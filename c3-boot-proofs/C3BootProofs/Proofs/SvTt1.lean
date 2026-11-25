import C3BootProofs.Proofs.SvGt

/-!
# `sigstore::verify`: the TSTInfo's version, policy, and message imprint

From 0x10A4 to 0x119C: the encapsulated content is one `TSTInfo` sequence whose version is `INTEGER 1`, whose policy is an OID, and whose message imprint is a SHA-256 algorithm identifier and a 32-byte digest with nothing after them.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svTt110ac : List BInstr :=
  [.aluImm .add a2 sp 0x280]
theorem svTt110ac_end : blockEnd sigstoreVerifyCode 0x10AC svTt110ac = some 0x10AE := by
  simp only [svTt110ac]
  rw [blockEnd, sv_at_10ac]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt110b4 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x27C]
theorem svTt110b4_end : blockEnd sigstoreVerifyCode 0x10B4 svTt110b4 = some 0x10BA := by
  simp only [svTt110b4]
  rw [blockEnd, sv_at_10b4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_10b8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt110ce : List BInstr :=
  [.aluImm .add a1 sp 0x425, .aluImm .add a0 sp 0x261, .aluImm .add a2 x0 0xB]
theorem svTt110ce_end : blockEnd sigstoreVerifyCode 0x10CE svTt110ce = some 0x10D8 := by
  simp only [svTt110ce]
  rw [blockEnd, sv_at_10ce]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_10d2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_10d6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt114c : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x1]
theorem svTt114c_end : blockEnd sigstoreVerifyCode 0x14C svTt114c = some 0x14E := by
  simp only [svTt114c]
  rw [blockEnd, sv_at_14c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt110f2 : List BInstr :=
  [.aluImm .add a0 sp 0x25C, .aluImm .add a1 x0 0x1]
theorem svTt110f2_end : blockEnd sigstoreVerifyCode 0x10F2 svTt110f2 = some 0x10F6 := by
  simp only [svTt110f2]
  rw [blockEnd, sv_at_10f2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_10f4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt110fe : List BInstr :=
  [.aluImm .and a0 a0 0x1, .alu .add (8 : Fin 32) x0 a1]
theorem svTt110fe_end : blockEnd sigstoreVerifyCode 0x10FE svTt110fe = some 0x1102 := by
  simp only [svTt110fe]
  rw [blockEnd, sv_at_10fe]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1100]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt11106 : List BInstr :=
  [.aluImm .and (8 : Fin 32) (8 : Fin 32) 0x1]
theorem svTt11106_end : blockEnd sigstoreVerifyCode 0x1106 svTt11106 = some 0x1108 := by
  simp only [svTt11106]
  rw [blockEnd, sv_at_1106]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt112b8 : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x18]
theorem svTt112b8_end : blockEnd sigstoreVerifyCode 0x12B8 svTt112b8 = some 0x12BA := by
  simp only [svTt112b8]
  rw [blockEnd, sv_at_12b8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt1110c : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x25C]
theorem svTt1110c_end : blockEnd sigstoreVerifyCode 0x110C svTt1110c = some 0x1112 := by
  simp only [svTt1110c]
  rw [blockEnd, sv_at_110c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1110]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt11122 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x25C]
theorem svTt11122_end : blockEnd sigstoreVerifyCode 0x1122 svTt11122 = some 0x1128 := by
  simp only [svTt11122]
  rw [blockEnd, sv_at_1122]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1126]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt1113c : List BInstr :=
  [.aluImm .add a1 sp 0x425, .aluImm .add a0 sp 0x3E5, .aluImm .add a2 x0 0xB]
theorem svTt1113c_end : blockEnd sigstoreVerifyCode 0x113C svTt1113c = some 0x1146 := by
  simp only [svTt1113c]
  rw [blockEnd, sv_at_113c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1140]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1144]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt11156 : List BInstr :=
  [.aluImm .add a0 sp 0x3E0]
theorem svTt11156_end : blockEnd sigstoreVerifyCode 0x1156 svTt11156 = some 0x1158 := by
  simp only [svTt11156]
  rw [blockEnd, sv_at_1156]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt11160 : List BInstr :=
  [.aluImm .and a0 a0 0x1, .alu .add (8 : Fin 32) x0 a1]
theorem svTt11160_end : blockEnd sigstoreVerifyCode 0x1160 svTt11160 = some 0x1164 := by
  simp only [svTt11160]
  rw [blockEnd, sv_at_1160]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1162]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt11168 : List BInstr :=
  [.aluImm .and a0 (8 : Fin 32) 0x1, .aluImm .add (8 : Fin 32) x0 0x18]
theorem svTt11168_end : blockEnd sigstoreVerifyCode 0x1168 svTt11168 = some 0x116E := by
  simp only [svTt11168]
  rw [blockEnd, sv_at_1168]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_116c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt11172 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x3E0]
theorem svTt11172_end : blockEnd sigstoreVerifyCode 0x1172 svTt11172 = some 0x1178 := by
  simp only [svTt11172]
  rw [blockEnd, sv_at_1172]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1176]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTt1118c : List BInstr :=
  [.aluImm .add a0 a0 0xFFFFFFE0]
theorem svTt1118c_end : blockEnd sigstoreVerifyCode 0x118C svTt1118c = some 0x118E := by
  simp only [svTt1118c]
  rw [blockEnd, sv_at_118c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_tt1 {B out bp x20 x21 x22 x23 x24 x25 x26 x27 tp tl : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x10A4 (reg n0))
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
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl)
    (tst_in : SvIn B (tp) (tl).toNat)
    (D0 : SvData M0) :
    (¬ (∃ tl9, derElement 0x30 (memBytes M0 (tp) (tl).toNat) = .ok tl9 ∧ ((tl) - BitVec.ofNat 32 (tl9.header + tl9.len) = 0) ∧ derIntIsOf M0 (memBytes M0 ((tp) + BitVec.ofNat 32 tl9.header) (BitVec.ofNat 32 tl9.len).toNat) ((tp) + BitVec.ofNat 32 tl9.header) (derElement 2 (memBytes M0 ((tp) + BitVec.ofNat 32 tl9.header) (BitVec.ofNat 32 tl9.len).toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = .ok true ∧ ∃ te20, derElement 2 (memBytes M0 ((tp) + BitVec.ofNat 32 tl9.header) (BitVec.ofNat 32 tl9.len).toNat) = .ok te20 ∧ ∃ op26 ol26, derContent (((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) (derOid (memBytes M0 (((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) ((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)).toNat)) = .ok (op26, ol26) ∧ ∃ to26, derOid (memBytes M0 (((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) ((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)).toNat) = .ok to26 ∧ ∃ tl30, derElement 0x30 (memBytes M0 ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)).toNat) = .ok tl30 ∧ isSha256Of M0 (((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) (BitVec.ofNat 32 tl30.len).toNat = .ok true ∧ ∃ te39, derElement 0x30 (memBytes M0 (((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) (BitVec.ofNat 32 tl30.len).toNat) = .ok te39 ∧ ∃ vp45 vl45, derContent ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) (derElement 4 (memBytes M0 ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)).toNat)) = .ok (vp45, vl45) ∧ ∃ te45, derElement 4 (memBytes M0 ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)).toNat) = .ok te45 ∧ (vl45 = 32) ∧ (((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) = 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ tl9, derElement 0x30 (memBytes M0 (tp) (tl).toNat) = .ok tl9 ∧
    ((tl) - BitVec.ofNat 32 (tl9.header + tl9.len) = 0) ∧
    derIntIsOf M0 (memBytes M0 ((tp) + BitVec.ofNat 32 tl9.header) (BitVec.ofNat 32 tl9.len).toNat) ((tp) + BitVec.ofNat 32 tl9.header) (derElement 2 (memBytes M0 ((tp) + BitVec.ofNat 32 tl9.header) (BitVec.ofNat 32 tl9.len).toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = .ok true ∧
    ∃ te20, derElement 2 (memBytes M0 ((tp) + BitVec.ofNat 32 tl9.header) (BitVec.ofNat 32 tl9.len).toNat) = .ok te20 ∧
    ∃ op26 ol26, derContent (((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) (derOid (memBytes M0 (((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) ((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)).toNat)) = .ok (op26, ol26) ∧
    ∃ to26, derOid (memBytes M0 (((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) ((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)).toNat) = .ok to26 ∧
    ∃ tl30, derElement 0x30 (memBytes M0 ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)).toNat) = .ok tl30 ∧
    isSha256Of M0 (((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) (BitVec.ofNat 32 tl30.len).toNat = .ok true ∧
    ∃ te39, derElement 0x30 (memBytes M0 (((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) (BitVec.ofNat 32 tl30.len).toNat) = .ok te39 ∧
    ∃ vp45 vl45, derContent ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) (derElement 4 (memBytes M0 ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)).toNat)) = .ok (vp45, vl45) ∧
    ∃ te45, derElement 4 (memBytes M0 ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)).toNat) = .ok te45 ∧
    (vl45 = 32) ∧
    (((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) = 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x119C (reg n') ∧
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
        reg n' (27 : Fin 32) = vp45 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) ∧
        SvKeepL B n0.mem n'.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x10A4: lw
  obtain ⟨n1, d1, u1⟩ := s0.lw E0.self sv_at_10a4 (off' := 0x10A6) (by decide)
    (by rw [g0_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s1 : St n1.mem SV n1 0x10A6 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
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
  have g1_24 : reg n1 (24 : Fin 32) = x24 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = x25 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = x27 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_27]
  have g1_10 : reg n1 a0 = tp := by
    rw [u1.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g0_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr, w0_74]
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_74 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m1]; exact w0_74
  have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m1]; exact w0_78
  -- 0x10A6: sw
  obtain ⟨n2, d2, s2, fr2, K2, W2, rg2⟩ := sv_sw F E1 s1 sv_at_10a6 (off' := 0x10AA) (c := 0x27C)
    (by decide) (by rw [g1_2]; sv_addr) (by decide) (by decide)
  have t2 : Steps n0 n2 := t1.trans d2
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.keep K2 (by decide)
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [rg2 sp, g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg2 (3 : Fin 32), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg2 (4 : Fin 32), g1_4]
  have g2_10 : reg n2 a0 = tp := by rw [rg2 a0, g1_10]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [rg2 (18 : Fin 32), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [rg2 (19 : Fin 32), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = x20 := by rw [rg2 (20 : Fin 32), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [rg2 (21 : Fin 32), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = x22 := by rw [rg2 (22 : Fin 32), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = x23 := by rw [rg2 (23 : Fin 32), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = x24 := by rw [rg2 (24 : Fin 32), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = x25 := by rw [rg2 (25 : Fin 32), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [rg2 (26 : Fin 32), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = x27 := by rw [rg2 (27 : Fin 32), g1_27]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x27C, 0x4)] := keep_kk1.trans K2.toL
  clear keep_kk1
  have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K2.w32 (by decide) (by decide)).trans w1_74
  have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K2.w32 (by decide) (by decide)).trans w1_78
  have w2_27c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [W2, g1_10]
  clear w1_78 w1_74 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x10AA: lw
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_10aa (off' := 0x10AC) (by decide)
    (by rw [g2_2, show B + 0x21A0 + 0x78 = B + 0x21A0 + BitVec.ofNat 32 0x78 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s3 : St n3.mem SV n3 0x10AC (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_10 : reg n3 a0 = tp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_10]
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
  have g3_11 : reg n3 a1 = tl := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_2, show B + 0x21A0 + 0x78 = B + 0x21A0 + BitVec.ofNat 32 0x78 by sv_addr, w2_78]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x27C, 0x4)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m3]; exact w2_74
  have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m3]; exact w2_78
  have w3_27c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m3]; exact w2_27c
  clear w2_27c w2_78 w2_74 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_10 g2_4 g2_3 g2_2 V2 E2 fR2 t2 rg2 W2 K2 fr2 s2 d2
  -- 0x10AC
  obtain ⟨n4, c4, u4⟩ := s3.block svTt110ac E3.self svTt110ac_end
    ⟨trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem SV n4 0x10AE (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock svTt110ac (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
  have g4_10 : reg n4 a0 = tp := by
    rw [rb4, runBlock_reg _ _ _ a0 s3.zero (by decide), g3_10]
  have g4_11 : reg n4 a1 = tl := by
    rw [rb4, runBlock_reg _ _ _ a1 s3.zero (by decide), g3_11]
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
  have g4_24 : reg n4 (24 : Fin 32) = x24 := by
    rw [rb4, runBlock_reg _ _ _ (24 : Fin 32) s3.zero (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = x25 := by
    rw [rb4, runBlock_reg _ _ _ (25 : Fin 32) s3.zero (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by
    rw [rb4, runBlock_reg _ _ _ (26 : Fin 32) s3.zero (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = x27 := by
    rw [rb4, runBlock_reg _ _ _ (27 : Fin 32) s3.zero (by decide), g3_27]
  have g4_12 : reg n4 a2 = B + 0x21A0 + BitVec.ofNat 32 0x280 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svTt110ac, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_10, g3_11, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x27C, 0x4)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m4]; exact w3_74
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m4]; exact w3_78
  have w4_27c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m4]; exact w3_27c
  clear w3_27c w3_78 w3_74 g3_11 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_10 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x10AE: sw
  obtain ⟨n5, d5, s5, fr5, K5, W5, rg5⟩ := sv_sw F E4 s4 sv_at_10ae (off' := 0x10B0) (c := 0x280)
    (by decide) (by rw [g4_12]; sv_addr) (by decide) (by decide)
  have t5 : Steps n0 n5 := t4.trans d5
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.keep K5 (by decide)
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [rg5 sp, g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg5 (3 : Fin 32), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg5 (4 : Fin 32), g4_4]
  have g5_10 : reg n5 a0 = tp := by rw [rg5 a0, g4_10]
  have g5_11 : reg n5 a1 = tl := by rw [rg5 a1, g4_11]
  have g5_12 : reg n5 a2 = B + 0x21A0 + BitVec.ofNat 32 0x280 := by rw [rg5 a2, g4_12]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [rg5 (18 : Fin 32), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [rg5 (19 : Fin 32), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [rg5 (20 : Fin 32), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [rg5 (21 : Fin 32), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [rg5 (22 : Fin 32), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [rg5 (23 : Fin 32), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = x24 := by rw [rg5 (24 : Fin 32), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [rg5 (25 : Fin 32), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [rg5 (26 : Fin 32), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = x27 := by rw [rg5 (27 : Fin 32), g4_27]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x27C, 0x4), (0x280, 0x4)] := keep_kk4.trans K5.toL
  clear keep_kk4
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K5.w32 (by decide) (by decide)).trans w4_74
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K5.w32 (by decide) (by decide)).trans w4_78
  have w5_27c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K5.w32 (by decide) (by decide)).trans w4_27c
  have w5_280 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [W5, g4_11]
  clear w4_27c w4_78 w4_74 g4_12 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_11 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  -- 0x10B0: sw
  obtain ⟨n6, d6, s6, fr6, K6, W6, rg6⟩ := sv_sw F E5 s5 sv_at_10b0 (off' := 0x10B2) (c := 0x284)
    (by decide) (by rw [g5_12]; sv_addr) (by decide) (by decide)
  have t6 : Steps n0 n6 := t5.trans d6
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.keep K6 (by decide)
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [rg6 sp, g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg6 (3 : Fin 32), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg6 (4 : Fin 32), g5_4]
  have g6_10 : reg n6 a0 = tp := by rw [rg6 a0, g5_10]
  have g6_11 : reg n6 a1 = tl := by rw [rg6 a1, g5_11]
  have g6_12 : reg n6 a2 = B + 0x21A0 + BitVec.ofNat 32 0x280 := by rw [rg6 a2, g5_12]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [rg6 (18 : Fin 32), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [rg6 (19 : Fin 32), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = x20 := by rw [rg6 (20 : Fin 32), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [rg6 (21 : Fin 32), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [rg6 (22 : Fin 32), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [rg6 (23 : Fin 32), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = x24 := by rw [rg6 (24 : Fin 32), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by rw [rg6 (25 : Fin 32), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [rg6 (26 : Fin 32), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = x27 := by rw [rg6 (27 : Fin 32), g5_27]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4)] := keep_kk5.trans K6.toL
  clear keep_kk5
  have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K6.w32 (by decide) (by decide)).trans w5_74
  have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K6.w32 (by decide) (by decide)).trans w5_78
  have w6_27c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K6.w32 (by decide) (by decide)).trans w5_27c
  have w6_280 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K6.w32 (by decide) (by decide)).trans w5_280
  have w6_284 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = tp := by rw [W6, g5_10]
  clear w5_280 w5_27c w5_78 w5_74 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_12 g5_11 g5_10 g5_4 g5_3 g5_2 V5 E5 fR5 t5 rg5 W5 K5 fr5 s5 d5
  -- 0x10B2: sw
  obtain ⟨n7, d7, s7, fr7, K7, W7, rg7⟩ := sv_sw F E6 s6 sv_at_10b2 (off' := 0x10B4) (c := 0x288)
    (by decide) (by rw [g6_12]; sv_addr) (by decide) (by decide)
  have t7 : Steps n0 n7 := t6.trans d7
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.keep K7 (by decide)
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [rg7 sp, g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg7 (3 : Fin 32), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg7 (4 : Fin 32), g6_4]
  have g7_10 : reg n7 a0 = tp := by rw [rg7 a0, g6_10]
  have g7_11 : reg n7 a1 = tl := by rw [rg7 a1, g6_11]
  have g7_12 : reg n7 a2 = B + 0x21A0 + BitVec.ofNat 32 0x280 := by rw [rg7 a2, g6_12]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [rg7 (18 : Fin 32), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [rg7 (19 : Fin 32), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [rg7 (20 : Fin 32), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [rg7 (21 : Fin 32), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [rg7 (22 : Fin 32), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [rg7 (23 : Fin 32), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = x24 := by rw [rg7 (24 : Fin 32), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [rg7 (25 : Fin 32), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [rg7 (26 : Fin 32), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = x27 := by rw [rg7 (27 : Fin 32), g6_27]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4)] := keep_kk6.trans K7.toL
  clear keep_kk6
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K7.w32 (by decide) (by decide)).trans w6_74
  have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K7.w32 (by decide) (by decide)).trans w6_78
  have w7_27c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K7.w32 (by decide) (by decide)).trans w6_27c
  have w7_280 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K7.w32 (by decide) (by decide)).trans w6_280
  have w7_284 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = tp := (K7.w32 (by decide) (by decide)).trans w6_284
  have w7_288 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = tl := by rw [W7, g6_11]
  clear w6_284 w6_280 w6_27c w6_78 w6_74 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_12 g6_11 g6_10 g6_4 g6_3 g6_2 V6 E6 fR6 t6 rg6 W6 K6 fr6 s6 d6
  -- 0x10B4
  obtain ⟨n8, c8, u8⟩ := s7.block svTt110b4 E7.self svTt110b4_end
    ⟨trivial, trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem SV n8 0x10BA (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock svTt110b4 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
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
  have g8_12 : reg n8 a2 = B + 0x21A0 + BitVec.ofNat 32 0x280 := by
    rw [rb8, runBlock_reg _ _ _ a2 s7.zero (by decide), g7_12]
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
  have g8_24 : reg n8 (24 : Fin 32) = x24 := by
    rw [rb8, runBlock_reg _ _ _ (24 : Fin 32) s7.zero (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by
    rw [rb8, runBlock_reg _ _ _ (25 : Fin 32) s7.zero (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by
    rw [rb8, runBlock_reg _ _ _ (26 : Fin 32) s7.zero (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = x27 := by
    rw [rb8, runBlock_reg _ _ _ (27 : Fin 32) s7.zero (by decide), g7_27]
  have g8_10 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svTt110b4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_10, g7_11, g7_12, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g8_11 : reg n8 a1 = B + 0x21A0 + BitVec.ofNat 32 0x27C := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svTt110b4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_10, g7_11, g7_12, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m8]; exact w7_74
  have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m8]; exact w7_78
  have w8_27c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m8]; exact w7_27c
  have w8_280 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m8]; exact w7_280
  have w8_284 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = tp := by rw [m8]; exact w7_284
  have w8_288 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = tl := by rw [m8]; exact w7_288
  clear w7_288 w7_284 w7_280 w7_27c w7_78 w7_74 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_12 g7_11 g7_10 g7_4 g7_3 g7_2 V7 E7 fR7 t7 rg7 W7 K7 fr7 s7 d7
  -- 0x10BA: sv_seqF
  obtain ⟨n9, c9, s9, sp9, rk9, K9, Ok9, Er9, fr9⟩ := sv_seqF (oc := 0x420) (dc := 0x27C)
    F E8 s8 sv_at_10ba sv_at_10be (by decide) (by decide) g8_2 g8_10 g8_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w8_284 w8_288 tst_in
  have t9 : Steps n0 n9 := t8.trans c9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keepL K9 (by decide)
  rw [sv_mb fR8 tst_in] at Ok9 Er9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rk9 sp (by decide) (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk9 (3 : Fin 32) (by decide) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk9 (4 : Fin 32) (by decide) (by decide), g8_4]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [rk9 (18 : Fin 32) (by decide) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [rk9 (19 : Fin 32) (by decide) (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [rk9 (20 : Fin 32) (by decide) (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [rk9 (21 : Fin 32) (by decide) (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [rk9 (22 : Fin 32) (by decide) (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [rk9 (23 : Fin 32) (by decide) (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = x24 := by rw [rk9 (24 : Fin 32) (by decide) (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [rk9 (25 : Fin 32) (by decide) (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [rk9 (26 : Fin 32) (by decide) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = x27 := by rw [rk9 (27 : Fin 32) (by decide) (by decide), g8_27]
  obtain ⟨r9, hr9⟩ : ∃ r, derElement 0x30 (memBytes M0 (tp) (tl).toNat) = r := ⟨_, rfl⟩
  rcases r9 with er9 | tl9
  · obtain ⟨z9, -⟩ := Er9 er9 hr9
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8)] := keep_kk8.trans K9
    clear keep_kk8
    have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K9.w32 (by decide) (by decide)).trans w8_74
    have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K9.w32 (by decide) (by decide)).trans w8_78
    have w9_27c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K9.w32 (by decide) (by decide)).trans w8_27c
    have w9_280 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K9.w32 (by decide) (by decide)).trans w8_280
    have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z9
    clear w8_288 w8_284 w8_280 w8_27c w8_78 w8_74 g8_11 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_12 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
    -- 0x10C2: lw
    obtain ⟨n10, d10, u10⟩ := s9.lw E9.self sv_at_10c2 (off' := 0x10C6) (by decide)
      (by rw [g9_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s10 : St n10.mem SV n10 0x10C6 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
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
    have g10_24 : reg n10 (24 : Fin 32) = x24 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_24]
    have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_25]
    have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = x27 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_27]
    have g10_9 : reg n10 (9 : Fin 32) = 0 := by
      rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g9_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w9_420]
    have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8)] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m10]; exact w9_74
    have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m10]; exact w9_78
    have w10_27c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m10]; exact w9_27c
    have w10_280 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m10]; exact w9_280
    have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m10]; exact w9_420
    clear w9_420 w9_280 w9_27c w9_78 w9_74 z9
    -- 0x10C6: lbu
    obtain ⟨n11, d11, u11⟩ := s10.lbu E10.self sv_at_10c6 (off' := 0x10CA) (by decide)
    have s11 : St n11.mem SV n11 0x10CA (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_4]
    have g11_9 : reg n11 (9 : Fin 32) = 0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_9]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, upd_ne (by decide) (by decide), g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = x27 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_27]
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m11]; exact w10_74
    have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m11]; exact w10_78
    have w11_27c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m11]; exact w10_27c
    have w11_280 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m11]; exact w10_280
    have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m11]; exact w10_420
    clear w10_420 w10_280 w10_27c w10_78 w10_74 g10_9 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
    -- 0x10CA: branch, taken
    obtain ⟨n12, d12, u12⟩ := s11.taken E11.self 0x7A4 sv_at_10ca
      (by decide) (by rw [g11_9, s11.zero]; rfl)
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
    have g12_9 : reg n12 (9 : Fin 32) = 0 := by rw [u12.regs, g11_9]
    have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, g11_19]
    have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [u12.regs, g11_20]
    have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [u12.regs, g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [u12.regs, g11_23]
    have g12_24 : reg n12 (24 : Fin 32) = x24 := by rw [u12.regs, g11_24]
    have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [u12.regs, g11_25]
    have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [u12.regs, g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = x27 := by rw [u12.regs, g11_27]
    have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m12]; exact w11_74
    have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m12]; exact w11_78
    have w12_27c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m12]; exact w11_27c
    have w12_280 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m12]; exact w11_280
    have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m12]; exact w11_420
    clear w11_420 w11_280 w11_27c w11_78 w11_74 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_9 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
    exact .inl ⟨(fun ⟨tl9', h0', _⟩ => by rw [hr9] at h0'; cases h0'), sv_fail F E12 s12 t12 (fun x hx => (fR12 x hx).trans (fM x hx).symm) V12 hret g12_2 g12_18 hO g12_3 g12_4⟩
  obtain ⟨o0_9, o4_9, o8_9, o12_9, d8_9, d12_9⟩ := Ok9 tl9 hr9
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8)] := keep_kk8.trans K9
  clear keep_kk8
  have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K9.w32 (by decide) (by decide)).trans w8_74
  have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K9.w32 (by decide) (by decide)).trans w8_78
  have w9_27c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K9.w32 (by decide) (by decide)).trans w8_27c
  have w9_280 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K9.w32 (by decide) (by decide)).trans w8_280
  have w9_284 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := d8_9
  have w9_288 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := d12_9
  have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := o0_9
  have w9_424 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := o4_9
  have w9_428 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := o8_9
  have w9_42c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := o12_9
  clear w8_288 w8_284 w8_280 w8_27c w8_78 w8_74 g8_11 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_12 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
  -- 0x10C2: lw
  obtain ⟨n10, d10, u10⟩ := s9.lw E9.self sv_at_10c2 (off' := 0x10C6) (by decide)
    (by rw [g9_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s10 : St n10.mem SV n10 0x10C6 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
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
  have g10_24 : reg n10 (24 : Fin 32) = x24 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = x27 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_27]
  have g10_9 : reg n10 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by
    rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g9_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w9_420]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m10]; exact w9_74
  have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m10]; exact w9_78
  have w10_27c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m10]; exact w9_27c
  have w10_280 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m10]; exact w9_280
  have w10_284 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m10]; exact w9_284
  have w10_288 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m10]; exact w9_288
  have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m10]; exact w9_420
  have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m10]; exact w9_424
  have w10_428 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m10]; exact w9_428
  have w10_42c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m10]; exact w9_42c
  clear w9_42c w9_428 w9_424 w9_420 w9_288 w9_284 w9_280 w9_27c w9_78 w9_74 d12_9 d8_9 o12_9 o8_9 o4_9 o0_9 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 Er9 Ok9 K9 rk9 sp9 s9 c9
  -- 0x10C6: lbu
  obtain ⟨n11, d11, u11⟩ := s10.lbu E10.self sv_at_10c6 (off' := 0x10CA) (by decide)
  have b10_424 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by
    have h := byte_of_ld w10_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact h.1
  have s11 : St n11.mem SV n11 0x10CA (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_4]
  have g11_9 : reg n11 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [u11.regs, upd_ne (by decide) (by decide), g10_9]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, upd_ne (by decide) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = x27 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_27]
  have g11_8 : reg n11 (8 : Fin 32) = ((BitVec.ofNat 32 tl9.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [u11.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g10_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b10_424]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m11]; exact w10_74
  have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m11]; exact w10_78
  have w11_27c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m11]; exact w10_27c
  have w11_280 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m11]; exact w10_280
  have w11_284 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m11]; exact w10_284
  have w11_288 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m11]; exact w10_288
  have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m11]; exact w10_420
  have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m11]; exact w10_424
  have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m11]; exact w10_428
  have w11_42c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m11]; exact w10_42c
  have b11_424 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m11]; exact b10_424
  clear w10_42c w10_428 w10_424 w10_420 w10_288 w10_284 w10_280 w10_27c w10_78 w10_74 g10_9 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
  -- 0x10CA: branch, not taken
  obtain ⟨n12, d12, u12⟩ := s11.notTaken E11.self 0x10CE sv_at_10ca
    (by decide) (by rw [g11_9, s11.zero]; exact br_beq_f (tst_in.ok_ne hr9))
  have s12 : St n12.mem SV n12 0x10CE (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = ((BitVec.ofNat 32 tl9.len).extractLsb' 0 8).zeroExtend 32 := by rw [u12.regs, g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [u12.regs, g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [u12.regs, g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [u12.regs, g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [u12.regs, g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = x24 := by rw [u12.regs, g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [u12.regs, g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [u12.regs, g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = x27 := by rw [u12.regs, g11_27]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m12]; exact w11_74
  have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m12]; exact w11_78
  have w12_27c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m12]; exact w11_27c
  have w12_280 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m12]; exact w11_280
  have w12_284 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m12]; exact w11_284
  have w12_288 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m12]; exact w11_288
  have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m12]; exact w11_420
  have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m12]; exact w11_424
  have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m12]; exact w11_428
  have w12_42c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m12]; exact w11_42c
  have b12_424 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m12]; exact b11_424
  clear b11_424 w11_42c w11_428 w11_424 w11_420 w11_288 w11_284 w11_280 w11_27c w11_78 w11_74 g11_8 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_9 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 b10_424 u11 d11
  -- 0x10CE
  obtain ⟨n13, c13, u13⟩ := s12.block svTt110ce E12.self svTt110ce_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem SV n13 0x10D8 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock svTt110ce (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
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
  have g13_8 : reg n13 (8 : Fin 32) = ((BitVec.ofNat 32 tl9.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb13, runBlock_reg _ _ _ (8 : Fin 32) s12.zero (by decide), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by
    rw [rb13, runBlock_reg _ _ _ (9 : Fin 32) s12.zero (by decide), g12_9]
  have g13_18 : reg n13 (18 : Fin 32) = out := by
    rw [rb13, runBlock_reg _ _ _ (18 : Fin 32) s12.zero (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by
    rw [rb13, runBlock_reg _ _ _ (19 : Fin 32) s12.zero (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = x20 := by
    rw [rb13, runBlock_reg _ _ _ (20 : Fin 32) s12.zero (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by
    rw [rb13, runBlock_reg _ _ _ (21 : Fin 32) s12.zero (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by
    rw [rb13, runBlock_reg _ _ _ (22 : Fin 32) s12.zero (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = x23 := by
    rw [rb13, runBlock_reg _ _ _ (23 : Fin 32) s12.zero (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = x24 := by
    rw [rb13, runBlock_reg _ _ _ (24 : Fin 32) s12.zero (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by
    rw [rb13, runBlock_reg _ _ _ (25 : Fin 32) s12.zero (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by
    rw [rb13, runBlock_reg _ _ _ (26 : Fin 32) s12.zero (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = x27 := by
    rw [rb13, runBlock_reg _ _ _ (27 : Fin 32) s12.zero (by decide), g12_27]
  have g13_10 : reg n13 a0 = B + 0x21A0 + BitVec.ofNat 32 0x261 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svTt110ce, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g13_11 : reg n13 a1 = B + 0x21A0 + BitVec.ofNat 32 0x425 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svTt110ce, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g13_12 : reg n13 a2 = BitVec.ofNat 32 0xB := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svTt110ce, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m13]; exact w12_74
  have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m13]; exact w12_78
  have w13_27c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m13]; exact w12_27c
  have w13_280 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m13]; exact w12_280
  have w13_284 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m13]; exact w12_284
  have w13_288 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m13]; exact w12_288
  have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m13]; exact w12_420
  have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m13]; exact w12_424
  have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m13]; exact w12_428
  have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m13]; exact w12_42c
  have b13_424 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m13]; exact b12_424
  clear b12_424 w12_42c w12_428 w12_424 w12_420 w12_288 w12_284 w12_280 w12_27c w12_78 w12_74 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
  have b13_425 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by
    have h := byte_of_ld w13_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x425 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 1 by sv_addr]; exact h.2.1
  have b13_426 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by
    have h := byte_of_ld w13_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x426 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 2 by sv_addr]; exact h.2.2.1
  have b13_427 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by
    have h := byte_of_ld w13_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x427 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 3 by sv_addr]; exact h.2.2.2
  -- 0x10D8: memcpy
  obtain ⟨n14, P14, K14, X14⟩ := sv_mc (c := 0x261) (d := 0x425) (N := 0xB) F E13 s13 sv_at_10d8 sv_at_10dc
    (by decide) (by decide) g13_2 g13_10 g13_11 g13_12
    (by decide) (by decide) (by decide)
  have s14 := P14.st
  have fr14 := P14.fr
  have t14 : Steps n0 n14 := t13.trans P14.steps
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keep K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [P14.regs sp (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P14.regs (3 : Fin 32) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P14.regs (4 : Fin 32) (by decide), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = ((BitVec.ofNat 32 tl9.len).extractLsb' 0 8).zeroExtend 32 := by rw [P14.regs (8 : Fin 32) (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [P14.regs (9 : Fin 32) (by decide), g13_9]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [P14.regs (18 : Fin 32) (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [P14.regs (19 : Fin 32) (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = x20 := by rw [P14.regs (20 : Fin 32) (by decide), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [P14.regs (21 : Fin 32) (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = x22 := by rw [P14.regs (22 : Fin 32) (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = x23 := by rw [P14.regs (23 : Fin 32) (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = x24 := by rw [P14.regs (24 : Fin 32) (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [P14.regs (25 : Fin 32) (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [P14.regs (26 : Fin 32) (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = x27 := by rw [P14.regs (27 : Fin 32) (by decide), g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB)] := keep_kk13.trans K14.toL
  clear keep_kk13
  have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K14.w32 (by decide) (by decide)).trans w13_74
  have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K14.w32 (by decide) (by decide)).trans w13_78
  have w14_27c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K14.w32 (by decide) (by decide)).trans w13_27c
  have w14_280 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K14.w32 (by decide) (by decide)).trans w13_280
  have w14_284 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K14.w32 (by decide) (by decide)).trans w13_284
  have w14_288 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K14.w32 (by decide) (by decide)).trans w13_288
  have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := (K14.w32 (by decide) (by decide)).trans w13_420
  have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := (K14.w32 (by decide) (by decide)).trans w13_424
  have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := (K14.w32 (by decide) (by decide)).trans w13_428
  have w14_42c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := (K14.w32 (by decide) (by decide)).trans w13_42c
  have b14_424 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := (K14.b8 (by decide) (by decide)).trans b13_424
  have b14_425 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := (K14.b8 (by decide) (by decide)).trans b13_425
  have b14_426 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := (K14.b8 (by decide) (by decide)).trans b13_426
  have b14_427 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := (K14.b8 (by decide) (by decide)).trans b13_427
  have w14_264 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (tp) + BitVec.ofNat 32 tl9.header := by
    rw [← w13_428]
    exact ld_cp fun q hq => by
      have := X14 (0x3 + q) (by omega)
      rwa [show 0x261 + (0x3 + q) = 0x264 + q by omega,
        show 0x425 + (0x3 + q) = 0x428 + q by omega] at this
  have w14_268 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = BitVec.ofNat 32 tl9.len := by
    rw [← w13_42c]
    exact ld_cp fun q hq => by
      have := X14 (0x7 + q) (by omega)
      rwa [show 0x261 + (0x7 + q) = 0x268 + q by omega,
        show 0x425 + (0x7 + q) = 0x42C + q by omega] at this
  have b14_261 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x261) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [show 0x261 = 0x261 + 0x0 from rfl, X14 0x0 (by decide)]; exact b13_425
  have b14_262 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x262) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [show 0x262 = 0x261 + 0x1 from rfl, X14 0x1 (by decide)]; exact b13_426
  have b14_263 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x263) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [show 0x263 = 0x261 + 0x2 from rfl, X14 0x2 (by decide)]; exact b13_427
  clear b13_424 w13_42c w13_428 w13_424 w13_420 w13_288 w13_284 w13_280 w13_27c w13_78 w13_74 g13_12 g13_11 g13_10 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
  -- 0x10E0: lw
  obtain ⟨n15, d15, u15⟩ := s14.lw E14.self sv_at_10e0 (off' := 0x10E4) (by decide)
    (by rw [g14_2, show B + 0x21A0 + 0x288 = B + 0x21A0 + BitVec.ofNat 32 0x288 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s15 : St n15.mem SV n15 0x10E4 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = ((BitVec.ofNat 32 tl9.len).extractLsb' 0 8).zeroExtend 32 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [u15.regs, upd_ne (by decide) (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, upd_ne (by decide) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = x24 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = x27 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_27]
  have g15_10 : reg n15 a0 = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by
    rw [u15.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g14_2, show B + 0x21A0 + 0x288 = B + 0x21A0 + BitVec.ofNat 32 0x288 by sv_addr, w14_288]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m15]; exact w14_74
  have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m15]; exact w14_78
  have w15_264 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m15]; exact w14_264
  have w15_268 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = BitVec.ofNat 32 tl9.len := by rw [m15]; exact w14_268
  have w15_27c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m15]; exact w14_27c
  have w15_280 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m15]; exact w14_280
  have w15_284 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m15]; exact w14_284
  have w15_288 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m15]; exact w14_288
  have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m15]; exact w14_420
  have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m15]; exact w14_424
  have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m15]; exact w14_428
  have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m15]; exact w14_42c
  have b15_261 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x261) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m15]; exact b14_261
  have b15_262 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x262) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m15]; exact b14_262
  have b15_263 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x263) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m15]; exact b14_263
  have b15_424 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m15]; exact b14_424
  have b15_425 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m15]; exact b14_425
  have b15_426 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m15]; exact b14_426
  have b15_427 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m15]; exact b14_427
  clear b14_263 b14_262 b14_261 w14_268 w14_264 b14_427 b14_426 b14_425 b14_424 w14_42c w14_428 w14_424 w14_420 w14_288 w14_284 w14_280 w14_27c w14_78 w14_74 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 s14 X14 K14 P14 b13_427 b13_426 b13_425
  -- 0x10E4: sw
  obtain ⟨n16, d16, s16, fr16, K16, W16, rg16⟩ := sv_sw F E15 s15 sv_at_10e4 (off' := 0x10E8) (c := 0x25C)
    (by decide) (by rw [g15_2]; sv_addr) (by decide) (by decide)
  have t16 : Steps n0 n16 := t15.trans d16
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.keep K16 (by decide)
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [rg16 sp, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg16 (3 : Fin 32), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg16 (4 : Fin 32), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = ((BitVec.ofNat 32 tl9.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg16 (8 : Fin 32), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [rg16 (9 : Fin 32), g15_9]
  have g16_10 : reg n16 a0 = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [rg16 a0, g15_10]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [rg16 (18 : Fin 32), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [rg16 (19 : Fin 32), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = x20 := by rw [rg16 (20 : Fin 32), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [rg16 (21 : Fin 32), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [rg16 (22 : Fin 32), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [rg16 (23 : Fin 32), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = x24 := by rw [rg16 (24 : Fin 32), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [rg16 (25 : Fin 32), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [rg16 (26 : Fin 32), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = x27 := by rw [rg16 (27 : Fin 32), g15_27]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4)] := keep_kk15.trans K16.toL
  clear keep_kk15
  have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K16.w32 (by decide) (by decide)).trans w15_74
  have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K16.w32 (by decide) (by decide)).trans w15_78
  have w16_264 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (tp) + BitVec.ofNat 32 tl9.header := (K16.w32 (by decide) (by decide)).trans w15_264
  have w16_268 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = BitVec.ofNat 32 tl9.len := (K16.w32 (by decide) (by decide)).trans w15_268
  have w16_27c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K16.w32 (by decide) (by decide)).trans w15_27c
  have w16_280 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K16.w32 (by decide) (by decide)).trans w15_280
  have w16_284 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K16.w32 (by decide) (by decide)).trans w15_284
  have w16_288 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K16.w32 (by decide) (by decide)).trans w15_288
  have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := (K16.w32 (by decide) (by decide)).trans w15_420
  have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := (K16.w32 (by decide) (by decide)).trans w15_424
  have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := (K16.w32 (by decide) (by decide)).trans w15_428
  have w16_42c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := (K16.w32 (by decide) (by decide)).trans w15_42c
  have b16_261 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x261) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := (K16.b8 (by decide) (by decide)).trans b15_261
  have b16_262 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x262) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := (K16.b8 (by decide) (by decide)).trans b15_262
  have b16_263 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x263) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := (K16.b8 (by decide) (by decide)).trans b15_263
  have b16_424 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := (K16.b8 (by decide) (by decide)).trans b15_424
  have b16_425 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := (K16.b8 (by decide) (by decide)).trans b15_425
  have b16_426 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := (K16.b8 (by decide) (by decide)).trans b15_426
  have b16_427 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := (K16.b8 (by decide) (by decide)).trans b15_427
  have w16_25c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [W16, g15_9]
  clear b15_427 b15_426 b15_425 b15_424 b15_263 b15_262 b15_261 w15_42c w15_428 w15_424 w15_420 w15_288 w15_284 w15_280 w15_27c w15_268 w15_264 w15_78 w15_74 g15_10 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
  -- 0x10E8: sb
  obtain ⟨n17, d17, s17, fr17, K17, W17, rg17⟩ := sv_sb F E16 s16 sv_at_10e8 (off' := 0x10EC) (c := 0x260)
    (by decide) (by rw [g16_2]; sv_addr) (by decide)
  have t17 : Steps n0 n17 := t16.trans d17
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.keep K17 (by decide)
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [rg17 sp, g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg17 (3 : Fin 32), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg17 (4 : Fin 32), g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = ((BitVec.ofNat 32 tl9.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg17 (8 : Fin 32), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [rg17 (9 : Fin 32), g16_9]
  have g17_10 : reg n17 a0 = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [rg17 a0, g16_10]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [rg17 (18 : Fin 32), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [rg17 (19 : Fin 32), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = x20 := by rw [rg17 (20 : Fin 32), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [rg17 (21 : Fin 32), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = x22 := by rw [rg17 (22 : Fin 32), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = x23 := by rw [rg17 (23 : Fin 32), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = x24 := by rw [rg17 (24 : Fin 32), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = x25 := by rw [rg17 (25 : Fin 32), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [rg17 (26 : Fin 32), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = x27 := by rw [rg17 (27 : Fin 32), g16_27]
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1)] := keep_kk16.trans K17.toL
  clear keep_kk16
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K17.w32 (by decide) (by decide)).trans w16_74
  have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K17.w32 (by decide) (by decide)).trans w16_78
  have w17_25c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := (K17.w32 (by decide) (by decide)).trans w16_25c
  have w17_264 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (tp) + BitVec.ofNat 32 tl9.header := (K17.w32 (by decide) (by decide)).trans w16_264
  have w17_268 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = BitVec.ofNat 32 tl9.len := (K17.w32 (by decide) (by decide)).trans w16_268
  have w17_27c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K17.w32 (by decide) (by decide)).trans w16_27c
  have w17_280 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K17.w32 (by decide) (by decide)).trans w16_280
  have w17_284 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K17.w32 (by decide) (by decide)).trans w16_284
  have w17_288 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K17.w32 (by decide) (by decide)).trans w16_288
  have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := (K17.w32 (by decide) (by decide)).trans w16_420
  have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := (K17.w32 (by decide) (by decide)).trans w16_424
  have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := (K17.w32 (by decide) (by decide)).trans w16_428
  have w17_42c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := (K17.w32 (by decide) (by decide)).trans w16_42c
  have b17_261 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x261) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := (K17.b8 (by decide) (by decide)).trans b16_261
  have b17_262 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x262) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := (K17.b8 (by decide) (by decide)).trans b16_262
  have b17_263 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x263) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := (K17.b8 (by decide) (by decide)).trans b16_263
  have b17_424 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := (K17.b8 (by decide) (by decide)).trans b16_424
  have b17_425 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := (K17.b8 (by decide) (by decide)).trans b16_425
  have b17_426 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := (K17.b8 (by decide) (by decide)).trans b16_426
  have b17_427 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := (K17.b8 (by decide) (by decide)).trans b16_427
  have b17_260 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [W17, g16_8, lbu_low]
  clear w16_25c b16_427 b16_426 b16_425 b16_424 b16_263 b16_262 b16_261 w16_42c w16_428 w16_424 w16_420 w16_288 w16_284 w16_280 w16_27c w16_268 w16_264 w16_78 w16_74 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_10 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 rg16 W16 K16 fr16 s16 d16
  have w17_260 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := ld_of_bytes b17_260
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x260 + 1 = B + 0x21A0 + BitVec.ofNat 32 0x261 by sv_addr]; exact b17_261)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x260 + 2 = B + 0x21A0 + BitVec.ofNat 32 0x262 by sv_addr]; exact b17_262)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x260 + 3 = B + 0x21A0 + BitVec.ofNat 32 0x263 by sv_addr]; exact b17_263)
  by_cases hrest0 : (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) = 0
  rotate_left
  · -- 0x10EC: branch, not taken
    obtain ⟨n18, d18, u18⟩ := s17.notTaken E17.self 0x10EE sv_at_10ec
      (by decide) (by rw [g17_10, s17.zero]; exact br_beq_f hrest0)
    have s18 : St n18.mem SV n18 0x10EE (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
    have m18 : n18.mem = n17.mem := u18.mem
    have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
    have t18 : Steps n0 n18 := t17.trans (.single d18)
    have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
    have E18 : SvCode n18.mem := E17.fr F fr18
    have V18 : SvSaves B n18.mem v := V17.same m18
    have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, g17_2]
    have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, g17_3]
    have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, g17_4]
    have g18_8 : reg n18 (8 : Fin 32) = ((BitVec.ofNat 32 tl9.len).extractLsb' 0 8).zeroExtend 32 := by rw [u18.regs, g17_8]
    have g18_9 : reg n18 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [u18.regs, g17_9]
    have g18_10 : reg n18 a0 = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [u18.regs, g17_10]
    have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, g17_18]
    have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, g17_19]
    have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [u18.regs, g17_20]
    have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [u18.regs, g17_21]
    have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [u18.regs, g17_22]
    have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [u18.regs, g17_23]
    have g18_24 : reg n18 (24 : Fin 32) = x24 := by rw [u18.regs, g17_24]
    have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [u18.regs, g17_25]
    have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [u18.regs, g17_26]
    have g18_27 : reg n18 (27 : Fin 32) = x27 := by rw [u18.regs, g17_27]
    have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1)] := by rw [m18]; exact keep_kk17
    clear keep_kk17
    have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m18]; exact w17_74
    have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m18]; exact w17_78
    have w18_25c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m18]; exact w17_25c
    have w18_260 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m18]; exact w17_260
    have w18_264 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m18]; exact w17_264
    have w18_268 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = BitVec.ofNat 32 tl9.len := by rw [m18]; exact w17_268
    have w18_27c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m18]; exact w17_27c
    have w18_280 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m18]; exact w17_280
    have w18_284 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m18]; exact w17_284
    have w18_288 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m18]; exact w17_288
    have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m18]; exact w17_420
    have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m18]; exact w17_424
    have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m18]; exact w17_428
    have w18_42c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m18]; exact w17_42c
    have b18_424 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m18]; exact b17_424
    have b18_425 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m18]; exact b17_425
    have b18_426 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m18]; exact b17_426
    have b18_427 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m18]; exact b17_427
    clear b17_260 b17_427 b17_426 b17_425 b17_424 b17_263 b17_262 b17_261 w17_42c w17_428 w17_424 w17_420 w17_288 w17_284 w17_280 w17_27c w17_268 w17_264 w17_25c w17_78 w17_74 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_10 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 rg17 W17 K17 fr17 s17 d17
    -- 0x10EE: j
    obtain ⟨n19, d19, u19⟩ := s18.jump E18.self sv_at_10ee (off' := 0x14C) (by decide)
      (by rw [s18.pc]; decide)
    have s19 : St n19.mem SV n19 0x14C (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
    have m19 : n19.mem = n18.mem := u19.mem
    have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
    have t19 : Steps n0 n19 := t18.trans (.single d19)
    have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
    have E19 : SvCode n19.mem := E18.fr F fr19
    have V19 : SvSaves B n19.mem v := V18.same m19
    have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, g18_2]
    have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, g18_3]
    have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, g18_4]
    have g19_8 : reg n19 (8 : Fin 32) = ((BitVec.ofNat 32 tl9.len).extractLsb' 0 8).zeroExtend 32 := by rw [u19.regs, g18_8]
    have g19_9 : reg n19 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [u19.regs, g18_9]
    have g19_10 : reg n19 a0 = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [u19.regs, g18_10]
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
    have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1)] := by rw [m19]; exact keep_kk18
    clear keep_kk18
    have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m19]; exact w18_74
    have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m19]; exact w18_78
    have w19_25c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m19]; exact w18_25c
    have w19_260 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m19]; exact w18_260
    have w19_264 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m19]; exact w18_264
    have w19_268 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = BitVec.ofNat 32 tl9.len := by rw [m19]; exact w18_268
    have w19_27c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m19]; exact w18_27c
    have w19_280 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m19]; exact w18_280
    have w19_284 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m19]; exact w18_284
    have w19_288 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m19]; exact w18_288
    have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m19]; exact w18_420
    have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m19]; exact w18_424
    have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m19]; exact w18_428
    have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m19]; exact w18_42c
    have b19_424 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m19]; exact b18_424
    have b19_425 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m19]; exact b18_425
    have b19_426 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m19]; exact b18_426
    have b19_427 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m19]; exact b18_427
    clear b18_427 b18_426 b18_425 b18_424 w18_42c w18_428 w18_424 w18_420 w18_288 w18_284 w18_280 w18_27c w18_268 w18_264 w18_260 w18_25c w18_78 w18_74 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_10 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
    -- 0x14C
    obtain ⟨n20, c20, u20⟩ := s19.block svTt114c E19.self svTt114c_end
      ⟨trivial, trivial⟩
    have m20 : n20.mem = n19.mem := u20.mem
    have s20 : St n20.mem SV n20 0x14E (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
    have rb20 : ∀ q, reg n20 q = (runBlock svTt114c (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
    have g20_9 : reg n20 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by
      rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
    have g20_10 : reg n20 a0 = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by
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
    have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb20]; simp +decide only [runBlock, BInstr.run, svTt114c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1)] := by rw [m20]; exact keep_kk19
    clear keep_kk19
    have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m20]; exact w19_74
    have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m20]; exact w19_78
    have w20_25c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m20]; exact w19_25c
    have w20_260 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m20]; exact w19_260
    have w20_264 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m20]; exact w19_264
    have w20_268 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = BitVec.ofNat 32 tl9.len := by rw [m20]; exact w19_268
    have w20_27c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m20]; exact w19_27c
    have w20_280 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m20]; exact w19_280
    have w20_284 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m20]; exact w19_284
    have w20_288 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m20]; exact w19_288
    have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m20]; exact w19_420
    have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m20]; exact w19_424
    have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m20]; exact w19_428
    have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m20]; exact w19_42c
    have b20_424 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m20]; exact b19_424
    have b20_425 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m20]; exact b19_425
    have b20_426 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m20]; exact b19_426
    have b20_427 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m20]; exact b19_427
    clear b19_427 b19_426 b19_425 b19_424 w19_42c w19_428 w19_424 w19_420 w19_288 w19_284 w19_280 w19_27c w19_268 w19_264 w19_260 w19_25c w19_78 w19_74 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_10 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
    -- 0x14E: j
    obtain ⟨n21, d21, u21⟩ := s20.jump E20.self sv_at_14e (off' := 0x7A4) (by decide)
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
    have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u21.regs, g20_8]
    have g21_9 : reg n21 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [u21.regs, g20_9]
    have g21_10 : reg n21 a0 = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [u21.regs, g20_10]
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
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1)] := by rw [m21]; exact keep_kk20
    clear keep_kk20
    have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m21]; exact w20_74
    have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m21]; exact w20_78
    have w21_25c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m21]; exact w20_25c
    have w21_260 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m21]; exact w20_260
    have w21_264 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m21]; exact w20_264
    have w21_268 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = BitVec.ofNat 32 tl9.len := by rw [m21]; exact w20_268
    have w21_27c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m21]; exact w20_27c
    have w21_280 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m21]; exact w20_280
    have w21_284 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m21]; exact w20_284
    have w21_288 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m21]; exact w20_288
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m21]; exact w20_420
    have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m21]; exact w20_424
    have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m21]; exact w20_428
    have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m21]; exact w20_42c
    have b21_424 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m21]; exact b20_424
    have b21_425 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m21]; exact b20_425
    have b21_426 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m21]; exact b20_426
    have b21_427 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m21]; exact b20_427
    clear b20_427 b20_426 b20_425 b20_424 w20_42c w20_428 w20_424 w20_420 w20_288 w20_284 w20_280 w20_27c w20_268 w20_264 w20_260 w20_25c w20_78 w20_74 g20_8 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_10 g20_9 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
    exact .inl ⟨(fun ⟨tl9', h0', h1', _⟩ => by rw [hr9] at h0'; cases h0'; exact hrest0 h1'), sv_fail F E21 s21 t21 (fun x hx => (fR21 x hx).trans (fM x hx).symm) V21 hret g21_2 g21_18 hO g21_3 g21_4⟩
  -- 0x10EC: branch, taken
  obtain ⟨n18, d18, u18⟩ := s17.taken E17.self 0x10F2 sv_at_10ec
    (by decide) (by rw [g17_10, s17.zero]; exact br_beq_t hrest0)
  have s18 : St n18.mem SV n18 0x10F2 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans (.single d18)
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = ((BitVec.ofNat 32 tl9.len).extractLsb' 0 8).zeroExtend 32 := by rw [u18.regs, g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [u18.regs, g17_9]
  have g18_10 : reg n18 a0 = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [u18.regs, g17_10]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [u18.regs, g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [u18.regs, g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [u18.regs, g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [u18.regs, g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = x24 := by rw [u18.regs, g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [u18.regs, g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [u18.regs, g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = x27 := by rw [u18.regs, g17_27]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m18]; exact w17_74
  have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m18]; exact w17_78
  have w18_25c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m18]; exact w17_25c
  have w18_260 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m18]; exact w17_260
  have w18_264 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m18]; exact w17_264
  have w18_268 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = BitVec.ofNat 32 tl9.len := by rw [m18]; exact w17_268
  have w18_27c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m18]; exact w17_27c
  have w18_280 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m18]; exact w17_280
  have w18_284 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m18]; exact w17_284
  have w18_288 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m18]; exact w17_288
  have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m18]; exact w17_420
  have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m18]; exact w17_424
  have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m18]; exact w17_428
  have w18_42c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m18]; exact w17_42c
  have b18_424 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m18]; exact b17_424
  have b18_425 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m18]; exact b17_425
  have b18_426 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m18]; exact b17_426
  have b18_427 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m18]; exact b17_427
  clear b17_260 b17_427 b17_426 b17_425 b17_424 b17_263 b17_262 b17_261 w17_42c w17_428 w17_424 w17_420 w17_288 w17_284 w17_280 w17_27c w17_268 w17_264 w17_25c w17_78 w17_74 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_10 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 rg17 W17 K17 fr17 s17 d17
  -- 0x10F2
  obtain ⟨n19, c19, u19⟩ := s18.block svTt110f2 E18.self svTt110f2_end
    ⟨trivial, trivial, trivial⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have s19 : St n19.mem SV n19 0x10F6 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have rb19 : ∀ q, reg n19 q = (runBlock svTt110f2 (n18.mem, reg n18)).2 q := fun q => by rw [u19.regs]
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
  have g19_8 : reg n19 (8 : Fin 32) = ((BitVec.ofNat 32 tl9.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb19, runBlock_reg _ _ _ (8 : Fin 32) s18.zero (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by
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
  have g19_24 : reg n19 (24 : Fin 32) = x24 := by
    rw [rb19, runBlock_reg _ _ _ (24 : Fin 32) s18.zero (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = x25 := by
    rw [rb19, runBlock_reg _ _ _ (25 : Fin 32) s18.zero (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by
    rw [rb19, runBlock_reg _ _ _ (26 : Fin 32) s18.zero (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = x27 := by
    rw [rb19, runBlock_reg _ _ _ (27 : Fin 32) s18.zero (by decide), g18_27]
  have g19_10 : reg n19 a0 = B + 0x21A0 + BitVec.ofNat 32 0x25C := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svTt110f2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_10, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_25, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g19_11 : reg n19 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svTt110f2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_10, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_25, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m19]; exact w18_74
  have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m19]; exact w18_78
  have w19_25c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m19]; exact w18_25c
  have w19_260 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m19]; exact w18_260
  have w19_264 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m19]; exact w18_264
  have w19_268 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = BitVec.ofNat 32 tl9.len := by rw [m19]; exact w18_268
  have w19_27c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m19]; exact w18_27c
  have w19_280 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m19]; exact w18_280
  have w19_284 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m19]; exact w18_284
  have w19_288 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m19]; exact w18_288
  have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m19]; exact w18_420
  have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m19]; exact w18_424
  have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m19]; exact w18_428
  have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m19]; exact w18_42c
  have b19_424 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m19]; exact b18_424
  have b19_425 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m19]; exact b18_425
  have b19_426 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m19]; exact b18_426
  have b19_427 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m19]; exact b18_427
  clear b18_427 b18_426 b18_425 b18_424 w18_42c w18_428 w18_424 w18_420 w18_288 w18_284 w18_280 w18_27c w18_268 w18_264 w18_260 w18_25c w18_78 w18_74 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_10 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18 w17_260
  -- 0x10F6: sv_iiF
  obtain ⟨n20, c20, s20, sp20, rk20, K20, A20, R20, fr20⟩ := sv_iiF (dc := 0x25C)
    F E19 s19 sv_at_10f6 sv_at_10fa (by decide) (by decide) g19_2 g19_10
    (by decide) (by decide) w19_264 w19_268 (tst_in.contentW hr9)
  have t20 : Steps n0 n20 := t19.trans c20
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.keepL K20 (by decide)
  rw [sv_mb fR19 (tst_in.contentW hr9), derIntIsOf_congr fR19 (tst_in.contentW hr9), g19_11] at R20
  rw [sv_mb fR19 (tst_in.contentW hr9)] at A20
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk20 (3 : Fin 32) (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk20 (4 : Fin 32) (by decide), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = ((BitVec.ofNat 32 tl9.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk20 (8 : Fin 32) (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [rk20 (9 : Fin 32) (by decide), g19_9]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [rk20 (18 : Fin 32) (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [rk20 (19 : Fin 32) (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = x20 := by rw [rk20 (20 : Fin 32) (by decide), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = x21 := by rw [rk20 (21 : Fin 32) (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = x22 := by rw [rk20 (22 : Fin 32) (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = x23 := by rw [rk20 (23 : Fin 32) (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = x24 := by rw [rk20 (24 : Fin 32) (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = x25 := by rw [rk20 (25 : Fin 32) (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [rk20 (26 : Fin 32) (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = x27 := by rw [rk20 (27 : Fin 32) (by decide), g19_27]
  have g20_2 : reg n20 sp = B + 0x21A0 := sp20
  obtain ⟨r20, hr20⟩ : ∃ r, derIntIsOf M0 (memBytes M0 ((tp) + BitVec.ofNat 32 tl9.header) (BitVec.ofNat 32 tl9.len).toNat) ((tp) + BitVec.ofNat 32 tl9.header) (derElement 2 (memBytes M0 ((tp) + BitVec.ofNat 32 tl9.header) (BitVec.ofNat 32 tl9.len).toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = r := ⟨_, rfl⟩
  rcases r20 with b20 | (_ | _)
  · rw [hr20] at R20
    obtain ⟨a0_20, a1_20⟩ := R20
    have g20_10 : reg n20 a0 = BitVec.ofNat 32 0x1 := a0_20
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8)] := keep_kk19.trans K20
    clear keep_kk19
    have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K20.w32 (by decide) (by decide)).trans w19_74
    have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K20.w32 (by decide) (by decide)).trans w19_78
    have w20_25c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := (K20.w32 (by decide) (by decide)).trans w19_25c
    have w20_260 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := (K20.w32 (by decide) (by decide)).trans w19_260
    have w20_27c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K20.w32 (by decide) (by decide)).trans w19_27c
    have w20_280 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K20.w32 (by decide) (by decide)).trans w19_280
    have w20_284 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K20.w32 (by decide) (by decide)).trans w19_284
    have w20_288 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K20.w32 (by decide) (by decide)).trans w19_288
    have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := (K20.w32 (by decide) (by decide)).trans w19_420
    have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := (K20.w32 (by decide) (by decide)).trans w19_424
    have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := (K20.w32 (by decide) (by decide)).trans w19_428
    have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := (K20.w32 (by decide) (by decide)).trans w19_42c
    have b20_424 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := (K20.b8 (by decide) (by decide)).trans b19_424
    have b20_425 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := (K20.b8 (by decide) (by decide)).trans b19_425
    have b20_426 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := (K20.b8 (by decide) (by decide)).trans b19_426
    have b20_427 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := (K20.b8 (by decide) (by decide)).trans b19_427
    clear b19_427 b19_426 b19_425 b19_424 w19_42c w19_428 w19_424 w19_420 w19_288 w19_284 w19_280 w19_27c w19_268 w19_264 w19_260 w19_25c w19_78 w19_74 g19_11 g19_10 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
    -- 0x10FE
    obtain ⟨n21, c21, u21⟩ := s20.block svTt110fe E20.self svTt110fe_end
      ⟨trivial, trivial, trivial⟩
    have m21 : n21.mem = n20.mem := u21.mem
    have s21 : St n21.mem SV n21 0x1102 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
    have rb21 : ∀ q, reg n21 q = (runBlock svTt110fe (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
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
    have g21_9 : reg n21 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by
      rw [rb21, runBlock_reg _ _ _ (9 : Fin 32) s20.zero (by decide), g20_9]
    have g21_18 : reg n21 (18 : Fin 32) = out := by
      rw [rb21, runBlock_reg _ _ _ (18 : Fin 32) s20.zero (by decide), g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by
      rw [rb21, runBlock_reg _ _ _ (19 : Fin 32) s20.zero (by decide), g20_19]
    have g21_20 : reg n21 (20 : Fin 32) = x20 := by
      rw [rb21, runBlock_reg _ _ _ (20 : Fin 32) s20.zero (by decide), g20_20]
    have g21_21 : reg n21 (21 : Fin 32) = x21 := by
      rw [rb21, runBlock_reg _ _ _ (21 : Fin 32) s20.zero (by decide), g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = x22 := by
      rw [rb21, runBlock_reg _ _ _ (22 : Fin 32) s20.zero (by decide), g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = x23 := by
      rw [rb21, runBlock_reg _ _ _ (23 : Fin 32) s20.zero (by decide), g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = x24 := by
      rw [rb21, runBlock_reg _ _ _ (24 : Fin 32) s20.zero (by decide), g20_24]
    have g21_25 : reg n21 (25 : Fin 32) = x25 := by
      rw [rb21, runBlock_reg _ _ _ (25 : Fin 32) s20.zero (by decide), g20_25]
    have g21_26 : reg n21 (26 : Fin 32) = x26 := by
      rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = x27 := by
      rw [rb21, runBlock_reg _ _ _ (27 : Fin 32) s20.zero (by decide), g20_27]
    have g21_10 : reg n21 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb21]; simp +decide only [runBlock, BInstr.run, svTt110fe, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_10, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_25, g20_26, g20_27, s20.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8)] := by rw [m21]; exact keep_kk20
    clear keep_kk20
    have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m21]; exact w20_74
    have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m21]; exact w20_78
    have w21_25c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m21]; exact w20_25c
    have w21_260 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m21]; exact w20_260
    have w21_27c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m21]; exact w20_27c
    have w21_280 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m21]; exact w20_280
    have w21_284 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m21]; exact w20_284
    have w21_288 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m21]; exact w20_288
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m21]; exact w20_420
    have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m21]; exact w20_424
    have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m21]; exact w20_428
    have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m21]; exact w20_42c
    have b21_424 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m21]; exact b20_424
    have b21_425 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m21]; exact b20_425
    have b21_426 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m21]; exact b20_426
    have b21_427 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m21]; exact b20_427
    clear b20_427 b20_426 b20_425 b20_424 w20_42c w20_428 w20_424 w20_420 w20_288 w20_284 w20_280 w20_27c w20_260 w20_25c w20_78 w20_74 g20_10 a1_20 a0_20
    -- 0x1102: branch, taken
    obtain ⟨n22, d22, u22⟩ := s21.taken E21.self 0x7A4 sv_at_1102
      (by decide) (by rw [g21_10, s21.zero]; decide)
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
    have g22_9 : reg n22 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [u22.regs, g21_9]
    have g22_10 : reg n22 a0 = BitVec.ofNat 32 0x1 := by rw [u22.regs, g21_10]
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
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m22]; exact w21_74
    have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m22]; exact w21_78
    have w22_25c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m22]; exact w21_25c
    have w22_260 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m22]; exact w21_260
    have w22_27c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m22]; exact w21_27c
    have w22_280 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m22]; exact w21_280
    have w22_284 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m22]; exact w21_284
    have w22_288 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m22]; exact w21_288
    have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m22]; exact w21_420
    have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m22]; exact w21_424
    have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m22]; exact w21_428
    have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m22]; exact w21_42c
    have b22_424 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m22]; exact b21_424
    have b22_425 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m22]; exact b21_425
    have b22_426 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m22]; exact b21_426
    have b22_427 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m22]; exact b21_427
    clear b21_427 b21_426 b21_425 b21_424 w21_42c w21_428 w21_424 w21_420 w21_288 w21_284 w21_280 w21_27c w21_260 w21_25c w21_78 w21_74 g21_10 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
    exact .inl ⟨(fun ⟨tl9', h0', h1', h2', _⟩ => by rw [hr9] at h0'; cases h0'; rw [hr20] at h2'; cases h2'), sv_fail F E22 s22 t22 (fun x hx => (fR22 x hx).trans (fM x hx).symm) V22 hret g22_2 g22_18 hO g22_3 g22_4⟩
  · rw [hr20] at R20
    obtain ⟨a0_20, a1_20⟩ := R20
    have g20_10 : reg n20 a0 = BitVec.ofNat 32 0x0 := a0_20
    have g20_11 : reg n20 a1 = BitVec.ofNat 32 0x0 := by rw [a1_20]; rfl
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8)] := keep_kk19.trans K20
    clear keep_kk19
    have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K20.w32 (by decide) (by decide)).trans w19_74
    have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K20.w32 (by decide) (by decide)).trans w19_78
    have w20_25c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := (K20.w32 (by decide) (by decide)).trans w19_25c
    have w20_260 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := (K20.w32 (by decide) (by decide)).trans w19_260
    have w20_27c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K20.w32 (by decide) (by decide)).trans w19_27c
    have w20_280 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K20.w32 (by decide) (by decide)).trans w19_280
    have w20_284 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K20.w32 (by decide) (by decide)).trans w19_284
    have w20_288 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K20.w32 (by decide) (by decide)).trans w19_288
    have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := (K20.w32 (by decide) (by decide)).trans w19_420
    have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := (K20.w32 (by decide) (by decide)).trans w19_424
    have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := (K20.w32 (by decide) (by decide)).trans w19_428
    have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := (K20.w32 (by decide) (by decide)).trans w19_42c
    have b20_424 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := (K20.b8 (by decide) (by decide)).trans b19_424
    have b20_425 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := (K20.b8 (by decide) (by decide)).trans b19_425
    have b20_426 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := (K20.b8 (by decide) (by decide)).trans b19_426
    have b20_427 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := (K20.b8 (by decide) (by decide)).trans b19_427
    clear b19_427 b19_426 b19_425 b19_424 w19_42c w19_428 w19_424 w19_420 w19_288 w19_284 w19_280 w19_27c w19_268 w19_264 w19_260 w19_25c w19_78 w19_74 g19_11 g19_10 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
    -- 0x10FE
    obtain ⟨n21, c21, u21⟩ := s20.block svTt110fe E20.self svTt110fe_end
      ⟨trivial, trivial, trivial⟩
    have m21 : n21.mem = n20.mem := u21.mem
    have s21 : St n21.mem SV n21 0x1102 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
    have rb21 : ∀ q, reg n21 q = (runBlock svTt110fe (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
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
    have g21_9 : reg n21 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by
      rw [rb21, runBlock_reg _ _ _ (9 : Fin 32) s20.zero (by decide), g20_9]
    have g21_11 : reg n21 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb21, runBlock_reg _ _ _ a1 s20.zero (by decide), g20_11]
    have g21_18 : reg n21 (18 : Fin 32) = out := by
      rw [rb21, runBlock_reg _ _ _ (18 : Fin 32) s20.zero (by decide), g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by
      rw [rb21, runBlock_reg _ _ _ (19 : Fin 32) s20.zero (by decide), g20_19]
    have g21_20 : reg n21 (20 : Fin 32) = x20 := by
      rw [rb21, runBlock_reg _ _ _ (20 : Fin 32) s20.zero (by decide), g20_20]
    have g21_21 : reg n21 (21 : Fin 32) = x21 := by
      rw [rb21, runBlock_reg _ _ _ (21 : Fin 32) s20.zero (by decide), g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = x22 := by
      rw [rb21, runBlock_reg _ _ _ (22 : Fin 32) s20.zero (by decide), g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = x23 := by
      rw [rb21, runBlock_reg _ _ _ (23 : Fin 32) s20.zero (by decide), g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = x24 := by
      rw [rb21, runBlock_reg _ _ _ (24 : Fin 32) s20.zero (by decide), g20_24]
    have g21_25 : reg n21 (25 : Fin 32) = x25 := by
      rw [rb21, runBlock_reg _ _ _ (25 : Fin 32) s20.zero (by decide), g20_25]
    have g21_26 : reg n21 (26 : Fin 32) = x26 := by
      rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = x27 := by
      rw [rb21, runBlock_reg _ _ _ (27 : Fin 32) s20.zero (by decide), g20_27]
    have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [rb21]; simp +decide only [runBlock, BInstr.run, svTt110fe, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_10, g20_11, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_25, g20_26, g20_27, s20.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g21_10 : reg n21 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb21]; simp +decide only [runBlock, BInstr.run, svTt110fe, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_10, g20_11, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_25, g20_26, g20_27, s20.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8)] := by rw [m21]; exact keep_kk20
    clear keep_kk20
    have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m21]; exact w20_74
    have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m21]; exact w20_78
    have w21_25c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m21]; exact w20_25c
    have w21_260 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m21]; exact w20_260
    have w21_27c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m21]; exact w20_27c
    have w21_280 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m21]; exact w20_280
    have w21_284 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m21]; exact w20_284
    have w21_288 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m21]; exact w20_288
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m21]; exact w20_420
    have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m21]; exact w20_424
    have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m21]; exact w20_428
    have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m21]; exact w20_42c
    have b21_424 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m21]; exact b20_424
    have b21_425 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m21]; exact b20_425
    have b21_426 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m21]; exact b20_426
    have b21_427 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m21]; exact b20_427
    clear b20_427 b20_426 b20_425 b20_424 w20_42c w20_428 w20_424 w20_420 w20_288 w20_284 w20_280 w20_27c w20_260 w20_25c w20_78 w20_74 g20_11 g20_10 a1_20 a0_20
    -- 0x1102: branch, not taken
    obtain ⟨n22, d22, u22⟩ := s21.notTaken E21.self 0x1106 sv_at_1102
      (by decide) (by rw [g21_10, s21.zero]; decide)
    have s22 : St n22.mem SV n22 0x1106 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans (.single d22)
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, g21_4]
    have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u22.regs, g21_8]
    have g22_9 : reg n22 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [u22.regs, g21_9]
    have g22_10 : reg n22 a0 = BitVec.ofNat 32 0x0 := by rw [u22.regs, g21_10]
    have g22_11 : reg n22 a1 = BitVec.ofNat 32 0x0 := by rw [u22.regs, g21_11]
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
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m22]; exact w21_74
    have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m22]; exact w21_78
    have w22_25c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m22]; exact w21_25c
    have w22_260 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m22]; exact w21_260
    have w22_27c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m22]; exact w21_27c
    have w22_280 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m22]; exact w21_280
    have w22_284 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m22]; exact w21_284
    have w22_288 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m22]; exact w21_288
    have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m22]; exact w21_420
    have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m22]; exact w21_424
    have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m22]; exact w21_428
    have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m22]; exact w21_42c
    have b22_424 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m22]; exact b21_424
    have b22_425 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m22]; exact b21_425
    have b22_426 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m22]; exact b21_426
    have b22_427 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m22]; exact b21_427
    clear b21_427 b21_426 b21_425 b21_424 w21_42c w21_428 w21_424 w21_420 w21_288 w21_284 w21_280 w21_27c w21_260 w21_25c w21_78 w21_74 g21_10 g21_8 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_11 g21_9 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
    -- 0x1106
    obtain ⟨n23, c23, u23⟩ := s22.block svTt11106 E22.self svTt11106_end
      ⟨trivial, trivial⟩
    have m23 : n23.mem = n22.mem := u23.mem
    have s23 : St n23.mem SV n23 0x1108 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
    have rb23 : ∀ q, reg n23 q = (runBlock svTt11106 (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
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
    have g23_9 : reg n23 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by
      rw [rb23, runBlock_reg _ _ _ (9 : Fin 32) s22.zero (by decide), g22_9]
    have g23_10 : reg n23 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb23, runBlock_reg _ _ _ a0 s22.zero (by decide), g22_10]
    have g23_11 : reg n23 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb23, runBlock_reg _ _ _ a1 s22.zero (by decide), g22_11]
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
    have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [rb23]; simp +decide only [runBlock, BInstr.run, svTt11106, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_10, g22_11, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_25, g22_26, g22_27, s22.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8)] := by rw [m23]; exact keep_kk22
    clear keep_kk22
    have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m23]; exact w22_74
    have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m23]; exact w22_78
    have w23_25c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m23]; exact w22_25c
    have w23_260 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m23]; exact w22_260
    have w23_27c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m23]; exact w22_27c
    have w23_280 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m23]; exact w22_280
    have w23_284 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m23]; exact w22_284
    have w23_288 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m23]; exact w22_288
    have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m23]; exact w22_420
    have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m23]; exact w22_424
    have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m23]; exact w22_428
    have w23_42c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m23]; exact w22_42c
    have b23_424 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m23]; exact b22_424
    have b23_425 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m23]; exact b22_425
    have b23_426 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m23]; exact b22_426
    have b23_427 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m23]; exact b22_427
    clear b22_427 b22_426 b22_425 b22_424 w22_42c w22_428 w22_424 w22_420 w22_288 w22_284 w22_280 w22_27c w22_260 w22_25c w22_78 w22_74 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_11 g22_10 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
    -- 0x1108: branch, taken
    obtain ⟨n24, d24, u24⟩ := s23.taken E23.self 0x12B8 sv_at_1108
      (by decide) (by rw [g23_8, s23.zero]; decide)
    have s24 : St n24.mem SV n24 0x12B8 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
    have m24 : n24.mem = n23.mem := u24.mem
    have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
    have t24 : Steps n0 n24 := t23.trans (.single d24)
    have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
    have E24 : SvCode n24.mem := E23.fr F fr24
    have V24 : SvSaves B n24.mem v := V23.same m24
    have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
    have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
    have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
    have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u24.regs, g23_8]
    have g24_9 : reg n24 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [u24.regs, g23_9]
    have g24_10 : reg n24 a0 = BitVec.ofNat 32 0x0 := by rw [u24.regs, g23_10]
    have g24_11 : reg n24 a1 = BitVec.ofNat 32 0x0 := by rw [u24.regs, g23_11]
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
    have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8)] := by rw [m24]; exact keep_kk23
    clear keep_kk23
    have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m24]; exact w23_74
    have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m24]; exact w23_78
    have w24_25c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m24]; exact w23_25c
    have w24_260 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m24]; exact w23_260
    have w24_27c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m24]; exact w23_27c
    have w24_280 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m24]; exact w23_280
    have w24_284 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m24]; exact w23_284
    have w24_288 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m24]; exact w23_288
    have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m24]; exact w23_420
    have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m24]; exact w23_424
    have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m24]; exact w23_428
    have w24_42c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m24]; exact w23_42c
    have b24_424 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m24]; exact b23_424
    have b24_425 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m24]; exact b23_425
    have b24_426 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m24]; exact b23_426
    have b24_427 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m24]; exact b23_427
    clear b23_427 b23_426 b23_425 b23_424 w23_42c w23_428 w23_424 w23_420 w23_288 w23_284 w23_280 w23_27c w23_260 w23_25c w23_78 w23_74 g23_8 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_11 g23_10 g23_9 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
    -- 0x12B8
    obtain ⟨n25, c25, u25⟩ := s24.block svTt112b8 E24.self svTt112b8_end
      ⟨trivial, trivial⟩
    have m25 : n25.mem = n24.mem := u25.mem
    have s25 : St n25.mem SV n25 0x12BA (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
    have rb25 : ∀ q, reg n25 q = (runBlock svTt112b8 (n24.mem, reg n24)).2 q := fun q => by rw [u25.regs]
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
    have g25_9 : reg n25 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by
      rw [rb25, runBlock_reg _ _ _ (9 : Fin 32) s24.zero (by decide), g24_9]
    have g25_10 : reg n25 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb25, runBlock_reg _ _ _ a0 s24.zero (by decide), g24_10]
    have g25_11 : reg n25 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb25, runBlock_reg _ _ _ a1 s24.zero (by decide), g24_11]
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
    have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb25]; simp +decide only [runBlock, BInstr.run, svTt112b8, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_10, g24_11, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8)] := by rw [m25]; exact keep_kk24
    clear keep_kk24
    have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m25]; exact w24_74
    have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m25]; exact w24_78
    have w25_25c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m25]; exact w24_25c
    have w25_260 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m25]; exact w24_260
    have w25_27c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m25]; exact w24_27c
    have w25_280 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m25]; exact w24_280
    have w25_284 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m25]; exact w24_284
    have w25_288 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m25]; exact w24_288
    have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m25]; exact w24_420
    have w25_424 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m25]; exact w24_424
    have w25_428 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m25]; exact w24_428
    have w25_42c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m25]; exact w24_42c
    have b25_424 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m25]; exact b24_424
    have b25_425 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m25]; exact b24_425
    have b25_426 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m25]; exact b24_426
    have b25_427 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m25]; exact b24_427
    clear b24_427 b24_426 b24_425 b24_424 w24_42c w24_428 w24_424 w24_420 w24_288 w24_284 w24_280 w24_27c w24_260 w24_25c w24_78 w24_74 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_11 g24_10 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
    -- 0x12BA: j
    obtain ⟨n26, d26, u26⟩ := s25.jump E25.self sv_at_12ba (off' := 0x7A4) (by decide)
      (by rw [s25.pc]; decide)
    have s26 : St n26.mem SV n26 0x7A4 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
    have m26 : n26.mem = n25.mem := u26.mem
    have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
    have t26 : Steps n0 n26 := t25.trans (.single d26)
    have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
    have E26 : SvCode n26.mem := E25.fr F fr26
    have V26 : SvSaves B n26.mem v := V25.same m26
    have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, g25_2]
    have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, g25_3]
    have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, g25_4]
    have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u26.regs, g25_8]
    have g26_9 : reg n26 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [u26.regs, g25_9]
    have g26_10 : reg n26 a0 = BitVec.ofNat 32 0x0 := by rw [u26.regs, g25_10]
    have g26_11 : reg n26 a1 = BitVec.ofNat 32 0x0 := by rw [u26.regs, g25_11]
    have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, g25_18]
    have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, g25_19]
    have g26_20 : reg n26 (20 : Fin 32) = x20 := by rw [u26.regs, g25_20]
    have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [u26.regs, g25_21]
    have g26_22 : reg n26 (22 : Fin 32) = x22 := by rw [u26.regs, g25_22]
    have g26_23 : reg n26 (23 : Fin 32) = x23 := by rw [u26.regs, g25_23]
    have g26_24 : reg n26 (24 : Fin 32) = x24 := by rw [u26.regs, g25_24]
    have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [u26.regs, g25_25]
    have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [u26.regs, g25_26]
    have g26_27 : reg n26 (27 : Fin 32) = x27 := by rw [u26.regs, g25_27]
    have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8)] := by rw [m26]; exact keep_kk25
    clear keep_kk25
    have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m26]; exact w25_74
    have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m26]; exact w25_78
    have w26_25c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m26]; exact w25_25c
    have w26_260 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m26]; exact w25_260
    have w26_27c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m26]; exact w25_27c
    have w26_280 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m26]; exact w25_280
    have w26_284 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m26]; exact w25_284
    have w26_288 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m26]; exact w25_288
    have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m26]; exact w25_420
    have w26_424 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m26]; exact w25_424
    have w26_428 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m26]; exact w25_428
    have w26_42c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m26]; exact w25_42c
    have b26_424 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m26]; exact b25_424
    have b26_425 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m26]; exact b25_425
    have b26_426 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m26]; exact b25_426
    have b26_427 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m26]; exact b25_427
    clear b25_427 b25_426 b25_425 b25_424 w25_42c w25_428 w25_424 w25_420 w25_288 w25_284 w25_280 w25_27c w25_260 w25_25c w25_78 w25_74 g25_8 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_11 g25_10 g25_9 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
    exact .inl ⟨(fun ⟨tl9', h0', h1', h2', _⟩ => by rw [hr9] at h0'; cases h0'; rw [hr20] at h2'; cases h2'), sv_fail F E26 s26 t26 (fun x hx => (fR26 x hx).trans (fM x hx).symm) V26 hret g26_2 g26_18 hO g26_3 g26_4⟩
  obtain ⟨te20, hte20⟩ := ii_ok_elem hr20
  obtain ⟨d8_20, d12_20⟩ := A20 te20 hte20
  rw [hr20] at R20
  obtain ⟨a0_20, a1_20⟩ := R20
  have g20_10 : reg n20 a0 = BitVec.ofNat 32 0x0 := a0_20
  have g20_11 : reg n20 a1 = BitVec.ofNat 32 0x1 := by rw [a1_20]; rfl
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8)] := keep_kk19.trans K20
  clear keep_kk19
  have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K20.w32 (by decide) (by decide)).trans w19_74
  have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K20.w32 (by decide) (by decide)).trans w19_78
  have w20_25c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := (K20.w32 (by decide) (by decide)).trans w19_25c
  have w20_260 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := (K20.w32 (by decide) (by decide)).trans w19_260
  have w20_27c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K20.w32 (by decide) (by decide)).trans w19_27c
  have w20_280 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K20.w32 (by decide) (by decide)).trans w19_280
  have w20_284 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K20.w32 (by decide) (by decide)).trans w19_284
  have w20_288 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K20.w32 (by decide) (by decide)).trans w19_288
  have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := (K20.w32 (by decide) (by decide)).trans w19_420
  have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := (K20.w32 (by decide) (by decide)).trans w19_424
  have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := (K20.w32 (by decide) (by decide)).trans w19_428
  have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := (K20.w32 (by decide) (by decide)).trans w19_42c
  have b20_424 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := (K20.b8 (by decide) (by decide)).trans b19_424
  have b20_425 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := (K20.b8 (by decide) (by decide)).trans b19_425
  have b20_426 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := (K20.b8 (by decide) (by decide)).trans b19_426
  have b20_427 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := (K20.b8 (by decide) (by decide)).trans b19_427
  have w20_264 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len) := d8_20
  have w20_268 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len) := d12_20
  clear b19_427 b19_426 b19_425 b19_424 w19_42c w19_428 w19_424 w19_420 w19_288 w19_284 w19_280 w19_27c w19_268 w19_264 w19_260 w19_25c w19_78 w19_74 g19_11 g19_10 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
  -- 0x10FE
  obtain ⟨n21, c21, u21⟩ := s20.block svTt110fe E20.self svTt110fe_end
    ⟨trivial, trivial, trivial⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have s21 : St n21.mem SV n21 0x1102 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have rb21 : ∀ q, reg n21 q = (runBlock svTt110fe (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
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
  have g21_9 : reg n21 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by
    rw [rb21, runBlock_reg _ _ _ (9 : Fin 32) s20.zero (by decide), g20_9]
  have g21_11 : reg n21 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb21, runBlock_reg _ _ _ a1 s20.zero (by decide), g20_11]
  have g21_18 : reg n21 (18 : Fin 32) = out := by
    rw [rb21, runBlock_reg _ _ _ (18 : Fin 32) s20.zero (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by
    rw [rb21, runBlock_reg _ _ _ (19 : Fin 32) s20.zero (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = x20 := by
    rw [rb21, runBlock_reg _ _ _ (20 : Fin 32) s20.zero (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by
    rw [rb21, runBlock_reg _ _ _ (21 : Fin 32) s20.zero (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = x22 := by
    rw [rb21, runBlock_reg _ _ _ (22 : Fin 32) s20.zero (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = x23 := by
    rw [rb21, runBlock_reg _ _ _ (23 : Fin 32) s20.zero (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = x24 := by
    rw [rb21, runBlock_reg _ _ _ (24 : Fin 32) s20.zero (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = x25 := by
    rw [rb21, runBlock_reg _ _ _ (25 : Fin 32) s20.zero (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by
    rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = x27 := by
    rw [rb21, runBlock_reg _ _ _ (27 : Fin 32) s20.zero (by decide), g20_27]
  have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svTt110fe, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_10, g20_11, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_25, g20_26, g20_27, s20.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g21_10 : reg n21 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svTt110fe, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_10, g20_11, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_25, g20_26, g20_27, s20.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m21]; exact w20_74
  have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m21]; exact w20_78
  have w21_25c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m21]; exact w20_25c
  have w21_260 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m21]; exact w20_260
  have w21_264 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m21]; exact w20_264
  have w21_268 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m21]; exact w20_268
  have w21_27c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m21]; exact w20_27c
  have w21_280 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m21]; exact w20_280
  have w21_284 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m21]; exact w20_284
  have w21_288 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m21]; exact w20_288
  have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m21]; exact w20_420
  have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m21]; exact w20_424
  have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m21]; exact w20_428
  have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m21]; exact w20_42c
  have b21_424 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m21]; exact b20_424
  have b21_425 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m21]; exact b20_425
  have b21_426 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m21]; exact b20_426
  have b21_427 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m21]; exact b20_427
  clear w20_268 w20_264 b20_427 b20_426 b20_425 b20_424 w20_42c w20_428 w20_424 w20_420 w20_288 w20_284 w20_280 w20_27c w20_260 w20_25c w20_78 w20_74 g20_11 g20_10 a1_20 a0_20 d12_20 d8_20 g20_2 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 V20 E20 fR20 t20 fr20 A20 K20 rk20 sp20 s20 c20
  -- 0x1102: branch, not taken
  obtain ⟨n22, d22, u22⟩ := s21.notTaken E21.self 0x1106 sv_at_1102
    (by decide) (by rw [g21_10, s21.zero]; decide)
  have s22 : St n22.mem SV n22 0x1106 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans (.single d22)
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u22.regs, g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [u22.regs, g21_9]
  have g22_10 : reg n22 a0 = BitVec.ofNat 32 0x0 := by rw [u22.regs, g21_10]
  have g22_11 : reg n22 a1 = BitVec.ofNat 32 0x1 := by rw [u22.regs, g21_11]
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
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m22]; exact w21_74
  have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m22]; exact w21_78
  have w22_25c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m22]; exact w21_25c
  have w22_260 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m22]; exact w21_260
  have w22_264 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m22]; exact w21_264
  have w22_268 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m22]; exact w21_268
  have w22_27c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m22]; exact w21_27c
  have w22_280 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m22]; exact w21_280
  have w22_284 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m22]; exact w21_284
  have w22_288 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m22]; exact w21_288
  have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m22]; exact w21_420
  have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m22]; exact w21_424
  have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m22]; exact w21_428
  have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m22]; exact w21_42c
  have b22_424 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m22]; exact b21_424
  have b22_425 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m22]; exact b21_425
  have b22_426 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m22]; exact b21_426
  have b22_427 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m22]; exact b21_427
  clear b21_427 b21_426 b21_425 b21_424 w21_42c w21_428 w21_424 w21_420 w21_288 w21_284 w21_280 w21_27c w21_268 w21_264 w21_260 w21_25c w21_78 w21_74 g21_10 g21_8 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_11 g21_9 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
  -- 0x1106
  obtain ⟨n23, c23, u23⟩ := s22.block svTt11106 E22.self svTt11106_end
    ⟨trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem SV n23 0x1108 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock svTt11106 (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
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
  have g23_9 : reg n23 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by
    rw [rb23, runBlock_reg _ _ _ (9 : Fin 32) s22.zero (by decide), g22_9]
  have g23_10 : reg n23 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb23, runBlock_reg _ _ _ a0 s22.zero (by decide), g22_10]
  have g23_11 : reg n23 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb23, runBlock_reg _ _ _ a1 s22.zero (by decide), g22_11]
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
  have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svTt11106, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_10, g22_11, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m23]; exact w22_74
  have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m23]; exact w22_78
  have w23_25c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m23]; exact w22_25c
  have w23_260 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m23]; exact w22_260
  have w23_264 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m23]; exact w22_264
  have w23_268 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m23]; exact w22_268
  have w23_27c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m23]; exact w22_27c
  have w23_280 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m23]; exact w22_280
  have w23_284 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m23]; exact w22_284
  have w23_288 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m23]; exact w22_288
  have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m23]; exact w22_420
  have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m23]; exact w22_424
  have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m23]; exact w22_428
  have w23_42c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m23]; exact w22_42c
  have b23_424 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m23]; exact b22_424
  have b23_425 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m23]; exact b22_425
  have b23_426 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m23]; exact b22_426
  have b23_427 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m23]; exact b22_427
  clear b22_427 b22_426 b22_425 b22_424 w22_42c w22_428 w22_424 w22_420 w22_288 w22_284 w22_280 w22_27c w22_268 w22_264 w22_260 w22_25c w22_78 w22_74 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_11 g22_10 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
  -- 0x1108: branch, not taken
  obtain ⟨n24, d24, u24⟩ := s23.notTaken E23.self 0x110C sv_at_1108
    (by decide) (by rw [g23_8, s23.zero]; decide)
  have s24 : St n24.mem SV n24 0x110C (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u24.regs, g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [u24.regs, g23_9]
  have g24_10 : reg n24 a0 = BitVec.ofNat 32 0x0 := by rw [u24.regs, g23_10]
  have g24_11 : reg n24 a1 = BitVec.ofNat 32 0x1 := by rw [u24.regs, g23_11]
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
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m24]; exact w23_74
  have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m24]; exact w23_78
  have w24_25c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m24]; exact w23_25c
  have w24_260 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m24]; exact w23_260
  have w24_264 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m24]; exact w23_264
  have w24_268 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m24]; exact w23_268
  have w24_27c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m24]; exact w23_27c
  have w24_280 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m24]; exact w23_280
  have w24_284 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m24]; exact w23_284
  have w24_288 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m24]; exact w23_288
  have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m24]; exact w23_420
  have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m24]; exact w23_424
  have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m24]; exact w23_428
  have w24_42c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m24]; exact w23_42c
  have b24_424 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m24]; exact b23_424
  have b24_425 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m24]; exact b23_425
  have b24_426 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m24]; exact b23_426
  have b24_427 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m24]; exact b23_427
  clear b23_427 b23_426 b23_425 b23_424 w23_42c w23_428 w23_424 w23_420 w23_288 w23_284 w23_280 w23_27c w23_268 w23_264 w23_260 w23_25c w23_78 w23_74 g23_8 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_11 g23_10 g23_9 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
  -- 0x110C
  obtain ⟨n25, c25, u25⟩ := s24.block svTt1110c E24.self svTt1110c_end
    ⟨trivial, trivial, trivial⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have s25 : St n25.mem SV n25 0x1112 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have rb25 : ∀ q, reg n25 q = (runBlock svTt1110c (n24.mem, reg n24)).2 q := fun q => by rw [u25.regs]
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
  have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb25, runBlock_reg _ _ _ (8 : Fin 32) s24.zero (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by
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
  have g25_10 : reg n25 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svTt1110c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_10, g24_11, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g25_11 : reg n25 a1 = B + 0x21A0 + BitVec.ofNat 32 0x25C := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svTt1110c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_10, g24_11, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m25]; exact w24_74
  have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m25]; exact w24_78
  have w25_25c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m25]; exact w24_25c
  have w25_260 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m25]; exact w24_260
  have w25_264 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len) := by rw [m25]; exact w24_264
  have w25_268 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len) := by rw [m25]; exact w24_268
  have w25_27c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m25]; exact w24_27c
  have w25_280 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m25]; exact w24_280
  have w25_284 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m25]; exact w24_284
  have w25_288 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m25]; exact w24_288
  have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m25]; exact w24_420
  have w25_424 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl9.len := by rw [m25]; exact w24_424
  have w25_428 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m25]; exact w24_428
  have w25_42c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m25]; exact w24_42c
  have b25_424 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl9.len).extractLsb' 0 8 := by rw [m25]; exact b24_424
  have b25_425 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl9.len).extractLsb' 8 8 := by rw [m25]; exact b24_425
  have b25_426 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl9.len).extractLsb' 16 8 := by rw [m25]; exact b24_426
  have b25_427 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl9.len).extractLsb' 24 8 := by rw [m25]; exact b24_427
  clear b24_427 b24_426 b24_425 b24_424 w24_42c w24_428 w24_424 w24_420 w24_288 w24_284 w24_280 w24_27c w24_268 w24_264 w24_260 w24_25c w24_78 w24_74 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_11 g24_10 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
  -- 0x1112: sv_oidF
  obtain ⟨n26, c26, s26, sp26, rk26, K26, A26, Ok26, Er26, fr26⟩ := sv_oidF (oc := 0x420) (dc := 0x25C)
    F E25 s25 sv_at_1112 sv_at_1116 (by decide) (by decide) g25_2 g25_10 g25_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w25_264 w25_268 ((tst_in.contentW hr9).restW hte20)
  have t26 : Steps n0 n26 := t25.trans c26
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.keepL K26 (by decide)
  rw [sv_mb fR25 ((tst_in.contentW hr9).restW hte20)] at A26 Ok26 Er26
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [rk26 sp (by decide) (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk26 (3 : Fin 32) (by decide) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk26 (4 : Fin 32) (by decide) (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk26 (8 : Fin 32) (by decide) (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [rk26 (9 : Fin 32) (by decide) (by decide), g25_9]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [rk26 (18 : Fin 32) (by decide) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [rk26 (19 : Fin 32) (by decide) (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = x20 := by rw [rk26 (20 : Fin 32) (by decide) (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [rk26 (21 : Fin 32) (by decide) (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = x22 := by rw [rk26 (22 : Fin 32) (by decide) (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = x23 := by rw [rk26 (23 : Fin 32) (by decide) (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = x24 := by rw [rk26 (24 : Fin 32) (by decide) (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [rk26 (25 : Fin 32) (by decide) (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [rk26 (26 : Fin 32) (by decide) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = x27 := by rw [rk26 (27 : Fin 32) (by decide) (by decide), g25_27]
  obtain ⟨r26, hr26⟩ : ∃ r, derContent (((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) (derOid (memBytes M0 (((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) ((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)).toNat)) = r := ⟨_, rfl⟩
  rcases r26 with er26 | ⟨op26, ol26⟩
  · obtain ⟨z26, -⟩ := Er26 er26 hr26
    have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8)] := keep_kk25.trans K26
    clear keep_kk25
    have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K26.w32 (by decide) (by decide)).trans w25_74
    have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K26.w32 (by decide) (by decide)).trans w25_78
    have w26_25c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := (K26.w32 (by decide) (by decide)).trans w25_25c
    have w26_260 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := (K26.w32 (by decide) (by decide)).trans w25_260
    have w26_27c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K26.w32 (by decide) (by decide)).trans w25_27c
    have w26_280 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K26.w32 (by decide) (by decide)).trans w25_280
    have w26_284 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K26.w32 (by decide) (by decide)).trans w25_284
    have w26_288 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K26.w32 (by decide) (by decide)).trans w25_288
    have w26_428 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := (K26.w32 (by decide) (by decide)).trans w25_428
    have w26_42c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := (K26.w32 (by decide) (by decide)).trans w25_42c
    have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z26
    clear b25_427 b25_426 b25_425 b25_424 w25_42c w25_428 w25_424 w25_420 w25_288 w25_284 w25_280 w25_27c w25_268 w25_264 w25_260 w25_25c w25_78 w25_74 g25_11 g25_10 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
    -- 0x111A: lw
    obtain ⟨n27, d27, u27⟩ := s26.lw E26.self sv_at_111a (off' := 0x111E) (by decide)
      (by rw [g26_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s27 : St n27.mem SV n27 0x111E (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
    have m27 : n27.mem = n26.mem := u27.mem
    have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
    have t27 : Steps n0 n27 := t26.trans (.single d27)
    have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
    have E27 : SvCode n27.mem := E26.fr F fr27
    have V27 : SvSaves B n27.mem v := V26.same m27
    have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_2]
    have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_3]
    have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_4]
    have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_8]
    have g27_9 : reg n27 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [u27.regs, upd_ne (by decide) (by decide), g26_9]
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
    have g27_10 : reg n27 a0 = 0 := by
      rw [u27.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g26_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w26_420]
    have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8)] := by rw [m27]; exact keep_kk26
    clear keep_kk26
    have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m27]; exact w26_74
    have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m27]; exact w26_78
    have w27_25c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m27]; exact w26_25c
    have w27_260 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m27]; exact w26_260
    have w27_27c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m27]; exact w26_27c
    have w27_280 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m27]; exact w26_280
    have w27_284 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m27]; exact w26_284
    have w27_288 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m27]; exact w26_288
    have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m27]; exact w26_420
    have w27_428 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m27]; exact w26_428
    have w27_42c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m27]; exact w26_42c
    clear w26_420 w26_42c w26_428 w26_288 w26_284 w26_280 w26_27c w26_260 w26_25c w26_78 w26_74 z26
    -- 0x111E: branch, taken
    obtain ⟨n28, d28, u28⟩ := s27.taken E27.self 0x12AA sv_at_111e
      (by decide) (by rw [g27_10, s27.zero]; rfl)
    have s28 : St n28.mem SV n28 0x12AA (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
    have m28 : n28.mem = n27.mem := u28.mem
    have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
    have t28 : Steps n0 n28 := t27.trans (.single d28)
    have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
    have E28 : SvCode n28.mem := E27.fr F fr28
    have V28 : SvSaves B n28.mem v := V27.same m28
    have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, g27_2]
    have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, g27_3]
    have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, g27_4]
    have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u28.regs, g27_8]
    have g28_9 : reg n28 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [u28.regs, g27_9]
    have g28_10 : reg n28 a0 = 0 := by rw [u28.regs, g27_10]
    have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, g27_18]
    have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, g27_19]
    have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [u28.regs, g27_20]
    have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [u28.regs, g27_21]
    have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [u28.regs, g27_22]
    have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [u28.regs, g27_23]
    have g28_24 : reg n28 (24 : Fin 32) = x24 := by rw [u28.regs, g27_24]
    have g28_25 : reg n28 (25 : Fin 32) = x25 := by rw [u28.regs, g27_25]
    have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [u28.regs, g27_26]
    have g28_27 : reg n28 (27 : Fin 32) = x27 := by rw [u28.regs, g27_27]
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8)] := by rw [m28]; exact keep_kk27
    clear keep_kk27
    have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m28]; exact w27_74
    have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m28]; exact w27_78
    have w28_25c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m28]; exact w27_25c
    have w28_260 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m28]; exact w27_260
    have w28_27c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m28]; exact w27_27c
    have w28_280 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m28]; exact w27_280
    have w28_284 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m28]; exact w27_284
    have w28_288 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m28]; exact w27_288
    have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m28]; exact w27_420
    have w28_428 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m28]; exact w27_428
    have w28_42c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m28]; exact w27_42c
    clear w27_42c w27_428 w27_420 w27_288 w27_284 w27_280 w27_27c w27_260 w27_25c w27_78 w27_74 g27_10 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
    -- 0x12AA: lbu
    obtain ⟨n29, d29, u29⟩ := s28.lbu E28.self sv_at_12aa (off' := 0x12AE) (by decide)
    have s29 : St n29.mem SV n29 0x12AE (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
    have t29 : Steps n0 n29 := t28.trans (.single d29)
    have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
    have E29 : SvCode n29.mem := E28.fr F fr29
    have V29 : SvSaves B n29.mem v := V28.same m29
    have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_2]
    have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_3]
    have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_4]
    have g29_9 : reg n29 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [u29.regs, upd_ne (by decide) (by decide), g28_9]
    have g29_10 : reg n29 a0 = 0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_10]
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
    have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8)] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m29]; exact w28_74
    have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m29]; exact w28_78
    have w29_25c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m29]; exact w28_25c
    have w29_260 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m29]; exact w28_260
    have w29_27c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m29]; exact w28_27c
    have w29_280 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m29]; exact w28_280
    have w29_284 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_284
    have w29_288 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_288
    have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m29]; exact w28_420
    have w29_428 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m29]; exact w28_428
    have w29_42c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m29]; exact w28_42c
    clear w28_42c w28_428 w28_420 w28_288 w28_284 w28_280 w28_27c w28_260 w28_25c w28_78 w28_74 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_10 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
    -- 0x12AE: j
    obtain ⟨n30, d30, u30⟩ := s29.jump E29.self sv_at_12ae (off' := 0x7A4) (by decide)
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
    have g30_9 : reg n30 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [u30.regs, g29_9]
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
    have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8)] := by rw [m30]; exact keep_kk29
    clear keep_kk29
    have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m30]; exact w29_74
    have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m30]; exact w29_78
    have w30_25c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m30]; exact w29_25c
    have w30_260 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m30]; exact w29_260
    have w30_27c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m30]; exact w29_27c
    have w30_280 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m30]; exact w29_280
    have w30_284 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m30]; exact w29_284
    have w30_288 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m30]; exact w29_288
    have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m30]; exact w29_420
    have w30_428 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m30]; exact w29_428
    have w30_42c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m30]; exact w29_42c
    clear w29_42c w29_428 w29_420 w29_288 w29_284 w29_280 w29_27c w29_260 w29_25c w29_78 w29_74 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_10 g29_9 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
    exact .inl ⟨(fun ⟨tl9', h0', h1', h2', te20', h3', op26', ol26', h4', _⟩ => by rw [hr9] at h0'; cases h0'; rw [hr20] at h2'; cases h2'; rw [hte20] at h3'; cases h3'; rw [hr26] at h4'; cases h4'), sv_fail F E30 s30 t30 (fun x hx => (fR30 x hx).trans (fM x hx).symm) V30 hret g30_2 g30_18 hO g30_3 g30_4⟩
  obtain ⟨to26, ht26, -, -⟩ := oid_ok_content hr26
  obtain ⟨p0_26, p4_26⟩ := Ok26 op26 ol26 hr26
  obtain ⟨d8_26, d12_26⟩ := A26 to26 (derOid_ok_elem ht26)
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8)] := keep_kk25.trans K26
  clear keep_kk25
  have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K26.w32 (by decide) (by decide)).trans w25_74
  have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K26.w32 (by decide) (by decide)).trans w25_78
  have w26_25c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := (K26.w32 (by decide) (by decide)).trans w25_25c
  have w26_260 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := (K26.w32 (by decide) (by decide)).trans w25_260
  have w26_27c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K26.w32 (by decide) (by decide)).trans w25_27c
  have w26_280 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K26.w32 (by decide) (by decide)).trans w25_280
  have w26_284 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K26.w32 (by decide) (by decide)).trans w25_284
  have w26_288 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K26.w32 (by decide) (by decide)).trans w25_288
  have w26_428 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := (K26.w32 (by decide) (by decide)).trans w25_428
  have w26_42c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := (K26.w32 (by decide) (by decide)).trans w25_42c
  have w26_264 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len) := d8_26
  have w26_268 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len) := d12_26
  have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op26 := p0_26
  have w26_424 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol26 := p4_26
  clear b25_427 b25_426 b25_425 b25_424 w25_42c w25_428 w25_424 w25_420 w25_288 w25_284 w25_280 w25_27c w25_268 w25_264 w25_260 w25_25c w25_78 w25_74 g25_11 g25_10 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
  -- 0x111A: lw
  obtain ⟨n27, d27, u27⟩ := s26.lw E26.self sv_at_111a (off' := 0x111E) (by decide)
    (by rw [g26_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s27 : St n27.mem SV n27 0x111E (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans (.single d27)
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [u27.regs, upd_ne (by decide) (by decide), g26_9]
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
  have g27_10 : reg n27 a0 = op26 := by
    rw [u27.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g26_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w26_420]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m27]; exact w26_74
  have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m27]; exact w26_78
  have w27_25c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m27]; exact w26_25c
  have w27_260 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m27]; exact w26_260
  have w27_264 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len) := by rw [m27]; exact w26_264
  have w27_268 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len) := by rw [m27]; exact w26_268
  have w27_27c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m27]; exact w26_27c
  have w27_280 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m27]; exact w26_280
  have w27_284 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m27]; exact w26_284
  have w27_288 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m27]; exact w26_288
  have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op26 := by rw [m27]; exact w26_420
  have w27_424 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol26 := by rw [m27]; exact w26_424
  have w27_428 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m27]; exact w26_428
  have w27_42c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m27]; exact w26_42c
  clear w26_424 w26_420 w26_268 w26_264 w26_42c w26_428 w26_288 w26_284 w26_280 w26_27c w26_260 w26_25c w26_78 w26_74 d12_26 d8_26 p4_26 p0_26 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 Er26 Ok26 A26 K26 rk26 sp26 s26 c26
  -- 0x111E: branch, not taken
  obtain ⟨n28, d28, u28⟩ := s27.notTaken E27.self 0x1122 sv_at_111e
    (by decide) (by rw [g27_10, s27.zero]; exact br_beq_f ((((tst_in.contentW hr9).restW hte20).oidIn hr26).pos_ne))
  have s28 : St n28.mem SV n28 0x1122 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
  have t28 : Steps n0 n28 := t27.trans (.single d28)
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.same m28
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u28.regs, g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [u28.regs, g27_9]
  have g28_10 : reg n28 a0 = op26 := by rw [u28.regs, g27_10]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [u28.regs, g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [u28.regs, g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [u28.regs, g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [u28.regs, g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = x24 := by rw [u28.regs, g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = x25 := by rw [u28.regs, g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [u28.regs, g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = x27 := by rw [u28.regs, g27_27]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8)] := by rw [m28]; exact keep_kk27
  clear keep_kk27
  have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m28]; exact w27_74
  have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m28]; exact w27_78
  have w28_25c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m28]; exact w27_25c
  have w28_260 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m28]; exact w27_260
  have w28_264 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len) := by rw [m28]; exact w27_264
  have w28_268 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len) := by rw [m28]; exact w27_268
  have w28_27c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m28]; exact w27_27c
  have w28_280 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m28]; exact w27_280
  have w28_284 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m28]; exact w27_284
  have w28_288 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m28]; exact w27_288
  have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op26 := by rw [m28]; exact w27_420
  have w28_424 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol26 := by rw [m28]; exact w27_424
  have w28_428 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m28]; exact w27_428
  have w28_42c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m28]; exact w27_42c
  clear w27_42c w27_428 w27_424 w27_420 w27_288 w27_284 w27_280 w27_27c w27_268 w27_264 w27_260 w27_25c w27_78 w27_74 g27_10 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
  -- 0x1122
  obtain ⟨n29, c29, u29⟩ := s28.block svTt11122 E28.self svTt11122_end
    ⟨trivial, trivial, trivial⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have s29 : St n29.mem SV n29 0x1128 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have rb29 : ∀ q, reg n29 q = (runBlock svTt11122 (n28.mem, reg n28)).2 q := fun q => by rw [u29.regs]
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
  have g29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb29, runBlock_reg _ _ _ (8 : Fin 32) s28.zero (by decide), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by
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
  have g29_24 : reg n29 (24 : Fin 32) = x24 := by
    rw [rb29, runBlock_reg _ _ _ (24 : Fin 32) s28.zero (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = x25 := by
    rw [rb29, runBlock_reg _ _ _ (25 : Fin 32) s28.zero (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by
    rw [rb29, runBlock_reg _ _ _ (26 : Fin 32) s28.zero (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = x27 := by
    rw [rb29, runBlock_reg _ _ _ (27 : Fin 32) s28.zero (by decide), g28_27]
  have g29_10 : reg n29 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svTt11122, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_10, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g29_11 : reg n29 a1 = B + 0x21A0 + BitVec.ofNat 32 0x25C := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svTt11122, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_10, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m29]; exact w28_74
  have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m29]; exact w28_78
  have w29_25c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m29]; exact w28_25c
  have w29_260 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m29]; exact w28_260
  have w29_264 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len) := by rw [m29]; exact w28_264
  have w29_268 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len) := by rw [m29]; exact w28_268
  have w29_27c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m29]; exact w28_27c
  have w29_280 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m29]; exact w28_280
  have w29_284 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_284
  have w29_288 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_288
  have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = op26 := by rw [m29]; exact w28_420
  have w29_424 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ol26 := by rw [m29]; exact w28_424
  have w29_428 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m29]; exact w28_428
  have w29_42c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl9.len := by rw [m29]; exact w28_42c
  clear w28_42c w28_428 w28_424 w28_420 w28_288 w28_284 w28_280 w28_27c w28_268 w28_264 w28_260 w28_25c w28_78 w28_74 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_10 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
  -- 0x1128: sv_seqF
  obtain ⟨n30, c30, s30, sp30, rk30, K30, Ok30, Er30, fr30⟩ := sv_seqF (oc := 0x420) (dc := 0x25C)
    F E29 s29 sv_at_1128 sv_at_112c (by decide) (by decide) g29_2 g29_10 g29_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w29_264 w29_268 (((tst_in.contentW hr9).restW hte20).restW (derOid_ok_elem ht26))
  have t30 : Steps n0 n30 := t29.trans c30
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.keepL K30 (by decide)
  rw [sv_mb fR29 (((tst_in.contentW hr9).restW hte20).restW (derOid_ok_elem ht26))] at Ok30 Er30
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [rk30 sp (by decide) (by decide), g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk30 (3 : Fin 32) (by decide) (by decide), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk30 (4 : Fin 32) (by decide) (by decide), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk30 (8 : Fin 32) (by decide) (by decide), g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = (tp) + BitVec.ofNat 32 tl9.header := by rw [rk30 (9 : Fin 32) (by decide) (by decide), g29_9]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [rk30 (18 : Fin 32) (by decide) (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [rk30 (19 : Fin 32) (by decide) (by decide), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = x20 := by rw [rk30 (20 : Fin 32) (by decide) (by decide), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = x21 := by rw [rk30 (21 : Fin 32) (by decide) (by decide), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = x22 := by rw [rk30 (22 : Fin 32) (by decide) (by decide), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = x23 := by rw [rk30 (23 : Fin 32) (by decide) (by decide), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = x24 := by rw [rk30 (24 : Fin 32) (by decide) (by decide), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = x25 := by rw [rk30 (25 : Fin 32) (by decide) (by decide), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [rk30 (26 : Fin 32) (by decide) (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = x27 := by rw [rk30 (27 : Fin 32) (by decide) (by decide), g29_27]
  obtain ⟨r30, hr30⟩ : ∃ r, derElement 0x30 (memBytes M0 ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)).toNat) = r := ⟨_, rfl⟩
  rcases r30 with er30 | tl30
  · obtain ⟨z30, -⟩ := Er30 er30 hr30
    have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8)] := keep_kk29.trans K30
    clear keep_kk29
    have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K30.w32 (by decide) (by decide)).trans w29_74
    have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K30.w32 (by decide) (by decide)).trans w29_78
    have w30_25c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := (K30.w32 (by decide) (by decide)).trans w29_25c
    have w30_260 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := (K30.w32 (by decide) (by decide)).trans w29_260
    have w30_27c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K30.w32 (by decide) (by decide)).trans w29_27c
    have w30_280 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K30.w32 (by decide) (by decide)).trans w29_280
    have w30_284 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K30.w32 (by decide) (by decide)).trans w29_284
    have w30_288 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K30.w32 (by decide) (by decide)).trans w29_288
    have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z30
    clear w29_42c w29_428 w29_424 w29_420 w29_288 w29_284 w29_280 w29_27c w29_268 w29_264 w29_260 w29_25c w29_78 w29_74 g29_11 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29
    -- 0x1130: lw
    obtain ⟨n31, d31, u31⟩ := s30.lw E30.self sv_at_1130 (off' := 0x1134) (by decide)
      (by rw [g30_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s31 : St n31.mem SV n31 0x1134 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
    have m31 : n31.mem = n30.mem := u31.mem
    have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
    have t31 : Steps n0 n31 := t30.trans (.single d31)
    have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
    have E31 : SvCode n31.mem := E30.fr F fr31
    have V31 : SvSaves B n31.mem v := V30.same m31
    have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_2]
    have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_3]
    have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_4]
    have g31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_8]
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
    have g31_9 : reg n31 (9 : Fin 32) = 0 := by
      rw [u31.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g30_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w30_420]
    have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8)] := by rw [m31]; exact keep_kk30
    clear keep_kk30
    have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m31]; exact w30_74
    have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m31]; exact w30_78
    have w31_25c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m31]; exact w30_25c
    have w31_260 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m31]; exact w30_260
    have w31_27c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m31]; exact w30_27c
    have w31_280 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m31]; exact w30_280
    have w31_284 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m31]; exact w30_284
    have w31_288 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m31]; exact w30_288
    have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m31]; exact w30_420
    clear w30_420 w30_288 w30_284 w30_280 w30_27c w30_260 w30_25c w30_78 w30_74 z30
    -- 0x1134: lbu
    obtain ⟨n32, d32, u32⟩ := s31.lbu E31.self sv_at_1134 (off' := 0x1138) (by decide)
    have s32 : St n32.mem SV n32 0x1138 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
    have m32 : n32.mem = n31.mem := u32.mem
    have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
    have t32 : Steps n0 n32 := t31.trans (.single d32)
    have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
    have E32 : SvCode n32.mem := E31.fr F fr32
    have V32 : SvSaves B n32.mem v := V31.same m32
    have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_2]
    have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_3]
    have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_4]
    have g32_9 : reg n32 (9 : Fin 32) = 0 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_9]
    have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, upd_ne (by decide) (by decide), g31_18]
    have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_19]
    have g32_20 : reg n32 (20 : Fin 32) = x20 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_20]
    have g32_21 : reg n32 (21 : Fin 32) = x21 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_21]
    have g32_22 : reg n32 (22 : Fin 32) = x22 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_22]
    have g32_23 : reg n32 (23 : Fin 32) = x23 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_23]
    have g32_24 : reg n32 (24 : Fin 32) = x24 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_24]
    have g32_25 : reg n32 (25 : Fin 32) = x25 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_25]
    have g32_26 : reg n32 (26 : Fin 32) = x26 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_26]
    have g32_27 : reg n32 (27 : Fin 32) = x27 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_27]
    have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8)] := by rw [m32]; exact keep_kk31
    clear keep_kk31
    have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m32]; exact w31_74
    have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m32]; exact w31_78
    have w32_25c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m32]; exact w31_25c
    have w32_260 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m32]; exact w31_260
    have w32_27c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m32]; exact w31_27c
    have w32_280 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m32]; exact w31_280
    have w32_284 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m32]; exact w31_284
    have w32_288 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m32]; exact w31_288
    have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m32]; exact w31_420
    clear w31_420 w31_288 w31_284 w31_280 w31_27c w31_260 w31_25c w31_78 w31_74 g31_9 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
    -- 0x1138: branch, taken
    obtain ⟨n33, d33, u33⟩ := s32.taken E32.self 0x7A4 sv_at_1138
      (by decide) (by rw [g32_9, s32.zero]; rfl)
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
    have g33_9 : reg n33 (9 : Fin 32) = 0 := by rw [u33.regs, g32_9]
    have g33_18 : reg n33 (18 : Fin 32) = out := by rw [u33.regs, g32_18]
    have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [u33.regs, g32_19]
    have g33_20 : reg n33 (20 : Fin 32) = x20 := by rw [u33.regs, g32_20]
    have g33_21 : reg n33 (21 : Fin 32) = x21 := by rw [u33.regs, g32_21]
    have g33_22 : reg n33 (22 : Fin 32) = x22 := by rw [u33.regs, g32_22]
    have g33_23 : reg n33 (23 : Fin 32) = x23 := by rw [u33.regs, g32_23]
    have g33_24 : reg n33 (24 : Fin 32) = x24 := by rw [u33.regs, g32_24]
    have g33_25 : reg n33 (25 : Fin 32) = x25 := by rw [u33.regs, g32_25]
    have g33_26 : reg n33 (26 : Fin 32) = x26 := by rw [u33.regs, g32_26]
    have g33_27 : reg n33 (27 : Fin 32) = x27 := by rw [u33.regs, g32_27]
    have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8)] := by rw [m33]; exact keep_kk32
    clear keep_kk32
    have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m33]; exact w32_74
    have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m33]; exact w32_78
    have w33_25c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m33]; exact w32_25c
    have w33_260 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m33]; exact w32_260
    have w33_27c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m33]; exact w32_27c
    have w33_280 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m33]; exact w32_280
    have w33_284 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m33]; exact w32_284
    have w33_288 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m33]; exact w32_288
    have w33_420 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m33]; exact w32_420
    clear w32_420 w32_288 w32_284 w32_280 w32_27c w32_260 w32_25c w32_78 w32_74 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_9 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
    exact .inl ⟨(fun ⟨tl9', h0', h1', h2', te20', h3', op26', ol26', h4', to26', h5', tl30', h6', _⟩ => by rw [hr9] at h0'; cases h0'; rw [hr20] at h2'; cases h2'; rw [hte20] at h3'; cases h3'; rw [hr26] at h4'; cases h4'; rw [ht26] at h5'; cases h5'; rw [hr30] at h6'; cases h6'), sv_fail F E33 s33 t33 (fun x hx => (fR33 x hx).trans (fM x hx).symm) V33 hret g33_2 g33_18 hO g33_3 g33_4⟩
  obtain ⟨o0_30, o4_30, o8_30, o12_30, d8_30, d12_30⟩ := Ok30 tl30 hr30
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8)] := keep_kk29.trans K30
  clear keep_kk29
  have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K30.w32 (by decide) (by decide)).trans w29_74
  have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K30.w32 (by decide) (by decide)).trans w29_78
  have w30_25c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := (K30.w32 (by decide) (by decide)).trans w29_25c
  have w30_260 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := (K30.w32 (by decide) (by decide)).trans w29_260
  have w30_27c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K30.w32 (by decide) (by decide)).trans w29_27c
  have w30_280 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K30.w32 (by decide) (by decide)).trans w29_280
  have w30_284 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K30.w32 (by decide) (by decide)).trans w29_284
  have w30_288 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K30.w32 (by decide) (by decide)).trans w29_288
  have w30_264 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := d8_30
  have w30_268 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := d12_30
  have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := o0_30
  have w30_424 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := o4_30
  have w30_428 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := o8_30
  have w30_42c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := o12_30
  clear w29_42c w29_428 w29_424 w29_420 w29_288 w29_284 w29_280 w29_27c w29_268 w29_264 w29_260 w29_25c w29_78 w29_74 g29_11 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29
  -- 0x1130: lw
  obtain ⟨n31, d31, u31⟩ := s30.lw E30.self sv_at_1130 (off' := 0x1134) (by decide)
    (by rw [g30_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s31 : St n31.mem SV n31 0x1134 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans (.single d31)
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_8]
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
  have g31_9 : reg n31 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by
    rw [u31.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g30_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w30_420]
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m31]; exact w30_74
  have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m31]; exact w30_78
  have w31_25c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m31]; exact w30_25c
  have w31_260 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m31]; exact w30_260
  have w31_264 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m31]; exact w30_264
  have w31_268 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m31]; exact w30_268
  have w31_27c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m31]; exact w30_27c
  have w31_280 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m31]; exact w30_280
  have w31_284 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m31]; exact w30_284
  have w31_288 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m31]; exact w30_288
  have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m31]; exact w30_420
  have w31_424 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := by rw [m31]; exact w30_424
  have w31_428 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m31]; exact w30_428
  have w31_42c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m31]; exact w30_42c
  clear w30_42c w30_428 w30_424 w30_420 w30_268 w30_264 w30_288 w30_284 w30_280 w30_27c w30_260 w30_25c w30_78 w30_74 d12_30 d8_30 o12_30 o8_30 o4_30 o0_30 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 Er30 Ok30 K30 rk30 sp30 s30 c30
  -- 0x1134: lbu
  obtain ⟨n32, d32, u32⟩ := s31.lbu E31.self sv_at_1134 (off' := 0x1138) (by decide)
  have b31_424 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := by
    have h := byte_of_ld w31_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact h.1
  have s32 : St n32.mem SV n32 0x1138 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans (.single d32)
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_4]
  have g32_9 : reg n32 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u32.regs, upd_ne (by decide) (by decide), g31_9]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, upd_ne (by decide) (by decide), g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = x20 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = x21 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = x22 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = x23 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = x24 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = x25 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = x26 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = x27 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_27]
  have g32_8 : reg n32 (8 : Fin 32) = ((BitVec.ofNat 32 tl30.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [u32.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g31_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b31_424]
  have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8)] := by rw [m32]; exact keep_kk31
  clear keep_kk31
  have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m32]; exact w31_74
  have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m32]; exact w31_78
  have w32_25c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m32]; exact w31_25c
  have w32_260 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m32]; exact w31_260
  have w32_264 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m32]; exact w31_264
  have w32_268 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m32]; exact w31_268
  have w32_27c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m32]; exact w31_27c
  have w32_280 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m32]; exact w31_280
  have w32_284 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m32]; exact w31_284
  have w32_288 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m32]; exact w31_288
  have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m32]; exact w31_420
  have w32_424 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := by rw [m32]; exact w31_424
  have w32_428 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m32]; exact w31_428
  have w32_42c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m32]; exact w31_42c
  have b32_424 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := by rw [m32]; exact b31_424
  clear w31_42c w31_428 w31_424 w31_420 w31_288 w31_284 w31_280 w31_27c w31_268 w31_264 w31_260 w31_25c w31_78 w31_74 g31_9 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
  -- 0x1138: branch, not taken
  obtain ⟨n33, d33, u33⟩ := s32.notTaken E32.self 0x113C sv_at_1138
    (by decide) (by rw [g32_9, s32.zero]; exact br_beq_f ((((tst_in.contentW hr9).restW hte20).restW (derOid_ok_elem ht26)).ok_ne hr30))
  have s33 : St n33.mem SV n33 0x113C (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
  have t33 : Steps n0 n33 := t32.trans (.single d33)
  have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.same m33
  have g33_2 : reg n33 sp = B + 0x21A0 := by rw [u33.regs, g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u33.regs, g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u33.regs, g32_4]
  have g33_8 : reg n33 (8 : Fin 32) = ((BitVec.ofNat 32 tl30.len).extractLsb' 0 8).zeroExtend 32 := by rw [u33.regs, g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u33.regs, g32_9]
  have g33_18 : reg n33 (18 : Fin 32) = out := by rw [u33.regs, g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [u33.regs, g32_19]
  have g33_20 : reg n33 (20 : Fin 32) = x20 := by rw [u33.regs, g32_20]
  have g33_21 : reg n33 (21 : Fin 32) = x21 := by rw [u33.regs, g32_21]
  have g33_22 : reg n33 (22 : Fin 32) = x22 := by rw [u33.regs, g32_22]
  have g33_23 : reg n33 (23 : Fin 32) = x23 := by rw [u33.regs, g32_23]
  have g33_24 : reg n33 (24 : Fin 32) = x24 := by rw [u33.regs, g32_24]
  have g33_25 : reg n33 (25 : Fin 32) = x25 := by rw [u33.regs, g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = x26 := by rw [u33.regs, g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = x27 := by rw [u33.regs, g32_27]
  have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8)] := by rw [m33]; exact keep_kk32
  clear keep_kk32
  have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m33]; exact w32_74
  have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m33]; exact w32_78
  have w33_25c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m33]; exact w32_25c
  have w33_260 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m33]; exact w32_260
  have w33_264 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m33]; exact w32_264
  have w33_268 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m33]; exact w32_268
  have w33_27c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m33]; exact w32_27c
  have w33_280 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m33]; exact w32_280
  have w33_284 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m33]; exact w32_284
  have w33_288 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m33]; exact w32_288
  have w33_420 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m33]; exact w32_420
  have w33_424 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := by rw [m33]; exact w32_424
  have w33_428 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m33]; exact w32_428
  have w33_42c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m33]; exact w32_42c
  have b33_424 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := by rw [m33]; exact b32_424
  clear b32_424 w32_42c w32_428 w32_424 w32_420 w32_288 w32_284 w32_280 w32_27c w32_268 w32_264 w32_260 w32_25c w32_78 w32_74 g32_8 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_9 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 b31_424 u32 d32
  -- 0x113C
  obtain ⟨n34, c34, u34⟩ := s33.block svTt1113c E33.self svTt1113c_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m34 : n34.mem = n33.mem := u34.mem
  have s34 : St n34.mem SV n34 0x1146 (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
  have rb34 : ∀ q, reg n34 q = (runBlock svTt1113c (n33.mem, reg n33)).2 q := fun q => by rw [u34.regs]
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
  have g34_8 : reg n34 (8 : Fin 32) = ((BitVec.ofNat 32 tl30.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb34, runBlock_reg _ _ _ (8 : Fin 32) s33.zero (by decide), g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by
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
  have g34_24 : reg n34 (24 : Fin 32) = x24 := by
    rw [rb34, runBlock_reg _ _ _ (24 : Fin 32) s33.zero (by decide), g33_24]
  have g34_25 : reg n34 (25 : Fin 32) = x25 := by
    rw [rb34, runBlock_reg _ _ _ (25 : Fin 32) s33.zero (by decide), g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = x26 := by
    rw [rb34, runBlock_reg _ _ _ (26 : Fin 32) s33.zero (by decide), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = x27 := by
    rw [rb34, runBlock_reg _ _ _ (27 : Fin 32) s33.zero (by decide), g33_27]
  have g34_10 : reg n34 a0 = B + 0x21A0 + BitVec.ofNat 32 0x3E5 := by
    rw [rb34]; simp +decide only [runBlock, BInstr.run, svTt1113c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g33_2, g33_3, g33_4, g33_8, g33_9, g33_18, g33_19, g33_20, g33_21, g33_22, g33_23, g33_24, g33_25, g33_26, g33_27, s33.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g34_11 : reg n34 a1 = B + 0x21A0 + BitVec.ofNat 32 0x425 := by
    rw [rb34]; simp +decide only [runBlock, BInstr.run, svTt1113c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g33_2, g33_3, g33_4, g33_8, g33_9, g33_18, g33_19, g33_20, g33_21, g33_22, g33_23, g33_24, g33_25, g33_26, g33_27, s33.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g34_12 : reg n34 a2 = BitVec.ofNat 32 0xB := by
    rw [rb34]; simp +decide only [runBlock, BInstr.run, svTt1113c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g33_2, g33_3, g33_4, g33_8, g33_9, g33_18, g33_19, g33_20, g33_21, g33_22, g33_23, g33_24, g33_25, g33_26, g33_27, s33.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8)] := by rw [m34]; exact keep_kk33
  clear keep_kk33
  have w34_74 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m34]; exact w33_74
  have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m34]; exact w33_78
  have w34_25c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m34]; exact w33_25c
  have w34_260 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m34]; exact w33_260
  have w34_264 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m34]; exact w33_264
  have w34_268 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m34]; exact w33_268
  have w34_27c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m34]; exact w33_27c
  have w34_280 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m34]; exact w33_280
  have w34_284 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m34]; exact w33_284
  have w34_288 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m34]; exact w33_288
  have w34_420 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m34]; exact w33_420
  have w34_424 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := by rw [m34]; exact w33_424
  have w34_428 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m34]; exact w33_428
  have w34_42c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m34]; exact w33_42c
  have b34_424 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := by rw [m34]; exact b33_424
  clear b33_424 w33_42c w33_428 w33_424 w33_420 w33_288 w33_284 w33_280 w33_27c w33_268 w33_264 w33_260 w33_25c w33_78 w33_74 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 m33 s33 u33 d33
  have b34_425 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := by
    have h := byte_of_ld w34_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x425 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 1 by sv_addr]; exact h.2.1
  have b34_426 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := by
    have h := byte_of_ld w34_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x426 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 2 by sv_addr]; exact h.2.2.1
  have b34_427 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := by
    have h := byte_of_ld w34_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x427 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 3 by sv_addr]; exact h.2.2.2
  -- 0x1146: memcpy
  obtain ⟨n35, P35, K35, X35⟩ := sv_mc (c := 0x3E5) (d := 0x425) (N := 0xB) F E34 s34 sv_at_1146 sv_at_114a
    (by decide) (by decide) g34_2 g34_10 g34_11 g34_12
    (by decide) (by decide) (by decide)
  have s35 := P35.st
  have fr35 := P35.fr
  have t35 : Steps n0 n35 := t34.trans P35.steps
  have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.keep K35 (by decide)
  have g35_2 : reg n35 sp = B + 0x21A0 := by rw [P35.regs sp (by decide), g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P35.regs (3 : Fin 32) (by decide), g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P35.regs (4 : Fin 32) (by decide), g34_4]
  have g35_8 : reg n35 (8 : Fin 32) = ((BitVec.ofNat 32 tl30.len).extractLsb' 0 8).zeroExtend 32 := by rw [P35.regs (8 : Fin 32) (by decide), g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [P35.regs (9 : Fin 32) (by decide), g34_9]
  have g35_18 : reg n35 (18 : Fin 32) = out := by rw [P35.regs (18 : Fin 32) (by decide), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [P35.regs (19 : Fin 32) (by decide), g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = x20 := by rw [P35.regs (20 : Fin 32) (by decide), g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = x21 := by rw [P35.regs (21 : Fin 32) (by decide), g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = x22 := by rw [P35.regs (22 : Fin 32) (by decide), g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = x23 := by rw [P35.regs (23 : Fin 32) (by decide), g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = x24 := by rw [P35.regs (24 : Fin 32) (by decide), g34_24]
  have g35_25 : reg n35 (25 : Fin 32) = x25 := by rw [P35.regs (25 : Fin 32) (by decide), g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = x26 := by rw [P35.regs (26 : Fin 32) (by decide), g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = x27 := by rw [P35.regs (27 : Fin 32) (by decide), g34_27]
  have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB)] := keep_kk34.trans K35.toL
  clear keep_kk34
  have w35_74 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K35.w32 (by decide) (by decide)).trans w34_74
  have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K35.w32 (by decide) (by decide)).trans w34_78
  have w35_25c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := (K35.w32 (by decide) (by decide)).trans w34_25c
  have w35_260 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := (K35.w32 (by decide) (by decide)).trans w34_260
  have w35_264 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := (K35.w32 (by decide) (by decide)).trans w34_264
  have w35_268 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := (K35.w32 (by decide) (by decide)).trans w34_268
  have w35_27c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K35.w32 (by decide) (by decide)).trans w34_27c
  have w35_280 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K35.w32 (by decide) (by decide)).trans w34_280
  have w35_284 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K35.w32 (by decide) (by decide)).trans w34_284
  have w35_288 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K35.w32 (by decide) (by decide)).trans w34_288
  have w35_420 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K35.w32 (by decide) (by decide)).trans w34_420
  have w35_424 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := (K35.w32 (by decide) (by decide)).trans w34_424
  have w35_428 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K35.w32 (by decide) (by decide)).trans w34_428
  have w35_42c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := (K35.w32 (by decide) (by decide)).trans w34_42c
  have b35_424 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := (K35.b8 (by decide) (by decide)).trans b34_424
  have b35_425 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := (K35.b8 (by decide) (by decide)).trans b34_425
  have b35_426 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := (K35.b8 (by decide) (by decide)).trans b34_426
  have b35_427 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := (K35.b8 (by decide) (by decide)).trans b34_427
  have w35_3e8 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by
    rw [← w34_428]
    exact ld_cp fun q hq => by
      have := X35 (0x3 + q) (by omega)
      rwa [show 0x3E5 + (0x3 + q) = 0x3E8 + q by omega,
        show 0x425 + (0x3 + q) = 0x428 + q by omega] at this
  have w35_3ec : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 tl30.len := by
    rw [← w34_42c]
    exact ld_cp fun q hq => by
      have := X35 (0x7 + q) (by omega)
      rwa [show 0x3E5 + (0x7 + q) = 0x3EC + q by omega,
        show 0x425 + (0x7 + q) = 0x42C + q by omega] at this
  have b35_3e5 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := by rw [show 0x3E5 = 0x3E5 + 0x0 from rfl, X35 0x0 (by decide)]; exact b34_425
  have b35_3e6 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := by rw [show 0x3E6 = 0x3E5 + 0x1 from rfl, X35 0x1 (by decide)]; exact b34_426
  have b35_3e7 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := by rw [show 0x3E7 = 0x3E5 + 0x2 from rfl, X35 0x2 (by decide)]; exact b34_427
  clear b34_424 w34_42c w34_428 w34_424 w34_420 w34_288 w34_284 w34_280 w34_27c w34_268 w34_264 w34_260 w34_25c w34_78 w34_74 g34_12 g34_11 g34_10 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 rb34 s34 m34 u34 c34
  -- 0x114E: sw
  obtain ⟨n36, d36, s36, fr36, K36, W36, rg36⟩ := sv_sw F E35 s35 sv_at_114e (off' := 0x1152) (c := 0x3E0)
    (by decide) (by rw [g35_2]; sv_addr) (by decide) (by decide)
  have t36 : Steps n0 n36 := t35.trans d36
  have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.keep K36 (by decide)
  have g36_2 : reg n36 sp = B + 0x21A0 := by rw [rg36 sp, g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg36 (3 : Fin 32), g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg36 (4 : Fin 32), g35_4]
  have g36_8 : reg n36 (8 : Fin 32) = ((BitVec.ofNat 32 tl30.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg36 (8 : Fin 32), g35_8]
  have g36_9 : reg n36 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [rg36 (9 : Fin 32), g35_9]
  have g36_18 : reg n36 (18 : Fin 32) = out := by rw [rg36 (18 : Fin 32), g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [rg36 (19 : Fin 32), g35_19]
  have g36_20 : reg n36 (20 : Fin 32) = x20 := by rw [rg36 (20 : Fin 32), g35_20]
  have g36_21 : reg n36 (21 : Fin 32) = x21 := by rw [rg36 (21 : Fin 32), g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = x22 := by rw [rg36 (22 : Fin 32), g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = x23 := by rw [rg36 (23 : Fin 32), g35_23]
  have g36_24 : reg n36 (24 : Fin 32) = x24 := by rw [rg36 (24 : Fin 32), g35_24]
  have g36_25 : reg n36 (25 : Fin 32) = x25 := by rw [rg36 (25 : Fin 32), g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = x26 := by rw [rg36 (26 : Fin 32), g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = x27 := by rw [rg36 (27 : Fin 32), g35_27]
  have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4)] := keep_kk35.trans K36.toL
  clear keep_kk35
  have w36_74 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K36.w32 (by decide) (by decide)).trans w35_74
  have w36_78 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K36.w32 (by decide) (by decide)).trans w35_78
  have w36_25c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := (K36.w32 (by decide) (by decide)).trans w35_25c
  have w36_260 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := (K36.w32 (by decide) (by decide)).trans w35_260
  have w36_264 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := (K36.w32 (by decide) (by decide)).trans w35_264
  have w36_268 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := (K36.w32 (by decide) (by decide)).trans w35_268
  have w36_27c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K36.w32 (by decide) (by decide)).trans w35_27c
  have w36_280 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K36.w32 (by decide) (by decide)).trans w35_280
  have w36_284 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K36.w32 (by decide) (by decide)).trans w35_284
  have w36_288 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K36.w32 (by decide) (by decide)).trans w35_288
  have w36_3e8 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K36.w32 (by decide) (by decide)).trans w35_3e8
  have w36_3ec : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 tl30.len := (K36.w32 (by decide) (by decide)).trans w35_3ec
  have w36_420 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K36.w32 (by decide) (by decide)).trans w35_420
  have w36_424 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := (K36.w32 (by decide) (by decide)).trans w35_424
  have w36_428 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K36.w32 (by decide) (by decide)).trans w35_428
  have w36_42c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := (K36.w32 (by decide) (by decide)).trans w35_42c
  have b36_3e5 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := (K36.b8 (by decide) (by decide)).trans b35_3e5
  have b36_3e6 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := (K36.b8 (by decide) (by decide)).trans b35_3e6
  have b36_3e7 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := (K36.b8 (by decide) (by decide)).trans b35_3e7
  have b36_424 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := (K36.b8 (by decide) (by decide)).trans b35_424
  have b36_425 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := (K36.b8 (by decide) (by decide)).trans b35_425
  have b36_426 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := (K36.b8 (by decide) (by decide)).trans b35_426
  have b36_427 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := (K36.b8 (by decide) (by decide)).trans b35_427
  have w36_3e0 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [W36, g35_9]
  clear b35_3e7 b35_3e6 b35_3e5 w35_3ec w35_3e8 b35_427 b35_426 b35_425 b35_424 w35_42c w35_428 w35_424 w35_420 w35_288 w35_284 w35_280 w35_27c w35_268 w35_264 w35_260 w35_25c w35_78 w35_74 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 s35 X35 K35 P35 b34_427 b34_426 b34_425
  -- 0x1152: sb
  obtain ⟨n37, d37, s37, fr37, K37, W37, rg37⟩ := sv_sb F E36 s36 sv_at_1152 (off' := 0x1156) (c := 0x3E4)
    (by decide) (by rw [g36_2]; sv_addr) (by decide)
  have t37 : Steps n0 n37 := t36.trans d37
  have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : SvCode n37.mem := E36.fr F fr37
  have V37 : SvSaves B n37.mem v := V36.keep K37 (by decide)
  have g37_2 : reg n37 sp = B + 0x21A0 := by rw [rg37 sp, g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg37 (3 : Fin 32), g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg37 (4 : Fin 32), g36_4]
  have g37_8 : reg n37 (8 : Fin 32) = ((BitVec.ofNat 32 tl30.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg37 (8 : Fin 32), g36_8]
  have g37_9 : reg n37 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [rg37 (9 : Fin 32), g36_9]
  have g37_18 : reg n37 (18 : Fin 32) = out := by rw [rg37 (18 : Fin 32), g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [rg37 (19 : Fin 32), g36_19]
  have g37_20 : reg n37 (20 : Fin 32) = x20 := by rw [rg37 (20 : Fin 32), g36_20]
  have g37_21 : reg n37 (21 : Fin 32) = x21 := by rw [rg37 (21 : Fin 32), g36_21]
  have g37_22 : reg n37 (22 : Fin 32) = x22 := by rw [rg37 (22 : Fin 32), g36_22]
  have g37_23 : reg n37 (23 : Fin 32) = x23 := by rw [rg37 (23 : Fin 32), g36_23]
  have g37_24 : reg n37 (24 : Fin 32) = x24 := by rw [rg37 (24 : Fin 32), g36_24]
  have g37_25 : reg n37 (25 : Fin 32) = x25 := by rw [rg37 (25 : Fin 32), g36_25]
  have g37_26 : reg n37 (26 : Fin 32) = x26 := by rw [rg37 (26 : Fin 32), g36_26]
  have g37_27 : reg n37 (27 : Fin 32) = x27 := by rw [rg37 (27 : Fin 32), g36_27]
  have keep_kk37 : SvKeepL B n0.mem n37.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1)] := keep_kk36.trans K37.toL
  clear keep_kk36
  have w37_74 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K37.w32 (by decide) (by decide)).trans w36_74
  have w37_78 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K37.w32 (by decide) (by decide)).trans w36_78
  have w37_25c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := (K37.w32 (by decide) (by decide)).trans w36_25c
  have w37_260 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := (K37.w32 (by decide) (by decide)).trans w36_260
  have w37_264 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := (K37.w32 (by decide) (by decide)).trans w36_264
  have w37_268 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := (K37.w32 (by decide) (by decide)).trans w36_268
  have w37_27c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K37.w32 (by decide) (by decide)).trans w36_27c
  have w37_280 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K37.w32 (by decide) (by decide)).trans w36_280
  have w37_284 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K37.w32 (by decide) (by decide)).trans w36_284
  have w37_288 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K37.w32 (by decide) (by decide)).trans w36_288
  have w37_3e0 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K37.w32 (by decide) (by decide)).trans w36_3e0
  have w37_3e8 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K37.w32 (by decide) (by decide)).trans w36_3e8
  have w37_3ec : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 tl30.len := (K37.w32 (by decide) (by decide)).trans w36_3ec
  have w37_420 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K37.w32 (by decide) (by decide)).trans w36_420
  have w37_424 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := (K37.w32 (by decide) (by decide)).trans w36_424
  have w37_428 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K37.w32 (by decide) (by decide)).trans w36_428
  have w37_42c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := (K37.w32 (by decide) (by decide)).trans w36_42c
  have b37_3e5 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E5) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := (K37.b8 (by decide) (by decide)).trans b36_3e5
  have b37_3e6 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E6) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := (K37.b8 (by decide) (by decide)).trans b36_3e6
  have b37_3e7 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E7) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := (K37.b8 (by decide) (by decide)).trans b36_3e7
  have b37_424 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := (K37.b8 (by decide) (by decide)).trans b36_424
  have b37_425 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := (K37.b8 (by decide) (by decide)).trans b36_425
  have b37_426 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := (K37.b8 (by decide) (by decide)).trans b36_426
  have b37_427 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := (K37.b8 (by decide) (by decide)).trans b36_427
  have b37_3e4 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := by rw [W37, g36_8, lbu_low]
  clear w36_3e0 b36_427 b36_426 b36_425 b36_424 b36_3e7 b36_3e6 b36_3e5 w36_42c w36_428 w36_424 w36_420 w36_3ec w36_3e8 w36_288 w36_284 w36_280 w36_27c w36_268 w36_264 w36_260 w36_25c w36_78 w36_74 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 rg36 W36 K36 fr36 s36 d36
  have w37_3e4 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := ld_of_bytes b37_3e4
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x3E4 + 1 = B + 0x21A0 + BitVec.ofNat 32 0x3E5 by sv_addr]; exact b37_3e5)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x3E4 + 2 = B + 0x21A0 + BitVec.ofNat 32 0x3E6 by sv_addr]; exact b37_3e6)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x3E4 + 3 = B + 0x21A0 + BitVec.ofNat 32 0x3E7 by sv_addr]; exact b37_3e7)
  -- 0x1156
  obtain ⟨n38, c38, u38⟩ := s37.block svTt11156 E37.self svTt11156_end
    ⟨trivial, trivial⟩
  have m38 : n38.mem = n37.mem := u38.mem
  have s38 : St n38.mem SV n38 0x1158 (reg n38) := ⟨u38.pc, rfl, fun _ => rfl⟩
  have rb38 : ∀ q, reg n38 q = (runBlock svTt11156 (n37.mem, reg n37)).2 q := fun q => by rw [u38.regs]
  have fr38 : ∀ x, SvR B x → n38.mem x = n37.mem x := fun x _ => by rw [m38]
  have t38 : Steps n0 n38 := t37.trans c38
  have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : SvCode n38.mem := E37.fr F fr38
  have V38 : SvSaves B n38.mem v := V37.same m38
  have g38_2 : reg n38 sp = B + 0x21A0 := by
    rw [rb38, runBlock_reg _ _ _ sp s37.zero (by decide), g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb38, runBlock_reg _ _ _ (3 : Fin 32) s37.zero (by decide), g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb38, runBlock_reg _ _ _ (4 : Fin 32) s37.zero (by decide), g37_4]
  have g38_8 : reg n38 (8 : Fin 32) = ((BitVec.ofNat 32 tl30.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb38, runBlock_reg _ _ _ (8 : Fin 32) s37.zero (by decide), g37_8]
  have g38_9 : reg n38 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by
    rw [rb38, runBlock_reg _ _ _ (9 : Fin 32) s37.zero (by decide), g37_9]
  have g38_18 : reg n38 (18 : Fin 32) = out := by
    rw [rb38, runBlock_reg _ _ _ (18 : Fin 32) s37.zero (by decide), g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = bp := by
    rw [rb38, runBlock_reg _ _ _ (19 : Fin 32) s37.zero (by decide), g37_19]
  have g38_20 : reg n38 (20 : Fin 32) = x20 := by
    rw [rb38, runBlock_reg _ _ _ (20 : Fin 32) s37.zero (by decide), g37_20]
  have g38_21 : reg n38 (21 : Fin 32) = x21 := by
    rw [rb38, runBlock_reg _ _ _ (21 : Fin 32) s37.zero (by decide), g37_21]
  have g38_22 : reg n38 (22 : Fin 32) = x22 := by
    rw [rb38, runBlock_reg _ _ _ (22 : Fin 32) s37.zero (by decide), g37_22]
  have g38_23 : reg n38 (23 : Fin 32) = x23 := by
    rw [rb38, runBlock_reg _ _ _ (23 : Fin 32) s37.zero (by decide), g37_23]
  have g38_24 : reg n38 (24 : Fin 32) = x24 := by
    rw [rb38, runBlock_reg _ _ _ (24 : Fin 32) s37.zero (by decide), g37_24]
  have g38_25 : reg n38 (25 : Fin 32) = x25 := by
    rw [rb38, runBlock_reg _ _ _ (25 : Fin 32) s37.zero (by decide), g37_25]
  have g38_26 : reg n38 (26 : Fin 32) = x26 := by
    rw [rb38, runBlock_reg _ _ _ (26 : Fin 32) s37.zero (by decide), g37_26]
  have g38_27 : reg n38 (27 : Fin 32) = x27 := by
    rw [rb38, runBlock_reg _ _ _ (27 : Fin 32) s37.zero (by decide), g37_27]
  have g38_10 : reg n38 a0 = B + 0x21A0 + BitVec.ofNat 32 0x3E0 := by
    rw [rb38]; simp +decide only [runBlock, BInstr.run, svTt11156, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g37_2, g37_3, g37_4, g37_8, g37_9, g37_18, g37_19, g37_20, g37_21, g37_22, g37_23, g37_24, g37_25, g37_26, g37_27, s37.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk38 : SvKeepL B n0.mem n38.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1)] := by rw [m38]; exact keep_kk37
  clear keep_kk37
  have w38_74 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m38]; exact w37_74
  have w38_78 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m38]; exact w37_78
  have w38_25c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m38]; exact w37_25c
  have w38_260 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m38]; exact w37_260
  have w38_264 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m38]; exact w37_264
  have w38_268 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m38]; exact w37_268
  have w38_27c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m38]; exact w37_27c
  have w38_280 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m38]; exact w37_280
  have w38_284 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m38]; exact w37_284
  have w38_288 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m38]; exact w37_288
  have w38_3e0 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m38]; exact w37_3e0
  have w38_3e4 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m38]; exact w37_3e4
  have w38_3e8 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m38]; exact w37_3e8
  have w38_3ec : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = BitVec.ofNat 32 tl30.len := by rw [m38]; exact w37_3ec
  have w38_420 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m38]; exact w37_420
  have w38_424 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := by rw [m38]; exact w37_424
  have w38_428 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m38]; exact w37_428
  have w38_42c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m38]; exact w37_42c
  have b38_424 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := by rw [m38]; exact b37_424
  have b38_425 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := by rw [m38]; exact b37_425
  have b38_426 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := by rw [m38]; exact b37_426
  have b38_427 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := by rw [m38]; exact b37_427
  clear b37_3e4 b37_427 b37_426 b37_425 b37_424 b37_3e7 b37_3e6 b37_3e5 w37_42c w37_428 w37_424 w37_420 w37_3ec w37_3e8 w37_3e0 w37_288 w37_284 w37_280 w37_27c w37_268 w37_264 w37_260 w37_25c w37_78 w37_74 g37_27 g37_26 g37_25 g37_24 g37_23 g37_22 g37_21 g37_20 g37_19 g37_18 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 rg37 W37 K37 fr37 s37 d37
  -- 0x1158: sv_isShaF
  obtain ⟨n39, c39, s39, sp39, rk39, K39, A39, R39, fr39⟩ := sv_isShaF (dc := 0x3E0)
    F E38 (D0.sv FW fR38) s38 sv_at_1158 sv_at_115c (by decide) (by decide) g38_2
    g38_10 (by decide) (by decide) w38_3e8 w38_3ec ((((tst_in.contentW hr9).restW hte20).restW (derOid_ok_elem ht26)).contentW hr30)
  have t39 : Steps n0 n39 := t38.trans c39
  have fR39 : ∀ x, SvR B x → n39.mem x = M0 x := fun x hx => (fr39 x hx).trans (fR38 x hx)
  have E39 : SvCode n39.mem := E38.fr F fr39
  have V39 : SvSaves B n39.mem v := V38.keepL K39 (by decide)
  rw [isSha256Of_congr (sv_pt fR38 ((((tst_in.contentW hr9).restW hte20).restW (derOid_ok_elem ht26)).contentW hr30))] at R39
  rw [sv_mb fR38 ((((tst_in.contentW hr9).restW hte20).restW (derOid_ok_elem ht26)).contentW hr30)] at A39
  have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk39 (3 : Fin 32) (by decide), g38_3]
  have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk39 (4 : Fin 32) (by decide), g38_4]
  have g39_8 : reg n39 (8 : Fin 32) = ((BitVec.ofNat 32 tl30.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk39 (8 : Fin 32) (by decide), g38_8]
  have g39_9 : reg n39 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [rk39 (9 : Fin 32) (by decide), g38_9]
  have g39_18 : reg n39 (18 : Fin 32) = out := by rw [rk39 (18 : Fin 32) (by decide), g38_18]
  have g39_19 : reg n39 (19 : Fin 32) = bp := by rw [rk39 (19 : Fin 32) (by decide), g38_19]
  have g39_20 : reg n39 (20 : Fin 32) = x20 := by rw [rk39 (20 : Fin 32) (by decide), g38_20]
  have g39_21 : reg n39 (21 : Fin 32) = x21 := by rw [rk39 (21 : Fin 32) (by decide), g38_21]
  have g39_22 : reg n39 (22 : Fin 32) = x22 := by rw [rk39 (22 : Fin 32) (by decide), g38_22]
  have g39_23 : reg n39 (23 : Fin 32) = x23 := by rw [rk39 (23 : Fin 32) (by decide), g38_23]
  have g39_24 : reg n39 (24 : Fin 32) = x24 := by rw [rk39 (24 : Fin 32) (by decide), g38_24]
  have g39_25 : reg n39 (25 : Fin 32) = x25 := by rw [rk39 (25 : Fin 32) (by decide), g38_25]
  have g39_26 : reg n39 (26 : Fin 32) = x26 := by rw [rk39 (26 : Fin 32) (by decide), g38_26]
  have g39_27 : reg n39 (27 : Fin 32) = x27 := by rw [rk39 (27 : Fin 32) (by decide), g38_27]
  have g39_2 : reg n39 sp = B + 0x21A0 := sp39
  obtain ⟨r39, hr39⟩ : ∃ r, isSha256Of M0 (((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) (BitVec.ofNat 32 tl30.len).toNat = r := ⟨_, rfl⟩
  rcases r39 with b39 | (_ | _)
  · rw [hr39] at R39
    obtain ⟨a0_39, a1_39⟩ := R39
    have g39_10 : reg n39 a0 = BitVec.ofNat 32 0x1 := a0_39
    have keep_kk39 : SvKeepL B n0.mem n39.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8)] := keep_kk38.trans K39
    clear keep_kk38
    have w39_74 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K39.w32 (by decide) (by decide)).trans w38_74
    have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K39.w32 (by decide) (by decide)).trans w38_78
    have w39_25c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := (K39.w32 (by decide) (by decide)).trans w38_25c
    have w39_260 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := (K39.w32 (by decide) (by decide)).trans w38_260
    have w39_264 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := (K39.w32 (by decide) (by decide)).trans w38_264
    have w39_268 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := (K39.w32 (by decide) (by decide)).trans w38_268
    have w39_27c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K39.w32 (by decide) (by decide)).trans w38_27c
    have w39_280 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K39.w32 (by decide) (by decide)).trans w38_280
    have w39_284 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K39.w32 (by decide) (by decide)).trans w38_284
    have w39_288 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K39.w32 (by decide) (by decide)).trans w38_288
    have w39_3e0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K39.w32 (by decide) (by decide)).trans w38_3e0
    have w39_3e4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := (K39.w32 (by decide) (by decide)).trans w38_3e4
    have w39_420 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K39.w32 (by decide) (by decide)).trans w38_420
    have w39_424 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := (K39.w32 (by decide) (by decide)).trans w38_424
    have w39_428 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K39.w32 (by decide) (by decide)).trans w38_428
    have w39_42c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := (K39.w32 (by decide) (by decide)).trans w38_42c
    have b39_424 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := (K39.b8 (by decide) (by decide)).trans b38_424
    have b39_425 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := (K39.b8 (by decide) (by decide)).trans b38_425
    have b39_426 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := (K39.b8 (by decide) (by decide)).trans b38_426
    have b39_427 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := (K39.b8 (by decide) (by decide)).trans b38_427
    clear b38_427 b38_426 b38_425 b38_424 w38_42c w38_428 w38_424 w38_420 w38_3ec w38_3e8 w38_3e4 w38_3e0 w38_288 w38_284 w38_280 w38_27c w38_268 w38_264 w38_260 w38_25c w38_78 w38_74 g38_10 g38_27 g38_26 g38_25 g38_24 g38_23 g38_22 g38_21 g38_20 g38_19 g38_18 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 rb38 s38 m38 u38 c38 w37_3e4
    -- 0x1160
    obtain ⟨n40, c40, u40⟩ := s39.block svTt11160 E39.self svTt11160_end
      ⟨trivial, trivial, trivial⟩
    have m40 : n40.mem = n39.mem := u40.mem
    have s40 : St n40.mem SV n40 0x1164 (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
    have rb40 : ∀ q, reg n40 q = (runBlock svTt11160 (n39.mem, reg n39)).2 q := fun q => by rw [u40.regs]
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
    have g40_9 : reg n40 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by
      rw [rb40, runBlock_reg _ _ _ (9 : Fin 32) s39.zero (by decide), g39_9]
    have g40_18 : reg n40 (18 : Fin 32) = out := by
      rw [rb40, runBlock_reg _ _ _ (18 : Fin 32) s39.zero (by decide), g39_18]
    have g40_19 : reg n40 (19 : Fin 32) = bp := by
      rw [rb40, runBlock_reg _ _ _ (19 : Fin 32) s39.zero (by decide), g39_19]
    have g40_20 : reg n40 (20 : Fin 32) = x20 := by
      rw [rb40, runBlock_reg _ _ _ (20 : Fin 32) s39.zero (by decide), g39_20]
    have g40_21 : reg n40 (21 : Fin 32) = x21 := by
      rw [rb40, runBlock_reg _ _ _ (21 : Fin 32) s39.zero (by decide), g39_21]
    have g40_22 : reg n40 (22 : Fin 32) = x22 := by
      rw [rb40, runBlock_reg _ _ _ (22 : Fin 32) s39.zero (by decide), g39_22]
    have g40_23 : reg n40 (23 : Fin 32) = x23 := by
      rw [rb40, runBlock_reg _ _ _ (23 : Fin 32) s39.zero (by decide), g39_23]
    have g40_24 : reg n40 (24 : Fin 32) = x24 := by
      rw [rb40, runBlock_reg _ _ _ (24 : Fin 32) s39.zero (by decide), g39_24]
    have g40_25 : reg n40 (25 : Fin 32) = x25 := by
      rw [rb40, runBlock_reg _ _ _ (25 : Fin 32) s39.zero (by decide), g39_25]
    have g40_26 : reg n40 (26 : Fin 32) = x26 := by
      rw [rb40, runBlock_reg _ _ _ (26 : Fin 32) s39.zero (by decide), g39_26]
    have g40_27 : reg n40 (27 : Fin 32) = x27 := by
      rw [rb40, runBlock_reg _ _ _ (27 : Fin 32) s39.zero (by decide), g39_27]
    have g40_10 : reg n40 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb40]; simp +decide only [runBlock, BInstr.run, svTt11160, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g39_2, g39_3, g39_4, g39_8, g39_9, g39_10, g39_18, g39_19, g39_20, g39_21, g39_22, g39_23, g39_24, g39_25, g39_26, g39_27, s39.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk40 : SvKeepL B n0.mem n40.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8)] := by rw [m40]; exact keep_kk39
    clear keep_kk39
    have w40_74 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m40]; exact w39_74
    have w40_78 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m40]; exact w39_78
    have w40_25c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m40]; exact w39_25c
    have w40_260 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m40]; exact w39_260
    have w40_264 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m40]; exact w39_264
    have w40_268 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m40]; exact w39_268
    have w40_27c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m40]; exact w39_27c
    have w40_280 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m40]; exact w39_280
    have w40_284 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m40]; exact w39_284
    have w40_288 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m40]; exact w39_288
    have w40_3e0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m40]; exact w39_3e0
    have w40_3e4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m40]; exact w39_3e4
    have w40_420 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m40]; exact w39_420
    have w40_424 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := by rw [m40]; exact w39_424
    have w40_428 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m40]; exact w39_428
    have w40_42c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m40]; exact w39_42c
    have b40_424 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := by rw [m40]; exact b39_424
    have b40_425 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := by rw [m40]; exact b39_425
    have b40_426 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := by rw [m40]; exact b39_426
    have b40_427 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := by rw [m40]; exact b39_427
    clear b39_427 b39_426 b39_425 b39_424 w39_42c w39_428 w39_424 w39_420 w39_3e4 w39_3e0 w39_288 w39_284 w39_280 w39_27c w39_268 w39_264 w39_260 w39_25c w39_78 w39_74 g39_10 a1_39 a0_39
    -- 0x1164: branch, taken
    obtain ⟨n41, d41, u41⟩ := s40.taken E40.self 0x7A4 sv_at_1164
      (by decide) (by rw [g40_10, s40.zero]; decide)
    have s41 : St n41.mem SV n41 0x7A4 (reg n41) := ⟨u41.pc, rfl, fun _ => rfl⟩
    have m41 : n41.mem = n40.mem := u41.mem
    have fr41 : ∀ x, SvR B x → n41.mem x = n40.mem x := fun x _ => by rw [m41]
    have t41 : Steps n0 n41 := t40.trans (.single d41)
    have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
    have E41 : SvCode n41.mem := E40.fr F fr41
    have V41 : SvSaves B n41.mem v := V40.same m41
    have g41_2 : reg n41 sp = B + 0x21A0 := by rw [u41.regs, g40_2]
    have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u41.regs, g40_3]
    have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u41.regs, g40_4]
    have g41_9 : reg n41 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u41.regs, g40_9]
    have g41_10 : reg n41 a0 = BitVec.ofNat 32 0x1 := by rw [u41.regs, g40_10]
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
    have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8)] := by rw [m41]; exact keep_kk40
    clear keep_kk40
    have w41_74 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m41]; exact w40_74
    have w41_78 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m41]; exact w40_78
    have w41_25c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m41]; exact w40_25c
    have w41_260 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m41]; exact w40_260
    have w41_264 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m41]; exact w40_264
    have w41_268 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m41]; exact w40_268
    have w41_27c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m41]; exact w40_27c
    have w41_280 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m41]; exact w40_280
    have w41_284 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m41]; exact w40_284
    have w41_288 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m41]; exact w40_288
    have w41_3e0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m41]; exact w40_3e0
    have w41_3e4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m41]; exact w40_3e4
    have w41_420 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m41]; exact w40_420
    have w41_424 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := by rw [m41]; exact w40_424
    have w41_428 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m41]; exact w40_428
    have w41_42c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m41]; exact w40_42c
    have b41_424 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := by rw [m41]; exact b40_424
    have b41_425 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := by rw [m41]; exact b40_425
    have b41_426 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := by rw [m41]; exact b40_426
    have b41_427 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := by rw [m41]; exact b40_427
    clear b40_427 b40_426 b40_425 b40_424 w40_42c w40_428 w40_424 w40_420 w40_3e4 w40_3e0 w40_288 w40_284 w40_280 w40_27c w40_268 w40_264 w40_260 w40_25c w40_78 w40_74 g40_10 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_9 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 rb40 s40 m40 u40 c40
    exact .inl ⟨(fun ⟨tl9', h0', h1', h2', te20', h3', op26', ol26', h4', to26', h5', tl30', h6', h7', _⟩ => by rw [hr9] at h0'; cases h0'; rw [hr20] at h2'; cases h2'; rw [hte20] at h3'; cases h3'; rw [hr26] at h4'; cases h4'; rw [ht26] at h5'; cases h5'; rw [hr30] at h6'; cases h6'; rw [hr39] at h7'; cases h7'), sv_fail F E41 s41 t41 (fun x hx => (fR41 x hx).trans (fM x hx).symm) V41 hret g41_2 g41_18 hO g41_3 g41_4⟩
  · rw [hr39] at R39
    obtain ⟨a0_39, a1_39⟩ := R39
    have g39_10 : reg n39 a0 = BitVec.ofNat 32 0x0 := a0_39
    have g39_11 : reg n39 a1 = BitVec.ofNat 32 0x0 := by rw [a1_39]; rfl
    have keep_kk39 : SvKeepL B n0.mem n39.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8)] := keep_kk38.trans K39
    clear keep_kk38
    have w39_74 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K39.w32 (by decide) (by decide)).trans w38_74
    have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K39.w32 (by decide) (by decide)).trans w38_78
    have w39_25c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := (K39.w32 (by decide) (by decide)).trans w38_25c
    have w39_260 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := (K39.w32 (by decide) (by decide)).trans w38_260
    have w39_264 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := (K39.w32 (by decide) (by decide)).trans w38_264
    have w39_268 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := (K39.w32 (by decide) (by decide)).trans w38_268
    have w39_27c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K39.w32 (by decide) (by decide)).trans w38_27c
    have w39_280 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K39.w32 (by decide) (by decide)).trans w38_280
    have w39_284 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K39.w32 (by decide) (by decide)).trans w38_284
    have w39_288 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K39.w32 (by decide) (by decide)).trans w38_288
    have w39_3e0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K39.w32 (by decide) (by decide)).trans w38_3e0
    have w39_3e4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := (K39.w32 (by decide) (by decide)).trans w38_3e4
    have w39_420 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K39.w32 (by decide) (by decide)).trans w38_420
    have w39_424 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := (K39.w32 (by decide) (by decide)).trans w38_424
    have w39_428 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K39.w32 (by decide) (by decide)).trans w38_428
    have w39_42c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := (K39.w32 (by decide) (by decide)).trans w38_42c
    have b39_424 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := (K39.b8 (by decide) (by decide)).trans b38_424
    have b39_425 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := (K39.b8 (by decide) (by decide)).trans b38_425
    have b39_426 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := (K39.b8 (by decide) (by decide)).trans b38_426
    have b39_427 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := (K39.b8 (by decide) (by decide)).trans b38_427
    clear b38_427 b38_426 b38_425 b38_424 w38_42c w38_428 w38_424 w38_420 w38_3ec w38_3e8 w38_3e4 w38_3e0 w38_288 w38_284 w38_280 w38_27c w38_268 w38_264 w38_260 w38_25c w38_78 w38_74 g38_10 g38_27 g38_26 g38_25 g38_24 g38_23 g38_22 g38_21 g38_20 g38_19 g38_18 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 rb38 s38 m38 u38 c38 w37_3e4
    -- 0x1160
    obtain ⟨n40, c40, u40⟩ := s39.block svTt11160 E39.self svTt11160_end
      ⟨trivial, trivial, trivial⟩
    have m40 : n40.mem = n39.mem := u40.mem
    have s40 : St n40.mem SV n40 0x1164 (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
    have rb40 : ∀ q, reg n40 q = (runBlock svTt11160 (n39.mem, reg n39)).2 q := fun q => by rw [u40.regs]
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
    have g40_9 : reg n40 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by
      rw [rb40, runBlock_reg _ _ _ (9 : Fin 32) s39.zero (by decide), g39_9]
    have g40_11 : reg n40 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb40, runBlock_reg _ _ _ a1 s39.zero (by decide), g39_11]
    have g40_18 : reg n40 (18 : Fin 32) = out := by
      rw [rb40, runBlock_reg _ _ _ (18 : Fin 32) s39.zero (by decide), g39_18]
    have g40_19 : reg n40 (19 : Fin 32) = bp := by
      rw [rb40, runBlock_reg _ _ _ (19 : Fin 32) s39.zero (by decide), g39_19]
    have g40_20 : reg n40 (20 : Fin 32) = x20 := by
      rw [rb40, runBlock_reg _ _ _ (20 : Fin 32) s39.zero (by decide), g39_20]
    have g40_21 : reg n40 (21 : Fin 32) = x21 := by
      rw [rb40, runBlock_reg _ _ _ (21 : Fin 32) s39.zero (by decide), g39_21]
    have g40_22 : reg n40 (22 : Fin 32) = x22 := by
      rw [rb40, runBlock_reg _ _ _ (22 : Fin 32) s39.zero (by decide), g39_22]
    have g40_23 : reg n40 (23 : Fin 32) = x23 := by
      rw [rb40, runBlock_reg _ _ _ (23 : Fin 32) s39.zero (by decide), g39_23]
    have g40_24 : reg n40 (24 : Fin 32) = x24 := by
      rw [rb40, runBlock_reg _ _ _ (24 : Fin 32) s39.zero (by decide), g39_24]
    have g40_25 : reg n40 (25 : Fin 32) = x25 := by
      rw [rb40, runBlock_reg _ _ _ (25 : Fin 32) s39.zero (by decide), g39_25]
    have g40_26 : reg n40 (26 : Fin 32) = x26 := by
      rw [rb40, runBlock_reg _ _ _ (26 : Fin 32) s39.zero (by decide), g39_26]
    have g40_27 : reg n40 (27 : Fin 32) = x27 := by
      rw [rb40, runBlock_reg _ _ _ (27 : Fin 32) s39.zero (by decide), g39_27]
    have g40_8 : reg n40 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [rb40]; simp +decide only [runBlock, BInstr.run, svTt11160, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g39_2, g39_3, g39_4, g39_8, g39_9, g39_10, g39_11, g39_18, g39_19, g39_20, g39_21, g39_22, g39_23, g39_24, g39_25, g39_26, g39_27, s39.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g40_10 : reg n40 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb40]; simp +decide only [runBlock, BInstr.run, svTt11160, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g39_2, g39_3, g39_4, g39_8, g39_9, g39_10, g39_11, g39_18, g39_19, g39_20, g39_21, g39_22, g39_23, g39_24, g39_25, g39_26, g39_27, s39.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk40 : SvKeepL B n0.mem n40.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8)] := by rw [m40]; exact keep_kk39
    clear keep_kk39
    have w40_74 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m40]; exact w39_74
    have w40_78 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m40]; exact w39_78
    have w40_25c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m40]; exact w39_25c
    have w40_260 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m40]; exact w39_260
    have w40_264 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m40]; exact w39_264
    have w40_268 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m40]; exact w39_268
    have w40_27c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m40]; exact w39_27c
    have w40_280 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m40]; exact w39_280
    have w40_284 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m40]; exact w39_284
    have w40_288 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m40]; exact w39_288
    have w40_3e0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m40]; exact w39_3e0
    have w40_3e4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m40]; exact w39_3e4
    have w40_420 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m40]; exact w39_420
    have w40_424 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := by rw [m40]; exact w39_424
    have w40_428 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m40]; exact w39_428
    have w40_42c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m40]; exact w39_42c
    have b40_424 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := by rw [m40]; exact b39_424
    have b40_425 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := by rw [m40]; exact b39_425
    have b40_426 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := by rw [m40]; exact b39_426
    have b40_427 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := by rw [m40]; exact b39_427
    clear b39_427 b39_426 b39_425 b39_424 w39_42c w39_428 w39_424 w39_420 w39_3e4 w39_3e0 w39_288 w39_284 w39_280 w39_27c w39_268 w39_264 w39_260 w39_25c w39_78 w39_74 g39_11 g39_10 a1_39 a0_39
    -- 0x1164: branch, not taken
    obtain ⟨n41, d41, u41⟩ := s40.notTaken E40.self 0x1168 sv_at_1164
      (by decide) (by rw [g40_10, s40.zero]; decide)
    have s41 : St n41.mem SV n41 0x1168 (reg n41) := ⟨u41.pc, rfl, fun _ => rfl⟩
    have m41 : n41.mem = n40.mem := u41.mem
    have fr41 : ∀ x, SvR B x → n41.mem x = n40.mem x := fun x _ => by rw [m41]
    have t41 : Steps n0 n41 := t40.trans (.single d41)
    have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
    have E41 : SvCode n41.mem := E40.fr F fr41
    have V41 : SvSaves B n41.mem v := V40.same m41
    have g41_2 : reg n41 sp = B + 0x21A0 := by rw [u41.regs, g40_2]
    have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u41.regs, g40_3]
    have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u41.regs, g40_4]
    have g41_8 : reg n41 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u41.regs, g40_8]
    have g41_9 : reg n41 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u41.regs, g40_9]
    have g41_10 : reg n41 a0 = BitVec.ofNat 32 0x0 := by rw [u41.regs, g40_10]
    have g41_11 : reg n41 a1 = BitVec.ofNat 32 0x0 := by rw [u41.regs, g40_11]
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
    have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8)] := by rw [m41]; exact keep_kk40
    clear keep_kk40
    have w41_74 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m41]; exact w40_74
    have w41_78 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m41]; exact w40_78
    have w41_25c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m41]; exact w40_25c
    have w41_260 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m41]; exact w40_260
    have w41_264 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m41]; exact w40_264
    have w41_268 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m41]; exact w40_268
    have w41_27c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m41]; exact w40_27c
    have w41_280 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m41]; exact w40_280
    have w41_284 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m41]; exact w40_284
    have w41_288 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m41]; exact w40_288
    have w41_3e0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m41]; exact w40_3e0
    have w41_3e4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m41]; exact w40_3e4
    have w41_420 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m41]; exact w40_420
    have w41_424 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := by rw [m41]; exact w40_424
    have w41_428 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m41]; exact w40_428
    have w41_42c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m41]; exact w40_42c
    have b41_424 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := by rw [m41]; exact b40_424
    have b41_425 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := by rw [m41]; exact b40_425
    have b41_426 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := by rw [m41]; exact b40_426
    have b41_427 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := by rw [m41]; exact b40_427
    clear b40_427 b40_426 b40_425 b40_424 w40_42c w40_428 w40_424 w40_420 w40_3e4 w40_3e0 w40_288 w40_284 w40_280 w40_27c w40_268 w40_264 w40_260 w40_25c w40_78 w40_74 g40_10 g40_8 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_11 g40_9 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 rb40 s40 m40 u40 c40
    -- 0x1168
    obtain ⟨n42, c42, u42⟩ := s41.block svTt11168 E41.self svTt11168_end
      ⟨trivial, trivial, trivial⟩
    have m42 : n42.mem = n41.mem := u42.mem
    have s42 : St n42.mem SV n42 0x116E (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
    have rb42 : ∀ q, reg n42 q = (runBlock svTt11168 (n41.mem, reg n41)).2 q := fun q => by rw [u42.regs]
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
    have g42_9 : reg n42 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by
      rw [rb42, runBlock_reg _ _ _ (9 : Fin 32) s41.zero (by decide), g41_9]
    have g42_11 : reg n42 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb42, runBlock_reg _ _ _ a1 s41.zero (by decide), g41_11]
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
    have g42_8 : reg n42 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb42]; simp +decide only [runBlock, BInstr.run, svTt11168, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_11, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g42_10 : reg n42 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb42]; simp +decide only [runBlock, BInstr.run, svTt11168, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_11, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8)] := by rw [m42]; exact keep_kk41
    clear keep_kk41
    have w42_74 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m42]; exact w41_74
    have w42_78 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m42]; exact w41_78
    have w42_25c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m42]; exact w41_25c
    have w42_260 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m42]; exact w41_260
    have w42_264 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m42]; exact w41_264
    have w42_268 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m42]; exact w41_268
    have w42_27c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m42]; exact w41_27c
    have w42_280 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m42]; exact w41_280
    have w42_284 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m42]; exact w41_284
    have w42_288 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m42]; exact w41_288
    have w42_3e0 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m42]; exact w41_3e0
    have w42_3e4 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m42]; exact w41_3e4
    have w42_420 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m42]; exact w41_420
    have w42_424 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := by rw [m42]; exact w41_424
    have w42_428 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m42]; exact w41_428
    have w42_42c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m42]; exact w41_42c
    have b42_424 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := by rw [m42]; exact b41_424
    have b42_425 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := by rw [m42]; exact b41_425
    have b42_426 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := by rw [m42]; exact b41_426
    have b42_427 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := by rw [m42]; exact b41_427
    clear b41_427 b41_426 b41_425 b41_424 w41_42c w41_428 w41_424 w41_420 w41_3e4 w41_3e0 w41_288 w41_284 w41_280 w41_27c w41_268 w41_264 w41_260 w41_25c w41_78 w41_74 g41_27 g41_26 g41_25 g41_24 g41_23 g41_22 g41_21 g41_20 g41_19 g41_18 g41_11 g41_10 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 fr41 m41 s41 u41 d41
    -- 0x116E: branch, taken
    obtain ⟨n43, d43, u43⟩ := s42.taken E42.self 0x7A4 sv_at_116e
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
    have g43_8 : reg n43 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u43.regs, g42_8]
    have g43_9 : reg n43 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u43.regs, g42_9]
    have g43_10 : reg n43 a0 = BitVec.ofNat 32 0x0 := by rw [u43.regs, g42_10]
    have g43_11 : reg n43 a1 = BitVec.ofNat 32 0x0 := by rw [u43.regs, g42_11]
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
    have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8)] := by rw [m43]; exact keep_kk42
    clear keep_kk42
    have w43_74 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m43]; exact w42_74
    have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m43]; exact w42_78
    have w43_25c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m43]; exact w42_25c
    have w43_260 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m43]; exact w42_260
    have w43_264 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m43]; exact w42_264
    have w43_268 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m43]; exact w42_268
    have w43_27c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m43]; exact w42_27c
    have w43_280 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m43]; exact w42_280
    have w43_284 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m43]; exact w42_284
    have w43_288 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m43]; exact w42_288
    have w43_3e0 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m43]; exact w42_3e0
    have w43_3e4 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m43]; exact w42_3e4
    have w43_420 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m43]; exact w42_420
    have w43_424 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := by rw [m43]; exact w42_424
    have w43_428 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m43]; exact w42_428
    have w43_42c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m43]; exact w42_42c
    have b43_424 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := by rw [m43]; exact b42_424
    have b43_425 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := by rw [m43]; exact b42_425
    have b43_426 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := by rw [m43]; exact b42_426
    have b43_427 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := by rw [m43]; exact b42_427
    clear b42_427 b42_426 b42_425 b42_424 w42_42c w42_428 w42_424 w42_420 w42_3e4 w42_3e0 w42_288 w42_284 w42_280 w42_27c w42_268 w42_264 w42_260 w42_25c w42_78 w42_74 g42_10 g42_8 g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_11 g42_9 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
    exact .inl ⟨(fun ⟨tl9', h0', h1', h2', te20', h3', op26', ol26', h4', to26', h5', tl30', h6', h7', _⟩ => by rw [hr9] at h0'; cases h0'; rw [hr20] at h2'; cases h2'; rw [hte20] at h3'; cases h3'; rw [hr26] at h4'; cases h4'; rw [ht26] at h5'; cases h5'; rw [hr30] at h6'; cases h6'; rw [hr39] at h7'; cases h7'), sv_fail F E43 s43 t43 (fun x hx => (fR43 x hx).trans (fM x hx).symm) V43 hret g43_2 g43_18 hO g43_3 g43_4⟩
  obtain ⟨te39, hte39⟩ := isSha256Of_ok_elem hr39
  obtain ⟨d8_39, d12_39⟩ := A39 te39 hte39
  rw [hr39] at R39
  obtain ⟨a0_39, a1_39⟩ := R39
  have g39_10 : reg n39 a0 = BitVec.ofNat 32 0x0 := a0_39
  have g39_11 : reg n39 a1 = BitVec.ofNat 32 0x1 := by rw [a1_39]; rfl
  have keep_kk39 : SvKeepL B n0.mem n39.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8)] := keep_kk38.trans K39
  clear keep_kk38
  have w39_74 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K39.w32 (by decide) (by decide)).trans w38_74
  have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K39.w32 (by decide) (by decide)).trans w38_78
  have w39_25c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := (K39.w32 (by decide) (by decide)).trans w38_25c
  have w39_260 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := (K39.w32 (by decide) (by decide)).trans w38_260
  have w39_264 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := (K39.w32 (by decide) (by decide)).trans w38_264
  have w39_268 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := (K39.w32 (by decide) (by decide)).trans w38_268
  have w39_27c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K39.w32 (by decide) (by decide)).trans w38_27c
  have w39_280 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K39.w32 (by decide) (by decide)).trans w38_280
  have w39_284 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K39.w32 (by decide) (by decide)).trans w38_284
  have w39_288 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K39.w32 (by decide) (by decide)).trans w38_288
  have w39_3e0 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K39.w32 (by decide) (by decide)).trans w38_3e0
  have w39_3e4 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := (K39.w32 (by decide) (by decide)).trans w38_3e4
  have w39_420 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K39.w32 (by decide) (by decide)).trans w38_420
  have w39_424 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := (K39.w32 (by decide) (by decide)).trans w38_424
  have w39_428 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K39.w32 (by decide) (by decide)).trans w38_428
  have w39_42c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := (K39.w32 (by decide) (by decide)).trans w38_42c
  have b39_424 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := (K39.b8 (by decide) (by decide)).trans b38_424
  have b39_425 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := (K39.b8 (by decide) (by decide)).trans b38_425
  have b39_426 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := (K39.b8 (by decide) (by decide)).trans b38_426
  have b39_427 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := (K39.b8 (by decide) (by decide)).trans b38_427
  have w39_3e8 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len) := d8_39
  have w39_3ec : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = (BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len) := d12_39
  clear b38_427 b38_426 b38_425 b38_424 w38_42c w38_428 w38_424 w38_420 w38_3ec w38_3e8 w38_3e4 w38_3e0 w38_288 w38_284 w38_280 w38_27c w38_268 w38_264 w38_260 w38_25c w38_78 w38_74 g38_10 g38_27 g38_26 g38_25 g38_24 g38_23 g38_22 g38_21 g38_20 g38_19 g38_18 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 rb38 s38 m38 u38 c38 w37_3e4
  -- 0x1160
  obtain ⟨n40, c40, u40⟩ := s39.block svTt11160 E39.self svTt11160_end
    ⟨trivial, trivial, trivial⟩
  have m40 : n40.mem = n39.mem := u40.mem
  have s40 : St n40.mem SV n40 0x1164 (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
  have rb40 : ∀ q, reg n40 q = (runBlock svTt11160 (n39.mem, reg n39)).2 q := fun q => by rw [u40.regs]
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
  have g40_9 : reg n40 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by
    rw [rb40, runBlock_reg _ _ _ (9 : Fin 32) s39.zero (by decide), g39_9]
  have g40_11 : reg n40 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb40, runBlock_reg _ _ _ a1 s39.zero (by decide), g39_11]
  have g40_18 : reg n40 (18 : Fin 32) = out := by
    rw [rb40, runBlock_reg _ _ _ (18 : Fin 32) s39.zero (by decide), g39_18]
  have g40_19 : reg n40 (19 : Fin 32) = bp := by
    rw [rb40, runBlock_reg _ _ _ (19 : Fin 32) s39.zero (by decide), g39_19]
  have g40_20 : reg n40 (20 : Fin 32) = x20 := by
    rw [rb40, runBlock_reg _ _ _ (20 : Fin 32) s39.zero (by decide), g39_20]
  have g40_21 : reg n40 (21 : Fin 32) = x21 := by
    rw [rb40, runBlock_reg _ _ _ (21 : Fin 32) s39.zero (by decide), g39_21]
  have g40_22 : reg n40 (22 : Fin 32) = x22 := by
    rw [rb40, runBlock_reg _ _ _ (22 : Fin 32) s39.zero (by decide), g39_22]
  have g40_23 : reg n40 (23 : Fin 32) = x23 := by
    rw [rb40, runBlock_reg _ _ _ (23 : Fin 32) s39.zero (by decide), g39_23]
  have g40_24 : reg n40 (24 : Fin 32) = x24 := by
    rw [rb40, runBlock_reg _ _ _ (24 : Fin 32) s39.zero (by decide), g39_24]
  have g40_25 : reg n40 (25 : Fin 32) = x25 := by
    rw [rb40, runBlock_reg _ _ _ (25 : Fin 32) s39.zero (by decide), g39_25]
  have g40_26 : reg n40 (26 : Fin 32) = x26 := by
    rw [rb40, runBlock_reg _ _ _ (26 : Fin 32) s39.zero (by decide), g39_26]
  have g40_27 : reg n40 (27 : Fin 32) = x27 := by
    rw [rb40, runBlock_reg _ _ _ (27 : Fin 32) s39.zero (by decide), g39_27]
  have g40_8 : reg n40 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb40]; simp +decide only [runBlock, BInstr.run, svTt11160, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g39_2, g39_3, g39_4, g39_8, g39_9, g39_10, g39_11, g39_18, g39_19, g39_20, g39_21, g39_22, g39_23, g39_24, g39_25, g39_26, g39_27, s39.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g40_10 : reg n40 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb40]; simp +decide only [runBlock, BInstr.run, svTt11160, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g39_2, g39_3, g39_4, g39_8, g39_9, g39_10, g39_11, g39_18, g39_19, g39_20, g39_21, g39_22, g39_23, g39_24, g39_25, g39_26, g39_27, s39.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk40 : SvKeepL B n0.mem n40.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8)] := by rw [m40]; exact keep_kk39
  clear keep_kk39
  have w40_74 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m40]; exact w39_74
  have w40_78 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m40]; exact w39_78
  have w40_25c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m40]; exact w39_25c
  have w40_260 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m40]; exact w39_260
  have w40_264 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m40]; exact w39_264
  have w40_268 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m40]; exact w39_268
  have w40_27c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m40]; exact w39_27c
  have w40_280 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m40]; exact w39_280
  have w40_284 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m40]; exact w39_284
  have w40_288 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m40]; exact w39_288
  have w40_3e0 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m40]; exact w39_3e0
  have w40_3e4 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m40]; exact w39_3e4
  have w40_3e8 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len) := by rw [m40]; exact w39_3e8
  have w40_3ec : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = (BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len) := by rw [m40]; exact w39_3ec
  have w40_420 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m40]; exact w39_420
  have w40_424 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := by rw [m40]; exact w39_424
  have w40_428 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m40]; exact w39_428
  have w40_42c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m40]; exact w39_42c
  have b40_424 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := by rw [m40]; exact b39_424
  have b40_425 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := by rw [m40]; exact b39_425
  have b40_426 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := by rw [m40]; exact b39_426
  have b40_427 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := by rw [m40]; exact b39_427
  clear w39_3ec w39_3e8 b39_427 b39_426 b39_425 b39_424 w39_42c w39_428 w39_424 w39_420 w39_3e4 w39_3e0 w39_288 w39_284 w39_280 w39_27c w39_268 w39_264 w39_260 w39_25c w39_78 w39_74 g39_11 g39_10 a1_39 a0_39 d12_39 d8_39 g39_2 g39_27 g39_26 g39_25 g39_24 g39_23 g39_22 g39_21 g39_20 g39_19 g39_18 g39_9 g39_8 g39_4 g39_3 V39 E39 fR39 t39 fr39 A39 K39 rk39 sp39 s39 c39
  -- 0x1164: branch, not taken
  obtain ⟨n41, d41, u41⟩ := s40.notTaken E40.self 0x1168 sv_at_1164
    (by decide) (by rw [g40_10, s40.zero]; decide)
  have s41 : St n41.mem SV n41 0x1168 (reg n41) := ⟨u41.pc, rfl, fun _ => rfl⟩
  have m41 : n41.mem = n40.mem := u41.mem
  have fr41 : ∀ x, SvR B x → n41.mem x = n40.mem x := fun x _ => by rw [m41]
  have t41 : Steps n0 n41 := t40.trans (.single d41)
  have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
  have E41 : SvCode n41.mem := E40.fr F fr41
  have V41 : SvSaves B n41.mem v := V40.same m41
  have g41_2 : reg n41 sp = B + 0x21A0 := by rw [u41.regs, g40_2]
  have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u41.regs, g40_3]
  have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u41.regs, g40_4]
  have g41_8 : reg n41 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u41.regs, g40_8]
  have g41_9 : reg n41 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u41.regs, g40_9]
  have g41_10 : reg n41 a0 = BitVec.ofNat 32 0x0 := by rw [u41.regs, g40_10]
  have g41_11 : reg n41 a1 = BitVec.ofNat 32 0x1 := by rw [u41.regs, g40_11]
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
  have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8)] := by rw [m41]; exact keep_kk40
  clear keep_kk40
  have w41_74 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m41]; exact w40_74
  have w41_78 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m41]; exact w40_78
  have w41_25c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m41]; exact w40_25c
  have w41_260 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m41]; exact w40_260
  have w41_264 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m41]; exact w40_264
  have w41_268 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m41]; exact w40_268
  have w41_27c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m41]; exact w40_27c
  have w41_280 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m41]; exact w40_280
  have w41_284 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m41]; exact w40_284
  have w41_288 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m41]; exact w40_288
  have w41_3e0 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m41]; exact w40_3e0
  have w41_3e4 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m41]; exact w40_3e4
  have w41_3e8 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len) := by rw [m41]; exact w40_3e8
  have w41_3ec : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = (BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len) := by rw [m41]; exact w40_3ec
  have w41_420 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m41]; exact w40_420
  have w41_424 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := by rw [m41]; exact w40_424
  have w41_428 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m41]; exact w40_428
  have w41_42c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m41]; exact w40_42c
  have b41_424 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := by rw [m41]; exact b40_424
  have b41_425 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := by rw [m41]; exact b40_425
  have b41_426 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := by rw [m41]; exact b40_426
  have b41_427 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := by rw [m41]; exact b40_427
  clear b40_427 b40_426 b40_425 b40_424 w40_42c w40_428 w40_424 w40_420 w40_3ec w40_3e8 w40_3e4 w40_3e0 w40_288 w40_284 w40_280 w40_27c w40_268 w40_264 w40_260 w40_25c w40_78 w40_74 g40_10 g40_8 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_11 g40_9 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 rb40 s40 m40 u40 c40
  -- 0x1168
  obtain ⟨n42, c42, u42⟩ := s41.block svTt11168 E41.self svTt11168_end
    ⟨trivial, trivial, trivial⟩
  have m42 : n42.mem = n41.mem := u42.mem
  have s42 : St n42.mem SV n42 0x116E (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
  have rb42 : ∀ q, reg n42 q = (runBlock svTt11168 (n41.mem, reg n41)).2 q := fun q => by rw [u42.regs]
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
  have g42_9 : reg n42 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by
    rw [rb42, runBlock_reg _ _ _ (9 : Fin 32) s41.zero (by decide), g41_9]
  have g42_11 : reg n42 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb42, runBlock_reg _ _ _ a1 s41.zero (by decide), g41_11]
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
  have g42_8 : reg n42 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb42]; simp +decide only [runBlock, BInstr.run, svTt11168, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_11, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g42_10 : reg n42 a0 = BitVec.ofNat 32 0x1 := by
    rw [rb42]; simp +decide only [runBlock, BInstr.run, svTt11168, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_11, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8)] := by rw [m42]; exact keep_kk41
  clear keep_kk41
  have w42_74 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m42]; exact w41_74
  have w42_78 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m42]; exact w41_78
  have w42_25c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m42]; exact w41_25c
  have w42_260 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m42]; exact w41_260
  have w42_264 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m42]; exact w41_264
  have w42_268 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m42]; exact w41_268
  have w42_27c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m42]; exact w41_27c
  have w42_280 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m42]; exact w41_280
  have w42_284 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m42]; exact w41_284
  have w42_288 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m42]; exact w41_288
  have w42_3e0 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m42]; exact w41_3e0
  have w42_3e4 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m42]; exact w41_3e4
  have w42_3e8 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len) := by rw [m42]; exact w41_3e8
  have w42_3ec : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = (BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len) := by rw [m42]; exact w41_3ec
  have w42_420 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m42]; exact w41_420
  have w42_424 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := by rw [m42]; exact w41_424
  have w42_428 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m42]; exact w41_428
  have w42_42c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m42]; exact w41_42c
  have b42_424 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := by rw [m42]; exact b41_424
  have b42_425 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := by rw [m42]; exact b41_425
  have b42_426 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := by rw [m42]; exact b41_426
  have b42_427 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := by rw [m42]; exact b41_427
  clear b41_427 b41_426 b41_425 b41_424 w41_42c w41_428 w41_424 w41_420 w41_3ec w41_3e8 w41_3e4 w41_3e0 w41_288 w41_284 w41_280 w41_27c w41_268 w41_264 w41_260 w41_25c w41_78 w41_74 g41_27 g41_26 g41_25 g41_24 g41_23 g41_22 g41_21 g41_20 g41_19 g41_18 g41_11 g41_10 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 fr41 m41 s41 u41 d41
  -- 0x116E: branch, not taken
  obtain ⟨n43, d43, u43⟩ := s42.notTaken E42.self 0x1172 sv_at_116e
    (by decide) (by rw [g42_10, s42.zero]; decide)
  have s43 : St n43.mem SV n43 0x1172 (reg n43) := ⟨u43.pc, rfl, fun _ => rfl⟩
  have m43 : n43.mem = n42.mem := u43.mem
  have fr43 : ∀ x, SvR B x → n43.mem x = n42.mem x := fun x _ => by rw [m43]
  have t43 : Steps n0 n43 := t42.trans (.single d43)
  have fR43 : ∀ x, SvR B x → n43.mem x = M0 x := fun x hx => (fr43 x hx).trans (fR42 x hx)
  have E43 : SvCode n43.mem := E42.fr F fr43
  have V43 : SvSaves B n43.mem v := V42.same m43
  have g43_2 : reg n43 sp = B + 0x21A0 := by rw [u43.regs, g42_2]
  have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u43.regs, g42_3]
  have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u43.regs, g42_4]
  have g43_8 : reg n43 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u43.regs, g42_8]
  have g43_9 : reg n43 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u43.regs, g42_9]
  have g43_10 : reg n43 a0 = BitVec.ofNat 32 0x1 := by rw [u43.regs, g42_10]
  have g43_11 : reg n43 a1 = BitVec.ofNat 32 0x1 := by rw [u43.regs, g42_11]
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
  have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8)] := by rw [m43]; exact keep_kk42
  clear keep_kk42
  have w43_74 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m43]; exact w42_74
  have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m43]; exact w42_78
  have w43_25c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m43]; exact w42_25c
  have w43_260 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m43]; exact w42_260
  have w43_264 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m43]; exact w42_264
  have w43_268 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m43]; exact w42_268
  have w43_27c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m43]; exact w42_27c
  have w43_280 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m43]; exact w42_280
  have w43_284 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m43]; exact w42_284
  have w43_288 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m43]; exact w42_288
  have w43_3e0 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m43]; exact w42_3e0
  have w43_3e4 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m43]; exact w42_3e4
  have w43_3e8 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len) := by rw [m43]; exact w42_3e8
  have w43_3ec : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = (BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len) := by rw [m43]; exact w42_3ec
  have w43_420 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m43]; exact w42_420
  have w43_424 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := by rw [m43]; exact w42_424
  have w43_428 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m43]; exact w42_428
  have w43_42c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m43]; exact w42_42c
  have b43_424 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := by rw [m43]; exact b42_424
  have b43_425 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := by rw [m43]; exact b42_425
  have b43_426 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := by rw [m43]; exact b42_426
  have b43_427 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := by rw [m43]; exact b42_427
  clear b42_427 b42_426 b42_425 b42_424 w42_42c w42_428 w42_424 w42_420 w42_3ec w42_3e8 w42_3e4 w42_3e0 w42_288 w42_284 w42_280 w42_27c w42_268 w42_264 w42_260 w42_25c w42_78 w42_74 g42_10 g42_8 g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_11 g42_9 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
  -- 0x1172
  obtain ⟨n44, c44, u44⟩ := s43.block svTt11172 E43.self svTt11172_end
    ⟨trivial, trivial, trivial⟩
  have m44 : n44.mem = n43.mem := u44.mem
  have s44 : St n44.mem SV n44 0x1178 (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
  have rb44 : ∀ q, reg n44 q = (runBlock svTt11172 (n43.mem, reg n43)).2 q := fun q => by rw [u44.regs]
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
  have g44_8 : reg n44 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb44, runBlock_reg _ _ _ (8 : Fin 32) s43.zero (by decide), g43_8]
  have g44_9 : reg n44 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by
    rw [rb44, runBlock_reg _ _ _ (9 : Fin 32) s43.zero (by decide), g43_9]
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
  have g44_10 : reg n44 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb44]; simp +decide only [runBlock, BInstr.run, svTt11172, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g44_11 : reg n44 a1 = B + 0x21A0 + BitVec.ofNat 32 0x3E0 := by
    rw [rb44]; simp +decide only [runBlock, BInstr.run, svTt11172, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk44 : SvKeepL B n0.mem n44.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8)] := by rw [m44]; exact keep_kk43
  clear keep_kk43
  have w44_74 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m44]; exact w43_74
  have w44_78 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m44]; exact w43_78
  have w44_25c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m44]; exact w43_25c
  have w44_260 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m44]; exact w43_260
  have w44_264 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m44]; exact w43_264
  have w44_268 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m44]; exact w43_268
  have w44_27c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m44]; exact w43_27c
  have w44_280 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m44]; exact w43_280
  have w44_284 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m44]; exact w43_284
  have w44_288 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m44]; exact w43_288
  have w44_3e0 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m44]; exact w43_3e0
  have w44_3e4 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m44]; exact w43_3e4
  have w44_3e8 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = (((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len) := by rw [m44]; exact w43_3e8
  have w44_3ec : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = (BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len) := by rw [m44]; exact w43_3ec
  have w44_420 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m44]; exact w43_420
  have w44_424 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl30.len := by rw [m44]; exact w43_424
  have w44_428 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m44]; exact w43_428
  have w44_42c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m44]; exact w43_42c
  have b44_424 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl30.len).extractLsb' 0 8 := by rw [m44]; exact b43_424
  have b44_425 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl30.len).extractLsb' 8 8 := by rw [m44]; exact b43_425
  have b44_426 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl30.len).extractLsb' 16 8 := by rw [m44]; exact b43_426
  have b44_427 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl30.len).extractLsb' 24 8 := by rw [m44]; exact b43_427
  clear b43_427 b43_426 b43_425 b43_424 w43_42c w43_428 w43_424 w43_420 w43_3ec w43_3e8 w43_3e4 w43_3e0 w43_288 w43_284 w43_280 w43_27c w43_268 w43_264 w43_260 w43_25c w43_78 w43_74 g43_27 g43_26 g43_25 g43_24 g43_23 g43_22 g43_21 g43_20 g43_19 g43_18 g43_11 g43_10 g43_9 g43_8 g43_4 g43_3 g43_2 V43 E43 fR43 t43 fr43 m43 s43 u43 d43
  -- 0x1178: sv_octF
  obtain ⟨n45, c45, s45, sp45, rk45, K45, A45, Ok45, Er45, fr45⟩ := sv_octF (oc := 0x420) (dc := 0x3E0)
    F E44 s44 sv_at_1178 sv_at_117c (by decide) (by decide) g44_2 g44_10 g44_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w44_3e8 w44_3ec (((((tst_in.contentW hr9).restW hte20).restW (derOid_ok_elem ht26)).contentW hr30).restW hte39)
  have t45 : Steps n0 n45 := t44.trans c45
  have fR45 : ∀ x, SvR B x → n45.mem x = M0 x := fun x hx => (fr45 x hx).trans (fR44 x hx)
  have E45 : SvCode n45.mem := E44.fr F fr45
  have V45 : SvSaves B n45.mem v := V44.keepL K45 (by decide)
  rw [sv_mb fR44 (((((tst_in.contentW hr9).restW hte20).restW (derOid_ok_elem ht26)).contentW hr30).restW hte39)] at A45 Ok45 Er45
  have g45_2 : reg n45 sp = B + 0x21A0 := by rw [rk45 sp (by decide) (by decide), g44_2]
  have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk45 (3 : Fin 32) (by decide) (by decide), g44_3]
  have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk45 (4 : Fin 32) (by decide) (by decide), g44_4]
  have g45_8 : reg n45 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rk45 (8 : Fin 32) (by decide) (by decide), g44_8]
  have g45_9 : reg n45 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [rk45 (9 : Fin 32) (by decide) (by decide), g44_9]
  have g45_18 : reg n45 (18 : Fin 32) = out := by rw [rk45 (18 : Fin 32) (by decide) (by decide), g44_18]
  have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [rk45 (19 : Fin 32) (by decide) (by decide), g44_19]
  have g45_20 : reg n45 (20 : Fin 32) = x20 := by rw [rk45 (20 : Fin 32) (by decide) (by decide), g44_20]
  have g45_21 : reg n45 (21 : Fin 32) = x21 := by rw [rk45 (21 : Fin 32) (by decide) (by decide), g44_21]
  have g45_22 : reg n45 (22 : Fin 32) = x22 := by rw [rk45 (22 : Fin 32) (by decide) (by decide), g44_22]
  have g45_23 : reg n45 (23 : Fin 32) = x23 := by rw [rk45 (23 : Fin 32) (by decide) (by decide), g44_23]
  have g45_24 : reg n45 (24 : Fin 32) = x24 := by rw [rk45 (24 : Fin 32) (by decide) (by decide), g44_24]
  have g45_25 : reg n45 (25 : Fin 32) = x25 := by rw [rk45 (25 : Fin 32) (by decide) (by decide), g44_25]
  have g45_26 : reg n45 (26 : Fin 32) = x26 := by rw [rk45 (26 : Fin 32) (by decide) (by decide), g44_26]
  have g45_27 : reg n45 (27 : Fin 32) = x27 := by rw [rk45 (27 : Fin 32) (by decide) (by decide), g44_27]
  obtain ⟨r45, hr45⟩ : ∃ r, derContent ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) (derElement 4 (memBytes M0 ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)).toNat)) = r := ⟨_, rfl⟩
  rcases r45 with er45 | ⟨vp45, vl45⟩
  · obtain ⟨z45, -⟩ := Er45 er45 hr45
    have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8)] := keep_kk44.trans K45
    clear keep_kk44
    have w45_74 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K45.w32 (by decide) (by decide)).trans w44_74
    have w45_78 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K45.w32 (by decide) (by decide)).trans w44_78
    have w45_25c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := (K45.w32 (by decide) (by decide)).trans w44_25c
    have w45_260 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := (K45.w32 (by decide) (by decide)).trans w44_260
    have w45_264 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := (K45.w32 (by decide) (by decide)).trans w44_264
    have w45_268 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := (K45.w32 (by decide) (by decide)).trans w44_268
    have w45_27c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K45.w32 (by decide) (by decide)).trans w44_27c
    have w45_280 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K45.w32 (by decide) (by decide)).trans w44_280
    have w45_284 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K45.w32 (by decide) (by decide)).trans w44_284
    have w45_288 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K45.w32 (by decide) (by decide)).trans w44_288
    have w45_3e0 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K45.w32 (by decide) (by decide)).trans w44_3e0
    have w45_3e4 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := (K45.w32 (by decide) (by decide)).trans w44_3e4
    have w45_428 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K45.w32 (by decide) (by decide)).trans w44_428
    have w45_42c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := (K45.w32 (by decide) (by decide)).trans w44_42c
    have w45_420 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z45
    clear b44_427 b44_426 b44_425 b44_424 w44_42c w44_428 w44_424 w44_420 w44_3ec w44_3e8 w44_3e4 w44_3e0 w44_288 w44_284 w44_280 w44_27c w44_268 w44_264 w44_260 w44_25c w44_78 w44_74 g44_11 g44_10 g44_27 g44_26 g44_25 g44_24 g44_23 g44_22 g44_21 g44_20 g44_19 g44_18 g44_9 g44_8 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 rb44 s44 m44 u44 c44
    -- 0x1180: lw
    obtain ⟨n46, d46, u46⟩ := s45.lw E45.self sv_at_1180 (off' := 0x1184) (by decide)
      (by rw [g45_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s46 : St n46.mem SV n46 0x1184 (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
    have m46 : n46.mem = n45.mem := u46.mem
    have fr46 : ∀ x, SvR B x → n46.mem x = n45.mem x := fun x _ => by rw [m46]
    have t46 : Steps n0 n46 := t45.trans (.single d46)
    have fR46 : ∀ x, SvR B x → n46.mem x = M0 x := fun x hx => (fr46 x hx).trans (fR45 x hx)
    have E46 : SvCode n46.mem := E45.fr F fr46
    have V46 : SvSaves B n46.mem v := V45.same m46
    have g46_2 : reg n46 sp = B + 0x21A0 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_2]
    have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u46.regs, upd_ne (by decide) (by decide), g45_3]
    have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u46.regs, upd_ne (by decide) (by decide), g45_4]
    have g46_8 : reg n46 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_8]
    have g46_9 : reg n46 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u46.regs, upd_ne (by decide) (by decide), g45_9]
    have g46_18 : reg n46 (18 : Fin 32) = out := by rw [u46.regs, upd_ne (by decide) (by decide), g45_18]
    have g46_19 : reg n46 (19 : Fin 32) = bp := by rw [u46.regs, upd_ne (by decide) (by decide), g45_19]
    have g46_20 : reg n46 (20 : Fin 32) = x20 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_20]
    have g46_21 : reg n46 (21 : Fin 32) = x21 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_21]
    have g46_22 : reg n46 (22 : Fin 32) = x22 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_22]
    have g46_23 : reg n46 (23 : Fin 32) = x23 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_23]
    have g46_24 : reg n46 (24 : Fin 32) = x24 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_24]
    have g46_25 : reg n46 (25 : Fin 32) = x25 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_25]
    have g46_26 : reg n46 (26 : Fin 32) = x26 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_26]
    have g46_27 : reg n46 (27 : Fin 32) = 0 := by
      rw [u46.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g45_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w45_420]
    have keep_kk46 : SvKeepL B n0.mem n46.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m46]; exact keep_kk45
    clear keep_kk45
    have w46_74 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m46]; exact w45_74
    have w46_78 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m46]; exact w45_78
    have w46_25c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m46]; exact w45_25c
    have w46_260 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m46]; exact w45_260
    have w46_264 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m46]; exact w45_264
    have w46_268 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m46]; exact w45_268
    have w46_27c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m46]; exact w45_27c
    have w46_280 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m46]; exact w45_280
    have w46_284 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m46]; exact w45_284
    have w46_288 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m46]; exact w45_288
    have w46_3e0 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m46]; exact w45_3e0
    have w46_3e4 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m46]; exact w45_3e4
    have w46_420 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m46]; exact w45_420
    have w46_428 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m46]; exact w45_428
    have w46_42c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m46]; exact w45_42c
    clear w45_420 w45_42c w45_428 w45_3e4 w45_3e0 w45_288 w45_284 w45_280 w45_27c w45_268 w45_264 w45_260 w45_25c w45_78 w45_74 z45
    -- 0x1184: branch, taken
    obtain ⟨n47, d47, u47⟩ := s46.taken E46.self 0x12AA sv_at_1184
      (by decide) (by rw [g46_27, s46.zero]; rfl)
    have s47 : St n47.mem SV n47 0x12AA (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
    have m47 : n47.mem = n46.mem := u47.mem
    have fr47 : ∀ x, SvR B x → n47.mem x = n46.mem x := fun x _ => by rw [m47]
    have t47 : Steps n0 n47 := t46.trans (.single d47)
    have fR47 : ∀ x, SvR B x → n47.mem x = M0 x := fun x hx => (fr47 x hx).trans (fR46 x hx)
    have E47 : SvCode n47.mem := E46.fr F fr47
    have V47 : SvSaves B n47.mem v := V46.same m47
    have g47_2 : reg n47 sp = B + 0x21A0 := by rw [u47.regs, g46_2]
    have g47_3 : reg n47 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u47.regs, g46_3]
    have g47_4 : reg n47 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u47.regs, g46_4]
    have g47_8 : reg n47 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u47.regs, g46_8]
    have g47_9 : reg n47 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u47.regs, g46_9]
    have g47_18 : reg n47 (18 : Fin 32) = out := by rw [u47.regs, g46_18]
    have g47_19 : reg n47 (19 : Fin 32) = bp := by rw [u47.regs, g46_19]
    have g47_20 : reg n47 (20 : Fin 32) = x20 := by rw [u47.regs, g46_20]
    have g47_21 : reg n47 (21 : Fin 32) = x21 := by rw [u47.regs, g46_21]
    have g47_22 : reg n47 (22 : Fin 32) = x22 := by rw [u47.regs, g46_22]
    have g47_23 : reg n47 (23 : Fin 32) = x23 := by rw [u47.regs, g46_23]
    have g47_24 : reg n47 (24 : Fin 32) = x24 := by rw [u47.regs, g46_24]
    have g47_25 : reg n47 (25 : Fin 32) = x25 := by rw [u47.regs, g46_25]
    have g47_26 : reg n47 (26 : Fin 32) = x26 := by rw [u47.regs, g46_26]
    have g47_27 : reg n47 (27 : Fin 32) = 0 := by rw [u47.regs, g46_27]
    have keep_kk47 : SvKeepL B n0.mem n47.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m47]; exact keep_kk46
    clear keep_kk46
    have w47_74 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m47]; exact w46_74
    have w47_78 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m47]; exact w46_78
    have w47_25c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m47]; exact w46_25c
    have w47_260 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m47]; exact w46_260
    have w47_264 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m47]; exact w46_264
    have w47_268 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m47]; exact w46_268
    have w47_27c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m47]; exact w46_27c
    have w47_280 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m47]; exact w46_280
    have w47_284 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m47]; exact w46_284
    have w47_288 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m47]; exact w46_288
    have w47_3e0 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m47]; exact w46_3e0
    have w47_3e4 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m47]; exact w46_3e4
    have w47_420 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m47]; exact w46_420
    have w47_428 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m47]; exact w46_428
    have w47_42c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m47]; exact w46_42c
    clear w46_42c w46_428 w46_420 w46_3e4 w46_3e0 w46_288 w46_284 w46_280 w46_27c w46_268 w46_264 w46_260 w46_25c w46_78 w46_74 g46_27 g46_26 g46_25 g46_24 g46_23 g46_22 g46_21 g46_20 g46_19 g46_18 g46_9 g46_8 g46_4 g46_3 g46_2 V46 E46 fR46 t46 fr46 m46 s46 u46 d46
    -- 0x12AA: lbu
    obtain ⟨n48, d48, u48⟩ := s47.lbu E47.self sv_at_12aa (off' := 0x12AE) (by decide)
    have s48 : St n48.mem SV n48 0x12AE (reg n48) := ⟨u48.pc, rfl, fun _ => rfl⟩
    have m48 : n48.mem = n47.mem := u48.mem
    have fr48 : ∀ x, SvR B x → n48.mem x = n47.mem x := fun x _ => by rw [m48]
    have t48 : Steps n0 n48 := t47.trans (.single d48)
    have fR48 : ∀ x, SvR B x → n48.mem x = M0 x := fun x hx => (fr48 x hx).trans (fR47 x hx)
    have E48 : SvCode n48.mem := E47.fr F fr48
    have V48 : SvSaves B n48.mem v := V47.same m48
    have g48_2 : reg n48 sp = B + 0x21A0 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_2]
    have g48_3 : reg n48 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u48.regs, upd_ne (by decide) (by decide), g47_3]
    have g48_4 : reg n48 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u48.regs, upd_ne (by decide) (by decide), g47_4]
    have g48_9 : reg n48 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u48.regs, upd_ne (by decide) (by decide), g47_9]
    have g48_18 : reg n48 (18 : Fin 32) = out := by rw [u48.regs, upd_ne (by decide) (by decide), g47_18]
    have g48_19 : reg n48 (19 : Fin 32) = bp := by rw [u48.regs, upd_ne (by decide) (by decide), g47_19]
    have g48_20 : reg n48 (20 : Fin 32) = x20 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_20]
    have g48_21 : reg n48 (21 : Fin 32) = x21 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_21]
    have g48_22 : reg n48 (22 : Fin 32) = x22 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_22]
    have g48_23 : reg n48 (23 : Fin 32) = x23 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_23]
    have g48_24 : reg n48 (24 : Fin 32) = x24 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_24]
    have g48_25 : reg n48 (25 : Fin 32) = x25 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_25]
    have g48_26 : reg n48 (26 : Fin 32) = x26 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_26]
    have g48_27 : reg n48 (27 : Fin 32) = 0 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_27]
    have keep_kk48 : SvKeepL B n0.mem n48.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m48]; exact keep_kk47
    clear keep_kk47
    have w48_74 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m48]; exact w47_74
    have w48_78 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m48]; exact w47_78
    have w48_25c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m48]; exact w47_25c
    have w48_260 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m48]; exact w47_260
    have w48_264 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m48]; exact w47_264
    have w48_268 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m48]; exact w47_268
    have w48_27c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m48]; exact w47_27c
    have w48_280 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m48]; exact w47_280
    have w48_284 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m48]; exact w47_284
    have w48_288 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m48]; exact w47_288
    have w48_3e0 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m48]; exact w47_3e0
    have w48_3e4 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m48]; exact w47_3e4
    have w48_420 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m48]; exact w47_420
    have w48_428 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m48]; exact w47_428
    have w48_42c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m48]; exact w47_42c
    clear w47_42c w47_428 w47_420 w47_3e4 w47_3e0 w47_288 w47_284 w47_280 w47_27c w47_268 w47_264 w47_260 w47_25c w47_78 w47_74 g47_27 g47_26 g47_25 g47_24 g47_23 g47_22 g47_21 g47_20 g47_19 g47_18 g47_9 g47_8 g47_4 g47_3 g47_2 V47 E47 fR47 t47 fr47 m47 s47 u47 d47
    -- 0x12AE: j
    obtain ⟨n49, d49, u49⟩ := s48.jump E48.self sv_at_12ae (off' := 0x7A4) (by decide)
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
    have g49_9 : reg n49 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u49.regs, g48_9]
    have g49_18 : reg n49 (18 : Fin 32) = out := by rw [u49.regs, g48_18]
    have g49_19 : reg n49 (19 : Fin 32) = bp := by rw [u49.regs, g48_19]
    have g49_20 : reg n49 (20 : Fin 32) = x20 := by rw [u49.regs, g48_20]
    have g49_21 : reg n49 (21 : Fin 32) = x21 := by rw [u49.regs, g48_21]
    have g49_22 : reg n49 (22 : Fin 32) = x22 := by rw [u49.regs, g48_22]
    have g49_23 : reg n49 (23 : Fin 32) = x23 := by rw [u49.regs, g48_23]
    have g49_24 : reg n49 (24 : Fin 32) = x24 := by rw [u49.regs, g48_24]
    have g49_25 : reg n49 (25 : Fin 32) = x25 := by rw [u49.regs, g48_25]
    have g49_26 : reg n49 (26 : Fin 32) = x26 := by rw [u49.regs, g48_26]
    have g49_27 : reg n49 (27 : Fin 32) = 0 := by rw [u49.regs, g48_27]
    have keep_kk49 : SvKeepL B n0.mem n49.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m49]; exact keep_kk48
    clear keep_kk48
    have w49_74 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m49]; exact w48_74
    have w49_78 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m49]; exact w48_78
    have w49_25c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m49]; exact w48_25c
    have w49_260 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m49]; exact w48_260
    have w49_264 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m49]; exact w48_264
    have w49_268 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m49]; exact w48_268
    have w49_27c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m49]; exact w48_27c
    have w49_280 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m49]; exact w48_280
    have w49_284 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m49]; exact w48_284
    have w49_288 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m49]; exact w48_288
    have w49_3e0 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m49]; exact w48_3e0
    have w49_3e4 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m49]; exact w48_3e4
    have w49_420 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m49]; exact w48_420
    have w49_428 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m49]; exact w48_428
    have w49_42c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m49]; exact w48_42c
    clear w48_42c w48_428 w48_420 w48_3e4 w48_3e0 w48_288 w48_284 w48_280 w48_27c w48_268 w48_264 w48_260 w48_25c w48_78 w48_74 g48_27 g48_26 g48_25 g48_24 g48_23 g48_22 g48_21 g48_20 g48_19 g48_18 g48_9 g48_4 g48_3 g48_2 V48 E48 fR48 t48 fr48 m48 s48 u48 d48
    exact .inl ⟨(fun ⟨tl9', h0', h1', h2', te20', h3', op26', ol26', h4', to26', h5', tl30', h6', h7', te39', h8', vp45', vl45', h9', _⟩ => by rw [hr9] at h0'; cases h0'; rw [hr20] at h2'; cases h2'; rw [hte20] at h3'; cases h3'; rw [hr26] at h4'; cases h4'; rw [ht26] at h5'; cases h5'; rw [hr30] at h6'; cases h6'; rw [hr39] at h7'; cases h7'; rw [hte39] at h8'; cases h8'; rw [hr45] at h9'; cases h9'), sv_fail F E49 s49 t49 (fun x hx => (fR49 x hx).trans (fM x hx).symm) V49 hret g49_2 g49_18 hO g49_3 g49_4⟩
  obtain ⟨te45, ht45, -, -⟩ := content_ok_elem hr45
  obtain ⟨p0_45, p4_45⟩ := Ok45 vp45 vl45 hr45
  obtain ⟨d8_45, d12_45⟩ := A45 te45 ht45
  have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8)] := keep_kk44.trans K45
  clear keep_kk44
  have w45_74 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := (K45.w32 (by decide) (by decide)).trans w44_74
  have w45_78 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := (K45.w32 (by decide) (by decide)).trans w44_78
  have w45_25c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := (K45.w32 (by decide) (by decide)).trans w44_25c
  have w45_260 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := (K45.w32 (by decide) (by decide)).trans w44_260
  have w45_264 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := (K45.w32 (by decide) (by decide)).trans w44_264
  have w45_268 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := (K45.w32 (by decide) (by decide)).trans w44_268
  have w45_27c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := (K45.w32 (by decide) (by decide)).trans w44_27c
  have w45_280 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := (K45.w32 (by decide) (by decide)).trans w44_280
  have w45_284 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K45.w32 (by decide) (by decide)).trans w44_284
  have w45_288 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K45.w32 (by decide) (by decide)).trans w44_288
  have w45_3e0 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K45.w32 (by decide) (by decide)).trans w44_3e0
  have w45_3e4 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := (K45.w32 (by decide) (by decide)).trans w44_3e4
  have w45_428 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := (K45.w32 (by decide) (by decide)).trans w44_428
  have w45_42c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := (K45.w32 (by decide) (by decide)).trans w44_42c
  have w45_3e8 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 (te45.header + te45.len) := d8_45
  have w45_3ec : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) := d12_45
  have w45_420 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp45 := p0_45
  have w45_424 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl45 := p4_45
  clear b44_427 b44_426 b44_425 b44_424 w44_42c w44_428 w44_424 w44_420 w44_3ec w44_3e8 w44_3e4 w44_3e0 w44_288 w44_284 w44_280 w44_27c w44_268 w44_264 w44_260 w44_25c w44_78 w44_74 g44_11 g44_10 g44_27 g44_26 g44_25 g44_24 g44_23 g44_22 g44_21 g44_20 g44_19 g44_18 g44_9 g44_8 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 rb44 s44 m44 u44 c44
  -- 0x1180: lw
  obtain ⟨n46, d46, u46⟩ := s45.lw E45.self sv_at_1180 (off' := 0x1184) (by decide)
    (by rw [g45_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s46 : St n46.mem SV n46 0x1184 (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
  have m46 : n46.mem = n45.mem := u46.mem
  have fr46 : ∀ x, SvR B x → n46.mem x = n45.mem x := fun x _ => by rw [m46]
  have t46 : Steps n0 n46 := t45.trans (.single d46)
  have fR46 : ∀ x, SvR B x → n46.mem x = M0 x := fun x hx => (fr46 x hx).trans (fR45 x hx)
  have E46 : SvCode n46.mem := E45.fr F fr46
  have V46 : SvSaves B n46.mem v := V45.same m46
  have g46_2 : reg n46 sp = B + 0x21A0 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_2]
  have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u46.regs, upd_ne (by decide) (by decide), g45_3]
  have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u46.regs, upd_ne (by decide) (by decide), g45_4]
  have g46_8 : reg n46 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_8]
  have g46_9 : reg n46 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u46.regs, upd_ne (by decide) (by decide), g45_9]
  have g46_18 : reg n46 (18 : Fin 32) = out := by rw [u46.regs, upd_ne (by decide) (by decide), g45_18]
  have g46_19 : reg n46 (19 : Fin 32) = bp := by rw [u46.regs, upd_ne (by decide) (by decide), g45_19]
  have g46_20 : reg n46 (20 : Fin 32) = x20 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_20]
  have g46_21 : reg n46 (21 : Fin 32) = x21 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_21]
  have g46_22 : reg n46 (22 : Fin 32) = x22 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_22]
  have g46_23 : reg n46 (23 : Fin 32) = x23 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_23]
  have g46_24 : reg n46 (24 : Fin 32) = x24 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_24]
  have g46_25 : reg n46 (25 : Fin 32) = x25 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_25]
  have g46_26 : reg n46 (26 : Fin 32) = x26 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_26]
  have g46_27 : reg n46 (27 : Fin 32) = vp45 := by
    rw [u46.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g45_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w45_420]
  have keep_kk46 : SvKeepL B n0.mem n46.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m46]; exact keep_kk45
  clear keep_kk45
  have w46_74 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m46]; exact w45_74
  have w46_78 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m46]; exact w45_78
  have w46_25c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m46]; exact w45_25c
  have w46_260 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m46]; exact w45_260
  have w46_264 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m46]; exact w45_264
  have w46_268 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m46]; exact w45_268
  have w46_27c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m46]; exact w45_27c
  have w46_280 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m46]; exact w45_280
  have w46_284 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m46]; exact w45_284
  have w46_288 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m46]; exact w45_288
  have w46_3e0 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m46]; exact w45_3e0
  have w46_3e4 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m46]; exact w45_3e4
  have w46_3e8 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 (te45.header + te45.len) := by rw [m46]; exact w45_3e8
  have w46_3ec : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) := by rw [m46]; exact w45_3ec
  have w46_420 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp45 := by rw [m46]; exact w45_420
  have w46_424 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl45 := by rw [m46]; exact w45_424
  have w46_428 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m46]; exact w45_428
  have w46_42c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m46]; exact w45_42c
  clear w45_424 w45_420 w45_3ec w45_3e8 w45_42c w45_428 w45_3e4 w45_3e0 w45_288 w45_284 w45_280 w45_27c w45_268 w45_264 w45_260 w45_25c w45_78 w45_74 d12_45 d8_45 p4_45 p0_45 g45_27 g45_26 g45_25 g45_24 g45_23 g45_22 g45_21 g45_20 g45_19 g45_18 g45_9 g45_8 g45_4 g45_3 g45_2 V45 E45 fR45 t45 fr45 Er45 Ok45 A45 K45 rk45 sp45 s45 c45
  -- 0x1184: branch, not taken
  obtain ⟨n47, d47, u47⟩ := s46.notTaken E46.self 0x1188 sv_at_1184
    (by decide) (by rw [g46_27, s46.zero]; exact br_beq_f (((((((tst_in.contentW hr9).restW hte20).restW (derOid_ok_elem ht26)).contentW hr30).restW hte39).contentIn hr45).pos_ne))
  have s47 : St n47.mem SV n47 0x1188 (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
  have m47 : n47.mem = n46.mem := u47.mem
  have fr47 : ∀ x, SvR B x → n47.mem x = n46.mem x := fun x _ => by rw [m47]
  have t47 : Steps n0 n47 := t46.trans (.single d47)
  have fR47 : ∀ x, SvR B x → n47.mem x = M0 x := fun x hx => (fr47 x hx).trans (fR46 x hx)
  have E47 : SvCode n47.mem := E46.fr F fr47
  have V47 : SvSaves B n47.mem v := V46.same m47
  have g47_2 : reg n47 sp = B + 0x21A0 := by rw [u47.regs, g46_2]
  have g47_3 : reg n47 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u47.regs, g46_3]
  have g47_4 : reg n47 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u47.regs, g46_4]
  have g47_8 : reg n47 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u47.regs, g46_8]
  have g47_9 : reg n47 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u47.regs, g46_9]
  have g47_18 : reg n47 (18 : Fin 32) = out := by rw [u47.regs, g46_18]
  have g47_19 : reg n47 (19 : Fin 32) = bp := by rw [u47.regs, g46_19]
  have g47_20 : reg n47 (20 : Fin 32) = x20 := by rw [u47.regs, g46_20]
  have g47_21 : reg n47 (21 : Fin 32) = x21 := by rw [u47.regs, g46_21]
  have g47_22 : reg n47 (22 : Fin 32) = x22 := by rw [u47.regs, g46_22]
  have g47_23 : reg n47 (23 : Fin 32) = x23 := by rw [u47.regs, g46_23]
  have g47_24 : reg n47 (24 : Fin 32) = x24 := by rw [u47.regs, g46_24]
  have g47_25 : reg n47 (25 : Fin 32) = x25 := by rw [u47.regs, g46_25]
  have g47_26 : reg n47 (26 : Fin 32) = x26 := by rw [u47.regs, g46_26]
  have g47_27 : reg n47 (27 : Fin 32) = vp45 := by rw [u47.regs, g46_27]
  have keep_kk47 : SvKeepL B n0.mem n47.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m47]; exact keep_kk46
  clear keep_kk46
  have w47_74 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m47]; exact w46_74
  have w47_78 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m47]; exact w46_78
  have w47_25c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m47]; exact w46_25c
  have w47_260 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m47]; exact w46_260
  have w47_264 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m47]; exact w46_264
  have w47_268 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m47]; exact w46_268
  have w47_27c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m47]; exact w46_27c
  have w47_280 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m47]; exact w46_280
  have w47_284 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m47]; exact w46_284
  have w47_288 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m47]; exact w46_288
  have w47_3e0 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m47]; exact w46_3e0
  have w47_3e4 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m47]; exact w46_3e4
  have w47_3e8 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 (te45.header + te45.len) := by rw [m47]; exact w46_3e8
  have w47_3ec : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) := by rw [m47]; exact w46_3ec
  have w47_420 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp45 := by rw [m47]; exact w46_420
  have w47_424 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl45 := by rw [m47]; exact w46_424
  have w47_428 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m47]; exact w46_428
  have w47_42c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m47]; exact w46_42c
  clear w46_42c w46_428 w46_424 w46_420 w46_3ec w46_3e8 w46_3e4 w46_3e0 w46_288 w46_284 w46_280 w46_27c w46_268 w46_264 w46_260 w46_25c w46_78 w46_74 g46_27 g46_26 g46_25 g46_24 g46_23 g46_22 g46_21 g46_20 g46_19 g46_18 g46_9 g46_8 g46_4 g46_3 g46_2 V46 E46 fR46 t46 fr46 m46 s46 u46 d46
  -- 0x1188: lw
  obtain ⟨n48, d48, u48⟩ := s47.lw E47.self sv_at_1188 (off' := 0x118C) (by decide)
    (by rw [g47_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s48 : St n48.mem SV n48 0x118C (reg n48) := ⟨u48.pc, rfl, fun _ => rfl⟩
  have m48 : n48.mem = n47.mem := u48.mem
  have fr48 : ∀ x, SvR B x → n48.mem x = n47.mem x := fun x _ => by rw [m48]
  have t48 : Steps n0 n48 := t47.trans (.single d48)
  have fR48 : ∀ x, SvR B x → n48.mem x = M0 x := fun x hx => (fr48 x hx).trans (fR47 x hx)
  have E48 : SvCode n48.mem := E47.fr F fr48
  have V48 : SvSaves B n48.mem v := V47.same m48
  have g48_2 : reg n48 sp = B + 0x21A0 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_2]
  have g48_3 : reg n48 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u48.regs, upd_ne (by decide) (by decide), g47_3]
  have g48_4 : reg n48 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u48.regs, upd_ne (by decide) (by decide), g47_4]
  have g48_8 : reg n48 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_8]
  have g48_9 : reg n48 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u48.regs, upd_ne (by decide) (by decide), g47_9]
  have g48_18 : reg n48 (18 : Fin 32) = out := by rw [u48.regs, upd_ne (by decide) (by decide), g47_18]
  have g48_19 : reg n48 (19 : Fin 32) = bp := by rw [u48.regs, upd_ne (by decide) (by decide), g47_19]
  have g48_20 : reg n48 (20 : Fin 32) = x20 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_20]
  have g48_21 : reg n48 (21 : Fin 32) = x21 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_21]
  have g48_22 : reg n48 (22 : Fin 32) = x22 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_22]
  have g48_23 : reg n48 (23 : Fin 32) = x23 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_23]
  have g48_24 : reg n48 (24 : Fin 32) = x24 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_24]
  have g48_25 : reg n48 (25 : Fin 32) = x25 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_25]
  have g48_26 : reg n48 (26 : Fin 32) = x26 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_26]
  have g48_27 : reg n48 (27 : Fin 32) = vp45 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_27]
  have g48_10 : reg n48 a0 = vl45 := by
    rw [u48.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g47_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w47_424]
  have keep_kk48 : SvKeepL B n0.mem n48.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m48]; exact keep_kk47
  clear keep_kk47
  have w48_74 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m48]; exact w47_74
  have w48_78 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m48]; exact w47_78
  have w48_25c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m48]; exact w47_25c
  have w48_260 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m48]; exact w47_260
  have w48_264 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m48]; exact w47_264
  have w48_268 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m48]; exact w47_268
  have w48_27c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m48]; exact w47_27c
  have w48_280 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m48]; exact w47_280
  have w48_284 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m48]; exact w47_284
  have w48_288 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m48]; exact w47_288
  have w48_3e0 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m48]; exact w47_3e0
  have w48_3e4 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m48]; exact w47_3e4
  have w48_3e8 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 (te45.header + te45.len) := by rw [m48]; exact w47_3e8
  have w48_3ec : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) := by rw [m48]; exact w47_3ec
  have w48_420 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp45 := by rw [m48]; exact w47_420
  have w48_424 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl45 := by rw [m48]; exact w47_424
  have w48_428 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m48]; exact w47_428
  have w48_42c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m48]; exact w47_42c
  clear w47_42c w47_428 w47_424 w47_420 w47_3ec w47_3e8 w47_3e4 w47_3e0 w47_288 w47_284 w47_280 w47_27c w47_268 w47_264 w47_260 w47_25c w47_78 w47_74 g47_27 g47_26 g47_25 g47_24 g47_23 g47_22 g47_21 g47_20 g47_19 g47_18 g47_9 g47_8 g47_4 g47_3 g47_2 V47 E47 fR47 t47 fr47 m47 s47 u47 d47
  -- 0x118C
  obtain ⟨n49, c49, u49⟩ := s48.block svTt1118c E48.self svTt1118c_end
    ⟨trivial, trivial⟩
  have m49 : n49.mem = n48.mem := u49.mem
  have s49 : St n49.mem SV n49 0x118E (reg n49) := ⟨u49.pc, rfl, fun _ => rfl⟩
  have rb49 : ∀ q, reg n49 q = (runBlock svTt1118c (n48.mem, reg n48)).2 q := fun q => by rw [u49.regs]
  have fr49 : ∀ x, SvR B x → n49.mem x = n48.mem x := fun x _ => by rw [m49]
  have t49 : Steps n0 n49 := t48.trans c49
  have fR49 : ∀ x, SvR B x → n49.mem x = M0 x := fun x hx => (fr49 x hx).trans (fR48 x hx)
  have E49 : SvCode n49.mem := E48.fr F fr49
  have V49 : SvSaves B n49.mem v := V48.same m49
  have g49_2 : reg n49 sp = B + 0x21A0 := by
    rw [rb49, runBlock_reg _ _ _ sp s48.zero (by decide), g48_2]
  have g49_3 : reg n49 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb49, runBlock_reg _ _ _ (3 : Fin 32) s48.zero (by decide), g48_3]
  have g49_4 : reg n49 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb49, runBlock_reg _ _ _ (4 : Fin 32) s48.zero (by decide), g48_4]
  have g49_8 : reg n49 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb49, runBlock_reg _ _ _ (8 : Fin 32) s48.zero (by decide), g48_8]
  have g49_9 : reg n49 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by
    rw [rb49, runBlock_reg _ _ _ (9 : Fin 32) s48.zero (by decide), g48_9]
  have g49_18 : reg n49 (18 : Fin 32) = out := by
    rw [rb49, runBlock_reg _ _ _ (18 : Fin 32) s48.zero (by decide), g48_18]
  have g49_19 : reg n49 (19 : Fin 32) = bp := by
    rw [rb49, runBlock_reg _ _ _ (19 : Fin 32) s48.zero (by decide), g48_19]
  have g49_20 : reg n49 (20 : Fin 32) = x20 := by
    rw [rb49, runBlock_reg _ _ _ (20 : Fin 32) s48.zero (by decide), g48_20]
  have g49_21 : reg n49 (21 : Fin 32) = x21 := by
    rw [rb49, runBlock_reg _ _ _ (21 : Fin 32) s48.zero (by decide), g48_21]
  have g49_22 : reg n49 (22 : Fin 32) = x22 := by
    rw [rb49, runBlock_reg _ _ _ (22 : Fin 32) s48.zero (by decide), g48_22]
  have g49_23 : reg n49 (23 : Fin 32) = x23 := by
    rw [rb49, runBlock_reg _ _ _ (23 : Fin 32) s48.zero (by decide), g48_23]
  have g49_24 : reg n49 (24 : Fin 32) = x24 := by
    rw [rb49, runBlock_reg _ _ _ (24 : Fin 32) s48.zero (by decide), g48_24]
  have g49_25 : reg n49 (25 : Fin 32) = x25 := by
    rw [rb49, runBlock_reg _ _ _ (25 : Fin 32) s48.zero (by decide), g48_25]
  have g49_26 : reg n49 (26 : Fin 32) = x26 := by
    rw [rb49, runBlock_reg _ _ _ (26 : Fin 32) s48.zero (by decide), g48_26]
  have g49_27 : reg n49 (27 : Fin 32) = vp45 := by
    rw [rb49, runBlock_reg _ _ _ (27 : Fin 32) s48.zero (by decide), g48_27]
  have g49_10 : reg n49 a0 = (vl45) + BitVec.ofNat 32 0xFFFFFFE0 := by
    rw [rb49, ← g48_10]; rfl
  have keep_kk49 : SvKeepL B n0.mem n49.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m49]; exact keep_kk48
  clear keep_kk48
  have w49_74 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m49]; exact w48_74
  have w49_78 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m49]; exact w48_78
  have w49_25c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m49]; exact w48_25c
  have w49_260 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m49]; exact w48_260
  have w49_264 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m49]; exact w48_264
  have w49_268 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m49]; exact w48_268
  have w49_27c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m49]; exact w48_27c
  have w49_280 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m49]; exact w48_280
  have w49_284 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m49]; exact w48_284
  have w49_288 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m49]; exact w48_288
  have w49_3e0 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m49]; exact w48_3e0
  have w49_3e4 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m49]; exact w48_3e4
  have w49_3e8 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 (te45.header + te45.len) := by rw [m49]; exact w48_3e8
  have w49_3ec : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) := by rw [m49]; exact w48_3ec
  have w49_420 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp45 := by rw [m49]; exact w48_420
  have w49_424 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl45 := by rw [m49]; exact w48_424
  have w49_428 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m49]; exact w48_428
  have w49_42c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m49]; exact w48_42c
  clear w48_42c w48_428 w48_424 w48_420 w48_3ec w48_3e8 w48_3e4 w48_3e0 w48_288 w48_284 w48_280 w48_27c w48_268 w48_264 w48_260 w48_25c w48_78 w48_74 g48_10 g48_27 g48_26 g48_25 g48_24 g48_23 g48_22 g48_21 g48_20 g48_19 g48_18 g48_9 g48_8 g48_4 g48_3 g48_2 V48 E48 fR48 t48 fr48 m48 s48 u48 d48
  by_cases h32 : vl45 = 32
  rotate_left
  · -- 0x118E: branch, taken
    obtain ⟨n50, d50, u50⟩ := s49.taken E49.self 0x7A4 sv_at_118e
      (by decide) (by rw [g49_10, s49.zero]; exact br_m32_t h32)
    have s50 : St n50.mem SV n50 0x7A4 (reg n50) := ⟨u50.pc, rfl, fun _ => rfl⟩
    have m50 : n50.mem = n49.mem := u50.mem
    have fr50 : ∀ x, SvR B x → n50.mem x = n49.mem x := fun x _ => by rw [m50]
    have t50 : Steps n0 n50 := t49.trans (.single d50)
    have fR50 : ∀ x, SvR B x → n50.mem x = M0 x := fun x hx => (fr50 x hx).trans (fR49 x hx)
    have E50 : SvCode n50.mem := E49.fr F fr50
    have V50 : SvSaves B n50.mem v := V49.same m50
    have g50_2 : reg n50 sp = B + 0x21A0 := by rw [u50.regs, g49_2]
    have g50_3 : reg n50 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u50.regs, g49_3]
    have g50_4 : reg n50 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u50.regs, g49_4]
    have g50_8 : reg n50 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u50.regs, g49_8]
    have g50_9 : reg n50 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u50.regs, g49_9]
    have g50_10 : reg n50 a0 = (vl45) + BitVec.ofNat 32 0xFFFFFFE0 := by rw [u50.regs, g49_10]
    have g50_18 : reg n50 (18 : Fin 32) = out := by rw [u50.regs, g49_18]
    have g50_19 : reg n50 (19 : Fin 32) = bp := by rw [u50.regs, g49_19]
    have g50_20 : reg n50 (20 : Fin 32) = x20 := by rw [u50.regs, g49_20]
    have g50_21 : reg n50 (21 : Fin 32) = x21 := by rw [u50.regs, g49_21]
    have g50_22 : reg n50 (22 : Fin 32) = x22 := by rw [u50.regs, g49_22]
    have g50_23 : reg n50 (23 : Fin 32) = x23 := by rw [u50.regs, g49_23]
    have g50_24 : reg n50 (24 : Fin 32) = x24 := by rw [u50.regs, g49_24]
    have g50_25 : reg n50 (25 : Fin 32) = x25 := by rw [u50.regs, g49_25]
    have g50_26 : reg n50 (26 : Fin 32) = x26 := by rw [u50.regs, g49_26]
    have g50_27 : reg n50 (27 : Fin 32) = vp45 := by rw [u50.regs, g49_27]
    have keep_kk50 : SvKeepL B n0.mem n50.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m50]; exact keep_kk49
    clear keep_kk49
    have w50_74 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m50]; exact w49_74
    have w50_78 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m50]; exact w49_78
    have w50_25c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m50]; exact w49_25c
    have w50_260 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m50]; exact w49_260
    have w50_264 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m50]; exact w49_264
    have w50_268 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m50]; exact w49_268
    have w50_27c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m50]; exact w49_27c
    have w50_280 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m50]; exact w49_280
    have w50_284 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m50]; exact w49_284
    have w50_288 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m50]; exact w49_288
    have w50_3e0 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m50]; exact w49_3e0
    have w50_3e4 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m50]; exact w49_3e4
    have w50_3e8 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 (te45.header + te45.len) := by rw [m50]; exact w49_3e8
    have w50_3ec : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) := by rw [m50]; exact w49_3ec
    have w50_420 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp45 := by rw [m50]; exact w49_420
    have w50_424 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl45 := by rw [m50]; exact w49_424
    have w50_428 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m50]; exact w49_428
    have w50_42c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m50]; exact w49_42c
    clear w49_42c w49_428 w49_424 w49_420 w49_3ec w49_3e8 w49_3e4 w49_3e0 w49_288 w49_284 w49_280 w49_27c w49_268 w49_264 w49_260 w49_25c w49_78 w49_74 g49_10 g49_27 g49_26 g49_25 g49_24 g49_23 g49_22 g49_21 g49_20 g49_19 g49_18 g49_9 g49_8 g49_4 g49_3 g49_2 V49 E49 fR49 t49 fr49 rb49 s49 m49 u49 c49
    exact .inl ⟨(fun ⟨tl9', h0', h1', h2', te20', h3', op26', ol26', h4', to26', h5', tl30', h6', h7', te39', h8', vp45', vl45', h9', te45', h10', h11', _⟩ => by rw [hr9] at h0'; cases h0'; rw [hr20] at h2'; cases h2'; rw [hte20] at h3'; cases h3'; rw [hr26] at h4'; cases h4'; rw [ht26] at h5'; cases h5'; rw [hr30] at h6'; cases h6'; rw [hr39] at h7'; cases h7'; rw [hte39] at h8'; cases h8'; rw [hr45] at h9'; cases h9'; rw [ht45] at h10'; cases h10'; exact h32 h11'), sv_fail F E50 s50 t50 (fun x hx => (fR50 x hx).trans (fM x hx).symm) V50 hret g50_2 g50_18 hO g50_3 g50_4⟩
  -- 0x118E: branch, not taken
  obtain ⟨n50, d50, u50⟩ := s49.notTaken E49.self 0x1192 sv_at_118e
    (by decide) (by rw [g49_10, s49.zero]; exact br_m32_f h32)
  have s50 : St n50.mem SV n50 0x1192 (reg n50) := ⟨u50.pc, rfl, fun _ => rfl⟩
  have m50 : n50.mem = n49.mem := u50.mem
  have fr50 : ∀ x, SvR B x → n50.mem x = n49.mem x := fun x _ => by rw [m50]
  have t50 : Steps n0 n50 := t49.trans (.single d50)
  have fR50 : ∀ x, SvR B x → n50.mem x = M0 x := fun x hx => (fr50 x hx).trans (fR49 x hx)
  have E50 : SvCode n50.mem := E49.fr F fr50
  have V50 : SvSaves B n50.mem v := V49.same m50
  have g50_2 : reg n50 sp = B + 0x21A0 := by rw [u50.regs, g49_2]
  have g50_3 : reg n50 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u50.regs, g49_3]
  have g50_4 : reg n50 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u50.regs, g49_4]
  have g50_8 : reg n50 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u50.regs, g49_8]
  have g50_9 : reg n50 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u50.regs, g49_9]
  have g50_10 : reg n50 a0 = (vl45) + BitVec.ofNat 32 0xFFFFFFE0 := by rw [u50.regs, g49_10]
  have g50_18 : reg n50 (18 : Fin 32) = out := by rw [u50.regs, g49_18]
  have g50_19 : reg n50 (19 : Fin 32) = bp := by rw [u50.regs, g49_19]
  have g50_20 : reg n50 (20 : Fin 32) = x20 := by rw [u50.regs, g49_20]
  have g50_21 : reg n50 (21 : Fin 32) = x21 := by rw [u50.regs, g49_21]
  have g50_22 : reg n50 (22 : Fin 32) = x22 := by rw [u50.regs, g49_22]
  have g50_23 : reg n50 (23 : Fin 32) = x23 := by rw [u50.regs, g49_23]
  have g50_24 : reg n50 (24 : Fin 32) = x24 := by rw [u50.regs, g49_24]
  have g50_25 : reg n50 (25 : Fin 32) = x25 := by rw [u50.regs, g49_25]
  have g50_26 : reg n50 (26 : Fin 32) = x26 := by rw [u50.regs, g49_26]
  have g50_27 : reg n50 (27 : Fin 32) = vp45 := by rw [u50.regs, g49_27]
  have keep_kk50 : SvKeepL B n0.mem n50.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m50]; exact keep_kk49
  clear keep_kk49
  have w50_74 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m50]; exact w49_74
  have w50_78 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m50]; exact w49_78
  have w50_25c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m50]; exact w49_25c
  have w50_260 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m50]; exact w49_260
  have w50_264 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m50]; exact w49_264
  have w50_268 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m50]; exact w49_268
  have w50_27c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m50]; exact w49_27c
  have w50_280 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m50]; exact w49_280
  have w50_284 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m50]; exact w49_284
  have w50_288 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m50]; exact w49_288
  have w50_3e0 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m50]; exact w49_3e0
  have w50_3e4 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m50]; exact w49_3e4
  have w50_3e8 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 (te45.header + te45.len) := by rw [m50]; exact w49_3e8
  have w50_3ec : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) := by rw [m50]; exact w49_3ec
  have w50_420 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp45 := by rw [m50]; exact w49_420
  have w50_424 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl45 := by rw [m50]; exact w49_424
  have w50_428 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m50]; exact w49_428
  have w50_42c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m50]; exact w49_42c
  clear w49_42c w49_428 w49_424 w49_420 w49_3ec w49_3e8 w49_3e4 w49_3e0 w49_288 w49_284 w49_280 w49_27c w49_268 w49_264 w49_260 w49_25c w49_78 w49_74 g49_10 g49_27 g49_26 g49_25 g49_24 g49_23 g49_22 g49_21 g49_20 g49_19 g49_18 g49_9 g49_8 g49_4 g49_3 g49_2 V49 E49 fR49 t49 fr49 rb49 s49 m49 u49 c49
  -- 0x1192: lw
  obtain ⟨n51, d51, u51⟩ := s50.lw E50.self sv_at_1192 (off' := 0x1196) (by decide)
    (by rw [g50_2, show B + 0x21A0 + 0x3EC = B + 0x21A0 + BitVec.ofNat 32 0x3EC by sv_addr]; exact sv_al F (by decide) (by decide))
  have s51 : St n51.mem SV n51 0x1196 (reg n51) := ⟨u51.pc, rfl, fun _ => rfl⟩
  have m51 : n51.mem = n50.mem := u51.mem
  have fr51 : ∀ x, SvR B x → n51.mem x = n50.mem x := fun x _ => by rw [m51]
  have t51 : Steps n0 n51 := t50.trans (.single d51)
  have fR51 : ∀ x, SvR B x → n51.mem x = M0 x := fun x hx => (fr51 x hx).trans (fR50 x hx)
  have E51 : SvCode n51.mem := E50.fr F fr51
  have V51 : SvSaves B n51.mem v := V50.same m51
  have g51_2 : reg n51 sp = B + 0x21A0 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_2]
  have g51_3 : reg n51 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u51.regs, upd_ne (by decide) (by decide), g50_3]
  have g51_4 : reg n51 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u51.regs, upd_ne (by decide) (by decide), g50_4]
  have g51_8 : reg n51 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_8]
  have g51_9 : reg n51 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u51.regs, upd_ne (by decide) (by decide), g50_9]
  have g51_18 : reg n51 (18 : Fin 32) = out := by rw [u51.regs, upd_ne (by decide) (by decide), g50_18]
  have g51_19 : reg n51 (19 : Fin 32) = bp := by rw [u51.regs, upd_ne (by decide) (by decide), g50_19]
  have g51_20 : reg n51 (20 : Fin 32) = x20 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_20]
  have g51_21 : reg n51 (21 : Fin 32) = x21 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_21]
  have g51_22 : reg n51 (22 : Fin 32) = x22 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_22]
  have g51_23 : reg n51 (23 : Fin 32) = x23 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_23]
  have g51_24 : reg n51 (24 : Fin 32) = x24 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_24]
  have g51_25 : reg n51 (25 : Fin 32) = x25 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_25]
  have g51_26 : reg n51 (26 : Fin 32) = x26 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_26]
  have g51_27 : reg n51 (27 : Fin 32) = vp45 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_27]
  have g51_10 : reg n51 a0 = ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) := by
    rw [u51.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g50_2, show B + 0x21A0 + 0x3EC = B + 0x21A0 + BitVec.ofNat 32 0x3EC by sv_addr, w50_3ec]
  have keep_kk51 : SvKeepL B n0.mem n51.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m51]; exact keep_kk50
  clear keep_kk50
  have w51_74 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m51]; exact w50_74
  have w51_78 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m51]; exact w50_78
  have w51_25c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m51]; exact w50_25c
  have w51_260 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m51]; exact w50_260
  have w51_264 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m51]; exact w50_264
  have w51_268 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m51]; exact w50_268
  have w51_27c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m51]; exact w50_27c
  have w51_280 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m51]; exact w50_280
  have w51_284 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m51]; exact w50_284
  have w51_288 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m51]; exact w50_288
  have w51_3e0 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m51]; exact w50_3e0
  have w51_3e4 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m51]; exact w50_3e4
  have w51_3e8 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 (te45.header + te45.len) := by rw [m51]; exact w50_3e8
  have w51_3ec : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) := by rw [m51]; exact w50_3ec
  have w51_420 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp45 := by rw [m51]; exact w50_420
  have w51_424 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl45 := by rw [m51]; exact w50_424
  have w51_428 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m51]; exact w50_428
  have w51_42c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m51]; exact w50_42c
  clear w50_42c w50_428 w50_424 w50_420 w50_3ec w50_3e8 w50_3e4 w50_3e0 w50_288 w50_284 w50_280 w50_27c w50_268 w50_264 w50_260 w50_25c w50_78 w50_74 g50_27 g50_26 g50_25 g50_24 g50_23 g50_22 g50_21 g50_20 g50_19 g50_18 g50_10 g50_9 g50_8 g50_4 g50_3 g50_2 V50 E50 fR50 t50 fr50 m50 s50 u50 d50
  by_cases hrest1 : ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) = 0
  rotate_left
  · -- 0x1196: branch, not taken
    obtain ⟨n52, d52, u52⟩ := s51.notTaken E51.self 0x1198 sv_at_1196
      (by decide) (by rw [g51_10, s51.zero]; exact br_beq_f hrest1)
    have s52 : St n52.mem SV n52 0x1198 (reg n52) := ⟨u52.pc, rfl, fun _ => rfl⟩
    have m52 : n52.mem = n51.mem := u52.mem
    have fr52 : ∀ x, SvR B x → n52.mem x = n51.mem x := fun x _ => by rw [m52]
    have t52 : Steps n0 n52 := t51.trans (.single d52)
    have fR52 : ∀ x, SvR B x → n52.mem x = M0 x := fun x hx => (fr52 x hx).trans (fR51 x hx)
    have E52 : SvCode n52.mem := E51.fr F fr52
    have V52 : SvSaves B n52.mem v := V51.same m52
    have g52_2 : reg n52 sp = B + 0x21A0 := by rw [u52.regs, g51_2]
    have g52_3 : reg n52 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u52.regs, g51_3]
    have g52_4 : reg n52 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u52.regs, g51_4]
    have g52_8 : reg n52 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u52.regs, g51_8]
    have g52_9 : reg n52 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u52.regs, g51_9]
    have g52_10 : reg n52 a0 = ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) := by rw [u52.regs, g51_10]
    have g52_18 : reg n52 (18 : Fin 32) = out := by rw [u52.regs, g51_18]
    have g52_19 : reg n52 (19 : Fin 32) = bp := by rw [u52.regs, g51_19]
    have g52_20 : reg n52 (20 : Fin 32) = x20 := by rw [u52.regs, g51_20]
    have g52_21 : reg n52 (21 : Fin 32) = x21 := by rw [u52.regs, g51_21]
    have g52_22 : reg n52 (22 : Fin 32) = x22 := by rw [u52.regs, g51_22]
    have g52_23 : reg n52 (23 : Fin 32) = x23 := by rw [u52.regs, g51_23]
    have g52_24 : reg n52 (24 : Fin 32) = x24 := by rw [u52.regs, g51_24]
    have g52_25 : reg n52 (25 : Fin 32) = x25 := by rw [u52.regs, g51_25]
    have g52_26 : reg n52 (26 : Fin 32) = x26 := by rw [u52.regs, g51_26]
    have g52_27 : reg n52 (27 : Fin 32) = vp45 := by rw [u52.regs, g51_27]
    have keep_kk52 : SvKeepL B n0.mem n52.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m52]; exact keep_kk51
    clear keep_kk51
    have w52_74 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m52]; exact w51_74
    have w52_78 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m52]; exact w51_78
    have w52_25c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m52]; exact w51_25c
    have w52_260 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m52]; exact w51_260
    have w52_264 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m52]; exact w51_264
    have w52_268 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m52]; exact w51_268
    have w52_27c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m52]; exact w51_27c
    have w52_280 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m52]; exact w51_280
    have w52_284 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m52]; exact w51_284
    have w52_288 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m52]; exact w51_288
    have w52_3e0 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m52]; exact w51_3e0
    have w52_3e4 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m52]; exact w51_3e4
    have w52_3e8 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 (te45.header + te45.len) := by rw [m52]; exact w51_3e8
    have w52_3ec : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) := by rw [m52]; exact w51_3ec
    have w52_420 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp45 := by rw [m52]; exact w51_420
    have w52_424 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl45 := by rw [m52]; exact w51_424
    have w52_428 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m52]; exact w51_428
    have w52_42c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m52]; exact w51_42c
    clear w51_42c w51_428 w51_424 w51_420 w51_3ec w51_3e8 w51_3e4 w51_3e0 w51_288 w51_284 w51_280 w51_27c w51_268 w51_264 w51_260 w51_25c w51_78 w51_74 g51_10 g51_27 g51_26 g51_25 g51_24 g51_23 g51_22 g51_21 g51_20 g51_19 g51_18 g51_9 g51_8 g51_4 g51_3 g51_2 V51 E51 fR51 t51 fr51 m51 s51 u51 d51
    -- 0x1198: j
    obtain ⟨n53, d53, u53⟩ := s52.jump E52.self sv_at_1198 (off' := 0x14C) (by decide)
      (by rw [s52.pc]; decide)
    have s53 : St n53.mem SV n53 0x14C (reg n53) := ⟨u53.pc, rfl, fun _ => rfl⟩
    have m53 : n53.mem = n52.mem := u53.mem
    have fr53 : ∀ x, SvR B x → n53.mem x = n52.mem x := fun x _ => by rw [m53]
    have t53 : Steps n0 n53 := t52.trans (.single d53)
    have fR53 : ∀ x, SvR B x → n53.mem x = M0 x := fun x hx => (fr53 x hx).trans (fR52 x hx)
    have E53 : SvCode n53.mem := E52.fr F fr53
    have V53 : SvSaves B n53.mem v := V52.same m53
    have g53_2 : reg n53 sp = B + 0x21A0 := by rw [u53.regs, g52_2]
    have g53_3 : reg n53 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u53.regs, g52_3]
    have g53_4 : reg n53 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u53.regs, g52_4]
    have g53_8 : reg n53 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u53.regs, g52_8]
    have g53_9 : reg n53 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u53.regs, g52_9]
    have g53_10 : reg n53 a0 = ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) := by rw [u53.regs, g52_10]
    have g53_18 : reg n53 (18 : Fin 32) = out := by rw [u53.regs, g52_18]
    have g53_19 : reg n53 (19 : Fin 32) = bp := by rw [u53.regs, g52_19]
    have g53_20 : reg n53 (20 : Fin 32) = x20 := by rw [u53.regs, g52_20]
    have g53_21 : reg n53 (21 : Fin 32) = x21 := by rw [u53.regs, g52_21]
    have g53_22 : reg n53 (22 : Fin 32) = x22 := by rw [u53.regs, g52_22]
    have g53_23 : reg n53 (23 : Fin 32) = x23 := by rw [u53.regs, g52_23]
    have g53_24 : reg n53 (24 : Fin 32) = x24 := by rw [u53.regs, g52_24]
    have g53_25 : reg n53 (25 : Fin 32) = x25 := by rw [u53.regs, g52_25]
    have g53_26 : reg n53 (26 : Fin 32) = x26 := by rw [u53.regs, g52_26]
    have g53_27 : reg n53 (27 : Fin 32) = vp45 := by rw [u53.regs, g52_27]
    have keep_kk53 : SvKeepL B n0.mem n53.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m53]; exact keep_kk52
    clear keep_kk52
    have w53_74 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m53]; exact w52_74
    have w53_78 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m53]; exact w52_78
    have w53_25c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m53]; exact w52_25c
    have w53_260 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m53]; exact w52_260
    have w53_264 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m53]; exact w52_264
    have w53_268 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m53]; exact w52_268
    have w53_27c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m53]; exact w52_27c
    have w53_280 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m53]; exact w52_280
    have w53_284 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m53]; exact w52_284
    have w53_288 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m53]; exact w52_288
    have w53_3e0 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m53]; exact w52_3e0
    have w53_3e4 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m53]; exact w52_3e4
    have w53_3e8 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 (te45.header + te45.len) := by rw [m53]; exact w52_3e8
    have w53_3ec : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) := by rw [m53]; exact w52_3ec
    have w53_420 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp45 := by rw [m53]; exact w52_420
    have w53_424 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl45 := by rw [m53]; exact w52_424
    have w53_428 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m53]; exact w52_428
    have w53_42c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m53]; exact w52_42c
    clear w52_42c w52_428 w52_424 w52_420 w52_3ec w52_3e8 w52_3e4 w52_3e0 w52_288 w52_284 w52_280 w52_27c w52_268 w52_264 w52_260 w52_25c w52_78 w52_74 g52_27 g52_26 g52_25 g52_24 g52_23 g52_22 g52_21 g52_20 g52_19 g52_18 g52_10 g52_9 g52_8 g52_4 g52_3 g52_2 V52 E52 fR52 t52 fr52 m52 s52 u52 d52
    -- 0x14C
    obtain ⟨n54, c54, u54⟩ := s53.block svTt114c E53.self svTt114c_end
      ⟨trivial, trivial⟩
    have m54 : n54.mem = n53.mem := u54.mem
    have s54 : St n54.mem SV n54 0x14E (reg n54) := ⟨u54.pc, rfl, fun _ => rfl⟩
    have rb54 : ∀ q, reg n54 q = (runBlock svTt114c (n53.mem, reg n53)).2 q := fun q => by rw [u54.regs]
    have fr54 : ∀ x, SvR B x → n54.mem x = n53.mem x := fun x _ => by rw [m54]
    have t54 : Steps n0 n54 := t53.trans c54
    have fR54 : ∀ x, SvR B x → n54.mem x = M0 x := fun x hx => (fr54 x hx).trans (fR53 x hx)
    have E54 : SvCode n54.mem := E53.fr F fr54
    have V54 : SvSaves B n54.mem v := V53.same m54
    have g54_2 : reg n54 sp = B + 0x21A0 := by
      rw [rb54, runBlock_reg _ _ _ sp s53.zero (by decide), g53_2]
    have g54_3 : reg n54 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb54, runBlock_reg _ _ _ (3 : Fin 32) s53.zero (by decide), g53_3]
    have g54_4 : reg n54 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb54, runBlock_reg _ _ _ (4 : Fin 32) s53.zero (by decide), g53_4]
    have g54_9 : reg n54 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by
      rw [rb54, runBlock_reg _ _ _ (9 : Fin 32) s53.zero (by decide), g53_9]
    have g54_10 : reg n54 a0 = ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) := by
      rw [rb54, runBlock_reg _ _ _ a0 s53.zero (by decide), g53_10]
    have g54_18 : reg n54 (18 : Fin 32) = out := by
      rw [rb54, runBlock_reg _ _ _ (18 : Fin 32) s53.zero (by decide), g53_18]
    have g54_19 : reg n54 (19 : Fin 32) = bp := by
      rw [rb54, runBlock_reg _ _ _ (19 : Fin 32) s53.zero (by decide), g53_19]
    have g54_20 : reg n54 (20 : Fin 32) = x20 := by
      rw [rb54, runBlock_reg _ _ _ (20 : Fin 32) s53.zero (by decide), g53_20]
    have g54_21 : reg n54 (21 : Fin 32) = x21 := by
      rw [rb54, runBlock_reg _ _ _ (21 : Fin 32) s53.zero (by decide), g53_21]
    have g54_22 : reg n54 (22 : Fin 32) = x22 := by
      rw [rb54, runBlock_reg _ _ _ (22 : Fin 32) s53.zero (by decide), g53_22]
    have g54_23 : reg n54 (23 : Fin 32) = x23 := by
      rw [rb54, runBlock_reg _ _ _ (23 : Fin 32) s53.zero (by decide), g53_23]
    have g54_24 : reg n54 (24 : Fin 32) = x24 := by
      rw [rb54, runBlock_reg _ _ _ (24 : Fin 32) s53.zero (by decide), g53_24]
    have g54_25 : reg n54 (25 : Fin 32) = x25 := by
      rw [rb54, runBlock_reg _ _ _ (25 : Fin 32) s53.zero (by decide), g53_25]
    have g54_26 : reg n54 (26 : Fin 32) = x26 := by
      rw [rb54, runBlock_reg _ _ _ (26 : Fin 32) s53.zero (by decide), g53_26]
    have g54_27 : reg n54 (27 : Fin 32) = vp45 := by
      rw [rb54, runBlock_reg _ _ _ (27 : Fin 32) s53.zero (by decide), g53_27]
    have g54_8 : reg n54 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb54]; simp +decide only [runBlock, BInstr.run, svTt114c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g53_2, g53_3, g53_4, g53_8, g53_9, g53_10, g53_18, g53_19, g53_20, g53_21, g53_22, g53_23, g53_24, g53_25, g53_26, g53_27, s53.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk54 : SvKeepL B n0.mem n54.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m54]; exact keep_kk53
    clear keep_kk53
    have w54_74 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m54]; exact w53_74
    have w54_78 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m54]; exact w53_78
    have w54_25c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m54]; exact w53_25c
    have w54_260 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m54]; exact w53_260
    have w54_264 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m54]; exact w53_264
    have w54_268 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m54]; exact w53_268
    have w54_27c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m54]; exact w53_27c
    have w54_280 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m54]; exact w53_280
    have w54_284 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m54]; exact w53_284
    have w54_288 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m54]; exact w53_288
    have w54_3e0 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m54]; exact w53_3e0
    have w54_3e4 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m54]; exact w53_3e4
    have w54_3e8 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 (te45.header + te45.len) := by rw [m54]; exact w53_3e8
    have w54_3ec : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) := by rw [m54]; exact w53_3ec
    have w54_420 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp45 := by rw [m54]; exact w53_420
    have w54_424 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl45 := by rw [m54]; exact w53_424
    have w54_428 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m54]; exact w53_428
    have w54_42c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m54]; exact w53_42c
    clear w53_42c w53_428 w53_424 w53_420 w53_3ec w53_3e8 w53_3e4 w53_3e0 w53_288 w53_284 w53_280 w53_27c w53_268 w53_264 w53_260 w53_25c w53_78 w53_74 g53_27 g53_26 g53_25 g53_24 g53_23 g53_22 g53_21 g53_20 g53_19 g53_18 g53_10 g53_9 g53_8 g53_4 g53_3 g53_2 V53 E53 fR53 t53 fr53 m53 s53 u53 d53
    -- 0x14E: j
    obtain ⟨n55, d55, u55⟩ := s54.jump E54.self sv_at_14e (off' := 0x7A4) (by decide)
      (by rw [s54.pc]; decide)
    have s55 : St n55.mem SV n55 0x7A4 (reg n55) := ⟨u55.pc, rfl, fun _ => rfl⟩
    have m55 : n55.mem = n54.mem := u55.mem
    have fr55 : ∀ x, SvR B x → n55.mem x = n54.mem x := fun x _ => by rw [m55]
    have t55 : Steps n0 n55 := t54.trans (.single d55)
    have fR55 : ∀ x, SvR B x → n55.mem x = M0 x := fun x hx => (fr55 x hx).trans (fR54 x hx)
    have E55 : SvCode n55.mem := E54.fr F fr55
    have V55 : SvSaves B n55.mem v := V54.same m55
    have g55_2 : reg n55 sp = B + 0x21A0 := by rw [u55.regs, g54_2]
    have g55_3 : reg n55 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u55.regs, g54_3]
    have g55_4 : reg n55 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u55.regs, g54_4]
    have g55_8 : reg n55 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u55.regs, g54_8]
    have g55_9 : reg n55 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u55.regs, g54_9]
    have g55_10 : reg n55 a0 = ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) := by rw [u55.regs, g54_10]
    have g55_18 : reg n55 (18 : Fin 32) = out := by rw [u55.regs, g54_18]
    have g55_19 : reg n55 (19 : Fin 32) = bp := by rw [u55.regs, g54_19]
    have g55_20 : reg n55 (20 : Fin 32) = x20 := by rw [u55.regs, g54_20]
    have g55_21 : reg n55 (21 : Fin 32) = x21 := by rw [u55.regs, g54_21]
    have g55_22 : reg n55 (22 : Fin 32) = x22 := by rw [u55.regs, g54_22]
    have g55_23 : reg n55 (23 : Fin 32) = x23 := by rw [u55.regs, g54_23]
    have g55_24 : reg n55 (24 : Fin 32) = x24 := by rw [u55.regs, g54_24]
    have g55_25 : reg n55 (25 : Fin 32) = x25 := by rw [u55.regs, g54_25]
    have g55_26 : reg n55 (26 : Fin 32) = x26 := by rw [u55.regs, g54_26]
    have g55_27 : reg n55 (27 : Fin 32) = vp45 := by rw [u55.regs, g54_27]
    have keep_kk55 : SvKeepL B n0.mem n55.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m55]; exact keep_kk54
    clear keep_kk54
    have w55_74 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m55]; exact w54_74
    have w55_78 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m55]; exact w54_78
    have w55_25c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m55]; exact w54_25c
    have w55_260 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m55]; exact w54_260
    have w55_264 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m55]; exact w54_264
    have w55_268 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m55]; exact w54_268
    have w55_27c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m55]; exact w54_27c
    have w55_280 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m55]; exact w54_280
    have w55_284 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m55]; exact w54_284
    have w55_288 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m55]; exact w54_288
    have w55_3e0 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m55]; exact w54_3e0
    have w55_3e4 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m55]; exact w54_3e4
    have w55_3e8 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 (te45.header + te45.len) := by rw [m55]; exact w54_3e8
    have w55_3ec : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) := by rw [m55]; exact w54_3ec
    have w55_420 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp45 := by rw [m55]; exact w54_420
    have w55_424 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl45 := by rw [m55]; exact w54_424
    have w55_428 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m55]; exact w54_428
    have w55_42c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m55]; exact w54_42c
    clear w54_42c w54_428 w54_424 w54_420 w54_3ec w54_3e8 w54_3e4 w54_3e0 w54_288 w54_284 w54_280 w54_27c w54_268 w54_264 w54_260 w54_25c w54_78 w54_74 g54_8 g54_27 g54_26 g54_25 g54_24 g54_23 g54_22 g54_21 g54_20 g54_19 g54_18 g54_10 g54_9 g54_4 g54_3 g54_2 V54 E54 fR54 t54 fr54 rb54 s54 m54 u54 c54
    exact .inl ⟨(fun ⟨tl9', h0', h1', h2', te20', h3', op26', ol26', h4', to26', h5', tl30', h6', h7', te39', h8', vp45', vl45', h9', te45', h10', h11', h12', _⟩ => by rw [hr9] at h0'; cases h0'; rw [hr20] at h2'; cases h2'; rw [hte20] at h3'; cases h3'; rw [hr26] at h4'; cases h4'; rw [ht26] at h5'; cases h5'; rw [hr30] at h6'; cases h6'; rw [hr39] at h7'; cases h7'; rw [hte39] at h8'; cases h8'; rw [hr45] at h9'; cases h9'; rw [ht45] at h10'; cases h10'; exact hrest1 h12'), sv_fail F E55 s55 t55 (fun x hx => (fR55 x hx).trans (fM x hx).symm) V55 hret g55_2 g55_18 hO g55_3 g55_4⟩
  -- 0x1196: branch, taken
  obtain ⟨n52, d52, u52⟩ := s51.taken E51.self 0x119C sv_at_1196
    (by decide) (by rw [g51_10, s51.zero]; exact br_beq_t hrest1)
  have s52 : St n52.mem SV n52 0x119C (reg n52) := ⟨u52.pc, rfl, fun _ => rfl⟩
  have m52 : n52.mem = n51.mem := u52.mem
  have fr52 : ∀ x, SvR B x → n52.mem x = n51.mem x := fun x _ => by rw [m52]
  have t52 : Steps n0 n52 := t51.trans (.single d52)
  have fR52 : ∀ x, SvR B x → n52.mem x = M0 x := fun x hx => (fr52 x hx).trans (fR51 x hx)
  have E52 : SvCode n52.mem := E51.fr F fr52
  have V52 : SvSaves B n52.mem v := V51.same m52
  have g52_2 : reg n52 sp = B + 0x21A0 := by rw [u52.regs, g51_2]
  have g52_3 : reg n52 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u52.regs, g51_3]
  have g52_4 : reg n52 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u52.regs, g51_4]
  have g52_8 : reg n52 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u52.regs, g51_8]
  have g52_9 : reg n52 (9 : Fin 32) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [u52.regs, g51_9]
  have g52_10 : reg n52 a0 = ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) := by rw [u52.regs, g51_10]
  have g52_18 : reg n52 (18 : Fin 32) = out := by rw [u52.regs, g51_18]
  have g52_19 : reg n52 (19 : Fin 32) = bp := by rw [u52.regs, g51_19]
  have g52_20 : reg n52 (20 : Fin 32) = x20 := by rw [u52.regs, g51_20]
  have g52_21 : reg n52 (21 : Fin 32) = x21 := by rw [u52.regs, g51_21]
  have g52_22 : reg n52 (22 : Fin 32) = x22 := by rw [u52.regs, g51_22]
  have g52_23 : reg n52 (23 : Fin 32) = x23 := by rw [u52.regs, g51_23]
  have g52_24 : reg n52 (24 : Fin 32) = x24 := by rw [u52.regs, g51_24]
  have g52_25 : reg n52 (25 : Fin 32) = x25 := by rw [u52.regs, g51_25]
  have g52_26 : reg n52 (26 : Fin 32) = x26 := by rw [u52.regs, g51_26]
  have g52_27 : reg n52 (27 : Fin 32) = vp45 := by rw [u52.regs, g51_27]
  have keep_kk52 : SvKeepL B n0.mem n52.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8)] := by rw [m52]; exact keep_kk51
  clear keep_kk51
  have w52_74 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp := by rw [m52]; exact w51_74
  have w52_78 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl := by rw [m52]; exact w51_78
  have w52_25c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (tp) + BitVec.ofNat 32 tl9.header := by rw [m52]; exact w51_25c
  have w52_260 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = BitVec.ofNat 32 tl9.len := by rw [m52]; exact w51_260
  have w52_264 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m52]; exact w51_264
  have w52_268 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (te20.header + te20.len)) - BitVec.ofNat 32 (to26.header + to26.len)) - BitVec.ofNat 32 (tl30.header + tl30.len) := by rw [m52]; exact w51_268
  have w52_27c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = tp := by rw [m52]; exact w51_27c
  have w52_280 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = tl := by rw [m52]; exact w51_280
  have w52_284 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (tp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m52]; exact w51_284
  have w52_288 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (tl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m52]; exact w51_288
  have w52_3e0 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E0) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m52]; exact w51_3e0
  have w52_3e4 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E4) = BitVec.ofNat 32 tl30.len := by rw [m52]; exact w51_3e4
  have w52_3e8 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x3E8) = ((((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 (te45.header + te45.len) := by rw [m52]; exact w51_3e8
  have w52_3ec : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x3EC) = ((BitVec.ofNat 32 tl30.len) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (te45.header + te45.len) := by rw [m52]; exact w51_3ec
  have w52_420 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = vp45 := by rw [m52]; exact w51_420
  have w52_424 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = vl45 := by rw [m52]; exact w51_424
  have w52_428 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((tp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (te20.header + te20.len)) + BitVec.ofNat 32 (to26.header + to26.len)) + BitVec.ofNat 32 tl30.header := by rw [m52]; exact w51_428
  have w52_42c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl30.len := by rw [m52]; exact w51_42c
  clear w51_42c w51_428 w51_424 w51_420 w51_3ec w51_3e8 w51_3e4 w51_3e0 w51_288 w51_284 w51_280 w51_27c w51_268 w51_264 w51_260 w51_25c w51_78 w51_74 g51_10 g51_27 g51_26 g51_25 g51_24 g51_23 g51_22 g51_21 g51_20 g51_19 g51_18 g51_9 g51_8 g51_4 g51_3 g51_2 V51 E51 fR51 t51 fr51 m51 s51 u51 d51
  exact .inr ⟨tl9, hr9, hrest0, hr20, te20, hte20, op26, ol26, hr26, to26, ht26, tl30, hr30, hr39, te39, hte39, vp45, vl45, hr45, te45, ht45, h32, hrest1, n52, t52, s52, E52, V52, fR52, g52_2, g52_3, g52_4, g52_18, g52_19, g52_20, g52_21, g52_22, g52_23, g52_24, g52_25, g52_26, g52_27, w52_264, w52_268, keep_kk52.mono (by decide)⟩

end C3.RV32.Sv
