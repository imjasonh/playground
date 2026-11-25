import C3BootProofs.Proofs.SvSha2

/-!
# `sigstore::verify`: the timestamp's `SignerInfo`

From 0xD70 to 0xE7C: the signer infos are a `SET` with nothing after it that holds one `SignerInfo` and nothing else, whose version is `INTEGER 1`, whose `sid` is a `SEQUENCE`, whose digest algorithm is SHA-256, and which has `[0]` signed attributes.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svTr6d70 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x320]
theorem svTr6d70_end : blockEnd sigstoreVerifyCode 0xD70 svTr6d70 = some 0xD76 := by
  simp only [svTr6d70]
  rw [blockEnd, sv_at_d70]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_d74]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr6d8a : List BInstr :=
  [.aluImm .add a1 sp 0x425, .aluImm .add a0 sp 0x365, .aluImm .add a2 x0 0xB]
theorem svTr6d8a_end : blockEnd sigstoreVerifyCode 0xD8A svTr6d8a = some 0xD94 := by
  simp only [svTr6d8a]
  rw [blockEnd, sv_at_d8a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_d8e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_d92]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr614c : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x1]
theorem svTr614c_end : blockEnd sigstoreVerifyCode 0x14C svTr614c = some 0x14E := by
  simp only [svTr614c]
  rw [blockEnd, sv_at_14c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr6dac : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x360]
theorem svTr6dac_end : blockEnd sigstoreVerifyCode 0xDAC svTr6dac = some 0xDB2 := by
  simp only [svTr6dac]
  rw [blockEnd, sv_at_dac]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_db0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr6dc6 : List BInstr :=
  [.aluImm .add a1 sp 0x425, .aluImm .add a0 sp 0x375, .aluImm .add a2 x0 0xB]
theorem svTr6dc6_end : blockEnd sigstoreVerifyCode 0xDC6 svTr6dc6 = some 0xDD0 := by
  simp only [svTr6dc6]
  rw [blockEnd, sv_at_dc6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_dca]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_dce]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr6de4 : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x18]
theorem svTr6de4_end : blockEnd sigstoreVerifyCode 0xDE4 svTr6de4 = some 0xDE6 := by
  simp only [svTr6de4]
  rw [blockEnd, sv_at_de4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr6dea : List BInstr :=
  [.aluImm .add a0 sp 0x370, .aluImm .add a1 x0 0x1]
theorem svTr6dea_end : blockEnd sigstoreVerifyCode 0xDEA svTr6dea = some 0xDEE := by
  simp only [svTr6dea]
  rw [blockEnd, sv_at_dea]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_dec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr6df6 : List BInstr :=
  [.aluImm .and a0 a0 0x1]
theorem svTr6df6_end : blockEnd sigstoreVerifyCode 0xDF6 svTr6df6 = some 0xDF8 := by
  simp only [svTr6df6]
  rw [blockEnd, sv_at_df6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr6e34 : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a1]
theorem svTr6e34_end : blockEnd sigstoreVerifyCode 0xE34 svTr6e34 = some 0xE36 := by
  simp only [svTr6e34]
  rw [blockEnd, sv_at_e34]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr6dfa : List BInstr :=
  [.aluImm .and a1 a1 0x1]
theorem svTr6dfa_end : blockEnd sigstoreVerifyCode 0xDFA svTr6dfa = some 0xDFC := by
  simp only [svTr6dfa]
  rw [blockEnd, sv_at_dfa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr6e00 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x370, .aluImm .add a2 x0 0x30]
theorem svTr6e00_end : blockEnd sigstoreVerifyCode 0xE00 svTr6e00 = some 0xE0A := by
  simp only [svTr6e00]
  rw [blockEnd, sv_at_e00]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_e04]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_e06]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr6e26 : List BInstr :=
  [.aluImm .add a0 sp 0x370]
theorem svTr6e26_end : blockEnd sigstoreVerifyCode 0xE26 svTr6e26 = some 0xE28 := by
  simp only [svTr6e26]
  rw [blockEnd, sv_at_e26]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr6e30 : List BInstr :=
  [.aluImm .and a0 a0 0x1]
theorem svTr6e30_end : blockEnd sigstoreVerifyCode 0xE30 svTr6e30 = some 0xE32 := by
  simp only [svTr6e30]
  rw [blockEnd, sv_at_e30]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr6e54 : List BInstr :=
  [.aluImm .and a1 a1 0x1]
theorem svTr6e54_end : blockEnd sigstoreVerifyCode 0xE54 svTr6e54 = some 0xE56 := by
  simp only [svTr6e54]
  rw [blockEnd, sv_at_e54]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svTr6e5a : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x370, .aluImm .add a2 x0 0xA0]
theorem svTr6e5a_end : blockEnd sigstoreVerifyCode 0xE5A svTr6e5a = some 0xE64 := by
  simp only [svTr6e5a]
  rw [blockEnd, sv_at_e5a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_e5e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_e60]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_tr6 {B out bp x20 x21 x22 x23 x24 x25 x26 x27 sdp sdl ecp ecl : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0xD70 (reg n0))
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
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl)
    (w0_328 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp)
    (w0_32c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl)
    (sd_in : SvIn B (sdp) (sdl).toNat)
    (D0 : SvData M0) :
    (¬ (∃ tl2, derElement 0x31 (memBytes M0 (sdp) (sdl).toNat) = .ok tl2 ∧ ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0) ∧ ∃ tl13, derElement 0x30 (memBytes M0 ((sdp) + BitVec.ofNat 32 tl2.header) (BitVec.ofNat 32 tl2.len).toNat) = .ok tl13 ∧ ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) = 0) ∧ derIntIsOf M0 (memBytes M0 (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) (BitVec.ofNat 32 tl13.len).toNat) (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) (derElement 2 (memBytes M0 (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) (BitVec.ofNat 32 tl13.len).toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = .ok true ∧ ∃ te25, derElement 2 (memBytes M0 (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) (BitVec.ofNat 32 tl13.len).toNat) = .ok te25 ∧ ∃ tl31, derElement 0x30 (memBytes M0 ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) ((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)).toNat) = .ok tl31 ∧ isSha256Of M0 (((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) (((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)).toNat = .ok true ∧ ∃ te39, derElement 0x30 (memBytes M0 (((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) (((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)).toNat) = .ok te39 ∧ ∃ tl45, derOptRes 0xA0 (memBytes M0 ((((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len)) ((((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)) - BitVec.ofNat 32 (te39.header + te39.len)).toNat) = some (.ok tl45) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ tl2, derElement 0x31 (memBytes M0 (sdp) (sdl).toNat) = .ok tl2 ∧
    ((sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0) ∧
    ∃ tl13, derElement 0x30 (memBytes M0 ((sdp) + BitVec.ofNat 32 tl2.header) (BitVec.ofNat 32 tl2.len).toNat) = .ok tl13 ∧
    ((BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) = 0) ∧
    derIntIsOf M0 (memBytes M0 (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) (BitVec.ofNat 32 tl13.len).toNat) (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) (derElement 2 (memBytes M0 (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) (BitVec.ofNat 32 tl13.len).toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = .ok true ∧
    ∃ te25, derElement 2 (memBytes M0 (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) (BitVec.ofNat 32 tl13.len).toNat) = .ok te25 ∧
    ∃ tl31, derElement 0x30 (memBytes M0 ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) ((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)).toNat) = .ok tl31 ∧
    isSha256Of M0 (((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) (((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)).toNat = .ok true ∧
    ∃ te39, derElement 0x30 (memBytes M0 (((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) (((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)).toNat) = .ok te39 ∧
    ∃ tl45, derOptRes 0xA0 (memBytes M0 ((((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len)) ((((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)) - BitVec.ofNat 32 (te39.header + te39.len)).toNat) = some (.ok tl45) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0xE7C (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 0x18 ∧
        reg n' a0 = ((((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 tl45.header ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 (tl45.header + tl45.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (tl45.header + tl45.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ((((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 tl45.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl45.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl45.header + tl45.len) ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8), (0x420, 0x18), (0x378, 0x8)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0xD70
  obtain ⟨n1, c1, u1⟩ := s0.block svTr6d70 E0.self svTr6d70_end
    ⟨trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0xD76 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svTr6d70 (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTr6d70, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_11 : reg n1 a1 = B + 0x21A0 + BitVec.ofNat 32 0x320 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svTr6d70, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_74 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m1]; exact w0_74
  have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m1]; exact w0_78
  have w1_328 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = sdp := by rw [m1]; exact w0_328
  have w1_32c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = sdl := by rw [m1]; exact w0_32c
  -- 0xD76: sv_setF
  obtain ⟨n2, c2, s2, sp2, rk2, K2, Ok2, Er2, fr2⟩ := sv_setF (oc := 0x420) (dc := 0x320)
    F E1 s1 sv_at_d76 sv_at_d7a (by decide) (by decide) g1_2 g1_10 g1_11 (by decide) (by decide) (by decide) (by decide)
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
    have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K2.w32 (by decide) (by decide)).trans w1_74
    have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K2.w32 (by decide) (by decide)).trans w1_78
    have w2_420 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z2
    clear w1_32c w1_328 w1_78 w1_74 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
    -- 0xD7E: lw
    obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_d7e (off' := 0xD82) (by decide)
      (by rw [g2_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s3 : St n3.mem SV n3 0xD82 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
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
    have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m3]; exact w2_74
    have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m3]; exact w2_78
    have w3_420 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m3]; exact w2_420
    clear w2_420 w2_78 w2_74 z2
    -- 0xD82: lbu
    obtain ⟨n4, d4, u4⟩ := s3.lbu E3.self sv_at_d82 (off' := 0xD86) (by decide)
    have s4 : St n4.mem SV n4 0xD86 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
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
    have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m4]; exact w3_74
    have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m4]; exact w3_78
    have w4_420 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m4]; exact w3_420
    clear w3_420 w3_78 w3_74 g3_9 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
    -- 0xD86: branch, taken
    obtain ⟨n5, d5, u5⟩ := s4.taken E4.self 0x7A4 sv_at_d86
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
    have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m5]; exact w4_74
    have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m5]; exact w4_78
    have w5_420 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m5]; exact w4_420
    clear w4_420 w4_78 w4_74 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
    exact .inl ⟨(fun ⟨tl2', h0', _⟩ => by rw [hr2] at h0'; cases h0'), sv_fail F E5 s5 t5 (fun x hx => (fR5 x hx).trans (fM x hx).symm) V5 hret g5_2 g5_18 hO g5_3 g5_4⟩
  obtain ⟨o0_2, o4_2, o8_2, o12_2, d8_2, d12_2⟩ := Ok2 tl2 hr2
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x420, 0x10), (0x328, 0x8)] := keep_kk1.trans K2
  clear keep_kk1
  have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K2.w32 (by decide) (by decide)).trans w1_74
  have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K2.w32 (by decide) (by decide)).trans w1_78
  have w2_328 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := d8_2
  have w2_32c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := d12_2
  have w2_420 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := o0_2
  have w2_424 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := o4_2
  have w2_428 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := o8_2
  have w2_42c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := o12_2
  clear w1_32c w1_328 w1_78 w1_74 g1_11 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0xD7E: lw
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_d7e (off' := 0xD82) (by decide)
    (by rw [g2_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s3 : St n3.mem SV n3 0xD82 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
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
  have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m3]; exact w2_74
  have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m3]; exact w2_78
  have w3_328 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m3]; exact w2_328
  have w3_32c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m3]; exact w2_32c
  have w3_420 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m3]; exact w2_420
  have w3_424 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m3]; exact w2_424
  have w3_428 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m3]; exact w2_428
  have w3_42c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m3]; exact w2_42c
  clear w2_42c w2_428 w2_424 w2_420 w2_32c w2_328 w2_78 w2_74 d12_2 d8_2 o12_2 o8_2 o4_2 o0_2 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 Er2 Ok2 K2 rk2 sp2 s2 c2
  -- 0xD82: lbu
  obtain ⟨n4, d4, u4⟩ := s3.lbu E3.self sv_at_d82 (off' := 0xD86) (by decide)
  have b3_424 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by
    have h := byte_of_ld w3_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact h.1
  have s4 : St n4.mem SV n4 0xD86 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
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
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m4]; exact w3_74
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m4]; exact w3_78
  have w4_328 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m4]; exact w3_328
  have w4_32c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m4]; exact w3_32c
  have w4_420 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m4]; exact w3_420
  have w4_424 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m4]; exact w3_424
  have w4_428 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m4]; exact w3_428
  have w4_42c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m4]; exact w3_42c
  have b4_424 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m4]; exact b3_424
  clear w3_42c w3_428 w3_424 w3_420 w3_32c w3_328 w3_78 w3_74 g3_9 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0xD86: branch, not taken
  obtain ⟨n5, d5, u5⟩ := s4.notTaken E4.self 0xD8A sv_at_d86
    (by decide) (by rw [g4_9, s4.zero]; exact br_beq_f (sd_in.ok_ne hr2))
  have s5 : St n5.mem SV n5 0xD8A (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
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
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m5]; exact w4_74
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m5]; exact w4_78
  have w5_328 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m5]; exact w4_328
  have w5_32c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m5]; exact w4_32c
  have w5_420 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m5]; exact w4_420
  have w5_424 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m5]; exact w4_424
  have w5_428 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m5]; exact w4_428
  have w5_42c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m5]; exact w4_42c
  have b5_424 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m5]; exact b4_424
  clear b4_424 w4_42c w4_428 w4_424 w4_420 w4_32c w4_328 w4_78 w4_74 g4_8 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 b3_424 u4 d4
  -- 0xD8A
  obtain ⟨n6, c6, u6⟩ := s5.block svTr6d8a E5.self svTr6d8a_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem SV n6 0xD94 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock svTr6d8a (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
  have g6_10 : reg n6 a0 = B + 0x21A0 + BitVec.ofNat 32 0x365 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svTr6d8a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g6_11 : reg n6 a1 = B + 0x21A0 + BitVec.ofNat 32 0x425 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svTr6d8a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g6_12 : reg n6 a2 = BitVec.ofNat 32 0xB := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svTr6d8a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x10), (0x328, 0x8)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m6]; exact w5_74
  have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m6]; exact w5_78
  have w6_328 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_328
  have w6_32c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m6]; exact w5_32c
  have w6_420 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m6]; exact w5_420
  have w6_424 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m6]; exact w5_424
  have w6_428 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m6]; exact w5_428
  have w6_42c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m6]; exact w5_42c
  have b6_424 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m6]; exact b5_424
  clear b5_424 w5_42c w5_428 w5_424 w5_420 w5_32c w5_328 w5_78 w5_74 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  have b6_425 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by
    have h := byte_of_ld w6_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x425 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 1 by sv_addr]; exact h.2.1
  have b6_426 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by
    have h := byte_of_ld w6_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x426 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 2 by sv_addr]; exact h.2.2.1
  have b6_427 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by
    have h := byte_of_ld w6_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x427 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 3 by sv_addr]; exact h.2.2.2
  -- 0xD94: memcpy
  obtain ⟨n7, P7, K7, X7⟩ := sv_mc (c := 0x365) (d := 0x425) (N := 0xB) F E6 s6 sv_at_d94 sv_at_d98
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
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB)] := keep_kk6.trans K7.toL
  clear keep_kk6
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K7.w32 (by decide) (by decide)).trans w6_74
  have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K7.w32 (by decide) (by decide)).trans w6_78
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
  have w7_368 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = (sdp) + BitVec.ofNat 32 tl2.header := by
    rw [← w6_428]
    exact ld_cp fun q hq => by
      have := X7 (0x3 + q) (by omega)
      rwa [show 0x365 + (0x3 + q) = 0x368 + q by omega,
        show 0x425 + (0x3 + q) = 0x428 + q by omega] at this
  have w7_36c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = BitVec.ofNat 32 tl2.len := by
    rw [← w6_42c]
    exact ld_cp fun q hq => by
      have := X7 (0x7 + q) (by omega)
      rwa [show 0x365 + (0x7 + q) = 0x36C + q by omega,
        show 0x425 + (0x7 + q) = 0x42C + q by omega] at this
  have b7_365 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x365) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [show 0x365 = 0x365 + 0x0 from rfl, X7 0x0 (by decide)]; exact b6_425
  have b7_366 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x366) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [show 0x366 = 0x365 + 0x1 from rfl, X7 0x1 (by decide)]; exact b6_426
  have b7_367 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x367) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [show 0x367 = 0x365 + 0x2 from rfl, X7 0x2 (by decide)]; exact b6_427
  clear b6_424 w6_42c w6_428 w6_424 w6_420 w6_32c w6_328 w6_78 w6_74 g6_12 g6_11 g6_10 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
  -- 0xD9C: lw
  obtain ⟨n8, d8, u8⟩ := s7.lw E7.self sv_at_d9c (off' := 0xDA0) (by decide)
    (by rw [g7_2, show B + 0x21A0 + 0x32C = B + 0x21A0 + BitVec.ofNat 32 0x32C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s8 : St n8.mem SV n8 0xDA0 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
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
  have g8_9 : reg n8 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [u8.regs, upd_ne (by decide) (by decide), g7_9]
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
  have g8_10 : reg n8 a0 = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by
    rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g7_2, show B + 0x21A0 + 0x32C = B + 0x21A0 + BitVec.ofNat 32 0x32C by sv_addr, w7_32c]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m8]; exact w7_74
  have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m8]; exact w7_78
  have w8_328 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m8]; exact w7_328
  have w8_32c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m8]; exact w7_32c
  have w8_368 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m8]; exact w7_368
  have w8_36c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = BitVec.ofNat 32 tl2.len := by rw [m8]; exact w7_36c
  have w8_420 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m8]; exact w7_420
  have w8_424 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m8]; exact w7_424
  have w8_428 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m8]; exact w7_428
  have w8_42c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m8]; exact w7_42c
  have b8_365 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x365) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m8]; exact b7_365
  have b8_366 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x366) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m8]; exact b7_366
  have b8_367 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x367) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m8]; exact b7_367
  have b8_424 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m8]; exact b7_424
  have b8_425 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m8]; exact b7_425
  have b8_426 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m8]; exact b7_426
  have b8_427 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m8]; exact b7_427
  clear b7_367 b7_366 b7_365 w7_36c w7_368 b7_427 b7_426 b7_425 b7_424 w7_42c w7_428 w7_424 w7_420 w7_32c w7_328 w7_78 w7_74 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 s7 X7 K7 P7 b6_427 b6_426 b6_425
  -- 0xDA0: sw
  obtain ⟨n9, d9, s9, fr9, K9, W9, rg9⟩ := sv_sw F E8 s8 sv_at_da0 (off' := 0xDA4) (c := 0x360)
    (by decide) (by rw [g8_2]; sv_addr) (by decide) (by decide)
  have t9 : Steps n0 n9 := t8.trans d9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keep K9 (by decide)
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rg9 sp, g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg9 (3 : Fin 32), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg9 (4 : Fin 32), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg9 (8 : Fin 32), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [rg9 (9 : Fin 32), g8_9]
  have g9_10 : reg n9 a0 = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rg9 a0, g8_10]
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
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4)] := keep_kk8.trans K9.toL
  clear keep_kk8
  have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K9.w32 (by decide) (by decide)).trans w8_74
  have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K9.w32 (by decide) (by decide)).trans w8_78
  have w9_328 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K9.w32 (by decide) (by decide)).trans w8_328
  have w9_32c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K9.w32 (by decide) (by decide)).trans w8_32c
  have w9_368 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = (sdp) + BitVec.ofNat 32 tl2.header := (K9.w32 (by decide) (by decide)).trans w8_368
  have w9_36c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = BitVec.ofNat 32 tl2.len := (K9.w32 (by decide) (by decide)).trans w8_36c
  have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := (K9.w32 (by decide) (by decide)).trans w8_420
  have w9_424 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := (K9.w32 (by decide) (by decide)).trans w8_424
  have w9_428 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := (K9.w32 (by decide) (by decide)).trans w8_428
  have w9_42c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := (K9.w32 (by decide) (by decide)).trans w8_42c
  have b9_365 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x365) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := (K9.b8 (by decide) (by decide)).trans b8_365
  have b9_366 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x366) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := (K9.b8 (by decide) (by decide)).trans b8_366
  have b9_367 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x367) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := (K9.b8 (by decide) (by decide)).trans b8_367
  have b9_424 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := (K9.b8 (by decide) (by decide)).trans b8_424
  have b9_425 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := (K9.b8 (by decide) (by decide)).trans b8_425
  have b9_426 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := (K9.b8 (by decide) (by decide)).trans b8_426
  have b9_427 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := (K9.b8 (by decide) (by decide)).trans b8_427
  have w9_360 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [W9, g8_9]
  clear b8_427 b8_426 b8_425 b8_424 b8_367 b8_366 b8_365 w8_42c w8_428 w8_424 w8_420 w8_36c w8_368 w8_32c w8_328 w8_78 w8_74 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
  -- 0xDA4: sb
  obtain ⟨n10, d10, s10, fr10, K10, W10, rg10⟩ := sv_sb F E9 s9 sv_at_da4 (off' := 0xDA8) (c := 0x364)
    (by decide) (by rw [g9_2]; sv_addr) (by decide)
  have t10 : Steps n0 n10 := t9.trans d10
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.keep K10 (by decide)
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [rg10 sp, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg10 (3 : Fin 32), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg10 (4 : Fin 32), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg10 (8 : Fin 32), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [rg10 (9 : Fin 32), g9_9]
  have g10_10 : reg n10 a0 = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [rg10 a0, g9_10]
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
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1)] := keep_kk9.trans K10.toL
  clear keep_kk9
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K10.w32 (by decide) (by decide)).trans w9_74
  have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K10.w32 (by decide) (by decide)).trans w9_78
  have w10_328 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K10.w32 (by decide) (by decide)).trans w9_328
  have w10_32c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K10.w32 (by decide) (by decide)).trans w9_32c
  have w10_360 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := (K10.w32 (by decide) (by decide)).trans w9_360
  have w10_368 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = (sdp) + BitVec.ofNat 32 tl2.header := (K10.w32 (by decide) (by decide)).trans w9_368
  have w10_36c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = BitVec.ofNat 32 tl2.len := (K10.w32 (by decide) (by decide)).trans w9_36c
  have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := (K10.w32 (by decide) (by decide)).trans w9_420
  have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := (K10.w32 (by decide) (by decide)).trans w9_424
  have w10_428 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := (K10.w32 (by decide) (by decide)).trans w9_428
  have w10_42c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := (K10.w32 (by decide) (by decide)).trans w9_42c
  have b10_365 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x365) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := (K10.b8 (by decide) (by decide)).trans b9_365
  have b10_366 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x366) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := (K10.b8 (by decide) (by decide)).trans b9_366
  have b10_367 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x367) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := (K10.b8 (by decide) (by decide)).trans b9_367
  have b10_424 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := (K10.b8 (by decide) (by decide)).trans b9_424
  have b10_425 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := (K10.b8 (by decide) (by decide)).trans b9_425
  have b10_426 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := (K10.b8 (by decide) (by decide)).trans b9_426
  have b10_427 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := (K10.b8 (by decide) (by decide)).trans b9_427
  have b10_364 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [W10, g9_8, lbu_low]
  clear w9_360 b9_427 b9_426 b9_425 b9_424 b9_367 b9_366 b9_365 w9_42c w9_428 w9_424 w9_420 w9_36c w9_368 w9_32c w9_328 w9_78 w9_74 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 rg9 W9 K9 fr9 s9 d9
  have w10_364 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := ld_of_bytes b10_364
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x364 + 1 = B + 0x21A0 + BitVec.ofNat 32 0x365 by sv_addr]; exact b10_365)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x364 + 2 = B + 0x21A0 + BitVec.ofNat 32 0x366 by sv_addr]; exact b10_366)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x364 + 3 = B + 0x21A0 + BitVec.ofNat 32 0x367 by sv_addr]; exact b10_367)
  by_cases hsdrem : (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0
  rotate_left
  · -- 0xDA8: branch, taken
    obtain ⟨n11, d11, u11⟩ := s10.taken E10.self 0x14C sv_at_da8
      (by decide) (by rw [g10_10, s10.zero]; exact br_bne_t hsdrem)
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
    have g11_9 : reg n11 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [u11.regs, g10_9]
    have g11_10 : reg n11 a0 = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u11.regs, g10_10]
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
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m11]; exact w10_74
    have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m11]; exact w10_78
    have w11_328 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_328
    have w11_32c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_32c
    have w11_360 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m11]; exact w10_360
    have w11_364 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m11]; exact w10_364
    have w11_368 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m11]; exact w10_368
    have w11_36c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = BitVec.ofNat 32 tl2.len := by rw [m11]; exact w10_36c
    have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m11]; exact w10_420
    have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m11]; exact w10_424
    have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m11]; exact w10_428
    have w11_42c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m11]; exact w10_42c
    have b11_424 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m11]; exact b10_424
    have b11_425 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m11]; exact b10_425
    have b11_426 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m11]; exact b10_426
    have b11_427 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m11]; exact b10_427
    clear b10_364 b10_427 b10_426 b10_425 b10_424 b10_367 b10_366 b10_365 w10_42c w10_428 w10_424 w10_420 w10_36c w10_368 w10_360 w10_32c w10_328 w10_78 w10_74 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 rg10 W10 K10 fr10 s10 d10
    -- 0x14C
    obtain ⟨n12, c12, u12⟩ := s11.block svTr614c E11.self svTr614c_end
      ⟨trivial, trivial⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have s12 : St n12.mem SV n12 0x14E (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have rb12 : ∀ q, reg n12 q = (runBlock svTr614c (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
    have g12_10 : reg n12 a0 = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by
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
      rw [rb12]; simp +decide only [runBlock, BInstr.run, svTr614c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m12]; exact w11_74
    have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m12]; exact w11_78
    have w12_328 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m12]; exact w11_328
    have w12_32c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m12]; exact w11_32c
    have w12_360 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_360
    have w12_364 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_364
    have w12_368 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_368
    have w12_36c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_36c
    have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_420
    have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_424
    have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_428
    have w12_42c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_42c
    have b12_424 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m12]; exact b11_424
    have b12_425 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m12]; exact b11_425
    have b12_426 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m12]; exact b11_426
    have b12_427 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m12]; exact b11_427
    clear b11_427 b11_426 b11_425 b11_424 w11_42c w11_428 w11_424 w11_420 w11_36c w11_368 w11_364 w11_360 w11_32c w11_328 w11_78 w11_74 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
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
    have g13_9 : reg n13 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [u13.regs, g12_9]
    have g13_10 : reg n13 a0 = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u13.regs, g12_10]
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
    have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1)] := by rw [m13]; exact keep_kk12
    clear keep_kk12
    have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m13]; exact w12_74
    have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m13]; exact w12_78
    have w13_328 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m13]; exact w12_328
    have w13_32c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m13]; exact w12_32c
    have w13_360 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m13]; exact w12_360
    have w13_364 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m13]; exact w12_364
    have w13_368 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m13]; exact w12_368
    have w13_36c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = BitVec.ofNat 32 tl2.len := by rw [m13]; exact w12_36c
    have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m13]; exact w12_420
    have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m13]; exact w12_424
    have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m13]; exact w12_428
    have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m13]; exact w12_42c
    have b13_424 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m13]; exact b12_424
    have b13_425 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m13]; exact b12_425
    have b13_426 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m13]; exact b12_426
    have b13_427 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m13]; exact b12_427
    clear b12_427 b12_426 b12_425 b12_424 w12_42c w12_428 w12_424 w12_420 w12_36c w12_368 w12_364 w12_360 w12_32c w12_328 w12_78 w12_74 g12_8 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_10 g12_9 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
    exact .inl ⟨(fun ⟨tl2', h0', h1', _⟩ => by rw [hr2] at h0'; cases h0'; exact hsdrem h1'), sv_fail F E13 s13 t13 (fun x hx => (fR13 x hx).trans (fM x hx).symm) V13 hret g13_2 g13_18 hO g13_3 g13_4⟩
  -- 0xDA8: branch, not taken
  obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.self 0xDAC sv_at_da8
    (by decide) (by rw [g10_10, s10.zero]; exact br_bne_f hsdrem)
  have s11 : St n11.mem SV n11 0xDAC (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
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
  have g11_9 : reg n11 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [u11.regs, g10_9]
  have g11_10 : reg n11 a0 = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [u11.regs, g10_10]
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
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m11]; exact w10_74
  have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m11]; exact w10_78
  have w11_328 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_328
  have w11_32c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m11]; exact w10_32c
  have w11_360 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m11]; exact w10_360
  have w11_364 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m11]; exact w10_364
  have w11_368 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m11]; exact w10_368
  have w11_36c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = BitVec.ofNat 32 tl2.len := by rw [m11]; exact w10_36c
  have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m11]; exact w10_420
  have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m11]; exact w10_424
  have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m11]; exact w10_428
  have w11_42c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m11]; exact w10_42c
  have b11_424 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m11]; exact b10_424
  have b11_425 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m11]; exact b10_425
  have b11_426 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m11]; exact b10_426
  have b11_427 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m11]; exact b10_427
  clear b10_364 b10_427 b10_426 b10_425 b10_424 b10_367 b10_366 b10_365 w10_42c w10_428 w10_424 w10_420 w10_36c w10_368 w10_360 w10_32c w10_328 w10_78 w10_74 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 rg10 W10 K10 fr10 s10 d10
  -- 0xDAC
  obtain ⟨n12, c12, u12⟩ := s11.block svTr6dac E11.self svTr6dac_end
    ⟨trivial, trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem SV n12 0xDB2 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock svTr6dac (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
  have g12_10 : reg n12 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svTr6dac, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g12_11 : reg n12 a1 = B + 0x21A0 + BitVec.ofNat 32 0x360 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svTr6dac, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_18, g11_19, g11_20, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m12]; exact w11_74
  have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m12]; exact w11_78
  have w12_328 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m12]; exact w11_328
  have w12_32c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m12]; exact w11_32c
  have w12_360 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_360
  have w12_364 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_364
  have w12_368 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_368
  have w12_36c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_36c
  have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_420
  have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_424
  have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m12]; exact w11_428
  have w12_42c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl2.len := by rw [m12]; exact w11_42c
  have b12_424 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl2.len).extractLsb' 0 8 := by rw [m12]; exact b11_424
  have b12_425 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl2.len).extractLsb' 8 8 := by rw [m12]; exact b11_425
  have b12_426 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl2.len).extractLsb' 16 8 := by rw [m12]; exact b11_426
  have b12_427 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl2.len).extractLsb' 24 8 := by rw [m12]; exact b11_427
  clear b11_427 b11_426 b11_425 b11_424 w11_42c w11_428 w11_424 w11_420 w11_36c w11_368 w11_364 w11_360 w11_32c w11_328 w11_78 w11_74 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11 w10_364
  -- 0xDB2: sv_seqF
  obtain ⟨n13, c13, s13, sp13, rk13, K13, Ok13, Er13, fr13⟩ := sv_seqF (oc := 0x420) (dc := 0x360)
    F E12 s12 sv_at_db2 sv_at_db6 (by decide) (by decide) g12_2 g12_10 g12_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w12_368 w12_36c (sd_in.contentW hr2)
  have t13 : Steps n0 n13 := t12.trans c13
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.keepL K13 (by decide)
  rw [sv_mb fR12 (sd_in.contentW hr2)] at Ok13 Er13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [rk13 sp (by decide) (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk13 (3 : Fin 32) (by decide) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk13 (4 : Fin 32) (by decide) (by decide), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = ((BitVec.ofNat 32 tl2.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk13 (8 : Fin 32) (by decide) (by decide), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [rk13 (9 : Fin 32) (by decide) (by decide), g12_9]
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
  obtain ⟨r13, hr13⟩ : ∃ r, derElement 0x30 (memBytes M0 ((sdp) + BitVec.ofNat 32 tl2.header) (BitVec.ofNat 32 tl2.len).toNat) = r := ⟨_, rfl⟩
  rcases r13 with er13 | tl13
  · obtain ⟨z13, -⟩ := Er13 er13 hr13
    have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8)] := keep_kk12.trans K13
    clear keep_kk12
    have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K13.w32 (by decide) (by decide)).trans w12_74
    have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K13.w32 (by decide) (by decide)).trans w12_78
    have w13_328 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K13.w32 (by decide) (by decide)).trans w12_328
    have w13_32c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K13.w32 (by decide) (by decide)).trans w12_32c
    have w13_360 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := (K13.w32 (by decide) (by decide)).trans w12_360
    have w13_364 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := (K13.w32 (by decide) (by decide)).trans w12_364
    have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := z13
    clear b12_427 b12_426 b12_425 b12_424 w12_42c w12_428 w12_424 w12_420 w12_36c w12_368 w12_364 w12_360 w12_32c w12_328 w12_78 w12_74 g12_11 g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
    -- 0xDBA: lw
    obtain ⟨n14, d14, u14⟩ := s13.lw E13.self sv_at_dba (off' := 0xDBE) (by decide)
      (by rw [g13_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s14 : St n14.mem SV n14 0xDBE (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
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
    have g14_9 : reg n14 (9 : Fin 32) = 0 := by
      rw [u14.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g13_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w13_420]
    have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8)] := by rw [m14]; exact keep_kk13
    clear keep_kk13
    have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m14]; exact w13_74
    have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m14]; exact w13_78
    have w14_328 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m14]; exact w13_328
    have w14_32c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m14]; exact w13_32c
    have w14_360 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m14]; exact w13_360
    have w14_364 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m14]; exact w13_364
    have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m14]; exact w13_420
    clear w13_420 w13_364 w13_360 w13_32c w13_328 w13_78 w13_74 z13
    -- 0xDBE: lbu
    obtain ⟨n15, d15, u15⟩ := s14.lbu E14.self sv_at_dbe (off' := 0xDC2) (by decide)
    have s15 : St n15.mem SV n15 0xDC2 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
    have m15 : n15.mem = n14.mem := u15.mem
    have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
    have t15 : Steps n0 n15 := t14.trans (.single d15)
    have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
    have E15 : SvCode n15.mem := E14.fr F fr15
    have V15 : SvSaves B n15.mem v := V14.same m15
    have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_2]
    have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_3]
    have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_4]
    have g15_9 : reg n15 (9 : Fin 32) = 0 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_9]
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
    have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8)] := by rw [m15]; exact keep_kk14
    clear keep_kk14
    have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m15]; exact w14_74
    have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m15]; exact w14_78
    have w15_328 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m15]; exact w14_328
    have w15_32c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m15]; exact w14_32c
    have w15_360 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m15]; exact w14_360
    have w15_364 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m15]; exact w14_364
    have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m15]; exact w14_420
    clear w14_420 w14_364 w14_360 w14_32c w14_328 w14_78 w14_74 g14_9 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
    -- 0xDC2: branch, taken
    obtain ⟨n16, d16, u16⟩ := s15.taken E15.self 0x7A4 sv_at_dc2
      (by decide) (by rw [g15_9, s15.zero]; rfl)
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
    have g16_9 : reg n16 (9 : Fin 32) = 0 := by rw [u16.regs, g15_9]
    have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, g15_18]
    have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, g15_19]
    have g16_20 : reg n16 (20 : Fin 32) = x20 := by rw [u16.regs, g15_20]
    have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [u16.regs, g15_21]
    have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [u16.regs, g15_22]
    have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [u16.regs, g15_23]
    have g16_24 : reg n16 (24 : Fin 32) = x24 := by rw [u16.regs, g15_24]
    have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [u16.regs, g15_25]
    have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [u16.regs, g15_26]
    have g16_27 : reg n16 (27 : Fin 32) = x27 := by rw [u16.regs, g15_27]
    have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8)] := by rw [m16]; exact keep_kk15
    clear keep_kk15
    have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m16]; exact w15_74
    have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m16]; exact w15_78
    have w16_328 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m16]; exact w15_328
    have w16_32c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m16]; exact w15_32c
    have w16_360 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m16]; exact w15_360
    have w16_364 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m16]; exact w15_364
    have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m16]; exact w15_420
    clear w15_420 w15_364 w15_360 w15_32c w15_328 w15_78 w15_74 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
    exact .inl ⟨(fun ⟨tl2', h0', h1', tl13', h2', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr13] at h2'; cases h2'), sv_fail F E16 s16 t16 (fun x hx => (fR16 x hx).trans (fM x hx).symm) V16 hret g16_2 g16_18 hO g16_3 g16_4⟩
  obtain ⟨o0_13, o4_13, o8_13, o12_13, d8_13, d12_13⟩ := Ok13 tl13 hr13
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8)] := keep_kk12.trans K13
  clear keep_kk12
  have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K13.w32 (by decide) (by decide)).trans w12_74
  have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K13.w32 (by decide) (by decide)).trans w12_78
  have w13_328 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K13.w32 (by decide) (by decide)).trans w12_328
  have w13_32c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K13.w32 (by decide) (by decide)).trans w12_32c
  have w13_360 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := (K13.w32 (by decide) (by decide)).trans w12_360
  have w13_364 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := (K13.w32 (by decide) (by decide)).trans w12_364
  have w13_368 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := d8_13
  have w13_36c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := d12_13
  have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := o0_13
  have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := o4_13
  have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := o8_13
  have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := o12_13
  clear b12_427 b12_426 b12_425 b12_424 w12_42c w12_428 w12_424 w12_420 w12_36c w12_368 w12_364 w12_360 w12_32c w12_328 w12_78 w12_74 g12_11 g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
  -- 0xDBA: lw
  obtain ⟨n14, d14, u14⟩ := s13.lw E13.self sv_at_dba (off' := 0xDBE) (by decide)
    (by rw [g13_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s14 : St n14.mem SV n14 0xDBE (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
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
  have g14_9 : reg n14 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
    rw [u14.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g13_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w13_420]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m14]; exact w13_74
  have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m14]; exact w13_78
  have w14_328 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m14]; exact w13_328
  have w14_32c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m14]; exact w13_32c
  have w14_360 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m14]; exact w13_360
  have w14_364 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m14]; exact w13_364
  have w14_368 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m14]; exact w13_368
  have w14_36c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m14]; exact w13_36c
  have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m14]; exact w13_420
  have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m14]; exact w13_424
  have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m14]; exact w13_428
  have w14_42c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m14]; exact w13_42c
  clear w13_42c w13_428 w13_424 w13_420 w13_36c w13_368 w13_364 w13_360 w13_32c w13_328 w13_78 w13_74 d12_13 d8_13 o12_13 o8_13 o4_13 o0_13 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 Er13 Ok13 K13 rk13 sp13 s13 c13
  -- 0xDBE: lbu
  obtain ⟨n15, d15, u15⟩ := s14.lbu E14.self sv_at_dbe (off' := 0xDC2) (by decide)
  have b14_424 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by
    have h := byte_of_ld w14_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact h.1
  have s15 : St n15.mem SV n15 0xDC2 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_4]
  have g15_9 : reg n15 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u15.regs, upd_ne (by decide) (by decide), g14_9]
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
  have g15_8 : reg n15 (8 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [u15.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g14_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, b14_424]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m15]; exact w14_74
  have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m15]; exact w14_78
  have w15_328 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m15]; exact w14_328
  have w15_32c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m15]; exact w14_32c
  have w15_360 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m15]; exact w14_360
  have w15_364 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m15]; exact w14_364
  have w15_368 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m15]; exact w14_368
  have w15_36c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m15]; exact w14_36c
  have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m15]; exact w14_420
  have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m15]; exact w14_424
  have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m15]; exact w14_428
  have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m15]; exact w14_42c
  have b15_424 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m15]; exact b14_424
  clear w14_42c w14_428 w14_424 w14_420 w14_36c w14_368 w14_364 w14_360 w14_32c w14_328 w14_78 w14_74 g14_9 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
  -- 0xDC2: branch, not taken
  obtain ⟨n16, d16, u16⟩ := s15.notTaken E15.self 0xDC6 sv_at_dc2
    (by decide) (by rw [g15_9, s15.zero]; exact br_beq_f ((sd_in.contentW hr2).ok_ne hr13))
  have s16 : St n16.mem SV n16 0xDC6 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans (.single d16)
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [u16.regs, g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u16.regs, g15_9]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = x20 := by rw [u16.regs, g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [u16.regs, g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [u16.regs, g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [u16.regs, g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = x24 := by rw [u16.regs, g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [u16.regs, g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [u16.regs, g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = x27 := by rw [u16.regs, g15_27]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m16]; exact w15_74
  have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m16]; exact w15_78
  have w16_328 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m16]; exact w15_328
  have w16_32c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m16]; exact w15_32c
  have w16_360 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m16]; exact w15_360
  have w16_364 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m16]; exact w15_364
  have w16_368 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m16]; exact w15_368
  have w16_36c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m16]; exact w15_36c
  have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m16]; exact w15_420
  have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m16]; exact w15_424
  have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m16]; exact w15_428
  have w16_42c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m16]; exact w15_42c
  have b16_424 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m16]; exact b15_424
  clear b15_424 w15_42c w15_428 w15_424 w15_420 w15_36c w15_368 w15_364 w15_360 w15_32c w15_328 w15_78 w15_74 g15_8 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 b14_424 u15 d15
  -- 0xDC6
  obtain ⟨n17, c17, u17⟩ := s16.block svTr6dc6 E16.self svTr6dc6_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem SV n17 0xDD0 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock svTr6dc6 (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
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
  have g17_8 : reg n17 (8 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb17, runBlock_reg _ _ _ (8 : Fin 32) s16.zero (by decide), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
    rw [rb17, runBlock_reg _ _ _ (9 : Fin 32) s16.zero (by decide), g16_9]
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
  have g17_10 : reg n17 a0 = B + 0x21A0 + BitVec.ofNat 32 0x375 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svTr6dc6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g17_11 : reg n17 a1 = B + 0x21A0 + BitVec.ofNat 32 0x425 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svTr6dc6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g17_12 : reg n17 a2 = BitVec.ofNat 32 0xB := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svTr6dc6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m17]; exact w16_74
  have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m17]; exact w16_78
  have w17_328 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m17]; exact w16_328
  have w17_32c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m17]; exact w16_32c
  have w17_360 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m17]; exact w16_360
  have w17_364 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m17]; exact w16_364
  have w17_368 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m17]; exact w16_368
  have w17_36c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m17]; exact w16_36c
  have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m17]; exact w16_420
  have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m17]; exact w16_424
  have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m17]; exact w16_428
  have w17_42c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m17]; exact w16_42c
  have b17_424 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m17]; exact b16_424
  clear b16_424 w16_42c w16_428 w16_424 w16_420 w16_36c w16_368 w16_364 w16_360 w16_32c w16_328 w16_78 w16_74 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
  have b17_425 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by
    have h := byte_of_ld w17_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x425 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 1 by sv_addr]; exact h.2.1
  have b17_426 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by
    have h := byte_of_ld w17_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x426 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 2 by sv_addr]; exact h.2.2.1
  have b17_427 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by
    have h := byte_of_ld w17_424
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x427 = B + 0x21A0 + BitVec.ofNat 32 0x424 + 3 by sv_addr]; exact h.2.2.2
  -- 0xDD0: memcpy
  obtain ⟨n18, P18, K18, X18⟩ := sv_mc (c := 0x375) (d := 0x425) (N := 0xB) F E17 s17 sv_at_dd0 sv_at_dd4
    (by decide) (by decide) g17_2 g17_10 g17_11 g17_12
    (by decide) (by decide) (by decide)
  have s18 := P18.st
  have fr18 := P18.fr
  have t18 : Steps n0 n18 := t17.trans P18.steps
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.keep K18 (by decide)
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [P18.regs sp (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P18.regs (3 : Fin 32) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P18.regs (4 : Fin 32) (by decide), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [P18.regs (8 : Fin 32) (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [P18.regs (9 : Fin 32) (by decide), g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [P18.regs (18 : Fin 32) (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [P18.regs (19 : Fin 32) (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [P18.regs (20 : Fin 32) (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [P18.regs (21 : Fin 32) (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [P18.regs (22 : Fin 32) (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [P18.regs (23 : Fin 32) (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = x24 := by rw [P18.regs (24 : Fin 32) (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [P18.regs (25 : Fin 32) (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [P18.regs (26 : Fin 32) (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = x27 := by rw [P18.regs (27 : Fin 32) (by decide), g17_27]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB)] := keep_kk17.trans K18.toL
  clear keep_kk17
  have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K18.w32 (by decide) (by decide)).trans w17_74
  have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K18.w32 (by decide) (by decide)).trans w17_78
  have w18_328 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K18.w32 (by decide) (by decide)).trans w17_328
  have w18_32c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K18.w32 (by decide) (by decide)).trans w17_32c
  have w18_360 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := (K18.w32 (by decide) (by decide)).trans w17_360
  have w18_364 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := (K18.w32 (by decide) (by decide)).trans w17_364
  have w18_368 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K18.w32 (by decide) (by decide)).trans w17_368
  have w18_36c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K18.w32 (by decide) (by decide)).trans w17_36c
  have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K18.w32 (by decide) (by decide)).trans w17_420
  have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := (K18.w32 (by decide) (by decide)).trans w17_424
  have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K18.w32 (by decide) (by decide)).trans w17_428
  have w18_42c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := (K18.w32 (by decide) (by decide)).trans w17_42c
  have b18_424 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := (K18.b8 (by decide) (by decide)).trans b17_424
  have b18_425 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K18.b8 (by decide) (by decide)).trans b17_425
  have b18_426 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K18.b8 (by decide) (by decide)).trans b17_426
  have b18_427 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K18.b8 (by decide) (by decide)).trans b17_427
  have w18_378 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
    rw [← w17_428]
    exact ld_cp fun q hq => by
      have := X18 (0x3 + q) (by omega)
      rwa [show 0x375 + (0x3 + q) = 0x378 + q by omega,
        show 0x425 + (0x3 + q) = 0x428 + q by omega] at this
  have w18_37c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = BitVec.ofNat 32 tl13.len := by
    rw [← w17_42c]
    exact ld_cp fun q hq => by
      have := X18 (0x7 + q) (by omega)
      rwa [show 0x375 + (0x7 + q) = 0x37C + q by omega,
        show 0x425 + (0x7 + q) = 0x42C + q by omega] at this
  have b18_375 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x375) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [show 0x375 = 0x375 + 0x0 from rfl, X18 0x0 (by decide)]; exact b17_425
  have b18_376 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x376) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [show 0x376 = 0x375 + 0x1 from rfl, X18 0x1 (by decide)]; exact b17_426
  have b18_377 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x377) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [show 0x377 = 0x375 + 0x2 from rfl, X18 0x2 (by decide)]; exact b17_427
  clear b17_424 w17_42c w17_428 w17_424 w17_420 w17_36c w17_368 w17_364 w17_360 w17_32c w17_328 w17_78 w17_74 g17_12 g17_11 g17_10 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
  -- 0xDD8: lw
  obtain ⟨n19, d19, u19⟩ := s18.lw E18.self sv_at_dd8 (off' := 0xDDC) (by decide)
    (by rw [g18_2, show B + 0x21A0 + 0x36C = B + 0x21A0 + BitVec.ofNat 32 0x36C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s19 : St n19.mem SV n19 0xDDC (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans (.single d19)
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u19.regs, upd_ne (by decide) (by decide), g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = x20 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = x24 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = x27 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
  have g19_10 : reg n19 a0 = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by
    rw [u19.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g18_2, show B + 0x21A0 + 0x36C = B + 0x21A0 + BitVec.ofNat 32 0x36C by sv_addr, w18_36c]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m19]; exact w18_74
  have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m19]; exact w18_78
  have w19_328 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m19]; exact w18_328
  have w19_32c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m19]; exact w18_32c
  have w19_360 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m19]; exact w18_360
  have w19_364 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m19]; exact w18_364
  have w19_368 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m19]; exact w18_368
  have w19_36c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m19]; exact w18_36c
  have w19_378 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m19]; exact w18_378
  have w19_37c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = BitVec.ofNat 32 tl13.len := by rw [m19]; exact w18_37c
  have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m19]; exact w18_420
  have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m19]; exact w18_424
  have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m19]; exact w18_428
  have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m19]; exact w18_42c
  have b19_375 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x375) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m19]; exact b18_375
  have b19_376 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x376) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m19]; exact b18_376
  have b19_377 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x377) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m19]; exact b18_377
  have b19_424 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m19]; exact b18_424
  have b19_425 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m19]; exact b18_425
  have b19_426 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m19]; exact b18_426
  have b19_427 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m19]; exact b18_427
  clear b18_377 b18_376 b18_375 w18_37c w18_378 b18_427 b18_426 b18_425 b18_424 w18_42c w18_428 w18_424 w18_420 w18_36c w18_368 w18_364 w18_360 w18_32c w18_328 w18_78 w18_74 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 s18 X18 K18 P18 b17_427 b17_426 b17_425
  -- 0xDDC: sw
  obtain ⟨n20, d20, s20, fr20, K20, W20, rg20⟩ := sv_sw F E19 s19 sv_at_ddc (off' := 0xDE0) (c := 0x370)
    (by decide) (by rw [g19_2]; sv_addr) (by decide) (by decide)
  have t20 : Steps n0 n20 := t19.trans d20
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.keep K20 (by decide)
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [rg20 sp, g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg20 (3 : Fin 32), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg20 (4 : Fin 32), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg20 (8 : Fin 32), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [rg20 (9 : Fin 32), g19_9]
  have g20_10 : reg n20 a0 = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [rg20 a0, g19_10]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [rg20 (18 : Fin 32), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [rg20 (19 : Fin 32), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = x20 := by rw [rg20 (20 : Fin 32), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = x21 := by rw [rg20 (21 : Fin 32), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = x22 := by rw [rg20 (22 : Fin 32), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = x23 := by rw [rg20 (23 : Fin 32), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = x24 := by rw [rg20 (24 : Fin 32), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = x25 := by rw [rg20 (25 : Fin 32), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [rg20 (26 : Fin 32), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = x27 := by rw [rg20 (27 : Fin 32), g19_27]
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4)] := keep_kk19.trans K20.toL
  clear keep_kk19
  have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K20.w32 (by decide) (by decide)).trans w19_74
  have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K20.w32 (by decide) (by decide)).trans w19_78
  have w20_328 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K20.w32 (by decide) (by decide)).trans w19_328
  have w20_32c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K20.w32 (by decide) (by decide)).trans w19_32c
  have w20_360 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := (K20.w32 (by decide) (by decide)).trans w19_360
  have w20_364 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := (K20.w32 (by decide) (by decide)).trans w19_364
  have w20_368 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K20.w32 (by decide) (by decide)).trans w19_368
  have w20_36c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K20.w32 (by decide) (by decide)).trans w19_36c
  have w20_378 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K20.w32 (by decide) (by decide)).trans w19_378
  have w20_37c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = BitVec.ofNat 32 tl13.len := (K20.w32 (by decide) (by decide)).trans w19_37c
  have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K20.w32 (by decide) (by decide)).trans w19_420
  have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := (K20.w32 (by decide) (by decide)).trans w19_424
  have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K20.w32 (by decide) (by decide)).trans w19_428
  have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := (K20.w32 (by decide) (by decide)).trans w19_42c
  have b20_375 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x375) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K20.b8 (by decide) (by decide)).trans b19_375
  have b20_376 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x376) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K20.b8 (by decide) (by decide)).trans b19_376
  have b20_377 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x377) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K20.b8 (by decide) (by decide)).trans b19_377
  have b20_424 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := (K20.b8 (by decide) (by decide)).trans b19_424
  have b20_425 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K20.b8 (by decide) (by decide)).trans b19_425
  have b20_426 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K20.b8 (by decide) (by decide)).trans b19_426
  have b20_427 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K20.b8 (by decide) (by decide)).trans b19_427
  have w20_370 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [W20, g19_9]
  clear b19_427 b19_426 b19_425 b19_424 b19_377 b19_376 b19_375 w19_42c w19_428 w19_424 w19_420 w19_37c w19_378 w19_36c w19_368 w19_364 w19_360 w19_32c w19_328 w19_78 w19_74 g19_10 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
  -- 0xDE0: sb
  obtain ⟨n21, d21, s21, fr21, K21, W21, rg21⟩ := sv_sb F E20 s20 sv_at_de0 (off' := 0xDE4) (c := 0x374)
    (by decide) (by rw [g20_2]; sv_addr) (by decide)
  have t21 : Steps n0 n21 := t20.trans d21
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.keep K21 (by decide)
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [rg21 sp, g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg21 (3 : Fin 32), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg21 (4 : Fin 32), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg21 (8 : Fin 32), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [rg21 (9 : Fin 32), g20_9]
  have g21_10 : reg n21 a0 = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [rg21 a0, g20_10]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [rg21 (18 : Fin 32), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [rg21 (19 : Fin 32), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = x20 := by rw [rg21 (20 : Fin 32), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [rg21 (21 : Fin 32), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [rg21 (22 : Fin 32), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = x23 := by rw [rg21 (23 : Fin 32), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = x24 := by rw [rg21 (24 : Fin 32), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [rg21 (25 : Fin 32), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [rg21 (26 : Fin 32), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = x27 := by rw [rg21 (27 : Fin 32), g20_27]
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1)] := keep_kk20.trans K21.toL
  clear keep_kk20
  have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K21.w32 (by decide) (by decide)).trans w20_74
  have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K21.w32 (by decide) (by decide)).trans w20_78
  have w21_328 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K21.w32 (by decide) (by decide)).trans w20_328
  have w21_32c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K21.w32 (by decide) (by decide)).trans w20_32c
  have w21_360 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := (K21.w32 (by decide) (by decide)).trans w20_360
  have w21_364 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := (K21.w32 (by decide) (by decide)).trans w20_364
  have w21_368 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K21.w32 (by decide) (by decide)).trans w20_368
  have w21_36c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K21.w32 (by decide) (by decide)).trans w20_36c
  have w21_370 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K21.w32 (by decide) (by decide)).trans w20_370
  have w21_378 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K21.w32 (by decide) (by decide)).trans w20_378
  have w21_37c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = BitVec.ofNat 32 tl13.len := (K21.w32 (by decide) (by decide)).trans w20_37c
  have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K21.w32 (by decide) (by decide)).trans w20_420
  have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := (K21.w32 (by decide) (by decide)).trans w20_424
  have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K21.w32 (by decide) (by decide)).trans w20_428
  have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := (K21.w32 (by decide) (by decide)).trans w20_42c
  have b21_375 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x375) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K21.b8 (by decide) (by decide)).trans b20_375
  have b21_376 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x376) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K21.b8 (by decide) (by decide)).trans b20_376
  have b21_377 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x377) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K21.b8 (by decide) (by decide)).trans b20_377
  have b21_424 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := (K21.b8 (by decide) (by decide)).trans b20_424
  have b21_425 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K21.b8 (by decide) (by decide)).trans b20_425
  have b21_426 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K21.b8 (by decide) (by decide)).trans b20_426
  have b21_427 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K21.b8 (by decide) (by decide)).trans b20_427
  have b21_374 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [W21, g20_8, lbu_low]
  clear w20_370 b20_427 b20_426 b20_425 b20_424 b20_377 b20_376 b20_375 w20_42c w20_428 w20_424 w20_420 w20_37c w20_378 w20_36c w20_368 w20_364 w20_360 w20_32c w20_328 w20_78 w20_74 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_10 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 rg20 W20 K20 fr20 s20 d20
  have w21_374 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := ld_of_bytes b21_374
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x374 + 1 = B + 0x21A0 + BitVec.ofNat 32 0x375 by sv_addr]; exact b21_375)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x374 + 2 = B + 0x21A0 + BitVec.ofNat 32 0x376 by sv_addr]; exact b21_376)
    (by rw [show B + 0x21A0 + BitVec.ofNat 32 0x374 + 3 = B + 0x21A0 + BitVec.ofNat 32 0x377 by sv_addr]; exact b21_377)
  -- 0xDE4
  obtain ⟨n22, c22, u22⟩ := s21.block svTr6de4 E21.self svTr6de4_end
    ⟨trivial, trivial⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have s22 : St n22.mem SV n22 0xDE6 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have rb22 : ∀ q, reg n22 q = (runBlock svTr6de4 (n21.mem, reg n21)).2 q := fun q => by rw [u22.regs]
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans c22
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by
    rw [rb22, runBlock_reg _ _ _ sp s21.zero (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb22, runBlock_reg _ _ _ (3 : Fin 32) s21.zero (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb22, runBlock_reg _ _ _ (4 : Fin 32) s21.zero (by decide), g21_4]
  have g22_9 : reg n22 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
    rw [rb22, runBlock_reg _ _ _ (9 : Fin 32) s21.zero (by decide), g21_9]
  have g22_10 : reg n22 a0 = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by
    rw [rb22, runBlock_reg _ _ _ a0 s21.zero (by decide), g21_10]
  have g22_18 : reg n22 (18 : Fin 32) = out := by
    rw [rb22, runBlock_reg _ _ _ (18 : Fin 32) s21.zero (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by
    rw [rb22, runBlock_reg _ _ _ (19 : Fin 32) s21.zero (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = x20 := by
    rw [rb22, runBlock_reg _ _ _ (20 : Fin 32) s21.zero (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = x21 := by
    rw [rb22, runBlock_reg _ _ _ (21 : Fin 32) s21.zero (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = x22 := by
    rw [rb22, runBlock_reg _ _ _ (22 : Fin 32) s21.zero (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = x23 := by
    rw [rb22, runBlock_reg _ _ _ (23 : Fin 32) s21.zero (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = x24 := by
    rw [rb22, runBlock_reg _ _ _ (24 : Fin 32) s21.zero (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = x25 := by
    rw [rb22, runBlock_reg _ _ _ (25 : Fin 32) s21.zero (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by
    rw [rb22, runBlock_reg _ _ _ (26 : Fin 32) s21.zero (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = x27 := by
    rw [rb22, runBlock_reg _ _ _ (27 : Fin 32) s21.zero (by decide), g21_27]
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, svTr6de4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_10, g21_18, g21_19, g21_20, g21_21, g21_22, g21_23, g21_24, g21_25, g21_26, g21_27, s21.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m22]; exact w21_74
  have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m22]; exact w21_78
  have w22_328 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m22]; exact w21_328
  have w22_32c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m22]; exact w21_32c
  have w22_360 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m22]; exact w21_360
  have w22_364 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m22]; exact w21_364
  have w22_368 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m22]; exact w21_368
  have w22_36c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m22]; exact w21_36c
  have w22_370 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m22]; exact w21_370
  have w22_374 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m22]; exact w21_374
  have w22_378 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m22]; exact w21_378
  have w22_37c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = BitVec.ofNat 32 tl13.len := by rw [m22]; exact w21_37c
  have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m22]; exact w21_420
  have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m22]; exact w21_424
  have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m22]; exact w21_428
  have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m22]; exact w21_42c
  have b22_424 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m22]; exact b21_424
  have b22_425 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m22]; exact b21_425
  have b22_426 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m22]; exact b21_426
  have b22_427 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m22]; exact b21_427
  clear b21_374 b21_427 b21_426 b21_425 b21_424 b21_377 b21_376 b21_375 w21_42c w21_428 w21_424 w21_420 w21_37c w21_378 w21_370 w21_36c w21_368 w21_364 w21_360 w21_32c w21_328 w21_78 w21_74 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_10 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 rg21 W21 K21 fr21 s21 d21
  by_cases hsirem : (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) = 0
  rotate_left
  · -- 0xDE6: branch, taken
    obtain ⟨n23, d23, u23⟩ := s22.taken E22.self 0x7A4 sv_at_de6
      (by decide) (by rw [g22_10, s22.zero]; exact br_bne_t hsirem)
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
    have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u23.regs, g22_8]
    have g23_9 : reg n23 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u23.regs, g22_9]
    have g23_10 : reg n23 a0 = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [u23.regs, g22_10]
    have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, g22_18]
    have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, g22_19]
    have g23_20 : reg n23 (20 : Fin 32) = x20 := by rw [u23.regs, g22_20]
    have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [u23.regs, g22_21]
    have g23_22 : reg n23 (22 : Fin 32) = x22 := by rw [u23.regs, g22_22]
    have g23_23 : reg n23 (23 : Fin 32) = x23 := by rw [u23.regs, g22_23]
    have g23_24 : reg n23 (24 : Fin 32) = x24 := by rw [u23.regs, g22_24]
    have g23_25 : reg n23 (25 : Fin 32) = x25 := by rw [u23.regs, g22_25]
    have g23_26 : reg n23 (26 : Fin 32) = x26 := by rw [u23.regs, g22_26]
    have g23_27 : reg n23 (27 : Fin 32) = x27 := by rw [u23.regs, g22_27]
    have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1)] := by rw [m23]; exact keep_kk22
    clear keep_kk22
    have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m23]; exact w22_74
    have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m23]; exact w22_78
    have w23_328 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m23]; exact w22_328
    have w23_32c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m23]; exact w22_32c
    have w23_360 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m23]; exact w22_360
    have w23_364 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m23]; exact w22_364
    have w23_368 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m23]; exact w22_368
    have w23_36c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m23]; exact w22_36c
    have w23_370 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m23]; exact w22_370
    have w23_374 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m23]; exact w22_374
    have w23_378 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m23]; exact w22_378
    have w23_37c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = BitVec.ofNat 32 tl13.len := by rw [m23]; exact w22_37c
    have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m23]; exact w22_420
    have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m23]; exact w22_424
    have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m23]; exact w22_428
    have w23_42c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m23]; exact w22_42c
    have b23_424 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m23]; exact b22_424
    have b23_425 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m23]; exact b22_425
    have b23_426 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m23]; exact b22_426
    have b23_427 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m23]; exact b22_427
    clear b22_427 b22_426 b22_425 b22_424 w22_42c w22_428 w22_424 w22_420 w22_37c w22_378 w22_374 w22_370 w22_36c w22_368 w22_364 w22_360 w22_32c w22_328 w22_78 w22_74 g22_8 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_10 g22_9 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 rb22 s22 m22 u22 c22 w21_374
    exact .inl ⟨(fun ⟨tl2', h0', h1', tl13', h2', h3', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr13] at h2'; cases h2'; exact hsirem h3'), sv_fail F E23 s23 t23 (fun x hx => (fR23 x hx).trans (fM x hx).symm) V23 hret g23_2 g23_18 hO g23_3 g23_4⟩
  -- 0xDE6: branch, not taken
  obtain ⟨n23, d23, u23⟩ := s22.notTaken E22.self 0xDEA sv_at_de6
    (by decide) (by rw [g22_10, s22.zero]; exact br_bne_f hsirem)
  have s23 : St n23.mem SV n23 0xDEA (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u23.regs, g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u23.regs, g22_9]
  have g23_10 : reg n23 a0 = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [u23.regs, g22_10]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = x20 := by rw [u23.regs, g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [u23.regs, g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = x22 := by rw [u23.regs, g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = x23 := by rw [u23.regs, g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = x24 := by rw [u23.regs, g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = x25 := by rw [u23.regs, g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by rw [u23.regs, g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = x27 := by rw [u23.regs, g22_27]
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m23]; exact w22_74
  have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m23]; exact w22_78
  have w23_328 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m23]; exact w22_328
  have w23_32c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m23]; exact w22_32c
  have w23_360 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m23]; exact w22_360
  have w23_364 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m23]; exact w22_364
  have w23_368 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m23]; exact w22_368
  have w23_36c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m23]; exact w22_36c
  have w23_370 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m23]; exact w22_370
  have w23_374 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m23]; exact w22_374
  have w23_378 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m23]; exact w22_378
  have w23_37c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = BitVec.ofNat 32 tl13.len := by rw [m23]; exact w22_37c
  have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m23]; exact w22_420
  have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m23]; exact w22_424
  have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m23]; exact w22_428
  have w23_42c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m23]; exact w22_42c
  have b23_424 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m23]; exact b22_424
  have b23_425 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m23]; exact b22_425
  have b23_426 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m23]; exact b22_426
  have b23_427 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m23]; exact b22_427
  clear b22_427 b22_426 b22_425 b22_424 w22_42c w22_428 w22_424 w22_420 w22_37c w22_378 w22_374 w22_370 w22_36c w22_368 w22_364 w22_360 w22_32c w22_328 w22_78 w22_74 g22_8 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_10 g22_9 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 rb22 s22 m22 u22 c22 w21_374
  -- 0xDEA
  obtain ⟨n24, c24, u24⟩ := s23.block svTr6dea E23.self svTr6dea_end
    ⟨trivial, trivial, trivial⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have s24 : St n24.mem SV n24 0xDEE (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have rb24 : ∀ q, reg n24 q = (runBlock svTr6dea (n23.mem, reg n23)).2 q := fun q => by rw [u24.regs]
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
  have g24_9 : reg n24 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
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
  have g24_24 : reg n24 (24 : Fin 32) = x24 := by
    rw [rb24, runBlock_reg _ _ _ (24 : Fin 32) s23.zero (by decide), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = x25 := by
    rw [rb24, runBlock_reg _ _ _ (25 : Fin 32) s23.zero (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by
    rw [rb24, runBlock_reg _ _ _ (26 : Fin 32) s23.zero (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = x27 := by
    rw [rb24, runBlock_reg _ _ _ (27 : Fin 32) s23.zero (by decide), g23_27]
  have g24_10 : reg n24 a0 = B + 0x21A0 + BitVec.ofNat 32 0x370 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svTr6dea, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_10, g23_18, g23_19, g23_20, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g24_11 : reg n24 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svTr6dea, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_10, g23_18, g23_19, g23_20, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m24]; exact w23_74
  have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m24]; exact w23_78
  have w24_328 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m24]; exact w23_328
  have w24_32c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m24]; exact w23_32c
  have w24_360 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m24]; exact w23_360
  have w24_364 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m24]; exact w23_364
  have w24_368 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m24]; exact w23_368
  have w24_36c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m24]; exact w23_36c
  have w24_370 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m24]; exact w23_370
  have w24_374 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m24]; exact w23_374
  have w24_378 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m24]; exact w23_378
  have w24_37c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = BitVec.ofNat 32 tl13.len := by rw [m24]; exact w23_37c
  have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m24]; exact w23_420
  have w24_424 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m24]; exact w23_424
  have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m24]; exact w23_428
  have w24_42c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m24]; exact w23_42c
  have b24_424 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m24]; exact b23_424
  have b24_425 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m24]; exact b23_425
  have b24_426 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m24]; exact b23_426
  have b24_427 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m24]; exact b23_427
  clear b23_427 b23_426 b23_425 b23_424 w23_42c w23_428 w23_424 w23_420 w23_37c w23_378 w23_374 w23_370 w23_36c w23_368 w23_364 w23_360 w23_32c w23_328 w23_78 w23_74 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
  -- 0xDEE: sv_iiF
  obtain ⟨n25, c25, s25, sp25, rk25, K25, A25, R25, fr25⟩ := sv_iiF (dc := 0x370)
    F E24 s24 sv_at_dee sv_at_df2 (by decide) (by decide) g24_2 g24_10
    (by decide) (by decide) w24_378 w24_37c ((sd_in.contentW hr2).contentW hr13)
  have t25 : Steps n0 n25 := t24.trans c25
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.keepL K25 (by decide)
  rw [sv_mb fR24 ((sd_in.contentW hr2).contentW hr13), derIntIsOf_congr fR24 ((sd_in.contentW hr2).contentW hr13), g24_11] at R25
  rw [sv_mb fR24 ((sd_in.contentW hr2).contentW hr13)] at A25
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk25 (3 : Fin 32) (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk25 (4 : Fin 32) (by decide), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rk25 (8 : Fin 32) (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [rk25 (9 : Fin 32) (by decide), g24_9]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [rk25 (18 : Fin 32) (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [rk25 (19 : Fin 32) (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = x20 := by rw [rk25 (20 : Fin 32) (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = x21 := by rw [rk25 (21 : Fin 32) (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = x22 := by rw [rk25 (22 : Fin 32) (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = x23 := by rw [rk25 (23 : Fin 32) (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = x24 := by rw [rk25 (24 : Fin 32) (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = x25 := by rw [rk25 (25 : Fin 32) (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by rw [rk25 (26 : Fin 32) (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = x27 := by rw [rk25 (27 : Fin 32) (by decide), g24_27]
  have g25_2 : reg n25 sp = B + 0x21A0 := sp25
  obtain ⟨r25, hr25⟩ : ∃ r, derIntIsOf M0 (memBytes M0 (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) (BitVec.ofNat 32 tl13.len).toNat) (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) (derElement 2 (memBytes M0 (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) (BitVec.ofNat 32 tl13.len).toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = r := ⟨_, rfl⟩
  rcases r25 with b25 | (_ | _)
  · rw [hr25] at R25
    obtain ⟨a0_25, a1_25⟩ := R25
    have g25_10 : reg n25 a0 = BitVec.ofNat 32 0x1 := a0_25
    have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8)] := keep_kk24.trans K25
    clear keep_kk24
    have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K25.w32 (by decide) (by decide)).trans w24_74
    have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K25.w32 (by decide) (by decide)).trans w24_78
    have w25_328 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K25.w32 (by decide) (by decide)).trans w24_328
    have w25_32c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K25.w32 (by decide) (by decide)).trans w24_32c
    have w25_360 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := (K25.w32 (by decide) (by decide)).trans w24_360
    have w25_364 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := (K25.w32 (by decide) (by decide)).trans w24_364
    have w25_368 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K25.w32 (by decide) (by decide)).trans w24_368
    have w25_36c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K25.w32 (by decide) (by decide)).trans w24_36c
    have w25_370 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K25.w32 (by decide) (by decide)).trans w24_370
    have w25_374 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := (K25.w32 (by decide) (by decide)).trans w24_374
    have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K25.w32 (by decide) (by decide)).trans w24_420
    have w25_424 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := (K25.w32 (by decide) (by decide)).trans w24_424
    have w25_428 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K25.w32 (by decide) (by decide)).trans w24_428
    have w25_42c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := (K25.w32 (by decide) (by decide)).trans w24_42c
    have b25_424 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := (K25.b8 (by decide) (by decide)).trans b24_424
    have b25_425 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K25.b8 (by decide) (by decide)).trans b24_425
    have b25_426 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K25.b8 (by decide) (by decide)).trans b24_426
    have b25_427 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K25.b8 (by decide) (by decide)).trans b24_427
    clear b24_427 b24_426 b24_425 b24_424 w24_42c w24_428 w24_424 w24_420 w24_37c w24_378 w24_374 w24_370 w24_36c w24_368 w24_364 w24_360 w24_32c w24_328 w24_78 w24_74 g24_11 g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
    -- 0xDF6
    obtain ⟨n26, c26, u26⟩ := s25.block svTr6df6 E25.self svTr6df6_end
      ⟨trivial, trivial⟩
    have m26 : n26.mem = n25.mem := u26.mem
    have s26 : St n26.mem SV n26 0xDF8 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
    have rb26 : ∀ q, reg n26 q = (runBlock svTr6df6 (n25.mem, reg n25)).2 q := fun q => by rw [u26.regs]
    have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
    have t26 : Steps n0 n26 := t25.trans c26
    have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
    have E26 : SvCode n26.mem := E25.fr F fr26
    have V26 : SvSaves B n26.mem v := V25.same m26
    have g26_2 : reg n26 sp = B + 0x21A0 := by
      rw [rb26, runBlock_reg _ _ _ sp s25.zero (by decide), g25_2]
    have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb26, runBlock_reg _ _ _ (3 : Fin 32) s25.zero (by decide), g25_3]
    have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb26, runBlock_reg _ _ _ (4 : Fin 32) s25.zero (by decide), g25_4]
    have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb26, runBlock_reg _ _ _ (8 : Fin 32) s25.zero (by decide), g25_8]
    have g26_9 : reg n26 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
      rw [rb26, runBlock_reg _ _ _ (9 : Fin 32) s25.zero (by decide), g25_9]
    have g26_18 : reg n26 (18 : Fin 32) = out := by
      rw [rb26, runBlock_reg _ _ _ (18 : Fin 32) s25.zero (by decide), g25_18]
    have g26_19 : reg n26 (19 : Fin 32) = bp := by
      rw [rb26, runBlock_reg _ _ _ (19 : Fin 32) s25.zero (by decide), g25_19]
    have g26_20 : reg n26 (20 : Fin 32) = x20 := by
      rw [rb26, runBlock_reg _ _ _ (20 : Fin 32) s25.zero (by decide), g25_20]
    have g26_21 : reg n26 (21 : Fin 32) = x21 := by
      rw [rb26, runBlock_reg _ _ _ (21 : Fin 32) s25.zero (by decide), g25_21]
    have g26_22 : reg n26 (22 : Fin 32) = x22 := by
      rw [rb26, runBlock_reg _ _ _ (22 : Fin 32) s25.zero (by decide), g25_22]
    have g26_23 : reg n26 (23 : Fin 32) = x23 := by
      rw [rb26, runBlock_reg _ _ _ (23 : Fin 32) s25.zero (by decide), g25_23]
    have g26_24 : reg n26 (24 : Fin 32) = x24 := by
      rw [rb26, runBlock_reg _ _ _ (24 : Fin 32) s25.zero (by decide), g25_24]
    have g26_25 : reg n26 (25 : Fin 32) = x25 := by
      rw [rb26, runBlock_reg _ _ _ (25 : Fin 32) s25.zero (by decide), g25_25]
    have g26_26 : reg n26 (26 : Fin 32) = x26 := by
      rw [rb26, runBlock_reg _ _ _ (26 : Fin 32) s25.zero (by decide), g25_26]
    have g26_27 : reg n26 (27 : Fin 32) = x27 := by
      rw [rb26, runBlock_reg _ _ _ (27 : Fin 32) s25.zero (by decide), g25_27]
    have g26_10 : reg n26 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb26]; simp +decide only [runBlock, BInstr.run, svTr6df6, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_10, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_25, g25_26, g25_27, s25.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8)] := by rw [m26]; exact keep_kk25
    clear keep_kk25
    have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m26]; exact w25_74
    have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m26]; exact w25_78
    have w26_328 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m26]; exact w25_328
    have w26_32c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m26]; exact w25_32c
    have w26_360 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m26]; exact w25_360
    have w26_364 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m26]; exact w25_364
    have w26_368 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m26]; exact w25_368
    have w26_36c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m26]; exact w25_36c
    have w26_370 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m26]; exact w25_370
    have w26_374 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m26]; exact w25_374
    have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m26]; exact w25_420
    have w26_424 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m26]; exact w25_424
    have w26_428 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m26]; exact w25_428
    have w26_42c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m26]; exact w25_42c
    have b26_424 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m26]; exact b25_424
    have b26_425 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m26]; exact b25_425
    have b26_426 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m26]; exact b25_426
    have b26_427 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m26]; exact b25_427
    clear b25_427 b25_426 b25_425 b25_424 w25_42c w25_428 w25_424 w25_420 w25_374 w25_370 w25_36c w25_368 w25_364 w25_360 w25_32c w25_328 w25_78 w25_74 g25_10 a1_25 a0_25
    -- 0xDF8: branch, taken
    obtain ⟨n27, d27, u27⟩ := s26.taken E26.self 0xE34 sv_at_df8
      (by decide) (by rw [g26_10, s26.zero]; decide)
    have s27 : St n27.mem SV n27 0xE34 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
    have m27 : n27.mem = n26.mem := u27.mem
    have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
    have t27 : Steps n0 n27 := t26.trans (.single d27)
    have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
    have E27 : SvCode n27.mem := E26.fr F fr27
    have V27 : SvSaves B n27.mem v := V26.same m27
    have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, g26_2]
    have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, g26_3]
    have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, g26_4]
    have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u27.regs, g26_8]
    have g27_9 : reg n27 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u27.regs, g26_9]
    have g27_10 : reg n27 a0 = BitVec.ofNat 32 0x1 := by rw [u27.regs, g26_10]
    have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, g26_18]
    have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, g26_19]
    have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [u27.regs, g26_20]
    have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [u27.regs, g26_21]
    have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [u27.regs, g26_22]
    have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [u27.regs, g26_23]
    have g27_24 : reg n27 (24 : Fin 32) = x24 := by rw [u27.regs, g26_24]
    have g27_25 : reg n27 (25 : Fin 32) = x25 := by rw [u27.regs, g26_25]
    have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, g26_26]
    have g27_27 : reg n27 (27 : Fin 32) = x27 := by rw [u27.regs, g26_27]
    have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8)] := by rw [m27]; exact keep_kk26
    clear keep_kk26
    have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m27]; exact w26_74
    have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m27]; exact w26_78
    have w27_328 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m27]; exact w26_328
    have w27_32c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m27]; exact w26_32c
    have w27_360 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m27]; exact w26_360
    have w27_364 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m27]; exact w26_364
    have w27_368 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m27]; exact w26_368
    have w27_36c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m27]; exact w26_36c
    have w27_370 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m27]; exact w26_370
    have w27_374 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m27]; exact w26_374
    have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m27]; exact w26_420
    have w27_424 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m27]; exact w26_424
    have w27_428 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m27]; exact w26_428
    have w27_42c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m27]; exact w26_42c
    have b27_424 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m27]; exact b26_424
    have b27_425 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m27]; exact b26_425
    have b27_426 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m27]; exact b26_426
    have b27_427 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m27]; exact b26_427
    clear b26_427 b26_426 b26_425 b26_424 w26_42c w26_428 w26_424 w26_420 w26_374 w26_370 w26_36c w26_368 w26_364 w26_360 w26_32c w26_328 w26_78 w26_74 g26_10 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 rb26 s26 m26 u26 c26
    -- 0xE34
    obtain ⟨n28, c28, u28⟩ := s27.block svTr6e34 E27.self svTr6e34_end
      ⟨trivial, trivial⟩
    have m28 : n28.mem = n27.mem := u28.mem
    have s28 : St n28.mem SV n28 0xE36 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
    have rb28 : ∀ q, reg n28 q = (runBlock svTr6e34 (n27.mem, reg n27)).2 q := fun q => by rw [u28.regs]
    have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
    have t28 : Steps n0 n28 := t27.trans c28
    have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
    have E28 : SvCode n28.mem := E27.fr F fr28
    have V28 : SvSaves B n28.mem v := V27.same m28
    have g28_2 : reg n28 sp = B + 0x21A0 := by
      rw [rb28, runBlock_reg _ _ _ sp s27.zero (by decide), g27_2]
    have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb28, runBlock_reg _ _ _ (3 : Fin 32) s27.zero (by decide), g27_3]
    have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb28, runBlock_reg _ _ _ (4 : Fin 32) s27.zero (by decide), g27_4]
    have g28_9 : reg n28 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
      rw [rb28, runBlock_reg _ _ _ (9 : Fin 32) s27.zero (by decide), g27_9]
    have g28_10 : reg n28 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb28, runBlock_reg _ _ _ a0 s27.zero (by decide), g27_10]
    have g28_18 : reg n28 (18 : Fin 32) = out := by
      rw [rb28, runBlock_reg _ _ _ (18 : Fin 32) s27.zero (by decide), g27_18]
    have g28_19 : reg n28 (19 : Fin 32) = bp := by
      rw [rb28, runBlock_reg _ _ _ (19 : Fin 32) s27.zero (by decide), g27_19]
    have g28_20 : reg n28 (20 : Fin 32) = x20 := by
      rw [rb28, runBlock_reg _ _ _ (20 : Fin 32) s27.zero (by decide), g27_20]
    have g28_21 : reg n28 (21 : Fin 32) = x21 := by
      rw [rb28, runBlock_reg _ _ _ (21 : Fin 32) s27.zero (by decide), g27_21]
    have g28_22 : reg n28 (22 : Fin 32) = x22 := by
      rw [rb28, runBlock_reg _ _ _ (22 : Fin 32) s27.zero (by decide), g27_22]
    have g28_23 : reg n28 (23 : Fin 32) = x23 := by
      rw [rb28, runBlock_reg _ _ _ (23 : Fin 32) s27.zero (by decide), g27_23]
    have g28_24 : reg n28 (24 : Fin 32) = x24 := by
      rw [rb28, runBlock_reg _ _ _ (24 : Fin 32) s27.zero (by decide), g27_24]
    have g28_25 : reg n28 (25 : Fin 32) = x25 := by
      rw [rb28, runBlock_reg _ _ _ (25 : Fin 32) s27.zero (by decide), g27_25]
    have g28_26 : reg n28 (26 : Fin 32) = x26 := by
      rw [rb28, runBlock_reg _ _ _ (26 : Fin 32) s27.zero (by decide), g27_26]
    have g28_27 : reg n28 (27 : Fin 32) = x27 := by
      rw [rb28, runBlock_reg _ _ _ (27 : Fin 32) s27.zero (by decide), g27_27]
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8)] := by rw [m28]; exact keep_kk27
    clear keep_kk27
    have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m28]; exact w27_74
    have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m28]; exact w27_78
    have w28_328 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m28]; exact w27_328
    have w28_32c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m28]; exact w27_32c
    have w28_360 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m28]; exact w27_360
    have w28_364 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m28]; exact w27_364
    have w28_368 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m28]; exact w27_368
    have w28_36c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m28]; exact w27_36c
    have w28_370 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m28]; exact w27_370
    have w28_374 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m28]; exact w27_374
    have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m28]; exact w27_420
    have w28_424 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m28]; exact w27_424
    have w28_428 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m28]; exact w27_428
    have w28_42c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m28]; exact w27_42c
    have b28_424 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m28]; exact b27_424
    have b28_425 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m28]; exact b27_425
    have b28_426 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m28]; exact b27_426
    have b28_427 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m28]; exact b27_427
    clear b27_427 b27_426 b27_425 b27_424 w27_42c w27_428 w27_424 w27_420 w27_374 w27_370 w27_36c w27_368 w27_364 w27_360 w27_32c w27_328 w27_78 w27_74 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_10 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
    -- 0xE36: j
    obtain ⟨n29, d29, u29⟩ := s28.jump E28.self sv_at_e36 (off' := 0x7A4) (by decide)
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
    have g29_9 : reg n29 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u29.regs, g28_9]
    have g29_10 : reg n29 a0 = BitVec.ofNat 32 0x1 := by rw [u29.regs, g28_10]
    have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, g28_19]
    have g29_20 : reg n29 (20 : Fin 32) = x20 := by rw [u29.regs, g28_20]
    have g29_21 : reg n29 (21 : Fin 32) = x21 := by rw [u29.regs, g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = x22 := by rw [u29.regs, g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = x23 := by rw [u29.regs, g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = x24 := by rw [u29.regs, g28_24]
    have g29_25 : reg n29 (25 : Fin 32) = x25 := by rw [u29.regs, g28_25]
    have g29_26 : reg n29 (26 : Fin 32) = x26 := by rw [u29.regs, g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = x27 := by rw [u29.regs, g28_27]
    have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8)] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m29]; exact w28_74
    have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m29]; exact w28_78
    have w29_328 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m29]; exact w28_328
    have w29_32c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m29]; exact w28_32c
    have w29_360 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m29]; exact w28_360
    have w29_364 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m29]; exact w28_364
    have w29_368 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m29]; exact w28_368
    have w29_36c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m29]; exact w28_36c
    have w29_370 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m29]; exact w28_370
    have w29_374 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m29]; exact w28_374
    have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m29]; exact w28_420
    have w29_424 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m29]; exact w28_424
    have w29_428 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m29]; exact w28_428
    have w29_42c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m29]; exact w28_42c
    have b29_424 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m29]; exact b28_424
    have b29_425 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m29]; exact b28_425
    have b29_426 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m29]; exact b28_426
    have b29_427 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m29]; exact b28_427
    clear b28_427 b28_426 b28_425 b28_424 w28_42c w28_428 w28_424 w28_420 w28_374 w28_370 w28_36c w28_368 w28_364 w28_360 w28_32c w28_328 w28_78 w28_74 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_10 g28_9 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 rb28 s28 m28 u28 c28
    exact .inl ⟨(fun ⟨tl2', h0', h1', tl13', h2', h3', h4', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr13] at h2'; cases h2'; rw [hr25] at h4'; cases h4'), sv_fail F E29 s29 t29 (fun x hx => (fR29 x hx).trans (fM x hx).symm) V29 hret g29_2 g29_18 hO g29_3 g29_4⟩
  · rw [hr25] at R25
    obtain ⟨a0_25, a1_25⟩ := R25
    have g25_10 : reg n25 a0 = BitVec.ofNat 32 0x0 := a0_25
    have g25_11 : reg n25 a1 = BitVec.ofNat 32 0x0 := by rw [a1_25]; rfl
    have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8)] := keep_kk24.trans K25
    clear keep_kk24
    have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K25.w32 (by decide) (by decide)).trans w24_74
    have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K25.w32 (by decide) (by decide)).trans w24_78
    have w25_328 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K25.w32 (by decide) (by decide)).trans w24_328
    have w25_32c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K25.w32 (by decide) (by decide)).trans w24_32c
    have w25_360 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := (K25.w32 (by decide) (by decide)).trans w24_360
    have w25_364 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := (K25.w32 (by decide) (by decide)).trans w24_364
    have w25_368 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K25.w32 (by decide) (by decide)).trans w24_368
    have w25_36c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K25.w32 (by decide) (by decide)).trans w24_36c
    have w25_370 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K25.w32 (by decide) (by decide)).trans w24_370
    have w25_374 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := (K25.w32 (by decide) (by decide)).trans w24_374
    have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K25.w32 (by decide) (by decide)).trans w24_420
    have w25_424 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := (K25.w32 (by decide) (by decide)).trans w24_424
    have w25_428 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K25.w32 (by decide) (by decide)).trans w24_428
    have w25_42c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := (K25.w32 (by decide) (by decide)).trans w24_42c
    have b25_424 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := (K25.b8 (by decide) (by decide)).trans b24_424
    have b25_425 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K25.b8 (by decide) (by decide)).trans b24_425
    have b25_426 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K25.b8 (by decide) (by decide)).trans b24_426
    have b25_427 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K25.b8 (by decide) (by decide)).trans b24_427
    clear b24_427 b24_426 b24_425 b24_424 w24_42c w24_428 w24_424 w24_420 w24_37c w24_378 w24_374 w24_370 w24_36c w24_368 w24_364 w24_360 w24_32c w24_328 w24_78 w24_74 g24_11 g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
    -- 0xDF6
    obtain ⟨n26, c26, u26⟩ := s25.block svTr6df6 E25.self svTr6df6_end
      ⟨trivial, trivial⟩
    have m26 : n26.mem = n25.mem := u26.mem
    have s26 : St n26.mem SV n26 0xDF8 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
    have rb26 : ∀ q, reg n26 q = (runBlock svTr6df6 (n25.mem, reg n25)).2 q := fun q => by rw [u26.regs]
    have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
    have t26 : Steps n0 n26 := t25.trans c26
    have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
    have E26 : SvCode n26.mem := E25.fr F fr26
    have V26 : SvSaves B n26.mem v := V25.same m26
    have g26_2 : reg n26 sp = B + 0x21A0 := by
      rw [rb26, runBlock_reg _ _ _ sp s25.zero (by decide), g25_2]
    have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb26, runBlock_reg _ _ _ (3 : Fin 32) s25.zero (by decide), g25_3]
    have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb26, runBlock_reg _ _ _ (4 : Fin 32) s25.zero (by decide), g25_4]
    have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb26, runBlock_reg _ _ _ (8 : Fin 32) s25.zero (by decide), g25_8]
    have g26_9 : reg n26 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
      rw [rb26, runBlock_reg _ _ _ (9 : Fin 32) s25.zero (by decide), g25_9]
    have g26_11 : reg n26 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb26, runBlock_reg _ _ _ a1 s25.zero (by decide), g25_11]
    have g26_18 : reg n26 (18 : Fin 32) = out := by
      rw [rb26, runBlock_reg _ _ _ (18 : Fin 32) s25.zero (by decide), g25_18]
    have g26_19 : reg n26 (19 : Fin 32) = bp := by
      rw [rb26, runBlock_reg _ _ _ (19 : Fin 32) s25.zero (by decide), g25_19]
    have g26_20 : reg n26 (20 : Fin 32) = x20 := by
      rw [rb26, runBlock_reg _ _ _ (20 : Fin 32) s25.zero (by decide), g25_20]
    have g26_21 : reg n26 (21 : Fin 32) = x21 := by
      rw [rb26, runBlock_reg _ _ _ (21 : Fin 32) s25.zero (by decide), g25_21]
    have g26_22 : reg n26 (22 : Fin 32) = x22 := by
      rw [rb26, runBlock_reg _ _ _ (22 : Fin 32) s25.zero (by decide), g25_22]
    have g26_23 : reg n26 (23 : Fin 32) = x23 := by
      rw [rb26, runBlock_reg _ _ _ (23 : Fin 32) s25.zero (by decide), g25_23]
    have g26_24 : reg n26 (24 : Fin 32) = x24 := by
      rw [rb26, runBlock_reg _ _ _ (24 : Fin 32) s25.zero (by decide), g25_24]
    have g26_25 : reg n26 (25 : Fin 32) = x25 := by
      rw [rb26, runBlock_reg _ _ _ (25 : Fin 32) s25.zero (by decide), g25_25]
    have g26_26 : reg n26 (26 : Fin 32) = x26 := by
      rw [rb26, runBlock_reg _ _ _ (26 : Fin 32) s25.zero (by decide), g25_26]
    have g26_27 : reg n26 (27 : Fin 32) = x27 := by
      rw [rb26, runBlock_reg _ _ _ (27 : Fin 32) s25.zero (by decide), g25_27]
    have g26_10 : reg n26 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb26]; simp +decide only [runBlock, BInstr.run, svTr6df6, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_10, g25_11, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_25, g25_26, g25_27, s25.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8)] := by rw [m26]; exact keep_kk25
    clear keep_kk25
    have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m26]; exact w25_74
    have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m26]; exact w25_78
    have w26_328 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m26]; exact w25_328
    have w26_32c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m26]; exact w25_32c
    have w26_360 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m26]; exact w25_360
    have w26_364 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m26]; exact w25_364
    have w26_368 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m26]; exact w25_368
    have w26_36c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m26]; exact w25_36c
    have w26_370 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m26]; exact w25_370
    have w26_374 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m26]; exact w25_374
    have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m26]; exact w25_420
    have w26_424 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m26]; exact w25_424
    have w26_428 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m26]; exact w25_428
    have w26_42c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m26]; exact w25_42c
    have b26_424 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m26]; exact b25_424
    have b26_425 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m26]; exact b25_425
    have b26_426 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m26]; exact b25_426
    have b26_427 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m26]; exact b25_427
    clear b25_427 b25_426 b25_425 b25_424 w25_42c w25_428 w25_424 w25_420 w25_374 w25_370 w25_36c w25_368 w25_364 w25_360 w25_32c w25_328 w25_78 w25_74 g25_11 g25_10 a1_25 a0_25
    -- 0xDF8: branch, not taken
    obtain ⟨n27, d27, u27⟩ := s26.notTaken E26.self 0xDFA sv_at_df8
      (by decide) (by rw [g26_10, s26.zero]; decide)
    have s27 : St n27.mem SV n27 0xDFA (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
    have m27 : n27.mem = n26.mem := u27.mem
    have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
    have t27 : Steps n0 n27 := t26.trans (.single d27)
    have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
    have E27 : SvCode n27.mem := E26.fr F fr27
    have V27 : SvSaves B n27.mem v := V26.same m27
    have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, g26_2]
    have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, g26_3]
    have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, g26_4]
    have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u27.regs, g26_8]
    have g27_9 : reg n27 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u27.regs, g26_9]
    have g27_10 : reg n27 a0 = BitVec.ofNat 32 0x0 := by rw [u27.regs, g26_10]
    have g27_11 : reg n27 a1 = BitVec.ofNat 32 0x0 := by rw [u27.regs, g26_11]
    have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, g26_18]
    have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, g26_19]
    have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [u27.regs, g26_20]
    have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [u27.regs, g26_21]
    have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [u27.regs, g26_22]
    have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [u27.regs, g26_23]
    have g27_24 : reg n27 (24 : Fin 32) = x24 := by rw [u27.regs, g26_24]
    have g27_25 : reg n27 (25 : Fin 32) = x25 := by rw [u27.regs, g26_25]
    have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, g26_26]
    have g27_27 : reg n27 (27 : Fin 32) = x27 := by rw [u27.regs, g26_27]
    have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8)] := by rw [m27]; exact keep_kk26
    clear keep_kk26
    have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m27]; exact w26_74
    have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m27]; exact w26_78
    have w27_328 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m27]; exact w26_328
    have w27_32c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m27]; exact w26_32c
    have w27_360 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m27]; exact w26_360
    have w27_364 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m27]; exact w26_364
    have w27_368 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m27]; exact w26_368
    have w27_36c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m27]; exact w26_36c
    have w27_370 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m27]; exact w26_370
    have w27_374 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m27]; exact w26_374
    have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m27]; exact w26_420
    have w27_424 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m27]; exact w26_424
    have w27_428 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m27]; exact w26_428
    have w27_42c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m27]; exact w26_42c
    have b27_424 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m27]; exact b26_424
    have b27_425 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m27]; exact b26_425
    have b27_426 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m27]; exact b26_426
    have b27_427 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m27]; exact b26_427
    clear b26_427 b26_426 b26_425 b26_424 w26_42c w26_428 w26_424 w26_420 w26_374 w26_370 w26_36c w26_368 w26_364 w26_360 w26_32c w26_328 w26_78 w26_74 g26_10 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_11 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 rb26 s26 m26 u26 c26
    -- 0xDFA
    obtain ⟨n28, c28, u28⟩ := s27.block svTr6dfa E27.self svTr6dfa_end
      ⟨trivial, trivial⟩
    have m28 : n28.mem = n27.mem := u28.mem
    have s28 : St n28.mem SV n28 0xDFC (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
    have rb28 : ∀ q, reg n28 q = (runBlock svTr6dfa (n27.mem, reg n27)).2 q := fun q => by rw [u28.regs]
    have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
    have t28 : Steps n0 n28 := t27.trans c28
    have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
    have E28 : SvCode n28.mem := E27.fr F fr28
    have V28 : SvSaves B n28.mem v := V27.same m28
    have g28_2 : reg n28 sp = B + 0x21A0 := by
      rw [rb28, runBlock_reg _ _ _ sp s27.zero (by decide), g27_2]
    have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb28, runBlock_reg _ _ _ (3 : Fin 32) s27.zero (by decide), g27_3]
    have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb28, runBlock_reg _ _ _ (4 : Fin 32) s27.zero (by decide), g27_4]
    have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb28, runBlock_reg _ _ _ (8 : Fin 32) s27.zero (by decide), g27_8]
    have g28_9 : reg n28 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
      rw [rb28, runBlock_reg _ _ _ (9 : Fin 32) s27.zero (by decide), g27_9]
    have g28_10 : reg n28 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb28, runBlock_reg _ _ _ a0 s27.zero (by decide), g27_10]
    have g28_18 : reg n28 (18 : Fin 32) = out := by
      rw [rb28, runBlock_reg _ _ _ (18 : Fin 32) s27.zero (by decide), g27_18]
    have g28_19 : reg n28 (19 : Fin 32) = bp := by
      rw [rb28, runBlock_reg _ _ _ (19 : Fin 32) s27.zero (by decide), g27_19]
    have g28_20 : reg n28 (20 : Fin 32) = x20 := by
      rw [rb28, runBlock_reg _ _ _ (20 : Fin 32) s27.zero (by decide), g27_20]
    have g28_21 : reg n28 (21 : Fin 32) = x21 := by
      rw [rb28, runBlock_reg _ _ _ (21 : Fin 32) s27.zero (by decide), g27_21]
    have g28_22 : reg n28 (22 : Fin 32) = x22 := by
      rw [rb28, runBlock_reg _ _ _ (22 : Fin 32) s27.zero (by decide), g27_22]
    have g28_23 : reg n28 (23 : Fin 32) = x23 := by
      rw [rb28, runBlock_reg _ _ _ (23 : Fin 32) s27.zero (by decide), g27_23]
    have g28_24 : reg n28 (24 : Fin 32) = x24 := by
      rw [rb28, runBlock_reg _ _ _ (24 : Fin 32) s27.zero (by decide), g27_24]
    have g28_25 : reg n28 (25 : Fin 32) = x25 := by
      rw [rb28, runBlock_reg _ _ _ (25 : Fin 32) s27.zero (by decide), g27_25]
    have g28_26 : reg n28 (26 : Fin 32) = x26 := by
      rw [rb28, runBlock_reg _ _ _ (26 : Fin 32) s27.zero (by decide), g27_26]
    have g28_27 : reg n28 (27 : Fin 32) = x27 := by
      rw [rb28, runBlock_reg _ _ _ (27 : Fin 32) s27.zero (by decide), g27_27]
    have g28_11 : reg n28 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb28]; simp +decide only [runBlock, BInstr.run, svTr6dfa, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g27_2, g27_3, g27_4, g27_8, g27_9, g27_10, g27_11, g27_18, g27_19, g27_20, g27_21, g27_22, g27_23, g27_24, g27_25, g27_26, g27_27, s27.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8)] := by rw [m28]; exact keep_kk27
    clear keep_kk27
    have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m28]; exact w27_74
    have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m28]; exact w27_78
    have w28_328 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m28]; exact w27_328
    have w28_32c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m28]; exact w27_32c
    have w28_360 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m28]; exact w27_360
    have w28_364 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m28]; exact w27_364
    have w28_368 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m28]; exact w27_368
    have w28_36c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m28]; exact w27_36c
    have w28_370 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m28]; exact w27_370
    have w28_374 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m28]; exact w27_374
    have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m28]; exact w27_420
    have w28_424 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m28]; exact w27_424
    have w28_428 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m28]; exact w27_428
    have w28_42c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m28]; exact w27_42c
    have b28_424 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m28]; exact b27_424
    have b28_425 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m28]; exact b27_425
    have b28_426 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m28]; exact b27_426
    have b28_427 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m28]; exact b27_427
    clear b27_427 b27_426 b27_425 b27_424 w27_42c w27_428 w27_424 w27_420 w27_374 w27_370 w27_36c w27_368 w27_364 w27_360 w27_32c w27_328 w27_78 w27_74 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_11 g27_10 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
    -- 0xDFC: branch, taken
    obtain ⟨n29, d29, u29⟩ := s28.taken E28.self 0x7A4 sv_at_dfc
      (by decide) (by rw [g28_11, s28.zero]; decide)
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
    have g29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u29.regs, g28_8]
    have g29_9 : reg n29 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u29.regs, g28_9]
    have g29_10 : reg n29 a0 = BitVec.ofNat 32 0x0 := by rw [u29.regs, g28_10]
    have g29_11 : reg n29 a1 = BitVec.ofNat 32 0x0 := by rw [u29.regs, g28_11]
    have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, g28_19]
    have g29_20 : reg n29 (20 : Fin 32) = x20 := by rw [u29.regs, g28_20]
    have g29_21 : reg n29 (21 : Fin 32) = x21 := by rw [u29.regs, g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = x22 := by rw [u29.regs, g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = x23 := by rw [u29.regs, g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = x24 := by rw [u29.regs, g28_24]
    have g29_25 : reg n29 (25 : Fin 32) = x25 := by rw [u29.regs, g28_25]
    have g29_26 : reg n29 (26 : Fin 32) = x26 := by rw [u29.regs, g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = x27 := by rw [u29.regs, g28_27]
    have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8)] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m29]; exact w28_74
    have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m29]; exact w28_78
    have w29_328 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m29]; exact w28_328
    have w29_32c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m29]; exact w28_32c
    have w29_360 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m29]; exact w28_360
    have w29_364 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m29]; exact w28_364
    have w29_368 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m29]; exact w28_368
    have w29_36c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m29]; exact w28_36c
    have w29_370 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m29]; exact w28_370
    have w29_374 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m29]; exact w28_374
    have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m29]; exact w28_420
    have w29_424 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m29]; exact w28_424
    have w29_428 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m29]; exact w28_428
    have w29_42c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m29]; exact w28_42c
    have b29_424 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m29]; exact b28_424
    have b29_425 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m29]; exact b28_425
    have b29_426 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m29]; exact b28_426
    have b29_427 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m29]; exact b28_427
    clear b28_427 b28_426 b28_425 b28_424 w28_42c w28_428 w28_424 w28_420 w28_374 w28_370 w28_36c w28_368 w28_364 w28_360 w28_32c w28_328 w28_78 w28_74 g28_11 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_10 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 rb28 s28 m28 u28 c28
    exact .inl ⟨(fun ⟨tl2', h0', h1', tl13', h2', h3', h4', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr13] at h2'; cases h2'; rw [hr25] at h4'; cases h4'), sv_fail F E29 s29 t29 (fun x hx => (fR29 x hx).trans (fM x hx).symm) V29 hret g29_2 g29_18 hO g29_3 g29_4⟩
  obtain ⟨te25, hte25⟩ := ii_ok_elem hr25
  obtain ⟨d8_25, d12_25⟩ := A25 te25 hte25
  rw [hr25] at R25
  obtain ⟨a0_25, a1_25⟩ := R25
  have g25_10 : reg n25 a0 = BitVec.ofNat 32 0x0 := a0_25
  have g25_11 : reg n25 a1 = BitVec.ofNat 32 0x1 := by rw [a1_25]; rfl
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8)] := keep_kk24.trans K25
  clear keep_kk24
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K25.w32 (by decide) (by decide)).trans w24_74
  have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K25.w32 (by decide) (by decide)).trans w24_78
  have w25_328 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K25.w32 (by decide) (by decide)).trans w24_328
  have w25_32c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K25.w32 (by decide) (by decide)).trans w24_32c
  have w25_360 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := (K25.w32 (by decide) (by decide)).trans w24_360
  have w25_364 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := (K25.w32 (by decide) (by decide)).trans w24_364
  have w25_368 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K25.w32 (by decide) (by decide)).trans w24_368
  have w25_36c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K25.w32 (by decide) (by decide)).trans w24_36c
  have w25_370 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K25.w32 (by decide) (by decide)).trans w24_370
  have w25_374 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := (K25.w32 (by decide) (by decide)).trans w24_374
  have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K25.w32 (by decide) (by decide)).trans w24_420
  have w25_424 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := (K25.w32 (by decide) (by decide)).trans w24_424
  have w25_428 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K25.w32 (by decide) (by decide)).trans w24_428
  have w25_42c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := (K25.w32 (by decide) (by decide)).trans w24_42c
  have b25_424 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := (K25.b8 (by decide) (by decide)).trans b24_424
  have b25_425 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K25.b8 (by decide) (by decide)).trans b24_425
  have b25_426 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K25.b8 (by decide) (by decide)).trans b24_426
  have b25_427 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K25.b8 (by decide) (by decide)).trans b24_427
  have w25_378 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := d8_25
  have w25_37c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len) := d12_25
  clear b24_427 b24_426 b24_425 b24_424 w24_42c w24_428 w24_424 w24_420 w24_37c w24_378 w24_374 w24_370 w24_36c w24_368 w24_364 w24_360 w24_32c w24_328 w24_78 w24_74 g24_11 g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
  -- 0xDF6
  obtain ⟨n26, c26, u26⟩ := s25.block svTr6df6 E25.self svTr6df6_end
    ⟨trivial, trivial⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have s26 : St n26.mem SV n26 0xDF8 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have rb26 : ∀ q, reg n26 q = (runBlock svTr6df6 (n25.mem, reg n25)).2 q := fun q => by rw [u26.regs]
  have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans c26
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by
    rw [rb26, runBlock_reg _ _ _ sp s25.zero (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb26, runBlock_reg _ _ _ (3 : Fin 32) s25.zero (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb26, runBlock_reg _ _ _ (4 : Fin 32) s25.zero (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb26, runBlock_reg _ _ _ (8 : Fin 32) s25.zero (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
    rw [rb26, runBlock_reg _ _ _ (9 : Fin 32) s25.zero (by decide), g25_9]
  have g26_11 : reg n26 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb26, runBlock_reg _ _ _ a1 s25.zero (by decide), g25_11]
  have g26_18 : reg n26 (18 : Fin 32) = out := by
    rw [rb26, runBlock_reg _ _ _ (18 : Fin 32) s25.zero (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by
    rw [rb26, runBlock_reg _ _ _ (19 : Fin 32) s25.zero (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = x20 := by
    rw [rb26, runBlock_reg _ _ _ (20 : Fin 32) s25.zero (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = x21 := by
    rw [rb26, runBlock_reg _ _ _ (21 : Fin 32) s25.zero (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = x22 := by
    rw [rb26, runBlock_reg _ _ _ (22 : Fin 32) s25.zero (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = x23 := by
    rw [rb26, runBlock_reg _ _ _ (23 : Fin 32) s25.zero (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = x24 := by
    rw [rb26, runBlock_reg _ _ _ (24 : Fin 32) s25.zero (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = x25 := by
    rw [rb26, runBlock_reg _ _ _ (25 : Fin 32) s25.zero (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by
    rw [rb26, runBlock_reg _ _ _ (26 : Fin 32) s25.zero (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = x27 := by
    rw [rb26, runBlock_reg _ _ _ (27 : Fin 32) s25.zero (by decide), g25_27]
  have g26_10 : reg n26 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, svTr6df6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_10, g25_11, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_25, g25_26, g25_27, s25.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m26]; exact w25_74
  have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m26]; exact w25_78
  have w26_328 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m26]; exact w25_328
  have w26_32c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m26]; exact w25_32c
  have w26_360 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m26]; exact w25_360
  have w26_364 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m26]; exact w25_364
  have w26_368 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m26]; exact w25_368
  have w26_36c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m26]; exact w25_36c
  have w26_370 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m26]; exact w25_370
  have w26_374 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m26]; exact w25_374
  have w26_378 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m26]; exact w25_378
  have w26_37c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len) := by rw [m26]; exact w25_37c
  have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m26]; exact w25_420
  have w26_424 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m26]; exact w25_424
  have w26_428 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m26]; exact w25_428
  have w26_42c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m26]; exact w25_42c
  have b26_424 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m26]; exact b25_424
  have b26_425 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m26]; exact b25_425
  have b26_426 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m26]; exact b25_426
  have b26_427 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m26]; exact b25_427
  clear w25_37c w25_378 b25_427 b25_426 b25_425 b25_424 w25_42c w25_428 w25_424 w25_420 w25_374 w25_370 w25_36c w25_368 w25_364 w25_360 w25_32c w25_328 w25_78 w25_74 g25_11 g25_10 a1_25 a0_25 d12_25 d8_25 g25_2 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 V25 E25 fR25 t25 fr25 A25 K25 rk25 sp25 s25 c25
  -- 0xDF8: branch, not taken
  obtain ⟨n27, d27, u27⟩ := s26.notTaken E26.self 0xDFA sv_at_df8
    (by decide) (by rw [g26_10, s26.zero]; decide)
  have s27 : St n27.mem SV n27 0xDFA (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans (.single d27)
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u27.regs, g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u27.regs, g26_9]
  have g27_10 : reg n27 a0 = BitVec.ofNat 32 0x0 := by rw [u27.regs, g26_10]
  have g27_11 : reg n27 a1 = BitVec.ofNat 32 0x1 := by rw [u27.regs, g26_11]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [u27.regs, g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [u27.regs, g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [u27.regs, g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [u27.regs, g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = x24 := by rw [u27.regs, g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = x25 := by rw [u27.regs, g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = x27 := by rw [u27.regs, g26_27]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m27]; exact w26_74
  have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m27]; exact w26_78
  have w27_328 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m27]; exact w26_328
  have w27_32c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m27]; exact w26_32c
  have w27_360 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m27]; exact w26_360
  have w27_364 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m27]; exact w26_364
  have w27_368 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m27]; exact w26_368
  have w27_36c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m27]; exact w26_36c
  have w27_370 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m27]; exact w26_370
  have w27_374 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m27]; exact w26_374
  have w27_378 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m27]; exact w26_378
  have w27_37c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len) := by rw [m27]; exact w26_37c
  have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m27]; exact w26_420
  have w27_424 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m27]; exact w26_424
  have w27_428 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m27]; exact w26_428
  have w27_42c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m27]; exact w26_42c
  have b27_424 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m27]; exact b26_424
  have b27_425 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m27]; exact b26_425
  have b27_426 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m27]; exact b26_426
  have b27_427 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m27]; exact b26_427
  clear b26_427 b26_426 b26_425 b26_424 w26_42c w26_428 w26_424 w26_420 w26_37c w26_378 w26_374 w26_370 w26_36c w26_368 w26_364 w26_360 w26_32c w26_328 w26_78 w26_74 g26_10 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_11 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 rb26 s26 m26 u26 c26
  -- 0xDFA
  obtain ⟨n28, c28, u28⟩ := s27.block svTr6dfa E27.self svTr6dfa_end
    ⟨trivial, trivial⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have s28 : St n28.mem SV n28 0xDFC (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have rb28 : ∀ q, reg n28 q = (runBlock svTr6dfa (n27.mem, reg n27)).2 q := fun q => by rw [u28.regs]
  have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
  have t28 : Steps n0 n28 := t27.trans c28
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.same m28
  have g28_2 : reg n28 sp = B + 0x21A0 := by
    rw [rb28, runBlock_reg _ _ _ sp s27.zero (by decide), g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb28, runBlock_reg _ _ _ (3 : Fin 32) s27.zero (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb28, runBlock_reg _ _ _ (4 : Fin 32) s27.zero (by decide), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb28, runBlock_reg _ _ _ (8 : Fin 32) s27.zero (by decide), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
    rw [rb28, runBlock_reg _ _ _ (9 : Fin 32) s27.zero (by decide), g27_9]
  have g28_10 : reg n28 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb28, runBlock_reg _ _ _ a0 s27.zero (by decide), g27_10]
  have g28_18 : reg n28 (18 : Fin 32) = out := by
    rw [rb28, runBlock_reg _ _ _ (18 : Fin 32) s27.zero (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by
    rw [rb28, runBlock_reg _ _ _ (19 : Fin 32) s27.zero (by decide), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = x20 := by
    rw [rb28, runBlock_reg _ _ _ (20 : Fin 32) s27.zero (by decide), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = x21 := by
    rw [rb28, runBlock_reg _ _ _ (21 : Fin 32) s27.zero (by decide), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = x22 := by
    rw [rb28, runBlock_reg _ _ _ (22 : Fin 32) s27.zero (by decide), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = x23 := by
    rw [rb28, runBlock_reg _ _ _ (23 : Fin 32) s27.zero (by decide), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = x24 := by
    rw [rb28, runBlock_reg _ _ _ (24 : Fin 32) s27.zero (by decide), g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = x25 := by
    rw [rb28, runBlock_reg _ _ _ (25 : Fin 32) s27.zero (by decide), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by
    rw [rb28, runBlock_reg _ _ _ (26 : Fin 32) s27.zero (by decide), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = x27 := by
    rw [rb28, runBlock_reg _ _ _ (27 : Fin 32) s27.zero (by decide), g27_27]
  have g28_11 : reg n28 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb28]; simp +decide only [runBlock, BInstr.run, svTr6dfa, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g27_2, g27_3, g27_4, g27_8, g27_9, g27_10, g27_11, g27_18, g27_19, g27_20, g27_21, g27_22, g27_23, g27_24, g27_25, g27_26, g27_27, s27.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8)] := by rw [m28]; exact keep_kk27
  clear keep_kk27
  have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m28]; exact w27_74
  have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m28]; exact w27_78
  have w28_328 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m28]; exact w27_328
  have w28_32c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m28]; exact w27_32c
  have w28_360 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m28]; exact w27_360
  have w28_364 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m28]; exact w27_364
  have w28_368 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m28]; exact w27_368
  have w28_36c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m28]; exact w27_36c
  have w28_370 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m28]; exact w27_370
  have w28_374 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m28]; exact w27_374
  have w28_378 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m28]; exact w27_378
  have w28_37c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len) := by rw [m28]; exact w27_37c
  have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m28]; exact w27_420
  have w28_424 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m28]; exact w27_424
  have w28_428 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m28]; exact w27_428
  have w28_42c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m28]; exact w27_42c
  have b28_424 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m28]; exact b27_424
  have b28_425 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m28]; exact b27_425
  have b28_426 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m28]; exact b27_426
  have b28_427 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m28]; exact b27_427
  clear b27_427 b27_426 b27_425 b27_424 w27_42c w27_428 w27_424 w27_420 w27_37c w27_378 w27_374 w27_370 w27_36c w27_368 w27_364 w27_360 w27_32c w27_328 w27_78 w27_74 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_11 g27_10 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
  -- 0xDFC: branch, not taken
  obtain ⟨n29, d29, u29⟩ := s28.notTaken E28.self 0xE00 sv_at_dfc
    (by decide) (by rw [g28_11, s28.zero]; decide)
  have s29 : St n29.mem SV n29 0xE00 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans (.single d29)
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u29.regs, g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u29.regs, g28_9]
  have g29_10 : reg n29 a0 = BitVec.ofNat 32 0x0 := by rw [u29.regs, g28_10]
  have g29_11 : reg n29 a1 = BitVec.ofNat 32 0x1 := by rw [u29.regs, g28_11]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = x20 := by rw [u29.regs, g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = x21 := by rw [u29.regs, g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = x22 := by rw [u29.regs, g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = x23 := by rw [u29.regs, g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = x24 := by rw [u29.regs, g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = x25 := by rw [u29.regs, g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by rw [u29.regs, g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = x27 := by rw [u29.regs, g28_27]
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m29]; exact w28_74
  have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m29]; exact w28_78
  have w29_328 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m29]; exact w28_328
  have w29_32c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m29]; exact w28_32c
  have w29_360 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m29]; exact w28_360
  have w29_364 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m29]; exact w28_364
  have w29_368 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m29]; exact w28_368
  have w29_36c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m29]; exact w28_36c
  have w29_370 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m29]; exact w28_370
  have w29_374 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m29]; exact w28_374
  have w29_378 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m29]; exact w28_378
  have w29_37c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len) := by rw [m29]; exact w28_37c
  have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m29]; exact w28_420
  have w29_424 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m29]; exact w28_424
  have w29_428 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m29]; exact w28_428
  have w29_42c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m29]; exact w28_42c
  have b29_424 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m29]; exact b28_424
  have b29_425 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m29]; exact b28_425
  have b29_426 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m29]; exact b28_426
  have b29_427 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m29]; exact b28_427
  clear b28_427 b28_426 b28_425 b28_424 w28_42c w28_428 w28_424 w28_420 w28_37c w28_378 w28_374 w28_370 w28_36c w28_368 w28_364 w28_360 w28_32c w28_328 w28_78 w28_74 g28_11 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_10 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 rb28 s28 m28 u28 c28
  -- 0xE00
  obtain ⟨n30, c30, u30⟩ := s29.block svTr6e00 E29.self svTr6e00_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have s30 : St n30.mem SV n30 0xE0A (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have rb30 : ∀ q, reg n30 q = (runBlock svTr6e00 (n29.mem, reg n29)).2 q := fun q => by rw [u30.regs]
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
  have g30_8 : reg n30 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb30, runBlock_reg _ _ _ (8 : Fin 32) s29.zero (by decide), g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
    rw [rb30, runBlock_reg _ _ _ (9 : Fin 32) s29.zero (by decide), g29_9]
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
  have g30_24 : reg n30 (24 : Fin 32) = x24 := by
    rw [rb30, runBlock_reg _ _ _ (24 : Fin 32) s29.zero (by decide), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = x25 := by
    rw [rb30, runBlock_reg _ _ _ (25 : Fin 32) s29.zero (by decide), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = x26 := by
    rw [rb30, runBlock_reg _ _ _ (26 : Fin 32) s29.zero (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = x27 := by
    rw [rb30, runBlock_reg _ _ _ (27 : Fin 32) s29.zero (by decide), g29_27]
  have g30_10 : reg n30 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb30]; simp +decide only [runBlock, BInstr.run, svTr6e00, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g29_2, g29_3, g29_4, g29_8, g29_9, g29_10, g29_11, g29_18, g29_19, g29_20, g29_21, g29_22, g29_23, g29_24, g29_25, g29_26, g29_27, s29.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g30_11 : reg n30 a1 = B + 0x21A0 + BitVec.ofNat 32 0x370 := by
    rw [rb30]; simp +decide only [runBlock, BInstr.run, svTr6e00, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g29_2, g29_3, g29_4, g29_8, g29_9, g29_10, g29_11, g29_18, g29_19, g29_20, g29_21, g29_22, g29_23, g29_24, g29_25, g29_26, g29_27, s29.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g30_12 : reg n30 a2 = BitVec.ofNat 32 0x30 := by
    rw [rb30]; simp +decide only [runBlock, BInstr.run, svTr6e00, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g29_2, g29_3, g29_4, g29_8, g29_9, g29_10, g29_11, g29_18, g29_19, g29_20, g29_21, g29_22, g29_23, g29_24, g29_25, g29_26, g29_27, s29.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8)] := by rw [m30]; exact keep_kk29
  clear keep_kk29
  have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m30]; exact w29_74
  have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m30]; exact w29_78
  have w30_328 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m30]; exact w29_328
  have w30_32c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m30]; exact w29_32c
  have w30_360 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m30]; exact w29_360
  have w30_364 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m30]; exact w29_364
  have w30_368 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m30]; exact w29_368
  have w30_36c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m30]; exact w29_36c
  have w30_370 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m30]; exact w29_370
  have w30_374 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m30]; exact w29_374
  have w30_378 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m30]; exact w29_378
  have w30_37c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len) := by rw [m30]; exact w29_37c
  have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m30]; exact w29_420
  have w30_424 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl13.len := by rw [m30]; exact w29_424
  have w30_428 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m30]; exact w29_428
  have w30_42c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl13.len := by rw [m30]; exact w29_42c
  have b30_424 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m30]; exact b29_424
  have b30_425 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m30]; exact b29_425
  have b30_426 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m30]; exact b29_426
  have b30_427 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m30]; exact b29_427
  clear b29_427 b29_426 b29_425 b29_424 w29_42c w29_428 w29_424 w29_420 w29_37c w29_378 w29_374 w29_370 w29_36c w29_368 w29_364 w29_360 w29_32c w29_328 w29_78 w29_74 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_11 g29_10 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
  -- 0xE0A: sv_elemF
  obtain ⟨n31, c31, s31, rk31, K31, Ok31, Er31, fr31⟩ := sv_elemF (oc := 0x420) (dc := 0x370) (tag := 0x30)
    F E30 s30 sv_at_e0a sv_at_e0e (by decide) (by decide) g30_10 g30_11 g30_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w30_378 w30_37c
  have t31 : Steps n0 n31 := t30.trans c31
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.keepL K31 (by decide)
  rw [sv_mb fR30 (((sd_in.contentW hr2).contentW hr13).restW hte25)] at Ok31 Er31
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [rk31 sp (by decide) (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk31 (3 : Fin 32) (by decide) (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk31 (4 : Fin 32) (by decide) (by decide), g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rk31 (8 : Fin 32) (by decide) (by decide), g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [rk31 (9 : Fin 32) (by decide) (by decide), g30_9]
  have g31_10 : reg n31 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by rw [rk31 a0 (by decide) (by decide), g30_10]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [rk31 (18 : Fin 32) (by decide) (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [rk31 (19 : Fin 32) (by decide) (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = x20 := by rw [rk31 (20 : Fin 32) (by decide) (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = x21 := by rw [rk31 (21 : Fin 32) (by decide) (by decide), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = x22 := by rw [rk31 (22 : Fin 32) (by decide) (by decide), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = x23 := by rw [rk31 (23 : Fin 32) (by decide) (by decide), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = x24 := by rw [rk31 (24 : Fin 32) (by decide) (by decide), g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = x25 := by rw [rk31 (25 : Fin 32) (by decide) (by decide), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = x26 := by rw [rk31 (26 : Fin 32) (by decide) (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = x27 := by rw [rk31 (27 : Fin 32) (by decide) (by decide), g30_27]
  obtain ⟨r31, hr31⟩ : ∃ r, derElement 0x30 (memBytes M0 ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) ((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)).toNat) = r := ⟨_, rfl⟩
  rcases r31 with er31 | tl31
  · obtain ⟨zhr31, -⟩ := Er31 er31 hr31
    have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8)] := keep_kk30.trans K31
    clear keep_kk30
    have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K31.w32 (by decide) (by decide)).trans w30_74
    have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K31.w32 (by decide) (by decide)).trans w30_78
    have w31_328 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K31.w32 (by decide) (by decide)).trans w30_328
    have w31_32c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K31.w32 (by decide) (by decide)).trans w30_32c
    have w31_360 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := (K31.w32 (by decide) (by decide)).trans w30_360
    have w31_364 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := (K31.w32 (by decide) (by decide)).trans w30_364
    have w31_368 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K31.w32 (by decide) (by decide)).trans w30_368
    have w31_36c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K31.w32 (by decide) (by decide)).trans w30_36c
    have w31_370 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K31.w32 (by decide) (by decide)).trans w30_370
    have w31_374 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := (K31.w32 (by decide) (by decide)).trans w30_374
    have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := zhr31
    clear b30_427 b30_426 b30_425 b30_424 w30_42c w30_428 w30_424 w30_420 w30_37c w30_378 w30_374 w30_370 w30_36c w30_368 w30_364 w30_360 w30_32c w30_328 w30_78 w30_74 g30_12 g30_11 g30_10 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 rb30 s30 m30 u30 c30
    -- 0xE12: lw
    obtain ⟨n32, d32, u32⟩ := s31.lw E31.self sv_at_e12 (off' := 0xE16) (by decide)
      (by rw [g31_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s32 : St n32.mem SV n32 0xE16 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
    have m32 : n32.mem = n31.mem := u32.mem
    have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
    have t32 : Steps n0 n32 := t31.trans (.single d32)
    have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
    have E32 : SvCode n32.mem := E31.fr F fr32
    have V32 : SvSaves B n32.mem v := V31.same m32
    have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_2]
    have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_3]
    have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_4]
    have g32_8 : reg n32 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_8]
    have g32_9 : reg n32 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u32.regs, upd_ne (by decide) (by decide), g31_9]
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
    have g32_10 : reg n32 a0 = 0 := by
      rw [u32.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g31_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w31_420]
    have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8)] := by rw [m32]; exact keep_kk31
    clear keep_kk31
    have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m32]; exact w31_74
    have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m32]; exact w31_78
    have w32_328 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m32]; exact w31_328
    have w32_32c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m32]; exact w31_32c
    have w32_360 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m32]; exact w31_360
    have w32_364 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m32]; exact w31_364
    have w32_368 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m32]; exact w31_368
    have w32_36c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m32]; exact w31_36c
    have w32_370 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m32]; exact w31_370
    have w32_374 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m32]; exact w31_374
    have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m32]; exact w31_420
    clear w31_420 w31_374 w31_370 w31_36c w31_368 w31_364 w31_360 w31_32c w31_328 w31_78 w31_74 zhr31
    -- 0xE16: branch, taken
    obtain ⟨n33, d33, u33⟩ := s32.taken E32.self 0x12AA sv_at_e16
      (by decide) (by rw [g32_10, s32.zero]; rfl)
    have s33 : St n33.mem SV n33 0x12AA (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
    have m33 : n33.mem = n32.mem := u33.mem
    have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
    have t33 : Steps n0 n33 := t32.trans (.single d33)
    have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
    have E33 : SvCode n33.mem := E32.fr F fr33
    have V33 : SvSaves B n33.mem v := V32.same m33
    have g33_2 : reg n33 sp = B + 0x21A0 := by rw [u33.regs, g32_2]
    have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u33.regs, g32_3]
    have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u33.regs, g32_4]
    have g33_8 : reg n33 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u33.regs, g32_8]
    have g33_9 : reg n33 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u33.regs, g32_9]
    have g33_10 : reg n33 a0 = 0 := by rw [u33.regs, g32_10]
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
    have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8)] := by rw [m33]; exact keep_kk32
    clear keep_kk32
    have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m33]; exact w32_74
    have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m33]; exact w32_78
    have w33_328 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m33]; exact w32_328
    have w33_32c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m33]; exact w32_32c
    have w33_360 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m33]; exact w32_360
    have w33_364 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m33]; exact w32_364
    have w33_368 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m33]; exact w32_368
    have w33_36c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m33]; exact w32_36c
    have w33_370 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m33]; exact w32_370
    have w33_374 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m33]; exact w32_374
    have w33_420 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m33]; exact w32_420
    clear w32_420 w32_374 w32_370 w32_36c w32_368 w32_364 w32_360 w32_32c w32_328 w32_78 w32_74 g32_10 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
    -- 0x12AA: lbu
    obtain ⟨n34, d34, u34⟩ := s33.lbu E33.self sv_at_12aa (off' := 0x12AE) (by decide)
    have s34 : St n34.mem SV n34 0x12AE (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
    have m34 : n34.mem = n33.mem := u34.mem
    have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
    have t34 : Steps n0 n34 := t33.trans (.single d34)
    have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
    have E34 : SvCode n34.mem := E33.fr F fr34
    have V34 : SvSaves B n34.mem v := V33.same m34
    have g34_2 : reg n34 sp = B + 0x21A0 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_2]
    have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_3]
    have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_4]
    have g34_9 : reg n34 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u34.regs, upd_ne (by decide) (by decide), g33_9]
    have g34_10 : reg n34 a0 = 0 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_10]
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
    have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8)] := by rw [m34]; exact keep_kk33
    clear keep_kk33
    have w34_74 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m34]; exact w33_74
    have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m34]; exact w33_78
    have w34_328 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m34]; exact w33_328
    have w34_32c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m34]; exact w33_32c
    have w34_360 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m34]; exact w33_360
    have w34_364 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m34]; exact w33_364
    have w34_368 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m34]; exact w33_368
    have w34_36c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m34]; exact w33_36c
    have w34_370 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m34]; exact w33_370
    have w34_374 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m34]; exact w33_374
    have w34_420 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m34]; exact w33_420
    clear w33_420 w33_374 w33_370 w33_36c w33_368 w33_364 w33_360 w33_32c w33_328 w33_78 w33_74 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_10 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 m33 s33 u33 d33
    -- 0x12AE: j
    obtain ⟨n35, d35, u35⟩ := s34.jump E34.self sv_at_12ae (off' := 0x7A4) (by decide)
      (by rw [s34.pc]; decide)
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
    have g35_9 : reg n35 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u35.regs, g34_9]
    have g35_10 : reg n35 a0 = 0 := by rw [u35.regs, g34_10]
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
    have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8)] := by rw [m35]; exact keep_kk34
    clear keep_kk34
    have w35_74 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m35]; exact w34_74
    have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m35]; exact w34_78
    have w35_328 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m35]; exact w34_328
    have w35_32c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m35]; exact w34_32c
    have w35_360 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m35]; exact w34_360
    have w35_364 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m35]; exact w34_364
    have w35_368 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m35]; exact w34_368
    have w35_36c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m35]; exact w34_36c
    have w35_370 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m35]; exact w34_370
    have w35_374 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m35]; exact w34_374
    have w35_420 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = 0 := by rw [m35]; exact w34_420
    clear w34_420 w34_374 w34_370 w34_36c w34_368 w34_364 w34_360 w34_32c w34_328 w34_78 w34_74 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_10 g34_9 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 m34 s34 u34 d34
    exact .inl ⟨(fun ⟨tl2', h0', h1', tl13', h2', h3', h4', te25', h5', tl31', h6', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr13] at h2'; cases h2'; rw [hr25] at h4'; cases h4'; rw [hte25] at h5'; cases h5'; rw [hr31] at h6'; cases h6'), sv_fail F E35 s35 t35 (fun x hx => (fR35 x hx).trans (fM x hx).symm) V35 hret g35_2 g35_18 hO g35_3 g35_4⟩
  obtain ⟨o0_31, o4_31, o8_31, o12_31, o16_31, d8_31, d12_31⟩ := Ok31 tl31 hr31
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8)] := keep_kk30.trans K31
  clear keep_kk30
  have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K31.w32 (by decide) (by decide)).trans w30_74
  have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K31.w32 (by decide) (by decide)).trans w30_78
  have w31_328 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K31.w32 (by decide) (by decide)).trans w30_328
  have w31_32c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K31.w32 (by decide) (by decide)).trans w30_32c
  have w31_360 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := (K31.w32 (by decide) (by decide)).trans w30_360
  have w31_364 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := (K31.w32 (by decide) (by decide)).trans w30_364
  have w31_368 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K31.w32 (by decide) (by decide)).trans w30_368
  have w31_36c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K31.w32 (by decide) (by decide)).trans w30_36c
  have w31_370 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K31.w32 (by decide) (by decide)).trans w30_370
  have w31_374 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := (K31.w32 (by decide) (by decide)).trans w30_374
  have w31_378 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len) := d8_31
  have w31_37c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len) := d12_31
  have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := o0_31
  have w31_424 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := o4_31
  have w31_428 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := o8_31
  have w31_42c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := o12_31
  have b31_430 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := o16_31
  clear b30_427 b30_426 b30_425 b30_424 w30_42c w30_428 w30_424 w30_420 w30_37c w30_378 w30_374 w30_370 w30_36c w30_368 w30_364 w30_360 w30_32c w30_328 w30_78 w30_74 g30_12 g30_11 g30_10 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 rb30 s30 m30 u30 c30
  -- 0xE12: lw
  obtain ⟨n32, d32, u32⟩ := s31.lw E31.self sv_at_e12 (off' := 0xE16) (by decide)
    (by rw [g31_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s32 : St n32.mem SV n32 0xE16 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans (.single d32)
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u32.regs, upd_ne (by decide) (by decide), g31_9]
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
  have g32_10 : reg n32 a0 = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by
    rw [u32.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g31_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, w31_420]
  have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8)] := by rw [m32]; exact keep_kk31
  clear keep_kk31
  have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m32]; exact w31_74
  have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m32]; exact w31_78
  have w32_328 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m32]; exact w31_328
  have w32_32c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m32]; exact w31_32c
  have w32_360 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m32]; exact w31_360
  have w32_364 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m32]; exact w31_364
  have w32_368 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m32]; exact w31_368
  have w32_36c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m32]; exact w31_36c
  have w32_370 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m32]; exact w31_370
  have w32_374 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m32]; exact w31_374
  have w32_378 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m32]; exact w31_378
  have w32_37c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m32]; exact w31_37c
  have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by rw [m32]; exact w31_420
  have w32_424 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := by rw [m32]; exact w31_424
  have w32_428 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m32]; exact w31_428
  have w32_42c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m32]; exact w31_42c
  have b32_430 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := by rw [m32]; exact b31_430
  clear b31_430 w31_42c w31_428 w31_424 w31_420 w31_37c w31_378 w31_374 w31_370 w31_36c w31_368 w31_364 w31_360 w31_32c w31_328 w31_78 w31_74 d12_31 d8_31 o16_31 o12_31 o8_31 o4_31 o0_31 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_10 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 Er31 Ok31 K31 rk31 s31 c31
  -- 0xE16: branch, not taken
  obtain ⟨n33, d33, u33⟩ := s32.notTaken E32.self 0xE1A sv_at_e16
    (by decide) (by rw [g32_10, s32.zero]; exact br_beq_f ((((sd_in.contentW hr2).contentW hr13).restW hte25).ok_ne hr31))
  have s33 : St n33.mem SV n33 0xE1A (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
  have t33 : Steps n0 n33 := t32.trans (.single d33)
  have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.same m33
  have g33_2 : reg n33 sp = B + 0x21A0 := by rw [u33.regs, g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u33.regs, g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u33.regs, g32_4]
  have g33_8 : reg n33 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u33.regs, g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u33.regs, g32_9]
  have g33_10 : reg n33 a0 = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by rw [u33.regs, g32_10]
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
  have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8)] := by rw [m33]; exact keep_kk32
  clear keep_kk32
  have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m33]; exact w32_74
  have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m33]; exact w32_78
  have w33_328 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m33]; exact w32_328
  have w33_32c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m33]; exact w32_32c
  have w33_360 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m33]; exact w32_360
  have w33_364 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m33]; exact w32_364
  have w33_368 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m33]; exact w32_368
  have w33_36c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m33]; exact w32_36c
  have w33_370 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m33]; exact w32_370
  have w33_374 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m33]; exact w32_374
  have w33_378 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m33]; exact w32_378
  have w33_37c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m33]; exact w32_37c
  have w33_420 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by rw [m33]; exact w32_420
  have w33_424 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := by rw [m33]; exact w32_424
  have w33_428 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m33]; exact w32_428
  have w33_42c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m33]; exact w32_42c
  have b33_430 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := by rw [m33]; exact b32_430
  clear b32_430 w32_42c w32_428 w32_424 w32_420 w32_37c w32_378 w32_374 w32_370 w32_36c w32_368 w32_364 w32_360 w32_32c w32_328 w32_78 w32_74 g32_10 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
  -- 0xE1A: lw
  obtain ⟨n34, d34, u34⟩ := s33.lw E33.self sv_at_e1a (off' := 0xE1E) (by decide)
    (by rw [g33_2, show B + 0x21A0 + 0x428 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s34 : St n34.mem SV n34 0xE1E (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
  have m34 : n34.mem = n33.mem := u34.mem
  have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
  have t34 : Steps n0 n34 := t33.trans (.single d34)
  have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.same m34
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_4]
  have g34_8 : reg n34 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u34.regs, upd_ne (by decide) (by decide), g33_9]
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
  have g34_10 : reg n34 a0 = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by
    rw [u34.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g33_2, show B + 0x21A0 + 0x428 = B + 0x21A0 + BitVec.ofNat 32 0x428 by sv_addr, w33_428]
  have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8)] := by rw [m34]; exact keep_kk33
  clear keep_kk33
  have w34_74 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m34]; exact w33_74
  have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m34]; exact w33_78
  have w34_328 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m34]; exact w33_328
  have w34_32c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m34]; exact w33_32c
  have w34_360 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m34]; exact w33_360
  have w34_364 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m34]; exact w33_364
  have w34_368 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m34]; exact w33_368
  have w34_36c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m34]; exact w33_36c
  have w34_370 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m34]; exact w33_370
  have w34_374 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m34]; exact w33_374
  have w34_378 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m34]; exact w33_378
  have w34_37c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m34]; exact w33_37c
  have w34_420 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by rw [m34]; exact w33_420
  have w34_424 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := by rw [m34]; exact w33_424
  have w34_428 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m34]; exact w33_428
  have w34_42c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m34]; exact w33_42c
  have b34_430 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := by rw [m34]; exact b33_430
  clear b33_430 w33_42c w33_428 w33_424 w33_420 w33_37c w33_378 w33_374 w33_370 w33_36c w33_368 w33_364 w33_360 w33_32c w33_328 w33_78 w33_74 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_10 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 m33 s33 u33 d33
  -- 0xE1E: sw
  obtain ⟨n35, d35, s35, fr35, K35, W35, rg35⟩ := sv_sw F E34 s34 sv_at_e1e (off' := 0xE20) (c := 0x4C)
    (by decide) (by rw [g34_2]; sv_addr) (by decide) (by decide)
  have t35 : Steps n0 n35 := t34.trans d35
  have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.keep K35 (by decide)
  have g35_2 : reg n35 sp = B + 0x21A0 := by rw [rg35 sp, g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg35 (3 : Fin 32), g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg35 (4 : Fin 32), g34_4]
  have g35_8 : reg n35 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rg35 (8 : Fin 32), g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [rg35 (9 : Fin 32), g34_9]
  have g35_10 : reg n35 a0 = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [rg35 a0, g34_10]
  have g35_18 : reg n35 (18 : Fin 32) = out := by rw [rg35 (18 : Fin 32), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [rg35 (19 : Fin 32), g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = x20 := by rw [rg35 (20 : Fin 32), g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = x21 := by rw [rg35 (21 : Fin 32), g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = x22 := by rw [rg35 (22 : Fin 32), g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = x23 := by rw [rg35 (23 : Fin 32), g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = x24 := by rw [rg35 (24 : Fin 32), g34_24]
  have g35_25 : reg n35 (25 : Fin 32) = x25 := by rw [rg35 (25 : Fin 32), g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = x26 := by rw [rg35 (26 : Fin 32), g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = x27 := by rw [rg35 (27 : Fin 32), g34_27]
  have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4)] := keep_kk34.trans K35.toL
  clear keep_kk34
  have w35_74 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K35.w32 (by decide) (by decide)).trans w34_74
  have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K35.w32 (by decide) (by decide)).trans w34_78
  have w35_328 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K35.w32 (by decide) (by decide)).trans w34_328
  have w35_32c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K35.w32 (by decide) (by decide)).trans w34_32c
  have w35_360 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := (K35.w32 (by decide) (by decide)).trans w34_360
  have w35_364 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := (K35.w32 (by decide) (by decide)).trans w34_364
  have w35_368 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K35.w32 (by decide) (by decide)).trans w34_368
  have w35_36c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K35.w32 (by decide) (by decide)).trans w34_36c
  have w35_370 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K35.w32 (by decide) (by decide)).trans w34_370
  have w35_374 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := (K35.w32 (by decide) (by decide)).trans w34_374
  have w35_378 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len) := (K35.w32 (by decide) (by decide)).trans w34_378
  have w35_37c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len) := (K35.w32 (by decide) (by decide)).trans w34_37c
  have w35_420 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := (K35.w32 (by decide) (by decide)).trans w34_420
  have w35_424 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := (K35.w32 (by decide) (by decide)).trans w34_424
  have w35_428 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := (K35.w32 (by decide) (by decide)).trans w34_428
  have w35_42c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := (K35.w32 (by decide) (by decide)).trans w34_42c
  have b35_430 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := (K35.b8 (by decide) (by decide)).trans b34_430
  have w35_4c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [W35, g34_10]
  clear b34_430 w34_42c w34_428 w34_424 w34_420 w34_37c w34_378 w34_374 w34_370 w34_36c w34_368 w34_364 w34_360 w34_32c w34_328 w34_78 w34_74 g34_10 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 m34 s34 u34 d34
  -- 0xE20: lw
  obtain ⟨n36, d36, u36⟩ := s35.lw E35.self sv_at_e20 (off' := 0xE24) (by decide)
    (by rw [g35_2, show B + 0x21A0 + 0x42C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s36 : St n36.mem SV n36 0xE24 (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
  have m36 : n36.mem = n35.mem := u36.mem
  have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
  have t36 : Steps n0 n36 := t35.trans (.single d36)
  have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.same m36
  have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_4]
  have g36_8 : reg n36 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_8]
  have g36_9 : reg n36 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u36.regs, upd_ne (by decide) (by decide), g35_9]
  have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, upd_ne (by decide) (by decide), g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_19]
  have g36_20 : reg n36 (20 : Fin 32) = x20 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_20]
  have g36_21 : reg n36 (21 : Fin 32) = x21 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = x22 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = x23 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_23]
  have g36_24 : reg n36 (24 : Fin 32) = x24 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_24]
  have g36_25 : reg n36 (25 : Fin 32) = x25 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = x26 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = x27 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_27]
  have g36_10 : reg n36 a0 = BitVec.ofNat 32 (tl31.header + tl31.len) := by
    rw [u36.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g35_2, show B + 0x21A0 + 0x42C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr, w35_42c]
  have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4)] := by rw [m36]; exact keep_kk35
  clear keep_kk35
  have w36_4c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m36]; exact w35_4c
  have w36_74 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m36]; exact w35_74
  have w36_78 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m36]; exact w35_78
  have w36_328 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m36]; exact w35_328
  have w36_32c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m36]; exact w35_32c
  have w36_360 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m36]; exact w35_360
  have w36_364 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m36]; exact w35_364
  have w36_368 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m36]; exact w35_368
  have w36_36c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m36]; exact w35_36c
  have w36_370 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m36]; exact w35_370
  have w36_374 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m36]; exact w35_374
  have w36_378 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m36]; exact w35_378
  have w36_37c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m36]; exact w35_37c
  have w36_420 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by rw [m36]; exact w35_420
  have w36_424 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := by rw [m36]; exact w35_424
  have w36_428 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m36]; exact w35_428
  have w36_42c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m36]; exact w35_42c
  have b36_430 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := by rw [m36]; exact b35_430
  clear w35_4c b35_430 w35_42c w35_428 w35_424 w35_420 w35_37c w35_378 w35_374 w35_370 w35_36c w35_368 w35_364 w35_360 w35_32c w35_328 w35_78 w35_74 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_10 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 rg35 W35 K35 fr35 s35 d35
  -- 0xE24: sw
  obtain ⟨n37, d37, s37, fr37, K37, W37, rg37⟩ := sv_sw F E36 s36 sv_at_e24 (off' := 0xE26) (c := 0x48)
    (by decide) (by rw [g36_2]; sv_addr) (by decide) (by decide)
  have t37 : Steps n0 n37 := t36.trans d37
  have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : SvCode n37.mem := E36.fr F fr37
  have V37 : SvSaves B n37.mem v := V36.keep K37 (by decide)
  have g37_2 : reg n37 sp = B + 0x21A0 := by rw [rg37 sp, g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg37 (3 : Fin 32), g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg37 (4 : Fin 32), g36_4]
  have g37_8 : reg n37 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rg37 (8 : Fin 32), g36_8]
  have g37_9 : reg n37 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [rg37 (9 : Fin 32), g36_9]
  have g37_10 : reg n37 a0 = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [rg37 a0, g36_10]
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
  have keep_kk37 : SvKeepL B n0.mem n37.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4)] := keep_kk36.trans K37.toL
  clear keep_kk36
  have w37_4c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := (K37.w32 (by decide) (by decide)).trans w36_4c
  have w37_74 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K37.w32 (by decide) (by decide)).trans w36_74
  have w37_78 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K37.w32 (by decide) (by decide)).trans w36_78
  have w37_328 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K37.w32 (by decide) (by decide)).trans w36_328
  have w37_32c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K37.w32 (by decide) (by decide)).trans w36_32c
  have w37_360 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := (K37.w32 (by decide) (by decide)).trans w36_360
  have w37_364 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := (K37.w32 (by decide) (by decide)).trans w36_364
  have w37_368 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K37.w32 (by decide) (by decide)).trans w36_368
  have w37_36c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K37.w32 (by decide) (by decide)).trans w36_36c
  have w37_370 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K37.w32 (by decide) (by decide)).trans w36_370
  have w37_374 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := (K37.w32 (by decide) (by decide)).trans w36_374
  have w37_378 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len) := (K37.w32 (by decide) (by decide)).trans w36_378
  have w37_37c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len) := (K37.w32 (by decide) (by decide)).trans w36_37c
  have w37_420 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := (K37.w32 (by decide) (by decide)).trans w36_420
  have w37_424 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := (K37.w32 (by decide) (by decide)).trans w36_424
  have w37_428 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := (K37.w32 (by decide) (by decide)).trans w36_428
  have w37_42c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := (K37.w32 (by decide) (by decide)).trans w36_42c
  have b37_430 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := (K37.b8 (by decide) (by decide)).trans b36_430
  have w37_48 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [W37, g36_10]
  clear b36_430 w36_42c w36_428 w36_424 w36_420 w36_37c w36_378 w36_374 w36_370 w36_36c w36_368 w36_364 w36_360 w36_32c w36_328 w36_78 w36_74 w36_4c g36_10 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 m36 s36 u36 d36
  -- 0xE26
  obtain ⟨n38, c38, u38⟩ := s37.block svTr6e26 E37.self svTr6e26_end
    ⟨trivial, trivial⟩
  have m38 : n38.mem = n37.mem := u38.mem
  have s38 : St n38.mem SV n38 0xE28 (reg n38) := ⟨u38.pc, rfl, fun _ => rfl⟩
  have rb38 : ∀ q, reg n38 q = (runBlock svTr6e26 (n37.mem, reg n37)).2 q := fun q => by rw [u38.regs]
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
  have g38_8 : reg n38 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb38, runBlock_reg _ _ _ (8 : Fin 32) s37.zero (by decide), g37_8]
  have g38_9 : reg n38 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
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
  have g38_10 : reg n38 a0 = B + 0x21A0 + BitVec.ofNat 32 0x370 := by
    rw [rb38]; simp +decide only [runBlock, BInstr.run, svTr6e26, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g37_2, g37_3, g37_4, g37_8, g37_9, g37_10, g37_18, g37_19, g37_20, g37_21, g37_22, g37_23, g37_24, g37_25, g37_26, g37_27, s37.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk38 : SvKeepL B n0.mem n38.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4)] := by rw [m38]; exact keep_kk37
  clear keep_kk37
  have w38_48 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m38]; exact w37_48
  have w38_4c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m38]; exact w37_4c
  have w38_74 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m38]; exact w37_74
  have w38_78 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m38]; exact w37_78
  have w38_328 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m38]; exact w37_328
  have w38_32c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m38]; exact w37_32c
  have w38_360 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m38]; exact w37_360
  have w38_364 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m38]; exact w37_364
  have w38_368 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m38]; exact w37_368
  have w38_36c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m38]; exact w37_36c
  have w38_370 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m38]; exact w37_370
  have w38_374 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m38]; exact w37_374
  have w38_378 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m38]; exact w37_378
  have w38_37c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m38]; exact w37_37c
  have w38_420 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by rw [m38]; exact w37_420
  have w38_424 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := by rw [m38]; exact w37_424
  have w38_428 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m38]; exact w37_428
  have w38_42c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m38]; exact w37_42c
  have b38_430 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := by rw [m38]; exact b37_430
  clear w37_48 b37_430 w37_42c w37_428 w37_424 w37_420 w37_37c w37_378 w37_374 w37_370 w37_36c w37_368 w37_364 w37_360 w37_32c w37_328 w37_78 w37_74 w37_4c g37_27 g37_26 g37_25 g37_24 g37_23 g37_22 g37_21 g37_20 g37_19 g37_18 g37_10 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 rg37 W37 K37 fr37 s37 d37
  -- 0xE28: sv_isShaF
  obtain ⟨n39, c39, s39, sp39, rk39, K39, A39, R39, fr39⟩ := sv_isShaF (dc := 0x370)
    F E38 (D0.sv FW fR38) s38 sv_at_e28 sv_at_e2c (by decide) (by decide) g38_2
    g38_10 (by decide) (by decide) w38_378 w38_37c ((((sd_in.contentW hr2).contentW hr13).restW hte25).restW hr31)
  have t39 : Steps n0 n39 := t38.trans c39
  have fR39 : ∀ x, SvR B x → n39.mem x = M0 x := fun x hx => (fr39 x hx).trans (fR38 x hx)
  have E39 : SvCode n39.mem := E38.fr F fr39
  have V39 : SvSaves B n39.mem v := V38.keepL K39 (by decide)
  rw [isSha256Of_congr (sv_pt fR38 ((((sd_in.contentW hr2).contentW hr13).restW hte25).restW hr31))] at R39
  rw [sv_mb fR38 ((((sd_in.contentW hr2).contentW hr13).restW hte25).restW hr31)] at A39
  have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk39 (3 : Fin 32) (by decide), g38_3]
  have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk39 (4 : Fin 32) (by decide), g38_4]
  have g39_8 : reg n39 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rk39 (8 : Fin 32) (by decide), g38_8]
  have g39_9 : reg n39 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [rk39 (9 : Fin 32) (by decide), g38_9]
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
  obtain ⟨r39, hr39⟩ : ∃ r, isSha256Of M0 (((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) (((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)).toNat = r := ⟨_, rfl⟩
  rcases r39 with b39 | (_ | _)
  · rw [hr39] at R39
    obtain ⟨a0_39, a1_39⟩ := R39
    have g39_10 : reg n39 a0 = BitVec.ofNat 32 0x1 := a0_39
    have keep_kk39 : SvKeepL B n0.mem n39.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8)] := keep_kk38.trans K39
    clear keep_kk38
    have w39_48 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := (K39.w32 (by decide) (by decide)).trans w38_48
    have w39_4c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := (K39.w32 (by decide) (by decide)).trans w38_4c
    have w39_74 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K39.w32 (by decide) (by decide)).trans w38_74
    have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K39.w32 (by decide) (by decide)).trans w38_78
    have w39_328 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K39.w32 (by decide) (by decide)).trans w38_328
    have w39_32c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K39.w32 (by decide) (by decide)).trans w38_32c
    have w39_360 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := (K39.w32 (by decide) (by decide)).trans w38_360
    have w39_364 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := (K39.w32 (by decide) (by decide)).trans w38_364
    have w39_368 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K39.w32 (by decide) (by decide)).trans w38_368
    have w39_36c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K39.w32 (by decide) (by decide)).trans w38_36c
    have w39_370 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K39.w32 (by decide) (by decide)).trans w38_370
    have w39_374 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := (K39.w32 (by decide) (by decide)).trans w38_374
    have w39_420 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := (K39.w32 (by decide) (by decide)).trans w38_420
    have w39_424 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := (K39.w32 (by decide) (by decide)).trans w38_424
    have w39_428 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := (K39.w32 (by decide) (by decide)).trans w38_428
    have w39_42c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := (K39.w32 (by decide) (by decide)).trans w38_42c
    have b39_430 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := (K39.b8 (by decide) (by decide)).trans b38_430
    clear b38_430 w38_42c w38_428 w38_424 w38_420 w38_37c w38_378 w38_374 w38_370 w38_36c w38_368 w38_364 w38_360 w38_32c w38_328 w38_78 w38_74 w38_4c w38_48 g38_10 g38_27 g38_26 g38_25 g38_24 g38_23 g38_22 g38_21 g38_20 g38_19 g38_18 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 rb38 s38 m38 u38 c38
    -- 0xE30
    obtain ⟨n40, c40, u40⟩ := s39.block svTr6e30 E39.self svTr6e30_end
      ⟨trivial, trivial⟩
    have m40 : n40.mem = n39.mem := u40.mem
    have s40 : St n40.mem SV n40 0xE32 (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
    have rb40 : ∀ q, reg n40 q = (runBlock svTr6e30 (n39.mem, reg n39)).2 q := fun q => by rw [u40.regs]
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
    have g40_8 : reg n40 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb40, runBlock_reg _ _ _ (8 : Fin 32) s39.zero (by decide), g39_8]
    have g40_9 : reg n40 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
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
      rw [rb40]; simp +decide only [runBlock, BInstr.run, svTr6e30, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g39_2, g39_3, g39_4, g39_8, g39_9, g39_10, g39_18, g39_19, g39_20, g39_21, g39_22, g39_23, g39_24, g39_25, g39_26, g39_27, s39.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk40 : SvKeepL B n0.mem n40.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8)] := by rw [m40]; exact keep_kk39
    clear keep_kk39
    have w40_48 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m40]; exact w39_48
    have w40_4c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m40]; exact w39_4c
    have w40_74 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m40]; exact w39_74
    have w40_78 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m40]; exact w39_78
    have w40_328 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m40]; exact w39_328
    have w40_32c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m40]; exact w39_32c
    have w40_360 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m40]; exact w39_360
    have w40_364 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m40]; exact w39_364
    have w40_368 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m40]; exact w39_368
    have w40_36c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m40]; exact w39_36c
    have w40_370 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m40]; exact w39_370
    have w40_374 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m40]; exact w39_374
    have w40_420 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by rw [m40]; exact w39_420
    have w40_424 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := by rw [m40]; exact w39_424
    have w40_428 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m40]; exact w39_428
    have w40_42c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m40]; exact w39_42c
    have b40_430 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := by rw [m40]; exact b39_430
    clear b39_430 w39_42c w39_428 w39_424 w39_420 w39_374 w39_370 w39_36c w39_368 w39_364 w39_360 w39_32c w39_328 w39_78 w39_74 w39_4c w39_48 g39_10 a1_39 a0_39
    -- 0xE32: branch, not taken
    obtain ⟨n41, d41, u41⟩ := s40.notTaken E40.self 0xE34 sv_at_e32
      (by decide) (by rw [g40_10, s40.zero]; decide)
    have s41 : St n41.mem SV n41 0xE34 (reg n41) := ⟨u41.pc, rfl, fun _ => rfl⟩
    have m41 : n41.mem = n40.mem := u41.mem
    have fr41 : ∀ x, SvR B x → n41.mem x = n40.mem x := fun x _ => by rw [m41]
    have t41 : Steps n0 n41 := t40.trans (.single d41)
    have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
    have E41 : SvCode n41.mem := E40.fr F fr41
    have V41 : SvSaves B n41.mem v := V40.same m41
    have g41_2 : reg n41 sp = B + 0x21A0 := by rw [u41.regs, g40_2]
    have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u41.regs, g40_3]
    have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u41.regs, g40_4]
    have g41_8 : reg n41 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u41.regs, g40_8]
    have g41_9 : reg n41 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u41.regs, g40_9]
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
    have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8)] := by rw [m41]; exact keep_kk40
    clear keep_kk40
    have w41_48 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m41]; exact w40_48
    have w41_4c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m41]; exact w40_4c
    have w41_74 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m41]; exact w40_74
    have w41_78 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m41]; exact w40_78
    have w41_328 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m41]; exact w40_328
    have w41_32c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m41]; exact w40_32c
    have w41_360 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m41]; exact w40_360
    have w41_364 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m41]; exact w40_364
    have w41_368 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m41]; exact w40_368
    have w41_36c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m41]; exact w40_36c
    have w41_370 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m41]; exact w40_370
    have w41_374 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m41]; exact w40_374
    have w41_420 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by rw [m41]; exact w40_420
    have w41_424 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := by rw [m41]; exact w40_424
    have w41_428 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m41]; exact w40_428
    have w41_42c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m41]; exact w40_42c
    have b41_430 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := by rw [m41]; exact b40_430
    clear b40_430 w40_42c w40_428 w40_424 w40_420 w40_374 w40_370 w40_36c w40_368 w40_364 w40_360 w40_32c w40_328 w40_78 w40_74 w40_4c w40_48 g40_10 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_9 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 rb40 s40 m40 u40 c40
    -- 0xE34
    obtain ⟨n42, c42, u42⟩ := s41.block svTr6e34 E41.self svTr6e34_end
      ⟨trivial, trivial⟩
    have m42 : n42.mem = n41.mem := u42.mem
    have s42 : St n42.mem SV n42 0xE36 (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
    have rb42 : ∀ q, reg n42 q = (runBlock svTr6e34 (n41.mem, reg n41)).2 q := fun q => by rw [u42.regs]
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
    have g42_9 : reg n42 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
      rw [rb42, runBlock_reg _ _ _ (9 : Fin 32) s41.zero (by decide), g41_9]
    have g42_10 : reg n42 a0 = BitVec.ofNat 32 0x1 := by
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
    have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8)] := by rw [m42]; exact keep_kk41
    clear keep_kk41
    have w42_48 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m42]; exact w41_48
    have w42_4c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m42]; exact w41_4c
    have w42_74 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m42]; exact w41_74
    have w42_78 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m42]; exact w41_78
    have w42_328 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m42]; exact w41_328
    have w42_32c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m42]; exact w41_32c
    have w42_360 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m42]; exact w41_360
    have w42_364 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m42]; exact w41_364
    have w42_368 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m42]; exact w41_368
    have w42_36c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m42]; exact w41_36c
    have w42_370 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m42]; exact w41_370
    have w42_374 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m42]; exact w41_374
    have w42_420 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by rw [m42]; exact w41_420
    have w42_424 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := by rw [m42]; exact w41_424
    have w42_428 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m42]; exact w41_428
    have w42_42c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m42]; exact w41_42c
    have b42_430 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := by rw [m42]; exact b41_430
    clear b41_430 w41_42c w41_428 w41_424 w41_420 w41_374 w41_370 w41_36c w41_368 w41_364 w41_360 w41_32c w41_328 w41_78 w41_74 w41_4c w41_48 g41_27 g41_26 g41_25 g41_24 g41_23 g41_22 g41_21 g41_20 g41_19 g41_18 g41_10 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 fr41 m41 s41 u41 d41
    -- 0xE36: j
    obtain ⟨n43, d43, u43⟩ := s42.jump E42.self sv_at_e36 (off' := 0x7A4) (by decide)
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
    have g43_9 : reg n43 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u43.regs, g42_9]
    have g43_10 : reg n43 a0 = BitVec.ofNat 32 0x1 := by rw [u43.regs, g42_10]
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
    have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8)] := by rw [m43]; exact keep_kk42
    clear keep_kk42
    have w43_48 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m43]; exact w42_48
    have w43_4c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m43]; exact w42_4c
    have w43_74 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m43]; exact w42_74
    have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m43]; exact w42_78
    have w43_328 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m43]; exact w42_328
    have w43_32c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m43]; exact w42_32c
    have w43_360 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m43]; exact w42_360
    have w43_364 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m43]; exact w42_364
    have w43_368 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m43]; exact w42_368
    have w43_36c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m43]; exact w42_36c
    have w43_370 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m43]; exact w42_370
    have w43_374 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m43]; exact w42_374
    have w43_420 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by rw [m43]; exact w42_420
    have w43_424 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := by rw [m43]; exact w42_424
    have w43_428 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m43]; exact w42_428
    have w43_42c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m43]; exact w42_42c
    have b43_430 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := by rw [m43]; exact b42_430
    clear b42_430 w42_42c w42_428 w42_424 w42_420 w42_374 w42_370 w42_36c w42_368 w42_364 w42_360 w42_32c w42_328 w42_78 w42_74 w42_4c w42_48 g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_10 g42_9 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
    exact .inl ⟨(fun ⟨tl2', h0', h1', tl13', h2', h3', h4', te25', h5', tl31', h6', h7', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr13] at h2'; cases h2'; rw [hr25] at h4'; cases h4'; rw [hte25] at h5'; cases h5'; rw [hr31] at h6'; cases h6'; rw [hr39] at h7'; cases h7'), sv_fail F E43 s43 t43 (fun x hx => (fR43 x hx).trans (fM x hx).symm) V43 hret g43_2 g43_18 hO g43_3 g43_4⟩
  · rw [hr39] at R39
    obtain ⟨a0_39, a1_39⟩ := R39
    have g39_10 : reg n39 a0 = BitVec.ofNat 32 0x0 := a0_39
    have g39_11 : reg n39 a1 = BitVec.ofNat 32 0x0 := by rw [a1_39]; rfl
    have keep_kk39 : SvKeepL B n0.mem n39.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8)] := keep_kk38.trans K39
    clear keep_kk38
    have w39_48 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := (K39.w32 (by decide) (by decide)).trans w38_48
    have w39_4c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := (K39.w32 (by decide) (by decide)).trans w38_4c
    have w39_74 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K39.w32 (by decide) (by decide)).trans w38_74
    have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K39.w32 (by decide) (by decide)).trans w38_78
    have w39_328 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K39.w32 (by decide) (by decide)).trans w38_328
    have w39_32c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K39.w32 (by decide) (by decide)).trans w38_32c
    have w39_360 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := (K39.w32 (by decide) (by decide)).trans w38_360
    have w39_364 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := (K39.w32 (by decide) (by decide)).trans w38_364
    have w39_368 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K39.w32 (by decide) (by decide)).trans w38_368
    have w39_36c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K39.w32 (by decide) (by decide)).trans w38_36c
    have w39_370 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K39.w32 (by decide) (by decide)).trans w38_370
    have w39_374 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := (K39.w32 (by decide) (by decide)).trans w38_374
    have w39_420 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := (K39.w32 (by decide) (by decide)).trans w38_420
    have w39_424 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := (K39.w32 (by decide) (by decide)).trans w38_424
    have w39_428 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := (K39.w32 (by decide) (by decide)).trans w38_428
    have w39_42c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := (K39.w32 (by decide) (by decide)).trans w38_42c
    have b39_430 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := (K39.b8 (by decide) (by decide)).trans b38_430
    clear b38_430 w38_42c w38_428 w38_424 w38_420 w38_37c w38_378 w38_374 w38_370 w38_36c w38_368 w38_364 w38_360 w38_32c w38_328 w38_78 w38_74 w38_4c w38_48 g38_10 g38_27 g38_26 g38_25 g38_24 g38_23 g38_22 g38_21 g38_20 g38_19 g38_18 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 rb38 s38 m38 u38 c38
    -- 0xE30
    obtain ⟨n40, c40, u40⟩ := s39.block svTr6e30 E39.self svTr6e30_end
      ⟨trivial, trivial⟩
    have m40 : n40.mem = n39.mem := u40.mem
    have s40 : St n40.mem SV n40 0xE32 (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
    have rb40 : ∀ q, reg n40 q = (runBlock svTr6e30 (n39.mem, reg n39)).2 q := fun q => by rw [u40.regs]
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
    have g40_8 : reg n40 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb40, runBlock_reg _ _ _ (8 : Fin 32) s39.zero (by decide), g39_8]
    have g40_9 : reg n40 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
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
    have g40_10 : reg n40 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb40]; simp +decide only [runBlock, BInstr.run, svTr6e30, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g39_2, g39_3, g39_4, g39_8, g39_9, g39_10, g39_11, g39_18, g39_19, g39_20, g39_21, g39_22, g39_23, g39_24, g39_25, g39_26, g39_27, s39.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk40 : SvKeepL B n0.mem n40.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8)] := by rw [m40]; exact keep_kk39
    clear keep_kk39
    have w40_48 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m40]; exact w39_48
    have w40_4c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m40]; exact w39_4c
    have w40_74 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m40]; exact w39_74
    have w40_78 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m40]; exact w39_78
    have w40_328 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m40]; exact w39_328
    have w40_32c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m40]; exact w39_32c
    have w40_360 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m40]; exact w39_360
    have w40_364 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m40]; exact w39_364
    have w40_368 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m40]; exact w39_368
    have w40_36c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m40]; exact w39_36c
    have w40_370 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m40]; exact w39_370
    have w40_374 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m40]; exact w39_374
    have w40_420 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by rw [m40]; exact w39_420
    have w40_424 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := by rw [m40]; exact w39_424
    have w40_428 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m40]; exact w39_428
    have w40_42c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m40]; exact w39_42c
    have b40_430 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := by rw [m40]; exact b39_430
    clear b39_430 w39_42c w39_428 w39_424 w39_420 w39_374 w39_370 w39_36c w39_368 w39_364 w39_360 w39_32c w39_328 w39_78 w39_74 w39_4c w39_48 g39_11 g39_10 a1_39 a0_39
    -- 0xE32: branch, taken
    obtain ⟨n41, d41, u41⟩ := s40.taken E40.self 0xE54 sv_at_e32
      (by decide) (by rw [g40_10, s40.zero]; decide)
    have s41 : St n41.mem SV n41 0xE54 (reg n41) := ⟨u41.pc, rfl, fun _ => rfl⟩
    have m41 : n41.mem = n40.mem := u41.mem
    have fr41 : ∀ x, SvR B x → n41.mem x = n40.mem x := fun x _ => by rw [m41]
    have t41 : Steps n0 n41 := t40.trans (.single d41)
    have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
    have E41 : SvCode n41.mem := E40.fr F fr41
    have V41 : SvSaves B n41.mem v := V40.same m41
    have g41_2 : reg n41 sp = B + 0x21A0 := by rw [u41.regs, g40_2]
    have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u41.regs, g40_3]
    have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u41.regs, g40_4]
    have g41_8 : reg n41 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u41.regs, g40_8]
    have g41_9 : reg n41 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u41.regs, g40_9]
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
    have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8)] := by rw [m41]; exact keep_kk40
    clear keep_kk40
    have w41_48 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m41]; exact w40_48
    have w41_4c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m41]; exact w40_4c
    have w41_74 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m41]; exact w40_74
    have w41_78 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m41]; exact w40_78
    have w41_328 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m41]; exact w40_328
    have w41_32c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m41]; exact w40_32c
    have w41_360 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m41]; exact w40_360
    have w41_364 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m41]; exact w40_364
    have w41_368 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m41]; exact w40_368
    have w41_36c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m41]; exact w40_36c
    have w41_370 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m41]; exact w40_370
    have w41_374 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m41]; exact w40_374
    have w41_420 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by rw [m41]; exact w40_420
    have w41_424 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := by rw [m41]; exact w40_424
    have w41_428 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m41]; exact w40_428
    have w41_42c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m41]; exact w40_42c
    have b41_430 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := by rw [m41]; exact b40_430
    clear b40_430 w40_42c w40_428 w40_424 w40_420 w40_374 w40_370 w40_36c w40_368 w40_364 w40_360 w40_32c w40_328 w40_78 w40_74 w40_4c w40_48 g40_10 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_11 g40_9 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 rb40 s40 m40 u40 c40
    -- 0xE54
    obtain ⟨n42, c42, u42⟩ := s41.block svTr6e54 E41.self svTr6e54_end
      ⟨trivial, trivial⟩
    have m42 : n42.mem = n41.mem := u42.mem
    have s42 : St n42.mem SV n42 0xE56 (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
    have rb42 : ∀ q, reg n42 q = (runBlock svTr6e54 (n41.mem, reg n41)).2 q := fun q => by rw [u42.regs]
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
    have g42_8 : reg n42 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
      rw [rb42, runBlock_reg _ _ _ (8 : Fin 32) s41.zero (by decide), g41_8]
    have g42_9 : reg n42 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
      rw [rb42, runBlock_reg _ _ _ (9 : Fin 32) s41.zero (by decide), g41_9]
    have g42_10 : reg n42 a0 = BitVec.ofNat 32 0x0 := by
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
    have g42_11 : reg n42 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb42]; simp +decide only [runBlock, BInstr.run, svTr6e54, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_11, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8)] := by rw [m42]; exact keep_kk41
    clear keep_kk41
    have w42_48 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m42]; exact w41_48
    have w42_4c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m42]; exact w41_4c
    have w42_74 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m42]; exact w41_74
    have w42_78 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m42]; exact w41_78
    have w42_328 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m42]; exact w41_328
    have w42_32c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m42]; exact w41_32c
    have w42_360 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m42]; exact w41_360
    have w42_364 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m42]; exact w41_364
    have w42_368 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m42]; exact w41_368
    have w42_36c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m42]; exact w41_36c
    have w42_370 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m42]; exact w41_370
    have w42_374 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m42]; exact w41_374
    have w42_420 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by rw [m42]; exact w41_420
    have w42_424 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := by rw [m42]; exact w41_424
    have w42_428 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m42]; exact w41_428
    have w42_42c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m42]; exact w41_42c
    have b42_430 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := by rw [m42]; exact b41_430
    clear b41_430 w41_42c w41_428 w41_424 w41_420 w41_374 w41_370 w41_36c w41_368 w41_364 w41_360 w41_32c w41_328 w41_78 w41_74 w41_4c w41_48 g41_27 g41_26 g41_25 g41_24 g41_23 g41_22 g41_21 g41_20 g41_19 g41_18 g41_11 g41_10 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 fr41 m41 s41 u41 d41
    -- 0xE56: branch, taken
    obtain ⟨n43, d43, u43⟩ := s42.taken E42.self 0x7A4 sv_at_e56
      (by decide) (by rw [g42_11, s42.zero]; decide)
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
    have g43_9 : reg n43 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u43.regs, g42_9]
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
    have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8)] := by rw [m43]; exact keep_kk42
    clear keep_kk42
    have w43_48 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m43]; exact w42_48
    have w43_4c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m43]; exact w42_4c
    have w43_74 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m43]; exact w42_74
    have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m43]; exact w42_78
    have w43_328 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m43]; exact w42_328
    have w43_32c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m43]; exact w42_32c
    have w43_360 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m43]; exact w42_360
    have w43_364 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m43]; exact w42_364
    have w43_368 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m43]; exact w42_368
    have w43_36c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m43]; exact w42_36c
    have w43_370 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m43]; exact w42_370
    have w43_374 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m43]; exact w42_374
    have w43_420 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by rw [m43]; exact w42_420
    have w43_424 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := by rw [m43]; exact w42_424
    have w43_428 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m43]; exact w42_428
    have w43_42c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m43]; exact w42_42c
    have b43_430 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := by rw [m43]; exact b42_430
    clear b42_430 w42_42c w42_428 w42_424 w42_420 w42_374 w42_370 w42_36c w42_368 w42_364 w42_360 w42_32c w42_328 w42_78 w42_74 w42_4c w42_48 g42_11 g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_10 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
    exact .inl ⟨(fun ⟨tl2', h0', h1', tl13', h2', h3', h4', te25', h5', tl31', h6', h7', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr13] at h2'; cases h2'; rw [hr25] at h4'; cases h4'; rw [hte25] at h5'; cases h5'; rw [hr31] at h6'; cases h6'; rw [hr39] at h7'; cases h7'), sv_fail F E43 s43 t43 (fun x hx => (fR43 x hx).trans (fM x hx).symm) V43 hret g43_2 g43_18 hO g43_3 g43_4⟩
  obtain ⟨te39, hte39⟩ := isSha256Of_ok_elem hr39
  obtain ⟨d8_39, d12_39⟩ := A39 te39 hte39
  rw [hr39] at R39
  obtain ⟨a0_39, a1_39⟩ := R39
  have g39_10 : reg n39 a0 = BitVec.ofNat 32 0x0 := a0_39
  have g39_11 : reg n39 a1 = BitVec.ofNat 32 0x1 := by rw [a1_39]; rfl
  have keep_kk39 : SvKeepL B n0.mem n39.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8)] := keep_kk38.trans K39
  clear keep_kk38
  have w39_48 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := (K39.w32 (by decide) (by decide)).trans w38_48
  have w39_4c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := (K39.w32 (by decide) (by decide)).trans w38_4c
  have w39_74 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K39.w32 (by decide) (by decide)).trans w38_74
  have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K39.w32 (by decide) (by decide)).trans w38_78
  have w39_328 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K39.w32 (by decide) (by decide)).trans w38_328
  have w39_32c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K39.w32 (by decide) (by decide)).trans w38_32c
  have w39_360 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := (K39.w32 (by decide) (by decide)).trans w38_360
  have w39_364 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := (K39.w32 (by decide) (by decide)).trans w38_364
  have w39_368 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K39.w32 (by decide) (by decide)).trans w38_368
  have w39_36c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K39.w32 (by decide) (by decide)).trans w38_36c
  have w39_370 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K39.w32 (by decide) (by decide)).trans w38_370
  have w39_374 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := (K39.w32 (by decide) (by decide)).trans w38_374
  have w39_420 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := (K39.w32 (by decide) (by decide)).trans w38_420
  have w39_424 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := (K39.w32 (by decide) (by decide)).trans w38_424
  have w39_428 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := (K39.w32 (by decide) (by decide)).trans w38_428
  have w39_42c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := (K39.w32 (by decide) (by decide)).trans w38_42c
  have b39_430 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := (K39.b8 (by decide) (by decide)).trans b38_430
  have w39_378 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len) := d8_39
  have w39_37c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)) - BitVec.ofNat 32 (te39.header + te39.len) := d12_39
  clear b38_430 w38_42c w38_428 w38_424 w38_420 w38_37c w38_378 w38_374 w38_370 w38_36c w38_368 w38_364 w38_360 w38_32c w38_328 w38_78 w38_74 w38_4c w38_48 g38_10 g38_27 g38_26 g38_25 g38_24 g38_23 g38_22 g38_21 g38_20 g38_19 g38_18 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 rb38 s38 m38 u38 c38
  -- 0xE30
  obtain ⟨n40, c40, u40⟩ := s39.block svTr6e30 E39.self svTr6e30_end
    ⟨trivial, trivial⟩
  have m40 : n40.mem = n39.mem := u40.mem
  have s40 : St n40.mem SV n40 0xE32 (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
  have rb40 : ∀ q, reg n40 q = (runBlock svTr6e30 (n39.mem, reg n39)).2 q := fun q => by rw [u40.regs]
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
  have g40_8 : reg n40 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb40, runBlock_reg _ _ _ (8 : Fin 32) s39.zero (by decide), g39_8]
  have g40_9 : reg n40 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
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
  have g40_10 : reg n40 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb40]; simp +decide only [runBlock, BInstr.run, svTr6e30, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g39_2, g39_3, g39_4, g39_8, g39_9, g39_10, g39_11, g39_18, g39_19, g39_20, g39_21, g39_22, g39_23, g39_24, g39_25, g39_26, g39_27, s39.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk40 : SvKeepL B n0.mem n40.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8)] := by rw [m40]; exact keep_kk39
  clear keep_kk39
  have w40_48 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m40]; exact w39_48
  have w40_4c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m40]; exact w39_4c
  have w40_74 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m40]; exact w39_74
  have w40_78 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m40]; exact w39_78
  have w40_328 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m40]; exact w39_328
  have w40_32c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m40]; exact w39_32c
  have w40_360 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m40]; exact w39_360
  have w40_364 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m40]; exact w39_364
  have w40_368 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m40]; exact w39_368
  have w40_36c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m40]; exact w39_36c
  have w40_370 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m40]; exact w39_370
  have w40_374 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m40]; exact w39_374
  have w40_378 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len) := by rw [m40]; exact w39_378
  have w40_37c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)) - BitVec.ofNat 32 (te39.header + te39.len) := by rw [m40]; exact w39_37c
  have w40_420 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by rw [m40]; exact w39_420
  have w40_424 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := by rw [m40]; exact w39_424
  have w40_428 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m40]; exact w39_428
  have w40_42c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m40]; exact w39_42c
  have b40_430 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := by rw [m40]; exact b39_430
  clear w39_37c w39_378 b39_430 w39_42c w39_428 w39_424 w39_420 w39_374 w39_370 w39_36c w39_368 w39_364 w39_360 w39_32c w39_328 w39_78 w39_74 w39_4c w39_48 g39_11 g39_10 a1_39 a0_39 d12_39 d8_39 g39_2 g39_27 g39_26 g39_25 g39_24 g39_23 g39_22 g39_21 g39_20 g39_19 g39_18 g39_9 g39_8 g39_4 g39_3 V39 E39 fR39 t39 fr39 A39 K39 rk39 sp39 s39 c39
  -- 0xE32: branch, taken
  obtain ⟨n41, d41, u41⟩ := s40.taken E40.self 0xE54 sv_at_e32
    (by decide) (by rw [g40_10, s40.zero]; decide)
  have s41 : St n41.mem SV n41 0xE54 (reg n41) := ⟨u41.pc, rfl, fun _ => rfl⟩
  have m41 : n41.mem = n40.mem := u41.mem
  have fr41 : ∀ x, SvR B x → n41.mem x = n40.mem x := fun x _ => by rw [m41]
  have t41 : Steps n0 n41 := t40.trans (.single d41)
  have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
  have E41 : SvCode n41.mem := E40.fr F fr41
  have V41 : SvSaves B n41.mem v := V40.same m41
  have g41_2 : reg n41 sp = B + 0x21A0 := by rw [u41.regs, g40_2]
  have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u41.regs, g40_3]
  have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u41.regs, g40_4]
  have g41_8 : reg n41 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [u41.regs, g40_8]
  have g41_9 : reg n41 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u41.regs, g40_9]
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
  have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8)] := by rw [m41]; exact keep_kk40
  clear keep_kk40
  have w41_48 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m41]; exact w40_48
  have w41_4c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m41]; exact w40_4c
  have w41_74 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m41]; exact w40_74
  have w41_78 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m41]; exact w40_78
  have w41_328 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m41]; exact w40_328
  have w41_32c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m41]; exact w40_32c
  have w41_360 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m41]; exact w40_360
  have w41_364 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m41]; exact w40_364
  have w41_368 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m41]; exact w40_368
  have w41_36c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m41]; exact w40_36c
  have w41_370 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m41]; exact w40_370
  have w41_374 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m41]; exact w40_374
  have w41_378 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len) := by rw [m41]; exact w40_378
  have w41_37c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)) - BitVec.ofNat 32 (te39.header + te39.len) := by rw [m41]; exact w40_37c
  have w41_420 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by rw [m41]; exact w40_420
  have w41_424 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := by rw [m41]; exact w40_424
  have w41_428 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m41]; exact w40_428
  have w41_42c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m41]; exact w40_42c
  have b41_430 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := by rw [m41]; exact b40_430
  clear b40_430 w40_42c w40_428 w40_424 w40_420 w40_37c w40_378 w40_374 w40_370 w40_36c w40_368 w40_364 w40_360 w40_32c w40_328 w40_78 w40_74 w40_4c w40_48 g40_10 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_11 g40_9 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 rb40 s40 m40 u40 c40
  -- 0xE54
  obtain ⟨n42, c42, u42⟩ := s41.block svTr6e54 E41.self svTr6e54_end
    ⟨trivial, trivial⟩
  have m42 : n42.mem = n41.mem := u42.mem
  have s42 : St n42.mem SV n42 0xE56 (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
  have rb42 : ∀ q, reg n42 q = (runBlock svTr6e54 (n41.mem, reg n41)).2 q := fun q => by rw [u42.regs]
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
  have g42_8 : reg n42 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by
    rw [rb42, runBlock_reg _ _ _ (8 : Fin 32) s41.zero (by decide), g41_8]
  have g42_9 : reg n42 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
    rw [rb42, runBlock_reg _ _ _ (9 : Fin 32) s41.zero (by decide), g41_9]
  have g42_10 : reg n42 a0 = BitVec.ofNat 32 0x0 := by
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
  have g42_11 : reg n42 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb42]; simp +decide only [runBlock, BInstr.run, svTr6e54, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_11, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8)] := by rw [m42]; exact keep_kk41
  clear keep_kk41
  have w42_48 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m42]; exact w41_48
  have w42_4c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m42]; exact w41_4c
  have w42_74 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m42]; exact w41_74
  have w42_78 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m42]; exact w41_78
  have w42_328 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m42]; exact w41_328
  have w42_32c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m42]; exact w41_32c
  have w42_360 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m42]; exact w41_360
  have w42_364 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m42]; exact w41_364
  have w42_368 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m42]; exact w41_368
  have w42_36c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m42]; exact w41_36c
  have w42_370 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m42]; exact w41_370
  have w42_374 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m42]; exact w41_374
  have w42_378 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len) := by rw [m42]; exact w41_378
  have w42_37c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)) - BitVec.ofNat 32 (te39.header + te39.len) := by rw [m42]; exact w41_37c
  have w42_420 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by rw [m42]; exact w41_420
  have w42_424 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := by rw [m42]; exact w41_424
  have w42_428 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m42]; exact w41_428
  have w42_42c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m42]; exact w41_42c
  have b42_430 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := by rw [m42]; exact b41_430
  clear b41_430 w41_42c w41_428 w41_424 w41_420 w41_37c w41_378 w41_374 w41_370 w41_36c w41_368 w41_364 w41_360 w41_32c w41_328 w41_78 w41_74 w41_4c w41_48 g41_27 g41_26 g41_25 g41_24 g41_23 g41_22 g41_21 g41_20 g41_19 g41_18 g41_11 g41_10 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 fr41 m41 s41 u41 d41
  -- 0xE56: branch, not taken
  obtain ⟨n43, d43, u43⟩ := s42.notTaken E42.self 0xE5A sv_at_e56
    (by decide) (by rw [g42_11, s42.zero]; decide)
  have s43 : St n43.mem SV n43 0xE5A (reg n43) := ⟨u43.pc, rfl, fun _ => rfl⟩
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
  have g43_9 : reg n43 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u43.regs, g42_9]
  have g43_10 : reg n43 a0 = BitVec.ofNat 32 0x0 := by rw [u43.regs, g42_10]
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
  have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8)] := by rw [m43]; exact keep_kk42
  clear keep_kk42
  have w43_48 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m43]; exact w42_48
  have w43_4c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m43]; exact w42_4c
  have w43_74 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m43]; exact w42_74
  have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m43]; exact w42_78
  have w43_328 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m43]; exact w42_328
  have w43_32c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m43]; exact w42_32c
  have w43_360 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m43]; exact w42_360
  have w43_364 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m43]; exact w42_364
  have w43_368 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m43]; exact w42_368
  have w43_36c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m43]; exact w42_36c
  have w43_370 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m43]; exact w42_370
  have w43_374 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m43]; exact w42_374
  have w43_378 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len) := by rw [m43]; exact w42_378
  have w43_37c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)) - BitVec.ofNat 32 (te39.header + te39.len) := by rw [m43]; exact w42_37c
  have w43_420 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by rw [m43]; exact w42_420
  have w43_424 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := by rw [m43]; exact w42_424
  have w43_428 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m43]; exact w42_428
  have w43_42c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m43]; exact w42_42c
  have b43_430 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := by rw [m43]; exact b42_430
  clear b42_430 w42_42c w42_428 w42_424 w42_420 w42_37c w42_378 w42_374 w42_370 w42_36c w42_368 w42_364 w42_360 w42_32c w42_328 w42_78 w42_74 w42_4c w42_48 g42_11 g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_10 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
  -- 0xE5A
  obtain ⟨n44, c44, u44⟩ := s43.block svTr6e5a E43.self svTr6e5a_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m44 : n44.mem = n43.mem := u44.mem
  have s44 : St n44.mem SV n44 0xE64 (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
  have rb44 : ∀ q, reg n44 q = (runBlock svTr6e5a (n43.mem, reg n43)).2 q := fun q => by rw [u44.regs]
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
  have g44_9 : reg n44 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by
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
    rw [rb44]; simp +decide only [runBlock, BInstr.run, svTr6e5a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g44_11 : reg n44 a1 = B + 0x21A0 + BitVec.ofNat 32 0x370 := by
    rw [rb44]; simp +decide only [runBlock, BInstr.run, svTr6e5a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g44_12 : reg n44 a2 = BitVec.ofNat 32 0xA0 := by
    rw [rb44]; simp +decide only [runBlock, BInstr.run, svTr6e5a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk44 : SvKeepL B n0.mem n44.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8)] := by rw [m44]; exact keep_kk43
  clear keep_kk43
  have w44_48 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m44]; exact w43_48
  have w44_4c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m44]; exact w43_4c
  have w44_74 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m44]; exact w43_74
  have w44_78 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m44]; exact w43_78
  have w44_328 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m44]; exact w43_328
  have w44_32c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m44]; exact w43_32c
  have w44_360 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m44]; exact w43_360
  have w44_364 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m44]; exact w43_364
  have w44_368 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m44]; exact w43_368
  have w44_36c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m44]; exact w43_36c
  have w44_370 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m44]; exact w43_370
  have w44_374 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m44]; exact w43_374
  have w44_378 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len) := by rw [m44]; exact w43_378
  have w44_37c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)) - BitVec.ofNat 32 (te39.header + te39.len) := by rw [m44]; exact w43_37c
  have w44_420 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 tl31.header := by rw [m44]; exact w43_420
  have w44_424 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = BitVec.ofNat 32 tl31.len := by rw [m44]; exact w43_424
  have w44_428 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m44]; exact w43_428
  have w44_42c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m44]; exact w43_42c
  have b44_430 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 8 tl31.tag := by rw [m44]; exact b43_430
  clear b43_430 w43_42c w43_428 w43_424 w43_420 w43_37c w43_378 w43_374 w43_370 w43_36c w43_368 w43_364 w43_360 w43_32c w43_328 w43_78 w43_74 w43_4c w43_48 g43_27 g43_26 g43_25 g43_24 g43_23 g43_22 g43_21 g43_20 g43_19 g43_18 g43_11 g43_10 g43_9 g43_8 g43_4 g43_3 g43_2 V43 E43 fR43 t43 fr43 m43 s43 u43 d43
  -- 0xE64: sv_optF
  obtain ⟨n45, c45, s45, sp45, rk45, K45, R45, fr45⟩ := sv_optF (oc := 0x420) (dc := 0x370) (tag := 0xA0)
    F E44 s44 sv_at_e64 sv_at_e68 (by decide) (by decide) g44_2 g44_10 g44_11 g44_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w44_378 w44_37c (((((sd_in.contentW hr2).contentW hr13).restW hte25).restW hr31).restW hte39)
  have t45 : Steps n0 n45 := t44.trans c45
  have fR45 : ∀ x, SvR B x → n45.mem x = M0 x := fun x hx => (fr45 x hx).trans (fR44 x hx)
  have E45 : SvCode n45.mem := E44.fr F fr45
  have V45 : SvSaves B n45.mem v := V44.keepL K45 (by decide)
  rw [sv_mb fR44 (((((sd_in.contentW hr2).contentW hr13).restW hte25).restW hr31).restW hte39)] at R45
  have g45_2 : reg n45 sp = B + 0x21A0 := by rw [rk45 sp (by decide) (by decide), g44_2]
  have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk45 (3 : Fin 32) (by decide) (by decide), g44_3]
  have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk45 (4 : Fin 32) (by decide) (by decide), g44_4]
  have g45_8 : reg n45 (8 : Fin 32) = BitVec.ofNat 32 0x18 := by rw [rk45 (8 : Fin 32) (by decide) (by decide), g44_8]
  have g45_9 : reg n45 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [rk45 (9 : Fin 32) (by decide) (by decide), g44_9]
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
  obtain ⟨r45, hr45⟩ : ∃ r, derOptRes 0xA0 (memBytes M0 ((((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len)) ((((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)) - BitVec.ofNat 32 (te39.header + te39.len)).toNat) = r := ⟨_, rfl⟩
  rcases r45 with _ | (er45 | tl45)
  · rw [hr45] at R45
    obtain ⟨y0_45, y4_45⟩ := R45
    have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8), (0x420, 0x18), (0x378, 0x8)] := keep_kk44.trans K45
    clear keep_kk44
    have w45_48 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := (K45.w32 (by decide) (by decide)).trans w44_48
    have w45_4c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := (K45.w32 (by decide) (by decide)).trans w44_4c
    have w45_74 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K45.w32 (by decide) (by decide)).trans w44_74
    have w45_78 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K45.w32 (by decide) (by decide)).trans w44_78
    have w45_328 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K45.w32 (by decide) (by decide)).trans w44_328
    have w45_32c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K45.w32 (by decide) (by decide)).trans w44_32c
    have w45_360 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := (K45.w32 (by decide) (by decide)).trans w44_360
    have w45_364 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := (K45.w32 (by decide) (by decide)).trans w44_364
    have w45_368 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K45.w32 (by decide) (by decide)).trans w44_368
    have w45_36c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K45.w32 (by decide) (by decide)).trans w44_36c
    have w45_370 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K45.w32 (by decide) (by decide)).trans w44_370
    have w45_374 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := (K45.w32 (by decide) (by decide)).trans w44_374
    have w45_424 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = 0 := y4_45
    have b45_420 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := y0_45
    clear b44_430 w44_42c w44_428 w44_424 w44_420 w44_37c w44_378 w44_374 w44_370 w44_36c w44_368 w44_364 w44_360 w44_32c w44_328 w44_78 w44_74 w44_4c w44_48 g44_12 g44_11 g44_10 g44_27 g44_26 g44_25 g44_24 g44_23 g44_22 g44_21 g44_20 g44_19 g44_18 g44_9 g44_8 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 rb44 s44 m44 u44 c44
    -- 0xE6C: lbu
    obtain ⟨n46, d46, u46⟩ := s45.lbu E45.self sv_at_e6c (off' := 0xE70) (by decide)
    have s46 : St n46.mem SV n46 0xE70 (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
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
    have g46_9 : reg n46 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u46.regs, upd_ne (by decide) (by decide), g45_9]
    have g46_18 : reg n46 (18 : Fin 32) = out := by rw [u46.regs, upd_ne (by decide) (by decide), g45_18]
    have g46_19 : reg n46 (19 : Fin 32) = bp := by rw [u46.regs, upd_ne (by decide) (by decide), g45_19]
    have g46_20 : reg n46 (20 : Fin 32) = x20 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_20]
    have g46_21 : reg n46 (21 : Fin 32) = x21 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_21]
    have g46_22 : reg n46 (22 : Fin 32) = x22 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_22]
    have g46_23 : reg n46 (23 : Fin 32) = x23 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_23]
    have g46_24 : reg n46 (24 : Fin 32) = x24 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_24]
    have g46_25 : reg n46 (25 : Fin 32) = x25 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_25]
    have g46_26 : reg n46 (26 : Fin 32) = x26 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_26]
    have g46_27 : reg n46 (27 : Fin 32) = x27 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_27]
    have g46_10 : reg n46 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
      rw [u46.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g45_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, b45_420]
    have keep_kk46 : SvKeepL B n0.mem n46.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8), (0x420, 0x18), (0x378, 0x8)] := by rw [m46]; exact keep_kk45
    clear keep_kk45
    have w46_48 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m46]; exact w45_48
    have w46_4c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m46]; exact w45_4c
    have w46_74 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m46]; exact w45_74
    have w46_78 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m46]; exact w45_78
    have w46_328 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m46]; exact w45_328
    have w46_32c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m46]; exact w45_32c
    have w46_360 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m46]; exact w45_360
    have w46_364 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m46]; exact w45_364
    have w46_368 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m46]; exact w45_368
    have w46_36c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m46]; exact w45_36c
    have w46_370 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m46]; exact w45_370
    have w46_374 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m46]; exact w45_374
    have w46_424 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = 0 := by rw [m46]; exact w45_424
    have b46_420 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m46]; exact b45_420
    clear b45_420 w45_424 w45_374 w45_370 w45_36c w45_368 w45_364 w45_360 w45_32c w45_328 w45_78 w45_74 w45_4c w45_48 y4_45 y0_45
    -- 0xE70: branch, not taken
    obtain ⟨n47, d47, u47⟩ := s46.notTaken E46.self 0xE74 sv_at_e70
      (by decide) (by rw [g46_10, s46.zero]; decide)
    have s47 : St n47.mem SV n47 0xE74 (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
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
    have g47_9 : reg n47 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u47.regs, g46_9]
    have g47_10 : reg n47 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u47.regs, g46_10]
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
    have keep_kk47 : SvKeepL B n0.mem n47.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8), (0x420, 0x18), (0x378, 0x8)] := by rw [m47]; exact keep_kk46
    clear keep_kk46
    have w47_48 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m47]; exact w46_48
    have w47_4c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m47]; exact w46_4c
    have w47_74 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m47]; exact w46_74
    have w47_78 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m47]; exact w46_78
    have w47_328 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m47]; exact w46_328
    have w47_32c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m47]; exact w46_32c
    have w47_360 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m47]; exact w46_360
    have w47_364 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m47]; exact w46_364
    have w47_368 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m47]; exact w46_368
    have w47_36c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m47]; exact w46_36c
    have w47_370 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m47]; exact w46_370
    have w47_374 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m47]; exact w46_374
    have w47_424 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = 0 := by rw [m47]; exact w46_424
    have b47_420 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m47]; exact b46_420
    clear b46_420 w46_424 w46_374 w46_370 w46_36c w46_368 w46_364 w46_360 w46_32c w46_328 w46_78 w46_74 w46_4c w46_48 g46_10 g46_27 g46_26 g46_25 g46_24 g46_23 g46_22 g46_21 g46_20 g46_19 g46_18 g46_9 g46_8 g46_4 g46_3 g46_2 V46 E46 fR46 t46 fr46 m46 s46 u46 d46
    -- 0xE74: lw
    obtain ⟨n48, d48, u48⟩ := s47.lw E47.self sv_at_e74 (off' := 0xE78) (by decide)
      (by rw [g47_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s48 : St n48.mem SV n48 0xE78 (reg n48) := ⟨u48.pc, rfl, fun _ => rfl⟩
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
    have g48_9 : reg n48 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u48.regs, upd_ne (by decide) (by decide), g47_9]
    have g48_18 : reg n48 (18 : Fin 32) = out := by rw [u48.regs, upd_ne (by decide) (by decide), g47_18]
    have g48_19 : reg n48 (19 : Fin 32) = bp := by rw [u48.regs, upd_ne (by decide) (by decide), g47_19]
    have g48_20 : reg n48 (20 : Fin 32) = x20 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_20]
    have g48_21 : reg n48 (21 : Fin 32) = x21 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_21]
    have g48_22 : reg n48 (22 : Fin 32) = x22 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_22]
    have g48_23 : reg n48 (23 : Fin 32) = x23 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_23]
    have g48_24 : reg n48 (24 : Fin 32) = x24 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_24]
    have g48_25 : reg n48 (25 : Fin 32) = x25 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_25]
    have g48_26 : reg n48 (26 : Fin 32) = x26 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_26]
    have g48_27 : reg n48 (27 : Fin 32) = x27 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_27]
    have g48_10 : reg n48 a0 = 0 := by
      rw [u48.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g47_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w47_424]
    have keep_kk48 : SvKeepL B n0.mem n48.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8), (0x420, 0x18), (0x378, 0x8)] := by rw [m48]; exact keep_kk47
    clear keep_kk47
    have w48_48 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m48]; exact w47_48
    have w48_4c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m48]; exact w47_4c
    have w48_74 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m48]; exact w47_74
    have w48_78 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m48]; exact w47_78
    have w48_328 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m48]; exact w47_328
    have w48_32c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m48]; exact w47_32c
    have w48_360 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m48]; exact w47_360
    have w48_364 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m48]; exact w47_364
    have w48_368 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m48]; exact w47_368
    have w48_36c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m48]; exact w47_36c
    have w48_370 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m48]; exact w47_370
    have w48_374 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m48]; exact w47_374
    have w48_424 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = 0 := by rw [m48]; exact w47_424
    have b48_420 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m48]; exact b47_420
    clear b47_420 w47_424 w47_374 w47_370 w47_36c w47_368 w47_364 w47_360 w47_32c w47_328 w47_78 w47_74 w47_4c w47_48 g47_27 g47_26 g47_25 g47_24 g47_23 g47_22 g47_21 g47_20 g47_19 g47_18 g47_10 g47_9 g47_8 g47_4 g47_3 g47_2 V47 E47 fR47 t47 fr47 m47 s47 u47 d47
    -- 0xE78: branch, taken
    obtain ⟨n49, d49, u49⟩ := s48.taken E48.self 0x7A4 sv_at_e78
      (by decide) (by rw [g48_10, s48.zero]; rfl)
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
    have g49_9 : reg n49 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u49.regs, g48_9]
    have g49_10 : reg n49 a0 = 0 := by rw [u49.regs, g48_10]
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
    have keep_kk49 : SvKeepL B n0.mem n49.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8), (0x420, 0x18), (0x378, 0x8)] := by rw [m49]; exact keep_kk48
    clear keep_kk48
    have w49_48 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m49]; exact w48_48
    have w49_4c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m49]; exact w48_4c
    have w49_74 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m49]; exact w48_74
    have w49_78 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m49]; exact w48_78
    have w49_328 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m49]; exact w48_328
    have w49_32c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m49]; exact w48_32c
    have w49_360 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m49]; exact w48_360
    have w49_364 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m49]; exact w48_364
    have w49_368 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m49]; exact w48_368
    have w49_36c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m49]; exact w48_36c
    have w49_370 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m49]; exact w48_370
    have w49_374 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m49]; exact w48_374
    have w49_424 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = 0 := by rw [m49]; exact w48_424
    have b49_420 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m49]; exact b48_420
    clear b48_420 w48_424 w48_374 w48_370 w48_36c w48_368 w48_364 w48_360 w48_32c w48_328 w48_78 w48_74 w48_4c w48_48 g48_10 g48_27 g48_26 g48_25 g48_24 g48_23 g48_22 g48_21 g48_20 g48_19 g48_18 g48_9 g48_8 g48_4 g48_3 g48_2 V48 E48 fR48 t48 fr48 m48 s48 u48 d48
    exact .inl ⟨(fun ⟨tl2', h0', h1', tl13', h2', h3', h4', te25', h5', tl31', h6', h7', te39', h8', tl45', h9', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr13] at h2'; cases h2'; rw [hr25] at h4'; cases h4'; rw [hte25] at h5'; cases h5'; rw [hr31] at h6'; cases h6'; rw [hr39] at h7'; cases h7'; rw [hte39] at h8'; cases h8'; rw [hr45] at h9'; cases h9'), sv_fail F E49 s49 t49 (fun x hx => (fR49 x hx).trans (fM x hx).symm) V49 hret g49_2 g49_18 hO g49_3 g49_4⟩
  · rw [hr45] at R45
    obtain ⟨y0_45, -⟩ := R45
    have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8), (0x420, 0x18), (0x378, 0x8)] := keep_kk44.trans K45
    clear keep_kk44
    have w45_48 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := (K45.w32 (by decide) (by decide)).trans w44_48
    have w45_4c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := (K45.w32 (by decide) (by decide)).trans w44_4c
    have w45_74 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K45.w32 (by decide) (by decide)).trans w44_74
    have w45_78 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K45.w32 (by decide) (by decide)).trans w44_78
    have w45_328 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K45.w32 (by decide) (by decide)).trans w44_328
    have w45_32c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K45.w32 (by decide) (by decide)).trans w44_32c
    have w45_360 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := (K45.w32 (by decide) (by decide)).trans w44_360
    have w45_364 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := (K45.w32 (by decide) (by decide)).trans w44_364
    have w45_368 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K45.w32 (by decide) (by decide)).trans w44_368
    have w45_36c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K45.w32 (by decide) (by decide)).trans w44_36c
    have w45_370 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K45.w32 (by decide) (by decide)).trans w44_370
    have w45_374 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := (K45.w32 (by decide) (by decide)).trans w44_374
    have b45_420 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := y0_45
    clear b44_430 w44_42c w44_428 w44_424 w44_420 w44_37c w44_378 w44_374 w44_370 w44_36c w44_368 w44_364 w44_360 w44_32c w44_328 w44_78 w44_74 w44_4c w44_48 g44_12 g44_11 g44_10 g44_27 g44_26 g44_25 g44_24 g44_23 g44_22 g44_21 g44_20 g44_19 g44_18 g44_9 g44_8 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 rb44 s44 m44 u44 c44
    -- 0xE6C: lbu
    obtain ⟨n46, d46, u46⟩ := s45.lbu E45.self sv_at_e6c (off' := 0xE70) (by decide)
    have s46 : St n46.mem SV n46 0xE70 (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
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
    have g46_9 : reg n46 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u46.regs, upd_ne (by decide) (by decide), g45_9]
    have g46_18 : reg n46 (18 : Fin 32) = out := by rw [u46.regs, upd_ne (by decide) (by decide), g45_18]
    have g46_19 : reg n46 (19 : Fin 32) = bp := by rw [u46.regs, upd_ne (by decide) (by decide), g45_19]
    have g46_20 : reg n46 (20 : Fin 32) = x20 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_20]
    have g46_21 : reg n46 (21 : Fin 32) = x21 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_21]
    have g46_22 : reg n46 (22 : Fin 32) = x22 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_22]
    have g46_23 : reg n46 (23 : Fin 32) = x23 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_23]
    have g46_24 : reg n46 (24 : Fin 32) = x24 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_24]
    have g46_25 : reg n46 (25 : Fin 32) = x25 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_25]
    have g46_26 : reg n46 (26 : Fin 32) = x26 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_26]
    have g46_27 : reg n46 (27 : Fin 32) = x27 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_27]
    have g46_10 : reg n46 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [u46.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g45_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, b45_420]
    have keep_kk46 : SvKeepL B n0.mem n46.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8), (0x420, 0x18), (0x378, 0x8)] := by rw [m46]; exact keep_kk45
    clear keep_kk45
    have w46_48 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m46]; exact w45_48
    have w46_4c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m46]; exact w45_4c
    have w46_74 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m46]; exact w45_74
    have w46_78 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m46]; exact w45_78
    have w46_328 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m46]; exact w45_328
    have w46_32c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m46]; exact w45_32c
    have w46_360 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m46]; exact w45_360
    have w46_364 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m46]; exact w45_364
    have w46_368 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m46]; exact w45_368
    have w46_36c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m46]; exact w45_36c
    have w46_370 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m46]; exact w45_370
    have w46_374 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m46]; exact w45_374
    have b46_420 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m46]; exact b45_420
    clear b45_420 w45_374 w45_370 w45_36c w45_368 w45_364 w45_360 w45_32c w45_328 w45_78 w45_74 w45_4c w45_48 y0_45
    -- 0xE70: branch, taken
    obtain ⟨n47, d47, u47⟩ := s46.taken E46.self 0x12A2 sv_at_e70
      (by decide) (by rw [g46_10, s46.zero]; decide)
    have s47 : St n47.mem SV n47 0x12A2 (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
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
    have g47_9 : reg n47 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u47.regs, g46_9]
    have g47_10 : reg n47 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u47.regs, g46_10]
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
    have keep_kk47 : SvKeepL B n0.mem n47.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8), (0x420, 0x18), (0x378, 0x8)] := by rw [m47]; exact keep_kk46
    clear keep_kk46
    have w47_48 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m47]; exact w46_48
    have w47_4c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m47]; exact w46_4c
    have w47_74 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m47]; exact w46_74
    have w47_78 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m47]; exact w46_78
    have w47_328 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m47]; exact w46_328
    have w47_32c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m47]; exact w46_32c
    have w47_360 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m47]; exact w46_360
    have w47_364 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m47]; exact w46_364
    have w47_368 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m47]; exact w46_368
    have w47_36c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m47]; exact w46_36c
    have w47_370 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m47]; exact w46_370
    have w47_374 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m47]; exact w46_374
    have b47_420 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m47]; exact b46_420
    clear b46_420 w46_374 w46_370 w46_36c w46_368 w46_364 w46_360 w46_32c w46_328 w46_78 w46_74 w46_4c w46_48 g46_10 g46_27 g46_26 g46_25 g46_24 g46_23 g46_22 g46_21 g46_20 g46_19 g46_18 g46_9 g46_8 g46_4 g46_3 g46_2 V46 E46 fR46 t46 fr46 m46 s46 u46 d46
    -- 0x12A2: lbu
    obtain ⟨n48, d48, u48⟩ := s47.lbu E47.self sv_at_12a2 (off' := 0x12A6) (by decide)
    have s48 : St n48.mem SV n48 0x12A6 (reg n48) := ⟨u48.pc, rfl, fun _ => rfl⟩
    have m48 : n48.mem = n47.mem := u48.mem
    have fr48 : ∀ x, SvR B x → n48.mem x = n47.mem x := fun x _ => by rw [m48]
    have t48 : Steps n0 n48 := t47.trans (.single d48)
    have fR48 : ∀ x, SvR B x → n48.mem x = M0 x := fun x hx => (fr48 x hx).trans (fR47 x hx)
    have E48 : SvCode n48.mem := E47.fr F fr48
    have V48 : SvSaves B n48.mem v := V47.same m48
    have g48_2 : reg n48 sp = B + 0x21A0 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_2]
    have g48_3 : reg n48 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u48.regs, upd_ne (by decide) (by decide), g47_3]
    have g48_4 : reg n48 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u48.regs, upd_ne (by decide) (by decide), g47_4]
    have g48_9 : reg n48 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u48.regs, upd_ne (by decide) (by decide), g47_9]
    have g48_10 : reg n48 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_10]
    have g48_18 : reg n48 (18 : Fin 32) = out := by rw [u48.regs, upd_ne (by decide) (by decide), g47_18]
    have g48_19 : reg n48 (19 : Fin 32) = bp := by rw [u48.regs, upd_ne (by decide) (by decide), g47_19]
    have g48_20 : reg n48 (20 : Fin 32) = x20 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_20]
    have g48_21 : reg n48 (21 : Fin 32) = x21 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_21]
    have g48_22 : reg n48 (22 : Fin 32) = x22 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_22]
    have g48_23 : reg n48 (23 : Fin 32) = x23 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_23]
    have g48_24 : reg n48 (24 : Fin 32) = x24 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_24]
    have g48_25 : reg n48 (25 : Fin 32) = x25 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_25]
    have g48_26 : reg n48 (26 : Fin 32) = x26 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_26]
    have g48_27 : reg n48 (27 : Fin 32) = x27 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_27]
    have keep_kk48 : SvKeepL B n0.mem n48.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8), (0x420, 0x18), (0x378, 0x8)] := by rw [m48]; exact keep_kk47
    clear keep_kk47
    have w48_48 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m48]; exact w47_48
    have w48_4c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m48]; exact w47_4c
    have w48_74 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m48]; exact w47_74
    have w48_78 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m48]; exact w47_78
    have w48_328 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m48]; exact w47_328
    have w48_32c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m48]; exact w47_32c
    have w48_360 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m48]; exact w47_360
    have w48_364 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m48]; exact w47_364
    have w48_368 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m48]; exact w47_368
    have w48_36c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m48]; exact w47_36c
    have w48_370 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m48]; exact w47_370
    have w48_374 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m48]; exact w47_374
    have b48_420 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m48]; exact b47_420
    clear b47_420 w47_374 w47_370 w47_36c w47_368 w47_364 w47_360 w47_32c w47_328 w47_78 w47_74 w47_4c w47_48 g47_27 g47_26 g47_25 g47_24 g47_23 g47_22 g47_21 g47_20 g47_19 g47_18 g47_10 g47_9 g47_8 g47_4 g47_3 g47_2 V47 E47 fR47 t47 fr47 m47 s47 u47 d47
    -- 0x12A6: j
    obtain ⟨n49, d49, u49⟩ := s48.jump E48.self sv_at_12a6 (off' := 0x7A4) (by decide)
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
    have g49_9 : reg n49 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u49.regs, g48_9]
    have g49_10 : reg n49 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u49.regs, g48_10]
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
    have keep_kk49 : SvKeepL B n0.mem n49.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8), (0x420, 0x18), (0x378, 0x8)] := by rw [m49]; exact keep_kk48
    clear keep_kk48
    have w49_48 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m49]; exact w48_48
    have w49_4c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m49]; exact w48_4c
    have w49_74 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m49]; exact w48_74
    have w49_78 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m49]; exact w48_78
    have w49_328 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m49]; exact w48_328
    have w49_32c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m49]; exact w48_32c
    have w49_360 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m49]; exact w48_360
    have w49_364 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m49]; exact w48_364
    have w49_368 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m49]; exact w48_368
    have w49_36c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m49]; exact w48_36c
    have w49_370 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m49]; exact w48_370
    have w49_374 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m49]; exact w48_374
    have b49_420 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m49]; exact b48_420
    clear b48_420 w48_374 w48_370 w48_36c w48_368 w48_364 w48_360 w48_32c w48_328 w48_78 w48_74 w48_4c w48_48 g48_27 g48_26 g48_25 g48_24 g48_23 g48_22 g48_21 g48_20 g48_19 g48_18 g48_10 g48_9 g48_4 g48_3 g48_2 V48 E48 fR48 t48 fr48 m48 s48 u48 d48
    exact .inl ⟨(fun ⟨tl2', h0', h1', tl13', h2', h3', h4', te25', h5', tl31', h6', h7', te39', h8', tl45', h9', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr13] at h2'; cases h2'; rw [hr25] at h4'; cases h4'; rw [hte25] at h5'; cases h5'; rw [hr31] at h6'; cases h6'; rw [hr39] at h7'; cases h7'; rw [hte39] at h8'; cases h8'; rw [hr45] at h9'; cases h9'), sv_fail F E49 s49 t49 (fun x hx => (fR49 x hx).trans (fM x hx).symm) V49 hret g49_2 g49_18 hO g49_3 g49_4⟩
  rw [hr45] at R45
  obtain ⟨y0_45, y4_45, y8_45, y12_45, y16_45, y20_45, d8_45, d12_45⟩ := R45
  have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8), (0x420, 0x18), (0x378, 0x8)] := keep_kk44.trans K45
  clear keep_kk44
  have w45_48 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := (K45.w32 (by decide) (by decide)).trans w44_48
  have w45_4c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := (K45.w32 (by decide) (by decide)).trans w44_4c
  have w45_74 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := (K45.w32 (by decide) (by decide)).trans w44_74
  have w45_78 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := (K45.w32 (by decide) (by decide)).trans w44_78
  have w45_328 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := (K45.w32 (by decide) (by decide)).trans w44_328
  have w45_32c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := (K45.w32 (by decide) (by decide)).trans w44_32c
  have w45_360 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := (K45.w32 (by decide) (by decide)).trans w44_360
  have w45_364 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := (K45.w32 (by decide) (by decide)).trans w44_364
  have w45_368 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K45.w32 (by decide) (by decide)).trans w44_368
  have w45_36c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K45.w32 (by decide) (by decide)).trans w44_36c
  have w45_370 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := (K45.w32 (by decide) (by decide)).trans w44_370
  have w45_374 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := (K45.w32 (by decide) (by decide)).trans w44_374
  have w45_378 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 (tl45.header + tl45.len) := d8_45
  have w45_37c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (tl45.header + tl45.len) := d12_45
  have w45_424 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ((((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 tl45.header := y4_45
  have w45_428 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl45.len := y8_45
  have w45_42c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len) := y12_45
  have w45_430 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl45.header + tl45.len) := y16_45
  have b45_420 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := y0_45
  have b45_434 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl45.tag := y20_45
  clear b44_430 w44_42c w44_428 w44_424 w44_420 w44_37c w44_378 w44_374 w44_370 w44_36c w44_368 w44_364 w44_360 w44_32c w44_328 w44_78 w44_74 w44_4c w44_48 g44_12 g44_11 g44_10 g44_27 g44_26 g44_25 g44_24 g44_23 g44_22 g44_21 g44_20 g44_19 g44_18 g44_9 g44_8 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 rb44 s44 m44 u44 c44
  -- 0xE6C: lbu
  obtain ⟨n46, d46, u46⟩ := s45.lbu E45.self sv_at_e6c (off' := 0xE70) (by decide)
  have s46 : St n46.mem SV n46 0xE70 (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
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
  have g46_9 : reg n46 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u46.regs, upd_ne (by decide) (by decide), g45_9]
  have g46_18 : reg n46 (18 : Fin 32) = out := by rw [u46.regs, upd_ne (by decide) (by decide), g45_18]
  have g46_19 : reg n46 (19 : Fin 32) = bp := by rw [u46.regs, upd_ne (by decide) (by decide), g45_19]
  have g46_20 : reg n46 (20 : Fin 32) = x20 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_20]
  have g46_21 : reg n46 (21 : Fin 32) = x21 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_21]
  have g46_22 : reg n46 (22 : Fin 32) = x22 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_22]
  have g46_23 : reg n46 (23 : Fin 32) = x23 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_23]
  have g46_24 : reg n46 (24 : Fin 32) = x24 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_24]
  have g46_25 : reg n46 (25 : Fin 32) = x25 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_25]
  have g46_26 : reg n46 (26 : Fin 32) = x26 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_26]
  have g46_27 : reg n46 (27 : Fin 32) = x27 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_27]
  have g46_10 : reg n46 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [u46.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g45_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, b45_420]
  have keep_kk46 : SvKeepL B n0.mem n46.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8), (0x420, 0x18), (0x378, 0x8)] := by rw [m46]; exact keep_kk45
  clear keep_kk45
  have w46_48 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m46]; exact w45_48
  have w46_4c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m46]; exact w45_4c
  have w46_74 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m46]; exact w45_74
  have w46_78 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m46]; exact w45_78
  have w46_328 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m46]; exact w45_328
  have w46_32c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m46]; exact w45_32c
  have w46_360 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m46]; exact w45_360
  have w46_364 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m46]; exact w45_364
  have w46_368 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m46]; exact w45_368
  have w46_36c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m46]; exact w45_36c
  have w46_370 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m46]; exact w45_370
  have w46_374 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m46]; exact w45_374
  have w46_378 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 (tl45.header + tl45.len) := by rw [m46]; exact w45_378
  have w46_37c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (tl45.header + tl45.len) := by rw [m46]; exact w45_37c
  have w46_424 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ((((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 tl45.header := by rw [m46]; exact w45_424
  have w46_428 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl45.len := by rw [m46]; exact w45_428
  have w46_42c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len) := by rw [m46]; exact w45_42c
  have w46_430 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl45.header + tl45.len) := by rw [m46]; exact w45_430
  have b46_420 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m46]; exact b45_420
  have b46_434 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl45.tag := by rw [m46]; exact b45_434
  clear b45_434 b45_420 w45_430 w45_42c w45_428 w45_424 w45_37c w45_378 w45_374 w45_370 w45_36c w45_368 w45_364 w45_360 w45_32c w45_328 w45_78 w45_74 w45_4c w45_48 d12_45 d8_45 y20_45 y16_45 y12_45 y8_45 y4_45 y0_45 g45_27 g45_26 g45_25 g45_24 g45_23 g45_22 g45_21 g45_20 g45_19 g45_18 g45_9 g45_8 g45_4 g45_3 g45_2 V45 E45 fR45 t45 fr45 K45 rk45 sp45 s45 c45
  -- 0xE70: branch, not taken
  obtain ⟨n47, d47, u47⟩ := s46.notTaken E46.self 0xE74 sv_at_e70
    (by decide) (by rw [g46_10, s46.zero]; decide)
  have s47 : St n47.mem SV n47 0xE74 (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
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
  have g47_9 : reg n47 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u47.regs, g46_9]
  have g47_10 : reg n47 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u47.regs, g46_10]
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
  have keep_kk47 : SvKeepL B n0.mem n47.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8), (0x420, 0x18), (0x378, 0x8)] := by rw [m47]; exact keep_kk46
  clear keep_kk46
  have w47_48 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m47]; exact w46_48
  have w47_4c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m47]; exact w46_4c
  have w47_74 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m47]; exact w46_74
  have w47_78 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m47]; exact w46_78
  have w47_328 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m47]; exact w46_328
  have w47_32c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m47]; exact w46_32c
  have w47_360 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m47]; exact w46_360
  have w47_364 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m47]; exact w46_364
  have w47_368 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m47]; exact w46_368
  have w47_36c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m47]; exact w46_36c
  have w47_370 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m47]; exact w46_370
  have w47_374 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m47]; exact w46_374
  have w47_378 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 (tl45.header + tl45.len) := by rw [m47]; exact w46_378
  have w47_37c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (tl45.header + tl45.len) := by rw [m47]; exact w46_37c
  have w47_424 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ((((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 tl45.header := by rw [m47]; exact w46_424
  have w47_428 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl45.len := by rw [m47]; exact w46_428
  have w47_42c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len) := by rw [m47]; exact w46_42c
  have w47_430 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl45.header + tl45.len) := by rw [m47]; exact w46_430
  have b47_420 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m47]; exact b46_420
  have b47_434 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl45.tag := by rw [m47]; exact b46_434
  clear b46_434 b46_420 w46_430 w46_42c w46_428 w46_424 w46_37c w46_378 w46_374 w46_370 w46_36c w46_368 w46_364 w46_360 w46_32c w46_328 w46_78 w46_74 w46_4c w46_48 g46_10 g46_27 g46_26 g46_25 g46_24 g46_23 g46_22 g46_21 g46_20 g46_19 g46_18 g46_9 g46_8 g46_4 g46_3 g46_2 V46 E46 fR46 t46 fr46 m46 s46 u46 d46
  -- 0xE74: lw
  obtain ⟨n48, d48, u48⟩ := s47.lw E47.self sv_at_e74 (off' := 0xE78) (by decide)
    (by rw [g47_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s48 : St n48.mem SV n48 0xE78 (reg n48) := ⟨u48.pc, rfl, fun _ => rfl⟩
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
  have g48_9 : reg n48 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u48.regs, upd_ne (by decide) (by decide), g47_9]
  have g48_18 : reg n48 (18 : Fin 32) = out := by rw [u48.regs, upd_ne (by decide) (by decide), g47_18]
  have g48_19 : reg n48 (19 : Fin 32) = bp := by rw [u48.regs, upd_ne (by decide) (by decide), g47_19]
  have g48_20 : reg n48 (20 : Fin 32) = x20 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_20]
  have g48_21 : reg n48 (21 : Fin 32) = x21 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_21]
  have g48_22 : reg n48 (22 : Fin 32) = x22 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_22]
  have g48_23 : reg n48 (23 : Fin 32) = x23 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_23]
  have g48_24 : reg n48 (24 : Fin 32) = x24 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_24]
  have g48_25 : reg n48 (25 : Fin 32) = x25 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_25]
  have g48_26 : reg n48 (26 : Fin 32) = x26 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_26]
  have g48_27 : reg n48 (27 : Fin 32) = x27 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_27]
  have g48_10 : reg n48 a0 = ((((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 tl45.header := by
    rw [u48.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g47_2, show B + 0x21A0 + 0x424 = B + 0x21A0 + BitVec.ofNat 32 0x424 by sv_addr, w47_424]
  have keep_kk48 : SvKeepL B n0.mem n48.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8), (0x420, 0x18), (0x378, 0x8)] := by rw [m48]; exact keep_kk47
  clear keep_kk47
  have w48_48 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m48]; exact w47_48
  have w48_4c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m48]; exact w47_4c
  have w48_74 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m48]; exact w47_74
  have w48_78 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m48]; exact w47_78
  have w48_328 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m48]; exact w47_328
  have w48_32c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m48]; exact w47_32c
  have w48_360 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m48]; exact w47_360
  have w48_364 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m48]; exact w47_364
  have w48_368 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m48]; exact w47_368
  have w48_36c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m48]; exact w47_36c
  have w48_370 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m48]; exact w47_370
  have w48_374 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m48]; exact w47_374
  have w48_378 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 (tl45.header + tl45.len) := by rw [m48]; exact w47_378
  have w48_37c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (tl45.header + tl45.len) := by rw [m48]; exact w47_37c
  have w48_424 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ((((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 tl45.header := by rw [m48]; exact w47_424
  have w48_428 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl45.len := by rw [m48]; exact w47_428
  have w48_42c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len) := by rw [m48]; exact w47_42c
  have w48_430 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl45.header + tl45.len) := by rw [m48]; exact w47_430
  have b48_420 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m48]; exact b47_420
  have b48_434 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl45.tag := by rw [m48]; exact b47_434
  clear b47_434 b47_420 w47_430 w47_42c w47_428 w47_424 w47_37c w47_378 w47_374 w47_370 w47_36c w47_368 w47_364 w47_360 w47_32c w47_328 w47_78 w47_74 w47_4c w47_48 g47_27 g47_26 g47_25 g47_24 g47_23 g47_22 g47_21 g47_20 g47_19 g47_18 g47_10 g47_9 g47_8 g47_4 g47_3 g47_2 V47 E47 fR47 t47 fr47 m47 s47 u47 d47
  -- 0xE78: branch, not taken
  obtain ⟨n49, d49, u49⟩ := s48.notTaken E48.self 0xE7C sv_at_e78
    (by decide) (by rw [g48_10, s48.zero]; exact br_beq_f ((((((sd_in.contentW hr2).contentW hr13).restW hte25).restW hr31).restW hte39).ok_ne (opt_ok_elem hr45)))
  have s49 : St n49.mem SV n49 0xE7C (reg n49) := ⟨u49.pc, rfl, fun _ => rfl⟩
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
  have g49_9 : reg n49 (9 : Fin 32) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [u49.regs, g48_9]
  have g49_10 : reg n49 a0 = ((((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 tl45.header := by rw [u49.regs, g48_10]
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
  have keep_kk49 : SvKeepL B n0.mem n49.mem [(0x420, 0x10), (0x328, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8), (0x420, 0x18), (0x378, 0x8)] := by rw [m49]; exact keep_kk48
  clear keep_kk48
  have w49_48 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31.header + tl31.len) := by rw [m49]; exact w48_48
  have w49_4c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len) := by rw [m49]; exact w48_4c
  have w49_74 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ecp := by rw [m49]; exact w48_74
  have w49_78 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ecl := by rw [m49]; exact w48_78
  have w49_328 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = (sdp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m49]; exact w48_328
  have w49_32c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = (sdl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m49]; exact w48_32c
  have w49_360 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = (sdp) + BitVec.ofNat 32 tl2.header := by rw [m49]; exact w48_360
  have w49_364 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = BitVec.ofNat 32 tl2.len := by rw [m49]; exact w48_364
  have w49_368 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m49]; exact w48_368
  have w49_36c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = (BitVec.ofNat 32 tl2.len) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m49]; exact w48_36c
  have w49_370 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = ((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header := by rw [m49]; exact w48_370
  have w49_374 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = BitVec.ofNat 32 tl13.len := by rw [m49]; exact w48_374
  have w49_378 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = ((((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 (tl45.header + tl45.len) := by rw [m49]; exact w48_378
  have w49_37c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = ((((BitVec.ofNat 32 tl13.len) - BitVec.ofNat 32 (te25.header + te25.len)) - BitVec.ofNat 32 (tl31.header + tl31.len)) - BitVec.ofNat 32 (te39.header + te39.len)) - BitVec.ofNat 32 (tl45.header + tl45.len) := by rw [m49]; exact w48_37c
  have w49_424 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ((((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len)) + BitVec.ofNat 32 tl45.header := by rw [m49]; exact w48_424
  have w49_428 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl45.len := by rw [m49]; exact w48_428
  have w49_42c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (((((sdp) + BitVec.ofNat 32 tl2.header) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 (te25.header + te25.len)) + BitVec.ofNat 32 (tl31.header + tl31.len)) + BitVec.ofNat 32 (te39.header + te39.len) := by rw [m49]; exact w48_42c
  have w49_430 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl45.header + tl45.len) := by rw [m49]; exact w48_430
  have b49_420 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m49]; exact b48_420
  have b49_434 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 8 tl45.tag := by rw [m49]; exact b48_434
  clear b48_434 b48_420 w48_430 w48_42c w48_428 w48_424 w48_37c w48_378 w48_374 w48_370 w48_36c w48_368 w48_364 w48_360 w48_32c w48_328 w48_78 w48_74 w48_4c w48_48 g48_10 g48_27 g48_26 g48_25 g48_24 g48_23 g48_22 g48_21 g48_20 g48_19 g48_18 g48_9 g48_8 g48_4 g48_3 g48_2 V48 E48 fR48 t48 fr48 m48 s48 u48 d48
  exact .inr ⟨tl2, hr2, hsdrem, tl13, hr13, hsirem, hr25, te25, hte25, tl31, hr31, hr39, te39, hte39, tl45, hr45, n49, t49, s49, E49, V49, fR49, g49_2, g49_3, g49_4, g49_8, g49_10, g49_18, g49_19, g49_20, g49_21, g49_22, g49_23, g49_24, g49_25, g49_26, g49_27, w49_48, w49_4c, w49_74, w49_78, w49_378, w49_37c, w49_424, w49_428, w49_42c, w49_430, keep_kk49.mono (by decide)⟩

end C3.RV32.Sv
