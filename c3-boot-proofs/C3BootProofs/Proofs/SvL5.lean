import C3BootProofs.Proofs.SvCongr
import C3BootProofs.Image.BootloaderData3

/-!
# `sigstore::verify`: the subject and its public key

From the subject at 0x25A to 0x326: the subject, and the subject public key info, whose algorithm must be id-ecPublicKey with the P-256 curve and whose key must be a 65-byte BIT STRING.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svL525a : List BInstr :=
  [.aluImm .add a0 sp 0x80, .aluImm .add a1 sp 0x27C, .aluImm .add a2 x0 0x30]
theorem svL525a_end : blockEnd sigstoreVerifyCode 0x25A svL525a = some 0x262 := by
  simp only [svL525a]
  rw [blockEnd, sv_at_25a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_25c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_25e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL5270 : List BInstr :=
  [.aluImm .add a0 sp 0x80, .aluImm .add a1 sp 0x27C]
theorem svL5270_end : blockEnd sigstoreVerifyCode 0x270 svL5270 = some 0x274 := by
  simp only [svL5270]
  rw [blockEnd, sv_at_270]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_272]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL5286 : List BInstr :=
  [.aluImm .add a1 sp 0x85, .aluImm .add a0 sp 0x425, .aluImm .add a2 x0 0xB]
theorem svL5286_end : blockEnd sigstoreVerifyCode 0x286 svL5286 = some 0x290 := by
  simp only [svL5286]
  rw [blockEnd, sv_at_286]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_28a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_28e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL52a0 : List BInstr :=
  [.aluImm .add a0 sp 0x80, .aluImm .add a1 sp 0x420]
theorem svL52a0_end : blockEnd sigstoreVerifyCode 0x2A0 svL52a0 = some 0x2A6 := by
  simp only [svL52a0]
  rw [blockEnd, sv_at_2a0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_2a2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL52b8 : List BInstr :=
  [.aluImm .add (24 : Fin 32) x0 0x1]
theorem svL52b8_end : blockEnd sigstoreVerifyCode 0x2B8 svL52b8 = some 0x2BA := by
  simp only [svL52b8]
  rw [blockEnd, sv_at_2b8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL52de : List BInstr :=
  [.lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF832, .aluImm .add a3 x0 0x7, .alu .add a0 x0 (8 : Fin 32), .alu .add a1 x0 (26 : Fin 32)]
theorem svL52de_end : blockEnd sigstoreVerifyCode 0x2DE svL52de = some 0x2EC := by
  simp only [svL52de]
  rw [blockEnd, sv_at_2de]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_2e2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_2e6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_2e8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_2ea]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL52f4 : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x15]
theorem svL52f4_end : blockEnd sigstoreVerifyCode 0x2F4 svL52f4 = some 0x2F6 := by
  simp only [svL52f4]
  rw [blockEnd, sv_at_2f4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL52c0 : List BInstr :=
  [.aluImm .add a2 x0 0x6]
theorem svL52c0_end : blockEnd sigstoreVerifyCode 0x2C0 svL52c0 = some 0x2C2 := by
  simp only [svL52c0]
  rw [blockEnd, sv_at_2c0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL52c8 : List BInstr :=
  [.lui a2 0x3FCC4000, .aluImm .add a2 a2 0x748, .aluImm .add a3 x0 0x8]
theorem svL52c8_end : blockEnd sigstoreVerifyCode 0x2C8 svL52c8 = some 0x2D2 := by
  simp only [svL52c8]
  rw [blockEnd, sv_at_2c8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_2cc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_2d0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL52da : List BInstr :=
  [.aluImm .xor (24 : Fin 32) a0 0x1]
theorem svL52da_end : blockEnd sigstoreVerifyCode 0x2DA svL52da = some 0x2DE := by
  simp only [svL52da]
  rw [blockEnd, sv_at_2da]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL52fe : List BInstr :=
  [.aluImm .add a0 sp 0x80, .aluImm .add a1 sp 0x420]
theorem svL52fe_end : blockEnd sigstoreVerifyCode 0x2FE svL52fe = some 0x304 := by
  simp only [svL52fe]
  rw [blockEnd, sv_at_2fe]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_300]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL5312 : List BInstr :=
  [.alu .add (24 : Fin 32) x0 a0]
theorem svL5312_end : blockEnd sigstoreVerifyCode 0x312 svL5312 = some 0x314 := by
  simp only [svL5312]
  rw [blockEnd, sv_at_312]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL5316 : List BInstr :=
  [.aluImm .add a0 a0 0xFFFFFFBF]
theorem svL5316_end : blockEnd sigstoreVerifyCode 0x316 svL5316 = some 0x31A := by
  simp only [svL5316]
  rw [blockEnd, sv_at_316]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL514c : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x1]
theorem svL514c_end : blockEnd sigstoreVerifyCode 0x14C svL514c = some 0x14E := by
  simp only [svL514c]
  rw [blockEnd, sv_at_14c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_l5 {B out bp rootp dg lp ll rp rl tbp tbl sgp sgl : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x25A (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_9 : reg n0 (9 : Fin 32) = tbp)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = dg)
    (g0_21 : reg n0 (21 : Fin 32) = rootp)
    (g0_22 : reg n0 (22 : Fin 32) = ll)
    (g0_23 : reg n0 (23 : Fin 32) = sgp)
    (g0_25 : reg n0 (25 : Fin 32) = sgl)
    (g0_26 : reg n0 (26 : Fin 32) = lp)
    (g0_27 : reg n0 (27 : Fin 32) = tbl)
    (w0_284 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = rp)
    (w0_288 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = rl)
    (tb_in : SvIn B (rp) (rl).toNat) :
    (¬ (∃ tl2, derElement 0x30 (memBytes M0 (rp) (rl).toNat) = .ok tl2 ∧ ∃ tl6, derElement 0x30 (memBytes M0 ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)).toNat) = .ok tl6 ∧ ∃ op15 ol15 prp15 pu15, derAlgOf M0 (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) (tl6.len) = .ok ((op15, ol15), some (prp15, pu15)) ∧ ∃ ta15, derElement 0x30 (memBytes M0 (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) (tl6.len)) = .ok ta15 ∧ (BitVec.ofNat 8 pu15.tag = BitVec.ofNat 8 6) ∧ (memBytes M0 (prp15 + BitVec.ofNat 32 pu15.header) pu15.len = memBytes M0 (BitVec.ofNat 32 (img% svOidPrime256v1Address)) 8) ∧ (memBytes M0 op15 ol15 = memBytes M0 (BitVec.ofNat 32 (img% svOidEcPublicKeyAddress)) 7) ∧ ∃ tl35, derElement 3 (memBytes M0 ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)).toNat) = .ok tl35 ∧ ∃ bp35 bl35, derBitsOf (memBytes M0 ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)).toNat) ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) (.ok tl35) = .ok (bp35, bl35) ∧ (bl35 = BitVec.ofNat 32 0x41) ∧ (((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) = 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ tl2, derElement 0x30 (memBytes M0 (rp) (rl).toNat) = .ok tl2 ∧
    ∃ tl6, derElement 0x30 (memBytes M0 ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)).toNat) = .ok tl6 ∧
    ∃ op15 ol15 prp15 pu15, derAlgOf M0 (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) (tl6.len) = .ok ((op15, ol15), some (prp15, pu15)) ∧
    ∃ ta15, derElement 0x30 (memBytes M0 (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) (tl6.len)) = .ok ta15 ∧
    (BitVec.ofNat 8 pu15.tag = BitVec.ofNat 8 6) ∧
    (memBytes M0 (prp15 + BitVec.ofNat 32 pu15.header) pu15.len = memBytes M0 (BitVec.ofNat 32 (img% svOidPrime256v1Address)) 8) ∧
    (memBytes M0 op15 ol15 = memBytes M0 (BitVec.ofNat 32 (img% svOidEcPublicKeyAddress)) 7) ∧
    ∃ tl35, derElement 3 (memBytes M0 ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)).toNat) = .ok tl35 ∧
    ∃ bp35 bl35, derBitsOf (memBytes M0 ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)).toNat) ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) (.ok tl35) = .ok (bp35, bl35) ∧
    (bl35 = BitVec.ofNat 32 0x41) ∧
    (((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) = 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x326 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 0x15 ∧
        reg n' (9 : Fin 32) = tbp ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = dg ∧
        reg n' (21 : Fin 32) = rootp ∧
        reg n' (22 : Fin 32) = ll ∧
        reg n' (23 : Fin 32) = sgp ∧
        reg n' (24 : Fin 32) = bp35 ∧
        reg n' (25 : Fin 32) = sgl ∧
        reg n' (26 : Fin 32) = BitVec.ofNat 32 ol15 ∧
        reg n' (27 : Fin 32) = tbl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) ∧
        SvKeepL B n0.mem n'.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x25A
  obtain ⟨n1, c1, u1⟩ := s0.block svL525a E0.self svL525a_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0x262 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svL525a (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_9 : reg n1 (9 : Fin 32) = tbp := by
    rw [rb1, runBlock_reg _ _ _ (9 : Fin 32) s0.zero (by decide), g0_9]
  have g1_18 : reg n1 (18 : Fin 32) = out := by
    rw [rb1, runBlock_reg _ _ _ (18 : Fin 32) s0.zero (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by
    rw [rb1, runBlock_reg _ _ _ (19 : Fin 32) s0.zero (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = dg := by
    rw [rb1, runBlock_reg _ _ _ (20 : Fin 32) s0.zero (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = rootp := by
    rw [rb1, runBlock_reg _ _ _ (21 : Fin 32) s0.zero (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = ll := by
    rw [rb1, runBlock_reg _ _ _ (22 : Fin 32) s0.zero (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = sgp := by
    rw [rb1, runBlock_reg _ _ _ (23 : Fin 32) s0.zero (by decide), g0_23]
  have g1_25 : reg n1 (25 : Fin 32) = sgl := by
    rw [rb1, runBlock_reg _ _ _ (25 : Fin 32) s0.zero (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = lp := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = tbl := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svL525a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_9, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_11 : reg n1 a1 = B + 0x21A0 + BitVec.ofNat 32 0x27C := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svL525a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_9, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_12 : reg n1 a2 = BitVec.ofNat 32 0x30 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svL525a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_9, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_284 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = rp := by rw [m1]; exact w0_284
  have w1_288 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = rl := by rw [m1]; exact w0_288
  -- 0x262: sv_elemF
  obtain ⟨n2, c2, s2, rk2, K2, Ok2, Er2, fr2⟩ := sv_elemF (oc := 0x80) (dc := 0x27C) (tag := 0x30)
    F E1 s1 sv_at_262 sv_at_266 (by decide) (by decide) g1_10 g1_11 g1_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w1_284 w1_288
  have t2 : Steps n0 n2 := t1.trans c2
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.keepL K2 (by decide)
  rw [sv_mb fR1 tb_in] at Ok2 Er2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [rk2 sp (by decide) (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk2 (3 : Fin 32) (by decide) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk2 (4 : Fin 32) (by decide) (by decide), g1_4]
  have g2_9 : reg n2 (9 : Fin 32) = tbp := by rw [rk2 (9 : Fin 32) (by decide) (by decide), g1_9]
  have g2_10 : reg n2 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by rw [rk2 a0 (by decide) (by decide), g1_10]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [rk2 (18 : Fin 32) (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [rk2 (19 : Fin 32) (by decide) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = dg := by rw [rk2 (20 : Fin 32) (by decide) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = rootp := by rw [rk2 (21 : Fin 32) (by decide) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = ll := by rw [rk2 (22 : Fin 32) (by decide) (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = sgp := by rw [rk2 (23 : Fin 32) (by decide) (by decide), g1_23]
  have g2_25 : reg n2 (25 : Fin 32) = sgl := by rw [rk2 (25 : Fin 32) (by decide) (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = lp := by rw [rk2 (26 : Fin 32) (by decide) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = tbl := by rw [rk2 (27 : Fin 32) (by decide) (by decide), g1_27]
  obtain ⟨r2, hr2⟩ : ∃ r, derElement 0x30 (memBytes M0 (rp) (rl).toNat) = r := ⟨_, rfl⟩
  rcases r2 with er2 | tl2
  · obtain ⟨zhr2, ezhr2⟩ := Er2 er2 hr2
    have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x80, 0x11), (0x284, 0x8)] := keep_kk1.trans K2
    clear keep_kk1
    have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := zhr2
    have b2_84 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er2 := ezhr2
    clear w1_288 w1_284 g1_12 g1_11 g1_10 g1_27 g1_26 g1_25 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_9 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
    -- 0x26A: lw
    obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_26a (off' := 0x26C) (by decide)
      (by rw [g2_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s3 : St n3.mem SV n3 0x26C (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = n2.mem := u3.mem
    have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
    have t3 : Steps n0 n3 := t2.trans (.single d3)
    have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
    have E3 : SvCode n3.mem := E2.fr F fr3
    have V3 : SvSaves B n3.mem v := V2.same m3
    have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
    have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
    have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
    have g3_9 : reg n3 (9 : Fin 32) = tbp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_9]
    have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
    have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
    have g3_20 : reg n3 (20 : Fin 32) = dg := by rw [u3.regs, upd_ne (by decide) (by decide), g2_20]
    have g3_21 : reg n3 (21 : Fin 32) = rootp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
    have g3_22 : reg n3 (22 : Fin 32) = ll := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
    have g3_23 : reg n3 (23 : Fin 32) = sgp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_23]
    have g3_25 : reg n3 (25 : Fin 32) = sgl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
    have g3_26 : reg n3 (26 : Fin 32) = lp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
    have g3_27 : reg n3 (27 : Fin 32) = tbl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
    have g3_10 : reg n3 a0 = 0 := by
      rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g2_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w2_80]
    have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x80, 0x11), (0x284, 0x8)] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m3]; exact w2_80
    have b3_84 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er2 := by rw [m3]; exact b2_84
    clear b2_84 w2_80 ezhr2 zhr2
    -- 0x26C: branch, taken
    obtain ⟨n4, d4, u4⟩ := s3.taken E3.self 0x7A0 sv_at_26c
      (by decide) (by rw [g3_10, s3.zero]; rfl)
    have s4 : St n4.mem SV n4 0x7A0 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    have m4 : n4.mem = n3.mem := u4.mem
    have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
    have t4 : Steps n0 n4 := t3.trans (.single d4)
    have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
    have E4 : SvCode n4.mem := E3.fr F fr4
    have V4 : SvSaves B n4.mem v := V3.same m4
    have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
    have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
    have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
    have g4_9 : reg n4 (9 : Fin 32) = tbp := by rw [u4.regs, g3_9]
    have g4_10 : reg n4 a0 = 0 := by rw [u4.regs, g3_10]
    have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, g3_18]
    have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, g3_19]
    have g4_20 : reg n4 (20 : Fin 32) = dg := by rw [u4.regs, g3_20]
    have g4_21 : reg n4 (21 : Fin 32) = rootp := by rw [u4.regs, g3_21]
    have g4_22 : reg n4 (22 : Fin 32) = ll := by rw [u4.regs, g3_22]
    have g4_23 : reg n4 (23 : Fin 32) = sgp := by rw [u4.regs, g3_23]
    have g4_25 : reg n4 (25 : Fin 32) = sgl := by rw [u4.regs, g3_25]
    have g4_26 : reg n4 (26 : Fin 32) = lp := by rw [u4.regs, g3_26]
    have g4_27 : reg n4 (27 : Fin 32) = tbl := by rw [u4.regs, g3_27]
    have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x80, 0x11), (0x284, 0x8)] := by rw [m4]; exact keep_kk3
    clear keep_kk3
    have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m4]; exact w3_80
    have b4_84 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er2 := by rw [m4]; exact b3_84
    clear b3_84 w3_80 g3_10 g3_27 g3_26 g3_25 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_9 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
    -- 0x7A0: lbu
    obtain ⟨n5, d5, u5⟩ := s4.lbu E4.self sv_at_7a0 (off' := 0x7A4) (by decide)
    have s5 : St n5.mem SV n5 0x7A4 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
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
    have g5_10 : reg n5 a0 = 0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_10]
    have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, upd_ne (by decide) (by decide), g4_18]
    have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_19]
    have g5_20 : reg n5 (20 : Fin 32) = dg := by rw [u5.regs, upd_ne (by decide) (by decide), g4_20]
    have g5_21 : reg n5 (21 : Fin 32) = rootp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_21]
    have g5_22 : reg n5 (22 : Fin 32) = ll := by rw [u5.regs, upd_ne (by decide) (by decide), g4_22]
    have g5_23 : reg n5 (23 : Fin 32) = sgp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_23]
    have g5_25 : reg n5 (25 : Fin 32) = sgl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_25]
    have g5_26 : reg n5 (26 : Fin 32) = lp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_26]
    have g5_27 : reg n5 (27 : Fin 32) = tbl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_27]
    have g5_8 : reg n5 (8 : Fin 32) = (derErrByte er2).zeroExtend 32 := by
      rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g4_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, b4_84]
    have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x80, 0x11), (0x284, 0x8)] := by rw [m5]; exact keep_kk4
    clear keep_kk4
    have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m5]; exact w4_80
    have b5_84 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er2 := by rw [m5]; exact b4_84
    clear b4_84 w4_80 g4_27 g4_26 g4_25 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
    exact .inl ⟨(fun ⟨tl2', h0', _⟩ => by rw [hr2] at h0'; cases h0'), sv_fail F E5 s5 t5 (fun x hx => (fR5 x hx).trans (fM x hx).symm) V5 hret g5_2 g5_18 hO g5_3 g5_4 (by rw [g5_8]; sv_code)⟩
  obtain ⟨o0_2, o4_2, o8_2, o12_2, o16_2, d8_2, d12_2⟩ := Ok2 tl2 hr2
  have keep_kk2 : SvKeepL B n0.mem n2.mem [(0x80, 0x11), (0x284, 0x8)] := keep_kk1.trans K2
  clear keep_kk1
  have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (rp) + BitVec.ofNat 32 tl2.header := o0_2
  have w2_84 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl2.len := o4_2
  have w2_88 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = rp := o8_2
  have w2_8c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl2.header + tl2.len) := o12_2
  have w2_284 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := d8_2
  have w2_288 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := d12_2
  have b2_90 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl2.tag := o16_2
  clear w1_288 w1_284 g1_12 g1_11 g1_10 g1_27 g1_26 g1_25 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_9 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x26A: lw
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_26a (off' := 0x26C) (by decide)
    (by rw [g2_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s3 : St n3.mem SV n3 0x26C (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_9 : reg n3 (9 : Fin 32) = tbp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_9]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = dg := by rw [u3.regs, upd_ne (by decide) (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = rootp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = ll := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = sgp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_23]
  have g3_25 : reg n3 (25 : Fin 32) = sgl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = lp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = tbl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_10 : reg n3 a0 = (rp) + BitVec.ofNat 32 tl2.header := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w2_80]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [(0x80, 0x11), (0x284, 0x8)] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m3]; exact w2_80
  have w3_84 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl2.len := by rw [m3]; exact w2_84
  have w3_88 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = rp := by rw [m3]; exact w2_88
  have w3_8c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m3]; exact w2_8c
  have w3_284 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m3]; exact w2_284
  have w3_288 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m3]; exact w2_288
  have b3_90 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl2.tag := by rw [m3]; exact b2_90
  clear b2_90 w2_288 w2_284 w2_8c w2_88 w2_84 w2_80 d12_2 d8_2 o16_2 o12_2 o8_2 o4_2 o0_2 g2_27 g2_26 g2_25 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_10 g2_9 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 Er2 Ok2 K2 rk2 s2 c2
  -- 0x26C: branch, not taken
  obtain ⟨n4, d4, u4⟩ := s3.notTaken E3.self 0x270 sv_at_26c
    (by decide) (by rw [g3_10, s3.zero]; exact br_beq_f (tb_in.ok_ne hr2))
  have s4 : St n4.mem SV n4 0x270 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, g3_4]
  have g4_9 : reg n4 (9 : Fin 32) = tbp := by rw [u4.regs, g3_9]
  have g4_10 : reg n4 a0 = (rp) + BitVec.ofNat 32 tl2.header := by rw [u4.regs, g3_10]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = dg := by rw [u4.regs, g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = rootp := by rw [u4.regs, g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = ll := by rw [u4.regs, g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = sgp := by rw [u4.regs, g3_23]
  have g4_25 : reg n4 (25 : Fin 32) = sgl := by rw [u4.regs, g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = lp := by rw [u4.regs, g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = tbl := by rw [u4.regs, g3_27]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x80, 0x11), (0x284, 0x8)] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m4]; exact w3_80
  have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl2.len := by rw [m4]; exact w3_84
  have w4_88 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = rp := by rw [m4]; exact w3_88
  have w4_8c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m4]; exact w3_8c
  have w4_284 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m4]; exact w3_284
  have w4_288 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m4]; exact w3_288
  have b4_90 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl2.tag := by rw [m4]; exact b3_90
  clear b3_90 w3_288 w3_284 w3_8c w3_88 w3_84 w3_80 g3_10 g3_27 g3_26 g3_25 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_9 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x270
  obtain ⟨n5, c5, u5⟩ := s4.block svL5270 E4.self svL5270_end
    ⟨trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0x274 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock svL5270 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
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
  have g5_9 : reg n5 (9 : Fin 32) = tbp := by
    rw [rb5, runBlock_reg _ _ _ (9 : Fin 32) s4.zero (by decide), g4_9]
  have g5_18 : reg n5 (18 : Fin 32) = out := by
    rw [rb5, runBlock_reg _ _ _ (18 : Fin 32) s4.zero (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by
    rw [rb5, runBlock_reg _ _ _ (19 : Fin 32) s4.zero (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = dg := by
    rw [rb5, runBlock_reg _ _ _ (20 : Fin 32) s4.zero (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = rootp := by
    rw [rb5, runBlock_reg _ _ _ (21 : Fin 32) s4.zero (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = ll := by
    rw [rb5, runBlock_reg _ _ _ (22 : Fin 32) s4.zero (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = sgp := by
    rw [rb5, runBlock_reg _ _ _ (23 : Fin 32) s4.zero (by decide), g4_23]
  have g5_25 : reg n5 (25 : Fin 32) = sgl := by
    rw [rb5, runBlock_reg _ _ _ (25 : Fin 32) s4.zero (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = lp := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = tbl := by
    rw [rb5, runBlock_reg _ _ _ (27 : Fin 32) s4.zero (by decide), g4_27]
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svL5270, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_9, g4_10, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g5_11 : reg n5 a1 = B + 0x21A0 + BitVec.ofNat 32 0x27C := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svL5270, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_9, g4_10, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x80, 0x11), (0x284, 0x8)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (rp) + BitVec.ofNat 32 tl2.header := by rw [m5]; exact w4_80
  have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl2.len := by rw [m5]; exact w4_84
  have w5_88 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = rp := by rw [m5]; exact w4_88
  have w5_8c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m5]; exact w4_8c
  have w5_284 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = (rp) + BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m5]; exact w4_284
  have w5_288 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = (rl) - BitVec.ofNat 32 (tl2.header + tl2.len) := by rw [m5]; exact w4_288
  have b5_90 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl2.tag := by rw [m5]; exact b4_90
  clear b4_90 w4_288 w4_284 w4_8c w4_88 w4_84 w4_80 g4_27 g4_26 g4_25 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_9 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  -- 0x274: sv_seqF
  obtain ⟨n6, c6, s6, sp6, rk6, K6, Ok6, Er6, fr6⟩ := sv_seqF (oc := 0x80) (dc := 0x27C)
    F E5 s5 sv_at_274 sv_at_278 (by decide) (by decide) g5_2 g5_10 g5_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w5_284 w5_288 (tb_in.restW hr2)
  have t6 : Steps n0 n6 := t5.trans c6
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.keepL K6 (by decide)
  rw [sv_mb fR5 (tb_in.restW hr2)] at Ok6 Er6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [rk6 sp (by decide) (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk6 (3 : Fin 32) (by decide) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk6 (4 : Fin 32) (by decide) (by decide), g5_4]
  have g6_9 : reg n6 (9 : Fin 32) = tbp := by rw [rk6 (9 : Fin 32) (by decide) (by decide), g5_9]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [rk6 (18 : Fin 32) (by decide) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [rk6 (19 : Fin 32) (by decide) (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = dg := by rw [rk6 (20 : Fin 32) (by decide) (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = rootp := by rw [rk6 (21 : Fin 32) (by decide) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = ll := by rw [rk6 (22 : Fin 32) (by decide) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = sgp := by rw [rk6 (23 : Fin 32) (by decide) (by decide), g5_23]
  have g6_25 : reg n6 (25 : Fin 32) = sgl := by rw [rk6 (25 : Fin 32) (by decide) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = lp := by rw [rk6 (26 : Fin 32) (by decide) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = tbl := by rw [rk6 (27 : Fin 32) (by decide) (by decide), g5_27]
  obtain ⟨r6, hr6⟩ : ∃ r, derElement 0x30 (memBytes M0 ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)).toNat) = r := ⟨_, rfl⟩
  rcases r6 with er6 | tl6
  · obtain ⟨z6, ez6⟩ := Er6 er6 hr6
    have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8)] := keep_kk5.trans K6
    clear keep_kk5
    have b6_90 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl2.tag := (K6.b8 (by decide) (by decide)).trans b5_90
    have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := z6
    have b6_84 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er6 := ez6
    clear b5_90 w5_288 w5_284 w5_8c w5_88 w5_84 w5_80 g5_11 g5_10 g5_27 g5_26 g5_25 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_9 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
    -- 0x27C: lw
    obtain ⟨n7, d7, u7⟩ := s6.lw E6.self sv_at_27c (off' := 0x27E) (by decide)
      (by rw [g6_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s7 : St n7.mem SV n7 0x27E (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
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
    have g7_25 : reg n7 (25 : Fin 32) = sgl := by rw [u7.regs, upd_ne (by decide) (by decide), g6_25]
    have g7_26 : reg n7 (26 : Fin 32) = lp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_26]
    have g7_27 : reg n7 (27 : Fin 32) = tbl := by rw [u7.regs, upd_ne (by decide) (by decide), g6_27]
    have g7_24 : reg n7 (24 : Fin 32) = 0 := by
      rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g6_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w6_80]
    have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8)] := by rw [m7]; exact keep_kk6
    clear keep_kk6
    have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m7]; exact w6_80
    have b7_84 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er6 := by rw [m7]; exact b6_84
    have b7_90 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl2.tag := by rw [m7]; exact b6_90
    clear b6_84 w6_80 b6_90 ez6 z6
    -- 0x27E: lbu
    obtain ⟨n8, d8, u8⟩ := s7.lbu E7.self sv_at_27e (off' := 0x282) (by decide)
    have s8 : St n8.mem SV n8 0x282 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
    have m8 : n8.mem = n7.mem := u8.mem
    have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
    have t8 : Steps n0 n8 := t7.trans (.single d8)
    have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
    have E8 : SvCode n8.mem := E7.fr F fr8
    have V8 : SvSaves B n8.mem v := V7.same m8
    have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_2]
    have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_3]
    have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_4]
    have g8_9 : reg n8 (9 : Fin 32) = tbp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_9]
    have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, upd_ne (by decide) (by decide), g7_18]
    have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_19]
    have g8_20 : reg n8 (20 : Fin 32) = dg := by rw [u8.regs, upd_ne (by decide) (by decide), g7_20]
    have g8_21 : reg n8 (21 : Fin 32) = rootp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_21]
    have g8_22 : reg n8 (22 : Fin 32) = ll := by rw [u8.regs, upd_ne (by decide) (by decide), g7_22]
    have g8_23 : reg n8 (23 : Fin 32) = sgp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_23]
    have g8_24 : reg n8 (24 : Fin 32) = 0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_24]
    have g8_25 : reg n8 (25 : Fin 32) = sgl := by rw [u8.regs, upd_ne (by decide) (by decide), g7_25]
    have g8_26 : reg n8 (26 : Fin 32) = lp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_26]
    have g8_27 : reg n8 (27 : Fin 32) = tbl := by rw [u8.regs, upd_ne (by decide) (by decide), g7_27]
    have g8_8 : reg n8 (8 : Fin 32) = (derErrByte er6).zeroExtend 32 := by
      rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g7_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, b7_84]
    have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8)] := by rw [m8]; exact keep_kk7
    clear keep_kk7
    have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m8]; exact w7_80
    have b8_84 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er6 := by rw [m8]; exact b7_84
    have b8_90 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl2.tag := by rw [m8]; exact b7_90
    clear b7_90 b7_84 w7_80 g7_24 g7_27 g7_26 g7_25 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_9 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
    -- 0x282: branch, taken
    obtain ⟨n9, d9, u9⟩ := s8.taken E8.self 0x7A4 sv_at_282
      (by decide) (by rw [g8_24, s8.zero]; rfl)
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
    have g9_8 : reg n9 (8 : Fin 32) = (derErrByte er6).zeroExtend 32 := by rw [u9.regs, g8_8]
    have g9_9 : reg n9 (9 : Fin 32) = tbp := by rw [u9.regs, g8_9]
    have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, g8_19]
    have g9_20 : reg n9 (20 : Fin 32) = dg := by rw [u9.regs, g8_20]
    have g9_21 : reg n9 (21 : Fin 32) = rootp := by rw [u9.regs, g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = ll := by rw [u9.regs, g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = sgp := by rw [u9.regs, g8_23]
    have g9_24 : reg n9 (24 : Fin 32) = 0 := by rw [u9.regs, g8_24]
    have g9_25 : reg n9 (25 : Fin 32) = sgl := by rw [u9.regs, g8_25]
    have g9_26 : reg n9 (26 : Fin 32) = lp := by rw [u9.regs, g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = tbl := by rw [u9.regs, g8_27]
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8)] := by rw [m9]; exact keep_kk8
    clear keep_kk8
    have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m9]; exact w8_80
    have b9_84 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er6 := by rw [m9]; exact b8_84
    have b9_90 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl2.tag := by rw [m9]; exact b8_90
    clear b8_90 b8_84 w8_80 g8_8 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
    exact .inl ⟨(fun ⟨tl2', h0', tl6', h1', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr6] at h1'; cases h1'), sv_fail F E9 s9 t9 (fun x hx => (fR9 x hx).trans (fM x hx).symm) V9 hret g9_2 g9_18 hO g9_3 g9_4 (by rw [g9_8]; sv_code)⟩
  obtain ⟨o0_6, o4_6, o8_6, o12_6, d8_6, d12_6⟩ := Ok6 tl6 hr6
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8)] := keep_kk5.trans K6
  clear keep_kk5
  have b6_90 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl2.tag := (K6.b8 (by decide) (by decide)).trans b5_90
  have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := o0_6
  have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl6.len := o4_6
  have w6_88 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := o8_6
  have w6_8c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl6.len := o12_6
  have w6_284 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := d8_6
  have w6_288 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := d12_6
  clear b5_90 w5_288 w5_284 w5_8c w5_88 w5_84 w5_80 g5_11 g5_10 g5_27 g5_26 g5_25 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_9 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0x27C: lw
  obtain ⟨n7, d7, u7⟩ := s6.lw E6.self sv_at_27c (off' := 0x27E) (by decide)
    (by rw [g6_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s7 : St n7.mem SV n7 0x27E (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
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
  have g7_25 : reg n7 (25 : Fin 32) = sgl := by rw [u7.regs, upd_ne (by decide) (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = lp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = tbl := by rw [u7.regs, upd_ne (by decide) (by decide), g6_27]
  have g7_24 : reg n7 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by
    rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g6_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w6_80]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m7]; exact w6_80
  have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl6.len := by rw [m7]; exact w6_84
  have w7_88 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m7]; exact w6_88
  have w7_8c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl6.len := by rw [m7]; exact w6_8c
  have w7_284 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m7]; exact w6_284
  have w7_288 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m7]; exact w6_288
  have b7_90 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl2.tag := by rw [m7]; exact b6_90
  clear w6_288 w6_284 w6_8c w6_88 w6_84 w6_80 b6_90 d12_6 d8_6 o12_6 o8_6 o4_6 o0_6 g6_27 g6_26 g6_25 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_9 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 Er6 Ok6 K6 rk6 sp6 s6 c6
  -- 0x27E: lbu
  obtain ⟨n8, d8, u8⟩ := s7.lbu E7.self sv_at_27e (off' := 0x282) (by decide)
  have b7_84 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by
    have h := byte_of_ld w7_84
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr]; exact h.1
  have s8 : St n8.mem SV n8 0x282 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans (.single d8)
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_4]
  have g8_9 : reg n8 (9 : Fin 32) = tbp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_9]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, upd_ne (by decide) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = dg := by rw [u8.regs, upd_ne (by decide) (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = rootp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = ll := by rw [u8.regs, upd_ne (by decide) (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = sgp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [u8.regs, upd_ne (by decide) (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = sgl := by rw [u8.regs, upd_ne (by decide) (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = lp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = tbl := by rw [u8.regs, upd_ne (by decide) (by decide), g7_27]
  have g8_8 : reg n8 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g7_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, b7_84]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m8]; exact w7_80
  have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl6.len := by rw [m8]; exact w7_84
  have w8_88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m8]; exact w7_88
  have w8_8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl6.len := by rw [m8]; exact w7_8c
  have w8_284 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m8]; exact w7_284
  have w8_288 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m8]; exact w7_288
  have b8_84 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m8]; exact b7_84
  have b8_90 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl2.tag := by rw [m8]; exact b7_90
  clear b7_90 w7_288 w7_284 w7_8c w7_88 w7_84 w7_80 g7_24 g7_27 g7_26 g7_25 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_9 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0x282: branch, not taken
  obtain ⟨n9, d9, u9⟩ := s8.notTaken E8.self 0x286 sv_at_282
    (by decide) (by rw [g8_24, s8.zero]; exact br_beq_f ((tb_in.restW hr2).ok_ne hr6))
  have s9 : St n9.mem SV n9 0x286 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
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
  have g9_9 : reg n9 (9 : Fin 32) = tbp := by rw [u9.regs, g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = dg := by rw [u9.regs, g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = rootp := by rw [u9.regs, g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = ll := by rw [u9.regs, g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = sgp := by rw [u9.regs, g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [u9.regs, g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = sgl := by rw [u9.regs, g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = lp := by rw [u9.regs, g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = tbl := by rw [u9.regs, g8_27]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m9]; exact w8_80
  have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl6.len := by rw [m9]; exact w8_84
  have w9_88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m9]; exact w8_88
  have w9_8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl6.len := by rw [m9]; exact w8_8c
  have w9_284 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m9]; exact w8_284
  have w9_288 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m9]; exact w8_288
  have b9_84 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m9]; exact b8_84
  have b9_90 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl2.tag := by rw [m9]; exact b8_90
  clear b8_90 b8_84 w8_288 w8_284 w8_8c w8_88 w8_84 w8_80 g8_8 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 b7_84 u8 d8
  -- 0x286
  obtain ⟨n10, c10, u10⟩ := s9.block svL5286 E9.self svL5286_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0x290 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock svL5286 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
  have g10_9 : reg n10 (9 : Fin 32) = tbp := by
    rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
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
  have g10_24 : reg n10 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by
    rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = sgl := by
    rw [rb10, runBlock_reg _ _ _ (25 : Fin 32) s9.zero (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = lp := by
    rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = tbl := by
    rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
  have g10_10 : reg n10 a0 = B + 0x21A0 + BitVec.ofNat 32 0x425 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svL5286, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g10_11 : reg n10 a1 = B + 0x21A0 + BitVec.ofNat 32 0x85 := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svL5286, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g10_12 : reg n10 a2 = BitVec.ofNat 32 0xB := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svL5286, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m10]; exact w9_80
  have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl6.len := by rw [m10]; exact w9_84
  have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m10]; exact w9_88
  have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl6.len := by rw [m10]; exact w9_8c
  have w10_284 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m10]; exact w9_284
  have w10_288 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m10]; exact w9_288
  have b10_84 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m10]; exact b9_84
  have b10_90 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl2.tag := by rw [m10]; exact b9_90
  clear b9_90 b9_84 w9_288 w9_284 w9_8c w9_88 w9_84 w9_80 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
  have b10_85 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by
    have h := byte_of_ld w10_84
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x85 = B + 0x21A0 + BitVec.ofNat 32 0x84 + 1 by sv_addr]; exact h.2.1
  have b10_86 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by
    have h := byte_of_ld w10_84
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x86 = B + 0x21A0 + BitVec.ofNat 32 0x84 + 2 by sv_addr]; exact h.2.2.1
  have b10_87 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by
    have h := byte_of_ld w10_84
    rw [show B + 0x21A0 + BitVec.ofNat 32 0x87 = B + 0x21A0 + BitVec.ofNat 32 0x84 + 3 by sv_addr]; exact h.2.2.2
  -- 0x290: memcpy
  obtain ⟨n11, P11, K11, X11⟩ := sv_mc (c := 0x425) (d := 0x85) (N := 0xB) F E10 s10 sv_at_290 sv_at_294
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
  have g11_9 : reg n11 (9 : Fin 32) = tbp := by rw [P11.regs (9 : Fin 32) (by decide), g10_9]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [P11.regs (18 : Fin 32) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [P11.regs (19 : Fin 32) (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = dg := by rw [P11.regs (20 : Fin 32) (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = rootp := by rw [P11.regs (21 : Fin 32) (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = ll := by rw [P11.regs (22 : Fin 32) (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = sgp := by rw [P11.regs (23 : Fin 32) (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [P11.regs (24 : Fin 32) (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = sgl := by rw [P11.regs (25 : Fin 32) (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = lp := by rw [P11.regs (26 : Fin 32) (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = tbl := by rw [P11.regs (27 : Fin 32) (by decide), g10_27]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB)] := keep_kk10.trans K11.toL
  clear keep_kk10
  have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K11.w32 (by decide) (by decide)).trans w10_80
  have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl6.len := (K11.w32 (by decide) (by decide)).trans w10_84
  have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K11.w32 (by decide) (by decide)).trans w10_88
  have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl6.len := (K11.w32 (by decide) (by decide)).trans w10_8c
  have w11_284 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K11.w32 (by decide) (by decide)).trans w10_284
  have w11_288 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K11.w32 (by decide) (by decide)).trans w10_288
  have b11_84 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := (K11.b8 (by decide) (by decide)).trans b10_84
  have b11_85 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K11.b8 (by decide) (by decide)).trans b10_85
  have b11_86 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K11.b8 (by decide) (by decide)).trans b10_86
  have b11_87 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K11.b8 (by decide) (by decide)).trans b10_87
  have b11_90 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl2.tag := (K11.b8 (by decide) (by decide)).trans b10_90
  have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by
    rw [← w10_88]
    exact ld_cp fun q hq => by
      have := X11 (0x3 + q) (by omega)
      rwa [show 0x425 + (0x3 + q) = 0x428 + q by omega,
        show 0x85 + (0x3 + q) = 0x88 + q by omega] at this
  have w11_42c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := by
    rw [← w10_8c]
    exact ld_cp fun q hq => by
      have := X11 (0x7 + q) (by omega)
      rwa [show 0x425 + (0x7 + q) = 0x42C + q by omega,
        show 0x85 + (0x7 + q) = 0x8C + q by omega] at this
  have b11_425 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [show 0x425 = 0x425 + 0x0 from rfl, X11 0x0 (by decide)]; exact b10_85
  have b11_426 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [show 0x426 = 0x425 + 0x1 from rfl, X11 0x1 (by decide)]; exact b10_86
  have b11_427 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [show 0x427 = 0x425 + 0x2 from rfl, X11 0x2 (by decide)]; exact b10_87
  clear b10_90 b10_84 w10_288 w10_284 w10_8c w10_88 w10_84 w10_80 g10_12 g10_11 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  -- 0x298: sw
  obtain ⟨n12, d12, s12, fr12, K12, W12, rg12⟩ := sv_sw F E11 s11 sv_at_298 (off' := 0x29C) (c := 0x420)
    (by decide) (by rw [g11_2]; sv_addr) (by decide) (by decide)
  have t12 : Steps n0 n12 := t11.trans d12
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.keep K12 (by decide)
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [rg12 sp, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg12 (3 : Fin 32), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg12 (4 : Fin 32), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg12 (8 : Fin 32), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = tbp := by rw [rg12 (9 : Fin 32), g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [rg12 (18 : Fin 32), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [rg12 (19 : Fin 32), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = dg := by rw [rg12 (20 : Fin 32), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = rootp := by rw [rg12 (21 : Fin 32), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = ll := by rw [rg12 (22 : Fin 32), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = sgp := by rw [rg12 (23 : Fin 32), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [rg12 (24 : Fin 32), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = sgl := by rw [rg12 (25 : Fin 32), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = lp := by rw [rg12 (26 : Fin 32), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = tbl := by rw [rg12 (27 : Fin 32), g11_27]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4)] := keep_kk11.trans K12.toL
  clear keep_kk11
  have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K12.w32 (by decide) (by decide)).trans w11_80
  have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl6.len := (K12.w32 (by decide) (by decide)).trans w11_84
  have w12_88 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K12.w32 (by decide) (by decide)).trans w11_88
  have w12_8c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl6.len := (K12.w32 (by decide) (by decide)).trans w11_8c
  have w12_284 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K12.w32 (by decide) (by decide)).trans w11_284
  have w12_288 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K12.w32 (by decide) (by decide)).trans w11_288
  have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K12.w32 (by decide) (by decide)).trans w11_428
  have w12_42c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := (K12.w32 (by decide) (by decide)).trans w11_42c
  have b12_84 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := (K12.b8 (by decide) (by decide)).trans b11_84
  have b12_85 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K12.b8 (by decide) (by decide)).trans b11_85
  have b12_86 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K12.b8 (by decide) (by decide)).trans b11_86
  have b12_87 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K12.b8 (by decide) (by decide)).trans b11_87
  have b12_90 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl2.tag := (K12.b8 (by decide) (by decide)).trans b11_90
  have b12_425 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K12.b8 (by decide) (by decide)).trans b11_425
  have b12_426 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K12.b8 (by decide) (by decide)).trans b11_426
  have b12_427 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K12.b8 (by decide) (by decide)).trans b11_427
  have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [W12, g11_24]
  clear b11_427 b11_426 b11_425 w11_42c w11_428 b11_90 b11_87 b11_86 b11_85 b11_84 w11_288 w11_284 w11_8c w11_88 w11_84 w11_80 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 s11 X11 K11 P11 b10_87 b10_86 b10_85
  -- 0x29C: sb
  obtain ⟨n13, d13, s13, fr13, K13, W13, rg13⟩ := sv_sb F E12 s12 sv_at_29c (off' := 0x2A0) (c := 0x424)
    (by decide) (by rw [g12_2]; sv_addr) (by decide)
  have t13 : Steps n0 n13 := t12.trans d13
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.keep K13 (by decide)
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [rg13 sp, g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg13 (3 : Fin 32), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg13 (4 : Fin 32), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg13 (8 : Fin 32), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = tbp := by rw [rg13 (9 : Fin 32), g12_9]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [rg13 (18 : Fin 32), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [rg13 (19 : Fin 32), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = dg := by rw [rg13 (20 : Fin 32), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = rootp := by rw [rg13 (21 : Fin 32), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = ll := by rw [rg13 (22 : Fin 32), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = sgp := by rw [rg13 (23 : Fin 32), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [rg13 (24 : Fin 32), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = sgl := by rw [rg13 (25 : Fin 32), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = lp := by rw [rg13 (26 : Fin 32), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = tbl := by rw [rg13 (27 : Fin 32), g12_27]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1)] := keep_kk12.trans K13.toL
  clear keep_kk12
  have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K13.w32 (by decide) (by decide)).trans w12_80
  have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl6.len := (K13.w32 (by decide) (by decide)).trans w12_84
  have w13_88 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K13.w32 (by decide) (by decide)).trans w12_88
  have w13_8c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl6.len := (K13.w32 (by decide) (by decide)).trans w12_8c
  have w13_284 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K13.w32 (by decide) (by decide)).trans w12_284
  have w13_288 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K13.w32 (by decide) (by decide)).trans w12_288
  have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K13.w32 (by decide) (by decide)).trans w12_420
  have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K13.w32 (by decide) (by decide)).trans w12_428
  have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := (K13.w32 (by decide) (by decide)).trans w12_42c
  have b13_84 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := (K13.b8 (by decide) (by decide)).trans b12_84
  have b13_85 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K13.b8 (by decide) (by decide)).trans b12_85
  have b13_86 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K13.b8 (by decide) (by decide)).trans b12_86
  have b13_87 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K13.b8 (by decide) (by decide)).trans b12_87
  have b13_90 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl2.tag := (K13.b8 (by decide) (by decide)).trans b12_90
  have b13_425 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K13.b8 (by decide) (by decide)).trans b12_425
  have b13_426 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K13.b8 (by decide) (by decide)).trans b12_426
  have b13_427 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K13.b8 (by decide) (by decide)).trans b12_427
  have b13_424 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [W13, g12_8, lbu_low]
  clear w12_420 b12_427 b12_426 b12_425 b12_90 b12_87 b12_86 b12_85 b12_84 w12_42c w12_428 w12_288 w12_284 w12_8c w12_88 w12_84 w12_80 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 rg12 W12 K12 fr12 s12 d12
  -- 0x2A0
  obtain ⟨n14, c14, u14⟩ := s13.block svL52a0 E13.self svL52a0_end
    ⟨trivial, trivial, trivial⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have s14 : St n14.mem SV n14 0x2A6 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have rb14 : ∀ q, reg n14 q = (runBlock svL52a0 (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
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
  have g14_9 : reg n14 (9 : Fin 32) = tbp := by
    rw [rb14, runBlock_reg _ _ _ (9 : Fin 32) s13.zero (by decide), g13_9]
  have g14_18 : reg n14 (18 : Fin 32) = out := by
    rw [rb14, runBlock_reg _ _ _ (18 : Fin 32) s13.zero (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by
    rw [rb14, runBlock_reg _ _ _ (19 : Fin 32) s13.zero (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = dg := by
    rw [rb14, runBlock_reg _ _ _ (20 : Fin 32) s13.zero (by decide), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = rootp := by
    rw [rb14, runBlock_reg _ _ _ (21 : Fin 32) s13.zero (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = ll := by
    rw [rb14, runBlock_reg _ _ _ (22 : Fin 32) s13.zero (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = sgp := by
    rw [rb14, runBlock_reg _ _ _ (23 : Fin 32) s13.zero (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by
    rw [rb14, runBlock_reg _ _ _ (24 : Fin 32) s13.zero (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = sgl := by
    rw [rb14, runBlock_reg _ _ _ (25 : Fin 32) s13.zero (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = lp := by
    rw [rb14, runBlock_reg _ _ _ (26 : Fin 32) s13.zero (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = tbl := by
    rw [rb14, runBlock_reg _ _ _ (27 : Fin 32) s13.zero (by decide), g13_27]
  have g14_10 : reg n14 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svL52a0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g14_11 : reg n14 a1 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svL52a0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g13_2, g13_3, g13_4, g13_8, g13_9, g13_18, g13_19, g13_20, g13_21, g13_22, g13_23, g13_24, g13_25, g13_26, g13_27, s13.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1)] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m14]; exact w13_80
  have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 tl6.len := by rw [m14]; exact w13_84
  have w14_88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m14]; exact w13_88
  have w14_8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl6.len := by rw [m14]; exact w13_8c
  have w14_284 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m14]; exact w13_284
  have w14_288 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m14]; exact w13_288
  have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m14]; exact w13_420
  have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m14]; exact w13_428
  have w14_42c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 tl6.len := by rw [m14]; exact w13_42c
  have b14_84 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m14]; exact b13_84
  have b14_85 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x85) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m14]; exact b13_85
  have b14_86 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x86) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m14]; exact b13_86
  have b14_87 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x87) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m14]; exact b13_87
  have b14_90 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = BitVec.ofNat 8 tl2.tag := by rw [m14]; exact b13_90
  have b14_424 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m14]; exact b13_424
  have b14_425 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m14]; exact b13_425
  have b14_426 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m14]; exact b13_426
  have b14_427 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m14]; exact b13_427
  clear b13_424 b13_427 b13_426 b13_425 b13_90 b13_87 b13_86 b13_85 b13_84 w13_42c w13_428 w13_420 w13_288 w13_284 w13_8c w13_88 w13_84 w13_80 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 rg13 W13 K13 fr13 s13 d13
  -- 0x2A6: sv_algF
  obtain ⟨n15, c15, s15, sp15, rk15, K15, A15, R15, fr15⟩ := sv_algF (oc := 0x80) (dc := 0x420) (nl := tl6.len)
    F E14 s14 sv_at_2a6 sv_at_2aa (by decide) (by decide) g14_2 g14_10 g14_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w14_428 w14_42c ((tb_in.restW hr2).content hr6)
  have t15 : Steps n0 n15 := t14.trans c15
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.keepL K15 (by decide)
  rw [derAlgOf_congr (sv_pt fR14 ((tb_in.restW hr2).content hr6))] at R15
  rw [sv_mb fR14 ((tb_in.restW hr2).content hr6)] at A15
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk15 (3 : Fin 32) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk15 (4 : Fin 32) (by decide), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = ((BitVec.ofNat 32 tl6.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk15 (8 : Fin 32) (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = tbp := by rw [rk15 (9 : Fin 32) (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [rk15 (18 : Fin 32) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [rk15 (19 : Fin 32) (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = dg := by rw [rk15 (20 : Fin 32) (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = rootp := by rw [rk15 (21 : Fin 32) (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = ll := by rw [rk15 (22 : Fin 32) (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = sgp := by rw [rk15 (23 : Fin 32) (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [rk15 (24 : Fin 32) (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = sgl := by rw [rk15 (25 : Fin 32) (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = lp := by rw [rk15 (26 : Fin 32) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = tbl := by rw [rk15 (27 : Fin 32) (by decide), g14_27]
  have g15_2 : reg n15 sp = B + 0x21A0 := sp15
  obtain ⟨r15, hr15⟩ : ∃ r, derAlgOf M0 (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) (tl6.len) = r := ⟨_, rfl⟩
  rcases r15 with ab15 | ⟨⟨op15, ol15⟩, _ | ⟨prp15, pu15⟩⟩
  · rw [hr15] at R15
    obtain ⟨y0_15, y1_15⟩ := R15
    obtain ⟨ec_15, ey_15, hz_c15⟩ : ∃ b : BitVec 8, n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = b ∧ b.toNat < 0x27 :=
      ⟨_, y1_15, by sv_eb hr15⟩
    have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := keep_kk14.trans K15
    clear keep_kk14
    have w15_284 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K15.w32 (by decide) (by decide)).trans w14_284
    have w15_288 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K15.w32 (by decide) (by decide)).trans w14_288
    have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K15.w32 (by decide) (by decide)).trans w14_420
    have b15_424 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := (K15.b8 (by decide) (by decide)).trans b14_424
    have b15_425 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K15.b8 (by decide) (by decide)).trans b14_425
    have b15_426 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K15.b8 (by decide) (by decide)).trans b14_426
    have b15_427 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K15.b8 (by decide) (by decide)).trans b14_427
    have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := y0_15
    have b15_84 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ec_15 := ey_15
    clear b14_427 b14_426 b14_425 b14_424 b14_90 b14_87 b14_86 b14_85 b14_84 w14_42c w14_428 w14_420 w14_288 w14_284 w14_8c w14_88 w14_84 w14_80 g14_11 g14_10 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
    -- 0x2AE: lw
    obtain ⟨n16, d16, u16⟩ := s15.lw E15.self sv_at_2ae (off' := 0x2B0) (by decide)
      (by rw [g15_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s16 : St n16.mem SV n16 0x2B0 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
    have m16 : n16.mem = n15.mem := u16.mem
    have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
    have t16 : Steps n0 n16 := t15.trans (.single d16)
    have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
    have E16 : SvCode n16.mem := E15.fr F fr16
    have V16 : SvSaves B n16.mem v := V15.same m16
    have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
    have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
    have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
    have g16_9 : reg n16 (9 : Fin 32) = tbp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_9]
    have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, upd_ne (by decide) (by decide), g15_18]
    have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_19]
    have g16_20 : reg n16 (20 : Fin 32) = dg := by rw [u16.regs, upd_ne (by decide) (by decide), g15_20]
    have g16_21 : reg n16 (21 : Fin 32) = rootp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_21]
    have g16_22 : reg n16 (22 : Fin 32) = ll := by rw [u16.regs, upd_ne (by decide) (by decide), g15_22]
    have g16_23 : reg n16 (23 : Fin 32) = sgp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_23]
    have g16_24 : reg n16 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [u16.regs, upd_ne (by decide) (by decide), g15_24]
    have g16_25 : reg n16 (25 : Fin 32) = sgl := by rw [u16.regs, upd_ne (by decide) (by decide), g15_25]
    have g16_26 : reg n16 (26 : Fin 32) = lp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_26]
    have g16_27 : reg n16 (27 : Fin 32) = tbl := by rw [u16.regs, upd_ne (by decide) (by decide), g15_27]
    have g16_8 : reg n16 (8 : Fin 32) = 0 := by
      rw [u16.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g15_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w15_80]
    have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m16]; exact keep_kk15
    clear keep_kk15
    have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m16]; exact w15_80
    have w16_284 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m16]; exact w15_284
    have w16_288 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m16]; exact w15_288
    have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m16]; exact w15_420
    have b16_84 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ec_15 := by rw [m16]; exact b15_84
    have b16_424 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m16]; exact b15_424
    have b16_425 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m16]; exact b15_425
    have b16_426 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m16]; exact b15_426
    have b16_427 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m16]; exact b15_427
    clear b15_84 w15_80 b15_427 b15_426 b15_425 b15_424 w15_420 w15_288 w15_284 ey_15 y1_15 y0_15
    -- 0x2B0: branch, taken
    obtain ⟨n17, d17, u17⟩ := s16.taken E16.self 0x7A0 sv_at_2b0
      (by decide) (by rw [g16_8, s16.zero]; rfl)
    have s17 : St n17.mem SV n17 0x7A0 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
    have m17 : n17.mem = n16.mem := u17.mem
    have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
    have t17 : Steps n0 n17 := t16.trans (.single d17)
    have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
    have E17 : SvCode n17.mem := E16.fr F fr17
    have V17 : SvSaves B n17.mem v := V16.same m17
    have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, g16_2]
    have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, g16_3]
    have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, g16_4]
    have g17_8 : reg n17 (8 : Fin 32) = 0 := by rw [u17.regs, g16_8]
    have g17_9 : reg n17 (9 : Fin 32) = tbp := by rw [u17.regs, g16_9]
    have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, g16_18]
    have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, g16_19]
    have g17_20 : reg n17 (20 : Fin 32) = dg := by rw [u17.regs, g16_20]
    have g17_21 : reg n17 (21 : Fin 32) = rootp := by rw [u17.regs, g16_21]
    have g17_22 : reg n17 (22 : Fin 32) = ll := by rw [u17.regs, g16_22]
    have g17_23 : reg n17 (23 : Fin 32) = sgp := by rw [u17.regs, g16_23]
    have g17_24 : reg n17 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [u17.regs, g16_24]
    have g17_25 : reg n17 (25 : Fin 32) = sgl := by rw [u17.regs, g16_25]
    have g17_26 : reg n17 (26 : Fin 32) = lp := by rw [u17.regs, g16_26]
    have g17_27 : reg n17 (27 : Fin 32) = tbl := by rw [u17.regs, g16_27]
    have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m17]; exact keep_kk16
    clear keep_kk16
    have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m17]; exact w16_80
    have w17_284 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m17]; exact w16_284
    have w17_288 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m17]; exact w16_288
    have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m17]; exact w16_420
    have b17_84 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ec_15 := by rw [m17]; exact b16_84
    have b17_424 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m17]; exact b16_424
    have b17_425 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m17]; exact b16_425
    have b17_426 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m17]; exact b16_426
    have b17_427 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m17]; exact b16_427
    clear b16_427 b16_426 b16_425 b16_424 b16_84 w16_420 w16_288 w16_284 w16_80 g16_8 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_9 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
    -- 0x7A0: lbu
    obtain ⟨n18, d18, u18⟩ := s17.lbu E17.self sv_at_7a0 (off' := 0x7A4) (by decide)
    have s18 : St n18.mem SV n18 0x7A4 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
    have m18 : n18.mem = n17.mem := u18.mem
    have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
    have t18 : Steps n0 n18 := t17.trans (.single d18)
    have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
    have E18 : SvCode n18.mem := E17.fr F fr18
    have V18 : SvSaves B n18.mem v := V17.same m18
    have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_2]
    have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_3]
    have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_4]
    have g18_9 : reg n18 (9 : Fin 32) = tbp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_9]
    have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, upd_ne (by decide) (by decide), g17_18]
    have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_19]
    have g18_20 : reg n18 (20 : Fin 32) = dg := by rw [u18.regs, upd_ne (by decide) (by decide), g17_20]
    have g18_21 : reg n18 (21 : Fin 32) = rootp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_21]
    have g18_22 : reg n18 (22 : Fin 32) = ll := by rw [u18.regs, upd_ne (by decide) (by decide), g17_22]
    have g18_23 : reg n18 (23 : Fin 32) = sgp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_23]
    have g18_24 : reg n18 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [u18.regs, upd_ne (by decide) (by decide), g17_24]
    have g18_25 : reg n18 (25 : Fin 32) = sgl := by rw [u18.regs, upd_ne (by decide) (by decide), g17_25]
    have g18_26 : reg n18 (26 : Fin 32) = lp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_26]
    have g18_27 : reg n18 (27 : Fin 32) = tbl := by rw [u18.regs, upd_ne (by decide) (by decide), g17_27]
    have g18_8 : reg n18 (8 : Fin 32) = (ec_15).zeroExtend 32 := by
      rw [u18.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g17_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, b17_84]
    have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m18]; exact keep_kk17
    clear keep_kk17
    have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m18]; exact w17_80
    have w18_284 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m18]; exact w17_284
    have w18_288 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m18]; exact w17_288
    have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m18]; exact w17_420
    have b18_84 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = ec_15 := by rw [m18]; exact b17_84
    have b18_424 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m18]; exact b17_424
    have b18_425 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m18]; exact b17_425
    have b18_426 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m18]; exact b17_426
    have b18_427 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m18]; exact b17_427
    clear b17_427 b17_426 b17_425 b17_424 b17_84 w17_420 w17_288 w17_284 w17_80 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
    exact .inl ⟨(fun ⟨tl2', h0', tl6', h1', op15', ol15', prp15', pu15', h2', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr6] at h1'; cases h1'; rw [hr15] at h2'; cases h2'), sv_fail F E18 s18 t18 (fun x hx => (fR18 x hx).trans (fM x hx).symm) V18 hret g18_2 g18_18 hO g18_3 g18_4 (by rw [g18_8]; sv_code)⟩
  · rw [hr15] at R15
    obtain ⟨y0_15, y4_15, y8_15⟩ := R15
    have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := keep_kk14.trans K15
    clear keep_kk14
    have w15_284 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K15.w32 (by decide) (by decide)).trans w14_284
    have w15_288 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K15.w32 (by decide) (by decide)).trans w14_288
    have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K15.w32 (by decide) (by decide)).trans w14_420
    have b15_424 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := (K15.b8 (by decide) (by decide)).trans b14_424
    have b15_425 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K15.b8 (by decide) (by decide)).trans b14_425
    have b15_426 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K15.b8 (by decide) (by decide)).trans b14_426
    have b15_427 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K15.b8 (by decide) (by decide)).trans b14_427
    have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := y0_15
    have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := y4_15
    have w15_88 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := y8_15
    clear b14_427 b14_426 b14_425 b14_424 b14_90 b14_87 b14_86 b14_85 b14_84 w14_42c w14_428 w14_420 w14_288 w14_284 w14_8c w14_88 w14_84 w14_80 g14_11 g14_10 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
    -- 0x2AE: lw
    obtain ⟨n16, d16, u16⟩ := s15.lw E15.self sv_at_2ae (off' := 0x2B0) (by decide)
      (by rw [g15_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s16 : St n16.mem SV n16 0x2B0 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
    have m16 : n16.mem = n15.mem := u16.mem
    have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
    have t16 : Steps n0 n16 := t15.trans (.single d16)
    have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
    have E16 : SvCode n16.mem := E15.fr F fr16
    have V16 : SvSaves B n16.mem v := V15.same m16
    have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
    have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
    have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
    have g16_9 : reg n16 (9 : Fin 32) = tbp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_9]
    have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, upd_ne (by decide) (by decide), g15_18]
    have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_19]
    have g16_20 : reg n16 (20 : Fin 32) = dg := by rw [u16.regs, upd_ne (by decide) (by decide), g15_20]
    have g16_21 : reg n16 (21 : Fin 32) = rootp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_21]
    have g16_22 : reg n16 (22 : Fin 32) = ll := by rw [u16.regs, upd_ne (by decide) (by decide), g15_22]
    have g16_23 : reg n16 (23 : Fin 32) = sgp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_23]
    have g16_24 : reg n16 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [u16.regs, upd_ne (by decide) (by decide), g15_24]
    have g16_25 : reg n16 (25 : Fin 32) = sgl := by rw [u16.regs, upd_ne (by decide) (by decide), g15_25]
    have g16_26 : reg n16 (26 : Fin 32) = lp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_26]
    have g16_27 : reg n16 (27 : Fin 32) = tbl := by rw [u16.regs, upd_ne (by decide) (by decide), g15_27]
    have g16_8 : reg n16 (8 : Fin 32) = op15 := by
      rw [u16.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g15_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w15_80]
    have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m16]; exact keep_kk15
    clear keep_kk15
    have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m16]; exact w15_80
    have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m16]; exact w15_84
    have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := by rw [m16]; exact w15_88
    have w16_284 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m16]; exact w15_284
    have w16_288 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m16]; exact w15_288
    have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m16]; exact w15_420
    have b16_424 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m16]; exact b15_424
    have b16_425 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m16]; exact b15_425
    have b16_426 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m16]; exact b15_426
    have b16_427 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m16]; exact b15_427
    clear w15_88 w15_84 w15_80 b15_427 b15_426 b15_425 b15_424 w15_420 w15_288 w15_284 y8_15 y4_15 y0_15
    -- 0x2B0: branch, not taken
    obtain ⟨n17, d17, u17⟩ := s16.notTaken E16.self 0x2B4 sv_at_2b0
      (by decide) (by rw [g16_8, s16.zero]; exact br_beq_f (((tb_in.restW hr2).content hr6).algOid hr15).pos_ne)
    have s17 : St n17.mem SV n17 0x2B4 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
    have m17 : n17.mem = n16.mem := u17.mem
    have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
    have t17 : Steps n0 n17 := t16.trans (.single d17)
    have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
    have E17 : SvCode n17.mem := E16.fr F fr17
    have V17 : SvSaves B n17.mem v := V16.same m17
    have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, g16_2]
    have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, g16_3]
    have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, g16_4]
    have g17_8 : reg n17 (8 : Fin 32) = op15 := by rw [u17.regs, g16_8]
    have g17_9 : reg n17 (9 : Fin 32) = tbp := by rw [u17.regs, g16_9]
    have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, g16_18]
    have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, g16_19]
    have g17_20 : reg n17 (20 : Fin 32) = dg := by rw [u17.regs, g16_20]
    have g17_21 : reg n17 (21 : Fin 32) = rootp := by rw [u17.regs, g16_21]
    have g17_22 : reg n17 (22 : Fin 32) = ll := by rw [u17.regs, g16_22]
    have g17_23 : reg n17 (23 : Fin 32) = sgp := by rw [u17.regs, g16_23]
    have g17_24 : reg n17 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [u17.regs, g16_24]
    have g17_25 : reg n17 (25 : Fin 32) = sgl := by rw [u17.regs, g16_25]
    have g17_26 : reg n17 (26 : Fin 32) = lp := by rw [u17.regs, g16_26]
    have g17_27 : reg n17 (27 : Fin 32) = tbl := by rw [u17.regs, g16_27]
    have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m17]; exact keep_kk16
    clear keep_kk16
    have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m17]; exact w16_80
    have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m17]; exact w16_84
    have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := by rw [m17]; exact w16_88
    have w17_284 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m17]; exact w16_284
    have w17_288 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m17]; exact w16_288
    have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m17]; exact w16_420
    have b17_424 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m17]; exact b16_424
    have b17_425 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m17]; exact b16_425
    have b17_426 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m17]; exact b16_426
    have b17_427 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m17]; exact b16_427
    clear b16_427 b16_426 b16_425 b16_424 w16_420 w16_288 w16_284 w16_88 w16_84 w16_80 g16_8 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_9 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
    -- 0x2B4: lw
    obtain ⟨n18, d18, u18⟩ := s17.lw E17.self sv_at_2b4 (off' := 0x2B6) (by decide)
      (by rw [g17_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s18 : St n18.mem SV n18 0x2B6 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
    have m18 : n18.mem = n17.mem := u18.mem
    have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
    have t18 : Steps n0 n18 := t17.trans (.single d18)
    have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
    have E18 : SvCode n18.mem := E17.fr F fr18
    have V18 : SvSaves B n18.mem v := V17.same m18
    have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_2]
    have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_3]
    have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_4]
    have g18_8 : reg n18 (8 : Fin 32) = op15 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_8]
    have g18_9 : reg n18 (9 : Fin 32) = tbp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_9]
    have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, upd_ne (by decide) (by decide), g17_18]
    have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_19]
    have g18_20 : reg n18 (20 : Fin 32) = dg := by rw [u18.regs, upd_ne (by decide) (by decide), g17_20]
    have g18_21 : reg n18 (21 : Fin 32) = rootp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_21]
    have g18_22 : reg n18 (22 : Fin 32) = ll := by rw [u18.regs, upd_ne (by decide) (by decide), g17_22]
    have g18_23 : reg n18 (23 : Fin 32) = sgp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_23]
    have g18_24 : reg n18 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [u18.regs, upd_ne (by decide) (by decide), g17_24]
    have g18_25 : reg n18 (25 : Fin 32) = sgl := by rw [u18.regs, upd_ne (by decide) (by decide), g17_25]
    have g18_26 : reg n18 (26 : Fin 32) = lp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_26]
    have g18_27 : reg n18 (27 : Fin 32) = tbl := by rw [u18.regs, upd_ne (by decide) (by decide), g17_27]
    have g18_10 : reg n18 a0 = 0 := by
      rw [u18.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g17_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr, w17_88]
    have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m18]; exact keep_kk17
    clear keep_kk17
    have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m18]; exact w17_80
    have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m18]; exact w17_84
    have w18_88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := by rw [m18]; exact w17_88
    have w18_284 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m18]; exact w17_284
    have w18_288 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m18]; exact w17_288
    have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m18]; exact w17_420
    have b18_424 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m18]; exact b17_424
    have b18_425 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m18]; exact b17_425
    have b18_426 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m18]; exact b17_426
    have b18_427 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m18]; exact b17_427
    clear b17_427 b17_426 b17_425 b17_424 w17_420 w17_288 w17_284 w17_88 w17_84 w17_80 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
    -- 0x2B6: lw
    obtain ⟨n19, d19, u19⟩ := s18.lw E18.self sv_at_2b6 (off' := 0x2B8) (by decide)
      (by rw [g18_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s19 : St n19.mem SV n19 0x2B8 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
    have m19 : n19.mem = n18.mem := u19.mem
    have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
    have t19 : Steps n0 n19 := t18.trans (.single d19)
    have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
    have E19 : SvCode n19.mem := E18.fr F fr19
    have V19 : SvSaves B n19.mem v := V18.same m19
    have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
    have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
    have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
    have g19_8 : reg n19 (8 : Fin 32) = op15 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_8]
    have g19_9 : reg n19 (9 : Fin 32) = tbp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_9]
    have g19_10 : reg n19 a0 = 0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_10]
    have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
    have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
    have g19_20 : reg n19 (20 : Fin 32) = dg := by rw [u19.regs, upd_ne (by decide) (by decide), g18_20]
    have g19_21 : reg n19 (21 : Fin 32) = rootp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
    have g19_22 : reg n19 (22 : Fin 32) = ll := by rw [u19.regs, upd_ne (by decide) (by decide), g18_22]
    have g19_23 : reg n19 (23 : Fin 32) = sgp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_23]
    have g19_24 : reg n19 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [u19.regs, upd_ne (by decide) (by decide), g18_24]
    have g19_25 : reg n19 (25 : Fin 32) = sgl := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
    have g19_27 : reg n19 (27 : Fin 32) = tbl := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
    have g19_26 : reg n19 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
      rw [u19.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g18_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, w18_84]
    have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m19]; exact keep_kk18
    clear keep_kk18
    have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m19]; exact w18_80
    have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m19]; exact w18_84
    have w19_88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := by rw [m19]; exact w18_88
    have w19_284 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m19]; exact w18_284
    have w19_288 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m19]; exact w18_288
    have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m19]; exact w18_420
    have b19_424 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m19]; exact b18_424
    have b19_425 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m19]; exact b18_425
    have b19_426 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m19]; exact b18_426
    have b19_427 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m19]; exact b18_427
    clear b18_427 b18_426 b18_425 b18_424 w18_420 w18_288 w18_284 w18_88 w18_84 w18_80 g18_10 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
    -- 0x2B8
    obtain ⟨n20, c20, u20⟩ := s19.block svL52b8 E19.self svL52b8_end
      ⟨trivial, trivial⟩
    have m20 : n20.mem = n19.mem := u20.mem
    have s20 : St n20.mem SV n20 0x2BA (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
    have rb20 : ∀ q, reg n20 q = (runBlock svL52b8 (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
    have g20_8 : reg n20 (8 : Fin 32) = op15 := by
      rw [rb20, runBlock_reg _ _ _ (8 : Fin 32) s19.zero (by decide), g19_8]
    have g20_9 : reg n20 (9 : Fin 32) = tbp := by
      rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
    have g20_10 : reg n20 a0 = 0 := by
      rw [rb20, runBlock_reg _ _ _ a0 s19.zero (by decide), g19_10]
    have g20_18 : reg n20 (18 : Fin 32) = out := by
      rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
    have g20_19 : reg n20 (19 : Fin 32) = bp := by
      rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
    have g20_20 : reg n20 (20 : Fin 32) = dg := by
      rw [rb20, runBlock_reg _ _ _ (20 : Fin 32) s19.zero (by decide), g19_20]
    have g20_21 : reg n20 (21 : Fin 32) = rootp := by
      rw [rb20, runBlock_reg _ _ _ (21 : Fin 32) s19.zero (by decide), g19_21]
    have g20_22 : reg n20 (22 : Fin 32) = ll := by
      rw [rb20, runBlock_reg _ _ _ (22 : Fin 32) s19.zero (by decide), g19_22]
    have g20_23 : reg n20 (23 : Fin 32) = sgp := by
      rw [rb20, runBlock_reg _ _ _ (23 : Fin 32) s19.zero (by decide), g19_23]
    have g20_25 : reg n20 (25 : Fin 32) = sgl := by
      rw [rb20, runBlock_reg _ _ _ (25 : Fin 32) s19.zero (by decide), g19_25]
    have g20_26 : reg n20 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
      rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
    have g20_27 : reg n20 (27 : Fin 32) = tbl := by
      rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
    have g20_24 : reg n20 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb20]; simp +decide only [runBlock, BInstr.run, svL52b8, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m20]; exact keep_kk19
    clear keep_kk19
    have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m20]; exact w19_80
    have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m20]; exact w19_84
    have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := by rw [m20]; exact w19_88
    have w20_284 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m20]; exact w19_284
    have w20_288 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m20]; exact w19_288
    have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m20]; exact w19_420
    have b20_424 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m20]; exact b19_424
    have b20_425 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m20]; exact b19_425
    have b20_426 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m20]; exact b19_426
    have b20_427 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m20]; exact b19_427
    clear b19_427 b19_426 b19_425 b19_424 w19_420 w19_288 w19_284 w19_88 w19_84 w19_80 g19_26 g19_27 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_10 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
    -- 0x2BA: branch, taken
    obtain ⟨n21, d21, u21⟩ := s20.taken E20.self 0x2DE sv_at_2ba
      (by decide) (by rw [g20_10, s20.zero]; rfl)
    have s21 : St n21.mem SV n21 0x2DE (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
    have m21 : n21.mem = n20.mem := u21.mem
    have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
    have t21 : Steps n0 n21 := t20.trans (.single d21)
    have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
    have E21 : SvCode n21.mem := E20.fr F fr21
    have V21 : SvSaves B n21.mem v := V20.same m21
    have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, g20_2]
    have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, g20_3]
    have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, g20_4]
    have g21_8 : reg n21 (8 : Fin 32) = op15 := by rw [u21.regs, g20_8]
    have g21_9 : reg n21 (9 : Fin 32) = tbp := by rw [u21.regs, g20_9]
    have g21_10 : reg n21 a0 = 0 := by rw [u21.regs, g20_10]
    have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, g20_19]
    have g21_20 : reg n21 (20 : Fin 32) = dg := by rw [u21.regs, g20_20]
    have g21_21 : reg n21 (21 : Fin 32) = rootp := by rw [u21.regs, g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = ll := by rw [u21.regs, g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = sgp := by rw [u21.regs, g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u21.regs, g20_24]
    have g21_25 : reg n21 (25 : Fin 32) = sgl := by rw [u21.regs, g20_25]
    have g21_26 : reg n21 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u21.regs, g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = tbl := by rw [u21.regs, g20_27]
    have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m21]; exact keep_kk20
    clear keep_kk20
    have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m21]; exact w20_80
    have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m21]; exact w20_84
    have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := by rw [m21]; exact w20_88
    have w21_284 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m21]; exact w20_284
    have w21_288 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m21]; exact w20_288
    have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m21]; exact w20_420
    have b21_424 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m21]; exact b20_424
    have b21_425 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m21]; exact b20_425
    have b21_426 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m21]; exact b20_426
    have b21_427 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m21]; exact b20_427
    clear b20_427 b20_426 b20_425 b20_424 w20_420 w20_288 w20_284 w20_88 w20_84 w20_80 g20_24 g20_27 g20_26 g20_25 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_10 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
    -- 0x2DE
    obtain ⟨n22, c22, u22⟩ := s21.block svL52de E21.self svL52de_end
      ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have s22 : St n22.mem SV n22 0x2EC (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have rb22 : ∀ q, reg n22 q = (runBlock svL52de (n21.mem, reg n21)).2 q := fun q => by rw [u22.regs]
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
    have g22_8 : reg n22 (8 : Fin 32) = op15 := by
      rw [rb22, runBlock_reg _ _ _ (8 : Fin 32) s21.zero (by decide), g21_8]
    have g22_9 : reg n22 (9 : Fin 32) = tbp := by
      rw [rb22, runBlock_reg _ _ _ (9 : Fin 32) s21.zero (by decide), g21_9]
    have g22_18 : reg n22 (18 : Fin 32) = out := by
      rw [rb22, runBlock_reg _ _ _ (18 : Fin 32) s21.zero (by decide), g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by
      rw [rb22, runBlock_reg _ _ _ (19 : Fin 32) s21.zero (by decide), g21_19]
    have g22_20 : reg n22 (20 : Fin 32) = dg := by
      rw [rb22, runBlock_reg _ _ _ (20 : Fin 32) s21.zero (by decide), g21_20]
    have g22_21 : reg n22 (21 : Fin 32) = rootp := by
      rw [rb22, runBlock_reg _ _ _ (21 : Fin 32) s21.zero (by decide), g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = ll := by
      rw [rb22, runBlock_reg _ _ _ (22 : Fin 32) s21.zero (by decide), g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = sgp := by
      rw [rb22, runBlock_reg _ _ _ (23 : Fin 32) s21.zero (by decide), g21_23]
    have g22_24 : reg n22 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb22, runBlock_reg _ _ _ (24 : Fin 32) s21.zero (by decide), g21_24]
    have g22_25 : reg n22 (25 : Fin 32) = sgl := by
      rw [rb22, runBlock_reg _ _ _ (25 : Fin 32) s21.zero (by decide), g21_25]
    have g22_26 : reg n22 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
      rw [rb22, runBlock_reg _ _ _ (26 : Fin 32) s21.zero (by decide), g21_26]
    have g22_27 : reg n22 (27 : Fin 32) = tbl := by
      rw [rb22, runBlock_reg _ _ _ (27 : Fin 32) s21.zero (by decide), g21_27]
    have g22_10 : reg n22 a0 = op15 := by
      rw [rb22]; simp +decide only [runBlock, BInstr.run, svL52de, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_10, g21_18, g21_19, g21_20, g21_21, g21_22, g21_23, g21_24, g21_25, g21_26, g21_27, s21.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g22_11 : reg n22 a1 = BitVec.ofNat 32 ol15 := by
      rw [rb22]; simp +decide only [runBlock, BInstr.run, svL52de, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_10, g21_18, g21_19, g21_20, g21_21, g21_22, g21_23, g21_24, g21_25, g21_26, g21_27, s21.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g22_12 : reg n22 a2 = BitVec.ofNat 32 (img% svOidEcPublicKeyAddress) := by
      rw [rb22]; simp +decide only [runBlock, BInstr.run, svL52de, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_10, g21_18, g21_19, g21_20, g21_21, g21_22, g21_23, g21_24, g21_25, g21_26, g21_27, s21.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g22_13 : reg n22 a3 = BitVec.ofNat 32 0x7 := by
      rw [rb22]; simp +decide only [runBlock, BInstr.run, svL52de, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_10, g21_18, g21_19, g21_20, g21_21, g21_22, g21_23, g21_24, g21_25, g21_26, g21_27, s21.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m22]; exact w21_80
    have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m22]; exact w21_84
    have w22_88 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := by rw [m22]; exact w21_88
    have w22_284 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m22]; exact w21_284
    have w22_288 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m22]; exact w21_288
    have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m22]; exact w21_420
    have b22_424 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m22]; exact b21_424
    have b22_425 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m22]; exact b21_425
    have b22_426 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m22]; exact b21_426
    have b22_427 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m22]; exact b21_427
    clear b21_427 b21_426 b21_425 b21_424 w21_420 w21_288 w21_284 w21_88 w21_84 w21_80 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_10 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
    -- 0x2EC: sv_sneF
    obtain ⟨n23, c23, s23, rk23, a0_23, K23, fr23⟩ := sv_sneF (pl := ol15) (ql := 7)
      F E22 s22 sv_at_2ec sv_at_2f0 (by decide) (by decide) g22_2
      g22_10 g22_11 g22_12 g22_13 (.inl (((tb_in.restW hr2).content hr6).algOid hr15)) (.inr ⟨by decide, by decide⟩)
    have t23 : Steps n0 n23 := t22.trans c23
    have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
    have E23 : SvCode n23.mem := E22.fr F fr23
    have V23 : SvSaves B n23.mem v := V22.keepL K23 (by decide)
    rw [sv_mbRo FW fR22 (.inl (((tb_in.restW hr2).content hr6).algOid hr15)), sv_mbRo FW fR22 (.inr ⟨by decide, by decide⟩)] at a0_23
    have g23_2 : reg n23 sp = B + 0x21A0 := by rw [rk23 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g22_2]
    have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk23 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g22_3]
    have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk23 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g22_4]
    have g23_8 : reg n23 (8 : Fin 32) = op15 := by rw [rk23 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g22_8]
    have g23_9 : reg n23 (9 : Fin 32) = tbp := by rw [rk23 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g22_9]
    have g23_18 : reg n23 (18 : Fin 32) = out := by rw [rk23 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g22_18]
    have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [rk23 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g22_19]
    have g23_20 : reg n23 (20 : Fin 32) = dg := by rw [rk23 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g22_20]
    have g23_21 : reg n23 (21 : Fin 32) = rootp := by rw [rk23 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g22_21]
    have g23_22 : reg n23 (22 : Fin 32) = ll := by rw [rk23 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g22_22]
    have g23_23 : reg n23 (23 : Fin 32) = sgp := by rw [rk23 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g22_23]
    have g23_24 : reg n23 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk23 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g22_24]
    have g23_25 : reg n23 (25 : Fin 32) = sgl := by rw [rk23 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g22_25]
    have g23_26 : reg n23 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [rk23 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g22_26]
    have g23_27 : reg n23 (27 : Fin 32) = tbl := by rw [rk23 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g22_27]
    have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := keep_kk22.trans K23
    clear keep_kk22
    have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := (K23.w32 (by decide) (by decide)).trans w22_80
    have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := (K23.w32 (by decide) (by decide)).trans w22_84
    have w23_88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := (K23.w32 (by decide) (by decide)).trans w22_88
    have w23_284 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K23.w32 (by decide) (by decide)).trans w22_284
    have w23_288 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K23.w32 (by decide) (by decide)).trans w22_288
    have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K23.w32 (by decide) (by decide)).trans w22_420
    have b23_424 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := (K23.b8 (by decide) (by decide)).trans b22_424
    have b23_425 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K23.b8 (by decide) (by decide)).trans b22_425
    have b23_426 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K23.b8 (by decide) (by decide)).trans b22_426
    have b23_427 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K23.b8 (by decide) (by decide)).trans b22_427
    clear b22_427 b22_426 b22_425 b22_424 w22_420 w22_288 w22_284 w22_88 w22_84 w22_80 g22_13 g22_12 g22_11 g22_10 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 rb22 s22 m22 u22 c22
    -- 0x2F4
    obtain ⟨n24, c24, u24⟩ := s23.block svL52f4 E23.self svL52f4_end
      ⟨trivial, trivial⟩
    have m24 : n24.mem = n23.mem := u24.mem
    have s24 : St n24.mem SV n24 0x2F6 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
    have rb24 : ∀ q, reg n24 q = (runBlock svL52f4 (n23.mem, reg n23)).2 q := fun q => by rw [u24.regs]
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
    have g24_9 : reg n24 (9 : Fin 32) = tbp := by
      rw [rb24, runBlock_reg _ _ _ (9 : Fin 32) s23.zero (by decide), g23_9]
    have g24_18 : reg n24 (18 : Fin 32) = out := by
      rw [rb24, runBlock_reg _ _ _ (18 : Fin 32) s23.zero (by decide), g23_18]
    have g24_19 : reg n24 (19 : Fin 32) = bp := by
      rw [rb24, runBlock_reg _ _ _ (19 : Fin 32) s23.zero (by decide), g23_19]
    have g24_20 : reg n24 (20 : Fin 32) = dg := by
      rw [rb24, runBlock_reg _ _ _ (20 : Fin 32) s23.zero (by decide), g23_20]
    have g24_21 : reg n24 (21 : Fin 32) = rootp := by
      rw [rb24, runBlock_reg _ _ _ (21 : Fin 32) s23.zero (by decide), g23_21]
    have g24_22 : reg n24 (22 : Fin 32) = ll := by
      rw [rb24, runBlock_reg _ _ _ (22 : Fin 32) s23.zero (by decide), g23_22]
    have g24_23 : reg n24 (23 : Fin 32) = sgp := by
      rw [rb24, runBlock_reg _ _ _ (23 : Fin 32) s23.zero (by decide), g23_23]
    have g24_24 : reg n24 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb24, runBlock_reg _ _ _ (24 : Fin 32) s23.zero (by decide), g23_24]
    have g24_25 : reg n24 (25 : Fin 32) = sgl := by
      rw [rb24, runBlock_reg _ _ _ (25 : Fin 32) s23.zero (by decide), g23_25]
    have g24_26 : reg n24 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
      rw [rb24, runBlock_reg _ _ _ (26 : Fin 32) s23.zero (by decide), g23_26]
    have g24_27 : reg n24 (27 : Fin 32) = tbl := by
      rw [rb24, runBlock_reg _ _ _ (27 : Fin 32) s23.zero (by decide), g23_27]
    have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
      rw [rb24]; simp +decide only [runBlock, BInstr.run, svL52f4, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_18, g23_19, g23_20, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m24]; exact keep_kk23
    clear keep_kk23
    have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m24]; exact w23_80
    have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m24]; exact w23_84
    have w24_88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := by rw [m24]; exact w23_88
    have w24_284 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m24]; exact w23_284
    have w24_288 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m24]; exact w23_288
    have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m24]; exact w23_420
    have b24_424 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m24]; exact b23_424
    have b24_425 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m24]; exact b23_425
    have b24_426 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m24]; exact b23_426
    have b24_427 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m24]; exact b23_427
    clear b23_427 b23_426 b23_425 b23_424 w23_420 w23_288 w23_284 w23_88 w23_84 w23_80 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 K23 a0_23 rk23 s23 c23
    -- 0x2F6: branch, taken
    obtain ⟨n25, d25, u25⟩ := s24.taken E24.self 0x7A4 sv_at_2f6
      (by decide) (by rw [g24_24, s24.zero]; decide)
    have s25 : St n25.mem SV n25 0x7A4 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
    have m25 : n25.mem = n24.mem := u25.mem
    have fr25 : ∀ x, SvR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
    have t25 : Steps n0 n25 := t24.trans (.single d25)
    have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
    have E25 : SvCode n25.mem := E24.fr F fr25
    have V25 : SvSaves B n25.mem v := V24.same m25
    have g25_2 : reg n25 sp = B + 0x21A0 := by rw [u25.regs, g24_2]
    have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u25.regs, g24_3]
    have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u25.regs, g24_4]
    have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u25.regs, g24_8]
    have g25_9 : reg n25 (9 : Fin 32) = tbp := by rw [u25.regs, g24_9]
    have g25_18 : reg n25 (18 : Fin 32) = out := by rw [u25.regs, g24_18]
    have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [u25.regs, g24_19]
    have g25_20 : reg n25 (20 : Fin 32) = dg := by rw [u25.regs, g24_20]
    have g25_21 : reg n25 (21 : Fin 32) = rootp := by rw [u25.regs, g24_21]
    have g25_22 : reg n25 (22 : Fin 32) = ll := by rw [u25.regs, g24_22]
    have g25_23 : reg n25 (23 : Fin 32) = sgp := by rw [u25.regs, g24_23]
    have g25_24 : reg n25 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u25.regs, g24_24]
    have g25_25 : reg n25 (25 : Fin 32) = sgl := by rw [u25.regs, g24_25]
    have g25_26 : reg n25 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u25.regs, g24_26]
    have g25_27 : reg n25 (27 : Fin 32) = tbl := by rw [u25.regs, g24_27]
    have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m25]; exact keep_kk24
    clear keep_kk24
    have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m25]; exact w24_80
    have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m25]; exact w24_84
    have w25_88 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = 0 := by rw [m25]; exact w24_88
    have w25_284 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m25]; exact w24_284
    have w25_288 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m25]; exact w24_288
    have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m25]; exact w24_420
    have b25_424 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m25]; exact b24_424
    have b25_425 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m25]; exact b24_425
    have b25_426 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m25]; exact b24_426
    have b25_427 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m25]; exact b24_427
    clear b24_427 b24_426 b24_425 b24_424 w24_420 w24_288 w24_284 w24_88 w24_84 w24_80 g24_8 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_9 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
    exact .inl ⟨(fun ⟨tl2', h0', tl6', h1', op15', ol15', prp15', pu15', h2', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr6] at h1'; cases h1'; rw [hr15] at h2'; cases h2'), sv_fail F E25 s25 t25 (fun x hx => (fR25 x hx).trans (fM x hx).symm) V25 hret g25_2 g25_18 hO g25_3 g25_4 (by rw [g25_8]; sv_code)⟩
  obtain ⟨ta15, hta15⟩ := alg_ok_elem hr15
  rw [hr15] at R15
  obtain ⟨y0_15, y4_15, y8_15, y12_15, y24_15⟩ := R15
  obtain ⟨d8_15, d12_15⟩ := A15 ta15 hta15
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := keep_kk14.trans K15
  clear keep_kk14
  have w15_284 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K15.w32 (by decide) (by decide)).trans w14_284
  have w15_288 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K15.w32 (by decide) (by decide)).trans w14_288
  have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K15.w32 (by decide) (by decide)).trans w14_420
  have b15_424 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := (K15.b8 (by decide) (by decide)).trans b14_424
  have b15_425 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K15.b8 (by decide) (by decide)).trans b14_425
  have b15_426 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K15.b8 (by decide) (by decide)).trans b14_426
  have b15_427 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K15.b8 (by decide) (by decide)).trans b14_427
  have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := y0_15
  have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := y4_15
  have w15_88 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := y8_15
  have w15_8c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := y12_15
  have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := d8_15
  have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := d12_15
  have b15_98 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := y24_15
  clear b14_427 b14_426 b14_425 b14_424 b14_90 b14_87 b14_86 b14_85 b14_84 w14_42c w14_428 w14_420 w14_288 w14_284 w14_8c w14_88 w14_84 w14_80 g14_11 g14_10 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
  -- 0x2AE: lw
  obtain ⟨n16, d16, u16⟩ := s15.lw E15.self sv_at_2ae (off' := 0x2B0) (by decide)
    (by rw [g15_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s16 : St n16.mem SV n16 0x2B0 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans (.single d16)
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
  have g16_9 : reg n16 (9 : Fin 32) = tbp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_9]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, upd_ne (by decide) (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = dg := by rw [u16.regs, upd_ne (by decide) (by decide), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = rootp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = ll := by rw [u16.regs, upd_ne (by decide) (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = sgp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [u16.regs, upd_ne (by decide) (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = sgl := by rw [u16.regs, upd_ne (by decide) (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = lp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = tbl := by rw [u16.regs, upd_ne (by decide) (by decide), g15_27]
  have g16_8 : reg n16 (8 : Fin 32) = op15 := by
    rw [u16.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g15_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w15_80]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m16]; exact w15_80
  have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m16]; exact w15_84
  have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m16]; exact w15_88
  have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m16]; exact w15_8c
  have w16_284 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m16]; exact w15_284
  have w16_288 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m16]; exact w15_288
  have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m16]; exact w15_420
  have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m16]; exact w15_428
  have w16_42c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m16]; exact w15_42c
  have b16_98 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m16]; exact b15_98
  have b16_424 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m16]; exact b15_424
  have b16_425 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m16]; exact b15_425
  have b16_426 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m16]; exact b15_426
  have b16_427 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m16]; exact b15_427
  clear b15_98 w15_42c w15_428 w15_8c w15_88 w15_84 w15_80 b15_427 b15_426 b15_425 b15_424 w15_420 w15_288 w15_284 d12_15 d8_15 y24_15 y12_15 y8_15 y4_15 y0_15 g15_2 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_8 g15_4 g15_3 V15 E15 fR15 t15 fr15 A15 K15 rk15 sp15 s15 c15
  -- 0x2B0: branch, not taken
  obtain ⟨n17, d17, u17⟩ := s16.notTaken E16.self 0x2B4 sv_at_2b0
    (by decide) (by rw [g16_8, s16.zero]; exact br_beq_f (((tb_in.restW hr2).content hr6).algOid hr15).pos_ne)
  have s17 : St n17.mem SV n17 0x2B4 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans (.single d17)
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = op15 := by rw [u17.regs, g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = tbp := by rw [u17.regs, g16_9]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = dg := by rw [u17.regs, g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = rootp := by rw [u17.regs, g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = ll := by rw [u17.regs, g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = sgp := by rw [u17.regs, g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [u17.regs, g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = sgl := by rw [u17.regs, g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = lp := by rw [u17.regs, g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = tbl := by rw [u17.regs, g16_27]
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m17]; exact w16_80
  have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m17]; exact w16_84
  have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m17]; exact w16_88
  have w17_8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m17]; exact w16_8c
  have w17_284 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m17]; exact w16_284
  have w17_288 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m17]; exact w16_288
  have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m17]; exact w16_420
  have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m17]; exact w16_428
  have w17_42c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m17]; exact w16_42c
  have b17_98 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m17]; exact b16_98
  have b17_424 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m17]; exact b16_424
  have b17_425 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m17]; exact b16_425
  have b17_426 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m17]; exact b16_426
  have b17_427 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m17]; exact b16_427
  clear b16_427 b16_426 b16_425 b16_424 b16_98 w16_42c w16_428 w16_420 w16_288 w16_284 w16_8c w16_88 w16_84 w16_80 g16_8 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_9 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
  -- 0x2B4: lw
  obtain ⟨n18, d18, u18⟩ := s17.lw E17.self sv_at_2b4 (off' := 0x2B6) (by decide)
    (by rw [g17_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s18 : St n18.mem SV n18 0x2B6 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans (.single d18)
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = op15 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = tbp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, upd_ne (by decide) (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = dg := by rw [u18.regs, upd_ne (by decide) (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = rootp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = ll := by rw [u18.regs, upd_ne (by decide) (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = sgp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [u18.regs, upd_ne (by decide) (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = sgl := by rw [u18.regs, upd_ne (by decide) (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = lp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = tbl := by rw [u18.regs, upd_ne (by decide) (by decide), g17_27]
  have g18_10 : reg n18 a0 = prp15 + BitVec.ofNat 32 pu15.header := by
    rw [u18.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g17_2, show B + 0x21A0 + 0x88 = B + 0x21A0 + BitVec.ofNat 32 0x88 by sv_addr, w17_88]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m18]; exact w17_80
  have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m18]; exact w17_84
  have w18_88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m18]; exact w17_88
  have w18_8c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m18]; exact w17_8c
  have w18_284 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m18]; exact w17_284
  have w18_288 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m18]; exact w17_288
  have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m18]; exact w17_420
  have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m18]; exact w17_428
  have w18_42c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m18]; exact w17_42c
  have b18_98 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m18]; exact b17_98
  have b18_424 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m18]; exact b17_424
  have b18_425 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m18]; exact b17_425
  have b18_426 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m18]; exact b17_426
  have b18_427 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m18]; exact b17_427
  clear b17_427 b17_426 b17_425 b17_424 b17_98 w17_42c w17_428 w17_420 w17_288 w17_284 w17_8c w17_88 w17_84 w17_80 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
  -- 0x2B6: lw
  obtain ⟨n19, d19, u19⟩ := s18.lw E18.self sv_at_2b6 (off' := 0x2B8) (by decide)
    (by rw [g18_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s19 : St n19.mem SV n19 0x2B8 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans (.single d19)
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = op15 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = tbp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_9]
  have g19_10 : reg n19 a0 = prp15 + BitVec.ofNat 32 pu15.header := by rw [u19.regs, upd_ne (by decide) (by decide), g18_10]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = dg := by rw [u19.regs, upd_ne (by decide) (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = rootp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = ll := by rw [u19.regs, upd_ne (by decide) (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = sgp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [u19.regs, upd_ne (by decide) (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = sgl := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
  have g19_27 : reg n19 (27 : Fin 32) = tbl := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
  have g19_26 : reg n19 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
    rw [u19.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g18_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, w18_84]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m19]; exact w18_80
  have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m19]; exact w18_84
  have w19_88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m19]; exact w18_88
  have w19_8c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m19]; exact w18_8c
  have w19_284 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m19]; exact w18_284
  have w19_288 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m19]; exact w18_288
  have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m19]; exact w18_420
  have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m19]; exact w18_428
  have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m19]; exact w18_42c
  have b19_98 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m19]; exact b18_98
  have b19_424 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m19]; exact b18_424
  have b19_425 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m19]; exact b18_425
  have b19_426 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m19]; exact b18_426
  have b19_427 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m19]; exact b18_427
  clear b18_427 b18_426 b18_425 b18_424 b18_98 w18_42c w18_428 w18_420 w18_288 w18_284 w18_8c w18_88 w18_84 w18_80 g18_10 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
  -- 0x2B8
  obtain ⟨n20, c20, u20⟩ := s19.block svL52b8 E19.self svL52b8_end
    ⟨trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem SV n20 0x2BA (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock svL52b8 (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
  have g20_8 : reg n20 (8 : Fin 32) = op15 := by
    rw [rb20, runBlock_reg _ _ _ (8 : Fin 32) s19.zero (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = tbp := by
    rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
  have g20_10 : reg n20 a0 = prp15 + BitVec.ofNat 32 pu15.header := by
    rw [rb20, runBlock_reg _ _ _ a0 s19.zero (by decide), g19_10]
  have g20_18 : reg n20 (18 : Fin 32) = out := by
    rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by
    rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = dg := by
    rw [rb20, runBlock_reg _ _ _ (20 : Fin 32) s19.zero (by decide), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = rootp := by
    rw [rb20, runBlock_reg _ _ _ (21 : Fin 32) s19.zero (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = ll := by
    rw [rb20, runBlock_reg _ _ _ (22 : Fin 32) s19.zero (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = sgp := by
    rw [rb20, runBlock_reg _ _ _ (23 : Fin 32) s19.zero (by decide), g19_23]
  have g20_25 : reg n20 (25 : Fin 32) = sgl := by
    rw [rb20, runBlock_reg _ _ _ (25 : Fin 32) s19.zero (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
    rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = tbl := by
    rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
  have g20_24 : reg n20 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svL52b8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m20]; exact w19_80
  have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m20]; exact w19_84
  have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m20]; exact w19_88
  have w20_8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m20]; exact w19_8c
  have w20_284 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m20]; exact w19_284
  have w20_288 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m20]; exact w19_288
  have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m20]; exact w19_420
  have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m20]; exact w19_428
  have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m20]; exact w19_42c
  have b20_98 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m20]; exact b19_98
  have b20_424 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m20]; exact b19_424
  have b20_425 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m20]; exact b19_425
  have b20_426 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m20]; exact b19_426
  have b20_427 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m20]; exact b19_427
  clear b19_427 b19_426 b19_425 b19_424 b19_98 w19_42c w19_428 w19_420 w19_288 w19_284 w19_8c w19_88 w19_84 w19_80 g19_26 g19_27 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_10 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
  -- 0x2BA: branch, not taken
  obtain ⟨n21, d21, u21⟩ := s20.notTaken E20.self 0x2BC sv_at_2ba
    (by decide) (by rw [g20_10, s20.zero]; exact br_beq_f (((tb_in.restW hr2).content hr6).algParams hr15))
  have s21 : St n21.mem SV n21 0x2BC (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans (.single d21)
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = op15 := by rw [u21.regs, g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = tbp := by rw [u21.regs, g20_9]
  have g21_10 : reg n21 a0 = prp15 + BitVec.ofNat 32 pu15.header := by rw [u21.regs, g20_10]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = dg := by rw [u21.regs, g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = rootp := by rw [u21.regs, g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = ll := by rw [u21.regs, g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = sgp := by rw [u21.regs, g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u21.regs, g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = sgl := by rw [u21.regs, g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u21.regs, g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = tbl := by rw [u21.regs, g20_27]
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m21]; exact w20_80
  have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m21]; exact w20_84
  have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m21]; exact w20_88
  have w21_8c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m21]; exact w20_8c
  have w21_284 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m21]; exact w20_284
  have w21_288 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m21]; exact w20_288
  have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m21]; exact w20_420
  have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m21]; exact w20_428
  have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m21]; exact w20_42c
  have b21_98 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m21]; exact b20_98
  have b21_424 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m21]; exact b20_424
  have b21_425 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m21]; exact b20_425
  have b21_426 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m21]; exact b20_426
  have b21_427 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m21]; exact b20_427
  clear b20_427 b20_426 b20_425 b20_424 b20_98 w20_42c w20_428 w20_420 w20_288 w20_284 w20_8c w20_88 w20_84 w20_80 g20_24 g20_27 g20_26 g20_25 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_10 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  -- 0x2BC: lbu
  obtain ⟨n22, d22, u22⟩ := s21.lbu E21.self sv_at_2bc (off' := 0x2C0) (by decide)
  have s22 : St n22.mem SV n22 0x2C0 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans (.single d22)
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = op15 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = tbp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_9]
  have g22_10 : reg n22 a0 = prp15 + BitVec.ofNat 32 pu15.header := by rw [u22.regs, upd_ne (by decide) (by decide), g21_10]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, upd_ne (by decide) (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = dg := by rw [u22.regs, upd_ne (by decide) (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = rootp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = ll := by rw [u22.regs, upd_ne (by decide) (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = sgp := by rw [u22.regs, upd_ne (by decide) (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = sgl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = tbl := by rw [u22.regs, upd_ne (by decide) (by decide), g21_27]
  have g22_11 : reg n22 a1 = (BitVec.ofNat 8 pu15.tag).zeroExtend 32 := by
    rw [u22.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g21_2, show B + 0x21A0 + 0x98 = B + 0x21A0 + BitVec.ofNat 32 0x98 by sv_addr, b21_98]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m22]; exact w21_80
  have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m22]; exact w21_84
  have w22_88 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m22]; exact w21_88
  have w22_8c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m22]; exact w21_8c
  have w22_284 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m22]; exact w21_284
  have w22_288 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m22]; exact w21_288
  have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m22]; exact w21_420
  have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m22]; exact w21_428
  have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m22]; exact w21_42c
  have b22_98 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m22]; exact b21_98
  have b22_424 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m22]; exact b21_424
  have b22_425 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m22]; exact b21_425
  have b22_426 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m22]; exact b21_426
  have b22_427 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m22]; exact b21_427
  clear b21_427 b21_426 b21_425 b21_424 b21_98 w21_42c w21_428 w21_420 w21_288 w21_284 w21_8c w21_88 w21_84 w21_80 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_10 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
  -- 0x2C0
  obtain ⟨n23, c23, u23⟩ := s22.block svL52c0 E22.self svL52c0_end
    ⟨trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem SV n23 0x2C2 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock svL52c0 (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
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
  have g23_8 : reg n23 (8 : Fin 32) = op15 := by
    rw [rb23, runBlock_reg _ _ _ (8 : Fin 32) s22.zero (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = tbp := by
    rw [rb23, runBlock_reg _ _ _ (9 : Fin 32) s22.zero (by decide), g22_9]
  have g23_10 : reg n23 a0 = prp15 + BitVec.ofNat 32 pu15.header := by
    rw [rb23, runBlock_reg _ _ _ a0 s22.zero (by decide), g22_10]
  have g23_11 : reg n23 a1 = (BitVec.ofNat 8 pu15.tag).zeroExtend 32 := by
    rw [rb23, runBlock_reg _ _ _ a1 s22.zero (by decide), g22_11]
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
  have g23_23 : reg n23 (23 : Fin 32) = sgp := by
    rw [rb23, runBlock_reg _ _ _ (23 : Fin 32) s22.zero (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb23, runBlock_reg _ _ _ (24 : Fin 32) s22.zero (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = sgl := by
    rw [rb23, runBlock_reg _ _ _ (25 : Fin 32) s22.zero (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
    rw [rb23, runBlock_reg _ _ _ (26 : Fin 32) s22.zero (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = tbl := by
    rw [rb23, runBlock_reg _ _ _ (27 : Fin 32) s22.zero (by decide), g22_27]
  have g23_12 : reg n23 a2 = BitVec.ofNat 32 0x6 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svL52c0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_10, g22_11, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m23]; exact w22_80
  have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m23]; exact w22_84
  have w23_88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m23]; exact w22_88
  have w23_8c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m23]; exact w22_8c
  have w23_284 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m23]; exact w22_284
  have w23_288 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m23]; exact w22_288
  have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m23]; exact w22_420
  have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m23]; exact w22_428
  have w23_42c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m23]; exact w22_42c
  have b23_98 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m23]; exact b22_98
  have b23_424 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m23]; exact b22_424
  have b23_425 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m23]; exact b22_425
  have b23_426 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m23]; exact b22_426
  have b23_427 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m23]; exact b22_427
  clear b22_427 b22_426 b22_425 b22_424 b22_98 w22_42c w22_428 w22_420 w22_288 w22_284 w22_8c w22_88 w22_84 w22_80 g22_11 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_10 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
  by_cases hz_23 : BitVec.ofNat 8 pu15.tag = BitVec.ofNat 8 6
  rotate_left
  · -- 0x2C2: branch, taken
    obtain ⟨n24, d24, u24⟩ := s23.taken E23.self 0x2DE sv_at_2c2
      (by decide) (by rw [g23_11, g23_12]; exact br_bne_byte_t (by decide) hz_23)
    have s24 : St n24.mem SV n24 0x2DE (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
    have m24 : n24.mem = n23.mem := u24.mem
    have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
    have t24 : Steps n0 n24 := t23.trans (.single d24)
    have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
    have E24 : SvCode n24.mem := E23.fr F fr24
    have V24 : SvSaves B n24.mem v := V23.same m24
    have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
    have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
    have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
    have g24_8 : reg n24 (8 : Fin 32) = op15 := by rw [u24.regs, g23_8]
    have g24_9 : reg n24 (9 : Fin 32) = tbp := by rw [u24.regs, g23_9]
    have g24_10 : reg n24 a0 = prp15 + BitVec.ofNat 32 pu15.header := by rw [u24.regs, g23_10]
    have g24_11 : reg n24 a1 = (BitVec.ofNat 8 pu15.tag).zeroExtend 32 := by rw [u24.regs, g23_11]
    have g24_12 : reg n24 a2 = BitVec.ofNat 32 0x6 := by rw [u24.regs, g23_12]
    have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
    have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
    have g24_20 : reg n24 (20 : Fin 32) = dg := by rw [u24.regs, g23_20]
    have g24_21 : reg n24 (21 : Fin 32) = rootp := by rw [u24.regs, g23_21]
    have g24_22 : reg n24 (22 : Fin 32) = ll := by rw [u24.regs, g23_22]
    have g24_23 : reg n24 (23 : Fin 32) = sgp := by rw [u24.regs, g23_23]
    have g24_24 : reg n24 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u24.regs, g23_24]
    have g24_25 : reg n24 (25 : Fin 32) = sgl := by rw [u24.regs, g23_25]
    have g24_26 : reg n24 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u24.regs, g23_26]
    have g24_27 : reg n24 (27 : Fin 32) = tbl := by rw [u24.regs, g23_27]
    have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m24]; exact keep_kk23
    clear keep_kk23
    have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m24]; exact w23_80
    have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m24]; exact w23_84
    have w24_88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m24]; exact w23_88
    have w24_8c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m24]; exact w23_8c
    have w24_284 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m24]; exact w23_284
    have w24_288 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m24]; exact w23_288
    have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m24]; exact w23_420
    have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m24]; exact w23_428
    have w24_42c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m24]; exact w23_42c
    have b24_98 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m24]; exact b23_98
    have b24_424 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m24]; exact b23_424
    have b24_425 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m24]; exact b23_425
    have b24_426 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m24]; exact b23_426
    have b24_427 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m24]; exact b23_427
    clear b23_427 b23_426 b23_425 b23_424 b23_98 w23_42c w23_428 w23_420 w23_288 w23_284 w23_8c w23_88 w23_84 w23_80 g23_12 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_11 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
    -- 0x2DE
    obtain ⟨n25, c25, u25⟩ := s24.block svL52de E24.self svL52de_end
      ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
    have m25 : n25.mem = n24.mem := u25.mem
    have s25 : St n25.mem SV n25 0x2EC (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
    have rb25 : ∀ q, reg n25 q = (runBlock svL52de (n24.mem, reg n24)).2 q := fun q => by rw [u25.regs]
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
    have g25_8 : reg n25 (8 : Fin 32) = op15 := by
      rw [rb25, runBlock_reg _ _ _ (8 : Fin 32) s24.zero (by decide), g24_8]
    have g25_9 : reg n25 (9 : Fin 32) = tbp := by
      rw [rb25, runBlock_reg _ _ _ (9 : Fin 32) s24.zero (by decide), g24_9]
    have g25_18 : reg n25 (18 : Fin 32) = out := by
      rw [rb25, runBlock_reg _ _ _ (18 : Fin 32) s24.zero (by decide), g24_18]
    have g25_19 : reg n25 (19 : Fin 32) = bp := by
      rw [rb25, runBlock_reg _ _ _ (19 : Fin 32) s24.zero (by decide), g24_19]
    have g25_20 : reg n25 (20 : Fin 32) = dg := by
      rw [rb25, runBlock_reg _ _ _ (20 : Fin 32) s24.zero (by decide), g24_20]
    have g25_21 : reg n25 (21 : Fin 32) = rootp := by
      rw [rb25, runBlock_reg _ _ _ (21 : Fin 32) s24.zero (by decide), g24_21]
    have g25_22 : reg n25 (22 : Fin 32) = ll := by
      rw [rb25, runBlock_reg _ _ _ (22 : Fin 32) s24.zero (by decide), g24_22]
    have g25_23 : reg n25 (23 : Fin 32) = sgp := by
      rw [rb25, runBlock_reg _ _ _ (23 : Fin 32) s24.zero (by decide), g24_23]
    have g25_24 : reg n25 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb25, runBlock_reg _ _ _ (24 : Fin 32) s24.zero (by decide), g24_24]
    have g25_25 : reg n25 (25 : Fin 32) = sgl := by
      rw [rb25, runBlock_reg _ _ _ (25 : Fin 32) s24.zero (by decide), g24_25]
    have g25_26 : reg n25 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
      rw [rb25, runBlock_reg _ _ _ (26 : Fin 32) s24.zero (by decide), g24_26]
    have g25_27 : reg n25 (27 : Fin 32) = tbl := by
      rw [rb25, runBlock_reg _ _ _ (27 : Fin 32) s24.zero (by decide), g24_27]
    have g25_10 : reg n25 a0 = op15 := by
      rw [rb25]; simp +decide only [runBlock, BInstr.run, svL52de, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_10, g24_11, g24_12, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g25_11 : reg n25 a1 = BitVec.ofNat 32 ol15 := by
      rw [rb25]; simp +decide only [runBlock, BInstr.run, svL52de, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_10, g24_11, g24_12, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g25_12 : reg n25 a2 = BitVec.ofNat 32 (img% svOidEcPublicKeyAddress) := by
      rw [rb25]; simp +decide only [runBlock, BInstr.run, svL52de, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_10, g24_11, g24_12, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g25_13 : reg n25 a3 = BitVec.ofNat 32 0x7 := by
      rw [rb25]; simp +decide only [runBlock, BInstr.run, svL52de, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_10, g24_11, g24_12, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m25]; exact keep_kk24
    clear keep_kk24
    have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m25]; exact w24_80
    have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m25]; exact w24_84
    have w25_88 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m25]; exact w24_88
    have w25_8c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m25]; exact w24_8c
    have w25_284 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m25]; exact w24_284
    have w25_288 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m25]; exact w24_288
    have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m25]; exact w24_420
    have w25_428 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m25]; exact w24_428
    have w25_42c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m25]; exact w24_42c
    have b25_98 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m25]; exact b24_98
    have b25_424 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m25]; exact b24_424
    have b25_425 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m25]; exact b24_425
    have b25_426 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m25]; exact b24_426
    have b25_427 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m25]; exact b24_427
    clear b24_427 b24_426 b24_425 b24_424 b24_98 w24_42c w24_428 w24_420 w24_288 w24_284 w24_8c w24_88 w24_84 w24_80 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_12 g24_11 g24_10 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
    -- 0x2EC: sv_sneF
    obtain ⟨n26, c26, s26, rk26, a0_26, K26, fr26⟩ := sv_sneF (pl := ol15) (ql := 7)
      F E25 s25 sv_at_2ec sv_at_2f0 (by decide) (by decide) g25_2
      g25_10 g25_11 g25_12 g25_13 (.inl (((tb_in.restW hr2).content hr6).algOid hr15)) (.inr ⟨by decide, by decide⟩)
    have t26 : Steps n0 n26 := t25.trans c26
    have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
    have E26 : SvCode n26.mem := E25.fr F fr26
    have V26 : SvSaves B n26.mem v := V25.keepL K26 (by decide)
    rw [sv_mbRo FW fR25 (.inl (((tb_in.restW hr2).content hr6).algOid hr15)), sv_mbRo FW fR25 (.inr ⟨by decide, by decide⟩)] at a0_26
    have g26_2 : reg n26 sp = B + 0x21A0 := by rw [rk26 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g25_2]
    have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk26 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g25_3]
    have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk26 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g25_4]
    have g26_8 : reg n26 (8 : Fin 32) = op15 := by rw [rk26 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g25_8]
    have g26_9 : reg n26 (9 : Fin 32) = tbp := by rw [rk26 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g25_9]
    have g26_18 : reg n26 (18 : Fin 32) = out := by rw [rk26 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g25_18]
    have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [rk26 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g25_19]
    have g26_20 : reg n26 (20 : Fin 32) = dg := by rw [rk26 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g25_20]
    have g26_21 : reg n26 (21 : Fin 32) = rootp := by rw [rk26 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g25_21]
    have g26_22 : reg n26 (22 : Fin 32) = ll := by rw [rk26 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g25_22]
    have g26_23 : reg n26 (23 : Fin 32) = sgp := by rw [rk26 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g25_23]
    have g26_24 : reg n26 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk26 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g25_24]
    have g26_25 : reg n26 (25 : Fin 32) = sgl := by rw [rk26 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g25_25]
    have g26_26 : reg n26 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [rk26 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g25_26]
    have g26_27 : reg n26 (27 : Fin 32) = tbl := by rw [rk26 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g25_27]
    have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := keep_kk25.trans K26
    clear keep_kk25
    have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := (K26.w32 (by decide) (by decide)).trans w25_80
    have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := (K26.w32 (by decide) (by decide)).trans w25_84
    have w26_88 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := (K26.w32 (by decide) (by decide)).trans w25_88
    have w26_8c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := (K26.w32 (by decide) (by decide)).trans w25_8c
    have w26_284 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K26.w32 (by decide) (by decide)).trans w25_284
    have w26_288 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K26.w32 (by decide) (by decide)).trans w25_288
    have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K26.w32 (by decide) (by decide)).trans w25_420
    have w26_428 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := (K26.w32 (by decide) (by decide)).trans w25_428
    have w26_42c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := (K26.w32 (by decide) (by decide)).trans w25_42c
    have b26_98 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := (K26.b8 (by decide) (by decide)).trans b25_98
    have b26_424 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := (K26.b8 (by decide) (by decide)).trans b25_424
    have b26_425 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K26.b8 (by decide) (by decide)).trans b25_425
    have b26_426 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K26.b8 (by decide) (by decide)).trans b25_426
    have b26_427 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K26.b8 (by decide) (by decide)).trans b25_427
    clear b25_427 b25_426 b25_425 b25_424 b25_98 w25_42c w25_428 w25_420 w25_288 w25_284 w25_8c w25_88 w25_84 w25_80 g25_13 g25_12 g25_11 g25_10 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
    -- 0x2F4
    obtain ⟨n27, c27, u27⟩ := s26.block svL52f4 E26.self svL52f4_end
      ⟨trivial, trivial⟩
    have m27 : n27.mem = n26.mem := u27.mem
    have s27 : St n27.mem SV n27 0x2F6 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
    have rb27 : ∀ q, reg n27 q = (runBlock svL52f4 (n26.mem, reg n26)).2 q := fun q => by rw [u27.regs]
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
    have g27_9 : reg n27 (9 : Fin 32) = tbp := by
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
    have g27_23 : reg n27 (23 : Fin 32) = sgp := by
      rw [rb27, runBlock_reg _ _ _ (23 : Fin 32) s26.zero (by decide), g26_23]
    have g27_24 : reg n27 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb27, runBlock_reg _ _ _ (24 : Fin 32) s26.zero (by decide), g26_24]
    have g27_25 : reg n27 (25 : Fin 32) = sgl := by
      rw [rb27, runBlock_reg _ _ _ (25 : Fin 32) s26.zero (by decide), g26_25]
    have g27_26 : reg n27 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
      rw [rb27, runBlock_reg _ _ _ (26 : Fin 32) s26.zero (by decide), g26_26]
    have g27_27 : reg n27 (27 : Fin 32) = tbl := by
      rw [rb27, runBlock_reg _ _ _ (27 : Fin 32) s26.zero (by decide), g26_27]
    have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
      rw [rb27]; simp +decide only [runBlock, BInstr.run, svL52f4, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_18, g26_19, g26_20, g26_21, g26_22, g26_23, g26_24, g26_25, g26_26, g26_27, s26.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m27]; exact keep_kk26
    clear keep_kk26
    have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m27]; exact w26_80
    have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m27]; exact w26_84
    have w27_88 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m27]; exact w26_88
    have w27_8c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m27]; exact w26_8c
    have w27_284 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m27]; exact w26_284
    have w27_288 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m27]; exact w26_288
    have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m27]; exact w26_420
    have w27_428 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m27]; exact w26_428
    have w27_42c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m27]; exact w26_42c
    have b27_98 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m27]; exact b26_98
    have b27_424 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m27]; exact b26_424
    have b27_425 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m27]; exact b26_425
    have b27_426 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m27]; exact b26_426
    have b27_427 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m27]; exact b26_427
    clear b26_427 b26_426 b26_425 b26_424 b26_98 w26_42c w26_428 w26_420 w26_288 w26_284 w26_8c w26_88 w26_84 w26_80 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 K26 a0_26 rk26 s26 c26
    -- 0x2F6: branch, taken
    obtain ⟨n28, d28, u28⟩ := s27.taken E27.self 0x7A4 sv_at_2f6
      (by decide) (by rw [g27_24, s27.zero]; decide)
    have s28 : St n28.mem SV n28 0x7A4 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
    have m28 : n28.mem = n27.mem := u28.mem
    have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
    have t28 : Steps n0 n28 := t27.trans (.single d28)
    have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
    have E28 : SvCode n28.mem := E27.fr F fr28
    have V28 : SvSaves B n28.mem v := V27.same m28
    have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, g27_2]
    have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, g27_3]
    have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, g27_4]
    have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u28.regs, g27_8]
    have g28_9 : reg n28 (9 : Fin 32) = tbp := by rw [u28.regs, g27_9]
    have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, g27_18]
    have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, g27_19]
    have g28_20 : reg n28 (20 : Fin 32) = dg := by rw [u28.regs, g27_20]
    have g28_21 : reg n28 (21 : Fin 32) = rootp := by rw [u28.regs, g27_21]
    have g28_22 : reg n28 (22 : Fin 32) = ll := by rw [u28.regs, g27_22]
    have g28_23 : reg n28 (23 : Fin 32) = sgp := by rw [u28.regs, g27_23]
    have g28_24 : reg n28 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u28.regs, g27_24]
    have g28_25 : reg n28 (25 : Fin 32) = sgl := by rw [u28.regs, g27_25]
    have g28_26 : reg n28 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u28.regs, g27_26]
    have g28_27 : reg n28 (27 : Fin 32) = tbl := by rw [u28.regs, g27_27]
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m28]; exact keep_kk27
    clear keep_kk27
    have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m28]; exact w27_80
    have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m28]; exact w27_84
    have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m28]; exact w27_88
    have w28_8c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m28]; exact w27_8c
    have w28_284 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m28]; exact w27_284
    have w28_288 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m28]; exact w27_288
    have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m28]; exact w27_420
    have w28_428 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m28]; exact w27_428
    have w28_42c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m28]; exact w27_42c
    have b28_98 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m28]; exact b27_98
    have b28_424 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m28]; exact b27_424
    have b28_425 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m28]; exact b27_425
    have b28_426 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m28]; exact b27_426
    have b28_427 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m28]; exact b27_427
    clear b27_427 b27_426 b27_425 b27_424 b27_98 w27_42c w27_428 w27_420 w27_288 w27_284 w27_8c w27_88 w27_84 w27_80 g27_8 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 rb27 s27 m27 u27 c27
    exact .inl ⟨(fun ⟨tl2', h0', tl6', h1', op15', ol15', prp15', pu15', h2', ta15', h3', h4', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr6] at h1'; cases h1'; rw [hr15] at h2'; cases h2'; rw [hta15] at h3'; cases h3'; exact hz_23 h4'), sv_fail F E28 s28 t28 (fun x hx => (fR28 x hx).trans (fM x hx).symm) V28 hret g28_2 g28_18 hO g28_3 g28_4 (by rw [g28_8]; sv_code)⟩
  -- 0x2C2: branch, not taken
  obtain ⟨n24, d24, u24⟩ := s23.notTaken E23.self 0x2C6 sv_at_2c2
    (by decide) (by rw [g23_11, g23_12]; exact br_bne_byte_f (by decide) hz_23)
  have s24 : St n24.mem SV n24 0x2C6 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = op15 := by rw [u24.regs, g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = tbp := by rw [u24.regs, g23_9]
  have g24_10 : reg n24 a0 = prp15 + BitVec.ofNat 32 pu15.header := by rw [u24.regs, g23_10]
  have g24_11 : reg n24 a1 = (BitVec.ofNat 8 pu15.tag).zeroExtend 32 := by rw [u24.regs, g23_11]
  have g24_12 : reg n24 a2 = BitVec.ofNat 32 0x6 := by rw [u24.regs, g23_12]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = dg := by rw [u24.regs, g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = rootp := by rw [u24.regs, g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = ll := by rw [u24.regs, g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = sgp := by rw [u24.regs, g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u24.regs, g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = sgl := by rw [u24.regs, g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u24.regs, g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = tbl := by rw [u24.regs, g23_27]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m24]; exact w23_80
  have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m24]; exact w23_84
  have w24_88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m24]; exact w23_88
  have w24_8c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m24]; exact w23_8c
  have w24_284 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m24]; exact w23_284
  have w24_288 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m24]; exact w23_288
  have w24_420 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m24]; exact w23_420
  have w24_428 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m24]; exact w23_428
  have w24_42c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m24]; exact w23_42c
  have b24_98 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m24]; exact b23_98
  have b24_424 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m24]; exact b23_424
  have b24_425 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m24]; exact b23_425
  have b24_426 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m24]; exact b23_426
  have b24_427 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m24]; exact b23_427
  clear b23_427 b23_426 b23_425 b23_424 b23_98 w23_42c w23_428 w23_420 w23_288 w23_284 w23_8c w23_88 w23_84 w23_80 g23_12 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_11 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
  -- 0x2C6: lw
  obtain ⟨n25, d25, u25⟩ := s24.lw E24.self sv_at_2c6 (off' := 0x2C8) (by decide)
    (by rw [g24_2, show B + 0x21A0 + 0x8C = B + 0x21A0 + BitVec.ofNat 32 0x8C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s25 : St n25.mem SV n25 0x2C8 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have fr25 : ∀ x, SvR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
  have t25 : Steps n0 n25 := t24.trans (.single d25)
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.same m25
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = op15 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = tbp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_9]
  have g25_10 : reg n25 a0 = prp15 + BitVec.ofNat 32 pu15.header := by rw [u25.regs, upd_ne (by decide) (by decide), g24_10]
  have g25_12 : reg n25 a2 = BitVec.ofNat 32 0x6 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_12]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [u25.regs, upd_ne (by decide) (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = dg := by rw [u25.regs, upd_ne (by decide) (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = rootp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = ll := by rw [u25.regs, upd_ne (by decide) (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = sgp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = sgl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = tbl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_27]
  have g25_11 : reg n25 a1 = BitVec.ofNat 32 pu15.len := by
    rw [u25.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g24_2, show B + 0x21A0 + 0x8C = B + 0x21A0 + BitVec.ofNat 32 0x8C by sv_addr, w24_8c]
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m25]; exact w24_80
  have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m25]; exact w24_84
  have w25_88 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m25]; exact w24_88
  have w25_8c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m25]; exact w24_8c
  have w25_284 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m25]; exact w24_284
  have w25_288 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m25]; exact w24_288
  have w25_420 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m25]; exact w24_420
  have w25_428 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m25]; exact w24_428
  have w25_42c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m25]; exact w24_42c
  have b25_98 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m25]; exact b24_98
  have b25_424 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m25]; exact b24_424
  have b25_425 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m25]; exact b24_425
  have b25_426 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m25]; exact b24_426
  have b25_427 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m25]; exact b24_427
  clear b24_427 b24_426 b24_425 b24_424 b24_98 w24_42c w24_428 w24_420 w24_288 w24_284 w24_8c w24_88 w24_84 w24_80 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_12 g24_11 g24_10 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
  -- 0x2C8
  obtain ⟨n26, c26, u26⟩ := s25.block svL52c8 E25.self svL52c8_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have s26 : St n26.mem SV n26 0x2D2 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have rb26 : ∀ q, reg n26 q = (runBlock svL52c8 (n25.mem, reg n25)).2 q := fun q => by rw [u26.regs]
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
  have g26_8 : reg n26 (8 : Fin 32) = op15 := by
    rw [rb26, runBlock_reg _ _ _ (8 : Fin 32) s25.zero (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = tbp := by
    rw [rb26, runBlock_reg _ _ _ (9 : Fin 32) s25.zero (by decide), g25_9]
  have g26_10 : reg n26 a0 = prp15 + BitVec.ofNat 32 pu15.header := by
    rw [rb26, runBlock_reg _ _ _ a0 s25.zero (by decide), g25_10]
  have g26_11 : reg n26 a1 = BitVec.ofNat 32 pu15.len := by
    rw [rb26, runBlock_reg _ _ _ a1 s25.zero (by decide), g25_11]
  have g26_18 : reg n26 (18 : Fin 32) = out := by
    rw [rb26, runBlock_reg _ _ _ (18 : Fin 32) s25.zero (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by
    rw [rb26, runBlock_reg _ _ _ (19 : Fin 32) s25.zero (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = dg := by
    rw [rb26, runBlock_reg _ _ _ (20 : Fin 32) s25.zero (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = rootp := by
    rw [rb26, runBlock_reg _ _ _ (21 : Fin 32) s25.zero (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = ll := by
    rw [rb26, runBlock_reg _ _ _ (22 : Fin 32) s25.zero (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = sgp := by
    rw [rb26, runBlock_reg _ _ _ (23 : Fin 32) s25.zero (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb26, runBlock_reg _ _ _ (24 : Fin 32) s25.zero (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = sgl := by
    rw [rb26, runBlock_reg _ _ _ (25 : Fin 32) s25.zero (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
    rw [rb26, runBlock_reg _ _ _ (26 : Fin 32) s25.zero (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = tbl := by
    rw [rb26, runBlock_reg _ _ _ (27 : Fin 32) s25.zero (by decide), g25_27]
  have g26_12 : reg n26 a2 = BitVec.ofNat 32 (img% svOidPrime256v1Address) := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, svL52c8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_10, g25_11, g25_12, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_25, g25_26, g25_27, s25.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g26_13 : reg n26 a3 = BitVec.ofNat 32 0x8 := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, svL52c8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_10, g25_11, g25_12, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_25, g25_26, g25_27, s25.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m26]; exact w25_80
  have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m26]; exact w25_84
  have w26_88 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m26]; exact w25_88
  have w26_8c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m26]; exact w25_8c
  have w26_284 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m26]; exact w25_284
  have w26_288 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m26]; exact w25_288
  have w26_420 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m26]; exact w25_420
  have w26_428 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m26]; exact w25_428
  have w26_42c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m26]; exact w25_42c
  have b26_98 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m26]; exact b25_98
  have b26_424 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m26]; exact b25_424
  have b26_425 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m26]; exact b25_425
  have b26_426 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m26]; exact b25_426
  have b26_427 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m26]; exact b25_427
  clear b25_427 b25_426 b25_425 b25_424 b25_98 w25_42c w25_428 w25_420 w25_288 w25_284 w25_8c w25_88 w25_84 w25_80 g25_11 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_12 g25_10 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 m25 s25 u25 d25
  -- 0x2D2: sv_seqEqF
  obtain ⟨n27, c27, s27, rk27, a0_27, K27, fr27⟩ := sv_seqEqF (pl := pu15.len) (ql := 8)
    F E26 s26 sv_at_2d2 sv_at_2d6 (by decide) (by decide) g26_2
    g26_10 g26_11 g26_12 g26_13 (.inl (((tb_in.restW hr2).content hr6).algParamsIn hr15)) (.inr ⟨by decide, by decide⟩)
  have t27 : Steps n0 n27 := t26.trans c27
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.keepL K27 (by decide)
  rw [sv_mbRo FW fR26 (.inl (((tb_in.restW hr2).content hr6).algParamsIn hr15)), sv_mbRo FW fR26 (.inr ⟨by decide, by decide⟩)] at a0_27
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [rk27 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk27 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk27 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = op15 := by rw [rk27 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = tbp := by rw [rk27 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_9]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [rk27 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [rk27 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = dg := by rw [rk27 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = rootp := by rw [rk27 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = ll := by rw [rk27 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = sgp := by rw [rk27 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk27 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = sgl := by rw [rk27 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [rk27 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = tbl := by rw [rk27 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g26_27]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := keep_kk26.trans K27
  clear keep_kk26
  have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := (K27.w32 (by decide) (by decide)).trans w26_80
  have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := (K27.w32 (by decide) (by decide)).trans w26_84
  have w27_88 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := (K27.w32 (by decide) (by decide)).trans w26_88
  have w27_8c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := (K27.w32 (by decide) (by decide)).trans w26_8c
  have w27_284 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K27.w32 (by decide) (by decide)).trans w26_284
  have w27_288 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K27.w32 (by decide) (by decide)).trans w26_288
  have w27_420 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K27.w32 (by decide) (by decide)).trans w26_420
  have w27_428 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := (K27.w32 (by decide) (by decide)).trans w26_428
  have w27_42c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := (K27.w32 (by decide) (by decide)).trans w26_42c
  have b27_98 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := (K27.b8 (by decide) (by decide)).trans b26_98
  have b27_424 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := (K27.b8 (by decide) (by decide)).trans b26_424
  have b27_425 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K27.b8 (by decide) (by decide)).trans b26_425
  have b27_426 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K27.b8 (by decide) (by decide)).trans b26_426
  have b27_427 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K27.b8 (by decide) (by decide)).trans b26_427
  clear b26_427 b26_426 b26_425 b26_424 b26_98 w26_42c w26_428 w26_420 w26_288 w26_284 w26_8c w26_88 w26_84 w26_80 g26_13 g26_12 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_11 g26_10 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 rb26 s26 m26 u26 c26
  by_cases hz_27 : memBytes M0 (prp15 + BitVec.ofNat 32 pu15.header) pu15.len = memBytes M0 (BitVec.ofNat 32 (img% svOidPrime256v1Address)) 8
  rotate_left
  · have g27_10 : reg n27 a0 = BitVec.ofNat 32 0 := by rw [a0_27, ite_eq_right hz_27]; rfl
    -- 0x2DA
    obtain ⟨n28, c28, u28⟩ := s27.block svL52da E27.self svL52da_end
      ⟨trivial, trivial⟩
    have m28 : n28.mem = n27.mem := u28.mem
    have s28 : St n28.mem SV n28 0x2DE (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
    have rb28 : ∀ q, reg n28 q = (runBlock svL52da (n27.mem, reg n27)).2 q := fun q => by rw [u28.regs]
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
    have g28_8 : reg n28 (8 : Fin 32) = op15 := by
      rw [rb28, runBlock_reg _ _ _ (8 : Fin 32) s27.zero (by decide), g27_8]
    have g28_9 : reg n28 (9 : Fin 32) = tbp := by
      rw [rb28, runBlock_reg _ _ _ (9 : Fin 32) s27.zero (by decide), g27_9]
    have g28_10 : reg n28 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb28, runBlock_reg _ _ _ a0 s27.zero (by decide), g27_10]
    have g28_18 : reg n28 (18 : Fin 32) = out := by
      rw [rb28, runBlock_reg _ _ _ (18 : Fin 32) s27.zero (by decide), g27_18]
    have g28_19 : reg n28 (19 : Fin 32) = bp := by
      rw [rb28, runBlock_reg _ _ _ (19 : Fin 32) s27.zero (by decide), g27_19]
    have g28_20 : reg n28 (20 : Fin 32) = dg := by
      rw [rb28, runBlock_reg _ _ _ (20 : Fin 32) s27.zero (by decide), g27_20]
    have g28_21 : reg n28 (21 : Fin 32) = rootp := by
      rw [rb28, runBlock_reg _ _ _ (21 : Fin 32) s27.zero (by decide), g27_21]
    have g28_22 : reg n28 (22 : Fin 32) = ll := by
      rw [rb28, runBlock_reg _ _ _ (22 : Fin 32) s27.zero (by decide), g27_22]
    have g28_23 : reg n28 (23 : Fin 32) = sgp := by
      rw [rb28, runBlock_reg _ _ _ (23 : Fin 32) s27.zero (by decide), g27_23]
    have g28_25 : reg n28 (25 : Fin 32) = sgl := by
      rw [rb28, runBlock_reg _ _ _ (25 : Fin 32) s27.zero (by decide), g27_25]
    have g28_26 : reg n28 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
      rw [rb28, runBlock_reg _ _ _ (26 : Fin 32) s27.zero (by decide), g27_26]
    have g28_27 : reg n28 (27 : Fin 32) = tbl := by
      rw [rb28, runBlock_reg _ _ _ (27 : Fin 32) s27.zero (by decide), g27_27]
    have g28_24 : reg n28 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb28]; simp +decide only [runBlock, BInstr.run, svL52da, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g27_2, g27_3, g27_4, g27_8, g27_9, g27_10, g27_18, g27_19, g27_20, g27_21, g27_22, g27_23, g27_24, g27_25, g27_26, g27_27, s27.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m28]; exact keep_kk27
    clear keep_kk27
    have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m28]; exact w27_80
    have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m28]; exact w27_84
    have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m28]; exact w27_88
    have w28_8c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m28]; exact w27_8c
    have w28_284 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m28]; exact w27_284
    have w28_288 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m28]; exact w27_288
    have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m28]; exact w27_420
    have w28_428 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m28]; exact w27_428
    have w28_42c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m28]; exact w27_42c
    have b28_98 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m28]; exact b27_98
    have b28_424 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m28]; exact b27_424
    have b28_425 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m28]; exact b27_425
    have b28_426 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m28]; exact b27_426
    have b28_427 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m28]; exact b27_427
    clear b27_427 b27_426 b27_425 b27_424 b27_98 w27_42c w27_428 w27_420 w27_288 w27_284 w27_8c w27_88 w27_84 w27_80 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 K27 a0_27 rk27 s27 c27
    -- 0x2DE
    obtain ⟨n29, c29, u29⟩ := s28.block svL52de E28.self svL52de_end
      ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have s29 : St n29.mem SV n29 0x2EC (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have rb29 : ∀ q, reg n29 q = (runBlock svL52de (n28.mem, reg n28)).2 q := fun q => by rw [u29.regs]
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
    have g29_8 : reg n29 (8 : Fin 32) = op15 := by
      rw [rb29, runBlock_reg _ _ _ (8 : Fin 32) s28.zero (by decide), g28_8]
    have g29_9 : reg n29 (9 : Fin 32) = tbp := by
      rw [rb29, runBlock_reg _ _ _ (9 : Fin 32) s28.zero (by decide), g28_9]
    have g29_18 : reg n29 (18 : Fin 32) = out := by
      rw [rb29, runBlock_reg _ _ _ (18 : Fin 32) s28.zero (by decide), g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by
      rw [rb29, runBlock_reg _ _ _ (19 : Fin 32) s28.zero (by decide), g28_19]
    have g29_20 : reg n29 (20 : Fin 32) = dg := by
      rw [rb29, runBlock_reg _ _ _ (20 : Fin 32) s28.zero (by decide), g28_20]
    have g29_21 : reg n29 (21 : Fin 32) = rootp := by
      rw [rb29, runBlock_reg _ _ _ (21 : Fin 32) s28.zero (by decide), g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = ll := by
      rw [rb29, runBlock_reg _ _ _ (22 : Fin 32) s28.zero (by decide), g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = sgp := by
      rw [rb29, runBlock_reg _ _ _ (23 : Fin 32) s28.zero (by decide), g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb29, runBlock_reg _ _ _ (24 : Fin 32) s28.zero (by decide), g28_24]
    have g29_25 : reg n29 (25 : Fin 32) = sgl := by
      rw [rb29, runBlock_reg _ _ _ (25 : Fin 32) s28.zero (by decide), g28_25]
    have g29_26 : reg n29 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
      rw [rb29, runBlock_reg _ _ _ (26 : Fin 32) s28.zero (by decide), g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = tbl := by
      rw [rb29, runBlock_reg _ _ _ (27 : Fin 32) s28.zero (by decide), g28_27]
    have g29_10 : reg n29 a0 = op15 := by
      rw [rb29]; simp +decide only [runBlock, BInstr.run, svL52de, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_10, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g29_11 : reg n29 a1 = BitVec.ofNat 32 ol15 := by
      rw [rb29]; simp +decide only [runBlock, BInstr.run, svL52de, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_10, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g29_12 : reg n29 a2 = BitVec.ofNat 32 (img% svOidEcPublicKeyAddress) := by
      rw [rb29]; simp +decide only [runBlock, BInstr.run, svL52de, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_10, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have g29_13 : reg n29 a3 = BitVec.ofNat 32 0x7 := by
      rw [rb29]; simp +decide only [runBlock, BInstr.run, svL52de, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_10, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m29]; exact w28_80
    have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m29]; exact w28_84
    have w29_88 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m29]; exact w28_88
    have w29_8c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m29]; exact w28_8c
    have w29_284 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m29]; exact w28_284
    have w29_288 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m29]; exact w28_288
    have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m29]; exact w28_420
    have w29_428 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m29]; exact w28_428
    have w29_42c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m29]; exact w28_42c
    have b29_98 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m29]; exact b28_98
    have b29_424 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m29]; exact b28_424
    have b29_425 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m29]; exact b28_425
    have b29_426 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m29]; exact b28_426
    have b29_427 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m29]; exact b28_427
    clear b28_427 b28_426 b28_425 b28_424 b28_98 w28_42c w28_428 w28_420 w28_288 w28_284 w28_8c w28_88 w28_84 w28_80 g28_24 g28_27 g28_26 g28_25 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_10 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 rb28 s28 m28 u28 c28 g27_10
    -- 0x2EC: sv_sneF
    obtain ⟨n30, c30, s30, rk30, a0_30, K30, fr30⟩ := sv_sneF (pl := ol15) (ql := 7)
      F E29 s29 sv_at_2ec sv_at_2f0 (by decide) (by decide) g29_2
      g29_10 g29_11 g29_12 g29_13 (.inl (((tb_in.restW hr2).content hr6).algOid hr15)) (.inr ⟨by decide, by decide⟩)
    have t30 : Steps n0 n30 := t29.trans c30
    have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
    have E30 : SvCode n30.mem := E29.fr F fr30
    have V30 : SvSaves B n30.mem v := V29.keepL K30 (by decide)
    rw [sv_mbRo FW fR29 (.inl (((tb_in.restW hr2).content hr6).algOid hr15)), sv_mbRo FW fR29 (.inr ⟨by decide, by decide⟩)] at a0_30
    have g30_2 : reg n30 sp = B + 0x21A0 := by rw [rk30 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_2]
    have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk30 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_3]
    have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk30 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_4]
    have g30_8 : reg n30 (8 : Fin 32) = op15 := by rw [rk30 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_8]
    have g30_9 : reg n30 (9 : Fin 32) = tbp := by rw [rk30 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_9]
    have g30_18 : reg n30 (18 : Fin 32) = out := by rw [rk30 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_18]
    have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [rk30 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_19]
    have g30_20 : reg n30 (20 : Fin 32) = dg := by rw [rk30 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_20]
    have g30_21 : reg n30 (21 : Fin 32) = rootp := by rw [rk30 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_21]
    have g30_22 : reg n30 (22 : Fin 32) = ll := by rw [rk30 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_22]
    have g30_23 : reg n30 (23 : Fin 32) = sgp := by rw [rk30 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_23]
    have g30_24 : reg n30 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk30 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_24]
    have g30_25 : reg n30 (25 : Fin 32) = sgl := by rw [rk30 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_25]
    have g30_26 : reg n30 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [rk30 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_26]
    have g30_27 : reg n30 (27 : Fin 32) = tbl := by rw [rk30 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_27]
    have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := keep_kk29.trans K30
    clear keep_kk29
    have w30_80 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := (K30.w32 (by decide) (by decide)).trans w29_80
    have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := (K30.w32 (by decide) (by decide)).trans w29_84
    have w30_88 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := (K30.w32 (by decide) (by decide)).trans w29_88
    have w30_8c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := (K30.w32 (by decide) (by decide)).trans w29_8c
    have w30_284 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K30.w32 (by decide) (by decide)).trans w29_284
    have w30_288 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K30.w32 (by decide) (by decide)).trans w29_288
    have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K30.w32 (by decide) (by decide)).trans w29_420
    have w30_428 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := (K30.w32 (by decide) (by decide)).trans w29_428
    have w30_42c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := (K30.w32 (by decide) (by decide)).trans w29_42c
    have b30_98 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := (K30.b8 (by decide) (by decide)).trans b29_98
    have b30_424 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := (K30.b8 (by decide) (by decide)).trans b29_424
    have b30_425 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K30.b8 (by decide) (by decide)).trans b29_425
    have b30_426 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K30.b8 (by decide) (by decide)).trans b29_426
    have b30_427 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K30.b8 (by decide) (by decide)).trans b29_427
    clear b29_427 b29_426 b29_425 b29_424 b29_98 w29_42c w29_428 w29_420 w29_288 w29_284 w29_8c w29_88 w29_84 w29_80 g29_13 g29_12 g29_11 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29
    -- 0x2F4
    obtain ⟨n31, c31, u31⟩ := s30.block svL52f4 E30.self svL52f4_end
      ⟨trivial, trivial⟩
    have m31 : n31.mem = n30.mem := u31.mem
    have s31 : St n31.mem SV n31 0x2F6 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
    have rb31 : ∀ q, reg n31 q = (runBlock svL52f4 (n30.mem, reg n30)).2 q := fun q => by rw [u31.regs]
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
    have g31_9 : reg n31 (9 : Fin 32) = tbp := by
      rw [rb31, runBlock_reg _ _ _ (9 : Fin 32) s30.zero (by decide), g30_9]
    have g31_18 : reg n31 (18 : Fin 32) = out := by
      rw [rb31, runBlock_reg _ _ _ (18 : Fin 32) s30.zero (by decide), g30_18]
    have g31_19 : reg n31 (19 : Fin 32) = bp := by
      rw [rb31, runBlock_reg _ _ _ (19 : Fin 32) s30.zero (by decide), g30_19]
    have g31_20 : reg n31 (20 : Fin 32) = dg := by
      rw [rb31, runBlock_reg _ _ _ (20 : Fin 32) s30.zero (by decide), g30_20]
    have g31_21 : reg n31 (21 : Fin 32) = rootp := by
      rw [rb31, runBlock_reg _ _ _ (21 : Fin 32) s30.zero (by decide), g30_21]
    have g31_22 : reg n31 (22 : Fin 32) = ll := by
      rw [rb31, runBlock_reg _ _ _ (22 : Fin 32) s30.zero (by decide), g30_22]
    have g31_23 : reg n31 (23 : Fin 32) = sgp := by
      rw [rb31, runBlock_reg _ _ _ (23 : Fin 32) s30.zero (by decide), g30_23]
    have g31_24 : reg n31 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb31, runBlock_reg _ _ _ (24 : Fin 32) s30.zero (by decide), g30_24]
    have g31_25 : reg n31 (25 : Fin 32) = sgl := by
      rw [rb31, runBlock_reg _ _ _ (25 : Fin 32) s30.zero (by decide), g30_25]
    have g31_26 : reg n31 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
      rw [rb31, runBlock_reg _ _ _ (26 : Fin 32) s30.zero (by decide), g30_26]
    have g31_27 : reg n31 (27 : Fin 32) = tbl := by
      rw [rb31, runBlock_reg _ _ _ (27 : Fin 32) s30.zero (by decide), g30_27]
    have g31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
      rw [rb31]; simp +decide only [runBlock, BInstr.run, svL52f4, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, s30.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m31]; exact keep_kk30
    clear keep_kk30
    have w31_80 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m31]; exact w30_80
    have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m31]; exact w30_84
    have w31_88 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m31]; exact w30_88
    have w31_8c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m31]; exact w30_8c
    have w31_284 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m31]; exact w30_284
    have w31_288 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m31]; exact w30_288
    have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m31]; exact w30_420
    have w31_428 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m31]; exact w30_428
    have w31_42c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m31]; exact w30_42c
    have b31_98 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m31]; exact b30_98
    have b31_424 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m31]; exact b30_424
    have b31_425 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m31]; exact b30_425
    have b31_426 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m31]; exact b30_426
    have b31_427 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m31]; exact b30_427
    clear b30_427 b30_426 b30_425 b30_424 b30_98 w30_42c w30_428 w30_420 w30_288 w30_284 w30_8c w30_88 w30_84 w30_80 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 K30 a0_30 rk30 s30 c30
    -- 0x2F6: branch, taken
    obtain ⟨n32, d32, u32⟩ := s31.taken E31.self 0x7A4 sv_at_2f6
      (by decide) (by rw [g31_24, s31.zero]; decide)
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
    have g32_8 : reg n32 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u32.regs, g31_8]
    have g32_9 : reg n32 (9 : Fin 32) = tbp := by rw [u32.regs, g31_9]
    have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, g31_18]
    have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, g31_19]
    have g32_20 : reg n32 (20 : Fin 32) = dg := by rw [u32.regs, g31_20]
    have g32_21 : reg n32 (21 : Fin 32) = rootp := by rw [u32.regs, g31_21]
    have g32_22 : reg n32 (22 : Fin 32) = ll := by rw [u32.regs, g31_22]
    have g32_23 : reg n32 (23 : Fin 32) = sgp := by rw [u32.regs, g31_23]
    have g32_24 : reg n32 (24 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u32.regs, g31_24]
    have g32_25 : reg n32 (25 : Fin 32) = sgl := by rw [u32.regs, g31_25]
    have g32_26 : reg n32 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u32.regs, g31_26]
    have g32_27 : reg n32 (27 : Fin 32) = tbl := by rw [u32.regs, g31_27]
    have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m32]; exact keep_kk31
    clear keep_kk31
    have w32_80 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m32]; exact w31_80
    have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m32]; exact w31_84
    have w32_88 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m32]; exact w31_88
    have w32_8c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m32]; exact w31_8c
    have w32_284 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m32]; exact w31_284
    have w32_288 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m32]; exact w31_288
    have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m32]; exact w31_420
    have w32_428 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m32]; exact w31_428
    have w32_42c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m32]; exact w31_42c
    have b32_98 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m32]; exact b31_98
    have b32_424 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m32]; exact b31_424
    have b32_425 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m32]; exact b31_425
    have b32_426 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m32]; exact b31_426
    have b32_427 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m32]; exact b31_427
    clear b31_427 b31_426 b31_425 b31_424 b31_98 w31_42c w31_428 w31_420 w31_288 w31_284 w31_8c w31_88 w31_84 w31_80 g31_8 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_9 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 rb31 s31 m31 u31 c31
    exact .inl ⟨(fun ⟨tl2', h0', tl6', h1', op15', ol15', prp15', pu15', h2', ta15', h3', h4', h5', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr6] at h1'; cases h1'; rw [hr15] at h2'; cases h2'; rw [hta15] at h3'; cases h3'; exact hz_27 h5'), sv_fail F E32 s32 t32 (fun x hx => (fR32 x hx).trans (fM x hx).symm) V32 hret g32_2 g32_18 hO g32_3 g32_4 (by rw [g32_8]; sv_code)⟩
  have g27_10 : reg n27 a0 = BitVec.ofNat 32 1 := by rw [a0_27, ite_eq_left hz_27]; rfl
  -- 0x2DA
  obtain ⟨n28, c28, u28⟩ := s27.block svL52da E27.self svL52da_end
    ⟨trivial, trivial⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have s28 : St n28.mem SV n28 0x2DE (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have rb28 : ∀ q, reg n28 q = (runBlock svL52da (n27.mem, reg n27)).2 q := fun q => by rw [u28.regs]
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
  have g28_8 : reg n28 (8 : Fin 32) = op15 := by
    rw [rb28, runBlock_reg _ _ _ (8 : Fin 32) s27.zero (by decide), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = tbp := by
    rw [rb28, runBlock_reg _ _ _ (9 : Fin 32) s27.zero (by decide), g27_9]
  have g28_10 : reg n28 a0 = BitVec.ofNat 32 0x1 := by
    rw [rb28, runBlock_reg _ _ _ a0 s27.zero (by decide), g27_10]
  have g28_18 : reg n28 (18 : Fin 32) = out := by
    rw [rb28, runBlock_reg _ _ _ (18 : Fin 32) s27.zero (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by
    rw [rb28, runBlock_reg _ _ _ (19 : Fin 32) s27.zero (by decide), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = dg := by
    rw [rb28, runBlock_reg _ _ _ (20 : Fin 32) s27.zero (by decide), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = rootp := by
    rw [rb28, runBlock_reg _ _ _ (21 : Fin 32) s27.zero (by decide), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = ll := by
    rw [rb28, runBlock_reg _ _ _ (22 : Fin 32) s27.zero (by decide), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = sgp := by
    rw [rb28, runBlock_reg _ _ _ (23 : Fin 32) s27.zero (by decide), g27_23]
  have g28_25 : reg n28 (25 : Fin 32) = sgl := by
    rw [rb28, runBlock_reg _ _ _ (25 : Fin 32) s27.zero (by decide), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
    rw [rb28, runBlock_reg _ _ _ (26 : Fin 32) s27.zero (by decide), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = tbl := by
    rw [rb28, runBlock_reg _ _ _ (27 : Fin 32) s27.zero (by decide), g27_27]
  have g28_24 : reg n28 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb28]; simp +decide only [runBlock, BInstr.run, svL52da, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g27_2, g27_3, g27_4, g27_8, g27_9, g27_10, g27_18, g27_19, g27_20, g27_21, g27_22, g27_23, g27_24, g27_25, g27_26, g27_27, s27.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m28]; exact keep_kk27
  clear keep_kk27
  have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m28]; exact w27_80
  have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m28]; exact w27_84
  have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m28]; exact w27_88
  have w28_8c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m28]; exact w27_8c
  have w28_284 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m28]; exact w27_284
  have w28_288 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m28]; exact w27_288
  have w28_420 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m28]; exact w27_420
  have w28_428 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m28]; exact w27_428
  have w28_42c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m28]; exact w27_42c
  have b28_98 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m28]; exact b27_98
  have b28_424 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m28]; exact b27_424
  have b28_425 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m28]; exact b27_425
  have b28_426 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m28]; exact b27_426
  have b28_427 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m28]; exact b27_427
  clear b27_427 b27_426 b27_425 b27_424 b27_98 w27_42c w27_428 w27_420 w27_288 w27_284 w27_8c w27_88 w27_84 w27_80 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 K27 a0_27 rk27 s27 c27
  -- 0x2DE
  obtain ⟨n29, c29, u29⟩ := s28.block svL52de E28.self svL52de_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have s29 : St n29.mem SV n29 0x2EC (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have rb29 : ∀ q, reg n29 q = (runBlock svL52de (n28.mem, reg n28)).2 q := fun q => by rw [u29.regs]
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
  have g29_8 : reg n29 (8 : Fin 32) = op15 := by
    rw [rb29, runBlock_reg _ _ _ (8 : Fin 32) s28.zero (by decide), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = tbp := by
    rw [rb29, runBlock_reg _ _ _ (9 : Fin 32) s28.zero (by decide), g28_9]
  have g29_18 : reg n29 (18 : Fin 32) = out := by
    rw [rb29, runBlock_reg _ _ _ (18 : Fin 32) s28.zero (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by
    rw [rb29, runBlock_reg _ _ _ (19 : Fin 32) s28.zero (by decide), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = dg := by
    rw [rb29, runBlock_reg _ _ _ (20 : Fin 32) s28.zero (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = rootp := by
    rw [rb29, runBlock_reg _ _ _ (21 : Fin 32) s28.zero (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = ll := by
    rw [rb29, runBlock_reg _ _ _ (22 : Fin 32) s28.zero (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = sgp := by
    rw [rb29, runBlock_reg _ _ _ (23 : Fin 32) s28.zero (by decide), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb29, runBlock_reg _ _ _ (24 : Fin 32) s28.zero (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = sgl := by
    rw [rb29, runBlock_reg _ _ _ (25 : Fin 32) s28.zero (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
    rw [rb29, runBlock_reg _ _ _ (26 : Fin 32) s28.zero (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = tbl := by
    rw [rb29, runBlock_reg _ _ _ (27 : Fin 32) s28.zero (by decide), g28_27]
  have g29_10 : reg n29 a0 = op15 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svL52de, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_10, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g29_11 : reg n29 a1 = BitVec.ofNat 32 ol15 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svL52de, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_10, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g29_12 : reg n29 a2 = BitVec.ofNat 32 (img% svOidEcPublicKeyAddress) := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svL52de, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_10, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g29_13 : reg n29 a3 = BitVec.ofNat 32 0x7 := by
    rw [rb29]; simp +decide only [runBlock, BInstr.run, svL52de, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_10, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m29]; exact w28_80
  have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m29]; exact w28_84
  have w29_88 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m29]; exact w28_88
  have w29_8c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m29]; exact w28_8c
  have w29_284 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m29]; exact w28_284
  have w29_288 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m29]; exact w28_288
  have w29_420 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m29]; exact w28_420
  have w29_428 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m29]; exact w28_428
  have w29_42c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m29]; exact w28_42c
  have b29_98 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m29]; exact b28_98
  have b29_424 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m29]; exact b28_424
  have b29_425 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m29]; exact b28_425
  have b29_426 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m29]; exact b28_426
  have b29_427 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m29]; exact b28_427
  clear b28_427 b28_426 b28_425 b28_424 b28_98 w28_42c w28_428 w28_420 w28_288 w28_284 w28_8c w28_88 w28_84 w28_80 g28_24 g28_27 g28_26 g28_25 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_10 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 rb28 s28 m28 u28 c28 g27_10
  -- 0x2EC: sv_sneF
  obtain ⟨n30, c30, s30, rk30, a0_30, K30, fr30⟩ := sv_sneF (pl := ol15) (ql := 7)
    F E29 s29 sv_at_2ec sv_at_2f0 (by decide) (by decide) g29_2
    g29_10 g29_11 g29_12 g29_13 (.inl (((tb_in.restW hr2).content hr6).algOid hr15)) (.inr ⟨by decide, by decide⟩)
  have t30 : Steps n0 n30 := t29.trans c30
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.keepL K30 (by decide)
  rw [sv_mbRo FW fR29 (.inl (((tb_in.restW hr2).content hr6).algOid hr15)), sv_mbRo FW fR29 (.inr ⟨by decide, by decide⟩)] at a0_30
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [rk30 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk30 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk30 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = op15 := by rw [rk30 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = tbp := by rw [rk30 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_9]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [rk30 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [rk30 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = dg := by rw [rk30 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = rootp := by rw [rk30 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = ll := by rw [rk30 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = sgp := by rw [rk30 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rk30 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = sgl := by rw [rk30 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [rk30 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = tbl := by rw [rk30 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_27]
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := keep_kk29.trans K30
  clear keep_kk29
  have w30_80 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := (K30.w32 (by decide) (by decide)).trans w29_80
  have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := (K30.w32 (by decide) (by decide)).trans w29_84
  have w30_88 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := (K30.w32 (by decide) (by decide)).trans w29_88
  have w30_8c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := (K30.w32 (by decide) (by decide)).trans w29_8c
  have w30_284 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K30.w32 (by decide) (by decide)).trans w29_284
  have w30_288 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K30.w32 (by decide) (by decide)).trans w29_288
  have w30_420 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K30.w32 (by decide) (by decide)).trans w29_420
  have w30_428 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := (K30.w32 (by decide) (by decide)).trans w29_428
  have w30_42c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := (K30.w32 (by decide) (by decide)).trans w29_42c
  have b30_98 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := (K30.b8 (by decide) (by decide)).trans b29_98
  have b30_424 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := (K30.b8 (by decide) (by decide)).trans b29_424
  have b30_425 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K30.b8 (by decide) (by decide)).trans b29_425
  have b30_426 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K30.b8 (by decide) (by decide)).trans b29_426
  have b30_427 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K30.b8 (by decide) (by decide)).trans b29_427
  clear b29_427 b29_426 b29_425 b29_424 b29_98 w29_42c w29_428 w29_420 w29_288 w29_284 w29_8c w29_88 w29_84 w29_80 g29_13 g29_12 g29_11 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29
  by_cases hz_30 : memBytes M0 op15 ol15 = memBytes M0 (BitVec.ofNat 32 (img% svOidEcPublicKeyAddress)) 7
  rotate_left
  · have g30_10 : reg n30 a0 = BitVec.ofNat 32 1 := by rw [a0_30, ite_eq_right hz_30]; rfl
    -- 0x2F4
    obtain ⟨n31, c31, u31⟩ := s30.block svL52f4 E30.self svL52f4_end
      ⟨trivial, trivial⟩
    have m31 : n31.mem = n30.mem := u31.mem
    have s31 : St n31.mem SV n31 0x2F6 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
    have rb31 : ∀ q, reg n31 q = (runBlock svL52f4 (n30.mem, reg n30)).2 q := fun q => by rw [u31.regs]
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
    have g31_9 : reg n31 (9 : Fin 32) = tbp := by
      rw [rb31, runBlock_reg _ _ _ (9 : Fin 32) s30.zero (by decide), g30_9]
    have g31_10 : reg n31 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb31, runBlock_reg _ _ _ a0 s30.zero (by decide), g30_10]
    have g31_18 : reg n31 (18 : Fin 32) = out := by
      rw [rb31, runBlock_reg _ _ _ (18 : Fin 32) s30.zero (by decide), g30_18]
    have g31_19 : reg n31 (19 : Fin 32) = bp := by
      rw [rb31, runBlock_reg _ _ _ (19 : Fin 32) s30.zero (by decide), g30_19]
    have g31_20 : reg n31 (20 : Fin 32) = dg := by
      rw [rb31, runBlock_reg _ _ _ (20 : Fin 32) s30.zero (by decide), g30_20]
    have g31_21 : reg n31 (21 : Fin 32) = rootp := by
      rw [rb31, runBlock_reg _ _ _ (21 : Fin 32) s30.zero (by decide), g30_21]
    have g31_22 : reg n31 (22 : Fin 32) = ll := by
      rw [rb31, runBlock_reg _ _ _ (22 : Fin 32) s30.zero (by decide), g30_22]
    have g31_23 : reg n31 (23 : Fin 32) = sgp := by
      rw [rb31, runBlock_reg _ _ _ (23 : Fin 32) s30.zero (by decide), g30_23]
    have g31_24 : reg n31 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [rb31, runBlock_reg _ _ _ (24 : Fin 32) s30.zero (by decide), g30_24]
    have g31_25 : reg n31 (25 : Fin 32) = sgl := by
      rw [rb31, runBlock_reg _ _ _ (25 : Fin 32) s30.zero (by decide), g30_25]
    have g31_26 : reg n31 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
      rw [rb31, runBlock_reg _ _ _ (26 : Fin 32) s30.zero (by decide), g30_26]
    have g31_27 : reg n31 (27 : Fin 32) = tbl := by
      rw [rb31, runBlock_reg _ _ _ (27 : Fin 32) s30.zero (by decide), g30_27]
    have g31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
      rw [rb31]; simp +decide only [runBlock, BInstr.run, svL52f4, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_10, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, s30.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m31]; exact keep_kk30
    clear keep_kk30
    have w31_80 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m31]; exact w30_80
    have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m31]; exact w30_84
    have w31_88 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m31]; exact w30_88
    have w31_8c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m31]; exact w30_8c
    have w31_284 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m31]; exact w30_284
    have w31_288 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m31]; exact w30_288
    have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m31]; exact w30_420
    have w31_428 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m31]; exact w30_428
    have w31_42c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m31]; exact w30_42c
    have b31_98 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m31]; exact b30_98
    have b31_424 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m31]; exact b30_424
    have b31_425 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m31]; exact b30_425
    have b31_426 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m31]; exact b30_426
    have b31_427 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m31]; exact b30_427
    clear b30_427 b30_426 b30_425 b30_424 b30_98 w30_42c w30_428 w30_420 w30_288 w30_284 w30_8c w30_88 w30_84 w30_80 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 K30 a0_30 rk30 s30 c30
    -- 0x2F6: branch, not taken
    obtain ⟨n32, d32, u32⟩ := s31.notTaken E31.self 0x2FA sv_at_2f6
      (by decide) (by rw [g31_24, s31.zero]; decide)
    have s32 : St n32.mem SV n32 0x2FA (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
    have m32 : n32.mem = n31.mem := u32.mem
    have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
    have t32 : Steps n0 n32 := t31.trans (.single d32)
    have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
    have E32 : SvCode n32.mem := E31.fr F fr32
    have V32 : SvSaves B n32.mem v := V31.same m32
    have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, g31_2]
    have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, g31_3]
    have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, g31_4]
    have g32_8 : reg n32 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u32.regs, g31_8]
    have g32_9 : reg n32 (9 : Fin 32) = tbp := by rw [u32.regs, g31_9]
    have g32_10 : reg n32 a0 = BitVec.ofNat 32 0x1 := by rw [u32.regs, g31_10]
    have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, g31_18]
    have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, g31_19]
    have g32_20 : reg n32 (20 : Fin 32) = dg := by rw [u32.regs, g31_20]
    have g32_21 : reg n32 (21 : Fin 32) = rootp := by rw [u32.regs, g31_21]
    have g32_22 : reg n32 (22 : Fin 32) = ll := by rw [u32.regs, g31_22]
    have g32_23 : reg n32 (23 : Fin 32) = sgp := by rw [u32.regs, g31_23]
    have g32_24 : reg n32 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u32.regs, g31_24]
    have g32_25 : reg n32 (25 : Fin 32) = sgl := by rw [u32.regs, g31_25]
    have g32_26 : reg n32 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u32.regs, g31_26]
    have g32_27 : reg n32 (27 : Fin 32) = tbl := by rw [u32.regs, g31_27]
    have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m32]; exact keep_kk31
    clear keep_kk31
    have w32_80 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m32]; exact w31_80
    have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m32]; exact w31_84
    have w32_88 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m32]; exact w31_88
    have w32_8c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m32]; exact w31_8c
    have w32_284 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m32]; exact w31_284
    have w32_288 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m32]; exact w31_288
    have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m32]; exact w31_420
    have w32_428 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m32]; exact w31_428
    have w32_42c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m32]; exact w31_42c
    have b32_98 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m32]; exact b31_98
    have b32_424 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m32]; exact b31_424
    have b32_425 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m32]; exact b31_425
    have b32_426 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m32]; exact b31_426
    have b32_427 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m32]; exact b31_427
    clear b31_427 b31_426 b31_425 b31_424 b31_98 w31_42c w31_428 w31_420 w31_288 w31_284 w31_8c w31_88 w31_84 w31_80 g31_8 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_10 g31_9 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 rb31 s31 m31 u31 c31 g30_10
    -- 0x2FA: branch, taken
    obtain ⟨n33, d33, u33⟩ := s32.taken E32.self 0x7A4 sv_at_2fa
      (by decide) (by rw [g32_10, s32.zero]; decide)
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
    have g33_8 : reg n33 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u33.regs, g32_8]
    have g33_9 : reg n33 (9 : Fin 32) = tbp := by rw [u33.regs, g32_9]
    have g33_10 : reg n33 a0 = BitVec.ofNat 32 0x1 := by rw [u33.regs, g32_10]
    have g33_18 : reg n33 (18 : Fin 32) = out := by rw [u33.regs, g32_18]
    have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [u33.regs, g32_19]
    have g33_20 : reg n33 (20 : Fin 32) = dg := by rw [u33.regs, g32_20]
    have g33_21 : reg n33 (21 : Fin 32) = rootp := by rw [u33.regs, g32_21]
    have g33_22 : reg n33 (22 : Fin 32) = ll := by rw [u33.regs, g32_22]
    have g33_23 : reg n33 (23 : Fin 32) = sgp := by rw [u33.regs, g32_23]
    have g33_24 : reg n33 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u33.regs, g32_24]
    have g33_25 : reg n33 (25 : Fin 32) = sgl := by rw [u33.regs, g32_25]
    have g33_26 : reg n33 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u33.regs, g32_26]
    have g33_27 : reg n33 (27 : Fin 32) = tbl := by rw [u33.regs, g32_27]
    have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m33]; exact keep_kk32
    clear keep_kk32
    have w33_80 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m33]; exact w32_80
    have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m33]; exact w32_84
    have w33_88 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m33]; exact w32_88
    have w33_8c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m33]; exact w32_8c
    have w33_284 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m33]; exact w32_284
    have w33_288 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m33]; exact w32_288
    have w33_420 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m33]; exact w32_420
    have w33_428 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m33]; exact w32_428
    have w33_42c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m33]; exact w32_42c
    have b33_98 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m33]; exact b32_98
    have b33_424 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m33]; exact b32_424
    have b33_425 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m33]; exact b32_425
    have b33_426 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m33]; exact b32_426
    have b33_427 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m33]; exact b32_427
    clear b32_427 b32_426 b32_425 b32_424 b32_98 w32_42c w32_428 w32_420 w32_288 w32_284 w32_8c w32_88 w32_84 w32_80 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_10 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
    exact .inl ⟨(fun ⟨tl2', h0', tl6', h1', op15', ol15', prp15', pu15', h2', ta15', h3', h4', h5', h6', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr6] at h1'; cases h1'; rw [hr15] at h2'; cases h2'; rw [hta15] at h3'; cases h3'; exact hz_30 h6'), sv_fail F E33 s33 t33 (fun x hx => (fR33 x hx).trans (fM x hx).symm) V33 hret g33_2 g33_18 hO g33_3 g33_4 (by rw [g33_8]; sv_code)⟩
  have g30_10 : reg n30 a0 = BitVec.ofNat 32 0 := by rw [a0_30, ite_eq_left hz_30]; rfl
  -- 0x2F4
  obtain ⟨n31, c31, u31⟩ := s30.block svL52f4 E30.self svL52f4_end
    ⟨trivial, trivial⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have s31 : St n31.mem SV n31 0x2F6 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have rb31 : ∀ q, reg n31 q = (runBlock svL52f4 (n30.mem, reg n30)).2 q := fun q => by rw [u31.regs]
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
  have g31_9 : reg n31 (9 : Fin 32) = tbp := by
    rw [rb31, runBlock_reg _ _ _ (9 : Fin 32) s30.zero (by decide), g30_9]
  have g31_10 : reg n31 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb31, runBlock_reg _ _ _ a0 s30.zero (by decide), g30_10]
  have g31_18 : reg n31 (18 : Fin 32) = out := by
    rw [rb31, runBlock_reg _ _ _ (18 : Fin 32) s30.zero (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by
    rw [rb31, runBlock_reg _ _ _ (19 : Fin 32) s30.zero (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = dg := by
    rw [rb31, runBlock_reg _ _ _ (20 : Fin 32) s30.zero (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = rootp := by
    rw [rb31, runBlock_reg _ _ _ (21 : Fin 32) s30.zero (by decide), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = ll := by
    rw [rb31, runBlock_reg _ _ _ (22 : Fin 32) s30.zero (by decide), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = sgp := by
    rw [rb31, runBlock_reg _ _ _ (23 : Fin 32) s30.zero (by decide), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb31, runBlock_reg _ _ _ (24 : Fin 32) s30.zero (by decide), g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = sgl := by
    rw [rb31, runBlock_reg _ _ _ (25 : Fin 32) s30.zero (by decide), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
    rw [rb31, runBlock_reg _ _ _ (26 : Fin 32) s30.zero (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = tbl := by
    rw [rb31, runBlock_reg _ _ _ (27 : Fin 32) s30.zero (by decide), g30_27]
  have g31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb31]; simp +decide only [runBlock, BInstr.run, svL52f4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_10, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, s30.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_80 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m31]; exact w30_80
  have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m31]; exact w30_84
  have w31_88 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m31]; exact w30_88
  have w31_8c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m31]; exact w30_8c
  have w31_284 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m31]; exact w30_284
  have w31_288 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m31]; exact w30_288
  have w31_420 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m31]; exact w30_420
  have w31_428 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m31]; exact w30_428
  have w31_42c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m31]; exact w30_42c
  have b31_98 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m31]; exact b30_98
  have b31_424 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m31]; exact b30_424
  have b31_425 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m31]; exact b30_425
  have b31_426 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m31]; exact b30_426
  have b31_427 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m31]; exact b30_427
  clear b30_427 b30_426 b30_425 b30_424 b30_98 w30_42c w30_428 w30_420 w30_288 w30_284 w30_8c w30_88 w30_84 w30_80 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 K30 a0_30 rk30 s30 c30
  -- 0x2F6: branch, not taken
  obtain ⟨n32, d32, u32⟩ := s31.notTaken E31.self 0x2FA sv_at_2f6
    (by decide) (by rw [g31_24, s31.zero]; decide)
  have s32 : St n32.mem SV n32 0x2FA (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans (.single d32)
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u32.regs, g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = tbp := by rw [u32.regs, g31_9]
  have g32_10 : reg n32 a0 = BitVec.ofNat 32 0x0 := by rw [u32.regs, g31_10]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = dg := by rw [u32.regs, g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = rootp := by rw [u32.regs, g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = ll := by rw [u32.regs, g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = sgp := by rw [u32.regs, g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u32.regs, g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = sgl := by rw [u32.regs, g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u32.regs, g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = tbl := by rw [u32.regs, g31_27]
  have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m32]; exact keep_kk31
  clear keep_kk31
  have w32_80 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m32]; exact w31_80
  have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m32]; exact w31_84
  have w32_88 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m32]; exact w31_88
  have w32_8c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m32]; exact w31_8c
  have w32_284 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m32]; exact w31_284
  have w32_288 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m32]; exact w31_288
  have w32_420 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m32]; exact w31_420
  have w32_428 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m32]; exact w31_428
  have w32_42c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m32]; exact w31_42c
  have b32_98 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m32]; exact b31_98
  have b32_424 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m32]; exact b31_424
  have b32_425 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m32]; exact b31_425
  have b32_426 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m32]; exact b31_426
  have b32_427 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m32]; exact b31_427
  clear b31_427 b31_426 b31_425 b31_424 b31_98 w31_42c w31_428 w31_420 w31_288 w31_284 w31_8c w31_88 w31_84 w31_80 g31_8 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_10 g31_9 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 rb31 s31 m31 u31 c31 g30_10
  -- 0x2FA: branch, not taken
  obtain ⟨n33, d33, u33⟩ := s32.notTaken E32.self 0x2FE sv_at_2fa
    (by decide) (by rw [g32_10, s32.zero]; decide)
  have s33 : St n33.mem SV n33 0x2FE (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
  have t33 : Steps n0 n33 := t32.trans (.single d33)
  have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.same m33
  have g33_2 : reg n33 sp = B + 0x21A0 := by rw [u33.regs, g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u33.regs, g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u33.regs, g32_4]
  have g33_8 : reg n33 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u33.regs, g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = tbp := by rw [u33.regs, g32_9]
  have g33_10 : reg n33 a0 = BitVec.ofNat 32 0x0 := by rw [u33.regs, g32_10]
  have g33_18 : reg n33 (18 : Fin 32) = out := by rw [u33.regs, g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [u33.regs, g32_19]
  have g33_20 : reg n33 (20 : Fin 32) = dg := by rw [u33.regs, g32_20]
  have g33_21 : reg n33 (21 : Fin 32) = rootp := by rw [u33.regs, g32_21]
  have g33_22 : reg n33 (22 : Fin 32) = ll := by rw [u33.regs, g32_22]
  have g33_23 : reg n33 (23 : Fin 32) = sgp := by rw [u33.regs, g32_23]
  have g33_24 : reg n33 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u33.regs, g32_24]
  have g33_25 : reg n33 (25 : Fin 32) = sgl := by rw [u33.regs, g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u33.regs, g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = tbl := by rw [u33.regs, g32_27]
  have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m33]; exact keep_kk32
  clear keep_kk32
  have w33_80 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m33]; exact w32_80
  have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m33]; exact w32_84
  have w33_88 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m33]; exact w32_88
  have w33_8c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m33]; exact w32_8c
  have w33_284 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m33]; exact w32_284
  have w33_288 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m33]; exact w32_288
  have w33_420 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m33]; exact w32_420
  have w33_428 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m33]; exact w32_428
  have w33_42c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m33]; exact w32_42c
  have b33_98 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m33]; exact b32_98
  have b33_424 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m33]; exact b32_424
  have b33_425 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m33]; exact b32_425
  have b33_426 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m33]; exact b32_426
  have b33_427 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m33]; exact b32_427
  clear b32_427 b32_426 b32_425 b32_424 b32_98 w32_42c w32_428 w32_420 w32_288 w32_284 w32_8c w32_88 w32_84 w32_80 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_10 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
  -- 0x2FE
  obtain ⟨n34, c34, u34⟩ := s33.block svL52fe E33.self svL52fe_end
    ⟨trivial, trivial, trivial⟩
  have m34 : n34.mem = n33.mem := u34.mem
  have s34 : St n34.mem SV n34 0x304 (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
  have rb34 : ∀ q, reg n34 q = (runBlock svL52fe (n33.mem, reg n33)).2 q := fun q => by rw [u34.regs]
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
  have g34_8 : reg n34 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb34, runBlock_reg _ _ _ (8 : Fin 32) s33.zero (by decide), g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = tbp := by
    rw [rb34, runBlock_reg _ _ _ (9 : Fin 32) s33.zero (by decide), g33_9]
  have g34_18 : reg n34 (18 : Fin 32) = out := by
    rw [rb34, runBlock_reg _ _ _ (18 : Fin 32) s33.zero (by decide), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by
    rw [rb34, runBlock_reg _ _ _ (19 : Fin 32) s33.zero (by decide), g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = dg := by
    rw [rb34, runBlock_reg _ _ _ (20 : Fin 32) s33.zero (by decide), g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = rootp := by
    rw [rb34, runBlock_reg _ _ _ (21 : Fin 32) s33.zero (by decide), g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = ll := by
    rw [rb34, runBlock_reg _ _ _ (22 : Fin 32) s33.zero (by decide), g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = sgp := by
    rw [rb34, runBlock_reg _ _ _ (23 : Fin 32) s33.zero (by decide), g33_23]
  have g34_24 : reg n34 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb34, runBlock_reg _ _ _ (24 : Fin 32) s33.zero (by decide), g33_24]
  have g34_25 : reg n34 (25 : Fin 32) = sgl := by
    rw [rb34, runBlock_reg _ _ _ (25 : Fin 32) s33.zero (by decide), g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
    rw [rb34, runBlock_reg _ _ _ (26 : Fin 32) s33.zero (by decide), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = tbl := by
    rw [rb34, runBlock_reg _ _ _ (27 : Fin 32) s33.zero (by decide), g33_27]
  have g34_10 : reg n34 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80 := by
    rw [rb34]; simp +decide only [runBlock, BInstr.run, svL52fe, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g33_2, g33_3, g33_4, g33_8, g33_9, g33_10, g33_18, g33_19, g33_20, g33_21, g33_22, g33_23, g33_24, g33_25, g33_26, g33_27, s33.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g34_11 : reg n34 a1 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb34]; simp +decide only [runBlock, BInstr.run, svL52fe, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g33_2, g33_3, g33_4, g33_8, g33_9, g33_10, g33_18, g33_19, g33_20, g33_21, g33_22, g33_23, g33_24, g33_25, g33_26, g33_27, s33.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8)] := by rw [m34]; exact keep_kk33
  clear keep_kk33
  have w34_80 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = op15 := by rw [m34]; exact w33_80
  have w34_84 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = BitVec.ofNat 32 ol15 := by rw [m34]; exact w33_84
  have w34_88 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m34]; exact w33_88
  have w34_8c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m34]; exact w33_8c
  have w34_284 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m34]; exact w33_284
  have w34_288 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m34]; exact w33_288
  have w34_420 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m34]; exact w33_420
  have w34_428 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = (((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m34]; exact w33_428
  have w34_42c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len) := by rw [m34]; exact w33_42c
  have b34_98 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m34]; exact b33_98
  have b34_424 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m34]; exact b33_424
  have b34_425 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m34]; exact b33_425
  have b34_426 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m34]; exact b33_426
  have b34_427 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m34]; exact b33_427
  clear b33_427 b33_426 b33_425 b33_424 b33_98 w33_42c w33_428 w33_420 w33_288 w33_284 w33_8c w33_88 w33_84 w33_80 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_10 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 m33 s33 u33 d33
  -- 0x304: sv_bitsF
  obtain ⟨n35, c35, s35, sp35, rk35, K35, A35, Ok35, Er35, fr35⟩ := sv_bitsF (oc := 0x80) (dc := 0x420)
    F E34 s34 sv_at_304 sv_at_308 (by decide) (by decide) g34_2 g34_10 g34_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w34_428 w34_42c (((tb_in.restW hr2).content hr6).restN hta15)
  have t35 : Steps n0 n35 := t34.trans c35
  have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.keepL K35 (by decide)
  rw [sv_mb fR34 (((tb_in.restW hr2).content hr6).restN hta15)] at A35 Ok35 Er35
  have g35_2 : reg n35 sp = B + 0x21A0 := by rw [rk35 sp (by decide) (by decide), g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk35 (3 : Fin 32) (by decide) (by decide), g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk35 (4 : Fin 32) (by decide) (by decide), g34_4]
  have g35_8 : reg n35 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rk35 (8 : Fin 32) (by decide) (by decide), g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = tbp := by rw [rk35 (9 : Fin 32) (by decide) (by decide), g34_9]
  have g35_18 : reg n35 (18 : Fin 32) = out := by rw [rk35 (18 : Fin 32) (by decide) (by decide), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [rk35 (19 : Fin 32) (by decide) (by decide), g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = dg := by rw [rk35 (20 : Fin 32) (by decide) (by decide), g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = rootp := by rw [rk35 (21 : Fin 32) (by decide) (by decide), g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = ll := by rw [rk35 (22 : Fin 32) (by decide) (by decide), g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = sgp := by rw [rk35 (23 : Fin 32) (by decide) (by decide), g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rk35 (24 : Fin 32) (by decide) (by decide), g34_24]
  have g35_25 : reg n35 (25 : Fin 32) = sgl := by rw [rk35 (25 : Fin 32) (by decide) (by decide), g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [rk35 (26 : Fin 32) (by decide) (by decide), g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = tbl := by rw [rk35 (27 : Fin 32) (by decide) (by decide), g34_27]
  obtain ⟨r35, hr35⟩ : ∃ r, derElement 3 (memBytes M0 ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)).toNat) = r := ⟨_, rfl⟩
  rcases r35 with er35 | tl35
  · obtain ⟨zhr35, ezhr35⟩ := Er35 er35 (by rw [hr35]; rfl)
    have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := keep_kk34.trans K35
    clear keep_kk34
    have w35_88 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := (K35.w32 (by decide) (by decide)).trans w34_88
    have w35_8c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := (K35.w32 (by decide) (by decide)).trans w34_8c
    have w35_284 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K35.w32 (by decide) (by decide)).trans w34_284
    have w35_288 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K35.w32 (by decide) (by decide)).trans w34_288
    have w35_420 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K35.w32 (by decide) (by decide)).trans w34_420
    have b35_98 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := (K35.b8 (by decide) (by decide)).trans b34_98
    have b35_424 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := (K35.b8 (by decide) (by decide)).trans b34_424
    have b35_425 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K35.b8 (by decide) (by decide)).trans b34_425
    have b35_426 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K35.b8 (by decide) (by decide)).trans b34_426
    have b35_427 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K35.b8 (by decide) (by decide)).trans b34_427
    have w35_80 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := zhr35
    have b35_84 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er35 := ezhr35
    clear b34_427 b34_426 b34_425 b34_424 b34_98 w34_42c w34_428 w34_420 w34_288 w34_284 w34_8c w34_88 w34_84 w34_80 g34_11 g34_10 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 rb34 s34 m34 u34 c34
    -- 0x30C: lw
    obtain ⟨n36, d36, u36⟩ := s35.lw E35.self sv_at_30c (off' := 0x30E) (by decide)
      (by rw [g35_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s36 : St n36.mem SV n36 0x30E (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
    have m36 : n36.mem = n35.mem := u36.mem
    have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
    have t36 : Steps n0 n36 := t35.trans (.single d36)
    have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
    have E36 : SvCode n36.mem := E35.fr F fr36
    have V36 : SvSaves B n36.mem v := V35.same m36
    have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_2]
    have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_3]
    have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_4]
    have g36_8 : reg n36 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_8]
    have g36_9 : reg n36 (9 : Fin 32) = tbp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_9]
    have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, upd_ne (by decide) (by decide), g35_18]
    have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_19]
    have g36_20 : reg n36 (20 : Fin 32) = dg := by rw [u36.regs, upd_ne (by decide) (by decide), g35_20]
    have g36_21 : reg n36 (21 : Fin 32) = rootp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_21]
    have g36_22 : reg n36 (22 : Fin 32) = ll := by rw [u36.regs, upd_ne (by decide) (by decide), g35_22]
    have g36_23 : reg n36 (23 : Fin 32) = sgp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_23]
    have g36_24 : reg n36 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_24]
    have g36_25 : reg n36 (25 : Fin 32) = sgl := by rw [u36.regs, upd_ne (by decide) (by decide), g35_25]
    have g36_26 : reg n36 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_26]
    have g36_27 : reg n36 (27 : Fin 32) = tbl := by rw [u36.regs, upd_ne (by decide) (by decide), g35_27]
    have g36_10 : reg n36 a0 = 0 := by
      rw [u36.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g35_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w35_80]
    have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := by rw [m36]; exact keep_kk35
    clear keep_kk35
    have w36_80 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m36]; exact w35_80
    have w36_88 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m36]; exact w35_88
    have w36_8c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m36]; exact w35_8c
    have w36_284 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m36]; exact w35_284
    have w36_288 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m36]; exact w35_288
    have w36_420 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m36]; exact w35_420
    have b36_84 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er35 := by rw [m36]; exact b35_84
    have b36_98 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m36]; exact b35_98
    have b36_424 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m36]; exact b35_424
    have b36_425 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m36]; exact b35_425
    have b36_426 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m36]; exact b35_426
    have b36_427 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m36]; exact b35_427
    clear b35_84 w35_80 b35_427 b35_426 b35_425 b35_424 b35_98 w35_420 w35_288 w35_284 w35_8c w35_88 ezhr35 zhr35
    -- 0x30E: branch, taken
    obtain ⟨n37, d37, u37⟩ := s36.taken E36.self 0x7A0 sv_at_30e
      (by decide) (by rw [g36_10, s36.zero]; rfl)
    have s37 : St n37.mem SV n37 0x7A0 (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
    have m37 : n37.mem = n36.mem := u37.mem
    have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
    have t37 : Steps n0 n37 := t36.trans (.single d37)
    have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
    have E37 : SvCode n37.mem := E36.fr F fr37
    have V37 : SvSaves B n37.mem v := V36.same m37
    have g37_2 : reg n37 sp = B + 0x21A0 := by rw [u37.regs, g36_2]
    have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u37.regs, g36_3]
    have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u37.regs, g36_4]
    have g37_8 : reg n37 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u37.regs, g36_8]
    have g37_9 : reg n37 (9 : Fin 32) = tbp := by rw [u37.regs, g36_9]
    have g37_10 : reg n37 a0 = 0 := by rw [u37.regs, g36_10]
    have g37_18 : reg n37 (18 : Fin 32) = out := by rw [u37.regs, g36_18]
    have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [u37.regs, g36_19]
    have g37_20 : reg n37 (20 : Fin 32) = dg := by rw [u37.regs, g36_20]
    have g37_21 : reg n37 (21 : Fin 32) = rootp := by rw [u37.regs, g36_21]
    have g37_22 : reg n37 (22 : Fin 32) = ll := by rw [u37.regs, g36_22]
    have g37_23 : reg n37 (23 : Fin 32) = sgp := by rw [u37.regs, g36_23]
    have g37_24 : reg n37 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u37.regs, g36_24]
    have g37_25 : reg n37 (25 : Fin 32) = sgl := by rw [u37.regs, g36_25]
    have g37_26 : reg n37 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u37.regs, g36_26]
    have g37_27 : reg n37 (27 : Fin 32) = tbl := by rw [u37.regs, g36_27]
    have keep_kk37 : SvKeepL B n0.mem n37.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := by rw [m37]; exact keep_kk36
    clear keep_kk36
    have w37_80 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m37]; exact w36_80
    have w37_88 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m37]; exact w36_88
    have w37_8c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m37]; exact w36_8c
    have w37_284 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m37]; exact w36_284
    have w37_288 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m37]; exact w36_288
    have w37_420 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m37]; exact w36_420
    have b37_84 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er35 := by rw [m37]; exact b36_84
    have b37_98 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m37]; exact b36_98
    have b37_424 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m37]; exact b36_424
    have b37_425 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m37]; exact b36_425
    have b37_426 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m37]; exact b36_426
    have b37_427 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m37]; exact b36_427
    clear b36_427 b36_426 b36_425 b36_424 b36_98 b36_84 w36_420 w36_288 w36_284 w36_8c w36_88 w36_80 g36_10 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 m36 s36 u36 d36
    -- 0x7A0: lbu
    obtain ⟨n38, d38, u38⟩ := s37.lbu E37.self sv_at_7a0 (off' := 0x7A4) (by decide)
    have s38 : St n38.mem SV n38 0x7A4 (reg n38) := ⟨u38.pc, rfl, fun _ => rfl⟩
    have m38 : n38.mem = n37.mem := u38.mem
    have fr38 : ∀ x, SvR B x → n38.mem x = n37.mem x := fun x _ => by rw [m38]
    have t38 : Steps n0 n38 := t37.trans (.single d38)
    have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
    have E38 : SvCode n38.mem := E37.fr F fr38
    have V38 : SvSaves B n38.mem v := V37.same m38
    have g38_2 : reg n38 sp = B + 0x21A0 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_2]
    have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_3]
    have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_4]
    have g38_9 : reg n38 (9 : Fin 32) = tbp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_9]
    have g38_10 : reg n38 a0 = 0 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_10]
    have g38_18 : reg n38 (18 : Fin 32) = out := by rw [u38.regs, upd_ne (by decide) (by decide), g37_18]
    have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_19]
    have g38_20 : reg n38 (20 : Fin 32) = dg := by rw [u38.regs, upd_ne (by decide) (by decide), g37_20]
    have g38_21 : reg n38 (21 : Fin 32) = rootp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_21]
    have g38_22 : reg n38 (22 : Fin 32) = ll := by rw [u38.regs, upd_ne (by decide) (by decide), g37_22]
    have g38_23 : reg n38 (23 : Fin 32) = sgp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_23]
    have g38_24 : reg n38 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_24]
    have g38_25 : reg n38 (25 : Fin 32) = sgl := by rw [u38.regs, upd_ne (by decide) (by decide), g37_25]
    have g38_26 : reg n38 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_26]
    have g38_27 : reg n38 (27 : Fin 32) = tbl := by rw [u38.regs, upd_ne (by decide) (by decide), g37_27]
    have g38_8 : reg n38 (8 : Fin 32) = (derErrByte er35).zeroExtend 32 := by
      rw [u38.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g37_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, b37_84]
    have keep_kk38 : SvKeepL B n0.mem n38.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := by rw [m38]; exact keep_kk37
    clear keep_kk37
    have w38_80 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m38]; exact w37_80
    have w38_88 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m38]; exact w37_88
    have w38_8c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m38]; exact w37_8c
    have w38_284 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m38]; exact w37_284
    have w38_288 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m38]; exact w37_288
    have w38_420 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m38]; exact w37_420
    have b38_84 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er35 := by rw [m38]; exact b37_84
    have b38_98 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m38]; exact b37_98
    have b38_424 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m38]; exact b37_424
    have b38_425 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m38]; exact b37_425
    have b38_426 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m38]; exact b37_426
    have b38_427 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m38]; exact b37_427
    clear b37_427 b37_426 b37_425 b37_424 b37_98 b37_84 w37_420 w37_288 w37_284 w37_8c w37_88 w37_80 g37_27 g37_26 g37_25 g37_24 g37_23 g37_22 g37_21 g37_20 g37_19 g37_18 g37_10 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 m37 s37 u37 d37
    exact .inl ⟨(fun ⟨tl2', h0', tl6', h1', op15', ol15', prp15', pu15', h2', ta15', h3', h4', h5', h6', tl35', h7', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr6] at h1'; cases h1'; rw [hr15] at h2'; cases h2'; rw [hta15] at h3'; cases h3'; rw [hr35] at h7'; cases h7'), sv_fail F E38 s38 t38 (fun x hx => (fR38 x hx).trans (fM x hx).symm) V38 hret g38_2 g38_18 hO g38_3 g38_4 (by rw [g38_8]; sv_code)⟩
  obtain ⟨r35b, hr35b⟩ : ∃ r, derBitsOf (memBytes M0 ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)).toNat) ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) (.ok tl35) = r := ⟨_, rfl⟩
  rcases r35b with er35b | ⟨bp35, bl35⟩
  · obtain ⟨zhr35b, ezhr35b⟩ := Er35 er35b (by rw [hr35, hr35b])
    have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := keep_kk34.trans K35
    clear keep_kk34
    have w35_88 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := (K35.w32 (by decide) (by decide)).trans w34_88
    have w35_8c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := (K35.w32 (by decide) (by decide)).trans w34_8c
    have w35_284 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K35.w32 (by decide) (by decide)).trans w34_284
    have w35_288 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K35.w32 (by decide) (by decide)).trans w34_288
    have w35_420 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K35.w32 (by decide) (by decide)).trans w34_420
    have b35_98 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := (K35.b8 (by decide) (by decide)).trans b34_98
    have b35_424 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := (K35.b8 (by decide) (by decide)).trans b34_424
    have b35_425 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K35.b8 (by decide) (by decide)).trans b34_425
    have b35_426 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K35.b8 (by decide) (by decide)).trans b34_426
    have b35_427 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K35.b8 (by decide) (by decide)).trans b34_427
    have w35_80 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := zhr35b
    have b35_84 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er35b := ezhr35b
    clear b34_427 b34_426 b34_425 b34_424 b34_98 w34_42c w34_428 w34_420 w34_288 w34_284 w34_8c w34_88 w34_84 w34_80 g34_11 g34_10 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 rb34 s34 m34 u34 c34
    -- 0x30C: lw
    obtain ⟨n36, d36, u36⟩ := s35.lw E35.self sv_at_30c (off' := 0x30E) (by decide)
      (by rw [g35_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s36 : St n36.mem SV n36 0x30E (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
    have m36 : n36.mem = n35.mem := u36.mem
    have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
    have t36 : Steps n0 n36 := t35.trans (.single d36)
    have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
    have E36 : SvCode n36.mem := E35.fr F fr36
    have V36 : SvSaves B n36.mem v := V35.same m36
    have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_2]
    have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_3]
    have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_4]
    have g36_8 : reg n36 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_8]
    have g36_9 : reg n36 (9 : Fin 32) = tbp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_9]
    have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, upd_ne (by decide) (by decide), g35_18]
    have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_19]
    have g36_20 : reg n36 (20 : Fin 32) = dg := by rw [u36.regs, upd_ne (by decide) (by decide), g35_20]
    have g36_21 : reg n36 (21 : Fin 32) = rootp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_21]
    have g36_22 : reg n36 (22 : Fin 32) = ll := by rw [u36.regs, upd_ne (by decide) (by decide), g35_22]
    have g36_23 : reg n36 (23 : Fin 32) = sgp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_23]
    have g36_24 : reg n36 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_24]
    have g36_25 : reg n36 (25 : Fin 32) = sgl := by rw [u36.regs, upd_ne (by decide) (by decide), g35_25]
    have g36_26 : reg n36 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_26]
    have g36_27 : reg n36 (27 : Fin 32) = tbl := by rw [u36.regs, upd_ne (by decide) (by decide), g35_27]
    have g36_10 : reg n36 a0 = 0 := by
      rw [u36.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g35_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w35_80]
    have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := by rw [m36]; exact keep_kk35
    clear keep_kk35
    have w36_80 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m36]; exact w35_80
    have w36_88 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m36]; exact w35_88
    have w36_8c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m36]; exact w35_8c
    have w36_284 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m36]; exact w35_284
    have w36_288 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m36]; exact w35_288
    have w36_420 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m36]; exact w35_420
    have b36_84 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er35b := by rw [m36]; exact b35_84
    have b36_98 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m36]; exact b35_98
    have b36_424 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m36]; exact b35_424
    have b36_425 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m36]; exact b35_425
    have b36_426 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m36]; exact b35_426
    have b36_427 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m36]; exact b35_427
    clear b35_84 w35_80 b35_427 b35_426 b35_425 b35_424 b35_98 w35_420 w35_288 w35_284 w35_8c w35_88 ezhr35b zhr35b
    -- 0x30E: branch, taken
    obtain ⟨n37, d37, u37⟩ := s36.taken E36.self 0x7A0 sv_at_30e
      (by decide) (by rw [g36_10, s36.zero]; rfl)
    have s37 : St n37.mem SV n37 0x7A0 (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
    have m37 : n37.mem = n36.mem := u37.mem
    have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
    have t37 : Steps n0 n37 := t36.trans (.single d37)
    have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
    have E37 : SvCode n37.mem := E36.fr F fr37
    have V37 : SvSaves B n37.mem v := V36.same m37
    have g37_2 : reg n37 sp = B + 0x21A0 := by rw [u37.regs, g36_2]
    have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u37.regs, g36_3]
    have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u37.regs, g36_4]
    have g37_8 : reg n37 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u37.regs, g36_8]
    have g37_9 : reg n37 (9 : Fin 32) = tbp := by rw [u37.regs, g36_9]
    have g37_10 : reg n37 a0 = 0 := by rw [u37.regs, g36_10]
    have g37_18 : reg n37 (18 : Fin 32) = out := by rw [u37.regs, g36_18]
    have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [u37.regs, g36_19]
    have g37_20 : reg n37 (20 : Fin 32) = dg := by rw [u37.regs, g36_20]
    have g37_21 : reg n37 (21 : Fin 32) = rootp := by rw [u37.regs, g36_21]
    have g37_22 : reg n37 (22 : Fin 32) = ll := by rw [u37.regs, g36_22]
    have g37_23 : reg n37 (23 : Fin 32) = sgp := by rw [u37.regs, g36_23]
    have g37_24 : reg n37 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u37.regs, g36_24]
    have g37_25 : reg n37 (25 : Fin 32) = sgl := by rw [u37.regs, g36_25]
    have g37_26 : reg n37 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u37.regs, g36_26]
    have g37_27 : reg n37 (27 : Fin 32) = tbl := by rw [u37.regs, g36_27]
    have keep_kk37 : SvKeepL B n0.mem n37.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := by rw [m37]; exact keep_kk36
    clear keep_kk36
    have w37_80 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m37]; exact w36_80
    have w37_88 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m37]; exact w36_88
    have w37_8c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m37]; exact w36_8c
    have w37_284 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m37]; exact w36_284
    have w37_288 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m37]; exact w36_288
    have w37_420 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m37]; exact w36_420
    have b37_84 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er35b := by rw [m37]; exact b36_84
    have b37_98 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m37]; exact b36_98
    have b37_424 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m37]; exact b36_424
    have b37_425 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m37]; exact b36_425
    have b37_426 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m37]; exact b36_426
    have b37_427 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m37]; exact b36_427
    clear b36_427 b36_426 b36_425 b36_424 b36_98 b36_84 w36_420 w36_288 w36_284 w36_8c w36_88 w36_80 g36_10 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 m36 s36 u36 d36
    -- 0x7A0: lbu
    obtain ⟨n38, d38, u38⟩ := s37.lbu E37.self sv_at_7a0 (off' := 0x7A4) (by decide)
    have s38 : St n38.mem SV n38 0x7A4 (reg n38) := ⟨u38.pc, rfl, fun _ => rfl⟩
    have m38 : n38.mem = n37.mem := u38.mem
    have fr38 : ∀ x, SvR B x → n38.mem x = n37.mem x := fun x _ => by rw [m38]
    have t38 : Steps n0 n38 := t37.trans (.single d38)
    have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
    have E38 : SvCode n38.mem := E37.fr F fr38
    have V38 : SvSaves B n38.mem v := V37.same m38
    have g38_2 : reg n38 sp = B + 0x21A0 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_2]
    have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_3]
    have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_4]
    have g38_9 : reg n38 (9 : Fin 32) = tbp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_9]
    have g38_10 : reg n38 a0 = 0 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_10]
    have g38_18 : reg n38 (18 : Fin 32) = out := by rw [u38.regs, upd_ne (by decide) (by decide), g37_18]
    have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_19]
    have g38_20 : reg n38 (20 : Fin 32) = dg := by rw [u38.regs, upd_ne (by decide) (by decide), g37_20]
    have g38_21 : reg n38 (21 : Fin 32) = rootp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_21]
    have g38_22 : reg n38 (22 : Fin 32) = ll := by rw [u38.regs, upd_ne (by decide) (by decide), g37_22]
    have g38_23 : reg n38 (23 : Fin 32) = sgp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_23]
    have g38_24 : reg n38 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_24]
    have g38_25 : reg n38 (25 : Fin 32) = sgl := by rw [u38.regs, upd_ne (by decide) (by decide), g37_25]
    have g38_26 : reg n38 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_26]
    have g38_27 : reg n38 (27 : Fin 32) = tbl := by rw [u38.regs, upd_ne (by decide) (by decide), g37_27]
    have g38_8 : reg n38 (8 : Fin 32) = (derErrByte er35b).zeroExtend 32 := by
      rw [u38.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g37_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, b37_84]
    have keep_kk38 : SvKeepL B n0.mem n38.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := by rw [m38]; exact keep_kk37
    clear keep_kk37
    have w38_80 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = 0 := by rw [m38]; exact w37_80
    have w38_88 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m38]; exact w37_88
    have w38_8c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m38]; exact w37_8c
    have w38_284 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m38]; exact w37_284
    have w38_288 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m38]; exact w37_288
    have w38_420 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m38]; exact w37_420
    have b38_84 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = derErrByte er35b := by rw [m38]; exact b37_84
    have b38_98 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m38]; exact b37_98
    have b38_424 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m38]; exact b37_424
    have b38_425 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m38]; exact b37_425
    have b38_426 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m38]; exact b37_426
    have b38_427 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m38]; exact b37_427
    clear b37_427 b37_426 b37_425 b37_424 b37_98 b37_84 w37_420 w37_288 w37_284 w37_8c w37_88 w37_80 g37_27 g37_26 g37_25 g37_24 g37_23 g37_22 g37_21 g37_20 g37_19 g37_18 g37_10 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 m37 s37 u37 d37
    exact .inl ⟨(fun ⟨tl2', h0', tl6', h1', op15', ol15', prp15', pu15', h2', ta15', h3', h4', h5', h6', tl35', h7', bp35', bl35', h8', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr6] at h1'; cases h1'; rw [hr15] at h2'; cases h2'; rw [hta15] at h3'; cases h3'; rw [hr35] at h7'; cases h7'; rw [hr35b] at h8'; cases h8'), sv_fail F E38 s38 t38 (fun x hx => (fR38 x hx).trans (fM x hx).symm) V38 hret g38_2 g38_18 hO g38_3 g38_4 (by rw [g38_8]; sv_code)⟩
  obtain ⟨p0_35, p4_35⟩ := Ok35 bp35 bl35 (by rw [hr35, hr35b])
  obtain ⟨d8_35, d12_35⟩ := A35 tl35 hr35
  have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := keep_kk34.trans K35
  clear keep_kk34
  have w35_88 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := (K35.w32 (by decide) (by decide)).trans w34_88
  have w35_8c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := (K35.w32 (by decide) (by decide)).trans w34_8c
  have w35_284 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K35.w32 (by decide) (by decide)).trans w34_284
  have w35_288 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K35.w32 (by decide) (by decide)).trans w34_288
  have w35_420 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := (K35.w32 (by decide) (by decide)).trans w34_420
  have b35_98 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := (K35.b8 (by decide) (by decide)).trans b34_98
  have b35_424 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := (K35.b8 (by decide) (by decide)).trans b34_424
  have b35_425 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := (K35.b8 (by decide) (by decide)).trans b34_425
  have b35_426 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := (K35.b8 (by decide) (by decide)).trans b34_426
  have b35_427 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := (K35.b8 (by decide) (by decide)).trans b34_427
  have w35_80 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp35 := p0_35
  have w35_84 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl35 := p4_35
  have w35_428 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) + BitVec.ofNat 32 (tl35.header + tl35.len) := d8_35
  have w35_42c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) := d12_35
  clear b34_427 b34_426 b34_425 b34_424 b34_98 w34_42c w34_428 w34_420 w34_288 w34_284 w34_8c w34_88 w34_84 w34_80 g34_11 g34_10 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 rb34 s34 m34 u34 c34
  -- 0x30C: lw
  obtain ⟨n36, d36, u36⟩ := s35.lw E35.self sv_at_30c (off' := 0x30E) (by decide)
    (by rw [g35_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s36 : St n36.mem SV n36 0x30E (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
  have m36 : n36.mem = n35.mem := u36.mem
  have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
  have t36 : Steps n0 n36 := t35.trans (.single d36)
  have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.same m36
  have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_4]
  have g36_8 : reg n36 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_8]
  have g36_9 : reg n36 (9 : Fin 32) = tbp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_9]
  have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, upd_ne (by decide) (by decide), g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_19]
  have g36_20 : reg n36 (20 : Fin 32) = dg := by rw [u36.regs, upd_ne (by decide) (by decide), g35_20]
  have g36_21 : reg n36 (21 : Fin 32) = rootp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = ll := by rw [u36.regs, upd_ne (by decide) (by decide), g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = sgp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_23]
  have g36_24 : reg n36 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_24]
  have g36_25 : reg n36 (25 : Fin 32) = sgl := by rw [u36.regs, upd_ne (by decide) (by decide), g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = tbl := by rw [u36.regs, upd_ne (by decide) (by decide), g35_27]
  have g36_10 : reg n36 a0 = bp35 := by
    rw [u36.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g35_2, show B + 0x21A0 + 0x80 = B + 0x21A0 + BitVec.ofNat 32 0x80 by sv_addr, w35_80]
  have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := by rw [m36]; exact keep_kk35
  clear keep_kk35
  have w36_80 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp35 := by rw [m36]; exact w35_80
  have w36_84 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl35 := by rw [m36]; exact w35_84
  have w36_88 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m36]; exact w35_88
  have w36_8c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m36]; exact w35_8c
  have w36_284 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m36]; exact w35_284
  have w36_288 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m36]; exact w35_288
  have w36_420 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m36]; exact w35_420
  have w36_428 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m36]; exact w35_428
  have w36_42c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m36]; exact w35_42c
  have b36_98 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m36]; exact b35_98
  have b36_424 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m36]; exact b35_424
  have b36_425 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m36]; exact b35_425
  have b36_426 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m36]; exact b35_426
  have b36_427 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m36]; exact b35_427
  clear w35_42c w35_428 w35_84 w35_80 b35_427 b35_426 b35_425 b35_424 b35_98 w35_420 w35_288 w35_284 w35_8c w35_88 d12_35 d8_35 p4_35 p0_35 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 Er35 Ok35 A35 K35 rk35 sp35 s35 c35
  -- 0x30E: branch, not taken
  obtain ⟨n37, d37, u37⟩ := s36.notTaken E36.self 0x312 sv_at_30e
    (by decide) (by rw [g36_10, s36.zero]; exact br_beq_f (((((tb_in.restW hr2).content hr6).restN hta15).bitsW hr35 hr35b).pos_ne))
  have s37 : St n37.mem SV n37 0x312 (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
  have m37 : n37.mem = n36.mem := u37.mem
  have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
  have t37 : Steps n0 n37 := t36.trans (.single d37)
  have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : SvCode n37.mem := E36.fr F fr37
  have V37 : SvSaves B n37.mem v := V36.same m37
  have g37_2 : reg n37 sp = B + 0x21A0 := by rw [u37.regs, g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u37.regs, g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u37.regs, g36_4]
  have g37_8 : reg n37 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u37.regs, g36_8]
  have g37_9 : reg n37 (9 : Fin 32) = tbp := by rw [u37.regs, g36_9]
  have g37_10 : reg n37 a0 = bp35 := by rw [u37.regs, g36_10]
  have g37_18 : reg n37 (18 : Fin 32) = out := by rw [u37.regs, g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [u37.regs, g36_19]
  have g37_20 : reg n37 (20 : Fin 32) = dg := by rw [u37.regs, g36_20]
  have g37_21 : reg n37 (21 : Fin 32) = rootp := by rw [u37.regs, g36_21]
  have g37_22 : reg n37 (22 : Fin 32) = ll := by rw [u37.regs, g36_22]
  have g37_23 : reg n37 (23 : Fin 32) = sgp := by rw [u37.regs, g36_23]
  have g37_24 : reg n37 (24 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u37.regs, g36_24]
  have g37_25 : reg n37 (25 : Fin 32) = sgl := by rw [u37.regs, g36_25]
  have g37_26 : reg n37 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u37.regs, g36_26]
  have g37_27 : reg n37 (27 : Fin 32) = tbl := by rw [u37.regs, g36_27]
  have keep_kk37 : SvKeepL B n0.mem n37.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := by rw [m37]; exact keep_kk36
  clear keep_kk36
  have w37_80 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp35 := by rw [m37]; exact w36_80
  have w37_84 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl35 := by rw [m37]; exact w36_84
  have w37_88 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m37]; exact w36_88
  have w37_8c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m37]; exact w36_8c
  have w37_284 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m37]; exact w36_284
  have w37_288 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m37]; exact w36_288
  have w37_420 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m37]; exact w36_420
  have w37_428 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m37]; exact w36_428
  have w37_42c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m37]; exact w36_42c
  have b37_98 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m37]; exact b36_98
  have b37_424 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m37]; exact b36_424
  have b37_425 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m37]; exact b36_425
  have b37_426 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m37]; exact b36_426
  have b37_427 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m37]; exact b36_427
  clear b36_427 b36_426 b36_425 b36_424 b36_98 w36_42c w36_428 w36_420 w36_288 w36_284 w36_8c w36_88 w36_84 w36_80 g36_10 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 m36 s36 u36 d36
  -- 0x312
  obtain ⟨n38, c38, u38⟩ := s37.block svL5312 E37.self svL5312_end
    ⟨trivial, trivial⟩
  have m38 : n38.mem = n37.mem := u38.mem
  have s38 : St n38.mem SV n38 0x314 (reg n38) := ⟨u38.pc, rfl, fun _ => rfl⟩
  have rb38 : ∀ q, reg n38 q = (runBlock svL5312 (n37.mem, reg n37)).2 q := fun q => by rw [u38.regs]
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
  have g38_8 : reg n38 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb38, runBlock_reg _ _ _ (8 : Fin 32) s37.zero (by decide), g37_8]
  have g38_9 : reg n38 (9 : Fin 32) = tbp := by
    rw [rb38, runBlock_reg _ _ _ (9 : Fin 32) s37.zero (by decide), g37_9]
  have g38_10 : reg n38 a0 = bp35 := by
    rw [rb38, runBlock_reg _ _ _ a0 s37.zero (by decide), g37_10]
  have g38_18 : reg n38 (18 : Fin 32) = out := by
    rw [rb38, runBlock_reg _ _ _ (18 : Fin 32) s37.zero (by decide), g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = bp := by
    rw [rb38, runBlock_reg _ _ _ (19 : Fin 32) s37.zero (by decide), g37_19]
  have g38_20 : reg n38 (20 : Fin 32) = dg := by
    rw [rb38, runBlock_reg _ _ _ (20 : Fin 32) s37.zero (by decide), g37_20]
  have g38_21 : reg n38 (21 : Fin 32) = rootp := by
    rw [rb38, runBlock_reg _ _ _ (21 : Fin 32) s37.zero (by decide), g37_21]
  have g38_22 : reg n38 (22 : Fin 32) = ll := by
    rw [rb38, runBlock_reg _ _ _ (22 : Fin 32) s37.zero (by decide), g37_22]
  have g38_23 : reg n38 (23 : Fin 32) = sgp := by
    rw [rb38, runBlock_reg _ _ _ (23 : Fin 32) s37.zero (by decide), g37_23]
  have g38_25 : reg n38 (25 : Fin 32) = sgl := by
    rw [rb38, runBlock_reg _ _ _ (25 : Fin 32) s37.zero (by decide), g37_25]
  have g38_26 : reg n38 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
    rw [rb38, runBlock_reg _ _ _ (26 : Fin 32) s37.zero (by decide), g37_26]
  have g38_27 : reg n38 (27 : Fin 32) = tbl := by
    rw [rb38, runBlock_reg _ _ _ (27 : Fin 32) s37.zero (by decide), g37_27]
  have g38_24 : reg n38 (24 : Fin 32) = bp35 := by
    rw [rb38]; simp +decide only [runBlock, BInstr.run, svL5312, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g37_2, g37_3, g37_4, g37_8, g37_9, g37_10, g37_18, g37_19, g37_20, g37_21, g37_22, g37_23, g37_24, g37_25, g37_26, g37_27, s37.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk38 : SvKeepL B n0.mem n38.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := by rw [m38]; exact keep_kk37
  clear keep_kk37
  have w38_80 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp35 := by rw [m38]; exact w37_80
  have w38_84 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl35 := by rw [m38]; exact w37_84
  have w38_88 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m38]; exact w37_88
  have w38_8c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m38]; exact w37_8c
  have w38_284 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m38]; exact w37_284
  have w38_288 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m38]; exact w37_288
  have w38_420 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m38]; exact w37_420
  have w38_428 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m38]; exact w37_428
  have w38_42c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m38]; exact w37_42c
  have b38_98 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m38]; exact b37_98
  have b38_424 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m38]; exact b37_424
  have b38_425 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m38]; exact b37_425
  have b38_426 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m38]; exact b37_426
  have b38_427 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m38]; exact b37_427
  clear b37_427 b37_426 b37_425 b37_424 b37_98 w37_42c w37_428 w37_420 w37_288 w37_284 w37_8c w37_88 w37_84 w37_80 g37_27 g37_26 g37_25 g37_24 g37_23 g37_22 g37_21 g37_20 g37_19 g37_18 g37_10 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 m37 s37 u37 d37
  -- 0x314: lw
  obtain ⟨n39, d39, u39⟩ := s38.lw E38.self sv_at_314 (off' := 0x316) (by decide)
    (by rw [g38_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s39 : St n39.mem SV n39 0x316 (reg n39) := ⟨u39.pc, rfl, fun _ => rfl⟩
  have m39 : n39.mem = n38.mem := u39.mem
  have fr39 : ∀ x, SvR B x → n39.mem x = n38.mem x := fun x _ => by rw [m39]
  have t39 : Steps n0 n39 := t38.trans (.single d39)
  have fR39 : ∀ x, SvR B x → n39.mem x = M0 x := fun x hx => (fr39 x hx).trans (fR38 x hx)
  have E39 : SvCode n39.mem := E38.fr F fr39
  have V39 : SvSaves B n39.mem v := V38.same m39
  have g39_2 : reg n39 sp = B + 0x21A0 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_2]
  have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u39.regs, upd_ne (by decide) (by decide), g38_3]
  have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u39.regs, upd_ne (by decide) (by decide), g38_4]
  have g39_8 : reg n39 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_8]
  have g39_9 : reg n39 (9 : Fin 32) = tbp := by rw [u39.regs, upd_ne (by decide) (by decide), g38_9]
  have g39_18 : reg n39 (18 : Fin 32) = out := by rw [u39.regs, upd_ne (by decide) (by decide), g38_18]
  have g39_19 : reg n39 (19 : Fin 32) = bp := by rw [u39.regs, upd_ne (by decide) (by decide), g38_19]
  have g39_20 : reg n39 (20 : Fin 32) = dg := by rw [u39.regs, upd_ne (by decide) (by decide), g38_20]
  have g39_21 : reg n39 (21 : Fin 32) = rootp := by rw [u39.regs, upd_ne (by decide) (by decide), g38_21]
  have g39_22 : reg n39 (22 : Fin 32) = ll := by rw [u39.regs, upd_ne (by decide) (by decide), g38_22]
  have g39_23 : reg n39 (23 : Fin 32) = sgp := by rw [u39.regs, upd_ne (by decide) (by decide), g38_23]
  have g39_24 : reg n39 (24 : Fin 32) = bp35 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_24]
  have g39_25 : reg n39 (25 : Fin 32) = sgl := by rw [u39.regs, upd_ne (by decide) (by decide), g38_25]
  have g39_26 : reg n39 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_26]
  have g39_27 : reg n39 (27 : Fin 32) = tbl := by rw [u39.regs, upd_ne (by decide) (by decide), g38_27]
  have g39_10 : reg n39 a0 = bl35 := by
    rw [u39.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g38_2, show B + 0x21A0 + 0x84 = B + 0x21A0 + BitVec.ofNat 32 0x84 by sv_addr, w38_84]
  have keep_kk39 : SvKeepL B n0.mem n39.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := by rw [m39]; exact keep_kk38
  clear keep_kk38
  have w39_80 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp35 := by rw [m39]; exact w38_80
  have w39_84 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl35 := by rw [m39]; exact w38_84
  have w39_88 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m39]; exact w38_88
  have w39_8c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m39]; exact w38_8c
  have w39_284 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m39]; exact w38_284
  have w39_288 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m39]; exact w38_288
  have w39_420 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m39]; exact w38_420
  have w39_428 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m39]; exact w38_428
  have w39_42c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m39]; exact w38_42c
  have b39_98 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m39]; exact b38_98
  have b39_424 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m39]; exact b38_424
  have b39_425 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m39]; exact b38_425
  have b39_426 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m39]; exact b38_426
  have b39_427 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m39]; exact b38_427
  clear b38_427 b38_426 b38_425 b38_424 b38_98 w38_42c w38_428 w38_420 w38_288 w38_284 w38_8c w38_88 w38_84 w38_80 g38_24 g38_27 g38_26 g38_25 g38_23 g38_22 g38_21 g38_20 g38_19 g38_18 g38_10 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 rb38 s38 m38 u38 c38
  -- 0x316
  obtain ⟨n40, c40, u40⟩ := s39.block svL5316 E39.self svL5316_end
    ⟨trivial, trivial⟩
  have m40 : n40.mem = n39.mem := u40.mem
  have s40 : St n40.mem SV n40 0x31A (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
  have rb40 : ∀ q, reg n40 q = (runBlock svL5316 (n39.mem, reg n39)).2 q := fun q => by rw [u40.regs]
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
  have g40_8 : reg n40 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb40, runBlock_reg _ _ _ (8 : Fin 32) s39.zero (by decide), g39_8]
  have g40_9 : reg n40 (9 : Fin 32) = tbp := by
    rw [rb40, runBlock_reg _ _ _ (9 : Fin 32) s39.zero (by decide), g39_9]
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
  have g40_23 : reg n40 (23 : Fin 32) = sgp := by
    rw [rb40, runBlock_reg _ _ _ (23 : Fin 32) s39.zero (by decide), g39_23]
  have g40_24 : reg n40 (24 : Fin 32) = bp35 := by
    rw [rb40, runBlock_reg _ _ _ (24 : Fin 32) s39.zero (by decide), g39_24]
  have g40_25 : reg n40 (25 : Fin 32) = sgl := by
    rw [rb40, runBlock_reg _ _ _ (25 : Fin 32) s39.zero (by decide), g39_25]
  have g40_26 : reg n40 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
    rw [rb40, runBlock_reg _ _ _ (26 : Fin 32) s39.zero (by decide), g39_26]
  have g40_27 : reg n40 (27 : Fin 32) = tbl := by
    rw [rb40, runBlock_reg _ _ _ (27 : Fin 32) s39.zero (by decide), g39_27]
  have g40_10 : reg n40 a0 = (bl35) + BitVec.ofNat 32 0xFFFFFFBF := by
    rw [rb40, ← g39_10]; rfl
  have keep_kk40 : SvKeepL B n0.mem n40.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := by rw [m40]; exact keep_kk39
  clear keep_kk39
  have w40_80 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp35 := by rw [m40]; exact w39_80
  have w40_84 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl35 := by rw [m40]; exact w39_84
  have w40_88 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m40]; exact w39_88
  have w40_8c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m40]; exact w39_8c
  have w40_284 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m40]; exact w39_284
  have w40_288 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m40]; exact w39_288
  have w40_420 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m40]; exact w39_420
  have w40_428 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m40]; exact w39_428
  have w40_42c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m40]; exact w39_42c
  have b40_98 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m40]; exact b39_98
  have b40_424 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m40]; exact b39_424
  have b40_425 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m40]; exact b39_425
  have b40_426 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m40]; exact b39_426
  have b40_427 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m40]; exact b39_427
  clear b39_427 b39_426 b39_425 b39_424 b39_98 w39_42c w39_428 w39_420 w39_288 w39_284 w39_8c w39_88 w39_84 w39_80 g39_10 g39_27 g39_26 g39_25 g39_24 g39_23 g39_22 g39_21 g39_20 g39_19 g39_18 g39_9 g39_8 g39_4 g39_3 g39_2 V39 E39 fR39 t39 fr39 m39 s39 u39 d39
  by_cases hz_40 : bl35 = BitVec.ofNat 32 0x41
  rotate_left
  · -- 0x31A: branch, taken
    obtain ⟨n41, d41, u41⟩ := s40.taken E40.self 0x7A4 sv_at_31a
      (by decide) (by rw [g40_10, s40.zero]; exact br_bne_t (sub_lit_ne (c := 0x41) (by decide) hz_40))
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
    have g41_8 : reg n41 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u41.regs, g40_8]
    have g41_9 : reg n41 (9 : Fin 32) = tbp := by rw [u41.regs, g40_9]
    have g41_10 : reg n41 a0 = (bl35) + BitVec.ofNat 32 0xFFFFFFBF := by rw [u41.regs, g40_10]
    have g41_18 : reg n41 (18 : Fin 32) = out := by rw [u41.regs, g40_18]
    have g41_19 : reg n41 (19 : Fin 32) = bp := by rw [u41.regs, g40_19]
    have g41_20 : reg n41 (20 : Fin 32) = dg := by rw [u41.regs, g40_20]
    have g41_21 : reg n41 (21 : Fin 32) = rootp := by rw [u41.regs, g40_21]
    have g41_22 : reg n41 (22 : Fin 32) = ll := by rw [u41.regs, g40_22]
    have g41_23 : reg n41 (23 : Fin 32) = sgp := by rw [u41.regs, g40_23]
    have g41_24 : reg n41 (24 : Fin 32) = bp35 := by rw [u41.regs, g40_24]
    have g41_25 : reg n41 (25 : Fin 32) = sgl := by rw [u41.regs, g40_25]
    have g41_26 : reg n41 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u41.regs, g40_26]
    have g41_27 : reg n41 (27 : Fin 32) = tbl := by rw [u41.regs, g40_27]
    have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := by rw [m41]; exact keep_kk40
    clear keep_kk40
    have w41_80 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp35 := by rw [m41]; exact w40_80
    have w41_84 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl35 := by rw [m41]; exact w40_84
    have w41_88 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m41]; exact w40_88
    have w41_8c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m41]; exact w40_8c
    have w41_284 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m41]; exact w40_284
    have w41_288 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m41]; exact w40_288
    have w41_420 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m41]; exact w40_420
    have w41_428 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m41]; exact w40_428
    have w41_42c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m41]; exact w40_42c
    have b41_98 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m41]; exact b40_98
    have b41_424 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m41]; exact b40_424
    have b41_425 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m41]; exact b40_425
    have b41_426 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m41]; exact b40_426
    have b41_427 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m41]; exact b40_427
    clear b40_427 b40_426 b40_425 b40_424 b40_98 w40_42c w40_428 w40_420 w40_288 w40_284 w40_8c w40_88 w40_84 w40_80 g40_10 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_9 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 rb40 s40 m40 u40 c40
    exact .inl ⟨(fun ⟨tl2', h0', tl6', h1', op15', ol15', prp15', pu15', h2', ta15', h3', h4', h5', h6', tl35', h7', bp35', bl35', h8', h9', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr6] at h1'; cases h1'; rw [hr15] at h2'; cases h2'; rw [hta15] at h3'; cases h3'; rw [hr35] at h7'; cases h7'; rw [hr35b] at h8'; cases h8'; exact hz_40 h9'), sv_fail F E41 s41 t41 (fun x hx => (fR41 x hx).trans (fM x hx).symm) V41 hret g41_2 g41_18 hO g41_3 g41_4 (by rw [g41_8]; sv_code)⟩
  -- 0x31A: branch, not taken
  obtain ⟨n41, d41, u41⟩ := s40.notTaken E40.self 0x31E sv_at_31a
    (by decide) (by rw [g40_10, s40.zero]; exact br_bne_f (sub_lit_eq (c := 0x41) (by decide) hz_40))
  have s41 : St n41.mem SV n41 0x31E (reg n41) := ⟨u41.pc, rfl, fun _ => rfl⟩
  have m41 : n41.mem = n40.mem := u41.mem
  have fr41 : ∀ x, SvR B x → n41.mem x = n40.mem x := fun x _ => by rw [m41]
  have t41 : Steps n0 n41 := t40.trans (.single d41)
  have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
  have E41 : SvCode n41.mem := E40.fr F fr41
  have V41 : SvSaves B n41.mem v := V40.same m41
  have g41_2 : reg n41 sp = B + 0x21A0 := by rw [u41.regs, g40_2]
  have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u41.regs, g40_3]
  have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u41.regs, g40_4]
  have g41_8 : reg n41 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u41.regs, g40_8]
  have g41_9 : reg n41 (9 : Fin 32) = tbp := by rw [u41.regs, g40_9]
  have g41_10 : reg n41 a0 = (bl35) + BitVec.ofNat 32 0xFFFFFFBF := by rw [u41.regs, g40_10]
  have g41_18 : reg n41 (18 : Fin 32) = out := by rw [u41.regs, g40_18]
  have g41_19 : reg n41 (19 : Fin 32) = bp := by rw [u41.regs, g40_19]
  have g41_20 : reg n41 (20 : Fin 32) = dg := by rw [u41.regs, g40_20]
  have g41_21 : reg n41 (21 : Fin 32) = rootp := by rw [u41.regs, g40_21]
  have g41_22 : reg n41 (22 : Fin 32) = ll := by rw [u41.regs, g40_22]
  have g41_23 : reg n41 (23 : Fin 32) = sgp := by rw [u41.regs, g40_23]
  have g41_24 : reg n41 (24 : Fin 32) = bp35 := by rw [u41.regs, g40_24]
  have g41_25 : reg n41 (25 : Fin 32) = sgl := by rw [u41.regs, g40_25]
  have g41_26 : reg n41 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u41.regs, g40_26]
  have g41_27 : reg n41 (27 : Fin 32) = tbl := by rw [u41.regs, g40_27]
  have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := by rw [m41]; exact keep_kk40
  clear keep_kk40
  have w41_80 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp35 := by rw [m41]; exact w40_80
  have w41_84 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl35 := by rw [m41]; exact w40_84
  have w41_88 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m41]; exact w40_88
  have w41_8c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m41]; exact w40_8c
  have w41_284 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m41]; exact w40_284
  have w41_288 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m41]; exact w40_288
  have w41_420 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m41]; exact w40_420
  have w41_428 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m41]; exact w40_428
  have w41_42c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m41]; exact w40_42c
  have b41_98 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m41]; exact b40_98
  have b41_424 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m41]; exact b40_424
  have b41_425 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m41]; exact b40_425
  have b41_426 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m41]; exact b40_426
  have b41_427 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m41]; exact b40_427
  clear b40_427 b40_426 b40_425 b40_424 b40_98 w40_42c w40_428 w40_420 w40_288 w40_284 w40_8c w40_88 w40_84 w40_80 g40_10 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_9 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 rb40 s40 m40 u40 c40
  -- 0x31E: lw
  obtain ⟨n42, d42, u42⟩ := s41.lw E41.self sv_at_31e (off' := 0x322) (by decide)
    (by rw [g41_2, show B + 0x21A0 + 0x42C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s42 : St n42.mem SV n42 0x322 (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
  have m42 : n42.mem = n41.mem := u42.mem
  have fr42 : ∀ x, SvR B x → n42.mem x = n41.mem x := fun x _ => by rw [m42]
  have t42 : Steps n0 n42 := t41.trans (.single d42)
  have fR42 : ∀ x, SvR B x → n42.mem x = M0 x := fun x hx => (fr42 x hx).trans (fR41 x hx)
  have E42 : SvCode n42.mem := E41.fr F fr42
  have V42 : SvSaves B n42.mem v := V41.same m42
  have g42_2 : reg n42 sp = B + 0x21A0 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_2]
  have g42_3 : reg n42 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u42.regs, upd_ne (by decide) (by decide), g41_3]
  have g42_4 : reg n42 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u42.regs, upd_ne (by decide) (by decide), g41_4]
  have g42_8 : reg n42 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_8]
  have g42_9 : reg n42 (9 : Fin 32) = tbp := by rw [u42.regs, upd_ne (by decide) (by decide), g41_9]
  have g42_18 : reg n42 (18 : Fin 32) = out := by rw [u42.regs, upd_ne (by decide) (by decide), g41_18]
  have g42_19 : reg n42 (19 : Fin 32) = bp := by rw [u42.regs, upd_ne (by decide) (by decide), g41_19]
  have g42_20 : reg n42 (20 : Fin 32) = dg := by rw [u42.regs, upd_ne (by decide) (by decide), g41_20]
  have g42_21 : reg n42 (21 : Fin 32) = rootp := by rw [u42.regs, upd_ne (by decide) (by decide), g41_21]
  have g42_22 : reg n42 (22 : Fin 32) = ll := by rw [u42.regs, upd_ne (by decide) (by decide), g41_22]
  have g42_23 : reg n42 (23 : Fin 32) = sgp := by rw [u42.regs, upd_ne (by decide) (by decide), g41_23]
  have g42_24 : reg n42 (24 : Fin 32) = bp35 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_24]
  have g42_25 : reg n42 (25 : Fin 32) = sgl := by rw [u42.regs, upd_ne (by decide) (by decide), g41_25]
  have g42_26 : reg n42 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_26]
  have g42_27 : reg n42 (27 : Fin 32) = tbl := by rw [u42.regs, upd_ne (by decide) (by decide), g41_27]
  have g42_10 : reg n42 a0 = ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) := by
    rw [u42.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g41_2, show B + 0x21A0 + 0x42C = B + 0x21A0 + BitVec.ofNat 32 0x42C by sv_addr, w41_42c]
  have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := by rw [m42]; exact keep_kk41
  clear keep_kk41
  have w42_80 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp35 := by rw [m42]; exact w41_80
  have w42_84 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl35 := by rw [m42]; exact w41_84
  have w42_88 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m42]; exact w41_88
  have w42_8c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m42]; exact w41_8c
  have w42_284 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m42]; exact w41_284
  have w42_288 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m42]; exact w41_288
  have w42_420 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m42]; exact w41_420
  have w42_428 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m42]; exact w41_428
  have w42_42c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m42]; exact w41_42c
  have b42_98 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m42]; exact b41_98
  have b42_424 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m42]; exact b41_424
  have b42_425 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m42]; exact b41_425
  have b42_426 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m42]; exact b41_426
  have b42_427 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m42]; exact b41_427
  clear b41_427 b41_426 b41_425 b41_424 b41_98 w41_42c w41_428 w41_420 w41_288 w41_284 w41_8c w41_88 w41_84 w41_80 g41_27 g41_26 g41_25 g41_24 g41_23 g41_22 g41_21 g41_20 g41_19 g41_18 g41_10 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 fr41 m41 s41 u41 d41
  by_cases hz_42 : ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) = 0
  rotate_left
  · -- 0x322: branch, taken
    obtain ⟨n43, d43, u43⟩ := s42.taken E42.self 0x14C sv_at_322
      (by decide) (by rw [g42_10, s42.zero]; exact br_bne_t hz_42)
    have s43 : St n43.mem SV n43 0x14C (reg n43) := ⟨u43.pc, rfl, fun _ => rfl⟩
    have m43 : n43.mem = n42.mem := u43.mem
    have fr43 : ∀ x, SvR B x → n43.mem x = n42.mem x := fun x _ => by rw [m43]
    have t43 : Steps n0 n43 := t42.trans (.single d43)
    have fR43 : ∀ x, SvR B x → n43.mem x = M0 x := fun x hx => (fr43 x hx).trans (fR42 x hx)
    have E43 : SvCode n43.mem := E42.fr F fr43
    have V43 : SvSaves B n43.mem v := V42.same m43
    have g43_2 : reg n43 sp = B + 0x21A0 := by rw [u43.regs, g42_2]
    have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u43.regs, g42_3]
    have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u43.regs, g42_4]
    have g43_8 : reg n43 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u43.regs, g42_8]
    have g43_9 : reg n43 (9 : Fin 32) = tbp := by rw [u43.regs, g42_9]
    have g43_10 : reg n43 a0 = ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [u43.regs, g42_10]
    have g43_18 : reg n43 (18 : Fin 32) = out := by rw [u43.regs, g42_18]
    have g43_19 : reg n43 (19 : Fin 32) = bp := by rw [u43.regs, g42_19]
    have g43_20 : reg n43 (20 : Fin 32) = dg := by rw [u43.regs, g42_20]
    have g43_21 : reg n43 (21 : Fin 32) = rootp := by rw [u43.regs, g42_21]
    have g43_22 : reg n43 (22 : Fin 32) = ll := by rw [u43.regs, g42_22]
    have g43_23 : reg n43 (23 : Fin 32) = sgp := by rw [u43.regs, g42_23]
    have g43_24 : reg n43 (24 : Fin 32) = bp35 := by rw [u43.regs, g42_24]
    have g43_25 : reg n43 (25 : Fin 32) = sgl := by rw [u43.regs, g42_25]
    have g43_26 : reg n43 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u43.regs, g42_26]
    have g43_27 : reg n43 (27 : Fin 32) = tbl := by rw [u43.regs, g42_27]
    have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := by rw [m43]; exact keep_kk42
    clear keep_kk42
    have w43_80 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp35 := by rw [m43]; exact w42_80
    have w43_84 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl35 := by rw [m43]; exact w42_84
    have w43_88 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m43]; exact w42_88
    have w43_8c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m43]; exact w42_8c
    have w43_284 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m43]; exact w42_284
    have w43_288 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m43]; exact w42_288
    have w43_420 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m43]; exact w42_420
    have w43_428 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m43]; exact w42_428
    have w43_42c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m43]; exact w42_42c
    have b43_98 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m43]; exact b42_98
    have b43_424 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m43]; exact b42_424
    have b43_425 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m43]; exact b42_425
    have b43_426 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m43]; exact b42_426
    have b43_427 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m43]; exact b42_427
    clear b42_427 b42_426 b42_425 b42_424 b42_98 w42_42c w42_428 w42_420 w42_288 w42_284 w42_8c w42_88 w42_84 w42_80 g42_10 g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 m42 s42 u42 d42
    -- 0x14C
    obtain ⟨n44, c44, u44⟩ := s43.block svL514c E43.self svL514c_end
      ⟨trivial, trivial⟩
    have m44 : n44.mem = n43.mem := u44.mem
    have s44 : St n44.mem SV n44 0x14E (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
    have rb44 : ∀ q, reg n44 q = (runBlock svL514c (n43.mem, reg n43)).2 q := fun q => by rw [u44.regs]
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
    have g44_9 : reg n44 (9 : Fin 32) = tbp := by
      rw [rb44, runBlock_reg _ _ _ (9 : Fin 32) s43.zero (by decide), g43_9]
    have g44_10 : reg n44 a0 = ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) := by
      rw [rb44, runBlock_reg _ _ _ a0 s43.zero (by decide), g43_10]
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
    have g44_23 : reg n44 (23 : Fin 32) = sgp := by
      rw [rb44, runBlock_reg _ _ _ (23 : Fin 32) s43.zero (by decide), g43_23]
    have g44_24 : reg n44 (24 : Fin 32) = bp35 := by
      rw [rb44, runBlock_reg _ _ _ (24 : Fin 32) s43.zero (by decide), g43_24]
    have g44_25 : reg n44 (25 : Fin 32) = sgl := by
      rw [rb44, runBlock_reg _ _ _ (25 : Fin 32) s43.zero (by decide), g43_25]
    have g44_26 : reg n44 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by
      rw [rb44, runBlock_reg _ _ _ (26 : Fin 32) s43.zero (by decide), g43_26]
    have g44_27 : reg n44 (27 : Fin 32) = tbl := by
      rw [rb44, runBlock_reg _ _ _ (27 : Fin 32) s43.zero (by decide), g43_27]
    have g44_8 : reg n44 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb44]; simp +decide only [runBlock, BInstr.run, svL514c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk44 : SvKeepL B n0.mem n44.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := by rw [m44]; exact keep_kk43
    clear keep_kk43
    have w44_80 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp35 := by rw [m44]; exact w43_80
    have w44_84 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl35 := by rw [m44]; exact w43_84
    have w44_88 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m44]; exact w43_88
    have w44_8c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m44]; exact w43_8c
    have w44_284 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m44]; exact w43_284
    have w44_288 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m44]; exact w43_288
    have w44_420 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m44]; exact w43_420
    have w44_428 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m44]; exact w43_428
    have w44_42c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m44]; exact w43_42c
    have b44_98 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m44]; exact b43_98
    have b44_424 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m44]; exact b43_424
    have b44_425 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m44]; exact b43_425
    have b44_426 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m44]; exact b43_426
    have b44_427 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m44]; exact b43_427
    clear b43_427 b43_426 b43_425 b43_424 b43_98 w43_42c w43_428 w43_420 w43_288 w43_284 w43_8c w43_88 w43_84 w43_80 g43_27 g43_26 g43_25 g43_24 g43_23 g43_22 g43_21 g43_20 g43_19 g43_18 g43_10 g43_9 g43_8 g43_4 g43_3 g43_2 V43 E43 fR43 t43 fr43 m43 s43 u43 d43
    -- 0x14E: j
    obtain ⟨n45, d45, u45⟩ := s44.jump E44.self sv_at_14e (off' := 0x7A4) (by decide)
      (by rw [s44.pc]; decide)
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
    have g45_8 : reg n45 (8 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u45.regs, g44_8]
    have g45_9 : reg n45 (9 : Fin 32) = tbp := by rw [u45.regs, g44_9]
    have g45_10 : reg n45 a0 = ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [u45.regs, g44_10]
    have g45_18 : reg n45 (18 : Fin 32) = out := by rw [u45.regs, g44_18]
    have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [u45.regs, g44_19]
    have g45_20 : reg n45 (20 : Fin 32) = dg := by rw [u45.regs, g44_20]
    have g45_21 : reg n45 (21 : Fin 32) = rootp := by rw [u45.regs, g44_21]
    have g45_22 : reg n45 (22 : Fin 32) = ll := by rw [u45.regs, g44_22]
    have g45_23 : reg n45 (23 : Fin 32) = sgp := by rw [u45.regs, g44_23]
    have g45_24 : reg n45 (24 : Fin 32) = bp35 := by rw [u45.regs, g44_24]
    have g45_25 : reg n45 (25 : Fin 32) = sgl := by rw [u45.regs, g44_25]
    have g45_26 : reg n45 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u45.regs, g44_26]
    have g45_27 : reg n45 (27 : Fin 32) = tbl := by rw [u45.regs, g44_27]
    have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := by rw [m45]; exact keep_kk44
    clear keep_kk44
    have w45_80 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp35 := by rw [m45]; exact w44_80
    have w45_84 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl35 := by rw [m45]; exact w44_84
    have w45_88 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m45]; exact w44_88
    have w45_8c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m45]; exact w44_8c
    have w45_284 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m45]; exact w44_284
    have w45_288 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m45]; exact w44_288
    have w45_420 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m45]; exact w44_420
    have w45_428 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m45]; exact w44_428
    have w45_42c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m45]; exact w44_42c
    have b45_98 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m45]; exact b44_98
    have b45_424 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m45]; exact b44_424
    have b45_425 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m45]; exact b44_425
    have b45_426 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m45]; exact b44_426
    have b45_427 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m45]; exact b44_427
    clear b44_427 b44_426 b44_425 b44_424 b44_98 w44_42c w44_428 w44_420 w44_288 w44_284 w44_8c w44_88 w44_84 w44_80 g44_8 g44_27 g44_26 g44_25 g44_24 g44_23 g44_22 g44_21 g44_20 g44_19 g44_18 g44_10 g44_9 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 rb44 s44 m44 u44 c44
    exact .inl ⟨(fun ⟨tl2', h0', tl6', h1', op15', ol15', prp15', pu15', h2', ta15', h3', h4', h5', h6', tl35', h7', bp35', bl35', h8', h9', h10', _⟩ => by rw [hr2] at h0'; cases h0'; rw [hr6] at h1'; cases h1'; rw [hr15] at h2'; cases h2'; rw [hta15] at h3'; cases h3'; rw [hr35] at h7'; cases h7'; rw [hr35b] at h8'; cases h8'; exact hz_42 h10'), sv_fail F E45 s45 t45 (fun x hx => (fR45 x hx).trans (fM x hx).symm) V45 hret g45_2 g45_18 hO g45_3 g45_4 (by rw [g45_8]; sv_code)⟩
  -- 0x322: branch, not taken
  obtain ⟨n43, d43, u43⟩ := s42.notTaken E42.self 0x326 sv_at_322
    (by decide) (by rw [g42_10, s42.zero]; exact br_bne_f hz_42)
  have s43 : St n43.mem SV n43 0x326 (reg n43) := ⟨u43.pc, rfl, fun _ => rfl⟩
  have m43 : n43.mem = n42.mem := u43.mem
  have fr43 : ∀ x, SvR B x → n43.mem x = n42.mem x := fun x _ => by rw [m43]
  have t43 : Steps n0 n43 := t42.trans (.single d43)
  have fR43 : ∀ x, SvR B x → n43.mem x = M0 x := fun x hx => (fr43 x hx).trans (fR42 x hx)
  have E43 : SvCode n43.mem := E42.fr F fr43
  have V43 : SvSaves B n43.mem v := V42.same m43
  have g43_2 : reg n43 sp = B + 0x21A0 := by rw [u43.regs, g42_2]
  have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u43.regs, g42_3]
  have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u43.regs, g42_4]
  have g43_8 : reg n43 (8 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u43.regs, g42_8]
  have g43_9 : reg n43 (9 : Fin 32) = tbp := by rw [u43.regs, g42_9]
  have g43_10 : reg n43 a0 = ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [u43.regs, g42_10]
  have g43_18 : reg n43 (18 : Fin 32) = out := by rw [u43.regs, g42_18]
  have g43_19 : reg n43 (19 : Fin 32) = bp := by rw [u43.regs, g42_19]
  have g43_20 : reg n43 (20 : Fin 32) = dg := by rw [u43.regs, g42_20]
  have g43_21 : reg n43 (21 : Fin 32) = rootp := by rw [u43.regs, g42_21]
  have g43_22 : reg n43 (22 : Fin 32) = ll := by rw [u43.regs, g42_22]
  have g43_23 : reg n43 (23 : Fin 32) = sgp := by rw [u43.regs, g42_23]
  have g43_24 : reg n43 (24 : Fin 32) = bp35 := by rw [u43.regs, g42_24]
  have g43_25 : reg n43 (25 : Fin 32) = sgl := by rw [u43.regs, g42_25]
  have g43_26 : reg n43 (26 : Fin 32) = BitVec.ofNat 32 ol15 := by rw [u43.regs, g42_26]
  have g43_27 : reg n43 (27 : Fin 32) = tbl := by rw [u43.regs, g42_27]
  have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x80, 0x11), (0x284, 0x8), (0x80, 0x10), (0x284, 0x8), (0x425, 0xB), (0x420, 0x4), (0x424, 0x1), (0x80, 0x1C), (0x428, 0x8), (0x80, 0x8), (0x428, 0x8)] := by rw [m43]; exact keep_kk42
  clear keep_kk42
  have w43_80 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = bp35 := by rw [m43]; exact w42_80
  have w43_84 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = bl35 := by rw [m43]; exact w42_84
  have w43_88 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = prp15 + BitVec.ofNat 32 pu15.header := by rw [m43]; exact w42_88
  have w43_8c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 pu15.len := by rw [m43]; exact w42_8c
  have w43_284 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x284) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m43]; exact w42_284
  have w43_288 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x288) = ((rl) - BitVec.ofNat 32 (tl2.header + tl2.len)) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m43]; exact w42_288
  have w43_420 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = ((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header := by rw [m43]; exact w42_420
  have w43_428 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = ((((rp) + BitVec.ofNat 32 (tl2.header + tl2.len)) + BitVec.ofNat 32 tl6.header) + BitVec.ofNat 32 (ta15.header + ta15.len)) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m43]; exact w42_428
  have w43_42c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = ((BitVec.ofNat 32 (tl6.len)) - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m43]; exact w42_42c
  have b43_98 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = BitVec.ofNat 8 pu15.tag := by rw [m43]; exact b42_98
  have b43_424 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = (BitVec.ofNat 32 tl6.len).extractLsb' 0 8 := by rw [m43]; exact b42_424
  have b43_425 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x425) = (BitVec.ofNat 32 tl6.len).extractLsb' 8 8 := by rw [m43]; exact b42_425
  have b43_426 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x426) = (BitVec.ofNat 32 tl6.len).extractLsb' 16 8 := by rw [m43]; exact b42_426
  have b43_427 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x427) = (BitVec.ofNat 32 tl6.len).extractLsb' 24 8 := by rw [m43]; exact b42_427
  clear b42_427 b42_426 b42_425 b42_424 b42_98 w42_42c w42_428 w42_420 w42_288 w42_284 w42_8c w42_88 w42_84 w42_80 g42_10 g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 m42 s42 u42 d42
  exact .inr ⟨tl2, hr2, tl6, hr6, op15, ol15, prp15, pu15, hr15, ta15, hta15, hz_23, hz_27, hz_30, tl35, hr35, bp35, bl35, hr35b, hz_40, hz_42, n43, t43, s43, E43, V43, fR43, g43_2, g43_3, g43_4, g43_8, g43_9, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, w43_284, w43_288, keep_kk43.mono (by decide)⟩

end C3.RV32.Sv
