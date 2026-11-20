import C3BootProofs.Proofs.SvP256

/-!
# `sigstore::verify`: the leaf's key and the extensions' start

From 0x424 to the extensions loop at 0x4EA: the key is tag 4 and a point on P-256, the tbsCertificate ends with `[3] EXPLICIT` extensions that hold one `SEQUENCE`, and the five identity-policy slots and the two flags start at zero.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svL6428 : List BInstr :=
  [.aluImm .add a1 x0 0x4, .aluImm .add (20 : Fin 32) x0 0xE]
theorem svL6428_end : blockEnd sigstoreVerifyCode 0x428 svL6428 = some 0x42C := by
  simp only [svL6428]
  rw [blockEnd, sv_at_428]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_42a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL6430 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .alu .add a1 x0 (21 : Fin 32)]
theorem svL6430_end : blockEnd sigstoreVerifyCode 0x430 svL6430 = some 0x43A := by
  simp only [svL6430]
  rw [blockEnd, sv_at_430]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_434]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_438]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL644a : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .aluImm .add a1 sp 0x178, .aluImm .add a2 x0 0xA3]
theorem svL644a_end : blockEnd sigstoreVerifyCode 0x44A svL644a = some 0x458 := by
  simp only [svL644a]
  rw [blockEnd, sv_at_44a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_44e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_452]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_454]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL646c : List BInstr :=
  [.aluImm .add (20 : Fin 32) x0 0x15]
theorem svL646c_end : blockEnd sigstoreVerifyCode 0x46C svL646c = some 0x46E := by
  simp only [svL646c]
  rw [blockEnd, sv_at_46c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL61c0 : List BInstr :=
  [.aluImm .add (20 : Fin 32) x0 0x1]
theorem svL61c0_end : blockEnd sigstoreVerifyCode 0x1C0 svL61c0 = some 0x1C2 := by
  simp only [svL61c0]
  rw [blockEnd, sv_at_1c0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL647e : List BInstr :=
  [.lui a2 0x1000, .aluImm .add a2 a2 0x320, .alu .add a2 a2 sp]
theorem svL647e_end : blockEnd sigstoreVerifyCode 0x47E svL647e = some 0x486 := by
  simp only [svL647e]
  rw [blockEnd, sv_at_47e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_480]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_484]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL648c : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x320, .alu .add (8 : Fin 32) sp a0]
theorem svL648c_end : blockEnd sigstoreVerifyCode 0x48C svL648c = some 0x496 := by
  simp only [svL648c]
  rw [blockEnd, sv_at_48c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_48e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_492]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL6498 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .lui a1 0x1000, .aluImm .add a1 a1 0x320, .alu .add a1 a1 sp, .aluImm .add a2 x0 0x30]
theorem svL6498_end : blockEnd sigstoreVerifyCode 0x498 svL6498 = some 0x4AC := by
  simp only [svL6498]
  rw [blockEnd, sv_at_498]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_49c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_4a0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_4a2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_4a6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_4a8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL64d0 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .aluImm .add a1 x0 0x5]
theorem svL64d0_end : blockEnd sigstoreVerifyCode 0x4D0 svL64d0 = some 0x4DA := by
  simp only [svL64d0]
  rw [blockEnd, sv_at_4d0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_4d4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_4d8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svL64e0 : List BInstr :=
  [.aluImm .add a0 a0 0x8, .aluImm .add a1 a1 0xFFFFFFFF]
theorem svL64e0_end : blockEnd sigstoreVerifyCode 0x4E0 svL64e0 = some 0x4E4 := by
  simp only [svL64e0]
  rw [blockEnd, sv_at_4e0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_4e2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_l6 {B out bp rootp dg lp ll rp rl kp x8 x9 x22 x23 x24 x25 : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x424 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = x8)
    (g0_9 : reg n0 (9 : Fin 32) = x9)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = kp)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = x24)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = ll)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_180 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp)
    (w0_184 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl)
    (tb_in : SvIn B (rp) (rl).toNat)
    (kb_in : SvIn B kp 0x41)
    (D0 : P2Data M0) :
    (¬ ((M0 kp = BitVec.ofNat 8 4) ∧ (GsOk M0 kp) ∧ ∃ tl9, derOptRes 0xA3 (memBytes M0 (rp) (rl).toNat) = some (.ok tl9) ∧ ((rl) - BitVec.ofNat 32 (tl9.header + tl9.len) = 0) ∧ ∃ tl25, derElement 0x30 (memBytes M0 ((rp) + BitVec.ofNat 32 tl9.header) (BitVec.ofNat 32 tl9.len).toNat) = .ok tl25 ∧ ((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) = 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    ((M0 kp = BitVec.ofNat 8 4) ∧
    (GsOk M0 kp) ∧
    ∃ tl9, derOptRes 0xA3 (memBytes M0 (rp) (rl).toNat) = some (.ok tl9) ∧
    ((rl) - BitVec.ofNat 32 (tl9.header + tl9.len) = 0) ∧
    ∃ tl25, derElement 0x30 (memBytes M0 ((rp) + BitVec.ofNat 32 tl9.header) (BitVec.ofNat 32 tl9.len).toNat) = .ok tl25 ∧
    ((BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) = 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x4EA (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 ∧
        reg n' (9 : Fin 32) = x9 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = BitVec.ofNat 32 0x15 ∧
        reg n' (21 : Fin 32) = kp ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = x24 ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = ll ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 32 0x0) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x424: lbu from the bundle
  obtain ⟨n1, d1, u1⟩ := s0.lbu E0.self sv_at_424 (off' := 0x428) (by decide)
  have s1 : St n1.mem SV n1 0x428 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_4]
  have g1_8 : reg n1 (8 : Fin 32) = x8 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_8]
  have g1_9 : reg n1 (9 : Fin 32) = x9 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_9]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, upd_ne (by decide) (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_19]
  have g1_21 : reg n1 (21 : Fin 32) = kp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = x22 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = x23 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = x24 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = x25 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = ll := by rw [u1.regs, upd_ne (by decide) (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_27]
  have g1_10 : reg n1 a0 = (M0 (kp)).zeroExtend 32 := by
    rw [u1.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g0_21, show (kp) + 0x0 = kp from BitVec.add_zero _, fR0 _ (kb_in.r0 (by omega))]
  have w1_180 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp := by rw [m1]; exact w0_180
  have w1_184 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl := by rw [m1]; exact w0_184
  -- 0x428
  obtain ⟨n2, c2, u2⟩ := s1.block svL6428 E1.self svL6428_end
    ⟨trivial, trivial, trivial⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have s2 : St n2.mem SV n2 0x42C (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have rb2 : ∀ q, reg n2 q = (runBlock svL6428 (n1.mem, reg n1)).2 q := fun q => by rw [u2.regs]
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans c2
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by
    rw [rb2, runBlock_reg _ _ _ sp s1.zero (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb2, runBlock_reg _ _ _ (3 : Fin 32) s1.zero (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb2, runBlock_reg _ _ _ (4 : Fin 32) s1.zero (by decide), g1_4]
  have g2_8 : reg n2 (8 : Fin 32) = x8 := by
    rw [rb2, runBlock_reg _ _ _ (8 : Fin 32) s1.zero (by decide), g1_8]
  have g2_9 : reg n2 (9 : Fin 32) = x9 := by
    rw [rb2, runBlock_reg _ _ _ (9 : Fin 32) s1.zero (by decide), g1_9]
  have g2_10 : reg n2 a0 = (M0 (kp)).zeroExtend 32 := by
    rw [rb2, runBlock_reg _ _ _ a0 s1.zero (by decide), g1_10]
  have g2_18 : reg n2 (18 : Fin 32) = out := by
    rw [rb2, runBlock_reg _ _ _ (18 : Fin 32) s1.zero (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by
    rw [rb2, runBlock_reg _ _ _ (19 : Fin 32) s1.zero (by decide), g1_19]
  have g2_21 : reg n2 (21 : Fin 32) = kp := by
    rw [rb2, runBlock_reg _ _ _ (21 : Fin 32) s1.zero (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = x22 := by
    rw [rb2, runBlock_reg _ _ _ (22 : Fin 32) s1.zero (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = x23 := by
    rw [rb2, runBlock_reg _ _ _ (23 : Fin 32) s1.zero (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = x24 := by
    rw [rb2, runBlock_reg _ _ _ (24 : Fin 32) s1.zero (by decide), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = x25 := by
    rw [rb2, runBlock_reg _ _ _ (25 : Fin 32) s1.zero (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = ll := by
    rw [rb2, runBlock_reg _ _ _ (26 : Fin 32) s1.zero (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb2, runBlock_reg _ _ _ (27 : Fin 32) s1.zero (by decide), g1_27]
  have g2_11 : reg n2 a1 = BitVec.ofNat 32 0x4 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, svL6428, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_8, g1_9, g1_10, g1_18, g1_19, g1_21, g1_22, g1_23, g1_24, g1_25, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g2_20 : reg n2 (20 : Fin 32) = BitVec.ofNat 32 0xE := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, svL6428, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_8, g1_9, g1_10, g1_18, g1_19, g1_21, g1_22, g1_23, g1_24, g1_25, g1_26, g1_27, s1.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w2_180 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp := by rw [m2]; exact w1_180
  have w2_184 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl := by rw [m2]; exact w1_184
  clear w1_184 w1_180 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_19 g1_18 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  by_cases hz_2 : M0 kp = BitVec.ofNat 8 4
  rotate_left
  · -- 0x42C: branch, taken
    obtain ⟨n3, d3, u3⟩ := s2.taken E2.self 0x966 sv_at_42c
      (by decide) (by rw [g2_10, g2_11]; exact br_bne_byte_t (by decide) hz_2)
    have s3 : St n3.mem SV n3 0x966 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = n2.mem := u3.mem
    have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
    have t3 : Steps n0 n3 := t2.trans (.single d3)
    have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
    have E3 : SvCode n3.mem := E2.fr F fr3
    have V3 : SvSaves B n3.mem v := V2.same m3
    have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, g2_2]
    have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, g2_3]
    have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, g2_4]
    have g3_8 : reg n3 (8 : Fin 32) = x8 := by rw [u3.regs, g2_8]
    have g3_9 : reg n3 (9 : Fin 32) = x9 := by rw [u3.regs, g2_9]
    have g3_10 : reg n3 a0 = (M0 (kp)).zeroExtend 32 := by rw [u3.regs, g2_10]
    have g3_11 : reg n3 a1 = BitVec.ofNat 32 0x4 := by rw [u3.regs, g2_11]
    have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, g2_18]
    have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, g2_19]
    have g3_20 : reg n3 (20 : Fin 32) = BitVec.ofNat 32 0xE := by rw [u3.regs, g2_20]
    have g3_21 : reg n3 (21 : Fin 32) = kp := by rw [u3.regs, g2_21]
    have g3_22 : reg n3 (22 : Fin 32) = x22 := by rw [u3.regs, g2_22]
    have g3_23 : reg n3 (23 : Fin 32) = x23 := by rw [u3.regs, g2_23]
    have g3_24 : reg n3 (24 : Fin 32) = x24 := by rw [u3.regs, g2_24]
    have g3_25 : reg n3 (25 : Fin 32) = x25 := by rw [u3.regs, g2_25]
    have g3_26 : reg n3 (26 : Fin 32) = ll := by rw [u3.regs, g2_26]
    have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u3.regs, g2_27]
    have w3_180 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp := by rw [m3]; exact w2_180
    have w3_184 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl := by rw [m3]; exact w2_184
    clear w2_184 w2_180 g2_20 g2_11 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_19 g2_18 g2_10 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 rb2 s2 m2 u2 c2
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hz_2 h0'), sv_fail F E3 s3 t3 (fun x hx => (fR3 x hx).trans (fM x hx).symm) V3 hret g3_2 g3_18 hO g3_3 g3_4⟩
  -- 0x42C: branch, not taken
  obtain ⟨n3, d3, u3⟩ := s2.notTaken E2.self 0x430 sv_at_42c
    (by decide) (by rw [g2_10, g2_11]; exact br_bne_byte_f (by decide) hz_2)
  have s3 : St n3.mem SV n3 0x430 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = x8 := by rw [u3.regs, g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = x9 := by rw [u3.regs, g2_9]
  have g3_10 : reg n3 a0 = (M0 (kp)).zeroExtend 32 := by rw [u3.regs, g2_10]
  have g3_11 : reg n3 a1 = BitVec.ofNat 32 0x4 := by rw [u3.regs, g2_11]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = BitVec.ofNat 32 0xE := by rw [u3.regs, g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = kp := by rw [u3.regs, g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = x22 := by rw [u3.regs, g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = x23 := by rw [u3.regs, g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = x24 := by rw [u3.regs, g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = x25 := by rw [u3.regs, g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = ll := by rw [u3.regs, g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u3.regs, g2_27]
  have w3_180 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp := by rw [m3]; exact w2_180
  have w3_184 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl := by rw [m3]; exact w2_184
  clear w2_184 w2_180 g2_20 g2_11 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_19 g2_18 g2_10 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 rb2 s2 m2 u2 c2
  -- 0x430
  obtain ⟨n4, c4, u4⟩ := s3.block svL6430 E3.self svL6430_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem SV n4 0x43A (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock svL6430 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
  have g4_8 : reg n4 (8 : Fin 32) = x8 := by
    rw [rb4, runBlock_reg _ _ _ (8 : Fin 32) s3.zero (by decide), g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = x9 := by
    rw [rb4, runBlock_reg _ _ _ (9 : Fin 32) s3.zero (by decide), g3_9]
  have g4_18 : reg n4 (18 : Fin 32) = out := by
    rw [rb4, runBlock_reg _ _ _ (18 : Fin 32) s3.zero (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by
    rw [rb4, runBlock_reg _ _ _ (19 : Fin 32) s3.zero (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = BitVec.ofNat 32 0xE := by
    rw [rb4, runBlock_reg _ _ _ (20 : Fin 32) s3.zero (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = kp := by
    rw [rb4, runBlock_reg _ _ _ (21 : Fin 32) s3.zero (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = x22 := by
    rw [rb4, runBlock_reg _ _ _ (22 : Fin 32) s3.zero (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = x23 := by
    rw [rb4, runBlock_reg _ _ _ (23 : Fin 32) s3.zero (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = x24 := by
    rw [rb4, runBlock_reg _ _ _ (24 : Fin 32) s3.zero (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = x25 := by
    rw [rb4, runBlock_reg _ _ _ (25 : Fin 32) s3.zero (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = ll := by
    rw [rb4, runBlock_reg _ _ _ (26 : Fin 32) s3.zero (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb4, runBlock_reg _ _ _ (27 : Fin 32) s3.zero (by decide), g3_27]
  have g4_10 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svL6430, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_8, g3_9, g3_10, g3_11, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g4_11 : reg n4 a1 = kp := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svL6430, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_8, g3_9, g3_10, g3_11, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w4_180 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp := by rw [m4]; exact w3_180
  have w4_184 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl := by rw [m4]; exact w3_184
  clear w3_184 w3_180 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_11 g3_10 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x43A: sv_gsF
  obtain ⟨n5, c5, s5, sp5, rk5, K5, Ok5, Er5, fr5⟩ := sv_gsF (oc := 0xA20)
    F E4 (P2Data.sv F D0 fR4) s4 sv_at_43a sv_at_43e (by decide) (by decide) g4_2
    g4_10 g4_11 (by decide) (by decide) kb_in
  have t5 : Steps n0 n5 := t4.trans c5
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.keepL K5 (by decide)
  rw [gsOk_congr (sv_pt fR4 kb_in)] at Ok5 Er5
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk5 (3 : Fin 32) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk5 (4 : Fin 32) (by decide), g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = x8 := by rw [rk5 (8 : Fin 32) (by decide), g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = x9 := by rw [rk5 (9 : Fin 32) (by decide), g4_9]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [rk5 (18 : Fin 32) (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [rk5 (19 : Fin 32) (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = BitVec.ofNat 32 0xE := by rw [rk5 (20 : Fin 32) (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = kp := by rw [rk5 (21 : Fin 32) (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [rk5 (22 : Fin 32) (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [rk5 (23 : Fin 32) (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = x24 := by rw [rk5 (24 : Fin 32) (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [rk5 (25 : Fin 32) (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = ll := by rw [rk5 (26 : Fin 32) (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk5 (27 : Fin 32) (by decide), g4_27]
  have g5_2 : reg n5 sp = B + 0x21A0 := sp5
  by_cases hz_5 : GsOk M0 kp
  rotate_left
  · have y0_5 := Er5 hz_5
    have w5_180 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp := (K5.w32 (by decide) (by decide)).trans w4_180
    have w5_184 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl := (K5.w32 (by decide) (by decide)).trans w4_184
    have w5_a20 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 1 := y0_5
    clear w4_184 w4_180 g4_11 g4_10 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
    -- 0x442: lw
    obtain ⟨n6, d6, u6⟩ := s5.lw E5.self sv_at_442 (off' := 0x446) (by decide)
      (by rw [g5_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s6 : St n6.mem SV n6 0x446 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
    have m6 : n6.mem = n5.mem := u6.mem
    have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
    have t6 : Steps n0 n6 := t5.trans (.single d6)
    have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
    have E6 : SvCode n6.mem := E5.fr F fr6
    have V6 : SvSaves B n6.mem v := V5.same m6
    have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_2]
    have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_3]
    have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_4]
    have g6_8 : reg n6 (8 : Fin 32) = x8 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_8]
    have g6_9 : reg n6 (9 : Fin 32) = x9 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_9]
    have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, upd_ne (by decide) (by decide), g5_18]
    have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_19]
    have g6_20 : reg n6 (20 : Fin 32) = BitVec.ofNat 32 0xE := by rw [u6.regs, upd_ne (by decide) (by decide), g5_20]
    have g6_21 : reg n6 (21 : Fin 32) = kp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_21]
    have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_22]
    have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_23]
    have g6_24 : reg n6 (24 : Fin 32) = x24 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_24]
    have g6_25 : reg n6 (25 : Fin 32) = x25 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_25]
    have g6_26 : reg n6 (26 : Fin 32) = ll := by rw [u6.regs, upd_ne (by decide) (by decide), g5_26]
    have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_27]
    have g6_10 : reg n6 a0 = 1 := by
      rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g5_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w5_a20]
    have w6_180 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp := by rw [m6]; exact w5_180
    have w6_184 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl := by rw [m6]; exact w5_184
    have w6_a20 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 1 := by rw [m6]; exact w5_a20
    clear w5_a20 w5_184 w5_180 y0_5
    -- 0x446: branch, taken
    obtain ⟨n7, d7, u7⟩ := s6.taken E6.self 0x966 sv_at_446
      (by decide) (by rw [g6_10, s6.zero]; decide)
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
    have g7_8 : reg n7 (8 : Fin 32) = x8 := by rw [u7.regs, g6_8]
    have g7_9 : reg n7 (9 : Fin 32) = x9 := by rw [u7.regs, g6_9]
    have g7_10 : reg n7 a0 = 1 := by rw [u7.regs, g6_10]
    have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, g6_18]
    have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, g6_19]
    have g7_20 : reg n7 (20 : Fin 32) = BitVec.ofNat 32 0xE := by rw [u7.regs, g6_20]
    have g7_21 : reg n7 (21 : Fin 32) = kp := by rw [u7.regs, g6_21]
    have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [u7.regs, g6_22]
    have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [u7.regs, g6_23]
    have g7_24 : reg n7 (24 : Fin 32) = x24 := by rw [u7.regs, g6_24]
    have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [u7.regs, g6_25]
    have g7_26 : reg n7 (26 : Fin 32) = ll := by rw [u7.regs, g6_26]
    have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u7.regs, g6_27]
    have w7_180 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp := by rw [m7]; exact w6_180
    have w7_184 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl := by rw [m7]; exact w6_184
    have w7_a20 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 1 := by rw [m7]; exact w6_a20
    clear w6_a20 w6_184 w6_180 g6_10 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
    exact .inl ⟨(fun ⟨h0', h1', _⟩ => by exact hz_5 h1'), sv_fail F E7 s7 t7 (fun x hx => (fR7 x hx).trans (fM x hx).symm) V7 hret g7_2 g7_18 hO g7_3 g7_4⟩
  have y0_5 := Ok5 hz_5
  have w5_180 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp := (K5.w32 (by decide) (by decide)).trans w4_180
  have w5_184 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl := (K5.w32 (by decide) (by decide)).trans w4_184
  have w5_a20 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := y0_5
  clear w4_184 w4_180 g4_11 g4_10 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  -- 0x442: lw
  obtain ⟨n6, d6, u6⟩ := s5.lw E5.self sv_at_442 (off' := 0x446) (by decide)
    (by rw [g5_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s6 : St n6.mem SV n6 0x446 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = x8 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = x9 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_9]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, upd_ne (by decide) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = BitVec.ofNat 32 0xE := by rw [u6.regs, upd_ne (by decide) (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = kp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = x24 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = ll := by rw [u6.regs, upd_ne (by decide) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_27]
  have g6_10 : reg n6 a0 = 0 := by
    rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g5_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w5_a20]
  have w6_180 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp := by rw [m6]; exact w5_180
  have w6_184 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl := by rw [m6]; exact w5_184
  have w6_a20 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m6]; exact w5_a20
  clear w5_a20 w5_184 w5_180 y0_5 g5_2 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_9 g5_8 g5_4 g5_3 V5 E5 fR5 t5 fr5 Er5 Ok5 K5 rk5 sp5 s5 c5
  -- 0x446: branch, not taken
  obtain ⟨n7, d7, u7⟩ := s6.notTaken E6.self 0x44A sv_at_446
    (by decide) (by rw [g6_10, s6.zero]; decide)
  have s7 : St n7.mem SV n7 0x44A (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = x8 := by rw [u7.regs, g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = x9 := by rw [u7.regs, g6_9]
  have g7_10 : reg n7 a0 = 0 := by rw [u7.regs, g6_10]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = BitVec.ofNat 32 0xE := by rw [u7.regs, g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = kp := by rw [u7.regs, g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [u7.regs, g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [u7.regs, g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = x24 := by rw [u7.regs, g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [u7.regs, g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = ll := by rw [u7.regs, g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u7.regs, g6_27]
  have w7_180 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp := by rw [m7]; exact w6_180
  have w7_184 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl := by rw [m7]; exact w6_184
  have w7_a20 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m7]; exact w6_a20
  clear w6_a20 w6_184 w6_180 g6_10 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  -- 0x44A
  obtain ⟨n8, c8, u8⟩ := s7.block svL644a E7.self svL644a_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem SV n8 0x458 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock svL644a (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
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
  have g8_8 : reg n8 (8 : Fin 32) = x8 := by
    rw [rb8, runBlock_reg _ _ _ (8 : Fin 32) s7.zero (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = x9 := by
    rw [rb8, runBlock_reg _ _ _ (9 : Fin 32) s7.zero (by decide), g7_9]
  have g8_18 : reg n8 (18 : Fin 32) = out := by
    rw [rb8, runBlock_reg _ _ _ (18 : Fin 32) s7.zero (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by
    rw [rb8, runBlock_reg _ _ _ (19 : Fin 32) s7.zero (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = BitVec.ofNat 32 0xE := by
    rw [rb8, runBlock_reg _ _ _ (20 : Fin 32) s7.zero (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = kp := by
    rw [rb8, runBlock_reg _ _ _ (21 : Fin 32) s7.zero (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = x22 := by
    rw [rb8, runBlock_reg _ _ _ (22 : Fin 32) s7.zero (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = x23 := by
    rw [rb8, runBlock_reg _ _ _ (23 : Fin 32) s7.zero (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = x24 := by
    rw [rb8, runBlock_reg _ _ _ (24 : Fin 32) s7.zero (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by
    rw [rb8, runBlock_reg _ _ _ (25 : Fin 32) s7.zero (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = ll := by
    rw [rb8, runBlock_reg _ _ _ (26 : Fin 32) s7.zero (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb8, runBlock_reg _ _ _ (27 : Fin 32) s7.zero (by decide), g7_27]
  have g8_10 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svL644a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g8_11 : reg n8 a1 = B + 0x21A0 + BitVec.ofNat 32 0x178 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svL644a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g8_12 : reg n8 a2 = BitVec.ofNat 32 0xA3 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svL644a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_18, g7_19, g7_20, g7_21, g7_22, g7_23, g7_24, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w8_180 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp := by rw [m8]; exact w7_180
  have w8_184 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl := by rw [m8]; exact w7_184
  have w8_a20 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m8]; exact w7_a20
  clear w7_a20 w7_184 w7_180 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_10 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0x458: sv_optF
  obtain ⟨n9, c9, s9, sp9, rk9, K9, R9, fr9⟩ := sv_optF (oc := 0xA20) (dc := 0x178) (tag := 0xA3)
    F E8 s8 sv_at_458 sv_at_45c (by decide) (by decide) g8_2 g8_10 g8_11 g8_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w8_180 w8_184 tb_in
  have t9 : Steps n0 n9 := t8.trans c9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keepL K9 (by decide)
  rw [sv_mb fR8 tb_in] at R9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rk9 sp (by decide) (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk9 (3 : Fin 32) (by decide) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk9 (4 : Fin 32) (by decide) (by decide), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = x8 := by rw [rk9 (8 : Fin 32) (by decide) (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = x9 := by rw [rk9 (9 : Fin 32) (by decide) (by decide), g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [rk9 (18 : Fin 32) (by decide) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [rk9 (19 : Fin 32) (by decide) (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = BitVec.ofNat 32 0xE := by rw [rk9 (20 : Fin 32) (by decide) (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = kp := by rw [rk9 (21 : Fin 32) (by decide) (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [rk9 (22 : Fin 32) (by decide) (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [rk9 (23 : Fin 32) (by decide) (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = x24 := by rw [rk9 (24 : Fin 32) (by decide) (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [rk9 (25 : Fin 32) (by decide) (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = ll := by rw [rk9 (26 : Fin 32) (by decide) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk9 (27 : Fin 32) (by decide) (by decide), g8_27]
  obtain ⟨r9, hr9⟩ : ∃ r, derOptRes 0xA3 (memBytes M0 (rp) (rl).toNat) = r := ⟨_, rfl⟩
  rcases r9 with _ | (er9 | tl9)
  · rw [hr9] at R9
    obtain ⟨y0_9, y4_9⟩ := R9
    have w9_a24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = 0 := y4_9
    have b9_a20 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := y0_9
    clear w8_a20 w8_184 w8_180 g8_12 g8_11 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
    -- 0x460: lbu
    obtain ⟨n10, d10, u10⟩ := s9.lbu E9.self sv_at_460 (off' := 0x464) (by decide)
    have s10 : St n10.mem SV n10 0x464 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
    have t10 : Steps n0 n10 := t9.trans (.single d10)
    have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : SvCode n10.mem := E9.fr F fr10
    have V10 : SvSaves B n10.mem v := V9.same m10
    have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_4]
    have g10_8 : reg n10 (8 : Fin 32) = x8 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_8]
    have g10_9 : reg n10 (9 : Fin 32) = x9 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_9]
    have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, upd_ne (by decide) (by decide), g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_19]
    have g10_20 : reg n10 (20 : Fin 32) = BitVec.ofNat 32 0xE := by rw [u10.regs, upd_ne (by decide) (by decide), g9_20]
    have g10_21 : reg n10 (21 : Fin 32) = kp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_22]
    have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_23]
    have g10_24 : reg n10 (24 : Fin 32) = x24 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_24]
    have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_25]
    have g10_26 : reg n10 (26 : Fin 32) = ll := by rw [u10.regs, upd_ne (by decide) (by decide), g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_27]
    have g10_10 : reg n10 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
      rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g9_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, b9_a20]
    have w10_a24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = 0 := by rw [m10]; exact w9_a24
    have b10_a20 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m10]; exact b9_a20
    clear b9_a20 w9_a24 y4_9 y0_9
    -- 0x464: branch, not taken
    obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.self 0x468 sv_at_464
      (by decide) (by rw [g10_10, s10.zero]; decide)
    have s11 : St n11.mem SV n11 0x468 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
    have g11_8 : reg n11 (8 : Fin 32) = x8 := by rw [u11.regs, g10_8]
    have g11_9 : reg n11 (9 : Fin 32) = x9 := by rw [u11.regs, g10_9]
    have g11_10 : reg n11 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u11.regs, g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = BitVec.ofNat 32 0xE := by rw [u11.regs, g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = kp := by rw [u11.regs, g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [u11.regs, g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = ll := by rw [u11.regs, g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u11.regs, g10_27]
    have w11_a24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = 0 := by rw [m11]; exact w10_a24
    have b11_a20 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m11]; exact b10_a20
    clear b10_a20 w10_a24 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
    -- 0x468: lw
    obtain ⟨n12, d12, u12⟩ := s11.lw E11.self sv_at_468 (off' := 0x46C) (by decide)
      (by rw [g11_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s12 : St n12.mem SV n12 0x46C (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
    have t12 : Steps n0 n12 := t11.trans (.single d12)
    have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
    have E12 : SvCode n12.mem := E11.fr F fr12
    have V12 : SvSaves B n12.mem v := V11.same m12
    have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
    have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
    have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
    have g12_8 : reg n12 (8 : Fin 32) = x8 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_8]
    have g12_9 : reg n12 (9 : Fin 32) = x9 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_9]
    have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
    have g12_20 : reg n12 (20 : Fin 32) = BitVec.ofNat 32 0xE := by rw [u12.regs, upd_ne (by decide) (by decide), g11_20]
    have g12_21 : reg n12 (21 : Fin 32) = kp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
    have g12_24 : reg n12 (24 : Fin 32) = x24 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
    have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
    have g12_26 : reg n12 (26 : Fin 32) = ll := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
    have g12_10 : reg n12 a0 = 0 := by
      rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g11_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr, w11_a24]
    have w12_a24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = 0 := by rw [m12]; exact w11_a24
    have b12_a20 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m12]; exact b11_a20
    clear b11_a20 w11_a24 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
    -- 0x46C
    obtain ⟨n13, c13, u13⟩ := s12.block svL646c E12.self svL646c_end
      ⟨trivial, trivial⟩
    have m13 : n13.mem = n12.mem := u13.mem
    have s13 : St n13.mem SV n13 0x46E (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
    have rb13 : ∀ q, reg n13 q = (runBlock svL646c (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
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
    have g13_8 : reg n13 (8 : Fin 32) = x8 := by
      rw [rb13, runBlock_reg _ _ _ (8 : Fin 32) s12.zero (by decide), g12_8]
    have g13_9 : reg n13 (9 : Fin 32) = x9 := by
      rw [rb13, runBlock_reg _ _ _ (9 : Fin 32) s12.zero (by decide), g12_9]
    have g13_10 : reg n13 a0 = 0 := by
      rw [rb13, runBlock_reg _ _ _ a0 s12.zero (by decide), g12_10]
    have g13_18 : reg n13 (18 : Fin 32) = out := by
      rw [rb13, runBlock_reg _ _ _ (18 : Fin 32) s12.zero (by decide), g12_18]
    have g13_19 : reg n13 (19 : Fin 32) = bp := by
      rw [rb13, runBlock_reg _ _ _ (19 : Fin 32) s12.zero (by decide), g12_19]
    have g13_21 : reg n13 (21 : Fin 32) = kp := by
      rw [rb13, runBlock_reg _ _ _ (21 : Fin 32) s12.zero (by decide), g12_21]
    have g13_22 : reg n13 (22 : Fin 32) = x22 := by
      rw [rb13, runBlock_reg _ _ _ (22 : Fin 32) s12.zero (by decide), g12_22]
    have g13_23 : reg n13 (23 : Fin 32) = x23 := by
      rw [rb13, runBlock_reg _ _ _ (23 : Fin 32) s12.zero (by decide), g12_23]
    have g13_24 : reg n13 (24 : Fin 32) = x24 := by
      rw [rb13, runBlock_reg _ _ _ (24 : Fin 32) s12.zero (by decide), g12_24]
    have g13_25 : reg n13 (25 : Fin 32) = x25 := by
      rw [rb13, runBlock_reg _ _ _ (25 : Fin 32) s12.zero (by decide), g12_25]
    have g13_26 : reg n13 (26 : Fin 32) = ll := by
      rw [rb13, runBlock_reg _ _ _ (26 : Fin 32) s12.zero (by decide), g12_26]
    have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb13, runBlock_reg _ _ _ (27 : Fin 32) s12.zero (by decide), g12_27]
    have g13_20 : reg n13 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by
      rw [rb13]; simp +decide only [runBlock, BInstr.run, svL646c, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_10, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have w13_a24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = 0 := by rw [m13]; exact w12_a24
    have b13_a20 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m13]; exact b12_a20
    clear b12_a20 w12_a24 g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
    -- 0x46E: branch, taken
    obtain ⟨n14, d14, u14⟩ := s13.taken E13.self 0x966 sv_at_46e
      (by decide) (by rw [g13_10, s13.zero]; rfl)
    have s14 : St n14.mem SV n14 0x966 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
    have m14 : n14.mem = n13.mem := u14.mem
    have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
    have t14 : Steps n0 n14 := t13.trans (.single d14)
    have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
    have E14 : SvCode n14.mem := E13.fr F fr14
    have V14 : SvSaves B n14.mem v := V13.same m14
    have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, g13_2]
    have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, g13_3]
    have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, g13_4]
    have g14_8 : reg n14 (8 : Fin 32) = x8 := by rw [u14.regs, g13_8]
    have g14_9 : reg n14 (9 : Fin 32) = x9 := by rw [u14.regs, g13_9]
    have g14_10 : reg n14 a0 = 0 := by rw [u14.regs, g13_10]
    have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, g13_18]
    have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, g13_19]
    have g14_20 : reg n14 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u14.regs, g13_20]
    have g14_21 : reg n14 (21 : Fin 32) = kp := by rw [u14.regs, g13_21]
    have g14_22 : reg n14 (22 : Fin 32) = x22 := by rw [u14.regs, g13_22]
    have g14_23 : reg n14 (23 : Fin 32) = x23 := by rw [u14.regs, g13_23]
    have g14_24 : reg n14 (24 : Fin 32) = x24 := by rw [u14.regs, g13_24]
    have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [u14.regs, g13_25]
    have g14_26 : reg n14 (26 : Fin 32) = ll := by rw [u14.regs, g13_26]
    have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u14.regs, g13_27]
    have w14_a24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = 0 := by rw [m14]; exact w13_a24
    have b14_a20 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m14]; exact b13_a20
    clear b13_a20 w13_a24 g13_20 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_19 g13_18 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
    exact .inl ⟨(fun ⟨h0', h1', tl9', h2', _⟩ => by rw [hr9] at h2'; cases h2'), sv_fail F E14 s14 t14 (fun x hx => (fR14 x hx).trans (fM x hx).symm) V14 hret g14_2 g14_18 hO g14_3 g14_4⟩
  · rw [hr9] at R9
    obtain ⟨y0_9, -⟩ := R9
    have b9_a20 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := y0_9
    clear w8_a20 w8_184 w8_180 g8_12 g8_11 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
    -- 0x460: lbu
    obtain ⟨n10, d10, u10⟩ := s9.lbu E9.self sv_at_460 (off' := 0x464) (by decide)
    have s10 : St n10.mem SV n10 0x464 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
    have t10 : Steps n0 n10 := t9.trans (.single d10)
    have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : SvCode n10.mem := E9.fr F fr10
    have V10 : SvSaves B n10.mem v := V9.same m10
    have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_4]
    have g10_8 : reg n10 (8 : Fin 32) = x8 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_8]
    have g10_9 : reg n10 (9 : Fin 32) = x9 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_9]
    have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, upd_ne (by decide) (by decide), g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_19]
    have g10_20 : reg n10 (20 : Fin 32) = BitVec.ofNat 32 0xE := by rw [u10.regs, upd_ne (by decide) (by decide), g9_20]
    have g10_21 : reg n10 (21 : Fin 32) = kp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_22]
    have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_23]
    have g10_24 : reg n10 (24 : Fin 32) = x24 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_24]
    have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_25]
    have g10_26 : reg n10 (26 : Fin 32) = ll := by rw [u10.regs, upd_ne (by decide) (by decide), g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_27]
    have g10_10 : reg n10 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g9_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, b9_a20]
    have b10_a20 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := by rw [m10]; exact b9_a20
    clear b9_a20 y0_9
    -- 0x464: branch, taken
    obtain ⟨n11, d11, u11⟩ := s10.taken E10.self 0x17E sv_at_464
      (by decide) (by rw [g10_10, s10.zero]; decide)
    have s11 : St n11.mem SV n11 0x17E (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
    have g11_8 : reg n11 (8 : Fin 32) = x8 := by rw [u11.regs, g10_8]
    have g11_9 : reg n11 (9 : Fin 32) = x9 := by rw [u11.regs, g10_9]
    have g11_10 : reg n11 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u11.regs, g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = BitVec.ofNat 32 0xE := by rw [u11.regs, g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = kp := by rw [u11.regs, g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [u11.regs, g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = ll := by rw [u11.regs, g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u11.regs, g10_27]
    have b11_a20 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := by rw [m11]; exact b10_a20
    clear b10_a20 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
    -- 0x17E: lbu
    obtain ⟨n12, d12, u12⟩ := s11.lbu E11.self sv_at_17e (off' := 0x182) (by decide)
    have s12 : St n12.mem SV n12 0x182 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
    have t12 : Steps n0 n12 := t11.trans (.single d12)
    have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
    have E12 : SvCode n12.mem := E11.fr F fr12
    have V12 : SvSaves B n12.mem v := V11.same m12
    have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
    have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
    have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
    have g12_8 : reg n12 (8 : Fin 32) = x8 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_8]
    have g12_9 : reg n12 (9 : Fin 32) = x9 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_9]
    have g12_10 : reg n12 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_10]
    have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
    have g12_21 : reg n12 (21 : Fin 32) = kp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
    have g12_24 : reg n12 (24 : Fin 32) = x24 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
    have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
    have g12_26 : reg n12 (26 : Fin 32) = ll := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
    have b12_a20 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := by rw [m12]; exact b11_a20
    clear b11_a20 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
    -- 0x182: j
    obtain ⟨n13, d13, u13⟩ := s12.jump E12.self sv_at_182 (off' := 0x966) (by decide)
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
    have g13_8 : reg n13 (8 : Fin 32) = x8 := by rw [u13.regs, g12_8]
    have g13_9 : reg n13 (9 : Fin 32) = x9 := by rw [u13.regs, g12_9]
    have g13_10 : reg n13 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u13.regs, g12_10]
    have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, g12_18]
    have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, g12_19]
    have g13_21 : reg n13 (21 : Fin 32) = kp := by rw [u13.regs, g12_21]
    have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [u13.regs, g12_22]
    have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [u13.regs, g12_23]
    have g13_24 : reg n13 (24 : Fin 32) = x24 := by rw [u13.regs, g12_24]
    have g13_25 : reg n13 (25 : Fin 32) = x25 := by rw [u13.regs, g12_25]
    have g13_26 : reg n13 (26 : Fin 32) = ll := by rw [u13.regs, g12_26]
    have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u13.regs, g12_27]
    have b13_a20 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := by rw [m13]; exact b12_a20
    clear b12_a20 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_19 g12_18 g12_10 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
    exact .inl ⟨(fun ⟨h0', h1', tl9', h2', _⟩ => by rw [hr9] at h2'; cases h2'), sv_fail F E13 s13 t13 (fun x hx => (fR13 x hx).trans (fM x hx).symm) V13 hret g13_2 g13_18 hO g13_3 g13_4⟩
  rw [hr9] at R9
  obtain ⟨y0_9, y4_9, y8_9, y12_9, y16_9, y20_9, d8_9, d12_9⟩ := R9
  have w9_180 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := d8_9
  have w9_184 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := d12_9
  have w9_a24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (rp) + BitVec.ofNat 32 tl9.header := y4_9
  have w9_a28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl9.len := y8_9
  have w9_a2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = rp := y12_9
  have w9_a30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl9.header + tl9.len) := y16_9
  have b9_a20 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := y0_9
  have b9_a34 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := y20_9
  clear w8_a20 w8_184 w8_180 g8_12 g8_11 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
  -- 0x460: lbu
  obtain ⟨n10, d10, u10⟩ := s9.lbu E9.self sv_at_460 (off' := 0x464) (by decide)
  have s10 : St n10.mem SV n10 0x464 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = x8 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = x9 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_9]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, upd_ne (by decide) (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = BitVec.ofNat 32 0xE := by rw [u10.regs, upd_ne (by decide) (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = kp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = x24 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = ll := by rw [u10.regs, upd_ne (by decide) (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_27]
  have g10_10 : reg n10 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g9_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, b9_a20]
  have w10_180 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m10]; exact w9_180
  have w10_184 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m10]; exact w9_184
  have w10_a24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m10]; exact w9_a24
  have w10_a28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl9.len := by rw [m10]; exact w9_a28
  have w10_a2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = rp := by rw [m10]; exact w9_a2c
  have w10_a30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m10]; exact w9_a30
  have b10_a20 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m10]; exact b9_a20
  have b10_a34 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m10]; exact b9_a34
  clear b9_a34 b9_a20 w9_a30 w9_a2c w9_a28 w9_a24 w9_184 w9_180 d12_9 d8_9 y20_9 y16_9 y12_9 y8_9 y4_9 y0_9 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 K9 rk9 sp9 s9 c9
  -- 0x464: branch, not taken
  obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.self 0x468 sv_at_464
    (by decide) (by rw [g10_10, s10.zero]; decide)
  have s11 : St n11.mem SV n11 0x468 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = x8 := by rw [u11.regs, g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = x9 := by rw [u11.regs, g10_9]
  have g11_10 : reg n11 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u11.regs, g10_10]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = BitVec.ofNat 32 0xE := by rw [u11.regs, g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = kp := by rw [u11.regs, g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [u11.regs, g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [u11.regs, g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = ll := by rw [u11.regs, g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u11.regs, g10_27]
  have w11_180 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m11]; exact w10_180
  have w11_184 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m11]; exact w10_184
  have w11_a24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m11]; exact w10_a24
  have w11_a28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl9.len := by rw [m11]; exact w10_a28
  have w11_a2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = rp := by rw [m11]; exact w10_a2c
  have w11_a30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m11]; exact w10_a30
  have b11_a20 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m11]; exact b10_a20
  have b11_a34 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m11]; exact b10_a34
  clear b10_a34 b10_a20 w10_a30 w10_a2c w10_a28 w10_a24 w10_184 w10_180 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
  -- 0x468: lw
  obtain ⟨n12, d12, u12⟩ := s11.lw E11.self sv_at_468 (off' := 0x46C) (by decide)
    (by rw [g11_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s12 : St n12.mem SV n12 0x46C (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = x8 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = x9 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = BitVec.ofNat 32 0xE := by rw [u12.regs, upd_ne (by decide) (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = kp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = x24 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = ll := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
  have g12_10 : reg n12 a0 = (rp) + BitVec.ofNat 32 tl9.header := by
    rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g11_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr, w11_a24]
  have w12_180 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m12]; exact w11_180
  have w12_184 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m12]; exact w11_184
  have w12_a24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m12]; exact w11_a24
  have w12_a28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl9.len := by rw [m12]; exact w11_a28
  have w12_a2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = rp := by rw [m12]; exact w11_a2c
  have w12_a30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m12]; exact w11_a30
  have b12_a20 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m12]; exact b11_a20
  have b12_a34 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m12]; exact b11_a34
  clear b11_a34 b11_a20 w11_a30 w11_a2c w11_a28 w11_a24 w11_184 w11_180 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  -- 0x46C
  obtain ⟨n13, c13, u13⟩ := s12.block svL646c E12.self svL646c_end
    ⟨trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem SV n13 0x46E (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock svL646c (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
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
  have g13_8 : reg n13 (8 : Fin 32) = x8 := by
    rw [rb13, runBlock_reg _ _ _ (8 : Fin 32) s12.zero (by decide), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = x9 := by
    rw [rb13, runBlock_reg _ _ _ (9 : Fin 32) s12.zero (by decide), g12_9]
  have g13_10 : reg n13 a0 = (rp) + BitVec.ofNat 32 tl9.header := by
    rw [rb13, runBlock_reg _ _ _ a0 s12.zero (by decide), g12_10]
  have g13_18 : reg n13 (18 : Fin 32) = out := by
    rw [rb13, runBlock_reg _ _ _ (18 : Fin 32) s12.zero (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by
    rw [rb13, runBlock_reg _ _ _ (19 : Fin 32) s12.zero (by decide), g12_19]
  have g13_21 : reg n13 (21 : Fin 32) = kp := by
    rw [rb13, runBlock_reg _ _ _ (21 : Fin 32) s12.zero (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by
    rw [rb13, runBlock_reg _ _ _ (22 : Fin 32) s12.zero (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = x23 := by
    rw [rb13, runBlock_reg _ _ _ (23 : Fin 32) s12.zero (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = x24 := by
    rw [rb13, runBlock_reg _ _ _ (24 : Fin 32) s12.zero (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by
    rw [rb13, runBlock_reg _ _ _ (25 : Fin 32) s12.zero (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = ll := by
    rw [rb13, runBlock_reg _ _ _ (26 : Fin 32) s12.zero (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb13, runBlock_reg _ _ _ (27 : Fin 32) s12.zero (by decide), g12_27]
  have g13_20 : reg n13 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svL646c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_10, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w13_180 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m13]; exact w12_180
  have w13_184 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m13]; exact w12_184
  have w13_a24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m13]; exact w12_a24
  have w13_a28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl9.len := by rw [m13]; exact w12_a28
  have w13_a2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = rp := by rw [m13]; exact w12_a2c
  have w13_a30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m13]; exact w12_a30
  have b13_a20 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m13]; exact b12_a20
  have b13_a34 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m13]; exact b12_a34
  clear b12_a34 b12_a20 w12_a30 w12_a2c w12_a28 w12_a24 w12_184 w12_180 g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
  -- 0x46E: branch, not taken
  obtain ⟨n14, d14, u14⟩ := s13.notTaken E13.self 0x472 sv_at_46e
    (by decide) (by rw [g13_10, s13.zero]; exact br_beq_f (tb_in.ok_ne (opt_ok_elem hr9)))
  have s14 : St n14.mem SV n14 0x472 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
  have t14 : Steps n0 n14 := t13.trans (.single d14)
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.same m14
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = x8 := by rw [u14.regs, g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = x9 := by rw [u14.regs, g13_9]
  have g14_10 : reg n14 a0 = (rp) + BitVec.ofNat 32 tl9.header := by rw [u14.regs, g13_10]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u14.regs, g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = kp := by rw [u14.regs, g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = x22 := by rw [u14.regs, g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = x23 := by rw [u14.regs, g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = x24 := by rw [u14.regs, g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [u14.regs, g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = ll := by rw [u14.regs, g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u14.regs, g13_27]
  have w14_180 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m14]; exact w13_180
  have w14_184 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m14]; exact w13_184
  have w14_a24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m14]; exact w13_a24
  have w14_a28 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl9.len := by rw [m14]; exact w13_a28
  have w14_a2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = rp := by rw [m14]; exact w13_a2c
  have w14_a30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m14]; exact w13_a30
  have b14_a20 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m14]; exact b13_a20
  have b14_a34 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m14]; exact b13_a34
  clear b13_a34 b13_a20 w13_a30 w13_a2c w13_a28 w13_a24 w13_184 w13_180 g13_20 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_19 g13_18 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
  -- 0x472: lw
  obtain ⟨n15, d15, u15⟩ := s14.lw E14.self sv_at_472 (off' := 0x476) (by decide)
    (by rw [g14_2, show B + 0x21A0 + 0x184 = B + 0x21A0 + BitVec.ofNat 32 0x184 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s15 : St n15.mem SV n15 0x476 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = x8 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = x9 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_9]
  have g15_10 : reg n15 a0 = (rp) + BitVec.ofNat 32 tl9.header := by rw [u15.regs, upd_ne (by decide) (by decide), g14_10]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, upd_ne (by decide) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = kp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = x24 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = ll := by rw [u15.regs, upd_ne (by decide) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_27]
  have g15_11 : reg n15 a1 = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by
    rw [u15.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g14_2, show B + 0x21A0 + 0x184 = B + 0x21A0 + BitVec.ofNat 32 0x184 by sv_addr, w14_184]
  have w15_180 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m15]; exact w14_180
  have w15_184 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m15]; exact w14_184
  have w15_a24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m15]; exact w14_a24
  have w15_a28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl9.len := by rw [m15]; exact w14_a28
  have w15_a2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = rp := by rw [m15]; exact w14_a2c
  have w15_a30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m15]; exact w14_a30
  have b15_a20 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m15]; exact b14_a20
  have b15_a34 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m15]; exact b14_a34
  clear b14_a34 b14_a20 w14_a30 w14_a2c w14_a28 w14_a24 w14_184 w14_180 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_10 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
  by_cases hz_15 : (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) = 0
  rotate_left
  · -- 0x476: branch, taken
    obtain ⟨n16, d16, u16⟩ := s15.taken E15.self 0x1C0 sv_at_476
      (by decide) (by rw [g15_11, s15.zero]; exact br_bne_t hz_15)
    have s16 : St n16.mem SV n16 0x1C0 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
    have m16 : n16.mem = n15.mem := u16.mem
    have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
    have t16 : Steps n0 n16 := t15.trans (.single d16)
    have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
    have E16 : SvCode n16.mem := E15.fr F fr16
    have V16 : SvSaves B n16.mem v := V15.same m16
    have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, g15_2]
    have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, g15_3]
    have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, g15_4]
    have g16_8 : reg n16 (8 : Fin 32) = x8 := by rw [u16.regs, g15_8]
    have g16_9 : reg n16 (9 : Fin 32) = x9 := by rw [u16.regs, g15_9]
    have g16_10 : reg n16 a0 = (rp) + BitVec.ofNat 32 tl9.header := by rw [u16.regs, g15_10]
    have g16_11 : reg n16 a1 = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [u16.regs, g15_11]
    have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, g15_18]
    have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, g15_19]
    have g16_20 : reg n16 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u16.regs, g15_20]
    have g16_21 : reg n16 (21 : Fin 32) = kp := by rw [u16.regs, g15_21]
    have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [u16.regs, g15_22]
    have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [u16.regs, g15_23]
    have g16_24 : reg n16 (24 : Fin 32) = x24 := by rw [u16.regs, g15_24]
    have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [u16.regs, g15_25]
    have g16_26 : reg n16 (26 : Fin 32) = ll := by rw [u16.regs, g15_26]
    have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u16.regs, g15_27]
    have w16_180 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m16]; exact w15_180
    have w16_184 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m16]; exact w15_184
    have w16_a24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m16]; exact w15_a24
    have w16_a28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl9.len := by rw [m16]; exact w15_a28
    have w16_a2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = rp := by rw [m16]; exact w15_a2c
    have w16_a30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m16]; exact w15_a30
    have b16_a20 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m16]; exact b15_a20
    have b16_a34 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m16]; exact b15_a34
    clear b15_a34 b15_a20 w15_a30 w15_a2c w15_a28 w15_a24 w15_184 w15_180 g15_11 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_10 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
    -- 0x1C0
    obtain ⟨n17, c17, u17⟩ := s16.block svL61c0 E16.self svL61c0_end
      ⟨trivial, trivial⟩
    have m17 : n17.mem = n16.mem := u17.mem
    have s17 : St n17.mem SV n17 0x1C2 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
    have rb17 : ∀ q, reg n17 q = (runBlock svL61c0 (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
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
    have g17_8 : reg n17 (8 : Fin 32) = x8 := by
      rw [rb17, runBlock_reg _ _ _ (8 : Fin 32) s16.zero (by decide), g16_8]
    have g17_9 : reg n17 (9 : Fin 32) = x9 := by
      rw [rb17, runBlock_reg _ _ _ (9 : Fin 32) s16.zero (by decide), g16_9]
    have g17_10 : reg n17 a0 = (rp) + BitVec.ofNat 32 tl9.header := by
      rw [rb17, runBlock_reg _ _ _ a0 s16.zero (by decide), g16_10]
    have g17_11 : reg n17 a1 = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by
      rw [rb17, runBlock_reg _ _ _ a1 s16.zero (by decide), g16_11]
    have g17_18 : reg n17 (18 : Fin 32) = out := by
      rw [rb17, runBlock_reg _ _ _ (18 : Fin 32) s16.zero (by decide), g16_18]
    have g17_19 : reg n17 (19 : Fin 32) = bp := by
      rw [rb17, runBlock_reg _ _ _ (19 : Fin 32) s16.zero (by decide), g16_19]
    have g17_21 : reg n17 (21 : Fin 32) = kp := by
      rw [rb17, runBlock_reg _ _ _ (21 : Fin 32) s16.zero (by decide), g16_21]
    have g17_22 : reg n17 (22 : Fin 32) = x22 := by
      rw [rb17, runBlock_reg _ _ _ (22 : Fin 32) s16.zero (by decide), g16_22]
    have g17_23 : reg n17 (23 : Fin 32) = x23 := by
      rw [rb17, runBlock_reg _ _ _ (23 : Fin 32) s16.zero (by decide), g16_23]
    have g17_24 : reg n17 (24 : Fin 32) = x24 := by
      rw [rb17, runBlock_reg _ _ _ (24 : Fin 32) s16.zero (by decide), g16_24]
    have g17_25 : reg n17 (25 : Fin 32) = x25 := by
      rw [rb17, runBlock_reg _ _ _ (25 : Fin 32) s16.zero (by decide), g16_25]
    have g17_26 : reg n17 (26 : Fin 32) = ll := by
      rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
    have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb17, runBlock_reg _ _ _ (27 : Fin 32) s16.zero (by decide), g16_27]
    have g17_20 : reg n17 (20 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb17]; simp +decide only [runBlock, BInstr.run, svL61c0, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_10, g16_11, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, s16.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have w17_180 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m17]; exact w16_180
    have w17_184 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m17]; exact w16_184
    have w17_a24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m17]; exact w16_a24
    have w17_a28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl9.len := by rw [m17]; exact w16_a28
    have w17_a2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = rp := by rw [m17]; exact w16_a2c
    have w17_a30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m17]; exact w16_a30
    have b17_a20 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m17]; exact b16_a20
    have b17_a34 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m17]; exact b16_a34
    clear b16_a34 b16_a20 w16_a30 w16_a2c w16_a28 w16_a24 w16_184 w16_180 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_11 g16_10 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
    -- 0x1C2: j
    obtain ⟨n18, d18, u18⟩ := s17.jump E17.self sv_at_1c2 (off' := 0x966) (by decide)
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
    have g18_8 : reg n18 (8 : Fin 32) = x8 := by rw [u18.regs, g17_8]
    have g18_9 : reg n18 (9 : Fin 32) = x9 := by rw [u18.regs, g17_9]
    have g18_10 : reg n18 a0 = (rp) + BitVec.ofNat 32 tl9.header := by rw [u18.regs, g17_10]
    have g18_11 : reg n18 a1 = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [u18.regs, g17_11]
    have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, g17_18]
    have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, g17_19]
    have g18_20 : reg n18 (20 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u18.regs, g17_20]
    have g18_21 : reg n18 (21 : Fin 32) = kp := by rw [u18.regs, g17_21]
    have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [u18.regs, g17_22]
    have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [u18.regs, g17_23]
    have g18_24 : reg n18 (24 : Fin 32) = x24 := by rw [u18.regs, g17_24]
    have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [u18.regs, g17_25]
    have g18_26 : reg n18 (26 : Fin 32) = ll := by rw [u18.regs, g17_26]
    have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u18.regs, g17_27]
    have w18_180 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m18]; exact w17_180
    have w18_184 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m18]; exact w17_184
    have w18_a24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m18]; exact w17_a24
    have w18_a28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl9.len := by rw [m18]; exact w17_a28
    have w18_a2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = rp := by rw [m18]; exact w17_a2c
    have w18_a30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m18]; exact w17_a30
    have b18_a20 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m18]; exact b17_a20
    have b18_a34 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m18]; exact b17_a34
    clear b17_a34 b17_a20 w17_a30 w17_a2c w17_a28 w17_a24 w17_184 w17_180 g17_20 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_19 g17_18 g17_11 g17_10 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
    exact .inl ⟨(fun ⟨h0', h1', tl9', h2', h3', _⟩ => by rw [hr9] at h2'; cases h2'; exact hz_15 h3'), sv_fail F E18 s18 t18 (fun x hx => (fR18 x hx).trans (fM x hx).symm) V18 hret g18_2 g18_18 hO g18_3 g18_4⟩
  -- 0x476: branch, not taken
  obtain ⟨n16, d16, u16⟩ := s15.notTaken E15.self 0x47A sv_at_476
    (by decide) (by rw [g15_11, s15.zero]; exact br_bne_f hz_15)
  have s16 : St n16.mem SV n16 0x47A (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans (.single d16)
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = x8 := by rw [u16.regs, g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = x9 := by rw [u16.regs, g15_9]
  have g16_10 : reg n16 a0 = (rp) + BitVec.ofNat 32 tl9.header := by rw [u16.regs, g15_10]
  have g16_11 : reg n16 a1 = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [u16.regs, g15_11]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u16.regs, g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = kp := by rw [u16.regs, g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [u16.regs, g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [u16.regs, g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = x24 := by rw [u16.regs, g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = x25 := by rw [u16.regs, g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = ll := by rw [u16.regs, g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u16.regs, g15_27]
  have w16_180 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m16]; exact w15_180
  have w16_184 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m16]; exact w15_184
  have w16_a24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m16]; exact w15_a24
  have w16_a28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl9.len := by rw [m16]; exact w15_a28
  have w16_a2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = rp := by rw [m16]; exact w15_a2c
  have w16_a30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m16]; exact w15_a30
  have b16_a20 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m16]; exact b15_a20
  have b16_a34 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m16]; exact b15_a34
  clear b15_a34 b15_a20 w15_a30 w15_a2c w15_a28 w15_a24 w15_184 w15_180 g15_11 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_10 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
  -- 0x47A: lw
  obtain ⟨n17, d17, u17⟩ := s16.lw E16.self sv_at_47a (off' := 0x47E) (by decide)
    (by rw [g16_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s17 : St n17.mem SV n17 0x47E (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans (.single d17)
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = x8 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = x9 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_9]
  have g17_10 : reg n17 a0 = (rp) + BitVec.ofNat 32 tl9.header := by rw [u17.regs, upd_ne (by decide) (by decide), g16_10]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, upd_ne (by decide) (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = kp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = x22 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = x23 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = x24 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = x25 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = ll := by rw [u17.regs, upd_ne (by decide) (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_27]
  have g17_11 : reg n17 a1 = BitVec.ofNat 32 tl9.len := by
    rw [u17.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g16_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr, w16_a28]
  have w17_180 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m17]; exact w16_180
  have w17_184 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m17]; exact w16_184
  have w17_a24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m17]; exact w16_a24
  have w17_a28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl9.len := by rw [m17]; exact w16_a28
  have w17_a2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = rp := by rw [m17]; exact w16_a2c
  have w17_a30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m17]; exact w16_a30
  have b17_a20 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m17]; exact b16_a20
  have b17_a34 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m17]; exact b16_a34
  clear b16_a34 b16_a20 w16_a30 w16_a2c w16_a28 w16_a24 w16_184 w16_180 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_11 g16_10 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
  -- 0x47E
  obtain ⟨n18, c18, u18⟩ := s17.block svL647e E17.self svL647e_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have s18 : St n18.mem SV n18 0x486 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have rb18 : ∀ q, reg n18 q = (runBlock svL647e (n17.mem, reg n17)).2 q := fun q => by rw [u18.regs]
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
  have g18_8 : reg n18 (8 : Fin 32) = x8 := by
    rw [rb18, runBlock_reg _ _ _ (8 : Fin 32) s17.zero (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = x9 := by
    rw [rb18, runBlock_reg _ _ _ (9 : Fin 32) s17.zero (by decide), g17_9]
  have g18_10 : reg n18 a0 = (rp) + BitVec.ofNat 32 tl9.header := by
    rw [rb18, runBlock_reg _ _ _ a0 s17.zero (by decide), g17_10]
  have g18_11 : reg n18 a1 = BitVec.ofNat 32 tl9.len := by
    rw [rb18, runBlock_reg _ _ _ a1 s17.zero (by decide), g17_11]
  have g18_18 : reg n18 (18 : Fin 32) = out := by
    rw [rb18, runBlock_reg _ _ _ (18 : Fin 32) s17.zero (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by
    rw [rb18, runBlock_reg _ _ _ (19 : Fin 32) s17.zero (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb18, runBlock_reg _ _ _ (20 : Fin 32) s17.zero (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = kp := by
    rw [rb18, runBlock_reg _ _ _ (21 : Fin 32) s17.zero (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = x22 := by
    rw [rb18, runBlock_reg _ _ _ (22 : Fin 32) s17.zero (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = x23 := by
    rw [rb18, runBlock_reg _ _ _ (23 : Fin 32) s17.zero (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = x24 := by
    rw [rb18, runBlock_reg _ _ _ (24 : Fin 32) s17.zero (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by
    rw [rb18, runBlock_reg _ _ _ (25 : Fin 32) s17.zero (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = ll := by
    rw [rb18, runBlock_reg _ _ _ (26 : Fin 32) s17.zero (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb18, runBlock_reg _ _ _ (27 : Fin 32) s17.zero (by decide), g17_27]
  have g18_12 : reg n18 a2 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svL647e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g17_2, g17_3, g17_4, g17_8, g17_9, g17_10, g17_11, g17_18, g17_19, g17_20, g17_21, g17_22, g17_23, g17_24, g17_25, g17_26, g17_27, s17.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w18_180 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m18]; exact w17_180
  have w18_184 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m18]; exact w17_184
  have w18_a24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m18]; exact w17_a24
  have w18_a28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl9.len := by rw [m18]; exact w17_a28
  have w18_a2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = rp := by rw [m18]; exact w17_a2c
  have w18_a30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m18]; exact w17_a30
  have b18_a20 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m18]; exact b17_a20
  have b18_a34 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m18]; exact b17_a34
  clear b17_a34 b17_a20 w17_a30 w17_a2c w17_a28 w17_a24 w17_184 w17_180 g17_11 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_10 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
  -- 0x486: sw
  obtain ⟨n19, d19, s19, fr19, K19, W19, rg19⟩ := sv_sw F E18 s18 sv_at_486 (off' := 0x488) (c := 0x1320)
    (by decide) (by rw [g18_12]; sv_addr) (by decide) (by decide)
  have t19 : Steps n0 n19 := t18.trans d19
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.keep K19 (by decide)
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [rg19 sp, g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg19 (3 : Fin 32), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg19 (4 : Fin 32), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = x8 := by rw [rg19 (8 : Fin 32), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = x9 := by rw [rg19 (9 : Fin 32), g18_9]
  have g19_10 : reg n19 a0 = (rp) + BitVec.ofNat 32 tl9.header := by rw [rg19 a0, g18_10]
  have g19_11 : reg n19 a1 = BitVec.ofNat 32 tl9.len := by rw [rg19 a1, g18_11]
  have g19_12 : reg n19 a2 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg19 a2, g18_12]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [rg19 (18 : Fin 32), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [rg19 (19 : Fin 32), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg19 (20 : Fin 32), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = kp := by rw [rg19 (21 : Fin 32), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [rg19 (22 : Fin 32), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [rg19 (23 : Fin 32), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = x24 := by rw [rg19 (24 : Fin 32), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [rg19 (25 : Fin 32), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = ll := by rw [rg19 (26 : Fin 32), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg19 (27 : Fin 32), g18_27]
  have w19_180 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K19.w32 (by decide) (by decide)).trans w18_180
  have w19_184 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K19.w32 (by decide) (by decide)).trans w18_184
  have w19_a24 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (rp) + BitVec.ofNat 32 tl9.header := (K19.w32 (by decide) (by decide)).trans w18_a24
  have w19_a28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl9.len := (K19.w32 (by decide) (by decide)).trans w18_a28
  have w19_a2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = rp := (K19.w32 (by decide) (by decide)).trans w18_a2c
  have w19_a30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K19.w32 (by decide) (by decide)).trans w18_a30
  have b19_a20 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := (K19.b8 (by decide) (by decide)).trans b18_a20
  have b19_a34 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := (K19.b8 (by decide) (by decide)).trans b18_a34
  have w19_1320 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [W19, g18_10]
  clear b18_a34 b18_a20 w18_a30 w18_a2c w18_a28 w18_a24 w18_184 w18_180 g18_12 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_11 g18_10 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 rb18 s18 m18 u18 c18
  -- 0x488: sw
  obtain ⟨n20, d20, s20, fr20, K20, W20, rg20⟩ := sv_sw F E19 s19 sv_at_488 (off' := 0x48A) (c := 0x1324)
    (by decide) (by rw [g19_12]; sv_addr) (by decide) (by decide)
  have t20 : Steps n0 n20 := t19.trans d20
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.keep K20 (by decide)
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [rg20 sp, g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg20 (3 : Fin 32), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg20 (4 : Fin 32), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = x8 := by rw [rg20 (8 : Fin 32), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = x9 := by rw [rg20 (9 : Fin 32), g19_9]
  have g20_10 : reg n20 a0 = (rp) + BitVec.ofNat 32 tl9.header := by rw [rg20 a0, g19_10]
  have g20_11 : reg n20 a1 = BitVec.ofNat 32 tl9.len := by rw [rg20 a1, g19_11]
  have g20_12 : reg n20 a2 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg20 a2, g19_12]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [rg20 (18 : Fin 32), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [rg20 (19 : Fin 32), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg20 (20 : Fin 32), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = kp := by rw [rg20 (21 : Fin 32), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = x22 := by rw [rg20 (22 : Fin 32), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = x23 := by rw [rg20 (23 : Fin 32), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = x24 := by rw [rg20 (24 : Fin 32), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = x25 := by rw [rg20 (25 : Fin 32), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = ll := by rw [rg20 (26 : Fin 32), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg20 (27 : Fin 32), g19_27]
  have w20_180 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K20.w32 (by decide) (by decide)).trans w19_180
  have w20_184 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K20.w32 (by decide) (by decide)).trans w19_184
  have w20_a24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (rp) + BitVec.ofNat 32 tl9.header := (K20.w32 (by decide) (by decide)).trans w19_a24
  have w20_a28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl9.len := (K20.w32 (by decide) (by decide)).trans w19_a28
  have w20_a2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = rp := (K20.w32 (by decide) (by decide)).trans w19_a2c
  have w20_a30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K20.w32 (by decide) (by decide)).trans w19_a30
  have w20_1320 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := (K20.w32 (by decide) (by decide)).trans w19_1320
  have b20_a20 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := (K20.b8 (by decide) (by decide)).trans b19_a20
  have b20_a34 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := (K20.b8 (by decide) (by decide)).trans b19_a34
  have w20_1324 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [W20, g19_11]
  clear w19_1320 b19_a34 b19_a20 w19_a30 w19_a2c w19_a28 w19_a24 w19_184 w19_180 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_12 g19_11 g19_10 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 rg19 W19 K19 fr19 s19 d19
  -- 0x48A: sw
  obtain ⟨n21, d21, s21, fr21, K21, W21, rg21⟩ := sv_sw F E20 s20 sv_at_48a (off' := 0x48C) (c := 0x1328)
    (by decide) (by rw [g20_12]; sv_addr) (by decide) (by decide)
  have t21 : Steps n0 n21 := t20.trans d21
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.keep K21 (by decide)
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [rg21 sp, g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg21 (3 : Fin 32), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg21 (4 : Fin 32), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = x8 := by rw [rg21 (8 : Fin 32), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = x9 := by rw [rg21 (9 : Fin 32), g20_9]
  have g21_10 : reg n21 a0 = (rp) + BitVec.ofNat 32 tl9.header := by rw [rg21 a0, g20_10]
  have g21_11 : reg n21 a1 = BitVec.ofNat 32 tl9.len := by rw [rg21 a1, g20_11]
  have g21_12 : reg n21 a2 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg21 a2, g20_12]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [rg21 (18 : Fin 32), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [rg21 (19 : Fin 32), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg21 (20 : Fin 32), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = kp := by rw [rg21 (21 : Fin 32), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [rg21 (22 : Fin 32), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = x23 := by rw [rg21 (23 : Fin 32), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = x24 := by rw [rg21 (24 : Fin 32), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [rg21 (25 : Fin 32), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = ll := by rw [rg21 (26 : Fin 32), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg21 (27 : Fin 32), g20_27]
  have w21_180 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K21.w32 (by decide) (by decide)).trans w20_180
  have w21_184 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K21.w32 (by decide) (by decide)).trans w20_184
  have w21_a24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (rp) + BitVec.ofNat 32 tl9.header := (K21.w32 (by decide) (by decide)).trans w20_a24
  have w21_a28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl9.len := (K21.w32 (by decide) (by decide)).trans w20_a28
  have w21_a2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = rp := (K21.w32 (by decide) (by decide)).trans w20_a2c
  have w21_a30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K21.w32 (by decide) (by decide)).trans w20_a30
  have w21_1320 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := (K21.w32 (by decide) (by decide)).trans w20_1320
  have w21_1324 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := (K21.w32 (by decide) (by decide)).trans w20_1324
  have b21_a20 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := (K21.b8 (by decide) (by decide)).trans b20_a20
  have b21_a34 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := (K21.b8 (by decide) (by decide)).trans b20_a34
  have w21_1328 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = (rp) + BitVec.ofNat 32 tl9.header := by rw [W21, g20_10]
  clear w20_1324 b20_a34 b20_a20 w20_1320 w20_a30 w20_a2c w20_a28 w20_a24 w20_184 w20_180 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_12 g20_11 g20_10 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 rg20 W20 K20 fr20 s20 d20
  -- 0x48C
  obtain ⟨n22, c22, u22⟩ := s21.block svL648c E21.self svL648c_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have s22 : St n22.mem SV n22 0x496 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have rb22 : ∀ q, reg n22 q = (runBlock svL648c (n21.mem, reg n21)).2 q := fun q => by rw [u22.regs]
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
  have g22_9 : reg n22 (9 : Fin 32) = x9 := by
    rw [rb22, runBlock_reg _ _ _ (9 : Fin 32) s21.zero (by decide), g21_9]
  have g22_11 : reg n22 a1 = BitVec.ofNat 32 tl9.len := by
    rw [rb22, runBlock_reg _ _ _ a1 s21.zero (by decide), g21_11]
  have g22_12 : reg n22 a2 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb22, runBlock_reg _ _ _ a2 s21.zero (by decide), g21_12]
  have g22_18 : reg n22 (18 : Fin 32) = out := by
    rw [rb22, runBlock_reg _ _ _ (18 : Fin 32) s21.zero (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by
    rw [rb22, runBlock_reg _ _ _ (19 : Fin 32) s21.zero (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb22, runBlock_reg _ _ _ (20 : Fin 32) s21.zero (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = kp := by
    rw [rb22, runBlock_reg _ _ _ (21 : Fin 32) s21.zero (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = x22 := by
    rw [rb22, runBlock_reg _ _ _ (22 : Fin 32) s21.zero (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = x23 := by
    rw [rb22, runBlock_reg _ _ _ (23 : Fin 32) s21.zero (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = x24 := by
    rw [rb22, runBlock_reg _ _ _ (24 : Fin 32) s21.zero (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = x25 := by
    rw [rb22, runBlock_reg _ _ _ (25 : Fin 32) s21.zero (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = ll := by
    rw [rb22, runBlock_reg _ _ _ (26 : Fin 32) s21.zero (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb22, runBlock_reg _ _ _ (27 : Fin 32) s21.zero (by decide), g21_27]
  have g22_8 : reg n22 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, svL648c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_10, g21_11, g21_12, g21_18, g21_19, g21_20, g21_21, g21_22, g21_23, g21_24, g21_25, g21_26, g21_27, s21.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g22_10 : reg n22 a0 = BitVec.ofNat 32 0x1320 := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, svL648c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_10, g21_11, g21_12, g21_18, g21_19, g21_20, g21_21, g21_22, g21_23, g21_24, g21_25, g21_26, g21_27, s21.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w22_180 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m22]; exact w21_180
  have w22_184 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m22]; exact w21_184
  have w22_a24 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m22]; exact w21_a24
  have w22_a28 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl9.len := by rw [m22]; exact w21_a28
  have w22_a2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = rp := by rw [m22]; exact w21_a2c
  have w22_a30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m22]; exact w21_a30
  have w22_1320 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m22]; exact w21_1320
  have w22_1324 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m22]; exact w21_1324
  have w22_1328 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m22]; exact w21_1328
  have b22_a20 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m22]; exact b21_a20
  have b22_a34 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m22]; exact b21_a34
  clear w21_1328 b21_a34 b21_a20 w21_1324 w21_1320 w21_a30 w21_a2c w21_a28 w21_a24 w21_184 w21_180 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_12 g21_11 g21_10 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 rg21 W21 K21 fr21 s21 d21
  -- 0x496: sw
  obtain ⟨n23, d23, s23, fr23, K23, W23, rg23⟩ := sv_sw F E22 s22 sv_at_496 (off' := 0x498) (c := 0x132C)
    (by decide) (by rw [g22_12]; sv_addr) (by decide) (by decide)
  have t23 : Steps n0 n23 := t22.trans d23
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.keep K23 (by decide)
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [rg23 sp, g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg23 (3 : Fin 32), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg23 (4 : Fin 32), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg23 (8 : Fin 32), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = x9 := by rw [rg23 (9 : Fin 32), g22_9]
  have g23_10 : reg n23 a0 = BitVec.ofNat 32 0x1320 := by rw [rg23 a0, g22_10]
  have g23_11 : reg n23 a1 = BitVec.ofNat 32 tl9.len := by rw [rg23 a1, g22_11]
  have g23_12 : reg n23 a2 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg23 a2, g22_12]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [rg23 (18 : Fin 32), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [rg23 (19 : Fin 32), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg23 (20 : Fin 32), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = kp := by rw [rg23 (21 : Fin 32), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = x22 := by rw [rg23 (22 : Fin 32), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = x23 := by rw [rg23 (23 : Fin 32), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = x24 := by rw [rg23 (24 : Fin 32), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = x25 := by rw [rg23 (25 : Fin 32), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = ll := by rw [rg23 (26 : Fin 32), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg23 (27 : Fin 32), g22_27]
  have w23_180 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K23.w32 (by decide) (by decide)).trans w22_180
  have w23_184 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K23.w32 (by decide) (by decide)).trans w22_184
  have w23_a24 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (rp) + BitVec.ofNat 32 tl9.header := (K23.w32 (by decide) (by decide)).trans w22_a24
  have w23_a28 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl9.len := (K23.w32 (by decide) (by decide)).trans w22_a28
  have w23_a2c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = rp := (K23.w32 (by decide) (by decide)).trans w22_a2c
  have w23_a30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl9.header + tl9.len) := (K23.w32 (by decide) (by decide)).trans w22_a30
  have w23_1320 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := (K23.w32 (by decide) (by decide)).trans w22_1320
  have w23_1324 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := (K23.w32 (by decide) (by decide)).trans w22_1324
  have w23_1328 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = (rp) + BitVec.ofNat 32 tl9.header := (K23.w32 (by decide) (by decide)).trans w22_1328
  have b23_a20 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := (K23.b8 (by decide) (by decide)).trans b22_a20
  have b23_a34 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := (K23.b8 (by decide) (by decide)).trans b22_a34
  have w23_132c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = BitVec.ofNat 32 tl9.len := by rw [W23, g22_11]
  clear b22_a34 b22_a20 w22_1328 w22_1324 w22_1320 w22_a30 w22_a2c w22_a28 w22_a24 w22_184 w22_180 g22_10 g22_8 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_12 g22_11 g22_9 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 rb22 s22 m22 u22 c22
  -- 0x498
  obtain ⟨n24, c24, u24⟩ := s23.block svL6498 E23.self svL6498_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have s24 : St n24.mem SV n24 0x4AC (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have rb24 : ∀ q, reg n24 q = (runBlock svL6498 (n23.mem, reg n23)).2 q := fun q => by rw [u24.regs]
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
  have g24_8 : reg n24 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb24, runBlock_reg _ _ _ (8 : Fin 32) s23.zero (by decide), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = x9 := by
    rw [rb24, runBlock_reg _ _ _ (9 : Fin 32) s23.zero (by decide), g23_9]
  have g24_18 : reg n24 (18 : Fin 32) = out := by
    rw [rb24, runBlock_reg _ _ _ (18 : Fin 32) s23.zero (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by
    rw [rb24, runBlock_reg _ _ _ (19 : Fin 32) s23.zero (by decide), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb24, runBlock_reg _ _ _ (20 : Fin 32) s23.zero (by decide), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = kp := by
    rw [rb24, runBlock_reg _ _ _ (21 : Fin 32) s23.zero (by decide), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = x22 := by
    rw [rb24, runBlock_reg _ _ _ (22 : Fin 32) s23.zero (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = x23 := by
    rw [rb24, runBlock_reg _ _ _ (23 : Fin 32) s23.zero (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = x24 := by
    rw [rb24, runBlock_reg _ _ _ (24 : Fin 32) s23.zero (by decide), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = x25 := by
    rw [rb24, runBlock_reg _ _ _ (25 : Fin 32) s23.zero (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = ll := by
    rw [rb24, runBlock_reg _ _ _ (26 : Fin 32) s23.zero (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb24, runBlock_reg _ _ _ (27 : Fin 32) s23.zero (by decide), g23_27]
  have g24_10 : reg n24 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svL6498, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_10, g23_11, g23_12, g23_18, g23_19, g23_20, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g24_11 : reg n24 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svL6498, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_10, g23_11, g23_12, g23_18, g23_19, g23_20, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g24_12 : reg n24 a2 = BitVec.ofNat 32 0x30 := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svL6498, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g23_2, g23_3, g23_4, g23_8, g23_9, g23_10, g23_11, g23_12, g23_18, g23_19, g23_20, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, s23.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w24_180 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m24]; exact w23_180
  have w24_184 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m24]; exact w23_184
  have w24_a24 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m24]; exact w23_a24
  have w24_a28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl9.len := by rw [m24]; exact w23_a28
  have w24_a2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = rp := by rw [m24]; exact w23_a2c
  have w24_a30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m24]; exact w23_a30
  have w24_1320 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m24]; exact w23_1320
  have w24_1324 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m24]; exact w23_1324
  have w24_1328 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m24]; exact w23_1328
  have w24_132c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = BitVec.ofNat 32 tl9.len := by rw [m24]; exact w23_132c
  have b24_a20 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m24]; exact b23_a20
  have b24_a34 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m24]; exact b23_a34
  clear w23_132c b23_a34 b23_a20 w23_1328 w23_1324 w23_1320 w23_a30 w23_a2c w23_a28 w23_a24 w23_184 w23_180 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_12 g23_11 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 rg23 W23 K23 fr23 s23 d23
  -- 0x4AC: sv_elemF
  obtain ⟨n25, c25, s25, rk25, K25, Ok25, Er25, fr25⟩ := sv_elemF (oc := 0xA20) (dc := 0x1320) (tag := 0x30)
    F E24 s24 sv_at_4ac sv_at_4b0 (by decide) (by decide) g24_10 g24_11 g24_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w24_1328 w24_132c
  have t25 : Steps n0 n25 := t24.trans c25
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.keepL K25 (by decide)
  rw [sv_mb fR24 (tb_in.contentW (opt_ok_elem hr9))] at Ok25 Er25
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [rk25 sp (by decide) (by decide), g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk25 (3 : Fin 32) (by decide) (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk25 (4 : Fin 32) (by decide) (by decide), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rk25 (8 : Fin 32) (by decide) (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = x9 := by rw [rk25 (9 : Fin 32) (by decide) (by decide), g24_9]
  have g25_10 : reg n25 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk25 a0 (by decide) (by decide), g24_10]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [rk25 (18 : Fin 32) (by decide) (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [rk25 (19 : Fin 32) (by decide) (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rk25 (20 : Fin 32) (by decide) (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = kp := by rw [rk25 (21 : Fin 32) (by decide) (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = x22 := by rw [rk25 (22 : Fin 32) (by decide) (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = x23 := by rw [rk25 (23 : Fin 32) (by decide) (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = x24 := by rw [rk25 (24 : Fin 32) (by decide) (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = x25 := by rw [rk25 (25 : Fin 32) (by decide) (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = ll := by rw [rk25 (26 : Fin 32) (by decide) (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk25 (27 : Fin 32) (by decide) (by decide), g24_27]
  obtain ⟨r25, hr25⟩ : ∃ r, derElement 0x30 (memBytes M0 ((rp) + BitVec.ofNat 32 tl9.header) (BitVec.ofNat 32 tl9.len).toNat) = r := ⟨_, rfl⟩
  rcases r25 with er25 | tl25
  · obtain ⟨zhr25, -⟩ := Er25 er25 hr25
    have w25_180 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K25.w32 (by decide) (by decide)).trans w24_180
    have w25_184 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K25.w32 (by decide) (by decide)).trans w24_184
    have w25_1320 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := (K25.w32 (by decide) (by decide)).trans w24_1320
    have w25_1324 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := (K25.w32 (by decide) (by decide)).trans w24_1324
    have b25_a34 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := (K25.b8 (by decide) (by decide)).trans b24_a34
    have w25_a20 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := zhr25
    clear b24_a34 b24_a20 w24_132c w24_1328 w24_1324 w24_1320 w24_a30 w24_a2c w24_a28 w24_a24 w24_184 w24_180 g24_12 g24_11 g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
    -- 0x4B4: lw
    obtain ⟨n26, d26, u26⟩ := s25.lw E25.self sv_at_4b4 (off' := 0x4B8) (by decide)
      (by rw [g25_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s26 : St n26.mem SV n26 0x4B8 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
    have m26 : n26.mem = n25.mem := u26.mem
    have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
    have t26 : Steps n0 n26 := t25.trans (.single d26)
    have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
    have E26 : SvCode n26.mem := E25.fr F fr26
    have V26 : SvSaves B n26.mem v := V25.same m26
    have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_2]
    have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_3]
    have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_4]
    have g26_8 : reg n26 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_8]
    have g26_9 : reg n26 (9 : Fin 32) = x9 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_9]
    have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, upd_ne (by decide) (by decide), g25_18]
    have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_19]
    have g26_20 : reg n26 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_20]
    have g26_21 : reg n26 (21 : Fin 32) = kp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_21]
    have g26_22 : reg n26 (22 : Fin 32) = x22 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_22]
    have g26_23 : reg n26 (23 : Fin 32) = x23 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_23]
    have g26_24 : reg n26 (24 : Fin 32) = x24 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_24]
    have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_25]
    have g26_26 : reg n26 (26 : Fin 32) = ll := by rw [u26.regs, upd_ne (by decide) (by decide), g25_26]
    have g26_27 : reg n26 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_27]
    have g26_10 : reg n26 a0 = 0 := by
      rw [u26.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g25_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w25_a20]
    have w26_180 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m26]; exact w25_180
    have w26_184 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m26]; exact w25_184
    have w26_a20 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m26]; exact w25_a20
    have w26_1320 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m26]; exact w25_1320
    have w26_1324 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m26]; exact w25_1324
    have b26_a34 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m26]; exact b25_a34
    clear w25_a20 b25_a34 w25_1324 w25_1320 w25_184 w25_180 zhr25
    -- 0x4B8: branch, taken
    obtain ⟨n27, d27, u27⟩ := s26.taken E26.self 0x962 sv_at_4b8
      (by decide) (by rw [g26_10, s26.zero]; rfl)
    have s27 : St n27.mem SV n27 0x962 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
    have m27 : n27.mem = n26.mem := u27.mem
    have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
    have t27 : Steps n0 n27 := t26.trans (.single d27)
    have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
    have E27 : SvCode n27.mem := E26.fr F fr27
    have V27 : SvSaves B n27.mem v := V26.same m27
    have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, g26_2]
    have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, g26_3]
    have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, g26_4]
    have g27_8 : reg n27 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u27.regs, g26_8]
    have g27_9 : reg n27 (9 : Fin 32) = x9 := by rw [u27.regs, g26_9]
    have g27_10 : reg n27 a0 = 0 := by rw [u27.regs, g26_10]
    have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, g26_18]
    have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, g26_19]
    have g27_20 : reg n27 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u27.regs, g26_20]
    have g27_21 : reg n27 (21 : Fin 32) = kp := by rw [u27.regs, g26_21]
    have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [u27.regs, g26_22]
    have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [u27.regs, g26_23]
    have g27_24 : reg n27 (24 : Fin 32) = x24 := by rw [u27.regs, g26_24]
    have g27_25 : reg n27 (25 : Fin 32) = x25 := by rw [u27.regs, g26_25]
    have g27_26 : reg n27 (26 : Fin 32) = ll := by rw [u27.regs, g26_26]
    have g27_27 : reg n27 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u27.regs, g26_27]
    have w27_180 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m27]; exact w26_180
    have w27_184 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m27]; exact w26_184
    have w27_a20 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m27]; exact w26_a20
    have w27_1320 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m27]; exact w26_1320
    have w27_1324 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m27]; exact w26_1324
    have b27_a34 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m27]; exact b26_a34
    clear b26_a34 w26_1324 w26_1320 w26_a20 w26_184 w26_180 g26_10 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
    -- 0x962: lbu
    obtain ⟨n28, d28, u28⟩ := s27.lbu E27.self sv_at_962 (off' := 0x966) (by decide)
    have s28 : St n28.mem SV n28 0x966 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
    have m28 : n28.mem = n27.mem := u28.mem
    have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
    have t28 : Steps n0 n28 := t27.trans (.single d28)
    have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
    have E28 : SvCode n28.mem := E27.fr F fr28
    have V28 : SvSaves B n28.mem v := V27.same m28
    have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_2]
    have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_3]
    have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_4]
    have g28_8 : reg n28 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_8]
    have g28_9 : reg n28 (9 : Fin 32) = x9 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_9]
    have g28_10 : reg n28 a0 = 0 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_10]
    have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, upd_ne (by decide) (by decide), g27_18]
    have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_19]
    have g28_21 : reg n28 (21 : Fin 32) = kp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_21]
    have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_22]
    have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_23]
    have g28_24 : reg n28 (24 : Fin 32) = x24 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_24]
    have g28_25 : reg n28 (25 : Fin 32) = x25 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_25]
    have g28_26 : reg n28 (26 : Fin 32) = ll := by rw [u28.regs, upd_ne (by decide) (by decide), g27_26]
    have g28_27 : reg n28 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_27]
    have w28_180 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m28]; exact w27_180
    have w28_184 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m28]; exact w27_184
    have w28_a20 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m28]; exact w27_a20
    have w28_1320 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m28]; exact w27_1320
    have w28_1324 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m28]; exact w27_1324
    have b28_a34 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m28]; exact b27_a34
    clear b27_a34 w27_1324 w27_1320 w27_a20 w27_184 w27_180 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_10 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
    exact .inl ⟨(fun ⟨h0', h1', tl9', h2', h3', tl25', h4', _⟩ => by rw [hr9] at h2'; cases h2'; rw [hr25] at h4'; cases h4'), sv_fail F E28 s28 t28 (fun x hx => (fR28 x hx).trans (fM x hx).symm) V28 hret g28_2 g28_18 hO g28_3 g28_4⟩
  obtain ⟨o0_25, o4_25, o8_25, o12_25, o16_25, d8_25, d12_25⟩ := Ok25 tl25 hr25
  have w25_180 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K25.w32 (by decide) (by decide)).trans w24_180
  have w25_184 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K25.w32 (by decide) (by decide)).trans w24_184
  have w25_1320 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := (K25.w32 (by decide) (by decide)).trans w24_1320
  have w25_1324 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := (K25.w32 (by decide) (by decide)).trans w24_1324
  have b25_a34 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := (K25.b8 (by decide) (by decide)).trans b24_a34
  have w25_a20 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := o0_25
  have w25_a24 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := o4_25
  have w25_a28 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 tl9.header := o8_25
  have w25_a2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := o12_25
  have w25_1328 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := d8_25
  have w25_132c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := d12_25
  have b25_a30 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := o16_25
  clear b24_a34 b24_a20 w24_132c w24_1328 w24_1324 w24_1320 w24_a30 w24_a2c w24_a28 w24_a24 w24_184 w24_180 g24_12 g24_11 g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
  -- 0x4B4: lw
  obtain ⟨n26, d26, u26⟩ := s25.lw E25.self sv_at_4b4 (off' := 0x4B8) (by decide)
    (by rw [g25_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s26 : St n26.mem SV n26 0x4B8 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans (.single d26)
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = x9 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_9]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, upd_ne (by decide) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = kp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = x22 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = x23 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = x24 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = ll := by rw [u26.regs, upd_ne (by decide) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_27]
  have g26_10 : reg n26 a0 = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by
    rw [u26.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g25_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w25_a20]
  have w26_180 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m26]; exact w25_180
  have w26_184 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m26]; exact w25_184
  have w26_a20 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m26]; exact w25_a20
  have w26_a24 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m26]; exact w25_a24
  have w26_a28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m26]; exact w25_a28
  have w26_a2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m26]; exact w25_a2c
  have w26_1320 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m26]; exact w25_1320
  have w26_1324 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m26]; exact w25_1324
  have w26_1328 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m26]; exact w25_1328
  have w26_132c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m26]; exact w25_132c
  have b26_a30 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := by rw [m26]; exact b25_a30
  have b26_a34 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m26]; exact b25_a34
  clear b25_a30 w25_132c w25_1328 w25_a2c w25_a28 w25_a24 w25_a20 b25_a34 w25_1324 w25_1320 w25_184 w25_180 d12_25 d8_25 o16_25 o12_25 o8_25 o4_25 o0_25 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_10 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 Er25 Ok25 K25 rk25 s25 c25
  -- 0x4B8: branch, not taken
  obtain ⟨n27, d27, u27⟩ := s26.notTaken E26.self 0x4BC sv_at_4b8
    (by decide) (by rw [g26_10, s26.zero]; exact br_beq_f ((tb_in.contentW (opt_ok_elem hr9)).ok_ne hr25))
  have s27 : St n27.mem SV n27 0x4BC (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans (.single d27)
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u27.regs, g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = x9 := by rw [u27.regs, g26_9]
  have g27_10 : reg n27 a0 = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [u27.regs, g26_10]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u27.regs, g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = kp := by rw [u27.regs, g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [u27.regs, g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [u27.regs, g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = x24 := by rw [u27.regs, g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = x25 := by rw [u27.regs, g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = ll := by rw [u27.regs, g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u27.regs, g26_27]
  have w27_180 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m27]; exact w26_180
  have w27_184 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m27]; exact w26_184
  have w27_a20 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m27]; exact w26_a20
  have w27_a24 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m27]; exact w26_a24
  have w27_a28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m27]; exact w26_a28
  have w27_a2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m27]; exact w26_a2c
  have w27_1320 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m27]; exact w26_1320
  have w27_1324 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m27]; exact w26_1324
  have w27_1328 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m27]; exact w26_1328
  have w27_132c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m27]; exact w26_132c
  have b27_a30 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := by rw [m27]; exact b26_a30
  have b27_a34 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m27]; exact b26_a34
  clear b26_a34 b26_a30 w26_132c w26_1328 w26_1324 w26_1320 w26_a2c w26_a28 w26_a24 w26_a20 w26_184 w26_180 g26_10 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
  -- 0x4BC: lw
  obtain ⟨n28, d28, u28⟩ := s27.lw E27.self sv_at_4bc (off' := 0x4BE) (by decide)
    (by rw [g27_8, show B + 0x21A0 + BitVec.ofNat 32 0x1320 + 0xC = B + 0x21A0 + BitVec.ofNat 32 0x132C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s28 : St n28.mem SV n28 0x4BE (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
  have t28 : Steps n0 n28 := t27.trans (.single d28)
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.same m28
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = x9 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_9]
  have g28_10 : reg n28 a0 = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [u28.regs, upd_ne (by decide) (by decide), g27_10]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, upd_ne (by decide) (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = kp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = x24 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = x25 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = ll := by rw [u28.regs, upd_ne (by decide) (by decide), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_27]
  have g28_11 : reg n28 a1 = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by
    rw [u28.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g27_8, show B + 0x21A0 + BitVec.ofNat 32 0x1320 + 0xC = B + 0x21A0 + BitVec.ofNat 32 0x132C by sv_addr, w27_132c]
  have w28_180 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m28]; exact w27_180
  have w28_184 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m28]; exact w27_184
  have w28_a20 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m28]; exact w27_a20
  have w28_a24 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m28]; exact w27_a24
  have w28_a28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m28]; exact w27_a28
  have w28_a2c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m28]; exact w27_a2c
  have w28_1320 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m28]; exact w27_1320
  have w28_1324 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m28]; exact w27_1324
  have w28_1328 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m28]; exact w27_1328
  have w28_132c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m28]; exact w27_132c
  have b28_a30 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := by rw [m28]; exact b27_a30
  have b28_a34 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m28]; exact b27_a34
  clear b27_a34 b27_a30 w27_132c w27_1328 w27_1324 w27_1320 w27_a2c w27_a28 w27_a24 w27_a20 w27_184 w27_180 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_10 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
  by_cases hz_28 : (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) = 0
  rotate_left
  · -- 0x4BE: branch, taken
    obtain ⟨n29, d29, u29⟩ := s28.taken E28.self 0x1C0 sv_at_4be
      (by decide) (by rw [g28_11, s28.zero]; exact br_bne_t hz_28)
    have s29 : St n29.mem SV n29 0x1C0 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
    have t29 : Steps n0 n29 := t28.trans (.single d29)
    have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
    have E29 : SvCode n29.mem := E28.fr F fr29
    have V29 : SvSaves B n29.mem v := V28.same m29
    have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, g28_2]
    have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, g28_3]
    have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, g28_4]
    have g29_8 : reg n29 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u29.regs, g28_8]
    have g29_9 : reg n29 (9 : Fin 32) = x9 := by rw [u29.regs, g28_9]
    have g29_10 : reg n29 a0 = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [u29.regs, g28_10]
    have g29_11 : reg n29 a1 = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [u29.regs, g28_11]
    have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, g28_19]
    have g29_20 : reg n29 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u29.regs, g28_20]
    have g29_21 : reg n29 (21 : Fin 32) = kp := by rw [u29.regs, g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = x22 := by rw [u29.regs, g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = x23 := by rw [u29.regs, g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = x24 := by rw [u29.regs, g28_24]
    have g29_25 : reg n29 (25 : Fin 32) = x25 := by rw [u29.regs, g28_25]
    have g29_26 : reg n29 (26 : Fin 32) = ll := by rw [u29.regs, g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u29.regs, g28_27]
    have w29_180 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_180
    have w29_184 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_184
    have w29_a20 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m29]; exact w28_a20
    have w29_a24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m29]; exact w28_a24
    have w29_a28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m29]; exact w28_a28
    have w29_a2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m29]; exact w28_a2c
    have w29_1320 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m29]; exact w28_1320
    have w29_1324 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m29]; exact w28_1324
    have w29_1328 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m29]; exact w28_1328
    have w29_132c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m29]; exact w28_132c
    have b29_a30 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := by rw [m29]; exact b28_a30
    have b29_a34 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m29]; exact b28_a34
    clear b28_a34 b28_a30 w28_132c w28_1328 w28_1324 w28_1320 w28_a2c w28_a28 w28_a24 w28_a20 w28_184 w28_180 g28_11 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_10 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
    -- 0x1C0
    obtain ⟨n30, c30, u30⟩ := s29.block svL61c0 E29.self svL61c0_end
      ⟨trivial, trivial⟩
    have m30 : n30.mem = n29.mem := u30.mem
    have s30 : St n30.mem SV n30 0x1C2 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
    have rb30 : ∀ q, reg n30 q = (runBlock svL61c0 (n29.mem, reg n29)).2 q := fun q => by rw [u30.regs]
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
    have g30_8 : reg n30 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
      rw [rb30, runBlock_reg _ _ _ (8 : Fin 32) s29.zero (by decide), g29_8]
    have g30_9 : reg n30 (9 : Fin 32) = x9 := by
      rw [rb30, runBlock_reg _ _ _ (9 : Fin 32) s29.zero (by decide), g29_9]
    have g30_10 : reg n30 a0 = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by
      rw [rb30, runBlock_reg _ _ _ a0 s29.zero (by decide), g29_10]
    have g30_11 : reg n30 a1 = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by
      rw [rb30, runBlock_reg _ _ _ a1 s29.zero (by decide), g29_11]
    have g30_18 : reg n30 (18 : Fin 32) = out := by
      rw [rb30, runBlock_reg _ _ _ (18 : Fin 32) s29.zero (by decide), g29_18]
    have g30_19 : reg n30 (19 : Fin 32) = bp := by
      rw [rb30, runBlock_reg _ _ _ (19 : Fin 32) s29.zero (by decide), g29_19]
    have g30_21 : reg n30 (21 : Fin 32) = kp := by
      rw [rb30, runBlock_reg _ _ _ (21 : Fin 32) s29.zero (by decide), g29_21]
    have g30_22 : reg n30 (22 : Fin 32) = x22 := by
      rw [rb30, runBlock_reg _ _ _ (22 : Fin 32) s29.zero (by decide), g29_22]
    have g30_23 : reg n30 (23 : Fin 32) = x23 := by
      rw [rb30, runBlock_reg _ _ _ (23 : Fin 32) s29.zero (by decide), g29_23]
    have g30_24 : reg n30 (24 : Fin 32) = x24 := by
      rw [rb30, runBlock_reg _ _ _ (24 : Fin 32) s29.zero (by decide), g29_24]
    have g30_25 : reg n30 (25 : Fin 32) = x25 := by
      rw [rb30, runBlock_reg _ _ _ (25 : Fin 32) s29.zero (by decide), g29_25]
    have g30_26 : reg n30 (26 : Fin 32) = ll := by
      rw [rb30, runBlock_reg _ _ _ (26 : Fin 32) s29.zero (by decide), g29_26]
    have g30_27 : reg n30 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb30, runBlock_reg _ _ _ (27 : Fin 32) s29.zero (by decide), g29_27]
    have g30_20 : reg n30 (20 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb30]; simp +decide only [runBlock, BInstr.run, svL61c0, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g29_2, g29_3, g29_4, g29_8, g29_9, g29_10, g29_11, g29_18, g29_19, g29_20, g29_21, g29_22, g29_23, g29_24, g29_25, g29_26, g29_27, s29.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have w30_180 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m30]; exact w29_180
    have w30_184 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m30]; exact w29_184
    have w30_a20 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m30]; exact w29_a20
    have w30_a24 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m30]; exact w29_a24
    have w30_a28 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m30]; exact w29_a28
    have w30_a2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m30]; exact w29_a2c
    have w30_1320 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m30]; exact w29_1320
    have w30_1324 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m30]; exact w29_1324
    have w30_1328 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m30]; exact w29_1328
    have w30_132c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m30]; exact w29_132c
    have b30_a30 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := by rw [m30]; exact b29_a30
    have b30_a34 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m30]; exact b29_a34
    clear b29_a34 b29_a30 w29_132c w29_1328 w29_1324 w29_1320 w29_a2c w29_a28 w29_a24 w29_a20 w29_184 w29_180 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_11 g29_10 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
    -- 0x1C2: j
    obtain ⟨n31, d31, u31⟩ := s30.jump E30.self sv_at_1c2 (off' := 0x966) (by decide)
      (by rw [s30.pc]; decide)
    have s31 : St n31.mem SV n31 0x966 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
    have m31 : n31.mem = n30.mem := u31.mem
    have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
    have t31 : Steps n0 n31 := t30.trans (.single d31)
    have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
    have E31 : SvCode n31.mem := E30.fr F fr31
    have V31 : SvSaves B n31.mem v := V30.same m31
    have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, g30_2]
    have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, g30_3]
    have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, g30_4]
    have g31_8 : reg n31 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u31.regs, g30_8]
    have g31_9 : reg n31 (9 : Fin 32) = x9 := by rw [u31.regs, g30_9]
    have g31_10 : reg n31 a0 = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [u31.regs, g30_10]
    have g31_11 : reg n31 a1 = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [u31.regs, g30_11]
    have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, g30_18]
    have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, g30_19]
    have g31_20 : reg n31 (20 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u31.regs, g30_20]
    have g31_21 : reg n31 (21 : Fin 32) = kp := by rw [u31.regs, g30_21]
    have g31_22 : reg n31 (22 : Fin 32) = x22 := by rw [u31.regs, g30_22]
    have g31_23 : reg n31 (23 : Fin 32) = x23 := by rw [u31.regs, g30_23]
    have g31_24 : reg n31 (24 : Fin 32) = x24 := by rw [u31.regs, g30_24]
    have g31_25 : reg n31 (25 : Fin 32) = x25 := by rw [u31.regs, g30_25]
    have g31_26 : reg n31 (26 : Fin 32) = ll := by rw [u31.regs, g30_26]
    have g31_27 : reg n31 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u31.regs, g30_27]
    have w31_180 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m31]; exact w30_180
    have w31_184 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m31]; exact w30_184
    have w31_a20 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m31]; exact w30_a20
    have w31_a24 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m31]; exact w30_a24
    have w31_a28 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m31]; exact w30_a28
    have w31_a2c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m31]; exact w30_a2c
    have w31_1320 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m31]; exact w30_1320
    have w31_1324 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m31]; exact w30_1324
    have w31_1328 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m31]; exact w30_1328
    have w31_132c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m31]; exact w30_132c
    have b31_a30 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := by rw [m31]; exact b30_a30
    have b31_a34 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m31]; exact b30_a34
    clear b30_a34 b30_a30 w30_132c w30_1328 w30_1324 w30_1320 w30_a2c w30_a28 w30_a24 w30_a20 w30_184 w30_180 g30_20 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_19 g30_18 g30_11 g30_10 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 rb30 s30 m30 u30 c30
    exact .inl ⟨(fun ⟨h0', h1', tl9', h2', h3', tl25', h4', h5', _⟩ => by rw [hr9] at h2'; cases h2'; rw [hr25] at h4'; cases h4'; exact hz_28 h5'), sv_fail F E31 s31 t31 (fun x hx => (fR31 x hx).trans (fM x hx).symm) V31 hret g31_2 g31_18 hO g31_3 g31_4⟩
  -- 0x4BE: branch, not taken
  obtain ⟨n29, d29, u29⟩ := s28.notTaken E28.self 0x4C2 sv_at_4be
    (by decide) (by rw [g28_11, s28.zero]; exact br_bne_f hz_28)
  have s29 : St n29.mem SV n29 0x4C2 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans (.single d29)
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u29.regs, g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = x9 := by rw [u29.regs, g28_9]
  have g29_10 : reg n29 a0 = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [u29.regs, g28_10]
  have g29_11 : reg n29 a1 = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [u29.regs, g28_11]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u29.regs, g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = kp := by rw [u29.regs, g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = x22 := by rw [u29.regs, g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = x23 := by rw [u29.regs, g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = x24 := by rw [u29.regs, g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = x25 := by rw [u29.regs, g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = ll := by rw [u29.regs, g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u29.regs, g28_27]
  have w29_180 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_180
  have w29_184 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m29]; exact w28_184
  have w29_a20 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m29]; exact w28_a20
  have w29_a24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m29]; exact w28_a24
  have w29_a28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m29]; exact w28_a28
  have w29_a2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m29]; exact w28_a2c
  have w29_1320 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m29]; exact w28_1320
  have w29_1324 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m29]; exact w28_1324
  have w29_1328 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m29]; exact w28_1328
  have w29_132c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m29]; exact w28_132c
  have b29_a30 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := by rw [m29]; exact b28_a30
  have b29_a34 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m29]; exact b28_a34
  clear b28_a34 b28_a30 w28_132c w28_1328 w28_1324 w28_1320 w28_a2c w28_a28 w28_a24 w28_a20 w28_184 w28_180 g28_11 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_10 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
  -- 0x4C2: lw
  obtain ⟨n30, d30, u30⟩ := s29.lw E29.self sv_at_4c2 (off' := 0x4C6) (by decide)
    (by rw [g29_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s30 : St n30.mem SV n30 0x4C6 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
  have t30 : Steps n0 n30 := t29.trans (.single d30)
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.same m30
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = x9 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_9]
  have g30_10 : reg n30 a0 = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [u30.regs, upd_ne (by decide) (by decide), g29_10]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, upd_ne (by decide) (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, upd_ne (by decide) (by decide), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = kp := by rw [u30.regs, upd_ne (by decide) (by decide), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = x22 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = x23 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = x24 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = x25 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = ll := by rw [u30.regs, upd_ne (by decide) (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_27]
  have g30_11 : reg n30 a1 = BitVec.ofNat 32 tl25.len := by
    rw [u30.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g29_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr, w29_a24]
  have w30_180 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m30]; exact w29_180
  have w30_184 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m30]; exact w29_184
  have w30_a20 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m30]; exact w29_a20
  have w30_a24 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m30]; exact w29_a24
  have w30_a28 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m30]; exact w29_a28
  have w30_a2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m30]; exact w29_a2c
  have w30_1320 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m30]; exact w29_1320
  have w30_1324 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m30]; exact w29_1324
  have w30_1328 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m30]; exact w29_1328
  have w30_132c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m30]; exact w29_132c
  have b30_a30 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := by rw [m30]; exact b29_a30
  have b30_a34 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m30]; exact b29_a34
  clear b29_a34 b29_a30 w29_132c w29_1328 w29_1324 w29_1320 w29_a2c w29_a28 w29_a24 w29_a20 w29_184 w29_180 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_11 g29_10 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
  -- 0x4C6: sw
  obtain ⟨n31, d31, s31, fr31, K31, W31, rg31⟩ := sv_sw F E30 s30 sv_at_4c6 (off' := 0x4C8) (c := 0x88)
    (by decide) (by rw [g30_2]; sv_addr) (by decide) (by decide)
  have t31 : Steps n0 n31 := t30.trans d31
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.keep K31 (by decide)
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [rg31 sp, g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg31 (3 : Fin 32), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg31 (4 : Fin 32), g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg31 (8 : Fin 32), g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = x9 := by rw [rg31 (9 : Fin 32), g30_9]
  have g31_10 : reg n31 a0 = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [rg31 a0, g30_10]
  have g31_11 : reg n31 a1 = BitVec.ofNat 32 tl25.len := by rw [rg31 a1, g30_11]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [rg31 (18 : Fin 32), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [rg31 (19 : Fin 32), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg31 (20 : Fin 32), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = kp := by rw [rg31 (21 : Fin 32), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = x22 := by rw [rg31 (22 : Fin 32), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = x23 := by rw [rg31 (23 : Fin 32), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = x24 := by rw [rg31 (24 : Fin 32), g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = x25 := by rw [rg31 (25 : Fin 32), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = ll := by rw [rg31 (26 : Fin 32), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg31 (27 : Fin 32), g30_27]
  have w31_180 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K31.w32 (by decide) (by decide)).trans w30_180
  have w31_184 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K31.w32 (by decide) (by decide)).trans w30_184
  have w31_a20 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K31.w32 (by decide) (by decide)).trans w30_a20
  have w31_a24 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := (K31.w32 (by decide) (by decide)).trans w30_a24
  have w31_a28 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 tl9.header := (K31.w32 (by decide) (by decide)).trans w30_a28
  have w31_a2c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := (K31.w32 (by decide) (by decide)).trans w30_a2c
  have w31_1320 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := (K31.w32 (by decide) (by decide)).trans w30_1320
  have w31_1324 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := (K31.w32 (by decide) (by decide)).trans w30_1324
  have w31_1328 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := (K31.w32 (by decide) (by decide)).trans w30_1328
  have w31_132c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := (K31.w32 (by decide) (by decide)).trans w30_132c
  have b31_a30 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := (K31.b8 (by decide) (by decide)).trans b30_a30
  have b31_a34 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := (K31.b8 (by decide) (by decide)).trans b30_a34
  have w31_88 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [W31, g30_10]
  clear b30_a34 b30_a30 w30_132c w30_1328 w30_1324 w30_1320 w30_a2c w30_a28 w30_a24 w30_a20 w30_184 w30_180 g30_11 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_10 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30
  -- 0x4C8: sw
  obtain ⟨n32, d32, s32, fr32, K32, W32, rg32⟩ := sv_sw F E31 s31 sv_at_4c8 (off' := 0x4CA) (c := 0x8C)
    (by decide) (by rw [g31_2]; sv_addr) (by decide) (by decide)
  have t32 : Steps n0 n32 := t31.trans d32
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.keep K32 (by decide)
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [rg32 sp, g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg32 (3 : Fin 32), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg32 (4 : Fin 32), g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg32 (8 : Fin 32), g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = x9 := by rw [rg32 (9 : Fin 32), g31_9]
  have g32_10 : reg n32 a0 = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [rg32 a0, g31_10]
  have g32_11 : reg n32 a1 = BitVec.ofNat 32 tl25.len := by rw [rg32 a1, g31_11]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [rg32 (18 : Fin 32), g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [rg32 (19 : Fin 32), g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg32 (20 : Fin 32), g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = kp := by rw [rg32 (21 : Fin 32), g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = x22 := by rw [rg32 (22 : Fin 32), g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = x23 := by rw [rg32 (23 : Fin 32), g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = x24 := by rw [rg32 (24 : Fin 32), g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = x25 := by rw [rg32 (25 : Fin 32), g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = ll := by rw [rg32 (26 : Fin 32), g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg32 (27 : Fin 32), g31_27]
  have w32_88 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K32.w32 (by decide) (by decide)).trans w31_88
  have w32_180 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K32.w32 (by decide) (by decide)).trans w31_180
  have w32_184 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K32.w32 (by decide) (by decide)).trans w31_184
  have w32_a20 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K32.w32 (by decide) (by decide)).trans w31_a20
  have w32_a24 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := (K32.w32 (by decide) (by decide)).trans w31_a24
  have w32_a28 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 tl9.header := (K32.w32 (by decide) (by decide)).trans w31_a28
  have w32_a2c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := (K32.w32 (by decide) (by decide)).trans w31_a2c
  have w32_1320 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := (K32.w32 (by decide) (by decide)).trans w31_1320
  have w32_1324 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := (K32.w32 (by decide) (by decide)).trans w31_1324
  have w32_1328 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := (K32.w32 (by decide) (by decide)).trans w31_1328
  have w32_132c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := (K32.w32 (by decide) (by decide)).trans w31_132c
  have b32_a30 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := (K32.b8 (by decide) (by decide)).trans b31_a30
  have b32_a34 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := (K32.b8 (by decide) (by decide)).trans b31_a34
  have w32_8c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := by rw [W32, g31_11]
  clear w31_88 b31_a34 b31_a30 w31_132c w31_1328 w31_1324 w31_1320 w31_a2c w31_a28 w31_a24 w31_a20 w31_184 w31_180 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_11 g31_10 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 rg31 W31 K31 fr31 s31 d31
  -- 0x4CA: sw
  obtain ⟨n33, d33, s33, fr33, K33, W33, rg33⟩ := sv_sw F E32 s32 sv_at_4ca (off' := 0x4CC) (c := 0x90)
    (by decide) (by rw [g32_2]; sv_addr) (by decide) (by decide)
  have t33 : Steps n0 n33 := t32.trans d33
  have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.keep K33 (by decide)
  have g33_2 : reg n33 sp = B + 0x21A0 := by rw [rg33 sp, g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg33 (3 : Fin 32), g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg33 (4 : Fin 32), g32_4]
  have g33_8 : reg n33 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg33 (8 : Fin 32), g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = x9 := by rw [rg33 (9 : Fin 32), g32_9]
  have g33_10 : reg n33 a0 = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [rg33 a0, g32_10]
  have g33_11 : reg n33 a1 = BitVec.ofNat 32 tl25.len := by rw [rg33 a1, g32_11]
  have g33_18 : reg n33 (18 : Fin 32) = out := by rw [rg33 (18 : Fin 32), g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [rg33 (19 : Fin 32), g32_19]
  have g33_20 : reg n33 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg33 (20 : Fin 32), g32_20]
  have g33_21 : reg n33 (21 : Fin 32) = kp := by rw [rg33 (21 : Fin 32), g32_21]
  have g33_22 : reg n33 (22 : Fin 32) = x22 := by rw [rg33 (22 : Fin 32), g32_22]
  have g33_23 : reg n33 (23 : Fin 32) = x23 := by rw [rg33 (23 : Fin 32), g32_23]
  have g33_24 : reg n33 (24 : Fin 32) = x24 := by rw [rg33 (24 : Fin 32), g32_24]
  have g33_25 : reg n33 (25 : Fin 32) = x25 := by rw [rg33 (25 : Fin 32), g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = ll := by rw [rg33 (26 : Fin 32), g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg33 (27 : Fin 32), g32_27]
  have w33_88 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K33.w32 (by decide) (by decide)).trans w32_88
  have w33_8c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := (K33.w32 (by decide) (by decide)).trans w32_8c
  have w33_180 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K33.w32 (by decide) (by decide)).trans w32_180
  have w33_184 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K33.w32 (by decide) (by decide)).trans w32_184
  have w33_a20 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K33.w32 (by decide) (by decide)).trans w32_a20
  have w33_a24 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := (K33.w32 (by decide) (by decide)).trans w32_a24
  have w33_a28 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 tl9.header := (K33.w32 (by decide) (by decide)).trans w32_a28
  have w33_a2c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := (K33.w32 (by decide) (by decide)).trans w32_a2c
  have w33_1320 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := (K33.w32 (by decide) (by decide)).trans w32_1320
  have w33_1324 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := (K33.w32 (by decide) (by decide)).trans w32_1324
  have w33_1328 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := (K33.w32 (by decide) (by decide)).trans w32_1328
  have w33_132c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := (K33.w32 (by decide) (by decide)).trans w32_132c
  have b33_a30 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := (K33.b8 (by decide) (by decide)).trans b32_a30
  have b33_a34 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := (K33.b8 (by decide) (by decide)).trans b32_a34
  have w33_90 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [W33, g32_10]
  clear w32_8c b32_a34 b32_a30 w32_132c w32_1328 w32_1324 w32_1320 w32_a2c w32_a28 w32_a24 w32_a20 w32_184 w32_180 w32_88 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_11 g32_10 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 rg32 W32 K32 fr32 s32 d32
  -- 0x4CC: sw
  obtain ⟨n34, d34, s34, fr34, K34, W34, rg34⟩ := sv_sw F E33 s33 sv_at_4cc (off' := 0x4CE) (c := 0x40)
    (by decide) (by rw [g33_2]; sv_addr) (by decide) (by decide)
  have t34 : Steps n0 n34 := t33.trans d34
  have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.keep K34 (by decide)
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [rg34 sp, g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg34 (3 : Fin 32), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg34 (4 : Fin 32), g33_4]
  have g34_8 : reg n34 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg34 (8 : Fin 32), g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = x9 := by rw [rg34 (9 : Fin 32), g33_9]
  have g34_10 : reg n34 a0 = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [rg34 a0, g33_10]
  have g34_11 : reg n34 a1 = BitVec.ofNat 32 tl25.len := by rw [rg34 a1, g33_11]
  have g34_18 : reg n34 (18 : Fin 32) = out := by rw [rg34 (18 : Fin 32), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [rg34 (19 : Fin 32), g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg34 (20 : Fin 32), g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = kp := by rw [rg34 (21 : Fin 32), g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = x22 := by rw [rg34 (22 : Fin 32), g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = x23 := by rw [rg34 (23 : Fin 32), g33_23]
  have g34_24 : reg n34 (24 : Fin 32) = x24 := by rw [rg34 (24 : Fin 32), g33_24]
  have g34_25 : reg n34 (25 : Fin 32) = x25 := by rw [rg34 (25 : Fin 32), g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = ll := by rw [rg34 (26 : Fin 32), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg34 (27 : Fin 32), g33_27]
  have w34_88 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K34.w32 (by decide) (by decide)).trans w33_88
  have w34_8c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := (K34.w32 (by decide) (by decide)).trans w33_8c
  have w34_90 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K34.w32 (by decide) (by decide)).trans w33_90
  have w34_180 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K34.w32 (by decide) (by decide)).trans w33_180
  have w34_184 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K34.w32 (by decide) (by decide)).trans w33_184
  have w34_a20 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K34.w32 (by decide) (by decide)).trans w33_a20
  have w34_a24 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := (K34.w32 (by decide) (by decide)).trans w33_a24
  have w34_a28 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 tl9.header := (K34.w32 (by decide) (by decide)).trans w33_a28
  have w34_a2c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := (K34.w32 (by decide) (by decide)).trans w33_a2c
  have w34_1320 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := (K34.w32 (by decide) (by decide)).trans w33_1320
  have w34_1324 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := (K34.w32 (by decide) (by decide)).trans w33_1324
  have w34_1328 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := (K34.w32 (by decide) (by decide)).trans w33_1328
  have w34_132c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := (K34.w32 (by decide) (by decide)).trans w33_132c
  have b34_a30 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := (K34.b8 (by decide) (by decide)).trans b33_a30
  have b34_a34 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := (K34.b8 (by decide) (by decide)).trans b33_a34
  have w34_40 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := by rw [W34, g33_11]
  clear w33_90 b33_a34 b33_a30 w33_132c w33_1328 w33_1324 w33_1320 w33_a2c w33_a28 w33_a24 w33_a20 w33_184 w33_180 w33_8c w33_88 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_11 g33_10 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 rg33 W33 K33 fr33 s33 d33
  -- 0x4CE: sw
  obtain ⟨n35, d35, s35, fr35, K35, W35, rg35⟩ := sv_sw F E34 s34 sv_at_4ce (off' := 0x4D0) (c := 0x94)
    (by decide) (by rw [g34_2]; sv_addr) (by decide) (by decide)
  have t35 : Steps n0 n35 := t34.trans d35
  have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.keep K35 (by decide)
  have g35_2 : reg n35 sp = B + 0x21A0 := by rw [rg35 sp, g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg35 (3 : Fin 32), g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg35 (4 : Fin 32), g34_4]
  have g35_8 : reg n35 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg35 (8 : Fin 32), g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = x9 := by rw [rg35 (9 : Fin 32), g34_9]
  have g35_10 : reg n35 a0 = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [rg35 a0, g34_10]
  have g35_11 : reg n35 a1 = BitVec.ofNat 32 tl25.len := by rw [rg35 a1, g34_11]
  have g35_18 : reg n35 (18 : Fin 32) = out := by rw [rg35 (18 : Fin 32), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [rg35 (19 : Fin 32), g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg35 (20 : Fin 32), g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = kp := by rw [rg35 (21 : Fin 32), g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = x22 := by rw [rg35 (22 : Fin 32), g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = x23 := by rw [rg35 (23 : Fin 32), g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = x24 := by rw [rg35 (24 : Fin 32), g34_24]
  have g35_25 : reg n35 (25 : Fin 32) = x25 := by rw [rg35 (25 : Fin 32), g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = ll := by rw [rg35 (26 : Fin 32), g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg35 (27 : Fin 32), g34_27]
  have w35_40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := (K35.w32 (by decide) (by decide)).trans w34_40
  have w35_88 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K35.w32 (by decide) (by decide)).trans w34_88
  have w35_8c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := (K35.w32 (by decide) (by decide)).trans w34_8c
  have w35_90 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K35.w32 (by decide) (by decide)).trans w34_90
  have w35_180 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K35.w32 (by decide) (by decide)).trans w34_180
  have w35_184 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K35.w32 (by decide) (by decide)).trans w34_184
  have w35_a20 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K35.w32 (by decide) (by decide)).trans w34_a20
  have w35_a24 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := (K35.w32 (by decide) (by decide)).trans w34_a24
  have w35_a28 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 tl9.header := (K35.w32 (by decide) (by decide)).trans w34_a28
  have w35_a2c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := (K35.w32 (by decide) (by decide)).trans w34_a2c
  have w35_1320 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := (K35.w32 (by decide) (by decide)).trans w34_1320
  have w35_1324 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := (K35.w32 (by decide) (by decide)).trans w34_1324
  have w35_1328 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := (K35.w32 (by decide) (by decide)).trans w34_1328
  have w35_132c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := (K35.w32 (by decide) (by decide)).trans w34_132c
  have b35_a30 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := (K35.b8 (by decide) (by decide)).trans b34_a30
  have b35_a34 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := (K35.b8 (by decide) (by decide)).trans b34_a34
  have w35_94 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := by rw [W35, g34_11]
  clear w34_40 b34_a34 b34_a30 w34_132c w34_1328 w34_1324 w34_1320 w34_a2c w34_a28 w34_a24 w34_a20 w34_184 w34_180 w34_90 w34_8c w34_88 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_11 g34_10 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 rg34 W34 K34 fr34 s34 d34
  -- 0x4D0
  obtain ⟨n36, c36, u36⟩ := s35.block svL64d0 E35.self svL64d0_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m36 : n36.mem = n35.mem := u36.mem
  have s36 : St n36.mem SV n36 0x4DA (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
  have rb36 : ∀ q, reg n36 q = (runBlock svL64d0 (n35.mem, reg n35)).2 q := fun q => by rw [u36.regs]
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
  have g36_8 : reg n36 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb36, runBlock_reg _ _ _ (8 : Fin 32) s35.zero (by decide), g35_8]
  have g36_9 : reg n36 (9 : Fin 32) = x9 := by
    rw [rb36, runBlock_reg _ _ _ (9 : Fin 32) s35.zero (by decide), g35_9]
  have g36_18 : reg n36 (18 : Fin 32) = out := by
    rw [rb36, runBlock_reg _ _ _ (18 : Fin 32) s35.zero (by decide), g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by
    rw [rb36, runBlock_reg _ _ _ (19 : Fin 32) s35.zero (by decide), g35_19]
  have g36_20 : reg n36 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb36, runBlock_reg _ _ _ (20 : Fin 32) s35.zero (by decide), g35_20]
  have g36_21 : reg n36 (21 : Fin 32) = kp := by
    rw [rb36, runBlock_reg _ _ _ (21 : Fin 32) s35.zero (by decide), g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = x22 := by
    rw [rb36, runBlock_reg _ _ _ (22 : Fin 32) s35.zero (by decide), g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = x23 := by
    rw [rb36, runBlock_reg _ _ _ (23 : Fin 32) s35.zero (by decide), g35_23]
  have g36_24 : reg n36 (24 : Fin 32) = x24 := by
    rw [rb36, runBlock_reg _ _ _ (24 : Fin 32) s35.zero (by decide), g35_24]
  have g36_25 : reg n36 (25 : Fin 32) = x25 := by
    rw [rb36, runBlock_reg _ _ _ (25 : Fin 32) s35.zero (by decide), g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = ll := by
    rw [rb36, runBlock_reg _ _ _ (26 : Fin 32) s35.zero (by decide), g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb36, runBlock_reg _ _ _ (27 : Fin 32) s35.zero (by decide), g35_27]
  have g36_10 : reg n36 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb36]; simp +decide only [runBlock, BInstr.run, svL64d0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g35_2, g35_3, g35_4, g35_8, g35_9, g35_10, g35_11, g35_18, g35_19, g35_20, g35_21, g35_22, g35_23, g35_24, g35_25, g35_26, g35_27, s35.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g36_11 : reg n36 a1 = BitVec.ofNat 32 0x5 := by
    rw [rb36]; simp +decide only [runBlock, BInstr.run, svL64d0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g35_2, g35_3, g35_4, g35_8, g35_9, g35_10, g35_11, g35_18, g35_19, g35_20, g35_21, g35_22, g35_23, g35_24, g35_25, g35_26, g35_27, s35.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w36_40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := by rw [m36]; exact w35_40
  have w36_88 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m36]; exact w35_88
  have w36_8c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := by rw [m36]; exact w35_8c
  have w36_90 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m36]; exact w35_90
  have w36_94 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := by rw [m36]; exact w35_94
  have w36_180 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m36]; exact w35_180
  have w36_184 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m36]; exact w35_184
  have w36_a20 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m36]; exact w35_a20
  have w36_a24 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m36]; exact w35_a24
  have w36_a28 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m36]; exact w35_a28
  have w36_a2c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m36]; exact w35_a2c
  have w36_1320 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m36]; exact w35_1320
  have w36_1324 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m36]; exact w35_1324
  have w36_1328 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m36]; exact w35_1328
  have w36_132c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m36]; exact w35_132c
  have b36_a30 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := by rw [m36]; exact b35_a30
  have b36_a34 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m36]; exact b35_a34
  clear w35_94 b35_a34 b35_a30 w35_132c w35_1328 w35_1324 w35_1320 w35_a2c w35_a28 w35_a24 w35_a20 w35_184 w35_180 w35_90 w35_8c w35_88 w35_40 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_11 g35_10 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 rg35 W35 K35 fr35 s35 d35
  -- 0x4DA: branch, not taken
  obtain ⟨n37, d37, u37⟩ := s36.notTaken E36.self 0x4DC sv_at_4da
    (by decide) (by rw [g36_11, s36.zero]; decide)
  have s37 : St n37.mem SV n37 0x4DC (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
  have m37 : n37.mem = n36.mem := u37.mem
  have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
  have t37 : Steps n0 n37 := t36.trans (.single d37)
  have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : SvCode n37.mem := E36.fr F fr37
  have V37 : SvSaves B n37.mem v := V36.same m37
  have g37_2 : reg n37 sp = B + 0x21A0 := by rw [u37.regs, g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u37.regs, g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u37.regs, g36_4]
  have g37_8 : reg n37 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u37.regs, g36_8]
  have g37_9 : reg n37 (9 : Fin 32) = x9 := by rw [u37.regs, g36_9]
  have g37_10 : reg n37 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u37.regs, g36_10]
  have g37_11 : reg n37 a1 = BitVec.ofNat 32 0x5 := by rw [u37.regs, g36_11]
  have g37_18 : reg n37 (18 : Fin 32) = out := by rw [u37.regs, g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [u37.regs, g36_19]
  have g37_20 : reg n37 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u37.regs, g36_20]
  have g37_21 : reg n37 (21 : Fin 32) = kp := by rw [u37.regs, g36_21]
  have g37_22 : reg n37 (22 : Fin 32) = x22 := by rw [u37.regs, g36_22]
  have g37_23 : reg n37 (23 : Fin 32) = x23 := by rw [u37.regs, g36_23]
  have g37_24 : reg n37 (24 : Fin 32) = x24 := by rw [u37.regs, g36_24]
  have g37_25 : reg n37 (25 : Fin 32) = x25 := by rw [u37.regs, g36_25]
  have g37_26 : reg n37 (26 : Fin 32) = ll := by rw [u37.regs, g36_26]
  have g37_27 : reg n37 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u37.regs, g36_27]
  have w37_40 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := by rw [m37]; exact w36_40
  have w37_88 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m37]; exact w36_88
  have w37_8c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := by rw [m37]; exact w36_8c
  have w37_90 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m37]; exact w36_90
  have w37_94 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := by rw [m37]; exact w36_94
  have w37_180 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m37]; exact w36_180
  have w37_184 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m37]; exact w36_184
  have w37_a20 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m37]; exact w36_a20
  have w37_a24 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m37]; exact w36_a24
  have w37_a28 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m37]; exact w36_a28
  have w37_a2c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m37]; exact w36_a2c
  have w37_1320 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m37]; exact w36_1320
  have w37_1324 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m37]; exact w36_1324
  have w37_1328 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m37]; exact w36_1328
  have w37_132c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m37]; exact w36_132c
  have b37_a30 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := by rw [m37]; exact b36_a30
  have b37_a34 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m37]; exact b36_a34
  clear b36_a34 b36_a30 w36_132c w36_1328 w36_1324 w36_1320 w36_a2c w36_a28 w36_a24 w36_a20 w36_184 w36_180 w36_94 w36_90 w36_8c w36_88 w36_40 g36_11 g36_10 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 rb36 s36 m36 u36 c36
  -- 0x4DC: sw
  obtain ⟨n38, d38, s38, fr38, K38, W38, rg38⟩ := sv_sw F E37 s37 sv_at_4dc (off' := 0x4E0) (c := 0xA20)
    (by decide) (by rw [g37_10]; sv_addr) (by decide) (by decide)
  have t38 : Steps n0 n38 := t37.trans d38
  have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : SvCode n38.mem := E37.fr F fr38
  have V38 : SvSaves B n38.mem v := V37.keep K38 (by decide)
  have g38_2 : reg n38 sp = B + 0x21A0 := by rw [rg38 sp, g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg38 (3 : Fin 32), g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg38 (4 : Fin 32), g37_4]
  have g38_8 : reg n38 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg38 (8 : Fin 32), g37_8]
  have g38_9 : reg n38 (9 : Fin 32) = x9 := by rw [rg38 (9 : Fin 32), g37_9]
  have g38_10 : reg n38 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg38 a0, g37_10]
  have g38_11 : reg n38 a1 = BitVec.ofNat 32 0x5 := by rw [rg38 a1, g37_11]
  have g38_18 : reg n38 (18 : Fin 32) = out := by rw [rg38 (18 : Fin 32), g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [rg38 (19 : Fin 32), g37_19]
  have g38_20 : reg n38 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg38 (20 : Fin 32), g37_20]
  have g38_21 : reg n38 (21 : Fin 32) = kp := by rw [rg38 (21 : Fin 32), g37_21]
  have g38_22 : reg n38 (22 : Fin 32) = x22 := by rw [rg38 (22 : Fin 32), g37_22]
  have g38_23 : reg n38 (23 : Fin 32) = x23 := by rw [rg38 (23 : Fin 32), g37_23]
  have g38_24 : reg n38 (24 : Fin 32) = x24 := by rw [rg38 (24 : Fin 32), g37_24]
  have g38_25 : reg n38 (25 : Fin 32) = x25 := by rw [rg38 (25 : Fin 32), g37_25]
  have g38_26 : reg n38 (26 : Fin 32) = ll := by rw [rg38 (26 : Fin 32), g37_26]
  have g38_27 : reg n38 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg38 (27 : Fin 32), g37_27]
  have w38_40 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := (K38.w32 (by decide) (by decide)).trans w37_40
  have w38_88 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K38.w32 (by decide) (by decide)).trans w37_88
  have w38_8c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := (K38.w32 (by decide) (by decide)).trans w37_8c
  have w38_90 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K38.w32 (by decide) (by decide)).trans w37_90
  have w38_94 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := (K38.w32 (by decide) (by decide)).trans w37_94
  have w38_180 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K38.w32 (by decide) (by decide)).trans w37_180
  have w38_184 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K38.w32 (by decide) (by decide)).trans w37_184
  have w38_a24 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := (K38.w32 (by decide) (by decide)).trans w37_a24
  have w38_a28 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 tl9.header := (K38.w32 (by decide) (by decide)).trans w37_a28
  have w38_a2c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := (K38.w32 (by decide) (by decide)).trans w37_a2c
  have w38_1320 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := (K38.w32 (by decide) (by decide)).trans w37_1320
  have w38_1324 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := (K38.w32 (by decide) (by decide)).trans w37_1324
  have w38_1328 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := (K38.w32 (by decide) (by decide)).trans w37_1328
  have w38_132c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := (K38.w32 (by decide) (by decide)).trans w37_132c
  have b38_a30 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := (K38.b8 (by decide) (by decide)).trans b37_a30
  have b38_a34 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := (K38.b8 (by decide) (by decide)).trans b37_a34
  have w38_a20 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := by rw [W38, s37.zero]; rfl
  clear b37_a34 b37_a30 w37_132c w37_1328 w37_1324 w37_1320 w37_a2c w37_a28 w37_a24 w37_a20 w37_184 w37_180 w37_94 w37_90 w37_8c w37_88 w37_40 g37_27 g37_26 g37_25 g37_24 g37_23 g37_22 g37_21 g37_20 g37_19 g37_18 g37_11 g37_10 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 m37 s37 u37 d37
  -- 0x4E0
  obtain ⟨n39, c39, u39⟩ := s38.block svL64e0 E38.self svL64e0_end
    ⟨trivial, trivial, trivial⟩
  have m39 : n39.mem = n38.mem := u39.mem
  have s39 : St n39.mem SV n39 0x4E4 (reg n39) := ⟨u39.pc, rfl, fun _ => rfl⟩
  have rb39 : ∀ q, reg n39 q = (runBlock svL64e0 (n38.mem, reg n38)).2 q := fun q => by rw [u39.regs]
  have fr39 : ∀ x, SvR B x → n39.mem x = n38.mem x := fun x _ => by rw [m39]
  have t39 : Steps n0 n39 := t38.trans c39
  have fR39 : ∀ x, SvR B x → n39.mem x = M0 x := fun x hx => (fr39 x hx).trans (fR38 x hx)
  have E39 : SvCode n39.mem := E38.fr F fr39
  have V39 : SvSaves B n39.mem v := V38.same m39
  have g39_2 : reg n39 sp = B + 0x21A0 := by
    rw [rb39, runBlock_reg _ _ _ sp s38.zero (by decide), g38_2]
  have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb39, runBlock_reg _ _ _ (3 : Fin 32) s38.zero (by decide), g38_3]
  have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb39, runBlock_reg _ _ _ (4 : Fin 32) s38.zero (by decide), g38_4]
  have g39_8 : reg n39 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb39, runBlock_reg _ _ _ (8 : Fin 32) s38.zero (by decide), g38_8]
  have g39_9 : reg n39 (9 : Fin 32) = x9 := by
    rw [rb39, runBlock_reg _ _ _ (9 : Fin 32) s38.zero (by decide), g38_9]
  have g39_18 : reg n39 (18 : Fin 32) = out := by
    rw [rb39, runBlock_reg _ _ _ (18 : Fin 32) s38.zero (by decide), g38_18]
  have g39_19 : reg n39 (19 : Fin 32) = bp := by
    rw [rb39, runBlock_reg _ _ _ (19 : Fin 32) s38.zero (by decide), g38_19]
  have g39_20 : reg n39 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb39, runBlock_reg _ _ _ (20 : Fin 32) s38.zero (by decide), g38_20]
  have g39_21 : reg n39 (21 : Fin 32) = kp := by
    rw [rb39, runBlock_reg _ _ _ (21 : Fin 32) s38.zero (by decide), g38_21]
  have g39_22 : reg n39 (22 : Fin 32) = x22 := by
    rw [rb39, runBlock_reg _ _ _ (22 : Fin 32) s38.zero (by decide), g38_22]
  have g39_23 : reg n39 (23 : Fin 32) = x23 := by
    rw [rb39, runBlock_reg _ _ _ (23 : Fin 32) s38.zero (by decide), g38_23]
  have g39_24 : reg n39 (24 : Fin 32) = x24 := by
    rw [rb39, runBlock_reg _ _ _ (24 : Fin 32) s38.zero (by decide), g38_24]
  have g39_25 : reg n39 (25 : Fin 32) = x25 := by
    rw [rb39, runBlock_reg _ _ _ (25 : Fin 32) s38.zero (by decide), g38_25]
  have g39_26 : reg n39 (26 : Fin 32) = ll := by
    rw [rb39, runBlock_reg _ _ _ (26 : Fin 32) s38.zero (by decide), g38_26]
  have g39_27 : reg n39 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb39, runBlock_reg _ _ _ (27 : Fin 32) s38.zero (by decide), g38_27]
  have g39_10 : reg n39 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA28 := by
    rw [rb39]; simp +decide only [runBlock, BInstr.run, svL64e0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g38_2, g38_3, g38_4, g38_8, g38_9, g38_10, g38_11, g38_18, g38_19, g38_20, g38_21, g38_22, g38_23, g38_24, g38_25, g38_26, g38_27, s38.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g39_11 : reg n39 a1 = BitVec.ofNat 32 0x4 := by
    rw [rb39]; simp +decide only [runBlock, BInstr.run, svL64e0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g38_2, g38_3, g38_4, g38_8, g38_9, g38_10, g38_11, g38_18, g38_19, g38_20, g38_21, g38_22, g38_23, g38_24, g38_25, g38_26, g38_27, s38.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w39_40 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := by rw [m39]; exact w38_40
  have w39_88 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m39]; exact w38_88
  have w39_8c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := by rw [m39]; exact w38_8c
  have w39_90 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m39]; exact w38_90
  have w39_94 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := by rw [m39]; exact w38_94
  have w39_180 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m39]; exact w38_180
  have w39_184 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m39]; exact w38_184
  have w39_a20 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := by rw [m39]; exact w38_a20
  have w39_a24 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m39]; exact w38_a24
  have w39_a28 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m39]; exact w38_a28
  have w39_a2c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m39]; exact w38_a2c
  have w39_1320 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m39]; exact w38_1320
  have w39_1324 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m39]; exact w38_1324
  have w39_1328 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m39]; exact w38_1328
  have w39_132c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m39]; exact w38_132c
  have b39_a30 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := by rw [m39]; exact b38_a30
  have b39_a34 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m39]; exact b38_a34
  clear w38_a20 b38_a34 b38_a30 w38_132c w38_1328 w38_1324 w38_1320 w38_a2c w38_a28 w38_a24 w38_184 w38_180 w38_94 w38_90 w38_8c w38_88 w38_40 g38_27 g38_26 g38_25 g38_24 g38_23 g38_22 g38_21 g38_20 g38_19 g38_18 g38_11 g38_10 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 rg38 W38 K38 fr38 s38 d38
  -- 0x4E4: branch, taken
  obtain ⟨n40, d40, u40⟩ := s39.taken E39.self 0x4DC sv_at_4e4
    (by decide) (by rw [g39_11, s39.zero]; decide)
  have s40 : St n40.mem SV n40 0x4DC (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
  have m40 : n40.mem = n39.mem := u40.mem
  have fr40 : ∀ x, SvR B x → n40.mem x = n39.mem x := fun x _ => by rw [m40]
  have t40 : Steps n0 n40 := t39.trans (.single d40)
  have fR40 : ∀ x, SvR B x → n40.mem x = M0 x := fun x hx => (fr40 x hx).trans (fR39 x hx)
  have E40 : SvCode n40.mem := E39.fr F fr40
  have V40 : SvSaves B n40.mem v := V39.same m40
  have g40_2 : reg n40 sp = B + 0x21A0 := by rw [u40.regs, g39_2]
  have g40_3 : reg n40 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u40.regs, g39_3]
  have g40_4 : reg n40 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u40.regs, g39_4]
  have g40_8 : reg n40 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u40.regs, g39_8]
  have g40_9 : reg n40 (9 : Fin 32) = x9 := by rw [u40.regs, g39_9]
  have g40_10 : reg n40 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA28 := by rw [u40.regs, g39_10]
  have g40_11 : reg n40 a1 = BitVec.ofNat 32 0x4 := by rw [u40.regs, g39_11]
  have g40_18 : reg n40 (18 : Fin 32) = out := by rw [u40.regs, g39_18]
  have g40_19 : reg n40 (19 : Fin 32) = bp := by rw [u40.regs, g39_19]
  have g40_20 : reg n40 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u40.regs, g39_20]
  have g40_21 : reg n40 (21 : Fin 32) = kp := by rw [u40.regs, g39_21]
  have g40_22 : reg n40 (22 : Fin 32) = x22 := by rw [u40.regs, g39_22]
  have g40_23 : reg n40 (23 : Fin 32) = x23 := by rw [u40.regs, g39_23]
  have g40_24 : reg n40 (24 : Fin 32) = x24 := by rw [u40.regs, g39_24]
  have g40_25 : reg n40 (25 : Fin 32) = x25 := by rw [u40.regs, g39_25]
  have g40_26 : reg n40 (26 : Fin 32) = ll := by rw [u40.regs, g39_26]
  have g40_27 : reg n40 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u40.regs, g39_27]
  have w40_40 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := by rw [m40]; exact w39_40
  have w40_88 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m40]; exact w39_88
  have w40_8c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := by rw [m40]; exact w39_8c
  have w40_90 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m40]; exact w39_90
  have w40_94 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := by rw [m40]; exact w39_94
  have w40_180 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m40]; exact w39_180
  have w40_184 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m40]; exact w39_184
  have w40_a20 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := by rw [m40]; exact w39_a20
  have w40_a24 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m40]; exact w39_a24
  have w40_a28 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m40]; exact w39_a28
  have w40_a2c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m40]; exact w39_a2c
  have w40_1320 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m40]; exact w39_1320
  have w40_1324 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m40]; exact w39_1324
  have w40_1328 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m40]; exact w39_1328
  have w40_132c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m40]; exact w39_132c
  have b40_a30 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := by rw [m40]; exact b39_a30
  have b40_a34 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m40]; exact b39_a34
  clear b39_a34 b39_a30 w39_132c w39_1328 w39_1324 w39_1320 w39_a2c w39_a28 w39_a24 w39_a20 w39_184 w39_180 w39_94 w39_90 w39_8c w39_88 w39_40 g39_11 g39_10 g39_27 g39_26 g39_25 g39_24 g39_23 g39_22 g39_21 g39_20 g39_19 g39_18 g39_9 g39_8 g39_4 g39_3 g39_2 V39 E39 fR39 t39 fr39 rb39 s39 m39 u39 c39
  -- 0x4DC: sw
  obtain ⟨n41, d41, s41, fr41, K41, W41, rg41⟩ := sv_sw F E40 s40 sv_at_4dc (off' := 0x4E0) (c := 0xA28)
    (by decide) (by rw [g40_10]; sv_addr) (by decide) (by decide)
  have t41 : Steps n0 n41 := t40.trans d41
  have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
  have E41 : SvCode n41.mem := E40.fr F fr41
  have V41 : SvSaves B n41.mem v := V40.keep K41 (by decide)
  have g41_2 : reg n41 sp = B + 0x21A0 := by rw [rg41 sp, g40_2]
  have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg41 (3 : Fin 32), g40_3]
  have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg41 (4 : Fin 32), g40_4]
  have g41_8 : reg n41 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg41 (8 : Fin 32), g40_8]
  have g41_9 : reg n41 (9 : Fin 32) = x9 := by rw [rg41 (9 : Fin 32), g40_9]
  have g41_10 : reg n41 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA28 := by rw [rg41 a0, g40_10]
  have g41_11 : reg n41 a1 = BitVec.ofNat 32 0x4 := by rw [rg41 a1, g40_11]
  have g41_18 : reg n41 (18 : Fin 32) = out := by rw [rg41 (18 : Fin 32), g40_18]
  have g41_19 : reg n41 (19 : Fin 32) = bp := by rw [rg41 (19 : Fin 32), g40_19]
  have g41_20 : reg n41 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg41 (20 : Fin 32), g40_20]
  have g41_21 : reg n41 (21 : Fin 32) = kp := by rw [rg41 (21 : Fin 32), g40_21]
  have g41_22 : reg n41 (22 : Fin 32) = x22 := by rw [rg41 (22 : Fin 32), g40_22]
  have g41_23 : reg n41 (23 : Fin 32) = x23 := by rw [rg41 (23 : Fin 32), g40_23]
  have g41_24 : reg n41 (24 : Fin 32) = x24 := by rw [rg41 (24 : Fin 32), g40_24]
  have g41_25 : reg n41 (25 : Fin 32) = x25 := by rw [rg41 (25 : Fin 32), g40_25]
  have g41_26 : reg n41 (26 : Fin 32) = ll := by rw [rg41 (26 : Fin 32), g40_26]
  have g41_27 : reg n41 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg41 (27 : Fin 32), g40_27]
  have w41_40 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := (K41.w32 (by decide) (by decide)).trans w40_40
  have w41_88 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K41.w32 (by decide) (by decide)).trans w40_88
  have w41_8c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := (K41.w32 (by decide) (by decide)).trans w40_8c
  have w41_90 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K41.w32 (by decide) (by decide)).trans w40_90
  have w41_94 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := (K41.w32 (by decide) (by decide)).trans w40_94
  have w41_180 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K41.w32 (by decide) (by decide)).trans w40_180
  have w41_184 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K41.w32 (by decide) (by decide)).trans w40_184
  have w41_a20 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := (K41.w32 (by decide) (by decide)).trans w40_a20
  have w41_a24 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := (K41.w32 (by decide) (by decide)).trans w40_a24
  have w41_a2c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := (K41.w32 (by decide) (by decide)).trans w40_a2c
  have w41_1320 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := (K41.w32 (by decide) (by decide)).trans w40_1320
  have w41_1324 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := (K41.w32 (by decide) (by decide)).trans w40_1324
  have w41_1328 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := (K41.w32 (by decide) (by decide)).trans w40_1328
  have w41_132c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := (K41.w32 (by decide) (by decide)).trans w40_132c
  have b41_a30 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := (K41.b8 (by decide) (by decide)).trans b40_a30
  have b41_a34 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := (K41.b8 (by decide) (by decide)).trans b40_a34
  have w41_a28 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 0x0 := by rw [W41, s40.zero]; rfl
  clear b40_a34 b40_a30 w40_132c w40_1328 w40_1324 w40_1320 w40_a2c w40_a28 w40_a24 w40_a20 w40_184 w40_180 w40_94 w40_90 w40_8c w40_88 w40_40 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_11 g40_10 g40_9 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 m40 s40 u40 d40
  -- 0x4E0
  obtain ⟨n42, c42, u42⟩ := s41.block svL64e0 E41.self svL64e0_end
    ⟨trivial, trivial, trivial⟩
  have m42 : n42.mem = n41.mem := u42.mem
  have s42 : St n42.mem SV n42 0x4E4 (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
  have rb42 : ∀ q, reg n42 q = (runBlock svL64e0 (n41.mem, reg n41)).2 q := fun q => by rw [u42.regs]
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
  have g42_8 : reg n42 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb42, runBlock_reg _ _ _ (8 : Fin 32) s41.zero (by decide), g41_8]
  have g42_9 : reg n42 (9 : Fin 32) = x9 := by
    rw [rb42, runBlock_reg _ _ _ (9 : Fin 32) s41.zero (by decide), g41_9]
  have g42_18 : reg n42 (18 : Fin 32) = out := by
    rw [rb42, runBlock_reg _ _ _ (18 : Fin 32) s41.zero (by decide), g41_18]
  have g42_19 : reg n42 (19 : Fin 32) = bp := by
    rw [rb42, runBlock_reg _ _ _ (19 : Fin 32) s41.zero (by decide), g41_19]
  have g42_20 : reg n42 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb42, runBlock_reg _ _ _ (20 : Fin 32) s41.zero (by decide), g41_20]
  have g42_21 : reg n42 (21 : Fin 32) = kp := by
    rw [rb42, runBlock_reg _ _ _ (21 : Fin 32) s41.zero (by decide), g41_21]
  have g42_22 : reg n42 (22 : Fin 32) = x22 := by
    rw [rb42, runBlock_reg _ _ _ (22 : Fin 32) s41.zero (by decide), g41_22]
  have g42_23 : reg n42 (23 : Fin 32) = x23 := by
    rw [rb42, runBlock_reg _ _ _ (23 : Fin 32) s41.zero (by decide), g41_23]
  have g42_24 : reg n42 (24 : Fin 32) = x24 := by
    rw [rb42, runBlock_reg _ _ _ (24 : Fin 32) s41.zero (by decide), g41_24]
  have g42_25 : reg n42 (25 : Fin 32) = x25 := by
    rw [rb42, runBlock_reg _ _ _ (25 : Fin 32) s41.zero (by decide), g41_25]
  have g42_26 : reg n42 (26 : Fin 32) = ll := by
    rw [rb42, runBlock_reg _ _ _ (26 : Fin 32) s41.zero (by decide), g41_26]
  have g42_27 : reg n42 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb42, runBlock_reg _ _ _ (27 : Fin 32) s41.zero (by decide), g41_27]
  have g42_10 : reg n42 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA30 := by
    rw [rb42]; simp +decide only [runBlock, BInstr.run, svL64e0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_11, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g42_11 : reg n42 a1 = BitVec.ofNat 32 0x3 := by
    rw [rb42]; simp +decide only [runBlock, BInstr.run, svL64e0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_11, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w42_40 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := by rw [m42]; exact w41_40
  have w42_88 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m42]; exact w41_88
  have w42_8c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := by rw [m42]; exact w41_8c
  have w42_90 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m42]; exact w41_90
  have w42_94 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := by rw [m42]; exact w41_94
  have w42_180 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m42]; exact w41_180
  have w42_184 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m42]; exact w41_184
  have w42_a20 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := by rw [m42]; exact w41_a20
  have w42_a24 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m42]; exact w41_a24
  have w42_a28 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 0x0 := by rw [m42]; exact w41_a28
  have w42_a2c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m42]; exact w41_a2c
  have w42_1320 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m42]; exact w41_1320
  have w42_1324 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m42]; exact w41_1324
  have w42_1328 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m42]; exact w41_1328
  have w42_132c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m42]; exact w41_132c
  have b42_a30 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := by rw [m42]; exact b41_a30
  have b42_a34 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m42]; exact b41_a34
  clear w41_a28 b41_a34 b41_a30 w41_132c w41_1328 w41_1324 w41_1320 w41_a2c w41_a24 w41_a20 w41_184 w41_180 w41_94 w41_90 w41_8c w41_88 w41_40 g41_27 g41_26 g41_25 g41_24 g41_23 g41_22 g41_21 g41_20 g41_19 g41_18 g41_11 g41_10 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 rg41 W41 K41 fr41 s41 d41
  -- 0x4E4: branch, taken
  obtain ⟨n43, d43, u43⟩ := s42.taken E42.self 0x4DC sv_at_4e4
    (by decide) (by rw [g42_11, s42.zero]; decide)
  have s43 : St n43.mem SV n43 0x4DC (reg n43) := ⟨u43.pc, rfl, fun _ => rfl⟩
  have m43 : n43.mem = n42.mem := u43.mem
  have fr43 : ∀ x, SvR B x → n43.mem x = n42.mem x := fun x _ => by rw [m43]
  have t43 : Steps n0 n43 := t42.trans (.single d43)
  have fR43 : ∀ x, SvR B x → n43.mem x = M0 x := fun x hx => (fr43 x hx).trans (fR42 x hx)
  have E43 : SvCode n43.mem := E42.fr F fr43
  have V43 : SvSaves B n43.mem v := V42.same m43
  have g43_2 : reg n43 sp = B + 0x21A0 := by rw [u43.regs, g42_2]
  have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u43.regs, g42_3]
  have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u43.regs, g42_4]
  have g43_8 : reg n43 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u43.regs, g42_8]
  have g43_9 : reg n43 (9 : Fin 32) = x9 := by rw [u43.regs, g42_9]
  have g43_10 : reg n43 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA30 := by rw [u43.regs, g42_10]
  have g43_11 : reg n43 a1 = BitVec.ofNat 32 0x3 := by rw [u43.regs, g42_11]
  have g43_18 : reg n43 (18 : Fin 32) = out := by rw [u43.regs, g42_18]
  have g43_19 : reg n43 (19 : Fin 32) = bp := by rw [u43.regs, g42_19]
  have g43_20 : reg n43 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u43.regs, g42_20]
  have g43_21 : reg n43 (21 : Fin 32) = kp := by rw [u43.regs, g42_21]
  have g43_22 : reg n43 (22 : Fin 32) = x22 := by rw [u43.regs, g42_22]
  have g43_23 : reg n43 (23 : Fin 32) = x23 := by rw [u43.regs, g42_23]
  have g43_24 : reg n43 (24 : Fin 32) = x24 := by rw [u43.regs, g42_24]
  have g43_25 : reg n43 (25 : Fin 32) = x25 := by rw [u43.regs, g42_25]
  have g43_26 : reg n43 (26 : Fin 32) = ll := by rw [u43.regs, g42_26]
  have g43_27 : reg n43 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u43.regs, g42_27]
  have w43_40 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := by rw [m43]; exact w42_40
  have w43_88 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m43]; exact w42_88
  have w43_8c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := by rw [m43]; exact w42_8c
  have w43_90 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m43]; exact w42_90
  have w43_94 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := by rw [m43]; exact w42_94
  have w43_180 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m43]; exact w42_180
  have w43_184 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m43]; exact w42_184
  have w43_a20 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := by rw [m43]; exact w42_a20
  have w43_a24 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m43]; exact w42_a24
  have w43_a28 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 0x0 := by rw [m43]; exact w42_a28
  have w43_a2c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m43]; exact w42_a2c
  have w43_1320 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m43]; exact w42_1320
  have w43_1324 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m43]; exact w42_1324
  have w43_1328 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m43]; exact w42_1328
  have w43_132c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m43]; exact w42_132c
  have b43_a30 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl25.tag := by rw [m43]; exact b42_a30
  have b43_a34 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m43]; exact b42_a34
  clear b42_a34 b42_a30 w42_132c w42_1328 w42_1324 w42_1320 w42_a2c w42_a28 w42_a24 w42_a20 w42_184 w42_180 w42_94 w42_90 w42_8c w42_88 w42_40 g42_11 g42_10 g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
  -- 0x4DC: sw
  obtain ⟨n44, d44, s44, fr44, K44, W44, rg44⟩ := sv_sw F E43 s43 sv_at_4dc (off' := 0x4E0) (c := 0xA30)
    (by decide) (by rw [g43_10]; sv_addr) (by decide) (by decide)
  have t44 : Steps n0 n44 := t43.trans d44
  have fR44 : ∀ x, SvR B x → n44.mem x = M0 x := fun x hx => (fr44 x hx).trans (fR43 x hx)
  have E44 : SvCode n44.mem := E43.fr F fr44
  have V44 : SvSaves B n44.mem v := V43.keep K44 (by decide)
  have g44_2 : reg n44 sp = B + 0x21A0 := by rw [rg44 sp, g43_2]
  have g44_3 : reg n44 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg44 (3 : Fin 32), g43_3]
  have g44_4 : reg n44 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg44 (4 : Fin 32), g43_4]
  have g44_8 : reg n44 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg44 (8 : Fin 32), g43_8]
  have g44_9 : reg n44 (9 : Fin 32) = x9 := by rw [rg44 (9 : Fin 32), g43_9]
  have g44_10 : reg n44 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA30 := by rw [rg44 a0, g43_10]
  have g44_11 : reg n44 a1 = BitVec.ofNat 32 0x3 := by rw [rg44 a1, g43_11]
  have g44_18 : reg n44 (18 : Fin 32) = out := by rw [rg44 (18 : Fin 32), g43_18]
  have g44_19 : reg n44 (19 : Fin 32) = bp := by rw [rg44 (19 : Fin 32), g43_19]
  have g44_20 : reg n44 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg44 (20 : Fin 32), g43_20]
  have g44_21 : reg n44 (21 : Fin 32) = kp := by rw [rg44 (21 : Fin 32), g43_21]
  have g44_22 : reg n44 (22 : Fin 32) = x22 := by rw [rg44 (22 : Fin 32), g43_22]
  have g44_23 : reg n44 (23 : Fin 32) = x23 := by rw [rg44 (23 : Fin 32), g43_23]
  have g44_24 : reg n44 (24 : Fin 32) = x24 := by rw [rg44 (24 : Fin 32), g43_24]
  have g44_25 : reg n44 (25 : Fin 32) = x25 := by rw [rg44 (25 : Fin 32), g43_25]
  have g44_26 : reg n44 (26 : Fin 32) = ll := by rw [rg44 (26 : Fin 32), g43_26]
  have g44_27 : reg n44 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg44 (27 : Fin 32), g43_27]
  have w44_40 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := (K44.w32 (by decide) (by decide)).trans w43_40
  have w44_88 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K44.w32 (by decide) (by decide)).trans w43_88
  have w44_8c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := (K44.w32 (by decide) (by decide)).trans w43_8c
  have w44_90 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K44.w32 (by decide) (by decide)).trans w43_90
  have w44_94 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := (K44.w32 (by decide) (by decide)).trans w43_94
  have w44_180 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K44.w32 (by decide) (by decide)).trans w43_180
  have w44_184 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K44.w32 (by decide) (by decide)).trans w43_184
  have w44_a20 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := (K44.w32 (by decide) (by decide)).trans w43_a20
  have w44_a24 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := (K44.w32 (by decide) (by decide)).trans w43_a24
  have w44_a28 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 0x0 := (K44.w32 (by decide) (by decide)).trans w43_a28
  have w44_a2c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := (K44.w32 (by decide) (by decide)).trans w43_a2c
  have w44_1320 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := (K44.w32 (by decide) (by decide)).trans w43_1320
  have w44_1324 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := (K44.w32 (by decide) (by decide)).trans w43_1324
  have w44_1328 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := (K44.w32 (by decide) (by decide)).trans w43_1328
  have w44_132c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := (K44.w32 (by decide) (by decide)).trans w43_132c
  have b44_a34 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := (K44.b8 (by decide) (by decide)).trans b43_a34
  have w44_a30 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 0x0 := by rw [W44, s43.zero]; rfl
  clear b43_a34 b43_a30 w43_132c w43_1328 w43_1324 w43_1320 w43_a2c w43_a28 w43_a24 w43_a20 w43_184 w43_180 w43_94 w43_90 w43_8c w43_88 w43_40 g43_27 g43_26 g43_25 g43_24 g43_23 g43_22 g43_21 g43_20 g43_19 g43_18 g43_11 g43_10 g43_9 g43_8 g43_4 g43_3 g43_2 V43 E43 fR43 t43 fr43 m43 s43 u43 d43
  -- 0x4E0
  obtain ⟨n45, c45, u45⟩ := s44.block svL64e0 E44.self svL64e0_end
    ⟨trivial, trivial, trivial⟩
  have m45 : n45.mem = n44.mem := u45.mem
  have s45 : St n45.mem SV n45 0x4E4 (reg n45) := ⟨u45.pc, rfl, fun _ => rfl⟩
  have rb45 : ∀ q, reg n45 q = (runBlock svL64e0 (n44.mem, reg n44)).2 q := fun q => by rw [u45.regs]
  have fr45 : ∀ x, SvR B x → n45.mem x = n44.mem x := fun x _ => by rw [m45]
  have t45 : Steps n0 n45 := t44.trans c45
  have fR45 : ∀ x, SvR B x → n45.mem x = M0 x := fun x hx => (fr45 x hx).trans (fR44 x hx)
  have E45 : SvCode n45.mem := E44.fr F fr45
  have V45 : SvSaves B n45.mem v := V44.same m45
  have g45_2 : reg n45 sp = B + 0x21A0 := by
    rw [rb45, runBlock_reg _ _ _ sp s44.zero (by decide), g44_2]
  have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb45, runBlock_reg _ _ _ (3 : Fin 32) s44.zero (by decide), g44_3]
  have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb45, runBlock_reg _ _ _ (4 : Fin 32) s44.zero (by decide), g44_4]
  have g45_8 : reg n45 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb45, runBlock_reg _ _ _ (8 : Fin 32) s44.zero (by decide), g44_8]
  have g45_9 : reg n45 (9 : Fin 32) = x9 := by
    rw [rb45, runBlock_reg _ _ _ (9 : Fin 32) s44.zero (by decide), g44_9]
  have g45_18 : reg n45 (18 : Fin 32) = out := by
    rw [rb45, runBlock_reg _ _ _ (18 : Fin 32) s44.zero (by decide), g44_18]
  have g45_19 : reg n45 (19 : Fin 32) = bp := by
    rw [rb45, runBlock_reg _ _ _ (19 : Fin 32) s44.zero (by decide), g44_19]
  have g45_20 : reg n45 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb45, runBlock_reg _ _ _ (20 : Fin 32) s44.zero (by decide), g44_20]
  have g45_21 : reg n45 (21 : Fin 32) = kp := by
    rw [rb45, runBlock_reg _ _ _ (21 : Fin 32) s44.zero (by decide), g44_21]
  have g45_22 : reg n45 (22 : Fin 32) = x22 := by
    rw [rb45, runBlock_reg _ _ _ (22 : Fin 32) s44.zero (by decide), g44_22]
  have g45_23 : reg n45 (23 : Fin 32) = x23 := by
    rw [rb45, runBlock_reg _ _ _ (23 : Fin 32) s44.zero (by decide), g44_23]
  have g45_24 : reg n45 (24 : Fin 32) = x24 := by
    rw [rb45, runBlock_reg _ _ _ (24 : Fin 32) s44.zero (by decide), g44_24]
  have g45_25 : reg n45 (25 : Fin 32) = x25 := by
    rw [rb45, runBlock_reg _ _ _ (25 : Fin 32) s44.zero (by decide), g44_25]
  have g45_26 : reg n45 (26 : Fin 32) = ll := by
    rw [rb45, runBlock_reg _ _ _ (26 : Fin 32) s44.zero (by decide), g44_26]
  have g45_27 : reg n45 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb45, runBlock_reg _ _ _ (27 : Fin 32) s44.zero (by decide), g44_27]
  have g45_10 : reg n45 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA38 := by
    rw [rb45]; simp +decide only [runBlock, BInstr.run, svL64e0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g44_2, g44_3, g44_4, g44_8, g44_9, g44_10, g44_11, g44_18, g44_19, g44_20, g44_21, g44_22, g44_23, g44_24, g44_25, g44_26, g44_27, s44.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g45_11 : reg n45 a1 = BitVec.ofNat 32 0x2 := by
    rw [rb45]; simp +decide only [runBlock, BInstr.run, svL64e0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g44_2, g44_3, g44_4, g44_8, g44_9, g44_10, g44_11, g44_18, g44_19, g44_20, g44_21, g44_22, g44_23, g44_24, g44_25, g44_26, g44_27, s44.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w45_40 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := by rw [m45]; exact w44_40
  have w45_88 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m45]; exact w44_88
  have w45_8c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := by rw [m45]; exact w44_8c
  have w45_90 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m45]; exact w44_90
  have w45_94 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := by rw [m45]; exact w44_94
  have w45_180 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m45]; exact w44_180
  have w45_184 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m45]; exact w44_184
  have w45_a20 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := by rw [m45]; exact w44_a20
  have w45_a24 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m45]; exact w44_a24
  have w45_a28 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 0x0 := by rw [m45]; exact w44_a28
  have w45_a2c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m45]; exact w44_a2c
  have w45_a30 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 0x0 := by rw [m45]; exact w44_a30
  have w45_1320 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m45]; exact w44_1320
  have w45_1324 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m45]; exact w44_1324
  have w45_1328 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m45]; exact w44_1328
  have w45_132c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m45]; exact w44_132c
  have b45_a34 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m45]; exact b44_a34
  clear w44_a30 b44_a34 w44_132c w44_1328 w44_1324 w44_1320 w44_a2c w44_a28 w44_a24 w44_a20 w44_184 w44_180 w44_94 w44_90 w44_8c w44_88 w44_40 g44_27 g44_26 g44_25 g44_24 g44_23 g44_22 g44_21 g44_20 g44_19 g44_18 g44_11 g44_10 g44_9 g44_8 g44_4 g44_3 g44_2 V44 E44 fR44 t44 rg44 W44 K44 fr44 s44 d44
  -- 0x4E4: branch, taken
  obtain ⟨n46, d46, u46⟩ := s45.taken E45.self 0x4DC sv_at_4e4
    (by decide) (by rw [g45_11, s45.zero]; decide)
  have s46 : St n46.mem SV n46 0x4DC (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
  have m46 : n46.mem = n45.mem := u46.mem
  have fr46 : ∀ x, SvR B x → n46.mem x = n45.mem x := fun x _ => by rw [m46]
  have t46 : Steps n0 n46 := t45.trans (.single d46)
  have fR46 : ∀ x, SvR B x → n46.mem x = M0 x := fun x hx => (fr46 x hx).trans (fR45 x hx)
  have E46 : SvCode n46.mem := E45.fr F fr46
  have V46 : SvSaves B n46.mem v := V45.same m46
  have g46_2 : reg n46 sp = B + 0x21A0 := by rw [u46.regs, g45_2]
  have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u46.regs, g45_3]
  have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u46.regs, g45_4]
  have g46_8 : reg n46 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u46.regs, g45_8]
  have g46_9 : reg n46 (9 : Fin 32) = x9 := by rw [u46.regs, g45_9]
  have g46_10 : reg n46 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA38 := by rw [u46.regs, g45_10]
  have g46_11 : reg n46 a1 = BitVec.ofNat 32 0x2 := by rw [u46.regs, g45_11]
  have g46_18 : reg n46 (18 : Fin 32) = out := by rw [u46.regs, g45_18]
  have g46_19 : reg n46 (19 : Fin 32) = bp := by rw [u46.regs, g45_19]
  have g46_20 : reg n46 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u46.regs, g45_20]
  have g46_21 : reg n46 (21 : Fin 32) = kp := by rw [u46.regs, g45_21]
  have g46_22 : reg n46 (22 : Fin 32) = x22 := by rw [u46.regs, g45_22]
  have g46_23 : reg n46 (23 : Fin 32) = x23 := by rw [u46.regs, g45_23]
  have g46_24 : reg n46 (24 : Fin 32) = x24 := by rw [u46.regs, g45_24]
  have g46_25 : reg n46 (25 : Fin 32) = x25 := by rw [u46.regs, g45_25]
  have g46_26 : reg n46 (26 : Fin 32) = ll := by rw [u46.regs, g45_26]
  have g46_27 : reg n46 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u46.regs, g45_27]
  have w46_40 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := by rw [m46]; exact w45_40
  have w46_88 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m46]; exact w45_88
  have w46_8c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := by rw [m46]; exact w45_8c
  have w46_90 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m46]; exact w45_90
  have w46_94 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := by rw [m46]; exact w45_94
  have w46_180 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m46]; exact w45_180
  have w46_184 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m46]; exact w45_184
  have w46_a20 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := by rw [m46]; exact w45_a20
  have w46_a24 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m46]; exact w45_a24
  have w46_a28 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 0x0 := by rw [m46]; exact w45_a28
  have w46_a2c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m46]; exact w45_a2c
  have w46_a30 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 0x0 := by rw [m46]; exact w45_a30
  have w46_1320 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m46]; exact w45_1320
  have w46_1324 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m46]; exact w45_1324
  have w46_1328 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m46]; exact w45_1328
  have w46_132c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m46]; exact w45_132c
  have b46_a34 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m46]; exact b45_a34
  clear b45_a34 w45_132c w45_1328 w45_1324 w45_1320 w45_a30 w45_a2c w45_a28 w45_a24 w45_a20 w45_184 w45_180 w45_94 w45_90 w45_8c w45_88 w45_40 g45_11 g45_10 g45_27 g45_26 g45_25 g45_24 g45_23 g45_22 g45_21 g45_20 g45_19 g45_18 g45_9 g45_8 g45_4 g45_3 g45_2 V45 E45 fR45 t45 fr45 rb45 s45 m45 u45 c45
  -- 0x4DC: sw
  obtain ⟨n47, d47, s47, fr47, K47, W47, rg47⟩ := sv_sw F E46 s46 sv_at_4dc (off' := 0x4E0) (c := 0xA38)
    (by decide) (by rw [g46_10]; sv_addr) (by decide) (by decide)
  have t47 : Steps n0 n47 := t46.trans d47
  have fR47 : ∀ x, SvR B x → n47.mem x = M0 x := fun x hx => (fr47 x hx).trans (fR46 x hx)
  have E47 : SvCode n47.mem := E46.fr F fr47
  have V47 : SvSaves B n47.mem v := V46.keep K47 (by decide)
  have g47_2 : reg n47 sp = B + 0x21A0 := by rw [rg47 sp, g46_2]
  have g47_3 : reg n47 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg47 (3 : Fin 32), g46_3]
  have g47_4 : reg n47 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg47 (4 : Fin 32), g46_4]
  have g47_8 : reg n47 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg47 (8 : Fin 32), g46_8]
  have g47_9 : reg n47 (9 : Fin 32) = x9 := by rw [rg47 (9 : Fin 32), g46_9]
  have g47_10 : reg n47 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA38 := by rw [rg47 a0, g46_10]
  have g47_11 : reg n47 a1 = BitVec.ofNat 32 0x2 := by rw [rg47 a1, g46_11]
  have g47_18 : reg n47 (18 : Fin 32) = out := by rw [rg47 (18 : Fin 32), g46_18]
  have g47_19 : reg n47 (19 : Fin 32) = bp := by rw [rg47 (19 : Fin 32), g46_19]
  have g47_20 : reg n47 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg47 (20 : Fin 32), g46_20]
  have g47_21 : reg n47 (21 : Fin 32) = kp := by rw [rg47 (21 : Fin 32), g46_21]
  have g47_22 : reg n47 (22 : Fin 32) = x22 := by rw [rg47 (22 : Fin 32), g46_22]
  have g47_23 : reg n47 (23 : Fin 32) = x23 := by rw [rg47 (23 : Fin 32), g46_23]
  have g47_24 : reg n47 (24 : Fin 32) = x24 := by rw [rg47 (24 : Fin 32), g46_24]
  have g47_25 : reg n47 (25 : Fin 32) = x25 := by rw [rg47 (25 : Fin 32), g46_25]
  have g47_26 : reg n47 (26 : Fin 32) = ll := by rw [rg47 (26 : Fin 32), g46_26]
  have g47_27 : reg n47 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg47 (27 : Fin 32), g46_27]
  have w47_40 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := (K47.w32 (by decide) (by decide)).trans w46_40
  have w47_88 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K47.w32 (by decide) (by decide)).trans w46_88
  have w47_8c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := (K47.w32 (by decide) (by decide)).trans w46_8c
  have w47_90 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K47.w32 (by decide) (by decide)).trans w46_90
  have w47_94 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := (K47.w32 (by decide) (by decide)).trans w46_94
  have w47_180 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K47.w32 (by decide) (by decide)).trans w46_180
  have w47_184 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K47.w32 (by decide) (by decide)).trans w46_184
  have w47_a20 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := (K47.w32 (by decide) (by decide)).trans w46_a20
  have w47_a24 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := (K47.w32 (by decide) (by decide)).trans w46_a24
  have w47_a28 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 0x0 := (K47.w32 (by decide) (by decide)).trans w46_a28
  have w47_a2c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := (K47.w32 (by decide) (by decide)).trans w46_a2c
  have w47_a30 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 0x0 := (K47.w32 (by decide) (by decide)).trans w46_a30
  have w47_1320 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := (K47.w32 (by decide) (by decide)).trans w46_1320
  have w47_1324 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := (K47.w32 (by decide) (by decide)).trans w46_1324
  have w47_1328 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := (K47.w32 (by decide) (by decide)).trans w46_1328
  have w47_132c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := (K47.w32 (by decide) (by decide)).trans w46_132c
  have b47_a34 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := (K47.b8 (by decide) (by decide)).trans b46_a34
  have w47_a38 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = BitVec.ofNat 32 0x0 := by rw [W47, s46.zero]; rfl
  clear b46_a34 w46_132c w46_1328 w46_1324 w46_1320 w46_a30 w46_a2c w46_a28 w46_a24 w46_a20 w46_184 w46_180 w46_94 w46_90 w46_8c w46_88 w46_40 g46_27 g46_26 g46_25 g46_24 g46_23 g46_22 g46_21 g46_20 g46_19 g46_18 g46_11 g46_10 g46_9 g46_8 g46_4 g46_3 g46_2 V46 E46 fR46 t46 fr46 m46 s46 u46 d46
  -- 0x4E0
  obtain ⟨n48, c48, u48⟩ := s47.block svL64e0 E47.self svL64e0_end
    ⟨trivial, trivial, trivial⟩
  have m48 : n48.mem = n47.mem := u48.mem
  have s48 : St n48.mem SV n48 0x4E4 (reg n48) := ⟨u48.pc, rfl, fun _ => rfl⟩
  have rb48 : ∀ q, reg n48 q = (runBlock svL64e0 (n47.mem, reg n47)).2 q := fun q => by rw [u48.regs]
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
  have g48_8 : reg n48 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb48, runBlock_reg _ _ _ (8 : Fin 32) s47.zero (by decide), g47_8]
  have g48_9 : reg n48 (9 : Fin 32) = x9 := by
    rw [rb48, runBlock_reg _ _ _ (9 : Fin 32) s47.zero (by decide), g47_9]
  have g48_18 : reg n48 (18 : Fin 32) = out := by
    rw [rb48, runBlock_reg _ _ _ (18 : Fin 32) s47.zero (by decide), g47_18]
  have g48_19 : reg n48 (19 : Fin 32) = bp := by
    rw [rb48, runBlock_reg _ _ _ (19 : Fin 32) s47.zero (by decide), g47_19]
  have g48_20 : reg n48 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb48, runBlock_reg _ _ _ (20 : Fin 32) s47.zero (by decide), g47_20]
  have g48_21 : reg n48 (21 : Fin 32) = kp := by
    rw [rb48, runBlock_reg _ _ _ (21 : Fin 32) s47.zero (by decide), g47_21]
  have g48_22 : reg n48 (22 : Fin 32) = x22 := by
    rw [rb48, runBlock_reg _ _ _ (22 : Fin 32) s47.zero (by decide), g47_22]
  have g48_23 : reg n48 (23 : Fin 32) = x23 := by
    rw [rb48, runBlock_reg _ _ _ (23 : Fin 32) s47.zero (by decide), g47_23]
  have g48_24 : reg n48 (24 : Fin 32) = x24 := by
    rw [rb48, runBlock_reg _ _ _ (24 : Fin 32) s47.zero (by decide), g47_24]
  have g48_25 : reg n48 (25 : Fin 32) = x25 := by
    rw [rb48, runBlock_reg _ _ _ (25 : Fin 32) s47.zero (by decide), g47_25]
  have g48_26 : reg n48 (26 : Fin 32) = ll := by
    rw [rb48, runBlock_reg _ _ _ (26 : Fin 32) s47.zero (by decide), g47_26]
  have g48_27 : reg n48 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb48, runBlock_reg _ _ _ (27 : Fin 32) s47.zero (by decide), g47_27]
  have g48_10 : reg n48 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by
    rw [rb48]; simp +decide only [runBlock, BInstr.run, svL64e0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g47_2, g47_3, g47_4, g47_8, g47_9, g47_10, g47_11, g47_18, g47_19, g47_20, g47_21, g47_22, g47_23, g47_24, g47_25, g47_26, g47_27, s47.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g48_11 : reg n48 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb48]; simp +decide only [runBlock, BInstr.run, svL64e0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g47_2, g47_3, g47_4, g47_8, g47_9, g47_10, g47_11, g47_18, g47_19, g47_20, g47_21, g47_22, g47_23, g47_24, g47_25, g47_26, g47_27, s47.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w48_40 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := by rw [m48]; exact w47_40
  have w48_88 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m48]; exact w47_88
  have w48_8c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := by rw [m48]; exact w47_8c
  have w48_90 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m48]; exact w47_90
  have w48_94 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := by rw [m48]; exact w47_94
  have w48_180 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m48]; exact w47_180
  have w48_184 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m48]; exact w47_184
  have w48_a20 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := by rw [m48]; exact w47_a20
  have w48_a24 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m48]; exact w47_a24
  have w48_a28 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 0x0 := by rw [m48]; exact w47_a28
  have w48_a2c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m48]; exact w47_a2c
  have w48_a30 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 0x0 := by rw [m48]; exact w47_a30
  have w48_a38 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = BitVec.ofNat 32 0x0 := by rw [m48]; exact w47_a38
  have w48_1320 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m48]; exact w47_1320
  have w48_1324 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m48]; exact w47_1324
  have w48_1328 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m48]; exact w47_1328
  have w48_132c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m48]; exact w47_132c
  have b48_a34 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m48]; exact b47_a34
  clear w47_a38 b47_a34 w47_132c w47_1328 w47_1324 w47_1320 w47_a30 w47_a2c w47_a28 w47_a24 w47_a20 w47_184 w47_180 w47_94 w47_90 w47_8c w47_88 w47_40 g47_27 g47_26 g47_25 g47_24 g47_23 g47_22 g47_21 g47_20 g47_19 g47_18 g47_11 g47_10 g47_9 g47_8 g47_4 g47_3 g47_2 V47 E47 fR47 t47 rg47 W47 K47 fr47 s47 d47
  -- 0x4E4: branch, taken
  obtain ⟨n49, d49, u49⟩ := s48.taken E48.self 0x4DC sv_at_4e4
    (by decide) (by rw [g48_11, s48.zero]; decide)
  have s49 : St n49.mem SV n49 0x4DC (reg n49) := ⟨u49.pc, rfl, fun _ => rfl⟩
  have m49 : n49.mem = n48.mem := u49.mem
  have fr49 : ∀ x, SvR B x → n49.mem x = n48.mem x := fun x _ => by rw [m49]
  have t49 : Steps n0 n49 := t48.trans (.single d49)
  have fR49 : ∀ x, SvR B x → n49.mem x = M0 x := fun x hx => (fr49 x hx).trans (fR48 x hx)
  have E49 : SvCode n49.mem := E48.fr F fr49
  have V49 : SvSaves B n49.mem v := V48.same m49
  have g49_2 : reg n49 sp = B + 0x21A0 := by rw [u49.regs, g48_2]
  have g49_3 : reg n49 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u49.regs, g48_3]
  have g49_4 : reg n49 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u49.regs, g48_4]
  have g49_8 : reg n49 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u49.regs, g48_8]
  have g49_9 : reg n49 (9 : Fin 32) = x9 := by rw [u49.regs, g48_9]
  have g49_10 : reg n49 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [u49.regs, g48_10]
  have g49_11 : reg n49 a1 = BitVec.ofNat 32 0x1 := by rw [u49.regs, g48_11]
  have g49_18 : reg n49 (18 : Fin 32) = out := by rw [u49.regs, g48_18]
  have g49_19 : reg n49 (19 : Fin 32) = bp := by rw [u49.regs, g48_19]
  have g49_20 : reg n49 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u49.regs, g48_20]
  have g49_21 : reg n49 (21 : Fin 32) = kp := by rw [u49.regs, g48_21]
  have g49_22 : reg n49 (22 : Fin 32) = x22 := by rw [u49.regs, g48_22]
  have g49_23 : reg n49 (23 : Fin 32) = x23 := by rw [u49.regs, g48_23]
  have g49_24 : reg n49 (24 : Fin 32) = x24 := by rw [u49.regs, g48_24]
  have g49_25 : reg n49 (25 : Fin 32) = x25 := by rw [u49.regs, g48_25]
  have g49_26 : reg n49 (26 : Fin 32) = ll := by rw [u49.regs, g48_26]
  have g49_27 : reg n49 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u49.regs, g48_27]
  have w49_40 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := by rw [m49]; exact w48_40
  have w49_88 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m49]; exact w48_88
  have w49_8c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := by rw [m49]; exact w48_8c
  have w49_90 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m49]; exact w48_90
  have w49_94 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := by rw [m49]; exact w48_94
  have w49_180 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m49]; exact w48_180
  have w49_184 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m49]; exact w48_184
  have w49_a20 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := by rw [m49]; exact w48_a20
  have w49_a24 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m49]; exact w48_a24
  have w49_a28 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 0x0 := by rw [m49]; exact w48_a28
  have w49_a2c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m49]; exact w48_a2c
  have w49_a30 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 0x0 := by rw [m49]; exact w48_a30
  have w49_a38 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = BitVec.ofNat 32 0x0 := by rw [m49]; exact w48_a38
  have w49_1320 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m49]; exact w48_1320
  have w49_1324 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m49]; exact w48_1324
  have w49_1328 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m49]; exact w48_1328
  have w49_132c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m49]; exact w48_132c
  have b49_a34 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m49]; exact b48_a34
  clear b48_a34 w48_132c w48_1328 w48_1324 w48_1320 w48_a38 w48_a30 w48_a2c w48_a28 w48_a24 w48_a20 w48_184 w48_180 w48_94 w48_90 w48_8c w48_88 w48_40 g48_11 g48_10 g48_27 g48_26 g48_25 g48_24 g48_23 g48_22 g48_21 g48_20 g48_19 g48_18 g48_9 g48_8 g48_4 g48_3 g48_2 V48 E48 fR48 t48 fr48 rb48 s48 m48 u48 c48
  -- 0x4DC: sw
  obtain ⟨n50, d50, s50, fr50, K50, W50, rg50⟩ := sv_sw F E49 s49 sv_at_4dc (off' := 0x4E0) (c := 0xA40)
    (by decide) (by rw [g49_10]; sv_addr) (by decide) (by decide)
  have t50 : Steps n0 n50 := t49.trans d50
  have fR50 : ∀ x, SvR B x → n50.mem x = M0 x := fun x hx => (fr50 x hx).trans (fR49 x hx)
  have E50 : SvCode n50.mem := E49.fr F fr50
  have V50 : SvSaves B n50.mem v := V49.keep K50 (by decide)
  have g50_2 : reg n50 sp = B + 0x21A0 := by rw [rg50 sp, g49_2]
  have g50_3 : reg n50 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg50 (3 : Fin 32), g49_3]
  have g50_4 : reg n50 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg50 (4 : Fin 32), g49_4]
  have g50_8 : reg n50 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg50 (8 : Fin 32), g49_8]
  have g50_9 : reg n50 (9 : Fin 32) = x9 := by rw [rg50 (9 : Fin 32), g49_9]
  have g50_10 : reg n50 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA40 := by rw [rg50 a0, g49_10]
  have g50_11 : reg n50 a1 = BitVec.ofNat 32 0x1 := by rw [rg50 a1, g49_11]
  have g50_18 : reg n50 (18 : Fin 32) = out := by rw [rg50 (18 : Fin 32), g49_18]
  have g50_19 : reg n50 (19 : Fin 32) = bp := by rw [rg50 (19 : Fin 32), g49_19]
  have g50_20 : reg n50 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg50 (20 : Fin 32), g49_20]
  have g50_21 : reg n50 (21 : Fin 32) = kp := by rw [rg50 (21 : Fin 32), g49_21]
  have g50_22 : reg n50 (22 : Fin 32) = x22 := by rw [rg50 (22 : Fin 32), g49_22]
  have g50_23 : reg n50 (23 : Fin 32) = x23 := by rw [rg50 (23 : Fin 32), g49_23]
  have g50_24 : reg n50 (24 : Fin 32) = x24 := by rw [rg50 (24 : Fin 32), g49_24]
  have g50_25 : reg n50 (25 : Fin 32) = x25 := by rw [rg50 (25 : Fin 32), g49_25]
  have g50_26 : reg n50 (26 : Fin 32) = ll := by rw [rg50 (26 : Fin 32), g49_26]
  have g50_27 : reg n50 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg50 (27 : Fin 32), g49_27]
  have w50_40 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := (K50.w32 (by decide) (by decide)).trans w49_40
  have w50_88 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K50.w32 (by decide) (by decide)).trans w49_88
  have w50_8c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := (K50.w32 (by decide) (by decide)).trans w49_8c
  have w50_90 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K50.w32 (by decide) (by decide)).trans w49_90
  have w50_94 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := (K50.w32 (by decide) (by decide)).trans w49_94
  have w50_180 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K50.w32 (by decide) (by decide)).trans w49_180
  have w50_184 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K50.w32 (by decide) (by decide)).trans w49_184
  have w50_a20 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := (K50.w32 (by decide) (by decide)).trans w49_a20
  have w50_a24 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := (K50.w32 (by decide) (by decide)).trans w49_a24
  have w50_a28 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 0x0 := (K50.w32 (by decide) (by decide)).trans w49_a28
  have w50_a2c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := (K50.w32 (by decide) (by decide)).trans w49_a2c
  have w50_a30 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 0x0 := (K50.w32 (by decide) (by decide)).trans w49_a30
  have w50_a38 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = BitVec.ofNat 32 0x0 := (K50.w32 (by decide) (by decide)).trans w49_a38
  have w50_1320 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := (K50.w32 (by decide) (by decide)).trans w49_1320
  have w50_1324 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := (K50.w32 (by decide) (by decide)).trans w49_1324
  have w50_1328 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := (K50.w32 (by decide) (by decide)).trans w49_1328
  have w50_132c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := (K50.w32 (by decide) (by decide)).trans w49_132c
  have b50_a34 : n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := (K50.b8 (by decide) (by decide)).trans b49_a34
  have w50_a40 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 32 0x0 := by rw [W50, s49.zero]; rfl
  clear b49_a34 w49_132c w49_1328 w49_1324 w49_1320 w49_a38 w49_a30 w49_a2c w49_a28 w49_a24 w49_a20 w49_184 w49_180 w49_94 w49_90 w49_8c w49_88 w49_40 g49_27 g49_26 g49_25 g49_24 g49_23 g49_22 g49_21 g49_20 g49_19 g49_18 g49_11 g49_10 g49_9 g49_8 g49_4 g49_3 g49_2 V49 E49 fR49 t49 fr49 m49 s49 u49 d49
  -- 0x4E0
  obtain ⟨n51, c51, u51⟩ := s50.block svL64e0 E50.self svL64e0_end
    ⟨trivial, trivial, trivial⟩
  have m51 : n51.mem = n50.mem := u51.mem
  have s51 : St n51.mem SV n51 0x4E4 (reg n51) := ⟨u51.pc, rfl, fun _ => rfl⟩
  have rb51 : ∀ q, reg n51 q = (runBlock svL64e0 (n50.mem, reg n50)).2 q := fun q => by rw [u51.regs]
  have fr51 : ∀ x, SvR B x → n51.mem x = n50.mem x := fun x _ => by rw [m51]
  have t51 : Steps n0 n51 := t50.trans c51
  have fR51 : ∀ x, SvR B x → n51.mem x = M0 x := fun x hx => (fr51 x hx).trans (fR50 x hx)
  have E51 : SvCode n51.mem := E50.fr F fr51
  have V51 : SvSaves B n51.mem v := V50.same m51
  have g51_2 : reg n51 sp = B + 0x21A0 := by
    rw [rb51, runBlock_reg _ _ _ sp s50.zero (by decide), g50_2]
  have g51_3 : reg n51 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb51, runBlock_reg _ _ _ (3 : Fin 32) s50.zero (by decide), g50_3]
  have g51_4 : reg n51 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb51, runBlock_reg _ _ _ (4 : Fin 32) s50.zero (by decide), g50_4]
  have g51_8 : reg n51 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb51, runBlock_reg _ _ _ (8 : Fin 32) s50.zero (by decide), g50_8]
  have g51_9 : reg n51 (9 : Fin 32) = x9 := by
    rw [rb51, runBlock_reg _ _ _ (9 : Fin 32) s50.zero (by decide), g50_9]
  have g51_18 : reg n51 (18 : Fin 32) = out := by
    rw [rb51, runBlock_reg _ _ _ (18 : Fin 32) s50.zero (by decide), g50_18]
  have g51_19 : reg n51 (19 : Fin 32) = bp := by
    rw [rb51, runBlock_reg _ _ _ (19 : Fin 32) s50.zero (by decide), g50_19]
  have g51_20 : reg n51 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb51, runBlock_reg _ _ _ (20 : Fin 32) s50.zero (by decide), g50_20]
  have g51_21 : reg n51 (21 : Fin 32) = kp := by
    rw [rb51, runBlock_reg _ _ _ (21 : Fin 32) s50.zero (by decide), g50_21]
  have g51_22 : reg n51 (22 : Fin 32) = x22 := by
    rw [rb51, runBlock_reg _ _ _ (22 : Fin 32) s50.zero (by decide), g50_22]
  have g51_23 : reg n51 (23 : Fin 32) = x23 := by
    rw [rb51, runBlock_reg _ _ _ (23 : Fin 32) s50.zero (by decide), g50_23]
  have g51_24 : reg n51 (24 : Fin 32) = x24 := by
    rw [rb51, runBlock_reg _ _ _ (24 : Fin 32) s50.zero (by decide), g50_24]
  have g51_25 : reg n51 (25 : Fin 32) = x25 := by
    rw [rb51, runBlock_reg _ _ _ (25 : Fin 32) s50.zero (by decide), g50_25]
  have g51_26 : reg n51 (26 : Fin 32) = ll := by
    rw [rb51, runBlock_reg _ _ _ (26 : Fin 32) s50.zero (by decide), g50_26]
  have g51_27 : reg n51 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb51, runBlock_reg _ _ _ (27 : Fin 32) s50.zero (by decide), g50_27]
  have g51_10 : reg n51 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA48 := by
    rw [rb51]; simp +decide only [runBlock, BInstr.run, svL64e0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g50_2, g50_3, g50_4, g50_8, g50_9, g50_10, g50_11, g50_18, g50_19, g50_20, g50_21, g50_22, g50_23, g50_24, g50_25, g50_26, g50_27, s50.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g51_11 : reg n51 a1 = BitVec.ofNat 32 0x0 := by
    rw [rb51]; simp +decide only [runBlock, BInstr.run, svL64e0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g50_2, g50_3, g50_4, g50_8, g50_9, g50_10, g50_11, g50_18, g50_19, g50_20, g50_21, g50_22, g50_23, g50_24, g50_25, g50_26, g50_27, s50.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w51_40 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := by rw [m51]; exact w50_40
  have w51_88 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m51]; exact w50_88
  have w51_8c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := by rw [m51]; exact w50_8c
  have w51_90 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m51]; exact w50_90
  have w51_94 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := by rw [m51]; exact w50_94
  have w51_180 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m51]; exact w50_180
  have w51_184 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m51]; exact w50_184
  have w51_a20 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := by rw [m51]; exact w50_a20
  have w51_a24 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m51]; exact w50_a24
  have w51_a28 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 0x0 := by rw [m51]; exact w50_a28
  have w51_a2c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m51]; exact w50_a2c
  have w51_a30 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 0x0 := by rw [m51]; exact w50_a30
  have w51_a38 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = BitVec.ofNat 32 0x0 := by rw [m51]; exact w50_a38
  have w51_a40 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 32 0x0 := by rw [m51]; exact w50_a40
  have w51_1320 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m51]; exact w50_1320
  have w51_1324 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m51]; exact w50_1324
  have w51_1328 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m51]; exact w50_1328
  have w51_132c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m51]; exact w50_132c
  have b51_a34 : n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m51]; exact b50_a34
  clear w50_a40 b50_a34 w50_132c w50_1328 w50_1324 w50_1320 w50_a38 w50_a30 w50_a2c w50_a28 w50_a24 w50_a20 w50_184 w50_180 w50_94 w50_90 w50_8c w50_88 w50_40 g50_27 g50_26 g50_25 g50_24 g50_23 g50_22 g50_21 g50_20 g50_19 g50_18 g50_11 g50_10 g50_9 g50_8 g50_4 g50_3 g50_2 V50 E50 fR50 t50 rg50 W50 K50 fr50 s50 d50
  -- 0x4E4: branch, not taken
  obtain ⟨n52, d52, u52⟩ := s51.notTaken E51.self 0x4E6 sv_at_4e4
    (by decide) (by rw [g51_11, s51.zero]; decide)
  have s52 : St n52.mem SV n52 0x4E6 (reg n52) := ⟨u52.pc, rfl, fun _ => rfl⟩
  have m52 : n52.mem = n51.mem := u52.mem
  have fr52 : ∀ x, SvR B x → n52.mem x = n51.mem x := fun x _ => by rw [m52]
  have t52 : Steps n0 n52 := t51.trans (.single d52)
  have fR52 : ∀ x, SvR B x → n52.mem x = M0 x := fun x hx => (fr52 x hx).trans (fR51 x hx)
  have E52 : SvCode n52.mem := E51.fr F fr52
  have V52 : SvSaves B n52.mem v := V51.same m52
  have g52_2 : reg n52 sp = B + 0x21A0 := by rw [u52.regs, g51_2]
  have g52_3 : reg n52 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u52.regs, g51_3]
  have g52_4 : reg n52 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u52.regs, g51_4]
  have g52_8 : reg n52 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u52.regs, g51_8]
  have g52_9 : reg n52 (9 : Fin 32) = x9 := by rw [u52.regs, g51_9]
  have g52_10 : reg n52 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA48 := by rw [u52.regs, g51_10]
  have g52_11 : reg n52 a1 = BitVec.ofNat 32 0x0 := by rw [u52.regs, g51_11]
  have g52_18 : reg n52 (18 : Fin 32) = out := by rw [u52.regs, g51_18]
  have g52_19 : reg n52 (19 : Fin 32) = bp := by rw [u52.regs, g51_19]
  have g52_20 : reg n52 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u52.regs, g51_20]
  have g52_21 : reg n52 (21 : Fin 32) = kp := by rw [u52.regs, g51_21]
  have g52_22 : reg n52 (22 : Fin 32) = x22 := by rw [u52.regs, g51_22]
  have g52_23 : reg n52 (23 : Fin 32) = x23 := by rw [u52.regs, g51_23]
  have g52_24 : reg n52 (24 : Fin 32) = x24 := by rw [u52.regs, g51_24]
  have g52_25 : reg n52 (25 : Fin 32) = x25 := by rw [u52.regs, g51_25]
  have g52_26 : reg n52 (26 : Fin 32) = ll := by rw [u52.regs, g51_26]
  have g52_27 : reg n52 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u52.regs, g51_27]
  have w52_40 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := by rw [m52]; exact w51_40
  have w52_88 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m52]; exact w51_88
  have w52_8c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := by rw [m52]; exact w51_8c
  have w52_90 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := by rw [m52]; exact w51_90
  have w52_94 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := by rw [m52]; exact w51_94
  have w52_180 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m52]; exact w51_180
  have w52_184 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := by rw [m52]; exact w51_184
  have w52_a20 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := by rw [m52]; exact w51_a20
  have w52_a24 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := by rw [m52]; exact w51_a24
  have w52_a28 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 0x0 := by rw [m52]; exact w51_a28
  have w52_a2c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m52]; exact w51_a2c
  have w52_a30 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 0x0 := by rw [m52]; exact w51_a30
  have w52_a38 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = BitVec.ofNat 32 0x0 := by rw [m52]; exact w51_a38
  have w52_a40 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 32 0x0 := by rw [m52]; exact w51_a40
  have w52_1320 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := by rw [m52]; exact w51_1320
  have w52_1324 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := by rw [m52]; exact w51_1324
  have w52_1328 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m52]; exact w51_1328
  have w52_132c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := by rw [m52]; exact w51_132c
  have b52_a34 : n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := by rw [m52]; exact b51_a34
  clear b51_a34 w51_132c w51_1328 w51_1324 w51_1320 w51_a40 w51_a38 w51_a30 w51_a2c w51_a28 w51_a24 w51_a20 w51_184 w51_180 w51_94 w51_90 w51_8c w51_88 w51_40 g51_11 g51_10 g51_27 g51_26 g51_25 g51_24 g51_23 g51_22 g51_21 g51_20 g51_19 g51_18 g51_9 g51_8 g51_4 g51_3 g51_2 V51 E51 fR51 t51 fr51 rb51 s51 m51 u51 c51
  -- 0x4E6: sw
  obtain ⟨n53, d53, s53, fr53, K53, W53, rg53⟩ := sv_sw F E52 s52 sv_at_4e6 (off' := 0x4E8) (c := 0x34)
    (by decide) (by rw [g52_2]; sv_addr) (by decide) (by decide)
  have t53 : Steps n0 n53 := t52.trans d53
  have fR53 : ∀ x, SvR B x → n53.mem x = M0 x := fun x hx => (fr53 x hx).trans (fR52 x hx)
  have E53 : SvCode n53.mem := E52.fr F fr53
  have V53 : SvSaves B n53.mem v := V52.keep K53 (by decide)
  have g53_2 : reg n53 sp = B + 0x21A0 := by rw [rg53 sp, g52_2]
  have g53_3 : reg n53 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg53 (3 : Fin 32), g52_3]
  have g53_4 : reg n53 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg53 (4 : Fin 32), g52_4]
  have g53_8 : reg n53 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg53 (8 : Fin 32), g52_8]
  have g53_9 : reg n53 (9 : Fin 32) = x9 := by rw [rg53 (9 : Fin 32), g52_9]
  have g53_10 : reg n53 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA48 := by rw [rg53 a0, g52_10]
  have g53_11 : reg n53 a1 = BitVec.ofNat 32 0x0 := by rw [rg53 a1, g52_11]
  have g53_18 : reg n53 (18 : Fin 32) = out := by rw [rg53 (18 : Fin 32), g52_18]
  have g53_19 : reg n53 (19 : Fin 32) = bp := by rw [rg53 (19 : Fin 32), g52_19]
  have g53_20 : reg n53 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg53 (20 : Fin 32), g52_20]
  have g53_21 : reg n53 (21 : Fin 32) = kp := by rw [rg53 (21 : Fin 32), g52_21]
  have g53_22 : reg n53 (22 : Fin 32) = x22 := by rw [rg53 (22 : Fin 32), g52_22]
  have g53_23 : reg n53 (23 : Fin 32) = x23 := by rw [rg53 (23 : Fin 32), g52_23]
  have g53_24 : reg n53 (24 : Fin 32) = x24 := by rw [rg53 (24 : Fin 32), g52_24]
  have g53_25 : reg n53 (25 : Fin 32) = x25 := by rw [rg53 (25 : Fin 32), g52_25]
  have g53_26 : reg n53 (26 : Fin 32) = ll := by rw [rg53 (26 : Fin 32), g52_26]
  have g53_27 : reg n53 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg53 (27 : Fin 32), g52_27]
  have w53_40 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := (K53.w32 (by decide) (by decide)).trans w52_40
  have w53_88 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K53.w32 (by decide) (by decide)).trans w52_88
  have w53_8c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := (K53.w32 (by decide) (by decide)).trans w52_8c
  have w53_90 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K53.w32 (by decide) (by decide)).trans w52_90
  have w53_94 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := (K53.w32 (by decide) (by decide)).trans w52_94
  have w53_180 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K53.w32 (by decide) (by decide)).trans w52_180
  have w53_184 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K53.w32 (by decide) (by decide)).trans w52_184
  have w53_a20 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := (K53.w32 (by decide) (by decide)).trans w52_a20
  have w53_a24 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := (K53.w32 (by decide) (by decide)).trans w52_a24
  have w53_a28 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 0x0 := (K53.w32 (by decide) (by decide)).trans w52_a28
  have w53_a2c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := (K53.w32 (by decide) (by decide)).trans w52_a2c
  have w53_a30 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 0x0 := (K53.w32 (by decide) (by decide)).trans w52_a30
  have w53_a38 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = BitVec.ofNat 32 0x0 := (K53.w32 (by decide) (by decide)).trans w52_a38
  have w53_a40 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 32 0x0 := (K53.w32 (by decide) (by decide)).trans w52_a40
  have w53_1320 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := (K53.w32 (by decide) (by decide)).trans w52_1320
  have w53_1324 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := (K53.w32 (by decide) (by decide)).trans w52_1324
  have w53_1328 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := (K53.w32 (by decide) (by decide)).trans w52_1328
  have w53_132c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := (K53.w32 (by decide) (by decide)).trans w52_132c
  have b53_a34 : n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := (K53.b8 (by decide) (by decide)).trans b52_a34
  have w53_34 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = BitVec.ofNat 32 0x0 := by rw [W53, s52.zero]; rfl
  clear b52_a34 w52_132c w52_1328 w52_1324 w52_1320 w52_a40 w52_a38 w52_a30 w52_a2c w52_a28 w52_a24 w52_a20 w52_184 w52_180 w52_94 w52_90 w52_8c w52_88 w52_40 g52_27 g52_26 g52_25 g52_24 g52_23 g52_22 g52_21 g52_20 g52_19 g52_18 g52_11 g52_10 g52_9 g52_8 g52_4 g52_3 g52_2 V52 E52 fR52 t52 fr52 m52 s52 u52 d52
  -- 0x4E8: sw
  obtain ⟨n54, d54, s54, fr54, K54, W54, rg54⟩ := sv_sw F E53 s53 sv_at_4e8 (off' := 0x4EA) (c := 0x30)
    (by decide) (by rw [g53_2]; sv_addr) (by decide) (by decide)
  have t54 : Steps n0 n54 := t53.trans d54
  have fR54 : ∀ x, SvR B x → n54.mem x = M0 x := fun x hx => (fr54 x hx).trans (fR53 x hx)
  have E54 : SvCode n54.mem := E53.fr F fr54
  have V54 : SvSaves B n54.mem v := V53.keep K54 (by decide)
  have g54_2 : reg n54 sp = B + 0x21A0 := by rw [rg54 sp, g53_2]
  have g54_3 : reg n54 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg54 (3 : Fin 32), g53_3]
  have g54_4 : reg n54 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg54 (4 : Fin 32), g53_4]
  have g54_8 : reg n54 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg54 (8 : Fin 32), g53_8]
  have g54_9 : reg n54 (9 : Fin 32) = x9 := by rw [rg54 (9 : Fin 32), g53_9]
  have g54_10 : reg n54 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA48 := by rw [rg54 a0, g53_10]
  have g54_11 : reg n54 a1 = BitVec.ofNat 32 0x0 := by rw [rg54 a1, g53_11]
  have g54_18 : reg n54 (18 : Fin 32) = out := by rw [rg54 (18 : Fin 32), g53_18]
  have g54_19 : reg n54 (19 : Fin 32) = bp := by rw [rg54 (19 : Fin 32), g53_19]
  have g54_20 : reg n54 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [rg54 (20 : Fin 32), g53_20]
  have g54_21 : reg n54 (21 : Fin 32) = kp := by rw [rg54 (21 : Fin 32), g53_21]
  have g54_22 : reg n54 (22 : Fin 32) = x22 := by rw [rg54 (22 : Fin 32), g53_22]
  have g54_23 : reg n54 (23 : Fin 32) = x23 := by rw [rg54 (23 : Fin 32), g53_23]
  have g54_24 : reg n54 (24 : Fin 32) = x24 := by rw [rg54 (24 : Fin 32), g53_24]
  have g54_25 : reg n54 (25 : Fin 32) = x25 := by rw [rg54 (25 : Fin 32), g53_25]
  have g54_26 : reg n54 (26 : Fin 32) = ll := by rw [rg54 (26 : Fin 32), g53_26]
  have g54_27 : reg n54 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg54 (27 : Fin 32), g53_27]
  have w54_34 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = BitVec.ofNat 32 0x0 := (K54.w32 (by decide) (by decide)).trans w53_34
  have w54_40 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25.len := (K54.w32 (by decide) (by decide)).trans w53_40
  have w54_88 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K54.w32 (by decide) (by decide)).trans w53_88
  have w54_8c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25.len := (K54.w32 (by decide) (by decide)).trans w53_8c
  have w54_90 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 tl25.header := (K54.w32 (by decide) (by decide)).trans w53_90
  have w54_94 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25.len := (K54.w32 (by decide) (by decide)).trans w53_94
  have w54_180 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl9.header + tl9.len) := (K54.w32 (by decide) (by decide)).trans w53_180
  have w54_184 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl9.header + tl9.len) := (K54.w32 (by decide) (by decide)).trans w53_184
  have w54_a20 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 := (K54.w32 (by decide) (by decide)).trans w53_a20
  have w54_a24 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25.len := (K54.w32 (by decide) (by decide)).trans w53_a24
  have w54_a28 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 0x0 := (K54.w32 (by decide) (by decide)).trans w53_a28
  have w54_a2c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25.header + tl25.len) := (K54.w32 (by decide) (by decide)).trans w53_a2c
  have w54_a30 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 0x0 := (K54.w32 (by decide) (by decide)).trans w53_a30
  have w54_a38 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = BitVec.ofNat 32 0x0 := (K54.w32 (by decide) (by decide)).trans w53_a38
  have w54_a40 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 32 0x0 := (K54.w32 (by decide) (by decide)).trans w53_a40
  have w54_1320 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (rp) + BitVec.ofNat 32 tl9.header := (K54.w32 (by decide) (by decide)).trans w53_1320
  have w54_1324 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = BitVec.ofNat 32 tl9.len := (K54.w32 (by decide) (by decide)).trans w53_1324
  have w54_1328 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((rp) + BitVec.ofNat 32 tl9.header) + BitVec.ofNat 32 (tl25.header + tl25.len) := (K54.w32 (by decide) (by decide)).trans w53_1328
  have w54_132c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (BitVec.ofNat 32 tl9.len) - BitVec.ofNat 32 (tl25.header + tl25.len) := (K54.w32 (by decide) (by decide)).trans w53_132c
  have b54_a34 : n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl9.tag := (K54.b8 (by decide) (by decide)).trans b53_a34
  have w54_30 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = BitVec.ofNat 32 0x0 := by rw [W54, s53.zero]; rfl
  clear w53_34 b53_a34 w53_132c w53_1328 w53_1324 w53_1320 w53_a40 w53_a38 w53_a30 w53_a2c w53_a28 w53_a24 w53_a20 w53_184 w53_180 w53_94 w53_90 w53_8c w53_88 w53_40 g53_27 g53_26 g53_25 g53_24 g53_23 g53_22 g53_21 g53_20 g53_19 g53_18 g53_11 g53_10 g53_9 g53_8 g53_4 g53_3 g53_2 V53 E53 fR53 t53 rg53 W53 K53 fr53 s53 d53
  exact .inr ⟨hz_2, hz_5, tl9, hr9, hz_15, tl25, hr25, hz_28, n54, t54, s54, E54, V54, fR54, g54_2, g54_3, g54_4, g54_8, g54_9, g54_18, g54_19, g54_20, g54_21, g54_22, g54_23, g54_24, g54_25, g54_26, g54_27, w54_30, w54_34, w54_40, w54_88, w54_8c, w54_90, w54_94, w54_a20, w54_a24, w54_a28, w54_a2c, w54_a30, w54_a38, w54_a40⟩

end C3.RV32.Sv
