import C3BootProofs.Proofs.SvCkpt

/-!
# `sigstore::verify`: the checkpoint's root hash

From the size's digit loop's end at 0x14FE to the log loop at 0x15C0: the size is below 2^63, and the root line is the base64 of 32 bytes, which go to the word at offset 0x20 and the 31 bytes at offset 0x3E0.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svCke1878 : List BInstr :=
  [.aluImm .add (25 : Fin 32) x0 0x1A]
theorem svCke1878_end : blockEnd sigstoreVerifyCode 0x1878 svCke1878 = some 0x187A := by
  simp only [svCke1878]
  rw [blockEnd, sv_at_1878]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCke1564 : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a2 x0 0x60, .aluImm .add a1 x0 0x0]
theorem svCke1564_end : blockEnd sigstoreVerifyCode 0x1564 svCke1564 = some 0x156E := by
  simp only [svCke1564]
  rw [blockEnd, sv_at_1564]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1568]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_156c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCke1576 : List BInstr :=
  [.aluImm .add a0 sp 0x400, .aluImm .add a3 sp 0x420, .aluImm .add a4 x0 0x60, .alu .add a1 x0 (25 : Fin 32), .alu .add a2 x0 (27 : Fin 32)]
theorem svCke1576_end : blockEnd sigstoreVerifyCode 0x1576 svCke1576 = some 0x1586 := by
  simp only [svCke1576]
  rw [blockEnd, sv_at_1576]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_157a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_157e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1582]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1584]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCke159a : List BInstr :=
  [.aluImm .add a0 a0 0xFFFFFFE0]
theorem svCke159a_end : blockEnd sigstoreVerifyCode 0x159A svCke159a = some 0x159C := by
  simp only [svCke159a]
  rw [blockEnd, sv_at_159a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCke15a6 : List BInstr :=
  [.aluImm .add a1 sp 0x421, .aluImm .add a0 sp 0x3E0, .aluImm .add a2 x0 0x1F]
theorem svCke15a6_end : blockEnd sigstoreVerifyCode 0x15A6 svCke15a6 = some 0x15AE := by
  simp only [svCke15a6]
  rw [blockEnd, sv_at_15a6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_15aa]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_15ac]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCke15b6 : List BInstr :=
  [.aluImm .add a0 (21 : Fin 32) 0x108]
theorem svCke15b6_end : blockEnd sigstoreVerifyCode 0x15B6 svCke15b6 = some 0x15BA := by
  simp only [svCke15b6]
  rw [blockEnd, sv_at_15b6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCke15bc : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x200]
theorem svCke15bc_end : blockEnd sigstoreVerifyCode 0x15BC svCke15bc = some 0x15C0 := by
  simp only [svCke15bc]
  rw [blockEnd, sv_at_15bc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_cke {B out bp x20 x21 x22 x23 x26 c p ckl rl rp w64 w74 : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x14FE (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = c)
    (g0_9 : reg n0 (9 : Fin 32) = ckl)
    (g0_10 : reg n0 a0 = BitVec.ofNat 32 0xA)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = p)
    (g0_25 : reg n0 (25 : Fin 32) = rp)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = rl)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74)
    (hc : c = 0)
    (CK0 : SvCkCode M0)
    (rt_in : SvIn B rp rl.toNat) :
    (¬ ((w74.toNat < 2 ^ 31) ∧ ∃ bs7, base64Decode (memBytes M0 (rp) ((rl).toNat)) = some bs7 ∧ (bs7.length = 32) ∧ True) ∧ SvErrRet B out v n0) ∨
    ((w74.toNat < 2 ^ 31) ∧
    ∃ bs7, base64Decode (memBytes M0 (rp) ((rl).toNat)) = some bs7 ∧
    (bs7.length = 32) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x15C0 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 0x200 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = p ∧
        reg n' (25 : Fin 32) = rp ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = rl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (bs7.getD 0 0)).zeroExtend 32 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (x21) + BitVec.ofNat 32 0x108 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = BitVec.ofNat 8 (bs7.getD 0 0) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (bs7.getD (1 + j) 0)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (bs7.getD j 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60), (0x20, 0x4), (0x3E0, 0x1F), (0x4C, 0x4)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x14FE: branch, taken
  obtain ⟨n1, d1, u1⟩ := s0.taken E0.self 0x155E sv_at_14fe
    (by decide) (by rw [g0_8, s0.zero]; exact br_beq_t hc)
  have s1 : St n1.mem SV n1 0x155E (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, g0_4]
  have g1_8 : reg n1 (8 : Fin 32) = c := by rw [u1.regs, g0_8]
  have g1_9 : reg n1 (9 : Fin 32) = ckl := by rw [u1.regs, g0_9]
  have g1_10 : reg n1 a0 = BitVec.ofNat 32 0xA := by rw [u1.regs, g0_10]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = x20 := by rw [u1.regs, g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = x21 := by rw [u1.regs, g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = x22 := by rw [u1.regs, g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = x23 := by rw [u1.regs, g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = p := by rw [u1.regs, g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = rp := by rw [u1.regs, g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by rw [u1.regs, g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = rl := by rw [u1.regs, g0_27]
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_64 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m1]; exact w0_64
  have w1_74 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m1]; exact w0_74
  -- 0x155E: lw
  obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_155e (off' := 0x1560) (by decide)
    (by rw [g1_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s2 : St n2.mem SV n2 0x1560 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_4]
  have g2_8 : reg n2 (8 : Fin 32) = c := by rw [u2.regs, upd_ne (by decide) (by decide), g1_8]
  have g2_9 : reg n2 (9 : Fin 32) = ckl := by rw [u2.regs, upd_ne (by decide) (by decide), g1_9]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = x20 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = x22 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = x23 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = p := by rw [u2.regs, upd_ne (by decide) (by decide), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = rp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = rl := by rw [u2.regs, upd_ne (by decide) (by decide), g1_27]
  have g2_10 : reg n2 a0 = w74 := by
    rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g1_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr, w1_74]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m2]; exact w1_64
  have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m2]; exact w1_74
  clear w1_74 w1_64 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_10 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  by_cases hsz : w74.toNat < 2 ^ 31
  rotate_left
  · -- 0x1560: branch, taken
    obtain ⟨n3, d3, u3⟩ := s2.taken E2.self 0x1878 sv_at_1560
      (by decide) (by rw [g2_10, s2.zero]; exact br_blt0_t hsz)
    have s3 : St n3.mem SV n3 0x1878 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = n2.mem := u3.mem
    have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
    have t3 : Steps n0 n3 := t2.trans (.single d3)
    have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
    have E3 : SvCode n3.mem := E2.fr F fr3
    have V3 : SvSaves B n3.mem v := V2.same m3
    have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, g2_2]
    have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, g2_3]
    have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, g2_4]
    have g3_8 : reg n3 (8 : Fin 32) = c := by rw [u3.regs, g2_8]
    have g3_9 : reg n3 (9 : Fin 32) = ckl := by rw [u3.regs, g2_9]
    have g3_10 : reg n3 a0 = w74 := by rw [u3.regs, g2_10]
    have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, g2_18]
    have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, g2_19]
    have g3_20 : reg n3 (20 : Fin 32) = x20 := by rw [u3.regs, g2_20]
    have g3_21 : reg n3 (21 : Fin 32) = x21 := by rw [u3.regs, g2_21]
    have g3_22 : reg n3 (22 : Fin 32) = x22 := by rw [u3.regs, g2_22]
    have g3_23 : reg n3 (23 : Fin 32) = x23 := by rw [u3.regs, g2_23]
    have g3_24 : reg n3 (24 : Fin 32) = p := by rw [u3.regs, g2_24]
    have g3_25 : reg n3 (25 : Fin 32) = rp := by rw [u3.regs, g2_25]
    have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [u3.regs, g2_26]
    have g3_27 : reg n3 (27 : Fin 32) = rl := by rw [u3.regs, g2_27]
    have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
    clear keep_kk2
    have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m3]; exact w2_64
    have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m3]; exact w2_74
    clear w2_74 w2_64 g2_10 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
    -- 0x1878
    obtain ⟨n4, c4, u4⟩ := s3.block svCke1878 E3.self svCke1878_end
      ⟨trivial, trivial⟩
    have m4 : n4.mem = n3.mem := u4.mem
    have s4 : St n4.mem SV n4 0x187A (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    have rb4 : ∀ q, reg n4 q = (runBlock svCke1878 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
    have g4_8 : reg n4 (8 : Fin 32) = c := by
      rw [rb4, runBlock_reg _ _ _ (8 : Fin 32) s3.zero (by decide), g3_8]
    have g4_9 : reg n4 (9 : Fin 32) = ckl := by
      rw [rb4, runBlock_reg _ _ _ (9 : Fin 32) s3.zero (by decide), g3_9]
    have g4_10 : reg n4 a0 = w74 := by
      rw [rb4, runBlock_reg _ _ _ a0 s3.zero (by decide), g3_10]
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
    have g4_24 : reg n4 (24 : Fin 32) = p := by
      rw [rb4, runBlock_reg _ _ _ (24 : Fin 32) s3.zero (by decide), g3_24]
    have g4_26 : reg n4 (26 : Fin 32) = x26 := by
      rw [rb4, runBlock_reg _ _ _ (26 : Fin 32) s3.zero (by decide), g3_26]
    have g4_27 : reg n4 (27 : Fin 32) = rl := by
      rw [rb4, runBlock_reg _ _ _ (27 : Fin 32) s3.zero (by decide), g3_27]
    have g4_25 : reg n4 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb4]; simp +decide only [runBlock, BInstr.run, svCke1878, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g3_2, g3_3, g3_4, g3_8, g3_9, g3_10, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, s3.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk4 : SvKeepL B n0.mem n4.mem [] := by rw [m4]; exact keep_kk3
    clear keep_kk3
    have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m4]; exact w3_64
    have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m4]; exact w3_74
    clear w3_74 w3_64 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_10 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
    -- 0x187A: j
    obtain ⟨n5, d5, u5⟩ := s4.jump E4.self sv_at_187a (off' := 0x1882) (by decide)
      (by rw [s4.pc]; decide)
    have s5 : St n5.mem SV n5 0x1882 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
    have m5 : n5.mem = n4.mem := u5.mem
    have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
    have t5 : Steps n0 n5 := t4.trans (.single d5)
    have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
    have E5 : SvCode n5.mem := E4.fr F fr5
    have V5 : SvSaves B n5.mem v := V4.same m5
    have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, g4_2]
    have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, g4_3]
    have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, g4_4]
    have g5_8 : reg n5 (8 : Fin 32) = c := by rw [u5.regs, g4_8]
    have g5_9 : reg n5 (9 : Fin 32) = ckl := by rw [u5.regs, g4_9]
    have g5_10 : reg n5 a0 = w74 := by rw [u5.regs, g4_10]
    have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, g4_18]
    have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, g4_19]
    have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [u5.regs, g4_20]
    have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, g4_21]
    have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [u5.regs, g4_22]
    have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [u5.regs, g4_23]
    have g5_24 : reg n5 (24 : Fin 32) = p := by rw [u5.regs, g4_24]
    have g5_25 : reg n5 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u5.regs, g4_25]
    have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, g4_26]
    have g5_27 : reg n5 (27 : Fin 32) = rl := by rw [u5.regs, g4_27]
    have keep_kk5 : SvKeepL B n0.mem n5.mem [] := by rw [m5]; exact keep_kk4
    clear keep_kk4
    have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m5]; exact w4_64
    have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m5]; exact w4_74
    clear w4_74 w4_64 g4_25 g4_27 g4_26 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hsz h0'), sv_fail_1882 F E5 s5 t5 (fun x hx => (fR5 x hx).trans (fM x hx).symm) V5 hret g5_2 g5_18 hO g5_3 g5_4⟩
  -- 0x1560: branch, not taken
  obtain ⟨n3, d3, u3⟩ := s2.notTaken E2.self 0x1564 sv_at_1560
    (by decide) (by rw [g2_10, s2.zero]; exact br_blt0_f hsz)
  have s3 : St n3.mem SV n3 0x1564 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = c := by rw [u3.regs, g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = ckl := by rw [u3.regs, g2_9]
  have g3_10 : reg n3 a0 = w74 := by rw [u3.regs, g2_10]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = x20 := by rw [u3.regs, g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by rw [u3.regs, g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = x22 := by rw [u3.regs, g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = x23 := by rw [u3.regs, g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = p := by rw [u3.regs, g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = rp := by rw [u3.regs, g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [u3.regs, g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = rl := by rw [u3.regs, g2_27]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m3]; exact w2_64
  have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m3]; exact w2_74
  clear w2_74 w2_64 g2_10 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x1564
  obtain ⟨n4, c4, u4⟩ := s3.block svCke1564 E3.self svCke1564_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem SV n4 0x156E (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock svCke1564 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
  have g4_8 : reg n4 (8 : Fin 32) = c := by
    rw [rb4, runBlock_reg _ _ _ (8 : Fin 32) s3.zero (by decide), g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = ckl := by
    rw [rb4, runBlock_reg _ _ _ (9 : Fin 32) s3.zero (by decide), g3_9]
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
  have g4_24 : reg n4 (24 : Fin 32) = p := by
    rw [rb4, runBlock_reg _ _ _ (24 : Fin 32) s3.zero (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = rp := by
    rw [rb4, runBlock_reg _ _ _ (25 : Fin 32) s3.zero (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by
    rw [rb4, runBlock_reg _ _ _ (26 : Fin 32) s3.zero (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = rl := by
    rw [rb4, runBlock_reg _ _ _ (27 : Fin 32) s3.zero (by decide), g3_27]
  have g4_10 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svCke1564, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_8, g3_9, g3_10, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g4_11 : reg n4 a1 = BitVec.ofNat 32 0x0 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svCke1564, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_8, g3_9, g3_10, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g4_12 : reg n4 a2 = BitVec.ofNat 32 0x60 := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svCke1564, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g3_2, g3_3, g3_4, g3_8, g3_9, g3_10, g3_18, g3_19, g3_20, g3_21, g3_22, g3_23, g3_24, g3_25, g3_26, g3_27, s3.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk4 : SvKeepL B n0.mem n4.mem [] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m4]; exact w3_64
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m4]; exact w3_74
  clear w3_74 w3_64 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_10 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x156E: sv_ms2F
  obtain ⟨n5, c5, s5, rk5, K5, fr5⟩ := sv_ms2F (c := 0x420) (N := 0x60)
    F E4 s4 sv_at_156e sv_at_1572 (by decide) (by decide)
    g4_10 g4_11 g4_12 (by decide)
  have t5 : Steps n0 n5 := t4.trans c5
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.keepL K5 (by decide)
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [rk5 sp (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk5 (3 : Fin 32) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk5 (4 : Fin 32) (by decide), g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = c := by rw [rk5 (8 : Fin 32) (by decide), g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = ckl := by rw [rk5 (9 : Fin 32) (by decide), g4_9]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [rk5 (18 : Fin 32) (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [rk5 (19 : Fin 32) (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [rk5 (20 : Fin 32) (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [rk5 (21 : Fin 32) (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [rk5 (22 : Fin 32) (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [rk5 (23 : Fin 32) (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = p := by rw [rk5 (24 : Fin 32) (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = rp := by rw [rk5 (25 : Fin 32) (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [rk5 (26 : Fin 32) (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = rl := by rw [rk5 (27 : Fin 32) (by decide), g4_27]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x420, 0x60)] := keep_kk4.trans K5
  clear keep_kk4
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K5.w32 (by decide) (by decide)).trans w4_64
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K5.w32 (by decide) (by decide)).trans w4_74
  clear w4_74 w4_64 g4_12 g4_11 g4_10 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  -- 0x1576
  obtain ⟨n6, c6, u6⟩ := s5.block svCke1576 E5.self svCke1576_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem SV n6 0x1586 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock svCke1576 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
  have g6_8 : reg n6 (8 : Fin 32) = c := by
    rw [rb6, runBlock_reg _ _ _ (8 : Fin 32) s5.zero (by decide), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = ckl := by
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
  have g6_24 : reg n6 (24 : Fin 32) = p := by
    rw [rb6, runBlock_reg _ _ _ (24 : Fin 32) s5.zero (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = rp := by
    rw [rb6, runBlock_reg _ _ _ (25 : Fin 32) s5.zero (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by
    rw [rb6, runBlock_reg _ _ _ (26 : Fin 32) s5.zero (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = rl := by
    rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
  have g6_10 : reg n6 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svCke1576, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g6_11 : reg n6 a1 = rp := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svCke1576, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g6_12 : reg n6 a2 = rl := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svCke1576, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g6_13 : reg n6 a3 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svCke1576, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g6_14 : reg n6 a4 = BitVec.ofNat 32 0x60 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svCke1576, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x420, 0x60)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m6]; exact w5_64
  have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m6]; exact w5_74
  clear w5_74 w5_64 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 K5 rk5 s5 c5
  -- 0x1586: sv_b64F
  obtain ⟨n7, c7, s7, sp7, rk7, K7, Ok7, Bad7, fr7⟩ := sv_b64F (rc := 0x400) (oc := 0x420) (nl := (rl).toNat) (L := 0x60)
    F E6 (CK0.sv FW fR6) s6 sv_at_1586 sv_at_158a (by decide) (by decide) g6_2
    g6_10 g6_11 (by rw [g6_12, ofNat_toNat_self]) g6_13 g6_14
    (by decide) (by decide) (by decide) (by decide) (.inl rt_in)
  have t7 : Steps n0 n7 := t6.trans c7
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.keepL K7 (by decide)
  rw [sv_mbRo FW fR6 (.inl rt_in)] at Ok7 Bad7
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk7 (3 : Fin 32) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk7 (4 : Fin 32) (by decide), g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = c := by rw [rk7 (8 : Fin 32) (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = ckl := by rw [rk7 (9 : Fin 32) (by decide), g6_9]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [rk7 (18 : Fin 32) (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [rk7 (19 : Fin 32) (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [rk7 (20 : Fin 32) (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [rk7 (21 : Fin 32) (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [rk7 (22 : Fin 32) (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [rk7 (23 : Fin 32) (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = p := by rw [rk7 (24 : Fin 32) (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = rp := by rw [rk7 (25 : Fin 32) (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [rk7 (26 : Fin 32) (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = rl := by rw [rk7 (27 : Fin 32) (by decide), g6_27]
  have g7_2 : reg n7 sp = B + 0x21A0 := sp7
  obtain ⟨r7, hr7⟩ : ∃ r, base64Decode (memBytes M0 (rp) ((rl).toNat)) = r := ⟨_, rfl⟩
  rcases r7 with _ | bs7
  · have z7 := Bad7 fun b h => by rw [hr7] at h; cases h
    have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := keep_kk6.trans K7
    clear keep_kk6
    have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K7.w32 (by decide) (by decide)).trans w6_64
    have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K7.w32 (by decide) (by decide)).trans w6_74
    have b7_400 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := z7
    clear w6_74 w6_64 g6_14 g6_13 g6_12 g6_11 g6_10 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
    -- 0x158E: lbu
    obtain ⟨n8, d8, u8⟩ := s7.lbu E7.self sv_at_158e (off' := 0x1592) (by decide)
    have s8 : St n8.mem SV n8 0x1592 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
    have m8 : n8.mem = n7.mem := u8.mem
    have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
    have t8 : Steps n0 n8 := t7.trans (.single d8)
    have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
    have E8 : SvCode n8.mem := E7.fr F fr8
    have V8 : SvSaves B n8.mem v := V7.same m8
    have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_2]
    have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_3]
    have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_4]
    have g8_8 : reg n8 (8 : Fin 32) = c := by rw [u8.regs, upd_ne (by decide) (by decide), g7_8]
    have g8_9 : reg n8 (9 : Fin 32) = ckl := by rw [u8.regs, upd_ne (by decide) (by decide), g7_9]
    have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, upd_ne (by decide) (by decide), g7_18]
    have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_19]
    have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_20]
    have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_21]
    have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_22]
    have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_23]
    have g8_24 : reg n8 (24 : Fin 32) = p := by rw [u8.regs, upd_ne (by decide) (by decide), g7_24]
    have g8_25 : reg n8 (25 : Fin 32) = rp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_25]
    have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_26]
    have g8_27 : reg n8 (27 : Fin 32) = rl := by rw [u8.regs, upd_ne (by decide) (by decide), g7_27]
    have g8_10 : reg n8 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g7_2, show B + 0x21A0 + 0x400 = B + 0x21A0 + BitVec.ofNat 32 0x400 by sv_addr, b7_400]
    have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m8]; exact keep_kk7
    clear keep_kk7
    have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m8]; exact w7_64
    have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m8]; exact w7_74
    have b8_400 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := by rw [m8]; exact b7_400
    clear b7_400 w7_74 w7_64 z7
    -- 0x1592: branch, taken
    obtain ⟨n9, d9, u9⟩ := s8.taken E8.self 0x1878 sv_at_1592
      (by decide) (by rw [g8_10, s8.zero]; decide)
    have s9 : St n9.mem SV n9 0x1878 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have m9 : n9.mem = n8.mem := u9.mem
    have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
    have t9 : Steps n0 n9 := t8.trans (.single d9)
    have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
    have E9 : SvCode n9.mem := E8.fr F fr9
    have V9 : SvSaves B n9.mem v := V8.same m9
    have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, g8_2]
    have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, g8_3]
    have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, g8_4]
    have g9_8 : reg n9 (8 : Fin 32) = c := by rw [u9.regs, g8_8]
    have g9_9 : reg n9 (9 : Fin 32) = ckl := by rw [u9.regs, g8_9]
    have g9_10 : reg n9 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u9.regs, g8_10]
    have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, g8_19]
    have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [u9.regs, g8_20]
    have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [u9.regs, g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [u9.regs, g8_23]
    have g9_24 : reg n9 (24 : Fin 32) = p := by rw [u9.regs, g8_24]
    have g9_25 : reg n9 (25 : Fin 32) = rp := by rw [u9.regs, g8_25]
    have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [u9.regs, g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = rl := by rw [u9.regs, g8_27]
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m9]; exact keep_kk8
    clear keep_kk8
    have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m9]; exact w8_64
    have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m9]; exact w8_74
    have b9_400 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := by rw [m9]; exact b8_400
    clear b8_400 w8_74 w8_64 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
    -- 0x1878
    obtain ⟨n10, c10, u10⟩ := s9.block svCke1878 E9.self svCke1878_end
      ⟨trivial, trivial⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have s10 : St n10.mem SV n10 0x187A (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have rb10 : ∀ q, reg n10 q = (runBlock svCke1878 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
    have g10_8 : reg n10 (8 : Fin 32) = c := by
      rw [rb10, runBlock_reg _ _ _ (8 : Fin 32) s9.zero (by decide), g9_8]
    have g10_9 : reg n10 (9 : Fin 32) = ckl := by
      rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
    have g10_10 : reg n10 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [rb10, runBlock_reg _ _ _ a0 s9.zero (by decide), g9_10]
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
    have g10_24 : reg n10 (24 : Fin 32) = p := by
      rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
    have g10_26 : reg n10 (26 : Fin 32) = x26 := by
      rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = rl := by
      rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
    have g10_25 : reg n10 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb10]; simp +decide only [runBlock, BInstr.run, svCke1878, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_10, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m10]; exact w9_64
    have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m10]; exact w9_74
    have b10_400 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := by rw [m10]; exact b9_400
    clear b9_400 w9_74 w9_64 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
    -- 0x187A: j
    obtain ⟨n11, d11, u11⟩ := s10.jump E10.self sv_at_187a (off' := 0x1882) (by decide)
      (by rw [s10.pc]; decide)
    have s11 : St n11.mem SV n11 0x1882 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
    have g11_8 : reg n11 (8 : Fin 32) = c := by rw [u11.regs, g10_8]
    have g11_9 : reg n11 (9 : Fin 32) = ckl := by rw [u11.regs, g10_9]
    have g11_10 : reg n11 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u11.regs, g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [u11.regs, g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = p := by rw [u11.regs, g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u11.regs, g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = rl := by rw [u11.regs, g10_27]
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m11]; exact w10_64
    have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m11]; exact w10_74
    have b11_400 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := by rw [m11]; exact b10_400
    clear b10_400 w10_74 w10_64 g10_25 g10_27 g10_26 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
    exact .inl ⟨(fun ⟨h0', bs7', h1', _⟩ => by rw [hr7] at h1'; cases h1'), sv_fail_1882 F E11 s11 t11 (fun x hx => (fR11 x hx).trans (fM x hx).symm) V11 hret g11_2 g11_18 hO g11_3 g11_4⟩
  by_cases hl32 : bs7.length = 32
  rotate_left
  · by_cases hle : bs7.length ≤ 0x60
    rotate_left
    · have z7 := Bad7 fun b h => by rw [hr7] at h; cases h; omega
      have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := keep_kk6.trans K7
      clear keep_kk6
      have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K7.w32 (by decide) (by decide)).trans w6_64
      have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K7.w32 (by decide) (by decide)).trans w6_74
      have b7_400 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := z7
      clear w6_74 w6_64 g6_14 g6_13 g6_12 g6_11 g6_10 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
      -- 0x158E: lbu
      obtain ⟨n8, d8, u8⟩ := s7.lbu E7.self sv_at_158e (off' := 0x1592) (by decide)
      have s8 : St n8.mem SV n8 0x1592 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
      have m8 : n8.mem = n7.mem := u8.mem
      have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
      have t8 : Steps n0 n8 := t7.trans (.single d8)
      have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
      have E8 : SvCode n8.mem := E7.fr F fr8
      have V8 : SvSaves B n8.mem v := V7.same m8
      have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_2]
      have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_3]
      have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_4]
      have g8_8 : reg n8 (8 : Fin 32) = c := by rw [u8.regs, upd_ne (by decide) (by decide), g7_8]
      have g8_9 : reg n8 (9 : Fin 32) = ckl := by rw [u8.regs, upd_ne (by decide) (by decide), g7_9]
      have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, upd_ne (by decide) (by decide), g7_18]
      have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_19]
      have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_20]
      have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_21]
      have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_22]
      have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_23]
      have g8_24 : reg n8 (24 : Fin 32) = p := by rw [u8.regs, upd_ne (by decide) (by decide), g7_24]
      have g8_25 : reg n8 (25 : Fin 32) = rp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_25]
      have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_26]
      have g8_27 : reg n8 (27 : Fin 32) = rl := by rw [u8.regs, upd_ne (by decide) (by decide), g7_27]
      have g8_10 : reg n8 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
        rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
        rw [g7_2, show B + 0x21A0 + 0x400 = B + 0x21A0 + BitVec.ofNat 32 0x400 by sv_addr, b7_400]
      have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m8]; exact keep_kk7
      clear keep_kk7
      have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m8]; exact w7_64
      have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m8]; exact w7_74
      have b8_400 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := by rw [m8]; exact b7_400
      clear b7_400 w7_74 w7_64 z7
      -- 0x1592: branch, taken
      obtain ⟨n9, d9, u9⟩ := s8.taken E8.self 0x1878 sv_at_1592
        (by decide) (by rw [g8_10, s8.zero]; decide)
      have s9 : St n9.mem SV n9 0x1878 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
      have m9 : n9.mem = n8.mem := u9.mem
      have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
      have t9 : Steps n0 n9 := t8.trans (.single d9)
      have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
      have E9 : SvCode n9.mem := E8.fr F fr9
      have V9 : SvSaves B n9.mem v := V8.same m9
      have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, g8_2]
      have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, g8_3]
      have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, g8_4]
      have g9_8 : reg n9 (8 : Fin 32) = c := by rw [u9.regs, g8_8]
      have g9_9 : reg n9 (9 : Fin 32) = ckl := by rw [u9.regs, g8_9]
      have g9_10 : reg n9 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u9.regs, g8_10]
      have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, g8_18]
      have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, g8_19]
      have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [u9.regs, g8_20]
      have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, g8_21]
      have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [u9.regs, g8_22]
      have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [u9.regs, g8_23]
      have g9_24 : reg n9 (24 : Fin 32) = p := by rw [u9.regs, g8_24]
      have g9_25 : reg n9 (25 : Fin 32) = rp := by rw [u9.regs, g8_25]
      have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [u9.regs, g8_26]
      have g9_27 : reg n9 (27 : Fin 32) = rl := by rw [u9.regs, g8_27]
      have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m9]; exact keep_kk8
      clear keep_kk8
      have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m9]; exact w8_64
      have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m9]; exact w8_74
      have b9_400 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := by rw [m9]; exact b8_400
      clear b8_400 w8_74 w8_64 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
      -- 0x1878
      obtain ⟨n10, c10, u10⟩ := s9.block svCke1878 E9.self svCke1878_end
        ⟨trivial, trivial⟩
      have m10 : n10.mem = n9.mem := u10.mem
      have s10 : St n10.mem SV n10 0x187A (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
      have rb10 : ∀ q, reg n10 q = (runBlock svCke1878 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
      have g10_8 : reg n10 (8 : Fin 32) = c := by
        rw [rb10, runBlock_reg _ _ _ (8 : Fin 32) s9.zero (by decide), g9_8]
      have g10_9 : reg n10 (9 : Fin 32) = ckl := by
        rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
      have g10_10 : reg n10 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
        rw [rb10, runBlock_reg _ _ _ a0 s9.zero (by decide), g9_10]
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
      have g10_24 : reg n10 (24 : Fin 32) = p := by
        rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
      have g10_26 : reg n10 (26 : Fin 32) = x26 := by
        rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
      have g10_27 : reg n10 (27 : Fin 32) = rl := by
        rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
      have g10_25 : reg n10 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
        rw [rb10]; simp +decide only [runBlock, BInstr.run, svCke1878, upd, ↓reduceIte, aluEval]
        all_goals (try simp only [g9_2, g9_3, g9_4, g9_8, g9_9, g9_10, g9_18, g9_19, g9_20, g9_21, g9_22, g9_23, g9_24, g9_25, g9_26, g9_27, s9.zero])
        all_goals first | with_reducible rfl | sv_addr | decide
      have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m10]; exact keep_kk9
      clear keep_kk9
      have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m10]; exact w9_64
      have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m10]; exact w9_74
      have b10_400 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := by rw [m10]; exact b9_400
      clear b9_400 w9_74 w9_64 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
      -- 0x187A: j
      obtain ⟨n11, d11, u11⟩ := s10.jump E10.self sv_at_187a (off' := 0x1882) (by decide)
        (by rw [s10.pc]; decide)
      have s11 : St n11.mem SV n11 0x1882 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
      have m11 : n11.mem = n10.mem := u11.mem
      have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
      have t11 : Steps n0 n11 := t10.trans (.single d11)
      have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
      have E11 : SvCode n11.mem := E10.fr F fr11
      have V11 : SvSaves B n11.mem v := V10.same m11
      have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, g10_2]
      have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, g10_3]
      have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, g10_4]
      have g11_8 : reg n11 (8 : Fin 32) = c := by rw [u11.regs, g10_8]
      have g11_9 : reg n11 (9 : Fin 32) = ckl := by rw [u11.regs, g10_9]
      have g11_10 : reg n11 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u11.regs, g10_10]
      have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, g10_18]
      have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, g10_19]
      have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [u11.regs, g10_20]
      have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, g10_21]
      have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, g10_22]
      have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [u11.regs, g10_23]
      have g11_24 : reg n11 (24 : Fin 32) = p := by rw [u11.regs, g10_24]
      have g11_25 : reg n11 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u11.regs, g10_25]
      have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, g10_26]
      have g11_27 : reg n11 (27 : Fin 32) = rl := by rw [u11.regs, g10_27]
      have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m11]; exact keep_kk10
      clear keep_kk10
      have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m11]; exact w10_64
      have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m11]; exact w10_74
      have b11_400 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (1 : BitVec 8) := by rw [m11]; exact b10_400
      clear b10_400 w10_74 w10_64 g10_25 g10_27 g10_26 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
      exact .inl ⟨(fun ⟨h0', bs7', h1', h2', _⟩ => by rw [hr7] at h1'; cases h1'; exact hl32 h2'), sv_fail_1882 F E11 s11 t11 (fun x hx => (fR11 x hx).trans (fM x hx).symm) V11 hret g11_2 g11_18 hO g11_3 g11_4⟩
    obtain ⟨b0_7, b4_7, -⟩ := Ok7 bs7 hr7 hle
    have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := keep_kk6.trans K7
    clear keep_kk6
    have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K7.w32 (by decide) (by decide)).trans w6_64
    have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K7.w32 (by decide) (by decide)).trans w6_74
    have w7_404 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := b4_7
    have b7_400 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := b0_7
    clear w6_74 w6_64 g6_14 g6_13 g6_12 g6_11 g6_10 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
    -- 0x158E: lbu
    obtain ⟨n8, d8, u8⟩ := s7.lbu E7.self sv_at_158e (off' := 0x1592) (by decide)
    have s8 : St n8.mem SV n8 0x1592 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
    have m8 : n8.mem = n7.mem := u8.mem
    have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
    have t8 : Steps n0 n8 := t7.trans (.single d8)
    have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
    have E8 : SvCode n8.mem := E7.fr F fr8
    have V8 : SvSaves B n8.mem v := V7.same m8
    have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_2]
    have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_3]
    have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_4]
    have g8_8 : reg n8 (8 : Fin 32) = c := by rw [u8.regs, upd_ne (by decide) (by decide), g7_8]
    have g8_9 : reg n8 (9 : Fin 32) = ckl := by rw [u8.regs, upd_ne (by decide) (by decide), g7_9]
    have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, upd_ne (by decide) (by decide), g7_18]
    have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_19]
    have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_20]
    have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_21]
    have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_22]
    have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_23]
    have g8_24 : reg n8 (24 : Fin 32) = p := by rw [u8.regs, upd_ne (by decide) (by decide), g7_24]
    have g8_25 : reg n8 (25 : Fin 32) = rp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_25]
    have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_26]
    have g8_27 : reg n8 (27 : Fin 32) = rl := by rw [u8.regs, upd_ne (by decide) (by decide), g7_27]
    have g8_10 : reg n8 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
      rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g7_2, show B + 0x21A0 + 0x400 = B + 0x21A0 + BitVec.ofNat 32 0x400 by sv_addr, b7_400]
    have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m8]; exact keep_kk7
    clear keep_kk7
    have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m8]; exact w7_64
    have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m8]; exact w7_74
    have w8_404 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := by rw [m8]; exact w7_404
    have b8_400 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m8]; exact b7_400
    clear b7_400 w7_404 w7_74 w7_64 b4_7 b0_7
    -- 0x1592: branch, not taken
    obtain ⟨n9, d9, u9⟩ := s8.notTaken E8.self 0x1596 sv_at_1592
      (by decide) (by rw [g8_10, s8.zero]; decide)
    have s9 : St n9.mem SV n9 0x1596 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have m9 : n9.mem = n8.mem := u9.mem
    have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
    have t9 : Steps n0 n9 := t8.trans (.single d9)
    have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
    have E9 : SvCode n9.mem := E8.fr F fr9
    have V9 : SvSaves B n9.mem v := V8.same m9
    have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, g8_2]
    have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, g8_3]
    have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, g8_4]
    have g9_8 : reg n9 (8 : Fin 32) = c := by rw [u9.regs, g8_8]
    have g9_9 : reg n9 (9 : Fin 32) = ckl := by rw [u9.regs, g8_9]
    have g9_10 : reg n9 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u9.regs, g8_10]
    have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, g8_19]
    have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [u9.regs, g8_20]
    have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [u9.regs, g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [u9.regs, g8_23]
    have g9_24 : reg n9 (24 : Fin 32) = p := by rw [u9.regs, g8_24]
    have g9_25 : reg n9 (25 : Fin 32) = rp := by rw [u9.regs, g8_25]
    have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [u9.regs, g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = rl := by rw [u9.regs, g8_27]
    have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m9]; exact keep_kk8
    clear keep_kk8
    have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m9]; exact w8_64
    have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m9]; exact w8_74
    have w9_404 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := by rw [m9]; exact w8_404
    have b9_400 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m9]; exact b8_400
    clear b8_400 w8_404 w8_74 w8_64 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
    -- 0x1596: lw
    obtain ⟨n10, d10, u10⟩ := s9.lw E9.self sv_at_1596 (off' := 0x159A) (by decide)
      (by rw [g9_2, show B + 0x21A0 + 0x404 = B + 0x21A0 + BitVec.ofNat 32 0x404 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s10 : St n10.mem SV n10 0x159A (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
    have t10 : Steps n0 n10 := t9.trans (.single d10)
    have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : SvCode n10.mem := E9.fr F fr10
    have V10 : SvSaves B n10.mem v := V9.same m10
    have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_4]
    have g10_8 : reg n10 (8 : Fin 32) = c := by rw [u10.regs, upd_ne (by decide) (by decide), g9_8]
    have g10_9 : reg n10 (9 : Fin 32) = ckl := by rw [u10.regs, upd_ne (by decide) (by decide), g9_9]
    have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, upd_ne (by decide) (by decide), g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_19]
    have g10_20 : reg n10 (20 : Fin 32) = x20 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_20]
    have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_22]
    have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_23]
    have g10_24 : reg n10 (24 : Fin 32) = p := by rw [u10.regs, upd_ne (by decide) (by decide), g9_24]
    have g10_25 : reg n10 (25 : Fin 32) = rp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_25]
    have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = rl := by rw [u10.regs, upd_ne (by decide) (by decide), g9_27]
    have g10_10 : reg n10 a0 = BitVec.ofNat 32 bs7.length := by
      rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g9_2, show B + 0x21A0 + 0x404 = B + 0x21A0 + BitVec.ofNat 32 0x404 by sv_addr, w9_404]
    have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m10]; exact keep_kk9
    clear keep_kk9
    have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m10]; exact w9_64
    have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m10]; exact w9_74
    have w10_404 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := by rw [m10]; exact w9_404
    have b10_400 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m10]; exact b9_400
    clear b9_400 w9_404 w9_74 w9_64 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
    -- 0x159A
    obtain ⟨n11, c11, u11⟩ := s10.block svCke159a E10.self svCke159a_end
      ⟨trivial, trivial⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have s11 : St n11.mem SV n11 0x159C (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have rb11 : ∀ q, reg n11 q = (runBlock svCke159a (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans c11
    have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by
      rw [rb11, runBlock_reg _ _ _ sp s10.zero (by decide), g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb11, runBlock_reg _ _ _ (3 : Fin 32) s10.zero (by decide), g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb11, runBlock_reg _ _ _ (4 : Fin 32) s10.zero (by decide), g10_4]
    have g11_8 : reg n11 (8 : Fin 32) = c := by
      rw [rb11, runBlock_reg _ _ _ (8 : Fin 32) s10.zero (by decide), g10_8]
    have g11_9 : reg n11 (9 : Fin 32) = ckl := by
      rw [rb11, runBlock_reg _ _ _ (9 : Fin 32) s10.zero (by decide), g10_9]
    have g11_18 : reg n11 (18 : Fin 32) = out := by
      rw [rb11, runBlock_reg _ _ _ (18 : Fin 32) s10.zero (by decide), g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by
      rw [rb11, runBlock_reg _ _ _ (19 : Fin 32) s10.zero (by decide), g10_19]
    have g11_20 : reg n11 (20 : Fin 32) = x20 := by
      rw [rb11, runBlock_reg _ _ _ (20 : Fin 32) s10.zero (by decide), g10_20]
    have g11_21 : reg n11 (21 : Fin 32) = x21 := by
      rw [rb11, runBlock_reg _ _ _ (21 : Fin 32) s10.zero (by decide), g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = x22 := by
      rw [rb11, runBlock_reg _ _ _ (22 : Fin 32) s10.zero (by decide), g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = x23 := by
      rw [rb11, runBlock_reg _ _ _ (23 : Fin 32) s10.zero (by decide), g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = p := by
      rw [rb11, runBlock_reg _ _ _ (24 : Fin 32) s10.zero (by decide), g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = rp := by
      rw [rb11, runBlock_reg _ _ _ (25 : Fin 32) s10.zero (by decide), g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = x26 := by
      rw [rb11, runBlock_reg _ _ _ (26 : Fin 32) s10.zero (by decide), g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = rl := by
      rw [rb11, runBlock_reg _ _ _ (27 : Fin 32) s10.zero (by decide), g10_27]
    have g11_10 : reg n11 a0 = (BitVec.ofNat 32 bs7.length) + BitVec.ofNat 32 0xFFFFFFE0 := by
      rw [rb11]; simp +decide only [runBlock, BInstr.run, svCke159a, upd, ↓reduceIte]; rw [g10_10] <;> rfl
    have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m11]; exact keep_kk10
    clear keep_kk10
    have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m11]; exact w10_64
    have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m11]; exact w10_74
    have w11_404 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := by rw [m11]; exact w10_404
    have b11_400 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m11]; exact b10_400
    clear b10_400 w10_404 w10_74 w10_64 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
    -- 0x159C: branch, taken
    obtain ⟨n12, d12, u12⟩ := s11.taken E11.self 0x1878 sv_at_159c
      (by decide) (by rw [g11_10, s11.zero]; exact br_bne_t (ne32_add (by omega) hl32))
    have s12 : St n12.mem SV n12 0x1878 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
    have t12 : Steps n0 n12 := t11.trans (.single d12)
    have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
    have E12 : SvCode n12.mem := E11.fr F fr12
    have V12 : SvSaves B n12.mem v := V11.same m12
    have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, g11_2]
    have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, g11_3]
    have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, g11_4]
    have g12_8 : reg n12 (8 : Fin 32) = c := by rw [u12.regs, g11_8]
    have g12_9 : reg n12 (9 : Fin 32) = ckl := by rw [u12.regs, g11_9]
    have g12_10 : reg n12 a0 = (BitVec.ofNat 32 bs7.length) + BitVec.ofNat 32 0xFFFFFFE0 := by rw [u12.regs, g11_10]
    have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, g11_18]
    have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, g11_19]
    have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [u12.regs, g11_20]
    have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, g11_21]
    have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [u12.regs, g11_22]
    have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [u12.regs, g11_23]
    have g12_24 : reg n12 (24 : Fin 32) = p := by rw [u12.regs, g11_24]
    have g12_25 : reg n12 (25 : Fin 32) = rp := by rw [u12.regs, g11_25]
    have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [u12.regs, g11_26]
    have g12_27 : reg n12 (27 : Fin 32) = rl := by rw [u12.regs, g11_27]
    have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m12]; exact keep_kk11
    clear keep_kk11
    have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m12]; exact w11_64
    have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m12]; exact w11_74
    have w12_404 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := by rw [m12]; exact w11_404
    have b12_400 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m12]; exact b11_400
    clear b11_400 w11_404 w11_74 w11_64 g11_10 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 rb11 s11 m11 u11 c11
    -- 0x1878
    obtain ⟨n13, c13, u13⟩ := s12.block svCke1878 E12.self svCke1878_end
      ⟨trivial, trivial⟩
    have m13 : n13.mem = n12.mem := u13.mem
    have s13 : St n13.mem SV n13 0x187A (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
    have rb13 : ∀ q, reg n13 q = (runBlock svCke1878 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
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
    have g13_8 : reg n13 (8 : Fin 32) = c := by
      rw [rb13, runBlock_reg _ _ _ (8 : Fin 32) s12.zero (by decide), g12_8]
    have g13_9 : reg n13 (9 : Fin 32) = ckl := by
      rw [rb13, runBlock_reg _ _ _ (9 : Fin 32) s12.zero (by decide), g12_9]
    have g13_10 : reg n13 a0 = (BitVec.ofNat 32 bs7.length) + BitVec.ofNat 32 0xFFFFFFE0 := by
      rw [rb13, runBlock_reg _ _ _ a0 s12.zero (by decide), g12_10]
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
    have g13_24 : reg n13 (24 : Fin 32) = p := by
      rw [rb13, runBlock_reg _ _ _ (24 : Fin 32) s12.zero (by decide), g12_24]
    have g13_26 : reg n13 (26 : Fin 32) = x26 := by
      rw [rb13, runBlock_reg _ _ _ (26 : Fin 32) s12.zero (by decide), g12_26]
    have g13_27 : reg n13 (27 : Fin 32) = rl := by
      rw [rb13, runBlock_reg _ _ _ (27 : Fin 32) s12.zero (by decide), g12_27]
    have g13_25 : reg n13 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb13]; simp +decide only [runBlock, BInstr.run, svCke1878, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_10, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m13]; exact keep_kk12
    clear keep_kk12
    have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m13]; exact w12_64
    have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m13]; exact w12_74
    have w13_404 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := by rw [m13]; exact w12_404
    have b13_400 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m13]; exact b12_400
    clear b12_400 w12_404 w12_74 w12_64 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_10 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
    -- 0x187A: j
    obtain ⟨n14, d14, u14⟩ := s13.jump E13.self sv_at_187a (off' := 0x1882) (by decide)
      (by rw [s13.pc]; decide)
    have s14 : St n14.mem SV n14 0x1882 (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
    have m14 : n14.mem = n13.mem := u14.mem
    have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
    have t14 : Steps n0 n14 := t13.trans (.single d14)
    have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
    have E14 : SvCode n14.mem := E13.fr F fr14
    have V14 : SvSaves B n14.mem v := V13.same m14
    have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, g13_2]
    have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, g13_3]
    have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, g13_4]
    have g14_8 : reg n14 (8 : Fin 32) = c := by rw [u14.regs, g13_8]
    have g14_9 : reg n14 (9 : Fin 32) = ckl := by rw [u14.regs, g13_9]
    have g14_10 : reg n14 a0 = (BitVec.ofNat 32 bs7.length) + BitVec.ofNat 32 0xFFFFFFE0 := by rw [u14.regs, g13_10]
    have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, g13_18]
    have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, g13_19]
    have g14_20 : reg n14 (20 : Fin 32) = x20 := by rw [u14.regs, g13_20]
    have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [u14.regs, g13_21]
    have g14_22 : reg n14 (22 : Fin 32) = x22 := by rw [u14.regs, g13_22]
    have g14_23 : reg n14 (23 : Fin 32) = x23 := by rw [u14.regs, g13_23]
    have g14_24 : reg n14 (24 : Fin 32) = p := by rw [u14.regs, g13_24]
    have g14_25 : reg n14 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u14.regs, g13_25]
    have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [u14.regs, g13_26]
    have g14_27 : reg n14 (27 : Fin 32) = rl := by rw [u14.regs, g13_27]
    have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m14]; exact keep_kk13
    clear keep_kk13
    have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m14]; exact w13_64
    have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m14]; exact w13_74
    have w14_404 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := by rw [m14]; exact w13_404
    have b14_400 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m14]; exact b13_400
    clear b13_400 w13_404 w13_74 w13_64 g13_25 g13_27 g13_26 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
    exact .inl ⟨(fun ⟨h0', bs7', h1', h2', _⟩ => by rw [hr7] at h1'; cases h1'; exact hl32 h2'), sv_fail_1882 F E14 s14 t14 (fun x hx => (fR14 x hx).trans (fM x hx).symm) V14 hret g14_2 g14_18 hO g14_3 g14_4⟩
  obtain ⟨b0_7, b4_7, bm_7⟩ := Ok7 bs7 hr7 (by omega)
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := keep_kk6.trans K7
  clear keep_kk6
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K7.w32 (by decide) (by decide)).trans w6_64
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K7.w32 (by decide) (by decide)).trans w6_74
  have w7_404 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := b4_7
  have b7_400 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := b0_7
  clear w6_74 w6_64 g6_14 g6_13 g6_12 g6_11 g6_10 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
  have q7_420 : ∀ j, j < 32 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (bs7.getD j 0) :=
    fun j hj => by rw [← add_ofNat_assoc]; exact memBytes_range bm_7 j (by omega)
  -- 0x158E: lbu
  obtain ⟨n8, d8, u8⟩ := s7.lbu E7.self sv_at_158e (off' := 0x1592) (by decide)
  have s8 : St n8.mem SV n8 0x1592 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans (.single d8)
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = c := by rw [u8.regs, upd_ne (by decide) (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = ckl := by rw [u8.regs, upd_ne (by decide) (by decide), g7_9]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, upd_ne (by decide) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = x23 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = p := by rw [u8.regs, upd_ne (by decide) (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = rp := by rw [u8.regs, upd_ne (by decide) (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = rl := by rw [u8.regs, upd_ne (by decide) (by decide), g7_27]
  have g8_10 : reg n8 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g7_2, show B + 0x21A0 + 0x400 = B + 0x21A0 + BitVec.ofNat 32 0x400 by sv_addr, b7_400]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m8]; exact w7_64
  have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m8]; exact w7_74
  have w8_404 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := by rw [m8]; exact w7_404
  have b8_400 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m8]; exact b7_400
  have q8_420 : ∀ j, j < 32 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (bs7.getD j 0) := fun j hj => by rw [m8]; exact q7_420 j hj
  clear b7_400 w7_404 w7_74 w7_64 b4_7 b0_7 g7_2 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 V7 E7 fR7 t7 fr7 Bad7 Ok7 K7 rk7 sp7 s7 c7
  -- 0x1592: branch, not taken
  obtain ⟨n9, d9, u9⟩ := s8.notTaken E8.self 0x1596 sv_at_1592
    (by decide) (by rw [g8_10, s8.zero]; decide)
  have s9 : St n9.mem SV n9 0x1596 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans (.single d9)
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = c := by rw [u9.regs, g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = ckl := by rw [u9.regs, g8_9]
  have g9_10 : reg n9 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u9.regs, g8_10]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [u9.regs, g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [u9.regs, g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [u9.regs, g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = p := by rw [u9.regs, g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = rp := by rw [u9.regs, g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [u9.regs, g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = rl := by rw [u9.regs, g8_27]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m9]; exact w8_64
  have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m9]; exact w8_74
  have w9_404 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := by rw [m9]; exact w8_404
  have b9_400 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m9]; exact b8_400
  have q9_420 : ∀ j, j < 32 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (bs7.getD j 0) := fun j hj => by rw [m9]; exact q8_420 j hj
  clear q8_420 b8_400 w8_404 w8_74 w8_64 g8_10 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8 q7_420
  -- 0x1596: lw
  obtain ⟨n10, d10, u10⟩ := s9.lw E9.self sv_at_1596 (off' := 0x159A) (by decide)
    (by rw [g9_2, show B + 0x21A0 + 0x404 = B + 0x21A0 + BitVec.ofNat 32 0x404 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s10 : St n10.mem SV n10 0x159A (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = c := by rw [u10.regs, upd_ne (by decide) (by decide), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = ckl := by rw [u10.regs, upd_ne (by decide) (by decide), g9_9]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, upd_ne (by decide) (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = x20 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = x23 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = p := by rw [u10.regs, upd_ne (by decide) (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = rp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = rl := by rw [u10.regs, upd_ne (by decide) (by decide), g9_27]
  have g10_10 : reg n10 a0 = BitVec.ofNat 32 bs7.length := by
    rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g9_2, show B + 0x21A0 + 0x404 = B + 0x21A0 + BitVec.ofNat 32 0x404 by sv_addr, w9_404]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m10]; exact w9_64
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m10]; exact w9_74
  have w10_404 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := by rw [m10]; exact w9_404
  have b10_400 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m10]; exact b9_400
  have q10_420 : ∀ j, j < 32 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (bs7.getD j 0) := fun j hj => by rw [m10]; exact q9_420 j hj
  clear q9_420 b9_400 w9_404 w9_74 w9_64 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
  -- 0x159A
  obtain ⟨n11, c11, u11⟩ := s10.block svCke159a E10.self svCke159a_end
    ⟨trivial, trivial⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have s11 : St n11.mem SV n11 0x159C (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have rb11 : ∀ q, reg n11 q = (runBlock svCke159a (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans c11
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by
    rw [rb11, runBlock_reg _ _ _ sp s10.zero (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb11, runBlock_reg _ _ _ (3 : Fin 32) s10.zero (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb11, runBlock_reg _ _ _ (4 : Fin 32) s10.zero (by decide), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = c := by
    rw [rb11, runBlock_reg _ _ _ (8 : Fin 32) s10.zero (by decide), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = ckl := by
    rw [rb11, runBlock_reg _ _ _ (9 : Fin 32) s10.zero (by decide), g10_9]
  have g11_18 : reg n11 (18 : Fin 32) = out := by
    rw [rb11, runBlock_reg _ _ _ (18 : Fin 32) s10.zero (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by
    rw [rb11, runBlock_reg _ _ _ (19 : Fin 32) s10.zero (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by
    rw [rb11, runBlock_reg _ _ _ (20 : Fin 32) s10.zero (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by
    rw [rb11, runBlock_reg _ _ _ (21 : Fin 32) s10.zero (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by
    rw [rb11, runBlock_reg _ _ _ (22 : Fin 32) s10.zero (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by
    rw [rb11, runBlock_reg _ _ _ (23 : Fin 32) s10.zero (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = p := by
    rw [rb11, runBlock_reg _ _ _ (24 : Fin 32) s10.zero (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = rp := by
    rw [rb11, runBlock_reg _ _ _ (25 : Fin 32) s10.zero (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by
    rw [rb11, runBlock_reg _ _ _ (26 : Fin 32) s10.zero (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = rl := by
    rw [rb11, runBlock_reg _ _ _ (27 : Fin 32) s10.zero (by decide), g10_27]
  have g11_10 : reg n11 a0 = (BitVec.ofNat 32 bs7.length) + BitVec.ofNat 32 0xFFFFFFE0 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, svCke159a, upd, ↓reduceIte]; rw [g10_10] <;> rfl
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m11]; exact w10_64
  have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m11]; exact w10_74
  have w11_404 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := by rw [m11]; exact w10_404
  have b11_400 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m11]; exact b10_400
  have q11_420 : ∀ j, j < 32 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (bs7.getD j 0) := fun j hj => by rw [m11]; exact q10_420 j hj
  clear q10_420 b10_400 w10_404 w10_74 w10_64 g10_10 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
  -- 0x159C: branch, not taken
  obtain ⟨n12, d12, u12⟩ := s11.notTaken E11.self 0x15A0 sv_at_159c
    (by decide) (by rw [g11_10, s11.zero, hl32]; decide)
  have s12 : St n12.mem SV n12 0x15A0 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = c := by rw [u12.regs, g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = ckl := by rw [u12.regs, g11_9]
  have g12_10 : reg n12 a0 = (BitVec.ofNat 32 bs7.length) + BitVec.ofNat 32 0xFFFFFFE0 := by rw [u12.regs, g11_10]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [u12.regs, g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [u12.regs, g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [u12.regs, g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = p := by rw [u12.regs, g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = rp := by rw [u12.regs, g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [u12.regs, g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = rl := by rw [u12.regs, g11_27]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m12]; exact w11_64
  have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m12]; exact w11_74
  have w12_404 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := by rw [m12]; exact w11_404
  have b12_400 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m12]; exact b11_400
  have q12_420 : ∀ j, j < 32 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (bs7.getD j 0) := fun j hj => by rw [m12]; exact q11_420 j hj
  clear q11_420 b11_400 w11_404 w11_74 w11_64 g11_10 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 rb11 s11 m11 u11 c11
  -- 0x15A0: lbu
  have b12_420 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = BitVec.ofNat 8 (bs7.getD 0 0) := q12_420 0 (by decide)
  obtain ⟨n13, d13, u13⟩ := s12.lbu E12.self sv_at_15a0 (off' := 0x15A4) (by decide)
  have s13 : St n13.mem SV n13 0x15A4 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans (.single d13)
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = c := by rw [u13.regs, upd_ne (by decide) (by decide), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = ckl := by rw [u13.regs, upd_ne (by decide) (by decide), g12_9]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, upd_ne (by decide) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = x23 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = p := by rw [u13.regs, upd_ne (by decide) (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = rp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = rl := by rw [u13.regs, upd_ne (by decide) (by decide), g12_27]
  have g13_10 : reg n13 a0 = (BitVec.ofNat 8 (bs7.getD 0 0)).zeroExtend 32 := by
    rw [u13.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g12_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, b12_420]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m13]; exact w12_64
  have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m13]; exact w12_74
  have w13_404 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := by rw [m13]; exact w12_404
  have b13_400 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m13]; exact b12_400
  have b13_420 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = BitVec.ofNat 8 (bs7.getD 0 0) := by rw [m13]; exact b12_420
  have q13_420 : ∀ j, j < 32 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (bs7.getD j 0) := fun j hj => by rw [m13]; exact q12_420 j hj
  clear q12_420 b12_400 w12_404 w12_74 w12_64 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_10 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
  -- 0x15A4: sw
  obtain ⟨n14, d14, s14, fr14, K14, W14, rg14⟩ := sv_sw F E13 s13 sv_at_15a4 (off' := 0x15A6) (c := 0x20)
    (by decide) (by rw [g13_2]; sv_addr) (by decide) (by decide)
  have t14 : Steps n0 n14 := t13.trans d14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keep K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [rg14 sp, g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg14 (3 : Fin 32), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg14 (4 : Fin 32), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = c := by rw [rg14 (8 : Fin 32), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = ckl := by rw [rg14 (9 : Fin 32), g13_9]
  have g14_10 : reg n14 a0 = (BitVec.ofNat 8 (bs7.getD 0 0)).zeroExtend 32 := by rw [rg14 a0, g13_10]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [rg14 (18 : Fin 32), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [rg14 (19 : Fin 32), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = x20 := by rw [rg14 (20 : Fin 32), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [rg14 (21 : Fin 32), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = x22 := by rw [rg14 (22 : Fin 32), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = x23 := by rw [rg14 (23 : Fin 32), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = p := by rw [rg14 (24 : Fin 32), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = rp := by rw [rg14 (25 : Fin 32), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [rg14 (26 : Fin 32), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = rl := by rw [rg14 (27 : Fin 32), g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60), (0x20, 0x4)] := keep_kk13.trans K14.toL
  clear keep_kk13
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K14.w32 (by decide) (by decide)).trans w13_64
  have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K14.w32 (by decide) (by decide)).trans w13_74
  have w14_404 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := (K14.w32 (by decide) (by decide)).trans w13_404
  have b14_400 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := (K14.b8 (by decide) (by decide)).trans b13_400
  have b14_420 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = BitVec.ofNat 8 (bs7.getD 0 0) := (K14.b8 (by decide) (by decide)).trans b13_420
  have w14_20 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (bs7.getD 0 0)).zeroExtend 32 := by rw [W14, g13_10]
  have q14_420 : ∀ j, j < 32 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (bs7.getD j 0) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_420 j hj)
  clear q13_420 b13_420 b13_400 w13_404 w13_74 w13_64 g13_10 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13 b12_420
  -- 0x15A6
  obtain ⟨n15, c15, u15⟩ := s14.block svCke15a6 E14.self svCke15a6_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have s15 : St n15.mem SV n15 0x15AE (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have rb15 : ∀ q, reg n15 q = (runBlock svCke15a6 (n14.mem, reg n14)).2 q := fun q => by rw [u15.regs]
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
  have g15_8 : reg n15 (8 : Fin 32) = c := by
    rw [rb15, runBlock_reg _ _ _ (8 : Fin 32) s14.zero (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = ckl := by
    rw [rb15, runBlock_reg _ _ _ (9 : Fin 32) s14.zero (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = out := by
    rw [rb15, runBlock_reg _ _ _ (18 : Fin 32) s14.zero (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by
    rw [rb15, runBlock_reg _ _ _ (19 : Fin 32) s14.zero (by decide), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by
    rw [rb15, runBlock_reg _ _ _ (20 : Fin 32) s14.zero (by decide), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by
    rw [rb15, runBlock_reg _ _ _ (21 : Fin 32) s14.zero (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by
    rw [rb15, runBlock_reg _ _ _ (22 : Fin 32) s14.zero (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by
    rw [rb15, runBlock_reg _ _ _ (23 : Fin 32) s14.zero (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = p := by
    rw [rb15, runBlock_reg _ _ _ (24 : Fin 32) s14.zero (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = rp := by
    rw [rb15, runBlock_reg _ _ _ (25 : Fin 32) s14.zero (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by
    rw [rb15, runBlock_reg _ _ _ (26 : Fin 32) s14.zero (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = rl := by
    rw [rb15, runBlock_reg _ _ _ (27 : Fin 32) s14.zero (by decide), g14_27]
  have g15_10 : reg n15 a0 = B + 0x21A0 + BitVec.ofNat 32 0x3E0 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, svCke15a6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_10, g14_18, g14_19, g14_20, g14_21, g14_22, g14_23, g14_24, g14_25, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g15_11 : reg n15 a1 = B + 0x21A0 + BitVec.ofNat 32 0x421 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, svCke15a6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_10, g14_18, g14_19, g14_20, g14_21, g14_22, g14_23, g14_24, g14_25, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g15_12 : reg n15 a2 = BitVec.ofNat 32 0x1F := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, svCke15a6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_10, g14_18, g14_19, g14_20, g14_21, g14_22, g14_23, g14_24, g14_25, g14_26, g14_27, s14.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60), (0x20, 0x4)] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_20 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (bs7.getD 0 0)).zeroExtend 32 := by rw [m15]; exact w14_20
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m15]; exact w14_64
  have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m15]; exact w14_74
  have w15_404 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := by rw [m15]; exact w14_404
  have b15_400 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m15]; exact b14_400
  have b15_420 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = BitVec.ofNat 8 (bs7.getD 0 0) := by rw [m15]; exact b14_420
  have q15_420 : ∀ j, j < 32 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (bs7.getD j 0) := fun j hj => by rw [m15]; exact q14_420 j hj
  clear q14_420 w14_20 b14_420 b14_400 w14_404 w14_74 w14_64 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_10 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 rg14 W14 K14 fr14 s14 d14
  -- 0x15AE: memcpy
  obtain ⟨n16, P16, K16, X16⟩ := sv_mc (c := 0x3E0) (d := 0x421) (N := 0x1F) F E15 s15 sv_at_15ae sv_at_15b2
    (by decide) (by decide) g15_2 g15_10 g15_11 g15_12
    (by decide) (by decide) (by decide)
  have s16 := P16.st
  have fr16 := P16.fr
  have t16 : Steps n0 n16 := t15.trans P16.steps
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.keep K16 (by decide)
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [P16.regs sp (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P16.regs (3 : Fin 32) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P16.regs (4 : Fin 32) (by decide), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = c := by rw [P16.regs (8 : Fin 32) (by decide), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = ckl := by rw [P16.regs (9 : Fin 32) (by decide), g15_9]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [P16.regs (18 : Fin 32) (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [P16.regs (19 : Fin 32) (by decide), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = x20 := by rw [P16.regs (20 : Fin 32) (by decide), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [P16.regs (21 : Fin 32) (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [P16.regs (22 : Fin 32) (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [P16.regs (23 : Fin 32) (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = p := by rw [P16.regs (24 : Fin 32) (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = rp := by rw [P16.regs (25 : Fin 32) (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [P16.regs (26 : Fin 32) (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = rl := by rw [P16.regs (27 : Fin 32) (by decide), g15_27]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60), (0x20, 0x4), (0x3E0, 0x1F)] := keep_kk15.trans K16.toL
  clear keep_kk15
  have w16_20 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (bs7.getD 0 0)).zeroExtend 32 := (K16.w32 (by decide) (by decide)).trans w15_20
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K16.w32 (by decide) (by decide)).trans w15_64
  have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K16.w32 (by decide) (by decide)).trans w15_74
  have w16_404 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := (K16.w32 (by decide) (by decide)).trans w15_404
  have b16_400 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := (K16.b8 (by decide) (by decide)).trans b15_400
  have b16_420 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = BitVec.ofNat 8 (bs7.getD 0 0) := (K16.b8 (by decide) (by decide)).trans b15_420
  have q16_420 : ∀ j, j < 32 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (bs7.getD j 0) := fun j hj => (K16.range (by decide) (by decide) j hj).trans (q15_420 j hj)
  have q16_3e0 : ∀ j, j < 31 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (bs7.getD (1 + j) 0) := fun j hj => by
    rw [show 0x3E0 + j = 0x3E0 + (0x0 + j) by omega, X16 (0x0 + j) (by omega),
      show 0x421 + (0x0 + j) = 0x420 + (1 + j) by omega]; exact q15_420 (1 + j) (by omega)
  clear q15_420 b15_420 b15_400 w15_404 w15_74 w15_64 w15_20 g15_12 g15_11 g15_10 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 rb15 s15 m15 u15 c15
  -- 0x15B6
  obtain ⟨n17, c17, u17⟩ := s16.block svCke15b6 E16.self svCke15b6_end
    ⟨trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem SV n17 0x15BA (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock svCke15b6 (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
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
  have g17_8 : reg n17 (8 : Fin 32) = c := by
    rw [rb17, runBlock_reg _ _ _ (8 : Fin 32) s16.zero (by decide), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = ckl := by
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
  have g17_24 : reg n17 (24 : Fin 32) = p := by
    rw [rb17, runBlock_reg _ _ _ (24 : Fin 32) s16.zero (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = rp := by
    rw [rb17, runBlock_reg _ _ _ (25 : Fin 32) s16.zero (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by
    rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = rl := by
    rw [rb17, runBlock_reg _ _ _ (27 : Fin 32) s16.zero (by decide), g16_27]
  have g17_10 : reg n17 a0 = (x21) + BitVec.ofNat 32 0x108 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svCke15b6, upd, ↓reduceIte]; rw [g16_21] <;> rfl
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60), (0x20, 0x4), (0x3E0, 0x1F)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_20 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (bs7.getD 0 0)).zeroExtend 32 := by rw [m17]; exact w16_20
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m17]; exact w16_64
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m17]; exact w16_74
  have w17_404 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := by rw [m17]; exact w16_404
  have b17_400 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m17]; exact b16_400
  have b17_420 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = BitVec.ofNat 8 (bs7.getD 0 0) := by rw [m17]; exact b16_420
  have q17_3e0 : ∀ j, j < 31 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (bs7.getD (1 + j) 0) := fun j hj => by rw [m17]; exact q16_3e0 j hj
  have q17_420 : ∀ j, j < 32 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (bs7.getD j 0) := fun j hj => by rw [m17]; exact q16_420 j hj
  clear q16_3e0 q16_420 b16_420 b16_400 w16_404 w16_74 w16_64 w16_20 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 s16 X16 K16 P16
  -- 0x15BA: sw
  obtain ⟨n18, d18, s18, fr18, K18, W18, rg18⟩ := sv_sw F E17 s17 sv_at_15ba (off' := 0x15BC) (c := 0x4C)
    (by decide) (by rw [g17_2]; sv_addr) (by decide) (by decide)
  have t18 : Steps n0 n18 := t17.trans d18
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.keep K18 (by decide)
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [rg18 sp, g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg18 (3 : Fin 32), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg18 (4 : Fin 32), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = c := by rw [rg18 (8 : Fin 32), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = ckl := by rw [rg18 (9 : Fin 32), g17_9]
  have g18_10 : reg n18 a0 = (x21) + BitVec.ofNat 32 0x108 := by rw [rg18 a0, g17_10]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [rg18 (18 : Fin 32), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [rg18 (19 : Fin 32), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [rg18 (20 : Fin 32), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [rg18 (21 : Fin 32), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [rg18 (22 : Fin 32), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [rg18 (23 : Fin 32), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = p := by rw [rg18 (24 : Fin 32), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = rp := by rw [rg18 (25 : Fin 32), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [rg18 (26 : Fin 32), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = rl := by rw [rg18 (27 : Fin 32), g17_27]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60), (0x20, 0x4), (0x3E0, 0x1F), (0x4C, 0x4)] := keep_kk17.trans K18.toL
  clear keep_kk17
  have w18_20 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (bs7.getD 0 0)).zeroExtend 32 := (K18.w32 (by decide) (by decide)).trans w17_20
  have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K18.w32 (by decide) (by decide)).trans w17_64
  have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K18.w32 (by decide) (by decide)).trans w17_74
  have w18_404 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := (K18.w32 (by decide) (by decide)).trans w17_404
  have b18_400 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := (K18.b8 (by decide) (by decide)).trans b17_400
  have b18_420 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = BitVec.ofNat 8 (bs7.getD 0 0) := (K18.b8 (by decide) (by decide)).trans b17_420
  have w18_4c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (x21) + BitVec.ofNat 32 0x108 := by rw [W18, g17_10]
  have q18_3e0 : ∀ j, j < 31 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (bs7.getD (1 + j) 0) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_3e0 j hj)
  have q18_420 : ∀ j, j < 32 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (bs7.getD j 0) := fun j hj => (K18.range (by decide) (by decide) j hj).trans (q17_420 j hj)
  clear q17_420 q17_3e0 b17_420 b17_400 w17_404 w17_74 w17_64 w17_20 g17_10 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
  -- 0x15BC
  obtain ⟨n19, c19, u19⟩ := s18.block svCke15bc E18.self svCke15bc_end
    ⟨trivial, trivial⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have s19 : St n19.mem SV n19 0x15C0 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have rb19 : ∀ q, reg n19 q = (runBlock svCke15bc (n18.mem, reg n18)).2 q := fun q => by rw [u19.regs]
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
  have g19_9 : reg n19 (9 : Fin 32) = ckl := by
    rw [rb19, runBlock_reg _ _ _ (9 : Fin 32) s18.zero (by decide), g18_9]
  have g19_10 : reg n19 a0 = (x21) + BitVec.ofNat 32 0x108 := by
    rw [rb19, runBlock_reg _ _ _ a0 s18.zero (by decide), g18_10]
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
  have g19_24 : reg n19 (24 : Fin 32) = p := by
    rw [rb19, runBlock_reg _ _ _ (24 : Fin 32) s18.zero (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = rp := by
    rw [rb19, runBlock_reg _ _ _ (25 : Fin 32) s18.zero (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by
    rw [rb19, runBlock_reg _ _ _ (26 : Fin 32) s18.zero (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = rl := by
    rw [rb19, runBlock_reg _ _ _ (27 : Fin 32) s18.zero (by decide), g18_27]
  have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 0x200 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svCke15bc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_10, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_25, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x420, 0x60), (0x400, 0x8), (0x420, 0x60), (0x20, 0x4), (0x3E0, 0x1F), (0x4C, 0x4)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_20 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (bs7.getD 0 0)).zeroExtend 32 := by rw [m19]; exact w18_20
  have w19_4c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (x21) + BitVec.ofNat 32 0x108 := by rw [m19]; exact w18_4c
  have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m19]; exact w18_64
  have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m19]; exact w18_74
  have w19_404 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length := by rw [m19]; exact w18_404
  have b19_400 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) := by rw [m19]; exact b18_400
  have b19_420 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = BitVec.ofNat 8 (bs7.getD 0 0) := by rw [m19]; exact b18_420
  have q19_3e0 : ∀ j, j < 31 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (bs7.getD (1 + j) 0) := fun j hj => by rw [m19]; exact q18_3e0 j hj
  have q19_420 : ∀ j, j < 32 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (bs7.getD j 0) := fun j hj => by rw [m19]; exact q18_420 j hj
  clear q18_420 q18_3e0 w18_4c b18_420 b18_400 w18_404 w18_74 w18_64 w18_20 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_10 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 rg18 W18 K18 fr18 s18 d18
  exact .inr ⟨hsz, bs7, hr7, hl32, n19, t19, s19, E19, V19, fR19, g19_2, g19_3, g19_4, g19_8, g19_18, g19_19, g19_20, g19_21, g19_22, g19_23, g19_24, g19_25, g19_26, g19_27, w19_20, w19_4c, w19_64, w19_74, w19_404, b19_400, b19_420, q19_3e0, q19_420, keep_kk19.mono (by decide)⟩

end C3.RV32.Sv
