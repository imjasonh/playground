import C3BootProofs.Proofs.SvCkpt

/-!
# `sigstore::verify`: the log key's hash

From the log's entry at 0x15F0 to the signature loop at 0x1642: the word at offset 0x18 is the first word of SHA-256 of the origin line, a newline, the Ed25519 key tag, and the log's key.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svCs115f8 : List BInstr :=
  [.lui a0 0x3FCC4000, .aluImm .add a0 a0 0x784, .aluImm .add a1 x0 0x1]
theorem svCs115f8_end : blockEnd sigstoreVerifyCode 0x15F8 svCs115f8 = some 0x1602 := by
  simp only [svCs115f8]
  rw [blockEnd, sv_at_15f8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_15fc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1600]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCs11604 : List BInstr :=
  [.aluImm .add a4 sp 0x400]
theorem svCs11604_end : blockEnd sigstoreVerifyCode 0x1604 svCs11604 = some 0x1608 := by
  simp only [svCs11604]
  rw [blockEnd, sv_at_1604]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCs11612 : List BInstr :=
  [.lui a0 0x3FCC4000, .aluImm .add a0 a0 0x647, .aluImm .add a2 x0 0x20]
theorem svCs11612_end : blockEnd sigstoreVerifyCode 0x1612 svCs11612 = some 0x161E := by
  simp only [svCs11612]
  rw [blockEnd, sv_at_1612]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1616]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_161a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCs11628 : List BInstr :=
  [.aluImm .add a0 sp 0x400, .aluImm .add a1 sp 0x420, .aluImm .add a2 x0 0x4]
theorem svCs11628_end : blockEnd sigstoreVerifyCode 0x1628 svCs11628 = some 0x1632 := by
  simp only [svCs11628]
  rw [blockEnd, sv_at_1628]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_162c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1630]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_cs1 {B out bp x20 x21 x22 x23 x24 x25 x26 x27 c q kp kw w48 w44 : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x15F0 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = c)
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
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q)
    (S2 : SvSha2Code M0)
    (RS : SvRoSep B)
    (hkp : memLoad32 M0 (q + 0x18) = kp)
    (hkw : memLoad32 M0 (q + 0x1C) = kw)
    (kp_in4 : SvIn B (q + 0x18) 4)
    (kw_in4 : SvIn B (q + 0x1C) 4)
    (a_kp : (q + 0x18).toNat % 4 = 0)
    (a_kw : (q + 0x1C).toNat % 4 = 0)
    (kp_in : SvIn B kp 32)
    (l_in : SvIn B w48 w44.toNat) :
    (¬ (True) ∧ SvErrRet B out v n0) ∨
    (∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x1642 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = c ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = le4 (sha256 (memBytes M0 (w48) ((w44).toNat) ++ memBytes M0 (BitVec.ofNat 32 (img% svNewlineAddress)) (1) ++ memBytes M0 (BitVec.ofNat 32 (img% merklePrefixAddress)) (1) ++ memBytes M0 (kp) (32))) 0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = le4 (sha256 (memBytes M0 (w48) ((w44).toNat) ++ memBytes M0 (BitVec.ofNat 32 (img% svNewlineAddress)) (1) ++ memBytes M0 (BitVec.ofNat 32 (img% merklePrefixAddress)) (1) ++ memBytes M0 (kp) (32))) 0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 (img% svNewlineAddress) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (img% merklePrefixAddress) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x438) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x43C) = BitVec.ofNat 32 0x20 ∧
        SvKeepL B n0.mem n'.mem [(0x1C, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4), (0x438, 0x4), (0x43C, 0x4), (0x400, 0x20), (0x30, 0x4), (0x18, 0x4)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x15F0: lw
  obtain ⟨n1, d1, u1⟩ := s0.lw E0.self sv_at_15f0 (off' := 0x15F2) (by decide)
    (by rw [g0_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s1 : St n1.mem SV n1 0x15F2 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_4]
  have g1_8 : reg n1 (8 : Fin 32) = c := by rw [u1.regs, upd_ne (by decide) (by decide), g0_8]
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
  have g1_10 : reg n1 a0 = q := by
    rw [u1.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g0_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr, w0_4c]
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_44 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m1]; exact w0_44
  have w1_48 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m1]; exact w0_48
  have w1_4c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m1]; exact w0_4c
  -- 0x15F2: lw outside the stack
  obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_15f2 (off' := 0x15F4) (by decide)
    (by rw [g1_10]; exact a_kp)
  have s2 : St n2.mem SV n2 0x15F4 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
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
  have g2_10 : reg n2 a0 = q := by rw [u2.regs, upd_ne (by decide) (by decide), g1_10]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = x20 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = x22 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = x23 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = x24 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = x25 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = x27 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_27]
  have g2_13 : reg n2 a3 = kp := by
    rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g1_10, sv_ld fR1 kp_in4, hkp]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_44 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m2]; exact w1_44
  have w2_48 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m2]; exact w1_48
  have w2_4c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m2]; exact w1_4c
  clear w1_4c w1_48 w1_44 g1_10 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x15F4: lw outside the stack
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_15f4 (off' := 0x15F6) (by decide)
    (by rw [g2_10]; exact a_kw)
  have s3 : St n3.mem SV n3 0x15F6 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = c := by rw [u3.regs, upd_ne (by decide) (by decide), g2_8]
  have g3_13 : reg n3 a3 = kp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_13]
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
  have g3_10 : reg n3 a0 = kw := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_10, sv_ld fR2 kw_in4, hkw]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_44 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m3]; exact w2_44
  have w3_48 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m3]; exact w2_48
  have w3_4c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m3]; exact w2_4c
  clear w2_4c w2_48 w2_44 g2_13 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_10 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x15F6: sw
  obtain ⟨n4, d4, s4, fr4, K4, W4, rg4⟩ := sv_sw F E3 s3 sv_at_15f6 (off' := 0x15F8) (c := 0x1C)
    (by decide) (by rw [g3_2]; sv_addr) (by decide) (by decide)
  have t4 : Steps n0 n4 := t3.trans d4
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.keep K4 (by decide)
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [rg4 sp, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg4 (3 : Fin 32), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg4 (4 : Fin 32), g3_4]
  have g4_8 : reg n4 (8 : Fin 32) = c := by rw [rg4 (8 : Fin 32), g3_8]
  have g4_10 : reg n4 a0 = kw := by rw [rg4 a0, g3_10]
  have g4_13 : reg n4 a3 = kp := by rw [rg4 a3, g3_13]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [rg4 (18 : Fin 32), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [rg4 (19 : Fin 32), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = x20 := by rw [rg4 (20 : Fin 32), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [rg4 (21 : Fin 32), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = x22 := by rw [rg4 (22 : Fin 32), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = x23 := by rw [rg4 (23 : Fin 32), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = x24 := by rw [rg4 (24 : Fin 32), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = x25 := by rw [rg4 (25 : Fin 32), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [rg4 (26 : Fin 32), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = x27 := by rw [rg4 (27 : Fin 32), g3_27]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [(0x1C, 0x4)] := keep_kk3.trans K4.toL
  clear keep_kk3
  have w4_44 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K4.w32 (by decide) (by decide)).trans w3_44
  have w4_48 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K4.w32 (by decide) (by decide)).trans w3_48
  have w4_4c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K4.w32 (by decide) (by decide)).trans w3_4c
  have w4_1c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := by rw [W4, g3_10]
  clear w3_4c w3_48 w3_44 g3_10 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_13 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x15F8
  obtain ⟨n5, c5, u5⟩ := s4.block svCs115f8 E4.self svCs115f8_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0x1602 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock svCs115f8 (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
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
  have g5_8 : reg n5 (8 : Fin 32) = c := by
    rw [rb5, runBlock_reg _ _ _ (8 : Fin 32) s4.zero (by decide), g4_8]
  have g5_13 : reg n5 a3 = kp := by
    rw [rb5, runBlock_reg _ _ _ a3 s4.zero (by decide), g4_13]
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
  have g5_24 : reg n5 (24 : Fin 32) = x24 := by
    rw [rb5, runBlock_reg _ _ _ (24 : Fin 32) s4.zero (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by
    rw [rb5, runBlock_reg _ _ _ (25 : Fin 32) s4.zero (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = x27 := by
    rw [rb5, runBlock_reg _ _ _ (27 : Fin 32) s4.zero (by decide), g4_27]
  have g5_10 : reg n5 a0 = BitVec.ofNat 32 (img% svNewlineAddress) := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svCs115f8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_10, g4_13, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g5_11 : reg n5 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svCs115f8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_10, g4_13, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk5 : SvKeepL B n0.mem n5.mem [(0x1C, 0x4)] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_1c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := by rw [m5]; exact w4_1c
  have w5_44 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m5]; exact w4_44
  have w5_48 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m5]; exact w4_48
  have w5_4c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m5]; exact w4_4c
  clear w4_1c w4_4c w4_48 w4_44 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_13 g4_10 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 rg4 W4 K4 fr4 s4 d4
  -- 0x1602: lw
  obtain ⟨n6, d6, u6⟩ := s5.lw E5.self sv_at_1602 (off' := 0x1604) (by decide)
    (by rw [g5_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s6 : St n6.mem SV n6 0x1604 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = c := by rw [u6.regs, upd_ne (by decide) (by decide), g5_8]
  have g6_10 : reg n6 a0 = BitVec.ofNat 32 (img% svNewlineAddress) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_10]
  have g6_11 : reg n6 a1 = BitVec.ofNat 32 0x1 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_11]
  have g6_13 : reg n6 a3 = kp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_13]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, upd_ne (by decide) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = x20 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = x24 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = x27 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_27]
  have g6_12 : reg n6 a2 = w48 := by
    rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g5_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w5_48]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [(0x1C, 0x4)] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_1c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := by rw [m6]; exact w5_1c
  have w6_44 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m6]; exact w5_44
  have w6_48 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m6]; exact w5_48
  have w6_4c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m6]; exact w5_4c
  clear w5_4c w5_48 w5_44 w5_1c g5_11 g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_13 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0x1604
  obtain ⟨n7, c7, u7⟩ := s6.block svCs11604 E6.self svCs11604_end
    ⟨trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem SV n7 0x1608 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have rb7 : ∀ q, reg n7 q = (runBlock svCs11604 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
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
  have g7_8 : reg n7 (8 : Fin 32) = c := by
    rw [rb7, runBlock_reg _ _ _ (8 : Fin 32) s6.zero (by decide), g6_8]
  have g7_10 : reg n7 a0 = BitVec.ofNat 32 (img% svNewlineAddress) := by
    rw [rb7, runBlock_reg _ _ _ a0 s6.zero (by decide), g6_10]
  have g7_11 : reg n7 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb7, runBlock_reg _ _ _ a1 s6.zero (by decide), g6_11]
  have g7_12 : reg n7 a2 = w48 := by
    rw [rb7, runBlock_reg _ _ _ a2 s6.zero (by decide), g6_12]
  have g7_13 : reg n7 a3 = kp := by
    rw [rb7, runBlock_reg _ _ _ a3 s6.zero (by decide), g6_13]
  have g7_18 : reg n7 (18 : Fin 32) = out := by
    rw [rb7, runBlock_reg _ _ _ (18 : Fin 32) s6.zero (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by
    rw [rb7, runBlock_reg _ _ _ (19 : Fin 32) s6.zero (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = x20 := by
    rw [rb7, runBlock_reg _ _ _ (20 : Fin 32) s6.zero (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by
    rw [rb7, runBlock_reg _ _ _ (21 : Fin 32) s6.zero (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = x22 := by
    rw [rb7, runBlock_reg _ _ _ (22 : Fin 32) s6.zero (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = x23 := by
    rw [rb7, runBlock_reg _ _ _ (23 : Fin 32) s6.zero (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = x24 := by
    rw [rb7, runBlock_reg _ _ _ (24 : Fin 32) s6.zero (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by
    rw [rb7, runBlock_reg _ _ _ (25 : Fin 32) s6.zero (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by
    rw [rb7, runBlock_reg _ _ _ (26 : Fin 32) s6.zero (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = x27 := by
    rw [rb7, runBlock_reg _ _ _ (27 : Fin 32) s6.zero (by decide), g6_27]
  have g7_14 : reg n7 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svCs11604, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_10, g6_11, g6_12, g6_13, g6_18, g6_19, g6_20, g6_21, g6_22, g6_23, g6_24, g6_25, g6_26, g6_27, s6.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk7 : SvKeepL B n0.mem n7.mem [(0x1C, 0x4)] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_1c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := by rw [m7]; exact w6_1c
  have w7_44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m7]; exact w6_44
  have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m7]; exact w6_48
  have w7_4c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m7]; exact w6_4c
  clear w6_4c w6_48 w6_44 w6_1c g6_12 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_13 g6_11 g6_10 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  -- 0x1608: sw
  obtain ⟨n8, d8, s8, fr8, K8, W8, rg8⟩ := sv_sw F E7 s7 sv_at_1608 (off' := 0x160A) (c := 0x420)
    (by decide) (by rw [g7_14]; sv_addr) (by decide) (by decide)
  have t8 : Steps n0 n8 := t7.trans d8
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keep K8 (by decide)
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rg8 sp, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg8 (3 : Fin 32), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg8 (4 : Fin 32), g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = c := by rw [rg8 (8 : Fin 32), g7_8]
  have g8_10 : reg n8 a0 = BitVec.ofNat 32 (img% svNewlineAddress) := by rw [rg8 a0, g7_10]
  have g8_11 : reg n8 a1 = BitVec.ofNat 32 0x1 := by rw [rg8 a1, g7_11]
  have g8_12 : reg n8 a2 = w48 := by rw [rg8 a2, g7_12]
  have g8_13 : reg n8 a3 = kp := by rw [rg8 a3, g7_13]
  have g8_14 : reg n8 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg8 a4, g7_14]
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
  have keep_kk8 : SvKeepL B n0.mem n8.mem [(0x1C, 0x4), (0x420, 0x4)] := keep_kk7.trans K8.toL
  clear keep_kk7
  have w8_1c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := (K8.w32 (by decide) (by decide)).trans w7_1c
  have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K8.w32 (by decide) (by decide)).trans w7_44
  have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K8.w32 (by decide) (by decide)).trans w7_48
  have w8_4c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K8.w32 (by decide) (by decide)).trans w7_4c
  have w8_420 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := by rw [W8, g7_12]
  clear w7_4c w7_48 w7_44 w7_1c g7_14 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_13 g7_12 g7_11 g7_10 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
  -- 0x160A: lw
  obtain ⟨n9, d9, u9⟩ := s8.lw E8.self sv_at_160a (off' := 0x160C) (by decide)
    (by rw [g8_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s9 : St n9.mem SV n9 0x160C (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans (.single d9)
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = c := by rw [u9.regs, upd_ne (by decide) (by decide), g8_8]
  have g9_10 : reg n9 a0 = BitVec.ofNat 32 (img% svNewlineAddress) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_10]
  have g9_11 : reg n9 a1 = BitVec.ofNat 32 0x1 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_11]
  have g9_13 : reg n9 a3 = kp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_13]
  have g9_14 : reg n9 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_14]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, upd_ne (by decide) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = x20 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = x22 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = x23 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = x24 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = x27 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_27]
  have g9_12 : reg n9 a2 = w44 := by
    rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g8_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w8_44]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [(0x1C, 0x4), (0x420, 0x4)] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_1c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := by rw [m9]; exact w8_1c
  have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m9]; exact w8_44
  have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m9]; exact w8_48
  have w9_4c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m9]; exact w8_4c
  have w9_420 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := by rw [m9]; exact w8_420
  clear w8_420 w8_4c w8_48 w8_44 w8_1c g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_14 g8_13 g8_12 g8_11 g8_10 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 rg8 W8 K8 fr8 s8 d8
  -- 0x160C: sw
  obtain ⟨n10, d10, s10, fr10, K10, W10, rg10⟩ := sv_sw F E9 s9 sv_at_160c (off' := 0x160E) (c := 0x424)
    (by decide) (by rw [g9_14]; sv_addr) (by decide) (by decide)
  have t10 : Steps n0 n10 := t9.trans d10
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.keep K10 (by decide)
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [rg10 sp, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg10 (3 : Fin 32), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg10 (4 : Fin 32), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = c := by rw [rg10 (8 : Fin 32), g9_8]
  have g10_10 : reg n10 a0 = BitVec.ofNat 32 (img% svNewlineAddress) := by rw [rg10 a0, g9_10]
  have g10_11 : reg n10 a1 = BitVec.ofNat 32 0x1 := by rw [rg10 a1, g9_11]
  have g10_12 : reg n10 a2 = w44 := by rw [rg10 a2, g9_12]
  have g10_13 : reg n10 a3 = kp := by rw [rg10 a3, g9_13]
  have g10_14 : reg n10 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg10 a4, g9_14]
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
  have keep_kk10 : SvKeepL B n0.mem n10.mem [(0x1C, 0x4), (0x420, 0x4), (0x424, 0x4)] := keep_kk9.trans K10.toL
  clear keep_kk9
  have w10_1c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := (K10.w32 (by decide) (by decide)).trans w9_1c
  have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K10.w32 (by decide) (by decide)).trans w9_44
  have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K10.w32 (by decide) (by decide)).trans w9_48
  have w10_4c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K10.w32 (by decide) (by decide)).trans w9_4c
  have w10_420 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K10.w32 (by decide) (by decide)).trans w9_420
  have w10_424 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := by rw [W10, g9_12]
  clear w9_420 w9_4c w9_48 w9_44 w9_1c g9_12 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_14 g9_13 g9_11 g9_10 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
  -- 0x160E: sw
  obtain ⟨n11, d11, s11, fr11, K11, W11, rg11⟩ := sv_sw F E10 s10 sv_at_160e (off' := 0x1610) (c := 0x428)
    (by decide) (by rw [g10_14]; sv_addr) (by decide) (by decide)
  have t11 : Steps n0 n11 := t10.trans d11
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.keep K11 (by decide)
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [rg11 sp, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg11 (3 : Fin 32), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg11 (4 : Fin 32), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = c := by rw [rg11 (8 : Fin 32), g10_8]
  have g11_10 : reg n11 a0 = BitVec.ofNat 32 (img% svNewlineAddress) := by rw [rg11 a0, g10_10]
  have g11_11 : reg n11 a1 = BitVec.ofNat 32 0x1 := by rw [rg11 a1, g10_11]
  have g11_12 : reg n11 a2 = w44 := by rw [rg11 a2, g10_12]
  have g11_13 : reg n11 a3 = kp := by rw [rg11 a3, g10_13]
  have g11_14 : reg n11 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg11 a4, g10_14]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [rg11 (18 : Fin 32), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [rg11 (19 : Fin 32), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [rg11 (20 : Fin 32), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [rg11 (21 : Fin 32), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [rg11 (22 : Fin 32), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by rw [rg11 (23 : Fin 32), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [rg11 (24 : Fin 32), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by rw [rg11 (25 : Fin 32), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [rg11 (26 : Fin 32), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = x27 := by rw [rg11 (27 : Fin 32), g10_27]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [(0x1C, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4)] := keep_kk10.trans K11.toL
  clear keep_kk10
  have w11_1c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := (K11.w32 (by decide) (by decide)).trans w10_1c
  have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K11.w32 (by decide) (by decide)).trans w10_44
  have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K11.w32 (by decide) (by decide)).trans w10_48
  have w11_4c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K11.w32 (by decide) (by decide)).trans w10_4c
  have w11_420 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K11.w32 (by decide) (by decide)).trans w10_420
  have w11_424 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K11.w32 (by decide) (by decide)).trans w10_424
  have w11_428 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 (img% svNewlineAddress) := by rw [W11, g10_10]
  clear w10_424 w10_420 w10_4c w10_48 w10_44 w10_1c g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_14 g10_13 g10_12 g10_11 g10_10 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 rg10 W10 K10 fr10 s10 d10
  -- 0x1610: sw
  obtain ⟨n12, d12, s12, fr12, K12, W12, rg12⟩ := sv_sw F E11 s11 sv_at_1610 (off' := 0x1612) (c := 0x42C)
    (by decide) (by rw [g11_14]; sv_addr) (by decide) (by decide)
  have t12 : Steps n0 n12 := t11.trans d12
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.keep K12 (by decide)
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [rg12 sp, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg12 (3 : Fin 32), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg12 (4 : Fin 32), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = c := by rw [rg12 (8 : Fin 32), g11_8]
  have g12_10 : reg n12 a0 = BitVec.ofNat 32 (img% svNewlineAddress) := by rw [rg12 a0, g11_10]
  have g12_11 : reg n12 a1 = BitVec.ofNat 32 0x1 := by rw [rg12 a1, g11_11]
  have g12_12 : reg n12 a2 = w44 := by rw [rg12 a2, g11_12]
  have g12_13 : reg n12 a3 = kp := by rw [rg12 a3, g11_13]
  have g12_14 : reg n12 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg12 a4, g11_14]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [rg12 (18 : Fin 32), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [rg12 (19 : Fin 32), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [rg12 (20 : Fin 32), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [rg12 (21 : Fin 32), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [rg12 (22 : Fin 32), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = x23 := by rw [rg12 (23 : Fin 32), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = x24 := by rw [rg12 (24 : Fin 32), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [rg12 (25 : Fin 32), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [rg12 (26 : Fin 32), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = x27 := by rw [rg12 (27 : Fin 32), g11_27]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [(0x1C, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4)] := keep_kk11.trans K12.toL
  clear keep_kk11
  have w12_1c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := (K12.w32 (by decide) (by decide)).trans w11_1c
  have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K12.w32 (by decide) (by decide)).trans w11_44
  have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K12.w32 (by decide) (by decide)).trans w11_48
  have w12_4c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K12.w32 (by decide) (by decide)).trans w11_4c
  have w12_420 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K12.w32 (by decide) (by decide)).trans w11_420
  have w12_424 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K12.w32 (by decide) (by decide)).trans w11_424
  have w12_428 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 (img% svNewlineAddress) := (K12.w32 (by decide) (by decide)).trans w11_428
  have w12_42c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := by rw [W12, g11_11]
  clear w11_428 w11_424 w11_420 w11_4c w11_48 w11_44 w11_1c g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_14 g11_13 g11_12 g11_11 g11_10 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 rg11 W11 K11 fr11 s11 d11
  -- 0x1612
  obtain ⟨n13, c13, u13⟩ := s12.block svCs11612 E12.self svCs11612_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem SV n13 0x161E (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock svCs11612 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
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
  have g13_11 : reg n13 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb13, runBlock_reg _ _ _ a1 s12.zero (by decide), g12_11]
  have g13_13 : reg n13 a3 = kp := by
    rw [rb13, runBlock_reg _ _ _ a3 s12.zero (by decide), g12_13]
  have g13_14 : reg n13 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb13, runBlock_reg _ _ _ a4 s12.zero (by decide), g12_14]
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
  have g13_10 : reg n13 a0 = BitVec.ofNat 32 (img% merklePrefixAddress) := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svCs11612, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_10, g12_11, g12_12, g12_13, g12_14, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g13_12 : reg n13 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svCs11612, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_10, g12_11, g12_12, g12_13, g12_14, g12_18, g12_19, g12_20, g12_21, g12_22, g12_23, g12_24, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk13 : SvKeepL B n0.mem n13.mem [(0x1C, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4)] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_1c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := by rw [m13]; exact w12_1c
  have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m13]; exact w12_44
  have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m13]; exact w12_48
  have w13_4c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m13]; exact w12_4c
  have w13_420 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := by rw [m13]; exact w12_420
  have w13_424 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := by rw [m13]; exact w12_424
  have w13_428 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 (img% svNewlineAddress) := by rw [m13]; exact w12_428
  have w13_42c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := by rw [m13]; exact w12_42c
  clear w12_42c w12_428 w12_424 w12_420 w12_4c w12_48 w12_44 w12_1c g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_14 g12_13 g12_12 g12_11 g12_10 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 rg12 W12 K12 fr12 s12 d12
  -- 0x161E: sw
  obtain ⟨n14, d14, s14, fr14, K14, W14, rg14⟩ := sv_sw F E13 s13 sv_at_161e (off' := 0x1620) (c := 0x430)
    (by decide) (by rw [g13_14]; sv_addr) (by decide) (by decide)
  have t14 : Steps n0 n14 := t13.trans d14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keep K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [rg14 sp, g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg14 (3 : Fin 32), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg14 (4 : Fin 32), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = c := by rw [rg14 (8 : Fin 32), g13_8]
  have g14_10 : reg n14 a0 = BitVec.ofNat 32 (img% merklePrefixAddress) := by rw [rg14 a0, g13_10]
  have g14_11 : reg n14 a1 = BitVec.ofNat 32 0x1 := by rw [rg14 a1, g13_11]
  have g14_12 : reg n14 a2 = BitVec.ofNat 32 0x20 := by rw [rg14 a2, g13_12]
  have g14_13 : reg n14 a3 = kp := by rw [rg14 a3, g13_13]
  have g14_14 : reg n14 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg14 a4, g13_14]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [rg14 (18 : Fin 32), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [rg14 (19 : Fin 32), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = x20 := by rw [rg14 (20 : Fin 32), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [rg14 (21 : Fin 32), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = x22 := by rw [rg14 (22 : Fin 32), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = x23 := by rw [rg14 (23 : Fin 32), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = x24 := by rw [rg14 (24 : Fin 32), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [rg14 (25 : Fin 32), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [rg14 (26 : Fin 32), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = x27 := by rw [rg14 (27 : Fin 32), g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x1C, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4)] := keep_kk13.trans K14.toL
  clear keep_kk13
  have w14_1c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := (K14.w32 (by decide) (by decide)).trans w13_1c
  have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K14.w32 (by decide) (by decide)).trans w13_44
  have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K14.w32 (by decide) (by decide)).trans w13_48
  have w14_4c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K14.w32 (by decide) (by decide)).trans w13_4c
  have w14_420 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K14.w32 (by decide) (by decide)).trans w13_420
  have w14_424 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K14.w32 (by decide) (by decide)).trans w13_424
  have w14_428 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 (img% svNewlineAddress) := (K14.w32 (by decide) (by decide)).trans w13_428
  have w14_42c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := (K14.w32 (by decide) (by decide)).trans w13_42c
  have w14_430 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (img% merklePrefixAddress) := by rw [W14, g13_10]
  clear w13_42c w13_428 w13_424 w13_420 w13_4c w13_48 w13_44 w13_1c g13_12 g13_10 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_14 g13_13 g13_11 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
  -- 0x1620: sw
  obtain ⟨n15, d15, s15, fr15, K15, W15, rg15⟩ := sv_sw F E14 s14 sv_at_1620 (off' := 0x1622) (c := 0x434)
    (by decide) (by rw [g14_14]; sv_addr) (by decide) (by decide)
  have t15 : Steps n0 n15 := t14.trans d15
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.keep K15 (by decide)
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [rg15 sp, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg15 (3 : Fin 32), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg15 (4 : Fin 32), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = c := by rw [rg15 (8 : Fin 32), g14_8]
  have g15_10 : reg n15 a0 = BitVec.ofNat 32 (img% merklePrefixAddress) := by rw [rg15 a0, g14_10]
  have g15_11 : reg n15 a1 = BitVec.ofNat 32 0x1 := by rw [rg15 a1, g14_11]
  have g15_12 : reg n15 a2 = BitVec.ofNat 32 0x20 := by rw [rg15 a2, g14_12]
  have g15_13 : reg n15 a3 = kp := by rw [rg15 a3, g14_13]
  have g15_14 : reg n15 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg15 a4, g14_14]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [rg15 (18 : Fin 32), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [rg15 (19 : Fin 32), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [rg15 (20 : Fin 32), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [rg15 (21 : Fin 32), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [rg15 (22 : Fin 32), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [rg15 (23 : Fin 32), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = x24 := by rw [rg15 (24 : Fin 32), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [rg15 (25 : Fin 32), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [rg15 (26 : Fin 32), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = x27 := by rw [rg15 (27 : Fin 32), g14_27]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x1C, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4)] := keep_kk14.trans K15.toL
  clear keep_kk14
  have w15_1c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := (K15.w32 (by decide) (by decide)).trans w14_1c
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K15.w32 (by decide) (by decide)).trans w14_44
  have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K15.w32 (by decide) (by decide)).trans w14_48
  have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K15.w32 (by decide) (by decide)).trans w14_4c
  have w15_420 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K15.w32 (by decide) (by decide)).trans w14_420
  have w15_424 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K15.w32 (by decide) (by decide)).trans w14_424
  have w15_428 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 (img% svNewlineAddress) := (K15.w32 (by decide) (by decide)).trans w14_428
  have w15_42c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := (K15.w32 (by decide) (by decide)).trans w14_42c
  have w15_430 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (img% merklePrefixAddress) := (K15.w32 (by decide) (by decide)).trans w14_430
  have w15_434 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 := by rw [W15, g14_11]
  clear w14_430 w14_42c w14_428 w14_424 w14_420 w14_4c w14_48 w14_44 w14_1c g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_14 g14_13 g14_12 g14_11 g14_10 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 rg14 W14 K14 fr14 s14 d14
  -- 0x1622: sw
  obtain ⟨n16, d16, s16, fr16, K16, W16, rg16⟩ := sv_sw F E15 s15 sv_at_1622 (off' := 0x1624) (c := 0x34)
    (by decide) (by rw [g15_2]; sv_addr) (by decide) (by decide)
  have t16 : Steps n0 n16 := t15.trans d16
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.keep K16 (by decide)
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [rg16 sp, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg16 (3 : Fin 32), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg16 (4 : Fin 32), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = c := by rw [rg16 (8 : Fin 32), g15_8]
  have g16_10 : reg n16 a0 = BitVec.ofNat 32 (img% merklePrefixAddress) := by rw [rg16 a0, g15_10]
  have g16_11 : reg n16 a1 = BitVec.ofNat 32 0x1 := by rw [rg16 a1, g15_11]
  have g16_12 : reg n16 a2 = BitVec.ofNat 32 0x20 := by rw [rg16 a2, g15_12]
  have g16_13 : reg n16 a3 = kp := by rw [rg16 a3, g15_13]
  have g16_14 : reg n16 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg16 a4, g15_14]
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
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x1C, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4)] := keep_kk15.trans K16.toL
  clear keep_kk15
  have w16_1c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := (K16.w32 (by decide) (by decide)).trans w15_1c
  have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K16.w32 (by decide) (by decide)).trans w15_44
  have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K16.w32 (by decide) (by decide)).trans w15_48
  have w16_4c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K16.w32 (by decide) (by decide)).trans w15_4c
  have w16_420 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K16.w32 (by decide) (by decide)).trans w15_420
  have w16_424 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K16.w32 (by decide) (by decide)).trans w15_424
  have w16_428 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 (img% svNewlineAddress) := (K16.w32 (by decide) (by decide)).trans w15_428
  have w16_42c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := (K16.w32 (by decide) (by decide)).trans w15_42c
  have w16_430 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (img% merklePrefixAddress) := (K16.w32 (by decide) (by decide)).trans w15_430
  have w16_434 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 := (K16.w32 (by decide) (by decide)).trans w15_434
  have w16_34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [W16, g15_13]
  clear w15_434 w15_430 w15_42c w15_428 w15_424 w15_420 w15_4c w15_48 w15_44 w15_1c g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_14 g15_13 g15_12 g15_11 g15_10 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 rg15 W15 K15 fr15 s15 d15
  -- 0x1624: sw
  obtain ⟨n17, d17, s17, fr17, K17, W17, rg17⟩ := sv_sw F E16 s16 sv_at_1624 (off' := 0x1626) (c := 0x438)
    (by decide) (by rw [g16_14]; sv_addr) (by decide) (by decide)
  have t17 : Steps n0 n17 := t16.trans d17
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.keep K17 (by decide)
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [rg17 sp, g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg17 (3 : Fin 32), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg17 (4 : Fin 32), g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = c := by rw [rg17 (8 : Fin 32), g16_8]
  have g17_10 : reg n17 a0 = BitVec.ofNat 32 (img% merklePrefixAddress) := by rw [rg17 a0, g16_10]
  have g17_11 : reg n17 a1 = BitVec.ofNat 32 0x1 := by rw [rg17 a1, g16_11]
  have g17_12 : reg n17 a2 = BitVec.ofNat 32 0x20 := by rw [rg17 a2, g16_12]
  have g17_13 : reg n17 a3 = kp := by rw [rg17 a3, g16_13]
  have g17_14 : reg n17 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg17 a4, g16_14]
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
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x1C, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4), (0x438, 0x4)] := keep_kk16.trans K17.toL
  clear keep_kk16
  have w17_1c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := (K17.w32 (by decide) (by decide)).trans w16_1c
  have w17_34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K17.w32 (by decide) (by decide)).trans w16_34
  have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K17.w32 (by decide) (by decide)).trans w16_44
  have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K17.w32 (by decide) (by decide)).trans w16_48
  have w17_4c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K17.w32 (by decide) (by decide)).trans w16_4c
  have w17_420 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K17.w32 (by decide) (by decide)).trans w16_420
  have w17_424 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K17.w32 (by decide) (by decide)).trans w16_424
  have w17_428 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 (img% svNewlineAddress) := (K17.w32 (by decide) (by decide)).trans w16_428
  have w17_42c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := (K17.w32 (by decide) (by decide)).trans w16_42c
  have w17_430 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (img% merklePrefixAddress) := (K17.w32 (by decide) (by decide)).trans w16_430
  have w17_434 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 := (K17.w32 (by decide) (by decide)).trans w16_434
  have w17_438 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x438) = kp := by rw [W17, g16_13]
  clear w16_34 w16_434 w16_430 w16_42c w16_428 w16_424 w16_420 w16_4c w16_48 w16_44 w16_1c g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_14 g16_13 g16_12 g16_11 g16_10 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 rg16 W16 K16 fr16 s16 d16
  -- 0x1626: sw
  obtain ⟨n18, d18, s18, fr18, K18, W18, rg18⟩ := sv_sw F E17 s17 sv_at_1626 (off' := 0x1628) (c := 0x43C)
    (by decide) (by rw [g17_14]; sv_addr) (by decide) (by decide)
  have t18 : Steps n0 n18 := t17.trans d18
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.keep K18 (by decide)
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [rg18 sp, g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg18 (3 : Fin 32), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg18 (4 : Fin 32), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = c := by rw [rg18 (8 : Fin 32), g17_8]
  have g18_10 : reg n18 a0 = BitVec.ofNat 32 (img% merklePrefixAddress) := by rw [rg18 a0, g17_10]
  have g18_11 : reg n18 a1 = BitVec.ofNat 32 0x1 := by rw [rg18 a1, g17_11]
  have g18_12 : reg n18 a2 = BitVec.ofNat 32 0x20 := by rw [rg18 a2, g17_12]
  have g18_13 : reg n18 a3 = kp := by rw [rg18 a3, g17_13]
  have g18_14 : reg n18 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by rw [rg18 a4, g17_14]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [rg18 (18 : Fin 32), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [rg18 (19 : Fin 32), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [rg18 (20 : Fin 32), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [rg18 (21 : Fin 32), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [rg18 (22 : Fin 32), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [rg18 (23 : Fin 32), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = x24 := by rw [rg18 (24 : Fin 32), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [rg18 (25 : Fin 32), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [rg18 (26 : Fin 32), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = x27 := by rw [rg18 (27 : Fin 32), g17_27]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x1C, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4), (0x438, 0x4), (0x43C, 0x4)] := keep_kk17.trans K18.toL
  clear keep_kk17
  have w18_1c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := (K18.w32 (by decide) (by decide)).trans w17_1c
  have w18_34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K18.w32 (by decide) (by decide)).trans w17_34
  have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K18.w32 (by decide) (by decide)).trans w17_44
  have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K18.w32 (by decide) (by decide)).trans w17_48
  have w18_4c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K18.w32 (by decide) (by decide)).trans w17_4c
  have w18_420 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K18.w32 (by decide) (by decide)).trans w17_420
  have w18_424 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K18.w32 (by decide) (by decide)).trans w17_424
  have w18_428 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 (img% svNewlineAddress) := (K18.w32 (by decide) (by decide)).trans w17_428
  have w18_42c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := (K18.w32 (by decide) (by decide)).trans w17_42c
  have w18_430 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (img% merklePrefixAddress) := (K18.w32 (by decide) (by decide)).trans w17_430
  have w18_434 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 := (K18.w32 (by decide) (by decide)).trans w17_434
  have w18_438 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x438) = kp := (K18.w32 (by decide) (by decide)).trans w17_438
  have w18_43c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x43C) = BitVec.ofNat 32 0x20 := by rw [W18, g17_12]
  clear w17_438 w17_434 w17_430 w17_42c w17_428 w17_424 w17_420 w17_4c w17_48 w17_44 w17_34 w17_1c g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_14 g17_13 g17_12 g17_11 g17_10 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 rg17 W17 K17 fr17 s17 d17
  -- 0x1628
  obtain ⟨n19, c19, u19⟩ := s18.block svCs11628 E18.self svCs11628_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have s19 : St n19.mem SV n19 0x1632 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have rb19 : ∀ q, reg n19 q = (runBlock svCs11628 (n18.mem, reg n18)).2 q := fun q => by rw [u19.regs]
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
  have g19_8 : reg n19 (8 : Fin 32) = c := by
    rw [rb19, runBlock_reg _ _ _ (8 : Fin 32) s18.zero (by decide), g18_8]
  have g19_13 : reg n19 a3 = kp := by
    rw [rb19, runBlock_reg _ _ _ a3 s18.zero (by decide), g18_13]
  have g19_14 : reg n19 a4 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb19, runBlock_reg _ _ _ a4 s18.zero (by decide), g18_14]
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
  have g19_10 : reg n19 a0 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svCs11628, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_10, g18_11, g18_12, g18_13, g18_14, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_25, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g19_11 : reg n19 a1 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svCs11628, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_10, g18_11, g18_12, g18_13, g18_14, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_25, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g19_12 : reg n19 a2 = BitVec.ofNat 32 0x4 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svCs11628, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_10, g18_11, g18_12, g18_13, g18_14, g18_18, g18_19, g18_20, g18_21, g18_22, g18_23, g18_24, g18_25, g18_26, g18_27, s18.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x1C, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4), (0x438, 0x4), (0x43C, 0x4)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_1c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := by rw [m19]; exact w18_1c
  have w19_34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m19]; exact w18_34
  have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m19]; exact w18_44
  have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m19]; exact w18_48
  have w19_4c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m19]; exact w18_4c
  have w19_420 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := by rw [m19]; exact w18_420
  have w19_424 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := by rw [m19]; exact w18_424
  have w19_428 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 (img% svNewlineAddress) := by rw [m19]; exact w18_428
  have w19_42c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := by rw [m19]; exact w18_42c
  have w19_430 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (img% merklePrefixAddress) := by rw [m19]; exact w18_430
  have w19_434 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 := by rw [m19]; exact w18_434
  have w19_438 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x438) = kp := by rw [m19]; exact w18_438
  have w19_43c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x43C) = BitVec.ofNat 32 0x20 := by rw [m19]; exact w18_43c
  clear w18_43c w18_438 w18_434 w18_430 w18_42c w18_428 w18_424 w18_420 w18_4c w18_48 w18_44 w18_34 w18_1c g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_14 g18_13 g18_12 g18_11 g18_10 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 rg18 W18 K18 fr18 s18 d18
  -- 0x1632: sv_sha256P4F
  obtain ⟨n20, c20, s20, sp20, rk20, K20, D20, fr20⟩ := sv_sha256P4F (oc := 0x400) (pc := 0x420) (l0 := (w44).toNat) (l1 := 1) (l2 := 1) (l3 := 32)
    FW E19 (S2.sv FW RS fR19) RS s19 sv_at_1632 sv_at_1636 (by decide) (by decide) g19_2
    g19_10 g19_11 g19_12 (by decide) (by decide) (by decide)
    w19_420 (by rw [w19_424, ofNat_toNat_self]) w19_428 w19_42c w19_430 w19_434 w19_438 w19_43c
    (.inl l_in) (.inr ⟨by decide, by decide⟩) (.inr ⟨by decide, by decide⟩) (.inl kp_in) (by have := l_in.lo; omega) (by decide) (by decide) (by decide)
  have t20 : Steps n0 n20 := t19.trans c20
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.keepL K20 (by decide)
  rw [sv_mbRo FW fR19 (.inl l_in), sv_mbRo FW fR19 (.inr ⟨by decide, by decide⟩), sv_mbRo FW fR19 (.inr ⟨by decide, by decide⟩), sv_mbRo FW fR19 (.inl kp_in)] at D20
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk20 (3 : Fin 32) (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk20 (4 : Fin 32) (by decide), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = c := by rw [rk20 (8 : Fin 32) (by decide), g19_8]
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
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x1C, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4), (0x438, 0x4), (0x43C, 0x4), (0x400, 0x20)] := keep_kk19.trans K20
  clear keep_kk19
  have w20_1c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := (K20.w32 (by decide) (by decide)).trans w19_1c
  have w20_34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K20.w32 (by decide) (by decide)).trans w19_34
  have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K20.w32 (by decide) (by decide)).trans w19_44
  have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K20.w32 (by decide) (by decide)).trans w19_48
  have w20_4c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K20.w32 (by decide) (by decide)).trans w19_4c
  have w20_420 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K20.w32 (by decide) (by decide)).trans w19_420
  have w20_424 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K20.w32 (by decide) (by decide)).trans w19_424
  have w20_428 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 (img% svNewlineAddress) := (K20.w32 (by decide) (by decide)).trans w19_428
  have w20_42c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := (K20.w32 (by decide) (by decide)).trans w19_42c
  have w20_430 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (img% merklePrefixAddress) := (K20.w32 (by decide) (by decide)).trans w19_430
  have w20_434 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 := (K20.w32 (by decide) (by decide)).trans w19_434
  have w20_438 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x438) = kp := (K20.w32 (by decide) (by decide)).trans w19_438
  have w20_43c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x43C) = BitVec.ofNat 32 0x20 := (K20.w32 (by decide) (by decide)).trans w19_43c
  clear w19_43c w19_438 w19_434 w19_430 w19_42c w19_428 w19_424 w19_420 w19_4c w19_48 w19_44 w19_34 w19_1c g19_12 g19_11 g19_10 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_14 g19_13 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
  have w20_400 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = le4 (sha256 (memBytes M0 (w48) ((w44).toNat) ++ memBytes M0 (BitVec.ofNat 32 (img% svNewlineAddress)) (1) ++ memBytes M0 (BitVec.ofNat 32 (img% merklePrefixAddress)) (1) ++ memBytes M0 (kp) (32))) 0 := ld_digest D20 (by decide)
  -- 0x163A: sw
  obtain ⟨n21, d21, s21, fr21, K21, W21, rg21⟩ := sv_sw F E20 s20 sv_at_163a (off' := 0x163C) (c := 0x30)
    (by decide) (by rw [g20_2]; sv_addr) (by decide) (by decide)
  have t21 : Steps n0 n21 := t20.trans d21
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.keep K21 (by decide)
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [rg21 sp, g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg21 (3 : Fin 32), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg21 (4 : Fin 32), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = c := by rw [rg21 (8 : Fin 32), g20_8]
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
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x1C, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4), (0x438, 0x4), (0x43C, 0x4), (0x400, 0x20), (0x30, 0x4)] := keep_kk20.trans K21.toL
  clear keep_kk20
  have w21_1c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := (K21.w32 (by decide) (by decide)).trans w20_1c
  have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K21.w32 (by decide) (by decide)).trans w20_34
  have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K21.w32 (by decide) (by decide)).trans w20_44
  have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K21.w32 (by decide) (by decide)).trans w20_48
  have w21_4c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K21.w32 (by decide) (by decide)).trans w20_4c
  have w21_400 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = le4 (sha256 (memBytes M0 (w48) ((w44).toNat) ++ memBytes M0 (BitVec.ofNat 32 (img% svNewlineAddress)) (1) ++ memBytes M0 (BitVec.ofNat 32 (img% merklePrefixAddress)) (1) ++ memBytes M0 (kp) (32))) 0 := (K21.w32 (by decide) (by decide)).trans w20_400
  have w21_420 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K21.w32 (by decide) (by decide)).trans w20_420
  have w21_424 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K21.w32 (by decide) (by decide)).trans w20_424
  have w21_428 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 (img% svNewlineAddress) := (K21.w32 (by decide) (by decide)).trans w20_428
  have w21_42c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := (K21.w32 (by decide) (by decide)).trans w20_42c
  have w21_430 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (img% merklePrefixAddress) := (K21.w32 (by decide) (by decide)).trans w20_430
  have w21_434 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 := (K21.w32 (by decide) (by decide)).trans w20_434
  have w21_438 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x438) = kp := (K21.w32 (by decide) (by decide)).trans w20_438
  have w21_43c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x43C) = BitVec.ofNat 32 0x20 := (K21.w32 (by decide) (by decide)).trans w20_43c
  have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = BitVec.ofNat 32 0x0 := by rw [W21, s20.zero]; rfl
  clear w20_43c w20_438 w20_434 w20_430 w20_42c w20_428 w20_424 w20_420 w20_4c w20_48 w20_44 w20_34 w20_1c g20_2 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_8 g20_4 g20_3 V20 E20 fR20 t20 fr20 K20 rk20 sp20 s20 c20
  -- 0x163C: lw
  obtain ⟨n22, d22, u22⟩ := s21.lw E21.self sv_at_163c (off' := 0x1640) (by decide)
    (by rw [g21_2, show B + 0x21A0 + 0x400 = B + 0x21A0 + BitVec.ofNat 32 0x400 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s22 : St n22.mem SV n22 0x1640 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans (.single d22)
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, upd_ne (by decide) (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, upd_ne (by decide) (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = c := by rw [u22.regs, upd_ne (by decide) (by decide), g21_8]
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
  have g22_10 : reg n22 a0 = le4 (sha256 (memBytes M0 (w48) ((w44).toNat) ++ memBytes M0 (BitVec.ofNat 32 (img% svNewlineAddress)) (1) ++ memBytes M0 (BitVec.ofNat 32 (img% merklePrefixAddress)) (1) ++ memBytes M0 (kp) (32))) 0 := by
    rw [u22.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g21_2, show B + 0x21A0 + 0x400 = B + 0x21A0 + BitVec.ofNat 32 0x400 by sv_addr, w21_400]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x1C, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4), (0x438, 0x4), (0x43C, 0x4), (0x400, 0x20), (0x30, 0x4)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_1c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := by rw [m22]; exact w21_1c
  have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = BitVec.ofNat 32 0x0 := by rw [m22]; exact w21_30
  have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m22]; exact w21_34
  have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m22]; exact w21_44
  have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m22]; exact w21_48
  have w22_4c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := by rw [m22]; exact w21_4c
  have w22_400 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = le4 (sha256 (memBytes M0 (w48) ((w44).toNat) ++ memBytes M0 (BitVec.ofNat 32 (img% svNewlineAddress)) (1) ++ memBytes M0 (BitVec.ofNat 32 (img% merklePrefixAddress)) (1) ++ memBytes M0 (kp) (32))) 0 := by rw [m22]; exact w21_400
  have w22_420 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := by rw [m22]; exact w21_420
  have w22_424 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := by rw [m22]; exact w21_424
  have w22_428 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 (img% svNewlineAddress) := by rw [m22]; exact w21_428
  have w22_42c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := by rw [m22]; exact w21_42c
  have w22_430 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (img% merklePrefixAddress) := by rw [m22]; exact w21_430
  have w22_434 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 := by rw [m22]; exact w21_434
  have w22_438 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x438) = kp := by rw [m22]; exact w21_438
  have w22_43c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x43C) = BitVec.ofNat 32 0x20 := by rw [m22]; exact w21_43c
  clear w21_30 w21_43c w21_438 w21_434 w21_430 w21_42c w21_428 w21_424 w21_420 w21_400 w21_4c w21_48 w21_44 w21_34 w21_1c g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 rg21 W21 K21 fr21 s21 d21 w20_400
  -- 0x1640: sw
  obtain ⟨n23, d23, s23, fr23, K23, W23, rg23⟩ := sv_sw F E22 s22 sv_at_1640 (off' := 0x1642) (c := 0x18)
    (by decide) (by rw [g22_2]; sv_addr) (by decide) (by decide)
  have t23 : Steps n0 n23 := t22.trans d23
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.keep K23 (by decide)
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [rg23 sp, g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg23 (3 : Fin 32), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg23 (4 : Fin 32), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = c := by rw [rg23 (8 : Fin 32), g22_8]
  have g23_10 : reg n23 a0 = le4 (sha256 (memBytes M0 (w48) ((w44).toNat) ++ memBytes M0 (BitVec.ofNat 32 (img% svNewlineAddress)) (1) ++ memBytes M0 (BitVec.ofNat 32 (img% merklePrefixAddress)) (1) ++ memBytes M0 (kp) (32))) 0 := by rw [rg23 a0, g22_10]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [rg23 (18 : Fin 32), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [rg23 (19 : Fin 32), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = x20 := by rw [rg23 (20 : Fin 32), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = x21 := by rw [rg23 (21 : Fin 32), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = x22 := by rw [rg23 (22 : Fin 32), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = x23 := by rw [rg23 (23 : Fin 32), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = x24 := by rw [rg23 (24 : Fin 32), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = x25 := by rw [rg23 (25 : Fin 32), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by rw [rg23 (26 : Fin 32), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = x27 := by rw [rg23 (27 : Fin 32), g22_27]
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x1C, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x34, 0x4), (0x438, 0x4), (0x43C, 0x4), (0x400, 0x20), (0x30, 0x4), (0x18, 0x4)] := keep_kk22.trans K23.toL
  clear keep_kk22
  have w23_1c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = kw := (K23.w32 (by decide) (by decide)).trans w22_1c
  have w23_30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = BitVec.ofNat 32 0x0 := (K23.w32 (by decide) (by decide)).trans w22_30
  have w23_34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K23.w32 (by decide) (by decide)).trans w22_34
  have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K23.w32 (by decide) (by decide)).trans w22_44
  have w23_48 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K23.w32 (by decide) (by decide)).trans w22_48
  have w23_4c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q := (K23.w32 (by decide) (by decide)).trans w22_4c
  have w23_400 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = le4 (sha256 (memBytes M0 (w48) ((w44).toNat) ++ memBytes M0 (BitVec.ofNat 32 (img% svNewlineAddress)) (1) ++ memBytes M0 (BitVec.ofNat 32 (img% merklePrefixAddress)) (1) ++ memBytes M0 (kp) (32))) 0 := (K23.w32 (by decide) (by decide)).trans w22_400
  have w23_420 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = w48 := (K23.w32 (by decide) (by decide)).trans w22_420
  have w23_424 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = w44 := (K23.w32 (by decide) (by decide)).trans w22_424
  have w23_428 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 (img% svNewlineAddress) := (K23.w32 (by decide) (by decide)).trans w22_428
  have w23_42c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = BitVec.ofNat 32 0x1 := (K23.w32 (by decide) (by decide)).trans w22_42c
  have w23_430 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (img% merklePrefixAddress) := (K23.w32 (by decide) (by decide)).trans w22_430
  have w23_434 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x434) = BitVec.ofNat 32 0x1 := (K23.w32 (by decide) (by decide)).trans w22_434
  have w23_438 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x438) = kp := (K23.w32 (by decide) (by decide)).trans w22_438
  have w23_43c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x43C) = BitVec.ofNat 32 0x20 := (K23.w32 (by decide) (by decide)).trans w22_43c
  have w23_18 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = le4 (sha256 (memBytes M0 (w48) ((w44).toNat) ++ memBytes M0 (BitVec.ofNat 32 (img% svNewlineAddress)) (1) ++ memBytes M0 (BitVec.ofNat 32 (img% merklePrefixAddress)) (1) ++ memBytes M0 (kp) (32))) 0 := by rw [W23, g22_10]
  clear w22_43c w22_438 w22_434 w22_430 w22_42c w22_428 w22_424 w22_420 w22_400 w22_4c w22_48 w22_44 w22_34 w22_30 w22_1c g22_10 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22
  exact .inr ⟨n23, t23, s23, E23, V23, fR23, g23_2, g23_3, g23_4, g23_8, g23_18, g23_19, g23_20, g23_21, g23_22, g23_23, g23_24, g23_25, g23_26, g23_27, w23_18, w23_1c, w23_30, w23_34, w23_44, w23_48, w23_4c, w23_400, w23_420, w23_424, w23_428, w23_42c, w23_430, w23_434, w23_438, w23_43c, keep_kk23.mono (by decide)⟩

end C3.RV32.Sv
