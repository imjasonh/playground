import C3BootProofs.Proofs.SvCs

/-!
# `sigstore::verify`: a base64 group of a signature line

One pass of the base64 group loop, from 0x16D4 back to it: the next four bytes decode as base64, their first `=` is byte 0, and this is the last group.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svCg016ea : List BInstr :=
  [.aluImm .sll a1 a1 0x8]
theorem svCg016ea_end : blockEnd sigstoreVerifyCode 0x16EA svCg016ea = some 0x16EC := by
  simp only [svCg016ea]
  rw [blockEnd, sv_at_16ea]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCg016ec : List BInstr :=
  [.aluImm .sll a2 a2 0x10]
theorem svCg016ec_end : blockEnd sigstoreVerifyCode 0x16EC svCg016ec = some 0x16EE := by
  simp only [svCg016ec]
  rw [blockEnd, sv_at_16ec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCg016ee : List BInstr :=
  [.aluImm .sll a3 a3 0x18]
theorem svCg016ee_end : blockEnd sigstoreVerifyCode 0x16EE svCg016ee = some 0x16F0 := by
  simp only [svCg016ee]
  rw [blockEnd, sv_at_16ee]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCg016f0 : List BInstr :=
  [.alu .or a1 a1 a4]
theorem svCg016f0_end : blockEnd sigstoreVerifyCode 0x16F0 svCg016f0 = some 0x16F2 := by
  simp only [svCg016f0]
  rw [blockEnd, sv_at_16f0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCg016f2 : List BInstr :=
  [.alu .or a2 a2 a3]
theorem svCg016f2_end : blockEnd sigstoreVerifyCode 0x16F2 svCg016f2 = some 0x16F4 := by
  simp only [svCg016f2]
  rw [blockEnd, sv_at_16f2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCg016f4 : List BInstr :=
  [.alu .or a1 a1 a2]
theorem svCg016f4_end : blockEnd sigstoreVerifyCode 0x16F4 svCg016f4 = some 0x16F6 := by
  simp only [svCg016f4]
  rw [blockEnd, sv_at_16f4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCg016f6 : List BInstr :=
  [.aluImm .add a2 a0 0x4]
theorem svCg016f6_end : blockEnd sigstoreVerifyCode 0x16F6 svCg016f6 = some 0x16FA := by
  simp only [svCg016f6]
  rw [blockEnd, sv_at_16f6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCg01700 : List BInstr :=
  [.aluImm .add (21 : Fin 32) (21 : Fin 32) 0x1]
theorem svCg01700_end : blockEnd sigstoreVerifyCode 0x1700 svCg01700 = some 0x1702 := by
  simp only [svCg01700]
  rw [blockEnd, sv_at_1700]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCg01702 : List BInstr :=
  [.aluImm .add a1 x0 0x4]
theorem svCg01702_end : blockEnd sigstoreVerifyCode 0x1702 svCg01702 = some 0x1704 := by
  simp only [svCg01702]
  rw [blockEnd, sv_at_1702]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCg0170a : List BInstr :=
  [.aluImm .add a2 a2 0xFFFFFFC3]
theorem svCg0170a_end : blockEnd sigstoreVerifyCode 0x170A svCg0170a = some 0x170E := by
  simp only [svCg0170a]
  rw [blockEnd, sv_at_170a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCg0170e : List BInstr :=
  [.aluImm .add a0 a0 0x1]
theorem svCg0170e_end : blockEnd sigstoreVerifyCode 0x170E svCg0170e = some 0x1710 := by
  simp only [svCg0170e]
  rw [blockEnd, sv_at_170e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCg01710 : List BInstr :=
  [.aluImm .add a1 a1 0xFFFFFFFF]
theorem svCg01710_end : blockEnd sigstoreVerifyCode 0x1710 svCg01710 = some 0x1712 := by
  simp only [svCg01710]
  rw [blockEnd, sv_at_1710]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCg01878 : List BInstr :=
  [.aluImm .add (25 : Fin 32) x0 0x1A]
theorem svCg01878_end : blockEnd sigstoreVerifyCode 0x1878 svCg01878 = some 0x187A := by
  simp only [svCg01878]
  rw [blockEnd, sv_at_1878]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCg0171a : List BInstr :=
  [.aluImm .add a0 sp 0x420, .aluImm .add a1 sp 0x400, .aluImm .add a2 x0 0x4, .aluImm .add a3 sp 0x370, .aluImm .add a4 x0 0x3]
theorem svCg0171a_end : blockEnd sigstoreVerifyCode 0x171A svCg0171a = some 0x1728 := by
  simp only [svCg0171a]
  rw [blockEnd, sv_at_171a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_171e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1722]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1724]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_1726]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_cg0 {B out bp x20 x21 x22 x23 x24 x25 x26 x27 f w38 w50 kh w48 w44 kp ckp bl pg gi nl ns1 ni ns10 np w8 wc w10 : Word} {sg : Bytes} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x16D4 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = nl)
    (g0_9 : reg n0 (9 : Fin 32) = ns1)
    (g0_10 : reg n0 a0 = pg)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = gi)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = ni)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = ns10)
    (g0_27 : reg n0 (27 : Fin 32) = np)
    (w0_8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8)
    (w0_c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc)
    (w0_10 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10)
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh)
    (w0_24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl)
    (w0_28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp)
    (w0_2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
    (b0_14 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0))
    (q0_1fc : ∀ j, j < 63 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0))
    (hne : pg ≠ w8)
    (CK0 : SvCkCode M0)
    (pg_in : SvIn B pg 4)
    (pb1 : SvIn B (pg + 0x1) 1)
    (pb2 : SvIn B (pg + 0x2) 1)
    (pb3 : SvIn B (pg + 0x3) 1)
    (pc0 : SvIn B (pg) 1)
    (hq0 : M0 (pg) = 0x3D) :
    (¬ (((gi) + BitVec.ofNat 32 0x1 = wc) ∧ ∃ bq27, base64Decode (memBytes M0 pg 4) = some bq27 ∧ (bq27.length ≤ 3) ∧ True) ∧ SvErrRet B out v n0) ∨
    (((gi) + BitVec.ofNat 32 0x1 = wc) ∧
    ∃ bq27, base64Decode (memBytes M0 pg 4) = some bq27 ∧
    (bq27.length ≤ 3) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x16D4 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = nl ∧
        reg n' (9 : Fin 32) = ns1 ∧
        reg n' a0 = (pg) + BitVec.ofNat 32 0x4 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = ni ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = ns10 ∧
        reg n' (27 : Fin 32) = np ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x16D4: lw
  obtain ⟨n1, d1, u1⟩ := s0.lw E0.self sv_at_16d4 (off' := 0x16D6) (by decide)
    (by rw [g0_2, show B + 0x21A0 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0x8 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s1 : St n1.mem SV n1 0x16D6 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, upd_ne (by decide) (by decide), g0_4]
  have g1_8 : reg n1 (8 : Fin 32) = nl := by rw [u1.regs, upd_ne (by decide) (by decide), g0_8]
  have g1_9 : reg n1 (9 : Fin 32) = ns1 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_9]
  have g1_10 : reg n1 a0 = pg := by rw [u1.regs, upd_ne (by decide) (by decide), g0_10]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, upd_ne (by decide) (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, upd_ne (by decide) (by decide), g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = x20 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = gi := by rw [u1.regs, upd_ne (by decide) (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = x22 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = x23 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = ni := by rw [u1.regs, upd_ne (by decide) (by decide), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = x25 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = ns10 := by rw [u1.regs, upd_ne (by decide) (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = np := by rw [u1.regs, upd_ne (by decide) (by decide), g0_27]
  have g1_11 : reg n1 a1 = w8 := by
    rw [u1.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g0_2, show B + 0x21A0 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0x8 by sv_addr, w0_8]
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_8 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m1]; exact w0_8
  have w1_c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m1]; exact w0_c
  have w1_10 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m1]; exact w0_10
  have w1_18 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m1]; exact w0_18
  have w1_24 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m1]; exact w0_24
  have w1_28 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m1]; exact w0_28
  have w1_2c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m1]; exact w0_2c
  have w1_30 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m1]; exact w0_30
  have w1_34 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m1]; exact w0_34
  have w1_38 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m1]; exact w0_38
  have w1_44 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m1]; exact w0_44
  have w1_48 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m1]; exact w0_48
  have w1_50 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m1]; exact w0_50
  have b1_14 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m1]; exact b0_14
  have q1_1fc : ∀ j, j < 63 → n1.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m1]; exact q0_1fc j hj
  -- 0x16D6: branch, not taken
  obtain ⟨n2, d2, u2⟩ := s1.notTaken E1.self 0x16DA sv_at_16d6
    (by decide) (by rw [g1_10, g1_11]; exact br_beq_f hne)
  have s2 : St n2.mem SV n2 0x16DA (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, g1_4]
  have g2_8 : reg n2 (8 : Fin 32) = nl := by rw [u2.regs, g1_8]
  have g2_9 : reg n2 (9 : Fin 32) = ns1 := by rw [u2.regs, g1_9]
  have g2_10 : reg n2 a0 = pg := by rw [u2.regs, g1_10]
  have g2_11 : reg n2 a1 = w8 := by rw [u2.regs, g1_11]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = x20 := by rw [u2.regs, g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = gi := by rw [u2.regs, g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = x22 := by rw [u2.regs, g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = x23 := by rw [u2.regs, g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = ni := by rw [u2.regs, g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = x25 := by rw [u2.regs, g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = ns10 := by rw [u2.regs, g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = np := by rw [u2.regs, g1_27]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_8 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m2]; exact w1_8
  have w2_c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m2]; exact w1_c
  have w2_10 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m2]; exact w1_10
  have w2_18 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m2]; exact w1_18
  have w2_24 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m2]; exact w1_24
  have w2_28 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m2]; exact w1_28
  have w2_2c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m2]; exact w1_2c
  have w2_30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m2]; exact w1_30
  have w2_34 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m2]; exact w1_34
  have w2_38 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m2]; exact w1_38
  have w2_44 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m2]; exact w1_44
  have w2_48 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m2]; exact w1_48
  have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m2]; exact w1_50
  have b2_14 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m2]; exact b1_14
  have q2_1fc : ∀ j, j < 63 → n2.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m2]; exact q1_1fc j hj
  clear q1_1fc b1_14 w1_50 w1_48 w1_44 w1_38 w1_34 w1_30 w1_2c w1_28 w1_24 w1_18 w1_10 w1_c w1_8 g1_11 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_10 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x16DA: lbu from the bundle
  obtain ⟨n3, d3, u3⟩ := s2.lbu E2.self sv_at_16da (off' := 0x16DE) (by decide)
  have s3 : St n3.mem SV n3 0x16DE (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = nl := by rw [u3.regs, upd_ne (by decide) (by decide), g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = ns1 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_9]
  have g3_10 : reg n3 a0 = pg := by rw [u3.regs, upd_ne (by decide) (by decide), g2_10]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = x20 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = gi := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = x22 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = x23 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = ni := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = x25 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = ns10 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = np := by rw [u3.regs, upd_ne (by decide) (by decide), g2_27]
  have g3_11 : reg n3 a1 = (M0 ((pg) + 0x1)).zeroExtend 32 := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_10, fR2 _ (pb1.r0 (by decide))]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_8 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m3]; exact w2_8
  have w3_c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m3]; exact w2_c
  have w3_10 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m3]; exact w2_10
  have w3_18 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m3]; exact w2_18
  have w3_24 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m3]; exact w2_24
  have w3_28 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m3]; exact w2_28
  have w3_2c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m3]; exact w2_2c
  have w3_30 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m3]; exact w2_30
  have w3_34 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m3]; exact w2_34
  have w3_38 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m3]; exact w2_38
  have w3_44 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m3]; exact w2_44
  have w3_48 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m3]; exact w2_48
  have w3_50 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m3]; exact w2_50
  have b3_14 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m3]; exact b2_14
  have q3_1fc : ∀ j, j < 63 → n3.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m3]; exact q2_1fc j hj
  clear q2_1fc b2_14 w2_50 w2_48 w2_44 w2_38 w2_34 w2_30 w2_2c w2_28 w2_24 w2_18 w2_10 w2_c w2_8 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_11 g2_10 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x16DE: lbu from the bundle
  obtain ⟨n4, d4, u4⟩ := s3.lbu E3.self sv_at_16de (off' := 0x16E2) (by decide)
  have s4 : St n4.mem SV n4 0x16E2 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_4]
  have g4_8 : reg n4 (8 : Fin 32) = nl := by rw [u4.regs, upd_ne (by decide) (by decide), g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = ns1 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_9]
  have g4_10 : reg n4 a0 = pg := by rw [u4.regs, upd_ne (by decide) (by decide), g3_10]
  have g4_11 : reg n4 a1 = (M0 ((pg) + 0x1)).zeroExtend 32 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_11]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, upd_ne (by decide) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = x20 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = gi := by rw [u4.regs, upd_ne (by decide) (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = x22 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = x23 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = ni := by rw [u4.regs, upd_ne (by decide) (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = x25 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = ns10 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = np := by rw [u4.regs, upd_ne (by decide) (by decide), g3_27]
  have g4_12 : reg n4 a2 = (M0 ((pg) + 0x2)).zeroExtend 32 := by
    rw [u4.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g3_10, fR3 _ (pb2.r0 (by decide))]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_8 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m4]; exact w3_8
  have w4_c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m4]; exact w3_c
  have w4_10 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m4]; exact w3_10
  have w4_18 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m4]; exact w3_18
  have w4_24 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m4]; exact w3_24
  have w4_28 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m4]; exact w3_28
  have w4_2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m4]; exact w3_2c
  have w4_30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m4]; exact w3_30
  have w4_34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m4]; exact w3_34
  have w4_38 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m4]; exact w3_38
  have w4_44 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m4]; exact w3_44
  have w4_48 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m4]; exact w3_48
  have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m4]; exact w3_50
  have b4_14 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m4]; exact b3_14
  have q4_1fc : ∀ j, j < 63 → n4.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m4]; exact q3_1fc j hj
  clear q3_1fc b3_14 w3_50 w3_48 w3_44 w3_38 w3_34 w3_30 w3_2c w3_28 w3_24 w3_18 w3_10 w3_c w3_8 g3_11 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_10 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x16E2: lbu from the bundle
  obtain ⟨n5, d5, u5⟩ := s4.lbu E4.self sv_at_16e2 (off' := 0x16E6) (by decide)
  have s5 : St n5.mem SV n5 0x16E6 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = nl := by rw [u5.regs, upd_ne (by decide) (by decide), g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = ns1 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_9]
  have g5_10 : reg n5 a0 = pg := by rw [u5.regs, upd_ne (by decide) (by decide), g4_10]
  have g5_11 : reg n5 a1 = (M0 ((pg) + 0x1)).zeroExtend 32 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_11]
  have g5_12 : reg n5 a2 = (M0 ((pg) + 0x2)).zeroExtend 32 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_12]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, upd_ne (by decide) (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = gi := by rw [u5.regs, upd_ne (by decide) (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = ni := by rw [u5.regs, upd_ne (by decide) (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = ns10 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = np := by rw [u5.regs, upd_ne (by decide) (by decide), g4_27]
  have g5_13 : reg n5 a3 = (M0 ((pg) + 0x3)).zeroExtend 32 := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g4_10, fR4 _ (pb3.r0 (by decide))]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_8 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m5]; exact w4_8
  have w5_c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m5]; exact w4_c
  have w5_10 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m5]; exact w4_10
  have w5_18 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m5]; exact w4_18
  have w5_24 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m5]; exact w4_24
  have w5_28 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m5]; exact w4_28
  have w5_2c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m5]; exact w4_2c
  have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m5]; exact w4_30
  have w5_34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m5]; exact w4_34
  have w5_38 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m5]; exact w4_38
  have w5_44 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m5]; exact w4_44
  have w5_48 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m5]; exact w4_48
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m5]; exact w4_50
  have b5_14 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m5]; exact b4_14
  have q5_1fc : ∀ j, j < 63 → n5.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m5]; exact q4_1fc j hj
  clear q4_1fc b4_14 w4_50 w4_48 w4_44 w4_38 w4_34 w4_30 w4_2c w4_28 w4_24 w4_18 w4_10 w4_c w4_8 g4_12 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_11 g4_10 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  -- 0x16E6: lbu from the bundle
  obtain ⟨n6, d6, u6⟩ := s5.lbu E5.self sv_at_16e6 (off' := 0x16EA) (by decide)
  have s6 : St n6.mem SV n6 0x16EA (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = nl := by rw [u6.regs, upd_ne (by decide) (by decide), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = ns1 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_9]
  have g6_10 : reg n6 a0 = pg := by rw [u6.regs, upd_ne (by decide) (by decide), g5_10]
  have g6_11 : reg n6 a1 = (M0 ((pg) + 0x1)).zeroExtend 32 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_11]
  have g6_12 : reg n6 a2 = (M0 ((pg) + 0x2)).zeroExtend 32 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_12]
  have g6_13 : reg n6 a3 = (M0 ((pg) + 0x3)).zeroExtend 32 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_13]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, upd_ne (by decide) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = x20 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = gi := by rw [u6.regs, upd_ne (by decide) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = ni := by rw [u6.regs, upd_ne (by decide) (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = ns10 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = np := by rw [u6.regs, upd_ne (by decide) (by decide), g5_27]
  have g6_14 : reg n6 a4 = (M0 (pg)).zeroExtend 32 := by
    rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g5_10, show (pg) + 0x0 = pg from BitVec.add_zero _, fR5 _ (pg_in.r0 (by decide))]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_8 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m6]; exact w5_8
  have w6_c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m6]; exact w5_c
  have w6_10 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m6]; exact w5_10
  have w6_18 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m6]; exact w5_18
  have w6_24 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m6]; exact w5_24
  have w6_28 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m6]; exact w5_28
  have w6_2c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m6]; exact w5_2c
  have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m6]; exact w5_30
  have w6_34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m6]; exact w5_34
  have w6_38 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m6]; exact w5_38
  have w6_44 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m6]; exact w5_44
  have w6_48 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m6]; exact w5_48
  have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m6]; exact w5_50
  have b6_14 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m6]; exact b5_14
  have q6_1fc : ∀ j, j < 63 → n6.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m6]; exact q5_1fc j hj
  clear q5_1fc b5_14 w5_50 w5_48 w5_44 w5_38 w5_34 w5_30 w5_2c w5_28 w5_24 w5_18 w5_10 w5_c w5_8 g5_13 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_12 g5_11 g5_10 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  -- 0x16EA
  obtain ⟨n7, c7, u7⟩ := s6.block svCg016ea E6.self svCg016ea_end
    ⟨trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem SV n7 0x16EC (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have rb7 : ∀ q, reg n7 q = (runBlock svCg016ea (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
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
  have g7_8 : reg n7 (8 : Fin 32) = nl := by
    rw [rb7, runBlock_reg _ _ _ (8 : Fin 32) s6.zero (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = ns1 := by
    rw [rb7, runBlock_reg _ _ _ (9 : Fin 32) s6.zero (by decide), g6_9]
  have g7_10 : reg n7 a0 = pg := by
    rw [rb7, runBlock_reg _ _ _ a0 s6.zero (by decide), g6_10]
  have g7_12 : reg n7 a2 = (M0 ((pg) + 0x2)).zeroExtend 32 := by
    rw [rb7, runBlock_reg _ _ _ a2 s6.zero (by decide), g6_12]
  have g7_13 : reg n7 a3 = (M0 ((pg) + 0x3)).zeroExtend 32 := by
    rw [rb7, runBlock_reg _ _ _ a3 s6.zero (by decide), g6_13]
  have g7_14 : reg n7 a4 = (M0 (pg)).zeroExtend 32 := by
    rw [rb7, runBlock_reg _ _ _ a4 s6.zero (by decide), g6_14]
  have g7_18 : reg n7 (18 : Fin 32) = out := by
    rw [rb7, runBlock_reg _ _ _ (18 : Fin 32) s6.zero (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by
    rw [rb7, runBlock_reg _ _ _ (19 : Fin 32) s6.zero (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = x20 := by
    rw [rb7, runBlock_reg _ _ _ (20 : Fin 32) s6.zero (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = gi := by
    rw [rb7, runBlock_reg _ _ _ (21 : Fin 32) s6.zero (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = x22 := by
    rw [rb7, runBlock_reg _ _ _ (22 : Fin 32) s6.zero (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = x23 := by
    rw [rb7, runBlock_reg _ _ _ (23 : Fin 32) s6.zero (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = ni := by
    rw [rb7, runBlock_reg _ _ _ (24 : Fin 32) s6.zero (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by
    rw [rb7, runBlock_reg _ _ _ (25 : Fin 32) s6.zero (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = ns10 := by
    rw [rb7, runBlock_reg _ _ _ (26 : Fin 32) s6.zero (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = np := by
    rw [rb7, runBlock_reg _ _ _ (27 : Fin 32) s6.zero (by decide), g6_27]
  have g7_11 : reg n7 a1 = aluEval .sll ((M0 ((pg) + 0x1)).zeroExtend 32) (BitVec.ofNat 32 0x8) := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svCg016ea, upd, ↓reduceIte]; rw [g6_11] <;> rfl
  have keep_kk7 : SvKeepL B n0.mem n7.mem [] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_8 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m7]; exact w6_8
  have w7_c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m7]; exact w6_c
  have w7_10 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m7]; exact w6_10
  have w7_18 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m7]; exact w6_18
  have w7_24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m7]; exact w6_24
  have w7_28 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m7]; exact w6_28
  have w7_2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m7]; exact w6_2c
  have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m7]; exact w6_30
  have w7_34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m7]; exact w6_34
  have w7_38 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m7]; exact w6_38
  have w7_44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m7]; exact w6_44
  have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m7]; exact w6_48
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m7]; exact w6_50
  have b7_14 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m7]; exact b6_14
  have q7_1fc : ∀ j, j < 63 → n7.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m7]; exact q6_1fc j hj
  clear q6_1fc b6_14 w6_50 w6_48 w6_44 w6_38 w6_34 w6_30 w6_2c w6_28 w6_24 w6_18 w6_10 w6_c w6_8 g6_14 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_13 g6_12 g6_11 g6_10 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  -- 0x16EC
  obtain ⟨n8, c8, u8⟩ := s7.block svCg016ec E7.self svCg016ec_end
    ⟨trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem SV n8 0x16EE (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock svCg016ec (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
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
  have g8_8 : reg n8 (8 : Fin 32) = nl := by
    rw [rb8, runBlock_reg _ _ _ (8 : Fin 32) s7.zero (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = ns1 := by
    rw [rb8, runBlock_reg _ _ _ (9 : Fin 32) s7.zero (by decide), g7_9]
  have g8_10 : reg n8 a0 = pg := by
    rw [rb8, runBlock_reg _ _ _ a0 s7.zero (by decide), g7_10]
  have g8_11 : reg n8 a1 = aluEval .sll ((M0 ((pg) + 0x1)).zeroExtend 32) (BitVec.ofNat 32 0x8) := by
    rw [rb8, runBlock_reg _ _ _ a1 s7.zero (by decide), g7_11]
  have g8_13 : reg n8 a3 = (M0 ((pg) + 0x3)).zeroExtend 32 := by
    rw [rb8, runBlock_reg _ _ _ a3 s7.zero (by decide), g7_13]
  have g8_14 : reg n8 a4 = (M0 (pg)).zeroExtend 32 := by
    rw [rb8, runBlock_reg _ _ _ a4 s7.zero (by decide), g7_14]
  have g8_18 : reg n8 (18 : Fin 32) = out := by
    rw [rb8, runBlock_reg _ _ _ (18 : Fin 32) s7.zero (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by
    rw [rb8, runBlock_reg _ _ _ (19 : Fin 32) s7.zero (by decide), g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = x20 := by
    rw [rb8, runBlock_reg _ _ _ (20 : Fin 32) s7.zero (by decide), g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = gi := by
    rw [rb8, runBlock_reg _ _ _ (21 : Fin 32) s7.zero (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = x22 := by
    rw [rb8, runBlock_reg _ _ _ (22 : Fin 32) s7.zero (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = x23 := by
    rw [rb8, runBlock_reg _ _ _ (23 : Fin 32) s7.zero (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = ni := by
    rw [rb8, runBlock_reg _ _ _ (24 : Fin 32) s7.zero (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by
    rw [rb8, runBlock_reg _ _ _ (25 : Fin 32) s7.zero (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = ns10 := by
    rw [rb8, runBlock_reg _ _ _ (26 : Fin 32) s7.zero (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = np := by
    rw [rb8, runBlock_reg _ _ _ (27 : Fin 32) s7.zero (by decide), g7_27]
  have g8_12 : reg n8 a2 = aluEval .sll ((M0 ((pg) + 0x2)).zeroExtend 32) (BitVec.ofNat 32 0x10) := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svCg016ec, upd, ↓reduceIte]; rw [g7_12] <;> rfl
  have keep_kk8 : SvKeepL B n0.mem n8.mem [] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_8 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m8]; exact w7_8
  have w8_c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m8]; exact w7_c
  have w8_10 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m8]; exact w7_10
  have w8_18 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m8]; exact w7_18
  have w8_24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m8]; exact w7_24
  have w8_28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m8]; exact w7_28
  have w8_2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m8]; exact w7_2c
  have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m8]; exact w7_30
  have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m8]; exact w7_34
  have w8_38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m8]; exact w7_38
  have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m8]; exact w7_44
  have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m8]; exact w7_48
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m8]; exact w7_50
  have b8_14 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m8]; exact b7_14
  have q8_1fc : ∀ j, j < 63 → n8.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m8]; exact q7_1fc j hj
  clear q7_1fc b7_14 w7_50 w7_48 w7_44 w7_38 w7_34 w7_30 w7_2c w7_28 w7_24 w7_18 w7_10 w7_c w7_8 g7_11 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_14 g7_13 g7_12 g7_10 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
  -- 0x16EE
  obtain ⟨n9, c9, u9⟩ := s8.block svCg016ee E8.self svCg016ee_end
    ⟨trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem SV n9 0x16F0 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock svCg016ee (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
  have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans c9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by
    rw [rb9, runBlock_reg _ _ _ sp s8.zero (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb9, runBlock_reg _ _ _ (3 : Fin 32) s8.zero (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb9, runBlock_reg _ _ _ (4 : Fin 32) s8.zero (by decide), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = nl := by
    rw [rb9, runBlock_reg _ _ _ (8 : Fin 32) s8.zero (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = ns1 := by
    rw [rb9, runBlock_reg _ _ _ (9 : Fin 32) s8.zero (by decide), g8_9]
  have g9_10 : reg n9 a0 = pg := by
    rw [rb9, runBlock_reg _ _ _ a0 s8.zero (by decide), g8_10]
  have g9_11 : reg n9 a1 = aluEval .sll ((M0 ((pg) + 0x1)).zeroExtend 32) (BitVec.ofNat 32 0x8) := by
    rw [rb9, runBlock_reg _ _ _ a1 s8.zero (by decide), g8_11]
  have g9_12 : reg n9 a2 = aluEval .sll ((M0 ((pg) + 0x2)).zeroExtend 32) (BitVec.ofNat 32 0x10) := by
    rw [rb9, runBlock_reg _ _ _ a2 s8.zero (by decide), g8_12]
  have g9_14 : reg n9 a4 = (M0 (pg)).zeroExtend 32 := by
    rw [rb9, runBlock_reg _ _ _ a4 s8.zero (by decide), g8_14]
  have g9_18 : reg n9 (18 : Fin 32) = out := by
    rw [rb9, runBlock_reg _ _ _ (18 : Fin 32) s8.zero (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by
    rw [rb9, runBlock_reg _ _ _ (19 : Fin 32) s8.zero (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = x20 := by
    rw [rb9, runBlock_reg _ _ _ (20 : Fin 32) s8.zero (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = gi := by
    rw [rb9, runBlock_reg _ _ _ (21 : Fin 32) s8.zero (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = x22 := by
    rw [rb9, runBlock_reg _ _ _ (22 : Fin 32) s8.zero (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = x23 := by
    rw [rb9, runBlock_reg _ _ _ (23 : Fin 32) s8.zero (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = ni := by
    rw [rb9, runBlock_reg _ _ _ (24 : Fin 32) s8.zero (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by
    rw [rb9, runBlock_reg _ _ _ (25 : Fin 32) s8.zero (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = ns10 := by
    rw [rb9, runBlock_reg _ _ _ (26 : Fin 32) s8.zero (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = np := by
    rw [rb9, runBlock_reg _ _ _ (27 : Fin 32) s8.zero (by decide), g8_27]
  have g9_13 : reg n9 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svCg016ee, upd, ↓reduceIte]; rw [g8_13] <;> rfl
  have keep_kk9 : SvKeepL B n0.mem n9.mem [] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_8 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m9]; exact w8_8
  have w9_c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m9]; exact w8_c
  have w9_10 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m9]; exact w8_10
  have w9_18 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m9]; exact w8_18
  have w9_24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m9]; exact w8_24
  have w9_28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m9]; exact w8_28
  have w9_2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m9]; exact w8_2c
  have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m9]; exact w8_30
  have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m9]; exact w8_34
  have w9_38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m9]; exact w8_38
  have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m9]; exact w8_44
  have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m9]; exact w8_48
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m9]; exact w8_50
  have b9_14 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m9]; exact b8_14
  have q9_1fc : ∀ j, j < 63 → n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m9]; exact q8_1fc j hj
  clear q8_1fc b8_14 w8_50 w8_48 w8_44 w8_38 w8_34 w8_30 w8_2c w8_28 w8_24 w8_18 w8_10 w8_c w8_8 g8_12 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_14 g8_13 g8_11 g8_10 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
  -- 0x16F0
  obtain ⟨n10, c10, u10⟩ := s9.block svCg016f0 E9.self svCg016f0_end
    ⟨trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0x16F2 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock svCg016f0 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
  have g10_8 : reg n10 (8 : Fin 32) = nl := by
    rw [rb10, runBlock_reg _ _ _ (8 : Fin 32) s9.zero (by decide), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = ns1 := by
    rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
  have g10_10 : reg n10 a0 = pg := by
    rw [rb10, runBlock_reg _ _ _ a0 s9.zero (by decide), g9_10]
  have g10_12 : reg n10 a2 = aluEval .sll ((M0 ((pg) + 0x2)).zeroExtend 32) (BitVec.ofNat 32 0x10) := by
    rw [rb10, runBlock_reg _ _ _ a2 s9.zero (by decide), g9_12]
  have g10_13 : reg n10 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by
    rw [rb10, runBlock_reg _ _ _ a3 s9.zero (by decide), g9_13]
  have g10_14 : reg n10 a4 = (M0 (pg)).zeroExtend 32 := by
    rw [rb10, runBlock_reg _ _ _ a4 s9.zero (by decide), g9_14]
  have g10_18 : reg n10 (18 : Fin 32) = out := by
    rw [rb10, runBlock_reg _ _ _ (18 : Fin 32) s9.zero (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by
    rw [rb10, runBlock_reg _ _ _ (19 : Fin 32) s9.zero (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = x20 := by
    rw [rb10, runBlock_reg _ _ _ (20 : Fin 32) s9.zero (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = gi := by
    rw [rb10, runBlock_reg _ _ _ (21 : Fin 32) s9.zero (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = x22 := by
    rw [rb10, runBlock_reg _ _ _ (22 : Fin 32) s9.zero (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = x23 := by
    rw [rb10, runBlock_reg _ _ _ (23 : Fin 32) s9.zero (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = ni := by
    rw [rb10, runBlock_reg _ _ _ (24 : Fin 32) s9.zero (by decide), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by
    rw [rb10, runBlock_reg _ _ _ (25 : Fin 32) s9.zero (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = ns10 := by
    rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = np := by
    rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
  have g10_11 : reg n10 a1 = (aluEval .sll ((M0 ((pg) + 0x1)).zeroExtend 32) (BitVec.ofNat 32 0x8)) ||| ((M0 (pg)).zeroExtend 32) := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svCg016f0, upd, ↓reduceIte]; rw [g9_11, g9_14] <;> rfl
  have keep_kk10 : SvKeepL B n0.mem n10.mem [] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_8 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m10]; exact w9_8
  have w10_c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m10]; exact w9_c
  have w10_10 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m10]; exact w9_10
  have w10_18 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m10]; exact w9_18
  have w10_24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m10]; exact w9_24
  have w10_28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m10]; exact w9_28
  have w10_2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m10]; exact w9_2c
  have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m10]; exact w9_30
  have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m10]; exact w9_34
  have w10_38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m10]; exact w9_38
  have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m10]; exact w9_44
  have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m10]; exact w9_48
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m10]; exact w9_50
  have b10_14 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m10]; exact b9_14
  have q10_1fc : ∀ j, j < 63 → n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m10]; exact q9_1fc j hj
  clear q9_1fc b9_14 w9_50 w9_48 w9_44 w9_38 w9_34 w9_30 w9_2c w9_28 w9_24 w9_18 w9_10 w9_c w9_8 g9_13 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_14 g9_12 g9_11 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  -- 0x16F2
  obtain ⟨n11, c11, u11⟩ := s10.block svCg016f2 E10.self svCg016f2_end
    ⟨trivial, trivial⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have s11 : St n11.mem SV n11 0x16F4 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have rb11 : ∀ q, reg n11 q = (runBlock svCg016f2 (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
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
  have g11_8 : reg n11 (8 : Fin 32) = nl := by
    rw [rb11, runBlock_reg _ _ _ (8 : Fin 32) s10.zero (by decide), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = ns1 := by
    rw [rb11, runBlock_reg _ _ _ (9 : Fin 32) s10.zero (by decide), g10_9]
  have g11_10 : reg n11 a0 = pg := by
    rw [rb11, runBlock_reg _ _ _ a0 s10.zero (by decide), g10_10]
  have g11_11 : reg n11 a1 = (aluEval .sll ((M0 ((pg) + 0x1)).zeroExtend 32) (BitVec.ofNat 32 0x8)) ||| ((M0 (pg)).zeroExtend 32) := by
    rw [rb11, runBlock_reg _ _ _ a1 s10.zero (by decide), g10_11]
  have g11_13 : reg n11 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by
    rw [rb11, runBlock_reg _ _ _ a3 s10.zero (by decide), g10_13]
  have g11_14 : reg n11 a4 = (M0 (pg)).zeroExtend 32 := by
    rw [rb11, runBlock_reg _ _ _ a4 s10.zero (by decide), g10_14]
  have g11_18 : reg n11 (18 : Fin 32) = out := by
    rw [rb11, runBlock_reg _ _ _ (18 : Fin 32) s10.zero (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by
    rw [rb11, runBlock_reg _ _ _ (19 : Fin 32) s10.zero (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by
    rw [rb11, runBlock_reg _ _ _ (20 : Fin 32) s10.zero (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = gi := by
    rw [rb11, runBlock_reg _ _ _ (21 : Fin 32) s10.zero (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by
    rw [rb11, runBlock_reg _ _ _ (22 : Fin 32) s10.zero (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = x23 := by
    rw [rb11, runBlock_reg _ _ _ (23 : Fin 32) s10.zero (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = ni := by
    rw [rb11, runBlock_reg _ _ _ (24 : Fin 32) s10.zero (by decide), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by
    rw [rb11, runBlock_reg _ _ _ (25 : Fin 32) s10.zero (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = ns10 := by
    rw [rb11, runBlock_reg _ _ _ (26 : Fin 32) s10.zero (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = np := by
    rw [rb11, runBlock_reg _ _ _ (27 : Fin 32) s10.zero (by decide), g10_27]
  have g11_12 : reg n11 a2 = (aluEval .sll ((M0 ((pg) + 0x2)).zeroExtend 32) (BitVec.ofNat 32 0x10)) ||| (aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18)) := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, svCg016f2, upd, ↓reduceIte]; rw [g10_12, g10_13] <;> rfl
  have keep_kk11 : SvKeepL B n0.mem n11.mem [] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_8 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m11]; exact w10_8
  have w11_c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m11]; exact w10_c
  have w11_10 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m11]; exact w10_10
  have w11_18 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m11]; exact w10_18
  have w11_24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m11]; exact w10_24
  have w11_28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m11]; exact w10_28
  have w11_2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m11]; exact w10_2c
  have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m11]; exact w10_30
  have w11_34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m11]; exact w10_34
  have w11_38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m11]; exact w10_38
  have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m11]; exact w10_44
  have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m11]; exact w10_48
  have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m11]; exact w10_50
  have b11_14 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m11]; exact b10_14
  have q11_1fc : ∀ j, j < 63 → n11.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m11]; exact q10_1fc j hj
  clear q10_1fc b10_14 w10_50 w10_48 w10_44 w10_38 w10_34 w10_30 w10_2c w10_28 w10_24 w10_18 w10_10 w10_c w10_8 g10_11 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_14 g10_13 g10_12 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  -- 0x16F4
  obtain ⟨n12, c12, u12⟩ := s11.block svCg016f4 E11.self svCg016f4_end
    ⟨trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem SV n12 0x16F6 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock svCg016f4 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
  have g12_8 : reg n12 (8 : Fin 32) = nl := by
    rw [rb12, runBlock_reg _ _ _ (8 : Fin 32) s11.zero (by decide), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = ns1 := by
    rw [rb12, runBlock_reg _ _ _ (9 : Fin 32) s11.zero (by decide), g11_9]
  have g12_10 : reg n12 a0 = pg := by
    rw [rb12, runBlock_reg _ _ _ a0 s11.zero (by decide), g11_10]
  have g12_12 : reg n12 a2 = (aluEval .sll ((M0 ((pg) + 0x2)).zeroExtend 32) (BitVec.ofNat 32 0x10)) ||| (aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18)) := by
    rw [rb12, runBlock_reg _ _ _ a2 s11.zero (by decide), g11_12]
  have g12_13 : reg n12 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by
    rw [rb12, runBlock_reg _ _ _ a3 s11.zero (by decide), g11_13]
  have g12_14 : reg n12 a4 = (M0 (pg)).zeroExtend 32 := by
    rw [rb12, runBlock_reg _ _ _ a4 s11.zero (by decide), g11_14]
  have g12_18 : reg n12 (18 : Fin 32) = out := by
    rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by
    rw [rb12, runBlock_reg _ _ _ (19 : Fin 32) s11.zero (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = x20 := by
    rw [rb12, runBlock_reg _ _ _ (20 : Fin 32) s11.zero (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = gi := by
    rw [rb12, runBlock_reg _ _ _ (21 : Fin 32) s11.zero (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by
    rw [rb12, runBlock_reg _ _ _ (22 : Fin 32) s11.zero (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = x23 := by
    rw [rb12, runBlock_reg _ _ _ (23 : Fin 32) s11.zero (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = ni := by
    rw [rb12, runBlock_reg _ _ _ (24 : Fin 32) s11.zero (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by
    rw [rb12, runBlock_reg _ _ _ (25 : Fin 32) s11.zero (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = ns10 := by
    rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = np := by
    rw [rb12, runBlock_reg _ _ _ (27 : Fin 32) s11.zero (by decide), g11_27]
  have g12_11 : reg n12 a1 = ((aluEval .sll ((M0 ((pg) + 0x1)).zeroExtend 32) (BitVec.ofNat 32 0x8)) ||| ((M0 (pg)).zeroExtend 32)) ||| ((aluEval .sll ((M0 ((pg) + 0x2)).zeroExtend 32) (BitVec.ofNat 32 0x10)) ||| (aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18))) := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svCg016f4, upd, ↓reduceIte]; rw [g11_11, g11_12] <;> rfl
  have keep_kk12 : SvKeepL B n0.mem n12.mem [] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_8 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m12]; exact w11_8
  have w12_c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m12]; exact w11_c
  have w12_10 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m12]; exact w11_10
  have w12_18 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m12]; exact w11_18
  have w12_24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m12]; exact w11_24
  have w12_28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m12]; exact w11_28
  have w12_2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m12]; exact w11_2c
  have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m12]; exact w11_30
  have w12_34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m12]; exact w11_34
  have w12_38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m12]; exact w11_38
  have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m12]; exact w11_44
  have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m12]; exact w11_48
  have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m12]; exact w11_50
  have b12_14 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m12]; exact b11_14
  have q12_1fc : ∀ j, j < 63 → n12.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m12]; exact q11_1fc j hj
  clear q11_1fc b11_14 w11_50 w11_48 w11_44 w11_38 w11_34 w11_30 w11_2c w11_28 w11_24 w11_18 w11_10 w11_c w11_8 g11_12 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_14 g11_13 g11_11 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 rb11 s11 m11 u11 c11
  have pk12 : ((aluEval .sll ((M0 ((pg) + 0x1)).zeroExtend 32) (BitVec.ofNat 32 0x8)) ||| ((M0 (pg)).zeroExtend 32)) ||| ((aluEval .sll ((M0 ((pg) + 0x2)).zeroExtend 32) (BitVec.ofNat 32 0x10)) ||| (aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18))) = memLoad32 M0 pg := pack4 _ _ _ _
  rw [pk12] at g12_11
  -- 0x16F6
  obtain ⟨n13, c13, u13⟩ := s12.block svCg016f6 E12.self svCg016f6_end
    ⟨trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem SV n13 0x16FA (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock svCg016f6 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
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
  have g13_8 : reg n13 (8 : Fin 32) = nl := by
    rw [rb13, runBlock_reg _ _ _ (8 : Fin 32) s12.zero (by decide), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = ns1 := by
    rw [rb13, runBlock_reg _ _ _ (9 : Fin 32) s12.zero (by decide), g12_9]
  have g13_10 : reg n13 a0 = pg := by
    rw [rb13, runBlock_reg _ _ _ a0 s12.zero (by decide), g12_10]
  have g13_11 : reg n13 a1 = memLoad32 M0 pg := by
    rw [rb13, runBlock_reg _ _ _ a1 s12.zero (by decide), g12_11]
  have g13_13 : reg n13 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by
    rw [rb13, runBlock_reg _ _ _ a3 s12.zero (by decide), g12_13]
  have g13_14 : reg n13 a4 = (M0 (pg)).zeroExtend 32 := by
    rw [rb13, runBlock_reg _ _ _ a4 s12.zero (by decide), g12_14]
  have g13_18 : reg n13 (18 : Fin 32) = out := by
    rw [rb13, runBlock_reg _ _ _ (18 : Fin 32) s12.zero (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by
    rw [rb13, runBlock_reg _ _ _ (19 : Fin 32) s12.zero (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = x20 := by
    rw [rb13, runBlock_reg _ _ _ (20 : Fin 32) s12.zero (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = gi := by
    rw [rb13, runBlock_reg _ _ _ (21 : Fin 32) s12.zero (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by
    rw [rb13, runBlock_reg _ _ _ (22 : Fin 32) s12.zero (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = x23 := by
    rw [rb13, runBlock_reg _ _ _ (23 : Fin 32) s12.zero (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = ni := by
    rw [rb13, runBlock_reg _ _ _ (24 : Fin 32) s12.zero (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by
    rw [rb13, runBlock_reg _ _ _ (25 : Fin 32) s12.zero (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = ns10 := by
    rw [rb13, runBlock_reg _ _ _ (26 : Fin 32) s12.zero (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = np := by
    rw [rb13, runBlock_reg _ _ _ (27 : Fin 32) s12.zero (by decide), g12_27]
  have g13_12 : reg n13 a2 = (pg) + BitVec.ofNat 32 0x4 := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svCg016f6, upd, ↓reduceIte]; rw [g12_10] <;> rfl
  have keep_kk13 : SvKeepL B n0.mem n13.mem [] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_8 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m13]; exact w12_8
  have w13_c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m13]; exact w12_c
  have w13_10 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m13]; exact w12_10
  have w13_18 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m13]; exact w12_18
  have w13_24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m13]; exact w12_24
  have w13_28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m13]; exact w12_28
  have w13_2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m13]; exact w12_2c
  have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m13]; exact w12_30
  have w13_34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m13]; exact w12_34
  have w13_38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m13]; exact w12_38
  have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m13]; exact w12_44
  have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m13]; exact w12_48
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m13]; exact w12_50
  have b13_14 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m13]; exact b12_14
  have q13_1fc : ∀ j, j < 63 → n13.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m13]; exact q12_1fc j hj
  clear q12_1fc b12_14 w12_50 w12_48 w12_44 w12_38 w12_34 w12_30 w12_2c w12_28 w12_24 w12_18 w12_10 w12_c w12_8 g12_11 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_14 g12_13 g12_12 g12_10 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
  -- 0x16FA: sw
  obtain ⟨n14, d14, s14, fr14, K14, W14, rg14⟩ := sv_sw F E13 s13 sv_at_16fa (off' := 0x16FC) (c := 0x4)
    (by decide) (by rw [g13_2]; sv_addr) (by decide) (by decide)
  have t14 : Steps n0 n14 := t13.trans d14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keep K14 (by decide)
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [rg14 sp, g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg14 (3 : Fin 32), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg14 (4 : Fin 32), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = nl := by rw [rg14 (8 : Fin 32), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = ns1 := by rw [rg14 (9 : Fin 32), g13_9]
  have g14_10 : reg n14 a0 = pg := by rw [rg14 a0, g13_10]
  have g14_11 : reg n14 a1 = memLoad32 M0 pg := by rw [rg14 a1, g13_11]
  have g14_12 : reg n14 a2 = (pg) + BitVec.ofNat 32 0x4 := by rw [rg14 a2, g13_12]
  have g14_13 : reg n14 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by rw [rg14 a3, g13_13]
  have g14_14 : reg n14 a4 = (M0 (pg)).zeroExtend 32 := by rw [rg14 a4, g13_14]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [rg14 (18 : Fin 32), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [rg14 (19 : Fin 32), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = x20 := by rw [rg14 (20 : Fin 32), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = gi := by rw [rg14 (21 : Fin 32), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = x22 := by rw [rg14 (22 : Fin 32), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = x23 := by rw [rg14 (23 : Fin 32), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = ni := by rw [rg14 (24 : Fin 32), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [rg14 (25 : Fin 32), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = ns10 := by rw [rg14 (26 : Fin 32), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = np := by rw [rg14 (27 : Fin 32), g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [(0x4, 0x4)] := keep_kk13.trans K14.toL
  clear keep_kk13
  have w14_8 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K14.w32 (by decide) (by decide)).trans w13_8
  have w14_c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K14.w32 (by decide) (by decide)).trans w13_c
  have w14_10 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K14.w32 (by decide) (by decide)).trans w13_10
  have w14_18 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := (K14.w32 (by decide) (by decide)).trans w13_18
  have w14_24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := (K14.w32 (by decide) (by decide)).trans w13_24
  have w14_28 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K14.w32 (by decide) (by decide)).trans w13_28
  have w14_2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K14.w32 (by decide) (by decide)).trans w13_2c
  have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := (K14.w32 (by decide) (by decide)).trans w13_30
  have w14_34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K14.w32 (by decide) (by decide)).trans w13_34
  have w14_38 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K14.w32 (by decide) (by decide)).trans w13_38
  have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K14.w32 (by decide) (by decide)).trans w13_44
  have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K14.w32 (by decide) (by decide)).trans w13_48
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K14.w32 (by decide) (by decide)).trans w13_50
  have b14_14 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := (K14.b8 (by decide) (by decide)).trans b13_14
  have w14_4 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [W14, g13_12]
  have q14_1fc : ∀ j, j < 63 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => (K14.range (by decide) (by decide) j hj).trans (q13_1fc j hj)
  clear q13_1fc b13_14 w13_50 w13_48 w13_44 w13_38 w13_34 w13_30 w13_2c w13_28 w13_24 w13_18 w13_10 w13_c w13_8 g13_12 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_14 g13_13 g13_11 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13 pk12
  -- 0x16FC: sw
  obtain ⟨n15, d15, s15, fr15, K15, W15, rg15⟩ := sv_sw F E14 s14 sv_at_16fc (off' := 0x1700) (c := 0x400)
    (by decide) (by rw [g14_2]; sv_addr) (by decide) (by decide)
  have t15 : Steps n0 n15 := t14.trans d15
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.keep K15 (by decide)
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [rg15 sp, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg15 (3 : Fin 32), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg15 (4 : Fin 32), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = nl := by rw [rg15 (8 : Fin 32), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = ns1 := by rw [rg15 (9 : Fin 32), g14_9]
  have g15_10 : reg n15 a0 = pg := by rw [rg15 a0, g14_10]
  have g15_11 : reg n15 a1 = memLoad32 M0 pg := by rw [rg15 a1, g14_11]
  have g15_12 : reg n15 a2 = (pg) + BitVec.ofNat 32 0x4 := by rw [rg15 a2, g14_12]
  have g15_13 : reg n15 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by rw [rg15 a3, g14_13]
  have g15_14 : reg n15 a4 = (M0 (pg)).zeroExtend 32 := by rw [rg15 a4, g14_14]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [rg15 (18 : Fin 32), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [rg15 (19 : Fin 32), g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [rg15 (20 : Fin 32), g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = gi := by rw [rg15 (21 : Fin 32), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [rg15 (22 : Fin 32), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [rg15 (23 : Fin 32), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = ni := by rw [rg15 (24 : Fin 32), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [rg15 (25 : Fin 32), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = ns10 := by rw [rg15 (26 : Fin 32), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = np := by rw [rg15 (27 : Fin 32), g14_27]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [(0x4, 0x4), (0x400, 0x4)] := keep_kk14.trans K15.toL
  clear keep_kk14
  have w15_4 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := (K15.w32 (by decide) (by decide)).trans w14_4
  have w15_8 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K15.w32 (by decide) (by decide)).trans w14_8
  have w15_c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K15.w32 (by decide) (by decide)).trans w14_c
  have w15_10 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K15.w32 (by decide) (by decide)).trans w14_10
  have w15_18 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := (K15.w32 (by decide) (by decide)).trans w14_18
  have w15_24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := (K15.w32 (by decide) (by decide)).trans w14_24
  have w15_28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K15.w32 (by decide) (by decide)).trans w14_28
  have w15_2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K15.w32 (by decide) (by decide)).trans w14_2c
  have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := (K15.w32 (by decide) (by decide)).trans w14_30
  have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K15.w32 (by decide) (by decide)).trans w14_34
  have w15_38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K15.w32 (by decide) (by decide)).trans w14_38
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K15.w32 (by decide) (by decide)).trans w14_44
  have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K15.w32 (by decide) (by decide)).trans w14_48
  have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K15.w32 (by decide) (by decide)).trans w14_50
  have b15_14 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := (K15.b8 (by decide) (by decide)).trans b14_14
  have w15_400 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [W15, g14_11]
  have q15_1fc : ∀ j, j < 63 → n15.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => (K15.range (by decide) (by decide) j hj).trans (q14_1fc j hj)
  clear q14_1fc w14_4 b14_14 w14_50 w14_48 w14_44 w14_38 w14_34 w14_30 w14_2c w14_28 w14_24 w14_18 w14_10 w14_c w14_8 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_14 g14_13 g14_12 g14_11 g14_10 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 rg14 W14 K14 fr14 s14 d14
  -- 0x1700
  obtain ⟨n16, c16, u16⟩ := s15.block svCg01700 E15.self svCg01700_end
    ⟨trivial, trivial⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have s16 : St n16.mem SV n16 0x1702 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have rb16 : ∀ q, reg n16 q = (runBlock svCg01700 (n15.mem, reg n15)).2 q := fun q => by rw [u16.regs]
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans c16
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by
    rw [rb16, runBlock_reg _ _ _ sp s15.zero (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb16, runBlock_reg _ _ _ (3 : Fin 32) s15.zero (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb16, runBlock_reg _ _ _ (4 : Fin 32) s15.zero (by decide), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = nl := by
    rw [rb16, runBlock_reg _ _ _ (8 : Fin 32) s15.zero (by decide), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = ns1 := by
    rw [rb16, runBlock_reg _ _ _ (9 : Fin 32) s15.zero (by decide), g15_9]
  have g16_10 : reg n16 a0 = pg := by
    rw [rb16, runBlock_reg _ _ _ a0 s15.zero (by decide), g15_10]
  have g16_11 : reg n16 a1 = memLoad32 M0 pg := by
    rw [rb16, runBlock_reg _ _ _ a1 s15.zero (by decide), g15_11]
  have g16_12 : reg n16 a2 = (pg) + BitVec.ofNat 32 0x4 := by
    rw [rb16, runBlock_reg _ _ _ a2 s15.zero (by decide), g15_12]
  have g16_13 : reg n16 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by
    rw [rb16, runBlock_reg _ _ _ a3 s15.zero (by decide), g15_13]
  have g16_14 : reg n16 a4 = (M0 (pg)).zeroExtend 32 := by
    rw [rb16, runBlock_reg _ _ _ a4 s15.zero (by decide), g15_14]
  have g16_18 : reg n16 (18 : Fin 32) = out := by
    rw [rb16, runBlock_reg _ _ _ (18 : Fin 32) s15.zero (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by
    rw [rb16, runBlock_reg _ _ _ (19 : Fin 32) s15.zero (by decide), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = x20 := by
    rw [rb16, runBlock_reg _ _ _ (20 : Fin 32) s15.zero (by decide), g15_20]
  have g16_22 : reg n16 (22 : Fin 32) = x22 := by
    rw [rb16, runBlock_reg _ _ _ (22 : Fin 32) s15.zero (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = x23 := by
    rw [rb16, runBlock_reg _ _ _ (23 : Fin 32) s15.zero (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = ni := by
    rw [rb16, runBlock_reg _ _ _ (24 : Fin 32) s15.zero (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = x25 := by
    rw [rb16, runBlock_reg _ _ _ (25 : Fin 32) s15.zero (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = ns10 := by
    rw [rb16, runBlock_reg _ _ _ (26 : Fin 32) s15.zero (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = np := by
    rw [rb16, runBlock_reg _ _ _ (27 : Fin 32) s15.zero (by decide), g15_27]
  have g16_21 : reg n16 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, svCg01700, upd, ↓reduceIte]; rw [g15_21] <;> rfl
  have keep_kk16 : SvKeepL B n0.mem n16.mem [(0x4, 0x4), (0x400, 0x4)] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_4 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m16]; exact w15_4
  have w16_8 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m16]; exact w15_8
  have w16_c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m16]; exact w15_c
  have w16_10 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m16]; exact w15_10
  have w16_18 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m16]; exact w15_18
  have w16_24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m16]; exact w15_24
  have w16_28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m16]; exact w15_28
  have w16_2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m16]; exact w15_2c
  have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m16]; exact w15_30
  have w16_34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m16]; exact w15_34
  have w16_38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m16]; exact w15_38
  have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m16]; exact w15_44
  have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m16]; exact w15_48
  have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m16]; exact w15_50
  have w16_400 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m16]; exact w15_400
  have b16_14 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m16]; exact b15_14
  have q16_1fc : ∀ j, j < 63 → n16.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m16]; exact q15_1fc j hj
  clear q15_1fc w15_400 b15_14 w15_50 w15_48 w15_44 w15_38 w15_34 w15_30 w15_2c w15_28 w15_24 w15_18 w15_10 w15_c w15_8 w15_4 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_14 g15_13 g15_12 g15_11 g15_10 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 rg15 W15 K15 fr15 s15 d15
  -- 0x1702
  obtain ⟨n17, c17, u17⟩ := s16.block svCg01702 E16.self svCg01702_end
    ⟨trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem SV n17 0x1704 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock svCg01702 (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
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
  have g17_8 : reg n17 (8 : Fin 32) = nl := by
    rw [rb17, runBlock_reg _ _ _ (8 : Fin 32) s16.zero (by decide), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = ns1 := by
    rw [rb17, runBlock_reg _ _ _ (9 : Fin 32) s16.zero (by decide), g16_9]
  have g17_10 : reg n17 a0 = pg := by
    rw [rb17, runBlock_reg _ _ _ a0 s16.zero (by decide), g16_10]
  have g17_12 : reg n17 a2 = (pg) + BitVec.ofNat 32 0x4 := by
    rw [rb17, runBlock_reg _ _ _ a2 s16.zero (by decide), g16_12]
  have g17_13 : reg n17 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by
    rw [rb17, runBlock_reg _ _ _ a3 s16.zero (by decide), g16_13]
  have g17_14 : reg n17 a4 = (M0 (pg)).zeroExtend 32 := by
    rw [rb17, runBlock_reg _ _ _ a4 s16.zero (by decide), g16_14]
  have g17_18 : reg n17 (18 : Fin 32) = out := by
    rw [rb17, runBlock_reg _ _ _ (18 : Fin 32) s16.zero (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by
    rw [rb17, runBlock_reg _ _ _ (19 : Fin 32) s16.zero (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = x20 := by
    rw [rb17, runBlock_reg _ _ _ (20 : Fin 32) s16.zero (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by
    rw [rb17, runBlock_reg _ _ _ (21 : Fin 32) s16.zero (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = x22 := by
    rw [rb17, runBlock_reg _ _ _ (22 : Fin 32) s16.zero (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = x23 := by
    rw [rb17, runBlock_reg _ _ _ (23 : Fin 32) s16.zero (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = ni := by
    rw [rb17, runBlock_reg _ _ _ (24 : Fin 32) s16.zero (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = x25 := by
    rw [rb17, runBlock_reg _ _ _ (25 : Fin 32) s16.zero (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = ns10 := by
    rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = np := by
    rw [rb17, runBlock_reg _ _ _ (27 : Fin 32) s16.zero (by decide), g16_27]
  have g17_11 : reg n17 a1 = BitVec.ofNat 32 0x4 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svCg01702, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_10, g16_11, g16_12, g16_13, g16_14, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk17 : SvKeepL B n0.mem n17.mem [(0x4, 0x4), (0x400, 0x4)] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_4 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m17]; exact w16_4
  have w17_8 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m17]; exact w16_8
  have w17_c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m17]; exact w16_c
  have w17_10 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m17]; exact w16_10
  have w17_18 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m17]; exact w16_18
  have w17_24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m17]; exact w16_24
  have w17_28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m17]; exact w16_28
  have w17_2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m17]; exact w16_2c
  have w17_30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m17]; exact w16_30
  have w17_34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m17]; exact w16_34
  have w17_38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m17]; exact w16_38
  have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m17]; exact w16_44
  have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m17]; exact w16_48
  have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m17]; exact w16_50
  have w17_400 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m17]; exact w16_400
  have b17_14 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m17]; exact b16_14
  have q17_1fc : ∀ j, j < 63 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m17]; exact q16_1fc j hj
  clear q16_1fc b16_14 w16_400 w16_50 w16_48 w16_44 w16_38 w16_34 w16_30 w16_2c w16_28 w16_24 w16_18 w16_10 w16_c w16_8 w16_4 g16_21 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_20 g16_19 g16_18 g16_14 g16_13 g16_12 g16_11 g16_10 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 rb16 s16 m16 u16 c16
  -- 0x1704: branch, not taken
  obtain ⟨n18, d18, u18⟩ := s17.notTaken E17.self 0x1706 sv_at_1704
    (by decide) (by rw [g17_11, s17.zero]; decide)
  have s18 : St n18.mem SV n18 0x1706 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans (.single d18)
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = nl := by rw [u18.regs, g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = ns1 := by rw [u18.regs, g17_9]
  have g18_10 : reg n18 a0 = pg := by rw [u18.regs, g17_10]
  have g18_11 : reg n18 a1 = BitVec.ofNat 32 0x4 := by rw [u18.regs, g17_11]
  have g18_12 : reg n18 a2 = (pg) + BitVec.ofNat 32 0x4 := by rw [u18.regs, g17_12]
  have g18_13 : reg n18 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by rw [u18.regs, g17_13]
  have g18_14 : reg n18 a4 = (M0 (pg)).zeroExtend 32 := by rw [u18.regs, g17_14]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [u18.regs, g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [u18.regs, g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [u18.regs, g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = x23 := by rw [u18.regs, g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = ni := by rw [u18.regs, g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [u18.regs, g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = ns10 := by rw [u18.regs, g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = np := by rw [u18.regs, g17_27]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [(0x4, 0x4), (0x400, 0x4)] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_4 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m18]; exact w17_4
  have w18_8 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m18]; exact w17_8
  have w18_c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m18]; exact w17_c
  have w18_10 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m18]; exact w17_10
  have w18_18 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m18]; exact w17_18
  have w18_24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m18]; exact w17_24
  have w18_28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m18]; exact w17_28
  have w18_2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m18]; exact w17_2c
  have w18_30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m18]; exact w17_30
  have w18_34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m18]; exact w17_34
  have w18_38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m18]; exact w17_38
  have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m18]; exact w17_44
  have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m18]; exact w17_48
  have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m18]; exact w17_50
  have w18_400 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m18]; exact w17_400
  have b18_14 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m18]; exact b17_14
  have q18_1fc : ∀ j, j < 63 → n18.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m18]; exact q17_1fc j hj
  clear q17_1fc b17_14 w17_400 w17_50 w17_48 w17_44 w17_38 w17_34 w17_30 w17_2c w17_28 w17_24 w17_18 w17_10 w17_c w17_8 w17_4 g17_11 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_14 g17_13 g17_12 g17_10 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
  -- 0x1706: lbu from the bundle
  obtain ⟨n19, d19, u19⟩ := s18.lbu E18.self sv_at_1706 (off' := 0x170A) (by decide)
  have s19 : St n19.mem SV n19 0x170A (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans (.single d19)
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = nl := by rw [u19.regs, upd_ne (by decide) (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = ns1 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_9]
  have g19_10 : reg n19 a0 = pg := by rw [u19.regs, upd_ne (by decide) (by decide), g18_10]
  have g19_11 : reg n19 a1 = BitVec.ofNat 32 0x4 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_11]
  have g19_13 : reg n19 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_13]
  have g19_14 : reg n19 a4 = (M0 (pg)).zeroExtend 32 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_14]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = x20 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = ni := by rw [u19.regs, upd_ne (by decide) (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = ns10 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = np := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
  have g19_12 : reg n19 a2 = (M0 (pg)).zeroExtend 32 := by
    rw [u19.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g18_10, show (pg) + 0x0 = pg from BitVec.add_zero _, fR18 _ (pc0.r0 (by decide))]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x4, 0x4), (0x400, 0x4)] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_4 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m19]; exact w18_4
  have w19_8 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m19]; exact w18_8
  have w19_c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m19]; exact w18_c
  have w19_10 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m19]; exact w18_10
  have w19_18 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m19]; exact w18_18
  have w19_24 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m19]; exact w18_24
  have w19_28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m19]; exact w18_28
  have w19_2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m19]; exact w18_2c
  have w19_30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m19]; exact w18_30
  have w19_34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m19]; exact w18_34
  have w19_38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m19]; exact w18_38
  have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m19]; exact w18_44
  have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m19]; exact w18_48
  have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m19]; exact w18_50
  have w19_400 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m19]; exact w18_400
  have b19_14 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m19]; exact b18_14
  have q19_1fc : ∀ j, j < 63 → n19.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m19]; exact q18_1fc j hj
  clear q18_1fc b18_14 w18_400 w18_50 w18_48 w18_44 w18_38 w18_34 w18_30 w18_2c w18_28 w18_24 w18_18 w18_10 w18_c w18_8 w18_4 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_14 g18_13 g18_12 g18_11 g18_10 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
  -- 0x170A
  obtain ⟨n20, c20, u20⟩ := s19.block svCg0170a E19.self svCg0170a_end
    ⟨trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem SV n20 0x170E (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock svCg0170a (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
  have g20_8 : reg n20 (8 : Fin 32) = nl := by
    rw [rb20, runBlock_reg _ _ _ (8 : Fin 32) s19.zero (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = ns1 := by
    rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
  have g20_10 : reg n20 a0 = pg := by
    rw [rb20, runBlock_reg _ _ _ a0 s19.zero (by decide), g19_10]
  have g20_11 : reg n20 a1 = BitVec.ofNat 32 0x4 := by
    rw [rb20, runBlock_reg _ _ _ a1 s19.zero (by decide), g19_11]
  have g20_13 : reg n20 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by
    rw [rb20, runBlock_reg _ _ _ a3 s19.zero (by decide), g19_13]
  have g20_14 : reg n20 a4 = (M0 (pg)).zeroExtend 32 := by
    rw [rb20, runBlock_reg _ _ _ a4 s19.zero (by decide), g19_14]
  have g20_18 : reg n20 (18 : Fin 32) = out := by
    rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by
    rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = x20 := by
    rw [rb20, runBlock_reg _ _ _ (20 : Fin 32) s19.zero (by decide), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by
    rw [rb20, runBlock_reg _ _ _ (21 : Fin 32) s19.zero (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = x22 := by
    rw [rb20, runBlock_reg _ _ _ (22 : Fin 32) s19.zero (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = x23 := by
    rw [rb20, runBlock_reg _ _ _ (23 : Fin 32) s19.zero (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = ni := by
    rw [rb20, runBlock_reg _ _ _ (24 : Fin 32) s19.zero (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = x25 := by
    rw [rb20, runBlock_reg _ _ _ (25 : Fin 32) s19.zero (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = ns10 := by
    rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = np := by
    rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
  have g20_12 : reg n20 a2 = (M0 (pg)).zeroExtend 32 + 0xFFFFFFC3 := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svCg0170a, upd, ↓reduceIte]; rw [g19_12]; rfl
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x4, 0x4), (0x400, 0x4)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_4 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m20]; exact w19_4
  have w20_8 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m20]; exact w19_8
  have w20_c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m20]; exact w19_c
  have w20_10 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m20]; exact w19_10
  have w20_18 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m20]; exact w19_18
  have w20_24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m20]; exact w19_24
  have w20_28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m20]; exact w19_28
  have w20_2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m20]; exact w19_2c
  have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m20]; exact w19_30
  have w20_34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m20]; exact w19_34
  have w20_38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m20]; exact w19_38
  have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m20]; exact w19_44
  have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m20]; exact w19_48
  have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m20]; exact w19_50
  have w20_400 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m20]; exact w19_400
  have b20_14 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m20]; exact b19_14
  have q20_1fc : ∀ j, j < 63 → n20.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m20]; exact q19_1fc j hj
  clear q19_1fc b19_14 w19_400 w19_50 w19_48 w19_44 w19_38 w19_34 w19_30 w19_2c w19_28 w19_24 w19_18 w19_10 w19_c w19_8 w19_4 g19_12 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_14 g19_13 g19_11 g19_10 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
  -- 0x170E
  obtain ⟨n21, c21, u21⟩ := s20.block svCg0170e E20.self svCg0170e_end
    ⟨trivial, trivial⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have s21 : St n21.mem SV n21 0x1710 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have rb21 : ∀ q, reg n21 q = (runBlock svCg0170e (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
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
  have g21_8 : reg n21 (8 : Fin 32) = nl := by
    rw [rb21, runBlock_reg _ _ _ (8 : Fin 32) s20.zero (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = ns1 := by
    rw [rb21, runBlock_reg _ _ _ (9 : Fin 32) s20.zero (by decide), g20_9]
  have g21_11 : reg n21 a1 = BitVec.ofNat 32 0x4 := by
    rw [rb21, runBlock_reg _ _ _ a1 s20.zero (by decide), g20_11]
  have g21_12 : reg n21 a2 = (M0 (pg)).zeroExtend 32 + 0xFFFFFFC3 := by
    rw [rb21, runBlock_reg _ _ _ a2 s20.zero (by decide), g20_12]
  have g21_13 : reg n21 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by
    rw [rb21, runBlock_reg _ _ _ a3 s20.zero (by decide), g20_13]
  have g21_14 : reg n21 a4 = (M0 (pg)).zeroExtend 32 := by
    rw [rb21, runBlock_reg _ _ _ a4 s20.zero (by decide), g20_14]
  have g21_18 : reg n21 (18 : Fin 32) = out := by
    rw [rb21, runBlock_reg _ _ _ (18 : Fin 32) s20.zero (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by
    rw [rb21, runBlock_reg _ _ _ (19 : Fin 32) s20.zero (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = x20 := by
    rw [rb21, runBlock_reg _ _ _ (20 : Fin 32) s20.zero (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by
    rw [rb21, runBlock_reg _ _ _ (21 : Fin 32) s20.zero (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = x22 := by
    rw [rb21, runBlock_reg _ _ _ (22 : Fin 32) s20.zero (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = x23 := by
    rw [rb21, runBlock_reg _ _ _ (23 : Fin 32) s20.zero (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = ni := by
    rw [rb21, runBlock_reg _ _ _ (24 : Fin 32) s20.zero (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = x25 := by
    rw [rb21, runBlock_reg _ _ _ (25 : Fin 32) s20.zero (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = ns10 := by
    rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = np := by
    rw [rb21, runBlock_reg _ _ _ (27 : Fin 32) s20.zero (by decide), g20_27]
  have g21_10 : reg n21 a0 = (pg) + BitVec.ofNat 32 0x1 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svCg0170e, upd, ↓reduceIte]; rw [g20_10] <;> rfl
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x4, 0x4), (0x400, 0x4)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_4 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m21]; exact w20_4
  have w21_8 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m21]; exact w20_8
  have w21_c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m21]; exact w20_c
  have w21_10 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m21]; exact w20_10
  have w21_18 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m21]; exact w20_18
  have w21_24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m21]; exact w20_24
  have w21_28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m21]; exact w20_28
  have w21_2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m21]; exact w20_2c
  have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m21]; exact w20_30
  have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m21]; exact w20_34
  have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m21]; exact w20_38
  have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m21]; exact w20_44
  have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m21]; exact w20_48
  have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m21]; exact w20_50
  have w21_400 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m21]; exact w20_400
  have b21_14 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m21]; exact b20_14
  have q21_1fc : ∀ j, j < 63 → n21.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m21]; exact q20_1fc j hj
  clear q20_1fc b20_14 w20_400 w20_50 w20_48 w20_44 w20_38 w20_34 w20_30 w20_2c w20_28 w20_24 w20_18 w20_10 w20_c w20_8 w20_4 g20_12 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_14 g20_13 g20_11 g20_10 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  -- 0x1710
  obtain ⟨n22, c22, u22⟩ := s21.block svCg01710 E21.self svCg01710_end
    ⟨trivial, trivial⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have s22 : St n22.mem SV n22 0x1712 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have rb22 : ∀ q, reg n22 q = (runBlock svCg01710 (n21.mem, reg n21)).2 q := fun q => by rw [u22.regs]
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
  have g22_8 : reg n22 (8 : Fin 32) = nl := by
    rw [rb22, runBlock_reg _ _ _ (8 : Fin 32) s21.zero (by decide), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = ns1 := by
    rw [rb22, runBlock_reg _ _ _ (9 : Fin 32) s21.zero (by decide), g21_9]
  have g22_10 : reg n22 a0 = (pg) + BitVec.ofNat 32 0x1 := by
    rw [rb22, runBlock_reg _ _ _ a0 s21.zero (by decide), g21_10]
  have g22_12 : reg n22 a2 = (M0 (pg)).zeroExtend 32 + 0xFFFFFFC3 := by
    rw [rb22, runBlock_reg _ _ _ a2 s21.zero (by decide), g21_12]
  have g22_13 : reg n22 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by
    rw [rb22, runBlock_reg _ _ _ a3 s21.zero (by decide), g21_13]
  have g22_14 : reg n22 a4 = (M0 (pg)).zeroExtend 32 := by
    rw [rb22, runBlock_reg _ _ _ a4 s21.zero (by decide), g21_14]
  have g22_18 : reg n22 (18 : Fin 32) = out := by
    rw [rb22, runBlock_reg _ _ _ (18 : Fin 32) s21.zero (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by
    rw [rb22, runBlock_reg _ _ _ (19 : Fin 32) s21.zero (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = x20 := by
    rw [rb22, runBlock_reg _ _ _ (20 : Fin 32) s21.zero (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by
    rw [rb22, runBlock_reg _ _ _ (21 : Fin 32) s21.zero (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = x22 := by
    rw [rb22, runBlock_reg _ _ _ (22 : Fin 32) s21.zero (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = x23 := by
    rw [rb22, runBlock_reg _ _ _ (23 : Fin 32) s21.zero (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = ni := by
    rw [rb22, runBlock_reg _ _ _ (24 : Fin 32) s21.zero (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = x25 := by
    rw [rb22, runBlock_reg _ _ _ (25 : Fin 32) s21.zero (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = ns10 := by
    rw [rb22, runBlock_reg _ _ _ (26 : Fin 32) s21.zero (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = np := by
    rw [rb22, runBlock_reg _ _ _ (27 : Fin 32) s21.zero (by decide), g21_27]
  have g22_11 : reg n22 a1 = BitVec.ofNat 32 0x3 := by
    rw [rb22]; simp +decide only [runBlock, BInstr.run, svCg01710, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g21_2, g21_3, g21_4, g21_8, g21_9, g21_10, g21_11, g21_12, g21_13, g21_14, g21_18, g21_19, g21_20, g21_21, g21_22, g21_23, g21_24, g21_25, g21_26, g21_27, s21.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x4, 0x4), (0x400, 0x4)] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_4 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m22]; exact w21_4
  have w22_8 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m22]; exact w21_8
  have w22_c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m22]; exact w21_c
  have w22_10 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m22]; exact w21_10
  have w22_18 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m22]; exact w21_18
  have w22_24 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m22]; exact w21_24
  have w22_28 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m22]; exact w21_28
  have w22_2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m22]; exact w21_2c
  have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m22]; exact w21_30
  have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m22]; exact w21_34
  have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m22]; exact w21_38
  have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m22]; exact w21_44
  have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m22]; exact w21_48
  have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m22]; exact w21_50
  have w22_400 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m22]; exact w21_400
  have b22_14 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m22]; exact b21_14
  have q22_1fc : ∀ j, j < 63 → n22.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m22]; exact q21_1fc j hj
  clear q21_1fc b21_14 w21_400 w21_50 w21_48 w21_44 w21_38 w21_34 w21_30 w21_2c w21_28 w21_24 w21_18 w21_10 w21_c w21_8 w21_4 g21_10 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_14 g21_13 g21_12 g21_11 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
  -- 0x1712: branch, not taken
  obtain ⟨n23, d23, u23⟩ := s22.notTaken E22.self 0x1714 sv_at_1712
    (by decide) (by rw [g22_12, s22.zero]; exact br_bne_f ((pad_iff _).mpr hq0))
  have s23 : St n23.mem SV n23 0x1714 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, SvR B x → n23.mem x = M0 x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = nl := by rw [u23.regs, g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = ns1 := by rw [u23.regs, g22_9]
  have g23_10 : reg n23 a0 = (pg) + BitVec.ofNat 32 0x1 := by rw [u23.regs, g22_10]
  have g23_11 : reg n23 a1 = BitVec.ofNat 32 0x3 := by rw [u23.regs, g22_11]
  have g23_12 : reg n23 a2 = (M0 (pg)).zeroExtend 32 + 0xFFFFFFC3 := by rw [u23.regs, g22_12]
  have g23_13 : reg n23 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by rw [u23.regs, g22_13]
  have g23_14 : reg n23 a4 = (M0 (pg)).zeroExtend 32 := by rw [u23.regs, g22_14]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = x20 := by rw [u23.regs, g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [u23.regs, g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = x22 := by rw [u23.regs, g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = x23 := by rw [u23.regs, g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = ni := by rw [u23.regs, g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = x25 := by rw [u23.regs, g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = ns10 := by rw [u23.regs, g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = np := by rw [u23.regs, g22_27]
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x4, 0x4), (0x400, 0x4)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_4 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m23]; exact w22_4
  have w23_8 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m23]; exact w22_8
  have w23_c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m23]; exact w22_c
  have w23_10 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m23]; exact w22_10
  have w23_18 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m23]; exact w22_18
  have w23_24 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m23]; exact w22_24
  have w23_28 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m23]; exact w22_28
  have w23_2c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m23]; exact w22_2c
  have w23_30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m23]; exact w22_30
  have w23_34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m23]; exact w22_34
  have w23_38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m23]; exact w22_38
  have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m23]; exact w22_44
  have w23_48 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m23]; exact w22_48
  have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m23]; exact w22_50
  have w23_400 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m23]; exact w22_400
  have b23_14 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m23]; exact b22_14
  have q23_1fc : ∀ j, j < 63 → n23.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m23]; exact q22_1fc j hj
  clear q22_1fc b22_14 w22_400 w22_50 w22_48 w22_44 w22_38 w22_34 w22_30 w22_2c w22_28 w22_24 w22_18 w22_10 w22_c w22_8 w22_4 g22_11 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_14 g22_13 g22_12 g22_10 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 rb22 s22 m22 u22 c22
  -- 0x1714: lw
  obtain ⟨n24, d24, u24⟩ := s23.lw E23.self sv_at_1714 (off' := 0x1716) (by decide)
    (by rw [g23_2, show B + 0x21A0 + 0xC = B + 0x21A0 + BitVec.ofNat 32 0xC by sv_addr]; exact sv_al F (by decide) (by decide))
  have s24 : St n24.mem SV n24 0x1716 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = nl := by rw [u24.regs, upd_ne (by decide) (by decide), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = ns1 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_9]
  have g24_11 : reg n24 a1 = BitVec.ofNat 32 0x3 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_11]
  have g24_12 : reg n24 a2 = (M0 (pg)).zeroExtend 32 + 0xFFFFFFC3 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_12]
  have g24_13 : reg n24 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_13]
  have g24_14 : reg n24 a4 = (M0 (pg)).zeroExtend 32 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_14]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, upd_ne (by decide) (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = x20 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = x22 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = x23 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = ni := by rw [u24.regs, upd_ne (by decide) (by decide), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = ns10 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = np := by rw [u24.regs, upd_ne (by decide) (by decide), g23_27]
  have g24_10 : reg n24 a0 = wc := by
    rw [u24.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g23_2, show B + 0x21A0 + 0xC = B + 0x21A0 + BitVec.ofNat 32 0xC by sv_addr, w23_c]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x4, 0x4), (0x400, 0x4)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_4 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m24]; exact w23_4
  have w24_8 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m24]; exact w23_8
  have w24_c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m24]; exact w23_c
  have w24_10 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m24]; exact w23_10
  have w24_18 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m24]; exact w23_18
  have w24_24 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m24]; exact w23_24
  have w24_28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m24]; exact w23_28
  have w24_2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m24]; exact w23_2c
  have w24_30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m24]; exact w23_30
  have w24_34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m24]; exact w23_34
  have w24_38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m24]; exact w23_38
  have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m24]; exact w23_44
  have w24_48 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m24]; exact w23_48
  have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m24]; exact w23_50
  have w24_400 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m24]; exact w23_400
  have b24_14 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m24]; exact b23_14
  have q24_1fc : ∀ j, j < 63 → n24.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m24]; exact q23_1fc j hj
  clear q23_1fc b23_14 w23_400 w23_50 w23_48 w23_44 w23_38 w23_34 w23_30 w23_2c w23_28 w23_24 w23_18 w23_10 w23_c w23_8 w23_4 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_14 g23_13 g23_12 g23_11 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
  by_cases hlast : (gi) + BitVec.ofNat 32 0x1 = wc
  rotate_left
  · -- 0x1716: branch, taken
    obtain ⟨n25, d25, u25⟩ := s24.taken E24.self 0x1878 sv_at_1716
      (by decide) (by rw [g24_21, g24_10]; exact br_bne_t hlast)
    have s25 : St n25.mem SV n25 0x1878 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
    have m25 : n25.mem = n24.mem := u25.mem
    have fr25 : ∀ x, SvR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
    have t25 : Steps n0 n25 := t24.trans (.single d25)
    have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
    have E25 : SvCode n25.mem := E24.fr F fr25
    have V25 : SvSaves B n25.mem v := V24.same m25
    have g25_2 : reg n25 sp = B + 0x21A0 := by rw [u25.regs, g24_2]
    have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u25.regs, g24_3]
    have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u25.regs, g24_4]
    have g25_8 : reg n25 (8 : Fin 32) = nl := by rw [u25.regs, g24_8]
    have g25_9 : reg n25 (9 : Fin 32) = ns1 := by rw [u25.regs, g24_9]
    have g25_10 : reg n25 a0 = wc := by rw [u25.regs, g24_10]
    have g25_11 : reg n25 a1 = BitVec.ofNat 32 0x3 := by rw [u25.regs, g24_11]
    have g25_12 : reg n25 a2 = (M0 (pg)).zeroExtend 32 + 0xFFFFFFC3 := by rw [u25.regs, g24_12]
    have g25_13 : reg n25 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by rw [u25.regs, g24_13]
    have g25_14 : reg n25 a4 = (M0 (pg)).zeroExtend 32 := by rw [u25.regs, g24_14]
    have g25_18 : reg n25 (18 : Fin 32) = out := by rw [u25.regs, g24_18]
    have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [u25.regs, g24_19]
    have g25_20 : reg n25 (20 : Fin 32) = x20 := by rw [u25.regs, g24_20]
    have g25_21 : reg n25 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [u25.regs, g24_21]
    have g25_22 : reg n25 (22 : Fin 32) = x22 := by rw [u25.regs, g24_22]
    have g25_23 : reg n25 (23 : Fin 32) = x23 := by rw [u25.regs, g24_23]
    have g25_24 : reg n25 (24 : Fin 32) = ni := by rw [u25.regs, g24_24]
    have g25_25 : reg n25 (25 : Fin 32) = x25 := by rw [u25.regs, g24_25]
    have g25_26 : reg n25 (26 : Fin 32) = ns10 := by rw [u25.regs, g24_26]
    have g25_27 : reg n25 (27 : Fin 32) = np := by rw [u25.regs, g24_27]
    have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x4, 0x4), (0x400, 0x4)] := by rw [m25]; exact keep_kk24
    clear keep_kk24
    have w25_4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m25]; exact w24_4
    have w25_8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m25]; exact w24_8
    have w25_c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m25]; exact w24_c
    have w25_10 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m25]; exact w24_10
    have w25_18 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m25]; exact w24_18
    have w25_24 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m25]; exact w24_24
    have w25_28 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m25]; exact w24_28
    have w25_2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m25]; exact w24_2c
    have w25_30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m25]; exact w24_30
    have w25_34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m25]; exact w24_34
    have w25_38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m25]; exact w24_38
    have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m25]; exact w24_44
    have w25_48 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m25]; exact w24_48
    have w25_50 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m25]; exact w24_50
    have w25_400 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m25]; exact w24_400
    have b25_14 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m25]; exact b24_14
    have q25_1fc : ∀ j, j < 63 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m25]; exact q24_1fc j hj
    clear q24_1fc b24_14 w24_400 w24_50 w24_48 w24_44 w24_38 w24_34 w24_30 w24_2c w24_28 w24_24 w24_18 w24_10 w24_c w24_8 w24_4 g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_14 g24_13 g24_12 g24_11 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
    -- 0x1878
    obtain ⟨n26, c26, u26⟩ := s25.block svCg01878 E25.self svCg01878_end
      ⟨trivial, trivial⟩
    have m26 : n26.mem = n25.mem := u26.mem
    have s26 : St n26.mem SV n26 0x187A (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
    have rb26 : ∀ q, reg n26 q = (runBlock svCg01878 (n25.mem, reg n25)).2 q := fun q => by rw [u26.regs]
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
    have g26_8 : reg n26 (8 : Fin 32) = nl := by
      rw [rb26, runBlock_reg _ _ _ (8 : Fin 32) s25.zero (by decide), g25_8]
    have g26_9 : reg n26 (9 : Fin 32) = ns1 := by
      rw [rb26, runBlock_reg _ _ _ (9 : Fin 32) s25.zero (by decide), g25_9]
    have g26_10 : reg n26 a0 = wc := by
      rw [rb26, runBlock_reg _ _ _ a0 s25.zero (by decide), g25_10]
    have g26_11 : reg n26 a1 = BitVec.ofNat 32 0x3 := by
      rw [rb26, runBlock_reg _ _ _ a1 s25.zero (by decide), g25_11]
    have g26_12 : reg n26 a2 = (M0 (pg)).zeroExtend 32 + 0xFFFFFFC3 := by
      rw [rb26, runBlock_reg _ _ _ a2 s25.zero (by decide), g25_12]
    have g26_13 : reg n26 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by
      rw [rb26, runBlock_reg _ _ _ a3 s25.zero (by decide), g25_13]
    have g26_14 : reg n26 a4 = (M0 (pg)).zeroExtend 32 := by
      rw [rb26, runBlock_reg _ _ _ a4 s25.zero (by decide), g25_14]
    have g26_18 : reg n26 (18 : Fin 32) = out := by
      rw [rb26, runBlock_reg _ _ _ (18 : Fin 32) s25.zero (by decide), g25_18]
    have g26_19 : reg n26 (19 : Fin 32) = bp := by
      rw [rb26, runBlock_reg _ _ _ (19 : Fin 32) s25.zero (by decide), g25_19]
    have g26_20 : reg n26 (20 : Fin 32) = x20 := by
      rw [rb26, runBlock_reg _ _ _ (20 : Fin 32) s25.zero (by decide), g25_20]
    have g26_21 : reg n26 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by
      rw [rb26, runBlock_reg _ _ _ (21 : Fin 32) s25.zero (by decide), g25_21]
    have g26_22 : reg n26 (22 : Fin 32) = x22 := by
      rw [rb26, runBlock_reg _ _ _ (22 : Fin 32) s25.zero (by decide), g25_22]
    have g26_23 : reg n26 (23 : Fin 32) = x23 := by
      rw [rb26, runBlock_reg _ _ _ (23 : Fin 32) s25.zero (by decide), g25_23]
    have g26_24 : reg n26 (24 : Fin 32) = ni := by
      rw [rb26, runBlock_reg _ _ _ (24 : Fin 32) s25.zero (by decide), g25_24]
    have g26_26 : reg n26 (26 : Fin 32) = ns10 := by
      rw [rb26, runBlock_reg _ _ _ (26 : Fin 32) s25.zero (by decide), g25_26]
    have g26_27 : reg n26 (27 : Fin 32) = np := by
      rw [rb26, runBlock_reg _ _ _ (27 : Fin 32) s25.zero (by decide), g25_27]
    have g26_25 : reg n26 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb26]; simp +decide only [runBlock, BInstr.run, svCg01878, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_10, g25_11, g25_12, g25_13, g25_14, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_25, g25_26, g25_27, s25.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x4, 0x4), (0x400, 0x4)] := by rw [m26]; exact keep_kk25
    clear keep_kk25
    have w26_4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m26]; exact w25_4
    have w26_8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m26]; exact w25_8
    have w26_c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m26]; exact w25_c
    have w26_10 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m26]; exact w25_10
    have w26_18 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m26]; exact w25_18
    have w26_24 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m26]; exact w25_24
    have w26_28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m26]; exact w25_28
    have w26_2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m26]; exact w25_2c
    have w26_30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m26]; exact w25_30
    have w26_34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m26]; exact w25_34
    have w26_38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m26]; exact w25_38
    have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m26]; exact w25_44
    have w26_48 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m26]; exact w25_48
    have w26_50 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m26]; exact w25_50
    have w26_400 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m26]; exact w25_400
    have b26_14 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m26]; exact b25_14
    have q26_1fc : ∀ j, j < 63 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m26]; exact q25_1fc j hj
    clear q25_1fc b25_14 w25_400 w25_50 w25_48 w25_44 w25_38 w25_34 w25_30 w25_2c w25_28 w25_24 w25_18 w25_10 w25_c w25_8 w25_4 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_14 g25_13 g25_12 g25_11 g25_10 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 m25 s25 u25 d25
    -- 0x187A: j
    obtain ⟨n27, d27, u27⟩ := s26.jump E26.self sv_at_187a (off' := 0x1882) (by decide)
      (by rw [s26.pc]; decide)
    have s27 : St n27.mem SV n27 0x1882 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
    have m27 : n27.mem = n26.mem := u27.mem
    have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
    have t27 : Steps n0 n27 := t26.trans (.single d27)
    have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
    have E27 : SvCode n27.mem := E26.fr F fr27
    have V27 : SvSaves B n27.mem v := V26.same m27
    have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, g26_2]
    have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, g26_3]
    have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, g26_4]
    have g27_8 : reg n27 (8 : Fin 32) = nl := by rw [u27.regs, g26_8]
    have g27_9 : reg n27 (9 : Fin 32) = ns1 := by rw [u27.regs, g26_9]
    have g27_10 : reg n27 a0 = wc := by rw [u27.regs, g26_10]
    have g27_11 : reg n27 a1 = BitVec.ofNat 32 0x3 := by rw [u27.regs, g26_11]
    have g27_12 : reg n27 a2 = (M0 (pg)).zeroExtend 32 + 0xFFFFFFC3 := by rw [u27.regs, g26_12]
    have g27_13 : reg n27 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by rw [u27.regs, g26_13]
    have g27_14 : reg n27 a4 = (M0 (pg)).zeroExtend 32 := by rw [u27.regs, g26_14]
    have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, g26_18]
    have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, g26_19]
    have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [u27.regs, g26_20]
    have g27_21 : reg n27 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [u27.regs, g26_21]
    have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [u27.regs, g26_22]
    have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [u27.regs, g26_23]
    have g27_24 : reg n27 (24 : Fin 32) = ni := by rw [u27.regs, g26_24]
    have g27_25 : reg n27 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u27.regs, g26_25]
    have g27_26 : reg n27 (26 : Fin 32) = ns10 := by rw [u27.regs, g26_26]
    have g27_27 : reg n27 (27 : Fin 32) = np := by rw [u27.regs, g26_27]
    have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x4, 0x4), (0x400, 0x4)] := by rw [m27]; exact keep_kk26
    clear keep_kk26
    have w27_4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m27]; exact w26_4
    have w27_8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m27]; exact w26_8
    have w27_c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m27]; exact w26_c
    have w27_10 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m27]; exact w26_10
    have w27_18 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m27]; exact w26_18
    have w27_24 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m27]; exact w26_24
    have w27_28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m27]; exact w26_28
    have w27_2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m27]; exact w26_2c
    have w27_30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m27]; exact w26_30
    have w27_34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m27]; exact w26_34
    have w27_38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m27]; exact w26_38
    have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m27]; exact w26_44
    have w27_48 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m27]; exact w26_48
    have w27_50 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m27]; exact w26_50
    have w27_400 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m27]; exact w26_400
    have b27_14 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m27]; exact b26_14
    have q27_1fc : ∀ j, j < 63 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m27]; exact q26_1fc j hj
    clear q26_1fc b26_14 w26_400 w26_50 w26_48 w26_44 w26_38 w26_34 w26_30 w26_2c w26_28 w26_24 w26_18 w26_10 w26_c w26_8 w26_4 g26_25 g26_27 g26_26 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_14 g26_13 g26_12 g26_11 g26_10 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 rb26 s26 m26 u26 c26
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hlast h0'), sv_fail_1882 F E27 s27 t27 (fun x hx => (fR27 x hx).trans (fM x hx).symm) V27 hret g27_2 g27_18 hO g27_3 g27_4⟩
  -- 0x1716: branch, not taken
  obtain ⟨n25, d25, u25⟩ := s24.notTaken E24.self 0x171A sv_at_1716
    (by decide) (by rw [g24_21, g24_10]; exact br_bne_f hlast)
  have s25 : St n25.mem SV n25 0x171A (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have fr25 : ∀ x, SvR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
  have t25 : Steps n0 n25 := t24.trans (.single d25)
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.same m25
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [u25.regs, g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u25.regs, g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u25.regs, g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = nl := by rw [u25.regs, g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = ns1 := by rw [u25.regs, g24_9]
  have g25_10 : reg n25 a0 = wc := by rw [u25.regs, g24_10]
  have g25_11 : reg n25 a1 = BitVec.ofNat 32 0x3 := by rw [u25.regs, g24_11]
  have g25_12 : reg n25 a2 = (M0 (pg)).zeroExtend 32 + 0xFFFFFFC3 := by rw [u25.regs, g24_12]
  have g25_13 : reg n25 a3 = aluEval .sll ((M0 ((pg) + 0x3)).zeroExtend 32) (BitVec.ofNat 32 0x18) := by rw [u25.regs, g24_13]
  have g25_14 : reg n25 a4 = (M0 (pg)).zeroExtend 32 := by rw [u25.regs, g24_14]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [u25.regs, g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [u25.regs, g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = x20 := by rw [u25.regs, g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [u25.regs, g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = x22 := by rw [u25.regs, g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = x23 := by rw [u25.regs, g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = ni := by rw [u25.regs, g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = x25 := by rw [u25.regs, g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = ns10 := by rw [u25.regs, g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = np := by rw [u25.regs, g24_27]
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x4, 0x4), (0x400, 0x4)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_4 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m25]; exact w24_4
  have w25_8 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m25]; exact w24_8
  have w25_c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m25]; exact w24_c
  have w25_10 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m25]; exact w24_10
  have w25_18 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m25]; exact w24_18
  have w25_24 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m25]; exact w24_24
  have w25_28 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m25]; exact w24_28
  have w25_2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m25]; exact w24_2c
  have w25_30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m25]; exact w24_30
  have w25_34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m25]; exact w24_34
  have w25_38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m25]; exact w24_38
  have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m25]; exact w24_44
  have w25_48 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m25]; exact w24_48
  have w25_50 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m25]; exact w24_50
  have w25_400 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m25]; exact w24_400
  have b25_14 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m25]; exact b24_14
  have q25_1fc : ∀ j, j < 63 → n25.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m25]; exact q24_1fc j hj
  clear q24_1fc b24_14 w24_400 w24_50 w24_48 w24_44 w24_38 w24_34 w24_30 w24_2c w24_28 w24_24 w24_18 w24_10 w24_c w24_8 w24_4 g24_10 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_14 g24_13 g24_12 g24_11 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
  -- 0x171A
  obtain ⟨n26, c26, u26⟩ := s25.block svCg0171a E25.self svCg0171a_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have s26 : St n26.mem SV n26 0x1728 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have rb26 : ∀ q, reg n26 q = (runBlock svCg0171a (n25.mem, reg n25)).2 q := fun q => by rw [u26.regs]
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
  have g26_8 : reg n26 (8 : Fin 32) = nl := by
    rw [rb26, runBlock_reg _ _ _ (8 : Fin 32) s25.zero (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = ns1 := by
    rw [rb26, runBlock_reg _ _ _ (9 : Fin 32) s25.zero (by decide), g25_9]
  have g26_18 : reg n26 (18 : Fin 32) = out := by
    rw [rb26, runBlock_reg _ _ _ (18 : Fin 32) s25.zero (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by
    rw [rb26, runBlock_reg _ _ _ (19 : Fin 32) s25.zero (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = x20 := by
    rw [rb26, runBlock_reg _ _ _ (20 : Fin 32) s25.zero (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by
    rw [rb26, runBlock_reg _ _ _ (21 : Fin 32) s25.zero (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = x22 := by
    rw [rb26, runBlock_reg _ _ _ (22 : Fin 32) s25.zero (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = x23 := by
    rw [rb26, runBlock_reg _ _ _ (23 : Fin 32) s25.zero (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = ni := by
    rw [rb26, runBlock_reg _ _ _ (24 : Fin 32) s25.zero (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = x25 := by
    rw [rb26, runBlock_reg _ _ _ (25 : Fin 32) s25.zero (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = ns10 := by
    rw [rb26, runBlock_reg _ _ _ (26 : Fin 32) s25.zero (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = np := by
    rw [rb26, runBlock_reg _ _ _ (27 : Fin 32) s25.zero (by decide), g25_27]
  have g26_10 : reg n26 a0 = B + 0x21A0 + BitVec.ofNat 32 0x420 := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, svCg0171a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_10, g25_11, g25_12, g25_13, g25_14, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_25, g25_26, g25_27, s25.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g26_11 : reg n26 a1 = B + 0x21A0 + BitVec.ofNat 32 0x400 := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, svCg0171a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_10, g25_11, g25_12, g25_13, g25_14, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_25, g25_26, g25_27, s25.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g26_12 : reg n26 a2 = BitVec.ofNat 32 0x4 := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, svCg0171a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_10, g25_11, g25_12, g25_13, g25_14, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_25, g25_26, g25_27, s25.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g26_13 : reg n26 a3 = B + 0x21A0 + BitVec.ofNat 32 0x370 := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, svCg0171a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_10, g25_11, g25_12, g25_13, g25_14, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_25, g25_26, g25_27, s25.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g26_14 : reg n26 a4 = BitVec.ofNat 32 0x3 := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, svCg0171a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g25_2, g25_3, g25_4, g25_8, g25_9, g25_10, g25_11, g25_12, g25_13, g25_14, g25_18, g25_19, g25_20, g25_21, g25_22, g25_23, g25_24, g25_25, g25_26, g25_27, s25.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x4, 0x4), (0x400, 0x4)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_4 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m26]; exact w25_4
  have w26_8 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m26]; exact w25_8
  have w26_c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m26]; exact w25_c
  have w26_10 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m26]; exact w25_10
  have w26_18 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m26]; exact w25_18
  have w26_24 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m26]; exact w25_24
  have w26_28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m26]; exact w25_28
  have w26_2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m26]; exact w25_2c
  have w26_30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m26]; exact w25_30
  have w26_34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m26]; exact w25_34
  have w26_38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m26]; exact w25_38
  have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m26]; exact w25_44
  have w26_48 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m26]; exact w25_48
  have w26_50 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m26]; exact w25_50
  have w26_400 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m26]; exact w25_400
  have b26_14 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m26]; exact b25_14
  have q26_1fc : ∀ j, j < 63 → n26.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m26]; exact q25_1fc j hj
  clear q25_1fc b25_14 w25_400 w25_50 w25_48 w25_44 w25_38 w25_34 w25_30 w25_2c w25_28 w25_24 w25_18 w25_10 w25_c w25_8 w25_4 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_14 g25_13 g25_12 g25_11 g25_10 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 m25 s25 u25 d25
  -- 0x1728: sv_b64fF
  obtain ⟨n27, c27, s27, sp27, rk27, K27, Ok27, Bad27, fr27⟩ := sv_b64fF (rc := 0x420) (oc := 0x370) (tc := 0x400) (nl := 4) (L := 3)
    F E26 (CK0.sv FW fR26) s26 sv_at_1728 sv_at_172c (by decide) (by decide) g26_2
    g26_10 g26_11 g26_12 g26_13 g26_14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have t27 : Steps n0 n27 := t26.trans c27
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.keepL K27 (by decide)
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk27 (3 : Fin 32) (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk27 (4 : Fin 32) (by decide), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = nl := by rw [rk27 (8 : Fin 32) (by decide), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = ns1 := by rw [rk27 (9 : Fin 32) (by decide), g26_9]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [rk27 (18 : Fin 32) (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [rk27 (19 : Fin 32) (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [rk27 (20 : Fin 32) (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [rk27 (21 : Fin 32) (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [rk27 (22 : Fin 32) (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [rk27 (23 : Fin 32) (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = ni := by rw [rk27 (24 : Fin 32) (by decide), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = x25 := by rw [rk27 (25 : Fin 32) (by decide), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = ns10 := by rw [rk27 (26 : Fin 32) (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = np := by rw [rk27 (27 : Fin 32) (by decide), g26_27]
  have g27_2 : reg n27 sp = B + 0x21A0 := sp27
  rw [mb4_of_ld w26_400] at Ok27 Bad27
  obtain ⟨r27, hr27⟩ : ∃ r, base64Decode (memBytes M0 pg 4) = r := ⟨_, rfl⟩
  rcases r27 with _ | bq27
  · have z27 := Bad27 fun b h => by rw [hr27] at h; cases h
    have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)] := keep_kk26.trans K27
    clear keep_kk26
    have w27_4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := (K27.w32 (by decide) (by decide)).trans w26_4
    have w27_8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K27.w32 (by decide) (by decide)).trans w26_8
    have w27_c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K27.w32 (by decide) (by decide)).trans w26_c
    have w27_10 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K27.w32 (by decide) (by decide)).trans w26_10
    have w27_18 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := (K27.w32 (by decide) (by decide)).trans w26_18
    have w27_24 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := (K27.w32 (by decide) (by decide)).trans w26_24
    have w27_28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K27.w32 (by decide) (by decide)).trans w26_28
    have w27_2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K27.w32 (by decide) (by decide)).trans w26_2c
    have w27_30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := (K27.w32 (by decide) (by decide)).trans w26_30
    have w27_34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K27.w32 (by decide) (by decide)).trans w26_34
    have w27_38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K27.w32 (by decide) (by decide)).trans w26_38
    have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K27.w32 (by decide) (by decide)).trans w26_44
    have w27_48 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K27.w32 (by decide) (by decide)).trans w26_48
    have w27_50 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K27.w32 (by decide) (by decide)).trans w26_50
    have w27_400 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := (K27.w32 (by decide) (by decide)).trans w26_400
    have b27_14 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := (K27.b8 (by decide) (by decide)).trans b26_14
    have q27_1fc : ∀ j, j < 63 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_1fc j hj)
    have b27_420 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := z27
    clear q26_1fc b26_14 w26_400 w26_50 w26_48 w26_44 w26_38 w26_34 w26_30 w26_2c w26_28 w26_24 w26_18 w26_10 w26_c w26_8 w26_4 g26_14 g26_13 g26_12 g26_11 g26_10 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 rb26 s26 m26 u26 c26
    -- 0x1730: lbu
    obtain ⟨n28, d28, u28⟩ := s27.lbu E27.self sv_at_1730 (off' := 0x1734) (by decide)
    have s28 : St n28.mem SV n28 0x1734 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
    have m28 : n28.mem = n27.mem := u28.mem
    have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
    have t28 : Steps n0 n28 := t27.trans (.single d28)
    have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
    have E28 : SvCode n28.mem := E27.fr F fr28
    have V28 : SvSaves B n28.mem v := V27.same m28
    have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_2]
    have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_3]
    have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_4]
    have g28_8 : reg n28 (8 : Fin 32) = nl := by rw [u28.regs, upd_ne (by decide) (by decide), g27_8]
    have g28_9 : reg n28 (9 : Fin 32) = ns1 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_9]
    have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, upd_ne (by decide) (by decide), g27_18]
    have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_19]
    have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_20]
    have g28_21 : reg n28 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_21]
    have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_22]
    have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_23]
    have g28_24 : reg n28 (24 : Fin 32) = ni := by rw [u28.regs, upd_ne (by decide) (by decide), g27_24]
    have g28_25 : reg n28 (25 : Fin 32) = x25 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_25]
    have g28_26 : reg n28 (26 : Fin 32) = ns10 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_26]
    have g28_27 : reg n28 (27 : Fin 32) = np := by rw [u28.regs, upd_ne (by decide) (by decide), g27_27]
    have g28_11 : reg n28 a1 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [u28.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g27_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, b27_420]
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)] := by rw [m28]; exact keep_kk27
    clear keep_kk27
    have w28_4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m28]; exact w27_4
    have w28_8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m28]; exact w27_8
    have w28_c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m28]; exact w27_c
    have w28_10 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m28]; exact w27_10
    have w28_18 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m28]; exact w27_18
    have w28_24 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m28]; exact w27_24
    have w28_28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m28]; exact w27_28
    have w28_2c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m28]; exact w27_2c
    have w28_30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m28]; exact w27_30
    have w28_34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m28]; exact w27_34
    have w28_38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m28]; exact w27_38
    have w28_44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m28]; exact w27_44
    have w28_48 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m28]; exact w27_48
    have w28_50 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m28]; exact w27_50
    have w28_400 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m28]; exact w27_400
    have b28_14 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m28]; exact b27_14
    have b28_420 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m28]; exact b27_420
    have q28_1fc : ∀ j, j < 63 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m28]; exact q27_1fc j hj
    clear b27_420 q27_1fc b27_14 w27_400 w27_50 w27_48 w27_44 w27_38 w27_34 w27_30 w27_2c w27_28 w27_24 w27_18 w27_10 w27_c w27_8 w27_4 z27
    -- 0x1734: lw
    obtain ⟨n29, d29, u29⟩ := s28.lw E28.self sv_at_1734 (off' := 0x1736) (by decide)
      (by rw [g28_2, show B + 0x21A0 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0x4 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s29 : St n29.mem SV n29 0x1736 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
    have t29 : Steps n0 n29 := t28.trans (.single d29)
    have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
    have E29 : SvCode n29.mem := E28.fr F fr29
    have V29 : SvSaves B n29.mem v := V28.same m29
    have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_2]
    have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_3]
    have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_4]
    have g29_8 : reg n29 (8 : Fin 32) = nl := by rw [u29.regs, upd_ne (by decide) (by decide), g28_8]
    have g29_9 : reg n29 (9 : Fin 32) = ns1 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_9]
    have g29_11 : reg n29 a1 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_11]
    have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, upd_ne (by decide) (by decide), g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_19]
    have g29_20 : reg n29 (20 : Fin 32) = x20 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_20]
    have g29_21 : reg n29 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = x22 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = x23 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = ni := by rw [u29.regs, upd_ne (by decide) (by decide), g28_24]
    have g29_25 : reg n29 (25 : Fin 32) = x25 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_25]
    have g29_26 : reg n29 (26 : Fin 32) = ns10 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = np := by rw [u29.regs, upd_ne (by decide) (by decide), g28_27]
    have g29_10 : reg n29 a0 = (pg) + BitVec.ofNat 32 0x4 := by
      rw [u29.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g28_2, show B + 0x21A0 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0x4 by sv_addr, w28_4]
    have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m29]; exact w28_4
    have w29_8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m29]; exact w28_8
    have w29_c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m29]; exact w28_c
    have w29_10 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m29]; exact w28_10
    have w29_18 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m29]; exact w28_18
    have w29_24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m29]; exact w28_24
    have w29_28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m29]; exact w28_28
    have w29_2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m29]; exact w28_2c
    have w29_30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m29]; exact w28_30
    have w29_34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m29]; exact w28_34
    have w29_38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m29]; exact w28_38
    have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m29]; exact w28_44
    have w29_48 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m29]; exact w28_48
    have w29_50 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m29]; exact w28_50
    have w29_400 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m29]; exact w28_400
    have b29_14 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m29]; exact b28_14
    have b29_420 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m29]; exact b28_420
    have q29_1fc : ∀ j, j < 63 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m29]; exact q28_1fc j hj
    clear q28_1fc b28_420 b28_14 w28_400 w28_50 w28_48 w28_44 w28_38 w28_34 w28_30 w28_2c w28_28 w28_24 w28_18 w28_10 w28_c w28_8 w28_4 g28_11 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
    -- 0x1736: branch, taken
    obtain ⟨n30, d30, u30⟩ := s29.taken E29.self 0x1878 sv_at_1736
      (by decide) (by rw [g29_11, s29.zero]; decide)
    have s30 : St n30.mem SV n30 0x1878 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
    have m30 : n30.mem = n29.mem := u30.mem
    have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
    have t30 : Steps n0 n30 := t29.trans (.single d30)
    have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
    have E30 : SvCode n30.mem := E29.fr F fr30
    have V30 : SvSaves B n30.mem v := V29.same m30
    have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, g29_2]
    have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, g29_3]
    have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, g29_4]
    have g30_8 : reg n30 (8 : Fin 32) = nl := by rw [u30.regs, g29_8]
    have g30_9 : reg n30 (9 : Fin 32) = ns1 := by rw [u30.regs, g29_9]
    have g30_10 : reg n30 a0 = (pg) + BitVec.ofNat 32 0x4 := by rw [u30.regs, g29_10]
    have g30_11 : reg n30 a1 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u30.regs, g29_11]
    have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, g29_18]
    have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, g29_19]
    have g30_20 : reg n30 (20 : Fin 32) = x20 := by rw [u30.regs, g29_20]
    have g30_21 : reg n30 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [u30.regs, g29_21]
    have g30_22 : reg n30 (22 : Fin 32) = x22 := by rw [u30.regs, g29_22]
    have g30_23 : reg n30 (23 : Fin 32) = x23 := by rw [u30.regs, g29_23]
    have g30_24 : reg n30 (24 : Fin 32) = ni := by rw [u30.regs, g29_24]
    have g30_25 : reg n30 (25 : Fin 32) = x25 := by rw [u30.regs, g29_25]
    have g30_26 : reg n30 (26 : Fin 32) = ns10 := by rw [u30.regs, g29_26]
    have g30_27 : reg n30 (27 : Fin 32) = np := by rw [u30.regs, g29_27]
    have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)] := by rw [m30]; exact keep_kk29
    clear keep_kk29
    have w30_4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m30]; exact w29_4
    have w30_8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m30]; exact w29_8
    have w30_c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m30]; exact w29_c
    have w30_10 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m30]; exact w29_10
    have w30_18 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m30]; exact w29_18
    have w30_24 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m30]; exact w29_24
    have w30_28 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m30]; exact w29_28
    have w30_2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m30]; exact w29_2c
    have w30_30 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m30]; exact w29_30
    have w30_34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m30]; exact w29_34
    have w30_38 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m30]; exact w29_38
    have w30_44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m30]; exact w29_44
    have w30_48 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m30]; exact w29_48
    have w30_50 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m30]; exact w29_50
    have w30_400 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m30]; exact w29_400
    have b30_14 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m30]; exact b29_14
    have b30_420 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m30]; exact b29_420
    have q30_1fc : ∀ j, j < 63 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m30]; exact q29_1fc j hj
    clear q29_1fc b29_420 b29_14 w29_400 w29_50 w29_48 w29_44 w29_38 w29_34 w29_30 w29_2c w29_28 w29_24 w29_18 w29_10 w29_c w29_8 w29_4 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_11 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
    -- 0x1878
    obtain ⟨n31, c31, u31⟩ := s30.block svCg01878 E30.self svCg01878_end
      ⟨trivial, trivial⟩
    have m31 : n31.mem = n30.mem := u31.mem
    have s31 : St n31.mem SV n31 0x187A (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
    have rb31 : ∀ q, reg n31 q = (runBlock svCg01878 (n30.mem, reg n30)).2 q := fun q => by rw [u31.regs]
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
    have g31_8 : reg n31 (8 : Fin 32) = nl := by
      rw [rb31, runBlock_reg _ _ _ (8 : Fin 32) s30.zero (by decide), g30_8]
    have g31_9 : reg n31 (9 : Fin 32) = ns1 := by
      rw [rb31, runBlock_reg _ _ _ (9 : Fin 32) s30.zero (by decide), g30_9]
    have g31_10 : reg n31 a0 = (pg) + BitVec.ofNat 32 0x4 := by
      rw [rb31, runBlock_reg _ _ _ a0 s30.zero (by decide), g30_10]
    have g31_11 : reg n31 a1 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [rb31, runBlock_reg _ _ _ a1 s30.zero (by decide), g30_11]
    have g31_18 : reg n31 (18 : Fin 32) = out := by
      rw [rb31, runBlock_reg _ _ _ (18 : Fin 32) s30.zero (by decide), g30_18]
    have g31_19 : reg n31 (19 : Fin 32) = bp := by
      rw [rb31, runBlock_reg _ _ _ (19 : Fin 32) s30.zero (by decide), g30_19]
    have g31_20 : reg n31 (20 : Fin 32) = x20 := by
      rw [rb31, runBlock_reg _ _ _ (20 : Fin 32) s30.zero (by decide), g30_20]
    have g31_21 : reg n31 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by
      rw [rb31, runBlock_reg _ _ _ (21 : Fin 32) s30.zero (by decide), g30_21]
    have g31_22 : reg n31 (22 : Fin 32) = x22 := by
      rw [rb31, runBlock_reg _ _ _ (22 : Fin 32) s30.zero (by decide), g30_22]
    have g31_23 : reg n31 (23 : Fin 32) = x23 := by
      rw [rb31, runBlock_reg _ _ _ (23 : Fin 32) s30.zero (by decide), g30_23]
    have g31_24 : reg n31 (24 : Fin 32) = ni := by
      rw [rb31, runBlock_reg _ _ _ (24 : Fin 32) s30.zero (by decide), g30_24]
    have g31_26 : reg n31 (26 : Fin 32) = ns10 := by
      rw [rb31, runBlock_reg _ _ _ (26 : Fin 32) s30.zero (by decide), g30_26]
    have g31_27 : reg n31 (27 : Fin 32) = np := by
      rw [rb31, runBlock_reg _ _ _ (27 : Fin 32) s30.zero (by decide), g30_27]
    have g31_25 : reg n31 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb31]; simp +decide only [runBlock, BInstr.run, svCg01878, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_10, g30_11, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, s30.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)] := by rw [m31]; exact keep_kk30
    clear keep_kk30
    have w31_4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m31]; exact w30_4
    have w31_8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m31]; exact w30_8
    have w31_c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m31]; exact w30_c
    have w31_10 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m31]; exact w30_10
    have w31_18 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m31]; exact w30_18
    have w31_24 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m31]; exact w30_24
    have w31_28 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m31]; exact w30_28
    have w31_2c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m31]; exact w30_2c
    have w31_30 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m31]; exact w30_30
    have w31_34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m31]; exact w30_34
    have w31_38 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m31]; exact w30_38
    have w31_44 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m31]; exact w30_44
    have w31_48 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m31]; exact w30_48
    have w31_50 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m31]; exact w30_50
    have w31_400 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m31]; exact w30_400
    have b31_14 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m31]; exact b30_14
    have b31_420 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m31]; exact b30_420
    have q31_1fc : ∀ j, j < 63 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m31]; exact q30_1fc j hj
    clear q30_1fc b30_420 b30_14 w30_400 w30_50 w30_48 w30_44 w30_38 w30_34 w30_30 w30_2c w30_28 w30_24 w30_18 w30_10 w30_c w30_8 w30_4 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_11 g30_10 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30
    -- 0x187A: j
    obtain ⟨n32, d32, u32⟩ := s31.jump E31.self sv_at_187a (off' := 0x1882) (by decide)
      (by rw [s31.pc]; decide)
    have s32 : St n32.mem SV n32 0x1882 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
    have m32 : n32.mem = n31.mem := u32.mem
    have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
    have t32 : Steps n0 n32 := t31.trans (.single d32)
    have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
    have E32 : SvCode n32.mem := E31.fr F fr32
    have V32 : SvSaves B n32.mem v := V31.same m32
    have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, g31_2]
    have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, g31_3]
    have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, g31_4]
    have g32_8 : reg n32 (8 : Fin 32) = nl := by rw [u32.regs, g31_8]
    have g32_9 : reg n32 (9 : Fin 32) = ns1 := by rw [u32.regs, g31_9]
    have g32_10 : reg n32 a0 = (pg) + BitVec.ofNat 32 0x4 := by rw [u32.regs, g31_10]
    have g32_11 : reg n32 a1 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u32.regs, g31_11]
    have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, g31_18]
    have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, g31_19]
    have g32_20 : reg n32 (20 : Fin 32) = x20 := by rw [u32.regs, g31_20]
    have g32_21 : reg n32 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [u32.regs, g31_21]
    have g32_22 : reg n32 (22 : Fin 32) = x22 := by rw [u32.regs, g31_22]
    have g32_23 : reg n32 (23 : Fin 32) = x23 := by rw [u32.regs, g31_23]
    have g32_24 : reg n32 (24 : Fin 32) = ni := by rw [u32.regs, g31_24]
    have g32_25 : reg n32 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u32.regs, g31_25]
    have g32_26 : reg n32 (26 : Fin 32) = ns10 := by rw [u32.regs, g31_26]
    have g32_27 : reg n32 (27 : Fin 32) = np := by rw [u32.regs, g31_27]
    have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)] := by rw [m32]; exact keep_kk31
    clear keep_kk31
    have w32_4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m32]; exact w31_4
    have w32_8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m32]; exact w31_8
    have w32_c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m32]; exact w31_c
    have w32_10 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m32]; exact w31_10
    have w32_18 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m32]; exact w31_18
    have w32_24 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m32]; exact w31_24
    have w32_28 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m32]; exact w31_28
    have w32_2c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m32]; exact w31_2c
    have w32_30 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m32]; exact w31_30
    have w32_34 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m32]; exact w31_34
    have w32_38 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m32]; exact w31_38
    have w32_44 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m32]; exact w31_44
    have w32_48 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m32]; exact w31_48
    have w32_50 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m32]; exact w31_50
    have w32_400 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m32]; exact w31_400
    have b32_14 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m32]; exact b31_14
    have b32_420 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m32]; exact b31_420
    have q32_1fc : ∀ j, j < 63 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m32]; exact q31_1fc j hj
    clear q31_1fc b31_420 b31_14 w31_400 w31_50 w31_48 w31_44 w31_38 w31_34 w31_30 w31_2c w31_28 w31_24 w31_18 w31_10 w31_c w31_8 w31_4 g31_25 g31_27 g31_26 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_11 g31_10 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 rb31 s31 m31 u31 c31
    exact .inl ⟨(fun ⟨h0', bq27', h1', _⟩ => by rw [hr27] at h1'; cases h1'), sv_fail_1882 F E32 s32 t32 (fun x hx => (fR32 x hx).trans (fM x hx).symm) V32 hret g32_2 g32_18 hO g32_3 g32_4⟩
  by_cases hl3 : bq27.length ≤ 3
  rotate_left
  · have z27 := Bad27 fun b h => by rw [hr27] at h; cases h; omega
    have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)] := keep_kk26.trans K27
    clear keep_kk26
    have w27_4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := (K27.w32 (by decide) (by decide)).trans w26_4
    have w27_8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K27.w32 (by decide) (by decide)).trans w26_8
    have w27_c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K27.w32 (by decide) (by decide)).trans w26_c
    have w27_10 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K27.w32 (by decide) (by decide)).trans w26_10
    have w27_18 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := (K27.w32 (by decide) (by decide)).trans w26_18
    have w27_24 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := (K27.w32 (by decide) (by decide)).trans w26_24
    have w27_28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K27.w32 (by decide) (by decide)).trans w26_28
    have w27_2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K27.w32 (by decide) (by decide)).trans w26_2c
    have w27_30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := (K27.w32 (by decide) (by decide)).trans w26_30
    have w27_34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K27.w32 (by decide) (by decide)).trans w26_34
    have w27_38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K27.w32 (by decide) (by decide)).trans w26_38
    have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K27.w32 (by decide) (by decide)).trans w26_44
    have w27_48 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K27.w32 (by decide) (by decide)).trans w26_48
    have w27_50 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K27.w32 (by decide) (by decide)).trans w26_50
    have w27_400 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := (K27.w32 (by decide) (by decide)).trans w26_400
    have b27_14 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := (K27.b8 (by decide) (by decide)).trans b26_14
    have q27_1fc : ∀ j, j < 63 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_1fc j hj)
    have b27_420 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := z27
    clear q26_1fc b26_14 w26_400 w26_50 w26_48 w26_44 w26_38 w26_34 w26_30 w26_2c w26_28 w26_24 w26_18 w26_10 w26_c w26_8 w26_4 g26_14 g26_13 g26_12 g26_11 g26_10 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 rb26 s26 m26 u26 c26
    -- 0x1730: lbu
    obtain ⟨n28, d28, u28⟩ := s27.lbu E27.self sv_at_1730 (off' := 0x1734) (by decide)
    have s28 : St n28.mem SV n28 0x1734 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
    have m28 : n28.mem = n27.mem := u28.mem
    have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
    have t28 : Steps n0 n28 := t27.trans (.single d28)
    have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
    have E28 : SvCode n28.mem := E27.fr F fr28
    have V28 : SvSaves B n28.mem v := V27.same m28
    have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_2]
    have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_3]
    have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_4]
    have g28_8 : reg n28 (8 : Fin 32) = nl := by rw [u28.regs, upd_ne (by decide) (by decide), g27_8]
    have g28_9 : reg n28 (9 : Fin 32) = ns1 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_9]
    have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, upd_ne (by decide) (by decide), g27_18]
    have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_19]
    have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_20]
    have g28_21 : reg n28 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_21]
    have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_22]
    have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_23]
    have g28_24 : reg n28 (24 : Fin 32) = ni := by rw [u28.regs, upd_ne (by decide) (by decide), g27_24]
    have g28_25 : reg n28 (25 : Fin 32) = x25 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_25]
    have g28_26 : reg n28 (26 : Fin 32) = ns10 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_26]
    have g28_27 : reg n28 (27 : Fin 32) = np := by rw [u28.regs, upd_ne (by decide) (by decide), g27_27]
    have g28_11 : reg n28 a1 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [u28.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g27_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, b27_420]
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)] := by rw [m28]; exact keep_kk27
    clear keep_kk27
    have w28_4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m28]; exact w27_4
    have w28_8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m28]; exact w27_8
    have w28_c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m28]; exact w27_c
    have w28_10 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m28]; exact w27_10
    have w28_18 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m28]; exact w27_18
    have w28_24 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m28]; exact w27_24
    have w28_28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m28]; exact w27_28
    have w28_2c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m28]; exact w27_2c
    have w28_30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m28]; exact w27_30
    have w28_34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m28]; exact w27_34
    have w28_38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m28]; exact w27_38
    have w28_44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m28]; exact w27_44
    have w28_48 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m28]; exact w27_48
    have w28_50 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m28]; exact w27_50
    have w28_400 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m28]; exact w27_400
    have b28_14 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m28]; exact b27_14
    have b28_420 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m28]; exact b27_420
    have q28_1fc : ∀ j, j < 63 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m28]; exact q27_1fc j hj
    clear b27_420 q27_1fc b27_14 w27_400 w27_50 w27_48 w27_44 w27_38 w27_34 w27_30 w27_2c w27_28 w27_24 w27_18 w27_10 w27_c w27_8 w27_4 z27
    -- 0x1734: lw
    obtain ⟨n29, d29, u29⟩ := s28.lw E28.self sv_at_1734 (off' := 0x1736) (by decide)
      (by rw [g28_2, show B + 0x21A0 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0x4 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s29 : St n29.mem SV n29 0x1736 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
    have t29 : Steps n0 n29 := t28.trans (.single d29)
    have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
    have E29 : SvCode n29.mem := E28.fr F fr29
    have V29 : SvSaves B n29.mem v := V28.same m29
    have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_2]
    have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_3]
    have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_4]
    have g29_8 : reg n29 (8 : Fin 32) = nl := by rw [u29.regs, upd_ne (by decide) (by decide), g28_8]
    have g29_9 : reg n29 (9 : Fin 32) = ns1 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_9]
    have g29_11 : reg n29 a1 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_11]
    have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, upd_ne (by decide) (by decide), g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_19]
    have g29_20 : reg n29 (20 : Fin 32) = x20 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_20]
    have g29_21 : reg n29 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = x22 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = x23 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = ni := by rw [u29.regs, upd_ne (by decide) (by decide), g28_24]
    have g29_25 : reg n29 (25 : Fin 32) = x25 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_25]
    have g29_26 : reg n29 (26 : Fin 32) = ns10 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = np := by rw [u29.regs, upd_ne (by decide) (by decide), g28_27]
    have g29_10 : reg n29 a0 = (pg) + BitVec.ofNat 32 0x4 := by
      rw [u29.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g28_2, show B + 0x21A0 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0x4 by sv_addr, w28_4]
    have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m29]; exact w28_4
    have w29_8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m29]; exact w28_8
    have w29_c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m29]; exact w28_c
    have w29_10 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m29]; exact w28_10
    have w29_18 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m29]; exact w28_18
    have w29_24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m29]; exact w28_24
    have w29_28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m29]; exact w28_28
    have w29_2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m29]; exact w28_2c
    have w29_30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m29]; exact w28_30
    have w29_34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m29]; exact w28_34
    have w29_38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m29]; exact w28_38
    have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m29]; exact w28_44
    have w29_48 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m29]; exact w28_48
    have w29_50 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m29]; exact w28_50
    have w29_400 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m29]; exact w28_400
    have b29_14 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m29]; exact b28_14
    have b29_420 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m29]; exact b28_420
    have q29_1fc : ∀ j, j < 63 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m29]; exact q28_1fc j hj
    clear q28_1fc b28_420 b28_14 w28_400 w28_50 w28_48 w28_44 w28_38 w28_34 w28_30 w28_2c w28_28 w28_24 w28_18 w28_10 w28_c w28_8 w28_4 g28_11 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
    -- 0x1736: branch, taken
    obtain ⟨n30, d30, u30⟩ := s29.taken E29.self 0x1878 sv_at_1736
      (by decide) (by rw [g29_11, s29.zero]; decide)
    have s30 : St n30.mem SV n30 0x1878 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
    have m30 : n30.mem = n29.mem := u30.mem
    have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
    have t30 : Steps n0 n30 := t29.trans (.single d30)
    have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
    have E30 : SvCode n30.mem := E29.fr F fr30
    have V30 : SvSaves B n30.mem v := V29.same m30
    have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, g29_2]
    have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, g29_3]
    have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, g29_4]
    have g30_8 : reg n30 (8 : Fin 32) = nl := by rw [u30.regs, g29_8]
    have g30_9 : reg n30 (9 : Fin 32) = ns1 := by rw [u30.regs, g29_9]
    have g30_10 : reg n30 a0 = (pg) + BitVec.ofNat 32 0x4 := by rw [u30.regs, g29_10]
    have g30_11 : reg n30 a1 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u30.regs, g29_11]
    have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, g29_18]
    have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, g29_19]
    have g30_20 : reg n30 (20 : Fin 32) = x20 := by rw [u30.regs, g29_20]
    have g30_21 : reg n30 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [u30.regs, g29_21]
    have g30_22 : reg n30 (22 : Fin 32) = x22 := by rw [u30.regs, g29_22]
    have g30_23 : reg n30 (23 : Fin 32) = x23 := by rw [u30.regs, g29_23]
    have g30_24 : reg n30 (24 : Fin 32) = ni := by rw [u30.regs, g29_24]
    have g30_25 : reg n30 (25 : Fin 32) = x25 := by rw [u30.regs, g29_25]
    have g30_26 : reg n30 (26 : Fin 32) = ns10 := by rw [u30.regs, g29_26]
    have g30_27 : reg n30 (27 : Fin 32) = np := by rw [u30.regs, g29_27]
    have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)] := by rw [m30]; exact keep_kk29
    clear keep_kk29
    have w30_4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m30]; exact w29_4
    have w30_8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m30]; exact w29_8
    have w30_c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m30]; exact w29_c
    have w30_10 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m30]; exact w29_10
    have w30_18 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m30]; exact w29_18
    have w30_24 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m30]; exact w29_24
    have w30_28 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m30]; exact w29_28
    have w30_2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m30]; exact w29_2c
    have w30_30 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m30]; exact w29_30
    have w30_34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m30]; exact w29_34
    have w30_38 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m30]; exact w29_38
    have w30_44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m30]; exact w29_44
    have w30_48 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m30]; exact w29_48
    have w30_50 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m30]; exact w29_50
    have w30_400 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m30]; exact w29_400
    have b30_14 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m30]; exact b29_14
    have b30_420 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m30]; exact b29_420
    have q30_1fc : ∀ j, j < 63 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m30]; exact q29_1fc j hj
    clear q29_1fc b29_420 b29_14 w29_400 w29_50 w29_48 w29_44 w29_38 w29_34 w29_30 w29_2c w29_28 w29_24 w29_18 w29_10 w29_c w29_8 w29_4 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_11 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
    -- 0x1878
    obtain ⟨n31, c31, u31⟩ := s30.block svCg01878 E30.self svCg01878_end
      ⟨trivial, trivial⟩
    have m31 : n31.mem = n30.mem := u31.mem
    have s31 : St n31.mem SV n31 0x187A (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
    have rb31 : ∀ q, reg n31 q = (runBlock svCg01878 (n30.mem, reg n30)).2 q := fun q => by rw [u31.regs]
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
    have g31_8 : reg n31 (8 : Fin 32) = nl := by
      rw [rb31, runBlock_reg _ _ _ (8 : Fin 32) s30.zero (by decide), g30_8]
    have g31_9 : reg n31 (9 : Fin 32) = ns1 := by
      rw [rb31, runBlock_reg _ _ _ (9 : Fin 32) s30.zero (by decide), g30_9]
    have g31_10 : reg n31 a0 = (pg) + BitVec.ofNat 32 0x4 := by
      rw [rb31, runBlock_reg _ _ _ a0 s30.zero (by decide), g30_10]
    have g31_11 : reg n31 a1 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [rb31, runBlock_reg _ _ _ a1 s30.zero (by decide), g30_11]
    have g31_18 : reg n31 (18 : Fin 32) = out := by
      rw [rb31, runBlock_reg _ _ _ (18 : Fin 32) s30.zero (by decide), g30_18]
    have g31_19 : reg n31 (19 : Fin 32) = bp := by
      rw [rb31, runBlock_reg _ _ _ (19 : Fin 32) s30.zero (by decide), g30_19]
    have g31_20 : reg n31 (20 : Fin 32) = x20 := by
      rw [rb31, runBlock_reg _ _ _ (20 : Fin 32) s30.zero (by decide), g30_20]
    have g31_21 : reg n31 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by
      rw [rb31, runBlock_reg _ _ _ (21 : Fin 32) s30.zero (by decide), g30_21]
    have g31_22 : reg n31 (22 : Fin 32) = x22 := by
      rw [rb31, runBlock_reg _ _ _ (22 : Fin 32) s30.zero (by decide), g30_22]
    have g31_23 : reg n31 (23 : Fin 32) = x23 := by
      rw [rb31, runBlock_reg _ _ _ (23 : Fin 32) s30.zero (by decide), g30_23]
    have g31_24 : reg n31 (24 : Fin 32) = ni := by
      rw [rb31, runBlock_reg _ _ _ (24 : Fin 32) s30.zero (by decide), g30_24]
    have g31_26 : reg n31 (26 : Fin 32) = ns10 := by
      rw [rb31, runBlock_reg _ _ _ (26 : Fin 32) s30.zero (by decide), g30_26]
    have g31_27 : reg n31 (27 : Fin 32) = np := by
      rw [rb31, runBlock_reg _ _ _ (27 : Fin 32) s30.zero (by decide), g30_27]
    have g31_25 : reg n31 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb31]; simp +decide only [runBlock, BInstr.run, svCg01878, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_10, g30_11, g30_18, g30_19, g30_20, g30_21, g30_22, g30_23, g30_24, g30_25, g30_26, g30_27, s30.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)] := by rw [m31]; exact keep_kk30
    clear keep_kk30
    have w31_4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m31]; exact w30_4
    have w31_8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m31]; exact w30_8
    have w31_c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m31]; exact w30_c
    have w31_10 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m31]; exact w30_10
    have w31_18 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m31]; exact w30_18
    have w31_24 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m31]; exact w30_24
    have w31_28 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m31]; exact w30_28
    have w31_2c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m31]; exact w30_2c
    have w31_30 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m31]; exact w30_30
    have w31_34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m31]; exact w30_34
    have w31_38 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m31]; exact w30_38
    have w31_44 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m31]; exact w30_44
    have w31_48 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m31]; exact w30_48
    have w31_50 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m31]; exact w30_50
    have w31_400 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m31]; exact w30_400
    have b31_14 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m31]; exact b30_14
    have b31_420 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m31]; exact b30_420
    have q31_1fc : ∀ j, j < 63 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m31]; exact q30_1fc j hj
    clear q30_1fc b30_420 b30_14 w30_400 w30_50 w30_48 w30_44 w30_38 w30_34 w30_30 w30_2c w30_28 w30_24 w30_18 w30_10 w30_c w30_8 w30_4 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_11 g30_10 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30
    -- 0x187A: j
    obtain ⟨n32, d32, u32⟩ := s31.jump E31.self sv_at_187a (off' := 0x1882) (by decide)
      (by rw [s31.pc]; decide)
    have s32 : St n32.mem SV n32 0x1882 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
    have m32 : n32.mem = n31.mem := u32.mem
    have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
    have t32 : Steps n0 n32 := t31.trans (.single d32)
    have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
    have E32 : SvCode n32.mem := E31.fr F fr32
    have V32 : SvSaves B n32.mem v := V31.same m32
    have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, g31_2]
    have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, g31_3]
    have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, g31_4]
    have g32_8 : reg n32 (8 : Fin 32) = nl := by rw [u32.regs, g31_8]
    have g32_9 : reg n32 (9 : Fin 32) = ns1 := by rw [u32.regs, g31_9]
    have g32_10 : reg n32 a0 = (pg) + BitVec.ofNat 32 0x4 := by rw [u32.regs, g31_10]
    have g32_11 : reg n32 a1 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u32.regs, g31_11]
    have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, g31_18]
    have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, g31_19]
    have g32_20 : reg n32 (20 : Fin 32) = x20 := by rw [u32.regs, g31_20]
    have g32_21 : reg n32 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [u32.regs, g31_21]
    have g32_22 : reg n32 (22 : Fin 32) = x22 := by rw [u32.regs, g31_22]
    have g32_23 : reg n32 (23 : Fin 32) = x23 := by rw [u32.regs, g31_23]
    have g32_24 : reg n32 (24 : Fin 32) = ni := by rw [u32.regs, g31_24]
    have g32_25 : reg n32 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u32.regs, g31_25]
    have g32_26 : reg n32 (26 : Fin 32) = ns10 := by rw [u32.regs, g31_26]
    have g32_27 : reg n32 (27 : Fin 32) = np := by rw [u32.regs, g31_27]
    have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)] := by rw [m32]; exact keep_kk31
    clear keep_kk31
    have w32_4 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m32]; exact w31_4
    have w32_8 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m32]; exact w31_8
    have w32_c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m32]; exact w31_c
    have w32_10 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m32]; exact w31_10
    have w32_18 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m32]; exact w31_18
    have w32_24 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m32]; exact w31_24
    have w32_28 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m32]; exact w31_28
    have w32_2c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m32]; exact w31_2c
    have w32_30 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m32]; exact w31_30
    have w32_34 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m32]; exact w31_34
    have w32_38 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m32]; exact w31_38
    have w32_44 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m32]; exact w31_44
    have w32_48 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m32]; exact w31_48
    have w32_50 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m32]; exact w31_50
    have w32_400 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m32]; exact w31_400
    have b32_14 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m32]; exact b31_14
    have b32_420 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (1 : BitVec 8) := by rw [m32]; exact b31_420
    have q32_1fc : ∀ j, j < 63 → n32.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m32]; exact q31_1fc j hj
    clear q31_1fc b31_420 b31_14 w31_400 w31_50 w31_48 w31_44 w31_38 w31_34 w31_30 w31_2c w31_28 w31_24 w31_18 w31_10 w31_c w31_8 w31_4 g31_25 g31_27 g31_26 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_11 g31_10 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 rb31 s31 m31 u31 c31
    exact .inl ⟨(fun ⟨h0', bq27', h1', h2', _⟩ => by rw [hr27] at h1'; cases h1'; exact hl3 h2'), sv_fail_1882 F E32 s32 t32 (fun x hx => (fR32 x hx).trans (fM x hx).symm) V32 hret g32_2 g32_18 hO g32_3 g32_4⟩
  have z27 := Ok27 bq27 hr27 hl3
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)] := keep_kk26.trans K27
  clear keep_kk26
  have w27_4 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := (K27.w32 (by decide) (by decide)).trans w26_4
  have w27_8 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := (K27.w32 (by decide) (by decide)).trans w26_8
  have w27_c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := (K27.w32 (by decide) (by decide)).trans w26_c
  have w27_10 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := (K27.w32 (by decide) (by decide)).trans w26_10
  have w27_18 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := (K27.w32 (by decide) (by decide)).trans w26_18
  have w27_24 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := (K27.w32 (by decide) (by decide)).trans w26_24
  have w27_28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := (K27.w32 (by decide) (by decide)).trans w26_28
  have w27_2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := (K27.w32 (by decide) (by decide)).trans w26_2c
  have w27_30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := (K27.w32 (by decide) (by decide)).trans w26_30
  have w27_34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := (K27.w32 (by decide) (by decide)).trans w26_34
  have w27_38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K27.w32 (by decide) (by decide)).trans w26_38
  have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K27.w32 (by decide) (by decide)).trans w26_44
  have w27_48 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K27.w32 (by decide) (by decide)).trans w26_48
  have w27_50 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K27.w32 (by decide) (by decide)).trans w26_50
  have w27_400 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := (K27.w32 (by decide) (by decide)).trans w26_400
  have b27_14 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := (K27.b8 (by decide) (by decide)).trans b26_14
  have q27_1fc : ∀ j, j < 63 → n27.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => (K27.range (by decide) (by decide) j hj).trans (q26_1fc j hj)
  have b27_420 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := z27
  clear q26_1fc b26_14 w26_400 w26_50 w26_48 w26_44 w26_38 w26_34 w26_30 w26_2c w26_28 w26_24 w26_18 w26_10 w26_c w26_8 w26_4 g26_14 g26_13 g26_12 g26_11 g26_10 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 rb26 s26 m26 u26 c26
  -- 0x1730: lbu
  obtain ⟨n28, d28, u28⟩ := s27.lbu E27.self sv_at_1730 (off' := 0x1734) (by decide)
  have s28 : St n28.mem SV n28 0x1734 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
  have t28 : Steps n0 n28 := t27.trans (.single d28)
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.same m28
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = nl := by rw [u28.regs, upd_ne (by decide) (by decide), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = ns1 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_9]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, upd_ne (by decide) (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = ni := by rw [u28.regs, upd_ne (by decide) (by decide), g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = x25 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = ns10 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = np := by rw [u28.regs, upd_ne (by decide) (by decide), g27_27]
  have g28_11 : reg n28 a1 = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [u28.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g27_2, show B + 0x21A0 + 0x420 = B + 0x21A0 + BitVec.ofNat 32 0x420 by sv_addr, b27_420]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)] := by rw [m28]; exact keep_kk27
  clear keep_kk27
  have w28_4 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m28]; exact w27_4
  have w28_8 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m28]; exact w27_8
  have w28_c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m28]; exact w27_c
  have w28_10 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m28]; exact w27_10
  have w28_18 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m28]; exact w27_18
  have w28_24 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m28]; exact w27_24
  have w28_28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m28]; exact w27_28
  have w28_2c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m28]; exact w27_2c
  have w28_30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m28]; exact w27_30
  have w28_34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m28]; exact w27_34
  have w28_38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m28]; exact w27_38
  have w28_44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m28]; exact w27_44
  have w28_48 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m28]; exact w27_48
  have w28_50 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m28]; exact w27_50
  have w28_400 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m28]; exact w27_400
  have b28_14 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m28]; exact b27_14
  have b28_420 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m28]; exact b27_420
  have q28_1fc : ∀ j, j < 63 → n28.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m28]; exact q27_1fc j hj
  clear b27_420 q27_1fc b27_14 w27_400 w27_50 w27_48 w27_44 w27_38 w27_34 w27_30 w27_2c w27_28 w27_24 w27_18 w27_10 w27_c w27_8 w27_4 z27 g27_2 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 V27 E27 fR27 t27 fr27 Bad27 Ok27 K27 rk27 sp27 s27 c27
  -- 0x1734: lw
  obtain ⟨n29, d29, u29⟩ := s28.lw E28.self sv_at_1734 (off' := 0x1736) (by decide)
    (by rw [g28_2, show B + 0x21A0 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0x4 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s29 : St n29.mem SV n29 0x1736 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans (.single d29)
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = nl := by rw [u29.regs, upd_ne (by decide) (by decide), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = ns1 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_9]
  have g29_11 : reg n29 a1 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_11]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, upd_ne (by decide) (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = x20 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = x22 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = x23 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = ni := by rw [u29.regs, upd_ne (by decide) (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = x25 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = ns10 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = np := by rw [u29.regs, upd_ne (by decide) (by decide), g28_27]
  have g29_10 : reg n29 a0 = (pg) + BitVec.ofNat 32 0x4 := by
    rw [u29.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g28_2, show B + 0x21A0 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0x4 by sv_addr, w28_4]
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_4 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m29]; exact w28_4
  have w29_8 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m29]; exact w28_8
  have w29_c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m29]; exact w28_c
  have w29_10 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m29]; exact w28_10
  have w29_18 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m29]; exact w28_18
  have w29_24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m29]; exact w28_24
  have w29_28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m29]; exact w28_28
  have w29_2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m29]; exact w28_2c
  have w29_30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m29]; exact w28_30
  have w29_34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m29]; exact w28_34
  have w29_38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m29]; exact w28_38
  have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m29]; exact w28_44
  have w29_48 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m29]; exact w28_48
  have w29_50 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m29]; exact w28_50
  have w29_400 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m29]; exact w28_400
  have b29_14 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m29]; exact b28_14
  have b29_420 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m29]; exact b28_420
  have q29_1fc : ∀ j, j < 63 → n29.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m29]; exact q28_1fc j hj
  clear q28_1fc b28_420 b28_14 w28_400 w28_50 w28_48 w28_44 w28_38 w28_34 w28_30 w28_2c w28_28 w28_24 w28_18 w28_10 w28_c w28_8 w28_4 g28_11 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
  -- 0x1736: branch, not taken
  obtain ⟨n30, d30, u30⟩ := s29.notTaken E29.self 0x173A sv_at_1736
    (by decide) (by rw [g29_11, s29.zero]; decide)
  have s30 : St n30.mem SV n30 0x173A (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
  have t30 : Steps n0 n30 := t29.trans (.single d30)
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.same m30
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = nl := by rw [u30.regs, g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = ns1 := by rw [u30.regs, g29_9]
  have g30_10 : reg n30 a0 = (pg) + BitVec.ofNat 32 0x4 := by rw [u30.regs, g29_10]
  have g30_11 : reg n30 a1 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u30.regs, g29_11]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = x20 := by rw [u30.regs, g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [u30.regs, g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = x22 := by rw [u30.regs, g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = x23 := by rw [u30.regs, g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = ni := by rw [u30.regs, g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = x25 := by rw [u30.regs, g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = ns10 := by rw [u30.regs, g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = np := by rw [u30.regs, g29_27]
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)] := by rw [m30]; exact keep_kk29
  clear keep_kk29
  have w30_4 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m30]; exact w29_4
  have w30_8 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m30]; exact w29_8
  have w30_c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m30]; exact w29_c
  have w30_10 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m30]; exact w29_10
  have w30_18 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m30]; exact w29_18
  have w30_24 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m30]; exact w29_24
  have w30_28 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m30]; exact w29_28
  have w30_2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m30]; exact w29_2c
  have w30_30 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m30]; exact w29_30
  have w30_34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m30]; exact w29_34
  have w30_38 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m30]; exact w29_38
  have w30_44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m30]; exact w29_44
  have w30_48 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m30]; exact w29_48
  have w30_50 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m30]; exact w29_50
  have w30_400 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m30]; exact w29_400
  have b30_14 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m30]; exact b29_14
  have b30_420 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m30]; exact b29_420
  have q30_1fc : ∀ j, j < 63 → n30.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m30]; exact q29_1fc j hj
  clear q29_1fc b29_420 b29_14 w29_400 w29_50 w29_48 w29_44 w29_38 w29_34 w29_30 w29_2c w29_28 w29_24 w29_18 w29_10 w29_c w29_8 w29_4 g29_10 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_11 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
  -- 0x173A: j
  obtain ⟨n31, d31, u31⟩ := s30.jump E30.self sv_at_173a (off' := 0x16D4) (by decide)
    (by rw [s30.pc]; decide)
  have s31 : St n31.mem SV n31 0x16D4 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans (.single d31)
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = nl := by rw [u31.regs, g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = ns1 := by rw [u31.regs, g30_9]
  have g31_10 : reg n31 a0 = (pg) + BitVec.ofNat 32 0x4 := by rw [u31.regs, g30_10]
  have g31_11 : reg n31 a1 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u31.regs, g30_11]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = x20 := by rw [u31.regs, g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = (gi) + BitVec.ofNat 32 0x1 := by rw [u31.regs, g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = x22 := by rw [u31.regs, g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = x23 := by rw [u31.regs, g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = ni := by rw [u31.regs, g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = x25 := by rw [u31.regs, g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = ns10 := by rw [u31.regs, g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = np := by rw [u31.regs, g30_27]
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_4 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x4) = (pg) + BitVec.ofNat 32 0x4 := by rw [m31]; exact w30_4
  have w31_8 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 := by rw [m31]; exact w30_8
  have w31_c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc := by rw [m31]; exact w30_c
  have w31_10 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 := by rw [m31]; exact w30_10
  have w31_18 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh := by rw [m31]; exact w30_18
  have w31_24 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl := by rw [m31]; exact w30_24
  have w31_28 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp := by rw [m31]; exact w30_28
  have w31_2c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c := by rw [m31]; exact w30_2c
  have w31_30 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f := by rw [m31]; exact w30_30
  have w31_34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp := by rw [m31]; exact w30_34
  have w31_38 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m31]; exact w30_38
  have w31_44 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m31]; exact w30_44
  have w31_48 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m31]; exact w30_48
  have w31_50 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m31]; exact w30_50
  have w31_400 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = memLoad32 M0 pg := by rw [m31]; exact w30_400
  have b31_14 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) := by rw [m31]; exact b30_14
  have b31_420 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) := by rw [m31]; exact b30_420
  have q31_1fc : ∀ j, j < 63 → n31.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0) := fun j hj => by rw [m31]; exact q30_1fc j hj
  clear q30_1fc b30_420 b30_14 w30_400 w30_50 w30_48 w30_44 w30_38 w30_34 w30_30 w30_2c w30_28 w30_24 w30_18 w30_10 w30_c w30_8 w30_4 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_11 g30_10 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30
  exact .inr ⟨hlast, bq27, hr27, hl3, n31, t31, s31, E31, V31, fR31, g31_2, g31_3, g31_4, g31_8, g31_9, g31_10, g31_18, g31_19, g31_20, g31_21, g31_22, g31_23, g31_24, g31_25, g31_26, g31_27, w31_4, w31_8, w31_c, w31_10, w31_18, w31_24, w31_28, w31_2c, w31_30, w31_34, w31_38, w31_44, w31_48, w31_50, w31_400, b31_14, q31_1fc, keep_kk31.mono (by decide)⟩

end C3.RV32.Sv
