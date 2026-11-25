import C3BootProofs.Proofs.SvCkpt

/-!
# `sigstore::verify`: a digit of the checkpoint's size

One pass of the size's digit loop, from 0x14FE back to it: the next byte is a decimal digit, and the 64-bit size at offsets 0x64 and 0x74 times ten plus the digit doesn't overflow.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svCkd1504 : List BInstr :=
  [.aluImm .add a1 a1 0xFFFFFFD0]
theorem svCkd1504_end : blockEnd sigstoreVerifyCode 0x1504 svCkd1504 = some 0x1508 := by
  simp only [svCkd1504]
  rw [blockEnd, sv_at_1504]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCkd1508 : List BInstr :=
  [.aluImm .and a1 a1 0xFF]
theorem svCkd1508_end : blockEnd sigstoreVerifyCode 0x1508 svCkd1508 = some 0x150C := by
  simp only [svCkd1508]
  rw [blockEnd, sv_at_1508]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCkd1878 : List BInstr :=
  [.aluImm .add (25 : Fin 32) x0 0x1A]
theorem svCkd1878_end : blockEnd sigstoreVerifyCode 0x1878 svCkd1878 = some 0x187A := by
  simp only [svCkd1878]
  rw [blockEnd, sv_at_1878]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCkd1512 : List BInstr :=
  [.alu .mulhu a3 a2 a0]
theorem svCkd1512_end : blockEnd sigstoreVerifyCode 0x1512 svCkd1512 = some 0x1516 := by
  simp only [svCkd1512]
  rw [blockEnd, sv_at_1512]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCkd1518 : List BInstr :=
  [.alu .mul a2 (9 : Fin 32) a0]
theorem svCkd1518_end : blockEnd sigstoreVerifyCode 0x1518 svCkd1518 = some 0x151C := by
  simp only [svCkd1518]
  rw [blockEnd, sv_at_1518]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCkd151c : List BInstr :=
  [.alu .mulhu a4 (9 : Fin 32) a0]
theorem svCkd151c_end : blockEnd sigstoreVerifyCode 0x151C svCkd151c = some 0x1520 := by
  simp only [svCkd151c]
  rw [blockEnd, sv_at_151c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCkd1520 : List BInstr :=
  [.alu .add a2 a2 a3]
theorem svCkd1520_end : blockEnd sigstoreVerifyCode 0x1520 svCkd1520 = some 0x1522 := by
  simp only [svCkd1520]
  rw [blockEnd, sv_at_1520]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCkd1522 : List BInstr :=
  [.alu .sltu a3 a2 a3]
theorem svCkd1522_end : blockEnd sigstoreVerifyCode 0x1522 svCkd1522 = some 0x1526 := by
  simp only [svCkd1522]
  rw [blockEnd, sv_at_1522]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCkd1526 : List BInstr :=
  [.alu .sltu a4 x0 a4]
theorem svCkd1526_end : blockEnd sigstoreVerifyCode 0x1526 svCkd1526 = some 0x152A := by
  simp only [svCkd1526]
  rw [blockEnd, sv_at_1526]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCkd152a : List BInstr :=
  [.alu .or a3 a3 a4]
theorem svCkd152a_end : blockEnd sigstoreVerifyCode 0x152A svCkd152a = some 0x152C := by
  simp only [svCkd152a]
  rw [blockEnd, sv_at_152a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCkd1532 : List BInstr :=
  [.alu .mul a3 a3 a0]
theorem svCkd1532_end : blockEnd sigstoreVerifyCode 0x1532 svCkd1532 = some 0x1536 := by
  simp only [svCkd1532]
  rw [blockEnd, sv_at_1532]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCkd1536 : List BInstr :=
  [.alu .add a1 a1 a3]
theorem svCkd1536_end : blockEnd sigstoreVerifyCode 0x1536 svCkd1536 = some 0x1538 := by
  simp only [svCkd1536]
  rw [blockEnd, sv_at_1536]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCkd153a : List BInstr :=
  [.alu .sltu a1 a1 a3]
theorem svCkd153a_end : blockEnd sigstoreVerifyCode 0x153A svCkd153a = some 0x153E := by
  simp only [svCkd153a]
  rw [blockEnd, sv_at_153a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCkd153e : List BInstr :=
  [.alu .add a3 a2 a1]
theorem svCkd153e_end : blockEnd sigstoreVerifyCode 0x153E svCkd153e = some 0x1542 := by
  simp only [svCkd153e]
  rw [blockEnd, sv_at_153e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCkd1544 : List BInstr :=
  [.alu .sltu a2 a3 a2]
theorem svCkd1544_end : blockEnd sigstoreVerifyCode 0x1544 svCkd1544 = some 0x1548 := by
  simp only [svCkd1544]
  rw [blockEnd, sv_at_1544]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCkd1548 : List BInstr :=
  [.alu .and a1 a1 a2]
theorem svCkd1548_end : blockEnd sigstoreVerifyCode 0x1548 svCkd1548 = some 0x154A := by
  simp only [svCkd1548]
  rw [blockEnd, sv_at_1548]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCkd154a : List BInstr :=
  [.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x1]
theorem svCkd154a_end : blockEnd sigstoreVerifyCode 0x154A svCkd154a = some 0x154C := by
  simp only [svCkd154a]
  rw [blockEnd, sv_at_154a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svCkd154c : List BInstr :=
  [.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF]
theorem svCkd154c_end : blockEnd sigstoreVerifyCode 0x154C svCkd154c = some 0x154E := by
  simp only [svCkd154c]
  rw [blockEnd, sv_at_154c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_ckd {B out bp x20 x21 x22 x23 x26 c p ckl rl rp w64 w74 : Word} {v : Nat → Word} {n0 : Machine}
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
    (hc : c ≠ 0)
    (pin : SvIn B p c.toNat) :
    (¬ ((((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF).toNat < (BitVec.ofNat 32 0xA).toNat) ∧ ((aluEval .sltu ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) ||| (aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA))) = 0) ∧ ((aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) &&& (aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)))) = 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    ((((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF).toNat < (BitVec.ofNat 32 0xA).toNat) ∧
    ((aluEval .sltu ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) ||| (aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA))) = 0) ∧
    ((aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) &&& (aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)))) = 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x14FE (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = (c) + BitVec.ofNat 32 0xFFFFFFFF ∧
        reg n' (9 : Fin 32) = w74 ∧
        reg n' a0 = BitVec.ofNat 32 0xA ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = (p) + BitVec.ofNat 32 0x1 ∧
        reg n' (25 : Fin 32) = rp ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = rl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = ((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) ∧
        SvKeepL B n0.mem n'.mem [(0x64, 0x4), (0x74, 0x4)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x14FE: branch, not taken
  obtain ⟨n1, d1, u1⟩ := s0.notTaken E0.self 0x1500 sv_at_14fe
    (by decide) (by rw [g0_8, s0.zero]; exact br_beq_f hc)
  have s1 : St n1.mem SV n1 0x1500 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
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
  -- 0x1500: lbu from the bundle
  obtain ⟨n2, d2, u2⟩ := s1.lbu E1.self sv_at_1500 (off' := 0x1504) (by decide)
  have s2 : St n2.mem SV n2 0x1504 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
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
  have g2_10 : reg n2 a0 = BitVec.ofNat 32 0xA := by rw [u2.regs, upd_ne (by decide) (by decide), g1_10]
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
  have g2_11 : reg n2 a1 = (M0 (p)).zeroExtend 32 := by
    rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g1_24, show (p) + 0x0 = p from BitVec.add_zero _, fR1 _ (pin.r0 (toNat_pos_of_ne hc))]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m2]; exact w1_64
  have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m2]; exact w1_74
  clear w1_74 w1_64 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_10 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x1504
  obtain ⟨n3, c3, u3⟩ := s2.block svCkd1504 E2.self svCkd1504_end
    ⟨trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem SV n3 0x1508 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have rb3 : ∀ q, reg n3 q = (runBlock svCkd1504 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans c3
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by
    rw [rb3, runBlock_reg _ _ _ sp s2.zero (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb3, runBlock_reg _ _ _ (3 : Fin 32) s2.zero (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb3, runBlock_reg _ _ _ (4 : Fin 32) s2.zero (by decide), g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = c := by
    rw [rb3, runBlock_reg _ _ _ (8 : Fin 32) s2.zero (by decide), g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = ckl := by
    rw [rb3, runBlock_reg _ _ _ (9 : Fin 32) s2.zero (by decide), g2_9]
  have g3_10 : reg n3 a0 = BitVec.ofNat 32 0xA := by
    rw [rb3, runBlock_reg _ _ _ a0 s2.zero (by decide), g2_10]
  have g3_18 : reg n3 (18 : Fin 32) = out := by
    rw [rb3, runBlock_reg _ _ _ (18 : Fin 32) s2.zero (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by
    rw [rb3, runBlock_reg _ _ _ (19 : Fin 32) s2.zero (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = x20 := by
    rw [rb3, runBlock_reg _ _ _ (20 : Fin 32) s2.zero (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by
    rw [rb3, runBlock_reg _ _ _ (21 : Fin 32) s2.zero (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = x22 := by
    rw [rb3, runBlock_reg _ _ _ (22 : Fin 32) s2.zero (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = x23 := by
    rw [rb3, runBlock_reg _ _ _ (23 : Fin 32) s2.zero (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = p := by
    rw [rb3, runBlock_reg _ _ _ (24 : Fin 32) s2.zero (by decide), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = rp := by
    rw [rb3, runBlock_reg _ _ _ (25 : Fin 32) s2.zero (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by
    rw [rb3, runBlock_reg _ _ _ (26 : Fin 32) s2.zero (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = rl := by
    rw [rb3, runBlock_reg _ _ _ (27 : Fin 32) s2.zero (by decide), g2_27]
  have g3_11 : reg n3 a1 = ((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svCkd1504, upd, ↓reduceIte]; rw [g2_11] <;> rfl
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m3]; exact w2_64
  have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m3]; exact w2_74
  clear w2_74 w2_64 g2_11 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_10 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x1508
  obtain ⟨n4, c4, u4⟩ := s3.block svCkd1508 E3.self svCkd1508_end
    ⟨trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem SV n4 0x150C (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have rb4 : ∀ q, reg n4 q = (runBlock svCkd1508 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
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
  have g4_10 : reg n4 a0 = BitVec.ofNat 32 0xA := by
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
  have g4_25 : reg n4 (25 : Fin 32) = rp := by
    rw [rb4, runBlock_reg _ _ _ (25 : Fin 32) s3.zero (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by
    rw [rb4, runBlock_reg _ _ _ (26 : Fin 32) s3.zero (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = rl := by
    rw [rb4, runBlock_reg _ _ _ (27 : Fin 32) s3.zero (by decide), g3_27]
  have g4_11 : reg n4 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by
    rw [rb4]; simp +decide only [runBlock, BInstr.run, svCkd1508, upd, ↓reduceIte]; rw [g3_11] <;> rfl
  have keep_kk4 : SvKeepL B n0.mem n4.mem [] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m4]; exact w3_64
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m4]; exact w3_74
  clear w3_74 w3_64 g3_11 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_10 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
  by_cases hdig : ((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF).toNat < (BitVec.ofNat 32 0xA).toNat
  rotate_left
  · -- 0x150C: branch, taken
    obtain ⟨n5, d5, u5⟩ := s4.taken E4.self 0x1878 sv_at_150c
      (by decide) (by rw [g4_11, g4_10]; exact br_bgeu_t hdig)
    have s5 : St n5.mem SV n5 0x1878 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
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
    have g5_10 : reg n5 a0 = BitVec.ofNat 32 0xA := by rw [u5.regs, g4_10]
    have g5_11 : reg n5 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by rw [u5.regs, g4_11]
    have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, g4_18]
    have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, g4_19]
    have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [u5.regs, g4_20]
    have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, g4_21]
    have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [u5.regs, g4_22]
    have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [u5.regs, g4_23]
    have g5_24 : reg n5 (24 : Fin 32) = p := by rw [u5.regs, g4_24]
    have g5_25 : reg n5 (25 : Fin 32) = rp := by rw [u5.regs, g4_25]
    have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, g4_26]
    have g5_27 : reg n5 (27 : Fin 32) = rl := by rw [u5.regs, g4_27]
    have keep_kk5 : SvKeepL B n0.mem n5.mem [] := by rw [m5]; exact keep_kk4
    clear keep_kk4
    have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m5]; exact w4_64
    have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m5]; exact w4_74
    clear w4_74 w4_64 g4_11 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
    -- 0x1878
    obtain ⟨n6, c6, u6⟩ := s5.block svCkd1878 E5.self svCkd1878_end
      ⟨trivial, trivial⟩
    have m6 : n6.mem = n5.mem := u6.mem
    have s6 : St n6.mem SV n6 0x187A (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
    have rb6 : ∀ q, reg n6 q = (runBlock svCkd1878 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
    have g6_10 : reg n6 a0 = BitVec.ofNat 32 0xA := by
      rw [rb6, runBlock_reg _ _ _ a0 s5.zero (by decide), g5_10]
    have g6_11 : reg n6 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by
      rw [rb6, runBlock_reg _ _ _ a1 s5.zero (by decide), g5_11]
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
    have g6_26 : reg n6 (26 : Fin 32) = x26 := by
      rw [rb6, runBlock_reg _ _ _ (26 : Fin 32) s5.zero (by decide), g5_26]
    have g6_27 : reg n6 (27 : Fin 32) = rl := by
      rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
    have g6_25 : reg n6 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb6]; simp +decide only [runBlock, BInstr.run, svCkd1878, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_10, g5_11, g5_18, g5_19, g5_20, g5_21, g5_22, g5_23, g5_24, g5_25, g5_26, g5_27, s5.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk6 : SvKeepL B n0.mem n6.mem [] := by rw [m6]; exact keep_kk5
    clear keep_kk5
    have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m6]; exact w5_64
    have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m6]; exact w5_74
    clear w5_74 w5_64 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_11 g5_10 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
    -- 0x187A: j
    obtain ⟨n7, d7, u7⟩ := s6.jump E6.self sv_at_187a (off' := 0x1882) (by decide)
      (by rw [s6.pc]; decide)
    have s7 : St n7.mem SV n7 0x1882 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
    have m7 : n7.mem = n6.mem := u7.mem
    have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
    have t7 : Steps n0 n7 := t6.trans (.single d7)
    have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
    have E7 : SvCode n7.mem := E6.fr F fr7
    have V7 : SvSaves B n7.mem v := V6.same m7
    have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, g6_2]
    have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, g6_3]
    have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, g6_4]
    have g7_8 : reg n7 (8 : Fin 32) = c := by rw [u7.regs, g6_8]
    have g7_9 : reg n7 (9 : Fin 32) = ckl := by rw [u7.regs, g6_9]
    have g7_10 : reg n7 a0 = BitVec.ofNat 32 0xA := by rw [u7.regs, g6_10]
    have g7_11 : reg n7 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by rw [u7.regs, g6_11]
    have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, g6_18]
    have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, g6_19]
    have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [u7.regs, g6_20]
    have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [u7.regs, g6_21]
    have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [u7.regs, g6_22]
    have g7_23 : reg n7 (23 : Fin 32) = x23 := by rw [u7.regs, g6_23]
    have g7_24 : reg n7 (24 : Fin 32) = p := by rw [u7.regs, g6_24]
    have g7_25 : reg n7 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u7.regs, g6_25]
    have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [u7.regs, g6_26]
    have g7_27 : reg n7 (27 : Fin 32) = rl := by rw [u7.regs, g6_27]
    have keep_kk7 : SvKeepL B n0.mem n7.mem [] := by rw [m7]; exact keep_kk6
    clear keep_kk6
    have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m7]; exact w6_64
    have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m7]; exact w6_74
    clear w6_74 w6_64 g6_25 g6_27 g6_26 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_11 g6_10 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hdig h0'), sv_fail_1882 F E7 s7 t7 (fun x hx => (fR7 x hx).trans (fM x hx).symm) V7 hret g7_2 g7_18 hO g7_3 g7_4⟩
  -- 0x150C: branch, not taken
  obtain ⟨n5, d5, u5⟩ := s4.notTaken E4.self 0x1510 sv_at_150c
    (by decide) (by rw [g4_11, g4_10]; exact br_bgeu_f hdig)
  have s5 : St n5.mem SV n5 0x1510 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
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
  have g5_10 : reg n5 a0 = BitVec.ofNat 32 0xA := by rw [u5.regs, g4_10]
  have g5_11 : reg n5 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by rw [u5.regs, g4_11]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, g4_19]
  have g5_20 : reg n5 (20 : Fin 32) = x20 := by rw [u5.regs, g4_20]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = x22 := by rw [u5.regs, g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = x23 := by rw [u5.regs, g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = p := by rw [u5.regs, g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = rp := by rw [u5.regs, g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = rl := by rw [u5.regs, g4_27]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m5]; exact w4_64
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m5]; exact w4_74
  clear w4_74 w4_64 g4_11 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_10 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 rb4 s4 m4 u4 c4
  -- 0x1510: lw
  obtain ⟨n6, d6, u6⟩ := s5.lw E5.self sv_at_1510 (off' := 0x1512) (by decide)
    (by rw [g5_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s6 : St n6.mem SV n6 0x1512 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
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
  have g6_9 : reg n6 (9 : Fin 32) = ckl := by rw [u6.regs, upd_ne (by decide) (by decide), g5_9]
  have g6_10 : reg n6 a0 = BitVec.ofNat 32 0xA := by rw [u6.regs, upd_ne (by decide) (by decide), g5_10]
  have g6_11 : reg n6 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by rw [u6.regs, upd_ne (by decide) (by decide), g5_11]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, upd_ne (by decide) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = x20 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = x23 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = p := by rw [u6.regs, upd_ne (by decide) (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = rp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = rl := by rw [u6.regs, upd_ne (by decide) (by decide), g5_27]
  have g6_12 : reg n6 a2 = w64 := by
    rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g5_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr, w5_64]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m6]; exact w5_64
  have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m6]; exact w5_74
  clear w5_74 w5_64 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_11 g5_10 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  -- 0x1512
  obtain ⟨n7, c7, u7⟩ := s6.block svCkd1512 E6.self svCkd1512_end
    ⟨trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem SV n7 0x1516 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have rb7 : ∀ q, reg n7 q = (runBlock svCkd1512 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
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
  have g7_9 : reg n7 (9 : Fin 32) = ckl := by
    rw [rb7, runBlock_reg _ _ _ (9 : Fin 32) s6.zero (by decide), g6_9]
  have g7_10 : reg n7 a0 = BitVec.ofNat 32 0xA := by
    rw [rb7, runBlock_reg _ _ _ a0 s6.zero (by decide), g6_10]
  have g7_11 : reg n7 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by
    rw [rb7, runBlock_reg _ _ _ a1 s6.zero (by decide), g6_11]
  have g7_12 : reg n7 a2 = w64 := by
    rw [rb7, runBlock_reg _ _ _ a2 s6.zero (by decide), g6_12]
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
  have g7_24 : reg n7 (24 : Fin 32) = p := by
    rw [rb7, runBlock_reg _ _ _ (24 : Fin 32) s6.zero (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = rp := by
    rw [rb7, runBlock_reg _ _ _ (25 : Fin 32) s6.zero (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by
    rw [rb7, runBlock_reg _ _ _ (26 : Fin 32) s6.zero (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = rl := by
    rw [rb7, runBlock_reg _ _ _ (27 : Fin 32) s6.zero (by decide), g6_27]
  have g7_13 : reg n7 a3 = aluEval .mulhu (w64) (BitVec.ofNat 32 0xA) := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svCkd1512, upd, ↓reduceIte]; rw [g6_12, g6_10] <;> rfl
  have keep_kk7 : SvKeepL B n0.mem n7.mem [] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m7]; exact w6_64
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m7]; exact w6_74
  clear w6_74 w6_64 g6_12 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_11 g6_10 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  -- 0x1516: lw
  obtain ⟨n8, d8, u8⟩ := s7.lw E7.self sv_at_1516 (off' := 0x1518) (by decide)
    (by rw [g7_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s8 : St n8.mem SV n8 0x1518 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
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
  have g8_10 : reg n8 a0 = BitVec.ofNat 32 0xA := by rw [u8.regs, upd_ne (by decide) (by decide), g7_10]
  have g8_11 : reg n8 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by rw [u8.regs, upd_ne (by decide) (by decide), g7_11]
  have g8_12 : reg n8 a2 = w64 := by rw [u8.regs, upd_ne (by decide) (by decide), g7_12]
  have g8_13 : reg n8 a3 = aluEval .mulhu (w64) (BitVec.ofNat 32 0xA) := by rw [u8.regs, upd_ne (by decide) (by decide), g7_13]
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
  have g8_9 : reg n8 (9 : Fin 32) = w74 := by
    rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g7_2, show B + 0x21A0 + 0x74 = B + 0x21A0 + BitVec.ofNat 32 0x74 by sv_addr, w7_74]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m8]; exact w7_64
  have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m8]; exact w7_74
  clear w7_74 w7_64 g7_13 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_12 g7_11 g7_10 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
  -- 0x1518
  obtain ⟨n9, c9, u9⟩ := s8.block svCkd1518 E8.self svCkd1518_end
    ⟨trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem SV n9 0x151C (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock svCkd1518 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
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
  have g9_8 : reg n9 (8 : Fin 32) = c := by
    rw [rb9, runBlock_reg _ _ _ (8 : Fin 32) s8.zero (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = w74 := by
    rw [rb9, runBlock_reg _ _ _ (9 : Fin 32) s8.zero (by decide), g8_9]
  have g9_10 : reg n9 a0 = BitVec.ofNat 32 0xA := by
    rw [rb9, runBlock_reg _ _ _ a0 s8.zero (by decide), g8_10]
  have g9_11 : reg n9 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by
    rw [rb9, runBlock_reg _ _ _ a1 s8.zero (by decide), g8_11]
  have g9_13 : reg n9 a3 = aluEval .mulhu (w64) (BitVec.ofNat 32 0xA) := by
    rw [rb9, runBlock_reg _ _ _ a3 s8.zero (by decide), g8_13]
  have g9_18 : reg n9 (18 : Fin 32) = out := by
    rw [rb9, runBlock_reg _ _ _ (18 : Fin 32) s8.zero (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by
    rw [rb9, runBlock_reg _ _ _ (19 : Fin 32) s8.zero (by decide), g8_19]
  have g9_20 : reg n9 (20 : Fin 32) = x20 := by
    rw [rb9, runBlock_reg _ _ _ (20 : Fin 32) s8.zero (by decide), g8_20]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by
    rw [rb9, runBlock_reg _ _ _ (21 : Fin 32) s8.zero (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = x22 := by
    rw [rb9, runBlock_reg _ _ _ (22 : Fin 32) s8.zero (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = x23 := by
    rw [rb9, runBlock_reg _ _ _ (23 : Fin 32) s8.zero (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = p := by
    rw [rb9, runBlock_reg _ _ _ (24 : Fin 32) s8.zero (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = rp := by
    rw [rb9, runBlock_reg _ _ _ (25 : Fin 32) s8.zero (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by
    rw [rb9, runBlock_reg _ _ _ (26 : Fin 32) s8.zero (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = rl := by
    rw [rb9, runBlock_reg _ _ _ (27 : Fin 32) s8.zero (by decide), g8_27]
  have g9_12 : reg n9 a2 = aluEval .mul (w74) (BitVec.ofNat 32 0xA) := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svCkd1518, upd, ↓reduceIte]; rw [g8_9, g8_10] <;> rfl
  have keep_kk9 : SvKeepL B n0.mem n9.mem [] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m9]; exact w8_64
  have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m9]; exact w8_74
  clear w8_74 w8_64 g8_9 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_13 g8_12 g8_11 g8_10 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
  -- 0x151C
  obtain ⟨n10, c10, u10⟩ := s9.block svCkd151c E9.self svCkd151c_end
    ⟨trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0x1520 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have rb10 : ∀ q, reg n10 q = (runBlock svCkd151c (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
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
  have g10_9 : reg n10 (9 : Fin 32) = w74 := by
    rw [rb10, runBlock_reg _ _ _ (9 : Fin 32) s9.zero (by decide), g9_9]
  have g10_10 : reg n10 a0 = BitVec.ofNat 32 0xA := by
    rw [rb10, runBlock_reg _ _ _ a0 s9.zero (by decide), g9_10]
  have g10_11 : reg n10 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by
    rw [rb10, runBlock_reg _ _ _ a1 s9.zero (by decide), g9_11]
  have g10_12 : reg n10 a2 = aluEval .mul (w74) (BitVec.ofNat 32 0xA) := by
    rw [rb10, runBlock_reg _ _ _ a2 s9.zero (by decide), g9_12]
  have g10_13 : reg n10 a3 = aluEval .mulhu (w64) (BitVec.ofNat 32 0xA) := by
    rw [rb10, runBlock_reg _ _ _ a3 s9.zero (by decide), g9_13]
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
  have g10_25 : reg n10 (25 : Fin 32) = rp := by
    rw [rb10, runBlock_reg _ _ _ (25 : Fin 32) s9.zero (by decide), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by
    rw [rb10, runBlock_reg _ _ _ (26 : Fin 32) s9.zero (by decide), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = rl := by
    rw [rb10, runBlock_reg _ _ _ (27 : Fin 32) s9.zero (by decide), g9_27]
  have g10_14 : reg n10 a4 = aluEval .mulhu (w74) (BitVec.ofNat 32 0xA) := by
    rw [rb10]; simp +decide only [runBlock, BInstr.run, svCkd151c, upd, ↓reduceIte]; rw [g9_9, g9_10] <;> rfl
  have keep_kk10 : SvKeepL B n0.mem n10.mem [] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m10]; exact w9_64
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m10]; exact w9_74
  clear w9_74 w9_64 g9_12 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_13 g9_11 g9_10 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  -- 0x1520
  obtain ⟨n11, c11, u11⟩ := s10.block svCkd1520 E10.self svCkd1520_end
    ⟨trivial, trivial⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have s11 : St n11.mem SV n11 0x1522 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have rb11 : ∀ q, reg n11 q = (runBlock svCkd1520 (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
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
  have g11_9 : reg n11 (9 : Fin 32) = w74 := by
    rw [rb11, runBlock_reg _ _ _ (9 : Fin 32) s10.zero (by decide), g10_9]
  have g11_10 : reg n11 a0 = BitVec.ofNat 32 0xA := by
    rw [rb11, runBlock_reg _ _ _ a0 s10.zero (by decide), g10_10]
  have g11_11 : reg n11 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by
    rw [rb11, runBlock_reg _ _ _ a1 s10.zero (by decide), g10_11]
  have g11_13 : reg n11 a3 = aluEval .mulhu (w64) (BitVec.ofNat 32 0xA) := by
    rw [rb11, runBlock_reg _ _ _ a3 s10.zero (by decide), g10_13]
  have g11_14 : reg n11 a4 = aluEval .mulhu (w74) (BitVec.ofNat 32 0xA) := by
    rw [rb11, runBlock_reg _ _ _ a4 s10.zero (by decide), g10_14]
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
  have g11_12 : reg n11 a2 = (aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)) := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, svCkd1520, upd, ↓reduceIte]; rw [g10_12, g10_13] <;> rfl
  have keep_kk11 : SvKeepL B n0.mem n11.mem [] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m11]; exact w10_64
  have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m11]; exact w10_74
  clear w10_74 w10_64 g10_14 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_13 g10_12 g10_11 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 rb10 s10 m10 u10 c10
  -- 0x1522
  obtain ⟨n12, c12, u12⟩ := s11.block svCkd1522 E11.self svCkd1522_end
    ⟨trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem SV n12 0x1526 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock svCkd1522 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
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
  have g12_8 : reg n12 (8 : Fin 32) = c := by
    rw [rb12, runBlock_reg _ _ _ (8 : Fin 32) s11.zero (by decide), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = w74 := by
    rw [rb12, runBlock_reg _ _ _ (9 : Fin 32) s11.zero (by decide), g11_9]
  have g12_10 : reg n12 a0 = BitVec.ofNat 32 0xA := by
    rw [rb12, runBlock_reg _ _ _ a0 s11.zero (by decide), g11_10]
  have g12_11 : reg n12 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by
    rw [rb12, runBlock_reg _ _ _ a1 s11.zero (by decide), g11_11]
  have g12_12 : reg n12 a2 = (aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)) := by
    rw [rb12, runBlock_reg _ _ _ a2 s11.zero (by decide), g11_12]
  have g12_14 : reg n12 a4 = aluEval .mulhu (w74) (BitVec.ofNat 32 0xA) := by
    rw [rb12, runBlock_reg _ _ _ a4 s11.zero (by decide), g11_14]
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
  have g12_24 : reg n12 (24 : Fin 32) = p := by
    rw [rb12, runBlock_reg _ _ _ (24 : Fin 32) s11.zero (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = rp := by
    rw [rb12, runBlock_reg _ _ _ (25 : Fin 32) s11.zero (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by
    rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = rl := by
    rw [rb12, runBlock_reg _ _ _ (27 : Fin 32) s11.zero (by decide), g11_27]
  have g12_13 : reg n12 a3 = aluEval .sltu ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)) := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svCkd1522, upd, ↓reduceIte]; rw [g11_12, g11_13] <;> rfl
  have keep_kk12 : SvKeepL B n0.mem n12.mem [] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m12]; exact w11_64
  have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m12]; exact w11_74
  clear w11_74 w11_64 g11_12 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_14 g11_13 g11_11 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 rb11 s11 m11 u11 c11
  -- 0x1526
  obtain ⟨n13, c13, u13⟩ := s12.block svCkd1526 E12.self svCkd1526_end
    ⟨trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem SV n13 0x152A (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock svCkd1526 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
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
  have g13_9 : reg n13 (9 : Fin 32) = w74 := by
    rw [rb13, runBlock_reg _ _ _ (9 : Fin 32) s12.zero (by decide), g12_9]
  have g13_10 : reg n13 a0 = BitVec.ofNat 32 0xA := by
    rw [rb13, runBlock_reg _ _ _ a0 s12.zero (by decide), g12_10]
  have g13_11 : reg n13 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by
    rw [rb13, runBlock_reg _ _ _ a1 s12.zero (by decide), g12_11]
  have g13_12 : reg n13 a2 = (aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)) := by
    rw [rb13, runBlock_reg _ _ _ a2 s12.zero (by decide), g12_12]
  have g13_13 : reg n13 a3 = aluEval .sltu ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)) := by
    rw [rb13, runBlock_reg _ _ _ a3 s12.zero (by decide), g12_13]
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
  have g13_25 : reg n13 (25 : Fin 32) = rp := by
    rw [rb13, runBlock_reg _ _ _ (25 : Fin 32) s12.zero (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by
    rw [rb13, runBlock_reg _ _ _ (26 : Fin 32) s12.zero (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = rl := by
    rw [rb13, runBlock_reg _ _ _ (27 : Fin 32) s12.zero (by decide), g12_27]
  have g13_14 : reg n13 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svCkd1526, upd, ↓reduceIte]; rw [g12_14] <;> rfl
  have keep_kk13 : SvKeepL B n0.mem n13.mem [] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m13]; exact w12_64
  have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m13]; exact w12_74
  clear w12_74 w12_64 g12_13 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_14 g12_12 g12_11 g12_10 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
  -- 0x152A
  obtain ⟨n14, c14, u14⟩ := s13.block svCkd152a E13.self svCkd152a_end
    ⟨trivial, trivial⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have s14 : St n14.mem SV n14 0x152C (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have rb14 : ∀ q, reg n14 q = (runBlock svCkd152a (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
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
  have g14_8 : reg n14 (8 : Fin 32) = c := by
    rw [rb14, runBlock_reg _ _ _ (8 : Fin 32) s13.zero (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = w74 := by
    rw [rb14, runBlock_reg _ _ _ (9 : Fin 32) s13.zero (by decide), g13_9]
  have g14_10 : reg n14 a0 = BitVec.ofNat 32 0xA := by
    rw [rb14, runBlock_reg _ _ _ a0 s13.zero (by decide), g13_10]
  have g14_11 : reg n14 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by
    rw [rb14, runBlock_reg _ _ _ a1 s13.zero (by decide), g13_11]
  have g14_12 : reg n14 a2 = (aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)) := by
    rw [rb14, runBlock_reg _ _ _ a2 s13.zero (by decide), g13_12]
  have g14_14 : reg n14 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by
    rw [rb14, runBlock_reg _ _ _ a4 s13.zero (by decide), g13_14]
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
  have g14_24 : reg n14 (24 : Fin 32) = p := by
    rw [rb14, runBlock_reg _ _ _ (24 : Fin 32) s13.zero (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = rp := by
    rw [rb14, runBlock_reg _ _ _ (25 : Fin 32) s13.zero (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by
    rw [rb14, runBlock_reg _ _ _ (26 : Fin 32) s13.zero (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = rl := by
    rw [rb14, runBlock_reg _ _ _ (27 : Fin 32) s13.zero (by decide), g13_27]
  have g14_13 : reg n14 a3 = (aluEval .sltu ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) ||| (aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA))) := by
    rw [rb14]; simp +decide only [runBlock, BInstr.run, svCkd152a, upd, ↓reduceIte]; rw [g13_13, g13_14] <;> rfl
  have keep_kk14 : SvKeepL B n0.mem n14.mem [] := by rw [m14]; exact keep_kk13
  clear keep_kk13
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m14]; exact w13_64
  have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m14]; exact w13_74
  clear w13_74 w13_64 g13_14 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_13 g13_12 g13_11 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
  by_cases hov1 : (aluEval .sltu ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) ||| (aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA))) = 0
  rotate_left
  · -- 0x152C: branch, taken
    obtain ⟨n15, d15, u15⟩ := s14.taken E14.self 0x1878 sv_at_152c
      (by decide) (by rw [g14_13, s14.zero]; exact br_bne_t hov1)
    have s15 : St n15.mem SV n15 0x1878 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
    have m15 : n15.mem = n14.mem := u15.mem
    have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
    have t15 : Steps n0 n15 := t14.trans (.single d15)
    have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
    have E15 : SvCode n15.mem := E14.fr F fr15
    have V15 : SvSaves B n15.mem v := V14.same m15
    have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, g14_2]
    have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, g14_3]
    have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, g14_4]
    have g15_8 : reg n15 (8 : Fin 32) = c := by rw [u15.regs, g14_8]
    have g15_9 : reg n15 (9 : Fin 32) = w74 := by rw [u15.regs, g14_9]
    have g15_10 : reg n15 a0 = BitVec.ofNat 32 0xA := by rw [u15.regs, g14_10]
    have g15_11 : reg n15 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by rw [u15.regs, g14_11]
    have g15_12 : reg n15 a2 = (aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)) := by rw [u15.regs, g14_12]
    have g15_13 : reg n15 a3 = (aluEval .sltu ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) ||| (aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA))) := by rw [u15.regs, g14_13]
    have g15_14 : reg n15 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by rw [u15.regs, g14_14]
    have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, g14_18]
    have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, g14_19]
    have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [u15.regs, g14_20]
    have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, g14_21]
    have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [u15.regs, g14_22]
    have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [u15.regs, g14_23]
    have g15_24 : reg n15 (24 : Fin 32) = p := by rw [u15.regs, g14_24]
    have g15_25 : reg n15 (25 : Fin 32) = rp := by rw [u15.regs, g14_25]
    have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, g14_26]
    have g15_27 : reg n15 (27 : Fin 32) = rl := by rw [u15.regs, g14_27]
    have keep_kk15 : SvKeepL B n0.mem n15.mem [] := by rw [m15]; exact keep_kk14
    clear keep_kk14
    have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m15]; exact w14_64
    have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m15]; exact w14_74
    clear w14_74 w14_64 g14_13 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_14 g14_12 g14_11 g14_10 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
    -- 0x1878
    obtain ⟨n16, c16, u16⟩ := s15.block svCkd1878 E15.self svCkd1878_end
      ⟨trivial, trivial⟩
    have m16 : n16.mem = n15.mem := u16.mem
    have s16 : St n16.mem SV n16 0x187A (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
    have rb16 : ∀ q, reg n16 q = (runBlock svCkd1878 (n15.mem, reg n15)).2 q := fun q => by rw [u16.regs]
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
    have g16_8 : reg n16 (8 : Fin 32) = c := by
      rw [rb16, runBlock_reg _ _ _ (8 : Fin 32) s15.zero (by decide), g15_8]
    have g16_9 : reg n16 (9 : Fin 32) = w74 := by
      rw [rb16, runBlock_reg _ _ _ (9 : Fin 32) s15.zero (by decide), g15_9]
    have g16_10 : reg n16 a0 = BitVec.ofNat 32 0xA := by
      rw [rb16, runBlock_reg _ _ _ a0 s15.zero (by decide), g15_10]
    have g16_11 : reg n16 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by
      rw [rb16, runBlock_reg _ _ _ a1 s15.zero (by decide), g15_11]
    have g16_12 : reg n16 a2 = (aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)) := by
      rw [rb16, runBlock_reg _ _ _ a2 s15.zero (by decide), g15_12]
    have g16_13 : reg n16 a3 = (aluEval .sltu ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) ||| (aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA))) := by
      rw [rb16, runBlock_reg _ _ _ a3 s15.zero (by decide), g15_13]
    have g16_14 : reg n16 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by
      rw [rb16, runBlock_reg _ _ _ a4 s15.zero (by decide), g15_14]
    have g16_18 : reg n16 (18 : Fin 32) = out := by
      rw [rb16, runBlock_reg _ _ _ (18 : Fin 32) s15.zero (by decide), g15_18]
    have g16_19 : reg n16 (19 : Fin 32) = bp := by
      rw [rb16, runBlock_reg _ _ _ (19 : Fin 32) s15.zero (by decide), g15_19]
    have g16_20 : reg n16 (20 : Fin 32) = x20 := by
      rw [rb16, runBlock_reg _ _ _ (20 : Fin 32) s15.zero (by decide), g15_20]
    have g16_21 : reg n16 (21 : Fin 32) = x21 := by
      rw [rb16, runBlock_reg _ _ _ (21 : Fin 32) s15.zero (by decide), g15_21]
    have g16_22 : reg n16 (22 : Fin 32) = x22 := by
      rw [rb16, runBlock_reg _ _ _ (22 : Fin 32) s15.zero (by decide), g15_22]
    have g16_23 : reg n16 (23 : Fin 32) = x23 := by
      rw [rb16, runBlock_reg _ _ _ (23 : Fin 32) s15.zero (by decide), g15_23]
    have g16_24 : reg n16 (24 : Fin 32) = p := by
      rw [rb16, runBlock_reg _ _ _ (24 : Fin 32) s15.zero (by decide), g15_24]
    have g16_26 : reg n16 (26 : Fin 32) = x26 := by
      rw [rb16, runBlock_reg _ _ _ (26 : Fin 32) s15.zero (by decide), g15_26]
    have g16_27 : reg n16 (27 : Fin 32) = rl := by
      rw [rb16, runBlock_reg _ _ _ (27 : Fin 32) s15.zero (by decide), g15_27]
    have g16_25 : reg n16 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb16]; simp +decide only [runBlock, BInstr.run, svCkd1878, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g15_2, g15_3, g15_4, g15_8, g15_9, g15_10, g15_11, g15_12, g15_13, g15_14, g15_18, g15_19, g15_20, g15_21, g15_22, g15_23, g15_24, g15_25, g15_26, g15_27, s15.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk16 : SvKeepL B n0.mem n16.mem [] := by rw [m16]; exact keep_kk15
    clear keep_kk15
    have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m16]; exact w15_64
    have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m16]; exact w15_74
    clear w15_74 w15_64 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_14 g15_13 g15_12 g15_11 g15_10 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
    -- 0x187A: j
    obtain ⟨n17, d17, u17⟩ := s16.jump E16.self sv_at_187a (off' := 0x1882) (by decide)
      (by rw [s16.pc]; decide)
    have s17 : St n17.mem SV n17 0x1882 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
    have m17 : n17.mem = n16.mem := u17.mem
    have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
    have t17 : Steps n0 n17 := t16.trans (.single d17)
    have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
    have E17 : SvCode n17.mem := E16.fr F fr17
    have V17 : SvSaves B n17.mem v := V16.same m17
    have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, g16_2]
    have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, g16_3]
    have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, g16_4]
    have g17_8 : reg n17 (8 : Fin 32) = c := by rw [u17.regs, g16_8]
    have g17_9 : reg n17 (9 : Fin 32) = w74 := by rw [u17.regs, g16_9]
    have g17_10 : reg n17 a0 = BitVec.ofNat 32 0xA := by rw [u17.regs, g16_10]
    have g17_11 : reg n17 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by rw [u17.regs, g16_11]
    have g17_12 : reg n17 a2 = (aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)) := by rw [u17.regs, g16_12]
    have g17_13 : reg n17 a3 = (aluEval .sltu ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) ||| (aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA))) := by rw [u17.regs, g16_13]
    have g17_14 : reg n17 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by rw [u17.regs, g16_14]
    have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, g16_18]
    have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, g16_19]
    have g17_20 : reg n17 (20 : Fin 32) = x20 := by rw [u17.regs, g16_20]
    have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [u17.regs, g16_21]
    have g17_22 : reg n17 (22 : Fin 32) = x22 := by rw [u17.regs, g16_22]
    have g17_23 : reg n17 (23 : Fin 32) = x23 := by rw [u17.regs, g16_23]
    have g17_24 : reg n17 (24 : Fin 32) = p := by rw [u17.regs, g16_24]
    have g17_25 : reg n17 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u17.regs, g16_25]
    have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [u17.regs, g16_26]
    have g17_27 : reg n17 (27 : Fin 32) = rl := by rw [u17.regs, g16_27]
    have keep_kk17 : SvKeepL B n0.mem n17.mem [] := by rw [m17]; exact keep_kk16
    clear keep_kk16
    have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m17]; exact w16_64
    have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m17]; exact w16_74
    clear w16_74 w16_64 g16_25 g16_27 g16_26 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_14 g16_13 g16_12 g16_11 g16_10 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 rb16 s16 m16 u16 c16
    exact .inl ⟨(fun ⟨h0', h1', _⟩ => by exact hov1 h1'), sv_fail_1882 F E17 s17 t17 (fun x hx => (fR17 x hx).trans (fM x hx).symm) V17 hret g17_2 g17_18 hO g17_3 g17_4⟩
  -- 0x152C: branch, not taken
  obtain ⟨n15, d15, u15⟩ := s14.notTaken E14.self 0x1530 sv_at_152c
    (by decide) (by rw [g14_13, s14.zero]; exact br_bne_f hov1)
  have s15 : St n15.mem SV n15 0x1530 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = c := by rw [u15.regs, g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = w74 := by rw [u15.regs, g14_9]
  have g15_10 : reg n15 a0 = BitVec.ofNat 32 0xA := by rw [u15.regs, g14_10]
  have g15_11 : reg n15 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by rw [u15.regs, g14_11]
  have g15_12 : reg n15 a2 = (aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)) := by rw [u15.regs, g14_12]
  have g15_13 : reg n15 a3 = (aluEval .sltu ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) ||| (aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA))) := by rw [u15.regs, g14_13]
  have g15_14 : reg n15 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by rw [u15.regs, g14_14]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [u15.regs, g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [u15.regs, g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = x23 := by rw [u15.regs, g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = p := by rw [u15.regs, g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = rp := by rw [u15.regs, g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = rl := by rw [u15.regs, g14_27]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m15]; exact w14_64
  have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m15]; exact w14_74
  clear w14_74 w14_64 g14_13 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_14 g14_12 g14_11 g14_10 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 rb14 s14 m14 u14 c14
  -- 0x1530: lw
  obtain ⟨n16, d16, u16⟩ := s15.lw E15.self sv_at_1530 (off' := 0x1532) (by decide)
    (by rw [g15_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s16 : St n16.mem SV n16 0x1532 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans (.single d16)
  have fR16 : ∀ x, SvR B x → n16.mem x = M0 x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = c := by rw [u16.regs, upd_ne (by decide) (by decide), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = w74 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_9]
  have g16_10 : reg n16 a0 = BitVec.ofNat 32 0xA := by rw [u16.regs, upd_ne (by decide) (by decide), g15_10]
  have g16_11 : reg n16 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by rw [u16.regs, upd_ne (by decide) (by decide), g15_11]
  have g16_12 : reg n16 a2 = (aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_12]
  have g16_14 : reg n16 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by rw [u16.regs, upd_ne (by decide) (by decide), g15_14]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, upd_ne (by decide) (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = x20 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = x22 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = x23 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = p := by rw [u16.regs, upd_ne (by decide) (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = rp := by rw [u16.regs, upd_ne (by decide) (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by rw [u16.regs, upd_ne (by decide) (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = rl := by rw [u16.regs, upd_ne (by decide) (by decide), g15_27]
  have g16_13 : reg n16 a3 = w64 := by
    rw [u16.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g15_2, show B + 0x21A0 + 0x64 = B + 0x21A0 + BitVec.ofNat 32 0x64 by sv_addr, w15_64]
  have keep_kk16 : SvKeepL B n0.mem n16.mem [] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m16]; exact w15_64
  have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m16]; exact w15_74
  clear w15_74 w15_64 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_14 g15_13 g15_12 g15_11 g15_10 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
  -- 0x1532
  obtain ⟨n17, c17, u17⟩ := s16.block svCkd1532 E16.self svCkd1532_end
    ⟨trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem SV n17 0x1536 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock svCkd1532 (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
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
  have g17_9 : reg n17 (9 : Fin 32) = w74 := by
    rw [rb17, runBlock_reg _ _ _ (9 : Fin 32) s16.zero (by decide), g16_9]
  have g17_10 : reg n17 a0 = BitVec.ofNat 32 0xA := by
    rw [rb17, runBlock_reg _ _ _ a0 s16.zero (by decide), g16_10]
  have g17_11 : reg n17 a1 = (((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF := by
    rw [rb17, runBlock_reg _ _ _ a1 s16.zero (by decide), g16_11]
  have g17_12 : reg n17 a2 = (aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)) := by
    rw [rb17, runBlock_reg _ _ _ a2 s16.zero (by decide), g16_12]
  have g17_14 : reg n17 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by
    rw [rb17, runBlock_reg _ _ _ a4 s16.zero (by decide), g16_14]
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
  have g17_13 : reg n17 a3 = aluEval .mul (w64) (BitVec.ofNat 32 0xA) := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svCkd1532, upd, ↓reduceIte]; rw [g16_13, g16_10] <;> rfl
  have keep_kk17 : SvKeepL B n0.mem n17.mem [] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m17]; exact w16_64
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m17]; exact w16_74
  clear w16_74 w16_64 g16_13 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_14 g16_12 g16_11 g16_10 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
  -- 0x1536
  obtain ⟨n18, c18, u18⟩ := s17.block svCkd1536 E17.self svCkd1536_end
    ⟨trivial, trivial⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have s18 : St n18.mem SV n18 0x1538 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have rb18 : ∀ q, reg n18 q = (runBlock svCkd1536 (n17.mem, reg n17)).2 q := fun q => by rw [u18.regs]
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
  have g18_8 : reg n18 (8 : Fin 32) = c := by
    rw [rb18, runBlock_reg _ _ _ (8 : Fin 32) s17.zero (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = w74 := by
    rw [rb18, runBlock_reg _ _ _ (9 : Fin 32) s17.zero (by decide), g17_9]
  have g18_10 : reg n18 a0 = BitVec.ofNat 32 0xA := by
    rw [rb18, runBlock_reg _ _ _ a0 s17.zero (by decide), g17_10]
  have g18_12 : reg n18 a2 = (aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)) := by
    rw [rb18, runBlock_reg _ _ _ a2 s17.zero (by decide), g17_12]
  have g18_13 : reg n18 a3 = aluEval .mul (w64) (BitVec.ofNat 32 0xA) := by
    rw [rb18, runBlock_reg _ _ _ a3 s17.zero (by decide), g17_13]
  have g18_14 : reg n18 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by
    rw [rb18, runBlock_reg _ _ _ a4 s17.zero (by decide), g17_14]
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
  have g18_24 : reg n18 (24 : Fin 32) = p := by
    rw [rb18, runBlock_reg _ _ _ (24 : Fin 32) s17.zero (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = rp := by
    rw [rb18, runBlock_reg _ _ _ (25 : Fin 32) s17.zero (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by
    rw [rb18, runBlock_reg _ _ _ (26 : Fin 32) s17.zero (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = rl := by
    rw [rb18, runBlock_reg _ _ _ (27 : Fin 32) s17.zero (by decide), g17_27]
  have g18_11 : reg n18 a1 = ((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) := by
    rw [rb18]; simp +decide only [runBlock, BInstr.run, svCkd1536, upd, ↓reduceIte]; rw [g17_11, g17_13] <;> rfl
  have keep_kk18 : SvKeepL B n0.mem n18.mem [] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m18]; exact w17_64
  have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m18]; exact w17_74
  clear w17_74 w17_64 g17_13 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_14 g17_12 g17_11 g17_10 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
  -- 0x1538: sw
  obtain ⟨n19, d19, s19, fr19, K19, W19, rg19⟩ := sv_sw F E18 s18 sv_at_1538 (off' := 0x153A) (c := 0x64)
    (by decide) (by rw [g18_2]; sv_addr) (by decide) (by decide)
  have t19 : Steps n0 n19 := t18.trans d19
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.keep K19 (by decide)
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [rg19 sp, g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg19 (3 : Fin 32), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg19 (4 : Fin 32), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = c := by rw [rg19 (8 : Fin 32), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = w74 := by rw [rg19 (9 : Fin 32), g18_9]
  have g19_10 : reg n19 a0 = BitVec.ofNat 32 0xA := by rw [rg19 a0, g18_10]
  have g19_11 : reg n19 a1 = ((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) := by rw [rg19 a1, g18_11]
  have g19_12 : reg n19 a2 = (aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)) := by rw [rg19 a2, g18_12]
  have g19_13 : reg n19 a3 = aluEval .mul (w64) (BitVec.ofNat 32 0xA) := by rw [rg19 a3, g18_13]
  have g19_14 : reg n19 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by rw [rg19 a4, g18_14]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [rg19 (18 : Fin 32), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [rg19 (19 : Fin 32), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = x20 := by rw [rg19 (20 : Fin 32), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [rg19 (21 : Fin 32), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [rg19 (22 : Fin 32), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = x23 := by rw [rg19 (23 : Fin 32), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = p := by rw [rg19 (24 : Fin 32), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = rp := by rw [rg19 (25 : Fin 32), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [rg19 (26 : Fin 32), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = rl := by rw [rg19 (27 : Fin 32), g18_27]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [(0x64, 0x4)] := keep_kk18.trans K19.toL
  clear keep_kk18
  have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K19.w32 (by decide) (by decide)).trans w18_74
  have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = ((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) := by rw [W19, g18_11]
  clear w18_74 w18_64 g18_11 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_14 g18_13 g18_12 g18_10 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 rb18 s18 m18 u18 c18
  -- 0x153A
  obtain ⟨n20, c20, u20⟩ := s19.block svCkd153a E19.self svCkd153a_end
    ⟨trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem SV n20 0x153E (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock svCkd153a (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
  have g20_8 : reg n20 (8 : Fin 32) = c := by
    rw [rb20, runBlock_reg _ _ _ (8 : Fin 32) s19.zero (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = w74 := by
    rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
  have g20_10 : reg n20 a0 = BitVec.ofNat 32 0xA := by
    rw [rb20, runBlock_reg _ _ _ a0 s19.zero (by decide), g19_10]
  have g20_12 : reg n20 a2 = (aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)) := by
    rw [rb20, runBlock_reg _ _ _ a2 s19.zero (by decide), g19_12]
  have g20_13 : reg n20 a3 = aluEval .mul (w64) (BitVec.ofNat 32 0xA) := by
    rw [rb20, runBlock_reg _ _ _ a3 s19.zero (by decide), g19_13]
  have g20_14 : reg n20 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by
    rw [rb20, runBlock_reg _ _ _ a4 s19.zero (by decide), g19_14]
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
  have g20_24 : reg n20 (24 : Fin 32) = p := by
    rw [rb20, runBlock_reg _ _ _ (24 : Fin 32) s19.zero (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = rp := by
    rw [rb20, runBlock_reg _ _ _ (25 : Fin 32) s19.zero (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by
    rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = rl := by
    rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
  have g20_11 : reg n20 a1 = aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svCkd153a, upd, ↓reduceIte]; rw [g19_11, g19_13] <;> rfl
  have keep_kk20 : SvKeepL B n0.mem n20.mem [(0x64, 0x4)] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = ((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) := by rw [m20]; exact w19_64
  have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m20]; exact w19_74
  clear w19_64 w19_74 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_14 g19_13 g19_12 g19_11 g19_10 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 rg19 W19 K19 fr19 s19 d19
  -- 0x153E
  obtain ⟨n21, c21, u21⟩ := s20.block svCkd153e E20.self svCkd153e_end
    ⟨trivial, trivial⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have s21 : St n21.mem SV n21 0x1542 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have rb21 : ∀ q, reg n21 q = (runBlock svCkd153e (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
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
  have g21_8 : reg n21 (8 : Fin 32) = c := by
    rw [rb21, runBlock_reg _ _ _ (8 : Fin 32) s20.zero (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = w74 := by
    rw [rb21, runBlock_reg _ _ _ (9 : Fin 32) s20.zero (by decide), g20_9]
  have g21_10 : reg n21 a0 = BitVec.ofNat 32 0xA := by
    rw [rb21, runBlock_reg _ _ _ a0 s20.zero (by decide), g20_10]
  have g21_11 : reg n21 a1 = aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) := by
    rw [rb21, runBlock_reg _ _ _ a1 s20.zero (by decide), g20_11]
  have g21_12 : reg n21 a2 = (aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)) := by
    rw [rb21, runBlock_reg _ _ _ a2 s20.zero (by decide), g20_12]
  have g21_14 : reg n21 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by
    rw [rb21, runBlock_reg _ _ _ a4 s20.zero (by decide), g20_14]
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
  have g21_24 : reg n21 (24 : Fin 32) = p := by
    rw [rb21, runBlock_reg _ _ _ (24 : Fin 32) s20.zero (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = rp := by
    rw [rb21, runBlock_reg _ _ _ (25 : Fin 32) s20.zero (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by
    rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = rl := by
    rw [rb21, runBlock_reg _ _ _ (27 : Fin 32) s20.zero (by decide), g20_27]
  have g21_13 : reg n21 a3 = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svCkd153e, upd, ↓reduceIte]; rw [g20_12, g20_11] <;> rfl
  have keep_kk21 : SvKeepL B n0.mem n21.mem [(0x64, 0x4)] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = ((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) := by rw [m21]; exact w20_64
  have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m21]; exact w20_74
  clear w20_74 w20_64 g20_11 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_14 g20_13 g20_12 g20_10 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  -- 0x1542: sw
  obtain ⟨n22, d22, s22, fr22, K22, W22, rg22⟩ := sv_sw F E21 s21 sv_at_1542 (off' := 0x1544) (c := 0x74)
    (by decide) (by rw [g21_2]; sv_addr) (by decide) (by decide)
  have t22 : Steps n0 n22 := t21.trans d22
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.keep K22 (by decide)
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [rg22 sp, g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg22 (3 : Fin 32), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg22 (4 : Fin 32), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = c := by rw [rg22 (8 : Fin 32), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = w74 := by rw [rg22 (9 : Fin 32), g21_9]
  have g22_10 : reg n22 a0 = BitVec.ofNat 32 0xA := by rw [rg22 a0, g21_10]
  have g22_11 : reg n22 a1 = aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) := by rw [rg22 a1, g21_11]
  have g22_12 : reg n22 a2 = (aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)) := by rw [rg22 a2, g21_12]
  have g22_13 : reg n22 a3 = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by rw [rg22 a3, g21_13]
  have g22_14 : reg n22 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by rw [rg22 a4, g21_14]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [rg22 (18 : Fin 32), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [rg22 (19 : Fin 32), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [rg22 (20 : Fin 32), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [rg22 (21 : Fin 32), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [rg22 (22 : Fin 32), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = x23 := by rw [rg22 (23 : Fin 32), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = p := by rw [rg22 (24 : Fin 32), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = rp := by rw [rg22 (25 : Fin 32), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [rg22 (26 : Fin 32), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = rl := by rw [rg22 (27 : Fin 32), g21_27]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [(0x64, 0x4), (0x74, 0x4)] := keep_kk21.trans K22.toL
  clear keep_kk21
  have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = ((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) := (K22.w32 (by decide) (by decide)).trans w21_64
  have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by rw [W22, g21_13]
  clear w21_74 w21_64 g21_13 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_14 g21_12 g21_11 g21_10 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
  -- 0x1544
  obtain ⟨n23, c23, u23⟩ := s22.block svCkd1544 E22.self svCkd1544_end
    ⟨trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem SV n23 0x1548 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock svCkd1544 (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
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
  have g23_8 : reg n23 (8 : Fin 32) = c := by
    rw [rb23, runBlock_reg _ _ _ (8 : Fin 32) s22.zero (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = w74 := by
    rw [rb23, runBlock_reg _ _ _ (9 : Fin 32) s22.zero (by decide), g22_9]
  have g23_10 : reg n23 a0 = BitVec.ofNat 32 0xA := by
    rw [rb23, runBlock_reg _ _ _ a0 s22.zero (by decide), g22_10]
  have g23_11 : reg n23 a1 = aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) := by
    rw [rb23, runBlock_reg _ _ _ a1 s22.zero (by decide), g22_11]
  have g23_13 : reg n23 a3 = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by
    rw [rb23, runBlock_reg _ _ _ a3 s22.zero (by decide), g22_13]
  have g23_14 : reg n23 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by
    rw [rb23, runBlock_reg _ _ _ a4 s22.zero (by decide), g22_14]
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
  have g23_24 : reg n23 (24 : Fin 32) = p := by
    rw [rb23, runBlock_reg _ _ _ (24 : Fin 32) s22.zero (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = rp := by
    rw [rb23, runBlock_reg _ _ _ (25 : Fin 32) s22.zero (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by
    rw [rb23, runBlock_reg _ _ _ (26 : Fin 32) s22.zero (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = rl := by
    rw [rb23, runBlock_reg _ _ _ (27 : Fin 32) s22.zero (by decide), g22_27]
  have g23_12 : reg n23 a2 = aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svCkd1544, upd, ↓reduceIte]; rw [g22_13, g22_12] <;> rfl
  have keep_kk23 : SvKeepL B n0.mem n23.mem [(0x64, 0x4), (0x74, 0x4)] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = ((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) := by rw [m23]; exact w22_64
  have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by rw [m23]; exact w22_74
  clear w22_74 w22_64 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_14 g22_13 g22_12 g22_11 g22_10 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 rg22 W22 K22 fr22 s22 d22
  -- 0x1548
  obtain ⟨n24, c24, u24⟩ := s23.block svCkd1548 E23.self svCkd1548_end
    ⟨trivial, trivial⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have s24 : St n24.mem SV n24 0x154A (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have rb24 : ∀ q, reg n24 q = (runBlock svCkd1548 (n23.mem, reg n23)).2 q := fun q => by rw [u24.regs]
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
  have g24_8 : reg n24 (8 : Fin 32) = c := by
    rw [rb24, runBlock_reg _ _ _ (8 : Fin 32) s23.zero (by decide), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = w74 := by
    rw [rb24, runBlock_reg _ _ _ (9 : Fin 32) s23.zero (by decide), g23_9]
  have g24_10 : reg n24 a0 = BitVec.ofNat 32 0xA := by
    rw [rb24, runBlock_reg _ _ _ a0 s23.zero (by decide), g23_10]
  have g24_12 : reg n24 a2 = aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) := by
    rw [rb24, runBlock_reg _ _ _ a2 s23.zero (by decide), g23_12]
  have g24_13 : reg n24 a3 = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by
    rw [rb24, runBlock_reg _ _ _ a3 s23.zero (by decide), g23_13]
  have g24_14 : reg n24 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by
    rw [rb24, runBlock_reg _ _ _ a4 s23.zero (by decide), g23_14]
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
  have g24_24 : reg n24 (24 : Fin 32) = p := by
    rw [rb24, runBlock_reg _ _ _ (24 : Fin 32) s23.zero (by decide), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = rp := by
    rw [rb24, runBlock_reg _ _ _ (25 : Fin 32) s23.zero (by decide), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by
    rw [rb24, runBlock_reg _ _ _ (26 : Fin 32) s23.zero (by decide), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = rl := by
    rw [rb24, runBlock_reg _ _ _ (27 : Fin 32) s23.zero (by decide), g23_27]
  have g24_11 : reg n24 a1 = (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) &&& (aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)))) := by
    rw [rb24]; simp +decide only [runBlock, BInstr.run, svCkd1548, upd, ↓reduceIte]; rw [g23_11, g23_12] <;> rfl
  have keep_kk24 : SvKeepL B n0.mem n24.mem [(0x64, 0x4), (0x74, 0x4)] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = ((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) := by rw [m24]; exact w23_64
  have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by rw [m24]; exact w23_74
  clear w23_74 w23_64 g23_12 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_14 g23_13 g23_11 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
  -- 0x154A
  obtain ⟨n25, c25, u25⟩ := s24.block svCkd154a E24.self svCkd154a_end
    ⟨trivial, trivial⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have s25 : St n25.mem SV n25 0x154C (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have rb25 : ∀ q, reg n25 q = (runBlock svCkd154a (n24.mem, reg n24)).2 q := fun q => by rw [u25.regs]
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
  have g25_8 : reg n25 (8 : Fin 32) = c := by
    rw [rb25, runBlock_reg _ _ _ (8 : Fin 32) s24.zero (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = w74 := by
    rw [rb25, runBlock_reg _ _ _ (9 : Fin 32) s24.zero (by decide), g24_9]
  have g25_10 : reg n25 a0 = BitVec.ofNat 32 0xA := by
    rw [rb25, runBlock_reg _ _ _ a0 s24.zero (by decide), g24_10]
  have g25_11 : reg n25 a1 = (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) &&& (aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)))) := by
    rw [rb25, runBlock_reg _ _ _ a1 s24.zero (by decide), g24_11]
  have g25_12 : reg n25 a2 = aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) := by
    rw [rb25, runBlock_reg _ _ _ a2 s24.zero (by decide), g24_12]
  have g25_13 : reg n25 a3 = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by
    rw [rb25, runBlock_reg _ _ _ a3 s24.zero (by decide), g24_13]
  have g25_14 : reg n25 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by
    rw [rb25, runBlock_reg _ _ _ a4 s24.zero (by decide), g24_14]
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
  have g25_25 : reg n25 (25 : Fin 32) = rp := by
    rw [rb25, runBlock_reg _ _ _ (25 : Fin 32) s24.zero (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by
    rw [rb25, runBlock_reg _ _ _ (26 : Fin 32) s24.zero (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = rl := by
    rw [rb25, runBlock_reg _ _ _ (27 : Fin 32) s24.zero (by decide), g24_27]
  have g25_24 : reg n25 (24 : Fin 32) = (p) + BitVec.ofNat 32 0x1 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svCkd154a, upd, ↓reduceIte]; rw [g24_24] <;> rfl
  have keep_kk25 : SvKeepL B n0.mem n25.mem [(0x64, 0x4), (0x74, 0x4)] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = ((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) := by rw [m25]; exact w24_64
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by rw [m25]; exact w24_74
  clear w24_74 w24_64 g24_11 g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_14 g24_13 g24_12 g24_10 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 rb24 s24 m24 u24 c24
  -- 0x154C
  obtain ⟨n26, c26, u26⟩ := s25.block svCkd154c E25.self svCkd154c_end
    ⟨trivial, trivial⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have s26 : St n26.mem SV n26 0x154E (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have rb26 : ∀ q, reg n26 q = (runBlock svCkd154c (n25.mem, reg n25)).2 q := fun q => by rw [u26.regs]
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
  have g26_9 : reg n26 (9 : Fin 32) = w74 := by
    rw [rb26, runBlock_reg _ _ _ (9 : Fin 32) s25.zero (by decide), g25_9]
  have g26_10 : reg n26 a0 = BitVec.ofNat 32 0xA := by
    rw [rb26, runBlock_reg _ _ _ a0 s25.zero (by decide), g25_10]
  have g26_11 : reg n26 a1 = (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) &&& (aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)))) := by
    rw [rb26, runBlock_reg _ _ _ a1 s25.zero (by decide), g25_11]
  have g26_12 : reg n26 a2 = aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) := by
    rw [rb26, runBlock_reg _ _ _ a2 s25.zero (by decide), g25_12]
  have g26_13 : reg n26 a3 = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by
    rw [rb26, runBlock_reg _ _ _ a3 s25.zero (by decide), g25_13]
  have g26_14 : reg n26 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by
    rw [rb26, runBlock_reg _ _ _ a4 s25.zero (by decide), g25_14]
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
  have g26_24 : reg n26 (24 : Fin 32) = (p) + BitVec.ofNat 32 0x1 := by
    rw [rb26, runBlock_reg _ _ _ (24 : Fin 32) s25.zero (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = rp := by
    rw [rb26, runBlock_reg _ _ _ (25 : Fin 32) s25.zero (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by
    rw [rb26, runBlock_reg _ _ _ (26 : Fin 32) s25.zero (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = rl := by
    rw [rb26, runBlock_reg _ _ _ (27 : Fin 32) s25.zero (by decide), g25_27]
  have g26_8 : reg n26 (8 : Fin 32) = (c) + BitVec.ofNat 32 0xFFFFFFFF := by
    rw [rb26]; simp +decide only [runBlock, BInstr.run, svCkd154c, upd, ↓reduceIte]; rw [g25_8] <;> rfl
  have keep_kk26 : SvKeepL B n0.mem n26.mem [(0x64, 0x4), (0x74, 0x4)] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = ((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) := by rw [m26]; exact w25_64
  have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by rw [m26]; exact w25_74
  clear w25_74 w25_64 g25_24 g25_27 g25_26 g25_25 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_14 g25_13 g25_12 g25_11 g25_10 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
  by_cases hov2 : (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) &&& (aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)))) = 0
  rotate_left
  · -- 0x154E: branch, not taken
    obtain ⟨n27, d27, u27⟩ := s26.notTaken E26.self 0x1550 sv_at_154e
      (by decide) (by rw [g26_11, s26.zero]; exact br_beq_f hov2)
    have s27 : St n27.mem SV n27 0x1550 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
    have m27 : n27.mem = n26.mem := u27.mem
    have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
    have t27 : Steps n0 n27 := t26.trans (.single d27)
    have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
    have E27 : SvCode n27.mem := E26.fr F fr27
    have V27 : SvSaves B n27.mem v := V26.same m27
    have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, g26_2]
    have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, g26_3]
    have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, g26_4]
    have g27_8 : reg n27 (8 : Fin 32) = (c) + BitVec.ofNat 32 0xFFFFFFFF := by rw [u27.regs, g26_8]
    have g27_9 : reg n27 (9 : Fin 32) = w74 := by rw [u27.regs, g26_9]
    have g27_10 : reg n27 a0 = BitVec.ofNat 32 0xA := by rw [u27.regs, g26_10]
    have g27_11 : reg n27 a1 = (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) &&& (aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)))) := by rw [u27.regs, g26_11]
    have g27_12 : reg n27 a2 = aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) := by rw [u27.regs, g26_12]
    have g27_13 : reg n27 a3 = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by rw [u27.regs, g26_13]
    have g27_14 : reg n27 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by rw [u27.regs, g26_14]
    have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, g26_18]
    have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, g26_19]
    have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [u27.regs, g26_20]
    have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [u27.regs, g26_21]
    have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [u27.regs, g26_22]
    have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [u27.regs, g26_23]
    have g27_24 : reg n27 (24 : Fin 32) = (p) + BitVec.ofNat 32 0x1 := by rw [u27.regs, g26_24]
    have g27_25 : reg n27 (25 : Fin 32) = rp := by rw [u27.regs, g26_25]
    have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, g26_26]
    have g27_27 : reg n27 (27 : Fin 32) = rl := by rw [u27.regs, g26_27]
    have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x64, 0x4), (0x74, 0x4)] := by rw [m27]; exact keep_kk26
    clear keep_kk26
    have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = ((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) := by rw [m27]; exact w26_64
    have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by rw [m27]; exact w26_74
    clear w26_74 w26_64 g26_8 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_14 g26_13 g26_12 g26_11 g26_10 g26_9 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 rb26 s26 m26 u26 c26
    -- 0x1550: j
    obtain ⟨n28, d28, u28⟩ := s27.jump E27.self sv_at_1550 (off' := 0x1878) (by decide)
      (by rw [s27.pc]; decide)
    have s28 : St n28.mem SV n28 0x1878 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
    have m28 : n28.mem = n27.mem := u28.mem
    have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
    have t28 : Steps n0 n28 := t27.trans (.single d28)
    have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
    have E28 : SvCode n28.mem := E27.fr F fr28
    have V28 : SvSaves B n28.mem v := V27.same m28
    have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, g27_2]
    have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, g27_3]
    have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, g27_4]
    have g28_8 : reg n28 (8 : Fin 32) = (c) + BitVec.ofNat 32 0xFFFFFFFF := by rw [u28.regs, g27_8]
    have g28_9 : reg n28 (9 : Fin 32) = w74 := by rw [u28.regs, g27_9]
    have g28_10 : reg n28 a0 = BitVec.ofNat 32 0xA := by rw [u28.regs, g27_10]
    have g28_11 : reg n28 a1 = (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) &&& (aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)))) := by rw [u28.regs, g27_11]
    have g28_12 : reg n28 a2 = aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) := by rw [u28.regs, g27_12]
    have g28_13 : reg n28 a3 = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by rw [u28.regs, g27_13]
    have g28_14 : reg n28 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by rw [u28.regs, g27_14]
    have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, g27_18]
    have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, g27_19]
    have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [u28.regs, g27_20]
    have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [u28.regs, g27_21]
    have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [u28.regs, g27_22]
    have g28_23 : reg n28 (23 : Fin 32) = x23 := by rw [u28.regs, g27_23]
    have g28_24 : reg n28 (24 : Fin 32) = (p) + BitVec.ofNat 32 0x1 := by rw [u28.regs, g27_24]
    have g28_25 : reg n28 (25 : Fin 32) = rp := by rw [u28.regs, g27_25]
    have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [u28.regs, g27_26]
    have g28_27 : reg n28 (27 : Fin 32) = rl := by rw [u28.regs, g27_27]
    have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x64, 0x4), (0x74, 0x4)] := by rw [m28]; exact keep_kk27
    clear keep_kk27
    have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = ((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) := by rw [m28]; exact w27_64
    have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by rw [m28]; exact w27_74
    clear w27_74 w27_64 g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_14 g27_13 g27_12 g27_11 g27_10 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
    -- 0x1878
    obtain ⟨n29, c29, u29⟩ := s28.block svCkd1878 E28.self svCkd1878_end
      ⟨trivial, trivial⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have s29 : St n29.mem SV n29 0x187A (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have rb29 : ∀ q, reg n29 q = (runBlock svCkd1878 (n28.mem, reg n28)).2 q := fun q => by rw [u29.regs]
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
    have g29_8 : reg n29 (8 : Fin 32) = (c) + BitVec.ofNat 32 0xFFFFFFFF := by
      rw [rb29, runBlock_reg _ _ _ (8 : Fin 32) s28.zero (by decide), g28_8]
    have g29_9 : reg n29 (9 : Fin 32) = w74 := by
      rw [rb29, runBlock_reg _ _ _ (9 : Fin 32) s28.zero (by decide), g28_9]
    have g29_10 : reg n29 a0 = BitVec.ofNat 32 0xA := by
      rw [rb29, runBlock_reg _ _ _ a0 s28.zero (by decide), g28_10]
    have g29_11 : reg n29 a1 = (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) &&& (aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)))) := by
      rw [rb29, runBlock_reg _ _ _ a1 s28.zero (by decide), g28_11]
    have g29_12 : reg n29 a2 = aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) := by
      rw [rb29, runBlock_reg _ _ _ a2 s28.zero (by decide), g28_12]
    have g29_13 : reg n29 a3 = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by
      rw [rb29, runBlock_reg _ _ _ a3 s28.zero (by decide), g28_13]
    have g29_14 : reg n29 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by
      rw [rb29, runBlock_reg _ _ _ a4 s28.zero (by decide), g28_14]
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
    have g29_24 : reg n29 (24 : Fin 32) = (p) + BitVec.ofNat 32 0x1 := by
      rw [rb29, runBlock_reg _ _ _ (24 : Fin 32) s28.zero (by decide), g28_24]
    have g29_26 : reg n29 (26 : Fin 32) = x26 := by
      rw [rb29, runBlock_reg _ _ _ (26 : Fin 32) s28.zero (by decide), g28_26]
    have g29_27 : reg n29 (27 : Fin 32) = rl := by
      rw [rb29, runBlock_reg _ _ _ (27 : Fin 32) s28.zero (by decide), g28_27]
    have g29_25 : reg n29 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by
      rw [rb29]; simp +decide only [runBlock, BInstr.run, svCkd1878, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g28_2, g28_3, g28_4, g28_8, g28_9, g28_10, g28_11, g28_12, g28_13, g28_14, g28_18, g28_19, g28_20, g28_21, g28_22, g28_23, g28_24, g28_25, g28_26, g28_27, s28.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x64, 0x4), (0x74, 0x4)] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = ((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) := by rw [m29]; exact w28_64
    have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by rw [m29]; exact w28_74
    clear w28_74 w28_64 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_14 g28_13 g28_12 g28_11 g28_10 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
    -- 0x187A: j
    obtain ⟨n30, d30, u30⟩ := s29.jump E29.self sv_at_187a (off' := 0x1882) (by decide)
      (by rw [s29.pc]; decide)
    have s30 : St n30.mem SV n30 0x1882 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
    have m30 : n30.mem = n29.mem := u30.mem
    have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
    have t30 : Steps n0 n30 := t29.trans (.single d30)
    have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
    have E30 : SvCode n30.mem := E29.fr F fr30
    have V30 : SvSaves B n30.mem v := V29.same m30
    have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, g29_2]
    have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, g29_3]
    have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, g29_4]
    have g30_8 : reg n30 (8 : Fin 32) = (c) + BitVec.ofNat 32 0xFFFFFFFF := by rw [u30.regs, g29_8]
    have g30_9 : reg n30 (9 : Fin 32) = w74 := by rw [u30.regs, g29_9]
    have g30_10 : reg n30 a0 = BitVec.ofNat 32 0xA := by rw [u30.regs, g29_10]
    have g30_11 : reg n30 a1 = (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) &&& (aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)))) := by rw [u30.regs, g29_11]
    have g30_12 : reg n30 a2 = aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) := by rw [u30.regs, g29_12]
    have g30_13 : reg n30 a3 = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by rw [u30.regs, g29_13]
    have g30_14 : reg n30 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by rw [u30.regs, g29_14]
    have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, g29_18]
    have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, g29_19]
    have g30_20 : reg n30 (20 : Fin 32) = x20 := by rw [u30.regs, g29_20]
    have g30_21 : reg n30 (21 : Fin 32) = x21 := by rw [u30.regs, g29_21]
    have g30_22 : reg n30 (22 : Fin 32) = x22 := by rw [u30.regs, g29_22]
    have g30_23 : reg n30 (23 : Fin 32) = x23 := by rw [u30.regs, g29_23]
    have g30_24 : reg n30 (24 : Fin 32) = (p) + BitVec.ofNat 32 0x1 := by rw [u30.regs, g29_24]
    have g30_25 : reg n30 (25 : Fin 32) = BitVec.ofNat 32 0x1A := by rw [u30.regs, g29_25]
    have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [u30.regs, g29_26]
    have g30_27 : reg n30 (27 : Fin 32) = rl := by rw [u30.regs, g29_27]
    have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x64, 0x4), (0x74, 0x4)] := by rw [m30]; exact keep_kk29
    clear keep_kk29
    have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = ((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) := by rw [m30]; exact w29_64
    have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by rw [m30]; exact w29_74
    clear w29_74 w29_64 g29_25 g29_27 g29_26 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_14 g29_13 g29_12 g29_11 g29_10 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 rb29 s29 m29 u29 c29
    exact .inl ⟨(fun ⟨h0', h1', h2', _⟩ => by exact hov2 h2'), sv_fail_1882 F E30 s30 t30 (fun x hx => (fR30 x hx).trans (fM x hx).symm) V30 hret g30_2 g30_18 hO g30_3 g30_4⟩
  -- 0x154E: branch, taken
  obtain ⟨n27, d27, u27⟩ := s26.taken E26.self 0x14FE sv_at_154e
    (by decide) (by rw [g26_11, s26.zero]; exact br_beq_t hov2)
  have s27 : St n27.mem SV n27 0x14FE (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans (.single d27)
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = (c) + BitVec.ofNat 32 0xFFFFFFFF := by rw [u27.regs, g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = w74 := by rw [u27.regs, g26_9]
  have g27_10 : reg n27 a0 = BitVec.ofNat 32 0xA := by rw [u27.regs, g26_10]
  have g27_11 : reg n27 a1 = (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) &&& (aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA)))) := by rw [u27.regs, g26_11]
  have g27_12 : reg n27 a2 = aluEval .sltu (((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) := by rw [u27.regs, g26_12]
  have g27_13 : reg n27 a3 = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by rw [u27.regs, g26_13]
  have g27_14 : reg n27 a4 = aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74) (BitVec.ofNat 32 0xA)) := by rw [u27.regs, g26_14]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [u27.regs, g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [u27.regs, g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [u27.regs, g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = x23 := by rw [u27.regs, g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = (p) + BitVec.ofNat 32 0x1 := by rw [u27.regs, g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = rp := by rw [u27.regs, g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = rl := by rw [u27.regs, g26_27]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [(0x64, 0x4), (0x74, 0x4)] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = ((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA)) := by rw [m27]; exact w26_64
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ((aluEval .mul (w74) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64) (BitVec.ofNat 32 0xA))) := by rw [m27]; exact w26_74
  clear w26_74 w26_64 g26_8 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_14 g26_13 g26_12 g26_11 g26_10 g26_9 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 rb26 s26 m26 u26 c26
  exact .inr ⟨hdig, hov1, hov2, n27, t27, s27, E27, V27, fR27, g27_2, g27_3, g27_4, g27_8, g27_9, g27_10, g27_18, g27_19, g27_20, g27_21, g27_22, g27_23, g27_24, g27_25, g27_26, g27_27, w27_64, w27_74, keep_kk27.mono (by decide)⟩

end C3.RV32.Sv
