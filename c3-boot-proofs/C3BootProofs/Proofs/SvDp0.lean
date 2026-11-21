import C3BootProofs.Proofs.SvData

/-!
# `sigstore::verify`: an extension with policy OID 0

From the OID tests at 0x60E back to the loop head at 0x4EA, for an extension with policy OID 0: its value must be one `UTF8String`, which fills policy slot 0.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svDp060e : List BInstr :=
  [.aluImm .add a3 x0 0x3, .alu .add a0 x0 (8 : Fin 32)]
theorem svDp060e_end : blockEnd sigstoreVerifyCode 0x60E svDp060e = some 0x612 := by
  simp only [svDp060e]
  rw [blockEnd, sv_at_60e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_610]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp0614 : List BInstr :=
  [.lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF889]
theorem svDp0614_end : blockEnd sigstoreVerifyCode 0x614 svDp0614 = some 0x61C := by
  simp only [svDp0614]
  rw [blockEnd, sv_at_614]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_618]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp06bc : List BInstr :=
  [.aluImm .add a3 x0 0x3, .alu .add a0 x0 (8 : Fin 32)]
theorem svDp06bc_end : blockEnd sigstoreVerifyCode 0x6BC svDp06bc = some 0x6C0 := by
  simp only [svDp06bc]
  rw [blockEnd, sv_at_6bc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_6be]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp06c2 : List BInstr :=
  [.lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF892]
theorem svDp06c2_end : blockEnd sigstoreVerifyCode 0x6C2 svDp06c2 = some 0x6CA := by
  simp only [svDp06c2]
  rw [blockEnd, sv_at_6c2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_6c6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp078e : List BInstr :=
  [.aluImm .add a3 x0 0x3, .alu .add a0 x0 (8 : Fin 32)]
theorem svDp078e_end : blockEnd sigstoreVerifyCode 0x78E svDp078e = some 0x792 := by
  simp only [svDp078e]
  rw [blockEnd, sv_at_78e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_790]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp0794 : List BInstr :=
  [.lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF88F]
theorem svDp0794_end : blockEnd sigstoreVerifyCode 0x794 svDp0794 = some 0x79C := by
  simp only [svDp0794]
  rw [blockEnd, sv_at_794]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_798]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp089c : List BInstr :=
  [.aluImm .add (22 : Fin 32) x0 0xFFFFFFFF, .lui (23 : Fin 32) 0x3FCC5000, .aluImm .add (23 : Fin 32) (23 : Fin 32) 0xFFFFF8EC]
theorem svDp089c_end : blockEnd sigstoreVerifyCode 0x89C svDp089c = some 0x8A6 := by
  simp only [svDp089c]
  rw [blockEnd, sv_at_89c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_89e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_8a2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp08a6 : List BInstr :=
  [.aluImm .add a0 x0 0x4]
theorem svDp08a6_end : blockEnd sigstoreVerifyCode 0x8A6 svDp08a6 = some 0x8A8 := by
  simp only [svDp08a6]
  rw [blockEnd, sv_at_8a6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp08b0 : List BInstr :=
  [.aluImm .add a1 x0 0xA, .alu .add a2 x0 (8 : Fin 32)]
theorem svDp08b0_end : blockEnd sigstoreVerifyCode 0x8B0 svDp08b0 = some 0x8B4 := by
  simp only [svDp08b0]
  rw [blockEnd, sv_at_8b0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_8b2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp08be : List BInstr :=
  [.aluImm .add (22 : Fin 32) (22 : Fin 32) 0x1, .aluImm .add (23 : Fin 32) (23 : Fin 32) 0x8]
theorem svDp08be_end : blockEnd sigstoreVerifyCode 0x8BE svDp08be = some 0x8C2 := by
  simp only [svDp08be]
  rw [blockEnd, sv_at_8be]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_8c0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp08c4 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x320, .alu .add a0 a0 sp]
theorem svDp08c4_end : blockEnd sigstoreVerifyCode 0x8C4 svDp08c4 = some 0x8CC := by
  simp only [svDp08c4]
  rw [blockEnd, sv_at_8c4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_8c6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_8ca]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp08ce : List BInstr :=
  [.aluImm .add a3 a0 0x100]
theorem svDp08ce_end : blockEnd sigstoreVerifyCode 0x8CE svDp08ce = some 0x8D2 := by
  simp only [svDp08ce]
  rw [blockEnd, sv_at_8ce]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp08da : List BInstr :=
  [.lui a1 0x1000, .aluImm .add a1 a1 0x320, .alu .add (8 : Fin 32) sp a1]
theorem svDp08da_end : blockEnd sigstoreVerifyCode 0x8DA svDp08da = some 0x8E4 := by
  simp only [svDp08da]
  rw [blockEnd, sv_at_8da]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_8dc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_8e0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp08e6 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x20, .alu .add a0 a0 sp, .lui a1 0x1000, .aluImm .add a1 a1 0x480, .alu .add a1 a1 sp]
theorem svDp08e6_end : blockEnd sigstoreVerifyCode 0x8E6 svDp08e6 = some 0x8F6 := by
  simp only [svDp08e6]
  rw [blockEnd, sv_at_8e6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_8e8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_8ec]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_8ee]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_8f0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_8f4]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp0908 : List BInstr :=
  [.aluImm .add a2 x0 0xC]
theorem svDp0908_end : blockEnd sigstoreVerifyCode 0x908 svDp0908 = some 0x90A := by
  simp only [svDp0908]
  rw [blockEnd, sv_at_908]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp0b4e : List BInstr :=
  [.aluImm .add a0 x0 0x16]
theorem svDp0b4e_end : blockEnd sigstoreVerifyCode 0xB4E svDp0b4e = some 0xB50 := by
  simp only [svDp0b4e]
  rw [blockEnd, sv_at_b4e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp0b36 : List BInstr :=
  [.aluImm .add a0 x0 0x1]
theorem svDp0b36_end : blockEnd sigstoreVerifyCode 0xB36 svDp0b36 = some 0xB38 := by
  simp only [svDp0b36]
  rw [blockEnd, sv_at_b36]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDp091a : List BInstr :=
  [.aluImm .sll (22 : Fin 32) (22 : Fin 32) 0x3, .aluImm .add a2 sp 0x7FF, .aluImm .add a2 a2 0x221, .alu .add (22 : Fin 32) (22 : Fin 32) a2, .alu .add a2 x0 (22 : Fin 32)]
theorem svDp091a_end : blockEnd sigstoreVerifyCode 0x91A svDp091a = some 0x928 := by
  simp only [svDp091a]
  rw [blockEnd, sv_at_91a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_91c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_920]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_924]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_926]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_dp0 {B out bp x9 x21 x25 x26 f30 f34 rem p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 op ol vp vl rest : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x60E (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = op)
    (g0_9 : reg n0 (9 : Fin 32) = x9)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl)
    (w0_3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp)
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
    (w0_54 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54)
    (w0_58 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58)
    (w0_5c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c)
    (w0_60 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64)
    (w0_68 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68)
    (w0_6c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c)
    (w0_70 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c)
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80)
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84)
    (w0_88 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0)
    (w0_8c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L)
    (w0_90 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur)
    (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest)
    (w0_a20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0)
    (w0_a24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1)
    (w0_a28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2)
    (w0_a2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3)
    (w0_a30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4)
    (w0_a34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5)
    (w0_a38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6)
    (w0_a3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7)
    (w0_a40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8)
    (w0_a44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9)
    (val_in : SvIn B (vp) (vl).toNat)
    (oid_in : SvIn B (op) (ol).toNat)
    (SD0 : SvData M0)
    (hku : ¬ memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC4889) 3)
    (heku : ¬ memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC4892) 3)
    (hbc : ¬ memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC488F) 3)
    (hp0 : memBytes M0 (BitVec.ofNat 32 0x3FCC48B8) 10 = memBytes M0 op ol.toNat) :
    (¬ (∃ tl35, derTlv (memBytes M0 (vp) (vl).toNat) = .ok tl35 ∧ (BitVec.ofNat 8 tl35.tag = BitVec.ofNat 8 0xC) ∧ ((vl) - BitVec.ofNat 32 (tl35.header + tl35.len) = 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ tl35, derTlv (memBytes M0 (vp) (vl).toNat) = .ok tl35 ∧
    (BitVec.ofNat 8 tl35.tag = BitVec.ofNat 8 0xC) ∧
    ((vl) - BitVec.ofNat 32 (tl35.header + tl35.len) = 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x4EA (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (9 : Fin 32) = x9 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rest ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (vp) + BitVec.ofNat 32 tl35.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl35.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 ∧
        SvKeepL B n0.mem n'.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0xA20, 0x4), (0xA24, 0x4), (0x40, 0x4)]) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x60E
  obtain ⟨n1, c1, u1⟩ := s0.block svDp060e E0.self svDp060e_end
    ⟨trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0x612 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svDp060e (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
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
  have g1_8 : reg n1 (8 : Fin 32) = op := by
    rw [rb1, runBlock_reg _ _ _ (8 : Fin 32) s0.zero (by decide), g0_8]
  have g1_9 : reg n1 (9 : Fin 32) = x9 := by
    rw [rb1, runBlock_reg _ _ _ (9 : Fin 32) s0.zero (by decide), g0_9]
  have g1_18 : reg n1 (18 : Fin 32) = out := by
    rw [rb1, runBlock_reg _ _ _ (18 : Fin 32) s0.zero (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by
    rw [rb1, runBlock_reg _ _ _ (19 : Fin 32) s0.zero (by decide), g0_19]
  have g1_21 : reg n1 (21 : Fin 32) = x21 := by
    rw [rb1, runBlock_reg _ _ _ (21 : Fin 32) s0.zero (by decide), g0_21]
  have g1_25 : reg n1 (25 : Fin 32) = x25 := by
    rw [rb1, runBlock_reg _ _ _ (25 : Fin 32) s0.zero (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by
    rw [rb1, runBlock_reg _ _ _ (26 : Fin 32) s0.zero (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb1, runBlock_reg _ _ _ (27 : Fin 32) s0.zero (by decide), g0_27]
  have g1_10 : reg n1 a0 = op := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svDp060e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_21, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_13 : reg n1 a3 = BitVec.ofNat 32 0x3 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svDp060e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_21, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_30 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m1]; exact w0_30
  have w1_34 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m1]; exact w0_34
  have w1_38 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m1]; exact w0_38
  have w1_3c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m1]; exact w0_3c
  have w1_40 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m1]; exact w0_40
  have w1_48 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m1]; exact w0_48
  have w1_4c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m1]; exact w0_4c
  have w1_50 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m1]; exact w0_50
  have w1_54 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m1]; exact w0_54
  have w1_58 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m1]; exact w0_58
  have w1_5c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m1]; exact w0_5c
  have w1_60 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m1]; exact w0_60
  have w1_64 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m1]; exact w0_64
  have w1_68 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m1]; exact w0_68
  have w1_6c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m1]; exact w0_6c
  have w1_70 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m1]; exact w0_70
  have w1_74 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m1]; exact w0_74
  have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m1]; exact w0_78
  have w1_7c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m1]; exact w0_7c
  have w1_80 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m1]; exact w0_80
  have w1_84 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m1]; exact w0_84
  have w1_88 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m1]; exact w0_88
  have w1_8c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m1]; exact w0_8c
  have w1_90 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m1]; exact w0_90
  have w1_94 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m1]; exact w0_94
  have w1_a20 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m1]; exact w0_a20
  have w1_a24 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m1]; exact w0_a24
  have w1_a28 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m1]; exact w0_a28
  have w1_a2c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m1]; exact w0_a2c
  have w1_a30 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m1]; exact w0_a30
  have w1_a34 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m1]; exact w0_a34
  have w1_a38 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m1]; exact w0_a38
  have w1_a3c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m1]; exact w0_a3c
  have w1_a40 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m1]; exact w0_a40
  have w1_a44 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m1]; exact w0_a44
  -- 0x612: lw
  obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_612 (off' := 0x614) (by decide)
    (by rw [g1_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s2 : St n2.mem SV n2 0x614 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_4]
  have g2_8 : reg n2 (8 : Fin 32) = op := by rw [u2.regs, upd_ne (by decide) (by decide), g1_8]
  have g2_9 : reg n2 (9 : Fin 32) = x9 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_9]
  have g2_10 : reg n2 a0 = op := by rw [u2.regs, upd_ne (by decide) (by decide), g1_10]
  have g2_13 : reg n2 a3 = BitVec.ofNat 32 0x3 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_13]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
  have g2_25 : reg n2 (25 : Fin 32) = x25 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_27]
  have g2_11 : reg n2 a1 = ol := by
    rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g1_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w1_48]
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m2]; exact w1_30
  have w2_34 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m2]; exact w1_34
  have w2_38 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m2]; exact w1_38
  have w2_3c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m2]; exact w1_3c
  have w2_40 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m2]; exact w1_40
  have w2_48 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m2]; exact w1_48
  have w2_4c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m2]; exact w1_4c
  have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m2]; exact w1_50
  have w2_54 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m2]; exact w1_54
  have w2_58 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m2]; exact w1_58
  have w2_5c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m2]; exact w1_5c
  have w2_60 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m2]; exact w1_60
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m2]; exact w1_64
  have w2_68 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m2]; exact w1_68
  have w2_6c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m2]; exact w1_6c
  have w2_70 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m2]; exact w1_70
  have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m2]; exact w1_74
  have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m2]; exact w1_78
  have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m2]; exact w1_7c
  have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m2]; exact w1_80
  have w2_84 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m2]; exact w1_84
  have w2_88 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m2]; exact w1_88
  have w2_8c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m2]; exact w1_8c
  have w2_90 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m2]; exact w1_90
  have w2_94 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m2]; exact w1_94
  have w2_a20 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m2]; exact w1_a20
  have w2_a24 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m2]; exact w1_a24
  have w2_a28 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m2]; exact w1_a28
  have w2_a2c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m2]; exact w1_a2c
  have w2_a30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m2]; exact w1_a30
  have w2_a34 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m2]; exact w1_a34
  have w2_a38 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m2]; exact w1_a38
  have w2_a3c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m2]; exact w1_a3c
  have w2_a40 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m2]; exact w1_a40
  have w2_a44 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m2]; exact w1_a44
  clear w1_a44 w1_a40 w1_a3c w1_a38 w1_a34 w1_a30 w1_a2c w1_a28 w1_a24 w1_a20 w1_94 w1_90 w1_8c w1_88 w1_84 w1_80 w1_7c w1_78 w1_74 w1_70 w1_6c w1_68 w1_64 w1_60 w1_5c w1_58 w1_54 w1_50 w1_4c w1_48 w1_40 w1_3c w1_38 w1_34 w1_30 g1_13 g1_10 g1_27 g1_26 g1_25 g1_21 g1_19 g1_18 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 rb1 s1 m1 u1 c1 g0_4 g0_3 fR0 t0
  -- 0x614
  obtain ⟨n3, c3, u3⟩ := s2.block svDp0614 E2.self svDp0614_end
    ⟨trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem SV n3 0x61C (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have rb3 : ∀ q, reg n3 q = (runBlock svDp0614 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
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
  have g3_8 : reg n3 (8 : Fin 32) = op := by
    rw [rb3, runBlock_reg _ _ _ (8 : Fin 32) s2.zero (by decide), g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = x9 := by
    rw [rb3, runBlock_reg _ _ _ (9 : Fin 32) s2.zero (by decide), g2_9]
  have g3_10 : reg n3 a0 = op := by
    rw [rb3, runBlock_reg _ _ _ a0 s2.zero (by decide), g2_10]
  have g3_11 : reg n3 a1 = ol := by
    rw [rb3, runBlock_reg _ _ _ a1 s2.zero (by decide), g2_11]
  have g3_13 : reg n3 a3 = BitVec.ofNat 32 0x3 := by
    rw [rb3, runBlock_reg _ _ _ a3 s2.zero (by decide), g2_13]
  have g3_18 : reg n3 (18 : Fin 32) = out := by
    rw [rb3, runBlock_reg _ _ _ (18 : Fin 32) s2.zero (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by
    rw [rb3, runBlock_reg _ _ _ (19 : Fin 32) s2.zero (by decide), g2_19]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by
    rw [rb3, runBlock_reg _ _ _ (21 : Fin 32) s2.zero (by decide), g2_21]
  have g3_25 : reg n3 (25 : Fin 32) = x25 := by
    rw [rb3, runBlock_reg _ _ _ (25 : Fin 32) s2.zero (by decide), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by
    rw [rb3, runBlock_reg _ _ _ (26 : Fin 32) s2.zero (by decide), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb3, runBlock_reg _ _ _ (27 : Fin 32) s2.zero (by decide), g2_27]
  have g3_12 : reg n3 a2 = BitVec.ofNat 32 0x3FCC4889 := by
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svDp0614, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_8, g2_9, g2_10, g2_11, g2_13, g2_18, g2_19, g2_21, g2_25, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_30 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m3]; exact w2_30
  have w3_34 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m3]; exact w2_34
  have w3_38 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m3]; exact w2_38
  have w3_3c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m3]; exact w2_3c
  have w3_40 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m3]; exact w2_40
  have w3_48 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m3]; exact w2_48
  have w3_4c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m3]; exact w2_4c
  have w3_50 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m3]; exact w2_50
  have w3_54 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m3]; exact w2_54
  have w3_58 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m3]; exact w2_58
  have w3_5c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m3]; exact w2_5c
  have w3_60 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m3]; exact w2_60
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m3]; exact w2_64
  have w3_68 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m3]; exact w2_68
  have w3_6c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m3]; exact w2_6c
  have w3_70 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m3]; exact w2_70
  have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m3]; exact w2_74
  have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m3]; exact w2_78
  have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m3]; exact w2_7c
  have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m3]; exact w2_80
  have w3_84 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m3]; exact w2_84
  have w3_88 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m3]; exact w2_88
  have w3_8c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m3]; exact w2_8c
  have w3_90 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m3]; exact w2_90
  have w3_94 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m3]; exact w2_94
  have w3_a20 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m3]; exact w2_a20
  have w3_a24 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m3]; exact w2_a24
  have w3_a28 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m3]; exact w2_a28
  have w3_a2c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m3]; exact w2_a2c
  have w3_a30 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m3]; exact w2_a30
  have w3_a34 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m3]; exact w2_a34
  have w3_a38 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m3]; exact w2_a38
  have w3_a3c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m3]; exact w2_a3c
  have w3_a40 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m3]; exact w2_a40
  have w3_a44 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m3]; exact w2_a44
  clear w2_a44 w2_a40 w2_a3c w2_a38 w2_a34 w2_a30 w2_a2c w2_a28 w2_a24 w2_a20 w2_94 w2_90 w2_8c w2_88 w2_84 w2_80 w2_7c w2_78 w2_74 w2_70 w2_6c w2_68 w2_64 w2_60 w2_5c w2_58 w2_54 w2_50 w2_4c w2_48 w2_40 w2_3c w2_38 w2_34 w2_30 g2_11 g2_27 g2_26 g2_25 g2_21 g2_19 g2_18 g2_13 g2_10 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0x61C: sv_seqEqF
  obtain ⟨n4, c4, s4, rk4, a0_4, K4, fr4⟩ := sv_seqEqF (pl := ol.toNat) (ql := 3)
    F E3 s3 sv_at_61c sv_at_620 (by decide) (by decide) g3_2
    g3_10 (by rw [g3_11, ofNat_toNat_self]) g3_12 g3_13 (.inl oid_in) (.inr ⟨by decide, by decide⟩)
  have t4 : Steps n0 n4 := t3.trans c4
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.keepL K4 (by decide)
  rw [sv_mbRo F fR3 (.inl oid_in), sv_mbRo F fR3 (.inr ⟨by decide, by decide⟩)] at a0_4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [rk4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk4 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk4 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3_4]
  have g4_8 : reg n4 (8 : Fin 32) = op := by rw [rk4 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = x9 := by rw [rk4 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3_9]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [rk4 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [rk4 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3_19]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [rk4 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3_21]
  have g4_25 : reg n4 (25 : Fin 32) = x25 := by rw [rk4 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [rk4 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk4 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3_27]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [] := keep_kk3.trans K4
  clear keep_kk3
  have w4_30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K4.w32 (by decide) (by decide)).trans w3_30
  have w4_34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K4.w32 (by decide) (by decide)).trans w3_34
  have w4_38 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K4.w32 (by decide) (by decide)).trans w3_38
  have w4_3c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K4.w32 (by decide) (by decide)).trans w3_3c
  have w4_40 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K4.w32 (by decide) (by decide)).trans w3_40
  have w4_48 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K4.w32 (by decide) (by decide)).trans w3_48
  have w4_4c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K4.w32 (by decide) (by decide)).trans w3_4c
  have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K4.w32 (by decide) (by decide)).trans w3_50
  have w4_54 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K4.w32 (by decide) (by decide)).trans w3_54
  have w4_58 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K4.w32 (by decide) (by decide)).trans w3_58
  have w4_5c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K4.w32 (by decide) (by decide)).trans w3_5c
  have w4_60 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K4.w32 (by decide) (by decide)).trans w3_60
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K4.w32 (by decide) (by decide)).trans w3_64
  have w4_68 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K4.w32 (by decide) (by decide)).trans w3_68
  have w4_6c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K4.w32 (by decide) (by decide)).trans w3_6c
  have w4_70 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K4.w32 (by decide) (by decide)).trans w3_70
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K4.w32 (by decide) (by decide)).trans w3_74
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K4.w32 (by decide) (by decide)).trans w3_78
  have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K4.w32 (by decide) (by decide)).trans w3_7c
  have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K4.w32 (by decide) (by decide)).trans w3_80
  have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K4.w32 (by decide) (by decide)).trans w3_84
  have w4_88 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K4.w32 (by decide) (by decide)).trans w3_88
  have w4_8c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K4.w32 (by decide) (by decide)).trans w3_8c
  have w4_90 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K4.w32 (by decide) (by decide)).trans w3_90
  have w4_94 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K4.w32 (by decide) (by decide)).trans w3_94
  have w4_a20 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K4.w32 (by decide) (by decide)).trans w3_a20
  have w4_a24 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K4.w32 (by decide) (by decide)).trans w3_a24
  have w4_a28 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K4.w32 (by decide) (by decide)).trans w3_a28
  have w4_a2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K4.w32 (by decide) (by decide)).trans w3_a2c
  have w4_a30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K4.w32 (by decide) (by decide)).trans w3_a30
  have w4_a34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K4.w32 (by decide) (by decide)).trans w3_a34
  have w4_a38 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K4.w32 (by decide) (by decide)).trans w3_a38
  have w4_a3c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K4.w32 (by decide) (by decide)).trans w3_a3c
  have w4_a40 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K4.w32 (by decide) (by decide)).trans w3_a40
  have w4_a44 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K4.w32 (by decide) (by decide)).trans w3_a44
  clear w3_a44 w3_a40 w3_a3c w3_a38 w3_a34 w3_a30 w3_a2c w3_a28 w3_a24 w3_a20 w3_94 w3_90 w3_8c w3_88 w3_84 w3_80 w3_7c w3_78 w3_74 w3_70 w3_6c w3_68 w3_64 w3_60 w3_5c w3_58 w3_54 w3_50 w3_4c w3_48 w3_40 w3_3c w3_38 w3_34 w3_30 g3_12 g3_27 g3_26 g3_25 g3_21 g3_19 g3_18 g3_13 g3_11 g3_10 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 rb3 s3 m3 u3 c3
  have g4_10 : reg n4 a0 = BitVec.ofNat 32 0 := by rw [a0_4, ite_eq_right hku]; rfl
  -- 0x624: branch, taken
  obtain ⟨n5, d5, u5⟩ := s4.taken E4.self 0x6BC sv_at_624
    (by decide) (by rw [g4_10, s4.zero]; decide)
  have s5 : St n5.mem SV n5 0x6BC (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = M0 x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = op := by rw [u5.regs, g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = x9 := by rw [u5.regs, g4_9]
  have g5_10 : reg n5 a0 = BitVec.ofNat 32 0x0 := by rw [u5.regs, g4_10]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, g4_19]
  have g5_21 : reg n5 (21 : Fin 32) = x21 := by rw [u5.regs, g4_21]
  have g5_25 : reg n5 (25 : Fin 32) = x25 := by rw [u5.regs, g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by rw [u5.regs, g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u5.regs, g4_27]
  have keep_kk5 : SvKeepL B n0.mem n5.mem [] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m5]; exact w4_30
  have w5_34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m5]; exact w4_34
  have w5_38 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m5]; exact w4_38
  have w5_3c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m5]; exact w4_3c
  have w5_40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m5]; exact w4_40
  have w5_48 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m5]; exact w4_48
  have w5_4c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m5]; exact w4_4c
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m5]; exact w4_50
  have w5_54 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m5]; exact w4_54
  have w5_58 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m5]; exact w4_58
  have w5_5c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m5]; exact w4_5c
  have w5_60 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m5]; exact w4_60
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m5]; exact w4_64
  have w5_68 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m5]; exact w4_68
  have w5_6c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m5]; exact w4_6c
  have w5_70 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m5]; exact w4_70
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m5]; exact w4_74
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m5]; exact w4_78
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m5]; exact w4_7c
  have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m5]; exact w4_80
  have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m5]; exact w4_84
  have w5_88 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m5]; exact w4_88
  have w5_8c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m5]; exact w4_8c
  have w5_90 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m5]; exact w4_90
  have w5_94 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m5]; exact w4_94
  have w5_a20 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m5]; exact w4_a20
  have w5_a24 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m5]; exact w4_a24
  have w5_a28 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m5]; exact w4_a28
  have w5_a2c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m5]; exact w4_a2c
  have w5_a30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m5]; exact w4_a30
  have w5_a34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m5]; exact w4_a34
  have w5_a38 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m5]; exact w4_a38
  have w5_a3c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m5]; exact w4_a3c
  have w5_a40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m5]; exact w4_a40
  have w5_a44 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m5]; exact w4_a44
  clear w4_a44 w4_a40 w4_a3c w4_a38 w4_a34 w4_a30 w4_a2c w4_a28 w4_a24 w4_a20 w4_94 w4_90 w4_8c w4_88 w4_84 w4_80 w4_7c w4_78 w4_74 w4_70 w4_6c w4_68 w4_64 w4_60 w4_5c w4_58 w4_54 w4_50 w4_4c w4_48 w4_40 w4_3c w4_38 w4_34 w4_30 g4_27 g4_26 g4_25 g4_21 g4_19 g4_18 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 K4 a0_4 rk4 s4 c4
  -- 0x6BC
  obtain ⟨n6, c6, u6⟩ := s5.block svDp06bc E5.self svDp06bc_end
    ⟨trivial, trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem SV n6 0x6C0 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock svDp06bc (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
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
  have g6_8 : reg n6 (8 : Fin 32) = op := by
    rw [rb6, runBlock_reg _ _ _ (8 : Fin 32) s5.zero (by decide), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = x9 := by
    rw [rb6, runBlock_reg _ _ _ (9 : Fin 32) s5.zero (by decide), g5_9]
  have g6_18 : reg n6 (18 : Fin 32) = out := by
    rw [rb6, runBlock_reg _ _ _ (18 : Fin 32) s5.zero (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by
    rw [rb6, runBlock_reg _ _ _ (19 : Fin 32) s5.zero (by decide), g5_19]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by
    rw [rb6, runBlock_reg _ _ _ (21 : Fin 32) s5.zero (by decide), g5_21]
  have g6_25 : reg n6 (25 : Fin 32) = x25 := by
    rw [rb6, runBlock_reg _ _ _ (25 : Fin 32) s5.zero (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by
    rw [rb6, runBlock_reg _ _ _ (26 : Fin 32) s5.zero (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb6, runBlock_reg _ _ _ (27 : Fin 32) s5.zero (by decide), g5_27]
  have g6_10 : reg n6 a0 = op := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svDp06bc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_10, g5_18, g5_19, g5_21, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g6_13 : reg n6 a3 = BitVec.ofNat 32 0x3 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svDp06bc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_10, g5_18, g5_19, g5_21, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk6 : SvKeepL B n0.mem n6.mem [] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m6]; exact w5_30
  have w6_34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m6]; exact w5_34
  have w6_38 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m6]; exact w5_38
  have w6_3c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m6]; exact w5_3c
  have w6_40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m6]; exact w5_40
  have w6_48 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m6]; exact w5_48
  have w6_4c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m6]; exact w5_4c
  have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m6]; exact w5_50
  have w6_54 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m6]; exact w5_54
  have w6_58 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m6]; exact w5_58
  have w6_5c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m6]; exact w5_5c
  have w6_60 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m6]; exact w5_60
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m6]; exact w5_64
  have w6_68 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m6]; exact w5_68
  have w6_6c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m6]; exact w5_6c
  have w6_70 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m6]; exact w5_70
  have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m6]; exact w5_74
  have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m6]; exact w5_78
  have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m6]; exact w5_7c
  have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m6]; exact w5_80
  have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m6]; exact w5_84
  have w6_88 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m6]; exact w5_88
  have w6_8c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m6]; exact w5_8c
  have w6_90 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m6]; exact w5_90
  have w6_94 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m6]; exact w5_94
  have w6_a20 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m6]; exact w5_a20
  have w6_a24 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m6]; exact w5_a24
  have w6_a28 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m6]; exact w5_a28
  have w6_a2c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m6]; exact w5_a2c
  have w6_a30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m6]; exact w5_a30
  have w6_a34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m6]; exact w5_a34
  have w6_a38 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m6]; exact w5_a38
  have w6_a3c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m6]; exact w5_a3c
  have w6_a40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m6]; exact w5_a40
  have w6_a44 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m6]; exact w5_a44
  clear w5_a44 w5_a40 w5_a3c w5_a38 w5_a34 w5_a30 w5_a2c w5_a28 w5_a24 w5_a20 w5_94 w5_90 w5_8c w5_88 w5_84 w5_80 w5_7c w5_78 w5_74 w5_70 w5_6c w5_68 w5_64 w5_60 w5_5c w5_58 w5_54 w5_50 w5_4c w5_48 w5_40 w5_3c w5_38 w5_34 w5_30 g5_27 g5_26 g5_25 g5_21 g5_19 g5_18 g5_10 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5 g4_10
  -- 0x6C0: lw
  obtain ⟨n7, d7, u7⟩ := s6.lw E6.self sv_at_6c0 (off' := 0x6C2) (by decide)
    (by rw [g6_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s7 : St n7.mem SV n7 0x6C2 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = op := by rw [u7.regs, upd_ne (by decide) (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = x9 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_9]
  have g7_10 : reg n7 a0 = op := by rw [u7.regs, upd_ne (by decide) (by decide), g6_10]
  have g7_13 : reg n7 a3 = BitVec.ofNat 32 0x3 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_13]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, upd_ne (by decide) (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_19]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_21]
  have g7_25 : reg n7 (25 : Fin 32) = x25 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_27]
  have g7_11 : reg n7 a1 = ol := by
    rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g6_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w6_48]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [] := by rw [m7]; exact keep_kk6
  clear keep_kk6
  have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m7]; exact w6_30
  have w7_34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m7]; exact w6_34
  have w7_38 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m7]; exact w6_38
  have w7_3c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m7]; exact w6_3c
  have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m7]; exact w6_40
  have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m7]; exact w6_48
  have w7_4c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m7]; exact w6_4c
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m7]; exact w6_50
  have w7_54 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m7]; exact w6_54
  have w7_58 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m7]; exact w6_58
  have w7_5c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m7]; exact w6_5c
  have w7_60 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m7]; exact w6_60
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m7]; exact w6_64
  have w7_68 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m7]; exact w6_68
  have w7_6c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m7]; exact w6_6c
  have w7_70 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m7]; exact w6_70
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m7]; exact w6_74
  have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m7]; exact w6_78
  have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m7]; exact w6_7c
  have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m7]; exact w6_80
  have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m7]; exact w6_84
  have w7_88 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m7]; exact w6_88
  have w7_8c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m7]; exact w6_8c
  have w7_90 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m7]; exact w6_90
  have w7_94 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m7]; exact w6_94
  have w7_a20 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m7]; exact w6_a20
  have w7_a24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m7]; exact w6_a24
  have w7_a28 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m7]; exact w6_a28
  have w7_a2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m7]; exact w6_a2c
  have w7_a30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m7]; exact w6_a30
  have w7_a34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m7]; exact w6_a34
  have w7_a38 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m7]; exact w6_a38
  have w7_a3c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m7]; exact w6_a3c
  have w7_a40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m7]; exact w6_a40
  have w7_a44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m7]; exact w6_a44
  clear w6_a44 w6_a40 w6_a3c w6_a38 w6_a34 w6_a30 w6_a2c w6_a28 w6_a24 w6_a20 w6_94 w6_90 w6_8c w6_88 w6_84 w6_80 w6_7c w6_78 w6_74 w6_70 w6_6c w6_68 w6_64 w6_60 w6_5c w6_58 w6_54 w6_50 w6_4c w6_48 w6_40 w6_3c w6_38 w6_34 w6_30 g6_13 g6_10 g6_27 g6_26 g6_25 g6_21 g6_19 g6_18 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 rb6 s6 m6 u6 c6
  -- 0x6C2
  obtain ⟨n8, c8, u8⟩ := s7.block svDp06c2 E7.self svDp06c2_end
    ⟨trivial, trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem SV n8 0x6CA (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock svDp06c2 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
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
  have g8_8 : reg n8 (8 : Fin 32) = op := by
    rw [rb8, runBlock_reg _ _ _ (8 : Fin 32) s7.zero (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = x9 := by
    rw [rb8, runBlock_reg _ _ _ (9 : Fin 32) s7.zero (by decide), g7_9]
  have g8_10 : reg n8 a0 = op := by
    rw [rb8, runBlock_reg _ _ _ a0 s7.zero (by decide), g7_10]
  have g8_11 : reg n8 a1 = ol := by
    rw [rb8, runBlock_reg _ _ _ a1 s7.zero (by decide), g7_11]
  have g8_13 : reg n8 a3 = BitVec.ofNat 32 0x3 := by
    rw [rb8, runBlock_reg _ _ _ a3 s7.zero (by decide), g7_13]
  have g8_18 : reg n8 (18 : Fin 32) = out := by
    rw [rb8, runBlock_reg _ _ _ (18 : Fin 32) s7.zero (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by
    rw [rb8, runBlock_reg _ _ _ (19 : Fin 32) s7.zero (by decide), g7_19]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by
    rw [rb8, runBlock_reg _ _ _ (21 : Fin 32) s7.zero (by decide), g7_21]
  have g8_25 : reg n8 (25 : Fin 32) = x25 := by
    rw [rb8, runBlock_reg _ _ _ (25 : Fin 32) s7.zero (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by
    rw [rb8, runBlock_reg _ _ _ (26 : Fin 32) s7.zero (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb8, runBlock_reg _ _ _ (27 : Fin 32) s7.zero (by decide), g7_27]
  have g8_12 : reg n8 a2 = BitVec.ofNat 32 0x3FCC4892 := by
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svDp06c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_11, g7_13, g7_18, g7_19, g7_21, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk8 : SvKeepL B n0.mem n8.mem [] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m8]; exact w7_30
  have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m8]; exact w7_34
  have w8_38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m8]; exact w7_38
  have w8_3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m8]; exact w7_3c
  have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m8]; exact w7_40
  have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m8]; exact w7_48
  have w8_4c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m8]; exact w7_4c
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m8]; exact w7_50
  have w8_54 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m8]; exact w7_54
  have w8_58 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m8]; exact w7_58
  have w8_5c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m8]; exact w7_5c
  have w8_60 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m8]; exact w7_60
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m8]; exact w7_64
  have w8_68 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m8]; exact w7_68
  have w8_6c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m8]; exact w7_6c
  have w8_70 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m8]; exact w7_70
  have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m8]; exact w7_74
  have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m8]; exact w7_78
  have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m8]; exact w7_7c
  have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m8]; exact w7_80
  have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m8]; exact w7_84
  have w8_88 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m8]; exact w7_88
  have w8_8c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m8]; exact w7_8c
  have w8_90 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m8]; exact w7_90
  have w8_94 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m8]; exact w7_94
  have w8_a20 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m8]; exact w7_a20
  have w8_a24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m8]; exact w7_a24
  have w8_a28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m8]; exact w7_a28
  have w8_a2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m8]; exact w7_a2c
  have w8_a30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m8]; exact w7_a30
  have w8_a34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m8]; exact w7_a34
  have w8_a38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m8]; exact w7_a38
  have w8_a3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m8]; exact w7_a3c
  have w8_a40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m8]; exact w7_a40
  have w8_a44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m8]; exact w7_a44
  clear w7_a44 w7_a40 w7_a3c w7_a38 w7_a34 w7_a30 w7_a2c w7_a28 w7_a24 w7_a20 w7_94 w7_90 w7_8c w7_88 w7_84 w7_80 w7_7c w7_78 w7_74 w7_70 w7_6c w7_68 w7_64 w7_60 w7_5c w7_58 w7_54 w7_50 w7_4c w7_48 w7_40 w7_3c w7_38 w7_34 w7_30 g7_11 g7_27 g7_26 g7_25 g7_21 g7_19 g7_18 g7_13 g7_10 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0x6CA: sv_seqEqF
  obtain ⟨n9, c9, s9, rk9, a0_9, K9, fr9⟩ := sv_seqEqF (pl := ol.toNat) (ql := 3)
    F E8 s8 sv_at_6ca sv_at_6ce (by decide) (by decide) g8_2
    g8_10 (by rw [g8_11, ofNat_toNat_self]) g8_12 g8_13 (.inl oid_in) (.inr ⟨by decide, by decide⟩)
  have t9 : Steps n0 n9 := t8.trans c9
  have fR9 : ∀ x, SvR B x → n9.mem x = M0 x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.keepL K9 (by decide)
  rw [sv_mbRo F fR8 (.inl oid_in), sv_mbRo F fR8 (.inr ⟨by decide, by decide⟩)] at a0_9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [rk9 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk9 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk9 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = op := by rw [rk9 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = x9 := by rw [rk9 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [rk9 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [rk9 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_19]
  have g9_21 : reg n9 (21 : Fin 32) = x21 := by rw [rk9 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_21]
  have g9_25 : reg n9 (25 : Fin 32) = x25 := by rw [rk9 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by rw [rk9 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk9 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g8_27]
  have keep_kk9 : SvKeepL B n0.mem n9.mem [] := keep_kk8.trans K9
  clear keep_kk8
  have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K9.w32 (by decide) (by decide)).trans w8_30
  have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K9.w32 (by decide) (by decide)).trans w8_34
  have w9_38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K9.w32 (by decide) (by decide)).trans w8_38
  have w9_3c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K9.w32 (by decide) (by decide)).trans w8_3c
  have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K9.w32 (by decide) (by decide)).trans w8_40
  have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K9.w32 (by decide) (by decide)).trans w8_48
  have w9_4c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K9.w32 (by decide) (by decide)).trans w8_4c
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K9.w32 (by decide) (by decide)).trans w8_50
  have w9_54 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K9.w32 (by decide) (by decide)).trans w8_54
  have w9_58 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K9.w32 (by decide) (by decide)).trans w8_58
  have w9_5c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K9.w32 (by decide) (by decide)).trans w8_5c
  have w9_60 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K9.w32 (by decide) (by decide)).trans w8_60
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K9.w32 (by decide) (by decide)).trans w8_64
  have w9_68 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K9.w32 (by decide) (by decide)).trans w8_68
  have w9_6c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K9.w32 (by decide) (by decide)).trans w8_6c
  have w9_70 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K9.w32 (by decide) (by decide)).trans w8_70
  have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K9.w32 (by decide) (by decide)).trans w8_74
  have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K9.w32 (by decide) (by decide)).trans w8_78
  have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K9.w32 (by decide) (by decide)).trans w8_7c
  have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K9.w32 (by decide) (by decide)).trans w8_80
  have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K9.w32 (by decide) (by decide)).trans w8_84
  have w9_88 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K9.w32 (by decide) (by decide)).trans w8_88
  have w9_8c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K9.w32 (by decide) (by decide)).trans w8_8c
  have w9_90 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K9.w32 (by decide) (by decide)).trans w8_90
  have w9_94 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K9.w32 (by decide) (by decide)).trans w8_94
  have w9_a20 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K9.w32 (by decide) (by decide)).trans w8_a20
  have w9_a24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K9.w32 (by decide) (by decide)).trans w8_a24
  have w9_a28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K9.w32 (by decide) (by decide)).trans w8_a28
  have w9_a2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K9.w32 (by decide) (by decide)).trans w8_a2c
  have w9_a30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K9.w32 (by decide) (by decide)).trans w8_a30
  have w9_a34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K9.w32 (by decide) (by decide)).trans w8_a34
  have w9_a38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K9.w32 (by decide) (by decide)).trans w8_a38
  have w9_a3c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K9.w32 (by decide) (by decide)).trans w8_a3c
  have w9_a40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K9.w32 (by decide) (by decide)).trans w8_a40
  have w9_a44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K9.w32 (by decide) (by decide)).trans w8_a44
  clear w8_a44 w8_a40 w8_a3c w8_a38 w8_a34 w8_a30 w8_a2c w8_a28 w8_a24 w8_a20 w8_94 w8_90 w8_8c w8_88 w8_84 w8_80 w8_7c w8_78 w8_74 w8_70 w8_6c w8_68 w8_64 w8_60 w8_5c w8_58 w8_54 w8_50 w8_4c w8_48 w8_40 w8_3c w8_38 w8_34 w8_30 g8_12 g8_27 g8_26 g8_25 g8_21 g8_19 g8_18 g8_13 g8_11 g8_10 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 rb8 s8 m8 u8 c8
  have g9_10 : reg n9 a0 = BitVec.ofNat 32 0 := by rw [a0_9, ite_eq_right heku]; rfl
  -- 0x6D2: branch, taken
  obtain ⟨n10, d10, u10⟩ := s9.taken E9.self 0x78E sv_at_6d2
    (by decide) (by rw [g9_10, s9.zero]; decide)
  have s10 : St n10.mem SV n10 0x78E (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = op := by rw [u10.regs, g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = x9 := by rw [u10.regs, g9_9]
  have g10_10 : reg n10 a0 = BitVec.ofNat 32 0x0 := by rw [u10.regs, g9_10]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, g9_19]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [u10.regs, g9_21]
  have g10_25 : reg n10 (25 : Fin 32) = x25 := by rw [u10.regs, g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [u10.regs, g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u10.regs, g9_27]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m10]; exact w9_30
  have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m10]; exact w9_34
  have w10_38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m10]; exact w9_38
  have w10_3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m10]; exact w9_3c
  have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m10]; exact w9_40
  have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m10]; exact w9_48
  have w10_4c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m10]; exact w9_4c
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m10]; exact w9_50
  have w10_54 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m10]; exact w9_54
  have w10_58 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m10]; exact w9_58
  have w10_5c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m10]; exact w9_5c
  have w10_60 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m10]; exact w9_60
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m10]; exact w9_64
  have w10_68 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m10]; exact w9_68
  have w10_6c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m10]; exact w9_6c
  have w10_70 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m10]; exact w9_70
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m10]; exact w9_74
  have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m10]; exact w9_78
  have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m10]; exact w9_7c
  have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m10]; exact w9_80
  have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m10]; exact w9_84
  have w10_88 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m10]; exact w9_88
  have w10_8c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m10]; exact w9_8c
  have w10_90 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m10]; exact w9_90
  have w10_94 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m10]; exact w9_94
  have w10_a20 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m10]; exact w9_a20
  have w10_a24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m10]; exact w9_a24
  have w10_a28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m10]; exact w9_a28
  have w10_a2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m10]; exact w9_a2c
  have w10_a30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m10]; exact w9_a30
  have w10_a34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m10]; exact w9_a34
  have w10_a38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m10]; exact w9_a38
  have w10_a3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m10]; exact w9_a3c
  have w10_a40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m10]; exact w9_a40
  have w10_a44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m10]; exact w9_a44
  clear w9_a44 w9_a40 w9_a3c w9_a38 w9_a34 w9_a30 w9_a2c w9_a28 w9_a24 w9_a20 w9_94 w9_90 w9_8c w9_88 w9_84 w9_80 w9_7c w9_78 w9_74 w9_70 w9_6c w9_68 w9_64 w9_60 w9_5c w9_58 w9_54 w9_50 w9_4c w9_48 w9_40 w9_3c w9_38 w9_34 w9_30 g9_27 g9_26 g9_25 g9_21 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 K9 a0_9 rk9 s9 c9
  -- 0x78E
  obtain ⟨n11, c11, u11⟩ := s10.block svDp078e E10.self svDp078e_end
    ⟨trivial, trivial, trivial⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have s11 : St n11.mem SV n11 0x792 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have rb11 : ∀ q, reg n11 q = (runBlock svDp078e (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
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
  have g11_8 : reg n11 (8 : Fin 32) = op := by
    rw [rb11, runBlock_reg _ _ _ (8 : Fin 32) s10.zero (by decide), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = x9 := by
    rw [rb11, runBlock_reg _ _ _ (9 : Fin 32) s10.zero (by decide), g10_9]
  have g11_18 : reg n11 (18 : Fin 32) = out := by
    rw [rb11, runBlock_reg _ _ _ (18 : Fin 32) s10.zero (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by
    rw [rb11, runBlock_reg _ _ _ (19 : Fin 32) s10.zero (by decide), g10_19]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by
    rw [rb11, runBlock_reg _ _ _ (21 : Fin 32) s10.zero (by decide), g10_21]
  have g11_25 : reg n11 (25 : Fin 32) = x25 := by
    rw [rb11, runBlock_reg _ _ _ (25 : Fin 32) s10.zero (by decide), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by
    rw [rb11, runBlock_reg _ _ _ (26 : Fin 32) s10.zero (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb11, runBlock_reg _ _ _ (27 : Fin 32) s10.zero (by decide), g10_27]
  have g11_10 : reg n11 a0 = op := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, svDp078e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_8, g10_9, g10_10, g10_18, g10_19, g10_21, g10_25, g10_26, g10_27, s10.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g11_13 : reg n11 a3 = BitVec.ofNat 32 0x3 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, svDp078e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_8, g10_9, g10_10, g10_18, g10_19, g10_21, g10_25, g10_26, g10_27, s10.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk11 : SvKeepL B n0.mem n11.mem [] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m11]; exact w10_30
  have w11_34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m11]; exact w10_34
  have w11_38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m11]; exact w10_38
  have w11_3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m11]; exact w10_3c
  have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m11]; exact w10_40
  have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m11]; exact w10_48
  have w11_4c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m11]; exact w10_4c
  have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m11]; exact w10_50
  have w11_54 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m11]; exact w10_54
  have w11_58 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m11]; exact w10_58
  have w11_5c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m11]; exact w10_5c
  have w11_60 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m11]; exact w10_60
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m11]; exact w10_64
  have w11_68 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m11]; exact w10_68
  have w11_6c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m11]; exact w10_6c
  have w11_70 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m11]; exact w10_70
  have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m11]; exact w10_74
  have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m11]; exact w10_78
  have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m11]; exact w10_7c
  have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m11]; exact w10_80
  have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m11]; exact w10_84
  have w11_88 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m11]; exact w10_88
  have w11_8c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m11]; exact w10_8c
  have w11_90 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m11]; exact w10_90
  have w11_94 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m11]; exact w10_94
  have w11_a20 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m11]; exact w10_a20
  have w11_a24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m11]; exact w10_a24
  have w11_a28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m11]; exact w10_a28
  have w11_a2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m11]; exact w10_a2c
  have w11_a30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m11]; exact w10_a30
  have w11_a34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m11]; exact w10_a34
  have w11_a38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m11]; exact w10_a38
  have w11_a3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m11]; exact w10_a3c
  have w11_a40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m11]; exact w10_a40
  have w11_a44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m11]; exact w10_a44
  clear w10_a44 w10_a40 w10_a3c w10_a38 w10_a34 w10_a30 w10_a2c w10_a28 w10_a24 w10_a20 w10_94 w10_90 w10_8c w10_88 w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 w10_60 w10_5c w10_58 w10_54 w10_50 w10_4c w10_48 w10_40 w10_3c w10_38 w10_34 w10_30 g10_27 g10_26 g10_25 g10_21 g10_19 g10_18 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10 g9_10
  -- 0x792: lw
  obtain ⟨n12, d12, u12⟩ := s11.lw E11.self sv_at_792 (off' := 0x794) (by decide)
    (by rw [g11_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s12 : St n12.mem SV n12 0x794 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = op := by rw [u12.regs, upd_ne (by decide) (by decide), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = x9 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_9]
  have g12_10 : reg n12 a0 = op := by rw [u12.regs, upd_ne (by decide) (by decide), g11_10]
  have g12_13 : reg n12 a3 = BitVec.ofNat 32 0x3 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_13]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
  have g12_25 : reg n12 (25 : Fin 32) = x25 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_27]
  have g12_11 : reg n12 a1 = ol := by
    rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g11_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w11_48]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m12]; exact w11_30
  have w12_34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m12]; exact w11_34
  have w12_38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m12]; exact w11_38
  have w12_3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m12]; exact w11_3c
  have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m12]; exact w11_40
  have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m12]; exact w11_48
  have w12_4c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m12]; exact w11_4c
  have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m12]; exact w11_50
  have w12_54 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m12]; exact w11_54
  have w12_58 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m12]; exact w11_58
  have w12_5c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m12]; exact w11_5c
  have w12_60 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m12]; exact w11_60
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m12]; exact w11_64
  have w12_68 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m12]; exact w11_68
  have w12_6c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m12]; exact w11_6c
  have w12_70 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m12]; exact w11_70
  have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m12]; exact w11_74
  have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m12]; exact w11_78
  have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m12]; exact w11_7c
  have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m12]; exact w11_80
  have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m12]; exact w11_84
  have w12_88 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m12]; exact w11_88
  have w12_8c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m12]; exact w11_8c
  have w12_90 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m12]; exact w11_90
  have w12_94 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m12]; exact w11_94
  have w12_a20 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m12]; exact w11_a20
  have w12_a24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m12]; exact w11_a24
  have w12_a28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m12]; exact w11_a28
  have w12_a2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m12]; exact w11_a2c
  have w12_a30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m12]; exact w11_a30
  have w12_a34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m12]; exact w11_a34
  have w12_a38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m12]; exact w11_a38
  have w12_a3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m12]; exact w11_a3c
  have w12_a40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m12]; exact w11_a40
  have w12_a44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m12]; exact w11_a44
  clear w11_a44 w11_a40 w11_a3c w11_a38 w11_a34 w11_a30 w11_a2c w11_a28 w11_a24 w11_a20 w11_94 w11_90 w11_8c w11_88 w11_84 w11_80 w11_7c w11_78 w11_74 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c w11_58 w11_54 w11_50 w11_4c w11_48 w11_40 w11_3c w11_38 w11_34 w11_30 g11_13 g11_10 g11_27 g11_26 g11_25 g11_21 g11_19 g11_18 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 rb11 s11 m11 u11 c11
  -- 0x794
  obtain ⟨n13, c13, u13⟩ := s12.block svDp0794 E12.self svDp0794_end
    ⟨trivial, trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem SV n13 0x79C (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock svDp0794 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
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
  have g13_8 : reg n13 (8 : Fin 32) = op := by
    rw [rb13, runBlock_reg _ _ _ (8 : Fin 32) s12.zero (by decide), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = x9 := by
    rw [rb13, runBlock_reg _ _ _ (9 : Fin 32) s12.zero (by decide), g12_9]
  have g13_10 : reg n13 a0 = op := by
    rw [rb13, runBlock_reg _ _ _ a0 s12.zero (by decide), g12_10]
  have g13_11 : reg n13 a1 = ol := by
    rw [rb13, runBlock_reg _ _ _ a1 s12.zero (by decide), g12_11]
  have g13_13 : reg n13 a3 = BitVec.ofNat 32 0x3 := by
    rw [rb13, runBlock_reg _ _ _ a3 s12.zero (by decide), g12_13]
  have g13_18 : reg n13 (18 : Fin 32) = out := by
    rw [rb13, runBlock_reg _ _ _ (18 : Fin 32) s12.zero (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by
    rw [rb13, runBlock_reg _ _ _ (19 : Fin 32) s12.zero (by decide), g12_19]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by
    rw [rb13, runBlock_reg _ _ _ (21 : Fin 32) s12.zero (by decide), g12_21]
  have g13_25 : reg n13 (25 : Fin 32) = x25 := by
    rw [rb13, runBlock_reg _ _ _ (25 : Fin 32) s12.zero (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by
    rw [rb13, runBlock_reg _ _ _ (26 : Fin 32) s12.zero (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb13, runBlock_reg _ _ _ (27 : Fin 32) s12.zero (by decide), g12_27]
  have g13_12 : reg n13 a2 = BitVec.ofNat 32 0x3FCC488F := by
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svDp0794, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_10, g12_11, g12_13, g12_18, g12_19, g12_21, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk13 : SvKeepL B n0.mem n13.mem [] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m13]; exact w12_30
  have w13_34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m13]; exact w12_34
  have w13_38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m13]; exact w12_38
  have w13_3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m13]; exact w12_3c
  have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m13]; exact w12_40
  have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m13]; exact w12_48
  have w13_4c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m13]; exact w12_4c
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m13]; exact w12_50
  have w13_54 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m13]; exact w12_54
  have w13_58 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m13]; exact w12_58
  have w13_5c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m13]; exact w12_5c
  have w13_60 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m13]; exact w12_60
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m13]; exact w12_64
  have w13_68 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m13]; exact w12_68
  have w13_6c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m13]; exact w12_6c
  have w13_70 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m13]; exact w12_70
  have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m13]; exact w12_74
  have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m13]; exact w12_78
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m13]; exact w12_7c
  have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m13]; exact w12_80
  have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m13]; exact w12_84
  have w13_88 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m13]; exact w12_88
  have w13_8c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m13]; exact w12_8c
  have w13_90 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m13]; exact w12_90
  have w13_94 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m13]; exact w12_94
  have w13_a20 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m13]; exact w12_a20
  have w13_a24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m13]; exact w12_a24
  have w13_a28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m13]; exact w12_a28
  have w13_a2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m13]; exact w12_a2c
  have w13_a30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m13]; exact w12_a30
  have w13_a34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m13]; exact w12_a34
  have w13_a38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m13]; exact w12_a38
  have w13_a3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m13]; exact w12_a3c
  have w13_a40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m13]; exact w12_a40
  have w13_a44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m13]; exact w12_a44
  clear w12_a44 w12_a40 w12_a3c w12_a38 w12_a34 w12_a30 w12_a2c w12_a28 w12_a24 w12_a20 w12_94 w12_90 w12_8c w12_88 w12_84 w12_80 w12_7c w12_78 w12_74 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c w12_58 w12_54 w12_50 w12_4c w12_48 w12_40 w12_3c w12_38 w12_34 w12_30 g12_11 g12_27 g12_26 g12_25 g12_21 g12_19 g12_18 g12_13 g12_10 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
  -- 0x79C: sv_seqEqF
  obtain ⟨n14, c14, s14, rk14, a0_14, K14, fr14⟩ := sv_seqEqF (pl := ol.toNat) (ql := 3)
    F E13 s13 sv_at_79c sv_at_7a0 (by decide) (by decide) g13_2
    g13_10 (by rw [g13_11, ofNat_toNat_self]) g13_12 g13_13 (.inl oid_in) (.inr ⟨by decide, by decide⟩)
  have t14 : Steps n0 n14 := t13.trans c14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keepL K14 (by decide)
  rw [sv_mbRo F fR13 (.inl oid_in), sv_mbRo F fR13 (.inr ⟨by decide, by decide⟩)] at a0_14
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [rk14 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk14 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk14 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = op := by rw [rk14 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = x9 := by rw [rk14 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_9]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [rk14 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [rk14 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_19]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [rk14 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_21]
  have g14_25 : reg n14 (25 : Fin 32) = x25 := by rw [rk14 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [rk14 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk14 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_27]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [] := keep_kk13.trans K14
  clear keep_kk13
  have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K14.w32 (by decide) (by decide)).trans w13_30
  have w14_34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K14.w32 (by decide) (by decide)).trans w13_34
  have w14_38 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K14.w32 (by decide) (by decide)).trans w13_38
  have w14_3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K14.w32 (by decide) (by decide)).trans w13_3c
  have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K14.w32 (by decide) (by decide)).trans w13_40
  have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K14.w32 (by decide) (by decide)).trans w13_48
  have w14_4c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K14.w32 (by decide) (by decide)).trans w13_4c
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K14.w32 (by decide) (by decide)).trans w13_50
  have w14_54 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K14.w32 (by decide) (by decide)).trans w13_54
  have w14_58 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K14.w32 (by decide) (by decide)).trans w13_58
  have w14_5c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K14.w32 (by decide) (by decide)).trans w13_5c
  have w14_60 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K14.w32 (by decide) (by decide)).trans w13_60
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K14.w32 (by decide) (by decide)).trans w13_64
  have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K14.w32 (by decide) (by decide)).trans w13_68
  have w14_6c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K14.w32 (by decide) (by decide)).trans w13_6c
  have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K14.w32 (by decide) (by decide)).trans w13_70
  have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K14.w32 (by decide) (by decide)).trans w13_74
  have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K14.w32 (by decide) (by decide)).trans w13_78
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K14.w32 (by decide) (by decide)).trans w13_7c
  have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K14.w32 (by decide) (by decide)).trans w13_80
  have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K14.w32 (by decide) (by decide)).trans w13_84
  have w14_88 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K14.w32 (by decide) (by decide)).trans w13_88
  have w14_8c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K14.w32 (by decide) (by decide)).trans w13_8c
  have w14_90 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K14.w32 (by decide) (by decide)).trans w13_90
  have w14_94 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K14.w32 (by decide) (by decide)).trans w13_94
  have w14_a20 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K14.w32 (by decide) (by decide)).trans w13_a20
  have w14_a24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K14.w32 (by decide) (by decide)).trans w13_a24
  have w14_a28 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K14.w32 (by decide) (by decide)).trans w13_a28
  have w14_a2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K14.w32 (by decide) (by decide)).trans w13_a2c
  have w14_a30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K14.w32 (by decide) (by decide)).trans w13_a30
  have w14_a34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K14.w32 (by decide) (by decide)).trans w13_a34
  have w14_a38 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K14.w32 (by decide) (by decide)).trans w13_a38
  have w14_a3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K14.w32 (by decide) (by decide)).trans w13_a3c
  have w14_a40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K14.w32 (by decide) (by decide)).trans w13_a40
  have w14_a44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K14.w32 (by decide) (by decide)).trans w13_a44
  clear w13_a44 w13_a40 w13_a3c w13_a38 w13_a34 w13_a30 w13_a2c w13_a28 w13_a24 w13_a20 w13_94 w13_90 w13_8c w13_88 w13_84 w13_80 w13_7c w13_78 w13_74 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c w13_58 w13_54 w13_50 w13_4c w13_48 w13_40 w13_3c w13_38 w13_34 w13_30 g13_12 g13_27 g13_26 g13_25 g13_21 g13_19 g13_18 g13_13 g13_11 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 rb13 s13 m13 u13 c13
  have g14_10 : reg n14 a0 = BitVec.ofNat 32 0 := by rw [a0_14, ite_eq_right hbc]; rfl
  -- 0x7A4: branch, taken
  obtain ⟨n15, d15, u15⟩ := s14.taken E14.self 0x89C sv_at_7a4
    (by decide) (by rw [g14_10, s14.zero]; decide)
  have s15 : St n15.mem SV n15 0x89C (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = op := by rw [u15.regs, g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = x9 := by rw [u15.regs, g14_9]
  have g15_10 : reg n15 a0 = BitVec.ofNat 32 0x0 := by rw [u15.regs, g14_10]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, g14_19]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, g14_21]
  have g15_25 : reg n15 (25 : Fin 32) = x25 := by rw [u15.regs, g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u15.regs, g14_27]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m15]; exact w14_30
  have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m15]; exact w14_34
  have w15_38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m15]; exact w14_38
  have w15_3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m15]; exact w14_3c
  have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m15]; exact w14_40
  have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m15]; exact w14_48
  have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m15]; exact w14_4c
  have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m15]; exact w14_50
  have w15_54 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m15]; exact w14_54
  have w15_58 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m15]; exact w14_58
  have w15_5c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m15]; exact w14_5c
  have w15_60 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m15]; exact w14_60
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m15]; exact w14_64
  have w15_68 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m15]; exact w14_68
  have w15_6c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m15]; exact w14_6c
  have w15_70 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m15]; exact w14_70
  have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m15]; exact w14_74
  have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m15]; exact w14_78
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m15]; exact w14_7c
  have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m15]; exact w14_80
  have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m15]; exact w14_84
  have w15_88 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m15]; exact w14_88
  have w15_8c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m15]; exact w14_8c
  have w15_90 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m15]; exact w14_90
  have w15_94 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m15]; exact w14_94
  have w15_a20 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m15]; exact w14_a20
  have w15_a24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m15]; exact w14_a24
  have w15_a28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m15]; exact w14_a28
  have w15_a2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m15]; exact w14_a2c
  have w15_a30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m15]; exact w14_a30
  have w15_a34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m15]; exact w14_a34
  have w15_a38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m15]; exact w14_a38
  have w15_a3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m15]; exact w14_a3c
  have w15_a40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m15]; exact w14_a40
  have w15_a44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m15]; exact w14_a44
  clear w14_a44 w14_a40 w14_a3c w14_a38 w14_a34 w14_a30 w14_a2c w14_a28 w14_a24 w14_a20 w14_94 w14_90 w14_8c w14_88 w14_84 w14_80 w14_7c w14_78 w14_74 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c w14_58 w14_54 w14_50 w14_4c w14_48 w14_40 w14_3c w14_38 w14_34 w14_30 g14_27 g14_26 g14_25 g14_21 g14_19 g14_18 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 K14 a0_14 rk14 s14 c14
  -- 0x89C
  obtain ⟨n16, c16, u16⟩ := s15.block svDp089c E15.self svDp089c_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have s16 : St n16.mem SV n16 0x8A6 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have rb16 : ∀ q, reg n16 q = (runBlock svDp089c (n15.mem, reg n15)).2 q := fun q => by rw [u16.regs]
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
  have g16_8 : reg n16 (8 : Fin 32) = op := by
    rw [rb16, runBlock_reg _ _ _ (8 : Fin 32) s15.zero (by decide), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = x9 := by
    rw [rb16, runBlock_reg _ _ _ (9 : Fin 32) s15.zero (by decide), g15_9]
  have g16_10 : reg n16 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb16, runBlock_reg _ _ _ a0 s15.zero (by decide), g15_10]
  have g16_18 : reg n16 (18 : Fin 32) = out := by
    rw [rb16, runBlock_reg _ _ _ (18 : Fin 32) s15.zero (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by
    rw [rb16, runBlock_reg _ _ _ (19 : Fin 32) s15.zero (by decide), g15_19]
  have g16_21 : reg n16 (21 : Fin 32) = x21 := by
    rw [rb16, runBlock_reg _ _ _ (21 : Fin 32) s15.zero (by decide), g15_21]
  have g16_25 : reg n16 (25 : Fin 32) = x25 := by
    rw [rb16, runBlock_reg _ _ _ (25 : Fin 32) s15.zero (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by
    rw [rb16, runBlock_reg _ _ _ (26 : Fin 32) s15.zero (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb16, runBlock_reg _ _ _ (27 : Fin 32) s15.zero (by decide), g15_27]
  have g16_22 : reg n16 (22 : Fin 32) = BitVec.ofNat 32 0xFFFFFFFF := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, svDp089c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_8, g15_9, g15_10, g15_18, g15_19, g15_21, g15_25, g15_26, g15_27, s15.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g16_23 : reg n16 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48EC := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, svDp089c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_8, g15_9, g15_10, g15_18, g15_19, g15_21, g15_25, g15_26, g15_27, s15.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk16 : SvKeepL B n0.mem n16.mem [] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m16]; exact w15_30
  have w16_34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m16]; exact w15_34
  have w16_38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m16]; exact w15_38
  have w16_3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m16]; exact w15_3c
  have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m16]; exact w15_40
  have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m16]; exact w15_48
  have w16_4c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m16]; exact w15_4c
  have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m16]; exact w15_50
  have w16_54 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m16]; exact w15_54
  have w16_58 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m16]; exact w15_58
  have w16_5c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m16]; exact w15_5c
  have w16_60 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m16]; exact w15_60
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m16]; exact w15_64
  have w16_68 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m16]; exact w15_68
  have w16_6c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m16]; exact w15_6c
  have w16_70 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m16]; exact w15_70
  have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m16]; exact w15_74
  have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m16]; exact w15_78
  have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m16]; exact w15_7c
  have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m16]; exact w15_80
  have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m16]; exact w15_84
  have w16_88 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m16]; exact w15_88
  have w16_8c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m16]; exact w15_8c
  have w16_90 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m16]; exact w15_90
  have w16_94 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m16]; exact w15_94
  have w16_a20 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m16]; exact w15_a20
  have w16_a24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m16]; exact w15_a24
  have w16_a28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m16]; exact w15_a28
  have w16_a2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m16]; exact w15_a2c
  have w16_a30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m16]; exact w15_a30
  have w16_a34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m16]; exact w15_a34
  have w16_a38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m16]; exact w15_a38
  have w16_a3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m16]; exact w15_a3c
  have w16_a40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m16]; exact w15_a40
  have w16_a44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m16]; exact w15_a44
  clear w15_a44 w15_a40 w15_a3c w15_a38 w15_a34 w15_a30 w15_a2c w15_a28 w15_a24 w15_a20 w15_94 w15_90 w15_8c w15_88 w15_84 w15_80 w15_7c w15_78 w15_74 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c w15_58 w15_54 w15_50 w15_4c w15_48 w15_40 w15_3c w15_38 w15_34 w15_30 g15_27 g15_26 g15_25 g15_21 g15_19 g15_18 g15_10 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15 g14_10
  -- 0x8A6
  obtain ⟨n17, c17, u17⟩ := s16.block svDp08a6 E16.self svDp08a6_end
    ⟨trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem SV n17 0x8A8 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock svDp08a6 (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
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
  have g17_8 : reg n17 (8 : Fin 32) = op := by
    rw [rb17, runBlock_reg _ _ _ (8 : Fin 32) s16.zero (by decide), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = x9 := by
    rw [rb17, runBlock_reg _ _ _ (9 : Fin 32) s16.zero (by decide), g16_9]
  have g17_18 : reg n17 (18 : Fin 32) = out := by
    rw [rb17, runBlock_reg _ _ _ (18 : Fin 32) s16.zero (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by
    rw [rb17, runBlock_reg _ _ _ (19 : Fin 32) s16.zero (by decide), g16_19]
  have g17_21 : reg n17 (21 : Fin 32) = x21 := by
    rw [rb17, runBlock_reg _ _ _ (21 : Fin 32) s16.zero (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = BitVec.ofNat 32 0xFFFFFFFF := by
    rw [rb17, runBlock_reg _ _ _ (22 : Fin 32) s16.zero (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48EC := by
    rw [rb17, runBlock_reg _ _ _ (23 : Fin 32) s16.zero (by decide), g16_23]
  have g17_25 : reg n17 (25 : Fin 32) = x25 := by
    rw [rb17, runBlock_reg _ _ _ (25 : Fin 32) s16.zero (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by
    rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb17, runBlock_reg _ _ _ (27 : Fin 32) s16.zero (by decide), g16_27]
  have g17_10 : reg n17 a0 = BitVec.ofNat 32 0x4 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svDp08a6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_10, g16_18, g16_19, g16_21, g16_22, g16_23, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk17 : SvKeepL B n0.mem n17.mem [] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m17]; exact w16_30
  have w17_34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m17]; exact w16_34
  have w17_38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m17]; exact w16_38
  have w17_3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m17]; exact w16_3c
  have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m17]; exact w16_40
  have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m17]; exact w16_48
  have w17_4c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m17]; exact w16_4c
  have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m17]; exact w16_50
  have w17_54 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m17]; exact w16_54
  have w17_58 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m17]; exact w16_58
  have w17_5c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m17]; exact w16_5c
  have w17_60 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m17]; exact w16_60
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m17]; exact w16_64
  have w17_68 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m17]; exact w16_68
  have w17_6c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m17]; exact w16_6c
  have w17_70 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m17]; exact w16_70
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m17]; exact w16_74
  have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m17]; exact w16_78
  have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m17]; exact w16_7c
  have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m17]; exact w16_80
  have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m17]; exact w16_84
  have w17_88 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m17]; exact w16_88
  have w17_8c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m17]; exact w16_8c
  have w17_90 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m17]; exact w16_90
  have w17_94 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m17]; exact w16_94
  have w17_a20 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m17]; exact w16_a20
  have w17_a24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m17]; exact w16_a24
  have w17_a28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m17]; exact w16_a28
  have w17_a2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m17]; exact w16_a2c
  have w17_a30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m17]; exact w16_a30
  have w17_a34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m17]; exact w16_a34
  have w17_a38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m17]; exact w16_a38
  have w17_a3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m17]; exact w16_a3c
  have w17_a40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m17]; exact w16_a40
  have w17_a44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m17]; exact w16_a44
  clear w16_a44 w16_a40 w16_a3c w16_a38 w16_a34 w16_a30 w16_a2c w16_a28 w16_a24 w16_a20 w16_94 w16_90 w16_8c w16_88 w16_84 w16_80 w16_7c w16_78 w16_74 w16_70 w16_6c w16_68 w16_64 w16_60 w16_5c w16_58 w16_54 w16_50 w16_4c w16_48 w16_40 w16_3c w16_38 w16_34 w16_30 g16_23 g16_22 g16_27 g16_26 g16_25 g16_21 g16_19 g16_18 g16_10 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 rb16 s16 m16 u16 c16
  -- 0x8A8: branch, not taken
  obtain ⟨n18, d18, u18⟩ := s17.notTaken E17.self 0x8AC sv_at_8a8
    (by decide) (by rw [g17_22, g17_10]; decide)
  have s18 : St n18.mem SV n18 0x8AC (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans (.single d18)
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = op := by rw [u18.regs, g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = x9 := by rw [u18.regs, g17_9]
  have g18_10 : reg n18 a0 = BitVec.ofNat 32 0x4 := by rw [u18.regs, g17_10]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, g17_19]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [u18.regs, g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = BitVec.ofNat 32 0xFFFFFFFF := by rw [u18.regs, g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48EC := by rw [u18.regs, g17_23]
  have g18_25 : reg n18 (25 : Fin 32) = x25 := by rw [u18.regs, g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [u18.regs, g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u18.regs, g17_27]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m18]; exact w17_30
  have w18_34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m18]; exact w17_34
  have w18_38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m18]; exact w17_38
  have w18_3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m18]; exact w17_3c
  have w18_40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m18]; exact w17_40
  have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m18]; exact w17_48
  have w18_4c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m18]; exact w17_4c
  have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m18]; exact w17_50
  have w18_54 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m18]; exact w17_54
  have w18_58 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m18]; exact w17_58
  have w18_5c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m18]; exact w17_5c
  have w18_60 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m18]; exact w17_60
  have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m18]; exact w17_64
  have w18_68 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m18]; exact w17_68
  have w18_6c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m18]; exact w17_6c
  have w18_70 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m18]; exact w17_70
  have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m18]; exact w17_74
  have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m18]; exact w17_78
  have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m18]; exact w17_7c
  have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m18]; exact w17_80
  have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m18]; exact w17_84
  have w18_88 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m18]; exact w17_88
  have w18_8c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m18]; exact w17_8c
  have w18_90 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m18]; exact w17_90
  have w18_94 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m18]; exact w17_94
  have w18_a20 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m18]; exact w17_a20
  have w18_a24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m18]; exact w17_a24
  have w18_a28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m18]; exact w17_a28
  have w18_a2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m18]; exact w17_a2c
  have w18_a30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m18]; exact w17_a30
  have w18_a34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m18]; exact w17_a34
  have w18_a38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m18]; exact w17_a38
  have w18_a3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m18]; exact w17_a3c
  have w18_a40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m18]; exact w17_a40
  have w18_a44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m18]; exact w17_a44
  clear w17_a44 w17_a40 w17_a3c w17_a38 w17_a34 w17_a30 w17_a2c w17_a28 w17_a24 w17_a20 w17_94 w17_90 w17_8c w17_88 w17_84 w17_80 w17_7c w17_78 w17_74 w17_70 w17_6c w17_68 w17_64 w17_60 w17_5c w17_58 w17_54 w17_50 w17_4c w17_48 w17_40 w17_3c w17_38 w17_34 w17_30 g17_10 g17_27 g17_26 g17_25 g17_23 g17_22 g17_21 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
  -- 0x8AC: lw of a constant
  obtain ⟨n19, d19, u19⟩ := s18.lw E18.self sv_at_8ac (off' := 0x8B0) (by decide)
    (by rw [g18_23]; decide)
  have s19 : St n19.mem SV n19 0x8B0 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans (.single d19)
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = op := by rw [u19.regs, upd_ne (by decide) (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = x9 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = BitVec.ofNat 32 0xFFFFFFFF := by rw [u19.regs, upd_ne (by decide) (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48EC := by rw [u19.regs, upd_ne (by decide) (by decide), g18_23]
  have g19_25 : reg n19 (25 : Fin 32) = x25 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
  have g19_10 : reg n19 a0 = BitVec.ofNat 32 0x3FCC48B8 := by
    rw [u19.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g18_23, show BitVec.ofNat 32 0x3FCC48EC + 0x0 = SVK + BitVec.ofNat 32 0xD4 by decide]
    exact (SvData.sv F SD0 fR18).w32 (by decide) (by decide)
  have keep_kk19 : SvKeepL B n0.mem n19.mem [] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m19]; exact w18_30
  have w19_34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m19]; exact w18_34
  have w19_38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m19]; exact w18_38
  have w19_3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m19]; exact w18_3c
  have w19_40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m19]; exact w18_40
  have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m19]; exact w18_48
  have w19_4c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m19]; exact w18_4c
  have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m19]; exact w18_50
  have w19_54 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m19]; exact w18_54
  have w19_58 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m19]; exact w18_58
  have w19_5c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m19]; exact w18_5c
  have w19_60 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m19]; exact w18_60
  have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m19]; exact w18_64
  have w19_68 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m19]; exact w18_68
  have w19_6c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m19]; exact w18_6c
  have w19_70 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m19]; exact w18_70
  have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m19]; exact w18_74
  have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m19]; exact w18_78
  have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m19]; exact w18_7c
  have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m19]; exact w18_80
  have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m19]; exact w18_84
  have w19_88 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m19]; exact w18_88
  have w19_8c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m19]; exact w18_8c
  have w19_90 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m19]; exact w18_90
  have w19_94 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m19]; exact w18_94
  have w19_a20 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m19]; exact w18_a20
  have w19_a24 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m19]; exact w18_a24
  have w19_a28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m19]; exact w18_a28
  have w19_a2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m19]; exact w18_a2c
  have w19_a30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m19]; exact w18_a30
  have w19_a34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m19]; exact w18_a34
  have w19_a38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m19]; exact w18_a38
  have w19_a3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m19]; exact w18_a3c
  have w19_a40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m19]; exact w18_a40
  have w19_a44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m19]; exact w18_a44
  clear w18_a44 w18_a40 w18_a3c w18_a38 w18_a34 w18_a30 w18_a2c w18_a28 w18_a24 w18_a20 w18_94 w18_90 w18_8c w18_88 w18_84 w18_80 w18_7c w18_78 w18_74 w18_70 w18_6c w18_68 w18_64 w18_60 w18_5c w18_58 w18_54 w18_50 w18_4c w18_48 w18_40 w18_3c w18_38 w18_34 w18_30 g18_27 g18_26 g18_25 g18_23 g18_22 g18_21 g18_19 g18_18 g18_10 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
  -- 0x8B0
  obtain ⟨n20, c20, u20⟩ := s19.block svDp08b0 E19.self svDp08b0_end
    ⟨trivial, trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem SV n20 0x8B4 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock svDp08b0 (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
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
  have g20_8 : reg n20 (8 : Fin 32) = op := by
    rw [rb20, runBlock_reg _ _ _ (8 : Fin 32) s19.zero (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = x9 := by
    rw [rb20, runBlock_reg _ _ _ (9 : Fin 32) s19.zero (by decide), g19_9]
  have g20_10 : reg n20 a0 = BitVec.ofNat 32 0x3FCC48B8 := by
    rw [rb20, runBlock_reg _ _ _ a0 s19.zero (by decide), g19_10]
  have g20_18 : reg n20 (18 : Fin 32) = out := by
    rw [rb20, runBlock_reg _ _ _ (18 : Fin 32) s19.zero (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by
    rw [rb20, runBlock_reg _ _ _ (19 : Fin 32) s19.zero (by decide), g19_19]
  have g20_21 : reg n20 (21 : Fin 32) = x21 := by
    rw [rb20, runBlock_reg _ _ _ (21 : Fin 32) s19.zero (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = BitVec.ofNat 32 0xFFFFFFFF := by
    rw [rb20, runBlock_reg _ _ _ (22 : Fin 32) s19.zero (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48EC := by
    rw [rb20, runBlock_reg _ _ _ (23 : Fin 32) s19.zero (by decide), g19_23]
  have g20_25 : reg n20 (25 : Fin 32) = x25 := by
    rw [rb20, runBlock_reg _ _ _ (25 : Fin 32) s19.zero (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by
    rw [rb20, runBlock_reg _ _ _ (26 : Fin 32) s19.zero (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb20, runBlock_reg _ _ _ (27 : Fin 32) s19.zero (by decide), g19_27]
  have g20_11 : reg n20 a1 = BitVec.ofNat 32 0xA := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svDp08b0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_18, g19_19, g19_21, g19_22, g19_23, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g20_12 : reg n20 a2 = op := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svDp08b0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_18, g19_19, g19_21, g19_22, g19_23, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk20 : SvKeepL B n0.mem n20.mem [] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m20]; exact w19_30
  have w20_34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m20]; exact w19_34
  have w20_38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m20]; exact w19_38
  have w20_3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m20]; exact w19_3c
  have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m20]; exact w19_40
  have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m20]; exact w19_48
  have w20_4c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m20]; exact w19_4c
  have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m20]; exact w19_50
  have w20_54 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m20]; exact w19_54
  have w20_58 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m20]; exact w19_58
  have w20_5c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m20]; exact w19_5c
  have w20_60 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m20]; exact w19_60
  have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m20]; exact w19_64
  have w20_68 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m20]; exact w19_68
  have w20_6c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m20]; exact w19_6c
  have w20_70 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m20]; exact w19_70
  have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m20]; exact w19_74
  have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m20]; exact w19_78
  have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m20]; exact w19_7c
  have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m20]; exact w19_80
  have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m20]; exact w19_84
  have w20_88 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m20]; exact w19_88
  have w20_8c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m20]; exact w19_8c
  have w20_90 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m20]; exact w19_90
  have w20_94 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m20]; exact w19_94
  have w20_a20 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m20]; exact w19_a20
  have w20_a24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m20]; exact w19_a24
  have w20_a28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m20]; exact w19_a28
  have w20_a2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m20]; exact w19_a2c
  have w20_a30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m20]; exact w19_a30
  have w20_a34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m20]; exact w19_a34
  have w20_a38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m20]; exact w19_a38
  have w20_a3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m20]; exact w19_a3c
  have w20_a40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m20]; exact w19_a40
  have w20_a44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m20]; exact w19_a44
  clear w19_a44 w19_a40 w19_a3c w19_a38 w19_a34 w19_a30 w19_a2c w19_a28 w19_a24 w19_a20 w19_94 w19_90 w19_8c w19_88 w19_84 w19_80 w19_7c w19_78 w19_74 w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c w19_58 w19_54 w19_50 w19_4c w19_48 w19_40 w19_3c w19_38 w19_34 w19_30 g19_10 g19_27 g19_26 g19_25 g19_23 g19_22 g19_21 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
  -- 0x8B4: lw
  obtain ⟨n21, d21, u21⟩ := s20.lw E20.self sv_at_8b4 (off' := 0x8B6) (by decide)
    (by rw [g20_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s21 : St n21.mem SV n21 0x8B6 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans (.single d21)
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, upd_ne (by decide) (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = op := by rw [u21.regs, upd_ne (by decide) (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = x9 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_9]
  have g21_10 : reg n21 a0 = BitVec.ofNat 32 0x3FCC48B8 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_10]
  have g21_11 : reg n21 a1 = BitVec.ofNat 32 0xA := by rw [u21.regs, upd_ne (by decide) (by decide), g20_11]
  have g21_12 : reg n21 a2 = op := by rw [u21.regs, upd_ne (by decide) (by decide), g20_12]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, upd_ne (by decide) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, upd_ne (by decide) (by decide), g20_19]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = BitVec.ofNat 32 0xFFFFFFFF := by rw [u21.regs, upd_ne (by decide) (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48EC := by rw [u21.regs, upd_ne (by decide) (by decide), g20_23]
  have g21_25 : reg n21 (25 : Fin 32) = x25 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u21.regs, upd_ne (by decide) (by decide), g20_27]
  have g21_13 : reg n21 a3 = ol := by
    rw [u21.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g20_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w20_48]
  have keep_kk21 : SvKeepL B n0.mem n21.mem [] := by rw [m21]; exact keep_kk20
  clear keep_kk20
  have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m21]; exact w20_30
  have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m21]; exact w20_34
  have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m21]; exact w20_38
  have w21_3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m21]; exact w20_3c
  have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m21]; exact w20_40
  have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m21]; exact w20_48
  have w21_4c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m21]; exact w20_4c
  have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m21]; exact w20_50
  have w21_54 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m21]; exact w20_54
  have w21_58 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m21]; exact w20_58
  have w21_5c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m21]; exact w20_5c
  have w21_60 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m21]; exact w20_60
  have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m21]; exact w20_64
  have w21_68 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m21]; exact w20_68
  have w21_6c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m21]; exact w20_6c
  have w21_70 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m21]; exact w20_70
  have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m21]; exact w20_74
  have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m21]; exact w20_78
  have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m21]; exact w20_7c
  have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m21]; exact w20_80
  have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m21]; exact w20_84
  have w21_88 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m21]; exact w20_88
  have w21_8c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m21]; exact w20_8c
  have w21_90 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m21]; exact w20_90
  have w21_94 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m21]; exact w20_94
  have w21_a20 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m21]; exact w20_a20
  have w21_a24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m21]; exact w20_a24
  have w21_a28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m21]; exact w20_a28
  have w21_a2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m21]; exact w20_a2c
  have w21_a30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m21]; exact w20_a30
  have w21_a34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m21]; exact w20_a34
  have w21_a38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m21]; exact w20_a38
  have w21_a3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m21]; exact w20_a3c
  have w21_a40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m21]; exact w20_a40
  have w21_a44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m21]; exact w20_a44
  clear w20_a44 w20_a40 w20_a3c w20_a38 w20_a34 w20_a30 w20_a2c w20_a28 w20_a24 w20_a20 w20_94 w20_90 w20_8c w20_88 w20_84 w20_80 w20_7c w20_78 w20_74 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c w20_58 w20_54 w20_50 w20_4c w20_48 w20_40 w20_3c w20_38 w20_34 w20_30 g20_12 g20_11 g20_27 g20_26 g20_25 g20_23 g20_22 g20_21 g20_19 g20_18 g20_10 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 rb20 s20 m20 u20 c20
  -- 0x8B6: sv_seqEqF
  obtain ⟨n22, c22, s22, rk22, a0_22, K22, fr22⟩ := sv_seqEqF (pl := 10) (ql := ol.toNat)
    F E21 s21 sv_at_8b6 sv_at_8ba (by decide) (by decide) g21_2
    g21_10 g21_11 g21_12 (by rw [g21_13, ofNat_toNat_self]) (.inr ⟨by decide, by decide⟩) (.inl oid_in)
  have t22 : Steps n0 n22 := t21.trans c22
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.keepL K22 (by decide)
  rw [sv_mbRo F fR21 (.inr ⟨by decide, by decide⟩), sv_mbRo F fR21 (.inl oid_in)] at a0_22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [rk22 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk22 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk22 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = op := by rw [rk22 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = x9 := by rw [rk22 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g21_9]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [rk22 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [rk22 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g21_19]
  have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [rk22 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = BitVec.ofNat 32 0xFFFFFFFF := by rw [rk22 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48EC := by rw [rk22 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g21_23]
  have g22_25 : reg n22 (25 : Fin 32) = x25 := by rw [rk22 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [rk22 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk22 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g21_27]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [] := keep_kk21.trans K22
  clear keep_kk21
  have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K22.w32 (by decide) (by decide)).trans w21_30
  have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K22.w32 (by decide) (by decide)).trans w21_34
  have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K22.w32 (by decide) (by decide)).trans w21_38
  have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K22.w32 (by decide) (by decide)).trans w21_3c
  have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K22.w32 (by decide) (by decide)).trans w21_40
  have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K22.w32 (by decide) (by decide)).trans w21_48
  have w22_4c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K22.w32 (by decide) (by decide)).trans w21_4c
  have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K22.w32 (by decide) (by decide)).trans w21_50
  have w22_54 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K22.w32 (by decide) (by decide)).trans w21_54
  have w22_58 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K22.w32 (by decide) (by decide)).trans w21_58
  have w22_5c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K22.w32 (by decide) (by decide)).trans w21_5c
  have w22_60 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K22.w32 (by decide) (by decide)).trans w21_60
  have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K22.w32 (by decide) (by decide)).trans w21_64
  have w22_68 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K22.w32 (by decide) (by decide)).trans w21_68
  have w22_6c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K22.w32 (by decide) (by decide)).trans w21_6c
  have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K22.w32 (by decide) (by decide)).trans w21_70
  have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K22.w32 (by decide) (by decide)).trans w21_74
  have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K22.w32 (by decide) (by decide)).trans w21_78
  have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K22.w32 (by decide) (by decide)).trans w21_7c
  have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K22.w32 (by decide) (by decide)).trans w21_80
  have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K22.w32 (by decide) (by decide)).trans w21_84
  have w22_88 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K22.w32 (by decide) (by decide)).trans w21_88
  have w22_8c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K22.w32 (by decide) (by decide)).trans w21_8c
  have w22_90 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K22.w32 (by decide) (by decide)).trans w21_90
  have w22_94 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K22.w32 (by decide) (by decide)).trans w21_94
  have w22_a20 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K22.w32 (by decide) (by decide)).trans w21_a20
  have w22_a24 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K22.w32 (by decide) (by decide)).trans w21_a24
  have w22_a28 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K22.w32 (by decide) (by decide)).trans w21_a28
  have w22_a2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K22.w32 (by decide) (by decide)).trans w21_a2c
  have w22_a30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K22.w32 (by decide) (by decide)).trans w21_a30
  have w22_a34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K22.w32 (by decide) (by decide)).trans w21_a34
  have w22_a38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K22.w32 (by decide) (by decide)).trans w21_a38
  have w22_a3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K22.w32 (by decide) (by decide)).trans w21_a3c
  have w22_a40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K22.w32 (by decide) (by decide)).trans w21_a40
  have w22_a44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K22.w32 (by decide) (by decide)).trans w21_a44
  clear w21_a44 w21_a40 w21_a3c w21_a38 w21_a34 w21_a30 w21_a2c w21_a28 w21_a24 w21_a20 w21_94 w21_90 w21_8c w21_88 w21_84 w21_80 w21_7c w21_78 w21_74 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c w21_58 w21_54 w21_50 w21_4c w21_48 w21_40 w21_3c w21_38 w21_34 w21_30 g21_13 g21_27 g21_26 g21_25 g21_23 g21_22 g21_21 g21_19 g21_18 g21_12 g21_11 g21_10 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
  have g22_10 : reg n22 a0 = BitVec.ofNat 32 1 := by rw [a0_22, ite_eq_left hp0]; rfl
  -- 0x8BE
  obtain ⟨n23, c23, u23⟩ := s22.block svDp08be E22.self svDp08be_end
    ⟨trivial, trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem SV n23 0x8C2 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock svDp08be (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
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
  have g23_8 : reg n23 (8 : Fin 32) = op := by
    rw [rb23, runBlock_reg _ _ _ (8 : Fin 32) s22.zero (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = x9 := by
    rw [rb23, runBlock_reg _ _ _ (9 : Fin 32) s22.zero (by decide), g22_9]
  have g23_10 : reg n23 a0 = BitVec.ofNat 32 0x1 := by
    rw [rb23, runBlock_reg _ _ _ a0 s22.zero (by decide), g22_10]
  have g23_18 : reg n23 (18 : Fin 32) = out := by
    rw [rb23, runBlock_reg _ _ _ (18 : Fin 32) s22.zero (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by
    rw [rb23, runBlock_reg _ _ _ (19 : Fin 32) s22.zero (by decide), g22_19]
  have g23_21 : reg n23 (21 : Fin 32) = x21 := by
    rw [rb23, runBlock_reg _ _ _ (21 : Fin 32) s22.zero (by decide), g22_21]
  have g23_25 : reg n23 (25 : Fin 32) = x25 := by
    rw [rb23, runBlock_reg _ _ _ (25 : Fin 32) s22.zero (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by
    rw [rb23, runBlock_reg _ _ _ (26 : Fin 32) s22.zero (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb23, runBlock_reg _ _ _ (27 : Fin 32) s22.zero (by decide), g22_27]
  have g23_22 : reg n23 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svDp08be, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_10, g22_18, g22_19, g22_21, g22_22, g22_23, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g23_23 : reg n23 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svDp08be, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_10, g22_18, g22_19, g22_21, g22_22, g22_23, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk23 : SvKeepL B n0.mem n23.mem [] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m23]; exact w22_30
  have w23_34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m23]; exact w22_34
  have w23_38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m23]; exact w22_38
  have w23_3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m23]; exact w22_3c
  have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m23]; exact w22_40
  have w23_48 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m23]; exact w22_48
  have w23_4c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m23]; exact w22_4c
  have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m23]; exact w22_50
  have w23_54 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m23]; exact w22_54
  have w23_58 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m23]; exact w22_58
  have w23_5c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m23]; exact w22_5c
  have w23_60 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m23]; exact w22_60
  have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m23]; exact w22_64
  have w23_68 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m23]; exact w22_68
  have w23_6c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m23]; exact w22_6c
  have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m23]; exact w22_70
  have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m23]; exact w22_74
  have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m23]; exact w22_78
  have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m23]; exact w22_7c
  have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m23]; exact w22_80
  have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m23]; exact w22_84
  have w23_88 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m23]; exact w22_88
  have w23_8c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m23]; exact w22_8c
  have w23_90 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m23]; exact w22_90
  have w23_94 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m23]; exact w22_94
  have w23_a20 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m23]; exact w22_a20
  have w23_a24 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m23]; exact w22_a24
  have w23_a28 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m23]; exact w22_a28
  have w23_a2c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m23]; exact w22_a2c
  have w23_a30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m23]; exact w22_a30
  have w23_a34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m23]; exact w22_a34
  have w23_a38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m23]; exact w22_a38
  have w23_a3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m23]; exact w22_a3c
  have w23_a40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m23]; exact w22_a40
  have w23_a44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m23]; exact w22_a44
  clear w22_a44 w22_a40 w22_a3c w22_a38 w22_a34 w22_a30 w22_a2c w22_a28 w22_a24 w22_a20 w22_94 w22_90 w22_8c w22_88 w22_84 w22_80 w22_7c w22_78 w22_74 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c w22_58 w22_54 w22_50 w22_4c w22_48 w22_40 w22_3c w22_38 w22_34 w22_30 g22_27 g22_26 g22_25 g22_23 g22_22 g22_21 g22_19 g22_18 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 K22 a0_22 rk22 s22 c22
  -- 0x8C2: branch, not taken
  obtain ⟨n24, d24, u24⟩ := s23.notTaken E23.self 0x8C4 sv_at_8c2
    (by decide) (by rw [g23_10, s23.zero]; decide)
  have s24 : St n24.mem SV n24 0x8C4 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = op := by rw [u24.regs, g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = x9 := by rw [u24.regs, g23_9]
  have g24_10 : reg n24 a0 = BitVec.ofNat 32 0x1 := by rw [u24.regs, g23_10]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
  have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [u24.regs, g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u24.regs, g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u24.regs, g23_23]
  have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [u24.regs, g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [u24.regs, g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u24.regs, g23_27]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m24]; exact w23_30
  have w24_34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m24]; exact w23_34
  have w24_38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m24]; exact w23_38
  have w24_3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m24]; exact w23_3c
  have w24_40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m24]; exact w23_40
  have w24_48 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m24]; exact w23_48
  have w24_4c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m24]; exact w23_4c
  have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m24]; exact w23_50
  have w24_54 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m24]; exact w23_54
  have w24_58 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m24]; exact w23_58
  have w24_5c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m24]; exact w23_5c
  have w24_60 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m24]; exact w23_60
  have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m24]; exact w23_64
  have w24_68 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m24]; exact w23_68
  have w24_6c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m24]; exact w23_6c
  have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m24]; exact w23_70
  have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m24]; exact w23_74
  have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m24]; exact w23_78
  have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m24]; exact w23_7c
  have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m24]; exact w23_80
  have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m24]; exact w23_84
  have w24_88 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m24]; exact w23_88
  have w24_8c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m24]; exact w23_8c
  have w24_90 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m24]; exact w23_90
  have w24_94 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m24]; exact w23_94
  have w24_a20 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m24]; exact w23_a20
  have w24_a24 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m24]; exact w23_a24
  have w24_a28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m24]; exact w23_a28
  have w24_a2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m24]; exact w23_a2c
  have w24_a30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m24]; exact w23_a30
  have w24_a34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m24]; exact w23_a34
  have w24_a38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m24]; exact w23_a38
  have w24_a3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m24]; exact w23_a3c
  have w24_a40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m24]; exact w23_a40
  have w24_a44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m24]; exact w23_a44
  clear w23_a44 w23_a40 w23_a3c w23_a38 w23_a34 w23_a30 w23_a2c w23_a28 w23_a24 w23_a20 w23_94 w23_90 w23_8c w23_88 w23_84 w23_80 w23_7c w23_78 w23_74 w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c w23_58 w23_54 w23_50 w23_4c w23_48 w23_40 w23_3c w23_38 w23_34 w23_30 g23_23 g23_22 g23_27 g23_26 g23_25 g23_21 g23_19 g23_18 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23 g22_10
  -- 0x8C4
  obtain ⟨n25, c25, u25⟩ := s24.block svDp08c4 E24.self svDp08c4_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have s25 : St n25.mem SV n25 0x8CC (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have rb25 : ∀ q, reg n25 q = (runBlock svDp08c4 (n24.mem, reg n24)).2 q := fun q => by rw [u25.regs]
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
  have g25_8 : reg n25 (8 : Fin 32) = op := by
    rw [rb25, runBlock_reg _ _ _ (8 : Fin 32) s24.zero (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = x9 := by
    rw [rb25, runBlock_reg _ _ _ (9 : Fin 32) s24.zero (by decide), g24_9]
  have g25_18 : reg n25 (18 : Fin 32) = out := by
    rw [rb25, runBlock_reg _ _ _ (18 : Fin 32) s24.zero (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by
    rw [rb25, runBlock_reg _ _ _ (19 : Fin 32) s24.zero (by decide), g24_19]
  have g25_21 : reg n25 (21 : Fin 32) = x21 := by
    rw [rb25, runBlock_reg _ _ _ (21 : Fin 32) s24.zero (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb25, runBlock_reg _ _ _ (22 : Fin 32) s24.zero (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by
    rw [rb25, runBlock_reg _ _ _ (23 : Fin 32) s24.zero (by decide), g24_23]
  have g25_25 : reg n25 (25 : Fin 32) = x25 := by
    rw [rb25, runBlock_reg _ _ _ (25 : Fin 32) s24.zero (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by
    rw [rb25, runBlock_reg _ _ _ (26 : Fin 32) s24.zero (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb25, runBlock_reg _ _ _ (27 : Fin 32) s24.zero (by decide), g24_27]
  have g25_10 : reg n25 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svDp08c4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_10, g24_18, g24_19, g24_21, g24_22, g24_23, g24_25, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk25 : SvKeepL B n0.mem n25.mem [] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m25]; exact w24_30
  have w25_34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m25]; exact w24_34
  have w25_38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m25]; exact w24_38
  have w25_3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m25]; exact w24_3c
  have w25_40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m25]; exact w24_40
  have w25_48 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m25]; exact w24_48
  have w25_4c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m25]; exact w24_4c
  have w25_50 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m25]; exact w24_50
  have w25_54 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m25]; exact w24_54
  have w25_58 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m25]; exact w24_58
  have w25_5c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m25]; exact w24_5c
  have w25_60 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m25]; exact w24_60
  have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m25]; exact w24_64
  have w25_68 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m25]; exact w24_68
  have w25_6c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m25]; exact w24_6c
  have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m25]; exact w24_70
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m25]; exact w24_74
  have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m25]; exact w24_78
  have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m25]; exact w24_7c
  have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m25]; exact w24_80
  have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m25]; exact w24_84
  have w25_88 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m25]; exact w24_88
  have w25_8c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m25]; exact w24_8c
  have w25_90 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m25]; exact w24_90
  have w25_94 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m25]; exact w24_94
  have w25_a20 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m25]; exact w24_a20
  have w25_a24 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m25]; exact w24_a24
  have w25_a28 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m25]; exact w24_a28
  have w25_a2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m25]; exact w24_a2c
  have w25_a30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m25]; exact w24_a30
  have w25_a34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m25]; exact w24_a34
  have w25_a38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m25]; exact w24_a38
  have w25_a3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m25]; exact w24_a3c
  have w25_a40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m25]; exact w24_a40
  have w25_a44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m25]; exact w24_a44
  clear w24_a44 w24_a40 w24_a3c w24_a38 w24_a34 w24_a30 w24_a2c w24_a28 w24_a24 w24_a20 w24_94 w24_90 w24_8c w24_88 w24_84 w24_80 w24_7c w24_78 w24_74 w24_70 w24_6c w24_68 w24_64 w24_60 w24_5c w24_58 w24_54 w24_50 w24_4c w24_48 w24_40 w24_3c w24_38 w24_34 w24_30 g24_27 g24_26 g24_25 g24_23 g24_22 g24_21 g24_19 g24_18 g24_10 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
  -- 0x8CC: lw
  obtain ⟨n26, d26, u26⟩ := s25.lw E25.self sv_at_8cc (off' := 0x8CE) (by decide)
    (by rw [g25_2, show B + 0x21A0 + 0x3C = B + 0x21A0 + BitVec.ofNat 32 0x3C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s26 : St n26.mem SV n26 0x8CE (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans (.single d26)
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = op := by rw [u26.regs, upd_ne (by decide) (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = x9 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_9]
  have g26_10 : reg n26 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_10]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, upd_ne (by decide) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_19]
  have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_23]
  have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_27]
  have g26_11 : reg n26 a1 = vp := by
    rw [u26.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g25_2, show B + 0x21A0 + 0x3C = B + 0x21A0 + BitVec.ofNat 32 0x3C by sv_addr, w25_3c]
  have keep_kk26 : SvKeepL B n0.mem n26.mem [] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m26]; exact w25_30
  have w26_34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m26]; exact w25_34
  have w26_38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m26]; exact w25_38
  have w26_3c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m26]; exact w25_3c
  have w26_40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m26]; exact w25_40
  have w26_48 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m26]; exact w25_48
  have w26_4c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m26]; exact w25_4c
  have w26_50 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m26]; exact w25_50
  have w26_54 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m26]; exact w25_54
  have w26_58 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m26]; exact w25_58
  have w26_5c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m26]; exact w25_5c
  have w26_60 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m26]; exact w25_60
  have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m26]; exact w25_64
  have w26_68 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m26]; exact w25_68
  have w26_6c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m26]; exact w25_6c
  have w26_70 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m26]; exact w25_70
  have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m26]; exact w25_74
  have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m26]; exact w25_78
  have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m26]; exact w25_7c
  have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m26]; exact w25_80
  have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m26]; exact w25_84
  have w26_88 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m26]; exact w25_88
  have w26_8c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m26]; exact w25_8c
  have w26_90 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m26]; exact w25_90
  have w26_94 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m26]; exact w25_94
  have w26_a20 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m26]; exact w25_a20
  have w26_a24 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m26]; exact w25_a24
  have w26_a28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m26]; exact w25_a28
  have w26_a2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m26]; exact w25_a2c
  have w26_a30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m26]; exact w25_a30
  have w26_a34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m26]; exact w25_a34
  have w26_a38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m26]; exact w25_a38
  have w26_a3c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m26]; exact w25_a3c
  have w26_a40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m26]; exact w25_a40
  have w26_a44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m26]; exact w25_a44
  clear w25_a44 w25_a40 w25_a3c w25_a38 w25_a34 w25_a30 w25_a2c w25_a28 w25_a24 w25_a20 w25_94 w25_90 w25_8c w25_88 w25_84 w25_80 w25_7c w25_78 w25_74 w25_70 w25_6c w25_68 w25_64 w25_60 w25_5c w25_58 w25_54 w25_50 w25_4c w25_48 w25_40 w25_3c w25_38 w25_34 w25_30 g25_10 g25_27 g25_26 g25_25 g25_23 g25_22 g25_21 g25_19 g25_18 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
  -- 0x8CE
  obtain ⟨n27, c27, u27⟩ := s26.block svDp08ce E26.self svDp08ce_end
    ⟨trivial, trivial⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have s27 : St n27.mem SV n27 0x8D2 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have rb27 : ∀ q, reg n27 q = (runBlock svDp08ce (n26.mem, reg n26)).2 q := fun q => by rw [u27.regs]
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
  have g27_8 : reg n27 (8 : Fin 32) = op := by
    rw [rb27, runBlock_reg _ _ _ (8 : Fin 32) s26.zero (by decide), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = x9 := by
    rw [rb27, runBlock_reg _ _ _ (9 : Fin 32) s26.zero (by decide), g26_9]
  have g27_10 : reg n27 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb27, runBlock_reg _ _ _ a0 s26.zero (by decide), g26_10]
  have g27_11 : reg n27 a1 = vp := by
    rw [rb27, runBlock_reg _ _ _ a1 s26.zero (by decide), g26_11]
  have g27_18 : reg n27 (18 : Fin 32) = out := by
    rw [rb27, runBlock_reg _ _ _ (18 : Fin 32) s26.zero (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by
    rw [rb27, runBlock_reg _ _ _ (19 : Fin 32) s26.zero (by decide), g26_19]
  have g27_21 : reg n27 (21 : Fin 32) = x21 := by
    rw [rb27, runBlock_reg _ _ _ (21 : Fin 32) s26.zero (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb27, runBlock_reg _ _ _ (22 : Fin 32) s26.zero (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by
    rw [rb27, runBlock_reg _ _ _ (23 : Fin 32) s26.zero (by decide), g26_23]
  have g27_25 : reg n27 (25 : Fin 32) = x25 := by
    rw [rb27, runBlock_reg _ _ _ (25 : Fin 32) s26.zero (by decide), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by
    rw [rb27, runBlock_reg _ _ _ (26 : Fin 32) s26.zero (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb27, runBlock_reg _ _ _ (27 : Fin 32) s26.zero (by decide), g26_27]
  have g27_13 : reg n27 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1420 := by
    rw [rb27]; simp +decide only [runBlock, BInstr.run, svDp08ce, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g26_2, g26_3, g26_4, g26_8, g26_9, g26_10, g26_11, g26_18, g26_19, g26_21, g26_22, g26_23, g26_25, g26_26, g26_27, s26.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk27 : SvKeepL B n0.mem n27.mem [] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m27]; exact w26_30
  have w27_34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m27]; exact w26_34
  have w27_38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m27]; exact w26_38
  have w27_3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m27]; exact w26_3c
  have w27_40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m27]; exact w26_40
  have w27_48 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m27]; exact w26_48
  have w27_4c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m27]; exact w26_4c
  have w27_50 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m27]; exact w26_50
  have w27_54 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m27]; exact w26_54
  have w27_58 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m27]; exact w26_58
  have w27_5c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m27]; exact w26_5c
  have w27_60 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m27]; exact w26_60
  have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m27]; exact w26_64
  have w27_68 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m27]; exact w26_68
  have w27_6c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m27]; exact w26_6c
  have w27_70 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m27]; exact w26_70
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m27]; exact w26_74
  have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m27]; exact w26_78
  have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m27]; exact w26_7c
  have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m27]; exact w26_80
  have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m27]; exact w26_84
  have w27_88 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m27]; exact w26_88
  have w27_8c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m27]; exact w26_8c
  have w27_90 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m27]; exact w26_90
  have w27_94 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m27]; exact w26_94
  have w27_a20 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m27]; exact w26_a20
  have w27_a24 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m27]; exact w26_a24
  have w27_a28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m27]; exact w26_a28
  have w27_a2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m27]; exact w26_a2c
  have w27_a30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m27]; exact w26_a30
  have w27_a34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m27]; exact w26_a34
  have w27_a38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m27]; exact w26_a38
  have w27_a3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m27]; exact w26_a3c
  have w27_a40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m27]; exact w26_a40
  have w27_a44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m27]; exact w26_a44
  clear w26_a44 w26_a40 w26_a3c w26_a38 w26_a34 w26_a30 w26_a2c w26_a28 w26_a24 w26_a20 w26_94 w26_90 w26_8c w26_88 w26_84 w26_80 w26_7c w26_78 w26_74 w26_70 w26_6c w26_68 w26_64 w26_60 w26_5c w26_58 w26_54 w26_50 w26_4c w26_48 w26_40 w26_3c w26_38 w26_34 w26_30 g26_11 g26_27 g26_26 g26_25 g26_23 g26_22 g26_21 g26_19 g26_18 g26_10 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
  -- 0x8D2: sw
  obtain ⟨n28, d28, s28, fr28, K28, W28, rg28⟩ := sv_sw F E27 s27 sv_at_8d2 (off' := 0x8D4) (c := 0x1480)
    (by decide) (by rw [g27_13]; sv_addr) (by decide) (by decide)
  have t28 : Steps n0 n28 := t27.trans d28
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.keep K28 (by decide)
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [rg28 sp, g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg28 (3 : Fin 32), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg28 (4 : Fin 32), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = op := by rw [rg28 (8 : Fin 32), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = x9 := by rw [rg28 (9 : Fin 32), g27_9]
  have g28_10 : reg n28 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg28 a0, g27_10]
  have g28_11 : reg n28 a1 = vp := by rw [rg28 a1, g27_11]
  have g28_13 : reg n28 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1420 := by rw [rg28 a3, g27_13]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [rg28 (18 : Fin 32), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [rg28 (19 : Fin 32), g27_19]
  have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [rg28 (21 : Fin 32), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg28 (22 : Fin 32), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [rg28 (23 : Fin 32), g27_23]
  have g28_25 : reg n28 (25 : Fin 32) = x25 := by rw [rg28 (25 : Fin 32), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [rg28 (26 : Fin 32), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg28 (27 : Fin 32), g27_27]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [(0x1480, 0x4)] := keep_kk27.trans K28.toL
  clear keep_kk27
  have w28_30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K28.w32 (by decide) (by decide)).trans w27_30
  have w28_34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K28.w32 (by decide) (by decide)).trans w27_34
  have w28_38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K28.w32 (by decide) (by decide)).trans w27_38
  have w28_3c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K28.w32 (by decide) (by decide)).trans w27_3c
  have w28_40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K28.w32 (by decide) (by decide)).trans w27_40
  have w28_48 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K28.w32 (by decide) (by decide)).trans w27_48
  have w28_4c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K28.w32 (by decide) (by decide)).trans w27_4c
  have w28_50 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K28.w32 (by decide) (by decide)).trans w27_50
  have w28_54 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K28.w32 (by decide) (by decide)).trans w27_54
  have w28_58 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K28.w32 (by decide) (by decide)).trans w27_58
  have w28_5c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K28.w32 (by decide) (by decide)).trans w27_5c
  have w28_60 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K28.w32 (by decide) (by decide)).trans w27_60
  have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K28.w32 (by decide) (by decide)).trans w27_64
  have w28_68 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K28.w32 (by decide) (by decide)).trans w27_68
  have w28_6c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K28.w32 (by decide) (by decide)).trans w27_6c
  have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K28.w32 (by decide) (by decide)).trans w27_70
  have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K28.w32 (by decide) (by decide)).trans w27_74
  have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K28.w32 (by decide) (by decide)).trans w27_78
  have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K28.w32 (by decide) (by decide)).trans w27_7c
  have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K28.w32 (by decide) (by decide)).trans w27_80
  have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K28.w32 (by decide) (by decide)).trans w27_84
  have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K28.w32 (by decide) (by decide)).trans w27_88
  have w28_8c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K28.w32 (by decide) (by decide)).trans w27_8c
  have w28_90 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K28.w32 (by decide) (by decide)).trans w27_90
  have w28_94 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K28.w32 (by decide) (by decide)).trans w27_94
  have w28_a20 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K28.w32 (by decide) (by decide)).trans w27_a20
  have w28_a24 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K28.w32 (by decide) (by decide)).trans w27_a24
  have w28_a28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K28.w32 (by decide) (by decide)).trans w27_a28
  have w28_a2c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K28.w32 (by decide) (by decide)).trans w27_a2c
  have w28_a30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K28.w32 (by decide) (by decide)).trans w27_a30
  have w28_a34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K28.w32 (by decide) (by decide)).trans w27_a34
  have w28_a38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K28.w32 (by decide) (by decide)).trans w27_a38
  have w28_a3c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K28.w32 (by decide) (by decide)).trans w27_a3c
  have w28_a40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K28.w32 (by decide) (by decide)).trans w27_a40
  have w28_a44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K28.w32 (by decide) (by decide)).trans w27_a44
  have w28_1480 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [W28, g27_11]
  clear w27_a44 w27_a40 w27_a3c w27_a38 w27_a34 w27_a30 w27_a2c w27_a28 w27_a24 w27_a20 w27_94 w27_90 w27_8c w27_88 w27_84 w27_80 w27_7c w27_78 w27_74 w27_70 w27_6c w27_68 w27_64 w27_60 w27_5c w27_58 w27_54 w27_50 w27_4c w27_48 w27_40 w27_3c w27_38 w27_34 w27_30 g27_13 g27_27 g27_26 g27_25 g27_23 g27_22 g27_21 g27_19 g27_18 g27_11 g27_10 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 rb27 s27 m27 u27 c27
  -- 0x8D4: lw
  obtain ⟨n29, d29, u29⟩ := s28.lw E28.self sv_at_8d4 (off' := 0x8D6) (by decide)
    (by rw [g28_2, show B + 0x21A0 + 0x38 = B + 0x21A0 + BitVec.ofNat 32 0x38 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s29 : St n29.mem SV n29 0x8D6 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans (.single d29)
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = op := by rw [u29.regs, upd_ne (by decide) (by decide), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = x9 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_9]
  have g29_10 : reg n29 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_10]
  have g29_11 : reg n29 a1 = vp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_11]
  have g29_13 : reg n29 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1420 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_13]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, upd_ne (by decide) (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_19]
  have g29_21 : reg n29 (21 : Fin 32) = x21 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_23]
  have g29_25 : reg n29 (25 : Fin 32) = x25 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_27]
  have g29_12 : reg n29 a2 = vl := by
    rw [u29.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g28_2, show B + 0x21A0 + 0x38 = B + 0x21A0 + BitVec.ofNat 32 0x38 by sv_addr, w28_38]
  have keep_kk29 : SvKeepL B n0.mem n29.mem [(0x1480, 0x4)] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m29]; exact w28_30
  have w29_34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m29]; exact w28_34
  have w29_38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m29]; exact w28_38
  have w29_3c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m29]; exact w28_3c
  have w29_40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m29]; exact w28_40
  have w29_48 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m29]; exact w28_48
  have w29_4c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m29]; exact w28_4c
  have w29_50 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m29]; exact w28_50
  have w29_54 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m29]; exact w28_54
  have w29_58 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m29]; exact w28_58
  have w29_5c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m29]; exact w28_5c
  have w29_60 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m29]; exact w28_60
  have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m29]; exact w28_64
  have w29_68 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m29]; exact w28_68
  have w29_6c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m29]; exact w28_6c
  have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m29]; exact w28_70
  have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m29]; exact w28_74
  have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m29]; exact w28_78
  have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m29]; exact w28_7c
  have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m29]; exact w28_80
  have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m29]; exact w28_84
  have w29_88 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m29]; exact w28_88
  have w29_8c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m29]; exact w28_8c
  have w29_90 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m29]; exact w28_90
  have w29_94 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m29]; exact w28_94
  have w29_a20 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m29]; exact w28_a20
  have w29_a24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m29]; exact w28_a24
  have w29_a28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m29]; exact w28_a28
  have w29_a2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m29]; exact w28_a2c
  have w29_a30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m29]; exact w28_a30
  have w29_a34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m29]; exact w28_a34
  have w29_a38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m29]; exact w28_a38
  have w29_a3c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m29]; exact w28_a3c
  have w29_a40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m29]; exact w28_a40
  have w29_a44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m29]; exact w28_a44
  have w29_1480 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m29]; exact w28_1480
  clear w28_1480 w28_a44 w28_a40 w28_a3c w28_a38 w28_a34 w28_a30 w28_a2c w28_a28 w28_a24 w28_a20 w28_94 w28_90 w28_8c w28_88 w28_84 w28_80 w28_7c w28_78 w28_74 w28_70 w28_6c w28_68 w28_64 w28_60 w28_5c w28_58 w28_54 w28_50 w28_4c w28_48 w28_40 w28_3c w28_38 w28_34 w28_30 g28_27 g28_26 g28_25 g28_23 g28_22 g28_21 g28_19 g28_18 g28_13 g28_11 g28_10 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 rg28 W28 K28 fr28 s28 d28
  -- 0x8D6: sw
  obtain ⟨n30, d30, s30, fr30, K30, W30, rg30⟩ := sv_sw F E29 s29 sv_at_8d6 (off' := 0x8D8) (c := 0x1484)
    (by decide) (by rw [g29_13]; sv_addr) (by decide) (by decide)
  have t30 : Steps n0 n30 := t29.trans d30
  have fR30 : ∀ x, SvR B x → n30.mem x = M0 x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.keep K30 (by decide)
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [rg30 sp, g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg30 (3 : Fin 32), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg30 (4 : Fin 32), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = op := by rw [rg30 (8 : Fin 32), g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = x9 := by rw [rg30 (9 : Fin 32), g29_9]
  have g30_10 : reg n30 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg30 a0, g29_10]
  have g30_11 : reg n30 a1 = vp := by rw [rg30 a1, g29_11]
  have g30_12 : reg n30 a2 = vl := by rw [rg30 a2, g29_12]
  have g30_13 : reg n30 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1420 := by rw [rg30 a3, g29_13]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [rg30 (18 : Fin 32), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [rg30 (19 : Fin 32), g29_19]
  have g30_21 : reg n30 (21 : Fin 32) = x21 := by rw [rg30 (21 : Fin 32), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg30 (22 : Fin 32), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [rg30 (23 : Fin 32), g29_23]
  have g30_25 : reg n30 (25 : Fin 32) = x25 := by rw [rg30 (25 : Fin 32), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [rg30 (26 : Fin 32), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg30 (27 : Fin 32), g29_27]
  have keep_kk30 : SvKeepL B n0.mem n30.mem [(0x1480, 0x4), (0x1484, 0x4)] := keep_kk29.trans K30.toL
  clear keep_kk29
  have w30_30 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K30.w32 (by decide) (by decide)).trans w29_30
  have w30_34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K30.w32 (by decide) (by decide)).trans w29_34
  have w30_38 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K30.w32 (by decide) (by decide)).trans w29_38
  have w30_3c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K30.w32 (by decide) (by decide)).trans w29_3c
  have w30_40 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K30.w32 (by decide) (by decide)).trans w29_40
  have w30_48 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K30.w32 (by decide) (by decide)).trans w29_48
  have w30_4c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K30.w32 (by decide) (by decide)).trans w29_4c
  have w30_50 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K30.w32 (by decide) (by decide)).trans w29_50
  have w30_54 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K30.w32 (by decide) (by decide)).trans w29_54
  have w30_58 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K30.w32 (by decide) (by decide)).trans w29_58
  have w30_5c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K30.w32 (by decide) (by decide)).trans w29_5c
  have w30_60 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K30.w32 (by decide) (by decide)).trans w29_60
  have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K30.w32 (by decide) (by decide)).trans w29_64
  have w30_68 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K30.w32 (by decide) (by decide)).trans w29_68
  have w30_6c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K30.w32 (by decide) (by decide)).trans w29_6c
  have w30_70 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K30.w32 (by decide) (by decide)).trans w29_70
  have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K30.w32 (by decide) (by decide)).trans w29_74
  have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K30.w32 (by decide) (by decide)).trans w29_78
  have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K30.w32 (by decide) (by decide)).trans w29_7c
  have w30_80 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K30.w32 (by decide) (by decide)).trans w29_80
  have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K30.w32 (by decide) (by decide)).trans w29_84
  have w30_88 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K30.w32 (by decide) (by decide)).trans w29_88
  have w30_8c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K30.w32 (by decide) (by decide)).trans w29_8c
  have w30_90 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K30.w32 (by decide) (by decide)).trans w29_90
  have w30_94 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K30.w32 (by decide) (by decide)).trans w29_94
  have w30_a20 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K30.w32 (by decide) (by decide)).trans w29_a20
  have w30_a24 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K30.w32 (by decide) (by decide)).trans w29_a24
  have w30_a28 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K30.w32 (by decide) (by decide)).trans w29_a28
  have w30_a2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K30.w32 (by decide) (by decide)).trans w29_a2c
  have w30_a30 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K30.w32 (by decide) (by decide)).trans w29_a30
  have w30_a34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K30.w32 (by decide) (by decide)).trans w29_a34
  have w30_a38 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K30.w32 (by decide) (by decide)).trans w29_a38
  have w30_a3c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K30.w32 (by decide) (by decide)).trans w29_a3c
  have w30_a40 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K30.w32 (by decide) (by decide)).trans w29_a40
  have w30_a44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K30.w32 (by decide) (by decide)).trans w29_a44
  have w30_1480 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K30.w32 (by decide) (by decide)).trans w29_1480
  have w30_1484 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [W30, g29_12]
  clear w29_1480 w29_a44 w29_a40 w29_a3c w29_a38 w29_a34 w29_a30 w29_a2c w29_a28 w29_a24 w29_a20 w29_94 w29_90 w29_8c w29_88 w29_84 w29_80 w29_7c w29_78 w29_74 w29_70 w29_6c w29_68 w29_64 w29_60 w29_5c w29_58 w29_54 w29_50 w29_4c w29_48 w29_40 w29_3c w29_38 w29_34 w29_30 g29_12 g29_27 g29_26 g29_25 g29_23 g29_22 g29_21 g29_19 g29_18 g29_13 g29_11 g29_10 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
  -- 0x8D8: sw
  obtain ⟨n31, d31, s31, fr31, K31, W31, rg31⟩ := sv_sw F E30 s30 sv_at_8d8 (off' := 0x8DA) (c := 0x1488)
    (by decide) (by rw [g30_13]; sv_addr) (by decide) (by decide)
  have t31 : Steps n0 n31 := t30.trans d31
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.keep K31 (by decide)
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [rg31 sp, g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg31 (3 : Fin 32), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg31 (4 : Fin 32), g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = op := by rw [rg31 (8 : Fin 32), g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = x9 := by rw [rg31 (9 : Fin 32), g30_9]
  have g31_10 : reg n31 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg31 a0, g30_10]
  have g31_11 : reg n31 a1 = vp := by rw [rg31 a1, g30_11]
  have g31_12 : reg n31 a2 = vl := by rw [rg31 a2, g30_12]
  have g31_13 : reg n31 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1420 := by rw [rg31 a3, g30_13]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [rg31 (18 : Fin 32), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [rg31 (19 : Fin 32), g30_19]
  have g31_21 : reg n31 (21 : Fin 32) = x21 := by rw [rg31 (21 : Fin 32), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg31 (22 : Fin 32), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [rg31 (23 : Fin 32), g30_23]
  have g31_25 : reg n31 (25 : Fin 32) = x25 := by rw [rg31 (25 : Fin 32), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = x26 := by rw [rg31 (26 : Fin 32), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg31 (27 : Fin 32), g30_27]
  have keep_kk31 : SvKeepL B n0.mem n31.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4)] := keep_kk30.trans K31.toL
  clear keep_kk30
  have w31_30 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K31.w32 (by decide) (by decide)).trans w30_30
  have w31_34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K31.w32 (by decide) (by decide)).trans w30_34
  have w31_38 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K31.w32 (by decide) (by decide)).trans w30_38
  have w31_3c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K31.w32 (by decide) (by decide)).trans w30_3c
  have w31_40 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K31.w32 (by decide) (by decide)).trans w30_40
  have w31_48 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K31.w32 (by decide) (by decide)).trans w30_48
  have w31_4c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K31.w32 (by decide) (by decide)).trans w30_4c
  have w31_50 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K31.w32 (by decide) (by decide)).trans w30_50
  have w31_54 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K31.w32 (by decide) (by decide)).trans w30_54
  have w31_58 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K31.w32 (by decide) (by decide)).trans w30_58
  have w31_5c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K31.w32 (by decide) (by decide)).trans w30_5c
  have w31_60 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K31.w32 (by decide) (by decide)).trans w30_60
  have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K31.w32 (by decide) (by decide)).trans w30_64
  have w31_68 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K31.w32 (by decide) (by decide)).trans w30_68
  have w31_6c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K31.w32 (by decide) (by decide)).trans w30_6c
  have w31_70 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K31.w32 (by decide) (by decide)).trans w30_70
  have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K31.w32 (by decide) (by decide)).trans w30_74
  have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K31.w32 (by decide) (by decide)).trans w30_78
  have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K31.w32 (by decide) (by decide)).trans w30_7c
  have w31_80 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K31.w32 (by decide) (by decide)).trans w30_80
  have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K31.w32 (by decide) (by decide)).trans w30_84
  have w31_88 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K31.w32 (by decide) (by decide)).trans w30_88
  have w31_8c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K31.w32 (by decide) (by decide)).trans w30_8c
  have w31_90 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K31.w32 (by decide) (by decide)).trans w30_90
  have w31_94 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K31.w32 (by decide) (by decide)).trans w30_94
  have w31_a20 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K31.w32 (by decide) (by decide)).trans w30_a20
  have w31_a24 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K31.w32 (by decide) (by decide)).trans w30_a24
  have w31_a28 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K31.w32 (by decide) (by decide)).trans w30_a28
  have w31_a2c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K31.w32 (by decide) (by decide)).trans w30_a2c
  have w31_a30 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K31.w32 (by decide) (by decide)).trans w30_a30
  have w31_a34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K31.w32 (by decide) (by decide)).trans w30_a34
  have w31_a38 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K31.w32 (by decide) (by decide)).trans w30_a38
  have w31_a3c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K31.w32 (by decide) (by decide)).trans w30_a3c
  have w31_a40 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K31.w32 (by decide) (by decide)).trans w30_a40
  have w31_a44 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K31.w32 (by decide) (by decide)).trans w30_a44
  have w31_1480 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K31.w32 (by decide) (by decide)).trans w30_1480
  have w31_1484 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K31.w32 (by decide) (by decide)).trans w30_1484
  have w31_1488 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = vp := by rw [W31, g30_11]
  clear w30_1484 w30_1480 w30_a44 w30_a40 w30_a3c w30_a38 w30_a34 w30_a30 w30_a2c w30_a28 w30_a24 w30_a20 w30_94 w30_90 w30_8c w30_88 w30_84 w30_80 w30_7c w30_78 w30_74 w30_70 w30_6c w30_68 w30_64 w30_60 w30_5c w30_58 w30_54 w30_50 w30_4c w30_48 w30_40 w30_3c w30_38 w30_34 w30_30 g30_27 g30_26 g30_25 g30_23 g30_22 g30_21 g30_19 g30_18 g30_13 g30_12 g30_11 g30_10 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 rg30 W30 K30 fr30 s30 d30
  -- 0x8DA
  obtain ⟨n32, c32, u32⟩ := s31.block svDp08da E31.self svDp08da_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have s32 : St n32.mem SV n32 0x8E4 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have rb32 : ∀ q, reg n32 q = (runBlock svDp08da (n31.mem, reg n31)).2 q := fun q => by rw [u32.regs]
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
  have g32_9 : reg n32 (9 : Fin 32) = x9 := by
    rw [rb32, runBlock_reg _ _ _ (9 : Fin 32) s31.zero (by decide), g31_9]
  have g32_10 : reg n32 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb32, runBlock_reg _ _ _ a0 s31.zero (by decide), g31_10]
  have g32_12 : reg n32 a2 = vl := by
    rw [rb32, runBlock_reg _ _ _ a2 s31.zero (by decide), g31_12]
  have g32_13 : reg n32 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1420 := by
    rw [rb32, runBlock_reg _ _ _ a3 s31.zero (by decide), g31_13]
  have g32_18 : reg n32 (18 : Fin 32) = out := by
    rw [rb32, runBlock_reg _ _ _ (18 : Fin 32) s31.zero (by decide), g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by
    rw [rb32, runBlock_reg _ _ _ (19 : Fin 32) s31.zero (by decide), g31_19]
  have g32_21 : reg n32 (21 : Fin 32) = x21 := by
    rw [rb32, runBlock_reg _ _ _ (21 : Fin 32) s31.zero (by decide), g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb32, runBlock_reg _ _ _ (22 : Fin 32) s31.zero (by decide), g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by
    rw [rb32, runBlock_reg _ _ _ (23 : Fin 32) s31.zero (by decide), g31_23]
  have g32_25 : reg n32 (25 : Fin 32) = x25 := by
    rw [rb32, runBlock_reg _ _ _ (25 : Fin 32) s31.zero (by decide), g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = x26 := by
    rw [rb32, runBlock_reg _ _ _ (26 : Fin 32) s31.zero (by decide), g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb32, runBlock_reg _ _ _ (27 : Fin 32) s31.zero (by decide), g31_27]
  have g32_8 : reg n32 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb32]; simp +decide only [runBlock, BInstr.run, svDp08da, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g31_2, g31_3, g31_4, g31_8, g31_9, g31_10, g31_11, g31_12, g31_13, g31_18, g31_19, g31_21, g31_22, g31_23, g31_25, g31_26, g31_27, s31.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g32_11 : reg n32 a1 = BitVec.ofNat 32 0x1320 := by
    rw [rb32]; simp +decide only [runBlock, BInstr.run, svDp08da, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g31_2, g31_3, g31_4, g31_8, g31_9, g31_10, g31_11, g31_12, g31_13, g31_18, g31_19, g31_21, g31_22, g31_23, g31_25, g31_26, g31_27, s31.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk32 : SvKeepL B n0.mem n32.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4)] := by rw [m32]; exact keep_kk31
  clear keep_kk31
  have w32_30 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m32]; exact w31_30
  have w32_34 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m32]; exact w31_34
  have w32_38 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m32]; exact w31_38
  have w32_3c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m32]; exact w31_3c
  have w32_40 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m32]; exact w31_40
  have w32_48 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m32]; exact w31_48
  have w32_4c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m32]; exact w31_4c
  have w32_50 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m32]; exact w31_50
  have w32_54 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m32]; exact w31_54
  have w32_58 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m32]; exact w31_58
  have w32_5c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m32]; exact w31_5c
  have w32_60 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m32]; exact w31_60
  have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m32]; exact w31_64
  have w32_68 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m32]; exact w31_68
  have w32_6c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m32]; exact w31_6c
  have w32_70 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m32]; exact w31_70
  have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m32]; exact w31_74
  have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m32]; exact w31_78
  have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m32]; exact w31_7c
  have w32_80 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m32]; exact w31_80
  have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m32]; exact w31_84
  have w32_88 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m32]; exact w31_88
  have w32_8c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m32]; exact w31_8c
  have w32_90 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m32]; exact w31_90
  have w32_94 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m32]; exact w31_94
  have w32_a20 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m32]; exact w31_a20
  have w32_a24 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m32]; exact w31_a24
  have w32_a28 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m32]; exact w31_a28
  have w32_a2c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m32]; exact w31_a2c
  have w32_a30 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m32]; exact w31_a30
  have w32_a34 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m32]; exact w31_a34
  have w32_a38 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m32]; exact w31_a38
  have w32_a3c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m32]; exact w31_a3c
  have w32_a40 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m32]; exact w31_a40
  have w32_a44 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m32]; exact w31_a44
  have w32_1480 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m32]; exact w31_1480
  have w32_1484 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m32]; exact w31_1484
  have w32_1488 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = vp := by rw [m32]; exact w31_1488
  clear w31_1488 w31_1484 w31_1480 w31_a44 w31_a40 w31_a3c w31_a38 w31_a34 w31_a30 w31_a2c w31_a28 w31_a24 w31_a20 w31_94 w31_90 w31_8c w31_88 w31_84 w31_80 w31_7c w31_78 w31_74 w31_70 w31_6c w31_68 w31_64 w31_60 w31_5c w31_58 w31_54 w31_50 w31_4c w31_48 w31_40 w31_3c w31_38 w31_34 w31_30 g31_27 g31_26 g31_25 g31_23 g31_22 g31_21 g31_19 g31_18 g31_13 g31_12 g31_11 g31_10 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 rg31 W31 K31 fr31 s31 d31
  -- 0x8E4: sw
  obtain ⟨n33, d33, s33, fr33, K33, W33, rg33⟩ := sv_sw F E32 s32 sv_at_8e4 (off' := 0x8E6) (c := 0x148C)
    (by decide) (by rw [g32_13]; sv_addr) (by decide) (by decide)
  have t33 : Steps n0 n33 := t32.trans d33
  have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.keep K33 (by decide)
  have g33_2 : reg n33 sp = B + 0x21A0 := by rw [rg33 sp, g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg33 (3 : Fin 32), g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg33 (4 : Fin 32), g32_4]
  have g33_8 : reg n33 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg33 (8 : Fin 32), g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = x9 := by rw [rg33 (9 : Fin 32), g32_9]
  have g33_10 : reg n33 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg33 a0, g32_10]
  have g33_11 : reg n33 a1 = BitVec.ofNat 32 0x1320 := by rw [rg33 a1, g32_11]
  have g33_12 : reg n33 a2 = vl := by rw [rg33 a2, g32_12]
  have g33_13 : reg n33 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1420 := by rw [rg33 a3, g32_13]
  have g33_18 : reg n33 (18 : Fin 32) = out := by rw [rg33 (18 : Fin 32), g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [rg33 (19 : Fin 32), g32_19]
  have g33_21 : reg n33 (21 : Fin 32) = x21 := by rw [rg33 (21 : Fin 32), g32_21]
  have g33_22 : reg n33 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg33 (22 : Fin 32), g32_22]
  have g33_23 : reg n33 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [rg33 (23 : Fin 32), g32_23]
  have g33_25 : reg n33 (25 : Fin 32) = x25 := by rw [rg33 (25 : Fin 32), g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = x26 := by rw [rg33 (26 : Fin 32), g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg33 (27 : Fin 32), g32_27]
  have keep_kk33 : SvKeepL B n0.mem n33.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4)] := keep_kk32.trans K33.toL
  clear keep_kk32
  have w33_30 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K33.w32 (by decide) (by decide)).trans w32_30
  have w33_34 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K33.w32 (by decide) (by decide)).trans w32_34
  have w33_38 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K33.w32 (by decide) (by decide)).trans w32_38
  have w33_3c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K33.w32 (by decide) (by decide)).trans w32_3c
  have w33_40 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K33.w32 (by decide) (by decide)).trans w32_40
  have w33_48 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K33.w32 (by decide) (by decide)).trans w32_48
  have w33_4c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K33.w32 (by decide) (by decide)).trans w32_4c
  have w33_50 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K33.w32 (by decide) (by decide)).trans w32_50
  have w33_54 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K33.w32 (by decide) (by decide)).trans w32_54
  have w33_58 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K33.w32 (by decide) (by decide)).trans w32_58
  have w33_5c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K33.w32 (by decide) (by decide)).trans w32_5c
  have w33_60 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K33.w32 (by decide) (by decide)).trans w32_60
  have w33_64 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K33.w32 (by decide) (by decide)).trans w32_64
  have w33_68 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K33.w32 (by decide) (by decide)).trans w32_68
  have w33_6c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K33.w32 (by decide) (by decide)).trans w32_6c
  have w33_70 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K33.w32 (by decide) (by decide)).trans w32_70
  have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K33.w32 (by decide) (by decide)).trans w32_74
  have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K33.w32 (by decide) (by decide)).trans w32_78
  have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K33.w32 (by decide) (by decide)).trans w32_7c
  have w33_80 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K33.w32 (by decide) (by decide)).trans w32_80
  have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K33.w32 (by decide) (by decide)).trans w32_84
  have w33_88 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K33.w32 (by decide) (by decide)).trans w32_88
  have w33_8c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K33.w32 (by decide) (by decide)).trans w32_8c
  have w33_90 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K33.w32 (by decide) (by decide)).trans w32_90
  have w33_94 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K33.w32 (by decide) (by decide)).trans w32_94
  have w33_a20 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K33.w32 (by decide) (by decide)).trans w32_a20
  have w33_a24 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K33.w32 (by decide) (by decide)).trans w32_a24
  have w33_a28 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K33.w32 (by decide) (by decide)).trans w32_a28
  have w33_a2c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K33.w32 (by decide) (by decide)).trans w32_a2c
  have w33_a30 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K33.w32 (by decide) (by decide)).trans w32_a30
  have w33_a34 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K33.w32 (by decide) (by decide)).trans w32_a34
  have w33_a38 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K33.w32 (by decide) (by decide)).trans w32_a38
  have w33_a3c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K33.w32 (by decide) (by decide)).trans w32_a3c
  have w33_a40 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K33.w32 (by decide) (by decide)).trans w32_a40
  have w33_a44 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K33.w32 (by decide) (by decide)).trans w32_a44
  have w33_1480 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K33.w32 (by decide) (by decide)).trans w32_1480
  have w33_1484 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K33.w32 (by decide) (by decide)).trans w32_1484
  have w33_1488 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = vp := (K33.w32 (by decide) (by decide)).trans w32_1488
  have w33_148c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = vl := by rw [W33, g32_12]
  clear w32_1488 w32_1484 w32_1480 w32_a44 w32_a40 w32_a3c w32_a38 w32_a34 w32_a30 w32_a2c w32_a28 w32_a24 w32_a20 w32_94 w32_90 w32_8c w32_88 w32_84 w32_80 w32_7c w32_78 w32_74 w32_70 w32_6c w32_68 w32_64 w32_60 w32_5c w32_58 w32_54 w32_50 w32_4c w32_48 w32_40 w32_3c w32_38 w32_34 w32_30 g32_11 g32_8 g32_27 g32_26 g32_25 g32_23 g32_22 g32_21 g32_19 g32_18 g32_13 g32_12 g32_10 g32_9 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 rb32 s32 m32 u32 c32
  -- 0x8E6
  obtain ⟨n34, c34, u34⟩ := s33.block svDp08e6 E33.self svDp08e6_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m34 : n34.mem = n33.mem := u34.mem
  have s34 : St n34.mem SV n34 0x8F6 (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
  have rb34 : ∀ q, reg n34 q = (runBlock svDp08e6 (n33.mem, reg n33)).2 q := fun q => by rw [u34.regs]
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
  have g34_8 : reg n34 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb34, runBlock_reg _ _ _ (8 : Fin 32) s33.zero (by decide), g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = x9 := by
    rw [rb34, runBlock_reg _ _ _ (9 : Fin 32) s33.zero (by decide), g33_9]
  have g34_12 : reg n34 a2 = vl := by
    rw [rb34, runBlock_reg _ _ _ a2 s33.zero (by decide), g33_12]
  have g34_13 : reg n34 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1420 := by
    rw [rb34, runBlock_reg _ _ _ a3 s33.zero (by decide), g33_13]
  have g34_18 : reg n34 (18 : Fin 32) = out := by
    rw [rb34, runBlock_reg _ _ _ (18 : Fin 32) s33.zero (by decide), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by
    rw [rb34, runBlock_reg _ _ _ (19 : Fin 32) s33.zero (by decide), g33_19]
  have g34_21 : reg n34 (21 : Fin 32) = x21 := by
    rw [rb34, runBlock_reg _ _ _ (21 : Fin 32) s33.zero (by decide), g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb34, runBlock_reg _ _ _ (22 : Fin 32) s33.zero (by decide), g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by
    rw [rb34, runBlock_reg _ _ _ (23 : Fin 32) s33.zero (by decide), g33_23]
  have g34_25 : reg n34 (25 : Fin 32) = x25 := by
    rw [rb34, runBlock_reg _ _ _ (25 : Fin 32) s33.zero (by decide), g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = x26 := by
    rw [rb34, runBlock_reg _ _ _ (26 : Fin 32) s33.zero (by decide), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb34, runBlock_reg _ _ _ (27 : Fin 32) s33.zero (by decide), g33_27]
  have g34_10 : reg n34 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by
    rw [rb34]; simp +decide only [runBlock, BInstr.run, svDp08e6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g33_2, g33_3, g33_4, g33_8, g33_9, g33_10, g33_11, g33_12, g33_13, g33_18, g33_19, g33_21, g33_22, g33_23, g33_25, g33_26, g33_27, s33.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g34_11 : reg n34 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb34]; simp +decide only [runBlock, BInstr.run, svDp08e6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g33_2, g33_3, g33_4, g33_8, g33_9, g33_10, g33_11, g33_12, g33_13, g33_18, g33_19, g33_21, g33_22, g33_23, g33_25, g33_26, g33_27, s33.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk34 : SvKeepL B n0.mem n34.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4)] := by rw [m34]; exact keep_kk33
  clear keep_kk33
  have w34_30 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m34]; exact w33_30
  have w34_34 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m34]; exact w33_34
  have w34_38 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m34]; exact w33_38
  have w34_3c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m34]; exact w33_3c
  have w34_40 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m34]; exact w33_40
  have w34_48 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m34]; exact w33_48
  have w34_4c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m34]; exact w33_4c
  have w34_50 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m34]; exact w33_50
  have w34_54 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m34]; exact w33_54
  have w34_58 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m34]; exact w33_58
  have w34_5c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m34]; exact w33_5c
  have w34_60 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m34]; exact w33_60
  have w34_64 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m34]; exact w33_64
  have w34_68 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m34]; exact w33_68
  have w34_6c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m34]; exact w33_6c
  have w34_70 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m34]; exact w33_70
  have w34_74 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m34]; exact w33_74
  have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m34]; exact w33_78
  have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m34]; exact w33_7c
  have w34_80 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m34]; exact w33_80
  have w34_84 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m34]; exact w33_84
  have w34_88 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m34]; exact w33_88
  have w34_8c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m34]; exact w33_8c
  have w34_90 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m34]; exact w33_90
  have w34_94 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m34]; exact w33_94
  have w34_a20 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m34]; exact w33_a20
  have w34_a24 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m34]; exact w33_a24
  have w34_a28 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m34]; exact w33_a28
  have w34_a2c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m34]; exact w33_a2c
  have w34_a30 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m34]; exact w33_a30
  have w34_a34 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m34]; exact w33_a34
  have w34_a38 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m34]; exact w33_a38
  have w34_a3c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m34]; exact w33_a3c
  have w34_a40 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m34]; exact w33_a40
  have w34_a44 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m34]; exact w33_a44
  have w34_1480 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m34]; exact w33_1480
  have w34_1484 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m34]; exact w33_1484
  have w34_1488 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = vp := by rw [m34]; exact w33_1488
  have w34_148c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = vl := by rw [m34]; exact w33_148c
  clear w33_148c w33_1488 w33_1484 w33_1480 w33_a44 w33_a40 w33_a3c w33_a38 w33_a34 w33_a30 w33_a2c w33_a28 w33_a24 w33_a20 w33_94 w33_90 w33_8c w33_88 w33_84 w33_80 w33_7c w33_78 w33_74 w33_70 w33_6c w33_68 w33_64 w33_60 w33_5c w33_58 w33_54 w33_50 w33_4c w33_48 w33_40 w33_3c w33_38 w33_34 w33_30 g33_27 g33_26 g33_25 g33_23 g33_22 g33_21 g33_19 g33_18 g33_13 g33_12 g33_11 g33_10 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 rg33 W33 K33 fr33 s33 d33
  -- 0x8F6: sv_tlvF
  obtain ⟨n35, c35, s35, rk35, K35, Ok35, Er35, fr35⟩ := sv_tlvF (oc := 0x1020) (dc := 0x1480)
    F E34 s34 sv_at_8f6 sv_at_8fa (by decide) (by decide) g34_10
    g34_11 (by decide) (by decide) (by decide) (by decide) (by decide)
    w34_1488 w34_148c
  have t35 : Steps n0 n35 := t34.trans c35
  have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.keepL K35 (by decide)
  rw [sv_mb fR34 val_in] at Ok35 Er35
  have g35_2 : reg n35 sp = B + 0x21A0 := by rw [rk35 sp (by decide) (by decide), g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk35 (3 : Fin 32) (by decide) (by decide), g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk35 (4 : Fin 32) (by decide) (by decide), g34_4]
  have g35_8 : reg n35 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rk35 (8 : Fin 32) (by decide) (by decide), g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = x9 := by rw [rk35 (9 : Fin 32) (by decide) (by decide), g34_9]
  have g35_10 : reg n35 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by rw [rk35 a0 (by decide) (by decide), g34_10]
  have g35_18 : reg n35 (18 : Fin 32) = out := by rw [rk35 (18 : Fin 32) (by decide) (by decide), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [rk35 (19 : Fin 32) (by decide) (by decide), g34_19]
  have g35_21 : reg n35 (21 : Fin 32) = x21 := by rw [rk35 (21 : Fin 32) (by decide) (by decide), g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rk35 (22 : Fin 32) (by decide) (by decide), g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [rk35 (23 : Fin 32) (by decide) (by decide), g34_23]
  have g35_25 : reg n35 (25 : Fin 32) = x25 := by rw [rk35 (25 : Fin 32) (by decide) (by decide), g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = x26 := by rw [rk35 (26 : Fin 32) (by decide) (by decide), g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk35 (27 : Fin 32) (by decide) (by decide), g34_27]
  obtain ⟨r35, hr35⟩ : ∃ r, derTlv (memBytes M0 (vp) (vl).toNat) = r := ⟨_, rfl⟩
  rcases r35 with er35 | tl35
  · obtain ⟨zhr35, -⟩ := Er35 er35 hr35
    have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := keep_kk34.trans K35
    clear keep_kk34
    have w35_30 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K35.w32 (by decide) (by decide)).trans w34_30
    have w35_34 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K35.w32 (by decide) (by decide)).trans w34_34
    have w35_38 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K35.w32 (by decide) (by decide)).trans w34_38
    have w35_3c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K35.w32 (by decide) (by decide)).trans w34_3c
    have w35_40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K35.w32 (by decide) (by decide)).trans w34_40
    have w35_48 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K35.w32 (by decide) (by decide)).trans w34_48
    have w35_4c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K35.w32 (by decide) (by decide)).trans w34_4c
    have w35_50 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K35.w32 (by decide) (by decide)).trans w34_50
    have w35_54 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K35.w32 (by decide) (by decide)).trans w34_54
    have w35_58 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K35.w32 (by decide) (by decide)).trans w34_58
    have w35_5c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K35.w32 (by decide) (by decide)).trans w34_5c
    have w35_60 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K35.w32 (by decide) (by decide)).trans w34_60
    have w35_64 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K35.w32 (by decide) (by decide)).trans w34_64
    have w35_68 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K35.w32 (by decide) (by decide)).trans w34_68
    have w35_6c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K35.w32 (by decide) (by decide)).trans w34_6c
    have w35_70 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K35.w32 (by decide) (by decide)).trans w34_70
    have w35_74 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K35.w32 (by decide) (by decide)).trans w34_74
    have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K35.w32 (by decide) (by decide)).trans w34_78
    have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K35.w32 (by decide) (by decide)).trans w34_7c
    have w35_80 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K35.w32 (by decide) (by decide)).trans w34_80
    have w35_84 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K35.w32 (by decide) (by decide)).trans w34_84
    have w35_88 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K35.w32 (by decide) (by decide)).trans w34_88
    have w35_8c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K35.w32 (by decide) (by decide)).trans w34_8c
    have w35_90 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K35.w32 (by decide) (by decide)).trans w34_90
    have w35_94 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K35.w32 (by decide) (by decide)).trans w34_94
    have w35_a20 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K35.w32 (by decide) (by decide)).trans w34_a20
    have w35_a24 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K35.w32 (by decide) (by decide)).trans w34_a24
    have w35_a28 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K35.w32 (by decide) (by decide)).trans w34_a28
    have w35_a2c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K35.w32 (by decide) (by decide)).trans w34_a2c
    have w35_a30 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K35.w32 (by decide) (by decide)).trans w34_a30
    have w35_a34 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K35.w32 (by decide) (by decide)).trans w34_a34
    have w35_a38 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K35.w32 (by decide) (by decide)).trans w34_a38
    have w35_a3c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K35.w32 (by decide) (by decide)).trans w34_a3c
    have w35_a40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K35.w32 (by decide) (by decide)).trans w34_a40
    have w35_a44 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K35.w32 (by decide) (by decide)).trans w34_a44
    have w35_1480 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K35.w32 (by decide) (by decide)).trans w34_1480
    have w35_1484 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K35.w32 (by decide) (by decide)).trans w34_1484
    have w35_1020 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := zhr35
    clear w34_148c w34_1488 w34_1484 w34_1480 w34_a44 w34_a40 w34_a3c w34_a38 w34_a34 w34_a30 w34_a2c w34_a28 w34_a24 w34_a20 w34_94 w34_90 w34_8c w34_88 w34_84 w34_80 w34_7c w34_78 w34_74 w34_70 w34_6c w34_68 w34_64 w34_60 w34_5c w34_58 w34_54 w34_50 w34_4c w34_48 w34_40 w34_3c w34_38 w34_34 w34_30 g34_11 g34_10 g34_27 g34_26 g34_25 g34_23 g34_22 g34_21 g34_19 g34_18 g34_13 g34_12 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 rb34 s34 m34 u34 c34
    -- 0x8FE: lw
    obtain ⟨n36, d36, u36⟩ := s35.lw E35.self sv_at_8fe (off' := 0x902) (by decide)
      (by rw [g35_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x600 = B + 0x21A0 + BitVec.ofNat 32 0x1020 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s36 : St n36.mem SV n36 0x902 (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
    have m36 : n36.mem = n35.mem := u36.mem
    have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
    have t36 : Steps n0 n36 := t35.trans (.single d36)
    have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
    have E36 : SvCode n36.mem := E35.fr F fr36
    have V36 : SvSaves B n36.mem v := V35.same m36
    have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_2]
    have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_3]
    have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_4]
    have g36_8 : reg n36 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_8]
    have g36_9 : reg n36 (9 : Fin 32) = x9 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_9]
    have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, upd_ne (by decide) (by decide), g35_18]
    have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_19]
    have g36_21 : reg n36 (21 : Fin 32) = x21 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_21]
    have g36_22 : reg n36 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_22]
    have g36_23 : reg n36 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_23]
    have g36_25 : reg n36 (25 : Fin 32) = x25 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_25]
    have g36_26 : reg n36 (26 : Fin 32) = x26 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_26]
    have g36_27 : reg n36 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_27]
    have g36_10 : reg n36 a0 = 0 := by
      rw [u36.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g35_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x600 = B + 0x21A0 + BitVec.ofNat 32 0x1020 by sv_addr, w35_1020]
    have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := by rw [m36]; exact keep_kk35
    clear keep_kk35
    have w36_30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m36]; exact w35_30
    have w36_34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m36]; exact w35_34
    have w36_38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m36]; exact w35_38
    have w36_3c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m36]; exact w35_3c
    have w36_40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m36]; exact w35_40
    have w36_48 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m36]; exact w35_48
    have w36_4c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m36]; exact w35_4c
    have w36_50 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m36]; exact w35_50
    have w36_54 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m36]; exact w35_54
    have w36_58 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m36]; exact w35_58
    have w36_5c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m36]; exact w35_5c
    have w36_60 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m36]; exact w35_60
    have w36_64 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m36]; exact w35_64
    have w36_68 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m36]; exact w35_68
    have w36_6c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m36]; exact w35_6c
    have w36_70 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m36]; exact w35_70
    have w36_74 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m36]; exact w35_74
    have w36_78 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m36]; exact w35_78
    have w36_7c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m36]; exact w35_7c
    have w36_80 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m36]; exact w35_80
    have w36_84 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m36]; exact w35_84
    have w36_88 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m36]; exact w35_88
    have w36_8c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m36]; exact w35_8c
    have w36_90 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m36]; exact w35_90
    have w36_94 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m36]; exact w35_94
    have w36_a20 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m36]; exact w35_a20
    have w36_a24 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m36]; exact w35_a24
    have w36_a28 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m36]; exact w35_a28
    have w36_a2c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m36]; exact w35_a2c
    have w36_a30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m36]; exact w35_a30
    have w36_a34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m36]; exact w35_a34
    have w36_a38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m36]; exact w35_a38
    have w36_a3c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m36]; exact w35_a3c
    have w36_a40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m36]; exact w35_a40
    have w36_a44 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m36]; exact w35_a44
    have w36_1020 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m36]; exact w35_1020
    have w36_1480 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m36]; exact w35_1480
    have w36_1484 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m36]; exact w35_1484
    clear w35_1020 w35_1484 w35_1480 w35_a44 w35_a40 w35_a3c w35_a38 w35_a34 w35_a30 w35_a2c w35_a28 w35_a24 w35_a20 w35_94 w35_90 w35_8c w35_88 w35_84 w35_80 w35_7c w35_78 w35_74 w35_70 w35_6c w35_68 w35_64 w35_60 w35_5c w35_58 w35_54 w35_50 w35_4c w35_48 w35_40 w35_3c w35_38 w35_34 w35_30 zhr35
    -- 0x902: branch, taken
    obtain ⟨n37, d37, u37⟩ := s36.taken E36.self 0x9BA sv_at_902
      (by decide) (by rw [g36_10, s36.zero]; rfl)
    have s37 : St n37.mem SV n37 0x9BA (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
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
    have g37_10 : reg n37 a0 = 0 := by rw [u37.regs, g36_10]
    have g37_18 : reg n37 (18 : Fin 32) = out := by rw [u37.regs, g36_18]
    have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [u37.regs, g36_19]
    have g37_21 : reg n37 (21 : Fin 32) = x21 := by rw [u37.regs, g36_21]
    have g37_22 : reg n37 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u37.regs, g36_22]
    have g37_23 : reg n37 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u37.regs, g36_23]
    have g37_25 : reg n37 (25 : Fin 32) = x25 := by rw [u37.regs, g36_25]
    have g37_26 : reg n37 (26 : Fin 32) = x26 := by rw [u37.regs, g36_26]
    have g37_27 : reg n37 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u37.regs, g36_27]
    have keep_kk37 : SvKeepL B n0.mem n37.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := by rw [m37]; exact keep_kk36
    clear keep_kk36
    have w37_30 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m37]; exact w36_30
    have w37_34 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m37]; exact w36_34
    have w37_38 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m37]; exact w36_38
    have w37_3c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m37]; exact w36_3c
    have w37_40 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m37]; exact w36_40
    have w37_48 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m37]; exact w36_48
    have w37_4c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m37]; exact w36_4c
    have w37_50 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m37]; exact w36_50
    have w37_54 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m37]; exact w36_54
    have w37_58 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m37]; exact w36_58
    have w37_5c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m37]; exact w36_5c
    have w37_60 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m37]; exact w36_60
    have w37_64 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m37]; exact w36_64
    have w37_68 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m37]; exact w36_68
    have w37_6c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m37]; exact w36_6c
    have w37_70 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m37]; exact w36_70
    have w37_74 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m37]; exact w36_74
    have w37_78 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m37]; exact w36_78
    have w37_7c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m37]; exact w36_7c
    have w37_80 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m37]; exact w36_80
    have w37_84 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m37]; exact w36_84
    have w37_88 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m37]; exact w36_88
    have w37_8c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m37]; exact w36_8c
    have w37_90 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m37]; exact w36_90
    have w37_94 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m37]; exact w36_94
    have w37_a20 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m37]; exact w36_a20
    have w37_a24 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m37]; exact w36_a24
    have w37_a28 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m37]; exact w36_a28
    have w37_a2c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m37]; exact w36_a2c
    have w37_a30 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m37]; exact w36_a30
    have w37_a34 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m37]; exact w36_a34
    have w37_a38 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m37]; exact w36_a38
    have w37_a3c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m37]; exact w36_a3c
    have w37_a40 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m37]; exact w36_a40
    have w37_a44 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m37]; exact w36_a44
    have w37_1020 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m37]; exact w36_1020
    have w37_1480 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m37]; exact w36_1480
    have w37_1484 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m37]; exact w36_1484
    clear w36_1484 w36_1480 w36_1020 w36_a44 w36_a40 w36_a3c w36_a38 w36_a34 w36_a30 w36_a2c w36_a28 w36_a24 w36_a20 w36_94 w36_90 w36_8c w36_88 w36_84 w36_80 w36_7c w36_78 w36_74 w36_70 w36_6c w36_68 w36_64 w36_60 w36_5c w36_58 w36_54 w36_50 w36_4c w36_48 w36_40 w36_3c w36_38 w36_34 w36_30 g36_10 g36_27 g36_26 g36_25 g36_23 g36_22 g36_21 g36_19 g36_18 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 m36 s36 u36 d36
    -- 0x9BA: lbu
    obtain ⟨n38, d38, u38⟩ := s37.lbu E37.self sv_at_9ba (off' := 0x9BE) (by decide)
    have s38 : St n38.mem SV n38 0x9BE (reg n38) := ⟨u38.pc, rfl, fun _ => rfl⟩
    have m38 : n38.mem = n37.mem := u38.mem
    have fr38 : ∀ x, SvR B x → n38.mem x = n37.mem x := fun x _ => by rw [m38]
    have t38 : Steps n0 n38 := t37.trans (.single d38)
    have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
    have E38 : SvCode n38.mem := E37.fr F fr38
    have V38 : SvSaves B n38.mem v := V37.same m38
    have g38_2 : reg n38 sp = B + 0x21A0 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_2]
    have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_3]
    have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_4]
    have g38_8 : reg n38 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_8]
    have g38_9 : reg n38 (9 : Fin 32) = x9 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_9]
    have g38_18 : reg n38 (18 : Fin 32) = out := by rw [u38.regs, upd_ne (by decide) (by decide), g37_18]
    have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_19]
    have g38_21 : reg n38 (21 : Fin 32) = x21 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_21]
    have g38_22 : reg n38 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_22]
    have g38_23 : reg n38 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_23]
    have g38_25 : reg n38 (25 : Fin 32) = x25 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_25]
    have g38_26 : reg n38 (26 : Fin 32) = x26 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_26]
    have g38_27 : reg n38 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_27]
    have keep_kk38 : SvKeepL B n0.mem n38.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := by rw [m38]; exact keep_kk37
    clear keep_kk37
    have w38_30 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m38]; exact w37_30
    have w38_34 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m38]; exact w37_34
    have w38_38 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m38]; exact w37_38
    have w38_3c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m38]; exact w37_3c
    have w38_40 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m38]; exact w37_40
    have w38_48 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m38]; exact w37_48
    have w38_4c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m38]; exact w37_4c
    have w38_50 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m38]; exact w37_50
    have w38_54 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m38]; exact w37_54
    have w38_58 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m38]; exact w37_58
    have w38_5c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m38]; exact w37_5c
    have w38_60 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m38]; exact w37_60
    have w38_64 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m38]; exact w37_64
    have w38_68 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m38]; exact w37_68
    have w38_6c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m38]; exact w37_6c
    have w38_70 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m38]; exact w37_70
    have w38_74 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m38]; exact w37_74
    have w38_78 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m38]; exact w37_78
    have w38_7c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m38]; exact w37_7c
    have w38_80 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m38]; exact w37_80
    have w38_84 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m38]; exact w37_84
    have w38_88 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m38]; exact w37_88
    have w38_8c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m38]; exact w37_8c
    have w38_90 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m38]; exact w37_90
    have w38_94 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m38]; exact w37_94
    have w38_a20 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m38]; exact w37_a20
    have w38_a24 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m38]; exact w37_a24
    have w38_a28 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m38]; exact w37_a28
    have w38_a2c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m38]; exact w37_a2c
    have w38_a30 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m38]; exact w37_a30
    have w38_a34 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m38]; exact w37_a34
    have w38_a38 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m38]; exact w37_a38
    have w38_a3c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m38]; exact w37_a3c
    have w38_a40 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m38]; exact w37_a40
    have w38_a44 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m38]; exact w37_a44
    have w38_1020 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m38]; exact w37_1020
    have w38_1480 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m38]; exact w37_1480
    have w38_1484 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m38]; exact w37_1484
    clear w37_1484 w37_1480 w37_1020 w37_a44 w37_a40 w37_a3c w37_a38 w37_a34 w37_a30 w37_a2c w37_a28 w37_a24 w37_a20 w37_94 w37_90 w37_8c w37_88 w37_84 w37_80 w37_7c w37_78 w37_74 w37_70 w37_6c w37_68 w37_64 w37_60 w37_5c w37_58 w37_54 w37_50 w37_4c w37_48 w37_40 w37_3c w37_38 w37_34 w37_30 g37_27 g37_26 g37_25 g37_23 g37_22 g37_21 g37_19 g37_18 g37_10 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 m37 s37 u37 d37
    -- 0x9BE: j
    obtain ⟨n39, d39, u39⟩ := s38.jump E38.self sv_at_9be (off' := 0xB38) (by decide)
      (by rw [s38.pc]; decide)
    have s39 : St n39.mem SV n39 0xB38 (reg n39) := ⟨u39.pc, rfl, fun _ => rfl⟩
    have m39 : n39.mem = n38.mem := u39.mem
    have fr39 : ∀ x, SvR B x → n39.mem x = n38.mem x := fun x _ => by rw [m39]
    have t39 : Steps n0 n39 := t38.trans (.single d39)
    have fR39 : ∀ x, SvR B x → n39.mem x = M0 x := fun x hx => (fr39 x hx).trans (fR38 x hx)
    have E39 : SvCode n39.mem := E38.fr F fr39
    have V39 : SvSaves B n39.mem v := V38.same m39
    have g39_2 : reg n39 sp = B + 0x21A0 := by rw [u39.regs, g38_2]
    have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u39.regs, g38_3]
    have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u39.regs, g38_4]
    have g39_8 : reg n39 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u39.regs, g38_8]
    have g39_9 : reg n39 (9 : Fin 32) = x9 := by rw [u39.regs, g38_9]
    have g39_18 : reg n39 (18 : Fin 32) = out := by rw [u39.regs, g38_18]
    have g39_19 : reg n39 (19 : Fin 32) = bp := by rw [u39.regs, g38_19]
    have g39_21 : reg n39 (21 : Fin 32) = x21 := by rw [u39.regs, g38_21]
    have g39_22 : reg n39 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u39.regs, g38_22]
    have g39_23 : reg n39 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u39.regs, g38_23]
    have g39_25 : reg n39 (25 : Fin 32) = x25 := by rw [u39.regs, g38_25]
    have g39_26 : reg n39 (26 : Fin 32) = x26 := by rw [u39.regs, g38_26]
    have g39_27 : reg n39 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u39.regs, g38_27]
    have keep_kk39 : SvKeepL B n0.mem n39.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := by rw [m39]; exact keep_kk38
    clear keep_kk38
    have w39_30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m39]; exact w38_30
    have w39_34 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m39]; exact w38_34
    have w39_38 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m39]; exact w38_38
    have w39_3c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m39]; exact w38_3c
    have w39_40 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m39]; exact w38_40
    have w39_48 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m39]; exact w38_48
    have w39_4c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m39]; exact w38_4c
    have w39_50 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m39]; exact w38_50
    have w39_54 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m39]; exact w38_54
    have w39_58 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m39]; exact w38_58
    have w39_5c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m39]; exact w38_5c
    have w39_60 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m39]; exact w38_60
    have w39_64 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m39]; exact w38_64
    have w39_68 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m39]; exact w38_68
    have w39_6c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m39]; exact w38_6c
    have w39_70 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m39]; exact w38_70
    have w39_74 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m39]; exact w38_74
    have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m39]; exact w38_78
    have w39_7c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m39]; exact w38_7c
    have w39_80 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m39]; exact w38_80
    have w39_84 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m39]; exact w38_84
    have w39_88 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m39]; exact w38_88
    have w39_8c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m39]; exact w38_8c
    have w39_90 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m39]; exact w38_90
    have w39_94 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m39]; exact w38_94
    have w39_a20 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m39]; exact w38_a20
    have w39_a24 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m39]; exact w38_a24
    have w39_a28 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m39]; exact w38_a28
    have w39_a2c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m39]; exact w38_a2c
    have w39_a30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m39]; exact w38_a30
    have w39_a34 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m39]; exact w38_a34
    have w39_a38 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m39]; exact w38_a38
    have w39_a3c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m39]; exact w38_a3c
    have w39_a40 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m39]; exact w38_a40
    have w39_a44 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m39]; exact w38_a44
    have w39_1020 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m39]; exact w38_1020
    have w39_1480 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m39]; exact w38_1480
    have w39_1484 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m39]; exact w38_1484
    clear w38_1484 w38_1480 w38_1020 w38_a44 w38_a40 w38_a3c w38_a38 w38_a34 w38_a30 w38_a2c w38_a28 w38_a24 w38_a20 w38_94 w38_90 w38_8c w38_88 w38_84 w38_80 w38_7c w38_78 w38_74 w38_70 w38_6c w38_68 w38_64 w38_60 w38_5c w38_58 w38_54 w38_50 w38_4c w38_48 w38_40 w38_3c w38_38 w38_34 w38_30 g38_27 g38_26 g38_25 g38_23 g38_22 g38_21 g38_19 g38_18 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 m38 s38 u38 d38
    -- 0xB38: sw
    obtain ⟨n40, d40, s40, fr40, K40, W40, rg40⟩ := sv_sw F E39 s39 sv_at_b38 (off' := 0xB3A) (c := 0x44)
      (by decide) (by rw [g39_2]; sv_addr) (by decide) (by decide)
    have t40 : Steps n0 n40 := t39.trans d40
    have fR40 : ∀ x, SvR B x → n40.mem x = M0 x := fun x hx => (fr40 x hx).trans (fR39 x hx)
    have E40 : SvCode n40.mem := E39.fr F fr40
    have V40 : SvSaves B n40.mem v := V39.keep K40 (by decide)
    have g40_2 : reg n40 sp = B + 0x21A0 := by rw [rg40 sp, g39_2]
    have g40_3 : reg n40 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg40 (3 : Fin 32), g39_3]
    have g40_4 : reg n40 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg40 (4 : Fin 32), g39_4]
    have g40_8 : reg n40 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg40 (8 : Fin 32), g39_8]
    have g40_9 : reg n40 (9 : Fin 32) = x9 := by rw [rg40 (9 : Fin 32), g39_9]
    have g40_18 : reg n40 (18 : Fin 32) = out := by rw [rg40 (18 : Fin 32), g39_18]
    have g40_19 : reg n40 (19 : Fin 32) = bp := by rw [rg40 (19 : Fin 32), g39_19]
    have g40_21 : reg n40 (21 : Fin 32) = x21 := by rw [rg40 (21 : Fin 32), g39_21]
    have g40_22 : reg n40 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg40 (22 : Fin 32), g39_22]
    have g40_23 : reg n40 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [rg40 (23 : Fin 32), g39_23]
    have g40_25 : reg n40 (25 : Fin 32) = x25 := by rw [rg40 (25 : Fin 32), g39_25]
    have g40_26 : reg n40 (26 : Fin 32) = x26 := by rw [rg40 (26 : Fin 32), g39_26]
    have g40_27 : reg n40 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg40 (27 : Fin 32), g39_27]
    have keep_kk40 : SvKeepL B n0.mem n40.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0x44, 0x4)] := keep_kk39.trans K40.toL
    clear keep_kk39
    have w40_30 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K40.w32 (by decide) (by decide)).trans w39_30
    have w40_34 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K40.w32 (by decide) (by decide)).trans w39_34
    have w40_38 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K40.w32 (by decide) (by decide)).trans w39_38
    have w40_3c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K40.w32 (by decide) (by decide)).trans w39_3c
    have w40_40 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K40.w32 (by decide) (by decide)).trans w39_40
    have w40_48 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K40.w32 (by decide) (by decide)).trans w39_48
    have w40_4c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K40.w32 (by decide) (by decide)).trans w39_4c
    have w40_50 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K40.w32 (by decide) (by decide)).trans w39_50
    have w40_54 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K40.w32 (by decide) (by decide)).trans w39_54
    have w40_58 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K40.w32 (by decide) (by decide)).trans w39_58
    have w40_5c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K40.w32 (by decide) (by decide)).trans w39_5c
    have w40_60 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K40.w32 (by decide) (by decide)).trans w39_60
    have w40_64 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K40.w32 (by decide) (by decide)).trans w39_64
    have w40_68 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K40.w32 (by decide) (by decide)).trans w39_68
    have w40_6c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K40.w32 (by decide) (by decide)).trans w39_6c
    have w40_70 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K40.w32 (by decide) (by decide)).trans w39_70
    have w40_74 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K40.w32 (by decide) (by decide)).trans w39_74
    have w40_78 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K40.w32 (by decide) (by decide)).trans w39_78
    have w40_7c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K40.w32 (by decide) (by decide)).trans w39_7c
    have w40_80 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K40.w32 (by decide) (by decide)).trans w39_80
    have w40_84 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K40.w32 (by decide) (by decide)).trans w39_84
    have w40_88 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K40.w32 (by decide) (by decide)).trans w39_88
    have w40_8c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K40.w32 (by decide) (by decide)).trans w39_8c
    have w40_90 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K40.w32 (by decide) (by decide)).trans w39_90
    have w40_94 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K40.w32 (by decide) (by decide)).trans w39_94
    have w40_a20 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K40.w32 (by decide) (by decide)).trans w39_a20
    have w40_a24 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K40.w32 (by decide) (by decide)).trans w39_a24
    have w40_a28 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K40.w32 (by decide) (by decide)).trans w39_a28
    have w40_a2c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K40.w32 (by decide) (by decide)).trans w39_a2c
    have w40_a30 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K40.w32 (by decide) (by decide)).trans w39_a30
    have w40_a34 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K40.w32 (by decide) (by decide)).trans w39_a34
    have w40_a38 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K40.w32 (by decide) (by decide)).trans w39_a38
    have w40_a3c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K40.w32 (by decide) (by decide)).trans w39_a3c
    have w40_a40 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K40.w32 (by decide) (by decide)).trans w39_a40
    have w40_a44 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K40.w32 (by decide) (by decide)).trans w39_a44
    have w40_1020 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := (K40.w32 (by decide) (by decide)).trans w39_1020
    have w40_1480 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K40.w32 (by decide) (by decide)).trans w39_1480
    have w40_1484 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K40.w32 (by decide) (by decide)).trans w39_1484
    clear w39_1484 w39_1480 w39_1020 w39_a44 w39_a40 w39_a3c w39_a38 w39_a34 w39_a30 w39_a2c w39_a28 w39_a24 w39_a20 w39_94 w39_90 w39_8c w39_88 w39_84 w39_80 w39_7c w39_78 w39_74 w39_70 w39_6c w39_68 w39_64 w39_60 w39_5c w39_58 w39_54 w39_50 w39_4c w39_48 w39_40 w39_3c w39_38 w39_34 w39_30 g39_27 g39_26 g39_25 g39_23 g39_22 g39_21 g39_19 g39_18 g39_9 g39_8 g39_4 g39_3 g39_2 V39 E39 fR39 t39 fr39 m39 s39 u39 d39
    -- 0xB3A: j
    obtain ⟨n41, d41, u41⟩ := s40.jump E40.self sv_at_b3a (off' := 0xB46) (by decide)
      (by rw [s40.pc]; decide)
    have s41 : St n41.mem SV n41 0xB46 (reg n41) := ⟨u41.pc, rfl, fun _ => rfl⟩
    have m41 : n41.mem = n40.mem := u41.mem
    have fr41 : ∀ x, SvR B x → n41.mem x = n40.mem x := fun x _ => by rw [m41]
    have t41 : Steps n0 n41 := t40.trans (.single d41)
    have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
    have E41 : SvCode n41.mem := E40.fr F fr41
    have V41 : SvSaves B n41.mem v := V40.same m41
    have g41_2 : reg n41 sp = B + 0x21A0 := by rw [u41.regs, g40_2]
    have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u41.regs, g40_3]
    have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u41.regs, g40_4]
    have g41_8 : reg n41 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u41.regs, g40_8]
    have g41_9 : reg n41 (9 : Fin 32) = x9 := by rw [u41.regs, g40_9]
    have g41_18 : reg n41 (18 : Fin 32) = out := by rw [u41.regs, g40_18]
    have g41_19 : reg n41 (19 : Fin 32) = bp := by rw [u41.regs, g40_19]
    have g41_21 : reg n41 (21 : Fin 32) = x21 := by rw [u41.regs, g40_21]
    have g41_22 : reg n41 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u41.regs, g40_22]
    have g41_23 : reg n41 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u41.regs, g40_23]
    have g41_25 : reg n41 (25 : Fin 32) = x25 := by rw [u41.regs, g40_25]
    have g41_26 : reg n41 (26 : Fin 32) = x26 := by rw [u41.regs, g40_26]
    have g41_27 : reg n41 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u41.regs, g40_27]
    have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0x44, 0x4)] := by rw [m41]; exact keep_kk40
    clear keep_kk40
    have w41_30 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m41]; exact w40_30
    have w41_34 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m41]; exact w40_34
    have w41_38 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m41]; exact w40_38
    have w41_3c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m41]; exact w40_3c
    have w41_40 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m41]; exact w40_40
    have w41_48 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m41]; exact w40_48
    have w41_4c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m41]; exact w40_4c
    have w41_50 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m41]; exact w40_50
    have w41_54 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m41]; exact w40_54
    have w41_58 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m41]; exact w40_58
    have w41_5c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m41]; exact w40_5c
    have w41_60 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m41]; exact w40_60
    have w41_64 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m41]; exact w40_64
    have w41_68 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m41]; exact w40_68
    have w41_6c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m41]; exact w40_6c
    have w41_70 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m41]; exact w40_70
    have w41_74 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m41]; exact w40_74
    have w41_78 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m41]; exact w40_78
    have w41_7c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m41]; exact w40_7c
    have w41_80 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m41]; exact w40_80
    have w41_84 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m41]; exact w40_84
    have w41_88 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m41]; exact w40_88
    have w41_8c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m41]; exact w40_8c
    have w41_90 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m41]; exact w40_90
    have w41_94 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m41]; exact w40_94
    have w41_a20 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m41]; exact w40_a20
    have w41_a24 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m41]; exact w40_a24
    have w41_a28 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m41]; exact w40_a28
    have w41_a2c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m41]; exact w40_a2c
    have w41_a30 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m41]; exact w40_a30
    have w41_a34 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m41]; exact w40_a34
    have w41_a38 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m41]; exact w40_a38
    have w41_a3c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m41]; exact w40_a3c
    have w41_a40 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m41]; exact w40_a40
    have w41_a44 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m41]; exact w40_a44
    have w41_1020 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m41]; exact w40_1020
    have w41_1480 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m41]; exact w40_1480
    have w41_1484 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m41]; exact w40_1484
    clear w40_1484 w40_1480 w40_1020 w40_a44 w40_a40 w40_a3c w40_a38 w40_a34 w40_a30 w40_a2c w40_a28 w40_a24 w40_a20 w40_94 w40_90 w40_8c w40_88 w40_84 w40_80 w40_7c w40_78 w40_74 w40_70 w40_6c w40_68 w40_64 w40_60 w40_5c w40_58 w40_54 w40_50 w40_4c w40_48 w40_40 w40_3c w40_38 w40_34 w40_30 g40_27 g40_26 g40_25 g40_23 g40_22 g40_21 g40_19 g40_18 g40_9 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 rg40 W40 K40 fr40 s40 d40
    -- 0xB46: lw
    obtain ⟨n42, d42, u42⟩ := s41.lw E41.self sv_at_b46 (off' := 0xB48) (by decide)
      (by rw [g41_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s42 : St n42.mem SV n42 0xB48 (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
    have m42 : n42.mem = n41.mem := u42.mem
    have fr42 : ∀ x, SvR B x → n42.mem x = n41.mem x := fun x _ => by rw [m42]
    have t42 : Steps n0 n42 := t41.trans (.single d42)
    have fR42 : ∀ x, SvR B x → n42.mem x = M0 x := fun x hx => (fr42 x hx).trans (fR41 x hx)
    have E42 : SvCode n42.mem := E41.fr F fr42
    have V42 : SvSaves B n42.mem v := V41.same m42
    have g42_2 : reg n42 sp = B + 0x21A0 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_2]
    have g42_3 : reg n42 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u42.regs, upd_ne (by decide) (by decide), g41_3]
    have g42_4 : reg n42 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u42.regs, upd_ne (by decide) (by decide), g41_4]
    have g42_8 : reg n42 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_8]
    have g42_9 : reg n42 (9 : Fin 32) = x9 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_9]
    have g42_18 : reg n42 (18 : Fin 32) = out := by rw [u42.regs, upd_ne (by decide) (by decide), g41_18]
    have g42_19 : reg n42 (19 : Fin 32) = bp := by rw [u42.regs, upd_ne (by decide) (by decide), g41_19]
    have g42_21 : reg n42 (21 : Fin 32) = x21 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_21]
    have g42_22 : reg n42 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_22]
    have g42_23 : reg n42 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_23]
    have g42_25 : reg n42 (25 : Fin 32) = x25 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_25]
    have g42_26 : reg n42 (26 : Fin 32) = x26 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_26]
    have g42_27 : reg n42 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u42.regs, upd_ne (by decide) (by decide), g41_27]
    have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0x44, 0x4)] := by rw [m42]; exact keep_kk41
    clear keep_kk41
    have w42_30 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m42]; exact w41_30
    have w42_34 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m42]; exact w41_34
    have w42_38 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m42]; exact w41_38
    have w42_3c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m42]; exact w41_3c
    have w42_40 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m42]; exact w41_40
    have w42_48 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m42]; exact w41_48
    have w42_4c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m42]; exact w41_4c
    have w42_50 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m42]; exact w41_50
    have w42_54 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m42]; exact w41_54
    have w42_58 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m42]; exact w41_58
    have w42_5c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m42]; exact w41_5c
    have w42_60 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m42]; exact w41_60
    have w42_64 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m42]; exact w41_64
    have w42_68 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m42]; exact w41_68
    have w42_6c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m42]; exact w41_6c
    have w42_70 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m42]; exact w41_70
    have w42_74 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m42]; exact w41_74
    have w42_78 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m42]; exact w41_78
    have w42_7c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m42]; exact w41_7c
    have w42_80 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m42]; exact w41_80
    have w42_84 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m42]; exact w41_84
    have w42_88 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m42]; exact w41_88
    have w42_8c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m42]; exact w41_8c
    have w42_90 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m42]; exact w41_90
    have w42_94 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m42]; exact w41_94
    have w42_a20 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m42]; exact w41_a20
    have w42_a24 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m42]; exact w41_a24
    have w42_a28 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m42]; exact w41_a28
    have w42_a2c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m42]; exact w41_a2c
    have w42_a30 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m42]; exact w41_a30
    have w42_a34 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m42]; exact w41_a34
    have w42_a38 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m42]; exact w41_a38
    have w42_a3c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m42]; exact w41_a3c
    have w42_a40 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m42]; exact w41_a40
    have w42_a44 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m42]; exact w41_a44
    have w42_1020 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m42]; exact w41_1020
    have w42_1480 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m42]; exact w41_1480
    have w42_1484 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m42]; exact w41_1484
    clear w41_1484 w41_1480 w41_1020 w41_a44 w41_a40 w41_a3c w41_a38 w41_a34 w41_a30 w41_a2c w41_a28 w41_a24 w41_a20 w41_94 w41_90 w41_8c w41_88 w41_84 w41_80 w41_7c w41_78 w41_74 w41_70 w41_6c w41_68 w41_64 w41_60 w41_5c w41_58 w41_54 w41_50 w41_4c w41_48 w41_40 w41_3c w41_38 w41_34 w41_30 g41_27 g41_26 g41_25 g41_23 g41_22 g41_21 g41_19 g41_18 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 fr41 m41 s41 u41 d41
    -- 0xB48: j
    obtain ⟨n43, d43, u43⟩ := s42.jump E42.self sv_at_b48 (off' := 0x966) (by decide)
      (by rw [s42.pc]; decide)
    have s43 : St n43.mem SV n43 0x966 (reg n43) := ⟨u43.pc, rfl, fun _ => rfl⟩
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
    have g43_18 : reg n43 (18 : Fin 32) = out := by rw [u43.regs, g42_18]
    have g43_19 : reg n43 (19 : Fin 32) = bp := by rw [u43.regs, g42_19]
    have g43_21 : reg n43 (21 : Fin 32) = x21 := by rw [u43.regs, g42_21]
    have g43_22 : reg n43 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u43.regs, g42_22]
    have g43_23 : reg n43 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u43.regs, g42_23]
    have g43_25 : reg n43 (25 : Fin 32) = x25 := by rw [u43.regs, g42_25]
    have g43_26 : reg n43 (26 : Fin 32) = x26 := by rw [u43.regs, g42_26]
    have g43_27 : reg n43 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u43.regs, g42_27]
    have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0x44, 0x4)] := by rw [m43]; exact keep_kk42
    clear keep_kk42
    have w43_30 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m43]; exact w42_30
    have w43_34 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m43]; exact w42_34
    have w43_38 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m43]; exact w42_38
    have w43_3c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m43]; exact w42_3c
    have w43_40 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m43]; exact w42_40
    have w43_48 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m43]; exact w42_48
    have w43_4c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m43]; exact w42_4c
    have w43_50 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m43]; exact w42_50
    have w43_54 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m43]; exact w42_54
    have w43_58 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m43]; exact w42_58
    have w43_5c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m43]; exact w42_5c
    have w43_60 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m43]; exact w42_60
    have w43_64 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m43]; exact w42_64
    have w43_68 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m43]; exact w42_68
    have w43_6c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m43]; exact w42_6c
    have w43_70 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m43]; exact w42_70
    have w43_74 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m43]; exact w42_74
    have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m43]; exact w42_78
    have w43_7c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m43]; exact w42_7c
    have w43_80 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m43]; exact w42_80
    have w43_84 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m43]; exact w42_84
    have w43_88 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m43]; exact w42_88
    have w43_8c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m43]; exact w42_8c
    have w43_90 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m43]; exact w42_90
    have w43_94 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m43]; exact w42_94
    have w43_a20 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m43]; exact w42_a20
    have w43_a24 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m43]; exact w42_a24
    have w43_a28 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m43]; exact w42_a28
    have w43_a2c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m43]; exact w42_a2c
    have w43_a30 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m43]; exact w42_a30
    have w43_a34 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m43]; exact w42_a34
    have w43_a38 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m43]; exact w42_a38
    have w43_a3c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m43]; exact w42_a3c
    have w43_a40 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m43]; exact w42_a40
    have w43_a44 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m43]; exact w42_a44
    have w43_1020 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m43]; exact w42_1020
    have w43_1480 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m43]; exact w42_1480
    have w43_1484 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m43]; exact w42_1484
    clear w42_1484 w42_1480 w42_1020 w42_a44 w42_a40 w42_a3c w42_a38 w42_a34 w42_a30 w42_a2c w42_a28 w42_a24 w42_a20 w42_94 w42_90 w42_8c w42_88 w42_84 w42_80 w42_7c w42_78 w42_74 w42_70 w42_6c w42_68 w42_64 w42_60 w42_5c w42_58 w42_54 w42_50 w42_4c w42_48 w42_40 w42_3c w42_38 w42_34 w42_30 g42_27 g42_26 g42_25 g42_23 g42_22 g42_21 g42_19 g42_18 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 m42 s42 u42 d42
    exact .inl ⟨(fun ⟨tl35', h0', _⟩ => by rw [hr35] at h0'; cases h0'), sv_fail F E43 s43 t43 (fun x hx => (fR43 x hx).trans (fM x hx).symm) V43 hret g43_2 g43_18 hO g43_3 g43_4⟩
  obtain ⟨o0_35, o4_35, o8_35, o12_35, o16_35, d8_35, d12_35⟩ := Ok35 tl35 hr35
  have keep_kk35 : SvKeepL B n0.mem n35.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := keep_kk34.trans K35
  clear keep_kk34
  have w35_30 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K35.w32 (by decide) (by decide)).trans w34_30
  have w35_34 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K35.w32 (by decide) (by decide)).trans w34_34
  have w35_38 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K35.w32 (by decide) (by decide)).trans w34_38
  have w35_3c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K35.w32 (by decide) (by decide)).trans w34_3c
  have w35_40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K35.w32 (by decide) (by decide)).trans w34_40
  have w35_48 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K35.w32 (by decide) (by decide)).trans w34_48
  have w35_4c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K35.w32 (by decide) (by decide)).trans w34_4c
  have w35_50 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K35.w32 (by decide) (by decide)).trans w34_50
  have w35_54 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K35.w32 (by decide) (by decide)).trans w34_54
  have w35_58 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K35.w32 (by decide) (by decide)).trans w34_58
  have w35_5c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K35.w32 (by decide) (by decide)).trans w34_5c
  have w35_60 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K35.w32 (by decide) (by decide)).trans w34_60
  have w35_64 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K35.w32 (by decide) (by decide)).trans w34_64
  have w35_68 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K35.w32 (by decide) (by decide)).trans w34_68
  have w35_6c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K35.w32 (by decide) (by decide)).trans w34_6c
  have w35_70 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K35.w32 (by decide) (by decide)).trans w34_70
  have w35_74 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K35.w32 (by decide) (by decide)).trans w34_74
  have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K35.w32 (by decide) (by decide)).trans w34_78
  have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K35.w32 (by decide) (by decide)).trans w34_7c
  have w35_80 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K35.w32 (by decide) (by decide)).trans w34_80
  have w35_84 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K35.w32 (by decide) (by decide)).trans w34_84
  have w35_88 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K35.w32 (by decide) (by decide)).trans w34_88
  have w35_8c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K35.w32 (by decide) (by decide)).trans w34_8c
  have w35_90 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K35.w32 (by decide) (by decide)).trans w34_90
  have w35_94 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K35.w32 (by decide) (by decide)).trans w34_94
  have w35_a20 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K35.w32 (by decide) (by decide)).trans w34_a20
  have w35_a24 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K35.w32 (by decide) (by decide)).trans w34_a24
  have w35_a28 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K35.w32 (by decide) (by decide)).trans w34_a28
  have w35_a2c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K35.w32 (by decide) (by decide)).trans w34_a2c
  have w35_a30 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K35.w32 (by decide) (by decide)).trans w34_a30
  have w35_a34 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K35.w32 (by decide) (by decide)).trans w34_a34
  have w35_a38 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K35.w32 (by decide) (by decide)).trans w34_a38
  have w35_a3c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K35.w32 (by decide) (by decide)).trans w34_a3c
  have w35_a40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K35.w32 (by decide) (by decide)).trans w34_a40
  have w35_a44 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K35.w32 (by decide) (by decide)).trans w34_a44
  have w35_1480 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K35.w32 (by decide) (by decide)).trans w34_1480
  have w35_1484 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K35.w32 (by decide) (by decide)).trans w34_1484
  have w35_1020 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := o0_35
  have w35_1024 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := o4_35
  have w35_1028 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := o8_35
  have w35_102c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := o12_35
  have w35_1488 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := d8_35
  have w35_148c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := d12_35
  have b35_1030 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := o16_35
  clear w34_148c w34_1488 w34_1484 w34_1480 w34_a44 w34_a40 w34_a3c w34_a38 w34_a34 w34_a30 w34_a2c w34_a28 w34_a24 w34_a20 w34_94 w34_90 w34_8c w34_88 w34_84 w34_80 w34_7c w34_78 w34_74 w34_70 w34_6c w34_68 w34_64 w34_60 w34_5c w34_58 w34_54 w34_50 w34_4c w34_48 w34_40 w34_3c w34_38 w34_34 w34_30 g34_11 g34_10 g34_27 g34_26 g34_25 g34_23 g34_22 g34_21 g34_19 g34_18 g34_13 g34_12 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 rb34 s34 m34 u34 c34
  -- 0x8FE: lw
  obtain ⟨n36, d36, u36⟩ := s35.lw E35.self sv_at_8fe (off' := 0x902) (by decide)
    (by rw [g35_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x600 = B + 0x21A0 + BitVec.ofNat 32 0x1020 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s36 : St n36.mem SV n36 0x902 (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
  have m36 : n36.mem = n35.mem := u36.mem
  have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
  have t36 : Steps n0 n36 := t35.trans (.single d36)
  have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.same m36
  have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_4]
  have g36_8 : reg n36 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_8]
  have g36_9 : reg n36 (9 : Fin 32) = x9 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_9]
  have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, upd_ne (by decide) (by decide), g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_19]
  have g36_21 : reg n36 (21 : Fin 32) = x21 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_23]
  have g36_25 : reg n36 (25 : Fin 32) = x25 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = x26 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_27]
  have g36_10 : reg n36 a0 = (vp) + BitVec.ofNat 32 tl35.header := by
    rw [u36.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g35_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x600 = B + 0x21A0 + BitVec.ofNat 32 0x1020 by sv_addr, w35_1020]
  have keep_kk36 : SvKeepL B n0.mem n36.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := by rw [m36]; exact keep_kk35
  clear keep_kk35
  have w36_30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m36]; exact w35_30
  have w36_34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m36]; exact w35_34
  have w36_38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m36]; exact w35_38
  have w36_3c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m36]; exact w35_3c
  have w36_40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m36]; exact w35_40
  have w36_48 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m36]; exact w35_48
  have w36_4c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m36]; exact w35_4c
  have w36_50 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m36]; exact w35_50
  have w36_54 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m36]; exact w35_54
  have w36_58 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m36]; exact w35_58
  have w36_5c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m36]; exact w35_5c
  have w36_60 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m36]; exact w35_60
  have w36_64 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m36]; exact w35_64
  have w36_68 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m36]; exact w35_68
  have w36_6c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m36]; exact w35_6c
  have w36_70 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m36]; exact w35_70
  have w36_74 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m36]; exact w35_74
  have w36_78 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m36]; exact w35_78
  have w36_7c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m36]; exact w35_7c
  have w36_80 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m36]; exact w35_80
  have w36_84 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m36]; exact w35_84
  have w36_88 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m36]; exact w35_88
  have w36_8c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m36]; exact w35_8c
  have w36_90 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m36]; exact w35_90
  have w36_94 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m36]; exact w35_94
  have w36_a20 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m36]; exact w35_a20
  have w36_a24 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m36]; exact w35_a24
  have w36_a28 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m36]; exact w35_a28
  have w36_a2c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m36]; exact w35_a2c
  have w36_a30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m36]; exact w35_a30
  have w36_a34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m36]; exact w35_a34
  have w36_a38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m36]; exact w35_a38
  have w36_a3c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m36]; exact w35_a3c
  have w36_a40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m36]; exact w35_a40
  have w36_a44 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m36]; exact w35_a44
  have w36_1020 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m36]; exact w35_1020
  have w36_1024 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m36]; exact w35_1024
  have w36_1028 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m36]; exact w35_1028
  have w36_102c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m36]; exact w35_102c
  have w36_1480 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m36]; exact w35_1480
  have w36_1484 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m36]; exact w35_1484
  have w36_1488 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m36]; exact w35_1488
  have w36_148c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m36]; exact w35_148c
  have b36_1030 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m36]; exact b35_1030
  clear b35_1030 w35_148c w35_1488 w35_102c w35_1028 w35_1024 w35_1020 w35_1484 w35_1480 w35_a44 w35_a40 w35_a3c w35_a38 w35_a34 w35_a30 w35_a2c w35_a28 w35_a24 w35_a20 w35_94 w35_90 w35_8c w35_88 w35_84 w35_80 w35_7c w35_78 w35_74 w35_70 w35_6c w35_68 w35_64 w35_60 w35_5c w35_58 w35_54 w35_50 w35_4c w35_48 w35_40 w35_3c w35_38 w35_34 w35_30 d12_35 d8_35 o16_35 o12_35 o8_35 o4_35 o0_35 g35_27 g35_26 g35_25 g35_23 g35_22 g35_21 g35_19 g35_18 g35_10 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 Er35 Ok35 K35 rk35 s35 c35
  -- 0x902: branch, not taken
  obtain ⟨n37, d37, u37⟩ := s36.notTaken E36.self 0x904 sv_at_902
    (by decide) (by rw [g36_10, s36.zero]; exact br_beq_f (val_in.tlv_ne hr35))
  have s37 : St n37.mem SV n37 0x904 (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
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
  have g37_10 : reg n37 a0 = (vp) + BitVec.ofNat 32 tl35.header := by rw [u37.regs, g36_10]
  have g37_18 : reg n37 (18 : Fin 32) = out := by rw [u37.regs, g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [u37.regs, g36_19]
  have g37_21 : reg n37 (21 : Fin 32) = x21 := by rw [u37.regs, g36_21]
  have g37_22 : reg n37 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u37.regs, g36_22]
  have g37_23 : reg n37 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u37.regs, g36_23]
  have g37_25 : reg n37 (25 : Fin 32) = x25 := by rw [u37.regs, g36_25]
  have g37_26 : reg n37 (26 : Fin 32) = x26 := by rw [u37.regs, g36_26]
  have g37_27 : reg n37 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u37.regs, g36_27]
  have keep_kk37 : SvKeepL B n0.mem n37.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := by rw [m37]; exact keep_kk36
  clear keep_kk36
  have w37_30 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m37]; exact w36_30
  have w37_34 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m37]; exact w36_34
  have w37_38 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m37]; exact w36_38
  have w37_3c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m37]; exact w36_3c
  have w37_40 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m37]; exact w36_40
  have w37_48 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m37]; exact w36_48
  have w37_4c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m37]; exact w36_4c
  have w37_50 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m37]; exact w36_50
  have w37_54 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m37]; exact w36_54
  have w37_58 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m37]; exact w36_58
  have w37_5c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m37]; exact w36_5c
  have w37_60 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m37]; exact w36_60
  have w37_64 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m37]; exact w36_64
  have w37_68 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m37]; exact w36_68
  have w37_6c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m37]; exact w36_6c
  have w37_70 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m37]; exact w36_70
  have w37_74 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m37]; exact w36_74
  have w37_78 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m37]; exact w36_78
  have w37_7c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m37]; exact w36_7c
  have w37_80 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m37]; exact w36_80
  have w37_84 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m37]; exact w36_84
  have w37_88 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m37]; exact w36_88
  have w37_8c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m37]; exact w36_8c
  have w37_90 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m37]; exact w36_90
  have w37_94 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m37]; exact w36_94
  have w37_a20 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m37]; exact w36_a20
  have w37_a24 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m37]; exact w36_a24
  have w37_a28 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m37]; exact w36_a28
  have w37_a2c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m37]; exact w36_a2c
  have w37_a30 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m37]; exact w36_a30
  have w37_a34 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m37]; exact w36_a34
  have w37_a38 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m37]; exact w36_a38
  have w37_a3c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m37]; exact w36_a3c
  have w37_a40 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m37]; exact w36_a40
  have w37_a44 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m37]; exact w36_a44
  have w37_1020 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m37]; exact w36_1020
  have w37_1024 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m37]; exact w36_1024
  have w37_1028 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m37]; exact w36_1028
  have w37_102c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m37]; exact w36_102c
  have w37_1480 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m37]; exact w36_1480
  have w37_1484 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m37]; exact w36_1484
  have w37_1488 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m37]; exact w36_1488
  have w37_148c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m37]; exact w36_148c
  have b37_1030 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m37]; exact b36_1030
  clear b36_1030 w36_148c w36_1488 w36_1484 w36_1480 w36_102c w36_1028 w36_1024 w36_1020 w36_a44 w36_a40 w36_a3c w36_a38 w36_a34 w36_a30 w36_a2c w36_a28 w36_a24 w36_a20 w36_94 w36_90 w36_8c w36_88 w36_84 w36_80 w36_7c w36_78 w36_74 w36_70 w36_6c w36_68 w36_64 w36_60 w36_5c w36_58 w36_54 w36_50 w36_4c w36_48 w36_40 w36_3c w36_38 w36_34 w36_30 g36_10 g36_27 g36_26 g36_25 g36_23 g36_22 g36_21 g36_19 g36_18 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 m36 s36 u36 d36
  -- 0x904: lbu
  obtain ⟨n38, d38, u38⟩ := s37.lbu E37.self sv_at_904 (off' := 0x908) (by decide)
  have s38 : St n38.mem SV n38 0x908 (reg n38) := ⟨u38.pc, rfl, fun _ => rfl⟩
  have m38 : n38.mem = n37.mem := u38.mem
  have fr38 : ∀ x, SvR B x → n38.mem x = n37.mem x := fun x _ => by rw [m38]
  have t38 : Steps n0 n38 := t37.trans (.single d38)
  have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : SvCode n38.mem := E37.fr F fr38
  have V38 : SvSaves B n38.mem v := V37.same m38
  have g38_2 : reg n38 sp = B + 0x21A0 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_4]
  have g38_8 : reg n38 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_8]
  have g38_9 : reg n38 (9 : Fin 32) = x9 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_9]
  have g38_10 : reg n38 a0 = (vp) + BitVec.ofNat 32 tl35.header := by rw [u38.regs, upd_ne (by decide) (by decide), g37_10]
  have g38_18 : reg n38 (18 : Fin 32) = out := by rw [u38.regs, upd_ne (by decide) (by decide), g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_19]
  have g38_21 : reg n38 (21 : Fin 32) = x21 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_21]
  have g38_22 : reg n38 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_22]
  have g38_23 : reg n38 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_23]
  have g38_25 : reg n38 (25 : Fin 32) = x25 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_25]
  have g38_26 : reg n38 (26 : Fin 32) = x26 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_26]
  have g38_27 : reg n38 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_27]
  have g38_11 : reg n38 a1 = (BitVec.ofNat 8 tl35.tag).zeroExtend 32 := by
    rw [u38.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g37_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x610 = B + 0x21A0 + BitVec.ofNat 32 0x1030 by sv_addr, b37_1030]
  have keep_kk38 : SvKeepL B n0.mem n38.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := by rw [m38]; exact keep_kk37
  clear keep_kk37
  have w38_30 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m38]; exact w37_30
  have w38_34 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m38]; exact w37_34
  have w38_38 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m38]; exact w37_38
  have w38_3c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m38]; exact w37_3c
  have w38_40 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m38]; exact w37_40
  have w38_48 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m38]; exact w37_48
  have w38_4c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m38]; exact w37_4c
  have w38_50 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m38]; exact w37_50
  have w38_54 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m38]; exact w37_54
  have w38_58 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m38]; exact w37_58
  have w38_5c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m38]; exact w37_5c
  have w38_60 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m38]; exact w37_60
  have w38_64 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m38]; exact w37_64
  have w38_68 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m38]; exact w37_68
  have w38_6c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m38]; exact w37_6c
  have w38_70 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m38]; exact w37_70
  have w38_74 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m38]; exact w37_74
  have w38_78 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m38]; exact w37_78
  have w38_7c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m38]; exact w37_7c
  have w38_80 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m38]; exact w37_80
  have w38_84 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m38]; exact w37_84
  have w38_88 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m38]; exact w37_88
  have w38_8c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m38]; exact w37_8c
  have w38_90 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m38]; exact w37_90
  have w38_94 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m38]; exact w37_94
  have w38_a20 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m38]; exact w37_a20
  have w38_a24 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m38]; exact w37_a24
  have w38_a28 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m38]; exact w37_a28
  have w38_a2c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m38]; exact w37_a2c
  have w38_a30 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m38]; exact w37_a30
  have w38_a34 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m38]; exact w37_a34
  have w38_a38 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m38]; exact w37_a38
  have w38_a3c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m38]; exact w37_a3c
  have w38_a40 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m38]; exact w37_a40
  have w38_a44 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m38]; exact w37_a44
  have w38_1020 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m38]; exact w37_1020
  have w38_1024 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m38]; exact w37_1024
  have w38_1028 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m38]; exact w37_1028
  have w38_102c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m38]; exact w37_102c
  have w38_1480 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m38]; exact w37_1480
  have w38_1484 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m38]; exact w37_1484
  have w38_1488 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m38]; exact w37_1488
  have w38_148c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m38]; exact w37_148c
  have b38_1030 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m38]; exact b37_1030
  clear b37_1030 w37_148c w37_1488 w37_1484 w37_1480 w37_102c w37_1028 w37_1024 w37_1020 w37_a44 w37_a40 w37_a3c w37_a38 w37_a34 w37_a30 w37_a2c w37_a28 w37_a24 w37_a20 w37_94 w37_90 w37_8c w37_88 w37_84 w37_80 w37_7c w37_78 w37_74 w37_70 w37_6c w37_68 w37_64 w37_60 w37_5c w37_58 w37_54 w37_50 w37_4c w37_48 w37_40 w37_3c w37_38 w37_34 w37_30 g37_27 g37_26 g37_25 g37_23 g37_22 g37_21 g37_19 g37_18 g37_10 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 m37 s37 u37 d37
  -- 0x908
  obtain ⟨n39, c39, u39⟩ := s38.block svDp0908 E38.self svDp0908_end
    ⟨trivial, trivial⟩
  have m39 : n39.mem = n38.mem := u39.mem
  have s39 : St n39.mem SV n39 0x90A (reg n39) := ⟨u39.pc, rfl, fun _ => rfl⟩
  have rb39 : ∀ q, reg n39 q = (runBlock svDp0908 (n38.mem, reg n38)).2 q := fun q => by rw [u39.regs]
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
  have g39_10 : reg n39 a0 = (vp) + BitVec.ofNat 32 tl35.header := by
    rw [rb39, runBlock_reg _ _ _ a0 s38.zero (by decide), g38_10]
  have g39_11 : reg n39 a1 = (BitVec.ofNat 8 tl35.tag).zeroExtend 32 := by
    rw [rb39, runBlock_reg _ _ _ a1 s38.zero (by decide), g38_11]
  have g39_18 : reg n39 (18 : Fin 32) = out := by
    rw [rb39, runBlock_reg _ _ _ (18 : Fin 32) s38.zero (by decide), g38_18]
  have g39_19 : reg n39 (19 : Fin 32) = bp := by
    rw [rb39, runBlock_reg _ _ _ (19 : Fin 32) s38.zero (by decide), g38_19]
  have g39_21 : reg n39 (21 : Fin 32) = x21 := by
    rw [rb39, runBlock_reg _ _ _ (21 : Fin 32) s38.zero (by decide), g38_21]
  have g39_22 : reg n39 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb39, runBlock_reg _ _ _ (22 : Fin 32) s38.zero (by decide), g38_22]
  have g39_23 : reg n39 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by
    rw [rb39, runBlock_reg _ _ _ (23 : Fin 32) s38.zero (by decide), g38_23]
  have g39_25 : reg n39 (25 : Fin 32) = x25 := by
    rw [rb39, runBlock_reg _ _ _ (25 : Fin 32) s38.zero (by decide), g38_25]
  have g39_26 : reg n39 (26 : Fin 32) = x26 := by
    rw [rb39, runBlock_reg _ _ _ (26 : Fin 32) s38.zero (by decide), g38_26]
  have g39_27 : reg n39 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb39, runBlock_reg _ _ _ (27 : Fin 32) s38.zero (by decide), g38_27]
  have g39_12 : reg n39 a2 = BitVec.ofNat 32 0xC := by
    rw [rb39]; simp +decide only [runBlock, BInstr.run, svDp0908, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g38_2, g38_3, g38_4, g38_8, g38_9, g38_10, g38_11, g38_18, g38_19, g38_21, g38_22, g38_23, g38_25, g38_26, g38_27, s38.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk39 : SvKeepL B n0.mem n39.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := by rw [m39]; exact keep_kk38
  clear keep_kk38
  have w39_30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m39]; exact w38_30
  have w39_34 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m39]; exact w38_34
  have w39_38 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m39]; exact w38_38
  have w39_3c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m39]; exact w38_3c
  have w39_40 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m39]; exact w38_40
  have w39_48 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m39]; exact w38_48
  have w39_4c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m39]; exact w38_4c
  have w39_50 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m39]; exact w38_50
  have w39_54 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m39]; exact w38_54
  have w39_58 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m39]; exact w38_58
  have w39_5c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m39]; exact w38_5c
  have w39_60 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m39]; exact w38_60
  have w39_64 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m39]; exact w38_64
  have w39_68 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m39]; exact w38_68
  have w39_6c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m39]; exact w38_6c
  have w39_70 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m39]; exact w38_70
  have w39_74 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m39]; exact w38_74
  have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m39]; exact w38_78
  have w39_7c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m39]; exact w38_7c
  have w39_80 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m39]; exact w38_80
  have w39_84 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m39]; exact w38_84
  have w39_88 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m39]; exact w38_88
  have w39_8c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m39]; exact w38_8c
  have w39_90 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m39]; exact w38_90
  have w39_94 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m39]; exact w38_94
  have w39_a20 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m39]; exact w38_a20
  have w39_a24 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m39]; exact w38_a24
  have w39_a28 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m39]; exact w38_a28
  have w39_a2c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m39]; exact w38_a2c
  have w39_a30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m39]; exact w38_a30
  have w39_a34 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m39]; exact w38_a34
  have w39_a38 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m39]; exact w38_a38
  have w39_a3c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m39]; exact w38_a3c
  have w39_a40 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m39]; exact w38_a40
  have w39_a44 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m39]; exact w38_a44
  have w39_1020 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m39]; exact w38_1020
  have w39_1024 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m39]; exact w38_1024
  have w39_1028 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m39]; exact w38_1028
  have w39_102c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m39]; exact w38_102c
  have w39_1480 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m39]; exact w38_1480
  have w39_1484 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m39]; exact w38_1484
  have w39_1488 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m39]; exact w38_1488
  have w39_148c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m39]; exact w38_148c
  have b39_1030 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m39]; exact b38_1030
  clear b38_1030 w38_148c w38_1488 w38_1484 w38_1480 w38_102c w38_1028 w38_1024 w38_1020 w38_a44 w38_a40 w38_a3c w38_a38 w38_a34 w38_a30 w38_a2c w38_a28 w38_a24 w38_a20 w38_94 w38_90 w38_8c w38_88 w38_84 w38_80 w38_7c w38_78 w38_74 w38_70 w38_6c w38_68 w38_64 w38_60 w38_5c w38_58 w38_54 w38_50 w38_4c w38_48 w38_40 w38_3c w38_38 w38_34 w38_30 g38_11 g38_27 g38_26 g38_25 g38_23 g38_22 g38_21 g38_19 g38_18 g38_10 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 m38 s38 u38 d38
  by_cases hz_39 : BitVec.ofNat 8 tl35.tag = BitVec.ofNat 8 0xC
  rotate_left
  · -- 0x90A: branch, taken
    obtain ⟨n40, d40, u40⟩ := s39.taken E39.self 0xB4E sv_at_90a
      (by decide) (by rw [g39_11, g39_12]; exact br_bne_byte_t (by decide) hz_39)
    have s40 : St n40.mem SV n40 0xB4E (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
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
    have g40_10 : reg n40 a0 = (vp) + BitVec.ofNat 32 tl35.header := by rw [u40.regs, g39_10]
    have g40_11 : reg n40 a1 = (BitVec.ofNat 8 tl35.tag).zeroExtend 32 := by rw [u40.regs, g39_11]
    have g40_12 : reg n40 a2 = BitVec.ofNat 32 0xC := by rw [u40.regs, g39_12]
    have g40_18 : reg n40 (18 : Fin 32) = out := by rw [u40.regs, g39_18]
    have g40_19 : reg n40 (19 : Fin 32) = bp := by rw [u40.regs, g39_19]
    have g40_21 : reg n40 (21 : Fin 32) = x21 := by rw [u40.regs, g39_21]
    have g40_22 : reg n40 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u40.regs, g39_22]
    have g40_23 : reg n40 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u40.regs, g39_23]
    have g40_25 : reg n40 (25 : Fin 32) = x25 := by rw [u40.regs, g39_25]
    have g40_26 : reg n40 (26 : Fin 32) = x26 := by rw [u40.regs, g39_26]
    have g40_27 : reg n40 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u40.regs, g39_27]
    have keep_kk40 : SvKeepL B n0.mem n40.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := by rw [m40]; exact keep_kk39
    clear keep_kk39
    have w40_30 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m40]; exact w39_30
    have w40_34 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m40]; exact w39_34
    have w40_38 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m40]; exact w39_38
    have w40_3c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m40]; exact w39_3c
    have w40_40 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m40]; exact w39_40
    have w40_48 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m40]; exact w39_48
    have w40_4c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m40]; exact w39_4c
    have w40_50 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m40]; exact w39_50
    have w40_54 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m40]; exact w39_54
    have w40_58 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m40]; exact w39_58
    have w40_5c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m40]; exact w39_5c
    have w40_60 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m40]; exact w39_60
    have w40_64 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m40]; exact w39_64
    have w40_68 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m40]; exact w39_68
    have w40_6c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m40]; exact w39_6c
    have w40_70 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m40]; exact w39_70
    have w40_74 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m40]; exact w39_74
    have w40_78 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m40]; exact w39_78
    have w40_7c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m40]; exact w39_7c
    have w40_80 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m40]; exact w39_80
    have w40_84 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m40]; exact w39_84
    have w40_88 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m40]; exact w39_88
    have w40_8c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m40]; exact w39_8c
    have w40_90 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m40]; exact w39_90
    have w40_94 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m40]; exact w39_94
    have w40_a20 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m40]; exact w39_a20
    have w40_a24 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m40]; exact w39_a24
    have w40_a28 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m40]; exact w39_a28
    have w40_a2c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m40]; exact w39_a2c
    have w40_a30 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m40]; exact w39_a30
    have w40_a34 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m40]; exact w39_a34
    have w40_a38 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m40]; exact w39_a38
    have w40_a3c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m40]; exact w39_a3c
    have w40_a40 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m40]; exact w39_a40
    have w40_a44 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m40]; exact w39_a44
    have w40_1020 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m40]; exact w39_1020
    have w40_1024 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m40]; exact w39_1024
    have w40_1028 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m40]; exact w39_1028
    have w40_102c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m40]; exact w39_102c
    have w40_1480 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m40]; exact w39_1480
    have w40_1484 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m40]; exact w39_1484
    have w40_1488 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m40]; exact w39_1488
    have w40_148c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m40]; exact w39_148c
    have b40_1030 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m40]; exact b39_1030
    clear b39_1030 w39_148c w39_1488 w39_1484 w39_1480 w39_102c w39_1028 w39_1024 w39_1020 w39_a44 w39_a40 w39_a3c w39_a38 w39_a34 w39_a30 w39_a2c w39_a28 w39_a24 w39_a20 w39_94 w39_90 w39_8c w39_88 w39_84 w39_80 w39_7c w39_78 w39_74 w39_70 w39_6c w39_68 w39_64 w39_60 w39_5c w39_58 w39_54 w39_50 w39_4c w39_48 w39_40 w39_3c w39_38 w39_34 w39_30 g39_12 g39_27 g39_26 g39_25 g39_23 g39_22 g39_21 g39_19 g39_18 g39_11 g39_10 g39_9 g39_8 g39_4 g39_3 g39_2 V39 E39 fR39 t39 fr39 rb39 s39 m39 u39 c39
    -- 0xB4E
    obtain ⟨n41, c41, u41⟩ := s40.block svDp0b4e E40.self svDp0b4e_end
      ⟨trivial, trivial⟩
    have m41 : n41.mem = n40.mem := u41.mem
    have s41 : St n41.mem SV n41 0xB50 (reg n41) := ⟨u41.pc, rfl, fun _ => rfl⟩
    have rb41 : ∀ q, reg n41 q = (runBlock svDp0b4e (n40.mem, reg n40)).2 q := fun q => by rw [u41.regs]
    have fr41 : ∀ x, SvR B x → n41.mem x = n40.mem x := fun x _ => by rw [m41]
    have t41 : Steps n0 n41 := t40.trans c41
    have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
    have E41 : SvCode n41.mem := E40.fr F fr41
    have V41 : SvSaves B n41.mem v := V40.same m41
    have g41_2 : reg n41 sp = B + 0x21A0 := by
      rw [rb41, runBlock_reg _ _ _ sp s40.zero (by decide), g40_2]
    have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb41, runBlock_reg _ _ _ (3 : Fin 32) s40.zero (by decide), g40_3]
    have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb41, runBlock_reg _ _ _ (4 : Fin 32) s40.zero (by decide), g40_4]
    have g41_8 : reg n41 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
      rw [rb41, runBlock_reg _ _ _ (8 : Fin 32) s40.zero (by decide), g40_8]
    have g41_9 : reg n41 (9 : Fin 32) = x9 := by
      rw [rb41, runBlock_reg _ _ _ (9 : Fin 32) s40.zero (by decide), g40_9]
    have g41_11 : reg n41 a1 = (BitVec.ofNat 8 tl35.tag).zeroExtend 32 := by
      rw [rb41, runBlock_reg _ _ _ a1 s40.zero (by decide), g40_11]
    have g41_12 : reg n41 a2 = BitVec.ofNat 32 0xC := by
      rw [rb41, runBlock_reg _ _ _ a2 s40.zero (by decide), g40_12]
    have g41_18 : reg n41 (18 : Fin 32) = out := by
      rw [rb41, runBlock_reg _ _ _ (18 : Fin 32) s40.zero (by decide), g40_18]
    have g41_19 : reg n41 (19 : Fin 32) = bp := by
      rw [rb41, runBlock_reg _ _ _ (19 : Fin 32) s40.zero (by decide), g40_19]
    have g41_21 : reg n41 (21 : Fin 32) = x21 := by
      rw [rb41, runBlock_reg _ _ _ (21 : Fin 32) s40.zero (by decide), g40_21]
    have g41_22 : reg n41 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [rb41, runBlock_reg _ _ _ (22 : Fin 32) s40.zero (by decide), g40_22]
    have g41_23 : reg n41 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by
      rw [rb41, runBlock_reg _ _ _ (23 : Fin 32) s40.zero (by decide), g40_23]
    have g41_25 : reg n41 (25 : Fin 32) = x25 := by
      rw [rb41, runBlock_reg _ _ _ (25 : Fin 32) s40.zero (by decide), g40_25]
    have g41_26 : reg n41 (26 : Fin 32) = x26 := by
      rw [rb41, runBlock_reg _ _ _ (26 : Fin 32) s40.zero (by decide), g40_26]
    have g41_27 : reg n41 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb41, runBlock_reg _ _ _ (27 : Fin 32) s40.zero (by decide), g40_27]
    have g41_10 : reg n41 a0 = BitVec.ofNat 32 0x16 := by
      rw [rb41]; simp +decide only [runBlock, BInstr.run, svDp0b4e, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g40_2, g40_3, g40_4, g40_8, g40_9, g40_10, g40_11, g40_12, g40_18, g40_19, g40_21, g40_22, g40_23, g40_25, g40_26, g40_27, s40.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := by rw [m41]; exact keep_kk40
    clear keep_kk40
    have w41_30 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m41]; exact w40_30
    have w41_34 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m41]; exact w40_34
    have w41_38 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m41]; exact w40_38
    have w41_3c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m41]; exact w40_3c
    have w41_40 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m41]; exact w40_40
    have w41_48 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m41]; exact w40_48
    have w41_4c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m41]; exact w40_4c
    have w41_50 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m41]; exact w40_50
    have w41_54 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m41]; exact w40_54
    have w41_58 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m41]; exact w40_58
    have w41_5c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m41]; exact w40_5c
    have w41_60 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m41]; exact w40_60
    have w41_64 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m41]; exact w40_64
    have w41_68 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m41]; exact w40_68
    have w41_6c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m41]; exact w40_6c
    have w41_70 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m41]; exact w40_70
    have w41_74 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m41]; exact w40_74
    have w41_78 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m41]; exact w40_78
    have w41_7c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m41]; exact w40_7c
    have w41_80 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m41]; exact w40_80
    have w41_84 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m41]; exact w40_84
    have w41_88 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m41]; exact w40_88
    have w41_8c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m41]; exact w40_8c
    have w41_90 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m41]; exact w40_90
    have w41_94 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m41]; exact w40_94
    have w41_a20 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m41]; exact w40_a20
    have w41_a24 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m41]; exact w40_a24
    have w41_a28 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m41]; exact w40_a28
    have w41_a2c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m41]; exact w40_a2c
    have w41_a30 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m41]; exact w40_a30
    have w41_a34 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m41]; exact w40_a34
    have w41_a38 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m41]; exact w40_a38
    have w41_a3c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m41]; exact w40_a3c
    have w41_a40 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m41]; exact w40_a40
    have w41_a44 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m41]; exact w40_a44
    have w41_1020 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m41]; exact w40_1020
    have w41_1024 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m41]; exact w40_1024
    have w41_1028 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m41]; exact w40_1028
    have w41_102c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m41]; exact w40_102c
    have w41_1480 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m41]; exact w40_1480
    have w41_1484 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m41]; exact w40_1484
    have w41_1488 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m41]; exact w40_1488
    have w41_148c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m41]; exact w40_148c
    have b41_1030 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m41]; exact b40_1030
    clear b40_1030 w40_148c w40_1488 w40_1484 w40_1480 w40_102c w40_1028 w40_1024 w40_1020 w40_a44 w40_a40 w40_a3c w40_a38 w40_a34 w40_a30 w40_a2c w40_a28 w40_a24 w40_a20 w40_94 w40_90 w40_8c w40_88 w40_84 w40_80 w40_7c w40_78 w40_74 w40_70 w40_6c w40_68 w40_64 w40_60 w40_5c w40_58 w40_54 w40_50 w40_4c w40_48 w40_40 w40_3c w40_38 w40_34 w40_30 g40_27 g40_26 g40_25 g40_23 g40_22 g40_21 g40_19 g40_18 g40_12 g40_11 g40_10 g40_9 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 m40 s40 u40 d40
    -- 0xB50: j
    obtain ⟨n42, d42, u42⟩ := s41.jump E41.self sv_at_b50 (off' := 0xB38) (by decide)
      (by rw [s41.pc]; decide)
    have s42 : St n42.mem SV n42 0xB38 (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
    have m42 : n42.mem = n41.mem := u42.mem
    have fr42 : ∀ x, SvR B x → n42.mem x = n41.mem x := fun x _ => by rw [m42]
    have t42 : Steps n0 n42 := t41.trans (.single d42)
    have fR42 : ∀ x, SvR B x → n42.mem x = M0 x := fun x hx => (fr42 x hx).trans (fR41 x hx)
    have E42 : SvCode n42.mem := E41.fr F fr42
    have V42 : SvSaves B n42.mem v := V41.same m42
    have g42_2 : reg n42 sp = B + 0x21A0 := by rw [u42.regs, g41_2]
    have g42_3 : reg n42 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u42.regs, g41_3]
    have g42_4 : reg n42 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u42.regs, g41_4]
    have g42_8 : reg n42 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u42.regs, g41_8]
    have g42_9 : reg n42 (9 : Fin 32) = x9 := by rw [u42.regs, g41_9]
    have g42_10 : reg n42 a0 = BitVec.ofNat 32 0x16 := by rw [u42.regs, g41_10]
    have g42_11 : reg n42 a1 = (BitVec.ofNat 8 tl35.tag).zeroExtend 32 := by rw [u42.regs, g41_11]
    have g42_12 : reg n42 a2 = BitVec.ofNat 32 0xC := by rw [u42.regs, g41_12]
    have g42_18 : reg n42 (18 : Fin 32) = out := by rw [u42.regs, g41_18]
    have g42_19 : reg n42 (19 : Fin 32) = bp := by rw [u42.regs, g41_19]
    have g42_21 : reg n42 (21 : Fin 32) = x21 := by rw [u42.regs, g41_21]
    have g42_22 : reg n42 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u42.regs, g41_22]
    have g42_23 : reg n42 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u42.regs, g41_23]
    have g42_25 : reg n42 (25 : Fin 32) = x25 := by rw [u42.regs, g41_25]
    have g42_26 : reg n42 (26 : Fin 32) = x26 := by rw [u42.regs, g41_26]
    have g42_27 : reg n42 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u42.regs, g41_27]
    have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := by rw [m42]; exact keep_kk41
    clear keep_kk41
    have w42_30 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m42]; exact w41_30
    have w42_34 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m42]; exact w41_34
    have w42_38 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m42]; exact w41_38
    have w42_3c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m42]; exact w41_3c
    have w42_40 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m42]; exact w41_40
    have w42_48 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m42]; exact w41_48
    have w42_4c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m42]; exact w41_4c
    have w42_50 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m42]; exact w41_50
    have w42_54 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m42]; exact w41_54
    have w42_58 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m42]; exact w41_58
    have w42_5c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m42]; exact w41_5c
    have w42_60 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m42]; exact w41_60
    have w42_64 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m42]; exact w41_64
    have w42_68 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m42]; exact w41_68
    have w42_6c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m42]; exact w41_6c
    have w42_70 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m42]; exact w41_70
    have w42_74 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m42]; exact w41_74
    have w42_78 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m42]; exact w41_78
    have w42_7c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m42]; exact w41_7c
    have w42_80 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m42]; exact w41_80
    have w42_84 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m42]; exact w41_84
    have w42_88 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m42]; exact w41_88
    have w42_8c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m42]; exact w41_8c
    have w42_90 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m42]; exact w41_90
    have w42_94 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m42]; exact w41_94
    have w42_a20 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m42]; exact w41_a20
    have w42_a24 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m42]; exact w41_a24
    have w42_a28 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m42]; exact w41_a28
    have w42_a2c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m42]; exact w41_a2c
    have w42_a30 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m42]; exact w41_a30
    have w42_a34 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m42]; exact w41_a34
    have w42_a38 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m42]; exact w41_a38
    have w42_a3c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m42]; exact w41_a3c
    have w42_a40 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m42]; exact w41_a40
    have w42_a44 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m42]; exact w41_a44
    have w42_1020 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m42]; exact w41_1020
    have w42_1024 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m42]; exact w41_1024
    have w42_1028 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m42]; exact w41_1028
    have w42_102c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m42]; exact w41_102c
    have w42_1480 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m42]; exact w41_1480
    have w42_1484 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m42]; exact w41_1484
    have w42_1488 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m42]; exact w41_1488
    have w42_148c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m42]; exact w41_148c
    have b42_1030 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m42]; exact b41_1030
    clear b41_1030 w41_148c w41_1488 w41_1484 w41_1480 w41_102c w41_1028 w41_1024 w41_1020 w41_a44 w41_a40 w41_a3c w41_a38 w41_a34 w41_a30 w41_a2c w41_a28 w41_a24 w41_a20 w41_94 w41_90 w41_8c w41_88 w41_84 w41_80 w41_7c w41_78 w41_74 w41_70 w41_6c w41_68 w41_64 w41_60 w41_5c w41_58 w41_54 w41_50 w41_4c w41_48 w41_40 w41_3c w41_38 w41_34 w41_30 g41_10 g41_27 g41_26 g41_25 g41_23 g41_22 g41_21 g41_19 g41_18 g41_12 g41_11 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 fr41 rb41 s41 m41 u41 c41
    -- 0xB38: sw
    obtain ⟨n43, d43, s43, fr43, K43, W43, rg43⟩ := sv_sw F E42 s42 sv_at_b38 (off' := 0xB3A) (c := 0x44)
      (by decide) (by rw [g42_2]; sv_addr) (by decide) (by decide)
    have t43 : Steps n0 n43 := t42.trans d43
    have fR43 : ∀ x, SvR B x → n43.mem x = M0 x := fun x hx => (fr43 x hx).trans (fR42 x hx)
    have E43 : SvCode n43.mem := E42.fr F fr43
    have V43 : SvSaves B n43.mem v := V42.keep K43 (by decide)
    have g43_2 : reg n43 sp = B + 0x21A0 := by rw [rg43 sp, g42_2]
    have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg43 (3 : Fin 32), g42_3]
    have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg43 (4 : Fin 32), g42_4]
    have g43_8 : reg n43 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg43 (8 : Fin 32), g42_8]
    have g43_9 : reg n43 (9 : Fin 32) = x9 := by rw [rg43 (9 : Fin 32), g42_9]
    have g43_10 : reg n43 a0 = BitVec.ofNat 32 0x16 := by rw [rg43 a0, g42_10]
    have g43_11 : reg n43 a1 = (BitVec.ofNat 8 tl35.tag).zeroExtend 32 := by rw [rg43 a1, g42_11]
    have g43_12 : reg n43 a2 = BitVec.ofNat 32 0xC := by rw [rg43 a2, g42_12]
    have g43_18 : reg n43 (18 : Fin 32) = out := by rw [rg43 (18 : Fin 32), g42_18]
    have g43_19 : reg n43 (19 : Fin 32) = bp := by rw [rg43 (19 : Fin 32), g42_19]
    have g43_21 : reg n43 (21 : Fin 32) = x21 := by rw [rg43 (21 : Fin 32), g42_21]
    have g43_22 : reg n43 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg43 (22 : Fin 32), g42_22]
    have g43_23 : reg n43 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [rg43 (23 : Fin 32), g42_23]
    have g43_25 : reg n43 (25 : Fin 32) = x25 := by rw [rg43 (25 : Fin 32), g42_25]
    have g43_26 : reg n43 (26 : Fin 32) = x26 := by rw [rg43 (26 : Fin 32), g42_26]
    have g43_27 : reg n43 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg43 (27 : Fin 32), g42_27]
    have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0x44, 0x4)] := keep_kk42.trans K43.toL
    clear keep_kk42
    have w43_30 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K43.w32 (by decide) (by decide)).trans w42_30
    have w43_34 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K43.w32 (by decide) (by decide)).trans w42_34
    have w43_38 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K43.w32 (by decide) (by decide)).trans w42_38
    have w43_3c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K43.w32 (by decide) (by decide)).trans w42_3c
    have w43_40 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K43.w32 (by decide) (by decide)).trans w42_40
    have w43_48 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K43.w32 (by decide) (by decide)).trans w42_48
    have w43_4c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K43.w32 (by decide) (by decide)).trans w42_4c
    have w43_50 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K43.w32 (by decide) (by decide)).trans w42_50
    have w43_54 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K43.w32 (by decide) (by decide)).trans w42_54
    have w43_58 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K43.w32 (by decide) (by decide)).trans w42_58
    have w43_5c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K43.w32 (by decide) (by decide)).trans w42_5c
    have w43_60 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K43.w32 (by decide) (by decide)).trans w42_60
    have w43_64 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K43.w32 (by decide) (by decide)).trans w42_64
    have w43_68 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K43.w32 (by decide) (by decide)).trans w42_68
    have w43_6c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K43.w32 (by decide) (by decide)).trans w42_6c
    have w43_70 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K43.w32 (by decide) (by decide)).trans w42_70
    have w43_74 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K43.w32 (by decide) (by decide)).trans w42_74
    have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K43.w32 (by decide) (by decide)).trans w42_78
    have w43_7c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K43.w32 (by decide) (by decide)).trans w42_7c
    have w43_80 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K43.w32 (by decide) (by decide)).trans w42_80
    have w43_84 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K43.w32 (by decide) (by decide)).trans w42_84
    have w43_88 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K43.w32 (by decide) (by decide)).trans w42_88
    have w43_8c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K43.w32 (by decide) (by decide)).trans w42_8c
    have w43_90 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K43.w32 (by decide) (by decide)).trans w42_90
    have w43_94 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K43.w32 (by decide) (by decide)).trans w42_94
    have w43_a20 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K43.w32 (by decide) (by decide)).trans w42_a20
    have w43_a24 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K43.w32 (by decide) (by decide)).trans w42_a24
    have w43_a28 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K43.w32 (by decide) (by decide)).trans w42_a28
    have w43_a2c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K43.w32 (by decide) (by decide)).trans w42_a2c
    have w43_a30 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K43.w32 (by decide) (by decide)).trans w42_a30
    have w43_a34 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K43.w32 (by decide) (by decide)).trans w42_a34
    have w43_a38 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K43.w32 (by decide) (by decide)).trans w42_a38
    have w43_a3c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K43.w32 (by decide) (by decide)).trans w42_a3c
    have w43_a40 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K43.w32 (by decide) (by decide)).trans w42_a40
    have w43_a44 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K43.w32 (by decide) (by decide)).trans w42_a44
    have w43_1020 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := (K43.w32 (by decide) (by decide)).trans w42_1020
    have w43_1024 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := (K43.w32 (by decide) (by decide)).trans w42_1024
    have w43_1028 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := (K43.w32 (by decide) (by decide)).trans w42_1028
    have w43_102c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := (K43.w32 (by decide) (by decide)).trans w42_102c
    have w43_1480 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K43.w32 (by decide) (by decide)).trans w42_1480
    have w43_1484 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K43.w32 (by decide) (by decide)).trans w42_1484
    have w43_1488 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := (K43.w32 (by decide) (by decide)).trans w42_1488
    have w43_148c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := (K43.w32 (by decide) (by decide)).trans w42_148c
    have b43_1030 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := (K43.b8 (by decide) (by decide)).trans b42_1030
    have w43_44 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [W43, g42_10]
    clear b42_1030 w42_148c w42_1488 w42_1484 w42_1480 w42_102c w42_1028 w42_1024 w42_1020 w42_a44 w42_a40 w42_a3c w42_a38 w42_a34 w42_a30 w42_a2c w42_a28 w42_a24 w42_a20 w42_94 w42_90 w42_8c w42_88 w42_84 w42_80 w42_7c w42_78 w42_74 w42_70 w42_6c w42_68 w42_64 w42_60 w42_5c w42_58 w42_54 w42_50 w42_4c w42_48 w42_40 w42_3c w42_38 w42_34 w42_30 g42_27 g42_26 g42_25 g42_23 g42_22 g42_21 g42_19 g42_18 g42_12 g42_11 g42_10 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 m42 s42 u42 d42
    -- 0xB3A: j
    obtain ⟨n44, d44, u44⟩ := s43.jump E43.self sv_at_b3a (off' := 0xB46) (by decide)
      (by rw [s43.pc]; decide)
    have s44 : St n44.mem SV n44 0xB46 (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
    have m44 : n44.mem = n43.mem := u44.mem
    have fr44 : ∀ x, SvR B x → n44.mem x = n43.mem x := fun x _ => by rw [m44]
    have t44 : Steps n0 n44 := t43.trans (.single d44)
    have fR44 : ∀ x, SvR B x → n44.mem x = M0 x := fun x hx => (fr44 x hx).trans (fR43 x hx)
    have E44 : SvCode n44.mem := E43.fr F fr44
    have V44 : SvSaves B n44.mem v := V43.same m44
    have g44_2 : reg n44 sp = B + 0x21A0 := by rw [u44.regs, g43_2]
    have g44_3 : reg n44 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u44.regs, g43_3]
    have g44_4 : reg n44 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u44.regs, g43_4]
    have g44_8 : reg n44 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u44.regs, g43_8]
    have g44_9 : reg n44 (9 : Fin 32) = x9 := by rw [u44.regs, g43_9]
    have g44_10 : reg n44 a0 = BitVec.ofNat 32 0x16 := by rw [u44.regs, g43_10]
    have g44_11 : reg n44 a1 = (BitVec.ofNat 8 tl35.tag).zeroExtend 32 := by rw [u44.regs, g43_11]
    have g44_12 : reg n44 a2 = BitVec.ofNat 32 0xC := by rw [u44.regs, g43_12]
    have g44_18 : reg n44 (18 : Fin 32) = out := by rw [u44.regs, g43_18]
    have g44_19 : reg n44 (19 : Fin 32) = bp := by rw [u44.regs, g43_19]
    have g44_21 : reg n44 (21 : Fin 32) = x21 := by rw [u44.regs, g43_21]
    have g44_22 : reg n44 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u44.regs, g43_22]
    have g44_23 : reg n44 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u44.regs, g43_23]
    have g44_25 : reg n44 (25 : Fin 32) = x25 := by rw [u44.regs, g43_25]
    have g44_26 : reg n44 (26 : Fin 32) = x26 := by rw [u44.regs, g43_26]
    have g44_27 : reg n44 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u44.regs, g43_27]
    have keep_kk44 : SvKeepL B n0.mem n44.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0x44, 0x4)] := by rw [m44]; exact keep_kk43
    clear keep_kk43
    have w44_30 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m44]; exact w43_30
    have w44_34 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m44]; exact w43_34
    have w44_38 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m44]; exact w43_38
    have w44_3c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m44]; exact w43_3c
    have w44_40 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m44]; exact w43_40
    have w44_44 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m44]; exact w43_44
    have w44_48 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m44]; exact w43_48
    have w44_4c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m44]; exact w43_4c
    have w44_50 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m44]; exact w43_50
    have w44_54 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m44]; exact w43_54
    have w44_58 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m44]; exact w43_58
    have w44_5c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m44]; exact w43_5c
    have w44_60 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m44]; exact w43_60
    have w44_64 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m44]; exact w43_64
    have w44_68 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m44]; exact w43_68
    have w44_6c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m44]; exact w43_6c
    have w44_70 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m44]; exact w43_70
    have w44_74 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m44]; exact w43_74
    have w44_78 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m44]; exact w43_78
    have w44_7c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m44]; exact w43_7c
    have w44_80 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m44]; exact w43_80
    have w44_84 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m44]; exact w43_84
    have w44_88 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m44]; exact w43_88
    have w44_8c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m44]; exact w43_8c
    have w44_90 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m44]; exact w43_90
    have w44_94 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m44]; exact w43_94
    have w44_a20 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m44]; exact w43_a20
    have w44_a24 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m44]; exact w43_a24
    have w44_a28 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m44]; exact w43_a28
    have w44_a2c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m44]; exact w43_a2c
    have w44_a30 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m44]; exact w43_a30
    have w44_a34 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m44]; exact w43_a34
    have w44_a38 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m44]; exact w43_a38
    have w44_a3c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m44]; exact w43_a3c
    have w44_a40 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m44]; exact w43_a40
    have w44_a44 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m44]; exact w43_a44
    have w44_1020 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m44]; exact w43_1020
    have w44_1024 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m44]; exact w43_1024
    have w44_1028 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m44]; exact w43_1028
    have w44_102c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m44]; exact w43_102c
    have w44_1480 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m44]; exact w43_1480
    have w44_1484 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m44]; exact w43_1484
    have w44_1488 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m44]; exact w43_1488
    have w44_148c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m44]; exact w43_148c
    have b44_1030 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m44]; exact b43_1030
    clear w43_44 b43_1030 w43_148c w43_1488 w43_1484 w43_1480 w43_102c w43_1028 w43_1024 w43_1020 w43_a44 w43_a40 w43_a3c w43_a38 w43_a34 w43_a30 w43_a2c w43_a28 w43_a24 w43_a20 w43_94 w43_90 w43_8c w43_88 w43_84 w43_80 w43_7c w43_78 w43_74 w43_70 w43_6c w43_68 w43_64 w43_60 w43_5c w43_58 w43_54 w43_50 w43_4c w43_48 w43_40 w43_3c w43_38 w43_34 w43_30 g43_27 g43_26 g43_25 g43_23 g43_22 g43_21 g43_19 g43_18 g43_12 g43_11 g43_10 g43_9 g43_8 g43_4 g43_3 g43_2 V43 E43 fR43 t43 rg43 W43 K43 fr43 s43 d43
    -- 0xB46: lw
    obtain ⟨n45, d45, u45⟩ := s44.lw E44.self sv_at_b46 (off' := 0xB48) (by decide)
      (by rw [g44_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s45 : St n45.mem SV n45 0xB48 (reg n45) := ⟨u45.pc, rfl, fun _ => rfl⟩
    have m45 : n45.mem = n44.mem := u45.mem
    have fr45 : ∀ x, SvR B x → n45.mem x = n44.mem x := fun x _ => by rw [m45]
    have t45 : Steps n0 n45 := t44.trans (.single d45)
    have fR45 : ∀ x, SvR B x → n45.mem x = M0 x := fun x hx => (fr45 x hx).trans (fR44 x hx)
    have E45 : SvCode n45.mem := E44.fr F fr45
    have V45 : SvSaves B n45.mem v := V44.same m45
    have g45_2 : reg n45 sp = B + 0x21A0 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_2]
    have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u45.regs, upd_ne (by decide) (by decide), g44_3]
    have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u45.regs, upd_ne (by decide) (by decide), g44_4]
    have g45_8 : reg n45 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_8]
    have g45_9 : reg n45 (9 : Fin 32) = x9 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_9]
    have g45_10 : reg n45 a0 = BitVec.ofNat 32 0x16 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_10]
    have g45_11 : reg n45 a1 = (BitVec.ofNat 8 tl35.tag).zeroExtend 32 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_11]
    have g45_12 : reg n45 a2 = BitVec.ofNat 32 0xC := by rw [u45.regs, upd_ne (by decide) (by decide), g44_12]
    have g45_18 : reg n45 (18 : Fin 32) = out := by rw [u45.regs, upd_ne (by decide) (by decide), g44_18]
    have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [u45.regs, upd_ne (by decide) (by decide), g44_19]
    have g45_21 : reg n45 (21 : Fin 32) = x21 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_21]
    have g45_22 : reg n45 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_22]
    have g45_23 : reg n45 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_23]
    have g45_25 : reg n45 (25 : Fin 32) = x25 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_25]
    have g45_26 : reg n45 (26 : Fin 32) = x26 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_26]
    have g45_27 : reg n45 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_27]
    have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0x44, 0x4)] := by rw [m45]; exact keep_kk44
    clear keep_kk44
    have w45_30 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m45]; exact w44_30
    have w45_34 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m45]; exact w44_34
    have w45_38 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m45]; exact w44_38
    have w45_3c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m45]; exact w44_3c
    have w45_40 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m45]; exact w44_40
    have w45_44 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m45]; exact w44_44
    have w45_48 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m45]; exact w44_48
    have w45_4c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m45]; exact w44_4c
    have w45_50 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m45]; exact w44_50
    have w45_54 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m45]; exact w44_54
    have w45_58 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m45]; exact w44_58
    have w45_5c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m45]; exact w44_5c
    have w45_60 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m45]; exact w44_60
    have w45_64 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m45]; exact w44_64
    have w45_68 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m45]; exact w44_68
    have w45_6c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m45]; exact w44_6c
    have w45_70 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m45]; exact w44_70
    have w45_74 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m45]; exact w44_74
    have w45_78 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m45]; exact w44_78
    have w45_7c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m45]; exact w44_7c
    have w45_80 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m45]; exact w44_80
    have w45_84 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m45]; exact w44_84
    have w45_88 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m45]; exact w44_88
    have w45_8c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m45]; exact w44_8c
    have w45_90 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m45]; exact w44_90
    have w45_94 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m45]; exact w44_94
    have w45_a20 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m45]; exact w44_a20
    have w45_a24 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m45]; exact w44_a24
    have w45_a28 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m45]; exact w44_a28
    have w45_a2c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m45]; exact w44_a2c
    have w45_a30 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m45]; exact w44_a30
    have w45_a34 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m45]; exact w44_a34
    have w45_a38 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m45]; exact w44_a38
    have w45_a3c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m45]; exact w44_a3c
    have w45_a40 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m45]; exact w44_a40
    have w45_a44 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m45]; exact w44_a44
    have w45_1020 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m45]; exact w44_1020
    have w45_1024 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m45]; exact w44_1024
    have w45_1028 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m45]; exact w44_1028
    have w45_102c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m45]; exact w44_102c
    have w45_1480 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m45]; exact w44_1480
    have w45_1484 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m45]; exact w44_1484
    have w45_1488 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m45]; exact w44_1488
    have w45_148c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m45]; exact w44_148c
    have b45_1030 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m45]; exact b44_1030
    clear b44_1030 w44_148c w44_1488 w44_1484 w44_1480 w44_102c w44_1028 w44_1024 w44_1020 w44_a44 w44_a40 w44_a3c w44_a38 w44_a34 w44_a30 w44_a2c w44_a28 w44_a24 w44_a20 w44_94 w44_90 w44_8c w44_88 w44_84 w44_80 w44_7c w44_78 w44_74 w44_70 w44_6c w44_68 w44_64 w44_60 w44_5c w44_58 w44_54 w44_50 w44_4c w44_48 w44_44 w44_40 w44_3c w44_38 w44_34 w44_30 g44_27 g44_26 g44_25 g44_23 g44_22 g44_21 g44_19 g44_18 g44_12 g44_11 g44_10 g44_9 g44_8 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 m44 s44 u44 d44
    -- 0xB48: j
    obtain ⟨n46, d46, u46⟩ := s45.jump E45.self sv_at_b48 (off' := 0x966) (by decide)
      (by rw [s45.pc]; decide)
    have s46 : St n46.mem SV n46 0x966 (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
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
    have g46_10 : reg n46 a0 = BitVec.ofNat 32 0x16 := by rw [u46.regs, g45_10]
    have g46_11 : reg n46 a1 = (BitVec.ofNat 8 tl35.tag).zeroExtend 32 := by rw [u46.regs, g45_11]
    have g46_12 : reg n46 a2 = BitVec.ofNat 32 0xC := by rw [u46.regs, g45_12]
    have g46_18 : reg n46 (18 : Fin 32) = out := by rw [u46.regs, g45_18]
    have g46_19 : reg n46 (19 : Fin 32) = bp := by rw [u46.regs, g45_19]
    have g46_21 : reg n46 (21 : Fin 32) = x21 := by rw [u46.regs, g45_21]
    have g46_22 : reg n46 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u46.regs, g45_22]
    have g46_23 : reg n46 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u46.regs, g45_23]
    have g46_25 : reg n46 (25 : Fin 32) = x25 := by rw [u46.regs, g45_25]
    have g46_26 : reg n46 (26 : Fin 32) = x26 := by rw [u46.regs, g45_26]
    have g46_27 : reg n46 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u46.regs, g45_27]
    have keep_kk46 : SvKeepL B n0.mem n46.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0x44, 0x4)] := by rw [m46]; exact keep_kk45
    clear keep_kk45
    have w46_30 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m46]; exact w45_30
    have w46_34 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m46]; exact w45_34
    have w46_38 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m46]; exact w45_38
    have w46_3c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m46]; exact w45_3c
    have w46_40 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m46]; exact w45_40
    have w46_44 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m46]; exact w45_44
    have w46_48 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m46]; exact w45_48
    have w46_4c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m46]; exact w45_4c
    have w46_50 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m46]; exact w45_50
    have w46_54 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m46]; exact w45_54
    have w46_58 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m46]; exact w45_58
    have w46_5c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m46]; exact w45_5c
    have w46_60 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m46]; exact w45_60
    have w46_64 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m46]; exact w45_64
    have w46_68 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m46]; exact w45_68
    have w46_6c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m46]; exact w45_6c
    have w46_70 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m46]; exact w45_70
    have w46_74 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m46]; exact w45_74
    have w46_78 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m46]; exact w45_78
    have w46_7c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m46]; exact w45_7c
    have w46_80 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m46]; exact w45_80
    have w46_84 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m46]; exact w45_84
    have w46_88 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m46]; exact w45_88
    have w46_8c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m46]; exact w45_8c
    have w46_90 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m46]; exact w45_90
    have w46_94 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m46]; exact w45_94
    have w46_a20 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m46]; exact w45_a20
    have w46_a24 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m46]; exact w45_a24
    have w46_a28 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m46]; exact w45_a28
    have w46_a2c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m46]; exact w45_a2c
    have w46_a30 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m46]; exact w45_a30
    have w46_a34 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m46]; exact w45_a34
    have w46_a38 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m46]; exact w45_a38
    have w46_a3c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m46]; exact w45_a3c
    have w46_a40 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m46]; exact w45_a40
    have w46_a44 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m46]; exact w45_a44
    have w46_1020 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m46]; exact w45_1020
    have w46_1024 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m46]; exact w45_1024
    have w46_1028 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m46]; exact w45_1028
    have w46_102c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m46]; exact w45_102c
    have w46_1480 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m46]; exact w45_1480
    have w46_1484 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m46]; exact w45_1484
    have w46_1488 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m46]; exact w45_1488
    have w46_148c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m46]; exact w45_148c
    have b46_1030 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m46]; exact b45_1030
    clear b45_1030 w45_148c w45_1488 w45_1484 w45_1480 w45_102c w45_1028 w45_1024 w45_1020 w45_a44 w45_a40 w45_a3c w45_a38 w45_a34 w45_a30 w45_a2c w45_a28 w45_a24 w45_a20 w45_94 w45_90 w45_8c w45_88 w45_84 w45_80 w45_7c w45_78 w45_74 w45_70 w45_6c w45_68 w45_64 w45_60 w45_5c w45_58 w45_54 w45_50 w45_4c w45_48 w45_44 w45_40 w45_3c w45_38 w45_34 w45_30 g45_27 g45_26 g45_25 g45_23 g45_22 g45_21 g45_19 g45_18 g45_12 g45_11 g45_10 g45_9 g45_8 g45_4 g45_3 g45_2 V45 E45 fR45 t45 fr45 m45 s45 u45 d45
    exact .inl ⟨(fun ⟨tl35', h0', h1', _⟩ => by rw [hr35] at h0'; cases h0'; exact hz_39 h1'), sv_fail F E46 s46 t46 (fun x hx => (fR46 x hx).trans (fM x hx).symm) V46 hret g46_2 g46_18 hO g46_3 g46_4⟩
  -- 0x90A: branch, not taken
  obtain ⟨n40, d40, u40⟩ := s39.notTaken E39.self 0x90E sv_at_90a
    (by decide) (by rw [g39_11, g39_12]; exact br_bne_byte_f (by decide) hz_39)
  have s40 : St n40.mem SV n40 0x90E (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
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
  have g40_10 : reg n40 a0 = (vp) + BitVec.ofNat 32 tl35.header := by rw [u40.regs, g39_10]
  have g40_11 : reg n40 a1 = (BitVec.ofNat 8 tl35.tag).zeroExtend 32 := by rw [u40.regs, g39_11]
  have g40_12 : reg n40 a2 = BitVec.ofNat 32 0xC := by rw [u40.regs, g39_12]
  have g40_18 : reg n40 (18 : Fin 32) = out := by rw [u40.regs, g39_18]
  have g40_19 : reg n40 (19 : Fin 32) = bp := by rw [u40.regs, g39_19]
  have g40_21 : reg n40 (21 : Fin 32) = x21 := by rw [u40.regs, g39_21]
  have g40_22 : reg n40 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u40.regs, g39_22]
  have g40_23 : reg n40 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u40.regs, g39_23]
  have g40_25 : reg n40 (25 : Fin 32) = x25 := by rw [u40.regs, g39_25]
  have g40_26 : reg n40 (26 : Fin 32) = x26 := by rw [u40.regs, g39_26]
  have g40_27 : reg n40 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u40.regs, g39_27]
  have keep_kk40 : SvKeepL B n0.mem n40.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := by rw [m40]; exact keep_kk39
  clear keep_kk39
  have w40_30 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m40]; exact w39_30
  have w40_34 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m40]; exact w39_34
  have w40_38 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m40]; exact w39_38
  have w40_3c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m40]; exact w39_3c
  have w40_40 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m40]; exact w39_40
  have w40_48 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m40]; exact w39_48
  have w40_4c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m40]; exact w39_4c
  have w40_50 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m40]; exact w39_50
  have w40_54 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m40]; exact w39_54
  have w40_58 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m40]; exact w39_58
  have w40_5c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m40]; exact w39_5c
  have w40_60 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m40]; exact w39_60
  have w40_64 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m40]; exact w39_64
  have w40_68 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m40]; exact w39_68
  have w40_6c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m40]; exact w39_6c
  have w40_70 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m40]; exact w39_70
  have w40_74 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m40]; exact w39_74
  have w40_78 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m40]; exact w39_78
  have w40_7c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m40]; exact w39_7c
  have w40_80 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m40]; exact w39_80
  have w40_84 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m40]; exact w39_84
  have w40_88 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m40]; exact w39_88
  have w40_8c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m40]; exact w39_8c
  have w40_90 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m40]; exact w39_90
  have w40_94 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m40]; exact w39_94
  have w40_a20 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m40]; exact w39_a20
  have w40_a24 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m40]; exact w39_a24
  have w40_a28 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m40]; exact w39_a28
  have w40_a2c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m40]; exact w39_a2c
  have w40_a30 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m40]; exact w39_a30
  have w40_a34 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m40]; exact w39_a34
  have w40_a38 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m40]; exact w39_a38
  have w40_a3c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m40]; exact w39_a3c
  have w40_a40 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m40]; exact w39_a40
  have w40_a44 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m40]; exact w39_a44
  have w40_1020 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m40]; exact w39_1020
  have w40_1024 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m40]; exact w39_1024
  have w40_1028 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m40]; exact w39_1028
  have w40_102c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m40]; exact w39_102c
  have w40_1480 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m40]; exact w39_1480
  have w40_1484 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m40]; exact w39_1484
  have w40_1488 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m40]; exact w39_1488
  have w40_148c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m40]; exact w39_148c
  have b40_1030 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m40]; exact b39_1030
  clear b39_1030 w39_148c w39_1488 w39_1484 w39_1480 w39_102c w39_1028 w39_1024 w39_1020 w39_a44 w39_a40 w39_a3c w39_a38 w39_a34 w39_a30 w39_a2c w39_a28 w39_a24 w39_a20 w39_94 w39_90 w39_8c w39_88 w39_84 w39_80 w39_7c w39_78 w39_74 w39_70 w39_6c w39_68 w39_64 w39_60 w39_5c w39_58 w39_54 w39_50 w39_4c w39_48 w39_40 w39_3c w39_38 w39_34 w39_30 g39_12 g39_27 g39_26 g39_25 g39_23 g39_22 g39_21 g39_19 g39_18 g39_11 g39_10 g39_9 g39_8 g39_4 g39_3 g39_2 V39 E39 fR39 t39 fr39 rb39 s39 m39 u39 c39
  -- 0x90E: lw
  obtain ⟨n41, d41, u41⟩ := s40.lw E40.self sv_at_90e (off' := 0x912) (by decide)
    (by rw [g40_8, show B + 0x21A0 + BitVec.ofNat 32 0x1320 + 0x16C = B + 0x21A0 + BitVec.ofNat 32 0x148C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s41 : St n41.mem SV n41 0x912 (reg n41) := ⟨u41.pc, rfl, fun _ => rfl⟩
  have m41 : n41.mem = n40.mem := u41.mem
  have fr41 : ∀ x, SvR B x → n41.mem x = n40.mem x := fun x _ => by rw [m41]
  have t41 : Steps n0 n41 := t40.trans (.single d41)
  have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
  have E41 : SvCode n41.mem := E40.fr F fr41
  have V41 : SvSaves B n41.mem v := V40.same m41
  have g41_2 : reg n41 sp = B + 0x21A0 := by rw [u41.regs, upd_ne (by decide) (by decide), g40_2]
  have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u41.regs, upd_ne (by decide) (by decide), g40_3]
  have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u41.regs, upd_ne (by decide) (by decide), g40_4]
  have g41_8 : reg n41 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u41.regs, upd_ne (by decide) (by decide), g40_8]
  have g41_9 : reg n41 (9 : Fin 32) = x9 := by rw [u41.regs, upd_ne (by decide) (by decide), g40_9]
  have g41_10 : reg n41 a0 = (vp) + BitVec.ofNat 32 tl35.header := by rw [u41.regs, upd_ne (by decide) (by decide), g40_10]
  have g41_12 : reg n41 a2 = BitVec.ofNat 32 0xC := by rw [u41.regs, upd_ne (by decide) (by decide), g40_12]
  have g41_18 : reg n41 (18 : Fin 32) = out := by rw [u41.regs, upd_ne (by decide) (by decide), g40_18]
  have g41_19 : reg n41 (19 : Fin 32) = bp := by rw [u41.regs, upd_ne (by decide) (by decide), g40_19]
  have g41_21 : reg n41 (21 : Fin 32) = x21 := by rw [u41.regs, upd_ne (by decide) (by decide), g40_21]
  have g41_22 : reg n41 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u41.regs, upd_ne (by decide) (by decide), g40_22]
  have g41_23 : reg n41 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u41.regs, upd_ne (by decide) (by decide), g40_23]
  have g41_25 : reg n41 (25 : Fin 32) = x25 := by rw [u41.regs, upd_ne (by decide) (by decide), g40_25]
  have g41_26 : reg n41 (26 : Fin 32) = x26 := by rw [u41.regs, upd_ne (by decide) (by decide), g40_26]
  have g41_27 : reg n41 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u41.regs, upd_ne (by decide) (by decide), g40_27]
  have g41_11 : reg n41 a1 = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by
    rw [u41.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g40_8, show B + 0x21A0 + BitVec.ofNat 32 0x1320 + 0x16C = B + 0x21A0 + BitVec.ofNat 32 0x148C by sv_addr, w40_148c]
  have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := by rw [m41]; exact keep_kk40
  clear keep_kk40
  have w41_30 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m41]; exact w40_30
  have w41_34 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m41]; exact w40_34
  have w41_38 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m41]; exact w40_38
  have w41_3c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m41]; exact w40_3c
  have w41_40 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m41]; exact w40_40
  have w41_48 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m41]; exact w40_48
  have w41_4c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m41]; exact w40_4c
  have w41_50 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m41]; exact w40_50
  have w41_54 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m41]; exact w40_54
  have w41_58 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m41]; exact w40_58
  have w41_5c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m41]; exact w40_5c
  have w41_60 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m41]; exact w40_60
  have w41_64 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m41]; exact w40_64
  have w41_68 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m41]; exact w40_68
  have w41_6c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m41]; exact w40_6c
  have w41_70 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m41]; exact w40_70
  have w41_74 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m41]; exact w40_74
  have w41_78 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m41]; exact w40_78
  have w41_7c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m41]; exact w40_7c
  have w41_80 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m41]; exact w40_80
  have w41_84 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m41]; exact w40_84
  have w41_88 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m41]; exact w40_88
  have w41_8c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m41]; exact w40_8c
  have w41_90 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m41]; exact w40_90
  have w41_94 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m41]; exact w40_94
  have w41_a20 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m41]; exact w40_a20
  have w41_a24 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m41]; exact w40_a24
  have w41_a28 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m41]; exact w40_a28
  have w41_a2c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m41]; exact w40_a2c
  have w41_a30 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m41]; exact w40_a30
  have w41_a34 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m41]; exact w40_a34
  have w41_a38 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m41]; exact w40_a38
  have w41_a3c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m41]; exact w40_a3c
  have w41_a40 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m41]; exact w40_a40
  have w41_a44 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m41]; exact w40_a44
  have w41_1020 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m41]; exact w40_1020
  have w41_1024 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m41]; exact w40_1024
  have w41_1028 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m41]; exact w40_1028
  have w41_102c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m41]; exact w40_102c
  have w41_1480 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m41]; exact w40_1480
  have w41_1484 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m41]; exact w40_1484
  have w41_1488 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m41]; exact w40_1488
  have w41_148c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m41]; exact w40_148c
  have b41_1030 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m41]; exact b40_1030
  clear b40_1030 w40_148c w40_1488 w40_1484 w40_1480 w40_102c w40_1028 w40_1024 w40_1020 w40_a44 w40_a40 w40_a3c w40_a38 w40_a34 w40_a30 w40_a2c w40_a28 w40_a24 w40_a20 w40_94 w40_90 w40_8c w40_88 w40_84 w40_80 w40_7c w40_78 w40_74 w40_70 w40_6c w40_68 w40_64 w40_60 w40_5c w40_58 w40_54 w40_50 w40_4c w40_48 w40_40 w40_3c w40_38 w40_34 w40_30 g40_27 g40_26 g40_25 g40_23 g40_22 g40_21 g40_19 g40_18 g40_12 g40_11 g40_10 g40_9 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 m40 s40 u40 d40
  by_cases hz_41 : (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) = 0
  rotate_left
  · -- 0x912: branch, taken
    obtain ⟨n42, d42, u42⟩ := s41.taken E41.self 0xB36 sv_at_912
      (by decide) (by rw [g41_11, s41.zero]; exact br_bne_t hz_41)
    have s42 : St n42.mem SV n42 0xB36 (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
    have m42 : n42.mem = n41.mem := u42.mem
    have fr42 : ∀ x, SvR B x → n42.mem x = n41.mem x := fun x _ => by rw [m42]
    have t42 : Steps n0 n42 := t41.trans (.single d42)
    have fR42 : ∀ x, SvR B x → n42.mem x = M0 x := fun x hx => (fr42 x hx).trans (fR41 x hx)
    have E42 : SvCode n42.mem := E41.fr F fr42
    have V42 : SvSaves B n42.mem v := V41.same m42
    have g42_2 : reg n42 sp = B + 0x21A0 := by rw [u42.regs, g41_2]
    have g42_3 : reg n42 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u42.regs, g41_3]
    have g42_4 : reg n42 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u42.regs, g41_4]
    have g42_8 : reg n42 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u42.regs, g41_8]
    have g42_9 : reg n42 (9 : Fin 32) = x9 := by rw [u42.regs, g41_9]
    have g42_10 : reg n42 a0 = (vp) + BitVec.ofNat 32 tl35.header := by rw [u42.regs, g41_10]
    have g42_11 : reg n42 a1 = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [u42.regs, g41_11]
    have g42_12 : reg n42 a2 = BitVec.ofNat 32 0xC := by rw [u42.regs, g41_12]
    have g42_18 : reg n42 (18 : Fin 32) = out := by rw [u42.regs, g41_18]
    have g42_19 : reg n42 (19 : Fin 32) = bp := by rw [u42.regs, g41_19]
    have g42_21 : reg n42 (21 : Fin 32) = x21 := by rw [u42.regs, g41_21]
    have g42_22 : reg n42 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u42.regs, g41_22]
    have g42_23 : reg n42 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u42.regs, g41_23]
    have g42_25 : reg n42 (25 : Fin 32) = x25 := by rw [u42.regs, g41_25]
    have g42_26 : reg n42 (26 : Fin 32) = x26 := by rw [u42.regs, g41_26]
    have g42_27 : reg n42 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u42.regs, g41_27]
    have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := by rw [m42]; exact keep_kk41
    clear keep_kk41
    have w42_30 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m42]; exact w41_30
    have w42_34 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m42]; exact w41_34
    have w42_38 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m42]; exact w41_38
    have w42_3c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m42]; exact w41_3c
    have w42_40 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m42]; exact w41_40
    have w42_48 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m42]; exact w41_48
    have w42_4c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m42]; exact w41_4c
    have w42_50 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m42]; exact w41_50
    have w42_54 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m42]; exact w41_54
    have w42_58 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m42]; exact w41_58
    have w42_5c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m42]; exact w41_5c
    have w42_60 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m42]; exact w41_60
    have w42_64 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m42]; exact w41_64
    have w42_68 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m42]; exact w41_68
    have w42_6c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m42]; exact w41_6c
    have w42_70 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m42]; exact w41_70
    have w42_74 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m42]; exact w41_74
    have w42_78 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m42]; exact w41_78
    have w42_7c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m42]; exact w41_7c
    have w42_80 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m42]; exact w41_80
    have w42_84 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m42]; exact w41_84
    have w42_88 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m42]; exact w41_88
    have w42_8c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m42]; exact w41_8c
    have w42_90 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m42]; exact w41_90
    have w42_94 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m42]; exact w41_94
    have w42_a20 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m42]; exact w41_a20
    have w42_a24 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m42]; exact w41_a24
    have w42_a28 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m42]; exact w41_a28
    have w42_a2c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m42]; exact w41_a2c
    have w42_a30 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m42]; exact w41_a30
    have w42_a34 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m42]; exact w41_a34
    have w42_a38 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m42]; exact w41_a38
    have w42_a3c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m42]; exact w41_a3c
    have w42_a40 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m42]; exact w41_a40
    have w42_a44 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m42]; exact w41_a44
    have w42_1020 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m42]; exact w41_1020
    have w42_1024 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m42]; exact w41_1024
    have w42_1028 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m42]; exact w41_1028
    have w42_102c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m42]; exact w41_102c
    have w42_1480 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m42]; exact w41_1480
    have w42_1484 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m42]; exact w41_1484
    have w42_1488 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m42]; exact w41_1488
    have w42_148c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m42]; exact w41_148c
    have b42_1030 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m42]; exact b41_1030
    clear b41_1030 w41_148c w41_1488 w41_1484 w41_1480 w41_102c w41_1028 w41_1024 w41_1020 w41_a44 w41_a40 w41_a3c w41_a38 w41_a34 w41_a30 w41_a2c w41_a28 w41_a24 w41_a20 w41_94 w41_90 w41_8c w41_88 w41_84 w41_80 w41_7c w41_78 w41_74 w41_70 w41_6c w41_68 w41_64 w41_60 w41_5c w41_58 w41_54 w41_50 w41_4c w41_48 w41_40 w41_3c w41_38 w41_34 w41_30 g41_11 g41_27 g41_26 g41_25 g41_23 g41_22 g41_21 g41_19 g41_18 g41_12 g41_10 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 fr41 m41 s41 u41 d41
    -- 0xB36
    obtain ⟨n43, c43, u43⟩ := s42.block svDp0b36 E42.self svDp0b36_end
      ⟨trivial, trivial⟩
    have m43 : n43.mem = n42.mem := u43.mem
    have s43 : St n43.mem SV n43 0xB38 (reg n43) := ⟨u43.pc, rfl, fun _ => rfl⟩
    have rb43 : ∀ q, reg n43 q = (runBlock svDp0b36 (n42.mem, reg n42)).2 q := fun q => by rw [u43.regs]
    have fr43 : ∀ x, SvR B x → n43.mem x = n42.mem x := fun x _ => by rw [m43]
    have t43 : Steps n0 n43 := t42.trans c43
    have fR43 : ∀ x, SvR B x → n43.mem x = M0 x := fun x hx => (fr43 x hx).trans (fR42 x hx)
    have E43 : SvCode n43.mem := E42.fr F fr43
    have V43 : SvSaves B n43.mem v := V42.same m43
    have g43_2 : reg n43 sp = B + 0x21A0 := by
      rw [rb43, runBlock_reg _ _ _ sp s42.zero (by decide), g42_2]
    have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb43, runBlock_reg _ _ _ (3 : Fin 32) s42.zero (by decide), g42_3]
    have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb43, runBlock_reg _ _ _ (4 : Fin 32) s42.zero (by decide), g42_4]
    have g43_8 : reg n43 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
      rw [rb43, runBlock_reg _ _ _ (8 : Fin 32) s42.zero (by decide), g42_8]
    have g43_9 : reg n43 (9 : Fin 32) = x9 := by
      rw [rb43, runBlock_reg _ _ _ (9 : Fin 32) s42.zero (by decide), g42_9]
    have g43_11 : reg n43 a1 = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by
      rw [rb43, runBlock_reg _ _ _ a1 s42.zero (by decide), g42_11]
    have g43_12 : reg n43 a2 = BitVec.ofNat 32 0xC := by
      rw [rb43, runBlock_reg _ _ _ a2 s42.zero (by decide), g42_12]
    have g43_18 : reg n43 (18 : Fin 32) = out := by
      rw [rb43, runBlock_reg _ _ _ (18 : Fin 32) s42.zero (by decide), g42_18]
    have g43_19 : reg n43 (19 : Fin 32) = bp := by
      rw [rb43, runBlock_reg _ _ _ (19 : Fin 32) s42.zero (by decide), g42_19]
    have g43_21 : reg n43 (21 : Fin 32) = x21 := by
      rw [rb43, runBlock_reg _ _ _ (21 : Fin 32) s42.zero (by decide), g42_21]
    have g43_22 : reg n43 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [rb43, runBlock_reg _ _ _ (22 : Fin 32) s42.zero (by decide), g42_22]
    have g43_23 : reg n43 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by
      rw [rb43, runBlock_reg _ _ _ (23 : Fin 32) s42.zero (by decide), g42_23]
    have g43_25 : reg n43 (25 : Fin 32) = x25 := by
      rw [rb43, runBlock_reg _ _ _ (25 : Fin 32) s42.zero (by decide), g42_25]
    have g43_26 : reg n43 (26 : Fin 32) = x26 := by
      rw [rb43, runBlock_reg _ _ _ (26 : Fin 32) s42.zero (by decide), g42_26]
    have g43_27 : reg n43 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb43, runBlock_reg _ _ _ (27 : Fin 32) s42.zero (by decide), g42_27]
    have g43_10 : reg n43 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb43]; simp +decide only [runBlock, BInstr.run, svDp0b36, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g42_2, g42_3, g42_4, g42_8, g42_9, g42_10, g42_11, g42_12, g42_18, g42_19, g42_21, g42_22, g42_23, g42_25, g42_26, g42_27, s42.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := by rw [m43]; exact keep_kk42
    clear keep_kk42
    have w43_30 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m43]; exact w42_30
    have w43_34 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m43]; exact w42_34
    have w43_38 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m43]; exact w42_38
    have w43_3c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m43]; exact w42_3c
    have w43_40 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m43]; exact w42_40
    have w43_48 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m43]; exact w42_48
    have w43_4c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m43]; exact w42_4c
    have w43_50 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m43]; exact w42_50
    have w43_54 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m43]; exact w42_54
    have w43_58 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m43]; exact w42_58
    have w43_5c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m43]; exact w42_5c
    have w43_60 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m43]; exact w42_60
    have w43_64 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m43]; exact w42_64
    have w43_68 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m43]; exact w42_68
    have w43_6c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m43]; exact w42_6c
    have w43_70 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m43]; exact w42_70
    have w43_74 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m43]; exact w42_74
    have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m43]; exact w42_78
    have w43_7c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m43]; exact w42_7c
    have w43_80 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m43]; exact w42_80
    have w43_84 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m43]; exact w42_84
    have w43_88 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m43]; exact w42_88
    have w43_8c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m43]; exact w42_8c
    have w43_90 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m43]; exact w42_90
    have w43_94 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m43]; exact w42_94
    have w43_a20 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m43]; exact w42_a20
    have w43_a24 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m43]; exact w42_a24
    have w43_a28 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m43]; exact w42_a28
    have w43_a2c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m43]; exact w42_a2c
    have w43_a30 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m43]; exact w42_a30
    have w43_a34 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m43]; exact w42_a34
    have w43_a38 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m43]; exact w42_a38
    have w43_a3c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m43]; exact w42_a3c
    have w43_a40 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m43]; exact w42_a40
    have w43_a44 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m43]; exact w42_a44
    have w43_1020 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m43]; exact w42_1020
    have w43_1024 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m43]; exact w42_1024
    have w43_1028 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m43]; exact w42_1028
    have w43_102c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m43]; exact w42_102c
    have w43_1480 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m43]; exact w42_1480
    have w43_1484 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m43]; exact w42_1484
    have w43_1488 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m43]; exact w42_1488
    have w43_148c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m43]; exact w42_148c
    have b43_1030 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m43]; exact b42_1030
    clear b42_1030 w42_148c w42_1488 w42_1484 w42_1480 w42_102c w42_1028 w42_1024 w42_1020 w42_a44 w42_a40 w42_a3c w42_a38 w42_a34 w42_a30 w42_a2c w42_a28 w42_a24 w42_a20 w42_94 w42_90 w42_8c w42_88 w42_84 w42_80 w42_7c w42_78 w42_74 w42_70 w42_6c w42_68 w42_64 w42_60 w42_5c w42_58 w42_54 w42_50 w42_4c w42_48 w42_40 w42_3c w42_38 w42_34 w42_30 g42_27 g42_26 g42_25 g42_23 g42_22 g42_21 g42_19 g42_18 g42_12 g42_11 g42_10 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 m42 s42 u42 d42
    -- 0xB38: sw
    obtain ⟨n44, d44, s44, fr44, K44, W44, rg44⟩ := sv_sw F E43 s43 sv_at_b38 (off' := 0xB3A) (c := 0x44)
      (by decide) (by rw [g43_2]; sv_addr) (by decide) (by decide)
    have t44 : Steps n0 n44 := t43.trans d44
    have fR44 : ∀ x, SvR B x → n44.mem x = M0 x := fun x hx => (fr44 x hx).trans (fR43 x hx)
    have E44 : SvCode n44.mem := E43.fr F fr44
    have V44 : SvSaves B n44.mem v := V43.keep K44 (by decide)
    have g44_2 : reg n44 sp = B + 0x21A0 := by rw [rg44 sp, g43_2]
    have g44_3 : reg n44 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg44 (3 : Fin 32), g43_3]
    have g44_4 : reg n44 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg44 (4 : Fin 32), g43_4]
    have g44_8 : reg n44 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg44 (8 : Fin 32), g43_8]
    have g44_9 : reg n44 (9 : Fin 32) = x9 := by rw [rg44 (9 : Fin 32), g43_9]
    have g44_10 : reg n44 a0 = BitVec.ofNat 32 0x1 := by rw [rg44 a0, g43_10]
    have g44_11 : reg n44 a1 = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [rg44 a1, g43_11]
    have g44_12 : reg n44 a2 = BitVec.ofNat 32 0xC := by rw [rg44 a2, g43_12]
    have g44_18 : reg n44 (18 : Fin 32) = out := by rw [rg44 (18 : Fin 32), g43_18]
    have g44_19 : reg n44 (19 : Fin 32) = bp := by rw [rg44 (19 : Fin 32), g43_19]
    have g44_21 : reg n44 (21 : Fin 32) = x21 := by rw [rg44 (21 : Fin 32), g43_21]
    have g44_22 : reg n44 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg44 (22 : Fin 32), g43_22]
    have g44_23 : reg n44 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [rg44 (23 : Fin 32), g43_23]
    have g44_25 : reg n44 (25 : Fin 32) = x25 := by rw [rg44 (25 : Fin 32), g43_25]
    have g44_26 : reg n44 (26 : Fin 32) = x26 := by rw [rg44 (26 : Fin 32), g43_26]
    have g44_27 : reg n44 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg44 (27 : Fin 32), g43_27]
    have keep_kk44 : SvKeepL B n0.mem n44.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0x44, 0x4)] := keep_kk43.trans K44.toL
    clear keep_kk43
    have w44_30 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K44.w32 (by decide) (by decide)).trans w43_30
    have w44_34 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K44.w32 (by decide) (by decide)).trans w43_34
    have w44_38 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K44.w32 (by decide) (by decide)).trans w43_38
    have w44_3c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K44.w32 (by decide) (by decide)).trans w43_3c
    have w44_40 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K44.w32 (by decide) (by decide)).trans w43_40
    have w44_48 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K44.w32 (by decide) (by decide)).trans w43_48
    have w44_4c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K44.w32 (by decide) (by decide)).trans w43_4c
    have w44_50 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K44.w32 (by decide) (by decide)).trans w43_50
    have w44_54 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K44.w32 (by decide) (by decide)).trans w43_54
    have w44_58 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K44.w32 (by decide) (by decide)).trans w43_58
    have w44_5c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K44.w32 (by decide) (by decide)).trans w43_5c
    have w44_60 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K44.w32 (by decide) (by decide)).trans w43_60
    have w44_64 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K44.w32 (by decide) (by decide)).trans w43_64
    have w44_68 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K44.w32 (by decide) (by decide)).trans w43_68
    have w44_6c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K44.w32 (by decide) (by decide)).trans w43_6c
    have w44_70 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K44.w32 (by decide) (by decide)).trans w43_70
    have w44_74 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K44.w32 (by decide) (by decide)).trans w43_74
    have w44_78 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K44.w32 (by decide) (by decide)).trans w43_78
    have w44_7c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K44.w32 (by decide) (by decide)).trans w43_7c
    have w44_80 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K44.w32 (by decide) (by decide)).trans w43_80
    have w44_84 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K44.w32 (by decide) (by decide)).trans w43_84
    have w44_88 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K44.w32 (by decide) (by decide)).trans w43_88
    have w44_8c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K44.w32 (by decide) (by decide)).trans w43_8c
    have w44_90 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K44.w32 (by decide) (by decide)).trans w43_90
    have w44_94 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K44.w32 (by decide) (by decide)).trans w43_94
    have w44_a20 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K44.w32 (by decide) (by decide)).trans w43_a20
    have w44_a24 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K44.w32 (by decide) (by decide)).trans w43_a24
    have w44_a28 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K44.w32 (by decide) (by decide)).trans w43_a28
    have w44_a2c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K44.w32 (by decide) (by decide)).trans w43_a2c
    have w44_a30 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K44.w32 (by decide) (by decide)).trans w43_a30
    have w44_a34 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K44.w32 (by decide) (by decide)).trans w43_a34
    have w44_a38 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K44.w32 (by decide) (by decide)).trans w43_a38
    have w44_a3c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K44.w32 (by decide) (by decide)).trans w43_a3c
    have w44_a40 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K44.w32 (by decide) (by decide)).trans w43_a40
    have w44_a44 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K44.w32 (by decide) (by decide)).trans w43_a44
    have w44_1020 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := (K44.w32 (by decide) (by decide)).trans w43_1020
    have w44_1024 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := (K44.w32 (by decide) (by decide)).trans w43_1024
    have w44_1028 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := (K44.w32 (by decide) (by decide)).trans w43_1028
    have w44_102c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := (K44.w32 (by decide) (by decide)).trans w43_102c
    have w44_1480 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K44.w32 (by decide) (by decide)).trans w43_1480
    have w44_1484 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K44.w32 (by decide) (by decide)).trans w43_1484
    have w44_1488 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := (K44.w32 (by decide) (by decide)).trans w43_1488
    have w44_148c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := (K44.w32 (by decide) (by decide)).trans w43_148c
    have b44_1030 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := (K44.b8 (by decide) (by decide)).trans b43_1030
    have w44_44 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [W44, g43_10]
    clear b43_1030 w43_148c w43_1488 w43_1484 w43_1480 w43_102c w43_1028 w43_1024 w43_1020 w43_a44 w43_a40 w43_a3c w43_a38 w43_a34 w43_a30 w43_a2c w43_a28 w43_a24 w43_a20 w43_94 w43_90 w43_8c w43_88 w43_84 w43_80 w43_7c w43_78 w43_74 w43_70 w43_6c w43_68 w43_64 w43_60 w43_5c w43_58 w43_54 w43_50 w43_4c w43_48 w43_40 w43_3c w43_38 w43_34 w43_30 g43_10 g43_27 g43_26 g43_25 g43_23 g43_22 g43_21 g43_19 g43_18 g43_12 g43_11 g43_9 g43_8 g43_4 g43_3 g43_2 V43 E43 fR43 t43 fr43 rb43 s43 m43 u43 c43
    -- 0xB3A: j
    obtain ⟨n45, d45, u45⟩ := s44.jump E44.self sv_at_b3a (off' := 0xB46) (by decide)
      (by rw [s44.pc]; decide)
    have s45 : St n45.mem SV n45 0xB46 (reg n45) := ⟨u45.pc, rfl, fun _ => rfl⟩
    have m45 : n45.mem = n44.mem := u45.mem
    have fr45 : ∀ x, SvR B x → n45.mem x = n44.mem x := fun x _ => by rw [m45]
    have t45 : Steps n0 n45 := t44.trans (.single d45)
    have fR45 : ∀ x, SvR B x → n45.mem x = M0 x := fun x hx => (fr45 x hx).trans (fR44 x hx)
    have E45 : SvCode n45.mem := E44.fr F fr45
    have V45 : SvSaves B n45.mem v := V44.same m45
    have g45_2 : reg n45 sp = B + 0x21A0 := by rw [u45.regs, g44_2]
    have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u45.regs, g44_3]
    have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u45.regs, g44_4]
    have g45_8 : reg n45 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u45.regs, g44_8]
    have g45_9 : reg n45 (9 : Fin 32) = x9 := by rw [u45.regs, g44_9]
    have g45_10 : reg n45 a0 = BitVec.ofNat 32 0x1 := by rw [u45.regs, g44_10]
    have g45_11 : reg n45 a1 = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [u45.regs, g44_11]
    have g45_12 : reg n45 a2 = BitVec.ofNat 32 0xC := by rw [u45.regs, g44_12]
    have g45_18 : reg n45 (18 : Fin 32) = out := by rw [u45.regs, g44_18]
    have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [u45.regs, g44_19]
    have g45_21 : reg n45 (21 : Fin 32) = x21 := by rw [u45.regs, g44_21]
    have g45_22 : reg n45 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u45.regs, g44_22]
    have g45_23 : reg n45 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u45.regs, g44_23]
    have g45_25 : reg n45 (25 : Fin 32) = x25 := by rw [u45.regs, g44_25]
    have g45_26 : reg n45 (26 : Fin 32) = x26 := by rw [u45.regs, g44_26]
    have g45_27 : reg n45 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u45.regs, g44_27]
    have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0x44, 0x4)] := by rw [m45]; exact keep_kk44
    clear keep_kk44
    have w45_30 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m45]; exact w44_30
    have w45_34 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m45]; exact w44_34
    have w45_38 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m45]; exact w44_38
    have w45_3c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m45]; exact w44_3c
    have w45_40 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m45]; exact w44_40
    have w45_44 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m45]; exact w44_44
    have w45_48 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m45]; exact w44_48
    have w45_4c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m45]; exact w44_4c
    have w45_50 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m45]; exact w44_50
    have w45_54 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m45]; exact w44_54
    have w45_58 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m45]; exact w44_58
    have w45_5c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m45]; exact w44_5c
    have w45_60 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m45]; exact w44_60
    have w45_64 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m45]; exact w44_64
    have w45_68 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m45]; exact w44_68
    have w45_6c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m45]; exact w44_6c
    have w45_70 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m45]; exact w44_70
    have w45_74 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m45]; exact w44_74
    have w45_78 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m45]; exact w44_78
    have w45_7c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m45]; exact w44_7c
    have w45_80 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m45]; exact w44_80
    have w45_84 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m45]; exact w44_84
    have w45_88 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m45]; exact w44_88
    have w45_8c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m45]; exact w44_8c
    have w45_90 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m45]; exact w44_90
    have w45_94 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m45]; exact w44_94
    have w45_a20 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m45]; exact w44_a20
    have w45_a24 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m45]; exact w44_a24
    have w45_a28 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m45]; exact w44_a28
    have w45_a2c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m45]; exact w44_a2c
    have w45_a30 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m45]; exact w44_a30
    have w45_a34 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m45]; exact w44_a34
    have w45_a38 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m45]; exact w44_a38
    have w45_a3c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m45]; exact w44_a3c
    have w45_a40 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m45]; exact w44_a40
    have w45_a44 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m45]; exact w44_a44
    have w45_1020 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m45]; exact w44_1020
    have w45_1024 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m45]; exact w44_1024
    have w45_1028 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m45]; exact w44_1028
    have w45_102c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m45]; exact w44_102c
    have w45_1480 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m45]; exact w44_1480
    have w45_1484 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m45]; exact w44_1484
    have w45_1488 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m45]; exact w44_1488
    have w45_148c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m45]; exact w44_148c
    have b45_1030 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m45]; exact b44_1030
    clear w44_44 b44_1030 w44_148c w44_1488 w44_1484 w44_1480 w44_102c w44_1028 w44_1024 w44_1020 w44_a44 w44_a40 w44_a3c w44_a38 w44_a34 w44_a30 w44_a2c w44_a28 w44_a24 w44_a20 w44_94 w44_90 w44_8c w44_88 w44_84 w44_80 w44_7c w44_78 w44_74 w44_70 w44_6c w44_68 w44_64 w44_60 w44_5c w44_58 w44_54 w44_50 w44_4c w44_48 w44_40 w44_3c w44_38 w44_34 w44_30 g44_27 g44_26 g44_25 g44_23 g44_22 g44_21 g44_19 g44_18 g44_12 g44_11 g44_10 g44_9 g44_8 g44_4 g44_3 g44_2 V44 E44 fR44 t44 rg44 W44 K44 fr44 s44 d44
    -- 0xB46: lw
    obtain ⟨n46, d46, u46⟩ := s45.lw E45.self sv_at_b46 (off' := 0xB48) (by decide)
      (by rw [g45_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s46 : St n46.mem SV n46 0xB48 (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
    have m46 : n46.mem = n45.mem := u46.mem
    have fr46 : ∀ x, SvR B x → n46.mem x = n45.mem x := fun x _ => by rw [m46]
    have t46 : Steps n0 n46 := t45.trans (.single d46)
    have fR46 : ∀ x, SvR B x → n46.mem x = M0 x := fun x hx => (fr46 x hx).trans (fR45 x hx)
    have E46 : SvCode n46.mem := E45.fr F fr46
    have V46 : SvSaves B n46.mem v := V45.same m46
    have g46_2 : reg n46 sp = B + 0x21A0 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_2]
    have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u46.regs, upd_ne (by decide) (by decide), g45_3]
    have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u46.regs, upd_ne (by decide) (by decide), g45_4]
    have g46_8 : reg n46 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_8]
    have g46_9 : reg n46 (9 : Fin 32) = x9 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_9]
    have g46_10 : reg n46 a0 = BitVec.ofNat 32 0x1 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_10]
    have g46_11 : reg n46 a1 = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [u46.regs, upd_ne (by decide) (by decide), g45_11]
    have g46_12 : reg n46 a2 = BitVec.ofNat 32 0xC := by rw [u46.regs, upd_ne (by decide) (by decide), g45_12]
    have g46_18 : reg n46 (18 : Fin 32) = out := by rw [u46.regs, upd_ne (by decide) (by decide), g45_18]
    have g46_19 : reg n46 (19 : Fin 32) = bp := by rw [u46.regs, upd_ne (by decide) (by decide), g45_19]
    have g46_21 : reg n46 (21 : Fin 32) = x21 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_21]
    have g46_22 : reg n46 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_22]
    have g46_23 : reg n46 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_23]
    have g46_25 : reg n46 (25 : Fin 32) = x25 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_25]
    have g46_26 : reg n46 (26 : Fin 32) = x26 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_26]
    have g46_27 : reg n46 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_27]
    have keep_kk46 : SvKeepL B n0.mem n46.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0x44, 0x4)] := by rw [m46]; exact keep_kk45
    clear keep_kk45
    have w46_30 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m46]; exact w45_30
    have w46_34 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m46]; exact w45_34
    have w46_38 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m46]; exact w45_38
    have w46_3c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m46]; exact w45_3c
    have w46_40 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m46]; exact w45_40
    have w46_44 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m46]; exact w45_44
    have w46_48 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m46]; exact w45_48
    have w46_4c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m46]; exact w45_4c
    have w46_50 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m46]; exact w45_50
    have w46_54 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m46]; exact w45_54
    have w46_58 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m46]; exact w45_58
    have w46_5c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m46]; exact w45_5c
    have w46_60 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m46]; exact w45_60
    have w46_64 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m46]; exact w45_64
    have w46_68 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m46]; exact w45_68
    have w46_6c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m46]; exact w45_6c
    have w46_70 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m46]; exact w45_70
    have w46_74 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m46]; exact w45_74
    have w46_78 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m46]; exact w45_78
    have w46_7c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m46]; exact w45_7c
    have w46_80 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m46]; exact w45_80
    have w46_84 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m46]; exact w45_84
    have w46_88 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m46]; exact w45_88
    have w46_8c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m46]; exact w45_8c
    have w46_90 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m46]; exact w45_90
    have w46_94 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m46]; exact w45_94
    have w46_a20 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m46]; exact w45_a20
    have w46_a24 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m46]; exact w45_a24
    have w46_a28 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m46]; exact w45_a28
    have w46_a2c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m46]; exact w45_a2c
    have w46_a30 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m46]; exact w45_a30
    have w46_a34 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m46]; exact w45_a34
    have w46_a38 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m46]; exact w45_a38
    have w46_a3c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m46]; exact w45_a3c
    have w46_a40 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m46]; exact w45_a40
    have w46_a44 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m46]; exact w45_a44
    have w46_1020 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m46]; exact w45_1020
    have w46_1024 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m46]; exact w45_1024
    have w46_1028 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m46]; exact w45_1028
    have w46_102c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m46]; exact w45_102c
    have w46_1480 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m46]; exact w45_1480
    have w46_1484 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m46]; exact w45_1484
    have w46_1488 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m46]; exact w45_1488
    have w46_148c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m46]; exact w45_148c
    have b46_1030 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m46]; exact b45_1030
    clear b45_1030 w45_148c w45_1488 w45_1484 w45_1480 w45_102c w45_1028 w45_1024 w45_1020 w45_a44 w45_a40 w45_a3c w45_a38 w45_a34 w45_a30 w45_a2c w45_a28 w45_a24 w45_a20 w45_94 w45_90 w45_8c w45_88 w45_84 w45_80 w45_7c w45_78 w45_74 w45_70 w45_6c w45_68 w45_64 w45_60 w45_5c w45_58 w45_54 w45_50 w45_4c w45_48 w45_44 w45_40 w45_3c w45_38 w45_34 w45_30 g45_27 g45_26 g45_25 g45_23 g45_22 g45_21 g45_19 g45_18 g45_12 g45_11 g45_10 g45_9 g45_8 g45_4 g45_3 g45_2 V45 E45 fR45 t45 fr45 m45 s45 u45 d45
    -- 0xB48: j
    obtain ⟨n47, d47, u47⟩ := s46.jump E46.self sv_at_b48 (off' := 0x966) (by decide)
      (by rw [s46.pc]; decide)
    have s47 : St n47.mem SV n47 0x966 (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
    have m47 : n47.mem = n46.mem := u47.mem
    have fr47 : ∀ x, SvR B x → n47.mem x = n46.mem x := fun x _ => by rw [m47]
    have t47 : Steps n0 n47 := t46.trans (.single d47)
    have fR47 : ∀ x, SvR B x → n47.mem x = M0 x := fun x hx => (fr47 x hx).trans (fR46 x hx)
    have E47 : SvCode n47.mem := E46.fr F fr47
    have V47 : SvSaves B n47.mem v := V46.same m47
    have g47_2 : reg n47 sp = B + 0x21A0 := by rw [u47.regs, g46_2]
    have g47_3 : reg n47 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u47.regs, g46_3]
    have g47_4 : reg n47 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u47.regs, g46_4]
    have g47_8 : reg n47 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u47.regs, g46_8]
    have g47_9 : reg n47 (9 : Fin 32) = x9 := by rw [u47.regs, g46_9]
    have g47_10 : reg n47 a0 = BitVec.ofNat 32 0x1 := by rw [u47.regs, g46_10]
    have g47_11 : reg n47 a1 = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [u47.regs, g46_11]
    have g47_12 : reg n47 a2 = BitVec.ofNat 32 0xC := by rw [u47.regs, g46_12]
    have g47_18 : reg n47 (18 : Fin 32) = out := by rw [u47.regs, g46_18]
    have g47_19 : reg n47 (19 : Fin 32) = bp := by rw [u47.regs, g46_19]
    have g47_21 : reg n47 (21 : Fin 32) = x21 := by rw [u47.regs, g46_21]
    have g47_22 : reg n47 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u47.regs, g46_22]
    have g47_23 : reg n47 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u47.regs, g46_23]
    have g47_25 : reg n47 (25 : Fin 32) = x25 := by rw [u47.regs, g46_25]
    have g47_26 : reg n47 (26 : Fin 32) = x26 := by rw [u47.regs, g46_26]
    have g47_27 : reg n47 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u47.regs, g46_27]
    have keep_kk47 : SvKeepL B n0.mem n47.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0x44, 0x4)] := by rw [m47]; exact keep_kk46
    clear keep_kk46
    have w47_30 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m47]; exact w46_30
    have w47_34 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m47]; exact w46_34
    have w47_38 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m47]; exact w46_38
    have w47_3c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m47]; exact w46_3c
    have w47_40 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m47]; exact w46_40
    have w47_44 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m47]; exact w46_44
    have w47_48 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m47]; exact w46_48
    have w47_4c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m47]; exact w46_4c
    have w47_50 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m47]; exact w46_50
    have w47_54 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m47]; exact w46_54
    have w47_58 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m47]; exact w46_58
    have w47_5c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m47]; exact w46_5c
    have w47_60 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m47]; exact w46_60
    have w47_64 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m47]; exact w46_64
    have w47_68 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m47]; exact w46_68
    have w47_6c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m47]; exact w46_6c
    have w47_70 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m47]; exact w46_70
    have w47_74 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m47]; exact w46_74
    have w47_78 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m47]; exact w46_78
    have w47_7c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m47]; exact w46_7c
    have w47_80 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m47]; exact w46_80
    have w47_84 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m47]; exact w46_84
    have w47_88 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m47]; exact w46_88
    have w47_8c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m47]; exact w46_8c
    have w47_90 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m47]; exact w46_90
    have w47_94 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m47]; exact w46_94
    have w47_a20 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m47]; exact w46_a20
    have w47_a24 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m47]; exact w46_a24
    have w47_a28 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m47]; exact w46_a28
    have w47_a2c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m47]; exact w46_a2c
    have w47_a30 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m47]; exact w46_a30
    have w47_a34 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m47]; exact w46_a34
    have w47_a38 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m47]; exact w46_a38
    have w47_a3c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m47]; exact w46_a3c
    have w47_a40 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m47]; exact w46_a40
    have w47_a44 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m47]; exact w46_a44
    have w47_1020 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m47]; exact w46_1020
    have w47_1024 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m47]; exact w46_1024
    have w47_1028 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m47]; exact w46_1028
    have w47_102c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m47]; exact w46_102c
    have w47_1480 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m47]; exact w46_1480
    have w47_1484 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m47]; exact w46_1484
    have w47_1488 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m47]; exact w46_1488
    have w47_148c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m47]; exact w46_148c
    have b47_1030 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m47]; exact b46_1030
    clear b46_1030 w46_148c w46_1488 w46_1484 w46_1480 w46_102c w46_1028 w46_1024 w46_1020 w46_a44 w46_a40 w46_a3c w46_a38 w46_a34 w46_a30 w46_a2c w46_a28 w46_a24 w46_a20 w46_94 w46_90 w46_8c w46_88 w46_84 w46_80 w46_7c w46_78 w46_74 w46_70 w46_6c w46_68 w46_64 w46_60 w46_5c w46_58 w46_54 w46_50 w46_4c w46_48 w46_44 w46_40 w46_3c w46_38 w46_34 w46_30 g46_27 g46_26 g46_25 g46_23 g46_22 g46_21 g46_19 g46_18 g46_12 g46_11 g46_10 g46_9 g46_8 g46_4 g46_3 g46_2 V46 E46 fR46 t46 fr46 m46 s46 u46 d46
    exact .inl ⟨(fun ⟨tl35', h0', h1', h2', _⟩ => by rw [hr35] at h0'; cases h0'; exact hz_41 h2'), sv_fail F E47 s47 t47 (fun x hx => (fR47 x hx).trans (fM x hx).symm) V47 hret g47_2 g47_18 hO g47_3 g47_4⟩
  -- 0x912: branch, not taken
  obtain ⟨n42, d42, u42⟩ := s41.notTaken E41.self 0x916 sv_at_912
    (by decide) (by rw [g41_11, s41.zero]; exact br_bne_f hz_41)
  have s42 : St n42.mem SV n42 0x916 (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
  have m42 : n42.mem = n41.mem := u42.mem
  have fr42 : ∀ x, SvR B x → n42.mem x = n41.mem x := fun x _ => by rw [m42]
  have t42 : Steps n0 n42 := t41.trans (.single d42)
  have fR42 : ∀ x, SvR B x → n42.mem x = M0 x := fun x hx => (fr42 x hx).trans (fR41 x hx)
  have E42 : SvCode n42.mem := E41.fr F fr42
  have V42 : SvSaves B n42.mem v := V41.same m42
  have g42_2 : reg n42 sp = B + 0x21A0 := by rw [u42.regs, g41_2]
  have g42_3 : reg n42 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u42.regs, g41_3]
  have g42_4 : reg n42 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u42.regs, g41_4]
  have g42_8 : reg n42 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u42.regs, g41_8]
  have g42_9 : reg n42 (9 : Fin 32) = x9 := by rw [u42.regs, g41_9]
  have g42_10 : reg n42 a0 = (vp) + BitVec.ofNat 32 tl35.header := by rw [u42.regs, g41_10]
  have g42_11 : reg n42 a1 = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [u42.regs, g41_11]
  have g42_12 : reg n42 a2 = BitVec.ofNat 32 0xC := by rw [u42.regs, g41_12]
  have g42_18 : reg n42 (18 : Fin 32) = out := by rw [u42.regs, g41_18]
  have g42_19 : reg n42 (19 : Fin 32) = bp := by rw [u42.regs, g41_19]
  have g42_21 : reg n42 (21 : Fin 32) = x21 := by rw [u42.regs, g41_21]
  have g42_22 : reg n42 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u42.regs, g41_22]
  have g42_23 : reg n42 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u42.regs, g41_23]
  have g42_25 : reg n42 (25 : Fin 32) = x25 := by rw [u42.regs, g41_25]
  have g42_26 : reg n42 (26 : Fin 32) = x26 := by rw [u42.regs, g41_26]
  have g42_27 : reg n42 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u42.regs, g41_27]
  have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := by rw [m42]; exact keep_kk41
  clear keep_kk41
  have w42_30 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m42]; exact w41_30
  have w42_34 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m42]; exact w41_34
  have w42_38 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m42]; exact w41_38
  have w42_3c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m42]; exact w41_3c
  have w42_40 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m42]; exact w41_40
  have w42_48 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m42]; exact w41_48
  have w42_4c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m42]; exact w41_4c
  have w42_50 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m42]; exact w41_50
  have w42_54 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m42]; exact w41_54
  have w42_58 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m42]; exact w41_58
  have w42_5c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m42]; exact w41_5c
  have w42_60 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m42]; exact w41_60
  have w42_64 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m42]; exact w41_64
  have w42_68 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m42]; exact w41_68
  have w42_6c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m42]; exact w41_6c
  have w42_70 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m42]; exact w41_70
  have w42_74 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m42]; exact w41_74
  have w42_78 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m42]; exact w41_78
  have w42_7c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m42]; exact w41_7c
  have w42_80 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m42]; exact w41_80
  have w42_84 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m42]; exact w41_84
  have w42_88 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m42]; exact w41_88
  have w42_8c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m42]; exact w41_8c
  have w42_90 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m42]; exact w41_90
  have w42_94 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m42]; exact w41_94
  have w42_a20 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m42]; exact w41_a20
  have w42_a24 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m42]; exact w41_a24
  have w42_a28 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m42]; exact w41_a28
  have w42_a2c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m42]; exact w41_a2c
  have w42_a30 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m42]; exact w41_a30
  have w42_a34 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m42]; exact w41_a34
  have w42_a38 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m42]; exact w41_a38
  have w42_a3c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m42]; exact w41_a3c
  have w42_a40 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m42]; exact w41_a40
  have w42_a44 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m42]; exact w41_a44
  have w42_1020 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m42]; exact w41_1020
  have w42_1024 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m42]; exact w41_1024
  have w42_1028 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m42]; exact w41_1028
  have w42_102c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m42]; exact w41_102c
  have w42_1480 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m42]; exact w41_1480
  have w42_1484 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m42]; exact w41_1484
  have w42_1488 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m42]; exact w41_1488
  have w42_148c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m42]; exact w41_148c
  have b42_1030 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m42]; exact b41_1030
  clear b41_1030 w41_148c w41_1488 w41_1484 w41_1480 w41_102c w41_1028 w41_1024 w41_1020 w41_a44 w41_a40 w41_a3c w41_a38 w41_a34 w41_a30 w41_a2c w41_a28 w41_a24 w41_a20 w41_94 w41_90 w41_8c w41_88 w41_84 w41_80 w41_7c w41_78 w41_74 w41_70 w41_6c w41_68 w41_64 w41_60 w41_5c w41_58 w41_54 w41_50 w41_4c w41_48 w41_40 w41_3c w41_38 w41_34 w41_30 g41_11 g41_27 g41_26 g41_25 g41_23 g41_22 g41_21 g41_19 g41_18 g41_12 g41_10 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 fr41 m41 s41 u41 d41
  -- 0x916: lw
  obtain ⟨n43, d43, u43⟩ := s42.lw E42.self sv_at_916 (off' := 0x91A) (by decide)
    (by rw [g42_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x604 = B + 0x21A0 + BitVec.ofNat 32 0x1024 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s43 : St n43.mem SV n43 0x91A (reg n43) := ⟨u43.pc, rfl, fun _ => rfl⟩
  have m43 : n43.mem = n42.mem := u43.mem
  have fr43 : ∀ x, SvR B x → n43.mem x = n42.mem x := fun x _ => by rw [m43]
  have t43 : Steps n0 n43 := t42.trans (.single d43)
  have fR43 : ∀ x, SvR B x → n43.mem x = M0 x := fun x hx => (fr43 x hx).trans (fR42 x hx)
  have E43 : SvCode n43.mem := E42.fr F fr43
  have V43 : SvSaves B n43.mem v := V42.same m43
  have g43_2 : reg n43 sp = B + 0x21A0 := by rw [u43.regs, upd_ne (by decide) (by decide), g42_2]
  have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u43.regs, upd_ne (by decide) (by decide), g42_3]
  have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u43.regs, upd_ne (by decide) (by decide), g42_4]
  have g43_8 : reg n43 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u43.regs, upd_ne (by decide) (by decide), g42_8]
  have g43_9 : reg n43 (9 : Fin 32) = x9 := by rw [u43.regs, upd_ne (by decide) (by decide), g42_9]
  have g43_10 : reg n43 a0 = (vp) + BitVec.ofNat 32 tl35.header := by rw [u43.regs, upd_ne (by decide) (by decide), g42_10]
  have g43_12 : reg n43 a2 = BitVec.ofNat 32 0xC := by rw [u43.regs, upd_ne (by decide) (by decide), g42_12]
  have g43_18 : reg n43 (18 : Fin 32) = out := by rw [u43.regs, upd_ne (by decide) (by decide), g42_18]
  have g43_19 : reg n43 (19 : Fin 32) = bp := by rw [u43.regs, upd_ne (by decide) (by decide), g42_19]
  have g43_21 : reg n43 (21 : Fin 32) = x21 := by rw [u43.regs, upd_ne (by decide) (by decide), g42_21]
  have g43_22 : reg n43 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u43.regs, upd_ne (by decide) (by decide), g42_22]
  have g43_23 : reg n43 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u43.regs, upd_ne (by decide) (by decide), g42_23]
  have g43_25 : reg n43 (25 : Fin 32) = x25 := by rw [u43.regs, upd_ne (by decide) (by decide), g42_25]
  have g43_26 : reg n43 (26 : Fin 32) = x26 := by rw [u43.regs, upd_ne (by decide) (by decide), g42_26]
  have g43_27 : reg n43 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u43.regs, upd_ne (by decide) (by decide), g42_27]
  have g43_11 : reg n43 a1 = BitVec.ofNat 32 tl35.len := by
    rw [u43.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g42_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x604 = B + 0x21A0 + BitVec.ofNat 32 0x1024 by sv_addr, w42_1024]
  have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := by rw [m43]; exact keep_kk42
  clear keep_kk42
  have w43_30 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m43]; exact w42_30
  have w43_34 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m43]; exact w42_34
  have w43_38 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m43]; exact w42_38
  have w43_3c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m43]; exact w42_3c
  have w43_40 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m43]; exact w42_40
  have w43_48 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m43]; exact w42_48
  have w43_4c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m43]; exact w42_4c
  have w43_50 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m43]; exact w42_50
  have w43_54 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m43]; exact w42_54
  have w43_58 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m43]; exact w42_58
  have w43_5c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m43]; exact w42_5c
  have w43_60 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m43]; exact w42_60
  have w43_64 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m43]; exact w42_64
  have w43_68 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m43]; exact w42_68
  have w43_6c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m43]; exact w42_6c
  have w43_70 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m43]; exact w42_70
  have w43_74 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m43]; exact w42_74
  have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m43]; exact w42_78
  have w43_7c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m43]; exact w42_7c
  have w43_80 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m43]; exact w42_80
  have w43_84 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m43]; exact w42_84
  have w43_88 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m43]; exact w42_88
  have w43_8c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m43]; exact w42_8c
  have w43_90 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m43]; exact w42_90
  have w43_94 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m43]; exact w42_94
  have w43_a20 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m43]; exact w42_a20
  have w43_a24 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m43]; exact w42_a24
  have w43_a28 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m43]; exact w42_a28
  have w43_a2c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m43]; exact w42_a2c
  have w43_a30 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m43]; exact w42_a30
  have w43_a34 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m43]; exact w42_a34
  have w43_a38 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m43]; exact w42_a38
  have w43_a3c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m43]; exact w42_a3c
  have w43_a40 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m43]; exact w42_a40
  have w43_a44 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m43]; exact w42_a44
  have w43_1020 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m43]; exact w42_1020
  have w43_1024 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m43]; exact w42_1024
  have w43_1028 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m43]; exact w42_1028
  have w43_102c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m43]; exact w42_102c
  have w43_1480 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m43]; exact w42_1480
  have w43_1484 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m43]; exact w42_1484
  have w43_1488 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m43]; exact w42_1488
  have w43_148c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m43]; exact w42_148c
  have b43_1030 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m43]; exact b42_1030
  clear b42_1030 w42_148c w42_1488 w42_1484 w42_1480 w42_102c w42_1028 w42_1024 w42_1020 w42_a44 w42_a40 w42_a3c w42_a38 w42_a34 w42_a30 w42_a2c w42_a28 w42_a24 w42_a20 w42_94 w42_90 w42_8c w42_88 w42_84 w42_80 w42_7c w42_78 w42_74 w42_70 w42_6c w42_68 w42_64 w42_60 w42_5c w42_58 w42_54 w42_50 w42_4c w42_48 w42_40 w42_3c w42_38 w42_34 w42_30 g42_27 g42_26 g42_25 g42_23 g42_22 g42_21 g42_19 g42_18 g42_12 g42_11 g42_10 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 m42 s42 u42 d42
  -- 0x91A
  obtain ⟨n44, c44, u44⟩ := s43.block svDp091a E43.self svDp091a_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m44 : n44.mem = n43.mem := u44.mem
  have s44 : St n44.mem SV n44 0x928 (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
  have rb44 : ∀ q, reg n44 q = (runBlock svDp091a (n43.mem, reg n43)).2 q := fun q => by rw [u44.regs]
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
  have g44_8 : reg n44 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb44, runBlock_reg _ _ _ (8 : Fin 32) s43.zero (by decide), g43_8]
  have g44_9 : reg n44 (9 : Fin 32) = x9 := by
    rw [rb44, runBlock_reg _ _ _ (9 : Fin 32) s43.zero (by decide), g43_9]
  have g44_10 : reg n44 a0 = (vp) + BitVec.ofNat 32 tl35.header := by
    rw [rb44, runBlock_reg _ _ _ a0 s43.zero (by decide), g43_10]
  have g44_11 : reg n44 a1 = BitVec.ofNat 32 tl35.len := by
    rw [rb44, runBlock_reg _ _ _ a1 s43.zero (by decide), g43_11]
  have g44_18 : reg n44 (18 : Fin 32) = out := by
    rw [rb44, runBlock_reg _ _ _ (18 : Fin 32) s43.zero (by decide), g43_18]
  have g44_19 : reg n44 (19 : Fin 32) = bp := by
    rw [rb44, runBlock_reg _ _ _ (19 : Fin 32) s43.zero (by decide), g43_19]
  have g44_21 : reg n44 (21 : Fin 32) = x21 := by
    rw [rb44, runBlock_reg _ _ _ (21 : Fin 32) s43.zero (by decide), g43_21]
  have g44_23 : reg n44 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by
    rw [rb44, runBlock_reg _ _ _ (23 : Fin 32) s43.zero (by decide), g43_23]
  have g44_25 : reg n44 (25 : Fin 32) = x25 := by
    rw [rb44, runBlock_reg _ _ _ (25 : Fin 32) s43.zero (by decide), g43_25]
  have g44_26 : reg n44 (26 : Fin 32) = x26 := by
    rw [rb44, runBlock_reg _ _ _ (26 : Fin 32) s43.zero (by decide), g43_26]
  have g44_27 : reg n44 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb44, runBlock_reg _ _ _ (27 : Fin 32) s43.zero (by decide), g43_27]
  have g44_12 : reg n44 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb44]; simp +decide only [runBlock, BInstr.run, svDp091a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_12, g43_18, g43_19, g43_21, g43_22, g43_23, g43_25, g43_26, g43_27, s43.zero])
    all_goals (try simp only [BitVec.reduceToNat, Nat.reduceMod, BitVec.reduceHShiftLeft])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g44_22 : reg n44 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb44]; simp +decide only [runBlock, BInstr.run, svDp091a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_12, g43_18, g43_19, g43_21, g43_22, g43_23, g43_25, g43_26, g43_27, s43.zero])
    all_goals (try simp only [BitVec.reduceToNat, Nat.reduceMod, BitVec.reduceHShiftLeft])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk44 : SvKeepL B n0.mem n44.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8)] := by rw [m44]; exact keep_kk43
  clear keep_kk43
  have w44_30 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m44]; exact w43_30
  have w44_34 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m44]; exact w43_34
  have w44_38 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m44]; exact w43_38
  have w44_3c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m44]; exact w43_3c
  have w44_40 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m44]; exact w43_40
  have w44_48 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m44]; exact w43_48
  have w44_4c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m44]; exact w43_4c
  have w44_50 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m44]; exact w43_50
  have w44_54 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m44]; exact w43_54
  have w44_58 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m44]; exact w43_58
  have w44_5c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m44]; exact w43_5c
  have w44_60 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m44]; exact w43_60
  have w44_64 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m44]; exact w43_64
  have w44_68 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m44]; exact w43_68
  have w44_6c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m44]; exact w43_6c
  have w44_70 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m44]; exact w43_70
  have w44_74 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m44]; exact w43_74
  have w44_78 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m44]; exact w43_78
  have w44_7c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m44]; exact w43_7c
  have w44_80 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m44]; exact w43_80
  have w44_84 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m44]; exact w43_84
  have w44_88 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m44]; exact w43_88
  have w44_8c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m44]; exact w43_8c
  have w44_90 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m44]; exact w43_90
  have w44_94 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m44]; exact w43_94
  have w44_a20 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m44]; exact w43_a20
  have w44_a24 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m44]; exact w43_a24
  have w44_a28 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m44]; exact w43_a28
  have w44_a2c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m44]; exact w43_a2c
  have w44_a30 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m44]; exact w43_a30
  have w44_a34 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m44]; exact w43_a34
  have w44_a38 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m44]; exact w43_a38
  have w44_a3c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m44]; exact w43_a3c
  have w44_a40 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m44]; exact w43_a40
  have w44_a44 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m44]; exact w43_a44
  have w44_1020 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m44]; exact w43_1020
  have w44_1024 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m44]; exact w43_1024
  have w44_1028 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m44]; exact w43_1028
  have w44_102c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m44]; exact w43_102c
  have w44_1480 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m44]; exact w43_1480
  have w44_1484 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m44]; exact w43_1484
  have w44_1488 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m44]; exact w43_1488
  have w44_148c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m44]; exact w43_148c
  have b44_1030 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m44]; exact b43_1030
  clear b43_1030 w43_148c w43_1488 w43_1484 w43_1480 w43_102c w43_1028 w43_1024 w43_1020 w43_a44 w43_a40 w43_a3c w43_a38 w43_a34 w43_a30 w43_a2c w43_a28 w43_a24 w43_a20 w43_94 w43_90 w43_8c w43_88 w43_84 w43_80 w43_7c w43_78 w43_74 w43_70 w43_6c w43_68 w43_64 w43_60 w43_5c w43_58 w43_54 w43_50 w43_4c w43_48 w43_40 w43_3c w43_38 w43_34 w43_30 g43_11 g43_27 g43_26 g43_25 g43_23 g43_22 g43_21 g43_19 g43_18 g43_12 g43_10 g43_9 g43_8 g43_4 g43_3 g43_2 V43 E43 fR43 t43 fr43 m43 s43 u43 d43
  -- 0x928: sw
  obtain ⟨n45, d45, s45, fr45, K45, W45, rg45⟩ := sv_sw F E44 s44 sv_at_928 (off' := 0x92A) (c := 0xA20)
    (by decide) (by rw [g44_12]; sv_addr) (by decide) (by decide)
  have t45 : Steps n0 n45 := t44.trans d45
  have fR45 : ∀ x, SvR B x → n45.mem x = M0 x := fun x hx => (fr45 x hx).trans (fR44 x hx)
  have E45 : SvCode n45.mem := E44.fr F fr45
  have V45 : SvSaves B n45.mem v := V44.keep K45 (by decide)
  have g45_2 : reg n45 sp = B + 0x21A0 := by rw [rg45 sp, g44_2]
  have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg45 (3 : Fin 32), g44_3]
  have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg45 (4 : Fin 32), g44_4]
  have g45_8 : reg n45 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg45 (8 : Fin 32), g44_8]
  have g45_9 : reg n45 (9 : Fin 32) = x9 := by rw [rg45 (9 : Fin 32), g44_9]
  have g45_10 : reg n45 a0 = (vp) + BitVec.ofNat 32 tl35.header := by rw [rg45 a0, g44_10]
  have g45_11 : reg n45 a1 = BitVec.ofNat 32 tl35.len := by rw [rg45 a1, g44_11]
  have g45_12 : reg n45 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg45 a2, g44_12]
  have g45_18 : reg n45 (18 : Fin 32) = out := by rw [rg45 (18 : Fin 32), g44_18]
  have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [rg45 (19 : Fin 32), g44_19]
  have g45_21 : reg n45 (21 : Fin 32) = x21 := by rw [rg45 (21 : Fin 32), g44_21]
  have g45_22 : reg n45 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg45 (22 : Fin 32), g44_22]
  have g45_23 : reg n45 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [rg45 (23 : Fin 32), g44_23]
  have g45_25 : reg n45 (25 : Fin 32) = x25 := by rw [rg45 (25 : Fin 32), g44_25]
  have g45_26 : reg n45 (26 : Fin 32) = x26 := by rw [rg45 (26 : Fin 32), g44_26]
  have g45_27 : reg n45 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg45 (27 : Fin 32), g44_27]
  have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0xA20, 0x4)] := keep_kk44.trans K45.toL
  clear keep_kk44
  have w45_30 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K45.w32 (by decide) (by decide)).trans w44_30
  have w45_34 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K45.w32 (by decide) (by decide)).trans w44_34
  have w45_38 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K45.w32 (by decide) (by decide)).trans w44_38
  have w45_3c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K45.w32 (by decide) (by decide)).trans w44_3c
  have w45_40 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K45.w32 (by decide) (by decide)).trans w44_40
  have w45_48 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K45.w32 (by decide) (by decide)).trans w44_48
  have w45_4c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K45.w32 (by decide) (by decide)).trans w44_4c
  have w45_50 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K45.w32 (by decide) (by decide)).trans w44_50
  have w45_54 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K45.w32 (by decide) (by decide)).trans w44_54
  have w45_58 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K45.w32 (by decide) (by decide)).trans w44_58
  have w45_5c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K45.w32 (by decide) (by decide)).trans w44_5c
  have w45_60 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K45.w32 (by decide) (by decide)).trans w44_60
  have w45_64 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K45.w32 (by decide) (by decide)).trans w44_64
  have w45_68 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K45.w32 (by decide) (by decide)).trans w44_68
  have w45_6c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K45.w32 (by decide) (by decide)).trans w44_6c
  have w45_70 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K45.w32 (by decide) (by decide)).trans w44_70
  have w45_74 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K45.w32 (by decide) (by decide)).trans w44_74
  have w45_78 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K45.w32 (by decide) (by decide)).trans w44_78
  have w45_7c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K45.w32 (by decide) (by decide)).trans w44_7c
  have w45_80 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K45.w32 (by decide) (by decide)).trans w44_80
  have w45_84 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K45.w32 (by decide) (by decide)).trans w44_84
  have w45_88 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K45.w32 (by decide) (by decide)).trans w44_88
  have w45_8c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K45.w32 (by decide) (by decide)).trans w44_8c
  have w45_90 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K45.w32 (by decide) (by decide)).trans w44_90
  have w45_94 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K45.w32 (by decide) (by decide)).trans w44_94
  have w45_a24 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K45.w32 (by decide) (by decide)).trans w44_a24
  have w45_a28 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K45.w32 (by decide) (by decide)).trans w44_a28
  have w45_a2c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K45.w32 (by decide) (by decide)).trans w44_a2c
  have w45_a30 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K45.w32 (by decide) (by decide)).trans w44_a30
  have w45_a34 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K45.w32 (by decide) (by decide)).trans w44_a34
  have w45_a38 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K45.w32 (by decide) (by decide)).trans w44_a38
  have w45_a3c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K45.w32 (by decide) (by decide)).trans w44_a3c
  have w45_a40 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K45.w32 (by decide) (by decide)).trans w44_a40
  have w45_a44 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K45.w32 (by decide) (by decide)).trans w44_a44
  have w45_1020 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := (K45.w32 (by decide) (by decide)).trans w44_1020
  have w45_1024 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := (K45.w32 (by decide) (by decide)).trans w44_1024
  have w45_1028 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := (K45.w32 (by decide) (by decide)).trans w44_1028
  have w45_102c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := (K45.w32 (by decide) (by decide)).trans w44_102c
  have w45_1480 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K45.w32 (by decide) (by decide)).trans w44_1480
  have w45_1484 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K45.w32 (by decide) (by decide)).trans w44_1484
  have w45_1488 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := (K45.w32 (by decide) (by decide)).trans w44_1488
  have w45_148c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := (K45.w32 (by decide) (by decide)).trans w44_148c
  have b45_1030 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := (K45.b8 (by decide) (by decide)).trans b44_1030
  have w45_a20 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (vp) + BitVec.ofNat 32 tl35.header := by rw [W45, g44_10]
  clear b44_1030 w44_148c w44_1488 w44_1484 w44_1480 w44_102c w44_1028 w44_1024 w44_1020 w44_a44 w44_a40 w44_a3c w44_a38 w44_a34 w44_a30 w44_a2c w44_a28 w44_a24 w44_a20 w44_94 w44_90 w44_8c w44_88 w44_84 w44_80 w44_7c w44_78 w44_74 w44_70 w44_6c w44_68 w44_64 w44_60 w44_5c w44_58 w44_54 w44_50 w44_4c w44_48 w44_40 w44_3c w44_38 w44_34 w44_30 g44_22 g44_12 g44_27 g44_26 g44_25 g44_23 g44_21 g44_19 g44_18 g44_11 g44_10 g44_9 g44_8 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 rb44 s44 m44 u44 c44
  -- 0x92A: sw
  obtain ⟨n46, d46, s46, fr46, K46, W46, rg46⟩ := sv_sw F E45 s45 sv_at_92a (off' := 0x92C) (c := 0xA24)
    (by decide) (by rw [g45_12]; sv_addr) (by decide) (by decide)
  have t46 : Steps n0 n46 := t45.trans d46
  have fR46 : ∀ x, SvR B x → n46.mem x = M0 x := fun x hx => (fr46 x hx).trans (fR45 x hx)
  have E46 : SvCode n46.mem := E45.fr F fr46
  have V46 : SvSaves B n46.mem v := V45.keep K46 (by decide)
  have g46_2 : reg n46 sp = B + 0x21A0 := by rw [rg46 sp, g45_2]
  have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg46 (3 : Fin 32), g45_3]
  have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg46 (4 : Fin 32), g45_4]
  have g46_8 : reg n46 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg46 (8 : Fin 32), g45_8]
  have g46_9 : reg n46 (9 : Fin 32) = x9 := by rw [rg46 (9 : Fin 32), g45_9]
  have g46_10 : reg n46 a0 = (vp) + BitVec.ofNat 32 tl35.header := by rw [rg46 a0, g45_10]
  have g46_11 : reg n46 a1 = BitVec.ofNat 32 tl35.len := by rw [rg46 a1, g45_11]
  have g46_12 : reg n46 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg46 a2, g45_12]
  have g46_18 : reg n46 (18 : Fin 32) = out := by rw [rg46 (18 : Fin 32), g45_18]
  have g46_19 : reg n46 (19 : Fin 32) = bp := by rw [rg46 (19 : Fin 32), g45_19]
  have g46_21 : reg n46 (21 : Fin 32) = x21 := by rw [rg46 (21 : Fin 32), g45_21]
  have g46_22 : reg n46 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg46 (22 : Fin 32), g45_22]
  have g46_23 : reg n46 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [rg46 (23 : Fin 32), g45_23]
  have g46_25 : reg n46 (25 : Fin 32) = x25 := by rw [rg46 (25 : Fin 32), g45_25]
  have g46_26 : reg n46 (26 : Fin 32) = x26 := by rw [rg46 (26 : Fin 32), g45_26]
  have g46_27 : reg n46 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg46 (27 : Fin 32), g45_27]
  have keep_kk46 : SvKeepL B n0.mem n46.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0xA20, 0x4), (0xA24, 0x4)] := keep_kk45.trans K46.toL
  clear keep_kk45
  have w46_30 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K46.w32 (by decide) (by decide)).trans w45_30
  have w46_34 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K46.w32 (by decide) (by decide)).trans w45_34
  have w46_38 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K46.w32 (by decide) (by decide)).trans w45_38
  have w46_3c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K46.w32 (by decide) (by decide)).trans w45_3c
  have w46_40 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K46.w32 (by decide) (by decide)).trans w45_40
  have w46_48 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K46.w32 (by decide) (by decide)).trans w45_48
  have w46_4c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K46.w32 (by decide) (by decide)).trans w45_4c
  have w46_50 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K46.w32 (by decide) (by decide)).trans w45_50
  have w46_54 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K46.w32 (by decide) (by decide)).trans w45_54
  have w46_58 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K46.w32 (by decide) (by decide)).trans w45_58
  have w46_5c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K46.w32 (by decide) (by decide)).trans w45_5c
  have w46_60 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K46.w32 (by decide) (by decide)).trans w45_60
  have w46_64 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K46.w32 (by decide) (by decide)).trans w45_64
  have w46_68 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K46.w32 (by decide) (by decide)).trans w45_68
  have w46_6c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K46.w32 (by decide) (by decide)).trans w45_6c
  have w46_70 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K46.w32 (by decide) (by decide)).trans w45_70
  have w46_74 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K46.w32 (by decide) (by decide)).trans w45_74
  have w46_78 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K46.w32 (by decide) (by decide)).trans w45_78
  have w46_7c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K46.w32 (by decide) (by decide)).trans w45_7c
  have w46_80 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K46.w32 (by decide) (by decide)).trans w45_80
  have w46_84 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K46.w32 (by decide) (by decide)).trans w45_84
  have w46_88 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K46.w32 (by decide) (by decide)).trans w45_88
  have w46_8c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K46.w32 (by decide) (by decide)).trans w45_8c
  have w46_90 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K46.w32 (by decide) (by decide)).trans w45_90
  have w46_94 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K46.w32 (by decide) (by decide)).trans w45_94
  have w46_a20 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (vp) + BitVec.ofNat 32 tl35.header := (K46.w32 (by decide) (by decide)).trans w45_a20
  have w46_a28 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K46.w32 (by decide) (by decide)).trans w45_a28
  have w46_a2c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K46.w32 (by decide) (by decide)).trans w45_a2c
  have w46_a30 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K46.w32 (by decide) (by decide)).trans w45_a30
  have w46_a34 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K46.w32 (by decide) (by decide)).trans w45_a34
  have w46_a38 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K46.w32 (by decide) (by decide)).trans w45_a38
  have w46_a3c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K46.w32 (by decide) (by decide)).trans w45_a3c
  have w46_a40 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K46.w32 (by decide) (by decide)).trans w45_a40
  have w46_a44 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K46.w32 (by decide) (by decide)).trans w45_a44
  have w46_1020 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := (K46.w32 (by decide) (by decide)).trans w45_1020
  have w46_1024 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := (K46.w32 (by decide) (by decide)).trans w45_1024
  have w46_1028 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := (K46.w32 (by decide) (by decide)).trans w45_1028
  have w46_102c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := (K46.w32 (by decide) (by decide)).trans w45_102c
  have w46_1480 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K46.w32 (by decide) (by decide)).trans w45_1480
  have w46_1484 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K46.w32 (by decide) (by decide)).trans w45_1484
  have w46_1488 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := (K46.w32 (by decide) (by decide)).trans w45_1488
  have w46_148c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := (K46.w32 (by decide) (by decide)).trans w45_148c
  have b46_1030 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := (K46.b8 (by decide) (by decide)).trans b45_1030
  have w46_a24 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl35.len := by rw [W46, g45_11]
  clear w45_a20 b45_1030 w45_148c w45_1488 w45_1484 w45_1480 w45_102c w45_1028 w45_1024 w45_1020 w45_a44 w45_a40 w45_a3c w45_a38 w45_a34 w45_a30 w45_a2c w45_a28 w45_a24 w45_94 w45_90 w45_8c w45_88 w45_84 w45_80 w45_7c w45_78 w45_74 w45_70 w45_6c w45_68 w45_64 w45_60 w45_5c w45_58 w45_54 w45_50 w45_4c w45_48 w45_40 w45_3c w45_38 w45_34 w45_30 g45_27 g45_26 g45_25 g45_23 g45_22 g45_21 g45_19 g45_18 g45_12 g45_11 g45_10 g45_9 g45_8 g45_4 g45_3 g45_2 V45 E45 fR45 t45 rg45 W45 K45 fr45 s45 d45
  -- 0x92C: j
  obtain ⟨n47, d47, u47⟩ := s46.jump E46.self sv_at_92c (off' := 0x95C) (by decide)
    (by rw [s46.pc]; decide)
  have s47 : St n47.mem SV n47 0x95C (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
  have m47 : n47.mem = n46.mem := u47.mem
  have fr47 : ∀ x, SvR B x → n47.mem x = n46.mem x := fun x _ => by rw [m47]
  have t47 : Steps n0 n47 := t46.trans (.single d47)
  have fR47 : ∀ x, SvR B x → n47.mem x = M0 x := fun x hx => (fr47 x hx).trans (fR46 x hx)
  have E47 : SvCode n47.mem := E46.fr F fr47
  have V47 : SvSaves B n47.mem v := V46.same m47
  have g47_2 : reg n47 sp = B + 0x21A0 := by rw [u47.regs, g46_2]
  have g47_3 : reg n47 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u47.regs, g46_3]
  have g47_4 : reg n47 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u47.regs, g46_4]
  have g47_8 : reg n47 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u47.regs, g46_8]
  have g47_9 : reg n47 (9 : Fin 32) = x9 := by rw [u47.regs, g46_9]
  have g47_10 : reg n47 a0 = (vp) + BitVec.ofNat 32 tl35.header := by rw [u47.regs, g46_10]
  have g47_11 : reg n47 a1 = BitVec.ofNat 32 tl35.len := by rw [u47.regs, g46_11]
  have g47_12 : reg n47 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u47.regs, g46_12]
  have g47_18 : reg n47 (18 : Fin 32) = out := by rw [u47.regs, g46_18]
  have g47_19 : reg n47 (19 : Fin 32) = bp := by rw [u47.regs, g46_19]
  have g47_21 : reg n47 (21 : Fin 32) = x21 := by rw [u47.regs, g46_21]
  have g47_22 : reg n47 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u47.regs, g46_22]
  have g47_23 : reg n47 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u47.regs, g46_23]
  have g47_25 : reg n47 (25 : Fin 32) = x25 := by rw [u47.regs, g46_25]
  have g47_26 : reg n47 (26 : Fin 32) = x26 := by rw [u47.regs, g46_26]
  have g47_27 : reg n47 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u47.regs, g46_27]
  have keep_kk47 : SvKeepL B n0.mem n47.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0xA20, 0x4), (0xA24, 0x4)] := by rw [m47]; exact keep_kk46
  clear keep_kk46
  have w47_30 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m47]; exact w46_30
  have w47_34 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m47]; exact w46_34
  have w47_38 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m47]; exact w46_38
  have w47_3c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m47]; exact w46_3c
  have w47_40 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m47]; exact w46_40
  have w47_48 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m47]; exact w46_48
  have w47_4c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m47]; exact w46_4c
  have w47_50 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m47]; exact w46_50
  have w47_54 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m47]; exact w46_54
  have w47_58 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m47]; exact w46_58
  have w47_5c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m47]; exact w46_5c
  have w47_60 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m47]; exact w46_60
  have w47_64 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m47]; exact w46_64
  have w47_68 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m47]; exact w46_68
  have w47_6c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m47]; exact w46_6c
  have w47_70 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m47]; exact w46_70
  have w47_74 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m47]; exact w46_74
  have w47_78 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m47]; exact w46_78
  have w47_7c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m47]; exact w46_7c
  have w47_80 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m47]; exact w46_80
  have w47_84 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m47]; exact w46_84
  have w47_88 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m47]; exact w46_88
  have w47_8c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m47]; exact w46_8c
  have w47_90 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m47]; exact w46_90
  have w47_94 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m47]; exact w46_94
  have w47_a20 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m47]; exact w46_a20
  have w47_a24 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl35.len := by rw [m47]; exact w46_a24
  have w47_a28 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m47]; exact w46_a28
  have w47_a2c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m47]; exact w46_a2c
  have w47_a30 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m47]; exact w46_a30
  have w47_a34 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m47]; exact w46_a34
  have w47_a38 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m47]; exact w46_a38
  have w47_a3c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m47]; exact w46_a3c
  have w47_a40 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m47]; exact w46_a40
  have w47_a44 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m47]; exact w46_a44
  have w47_1020 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m47]; exact w46_1020
  have w47_1024 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m47]; exact w46_1024
  have w47_1028 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m47]; exact w46_1028
  have w47_102c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m47]; exact w46_102c
  have w47_1480 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m47]; exact w46_1480
  have w47_1484 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m47]; exact w46_1484
  have w47_1488 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m47]; exact w46_1488
  have w47_148c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m47]; exact w46_148c
  have b47_1030 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m47]; exact b46_1030
  clear w46_a24 b46_1030 w46_148c w46_1488 w46_1484 w46_1480 w46_102c w46_1028 w46_1024 w46_1020 w46_a44 w46_a40 w46_a3c w46_a38 w46_a34 w46_a30 w46_a2c w46_a28 w46_a20 w46_94 w46_90 w46_8c w46_88 w46_84 w46_80 w46_7c w46_78 w46_74 w46_70 w46_6c w46_68 w46_64 w46_60 w46_5c w46_58 w46_54 w46_50 w46_4c w46_48 w46_40 w46_3c w46_38 w46_34 w46_30 g46_27 g46_26 g46_25 g46_23 g46_22 g46_21 g46_19 g46_18 g46_12 g46_11 g46_10 g46_9 g46_8 g46_4 g46_3 g46_2 V46 E46 fR46 t46 rg46 W46 K46 fr46 s46 d46
  -- 0x95C: lw
  obtain ⟨n48, d48, u48⟩ := s47.lw E47.self sv_at_95c (off' := 0x95E) (by decide)
    (by rw [g47_2, show B + 0x21A0 + 0x94 = B + 0x21A0 + BitVec.ofNat 32 0x94 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s48 : St n48.mem SV n48 0x95E (reg n48) := ⟨u48.pc, rfl, fun _ => rfl⟩
  have m48 : n48.mem = n47.mem := u48.mem
  have fr48 : ∀ x, SvR B x → n48.mem x = n47.mem x := fun x _ => by rw [m48]
  have t48 : Steps n0 n48 := t47.trans (.single d48)
  have fR48 : ∀ x, SvR B x → n48.mem x = M0 x := fun x hx => (fr48 x hx).trans (fR47 x hx)
  have E48 : SvCode n48.mem := E47.fr F fr48
  have V48 : SvSaves B n48.mem v := V47.same m48
  have g48_2 : reg n48 sp = B + 0x21A0 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_2]
  have g48_3 : reg n48 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u48.regs, upd_ne (by decide) (by decide), g47_3]
  have g48_4 : reg n48 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u48.regs, upd_ne (by decide) (by decide), g47_4]
  have g48_8 : reg n48 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_8]
  have g48_9 : reg n48 (9 : Fin 32) = x9 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_9]
  have g48_11 : reg n48 a1 = BitVec.ofNat 32 tl35.len := by rw [u48.regs, upd_ne (by decide) (by decide), g47_11]
  have g48_12 : reg n48 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_12]
  have g48_18 : reg n48 (18 : Fin 32) = out := by rw [u48.regs, upd_ne (by decide) (by decide), g47_18]
  have g48_19 : reg n48 (19 : Fin 32) = bp := by rw [u48.regs, upd_ne (by decide) (by decide), g47_19]
  have g48_21 : reg n48 (21 : Fin 32) = x21 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_21]
  have g48_22 : reg n48 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_22]
  have g48_23 : reg n48 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_23]
  have g48_25 : reg n48 (25 : Fin 32) = x25 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_25]
  have g48_26 : reg n48 (26 : Fin 32) = x26 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_26]
  have g48_27 : reg n48 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_27]
  have g48_10 : reg n48 a0 = rest := by
    rw [u48.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g47_2, show B + 0x21A0 + 0x94 = B + 0x21A0 + BitVec.ofNat 32 0x94 by sv_addr, w47_94]
  have keep_kk48 : SvKeepL B n0.mem n48.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0xA20, 0x4), (0xA24, 0x4)] := by rw [m48]; exact keep_kk47
  clear keep_kk47
  have w48_30 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m48]; exact w47_30
  have w48_34 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m48]; exact w47_34
  have w48_38 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m48]; exact w47_38
  have w48_3c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m48]; exact w47_3c
  have w48_40 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m48]; exact w47_40
  have w48_48 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m48]; exact w47_48
  have w48_4c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m48]; exact w47_4c
  have w48_50 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m48]; exact w47_50
  have w48_54 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m48]; exact w47_54
  have w48_58 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m48]; exact w47_58
  have w48_5c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m48]; exact w47_5c
  have w48_60 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m48]; exact w47_60
  have w48_64 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m48]; exact w47_64
  have w48_68 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m48]; exact w47_68
  have w48_6c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m48]; exact w47_6c
  have w48_70 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m48]; exact w47_70
  have w48_74 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m48]; exact w47_74
  have w48_78 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m48]; exact w47_78
  have w48_7c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m48]; exact w47_7c
  have w48_80 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m48]; exact w47_80
  have w48_84 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m48]; exact w47_84
  have w48_88 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m48]; exact w47_88
  have w48_8c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m48]; exact w47_8c
  have w48_90 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m48]; exact w47_90
  have w48_94 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m48]; exact w47_94
  have w48_a20 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m48]; exact w47_a20
  have w48_a24 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl35.len := by rw [m48]; exact w47_a24
  have w48_a28 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m48]; exact w47_a28
  have w48_a2c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m48]; exact w47_a2c
  have w48_a30 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m48]; exact w47_a30
  have w48_a34 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m48]; exact w47_a34
  have w48_a38 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m48]; exact w47_a38
  have w48_a3c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m48]; exact w47_a3c
  have w48_a40 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m48]; exact w47_a40
  have w48_a44 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m48]; exact w47_a44
  have w48_1020 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m48]; exact w47_1020
  have w48_1024 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m48]; exact w47_1024
  have w48_1028 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m48]; exact w47_1028
  have w48_102c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m48]; exact w47_102c
  have w48_1480 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m48]; exact w47_1480
  have w48_1484 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m48]; exact w47_1484
  have w48_1488 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m48]; exact w47_1488
  have w48_148c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m48]; exact w47_148c
  have b48_1030 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m48]; exact b47_1030
  clear b47_1030 w47_148c w47_1488 w47_1484 w47_1480 w47_102c w47_1028 w47_1024 w47_1020 w47_a44 w47_a40 w47_a3c w47_a38 w47_a34 w47_a30 w47_a2c w47_a28 w47_a24 w47_a20 w47_94 w47_90 w47_8c w47_88 w47_84 w47_80 w47_7c w47_78 w47_74 w47_70 w47_6c w47_68 w47_64 w47_60 w47_5c w47_58 w47_54 w47_50 w47_4c w47_48 w47_40 w47_3c w47_38 w47_34 w47_30 g47_27 g47_26 g47_25 g47_23 g47_22 g47_21 g47_19 g47_18 g47_12 g47_11 g47_10 g47_9 g47_8 g47_4 g47_3 g47_2 V47 E47 fR47 t47 fr47 m47 s47 u47 d47
  -- 0x95E: sw
  obtain ⟨n49, d49, s49, fr49, K49, W49, rg49⟩ := sv_sw F E48 s48 sv_at_95e (off' := 0x960) (c := 0x40)
    (by decide) (by rw [g48_2]; sv_addr) (by decide) (by decide)
  have t49 : Steps n0 n49 := t48.trans d49
  have fR49 : ∀ x, SvR B x → n49.mem x = M0 x := fun x hx => (fr49 x hx).trans (fR48 x hx)
  have E49 : SvCode n49.mem := E48.fr F fr49
  have V49 : SvSaves B n49.mem v := V48.keep K49 (by decide)
  have g49_2 : reg n49 sp = B + 0x21A0 := by rw [rg49 sp, g48_2]
  have g49_3 : reg n49 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg49 (3 : Fin 32), g48_3]
  have g49_4 : reg n49 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg49 (4 : Fin 32), g48_4]
  have g49_8 : reg n49 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg49 (8 : Fin 32), g48_8]
  have g49_9 : reg n49 (9 : Fin 32) = x9 := by rw [rg49 (9 : Fin 32), g48_9]
  have g49_10 : reg n49 a0 = rest := by rw [rg49 a0, g48_10]
  have g49_11 : reg n49 a1 = BitVec.ofNat 32 tl35.len := by rw [rg49 a1, g48_11]
  have g49_12 : reg n49 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg49 a2, g48_12]
  have g49_18 : reg n49 (18 : Fin 32) = out := by rw [rg49 (18 : Fin 32), g48_18]
  have g49_19 : reg n49 (19 : Fin 32) = bp := by rw [rg49 (19 : Fin 32), g48_19]
  have g49_21 : reg n49 (21 : Fin 32) = x21 := by rw [rg49 (21 : Fin 32), g48_21]
  have g49_22 : reg n49 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg49 (22 : Fin 32), g48_22]
  have g49_23 : reg n49 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [rg49 (23 : Fin 32), g48_23]
  have g49_25 : reg n49 (25 : Fin 32) = x25 := by rw [rg49 (25 : Fin 32), g48_25]
  have g49_26 : reg n49 (26 : Fin 32) = x26 := by rw [rg49 (26 : Fin 32), g48_26]
  have g49_27 : reg n49 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg49 (27 : Fin 32), g48_27]
  have keep_kk49 : SvKeepL B n0.mem n49.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0xA20, 0x4), (0xA24, 0x4), (0x40, 0x4)] := keep_kk48.trans K49.toL
  clear keep_kk48
  have w49_30 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K49.w32 (by decide) (by decide)).trans w48_30
  have w49_34 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K49.w32 (by decide) (by decide)).trans w48_34
  have w49_38 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K49.w32 (by decide) (by decide)).trans w48_38
  have w49_3c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K49.w32 (by decide) (by decide)).trans w48_3c
  have w49_48 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K49.w32 (by decide) (by decide)).trans w48_48
  have w49_4c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K49.w32 (by decide) (by decide)).trans w48_4c
  have w49_50 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K49.w32 (by decide) (by decide)).trans w48_50
  have w49_54 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K49.w32 (by decide) (by decide)).trans w48_54
  have w49_58 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K49.w32 (by decide) (by decide)).trans w48_58
  have w49_5c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K49.w32 (by decide) (by decide)).trans w48_5c
  have w49_60 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K49.w32 (by decide) (by decide)).trans w48_60
  have w49_64 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K49.w32 (by decide) (by decide)).trans w48_64
  have w49_68 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K49.w32 (by decide) (by decide)).trans w48_68
  have w49_6c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K49.w32 (by decide) (by decide)).trans w48_6c
  have w49_70 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K49.w32 (by decide) (by decide)).trans w48_70
  have w49_74 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K49.w32 (by decide) (by decide)).trans w48_74
  have w49_78 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K49.w32 (by decide) (by decide)).trans w48_78
  have w49_7c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K49.w32 (by decide) (by decide)).trans w48_7c
  have w49_80 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K49.w32 (by decide) (by decide)).trans w48_80
  have w49_84 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K49.w32 (by decide) (by decide)).trans w48_84
  have w49_88 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K49.w32 (by decide) (by decide)).trans w48_88
  have w49_8c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K49.w32 (by decide) (by decide)).trans w48_8c
  have w49_90 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K49.w32 (by decide) (by decide)).trans w48_90
  have w49_94 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K49.w32 (by decide) (by decide)).trans w48_94
  have w49_a20 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (vp) + BitVec.ofNat 32 tl35.header := (K49.w32 (by decide) (by decide)).trans w48_a20
  have w49_a24 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl35.len := (K49.w32 (by decide) (by decide)).trans w48_a24
  have w49_a28 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K49.w32 (by decide) (by decide)).trans w48_a28
  have w49_a2c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K49.w32 (by decide) (by decide)).trans w48_a2c
  have w49_a30 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K49.w32 (by decide) (by decide)).trans w48_a30
  have w49_a34 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K49.w32 (by decide) (by decide)).trans w48_a34
  have w49_a38 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K49.w32 (by decide) (by decide)).trans w48_a38
  have w49_a3c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K49.w32 (by decide) (by decide)).trans w48_a3c
  have w49_a40 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K49.w32 (by decide) (by decide)).trans w48_a40
  have w49_a44 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K49.w32 (by decide) (by decide)).trans w48_a44
  have w49_1020 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := (K49.w32 (by decide) (by decide)).trans w48_1020
  have w49_1024 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := (K49.w32 (by decide) (by decide)).trans w48_1024
  have w49_1028 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := (K49.w32 (by decide) (by decide)).trans w48_1028
  have w49_102c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := (K49.w32 (by decide) (by decide)).trans w48_102c
  have w49_1480 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K49.w32 (by decide) (by decide)).trans w48_1480
  have w49_1484 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K49.w32 (by decide) (by decide)).trans w48_1484
  have w49_1488 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := (K49.w32 (by decide) (by decide)).trans w48_1488
  have w49_148c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := (K49.w32 (by decide) (by decide)).trans w48_148c
  have b49_1030 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := (K49.b8 (by decide) (by decide)).trans b48_1030
  have w49_40 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rest := by rw [W49, g48_10]
  clear b48_1030 w48_148c w48_1488 w48_1484 w48_1480 w48_102c w48_1028 w48_1024 w48_1020 w48_a44 w48_a40 w48_a3c w48_a38 w48_a34 w48_a30 w48_a2c w48_a28 w48_a24 w48_a20 w48_94 w48_90 w48_8c w48_88 w48_84 w48_80 w48_7c w48_78 w48_74 w48_70 w48_6c w48_68 w48_64 w48_60 w48_5c w48_58 w48_54 w48_50 w48_4c w48_48 w48_40 w48_3c w48_38 w48_34 w48_30 g48_10 g48_27 g48_26 g48_25 g48_23 g48_22 g48_21 g48_19 g48_18 g48_12 g48_11 g48_9 g48_8 g48_4 g48_3 g48_2 V48 E48 fR48 t48 fr48 m48 s48 u48 d48
  -- 0x960: j
  obtain ⟨n50, d50, u50⟩ := s49.jump E49.self sv_at_960 (off' := 0x4EA) (by decide)
    (by rw [s49.pc]; decide)
  have s50 : St n50.mem SV n50 0x4EA (reg n50) := ⟨u50.pc, rfl, fun _ => rfl⟩
  have m50 : n50.mem = n49.mem := u50.mem
  have fr50 : ∀ x, SvR B x → n50.mem x = n49.mem x := fun x _ => by rw [m50]
  have t50 : Steps n0 n50 := t49.trans (.single d50)
  have fR50 : ∀ x, SvR B x → n50.mem x = M0 x := fun x hx => (fr50 x hx).trans (fR49 x hx)
  have E50 : SvCode n50.mem := E49.fr F fr50
  have V50 : SvSaves B n50.mem v := V49.same m50
  have g50_2 : reg n50 sp = B + 0x21A0 := by rw [u50.regs, g49_2]
  have g50_3 : reg n50 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u50.regs, g49_3]
  have g50_4 : reg n50 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u50.regs, g49_4]
  have g50_8 : reg n50 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u50.regs, g49_8]
  have g50_9 : reg n50 (9 : Fin 32) = x9 := by rw [u50.regs, g49_9]
  have g50_10 : reg n50 a0 = rest := by rw [u50.regs, g49_10]
  have g50_11 : reg n50 a1 = BitVec.ofNat 32 tl35.len := by rw [u50.regs, g49_11]
  have g50_12 : reg n50 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u50.regs, g49_12]
  have g50_18 : reg n50 (18 : Fin 32) = out := by rw [u50.regs, g49_18]
  have g50_19 : reg n50 (19 : Fin 32) = bp := by rw [u50.regs, g49_19]
  have g50_21 : reg n50 (21 : Fin 32) = x21 := by rw [u50.regs, g49_21]
  have g50_22 : reg n50 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u50.regs, g49_22]
  have g50_23 : reg n50 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u50.regs, g49_23]
  have g50_25 : reg n50 (25 : Fin 32) = x25 := by rw [u50.regs, g49_25]
  have g50_26 : reg n50 (26 : Fin 32) = x26 := by rw [u50.regs, g49_26]
  have g50_27 : reg n50 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u50.regs, g49_27]
  have keep_kk50 : SvKeepL B n0.mem n50.mem [(0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0xA20, 0x4), (0xA24, 0x4), (0x40, 0x4)] := by rw [m50]; exact keep_kk49
  clear keep_kk49
  have w50_30 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m50]; exact w49_30
  have w50_34 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m50]; exact w49_34
  have w50_38 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m50]; exact w49_38
  have w50_3c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m50]; exact w49_3c
  have w50_40 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rest := by rw [m50]; exact w49_40
  have w50_48 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m50]; exact w49_48
  have w50_4c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m50]; exact w49_4c
  have w50_50 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m50]; exact w49_50
  have w50_54 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m50]; exact w49_54
  have w50_58 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m50]; exact w49_58
  have w50_5c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m50]; exact w49_5c
  have w50_60 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m50]; exact w49_60
  have w50_64 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m50]; exact w49_64
  have w50_68 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m50]; exact w49_68
  have w50_6c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m50]; exact w49_6c
  have w50_70 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m50]; exact w49_70
  have w50_74 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m50]; exact w49_74
  have w50_78 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m50]; exact w49_78
  have w50_7c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m50]; exact w49_7c
  have w50_80 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m50]; exact w49_80
  have w50_84 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m50]; exact w49_84
  have w50_88 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m50]; exact w49_88
  have w50_8c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m50]; exact w49_8c
  have w50_90 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m50]; exact w49_90
  have w50_94 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m50]; exact w49_94
  have w50_a20 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m50]; exact w49_a20
  have w50_a24 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl35.len := by rw [m50]; exact w49_a24
  have w50_a28 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m50]; exact w49_a28
  have w50_a2c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m50]; exact w49_a2c
  have w50_a30 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m50]; exact w49_a30
  have w50_a34 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m50]; exact w49_a34
  have w50_a38 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m50]; exact w49_a38
  have w50_a3c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m50]; exact w49_a3c
  have w50_a40 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m50]; exact w49_a40
  have w50_a44 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m50]; exact w49_a44
  have w50_1020 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl35.header := by rw [m50]; exact w49_1020
  have w50_1024 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl35.len := by rw [m50]; exact w49_1024
  have w50_1028 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m50]; exact w49_1028
  have w50_102c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m50]; exact w49_102c
  have w50_1480 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m50]; exact w49_1480
  have w50_1484 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m50]; exact w49_1484
  have w50_1488 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m50]; exact w49_1488
  have w50_148c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl35.header + tl35.len) := by rw [m50]; exact w49_148c
  have b50_1030 : n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl35.tag := by rw [m50]; exact b49_1030
  clear w49_40 b49_1030 w49_148c w49_1488 w49_1484 w49_1480 w49_102c w49_1028 w49_1024 w49_1020 w49_a44 w49_a40 w49_a3c w49_a38 w49_a34 w49_a30 w49_a2c w49_a28 w49_a24 w49_a20 w49_94 w49_90 w49_8c w49_88 w49_84 w49_80 w49_7c w49_78 w49_74 w49_70 w49_6c w49_68 w49_64 w49_60 w49_5c w49_58 w49_54 w49_50 w49_4c w49_48 w49_3c w49_38 w49_34 w49_30 g49_27 g49_26 g49_25 g49_23 g49_22 g49_21 g49_19 g49_18 g49_12 g49_11 g49_10 g49_9 g49_8 g49_4 g49_3 g49_2 V49 E49 fR49 t49 rg49 W49 K49 fr49 s49 d49
  exact .inr ⟨tl35, hr35, hz_39, hz_41, n50, t50, s50, E50, V50, fR50, g50_2, g50_3, g50_4, g50_9, g50_18, g50_19, g50_21, g50_25, g50_26, g50_27, w50_30, w50_34, w50_40, w50_4c, w50_50, w50_54, w50_58, w50_5c, w50_60, w50_64, w50_68, w50_6c, w50_70, w50_74, w50_78, w50_7c, w50_80, w50_84, w50_88, w50_8c, w50_90, w50_94, w50_a20, w50_a24, w50_a28, w50_a2c, w50_a30, w50_a34, w50_a38, w50_a3c, w50_a40, w50_a44, keep_kk50.mono (by decide)⟩

end C3.RV32.Sv
