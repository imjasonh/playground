import C3BootProofs.Proofs.SvData

/-!
# `sigstore::verify`: an extension with policy OID 1

From the OID tests at 0x60E back to the loop head at 0x4EA, for an extension with policy OID 1: its value must be one `UTF8String`, which fills policy slot 1.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svDp160e : List BInstr :=
  [.aluImm .add a3 x0 0x3, .alu .add a0 x0 (8 : Fin 32)]
set_option maxRecDepth 100000 in
theorem svDp160e_end : blockEnd sigstoreVerifyCode 0x60E svDp160e = some 0x612 := by decide

def svDp1614 : List BInstr :=
  [.lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF889]
set_option maxRecDepth 100000 in
theorem svDp1614_end : blockEnd sigstoreVerifyCode 0x614 svDp1614 = some 0x61C := by decide

def svDp16bc : List BInstr :=
  [.aluImm .add a3 x0 0x3, .alu .add a0 x0 (8 : Fin 32)]
set_option maxRecDepth 100000 in
theorem svDp16bc_end : blockEnd sigstoreVerifyCode 0x6BC svDp16bc = some 0x6C0 := by decide

def svDp16c2 : List BInstr :=
  [.lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF892]
set_option maxRecDepth 100000 in
theorem svDp16c2_end : blockEnd sigstoreVerifyCode 0x6C2 svDp16c2 = some 0x6CA := by decide

def svDp178e : List BInstr :=
  [.aluImm .add a3 x0 0x3, .alu .add a0 x0 (8 : Fin 32)]
set_option maxRecDepth 100000 in
theorem svDp178e_end : blockEnd sigstoreVerifyCode 0x78E svDp178e = some 0x792 := by decide

def svDp1794 : List BInstr :=
  [.lui a2 0x3FCC5000, .aluImm .add a2 a2 0xFFFFF88F]
set_option maxRecDepth 100000 in
theorem svDp1794_end : blockEnd sigstoreVerifyCode 0x794 svDp1794 = some 0x79C := by decide

def svDp189c : List BInstr :=
  [.aluImm .add (22 : Fin 32) x0 0xFFFFFFFF, .lui (23 : Fin 32) 0x3FCC5000, .aluImm .add (23 : Fin 32) (23 : Fin 32) 0xFFFFF8EC]
set_option maxRecDepth 100000 in
theorem svDp189c_end : blockEnd sigstoreVerifyCode 0x89C svDp189c = some 0x8A6 := by decide

def svDp18a6 : List BInstr :=
  [.aluImm .add a0 x0 0x4]
set_option maxRecDepth 100000 in
theorem svDp18a6_end : blockEnd sigstoreVerifyCode 0x8A6 svDp18a6 = some 0x8A8 := by decide

def svDp18b0 : List BInstr :=
  [.aluImm .add a1 x0 0xA, .alu .add a2 x0 (8 : Fin 32)]
set_option maxRecDepth 100000 in
theorem svDp18b0_end : blockEnd sigstoreVerifyCode 0x8B0 svDp18b0 = some 0x8B4 := by decide

def svDp18be : List BInstr :=
  [.aluImm .add (22 : Fin 32) (22 : Fin 32) 0x1, .aluImm .add (23 : Fin 32) (23 : Fin 32) 0x8]
set_option maxRecDepth 100000 in
theorem svDp18be_end : blockEnd sigstoreVerifyCode 0x8BE svDp18be = some 0x8C2 := by decide

def svDp18c4 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x320, .alu .add a0 a0 sp]
set_option maxRecDepth 100000 in
theorem svDp18c4_end : blockEnd sigstoreVerifyCode 0x8C4 svDp18c4 = some 0x8CC := by decide

def svDp18ce : List BInstr :=
  [.aluImm .add a3 a0 0x100]
set_option maxRecDepth 100000 in
theorem svDp18ce_end : blockEnd sigstoreVerifyCode 0x8CE svDp18ce = some 0x8D2 := by decide

def svDp18da : List BInstr :=
  [.lui a1 0x1000, .aluImm .add a1 a1 0x320, .alu .add (8 : Fin 32) sp a1]
set_option maxRecDepth 100000 in
theorem svDp18da_end : blockEnd sigstoreVerifyCode 0x8DA svDp18da = some 0x8E4 := by decide

def svDp18e6 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x20, .alu .add a0 a0 sp, .lui a1 0x1000, .aluImm .add a1 a1 0x480, .alu .add a1 a1 sp]
set_option maxRecDepth 100000 in
theorem svDp18e6_end : blockEnd sigstoreVerifyCode 0x8E6 svDp18e6 = some 0x8F6 := by decide

def svDp1908 : List BInstr :=
  [.aluImm .add a2 x0 0xC]
set_option maxRecDepth 100000 in
theorem svDp1908_end : blockEnd sigstoreVerifyCode 0x908 svDp1908 = some 0x90A := by decide

def svDp1b4e : List BInstr :=
  [.aluImm .add a0 x0 0x16]
set_option maxRecDepth 100000 in
theorem svDp1b4e_end : blockEnd sigstoreVerifyCode 0xB4E svDp1b4e = some 0xB50 := by decide

def svDp1b36 : List BInstr :=
  [.aluImm .add a0 x0 0x1]
set_option maxRecDepth 100000 in
theorem svDp1b36_end : blockEnd sigstoreVerifyCode 0xB36 svDp1b36 = some 0xB38 := by decide

def svDp191a : List BInstr :=
  [.aluImm .sll (22 : Fin 32) (22 : Fin 32) 0x3, .aluImm .add a2 sp 0x7FF, .aluImm .add a2 a2 0x221, .alu .add (22 : Fin 32) (22 : Fin 32) a2, .alu .add a2 x0 (22 : Fin 32)]
set_option maxRecDepth 100000 in
theorem svDp191a_end : blockEnd sigstoreVerifyCode 0x91A svDp191a = some 0x928 := by decide

set_option maxHeartbeats 0 in
theorem sv_dp1 {B out bp x9 x21 x25 x26 f30 f34 rem p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 op ol vp vl rest : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x60E (reg n0))
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
    (SD0 : SvData n0.mem)
    (hku : ¬ memBytes n0.mem op ol.toNat = memBytes n0.mem (BitVec.ofNat 32 0x3FCC4889) 3)
    (heku : ¬ memBytes n0.mem op ol.toNat = memBytes n0.mem (BitVec.ofNat 32 0x3FCC4892) 3)
    (hbc : ¬ memBytes n0.mem op ol.toNat = memBytes n0.mem (BitVec.ofNat 32 0x3FCC488F) 3)
    (hp0 : ¬ memBytes n0.mem (BitVec.ofNat 32 0x3FCC48B8) 10 = memBytes n0.mem op ol.toNat)
    (hp1 : memBytes n0.mem (BitVec.ofNat 32 0x3FCC48C2) 10 = memBytes n0.mem op ol.toNat) :
    (¬ (∃ tl43, derTlv (memBytes n0.mem (vp) (vl).toNat) = .ok tl43 ∧ (BitVec.ofNat 8 tl43.tag = BitVec.ofNat 8 0xC) ∧ ((vl) - BitVec.ofNat 32 (tl43.header + tl43.len) = 0) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ tl43, derTlv (memBytes n0.mem (vp) (vl).toNat) = .ok tl43 ∧
    (BitVec.ofNat 8 tl43.tag = BitVec.ofNat 8 0xC) ∧
    ((vl) - BitVec.ofNat 32 (tl43.header + tl43.len) = 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x4EA (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = n0.mem x) ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (vp) + BitVec.ofNat 32 tl43.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl43.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = n0.mem x := fun _ _ => rfl
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x60E
  obtain ⟨n1, c1, u1⟩ := s0.block svDp160e E0.self svDp160e_end
    ⟨trivial, trivial, trivial⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0x612 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have rb1 : ∀ q, reg n1 q = (runBlock svDp160e (n0.mem, reg n0)).2 q := fun q => by rw [u1.regs]
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans c1
  have fR1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x hx => (fr1 x hx).trans (fR0 x hx)
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
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svDp160e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_21, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g1_13 : reg n1 a3 = BitVec.ofNat 32 0x3 := by
    rw [rb1]; simp +decide only [runBlock, BInstr.run, svDp160e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g0_2, g0_3, g0_4, g0_8, g0_9, g0_18, g0_19, g0_21, g0_25, g0_26, g0_27, s0.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have fR2 : ∀ x, SvR B x → n2.mem x = n0.mem x := fun x hx => (fr2 x hx).trans (fR1 x hx)
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
  obtain ⟨n3, c3, u3⟩ := s2.block svDp1614 E2.self svDp1614_end
    ⟨trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem SV n3 0x61C (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have rb3 : ∀ q, reg n3 q = (runBlock svDp1614 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans c3
  have fR3 : ∀ x, SvR B x → n3.mem x = n0.mem x := fun x hx => (fr3 x hx).trans (fR2 x hx)
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
    rw [rb3]; simp +decide only [runBlock, BInstr.run, svDp1614, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g2_2, g2_3, g2_4, g2_8, g2_9, g2_10, g2_11, g2_13, g2_18, g2_19, g2_21, g2_25, g2_26, g2_27, s2.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have fR4 : ∀ x, SvR B x → n4.mem x = n0.mem x := fun x hx => (fr4 x hx).trans (fR3 x hx)
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
  have fR5 : ∀ x, SvR B x → n5.mem x = n0.mem x := fun x hx => (fr5 x hx).trans (fR4 x hx)
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
  obtain ⟨n6, c6, u6⟩ := s5.block svDp16bc E5.self svDp16bc_end
    ⟨trivial, trivial, trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem SV n6 0x6C0 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have rb6 : ∀ q, reg n6 q = (runBlock svDp16bc (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans c6
  have fR6 : ∀ x, SvR B x → n6.mem x = n0.mem x := fun x hx => (fr6 x hx).trans (fR5 x hx)
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
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svDp16bc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_10, g5_18, g5_19, g5_21, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g6_13 : reg n6 a3 = BitVec.ofNat 32 0x3 := by
    rw [rb6]; simp +decide only [runBlock, BInstr.run, svDp16bc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g5_2, g5_3, g5_4, g5_8, g5_9, g5_10, g5_18, g5_19, g5_21, g5_25, g5_26, g5_27, s5.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have fR7 : ∀ x, SvR B x → n7.mem x = n0.mem x := fun x hx => (fr7 x hx).trans (fR6 x hx)
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
  obtain ⟨n8, c8, u8⟩ := s7.block svDp16c2 E7.self svDp16c2_end
    ⟨trivial, trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem SV n8 0x6CA (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have rb8 : ∀ q, reg n8 q = (runBlock svDp16c2 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
  have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans c8
  have fR8 : ∀ x, SvR B x → n8.mem x = n0.mem x := fun x hx => (fr8 x hx).trans (fR7 x hx)
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
    rw [rb8]; simp +decide only [runBlock, BInstr.run, svDp16c2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g7_2, g7_3, g7_4, g7_8, g7_9, g7_10, g7_11, g7_13, g7_18, g7_19, g7_21, g7_25, g7_26, g7_27, s7.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have fR9 : ∀ x, SvR B x → n9.mem x = n0.mem x := fun x hx => (fr9 x hx).trans (fR8 x hx)
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
  have fR10 : ∀ x, SvR B x → n10.mem x = n0.mem x := fun x hx => (fr10 x hx).trans (fR9 x hx)
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
  obtain ⟨n11, c11, u11⟩ := s10.block svDp178e E10.self svDp178e_end
    ⟨trivial, trivial, trivial⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have s11 : St n11.mem SV n11 0x792 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have rb11 : ∀ q, reg n11 q = (runBlock svDp178e (n10.mem, reg n10)).2 q := fun q => by rw [u11.regs]
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans c11
  have fR11 : ∀ x, SvR B x → n11.mem x = n0.mem x := fun x hx => (fr11 x hx).trans (fR10 x hx)
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
    rw [rb11]; simp +decide only [runBlock, BInstr.run, svDp178e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_8, g10_9, g10_10, g10_18, g10_19, g10_21, g10_25, g10_26, g10_27, s10.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g11_13 : reg n11 a3 = BitVec.ofNat 32 0x3 := by
    rw [rb11]; simp +decide only [runBlock, BInstr.run, svDp178e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g10_2, g10_3, g10_4, g10_8, g10_9, g10_10, g10_18, g10_19, g10_21, g10_25, g10_26, g10_27, s10.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have fR12 : ∀ x, SvR B x → n12.mem x = n0.mem x := fun x hx => (fr12 x hx).trans (fR11 x hx)
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
  obtain ⟨n13, c13, u13⟩ := s12.block svDp1794 E12.self svDp1794_end
    ⟨trivial, trivial, trivial⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have s13 : St n13.mem SV n13 0x79C (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have rb13 : ∀ q, reg n13 q = (runBlock svDp1794 (n12.mem, reg n12)).2 q := fun q => by rw [u13.regs]
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans c13
  have fR13 : ∀ x, SvR B x → n13.mem x = n0.mem x := fun x hx => (fr13 x hx).trans (fR12 x hx)
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
    rw [rb13]; simp +decide only [runBlock, BInstr.run, svDp1794, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g12_2, g12_3, g12_4, g12_8, g12_9, g12_10, g12_11, g12_13, g12_18, g12_19, g12_21, g12_25, g12_26, g12_27, s12.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have fR14 : ∀ x, SvR B x → n14.mem x = n0.mem x := fun x hx => (fr14 x hx).trans (fR13 x hx)
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
  have fR15 : ∀ x, SvR B x → n15.mem x = n0.mem x := fun x hx => (fr15 x hx).trans (fR14 x hx)
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
  obtain ⟨n16, c16, u16⟩ := s15.block svDp189c E15.self svDp189c_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have s16 : St n16.mem SV n16 0x8A6 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have rb16 : ∀ q, reg n16 q = (runBlock svDp189c (n15.mem, reg n15)).2 q := fun q => by rw [u16.regs]
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans c16
  have fR16 : ∀ x, SvR B x → n16.mem x = n0.mem x := fun x hx => (fr16 x hx).trans (fR15 x hx)
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
    rw [rb16]; simp +decide only [runBlock, BInstr.run, svDp189c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_8, g15_9, g15_10, g15_18, g15_19, g15_21, g15_25, g15_26, g15_27, s15.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g16_23 : reg n16 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48EC := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, svDp189c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_8, g15_9, g15_10, g15_18, g15_19, g15_21, g15_25, g15_26, g15_27, s15.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  obtain ⟨n17, c17, u17⟩ := s16.block svDp18a6 E16.self svDp18a6_end
    ⟨trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem SV n17 0x8A8 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock svDp18a6 (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
  have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans c17
  have fR17 : ∀ x, SvR B x → n17.mem x = n0.mem x := fun x hx => (fr17 x hx).trans (fR16 x hx)
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
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svDp18a6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_10, g16_18, g16_19, g16_21, g16_22, g16_23, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have fR18 : ∀ x, SvR B x → n18.mem x = n0.mem x := fun x hx => (fr18 x hx).trans (fR17 x hx)
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
  have fR19 : ∀ x, SvR B x → n19.mem x = n0.mem x := fun x hx => (fr19 x hx).trans (fR18 x hx)
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
  obtain ⟨n20, c20, u20⟩ := s19.block svDp18b0 E19.self svDp18b0_end
    ⟨trivial, trivial, trivial⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have s20 : St n20.mem SV n20 0x8B4 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have rb20 : ∀ q, reg n20 q = (runBlock svDp18b0 (n19.mem, reg n19)).2 q := fun q => by rw [u20.regs]
  have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
  have t20 : Steps n0 n20 := t19.trans c20
  have fR20 : ∀ x, SvR B x → n20.mem x = n0.mem x := fun x hx => (fr20 x hx).trans (fR19 x hx)
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
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svDp18b0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_18, g19_19, g19_21, g19_22, g19_23, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g20_12 : reg n20 a2 = op := by
    rw [rb20]; simp +decide only [runBlock, BInstr.run, svDp18b0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g19_2, g19_3, g19_4, g19_8, g19_9, g19_10, g19_18, g19_19, g19_21, g19_22, g19_23, g19_25, g19_26, g19_27, s19.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have fR21 : ∀ x, SvR B x → n21.mem x = n0.mem x := fun x hx => (fr21 x hx).trans (fR20 x hx)
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
  have fR22 : ∀ x, SvR B x → n22.mem x = n0.mem x := fun x hx => (fr22 x hx).trans (fR21 x hx)
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
  have g22_10 : reg n22 a0 = BitVec.ofNat 32 0 := by rw [a0_22, ite_eq_right hp0]; rfl
  -- 0x8BE
  obtain ⟨n23, c23, u23⟩ := s22.block svDp18be E22.self svDp18be_end
    ⟨trivial, trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem SV n23 0x8C2 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock svDp18be (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans c23
  have fR23 : ∀ x, SvR B x → n23.mem x = n0.mem x := fun x hx => (fr23 x hx).trans (fR22 x hx)
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
  have g23_10 : reg n23 a0 = BitVec.ofNat 32 0x0 := by
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
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svDp18be, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_10, g22_18, g22_19, g22_21, g22_22, g22_23, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g23_23 : reg n23 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svDp18be, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_8, g22_9, g22_10, g22_18, g22_19, g22_21, g22_22, g22_23, g22_25, g22_26, g22_27, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  -- 0x8C2: branch, taken
  obtain ⟨n24, d24, u24⟩ := s23.taken E23.self 0x8A6 sv_at_8c2
    (by decide) (by rw [g23_10, s23.zero]; decide)
  have s24 : St n24.mem SV n24 0x8A6 (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, SvR B x → n24.mem x = n0.mem x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = op := by rw [u24.regs, g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = x9 := by rw [u24.regs, g23_9]
  have g24_10 : reg n24 a0 = BitVec.ofNat 32 0x0 := by rw [u24.regs, g23_10]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
  have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [u24.regs, g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u24.regs, g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u24.regs, g23_23]
  have g24_25 : reg n24 (25 : Fin 32) = x25 := by rw [u24.regs, g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [u24.regs, g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u24.regs, g23_27]
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
  -- 0x8A6
  obtain ⟨n25, c25, u25⟩ := s24.block svDp18a6 E24.self svDp18a6_end
    ⟨trivial, trivial⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have s25 : St n25.mem SV n25 0x8A8 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have rb25 : ∀ q, reg n25 q = (runBlock svDp18a6 (n24.mem, reg n24)).2 q := fun q => by rw [u25.regs]
  have fr25 : ∀ x, SvR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
  have t25 : Steps n0 n25 := t24.trans c25
  have fR25 : ∀ x, SvR B x → n25.mem x = n0.mem x := fun x hx => (fr25 x hx).trans (fR24 x hx)
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
  have g25_10 : reg n25 a0 = BitVec.ofNat 32 0x4 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svDp18a6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_10, g24_18, g24_19, g24_21, g24_22, g24_23, g24_25, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  -- 0x8A8: branch, not taken
  obtain ⟨n26, d26, u26⟩ := s25.notTaken E25.self 0x8AC sv_at_8a8
    (by decide) (by rw [g25_22, g25_10]; decide)
  have s26 : St n26.mem SV n26 0x8AC (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans (.single d26)
  have fR26 : ∀ x, SvR B x → n26.mem x = n0.mem x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = op := by rw [u26.regs, g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = x9 := by rw [u26.regs, g25_9]
  have g26_10 : reg n26 a0 = BitVec.ofNat 32 0x4 := by rw [u26.regs, g25_10]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, g25_19]
  have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [u26.regs, g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u26.regs, g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u26.regs, g25_23]
  have g26_25 : reg n26 (25 : Fin 32) = x25 := by rw [u26.regs, g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [u26.regs, g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u26.regs, g25_27]
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
  -- 0x8AC: lw of a constant
  obtain ⟨n27, d27, u27⟩ := s26.lw E26.self sv_at_8ac (off' := 0x8B0) (by decide)
    (by rw [g26_23]; decide)
  have s27 : St n27.mem SV n27 0x8B0 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans (.single d27)
  have fR27 : ∀ x, SvR B x → n27.mem x = n0.mem x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = op := by rw [u27.regs, upd_ne (by decide) (by decide), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = x9 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_9]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, upd_ne (by decide) (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_19]
  have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_23]
  have g27_25 : reg n27 (25 : Fin 32) = x25 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_27]
  have g27_10 : reg n27 a0 = BitVec.ofNat 32 0x3FCC48C2 := by
    rw [u27.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g26_23, show BitVec.ofNat 32 0x3FCC48F4 + 0x0 = SVK + BitVec.ofNat 32 0xDC by decide]
    exact (SvData.sv F SD0 fR26).w32 (by decide) (by decide)
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
  clear w26_a44 w26_a40 w26_a3c w26_a38 w26_a34 w26_a30 w26_a2c w26_a28 w26_a24 w26_a20 w26_94 w26_90 w26_8c w26_88 w26_84 w26_80 w26_7c w26_78 w26_74 w26_70 w26_6c w26_68 w26_64 w26_60 w26_5c w26_58 w26_54 w26_50 w26_4c w26_48 w26_40 w26_3c w26_38 w26_34 w26_30 g26_27 g26_26 g26_25 g26_23 g26_22 g26_21 g26_19 g26_18 g26_10 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
  -- 0x8B0
  obtain ⟨n28, c28, u28⟩ := s27.block svDp18b0 E27.self svDp18b0_end
    ⟨trivial, trivial, trivial⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have s28 : St n28.mem SV n28 0x8B4 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have rb28 : ∀ q, reg n28 q = (runBlock svDp18b0 (n27.mem, reg n27)).2 q := fun q => by rw [u28.regs]
  have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
  have t28 : Steps n0 n28 := t27.trans c28
  have fR28 : ∀ x, SvR B x → n28.mem x = n0.mem x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.same m28
  have g28_2 : reg n28 sp = B + 0x21A0 := by
    rw [rb28, runBlock_reg _ _ _ sp s27.zero (by decide), g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb28, runBlock_reg _ _ _ (3 : Fin 32) s27.zero (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb28, runBlock_reg _ _ _ (4 : Fin 32) s27.zero (by decide), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = op := by
    rw [rb28, runBlock_reg _ _ _ (8 : Fin 32) s27.zero (by decide), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = x9 := by
    rw [rb28, runBlock_reg _ _ _ (9 : Fin 32) s27.zero (by decide), g27_9]
  have g28_10 : reg n28 a0 = BitVec.ofNat 32 0x3FCC48C2 := by
    rw [rb28, runBlock_reg _ _ _ a0 s27.zero (by decide), g27_10]
  have g28_18 : reg n28 (18 : Fin 32) = out := by
    rw [rb28, runBlock_reg _ _ _ (18 : Fin 32) s27.zero (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by
    rw [rb28, runBlock_reg _ _ _ (19 : Fin 32) s27.zero (by decide), g27_19]
  have g28_21 : reg n28 (21 : Fin 32) = x21 := by
    rw [rb28, runBlock_reg _ _ _ (21 : Fin 32) s27.zero (by decide), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb28, runBlock_reg _ _ _ (22 : Fin 32) s27.zero (by decide), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by
    rw [rb28, runBlock_reg _ _ _ (23 : Fin 32) s27.zero (by decide), g27_23]
  have g28_25 : reg n28 (25 : Fin 32) = x25 := by
    rw [rb28, runBlock_reg _ _ _ (25 : Fin 32) s27.zero (by decide), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by
    rw [rb28, runBlock_reg _ _ _ (26 : Fin 32) s27.zero (by decide), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb28, runBlock_reg _ _ _ (27 : Fin 32) s27.zero (by decide), g27_27]
  have g28_11 : reg n28 a1 = BitVec.ofNat 32 0xA := by
    rw [rb28]; simp +decide only [runBlock, BInstr.run, svDp18b0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g27_2, g27_3, g27_4, g27_8, g27_9, g27_10, g27_18, g27_19, g27_21, g27_22, g27_23, g27_25, g27_26, g27_27, s27.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g28_12 : reg n28 a2 = op := by
    rw [rb28]; simp +decide only [runBlock, BInstr.run, svDp18b0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g27_2, g27_3, g27_4, g27_8, g27_9, g27_10, g27_18, g27_19, g27_21, g27_22, g27_23, g27_25, g27_26, g27_27, s27.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w28_30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m28]; exact w27_30
  have w28_34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m28]; exact w27_34
  have w28_38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m28]; exact w27_38
  have w28_3c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m28]; exact w27_3c
  have w28_40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m28]; exact w27_40
  have w28_48 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m28]; exact w27_48
  have w28_4c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m28]; exact w27_4c
  have w28_50 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m28]; exact w27_50
  have w28_54 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m28]; exact w27_54
  have w28_58 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m28]; exact w27_58
  have w28_5c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m28]; exact w27_5c
  have w28_60 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m28]; exact w27_60
  have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m28]; exact w27_64
  have w28_68 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m28]; exact w27_68
  have w28_6c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m28]; exact w27_6c
  have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m28]; exact w27_70
  have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m28]; exact w27_74
  have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m28]; exact w27_78
  have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m28]; exact w27_7c
  have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m28]; exact w27_80
  have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m28]; exact w27_84
  have w28_88 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m28]; exact w27_88
  have w28_8c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m28]; exact w27_8c
  have w28_90 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m28]; exact w27_90
  have w28_94 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m28]; exact w27_94
  have w28_a20 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m28]; exact w27_a20
  have w28_a24 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m28]; exact w27_a24
  have w28_a28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m28]; exact w27_a28
  have w28_a2c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m28]; exact w27_a2c
  have w28_a30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m28]; exact w27_a30
  have w28_a34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m28]; exact w27_a34
  have w28_a38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m28]; exact w27_a38
  have w28_a3c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m28]; exact w27_a3c
  have w28_a40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m28]; exact w27_a40
  have w28_a44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m28]; exact w27_a44
  clear w27_a44 w27_a40 w27_a3c w27_a38 w27_a34 w27_a30 w27_a2c w27_a28 w27_a24 w27_a20 w27_94 w27_90 w27_8c w27_88 w27_84 w27_80 w27_7c w27_78 w27_74 w27_70 w27_6c w27_68 w27_64 w27_60 w27_5c w27_58 w27_54 w27_50 w27_4c w27_48 w27_40 w27_3c w27_38 w27_34 w27_30 g27_10 g27_27 g27_26 g27_25 g27_23 g27_22 g27_21 g27_19 g27_18 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
  -- 0x8B4: lw
  obtain ⟨n29, d29, u29⟩ := s28.lw E28.self sv_at_8b4 (off' := 0x8B6) (by decide)
    (by rw [g28_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s29 : St n29.mem SV n29 0x8B6 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans (.single d29)
  have fR29 : ∀ x, SvR B x → n29.mem x = n0.mem x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, upd_ne (by decide) (by decide), g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = op := by rw [u29.regs, upd_ne (by decide) (by decide), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = x9 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_9]
  have g29_10 : reg n29 a0 = BitVec.ofNat 32 0x3FCC48C2 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_10]
  have g29_11 : reg n29 a1 = BitVec.ofNat 32 0xA := by rw [u29.regs, upd_ne (by decide) (by decide), g28_11]
  have g29_12 : reg n29 a2 = op := by rw [u29.regs, upd_ne (by decide) (by decide), g28_12]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, upd_ne (by decide) (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, upd_ne (by decide) (by decide), g28_19]
  have g29_21 : reg n29 (21 : Fin 32) = x21 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_23]
  have g29_25 : reg n29 (25 : Fin 32) = x25 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u29.regs, upd_ne (by decide) (by decide), g28_27]
  have g29_13 : reg n29 a3 = ol := by
    rw [u29.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g28_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w28_48]
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
  clear w28_a44 w28_a40 w28_a3c w28_a38 w28_a34 w28_a30 w28_a2c w28_a28 w28_a24 w28_a20 w28_94 w28_90 w28_8c w28_88 w28_84 w28_80 w28_7c w28_78 w28_74 w28_70 w28_6c w28_68 w28_64 w28_60 w28_5c w28_58 w28_54 w28_50 w28_4c w28_48 w28_40 w28_3c w28_38 w28_34 w28_30 g28_12 g28_11 g28_27 g28_26 g28_25 g28_23 g28_22 g28_21 g28_19 g28_18 g28_10 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 rb28 s28 m28 u28 c28
  -- 0x8B6: sv_seqEqF
  obtain ⟨n30, c30, s30, rk30, a0_30, K30, fr30⟩ := sv_seqEqF (pl := 10) (ql := ol.toNat)
    F E29 s29 sv_at_8b6 sv_at_8ba (by decide) (by decide) g29_2
    g29_10 g29_11 g29_12 (by rw [g29_13, ofNat_toNat_self]) (.inr ⟨by decide, by decide⟩) (.inl oid_in)
  have t30 : Steps n0 n30 := t29.trans c30
  have fR30 : ∀ x, SvR B x → n30.mem x = n0.mem x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.keepL K30 (by decide)
  rw [sv_mbRo F fR29 (.inr ⟨by decide, by decide⟩), sv_mbRo F fR29 (.inl oid_in)] at a0_30
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [rk30 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk30 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk30 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = op := by rw [rk30 (8 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = x9 := by rw [rk30 (9 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_9]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [rk30 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [rk30 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_19]
  have g30_21 : reg n30 (21 : Fin 32) = x21 := by rw [rk30 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rk30 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48F4 := by rw [rk30 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_23]
  have g30_25 : reg n30 (25 : Fin 32) = x25 := by rw [rk30 (25 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = x26 := by rw [rk30 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk30 (27 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g29_27]
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
  clear w29_a44 w29_a40 w29_a3c w29_a38 w29_a34 w29_a30 w29_a2c w29_a28 w29_a24 w29_a20 w29_94 w29_90 w29_8c w29_88 w29_84 w29_80 w29_7c w29_78 w29_74 w29_70 w29_6c w29_68 w29_64 w29_60 w29_5c w29_58 w29_54 w29_50 w29_4c w29_48 w29_40 w29_3c w29_38 w29_34 w29_30 g29_13 g29_27 g29_26 g29_25 g29_23 g29_22 g29_21 g29_19 g29_18 g29_12 g29_11 g29_10 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29
  have g30_10 : reg n30 a0 = BitVec.ofNat 32 1 := by rw [a0_30, ite_eq_left hp1]; rfl
  -- 0x8BE
  obtain ⟨n31, c31, u31⟩ := s30.block svDp18be E30.self svDp18be_end
    ⟨trivial, trivial, trivial⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have s31 : St n31.mem SV n31 0x8C2 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have rb31 : ∀ q, reg n31 q = (runBlock svDp18be (n30.mem, reg n30)).2 q := fun q => by rw [u31.regs]
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans c31
  have fR31 : ∀ x, SvR B x → n31.mem x = n0.mem x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by
    rw [rb31, runBlock_reg _ _ _ sp s30.zero (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb31, runBlock_reg _ _ _ (3 : Fin 32) s30.zero (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb31, runBlock_reg _ _ _ (4 : Fin 32) s30.zero (by decide), g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = op := by
    rw [rb31, runBlock_reg _ _ _ (8 : Fin 32) s30.zero (by decide), g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = x9 := by
    rw [rb31, runBlock_reg _ _ _ (9 : Fin 32) s30.zero (by decide), g30_9]
  have g31_10 : reg n31 a0 = BitVec.ofNat 32 0x1 := by
    rw [rb31, runBlock_reg _ _ _ a0 s30.zero (by decide), g30_10]
  have g31_18 : reg n31 (18 : Fin 32) = out := by
    rw [rb31, runBlock_reg _ _ _ (18 : Fin 32) s30.zero (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by
    rw [rb31, runBlock_reg _ _ _ (19 : Fin 32) s30.zero (by decide), g30_19]
  have g31_21 : reg n31 (21 : Fin 32) = x21 := by
    rw [rb31, runBlock_reg _ _ _ (21 : Fin 32) s30.zero (by decide), g30_21]
  have g31_25 : reg n31 (25 : Fin 32) = x25 := by
    rw [rb31, runBlock_reg _ _ _ (25 : Fin 32) s30.zero (by decide), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = x26 := by
    rw [rb31, runBlock_reg _ _ _ (26 : Fin 32) s30.zero (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb31, runBlock_reg _ _ _ (27 : Fin 32) s30.zero (by decide), g30_27]
  have g31_22 : reg n31 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb31]; simp +decide only [runBlock, BInstr.run, svDp18be, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_10, g30_18, g30_19, g30_21, g30_22, g30_23, g30_25, g30_26, g30_27, s30.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g31_23 : reg n31 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by
    rw [rb31]; simp +decide only [runBlock, BInstr.run, svDp18be, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g30_2, g30_3, g30_4, g30_8, g30_9, g30_10, g30_18, g30_19, g30_21, g30_22, g30_23, g30_25, g30_26, g30_27, s30.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w31_30 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m31]; exact w30_30
  have w31_34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m31]; exact w30_34
  have w31_38 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m31]; exact w30_38
  have w31_3c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m31]; exact w30_3c
  have w31_40 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m31]; exact w30_40
  have w31_48 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m31]; exact w30_48
  have w31_4c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m31]; exact w30_4c
  have w31_50 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m31]; exact w30_50
  have w31_54 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m31]; exact w30_54
  have w31_58 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m31]; exact w30_58
  have w31_5c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m31]; exact w30_5c
  have w31_60 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m31]; exact w30_60
  have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m31]; exact w30_64
  have w31_68 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m31]; exact w30_68
  have w31_6c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m31]; exact w30_6c
  have w31_70 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m31]; exact w30_70
  have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m31]; exact w30_74
  have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m31]; exact w30_78
  have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m31]; exact w30_7c
  have w31_80 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m31]; exact w30_80
  have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m31]; exact w30_84
  have w31_88 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m31]; exact w30_88
  have w31_8c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m31]; exact w30_8c
  have w31_90 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m31]; exact w30_90
  have w31_94 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m31]; exact w30_94
  have w31_a20 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m31]; exact w30_a20
  have w31_a24 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m31]; exact w30_a24
  have w31_a28 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m31]; exact w30_a28
  have w31_a2c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m31]; exact w30_a2c
  have w31_a30 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m31]; exact w30_a30
  have w31_a34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m31]; exact w30_a34
  have w31_a38 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m31]; exact w30_a38
  have w31_a3c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m31]; exact w30_a3c
  have w31_a40 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m31]; exact w30_a40
  have w31_a44 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m31]; exact w30_a44
  clear w30_a44 w30_a40 w30_a3c w30_a38 w30_a34 w30_a30 w30_a2c w30_a28 w30_a24 w30_a20 w30_94 w30_90 w30_8c w30_88 w30_84 w30_80 w30_7c w30_78 w30_74 w30_70 w30_6c w30_68 w30_64 w30_60 w30_5c w30_58 w30_54 w30_50 w30_4c w30_48 w30_40 w30_3c w30_38 w30_34 w30_30 g30_27 g30_26 g30_25 g30_23 g30_22 g30_21 g30_19 g30_18 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 K30 a0_30 rk30 s30 c30
  -- 0x8C2: branch, not taken
  obtain ⟨n32, d32, u32⟩ := s31.notTaken E31.self 0x8C4 sv_at_8c2
    (by decide) (by rw [g31_10, s31.zero]; decide)
  have s32 : St n32.mem SV n32 0x8C4 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans (.single d32)
  have fR32 : ∀ x, SvR B x → n32.mem x = n0.mem x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = op := by rw [u32.regs, g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = x9 := by rw [u32.regs, g31_9]
  have g32_10 : reg n32 a0 = BitVec.ofNat 32 0x1 := by rw [u32.regs, g31_10]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, g31_19]
  have g32_21 : reg n32 (21 : Fin 32) = x21 := by rw [u32.regs, g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u32.regs, g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u32.regs, g31_23]
  have g32_25 : reg n32 (25 : Fin 32) = x25 := by rw [u32.regs, g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = x26 := by rw [u32.regs, g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u32.regs, g31_27]
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
  clear w31_a44 w31_a40 w31_a3c w31_a38 w31_a34 w31_a30 w31_a2c w31_a28 w31_a24 w31_a20 w31_94 w31_90 w31_8c w31_88 w31_84 w31_80 w31_7c w31_78 w31_74 w31_70 w31_6c w31_68 w31_64 w31_60 w31_5c w31_58 w31_54 w31_50 w31_4c w31_48 w31_40 w31_3c w31_38 w31_34 w31_30 g31_23 g31_22 g31_27 g31_26 g31_25 g31_21 g31_19 g31_18 g31_10 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 rb31 s31 m31 u31 c31 g30_10
  -- 0x8C4
  obtain ⟨n33, c33, u33⟩ := s32.block svDp18c4 E32.self svDp18c4_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have s33 : St n33.mem SV n33 0x8CC (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have rb33 : ∀ q, reg n33 q = (runBlock svDp18c4 (n32.mem, reg n32)).2 q := fun q => by rw [u33.regs]
  have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
  have t33 : Steps n0 n33 := t32.trans c33
  have fR33 : ∀ x, SvR B x → n33.mem x = n0.mem x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.same m33
  have g33_2 : reg n33 sp = B + 0x21A0 := by
    rw [rb33, runBlock_reg _ _ _ sp s32.zero (by decide), g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb33, runBlock_reg _ _ _ (3 : Fin 32) s32.zero (by decide), g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb33, runBlock_reg _ _ _ (4 : Fin 32) s32.zero (by decide), g32_4]
  have g33_8 : reg n33 (8 : Fin 32) = op := by
    rw [rb33, runBlock_reg _ _ _ (8 : Fin 32) s32.zero (by decide), g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = x9 := by
    rw [rb33, runBlock_reg _ _ _ (9 : Fin 32) s32.zero (by decide), g32_9]
  have g33_18 : reg n33 (18 : Fin 32) = out := by
    rw [rb33, runBlock_reg _ _ _ (18 : Fin 32) s32.zero (by decide), g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by
    rw [rb33, runBlock_reg _ _ _ (19 : Fin 32) s32.zero (by decide), g32_19]
  have g33_21 : reg n33 (21 : Fin 32) = x21 := by
    rw [rb33, runBlock_reg _ _ _ (21 : Fin 32) s32.zero (by decide), g32_21]
  have g33_22 : reg n33 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb33, runBlock_reg _ _ _ (22 : Fin 32) s32.zero (by decide), g32_22]
  have g33_23 : reg n33 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by
    rw [rb33, runBlock_reg _ _ _ (23 : Fin 32) s32.zero (by decide), g32_23]
  have g33_25 : reg n33 (25 : Fin 32) = x25 := by
    rw [rb33, runBlock_reg _ _ _ (25 : Fin 32) s32.zero (by decide), g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = x26 := by
    rw [rb33, runBlock_reg _ _ _ (26 : Fin 32) s32.zero (by decide), g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb33, runBlock_reg _ _ _ (27 : Fin 32) s32.zero (by decide), g32_27]
  have g33_10 : reg n33 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb33]; simp +decide only [runBlock, BInstr.run, svDp18c4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g32_2, g32_3, g32_4, g32_8, g32_9, g32_10, g32_18, g32_19, g32_21, g32_22, g32_23, g32_25, g32_26, g32_27, s32.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w33_30 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m33]; exact w32_30
  have w33_34 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m33]; exact w32_34
  have w33_38 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m33]; exact w32_38
  have w33_3c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m33]; exact w32_3c
  have w33_40 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m33]; exact w32_40
  have w33_48 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m33]; exact w32_48
  have w33_4c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m33]; exact w32_4c
  have w33_50 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m33]; exact w32_50
  have w33_54 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m33]; exact w32_54
  have w33_58 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m33]; exact w32_58
  have w33_5c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m33]; exact w32_5c
  have w33_60 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m33]; exact w32_60
  have w33_64 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m33]; exact w32_64
  have w33_68 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m33]; exact w32_68
  have w33_6c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m33]; exact w32_6c
  have w33_70 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m33]; exact w32_70
  have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m33]; exact w32_74
  have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m33]; exact w32_78
  have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m33]; exact w32_7c
  have w33_80 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m33]; exact w32_80
  have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m33]; exact w32_84
  have w33_88 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m33]; exact w32_88
  have w33_8c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m33]; exact w32_8c
  have w33_90 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m33]; exact w32_90
  have w33_94 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m33]; exact w32_94
  have w33_a20 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m33]; exact w32_a20
  have w33_a24 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m33]; exact w32_a24
  have w33_a28 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m33]; exact w32_a28
  have w33_a2c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m33]; exact w32_a2c
  have w33_a30 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m33]; exact w32_a30
  have w33_a34 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m33]; exact w32_a34
  have w33_a38 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m33]; exact w32_a38
  have w33_a3c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m33]; exact w32_a3c
  have w33_a40 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m33]; exact w32_a40
  have w33_a44 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m33]; exact w32_a44
  clear w32_a44 w32_a40 w32_a3c w32_a38 w32_a34 w32_a30 w32_a2c w32_a28 w32_a24 w32_a20 w32_94 w32_90 w32_8c w32_88 w32_84 w32_80 w32_7c w32_78 w32_74 w32_70 w32_6c w32_68 w32_64 w32_60 w32_5c w32_58 w32_54 w32_50 w32_4c w32_48 w32_40 w32_3c w32_38 w32_34 w32_30 g32_27 g32_26 g32_25 g32_23 g32_22 g32_21 g32_19 g32_18 g32_10 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
  -- 0x8CC: lw
  obtain ⟨n34, d34, u34⟩ := s33.lw E33.self sv_at_8cc (off' := 0x8CE) (by decide)
    (by rw [g33_2, show B + 0x21A0 + 0x3C = B + 0x21A0 + BitVec.ofNat 32 0x3C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s34 : St n34.mem SV n34 0x8CE (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
  have m34 : n34.mem = n33.mem := u34.mem
  have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
  have t34 : Steps n0 n34 := t33.trans (.single d34)
  have fR34 : ∀ x, SvR B x → n34.mem x = n0.mem x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.same m34
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_4]
  have g34_8 : reg n34 (8 : Fin 32) = op := by rw [u34.regs, upd_ne (by decide) (by decide), g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = x9 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_9]
  have g34_10 : reg n34 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_10]
  have g34_18 : reg n34 (18 : Fin 32) = out := by rw [u34.regs, upd_ne (by decide) (by decide), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [u34.regs, upd_ne (by decide) (by decide), g33_19]
  have g34_21 : reg n34 (21 : Fin 32) = x21 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u34.regs, upd_ne (by decide) (by decide), g33_23]
  have g34_25 : reg n34 (25 : Fin 32) = x25 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = x26 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_27]
  have g34_11 : reg n34 a1 = vp := by
    rw [u34.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g33_2, show B + 0x21A0 + 0x3C = B + 0x21A0 + BitVec.ofNat 32 0x3C by sv_addr, w33_3c]
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
  clear w33_a44 w33_a40 w33_a3c w33_a38 w33_a34 w33_a30 w33_a2c w33_a28 w33_a24 w33_a20 w33_94 w33_90 w33_8c w33_88 w33_84 w33_80 w33_7c w33_78 w33_74 w33_70 w33_6c w33_68 w33_64 w33_60 w33_5c w33_58 w33_54 w33_50 w33_4c w33_48 w33_40 w33_3c w33_38 w33_34 w33_30 g33_10 g33_27 g33_26 g33_25 g33_23 g33_22 g33_21 g33_19 g33_18 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 rb33 s33 m33 u33 c33
  -- 0x8CE
  obtain ⟨n35, c35, u35⟩ := s34.block svDp18ce E34.self svDp18ce_end
    ⟨trivial, trivial⟩
  have m35 : n35.mem = n34.mem := u35.mem
  have s35 : St n35.mem SV n35 0x8D2 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
  have rb35 : ∀ q, reg n35 q = (runBlock svDp18ce (n34.mem, reg n34)).2 q := fun q => by rw [u35.regs]
  have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
  have t35 : Steps n0 n35 := t34.trans c35
  have fR35 : ∀ x, SvR B x → n35.mem x = n0.mem x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.same m35
  have g35_2 : reg n35 sp = B + 0x21A0 := by
    rw [rb35, runBlock_reg _ _ _ sp s34.zero (by decide), g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb35, runBlock_reg _ _ _ (3 : Fin 32) s34.zero (by decide), g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb35, runBlock_reg _ _ _ (4 : Fin 32) s34.zero (by decide), g34_4]
  have g35_8 : reg n35 (8 : Fin 32) = op := by
    rw [rb35, runBlock_reg _ _ _ (8 : Fin 32) s34.zero (by decide), g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = x9 := by
    rw [rb35, runBlock_reg _ _ _ (9 : Fin 32) s34.zero (by decide), g34_9]
  have g35_10 : reg n35 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb35, runBlock_reg _ _ _ a0 s34.zero (by decide), g34_10]
  have g35_11 : reg n35 a1 = vp := by
    rw [rb35, runBlock_reg _ _ _ a1 s34.zero (by decide), g34_11]
  have g35_18 : reg n35 (18 : Fin 32) = out := by
    rw [rb35, runBlock_reg _ _ _ (18 : Fin 32) s34.zero (by decide), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by
    rw [rb35, runBlock_reg _ _ _ (19 : Fin 32) s34.zero (by decide), g34_19]
  have g35_21 : reg n35 (21 : Fin 32) = x21 := by
    rw [rb35, runBlock_reg _ _ _ (21 : Fin 32) s34.zero (by decide), g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb35, runBlock_reg _ _ _ (22 : Fin 32) s34.zero (by decide), g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by
    rw [rb35, runBlock_reg _ _ _ (23 : Fin 32) s34.zero (by decide), g34_23]
  have g35_25 : reg n35 (25 : Fin 32) = x25 := by
    rw [rb35, runBlock_reg _ _ _ (25 : Fin 32) s34.zero (by decide), g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = x26 := by
    rw [rb35, runBlock_reg _ _ _ (26 : Fin 32) s34.zero (by decide), g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb35, runBlock_reg _ _ _ (27 : Fin 32) s34.zero (by decide), g34_27]
  have g35_13 : reg n35 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1420 := by
    rw [rb35]; simp +decide only [runBlock, BInstr.run, svDp18ce, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g34_2, g34_3, g34_4, g34_8, g34_9, g34_10, g34_11, g34_18, g34_19, g34_21, g34_22, g34_23, g34_25, g34_26, g34_27, s34.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w35_30 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m35]; exact w34_30
  have w35_34 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m35]; exact w34_34
  have w35_38 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m35]; exact w34_38
  have w35_3c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m35]; exact w34_3c
  have w35_40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m35]; exact w34_40
  have w35_48 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m35]; exact w34_48
  have w35_4c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m35]; exact w34_4c
  have w35_50 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m35]; exact w34_50
  have w35_54 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m35]; exact w34_54
  have w35_58 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m35]; exact w34_58
  have w35_5c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m35]; exact w34_5c
  have w35_60 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m35]; exact w34_60
  have w35_64 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m35]; exact w34_64
  have w35_68 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m35]; exact w34_68
  have w35_6c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m35]; exact w34_6c
  have w35_70 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m35]; exact w34_70
  have w35_74 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m35]; exact w34_74
  have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m35]; exact w34_78
  have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m35]; exact w34_7c
  have w35_80 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m35]; exact w34_80
  have w35_84 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m35]; exact w34_84
  have w35_88 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m35]; exact w34_88
  have w35_8c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m35]; exact w34_8c
  have w35_90 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m35]; exact w34_90
  have w35_94 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m35]; exact w34_94
  have w35_a20 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m35]; exact w34_a20
  have w35_a24 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m35]; exact w34_a24
  have w35_a28 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m35]; exact w34_a28
  have w35_a2c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m35]; exact w34_a2c
  have w35_a30 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m35]; exact w34_a30
  have w35_a34 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m35]; exact w34_a34
  have w35_a38 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m35]; exact w34_a38
  have w35_a3c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m35]; exact w34_a3c
  have w35_a40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m35]; exact w34_a40
  have w35_a44 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m35]; exact w34_a44
  clear w34_a44 w34_a40 w34_a3c w34_a38 w34_a34 w34_a30 w34_a2c w34_a28 w34_a24 w34_a20 w34_94 w34_90 w34_8c w34_88 w34_84 w34_80 w34_7c w34_78 w34_74 w34_70 w34_6c w34_68 w34_64 w34_60 w34_5c w34_58 w34_54 w34_50 w34_4c w34_48 w34_40 w34_3c w34_38 w34_34 w34_30 g34_11 g34_27 g34_26 g34_25 g34_23 g34_22 g34_21 g34_19 g34_18 g34_10 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 m34 s34 u34 d34
  -- 0x8D2: sw
  obtain ⟨n36, d36, s36, fr36, K36, W36, rg36⟩ := sv_sw F E35 s35 sv_at_8d2 (off' := 0x8D4) (c := 0x1480)
    (by decide) (by rw [g35_13]; sv_addr) (by decide) (by decide)
  have t36 : Steps n0 n36 := t35.trans d36
  have fR36 : ∀ x, SvR B x → n36.mem x = n0.mem x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.keep K36 (by decide)
  have g36_2 : reg n36 sp = B + 0x21A0 := by rw [rg36 sp, g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg36 (3 : Fin 32), g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg36 (4 : Fin 32), g35_4]
  have g36_8 : reg n36 (8 : Fin 32) = op := by rw [rg36 (8 : Fin 32), g35_8]
  have g36_9 : reg n36 (9 : Fin 32) = x9 := by rw [rg36 (9 : Fin 32), g35_9]
  have g36_10 : reg n36 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg36 a0, g35_10]
  have g36_11 : reg n36 a1 = vp := by rw [rg36 a1, g35_11]
  have g36_13 : reg n36 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1420 := by rw [rg36 a3, g35_13]
  have g36_18 : reg n36 (18 : Fin 32) = out := by rw [rg36 (18 : Fin 32), g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [rg36 (19 : Fin 32), g35_19]
  have g36_21 : reg n36 (21 : Fin 32) = x21 := by rw [rg36 (21 : Fin 32), g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg36 (22 : Fin 32), g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [rg36 (23 : Fin 32), g35_23]
  have g36_25 : reg n36 (25 : Fin 32) = x25 := by rw [rg36 (25 : Fin 32), g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = x26 := by rw [rg36 (26 : Fin 32), g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg36 (27 : Fin 32), g35_27]
  have w36_30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K36.w32 (by decide) (by decide)).trans w35_30
  have w36_34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K36.w32 (by decide) (by decide)).trans w35_34
  have w36_38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K36.w32 (by decide) (by decide)).trans w35_38
  have w36_3c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K36.w32 (by decide) (by decide)).trans w35_3c
  have w36_40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K36.w32 (by decide) (by decide)).trans w35_40
  have w36_48 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K36.w32 (by decide) (by decide)).trans w35_48
  have w36_4c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K36.w32 (by decide) (by decide)).trans w35_4c
  have w36_50 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K36.w32 (by decide) (by decide)).trans w35_50
  have w36_54 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K36.w32 (by decide) (by decide)).trans w35_54
  have w36_58 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K36.w32 (by decide) (by decide)).trans w35_58
  have w36_5c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K36.w32 (by decide) (by decide)).trans w35_5c
  have w36_60 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K36.w32 (by decide) (by decide)).trans w35_60
  have w36_64 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K36.w32 (by decide) (by decide)).trans w35_64
  have w36_68 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K36.w32 (by decide) (by decide)).trans w35_68
  have w36_6c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K36.w32 (by decide) (by decide)).trans w35_6c
  have w36_70 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K36.w32 (by decide) (by decide)).trans w35_70
  have w36_74 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K36.w32 (by decide) (by decide)).trans w35_74
  have w36_78 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K36.w32 (by decide) (by decide)).trans w35_78
  have w36_7c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K36.w32 (by decide) (by decide)).trans w35_7c
  have w36_80 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K36.w32 (by decide) (by decide)).trans w35_80
  have w36_84 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K36.w32 (by decide) (by decide)).trans w35_84
  have w36_88 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K36.w32 (by decide) (by decide)).trans w35_88
  have w36_8c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K36.w32 (by decide) (by decide)).trans w35_8c
  have w36_90 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K36.w32 (by decide) (by decide)).trans w35_90
  have w36_94 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K36.w32 (by decide) (by decide)).trans w35_94
  have w36_a20 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K36.w32 (by decide) (by decide)).trans w35_a20
  have w36_a24 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K36.w32 (by decide) (by decide)).trans w35_a24
  have w36_a28 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K36.w32 (by decide) (by decide)).trans w35_a28
  have w36_a2c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K36.w32 (by decide) (by decide)).trans w35_a2c
  have w36_a30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K36.w32 (by decide) (by decide)).trans w35_a30
  have w36_a34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K36.w32 (by decide) (by decide)).trans w35_a34
  have w36_a38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K36.w32 (by decide) (by decide)).trans w35_a38
  have w36_a3c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K36.w32 (by decide) (by decide)).trans w35_a3c
  have w36_a40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K36.w32 (by decide) (by decide)).trans w35_a40
  have w36_a44 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K36.w32 (by decide) (by decide)).trans w35_a44
  have w36_1480 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [W36, g35_11]
  clear w35_a44 w35_a40 w35_a3c w35_a38 w35_a34 w35_a30 w35_a2c w35_a28 w35_a24 w35_a20 w35_94 w35_90 w35_8c w35_88 w35_84 w35_80 w35_7c w35_78 w35_74 w35_70 w35_6c w35_68 w35_64 w35_60 w35_5c w35_58 w35_54 w35_50 w35_4c w35_48 w35_40 w35_3c w35_38 w35_34 w35_30 g35_13 g35_27 g35_26 g35_25 g35_23 g35_22 g35_21 g35_19 g35_18 g35_11 g35_10 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 rb35 s35 m35 u35 c35
  -- 0x8D4: lw
  obtain ⟨n37, d37, u37⟩ := s36.lw E36.self sv_at_8d4 (off' := 0x8D6) (by decide)
    (by rw [g36_2, show B + 0x21A0 + 0x38 = B + 0x21A0 + BitVec.ofNat 32 0x38 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s37 : St n37.mem SV n37 0x8D6 (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
  have m37 : n37.mem = n36.mem := u37.mem
  have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
  have t37 : Steps n0 n37 := t36.trans (.single d37)
  have fR37 : ∀ x, SvR B x → n37.mem x = n0.mem x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : SvCode n37.mem := E36.fr F fr37
  have V37 : SvSaves B n37.mem v := V36.same m37
  have g37_2 : reg n37 sp = B + 0x21A0 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u37.regs, upd_ne (by decide) (by decide), g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u37.regs, upd_ne (by decide) (by decide), g36_4]
  have g37_8 : reg n37 (8 : Fin 32) = op := by rw [u37.regs, upd_ne (by decide) (by decide), g36_8]
  have g37_9 : reg n37 (9 : Fin 32) = x9 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_9]
  have g37_10 : reg n37 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_10]
  have g37_11 : reg n37 a1 = vp := by rw [u37.regs, upd_ne (by decide) (by decide), g36_11]
  have g37_13 : reg n37 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1420 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_13]
  have g37_18 : reg n37 (18 : Fin 32) = out := by rw [u37.regs, upd_ne (by decide) (by decide), g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [u37.regs, upd_ne (by decide) (by decide), g36_19]
  have g37_21 : reg n37 (21 : Fin 32) = x21 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_21]
  have g37_22 : reg n37 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_22]
  have g37_23 : reg n37 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u37.regs, upd_ne (by decide) (by decide), g36_23]
  have g37_25 : reg n37 (25 : Fin 32) = x25 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_25]
  have g37_26 : reg n37 (26 : Fin 32) = x26 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_26]
  have g37_27 : reg n37 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_27]
  have g37_12 : reg n37 a2 = vl := by
    rw [u37.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g36_2, show B + 0x21A0 + 0x38 = B + 0x21A0 + BitVec.ofNat 32 0x38 by sv_addr, w36_38]
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
  have w37_1480 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m37]; exact w36_1480
  clear w36_1480 w36_a44 w36_a40 w36_a3c w36_a38 w36_a34 w36_a30 w36_a2c w36_a28 w36_a24 w36_a20 w36_94 w36_90 w36_8c w36_88 w36_84 w36_80 w36_7c w36_78 w36_74 w36_70 w36_6c w36_68 w36_64 w36_60 w36_5c w36_58 w36_54 w36_50 w36_4c w36_48 w36_40 w36_3c w36_38 w36_34 w36_30 g36_27 g36_26 g36_25 g36_23 g36_22 g36_21 g36_19 g36_18 g36_13 g36_11 g36_10 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 rg36 W36 K36 fr36 s36 d36
  -- 0x8D6: sw
  obtain ⟨n38, d38, s38, fr38, K38, W38, rg38⟩ := sv_sw F E37 s37 sv_at_8d6 (off' := 0x8D8) (c := 0x1484)
    (by decide) (by rw [g37_13]; sv_addr) (by decide) (by decide)
  have t38 : Steps n0 n38 := t37.trans d38
  have fR38 : ∀ x, SvR B x → n38.mem x = n0.mem x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : SvCode n38.mem := E37.fr F fr38
  have V38 : SvSaves B n38.mem v := V37.keep K38 (by decide)
  have g38_2 : reg n38 sp = B + 0x21A0 := by rw [rg38 sp, g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg38 (3 : Fin 32), g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg38 (4 : Fin 32), g37_4]
  have g38_8 : reg n38 (8 : Fin 32) = op := by rw [rg38 (8 : Fin 32), g37_8]
  have g38_9 : reg n38 (9 : Fin 32) = x9 := by rw [rg38 (9 : Fin 32), g37_9]
  have g38_10 : reg n38 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg38 a0, g37_10]
  have g38_11 : reg n38 a1 = vp := by rw [rg38 a1, g37_11]
  have g38_12 : reg n38 a2 = vl := by rw [rg38 a2, g37_12]
  have g38_13 : reg n38 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1420 := by rw [rg38 a3, g37_13]
  have g38_18 : reg n38 (18 : Fin 32) = out := by rw [rg38 (18 : Fin 32), g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [rg38 (19 : Fin 32), g37_19]
  have g38_21 : reg n38 (21 : Fin 32) = x21 := by rw [rg38 (21 : Fin 32), g37_21]
  have g38_22 : reg n38 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg38 (22 : Fin 32), g37_22]
  have g38_23 : reg n38 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [rg38 (23 : Fin 32), g37_23]
  have g38_25 : reg n38 (25 : Fin 32) = x25 := by rw [rg38 (25 : Fin 32), g37_25]
  have g38_26 : reg n38 (26 : Fin 32) = x26 := by rw [rg38 (26 : Fin 32), g37_26]
  have g38_27 : reg n38 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg38 (27 : Fin 32), g37_27]
  have w38_30 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K38.w32 (by decide) (by decide)).trans w37_30
  have w38_34 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K38.w32 (by decide) (by decide)).trans w37_34
  have w38_38 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K38.w32 (by decide) (by decide)).trans w37_38
  have w38_3c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K38.w32 (by decide) (by decide)).trans w37_3c
  have w38_40 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K38.w32 (by decide) (by decide)).trans w37_40
  have w38_48 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K38.w32 (by decide) (by decide)).trans w37_48
  have w38_4c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K38.w32 (by decide) (by decide)).trans w37_4c
  have w38_50 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K38.w32 (by decide) (by decide)).trans w37_50
  have w38_54 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K38.w32 (by decide) (by decide)).trans w37_54
  have w38_58 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K38.w32 (by decide) (by decide)).trans w37_58
  have w38_5c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K38.w32 (by decide) (by decide)).trans w37_5c
  have w38_60 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K38.w32 (by decide) (by decide)).trans w37_60
  have w38_64 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K38.w32 (by decide) (by decide)).trans w37_64
  have w38_68 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K38.w32 (by decide) (by decide)).trans w37_68
  have w38_6c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K38.w32 (by decide) (by decide)).trans w37_6c
  have w38_70 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K38.w32 (by decide) (by decide)).trans w37_70
  have w38_74 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K38.w32 (by decide) (by decide)).trans w37_74
  have w38_78 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K38.w32 (by decide) (by decide)).trans w37_78
  have w38_7c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K38.w32 (by decide) (by decide)).trans w37_7c
  have w38_80 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K38.w32 (by decide) (by decide)).trans w37_80
  have w38_84 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K38.w32 (by decide) (by decide)).trans w37_84
  have w38_88 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K38.w32 (by decide) (by decide)).trans w37_88
  have w38_8c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K38.w32 (by decide) (by decide)).trans w37_8c
  have w38_90 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K38.w32 (by decide) (by decide)).trans w37_90
  have w38_94 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K38.w32 (by decide) (by decide)).trans w37_94
  have w38_a20 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K38.w32 (by decide) (by decide)).trans w37_a20
  have w38_a24 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K38.w32 (by decide) (by decide)).trans w37_a24
  have w38_a28 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K38.w32 (by decide) (by decide)).trans w37_a28
  have w38_a2c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K38.w32 (by decide) (by decide)).trans w37_a2c
  have w38_a30 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K38.w32 (by decide) (by decide)).trans w37_a30
  have w38_a34 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K38.w32 (by decide) (by decide)).trans w37_a34
  have w38_a38 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K38.w32 (by decide) (by decide)).trans w37_a38
  have w38_a3c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K38.w32 (by decide) (by decide)).trans w37_a3c
  have w38_a40 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K38.w32 (by decide) (by decide)).trans w37_a40
  have w38_a44 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K38.w32 (by decide) (by decide)).trans w37_a44
  have w38_1480 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K38.w32 (by decide) (by decide)).trans w37_1480
  have w38_1484 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [W38, g37_12]
  clear w37_1480 w37_a44 w37_a40 w37_a3c w37_a38 w37_a34 w37_a30 w37_a2c w37_a28 w37_a24 w37_a20 w37_94 w37_90 w37_8c w37_88 w37_84 w37_80 w37_7c w37_78 w37_74 w37_70 w37_6c w37_68 w37_64 w37_60 w37_5c w37_58 w37_54 w37_50 w37_4c w37_48 w37_40 w37_3c w37_38 w37_34 w37_30 g37_12 g37_27 g37_26 g37_25 g37_23 g37_22 g37_21 g37_19 g37_18 g37_13 g37_11 g37_10 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 m37 s37 u37 d37
  -- 0x8D8: sw
  obtain ⟨n39, d39, s39, fr39, K39, W39, rg39⟩ := sv_sw F E38 s38 sv_at_8d8 (off' := 0x8DA) (c := 0x1488)
    (by decide) (by rw [g38_13]; sv_addr) (by decide) (by decide)
  have t39 : Steps n0 n39 := t38.trans d39
  have fR39 : ∀ x, SvR B x → n39.mem x = n0.mem x := fun x hx => (fr39 x hx).trans (fR38 x hx)
  have E39 : SvCode n39.mem := E38.fr F fr39
  have V39 : SvSaves B n39.mem v := V38.keep K39 (by decide)
  have g39_2 : reg n39 sp = B + 0x21A0 := by rw [rg39 sp, g38_2]
  have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg39 (3 : Fin 32), g38_3]
  have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg39 (4 : Fin 32), g38_4]
  have g39_8 : reg n39 (8 : Fin 32) = op := by rw [rg39 (8 : Fin 32), g38_8]
  have g39_9 : reg n39 (9 : Fin 32) = x9 := by rw [rg39 (9 : Fin 32), g38_9]
  have g39_10 : reg n39 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg39 a0, g38_10]
  have g39_11 : reg n39 a1 = vp := by rw [rg39 a1, g38_11]
  have g39_12 : reg n39 a2 = vl := by rw [rg39 a2, g38_12]
  have g39_13 : reg n39 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1420 := by rw [rg39 a3, g38_13]
  have g39_18 : reg n39 (18 : Fin 32) = out := by rw [rg39 (18 : Fin 32), g38_18]
  have g39_19 : reg n39 (19 : Fin 32) = bp := by rw [rg39 (19 : Fin 32), g38_19]
  have g39_21 : reg n39 (21 : Fin 32) = x21 := by rw [rg39 (21 : Fin 32), g38_21]
  have g39_22 : reg n39 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg39 (22 : Fin 32), g38_22]
  have g39_23 : reg n39 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [rg39 (23 : Fin 32), g38_23]
  have g39_25 : reg n39 (25 : Fin 32) = x25 := by rw [rg39 (25 : Fin 32), g38_25]
  have g39_26 : reg n39 (26 : Fin 32) = x26 := by rw [rg39 (26 : Fin 32), g38_26]
  have g39_27 : reg n39 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg39 (27 : Fin 32), g38_27]
  have w39_30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K39.w32 (by decide) (by decide)).trans w38_30
  have w39_34 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K39.w32 (by decide) (by decide)).trans w38_34
  have w39_38 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K39.w32 (by decide) (by decide)).trans w38_38
  have w39_3c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K39.w32 (by decide) (by decide)).trans w38_3c
  have w39_40 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K39.w32 (by decide) (by decide)).trans w38_40
  have w39_48 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K39.w32 (by decide) (by decide)).trans w38_48
  have w39_4c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K39.w32 (by decide) (by decide)).trans w38_4c
  have w39_50 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K39.w32 (by decide) (by decide)).trans w38_50
  have w39_54 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K39.w32 (by decide) (by decide)).trans w38_54
  have w39_58 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K39.w32 (by decide) (by decide)).trans w38_58
  have w39_5c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K39.w32 (by decide) (by decide)).trans w38_5c
  have w39_60 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K39.w32 (by decide) (by decide)).trans w38_60
  have w39_64 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K39.w32 (by decide) (by decide)).trans w38_64
  have w39_68 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K39.w32 (by decide) (by decide)).trans w38_68
  have w39_6c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K39.w32 (by decide) (by decide)).trans w38_6c
  have w39_70 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K39.w32 (by decide) (by decide)).trans w38_70
  have w39_74 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K39.w32 (by decide) (by decide)).trans w38_74
  have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K39.w32 (by decide) (by decide)).trans w38_78
  have w39_7c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K39.w32 (by decide) (by decide)).trans w38_7c
  have w39_80 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K39.w32 (by decide) (by decide)).trans w38_80
  have w39_84 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K39.w32 (by decide) (by decide)).trans w38_84
  have w39_88 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K39.w32 (by decide) (by decide)).trans w38_88
  have w39_8c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K39.w32 (by decide) (by decide)).trans w38_8c
  have w39_90 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K39.w32 (by decide) (by decide)).trans w38_90
  have w39_94 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K39.w32 (by decide) (by decide)).trans w38_94
  have w39_a20 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K39.w32 (by decide) (by decide)).trans w38_a20
  have w39_a24 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K39.w32 (by decide) (by decide)).trans w38_a24
  have w39_a28 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K39.w32 (by decide) (by decide)).trans w38_a28
  have w39_a2c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K39.w32 (by decide) (by decide)).trans w38_a2c
  have w39_a30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K39.w32 (by decide) (by decide)).trans w38_a30
  have w39_a34 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K39.w32 (by decide) (by decide)).trans w38_a34
  have w39_a38 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K39.w32 (by decide) (by decide)).trans w38_a38
  have w39_a3c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K39.w32 (by decide) (by decide)).trans w38_a3c
  have w39_a40 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K39.w32 (by decide) (by decide)).trans w38_a40
  have w39_a44 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K39.w32 (by decide) (by decide)).trans w38_a44
  have w39_1480 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K39.w32 (by decide) (by decide)).trans w38_1480
  have w39_1484 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K39.w32 (by decide) (by decide)).trans w38_1484
  have w39_1488 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = vp := by rw [W39, g38_11]
  clear w38_1484 w38_1480 w38_a44 w38_a40 w38_a3c w38_a38 w38_a34 w38_a30 w38_a2c w38_a28 w38_a24 w38_a20 w38_94 w38_90 w38_8c w38_88 w38_84 w38_80 w38_7c w38_78 w38_74 w38_70 w38_6c w38_68 w38_64 w38_60 w38_5c w38_58 w38_54 w38_50 w38_4c w38_48 w38_40 w38_3c w38_38 w38_34 w38_30 g38_27 g38_26 g38_25 g38_23 g38_22 g38_21 g38_19 g38_18 g38_13 g38_12 g38_11 g38_10 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 rg38 W38 K38 fr38 s38 d38
  -- 0x8DA
  obtain ⟨n40, c40, u40⟩ := s39.block svDp18da E39.self svDp18da_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m40 : n40.mem = n39.mem := u40.mem
  have s40 : St n40.mem SV n40 0x8E4 (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
  have rb40 : ∀ q, reg n40 q = (runBlock svDp18da (n39.mem, reg n39)).2 q := fun q => by rw [u40.regs]
  have fr40 : ∀ x, SvR B x → n40.mem x = n39.mem x := fun x _ => by rw [m40]
  have t40 : Steps n0 n40 := t39.trans c40
  have fR40 : ∀ x, SvR B x → n40.mem x = n0.mem x := fun x hx => (fr40 x hx).trans (fR39 x hx)
  have E40 : SvCode n40.mem := E39.fr F fr40
  have V40 : SvSaves B n40.mem v := V39.same m40
  have g40_2 : reg n40 sp = B + 0x21A0 := by
    rw [rb40, runBlock_reg _ _ _ sp s39.zero (by decide), g39_2]
  have g40_3 : reg n40 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb40, runBlock_reg _ _ _ (3 : Fin 32) s39.zero (by decide), g39_3]
  have g40_4 : reg n40 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb40, runBlock_reg _ _ _ (4 : Fin 32) s39.zero (by decide), g39_4]
  have g40_9 : reg n40 (9 : Fin 32) = x9 := by
    rw [rb40, runBlock_reg _ _ _ (9 : Fin 32) s39.zero (by decide), g39_9]
  have g40_10 : reg n40 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb40, runBlock_reg _ _ _ a0 s39.zero (by decide), g39_10]
  have g40_12 : reg n40 a2 = vl := by
    rw [rb40, runBlock_reg _ _ _ a2 s39.zero (by decide), g39_12]
  have g40_13 : reg n40 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1420 := by
    rw [rb40, runBlock_reg _ _ _ a3 s39.zero (by decide), g39_13]
  have g40_18 : reg n40 (18 : Fin 32) = out := by
    rw [rb40, runBlock_reg _ _ _ (18 : Fin 32) s39.zero (by decide), g39_18]
  have g40_19 : reg n40 (19 : Fin 32) = bp := by
    rw [rb40, runBlock_reg _ _ _ (19 : Fin 32) s39.zero (by decide), g39_19]
  have g40_21 : reg n40 (21 : Fin 32) = x21 := by
    rw [rb40, runBlock_reg _ _ _ (21 : Fin 32) s39.zero (by decide), g39_21]
  have g40_22 : reg n40 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb40, runBlock_reg _ _ _ (22 : Fin 32) s39.zero (by decide), g39_22]
  have g40_23 : reg n40 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by
    rw [rb40, runBlock_reg _ _ _ (23 : Fin 32) s39.zero (by decide), g39_23]
  have g40_25 : reg n40 (25 : Fin 32) = x25 := by
    rw [rb40, runBlock_reg _ _ _ (25 : Fin 32) s39.zero (by decide), g39_25]
  have g40_26 : reg n40 (26 : Fin 32) = x26 := by
    rw [rb40, runBlock_reg _ _ _ (26 : Fin 32) s39.zero (by decide), g39_26]
  have g40_27 : reg n40 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb40, runBlock_reg _ _ _ (27 : Fin 32) s39.zero (by decide), g39_27]
  have g40_8 : reg n40 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb40]; simp +decide only [runBlock, BInstr.run, svDp18da, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g39_2, g39_3, g39_4, g39_8, g39_9, g39_10, g39_11, g39_12, g39_13, g39_18, g39_19, g39_21, g39_22, g39_23, g39_25, g39_26, g39_27, s39.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g40_11 : reg n40 a1 = BitVec.ofNat 32 0x1320 := by
    rw [rb40]; simp +decide only [runBlock, BInstr.run, svDp18da, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g39_2, g39_3, g39_4, g39_8, g39_9, g39_10, g39_11, g39_12, g39_13, g39_18, g39_19, g39_21, g39_22, g39_23, g39_25, g39_26, g39_27, s39.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have w40_1480 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m40]; exact w39_1480
  have w40_1484 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m40]; exact w39_1484
  have w40_1488 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = vp := by rw [m40]; exact w39_1488
  clear w39_1488 w39_1484 w39_1480 w39_a44 w39_a40 w39_a3c w39_a38 w39_a34 w39_a30 w39_a2c w39_a28 w39_a24 w39_a20 w39_94 w39_90 w39_8c w39_88 w39_84 w39_80 w39_7c w39_78 w39_74 w39_70 w39_6c w39_68 w39_64 w39_60 w39_5c w39_58 w39_54 w39_50 w39_4c w39_48 w39_40 w39_3c w39_38 w39_34 w39_30 g39_27 g39_26 g39_25 g39_23 g39_22 g39_21 g39_19 g39_18 g39_13 g39_12 g39_11 g39_10 g39_9 g39_8 g39_4 g39_3 g39_2 V39 E39 fR39 t39 rg39 W39 K39 fr39 s39 d39
  -- 0x8E4: sw
  obtain ⟨n41, d41, s41, fr41, K41, W41, rg41⟩ := sv_sw F E40 s40 sv_at_8e4 (off' := 0x8E6) (c := 0x148C)
    (by decide) (by rw [g40_13]; sv_addr) (by decide) (by decide)
  have t41 : Steps n0 n41 := t40.trans d41
  have fR41 : ∀ x, SvR B x → n41.mem x = n0.mem x := fun x hx => (fr41 x hx).trans (fR40 x hx)
  have E41 : SvCode n41.mem := E40.fr F fr41
  have V41 : SvSaves B n41.mem v := V40.keep K41 (by decide)
  have g41_2 : reg n41 sp = B + 0x21A0 := by rw [rg41 sp, g40_2]
  have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg41 (3 : Fin 32), g40_3]
  have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg41 (4 : Fin 32), g40_4]
  have g41_8 : reg n41 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg41 (8 : Fin 32), g40_8]
  have g41_9 : reg n41 (9 : Fin 32) = x9 := by rw [rg41 (9 : Fin 32), g40_9]
  have g41_10 : reg n41 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg41 a0, g40_10]
  have g41_11 : reg n41 a1 = BitVec.ofNat 32 0x1320 := by rw [rg41 a1, g40_11]
  have g41_12 : reg n41 a2 = vl := by rw [rg41 a2, g40_12]
  have g41_13 : reg n41 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1420 := by rw [rg41 a3, g40_13]
  have g41_18 : reg n41 (18 : Fin 32) = out := by rw [rg41 (18 : Fin 32), g40_18]
  have g41_19 : reg n41 (19 : Fin 32) = bp := by rw [rg41 (19 : Fin 32), g40_19]
  have g41_21 : reg n41 (21 : Fin 32) = x21 := by rw [rg41 (21 : Fin 32), g40_21]
  have g41_22 : reg n41 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg41 (22 : Fin 32), g40_22]
  have g41_23 : reg n41 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [rg41 (23 : Fin 32), g40_23]
  have g41_25 : reg n41 (25 : Fin 32) = x25 := by rw [rg41 (25 : Fin 32), g40_25]
  have g41_26 : reg n41 (26 : Fin 32) = x26 := by rw [rg41 (26 : Fin 32), g40_26]
  have g41_27 : reg n41 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg41 (27 : Fin 32), g40_27]
  have w41_30 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K41.w32 (by decide) (by decide)).trans w40_30
  have w41_34 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K41.w32 (by decide) (by decide)).trans w40_34
  have w41_38 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K41.w32 (by decide) (by decide)).trans w40_38
  have w41_3c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K41.w32 (by decide) (by decide)).trans w40_3c
  have w41_40 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K41.w32 (by decide) (by decide)).trans w40_40
  have w41_48 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K41.w32 (by decide) (by decide)).trans w40_48
  have w41_4c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K41.w32 (by decide) (by decide)).trans w40_4c
  have w41_50 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K41.w32 (by decide) (by decide)).trans w40_50
  have w41_54 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K41.w32 (by decide) (by decide)).trans w40_54
  have w41_58 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K41.w32 (by decide) (by decide)).trans w40_58
  have w41_5c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K41.w32 (by decide) (by decide)).trans w40_5c
  have w41_60 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K41.w32 (by decide) (by decide)).trans w40_60
  have w41_64 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K41.w32 (by decide) (by decide)).trans w40_64
  have w41_68 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K41.w32 (by decide) (by decide)).trans w40_68
  have w41_6c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K41.w32 (by decide) (by decide)).trans w40_6c
  have w41_70 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K41.w32 (by decide) (by decide)).trans w40_70
  have w41_74 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K41.w32 (by decide) (by decide)).trans w40_74
  have w41_78 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K41.w32 (by decide) (by decide)).trans w40_78
  have w41_7c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K41.w32 (by decide) (by decide)).trans w40_7c
  have w41_80 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K41.w32 (by decide) (by decide)).trans w40_80
  have w41_84 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K41.w32 (by decide) (by decide)).trans w40_84
  have w41_88 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K41.w32 (by decide) (by decide)).trans w40_88
  have w41_8c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K41.w32 (by decide) (by decide)).trans w40_8c
  have w41_90 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K41.w32 (by decide) (by decide)).trans w40_90
  have w41_94 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K41.w32 (by decide) (by decide)).trans w40_94
  have w41_a20 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K41.w32 (by decide) (by decide)).trans w40_a20
  have w41_a24 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K41.w32 (by decide) (by decide)).trans w40_a24
  have w41_a28 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K41.w32 (by decide) (by decide)).trans w40_a28
  have w41_a2c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K41.w32 (by decide) (by decide)).trans w40_a2c
  have w41_a30 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K41.w32 (by decide) (by decide)).trans w40_a30
  have w41_a34 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K41.w32 (by decide) (by decide)).trans w40_a34
  have w41_a38 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K41.w32 (by decide) (by decide)).trans w40_a38
  have w41_a3c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K41.w32 (by decide) (by decide)).trans w40_a3c
  have w41_a40 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K41.w32 (by decide) (by decide)).trans w40_a40
  have w41_a44 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K41.w32 (by decide) (by decide)).trans w40_a44
  have w41_1480 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K41.w32 (by decide) (by decide)).trans w40_1480
  have w41_1484 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K41.w32 (by decide) (by decide)).trans w40_1484
  have w41_1488 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = vp := (K41.w32 (by decide) (by decide)).trans w40_1488
  have w41_148c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = vl := by rw [W41, g40_12]
  clear w40_1488 w40_1484 w40_1480 w40_a44 w40_a40 w40_a3c w40_a38 w40_a34 w40_a30 w40_a2c w40_a28 w40_a24 w40_a20 w40_94 w40_90 w40_8c w40_88 w40_84 w40_80 w40_7c w40_78 w40_74 w40_70 w40_6c w40_68 w40_64 w40_60 w40_5c w40_58 w40_54 w40_50 w40_4c w40_48 w40_40 w40_3c w40_38 w40_34 w40_30 g40_11 g40_8 g40_27 g40_26 g40_25 g40_23 g40_22 g40_21 g40_19 g40_18 g40_13 g40_12 g40_10 g40_9 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 rb40 s40 m40 u40 c40
  -- 0x8E6
  obtain ⟨n42, c42, u42⟩ := s41.block svDp18e6 E41.self svDp18e6_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m42 : n42.mem = n41.mem := u42.mem
  have s42 : St n42.mem SV n42 0x8F6 (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
  have rb42 : ∀ q, reg n42 q = (runBlock svDp18e6 (n41.mem, reg n41)).2 q := fun q => by rw [u42.regs]
  have fr42 : ∀ x, SvR B x → n42.mem x = n41.mem x := fun x _ => by rw [m42]
  have t42 : Steps n0 n42 := t41.trans c42
  have fR42 : ∀ x, SvR B x → n42.mem x = n0.mem x := fun x hx => (fr42 x hx).trans (fR41 x hx)
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
  have g42_12 : reg n42 a2 = vl := by
    rw [rb42, runBlock_reg _ _ _ a2 s41.zero (by decide), g41_12]
  have g42_13 : reg n42 a3 = B + 0x21A0 + BitVec.ofNat 32 0x1420 := by
    rw [rb42, runBlock_reg _ _ _ a3 s41.zero (by decide), g41_13]
  have g42_18 : reg n42 (18 : Fin 32) = out := by
    rw [rb42, runBlock_reg _ _ _ (18 : Fin 32) s41.zero (by decide), g41_18]
  have g42_19 : reg n42 (19 : Fin 32) = bp := by
    rw [rb42, runBlock_reg _ _ _ (19 : Fin 32) s41.zero (by decide), g41_19]
  have g42_21 : reg n42 (21 : Fin 32) = x21 := by
    rw [rb42, runBlock_reg _ _ _ (21 : Fin 32) s41.zero (by decide), g41_21]
  have g42_22 : reg n42 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb42, runBlock_reg _ _ _ (22 : Fin 32) s41.zero (by decide), g41_22]
  have g42_23 : reg n42 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by
    rw [rb42, runBlock_reg _ _ _ (23 : Fin 32) s41.zero (by decide), g41_23]
  have g42_25 : reg n42 (25 : Fin 32) = x25 := by
    rw [rb42, runBlock_reg _ _ _ (25 : Fin 32) s41.zero (by decide), g41_25]
  have g42_26 : reg n42 (26 : Fin 32) = x26 := by
    rw [rb42, runBlock_reg _ _ _ (26 : Fin 32) s41.zero (by decide), g41_26]
  have g42_27 : reg n42 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb42, runBlock_reg _ _ _ (27 : Fin 32) s41.zero (by decide), g41_27]
  have g42_10 : reg n42 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by
    rw [rb42]; simp +decide only [runBlock, BInstr.run, svDp18e6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_11, g41_12, g41_13, g41_18, g41_19, g41_21, g41_22, g41_23, g41_25, g41_26, g41_27, s41.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g42_11 : reg n42 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1480 := by
    rw [rb42]; simp +decide only [runBlock, BInstr.run, svDp18e6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_11, g41_12, g41_13, g41_18, g41_19, g41_21, g41_22, g41_23, g41_25, g41_26, g41_27, s41.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have w42_1480 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m42]; exact w41_1480
  have w42_1484 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m42]; exact w41_1484
  have w42_1488 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = vp := by rw [m42]; exact w41_1488
  have w42_148c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = vl := by rw [m42]; exact w41_148c
  clear w41_148c w41_1488 w41_1484 w41_1480 w41_a44 w41_a40 w41_a3c w41_a38 w41_a34 w41_a30 w41_a2c w41_a28 w41_a24 w41_a20 w41_94 w41_90 w41_8c w41_88 w41_84 w41_80 w41_7c w41_78 w41_74 w41_70 w41_6c w41_68 w41_64 w41_60 w41_5c w41_58 w41_54 w41_50 w41_4c w41_48 w41_40 w41_3c w41_38 w41_34 w41_30 g41_27 g41_26 g41_25 g41_23 g41_22 g41_21 g41_19 g41_18 g41_13 g41_12 g41_11 g41_10 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 rg41 W41 K41 fr41 s41 d41
  -- 0x8F6: sv_tlvF
  obtain ⟨n43, c43, s43, rk43, K43, Ok43, Er43, fr43⟩ := sv_tlvF (oc := 0x1020) (dc := 0x1480)
    F E42 s42 sv_at_8f6 sv_at_8fa (by decide) (by decide) g42_10
    g42_11 (by decide) (by decide) (by decide) (by decide) (by decide)
    w42_1488 w42_148c
  have t43 : Steps n0 n43 := t42.trans c43
  have fR43 : ∀ x, SvR B x → n43.mem x = n0.mem x := fun x hx => (fr43 x hx).trans (fR42 x hx)
  have E43 : SvCode n43.mem := E42.fr F fr43
  have V43 : SvSaves B n43.mem v := V42.keepL K43 (by decide)
  rw [sv_mb fR42 val_in] at Ok43 Er43
  have g43_2 : reg n43 sp = B + 0x21A0 := by rw [rk43 sp (by decide) (by decide), g42_2]
  have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk43 (3 : Fin 32) (by decide) (by decide), g42_3]
  have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk43 (4 : Fin 32) (by decide) (by decide), g42_4]
  have g43_8 : reg n43 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rk43 (8 : Fin 32) (by decide) (by decide), g42_8]
  have g43_9 : reg n43 (9 : Fin 32) = x9 := by rw [rk43 (9 : Fin 32) (by decide) (by decide), g42_9]
  have g43_10 : reg n43 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by rw [rk43 a0 (by decide) (by decide), g42_10]
  have g43_18 : reg n43 (18 : Fin 32) = out := by rw [rk43 (18 : Fin 32) (by decide) (by decide), g42_18]
  have g43_19 : reg n43 (19 : Fin 32) = bp := by rw [rk43 (19 : Fin 32) (by decide) (by decide), g42_19]
  have g43_21 : reg n43 (21 : Fin 32) = x21 := by rw [rk43 (21 : Fin 32) (by decide) (by decide), g42_21]
  have g43_22 : reg n43 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rk43 (22 : Fin 32) (by decide) (by decide), g42_22]
  have g43_23 : reg n43 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [rk43 (23 : Fin 32) (by decide) (by decide), g42_23]
  have g43_25 : reg n43 (25 : Fin 32) = x25 := by rw [rk43 (25 : Fin 32) (by decide) (by decide), g42_25]
  have g43_26 : reg n43 (26 : Fin 32) = x26 := by rw [rk43 (26 : Fin 32) (by decide) (by decide), g42_26]
  have g43_27 : reg n43 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk43 (27 : Fin 32) (by decide) (by decide), g42_27]
  obtain ⟨r43, hr43⟩ : ∃ r, derTlv (memBytes n0.mem (vp) (vl).toNat) = r := ⟨_, rfl⟩
  rcases r43 with er43 | tl43
  · obtain ⟨zhr43, -⟩ := Er43 er43 hr43
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
    have w43_1480 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K43.w32 (by decide) (by decide)).trans w42_1480
    have w43_1484 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K43.w32 (by decide) (by decide)).trans w42_1484
    have w43_1020 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := zhr43
    clear w42_148c w42_1488 w42_1484 w42_1480 w42_a44 w42_a40 w42_a3c w42_a38 w42_a34 w42_a30 w42_a2c w42_a28 w42_a24 w42_a20 w42_94 w42_90 w42_8c w42_88 w42_84 w42_80 w42_7c w42_78 w42_74 w42_70 w42_6c w42_68 w42_64 w42_60 w42_5c w42_58 w42_54 w42_50 w42_4c w42_48 w42_40 w42_3c w42_38 w42_34 w42_30 g42_11 g42_10 g42_27 g42_26 g42_25 g42_23 g42_22 g42_21 g42_19 g42_18 g42_13 g42_12 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
    -- 0x8FE: lw
    obtain ⟨n44, d44, u44⟩ := s43.lw E43.self sv_at_8fe (off' := 0x902) (by decide)
      (by rw [g43_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x600 = B + 0x21A0 + BitVec.ofNat 32 0x1020 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s44 : St n44.mem SV n44 0x902 (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
    have m44 : n44.mem = n43.mem := u44.mem
    have fr44 : ∀ x, SvR B x → n44.mem x = n43.mem x := fun x _ => by rw [m44]
    have t44 : Steps n0 n44 := t43.trans (.single d44)
    have fR44 : ∀ x, SvR B x → n44.mem x = n0.mem x := fun x hx => (fr44 x hx).trans (fR43 x hx)
    have E44 : SvCode n44.mem := E43.fr F fr44
    have V44 : SvSaves B n44.mem v := V43.same m44
    have g44_2 : reg n44 sp = B + 0x21A0 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_2]
    have g44_3 : reg n44 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u44.regs, upd_ne (by decide) (by decide), g43_3]
    have g44_4 : reg n44 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u44.regs, upd_ne (by decide) (by decide), g43_4]
    have g44_8 : reg n44 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_8]
    have g44_9 : reg n44 (9 : Fin 32) = x9 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_9]
    have g44_18 : reg n44 (18 : Fin 32) = out := by rw [u44.regs, upd_ne (by decide) (by decide), g43_18]
    have g44_19 : reg n44 (19 : Fin 32) = bp := by rw [u44.regs, upd_ne (by decide) (by decide), g43_19]
    have g44_21 : reg n44 (21 : Fin 32) = x21 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_21]
    have g44_22 : reg n44 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_22]
    have g44_23 : reg n44 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u44.regs, upd_ne (by decide) (by decide), g43_23]
    have g44_25 : reg n44 (25 : Fin 32) = x25 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_25]
    have g44_26 : reg n44 (26 : Fin 32) = x26 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_26]
    have g44_27 : reg n44 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_27]
    have g44_10 : reg n44 a0 = 0 := by
      rw [u44.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g43_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x600 = B + 0x21A0 + BitVec.ofNat 32 0x1020 by sv_addr, w43_1020]
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
    have w44_1020 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m44]; exact w43_1020
    have w44_1480 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m44]; exact w43_1480
    have w44_1484 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m44]; exact w43_1484
    clear w43_1020 w43_1484 w43_1480 w43_a44 w43_a40 w43_a3c w43_a38 w43_a34 w43_a30 w43_a2c w43_a28 w43_a24 w43_a20 w43_94 w43_90 w43_8c w43_88 w43_84 w43_80 w43_7c w43_78 w43_74 w43_70 w43_6c w43_68 w43_64 w43_60 w43_5c w43_58 w43_54 w43_50 w43_4c w43_48 w43_40 w43_3c w43_38 w43_34 w43_30 zhr43
    -- 0x902: branch, taken
    obtain ⟨n45, d45, u45⟩ := s44.taken E44.self 0x9BA sv_at_902
      (by decide) (by rw [g44_10, s44.zero]; rfl)
    have s45 : St n45.mem SV n45 0x9BA (reg n45) := ⟨u45.pc, rfl, fun _ => rfl⟩
    have m45 : n45.mem = n44.mem := u45.mem
    have fr45 : ∀ x, SvR B x → n45.mem x = n44.mem x := fun x _ => by rw [m45]
    have t45 : Steps n0 n45 := t44.trans (.single d45)
    have fR45 : ∀ x, SvR B x → n45.mem x = n0.mem x := fun x hx => (fr45 x hx).trans (fR44 x hx)
    have E45 : SvCode n45.mem := E44.fr F fr45
    have V45 : SvSaves B n45.mem v := V44.same m45
    have g45_2 : reg n45 sp = B + 0x21A0 := by rw [u45.regs, g44_2]
    have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u45.regs, g44_3]
    have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u45.regs, g44_4]
    have g45_8 : reg n45 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u45.regs, g44_8]
    have g45_9 : reg n45 (9 : Fin 32) = x9 := by rw [u45.regs, g44_9]
    have g45_10 : reg n45 a0 = 0 := by rw [u45.regs, g44_10]
    have g45_18 : reg n45 (18 : Fin 32) = out := by rw [u45.regs, g44_18]
    have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [u45.regs, g44_19]
    have g45_21 : reg n45 (21 : Fin 32) = x21 := by rw [u45.regs, g44_21]
    have g45_22 : reg n45 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u45.regs, g44_22]
    have g45_23 : reg n45 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u45.regs, g44_23]
    have g45_25 : reg n45 (25 : Fin 32) = x25 := by rw [u45.regs, g44_25]
    have g45_26 : reg n45 (26 : Fin 32) = x26 := by rw [u45.regs, g44_26]
    have g45_27 : reg n45 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u45.regs, g44_27]
    have w45_30 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m45]; exact w44_30
    have w45_34 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m45]; exact w44_34
    have w45_38 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m45]; exact w44_38
    have w45_3c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m45]; exact w44_3c
    have w45_40 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m45]; exact w44_40
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
    have w45_1020 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m45]; exact w44_1020
    have w45_1480 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m45]; exact w44_1480
    have w45_1484 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m45]; exact w44_1484
    clear w44_1484 w44_1480 w44_1020 w44_a44 w44_a40 w44_a3c w44_a38 w44_a34 w44_a30 w44_a2c w44_a28 w44_a24 w44_a20 w44_94 w44_90 w44_8c w44_88 w44_84 w44_80 w44_7c w44_78 w44_74 w44_70 w44_6c w44_68 w44_64 w44_60 w44_5c w44_58 w44_54 w44_50 w44_4c w44_48 w44_40 w44_3c w44_38 w44_34 w44_30 g44_10 g44_27 g44_26 g44_25 g44_23 g44_22 g44_21 g44_19 g44_18 g44_9 g44_8 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 m44 s44 u44 d44
    -- 0x9BA: lbu
    obtain ⟨n46, d46, u46⟩ := s45.lbu E45.self sv_at_9ba (off' := 0x9BE) (by decide)
    have s46 : St n46.mem SV n46 0x9BE (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
    have m46 : n46.mem = n45.mem := u46.mem
    have fr46 : ∀ x, SvR B x → n46.mem x = n45.mem x := fun x _ => by rw [m46]
    have t46 : Steps n0 n46 := t45.trans (.single d46)
    have fR46 : ∀ x, SvR B x → n46.mem x = n0.mem x := fun x hx => (fr46 x hx).trans (fR45 x hx)
    have E46 : SvCode n46.mem := E45.fr F fr46
    have V46 : SvSaves B n46.mem v := V45.same m46
    have g46_2 : reg n46 sp = B + 0x21A0 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_2]
    have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u46.regs, upd_ne (by decide) (by decide), g45_3]
    have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u46.regs, upd_ne (by decide) (by decide), g45_4]
    have g46_8 : reg n46 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_8]
    have g46_9 : reg n46 (9 : Fin 32) = x9 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_9]
    have g46_18 : reg n46 (18 : Fin 32) = out := by rw [u46.regs, upd_ne (by decide) (by decide), g45_18]
    have g46_19 : reg n46 (19 : Fin 32) = bp := by rw [u46.regs, upd_ne (by decide) (by decide), g45_19]
    have g46_21 : reg n46 (21 : Fin 32) = x21 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_21]
    have g46_22 : reg n46 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_22]
    have g46_23 : reg n46 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u46.regs, upd_ne (by decide) (by decide), g45_23]
    have g46_25 : reg n46 (25 : Fin 32) = x25 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_25]
    have g46_26 : reg n46 (26 : Fin 32) = x26 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_26]
    have g46_27 : reg n46 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_27]
    have w46_30 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m46]; exact w45_30
    have w46_34 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m46]; exact w45_34
    have w46_38 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m46]; exact w45_38
    have w46_3c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m46]; exact w45_3c
    have w46_40 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m46]; exact w45_40
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
    have w46_1020 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m46]; exact w45_1020
    have w46_1480 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m46]; exact w45_1480
    have w46_1484 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m46]; exact w45_1484
    clear w45_1484 w45_1480 w45_1020 w45_a44 w45_a40 w45_a3c w45_a38 w45_a34 w45_a30 w45_a2c w45_a28 w45_a24 w45_a20 w45_94 w45_90 w45_8c w45_88 w45_84 w45_80 w45_7c w45_78 w45_74 w45_70 w45_6c w45_68 w45_64 w45_60 w45_5c w45_58 w45_54 w45_50 w45_4c w45_48 w45_40 w45_3c w45_38 w45_34 w45_30 g45_27 g45_26 g45_25 g45_23 g45_22 g45_21 g45_19 g45_18 g45_10 g45_9 g45_8 g45_4 g45_3 g45_2 V45 E45 fR45 t45 fr45 m45 s45 u45 d45
    -- 0x9BE: j
    obtain ⟨n47, d47, u47⟩ := s46.jump E46.self sv_at_9be (off' := 0xB38) (by decide)
      (by rw [s46.pc]; decide)
    have s47 : St n47.mem SV n47 0xB38 (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
    have m47 : n47.mem = n46.mem := u47.mem
    have fr47 : ∀ x, SvR B x → n47.mem x = n46.mem x := fun x _ => by rw [m47]
    have t47 : Steps n0 n47 := t46.trans (.single d47)
    have fR47 : ∀ x, SvR B x → n47.mem x = n0.mem x := fun x hx => (fr47 x hx).trans (fR46 x hx)
    have E47 : SvCode n47.mem := E46.fr F fr47
    have V47 : SvSaves B n47.mem v := V46.same m47
    have g47_2 : reg n47 sp = B + 0x21A0 := by rw [u47.regs, g46_2]
    have g47_3 : reg n47 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u47.regs, g46_3]
    have g47_4 : reg n47 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u47.regs, g46_4]
    have g47_8 : reg n47 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u47.regs, g46_8]
    have g47_9 : reg n47 (9 : Fin 32) = x9 := by rw [u47.regs, g46_9]
    have g47_18 : reg n47 (18 : Fin 32) = out := by rw [u47.regs, g46_18]
    have g47_19 : reg n47 (19 : Fin 32) = bp := by rw [u47.regs, g46_19]
    have g47_21 : reg n47 (21 : Fin 32) = x21 := by rw [u47.regs, g46_21]
    have g47_22 : reg n47 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u47.regs, g46_22]
    have g47_23 : reg n47 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u47.regs, g46_23]
    have g47_25 : reg n47 (25 : Fin 32) = x25 := by rw [u47.regs, g46_25]
    have g47_26 : reg n47 (26 : Fin 32) = x26 := by rw [u47.regs, g46_26]
    have g47_27 : reg n47 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u47.regs, g46_27]
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
    have w47_1020 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m47]; exact w46_1020
    have w47_1480 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m47]; exact w46_1480
    have w47_1484 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m47]; exact w46_1484
    clear w46_1484 w46_1480 w46_1020 w46_a44 w46_a40 w46_a3c w46_a38 w46_a34 w46_a30 w46_a2c w46_a28 w46_a24 w46_a20 w46_94 w46_90 w46_8c w46_88 w46_84 w46_80 w46_7c w46_78 w46_74 w46_70 w46_6c w46_68 w46_64 w46_60 w46_5c w46_58 w46_54 w46_50 w46_4c w46_48 w46_40 w46_3c w46_38 w46_34 w46_30 g46_27 g46_26 g46_25 g46_23 g46_22 g46_21 g46_19 g46_18 g46_9 g46_8 g46_4 g46_3 g46_2 V46 E46 fR46 t46 fr46 m46 s46 u46 d46
    -- 0xB38: sw
    obtain ⟨n48, d48, s48, fr48, K48, W48, rg48⟩ := sv_sw F E47 s47 sv_at_b38 (off' := 0xB3A) (c := 0x44)
      (by decide) (by rw [g47_2]; sv_addr) (by decide) (by decide)
    have t48 : Steps n0 n48 := t47.trans d48
    have fR48 : ∀ x, SvR B x → n48.mem x = n0.mem x := fun x hx => (fr48 x hx).trans (fR47 x hx)
    have E48 : SvCode n48.mem := E47.fr F fr48
    have V48 : SvSaves B n48.mem v := V47.keep K48 (by decide)
    have g48_2 : reg n48 sp = B + 0x21A0 := by rw [rg48 sp, g47_2]
    have g48_3 : reg n48 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg48 (3 : Fin 32), g47_3]
    have g48_4 : reg n48 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg48 (4 : Fin 32), g47_4]
    have g48_8 : reg n48 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg48 (8 : Fin 32), g47_8]
    have g48_9 : reg n48 (9 : Fin 32) = x9 := by rw [rg48 (9 : Fin 32), g47_9]
    have g48_18 : reg n48 (18 : Fin 32) = out := by rw [rg48 (18 : Fin 32), g47_18]
    have g48_19 : reg n48 (19 : Fin 32) = bp := by rw [rg48 (19 : Fin 32), g47_19]
    have g48_21 : reg n48 (21 : Fin 32) = x21 := by rw [rg48 (21 : Fin 32), g47_21]
    have g48_22 : reg n48 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg48 (22 : Fin 32), g47_22]
    have g48_23 : reg n48 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [rg48 (23 : Fin 32), g47_23]
    have g48_25 : reg n48 (25 : Fin 32) = x25 := by rw [rg48 (25 : Fin 32), g47_25]
    have g48_26 : reg n48 (26 : Fin 32) = x26 := by rw [rg48 (26 : Fin 32), g47_26]
    have g48_27 : reg n48 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg48 (27 : Fin 32), g47_27]
    have w48_30 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K48.w32 (by decide) (by decide)).trans w47_30
    have w48_34 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K48.w32 (by decide) (by decide)).trans w47_34
    have w48_38 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K48.w32 (by decide) (by decide)).trans w47_38
    have w48_3c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K48.w32 (by decide) (by decide)).trans w47_3c
    have w48_40 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K48.w32 (by decide) (by decide)).trans w47_40
    have w48_48 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K48.w32 (by decide) (by decide)).trans w47_48
    have w48_4c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K48.w32 (by decide) (by decide)).trans w47_4c
    have w48_50 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K48.w32 (by decide) (by decide)).trans w47_50
    have w48_54 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K48.w32 (by decide) (by decide)).trans w47_54
    have w48_58 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K48.w32 (by decide) (by decide)).trans w47_58
    have w48_5c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K48.w32 (by decide) (by decide)).trans w47_5c
    have w48_60 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K48.w32 (by decide) (by decide)).trans w47_60
    have w48_64 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K48.w32 (by decide) (by decide)).trans w47_64
    have w48_68 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K48.w32 (by decide) (by decide)).trans w47_68
    have w48_6c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K48.w32 (by decide) (by decide)).trans w47_6c
    have w48_70 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K48.w32 (by decide) (by decide)).trans w47_70
    have w48_74 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K48.w32 (by decide) (by decide)).trans w47_74
    have w48_78 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K48.w32 (by decide) (by decide)).trans w47_78
    have w48_7c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K48.w32 (by decide) (by decide)).trans w47_7c
    have w48_80 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K48.w32 (by decide) (by decide)).trans w47_80
    have w48_84 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K48.w32 (by decide) (by decide)).trans w47_84
    have w48_88 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K48.w32 (by decide) (by decide)).trans w47_88
    have w48_8c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K48.w32 (by decide) (by decide)).trans w47_8c
    have w48_90 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K48.w32 (by decide) (by decide)).trans w47_90
    have w48_94 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K48.w32 (by decide) (by decide)).trans w47_94
    have w48_a20 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K48.w32 (by decide) (by decide)).trans w47_a20
    have w48_a24 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K48.w32 (by decide) (by decide)).trans w47_a24
    have w48_a28 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K48.w32 (by decide) (by decide)).trans w47_a28
    have w48_a2c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K48.w32 (by decide) (by decide)).trans w47_a2c
    have w48_a30 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K48.w32 (by decide) (by decide)).trans w47_a30
    have w48_a34 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K48.w32 (by decide) (by decide)).trans w47_a34
    have w48_a38 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K48.w32 (by decide) (by decide)).trans w47_a38
    have w48_a3c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K48.w32 (by decide) (by decide)).trans w47_a3c
    have w48_a40 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K48.w32 (by decide) (by decide)).trans w47_a40
    have w48_a44 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K48.w32 (by decide) (by decide)).trans w47_a44
    have w48_1020 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := (K48.w32 (by decide) (by decide)).trans w47_1020
    have w48_1480 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K48.w32 (by decide) (by decide)).trans w47_1480
    have w48_1484 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K48.w32 (by decide) (by decide)).trans w47_1484
    clear w47_1484 w47_1480 w47_1020 w47_a44 w47_a40 w47_a3c w47_a38 w47_a34 w47_a30 w47_a2c w47_a28 w47_a24 w47_a20 w47_94 w47_90 w47_8c w47_88 w47_84 w47_80 w47_7c w47_78 w47_74 w47_70 w47_6c w47_68 w47_64 w47_60 w47_5c w47_58 w47_54 w47_50 w47_4c w47_48 w47_40 w47_3c w47_38 w47_34 w47_30 g47_27 g47_26 g47_25 g47_23 g47_22 g47_21 g47_19 g47_18 g47_9 g47_8 g47_4 g47_3 g47_2 V47 E47 fR47 t47 fr47 m47 s47 u47 d47
    -- 0xB3A: j
    obtain ⟨n49, d49, u49⟩ := s48.jump E48.self sv_at_b3a (off' := 0xB46) (by decide)
      (by rw [s48.pc]; decide)
    have s49 : St n49.mem SV n49 0xB46 (reg n49) := ⟨u49.pc, rfl, fun _ => rfl⟩
    have m49 : n49.mem = n48.mem := u49.mem
    have fr49 : ∀ x, SvR B x → n49.mem x = n48.mem x := fun x _ => by rw [m49]
    have t49 : Steps n0 n49 := t48.trans (.single d49)
    have fR49 : ∀ x, SvR B x → n49.mem x = n0.mem x := fun x hx => (fr49 x hx).trans (fR48 x hx)
    have E49 : SvCode n49.mem := E48.fr F fr49
    have V49 : SvSaves B n49.mem v := V48.same m49
    have g49_2 : reg n49 sp = B + 0x21A0 := by rw [u49.regs, g48_2]
    have g49_3 : reg n49 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u49.regs, g48_3]
    have g49_4 : reg n49 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u49.regs, g48_4]
    have g49_8 : reg n49 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u49.regs, g48_8]
    have g49_9 : reg n49 (9 : Fin 32) = x9 := by rw [u49.regs, g48_9]
    have g49_18 : reg n49 (18 : Fin 32) = out := by rw [u49.regs, g48_18]
    have g49_19 : reg n49 (19 : Fin 32) = bp := by rw [u49.regs, g48_19]
    have g49_21 : reg n49 (21 : Fin 32) = x21 := by rw [u49.regs, g48_21]
    have g49_22 : reg n49 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u49.regs, g48_22]
    have g49_23 : reg n49 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u49.regs, g48_23]
    have g49_25 : reg n49 (25 : Fin 32) = x25 := by rw [u49.regs, g48_25]
    have g49_26 : reg n49 (26 : Fin 32) = x26 := by rw [u49.regs, g48_26]
    have g49_27 : reg n49 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u49.regs, g48_27]
    have w49_30 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m49]; exact w48_30
    have w49_34 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m49]; exact w48_34
    have w49_38 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m49]; exact w48_38
    have w49_3c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m49]; exact w48_3c
    have w49_40 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m49]; exact w48_40
    have w49_48 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m49]; exact w48_48
    have w49_4c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m49]; exact w48_4c
    have w49_50 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m49]; exact w48_50
    have w49_54 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m49]; exact w48_54
    have w49_58 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m49]; exact w48_58
    have w49_5c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m49]; exact w48_5c
    have w49_60 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m49]; exact w48_60
    have w49_64 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m49]; exact w48_64
    have w49_68 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m49]; exact w48_68
    have w49_6c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m49]; exact w48_6c
    have w49_70 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m49]; exact w48_70
    have w49_74 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m49]; exact w48_74
    have w49_78 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m49]; exact w48_78
    have w49_7c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m49]; exact w48_7c
    have w49_80 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m49]; exact w48_80
    have w49_84 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m49]; exact w48_84
    have w49_88 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m49]; exact w48_88
    have w49_8c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m49]; exact w48_8c
    have w49_90 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m49]; exact w48_90
    have w49_94 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m49]; exact w48_94
    have w49_a20 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m49]; exact w48_a20
    have w49_a24 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m49]; exact w48_a24
    have w49_a28 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m49]; exact w48_a28
    have w49_a2c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m49]; exact w48_a2c
    have w49_a30 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m49]; exact w48_a30
    have w49_a34 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m49]; exact w48_a34
    have w49_a38 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m49]; exact w48_a38
    have w49_a3c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m49]; exact w48_a3c
    have w49_a40 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m49]; exact w48_a40
    have w49_a44 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m49]; exact w48_a44
    have w49_1020 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m49]; exact w48_1020
    have w49_1480 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m49]; exact w48_1480
    have w49_1484 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m49]; exact w48_1484
    clear w48_1484 w48_1480 w48_1020 w48_a44 w48_a40 w48_a3c w48_a38 w48_a34 w48_a30 w48_a2c w48_a28 w48_a24 w48_a20 w48_94 w48_90 w48_8c w48_88 w48_84 w48_80 w48_7c w48_78 w48_74 w48_70 w48_6c w48_68 w48_64 w48_60 w48_5c w48_58 w48_54 w48_50 w48_4c w48_48 w48_40 w48_3c w48_38 w48_34 w48_30 g48_27 g48_26 g48_25 g48_23 g48_22 g48_21 g48_19 g48_18 g48_9 g48_8 g48_4 g48_3 g48_2 V48 E48 fR48 t48 rg48 W48 K48 fr48 s48 d48
    -- 0xB46: lw
    obtain ⟨n50, d50, u50⟩ := s49.lw E49.self sv_at_b46 (off' := 0xB48) (by decide)
      (by rw [g49_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s50 : St n50.mem SV n50 0xB48 (reg n50) := ⟨u50.pc, rfl, fun _ => rfl⟩
    have m50 : n50.mem = n49.mem := u50.mem
    have fr50 : ∀ x, SvR B x → n50.mem x = n49.mem x := fun x _ => by rw [m50]
    have t50 : Steps n0 n50 := t49.trans (.single d50)
    have fR50 : ∀ x, SvR B x → n50.mem x = n0.mem x := fun x hx => (fr50 x hx).trans (fR49 x hx)
    have E50 : SvCode n50.mem := E49.fr F fr50
    have V50 : SvSaves B n50.mem v := V49.same m50
    have g50_2 : reg n50 sp = B + 0x21A0 := by rw [u50.regs, upd_ne (by decide) (by decide), g49_2]
    have g50_3 : reg n50 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u50.regs, upd_ne (by decide) (by decide), g49_3]
    have g50_4 : reg n50 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u50.regs, upd_ne (by decide) (by decide), g49_4]
    have g50_8 : reg n50 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u50.regs, upd_ne (by decide) (by decide), g49_8]
    have g50_9 : reg n50 (9 : Fin 32) = x9 := by rw [u50.regs, upd_ne (by decide) (by decide), g49_9]
    have g50_18 : reg n50 (18 : Fin 32) = out := by rw [u50.regs, upd_ne (by decide) (by decide), g49_18]
    have g50_19 : reg n50 (19 : Fin 32) = bp := by rw [u50.regs, upd_ne (by decide) (by decide), g49_19]
    have g50_21 : reg n50 (21 : Fin 32) = x21 := by rw [u50.regs, upd_ne (by decide) (by decide), g49_21]
    have g50_22 : reg n50 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u50.regs, upd_ne (by decide) (by decide), g49_22]
    have g50_23 : reg n50 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u50.regs, upd_ne (by decide) (by decide), g49_23]
    have g50_25 : reg n50 (25 : Fin 32) = x25 := by rw [u50.regs, upd_ne (by decide) (by decide), g49_25]
    have g50_26 : reg n50 (26 : Fin 32) = x26 := by rw [u50.regs, upd_ne (by decide) (by decide), g49_26]
    have g50_27 : reg n50 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u50.regs, upd_ne (by decide) (by decide), g49_27]
    have w50_30 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m50]; exact w49_30
    have w50_34 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m50]; exact w49_34
    have w50_38 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m50]; exact w49_38
    have w50_3c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m50]; exact w49_3c
    have w50_40 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m50]; exact w49_40
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
    have w50_a20 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m50]; exact w49_a20
    have w50_a24 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m50]; exact w49_a24
    have w50_a28 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m50]; exact w49_a28
    have w50_a2c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m50]; exact w49_a2c
    have w50_a30 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m50]; exact w49_a30
    have w50_a34 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m50]; exact w49_a34
    have w50_a38 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m50]; exact w49_a38
    have w50_a3c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m50]; exact w49_a3c
    have w50_a40 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m50]; exact w49_a40
    have w50_a44 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m50]; exact w49_a44
    have w50_1020 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m50]; exact w49_1020
    have w50_1480 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m50]; exact w49_1480
    have w50_1484 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m50]; exact w49_1484
    clear w49_1484 w49_1480 w49_1020 w49_a44 w49_a40 w49_a3c w49_a38 w49_a34 w49_a30 w49_a2c w49_a28 w49_a24 w49_a20 w49_94 w49_90 w49_8c w49_88 w49_84 w49_80 w49_7c w49_78 w49_74 w49_70 w49_6c w49_68 w49_64 w49_60 w49_5c w49_58 w49_54 w49_50 w49_4c w49_48 w49_40 w49_3c w49_38 w49_34 w49_30 g49_27 g49_26 g49_25 g49_23 g49_22 g49_21 g49_19 g49_18 g49_9 g49_8 g49_4 g49_3 g49_2 V49 E49 fR49 t49 fr49 m49 s49 u49 d49
    -- 0xB48: j
    obtain ⟨n51, d51, u51⟩ := s50.jump E50.self sv_at_b48 (off' := 0x966) (by decide)
      (by rw [s50.pc]; decide)
    have s51 : St n51.mem SV n51 0x966 (reg n51) := ⟨u51.pc, rfl, fun _ => rfl⟩
    have m51 : n51.mem = n50.mem := u51.mem
    have fr51 : ∀ x, SvR B x → n51.mem x = n50.mem x := fun x _ => by rw [m51]
    have t51 : Steps n0 n51 := t50.trans (.single d51)
    have fR51 : ∀ x, SvR B x → n51.mem x = n0.mem x := fun x hx => (fr51 x hx).trans (fR50 x hx)
    have E51 : SvCode n51.mem := E50.fr F fr51
    have V51 : SvSaves B n51.mem v := V50.same m51
    have g51_2 : reg n51 sp = B + 0x21A0 := by rw [u51.regs, g50_2]
    have g51_3 : reg n51 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u51.regs, g50_3]
    have g51_4 : reg n51 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u51.regs, g50_4]
    have g51_8 : reg n51 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u51.regs, g50_8]
    have g51_9 : reg n51 (9 : Fin 32) = x9 := by rw [u51.regs, g50_9]
    have g51_18 : reg n51 (18 : Fin 32) = out := by rw [u51.regs, g50_18]
    have g51_19 : reg n51 (19 : Fin 32) = bp := by rw [u51.regs, g50_19]
    have g51_21 : reg n51 (21 : Fin 32) = x21 := by rw [u51.regs, g50_21]
    have g51_22 : reg n51 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u51.regs, g50_22]
    have g51_23 : reg n51 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u51.regs, g50_23]
    have g51_25 : reg n51 (25 : Fin 32) = x25 := by rw [u51.regs, g50_25]
    have g51_26 : reg n51 (26 : Fin 32) = x26 := by rw [u51.regs, g50_26]
    have g51_27 : reg n51 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u51.regs, g50_27]
    have w51_30 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m51]; exact w50_30
    have w51_34 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m51]; exact w50_34
    have w51_38 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m51]; exact w50_38
    have w51_3c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m51]; exact w50_3c
    have w51_40 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m51]; exact w50_40
    have w51_48 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m51]; exact w50_48
    have w51_4c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m51]; exact w50_4c
    have w51_50 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m51]; exact w50_50
    have w51_54 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m51]; exact w50_54
    have w51_58 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m51]; exact w50_58
    have w51_5c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m51]; exact w50_5c
    have w51_60 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m51]; exact w50_60
    have w51_64 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m51]; exact w50_64
    have w51_68 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m51]; exact w50_68
    have w51_6c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m51]; exact w50_6c
    have w51_70 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m51]; exact w50_70
    have w51_74 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m51]; exact w50_74
    have w51_78 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m51]; exact w50_78
    have w51_7c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m51]; exact w50_7c
    have w51_80 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m51]; exact w50_80
    have w51_84 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m51]; exact w50_84
    have w51_88 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m51]; exact w50_88
    have w51_8c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m51]; exact w50_8c
    have w51_90 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m51]; exact w50_90
    have w51_94 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m51]; exact w50_94
    have w51_a20 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m51]; exact w50_a20
    have w51_a24 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m51]; exact w50_a24
    have w51_a28 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m51]; exact w50_a28
    have w51_a2c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m51]; exact w50_a2c
    have w51_a30 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m51]; exact w50_a30
    have w51_a34 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m51]; exact w50_a34
    have w51_a38 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m51]; exact w50_a38
    have w51_a3c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m51]; exact w50_a3c
    have w51_a40 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m51]; exact w50_a40
    have w51_a44 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m51]; exact w50_a44
    have w51_1020 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = 0 := by rw [m51]; exact w50_1020
    have w51_1480 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m51]; exact w50_1480
    have w51_1484 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m51]; exact w50_1484
    clear w50_1484 w50_1480 w50_1020 w50_a44 w50_a40 w50_a3c w50_a38 w50_a34 w50_a30 w50_a2c w50_a28 w50_a24 w50_a20 w50_94 w50_90 w50_8c w50_88 w50_84 w50_80 w50_7c w50_78 w50_74 w50_70 w50_6c w50_68 w50_64 w50_60 w50_5c w50_58 w50_54 w50_50 w50_4c w50_48 w50_40 w50_3c w50_38 w50_34 w50_30 g50_27 g50_26 g50_25 g50_23 g50_22 g50_21 g50_19 g50_18 g50_9 g50_8 g50_4 g50_3 g50_2 V50 E50 fR50 t50 fr50 m50 s50 u50 d50
    exact .inl ⟨(fun ⟨tl43', h0', _⟩ => by rw [hr43] at h0'; cases h0'), sv_fail F E51 s51 t51 fR51 V51 hret g51_2 g51_18 hO g51_3 g51_4⟩
  obtain ⟨o0_43, o4_43, o8_43, o12_43, o16_43, d8_43, d12_43⟩ := Ok43 tl43 hr43
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
  have w43_1480 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K43.w32 (by decide) (by decide)).trans w42_1480
  have w43_1484 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K43.w32 (by decide) (by decide)).trans w42_1484
  have w43_1020 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := o0_43
  have w43_1024 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := o4_43
  have w43_1028 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := o8_43
  have w43_102c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := o12_43
  have w43_1488 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := d8_43
  have w43_148c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := d12_43
  have b43_1030 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := o16_43
  clear w42_148c w42_1488 w42_1484 w42_1480 w42_a44 w42_a40 w42_a3c w42_a38 w42_a34 w42_a30 w42_a2c w42_a28 w42_a24 w42_a20 w42_94 w42_90 w42_8c w42_88 w42_84 w42_80 w42_7c w42_78 w42_74 w42_70 w42_6c w42_68 w42_64 w42_60 w42_5c w42_58 w42_54 w42_50 w42_4c w42_48 w42_40 w42_3c w42_38 w42_34 w42_30 g42_11 g42_10 g42_27 g42_26 g42_25 g42_23 g42_22 g42_21 g42_19 g42_18 g42_13 g42_12 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
  -- 0x8FE: lw
  obtain ⟨n44, d44, u44⟩ := s43.lw E43.self sv_at_8fe (off' := 0x902) (by decide)
    (by rw [g43_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x600 = B + 0x21A0 + BitVec.ofNat 32 0x1020 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s44 : St n44.mem SV n44 0x902 (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
  have m44 : n44.mem = n43.mem := u44.mem
  have fr44 : ∀ x, SvR B x → n44.mem x = n43.mem x := fun x _ => by rw [m44]
  have t44 : Steps n0 n44 := t43.trans (.single d44)
  have fR44 : ∀ x, SvR B x → n44.mem x = n0.mem x := fun x hx => (fr44 x hx).trans (fR43 x hx)
  have E44 : SvCode n44.mem := E43.fr F fr44
  have V44 : SvSaves B n44.mem v := V43.same m44
  have g44_2 : reg n44 sp = B + 0x21A0 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_2]
  have g44_3 : reg n44 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u44.regs, upd_ne (by decide) (by decide), g43_3]
  have g44_4 : reg n44 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u44.regs, upd_ne (by decide) (by decide), g43_4]
  have g44_8 : reg n44 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_8]
  have g44_9 : reg n44 (9 : Fin 32) = x9 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_9]
  have g44_18 : reg n44 (18 : Fin 32) = out := by rw [u44.regs, upd_ne (by decide) (by decide), g43_18]
  have g44_19 : reg n44 (19 : Fin 32) = bp := by rw [u44.regs, upd_ne (by decide) (by decide), g43_19]
  have g44_21 : reg n44 (21 : Fin 32) = x21 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_21]
  have g44_22 : reg n44 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_22]
  have g44_23 : reg n44 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u44.regs, upd_ne (by decide) (by decide), g43_23]
  have g44_25 : reg n44 (25 : Fin 32) = x25 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_25]
  have g44_26 : reg n44 (26 : Fin 32) = x26 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_26]
  have g44_27 : reg n44 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_27]
  have g44_10 : reg n44 a0 = (vp) + BitVec.ofNat 32 tl43.header := by
    rw [u44.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g43_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x600 = B + 0x21A0 + BitVec.ofNat 32 0x1020 by sv_addr, w43_1020]
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
  have w44_1020 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m44]; exact w43_1020
  have w44_1024 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m44]; exact w43_1024
  have w44_1028 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m44]; exact w43_1028
  have w44_102c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m44]; exact w43_102c
  have w44_1480 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m44]; exact w43_1480
  have w44_1484 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m44]; exact w43_1484
  have w44_1488 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m44]; exact w43_1488
  have w44_148c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m44]; exact w43_148c
  have b44_1030 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m44]; exact b43_1030
  clear b43_1030 w43_148c w43_1488 w43_102c w43_1028 w43_1024 w43_1020 w43_1484 w43_1480 w43_a44 w43_a40 w43_a3c w43_a38 w43_a34 w43_a30 w43_a2c w43_a28 w43_a24 w43_a20 w43_94 w43_90 w43_8c w43_88 w43_84 w43_80 w43_7c w43_78 w43_74 w43_70 w43_6c w43_68 w43_64 w43_60 w43_5c w43_58 w43_54 w43_50 w43_4c w43_48 w43_40 w43_3c w43_38 w43_34 w43_30 d12_43 d8_43 o16_43 o12_43 o8_43 o4_43 o0_43 g43_27 g43_26 g43_25 g43_23 g43_22 g43_21 g43_19 g43_18 g43_10 g43_9 g43_8 g43_4 g43_3 g43_2 V43 E43 fR43 t43 fr43 Er43 Ok43 K43 rk43 s43 c43
  -- 0x902: branch, not taken
  obtain ⟨n45, d45, u45⟩ := s44.notTaken E44.self 0x904 sv_at_902
    (by decide) (by rw [g44_10, s44.zero]; exact br_beq_f (val_in.tlv_ne hr43))
  have s45 : St n45.mem SV n45 0x904 (reg n45) := ⟨u45.pc, rfl, fun _ => rfl⟩
  have m45 : n45.mem = n44.mem := u45.mem
  have fr45 : ∀ x, SvR B x → n45.mem x = n44.mem x := fun x _ => by rw [m45]
  have t45 : Steps n0 n45 := t44.trans (.single d45)
  have fR45 : ∀ x, SvR B x → n45.mem x = n0.mem x := fun x hx => (fr45 x hx).trans (fR44 x hx)
  have E45 : SvCode n45.mem := E44.fr F fr45
  have V45 : SvSaves B n45.mem v := V44.same m45
  have g45_2 : reg n45 sp = B + 0x21A0 := by rw [u45.regs, g44_2]
  have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u45.regs, g44_3]
  have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u45.regs, g44_4]
  have g45_8 : reg n45 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u45.regs, g44_8]
  have g45_9 : reg n45 (9 : Fin 32) = x9 := by rw [u45.regs, g44_9]
  have g45_10 : reg n45 a0 = (vp) + BitVec.ofNat 32 tl43.header := by rw [u45.regs, g44_10]
  have g45_18 : reg n45 (18 : Fin 32) = out := by rw [u45.regs, g44_18]
  have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [u45.regs, g44_19]
  have g45_21 : reg n45 (21 : Fin 32) = x21 := by rw [u45.regs, g44_21]
  have g45_22 : reg n45 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u45.regs, g44_22]
  have g45_23 : reg n45 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u45.regs, g44_23]
  have g45_25 : reg n45 (25 : Fin 32) = x25 := by rw [u45.regs, g44_25]
  have g45_26 : reg n45 (26 : Fin 32) = x26 := by rw [u45.regs, g44_26]
  have g45_27 : reg n45 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u45.regs, g44_27]
  have w45_30 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m45]; exact w44_30
  have w45_34 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m45]; exact w44_34
  have w45_38 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m45]; exact w44_38
  have w45_3c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m45]; exact w44_3c
  have w45_40 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m45]; exact w44_40
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
  have w45_1020 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m45]; exact w44_1020
  have w45_1024 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m45]; exact w44_1024
  have w45_1028 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m45]; exact w44_1028
  have w45_102c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m45]; exact w44_102c
  have w45_1480 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m45]; exact w44_1480
  have w45_1484 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m45]; exact w44_1484
  have w45_1488 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m45]; exact w44_1488
  have w45_148c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m45]; exact w44_148c
  have b45_1030 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m45]; exact b44_1030
  clear b44_1030 w44_148c w44_1488 w44_1484 w44_1480 w44_102c w44_1028 w44_1024 w44_1020 w44_a44 w44_a40 w44_a3c w44_a38 w44_a34 w44_a30 w44_a2c w44_a28 w44_a24 w44_a20 w44_94 w44_90 w44_8c w44_88 w44_84 w44_80 w44_7c w44_78 w44_74 w44_70 w44_6c w44_68 w44_64 w44_60 w44_5c w44_58 w44_54 w44_50 w44_4c w44_48 w44_40 w44_3c w44_38 w44_34 w44_30 g44_10 g44_27 g44_26 g44_25 g44_23 g44_22 g44_21 g44_19 g44_18 g44_9 g44_8 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 m44 s44 u44 d44
  -- 0x904: lbu
  obtain ⟨n46, d46, u46⟩ := s45.lbu E45.self sv_at_904 (off' := 0x908) (by decide)
  have s46 : St n46.mem SV n46 0x908 (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
  have m46 : n46.mem = n45.mem := u46.mem
  have fr46 : ∀ x, SvR B x → n46.mem x = n45.mem x := fun x _ => by rw [m46]
  have t46 : Steps n0 n46 := t45.trans (.single d46)
  have fR46 : ∀ x, SvR B x → n46.mem x = n0.mem x := fun x hx => (fr46 x hx).trans (fR45 x hx)
  have E46 : SvCode n46.mem := E45.fr F fr46
  have V46 : SvSaves B n46.mem v := V45.same m46
  have g46_2 : reg n46 sp = B + 0x21A0 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_2]
  have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u46.regs, upd_ne (by decide) (by decide), g45_3]
  have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u46.regs, upd_ne (by decide) (by decide), g45_4]
  have g46_8 : reg n46 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_8]
  have g46_9 : reg n46 (9 : Fin 32) = x9 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_9]
  have g46_10 : reg n46 a0 = (vp) + BitVec.ofNat 32 tl43.header := by rw [u46.regs, upd_ne (by decide) (by decide), g45_10]
  have g46_18 : reg n46 (18 : Fin 32) = out := by rw [u46.regs, upd_ne (by decide) (by decide), g45_18]
  have g46_19 : reg n46 (19 : Fin 32) = bp := by rw [u46.regs, upd_ne (by decide) (by decide), g45_19]
  have g46_21 : reg n46 (21 : Fin 32) = x21 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_21]
  have g46_22 : reg n46 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_22]
  have g46_23 : reg n46 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u46.regs, upd_ne (by decide) (by decide), g45_23]
  have g46_25 : reg n46 (25 : Fin 32) = x25 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_25]
  have g46_26 : reg n46 (26 : Fin 32) = x26 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_26]
  have g46_27 : reg n46 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u46.regs, upd_ne (by decide) (by decide), g45_27]
  have g46_11 : reg n46 a1 = (BitVec.ofNat 8 tl43.tag).zeroExtend 32 := by
    rw [u46.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g45_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x610 = B + 0x21A0 + BitVec.ofNat 32 0x1030 by sv_addr, b45_1030]
  have w46_30 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m46]; exact w45_30
  have w46_34 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m46]; exact w45_34
  have w46_38 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m46]; exact w45_38
  have w46_3c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m46]; exact w45_3c
  have w46_40 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m46]; exact w45_40
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
  have w46_1020 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m46]; exact w45_1020
  have w46_1024 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m46]; exact w45_1024
  have w46_1028 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m46]; exact w45_1028
  have w46_102c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m46]; exact w45_102c
  have w46_1480 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m46]; exact w45_1480
  have w46_1484 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m46]; exact w45_1484
  have w46_1488 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m46]; exact w45_1488
  have w46_148c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m46]; exact w45_148c
  have b46_1030 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m46]; exact b45_1030
  clear b45_1030 w45_148c w45_1488 w45_1484 w45_1480 w45_102c w45_1028 w45_1024 w45_1020 w45_a44 w45_a40 w45_a3c w45_a38 w45_a34 w45_a30 w45_a2c w45_a28 w45_a24 w45_a20 w45_94 w45_90 w45_8c w45_88 w45_84 w45_80 w45_7c w45_78 w45_74 w45_70 w45_6c w45_68 w45_64 w45_60 w45_5c w45_58 w45_54 w45_50 w45_4c w45_48 w45_40 w45_3c w45_38 w45_34 w45_30 g45_27 g45_26 g45_25 g45_23 g45_22 g45_21 g45_19 g45_18 g45_10 g45_9 g45_8 g45_4 g45_3 g45_2 V45 E45 fR45 t45 fr45 m45 s45 u45 d45
  -- 0x908
  obtain ⟨n47, c47, u47⟩ := s46.block svDp1908 E46.self svDp1908_end
    ⟨trivial, trivial⟩
  have m47 : n47.mem = n46.mem := u47.mem
  have s47 : St n47.mem SV n47 0x90A (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
  have rb47 : ∀ q, reg n47 q = (runBlock svDp1908 (n46.mem, reg n46)).2 q := fun q => by rw [u47.regs]
  have fr47 : ∀ x, SvR B x → n47.mem x = n46.mem x := fun x _ => by rw [m47]
  have t47 : Steps n0 n47 := t46.trans c47
  have fR47 : ∀ x, SvR B x → n47.mem x = n0.mem x := fun x hx => (fr47 x hx).trans (fR46 x hx)
  have E47 : SvCode n47.mem := E46.fr F fr47
  have V47 : SvSaves B n47.mem v := V46.same m47
  have g47_2 : reg n47 sp = B + 0x21A0 := by
    rw [rb47, runBlock_reg _ _ _ sp s46.zero (by decide), g46_2]
  have g47_3 : reg n47 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb47, runBlock_reg _ _ _ (3 : Fin 32) s46.zero (by decide), g46_3]
  have g47_4 : reg n47 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb47, runBlock_reg _ _ _ (4 : Fin 32) s46.zero (by decide), g46_4]
  have g47_8 : reg n47 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb47, runBlock_reg _ _ _ (8 : Fin 32) s46.zero (by decide), g46_8]
  have g47_9 : reg n47 (9 : Fin 32) = x9 := by
    rw [rb47, runBlock_reg _ _ _ (9 : Fin 32) s46.zero (by decide), g46_9]
  have g47_10 : reg n47 a0 = (vp) + BitVec.ofNat 32 tl43.header := by
    rw [rb47, runBlock_reg _ _ _ a0 s46.zero (by decide), g46_10]
  have g47_11 : reg n47 a1 = (BitVec.ofNat 8 tl43.tag).zeroExtend 32 := by
    rw [rb47, runBlock_reg _ _ _ a1 s46.zero (by decide), g46_11]
  have g47_18 : reg n47 (18 : Fin 32) = out := by
    rw [rb47, runBlock_reg _ _ _ (18 : Fin 32) s46.zero (by decide), g46_18]
  have g47_19 : reg n47 (19 : Fin 32) = bp := by
    rw [rb47, runBlock_reg _ _ _ (19 : Fin 32) s46.zero (by decide), g46_19]
  have g47_21 : reg n47 (21 : Fin 32) = x21 := by
    rw [rb47, runBlock_reg _ _ _ (21 : Fin 32) s46.zero (by decide), g46_21]
  have g47_22 : reg n47 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb47, runBlock_reg _ _ _ (22 : Fin 32) s46.zero (by decide), g46_22]
  have g47_23 : reg n47 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by
    rw [rb47, runBlock_reg _ _ _ (23 : Fin 32) s46.zero (by decide), g46_23]
  have g47_25 : reg n47 (25 : Fin 32) = x25 := by
    rw [rb47, runBlock_reg _ _ _ (25 : Fin 32) s46.zero (by decide), g46_25]
  have g47_26 : reg n47 (26 : Fin 32) = x26 := by
    rw [rb47, runBlock_reg _ _ _ (26 : Fin 32) s46.zero (by decide), g46_26]
  have g47_27 : reg n47 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb47, runBlock_reg _ _ _ (27 : Fin 32) s46.zero (by decide), g46_27]
  have g47_12 : reg n47 a2 = BitVec.ofNat 32 0xC := by
    rw [rb47]; simp +decide only [runBlock, BInstr.run, svDp1908, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g46_2, g46_3, g46_4, g46_8, g46_9, g46_10, g46_11, g46_18, g46_19, g46_21, g46_22, g46_23, g46_25, g46_26, g46_27, s46.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
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
  have w47_1020 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m47]; exact w46_1020
  have w47_1024 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m47]; exact w46_1024
  have w47_1028 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m47]; exact w46_1028
  have w47_102c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m47]; exact w46_102c
  have w47_1480 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m47]; exact w46_1480
  have w47_1484 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m47]; exact w46_1484
  have w47_1488 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m47]; exact w46_1488
  have w47_148c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m47]; exact w46_148c
  have b47_1030 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m47]; exact b46_1030
  clear b46_1030 w46_148c w46_1488 w46_1484 w46_1480 w46_102c w46_1028 w46_1024 w46_1020 w46_a44 w46_a40 w46_a3c w46_a38 w46_a34 w46_a30 w46_a2c w46_a28 w46_a24 w46_a20 w46_94 w46_90 w46_8c w46_88 w46_84 w46_80 w46_7c w46_78 w46_74 w46_70 w46_6c w46_68 w46_64 w46_60 w46_5c w46_58 w46_54 w46_50 w46_4c w46_48 w46_40 w46_3c w46_38 w46_34 w46_30 g46_11 g46_27 g46_26 g46_25 g46_23 g46_22 g46_21 g46_19 g46_18 g46_10 g46_9 g46_8 g46_4 g46_3 g46_2 V46 E46 fR46 t46 fr46 m46 s46 u46 d46
  by_cases hz_47 : BitVec.ofNat 8 tl43.tag = BitVec.ofNat 8 0xC
  rotate_left
  · -- 0x90A: branch, taken
    obtain ⟨n48, d48, u48⟩ := s47.taken E47.self 0xB4E sv_at_90a
      (by decide) (by rw [g47_11, g47_12]; exact br_bne_byte_t (by decide) hz_47)
    have s48 : St n48.mem SV n48 0xB4E (reg n48) := ⟨u48.pc, rfl, fun _ => rfl⟩
    have m48 : n48.mem = n47.mem := u48.mem
    have fr48 : ∀ x, SvR B x → n48.mem x = n47.mem x := fun x _ => by rw [m48]
    have t48 : Steps n0 n48 := t47.trans (.single d48)
    have fR48 : ∀ x, SvR B x → n48.mem x = n0.mem x := fun x hx => (fr48 x hx).trans (fR47 x hx)
    have E48 : SvCode n48.mem := E47.fr F fr48
    have V48 : SvSaves B n48.mem v := V47.same m48
    have g48_2 : reg n48 sp = B + 0x21A0 := by rw [u48.regs, g47_2]
    have g48_3 : reg n48 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u48.regs, g47_3]
    have g48_4 : reg n48 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u48.regs, g47_4]
    have g48_8 : reg n48 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u48.regs, g47_8]
    have g48_9 : reg n48 (9 : Fin 32) = x9 := by rw [u48.regs, g47_9]
    have g48_10 : reg n48 a0 = (vp) + BitVec.ofNat 32 tl43.header := by rw [u48.regs, g47_10]
    have g48_11 : reg n48 a1 = (BitVec.ofNat 8 tl43.tag).zeroExtend 32 := by rw [u48.regs, g47_11]
    have g48_12 : reg n48 a2 = BitVec.ofNat 32 0xC := by rw [u48.regs, g47_12]
    have g48_18 : reg n48 (18 : Fin 32) = out := by rw [u48.regs, g47_18]
    have g48_19 : reg n48 (19 : Fin 32) = bp := by rw [u48.regs, g47_19]
    have g48_21 : reg n48 (21 : Fin 32) = x21 := by rw [u48.regs, g47_21]
    have g48_22 : reg n48 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u48.regs, g47_22]
    have g48_23 : reg n48 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u48.regs, g47_23]
    have g48_25 : reg n48 (25 : Fin 32) = x25 := by rw [u48.regs, g47_25]
    have g48_26 : reg n48 (26 : Fin 32) = x26 := by rw [u48.regs, g47_26]
    have g48_27 : reg n48 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u48.regs, g47_27]
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
    have w48_a20 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m48]; exact w47_a20
    have w48_a24 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m48]; exact w47_a24
    have w48_a28 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m48]; exact w47_a28
    have w48_a2c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m48]; exact w47_a2c
    have w48_a30 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m48]; exact w47_a30
    have w48_a34 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m48]; exact w47_a34
    have w48_a38 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m48]; exact w47_a38
    have w48_a3c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m48]; exact w47_a3c
    have w48_a40 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m48]; exact w47_a40
    have w48_a44 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m48]; exact w47_a44
    have w48_1020 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m48]; exact w47_1020
    have w48_1024 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m48]; exact w47_1024
    have w48_1028 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m48]; exact w47_1028
    have w48_102c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m48]; exact w47_102c
    have w48_1480 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m48]; exact w47_1480
    have w48_1484 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m48]; exact w47_1484
    have w48_1488 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m48]; exact w47_1488
    have w48_148c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m48]; exact w47_148c
    have b48_1030 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m48]; exact b47_1030
    clear b47_1030 w47_148c w47_1488 w47_1484 w47_1480 w47_102c w47_1028 w47_1024 w47_1020 w47_a44 w47_a40 w47_a3c w47_a38 w47_a34 w47_a30 w47_a2c w47_a28 w47_a24 w47_a20 w47_94 w47_90 w47_8c w47_88 w47_84 w47_80 w47_7c w47_78 w47_74 w47_70 w47_6c w47_68 w47_64 w47_60 w47_5c w47_58 w47_54 w47_50 w47_4c w47_48 w47_40 w47_3c w47_38 w47_34 w47_30 g47_12 g47_27 g47_26 g47_25 g47_23 g47_22 g47_21 g47_19 g47_18 g47_11 g47_10 g47_9 g47_8 g47_4 g47_3 g47_2 V47 E47 fR47 t47 fr47 rb47 s47 m47 u47 c47
    -- 0xB4E
    obtain ⟨n49, c49, u49⟩ := s48.block svDp1b4e E48.self svDp1b4e_end
      ⟨trivial, trivial⟩
    have m49 : n49.mem = n48.mem := u49.mem
    have s49 : St n49.mem SV n49 0xB50 (reg n49) := ⟨u49.pc, rfl, fun _ => rfl⟩
    have rb49 : ∀ q, reg n49 q = (runBlock svDp1b4e (n48.mem, reg n48)).2 q := fun q => by rw [u49.regs]
    have fr49 : ∀ x, SvR B x → n49.mem x = n48.mem x := fun x _ => by rw [m49]
    have t49 : Steps n0 n49 := t48.trans c49
    have fR49 : ∀ x, SvR B x → n49.mem x = n0.mem x := fun x hx => (fr49 x hx).trans (fR48 x hx)
    have E49 : SvCode n49.mem := E48.fr F fr49
    have V49 : SvSaves B n49.mem v := V48.same m49
    have g49_2 : reg n49 sp = B + 0x21A0 := by
      rw [rb49, runBlock_reg _ _ _ sp s48.zero (by decide), g48_2]
    have g49_3 : reg n49 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb49, runBlock_reg _ _ _ (3 : Fin 32) s48.zero (by decide), g48_3]
    have g49_4 : reg n49 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb49, runBlock_reg _ _ _ (4 : Fin 32) s48.zero (by decide), g48_4]
    have g49_8 : reg n49 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
      rw [rb49, runBlock_reg _ _ _ (8 : Fin 32) s48.zero (by decide), g48_8]
    have g49_9 : reg n49 (9 : Fin 32) = x9 := by
      rw [rb49, runBlock_reg _ _ _ (9 : Fin 32) s48.zero (by decide), g48_9]
    have g49_11 : reg n49 a1 = (BitVec.ofNat 8 tl43.tag).zeroExtend 32 := by
      rw [rb49, runBlock_reg _ _ _ a1 s48.zero (by decide), g48_11]
    have g49_12 : reg n49 a2 = BitVec.ofNat 32 0xC := by
      rw [rb49, runBlock_reg _ _ _ a2 s48.zero (by decide), g48_12]
    have g49_18 : reg n49 (18 : Fin 32) = out := by
      rw [rb49, runBlock_reg _ _ _ (18 : Fin 32) s48.zero (by decide), g48_18]
    have g49_19 : reg n49 (19 : Fin 32) = bp := by
      rw [rb49, runBlock_reg _ _ _ (19 : Fin 32) s48.zero (by decide), g48_19]
    have g49_21 : reg n49 (21 : Fin 32) = x21 := by
      rw [rb49, runBlock_reg _ _ _ (21 : Fin 32) s48.zero (by decide), g48_21]
    have g49_22 : reg n49 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb49, runBlock_reg _ _ _ (22 : Fin 32) s48.zero (by decide), g48_22]
    have g49_23 : reg n49 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by
      rw [rb49, runBlock_reg _ _ _ (23 : Fin 32) s48.zero (by decide), g48_23]
    have g49_25 : reg n49 (25 : Fin 32) = x25 := by
      rw [rb49, runBlock_reg _ _ _ (25 : Fin 32) s48.zero (by decide), g48_25]
    have g49_26 : reg n49 (26 : Fin 32) = x26 := by
      rw [rb49, runBlock_reg _ _ _ (26 : Fin 32) s48.zero (by decide), g48_26]
    have g49_27 : reg n49 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb49, runBlock_reg _ _ _ (27 : Fin 32) s48.zero (by decide), g48_27]
    have g49_10 : reg n49 a0 = BitVec.ofNat 32 0x16 := by
      rw [rb49]; simp +decide only [runBlock, BInstr.run, svDp1b4e, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g48_2, g48_3, g48_4, g48_8, g48_9, g48_10, g48_11, g48_12, g48_18, g48_19, g48_21, g48_22, g48_23, g48_25, g48_26, g48_27, s48.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have w49_30 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m49]; exact w48_30
    have w49_34 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m49]; exact w48_34
    have w49_38 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m49]; exact w48_38
    have w49_3c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m49]; exact w48_3c
    have w49_40 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m49]; exact w48_40
    have w49_48 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m49]; exact w48_48
    have w49_4c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m49]; exact w48_4c
    have w49_50 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m49]; exact w48_50
    have w49_54 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m49]; exact w48_54
    have w49_58 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m49]; exact w48_58
    have w49_5c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m49]; exact w48_5c
    have w49_60 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m49]; exact w48_60
    have w49_64 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m49]; exact w48_64
    have w49_68 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m49]; exact w48_68
    have w49_6c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m49]; exact w48_6c
    have w49_70 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m49]; exact w48_70
    have w49_74 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m49]; exact w48_74
    have w49_78 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m49]; exact w48_78
    have w49_7c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m49]; exact w48_7c
    have w49_80 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m49]; exact w48_80
    have w49_84 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m49]; exact w48_84
    have w49_88 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m49]; exact w48_88
    have w49_8c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m49]; exact w48_8c
    have w49_90 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m49]; exact w48_90
    have w49_94 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m49]; exact w48_94
    have w49_a20 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m49]; exact w48_a20
    have w49_a24 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m49]; exact w48_a24
    have w49_a28 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m49]; exact w48_a28
    have w49_a2c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m49]; exact w48_a2c
    have w49_a30 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m49]; exact w48_a30
    have w49_a34 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m49]; exact w48_a34
    have w49_a38 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m49]; exact w48_a38
    have w49_a3c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m49]; exact w48_a3c
    have w49_a40 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m49]; exact w48_a40
    have w49_a44 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m49]; exact w48_a44
    have w49_1020 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m49]; exact w48_1020
    have w49_1024 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m49]; exact w48_1024
    have w49_1028 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m49]; exact w48_1028
    have w49_102c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m49]; exact w48_102c
    have w49_1480 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m49]; exact w48_1480
    have w49_1484 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m49]; exact w48_1484
    have w49_1488 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m49]; exact w48_1488
    have w49_148c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m49]; exact w48_148c
    have b49_1030 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m49]; exact b48_1030
    clear b48_1030 w48_148c w48_1488 w48_1484 w48_1480 w48_102c w48_1028 w48_1024 w48_1020 w48_a44 w48_a40 w48_a3c w48_a38 w48_a34 w48_a30 w48_a2c w48_a28 w48_a24 w48_a20 w48_94 w48_90 w48_8c w48_88 w48_84 w48_80 w48_7c w48_78 w48_74 w48_70 w48_6c w48_68 w48_64 w48_60 w48_5c w48_58 w48_54 w48_50 w48_4c w48_48 w48_40 w48_3c w48_38 w48_34 w48_30 g48_27 g48_26 g48_25 g48_23 g48_22 g48_21 g48_19 g48_18 g48_12 g48_11 g48_10 g48_9 g48_8 g48_4 g48_3 g48_2 V48 E48 fR48 t48 fr48 m48 s48 u48 d48
    -- 0xB50: j
    obtain ⟨n50, d50, u50⟩ := s49.jump E49.self sv_at_b50 (off' := 0xB38) (by decide)
      (by rw [s49.pc]; decide)
    have s50 : St n50.mem SV n50 0xB38 (reg n50) := ⟨u50.pc, rfl, fun _ => rfl⟩
    have m50 : n50.mem = n49.mem := u50.mem
    have fr50 : ∀ x, SvR B x → n50.mem x = n49.mem x := fun x _ => by rw [m50]
    have t50 : Steps n0 n50 := t49.trans (.single d50)
    have fR50 : ∀ x, SvR B x → n50.mem x = n0.mem x := fun x hx => (fr50 x hx).trans (fR49 x hx)
    have E50 : SvCode n50.mem := E49.fr F fr50
    have V50 : SvSaves B n50.mem v := V49.same m50
    have g50_2 : reg n50 sp = B + 0x21A0 := by rw [u50.regs, g49_2]
    have g50_3 : reg n50 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u50.regs, g49_3]
    have g50_4 : reg n50 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u50.regs, g49_4]
    have g50_8 : reg n50 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u50.regs, g49_8]
    have g50_9 : reg n50 (9 : Fin 32) = x9 := by rw [u50.regs, g49_9]
    have g50_10 : reg n50 a0 = BitVec.ofNat 32 0x16 := by rw [u50.regs, g49_10]
    have g50_11 : reg n50 a1 = (BitVec.ofNat 8 tl43.tag).zeroExtend 32 := by rw [u50.regs, g49_11]
    have g50_12 : reg n50 a2 = BitVec.ofNat 32 0xC := by rw [u50.regs, g49_12]
    have g50_18 : reg n50 (18 : Fin 32) = out := by rw [u50.regs, g49_18]
    have g50_19 : reg n50 (19 : Fin 32) = bp := by rw [u50.regs, g49_19]
    have g50_21 : reg n50 (21 : Fin 32) = x21 := by rw [u50.regs, g49_21]
    have g50_22 : reg n50 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u50.regs, g49_22]
    have g50_23 : reg n50 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u50.regs, g49_23]
    have g50_25 : reg n50 (25 : Fin 32) = x25 := by rw [u50.regs, g49_25]
    have g50_26 : reg n50 (26 : Fin 32) = x26 := by rw [u50.regs, g49_26]
    have g50_27 : reg n50 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u50.regs, g49_27]
    have w50_30 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m50]; exact w49_30
    have w50_34 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m50]; exact w49_34
    have w50_38 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m50]; exact w49_38
    have w50_3c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m50]; exact w49_3c
    have w50_40 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m50]; exact w49_40
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
    have w50_a20 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m50]; exact w49_a20
    have w50_a24 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m50]; exact w49_a24
    have w50_a28 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m50]; exact w49_a28
    have w50_a2c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m50]; exact w49_a2c
    have w50_a30 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m50]; exact w49_a30
    have w50_a34 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m50]; exact w49_a34
    have w50_a38 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m50]; exact w49_a38
    have w50_a3c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m50]; exact w49_a3c
    have w50_a40 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m50]; exact w49_a40
    have w50_a44 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m50]; exact w49_a44
    have w50_1020 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m50]; exact w49_1020
    have w50_1024 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m50]; exact w49_1024
    have w50_1028 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m50]; exact w49_1028
    have w50_102c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m50]; exact w49_102c
    have w50_1480 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m50]; exact w49_1480
    have w50_1484 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m50]; exact w49_1484
    have w50_1488 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m50]; exact w49_1488
    have w50_148c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m50]; exact w49_148c
    have b50_1030 : n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m50]; exact b49_1030
    clear b49_1030 w49_148c w49_1488 w49_1484 w49_1480 w49_102c w49_1028 w49_1024 w49_1020 w49_a44 w49_a40 w49_a3c w49_a38 w49_a34 w49_a30 w49_a2c w49_a28 w49_a24 w49_a20 w49_94 w49_90 w49_8c w49_88 w49_84 w49_80 w49_7c w49_78 w49_74 w49_70 w49_6c w49_68 w49_64 w49_60 w49_5c w49_58 w49_54 w49_50 w49_4c w49_48 w49_40 w49_3c w49_38 w49_34 w49_30 g49_10 g49_27 g49_26 g49_25 g49_23 g49_22 g49_21 g49_19 g49_18 g49_12 g49_11 g49_9 g49_8 g49_4 g49_3 g49_2 V49 E49 fR49 t49 fr49 rb49 s49 m49 u49 c49
    -- 0xB38: sw
    obtain ⟨n51, d51, s51, fr51, K51, W51, rg51⟩ := sv_sw F E50 s50 sv_at_b38 (off' := 0xB3A) (c := 0x44)
      (by decide) (by rw [g50_2]; sv_addr) (by decide) (by decide)
    have t51 : Steps n0 n51 := t50.trans d51
    have fR51 : ∀ x, SvR B x → n51.mem x = n0.mem x := fun x hx => (fr51 x hx).trans (fR50 x hx)
    have E51 : SvCode n51.mem := E50.fr F fr51
    have V51 : SvSaves B n51.mem v := V50.keep K51 (by decide)
    have g51_2 : reg n51 sp = B + 0x21A0 := by rw [rg51 sp, g50_2]
    have g51_3 : reg n51 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg51 (3 : Fin 32), g50_3]
    have g51_4 : reg n51 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg51 (4 : Fin 32), g50_4]
    have g51_8 : reg n51 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg51 (8 : Fin 32), g50_8]
    have g51_9 : reg n51 (9 : Fin 32) = x9 := by rw [rg51 (9 : Fin 32), g50_9]
    have g51_10 : reg n51 a0 = BitVec.ofNat 32 0x16 := by rw [rg51 a0, g50_10]
    have g51_11 : reg n51 a1 = (BitVec.ofNat 8 tl43.tag).zeroExtend 32 := by rw [rg51 a1, g50_11]
    have g51_12 : reg n51 a2 = BitVec.ofNat 32 0xC := by rw [rg51 a2, g50_12]
    have g51_18 : reg n51 (18 : Fin 32) = out := by rw [rg51 (18 : Fin 32), g50_18]
    have g51_19 : reg n51 (19 : Fin 32) = bp := by rw [rg51 (19 : Fin 32), g50_19]
    have g51_21 : reg n51 (21 : Fin 32) = x21 := by rw [rg51 (21 : Fin 32), g50_21]
    have g51_22 : reg n51 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg51 (22 : Fin 32), g50_22]
    have g51_23 : reg n51 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [rg51 (23 : Fin 32), g50_23]
    have g51_25 : reg n51 (25 : Fin 32) = x25 := by rw [rg51 (25 : Fin 32), g50_25]
    have g51_26 : reg n51 (26 : Fin 32) = x26 := by rw [rg51 (26 : Fin 32), g50_26]
    have g51_27 : reg n51 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg51 (27 : Fin 32), g50_27]
    have w51_30 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K51.w32 (by decide) (by decide)).trans w50_30
    have w51_34 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K51.w32 (by decide) (by decide)).trans w50_34
    have w51_38 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K51.w32 (by decide) (by decide)).trans w50_38
    have w51_3c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K51.w32 (by decide) (by decide)).trans w50_3c
    have w51_40 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K51.w32 (by decide) (by decide)).trans w50_40
    have w51_48 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K51.w32 (by decide) (by decide)).trans w50_48
    have w51_4c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K51.w32 (by decide) (by decide)).trans w50_4c
    have w51_50 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K51.w32 (by decide) (by decide)).trans w50_50
    have w51_54 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K51.w32 (by decide) (by decide)).trans w50_54
    have w51_58 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K51.w32 (by decide) (by decide)).trans w50_58
    have w51_5c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K51.w32 (by decide) (by decide)).trans w50_5c
    have w51_60 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K51.w32 (by decide) (by decide)).trans w50_60
    have w51_64 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K51.w32 (by decide) (by decide)).trans w50_64
    have w51_68 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K51.w32 (by decide) (by decide)).trans w50_68
    have w51_6c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K51.w32 (by decide) (by decide)).trans w50_6c
    have w51_70 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K51.w32 (by decide) (by decide)).trans w50_70
    have w51_74 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K51.w32 (by decide) (by decide)).trans w50_74
    have w51_78 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K51.w32 (by decide) (by decide)).trans w50_78
    have w51_7c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K51.w32 (by decide) (by decide)).trans w50_7c
    have w51_80 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K51.w32 (by decide) (by decide)).trans w50_80
    have w51_84 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K51.w32 (by decide) (by decide)).trans w50_84
    have w51_88 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K51.w32 (by decide) (by decide)).trans w50_88
    have w51_8c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K51.w32 (by decide) (by decide)).trans w50_8c
    have w51_90 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K51.w32 (by decide) (by decide)).trans w50_90
    have w51_94 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K51.w32 (by decide) (by decide)).trans w50_94
    have w51_a20 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K51.w32 (by decide) (by decide)).trans w50_a20
    have w51_a24 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K51.w32 (by decide) (by decide)).trans w50_a24
    have w51_a28 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K51.w32 (by decide) (by decide)).trans w50_a28
    have w51_a2c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K51.w32 (by decide) (by decide)).trans w50_a2c
    have w51_a30 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K51.w32 (by decide) (by decide)).trans w50_a30
    have w51_a34 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K51.w32 (by decide) (by decide)).trans w50_a34
    have w51_a38 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K51.w32 (by decide) (by decide)).trans w50_a38
    have w51_a3c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K51.w32 (by decide) (by decide)).trans w50_a3c
    have w51_a40 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K51.w32 (by decide) (by decide)).trans w50_a40
    have w51_a44 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K51.w32 (by decide) (by decide)).trans w50_a44
    have w51_1020 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := (K51.w32 (by decide) (by decide)).trans w50_1020
    have w51_1024 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := (K51.w32 (by decide) (by decide)).trans w50_1024
    have w51_1028 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := (K51.w32 (by decide) (by decide)).trans w50_1028
    have w51_102c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := (K51.w32 (by decide) (by decide)).trans w50_102c
    have w51_1480 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K51.w32 (by decide) (by decide)).trans w50_1480
    have w51_1484 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K51.w32 (by decide) (by decide)).trans w50_1484
    have w51_1488 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := (K51.w32 (by decide) (by decide)).trans w50_1488
    have w51_148c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := (K51.w32 (by decide) (by decide)).trans w50_148c
    have b51_1030 : n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := (K51.b8 (by decide) (by decide)).trans b50_1030
    have w51_44 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [W51, g50_10]
    clear b50_1030 w50_148c w50_1488 w50_1484 w50_1480 w50_102c w50_1028 w50_1024 w50_1020 w50_a44 w50_a40 w50_a3c w50_a38 w50_a34 w50_a30 w50_a2c w50_a28 w50_a24 w50_a20 w50_94 w50_90 w50_8c w50_88 w50_84 w50_80 w50_7c w50_78 w50_74 w50_70 w50_6c w50_68 w50_64 w50_60 w50_5c w50_58 w50_54 w50_50 w50_4c w50_48 w50_40 w50_3c w50_38 w50_34 w50_30 g50_27 g50_26 g50_25 g50_23 g50_22 g50_21 g50_19 g50_18 g50_12 g50_11 g50_10 g50_9 g50_8 g50_4 g50_3 g50_2 V50 E50 fR50 t50 fr50 m50 s50 u50 d50
    -- 0xB3A: j
    obtain ⟨n52, d52, u52⟩ := s51.jump E51.self sv_at_b3a (off' := 0xB46) (by decide)
      (by rw [s51.pc]; decide)
    have s52 : St n52.mem SV n52 0xB46 (reg n52) := ⟨u52.pc, rfl, fun _ => rfl⟩
    have m52 : n52.mem = n51.mem := u52.mem
    have fr52 : ∀ x, SvR B x → n52.mem x = n51.mem x := fun x _ => by rw [m52]
    have t52 : Steps n0 n52 := t51.trans (.single d52)
    have fR52 : ∀ x, SvR B x → n52.mem x = n0.mem x := fun x hx => (fr52 x hx).trans (fR51 x hx)
    have E52 : SvCode n52.mem := E51.fr F fr52
    have V52 : SvSaves B n52.mem v := V51.same m52
    have g52_2 : reg n52 sp = B + 0x21A0 := by rw [u52.regs, g51_2]
    have g52_3 : reg n52 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u52.regs, g51_3]
    have g52_4 : reg n52 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u52.regs, g51_4]
    have g52_8 : reg n52 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u52.regs, g51_8]
    have g52_9 : reg n52 (9 : Fin 32) = x9 := by rw [u52.regs, g51_9]
    have g52_10 : reg n52 a0 = BitVec.ofNat 32 0x16 := by rw [u52.regs, g51_10]
    have g52_11 : reg n52 a1 = (BitVec.ofNat 8 tl43.tag).zeroExtend 32 := by rw [u52.regs, g51_11]
    have g52_12 : reg n52 a2 = BitVec.ofNat 32 0xC := by rw [u52.regs, g51_12]
    have g52_18 : reg n52 (18 : Fin 32) = out := by rw [u52.regs, g51_18]
    have g52_19 : reg n52 (19 : Fin 32) = bp := by rw [u52.regs, g51_19]
    have g52_21 : reg n52 (21 : Fin 32) = x21 := by rw [u52.regs, g51_21]
    have g52_22 : reg n52 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u52.regs, g51_22]
    have g52_23 : reg n52 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u52.regs, g51_23]
    have g52_25 : reg n52 (25 : Fin 32) = x25 := by rw [u52.regs, g51_25]
    have g52_26 : reg n52 (26 : Fin 32) = x26 := by rw [u52.regs, g51_26]
    have g52_27 : reg n52 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u52.regs, g51_27]
    have w52_30 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m52]; exact w51_30
    have w52_34 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m52]; exact w51_34
    have w52_38 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m52]; exact w51_38
    have w52_3c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m52]; exact w51_3c
    have w52_40 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m52]; exact w51_40
    have w52_44 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m52]; exact w51_44
    have w52_48 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m52]; exact w51_48
    have w52_4c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m52]; exact w51_4c
    have w52_50 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m52]; exact w51_50
    have w52_54 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m52]; exact w51_54
    have w52_58 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m52]; exact w51_58
    have w52_5c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m52]; exact w51_5c
    have w52_60 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m52]; exact w51_60
    have w52_64 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m52]; exact w51_64
    have w52_68 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m52]; exact w51_68
    have w52_6c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m52]; exact w51_6c
    have w52_70 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m52]; exact w51_70
    have w52_74 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m52]; exact w51_74
    have w52_78 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m52]; exact w51_78
    have w52_7c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m52]; exact w51_7c
    have w52_80 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m52]; exact w51_80
    have w52_84 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m52]; exact w51_84
    have w52_88 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m52]; exact w51_88
    have w52_8c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m52]; exact w51_8c
    have w52_90 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m52]; exact w51_90
    have w52_94 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m52]; exact w51_94
    have w52_a20 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m52]; exact w51_a20
    have w52_a24 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m52]; exact w51_a24
    have w52_a28 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m52]; exact w51_a28
    have w52_a2c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m52]; exact w51_a2c
    have w52_a30 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m52]; exact w51_a30
    have w52_a34 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m52]; exact w51_a34
    have w52_a38 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m52]; exact w51_a38
    have w52_a3c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m52]; exact w51_a3c
    have w52_a40 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m52]; exact w51_a40
    have w52_a44 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m52]; exact w51_a44
    have w52_1020 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m52]; exact w51_1020
    have w52_1024 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m52]; exact w51_1024
    have w52_1028 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m52]; exact w51_1028
    have w52_102c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m52]; exact w51_102c
    have w52_1480 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m52]; exact w51_1480
    have w52_1484 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m52]; exact w51_1484
    have w52_1488 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m52]; exact w51_1488
    have w52_148c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m52]; exact w51_148c
    have b52_1030 : n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m52]; exact b51_1030
    clear w51_44 b51_1030 w51_148c w51_1488 w51_1484 w51_1480 w51_102c w51_1028 w51_1024 w51_1020 w51_a44 w51_a40 w51_a3c w51_a38 w51_a34 w51_a30 w51_a2c w51_a28 w51_a24 w51_a20 w51_94 w51_90 w51_8c w51_88 w51_84 w51_80 w51_7c w51_78 w51_74 w51_70 w51_6c w51_68 w51_64 w51_60 w51_5c w51_58 w51_54 w51_50 w51_4c w51_48 w51_40 w51_3c w51_38 w51_34 w51_30 g51_27 g51_26 g51_25 g51_23 g51_22 g51_21 g51_19 g51_18 g51_12 g51_11 g51_10 g51_9 g51_8 g51_4 g51_3 g51_2 V51 E51 fR51 t51 rg51 W51 K51 fr51 s51 d51
    -- 0xB46: lw
    obtain ⟨n53, d53, u53⟩ := s52.lw E52.self sv_at_b46 (off' := 0xB48) (by decide)
      (by rw [g52_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s53 : St n53.mem SV n53 0xB48 (reg n53) := ⟨u53.pc, rfl, fun _ => rfl⟩
    have m53 : n53.mem = n52.mem := u53.mem
    have fr53 : ∀ x, SvR B x → n53.mem x = n52.mem x := fun x _ => by rw [m53]
    have t53 : Steps n0 n53 := t52.trans (.single d53)
    have fR53 : ∀ x, SvR B x → n53.mem x = n0.mem x := fun x hx => (fr53 x hx).trans (fR52 x hx)
    have E53 : SvCode n53.mem := E52.fr F fr53
    have V53 : SvSaves B n53.mem v := V52.same m53
    have g53_2 : reg n53 sp = B + 0x21A0 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_2]
    have g53_3 : reg n53 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u53.regs, upd_ne (by decide) (by decide), g52_3]
    have g53_4 : reg n53 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u53.regs, upd_ne (by decide) (by decide), g52_4]
    have g53_8 : reg n53 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_8]
    have g53_9 : reg n53 (9 : Fin 32) = x9 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_9]
    have g53_10 : reg n53 a0 = BitVec.ofNat 32 0x16 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_10]
    have g53_11 : reg n53 a1 = (BitVec.ofNat 8 tl43.tag).zeroExtend 32 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_11]
    have g53_12 : reg n53 a2 = BitVec.ofNat 32 0xC := by rw [u53.regs, upd_ne (by decide) (by decide), g52_12]
    have g53_18 : reg n53 (18 : Fin 32) = out := by rw [u53.regs, upd_ne (by decide) (by decide), g52_18]
    have g53_19 : reg n53 (19 : Fin 32) = bp := by rw [u53.regs, upd_ne (by decide) (by decide), g52_19]
    have g53_21 : reg n53 (21 : Fin 32) = x21 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_21]
    have g53_22 : reg n53 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_22]
    have g53_23 : reg n53 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u53.regs, upd_ne (by decide) (by decide), g52_23]
    have g53_25 : reg n53 (25 : Fin 32) = x25 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_25]
    have g53_26 : reg n53 (26 : Fin 32) = x26 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_26]
    have g53_27 : reg n53 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u53.regs, upd_ne (by decide) (by decide), g52_27]
    have w53_30 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m53]; exact w52_30
    have w53_34 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m53]; exact w52_34
    have w53_38 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m53]; exact w52_38
    have w53_3c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m53]; exact w52_3c
    have w53_40 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m53]; exact w52_40
    have w53_44 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m53]; exact w52_44
    have w53_48 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m53]; exact w52_48
    have w53_4c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m53]; exact w52_4c
    have w53_50 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m53]; exact w52_50
    have w53_54 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m53]; exact w52_54
    have w53_58 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m53]; exact w52_58
    have w53_5c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m53]; exact w52_5c
    have w53_60 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m53]; exact w52_60
    have w53_64 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m53]; exact w52_64
    have w53_68 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m53]; exact w52_68
    have w53_6c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m53]; exact w52_6c
    have w53_70 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m53]; exact w52_70
    have w53_74 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m53]; exact w52_74
    have w53_78 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m53]; exact w52_78
    have w53_7c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m53]; exact w52_7c
    have w53_80 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m53]; exact w52_80
    have w53_84 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m53]; exact w52_84
    have w53_88 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m53]; exact w52_88
    have w53_8c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m53]; exact w52_8c
    have w53_90 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m53]; exact w52_90
    have w53_94 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m53]; exact w52_94
    have w53_a20 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m53]; exact w52_a20
    have w53_a24 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m53]; exact w52_a24
    have w53_a28 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m53]; exact w52_a28
    have w53_a2c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m53]; exact w52_a2c
    have w53_a30 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m53]; exact w52_a30
    have w53_a34 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m53]; exact w52_a34
    have w53_a38 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m53]; exact w52_a38
    have w53_a3c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m53]; exact w52_a3c
    have w53_a40 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m53]; exact w52_a40
    have w53_a44 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m53]; exact w52_a44
    have w53_1020 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m53]; exact w52_1020
    have w53_1024 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m53]; exact w52_1024
    have w53_1028 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m53]; exact w52_1028
    have w53_102c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m53]; exact w52_102c
    have w53_1480 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m53]; exact w52_1480
    have w53_1484 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m53]; exact w52_1484
    have w53_1488 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m53]; exact w52_1488
    have w53_148c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m53]; exact w52_148c
    have b53_1030 : n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m53]; exact b52_1030
    clear b52_1030 w52_148c w52_1488 w52_1484 w52_1480 w52_102c w52_1028 w52_1024 w52_1020 w52_a44 w52_a40 w52_a3c w52_a38 w52_a34 w52_a30 w52_a2c w52_a28 w52_a24 w52_a20 w52_94 w52_90 w52_8c w52_88 w52_84 w52_80 w52_7c w52_78 w52_74 w52_70 w52_6c w52_68 w52_64 w52_60 w52_5c w52_58 w52_54 w52_50 w52_4c w52_48 w52_44 w52_40 w52_3c w52_38 w52_34 w52_30 g52_27 g52_26 g52_25 g52_23 g52_22 g52_21 g52_19 g52_18 g52_12 g52_11 g52_10 g52_9 g52_8 g52_4 g52_3 g52_2 V52 E52 fR52 t52 fr52 m52 s52 u52 d52
    -- 0xB48: j
    obtain ⟨n54, d54, u54⟩ := s53.jump E53.self sv_at_b48 (off' := 0x966) (by decide)
      (by rw [s53.pc]; decide)
    have s54 : St n54.mem SV n54 0x966 (reg n54) := ⟨u54.pc, rfl, fun _ => rfl⟩
    have m54 : n54.mem = n53.mem := u54.mem
    have fr54 : ∀ x, SvR B x → n54.mem x = n53.mem x := fun x _ => by rw [m54]
    have t54 : Steps n0 n54 := t53.trans (.single d54)
    have fR54 : ∀ x, SvR B x → n54.mem x = n0.mem x := fun x hx => (fr54 x hx).trans (fR53 x hx)
    have E54 : SvCode n54.mem := E53.fr F fr54
    have V54 : SvSaves B n54.mem v := V53.same m54
    have g54_2 : reg n54 sp = B + 0x21A0 := by rw [u54.regs, g53_2]
    have g54_3 : reg n54 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u54.regs, g53_3]
    have g54_4 : reg n54 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u54.regs, g53_4]
    have g54_8 : reg n54 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u54.regs, g53_8]
    have g54_9 : reg n54 (9 : Fin 32) = x9 := by rw [u54.regs, g53_9]
    have g54_10 : reg n54 a0 = BitVec.ofNat 32 0x16 := by rw [u54.regs, g53_10]
    have g54_11 : reg n54 a1 = (BitVec.ofNat 8 tl43.tag).zeroExtend 32 := by rw [u54.regs, g53_11]
    have g54_12 : reg n54 a2 = BitVec.ofNat 32 0xC := by rw [u54.regs, g53_12]
    have g54_18 : reg n54 (18 : Fin 32) = out := by rw [u54.regs, g53_18]
    have g54_19 : reg n54 (19 : Fin 32) = bp := by rw [u54.regs, g53_19]
    have g54_21 : reg n54 (21 : Fin 32) = x21 := by rw [u54.regs, g53_21]
    have g54_22 : reg n54 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u54.regs, g53_22]
    have g54_23 : reg n54 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u54.regs, g53_23]
    have g54_25 : reg n54 (25 : Fin 32) = x25 := by rw [u54.regs, g53_25]
    have g54_26 : reg n54 (26 : Fin 32) = x26 := by rw [u54.regs, g53_26]
    have g54_27 : reg n54 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u54.regs, g53_27]
    have w54_30 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m54]; exact w53_30
    have w54_34 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m54]; exact w53_34
    have w54_38 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m54]; exact w53_38
    have w54_3c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m54]; exact w53_3c
    have w54_40 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m54]; exact w53_40
    have w54_44 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 := by rw [m54]; exact w53_44
    have w54_48 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m54]; exact w53_48
    have w54_4c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m54]; exact w53_4c
    have w54_50 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m54]; exact w53_50
    have w54_54 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m54]; exact w53_54
    have w54_58 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m54]; exact w53_58
    have w54_5c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m54]; exact w53_5c
    have w54_60 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m54]; exact w53_60
    have w54_64 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m54]; exact w53_64
    have w54_68 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m54]; exact w53_68
    have w54_6c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m54]; exact w53_6c
    have w54_70 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m54]; exact w53_70
    have w54_74 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m54]; exact w53_74
    have w54_78 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m54]; exact w53_78
    have w54_7c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m54]; exact w53_7c
    have w54_80 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m54]; exact w53_80
    have w54_84 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m54]; exact w53_84
    have w54_88 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m54]; exact w53_88
    have w54_8c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m54]; exact w53_8c
    have w54_90 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m54]; exact w53_90
    have w54_94 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m54]; exact w53_94
    have w54_a20 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m54]; exact w53_a20
    have w54_a24 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m54]; exact w53_a24
    have w54_a28 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m54]; exact w53_a28
    have w54_a2c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m54]; exact w53_a2c
    have w54_a30 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m54]; exact w53_a30
    have w54_a34 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m54]; exact w53_a34
    have w54_a38 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m54]; exact w53_a38
    have w54_a3c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m54]; exact w53_a3c
    have w54_a40 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m54]; exact w53_a40
    have w54_a44 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m54]; exact w53_a44
    have w54_1020 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m54]; exact w53_1020
    have w54_1024 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m54]; exact w53_1024
    have w54_1028 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m54]; exact w53_1028
    have w54_102c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m54]; exact w53_102c
    have w54_1480 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m54]; exact w53_1480
    have w54_1484 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m54]; exact w53_1484
    have w54_1488 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m54]; exact w53_1488
    have w54_148c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m54]; exact w53_148c
    have b54_1030 : n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m54]; exact b53_1030
    clear b53_1030 w53_148c w53_1488 w53_1484 w53_1480 w53_102c w53_1028 w53_1024 w53_1020 w53_a44 w53_a40 w53_a3c w53_a38 w53_a34 w53_a30 w53_a2c w53_a28 w53_a24 w53_a20 w53_94 w53_90 w53_8c w53_88 w53_84 w53_80 w53_7c w53_78 w53_74 w53_70 w53_6c w53_68 w53_64 w53_60 w53_5c w53_58 w53_54 w53_50 w53_4c w53_48 w53_44 w53_40 w53_3c w53_38 w53_34 w53_30 g53_27 g53_26 g53_25 g53_23 g53_22 g53_21 g53_19 g53_18 g53_12 g53_11 g53_10 g53_9 g53_8 g53_4 g53_3 g53_2 V53 E53 fR53 t53 fr53 m53 s53 u53 d53
    exact .inl ⟨(fun ⟨tl43', h0', h1', _⟩ => by rw [hr43] at h0'; cases h0'; exact hz_47 h1'), sv_fail F E54 s54 t54 fR54 V54 hret g54_2 g54_18 hO g54_3 g54_4⟩
  -- 0x90A: branch, not taken
  obtain ⟨n48, d48, u48⟩ := s47.notTaken E47.self 0x90E sv_at_90a
    (by decide) (by rw [g47_11, g47_12]; exact br_bne_byte_f (by decide) hz_47)
  have s48 : St n48.mem SV n48 0x90E (reg n48) := ⟨u48.pc, rfl, fun _ => rfl⟩
  have m48 : n48.mem = n47.mem := u48.mem
  have fr48 : ∀ x, SvR B x → n48.mem x = n47.mem x := fun x _ => by rw [m48]
  have t48 : Steps n0 n48 := t47.trans (.single d48)
  have fR48 : ∀ x, SvR B x → n48.mem x = n0.mem x := fun x hx => (fr48 x hx).trans (fR47 x hx)
  have E48 : SvCode n48.mem := E47.fr F fr48
  have V48 : SvSaves B n48.mem v := V47.same m48
  have g48_2 : reg n48 sp = B + 0x21A0 := by rw [u48.regs, g47_2]
  have g48_3 : reg n48 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u48.regs, g47_3]
  have g48_4 : reg n48 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u48.regs, g47_4]
  have g48_8 : reg n48 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u48.regs, g47_8]
  have g48_9 : reg n48 (9 : Fin 32) = x9 := by rw [u48.regs, g47_9]
  have g48_10 : reg n48 a0 = (vp) + BitVec.ofNat 32 tl43.header := by rw [u48.regs, g47_10]
  have g48_11 : reg n48 a1 = (BitVec.ofNat 8 tl43.tag).zeroExtend 32 := by rw [u48.regs, g47_11]
  have g48_12 : reg n48 a2 = BitVec.ofNat 32 0xC := by rw [u48.regs, g47_12]
  have g48_18 : reg n48 (18 : Fin 32) = out := by rw [u48.regs, g47_18]
  have g48_19 : reg n48 (19 : Fin 32) = bp := by rw [u48.regs, g47_19]
  have g48_21 : reg n48 (21 : Fin 32) = x21 := by rw [u48.regs, g47_21]
  have g48_22 : reg n48 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u48.regs, g47_22]
  have g48_23 : reg n48 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u48.regs, g47_23]
  have g48_25 : reg n48 (25 : Fin 32) = x25 := by rw [u48.regs, g47_25]
  have g48_26 : reg n48 (26 : Fin 32) = x26 := by rw [u48.regs, g47_26]
  have g48_27 : reg n48 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u48.regs, g47_27]
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
  have w48_a20 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m48]; exact w47_a20
  have w48_a24 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m48]; exact w47_a24
  have w48_a28 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m48]; exact w47_a28
  have w48_a2c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m48]; exact w47_a2c
  have w48_a30 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m48]; exact w47_a30
  have w48_a34 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m48]; exact w47_a34
  have w48_a38 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m48]; exact w47_a38
  have w48_a3c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m48]; exact w47_a3c
  have w48_a40 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m48]; exact w47_a40
  have w48_a44 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m48]; exact w47_a44
  have w48_1020 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m48]; exact w47_1020
  have w48_1024 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m48]; exact w47_1024
  have w48_1028 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m48]; exact w47_1028
  have w48_102c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m48]; exact w47_102c
  have w48_1480 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m48]; exact w47_1480
  have w48_1484 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m48]; exact w47_1484
  have w48_1488 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m48]; exact w47_1488
  have w48_148c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m48]; exact w47_148c
  have b48_1030 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m48]; exact b47_1030
  clear b47_1030 w47_148c w47_1488 w47_1484 w47_1480 w47_102c w47_1028 w47_1024 w47_1020 w47_a44 w47_a40 w47_a3c w47_a38 w47_a34 w47_a30 w47_a2c w47_a28 w47_a24 w47_a20 w47_94 w47_90 w47_8c w47_88 w47_84 w47_80 w47_7c w47_78 w47_74 w47_70 w47_6c w47_68 w47_64 w47_60 w47_5c w47_58 w47_54 w47_50 w47_4c w47_48 w47_40 w47_3c w47_38 w47_34 w47_30 g47_12 g47_27 g47_26 g47_25 g47_23 g47_22 g47_21 g47_19 g47_18 g47_11 g47_10 g47_9 g47_8 g47_4 g47_3 g47_2 V47 E47 fR47 t47 fr47 rb47 s47 m47 u47 c47
  -- 0x90E: lw
  obtain ⟨n49, d49, u49⟩ := s48.lw E48.self sv_at_90e (off' := 0x912) (by decide)
    (by rw [g48_8, show B + 0x21A0 + BitVec.ofNat 32 0x1320 + 0x16C = B + 0x21A0 + BitVec.ofNat 32 0x148C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s49 : St n49.mem SV n49 0x912 (reg n49) := ⟨u49.pc, rfl, fun _ => rfl⟩
  have m49 : n49.mem = n48.mem := u49.mem
  have fr49 : ∀ x, SvR B x → n49.mem x = n48.mem x := fun x _ => by rw [m49]
  have t49 : Steps n0 n49 := t48.trans (.single d49)
  have fR49 : ∀ x, SvR B x → n49.mem x = n0.mem x := fun x hx => (fr49 x hx).trans (fR48 x hx)
  have E49 : SvCode n49.mem := E48.fr F fr49
  have V49 : SvSaves B n49.mem v := V48.same m49
  have g49_2 : reg n49 sp = B + 0x21A0 := by rw [u49.regs, upd_ne (by decide) (by decide), g48_2]
  have g49_3 : reg n49 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u49.regs, upd_ne (by decide) (by decide), g48_3]
  have g49_4 : reg n49 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u49.regs, upd_ne (by decide) (by decide), g48_4]
  have g49_8 : reg n49 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u49.regs, upd_ne (by decide) (by decide), g48_8]
  have g49_9 : reg n49 (9 : Fin 32) = x9 := by rw [u49.regs, upd_ne (by decide) (by decide), g48_9]
  have g49_10 : reg n49 a0 = (vp) + BitVec.ofNat 32 tl43.header := by rw [u49.regs, upd_ne (by decide) (by decide), g48_10]
  have g49_12 : reg n49 a2 = BitVec.ofNat 32 0xC := by rw [u49.regs, upd_ne (by decide) (by decide), g48_12]
  have g49_18 : reg n49 (18 : Fin 32) = out := by rw [u49.regs, upd_ne (by decide) (by decide), g48_18]
  have g49_19 : reg n49 (19 : Fin 32) = bp := by rw [u49.regs, upd_ne (by decide) (by decide), g48_19]
  have g49_21 : reg n49 (21 : Fin 32) = x21 := by rw [u49.regs, upd_ne (by decide) (by decide), g48_21]
  have g49_22 : reg n49 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u49.regs, upd_ne (by decide) (by decide), g48_22]
  have g49_23 : reg n49 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u49.regs, upd_ne (by decide) (by decide), g48_23]
  have g49_25 : reg n49 (25 : Fin 32) = x25 := by rw [u49.regs, upd_ne (by decide) (by decide), g48_25]
  have g49_26 : reg n49 (26 : Fin 32) = x26 := by rw [u49.regs, upd_ne (by decide) (by decide), g48_26]
  have g49_27 : reg n49 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u49.regs, upd_ne (by decide) (by decide), g48_27]
  have g49_11 : reg n49 a1 = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by
    rw [u49.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g48_8, show B + 0x21A0 + BitVec.ofNat 32 0x1320 + 0x16C = B + 0x21A0 + BitVec.ofNat 32 0x148C by sv_addr, w48_148c]
  have w49_30 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m49]; exact w48_30
  have w49_34 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m49]; exact w48_34
  have w49_38 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m49]; exact w48_38
  have w49_3c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m49]; exact w48_3c
  have w49_40 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m49]; exact w48_40
  have w49_48 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m49]; exact w48_48
  have w49_4c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m49]; exact w48_4c
  have w49_50 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m49]; exact w48_50
  have w49_54 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m49]; exact w48_54
  have w49_58 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m49]; exact w48_58
  have w49_5c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m49]; exact w48_5c
  have w49_60 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m49]; exact w48_60
  have w49_64 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m49]; exact w48_64
  have w49_68 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m49]; exact w48_68
  have w49_6c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m49]; exact w48_6c
  have w49_70 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m49]; exact w48_70
  have w49_74 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m49]; exact w48_74
  have w49_78 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m49]; exact w48_78
  have w49_7c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m49]; exact w48_7c
  have w49_80 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m49]; exact w48_80
  have w49_84 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m49]; exact w48_84
  have w49_88 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m49]; exact w48_88
  have w49_8c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m49]; exact w48_8c
  have w49_90 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m49]; exact w48_90
  have w49_94 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m49]; exact w48_94
  have w49_a20 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m49]; exact w48_a20
  have w49_a24 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m49]; exact w48_a24
  have w49_a28 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m49]; exact w48_a28
  have w49_a2c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m49]; exact w48_a2c
  have w49_a30 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m49]; exact w48_a30
  have w49_a34 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m49]; exact w48_a34
  have w49_a38 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m49]; exact w48_a38
  have w49_a3c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m49]; exact w48_a3c
  have w49_a40 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m49]; exact w48_a40
  have w49_a44 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m49]; exact w48_a44
  have w49_1020 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m49]; exact w48_1020
  have w49_1024 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m49]; exact w48_1024
  have w49_1028 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m49]; exact w48_1028
  have w49_102c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m49]; exact w48_102c
  have w49_1480 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m49]; exact w48_1480
  have w49_1484 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m49]; exact w48_1484
  have w49_1488 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m49]; exact w48_1488
  have w49_148c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m49]; exact w48_148c
  have b49_1030 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m49]; exact b48_1030
  clear b48_1030 w48_148c w48_1488 w48_1484 w48_1480 w48_102c w48_1028 w48_1024 w48_1020 w48_a44 w48_a40 w48_a3c w48_a38 w48_a34 w48_a30 w48_a2c w48_a28 w48_a24 w48_a20 w48_94 w48_90 w48_8c w48_88 w48_84 w48_80 w48_7c w48_78 w48_74 w48_70 w48_6c w48_68 w48_64 w48_60 w48_5c w48_58 w48_54 w48_50 w48_4c w48_48 w48_40 w48_3c w48_38 w48_34 w48_30 g48_27 g48_26 g48_25 g48_23 g48_22 g48_21 g48_19 g48_18 g48_12 g48_11 g48_10 g48_9 g48_8 g48_4 g48_3 g48_2 V48 E48 fR48 t48 fr48 m48 s48 u48 d48
  by_cases hz_49 : (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) = 0
  rotate_left
  · -- 0x912: branch, taken
    obtain ⟨n50, d50, u50⟩ := s49.taken E49.self 0xB36 sv_at_912
      (by decide) (by rw [g49_11, s49.zero]; exact br_bne_t hz_49)
    have s50 : St n50.mem SV n50 0xB36 (reg n50) := ⟨u50.pc, rfl, fun _ => rfl⟩
    have m50 : n50.mem = n49.mem := u50.mem
    have fr50 : ∀ x, SvR B x → n50.mem x = n49.mem x := fun x _ => by rw [m50]
    have t50 : Steps n0 n50 := t49.trans (.single d50)
    have fR50 : ∀ x, SvR B x → n50.mem x = n0.mem x := fun x hx => (fr50 x hx).trans (fR49 x hx)
    have E50 : SvCode n50.mem := E49.fr F fr50
    have V50 : SvSaves B n50.mem v := V49.same m50
    have g50_2 : reg n50 sp = B + 0x21A0 := by rw [u50.regs, g49_2]
    have g50_3 : reg n50 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u50.regs, g49_3]
    have g50_4 : reg n50 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u50.regs, g49_4]
    have g50_8 : reg n50 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u50.regs, g49_8]
    have g50_9 : reg n50 (9 : Fin 32) = x9 := by rw [u50.regs, g49_9]
    have g50_10 : reg n50 a0 = (vp) + BitVec.ofNat 32 tl43.header := by rw [u50.regs, g49_10]
    have g50_11 : reg n50 a1 = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [u50.regs, g49_11]
    have g50_12 : reg n50 a2 = BitVec.ofNat 32 0xC := by rw [u50.regs, g49_12]
    have g50_18 : reg n50 (18 : Fin 32) = out := by rw [u50.regs, g49_18]
    have g50_19 : reg n50 (19 : Fin 32) = bp := by rw [u50.regs, g49_19]
    have g50_21 : reg n50 (21 : Fin 32) = x21 := by rw [u50.regs, g49_21]
    have g50_22 : reg n50 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u50.regs, g49_22]
    have g50_23 : reg n50 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u50.regs, g49_23]
    have g50_25 : reg n50 (25 : Fin 32) = x25 := by rw [u50.regs, g49_25]
    have g50_26 : reg n50 (26 : Fin 32) = x26 := by rw [u50.regs, g49_26]
    have g50_27 : reg n50 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u50.regs, g49_27]
    have w50_30 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m50]; exact w49_30
    have w50_34 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m50]; exact w49_34
    have w50_38 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m50]; exact w49_38
    have w50_3c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m50]; exact w49_3c
    have w50_40 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m50]; exact w49_40
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
    have w50_a20 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m50]; exact w49_a20
    have w50_a24 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m50]; exact w49_a24
    have w50_a28 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m50]; exact w49_a28
    have w50_a2c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m50]; exact w49_a2c
    have w50_a30 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m50]; exact w49_a30
    have w50_a34 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m50]; exact w49_a34
    have w50_a38 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m50]; exact w49_a38
    have w50_a3c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m50]; exact w49_a3c
    have w50_a40 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m50]; exact w49_a40
    have w50_a44 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m50]; exact w49_a44
    have w50_1020 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m50]; exact w49_1020
    have w50_1024 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m50]; exact w49_1024
    have w50_1028 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m50]; exact w49_1028
    have w50_102c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m50]; exact w49_102c
    have w50_1480 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m50]; exact w49_1480
    have w50_1484 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m50]; exact w49_1484
    have w50_1488 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m50]; exact w49_1488
    have w50_148c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m50]; exact w49_148c
    have b50_1030 : n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m50]; exact b49_1030
    clear b49_1030 w49_148c w49_1488 w49_1484 w49_1480 w49_102c w49_1028 w49_1024 w49_1020 w49_a44 w49_a40 w49_a3c w49_a38 w49_a34 w49_a30 w49_a2c w49_a28 w49_a24 w49_a20 w49_94 w49_90 w49_8c w49_88 w49_84 w49_80 w49_7c w49_78 w49_74 w49_70 w49_6c w49_68 w49_64 w49_60 w49_5c w49_58 w49_54 w49_50 w49_4c w49_48 w49_40 w49_3c w49_38 w49_34 w49_30 g49_11 g49_27 g49_26 g49_25 g49_23 g49_22 g49_21 g49_19 g49_18 g49_12 g49_10 g49_9 g49_8 g49_4 g49_3 g49_2 V49 E49 fR49 t49 fr49 m49 s49 u49 d49
    -- 0xB36
    obtain ⟨n51, c51, u51⟩ := s50.block svDp1b36 E50.self svDp1b36_end
      ⟨trivial, trivial⟩
    have m51 : n51.mem = n50.mem := u51.mem
    have s51 : St n51.mem SV n51 0xB38 (reg n51) := ⟨u51.pc, rfl, fun _ => rfl⟩
    have rb51 : ∀ q, reg n51 q = (runBlock svDp1b36 (n50.mem, reg n50)).2 q := fun q => by rw [u51.regs]
    have fr51 : ∀ x, SvR B x → n51.mem x = n50.mem x := fun x _ => by rw [m51]
    have t51 : Steps n0 n51 := t50.trans c51
    have fR51 : ∀ x, SvR B x → n51.mem x = n0.mem x := fun x hx => (fr51 x hx).trans (fR50 x hx)
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
    have g51_11 : reg n51 a1 = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by
      rw [rb51, runBlock_reg _ _ _ a1 s50.zero (by decide), g50_11]
    have g51_12 : reg n51 a2 = BitVec.ofNat 32 0xC := by
      rw [rb51, runBlock_reg _ _ _ a2 s50.zero (by decide), g50_12]
    have g51_18 : reg n51 (18 : Fin 32) = out := by
      rw [rb51, runBlock_reg _ _ _ (18 : Fin 32) s50.zero (by decide), g50_18]
    have g51_19 : reg n51 (19 : Fin 32) = bp := by
      rw [rb51, runBlock_reg _ _ _ (19 : Fin 32) s50.zero (by decide), g50_19]
    have g51_21 : reg n51 (21 : Fin 32) = x21 := by
      rw [rb51, runBlock_reg _ _ _ (21 : Fin 32) s50.zero (by decide), g50_21]
    have g51_22 : reg n51 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb51, runBlock_reg _ _ _ (22 : Fin 32) s50.zero (by decide), g50_22]
    have g51_23 : reg n51 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by
      rw [rb51, runBlock_reg _ _ _ (23 : Fin 32) s50.zero (by decide), g50_23]
    have g51_25 : reg n51 (25 : Fin 32) = x25 := by
      rw [rb51, runBlock_reg _ _ _ (25 : Fin 32) s50.zero (by decide), g50_25]
    have g51_26 : reg n51 (26 : Fin 32) = x26 := by
      rw [rb51, runBlock_reg _ _ _ (26 : Fin 32) s50.zero (by decide), g50_26]
    have g51_27 : reg n51 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb51, runBlock_reg _ _ _ (27 : Fin 32) s50.zero (by decide), g50_27]
    have g51_10 : reg n51 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb51]; simp +decide only [runBlock, BInstr.run, svDp1b36, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g50_2, g50_3, g50_4, g50_8, g50_9, g50_10, g50_11, g50_12, g50_18, g50_19, g50_21, g50_22, g50_23, g50_25, g50_26, g50_27, s50.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have w51_30 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m51]; exact w50_30
    have w51_34 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m51]; exact w50_34
    have w51_38 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m51]; exact w50_38
    have w51_3c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m51]; exact w50_3c
    have w51_40 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m51]; exact w50_40
    have w51_48 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m51]; exact w50_48
    have w51_4c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m51]; exact w50_4c
    have w51_50 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m51]; exact w50_50
    have w51_54 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m51]; exact w50_54
    have w51_58 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m51]; exact w50_58
    have w51_5c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m51]; exact w50_5c
    have w51_60 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m51]; exact w50_60
    have w51_64 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m51]; exact w50_64
    have w51_68 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m51]; exact w50_68
    have w51_6c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m51]; exact w50_6c
    have w51_70 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m51]; exact w50_70
    have w51_74 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m51]; exact w50_74
    have w51_78 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m51]; exact w50_78
    have w51_7c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m51]; exact w50_7c
    have w51_80 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m51]; exact w50_80
    have w51_84 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m51]; exact w50_84
    have w51_88 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m51]; exact w50_88
    have w51_8c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m51]; exact w50_8c
    have w51_90 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m51]; exact w50_90
    have w51_94 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m51]; exact w50_94
    have w51_a20 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m51]; exact w50_a20
    have w51_a24 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m51]; exact w50_a24
    have w51_a28 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m51]; exact w50_a28
    have w51_a2c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m51]; exact w50_a2c
    have w51_a30 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m51]; exact w50_a30
    have w51_a34 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m51]; exact w50_a34
    have w51_a38 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m51]; exact w50_a38
    have w51_a3c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m51]; exact w50_a3c
    have w51_a40 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m51]; exact w50_a40
    have w51_a44 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m51]; exact w50_a44
    have w51_1020 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m51]; exact w50_1020
    have w51_1024 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m51]; exact w50_1024
    have w51_1028 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m51]; exact w50_1028
    have w51_102c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m51]; exact w50_102c
    have w51_1480 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m51]; exact w50_1480
    have w51_1484 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m51]; exact w50_1484
    have w51_1488 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m51]; exact w50_1488
    have w51_148c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m51]; exact w50_148c
    have b51_1030 : n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m51]; exact b50_1030
    clear b50_1030 w50_148c w50_1488 w50_1484 w50_1480 w50_102c w50_1028 w50_1024 w50_1020 w50_a44 w50_a40 w50_a3c w50_a38 w50_a34 w50_a30 w50_a2c w50_a28 w50_a24 w50_a20 w50_94 w50_90 w50_8c w50_88 w50_84 w50_80 w50_7c w50_78 w50_74 w50_70 w50_6c w50_68 w50_64 w50_60 w50_5c w50_58 w50_54 w50_50 w50_4c w50_48 w50_40 w50_3c w50_38 w50_34 w50_30 g50_27 g50_26 g50_25 g50_23 g50_22 g50_21 g50_19 g50_18 g50_12 g50_11 g50_10 g50_9 g50_8 g50_4 g50_3 g50_2 V50 E50 fR50 t50 fr50 m50 s50 u50 d50
    -- 0xB38: sw
    obtain ⟨n52, d52, s52, fr52, K52, W52, rg52⟩ := sv_sw F E51 s51 sv_at_b38 (off' := 0xB3A) (c := 0x44)
      (by decide) (by rw [g51_2]; sv_addr) (by decide) (by decide)
    have t52 : Steps n0 n52 := t51.trans d52
    have fR52 : ∀ x, SvR B x → n52.mem x = n0.mem x := fun x hx => (fr52 x hx).trans (fR51 x hx)
    have E52 : SvCode n52.mem := E51.fr F fr52
    have V52 : SvSaves B n52.mem v := V51.keep K52 (by decide)
    have g52_2 : reg n52 sp = B + 0x21A0 := by rw [rg52 sp, g51_2]
    have g52_3 : reg n52 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg52 (3 : Fin 32), g51_3]
    have g52_4 : reg n52 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg52 (4 : Fin 32), g51_4]
    have g52_8 : reg n52 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg52 (8 : Fin 32), g51_8]
    have g52_9 : reg n52 (9 : Fin 32) = x9 := by rw [rg52 (9 : Fin 32), g51_9]
    have g52_10 : reg n52 a0 = BitVec.ofNat 32 0x1 := by rw [rg52 a0, g51_10]
    have g52_11 : reg n52 a1 = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [rg52 a1, g51_11]
    have g52_12 : reg n52 a2 = BitVec.ofNat 32 0xC := by rw [rg52 a2, g51_12]
    have g52_18 : reg n52 (18 : Fin 32) = out := by rw [rg52 (18 : Fin 32), g51_18]
    have g52_19 : reg n52 (19 : Fin 32) = bp := by rw [rg52 (19 : Fin 32), g51_19]
    have g52_21 : reg n52 (21 : Fin 32) = x21 := by rw [rg52 (21 : Fin 32), g51_21]
    have g52_22 : reg n52 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [rg52 (22 : Fin 32), g51_22]
    have g52_23 : reg n52 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [rg52 (23 : Fin 32), g51_23]
    have g52_25 : reg n52 (25 : Fin 32) = x25 := by rw [rg52 (25 : Fin 32), g51_25]
    have g52_26 : reg n52 (26 : Fin 32) = x26 := by rw [rg52 (26 : Fin 32), g51_26]
    have g52_27 : reg n52 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg52 (27 : Fin 32), g51_27]
    have w52_30 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K52.w32 (by decide) (by decide)).trans w51_30
    have w52_34 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K52.w32 (by decide) (by decide)).trans w51_34
    have w52_38 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K52.w32 (by decide) (by decide)).trans w51_38
    have w52_3c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K52.w32 (by decide) (by decide)).trans w51_3c
    have w52_40 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K52.w32 (by decide) (by decide)).trans w51_40
    have w52_48 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K52.w32 (by decide) (by decide)).trans w51_48
    have w52_4c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K52.w32 (by decide) (by decide)).trans w51_4c
    have w52_50 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K52.w32 (by decide) (by decide)).trans w51_50
    have w52_54 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K52.w32 (by decide) (by decide)).trans w51_54
    have w52_58 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K52.w32 (by decide) (by decide)).trans w51_58
    have w52_5c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K52.w32 (by decide) (by decide)).trans w51_5c
    have w52_60 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K52.w32 (by decide) (by decide)).trans w51_60
    have w52_64 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K52.w32 (by decide) (by decide)).trans w51_64
    have w52_68 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K52.w32 (by decide) (by decide)).trans w51_68
    have w52_6c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K52.w32 (by decide) (by decide)).trans w51_6c
    have w52_70 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K52.w32 (by decide) (by decide)).trans w51_70
    have w52_74 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K52.w32 (by decide) (by decide)).trans w51_74
    have w52_78 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K52.w32 (by decide) (by decide)).trans w51_78
    have w52_7c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K52.w32 (by decide) (by decide)).trans w51_7c
    have w52_80 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K52.w32 (by decide) (by decide)).trans w51_80
    have w52_84 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K52.w32 (by decide) (by decide)).trans w51_84
    have w52_88 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K52.w32 (by decide) (by decide)).trans w51_88
    have w52_8c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K52.w32 (by decide) (by decide)).trans w51_8c
    have w52_90 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K52.w32 (by decide) (by decide)).trans w51_90
    have w52_94 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K52.w32 (by decide) (by decide)).trans w51_94
    have w52_a20 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K52.w32 (by decide) (by decide)).trans w51_a20
    have w52_a24 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K52.w32 (by decide) (by decide)).trans w51_a24
    have w52_a28 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := (K52.w32 (by decide) (by decide)).trans w51_a28
    have w52_a2c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K52.w32 (by decide) (by decide)).trans w51_a2c
    have w52_a30 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K52.w32 (by decide) (by decide)).trans w51_a30
    have w52_a34 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K52.w32 (by decide) (by decide)).trans w51_a34
    have w52_a38 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K52.w32 (by decide) (by decide)).trans w51_a38
    have w52_a3c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K52.w32 (by decide) (by decide)).trans w51_a3c
    have w52_a40 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K52.w32 (by decide) (by decide)).trans w51_a40
    have w52_a44 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K52.w32 (by decide) (by decide)).trans w51_a44
    have w52_1020 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := (K52.w32 (by decide) (by decide)).trans w51_1020
    have w52_1024 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := (K52.w32 (by decide) (by decide)).trans w51_1024
    have w52_1028 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := (K52.w32 (by decide) (by decide)).trans w51_1028
    have w52_102c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := (K52.w32 (by decide) (by decide)).trans w51_102c
    have w52_1480 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K52.w32 (by decide) (by decide)).trans w51_1480
    have w52_1484 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K52.w32 (by decide) (by decide)).trans w51_1484
    have w52_1488 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := (K52.w32 (by decide) (by decide)).trans w51_1488
    have w52_148c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := (K52.w32 (by decide) (by decide)).trans w51_148c
    have b52_1030 : n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := (K52.b8 (by decide) (by decide)).trans b51_1030
    have w52_44 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [W52, g51_10]
    clear b51_1030 w51_148c w51_1488 w51_1484 w51_1480 w51_102c w51_1028 w51_1024 w51_1020 w51_a44 w51_a40 w51_a3c w51_a38 w51_a34 w51_a30 w51_a2c w51_a28 w51_a24 w51_a20 w51_94 w51_90 w51_8c w51_88 w51_84 w51_80 w51_7c w51_78 w51_74 w51_70 w51_6c w51_68 w51_64 w51_60 w51_5c w51_58 w51_54 w51_50 w51_4c w51_48 w51_40 w51_3c w51_38 w51_34 w51_30 g51_10 g51_27 g51_26 g51_25 g51_23 g51_22 g51_21 g51_19 g51_18 g51_12 g51_11 g51_9 g51_8 g51_4 g51_3 g51_2 V51 E51 fR51 t51 fr51 rb51 s51 m51 u51 c51
    -- 0xB3A: j
    obtain ⟨n53, d53, u53⟩ := s52.jump E52.self sv_at_b3a (off' := 0xB46) (by decide)
      (by rw [s52.pc]; decide)
    have s53 : St n53.mem SV n53 0xB46 (reg n53) := ⟨u53.pc, rfl, fun _ => rfl⟩
    have m53 : n53.mem = n52.mem := u53.mem
    have fr53 : ∀ x, SvR B x → n53.mem x = n52.mem x := fun x _ => by rw [m53]
    have t53 : Steps n0 n53 := t52.trans (.single d53)
    have fR53 : ∀ x, SvR B x → n53.mem x = n0.mem x := fun x hx => (fr53 x hx).trans (fR52 x hx)
    have E53 : SvCode n53.mem := E52.fr F fr53
    have V53 : SvSaves B n53.mem v := V52.same m53
    have g53_2 : reg n53 sp = B + 0x21A0 := by rw [u53.regs, g52_2]
    have g53_3 : reg n53 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u53.regs, g52_3]
    have g53_4 : reg n53 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u53.regs, g52_4]
    have g53_8 : reg n53 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u53.regs, g52_8]
    have g53_9 : reg n53 (9 : Fin 32) = x9 := by rw [u53.regs, g52_9]
    have g53_10 : reg n53 a0 = BitVec.ofNat 32 0x1 := by rw [u53.regs, g52_10]
    have g53_11 : reg n53 a1 = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [u53.regs, g52_11]
    have g53_12 : reg n53 a2 = BitVec.ofNat 32 0xC := by rw [u53.regs, g52_12]
    have g53_18 : reg n53 (18 : Fin 32) = out := by rw [u53.regs, g52_18]
    have g53_19 : reg n53 (19 : Fin 32) = bp := by rw [u53.regs, g52_19]
    have g53_21 : reg n53 (21 : Fin 32) = x21 := by rw [u53.regs, g52_21]
    have g53_22 : reg n53 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u53.regs, g52_22]
    have g53_23 : reg n53 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u53.regs, g52_23]
    have g53_25 : reg n53 (25 : Fin 32) = x25 := by rw [u53.regs, g52_25]
    have g53_26 : reg n53 (26 : Fin 32) = x26 := by rw [u53.regs, g52_26]
    have g53_27 : reg n53 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u53.regs, g52_27]
    have w53_30 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m53]; exact w52_30
    have w53_34 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m53]; exact w52_34
    have w53_38 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m53]; exact w52_38
    have w53_3c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m53]; exact w52_3c
    have w53_40 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m53]; exact w52_40
    have w53_44 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m53]; exact w52_44
    have w53_48 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m53]; exact w52_48
    have w53_4c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m53]; exact w52_4c
    have w53_50 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m53]; exact w52_50
    have w53_54 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m53]; exact w52_54
    have w53_58 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m53]; exact w52_58
    have w53_5c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m53]; exact w52_5c
    have w53_60 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m53]; exact w52_60
    have w53_64 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m53]; exact w52_64
    have w53_68 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m53]; exact w52_68
    have w53_6c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m53]; exact w52_6c
    have w53_70 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m53]; exact w52_70
    have w53_74 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m53]; exact w52_74
    have w53_78 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m53]; exact w52_78
    have w53_7c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m53]; exact w52_7c
    have w53_80 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m53]; exact w52_80
    have w53_84 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m53]; exact w52_84
    have w53_88 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m53]; exact w52_88
    have w53_8c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m53]; exact w52_8c
    have w53_90 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m53]; exact w52_90
    have w53_94 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m53]; exact w52_94
    have w53_a20 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m53]; exact w52_a20
    have w53_a24 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m53]; exact w52_a24
    have w53_a28 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m53]; exact w52_a28
    have w53_a2c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m53]; exact w52_a2c
    have w53_a30 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m53]; exact w52_a30
    have w53_a34 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m53]; exact w52_a34
    have w53_a38 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m53]; exact w52_a38
    have w53_a3c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m53]; exact w52_a3c
    have w53_a40 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m53]; exact w52_a40
    have w53_a44 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m53]; exact w52_a44
    have w53_1020 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m53]; exact w52_1020
    have w53_1024 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m53]; exact w52_1024
    have w53_1028 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m53]; exact w52_1028
    have w53_102c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m53]; exact w52_102c
    have w53_1480 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m53]; exact w52_1480
    have w53_1484 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m53]; exact w52_1484
    have w53_1488 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m53]; exact w52_1488
    have w53_148c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m53]; exact w52_148c
    have b53_1030 : n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m53]; exact b52_1030
    clear w52_44 b52_1030 w52_148c w52_1488 w52_1484 w52_1480 w52_102c w52_1028 w52_1024 w52_1020 w52_a44 w52_a40 w52_a3c w52_a38 w52_a34 w52_a30 w52_a2c w52_a28 w52_a24 w52_a20 w52_94 w52_90 w52_8c w52_88 w52_84 w52_80 w52_7c w52_78 w52_74 w52_70 w52_6c w52_68 w52_64 w52_60 w52_5c w52_58 w52_54 w52_50 w52_4c w52_48 w52_40 w52_3c w52_38 w52_34 w52_30 g52_27 g52_26 g52_25 g52_23 g52_22 g52_21 g52_19 g52_18 g52_12 g52_11 g52_10 g52_9 g52_8 g52_4 g52_3 g52_2 V52 E52 fR52 t52 rg52 W52 K52 fr52 s52 d52
    -- 0xB46: lw
    obtain ⟨n54, d54, u54⟩ := s53.lw E53.self sv_at_b46 (off' := 0xB48) (by decide)
      (by rw [g53_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s54 : St n54.mem SV n54 0xB48 (reg n54) := ⟨u54.pc, rfl, fun _ => rfl⟩
    have m54 : n54.mem = n53.mem := u54.mem
    have fr54 : ∀ x, SvR B x → n54.mem x = n53.mem x := fun x _ => by rw [m54]
    have t54 : Steps n0 n54 := t53.trans (.single d54)
    have fR54 : ∀ x, SvR B x → n54.mem x = n0.mem x := fun x hx => (fr54 x hx).trans (fR53 x hx)
    have E54 : SvCode n54.mem := E53.fr F fr54
    have V54 : SvSaves B n54.mem v := V53.same m54
    have g54_2 : reg n54 sp = B + 0x21A0 := by rw [u54.regs, upd_ne (by decide) (by decide), g53_2]
    have g54_3 : reg n54 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u54.regs, upd_ne (by decide) (by decide), g53_3]
    have g54_4 : reg n54 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u54.regs, upd_ne (by decide) (by decide), g53_4]
    have g54_8 : reg n54 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u54.regs, upd_ne (by decide) (by decide), g53_8]
    have g54_9 : reg n54 (9 : Fin 32) = x9 := by rw [u54.regs, upd_ne (by decide) (by decide), g53_9]
    have g54_10 : reg n54 a0 = BitVec.ofNat 32 0x1 := by rw [u54.regs, upd_ne (by decide) (by decide), g53_10]
    have g54_11 : reg n54 a1 = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [u54.regs, upd_ne (by decide) (by decide), g53_11]
    have g54_12 : reg n54 a2 = BitVec.ofNat 32 0xC := by rw [u54.regs, upd_ne (by decide) (by decide), g53_12]
    have g54_18 : reg n54 (18 : Fin 32) = out := by rw [u54.regs, upd_ne (by decide) (by decide), g53_18]
    have g54_19 : reg n54 (19 : Fin 32) = bp := by rw [u54.regs, upd_ne (by decide) (by decide), g53_19]
    have g54_21 : reg n54 (21 : Fin 32) = x21 := by rw [u54.regs, upd_ne (by decide) (by decide), g53_21]
    have g54_22 : reg n54 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u54.regs, upd_ne (by decide) (by decide), g53_22]
    have g54_23 : reg n54 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u54.regs, upd_ne (by decide) (by decide), g53_23]
    have g54_25 : reg n54 (25 : Fin 32) = x25 := by rw [u54.regs, upd_ne (by decide) (by decide), g53_25]
    have g54_26 : reg n54 (26 : Fin 32) = x26 := by rw [u54.regs, upd_ne (by decide) (by decide), g53_26]
    have g54_27 : reg n54 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u54.regs, upd_ne (by decide) (by decide), g53_27]
    have w54_30 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m54]; exact w53_30
    have w54_34 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m54]; exact w53_34
    have w54_38 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m54]; exact w53_38
    have w54_3c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m54]; exact w53_3c
    have w54_40 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m54]; exact w53_40
    have w54_44 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m54]; exact w53_44
    have w54_48 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m54]; exact w53_48
    have w54_4c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m54]; exact w53_4c
    have w54_50 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m54]; exact w53_50
    have w54_54 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m54]; exact w53_54
    have w54_58 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m54]; exact w53_58
    have w54_5c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m54]; exact w53_5c
    have w54_60 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m54]; exact w53_60
    have w54_64 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m54]; exact w53_64
    have w54_68 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m54]; exact w53_68
    have w54_6c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m54]; exact w53_6c
    have w54_70 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m54]; exact w53_70
    have w54_74 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m54]; exact w53_74
    have w54_78 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m54]; exact w53_78
    have w54_7c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m54]; exact w53_7c
    have w54_80 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m54]; exact w53_80
    have w54_84 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m54]; exact w53_84
    have w54_88 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m54]; exact w53_88
    have w54_8c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m54]; exact w53_8c
    have w54_90 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m54]; exact w53_90
    have w54_94 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m54]; exact w53_94
    have w54_a20 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m54]; exact w53_a20
    have w54_a24 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m54]; exact w53_a24
    have w54_a28 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m54]; exact w53_a28
    have w54_a2c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m54]; exact w53_a2c
    have w54_a30 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m54]; exact w53_a30
    have w54_a34 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m54]; exact w53_a34
    have w54_a38 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m54]; exact w53_a38
    have w54_a3c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m54]; exact w53_a3c
    have w54_a40 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m54]; exact w53_a40
    have w54_a44 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m54]; exact w53_a44
    have w54_1020 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m54]; exact w53_1020
    have w54_1024 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m54]; exact w53_1024
    have w54_1028 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m54]; exact w53_1028
    have w54_102c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m54]; exact w53_102c
    have w54_1480 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m54]; exact w53_1480
    have w54_1484 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m54]; exact w53_1484
    have w54_1488 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m54]; exact w53_1488
    have w54_148c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m54]; exact w53_148c
    have b54_1030 : n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m54]; exact b53_1030
    clear b53_1030 w53_148c w53_1488 w53_1484 w53_1480 w53_102c w53_1028 w53_1024 w53_1020 w53_a44 w53_a40 w53_a3c w53_a38 w53_a34 w53_a30 w53_a2c w53_a28 w53_a24 w53_a20 w53_94 w53_90 w53_8c w53_88 w53_84 w53_80 w53_7c w53_78 w53_74 w53_70 w53_6c w53_68 w53_64 w53_60 w53_5c w53_58 w53_54 w53_50 w53_4c w53_48 w53_44 w53_40 w53_3c w53_38 w53_34 w53_30 g53_27 g53_26 g53_25 g53_23 g53_22 g53_21 g53_19 g53_18 g53_12 g53_11 g53_10 g53_9 g53_8 g53_4 g53_3 g53_2 V53 E53 fR53 t53 fr53 m53 s53 u53 d53
    -- 0xB48: j
    obtain ⟨n55, d55, u55⟩ := s54.jump E54.self sv_at_b48 (off' := 0x966) (by decide)
      (by rw [s54.pc]; decide)
    have s55 : St n55.mem SV n55 0x966 (reg n55) := ⟨u55.pc, rfl, fun _ => rfl⟩
    have m55 : n55.mem = n54.mem := u55.mem
    have fr55 : ∀ x, SvR B x → n55.mem x = n54.mem x := fun x _ => by rw [m55]
    have t55 : Steps n0 n55 := t54.trans (.single d55)
    have fR55 : ∀ x, SvR B x → n55.mem x = n0.mem x := fun x hx => (fr55 x hx).trans (fR54 x hx)
    have E55 : SvCode n55.mem := E54.fr F fr55
    have V55 : SvSaves B n55.mem v := V54.same m55
    have g55_2 : reg n55 sp = B + 0x21A0 := by rw [u55.regs, g54_2]
    have g55_3 : reg n55 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u55.regs, g54_3]
    have g55_4 : reg n55 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u55.regs, g54_4]
    have g55_8 : reg n55 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u55.regs, g54_8]
    have g55_9 : reg n55 (9 : Fin 32) = x9 := by rw [u55.regs, g54_9]
    have g55_10 : reg n55 a0 = BitVec.ofNat 32 0x1 := by rw [u55.regs, g54_10]
    have g55_11 : reg n55 a1 = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [u55.regs, g54_11]
    have g55_12 : reg n55 a2 = BitVec.ofNat 32 0xC := by rw [u55.regs, g54_12]
    have g55_18 : reg n55 (18 : Fin 32) = out := by rw [u55.regs, g54_18]
    have g55_19 : reg n55 (19 : Fin 32) = bp := by rw [u55.regs, g54_19]
    have g55_21 : reg n55 (21 : Fin 32) = x21 := by rw [u55.regs, g54_21]
    have g55_22 : reg n55 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u55.regs, g54_22]
    have g55_23 : reg n55 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u55.regs, g54_23]
    have g55_25 : reg n55 (25 : Fin 32) = x25 := by rw [u55.regs, g54_25]
    have g55_26 : reg n55 (26 : Fin 32) = x26 := by rw [u55.regs, g54_26]
    have g55_27 : reg n55 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u55.regs, g54_27]
    have w55_30 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m55]; exact w54_30
    have w55_34 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m55]; exact w54_34
    have w55_38 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m55]; exact w54_38
    have w55_3c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m55]; exact w54_3c
    have w55_40 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m55]; exact w54_40
    have w55_44 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x1 := by rw [m55]; exact w54_44
    have w55_48 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m55]; exact w54_48
    have w55_4c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m55]; exact w54_4c
    have w55_50 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m55]; exact w54_50
    have w55_54 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m55]; exact w54_54
    have w55_58 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m55]; exact w54_58
    have w55_5c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m55]; exact w54_5c
    have w55_60 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m55]; exact w54_60
    have w55_64 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m55]; exact w54_64
    have w55_68 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m55]; exact w54_68
    have w55_6c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m55]; exact w54_6c
    have w55_70 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m55]; exact w54_70
    have w55_74 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m55]; exact w54_74
    have w55_78 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m55]; exact w54_78
    have w55_7c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m55]; exact w54_7c
    have w55_80 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m55]; exact w54_80
    have w55_84 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m55]; exact w54_84
    have w55_88 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m55]; exact w54_88
    have w55_8c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m55]; exact w54_8c
    have w55_90 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m55]; exact w54_90
    have w55_94 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m55]; exact w54_94
    have w55_a20 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m55]; exact w54_a20
    have w55_a24 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m55]; exact w54_a24
    have w55_a28 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m55]; exact w54_a28
    have w55_a2c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m55]; exact w54_a2c
    have w55_a30 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m55]; exact w54_a30
    have w55_a34 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m55]; exact w54_a34
    have w55_a38 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m55]; exact w54_a38
    have w55_a3c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m55]; exact w54_a3c
    have w55_a40 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m55]; exact w54_a40
    have w55_a44 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m55]; exact w54_a44
    have w55_1020 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m55]; exact w54_1020
    have w55_1024 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m55]; exact w54_1024
    have w55_1028 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m55]; exact w54_1028
    have w55_102c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m55]; exact w54_102c
    have w55_1480 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m55]; exact w54_1480
    have w55_1484 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m55]; exact w54_1484
    have w55_1488 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m55]; exact w54_1488
    have w55_148c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m55]; exact w54_148c
    have b55_1030 : n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m55]; exact b54_1030
    clear b54_1030 w54_148c w54_1488 w54_1484 w54_1480 w54_102c w54_1028 w54_1024 w54_1020 w54_a44 w54_a40 w54_a3c w54_a38 w54_a34 w54_a30 w54_a2c w54_a28 w54_a24 w54_a20 w54_94 w54_90 w54_8c w54_88 w54_84 w54_80 w54_7c w54_78 w54_74 w54_70 w54_6c w54_68 w54_64 w54_60 w54_5c w54_58 w54_54 w54_50 w54_4c w54_48 w54_44 w54_40 w54_3c w54_38 w54_34 w54_30 g54_27 g54_26 g54_25 g54_23 g54_22 g54_21 g54_19 g54_18 g54_12 g54_11 g54_10 g54_9 g54_8 g54_4 g54_3 g54_2 V54 E54 fR54 t54 fr54 m54 s54 u54 d54
    exact .inl ⟨(fun ⟨tl43', h0', h1', h2', _⟩ => by rw [hr43] at h0'; cases h0'; exact hz_49 h2'), sv_fail F E55 s55 t55 fR55 V55 hret g55_2 g55_18 hO g55_3 g55_4⟩
  -- 0x912: branch, not taken
  obtain ⟨n50, d50, u50⟩ := s49.notTaken E49.self 0x916 sv_at_912
    (by decide) (by rw [g49_11, s49.zero]; exact br_bne_f hz_49)
  have s50 : St n50.mem SV n50 0x916 (reg n50) := ⟨u50.pc, rfl, fun _ => rfl⟩
  have m50 : n50.mem = n49.mem := u50.mem
  have fr50 : ∀ x, SvR B x → n50.mem x = n49.mem x := fun x _ => by rw [m50]
  have t50 : Steps n0 n50 := t49.trans (.single d50)
  have fR50 : ∀ x, SvR B x → n50.mem x = n0.mem x := fun x hx => (fr50 x hx).trans (fR49 x hx)
  have E50 : SvCode n50.mem := E49.fr F fr50
  have V50 : SvSaves B n50.mem v := V49.same m50
  have g50_2 : reg n50 sp = B + 0x21A0 := by rw [u50.regs, g49_2]
  have g50_3 : reg n50 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u50.regs, g49_3]
  have g50_4 : reg n50 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u50.regs, g49_4]
  have g50_8 : reg n50 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u50.regs, g49_8]
  have g50_9 : reg n50 (9 : Fin 32) = x9 := by rw [u50.regs, g49_9]
  have g50_10 : reg n50 a0 = (vp) + BitVec.ofNat 32 tl43.header := by rw [u50.regs, g49_10]
  have g50_11 : reg n50 a1 = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [u50.regs, g49_11]
  have g50_12 : reg n50 a2 = BitVec.ofNat 32 0xC := by rw [u50.regs, g49_12]
  have g50_18 : reg n50 (18 : Fin 32) = out := by rw [u50.regs, g49_18]
  have g50_19 : reg n50 (19 : Fin 32) = bp := by rw [u50.regs, g49_19]
  have g50_21 : reg n50 (21 : Fin 32) = x21 := by rw [u50.regs, g49_21]
  have g50_22 : reg n50 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u50.regs, g49_22]
  have g50_23 : reg n50 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u50.regs, g49_23]
  have g50_25 : reg n50 (25 : Fin 32) = x25 := by rw [u50.regs, g49_25]
  have g50_26 : reg n50 (26 : Fin 32) = x26 := by rw [u50.regs, g49_26]
  have g50_27 : reg n50 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u50.regs, g49_27]
  have w50_30 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m50]; exact w49_30
  have w50_34 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m50]; exact w49_34
  have w50_38 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m50]; exact w49_38
  have w50_3c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m50]; exact w49_3c
  have w50_40 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m50]; exact w49_40
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
  have w50_a20 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m50]; exact w49_a20
  have w50_a24 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m50]; exact w49_a24
  have w50_a28 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m50]; exact w49_a28
  have w50_a2c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m50]; exact w49_a2c
  have w50_a30 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m50]; exact w49_a30
  have w50_a34 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m50]; exact w49_a34
  have w50_a38 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m50]; exact w49_a38
  have w50_a3c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m50]; exact w49_a3c
  have w50_a40 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m50]; exact w49_a40
  have w50_a44 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m50]; exact w49_a44
  have w50_1020 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m50]; exact w49_1020
  have w50_1024 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m50]; exact w49_1024
  have w50_1028 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m50]; exact w49_1028
  have w50_102c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m50]; exact w49_102c
  have w50_1480 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m50]; exact w49_1480
  have w50_1484 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m50]; exact w49_1484
  have w50_1488 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m50]; exact w49_1488
  have w50_148c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m50]; exact w49_148c
  have b50_1030 : n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m50]; exact b49_1030
  clear b49_1030 w49_148c w49_1488 w49_1484 w49_1480 w49_102c w49_1028 w49_1024 w49_1020 w49_a44 w49_a40 w49_a3c w49_a38 w49_a34 w49_a30 w49_a2c w49_a28 w49_a24 w49_a20 w49_94 w49_90 w49_8c w49_88 w49_84 w49_80 w49_7c w49_78 w49_74 w49_70 w49_6c w49_68 w49_64 w49_60 w49_5c w49_58 w49_54 w49_50 w49_4c w49_48 w49_40 w49_3c w49_38 w49_34 w49_30 g49_11 g49_27 g49_26 g49_25 g49_23 g49_22 g49_21 g49_19 g49_18 g49_12 g49_10 g49_9 g49_8 g49_4 g49_3 g49_2 V49 E49 fR49 t49 fr49 m49 s49 u49 d49
  -- 0x916: lw
  obtain ⟨n51, d51, u51⟩ := s50.lw E50.self sv_at_916 (off' := 0x91A) (by decide)
    (by rw [g50_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x604 = B + 0x21A0 + BitVec.ofNat 32 0x1024 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s51 : St n51.mem SV n51 0x91A (reg n51) := ⟨u51.pc, rfl, fun _ => rfl⟩
  have m51 : n51.mem = n50.mem := u51.mem
  have fr51 : ∀ x, SvR B x → n51.mem x = n50.mem x := fun x _ => by rw [m51]
  have t51 : Steps n0 n51 := t50.trans (.single d51)
  have fR51 : ∀ x, SvR B x → n51.mem x = n0.mem x := fun x hx => (fr51 x hx).trans (fR50 x hx)
  have E51 : SvCode n51.mem := E50.fr F fr51
  have V51 : SvSaves B n51.mem v := V50.same m51
  have g51_2 : reg n51 sp = B + 0x21A0 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_2]
  have g51_3 : reg n51 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u51.regs, upd_ne (by decide) (by decide), g50_3]
  have g51_4 : reg n51 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u51.regs, upd_ne (by decide) (by decide), g50_4]
  have g51_8 : reg n51 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_8]
  have g51_9 : reg n51 (9 : Fin 32) = x9 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_9]
  have g51_10 : reg n51 a0 = (vp) + BitVec.ofNat 32 tl43.header := by rw [u51.regs, upd_ne (by decide) (by decide), g50_10]
  have g51_12 : reg n51 a2 = BitVec.ofNat 32 0xC := by rw [u51.regs, upd_ne (by decide) (by decide), g50_12]
  have g51_18 : reg n51 (18 : Fin 32) = out := by rw [u51.regs, upd_ne (by decide) (by decide), g50_18]
  have g51_19 : reg n51 (19 : Fin 32) = bp := by rw [u51.regs, upd_ne (by decide) (by decide), g50_19]
  have g51_21 : reg n51 (21 : Fin 32) = x21 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_21]
  have g51_22 : reg n51 (22 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_22]
  have g51_23 : reg n51 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u51.regs, upd_ne (by decide) (by decide), g50_23]
  have g51_25 : reg n51 (25 : Fin 32) = x25 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_25]
  have g51_26 : reg n51 (26 : Fin 32) = x26 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_26]
  have g51_27 : reg n51 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u51.regs, upd_ne (by decide) (by decide), g50_27]
  have g51_11 : reg n51 a1 = BitVec.ofNat 32 tl43.len := by
    rw [u51.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g50_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x604 = B + 0x21A0 + BitVec.ofNat 32 0x1024 by sv_addr, w50_1024]
  have w51_30 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m51]; exact w50_30
  have w51_34 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m51]; exact w50_34
  have w51_38 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m51]; exact w50_38
  have w51_3c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m51]; exact w50_3c
  have w51_40 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m51]; exact w50_40
  have w51_48 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m51]; exact w50_48
  have w51_4c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m51]; exact w50_4c
  have w51_50 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m51]; exact w50_50
  have w51_54 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m51]; exact w50_54
  have w51_58 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m51]; exact w50_58
  have w51_5c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m51]; exact w50_5c
  have w51_60 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m51]; exact w50_60
  have w51_64 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m51]; exact w50_64
  have w51_68 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m51]; exact w50_68
  have w51_6c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m51]; exact w50_6c
  have w51_70 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m51]; exact w50_70
  have w51_74 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m51]; exact w50_74
  have w51_78 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m51]; exact w50_78
  have w51_7c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m51]; exact w50_7c
  have w51_80 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m51]; exact w50_80
  have w51_84 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m51]; exact w50_84
  have w51_88 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m51]; exact w50_88
  have w51_8c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m51]; exact w50_8c
  have w51_90 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m51]; exact w50_90
  have w51_94 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m51]; exact w50_94
  have w51_a20 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m51]; exact w50_a20
  have w51_a24 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m51]; exact w50_a24
  have w51_a28 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m51]; exact w50_a28
  have w51_a2c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m51]; exact w50_a2c
  have w51_a30 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m51]; exact w50_a30
  have w51_a34 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m51]; exact w50_a34
  have w51_a38 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m51]; exact w50_a38
  have w51_a3c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m51]; exact w50_a3c
  have w51_a40 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m51]; exact w50_a40
  have w51_a44 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m51]; exact w50_a44
  have w51_1020 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m51]; exact w50_1020
  have w51_1024 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m51]; exact w50_1024
  have w51_1028 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m51]; exact w50_1028
  have w51_102c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m51]; exact w50_102c
  have w51_1480 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m51]; exact w50_1480
  have w51_1484 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m51]; exact w50_1484
  have w51_1488 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m51]; exact w50_1488
  have w51_148c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m51]; exact w50_148c
  have b51_1030 : n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m51]; exact b50_1030
  clear b50_1030 w50_148c w50_1488 w50_1484 w50_1480 w50_102c w50_1028 w50_1024 w50_1020 w50_a44 w50_a40 w50_a3c w50_a38 w50_a34 w50_a30 w50_a2c w50_a28 w50_a24 w50_a20 w50_94 w50_90 w50_8c w50_88 w50_84 w50_80 w50_7c w50_78 w50_74 w50_70 w50_6c w50_68 w50_64 w50_60 w50_5c w50_58 w50_54 w50_50 w50_4c w50_48 w50_40 w50_3c w50_38 w50_34 w50_30 g50_27 g50_26 g50_25 g50_23 g50_22 g50_21 g50_19 g50_18 g50_12 g50_11 g50_10 g50_9 g50_8 g50_4 g50_3 g50_2 V50 E50 fR50 t50 fr50 m50 s50 u50 d50
  -- 0x91A
  obtain ⟨n52, c52, u52⟩ := s51.block svDp191a E51.self svDp191a_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m52 : n52.mem = n51.mem := u52.mem
  have s52 : St n52.mem SV n52 0x928 (reg n52) := ⟨u52.pc, rfl, fun _ => rfl⟩
  have rb52 : ∀ q, reg n52 q = (runBlock svDp191a (n51.mem, reg n51)).2 q := fun q => by rw [u52.regs]
  have fr52 : ∀ x, SvR B x → n52.mem x = n51.mem x := fun x _ => by rw [m52]
  have t52 : Steps n0 n52 := t51.trans c52
  have fR52 : ∀ x, SvR B x → n52.mem x = n0.mem x := fun x hx => (fr52 x hx).trans (fR51 x hx)
  have E52 : SvCode n52.mem := E51.fr F fr52
  have V52 : SvSaves B n52.mem v := V51.same m52
  have g52_2 : reg n52 sp = B + 0x21A0 := by
    rw [rb52, runBlock_reg _ _ _ sp s51.zero (by decide), g51_2]
  have g52_3 : reg n52 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb52, runBlock_reg _ _ _ (3 : Fin 32) s51.zero (by decide), g51_3]
  have g52_4 : reg n52 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb52, runBlock_reg _ _ _ (4 : Fin 32) s51.zero (by decide), g51_4]
  have g52_8 : reg n52 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb52, runBlock_reg _ _ _ (8 : Fin 32) s51.zero (by decide), g51_8]
  have g52_9 : reg n52 (9 : Fin 32) = x9 := by
    rw [rb52, runBlock_reg _ _ _ (9 : Fin 32) s51.zero (by decide), g51_9]
  have g52_10 : reg n52 a0 = (vp) + BitVec.ofNat 32 tl43.header := by
    rw [rb52, runBlock_reg _ _ _ a0 s51.zero (by decide), g51_10]
  have g52_11 : reg n52 a1 = BitVec.ofNat 32 tl43.len := by
    rw [rb52, runBlock_reg _ _ _ a1 s51.zero (by decide), g51_11]
  have g52_18 : reg n52 (18 : Fin 32) = out := by
    rw [rb52, runBlock_reg _ _ _ (18 : Fin 32) s51.zero (by decide), g51_18]
  have g52_19 : reg n52 (19 : Fin 32) = bp := by
    rw [rb52, runBlock_reg _ _ _ (19 : Fin 32) s51.zero (by decide), g51_19]
  have g52_21 : reg n52 (21 : Fin 32) = x21 := by
    rw [rb52, runBlock_reg _ _ _ (21 : Fin 32) s51.zero (by decide), g51_21]
  have g52_23 : reg n52 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by
    rw [rb52, runBlock_reg _ _ _ (23 : Fin 32) s51.zero (by decide), g51_23]
  have g52_25 : reg n52 (25 : Fin 32) = x25 := by
    rw [rb52, runBlock_reg _ _ _ (25 : Fin 32) s51.zero (by decide), g51_25]
  have g52_26 : reg n52 (26 : Fin 32) = x26 := by
    rw [rb52, runBlock_reg _ _ _ (26 : Fin 32) s51.zero (by decide), g51_26]
  have g52_27 : reg n52 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb52, runBlock_reg _ _ _ (27 : Fin 32) s51.zero (by decide), g51_27]
  have g52_12 : reg n52 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA28 := by
    rw [rb52]; simp +decide only [runBlock, BInstr.run, svDp191a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g51_2, g51_3, g51_4, g51_8, g51_9, g51_10, g51_11, g51_12, g51_18, g51_19, g51_21, g51_22, g51_23, g51_25, g51_26, g51_27, s51.zero])
    all_goals (try simp only [BitVec.reduceToNat, Nat.reduceMod, BitVec.reduceHShiftLeft])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g52_22 : reg n52 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA28 := by
    rw [rb52]; simp +decide only [runBlock, BInstr.run, svDp191a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g51_2, g51_3, g51_4, g51_8, g51_9, g51_10, g51_11, g51_12, g51_18, g51_19, g51_21, g51_22, g51_23, g51_25, g51_26, g51_27, s51.zero])
    all_goals (try simp only [BitVec.reduceToNat, Nat.reduceMod, BitVec.reduceHShiftLeft])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w52_30 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m52]; exact w51_30
  have w52_34 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m52]; exact w51_34
  have w52_38 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m52]; exact w51_38
  have w52_3c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m52]; exact w51_3c
  have w52_40 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m52]; exact w51_40
  have w52_48 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m52]; exact w51_48
  have w52_4c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m52]; exact w51_4c
  have w52_50 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m52]; exact w51_50
  have w52_54 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m52]; exact w51_54
  have w52_58 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m52]; exact w51_58
  have w52_5c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m52]; exact w51_5c
  have w52_60 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m52]; exact w51_60
  have w52_64 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m52]; exact w51_64
  have w52_68 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m52]; exact w51_68
  have w52_6c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m52]; exact w51_6c
  have w52_70 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m52]; exact w51_70
  have w52_74 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m52]; exact w51_74
  have w52_78 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m52]; exact w51_78
  have w52_7c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m52]; exact w51_7c
  have w52_80 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m52]; exact w51_80
  have w52_84 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m52]; exact w51_84
  have w52_88 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m52]; exact w51_88
  have w52_8c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m52]; exact w51_8c
  have w52_90 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m52]; exact w51_90
  have w52_94 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m52]; exact w51_94
  have w52_a20 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m52]; exact w51_a20
  have w52_a24 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m52]; exact w51_a24
  have w52_a28 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2 := by rw [m52]; exact w51_a28
  have w52_a2c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := by rw [m52]; exact w51_a2c
  have w52_a30 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m52]; exact w51_a30
  have w52_a34 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m52]; exact w51_a34
  have w52_a38 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m52]; exact w51_a38
  have w52_a3c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m52]; exact w51_a3c
  have w52_a40 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m52]; exact w51_a40
  have w52_a44 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m52]; exact w51_a44
  have w52_1020 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m52]; exact w51_1020
  have w52_1024 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m52]; exact w51_1024
  have w52_1028 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m52]; exact w51_1028
  have w52_102c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m52]; exact w51_102c
  have w52_1480 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m52]; exact w51_1480
  have w52_1484 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m52]; exact w51_1484
  have w52_1488 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m52]; exact w51_1488
  have w52_148c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m52]; exact w51_148c
  have b52_1030 : n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m52]; exact b51_1030
  clear b51_1030 w51_148c w51_1488 w51_1484 w51_1480 w51_102c w51_1028 w51_1024 w51_1020 w51_a44 w51_a40 w51_a3c w51_a38 w51_a34 w51_a30 w51_a2c w51_a28 w51_a24 w51_a20 w51_94 w51_90 w51_8c w51_88 w51_84 w51_80 w51_7c w51_78 w51_74 w51_70 w51_6c w51_68 w51_64 w51_60 w51_5c w51_58 w51_54 w51_50 w51_4c w51_48 w51_40 w51_3c w51_38 w51_34 w51_30 g51_11 g51_27 g51_26 g51_25 g51_23 g51_22 g51_21 g51_19 g51_18 g51_12 g51_10 g51_9 g51_8 g51_4 g51_3 g51_2 V51 E51 fR51 t51 fr51 m51 s51 u51 d51
  -- 0x928: sw
  obtain ⟨n53, d53, s53, fr53, K53, W53, rg53⟩ := sv_sw F E52 s52 sv_at_928 (off' := 0x92A) (c := 0xA28)
    (by decide) (by rw [g52_12]; sv_addr) (by decide) (by decide)
  have t53 : Steps n0 n53 := t52.trans d53
  have fR53 : ∀ x, SvR B x → n53.mem x = n0.mem x := fun x hx => (fr53 x hx).trans (fR52 x hx)
  have E53 : SvCode n53.mem := E52.fr F fr53
  have V53 : SvSaves B n53.mem v := V52.keep K53 (by decide)
  have g53_2 : reg n53 sp = B + 0x21A0 := by rw [rg53 sp, g52_2]
  have g53_3 : reg n53 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg53 (3 : Fin 32), g52_3]
  have g53_4 : reg n53 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg53 (4 : Fin 32), g52_4]
  have g53_8 : reg n53 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg53 (8 : Fin 32), g52_8]
  have g53_9 : reg n53 (9 : Fin 32) = x9 := by rw [rg53 (9 : Fin 32), g52_9]
  have g53_10 : reg n53 a0 = (vp) + BitVec.ofNat 32 tl43.header := by rw [rg53 a0, g52_10]
  have g53_11 : reg n53 a1 = BitVec.ofNat 32 tl43.len := by rw [rg53 a1, g52_11]
  have g53_12 : reg n53 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA28 := by rw [rg53 a2, g52_12]
  have g53_18 : reg n53 (18 : Fin 32) = out := by rw [rg53 (18 : Fin 32), g52_18]
  have g53_19 : reg n53 (19 : Fin 32) = bp := by rw [rg53 (19 : Fin 32), g52_19]
  have g53_21 : reg n53 (21 : Fin 32) = x21 := by rw [rg53 (21 : Fin 32), g52_21]
  have g53_22 : reg n53 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA28 := by rw [rg53 (22 : Fin 32), g52_22]
  have g53_23 : reg n53 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [rg53 (23 : Fin 32), g52_23]
  have g53_25 : reg n53 (25 : Fin 32) = x25 := by rw [rg53 (25 : Fin 32), g52_25]
  have g53_26 : reg n53 (26 : Fin 32) = x26 := by rw [rg53 (26 : Fin 32), g52_26]
  have g53_27 : reg n53 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg53 (27 : Fin 32), g52_27]
  have w53_30 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K53.w32 (by decide) (by decide)).trans w52_30
  have w53_34 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K53.w32 (by decide) (by decide)).trans w52_34
  have w53_38 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K53.w32 (by decide) (by decide)).trans w52_38
  have w53_3c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K53.w32 (by decide) (by decide)).trans w52_3c
  have w53_40 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K53.w32 (by decide) (by decide)).trans w52_40
  have w53_48 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K53.w32 (by decide) (by decide)).trans w52_48
  have w53_4c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K53.w32 (by decide) (by decide)).trans w52_4c
  have w53_50 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K53.w32 (by decide) (by decide)).trans w52_50
  have w53_54 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K53.w32 (by decide) (by decide)).trans w52_54
  have w53_58 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K53.w32 (by decide) (by decide)).trans w52_58
  have w53_5c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K53.w32 (by decide) (by decide)).trans w52_5c
  have w53_60 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K53.w32 (by decide) (by decide)).trans w52_60
  have w53_64 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K53.w32 (by decide) (by decide)).trans w52_64
  have w53_68 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K53.w32 (by decide) (by decide)).trans w52_68
  have w53_6c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K53.w32 (by decide) (by decide)).trans w52_6c
  have w53_70 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K53.w32 (by decide) (by decide)).trans w52_70
  have w53_74 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K53.w32 (by decide) (by decide)).trans w52_74
  have w53_78 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K53.w32 (by decide) (by decide)).trans w52_78
  have w53_7c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K53.w32 (by decide) (by decide)).trans w52_7c
  have w53_80 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K53.w32 (by decide) (by decide)).trans w52_80
  have w53_84 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K53.w32 (by decide) (by decide)).trans w52_84
  have w53_88 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K53.w32 (by decide) (by decide)).trans w52_88
  have w53_8c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K53.w32 (by decide) (by decide)).trans w52_8c
  have w53_90 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K53.w32 (by decide) (by decide)).trans w52_90
  have w53_94 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K53.w32 (by decide) (by decide)).trans w52_94
  have w53_a20 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K53.w32 (by decide) (by decide)).trans w52_a20
  have w53_a24 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K53.w32 (by decide) (by decide)).trans w52_a24
  have w53_a2c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3 := (K53.w32 (by decide) (by decide)).trans w52_a2c
  have w53_a30 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K53.w32 (by decide) (by decide)).trans w52_a30
  have w53_a34 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K53.w32 (by decide) (by decide)).trans w52_a34
  have w53_a38 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K53.w32 (by decide) (by decide)).trans w52_a38
  have w53_a3c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K53.w32 (by decide) (by decide)).trans w52_a3c
  have w53_a40 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K53.w32 (by decide) (by decide)).trans w52_a40
  have w53_a44 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K53.w32 (by decide) (by decide)).trans w52_a44
  have w53_1020 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := (K53.w32 (by decide) (by decide)).trans w52_1020
  have w53_1024 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := (K53.w32 (by decide) (by decide)).trans w52_1024
  have w53_1028 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := (K53.w32 (by decide) (by decide)).trans w52_1028
  have w53_102c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := (K53.w32 (by decide) (by decide)).trans w52_102c
  have w53_1480 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K53.w32 (by decide) (by decide)).trans w52_1480
  have w53_1484 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K53.w32 (by decide) (by decide)).trans w52_1484
  have w53_1488 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := (K53.w32 (by decide) (by decide)).trans w52_1488
  have w53_148c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := (K53.w32 (by decide) (by decide)).trans w52_148c
  have b53_1030 : n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := (K53.b8 (by decide) (by decide)).trans b52_1030
  have w53_a28 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (vp) + BitVec.ofNat 32 tl43.header := by rw [W53, g52_10]
  clear b52_1030 w52_148c w52_1488 w52_1484 w52_1480 w52_102c w52_1028 w52_1024 w52_1020 w52_a44 w52_a40 w52_a3c w52_a38 w52_a34 w52_a30 w52_a2c w52_a28 w52_a24 w52_a20 w52_94 w52_90 w52_8c w52_88 w52_84 w52_80 w52_7c w52_78 w52_74 w52_70 w52_6c w52_68 w52_64 w52_60 w52_5c w52_58 w52_54 w52_50 w52_4c w52_48 w52_40 w52_3c w52_38 w52_34 w52_30 g52_22 g52_12 g52_27 g52_26 g52_25 g52_23 g52_21 g52_19 g52_18 g52_11 g52_10 g52_9 g52_8 g52_4 g52_3 g52_2 V52 E52 fR52 t52 fr52 rb52 s52 m52 u52 c52
  -- 0x92A: sw
  obtain ⟨n54, d54, s54, fr54, K54, W54, rg54⟩ := sv_sw F E53 s53 sv_at_92a (off' := 0x92C) (c := 0xA2C)
    (by decide) (by rw [g53_12]; sv_addr) (by decide) (by decide)
  have t54 : Steps n0 n54 := t53.trans d54
  have fR54 : ∀ x, SvR B x → n54.mem x = n0.mem x := fun x hx => (fr54 x hx).trans (fR53 x hx)
  have E54 : SvCode n54.mem := E53.fr F fr54
  have V54 : SvSaves B n54.mem v := V53.keep K54 (by decide)
  have g54_2 : reg n54 sp = B + 0x21A0 := by rw [rg54 sp, g53_2]
  have g54_3 : reg n54 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg54 (3 : Fin 32), g53_3]
  have g54_4 : reg n54 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg54 (4 : Fin 32), g53_4]
  have g54_8 : reg n54 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg54 (8 : Fin 32), g53_8]
  have g54_9 : reg n54 (9 : Fin 32) = x9 := by rw [rg54 (9 : Fin 32), g53_9]
  have g54_10 : reg n54 a0 = (vp) + BitVec.ofNat 32 tl43.header := by rw [rg54 a0, g53_10]
  have g54_11 : reg n54 a1 = BitVec.ofNat 32 tl43.len := by rw [rg54 a1, g53_11]
  have g54_12 : reg n54 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA28 := by rw [rg54 a2, g53_12]
  have g54_18 : reg n54 (18 : Fin 32) = out := by rw [rg54 (18 : Fin 32), g53_18]
  have g54_19 : reg n54 (19 : Fin 32) = bp := by rw [rg54 (19 : Fin 32), g53_19]
  have g54_21 : reg n54 (21 : Fin 32) = x21 := by rw [rg54 (21 : Fin 32), g53_21]
  have g54_22 : reg n54 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA28 := by rw [rg54 (22 : Fin 32), g53_22]
  have g54_23 : reg n54 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [rg54 (23 : Fin 32), g53_23]
  have g54_25 : reg n54 (25 : Fin 32) = x25 := by rw [rg54 (25 : Fin 32), g53_25]
  have g54_26 : reg n54 (26 : Fin 32) = x26 := by rw [rg54 (26 : Fin 32), g53_26]
  have g54_27 : reg n54 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg54 (27 : Fin 32), g53_27]
  have w54_30 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K54.w32 (by decide) (by decide)).trans w53_30
  have w54_34 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K54.w32 (by decide) (by decide)).trans w53_34
  have w54_38 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K54.w32 (by decide) (by decide)).trans w53_38
  have w54_3c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K54.w32 (by decide) (by decide)).trans w53_3c
  have w54_40 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := (K54.w32 (by decide) (by decide)).trans w53_40
  have w54_48 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K54.w32 (by decide) (by decide)).trans w53_48
  have w54_4c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K54.w32 (by decide) (by decide)).trans w53_4c
  have w54_50 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K54.w32 (by decide) (by decide)).trans w53_50
  have w54_54 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K54.w32 (by decide) (by decide)).trans w53_54
  have w54_58 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K54.w32 (by decide) (by decide)).trans w53_58
  have w54_5c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K54.w32 (by decide) (by decide)).trans w53_5c
  have w54_60 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K54.w32 (by decide) (by decide)).trans w53_60
  have w54_64 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K54.w32 (by decide) (by decide)).trans w53_64
  have w54_68 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K54.w32 (by decide) (by decide)).trans w53_68
  have w54_6c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K54.w32 (by decide) (by decide)).trans w53_6c
  have w54_70 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K54.w32 (by decide) (by decide)).trans w53_70
  have w54_74 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K54.w32 (by decide) (by decide)).trans w53_74
  have w54_78 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K54.w32 (by decide) (by decide)).trans w53_78
  have w54_7c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K54.w32 (by decide) (by decide)).trans w53_7c
  have w54_80 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K54.w32 (by decide) (by decide)).trans w53_80
  have w54_84 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K54.w32 (by decide) (by decide)).trans w53_84
  have w54_88 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K54.w32 (by decide) (by decide)).trans w53_88
  have w54_8c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K54.w32 (by decide) (by decide)).trans w53_8c
  have w54_90 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K54.w32 (by decide) (by decide)).trans w53_90
  have w54_94 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K54.w32 (by decide) (by decide)).trans w53_94
  have w54_a20 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K54.w32 (by decide) (by decide)).trans w53_a20
  have w54_a24 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K54.w32 (by decide) (by decide)).trans w53_a24
  have w54_a28 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (vp) + BitVec.ofNat 32 tl43.header := (K54.w32 (by decide) (by decide)).trans w53_a28
  have w54_a30 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K54.w32 (by decide) (by decide)).trans w53_a30
  have w54_a34 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K54.w32 (by decide) (by decide)).trans w53_a34
  have w54_a38 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K54.w32 (by decide) (by decide)).trans w53_a38
  have w54_a3c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K54.w32 (by decide) (by decide)).trans w53_a3c
  have w54_a40 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K54.w32 (by decide) (by decide)).trans w53_a40
  have w54_a44 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K54.w32 (by decide) (by decide)).trans w53_a44
  have w54_1020 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := (K54.w32 (by decide) (by decide)).trans w53_1020
  have w54_1024 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := (K54.w32 (by decide) (by decide)).trans w53_1024
  have w54_1028 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := (K54.w32 (by decide) (by decide)).trans w53_1028
  have w54_102c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := (K54.w32 (by decide) (by decide)).trans w53_102c
  have w54_1480 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K54.w32 (by decide) (by decide)).trans w53_1480
  have w54_1484 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K54.w32 (by decide) (by decide)).trans w53_1484
  have w54_1488 : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := (K54.w32 (by decide) (by decide)).trans w53_1488
  have w54_148c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := (K54.w32 (by decide) (by decide)).trans w53_148c
  have b54_1030 : n54.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := (K54.b8 (by decide) (by decide)).trans b53_1030
  have w54_a2c : memLoad32 n54.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl43.len := by rw [W54, g53_11]
  clear w53_a28 b53_1030 w53_148c w53_1488 w53_1484 w53_1480 w53_102c w53_1028 w53_1024 w53_1020 w53_a44 w53_a40 w53_a3c w53_a38 w53_a34 w53_a30 w53_a2c w53_a24 w53_a20 w53_94 w53_90 w53_8c w53_88 w53_84 w53_80 w53_7c w53_78 w53_74 w53_70 w53_6c w53_68 w53_64 w53_60 w53_5c w53_58 w53_54 w53_50 w53_4c w53_48 w53_40 w53_3c w53_38 w53_34 w53_30 g53_27 g53_26 g53_25 g53_23 g53_22 g53_21 g53_19 g53_18 g53_12 g53_11 g53_10 g53_9 g53_8 g53_4 g53_3 g53_2 V53 E53 fR53 t53 rg53 W53 K53 fr53 s53 d53
  -- 0x92C: j
  obtain ⟨n55, d55, u55⟩ := s54.jump E54.self sv_at_92c (off' := 0x95C) (by decide)
    (by rw [s54.pc]; decide)
  have s55 : St n55.mem SV n55 0x95C (reg n55) := ⟨u55.pc, rfl, fun _ => rfl⟩
  have m55 : n55.mem = n54.mem := u55.mem
  have fr55 : ∀ x, SvR B x → n55.mem x = n54.mem x := fun x _ => by rw [m55]
  have t55 : Steps n0 n55 := t54.trans (.single d55)
  have fR55 : ∀ x, SvR B x → n55.mem x = n0.mem x := fun x hx => (fr55 x hx).trans (fR54 x hx)
  have E55 : SvCode n55.mem := E54.fr F fr55
  have V55 : SvSaves B n55.mem v := V54.same m55
  have g55_2 : reg n55 sp = B + 0x21A0 := by rw [u55.regs, g54_2]
  have g55_3 : reg n55 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u55.regs, g54_3]
  have g55_4 : reg n55 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u55.regs, g54_4]
  have g55_8 : reg n55 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u55.regs, g54_8]
  have g55_9 : reg n55 (9 : Fin 32) = x9 := by rw [u55.regs, g54_9]
  have g55_10 : reg n55 a0 = (vp) + BitVec.ofNat 32 tl43.header := by rw [u55.regs, g54_10]
  have g55_11 : reg n55 a1 = BitVec.ofNat 32 tl43.len := by rw [u55.regs, g54_11]
  have g55_12 : reg n55 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA28 := by rw [u55.regs, g54_12]
  have g55_18 : reg n55 (18 : Fin 32) = out := by rw [u55.regs, g54_18]
  have g55_19 : reg n55 (19 : Fin 32) = bp := by rw [u55.regs, g54_19]
  have g55_21 : reg n55 (21 : Fin 32) = x21 := by rw [u55.regs, g54_21]
  have g55_22 : reg n55 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA28 := by rw [u55.regs, g54_22]
  have g55_23 : reg n55 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u55.regs, g54_23]
  have g55_25 : reg n55 (25 : Fin 32) = x25 := by rw [u55.regs, g54_25]
  have g55_26 : reg n55 (26 : Fin 32) = x26 := by rw [u55.regs, g54_26]
  have g55_27 : reg n55 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u55.regs, g54_27]
  have w55_30 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m55]; exact w54_30
  have w55_34 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m55]; exact w54_34
  have w55_38 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m55]; exact w54_38
  have w55_3c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m55]; exact w54_3c
  have w55_40 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m55]; exact w54_40
  have w55_48 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m55]; exact w54_48
  have w55_4c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m55]; exact w54_4c
  have w55_50 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m55]; exact w54_50
  have w55_54 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m55]; exact w54_54
  have w55_58 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m55]; exact w54_58
  have w55_5c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m55]; exact w54_5c
  have w55_60 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m55]; exact w54_60
  have w55_64 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m55]; exact w54_64
  have w55_68 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m55]; exact w54_68
  have w55_6c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m55]; exact w54_6c
  have w55_70 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m55]; exact w54_70
  have w55_74 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m55]; exact w54_74
  have w55_78 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m55]; exact w54_78
  have w55_7c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m55]; exact w54_7c
  have w55_80 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m55]; exact w54_80
  have w55_84 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m55]; exact w54_84
  have w55_88 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m55]; exact w54_88
  have w55_8c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m55]; exact w54_8c
  have w55_90 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m55]; exact w54_90
  have w55_94 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m55]; exact w54_94
  have w55_a20 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m55]; exact w54_a20
  have w55_a24 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m55]; exact w54_a24
  have w55_a28 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m55]; exact w54_a28
  have w55_a2c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl43.len := by rw [m55]; exact w54_a2c
  have w55_a30 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m55]; exact w54_a30
  have w55_a34 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m55]; exact w54_a34
  have w55_a38 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m55]; exact w54_a38
  have w55_a3c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m55]; exact w54_a3c
  have w55_a40 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m55]; exact w54_a40
  have w55_a44 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m55]; exact w54_a44
  have w55_1020 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m55]; exact w54_1020
  have w55_1024 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m55]; exact w54_1024
  have w55_1028 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m55]; exact w54_1028
  have w55_102c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m55]; exact w54_102c
  have w55_1480 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m55]; exact w54_1480
  have w55_1484 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m55]; exact w54_1484
  have w55_1488 : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m55]; exact w54_1488
  have w55_148c : memLoad32 n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m55]; exact w54_148c
  have b55_1030 : n55.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m55]; exact b54_1030
  clear w54_a2c b54_1030 w54_148c w54_1488 w54_1484 w54_1480 w54_102c w54_1028 w54_1024 w54_1020 w54_a44 w54_a40 w54_a3c w54_a38 w54_a34 w54_a30 w54_a28 w54_a24 w54_a20 w54_94 w54_90 w54_8c w54_88 w54_84 w54_80 w54_7c w54_78 w54_74 w54_70 w54_6c w54_68 w54_64 w54_60 w54_5c w54_58 w54_54 w54_50 w54_4c w54_48 w54_40 w54_3c w54_38 w54_34 w54_30 g54_27 g54_26 g54_25 g54_23 g54_22 g54_21 g54_19 g54_18 g54_12 g54_11 g54_10 g54_9 g54_8 g54_4 g54_3 g54_2 V54 E54 fR54 t54 rg54 W54 K54 fr54 s54 d54
  -- 0x95C: lw
  obtain ⟨n56, d56, u56⟩ := s55.lw E55.self sv_at_95c (off' := 0x95E) (by decide)
    (by rw [g55_2, show B + 0x21A0 + 0x94 = B + 0x21A0 + BitVec.ofNat 32 0x94 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s56 : St n56.mem SV n56 0x95E (reg n56) := ⟨u56.pc, rfl, fun _ => rfl⟩
  have m56 : n56.mem = n55.mem := u56.mem
  have fr56 : ∀ x, SvR B x → n56.mem x = n55.mem x := fun x _ => by rw [m56]
  have t56 : Steps n0 n56 := t55.trans (.single d56)
  have fR56 : ∀ x, SvR B x → n56.mem x = n0.mem x := fun x hx => (fr56 x hx).trans (fR55 x hx)
  have E56 : SvCode n56.mem := E55.fr F fr56
  have V56 : SvSaves B n56.mem v := V55.same m56
  have g56_2 : reg n56 sp = B + 0x21A0 := by rw [u56.regs, upd_ne (by decide) (by decide), g55_2]
  have g56_3 : reg n56 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u56.regs, upd_ne (by decide) (by decide), g55_3]
  have g56_4 : reg n56 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u56.regs, upd_ne (by decide) (by decide), g55_4]
  have g56_8 : reg n56 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u56.regs, upd_ne (by decide) (by decide), g55_8]
  have g56_9 : reg n56 (9 : Fin 32) = x9 := by rw [u56.regs, upd_ne (by decide) (by decide), g55_9]
  have g56_11 : reg n56 a1 = BitVec.ofNat 32 tl43.len := by rw [u56.regs, upd_ne (by decide) (by decide), g55_11]
  have g56_12 : reg n56 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA28 := by rw [u56.regs, upd_ne (by decide) (by decide), g55_12]
  have g56_18 : reg n56 (18 : Fin 32) = out := by rw [u56.regs, upd_ne (by decide) (by decide), g55_18]
  have g56_19 : reg n56 (19 : Fin 32) = bp := by rw [u56.regs, upd_ne (by decide) (by decide), g55_19]
  have g56_21 : reg n56 (21 : Fin 32) = x21 := by rw [u56.regs, upd_ne (by decide) (by decide), g55_21]
  have g56_22 : reg n56 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA28 := by rw [u56.regs, upd_ne (by decide) (by decide), g55_22]
  have g56_23 : reg n56 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u56.regs, upd_ne (by decide) (by decide), g55_23]
  have g56_25 : reg n56 (25 : Fin 32) = x25 := by rw [u56.regs, upd_ne (by decide) (by decide), g55_25]
  have g56_26 : reg n56 (26 : Fin 32) = x26 := by rw [u56.regs, upd_ne (by decide) (by decide), g55_26]
  have g56_27 : reg n56 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u56.regs, upd_ne (by decide) (by decide), g55_27]
  have g56_10 : reg n56 a0 = rest := by
    rw [u56.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g55_2, show B + 0x21A0 + 0x94 = B + 0x21A0 + BitVec.ofNat 32 0x94 by sv_addr, w55_94]
  have w56_30 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m56]; exact w55_30
  have w56_34 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m56]; exact w55_34
  have w56_38 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m56]; exact w55_38
  have w56_3c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m56]; exact w55_3c
  have w56_40 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem := by rw [m56]; exact w55_40
  have w56_48 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m56]; exact w55_48
  have w56_4c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m56]; exact w55_4c
  have w56_50 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m56]; exact w55_50
  have w56_54 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m56]; exact w55_54
  have w56_58 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m56]; exact w55_58
  have w56_5c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m56]; exact w55_5c
  have w56_60 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m56]; exact w55_60
  have w56_64 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m56]; exact w55_64
  have w56_68 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m56]; exact w55_68
  have w56_6c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m56]; exact w55_6c
  have w56_70 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m56]; exact w55_70
  have w56_74 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m56]; exact w55_74
  have w56_78 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m56]; exact w55_78
  have w56_7c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m56]; exact w55_7c
  have w56_80 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m56]; exact w55_80
  have w56_84 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m56]; exact w55_84
  have w56_88 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m56]; exact w55_88
  have w56_8c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m56]; exact w55_8c
  have w56_90 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m56]; exact w55_90
  have w56_94 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m56]; exact w55_94
  have w56_a20 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m56]; exact w55_a20
  have w56_a24 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m56]; exact w55_a24
  have w56_a28 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m56]; exact w55_a28
  have w56_a2c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl43.len := by rw [m56]; exact w55_a2c
  have w56_a30 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m56]; exact w55_a30
  have w56_a34 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m56]; exact w55_a34
  have w56_a38 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m56]; exact w55_a38
  have w56_a3c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m56]; exact w55_a3c
  have w56_a40 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m56]; exact w55_a40
  have w56_a44 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m56]; exact w55_a44
  have w56_1020 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m56]; exact w55_1020
  have w56_1024 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m56]; exact w55_1024
  have w56_1028 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m56]; exact w55_1028
  have w56_102c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m56]; exact w55_102c
  have w56_1480 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m56]; exact w55_1480
  have w56_1484 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m56]; exact w55_1484
  have w56_1488 : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m56]; exact w55_1488
  have w56_148c : memLoad32 n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m56]; exact w55_148c
  have b56_1030 : n56.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m56]; exact b55_1030
  clear b55_1030 w55_148c w55_1488 w55_1484 w55_1480 w55_102c w55_1028 w55_1024 w55_1020 w55_a44 w55_a40 w55_a3c w55_a38 w55_a34 w55_a30 w55_a2c w55_a28 w55_a24 w55_a20 w55_94 w55_90 w55_8c w55_88 w55_84 w55_80 w55_7c w55_78 w55_74 w55_70 w55_6c w55_68 w55_64 w55_60 w55_5c w55_58 w55_54 w55_50 w55_4c w55_48 w55_40 w55_3c w55_38 w55_34 w55_30 g55_27 g55_26 g55_25 g55_23 g55_22 g55_21 g55_19 g55_18 g55_12 g55_11 g55_10 g55_9 g55_8 g55_4 g55_3 g55_2 V55 E55 fR55 t55 fr55 m55 s55 u55 d55
  -- 0x95E: sw
  obtain ⟨n57, d57, s57, fr57, K57, W57, rg57⟩ := sv_sw F E56 s56 sv_at_95e (off' := 0x960) (c := 0x40)
    (by decide) (by rw [g56_2]; sv_addr) (by decide) (by decide)
  have t57 : Steps n0 n57 := t56.trans d57
  have fR57 : ∀ x, SvR B x → n57.mem x = n0.mem x := fun x hx => (fr57 x hx).trans (fR56 x hx)
  have E57 : SvCode n57.mem := E56.fr F fr57
  have V57 : SvSaves B n57.mem v := V56.keep K57 (by decide)
  have g57_2 : reg n57 sp = B + 0x21A0 := by rw [rg57 sp, g56_2]
  have g57_3 : reg n57 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg57 (3 : Fin 32), g56_3]
  have g57_4 : reg n57 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg57 (4 : Fin 32), g56_4]
  have g57_8 : reg n57 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [rg57 (8 : Fin 32), g56_8]
  have g57_9 : reg n57 (9 : Fin 32) = x9 := by rw [rg57 (9 : Fin 32), g56_9]
  have g57_10 : reg n57 a0 = rest := by rw [rg57 a0, g56_10]
  have g57_11 : reg n57 a1 = BitVec.ofNat 32 tl43.len := by rw [rg57 a1, g56_11]
  have g57_12 : reg n57 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA28 := by rw [rg57 a2, g56_12]
  have g57_18 : reg n57 (18 : Fin 32) = out := by rw [rg57 (18 : Fin 32), g56_18]
  have g57_19 : reg n57 (19 : Fin 32) = bp := by rw [rg57 (19 : Fin 32), g56_19]
  have g57_21 : reg n57 (21 : Fin 32) = x21 := by rw [rg57 (21 : Fin 32), g56_21]
  have g57_22 : reg n57 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA28 := by rw [rg57 (22 : Fin 32), g56_22]
  have g57_23 : reg n57 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [rg57 (23 : Fin 32), g56_23]
  have g57_25 : reg n57 (25 : Fin 32) = x25 := by rw [rg57 (25 : Fin 32), g56_25]
  have g57_26 : reg n57 (26 : Fin 32) = x26 := by rw [rg57 (26 : Fin 32), g56_26]
  have g57_27 : reg n57 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg57 (27 : Fin 32), g56_27]
  have w57_30 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := (K57.w32 (by decide) (by decide)).trans w56_30
  have w57_34 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := (K57.w32 (by decide) (by decide)).trans w56_34
  have w57_38 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := (K57.w32 (by decide) (by decide)).trans w56_38
  have w57_3c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := (K57.w32 (by decide) (by decide)).trans w56_3c
  have w57_48 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := (K57.w32 (by decide) (by decide)).trans w56_48
  have w57_4c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K57.w32 (by decide) (by decide)).trans w56_4c
  have w57_50 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K57.w32 (by decide) (by decide)).trans w56_50
  have w57_54 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := (K57.w32 (by decide) (by decide)).trans w56_54
  have w57_58 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := (K57.w32 (by decide) (by decide)).trans w56_58
  have w57_5c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := (K57.w32 (by decide) (by decide)).trans w56_5c
  have w57_60 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := (K57.w32 (by decide) (by decide)).trans w56_60
  have w57_64 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := (K57.w32 (by decide) (by decide)).trans w56_64
  have w57_68 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := (K57.w32 (by decide) (by decide)).trans w56_68
  have w57_6c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := (K57.w32 (by decide) (by decide)).trans w56_6c
  have w57_70 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := (K57.w32 (by decide) (by decide)).trans w56_70
  have w57_74 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := (K57.w32 (by decide) (by decide)).trans w56_74
  have w57_78 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := (K57.w32 (by decide) (by decide)).trans w56_78
  have w57_7c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := (K57.w32 (by decide) (by decide)).trans w56_7c
  have w57_80 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := (K57.w32 (by decide) (by decide)).trans w56_80
  have w57_84 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := (K57.w32 (by decide) (by decide)).trans w56_84
  have w57_88 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := (K57.w32 (by decide) (by decide)).trans w56_88
  have w57_8c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := (K57.w32 (by decide) (by decide)).trans w56_8c
  have w57_90 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := (K57.w32 (by decide) (by decide)).trans w56_90
  have w57_94 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := (K57.w32 (by decide) (by decide)).trans w56_94
  have w57_a20 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := (K57.w32 (by decide) (by decide)).trans w56_a20
  have w57_a24 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := (K57.w32 (by decide) (by decide)).trans w56_a24
  have w57_a28 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (vp) + BitVec.ofNat 32 tl43.header := (K57.w32 (by decide) (by decide)).trans w56_a28
  have w57_a2c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl43.len := (K57.w32 (by decide) (by decide)).trans w56_a2c
  have w57_a30 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := (K57.w32 (by decide) (by decide)).trans w56_a30
  have w57_a34 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := (K57.w32 (by decide) (by decide)).trans w56_a34
  have w57_a38 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := (K57.w32 (by decide) (by decide)).trans w56_a38
  have w57_a3c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := (K57.w32 (by decide) (by decide)).trans w56_a3c
  have w57_a40 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := (K57.w32 (by decide) (by decide)).trans w56_a40
  have w57_a44 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := (K57.w32 (by decide) (by decide)).trans w56_a44
  have w57_1020 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := (K57.w32 (by decide) (by decide)).trans w56_1020
  have w57_1024 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := (K57.w32 (by decide) (by decide)).trans w56_1024
  have w57_1028 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := (K57.w32 (by decide) (by decide)).trans w56_1028
  have w57_102c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := (K57.w32 (by decide) (by decide)).trans w56_102c
  have w57_1480 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := (K57.w32 (by decide) (by decide)).trans w56_1480
  have w57_1484 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := (K57.w32 (by decide) (by decide)).trans w56_1484
  have w57_1488 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := (K57.w32 (by decide) (by decide)).trans w56_1488
  have w57_148c : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := (K57.w32 (by decide) (by decide)).trans w56_148c
  have b57_1030 : n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := (K57.b8 (by decide) (by decide)).trans b56_1030
  have w57_40 : memLoad32 n57.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rest := by rw [W57, g56_10]
  clear b56_1030 w56_148c w56_1488 w56_1484 w56_1480 w56_102c w56_1028 w56_1024 w56_1020 w56_a44 w56_a40 w56_a3c w56_a38 w56_a34 w56_a30 w56_a2c w56_a28 w56_a24 w56_a20 w56_94 w56_90 w56_8c w56_88 w56_84 w56_80 w56_7c w56_78 w56_74 w56_70 w56_6c w56_68 w56_64 w56_60 w56_5c w56_58 w56_54 w56_50 w56_4c w56_48 w56_40 w56_3c w56_38 w56_34 w56_30 g56_10 g56_27 g56_26 g56_25 g56_23 g56_22 g56_21 g56_19 g56_18 g56_12 g56_11 g56_9 g56_8 g56_4 g56_3 g56_2 V56 E56 fR56 t56 fr56 m56 s56 u56 d56
  -- 0x960: j
  obtain ⟨n58, d58, u58⟩ := s57.jump E57.self sv_at_960 (off' := 0x4EA) (by decide)
    (by rw [s57.pc]; decide)
  have s58 : St n58.mem SV n58 0x4EA (reg n58) := ⟨u58.pc, rfl, fun _ => rfl⟩
  have m58 : n58.mem = n57.mem := u58.mem
  have fr58 : ∀ x, SvR B x → n58.mem x = n57.mem x := fun x _ => by rw [m58]
  have t58 : Steps n0 n58 := t57.trans (.single d58)
  have fR58 : ∀ x, SvR B x → n58.mem x = n0.mem x := fun x hx => (fr58 x hx).trans (fR57 x hx)
  have E58 : SvCode n58.mem := E57.fr F fr58
  have V58 : SvSaves B n58.mem v := V57.same m58
  have g58_2 : reg n58 sp = B + 0x21A0 := by rw [u58.regs, g57_2]
  have g58_3 : reg n58 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u58.regs, g57_3]
  have g58_4 : reg n58 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u58.regs, g57_4]
  have g58_8 : reg n58 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by rw [u58.regs, g57_8]
  have g58_9 : reg n58 (9 : Fin 32) = x9 := by rw [u58.regs, g57_9]
  have g58_10 : reg n58 a0 = rest := by rw [u58.regs, g57_10]
  have g58_11 : reg n58 a1 = BitVec.ofNat 32 tl43.len := by rw [u58.regs, g57_11]
  have g58_12 : reg n58 a2 = B + 0x21A0 + BitVec.ofNat 32 0xA28 := by rw [u58.regs, g57_12]
  have g58_18 : reg n58 (18 : Fin 32) = out := by rw [u58.regs, g57_18]
  have g58_19 : reg n58 (19 : Fin 32) = bp := by rw [u58.regs, g57_19]
  have g58_21 : reg n58 (21 : Fin 32) = x21 := by rw [u58.regs, g57_21]
  have g58_22 : reg n58 (22 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA28 := by rw [u58.regs, g57_22]
  have g58_23 : reg n58 (23 : Fin 32) = BitVec.ofNat 32 0x3FCC48FC := by rw [u58.regs, g57_23]
  have g58_25 : reg n58 (25 : Fin 32) = x25 := by rw [u58.regs, g57_25]
  have g58_26 : reg n58 (26 : Fin 32) = x26 := by rw [u58.regs, g57_26]
  have g58_27 : reg n58 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u58.regs, g57_27]
  have w58_30 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 := by rw [m58]; exact w57_30
  have w58_34 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34 := by rw [m58]; exact w57_34
  have w58_38 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = vl := by rw [m58]; exact w57_38
  have w58_3c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = vp := by rw [m58]; exact w57_3c
  have w58_40 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rest := by rw [m58]; exact w57_40
  have w58_48 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol := by rw [m58]; exact w57_48
  have w58_4c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m58]; exact w57_4c
  have w58_50 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m58]; exact w57_50
  have w58_54 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 := by rw [m58]; exact w57_54
  have w58_58 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 := by rw [m58]; exact w57_58
  have w58_5c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c := by rw [m58]; exact w57_5c
  have w58_60 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 := by rw [m58]; exact w57_60
  have w58_64 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 := by rw [m58]; exact w57_64
  have w58_68 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 := by rw [m58]; exact w57_68
  have w58_6c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c := by rw [m58]; exact w57_6c
  have w58_70 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 := by rw [m58]; exact w57_70
  have w58_74 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 := by rw [m58]; exact w57_74
  have w58_78 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 := by rw [m58]; exact w57_78
  have w58_7c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c := by rw [m58]; exact w57_7c
  have w58_80 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 := by rw [m58]; exact w57_80
  have w58_84 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 := by rw [m58]; exact w57_84
  have w58_88 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 := by rw [m58]; exact w57_88
  have w58_8c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L := by rw [m58]; exact w57_8c
  have w58_90 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur := by rw [m58]; exact w57_90
  have w58_94 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rest := by rw [m58]; exact w57_94
  have w58_a20 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0 := by rw [m58]; exact w57_a20
  have w58_a24 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1 := by rw [m58]; exact w57_a24
  have w58_a28 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m58]; exact w57_a28
  have w58_a2c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl43.len := by rw [m58]; exact w57_a2c
  have w58_a30 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4 := by rw [m58]; exact w57_a30
  have w58_a34 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5 := by rw [m58]; exact w57_a34
  have w58_a38 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6 := by rw [m58]; exact w57_a38
  have w58_a3c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7 := by rw [m58]; exact w57_a3c
  have w58_a40 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8 := by rw [m58]; exact w57_a40
  have w58_a44 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9 := by rw [m58]; exact w57_a44
  have w58_1020 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (vp) + BitVec.ofNat 32 tl43.header := by rw [m58]; exact w57_1020
  have w58_1024 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x1024) = BitVec.ofNat 32 tl43.len := by rw [m58]; exact w57_1024
  have w58_1028 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = vp := by rw [m58]; exact w57_1028
  have w58_102c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m58]; exact w57_102c
  have w58_1480 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = vp := by rw [m58]; exact w57_1480
  have w58_1484 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x1484) = vl := by rw [m58]; exact w57_1484
  have w58_1488 : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x1488) = (vp) + BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m58]; exact w57_1488
  have w58_148c : memLoad32 n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x148C) = (vl) - BitVec.ofNat 32 (tl43.header + tl43.len) := by rw [m58]; exact w57_148c
  have b58_1030 : n58.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = BitVec.ofNat 8 tl43.tag := by rw [m58]; exact b57_1030
  clear w57_40 b57_1030 w57_148c w57_1488 w57_1484 w57_1480 w57_102c w57_1028 w57_1024 w57_1020 w57_a44 w57_a40 w57_a3c w57_a38 w57_a34 w57_a30 w57_a2c w57_a28 w57_a24 w57_a20 w57_94 w57_90 w57_8c w57_88 w57_84 w57_80 w57_7c w57_78 w57_74 w57_70 w57_6c w57_68 w57_64 w57_60 w57_5c w57_58 w57_54 w57_50 w57_4c w57_48 w57_3c w57_38 w57_34 w57_30 g57_27 g57_26 g57_25 g57_23 g57_22 g57_21 g57_19 g57_18 g57_12 g57_11 g57_10 g57_9 g57_8 g57_4 g57_3 g57_2 V57 E57 fR57 t57 rg57 W57 K57 fr57 s57 d57
  exact .inr ⟨tl43, hr43, hz_47, hz_49, n58, t58, s58, E58, V58, fR58, g58_2, g58_3, g58_4, g58_9, g58_18, g58_19, g58_21, g58_25, g58_26, g58_27, w58_30, w58_34, w58_40, w58_4c, w58_50, w58_54, w58_58, w58_5c, w58_60, w58_64, w58_68, w58_6c, w58_70, w58_74, w58_78, w58_7c, w58_80, w58_84, w58_88, w58_8c, w58_90, w58_94, w58_a20, w58_a24, w58_a28, w58_a2c, w58_a30, w58_a34, w58_a38, w58_a3c, w58_a40, w58_a44⟩

end C3.RV32.Sv
