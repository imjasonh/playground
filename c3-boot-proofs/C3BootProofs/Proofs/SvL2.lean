import C3BootProofs.Proofs.SvCongr

/-!
# `sigstore::verify`: the `tbsCertificate`

From the call to `Der::element` for the `tbsCertificate` at 0xD0 to the serial number at 0x1C8: the certificate's three parts, the empty rest, and the version, which must be `[0] EXPLICIT INTEGER 2`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svL2ec : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .lui a1 0x1000, .aluImm .add a1 a1 0x588, .alu .add a1 a1 sp, .aluImm .add a2 x0 0x30]
set_option maxRecDepth 100000 in
theorem svL2ec_end : blockEnd sigstoreVerifyCode 0xEC svL2ec = some 0x100 := by decide

def svL211c : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .lui a1 0x1000, .aluImm .add a1 a1 0x588, .alu .add a1 a1 sp]
set_option maxRecDepth 100000 in
theorem svL211c_end : blockEnd sigstoreVerifyCode 0x11C svL211c = some 0x12C := by decide

def svL213c : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x320, .alu .add a0 a0 sp]
set_option maxRecDepth 100000 in
theorem svL213c_end : blockEnd sigstoreVerifyCode 0x13C svL213c = some 0x144 := by decide

def svL2162 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .aluImm .add a1 sp 0x178, .aluImm .add a2 x0 0xA0]
set_option maxRecDepth 100000 in
theorem svL2162_end : blockEnd sigstoreVerifyCode 0x162 svL2162 = some 0x170 := by decide

def svL21c4 : List BInstr :=
  [.aluImm .add (20 : Fin 32) x0 0x15]
set_option maxRecDepth 100000 in
theorem svL21c4_end : blockEnd sigstoreVerifyCode 0x1C4 svL21c4 = some 0x1C6 := by decide

def svL218a : List BInstr :=
  [.alu .add (24 : Fin 32) x0 (20 : Fin 32)]
set_option maxRecDepth 100000 in
theorem svL218a_end : blockEnd sigstoreVerifyCode 0x18A svL218a = some 0x18C := by decide

def svL2192 : List BInstr :=
  [.aluImm .add a2 sp 0x200]
set_option maxRecDepth 100000 in
theorem svL2192_end : blockEnd sigstoreVerifyCode 0x192 svL2192 = some 0x194 := by decide

def svL219c : List BInstr :=
  [.aluImm .add a0 sp 0x200, .aluImm .add a1 x0 0x2]
set_option maxRecDepth 100000 in
theorem svL219c_end : blockEnd sigstoreVerifyCode 0x19C svL219c = some 0x1A0 := by decide

def svL21a8 : List BInstr :=
  [.aluImm .and a0 a0 0x1, .alu .add (20 : Fin 32) x0 a1]
set_option maxRecDepth 100000 in
theorem svL21a8_end : blockEnd sigstoreVerifyCode 0x1A8 svL21a8 = some 0x1AC := by decide

def svL21b0 : List BInstr :=
  [.aluImm .and a0 (20 : Fin 32) 0x1, .aluImm .add (20 : Fin 32) x0 0x15]
set_option maxRecDepth 100000 in
theorem svL21b0_end : blockEnd sigstoreVerifyCode 0x1B0 svL21b0 = some 0x1B6 := by decide

def svL21c0 : List BInstr :=
  [.aluImm .add (20 : Fin 32) x0 0x1]
set_option maxRecDepth 100000 in
theorem svL21c0_end : blockEnd sigstoreVerifyCode 0x1C0 svL21c0 = some 0x1C2 := by decide

set_option maxHeartbeats 0 in
theorem sv_l2 {B out bp rootp dg lp ll cp cl : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0xD0 (reg n0))
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_10 : reg n0 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (g0_11 : reg n0 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1588)
    (g0_12 : reg n0 a2 = BitVec.ofNat 32 0x30)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = lp)
    (g0_22 : reg n0 (22 : Fin 32) = dg)
    (g0_25 : reg n0 (25 : Fin 32) = rootp)
    (g0_26 : reg n0 (26 : Fin 32) = ll)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_1590 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = cp)
    (w0_1594 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = cl)
    (cc_in : SvIn B (cp) (cl).toNat) :
    (¬ (∃ tl1, derElement 0x30 (memBytes n0.mem (cp) (cl).toNat) = .ok tl1 ∧ ∃ tl8, derElement 0x30 (memBytes n0.mem ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)).toNat) = .ok tl8 ∧ ∃ tl16, derElement 3 (memBytes n0.mem (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)).toNat) = .ok tl16 ∧ ∃ bp16 bl16, derBitsOf (memBytes n0.mem (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)).toNat) (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) (.ok tl16) = .ok (bp16, bl16) ∧ (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) = 0 ∧ ∃ tl29, derOptRes 0xA0 (memBytes n0.mem ((cp) + BitVec.ofNat 32 tl1.header) (BitVec.ofNat 32 tl1.len).toNat) = some (.ok tl29) ∧ derIntIsOf n0.mem (memBytes n0.mem (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) (BitVec.ofNat 32 tl29.len).toNat) (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) (derElement 2 (memBytes n0.mem (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) (BitVec.ofNat 32 tl29.len).toNat)) ((BitVec.ofNat 32 0x2).extractLsb' 0 8) = .ok true ∧ ∃ te43, derElement 2 (memBytes n0.mem (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) (BitVec.ofNat 32 tl29.len).toNat) = .ok te43 ∧ (BitVec.ofNat 32 tl29.len) - BitVec.ofNat 32 (te43.header + te43.len) = 0 ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ tl1, derElement 0x30 (memBytes n0.mem (cp) (cl).toNat) = .ok tl1 ∧
    ∃ tl8, derElement 0x30 (memBytes n0.mem ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)).toNat) = .ok tl8 ∧
    ∃ tl16, derElement 3 (memBytes n0.mem (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)).toNat) = .ok tl16 ∧
    ∃ bp16 bl16, derBitsOf (memBytes n0.mem (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)).toNat) (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) (.ok tl16) = .ok (bp16, bl16) ∧
    (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) = 0 ∧
    ∃ tl29, derOptRes 0xA0 (memBytes n0.mem ((cp) + BitVec.ofNat 32 tl1.header) (BitVec.ofNat 32 tl1.len).toNat) = some (.ok tl29) ∧
    derIntIsOf n0.mem (memBytes n0.mem (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) (BitVec.ofNat 32 tl29.len).toNat) (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) (derElement 2 (memBytes n0.mem (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) (BitVec.ofNat 32 tl29.len).toNat)) ((BitVec.ofNat 32 0x2).extractLsb' 0 8) = .ok true ∧
    ∃ te43, derElement 2 (memBytes n0.mem (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) (BitVec.ofNat 32 tl29.len).toNat) = .ok te43 ∧
    (BitVec.ofNat 32 tl29.len) - BitVec.ofNat 32 (te43.header + te43.len) = 0 ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x1C8 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = n0.mem x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) ∧
        reg n' (9 : Fin 32) = cp ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = BitVec.ofNat 32 0x15 ∧
        reg n' (21 : Fin 32) = lp ∧
        reg n' (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) ∧
        reg n' (23 : Fin 32) = BitVec.ofNat 32 tl1.len ∧
        reg n' (24 : Fin 32) = bl16 ∧
        reg n' (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) ∧
        reg n' (26 : Fin 32) = ll ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len)) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = n0.mem x := fun _ _ => rfl
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0xD0: sv_elemF
  obtain ⟨n1, c1, s1, rk1, K1, Ok1, Er1, fr1⟩ := sv_elemF (oc := 0xA20) (dc := 0x1588) (tag := 0x30)
    F E0 s0 sv_at_d0 sv_at_d4 (by decide) (by decide) g0_10 g0_11 g0_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w0_1590 w0_1594
  have t1 : Steps n0 n1 := t0.trans c1
  have fR1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.keepL K1 (by decide)
  rw [sv_mb fR0 cc_in] at Ok1 Er1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [rk1 sp (by decide) (by decide), g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk1 (3 : Fin 32) (by decide) (by decide), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk1 (4 : Fin 32) (by decide) (by decide), g0_4]
  have g1_10 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk1 a0 (by decide) (by decide), g0_10]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [rk1 (18 : Fin 32) (by decide) (by decide), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [rk1 (19 : Fin 32) (by decide) (by decide), g0_19]
  have g1_21 : reg n1 (21 : Fin 32) = lp := by rw [rk1 (21 : Fin 32) (by decide) (by decide), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = dg := by rw [rk1 (22 : Fin 32) (by decide) (by decide), g0_22]
  have g1_25 : reg n1 (25 : Fin 32) = rootp := by rw [rk1 (25 : Fin 32) (by decide) (by decide), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = ll := by rw [rk1 (26 : Fin 32) (by decide) (by decide), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk1 (27 : Fin 32) (by decide) (by decide), g0_27]
  obtain ⟨r1, hr1⟩ : ∃ r, derElement 0x30 (memBytes n0.mem (cp) (cl).toNat) = r := ⟨_, rfl⟩
  rcases r1 with er1 | tl1
  · obtain ⟨zhr1, -⟩ := Er1 er1 hr1
    have w1_a20 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := zhr1
    -- 0xD8: lw
    obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_d8 (off' := 0xDC) (by decide)
      (by rw [g1_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s2 : St n2.mem SV n2 0xDC (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
    have m2 : n2.mem = n1.mem := u2.mem
    have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
    have t2 : Steps n0 n2 := t1.trans (.single d2)
    have fR2 : ∀ x, SvR B x → n2.mem x = n0.mem x := fun x hx => (fr2 x hx).trans (fR1 x hx)
    have E2 : SvCode n2.mem := E1.fr F fr2
    have V2 : SvSaves B n2.mem v := V1.same m2
    have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_2]
    have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_3]
    have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_4]
    have g2_10 : reg n2 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_10]
    have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
    have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
    have g2_21 : reg n2 (21 : Fin 32) = lp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
    have g2_22 : reg n2 (22 : Fin 32) = dg := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
    have g2_25 : reg n2 (25 : Fin 32) = rootp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_25]
    have g2_26 : reg n2 (26 : Fin 32) = ll := by rw [u2.regs, upd_ne (by decide) (by decide), g1_26]
    have g2_27 : reg n2 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_27]
    have g2_24 : reg n2 (24 : Fin 32) = 0 := by
      rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g1_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w1_a20]
    have w2_a20 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m2]; exact w1_a20
    clear w1_a20 zhr1
    -- 0xDC: branch, taken
    obtain ⟨n3, d3, u3⟩ := s2.taken E2.self 0x962 sv_at_dc
      (by decide) (by rw [g2_24, s2.zero]; rfl)
    have s3 : St n3.mem SV n3 0x962 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = n2.mem := u3.mem
    have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
    have t3 : Steps n0 n3 := t2.trans (.single d3)
    have fR3 : ∀ x, SvR B x → n3.mem x = n0.mem x := fun x hx => (fr3 x hx).trans (fR2 x hx)
    have E3 : SvCode n3.mem := E2.fr F fr3
    have V3 : SvSaves B n3.mem v := V2.same m3
    have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, g2_2]
    have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, g2_3]
    have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, g2_4]
    have g3_10 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u3.regs, g2_10]
    have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, g2_18]
    have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, g2_19]
    have g3_21 : reg n3 (21 : Fin 32) = lp := by rw [u3.regs, g2_21]
    have g3_22 : reg n3 (22 : Fin 32) = dg := by rw [u3.regs, g2_22]
    have g3_24 : reg n3 (24 : Fin 32) = 0 := by rw [u3.regs, g2_24]
    have g3_25 : reg n3 (25 : Fin 32) = rootp := by rw [u3.regs, g2_25]
    have g3_26 : reg n3 (26 : Fin 32) = ll := by rw [u3.regs, g2_26]
    have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u3.regs, g2_27]
    have w3_a20 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m3]; exact w2_a20
    clear w2_a20 g2_24 g2_27 g2_26 g2_25 g2_22 g2_21 g2_19 g2_18 g2_10 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
    -- 0x962: lbu
    obtain ⟨n4, d4, u4⟩ := s3.lbu E3.self sv_at_962 (off' := 0x966) (by decide)
    have s4 : St n4.mem SV n4 0x966 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
    have m4 : n4.mem = n3.mem := u4.mem
    have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
    have t4 : Steps n0 n4 := t3.trans (.single d4)
    have fR4 : ∀ x, SvR B x → n4.mem x = n0.mem x := fun x hx => (fr4 x hx).trans (fR3 x hx)
    have E4 : SvCode n4.mem := E3.fr F fr4
    have V4 : SvSaves B n4.mem v := V3.same m4
    have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_2]
    have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_3]
    have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_4]
    have g4_10 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_10]
    have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, upd_ne (by decide) (by decide), g3_18]
    have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_19]
    have g4_21 : reg n4 (21 : Fin 32) = lp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_21]
    have g4_22 : reg n4 (22 : Fin 32) = dg := by rw [u4.regs, upd_ne (by decide) (by decide), g3_22]
    have g4_24 : reg n4 (24 : Fin 32) = 0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_24]
    have g4_25 : reg n4 (25 : Fin 32) = rootp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_25]
    have g4_26 : reg n4 (26 : Fin 32) = ll := by rw [u4.regs, upd_ne (by decide) (by decide), g3_26]
    have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_27]
    have w4_a20 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m4]; exact w3_a20
    clear w3_a20 g3_27 g3_26 g3_25 g3_24 g3_22 g3_21 g3_19 g3_18 g3_10 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
    exact .inl ⟨(fun ⟨tl1', h0', _⟩ => by rw [hr1] at h0'; cases h0'), sv_fail F E4 s4 t4 fR4 V4 hret g4_2 g4_18 hO g4_3 g4_4⟩
  obtain ⟨o0_1, o4_1, o8_1, o12_1, o16_1, d8_1, d12_1⟩ := Ok1 tl1 hr1
  have w1_a20 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (cp) + BitVec.ofNat 32 tl1.header := o0_1
  have w1_a24 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := o4_1
  have w1_a28 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = cp := o8_1
  have w1_a2c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl1.header + tl1.len) := o12_1
  have w1_1590 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := d8_1
  have w1_1594 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (cl) - BitVec.ofNat 32 (tl1.header + tl1.len) := d12_1
  have b1_a30 : n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl1.tag := o16_1
  -- 0xD8: lw
  obtain ⟨n2, d2, u2⟩ := s1.lw E1.self sv_at_d8 (off' := 0xDC) (by decide)
    (by rw [g1_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s2 : St n2.mem SV n2 0xDC (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have fr2 : ∀ x, SvR B x → n2.mem x = n1.mem x := fun x _ => by rw [m2]
  have t2 : Steps n0 n2 := t1.trans (.single d2)
  have fR2 : ∀ x, SvR B x → n2.mem x = n0.mem x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.same m2
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u2.regs, upd_ne (by decide) (by decide), g1_4]
  have g2_10 : reg n2 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_10]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [u2.regs, upd_ne (by decide) (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_19]
  have g2_21 : reg n2 (21 : Fin 32) = lp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = dg := by rw [u2.regs, upd_ne (by decide) (by decide), g1_22]
  have g2_25 : reg n2 (25 : Fin 32) = rootp := by rw [u2.regs, upd_ne (by decide) (by decide), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = ll := by rw [u2.regs, upd_ne (by decide) (by decide), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u2.regs, upd_ne (by decide) (by decide), g1_27]
  have g2_24 : reg n2 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
    rw [u2.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g1_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w1_a20]
  have w2_a20 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m2]; exact w1_a20
  have w2_a24 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := by rw [m2]; exact w1_a24
  have w2_a28 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = cp := by rw [m2]; exact w1_a28
  have w2_a2c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m2]; exact w1_a2c
  have w2_1590 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m2]; exact w1_1590
  have w2_1594 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (cl) - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m2]; exact w1_1594
  have b2_a30 : n2.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl1.tag := by rw [m2]; exact b1_a30
  clear b1_a30 w1_1594 w1_1590 w1_a2c w1_a28 w1_a24 w1_a20 d12_1 d8_1 o16_1 o12_1 o8_1 o4_1 o0_1 g1_27 g1_26 g1_25 g1_22 g1_21 g1_19 g1_18 g1_10 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 Er1 Ok1 K1 rk1 s1 c1 g0_4 g0_3 fR0 t0
  -- 0xDC: branch, not taken
  obtain ⟨n3, d3, u3⟩ := s2.notTaken E2.self 0xE0 sv_at_dc
    (by decide) (by rw [g2_24, s2.zero]; exact br_beq_f (cc_in.ok_ne hr1))
  have s3 : St n3.mem SV n3 0xE0 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = n0.mem x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, g2_4]
  have g3_10 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u3.regs, g2_10]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, g2_19]
  have g3_21 : reg n3 (21 : Fin 32) = lp := by rw [u3.regs, g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = dg := by rw [u3.regs, g2_22]
  have g3_24 : reg n3 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u3.regs, g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = rootp := by rw [u3.regs, g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = ll := by rw [u3.regs, g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u3.regs, g2_27]
  have w3_a20 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m3]; exact w2_a20
  have w3_a24 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := by rw [m3]; exact w2_a24
  have w3_a28 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = cp := by rw [m3]; exact w2_a28
  have w3_a2c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m3]; exact w2_a2c
  have w3_1590 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m3]; exact w2_1590
  have w3_1594 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (cl) - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m3]; exact w2_1594
  have b3_a30 : n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl1.tag := by rw [m3]; exact b2_a30
  clear b2_a30 w2_1594 w2_1590 w2_a2c w2_a28 w2_a24 w2_a20 g2_24 g2_27 g2_26 g2_25 g2_22 g2_21 g2_19 g2_18 g2_10 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 m2 s2 u2 d2
  -- 0xE0: lw
  obtain ⟨n4, d4, u4⟩ := s3.lw E3.self sv_at_e0 (off' := 0xE4) (by decide)
    (by rw [g3_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s4 : St n4.mem SV n4 0xE4 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = n0.mem x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_4]
  have g4_10 : reg n4 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_10]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, upd_ne (by decide) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_19]
  have g4_21 : reg n4 (21 : Fin 32) = lp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = dg := by rw [u4.regs, upd_ne (by decide) (by decide), g3_22]
  have g4_24 : reg n4 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u4.regs, upd_ne (by decide) (by decide), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = rootp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = ll := by rw [u4.regs, upd_ne (by decide) (by decide), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_27]
  have g4_23 : reg n4 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by
    rw [u4.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g3_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr, w3_a24]
  have w4_a20 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m4]; exact w3_a20
  have w4_a24 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := by rw [m4]; exact w3_a24
  have w4_a28 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = cp := by rw [m4]; exact w3_a28
  have w4_a2c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m4]; exact w3_a2c
  have w4_1590 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m4]; exact w3_1590
  have w4_1594 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (cl) - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m4]; exact w3_1594
  have b4_a30 : n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl1.tag := by rw [m4]; exact b3_a30
  clear b3_a30 w3_1594 w3_1590 w3_a2c w3_a28 w3_a24 w3_a20 g3_27 g3_26 g3_25 g3_24 g3_22 g3_21 g3_19 g3_18 g3_10 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0xE4: lw
  obtain ⟨n5, d5, u5⟩ := s4.lw E4.self sv_at_e4 (off' := 0xE8) (by decide)
    (by rw [g4_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s5 : St n5.mem SV n5 0xE8 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans (.single d5)
  have fR5 : ∀ x, SvR B x → n5.mem x = n0.mem x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u5.regs, upd_ne (by decide) (by decide), g4_4]
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_10]
  have g5_18 : reg n5 (18 : Fin 32) = out := by rw [u5.regs, upd_ne (by decide) (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_19]
  have g5_21 : reg n5 (21 : Fin 32) = lp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = dg := by rw [u5.regs, upd_ne (by decide) (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u5.regs, upd_ne (by decide) (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u5.regs, upd_ne (by decide) (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = rootp := by rw [u5.regs, upd_ne (by decide) (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = ll := by rw [u5.regs, upd_ne (by decide) (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u5.regs, upd_ne (by decide) (by decide), g4_27]
  have g5_9 : reg n5 (9 : Fin 32) = cp := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g4_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr, w4_a28]
  have w5_a20 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m5]; exact w4_a20
  have w5_a24 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := by rw [m5]; exact w4_a24
  have w5_a28 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = cp := by rw [m5]; exact w4_a28
  have w5_a2c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m5]; exact w4_a2c
  have w5_1590 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m5]; exact w4_1590
  have w5_1594 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (cl) - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m5]; exact w4_1594
  have b5_a30 : n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl1.tag := by rw [m5]; exact b4_a30
  clear b4_a30 w4_1594 w4_1590 w4_a2c w4_a28 w4_a24 w4_a20 g4_23 g4_27 g4_26 g4_25 g4_24 g4_22 g4_21 g4_19 g4_18 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  -- 0xE8: lw
  obtain ⟨n6, d6, u6⟩ := s5.lw E5.self sv_at_e8 (off' := 0xEC) (by decide)
    (by rw [g5_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0xC = B + 0x21A0 + BitVec.ofNat 32 0xA2C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s6 : St n6.mem SV n6 0xEC (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = n0.mem x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_4]
  have g6_9 : reg n6 (9 : Fin 32) = cp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_9]
  have g6_10 : reg n6 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_10]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, upd_ne (by decide) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_19]
  have g6_21 : reg n6 (21 : Fin 32) = lp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = dg := by rw [u6.regs, upd_ne (by decide) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u6.regs, upd_ne (by decide) (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u6.regs, upd_ne (by decide) (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = rootp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = ll := by rw [u6.regs, upd_ne (by decide) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_27]
  have g6_8 : reg n6 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g5_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0xC = B + 0x21A0 + BitVec.ofNat 32 0xA2C by sv_addr, w5_a2c]
  have w6_a20 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m6]; exact w5_a20
  have w6_a24 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := by rw [m6]; exact w5_a24
  have w6_a28 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = cp := by rw [m6]; exact w5_a28
  have w6_a2c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m6]; exact w5_a2c
  have w6_1590 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m6]; exact w5_1590
  have w6_1594 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (cl) - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m6]; exact w5_1594
  have b6_a30 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl1.tag := by rw [m6]; exact b5_a30
  clear b5_a30 w5_1594 w5_1590 w5_a2c w5_a28 w5_a24 w5_a20 g5_9 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_19 g5_18 g5_10 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 m5 s5 u5 d5
  -- 0xEC
  obtain ⟨n7, c7, u7⟩ := s6.block svL2ec E6.self svL2ec_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem SV n7 0x100 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have rb7 : ∀ q, reg n7 q = (runBlock svL2ec (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans c7
  have fR7 : ∀ x, SvR B x → n7.mem x = n0.mem x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by
    rw [rb7, runBlock_reg _ _ _ sp s6.zero (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb7, runBlock_reg _ _ _ (3 : Fin 32) s6.zero (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb7, runBlock_reg _ _ _ (4 : Fin 32) s6.zero (by decide), g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb7, runBlock_reg _ _ _ (8 : Fin 32) s6.zero (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = cp := by
    rw [rb7, runBlock_reg _ _ _ (9 : Fin 32) s6.zero (by decide), g6_9]
  have g7_18 : reg n7 (18 : Fin 32) = out := by
    rw [rb7, runBlock_reg _ _ _ (18 : Fin 32) s6.zero (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by
    rw [rb7, runBlock_reg _ _ _ (19 : Fin 32) s6.zero (by decide), g6_19]
  have g7_21 : reg n7 (21 : Fin 32) = lp := by
    rw [rb7, runBlock_reg _ _ _ (21 : Fin 32) s6.zero (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = dg := by
    rw [rb7, runBlock_reg _ _ _ (22 : Fin 32) s6.zero (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by
    rw [rb7, runBlock_reg _ _ _ (23 : Fin 32) s6.zero (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
    rw [rb7, runBlock_reg _ _ _ (24 : Fin 32) s6.zero (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = rootp := by
    rw [rb7, runBlock_reg _ _ _ (25 : Fin 32) s6.zero (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = ll := by
    rw [rb7, runBlock_reg _ _ _ (26 : Fin 32) s6.zero (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb7, runBlock_reg _ _ _ (27 : Fin 32) s6.zero (by decide), g6_27]
  have g7_10 : reg n7 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svL2ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_10, g6_18, g6_19, g6_21, g6_22, g6_23, g6_24, g6_25, g6_26, g6_27, s6.zero])
    all_goals first | decide | sv_addr
  have g7_11 : reg n7 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1588 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svL2ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_10, g6_18, g6_19, g6_21, g6_22, g6_23, g6_24, g6_25, g6_26, g6_27, s6.zero])
    all_goals first | decide | sv_addr
  have g7_12 : reg n7 a2 = BitVec.ofNat 32 0x30 := by
    rw [rb7]; simp +decide only [runBlock, BInstr.run, svL2ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g6_2, g6_3, g6_4, g6_8, g6_9, g6_10, g6_18, g6_19, g6_21, g6_22, g6_23, g6_24, g6_25, g6_26, g6_27, s6.zero])
    all_goals first | decide | sv_addr
  have w7_a20 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m7]; exact w6_a20
  have w7_a24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl1.len := by rw [m7]; exact w6_a24
  have w7_a28 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = cp := by rw [m7]; exact w6_a28
  have w7_a2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m7]; exact w6_a2c
  have w7_1590 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m7]; exact w6_1590
  have w7_1594 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (cl) - BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m7]; exact w6_1594
  have b7_a30 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl1.tag := by rw [m7]; exact b6_a30
  clear b6_a30 w6_1594 w6_1590 w6_a2c w6_a28 w6_a24 w6_a20 g6_8 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_19 g6_18 g6_10 g6_9 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  -- 0x100: sv_elemF
  obtain ⟨n8, c8, s8, rk8, K8, Ok8, Er8, fr8⟩ := sv_elemF (oc := 0xA20) (dc := 0x1588) (tag := 0x30)
    F E7 s7 sv_at_100 sv_at_104 (by decide) (by decide) g7_10 g7_11 g7_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w7_1590 w7_1594
  have t8 : Steps n0 n8 := t7.trans c8
  have fR8 : ∀ x, SvR B x → n8.mem x = n0.mem x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.keepL K8 (by decide)
  rw [sv_mb fR7 (cc_in.restW hr1)] at Ok8 Er8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [rk8 sp (by decide) (by decide), g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk8 (3 : Fin 32) (by decide) (by decide), g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk8 (4 : Fin 32) (by decide) (by decide), g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rk8 (8 : Fin 32) (by decide) (by decide), g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = cp := by rw [rk8 (9 : Fin 32) (by decide) (by decide), g7_9]
  have g8_10 : reg n8 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk8 a0 (by decide) (by decide), g7_10]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [rk8 (18 : Fin 32) (by decide) (by decide), g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [rk8 (19 : Fin 32) (by decide) (by decide), g7_19]
  have g8_21 : reg n8 (21 : Fin 32) = lp := by rw [rk8 (21 : Fin 32) (by decide) (by decide), g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = dg := by rw [rk8 (22 : Fin 32) (by decide) (by decide), g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rk8 (23 : Fin 32) (by decide) (by decide), g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rk8 (24 : Fin 32) (by decide) (by decide), g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = rootp := by rw [rk8 (25 : Fin 32) (by decide) (by decide), g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = ll := by rw [rk8 (26 : Fin 32) (by decide) (by decide), g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk8 (27 : Fin 32) (by decide) (by decide), g7_27]
  obtain ⟨r8, hr8⟩ : ∃ r, derElement 0x30 (memBytes n0.mem ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)).toNat) = r := ⟨_, rfl⟩
  rcases r8 with er8 | tl8
  · obtain ⟨zhr8, -⟩ := Er8 er8 hr8
    have w8_a20 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := zhr8
    clear b7_a30 w7_1594 w7_1590 w7_a2c w7_a28 w7_a24 w7_a20 g7_12 g7_11 g7_10 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
    -- 0x108: lw
    obtain ⟨n9, d9, u9⟩ := s8.lw E8.self sv_at_108 (off' := 0x10C) (by decide)
      (by rw [g8_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s9 : St n9.mem SV n9 0x10C (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have m9 : n9.mem = n8.mem := u9.mem
    have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
    have t9 : Steps n0 n9 := t8.trans (.single d9)
    have fR9 : ∀ x, SvR B x → n9.mem x = n0.mem x := fun x hx => (fr9 x hx).trans (fR8 x hx)
    have E9 : SvCode n9.mem := E8.fr F fr9
    have V9 : SvSaves B n9.mem v := V8.same m9
    have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_2]
    have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_3]
    have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_4]
    have g9_8 : reg n9 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_8]
    have g9_9 : reg n9 (9 : Fin 32) = cp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_9]
    have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, upd_ne (by decide) (by decide), g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_19]
    have g9_21 : reg n9 (21 : Fin 32) = lp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = dg := by rw [u9.regs, upd_ne (by decide) (by decide), g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u9.regs, upd_ne (by decide) (by decide), g8_23]
    have g9_24 : reg n9 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u9.regs, upd_ne (by decide) (by decide), g8_24]
    have g9_25 : reg n9 (25 : Fin 32) = rootp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_25]
    have g9_26 : reg n9 (26 : Fin 32) = ll := by rw [u9.regs, upd_ne (by decide) (by decide), g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_27]
    have g9_10 : reg n9 a0 = 0 := by
      rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g8_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w8_a20]
    have w9_a20 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m9]; exact w8_a20
    clear w8_a20 zhr8
    -- 0x10C: branch, taken
    obtain ⟨n10, d10, u10⟩ := s9.taken E9.self 0x962 sv_at_10c
      (by decide) (by rw [g9_10, s9.zero]; rfl)
    have s10 : St n10.mem SV n10 0x962 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
    have m10 : n10.mem = n9.mem := u10.mem
    have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
    have t10 : Steps n0 n10 := t9.trans (.single d10)
    have fR10 : ∀ x, SvR B x → n10.mem x = n0.mem x := fun x hx => (fr10 x hx).trans (fR9 x hx)
    have E10 : SvCode n10.mem := E9.fr F fr10
    have V10 : SvSaves B n10.mem v := V9.same m10
    have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, g9_2]
    have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, g9_3]
    have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, g9_4]
    have g10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u10.regs, g9_8]
    have g10_9 : reg n10 (9 : Fin 32) = cp := by rw [u10.regs, g9_9]
    have g10_10 : reg n10 a0 = 0 := by rw [u10.regs, g9_10]
    have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, g9_18]
    have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, g9_19]
    have g10_21 : reg n10 (21 : Fin 32) = lp := by rw [u10.regs, g9_21]
    have g10_22 : reg n10 (22 : Fin 32) = dg := by rw [u10.regs, g9_22]
    have g10_23 : reg n10 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u10.regs, g9_23]
    have g10_24 : reg n10 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u10.regs, g9_24]
    have g10_25 : reg n10 (25 : Fin 32) = rootp := by rw [u10.regs, g9_25]
    have g10_26 : reg n10 (26 : Fin 32) = ll := by rw [u10.regs, g9_26]
    have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u10.regs, g9_27]
    have w10_a20 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m10]; exact w9_a20
    clear w9_a20 g9_10 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
    -- 0x962: lbu
    obtain ⟨n11, d11, u11⟩ := s10.lbu E10.self sv_at_962 (off' := 0x966) (by decide)
    have s11 : St n11.mem SV n11 0x966 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
    have t11 : Steps n0 n11 := t10.trans (.single d11)
    have fR11 : ∀ x, SvR B x → n11.mem x = n0.mem x := fun x hx => (fr11 x hx).trans (fR10 x hx)
    have E11 : SvCode n11.mem := E10.fr F fr11
    have V11 : SvSaves B n11.mem v := V10.same m11
    have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_2]
    have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_3]
    have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_4]
    have g11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_8]
    have g11_9 : reg n11 (9 : Fin 32) = cp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_9]
    have g11_10 : reg n11 a0 = 0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_10]
    have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, upd_ne (by decide) (by decide), g10_18]
    have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_19]
    have g11_21 : reg n11 (21 : Fin 32) = lp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_21]
    have g11_22 : reg n11 (22 : Fin 32) = dg := by rw [u11.regs, upd_ne (by decide) (by decide), g10_22]
    have g11_23 : reg n11 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u11.regs, upd_ne (by decide) (by decide), g10_23]
    have g11_24 : reg n11 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u11.regs, upd_ne (by decide) (by decide), g10_24]
    have g11_25 : reg n11 (25 : Fin 32) = rootp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_25]
    have g11_26 : reg n11 (26 : Fin 32) = ll := by rw [u11.regs, upd_ne (by decide) (by decide), g10_26]
    have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_27]
    have w11_a20 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m11]; exact w10_a20
    clear w10_a20 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_19 g10_18 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
    exact .inl ⟨(fun ⟨tl1', h0', tl8', h1', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr8] at h1'; cases h1'), sv_fail F E11 s11 t11 fR11 V11 hret g11_2 g11_18 hO g11_3 g11_4⟩
  obtain ⟨o0_8, o4_8, o8_8, o12_8, o16_8, d8_8, d12_8⟩ := Ok8 tl8 hr8
  have w8_a20 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := o0_8
  have w8_a24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl8.len := o4_8
  have w8_a28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := o8_8
  have w8_a2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := o12_8
  have w8_1590 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := d8_8
  have w8_1594 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := d12_8
  have b8_a30 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := o16_8
  clear b7_a30 w7_1594 w7_1590 w7_a2c w7_a28 w7_a24 w7_a20 g7_12 g7_11 g7_10 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 rb7 s7 m7 u7 c7
  -- 0x108: lw
  obtain ⟨n9, d9, u9⟩ := s8.lw E8.self sv_at_108 (off' := 0x10C) (by decide)
    (by rw [g8_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s9 : St n9.mem SV n9 0x10C (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans (.single d9)
  have fR9 : ∀ x, SvR B x → n9.mem x = n0.mem x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = cp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, upd_ne (by decide) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_19]
  have g9_21 : reg n9 (21 : Fin 32) = lp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = dg := by rw [u9.regs, upd_ne (by decide) (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u9.regs, upd_ne (by decide) (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u9.regs, upd_ne (by decide) (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = rootp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = ll := by rw [u9.regs, upd_ne (by decide) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_27]
  have g9_10 : reg n9 a0 = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by
    rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g8_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w8_a20]
  have w9_a20 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [m9]; exact w8_a20
  have w9_a24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl8.len := by rw [m9]; exact w8_a24
  have w9_a28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m9]; exact w8_a28
  have w9_a2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m9]; exact w8_a2c
  have w9_1590 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m9]; exact w8_1590
  have w9_1594 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m9]; exact w8_1594
  have b9_a30 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := by rw [m9]; exact b8_a30
  clear b8_a30 w8_1594 w8_1590 w8_a2c w8_a28 w8_a24 w8_a20 d12_8 d8_8 o16_8 o12_8 o8_8 o4_8 o0_8 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_19 g8_18 g8_10 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 Er8 Ok8 K8 rk8 s8 c8
  -- 0x10C: branch, not taken
  obtain ⟨n10, d10, u10⟩ := s9.notTaken E9.self 0x110 sv_at_10c
    (by decide) (by rw [g9_10, s9.zero]; exact br_beq_f ((cc_in.restW hr1).ok_ne hr8))
  have s10 : St n10.mem SV n10 0x110 (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, SvR B x → n10.mem x = n0.mem x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u10.regs, g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = cp := by rw [u10.regs, g9_9]
  have g10_10 : reg n10 a0 = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [u10.regs, g9_10]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, g9_19]
  have g10_21 : reg n10 (21 : Fin 32) = lp := by rw [u10.regs, g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = dg := by rw [u10.regs, g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u10.regs, g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u10.regs, g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = rootp := by rw [u10.regs, g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = ll := by rw [u10.regs, g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u10.regs, g9_27]
  have w10_a20 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [m10]; exact w9_a20
  have w10_a24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl8.len := by rw [m10]; exact w9_a24
  have w10_a28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m10]; exact w9_a28
  have w10_a2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m10]; exact w9_a2c
  have w10_1590 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m10]; exact w9_1590
  have w10_1594 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m10]; exact w9_1594
  have b10_a30 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := by rw [m10]; exact b9_a30
  clear b9_a30 w9_1594 w9_1590 w9_a2c w9_a28 w9_a24 w9_a20 g9_10 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
  -- 0x110: sw
  obtain ⟨n11, d11, s11, fr11, K11, W11, rg11⟩ := sv_sw F E10 s10 sv_at_110 (off' := 0x112) (c := 0x80)
    (by decide) (by rw [g10_2]; sv_addr) (by decide) (by decide)
  have t11 : Steps n0 n11 := t10.trans d11
  have fR11 : ∀ x, SvR B x → n11.mem x = n0.mem x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.keep K11 (by decide)
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [rg11 sp, g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg11 (3 : Fin 32), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg11 (4 : Fin 32), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg11 (8 : Fin 32), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = cp := by rw [rg11 (9 : Fin 32), g10_9]
  have g11_10 : reg n11 a0 = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [rg11 a0, g10_10]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [rg11 (18 : Fin 32), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [rg11 (19 : Fin 32), g10_19]
  have g11_21 : reg n11 (21 : Fin 32) = lp := by rw [rg11 (21 : Fin 32), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = dg := by rw [rg11 (22 : Fin 32), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rg11 (23 : Fin 32), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rg11 (24 : Fin 32), g10_24]
  have g11_25 : reg n11 (25 : Fin 32) = rootp := by rw [rg11 (25 : Fin 32), g10_25]
  have g11_26 : reg n11 (26 : Fin 32) = ll := by rw [rg11 (26 : Fin 32), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg11 (27 : Fin 32), g10_27]
  have w11_a20 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := (K11.w32 (by decide) (by decide)).trans w10_a20
  have w11_a24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl8.len := (K11.w32 (by decide) (by decide)).trans w10_a24
  have w11_a28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K11.w32 (by decide) (by decide)).trans w10_a28
  have w11_a2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K11.w32 (by decide) (by decide)).trans w10_a2c
  have w11_1590 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := (K11.w32 (by decide) (by decide)).trans w10_1590
  have w11_1594 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := (K11.w32 (by decide) (by decide)).trans w10_1594
  have b11_a30 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := (K11.b8 (by decide) (by decide)).trans b10_a30
  have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [W11, g10_25]
  clear b10_a30 w10_1594 w10_1590 w10_a2c w10_a28 w10_a24 w10_a20 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_19 g10_18 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
  -- 0x112: sw
  obtain ⟨n12, d12, s12, fr12, K12, W12, rg12⟩ := sv_sw F E11 s11 sv_at_112 (off' := 0x114) (c := 0x84)
    (by decide) (by rw [g11_2]; sv_addr) (by decide) (by decide)
  have t12 : Steps n0 n12 := t11.trans d12
  have fR12 : ∀ x, SvR B x → n12.mem x = n0.mem x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.keep K12 (by decide)
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [rg12 sp, g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg12 (3 : Fin 32), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg12 (4 : Fin 32), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg12 (8 : Fin 32), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = cp := by rw [rg12 (9 : Fin 32), g11_9]
  have g12_10 : reg n12 a0 = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [rg12 a0, g11_10]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [rg12 (18 : Fin 32), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [rg12 (19 : Fin 32), g11_19]
  have g12_21 : reg n12 (21 : Fin 32) = lp := by rw [rg12 (21 : Fin 32), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = dg := by rw [rg12 (22 : Fin 32), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rg12 (23 : Fin 32), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rg12 (24 : Fin 32), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = rootp := by rw [rg12 (25 : Fin 32), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = ll := by rw [rg12 (26 : Fin 32), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg12 (27 : Fin 32), g11_27]
  have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K12.w32 (by decide) (by decide)).trans w11_80
  have w12_a20 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := (K12.w32 (by decide) (by decide)).trans w11_a20
  have w12_a24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl8.len := (K12.w32 (by decide) (by decide)).trans w11_a24
  have w12_a28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K12.w32 (by decide) (by decide)).trans w11_a28
  have w12_a2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K12.w32 (by decide) (by decide)).trans w11_a2c
  have w12_1590 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := (K12.w32 (by decide) (by decide)).trans w11_1590
  have w12_1594 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := (K12.w32 (by decide) (by decide)).trans w11_1594
  have b12_a30 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := (K12.b8 (by decide) (by decide)).trans b11_a30
  have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [W12, g11_22]
  clear w11_80 b11_a30 w11_1594 w11_1590 w11_a2c w11_a28 w11_a24 w11_a20 g11_27 g11_26 g11_25 g11_24 g11_23 g11_22 g11_21 g11_19 g11_18 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 rg11 W11 K11 fr11 s11 d11
  -- 0x114: lw
  obtain ⟨n13, d13, u13⟩ := s12.lw E12.self sv_at_114 (off' := 0x118) (by decide)
    (by rw [g12_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s13 : St n13.mem SV n13 0x118 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans (.single d13)
  have fR13 : ∀ x, SvR B x → n13.mem x = n0.mem x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = cp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_9]
  have g13_10 : reg n13 a0 = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [u13.regs, upd_ne (by decide) (by decide), g12_10]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, upd_ne (by decide) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_19]
  have g13_21 : reg n13 (21 : Fin 32) = lp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_21]
  have g13_23 : reg n13 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u13.regs, upd_ne (by decide) (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u13.regs, upd_ne (by decide) (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = rootp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = ll := by rw [u13.regs, upd_ne (by decide) (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_27]
  have g13_22 : reg n13 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [u13.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g12_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr, w12_a28]
  have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m13]; exact w12_80
  have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m13]; exact w12_84
  have w13_a20 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [m13]; exact w12_a20
  have w13_a24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl8.len := by rw [m13]; exact w12_a24
  have w13_a28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m13]; exact w12_a28
  have w13_a2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m13]; exact w12_a2c
  have w13_1590 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m13]; exact w12_1590
  have w13_1594 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m13]; exact w12_1594
  have b13_a30 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := by rw [m13]; exact b12_a30
  clear w12_84 b12_a30 w12_1594 w12_1590 w12_a2c w12_a28 w12_a24 w12_a20 w12_80 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_19 g12_18 g12_10 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 rg12 W12 K12 fr12 s12 d12
  -- 0x118: lw
  obtain ⟨n14, d14, u14⟩ := s13.lw E13.self sv_at_118 (off' := 0x11C) (by decide)
    (by rw [g13_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0xC = B + 0x21A0 + BitVec.ofNat 32 0xA2C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s14 : St n14.mem SV n14 0x11C (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
  have t14 : Steps n0 n14 := t13.trans (.single d14)
  have fR14 : ∀ x, SvR B x → n14.mem x = n0.mem x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.same m14
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_4]
  have g14_8 : reg n14 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_8]
  have g14_9 : reg n14 (9 : Fin 32) = cp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_9]
  have g14_10 : reg n14 a0 = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [u14.regs, upd_ne (by decide) (by decide), g13_10]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, upd_ne (by decide) (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_19]
  have g14_21 : reg n14 (21 : Fin 32) = lp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u14.regs, upd_ne (by decide) (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u14.regs, upd_ne (by decide) (by decide), g13_24]
  have g14_26 : reg n14 (26 : Fin 32) = ll := by rw [u14.regs, upd_ne (by decide) (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_27]
  have g14_25 : reg n14 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by
    rw [u14.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g13_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0xC = B + 0x21A0 + BitVec.ofNat 32 0xA2C by sv_addr, w13_a2c]
  have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m14]; exact w13_80
  have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m14]; exact w13_84
  have w14_a20 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [m14]; exact w13_a20
  have w14_a24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl8.len := by rw [m14]; exact w13_a24
  have w14_a28 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m14]; exact w13_a28
  have w14_a2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m14]; exact w13_a2c
  have w14_1590 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m14]; exact w13_1590
  have w14_1594 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m14]; exact w13_1594
  have b14_a30 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := by rw [m14]; exact b13_a30
  clear b13_a30 w13_1594 w13_1590 w13_a2c w13_a28 w13_a24 w13_a20 w13_84 w13_80 g13_22 g13_27 g13_26 g13_25 g13_24 g13_23 g13_21 g13_19 g13_18 g13_10 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
  -- 0x11C
  obtain ⟨n15, c15, u15⟩ := s14.block svL211c E14.self svL211c_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have s15 : St n15.mem SV n15 0x12C (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have rb15 : ∀ q, reg n15 q = (runBlock svL211c (n14.mem, reg n14)).2 q := fun q => by rw [u15.regs]
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans c15
  have fR15 : ∀ x, SvR B x → n15.mem x = n0.mem x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by
    rw [rb15, runBlock_reg _ _ _ sp s14.zero (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb15, runBlock_reg _ _ _ (3 : Fin 32) s14.zero (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb15, runBlock_reg _ _ _ (4 : Fin 32) s14.zero (by decide), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb15, runBlock_reg _ _ _ (8 : Fin 32) s14.zero (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = cp := by
    rw [rb15, runBlock_reg _ _ _ (9 : Fin 32) s14.zero (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = out := by
    rw [rb15, runBlock_reg _ _ _ (18 : Fin 32) s14.zero (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by
    rw [rb15, runBlock_reg _ _ _ (19 : Fin 32) s14.zero (by decide), g14_19]
  have g15_21 : reg n15 (21 : Fin 32) = lp := by
    rw [rb15, runBlock_reg _ _ _ (21 : Fin 32) s14.zero (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb15, runBlock_reg _ _ _ (22 : Fin 32) s14.zero (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by
    rw [rb15, runBlock_reg _ _ _ (23 : Fin 32) s14.zero (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
    rw [rb15, runBlock_reg _ _ _ (24 : Fin 32) s14.zero (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by
    rw [rb15, runBlock_reg _ _ _ (25 : Fin 32) s14.zero (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = ll := by
    rw [rb15, runBlock_reg _ _ _ (26 : Fin 32) s14.zero (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb15, runBlock_reg _ _ _ (27 : Fin 32) s14.zero (by decide), g14_27]
  have g15_10 : reg n15 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, svL211c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_10, g14_18, g14_19, g14_21, g14_22, g14_23, g14_24, g14_25, g14_26, g14_27, s14.zero])
    all_goals first | decide | sv_addr
  have g15_11 : reg n15 a1 = B + 0x21A0 + BitVec.ofNat 32 0x1588 := by
    rw [rb15]; simp +decide only [runBlock, BInstr.run, svL211c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g14_2, g14_3, g14_4, g14_8, g14_9, g14_10, g14_18, g14_19, g14_21, g14_22, g14_23, g14_24, g14_25, g14_26, g14_27, s14.zero])
    all_goals first | decide | sv_addr
  have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m15]; exact w14_80
  have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m15]; exact w14_84
  have w15_a20 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 tl8.header := by rw [m15]; exact w14_a20
  have w15_a24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl8.len := by rw [m15]; exact w14_a24
  have w15_a28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m15]; exact w14_a28
  have w15_a2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m15]; exact w14_a2c
  have w15_1590 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = ((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m15]; exact w14_1590
  have w15_1594 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = ((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m15]; exact w14_1594
  have b15_a30 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := by rw [m15]; exact b14_a30
  clear b14_a30 w14_1594 w14_1590 w14_a2c w14_a28 w14_a24 w14_a20 w14_84 w14_80 g14_25 g14_27 g14_26 g14_24 g14_23 g14_22 g14_21 g14_19 g14_18 g14_10 g14_9 g14_8 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
  -- 0x12C: sv_bitsF
  obtain ⟨n16, c16, s16, sp16, rk16, K16, A16, Ok16, Er16, fr16⟩ := sv_bitsF (oc := 0xA20) (dc := 0x1588)
    F E15 s15 sv_at_12c sv_at_130 (by decide) (by decide) g15_2 g15_10 g15_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w15_1590 w15_1594 ((cc_in.restW hr1).restW hr8)
  have t16 : Steps n0 n16 := t15.trans c16
  have fR16 : ∀ x, SvR B x → n16.mem x = n0.mem x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.keepL K16 (by decide)
  rw [sv_mb fR15 ((cc_in.restW hr1).restW hr8)] at A16 Ok16 Er16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [rk16 sp (by decide) (by decide), g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk16 (3 : Fin 32) (by decide) (by decide), g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk16 (4 : Fin 32) (by decide) (by decide), g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rk16 (8 : Fin 32) (by decide) (by decide), g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = cp := by rw [rk16 (9 : Fin 32) (by decide) (by decide), g15_9]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [rk16 (18 : Fin 32) (by decide) (by decide), g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [rk16 (19 : Fin 32) (by decide) (by decide), g15_19]
  have g16_21 : reg n16 (21 : Fin 32) = lp := by rw [rk16 (21 : Fin 32) (by decide) (by decide), g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rk16 (22 : Fin 32) (by decide) (by decide), g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rk16 (23 : Fin 32) (by decide) (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rk16 (24 : Fin 32) (by decide) (by decide), g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rk16 (25 : Fin 32) (by decide) (by decide), g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = ll := by rw [rk16 (26 : Fin 32) (by decide) (by decide), g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk16 (27 : Fin 32) (by decide) (by decide), g15_27]
  obtain ⟨r16, hr16⟩ : ∃ r, derElement 3 (memBytes n0.mem (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)).toNat) = r := ⟨_, rfl⟩
  rcases r16 with er16 | tl16
  · obtain ⟨zhr16, -⟩ := Er16 er16 (by rw [hr16]; rfl)
    have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K16.w32 (by decide) (by decide)).trans w15_80
    have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K16.w32 (by decide) (by decide)).trans w15_84
    have w16_a28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K16.w32 (by decide) (by decide)).trans w15_a28
    have w16_a2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K16.w32 (by decide) (by decide)).trans w15_a2c
    have b16_a30 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := (K16.b8 (by decide) (by decide)).trans b15_a30
    have w16_a20 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := zhr16
    clear b15_a30 w15_1594 w15_1590 w15_a2c w15_a28 w15_a24 w15_a20 w15_84 w15_80 g15_11 g15_10 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_19 g15_18 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 rb15 s15 m15 u15 c15
    -- 0x134: lw
    obtain ⟨n17, d17, u17⟩ := s16.lw E16.self sv_at_134 (off' := 0x138) (by decide)
      (by rw [g16_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s17 : St n17.mem SV n17 0x138 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
    have m17 : n17.mem = n16.mem := u17.mem
    have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
    have t17 : Steps n0 n17 := t16.trans (.single d17)
    have fR17 : ∀ x, SvR B x → n17.mem x = n0.mem x := fun x hx => (fr17 x hx).trans (fR16 x hx)
    have E17 : SvCode n17.mem := E16.fr F fr17
    have V17 : SvSaves B n17.mem v := V16.same m17
    have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_2]
    have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_3]
    have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_4]
    have g17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_8]
    have g17_9 : reg n17 (9 : Fin 32) = cp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_9]
    have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, upd_ne (by decide) (by decide), g16_18]
    have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_19]
    have g17_21 : reg n17 (21 : Fin 32) = lp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_21]
    have g17_22 : reg n17 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_22]
    have g17_23 : reg n17 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u17.regs, upd_ne (by decide) (by decide), g16_23]
    have g17_24 : reg n17 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u17.regs, upd_ne (by decide) (by decide), g16_24]
    have g17_25 : reg n17 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_25]
    have g17_26 : reg n17 (26 : Fin 32) = ll := by rw [u17.regs, upd_ne (by decide) (by decide), g16_26]
    have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_27]
    have g17_11 : reg n17 a1 = 0 := by
      rw [u17.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g16_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w16_a20]
    have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m17]; exact w16_80
    have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m17]; exact w16_84
    have w17_a20 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m17]; exact w16_a20
    have w17_a28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m17]; exact w16_a28
    have w17_a2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m17]; exact w16_a2c
    have b17_a30 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := by rw [m17]; exact b16_a30
    clear w16_a20 b16_a30 w16_a2c w16_a28 w16_84 w16_80 zhr16
    -- 0x138: branch, taken
    obtain ⟨n18, d18, u18⟩ := s17.taken E17.self 0x962 sv_at_138
      (by decide) (by rw [g17_11, s17.zero]; rfl)
    have s18 : St n18.mem SV n18 0x962 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
    have m18 : n18.mem = n17.mem := u18.mem
    have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
    have t18 : Steps n0 n18 := t17.trans (.single d18)
    have fR18 : ∀ x, SvR B x → n18.mem x = n0.mem x := fun x hx => (fr18 x hx).trans (fR17 x hx)
    have E18 : SvCode n18.mem := E17.fr F fr18
    have V18 : SvSaves B n18.mem v := V17.same m18
    have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, g17_2]
    have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, g17_3]
    have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, g17_4]
    have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u18.regs, g17_8]
    have g18_9 : reg n18 (9 : Fin 32) = cp := by rw [u18.regs, g17_9]
    have g18_11 : reg n18 a1 = 0 := by rw [u18.regs, g17_11]
    have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, g17_18]
    have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, g17_19]
    have g18_21 : reg n18 (21 : Fin 32) = lp := by rw [u18.regs, g17_21]
    have g18_22 : reg n18 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u18.regs, g17_22]
    have g18_23 : reg n18 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u18.regs, g17_23]
    have g18_24 : reg n18 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u18.regs, g17_24]
    have g18_25 : reg n18 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u18.regs, g17_25]
    have g18_26 : reg n18 (26 : Fin 32) = ll := by rw [u18.regs, g17_26]
    have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u18.regs, g17_27]
    have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m18]; exact w17_80
    have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m18]; exact w17_84
    have w18_a20 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m18]; exact w17_a20
    have w18_a28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m18]; exact w17_a28
    have w18_a2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m18]; exact w17_a2c
    have b18_a30 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := by rw [m18]; exact b17_a30
    clear b17_a30 w17_a2c w17_a28 w17_a20 w17_84 w17_80 g17_11 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
    -- 0x962: lbu
    obtain ⟨n19, d19, u19⟩ := s18.lbu E18.self sv_at_962 (off' := 0x966) (by decide)
    have s19 : St n19.mem SV n19 0x966 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
    have m19 : n19.mem = n18.mem := u19.mem
    have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
    have t19 : Steps n0 n19 := t18.trans (.single d19)
    have fR19 : ∀ x, SvR B x → n19.mem x = n0.mem x := fun x hx => (fr19 x hx).trans (fR18 x hx)
    have E19 : SvCode n19.mem := E18.fr F fr19
    have V19 : SvSaves B n19.mem v := V18.same m19
    have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
    have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
    have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
    have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_8]
    have g19_9 : reg n19 (9 : Fin 32) = cp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_9]
    have g19_11 : reg n19 a1 = 0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_11]
    have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
    have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
    have g19_21 : reg n19 (21 : Fin 32) = lp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
    have g19_22 : reg n19 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_22]
    have g19_23 : reg n19 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u19.regs, upd_ne (by decide) (by decide), g18_23]
    have g19_24 : reg n19 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u19.regs, upd_ne (by decide) (by decide), g18_24]
    have g19_25 : reg n19 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
    have g19_26 : reg n19 (26 : Fin 32) = ll := by rw [u19.regs, upd_ne (by decide) (by decide), g18_26]
    have g19_27 : reg n19 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
    have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m19]; exact w18_80
    have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m19]; exact w18_84
    have w19_a20 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m19]; exact w18_a20
    have w19_a28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m19]; exact w18_a28
    have w19_a2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m19]; exact w18_a2c
    have b19_a30 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := by rw [m19]; exact b18_a30
    clear b18_a30 w18_a2c w18_a28 w18_a20 w18_84 w18_80 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_19 g18_18 g18_11 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
    exact .inl ⟨(fun ⟨tl1', h0', tl8', h1', tl16', h2', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr8] at h1'; cases h1'; rw [hr16] at h2'; cases h2'), sv_fail F E19 s19 t19 fR19 V19 hret g19_2 g19_18 hO g19_3 g19_4⟩
  obtain ⟨r16b, hr16b⟩ : ∃ r, derBitsOf (memBytes n0.mem (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)).toNat) (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) (.ok tl16) = r := ⟨_, rfl⟩
  rcases r16b with er16b | ⟨bp16, bl16⟩
  · obtain ⟨zhr16b, -⟩ := Er16 er16b (by rw [hr16, hr16b])
    have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K16.w32 (by decide) (by decide)).trans w15_80
    have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K16.w32 (by decide) (by decide)).trans w15_84
    have w16_a28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K16.w32 (by decide) (by decide)).trans w15_a28
    have w16_a2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K16.w32 (by decide) (by decide)).trans w15_a2c
    have b16_a30 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := (K16.b8 (by decide) (by decide)).trans b15_a30
    have w16_a20 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := zhr16b
    clear b15_a30 w15_1594 w15_1590 w15_a2c w15_a28 w15_a24 w15_a20 w15_84 w15_80 g15_11 g15_10 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_19 g15_18 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 rb15 s15 m15 u15 c15
    -- 0x134: lw
    obtain ⟨n17, d17, u17⟩ := s16.lw E16.self sv_at_134 (off' := 0x138) (by decide)
      (by rw [g16_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s17 : St n17.mem SV n17 0x138 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
    have m17 : n17.mem = n16.mem := u17.mem
    have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
    have t17 : Steps n0 n17 := t16.trans (.single d17)
    have fR17 : ∀ x, SvR B x → n17.mem x = n0.mem x := fun x hx => (fr17 x hx).trans (fR16 x hx)
    have E17 : SvCode n17.mem := E16.fr F fr17
    have V17 : SvSaves B n17.mem v := V16.same m17
    have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_2]
    have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_3]
    have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_4]
    have g17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_8]
    have g17_9 : reg n17 (9 : Fin 32) = cp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_9]
    have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, upd_ne (by decide) (by decide), g16_18]
    have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_19]
    have g17_21 : reg n17 (21 : Fin 32) = lp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_21]
    have g17_22 : reg n17 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_22]
    have g17_23 : reg n17 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u17.regs, upd_ne (by decide) (by decide), g16_23]
    have g17_24 : reg n17 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u17.regs, upd_ne (by decide) (by decide), g16_24]
    have g17_25 : reg n17 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_25]
    have g17_26 : reg n17 (26 : Fin 32) = ll := by rw [u17.regs, upd_ne (by decide) (by decide), g16_26]
    have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_27]
    have g17_11 : reg n17 a1 = 0 := by
      rw [u17.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g16_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w16_a20]
    have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m17]; exact w16_80
    have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m17]; exact w16_84
    have w17_a20 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m17]; exact w16_a20
    have w17_a28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m17]; exact w16_a28
    have w17_a2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m17]; exact w16_a2c
    have b17_a30 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := by rw [m17]; exact b16_a30
    clear w16_a20 b16_a30 w16_a2c w16_a28 w16_84 w16_80 zhr16b
    -- 0x138: branch, taken
    obtain ⟨n18, d18, u18⟩ := s17.taken E17.self 0x962 sv_at_138
      (by decide) (by rw [g17_11, s17.zero]; rfl)
    have s18 : St n18.mem SV n18 0x962 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
    have m18 : n18.mem = n17.mem := u18.mem
    have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
    have t18 : Steps n0 n18 := t17.trans (.single d18)
    have fR18 : ∀ x, SvR B x → n18.mem x = n0.mem x := fun x hx => (fr18 x hx).trans (fR17 x hx)
    have E18 : SvCode n18.mem := E17.fr F fr18
    have V18 : SvSaves B n18.mem v := V17.same m18
    have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, g17_2]
    have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, g17_3]
    have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, g17_4]
    have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u18.regs, g17_8]
    have g18_9 : reg n18 (9 : Fin 32) = cp := by rw [u18.regs, g17_9]
    have g18_11 : reg n18 a1 = 0 := by rw [u18.regs, g17_11]
    have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, g17_18]
    have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, g17_19]
    have g18_21 : reg n18 (21 : Fin 32) = lp := by rw [u18.regs, g17_21]
    have g18_22 : reg n18 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u18.regs, g17_22]
    have g18_23 : reg n18 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u18.regs, g17_23]
    have g18_24 : reg n18 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u18.regs, g17_24]
    have g18_25 : reg n18 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u18.regs, g17_25]
    have g18_26 : reg n18 (26 : Fin 32) = ll := by rw [u18.regs, g17_26]
    have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u18.regs, g17_27]
    have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m18]; exact w17_80
    have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m18]; exact w17_84
    have w18_a20 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m18]; exact w17_a20
    have w18_a28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m18]; exact w17_a28
    have w18_a2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m18]; exact w17_a2c
    have b18_a30 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := by rw [m18]; exact b17_a30
    clear b17_a30 w17_a2c w17_a28 w17_a20 w17_84 w17_80 g17_11 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
    -- 0x962: lbu
    obtain ⟨n19, d19, u19⟩ := s18.lbu E18.self sv_at_962 (off' := 0x966) (by decide)
    have s19 : St n19.mem SV n19 0x966 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
    have m19 : n19.mem = n18.mem := u19.mem
    have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
    have t19 : Steps n0 n19 := t18.trans (.single d19)
    have fR19 : ∀ x, SvR B x → n19.mem x = n0.mem x := fun x hx => (fr19 x hx).trans (fR18 x hx)
    have E19 : SvCode n19.mem := E18.fr F fr19
    have V19 : SvSaves B n19.mem v := V18.same m19
    have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
    have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
    have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
    have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_8]
    have g19_9 : reg n19 (9 : Fin 32) = cp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_9]
    have g19_11 : reg n19 a1 = 0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_11]
    have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
    have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
    have g19_21 : reg n19 (21 : Fin 32) = lp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
    have g19_22 : reg n19 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_22]
    have g19_23 : reg n19 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u19.regs, upd_ne (by decide) (by decide), g18_23]
    have g19_24 : reg n19 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u19.regs, upd_ne (by decide) (by decide), g18_24]
    have g19_25 : reg n19 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_25]
    have g19_26 : reg n19 (26 : Fin 32) = ll := by rw [u19.regs, upd_ne (by decide) (by decide), g18_26]
    have g19_27 : reg n19 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_27]
    have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m19]; exact w18_80
    have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m19]; exact w18_84
    have w19_a20 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m19]; exact w18_a20
    have w19_a28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m19]; exact w18_a28
    have w19_a2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m19]; exact w18_a2c
    have b19_a30 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := by rw [m19]; exact b18_a30
    clear b18_a30 w18_a2c w18_a28 w18_a20 w18_84 w18_80 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_19 g18_18 g18_11 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
    exact .inl ⟨(fun ⟨tl1', h0', tl8', h1', tl16', h2', bp16', bl16', h3', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr8] at h1'; cases h1'; rw [hr16] at h2'; cases h2'; rw [hr16b] at h3'; cases h3'), sv_fail F E19 s19 t19 fR19 V19 hret g19_2 g19_18 hO g19_3 g19_4⟩
  obtain ⟨p0_16, p4_16⟩ := Ok16 bp16 bl16 (by rw [hr16, hr16b])
  obtain ⟨d8_16, d12_16⟩ := A16 tl16 hr16
  have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K16.w32 (by decide) (by decide)).trans w15_80
  have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K16.w32 (by decide) (by decide)).trans w15_84
  have w16_a28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K16.w32 (by decide) (by decide)).trans w15_a28
  have w16_a2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K16.w32 (by decide) (by decide)).trans w15_a2c
  have b16_a30 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := (K16.b8 (by decide) (by decide)).trans b15_a30
  have w16_a20 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = bp16 := p0_16
  have w16_a24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = bl16 := p4_16
  have w16_1590 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := d8_16
  have w16_1594 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := d12_16
  clear b15_a30 w15_1594 w15_1590 w15_a2c w15_a28 w15_a24 w15_a20 w15_84 w15_80 g15_11 g15_10 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_19 g15_18 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 rb15 s15 m15 u15 c15
  -- 0x134: lw
  obtain ⟨n17, d17, u17⟩ := s16.lw E16.self sv_at_134 (off' := 0x138) (by decide)
    (by rw [g16_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s17 : St n17.mem SV n17 0x138 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans (.single d17)
  have fR17 : ∀ x, SvR B x → n17.mem x = n0.mem x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_4]
  have g17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = cp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_9]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, upd_ne (by decide) (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_19]
  have g17_21 : reg n17 (21 : Fin 32) = lp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u17.regs, upd_ne (by decide) (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u17.regs, upd_ne (by decide) (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = ll := by rw [u17.regs, upd_ne (by decide) (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_27]
  have g17_11 : reg n17 a1 = bp16 := by
    rw [u17.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g16_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w16_a20]
  have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m17]; exact w16_80
  have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m17]; exact w16_84
  have w17_a20 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = bp16 := by rw [m17]; exact w16_a20
  have w17_a24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = bl16 := by rw [m17]; exact w16_a24
  have w17_a28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m17]; exact w16_a28
  have w17_a2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m17]; exact w16_a2c
  have w17_1590 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m17]; exact w16_1590
  have w17_1594 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m17]; exact w16_1594
  have b17_a30 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := by rw [m17]; exact b16_a30
  clear w16_1594 w16_1590 w16_a24 w16_a20 b16_a30 w16_a2c w16_a28 w16_84 w16_80 d12_16 d8_16 p4_16 p0_16 g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_19 g16_18 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 Er16 Ok16 A16 K16 rk16 sp16 s16 c16
  -- 0x138: branch, not taken
  obtain ⟨n18, d18, u18⟩ := s17.notTaken E17.self 0x13C sv_at_138
    (by decide) (by rw [g17_11, s17.zero]; exact br_beq_f ((((cc_in.restW hr1).restW hr8).bitsW hr16 hr16b).pos_ne))
  have s18 : St n18.mem SV n18 0x13C (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans (.single d18)
  have fR18 : ∀ x, SvR B x → n18.mem x = n0.mem x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u18.regs, g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = cp := by rw [u18.regs, g17_9]
  have g18_11 : reg n18 a1 = bp16 := by rw [u18.regs, g17_11]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, g17_19]
  have g18_21 : reg n18 (21 : Fin 32) = lp := by rw [u18.regs, g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u18.regs, g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u18.regs, g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u18.regs, g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u18.regs, g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = ll := by rw [u18.regs, g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u18.regs, g17_27]
  have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m18]; exact w17_80
  have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m18]; exact w17_84
  have w18_a20 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = bp16 := by rw [m18]; exact w17_a20
  have w18_a24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = bl16 := by rw [m18]; exact w17_a24
  have w18_a28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m18]; exact w17_a28
  have w18_a2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m18]; exact w17_a2c
  have w18_1590 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m18]; exact w17_1590
  have w18_1594 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m18]; exact w17_1594
  have b18_a30 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := by rw [m18]; exact b17_a30
  clear b17_a30 w17_1594 w17_1590 w17_a2c w17_a28 w17_a24 w17_a20 w17_84 w17_80 g17_11 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
  -- 0x13C
  obtain ⟨n19, c19, u19⟩ := s18.block svL213c E18.self svL213c_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have s19 : St n19.mem SV n19 0x144 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have rb19 : ∀ q, reg n19 q = (runBlock svL213c (n18.mem, reg n18)).2 q := fun q => by rw [u19.regs]
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans c19
  have fR19 : ∀ x, SvR B x → n19.mem x = n0.mem x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by
    rw [rb19, runBlock_reg _ _ _ sp s18.zero (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb19, runBlock_reg _ _ _ (3 : Fin 32) s18.zero (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb19, runBlock_reg _ _ _ (4 : Fin 32) s18.zero (by decide), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb19, runBlock_reg _ _ _ (8 : Fin 32) s18.zero (by decide), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = cp := by
    rw [rb19, runBlock_reg _ _ _ (9 : Fin 32) s18.zero (by decide), g18_9]
  have g19_11 : reg n19 a1 = bp16 := by
    rw [rb19, runBlock_reg _ _ _ a1 s18.zero (by decide), g18_11]
  have g19_18 : reg n19 (18 : Fin 32) = out := by
    rw [rb19, runBlock_reg _ _ _ (18 : Fin 32) s18.zero (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by
    rw [rb19, runBlock_reg _ _ _ (19 : Fin 32) s18.zero (by decide), g18_19]
  have g19_21 : reg n19 (21 : Fin 32) = lp := by
    rw [rb19, runBlock_reg _ _ _ (21 : Fin 32) s18.zero (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb19, runBlock_reg _ _ _ (22 : Fin 32) s18.zero (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by
    rw [rb19, runBlock_reg _ _ _ (23 : Fin 32) s18.zero (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
    rw [rb19, runBlock_reg _ _ _ (24 : Fin 32) s18.zero (by decide), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by
    rw [rb19, runBlock_reg _ _ _ (25 : Fin 32) s18.zero (by decide), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = ll := by
    rw [rb19, runBlock_reg _ _ _ (26 : Fin 32) s18.zero (by decide), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb19, runBlock_reg _ _ _ (27 : Fin 32) s18.zero (by decide), g18_27]
  have g19_10 : reg n19 a0 = B + 0x21A0 + BitVec.ofNat 32 0x1320 := by
    rw [rb19]; simp +decide only [runBlock, BInstr.run, svL213c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g18_2, g18_3, g18_4, g18_8, g18_9, g18_11, g18_18, g18_19, g18_21, g18_22, g18_23, g18_24, g18_25, g18_26, g18_27, s18.zero])
    all_goals first | decide | sv_addr
  have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m19]; exact w18_80
  have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m19]; exact w18_84
  have w19_a20 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = bp16 := by rw [m19]; exact w18_a20
  have w19_a24 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = bl16 := by rw [m19]; exact w18_a24
  have w19_a28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m19]; exact w18_a28
  have w19_a2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m19]; exact w18_a2c
  have w19_1590 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m19]; exact w18_1590
  have w19_1594 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m19]; exact w18_1594
  have b19_a30 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := by rw [m19]; exact b18_a30
  clear b18_a30 w18_1594 w18_1590 w18_a2c w18_a28 w18_a24 w18_a20 w18_84 w18_80 g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_19 g18_18 g18_11 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
  -- 0x144: lw
  obtain ⟨n20, d20, u20⟩ := s19.lw E19.self sv_at_144 (off' := 0x148) (by decide)
    (by rw [g19_10, show B + 0x21A0 + BitVec.ofNat 32 0x1320 + 0x274 = B + 0x21A0 + BitVec.ofNat 32 0x1594 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s20 : St n20.mem SV n20 0x148 (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
  have t20 : Steps n0 n20 := t19.trans (.single d20)
  have fR20 : ∀ x, SvR B x → n20.mem x = n0.mem x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.same m20
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = cp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_9]
  have g20_11 : reg n20 a1 = bp16 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_11]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, upd_ne (by decide) (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_19]
  have g20_21 : reg n20 (21 : Fin 32) = lp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u20.regs, upd_ne (by decide) (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u20.regs, upd_ne (by decide) (by decide), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = ll := by rw [u20.regs, upd_ne (by decide) (by decide), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_27]
  have g20_10 : reg n20 a0 = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by
    rw [u20.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g19_10, show B + 0x21A0 + BitVec.ofNat 32 0x1320 + 0x274 = B + 0x21A0 + BitVec.ofNat 32 0x1594 by sv_addr, w19_1594]
  have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m20]; exact w19_80
  have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m20]; exact w19_84
  have w20_a20 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = bp16 := by rw [m20]; exact w19_a20
  have w20_a24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = bl16 := by rw [m20]; exact w19_a24
  have w20_a28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m20]; exact w19_a28
  have w20_a2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m20]; exact w19_a2c
  have w20_1590 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m20]; exact w19_1590
  have w20_1594 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m20]; exact w19_1594
  have b20_a30 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := by rw [m20]; exact b19_a30
  clear b19_a30 w19_1594 w19_1590 w19_a2c w19_a28 w19_a24 w19_a20 w19_84 w19_80 g19_10 g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_19 g19_18 g19_11 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 rb19 s19 m19 u19 c19
  by_cases hz_20 : (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) = 0
  rotate_left
  · -- 0x148: branch, taken
    obtain ⟨n21, d21, u21⟩ := s20.taken E20.self 0x966 sv_at_148
      (by decide) (by rw [g20_10, s20.zero]; exact br_bne_t hz_20)
    have s21 : St n21.mem SV n21 0x966 (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
    have m21 : n21.mem = n20.mem := u21.mem
    have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
    have t21 : Steps n0 n21 := t20.trans (.single d21)
    have fR21 : ∀ x, SvR B x → n21.mem x = n0.mem x := fun x hx => (fr21 x hx).trans (fR20 x hx)
    have E21 : SvCode n21.mem := E20.fr F fr21
    have V21 : SvSaves B n21.mem v := V20.same m21
    have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, g20_2]
    have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, g20_3]
    have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, g20_4]
    have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u21.regs, g20_8]
    have g21_9 : reg n21 (9 : Fin 32) = cp := by rw [u21.regs, g20_9]
    have g21_10 : reg n21 a0 = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [u21.regs, g20_10]
    have g21_11 : reg n21 a1 = bp16 := by rw [u21.regs, g20_11]
    have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, g20_18]
    have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, g20_19]
    have g21_21 : reg n21 (21 : Fin 32) = lp := by rw [u21.regs, g20_21]
    have g21_22 : reg n21 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u21.regs, g20_22]
    have g21_23 : reg n21 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u21.regs, g20_23]
    have g21_24 : reg n21 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u21.regs, g20_24]
    have g21_25 : reg n21 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u21.regs, g20_25]
    have g21_26 : reg n21 (26 : Fin 32) = ll := by rw [u21.regs, g20_26]
    have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u21.regs, g20_27]
    have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m21]; exact w20_80
    have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m21]; exact w20_84
    have w21_a20 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = bp16 := by rw [m21]; exact w20_a20
    have w21_a24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = bl16 := by rw [m21]; exact w20_a24
    have w21_a28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m21]; exact w20_a28
    have w21_a2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m21]; exact w20_a2c
    have w21_1590 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m21]; exact w20_1590
    have w21_1594 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m21]; exact w20_1594
    have b21_a30 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := by rw [m21]; exact b20_a30
    clear b20_a30 w20_1594 w20_1590 w20_a2c w20_a28 w20_a24 w20_a20 w20_84 w20_80 g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_19 g20_18 g20_11 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20
    exact .inl ⟨(fun ⟨tl1', h0', tl8', h1', tl16', h2', bp16', bl16', h3', h4', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr8] at h1'; cases h1'; rw [hr16] at h2'; cases h2'; rw [hr16b] at h3'; cases h3'; exact hz_20 h4'), sv_fail F E21 s21 t21 fR21 V21 hret g21_2 g21_18 hO g21_3 g21_4⟩
  -- 0x148: branch, not taken
  obtain ⟨n21, d21, u21⟩ := s20.notTaken E20.self 0x14C sv_at_148
    (by decide) (by rw [g20_10, s20.zero]; exact br_bne_f hz_20)
  have s21 : St n21.mem SV n21 0x14C (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans (.single d21)
  have fR21 : ∀ x, SvR B x → n21.mem x = n0.mem x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [u21.regs, g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u21.regs, g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u21.regs, g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u21.regs, g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = cp := by rw [u21.regs, g20_9]
  have g21_10 : reg n21 a0 = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [u21.regs, g20_10]
  have g21_11 : reg n21 a1 = bp16 := by rw [u21.regs, g20_11]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [u21.regs, g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [u21.regs, g20_19]
  have g21_21 : reg n21 (21 : Fin 32) = lp := by rw [u21.regs, g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u21.regs, g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u21.regs, g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u21.regs, g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u21.regs, g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = ll := by rw [u21.regs, g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u21.regs, g20_27]
  have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m21]; exact w20_80
  have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m21]; exact w20_84
  have w21_a20 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = bp16 := by rw [m21]; exact w20_a20
  have w21_a24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = bl16 := by rw [m21]; exact w20_a24
  have w21_a28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m21]; exact w20_a28
  have w21_a2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m21]; exact w20_a2c
  have w21_1590 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m21]; exact w20_1590
  have w21_1594 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m21]; exact w20_1594
  have b21_a30 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := by rw [m21]; exact b20_a30
  clear b20_a30 w20_1594 w20_1590 w20_a2c w20_a28 w20_a24 w20_a20 w20_84 w20_80 g20_10 g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_19 g20_18 g20_11 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20
  -- 0x14C: sw
  obtain ⟨n22, d22, s22, fr22, K22, W22, rg22⟩ := sv_sw F E21 s21 sv_at_14c (off' := 0x14E) (c := 0x7C)
    (by decide) (by rw [g21_2]; sv_addr) (by decide) (by decide)
  have t22 : Steps n0 n22 := t21.trans d22
  have fR22 : ∀ x, SvR B x → n22.mem x = n0.mem x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.keep K22 (by decide)
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [rg22 sp, g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg22 (3 : Fin 32), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg22 (4 : Fin 32), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg22 (8 : Fin 32), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = cp := by rw [rg22 (9 : Fin 32), g21_9]
  have g22_10 : reg n22 a0 = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [rg22 a0, g21_10]
  have g22_11 : reg n22 a1 = bp16 := by rw [rg22 a1, g21_11]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [rg22 (18 : Fin 32), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [rg22 (19 : Fin 32), g21_19]
  have g22_21 : reg n22 (21 : Fin 32) = lp := by rw [rg22 (21 : Fin 32), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg22 (22 : Fin 32), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rg22 (23 : Fin 32), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rg22 (24 : Fin 32), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rg22 (25 : Fin 32), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = ll := by rw [rg22 (26 : Fin 32), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg22 (27 : Fin 32), g21_27]
  have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K22.w32 (by decide) (by decide)).trans w21_80
  have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K22.w32 (by decide) (by decide)).trans w21_84
  have w22_a20 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = bp16 := (K22.w32 (by decide) (by decide)).trans w21_a20
  have w22_a24 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = bl16 := (K22.w32 (by decide) (by decide)).trans w21_a24
  have w22_a28 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K22.w32 (by decide) (by decide)).trans w21_a28
  have w22_a2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K22.w32 (by decide) (by decide)).trans w21_a2c
  have w22_1590 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K22.w32 (by decide) (by decide)).trans w21_1590
  have w22_1594 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K22.w32 (by decide) (by decide)).trans w21_1594
  have b22_a30 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := (K22.b8 (by decide) (by decide)).trans b21_a30
  have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [W22, g21_11]
  clear b21_a30 w21_1594 w21_1590 w21_a2c w21_a28 w21_a24 w21_a20 w21_84 w21_80 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_19 g21_18 g21_11 g21_10 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 m21 s21 u21 d21
  -- 0x14E: lw
  obtain ⟨n23, d23, u23⟩ := s22.lw E22.self sv_at_14e (off' := 0x152) (by decide)
    (by rw [g22_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s23 : St n23.mem SV n23 0x152 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, SvR B x → n23.mem x = n0.mem x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = cp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_9]
  have g23_10 : reg n23 a0 = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_10]
  have g23_11 : reg n23 a1 = bp16 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_11]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
  have g23_21 : reg n23 (21 : Fin 32) = lp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u23.regs, upd_ne (by decide) (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u23.regs, upd_ne (by decide) (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = ll := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_27]
  have g23_20 : reg n23 (20 : Fin 32) = bl16 := by
    rw [u23.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g22_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr, w22_a24]
  have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m23]; exact w22_7c
  have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m23]; exact w22_80
  have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m23]; exact w22_84
  have w23_a20 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = bp16 := by rw [m23]; exact w22_a20
  have w23_a24 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = bl16 := by rw [m23]; exact w22_a24
  have w23_a28 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m23]; exact w22_a28
  have w23_a2c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m23]; exact w22_a2c
  have w23_1590 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m23]; exact w22_1590
  have w23_1594 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m23]; exact w22_1594
  have b23_a30 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := by rw [m23]; exact b22_a30
  clear w22_7c b22_a30 w22_1594 w22_1590 w22_a2c w22_a28 w22_a24 w22_a20 w22_84 w22_80 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_19 g22_18 g22_11 g22_10 g22_9 g22_8 g22_4 g22_3 g22_2 V22 E22 fR22 t22 rg22 W22 K22 fr22 s22 d22
  -- 0x152: sw
  obtain ⟨n24, d24, s24, fr24, K24, W24, rg24⟩ := sv_sw F E23 s23 sv_at_152 (off' := 0x156) (c := 0x178)
    (by decide) (by rw [g23_2]; sv_addr) (by decide) (by decide)
  have t24 : Steps n0 n24 := t23.trans d24
  have fR24 : ∀ x, SvR B x → n24.mem x = n0.mem x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.keep K24 (by decide)
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [rg24 sp, g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg24 (3 : Fin 32), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg24 (4 : Fin 32), g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg24 (8 : Fin 32), g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = cp := by rw [rg24 (9 : Fin 32), g23_9]
  have g24_10 : reg n24 a0 = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [rg24 a0, g23_10]
  have g24_11 : reg n24 a1 = bp16 := by rw [rg24 a1, g23_11]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [rg24 (18 : Fin 32), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [rg24 (19 : Fin 32), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = bl16 := by rw [rg24 (20 : Fin 32), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = lp := by rw [rg24 (21 : Fin 32), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg24 (22 : Fin 32), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rg24 (23 : Fin 32), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rg24 (24 : Fin 32), g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rg24 (25 : Fin 32), g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = ll := by rw [rg24 (26 : Fin 32), g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg24 (27 : Fin 32), g23_27]
  have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := (K24.w32 (by decide) (by decide)).trans w23_7c
  have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K24.w32 (by decide) (by decide)).trans w23_80
  have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K24.w32 (by decide) (by decide)).trans w23_84
  have w24_a20 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = bp16 := (K24.w32 (by decide) (by decide)).trans w23_a20
  have w24_a24 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = bl16 := (K24.w32 (by decide) (by decide)).trans w23_a24
  have w24_a28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K24.w32 (by decide) (by decide)).trans w23_a28
  have w24_a2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K24.w32 (by decide) (by decide)).trans w23_a2c
  have w24_1590 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K24.w32 (by decide) (by decide)).trans w23_1590
  have w24_1594 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K24.w32 (by decide) (by decide)).trans w23_1594
  have b24_a30 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := (K24.b8 (by decide) (by decide)).trans b23_a30
  have w24_178 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [W24, g23_24]
  clear b23_a30 w23_1594 w23_1590 w23_a2c w23_a28 w23_a24 w23_a20 w23_84 w23_80 w23_7c g23_20 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_19 g23_18 g23_11 g23_10 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
  -- 0x156: sw
  obtain ⟨n25, d25, s25, fr25, K25, W25, rg25⟩ := sv_sw F E24 s24 sv_at_156 (off' := 0x15A) (c := 0x17C)
    (by decide) (by rw [g24_2]; sv_addr) (by decide) (by decide)
  have t25 : Steps n0 n25 := t24.trans d25
  have fR25 : ∀ x, SvR B x → n25.mem x = n0.mem x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.keep K25 (by decide)
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [rg25 sp, g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg25 (3 : Fin 32), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg25 (4 : Fin 32), g24_4]
  have g25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg25 (8 : Fin 32), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = cp := by rw [rg25 (9 : Fin 32), g24_9]
  have g25_10 : reg n25 a0 = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [rg25 a0, g24_10]
  have g25_11 : reg n25 a1 = bp16 := by rw [rg25 a1, g24_11]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [rg25 (18 : Fin 32), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [rg25 (19 : Fin 32), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = bl16 := by rw [rg25 (20 : Fin 32), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = lp := by rw [rg25 (21 : Fin 32), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg25 (22 : Fin 32), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rg25 (23 : Fin 32), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rg25 (24 : Fin 32), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rg25 (25 : Fin 32), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = ll := by rw [rg25 (26 : Fin 32), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg25 (27 : Fin 32), g24_27]
  have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := (K25.w32 (by decide) (by decide)).trans w24_7c
  have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K25.w32 (by decide) (by decide)).trans w24_80
  have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K25.w32 (by decide) (by decide)).trans w24_84
  have w25_178 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := (K25.w32 (by decide) (by decide)).trans w24_178
  have w25_a20 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = bp16 := (K25.w32 (by decide) (by decide)).trans w24_a20
  have w25_a24 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = bl16 := (K25.w32 (by decide) (by decide)).trans w24_a24
  have w25_a28 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K25.w32 (by decide) (by decide)).trans w24_a28
  have w25_a2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K25.w32 (by decide) (by decide)).trans w24_a2c
  have w25_1590 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K25.w32 (by decide) (by decide)).trans w24_1590
  have w25_1594 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K25.w32 (by decide) (by decide)).trans w24_1594
  have b25_a30 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := (K25.b8 (by decide) (by decide)).trans b24_a30
  have w25_17c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [W25, g24_23]
  clear w24_178 b24_a30 w24_1594 w24_1590 w24_a2c w24_a28 w24_a24 w24_a20 w24_84 w24_80 w24_7c g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_11 g24_10 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 rg24 W24 K24 fr24 s24 d24
  -- 0x15A: sw
  obtain ⟨n26, d26, s26, fr26, K26, W26, rg26⟩ := sv_sw F E25 s25 sv_at_15a (off' := 0x15E) (c := 0x180)
    (by decide) (by rw [g25_2]; sv_addr) (by decide) (by decide)
  have t26 : Steps n0 n26 := t25.trans d26
  have fR26 : ∀ x, SvR B x → n26.mem x = n0.mem x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.keep K26 (by decide)
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [rg26 sp, g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg26 (3 : Fin 32), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg26 (4 : Fin 32), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg26 (8 : Fin 32), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = cp := by rw [rg26 (9 : Fin 32), g25_9]
  have g26_10 : reg n26 a0 = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [rg26 a0, g25_10]
  have g26_11 : reg n26 a1 = bp16 := by rw [rg26 a1, g25_11]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [rg26 (18 : Fin 32), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [rg26 (19 : Fin 32), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = bl16 := by rw [rg26 (20 : Fin 32), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = lp := by rw [rg26 (21 : Fin 32), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg26 (22 : Fin 32), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rg26 (23 : Fin 32), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rg26 (24 : Fin 32), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rg26 (25 : Fin 32), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = ll := by rw [rg26 (26 : Fin 32), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg26 (27 : Fin 32), g25_27]
  have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := (K26.w32 (by decide) (by decide)).trans w25_7c
  have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K26.w32 (by decide) (by decide)).trans w25_80
  have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K26.w32 (by decide) (by decide)).trans w25_84
  have w26_178 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := (K26.w32 (by decide) (by decide)).trans w25_178
  have w26_17c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := (K26.w32 (by decide) (by decide)).trans w25_17c
  have w26_a20 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = bp16 := (K26.w32 (by decide) (by decide)).trans w25_a20
  have w26_a24 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = bl16 := (K26.w32 (by decide) (by decide)).trans w25_a24
  have w26_a28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K26.w32 (by decide) (by decide)).trans w25_a28
  have w26_a2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K26.w32 (by decide) (by decide)).trans w25_a2c
  have w26_1590 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K26.w32 (by decide) (by decide)).trans w25_1590
  have w26_1594 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K26.w32 (by decide) (by decide)).trans w25_1594
  have b26_a30 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := (K26.b8 (by decide) (by decide)).trans b25_a30
  have w26_180 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (cp) + BitVec.ofNat 32 tl1.header := by rw [W26, g25_24]
  clear w25_17c b25_a30 w25_1594 w25_1590 w25_a2c w25_a28 w25_a24 w25_a20 w25_178 w25_84 w25_80 w25_7c g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_11 g25_10 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 rg25 W25 K25 fr25 s25 d25
  -- 0x15E: sw
  obtain ⟨n27, d27, s27, fr27, K27, W27, rg27⟩ := sv_sw F E26 s26 sv_at_15e (off' := 0x162) (c := 0x184)
    (by decide) (by rw [g26_2]; sv_addr) (by decide) (by decide)
  have t27 : Steps n0 n27 := t26.trans d27
  have fR27 : ∀ x, SvR B x → n27.mem x = n0.mem x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.keep K27 (by decide)
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [rg27 sp, g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg27 (3 : Fin 32), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg27 (4 : Fin 32), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg27 (8 : Fin 32), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = cp := by rw [rg27 (9 : Fin 32), g26_9]
  have g27_10 : reg n27 a0 = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [rg27 a0, g26_10]
  have g27_11 : reg n27 a1 = bp16 := by rw [rg27 a1, g26_11]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [rg27 (18 : Fin 32), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [rg27 (19 : Fin 32), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = bl16 := by rw [rg27 (20 : Fin 32), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = lp := by rw [rg27 (21 : Fin 32), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg27 (22 : Fin 32), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rg27 (23 : Fin 32), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rg27 (24 : Fin 32), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rg27 (25 : Fin 32), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = ll := by rw [rg27 (26 : Fin 32), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg27 (27 : Fin 32), g26_27]
  have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := (K27.w32 (by decide) (by decide)).trans w26_7c
  have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K27.w32 (by decide) (by decide)).trans w26_80
  have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K27.w32 (by decide) (by decide)).trans w26_84
  have w27_178 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := (K27.w32 (by decide) (by decide)).trans w26_178
  have w27_17c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := (K27.w32 (by decide) (by decide)).trans w26_17c
  have w27_180 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (cp) + BitVec.ofNat 32 tl1.header := (K27.w32 (by decide) (by decide)).trans w26_180
  have w27_a20 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = bp16 := (K27.w32 (by decide) (by decide)).trans w26_a20
  have w27_a24 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = bl16 := (K27.w32 (by decide) (by decide)).trans w26_a24
  have w27_a28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := (K27.w32 (by decide) (by decide)).trans w26_a28
  have w27_a2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := (K27.w32 (by decide) (by decide)).trans w26_a2c
  have w27_1590 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K27.w32 (by decide) (by decide)).trans w26_1590
  have w27_1594 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K27.w32 (by decide) (by decide)).trans w26_1594
  have b27_a30 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := (K27.b8 (by decide) (by decide)).trans b26_a30
  have w27_184 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = BitVec.ofNat 32 tl1.len := by rw [W27, g26_23]
  clear w26_180 b26_a30 w26_1594 w26_1590 w26_a2c w26_a28 w26_a24 w26_a20 w26_17c w26_178 w26_84 w26_80 w26_7c g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_11 g26_10 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 rg26 W26 K26 fr26 s26 d26
  -- 0x162
  obtain ⟨n28, c28, u28⟩ := s27.block svL2162 E27.self svL2162_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have s28 : St n28.mem SV n28 0x170 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have rb28 : ∀ q, reg n28 q = (runBlock svL2162 (n27.mem, reg n27)).2 q := fun q => by rw [u28.regs]
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
  have g28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb28, runBlock_reg _ _ _ (8 : Fin 32) s27.zero (by decide), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = cp := by
    rw [rb28, runBlock_reg _ _ _ (9 : Fin 32) s27.zero (by decide), g27_9]
  have g28_18 : reg n28 (18 : Fin 32) = out := by
    rw [rb28, runBlock_reg _ _ _ (18 : Fin 32) s27.zero (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by
    rw [rb28, runBlock_reg _ _ _ (19 : Fin 32) s27.zero (by decide), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = bl16 := by
    rw [rb28, runBlock_reg _ _ _ (20 : Fin 32) s27.zero (by decide), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = lp := by
    rw [rb28, runBlock_reg _ _ _ (21 : Fin 32) s27.zero (by decide), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb28, runBlock_reg _ _ _ (22 : Fin 32) s27.zero (by decide), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by
    rw [rb28, runBlock_reg _ _ _ (23 : Fin 32) s27.zero (by decide), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
    rw [rb28, runBlock_reg _ _ _ (24 : Fin 32) s27.zero (by decide), g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by
    rw [rb28, runBlock_reg _ _ _ (25 : Fin 32) s27.zero (by decide), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = ll := by
    rw [rb28, runBlock_reg _ _ _ (26 : Fin 32) s27.zero (by decide), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb28, runBlock_reg _ _ _ (27 : Fin 32) s27.zero (by decide), g27_27]
  have g28_10 : reg n28 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb28]; simp +decide only [runBlock, BInstr.run, svL2162, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g27_2, g27_3, g27_4, g27_8, g27_9, g27_10, g27_11, g27_18, g27_19, g27_20, g27_21, g27_22, g27_23, g27_24, g27_25, g27_26, g27_27, s27.zero])
    all_goals first | decide | sv_addr
  have g28_11 : reg n28 a1 = B + 0x21A0 + BitVec.ofNat 32 0x178 := by
    rw [rb28]; simp +decide only [runBlock, BInstr.run, svL2162, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g27_2, g27_3, g27_4, g27_8, g27_9, g27_10, g27_11, g27_18, g27_19, g27_20, g27_21, g27_22, g27_23, g27_24, g27_25, g27_26, g27_27, s27.zero])
    all_goals first | decide | sv_addr
  have g28_12 : reg n28 a2 = BitVec.ofNat 32 0xA0 := by
    rw [rb28]; simp +decide only [runBlock, BInstr.run, svL2162, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g27_2, g27_3, g27_4, g27_8, g27_9, g27_10, g27_11, g27_18, g27_19, g27_20, g27_21, g27_22, g27_23, g27_24, g27_25, g27_26, g27_27, s27.zero])
    all_goals first | decide | sv_addr
  have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m28]; exact w27_7c
  have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m28]; exact w27_80
  have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m28]; exact w27_84
  have w28_178 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m28]; exact w27_178
  have w28_17c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m28]; exact w27_17c
  have w28_180 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m28]; exact w27_180
  have w28_184 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = BitVec.ofNat 32 tl1.len := by rw [m28]; exact w27_184
  have w28_a20 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = bp16 := by rw [m28]; exact w27_a20
  have w28_a24 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = bl16 := by rw [m28]; exact w27_a24
  have w28_a28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m28]; exact w27_a28
  have w28_a2c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [m28]; exact w27_a2c
  have w28_1590 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m28]; exact w27_1590
  have w28_1594 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m28]; exact w27_1594
  have b28_a30 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl8.tag := by rw [m28]; exact b27_a30
  clear w27_184 b27_a30 w27_1594 w27_1590 w27_a2c w27_a28 w27_a24 w27_a20 w27_180 w27_17c w27_178 w27_84 w27_80 w27_7c g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_11 g27_10 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 rg27 W27 K27 fr27 s27 d27
  -- 0x170: sv_optF
  obtain ⟨n29, c29, s29, sp29, rk29, K29, R29, fr29⟩ := sv_optF (oc := 0xA20) (dc := 0x178) (tag := 0xA0)
    F E28 s28 sv_at_170 sv_at_174 (by decide) (by decide) g28_2 g28_10 g28_11 g28_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w28_180 w28_184 (cc_in.contentW hr1)
  have t29 : Steps n0 n29 := t28.trans c29
  have fR29 : ∀ x, SvR B x → n29.mem x = n0.mem x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.keepL K29 (by decide)
  rw [sv_mb fR28 (cc_in.contentW hr1)] at R29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [rk29 sp (by decide) (by decide), g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk29 (3 : Fin 32) (by decide) (by decide), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk29 (4 : Fin 32) (by decide) (by decide), g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rk29 (8 : Fin 32) (by decide) (by decide), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = cp := by rw [rk29 (9 : Fin 32) (by decide) (by decide), g28_9]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [rk29 (18 : Fin 32) (by decide) (by decide), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [rk29 (19 : Fin 32) (by decide) (by decide), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = bl16 := by rw [rk29 (20 : Fin 32) (by decide) (by decide), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = lp := by rw [rk29 (21 : Fin 32) (by decide) (by decide), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rk29 (22 : Fin 32) (by decide) (by decide), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rk29 (23 : Fin 32) (by decide) (by decide), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [rk29 (24 : Fin 32) (by decide) (by decide), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rk29 (25 : Fin 32) (by decide) (by decide), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = ll := by rw [rk29 (26 : Fin 32) (by decide) (by decide), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk29 (27 : Fin 32) (by decide) (by decide), g28_27]
  obtain ⟨r29, hr29⟩ : ∃ r, derOptRes 0xA0 (memBytes n0.mem ((cp) + BitVec.ofNat 32 tl1.header) (BitVec.ofNat 32 tl1.len).toNat) = r := ⟨_, rfl⟩
  rcases r29 with _ | (er29 | tl29)
  · rw [hr29] at R29
    obtain ⟨y0_29, y4_29⟩ := R29
    have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := (K29.w32 (by decide) (by decide)).trans w28_7c
    have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K29.w32 (by decide) (by decide)).trans w28_80
    have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K29.w32 (by decide) (by decide)).trans w28_84
    have w29_178 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := (K29.w32 (by decide) (by decide)).trans w28_178
    have w29_17c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := (K29.w32 (by decide) (by decide)).trans w28_17c
    have w29_1590 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K29.w32 (by decide) (by decide)).trans w28_1590
    have w29_1594 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K29.w32 (by decide) (by decide)).trans w28_1594
    have w29_a24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = 0 := y4_29
    have b29_a20 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := y0_29
    clear b28_a30 w28_1594 w28_1590 w28_a2c w28_a28 w28_a24 w28_a20 w28_184 w28_180 w28_17c w28_178 w28_84 w28_80 w28_7c g28_12 g28_11 g28_10 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 rb28 s28 m28 u28 c28
    -- 0x178: lbu
    obtain ⟨n30, d30, u30⟩ := s29.lbu E29.self sv_at_178 (off' := 0x17C) (by decide)
    have s30 : St n30.mem SV n30 0x17C (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
    have m30 : n30.mem = n29.mem := u30.mem
    have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
    have t30 : Steps n0 n30 := t29.trans (.single d30)
    have fR30 : ∀ x, SvR B x → n30.mem x = n0.mem x := fun x hx => (fr30 x hx).trans (fR29 x hx)
    have E30 : SvCode n30.mem := E29.fr F fr30
    have V30 : SvSaves B n30.mem v := V29.same m30
    have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_2]
    have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_3]
    have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_4]
    have g30_8 : reg n30 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_8]
    have g30_9 : reg n30 (9 : Fin 32) = cp := by rw [u30.regs, upd_ne (by decide) (by decide), g29_9]
    have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, upd_ne (by decide) (by decide), g29_18]
    have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, upd_ne (by decide) (by decide), g29_19]
    have g30_20 : reg n30 (20 : Fin 32) = bl16 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_20]
    have g30_21 : reg n30 (21 : Fin 32) = lp := by rw [u30.regs, upd_ne (by decide) (by decide), g29_21]
    have g30_22 : reg n30 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_22]
    have g30_23 : reg n30 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u30.regs, upd_ne (by decide) (by decide), g29_23]
    have g30_24 : reg n30 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u30.regs, upd_ne (by decide) (by decide), g29_24]
    have g30_25 : reg n30 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_25]
    have g30_26 : reg n30 (26 : Fin 32) = ll := by rw [u30.regs, upd_ne (by decide) (by decide), g29_26]
    have g30_27 : reg n30 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_27]
    have g30_10 : reg n30 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
      rw [u30.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g29_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, b29_a20]
    have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m30]; exact w29_7c
    have w30_80 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m30]; exact w29_80
    have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m30]; exact w29_84
    have w30_178 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m30]; exact w29_178
    have w30_17c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m30]; exact w29_17c
    have w30_a24 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = 0 := by rw [m30]; exact w29_a24
    have w30_1590 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m30]; exact w29_1590
    have w30_1594 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m30]; exact w29_1594
    have b30_a20 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m30]; exact b29_a20
    clear b29_a20 w29_a24 w29_1594 w29_1590 w29_17c w29_178 w29_84 w29_80 w29_7c y4_29 y0_29
    -- 0x17C: branch, taken
    obtain ⟨n31, d31, u31⟩ := s30.taken E30.self 0x184 sv_at_17c
      (by decide) (by rw [g30_10, s30.zero]; rfl)
    have s31 : St n31.mem SV n31 0x184 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
    have m31 : n31.mem = n30.mem := u31.mem
    have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
    have t31 : Steps n0 n31 := t30.trans (.single d31)
    have fR31 : ∀ x, SvR B x → n31.mem x = n0.mem x := fun x hx => (fr31 x hx).trans (fR30 x hx)
    have E31 : SvCode n31.mem := E30.fr F fr31
    have V31 : SvSaves B n31.mem v := V30.same m31
    have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, g30_2]
    have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, g30_3]
    have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, g30_4]
    have g31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u31.regs, g30_8]
    have g31_9 : reg n31 (9 : Fin 32) = cp := by rw [u31.regs, g30_9]
    have g31_10 : reg n31 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u31.regs, g30_10]
    have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, g30_18]
    have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, g30_19]
    have g31_20 : reg n31 (20 : Fin 32) = bl16 := by rw [u31.regs, g30_20]
    have g31_21 : reg n31 (21 : Fin 32) = lp := by rw [u31.regs, g30_21]
    have g31_22 : reg n31 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u31.regs, g30_22]
    have g31_23 : reg n31 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u31.regs, g30_23]
    have g31_24 : reg n31 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u31.regs, g30_24]
    have g31_25 : reg n31 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u31.regs, g30_25]
    have g31_26 : reg n31 (26 : Fin 32) = ll := by rw [u31.regs, g30_26]
    have g31_27 : reg n31 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u31.regs, g30_27]
    have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m31]; exact w30_7c
    have w31_80 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m31]; exact w30_80
    have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m31]; exact w30_84
    have w31_178 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m31]; exact w30_178
    have w31_17c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m31]; exact w30_17c
    have w31_a24 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = 0 := by rw [m31]; exact w30_a24
    have w31_1590 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m31]; exact w30_1590
    have w31_1594 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m31]; exact w30_1594
    have b31_a20 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m31]; exact b30_a20
    clear b30_a20 w30_1594 w30_1590 w30_a24 w30_17c w30_178 w30_84 w30_80 w30_7c g30_10 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30
    -- 0x184: lw
    obtain ⟨n32, d32, u32⟩ := s31.lw E31.self sv_at_184 (off' := 0x188) (by decide)
      (by rw [g31_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s32 : St n32.mem SV n32 0x188 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
    have m32 : n32.mem = n31.mem := u32.mem
    have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
    have t32 : Steps n0 n32 := t31.trans (.single d32)
    have fR32 : ∀ x, SvR B x → n32.mem x = n0.mem x := fun x hx => (fr32 x hx).trans (fR31 x hx)
    have E32 : SvCode n32.mem := E31.fr F fr32
    have V32 : SvSaves B n32.mem v := V31.same m32
    have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_2]
    have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_3]
    have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_4]
    have g32_8 : reg n32 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_8]
    have g32_9 : reg n32 (9 : Fin 32) = cp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_9]
    have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, upd_ne (by decide) (by decide), g31_18]
    have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_19]
    have g32_20 : reg n32 (20 : Fin 32) = bl16 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_20]
    have g32_21 : reg n32 (21 : Fin 32) = lp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_21]
    have g32_22 : reg n32 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_22]
    have g32_23 : reg n32 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u32.regs, upd_ne (by decide) (by decide), g31_23]
    have g32_24 : reg n32 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u32.regs, upd_ne (by decide) (by decide), g31_24]
    have g32_25 : reg n32 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_25]
    have g32_26 : reg n32 (26 : Fin 32) = ll := by rw [u32.regs, upd_ne (by decide) (by decide), g31_26]
    have g32_27 : reg n32 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_27]
    have g32_10 : reg n32 a0 = 0 := by
      rw [u32.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g31_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr, w31_a24]
    have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m32]; exact w31_7c
    have w32_80 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m32]; exact w31_80
    have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m32]; exact w31_84
    have w32_178 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m32]; exact w31_178
    have w32_17c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m32]; exact w31_17c
    have w32_a24 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = 0 := by rw [m32]; exact w31_a24
    have w32_1590 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m32]; exact w31_1590
    have w32_1594 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m32]; exact w31_1594
    have b32_a20 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m32]; exact b31_a20
    clear b31_a20 w31_1594 w31_1590 w31_a24 w31_17c w31_178 w31_84 w31_80 w31_7c g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_10 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
    -- 0x188: branch, taken
    obtain ⟨n33, d33, u33⟩ := s32.taken E32.self 0x1C4 sv_at_188
      (by decide) (by rw [g32_10, s32.zero]; rfl)
    have s33 : St n33.mem SV n33 0x1C4 (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
    have m33 : n33.mem = n32.mem := u33.mem
    have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
    have t33 : Steps n0 n33 := t32.trans (.single d33)
    have fR33 : ∀ x, SvR B x → n33.mem x = n0.mem x := fun x hx => (fr33 x hx).trans (fR32 x hx)
    have E33 : SvCode n33.mem := E32.fr F fr33
    have V33 : SvSaves B n33.mem v := V32.same m33
    have g33_2 : reg n33 sp = B + 0x21A0 := by rw [u33.regs, g32_2]
    have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u33.regs, g32_3]
    have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u33.regs, g32_4]
    have g33_8 : reg n33 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u33.regs, g32_8]
    have g33_9 : reg n33 (9 : Fin 32) = cp := by rw [u33.regs, g32_9]
    have g33_10 : reg n33 a0 = 0 := by rw [u33.regs, g32_10]
    have g33_18 : reg n33 (18 : Fin 32) = out := by rw [u33.regs, g32_18]
    have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [u33.regs, g32_19]
    have g33_20 : reg n33 (20 : Fin 32) = bl16 := by rw [u33.regs, g32_20]
    have g33_21 : reg n33 (21 : Fin 32) = lp := by rw [u33.regs, g32_21]
    have g33_22 : reg n33 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u33.regs, g32_22]
    have g33_23 : reg n33 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u33.regs, g32_23]
    have g33_24 : reg n33 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u33.regs, g32_24]
    have g33_25 : reg n33 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u33.regs, g32_25]
    have g33_26 : reg n33 (26 : Fin 32) = ll := by rw [u33.regs, g32_26]
    have g33_27 : reg n33 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u33.regs, g32_27]
    have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m33]; exact w32_7c
    have w33_80 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m33]; exact w32_80
    have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m33]; exact w32_84
    have w33_178 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m33]; exact w32_178
    have w33_17c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m33]; exact w32_17c
    have w33_a24 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = 0 := by rw [m33]; exact w32_a24
    have w33_1590 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m33]; exact w32_1590
    have w33_1594 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m33]; exact w32_1594
    have b33_a20 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m33]; exact b32_a20
    clear b32_a20 w32_1594 w32_1590 w32_a24 w32_17c w32_178 w32_84 w32_80 w32_7c g32_10 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
    -- 0x1C4
    obtain ⟨n34, c34, u34⟩ := s33.block svL21c4 E33.self svL21c4_end
      ⟨trivial, trivial⟩
    have m34 : n34.mem = n33.mem := u34.mem
    have s34 : St n34.mem SV n34 0x1C6 (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
    have rb34 : ∀ q, reg n34 q = (runBlock svL21c4 (n33.mem, reg n33)).2 q := fun q => by rw [u34.regs]
    have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
    have t34 : Steps n0 n34 := t33.trans c34
    have fR34 : ∀ x, SvR B x → n34.mem x = n0.mem x := fun x hx => (fr34 x hx).trans (fR33 x hx)
    have E34 : SvCode n34.mem := E33.fr F fr34
    have V34 : SvSaves B n34.mem v := V33.same m34
    have g34_2 : reg n34 sp = B + 0x21A0 := by
      rw [rb34, runBlock_reg _ _ _ sp s33.zero (by decide), g33_2]
    have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb34, runBlock_reg _ _ _ (3 : Fin 32) s33.zero (by decide), g33_3]
    have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb34, runBlock_reg _ _ _ (4 : Fin 32) s33.zero (by decide), g33_4]
    have g34_8 : reg n34 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
      rw [rb34, runBlock_reg _ _ _ (8 : Fin 32) s33.zero (by decide), g33_8]
    have g34_9 : reg n34 (9 : Fin 32) = cp := by
      rw [rb34, runBlock_reg _ _ _ (9 : Fin 32) s33.zero (by decide), g33_9]
    have g34_10 : reg n34 a0 = 0 := by
      rw [rb34, runBlock_reg _ _ _ a0 s33.zero (by decide), g33_10]
    have g34_18 : reg n34 (18 : Fin 32) = out := by
      rw [rb34, runBlock_reg _ _ _ (18 : Fin 32) s33.zero (by decide), g33_18]
    have g34_19 : reg n34 (19 : Fin 32) = bp := by
      rw [rb34, runBlock_reg _ _ _ (19 : Fin 32) s33.zero (by decide), g33_19]
    have g34_21 : reg n34 (21 : Fin 32) = lp := by
      rw [rb34, runBlock_reg _ _ _ (21 : Fin 32) s33.zero (by decide), g33_21]
    have g34_22 : reg n34 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by
      rw [rb34, runBlock_reg _ _ _ (22 : Fin 32) s33.zero (by decide), g33_22]
    have g34_23 : reg n34 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by
      rw [rb34, runBlock_reg _ _ _ (23 : Fin 32) s33.zero (by decide), g33_23]
    have g34_24 : reg n34 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by
      rw [rb34, runBlock_reg _ _ _ (24 : Fin 32) s33.zero (by decide), g33_24]
    have g34_25 : reg n34 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by
      rw [rb34, runBlock_reg _ _ _ (25 : Fin 32) s33.zero (by decide), g33_25]
    have g34_26 : reg n34 (26 : Fin 32) = ll := by
      rw [rb34, runBlock_reg _ _ _ (26 : Fin 32) s33.zero (by decide), g33_26]
    have g34_27 : reg n34 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb34, runBlock_reg _ _ _ (27 : Fin 32) s33.zero (by decide), g33_27]
    have g34_20 : reg n34 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by
      rw [rb34]; simp +decide only [runBlock, BInstr.run, svL21c4, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g33_2, g33_3, g33_4, g33_8, g33_9, g33_10, g33_18, g33_19, g33_20, g33_21, g33_22, g33_23, g33_24, g33_25, g33_26, g33_27, s33.zero])
      all_goals first | decide | sv_addr
    have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m34]; exact w33_7c
    have w34_80 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m34]; exact w33_80
    have w34_84 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m34]; exact w33_84
    have w34_178 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m34]; exact w33_178
    have w34_17c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m34]; exact w33_17c
    have w34_a24 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = 0 := by rw [m34]; exact w33_a24
    have w34_1590 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m34]; exact w33_1590
    have w34_1594 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m34]; exact w33_1594
    have b34_a20 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m34]; exact b33_a20
    clear b33_a20 w33_1594 w33_1590 w33_a24 w33_17c w33_178 w33_84 w33_80 w33_7c g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_10 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 m33 s33 u33 d33
    -- 0x1C6: j
    obtain ⟨n35, d35, u35⟩ := s34.jump E34.self sv_at_1c6 (off' := 0x966) (by decide)
      (by rw [s34.pc]; decide)
    have s35 : St n35.mem SV n35 0x966 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
    have m35 : n35.mem = n34.mem := u35.mem
    have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
    have t35 : Steps n0 n35 := t34.trans (.single d35)
    have fR35 : ∀ x, SvR B x → n35.mem x = n0.mem x := fun x hx => (fr35 x hx).trans (fR34 x hx)
    have E35 : SvCode n35.mem := E34.fr F fr35
    have V35 : SvSaves B n35.mem v := V34.same m35
    have g35_2 : reg n35 sp = B + 0x21A0 := by rw [u35.regs, g34_2]
    have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u35.regs, g34_3]
    have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u35.regs, g34_4]
    have g35_8 : reg n35 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u35.regs, g34_8]
    have g35_9 : reg n35 (9 : Fin 32) = cp := by rw [u35.regs, g34_9]
    have g35_10 : reg n35 a0 = 0 := by rw [u35.regs, g34_10]
    have g35_18 : reg n35 (18 : Fin 32) = out := by rw [u35.regs, g34_18]
    have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [u35.regs, g34_19]
    have g35_20 : reg n35 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u35.regs, g34_20]
    have g35_21 : reg n35 (21 : Fin 32) = lp := by rw [u35.regs, g34_21]
    have g35_22 : reg n35 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u35.regs, g34_22]
    have g35_23 : reg n35 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u35.regs, g34_23]
    have g35_24 : reg n35 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u35.regs, g34_24]
    have g35_25 : reg n35 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u35.regs, g34_25]
    have g35_26 : reg n35 (26 : Fin 32) = ll := by rw [u35.regs, g34_26]
    have g35_27 : reg n35 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u35.regs, g34_27]
    have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m35]; exact w34_7c
    have w35_80 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m35]; exact w34_80
    have w35_84 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m35]; exact w34_84
    have w35_178 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m35]; exact w34_178
    have w35_17c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m35]; exact w34_17c
    have w35_a24 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = 0 := by rw [m35]; exact w34_a24
    have w35_1590 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m35]; exact w34_1590
    have w35_1594 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m35]; exact w34_1594
    have b35_a20 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m35]; exact b34_a20
    clear b34_a20 w34_1594 w34_1590 w34_a24 w34_17c w34_178 w34_84 w34_80 w34_7c g34_20 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_19 g34_18 g34_10 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 rb34 s34 m34 u34 c34
    exact .inl ⟨(fun ⟨tl1', h0', tl8', h1', tl16', h2', bp16', bl16', h3', h4', tl29', h5', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr8] at h1'; cases h1'; rw [hr16] at h2'; cases h2'; rw [hr16b] at h3'; cases h3'; rw [hr29] at h5'; cases h5'), sv_fail F E35 s35 t35 fR35 V35 hret g35_2 g35_18 hO g35_3 g35_4⟩
  · rw [hr29] at R29
    obtain ⟨y0_29, -⟩ := R29
    have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := (K29.w32 (by decide) (by decide)).trans w28_7c
    have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K29.w32 (by decide) (by decide)).trans w28_80
    have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K29.w32 (by decide) (by decide)).trans w28_84
    have w29_178 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := (K29.w32 (by decide) (by decide)).trans w28_178
    have w29_17c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := (K29.w32 (by decide) (by decide)).trans w28_17c
    have w29_1590 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K29.w32 (by decide) (by decide)).trans w28_1590
    have w29_1594 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K29.w32 (by decide) (by decide)).trans w28_1594
    have b29_a20 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := y0_29
    clear b28_a30 w28_1594 w28_1590 w28_a2c w28_a28 w28_a24 w28_a20 w28_184 w28_180 w28_17c w28_178 w28_84 w28_80 w28_7c g28_12 g28_11 g28_10 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 rb28 s28 m28 u28 c28
    -- 0x178: lbu
    obtain ⟨n30, d30, u30⟩ := s29.lbu E29.self sv_at_178 (off' := 0x17C) (by decide)
    have s30 : St n30.mem SV n30 0x17C (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
    have m30 : n30.mem = n29.mem := u30.mem
    have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
    have t30 : Steps n0 n30 := t29.trans (.single d30)
    have fR30 : ∀ x, SvR B x → n30.mem x = n0.mem x := fun x hx => (fr30 x hx).trans (fR29 x hx)
    have E30 : SvCode n30.mem := E29.fr F fr30
    have V30 : SvSaves B n30.mem v := V29.same m30
    have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_2]
    have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_3]
    have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_4]
    have g30_8 : reg n30 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_8]
    have g30_9 : reg n30 (9 : Fin 32) = cp := by rw [u30.regs, upd_ne (by decide) (by decide), g29_9]
    have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, upd_ne (by decide) (by decide), g29_18]
    have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, upd_ne (by decide) (by decide), g29_19]
    have g30_20 : reg n30 (20 : Fin 32) = bl16 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_20]
    have g30_21 : reg n30 (21 : Fin 32) = lp := by rw [u30.regs, upd_ne (by decide) (by decide), g29_21]
    have g30_22 : reg n30 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_22]
    have g30_23 : reg n30 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u30.regs, upd_ne (by decide) (by decide), g29_23]
    have g30_24 : reg n30 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u30.regs, upd_ne (by decide) (by decide), g29_24]
    have g30_25 : reg n30 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_25]
    have g30_26 : reg n30 (26 : Fin 32) = ll := by rw [u30.regs, upd_ne (by decide) (by decide), g29_26]
    have g30_27 : reg n30 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_27]
    have g30_10 : reg n30 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [u30.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g29_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, b29_a20]
    have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m30]; exact w29_7c
    have w30_80 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m30]; exact w29_80
    have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m30]; exact w29_84
    have w30_178 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m30]; exact w29_178
    have w30_17c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m30]; exact w29_17c
    have w30_1590 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m30]; exact w29_1590
    have w30_1594 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m30]; exact w29_1594
    have b30_a20 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := by rw [m30]; exact b29_a20
    clear b29_a20 w29_1594 w29_1590 w29_17c w29_178 w29_84 w29_80 w29_7c y0_29
    -- 0x17C: branch, not taken
    obtain ⟨n31, d31, u31⟩ := s30.notTaken E30.self 0x17E sv_at_17c
      (by decide) (by rw [g30_10, s30.zero]; decide)
    have s31 : St n31.mem SV n31 0x17E (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
    have m31 : n31.mem = n30.mem := u31.mem
    have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
    have t31 : Steps n0 n31 := t30.trans (.single d31)
    have fR31 : ∀ x, SvR B x → n31.mem x = n0.mem x := fun x hx => (fr31 x hx).trans (fR30 x hx)
    have E31 : SvCode n31.mem := E30.fr F fr31
    have V31 : SvSaves B n31.mem v := V30.same m31
    have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, g30_2]
    have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, g30_3]
    have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, g30_4]
    have g31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u31.regs, g30_8]
    have g31_9 : reg n31 (9 : Fin 32) = cp := by rw [u31.regs, g30_9]
    have g31_10 : reg n31 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u31.regs, g30_10]
    have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, g30_18]
    have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, g30_19]
    have g31_20 : reg n31 (20 : Fin 32) = bl16 := by rw [u31.regs, g30_20]
    have g31_21 : reg n31 (21 : Fin 32) = lp := by rw [u31.regs, g30_21]
    have g31_22 : reg n31 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u31.regs, g30_22]
    have g31_23 : reg n31 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u31.regs, g30_23]
    have g31_24 : reg n31 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u31.regs, g30_24]
    have g31_25 : reg n31 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u31.regs, g30_25]
    have g31_26 : reg n31 (26 : Fin 32) = ll := by rw [u31.regs, g30_26]
    have g31_27 : reg n31 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u31.regs, g30_27]
    have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m31]; exact w30_7c
    have w31_80 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m31]; exact w30_80
    have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m31]; exact w30_84
    have w31_178 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m31]; exact w30_178
    have w31_17c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m31]; exact w30_17c
    have w31_1590 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m31]; exact w30_1590
    have w31_1594 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m31]; exact w30_1594
    have b31_a20 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := by rw [m31]; exact b30_a20
    clear b30_a20 w30_1594 w30_1590 w30_17c w30_178 w30_84 w30_80 w30_7c g30_10 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30
    -- 0x17E: lbu
    obtain ⟨n32, d32, u32⟩ := s31.lbu E31.self sv_at_17e (off' := 0x182) (by decide)
    have s32 : St n32.mem SV n32 0x182 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
    have m32 : n32.mem = n31.mem := u32.mem
    have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
    have t32 : Steps n0 n32 := t31.trans (.single d32)
    have fR32 : ∀ x, SvR B x → n32.mem x = n0.mem x := fun x hx => (fr32 x hx).trans (fR31 x hx)
    have E32 : SvCode n32.mem := E31.fr F fr32
    have V32 : SvSaves B n32.mem v := V31.same m32
    have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_2]
    have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_3]
    have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_4]
    have g32_8 : reg n32 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_8]
    have g32_9 : reg n32 (9 : Fin 32) = cp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_9]
    have g32_10 : reg n32 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_10]
    have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, upd_ne (by decide) (by decide), g31_18]
    have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_19]
    have g32_21 : reg n32 (21 : Fin 32) = lp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_21]
    have g32_22 : reg n32 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_22]
    have g32_23 : reg n32 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u32.regs, upd_ne (by decide) (by decide), g31_23]
    have g32_24 : reg n32 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u32.regs, upd_ne (by decide) (by decide), g31_24]
    have g32_25 : reg n32 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_25]
    have g32_26 : reg n32 (26 : Fin 32) = ll := by rw [u32.regs, upd_ne (by decide) (by decide), g31_26]
    have g32_27 : reg n32 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_27]
    have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m32]; exact w31_7c
    have w32_80 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m32]; exact w31_80
    have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m32]; exact w31_84
    have w32_178 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m32]; exact w31_178
    have w32_17c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m32]; exact w31_17c
    have w32_1590 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m32]; exact w31_1590
    have w32_1594 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m32]; exact w31_1594
    have b32_a20 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := by rw [m32]; exact b31_a20
    clear b31_a20 w31_1594 w31_1590 w31_17c w31_178 w31_84 w31_80 w31_7c g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_10 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
    -- 0x182: j
    obtain ⟨n33, d33, u33⟩ := s32.jump E32.self sv_at_182 (off' := 0x966) (by decide)
      (by rw [s32.pc]; decide)
    have s33 : St n33.mem SV n33 0x966 (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
    have m33 : n33.mem = n32.mem := u33.mem
    have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
    have t33 : Steps n0 n33 := t32.trans (.single d33)
    have fR33 : ∀ x, SvR B x → n33.mem x = n0.mem x := fun x hx => (fr33 x hx).trans (fR32 x hx)
    have E33 : SvCode n33.mem := E32.fr F fr33
    have V33 : SvSaves B n33.mem v := V32.same m33
    have g33_2 : reg n33 sp = B + 0x21A0 := by rw [u33.regs, g32_2]
    have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u33.regs, g32_3]
    have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u33.regs, g32_4]
    have g33_8 : reg n33 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u33.regs, g32_8]
    have g33_9 : reg n33 (9 : Fin 32) = cp := by rw [u33.regs, g32_9]
    have g33_10 : reg n33 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u33.regs, g32_10]
    have g33_18 : reg n33 (18 : Fin 32) = out := by rw [u33.regs, g32_18]
    have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [u33.regs, g32_19]
    have g33_21 : reg n33 (21 : Fin 32) = lp := by rw [u33.regs, g32_21]
    have g33_22 : reg n33 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u33.regs, g32_22]
    have g33_23 : reg n33 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u33.regs, g32_23]
    have g33_24 : reg n33 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u33.regs, g32_24]
    have g33_25 : reg n33 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u33.regs, g32_25]
    have g33_26 : reg n33 (26 : Fin 32) = ll := by rw [u33.regs, g32_26]
    have g33_27 : reg n33 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u33.regs, g32_27]
    have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m33]; exact w32_7c
    have w33_80 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m33]; exact w32_80
    have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m33]; exact w32_84
    have w33_178 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m33]; exact w32_178
    have w33_17c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m33]; exact w32_17c
    have w33_1590 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m33]; exact w32_1590
    have w33_1594 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m33]; exact w32_1594
    have b33_a20 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := by rw [m33]; exact b32_a20
    clear b32_a20 w32_1594 w32_1590 w32_17c w32_178 w32_84 w32_80 w32_7c g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_19 g32_18 g32_10 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
    exact .inl ⟨(fun ⟨tl1', h0', tl8', h1', tl16', h2', bp16', bl16', h3', h4', tl29', h5', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr8] at h1'; cases h1'; rw [hr16] at h2'; cases h2'; rw [hr16b] at h3'; cases h3'; rw [hr29] at h5'; cases h5'), sv_fail F E33 s33 t33 fR33 V33 hret g33_2 g33_18 hO g33_3 g33_4⟩
  rw [hr29] at R29
  obtain ⟨y0_29, y4_29, y8_29, y12_29, y16_29, y20_29, d8_29, d12_29⟩ := R29
  have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := (K29.w32 (by decide) (by decide)).trans w28_7c
  have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K29.w32 (by decide) (by decide)).trans w28_80
  have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K29.w32 (by decide) (by decide)).trans w28_84
  have w29_178 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := (K29.w32 (by decide) (by decide)).trans w28_178
  have w29_17c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := (K29.w32 (by decide) (by decide)).trans w28_17c
  have w29_1590 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K29.w32 (by decide) (by decide)).trans w28_1590
  have w29_1594 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K29.w32 (by decide) (by decide)).trans w28_1594
  have w29_180 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := d8_29
  have w29_184 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := d12_29
  have w29_a24 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := y4_29
  have w29_a28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := y8_29
  have w29_a2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := y12_29
  have w29_a30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := y16_29
  have b29_a20 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := y0_29
  have b29_a34 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := y20_29
  clear b28_a30 w28_1594 w28_1590 w28_a2c w28_a28 w28_a24 w28_a20 w28_184 w28_180 w28_17c w28_178 w28_84 w28_80 w28_7c g28_12 g28_11 g28_10 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 rb28 s28 m28 u28 c28
  -- 0x178: lbu
  obtain ⟨n30, d30, u30⟩ := s29.lbu E29.self sv_at_178 (off' := 0x17C) (by decide)
  have s30 : St n30.mem SV n30 0x17C (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
  have t30 : Steps n0 n30 := t29.trans (.single d30)
  have fR30 : ∀ x, SvR B x → n30.mem x = n0.mem x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.same m30
  have g30_2 : reg n30 sp = B + 0x21A0 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = cp := by rw [u30.regs, upd_ne (by decide) (by decide), g29_9]
  have g30_18 : reg n30 (18 : Fin 32) = out := by rw [u30.regs, upd_ne (by decide) (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by rw [u30.regs, upd_ne (by decide) (by decide), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = bl16 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = lp := by rw [u30.regs, upd_ne (by decide) (by decide), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u30.regs, upd_ne (by decide) (by decide), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u30.regs, upd_ne (by decide) (by decide), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u30.regs, upd_ne (by decide) (by decide), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = ll := by rw [u30.regs, upd_ne (by decide) (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u30.regs, upd_ne (by decide) (by decide), g29_27]
  have g30_10 : reg n30 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [u30.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g29_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, b29_a20]
  have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m30]; exact w29_7c
  have w30_80 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m30]; exact w29_80
  have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m30]; exact w29_84
  have w30_178 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m30]; exact w29_178
  have w30_17c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m30]; exact w29_17c
  have w30_180 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m30]; exact w29_180
  have w30_184 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m30]; exact w29_184
  have w30_a24 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m30]; exact w29_a24
  have w30_a28 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m30]; exact w29_a28
  have w30_a2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m30]; exact w29_a2c
  have w30_a30 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m30]; exact w29_a30
  have w30_1590 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m30]; exact w29_1590
  have w30_1594 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m30]; exact w29_1594
  have b30_a20 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m30]; exact b29_a20
  have b30_a34 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m30]; exact b29_a34
  clear b29_a34 b29_a20 w29_a30 w29_a2c w29_a28 w29_a24 w29_184 w29_180 w29_1594 w29_1590 w29_17c w29_178 w29_84 w29_80 w29_7c d12_29 d8_29 y20_29 y16_29 y12_29 y8_29 y4_29 y0_29 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 K29 rk29 sp29 s29 c29
  -- 0x17C: branch, taken
  obtain ⟨n31, d31, u31⟩ := s30.taken E30.self 0x184 sv_at_17c
    (by decide) (by rw [g30_10, s30.zero]; rfl)
  have s31 : St n31.mem SV n31 0x184 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans (.single d31)
  have fR31 : ∀ x, SvR B x → n31.mem x = n0.mem x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u31.regs, g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = cp := by rw [u31.regs, g30_9]
  have g31_10 : reg n31 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u31.regs, g30_10]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = bl16 := by rw [u31.regs, g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = lp := by rw [u31.regs, g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u31.regs, g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u31.regs, g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u31.regs, g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u31.regs, g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = ll := by rw [u31.regs, g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u31.regs, g30_27]
  have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m31]; exact w30_7c
  have w31_80 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m31]; exact w30_80
  have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m31]; exact w30_84
  have w31_178 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m31]; exact w30_178
  have w31_17c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m31]; exact w30_17c
  have w31_180 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m31]; exact w30_180
  have w31_184 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m31]; exact w30_184
  have w31_a24 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m31]; exact w30_a24
  have w31_a28 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m31]; exact w30_a28
  have w31_a2c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m31]; exact w30_a2c
  have w31_a30 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m31]; exact w30_a30
  have w31_1590 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m31]; exact w30_1590
  have w31_1594 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m31]; exact w30_1594
  have b31_a20 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m31]; exact b30_a20
  have b31_a34 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m31]; exact b30_a34
  clear b30_a34 b30_a20 w30_1594 w30_1590 w30_a30 w30_a2c w30_a28 w30_a24 w30_184 w30_180 w30_17c w30_178 w30_84 w30_80 w30_7c g30_10 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 m30 s30 u30 d30
  -- 0x184: lw
  obtain ⟨n32, d32, u32⟩ := s31.lw E31.self sv_at_184 (off' := 0x188) (by decide)
    (by rw [g31_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s32 : St n32.mem SV n32 0x188 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans (.single d32)
  have fR32 : ∀ x, SvR B x → n32.mem x = n0.mem x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = cp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_9]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, upd_ne (by decide) (by decide), g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = bl16 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = lp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u32.regs, upd_ne (by decide) (by decide), g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u32.regs, upd_ne (by decide) (by decide), g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = ll := by rw [u32.regs, upd_ne (by decide) (by decide), g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_27]
  have g32_10 : reg n32 a0 = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by
    rw [u32.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g31_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr, w31_a24]
  have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m32]; exact w31_7c
  have w32_80 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m32]; exact w31_80
  have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m32]; exact w31_84
  have w32_178 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m32]; exact w31_178
  have w32_17c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m32]; exact w31_17c
  have w32_180 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m32]; exact w31_180
  have w32_184 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m32]; exact w31_184
  have w32_a24 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m32]; exact w31_a24
  have w32_a28 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m32]; exact w31_a28
  have w32_a2c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m32]; exact w31_a2c
  have w32_a30 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m32]; exact w31_a30
  have w32_1590 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m32]; exact w31_1590
  have w32_1594 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m32]; exact w31_1594
  have b32_a20 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m32]; exact b31_a20
  have b32_a34 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m32]; exact b31_a34
  clear b31_a34 b31_a20 w31_1594 w31_1590 w31_a30 w31_a2c w31_a28 w31_a24 w31_184 w31_180 w31_17c w31_178 w31_84 w31_80 w31_7c g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_10 g31_9 g31_8 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
  -- 0x188: branch, not taken
  obtain ⟨n33, d33, u33⟩ := s32.notTaken E32.self 0x18A sv_at_188
    (by decide) (by rw [g32_10, s32.zero]; exact br_beq_f ((cc_in.contentW hr1).ok_ne (opt_ok_elem hr29)))
  have s33 : St n33.mem SV n33 0x18A (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
  have t33 : Steps n0 n33 := t32.trans (.single d33)
  have fR33 : ∀ x, SvR B x → n33.mem x = n0.mem x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.same m33
  have g33_2 : reg n33 sp = B + 0x21A0 := by rw [u33.regs, g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u33.regs, g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u33.regs, g32_4]
  have g33_8 : reg n33 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u33.regs, g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = cp := by rw [u33.regs, g32_9]
  have g33_10 : reg n33 a0 = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [u33.regs, g32_10]
  have g33_18 : reg n33 (18 : Fin 32) = out := by rw [u33.regs, g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [u33.regs, g32_19]
  have g33_20 : reg n33 (20 : Fin 32) = bl16 := by rw [u33.regs, g32_20]
  have g33_21 : reg n33 (21 : Fin 32) = lp := by rw [u33.regs, g32_21]
  have g33_22 : reg n33 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u33.regs, g32_22]
  have g33_23 : reg n33 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u33.regs, g32_23]
  have g33_24 : reg n33 (24 : Fin 32) = (cp) + BitVec.ofNat 32 tl1.header := by rw [u33.regs, g32_24]
  have g33_25 : reg n33 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u33.regs, g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = ll := by rw [u33.regs, g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u33.regs, g32_27]
  have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m33]; exact w32_7c
  have w33_80 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m33]; exact w32_80
  have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m33]; exact w32_84
  have w33_178 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m33]; exact w32_178
  have w33_17c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m33]; exact w32_17c
  have w33_180 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m33]; exact w32_180
  have w33_184 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m33]; exact w32_184
  have w33_a24 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m33]; exact w32_a24
  have w33_a28 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m33]; exact w32_a28
  have w33_a2c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m33]; exact w32_a2c
  have w33_a30 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m33]; exact w32_a30
  have w33_1590 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m33]; exact w32_1590
  have w33_1594 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m33]; exact w32_1594
  have b33_a20 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m33]; exact b32_a20
  have b33_a34 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m33]; exact b32_a34
  clear b32_a34 b32_a20 w32_1594 w32_1590 w32_a30 w32_a2c w32_a28 w32_a24 w32_184 w32_180 w32_17c w32_178 w32_84 w32_80 w32_7c g32_10 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
  -- 0x18A
  obtain ⟨n34, c34, u34⟩ := s33.block svL218a E33.self svL218a_end
    ⟨trivial, trivial⟩
  have m34 : n34.mem = n33.mem := u34.mem
  have s34 : St n34.mem SV n34 0x18C (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
  have rb34 : ∀ q, reg n34 q = (runBlock svL218a (n33.mem, reg n33)).2 q := fun q => by rw [u34.regs]
  have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
  have t34 : Steps n0 n34 := t33.trans c34
  have fR34 : ∀ x, SvR B x → n34.mem x = n0.mem x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.same m34
  have g34_2 : reg n34 sp = B + 0x21A0 := by
    rw [rb34, runBlock_reg _ _ _ sp s33.zero (by decide), g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb34, runBlock_reg _ _ _ (3 : Fin 32) s33.zero (by decide), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb34, runBlock_reg _ _ _ (4 : Fin 32) s33.zero (by decide), g33_4]
  have g34_8 : reg n34 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb34, runBlock_reg _ _ _ (8 : Fin 32) s33.zero (by decide), g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = cp := by
    rw [rb34, runBlock_reg _ _ _ (9 : Fin 32) s33.zero (by decide), g33_9]
  have g34_10 : reg n34 a0 = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by
    rw [rb34, runBlock_reg _ _ _ a0 s33.zero (by decide), g33_10]
  have g34_18 : reg n34 (18 : Fin 32) = out := by
    rw [rb34, runBlock_reg _ _ _ (18 : Fin 32) s33.zero (by decide), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by
    rw [rb34, runBlock_reg _ _ _ (19 : Fin 32) s33.zero (by decide), g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = bl16 := by
    rw [rb34, runBlock_reg _ _ _ (20 : Fin 32) s33.zero (by decide), g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = lp := by
    rw [rb34, runBlock_reg _ _ _ (21 : Fin 32) s33.zero (by decide), g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb34, runBlock_reg _ _ _ (22 : Fin 32) s33.zero (by decide), g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by
    rw [rb34, runBlock_reg _ _ _ (23 : Fin 32) s33.zero (by decide), g33_23]
  have g34_25 : reg n34 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by
    rw [rb34, runBlock_reg _ _ _ (25 : Fin 32) s33.zero (by decide), g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = ll := by
    rw [rb34, runBlock_reg _ _ _ (26 : Fin 32) s33.zero (by decide), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb34, runBlock_reg _ _ _ (27 : Fin 32) s33.zero (by decide), g33_27]
  have g34_24 : reg n34 (24 : Fin 32) = bl16 := by
    rw [rb34]; simp +decide only [runBlock, BInstr.run, svL218a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g33_2, g33_3, g33_4, g33_8, g33_9, g33_10, g33_18, g33_19, g33_20, g33_21, g33_22, g33_23, g33_24, g33_25, g33_26, g33_27, s33.zero])
    all_goals first | decide | sv_addr
  have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m34]; exact w33_7c
  have w34_80 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m34]; exact w33_80
  have w34_84 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m34]; exact w33_84
  have w34_178 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m34]; exact w33_178
  have w34_17c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m34]; exact w33_17c
  have w34_180 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m34]; exact w33_180
  have w34_184 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m34]; exact w33_184
  have w34_a24 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m34]; exact w33_a24
  have w34_a28 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m34]; exact w33_a28
  have w34_a2c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m34]; exact w33_a2c
  have w34_a30 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m34]; exact w33_a30
  have w34_1590 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m34]; exact w33_1590
  have w34_1594 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m34]; exact w33_1594
  have b34_a20 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m34]; exact b33_a20
  have b34_a34 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m34]; exact b33_a34
  clear b33_a34 b33_a20 w33_1594 w33_1590 w33_a30 w33_a2c w33_a28 w33_a24 w33_184 w33_180 w33_17c w33_178 w33_84 w33_80 w33_7c g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_10 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 m33 s33 u33 d33
  -- 0x18C: sw
  obtain ⟨n35, d35, s35, fr35, K35, W35, rg35⟩ := sv_sw F E34 s34 sv_at_18c (off' := 0x18E) (c := 0x78)
    (by decide) (by rw [g34_2]; sv_addr) (by decide) (by decide)
  have t35 : Steps n0 n35 := t34.trans d35
  have fR35 : ∀ x, SvR B x → n35.mem x = n0.mem x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.keep K35 (by decide)
  have g35_2 : reg n35 sp = B + 0x21A0 := by rw [rg35 sp, g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg35 (3 : Fin 32), g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg35 (4 : Fin 32), g34_4]
  have g35_8 : reg n35 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg35 (8 : Fin 32), g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = cp := by rw [rg35 (9 : Fin 32), g34_9]
  have g35_10 : reg n35 a0 = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [rg35 a0, g34_10]
  have g35_18 : reg n35 (18 : Fin 32) = out := by rw [rg35 (18 : Fin 32), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [rg35 (19 : Fin 32), g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = bl16 := by rw [rg35 (20 : Fin 32), g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = lp := by rw [rg35 (21 : Fin 32), g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg35 (22 : Fin 32), g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rg35 (23 : Fin 32), g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = bl16 := by rw [rg35 (24 : Fin 32), g34_24]
  have g35_25 : reg n35 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rg35 (25 : Fin 32), g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = ll := by rw [rg35 (26 : Fin 32), g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg35 (27 : Fin 32), g34_27]
  have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := (K35.w32 (by decide) (by decide)).trans w34_7c
  have w35_80 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K35.w32 (by decide) (by decide)).trans w34_80
  have w35_84 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K35.w32 (by decide) (by decide)).trans w34_84
  have w35_178 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := (K35.w32 (by decide) (by decide)).trans w34_178
  have w35_17c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := (K35.w32 (by decide) (by decide)).trans w34_17c
  have w35_180 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := (K35.w32 (by decide) (by decide)).trans w34_180
  have w35_184 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := (K35.w32 (by decide) (by decide)).trans w34_184
  have w35_a24 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := (K35.w32 (by decide) (by decide)).trans w34_a24
  have w35_a28 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := (K35.w32 (by decide) (by decide)).trans w34_a28
  have w35_a2c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := (K35.w32 (by decide) (by decide)).trans w34_a2c
  have w35_a30 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := (K35.w32 (by decide) (by decide)).trans w34_a30
  have w35_1590 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K35.w32 (by decide) (by decide)).trans w34_1590
  have w35_1594 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K35.w32 (by decide) (by decide)).trans w34_1594
  have b35_a20 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := (K35.b8 (by decide) (by decide)).trans b34_a20
  have b35_a34 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := (K35.b8 (by decide) (by decide)).trans b34_a34
  have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [W35, g34_8]
  clear b34_a34 b34_a20 w34_1594 w34_1590 w34_a30 w34_a2c w34_a28 w34_a24 w34_184 w34_180 w34_17c w34_178 w34_84 w34_80 w34_7c g34_24 g34_27 g34_26 g34_25 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_10 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 rb34 s34 m34 u34 c34
  -- 0x18E: lw
  obtain ⟨n36, d36, u36⟩ := s35.lw E35.self sv_at_18e (off' := 0x192) (by decide)
    (by rw [g35_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s36 : St n36.mem SV n36 0x192 (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
  have m36 : n36.mem = n35.mem := u36.mem
  have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
  have t36 : Steps n0 n36 := t35.trans (.single d36)
  have fR36 : ∀ x, SvR B x → n36.mem x = n0.mem x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.same m36
  have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_4]
  have g36_8 : reg n36 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_8]
  have g36_9 : reg n36 (9 : Fin 32) = cp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_9]
  have g36_10 : reg n36 a0 = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [u36.regs, upd_ne (by decide) (by decide), g35_10]
  have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, upd_ne (by decide) (by decide), g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_19]
  have g36_20 : reg n36 (20 : Fin 32) = bl16 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_20]
  have g36_21 : reg n36 (21 : Fin 32) = lp := by rw [u36.regs, upd_ne (by decide) (by decide), g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u36.regs, upd_ne (by decide) (by decide), g35_23]
  have g36_24 : reg n36 (24 : Fin 32) = bl16 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_24]
  have g36_25 : reg n36 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u36.regs, upd_ne (by decide) (by decide), g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = ll := by rw [u36.regs, upd_ne (by decide) (by decide), g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u36.regs, upd_ne (by decide) (by decide), g35_27]
  have g36_11 : reg n36 a1 = BitVec.ofNat 32 tl29.len := by
    rw [u36.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g35_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr, w35_a28]
  have w36_78 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m36]; exact w35_78
  have w36_7c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m36]; exact w35_7c
  have w36_80 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m36]; exact w35_80
  have w36_84 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m36]; exact w35_84
  have w36_178 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m36]; exact w35_178
  have w36_17c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m36]; exact w35_17c
  have w36_180 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m36]; exact w35_180
  have w36_184 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m36]; exact w35_184
  have w36_a24 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m36]; exact w35_a24
  have w36_a28 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m36]; exact w35_a28
  have w36_a2c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m36]; exact w35_a2c
  have w36_a30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m36]; exact w35_a30
  have w36_1590 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m36]; exact w35_1590
  have w36_1594 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m36]; exact w35_1594
  have b36_a20 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m36]; exact b35_a20
  have b36_a34 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m36]; exact b35_a34
  clear w35_78 b35_a34 b35_a20 w35_1594 w35_1590 w35_a30 w35_a2c w35_a28 w35_a24 w35_184 w35_180 w35_17c w35_178 w35_84 w35_80 w35_7c g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_10 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 rg35 W35 K35 fr35 s35 d35
  -- 0x192
  obtain ⟨n37, c37, u37⟩ := s36.block svL2192 E36.self svL2192_end
    ⟨trivial, trivial⟩
  have m37 : n37.mem = n36.mem := u37.mem
  have s37 : St n37.mem SV n37 0x194 (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
  have rb37 : ∀ q, reg n37 q = (runBlock svL2192 (n36.mem, reg n36)).2 q := fun q => by rw [u37.regs]
  have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
  have t37 : Steps n0 n37 := t36.trans c37
  have fR37 : ∀ x, SvR B x → n37.mem x = n0.mem x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : SvCode n37.mem := E36.fr F fr37
  have V37 : SvSaves B n37.mem v := V36.same m37
  have g37_2 : reg n37 sp = B + 0x21A0 := by
    rw [rb37, runBlock_reg _ _ _ sp s36.zero (by decide), g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb37, runBlock_reg _ _ _ (3 : Fin 32) s36.zero (by decide), g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb37, runBlock_reg _ _ _ (4 : Fin 32) s36.zero (by decide), g36_4]
  have g37_8 : reg n37 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb37, runBlock_reg _ _ _ (8 : Fin 32) s36.zero (by decide), g36_8]
  have g37_9 : reg n37 (9 : Fin 32) = cp := by
    rw [rb37, runBlock_reg _ _ _ (9 : Fin 32) s36.zero (by decide), g36_9]
  have g37_10 : reg n37 a0 = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by
    rw [rb37, runBlock_reg _ _ _ a0 s36.zero (by decide), g36_10]
  have g37_11 : reg n37 a1 = BitVec.ofNat 32 tl29.len := by
    rw [rb37, runBlock_reg _ _ _ a1 s36.zero (by decide), g36_11]
  have g37_18 : reg n37 (18 : Fin 32) = out := by
    rw [rb37, runBlock_reg _ _ _ (18 : Fin 32) s36.zero (by decide), g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = bp := by
    rw [rb37, runBlock_reg _ _ _ (19 : Fin 32) s36.zero (by decide), g36_19]
  have g37_20 : reg n37 (20 : Fin 32) = bl16 := by
    rw [rb37, runBlock_reg _ _ _ (20 : Fin 32) s36.zero (by decide), g36_20]
  have g37_21 : reg n37 (21 : Fin 32) = lp := by
    rw [rb37, runBlock_reg _ _ _ (21 : Fin 32) s36.zero (by decide), g36_21]
  have g37_22 : reg n37 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb37, runBlock_reg _ _ _ (22 : Fin 32) s36.zero (by decide), g36_22]
  have g37_23 : reg n37 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by
    rw [rb37, runBlock_reg _ _ _ (23 : Fin 32) s36.zero (by decide), g36_23]
  have g37_24 : reg n37 (24 : Fin 32) = bl16 := by
    rw [rb37, runBlock_reg _ _ _ (24 : Fin 32) s36.zero (by decide), g36_24]
  have g37_25 : reg n37 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by
    rw [rb37, runBlock_reg _ _ _ (25 : Fin 32) s36.zero (by decide), g36_25]
  have g37_26 : reg n37 (26 : Fin 32) = ll := by
    rw [rb37, runBlock_reg _ _ _ (26 : Fin 32) s36.zero (by decide), g36_26]
  have g37_27 : reg n37 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb37, runBlock_reg _ _ _ (27 : Fin 32) s36.zero (by decide), g36_27]
  have g37_12 : reg n37 a2 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb37]; simp +decide only [runBlock, BInstr.run, svL2192, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g36_2, g36_3, g36_4, g36_8, g36_9, g36_10, g36_11, g36_18, g36_19, g36_20, g36_21, g36_22, g36_23, g36_24, g36_25, g36_26, g36_27, s36.zero])
    all_goals first | decide | sv_addr
  have w37_78 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m37]; exact w36_78
  have w37_7c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m37]; exact w36_7c
  have w37_80 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m37]; exact w36_80
  have w37_84 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m37]; exact w36_84
  have w37_178 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m37]; exact w36_178
  have w37_17c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m37]; exact w36_17c
  have w37_180 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m37]; exact w36_180
  have w37_184 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m37]; exact w36_184
  have w37_a24 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m37]; exact w36_a24
  have w37_a28 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m37]; exact w36_a28
  have w37_a2c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m37]; exact w36_a2c
  have w37_a30 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m37]; exact w36_a30
  have w37_1590 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m37]; exact w36_1590
  have w37_1594 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m37]; exact w36_1594
  have b37_a20 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m37]; exact b36_a20
  have b37_a34 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m37]; exact b36_a34
  clear b36_a34 b36_a20 w36_1594 w36_1590 w36_a30 w36_a2c w36_a28 w36_a24 w36_184 w36_180 w36_17c w36_178 w36_84 w36_80 w36_7c w36_78 g36_11 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_10 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 m36 s36 u36 d36
  -- 0x194: sw
  obtain ⟨n38, d38, s38, fr38, K38, W38, rg38⟩ := sv_sw F E37 s37 sv_at_194 (off' := 0x196) (c := 0x200)
    (by decide) (by rw [g37_12]; sv_addr) (by decide) (by decide)
  have t38 : Steps n0 n38 := t37.trans d38
  have fR38 : ∀ x, SvR B x → n38.mem x = n0.mem x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : SvCode n38.mem := E37.fr F fr38
  have V38 : SvSaves B n38.mem v := V37.keep K38 (by decide)
  have g38_2 : reg n38 sp = B + 0x21A0 := by rw [rg38 sp, g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg38 (3 : Fin 32), g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg38 (4 : Fin 32), g37_4]
  have g38_8 : reg n38 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg38 (8 : Fin 32), g37_8]
  have g38_9 : reg n38 (9 : Fin 32) = cp := by rw [rg38 (9 : Fin 32), g37_9]
  have g38_10 : reg n38 a0 = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [rg38 a0, g37_10]
  have g38_11 : reg n38 a1 = BitVec.ofNat 32 tl29.len := by rw [rg38 a1, g37_11]
  have g38_12 : reg n38 a2 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by rw [rg38 a2, g37_12]
  have g38_18 : reg n38 (18 : Fin 32) = out := by rw [rg38 (18 : Fin 32), g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [rg38 (19 : Fin 32), g37_19]
  have g38_20 : reg n38 (20 : Fin 32) = bl16 := by rw [rg38 (20 : Fin 32), g37_20]
  have g38_21 : reg n38 (21 : Fin 32) = lp := by rw [rg38 (21 : Fin 32), g37_21]
  have g38_22 : reg n38 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg38 (22 : Fin 32), g37_22]
  have g38_23 : reg n38 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rg38 (23 : Fin 32), g37_23]
  have g38_24 : reg n38 (24 : Fin 32) = bl16 := by rw [rg38 (24 : Fin 32), g37_24]
  have g38_25 : reg n38 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rg38 (25 : Fin 32), g37_25]
  have g38_26 : reg n38 (26 : Fin 32) = ll := by rw [rg38 (26 : Fin 32), g37_26]
  have g38_27 : reg n38 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg38 (27 : Fin 32), g37_27]
  have w38_78 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := (K38.w32 (by decide) (by decide)).trans w37_78
  have w38_7c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := (K38.w32 (by decide) (by decide)).trans w37_7c
  have w38_80 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K38.w32 (by decide) (by decide)).trans w37_80
  have w38_84 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K38.w32 (by decide) (by decide)).trans w37_84
  have w38_178 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := (K38.w32 (by decide) (by decide)).trans w37_178
  have w38_17c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := (K38.w32 (by decide) (by decide)).trans w37_17c
  have w38_180 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := (K38.w32 (by decide) (by decide)).trans w37_180
  have w38_184 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := (K38.w32 (by decide) (by decide)).trans w37_184
  have w38_a24 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := (K38.w32 (by decide) (by decide)).trans w37_a24
  have w38_a28 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := (K38.w32 (by decide) (by decide)).trans w37_a28
  have w38_a2c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := (K38.w32 (by decide) (by decide)).trans w37_a2c
  have w38_a30 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := (K38.w32 (by decide) (by decide)).trans w37_a30
  have w38_1590 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K38.w32 (by decide) (by decide)).trans w37_1590
  have w38_1594 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K38.w32 (by decide) (by decide)).trans w37_1594
  have b38_a20 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := (K38.b8 (by decide) (by decide)).trans b37_a20
  have b38_a34 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := (K38.b8 (by decide) (by decide)).trans b37_a34
  have w38_200 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [W38, g37_10]
  clear b37_a34 b37_a20 w37_1594 w37_1590 w37_a30 w37_a2c w37_a28 w37_a24 w37_184 w37_180 w37_17c w37_178 w37_84 w37_80 w37_7c w37_78 g37_12 g37_27 g37_26 g37_25 g37_24 g37_23 g37_22 g37_21 g37_20 g37_19 g37_18 g37_11 g37_10 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 rb37 s37 m37 u37 c37
  -- 0x196: sw
  obtain ⟨n39, d39, s39, fr39, K39, W39, rg39⟩ := sv_sw F E38 s38 sv_at_196 (off' := 0x198) (c := 0x204)
    (by decide) (by rw [g38_12]; sv_addr) (by decide) (by decide)
  have t39 : Steps n0 n39 := t38.trans d39
  have fR39 : ∀ x, SvR B x → n39.mem x = n0.mem x := fun x hx => (fr39 x hx).trans (fR38 x hx)
  have E39 : SvCode n39.mem := E38.fr F fr39
  have V39 : SvSaves B n39.mem v := V38.keep K39 (by decide)
  have g39_2 : reg n39 sp = B + 0x21A0 := by rw [rg39 sp, g38_2]
  have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg39 (3 : Fin 32), g38_3]
  have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg39 (4 : Fin 32), g38_4]
  have g39_8 : reg n39 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg39 (8 : Fin 32), g38_8]
  have g39_9 : reg n39 (9 : Fin 32) = cp := by rw [rg39 (9 : Fin 32), g38_9]
  have g39_10 : reg n39 a0 = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [rg39 a0, g38_10]
  have g39_11 : reg n39 a1 = BitVec.ofNat 32 tl29.len := by rw [rg39 a1, g38_11]
  have g39_12 : reg n39 a2 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by rw [rg39 a2, g38_12]
  have g39_18 : reg n39 (18 : Fin 32) = out := by rw [rg39 (18 : Fin 32), g38_18]
  have g39_19 : reg n39 (19 : Fin 32) = bp := by rw [rg39 (19 : Fin 32), g38_19]
  have g39_20 : reg n39 (20 : Fin 32) = bl16 := by rw [rg39 (20 : Fin 32), g38_20]
  have g39_21 : reg n39 (21 : Fin 32) = lp := by rw [rg39 (21 : Fin 32), g38_21]
  have g39_22 : reg n39 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg39 (22 : Fin 32), g38_22]
  have g39_23 : reg n39 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rg39 (23 : Fin 32), g38_23]
  have g39_24 : reg n39 (24 : Fin 32) = bl16 := by rw [rg39 (24 : Fin 32), g38_24]
  have g39_25 : reg n39 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rg39 (25 : Fin 32), g38_25]
  have g39_26 : reg n39 (26 : Fin 32) = ll := by rw [rg39 (26 : Fin 32), g38_26]
  have g39_27 : reg n39 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg39 (27 : Fin 32), g38_27]
  have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := (K39.w32 (by decide) (by decide)).trans w38_78
  have w39_7c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := (K39.w32 (by decide) (by decide)).trans w38_7c
  have w39_80 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K39.w32 (by decide) (by decide)).trans w38_80
  have w39_84 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K39.w32 (by decide) (by decide)).trans w38_84
  have w39_178 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := (K39.w32 (by decide) (by decide)).trans w38_178
  have w39_17c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := (K39.w32 (by decide) (by decide)).trans w38_17c
  have w39_180 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := (K39.w32 (by decide) (by decide)).trans w38_180
  have w39_184 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := (K39.w32 (by decide) (by decide)).trans w38_184
  have w39_200 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := (K39.w32 (by decide) (by decide)).trans w38_200
  have w39_a24 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := (K39.w32 (by decide) (by decide)).trans w38_a24
  have w39_a28 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := (K39.w32 (by decide) (by decide)).trans w38_a28
  have w39_a2c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := (K39.w32 (by decide) (by decide)).trans w38_a2c
  have w39_a30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := (K39.w32 (by decide) (by decide)).trans w38_a30
  have w39_1590 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K39.w32 (by decide) (by decide)).trans w38_1590
  have w39_1594 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K39.w32 (by decide) (by decide)).trans w38_1594
  have b39_a20 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := (K39.b8 (by decide) (by decide)).trans b38_a20
  have b39_a34 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := (K39.b8 (by decide) (by decide)).trans b38_a34
  have w39_204 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := by rw [W39, g38_11]
  clear w38_200 b38_a34 b38_a20 w38_1594 w38_1590 w38_a30 w38_a2c w38_a28 w38_a24 w38_184 w38_180 w38_17c w38_178 w38_84 w38_80 w38_7c w38_78 g38_27 g38_26 g38_25 g38_24 g38_23 g38_22 g38_21 g38_20 g38_19 g38_18 g38_12 g38_11 g38_10 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 rg38 W38 K38 fr38 s38 d38
  -- 0x198: sw
  obtain ⟨n40, d40, s40, fr40, K40, W40, rg40⟩ := sv_sw F E39 s39 sv_at_198 (off' := 0x19A) (c := 0x208)
    (by decide) (by rw [g39_12]; sv_addr) (by decide) (by decide)
  have t40 : Steps n0 n40 := t39.trans d40
  have fR40 : ∀ x, SvR B x → n40.mem x = n0.mem x := fun x hx => (fr40 x hx).trans (fR39 x hx)
  have E40 : SvCode n40.mem := E39.fr F fr40
  have V40 : SvSaves B n40.mem v := V39.keep K40 (by decide)
  have g40_2 : reg n40 sp = B + 0x21A0 := by rw [rg40 sp, g39_2]
  have g40_3 : reg n40 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg40 (3 : Fin 32), g39_3]
  have g40_4 : reg n40 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg40 (4 : Fin 32), g39_4]
  have g40_8 : reg n40 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg40 (8 : Fin 32), g39_8]
  have g40_9 : reg n40 (9 : Fin 32) = cp := by rw [rg40 (9 : Fin 32), g39_9]
  have g40_10 : reg n40 a0 = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [rg40 a0, g39_10]
  have g40_11 : reg n40 a1 = BitVec.ofNat 32 tl29.len := by rw [rg40 a1, g39_11]
  have g40_12 : reg n40 a2 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by rw [rg40 a2, g39_12]
  have g40_18 : reg n40 (18 : Fin 32) = out := by rw [rg40 (18 : Fin 32), g39_18]
  have g40_19 : reg n40 (19 : Fin 32) = bp := by rw [rg40 (19 : Fin 32), g39_19]
  have g40_20 : reg n40 (20 : Fin 32) = bl16 := by rw [rg40 (20 : Fin 32), g39_20]
  have g40_21 : reg n40 (21 : Fin 32) = lp := by rw [rg40 (21 : Fin 32), g39_21]
  have g40_22 : reg n40 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg40 (22 : Fin 32), g39_22]
  have g40_23 : reg n40 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rg40 (23 : Fin 32), g39_23]
  have g40_24 : reg n40 (24 : Fin 32) = bl16 := by rw [rg40 (24 : Fin 32), g39_24]
  have g40_25 : reg n40 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rg40 (25 : Fin 32), g39_25]
  have g40_26 : reg n40 (26 : Fin 32) = ll := by rw [rg40 (26 : Fin 32), g39_26]
  have g40_27 : reg n40 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg40 (27 : Fin 32), g39_27]
  have w40_78 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := (K40.w32 (by decide) (by decide)).trans w39_78
  have w40_7c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := (K40.w32 (by decide) (by decide)).trans w39_7c
  have w40_80 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K40.w32 (by decide) (by decide)).trans w39_80
  have w40_84 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K40.w32 (by decide) (by decide)).trans w39_84
  have w40_178 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := (K40.w32 (by decide) (by decide)).trans w39_178
  have w40_17c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := (K40.w32 (by decide) (by decide)).trans w39_17c
  have w40_180 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := (K40.w32 (by decide) (by decide)).trans w39_180
  have w40_184 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := (K40.w32 (by decide) (by decide)).trans w39_184
  have w40_200 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := (K40.w32 (by decide) (by decide)).trans w39_200
  have w40_204 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := (K40.w32 (by decide) (by decide)).trans w39_204
  have w40_a24 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := (K40.w32 (by decide) (by decide)).trans w39_a24
  have w40_a28 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := (K40.w32 (by decide) (by decide)).trans w39_a28
  have w40_a2c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := (K40.w32 (by decide) (by decide)).trans w39_a2c
  have w40_a30 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := (K40.w32 (by decide) (by decide)).trans w39_a30
  have w40_1590 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K40.w32 (by decide) (by decide)).trans w39_1590
  have w40_1594 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K40.w32 (by decide) (by decide)).trans w39_1594
  have b40_a20 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := (K40.b8 (by decide) (by decide)).trans b39_a20
  have b40_a34 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := (K40.b8 (by decide) (by decide)).trans b39_a34
  have w40_208 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [W40, g39_10]
  clear w39_204 b39_a34 b39_a20 w39_1594 w39_1590 w39_a30 w39_a2c w39_a28 w39_a24 w39_200 w39_184 w39_180 w39_17c w39_178 w39_84 w39_80 w39_7c w39_78 g39_27 g39_26 g39_25 g39_24 g39_23 g39_22 g39_21 g39_20 g39_19 g39_18 g39_12 g39_11 g39_10 g39_9 g39_8 g39_4 g39_3 g39_2 V39 E39 fR39 t39 rg39 W39 K39 fr39 s39 d39
  -- 0x19A: sw
  obtain ⟨n41, d41, s41, fr41, K41, W41, rg41⟩ := sv_sw F E40 s40 sv_at_19a (off' := 0x19C) (c := 0x20C)
    (by decide) (by rw [g40_12]; sv_addr) (by decide) (by decide)
  have t41 : Steps n0 n41 := t40.trans d41
  have fR41 : ∀ x, SvR B x → n41.mem x = n0.mem x := fun x hx => (fr41 x hx).trans (fR40 x hx)
  have E41 : SvCode n41.mem := E40.fr F fr41
  have V41 : SvSaves B n41.mem v := V40.keep K41 (by decide)
  have g41_2 : reg n41 sp = B + 0x21A0 := by rw [rg41 sp, g40_2]
  have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg41 (3 : Fin 32), g40_3]
  have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg41 (4 : Fin 32), g40_4]
  have g41_8 : reg n41 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg41 (8 : Fin 32), g40_8]
  have g41_9 : reg n41 (9 : Fin 32) = cp := by rw [rg41 (9 : Fin 32), g40_9]
  have g41_10 : reg n41 a0 = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [rg41 a0, g40_10]
  have g41_11 : reg n41 a1 = BitVec.ofNat 32 tl29.len := by rw [rg41 a1, g40_11]
  have g41_12 : reg n41 a2 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by rw [rg41 a2, g40_12]
  have g41_18 : reg n41 (18 : Fin 32) = out := by rw [rg41 (18 : Fin 32), g40_18]
  have g41_19 : reg n41 (19 : Fin 32) = bp := by rw [rg41 (19 : Fin 32), g40_19]
  have g41_20 : reg n41 (20 : Fin 32) = bl16 := by rw [rg41 (20 : Fin 32), g40_20]
  have g41_21 : reg n41 (21 : Fin 32) = lp := by rw [rg41 (21 : Fin 32), g40_21]
  have g41_22 : reg n41 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rg41 (22 : Fin 32), g40_22]
  have g41_23 : reg n41 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rg41 (23 : Fin 32), g40_23]
  have g41_24 : reg n41 (24 : Fin 32) = bl16 := by rw [rg41 (24 : Fin 32), g40_24]
  have g41_25 : reg n41 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rg41 (25 : Fin 32), g40_25]
  have g41_26 : reg n41 (26 : Fin 32) = ll := by rw [rg41 (26 : Fin 32), g40_26]
  have g41_27 : reg n41 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg41 (27 : Fin 32), g40_27]
  have w41_78 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := (K41.w32 (by decide) (by decide)).trans w40_78
  have w41_7c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := (K41.w32 (by decide) (by decide)).trans w40_7c
  have w41_80 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K41.w32 (by decide) (by decide)).trans w40_80
  have w41_84 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K41.w32 (by decide) (by decide)).trans w40_84
  have w41_178 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := (K41.w32 (by decide) (by decide)).trans w40_178
  have w41_17c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := (K41.w32 (by decide) (by decide)).trans w40_17c
  have w41_180 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := (K41.w32 (by decide) (by decide)).trans w40_180
  have w41_184 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := (K41.w32 (by decide) (by decide)).trans w40_184
  have w41_200 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := (K41.w32 (by decide) (by decide)).trans w40_200
  have w41_204 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := (K41.w32 (by decide) (by decide)).trans w40_204
  have w41_208 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := (K41.w32 (by decide) (by decide)).trans w40_208
  have w41_a24 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := (K41.w32 (by decide) (by decide)).trans w40_a24
  have w41_a28 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := (K41.w32 (by decide) (by decide)).trans w40_a28
  have w41_a2c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := (K41.w32 (by decide) (by decide)).trans w40_a2c
  have w41_a30 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := (K41.w32 (by decide) (by decide)).trans w40_a30
  have w41_1590 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K41.w32 (by decide) (by decide)).trans w40_1590
  have w41_1594 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K41.w32 (by decide) (by decide)).trans w40_1594
  have b41_a20 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := (K41.b8 (by decide) (by decide)).trans b40_a20
  have b41_a34 : n41.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := (K41.b8 (by decide) (by decide)).trans b40_a34
  have w41_20c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x20C) = BitVec.ofNat 32 tl29.len := by rw [W41, g40_11]
  clear w40_208 b40_a34 b40_a20 w40_1594 w40_1590 w40_a30 w40_a2c w40_a28 w40_a24 w40_204 w40_200 w40_184 w40_180 w40_17c w40_178 w40_84 w40_80 w40_7c w40_78 g40_27 g40_26 g40_25 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_12 g40_11 g40_10 g40_9 g40_8 g40_4 g40_3 g40_2 V40 E40 fR40 t40 rg40 W40 K40 fr40 s40 d40
  -- 0x19C
  obtain ⟨n42, c42, u42⟩ := s41.block svL219c E41.self svL219c_end
    ⟨trivial, trivial, trivial⟩
  have m42 : n42.mem = n41.mem := u42.mem
  have s42 : St n42.mem SV n42 0x1A0 (reg n42) := ⟨u42.pc, rfl, fun _ => rfl⟩
  have rb42 : ∀ q, reg n42 q = (runBlock svL219c (n41.mem, reg n41)).2 q := fun q => by rw [u42.regs]
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
  have g42_8 : reg n42 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb42, runBlock_reg _ _ _ (8 : Fin 32) s41.zero (by decide), g41_8]
  have g42_9 : reg n42 (9 : Fin 32) = cp := by
    rw [rb42, runBlock_reg _ _ _ (9 : Fin 32) s41.zero (by decide), g41_9]
  have g42_12 : reg n42 a2 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb42, runBlock_reg _ _ _ a2 s41.zero (by decide), g41_12]
  have g42_18 : reg n42 (18 : Fin 32) = out := by
    rw [rb42, runBlock_reg _ _ _ (18 : Fin 32) s41.zero (by decide), g41_18]
  have g42_19 : reg n42 (19 : Fin 32) = bp := by
    rw [rb42, runBlock_reg _ _ _ (19 : Fin 32) s41.zero (by decide), g41_19]
  have g42_20 : reg n42 (20 : Fin 32) = bl16 := by
    rw [rb42, runBlock_reg _ _ _ (20 : Fin 32) s41.zero (by decide), g41_20]
  have g42_21 : reg n42 (21 : Fin 32) = lp := by
    rw [rb42, runBlock_reg _ _ _ (21 : Fin 32) s41.zero (by decide), g41_21]
  have g42_22 : reg n42 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb42, runBlock_reg _ _ _ (22 : Fin 32) s41.zero (by decide), g41_22]
  have g42_23 : reg n42 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by
    rw [rb42, runBlock_reg _ _ _ (23 : Fin 32) s41.zero (by decide), g41_23]
  have g42_24 : reg n42 (24 : Fin 32) = bl16 := by
    rw [rb42, runBlock_reg _ _ _ (24 : Fin 32) s41.zero (by decide), g41_24]
  have g42_25 : reg n42 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by
    rw [rb42, runBlock_reg _ _ _ (25 : Fin 32) s41.zero (by decide), g41_25]
  have g42_26 : reg n42 (26 : Fin 32) = ll := by
    rw [rb42, runBlock_reg _ _ _ (26 : Fin 32) s41.zero (by decide), g41_26]
  have g42_27 : reg n42 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb42, runBlock_reg _ _ _ (27 : Fin 32) s41.zero (by decide), g41_27]
  have g42_10 : reg n42 a0 = B + 0x21A0 + BitVec.ofNat 32 0x200 := by
    rw [rb42]; simp +decide only [runBlock, BInstr.run, svL219c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_11, g41_12, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
    all_goals first | decide | sv_addr
  have g42_11 : reg n42 a1 = BitVec.ofNat 32 0x2 := by
    rw [rb42]; simp +decide only [runBlock, BInstr.run, svL219c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g41_2, g41_3, g41_4, g41_8, g41_9, g41_10, g41_11, g41_12, g41_18, g41_19, g41_20, g41_21, g41_22, g41_23, g41_24, g41_25, g41_26, g41_27, s41.zero])
    all_goals first | decide | sv_addr
  have w42_78 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m42]; exact w41_78
  have w42_7c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m42]; exact w41_7c
  have w42_80 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m42]; exact w41_80
  have w42_84 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m42]; exact w41_84
  have w42_178 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m42]; exact w41_178
  have w42_17c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m42]; exact w41_17c
  have w42_180 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m42]; exact w41_180
  have w42_184 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m42]; exact w41_184
  have w42_200 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m42]; exact w41_200
  have w42_204 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := by rw [m42]; exact w41_204
  have w42_208 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m42]; exact w41_208
  have w42_20c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x20C) = BitVec.ofNat 32 tl29.len := by rw [m42]; exact w41_20c
  have w42_a24 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m42]; exact w41_a24
  have w42_a28 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m42]; exact w41_a28
  have w42_a2c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m42]; exact w41_a2c
  have w42_a30 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m42]; exact w41_a30
  have w42_1590 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m42]; exact w41_1590
  have w42_1594 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m42]; exact w41_1594
  have b42_a20 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m42]; exact b41_a20
  have b42_a34 : n42.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m42]; exact b41_a34
  clear w41_20c b41_a34 b41_a20 w41_1594 w41_1590 w41_a30 w41_a2c w41_a28 w41_a24 w41_208 w41_204 w41_200 w41_184 w41_180 w41_17c w41_178 w41_84 w41_80 w41_7c w41_78 g41_27 g41_26 g41_25 g41_24 g41_23 g41_22 g41_21 g41_20 g41_19 g41_18 g41_12 g41_11 g41_10 g41_9 g41_8 g41_4 g41_3 g41_2 V41 E41 fR41 t41 rg41 W41 K41 fr41 s41 d41
  -- 0x1A0: sv_iiF
  obtain ⟨n43, c43, s43, sp43, rk43, K43, A43, R43, fr43⟩ := sv_iiF (dc := 0x200)
    F E42 s42 sv_at_1a0 sv_at_1a4 (by decide) (by decide) g42_2 g42_10
    (by decide) (by decide) w42_208 w42_20c ((cc_in.contentW hr1).contentW (opt_ok_elem hr29))
  have t43 : Steps n0 n43 := t42.trans c43
  have fR43 : ∀ x, SvR B x → n43.mem x = n0.mem x := fun x hx => (fr43 x hx).trans (fR42 x hx)
  have E43 : SvCode n43.mem := E42.fr F fr43
  have V43 : SvSaves B n43.mem v := V42.keepL K43 (by decide)
  rw [sv_mb fR42 ((cc_in.contentW hr1).contentW (opt_ok_elem hr29)), derIntIsOf_congr fR42 ((cc_in.contentW hr1).contentW (opt_ok_elem hr29)), g42_11] at R43
  rw [sv_mb fR42 ((cc_in.contentW hr1).contentW (opt_ok_elem hr29))] at A43
  have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk43 (3 : Fin 32) (by decide), g42_3]
  have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk43 (4 : Fin 32) (by decide), g42_4]
  have g43_8 : reg n43 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rk43 (8 : Fin 32) (by decide), g42_8]
  have g43_9 : reg n43 (9 : Fin 32) = cp := by rw [rk43 (9 : Fin 32) (by decide), g42_9]
  have g43_18 : reg n43 (18 : Fin 32) = out := by rw [rk43 (18 : Fin 32) (by decide), g42_18]
  have g43_19 : reg n43 (19 : Fin 32) = bp := by rw [rk43 (19 : Fin 32) (by decide), g42_19]
  have g43_20 : reg n43 (20 : Fin 32) = bl16 := by rw [rk43 (20 : Fin 32) (by decide), g42_20]
  have g43_21 : reg n43 (21 : Fin 32) = lp := by rw [rk43 (21 : Fin 32) (by decide), g42_21]
  have g43_22 : reg n43 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [rk43 (22 : Fin 32) (by decide), g42_22]
  have g43_23 : reg n43 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [rk43 (23 : Fin 32) (by decide), g42_23]
  have g43_24 : reg n43 (24 : Fin 32) = bl16 := by rw [rk43 (24 : Fin 32) (by decide), g42_24]
  have g43_25 : reg n43 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [rk43 (25 : Fin 32) (by decide), g42_25]
  have g43_26 : reg n43 (26 : Fin 32) = ll := by rw [rk43 (26 : Fin 32) (by decide), g42_26]
  have g43_27 : reg n43 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk43 (27 : Fin 32) (by decide), g42_27]
  have g43_2 : reg n43 sp = B + 0x21A0 := sp43
  obtain ⟨r43, hr43⟩ : ∃ r, derIntIsOf n0.mem (memBytes n0.mem (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) (BitVec.ofNat 32 tl29.len).toNat) (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) (derElement 2 (memBytes n0.mem (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) (BitVec.ofNat 32 tl29.len).toNat)) ((BitVec.ofNat 32 0x2).extractLsb' 0 8) = r := ⟨_, rfl⟩
  rcases r43 with b43 | (_ | _)
  · rw [hr43] at R43
    obtain ⟨a0_43, a1_43⟩ := R43
    have g43_10 : reg n43 a0 = BitVec.ofNat 32 0x1 := a0_43
    have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := (K43.w32 (by decide) (by decide)).trans w42_78
    have w43_7c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := (K43.w32 (by decide) (by decide)).trans w42_7c
    have w43_80 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K43.w32 (by decide) (by decide)).trans w42_80
    have w43_84 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K43.w32 (by decide) (by decide)).trans w42_84
    have w43_178 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := (K43.w32 (by decide) (by decide)).trans w42_178
    have w43_17c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := (K43.w32 (by decide) (by decide)).trans w42_17c
    have w43_180 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := (K43.w32 (by decide) (by decide)).trans w42_180
    have w43_184 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := (K43.w32 (by decide) (by decide)).trans w42_184
    have w43_200 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := (K43.w32 (by decide) (by decide)).trans w42_200
    have w43_204 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := (K43.w32 (by decide) (by decide)).trans w42_204
    have w43_a24 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := (K43.w32 (by decide) (by decide)).trans w42_a24
    have w43_a28 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := (K43.w32 (by decide) (by decide)).trans w42_a28
    have w43_a2c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := (K43.w32 (by decide) (by decide)).trans w42_a2c
    have w43_a30 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := (K43.w32 (by decide) (by decide)).trans w42_a30
    have w43_1590 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K43.w32 (by decide) (by decide)).trans w42_1590
    have w43_1594 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K43.w32 (by decide) (by decide)).trans w42_1594
    have b43_a20 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := (K43.b8 (by decide) (by decide)).trans b42_a20
    have b43_a34 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := (K43.b8 (by decide) (by decide)).trans b42_a34
    clear b42_a34 b42_a20 w42_1594 w42_1590 w42_a30 w42_a2c w42_a28 w42_a24 w42_20c w42_208 w42_204 w42_200 w42_184 w42_180 w42_17c w42_178 w42_84 w42_80 w42_7c w42_78 g42_11 g42_10 g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_12 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
    -- 0x1A8
    obtain ⟨n44, c44, u44⟩ := s43.block svL21a8 E43.self svL21a8_end
      ⟨trivial, trivial, trivial⟩
    have m44 : n44.mem = n43.mem := u44.mem
    have s44 : St n44.mem SV n44 0x1AC (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
    have rb44 : ∀ q, reg n44 q = (runBlock svL21a8 (n43.mem, reg n43)).2 q := fun q => by rw [u44.regs]
    have fr44 : ∀ x, SvR B x → n44.mem x = n43.mem x := fun x _ => by rw [m44]
    have t44 : Steps n0 n44 := t43.trans c44
    have fR44 : ∀ x, SvR B x → n44.mem x = n0.mem x := fun x hx => (fr44 x hx).trans (fR43 x hx)
    have E44 : SvCode n44.mem := E43.fr F fr44
    have V44 : SvSaves B n44.mem v := V43.same m44
    have g44_2 : reg n44 sp = B + 0x21A0 := by
      rw [rb44, runBlock_reg _ _ _ sp s43.zero (by decide), g43_2]
    have g44_3 : reg n44 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb44, runBlock_reg _ _ _ (3 : Fin 32) s43.zero (by decide), g43_3]
    have g44_4 : reg n44 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb44, runBlock_reg _ _ _ (4 : Fin 32) s43.zero (by decide), g43_4]
    have g44_8 : reg n44 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
      rw [rb44, runBlock_reg _ _ _ (8 : Fin 32) s43.zero (by decide), g43_8]
    have g44_9 : reg n44 (9 : Fin 32) = cp := by
      rw [rb44, runBlock_reg _ _ _ (9 : Fin 32) s43.zero (by decide), g43_9]
    have g44_18 : reg n44 (18 : Fin 32) = out := by
      rw [rb44, runBlock_reg _ _ _ (18 : Fin 32) s43.zero (by decide), g43_18]
    have g44_19 : reg n44 (19 : Fin 32) = bp := by
      rw [rb44, runBlock_reg _ _ _ (19 : Fin 32) s43.zero (by decide), g43_19]
    have g44_21 : reg n44 (21 : Fin 32) = lp := by
      rw [rb44, runBlock_reg _ _ _ (21 : Fin 32) s43.zero (by decide), g43_21]
    have g44_22 : reg n44 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by
      rw [rb44, runBlock_reg _ _ _ (22 : Fin 32) s43.zero (by decide), g43_22]
    have g44_23 : reg n44 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by
      rw [rb44, runBlock_reg _ _ _ (23 : Fin 32) s43.zero (by decide), g43_23]
    have g44_24 : reg n44 (24 : Fin 32) = bl16 := by
      rw [rb44, runBlock_reg _ _ _ (24 : Fin 32) s43.zero (by decide), g43_24]
    have g44_25 : reg n44 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by
      rw [rb44, runBlock_reg _ _ _ (25 : Fin 32) s43.zero (by decide), g43_25]
    have g44_26 : reg n44 (26 : Fin 32) = ll := by
      rw [rb44, runBlock_reg _ _ _ (26 : Fin 32) s43.zero (by decide), g43_26]
    have g44_27 : reg n44 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb44, runBlock_reg _ _ _ (27 : Fin 32) s43.zero (by decide), g43_27]
    have g44_10 : reg n44 a0 = BitVec.ofNat 32 0x1 := by
      rw [rb44]; simp +decide only [runBlock, BInstr.run, svL21a8, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
      all_goals first | decide | sv_addr
    have w44_78 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m44]; exact w43_78
    have w44_7c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m44]; exact w43_7c
    have w44_80 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m44]; exact w43_80
    have w44_84 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m44]; exact w43_84
    have w44_178 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m44]; exact w43_178
    have w44_17c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m44]; exact w43_17c
    have w44_180 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m44]; exact w43_180
    have w44_184 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m44]; exact w43_184
    have w44_200 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m44]; exact w43_200
    have w44_204 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := by rw [m44]; exact w43_204
    have w44_a24 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m44]; exact w43_a24
    have w44_a28 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m44]; exact w43_a28
    have w44_a2c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m44]; exact w43_a2c
    have w44_a30 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m44]; exact w43_a30
    have w44_1590 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m44]; exact w43_1590
    have w44_1594 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m44]; exact w43_1594
    have b44_a20 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m44]; exact b43_a20
    have b44_a34 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m44]; exact b43_a34
    clear b43_a34 b43_a20 w43_1594 w43_1590 w43_a30 w43_a2c w43_a28 w43_a24 w43_204 w43_200 w43_184 w43_180 w43_17c w43_178 w43_84 w43_80 w43_7c w43_78 g43_10 a1_43 a0_43
    -- 0x1AC: branch, taken
    obtain ⟨n45, d45, u45⟩ := s44.taken E44.self 0x966 sv_at_1ac
      (by decide) (by rw [g44_10, s44.zero]; decide)
    have s45 : St n45.mem SV n45 0x966 (reg n45) := ⟨u45.pc, rfl, fun _ => rfl⟩
    have m45 : n45.mem = n44.mem := u45.mem
    have fr45 : ∀ x, SvR B x → n45.mem x = n44.mem x := fun x _ => by rw [m45]
    have t45 : Steps n0 n45 := t44.trans (.single d45)
    have fR45 : ∀ x, SvR B x → n45.mem x = n0.mem x := fun x hx => (fr45 x hx).trans (fR44 x hx)
    have E45 : SvCode n45.mem := E44.fr F fr45
    have V45 : SvSaves B n45.mem v := V44.same m45
    have g45_2 : reg n45 sp = B + 0x21A0 := by rw [u45.regs, g44_2]
    have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u45.regs, g44_3]
    have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u45.regs, g44_4]
    have g45_8 : reg n45 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u45.regs, g44_8]
    have g45_9 : reg n45 (9 : Fin 32) = cp := by rw [u45.regs, g44_9]
    have g45_10 : reg n45 a0 = BitVec.ofNat 32 0x1 := by rw [u45.regs, g44_10]
    have g45_18 : reg n45 (18 : Fin 32) = out := by rw [u45.regs, g44_18]
    have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [u45.regs, g44_19]
    have g45_21 : reg n45 (21 : Fin 32) = lp := by rw [u45.regs, g44_21]
    have g45_22 : reg n45 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u45.regs, g44_22]
    have g45_23 : reg n45 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u45.regs, g44_23]
    have g45_24 : reg n45 (24 : Fin 32) = bl16 := by rw [u45.regs, g44_24]
    have g45_25 : reg n45 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u45.regs, g44_25]
    have g45_26 : reg n45 (26 : Fin 32) = ll := by rw [u45.regs, g44_26]
    have g45_27 : reg n45 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u45.regs, g44_27]
    have w45_78 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m45]; exact w44_78
    have w45_7c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m45]; exact w44_7c
    have w45_80 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m45]; exact w44_80
    have w45_84 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m45]; exact w44_84
    have w45_178 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m45]; exact w44_178
    have w45_17c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m45]; exact w44_17c
    have w45_180 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m45]; exact w44_180
    have w45_184 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m45]; exact w44_184
    have w45_200 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m45]; exact w44_200
    have w45_204 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := by rw [m45]; exact w44_204
    have w45_a24 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m45]; exact w44_a24
    have w45_a28 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m45]; exact w44_a28
    have w45_a2c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m45]; exact w44_a2c
    have w45_a30 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m45]; exact w44_a30
    have w45_1590 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m45]; exact w44_1590
    have w45_1594 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m45]; exact w44_1594
    have b45_a20 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m45]; exact b44_a20
    have b45_a34 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m45]; exact b44_a34
    clear b44_a34 b44_a20 w44_1594 w44_1590 w44_a30 w44_a2c w44_a28 w44_a24 w44_204 w44_200 w44_184 w44_180 w44_17c w44_178 w44_84 w44_80 w44_7c w44_78 g44_10 g44_27 g44_26 g44_25 g44_24 g44_23 g44_22 g44_21 g44_19 g44_18 g44_9 g44_8 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 rb44 s44 m44 u44 c44
    exact .inl ⟨(fun ⟨tl1', h0', tl8', h1', tl16', h2', bp16', bl16', h3', h4', tl29', h5', h6', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr8] at h1'; cases h1'; rw [hr16] at h2'; cases h2'; rw [hr16b] at h3'; cases h3'; rw [hr29] at h5'; cases h5'; rw [hr43] at h6'; cases h6'), sv_fail F E45 s45 t45 fR45 V45 hret g45_2 g45_18 hO g45_3 g45_4⟩
  · rw [hr43] at R43
    obtain ⟨a0_43, a1_43⟩ := R43
    have g43_10 : reg n43 a0 = BitVec.ofNat 32 0x0 := a0_43
    have g43_11 : reg n43 a1 = BitVec.ofNat 32 0x0 := by rw [a1_43]; rfl
    have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := (K43.w32 (by decide) (by decide)).trans w42_78
    have w43_7c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := (K43.w32 (by decide) (by decide)).trans w42_7c
    have w43_80 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K43.w32 (by decide) (by decide)).trans w42_80
    have w43_84 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K43.w32 (by decide) (by decide)).trans w42_84
    have w43_178 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := (K43.w32 (by decide) (by decide)).trans w42_178
    have w43_17c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := (K43.w32 (by decide) (by decide)).trans w42_17c
    have w43_180 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := (K43.w32 (by decide) (by decide)).trans w42_180
    have w43_184 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := (K43.w32 (by decide) (by decide)).trans w42_184
    have w43_200 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := (K43.w32 (by decide) (by decide)).trans w42_200
    have w43_204 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := (K43.w32 (by decide) (by decide)).trans w42_204
    have w43_a24 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := (K43.w32 (by decide) (by decide)).trans w42_a24
    have w43_a28 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := (K43.w32 (by decide) (by decide)).trans w42_a28
    have w43_a2c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := (K43.w32 (by decide) (by decide)).trans w42_a2c
    have w43_a30 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := (K43.w32 (by decide) (by decide)).trans w42_a30
    have w43_1590 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K43.w32 (by decide) (by decide)).trans w42_1590
    have w43_1594 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K43.w32 (by decide) (by decide)).trans w42_1594
    have b43_a20 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := (K43.b8 (by decide) (by decide)).trans b42_a20
    have b43_a34 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := (K43.b8 (by decide) (by decide)).trans b42_a34
    clear b42_a34 b42_a20 w42_1594 w42_1590 w42_a30 w42_a2c w42_a28 w42_a24 w42_20c w42_208 w42_204 w42_200 w42_184 w42_180 w42_17c w42_178 w42_84 w42_80 w42_7c w42_78 g42_11 g42_10 g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_12 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
    -- 0x1A8
    obtain ⟨n44, c44, u44⟩ := s43.block svL21a8 E43.self svL21a8_end
      ⟨trivial, trivial, trivial⟩
    have m44 : n44.mem = n43.mem := u44.mem
    have s44 : St n44.mem SV n44 0x1AC (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
    have rb44 : ∀ q, reg n44 q = (runBlock svL21a8 (n43.mem, reg n43)).2 q := fun q => by rw [u44.regs]
    have fr44 : ∀ x, SvR B x → n44.mem x = n43.mem x := fun x _ => by rw [m44]
    have t44 : Steps n0 n44 := t43.trans c44
    have fR44 : ∀ x, SvR B x → n44.mem x = n0.mem x := fun x hx => (fr44 x hx).trans (fR43 x hx)
    have E44 : SvCode n44.mem := E43.fr F fr44
    have V44 : SvSaves B n44.mem v := V43.same m44
    have g44_2 : reg n44 sp = B + 0x21A0 := by
      rw [rb44, runBlock_reg _ _ _ sp s43.zero (by decide), g43_2]
    have g44_3 : reg n44 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb44, runBlock_reg _ _ _ (3 : Fin 32) s43.zero (by decide), g43_3]
    have g44_4 : reg n44 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb44, runBlock_reg _ _ _ (4 : Fin 32) s43.zero (by decide), g43_4]
    have g44_8 : reg n44 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
      rw [rb44, runBlock_reg _ _ _ (8 : Fin 32) s43.zero (by decide), g43_8]
    have g44_9 : reg n44 (9 : Fin 32) = cp := by
      rw [rb44, runBlock_reg _ _ _ (9 : Fin 32) s43.zero (by decide), g43_9]
    have g44_11 : reg n44 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb44, runBlock_reg _ _ _ a1 s43.zero (by decide), g43_11]
    have g44_18 : reg n44 (18 : Fin 32) = out := by
      rw [rb44, runBlock_reg _ _ _ (18 : Fin 32) s43.zero (by decide), g43_18]
    have g44_19 : reg n44 (19 : Fin 32) = bp := by
      rw [rb44, runBlock_reg _ _ _ (19 : Fin 32) s43.zero (by decide), g43_19]
    have g44_21 : reg n44 (21 : Fin 32) = lp := by
      rw [rb44, runBlock_reg _ _ _ (21 : Fin 32) s43.zero (by decide), g43_21]
    have g44_22 : reg n44 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by
      rw [rb44, runBlock_reg _ _ _ (22 : Fin 32) s43.zero (by decide), g43_22]
    have g44_23 : reg n44 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by
      rw [rb44, runBlock_reg _ _ _ (23 : Fin 32) s43.zero (by decide), g43_23]
    have g44_24 : reg n44 (24 : Fin 32) = bl16 := by
      rw [rb44, runBlock_reg _ _ _ (24 : Fin 32) s43.zero (by decide), g43_24]
    have g44_25 : reg n44 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by
      rw [rb44, runBlock_reg _ _ _ (25 : Fin 32) s43.zero (by decide), g43_25]
    have g44_26 : reg n44 (26 : Fin 32) = ll := by
      rw [rb44, runBlock_reg _ _ _ (26 : Fin 32) s43.zero (by decide), g43_26]
    have g44_27 : reg n44 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb44, runBlock_reg _ _ _ (27 : Fin 32) s43.zero (by decide), g43_27]
    have g44_10 : reg n44 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb44]; simp +decide only [runBlock, BInstr.run, svL21a8, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
      all_goals first | decide | sv_addr
    have g44_20 : reg n44 (20 : Fin 32) = BitVec.ofNat 32 0x0 := by
      rw [rb44]; simp +decide only [runBlock, BInstr.run, svL21a8, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
      all_goals first | decide | sv_addr
    have w44_78 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m44]; exact w43_78
    have w44_7c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m44]; exact w43_7c
    have w44_80 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m44]; exact w43_80
    have w44_84 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m44]; exact w43_84
    have w44_178 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m44]; exact w43_178
    have w44_17c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m44]; exact w43_17c
    have w44_180 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m44]; exact w43_180
    have w44_184 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m44]; exact w43_184
    have w44_200 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m44]; exact w43_200
    have w44_204 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := by rw [m44]; exact w43_204
    have w44_a24 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m44]; exact w43_a24
    have w44_a28 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m44]; exact w43_a28
    have w44_a2c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m44]; exact w43_a2c
    have w44_a30 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m44]; exact w43_a30
    have w44_1590 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m44]; exact w43_1590
    have w44_1594 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m44]; exact w43_1594
    have b44_a20 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m44]; exact b43_a20
    have b44_a34 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m44]; exact b43_a34
    clear b43_a34 b43_a20 w43_1594 w43_1590 w43_a30 w43_a2c w43_a28 w43_a24 w43_204 w43_200 w43_184 w43_180 w43_17c w43_178 w43_84 w43_80 w43_7c w43_78 g43_11 g43_10 a1_43 a0_43
    -- 0x1AC: branch, not taken
    obtain ⟨n45, d45, u45⟩ := s44.notTaken E44.self 0x1B0 sv_at_1ac
      (by decide) (by rw [g44_10, s44.zero]; decide)
    have s45 : St n45.mem SV n45 0x1B0 (reg n45) := ⟨u45.pc, rfl, fun _ => rfl⟩
    have m45 : n45.mem = n44.mem := u45.mem
    have fr45 : ∀ x, SvR B x → n45.mem x = n44.mem x := fun x _ => by rw [m45]
    have t45 : Steps n0 n45 := t44.trans (.single d45)
    have fR45 : ∀ x, SvR B x → n45.mem x = n0.mem x := fun x hx => (fr45 x hx).trans (fR44 x hx)
    have E45 : SvCode n45.mem := E44.fr F fr45
    have V45 : SvSaves B n45.mem v := V44.same m45
    have g45_2 : reg n45 sp = B + 0x21A0 := by rw [u45.regs, g44_2]
    have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u45.regs, g44_3]
    have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u45.regs, g44_4]
    have g45_8 : reg n45 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u45.regs, g44_8]
    have g45_9 : reg n45 (9 : Fin 32) = cp := by rw [u45.regs, g44_9]
    have g45_10 : reg n45 a0 = BitVec.ofNat 32 0x0 := by rw [u45.regs, g44_10]
    have g45_11 : reg n45 a1 = BitVec.ofNat 32 0x0 := by rw [u45.regs, g44_11]
    have g45_18 : reg n45 (18 : Fin 32) = out := by rw [u45.regs, g44_18]
    have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [u45.regs, g44_19]
    have g45_20 : reg n45 (20 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u45.regs, g44_20]
    have g45_21 : reg n45 (21 : Fin 32) = lp := by rw [u45.regs, g44_21]
    have g45_22 : reg n45 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u45.regs, g44_22]
    have g45_23 : reg n45 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u45.regs, g44_23]
    have g45_24 : reg n45 (24 : Fin 32) = bl16 := by rw [u45.regs, g44_24]
    have g45_25 : reg n45 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u45.regs, g44_25]
    have g45_26 : reg n45 (26 : Fin 32) = ll := by rw [u45.regs, g44_26]
    have g45_27 : reg n45 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u45.regs, g44_27]
    have w45_78 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m45]; exact w44_78
    have w45_7c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m45]; exact w44_7c
    have w45_80 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m45]; exact w44_80
    have w45_84 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m45]; exact w44_84
    have w45_178 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m45]; exact w44_178
    have w45_17c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m45]; exact w44_17c
    have w45_180 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m45]; exact w44_180
    have w45_184 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m45]; exact w44_184
    have w45_200 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m45]; exact w44_200
    have w45_204 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := by rw [m45]; exact w44_204
    have w45_a24 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m45]; exact w44_a24
    have w45_a28 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m45]; exact w44_a28
    have w45_a2c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m45]; exact w44_a2c
    have w45_a30 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m45]; exact w44_a30
    have w45_1590 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m45]; exact w44_1590
    have w45_1594 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m45]; exact w44_1594
    have b45_a20 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m45]; exact b44_a20
    have b45_a34 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m45]; exact b44_a34
    clear b44_a34 b44_a20 w44_1594 w44_1590 w44_a30 w44_a2c w44_a28 w44_a24 w44_204 w44_200 w44_184 w44_180 w44_17c w44_178 w44_84 w44_80 w44_7c w44_78 g44_20 g44_10 g44_27 g44_26 g44_25 g44_24 g44_23 g44_22 g44_21 g44_19 g44_18 g44_11 g44_9 g44_8 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 rb44 s44 m44 u44 c44
    -- 0x1B0
    obtain ⟨n46, c46, u46⟩ := s45.block svL21b0 E45.self svL21b0_end
      ⟨trivial, trivial, trivial⟩
    have m46 : n46.mem = n45.mem := u46.mem
    have s46 : St n46.mem SV n46 0x1B6 (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
    have rb46 : ∀ q, reg n46 q = (runBlock svL21b0 (n45.mem, reg n45)).2 q := fun q => by rw [u46.regs]
    have fr46 : ∀ x, SvR B x → n46.mem x = n45.mem x := fun x _ => by rw [m46]
    have t46 : Steps n0 n46 := t45.trans c46
    have fR46 : ∀ x, SvR B x → n46.mem x = n0.mem x := fun x hx => (fr46 x hx).trans (fR45 x hx)
    have E46 : SvCode n46.mem := E45.fr F fr46
    have V46 : SvSaves B n46.mem v := V45.same m46
    have g46_2 : reg n46 sp = B + 0x21A0 := by
      rw [rb46, runBlock_reg _ _ _ sp s45.zero (by decide), g45_2]
    have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb46, runBlock_reg _ _ _ (3 : Fin 32) s45.zero (by decide), g45_3]
    have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb46, runBlock_reg _ _ _ (4 : Fin 32) s45.zero (by decide), g45_4]
    have g46_8 : reg n46 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
      rw [rb46, runBlock_reg _ _ _ (8 : Fin 32) s45.zero (by decide), g45_8]
    have g46_9 : reg n46 (9 : Fin 32) = cp := by
      rw [rb46, runBlock_reg _ _ _ (9 : Fin 32) s45.zero (by decide), g45_9]
    have g46_11 : reg n46 a1 = BitVec.ofNat 32 0x0 := by
      rw [rb46, runBlock_reg _ _ _ a1 s45.zero (by decide), g45_11]
    have g46_18 : reg n46 (18 : Fin 32) = out := by
      rw [rb46, runBlock_reg _ _ _ (18 : Fin 32) s45.zero (by decide), g45_18]
    have g46_19 : reg n46 (19 : Fin 32) = bp := by
      rw [rb46, runBlock_reg _ _ _ (19 : Fin 32) s45.zero (by decide), g45_19]
    have g46_21 : reg n46 (21 : Fin 32) = lp := by
      rw [rb46, runBlock_reg _ _ _ (21 : Fin 32) s45.zero (by decide), g45_21]
    have g46_22 : reg n46 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by
      rw [rb46, runBlock_reg _ _ _ (22 : Fin 32) s45.zero (by decide), g45_22]
    have g46_23 : reg n46 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by
      rw [rb46, runBlock_reg _ _ _ (23 : Fin 32) s45.zero (by decide), g45_23]
    have g46_24 : reg n46 (24 : Fin 32) = bl16 := by
      rw [rb46, runBlock_reg _ _ _ (24 : Fin 32) s45.zero (by decide), g45_24]
    have g46_25 : reg n46 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by
      rw [rb46, runBlock_reg _ _ _ (25 : Fin 32) s45.zero (by decide), g45_25]
    have g46_26 : reg n46 (26 : Fin 32) = ll := by
      rw [rb46, runBlock_reg _ _ _ (26 : Fin 32) s45.zero (by decide), g45_26]
    have g46_27 : reg n46 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb46, runBlock_reg _ _ _ (27 : Fin 32) s45.zero (by decide), g45_27]
    have g46_10 : reg n46 a0 = BitVec.ofNat 32 0x0 := by
      rw [rb46]; simp +decide only [runBlock, BInstr.run, svL21b0, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g45_2, g45_3, g45_4, g45_8, g45_9, g45_10, g45_11, g45_18, g45_19, g45_20, g45_21, g45_22, g45_23, g45_24, g45_25, g45_26, g45_27, s45.zero])
      all_goals first | decide | sv_addr
    have g46_20 : reg n46 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by
      rw [rb46]; simp +decide only [runBlock, BInstr.run, svL21b0, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g45_2, g45_3, g45_4, g45_8, g45_9, g45_10, g45_11, g45_18, g45_19, g45_20, g45_21, g45_22, g45_23, g45_24, g45_25, g45_26, g45_27, s45.zero])
      all_goals first | decide | sv_addr
    have w46_78 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m46]; exact w45_78
    have w46_7c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m46]; exact w45_7c
    have w46_80 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m46]; exact w45_80
    have w46_84 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m46]; exact w45_84
    have w46_178 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m46]; exact w45_178
    have w46_17c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m46]; exact w45_17c
    have w46_180 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m46]; exact w45_180
    have w46_184 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m46]; exact w45_184
    have w46_200 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m46]; exact w45_200
    have w46_204 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := by rw [m46]; exact w45_204
    have w46_a24 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m46]; exact w45_a24
    have w46_a28 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m46]; exact w45_a28
    have w46_a2c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m46]; exact w45_a2c
    have w46_a30 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m46]; exact w45_a30
    have w46_1590 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m46]; exact w45_1590
    have w46_1594 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m46]; exact w45_1594
    have b46_a20 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m46]; exact b45_a20
    have b46_a34 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m46]; exact b45_a34
    clear b45_a34 b45_a20 w45_1594 w45_1590 w45_a30 w45_a2c w45_a28 w45_a24 w45_204 w45_200 w45_184 w45_180 w45_17c w45_178 w45_84 w45_80 w45_7c w45_78 g45_27 g45_26 g45_25 g45_24 g45_23 g45_22 g45_21 g45_20 g45_19 g45_18 g45_11 g45_10 g45_9 g45_8 g45_4 g45_3 g45_2 V45 E45 fR45 t45 fr45 m45 s45 u45 d45
    -- 0x1B6: branch, taken
    obtain ⟨n47, d47, u47⟩ := s46.taken E46.self 0x966 sv_at_1b6
      (by decide) (by rw [g46_10, s46.zero]; decide)
    have s47 : St n47.mem SV n47 0x966 (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
    have m47 : n47.mem = n46.mem := u47.mem
    have fr47 : ∀ x, SvR B x → n47.mem x = n46.mem x := fun x _ => by rw [m47]
    have t47 : Steps n0 n47 := t46.trans (.single d47)
    have fR47 : ∀ x, SvR B x → n47.mem x = n0.mem x := fun x hx => (fr47 x hx).trans (fR46 x hx)
    have E47 : SvCode n47.mem := E46.fr F fr47
    have V47 : SvSaves B n47.mem v := V46.same m47
    have g47_2 : reg n47 sp = B + 0x21A0 := by rw [u47.regs, g46_2]
    have g47_3 : reg n47 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u47.regs, g46_3]
    have g47_4 : reg n47 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u47.regs, g46_4]
    have g47_8 : reg n47 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u47.regs, g46_8]
    have g47_9 : reg n47 (9 : Fin 32) = cp := by rw [u47.regs, g46_9]
    have g47_10 : reg n47 a0 = BitVec.ofNat 32 0x0 := by rw [u47.regs, g46_10]
    have g47_11 : reg n47 a1 = BitVec.ofNat 32 0x0 := by rw [u47.regs, g46_11]
    have g47_18 : reg n47 (18 : Fin 32) = out := by rw [u47.regs, g46_18]
    have g47_19 : reg n47 (19 : Fin 32) = bp := by rw [u47.regs, g46_19]
    have g47_20 : reg n47 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u47.regs, g46_20]
    have g47_21 : reg n47 (21 : Fin 32) = lp := by rw [u47.regs, g46_21]
    have g47_22 : reg n47 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u47.regs, g46_22]
    have g47_23 : reg n47 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u47.regs, g46_23]
    have g47_24 : reg n47 (24 : Fin 32) = bl16 := by rw [u47.regs, g46_24]
    have g47_25 : reg n47 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u47.regs, g46_25]
    have g47_26 : reg n47 (26 : Fin 32) = ll := by rw [u47.regs, g46_26]
    have g47_27 : reg n47 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u47.regs, g46_27]
    have w47_78 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m47]; exact w46_78
    have w47_7c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m47]; exact w46_7c
    have w47_80 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m47]; exact w46_80
    have w47_84 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m47]; exact w46_84
    have w47_178 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m47]; exact w46_178
    have w47_17c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m47]; exact w46_17c
    have w47_180 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m47]; exact w46_180
    have w47_184 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m47]; exact w46_184
    have w47_200 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m47]; exact w46_200
    have w47_204 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := by rw [m47]; exact w46_204
    have w47_a24 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m47]; exact w46_a24
    have w47_a28 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m47]; exact w46_a28
    have w47_a2c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m47]; exact w46_a2c
    have w47_a30 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m47]; exact w46_a30
    have w47_1590 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m47]; exact w46_1590
    have w47_1594 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m47]; exact w46_1594
    have b47_a20 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m47]; exact b46_a20
    have b47_a34 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m47]; exact b46_a34
    clear b46_a34 b46_a20 w46_1594 w46_1590 w46_a30 w46_a2c w46_a28 w46_a24 w46_204 w46_200 w46_184 w46_180 w46_17c w46_178 w46_84 w46_80 w46_7c w46_78 g46_20 g46_10 g46_27 g46_26 g46_25 g46_24 g46_23 g46_22 g46_21 g46_19 g46_18 g46_11 g46_9 g46_8 g46_4 g46_3 g46_2 V46 E46 fR46 t46 fr46 rb46 s46 m46 u46 c46
    exact .inl ⟨(fun ⟨tl1', h0', tl8', h1', tl16', h2', bp16', bl16', h3', h4', tl29', h5', h6', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr8] at h1'; cases h1'; rw [hr16] at h2'; cases h2'; rw [hr16b] at h3'; cases h3'; rw [hr29] at h5'; cases h5'; rw [hr43] at h6'; cases h6'), sv_fail F E47 s47 t47 fR47 V47 hret g47_2 g47_18 hO g47_3 g47_4⟩
  obtain ⟨te43, hte43⟩ := ii_ok_elem hr43
  obtain ⟨d8_43, d12_43⟩ := A43 te43 hte43
  rw [hr43] at R43
  obtain ⟨a0_43, a1_43⟩ := R43
  have g43_10 : reg n43 a0 = BitVec.ofNat 32 0x0 := a0_43
  have g43_11 : reg n43 a1 = BitVec.ofNat 32 0x1 := by rw [a1_43]; rfl
  have w43_78 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := (K43.w32 (by decide) (by decide)).trans w42_78
  have w43_7c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := (K43.w32 (by decide) (by decide)).trans w42_7c
  have w43_80 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K43.w32 (by decide) (by decide)).trans w42_80
  have w43_84 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K43.w32 (by decide) (by decide)).trans w42_84
  have w43_178 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := (K43.w32 (by decide) (by decide)).trans w42_178
  have w43_17c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := (K43.w32 (by decide) (by decide)).trans w42_17c
  have w43_180 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := (K43.w32 (by decide) (by decide)).trans w42_180
  have w43_184 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := (K43.w32 (by decide) (by decide)).trans w42_184
  have w43_200 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := (K43.w32 (by decide) (by decide)).trans w42_200
  have w43_204 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := (K43.w32 (by decide) (by decide)).trans w42_204
  have w43_a24 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := (K43.w32 (by decide) (by decide)).trans w42_a24
  have w43_a28 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := (K43.w32 (by decide) (by decide)).trans w42_a28
  have w43_a2c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := (K43.w32 (by decide) (by decide)).trans w42_a2c
  have w43_a30 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := (K43.w32 (by decide) (by decide)).trans w42_a30
  have w43_1590 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := (K43.w32 (by decide) (by decide)).trans w42_1590
  have w43_1594 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := (K43.w32 (by decide) (by decide)).trans w42_1594
  have b43_a20 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := (K43.b8 (by decide) (by decide)).trans b42_a20
  have b43_a34 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := (K43.b8 (by decide) (by decide)).trans b42_a34
  have w43_208 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) + BitVec.ofNat 32 (te43.header + te43.len) := d8_43
  have w43_20c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x20C) = (BitVec.ofNat 32 tl29.len) - BitVec.ofNat 32 (te43.header + te43.len) := d12_43
  clear b42_a34 b42_a20 w42_1594 w42_1590 w42_a30 w42_a2c w42_a28 w42_a24 w42_20c w42_208 w42_204 w42_200 w42_184 w42_180 w42_17c w42_178 w42_84 w42_80 w42_7c w42_78 g42_11 g42_10 g42_27 g42_26 g42_25 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_12 g42_9 g42_8 g42_4 g42_3 g42_2 V42 E42 fR42 t42 fr42 rb42 s42 m42 u42 c42
  -- 0x1A8
  obtain ⟨n44, c44, u44⟩ := s43.block svL21a8 E43.self svL21a8_end
    ⟨trivial, trivial, trivial⟩
  have m44 : n44.mem = n43.mem := u44.mem
  have s44 : St n44.mem SV n44 0x1AC (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
  have rb44 : ∀ q, reg n44 q = (runBlock svL21a8 (n43.mem, reg n43)).2 q := fun q => by rw [u44.regs]
  have fr44 : ∀ x, SvR B x → n44.mem x = n43.mem x := fun x _ => by rw [m44]
  have t44 : Steps n0 n44 := t43.trans c44
  have fR44 : ∀ x, SvR B x → n44.mem x = n0.mem x := fun x hx => (fr44 x hx).trans (fR43 x hx)
  have E44 : SvCode n44.mem := E43.fr F fr44
  have V44 : SvSaves B n44.mem v := V43.same m44
  have g44_2 : reg n44 sp = B + 0x21A0 := by
    rw [rb44, runBlock_reg _ _ _ sp s43.zero (by decide), g43_2]
  have g44_3 : reg n44 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb44, runBlock_reg _ _ _ (3 : Fin 32) s43.zero (by decide), g43_3]
  have g44_4 : reg n44 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb44, runBlock_reg _ _ _ (4 : Fin 32) s43.zero (by decide), g43_4]
  have g44_8 : reg n44 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb44, runBlock_reg _ _ _ (8 : Fin 32) s43.zero (by decide), g43_8]
  have g44_9 : reg n44 (9 : Fin 32) = cp := by
    rw [rb44, runBlock_reg _ _ _ (9 : Fin 32) s43.zero (by decide), g43_9]
  have g44_11 : reg n44 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb44, runBlock_reg _ _ _ a1 s43.zero (by decide), g43_11]
  have g44_18 : reg n44 (18 : Fin 32) = out := by
    rw [rb44, runBlock_reg _ _ _ (18 : Fin 32) s43.zero (by decide), g43_18]
  have g44_19 : reg n44 (19 : Fin 32) = bp := by
    rw [rb44, runBlock_reg _ _ _ (19 : Fin 32) s43.zero (by decide), g43_19]
  have g44_21 : reg n44 (21 : Fin 32) = lp := by
    rw [rb44, runBlock_reg _ _ _ (21 : Fin 32) s43.zero (by decide), g43_21]
  have g44_22 : reg n44 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb44, runBlock_reg _ _ _ (22 : Fin 32) s43.zero (by decide), g43_22]
  have g44_23 : reg n44 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by
    rw [rb44, runBlock_reg _ _ _ (23 : Fin 32) s43.zero (by decide), g43_23]
  have g44_24 : reg n44 (24 : Fin 32) = bl16 := by
    rw [rb44, runBlock_reg _ _ _ (24 : Fin 32) s43.zero (by decide), g43_24]
  have g44_25 : reg n44 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by
    rw [rb44, runBlock_reg _ _ _ (25 : Fin 32) s43.zero (by decide), g43_25]
  have g44_26 : reg n44 (26 : Fin 32) = ll := by
    rw [rb44, runBlock_reg _ _ _ (26 : Fin 32) s43.zero (by decide), g43_26]
  have g44_27 : reg n44 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb44, runBlock_reg _ _ _ (27 : Fin 32) s43.zero (by decide), g43_27]
  have g44_10 : reg n44 a0 = BitVec.ofNat 32 0x0 := by
    rw [rb44]; simp +decide only [runBlock, BInstr.run, svL21a8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
    all_goals first | decide | sv_addr
  have g44_20 : reg n44 (20 : Fin 32) = BitVec.ofNat 32 0x1 := by
    rw [rb44]; simp +decide only [runBlock, BInstr.run, svL21a8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g43_2, g43_3, g43_4, g43_8, g43_9, g43_10, g43_11, g43_18, g43_19, g43_20, g43_21, g43_22, g43_23, g43_24, g43_25, g43_26, g43_27, s43.zero])
    all_goals first | decide | sv_addr
  have w44_78 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m44]; exact w43_78
  have w44_7c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m44]; exact w43_7c
  have w44_80 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m44]; exact w43_80
  have w44_84 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m44]; exact w43_84
  have w44_178 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m44]; exact w43_178
  have w44_17c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m44]; exact w43_17c
  have w44_180 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m44]; exact w43_180
  have w44_184 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m44]; exact w43_184
  have w44_200 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m44]; exact w43_200
  have w44_204 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := by rw [m44]; exact w43_204
  have w44_208 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) + BitVec.ofNat 32 (te43.header + te43.len) := by rw [m44]; exact w43_208
  have w44_20c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x20C) = (BitVec.ofNat 32 tl29.len) - BitVec.ofNat 32 (te43.header + te43.len) := by rw [m44]; exact w43_20c
  have w44_a24 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m44]; exact w43_a24
  have w44_a28 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m44]; exact w43_a28
  have w44_a2c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m44]; exact w43_a2c
  have w44_a30 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m44]; exact w43_a30
  have w44_1590 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m44]; exact w43_1590
  have w44_1594 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m44]; exact w43_1594
  have b44_a20 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m44]; exact b43_a20
  have b44_a34 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m44]; exact b43_a34
  clear w43_20c w43_208 b43_a34 b43_a20 w43_1594 w43_1590 w43_a30 w43_a2c w43_a28 w43_a24 w43_204 w43_200 w43_184 w43_180 w43_17c w43_178 w43_84 w43_80 w43_7c w43_78 g43_11 g43_10 a1_43 a0_43 d12_43 d8_43 g43_2 g43_27 g43_26 g43_25 g43_24 g43_23 g43_22 g43_21 g43_20 g43_19 g43_18 g43_9 g43_8 g43_4 g43_3 V43 E43 fR43 t43 fr43 A43 K43 rk43 sp43 s43 c43
  -- 0x1AC: branch, not taken
  obtain ⟨n45, d45, u45⟩ := s44.notTaken E44.self 0x1B0 sv_at_1ac
    (by decide) (by rw [g44_10, s44.zero]; decide)
  have s45 : St n45.mem SV n45 0x1B0 (reg n45) := ⟨u45.pc, rfl, fun _ => rfl⟩
  have m45 : n45.mem = n44.mem := u45.mem
  have fr45 : ∀ x, SvR B x → n45.mem x = n44.mem x := fun x _ => by rw [m45]
  have t45 : Steps n0 n45 := t44.trans (.single d45)
  have fR45 : ∀ x, SvR B x → n45.mem x = n0.mem x := fun x hx => (fr45 x hx).trans (fR44 x hx)
  have E45 : SvCode n45.mem := E44.fr F fr45
  have V45 : SvSaves B n45.mem v := V44.same m45
  have g45_2 : reg n45 sp = B + 0x21A0 := by rw [u45.regs, g44_2]
  have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u45.regs, g44_3]
  have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u45.regs, g44_4]
  have g45_8 : reg n45 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u45.regs, g44_8]
  have g45_9 : reg n45 (9 : Fin 32) = cp := by rw [u45.regs, g44_9]
  have g45_10 : reg n45 a0 = BitVec.ofNat 32 0x0 := by rw [u45.regs, g44_10]
  have g45_11 : reg n45 a1 = BitVec.ofNat 32 0x1 := by rw [u45.regs, g44_11]
  have g45_18 : reg n45 (18 : Fin 32) = out := by rw [u45.regs, g44_18]
  have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [u45.regs, g44_19]
  have g45_20 : reg n45 (20 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u45.regs, g44_20]
  have g45_21 : reg n45 (21 : Fin 32) = lp := by rw [u45.regs, g44_21]
  have g45_22 : reg n45 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u45.regs, g44_22]
  have g45_23 : reg n45 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u45.regs, g44_23]
  have g45_24 : reg n45 (24 : Fin 32) = bl16 := by rw [u45.regs, g44_24]
  have g45_25 : reg n45 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u45.regs, g44_25]
  have g45_26 : reg n45 (26 : Fin 32) = ll := by rw [u45.regs, g44_26]
  have g45_27 : reg n45 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u45.regs, g44_27]
  have w45_78 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m45]; exact w44_78
  have w45_7c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m45]; exact w44_7c
  have w45_80 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m45]; exact w44_80
  have w45_84 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m45]; exact w44_84
  have w45_178 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m45]; exact w44_178
  have w45_17c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m45]; exact w44_17c
  have w45_180 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m45]; exact w44_180
  have w45_184 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m45]; exact w44_184
  have w45_200 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m45]; exact w44_200
  have w45_204 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := by rw [m45]; exact w44_204
  have w45_208 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) + BitVec.ofNat 32 (te43.header + te43.len) := by rw [m45]; exact w44_208
  have w45_20c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x20C) = (BitVec.ofNat 32 tl29.len) - BitVec.ofNat 32 (te43.header + te43.len) := by rw [m45]; exact w44_20c
  have w45_a24 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m45]; exact w44_a24
  have w45_a28 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m45]; exact w44_a28
  have w45_a2c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m45]; exact w44_a2c
  have w45_a30 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m45]; exact w44_a30
  have w45_1590 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m45]; exact w44_1590
  have w45_1594 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m45]; exact w44_1594
  have b45_a20 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m45]; exact b44_a20
  have b45_a34 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m45]; exact b44_a34
  clear b44_a34 b44_a20 w44_1594 w44_1590 w44_a30 w44_a2c w44_a28 w44_a24 w44_20c w44_208 w44_204 w44_200 w44_184 w44_180 w44_17c w44_178 w44_84 w44_80 w44_7c w44_78 g44_20 g44_10 g44_27 g44_26 g44_25 g44_24 g44_23 g44_22 g44_21 g44_19 g44_18 g44_11 g44_9 g44_8 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 rb44 s44 m44 u44 c44
  -- 0x1B0
  obtain ⟨n46, c46, u46⟩ := s45.block svL21b0 E45.self svL21b0_end
    ⟨trivial, trivial, trivial⟩
  have m46 : n46.mem = n45.mem := u46.mem
  have s46 : St n46.mem SV n46 0x1B6 (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
  have rb46 : ∀ q, reg n46 q = (runBlock svL21b0 (n45.mem, reg n45)).2 q := fun q => by rw [u46.regs]
  have fr46 : ∀ x, SvR B x → n46.mem x = n45.mem x := fun x _ => by rw [m46]
  have t46 : Steps n0 n46 := t45.trans c46
  have fR46 : ∀ x, SvR B x → n46.mem x = n0.mem x := fun x hx => (fr46 x hx).trans (fR45 x hx)
  have E46 : SvCode n46.mem := E45.fr F fr46
  have V46 : SvSaves B n46.mem v := V45.same m46
  have g46_2 : reg n46 sp = B + 0x21A0 := by
    rw [rb46, runBlock_reg _ _ _ sp s45.zero (by decide), g45_2]
  have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb46, runBlock_reg _ _ _ (3 : Fin 32) s45.zero (by decide), g45_3]
  have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb46, runBlock_reg _ _ _ (4 : Fin 32) s45.zero (by decide), g45_4]
  have g46_8 : reg n46 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb46, runBlock_reg _ _ _ (8 : Fin 32) s45.zero (by decide), g45_8]
  have g46_9 : reg n46 (9 : Fin 32) = cp := by
    rw [rb46, runBlock_reg _ _ _ (9 : Fin 32) s45.zero (by decide), g45_9]
  have g46_11 : reg n46 a1 = BitVec.ofNat 32 0x1 := by
    rw [rb46, runBlock_reg _ _ _ a1 s45.zero (by decide), g45_11]
  have g46_18 : reg n46 (18 : Fin 32) = out := by
    rw [rb46, runBlock_reg _ _ _ (18 : Fin 32) s45.zero (by decide), g45_18]
  have g46_19 : reg n46 (19 : Fin 32) = bp := by
    rw [rb46, runBlock_reg _ _ _ (19 : Fin 32) s45.zero (by decide), g45_19]
  have g46_21 : reg n46 (21 : Fin 32) = lp := by
    rw [rb46, runBlock_reg _ _ _ (21 : Fin 32) s45.zero (by decide), g45_21]
  have g46_22 : reg n46 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by
    rw [rb46, runBlock_reg _ _ _ (22 : Fin 32) s45.zero (by decide), g45_22]
  have g46_23 : reg n46 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by
    rw [rb46, runBlock_reg _ _ _ (23 : Fin 32) s45.zero (by decide), g45_23]
  have g46_24 : reg n46 (24 : Fin 32) = bl16 := by
    rw [rb46, runBlock_reg _ _ _ (24 : Fin 32) s45.zero (by decide), g45_24]
  have g46_25 : reg n46 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by
    rw [rb46, runBlock_reg _ _ _ (25 : Fin 32) s45.zero (by decide), g45_25]
  have g46_26 : reg n46 (26 : Fin 32) = ll := by
    rw [rb46, runBlock_reg _ _ _ (26 : Fin 32) s45.zero (by decide), g45_26]
  have g46_27 : reg n46 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb46, runBlock_reg _ _ _ (27 : Fin 32) s45.zero (by decide), g45_27]
  have g46_10 : reg n46 a0 = BitVec.ofNat 32 0x1 := by
    rw [rb46]; simp +decide only [runBlock, BInstr.run, svL21b0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g45_2, g45_3, g45_4, g45_8, g45_9, g45_10, g45_11, g45_18, g45_19, g45_20, g45_21, g45_22, g45_23, g45_24, g45_25, g45_26, g45_27, s45.zero])
    all_goals first | decide | sv_addr
  have g46_20 : reg n46 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by
    rw [rb46]; simp +decide only [runBlock, BInstr.run, svL21b0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g45_2, g45_3, g45_4, g45_8, g45_9, g45_10, g45_11, g45_18, g45_19, g45_20, g45_21, g45_22, g45_23, g45_24, g45_25, g45_26, g45_27, s45.zero])
    all_goals first | decide | sv_addr
  have w46_78 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m46]; exact w45_78
  have w46_7c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m46]; exact w45_7c
  have w46_80 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m46]; exact w45_80
  have w46_84 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m46]; exact w45_84
  have w46_178 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m46]; exact w45_178
  have w46_17c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m46]; exact w45_17c
  have w46_180 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m46]; exact w45_180
  have w46_184 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m46]; exact w45_184
  have w46_200 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m46]; exact w45_200
  have w46_204 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := by rw [m46]; exact w45_204
  have w46_208 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) + BitVec.ofNat 32 (te43.header + te43.len) := by rw [m46]; exact w45_208
  have w46_20c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x20C) = (BitVec.ofNat 32 tl29.len) - BitVec.ofNat 32 (te43.header + te43.len) := by rw [m46]; exact w45_20c
  have w46_a24 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m46]; exact w45_a24
  have w46_a28 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m46]; exact w45_a28
  have w46_a2c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m46]; exact w45_a2c
  have w46_a30 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m46]; exact w45_a30
  have w46_1590 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m46]; exact w45_1590
  have w46_1594 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m46]; exact w45_1594
  have b46_a20 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m46]; exact b45_a20
  have b46_a34 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m46]; exact b45_a34
  clear b45_a34 b45_a20 w45_1594 w45_1590 w45_a30 w45_a2c w45_a28 w45_a24 w45_20c w45_208 w45_204 w45_200 w45_184 w45_180 w45_17c w45_178 w45_84 w45_80 w45_7c w45_78 g45_27 g45_26 g45_25 g45_24 g45_23 g45_22 g45_21 g45_20 g45_19 g45_18 g45_11 g45_10 g45_9 g45_8 g45_4 g45_3 g45_2 V45 E45 fR45 t45 fr45 m45 s45 u45 d45
  -- 0x1B6: branch, not taken
  obtain ⟨n47, d47, u47⟩ := s46.notTaken E46.self 0x1BA sv_at_1b6
    (by decide) (by rw [g46_10, s46.zero]; decide)
  have s47 : St n47.mem SV n47 0x1BA (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
  have m47 : n47.mem = n46.mem := u47.mem
  have fr47 : ∀ x, SvR B x → n47.mem x = n46.mem x := fun x _ => by rw [m47]
  have t47 : Steps n0 n47 := t46.trans (.single d47)
  have fR47 : ∀ x, SvR B x → n47.mem x = n0.mem x := fun x hx => (fr47 x hx).trans (fR46 x hx)
  have E47 : SvCode n47.mem := E46.fr F fr47
  have V47 : SvSaves B n47.mem v := V46.same m47
  have g47_2 : reg n47 sp = B + 0x21A0 := by rw [u47.regs, g46_2]
  have g47_3 : reg n47 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u47.regs, g46_3]
  have g47_4 : reg n47 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u47.regs, g46_4]
  have g47_8 : reg n47 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u47.regs, g46_8]
  have g47_9 : reg n47 (9 : Fin 32) = cp := by rw [u47.regs, g46_9]
  have g47_10 : reg n47 a0 = BitVec.ofNat 32 0x1 := by rw [u47.regs, g46_10]
  have g47_11 : reg n47 a1 = BitVec.ofNat 32 0x1 := by rw [u47.regs, g46_11]
  have g47_18 : reg n47 (18 : Fin 32) = out := by rw [u47.regs, g46_18]
  have g47_19 : reg n47 (19 : Fin 32) = bp := by rw [u47.regs, g46_19]
  have g47_20 : reg n47 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u47.regs, g46_20]
  have g47_21 : reg n47 (21 : Fin 32) = lp := by rw [u47.regs, g46_21]
  have g47_22 : reg n47 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u47.regs, g46_22]
  have g47_23 : reg n47 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u47.regs, g46_23]
  have g47_24 : reg n47 (24 : Fin 32) = bl16 := by rw [u47.regs, g46_24]
  have g47_25 : reg n47 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u47.regs, g46_25]
  have g47_26 : reg n47 (26 : Fin 32) = ll := by rw [u47.regs, g46_26]
  have g47_27 : reg n47 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u47.regs, g46_27]
  have w47_78 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m47]; exact w46_78
  have w47_7c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m47]; exact w46_7c
  have w47_80 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m47]; exact w46_80
  have w47_84 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m47]; exact w46_84
  have w47_178 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m47]; exact w46_178
  have w47_17c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m47]; exact w46_17c
  have w47_180 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m47]; exact w46_180
  have w47_184 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m47]; exact w46_184
  have w47_200 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m47]; exact w46_200
  have w47_204 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := by rw [m47]; exact w46_204
  have w47_208 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) + BitVec.ofNat 32 (te43.header + te43.len) := by rw [m47]; exact w46_208
  have w47_20c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x20C) = (BitVec.ofNat 32 tl29.len) - BitVec.ofNat 32 (te43.header + te43.len) := by rw [m47]; exact w46_20c
  have w47_a24 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m47]; exact w46_a24
  have w47_a28 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m47]; exact w46_a28
  have w47_a2c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m47]; exact w46_a2c
  have w47_a30 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m47]; exact w46_a30
  have w47_1590 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m47]; exact w46_1590
  have w47_1594 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m47]; exact w46_1594
  have b47_a20 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m47]; exact b46_a20
  have b47_a34 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m47]; exact b46_a34
  clear b46_a34 b46_a20 w46_1594 w46_1590 w46_a30 w46_a2c w46_a28 w46_a24 w46_20c w46_208 w46_204 w46_200 w46_184 w46_180 w46_17c w46_178 w46_84 w46_80 w46_7c w46_78 g46_20 g46_10 g46_27 g46_26 g46_25 g46_24 g46_23 g46_22 g46_21 g46_19 g46_18 g46_11 g46_9 g46_8 g46_4 g46_3 g46_2 V46 E46 fR46 t46 fr46 rb46 s46 m46 u46 c46
  -- 0x1BA: lw
  obtain ⟨n48, d48, u48⟩ := s47.lw E47.self sv_at_1ba (off' := 0x1BE) (by decide)
    (by rw [g47_2, show B + 0x21A0 + 0x20C = B + 0x21A0 + BitVec.ofNat 32 0x20C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s48 : St n48.mem SV n48 0x1BE (reg n48) := ⟨u48.pc, rfl, fun _ => rfl⟩
  have m48 : n48.mem = n47.mem := u48.mem
  have fr48 : ∀ x, SvR B x → n48.mem x = n47.mem x := fun x _ => by rw [m48]
  have t48 : Steps n0 n48 := t47.trans (.single d48)
  have fR48 : ∀ x, SvR B x → n48.mem x = n0.mem x := fun x hx => (fr48 x hx).trans (fR47 x hx)
  have E48 : SvCode n48.mem := E47.fr F fr48
  have V48 : SvSaves B n48.mem v := V47.same m48
  have g48_2 : reg n48 sp = B + 0x21A0 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_2]
  have g48_3 : reg n48 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u48.regs, upd_ne (by decide) (by decide), g47_3]
  have g48_4 : reg n48 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u48.regs, upd_ne (by decide) (by decide), g47_4]
  have g48_8 : reg n48 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u48.regs, upd_ne (by decide) (by decide), g47_8]
  have g48_9 : reg n48 (9 : Fin 32) = cp := by rw [u48.regs, upd_ne (by decide) (by decide), g47_9]
  have g48_11 : reg n48 a1 = BitVec.ofNat 32 0x1 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_11]
  have g48_18 : reg n48 (18 : Fin 32) = out := by rw [u48.regs, upd_ne (by decide) (by decide), g47_18]
  have g48_19 : reg n48 (19 : Fin 32) = bp := by rw [u48.regs, upd_ne (by decide) (by decide), g47_19]
  have g48_20 : reg n48 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_20]
  have g48_21 : reg n48 (21 : Fin 32) = lp := by rw [u48.regs, upd_ne (by decide) (by decide), g47_21]
  have g48_22 : reg n48 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u48.regs, upd_ne (by decide) (by decide), g47_22]
  have g48_23 : reg n48 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u48.regs, upd_ne (by decide) (by decide), g47_23]
  have g48_24 : reg n48 (24 : Fin 32) = bl16 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_24]
  have g48_25 : reg n48 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u48.regs, upd_ne (by decide) (by decide), g47_25]
  have g48_26 : reg n48 (26 : Fin 32) = ll := by rw [u48.regs, upd_ne (by decide) (by decide), g47_26]
  have g48_27 : reg n48 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u48.regs, upd_ne (by decide) (by decide), g47_27]
  have g48_10 : reg n48 a0 = (BitVec.ofNat 32 tl29.len) - BitVec.ofNat 32 (te43.header + te43.len) := by
    rw [u48.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g47_2, show B + 0x21A0 + 0x20C = B + 0x21A0 + BitVec.ofNat 32 0x20C by sv_addr, w47_20c]
  have w48_78 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m48]; exact w47_78
  have w48_7c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m48]; exact w47_7c
  have w48_80 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m48]; exact w47_80
  have w48_84 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m48]; exact w47_84
  have w48_178 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m48]; exact w47_178
  have w48_17c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m48]; exact w47_17c
  have w48_180 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m48]; exact w47_180
  have w48_184 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m48]; exact w47_184
  have w48_200 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m48]; exact w47_200
  have w48_204 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := by rw [m48]; exact w47_204
  have w48_208 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) + BitVec.ofNat 32 (te43.header + te43.len) := by rw [m48]; exact w47_208
  have w48_20c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x20C) = (BitVec.ofNat 32 tl29.len) - BitVec.ofNat 32 (te43.header + te43.len) := by rw [m48]; exact w47_20c
  have w48_a24 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m48]; exact w47_a24
  have w48_a28 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m48]; exact w47_a28
  have w48_a2c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m48]; exact w47_a2c
  have w48_a30 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m48]; exact w47_a30
  have w48_1590 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m48]; exact w47_1590
  have w48_1594 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m48]; exact w47_1594
  have b48_a20 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m48]; exact b47_a20
  have b48_a34 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m48]; exact b47_a34
  clear b47_a34 b47_a20 w47_1594 w47_1590 w47_a30 w47_a2c w47_a28 w47_a24 w47_20c w47_208 w47_204 w47_200 w47_184 w47_180 w47_17c w47_178 w47_84 w47_80 w47_7c w47_78 g47_27 g47_26 g47_25 g47_24 g47_23 g47_22 g47_21 g47_20 g47_19 g47_18 g47_11 g47_10 g47_9 g47_8 g47_4 g47_3 g47_2 V47 E47 fR47 t47 fr47 m47 s47 u47 d47
  by_cases hz_48 : (BitVec.ofNat 32 tl29.len) - BitVec.ofNat 32 (te43.header + te43.len) = 0
  rotate_left
  · -- 0x1BE: branch, not taken
    obtain ⟨n49, d49, u49⟩ := s48.notTaken E48.self 0x1C0 sv_at_1be
      (by decide) (by rw [g48_10, s48.zero]; exact br_beq_f hz_48)
    have s49 : St n49.mem SV n49 0x1C0 (reg n49) := ⟨u49.pc, rfl, fun _ => rfl⟩
    have m49 : n49.mem = n48.mem := u49.mem
    have fr49 : ∀ x, SvR B x → n49.mem x = n48.mem x := fun x _ => by rw [m49]
    have t49 : Steps n0 n49 := t48.trans (.single d49)
    have fR49 : ∀ x, SvR B x → n49.mem x = n0.mem x := fun x hx => (fr49 x hx).trans (fR48 x hx)
    have E49 : SvCode n49.mem := E48.fr F fr49
    have V49 : SvSaves B n49.mem v := V48.same m49
    have g49_2 : reg n49 sp = B + 0x21A0 := by rw [u49.regs, g48_2]
    have g49_3 : reg n49 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u49.regs, g48_3]
    have g49_4 : reg n49 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u49.regs, g48_4]
    have g49_8 : reg n49 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u49.regs, g48_8]
    have g49_9 : reg n49 (9 : Fin 32) = cp := by rw [u49.regs, g48_9]
    have g49_10 : reg n49 a0 = (BitVec.ofNat 32 tl29.len) - BitVec.ofNat 32 (te43.header + te43.len) := by rw [u49.regs, g48_10]
    have g49_11 : reg n49 a1 = BitVec.ofNat 32 0x1 := by rw [u49.regs, g48_11]
    have g49_18 : reg n49 (18 : Fin 32) = out := by rw [u49.regs, g48_18]
    have g49_19 : reg n49 (19 : Fin 32) = bp := by rw [u49.regs, g48_19]
    have g49_20 : reg n49 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u49.regs, g48_20]
    have g49_21 : reg n49 (21 : Fin 32) = lp := by rw [u49.regs, g48_21]
    have g49_22 : reg n49 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u49.regs, g48_22]
    have g49_23 : reg n49 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u49.regs, g48_23]
    have g49_24 : reg n49 (24 : Fin 32) = bl16 := by rw [u49.regs, g48_24]
    have g49_25 : reg n49 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u49.regs, g48_25]
    have g49_26 : reg n49 (26 : Fin 32) = ll := by rw [u49.regs, g48_26]
    have g49_27 : reg n49 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u49.regs, g48_27]
    have w49_78 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m49]; exact w48_78
    have w49_7c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m49]; exact w48_7c
    have w49_80 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m49]; exact w48_80
    have w49_84 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m49]; exact w48_84
    have w49_178 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m49]; exact w48_178
    have w49_17c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m49]; exact w48_17c
    have w49_180 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m49]; exact w48_180
    have w49_184 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m49]; exact w48_184
    have w49_200 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m49]; exact w48_200
    have w49_204 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := by rw [m49]; exact w48_204
    have w49_208 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) + BitVec.ofNat 32 (te43.header + te43.len) := by rw [m49]; exact w48_208
    have w49_20c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x20C) = (BitVec.ofNat 32 tl29.len) - BitVec.ofNat 32 (te43.header + te43.len) := by rw [m49]; exact w48_20c
    have w49_a24 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m49]; exact w48_a24
    have w49_a28 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m49]; exact w48_a28
    have w49_a2c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m49]; exact w48_a2c
    have w49_a30 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m49]; exact w48_a30
    have w49_1590 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m49]; exact w48_1590
    have w49_1594 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m49]; exact w48_1594
    have b49_a20 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m49]; exact b48_a20
    have b49_a34 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m49]; exact b48_a34
    clear b48_a34 b48_a20 w48_1594 w48_1590 w48_a30 w48_a2c w48_a28 w48_a24 w48_20c w48_208 w48_204 w48_200 w48_184 w48_180 w48_17c w48_178 w48_84 w48_80 w48_7c w48_78 g48_10 g48_27 g48_26 g48_25 g48_24 g48_23 g48_22 g48_21 g48_20 g48_19 g48_18 g48_11 g48_9 g48_8 g48_4 g48_3 g48_2 V48 E48 fR48 t48 fr48 m48 s48 u48 d48
    -- 0x1C0
    obtain ⟨n50, c50, u50⟩ := s49.block svL21c0 E49.self svL21c0_end
      ⟨trivial, trivial⟩
    have m50 : n50.mem = n49.mem := u50.mem
    have s50 : St n50.mem SV n50 0x1C2 (reg n50) := ⟨u50.pc, rfl, fun _ => rfl⟩
    have rb50 : ∀ q, reg n50 q = (runBlock svL21c0 (n49.mem, reg n49)).2 q := fun q => by rw [u50.regs]
    have fr50 : ∀ x, SvR B x → n50.mem x = n49.mem x := fun x _ => by rw [m50]
    have t50 : Steps n0 n50 := t49.trans c50
    have fR50 : ∀ x, SvR B x → n50.mem x = n0.mem x := fun x hx => (fr50 x hx).trans (fR49 x hx)
    have E50 : SvCode n50.mem := E49.fr F fr50
    have V50 : SvSaves B n50.mem v := V49.same m50
    have g50_2 : reg n50 sp = B + 0x21A0 := by
      rw [rb50, runBlock_reg _ _ _ sp s49.zero (by decide), g49_2]
    have g50_3 : reg n50 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb50, runBlock_reg _ _ _ (3 : Fin 32) s49.zero (by decide), g49_3]
    have g50_4 : reg n50 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb50, runBlock_reg _ _ _ (4 : Fin 32) s49.zero (by decide), g49_4]
    have g50_8 : reg n50 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by
      rw [rb50, runBlock_reg _ _ _ (8 : Fin 32) s49.zero (by decide), g49_8]
    have g50_9 : reg n50 (9 : Fin 32) = cp := by
      rw [rb50, runBlock_reg _ _ _ (9 : Fin 32) s49.zero (by decide), g49_9]
    have g50_10 : reg n50 a0 = (BitVec.ofNat 32 tl29.len) - BitVec.ofNat 32 (te43.header + te43.len) := by
      rw [rb50, runBlock_reg _ _ _ a0 s49.zero (by decide), g49_10]
    have g50_11 : reg n50 a1 = BitVec.ofNat 32 0x1 := by
      rw [rb50, runBlock_reg _ _ _ a1 s49.zero (by decide), g49_11]
    have g50_18 : reg n50 (18 : Fin 32) = out := by
      rw [rb50, runBlock_reg _ _ _ (18 : Fin 32) s49.zero (by decide), g49_18]
    have g50_19 : reg n50 (19 : Fin 32) = bp := by
      rw [rb50, runBlock_reg _ _ _ (19 : Fin 32) s49.zero (by decide), g49_19]
    have g50_21 : reg n50 (21 : Fin 32) = lp := by
      rw [rb50, runBlock_reg _ _ _ (21 : Fin 32) s49.zero (by decide), g49_21]
    have g50_22 : reg n50 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by
      rw [rb50, runBlock_reg _ _ _ (22 : Fin 32) s49.zero (by decide), g49_22]
    have g50_23 : reg n50 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by
      rw [rb50, runBlock_reg _ _ _ (23 : Fin 32) s49.zero (by decide), g49_23]
    have g50_24 : reg n50 (24 : Fin 32) = bl16 := by
      rw [rb50, runBlock_reg _ _ _ (24 : Fin 32) s49.zero (by decide), g49_24]
    have g50_25 : reg n50 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by
      rw [rb50, runBlock_reg _ _ _ (25 : Fin 32) s49.zero (by decide), g49_25]
    have g50_26 : reg n50 (26 : Fin 32) = ll := by
      rw [rb50, runBlock_reg _ _ _ (26 : Fin 32) s49.zero (by decide), g49_26]
    have g50_27 : reg n50 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb50, runBlock_reg _ _ _ (27 : Fin 32) s49.zero (by decide), g49_27]
    have g50_20 : reg n50 (20 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb50]; simp +decide only [runBlock, BInstr.run, svL21c0, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g49_2, g49_3, g49_4, g49_8, g49_9, g49_10, g49_11, g49_18, g49_19, g49_20, g49_21, g49_22, g49_23, g49_24, g49_25, g49_26, g49_27, s49.zero])
      all_goals first | decide | sv_addr
    have w50_78 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m50]; exact w49_78
    have w50_7c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m50]; exact w49_7c
    have w50_80 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m50]; exact w49_80
    have w50_84 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m50]; exact w49_84
    have w50_178 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m50]; exact w49_178
    have w50_17c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m50]; exact w49_17c
    have w50_180 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m50]; exact w49_180
    have w50_184 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m50]; exact w49_184
    have w50_200 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m50]; exact w49_200
    have w50_204 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := by rw [m50]; exact w49_204
    have w50_208 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) + BitVec.ofNat 32 (te43.header + te43.len) := by rw [m50]; exact w49_208
    have w50_20c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x20C) = (BitVec.ofNat 32 tl29.len) - BitVec.ofNat 32 (te43.header + te43.len) := by rw [m50]; exact w49_20c
    have w50_a24 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m50]; exact w49_a24
    have w50_a28 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m50]; exact w49_a28
    have w50_a2c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m50]; exact w49_a2c
    have w50_a30 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m50]; exact w49_a30
    have w50_1590 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m50]; exact w49_1590
    have w50_1594 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m50]; exact w49_1594
    have b50_a20 : n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m50]; exact b49_a20
    have b50_a34 : n50.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m50]; exact b49_a34
    clear b49_a34 b49_a20 w49_1594 w49_1590 w49_a30 w49_a2c w49_a28 w49_a24 w49_20c w49_208 w49_204 w49_200 w49_184 w49_180 w49_17c w49_178 w49_84 w49_80 w49_7c w49_78 g49_27 g49_26 g49_25 g49_24 g49_23 g49_22 g49_21 g49_20 g49_19 g49_18 g49_11 g49_10 g49_9 g49_8 g49_4 g49_3 g49_2 V49 E49 fR49 t49 fr49 m49 s49 u49 d49
    -- 0x1C2: j
    obtain ⟨n51, d51, u51⟩ := s50.jump E50.self sv_at_1c2 (off' := 0x966) (by decide)
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
    have g51_8 : reg n51 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u51.regs, g50_8]
    have g51_9 : reg n51 (9 : Fin 32) = cp := by rw [u51.regs, g50_9]
    have g51_10 : reg n51 a0 = (BitVec.ofNat 32 tl29.len) - BitVec.ofNat 32 (te43.header + te43.len) := by rw [u51.regs, g50_10]
    have g51_11 : reg n51 a1 = BitVec.ofNat 32 0x1 := by rw [u51.regs, g50_11]
    have g51_18 : reg n51 (18 : Fin 32) = out := by rw [u51.regs, g50_18]
    have g51_19 : reg n51 (19 : Fin 32) = bp := by rw [u51.regs, g50_19]
    have g51_20 : reg n51 (20 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u51.regs, g50_20]
    have g51_21 : reg n51 (21 : Fin 32) = lp := by rw [u51.regs, g50_21]
    have g51_22 : reg n51 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u51.regs, g50_22]
    have g51_23 : reg n51 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u51.regs, g50_23]
    have g51_24 : reg n51 (24 : Fin 32) = bl16 := by rw [u51.regs, g50_24]
    have g51_25 : reg n51 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u51.regs, g50_25]
    have g51_26 : reg n51 (26 : Fin 32) = ll := by rw [u51.regs, g50_26]
    have g51_27 : reg n51 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u51.regs, g50_27]
    have w51_78 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m51]; exact w50_78
    have w51_7c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m51]; exact w50_7c
    have w51_80 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m51]; exact w50_80
    have w51_84 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m51]; exact w50_84
    have w51_178 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m51]; exact w50_178
    have w51_17c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m51]; exact w50_17c
    have w51_180 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m51]; exact w50_180
    have w51_184 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m51]; exact w50_184
    have w51_200 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m51]; exact w50_200
    have w51_204 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := by rw [m51]; exact w50_204
    have w51_208 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) + BitVec.ofNat 32 (te43.header + te43.len) := by rw [m51]; exact w50_208
    have w51_20c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x20C) = (BitVec.ofNat 32 tl29.len) - BitVec.ofNat 32 (te43.header + te43.len) := by rw [m51]; exact w50_20c
    have w51_a24 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m51]; exact w50_a24
    have w51_a28 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m51]; exact w50_a28
    have w51_a2c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m51]; exact w50_a2c
    have w51_a30 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m51]; exact w50_a30
    have w51_1590 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m51]; exact w50_1590
    have w51_1594 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m51]; exact w50_1594
    have b51_a20 : n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m51]; exact b50_a20
    have b51_a34 : n51.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m51]; exact b50_a34
    clear b50_a34 b50_a20 w50_1594 w50_1590 w50_a30 w50_a2c w50_a28 w50_a24 w50_20c w50_208 w50_204 w50_200 w50_184 w50_180 w50_17c w50_178 w50_84 w50_80 w50_7c w50_78 g50_20 g50_27 g50_26 g50_25 g50_24 g50_23 g50_22 g50_21 g50_19 g50_18 g50_11 g50_10 g50_9 g50_8 g50_4 g50_3 g50_2 V50 E50 fR50 t50 fr50 rb50 s50 m50 u50 c50
    exact .inl ⟨(fun ⟨tl1', h0', tl8', h1', tl16', h2', bp16', bl16', h3', h4', tl29', h5', h6', te43', h7', h8', _⟩ => by rw [hr1] at h0'; cases h0'; rw [hr8] at h1'; cases h1'; rw [hr16] at h2'; cases h2'; rw [hr16b] at h3'; cases h3'; rw [hr29] at h5'; cases h5'; rw [hr43] at h6'; cases h6'; rw [hte43] at h7'; cases h7'; exact hz_48 h8'), sv_fail F E51 s51 t51 fR51 V51 hret g51_2 g51_18 hO g51_3 g51_4⟩
  -- 0x1BE: branch, taken
  obtain ⟨n49, d49, u49⟩ := s48.taken E48.self 0x1C8 sv_at_1be
    (by decide) (by rw [g48_10, s48.zero]; exact br_beq_t hz_48)
  have s49 : St n49.mem SV n49 0x1C8 (reg n49) := ⟨u49.pc, rfl, fun _ => rfl⟩
  have m49 : n49.mem = n48.mem := u49.mem
  have fr49 : ∀ x, SvR B x → n49.mem x = n48.mem x := fun x _ => by rw [m49]
  have t49 : Steps n0 n49 := t48.trans (.single d49)
  have fR49 : ∀ x, SvR B x → n49.mem x = n0.mem x := fun x hx => (fr49 x hx).trans (fR48 x hx)
  have E49 : SvCode n49.mem := E48.fr F fr49
  have V49 : SvSaves B n49.mem v := V48.same m49
  have g49_2 : reg n49 sp = B + 0x21A0 := by rw [u49.regs, g48_2]
  have g49_3 : reg n49 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u49.regs, g48_3]
  have g49_4 : reg n49 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u49.regs, g48_4]
  have g49_8 : reg n49 (8 : Fin 32) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u49.regs, g48_8]
  have g49_9 : reg n49 (9 : Fin 32) = cp := by rw [u49.regs, g48_9]
  have g49_10 : reg n49 a0 = (BitVec.ofNat 32 tl29.len) - BitVec.ofNat 32 (te43.header + te43.len) := by rw [u49.regs, g48_10]
  have g49_11 : reg n49 a1 = BitVec.ofNat 32 0x1 := by rw [u49.regs, g48_11]
  have g49_18 : reg n49 (18 : Fin 32) = out := by rw [u49.regs, g48_18]
  have g49_19 : reg n49 (19 : Fin 32) = bp := by rw [u49.regs, g48_19]
  have g49_20 : reg n49 (20 : Fin 32) = BitVec.ofNat 32 0x15 := by rw [u49.regs, g48_20]
  have g49_21 : reg n49 (21 : Fin 32) = lp := by rw [u49.regs, g48_21]
  have g49_22 : reg n49 (22 : Fin 32) = (cp) + BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [u49.regs, g48_22]
  have g49_23 : reg n49 (23 : Fin 32) = BitVec.ofNat 32 tl1.len := by rw [u49.regs, g48_23]
  have g49_24 : reg n49 (24 : Fin 32) = bl16 := by rw [u49.regs, g48_24]
  have g49_25 : reg n49 (25 : Fin 32) = BitVec.ofNat 32 (tl8.header + tl8.len) := by rw [u49.regs, g48_25]
  have g49_26 : reg n49 (26 : Fin 32) = ll := by rw [u49.regs, g48_26]
  have g49_27 : reg n49 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u49.regs, g48_27]
  have w49_78 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (tl1.header + tl1.len) := by rw [m49]; exact w48_78
  have w49_7c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16 := by rw [m49]; exact w48_7c
  have w49_80 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m49]; exact w48_80
  have w49_84 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m49]; exact w48_84
  have w49_178 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m49]; exact w48_178
  have w49_17c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1.len := by rw [m49]; exact w48_17c
  have w49_180 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m49]; exact w48_180
  have w49_184 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl1.len) - BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m49]; exact w48_184
  have w49_200 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x200) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m49]; exact w48_200
  have w49_204 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl29.len := by rw [m49]; exact w48_204
  have w49_208 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = (((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header) + BitVec.ofNat 32 (te43.header + te43.len) := by rw [m49]; exact w48_208
  have w49_20c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x20C) = (BitVec.ofNat 32 tl29.len) - BitVec.ofNat 32 (te43.header + te43.len) := by rw [m49]; exact w48_20c
  have w49_a24 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = ((cp) + BitVec.ofNat 32 tl1.header) + BitVec.ofNat 32 tl29.header := by rw [m49]; exact w48_a24
  have w49_a28 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 tl29.len := by rw [m49]; exact w48_a28
  have w49_a2c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (cp) + BitVec.ofNat 32 tl1.header := by rw [m49]; exact w48_a2c
  have w49_a30 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 (tl29.header + tl29.len) := by rw [m49]; exact w48_a30
  have w49_1590 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((cp) + BitVec.ofNat 32 (tl1.header + tl1.len)) + BitVec.ofNat 32 (tl8.header + tl8.len)) + BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m49]; exact w48_1590
  have w49_1594 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (((cl) - BitVec.ofNat 32 (tl1.header + tl1.len)) - BitVec.ofNat 32 (tl8.header + tl8.len)) - BitVec.ofNat 32 (tl16.header + tl16.len) := by rw [m49]; exact w48_1594
  have b49_a20 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m49]; exact b48_a20
  have b49_a34 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = BitVec.ofNat 8 tl29.tag := by rw [m49]; exact b48_a34
  clear b48_a34 b48_a20 w48_1594 w48_1590 w48_a30 w48_a2c w48_a28 w48_a24 w48_20c w48_208 w48_204 w48_200 w48_184 w48_180 w48_17c w48_178 w48_84 w48_80 w48_7c w48_78 g48_10 g48_27 g48_26 g48_25 g48_24 g48_23 g48_22 g48_21 g48_20 g48_19 g48_18 g48_11 g48_9 g48_8 g48_4 g48_3 g48_2 V48 E48 fR48 t48 fr48 m48 s48 u48 d48
  exact .inr ⟨tl1, hr1, tl8, hr8, tl16, hr16, bp16, bl16, hr16b, hz_20, tl29, hr29, hr43, te43, hte43, hz_48, n49, t49, s49, E49, V49, fR49, g49_2, g49_3, g49_4, g49_8, g49_9, g49_18, g49_19, g49_20, g49_21, g49_22, g49_23, g49_24, g49_25, g49_26, g49_27, w49_78, w49_7c, w49_80, w49_84, w49_178, w49_17c, w49_180, w49_184⟩

end C3.RV32.Sv
