import C3BootProofs.Proofs.SvCongr

/-!
# `sigstore::verify`: the issuer and the validity

From 0x266 to the subject at 0x322: the issuer, and the validity, a sequence of exactly two times.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svL426e : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .aluImm .add a1 sp 0x178, .aluImm .add a2 x0 0x30]
set_option maxRecDepth 100000 in
theorem svL426e_end : blockEnd sigstoreVerifyCode 0x26E svL426e = some 0x27C := by decide

def svL4296 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .aluImm .add a1 sp 0x178]
set_option maxRecDepth 100000 in
theorem svL4296_end : blockEnd sigstoreVerifyCode 0x296 svL4296 = some 0x2A0 := by decide

def svL42b4 : List BInstr :=
  [.aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x226, .aluImm .add a0 sp 0x245, .aluImm .add a2 x0 0xB]
set_option maxRecDepth 100000 in
theorem svL42b4_end : blockEnd sigstoreVerifyCode 0x2B4 svL42b4 = some 0x2C2 := by decide

def svL42d2 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .aluImm .add a1 sp 0x240]
set_option maxRecDepth 100000 in
theorem svL42d2_end : blockEnd sigstoreVerifyCode 0x2D2 svL42d2 = some 0x2DC := by decide

def svL42ec : List BInstr :=
  [.alu .add a1 x0 (27 : Fin 32)]
set_option maxRecDepth 100000 in
theorem svL42ec_end : blockEnd sigstoreVerifyCode 0x2EC svL42ec = some 0x2EE := by decide

def svL42f6 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221, .aluImm .add a1 sp 0x240]
set_option maxRecDepth 100000 in
theorem svL42f6_end : blockEnd sigstoreVerifyCode 0x2F6 svL42f6 = some 0x300 := by decide

def svL41c0 : List BInstr :=
  [.aluImm .add (20 : Fin 32) x0 0x1]
set_option maxRecDepth 100000 in
theorem svL41c0_end : blockEnd sigstoreVerifyCode 0x1C0 svL41c0 = some 0x1C2 := by decide

def svL4318 : List BInstr :=
  [.alu .add (8 : Fin 32) x0 (27 : Fin 32)]
set_option maxRecDepth 100000 in
theorem svL4318_end : blockEnd sigstoreVerifyCode 0x318 svL4318 = some 0x31A := by decide

set_option maxHeartbeats 0 in
theorem sv_l4 {B out bp rootp dg lp ll rp rl sgl orl orp trp tcl sgp arp arl trl : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x266 (reg n0))
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = BitVec.ofNat 32 0x0)
    (g0_9 : reg n0 (9 : Fin 32) = trp)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = lp)
    (g0_22 : reg n0 (22 : Fin 32) = orp)
    (g0_23 : reg n0 (23 : Fin 32) = tcl)
    (g0_24 : reg n0 (24 : Fin 32) = sgl)
    (g0_25 : reg n0 (25 : Fin 32) = orl)
    (g0_26 : reg n0 (26 : Fin 32) = ll)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_70 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp)
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp)
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg)
    (w0_180 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp)
    (w0_184 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl)
    (tb_in : SvIn B (rp) (rl).toNat) :
    (¬ (∃ tl6, derElement 0x30 (memBytes n0.mem (rp) (rl).toNat) = .ok tl6 ∧ ∃ tl13, derElement 0x30 (memBytes n0.mem ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)).toNat) = .ok tl13 ∧ ∃ tm22 rs22, readTime (memBytes n0.mem (((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) (tl13.len)) = some (tm22, rs22) ∧ ∃ tm31 rs31, readTime rs22 = some (tm31, rs31) ∧ (rs31 = []) ∧ True) ∧ SvErrRet B out v n0) ∨
    (∃ tl6, derElement 0x30 (memBytes n0.mem (rp) (rl).toNat) = .ok tl6 ∧
    ∃ tl13, derElement 0x30 (memBytes n0.mem ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)).toNat) = .ok tl13 ∧
    ∃ tm22 rs22, readTime (memBytes n0.mem (((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) (tl13.len)) = some (tm22, rs22) ∧
    ∃ tm31 rs31, readTime rs22 = some (tm31, rs31) ∧
    (rs31 = []) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x322 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = n0.mem x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        reg n' (9 : Fin 32) = trp ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 ∧
        reg n' (21 : Fin 32) = lp ∧
        reg n' (22 : Fin 32) = orp ∧
        reg n' (23 : Fin 32) = tcl ∧
        reg n' (24 : Fin 32) = sgl ∧
        reg n' (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) ∧
        reg n' (26 : Fin 32) = ll ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = BitVec.ofNat 32 (tm31 / 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 (tm31 % 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len)) := by
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = n0.mem x := fun _ _ => rfl
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  -- 0x266: sw
  obtain ⟨n1, d1, s1, fr1, K1, W1, rg1⟩ := sv_sw F E0 s0 sv_at_266 (off' := 0x268) (c := 0x68)
    (by decide) (by rw [g0_2]; sv_addr) (by decide) (by decide)
  have t1 : Steps n0 n1 := t0.trans d1
  have fR1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.keep K1 (by decide)
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [rg1 sp, g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg1 (3 : Fin 32), g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg1 (4 : Fin 32), g0_4]
  have g1_8 : reg n1 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg1 (8 : Fin 32), g0_8]
  have g1_9 : reg n1 (9 : Fin 32) = trp := by rw [rg1 (9 : Fin 32), g0_9]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [rg1 (18 : Fin 32), g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [rg1 (19 : Fin 32), g0_19]
  have g1_21 : reg n1 (21 : Fin 32) = lp := by rw [rg1 (21 : Fin 32), g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = orp := by rw [rg1 (22 : Fin 32), g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = tcl := by rw [rg1 (23 : Fin 32), g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = sgl := by rw [rg1 (24 : Fin 32), g0_24]
  have g1_25 : reg n1 (25 : Fin 32) = orl := by rw [rg1 (25 : Fin 32), g0_25]
  have g1_26 : reg n1 (26 : Fin 32) = ll := by rw [rg1 (26 : Fin 32), g0_26]
  have g1_27 : reg n1 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg1 (27 : Fin 32), g0_27]
  have w1_70 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K1.w32 (by decide) (by decide)).trans w0_70
  have w1_74 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K1.w32 (by decide) (by decide)).trans w0_74
  have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K1.w32 (by decide) (by decide)).trans w0_78
  have w1_7c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K1.w32 (by decide) (by decide)).trans w0_7c
  have w1_80 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K1.w32 (by decide) (by decide)).trans w0_80
  have w1_84 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K1.w32 (by decide) (by decide)).trans w0_84
  have w1_180 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp := (K1.w32 (by decide) (by decide)).trans w0_180
  have w1_184 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl := (K1.w32 (by decide) (by decide)).trans w0_184
  have w1_68 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [W1, g0_24]
  -- 0x268: sw
  obtain ⟨n2, d2, s2, fr2, K2, W2, rg2⟩ := sv_sw F E1 s1 sv_at_268 (off' := 0x26A) (c := 0x64)
    (by decide) (by rw [g1_2]; sv_addr) (by decide) (by decide)
  have t2 : Steps n0 n2 := t1.trans d2
  have fR2 : ∀ x, SvR B x → n2.mem x = n0.mem x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  have E2 : SvCode n2.mem := E1.fr F fr2
  have V2 : SvSaves B n2.mem v := V1.keep K2 (by decide)
  have g2_2 : reg n2 sp = B + 0x21A0 := by rw [rg2 sp, g1_2]
  have g2_3 : reg n2 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg2 (3 : Fin 32), g1_3]
  have g2_4 : reg n2 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg2 (4 : Fin 32), g1_4]
  have g2_8 : reg n2 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg2 (8 : Fin 32), g1_8]
  have g2_9 : reg n2 (9 : Fin 32) = trp := by rw [rg2 (9 : Fin 32), g1_9]
  have g2_18 : reg n2 (18 : Fin 32) = out := by rw [rg2 (18 : Fin 32), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by rw [rg2 (19 : Fin 32), g1_19]
  have g2_21 : reg n2 (21 : Fin 32) = lp := by rw [rg2 (21 : Fin 32), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = orp := by rw [rg2 (22 : Fin 32), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = tcl := by rw [rg2 (23 : Fin 32), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = sgl := by rw [rg2 (24 : Fin 32), g1_24]
  have g2_25 : reg n2 (25 : Fin 32) = orl := by rw [rg2 (25 : Fin 32), g1_25]
  have g2_26 : reg n2 (26 : Fin 32) = ll := by rw [rg2 (26 : Fin 32), g1_26]
  have g2_27 : reg n2 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg2 (27 : Fin 32), g1_27]
  have w2_68 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K2.w32 (by decide) (by decide)).trans w1_68
  have w2_70 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K2.w32 (by decide) (by decide)).trans w1_70
  have w2_74 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K2.w32 (by decide) (by decide)).trans w1_74
  have w2_78 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K2.w32 (by decide) (by decide)).trans w1_78
  have w2_7c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K2.w32 (by decide) (by decide)).trans w1_7c
  have w2_80 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K2.w32 (by decide) (by decide)).trans w1_80
  have w2_84 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K2.w32 (by decide) (by decide)).trans w1_84
  have w2_180 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp := (K2.w32 (by decide) (by decide)).trans w1_180
  have w2_184 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl := (K2.w32 (by decide) (by decide)).trans w1_184
  have w2_64 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [W2, g1_25]
  clear w1_68 w1_184 w1_180 w1_84 w1_80 w1_7c w1_78 w1_74 w1_70 g1_27 g1_26 g1_25 g1_24 g1_23 g1_22 g1_21 g1_19 g1_18 g1_9 g1_8 g1_4 g1_3 g1_2 V1 E1 fR1 t1 rg1 W1 K1 fr1 s1 d1 g0_4 g0_3 fR0 t0
  -- 0x26A: sw
  obtain ⟨n3, d3, s3, fr3, K3, W3, rg3⟩ := sv_sw F E2 s2 sv_at_26a (off' := 0x26C) (c := 0x60)
    (by decide) (by rw [g2_2]; sv_addr) (by decide) (by decide)
  have t3 : Steps n0 n3 := t2.trans d3
  have fR3 : ∀ x, SvR B x → n3.mem x = n0.mem x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.keep K3 (by decide)
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [rg3 sp, g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg3 (3 : Fin 32), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg3 (4 : Fin 32), g2_4]
  have g3_8 : reg n3 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg3 (8 : Fin 32), g2_8]
  have g3_9 : reg n3 (9 : Fin 32) = trp := by rw [rg3 (9 : Fin 32), g2_9]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [rg3 (18 : Fin 32), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [rg3 (19 : Fin 32), g2_19]
  have g3_21 : reg n3 (21 : Fin 32) = lp := by rw [rg3 (21 : Fin 32), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = orp := by rw [rg3 (22 : Fin 32), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = tcl := by rw [rg3 (23 : Fin 32), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = sgl := by rw [rg3 (24 : Fin 32), g2_24]
  have g3_25 : reg n3 (25 : Fin 32) = orl := by rw [rg3 (25 : Fin 32), g2_25]
  have g3_26 : reg n3 (26 : Fin 32) = ll := by rw [rg3 (26 : Fin 32), g2_26]
  have g3_27 : reg n3 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg3 (27 : Fin 32), g2_27]
  have w3_64 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := (K3.w32 (by decide) (by decide)).trans w2_64
  have w3_68 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K3.w32 (by decide) (by decide)).trans w2_68
  have w3_70 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K3.w32 (by decide) (by decide)).trans w2_70
  have w3_74 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K3.w32 (by decide) (by decide)).trans w2_74
  have w3_78 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K3.w32 (by decide) (by decide)).trans w2_78
  have w3_7c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K3.w32 (by decide) (by decide)).trans w2_7c
  have w3_80 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K3.w32 (by decide) (by decide)).trans w2_80
  have w3_84 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K3.w32 (by decide) (by decide)).trans w2_84
  have w3_180 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp := (K3.w32 (by decide) (by decide)).trans w2_180
  have w3_184 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl := (K3.w32 (by decide) (by decide)).trans w2_184
  have w3_60 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [W3, g2_22]
  clear w2_64 w2_184 w2_180 w2_84 w2_80 w2_7c w2_78 w2_74 w2_70 w2_68 g2_27 g2_26 g2_25 g2_24 g2_23 g2_22 g2_21 g2_19 g2_18 g2_9 g2_8 g2_4 g2_3 g2_2 V2 E2 fR2 t2 rg2 W2 K2 fr2 s2 d2
  -- 0x26C: sw
  obtain ⟨n4, d4, s4, fr4, K4, W4, rg4⟩ := sv_sw F E3 s3 sv_at_26c (off' := 0x26E) (c := 0x6C)
    (by decide) (by rw [g3_2]; sv_addr) (by decide) (by decide)
  have t4 : Steps n0 n4 := t3.trans d4
  have fR4 : ∀ x, SvR B x → n4.mem x = n0.mem x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.keep K4 (by decide)
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [rg4 sp, g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg4 (3 : Fin 32), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg4 (4 : Fin 32), g3_4]
  have g4_8 : reg n4 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg4 (8 : Fin 32), g3_8]
  have g4_9 : reg n4 (9 : Fin 32) = trp := by rw [rg4 (9 : Fin 32), g3_9]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [rg4 (18 : Fin 32), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [rg4 (19 : Fin 32), g3_19]
  have g4_21 : reg n4 (21 : Fin 32) = lp := by rw [rg4 (21 : Fin 32), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = orp := by rw [rg4 (22 : Fin 32), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = tcl := by rw [rg4 (23 : Fin 32), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = sgl := by rw [rg4 (24 : Fin 32), g3_24]
  have g4_25 : reg n4 (25 : Fin 32) = orl := by rw [rg4 (25 : Fin 32), g3_25]
  have g4_26 : reg n4 (26 : Fin 32) = ll := by rw [rg4 (26 : Fin 32), g3_26]
  have g4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg4 (27 : Fin 32), g3_27]
  have w4_60 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K4.w32 (by decide) (by decide)).trans w3_60
  have w4_64 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := (K4.w32 (by decide) (by decide)).trans w3_64
  have w4_68 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K4.w32 (by decide) (by decide)).trans w3_68
  have w4_70 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K4.w32 (by decide) (by decide)).trans w3_70
  have w4_74 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K4.w32 (by decide) (by decide)).trans w3_74
  have w4_78 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K4.w32 (by decide) (by decide)).trans w3_78
  have w4_7c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K4.w32 (by decide) (by decide)).trans w3_7c
  have w4_80 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K4.w32 (by decide) (by decide)).trans w3_80
  have w4_84 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K4.w32 (by decide) (by decide)).trans w3_84
  have w4_180 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp := (K4.w32 (by decide) (by decide)).trans w3_180
  have w4_184 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl := (K4.w32 (by decide) (by decide)).trans w3_184
  have w4_6c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [W4, g3_21]
  clear w3_60 w3_184 w3_180 w3_84 w3_80 w3_7c w3_78 w3_74 w3_70 w3_68 w3_64 g3_27 g3_26 g3_25 g3_24 g3_23 g3_22 g3_21 g3_19 g3_18 g3_9 g3_8 g3_4 g3_3 g3_2 V3 E3 fR3 t3 rg3 W3 K3 fr3 s3 d3
  -- 0x26E
  obtain ⟨n5, c5, u5⟩ := s4.block svL426e E4.self svL426e_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0x27C (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock svL426e (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x _ => by rw [m5]
  have t5 : Steps n0 n5 := t4.trans c5
  have fR5 : ∀ x, SvR B x → n5.mem x = n0.mem x := fun x hx => (fr5 x hx).trans (fR4 x hx)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have V5 : SvSaves B n5.mem v := V4.same m5
  have g5_2 : reg n5 sp = B + 0x21A0 := by
    rw [rb5, runBlock_reg _ _ _ sp s4.zero (by decide), g4_2]
  have g5_3 : reg n5 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb5, runBlock_reg _ _ _ (3 : Fin 32) s4.zero (by decide), g4_3]
  have g5_4 : reg n5 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb5, runBlock_reg _ _ _ (4 : Fin 32) s4.zero (by decide), g4_4]
  have g5_8 : reg n5 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb5, runBlock_reg _ _ _ (8 : Fin 32) s4.zero (by decide), g4_8]
  have g5_9 : reg n5 (9 : Fin 32) = trp := by
    rw [rb5, runBlock_reg _ _ _ (9 : Fin 32) s4.zero (by decide), g4_9]
  have g5_18 : reg n5 (18 : Fin 32) = out := by
    rw [rb5, runBlock_reg _ _ _ (18 : Fin 32) s4.zero (by decide), g4_18]
  have g5_19 : reg n5 (19 : Fin 32) = bp := by
    rw [rb5, runBlock_reg _ _ _ (19 : Fin 32) s4.zero (by decide), g4_19]
  have g5_21 : reg n5 (21 : Fin 32) = lp := by
    rw [rb5, runBlock_reg _ _ _ (21 : Fin 32) s4.zero (by decide), g4_21]
  have g5_22 : reg n5 (22 : Fin 32) = orp := by
    rw [rb5, runBlock_reg _ _ _ (22 : Fin 32) s4.zero (by decide), g4_22]
  have g5_23 : reg n5 (23 : Fin 32) = tcl := by
    rw [rb5, runBlock_reg _ _ _ (23 : Fin 32) s4.zero (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = sgl := by
    rw [rb5, runBlock_reg _ _ _ (24 : Fin 32) s4.zero (by decide), g4_24]
  have g5_25 : reg n5 (25 : Fin 32) = orl := by
    rw [rb5, runBlock_reg _ _ _ (25 : Fin 32) s4.zero (by decide), g4_25]
  have g5_26 : reg n5 (26 : Fin 32) = ll := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_27 : reg n5 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb5, runBlock_reg _ _ _ (27 : Fin 32) s4.zero (by decide), g4_27]
  have g5_10 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svL426e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_18, g4_19, g4_21, g4_22, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g5_11 : reg n5 a1 = B + 0x21A0 + BitVec.ofNat 32 0x178 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svL426e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_18, g4_19, g4_21, g4_22, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g5_12 : reg n5 a2 = BitVec.ofNat 32 0x30 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svL426e, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_8, g4_9, g4_18, g4_19, g4_21, g4_22, g4_23, g4_24, g4_25, g4_26, g4_27, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w5_60 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m5]; exact w4_60
  have w5_64 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m5]; exact w4_64
  have w5_68 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m5]; exact w4_68
  have w5_6c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m5]; exact w4_6c
  have w5_70 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m5]; exact w4_70
  have w5_74 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m5]; exact w4_74
  have w5_78 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m5]; exact w4_78
  have w5_7c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m5]; exact w4_7c
  have w5_80 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m5]; exact w4_80
  have w5_84 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m5]; exact w4_84
  have w5_180 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = rp := by rw [m5]; exact w4_180
  have w5_184 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = rl := by rw [m5]; exact w4_184
  clear w4_6c w4_184 w4_180 w4_84 w4_80 w4_7c w4_78 w4_74 w4_70 w4_68 w4_64 w4_60 g4_27 g4_26 g4_25 g4_24 g4_23 g4_22 g4_21 g4_19 g4_18 g4_9 g4_8 g4_4 g4_3 g4_2 V4 E4 fR4 t4 rg4 W4 K4 fr4 s4 d4
  -- 0x27C: sv_elemF
  obtain ⟨n6, c6, s6, rk6, K6, Ok6, Er6, fr6⟩ := sv_elemF (oc := 0xA20) (dc := 0x178) (tag := 0x30)
    F E5 s5 sv_at_27c sv_at_280 (by decide) (by decide) g5_10 g5_11 g5_12 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) w5_180 w5_184
  have t6 : Steps n0 n6 := t5.trans c6
  have fR6 : ∀ x, SvR B x → n6.mem x = n0.mem x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.keepL K6 (by decide)
  rw [sv_mb fR5 tb_in] at Ok6 Er6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [rk6 sp (by decide) (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk6 (3 : Fin 32) (by decide) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk6 (4 : Fin 32) (by decide) (by decide), g5_4]
  have g6_8 : reg n6 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rk6 (8 : Fin 32) (by decide) (by decide), g5_8]
  have g6_9 : reg n6 (9 : Fin 32) = trp := by rw [rk6 (9 : Fin 32) (by decide) (by decide), g5_9]
  have g6_10 : reg n6 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk6 a0 (by decide) (by decide), g5_10]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [rk6 (18 : Fin 32) (by decide) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [rk6 (19 : Fin 32) (by decide) (by decide), g5_19]
  have g6_21 : reg n6 (21 : Fin 32) = lp := by rw [rk6 (21 : Fin 32) (by decide) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = orp := by rw [rk6 (22 : Fin 32) (by decide) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = tcl := by rw [rk6 (23 : Fin 32) (by decide) (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = sgl := by rw [rk6 (24 : Fin 32) (by decide) (by decide), g5_24]
  have g6_25 : reg n6 (25 : Fin 32) = orl := by rw [rk6 (25 : Fin 32) (by decide) (by decide), g5_25]
  have g6_26 : reg n6 (26 : Fin 32) = ll := by rw [rk6 (26 : Fin 32) (by decide) (by decide), g5_26]
  have g6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk6 (27 : Fin 32) (by decide) (by decide), g5_27]
  obtain ⟨r6, hr6⟩ : ∃ r, derElement 0x30 (memBytes n0.mem (rp) (rl).toNat) = r := ⟨_, rfl⟩
  rcases r6 with er6 | tl6
  · obtain ⟨zhr6, -⟩ := Er6 er6 hr6
    have w6_60 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K6.w32 (by decide) (by decide)).trans w5_60
    have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := (K6.w32 (by decide) (by decide)).trans w5_64
    have w6_68 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K6.w32 (by decide) (by decide)).trans w5_68
    have w6_6c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K6.w32 (by decide) (by decide)).trans w5_6c
    have w6_70 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K6.w32 (by decide) (by decide)).trans w5_70
    have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K6.w32 (by decide) (by decide)).trans w5_74
    have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K6.w32 (by decide) (by decide)).trans w5_78
    have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K6.w32 (by decide) (by decide)).trans w5_7c
    have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K6.w32 (by decide) (by decide)).trans w5_80
    have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K6.w32 (by decide) (by decide)).trans w5_84
    have w6_a20 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := zhr6
    clear w5_184 w5_180 w5_84 w5_80 w5_7c w5_78 w5_74 w5_70 w5_6c w5_68 w5_64 w5_60 g5_12 g5_11 g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_19 g5_18 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
    -- 0x284: lw
    obtain ⟨n7, d7, u7⟩ := s6.lw E6.self sv_at_284 (off' := 0x288) (by decide)
      (by rw [g6_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s7 : St n7.mem SV n7 0x288 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
    have m7 : n7.mem = n6.mem := u7.mem
    have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
    have t7 : Steps n0 n7 := t6.trans (.single d7)
    have fR7 : ∀ x, SvR B x → n7.mem x = n0.mem x := fun x hx => (fr7 x hx).trans (fR6 x hx)
    have E7 : SvCode n7.mem := E6.fr F fr7
    have V7 : SvSaves B n7.mem v := V6.same m7
    have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
    have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
    have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
    have g7_8 : reg n7 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_8]
    have g7_9 : reg n7 (9 : Fin 32) = trp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_9]
    have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, upd_ne (by decide) (by decide), g6_18]
    have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_19]
    have g7_21 : reg n7 (21 : Fin 32) = lp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_21]
    have g7_22 : reg n7 (22 : Fin 32) = orp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_22]
    have g7_23 : reg n7 (23 : Fin 32) = tcl := by rw [u7.regs, upd_ne (by decide) (by decide), g6_23]
    have g7_24 : reg n7 (24 : Fin 32) = sgl := by rw [u7.regs, upd_ne (by decide) (by decide), g6_24]
    have g7_25 : reg n7 (25 : Fin 32) = orl := by rw [u7.regs, upd_ne (by decide) (by decide), g6_25]
    have g7_26 : reg n7 (26 : Fin 32) = ll := by rw [u7.regs, upd_ne (by decide) (by decide), g6_26]
    have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_27]
    have g7_10 : reg n7 a0 = 0 := by
      rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g6_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w6_a20]
    have w7_60 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m7]; exact w6_60
    have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m7]; exact w6_64
    have w7_68 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m7]; exact w6_68
    have w7_6c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m7]; exact w6_6c
    have w7_70 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m7]; exact w6_70
    have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m7]; exact w6_74
    have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m7]; exact w6_78
    have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m7]; exact w6_7c
    have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m7]; exact w6_80
    have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m7]; exact w6_84
    have w7_a20 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m7]; exact w6_a20
    clear w6_a20 w6_84 w6_80 w6_7c w6_78 w6_74 w6_70 w6_6c w6_68 w6_64 w6_60 zhr6
    -- 0x288: branch, taken
    obtain ⟨n8, d8, u8⟩ := s7.taken E7.self 0x962 sv_at_288
      (by decide) (by rw [g7_10, s7.zero]; rfl)
    have s8 : St n8.mem SV n8 0x962 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
    have m8 : n8.mem = n7.mem := u8.mem
    have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
    have t8 : Steps n0 n8 := t7.trans (.single d8)
    have fR8 : ∀ x, SvR B x → n8.mem x = n0.mem x := fun x hx => (fr8 x hx).trans (fR7 x hx)
    have E8 : SvCode n8.mem := E7.fr F fr8
    have V8 : SvSaves B n8.mem v := V7.same m8
    have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, g7_2]
    have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, g7_3]
    have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, g7_4]
    have g8_8 : reg n8 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u8.regs, g7_8]
    have g8_9 : reg n8 (9 : Fin 32) = trp := by rw [u8.regs, g7_9]
    have g8_10 : reg n8 a0 = 0 := by rw [u8.regs, g7_10]
    have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, g7_18]
    have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, g7_19]
    have g8_21 : reg n8 (21 : Fin 32) = lp := by rw [u8.regs, g7_21]
    have g8_22 : reg n8 (22 : Fin 32) = orp := by rw [u8.regs, g7_22]
    have g8_23 : reg n8 (23 : Fin 32) = tcl := by rw [u8.regs, g7_23]
    have g8_24 : reg n8 (24 : Fin 32) = sgl := by rw [u8.regs, g7_24]
    have g8_25 : reg n8 (25 : Fin 32) = orl := by rw [u8.regs, g7_25]
    have g8_26 : reg n8 (26 : Fin 32) = ll := by rw [u8.regs, g7_26]
    have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u8.regs, g7_27]
    have w8_60 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m8]; exact w7_60
    have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m8]; exact w7_64
    have w8_68 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m8]; exact w7_68
    have w8_6c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m8]; exact w7_6c
    have w8_70 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m8]; exact w7_70
    have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m8]; exact w7_74
    have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m8]; exact w7_78
    have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m8]; exact w7_7c
    have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m8]; exact w7_80
    have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m8]; exact w7_84
    have w8_a20 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m8]; exact w7_a20
    clear w7_a20 w7_84 w7_80 w7_7c w7_78 w7_74 w7_70 w7_6c w7_68 w7_64 w7_60 g7_10 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
    -- 0x962: lbu
    obtain ⟨n9, d9, u9⟩ := s8.lbu E8.self sv_at_962 (off' := 0x966) (by decide)
    have s9 : St n9.mem SV n9 0x966 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have m9 : n9.mem = n8.mem := u9.mem
    have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
    have t9 : Steps n0 n9 := t8.trans (.single d9)
    have fR9 : ∀ x, SvR B x → n9.mem x = n0.mem x := fun x hx => (fr9 x hx).trans (fR8 x hx)
    have E9 : SvCode n9.mem := E8.fr F fr9
    have V9 : SvSaves B n9.mem v := V8.same m9
    have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_2]
    have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_3]
    have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_4]
    have g9_8 : reg n9 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_8]
    have g9_9 : reg n9 (9 : Fin 32) = trp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_9]
    have g9_10 : reg n9 a0 = 0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_10]
    have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, upd_ne (by decide) (by decide), g8_18]
    have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_19]
    have g9_21 : reg n9 (21 : Fin 32) = lp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_21]
    have g9_22 : reg n9 (22 : Fin 32) = orp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_22]
    have g9_23 : reg n9 (23 : Fin 32) = tcl := by rw [u9.regs, upd_ne (by decide) (by decide), g8_23]
    have g9_24 : reg n9 (24 : Fin 32) = sgl := by rw [u9.regs, upd_ne (by decide) (by decide), g8_24]
    have g9_25 : reg n9 (25 : Fin 32) = orl := by rw [u9.regs, upd_ne (by decide) (by decide), g8_25]
    have g9_26 : reg n9 (26 : Fin 32) = ll := by rw [u9.regs, upd_ne (by decide) (by decide), g8_26]
    have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_27]
    have w9_60 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m9]; exact w8_60
    have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m9]; exact w8_64
    have w9_68 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m9]; exact w8_68
    have w9_6c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m9]; exact w8_6c
    have w9_70 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m9]; exact w8_70
    have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m9]; exact w8_74
    have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m9]; exact w8_78
    have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m9]; exact w8_7c
    have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m9]; exact w8_80
    have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m9]; exact w8_84
    have w9_a20 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m9]; exact w8_a20
    clear w8_a20 w8_84 w8_80 w8_7c w8_78 w8_74 w8_70 w8_6c w8_68 w8_64 w8_60 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_19 g8_18 g8_10 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
    exact .inl ⟨(fun ⟨tl6', h0', _⟩ => by rw [hr6] at h0'; cases h0'), sv_fail F E9 s9 t9 fR9 V9 hret g9_2 g9_18 hO g9_3 g9_4⟩
  obtain ⟨o0_6, o4_6, o8_6, o12_6, o16_6, d8_6, d12_6⟩ := Ok6 tl6 hr6
  have w6_60 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K6.w32 (by decide) (by decide)).trans w5_60
  have w6_64 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := (K6.w32 (by decide) (by decide)).trans w5_64
  have w6_68 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K6.w32 (by decide) (by decide)).trans w5_68
  have w6_6c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K6.w32 (by decide) (by decide)).trans w5_6c
  have w6_70 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K6.w32 (by decide) (by decide)).trans w5_70
  have w6_74 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K6.w32 (by decide) (by decide)).trans w5_74
  have w6_78 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K6.w32 (by decide) (by decide)).trans w5_78
  have w6_7c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K6.w32 (by decide) (by decide)).trans w5_7c
  have w6_80 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K6.w32 (by decide) (by decide)).trans w5_80
  have w6_84 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K6.w32 (by decide) (by decide)).trans w5_84
  have w6_180 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl6.header + tl6.len) := d8_6
  have w6_184 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl6.header + tl6.len) := d12_6
  have w6_a20 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (rp) + BitVec.ofNat 32 tl6.header := o0_6
  have w6_a24 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl6.len := o4_6
  have w6_a28 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = rp := o8_6
  have w6_a2c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl6.header + tl6.len) := o12_6
  have b6_a30 : n6.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := o16_6
  clear w5_184 w5_180 w5_84 w5_80 w5_7c w5_78 w5_74 w5_70 w5_6c w5_68 w5_64 w5_60 g5_12 g5_11 g5_10 g5_27 g5_26 g5_25 g5_24 g5_23 g5_22 g5_21 g5_19 g5_18 g5_9 g5_8 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0x284: lw
  obtain ⟨n7, d7, u7⟩ := s6.lw E6.self sv_at_284 (off' := 0x288) (by decide)
    (by rw [g6_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s7 : St n7.mem SV n7 0x288 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x _ => by rw [m7]
  have t7 : Steps n0 n7 := t6.trans (.single d7)
  have fR7 : ∀ x, SvR B x → n7.mem x = n0.mem x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.same m7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u7.regs, upd_ne (by decide) (by decide), g6_4]
  have g7_8 : reg n7 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_8]
  have g7_9 : reg n7 (9 : Fin 32) = trp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_9]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [u7.regs, upd_ne (by decide) (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_19]
  have g7_21 : reg n7 (21 : Fin 32) = lp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = orp := by rw [u7.regs, upd_ne (by decide) (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = tcl := by rw [u7.regs, upd_ne (by decide) (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = sgl := by rw [u7.regs, upd_ne (by decide) (by decide), g6_24]
  have g7_25 : reg n7 (25 : Fin 32) = orl := by rw [u7.regs, upd_ne (by decide) (by decide), g6_25]
  have g7_26 : reg n7 (26 : Fin 32) = ll := by rw [u7.regs, upd_ne (by decide) (by decide), g6_26]
  have g7_27 : reg n7 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u7.regs, upd_ne (by decide) (by decide), g6_27]
  have g7_10 : reg n7 a0 = (rp) + BitVec.ofNat 32 tl6.header := by
    rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g6_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w6_a20]
  have w7_60 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m7]; exact w6_60
  have w7_64 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m7]; exact w6_64
  have w7_68 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m7]; exact w6_68
  have w7_6c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m7]; exact w6_6c
  have w7_70 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m7]; exact w6_70
  have w7_74 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m7]; exact w6_74
  have w7_78 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m7]; exact w6_78
  have w7_7c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m7]; exact w6_7c
  have w7_80 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m7]; exact w6_80
  have w7_84 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m7]; exact w6_84
  have w7_180 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m7]; exact w6_180
  have w7_184 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m7]; exact w6_184
  have w7_a20 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (rp) + BitVec.ofNat 32 tl6.header := by rw [m7]; exact w6_a20
  have w7_a24 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl6.len := by rw [m7]; exact w6_a24
  have w7_a28 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = rp := by rw [m7]; exact w6_a28
  have w7_a2c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m7]; exact w6_a2c
  have b7_a30 : n7.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m7]; exact b6_a30
  clear b6_a30 w6_a2c w6_a28 w6_a24 w6_a20 w6_184 w6_180 w6_84 w6_80 w6_7c w6_78 w6_74 w6_70 w6_6c w6_68 w6_64 w6_60 d12_6 d8_6 o16_6 o12_6 o8_6 o4_6 o0_6 g6_27 g6_26 g6_25 g6_24 g6_23 g6_22 g6_21 g6_19 g6_18 g6_10 g6_9 g6_8 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 Er6 Ok6 K6 rk6 s6 c6
  -- 0x288: branch, not taken
  obtain ⟨n8, d8, u8⟩ := s7.notTaken E7.self 0x28C sv_at_288
    (by decide) (by rw [g7_10, s7.zero]; exact br_beq_f (tb_in.ok_ne hr6))
  have s8 : St n8.mem SV n8 0x28C (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans (.single d8)
  have fR8 : ∀ x, SvR B x → n8.mem x = n0.mem x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, g7_4]
  have g8_8 : reg n8 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u8.regs, g7_8]
  have g8_9 : reg n8 (9 : Fin 32) = trp := by rw [u8.regs, g7_9]
  have g8_10 : reg n8 a0 = (rp) + BitVec.ofNat 32 tl6.header := by rw [u8.regs, g7_10]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, g7_19]
  have g8_21 : reg n8 (21 : Fin 32) = lp := by rw [u8.regs, g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = orp := by rw [u8.regs, g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = tcl := by rw [u8.regs, g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = sgl := by rw [u8.regs, g7_24]
  have g8_25 : reg n8 (25 : Fin 32) = orl := by rw [u8.regs, g7_25]
  have g8_26 : reg n8 (26 : Fin 32) = ll := by rw [u8.regs, g7_26]
  have g8_27 : reg n8 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u8.regs, g7_27]
  have w8_60 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m8]; exact w7_60
  have w8_64 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m8]; exact w7_64
  have w8_68 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m8]; exact w7_68
  have w8_6c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m8]; exact w7_6c
  have w8_70 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m8]; exact w7_70
  have w8_74 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m8]; exact w7_74
  have w8_78 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m8]; exact w7_78
  have w8_7c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m8]; exact w7_7c
  have w8_80 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m8]; exact w7_80
  have w8_84 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m8]; exact w7_84
  have w8_180 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m8]; exact w7_180
  have w8_184 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m8]; exact w7_184
  have w8_a20 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (rp) + BitVec.ofNat 32 tl6.header := by rw [m8]; exact w7_a20
  have w8_a24 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl6.len := by rw [m8]; exact w7_a24
  have w8_a28 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = rp := by rw [m8]; exact w7_a28
  have w8_a2c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m8]; exact w7_a2c
  have b8_a30 : n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m8]; exact b7_a30
  clear b7_a30 w7_a2c w7_a28 w7_a24 w7_a20 w7_184 w7_180 w7_84 w7_80 w7_7c w7_78 w7_74 w7_70 w7_6c w7_68 w7_64 w7_60 g7_10 g7_27 g7_26 g7_25 g7_24 g7_23 g7_22 g7_21 g7_19 g7_18 g7_9 g7_8 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 m7 s7 u7 d7
  -- 0x28C: lw
  obtain ⟨n9, d9, u9⟩ := s8.lw E8.self sv_at_28c (off' := 0x290) (by decide)
    (by rw [g8_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s9 : St n9.mem SV n9 0x290 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have fr9 : ∀ x, SvR B x → n9.mem x = n8.mem x := fun x _ => by rw [m9]
  have t9 : Steps n0 n9 := t8.trans (.single d9)
  have fR9 : ∀ x, SvR B x → n9.mem x = n0.mem x := fun x hx => (fr9 x hx).trans (fR8 x hx)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have V9 : SvSaves B n9.mem v := V8.same m9
  have g9_2 : reg n9 sp = B + 0x21A0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_2]
  have g9_3 : reg n9 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_3]
  have g9_4 : reg n9 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u9.regs, upd_ne (by decide) (by decide), g8_4]
  have g9_8 : reg n9 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_8]
  have g9_9 : reg n9 (9 : Fin 32) = trp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_9]
  have g9_18 : reg n9 (18 : Fin 32) = out := by rw [u9.regs, upd_ne (by decide) (by decide), g8_18]
  have g9_19 : reg n9 (19 : Fin 32) = bp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_19]
  have g9_21 : reg n9 (21 : Fin 32) = lp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_21]
  have g9_22 : reg n9 (22 : Fin 32) = orp := by rw [u9.regs, upd_ne (by decide) (by decide), g8_22]
  have g9_23 : reg n9 (23 : Fin 32) = tcl := by rw [u9.regs, upd_ne (by decide) (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = sgl := by rw [u9.regs, upd_ne (by decide) (by decide), g8_24]
  have g9_25 : reg n9 (25 : Fin 32) = orl := by rw [u9.regs, upd_ne (by decide) (by decide), g8_25]
  have g9_26 : reg n9 (26 : Fin 32) = ll := by rw [u9.regs, upd_ne (by decide) (by decide), g8_26]
  have g9_27 : reg n9 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u9.regs, upd_ne (by decide) (by decide), g8_27]
  have g9_10 : reg n9 a0 = rp := by
    rw [u9.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g8_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr, w8_a28]
  have w9_60 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m9]; exact w8_60
  have w9_64 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m9]; exact w8_64
  have w9_68 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m9]; exact w8_68
  have w9_6c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m9]; exact w8_6c
  have w9_70 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m9]; exact w8_70
  have w9_74 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m9]; exact w8_74
  have w9_78 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m9]; exact w8_78
  have w9_7c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m9]; exact w8_7c
  have w9_80 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m9]; exact w8_80
  have w9_84 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m9]; exact w8_84
  have w9_180 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m9]; exact w8_180
  have w9_184 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m9]; exact w8_184
  have w9_a20 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (rp) + BitVec.ofNat 32 tl6.header := by rw [m9]; exact w8_a20
  have w9_a24 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl6.len := by rw [m9]; exact w8_a24
  have w9_a28 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = rp := by rw [m9]; exact w8_a28
  have w9_a2c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m9]; exact w8_a2c
  have b9_a30 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m9]; exact b8_a30
  clear b8_a30 w8_a2c w8_a28 w8_a24 w8_a20 w8_184 w8_180 w8_84 w8_80 w8_7c w8_78 w8_74 w8_70 w8_6c w8_68 w8_64 w8_60 g8_27 g8_26 g8_25 g8_24 g8_23 g8_22 g8_21 g8_19 g8_18 g8_10 g8_9 g8_8 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8
  -- 0x290: sw
  obtain ⟨n10, d10, s10, fr10, K10, W10, rg10⟩ := sv_sw F E9 s9 sv_at_290 (off' := 0x292) (c := 0x5C)
    (by decide) (by rw [g9_2]; sv_addr) (by decide) (by decide)
  have t10 : Steps n0 n10 := t9.trans d10
  have fR10 : ∀ x, SvR B x → n10.mem x = n0.mem x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.keep K10 (by decide)
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [rg10 sp, g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg10 (3 : Fin 32), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg10 (4 : Fin 32), g9_4]
  have g10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rg10 (8 : Fin 32), g9_8]
  have g10_9 : reg n10 (9 : Fin 32) = trp := by rw [rg10 (9 : Fin 32), g9_9]
  have g10_10 : reg n10 a0 = rp := by rw [rg10 a0, g9_10]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [rg10 (18 : Fin 32), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [rg10 (19 : Fin 32), g9_19]
  have g10_21 : reg n10 (21 : Fin 32) = lp := by rw [rg10 (21 : Fin 32), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = orp := by rw [rg10 (22 : Fin 32), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = tcl := by rw [rg10 (23 : Fin 32), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = sgl := by rw [rg10 (24 : Fin 32), g9_24]
  have g10_25 : reg n10 (25 : Fin 32) = orl := by rw [rg10 (25 : Fin 32), g9_25]
  have g10_26 : reg n10 (26 : Fin 32) = ll := by rw [rg10 (26 : Fin 32), g9_26]
  have g10_27 : reg n10 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg10 (27 : Fin 32), g9_27]
  have w10_60 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K10.w32 (by decide) (by decide)).trans w9_60
  have w10_64 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := (K10.w32 (by decide) (by decide)).trans w9_64
  have w10_68 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K10.w32 (by decide) (by decide)).trans w9_68
  have w10_6c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K10.w32 (by decide) (by decide)).trans w9_6c
  have w10_70 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K10.w32 (by decide) (by decide)).trans w9_70
  have w10_74 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K10.w32 (by decide) (by decide)).trans w9_74
  have w10_78 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K10.w32 (by decide) (by decide)).trans w9_78
  have w10_7c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K10.w32 (by decide) (by decide)).trans w9_7c
  have w10_80 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K10.w32 (by decide) (by decide)).trans w9_80
  have w10_84 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K10.w32 (by decide) (by decide)).trans w9_84
  have w10_180 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl6.header + tl6.len) := (K10.w32 (by decide) (by decide)).trans w9_180
  have w10_184 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl6.header + tl6.len) := (K10.w32 (by decide) (by decide)).trans w9_184
  have w10_a20 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (rp) + BitVec.ofNat 32 tl6.header := (K10.w32 (by decide) (by decide)).trans w9_a20
  have w10_a24 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl6.len := (K10.w32 (by decide) (by decide)).trans w9_a24
  have w10_a28 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = rp := (K10.w32 (by decide) (by decide)).trans w9_a28
  have w10_a2c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl6.header + tl6.len) := (K10.w32 (by decide) (by decide)).trans w9_a2c
  have b10_a30 : n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := (K10.b8 (by decide) (by decide)).trans b9_a30
  have w10_5c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [W10, g9_10]
  clear b9_a30 w9_a2c w9_a28 w9_a24 w9_a20 w9_184 w9_180 w9_84 w9_80 w9_7c w9_78 w9_74 w9_70 w9_6c w9_68 w9_64 w9_60 g9_10 g9_27 g9_26 g9_25 g9_24 g9_23 g9_22 g9_21 g9_19 g9_18 g9_9 g9_8 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 m9 s9 u9 d9
  -- 0x292: lw
  obtain ⟨n11, d11, u11⟩ := s10.lw E10.self sv_at_292 (off' := 0x296) (by decide)
    (by rw [g10_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0xC = B + 0x21A0 + BitVec.ofNat 32 0xA2C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s11 : St n11.mem SV n11 0x296 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = n0.mem x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_4]
  have g11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_8]
  have g11_9 : reg n11 (9 : Fin 32) = trp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_9]
  have g11_10 : reg n11 a0 = rp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_10]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, upd_ne (by decide) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_19]
  have g11_21 : reg n11 (21 : Fin 32) = lp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = orp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = tcl := by rw [u11.regs, upd_ne (by decide) (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = sgl := by rw [u11.regs, upd_ne (by decide) (by decide), g10_24]
  have g11_26 : reg n11 (26 : Fin 32) = ll := by rw [u11.regs, upd_ne (by decide) (by decide), g10_26]
  have g11_27 : reg n11 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_27]
  have g11_25 : reg n11 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by
    rw [u11.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g10_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0xC = B + 0x21A0 + BitVec.ofNat 32 0xA2C by sv_addr, w10_a2c]
  have w11_5c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m11]; exact w10_5c
  have w11_60 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m11]; exact w10_60
  have w11_64 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m11]; exact w10_64
  have w11_68 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m11]; exact w10_68
  have w11_6c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m11]; exact w10_6c
  have w11_70 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m11]; exact w10_70
  have w11_74 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m11]; exact w10_74
  have w11_78 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m11]; exact w10_78
  have w11_7c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m11]; exact w10_7c
  have w11_80 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m11]; exact w10_80
  have w11_84 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m11]; exact w10_84
  have w11_180 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m11]; exact w10_180
  have w11_184 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m11]; exact w10_184
  have w11_a20 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (rp) + BitVec.ofNat 32 tl6.header := by rw [m11]; exact w10_a20
  have w11_a24 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl6.len := by rw [m11]; exact w10_a24
  have w11_a28 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = rp := by rw [m11]; exact w10_a28
  have w11_a2c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m11]; exact w10_a2c
  have b11_a30 : n11.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m11]; exact b10_a30
  clear w10_5c b10_a30 w10_a2c w10_a28 w10_a24 w10_a20 w10_184 w10_180 w10_84 w10_80 w10_7c w10_78 w10_74 w10_70 w10_6c w10_68 w10_64 w10_60 g10_27 g10_26 g10_25 g10_24 g10_23 g10_22 g10_21 g10_19 g10_18 g10_10 g10_9 g10_8 g10_4 g10_3 g10_2 V10 E10 fR10 t10 rg10 W10 K10 fr10 s10 d10
  -- 0x296
  obtain ⟨n12, c12, u12⟩ := s11.block svL4296 E11.self svL4296_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have s12 : St n12.mem SV n12 0x2A0 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have rb12 : ∀ q, reg n12 q = (runBlock svL4296 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans c12
  have fR12 : ∀ x, SvR B x → n12.mem x = n0.mem x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by
    rw [rb12, runBlock_reg _ _ _ sp s11.zero (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb12, runBlock_reg _ _ _ (3 : Fin 32) s11.zero (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb12, runBlock_reg _ _ _ (4 : Fin 32) s11.zero (by decide), g11_4]
  have g12_8 : reg n12 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by
    rw [rb12, runBlock_reg _ _ _ (8 : Fin 32) s11.zero (by decide), g11_8]
  have g12_9 : reg n12 (9 : Fin 32) = trp := by
    rw [rb12, runBlock_reg _ _ _ (9 : Fin 32) s11.zero (by decide), g11_9]
  have g12_18 : reg n12 (18 : Fin 32) = out := by
    rw [rb12, runBlock_reg _ _ _ (18 : Fin 32) s11.zero (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by
    rw [rb12, runBlock_reg _ _ _ (19 : Fin 32) s11.zero (by decide), g11_19]
  have g12_21 : reg n12 (21 : Fin 32) = lp := by
    rw [rb12, runBlock_reg _ _ _ (21 : Fin 32) s11.zero (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = orp := by
    rw [rb12, runBlock_reg _ _ _ (22 : Fin 32) s11.zero (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = tcl := by
    rw [rb12, runBlock_reg _ _ _ (23 : Fin 32) s11.zero (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = sgl := by
    rw [rb12, runBlock_reg _ _ _ (24 : Fin 32) s11.zero (by decide), g11_24]
  have g12_25 : reg n12 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by
    rw [rb12, runBlock_reg _ _ _ (25 : Fin 32) s11.zero (by decide), g11_25]
  have g12_26 : reg n12 (26 : Fin 32) = ll := by
    rw [rb12, runBlock_reg _ _ _ (26 : Fin 32) s11.zero (by decide), g11_26]
  have g12_27 : reg n12 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb12, runBlock_reg _ _ _ (27 : Fin 32) s11.zero (by decide), g11_27]
  have g12_10 : reg n12 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svL4296, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_18, g11_19, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g12_11 : reg n12 a1 = B + 0x21A0 + BitVec.ofNat 32 0x178 := by
    rw [rb12]; simp +decide only [runBlock, BInstr.run, svL4296, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g11_2, g11_3, g11_4, g11_8, g11_9, g11_10, g11_18, g11_19, g11_21, g11_22, g11_23, g11_24, g11_25, g11_26, g11_27, s11.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w12_5c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m12]; exact w11_5c
  have w12_60 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m12]; exact w11_60
  have w12_64 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m12]; exact w11_64
  have w12_68 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m12]; exact w11_68
  have w12_6c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m12]; exact w11_6c
  have w12_70 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m12]; exact w11_70
  have w12_74 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m12]; exact w11_74
  have w12_78 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m12]; exact w11_78
  have w12_7c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m12]; exact w11_7c
  have w12_80 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m12]; exact w11_80
  have w12_84 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m12]; exact w11_84
  have w12_180 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = (rp) + BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m12]; exact w11_180
  have w12_184 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (rl) - BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m12]; exact w11_184
  have w12_a20 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (rp) + BitVec.ofNat 32 tl6.header := by rw [m12]; exact w11_a20
  have w12_a24 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl6.len := by rw [m12]; exact w11_a24
  have w12_a28 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = rp := by rw [m12]; exact w11_a28
  have w12_a2c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [m12]; exact w11_a2c
  have b12_a30 : n12.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m12]; exact b11_a30
  clear b11_a30 w11_a2c w11_a28 w11_a24 w11_a20 w11_184 w11_180 w11_84 w11_80 w11_7c w11_78 w11_74 w11_70 w11_6c w11_68 w11_64 w11_60 w11_5c g11_25 g11_27 g11_26 g11_24 g11_23 g11_22 g11_21 g11_19 g11_18 g11_10 g11_9 g11_8 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  -- 0x2A0: sv_seqF
  obtain ⟨n13, c13, s13, sp13, rk13, K13, Ok13, Er13, fr13⟩ := sv_seqF (oc := 0xA20) (dc := 0x178)
    F E12 s12 sv_at_2a0 sv_at_2a4 (by decide) (by decide) g12_2 g12_10 g12_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w12_180 w12_184 (tb_in.restW hr6)
  have t13 : Steps n0 n13 := t12.trans c13
  have fR13 : ∀ x, SvR B x → n13.mem x = n0.mem x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.keepL K13 (by decide)
  rw [sv_mb fR12 (tb_in.restW hr6)] at Ok13 Er13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [rk13 sp (by decide) (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk13 (3 : Fin 32) (by decide) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk13 (4 : Fin 32) (by decide) (by decide), g12_4]
  have g13_8 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 0x0 := by rw [rk13 (8 : Fin 32) (by decide) (by decide), g12_8]
  have g13_9 : reg n13 (9 : Fin 32) = trp := by rw [rk13 (9 : Fin 32) (by decide) (by decide), g12_9]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [rk13 (18 : Fin 32) (by decide) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [rk13 (19 : Fin 32) (by decide) (by decide), g12_19]
  have g13_21 : reg n13 (21 : Fin 32) = lp := by rw [rk13 (21 : Fin 32) (by decide) (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = orp := by rw [rk13 (22 : Fin 32) (by decide) (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = tcl := by rw [rk13 (23 : Fin 32) (by decide) (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = sgl := by rw [rk13 (24 : Fin 32) (by decide) (by decide), g12_24]
  have g13_25 : reg n13 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [rk13 (25 : Fin 32) (by decide) (by decide), g12_25]
  have g13_26 : reg n13 (26 : Fin 32) = ll := by rw [rk13 (26 : Fin 32) (by decide) (by decide), g12_26]
  have g13_27 : reg n13 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk13 (27 : Fin 32) (by decide) (by decide), g12_27]
  obtain ⟨r13, hr13⟩ : ∃ r, derElement 0x30 (memBytes n0.mem ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)).toNat) = r := ⟨_, rfl⟩
  rcases r13 with er13 | tl13
  · obtain ⟨z13, -⟩ := Er13 er13 hr13
    have w13_5c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := (K13.w32 (by decide) (by decide)).trans w12_5c
    have w13_60 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K13.w32 (by decide) (by decide)).trans w12_60
    have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := (K13.w32 (by decide) (by decide)).trans w12_64
    have w13_68 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K13.w32 (by decide) (by decide)).trans w12_68
    have w13_6c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K13.w32 (by decide) (by decide)).trans w12_6c
    have w13_70 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K13.w32 (by decide) (by decide)).trans w12_70
    have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K13.w32 (by decide) (by decide)).trans w12_74
    have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K13.w32 (by decide) (by decide)).trans w12_78
    have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K13.w32 (by decide) (by decide)).trans w12_7c
    have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K13.w32 (by decide) (by decide)).trans w12_80
    have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K13.w32 (by decide) (by decide)).trans w12_84
    have b13_a30 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := (K13.b8 (by decide) (by decide)).trans b12_a30
    have w13_a20 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := z13
    clear b12_a30 w12_a2c w12_a28 w12_a24 w12_a20 w12_184 w12_180 w12_84 w12_80 w12_7c w12_78 w12_74 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c g12_11 g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
    -- 0x2A8: lw
    obtain ⟨n14, d14, u14⟩ := s13.lw E13.self sv_at_2a8 (off' := 0x2AC) (by decide)
      (by rw [g13_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
    have s14 : St n14.mem SV n14 0x2AC (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
    have m14 : n14.mem = n13.mem := u14.mem
    have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
    have t14 : Steps n0 n14 := t13.trans (.single d14)
    have fR14 : ∀ x, SvR B x → n14.mem x = n0.mem x := fun x hx => (fr14 x hx).trans (fR13 x hx)
    have E14 : SvCode n14.mem := E13.fr F fr14
    have V14 : SvSaves B n14.mem v := V13.same m14
    have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_2]
    have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_3]
    have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_4]
    have g14_9 : reg n14 (9 : Fin 32) = trp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_9]
    have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, upd_ne (by decide) (by decide), g13_18]
    have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_19]
    have g14_21 : reg n14 (21 : Fin 32) = lp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_21]
    have g14_22 : reg n14 (22 : Fin 32) = orp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_22]
    have g14_23 : reg n14 (23 : Fin 32) = tcl := by rw [u14.regs, upd_ne (by decide) (by decide), g13_23]
    have g14_24 : reg n14 (24 : Fin 32) = sgl := by rw [u14.regs, upd_ne (by decide) (by decide), g13_24]
    have g14_25 : reg n14 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_25]
    have g14_26 : reg n14 (26 : Fin 32) = ll := by rw [u14.regs, upd_ne (by decide) (by decide), g13_26]
    have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_27]
    have g14_8 : reg n14 (8 : Fin 32) = 0 := by
      rw [u14.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g13_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w13_a20]
    have w14_5c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m14]; exact w13_5c
    have w14_60 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m14]; exact w13_60
    have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m14]; exact w13_64
    have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m14]; exact w13_68
    have w14_6c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m14]; exact w13_6c
    have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m14]; exact w13_70
    have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m14]; exact w13_74
    have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m14]; exact w13_78
    have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m14]; exact w13_7c
    have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m14]; exact w13_80
    have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m14]; exact w13_84
    have w14_a20 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m14]; exact w13_a20
    have b14_a30 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m14]; exact b13_a30
    clear w13_a20 b13_a30 w13_84 w13_80 w13_7c w13_78 w13_74 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c z13
    -- 0x2AC: lbu
    obtain ⟨n15, d15, u15⟩ := s14.lbu E14.self sv_at_2ac (off' := 0x2B0) (by decide)
    have s15 : St n15.mem SV n15 0x2B0 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
    have m15 : n15.mem = n14.mem := u15.mem
    have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
    have t15 : Steps n0 n15 := t14.trans (.single d15)
    have fR15 : ∀ x, SvR B x → n15.mem x = n0.mem x := fun x hx => (fr15 x hx).trans (fR14 x hx)
    have E15 : SvCode n15.mem := E14.fr F fr15
    have V15 : SvSaves B n15.mem v := V14.same m15
    have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_2]
    have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_3]
    have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_4]
    have g15_8 : reg n15 (8 : Fin 32) = 0 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_8]
    have g15_9 : reg n15 (9 : Fin 32) = trp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_9]
    have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, upd_ne (by decide) (by decide), g14_18]
    have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_19]
    have g15_21 : reg n15 (21 : Fin 32) = lp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_21]
    have g15_22 : reg n15 (22 : Fin 32) = orp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_22]
    have g15_23 : reg n15 (23 : Fin 32) = tcl := by rw [u15.regs, upd_ne (by decide) (by decide), g14_23]
    have g15_24 : reg n15 (24 : Fin 32) = sgl := by rw [u15.regs, upd_ne (by decide) (by decide), g14_24]
    have g15_25 : reg n15 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_25]
    have g15_26 : reg n15 (26 : Fin 32) = ll := by rw [u15.regs, upd_ne (by decide) (by decide), g14_26]
    have g15_27 : reg n15 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_27]
    have w15_5c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m15]; exact w14_5c
    have w15_60 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m15]; exact w14_60
    have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m15]; exact w14_64
    have w15_68 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m15]; exact w14_68
    have w15_6c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m15]; exact w14_6c
    have w15_70 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m15]; exact w14_70
    have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m15]; exact w14_74
    have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m15]; exact w14_78
    have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m15]; exact w14_7c
    have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m15]; exact w14_80
    have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m15]; exact w14_84
    have w15_a20 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m15]; exact w14_a20
    have b15_a30 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m15]; exact b14_a30
    clear b14_a30 w14_a20 w14_84 w14_80 w14_7c w14_78 w14_74 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c g14_8 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_19 g14_18 g14_9 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
    -- 0x2B0: branch, taken
    obtain ⟨n16, d16, u16⟩ := s15.taken E15.self 0x966 sv_at_2b0
      (by decide) (by rw [g15_8, s15.zero]; rfl)
    have s16 : St n16.mem SV n16 0x966 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
    have m16 : n16.mem = n15.mem := u16.mem
    have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
    have t16 : Steps n0 n16 := t15.trans (.single d16)
    have fR16 : ∀ x, SvR B x → n16.mem x = n0.mem x := fun x hx => (fr16 x hx).trans (fR15 x hx)
    have E16 : SvCode n16.mem := E15.fr F fr16
    have V16 : SvSaves B n16.mem v := V15.same m16
    have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, g15_2]
    have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, g15_3]
    have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, g15_4]
    have g16_8 : reg n16 (8 : Fin 32) = 0 := by rw [u16.regs, g15_8]
    have g16_9 : reg n16 (9 : Fin 32) = trp := by rw [u16.regs, g15_9]
    have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, g15_18]
    have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, g15_19]
    have g16_21 : reg n16 (21 : Fin 32) = lp := by rw [u16.regs, g15_21]
    have g16_22 : reg n16 (22 : Fin 32) = orp := by rw [u16.regs, g15_22]
    have g16_23 : reg n16 (23 : Fin 32) = tcl := by rw [u16.regs, g15_23]
    have g16_24 : reg n16 (24 : Fin 32) = sgl := by rw [u16.regs, g15_24]
    have g16_25 : reg n16 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u16.regs, g15_25]
    have g16_26 : reg n16 (26 : Fin 32) = ll := by rw [u16.regs, g15_26]
    have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u16.regs, g15_27]
    have w16_5c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m16]; exact w15_5c
    have w16_60 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m16]; exact w15_60
    have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m16]; exact w15_64
    have w16_68 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m16]; exact w15_68
    have w16_6c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m16]; exact w15_6c
    have w16_70 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m16]; exact w15_70
    have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m16]; exact w15_74
    have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m16]; exact w15_78
    have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m16]; exact w15_7c
    have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m16]; exact w15_80
    have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m16]; exact w15_84
    have w16_a20 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = 0 := by rw [m16]; exact w15_a20
    have b16_a30 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m16]; exact b15_a30
    clear b15_a30 w15_a20 w15_84 w15_80 w15_7c w15_78 w15_74 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_19 g15_18 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15
    exact .inl ⟨(fun ⟨tl6', h0', tl13', h1', _⟩ => by rw [hr6] at h0'; cases h0'; rw [hr13] at h1'; cases h1'), sv_fail F E16 s16 t16 fR16 V16 hret g16_2 g16_18 hO g16_3 g16_4⟩
  obtain ⟨o0_13, o4_13, o8_13, o12_13, d8_13, d12_13⟩ := Ok13 tl13 hr13
  have w13_5c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := (K13.w32 (by decide) (by decide)).trans w12_5c
  have w13_60 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K13.w32 (by decide) (by decide)).trans w12_60
  have w13_64 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := (K13.w32 (by decide) (by decide)).trans w12_64
  have w13_68 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K13.w32 (by decide) (by decide)).trans w12_68
  have w13_6c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K13.w32 (by decide) (by decide)).trans w12_6c
  have w13_70 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K13.w32 (by decide) (by decide)).trans w12_70
  have w13_74 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K13.w32 (by decide) (by decide)).trans w12_74
  have w13_78 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K13.w32 (by decide) (by decide)).trans w12_78
  have w13_7c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K13.w32 (by decide) (by decide)).trans w12_7c
  have w13_80 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K13.w32 (by decide) (by decide)).trans w12_80
  have w13_84 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K13.w32 (by decide) (by decide)).trans w12_84
  have b13_a30 : n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := (K13.b8 (by decide) (by decide)).trans b12_a30
  have w13_180 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := d8_13
  have w13_184 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := d12_13
  have w13_a20 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := o0_13
  have w13_a24 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl13.len := o4_13
  have w13_a28 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := o8_13
  have w13_a2c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl13.len := o12_13
  clear b12_a30 w12_a2c w12_a28 w12_a24 w12_a20 w12_184 w12_180 w12_84 w12_80 w12_7c w12_78 w12_74 w12_70 w12_6c w12_68 w12_64 w12_60 w12_5c g12_11 g12_10 g12_27 g12_26 g12_25 g12_24 g12_23 g12_22 g12_21 g12_19 g12_18 g12_9 g12_8 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 rb12 s12 m12 u12 c12
  -- 0x2A8: lw
  obtain ⟨n14, d14, u14⟩ := s13.lw E13.self sv_at_2a8 (off' := 0x2AC) (by decide)
    (by rw [g13_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s14 : St n14.mem SV n14 0x2AC (reg n14) := ⟨u14.pc, rfl, fun _ => rfl⟩
  have m14 : n14.mem = n13.mem := u14.mem
  have fr14 : ∀ x, SvR B x → n14.mem x = n13.mem x := fun x _ => by rw [m14]
  have t14 : Steps n0 n14 := t13.trans (.single d14)
  have fR14 : ∀ x, SvR B x → n14.mem x = n0.mem x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.same m14
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_4]
  have g14_9 : reg n14 (9 : Fin 32) = trp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_9]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [u14.regs, upd_ne (by decide) (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_19]
  have g14_21 : reg n14 (21 : Fin 32) = lp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = orp := by rw [u14.regs, upd_ne (by decide) (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = tcl := by rw [u14.regs, upd_ne (by decide) (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = sgl := by rw [u14.regs, upd_ne (by decide) (by decide), g13_24]
  have g14_25 : reg n14 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u14.regs, upd_ne (by decide) (by decide), g13_25]
  have g14_26 : reg n14 (26 : Fin 32) = ll := by rw [u14.regs, upd_ne (by decide) (by decide), g13_26]
  have g14_27 : reg n14 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u14.regs, upd_ne (by decide) (by decide), g13_27]
  have g14_8 : reg n14 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by
    rw [u14.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g13_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, w13_a20]
  have w14_5c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m14]; exact w13_5c
  have w14_60 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m14]; exact w13_60
  have w14_64 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m14]; exact w13_64
  have w14_68 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m14]; exact w13_68
  have w14_6c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m14]; exact w13_6c
  have w14_70 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m14]; exact w13_70
  have w14_74 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m14]; exact w13_74
  have w14_78 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m14]; exact w13_78
  have w14_7c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m14]; exact w13_7c
  have w14_80 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m14]; exact w13_80
  have w14_84 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m14]; exact w13_84
  have w14_180 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m14]; exact w13_180
  have w14_184 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m14]; exact w13_184
  have w14_a20 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m14]; exact w13_a20
  have w14_a24 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl13.len := by rw [m14]; exact w13_a24
  have w14_a28 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m14]; exact w13_a28
  have w14_a2c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl13.len := by rw [m14]; exact w13_a2c
  have b14_a30 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m14]; exact b13_a30
  clear w13_a2c w13_a28 w13_a24 w13_a20 w13_184 w13_180 b13_a30 w13_84 w13_80 w13_7c w13_78 w13_74 w13_70 w13_6c w13_68 w13_64 w13_60 w13_5c d12_13 d8_13 o12_13 o8_13 o4_13 o0_13 g13_27 g13_26 g13_25 g13_24 g13_23 g13_22 g13_21 g13_19 g13_18 g13_9 g13_8 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 Er13 Ok13 K13 rk13 sp13 s13 c13
  -- 0x2AC: lbu
  obtain ⟨n15, d15, u15⟩ := s14.lbu E14.self sv_at_2ac (off' := 0x2B0) (by decide)
  have b14_a24 : n14.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by
    have h := byte_of_ld w14_a24
    rw [show B + 0x21A0 + BitVec.ofNat 32 0xA24 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr]; exact h.1
  have s15 : St n15.mem SV n15 0x2B0 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = n0.mem x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_4]
  have g15_8 : reg n15 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u15.regs, upd_ne (by decide) (by decide), g14_8]
  have g15_9 : reg n15 (9 : Fin 32) = trp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_9]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, upd_ne (by decide) (by decide), g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_19]
  have g15_21 : reg n15 (21 : Fin 32) = lp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = orp := by rw [u15.regs, upd_ne (by decide) (by decide), g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = tcl := by rw [u15.regs, upd_ne (by decide) (by decide), g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = sgl := by rw [u15.regs, upd_ne (by decide) (by decide), g14_24]
  have g15_25 : reg n15 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u15.regs, upd_ne (by decide) (by decide), g14_25]
  have g15_26 : reg n15 (26 : Fin 32) = ll := by rw [u15.regs, upd_ne (by decide) (by decide), g14_26]
  have g15_27 : reg n15 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u15.regs, upd_ne (by decide) (by decide), g14_27]
  have g15_20 : reg n15 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [u15.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g14_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x4 = B + 0x21A0 + BitVec.ofNat 32 0xA24 by sv_addr, b14_a24]
  have w15_5c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m15]; exact w14_5c
  have w15_60 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m15]; exact w14_60
  have w15_64 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m15]; exact w14_64
  have w15_68 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m15]; exact w14_68
  have w15_6c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m15]; exact w14_6c
  have w15_70 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m15]; exact w14_70
  have w15_74 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m15]; exact w14_74
  have w15_78 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m15]; exact w14_78
  have w15_7c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m15]; exact w14_7c
  have w15_80 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m15]; exact w14_80
  have w15_84 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m15]; exact w14_84
  have w15_180 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m15]; exact w14_180
  have w15_184 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m15]; exact w14_184
  have w15_a20 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m15]; exact w14_a20
  have w15_a24 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl13.len := by rw [m15]; exact w14_a24
  have w15_a28 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m15]; exact w14_a28
  have w15_a2c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl13.len := by rw [m15]; exact w14_a2c
  have b15_a24 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m15]; exact b14_a24
  have b15_a30 : n15.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m15]; exact b14_a30
  clear b14_a30 w14_a2c w14_a28 w14_a24 w14_a20 w14_184 w14_180 w14_84 w14_80 w14_7c w14_78 w14_74 w14_70 w14_6c w14_68 w14_64 w14_60 w14_5c g14_8 g14_27 g14_26 g14_25 g14_24 g14_23 g14_22 g14_21 g14_19 g14_18 g14_9 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 m14 s14 u14 d14
  -- 0x2B0: branch, not taken
  obtain ⟨n16, d16, u16⟩ := s15.notTaken E15.self 0x2B4 sv_at_2b0
    (by decide) (by rw [g15_8, s15.zero]; exact br_beq_f ((tb_in.restW hr6).ok_ne hr13))
  have s16 : St n16.mem SV n16 0x2B4 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have fr16 : ∀ x, SvR B x → n16.mem x = n15.mem x := fun x _ => by rw [m16]
  have t16 : Steps n0 n16 := t15.trans (.single d16)
  have fR16 : ∀ x, SvR B x → n16.mem x = n0.mem x := fun x hx => (fr16 x hx).trans (fR15 x hx)
  have E16 : SvCode n16.mem := E15.fr F fr16
  have V16 : SvSaves B n16.mem v := V15.same m16
  have g16_2 : reg n16 sp = B + 0x21A0 := by rw [u16.regs, g15_2]
  have g16_3 : reg n16 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u16.regs, g15_3]
  have g16_4 : reg n16 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u16.regs, g15_4]
  have g16_8 : reg n16 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u16.regs, g15_8]
  have g16_9 : reg n16 (9 : Fin 32) = trp := by rw [u16.regs, g15_9]
  have g16_18 : reg n16 (18 : Fin 32) = out := by rw [u16.regs, g15_18]
  have g16_19 : reg n16 (19 : Fin 32) = bp := by rw [u16.regs, g15_19]
  have g16_20 : reg n16 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [u16.regs, g15_20]
  have g16_21 : reg n16 (21 : Fin 32) = lp := by rw [u16.regs, g15_21]
  have g16_22 : reg n16 (22 : Fin 32) = orp := by rw [u16.regs, g15_22]
  have g16_23 : reg n16 (23 : Fin 32) = tcl := by rw [u16.regs, g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = sgl := by rw [u16.regs, g15_24]
  have g16_25 : reg n16 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u16.regs, g15_25]
  have g16_26 : reg n16 (26 : Fin 32) = ll := by rw [u16.regs, g15_26]
  have g16_27 : reg n16 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u16.regs, g15_27]
  have w16_5c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m16]; exact w15_5c
  have w16_60 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m16]; exact w15_60
  have w16_64 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m16]; exact w15_64
  have w16_68 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m16]; exact w15_68
  have w16_6c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m16]; exact w15_6c
  have w16_70 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m16]; exact w15_70
  have w16_74 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m16]; exact w15_74
  have w16_78 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m16]; exact w15_78
  have w16_7c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m16]; exact w15_7c
  have w16_80 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m16]; exact w15_80
  have w16_84 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m16]; exact w15_84
  have w16_180 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m16]; exact w15_180
  have w16_184 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m16]; exact w15_184
  have w16_a20 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m16]; exact w15_a20
  have w16_a24 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl13.len := by rw [m16]; exact w15_a24
  have w16_a28 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m16]; exact w15_a28
  have w16_a2c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl13.len := by rw [m16]; exact w15_a2c
  have b16_a24 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m16]; exact b15_a24
  have b16_a30 : n16.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m16]; exact b15_a30
  clear b15_a30 b15_a24 w15_a2c w15_a28 w15_a24 w15_a20 w15_184 w15_180 w15_84 w15_80 w15_7c w15_78 w15_74 w15_70 w15_6c w15_68 w15_64 w15_60 w15_5c g15_20 g15_27 g15_26 g15_25 g15_24 g15_23 g15_22 g15_21 g15_19 g15_18 g15_9 g15_8 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 b14_a24 u15 d15
  -- 0x2B4
  obtain ⟨n17, c17, u17⟩ := s16.block svL42b4 E16.self svL42b4_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have s17 : St n17.mem SV n17 0x2C2 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have rb17 : ∀ q, reg n17 q = (runBlock svL42b4 (n16.mem, reg n16)).2 q := fun q => by rw [u17.regs]
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
  have g17_8 : reg n17 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by
    rw [rb17, runBlock_reg _ _ _ (8 : Fin 32) s16.zero (by decide), g16_8]
  have g17_9 : reg n17 (9 : Fin 32) = trp := by
    rw [rb17, runBlock_reg _ _ _ (9 : Fin 32) s16.zero (by decide), g16_9]
  have g17_18 : reg n17 (18 : Fin 32) = out := by
    rw [rb17, runBlock_reg _ _ _ (18 : Fin 32) s16.zero (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by
    rw [rb17, runBlock_reg _ _ _ (19 : Fin 32) s16.zero (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb17, runBlock_reg _ _ _ (20 : Fin 32) s16.zero (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = lp := by
    rw [rb17, runBlock_reg _ _ _ (21 : Fin 32) s16.zero (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = orp := by
    rw [rb17, runBlock_reg _ _ _ (22 : Fin 32) s16.zero (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = tcl := by
    rw [rb17, runBlock_reg _ _ _ (23 : Fin 32) s16.zero (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = sgl := by
    rw [rb17, runBlock_reg _ _ _ (24 : Fin 32) s16.zero (by decide), g16_24]
  have g17_25 : reg n17 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by
    rw [rb17, runBlock_reg _ _ _ (25 : Fin 32) s16.zero (by decide), g16_25]
  have g17_26 : reg n17 (26 : Fin 32) = ll := by
    rw [rb17, runBlock_reg _ _ _ (26 : Fin 32) s16.zero (by decide), g16_26]
  have g17_27 : reg n17 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb17, runBlock_reg _ _ _ (27 : Fin 32) s16.zero (by decide), g16_27]
  have g17_10 : reg n17 a0 = B + 0x21A0 + BitVec.ofNat 32 0x245 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svL42b4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g17_11 : reg n17 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA25 := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svL42b4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g17_12 : reg n17 a2 = BitVec.ofNat 32 0xB := by
    rw [rb17]; simp +decide only [runBlock, BInstr.run, svL42b4, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g16_2, g16_3, g16_4, g16_8, g16_9, g16_18, g16_19, g16_20, g16_21, g16_22, g16_23, g16_24, g16_25, g16_26, g16_27, s16.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w17_5c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m17]; exact w16_5c
  have w17_60 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m17]; exact w16_60
  have w17_64 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m17]; exact w16_64
  have w17_68 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m17]; exact w16_68
  have w17_6c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m17]; exact w16_6c
  have w17_70 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m17]; exact w16_70
  have w17_74 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m17]; exact w16_74
  have w17_78 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m17]; exact w16_78
  have w17_7c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m17]; exact w16_7c
  have w17_80 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m17]; exact w16_80
  have w17_84 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m17]; exact w16_84
  have w17_180 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m17]; exact w16_180
  have w17_184 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m17]; exact w16_184
  have w17_a20 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m17]; exact w16_a20
  have w17_a24 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl13.len := by rw [m17]; exact w16_a24
  have w17_a28 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m17]; exact w16_a28
  have w17_a2c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl13.len := by rw [m17]; exact w16_a2c
  have b17_a24 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m17]; exact b16_a24
  have b17_a30 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m17]; exact b16_a30
  clear b16_a30 b16_a24 w16_a2c w16_a28 w16_a24 w16_a20 w16_184 w16_180 w16_84 w16_80 w16_7c w16_78 w16_74 w16_70 w16_6c w16_68 w16_64 w16_60 w16_5c g16_27 g16_26 g16_25 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_9 g16_8 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 m16 s16 u16 d16
  have b17_a25 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA25) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by
    have h := byte_of_ld w17_a24
    rw [show B + 0x21A0 + BitVec.ofNat 32 0xA25 = B + 0x21A0 + BitVec.ofNat 32 0xA24 + 1 by sv_addr]; exact h.2.1
  have b17_a26 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA26) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by
    have h := byte_of_ld w17_a24
    rw [show B + 0x21A0 + BitVec.ofNat 32 0xA26 = B + 0x21A0 + BitVec.ofNat 32 0xA24 + 2 by sv_addr]; exact h.2.2.1
  have b17_a27 : n17.mem (B + 0x21A0 + BitVec.ofNat 32 0xA27) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by
    have h := byte_of_ld w17_a24
    rw [show B + 0x21A0 + BitVec.ofNat 32 0xA27 = B + 0x21A0 + BitVec.ofNat 32 0xA24 + 3 by sv_addr]; exact h.2.2.2
  -- 0x2C2: memcpy
  obtain ⟨n18, P18, K18, X18⟩ := sv_mc (c := 0x245) (d := 0xA25) (N := 0xB) F E17 s17 sv_at_2c2 sv_at_2c6
    (by decide) (by decide) g17_2 g17_10 g17_11 g17_12
    (by decide) (by decide) (by decide)
  have s18 := P18.st
  have fr18 := P18.fr
  have t18 : Steps n0 n18 := t17.trans P18.steps
  have fR18 : ∀ x, SvR B x → n18.mem x = n0.mem x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.keep K18 (by decide)
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [P18.regs sp (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P18.regs (3 : Fin 32) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P18.regs (4 : Fin 32) (by decide), g17_4]
  have g18_8 : reg n18 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [P18.regs (8 : Fin 32) (by decide), g17_8]
  have g18_9 : reg n18 (9 : Fin 32) = trp := by rw [P18.regs (9 : Fin 32) (by decide), g17_9]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [P18.regs (18 : Fin 32) (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [P18.regs (19 : Fin 32) (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [P18.regs (20 : Fin 32) (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = lp := by rw [P18.regs (21 : Fin 32) (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = orp := by rw [P18.regs (22 : Fin 32) (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = tcl := by rw [P18.regs (23 : Fin 32) (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = sgl := by rw [P18.regs (24 : Fin 32) (by decide), g17_24]
  have g18_25 : reg n18 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [P18.regs (25 : Fin 32) (by decide), g17_25]
  have g18_26 : reg n18 (26 : Fin 32) = ll := by rw [P18.regs (26 : Fin 32) (by decide), g17_26]
  have g18_27 : reg n18 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [P18.regs (27 : Fin 32) (by decide), g17_27]
  have w18_5c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := (K18.w32 (by decide) (by decide)).trans w17_5c
  have w18_60 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K18.w32 (by decide) (by decide)).trans w17_60
  have w18_64 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := (K18.w32 (by decide) (by decide)).trans w17_64
  have w18_68 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K18.w32 (by decide) (by decide)).trans w17_68
  have w18_6c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K18.w32 (by decide) (by decide)).trans w17_6c
  have w18_70 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K18.w32 (by decide) (by decide)).trans w17_70
  have w18_74 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K18.w32 (by decide) (by decide)).trans w17_74
  have w18_78 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K18.w32 (by decide) (by decide)).trans w17_78
  have w18_7c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K18.w32 (by decide) (by decide)).trans w17_7c
  have w18_80 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K18.w32 (by decide) (by decide)).trans w17_80
  have w18_84 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K18.w32 (by decide) (by decide)).trans w17_84
  have w18_180 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K18.w32 (by decide) (by decide)).trans w17_180
  have w18_184 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K18.w32 (by decide) (by decide)).trans w17_184
  have w18_a20 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := (K18.w32 (by decide) (by decide)).trans w17_a20
  have w18_a24 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl13.len := (K18.w32 (by decide) (by decide)).trans w17_a24
  have w18_a28 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := (K18.w32 (by decide) (by decide)).trans w17_a28
  have w18_a2c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl13.len := (K18.w32 (by decide) (by decide)).trans w17_a2c
  have b18_a24 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := (K18.b8 (by decide) (by decide)).trans b17_a24
  have b18_a25 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA25) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K18.b8 (by decide) (by decide)).trans b17_a25
  have b18_a26 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA26) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K18.b8 (by decide) (by decide)).trans b17_a26
  have b18_a27 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA27) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K18.b8 (by decide) (by decide)).trans b17_a27
  have b18_a30 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := (K18.b8 (by decide) (by decide)).trans b17_a30
  have w18_248 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by
    rw [← w17_a28]
    exact ld_cp fun q hq => by
      have := X18 (0x3 + q) (by omega)
      rwa [show 0x245 + (0x3 + q) = 0x248 + q by omega,
        show 0xA25 + (0x3 + q) = 0xA28 + q by omega] at this
  have w18_24c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 tl13.len := by
    rw [← w17_a2c]
    exact ld_cp fun q hq => by
      have := X18 (0x7 + q) (by omega)
      rwa [show 0x245 + (0x7 + q) = 0x24C + q by omega,
        show 0xA25 + (0x7 + q) = 0xA2C + q by omega] at this
  have b18_245 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [show 0x245 = 0x245 + 0x0 from rfl, X18 0x0 (by decide)]; exact b17_a25
  have b18_246 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [show 0x246 = 0x245 + 0x1 from rfl, X18 0x1 (by decide)]; exact b17_a26
  have b18_247 : n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [show 0x247 = 0x245 + 0x2 from rfl, X18 0x2 (by decide)]; exact b17_a27
  clear b17_a30 b17_a24 w17_a2c w17_a28 w17_a24 w17_a20 w17_184 w17_180 w17_84 w17_80 w17_7c w17_78 w17_74 w17_70 w17_6c w17_68 w17_64 w17_60 w17_5c g17_12 g17_11 g17_10 g17_27 g17_26 g17_25 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_9 g17_8 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 rb17 s17 m17 u17 c17
  -- 0x2CA: sw
  obtain ⟨n19, d19, s19, fr19, K19, W19, rg19⟩ := sv_sw F E18 s18 sv_at_2ca (off' := 0x2CE) (c := 0x240)
    (by decide) (by rw [g18_2]; sv_addr) (by decide) (by decide)
  have t19 : Steps n0 n19 := t18.trans d19
  have fR19 : ∀ x, SvR B x → n19.mem x = n0.mem x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.keep K19 (by decide)
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [rg19 sp, g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg19 (3 : Fin 32), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg19 (4 : Fin 32), g18_4]
  have g19_8 : reg n19 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [rg19 (8 : Fin 32), g18_8]
  have g19_9 : reg n19 (9 : Fin 32) = trp := by rw [rg19 (9 : Fin 32), g18_9]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [rg19 (18 : Fin 32), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [rg19 (19 : Fin 32), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg19 (20 : Fin 32), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = lp := by rw [rg19 (21 : Fin 32), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = orp := by rw [rg19 (22 : Fin 32), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = tcl := by rw [rg19 (23 : Fin 32), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = sgl := by rw [rg19 (24 : Fin 32), g18_24]
  have g19_25 : reg n19 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [rg19 (25 : Fin 32), g18_25]
  have g19_26 : reg n19 (26 : Fin 32) = ll := by rw [rg19 (26 : Fin 32), g18_26]
  have g19_27 : reg n19 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg19 (27 : Fin 32), g18_27]
  have w19_5c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := (K19.w32 (by decide) (by decide)).trans w18_5c
  have w19_60 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K19.w32 (by decide) (by decide)).trans w18_60
  have w19_64 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := (K19.w32 (by decide) (by decide)).trans w18_64
  have w19_68 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K19.w32 (by decide) (by decide)).trans w18_68
  have w19_6c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K19.w32 (by decide) (by decide)).trans w18_6c
  have w19_70 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K19.w32 (by decide) (by decide)).trans w18_70
  have w19_74 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K19.w32 (by decide) (by decide)).trans w18_74
  have w19_78 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K19.w32 (by decide) (by decide)).trans w18_78
  have w19_7c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K19.w32 (by decide) (by decide)).trans w18_7c
  have w19_80 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K19.w32 (by decide) (by decide)).trans w18_80
  have w19_84 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K19.w32 (by decide) (by decide)).trans w18_84
  have w19_180 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K19.w32 (by decide) (by decide)).trans w18_180
  have w19_184 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K19.w32 (by decide) (by decide)).trans w18_184
  have w19_248 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := (K19.w32 (by decide) (by decide)).trans w18_248
  have w19_24c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 tl13.len := (K19.w32 (by decide) (by decide)).trans w18_24c
  have w19_a20 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := (K19.w32 (by decide) (by decide)).trans w18_a20
  have w19_a24 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl13.len := (K19.w32 (by decide) (by decide)).trans w18_a24
  have w19_a28 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := (K19.w32 (by decide) (by decide)).trans w18_a28
  have w19_a2c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl13.len := (K19.w32 (by decide) (by decide)).trans w18_a2c
  have b19_245 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K19.b8 (by decide) (by decide)).trans b18_245
  have b19_246 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K19.b8 (by decide) (by decide)).trans b18_246
  have b19_247 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K19.b8 (by decide) (by decide)).trans b18_247
  have b19_a24 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := (K19.b8 (by decide) (by decide)).trans b18_a24
  have b19_a25 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA25) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K19.b8 (by decide) (by decide)).trans b18_a25
  have b19_a26 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA26) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K19.b8 (by decide) (by decide)).trans b18_a26
  have b19_a27 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA27) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K19.b8 (by decide) (by decide)).trans b18_a27
  have b19_a30 : n19.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := (K19.b8 (by decide) (by decide)).trans b18_a30
  have w19_240 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [W19, g18_8]
  clear b18_247 b18_246 b18_245 w18_24c w18_248 b18_a30 b18_a27 b18_a26 b18_a25 b18_a24 w18_a2c w18_a28 w18_a24 w18_a20 w18_184 w18_180 w18_84 w18_80 w18_7c w18_78 w18_74 w18_70 w18_6c w18_68 w18_64 w18_60 w18_5c g18_27 g18_26 g18_25 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_9 g18_8 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 s18 X18 K18 P18 b17_a27 b17_a26 b17_a25
  -- 0x2CE: sb
  obtain ⟨n20, d20, s20, fr20, K20, W20, rg20⟩ := sv_sb F E19 s19 sv_at_2ce (off' := 0x2D2) (c := 0x244)
    (by decide) (by rw [g19_2]; sv_addr) (by decide)
  have t20 : Steps n0 n20 := t19.trans d20
  have fR20 : ∀ x, SvR B x → n20.mem x = n0.mem x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.keep K20 (by decide)
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [rg20 sp, g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg20 (3 : Fin 32), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg20 (4 : Fin 32), g19_4]
  have g20_8 : reg n20 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [rg20 (8 : Fin 32), g19_8]
  have g20_9 : reg n20 (9 : Fin 32) = trp := by rw [rg20 (9 : Fin 32), g19_9]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [rg20 (18 : Fin 32), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [rg20 (19 : Fin 32), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg20 (20 : Fin 32), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = lp := by rw [rg20 (21 : Fin 32), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = orp := by rw [rg20 (22 : Fin 32), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = tcl := by rw [rg20 (23 : Fin 32), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = sgl := by rw [rg20 (24 : Fin 32), g19_24]
  have g20_25 : reg n20 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [rg20 (25 : Fin 32), g19_25]
  have g20_26 : reg n20 (26 : Fin 32) = ll := by rw [rg20 (26 : Fin 32), g19_26]
  have g20_27 : reg n20 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg20 (27 : Fin 32), g19_27]
  have w20_5c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := (K20.w32 (by decide) (by decide)).trans w19_5c
  have w20_60 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K20.w32 (by decide) (by decide)).trans w19_60
  have w20_64 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := (K20.w32 (by decide) (by decide)).trans w19_64
  have w20_68 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K20.w32 (by decide) (by decide)).trans w19_68
  have w20_6c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K20.w32 (by decide) (by decide)).trans w19_6c
  have w20_70 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K20.w32 (by decide) (by decide)).trans w19_70
  have w20_74 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K20.w32 (by decide) (by decide)).trans w19_74
  have w20_78 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K20.w32 (by decide) (by decide)).trans w19_78
  have w20_7c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K20.w32 (by decide) (by decide)).trans w19_7c
  have w20_80 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K20.w32 (by decide) (by decide)).trans w19_80
  have w20_84 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K20.w32 (by decide) (by decide)).trans w19_84
  have w20_180 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K20.w32 (by decide) (by decide)).trans w19_180
  have w20_184 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K20.w32 (by decide) (by decide)).trans w19_184
  have w20_240 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := (K20.w32 (by decide) (by decide)).trans w19_240
  have w20_248 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := (K20.w32 (by decide) (by decide)).trans w19_248
  have w20_24c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 tl13.len := (K20.w32 (by decide) (by decide)).trans w19_24c
  have w20_a20 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := (K20.w32 (by decide) (by decide)).trans w19_a20
  have w20_a24 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl13.len := (K20.w32 (by decide) (by decide)).trans w19_a24
  have w20_a28 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := (K20.w32 (by decide) (by decide)).trans w19_a28
  have w20_a2c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl13.len := (K20.w32 (by decide) (by decide)).trans w19_a2c
  have b20_245 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K20.b8 (by decide) (by decide)).trans b19_245
  have b20_246 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K20.b8 (by decide) (by decide)).trans b19_246
  have b20_247 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K20.b8 (by decide) (by decide)).trans b19_247
  have b20_a24 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := (K20.b8 (by decide) (by decide)).trans b19_a24
  have b20_a25 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA25) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K20.b8 (by decide) (by decide)).trans b19_a25
  have b20_a26 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA26) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K20.b8 (by decide) (by decide)).trans b19_a26
  have b20_a27 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA27) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K20.b8 (by decide) (by decide)).trans b19_a27
  have b20_a30 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := (K20.b8 (by decide) (by decide)).trans b19_a30
  have b20_244 : n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [W20, g19_20, lbu_low]
  clear w19_240 b19_a30 b19_a27 b19_a26 b19_a25 b19_a24 b19_247 b19_246 b19_245 w19_a2c w19_a28 w19_a24 w19_a20 w19_24c w19_248 w19_184 w19_180 w19_84 w19_80 w19_7c w19_78 w19_74 w19_70 w19_6c w19_68 w19_64 w19_60 w19_5c g19_27 g19_26 g19_25 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_9 g19_8 g19_4 g19_3 g19_2 V19 E19 fR19 t19 rg19 W19 K19 fr19 s19 d19
  -- 0x2D2
  obtain ⟨n21, c21, u21⟩ := s20.block svL42d2 E20.self svL42d2_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m21 : n21.mem = n20.mem := u21.mem
  have s21 : St n21.mem SV n21 0x2DC (reg n21) := ⟨u21.pc, rfl, fun _ => rfl⟩
  have rb21 : ∀ q, reg n21 q = (runBlock svL42d2 (n20.mem, reg n20)).2 q := fun q => by rw [u21.regs]
  have fr21 : ∀ x, SvR B x → n21.mem x = n20.mem x := fun x _ => by rw [m21]
  have t21 : Steps n0 n21 := t20.trans c21
  have fR21 : ∀ x, SvR B x → n21.mem x = n0.mem x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.same m21
  have g21_2 : reg n21 sp = B + 0x21A0 := by
    rw [rb21, runBlock_reg _ _ _ sp s20.zero (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb21, runBlock_reg _ _ _ (3 : Fin 32) s20.zero (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb21, runBlock_reg _ _ _ (4 : Fin 32) s20.zero (by decide), g20_4]
  have g21_8 : reg n21 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by
    rw [rb21, runBlock_reg _ _ _ (8 : Fin 32) s20.zero (by decide), g20_8]
  have g21_9 : reg n21 (9 : Fin 32) = trp := by
    rw [rb21, runBlock_reg _ _ _ (9 : Fin 32) s20.zero (by decide), g20_9]
  have g21_18 : reg n21 (18 : Fin 32) = out := by
    rw [rb21, runBlock_reg _ _ _ (18 : Fin 32) s20.zero (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by
    rw [rb21, runBlock_reg _ _ _ (19 : Fin 32) s20.zero (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb21, runBlock_reg _ _ _ (20 : Fin 32) s20.zero (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = lp := by
    rw [rb21, runBlock_reg _ _ _ (21 : Fin 32) s20.zero (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = orp := by
    rw [rb21, runBlock_reg _ _ _ (22 : Fin 32) s20.zero (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = tcl := by
    rw [rb21, runBlock_reg _ _ _ (23 : Fin 32) s20.zero (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = sgl := by
    rw [rb21, runBlock_reg _ _ _ (24 : Fin 32) s20.zero (by decide), g20_24]
  have g21_25 : reg n21 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by
    rw [rb21, runBlock_reg _ _ _ (25 : Fin 32) s20.zero (by decide), g20_25]
  have g21_26 : reg n21 (26 : Fin 32) = ll := by
    rw [rb21, runBlock_reg _ _ _ (26 : Fin 32) s20.zero (by decide), g20_26]
  have g21_27 : reg n21 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb21, runBlock_reg _ _ _ (27 : Fin 32) s20.zero (by decide), g20_27]
  have g21_10 : reg n21 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svL42d2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_25, g20_26, g20_27, s20.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g21_11 : reg n21 a1 = B + 0x21A0 + BitVec.ofNat 32 0x240 := by
    rw [rb21]; simp +decide only [runBlock, BInstr.run, svL42d2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g20_2, g20_3, g20_4, g20_8, g20_9, g20_18, g20_19, g20_20, g20_21, g20_22, g20_23, g20_24, g20_25, g20_26, g20_27, s20.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w21_5c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m21]; exact w20_5c
  have w21_60 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m21]; exact w20_60
  have w21_64 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m21]; exact w20_64
  have w21_68 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m21]; exact w20_68
  have w21_6c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m21]; exact w20_6c
  have w21_70 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m21]; exact w20_70
  have w21_74 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m21]; exact w20_74
  have w21_78 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m21]; exact w20_78
  have w21_7c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m21]; exact w20_7c
  have w21_80 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m21]; exact w20_80
  have w21_84 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m21]; exact w20_84
  have w21_180 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m21]; exact w20_180
  have w21_184 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m21]; exact w20_184
  have w21_240 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m21]; exact w20_240
  have w21_248 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m21]; exact w20_248
  have w21_24c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 tl13.len := by rw [m21]; exact w20_24c
  have w21_a20 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m21]; exact w20_a20
  have w21_a24 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl13.len := by rw [m21]; exact w20_a24
  have w21_a28 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m21]; exact w20_a28
  have w21_a2c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 tl13.len := by rw [m21]; exact w20_a2c
  have b21_244 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m21]; exact b20_244
  have b21_245 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m21]; exact b20_245
  have b21_246 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m21]; exact b20_246
  have b21_247 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m21]; exact b20_247
  have b21_a24 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m21]; exact b20_a24
  have b21_a25 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA25) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m21]; exact b20_a25
  have b21_a26 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA26) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m21]; exact b20_a26
  have b21_a27 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA27) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m21]; exact b20_a27
  have b21_a30 : n21.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m21]; exact b20_a30
  clear b20_244 b20_a30 b20_a27 b20_a26 b20_a25 b20_a24 b20_247 b20_246 b20_245 w20_a2c w20_a28 w20_a24 w20_a20 w20_24c w20_248 w20_240 w20_184 w20_180 w20_84 w20_80 w20_7c w20_78 w20_74 w20_70 w20_6c w20_68 w20_64 w20_60 w20_5c g20_27 g20_26 g20_25 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_9 g20_8 g20_4 g20_3 g20_2 V20 E20 fR20 t20 rg20 W20 K20 fr20 s20 d20
  -- 0x2DC: sv_rtF
  obtain ⟨n22, c22, s22, sp22, rk22, K22, Ok22, Er22, fr22⟩ := sv_rtF (oc := 0xA20) (dc := 0x240) (rl := tl13.len)
    F E21 s21 sv_at_2dc sv_at_2e0 (by decide) (by decide) g21_2 g21_10 g21_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w21_248 w21_24c ((tb_in.restW hr6).content hr13)
  have t22 : Steps n0 n22 := t21.trans c22
  have fR22 : ∀ x, SvR B x → n22.mem x = n0.mem x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.keepL K22 (by decide)
  rw [sv_mb fR21 ((tb_in.restW hr6).content hr13)] at Ok22 Er22
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk22 (3 : Fin 32) (by decide), g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk22 (4 : Fin 32) (by decide), g21_4]
  have g22_8 : reg n22 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [rk22 (8 : Fin 32) (by decide), g21_8]
  have g22_9 : reg n22 (9 : Fin 32) = trp := by rw [rk22 (9 : Fin 32) (by decide), g21_9]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [rk22 (18 : Fin 32) (by decide), g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [rk22 (19 : Fin 32) (by decide), g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk22 (20 : Fin 32) (by decide), g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = lp := by rw [rk22 (21 : Fin 32) (by decide), g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = orp := by rw [rk22 (22 : Fin 32) (by decide), g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = tcl := by rw [rk22 (23 : Fin 32) (by decide), g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = sgl := by rw [rk22 (24 : Fin 32) (by decide), g21_24]
  have g22_25 : reg n22 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [rk22 (25 : Fin 32) (by decide), g21_25]
  have g22_26 : reg n22 (26 : Fin 32) = ll := by rw [rk22 (26 : Fin 32) (by decide), g21_26]
  have g22_27 : reg n22 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk22 (27 : Fin 32) (by decide), g21_27]
  have g22_2 : reg n22 sp = B + 0x21A0 := sp22
  obtain ⟨r22, hr22⟩ : ∃ r, readTime (memBytes n0.mem (((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) (tl13.len)) = r := ⟨_, rfl⟩
  rcases r22 with _ | ⟨tm22, rs22⟩
  · have y0_22 := Er22 hr22
    have w22_5c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := (K22.w32 (by decide) (by decide)).trans w21_5c
    have w22_60 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K22.w32 (by decide) (by decide)).trans w21_60
    have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := (K22.w32 (by decide) (by decide)).trans w21_64
    have w22_68 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K22.w32 (by decide) (by decide)).trans w21_68
    have w22_6c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K22.w32 (by decide) (by decide)).trans w21_6c
    have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K22.w32 (by decide) (by decide)).trans w21_70
    have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K22.w32 (by decide) (by decide)).trans w21_74
    have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K22.w32 (by decide) (by decide)).trans w21_78
    have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K22.w32 (by decide) (by decide)).trans w21_7c
    have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K22.w32 (by decide) (by decide)).trans w21_80
    have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K22.w32 (by decide) (by decide)).trans w21_84
    have w22_180 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K22.w32 (by decide) (by decide)).trans w21_180
    have w22_184 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K22.w32 (by decide) (by decide)).trans w21_184
    have w22_240 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := (K22.w32 (by decide) (by decide)).trans w21_240
    have b22_244 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := (K22.b8 (by decide) (by decide)).trans b21_244
    have b22_245 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K22.b8 (by decide) (by decide)).trans b21_245
    have b22_246 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K22.b8 (by decide) (by decide)).trans b21_246
    have b22_247 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K22.b8 (by decide) (by decide)).trans b21_247
    have b22_a30 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := (K22.b8 (by decide) (by decide)).trans b21_a30
    have b22_a20 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := y0_22
    clear b21_a30 b21_a27 b21_a26 b21_a25 b21_a24 b21_247 b21_246 b21_245 b21_244 w21_a2c w21_a28 w21_a24 w21_a20 w21_24c w21_248 w21_240 w21_184 w21_180 w21_84 w21_80 w21_7c w21_78 w21_74 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c g21_11 g21_10 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
    -- 0x2E4: lbu
    obtain ⟨n23, d23, u23⟩ := s22.lbu E22.self sv_at_2e4 (off' := 0x2E8) (by decide)
    have s23 : St n23.mem SV n23 0x2E8 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
    have m23 : n23.mem = n22.mem := u23.mem
    have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
    have t23 : Steps n0 n23 := t22.trans (.single d23)
    have fR23 : ∀ x, SvR B x → n23.mem x = n0.mem x := fun x hx => (fr23 x hx).trans (fR22 x hx)
    have E23 : SvCode n23.mem := E22.fr F fr23
    have V23 : SvSaves B n23.mem v := V22.same m23
    have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
    have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
    have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
    have g23_8 : reg n23 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u23.regs, upd_ne (by decide) (by decide), g22_8]
    have g23_9 : reg n23 (9 : Fin 32) = trp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_9]
    have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
    have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
    have g23_20 : reg n23 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_20]
    have g23_21 : reg n23 (21 : Fin 32) = lp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
    have g23_22 : reg n23 (22 : Fin 32) = orp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_22]
    have g23_23 : reg n23 (23 : Fin 32) = tcl := by rw [u23.regs, upd_ne (by decide) (by decide), g22_23]
    have g23_24 : reg n23 (24 : Fin 32) = sgl := by rw [u23.regs, upd_ne (by decide) (by decide), g22_24]
    have g23_25 : reg n23 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_25]
    have g23_26 : reg n23 (26 : Fin 32) = ll := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
    have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_27]
    have g23_10 : reg n23 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [u23.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g22_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, b22_a20]
    have w23_5c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m23]; exact w22_5c
    have w23_60 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m23]; exact w22_60
    have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m23]; exact w22_64
    have w23_68 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m23]; exact w22_68
    have w23_6c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m23]; exact w22_6c
    have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m23]; exact w22_70
    have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m23]; exact w22_74
    have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m23]; exact w22_78
    have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m23]; exact w22_7c
    have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m23]; exact w22_80
    have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m23]; exact w22_84
    have w23_180 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m23]; exact w22_180
    have w23_184 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m23]; exact w22_184
    have w23_240 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m23]; exact w22_240
    have b23_244 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m23]; exact b22_244
    have b23_245 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m23]; exact b22_245
    have b23_246 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m23]; exact b22_246
    have b23_247 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m23]; exact b22_247
    have b23_a20 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := by rw [m23]; exact b22_a20
    have b23_a30 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m23]; exact b22_a30
    clear b22_a20 b22_a30 b22_247 b22_246 b22_245 b22_244 w22_240 w22_184 w22_180 w22_84 w22_80 w22_7c w22_78 w22_74 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c y0_22
    -- 0x2E8: branch, taken
    obtain ⟨n24, d24, u24⟩ := s23.taken E23.self 0x17E sv_at_2e8
      (by decide) (by rw [g23_10, s23.zero]; decide)
    have s24 : St n24.mem SV n24 0x17E (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
    have m24 : n24.mem = n23.mem := u24.mem
    have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
    have t24 : Steps n0 n24 := t23.trans (.single d24)
    have fR24 : ∀ x, SvR B x → n24.mem x = n0.mem x := fun x hx => (fr24 x hx).trans (fR23 x hx)
    have E24 : SvCode n24.mem := E23.fr F fr24
    have V24 : SvSaves B n24.mem v := V23.same m24
    have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
    have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
    have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
    have g24_8 : reg n24 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u24.regs, g23_8]
    have g24_9 : reg n24 (9 : Fin 32) = trp := by rw [u24.regs, g23_9]
    have g24_10 : reg n24 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u24.regs, g23_10]
    have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
    have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
    have g24_20 : reg n24 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [u24.regs, g23_20]
    have g24_21 : reg n24 (21 : Fin 32) = lp := by rw [u24.regs, g23_21]
    have g24_22 : reg n24 (22 : Fin 32) = orp := by rw [u24.regs, g23_22]
    have g24_23 : reg n24 (23 : Fin 32) = tcl := by rw [u24.regs, g23_23]
    have g24_24 : reg n24 (24 : Fin 32) = sgl := by rw [u24.regs, g23_24]
    have g24_25 : reg n24 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u24.regs, g23_25]
    have g24_26 : reg n24 (26 : Fin 32) = ll := by rw [u24.regs, g23_26]
    have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u24.regs, g23_27]
    have w24_5c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m24]; exact w23_5c
    have w24_60 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m24]; exact w23_60
    have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m24]; exact w23_64
    have w24_68 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m24]; exact w23_68
    have w24_6c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m24]; exact w23_6c
    have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m24]; exact w23_70
    have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m24]; exact w23_74
    have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m24]; exact w23_78
    have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m24]; exact w23_7c
    have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m24]; exact w23_80
    have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m24]; exact w23_84
    have w24_180 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m24]; exact w23_180
    have w24_184 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m24]; exact w23_184
    have w24_240 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m24]; exact w23_240
    have b24_244 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m24]; exact b23_244
    have b24_245 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m24]; exact b23_245
    have b24_246 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m24]; exact b23_246
    have b24_247 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m24]; exact b23_247
    have b24_a20 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := by rw [m24]; exact b23_a20
    have b24_a30 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m24]; exact b23_a30
    clear b23_a30 b23_a20 b23_247 b23_246 b23_245 b23_244 w23_240 w23_184 w23_180 w23_84 w23_80 w23_7c w23_78 w23_74 w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c g23_10 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
    -- 0x17E: lbu
    obtain ⟨n25, d25, u25⟩ := s24.lbu E24.self sv_at_17e (off' := 0x182) (by decide)
    have s25 : St n25.mem SV n25 0x182 (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
    have m25 : n25.mem = n24.mem := u25.mem
    have fr25 : ∀ x, SvR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
    have t25 : Steps n0 n25 := t24.trans (.single d25)
    have fR25 : ∀ x, SvR B x → n25.mem x = n0.mem x := fun x hx => (fr25 x hx).trans (fR24 x hx)
    have E25 : SvCode n25.mem := E24.fr F fr25
    have V25 : SvSaves B n25.mem v := V24.same m25
    have g25_2 : reg n25 sp = B + 0x21A0 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_2]
    have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_3]
    have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_4]
    have g25_8 : reg n25 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u25.regs, upd_ne (by decide) (by decide), g24_8]
    have g25_9 : reg n25 (9 : Fin 32) = trp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_9]
    have g25_10 : reg n25 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_10]
    have g25_18 : reg n25 (18 : Fin 32) = out := by rw [u25.regs, upd_ne (by decide) (by decide), g24_18]
    have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_19]
    have g25_21 : reg n25 (21 : Fin 32) = lp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_21]
    have g25_22 : reg n25 (22 : Fin 32) = orp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_22]
    have g25_23 : reg n25 (23 : Fin 32) = tcl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_23]
    have g25_24 : reg n25 (24 : Fin 32) = sgl := by rw [u25.regs, upd_ne (by decide) (by decide), g24_24]
    have g25_25 : reg n25 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_25]
    have g25_26 : reg n25 (26 : Fin 32) = ll := by rw [u25.regs, upd_ne (by decide) (by decide), g24_26]
    have g25_27 : reg n25 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_27]
    have w25_5c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m25]; exact w24_5c
    have w25_60 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m25]; exact w24_60
    have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m25]; exact w24_64
    have w25_68 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m25]; exact w24_68
    have w25_6c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m25]; exact w24_6c
    have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m25]; exact w24_70
    have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m25]; exact w24_74
    have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m25]; exact w24_78
    have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m25]; exact w24_7c
    have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m25]; exact w24_80
    have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m25]; exact w24_84
    have w25_180 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m25]; exact w24_180
    have w25_184 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m25]; exact w24_184
    have w25_240 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m25]; exact w24_240
    have b25_244 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m25]; exact b24_244
    have b25_245 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m25]; exact b24_245
    have b25_246 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m25]; exact b24_246
    have b25_247 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m25]; exact b24_247
    have b25_a20 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := by rw [m25]; exact b24_a20
    have b25_a30 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m25]; exact b24_a30
    clear b24_a30 b24_a20 b24_247 b24_246 b24_245 b24_244 w24_240 w24_184 w24_180 w24_84 w24_80 w24_7c w24_78 w24_74 w24_70 w24_6c w24_68 w24_64 w24_60 w24_5c g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_10 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
    -- 0x182: j
    obtain ⟨n26, d26, u26⟩ := s25.jump E25.self sv_at_182 (off' := 0x966) (by decide)
      (by rw [s25.pc]; decide)
    have s26 : St n26.mem SV n26 0x966 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
    have m26 : n26.mem = n25.mem := u26.mem
    have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
    have t26 : Steps n0 n26 := t25.trans (.single d26)
    have fR26 : ∀ x, SvR B x → n26.mem x = n0.mem x := fun x hx => (fr26 x hx).trans (fR25 x hx)
    have E26 : SvCode n26.mem := E25.fr F fr26
    have V26 : SvSaves B n26.mem v := V25.same m26
    have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, g25_2]
    have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, g25_3]
    have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, g25_4]
    have g26_8 : reg n26 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u26.regs, g25_8]
    have g26_9 : reg n26 (9 : Fin 32) = trp := by rw [u26.regs, g25_9]
    have g26_10 : reg n26 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u26.regs, g25_10]
    have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, g25_18]
    have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, g25_19]
    have g26_21 : reg n26 (21 : Fin 32) = lp := by rw [u26.regs, g25_21]
    have g26_22 : reg n26 (22 : Fin 32) = orp := by rw [u26.regs, g25_22]
    have g26_23 : reg n26 (23 : Fin 32) = tcl := by rw [u26.regs, g25_23]
    have g26_24 : reg n26 (24 : Fin 32) = sgl := by rw [u26.regs, g25_24]
    have g26_25 : reg n26 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u26.regs, g25_25]
    have g26_26 : reg n26 (26 : Fin 32) = ll := by rw [u26.regs, g25_26]
    have g26_27 : reg n26 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u26.regs, g25_27]
    have w26_5c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m26]; exact w25_5c
    have w26_60 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m26]; exact w25_60
    have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m26]; exact w25_64
    have w26_68 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m26]; exact w25_68
    have w26_6c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m26]; exact w25_6c
    have w26_70 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m26]; exact w25_70
    have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m26]; exact w25_74
    have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m26]; exact w25_78
    have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m26]; exact w25_7c
    have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m26]; exact w25_80
    have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m26]; exact w25_84
    have w26_180 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m26]; exact w25_180
    have w26_184 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m26]; exact w25_184
    have w26_240 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m26]; exact w25_240
    have b26_244 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m26]; exact b25_244
    have b26_245 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m26]; exact b25_245
    have b26_246 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m26]; exact b25_246
    have b26_247 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m26]; exact b25_247
    have b26_a20 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := by rw [m26]; exact b25_a20
    have b26_a30 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m26]; exact b25_a30
    clear b25_a30 b25_a20 b25_247 b25_246 b25_245 b25_244 w25_240 w25_184 w25_180 w25_84 w25_80 w25_7c w25_78 w25_74 w25_70 w25_6c w25_68 w25_64 w25_60 w25_5c g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_19 g25_18 g25_10 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 m25 s25 u25 d25
    exact .inl ⟨(fun ⟨tl6', h0', tl13', h1', tm22', rs22', h2', _⟩ => by rw [hr6] at h0'; cases h0'; rw [hr13] at h1'; cases h1'; rw [hr22] at h2'; cases h2'), sv_fail F E26 s26 t26 fR26 V26 hret g26_2 g26_18 hO g26_3 g26_4⟩
  obtain ⟨h64_22, y0_22, y8_22, y12_22, kk22, hkk22, d8_22, d12_22, hrb22⟩ := Ok22 tm22 rs22 hr22
  rw [sv_mb fR21 (((tb_in.restW hr6).content hr13).drop hkk22)] at hrb22
  have w22_5c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := (K22.w32 (by decide) (by decide)).trans w21_5c
  have w22_60 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K22.w32 (by decide) (by decide)).trans w21_60
  have w22_64 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := (K22.w32 (by decide) (by decide)).trans w21_64
  have w22_68 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K22.w32 (by decide) (by decide)).trans w21_68
  have w22_6c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K22.w32 (by decide) (by decide)).trans w21_6c
  have w22_70 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K22.w32 (by decide) (by decide)).trans w21_70
  have w22_74 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K22.w32 (by decide) (by decide)).trans w21_74
  have w22_78 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K22.w32 (by decide) (by decide)).trans w21_78
  have w22_7c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K22.w32 (by decide) (by decide)).trans w21_7c
  have w22_80 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K22.w32 (by decide) (by decide)).trans w21_80
  have w22_84 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K22.w32 (by decide) (by decide)).trans w21_84
  have w22_180 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K22.w32 (by decide) (by decide)).trans w21_180
  have w22_184 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K22.w32 (by decide) (by decide)).trans w21_184
  have w22_240 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := (K22.w32 (by decide) (by decide)).trans w21_240
  have b22_244 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := (K22.b8 (by decide) (by decide)).trans b21_244
  have b22_245 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K22.b8 (by decide) (by decide)).trans b21_245
  have b22_246 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K22.b8 (by decide) (by decide)).trans b21_246
  have b22_247 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K22.b8 (by decide) (by decide)).trans b21_247
  have b22_a30 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := (K22.b8 (by decide) (by decide)).trans b21_a30
  have w22_248 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = (((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22 := d8_22
  have w22_24c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 ((tl13.len) - kk22) := d12_22
  have w22_a28 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := y8_22
  have w22_a2c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := y12_22
  have b22_a20 : n22.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := y0_22
  clear b21_a30 b21_a27 b21_a26 b21_a25 b21_a24 b21_247 b21_246 b21_245 b21_244 w21_a2c w21_a28 w21_a24 w21_a20 w21_24c w21_248 w21_240 w21_184 w21_180 w21_84 w21_80 w21_7c w21_78 w21_74 w21_70 w21_6c w21_68 w21_64 w21_60 w21_5c g21_11 g21_10 g21_27 g21_26 g21_25 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_9 g21_8 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 rb21 s21 m21 u21 c21
  -- 0x2E4: lbu
  obtain ⟨n23, d23, u23⟩ := s22.lbu E22.self sv_at_2e4 (off' := 0x2E8) (by decide)
  have s23 : St n23.mem SV n23 0x2E8 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have fr23 : ∀ x, SvR B x → n23.mem x = n22.mem x := fun x _ => by rw [m23]
  have t23 : Steps n0 n23 := t22.trans (.single d23)
  have fR23 : ∀ x, SvR B x → n23.mem x = n0.mem x := fun x hx => (fr23 x hx).trans (fR22 x hx)
  have E23 : SvCode n23.mem := E22.fr F fr23
  have V23 : SvSaves B n23.mem v := V22.same m23
  have g23_2 : reg n23 sp = B + 0x21A0 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_2]
  have g23_3 : reg n23 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_3]
  have g23_4 : reg n23 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_4]
  have g23_8 : reg n23 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u23.regs, upd_ne (by decide) (by decide), g22_8]
  have g23_9 : reg n23 (9 : Fin 32) = trp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_9]
  have g23_18 : reg n23 (18 : Fin 32) = out := by rw [u23.regs, upd_ne (by decide) (by decide), g22_18]
  have g23_19 : reg n23 (19 : Fin 32) = bp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_19]
  have g23_20 : reg n23 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_20]
  have g23_21 : reg n23 (21 : Fin 32) = lp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_21]
  have g23_22 : reg n23 (22 : Fin 32) = orp := by rw [u23.regs, upd_ne (by decide) (by decide), g22_22]
  have g23_23 : reg n23 (23 : Fin 32) = tcl := by rw [u23.regs, upd_ne (by decide) (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = sgl := by rw [u23.regs, upd_ne (by decide) (by decide), g22_24]
  have g23_25 : reg n23 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u23.regs, upd_ne (by decide) (by decide), g22_25]
  have g23_26 : reg n23 (26 : Fin 32) = ll := by rw [u23.regs, upd_ne (by decide) (by decide), g22_26]
  have g23_27 : reg n23 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u23.regs, upd_ne (by decide) (by decide), g22_27]
  have g23_10 : reg n23 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [u23.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g22_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, b22_a20]
  have w23_5c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m23]; exact w22_5c
  have w23_60 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m23]; exact w22_60
  have w23_64 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m23]; exact w22_64
  have w23_68 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m23]; exact w22_68
  have w23_6c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m23]; exact w22_6c
  have w23_70 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m23]; exact w22_70
  have w23_74 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m23]; exact w22_74
  have w23_78 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m23]; exact w22_78
  have w23_7c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m23]; exact w22_7c
  have w23_80 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m23]; exact w22_80
  have w23_84 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m23]; exact w22_84
  have w23_180 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m23]; exact w22_180
  have w23_184 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m23]; exact w22_184
  have w23_240 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m23]; exact w22_240
  have w23_248 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = (((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22 := by rw [m23]; exact w22_248
  have w23_24c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 ((tl13.len) - kk22) := by rw [m23]; exact w22_24c
  have w23_a28 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m23]; exact w22_a28
  have w23_a2c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m23]; exact w22_a2c
  have b23_244 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m23]; exact b22_244
  have b23_245 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m23]; exact b22_245
  have b23_246 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m23]; exact b22_246
  have b23_247 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m23]; exact b22_247
  have b23_a20 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m23]; exact b22_a20
  have b23_a30 : n23.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m23]; exact b22_a30
  clear b22_a20 w22_a2c w22_a28 w22_24c w22_248 b22_a30 b22_247 b22_246 b22_245 b22_244 w22_240 w22_184 w22_180 w22_84 w22_80 w22_7c w22_78 w22_74 w22_70 w22_6c w22_68 w22_64 w22_60 w22_5c d12_22 d8_22 y12_22 y8_22 y0_22 g22_2 g22_27 g22_26 g22_25 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_9 g22_8 g22_4 g22_3 V22 E22 fR22 t22 fr22 Er22 Ok22 K22 rk22 sp22 s22 c22
  -- 0x2E8: branch, not taken
  obtain ⟨n24, d24, u24⟩ := s23.notTaken E23.self 0x2EC sv_at_2e8
    (by decide) (by rw [g23_10, s23.zero]; decide)
  have s24 : St n24.mem SV n24 0x2EC (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, SvR B x → n24.mem x = n0.mem x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, g23_4]
  have g24_8 : reg n24 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u24.regs, g23_8]
  have g24_9 : reg n24 (9 : Fin 32) = trp := by rw [u24.regs, g23_9]
  have g24_10 : reg n24 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u24.regs, g23_10]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [u24.regs, g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = lp := by rw [u24.regs, g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = orp := by rw [u24.regs, g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = tcl := by rw [u24.regs, g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = sgl := by rw [u24.regs, g23_24]
  have g24_25 : reg n24 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u24.regs, g23_25]
  have g24_26 : reg n24 (26 : Fin 32) = ll := by rw [u24.regs, g23_26]
  have g24_27 : reg n24 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u24.regs, g23_27]
  have w24_5c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m24]; exact w23_5c
  have w24_60 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m24]; exact w23_60
  have w24_64 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m24]; exact w23_64
  have w24_68 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m24]; exact w23_68
  have w24_6c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m24]; exact w23_6c
  have w24_70 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m24]; exact w23_70
  have w24_74 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m24]; exact w23_74
  have w24_78 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m24]; exact w23_78
  have w24_7c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m24]; exact w23_7c
  have w24_80 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m24]; exact w23_80
  have w24_84 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m24]; exact w23_84
  have w24_180 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m24]; exact w23_180
  have w24_184 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m24]; exact w23_184
  have w24_240 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m24]; exact w23_240
  have w24_248 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = (((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22 := by rw [m24]; exact w23_248
  have w24_24c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 ((tl13.len) - kk22) := by rw [m24]; exact w23_24c
  have w24_a28 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m24]; exact w23_a28
  have w24_a2c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m24]; exact w23_a2c
  have b24_244 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m24]; exact b23_244
  have b24_245 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m24]; exact b23_245
  have b24_246 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m24]; exact b23_246
  have b24_247 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m24]; exact b23_247
  have b24_a20 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m24]; exact b23_a20
  have b24_a30 : n24.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m24]; exact b23_a30
  clear b23_a30 b23_a20 b23_247 b23_246 b23_245 b23_244 w23_a2c w23_a28 w23_24c w23_248 w23_240 w23_184 w23_180 w23_84 w23_80 w23_7c w23_78 w23_74 w23_70 w23_6c w23_68 w23_64 w23_60 w23_5c g23_10 g23_27 g23_26 g23_25 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_9 g23_8 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 m23 s23 u23 d23
  -- 0x2EC
  obtain ⟨n25, c25, u25⟩ := s24.block svL42ec E24.self svL42ec_end
    ⟨trivial, trivial⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have s25 : St n25.mem SV n25 0x2EE (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have rb25 : ∀ q, reg n25 q = (runBlock svL42ec (n24.mem, reg n24)).2 q := fun q => by rw [u25.regs]
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
  have g25_8 : reg n25 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by
    rw [rb25, runBlock_reg _ _ _ (8 : Fin 32) s24.zero (by decide), g24_8]
  have g25_9 : reg n25 (9 : Fin 32) = trp := by
    rw [rb25, runBlock_reg _ _ _ (9 : Fin 32) s24.zero (by decide), g24_9]
  have g25_10 : reg n25 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [rb25, runBlock_reg _ _ _ a0 s24.zero (by decide), g24_10]
  have g25_18 : reg n25 (18 : Fin 32) = out := by
    rw [rb25, runBlock_reg _ _ _ (18 : Fin 32) s24.zero (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by
    rw [rb25, runBlock_reg _ _ _ (19 : Fin 32) s24.zero (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb25, runBlock_reg _ _ _ (20 : Fin 32) s24.zero (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = lp := by
    rw [rb25, runBlock_reg _ _ _ (21 : Fin 32) s24.zero (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = orp := by
    rw [rb25, runBlock_reg _ _ _ (22 : Fin 32) s24.zero (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = tcl := by
    rw [rb25, runBlock_reg _ _ _ (23 : Fin 32) s24.zero (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = sgl := by
    rw [rb25, runBlock_reg _ _ _ (24 : Fin 32) s24.zero (by decide), g24_24]
  have g25_25 : reg n25 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by
    rw [rb25, runBlock_reg _ _ _ (25 : Fin 32) s24.zero (by decide), g24_25]
  have g25_26 : reg n25 (26 : Fin 32) = ll := by
    rw [rb25, runBlock_reg _ _ _ (26 : Fin 32) s24.zero (by decide), g24_26]
  have g25_27 : reg n25 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb25, runBlock_reg _ _ _ (27 : Fin 32) s24.zero (by decide), g24_27]
  have g25_11 : reg n25 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb25]; simp +decide only [runBlock, BInstr.run, svL42ec, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g24_2, g24_3, g24_4, g24_8, g24_9, g24_10, g24_18, g24_19, g24_20, g24_21, g24_22, g24_23, g24_24, g24_25, g24_26, g24_27, s24.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w25_5c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m25]; exact w24_5c
  have w25_60 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m25]; exact w24_60
  have w25_64 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m25]; exact w24_64
  have w25_68 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m25]; exact w24_68
  have w25_6c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m25]; exact w24_6c
  have w25_70 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m25]; exact w24_70
  have w25_74 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m25]; exact w24_74
  have w25_78 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m25]; exact w24_78
  have w25_7c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m25]; exact w24_7c
  have w25_80 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m25]; exact w24_80
  have w25_84 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m25]; exact w24_84
  have w25_180 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m25]; exact w24_180
  have w25_184 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m25]; exact w24_184
  have w25_240 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m25]; exact w24_240
  have w25_248 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = (((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22 := by rw [m25]; exact w24_248
  have w25_24c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 ((tl13.len) - kk22) := by rw [m25]; exact w24_24c
  have w25_a28 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m25]; exact w24_a28
  have w25_a2c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m25]; exact w24_a2c
  have b25_244 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m25]; exact b24_244
  have b25_245 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m25]; exact b24_245
  have b25_246 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m25]; exact b24_246
  have b25_247 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m25]; exact b24_247
  have b25_a20 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m25]; exact b24_a20
  have b25_a30 : n25.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m25]; exact b24_a30
  clear b24_a30 b24_a20 b24_247 b24_246 b24_245 b24_244 w24_a2c w24_a28 w24_24c w24_248 w24_240 w24_184 w24_180 w24_84 w24_80 w24_7c w24_78 w24_74 w24_70 w24_6c w24_68 w24_64 w24_60 w24_5c g24_27 g24_26 g24_25 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_10 g24_9 g24_8 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
  -- 0x2EE: lw
  obtain ⟨n26, d26, u26⟩ := s25.lw E25.self sv_at_2ee (off' := 0x2F0) (by decide)
    (by rw [g25_11, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s26 : St n26.mem SV n26 0x2F0 (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans (.single d26)
  have fR26 : ∀ x, SvR B x → n26.mem x = n0.mem x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_4]
  have g26_8 : reg n26 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u26.regs, upd_ne (by decide) (by decide), g25_8]
  have g26_9 : reg n26 (9 : Fin 32) = trp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_9]
  have g26_11 : reg n26 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_11]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, upd_ne (by decide) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = lp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = orp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = tcl := by rw [u26.regs, upd_ne (by decide) (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = sgl := by rw [u26.regs, upd_ne (by decide) (by decide), g25_24]
  have g26_25 : reg n26 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_25]
  have g26_26 : reg n26 (26 : Fin 32) = ll := by rw [u26.regs, upd_ne (by decide) (by decide), g25_26]
  have g26_27 : reg n26 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_27]
  have g26_10 : reg n26 a0 = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by
    rw [u26.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g25_11, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr, w25_a28]
  have w26_5c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m26]; exact w25_5c
  have w26_60 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m26]; exact w25_60
  have w26_64 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m26]; exact w25_64
  have w26_68 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m26]; exact w25_68
  have w26_6c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m26]; exact w25_6c
  have w26_70 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m26]; exact w25_70
  have w26_74 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m26]; exact w25_74
  have w26_78 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m26]; exact w25_78
  have w26_7c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m26]; exact w25_7c
  have w26_80 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m26]; exact w25_80
  have w26_84 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m26]; exact w25_84
  have w26_180 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m26]; exact w25_180
  have w26_184 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m26]; exact w25_184
  have w26_240 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m26]; exact w25_240
  have w26_248 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = (((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22 := by rw [m26]; exact w25_248
  have w26_24c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 ((tl13.len) - kk22) := by rw [m26]; exact w25_24c
  have w26_a28 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m26]; exact w25_a28
  have w26_a2c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m26]; exact w25_a2c
  have b26_244 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m26]; exact b25_244
  have b26_245 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m26]; exact b25_245
  have b26_246 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m26]; exact b25_246
  have b26_247 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m26]; exact b25_247
  have b26_a20 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m26]; exact b25_a20
  have b26_a30 : n26.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m26]; exact b25_a30
  clear b25_a30 b25_a20 b25_247 b25_246 b25_245 b25_244 w25_a2c w25_a28 w25_24c w25_248 w25_240 w25_184 w25_180 w25_84 w25_80 w25_7c w25_78 w25_74 w25_70 w25_6c w25_68 w25_64 w25_60 w25_5c g25_11 g25_27 g25_26 g25_25 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_10 g25_9 g25_8 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 rb25 s25 m25 u25 c25
  -- 0x2F0: sw
  obtain ⟨n27, d27, s27, fr27, K27, W27, rg27⟩ := sv_sw F E26 s26 sv_at_2f0 (off' := 0x2F2) (c := 0x58)
    (by decide) (by rw [g26_2]; sv_addr) (by decide) (by decide)
  have t27 : Steps n0 n27 := t26.trans d27
  have fR27 : ∀ x, SvR B x → n27.mem x = n0.mem x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.keep K27 (by decide)
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [rg27 sp, g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg27 (3 : Fin 32), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg27 (4 : Fin 32), g26_4]
  have g27_8 : reg n27 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [rg27 (8 : Fin 32), g26_8]
  have g27_9 : reg n27 (9 : Fin 32) = trp := by rw [rg27 (9 : Fin 32), g26_9]
  have g27_10 : reg n27 a0 = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [rg27 a0, g26_10]
  have g27_11 : reg n27 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg27 a1, g26_11]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [rg27 (18 : Fin 32), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [rg27 (19 : Fin 32), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg27 (20 : Fin 32), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = lp := by rw [rg27 (21 : Fin 32), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = orp := by rw [rg27 (22 : Fin 32), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = tcl := by rw [rg27 (23 : Fin 32), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = sgl := by rw [rg27 (24 : Fin 32), g26_24]
  have g27_25 : reg n27 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [rg27 (25 : Fin 32), g26_25]
  have g27_26 : reg n27 (26 : Fin 32) = ll := by rw [rg27 (26 : Fin 32), g26_26]
  have g27_27 : reg n27 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg27 (27 : Fin 32), g26_27]
  have w27_5c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := (K27.w32 (by decide) (by decide)).trans w26_5c
  have w27_60 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K27.w32 (by decide) (by decide)).trans w26_60
  have w27_64 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := (K27.w32 (by decide) (by decide)).trans w26_64
  have w27_68 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K27.w32 (by decide) (by decide)).trans w26_68
  have w27_6c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K27.w32 (by decide) (by decide)).trans w26_6c
  have w27_70 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K27.w32 (by decide) (by decide)).trans w26_70
  have w27_74 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K27.w32 (by decide) (by decide)).trans w26_74
  have w27_78 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K27.w32 (by decide) (by decide)).trans w26_78
  have w27_7c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K27.w32 (by decide) (by decide)).trans w26_7c
  have w27_80 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K27.w32 (by decide) (by decide)).trans w26_80
  have w27_84 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K27.w32 (by decide) (by decide)).trans w26_84
  have w27_180 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K27.w32 (by decide) (by decide)).trans w26_180
  have w27_184 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K27.w32 (by decide) (by decide)).trans w26_184
  have w27_240 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := (K27.w32 (by decide) (by decide)).trans w26_240
  have w27_248 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = (((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22 := (K27.w32 (by decide) (by decide)).trans w26_248
  have w27_24c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 ((tl13.len) - kk22) := (K27.w32 (by decide) (by decide)).trans w26_24c
  have w27_a28 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := (K27.w32 (by decide) (by decide)).trans w26_a28
  have w27_a2c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := (K27.w32 (by decide) (by decide)).trans w26_a2c
  have b27_244 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := (K27.b8 (by decide) (by decide)).trans b26_244
  have b27_245 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K27.b8 (by decide) (by decide)).trans b26_245
  have b27_246 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K27.b8 (by decide) (by decide)).trans b26_246
  have b27_247 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K27.b8 (by decide) (by decide)).trans b26_247
  have b27_a20 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := (K27.b8 (by decide) (by decide)).trans b26_a20
  have b27_a30 : n27.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := (K27.b8 (by decide) (by decide)).trans b26_a30
  have w27_58 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [W27, g26_10]
  clear b26_a30 b26_a20 b26_247 b26_246 b26_245 b26_244 w26_a2c w26_a28 w26_24c w26_248 w26_240 w26_184 w26_180 w26_84 w26_80 w26_7c w26_78 w26_74 w26_70 w26_6c w26_68 w26_64 w26_60 w26_5c g26_10 g26_27 g26_26 g26_25 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_11 g26_9 g26_8 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
  -- 0x2F2: lw
  obtain ⟨n28, d28, u28⟩ := s27.lw E27.self sv_at_2f2 (off' := 0x2F4) (by decide)
    (by rw [g27_11, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0xC = B + 0x21A0 + BitVec.ofNat 32 0xA2C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s28 : St n28.mem SV n28 0x2F4 (reg n28) := ⟨u28.pc, rfl, fun _ => rfl⟩
  have m28 : n28.mem = n27.mem := u28.mem
  have fr28 : ∀ x, SvR B x → n28.mem x = n27.mem x := fun x _ => by rw [m28]
  have t28 : Steps n0 n28 := t27.trans (.single d28)
  have fR28 : ∀ x, SvR B x → n28.mem x = n0.mem x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.same m28
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_4]
  have g28_8 : reg n28 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u28.regs, upd_ne (by decide) (by decide), g27_8]
  have g28_9 : reg n28 (9 : Fin 32) = trp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_9]
  have g28_11 : reg n28 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_11]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [u28.regs, upd_ne (by decide) (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = lp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = orp := by rw [u28.regs, upd_ne (by decide) (by decide), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = tcl := by rw [u28.regs, upd_ne (by decide) (by decide), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = sgl := by rw [u28.regs, upd_ne (by decide) (by decide), g27_24]
  have g28_25 : reg n28 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u28.regs, upd_ne (by decide) (by decide), g27_25]
  have g28_26 : reg n28 (26 : Fin 32) = ll := by rw [u28.regs, upd_ne (by decide) (by decide), g27_26]
  have g28_27 : reg n28 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u28.regs, upd_ne (by decide) (by decide), g27_27]
  have g28_10 : reg n28 a0 = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by
    rw [u28.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g27_11, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0xC = B + 0x21A0 + BitVec.ofNat 32 0xA2C by sv_addr, w27_a2c]
  have w28_58 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m28]; exact w27_58
  have w28_5c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m28]; exact w27_5c
  have w28_60 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m28]; exact w27_60
  have w28_64 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m28]; exact w27_64
  have w28_68 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m28]; exact w27_68
  have w28_6c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m28]; exact w27_6c
  have w28_70 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m28]; exact w27_70
  have w28_74 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m28]; exact w27_74
  have w28_78 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m28]; exact w27_78
  have w28_7c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m28]; exact w27_7c
  have w28_80 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m28]; exact w27_80
  have w28_84 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m28]; exact w27_84
  have w28_180 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m28]; exact w27_180
  have w28_184 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m28]; exact w27_184
  have w28_240 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m28]; exact w27_240
  have w28_248 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = (((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22 := by rw [m28]; exact w27_248
  have w28_24c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 ((tl13.len) - kk22) := by rw [m28]; exact w27_24c
  have w28_a28 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m28]; exact w27_a28
  have w28_a2c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m28]; exact w27_a2c
  have b28_244 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m28]; exact b27_244
  have b28_245 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m28]; exact b27_245
  have b28_246 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m28]; exact b27_246
  have b28_247 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m28]; exact b27_247
  have b28_a20 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m28]; exact b27_a20
  have b28_a30 : n28.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m28]; exact b27_a30
  clear w27_58 b27_a30 b27_a20 b27_247 b27_246 b27_245 b27_244 w27_a2c w27_a28 w27_24c w27_248 w27_240 w27_184 w27_180 w27_84 w27_80 w27_7c w27_78 w27_74 w27_70 w27_6c w27_68 w27_64 w27_60 w27_5c g27_27 g27_26 g27_25 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_11 g27_10 g27_9 g27_8 g27_4 g27_3 g27_2 V27 E27 fR27 t27 rg27 W27 K27 fr27 s27 d27
  -- 0x2F4: sw
  obtain ⟨n29, d29, s29, fr29, K29, W29, rg29⟩ := sv_sw F E28 s28 sv_at_2f4 (off' := 0x2F6) (c := 0x54)
    (by decide) (by rw [g28_2]; sv_addr) (by decide) (by decide)
  have t29 : Steps n0 n29 := t28.trans d29
  have fR29 : ∀ x, SvR B x → n29.mem x = n0.mem x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.keep K29 (by decide)
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [rg29 sp, g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg29 (3 : Fin 32), g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg29 (4 : Fin 32), g28_4]
  have g29_8 : reg n29 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [rg29 (8 : Fin 32), g28_8]
  have g29_9 : reg n29 (9 : Fin 32) = trp := by rw [rg29 (9 : Fin 32), g28_9]
  have g29_10 : reg n29 a0 = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [rg29 a0, g28_10]
  have g29_11 : reg n29 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg29 a1, g28_11]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [rg29 (18 : Fin 32), g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [rg29 (19 : Fin 32), g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg29 (20 : Fin 32), g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = lp := by rw [rg29 (21 : Fin 32), g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = orp := by rw [rg29 (22 : Fin 32), g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = tcl := by rw [rg29 (23 : Fin 32), g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = sgl := by rw [rg29 (24 : Fin 32), g28_24]
  have g29_25 : reg n29 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [rg29 (25 : Fin 32), g28_25]
  have g29_26 : reg n29 (26 : Fin 32) = ll := by rw [rg29 (26 : Fin 32), g28_26]
  have g29_27 : reg n29 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg29 (27 : Fin 32), g28_27]
  have w29_58 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := (K29.w32 (by decide) (by decide)).trans w28_58
  have w29_5c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := (K29.w32 (by decide) (by decide)).trans w28_5c
  have w29_60 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K29.w32 (by decide) (by decide)).trans w28_60
  have w29_64 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := (K29.w32 (by decide) (by decide)).trans w28_64
  have w29_68 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K29.w32 (by decide) (by decide)).trans w28_68
  have w29_6c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K29.w32 (by decide) (by decide)).trans w28_6c
  have w29_70 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K29.w32 (by decide) (by decide)).trans w28_70
  have w29_74 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K29.w32 (by decide) (by decide)).trans w28_74
  have w29_78 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K29.w32 (by decide) (by decide)).trans w28_78
  have w29_7c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K29.w32 (by decide) (by decide)).trans w28_7c
  have w29_80 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K29.w32 (by decide) (by decide)).trans w28_80
  have w29_84 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K29.w32 (by decide) (by decide)).trans w28_84
  have w29_180 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K29.w32 (by decide) (by decide)).trans w28_180
  have w29_184 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K29.w32 (by decide) (by decide)).trans w28_184
  have w29_240 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := (K29.w32 (by decide) (by decide)).trans w28_240
  have w29_248 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = (((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22 := (K29.w32 (by decide) (by decide)).trans w28_248
  have w29_24c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 ((tl13.len) - kk22) := (K29.w32 (by decide) (by decide)).trans w28_24c
  have w29_a28 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := (K29.w32 (by decide) (by decide)).trans w28_a28
  have w29_a2c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := (K29.w32 (by decide) (by decide)).trans w28_a2c
  have b29_244 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := (K29.b8 (by decide) (by decide)).trans b28_244
  have b29_245 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K29.b8 (by decide) (by decide)).trans b28_245
  have b29_246 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K29.b8 (by decide) (by decide)).trans b28_246
  have b29_247 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K29.b8 (by decide) (by decide)).trans b28_247
  have b29_a20 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := (K29.b8 (by decide) (by decide)).trans b28_a20
  have b29_a30 : n29.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := (K29.b8 (by decide) (by decide)).trans b28_a30
  have w29_54 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [W29, g28_10]
  clear b28_a30 b28_a20 b28_247 b28_246 b28_245 b28_244 w28_a2c w28_a28 w28_24c w28_248 w28_240 w28_184 w28_180 w28_84 w28_80 w28_7c w28_78 w28_74 w28_70 w28_6c w28_68 w28_64 w28_60 w28_5c w28_58 g28_10 g28_27 g28_26 g28_25 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_11 g28_9 g28_8 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 m28 s28 u28 d28
  -- 0x2F6
  obtain ⟨n30, c30, u30⟩ := s29.block svL42f6 E29.self svL42f6_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have s30 : St n30.mem SV n30 0x300 (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have rb30 : ∀ q, reg n30 q = (runBlock svL42f6 (n29.mem, reg n29)).2 q := fun q => by rw [u30.regs]
  have fr30 : ∀ x, SvR B x → n30.mem x = n29.mem x := fun x _ => by rw [m30]
  have t30 : Steps n0 n30 := t29.trans c30
  have fR30 : ∀ x, SvR B x → n30.mem x = n0.mem x := fun x hx => (fr30 x hx).trans (fR29 x hx)
  have E30 : SvCode n30.mem := E29.fr F fr30
  have V30 : SvSaves B n30.mem v := V29.same m30
  have g30_2 : reg n30 sp = B + 0x21A0 := by
    rw [rb30, runBlock_reg _ _ _ sp s29.zero (by decide), g29_2]
  have g30_3 : reg n30 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb30, runBlock_reg _ _ _ (3 : Fin 32) s29.zero (by decide), g29_3]
  have g30_4 : reg n30 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb30, runBlock_reg _ _ _ (4 : Fin 32) s29.zero (by decide), g29_4]
  have g30_8 : reg n30 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by
    rw [rb30, runBlock_reg _ _ _ (8 : Fin 32) s29.zero (by decide), g29_8]
  have g30_9 : reg n30 (9 : Fin 32) = trp := by
    rw [rb30, runBlock_reg _ _ _ (9 : Fin 32) s29.zero (by decide), g29_9]
  have g30_18 : reg n30 (18 : Fin 32) = out := by
    rw [rb30, runBlock_reg _ _ _ (18 : Fin 32) s29.zero (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by
    rw [rb30, runBlock_reg _ _ _ (19 : Fin 32) s29.zero (by decide), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb30, runBlock_reg _ _ _ (20 : Fin 32) s29.zero (by decide), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = lp := by
    rw [rb30, runBlock_reg _ _ _ (21 : Fin 32) s29.zero (by decide), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = orp := by
    rw [rb30, runBlock_reg _ _ _ (22 : Fin 32) s29.zero (by decide), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = tcl := by
    rw [rb30, runBlock_reg _ _ _ (23 : Fin 32) s29.zero (by decide), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = sgl := by
    rw [rb30, runBlock_reg _ _ _ (24 : Fin 32) s29.zero (by decide), g29_24]
  have g30_25 : reg n30 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by
    rw [rb30, runBlock_reg _ _ _ (25 : Fin 32) s29.zero (by decide), g29_25]
  have g30_26 : reg n30 (26 : Fin 32) = ll := by
    rw [rb30, runBlock_reg _ _ _ (26 : Fin 32) s29.zero (by decide), g29_26]
  have g30_27 : reg n30 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb30, runBlock_reg _ _ _ (27 : Fin 32) s29.zero (by decide), g29_27]
  have g30_10 : reg n30 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb30]; simp +decide only [runBlock, BInstr.run, svL42f6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g29_2, g29_3, g29_4, g29_8, g29_9, g29_10, g29_11, g29_18, g29_19, g29_20, g29_21, g29_22, g29_23, g29_24, g29_25, g29_26, g29_27, s29.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g30_11 : reg n30 a1 = B + 0x21A0 + BitVec.ofNat 32 0x240 := by
    rw [rb30]; simp +decide only [runBlock, BInstr.run, svL42f6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g29_2, g29_3, g29_4, g29_8, g29_9, g29_10, g29_11, g29_18, g29_19, g29_20, g29_21, g29_22, g29_23, g29_24, g29_25, g29_26, g29_27, s29.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w30_54 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m30]; exact w29_54
  have w30_58 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m30]; exact w29_58
  have w30_5c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m30]; exact w29_5c
  have w30_60 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m30]; exact w29_60
  have w30_64 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m30]; exact w29_64
  have w30_68 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m30]; exact w29_68
  have w30_6c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m30]; exact w29_6c
  have w30_70 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m30]; exact w29_70
  have w30_74 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m30]; exact w29_74
  have w30_78 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m30]; exact w29_78
  have w30_7c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m30]; exact w29_7c
  have w30_80 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m30]; exact w29_80
  have w30_84 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m30]; exact w29_84
  have w30_180 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m30]; exact w29_180
  have w30_184 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m30]; exact w29_184
  have w30_240 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m30]; exact w29_240
  have w30_248 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = (((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22 := by rw [m30]; exact w29_248
  have w30_24c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 ((tl13.len) - kk22) := by rw [m30]; exact w29_24c
  have w30_a28 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m30]; exact w29_a28
  have w30_a2c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m30]; exact w29_a2c
  have b30_244 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m30]; exact b29_244
  have b30_245 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m30]; exact b29_245
  have b30_246 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m30]; exact b29_246
  have b30_247 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m30]; exact b29_247
  have b30_a20 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m30]; exact b29_a20
  have b30_a30 : n30.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m30]; exact b29_a30
  clear w29_54 b29_a30 b29_a20 b29_247 b29_246 b29_245 b29_244 w29_a2c w29_a28 w29_24c w29_248 w29_240 w29_184 w29_180 w29_84 w29_80 w29_7c w29_78 w29_74 w29_70 w29_6c w29_68 w29_64 w29_60 w29_5c w29_58 g29_27 g29_26 g29_25 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_11 g29_10 g29_9 g29_8 g29_4 g29_3 g29_2 V29 E29 fR29 t29 rg29 W29 K29 fr29 s29 d29
  -- 0x300: sv_rtF
  obtain ⟨n31, c31, s31, sp31, rk31, K31, Ok31, Er31, fr31⟩ := sv_rtF (oc := 0xA20) (dc := 0x240) (rl := (tl13.len) - kk22)
    F E30 s30 sv_at_300 sv_at_304 (by decide) (by decide) g30_2 g30_10 g30_11 (by decide) (by decide) (by decide) (by decide)
    (by decide) w30_248 w30_24c (((tb_in.restW hr6).content hr13).drop hkk22)
  have t31 : Steps n0 n31 := t30.trans c31
  have fR31 : ∀ x, SvR B x → n31.mem x = n0.mem x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.keepL K31 (by decide)
  rw [sv_mb fR30 (((tb_in.restW hr6).content hr13).drop hkk22)] at Ok31 Er31
  rw [← hrb22] at Ok31 Er31
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk31 (3 : Fin 32) (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk31 (4 : Fin 32) (by decide), g30_4]
  have g31_8 : reg n31 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [rk31 (8 : Fin 32) (by decide), g30_8]
  have g31_9 : reg n31 (9 : Fin 32) = trp := by rw [rk31 (9 : Fin 32) (by decide), g30_9]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [rk31 (18 : Fin 32) (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [rk31 (19 : Fin 32) (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [rk31 (20 : Fin 32) (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = lp := by rw [rk31 (21 : Fin 32) (by decide), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = orp := by rw [rk31 (22 : Fin 32) (by decide), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = tcl := by rw [rk31 (23 : Fin 32) (by decide), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = sgl := by rw [rk31 (24 : Fin 32) (by decide), g30_24]
  have g31_25 : reg n31 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [rk31 (25 : Fin 32) (by decide), g30_25]
  have g31_26 : reg n31 (26 : Fin 32) = ll := by rw [rk31 (26 : Fin 32) (by decide), g30_26]
  have g31_27 : reg n31 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rk31 (27 : Fin 32) (by decide), g30_27]
  have g31_2 : reg n31 sp = B + 0x21A0 := sp31
  obtain ⟨r31, hr31⟩ : ∃ r, readTime rs22 = r := ⟨_, rfl⟩
  rcases r31 with _ | ⟨tm31, rs31⟩
  · have y0_31 := Er31 hr31
    have w31_54 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := (K31.w32 (by decide) (by decide)).trans w30_54
    have w31_58 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := (K31.w32 (by decide) (by decide)).trans w30_58
    have w31_5c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := (K31.w32 (by decide) (by decide)).trans w30_5c
    have w31_60 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K31.w32 (by decide) (by decide)).trans w30_60
    have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := (K31.w32 (by decide) (by decide)).trans w30_64
    have w31_68 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K31.w32 (by decide) (by decide)).trans w30_68
    have w31_6c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K31.w32 (by decide) (by decide)).trans w30_6c
    have w31_70 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K31.w32 (by decide) (by decide)).trans w30_70
    have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K31.w32 (by decide) (by decide)).trans w30_74
    have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K31.w32 (by decide) (by decide)).trans w30_78
    have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K31.w32 (by decide) (by decide)).trans w30_7c
    have w31_80 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K31.w32 (by decide) (by decide)).trans w30_80
    have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K31.w32 (by decide) (by decide)).trans w30_84
    have w31_180 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K31.w32 (by decide) (by decide)).trans w30_180
    have w31_184 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K31.w32 (by decide) (by decide)).trans w30_184
    have w31_240 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := (K31.w32 (by decide) (by decide)).trans w30_240
    have b31_244 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := (K31.b8 (by decide) (by decide)).trans b30_244
    have b31_245 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K31.b8 (by decide) (by decide)).trans b30_245
    have b31_246 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K31.b8 (by decide) (by decide)).trans b30_246
    have b31_247 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K31.b8 (by decide) (by decide)).trans b30_247
    have b31_a30 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := (K31.b8 (by decide) (by decide)).trans b30_a30
    have b31_a20 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := y0_31
    clear b30_a30 b30_a20 b30_247 b30_246 b30_245 b30_244 w30_a2c w30_a28 w30_24c w30_248 w30_240 w30_184 w30_180 w30_84 w30_80 w30_7c w30_78 w30_74 w30_70 w30_6c w30_68 w30_64 w30_60 w30_5c w30_58 w30_54 g30_11 g30_10 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 rb30 s30 m30 u30 c30
    -- 0x308: lbu
    obtain ⟨n32, d32, u32⟩ := s31.lbu E31.self sv_at_308 (off' := 0x30C) (by decide)
    have s32 : St n32.mem SV n32 0x30C (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
    have m32 : n32.mem = n31.mem := u32.mem
    have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
    have t32 : Steps n0 n32 := t31.trans (.single d32)
    have fR32 : ∀ x, SvR B x → n32.mem x = n0.mem x := fun x hx => (fr32 x hx).trans (fR31 x hx)
    have E32 : SvCode n32.mem := E31.fr F fr32
    have V32 : SvSaves B n32.mem v := V31.same m32
    have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_2]
    have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_3]
    have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_4]
    have g32_8 : reg n32 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u32.regs, upd_ne (by decide) (by decide), g31_8]
    have g32_9 : reg n32 (9 : Fin 32) = trp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_9]
    have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, upd_ne (by decide) (by decide), g31_18]
    have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_19]
    have g32_20 : reg n32 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_20]
    have g32_21 : reg n32 (21 : Fin 32) = lp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_21]
    have g32_22 : reg n32 (22 : Fin 32) = orp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_22]
    have g32_23 : reg n32 (23 : Fin 32) = tcl := by rw [u32.regs, upd_ne (by decide) (by decide), g31_23]
    have g32_24 : reg n32 (24 : Fin 32) = sgl := by rw [u32.regs, upd_ne (by decide) (by decide), g31_24]
    have g32_25 : reg n32 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_25]
    have g32_26 : reg n32 (26 : Fin 32) = ll := by rw [u32.regs, upd_ne (by decide) (by decide), g31_26]
    have g32_27 : reg n32 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_27]
    have g32_10 : reg n32 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [u32.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g31_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, b31_a20]
    have w32_54 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m32]; exact w31_54
    have w32_58 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m32]; exact w31_58
    have w32_5c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m32]; exact w31_5c
    have w32_60 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m32]; exact w31_60
    have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m32]; exact w31_64
    have w32_68 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m32]; exact w31_68
    have w32_6c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m32]; exact w31_6c
    have w32_70 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m32]; exact w31_70
    have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m32]; exact w31_74
    have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m32]; exact w31_78
    have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m32]; exact w31_7c
    have w32_80 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m32]; exact w31_80
    have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m32]; exact w31_84
    have w32_180 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m32]; exact w31_180
    have w32_184 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m32]; exact w31_184
    have w32_240 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m32]; exact w31_240
    have b32_244 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m32]; exact b31_244
    have b32_245 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m32]; exact b31_245
    have b32_246 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m32]; exact b31_246
    have b32_247 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m32]; exact b31_247
    have b32_a20 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := by rw [m32]; exact b31_a20
    have b32_a30 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m32]; exact b31_a30
    clear b31_a20 b31_a30 b31_247 b31_246 b31_245 b31_244 w31_240 w31_184 w31_180 w31_84 w31_80 w31_7c w31_78 w31_74 w31_70 w31_6c w31_68 w31_64 w31_60 w31_5c w31_58 w31_54 y0_31
    -- 0x30C: branch, taken
    obtain ⟨n33, d33, u33⟩ := s32.taken E32.self 0x17E sv_at_30c
      (by decide) (by rw [g32_10, s32.zero]; decide)
    have s33 : St n33.mem SV n33 0x17E (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
    have m33 : n33.mem = n32.mem := u33.mem
    have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
    have t33 : Steps n0 n33 := t32.trans (.single d33)
    have fR33 : ∀ x, SvR B x → n33.mem x = n0.mem x := fun x hx => (fr33 x hx).trans (fR32 x hx)
    have E33 : SvCode n33.mem := E32.fr F fr33
    have V33 : SvSaves B n33.mem v := V32.same m33
    have g33_2 : reg n33 sp = B + 0x21A0 := by rw [u33.regs, g32_2]
    have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u33.regs, g32_3]
    have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u33.regs, g32_4]
    have g33_8 : reg n33 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u33.regs, g32_8]
    have g33_9 : reg n33 (9 : Fin 32) = trp := by rw [u33.regs, g32_9]
    have g33_10 : reg n33 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u33.regs, g32_10]
    have g33_18 : reg n33 (18 : Fin 32) = out := by rw [u33.regs, g32_18]
    have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [u33.regs, g32_19]
    have g33_20 : reg n33 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [u33.regs, g32_20]
    have g33_21 : reg n33 (21 : Fin 32) = lp := by rw [u33.regs, g32_21]
    have g33_22 : reg n33 (22 : Fin 32) = orp := by rw [u33.regs, g32_22]
    have g33_23 : reg n33 (23 : Fin 32) = tcl := by rw [u33.regs, g32_23]
    have g33_24 : reg n33 (24 : Fin 32) = sgl := by rw [u33.regs, g32_24]
    have g33_25 : reg n33 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u33.regs, g32_25]
    have g33_26 : reg n33 (26 : Fin 32) = ll := by rw [u33.regs, g32_26]
    have g33_27 : reg n33 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u33.regs, g32_27]
    have w33_54 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m33]; exact w32_54
    have w33_58 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m33]; exact w32_58
    have w33_5c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m33]; exact w32_5c
    have w33_60 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m33]; exact w32_60
    have w33_64 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m33]; exact w32_64
    have w33_68 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m33]; exact w32_68
    have w33_6c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m33]; exact w32_6c
    have w33_70 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m33]; exact w32_70
    have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m33]; exact w32_74
    have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m33]; exact w32_78
    have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m33]; exact w32_7c
    have w33_80 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m33]; exact w32_80
    have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m33]; exact w32_84
    have w33_180 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m33]; exact w32_180
    have w33_184 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m33]; exact w32_184
    have w33_240 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m33]; exact w32_240
    have b33_244 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m33]; exact b32_244
    have b33_245 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m33]; exact b32_245
    have b33_246 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m33]; exact b32_246
    have b33_247 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m33]; exact b32_247
    have b33_a20 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := by rw [m33]; exact b32_a20
    have b33_a30 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m33]; exact b32_a30
    clear b32_a30 b32_a20 b32_247 b32_246 b32_245 b32_244 w32_240 w32_184 w32_180 w32_84 w32_80 w32_7c w32_78 w32_74 w32_70 w32_6c w32_68 w32_64 w32_60 w32_5c w32_58 w32_54 g32_10 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
    -- 0x17E: lbu
    obtain ⟨n34, d34, u34⟩ := s33.lbu E33.self sv_at_17e (off' := 0x182) (by decide)
    have s34 : St n34.mem SV n34 0x182 (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
    have m34 : n34.mem = n33.mem := u34.mem
    have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
    have t34 : Steps n0 n34 := t33.trans (.single d34)
    have fR34 : ∀ x, SvR B x → n34.mem x = n0.mem x := fun x hx => (fr34 x hx).trans (fR33 x hx)
    have E34 : SvCode n34.mem := E33.fr F fr34
    have V34 : SvSaves B n34.mem v := V33.same m34
    have g34_2 : reg n34 sp = B + 0x21A0 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_2]
    have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_3]
    have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_4]
    have g34_8 : reg n34 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u34.regs, upd_ne (by decide) (by decide), g33_8]
    have g34_9 : reg n34 (9 : Fin 32) = trp := by rw [u34.regs, upd_ne (by decide) (by decide), g33_9]
    have g34_10 : reg n34 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_10]
    have g34_18 : reg n34 (18 : Fin 32) = out := by rw [u34.regs, upd_ne (by decide) (by decide), g33_18]
    have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [u34.regs, upd_ne (by decide) (by decide), g33_19]
    have g34_21 : reg n34 (21 : Fin 32) = lp := by rw [u34.regs, upd_ne (by decide) (by decide), g33_21]
    have g34_22 : reg n34 (22 : Fin 32) = orp := by rw [u34.regs, upd_ne (by decide) (by decide), g33_22]
    have g34_23 : reg n34 (23 : Fin 32) = tcl := by rw [u34.regs, upd_ne (by decide) (by decide), g33_23]
    have g34_24 : reg n34 (24 : Fin 32) = sgl := by rw [u34.regs, upd_ne (by decide) (by decide), g33_24]
    have g34_25 : reg n34 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_25]
    have g34_26 : reg n34 (26 : Fin 32) = ll := by rw [u34.regs, upd_ne (by decide) (by decide), g33_26]
    have g34_27 : reg n34 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_27]
    have w34_54 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m34]; exact w33_54
    have w34_58 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m34]; exact w33_58
    have w34_5c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m34]; exact w33_5c
    have w34_60 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m34]; exact w33_60
    have w34_64 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m34]; exact w33_64
    have w34_68 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m34]; exact w33_68
    have w34_6c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m34]; exact w33_6c
    have w34_70 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m34]; exact w33_70
    have w34_74 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m34]; exact w33_74
    have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m34]; exact w33_78
    have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m34]; exact w33_7c
    have w34_80 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m34]; exact w33_80
    have w34_84 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m34]; exact w33_84
    have w34_180 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m34]; exact w33_180
    have w34_184 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m34]; exact w33_184
    have w34_240 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m34]; exact w33_240
    have b34_244 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m34]; exact b33_244
    have b34_245 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m34]; exact b33_245
    have b34_246 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m34]; exact b33_246
    have b34_247 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m34]; exact b33_247
    have b34_a20 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := by rw [m34]; exact b33_a20
    have b34_a30 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m34]; exact b33_a30
    clear b33_a30 b33_a20 b33_247 b33_246 b33_245 b33_244 w33_240 w33_184 w33_180 w33_84 w33_80 w33_7c w33_78 w33_74 w33_70 w33_6c w33_68 w33_64 w33_60 w33_5c w33_58 w33_54 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_10 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 m33 s33 u33 d33
    -- 0x182: j
    obtain ⟨n35, d35, u35⟩ := s34.jump E34.self sv_at_182 (off' := 0x966) (by decide)
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
    have g35_8 : reg n35 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u35.regs, g34_8]
    have g35_9 : reg n35 (9 : Fin 32) = trp := by rw [u35.regs, g34_9]
    have g35_10 : reg n35 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u35.regs, g34_10]
    have g35_18 : reg n35 (18 : Fin 32) = out := by rw [u35.regs, g34_18]
    have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [u35.regs, g34_19]
    have g35_21 : reg n35 (21 : Fin 32) = lp := by rw [u35.regs, g34_21]
    have g35_22 : reg n35 (22 : Fin 32) = orp := by rw [u35.regs, g34_22]
    have g35_23 : reg n35 (23 : Fin 32) = tcl := by rw [u35.regs, g34_23]
    have g35_24 : reg n35 (24 : Fin 32) = sgl := by rw [u35.regs, g34_24]
    have g35_25 : reg n35 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u35.regs, g34_25]
    have g35_26 : reg n35 (26 : Fin 32) = ll := by rw [u35.regs, g34_26]
    have g35_27 : reg n35 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u35.regs, g34_27]
    have w35_54 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m35]; exact w34_54
    have w35_58 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m35]; exact w34_58
    have w35_5c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m35]; exact w34_5c
    have w35_60 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m35]; exact w34_60
    have w35_64 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m35]; exact w34_64
    have w35_68 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m35]; exact w34_68
    have w35_6c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m35]; exact w34_6c
    have w35_70 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m35]; exact w34_70
    have w35_74 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m35]; exact w34_74
    have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m35]; exact w34_78
    have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m35]; exact w34_7c
    have w35_80 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m35]; exact w34_80
    have w35_84 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m35]; exact w34_84
    have w35_180 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m35]; exact w34_180
    have w35_184 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m35]; exact w34_184
    have w35_240 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m35]; exact w34_240
    have b35_244 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m35]; exact b34_244
    have b35_245 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m35]; exact b34_245
    have b35_246 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m35]; exact b34_246
    have b35_247 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m35]; exact b34_247
    have b35_a20 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (1 : BitVec 8) := by rw [m35]; exact b34_a20
    have b35_a30 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m35]; exact b34_a30
    clear b34_a30 b34_a20 b34_247 b34_246 b34_245 b34_244 w34_240 w34_184 w34_180 w34_84 w34_80 w34_7c w34_78 w34_74 w34_70 w34_6c w34_68 w34_64 w34_60 w34_5c w34_58 w34_54 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_19 g34_18 g34_10 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 m34 s34 u34 d34
    exact .inl ⟨(fun ⟨tl6', h0', tl13', h1', tm22', rs22', h2', tm31', rs31', h3', _⟩ => by rw [hr6] at h0'; cases h0'; rw [hr13] at h1'; cases h1'; rw [hr22] at h2'; cases h2'; rw [hr31] at h3'; cases h3'), sv_fail F E35 s35 t35 fR35 V35 hret g35_2 g35_18 hO g35_3 g35_4⟩
  obtain ⟨h64_31, y0_31, y8_31, y12_31, kk31, hkk31, d8_31, d12_31, hrb31⟩ := Ok31 tm31 rs31 hr31
  rw [sv_mb fR30 ((((tb_in.restW hr6).content hr13).drop hkk22).drop hkk31)] at hrb31
  have w31_54 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := (K31.w32 (by decide) (by decide)).trans w30_54
  have w31_58 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := (K31.w32 (by decide) (by decide)).trans w30_58
  have w31_5c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := (K31.w32 (by decide) (by decide)).trans w30_5c
  have w31_60 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K31.w32 (by decide) (by decide)).trans w30_60
  have w31_64 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := (K31.w32 (by decide) (by decide)).trans w30_64
  have w31_68 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K31.w32 (by decide) (by decide)).trans w30_68
  have w31_6c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K31.w32 (by decide) (by decide)).trans w30_6c
  have w31_70 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K31.w32 (by decide) (by decide)).trans w30_70
  have w31_74 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K31.w32 (by decide) (by decide)).trans w30_74
  have w31_78 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K31.w32 (by decide) (by decide)).trans w30_78
  have w31_7c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K31.w32 (by decide) (by decide)).trans w30_7c
  have w31_80 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K31.w32 (by decide) (by decide)).trans w30_80
  have w31_84 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K31.w32 (by decide) (by decide)).trans w30_84
  have w31_180 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K31.w32 (by decide) (by decide)).trans w30_180
  have w31_184 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K31.w32 (by decide) (by decide)).trans w30_184
  have w31_240 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := (K31.w32 (by decide) (by decide)).trans w30_240
  have b31_244 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := (K31.b8 (by decide) (by decide)).trans b30_244
  have b31_245 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K31.b8 (by decide) (by decide)).trans b30_245
  have b31_246 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K31.b8 (by decide) (by decide)).trans b30_246
  have b31_247 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K31.b8 (by decide) (by decide)).trans b30_247
  have b31_a30 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := (K31.b8 (by decide) (by decide)).trans b30_a30
  have w31_248 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = ((((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22) + BitVec.ofNat 32 kk31 := d8_31
  have w31_24c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 (((tl13.len) - kk22) - kk31) := d12_31
  have w31_a28 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm31 % 2 ^ 32) := y8_31
  have w31_a2c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm31 / 2 ^ 32) := y12_31
  have b31_a20 : n31.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := y0_31
  clear b30_a30 b30_a20 b30_247 b30_246 b30_245 b30_244 w30_a2c w30_a28 w30_24c w30_248 w30_240 w30_184 w30_180 w30_84 w30_80 w30_7c w30_78 w30_74 w30_70 w30_6c w30_68 w30_64 w30_60 w30_5c w30_58 w30_54 g30_11 g30_10 g30_27 g30_26 g30_25 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_9 g30_8 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 rb30 s30 m30 u30 c30
  -- 0x308: lbu
  obtain ⟨n32, d32, u32⟩ := s31.lbu E31.self sv_at_308 (off' := 0x30C) (by decide)
  have s32 : St n32.mem SV n32 0x30C (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans (.single d32)
  have fR32 : ∀ x, SvR B x → n32.mem x = n0.mem x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_4]
  have g32_8 : reg n32 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u32.regs, upd_ne (by decide) (by decide), g31_8]
  have g32_9 : reg n32 (9 : Fin 32) = trp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_9]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, upd_ne (by decide) (by decide), g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = lp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = orp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = tcl := by rw [u32.regs, upd_ne (by decide) (by decide), g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = sgl := by rw [u32.regs, upd_ne (by decide) (by decide), g31_24]
  have g32_25 : reg n32 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_25]
  have g32_26 : reg n32 (26 : Fin 32) = ll := by rw [u32.regs, upd_ne (by decide) (by decide), g31_26]
  have g32_27 : reg n32 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_27]
  have g32_10 : reg n32 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [u32.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g31_27, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x0 = B + 0x21A0 + BitVec.ofNat 32 0xA20 by sv_addr, b31_a20]
  have w32_54 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m32]; exact w31_54
  have w32_58 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m32]; exact w31_58
  have w32_5c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m32]; exact w31_5c
  have w32_60 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m32]; exact w31_60
  have w32_64 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m32]; exact w31_64
  have w32_68 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m32]; exact w31_68
  have w32_6c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m32]; exact w31_6c
  have w32_70 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m32]; exact w31_70
  have w32_74 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m32]; exact w31_74
  have w32_78 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m32]; exact w31_78
  have w32_7c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m32]; exact w31_7c
  have w32_80 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m32]; exact w31_80
  have w32_84 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m32]; exact w31_84
  have w32_180 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m32]; exact w31_180
  have w32_184 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m32]; exact w31_184
  have w32_240 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m32]; exact w31_240
  have w32_248 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = ((((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22) + BitVec.ofNat 32 kk31 := by rw [m32]; exact w31_248
  have w32_24c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 (((tl13.len) - kk22) - kk31) := by rw [m32]; exact w31_24c
  have w32_a28 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm31 % 2 ^ 32) := by rw [m32]; exact w31_a28
  have w32_a2c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm31 / 2 ^ 32) := by rw [m32]; exact w31_a2c
  have b32_244 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m32]; exact b31_244
  have b32_245 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m32]; exact b31_245
  have b32_246 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m32]; exact b31_246
  have b32_247 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m32]; exact b31_247
  have b32_a20 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m32]; exact b31_a20
  have b32_a30 : n32.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m32]; exact b31_a30
  clear b31_a20 w31_a2c w31_a28 w31_24c w31_248 b31_a30 b31_247 b31_246 b31_245 b31_244 w31_240 w31_184 w31_180 w31_84 w31_80 w31_7c w31_78 w31_74 w31_70 w31_6c w31_68 w31_64 w31_60 w31_5c w31_58 w31_54 d12_31 d8_31 y12_31 y8_31 y0_31 g31_2 g31_27 g31_26 g31_25 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_9 g31_8 g31_4 g31_3 V31 E31 fR31 t31 fr31 Er31 Ok31 K31 rk31 sp31 s31 c31
  -- 0x30C: branch, not taken
  obtain ⟨n33, d33, u33⟩ := s32.notTaken E32.self 0x310 sv_at_30c
    (by decide) (by rw [g32_10, s32.zero]; decide)
  have s33 : St n33.mem SV n33 0x310 (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
  have t33 : Steps n0 n33 := t32.trans (.single d33)
  have fR33 : ∀ x, SvR B x → n33.mem x = n0.mem x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.same m33
  have g33_2 : reg n33 sp = B + 0x21A0 := by rw [u33.regs, g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u33.regs, g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u33.regs, g32_4]
  have g33_8 : reg n33 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u33.regs, g32_8]
  have g33_9 : reg n33 (9 : Fin 32) = trp := by rw [u33.regs, g32_9]
  have g33_10 : reg n33 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u33.regs, g32_10]
  have g33_18 : reg n33 (18 : Fin 32) = out := by rw [u33.regs, g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [u33.regs, g32_19]
  have g33_20 : reg n33 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [u33.regs, g32_20]
  have g33_21 : reg n33 (21 : Fin 32) = lp := by rw [u33.regs, g32_21]
  have g33_22 : reg n33 (22 : Fin 32) = orp := by rw [u33.regs, g32_22]
  have g33_23 : reg n33 (23 : Fin 32) = tcl := by rw [u33.regs, g32_23]
  have g33_24 : reg n33 (24 : Fin 32) = sgl := by rw [u33.regs, g32_24]
  have g33_25 : reg n33 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u33.regs, g32_25]
  have g33_26 : reg n33 (26 : Fin 32) = ll := by rw [u33.regs, g32_26]
  have g33_27 : reg n33 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u33.regs, g32_27]
  have w33_54 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m33]; exact w32_54
  have w33_58 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m33]; exact w32_58
  have w33_5c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m33]; exact w32_5c
  have w33_60 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m33]; exact w32_60
  have w33_64 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m33]; exact w32_64
  have w33_68 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m33]; exact w32_68
  have w33_6c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m33]; exact w32_6c
  have w33_70 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m33]; exact w32_70
  have w33_74 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m33]; exact w32_74
  have w33_78 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m33]; exact w32_78
  have w33_7c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m33]; exact w32_7c
  have w33_80 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m33]; exact w32_80
  have w33_84 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m33]; exact w32_84
  have w33_180 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m33]; exact w32_180
  have w33_184 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m33]; exact w32_184
  have w33_240 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m33]; exact w32_240
  have w33_248 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = ((((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22) + BitVec.ofNat 32 kk31 := by rw [m33]; exact w32_248
  have w33_24c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 (((tl13.len) - kk22) - kk31) := by rw [m33]; exact w32_24c
  have w33_a28 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm31 % 2 ^ 32) := by rw [m33]; exact w32_a28
  have w33_a2c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm31 / 2 ^ 32) := by rw [m33]; exact w32_a2c
  have b33_244 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m33]; exact b32_244
  have b33_245 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m33]; exact b32_245
  have b33_246 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m33]; exact b32_246
  have b33_247 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m33]; exact b32_247
  have b33_a20 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m33]; exact b32_a20
  have b33_a30 : n33.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m33]; exact b32_a30
  clear b32_a30 b32_a20 b32_247 b32_246 b32_245 b32_244 w32_a2c w32_a28 w32_24c w32_248 w32_240 w32_184 w32_180 w32_84 w32_80 w32_7c w32_78 w32_74 w32_70 w32_6c w32_68 w32_64 w32_60 w32_5c w32_58 w32_54 g32_10 g32_27 g32_26 g32_25 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_9 g32_8 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
  -- 0x310: lw
  obtain ⟨n34, d34, u34⟩ := s33.lw E33.self sv_at_310 (off' := 0x314) (by decide)
    (by rw [g33_2, show B + 0x21A0 + 0x24C = B + 0x21A0 + BitVec.ofNat 32 0x24C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s34 : St n34.mem SV n34 0x314 (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
  have m34 : n34.mem = n33.mem := u34.mem
  have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
  have t34 : Steps n0 n34 := t33.trans (.single d34)
  have fR34 : ∀ x, SvR B x → n34.mem x = n0.mem x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.same m34
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_4]
  have g34_8 : reg n34 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u34.regs, upd_ne (by decide) (by decide), g33_8]
  have g34_9 : reg n34 (9 : Fin 32) = trp := by rw [u34.regs, upd_ne (by decide) (by decide), g33_9]
  have g34_18 : reg n34 (18 : Fin 32) = out := by rw [u34.regs, upd_ne (by decide) (by decide), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [u34.regs, upd_ne (by decide) (by decide), g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = lp := by rw [u34.regs, upd_ne (by decide) (by decide), g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = orp := by rw [u34.regs, upd_ne (by decide) (by decide), g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = tcl := by rw [u34.regs, upd_ne (by decide) (by decide), g33_23]
  have g34_24 : reg n34 (24 : Fin 32) = sgl := by rw [u34.regs, upd_ne (by decide) (by decide), g33_24]
  have g34_25 : reg n34 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_25]
  have g34_26 : reg n34 (26 : Fin 32) = ll := by rw [u34.regs, upd_ne (by decide) (by decide), g33_26]
  have g34_27 : reg n34 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_27]
  have g34_10 : reg n34 a0 = BitVec.ofNat 32 (((tl13.len) - kk22) - kk31) := by
    rw [u34.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g33_2, show B + 0x21A0 + 0x24C = B + 0x21A0 + BitVec.ofNat 32 0x24C by sv_addr, w33_24c]
  have w34_54 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m34]; exact w33_54
  have w34_58 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m34]; exact w33_58
  have w34_5c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m34]; exact w33_5c
  have w34_60 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m34]; exact w33_60
  have w34_64 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m34]; exact w33_64
  have w34_68 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m34]; exact w33_68
  have w34_6c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m34]; exact w33_6c
  have w34_70 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m34]; exact w33_70
  have w34_74 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m34]; exact w33_74
  have w34_78 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m34]; exact w33_78
  have w34_7c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m34]; exact w33_7c
  have w34_80 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m34]; exact w33_80
  have w34_84 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m34]; exact w33_84
  have w34_180 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m34]; exact w33_180
  have w34_184 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m34]; exact w33_184
  have w34_240 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m34]; exact w33_240
  have w34_248 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = ((((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22) + BitVec.ofNat 32 kk31 := by rw [m34]; exact w33_248
  have w34_24c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 (((tl13.len) - kk22) - kk31) := by rw [m34]; exact w33_24c
  have w34_a28 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm31 % 2 ^ 32) := by rw [m34]; exact w33_a28
  have w34_a2c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm31 / 2 ^ 32) := by rw [m34]; exact w33_a2c
  have b34_244 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m34]; exact b33_244
  have b34_245 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m34]; exact b33_245
  have b34_246 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m34]; exact b33_246
  have b34_247 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m34]; exact b33_247
  have b34_a20 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m34]; exact b33_a20
  have b34_a30 : n34.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m34]; exact b33_a30
  clear b33_a30 b33_a20 b33_247 b33_246 b33_245 b33_244 w33_a2c w33_a28 w33_24c w33_248 w33_240 w33_184 w33_180 w33_84 w33_80 w33_7c w33_78 w33_74 w33_70 w33_6c w33_68 w33_64 w33_60 w33_5c w33_58 w33_54 g33_27 g33_26 g33_25 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_10 g33_9 g33_8 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 m33 s33 u33 d33
  by_cases hz_34 : rs31 = []
  rotate_left
  · -- 0x314: branch, taken
    obtain ⟨n35, d35, u35⟩ := s34.taken E34.self 0x1C0 sv_at_314
      (by decide) (by rw [g34_10, s34.zero]; exact br_bne_t (rest_ne (by have := ((((tb_in.restW hr6).content hr13).drop hkk22).drop hkk31).fit; omega) hrb31 hz_34))
    have s35 : St n35.mem SV n35 0x1C0 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
    have m35 : n35.mem = n34.mem := u35.mem
    have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
    have t35 : Steps n0 n35 := t34.trans (.single d35)
    have fR35 : ∀ x, SvR B x → n35.mem x = n0.mem x := fun x hx => (fr35 x hx).trans (fR34 x hx)
    have E35 : SvCode n35.mem := E34.fr F fr35
    have V35 : SvSaves B n35.mem v := V34.same m35
    have g35_2 : reg n35 sp = B + 0x21A0 := by rw [u35.regs, g34_2]
    have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u35.regs, g34_3]
    have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u35.regs, g34_4]
    have g35_8 : reg n35 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u35.regs, g34_8]
    have g35_9 : reg n35 (9 : Fin 32) = trp := by rw [u35.regs, g34_9]
    have g35_10 : reg n35 a0 = BitVec.ofNat 32 (((tl13.len) - kk22) - kk31) := by rw [u35.regs, g34_10]
    have g35_18 : reg n35 (18 : Fin 32) = out := by rw [u35.regs, g34_18]
    have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [u35.regs, g34_19]
    have g35_20 : reg n35 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [u35.regs, g34_20]
    have g35_21 : reg n35 (21 : Fin 32) = lp := by rw [u35.regs, g34_21]
    have g35_22 : reg n35 (22 : Fin 32) = orp := by rw [u35.regs, g34_22]
    have g35_23 : reg n35 (23 : Fin 32) = tcl := by rw [u35.regs, g34_23]
    have g35_24 : reg n35 (24 : Fin 32) = sgl := by rw [u35.regs, g34_24]
    have g35_25 : reg n35 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u35.regs, g34_25]
    have g35_26 : reg n35 (26 : Fin 32) = ll := by rw [u35.regs, g34_26]
    have g35_27 : reg n35 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u35.regs, g34_27]
    have w35_54 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m35]; exact w34_54
    have w35_58 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m35]; exact w34_58
    have w35_5c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m35]; exact w34_5c
    have w35_60 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m35]; exact w34_60
    have w35_64 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m35]; exact w34_64
    have w35_68 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m35]; exact w34_68
    have w35_6c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m35]; exact w34_6c
    have w35_70 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m35]; exact w34_70
    have w35_74 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m35]; exact w34_74
    have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m35]; exact w34_78
    have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m35]; exact w34_7c
    have w35_80 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m35]; exact w34_80
    have w35_84 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m35]; exact w34_84
    have w35_180 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m35]; exact w34_180
    have w35_184 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m35]; exact w34_184
    have w35_240 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m35]; exact w34_240
    have w35_248 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = ((((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22) + BitVec.ofNat 32 kk31 := by rw [m35]; exact w34_248
    have w35_24c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 (((tl13.len) - kk22) - kk31) := by rw [m35]; exact w34_24c
    have w35_a28 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm31 % 2 ^ 32) := by rw [m35]; exact w34_a28
    have w35_a2c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm31 / 2 ^ 32) := by rw [m35]; exact w34_a2c
    have b35_244 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m35]; exact b34_244
    have b35_245 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m35]; exact b34_245
    have b35_246 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m35]; exact b34_246
    have b35_247 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m35]; exact b34_247
    have b35_a20 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m35]; exact b34_a20
    have b35_a30 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m35]; exact b34_a30
    clear b34_a30 b34_a20 b34_247 b34_246 b34_245 b34_244 w34_a2c w34_a28 w34_24c w34_248 w34_240 w34_184 w34_180 w34_84 w34_80 w34_7c w34_78 w34_74 w34_70 w34_6c w34_68 w34_64 w34_60 w34_5c w34_58 w34_54 g34_10 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 m34 s34 u34 d34
    -- 0x1C0
    obtain ⟨n36, c36, u36⟩ := s35.block svL41c0 E35.self svL41c0_end
      ⟨trivial, trivial⟩
    have m36 : n36.mem = n35.mem := u36.mem
    have s36 : St n36.mem SV n36 0x1C2 (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
    have rb36 : ∀ q, reg n36 q = (runBlock svL41c0 (n35.mem, reg n35)).2 q := fun q => by rw [u36.regs]
    have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
    have t36 : Steps n0 n36 := t35.trans c36
    have fR36 : ∀ x, SvR B x → n36.mem x = n0.mem x := fun x hx => (fr36 x hx).trans (fR35 x hx)
    have E36 : SvCode n36.mem := E35.fr F fr36
    have V36 : SvSaves B n36.mem v := V35.same m36
    have g36_2 : reg n36 sp = B + 0x21A0 := by
      rw [rb36, runBlock_reg _ _ _ sp s35.zero (by decide), g35_2]
    have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
      rw [rb36, runBlock_reg _ _ _ (3 : Fin 32) s35.zero (by decide), g35_3]
    have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
      rw [rb36, runBlock_reg _ _ _ (4 : Fin 32) s35.zero (by decide), g35_4]
    have g36_8 : reg n36 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by
      rw [rb36, runBlock_reg _ _ _ (8 : Fin 32) s35.zero (by decide), g35_8]
    have g36_9 : reg n36 (9 : Fin 32) = trp := by
      rw [rb36, runBlock_reg _ _ _ (9 : Fin 32) s35.zero (by decide), g35_9]
    have g36_10 : reg n36 a0 = BitVec.ofNat 32 (((tl13.len) - kk22) - kk31) := by
      rw [rb36, runBlock_reg _ _ _ a0 s35.zero (by decide), g35_10]
    have g36_18 : reg n36 (18 : Fin 32) = out := by
      rw [rb36, runBlock_reg _ _ _ (18 : Fin 32) s35.zero (by decide), g35_18]
    have g36_19 : reg n36 (19 : Fin 32) = bp := by
      rw [rb36, runBlock_reg _ _ _ (19 : Fin 32) s35.zero (by decide), g35_19]
    have g36_21 : reg n36 (21 : Fin 32) = lp := by
      rw [rb36, runBlock_reg _ _ _ (21 : Fin 32) s35.zero (by decide), g35_21]
    have g36_22 : reg n36 (22 : Fin 32) = orp := by
      rw [rb36, runBlock_reg _ _ _ (22 : Fin 32) s35.zero (by decide), g35_22]
    have g36_23 : reg n36 (23 : Fin 32) = tcl := by
      rw [rb36, runBlock_reg _ _ _ (23 : Fin 32) s35.zero (by decide), g35_23]
    have g36_24 : reg n36 (24 : Fin 32) = sgl := by
      rw [rb36, runBlock_reg _ _ _ (24 : Fin 32) s35.zero (by decide), g35_24]
    have g36_25 : reg n36 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by
      rw [rb36, runBlock_reg _ _ _ (25 : Fin 32) s35.zero (by decide), g35_25]
    have g36_26 : reg n36 (26 : Fin 32) = ll := by
      rw [rb36, runBlock_reg _ _ _ (26 : Fin 32) s35.zero (by decide), g35_26]
    have g36_27 : reg n36 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
      rw [rb36, runBlock_reg _ _ _ (27 : Fin 32) s35.zero (by decide), g35_27]
    have g36_20 : reg n36 (20 : Fin 32) = BitVec.ofNat 32 0x1 := by
      rw [rb36]; simp +decide only [runBlock, BInstr.run, svL41c0, upd, ↓reduceIte, aluEval]
      all_goals (try simp only [g35_2, g35_3, g35_4, g35_8, g35_9, g35_10, g35_18, g35_19, g35_20, g35_21, g35_22, g35_23, g35_24, g35_25, g35_26, g35_27, s35.zero])
      all_goals first | with_reducible rfl | sv_addr | decide
    have w36_54 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m36]; exact w35_54
    have w36_58 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m36]; exact w35_58
    have w36_5c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m36]; exact w35_5c
    have w36_60 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m36]; exact w35_60
    have w36_64 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m36]; exact w35_64
    have w36_68 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m36]; exact w35_68
    have w36_6c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m36]; exact w35_6c
    have w36_70 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m36]; exact w35_70
    have w36_74 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m36]; exact w35_74
    have w36_78 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m36]; exact w35_78
    have w36_7c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m36]; exact w35_7c
    have w36_80 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m36]; exact w35_80
    have w36_84 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m36]; exact w35_84
    have w36_180 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m36]; exact w35_180
    have w36_184 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m36]; exact w35_184
    have w36_240 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m36]; exact w35_240
    have w36_248 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = ((((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22) + BitVec.ofNat 32 kk31 := by rw [m36]; exact w35_248
    have w36_24c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 (((tl13.len) - kk22) - kk31) := by rw [m36]; exact w35_24c
    have w36_a28 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm31 % 2 ^ 32) := by rw [m36]; exact w35_a28
    have w36_a2c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm31 / 2 ^ 32) := by rw [m36]; exact w35_a2c
    have b36_244 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m36]; exact b35_244
    have b36_245 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m36]; exact b35_245
    have b36_246 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m36]; exact b35_246
    have b36_247 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m36]; exact b35_247
    have b36_a20 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m36]; exact b35_a20
    have b36_a30 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m36]; exact b35_a30
    clear b35_a30 b35_a20 b35_247 b35_246 b35_245 b35_244 w35_a2c w35_a28 w35_24c w35_248 w35_240 w35_184 w35_180 w35_84 w35_80 w35_7c w35_78 w35_74 w35_70 w35_6c w35_68 w35_64 w35_60 w35_5c w35_58 w35_54 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_10 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 m35 s35 u35 d35
    -- 0x1C2: j
    obtain ⟨n37, d37, u37⟩ := s36.jump E36.self sv_at_1c2 (off' := 0x966) (by decide)
      (by rw [s36.pc]; decide)
    have s37 : St n37.mem SV n37 0x966 (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
    have m37 : n37.mem = n36.mem := u37.mem
    have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
    have t37 : Steps n0 n37 := t36.trans (.single d37)
    have fR37 : ∀ x, SvR B x → n37.mem x = n0.mem x := fun x hx => (fr37 x hx).trans (fR36 x hx)
    have E37 : SvCode n37.mem := E36.fr F fr37
    have V37 : SvSaves B n37.mem v := V36.same m37
    have g37_2 : reg n37 sp = B + 0x21A0 := by rw [u37.regs, g36_2]
    have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u37.regs, g36_3]
    have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u37.regs, g36_4]
    have g37_8 : reg n37 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u37.regs, g36_8]
    have g37_9 : reg n37 (9 : Fin 32) = trp := by rw [u37.regs, g36_9]
    have g37_10 : reg n37 a0 = BitVec.ofNat 32 (((tl13.len) - kk22) - kk31) := by rw [u37.regs, g36_10]
    have g37_18 : reg n37 (18 : Fin 32) = out := by rw [u37.regs, g36_18]
    have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [u37.regs, g36_19]
    have g37_20 : reg n37 (20 : Fin 32) = BitVec.ofNat 32 0x1 := by rw [u37.regs, g36_20]
    have g37_21 : reg n37 (21 : Fin 32) = lp := by rw [u37.regs, g36_21]
    have g37_22 : reg n37 (22 : Fin 32) = orp := by rw [u37.regs, g36_22]
    have g37_23 : reg n37 (23 : Fin 32) = tcl := by rw [u37.regs, g36_23]
    have g37_24 : reg n37 (24 : Fin 32) = sgl := by rw [u37.regs, g36_24]
    have g37_25 : reg n37 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u37.regs, g36_25]
    have g37_26 : reg n37 (26 : Fin 32) = ll := by rw [u37.regs, g36_26]
    have g37_27 : reg n37 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u37.regs, g36_27]
    have w37_54 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m37]; exact w36_54
    have w37_58 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m37]; exact w36_58
    have w37_5c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m37]; exact w36_5c
    have w37_60 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m37]; exact w36_60
    have w37_64 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m37]; exact w36_64
    have w37_68 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m37]; exact w36_68
    have w37_6c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m37]; exact w36_6c
    have w37_70 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m37]; exact w36_70
    have w37_74 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m37]; exact w36_74
    have w37_78 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m37]; exact w36_78
    have w37_7c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m37]; exact w36_7c
    have w37_80 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m37]; exact w36_80
    have w37_84 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m37]; exact w36_84
    have w37_180 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m37]; exact w36_180
    have w37_184 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m37]; exact w36_184
    have w37_240 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m37]; exact w36_240
    have w37_248 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = ((((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22) + BitVec.ofNat 32 kk31 := by rw [m37]; exact w36_248
    have w37_24c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 (((tl13.len) - kk22) - kk31) := by rw [m37]; exact w36_24c
    have w37_a28 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm31 % 2 ^ 32) := by rw [m37]; exact w36_a28
    have w37_a2c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm31 / 2 ^ 32) := by rw [m37]; exact w36_a2c
    have b37_244 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m37]; exact b36_244
    have b37_245 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m37]; exact b36_245
    have b37_246 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m37]; exact b36_246
    have b37_247 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m37]; exact b36_247
    have b37_a20 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m37]; exact b36_a20
    have b37_a30 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m37]; exact b36_a30
    clear b36_a30 b36_a20 b36_247 b36_246 b36_245 b36_244 w36_a2c w36_a28 w36_24c w36_248 w36_240 w36_184 w36_180 w36_84 w36_80 w36_7c w36_78 w36_74 w36_70 w36_6c w36_68 w36_64 w36_60 w36_5c w36_58 w36_54 g36_20 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_19 g36_18 g36_10 g36_9 g36_8 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 rb36 s36 m36 u36 c36
    exact .inl ⟨(fun ⟨tl6', h0', tl13', h1', tm22', rs22', h2', tm31', rs31', h3', h4', _⟩ => by rw [hr6] at h0'; cases h0'; rw [hr13] at h1'; cases h1'; rw [hr22] at h2'; cases h2'; rw [hr31] at h3'; cases h3'; exact hz_34 h4'), sv_fail F E37 s37 t37 fR37 V37 hret g37_2 g37_18 hO g37_3 g37_4⟩
  -- 0x314: branch, not taken
  obtain ⟨n35, d35, u35⟩ := s34.notTaken E34.self 0x318 sv_at_314
    (by decide) (by rw [g34_10, s34.zero]; exact br_bne_f (rest_eq hrb31 hz_34))
  have s35 : St n35.mem SV n35 0x318 (reg n35) := ⟨u35.pc, rfl, fun _ => rfl⟩
  have m35 : n35.mem = n34.mem := u35.mem
  have fr35 : ∀ x, SvR B x → n35.mem x = n34.mem x := fun x _ => by rw [m35]
  have t35 : Steps n0 n35 := t34.trans (.single d35)
  have fR35 : ∀ x, SvR B x → n35.mem x = n0.mem x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.same m35
  have g35_2 : reg n35 sp = B + 0x21A0 := by rw [u35.regs, g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u35.regs, g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u35.regs, g34_4]
  have g35_8 : reg n35 (8 : Fin 32) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [u35.regs, g34_8]
  have g35_9 : reg n35 (9 : Fin 32) = trp := by rw [u35.regs, g34_9]
  have g35_10 : reg n35 a0 = BitVec.ofNat 32 (((tl13.len) - kk22) - kk31) := by rw [u35.regs, g34_10]
  have g35_18 : reg n35 (18 : Fin 32) = out := by rw [u35.regs, g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [u35.regs, g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [u35.regs, g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = lp := by rw [u35.regs, g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = orp := by rw [u35.regs, g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = tcl := by rw [u35.regs, g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = sgl := by rw [u35.regs, g34_24]
  have g35_25 : reg n35 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u35.regs, g34_25]
  have g35_26 : reg n35 (26 : Fin 32) = ll := by rw [u35.regs, g34_26]
  have g35_27 : reg n35 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u35.regs, g34_27]
  have w35_54 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m35]; exact w34_54
  have w35_58 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m35]; exact w34_58
  have w35_5c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m35]; exact w34_5c
  have w35_60 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m35]; exact w34_60
  have w35_64 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m35]; exact w34_64
  have w35_68 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m35]; exact w34_68
  have w35_6c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m35]; exact w34_6c
  have w35_70 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m35]; exact w34_70
  have w35_74 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m35]; exact w34_74
  have w35_78 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m35]; exact w34_78
  have w35_7c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m35]; exact w34_7c
  have w35_80 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m35]; exact w34_80
  have w35_84 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m35]; exact w34_84
  have w35_180 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m35]; exact w34_180
  have w35_184 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m35]; exact w34_184
  have w35_240 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m35]; exact w34_240
  have w35_248 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = ((((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22) + BitVec.ofNat 32 kk31 := by rw [m35]; exact w34_248
  have w35_24c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 (((tl13.len) - kk22) - kk31) := by rw [m35]; exact w34_24c
  have w35_a28 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm31 % 2 ^ 32) := by rw [m35]; exact w34_a28
  have w35_a2c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm31 / 2 ^ 32) := by rw [m35]; exact w34_a2c
  have b35_244 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m35]; exact b34_244
  have b35_245 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m35]; exact b34_245
  have b35_246 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m35]; exact b34_246
  have b35_247 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m35]; exact b34_247
  have b35_a20 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m35]; exact b34_a20
  have b35_a30 : n35.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m35]; exact b34_a30
  clear b34_a30 b34_a20 b34_247 b34_246 b34_245 b34_244 w34_a2c w34_a28 w34_24c w34_248 w34_240 w34_184 w34_180 w34_84 w34_80 w34_7c w34_78 w34_74 w34_70 w34_6c w34_68 w34_64 w34_60 w34_5c w34_58 w34_54 g34_10 g34_27 g34_26 g34_25 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_9 g34_8 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 m34 s34 u34 d34
  -- 0x318
  obtain ⟨n36, c36, u36⟩ := s35.block svL4318 E35.self svL4318_end
    ⟨trivial, trivial⟩
  have m36 : n36.mem = n35.mem := u36.mem
  have s36 : St n36.mem SV n36 0x31A (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
  have rb36 : ∀ q, reg n36 q = (runBlock svL4318 (n35.mem, reg n35)).2 q := fun q => by rw [u36.regs]
  have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
  have t36 : Steps n0 n36 := t35.trans c36
  have fR36 : ∀ x, SvR B x → n36.mem x = n0.mem x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.same m36
  have g36_2 : reg n36 sp = B + 0x21A0 := by
    rw [rb36, runBlock_reg _ _ _ sp s35.zero (by decide), g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb36, runBlock_reg _ _ _ (3 : Fin 32) s35.zero (by decide), g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb36, runBlock_reg _ _ _ (4 : Fin 32) s35.zero (by decide), g35_4]
  have g36_9 : reg n36 (9 : Fin 32) = trp := by
    rw [rb36, runBlock_reg _ _ _ (9 : Fin 32) s35.zero (by decide), g35_9]
  have g36_10 : reg n36 a0 = BitVec.ofNat 32 (((tl13.len) - kk22) - kk31) := by
    rw [rb36, runBlock_reg _ _ _ a0 s35.zero (by decide), g35_10]
  have g36_18 : reg n36 (18 : Fin 32) = out := by
    rw [rb36, runBlock_reg _ _ _ (18 : Fin 32) s35.zero (by decide), g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by
    rw [rb36, runBlock_reg _ _ _ (19 : Fin 32) s35.zero (by decide), g35_19]
  have g36_20 : reg n36 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by
    rw [rb36, runBlock_reg _ _ _ (20 : Fin 32) s35.zero (by decide), g35_20]
  have g36_21 : reg n36 (21 : Fin 32) = lp := by
    rw [rb36, runBlock_reg _ _ _ (21 : Fin 32) s35.zero (by decide), g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = orp := by
    rw [rb36, runBlock_reg _ _ _ (22 : Fin 32) s35.zero (by decide), g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = tcl := by
    rw [rb36, runBlock_reg _ _ _ (23 : Fin 32) s35.zero (by decide), g35_23]
  have g36_24 : reg n36 (24 : Fin 32) = sgl := by
    rw [rb36, runBlock_reg _ _ _ (24 : Fin 32) s35.zero (by decide), g35_24]
  have g36_25 : reg n36 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by
    rw [rb36, runBlock_reg _ _ _ (25 : Fin 32) s35.zero (by decide), g35_25]
  have g36_26 : reg n36 (26 : Fin 32) = ll := by
    rw [rb36, runBlock_reg _ _ _ (26 : Fin 32) s35.zero (by decide), g35_26]
  have g36_27 : reg n36 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb36, runBlock_reg _ _ _ (27 : Fin 32) s35.zero (by decide), g35_27]
  have g36_8 : reg n36 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [rb36]; simp +decide only [runBlock, BInstr.run, svL4318, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g35_2, g35_3, g35_4, g35_8, g35_9, g35_10, g35_18, g35_19, g35_20, g35_21, g35_22, g35_23, g35_24, g35_25, g35_26, g35_27, s35.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have w36_54 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m36]; exact w35_54
  have w36_58 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m36]; exact w35_58
  have w36_5c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m36]; exact w35_5c
  have w36_60 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m36]; exact w35_60
  have w36_64 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m36]; exact w35_64
  have w36_68 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m36]; exact w35_68
  have w36_6c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m36]; exact w35_6c
  have w36_70 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m36]; exact w35_70
  have w36_74 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m36]; exact w35_74
  have w36_78 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m36]; exact w35_78
  have w36_7c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m36]; exact w35_7c
  have w36_80 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m36]; exact w35_80
  have w36_84 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m36]; exact w35_84
  have w36_180 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m36]; exact w35_180
  have w36_184 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m36]; exact w35_184
  have w36_240 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m36]; exact w35_240
  have w36_248 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = ((((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22) + BitVec.ofNat 32 kk31 := by rw [m36]; exact w35_248
  have w36_24c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 (((tl13.len) - kk22) - kk31) := by rw [m36]; exact w35_24c
  have w36_a28 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm31 % 2 ^ 32) := by rw [m36]; exact w35_a28
  have w36_a2c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm31 / 2 ^ 32) := by rw [m36]; exact w35_a2c
  have b36_244 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m36]; exact b35_244
  have b36_245 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m36]; exact b35_245
  have b36_246 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m36]; exact b35_246
  have b36_247 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m36]; exact b35_247
  have b36_a20 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m36]; exact b35_a20
  have b36_a30 : n36.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m36]; exact b35_a30
  clear b35_a30 b35_a20 b35_247 b35_246 b35_245 b35_244 w35_a2c w35_a28 w35_24c w35_248 w35_240 w35_184 w35_180 w35_84 w35_80 w35_7c w35_78 w35_74 w35_70 w35_6c w35_68 w35_64 w35_60 w35_5c w35_58 w35_54 g35_27 g35_26 g35_25 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_10 g35_9 g35_8 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 m35 s35 u35 d35
  -- 0x31A: lw
  obtain ⟨n37, d37, u37⟩ := s36.lw E36.self sv_at_31a (off' := 0x31C) (by decide)
    (by rw [g36_8, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s37 : St n37.mem SV n37 0x31C (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
  have m37 : n37.mem = n36.mem := u37.mem
  have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
  have t37 : Steps n0 n37 := t36.trans (.single d37)
  have fR37 : ∀ x, SvR B x → n37.mem x = n0.mem x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : SvCode n37.mem := E36.fr F fr37
  have V37 : SvSaves B n37.mem v := V36.same m37
  have g37_2 : reg n37 sp = B + 0x21A0 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u37.regs, upd_ne (by decide) (by decide), g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u37.regs, upd_ne (by decide) (by decide), g36_4]
  have g37_8 : reg n37 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_8]
  have g37_9 : reg n37 (9 : Fin 32) = trp := by rw [u37.regs, upd_ne (by decide) (by decide), g36_9]
  have g37_18 : reg n37 (18 : Fin 32) = out := by rw [u37.regs, upd_ne (by decide) (by decide), g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = bp := by rw [u37.regs, upd_ne (by decide) (by decide), g36_19]
  have g37_20 : reg n37 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_20]
  have g37_21 : reg n37 (21 : Fin 32) = lp := by rw [u37.regs, upd_ne (by decide) (by decide), g36_21]
  have g37_22 : reg n37 (22 : Fin 32) = orp := by rw [u37.regs, upd_ne (by decide) (by decide), g36_22]
  have g37_23 : reg n37 (23 : Fin 32) = tcl := by rw [u37.regs, upd_ne (by decide) (by decide), g36_23]
  have g37_24 : reg n37 (24 : Fin 32) = sgl := by rw [u37.regs, upd_ne (by decide) (by decide), g36_24]
  have g37_25 : reg n37 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u37.regs, upd_ne (by decide) (by decide), g36_25]
  have g37_26 : reg n37 (26 : Fin 32) = ll := by rw [u37.regs, upd_ne (by decide) (by decide), g36_26]
  have g37_27 : reg n37 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u37.regs, upd_ne (by decide) (by decide), g36_27]
  have g37_10 : reg n37 a0 = BitVec.ofNat 32 (tm31 % 2 ^ 32) := by
    rw [u37.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g36_8, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0x8 = B + 0x21A0 + BitVec.ofNat 32 0xA28 by sv_addr, w36_a28]
  have w37_54 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m37]; exact w36_54
  have w37_58 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m37]; exact w36_58
  have w37_5c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m37]; exact w36_5c
  have w37_60 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m37]; exact w36_60
  have w37_64 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m37]; exact w36_64
  have w37_68 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m37]; exact w36_68
  have w37_6c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m37]; exact w36_6c
  have w37_70 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m37]; exact w36_70
  have w37_74 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m37]; exact w36_74
  have w37_78 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m37]; exact w36_78
  have w37_7c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m37]; exact w36_7c
  have w37_80 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m37]; exact w36_80
  have w37_84 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m37]; exact w36_84
  have w37_180 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m37]; exact w36_180
  have w37_184 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m37]; exact w36_184
  have w37_240 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m37]; exact w36_240
  have w37_248 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = ((((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22) + BitVec.ofNat 32 kk31 := by rw [m37]; exact w36_248
  have w37_24c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 (((tl13.len) - kk22) - kk31) := by rw [m37]; exact w36_24c
  have w37_a28 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm31 % 2 ^ 32) := by rw [m37]; exact w36_a28
  have w37_a2c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm31 / 2 ^ 32) := by rw [m37]; exact w36_a2c
  have b37_244 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m37]; exact b36_244
  have b37_245 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m37]; exact b36_245
  have b37_246 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m37]; exact b36_246
  have b37_247 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m37]; exact b36_247
  have b37_a20 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m37]; exact b36_a20
  have b37_a30 : n37.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m37]; exact b36_a30
  clear b36_a30 b36_a20 b36_247 b36_246 b36_245 b36_244 w36_a2c w36_a28 w36_24c w36_248 w36_240 w36_184 w36_180 w36_84 w36_80 w36_7c w36_78 w36_74 w36_70 w36_6c w36_68 w36_64 w36_60 w36_5c w36_58 w36_54 g36_8 g36_27 g36_26 g36_25 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_10 g36_9 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 rb36 s36 m36 u36 c36
  -- 0x31C: sw
  obtain ⟨n38, d38, s38, fr38, K38, W38, rg38⟩ := sv_sw F E37 s37 sv_at_31c (off' := 0x31E) (c := 0x50)
    (by decide) (by rw [g37_2]; sv_addr) (by decide) (by decide)
  have t38 : Steps n0 n38 := t37.trans d38
  have fR38 : ∀ x, SvR B x → n38.mem x = n0.mem x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : SvCode n38.mem := E37.fr F fr38
  have V38 : SvSaves B n38.mem v := V37.keep K38 (by decide)
  have g38_2 : reg n38 sp = B + 0x21A0 := by rw [rg38 sp, g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg38 (3 : Fin 32), g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg38 (4 : Fin 32), g37_4]
  have g38_8 : reg n38 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg38 (8 : Fin 32), g37_8]
  have g38_9 : reg n38 (9 : Fin 32) = trp := by rw [rg38 (9 : Fin 32), g37_9]
  have g38_10 : reg n38 a0 = BitVec.ofNat 32 (tm31 % 2 ^ 32) := by rw [rg38 a0, g37_10]
  have g38_18 : reg n38 (18 : Fin 32) = out := by rw [rg38 (18 : Fin 32), g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [rg38 (19 : Fin 32), g37_19]
  have g38_20 : reg n38 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg38 (20 : Fin 32), g37_20]
  have g38_21 : reg n38 (21 : Fin 32) = lp := by rw [rg38 (21 : Fin 32), g37_21]
  have g38_22 : reg n38 (22 : Fin 32) = orp := by rw [rg38 (22 : Fin 32), g37_22]
  have g38_23 : reg n38 (23 : Fin 32) = tcl := by rw [rg38 (23 : Fin 32), g37_23]
  have g38_24 : reg n38 (24 : Fin 32) = sgl := by rw [rg38 (24 : Fin 32), g37_24]
  have g38_25 : reg n38 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [rg38 (25 : Fin 32), g37_25]
  have g38_26 : reg n38 (26 : Fin 32) = ll := by rw [rg38 (26 : Fin 32), g37_26]
  have g38_27 : reg n38 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg38 (27 : Fin 32), g37_27]
  have w38_54 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := (K38.w32 (by decide) (by decide)).trans w37_54
  have w38_58 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := (K38.w32 (by decide) (by decide)).trans w37_58
  have w38_5c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := (K38.w32 (by decide) (by decide)).trans w37_5c
  have w38_60 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K38.w32 (by decide) (by decide)).trans w37_60
  have w38_64 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := (K38.w32 (by decide) (by decide)).trans w37_64
  have w38_68 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K38.w32 (by decide) (by decide)).trans w37_68
  have w38_6c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K38.w32 (by decide) (by decide)).trans w37_6c
  have w38_70 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K38.w32 (by decide) (by decide)).trans w37_70
  have w38_74 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K38.w32 (by decide) (by decide)).trans w37_74
  have w38_78 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K38.w32 (by decide) (by decide)).trans w37_78
  have w38_7c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K38.w32 (by decide) (by decide)).trans w37_7c
  have w38_80 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K38.w32 (by decide) (by decide)).trans w37_80
  have w38_84 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K38.w32 (by decide) (by decide)).trans w37_84
  have w38_180 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K38.w32 (by decide) (by decide)).trans w37_180
  have w38_184 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K38.w32 (by decide) (by decide)).trans w37_184
  have w38_240 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := (K38.w32 (by decide) (by decide)).trans w37_240
  have w38_248 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = ((((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22) + BitVec.ofNat 32 kk31 := (K38.w32 (by decide) (by decide)).trans w37_248
  have w38_24c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 (((tl13.len) - kk22) - kk31) := (K38.w32 (by decide) (by decide)).trans w37_24c
  have w38_a28 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm31 % 2 ^ 32) := (K38.w32 (by decide) (by decide)).trans w37_a28
  have w38_a2c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm31 / 2 ^ 32) := (K38.w32 (by decide) (by decide)).trans w37_a2c
  have b38_244 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := (K38.b8 (by decide) (by decide)).trans b37_244
  have b38_245 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K38.b8 (by decide) (by decide)).trans b37_245
  have b38_246 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K38.b8 (by decide) (by decide)).trans b37_246
  have b38_247 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K38.b8 (by decide) (by decide)).trans b37_247
  have b38_a20 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := (K38.b8 (by decide) (by decide)).trans b37_a20
  have b38_a30 : n38.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := (K38.b8 (by decide) (by decide)).trans b37_a30
  have w38_50 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 (tm31 % 2 ^ 32) := by rw [W38, g37_10]
  clear b37_a30 b37_a20 b37_247 b37_246 b37_245 b37_244 w37_a2c w37_a28 w37_24c w37_248 w37_240 w37_184 w37_180 w37_84 w37_80 w37_7c w37_78 w37_74 w37_70 w37_6c w37_68 w37_64 w37_60 w37_5c w37_58 w37_54 g37_10 g37_27 g37_26 g37_25 g37_24 g37_23 g37_22 g37_21 g37_20 g37_19 g37_18 g37_9 g37_8 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 m37 s37 u37 d37
  -- 0x31E: lw
  obtain ⟨n39, d39, u39⟩ := s38.lw E38.self sv_at_31e (off' := 0x320) (by decide)
    (by rw [g38_8, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0xC = B + 0x21A0 + BitVec.ofNat 32 0xA2C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s39 : St n39.mem SV n39 0x320 (reg n39) := ⟨u39.pc, rfl, fun _ => rfl⟩
  have m39 : n39.mem = n38.mem := u39.mem
  have fr39 : ∀ x, SvR B x → n39.mem x = n38.mem x := fun x _ => by rw [m39]
  have t39 : Steps n0 n39 := t38.trans (.single d39)
  have fR39 : ∀ x, SvR B x → n39.mem x = n0.mem x := fun x hx => (fr39 x hx).trans (fR38 x hx)
  have E39 : SvCode n39.mem := E38.fr F fr39
  have V39 : SvSaves B n39.mem v := V38.same m39
  have g39_2 : reg n39 sp = B + 0x21A0 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_2]
  have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u39.regs, upd_ne (by decide) (by decide), g38_3]
  have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u39.regs, upd_ne (by decide) (by decide), g38_4]
  have g39_8 : reg n39 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_8]
  have g39_9 : reg n39 (9 : Fin 32) = trp := by rw [u39.regs, upd_ne (by decide) (by decide), g38_9]
  have g39_18 : reg n39 (18 : Fin 32) = out := by rw [u39.regs, upd_ne (by decide) (by decide), g38_18]
  have g39_19 : reg n39 (19 : Fin 32) = bp := by rw [u39.regs, upd_ne (by decide) (by decide), g38_19]
  have g39_20 : reg n39 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_20]
  have g39_21 : reg n39 (21 : Fin 32) = lp := by rw [u39.regs, upd_ne (by decide) (by decide), g38_21]
  have g39_22 : reg n39 (22 : Fin 32) = orp := by rw [u39.regs, upd_ne (by decide) (by decide), g38_22]
  have g39_23 : reg n39 (23 : Fin 32) = tcl := by rw [u39.regs, upd_ne (by decide) (by decide), g38_23]
  have g39_24 : reg n39 (24 : Fin 32) = sgl := by rw [u39.regs, upd_ne (by decide) (by decide), g38_24]
  have g39_25 : reg n39 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [u39.regs, upd_ne (by decide) (by decide), g38_25]
  have g39_26 : reg n39 (26 : Fin 32) = ll := by rw [u39.regs, upd_ne (by decide) (by decide), g38_26]
  have g39_27 : reg n39 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_27]
  have g39_10 : reg n39 a0 = BitVec.ofNat 32 (tm31 / 2 ^ 32) := by
    rw [u39.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g38_8, show B + 0x21A0 + BitVec.ofNat 32 0xA20 + 0xC = B + 0x21A0 + BitVec.ofNat 32 0xA2C by sv_addr, w38_a2c]
  have w39_50 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 (tm31 % 2 ^ 32) := by rw [m39]; exact w38_50
  have w39_54 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := by rw [m39]; exact w38_54
  have w39_58 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := by rw [m39]; exact w38_58
  have w39_5c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := by rw [m39]; exact w38_5c
  have w39_60 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := by rw [m39]; exact w38_60
  have w39_64 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := by rw [m39]; exact w38_64
  have w39_68 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m39]; exact w38_68
  have w39_6c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := by rw [m39]; exact w38_6c
  have w39_70 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := by rw [m39]; exact w38_70
  have w39_74 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := by rw [m39]; exact w38_74
  have w39_78 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := by rw [m39]; exact w38_78
  have w39_7c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := by rw [m39]; exact w38_7c
  have w39_80 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := by rw [m39]; exact w38_80
  have w39_84 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := by rw [m39]; exact w38_84
  have w39_180 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m39]; exact w38_180
  have w39_184 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := by rw [m39]; exact w38_184
  have w39_240 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := by rw [m39]; exact w38_240
  have w39_248 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = ((((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22) + BitVec.ofNat 32 kk31 := by rw [m39]; exact w38_248
  have w39_24c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 (((tl13.len) - kk22) - kk31) := by rw [m39]; exact w38_24c
  have w39_a28 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm31 % 2 ^ 32) := by rw [m39]; exact w38_a28
  have w39_a2c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm31 / 2 ^ 32) := by rw [m39]; exact w38_a2c
  have b39_244 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := by rw [m39]; exact b38_244
  have b39_245 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := by rw [m39]; exact b38_245
  have b39_246 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := by rw [m39]; exact b38_246
  have b39_247 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := by rw [m39]; exact b38_247
  have b39_a20 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := by rw [m39]; exact b38_a20
  have b39_a30 : n39.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := by rw [m39]; exact b38_a30
  clear w38_50 b38_a30 b38_a20 b38_247 b38_246 b38_245 b38_244 w38_a2c w38_a28 w38_24c w38_248 w38_240 w38_184 w38_180 w38_84 w38_80 w38_7c w38_78 w38_74 w38_70 w38_6c w38_68 w38_64 w38_60 w38_5c w38_58 w38_54 g38_27 g38_26 g38_25 g38_24 g38_23 g38_22 g38_21 g38_20 g38_19 g38_18 g38_10 g38_9 g38_8 g38_4 g38_3 g38_2 V38 E38 fR38 t38 rg38 W38 K38 fr38 s38 d38
  -- 0x320: sw
  obtain ⟨n40, d40, s40, fr40, K40, W40, rg40⟩ := sv_sw F E39 s39 sv_at_320 (off' := 0x322) (c := 0x4C)
    (by decide) (by rw [g39_2]; sv_addr) (by decide) (by decide)
  have t40 : Steps n0 n40 := t39.trans d40
  have fR40 : ∀ x, SvR B x → n40.mem x = n0.mem x := fun x hx => (fr40 x hx).trans (fR39 x hx)
  have E40 : SvCode n40.mem := E39.fr F fr40
  have V40 : SvSaves B n40.mem v := V39.keep K40 (by decide)
  have g40_2 : reg n40 sp = B + 0x21A0 := by rw [rg40 sp, g39_2]
  have g40_3 : reg n40 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg40 (3 : Fin 32), g39_3]
  have g40_4 : reg n40 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg40 (4 : Fin 32), g39_4]
  have g40_8 : reg n40 (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg40 (8 : Fin 32), g39_8]
  have g40_9 : reg n40 (9 : Fin 32) = trp := by rw [rg40 (9 : Fin 32), g39_9]
  have g40_10 : reg n40 a0 = BitVec.ofNat 32 (tm31 / 2 ^ 32) := by rw [rg40 a0, g39_10]
  have g40_18 : reg n40 (18 : Fin 32) = out := by rw [rg40 (18 : Fin 32), g39_18]
  have g40_19 : reg n40 (19 : Fin 32) = bp := by rw [rg40 (19 : Fin 32), g39_19]
  have g40_20 : reg n40 (20 : Fin 32) = ((BitVec.ofNat 32 tl13.len).extractLsb' 0 8).zeroExtend 32 := by rw [rg40 (20 : Fin 32), g39_20]
  have g40_21 : reg n40 (21 : Fin 32) = lp := by rw [rg40 (21 : Fin 32), g39_21]
  have g40_22 : reg n40 (22 : Fin 32) = orp := by rw [rg40 (22 : Fin 32), g39_22]
  have g40_23 : reg n40 (23 : Fin 32) = tcl := by rw [rg40 (23 : Fin 32), g39_23]
  have g40_24 : reg n40 (24 : Fin 32) = sgl := by rw [rg40 (24 : Fin 32), g39_24]
  have g40_25 : reg n40 (25 : Fin 32) = BitVec.ofNat 32 (tl6.header + tl6.len) := by rw [rg40 (25 : Fin 32), g39_25]
  have g40_26 : reg n40 (26 : Fin 32) = ll := by rw [rg40 (26 : Fin 32), g39_26]
  have g40_27 : reg n40 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by rw [rg40 (27 : Fin 32), g39_27]
  have w40_50 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 (tm31 % 2 ^ 32) := (K40.w32 (by decide) (by decide)).trans w39_50
  have w40_54 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22 / 2 ^ 32) := (K40.w32 (by decide) (by decide)).trans w39_54
  have w40_58 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22 % 2 ^ 32) := (K40.w32 (by decide) (by decide)).trans w39_58
  have w40_5c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = rp := (K40.w32 (by decide) (by decide)).trans w39_5c
  have w40_60 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = orp := (K40.w32 (by decide) (by decide)).trans w39_60
  have w40_64 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = orl := (K40.w32 (by decide) (by decide)).trans w39_64
  have w40_68 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K40.w32 (by decide) (by decide)).trans w39_68
  have w40_6c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp := (K40.w32 (by decide) (by decide)).trans w39_6c
  have w40_70 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = arp := (K40.w32 (by decide) (by decide)).trans w39_70
  have w40_74 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = arl := (K40.w32 (by decide) (by decide)).trans w39_74
  have w40_78 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = trl := (K40.w32 (by decide) (by decide)).trans w39_78
  have w40_7c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = sgp := (K40.w32 (by decide) (by decide)).trans w39_7c
  have w40_80 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp := (K40.w32 (by decide) (by decide)).trans w39_80
  have w40_84 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg := (K40.w32 (by decide) (by decide)).trans w39_84
  have w40_180 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 (tl13.header + tl13.len) := (K40.w32 (by decide) (by decide)).trans w39_180
  have w40_184 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = ((rl) - BitVec.ofNat 32 (tl6.header + tl6.len)) - BitVec.ofNat 32 (tl13.header + tl13.len) := (K40.w32 (by decide) (by decide)).trans w39_184
  have w40_240 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x240) = ((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header := (K40.w32 (by decide) (by decide)).trans w39_240
  have w40_248 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x248) = ((((rp) + BitVec.ofNat 32 (tl6.header + tl6.len)) + BitVec.ofNat 32 tl13.header) + BitVec.ofNat 32 kk22) + BitVec.ofNat 32 kk31 := (K40.w32 (by decide) (by decide)).trans w39_248
  have w40_24c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x24C) = BitVec.ofNat 32 (((tl13.len) - kk22) - kk31) := (K40.w32 (by decide) (by decide)).trans w39_24c
  have w40_a28 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 (tm31 % 2 ^ 32) := (K40.w32 (by decide) (by decide)).trans w39_a28
  have w40_a2c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tm31 / 2 ^ 32) := (K40.w32 (by decide) (by decide)).trans w39_a2c
  have b40_244 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x244) = (BitVec.ofNat 32 tl13.len).extractLsb' 0 8 := (K40.b8 (by decide) (by decide)).trans b39_244
  have b40_245 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x245) = (BitVec.ofNat 32 tl13.len).extractLsb' 8 8 := (K40.b8 (by decide) (by decide)).trans b39_245
  have b40_246 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x246) = (BitVec.ofNat 32 tl13.len).extractLsb' 16 8 := (K40.b8 (by decide) (by decide)).trans b39_246
  have b40_247 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x247) = (BitVec.ofNat 32 tl13.len).extractLsb' 24 8 := (K40.b8 (by decide) (by decide)).trans b39_247
  have b40_a20 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) := (K40.b8 (by decide) (by decide)).trans b39_a20
  have b40_a30 : n40.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 8 tl6.tag := (K40.b8 (by decide) (by decide)).trans b39_a30
  have w40_4c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = BitVec.ofNat 32 (tm31 / 2 ^ 32) := by rw [W40, g39_10]
  clear b39_a30 b39_a20 b39_247 b39_246 b39_245 b39_244 w39_a2c w39_a28 w39_24c w39_248 w39_240 w39_184 w39_180 w39_84 w39_80 w39_7c w39_78 w39_74 w39_70 w39_6c w39_68 w39_64 w39_60 w39_5c w39_58 w39_54 w39_50 g39_10 g39_27 g39_26 g39_25 g39_24 g39_23 g39_22 g39_21 g39_20 g39_19 g39_18 g39_9 g39_8 g39_4 g39_3 g39_2 V39 E39 fR39 t39 fr39 m39 s39 u39 d39
  exact .inr ⟨tl6, hr6, tl13, hr13, tm22, rs22, hr22, tm31, rs31, hr31, hz_34, n40, t40, s40, E40, V40, fR40, g40_2, g40_3, g40_4, g40_8, g40_9, g40_18, g40_19, g40_20, g40_21, g40_22, g40_23, g40_24, g40_25, g40_26, g40_27, w40_4c, w40_50, w40_54, w40_58, w40_5c, w40_60, w40_64, w40_68, w40_6c, w40_70, w40_74, w40_78, w40_7c, w40_80, w40_84, w40_180, w40_184⟩

end C3.RV32.Sv
