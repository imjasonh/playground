import C3BootProofs.Proofs.SvFail

/-!
# `sigstore::verify`: the leaf's signature result, the policy values, and the image's signature

From 0x980 to 0xA4C: `p384_verify_prehash`'s result must be nonzero, the leaf's five policy values must equal the trust root's, and the image's signature must parse as an ECDSA P-256 signature, whose `r` and `s` the stage copies to offsets 0x130 and 0x150.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def svDpv984 : List BInstr :=
  [.alu .add a0 x0 (21 : Fin 32)]
theorem svDpv984_end : blockEnd sigstoreVerifyCode 0x984 svDpv984 = some 0x986 := by
  simp only [svDpv984]
  rw [blockEnd, sv_at_984]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDpv98a : List BInstr :=
  [.alu .add a0 x0 (26 : Fin 32)]
theorem svDpv98a_end : blockEnd sigstoreVerifyCode 0x98A svDpv98a = some 0x98C := by
  simp only [svDpv98a]
  rw [blockEnd, sv_at_98a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDpv99a : List BInstr :=
  [.alu .add a0 x0 (21 : Fin 32)]
theorem svDpv99a_end : blockEnd sigstoreVerifyCode 0x99A svDpv99a = some 0x99C := by
  simp only [svDpv99a]
  rw [blockEnd, sv_at_99a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDpv9b0 : List BInstr :=
  [.alu .add a0 x0 (21 : Fin 32)]
theorem svDpv9b0_end : blockEnd sigstoreVerifyCode 0x9B0 svDpv9b0 = some 0x9B2 := by
  simp only [svDpv9b0]
  rw [blockEnd, sv_at_9b0]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDpv9c6 : List BInstr :=
  [.alu .add a0 x0 (21 : Fin 32)]
theorem svDpv9c6_end : blockEnd sigstoreVerifyCode 0x9C6 svDpv9c6 = some 0x9C8 := by
  simp only [svDpv9c6]
  rw [blockEnd, sv_at_9c6]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDpv9dc : List BInstr :=
  [.alu .add a0 x0 (21 : Fin 32)]
theorem svDpv9dc_end : blockEnd sigstoreVerifyCode 0x9DC svDpv9dc = some 0x9DE := by
  simp only [svDpv9dc]
  rw [blockEnd, sv_at_9dc]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDpv9f2 : List BInstr :=
  [.alu .add a0 x0 (19 : Fin 32)]
theorem svDpv9f2_end : blockEnd sigstoreVerifyCode 0x9F2 svDpv9f2 = some 0x9F4 := by
  simp only [svDpv9f2]
  rw [blockEnd, sv_at_9f2]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDpv9f8 : List BInstr :=
  [.aluImm .add a0 sp 0x170]
theorem svDpv9f8_end : blockEnd sigstoreVerifyCode 0x9F8 svDpv9f8 = some 0x9FA := by
  simp only [svDpv9f8]
  rw [blockEnd, sv_at_9f8]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDpva12 : List BInstr :=
  [.aluImm .add a1 sp 0x172, .aluImm .add a0 sp 0x291, .aluImm .add a2 x0 0x3F]
theorem svDpva12_end : blockEnd sigstoreVerifyCode 0xA12 svDpva12 = some 0xA1E := by
  simp only [svDpva12]
  rw [blockEnd, sv_at_a12]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_a16]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_a1a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDpva2a : List BInstr :=
  [.aluImm .add a0 sp 0x131, .aluImm .add a1 sp 0x291, .aluImm .add a2 x0 0x1F]
theorem svDpva2a_end : blockEnd sigstoreVerifyCode 0xA2A svDpva2a = some 0xA34 := by
  simp only [svDpva2a]
  rw [blockEnd, sv_at_a2a]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_a2e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_a32]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

def svDpva3c : List BInstr :=
  [.aluImm .add a0 sp 0x150, .aluImm .add a2 x0 0x20, .aluImm .add a1 sp 0x2B0]
theorem svDpva3c_end : blockEnd sigstoreVerifyCode 0xA3C svDpva3c = some 0xA44 := by
  simp only [svDpva3c]
  rw [blockEnd, sv_at_a3c]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_a3e]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rw [blockEnd, sv_at_a42]; dsimp only; rw [if_pos (by decide)]; simp only [BitVec.reduceToNat, Nat.reduceAdd]
  rfl

set_option maxHeartbeats 0 in
theorem sv_dpv {B out bp x20 x21 x22 x24 x26 q pv sgp sgl e0p e0l e1p e1l e2p e2l e3p e3l e4p e4l : Word} {w30 w34 w38 w3c w40 w44 w48 w4c w50 : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x980 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_10 : reg n0 a0 = pv)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = q)
    (g0_24 : reg n0 (24 : Fin 32) = x24)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38)
    (w0_3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c)
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
    (he0p : memLoad32 M0 (x21 + 0x0) = e0p)
    (he0l : memLoad32 M0 (x21 + 0x4) = e0l)
    (he0p_in : SvIn B (x21 + 0x0) 4)
    (he0l_in : SvIn B (x21 + 0x4) 4)
    (ae0p : (x21 + 0x0).toNat % 4 = 0)
    (ae0l : (x21 + 0x4).toNat % 4 = 0)
    (p0_in : SvRo B x26 w40.toNat)
    (e0_in : SvRo B e0p e0l.toNat)
    (he1p : memLoad32 M0 (x21 + 0x8) = e1p)
    (he1l : memLoad32 M0 (x21 + 0xC) = e1l)
    (he1p_in : SvIn B (x21 + 0x8) 4)
    (he1l_in : SvIn B (x21 + 0xC) 4)
    (ae1p : (x21 + 0x8).toNat % 4 = 0)
    (ae1l : (x21 + 0xC).toNat % 4 = 0)
    (p1_in : SvRo B w50 w3c.toNat)
    (e1_in : SvRo B e1p e1l.toNat)
    (he2p : memLoad32 M0 (x21 + 0x10) = e2p)
    (he2l : memLoad32 M0 (x21 + 0x14) = e2l)
    (he2p_in : SvIn B (x21 + 0x10) 4)
    (he2l_in : SvIn B (x21 + 0x14) 4)
    (ae2p : (x21 + 0x10).toNat % 4 = 0)
    (ae2l : (x21 + 0x14).toNat % 4 = 0)
    (p2_in : SvRo B w4c w38.toNat)
    (e2_in : SvRo B e2p e2l.toNat)
    (he3p : memLoad32 M0 (x21 + 0x18) = e3p)
    (he3l : memLoad32 M0 (x21 + 0x1C) = e3l)
    (he3p_in : SvIn B (x21 + 0x18) 4)
    (he3l_in : SvIn B (x21 + 0x1C) 4)
    (ae3p : (x21 + 0x18).toNat % 4 = 0)
    (ae3l : (x21 + 0x1C).toNat % 4 = 0)
    (p3_in : SvRo B w48 w34.toNat)
    (e3_in : SvRo B e3p e3l.toNat)
    (he4p : memLoad32 M0 (x21 + 0x20) = e4p)
    (he4l : memLoad32 M0 (x21 + 0x24) = e4l)
    (he4p_in : SvIn B (x21 + 0x20) 4)
    (he4l_in : SvIn B (x21 + 0x24) 4)
    (ae4p : (x21 + 0x20).toNat % 4 = 0)
    (ae4l : (x21 + 0x24).toNat % 4 = 0)
    (p4_in : SvRo B w44 w30.toNat)
    (e4_in : SvRo B e4p e4l.toNat)
    (hsgp : memLoad32 M0 (bp + 0x8) = sgp)
    (hsgl : memLoad32 M0 (bp + 0xC) = sgl)
    (hsgp_in : SvIn B (bp + 0x8) 4)
    (hsgl_in : SvIn B (bp + 0xC) 4)
    (asgp : (bp + 0x8).toNat % 4 = 0)
    (asgl : (bp + 0xC).toNat % 4 = 0)
    (sg_in : SvIn B sgp sgl.toNat) :
    (¬ ((pv ≠ 0) ∧ (memBytes M0 x26 w40.toNat = memBytes M0 e0p e0l.toNat) ∧ (memBytes M0 w50 w3c.toNat = memBytes M0 e1p e1l.toNat) ∧ (memBytes M0 w4c w38.toNat = memBytes M0 e2p e2l.toNat) ∧ (memBytes M0 w48 w34.toNat = memBytes M0 e3p e3l.toNat) ∧ (memBytes M0 w44 w30.toNat = memBytes M0 e4p e4l.toNat) ∧ ∃ sr43 ss43, ecdsaSigOf 32 M0 (sgp) (sgl.toNat) = .ok (sr43, ss43) ∧ True) ∧ SvErrRet B out v n0) ∨
    ((pv ≠ 0) ∧
    (memBytes M0 x26 w40.toNat = memBytes M0 e0p e0l.toNat) ∧
    (memBytes M0 w50 w3c.toNat = memBytes M0 e1p e1l.toNat) ∧
    (memBytes M0 w4c w38.toNat = memBytes M0 e2p e2l.toNat) ∧
    (memBytes M0 w48 w34.toNat = memBytes M0 e3p e3l.toNat) ∧
    (memBytes M0 w44 w30.toNat = memBytes M0 e4p e4l.toNat) ∧
    ∃ sr43 ss43, ecdsaSigOf 32 M0 (sgp) (sgl.toNat) = .ok (sr43, ss43) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0xA4C (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = q ∧
        reg n' (24 : Fin 32) = x24 ∧
        reg n' (26 : Fin 32) = x26 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = sgp ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = BitVec.ofNat 8 ((sr43).getD 0 0) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x131 + j)) = BitVec.ofNat 8 ((sr43).getD (1 + j) 0)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x150 + j)) = BitVec.ofNat 8 ((ss43).getD j 0)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x171 + j)) = BitVec.ofNat 8 ((sr43).getD j 0)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 ((ss43).getD j 0)) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x291 + j)) = BitVec.ofNat 8 ((sr43).getD (1 + j) 0)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x2B0 + j)) = BitVec.ofNat 8 ((ss43).getD j 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x70, 0x4), (0x68, 0x4), (0x170, 0x41), (0x291, 0x3F), (0x130, 0x1), (0x131, 0x1F), (0x150, 0x20)]) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  by_cases hpv : pv ≠ 0
  rotate_left
  · -- 0x980: branch, taken
    obtain ⟨n1, d1, u1⟩ := s0.taken E0.self 0xE38 sv_at_980
      (by decide) (by rw [g0_10, s0.zero]; exact br_beq_t (Decidable.of_not_not hpv))
    have s1 : St n1.mem SV n1 0xE38 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
    have m1 : n1.mem = n0.mem := u1.mem
    have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
    have t1 : Steps n0 n1 := t0.trans (.single d1)
    have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
    have E1 : SvCode n1.mem := E0.fr F fr1
    have V1 : SvSaves B n1.mem v := V0.same m1
    have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, g0_2]
    have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, g0_3]
    have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, g0_4]
    have g1_10 : reg n1 a0 = pv := by rw [u1.regs, g0_10]
    have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, g0_18]
    have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, g0_19]
    have g1_20 : reg n1 (20 : Fin 32) = x20 := by rw [u1.regs, g0_20]
    have g1_21 : reg n1 (21 : Fin 32) = x21 := by rw [u1.regs, g0_21]
    have g1_22 : reg n1 (22 : Fin 32) = x22 := by rw [u1.regs, g0_22]
    have g1_23 : reg n1 (23 : Fin 32) = q := by rw [u1.regs, g0_23]
    have g1_24 : reg n1 (24 : Fin 32) = x24 := by rw [u1.regs, g0_24]
    have g1_26 : reg n1 (26 : Fin 32) = x26 := by rw [u1.regs, g0_26]
    have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
    have w1_30 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m1]; exact w0_30
    have w1_34 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m1]; exact w0_34
    have w1_38 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m1]; exact w0_38
    have w1_3c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m1]; exact w0_3c
    have w1_40 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m1]; exact w0_40
    have w1_44 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m1]; exact w0_44
    have w1_48 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m1]; exact w0_48
    have w1_4c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m1]; exact w0_4c
    have w1_50 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m1]; exact w0_50
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hpv h0'), sv_fail_e38 F E1 s1 t1 (fun x hx => (fR1 x hx).trans (fM x hx).symm) V1 hret g1_2 g1_18 hO g1_3 g1_4⟩
  -- 0x980: branch, not taken
  obtain ⟨n1, d1, u1⟩ := s0.notTaken E0.self 0x984 sv_at_980
    (by decide) (by rw [g0_10, s0.zero]; exact br_beq_f hpv)
  have s1 : St n1.mem SV n1 0x984 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n0.mem := u1.mem
  have fr1 : ∀ x, SvR B x → n1.mem x = n0.mem x := fun x _ => by rw [m1]
  have t1 : Steps n0 n1 := t0.trans (.single d1)
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fR0 x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.same m1
  have g1_2 : reg n1 sp = B + 0x21A0 := by rw [u1.regs, g0_2]
  have g1_3 : reg n1 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u1.regs, g0_3]
  have g1_4 : reg n1 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u1.regs, g0_4]
  have g1_10 : reg n1 a0 = pv := by rw [u1.regs, g0_10]
  have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, g0_18]
  have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, g0_19]
  have g1_20 : reg n1 (20 : Fin 32) = x20 := by rw [u1.regs, g0_20]
  have g1_21 : reg n1 (21 : Fin 32) = x21 := by rw [u1.regs, g0_21]
  have g1_22 : reg n1 (22 : Fin 32) = x22 := by rw [u1.regs, g0_22]
  have g1_23 : reg n1 (23 : Fin 32) = q := by rw [u1.regs, g0_23]
  have g1_24 : reg n1 (24 : Fin 32) = x24 := by rw [u1.regs, g0_24]
  have g1_26 : reg n1 (26 : Fin 32) = x26 := by rw [u1.regs, g0_26]
  have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
  have w1_30 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m1]; exact w0_30
  have w1_34 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m1]; exact w0_34
  have w1_38 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m1]; exact w0_38
  have w1_3c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m1]; exact w0_3c
  have w1_40 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m1]; exact w0_40
  have w1_44 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m1]; exact w0_44
  have w1_48 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m1]; exact w0_48
  have w1_4c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m1]; exact w0_4c
  have w1_50 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m1]; exact w0_50
  -- 0x984
  obtain ⟨n2, c2, u2⟩ := s1.block svDpv984 E1.self svDpv984_end
    ⟨trivial, trivial⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have s2 : St n2.mem SV n2 0x986 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have rb2 : ∀ q, reg n2 q = (runBlock svDpv984 (n1.mem, reg n1)).2 q := fun q => by rw [u2.regs]
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
  have g2_18 : reg n2 (18 : Fin 32) = out := by
    rw [rb2, runBlock_reg _ _ _ (18 : Fin 32) s1.zero (by decide), g1_18]
  have g2_19 : reg n2 (19 : Fin 32) = bp := by
    rw [rb2, runBlock_reg _ _ _ (19 : Fin 32) s1.zero (by decide), g1_19]
  have g2_20 : reg n2 (20 : Fin 32) = x20 := by
    rw [rb2, runBlock_reg _ _ _ (20 : Fin 32) s1.zero (by decide), g1_20]
  have g2_21 : reg n2 (21 : Fin 32) = x21 := by
    rw [rb2, runBlock_reg _ _ _ (21 : Fin 32) s1.zero (by decide), g1_21]
  have g2_22 : reg n2 (22 : Fin 32) = x22 := by
    rw [rb2, runBlock_reg _ _ _ (22 : Fin 32) s1.zero (by decide), g1_22]
  have g2_23 : reg n2 (23 : Fin 32) = q := by
    rw [rb2, runBlock_reg _ _ _ (23 : Fin 32) s1.zero (by decide), g1_23]
  have g2_24 : reg n2 (24 : Fin 32) = x24 := by
    rw [rb2, runBlock_reg _ _ _ (24 : Fin 32) s1.zero (by decide), g1_24]
  have g2_26 : reg n2 (26 : Fin 32) = x26 := by
    rw [rb2, runBlock_reg _ _ _ (26 : Fin 32) s1.zero (by decide), g1_26]
  have g2_10 : reg n2 a0 = x21 := by
    rw [rb2]; simp +decide only [runBlock, BInstr.run, svDpv984, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g1_2, g1_3, g1_4, g1_10, g1_18, g1_19, g1_20, g1_21, g1_22, g1_23, g1_24, g1_26, s1.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk2 : SvKeepL B n0.mem n2.mem [] := by rw [m2]; exact keep_kk1
  clear keep_kk1
  have w2_30 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m2]; exact w1_30
  have w2_34 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m2]; exact w1_34
  have w2_38 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m2]; exact w1_38
  have w2_3c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m2]; exact w1_3c
  have w2_40 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m2]; exact w1_40
  have w2_44 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m2]; exact w1_44
  have w2_48 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m2]; exact w1_48
  have w2_4c : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m2]; exact w1_4c
  have w2_50 : memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m2]; exact w1_50
  clear w1_50 w1_4c w1_48 w1_44 w1_40 w1_3c w1_38 w1_34 w1_30 g1_26 g1_24 g1_23 g1_22 g1_21 g1_20 g1_19 g1_18 g1_10 g1_4 g1_3 g1_2 V1 E1 fR1 t1 fr1 m1 s1 u1 d1 g0_4 g0_3 fR0 t0
  -- 0x986: lw outside the stack
  obtain ⟨n3, d3, u3⟩ := s2.lw E2.self sv_at_986 (off' := 0x988) (by decide)
    (by rw [g2_10]; exact ae0p)
  have s3 : St n3.mem SV n3 0x988 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x _ => by rw [m3]
  have t3 : Steps n0 n3 := t2.trans (.single d3)
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := fun x hx => (fr3 x hx).trans (fR2 x hx)
  have E3 : SvCode n3.mem := E2.fr F fr3
  have V3 : SvSaves B n3.mem v := V2.same m3
  have g3_2 : reg n3 sp = B + 0x21A0 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_2]
  have g3_3 : reg n3 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_3]
  have g3_4 : reg n3 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u3.regs, upd_ne (by decide) (by decide), g2_4]
  have g3_10 : reg n3 a0 = x21 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_10]
  have g3_18 : reg n3 (18 : Fin 32) = out := by rw [u3.regs, upd_ne (by decide) (by decide), g2_18]
  have g3_19 : reg n3 (19 : Fin 32) = bp := by rw [u3.regs, upd_ne (by decide) (by decide), g2_19]
  have g3_20 : reg n3 (20 : Fin 32) = x20 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_20]
  have g3_21 : reg n3 (21 : Fin 32) = x21 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_21]
  have g3_22 : reg n3 (22 : Fin 32) = x22 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_22]
  have g3_23 : reg n3 (23 : Fin 32) = q := by rw [u3.regs, upd_ne (by decide) (by decide), g2_23]
  have g3_24 : reg n3 (24 : Fin 32) = x24 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_24]
  have g3_26 : reg n3 (26 : Fin 32) = x26 := by rw [u3.regs, upd_ne (by decide) (by decide), g2_26]
  have g3_12 : reg n3 a2 = e0p := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g2_10, sv_ld fR2 he0p_in, he0p]
  have keep_kk3 : SvKeepL B n0.mem n3.mem [] := by rw [m3]; exact keep_kk2
  clear keep_kk2
  have w3_30 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m3]; exact w2_30
  have w3_34 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m3]; exact w2_34
  have w3_38 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m3]; exact w2_38
  have w3_3c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m3]; exact w2_3c
  have w3_40 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m3]; exact w2_40
  have w3_44 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m3]; exact w2_44
  have w3_48 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m3]; exact w2_48
  have w3_4c : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m3]; exact w2_4c
  have w3_50 : memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m3]; exact w2_50
  clear w2_50 w2_4c w2_48 w2_44 w2_40 w2_3c w2_38 w2_34 w2_30 g2_10 g2_26 g2_24 g2_23 g2_22 g2_21 g2_20 g2_19 g2_18 g2_4 g2_3 g2_2 V2 E2 fR2 t2 fr2 rb2 s2 m2 u2 c2
  -- 0x988: lw outside the stack
  obtain ⟨n4, d4, u4⟩ := s3.lw E3.self sv_at_988 (off' := 0x98A) (by decide)
    (by rw [g3_10]; exact ae0l)
  have s4 : St n4.mem SV n4 0x98A (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have fr4 : ∀ x, SvR B x → n4.mem x = n3.mem x := fun x _ => by rw [m4]
  have t4 : Steps n0 n4 := t3.trans (.single d4)
  have fR4 : ∀ x, SvR B x → n4.mem x = M0 x := fun x hx => (fr4 x hx).trans (fR3 x hx)
  have E4 : SvCode n4.mem := E3.fr F fr4
  have V4 : SvSaves B n4.mem v := V3.same m4
  have g4_2 : reg n4 sp = B + 0x21A0 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_2]
  have g4_3 : reg n4 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_3]
  have g4_4 : reg n4 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u4.regs, upd_ne (by decide) (by decide), g3_4]
  have g4_10 : reg n4 a0 = x21 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_10]
  have g4_12 : reg n4 a2 = e0p := by rw [u4.regs, upd_ne (by decide) (by decide), g3_12]
  have g4_18 : reg n4 (18 : Fin 32) = out := by rw [u4.regs, upd_ne (by decide) (by decide), g3_18]
  have g4_19 : reg n4 (19 : Fin 32) = bp := by rw [u4.regs, upd_ne (by decide) (by decide), g3_19]
  have g4_20 : reg n4 (20 : Fin 32) = x20 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_20]
  have g4_21 : reg n4 (21 : Fin 32) = x21 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_21]
  have g4_22 : reg n4 (22 : Fin 32) = x22 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_22]
  have g4_23 : reg n4 (23 : Fin 32) = q := by rw [u4.regs, upd_ne (by decide) (by decide), g3_23]
  have g4_24 : reg n4 (24 : Fin 32) = x24 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_24]
  have g4_26 : reg n4 (26 : Fin 32) = x26 := by rw [u4.regs, upd_ne (by decide) (by decide), g3_26]
  have g4_13 : reg n4 a3 = e0l := by
    rw [u4.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g3_10, sv_ld fR3 he0l_in, he0l]
  have keep_kk4 : SvKeepL B n0.mem n4.mem [] := by rw [m4]; exact keep_kk3
  clear keep_kk3
  have w4_30 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m4]; exact w3_30
  have w4_34 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m4]; exact w3_34
  have w4_38 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m4]; exact w3_38
  have w4_3c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m4]; exact w3_3c
  have w4_40 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m4]; exact w3_40
  have w4_44 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m4]; exact w3_44
  have w4_48 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m4]; exact w3_48
  have w4_4c : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m4]; exact w3_4c
  have w4_50 : memLoad32 n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m4]; exact w3_50
  clear w3_50 w3_4c w3_48 w3_44 w3_40 w3_3c w3_38 w3_34 w3_30 g3_12 g3_26 g3_24 g3_23 g3_22 g3_21 g3_20 g3_19 g3_18 g3_10 g3_4 g3_3 g3_2 V3 E3 fR3 t3 fr3 m3 s3 u3 d3
  -- 0x98A
  obtain ⟨n5, c5, u5⟩ := s4.block svDpv98a E4.self svDpv98a_end
    ⟨trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0x98C (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have rb5 : ∀ q, reg n5 q = (runBlock svDpv98a (n4.mem, reg n4)).2 q := fun q => by rw [u5.regs]
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
  have g5_12 : reg n5 a2 = e0p := by
    rw [rb5, runBlock_reg _ _ _ a2 s4.zero (by decide), g4_12]
  have g5_13 : reg n5 a3 = e0l := by
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
  have g5_23 : reg n5 (23 : Fin 32) = q := by
    rw [rb5, runBlock_reg _ _ _ (23 : Fin 32) s4.zero (by decide), g4_23]
  have g5_24 : reg n5 (24 : Fin 32) = x24 := by
    rw [rb5, runBlock_reg _ _ _ (24 : Fin 32) s4.zero (by decide), g4_24]
  have g5_26 : reg n5 (26 : Fin 32) = x26 := by
    rw [rb5, runBlock_reg _ _ _ (26 : Fin 32) s4.zero (by decide), g4_26]
  have g5_10 : reg n5 a0 = x26 := by
    rw [rb5]; simp +decide only [runBlock, BInstr.run, svDpv98a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g4_2, g4_3, g4_4, g4_10, g4_12, g4_13, g4_18, g4_19, g4_20, g4_21, g4_22, g4_23, g4_24, g4_26, s4.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk5 : SvKeepL B n0.mem n5.mem [] := by rw [m5]; exact keep_kk4
  clear keep_kk4
  have w5_30 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m5]; exact w4_30
  have w5_34 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m5]; exact w4_34
  have w5_38 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m5]; exact w4_38
  have w5_3c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m5]; exact w4_3c
  have w5_40 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m5]; exact w4_40
  have w5_44 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m5]; exact w4_44
  have w5_48 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m5]; exact w4_48
  have w5_4c : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m5]; exact w4_4c
  have w5_50 : memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m5]; exact w4_50
  clear w4_50 w4_4c w4_48 w4_44 w4_40 w4_3c w4_38 w4_34 w4_30 g4_13 g4_26 g4_24 g4_23 g4_22 g4_21 g4_20 g4_19 g4_18 g4_12 g4_10 g4_4 g4_3 g4_2 V4 E4 fR4 t4 fr4 m4 s4 u4 d4
  -- 0x98C: lw
  obtain ⟨n6, d6, u6⟩ := s5.lw E5.self sv_at_98c (off' := 0x98E) (by decide)
    (by rw [g5_2, show B + 0x21A0 + 0x40 = B + 0x21A0 + BitVec.ofNat 32 0x40 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s6 : St n6.mem SV n6 0x98E (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have fr6 : ∀ x, SvR B x → n6.mem x = n5.mem x := fun x _ => by rw [m6]
  have t6 : Steps n0 n6 := t5.trans (.single d6)
  have fR6 : ∀ x, SvR B x → n6.mem x = M0 x := fun x hx => (fr6 x hx).trans (fR5 x hx)
  have E6 : SvCode n6.mem := E5.fr F fr6
  have V6 : SvSaves B n6.mem v := V5.same m6
  have g6_2 : reg n6 sp = B + 0x21A0 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_2]
  have g6_3 : reg n6 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_3]
  have g6_4 : reg n6 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u6.regs, upd_ne (by decide) (by decide), g5_4]
  have g6_10 : reg n6 a0 = x26 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_10]
  have g6_12 : reg n6 a2 = e0p := by rw [u6.regs, upd_ne (by decide) (by decide), g5_12]
  have g6_13 : reg n6 a3 = e0l := by rw [u6.regs, upd_ne (by decide) (by decide), g5_13]
  have g6_18 : reg n6 (18 : Fin 32) = out := by rw [u6.regs, upd_ne (by decide) (by decide), g5_18]
  have g6_19 : reg n6 (19 : Fin 32) = bp := by rw [u6.regs, upd_ne (by decide) (by decide), g5_19]
  have g6_20 : reg n6 (20 : Fin 32) = x20 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_20]
  have g6_21 : reg n6 (21 : Fin 32) = x21 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_21]
  have g6_22 : reg n6 (22 : Fin 32) = x22 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_22]
  have g6_23 : reg n6 (23 : Fin 32) = q := by rw [u6.regs, upd_ne (by decide) (by decide), g5_23]
  have g6_24 : reg n6 (24 : Fin 32) = x24 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_24]
  have g6_26 : reg n6 (26 : Fin 32) = x26 := by rw [u6.regs, upd_ne (by decide) (by decide), g5_26]
  have g6_11 : reg n6 a1 = w40 := by
    rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g5_2, show B + 0x21A0 + 0x40 = B + 0x21A0 + BitVec.ofNat 32 0x40 by sv_addr, w5_40]
  have keep_kk6 : SvKeepL B n0.mem n6.mem [] := by rw [m6]; exact keep_kk5
  clear keep_kk5
  have w6_30 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m6]; exact w5_30
  have w6_34 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m6]; exact w5_34
  have w6_38 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m6]; exact w5_38
  have w6_3c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m6]; exact w5_3c
  have w6_40 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m6]; exact w5_40
  have w6_44 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m6]; exact w5_44
  have w6_48 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m6]; exact w5_48
  have w6_4c : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m6]; exact w5_4c
  have w6_50 : memLoad32 n6.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m6]; exact w5_50
  clear w5_50 w5_4c w5_48 w5_44 w5_40 w5_3c w5_38 w5_34 w5_30 g5_10 g5_26 g5_24 g5_23 g5_22 g5_21 g5_20 g5_19 g5_18 g5_13 g5_12 g5_4 g5_3 g5_2 V5 E5 fR5 t5 fr5 rb5 s5 m5 u5 c5
  -- 0x98E: sv_seqEqF
  obtain ⟨n7, c7, s7, rk7, a0_7, K7, fr7⟩ := sv_seqEqF (pl := w40.toNat) (ql := e0l.toNat)
    F E6 s6 sv_at_98e sv_at_992 (by decide) (by decide) g6_2
    g6_10 (by rw [g6_11, ofNat_toNat_self]) g6_12 (by rw [g6_13, ofNat_toNat_self]) p0_in e0_in
  have t7 : Steps n0 n7 := t6.trans c7
  have fR7 : ∀ x, SvR B x → n7.mem x = M0 x := fun x hx => (fr7 x hx).trans (fR6 x hx)
  have E7 : SvCode n7.mem := E6.fr F fr7
  have V7 : SvSaves B n7.mem v := V6.keepL K7 (by decide)
  rw [sv_mbRo FW fR6 p0_in, sv_mbRo FW fR6 e0_in] at a0_7
  have g7_2 : reg n7 sp = B + 0x21A0 := by rw [rk7 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g6_2]
  have g7_3 : reg n7 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk7 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g6_3]
  have g7_4 : reg n7 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk7 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g6_4]
  have g7_18 : reg n7 (18 : Fin 32) = out := by rw [rk7 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g6_18]
  have g7_19 : reg n7 (19 : Fin 32) = bp := by rw [rk7 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g6_19]
  have g7_20 : reg n7 (20 : Fin 32) = x20 := by rw [rk7 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g6_20]
  have g7_21 : reg n7 (21 : Fin 32) = x21 := by rw [rk7 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g6_21]
  have g7_22 : reg n7 (22 : Fin 32) = x22 := by rw [rk7 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g6_22]
  have g7_23 : reg n7 (23 : Fin 32) = q := by rw [rk7 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g6_23]
  have g7_24 : reg n7 (24 : Fin 32) = x24 := by rw [rk7 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g6_24]
  have g7_26 : reg n7 (26 : Fin 32) = x26 := by rw [rk7 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g6_26]
  have keep_kk7 : SvKeepL B n0.mem n7.mem [] := keep_kk6.trans K7
  clear keep_kk6
  have w7_30 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K7.w32 (by decide) (by decide)).trans w6_30
  have w7_34 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K7.w32 (by decide) (by decide)).trans w6_34
  have w7_38 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K7.w32 (by decide) (by decide)).trans w6_38
  have w7_3c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K7.w32 (by decide) (by decide)).trans w6_3c
  have w7_40 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K7.w32 (by decide) (by decide)).trans w6_40
  have w7_44 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K7.w32 (by decide) (by decide)).trans w6_44
  have w7_48 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K7.w32 (by decide) (by decide)).trans w6_48
  have w7_4c : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K7.w32 (by decide) (by decide)).trans w6_4c
  have w7_50 : memLoad32 n7.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K7.w32 (by decide) (by decide)).trans w6_50
  clear w6_50 w6_4c w6_48 w6_44 w6_40 w6_3c w6_38 w6_34 w6_30 g6_11 g6_26 g6_24 g6_23 g6_22 g6_21 g6_20 g6_19 g6_18 g6_13 g6_12 g6_10 g6_4 g6_3 g6_2 V6 E6 fR6 t6 fr6 m6 s6 u6 d6
  by_cases hq0 : memBytes M0 x26 w40.toNat = memBytes M0 e0p e0l.toNat
  rotate_left
  · have g7_10 : reg n7 a0 = BitVec.ofNat 32 0 := by rw [a0_7, ite_eq_right hq0]; rfl
    -- 0x996: branch, taken
    obtain ⟨n8, d8, u8⟩ := s7.taken E7.self 0xE46 sv_at_996
      (by decide) (by rw [g7_10, s7.zero]; decide)
    have s8 : St n8.mem SV n8 0xE46 (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
    have m8 : n8.mem = n7.mem := u8.mem
    have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
    have t8 : Steps n0 n8 := t7.trans (.single d8)
    have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
    have E8 : SvCode n8.mem := E7.fr F fr8
    have V8 : SvSaves B n8.mem v := V7.same m8
    have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, g7_2]
    have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, g7_3]
    have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, g7_4]
    have g8_10 : reg n8 a0 = BitVec.ofNat 32 0x0 := by rw [u8.regs, g7_10]
    have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, g7_18]
    have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, g7_19]
    have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [u8.regs, g7_20]
    have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, g7_21]
    have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [u8.regs, g7_22]
    have g8_23 : reg n8 (23 : Fin 32) = q := by rw [u8.regs, g7_23]
    have g8_24 : reg n8 (24 : Fin 32) = x24 := by rw [u8.regs, g7_24]
    have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [u8.regs, g7_26]
    have keep_kk8 : SvKeepL B n0.mem n8.mem [] := by rw [m8]; exact keep_kk7
    clear keep_kk7
    have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m8]; exact w7_30
    have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m8]; exact w7_34
    have w8_38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m8]; exact w7_38
    have w8_3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m8]; exact w7_3c
    have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m8]; exact w7_40
    have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m8]; exact w7_44
    have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m8]; exact w7_48
    have w8_4c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m8]; exact w7_4c
    have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m8]; exact w7_50
    clear w7_50 w7_4c w7_48 w7_44 w7_40 w7_3c w7_38 w7_34 w7_30 g7_26 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 K7 a0_7 rk7 s7 c7
    exact .inl ⟨(fun ⟨h0', h1', _⟩ => by exact hq0 h1'), sv_fail_e46 F E8 s8 t8 (fun x hx => (fR8 x hx).trans (fM x hx).symm) V8 hret g8_2 g8_18 hO g8_3 g8_4⟩
  have g7_10 : reg n7 a0 = BitVec.ofNat 32 1 := by rw [a0_7, ite_eq_left hq0]; rfl
  -- 0x996: branch, not taken
  obtain ⟨n8, d8, u8⟩ := s7.notTaken E7.self 0x99A sv_at_996
    (by decide) (by rw [g7_10, s7.zero]; decide)
  have s8 : St n8.mem SV n8 0x99A (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have fr8 : ∀ x, SvR B x → n8.mem x = n7.mem x := fun x _ => by rw [m8]
  have t8 : Steps n0 n8 := t7.trans (.single d8)
  have fR8 : ∀ x, SvR B x → n8.mem x = M0 x := fun x hx => (fr8 x hx).trans (fR7 x hx)
  have E8 : SvCode n8.mem := E7.fr F fr8
  have V8 : SvSaves B n8.mem v := V7.same m8
  have g8_2 : reg n8 sp = B + 0x21A0 := by rw [u8.regs, g7_2]
  have g8_3 : reg n8 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u8.regs, g7_3]
  have g8_4 : reg n8 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u8.regs, g7_4]
  have g8_10 : reg n8 a0 = BitVec.ofNat 32 0x1 := by rw [u8.regs, g7_10]
  have g8_18 : reg n8 (18 : Fin 32) = out := by rw [u8.regs, g7_18]
  have g8_19 : reg n8 (19 : Fin 32) = bp := by rw [u8.regs, g7_19]
  have g8_20 : reg n8 (20 : Fin 32) = x20 := by rw [u8.regs, g7_20]
  have g8_21 : reg n8 (21 : Fin 32) = x21 := by rw [u8.regs, g7_21]
  have g8_22 : reg n8 (22 : Fin 32) = x22 := by rw [u8.regs, g7_22]
  have g8_23 : reg n8 (23 : Fin 32) = q := by rw [u8.regs, g7_23]
  have g8_24 : reg n8 (24 : Fin 32) = x24 := by rw [u8.regs, g7_24]
  have g8_26 : reg n8 (26 : Fin 32) = x26 := by rw [u8.regs, g7_26]
  have keep_kk8 : SvKeepL B n0.mem n8.mem [] := by rw [m8]; exact keep_kk7
  clear keep_kk7
  have w8_30 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m8]; exact w7_30
  have w8_34 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m8]; exact w7_34
  have w8_38 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m8]; exact w7_38
  have w8_3c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m8]; exact w7_3c
  have w8_40 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m8]; exact w7_40
  have w8_44 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m8]; exact w7_44
  have w8_48 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m8]; exact w7_48
  have w8_4c : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m8]; exact w7_4c
  have w8_50 : memLoad32 n8.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m8]; exact w7_50
  clear w7_50 w7_4c w7_48 w7_44 w7_40 w7_3c w7_38 w7_34 w7_30 g7_26 g7_24 g7_23 g7_22 g7_21 g7_20 g7_19 g7_18 g7_4 g7_3 g7_2 V7 E7 fR7 t7 fr7 K7 a0_7 rk7 s7 c7
  -- 0x99A
  obtain ⟨n9, c9, u9⟩ := s8.block svDpv99a E8.self svDpv99a_end
    ⟨trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have s9 : St n9.mem SV n9 0x99C (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have rb9 : ∀ q, reg n9 q = (runBlock svDpv99a (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
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
  have g9_23 : reg n9 (23 : Fin 32) = q := by
    rw [rb9, runBlock_reg _ _ _ (23 : Fin 32) s8.zero (by decide), g8_23]
  have g9_24 : reg n9 (24 : Fin 32) = x24 := by
    rw [rb9, runBlock_reg _ _ _ (24 : Fin 32) s8.zero (by decide), g8_24]
  have g9_26 : reg n9 (26 : Fin 32) = x26 := by
    rw [rb9, runBlock_reg _ _ _ (26 : Fin 32) s8.zero (by decide), g8_26]
  have g9_10 : reg n9 a0 = x21 := by
    rw [rb9]; simp +decide only [runBlock, BInstr.run, svDpv99a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g8_2, g8_3, g8_4, g8_10, g8_18, g8_19, g8_20, g8_21, g8_22, g8_23, g8_24, g8_26, s8.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk9 : SvKeepL B n0.mem n9.mem [] := by rw [m9]; exact keep_kk8
  clear keep_kk8
  have w9_30 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m9]; exact w8_30
  have w9_34 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m9]; exact w8_34
  have w9_38 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m9]; exact w8_38
  have w9_3c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m9]; exact w8_3c
  have w9_40 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m9]; exact w8_40
  have w9_44 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m9]; exact w8_44
  have w9_48 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m9]; exact w8_48
  have w9_4c : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m9]; exact w8_4c
  have w9_50 : memLoad32 n9.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m9]; exact w8_50
  clear w8_50 w8_4c w8_48 w8_44 w8_40 w8_3c w8_38 w8_34 w8_30 g8_26 g8_24 g8_23 g8_22 g8_21 g8_20 g8_19 g8_18 g8_10 g8_4 g8_3 g8_2 V8 E8 fR8 t8 fr8 m8 s8 u8 d8 g7_10
  -- 0x99C: lw outside the stack
  obtain ⟨n10, d10, u10⟩ := s9.lw E9.self sv_at_99c (off' := 0x99E) (by decide)
    (by rw [g9_10]; exact ae1p)
  have s10 : St n10.mem SV n10 0x99E (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have fr10 : ∀ x, SvR B x → n10.mem x = n9.mem x := fun x _ => by rw [m10]
  have t10 : Steps n0 n10 := t9.trans (.single d10)
  have fR10 : ∀ x, SvR B x → n10.mem x = M0 x := fun x hx => (fr10 x hx).trans (fR9 x hx)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have V10 : SvSaves B n10.mem v := V9.same m10
  have g10_2 : reg n10 sp = B + 0x21A0 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_2]
  have g10_3 : reg n10 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_3]
  have g10_4 : reg n10 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u10.regs, upd_ne (by decide) (by decide), g9_4]
  have g10_10 : reg n10 a0 = x21 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_10]
  have g10_18 : reg n10 (18 : Fin 32) = out := by rw [u10.regs, upd_ne (by decide) (by decide), g9_18]
  have g10_19 : reg n10 (19 : Fin 32) = bp := by rw [u10.regs, upd_ne (by decide) (by decide), g9_19]
  have g10_20 : reg n10 (20 : Fin 32) = x20 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_20]
  have g10_21 : reg n10 (21 : Fin 32) = x21 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_21]
  have g10_22 : reg n10 (22 : Fin 32) = x22 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_22]
  have g10_23 : reg n10 (23 : Fin 32) = q := by rw [u10.regs, upd_ne (by decide) (by decide), g9_23]
  have g10_24 : reg n10 (24 : Fin 32) = x24 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_24]
  have g10_26 : reg n10 (26 : Fin 32) = x26 := by rw [u10.regs, upd_ne (by decide) (by decide), g9_26]
  have g10_12 : reg n10 a2 = e1p := by
    rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g9_10, sv_ld fR9 he1p_in, he1p]
  have keep_kk10 : SvKeepL B n0.mem n10.mem [] := by rw [m10]; exact keep_kk9
  clear keep_kk9
  have w10_30 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m10]; exact w9_30
  have w10_34 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m10]; exact w9_34
  have w10_38 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m10]; exact w9_38
  have w10_3c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m10]; exact w9_3c
  have w10_40 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m10]; exact w9_40
  have w10_44 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m10]; exact w9_44
  have w10_48 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m10]; exact w9_48
  have w10_4c : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m10]; exact w9_4c
  have w10_50 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m10]; exact w9_50
  clear w9_50 w9_4c w9_48 w9_44 w9_40 w9_3c w9_38 w9_34 w9_30 g9_10 g9_26 g9_24 g9_23 g9_22 g9_21 g9_20 g9_19 g9_18 g9_4 g9_3 g9_2 V9 E9 fR9 t9 fr9 rb9 s9 m9 u9 c9
  -- 0x99E: lw outside the stack
  obtain ⟨n11, d11, u11⟩ := s10.lw E10.self sv_at_99e (off' := 0x9A0) (by decide)
    (by rw [g10_10]; exact ae1l)
  have s11 : St n11.mem SV n11 0x9A0 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have m11 : n11.mem = n10.mem := u11.mem
  have fr11 : ∀ x, SvR B x → n11.mem x = n10.mem x := fun x _ => by rw [m11]
  have t11 : Steps n0 n11 := t10.trans (.single d11)
  have fR11 : ∀ x, SvR B x → n11.mem x = M0 x := fun x hx => (fr11 x hx).trans (fR10 x hx)
  have E11 : SvCode n11.mem := E10.fr F fr11
  have V11 : SvSaves B n11.mem v := V10.same m11
  have g11_2 : reg n11 sp = B + 0x21A0 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_2]
  have g11_3 : reg n11 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_3]
  have g11_4 : reg n11 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u11.regs, upd_ne (by decide) (by decide), g10_4]
  have g11_10 : reg n11 a0 = x21 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_10]
  have g11_12 : reg n11 a2 = e1p := by rw [u11.regs, upd_ne (by decide) (by decide), g10_12]
  have g11_18 : reg n11 (18 : Fin 32) = out := by rw [u11.regs, upd_ne (by decide) (by decide), g10_18]
  have g11_19 : reg n11 (19 : Fin 32) = bp := by rw [u11.regs, upd_ne (by decide) (by decide), g10_19]
  have g11_20 : reg n11 (20 : Fin 32) = x20 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_20]
  have g11_21 : reg n11 (21 : Fin 32) = x21 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_21]
  have g11_22 : reg n11 (22 : Fin 32) = x22 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_22]
  have g11_23 : reg n11 (23 : Fin 32) = q := by rw [u11.regs, upd_ne (by decide) (by decide), g10_23]
  have g11_24 : reg n11 (24 : Fin 32) = x24 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_24]
  have g11_26 : reg n11 (26 : Fin 32) = x26 := by rw [u11.regs, upd_ne (by decide) (by decide), g10_26]
  have g11_13 : reg n11 a3 = e1l := by
    rw [u11.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g10_10, sv_ld fR10 he1l_in, he1l]
  have keep_kk11 : SvKeepL B n0.mem n11.mem [] := by rw [m11]; exact keep_kk10
  clear keep_kk10
  have w11_30 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m11]; exact w10_30
  have w11_34 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m11]; exact w10_34
  have w11_38 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m11]; exact w10_38
  have w11_3c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m11]; exact w10_3c
  have w11_40 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m11]; exact w10_40
  have w11_44 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m11]; exact w10_44
  have w11_48 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m11]; exact w10_48
  have w11_4c : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m11]; exact w10_4c
  have w11_50 : memLoad32 n11.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m11]; exact w10_50
  clear w10_50 w10_4c w10_48 w10_44 w10_40 w10_3c w10_38 w10_34 w10_30 g10_12 g10_26 g10_24 g10_23 g10_22 g10_21 g10_20 g10_19 g10_18 g10_10 g10_4 g10_3 g10_2 V10 E10 fR10 t10 fr10 m10 s10 u10 d10
  -- 0x9A0: lw
  obtain ⟨n12, d12, u12⟩ := s11.lw E11.self sv_at_9a0 (off' := 0x9A2) (by decide)
    (by rw [g11_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s12 : St n12.mem SV n12 0x9A2 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
  have m12 : n12.mem = n11.mem := u12.mem
  have fr12 : ∀ x, SvR B x → n12.mem x = n11.mem x := fun x _ => by rw [m12]
  have t12 : Steps n0 n12 := t11.trans (.single d12)
  have fR12 : ∀ x, SvR B x → n12.mem x = M0 x := fun x hx => (fr12 x hx).trans (fR11 x hx)
  have E12 : SvCode n12.mem := E11.fr F fr12
  have V12 : SvSaves B n12.mem v := V11.same m12
  have g12_2 : reg n12 sp = B + 0x21A0 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_2]
  have g12_3 : reg n12 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_3]
  have g12_4 : reg n12 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u12.regs, upd_ne (by decide) (by decide), g11_4]
  have g12_12 : reg n12 a2 = e1p := by rw [u12.regs, upd_ne (by decide) (by decide), g11_12]
  have g12_13 : reg n12 a3 = e1l := by rw [u12.regs, upd_ne (by decide) (by decide), g11_13]
  have g12_18 : reg n12 (18 : Fin 32) = out := by rw [u12.regs, upd_ne (by decide) (by decide), g11_18]
  have g12_19 : reg n12 (19 : Fin 32) = bp := by rw [u12.regs, upd_ne (by decide) (by decide), g11_19]
  have g12_20 : reg n12 (20 : Fin 32) = x20 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_20]
  have g12_21 : reg n12 (21 : Fin 32) = x21 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_21]
  have g12_22 : reg n12 (22 : Fin 32) = x22 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_22]
  have g12_23 : reg n12 (23 : Fin 32) = q := by rw [u12.regs, upd_ne (by decide) (by decide), g11_23]
  have g12_24 : reg n12 (24 : Fin 32) = x24 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_24]
  have g12_26 : reg n12 (26 : Fin 32) = x26 := by rw [u12.regs, upd_ne (by decide) (by decide), g11_26]
  have g12_10 : reg n12 a0 = w50 := by
    rw [u12.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g11_2, show B + 0x21A0 + 0x50 = B + 0x21A0 + BitVec.ofNat 32 0x50 by sv_addr, w11_50]
  have keep_kk12 : SvKeepL B n0.mem n12.mem [] := by rw [m12]; exact keep_kk11
  clear keep_kk11
  have w12_30 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m12]; exact w11_30
  have w12_34 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m12]; exact w11_34
  have w12_38 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m12]; exact w11_38
  have w12_3c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m12]; exact w11_3c
  have w12_40 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m12]; exact w11_40
  have w12_44 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m12]; exact w11_44
  have w12_48 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m12]; exact w11_48
  have w12_4c : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m12]; exact w11_4c
  have w12_50 : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m12]; exact w11_50
  clear w11_50 w11_4c w11_48 w11_44 w11_40 w11_3c w11_38 w11_34 w11_30 g11_13 g11_26 g11_24 g11_23 g11_22 g11_21 g11_20 g11_19 g11_18 g11_12 g11_10 g11_4 g11_3 g11_2 V11 E11 fR11 t11 fr11 m11 s11 u11 d11
  -- 0x9A2: lw
  obtain ⟨n13, d13, u13⟩ := s12.lw E12.self sv_at_9a2 (off' := 0x9A4) (by decide)
    (by rw [g12_2, show B + 0x21A0 + 0x3C = B + 0x21A0 + BitVec.ofNat 32 0x3C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s13 : St n13.mem SV n13 0x9A4 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have m13 : n13.mem = n12.mem := u13.mem
  have fr13 : ∀ x, SvR B x → n13.mem x = n12.mem x := fun x _ => by rw [m13]
  have t13 : Steps n0 n13 := t12.trans (.single d13)
  have fR13 : ∀ x, SvR B x → n13.mem x = M0 x := fun x hx => (fr13 x hx).trans (fR12 x hx)
  have E13 : SvCode n13.mem := E12.fr F fr13
  have V13 : SvSaves B n13.mem v := V12.same m13
  have g13_2 : reg n13 sp = B + 0x21A0 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_2]
  have g13_3 : reg n13 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_3]
  have g13_4 : reg n13 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u13.regs, upd_ne (by decide) (by decide), g12_4]
  have g13_10 : reg n13 a0 = w50 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_10]
  have g13_12 : reg n13 a2 = e1p := by rw [u13.regs, upd_ne (by decide) (by decide), g12_12]
  have g13_13 : reg n13 a3 = e1l := by rw [u13.regs, upd_ne (by decide) (by decide), g12_13]
  have g13_18 : reg n13 (18 : Fin 32) = out := by rw [u13.regs, upd_ne (by decide) (by decide), g12_18]
  have g13_19 : reg n13 (19 : Fin 32) = bp := by rw [u13.regs, upd_ne (by decide) (by decide), g12_19]
  have g13_20 : reg n13 (20 : Fin 32) = x20 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_20]
  have g13_21 : reg n13 (21 : Fin 32) = x21 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_21]
  have g13_22 : reg n13 (22 : Fin 32) = x22 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_22]
  have g13_23 : reg n13 (23 : Fin 32) = q := by rw [u13.regs, upd_ne (by decide) (by decide), g12_23]
  have g13_24 : reg n13 (24 : Fin 32) = x24 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_24]
  have g13_26 : reg n13 (26 : Fin 32) = x26 := by rw [u13.regs, upd_ne (by decide) (by decide), g12_26]
  have g13_11 : reg n13 a1 = w3c := by
    rw [u13.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g12_2, show B + 0x21A0 + 0x3C = B + 0x21A0 + BitVec.ofNat 32 0x3C by sv_addr, w12_3c]
  have keep_kk13 : SvKeepL B n0.mem n13.mem [] := by rw [m13]; exact keep_kk12
  clear keep_kk12
  have w13_30 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m13]; exact w12_30
  have w13_34 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m13]; exact w12_34
  have w13_38 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m13]; exact w12_38
  have w13_3c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m13]; exact w12_3c
  have w13_40 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m13]; exact w12_40
  have w13_44 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m13]; exact w12_44
  have w13_48 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m13]; exact w12_48
  have w13_4c : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m13]; exact w12_4c
  have w13_50 : memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m13]; exact w12_50
  clear w12_50 w12_4c w12_48 w12_44 w12_40 w12_3c w12_38 w12_34 w12_30 g12_10 g12_26 g12_24 g12_23 g12_22 g12_21 g12_20 g12_19 g12_18 g12_13 g12_12 g12_4 g12_3 g12_2 V12 E12 fR12 t12 fr12 m12 s12 u12 d12
  -- 0x9A4: sv_seqEqF
  obtain ⟨n14, c14, s14, rk14, a0_14, K14, fr14⟩ := sv_seqEqF (pl := w3c.toNat) (ql := e1l.toNat)
    F E13 s13 sv_at_9a4 sv_at_9a8 (by decide) (by decide) g13_2
    g13_10 (by rw [g13_11, ofNat_toNat_self]) g13_12 (by rw [g13_13, ofNat_toNat_self]) p1_in e1_in
  have t14 : Steps n0 n14 := t13.trans c14
  have fR14 : ∀ x, SvR B x → n14.mem x = M0 x := fun x hx => (fr14 x hx).trans (fR13 x hx)
  have E14 : SvCode n14.mem := E13.fr F fr14
  have V14 : SvSaves B n14.mem v := V13.keepL K14 (by decide)
  rw [sv_mbRo FW fR13 p1_in, sv_mbRo FW fR13 e1_in] at a0_14
  have g14_2 : reg n14 sp = B + 0x21A0 := by rw [rk14 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_2]
  have g14_3 : reg n14 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk14 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_3]
  have g14_4 : reg n14 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk14 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_4]
  have g14_18 : reg n14 (18 : Fin 32) = out := by rw [rk14 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_18]
  have g14_19 : reg n14 (19 : Fin 32) = bp := by rw [rk14 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_19]
  have g14_20 : reg n14 (20 : Fin 32) = x20 := by rw [rk14 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_20]
  have g14_21 : reg n14 (21 : Fin 32) = x21 := by rw [rk14 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_21]
  have g14_22 : reg n14 (22 : Fin 32) = x22 := by rw [rk14 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_22]
  have g14_23 : reg n14 (23 : Fin 32) = q := by rw [rk14 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_23]
  have g14_24 : reg n14 (24 : Fin 32) = x24 := by rw [rk14 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_24]
  have g14_26 : reg n14 (26 : Fin 32) = x26 := by rw [rk14 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g13_26]
  have keep_kk14 : SvKeepL B n0.mem n14.mem [] := keep_kk13.trans K14
  clear keep_kk13
  have w14_30 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K14.w32 (by decide) (by decide)).trans w13_30
  have w14_34 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K14.w32 (by decide) (by decide)).trans w13_34
  have w14_38 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K14.w32 (by decide) (by decide)).trans w13_38
  have w14_3c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K14.w32 (by decide) (by decide)).trans w13_3c
  have w14_40 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K14.w32 (by decide) (by decide)).trans w13_40
  have w14_44 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K14.w32 (by decide) (by decide)).trans w13_44
  have w14_48 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K14.w32 (by decide) (by decide)).trans w13_48
  have w14_4c : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K14.w32 (by decide) (by decide)).trans w13_4c
  have w14_50 : memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K14.w32 (by decide) (by decide)).trans w13_50
  clear w13_50 w13_4c w13_48 w13_44 w13_40 w13_3c w13_38 w13_34 w13_30 g13_11 g13_26 g13_24 g13_23 g13_22 g13_21 g13_20 g13_19 g13_18 g13_13 g13_12 g13_10 g13_4 g13_3 g13_2 V13 E13 fR13 t13 fr13 m13 s13 u13 d13
  by_cases hq1 : memBytes M0 w50 w3c.toNat = memBytes M0 e1p e1l.toNat
  rotate_left
  · have g14_10 : reg n14 a0 = BitVec.ofNat 32 0 := by rw [a0_14, ite_eq_right hq1]; rfl
    -- 0x9AC: branch, taken
    obtain ⟨n15, d15, u15⟩ := s14.taken E14.self 0xE46 sv_at_9ac
      (by decide) (by rw [g14_10, s14.zero]; decide)
    have s15 : St n15.mem SV n15 0xE46 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
    have m15 : n15.mem = n14.mem := u15.mem
    have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
    have t15 : Steps n0 n15 := t14.trans (.single d15)
    have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
    have E15 : SvCode n15.mem := E14.fr F fr15
    have V15 : SvSaves B n15.mem v := V14.same m15
    have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, g14_2]
    have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, g14_3]
    have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, g14_4]
    have g15_10 : reg n15 a0 = BitVec.ofNat 32 0x0 := by rw [u15.regs, g14_10]
    have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, g14_18]
    have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, g14_19]
    have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [u15.regs, g14_20]
    have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, g14_21]
    have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [u15.regs, g14_22]
    have g15_23 : reg n15 (23 : Fin 32) = q := by rw [u15.regs, g14_23]
    have g15_24 : reg n15 (24 : Fin 32) = x24 := by rw [u15.regs, g14_24]
    have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, g14_26]
    have keep_kk15 : SvKeepL B n0.mem n15.mem [] := by rw [m15]; exact keep_kk14
    clear keep_kk14
    have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m15]; exact w14_30
    have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m15]; exact w14_34
    have w15_38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m15]; exact w14_38
    have w15_3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m15]; exact w14_3c
    have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m15]; exact w14_40
    have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m15]; exact w14_44
    have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m15]; exact w14_48
    have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m15]; exact w14_4c
    have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m15]; exact w14_50
    clear w14_50 w14_4c w14_48 w14_44 w14_40 w14_3c w14_38 w14_34 w14_30 g14_26 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 K14 a0_14 rk14 s14 c14
    exact .inl ⟨(fun ⟨h0', h1', h2', _⟩ => by exact hq1 h2'), sv_fail_e46 F E15 s15 t15 (fun x hx => (fR15 x hx).trans (fM x hx).symm) V15 hret g15_2 g15_18 hO g15_3 g15_4⟩
  have g14_10 : reg n14 a0 = BitVec.ofNat 32 1 := by rw [a0_14, ite_eq_left hq1]; rfl
  -- 0x9AC: branch, not taken
  obtain ⟨n15, d15, u15⟩ := s14.notTaken E14.self 0x9B0 sv_at_9ac
    (by decide) (by rw [g14_10, s14.zero]; decide)
  have s15 : St n15.mem SV n15 0x9B0 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have m15 : n15.mem = n14.mem := u15.mem
  have fr15 : ∀ x, SvR B x → n15.mem x = n14.mem x := fun x _ => by rw [m15]
  have t15 : Steps n0 n15 := t14.trans (.single d15)
  have fR15 : ∀ x, SvR B x → n15.mem x = M0 x := fun x hx => (fr15 x hx).trans (fR14 x hx)
  have E15 : SvCode n15.mem := E14.fr F fr15
  have V15 : SvSaves B n15.mem v := V14.same m15
  have g15_2 : reg n15 sp = B + 0x21A0 := by rw [u15.regs, g14_2]
  have g15_3 : reg n15 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u15.regs, g14_3]
  have g15_4 : reg n15 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u15.regs, g14_4]
  have g15_10 : reg n15 a0 = BitVec.ofNat 32 0x1 := by rw [u15.regs, g14_10]
  have g15_18 : reg n15 (18 : Fin 32) = out := by rw [u15.regs, g14_18]
  have g15_19 : reg n15 (19 : Fin 32) = bp := by rw [u15.regs, g14_19]
  have g15_20 : reg n15 (20 : Fin 32) = x20 := by rw [u15.regs, g14_20]
  have g15_21 : reg n15 (21 : Fin 32) = x21 := by rw [u15.regs, g14_21]
  have g15_22 : reg n15 (22 : Fin 32) = x22 := by rw [u15.regs, g14_22]
  have g15_23 : reg n15 (23 : Fin 32) = q := by rw [u15.regs, g14_23]
  have g15_24 : reg n15 (24 : Fin 32) = x24 := by rw [u15.regs, g14_24]
  have g15_26 : reg n15 (26 : Fin 32) = x26 := by rw [u15.regs, g14_26]
  have keep_kk15 : SvKeepL B n0.mem n15.mem [] := by rw [m15]; exact keep_kk14
  clear keep_kk14
  have w15_30 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m15]; exact w14_30
  have w15_34 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m15]; exact w14_34
  have w15_38 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m15]; exact w14_38
  have w15_3c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m15]; exact w14_3c
  have w15_40 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m15]; exact w14_40
  have w15_44 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m15]; exact w14_44
  have w15_48 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m15]; exact w14_48
  have w15_4c : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m15]; exact w14_4c
  have w15_50 : memLoad32 n15.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m15]; exact w14_50
  clear w14_50 w14_4c w14_48 w14_44 w14_40 w14_3c w14_38 w14_34 w14_30 g14_26 g14_24 g14_23 g14_22 g14_21 g14_20 g14_19 g14_18 g14_4 g14_3 g14_2 V14 E14 fR14 t14 fr14 K14 a0_14 rk14 s14 c14
  -- 0x9B0
  obtain ⟨n16, c16, u16⟩ := s15.block svDpv9b0 E15.self svDpv9b0_end
    ⟨trivial, trivial⟩
  have m16 : n16.mem = n15.mem := u16.mem
  have s16 : St n16.mem SV n16 0x9B2 (reg n16) := ⟨u16.pc, rfl, fun _ => rfl⟩
  have rb16 : ∀ q, reg n16 q = (runBlock svDpv9b0 (n15.mem, reg n15)).2 q := fun q => by rw [u16.regs]
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
  have g16_23 : reg n16 (23 : Fin 32) = q := by
    rw [rb16, runBlock_reg _ _ _ (23 : Fin 32) s15.zero (by decide), g15_23]
  have g16_24 : reg n16 (24 : Fin 32) = x24 := by
    rw [rb16, runBlock_reg _ _ _ (24 : Fin 32) s15.zero (by decide), g15_24]
  have g16_26 : reg n16 (26 : Fin 32) = x26 := by
    rw [rb16, runBlock_reg _ _ _ (26 : Fin 32) s15.zero (by decide), g15_26]
  have g16_10 : reg n16 a0 = x21 := by
    rw [rb16]; simp +decide only [runBlock, BInstr.run, svDpv9b0, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g15_2, g15_3, g15_4, g15_10, g15_18, g15_19, g15_20, g15_21, g15_22, g15_23, g15_24, g15_26, s15.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk16 : SvKeepL B n0.mem n16.mem [] := by rw [m16]; exact keep_kk15
  clear keep_kk15
  have w16_30 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m16]; exact w15_30
  have w16_34 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m16]; exact w15_34
  have w16_38 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m16]; exact w15_38
  have w16_3c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m16]; exact w15_3c
  have w16_40 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m16]; exact w15_40
  have w16_44 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m16]; exact w15_44
  have w16_48 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m16]; exact w15_48
  have w16_4c : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m16]; exact w15_4c
  have w16_50 : memLoad32 n16.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m16]; exact w15_50
  clear w15_50 w15_4c w15_48 w15_44 w15_40 w15_3c w15_38 w15_34 w15_30 g15_26 g15_24 g15_23 g15_22 g15_21 g15_20 g15_19 g15_18 g15_10 g15_4 g15_3 g15_2 V15 E15 fR15 t15 fr15 m15 s15 u15 d15 g14_10
  -- 0x9B2: lw outside the stack
  obtain ⟨n17, d17, u17⟩ := s16.lw E16.self sv_at_9b2 (off' := 0x9B4) (by decide)
    (by rw [g16_10]; exact ae2p)
  have s17 : St n17.mem SV n17 0x9B4 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
  have m17 : n17.mem = n16.mem := u17.mem
  have fr17 : ∀ x, SvR B x → n17.mem x = n16.mem x := fun x _ => by rw [m17]
  have t17 : Steps n0 n17 := t16.trans (.single d17)
  have fR17 : ∀ x, SvR B x → n17.mem x = M0 x := fun x hx => (fr17 x hx).trans (fR16 x hx)
  have E17 : SvCode n17.mem := E16.fr F fr17
  have V17 : SvSaves B n17.mem v := V16.same m17
  have g17_2 : reg n17 sp = B + 0x21A0 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_2]
  have g17_3 : reg n17 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_3]
  have g17_4 : reg n17 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u17.regs, upd_ne (by decide) (by decide), g16_4]
  have g17_10 : reg n17 a0 = x21 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_10]
  have g17_18 : reg n17 (18 : Fin 32) = out := by rw [u17.regs, upd_ne (by decide) (by decide), g16_18]
  have g17_19 : reg n17 (19 : Fin 32) = bp := by rw [u17.regs, upd_ne (by decide) (by decide), g16_19]
  have g17_20 : reg n17 (20 : Fin 32) = x20 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_20]
  have g17_21 : reg n17 (21 : Fin 32) = x21 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_21]
  have g17_22 : reg n17 (22 : Fin 32) = x22 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_22]
  have g17_23 : reg n17 (23 : Fin 32) = q := by rw [u17.regs, upd_ne (by decide) (by decide), g16_23]
  have g17_24 : reg n17 (24 : Fin 32) = x24 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_24]
  have g17_26 : reg n17 (26 : Fin 32) = x26 := by rw [u17.regs, upd_ne (by decide) (by decide), g16_26]
  have g17_12 : reg n17 a2 = e2p := by
    rw [u17.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g16_10, sv_ld fR16 he2p_in, he2p]
  have keep_kk17 : SvKeepL B n0.mem n17.mem [] := by rw [m17]; exact keep_kk16
  clear keep_kk16
  have w17_30 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m17]; exact w16_30
  have w17_34 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m17]; exact w16_34
  have w17_38 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m17]; exact w16_38
  have w17_3c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m17]; exact w16_3c
  have w17_40 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m17]; exact w16_40
  have w17_44 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m17]; exact w16_44
  have w17_48 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m17]; exact w16_48
  have w17_4c : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m17]; exact w16_4c
  have w17_50 : memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m17]; exact w16_50
  clear w16_50 w16_4c w16_48 w16_44 w16_40 w16_3c w16_38 w16_34 w16_30 g16_10 g16_26 g16_24 g16_23 g16_22 g16_21 g16_20 g16_19 g16_18 g16_4 g16_3 g16_2 V16 E16 fR16 t16 fr16 rb16 s16 m16 u16 c16
  -- 0x9B4: lw outside the stack
  obtain ⟨n18, d18, u18⟩ := s17.lw E17.self sv_at_9b4 (off' := 0x9B6) (by decide)
    (by rw [g17_10]; exact ae2l)
  have s18 : St n18.mem SV n18 0x9B6 (reg n18) := ⟨u18.pc, rfl, fun _ => rfl⟩
  have m18 : n18.mem = n17.mem := u18.mem
  have fr18 : ∀ x, SvR B x → n18.mem x = n17.mem x := fun x _ => by rw [m18]
  have t18 : Steps n0 n18 := t17.trans (.single d18)
  have fR18 : ∀ x, SvR B x → n18.mem x = M0 x := fun x hx => (fr18 x hx).trans (fR17 x hx)
  have E18 : SvCode n18.mem := E17.fr F fr18
  have V18 : SvSaves B n18.mem v := V17.same m18
  have g18_2 : reg n18 sp = B + 0x21A0 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_2]
  have g18_3 : reg n18 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_3]
  have g18_4 : reg n18 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u18.regs, upd_ne (by decide) (by decide), g17_4]
  have g18_10 : reg n18 a0 = x21 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_10]
  have g18_12 : reg n18 a2 = e2p := by rw [u18.regs, upd_ne (by decide) (by decide), g17_12]
  have g18_18 : reg n18 (18 : Fin 32) = out := by rw [u18.regs, upd_ne (by decide) (by decide), g17_18]
  have g18_19 : reg n18 (19 : Fin 32) = bp := by rw [u18.regs, upd_ne (by decide) (by decide), g17_19]
  have g18_20 : reg n18 (20 : Fin 32) = x20 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_20]
  have g18_21 : reg n18 (21 : Fin 32) = x21 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_21]
  have g18_22 : reg n18 (22 : Fin 32) = x22 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_22]
  have g18_23 : reg n18 (23 : Fin 32) = q := by rw [u18.regs, upd_ne (by decide) (by decide), g17_23]
  have g18_24 : reg n18 (24 : Fin 32) = x24 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_24]
  have g18_26 : reg n18 (26 : Fin 32) = x26 := by rw [u18.regs, upd_ne (by decide) (by decide), g17_26]
  have g18_13 : reg n18 a3 = e2l := by
    rw [u18.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g17_10, sv_ld fR17 he2l_in, he2l]
  have keep_kk18 : SvKeepL B n0.mem n18.mem [] := by rw [m18]; exact keep_kk17
  clear keep_kk17
  have w18_30 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m18]; exact w17_30
  have w18_34 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m18]; exact w17_34
  have w18_38 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m18]; exact w17_38
  have w18_3c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m18]; exact w17_3c
  have w18_40 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m18]; exact w17_40
  have w18_44 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m18]; exact w17_44
  have w18_48 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m18]; exact w17_48
  have w18_4c : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m18]; exact w17_4c
  have w18_50 : memLoad32 n18.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m18]; exact w17_50
  clear w17_50 w17_4c w17_48 w17_44 w17_40 w17_3c w17_38 w17_34 w17_30 g17_12 g17_26 g17_24 g17_23 g17_22 g17_21 g17_20 g17_19 g17_18 g17_10 g17_4 g17_3 g17_2 V17 E17 fR17 t17 fr17 m17 s17 u17 d17
  -- 0x9B6: lw
  obtain ⟨n19, d19, u19⟩ := s18.lw E18.self sv_at_9b6 (off' := 0x9B8) (by decide)
    (by rw [g18_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr]; exact sv_al F (by decide) (by decide))
  have s19 : St n19.mem SV n19 0x9B8 (reg n19) := ⟨u19.pc, rfl, fun _ => rfl⟩
  have m19 : n19.mem = n18.mem := u19.mem
  have fr19 : ∀ x, SvR B x → n19.mem x = n18.mem x := fun x _ => by rw [m19]
  have t19 : Steps n0 n19 := t18.trans (.single d19)
  have fR19 : ∀ x, SvR B x → n19.mem x = M0 x := fun x hx => (fr19 x hx).trans (fR18 x hx)
  have E19 : SvCode n19.mem := E18.fr F fr19
  have V19 : SvSaves B n19.mem v := V18.same m19
  have g19_2 : reg n19 sp = B + 0x21A0 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_2]
  have g19_3 : reg n19 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_3]
  have g19_4 : reg n19 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u19.regs, upd_ne (by decide) (by decide), g18_4]
  have g19_12 : reg n19 a2 = e2p := by rw [u19.regs, upd_ne (by decide) (by decide), g18_12]
  have g19_13 : reg n19 a3 = e2l := by rw [u19.regs, upd_ne (by decide) (by decide), g18_13]
  have g19_18 : reg n19 (18 : Fin 32) = out := by rw [u19.regs, upd_ne (by decide) (by decide), g18_18]
  have g19_19 : reg n19 (19 : Fin 32) = bp := by rw [u19.regs, upd_ne (by decide) (by decide), g18_19]
  have g19_20 : reg n19 (20 : Fin 32) = x20 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_20]
  have g19_21 : reg n19 (21 : Fin 32) = x21 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_21]
  have g19_22 : reg n19 (22 : Fin 32) = x22 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_22]
  have g19_23 : reg n19 (23 : Fin 32) = q := by rw [u19.regs, upd_ne (by decide) (by decide), g18_23]
  have g19_24 : reg n19 (24 : Fin 32) = x24 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_24]
  have g19_26 : reg n19 (26 : Fin 32) = x26 := by rw [u19.regs, upd_ne (by decide) (by decide), g18_26]
  have g19_10 : reg n19 a0 = w4c := by
    rw [u19.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g18_2, show B + 0x21A0 + 0x4C = B + 0x21A0 + BitVec.ofNat 32 0x4C by sv_addr, w18_4c]
  have keep_kk19 : SvKeepL B n0.mem n19.mem [] := by rw [m19]; exact keep_kk18
  clear keep_kk18
  have w19_30 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m19]; exact w18_30
  have w19_34 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m19]; exact w18_34
  have w19_38 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m19]; exact w18_38
  have w19_3c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m19]; exact w18_3c
  have w19_40 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m19]; exact w18_40
  have w19_44 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m19]; exact w18_44
  have w19_48 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m19]; exact w18_48
  have w19_4c : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m19]; exact w18_4c
  have w19_50 : memLoad32 n19.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m19]; exact w18_50
  clear w18_50 w18_4c w18_48 w18_44 w18_40 w18_3c w18_38 w18_34 w18_30 g18_13 g18_26 g18_24 g18_23 g18_22 g18_21 g18_20 g18_19 g18_18 g18_12 g18_10 g18_4 g18_3 g18_2 V18 E18 fR18 t18 fr18 m18 s18 u18 d18
  -- 0x9B8: lw
  obtain ⟨n20, d20, u20⟩ := s19.lw E19.self sv_at_9b8 (off' := 0x9BA) (by decide)
    (by rw [g19_2, show B + 0x21A0 + 0x38 = B + 0x21A0 + BitVec.ofNat 32 0x38 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s20 : St n20.mem SV n20 0x9BA (reg n20) := ⟨u20.pc, rfl, fun _ => rfl⟩
  have m20 : n20.mem = n19.mem := u20.mem
  have fr20 : ∀ x, SvR B x → n20.mem x = n19.mem x := fun x _ => by rw [m20]
  have t20 : Steps n0 n20 := t19.trans (.single d20)
  have fR20 : ∀ x, SvR B x → n20.mem x = M0 x := fun x hx => (fr20 x hx).trans (fR19 x hx)
  have E20 : SvCode n20.mem := E19.fr F fr20
  have V20 : SvSaves B n20.mem v := V19.same m20
  have g20_2 : reg n20 sp = B + 0x21A0 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_2]
  have g20_3 : reg n20 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_3]
  have g20_4 : reg n20 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u20.regs, upd_ne (by decide) (by decide), g19_4]
  have g20_10 : reg n20 a0 = w4c := by rw [u20.regs, upd_ne (by decide) (by decide), g19_10]
  have g20_12 : reg n20 a2 = e2p := by rw [u20.regs, upd_ne (by decide) (by decide), g19_12]
  have g20_13 : reg n20 a3 = e2l := by rw [u20.regs, upd_ne (by decide) (by decide), g19_13]
  have g20_18 : reg n20 (18 : Fin 32) = out := by rw [u20.regs, upd_ne (by decide) (by decide), g19_18]
  have g20_19 : reg n20 (19 : Fin 32) = bp := by rw [u20.regs, upd_ne (by decide) (by decide), g19_19]
  have g20_20 : reg n20 (20 : Fin 32) = x20 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_20]
  have g20_21 : reg n20 (21 : Fin 32) = x21 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_21]
  have g20_22 : reg n20 (22 : Fin 32) = x22 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_22]
  have g20_23 : reg n20 (23 : Fin 32) = q := by rw [u20.regs, upd_ne (by decide) (by decide), g19_23]
  have g20_24 : reg n20 (24 : Fin 32) = x24 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_24]
  have g20_26 : reg n20 (26 : Fin 32) = x26 := by rw [u20.regs, upd_ne (by decide) (by decide), g19_26]
  have g20_11 : reg n20 a1 = w38 := by
    rw [u20.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g19_2, show B + 0x21A0 + 0x38 = B + 0x21A0 + BitVec.ofNat 32 0x38 by sv_addr, w19_38]
  have keep_kk20 : SvKeepL B n0.mem n20.mem [] := by rw [m20]; exact keep_kk19
  clear keep_kk19
  have w20_30 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m20]; exact w19_30
  have w20_34 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m20]; exact w19_34
  have w20_38 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m20]; exact w19_38
  have w20_3c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m20]; exact w19_3c
  have w20_40 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m20]; exact w19_40
  have w20_44 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m20]; exact w19_44
  have w20_48 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m20]; exact w19_48
  have w20_4c : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m20]; exact w19_4c
  have w20_50 : memLoad32 n20.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m20]; exact w19_50
  clear w19_50 w19_4c w19_48 w19_44 w19_40 w19_3c w19_38 w19_34 w19_30 g19_10 g19_26 g19_24 g19_23 g19_22 g19_21 g19_20 g19_19 g19_18 g19_13 g19_12 g19_4 g19_3 g19_2 V19 E19 fR19 t19 fr19 m19 s19 u19 d19
  -- 0x9BA: sv_seqEqF
  obtain ⟨n21, c21, s21, rk21, a0_21, K21, fr21⟩ := sv_seqEqF (pl := w38.toNat) (ql := e2l.toNat)
    F E20 s20 sv_at_9ba sv_at_9be (by decide) (by decide) g20_2
    g20_10 (by rw [g20_11, ofNat_toNat_self]) g20_12 (by rw [g20_13, ofNat_toNat_self]) p2_in e2_in
  have t21 : Steps n0 n21 := t20.trans c21
  have fR21 : ∀ x, SvR B x → n21.mem x = M0 x := fun x hx => (fr21 x hx).trans (fR20 x hx)
  have E21 : SvCode n21.mem := E20.fr F fr21
  have V21 : SvSaves B n21.mem v := V20.keepL K21 (by decide)
  rw [sv_mbRo FW fR20 p2_in, sv_mbRo FW fR20 e2_in] at a0_21
  have g21_2 : reg n21 sp = B + 0x21A0 := by rw [rk21 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g20_2]
  have g21_3 : reg n21 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk21 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g20_3]
  have g21_4 : reg n21 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk21 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g20_4]
  have g21_18 : reg n21 (18 : Fin 32) = out := by rw [rk21 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g20_18]
  have g21_19 : reg n21 (19 : Fin 32) = bp := by rw [rk21 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g20_19]
  have g21_20 : reg n21 (20 : Fin 32) = x20 := by rw [rk21 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g20_20]
  have g21_21 : reg n21 (21 : Fin 32) = x21 := by rw [rk21 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g20_21]
  have g21_22 : reg n21 (22 : Fin 32) = x22 := by rw [rk21 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g20_22]
  have g21_23 : reg n21 (23 : Fin 32) = q := by rw [rk21 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g20_23]
  have g21_24 : reg n21 (24 : Fin 32) = x24 := by rw [rk21 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g20_24]
  have g21_26 : reg n21 (26 : Fin 32) = x26 := by rw [rk21 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g20_26]
  have keep_kk21 : SvKeepL B n0.mem n21.mem [] := keep_kk20.trans K21
  clear keep_kk20
  have w21_30 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K21.w32 (by decide) (by decide)).trans w20_30
  have w21_34 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K21.w32 (by decide) (by decide)).trans w20_34
  have w21_38 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K21.w32 (by decide) (by decide)).trans w20_38
  have w21_3c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K21.w32 (by decide) (by decide)).trans w20_3c
  have w21_40 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K21.w32 (by decide) (by decide)).trans w20_40
  have w21_44 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K21.w32 (by decide) (by decide)).trans w20_44
  have w21_48 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K21.w32 (by decide) (by decide)).trans w20_48
  have w21_4c : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K21.w32 (by decide) (by decide)).trans w20_4c
  have w21_50 : memLoad32 n21.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K21.w32 (by decide) (by decide)).trans w20_50
  clear w20_50 w20_4c w20_48 w20_44 w20_40 w20_3c w20_38 w20_34 w20_30 g20_11 g20_26 g20_24 g20_23 g20_22 g20_21 g20_20 g20_19 g20_18 g20_13 g20_12 g20_10 g20_4 g20_3 g20_2 V20 E20 fR20 t20 fr20 m20 s20 u20 d20
  by_cases hq2 : memBytes M0 w4c w38.toNat = memBytes M0 e2p e2l.toNat
  rotate_left
  · have g21_10 : reg n21 a0 = BitVec.ofNat 32 0 := by rw [a0_21, ite_eq_right hq2]; rfl
    -- 0x9C2: branch, taken
    obtain ⟨n22, d22, u22⟩ := s21.taken E21.self 0xE46 sv_at_9c2
      (by decide) (by rw [g21_10, s21.zero]; decide)
    have s22 : St n22.mem SV n22 0xE46 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
    have m22 : n22.mem = n21.mem := u22.mem
    have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
    have t22 : Steps n0 n22 := t21.trans (.single d22)
    have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
    have E22 : SvCode n22.mem := E21.fr F fr22
    have V22 : SvSaves B n22.mem v := V21.same m22
    have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, g21_2]
    have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, g21_3]
    have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, g21_4]
    have g22_10 : reg n22 a0 = BitVec.ofNat 32 0x0 := by rw [u22.regs, g21_10]
    have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, g21_18]
    have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, g21_19]
    have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [u22.regs, g21_20]
    have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, g21_21]
    have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [u22.regs, g21_22]
    have g22_23 : reg n22 (23 : Fin 32) = q := by rw [u22.regs, g21_23]
    have g22_24 : reg n22 (24 : Fin 32) = x24 := by rw [u22.regs, g21_24]
    have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, g21_26]
    have keep_kk22 : SvKeepL B n0.mem n22.mem [] := by rw [m22]; exact keep_kk21
    clear keep_kk21
    have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m22]; exact w21_30
    have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m22]; exact w21_34
    have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m22]; exact w21_38
    have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m22]; exact w21_3c
    have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m22]; exact w21_40
    have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m22]; exact w21_44
    have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m22]; exact w21_48
    have w22_4c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m22]; exact w21_4c
    have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m22]; exact w21_50
    clear w21_50 w21_4c w21_48 w21_44 w21_40 w21_3c w21_38 w21_34 w21_30 g21_26 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 K21 a0_21 rk21 s21 c21
    exact .inl ⟨(fun ⟨h0', h1', h2', h3', _⟩ => by exact hq2 h3'), sv_fail_e46 F E22 s22 t22 (fun x hx => (fR22 x hx).trans (fM x hx).symm) V22 hret g22_2 g22_18 hO g22_3 g22_4⟩
  have g21_10 : reg n21 a0 = BitVec.ofNat 32 1 := by rw [a0_21, ite_eq_left hq2]; rfl
  -- 0x9C2: branch, not taken
  obtain ⟨n22, d22, u22⟩ := s21.notTaken E21.self 0x9C6 sv_at_9c2
    (by decide) (by rw [g21_10, s21.zero]; decide)
  have s22 : St n22.mem SV n22 0x9C6 (reg n22) := ⟨u22.pc, rfl, fun _ => rfl⟩
  have m22 : n22.mem = n21.mem := u22.mem
  have fr22 : ∀ x, SvR B x → n22.mem x = n21.mem x := fun x _ => by rw [m22]
  have t22 : Steps n0 n22 := t21.trans (.single d22)
  have fR22 : ∀ x, SvR B x → n22.mem x = M0 x := fun x hx => (fr22 x hx).trans (fR21 x hx)
  have E22 : SvCode n22.mem := E21.fr F fr22
  have V22 : SvSaves B n22.mem v := V21.same m22
  have g22_2 : reg n22 sp = B + 0x21A0 := by rw [u22.regs, g21_2]
  have g22_3 : reg n22 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u22.regs, g21_3]
  have g22_4 : reg n22 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u22.regs, g21_4]
  have g22_10 : reg n22 a0 = BitVec.ofNat 32 0x1 := by rw [u22.regs, g21_10]
  have g22_18 : reg n22 (18 : Fin 32) = out := by rw [u22.regs, g21_18]
  have g22_19 : reg n22 (19 : Fin 32) = bp := by rw [u22.regs, g21_19]
  have g22_20 : reg n22 (20 : Fin 32) = x20 := by rw [u22.regs, g21_20]
  have g22_21 : reg n22 (21 : Fin 32) = x21 := by rw [u22.regs, g21_21]
  have g22_22 : reg n22 (22 : Fin 32) = x22 := by rw [u22.regs, g21_22]
  have g22_23 : reg n22 (23 : Fin 32) = q := by rw [u22.regs, g21_23]
  have g22_24 : reg n22 (24 : Fin 32) = x24 := by rw [u22.regs, g21_24]
  have g22_26 : reg n22 (26 : Fin 32) = x26 := by rw [u22.regs, g21_26]
  have keep_kk22 : SvKeepL B n0.mem n22.mem [] := by rw [m22]; exact keep_kk21
  clear keep_kk21
  have w22_30 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m22]; exact w21_30
  have w22_34 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m22]; exact w21_34
  have w22_38 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m22]; exact w21_38
  have w22_3c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m22]; exact w21_3c
  have w22_40 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m22]; exact w21_40
  have w22_44 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m22]; exact w21_44
  have w22_48 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m22]; exact w21_48
  have w22_4c : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m22]; exact w21_4c
  have w22_50 : memLoad32 n22.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m22]; exact w21_50
  clear w21_50 w21_4c w21_48 w21_44 w21_40 w21_3c w21_38 w21_34 w21_30 g21_26 g21_24 g21_23 g21_22 g21_21 g21_20 g21_19 g21_18 g21_4 g21_3 g21_2 V21 E21 fR21 t21 fr21 K21 a0_21 rk21 s21 c21
  -- 0x9C6
  obtain ⟨n23, c23, u23⟩ := s22.block svDpv9c6 E22.self svDpv9c6_end
    ⟨trivial, trivial⟩
  have m23 : n23.mem = n22.mem := u23.mem
  have s23 : St n23.mem SV n23 0x9C8 (reg n23) := ⟨u23.pc, rfl, fun _ => rfl⟩
  have rb23 : ∀ q, reg n23 q = (runBlock svDpv9c6 (n22.mem, reg n22)).2 q := fun q => by rw [u23.regs]
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
  have g23_23 : reg n23 (23 : Fin 32) = q := by
    rw [rb23, runBlock_reg _ _ _ (23 : Fin 32) s22.zero (by decide), g22_23]
  have g23_24 : reg n23 (24 : Fin 32) = x24 := by
    rw [rb23, runBlock_reg _ _ _ (24 : Fin 32) s22.zero (by decide), g22_24]
  have g23_26 : reg n23 (26 : Fin 32) = x26 := by
    rw [rb23, runBlock_reg _ _ _ (26 : Fin 32) s22.zero (by decide), g22_26]
  have g23_10 : reg n23 a0 = x21 := by
    rw [rb23]; simp +decide only [runBlock, BInstr.run, svDpv9c6, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g22_2, g22_3, g22_4, g22_10, g22_18, g22_19, g22_20, g22_21, g22_22, g22_23, g22_24, g22_26, s22.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk23 : SvKeepL B n0.mem n23.mem [] := by rw [m23]; exact keep_kk22
  clear keep_kk22
  have w23_30 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m23]; exact w22_30
  have w23_34 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m23]; exact w22_34
  have w23_38 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m23]; exact w22_38
  have w23_3c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m23]; exact w22_3c
  have w23_40 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m23]; exact w22_40
  have w23_44 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m23]; exact w22_44
  have w23_48 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m23]; exact w22_48
  have w23_4c : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m23]; exact w22_4c
  have w23_50 : memLoad32 n23.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m23]; exact w22_50
  clear w22_50 w22_4c w22_48 w22_44 w22_40 w22_3c w22_38 w22_34 w22_30 g22_26 g22_24 g22_23 g22_22 g22_21 g22_20 g22_19 g22_18 g22_10 g22_4 g22_3 g22_2 V22 E22 fR22 t22 fr22 m22 s22 u22 d22 g21_10
  -- 0x9C8: lw outside the stack
  obtain ⟨n24, d24, u24⟩ := s23.lw E23.self sv_at_9c8 (off' := 0x9CA) (by decide)
    (by rw [g23_10]; exact ae3p)
  have s24 : St n24.mem SV n24 0x9CA (reg n24) := ⟨u24.pc, rfl, fun _ => rfl⟩
  have m24 : n24.mem = n23.mem := u24.mem
  have fr24 : ∀ x, SvR B x → n24.mem x = n23.mem x := fun x _ => by rw [m24]
  have t24 : Steps n0 n24 := t23.trans (.single d24)
  have fR24 : ∀ x, SvR B x → n24.mem x = M0 x := fun x hx => (fr24 x hx).trans (fR23 x hx)
  have E24 : SvCode n24.mem := E23.fr F fr24
  have V24 : SvSaves B n24.mem v := V23.same m24
  have g24_2 : reg n24 sp = B + 0x21A0 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_2]
  have g24_3 : reg n24 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_3]
  have g24_4 : reg n24 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u24.regs, upd_ne (by decide) (by decide), g23_4]
  have g24_10 : reg n24 a0 = x21 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_10]
  have g24_18 : reg n24 (18 : Fin 32) = out := by rw [u24.regs, upd_ne (by decide) (by decide), g23_18]
  have g24_19 : reg n24 (19 : Fin 32) = bp := by rw [u24.regs, upd_ne (by decide) (by decide), g23_19]
  have g24_20 : reg n24 (20 : Fin 32) = x20 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_20]
  have g24_21 : reg n24 (21 : Fin 32) = x21 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_21]
  have g24_22 : reg n24 (22 : Fin 32) = x22 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_22]
  have g24_23 : reg n24 (23 : Fin 32) = q := by rw [u24.regs, upd_ne (by decide) (by decide), g23_23]
  have g24_24 : reg n24 (24 : Fin 32) = x24 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_24]
  have g24_26 : reg n24 (26 : Fin 32) = x26 := by rw [u24.regs, upd_ne (by decide) (by decide), g23_26]
  have g24_12 : reg n24 a2 = e3p := by
    rw [u24.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g23_10, sv_ld fR23 he3p_in, he3p]
  have keep_kk24 : SvKeepL B n0.mem n24.mem [] := by rw [m24]; exact keep_kk23
  clear keep_kk23
  have w24_30 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m24]; exact w23_30
  have w24_34 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m24]; exact w23_34
  have w24_38 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m24]; exact w23_38
  have w24_3c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m24]; exact w23_3c
  have w24_40 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m24]; exact w23_40
  have w24_44 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m24]; exact w23_44
  have w24_48 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m24]; exact w23_48
  have w24_4c : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m24]; exact w23_4c
  have w24_50 : memLoad32 n24.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m24]; exact w23_50
  clear w23_50 w23_4c w23_48 w23_44 w23_40 w23_3c w23_38 w23_34 w23_30 g23_10 g23_26 g23_24 g23_23 g23_22 g23_21 g23_20 g23_19 g23_18 g23_4 g23_3 g23_2 V23 E23 fR23 t23 fr23 rb23 s23 m23 u23 c23
  -- 0x9CA: lw outside the stack
  obtain ⟨n25, d25, u25⟩ := s24.lw E24.self sv_at_9ca (off' := 0x9CC) (by decide)
    (by rw [g24_10]; exact ae3l)
  have s25 : St n25.mem SV n25 0x9CC (reg n25) := ⟨u25.pc, rfl, fun _ => rfl⟩
  have m25 : n25.mem = n24.mem := u25.mem
  have fr25 : ∀ x, SvR B x → n25.mem x = n24.mem x := fun x _ => by rw [m25]
  have t25 : Steps n0 n25 := t24.trans (.single d25)
  have fR25 : ∀ x, SvR B x → n25.mem x = M0 x := fun x hx => (fr25 x hx).trans (fR24 x hx)
  have E25 : SvCode n25.mem := E24.fr F fr25
  have V25 : SvSaves B n25.mem v := V24.same m25
  have g25_2 : reg n25 sp = B + 0x21A0 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_2]
  have g25_3 : reg n25 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_3]
  have g25_4 : reg n25 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u25.regs, upd_ne (by decide) (by decide), g24_4]
  have g25_10 : reg n25 a0 = x21 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_10]
  have g25_12 : reg n25 a2 = e3p := by rw [u25.regs, upd_ne (by decide) (by decide), g24_12]
  have g25_18 : reg n25 (18 : Fin 32) = out := by rw [u25.regs, upd_ne (by decide) (by decide), g24_18]
  have g25_19 : reg n25 (19 : Fin 32) = bp := by rw [u25.regs, upd_ne (by decide) (by decide), g24_19]
  have g25_20 : reg n25 (20 : Fin 32) = x20 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_20]
  have g25_21 : reg n25 (21 : Fin 32) = x21 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_21]
  have g25_22 : reg n25 (22 : Fin 32) = x22 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_22]
  have g25_23 : reg n25 (23 : Fin 32) = q := by rw [u25.regs, upd_ne (by decide) (by decide), g24_23]
  have g25_24 : reg n25 (24 : Fin 32) = x24 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_24]
  have g25_26 : reg n25 (26 : Fin 32) = x26 := by rw [u25.regs, upd_ne (by decide) (by decide), g24_26]
  have g25_13 : reg n25 a3 = e3l := by
    rw [u25.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g24_10, sv_ld fR24 he3l_in, he3l]
  have keep_kk25 : SvKeepL B n0.mem n25.mem [] := by rw [m25]; exact keep_kk24
  clear keep_kk24
  have w25_30 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m25]; exact w24_30
  have w25_34 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m25]; exact w24_34
  have w25_38 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m25]; exact w24_38
  have w25_3c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m25]; exact w24_3c
  have w25_40 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m25]; exact w24_40
  have w25_44 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m25]; exact w24_44
  have w25_48 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m25]; exact w24_48
  have w25_4c : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m25]; exact w24_4c
  have w25_50 : memLoad32 n25.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m25]; exact w24_50
  clear w24_50 w24_4c w24_48 w24_44 w24_40 w24_3c w24_38 w24_34 w24_30 g24_12 g24_26 g24_24 g24_23 g24_22 g24_21 g24_20 g24_19 g24_18 g24_10 g24_4 g24_3 g24_2 V24 E24 fR24 t24 fr24 m24 s24 u24 d24
  -- 0x9CC: lw
  obtain ⟨n26, d26, u26⟩ := s25.lw E25.self sv_at_9cc (off' := 0x9CE) (by decide)
    (by rw [g25_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s26 : St n26.mem SV n26 0x9CE (reg n26) := ⟨u26.pc, rfl, fun _ => rfl⟩
  have m26 : n26.mem = n25.mem := u26.mem
  have fr26 : ∀ x, SvR B x → n26.mem x = n25.mem x := fun x _ => by rw [m26]
  have t26 : Steps n0 n26 := t25.trans (.single d26)
  have fR26 : ∀ x, SvR B x → n26.mem x = M0 x := fun x hx => (fr26 x hx).trans (fR25 x hx)
  have E26 : SvCode n26.mem := E25.fr F fr26
  have V26 : SvSaves B n26.mem v := V25.same m26
  have g26_2 : reg n26 sp = B + 0x21A0 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_2]
  have g26_3 : reg n26 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_3]
  have g26_4 : reg n26 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u26.regs, upd_ne (by decide) (by decide), g25_4]
  have g26_12 : reg n26 a2 = e3p := by rw [u26.regs, upd_ne (by decide) (by decide), g25_12]
  have g26_13 : reg n26 a3 = e3l := by rw [u26.regs, upd_ne (by decide) (by decide), g25_13]
  have g26_18 : reg n26 (18 : Fin 32) = out := by rw [u26.regs, upd_ne (by decide) (by decide), g25_18]
  have g26_19 : reg n26 (19 : Fin 32) = bp := by rw [u26.regs, upd_ne (by decide) (by decide), g25_19]
  have g26_20 : reg n26 (20 : Fin 32) = x20 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_20]
  have g26_21 : reg n26 (21 : Fin 32) = x21 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_21]
  have g26_22 : reg n26 (22 : Fin 32) = x22 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_22]
  have g26_23 : reg n26 (23 : Fin 32) = q := by rw [u26.regs, upd_ne (by decide) (by decide), g25_23]
  have g26_24 : reg n26 (24 : Fin 32) = x24 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_24]
  have g26_26 : reg n26 (26 : Fin 32) = x26 := by rw [u26.regs, upd_ne (by decide) (by decide), g25_26]
  have g26_10 : reg n26 a0 = w48 := by
    rw [u26.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g25_2, show B + 0x21A0 + 0x48 = B + 0x21A0 + BitVec.ofNat 32 0x48 by sv_addr, w25_48]
  have keep_kk26 : SvKeepL B n0.mem n26.mem [] := by rw [m26]; exact keep_kk25
  clear keep_kk25
  have w26_30 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m26]; exact w25_30
  have w26_34 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m26]; exact w25_34
  have w26_38 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m26]; exact w25_38
  have w26_3c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m26]; exact w25_3c
  have w26_40 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m26]; exact w25_40
  have w26_44 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m26]; exact w25_44
  have w26_48 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m26]; exact w25_48
  have w26_4c : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m26]; exact w25_4c
  have w26_50 : memLoad32 n26.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m26]; exact w25_50
  clear w25_50 w25_4c w25_48 w25_44 w25_40 w25_3c w25_38 w25_34 w25_30 g25_13 g25_26 g25_24 g25_23 g25_22 g25_21 g25_20 g25_19 g25_18 g25_12 g25_10 g25_4 g25_3 g25_2 V25 E25 fR25 t25 fr25 m25 s25 u25 d25
  -- 0x9CE: lw
  obtain ⟨n27, d27, u27⟩ := s26.lw E26.self sv_at_9ce (off' := 0x9D0) (by decide)
    (by rw [g26_2, show B + 0x21A0 + 0x34 = B + 0x21A0 + BitVec.ofNat 32 0x34 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s27 : St n27.mem SV n27 0x9D0 (reg n27) := ⟨u27.pc, rfl, fun _ => rfl⟩
  have m27 : n27.mem = n26.mem := u27.mem
  have fr27 : ∀ x, SvR B x → n27.mem x = n26.mem x := fun x _ => by rw [m27]
  have t27 : Steps n0 n27 := t26.trans (.single d27)
  have fR27 : ∀ x, SvR B x → n27.mem x = M0 x := fun x hx => (fr27 x hx).trans (fR26 x hx)
  have E27 : SvCode n27.mem := E26.fr F fr27
  have V27 : SvSaves B n27.mem v := V26.same m27
  have g27_2 : reg n27 sp = B + 0x21A0 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_2]
  have g27_3 : reg n27 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_3]
  have g27_4 : reg n27 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u27.regs, upd_ne (by decide) (by decide), g26_4]
  have g27_10 : reg n27 a0 = w48 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_10]
  have g27_12 : reg n27 a2 = e3p := by rw [u27.regs, upd_ne (by decide) (by decide), g26_12]
  have g27_13 : reg n27 a3 = e3l := by rw [u27.regs, upd_ne (by decide) (by decide), g26_13]
  have g27_18 : reg n27 (18 : Fin 32) = out := by rw [u27.regs, upd_ne (by decide) (by decide), g26_18]
  have g27_19 : reg n27 (19 : Fin 32) = bp := by rw [u27.regs, upd_ne (by decide) (by decide), g26_19]
  have g27_20 : reg n27 (20 : Fin 32) = x20 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_20]
  have g27_21 : reg n27 (21 : Fin 32) = x21 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_21]
  have g27_22 : reg n27 (22 : Fin 32) = x22 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_22]
  have g27_23 : reg n27 (23 : Fin 32) = q := by rw [u27.regs, upd_ne (by decide) (by decide), g26_23]
  have g27_24 : reg n27 (24 : Fin 32) = x24 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_24]
  have g27_26 : reg n27 (26 : Fin 32) = x26 := by rw [u27.regs, upd_ne (by decide) (by decide), g26_26]
  have g27_11 : reg n27 a1 = w34 := by
    rw [u27.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g26_2, show B + 0x21A0 + 0x34 = B + 0x21A0 + BitVec.ofNat 32 0x34 by sv_addr, w26_34]
  have keep_kk27 : SvKeepL B n0.mem n27.mem [] := by rw [m27]; exact keep_kk26
  clear keep_kk26
  have w27_30 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m27]; exact w26_30
  have w27_34 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m27]; exact w26_34
  have w27_38 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m27]; exact w26_38
  have w27_3c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m27]; exact w26_3c
  have w27_40 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m27]; exact w26_40
  have w27_44 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m27]; exact w26_44
  have w27_48 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m27]; exact w26_48
  have w27_4c : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m27]; exact w26_4c
  have w27_50 : memLoad32 n27.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m27]; exact w26_50
  clear w26_50 w26_4c w26_48 w26_44 w26_40 w26_3c w26_38 w26_34 w26_30 g26_10 g26_26 g26_24 g26_23 g26_22 g26_21 g26_20 g26_19 g26_18 g26_13 g26_12 g26_4 g26_3 g26_2 V26 E26 fR26 t26 fr26 m26 s26 u26 d26
  -- 0x9D0: sv_seqEqF
  obtain ⟨n28, c28, s28, rk28, a0_28, K28, fr28⟩ := sv_seqEqF (pl := w34.toNat) (ql := e3l.toNat)
    F E27 s27 sv_at_9d0 sv_at_9d4 (by decide) (by decide) g27_2
    g27_10 (by rw [g27_11, ofNat_toNat_self]) g27_12 (by rw [g27_13, ofNat_toNat_self]) p3_in e3_in
  have t28 : Steps n0 n28 := t27.trans c28
  have fR28 : ∀ x, SvR B x → n28.mem x = M0 x := fun x hx => (fr28 x hx).trans (fR27 x hx)
  have E28 : SvCode n28.mem := E27.fr F fr28
  have V28 : SvSaves B n28.mem v := V27.keepL K28 (by decide)
  rw [sv_mbRo FW fR27 p3_in, sv_mbRo FW fR27 e3_in] at a0_28
  have g28_2 : reg n28 sp = B + 0x21A0 := by rw [rk28 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_2]
  have g28_3 : reg n28 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk28 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_3]
  have g28_4 : reg n28 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk28 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_4]
  have g28_18 : reg n28 (18 : Fin 32) = out := by rw [rk28 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_18]
  have g28_19 : reg n28 (19 : Fin 32) = bp := by rw [rk28 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_19]
  have g28_20 : reg n28 (20 : Fin 32) = x20 := by rw [rk28 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_20]
  have g28_21 : reg n28 (21 : Fin 32) = x21 := by rw [rk28 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_21]
  have g28_22 : reg n28 (22 : Fin 32) = x22 := by rw [rk28 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_22]
  have g28_23 : reg n28 (23 : Fin 32) = q := by rw [rk28 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_23]
  have g28_24 : reg n28 (24 : Fin 32) = x24 := by rw [rk28 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_24]
  have g28_26 : reg n28 (26 : Fin 32) = x26 := by rw [rk28 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g27_26]
  have keep_kk28 : SvKeepL B n0.mem n28.mem [] := keep_kk27.trans K28
  clear keep_kk27
  have w28_30 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K28.w32 (by decide) (by decide)).trans w27_30
  have w28_34 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K28.w32 (by decide) (by decide)).trans w27_34
  have w28_38 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K28.w32 (by decide) (by decide)).trans w27_38
  have w28_3c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K28.w32 (by decide) (by decide)).trans w27_3c
  have w28_40 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K28.w32 (by decide) (by decide)).trans w27_40
  have w28_44 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K28.w32 (by decide) (by decide)).trans w27_44
  have w28_48 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K28.w32 (by decide) (by decide)).trans w27_48
  have w28_4c : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K28.w32 (by decide) (by decide)).trans w27_4c
  have w28_50 : memLoad32 n28.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K28.w32 (by decide) (by decide)).trans w27_50
  clear w27_50 w27_4c w27_48 w27_44 w27_40 w27_3c w27_38 w27_34 w27_30 g27_11 g27_26 g27_24 g27_23 g27_22 g27_21 g27_20 g27_19 g27_18 g27_13 g27_12 g27_10 g27_4 g27_3 g27_2 V27 E27 fR27 t27 fr27 m27 s27 u27 d27
  by_cases hq3 : memBytes M0 w48 w34.toNat = memBytes M0 e3p e3l.toNat
  rotate_left
  · have g28_10 : reg n28 a0 = BitVec.ofNat 32 0 := by rw [a0_28, ite_eq_right hq3]; rfl
    -- 0x9D8: branch, taken
    obtain ⟨n29, d29, u29⟩ := s28.taken E28.self 0xE46 sv_at_9d8
      (by decide) (by rw [g28_10, s28.zero]; decide)
    have s29 : St n29.mem SV n29 0xE46 (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
    have m29 : n29.mem = n28.mem := u29.mem
    have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
    have t29 : Steps n0 n29 := t28.trans (.single d29)
    have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
    have E29 : SvCode n29.mem := E28.fr F fr29
    have V29 : SvSaves B n29.mem v := V28.same m29
    have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, g28_2]
    have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, g28_3]
    have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, g28_4]
    have g29_10 : reg n29 a0 = BitVec.ofNat 32 0x0 := by rw [u29.regs, g28_10]
    have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, g28_18]
    have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, g28_19]
    have g29_20 : reg n29 (20 : Fin 32) = x20 := by rw [u29.regs, g28_20]
    have g29_21 : reg n29 (21 : Fin 32) = x21 := by rw [u29.regs, g28_21]
    have g29_22 : reg n29 (22 : Fin 32) = x22 := by rw [u29.regs, g28_22]
    have g29_23 : reg n29 (23 : Fin 32) = q := by rw [u29.regs, g28_23]
    have g29_24 : reg n29 (24 : Fin 32) = x24 := by rw [u29.regs, g28_24]
    have g29_26 : reg n29 (26 : Fin 32) = x26 := by rw [u29.regs, g28_26]
    have keep_kk29 : SvKeepL B n0.mem n29.mem [] := by rw [m29]; exact keep_kk28
    clear keep_kk28
    have w29_30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m29]; exact w28_30
    have w29_34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m29]; exact w28_34
    have w29_38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m29]; exact w28_38
    have w29_3c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m29]; exact w28_3c
    have w29_40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m29]; exact w28_40
    have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m29]; exact w28_44
    have w29_48 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m29]; exact w28_48
    have w29_4c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m29]; exact w28_4c
    have w29_50 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m29]; exact w28_50
    clear w28_50 w28_4c w28_48 w28_44 w28_40 w28_3c w28_38 w28_34 w28_30 g28_26 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 K28 a0_28 rk28 s28 c28
    exact .inl ⟨(fun ⟨h0', h1', h2', h3', h4', _⟩ => by exact hq3 h4'), sv_fail_e46 F E29 s29 t29 (fun x hx => (fR29 x hx).trans (fM x hx).symm) V29 hret g29_2 g29_18 hO g29_3 g29_4⟩
  have g28_10 : reg n28 a0 = BitVec.ofNat 32 1 := by rw [a0_28, ite_eq_left hq3]; rfl
  -- 0x9D8: branch, not taken
  obtain ⟨n29, d29, u29⟩ := s28.notTaken E28.self 0x9DC sv_at_9d8
    (by decide) (by rw [g28_10, s28.zero]; decide)
  have s29 : St n29.mem SV n29 0x9DC (reg n29) := ⟨u29.pc, rfl, fun _ => rfl⟩
  have m29 : n29.mem = n28.mem := u29.mem
  have fr29 : ∀ x, SvR B x → n29.mem x = n28.mem x := fun x _ => by rw [m29]
  have t29 : Steps n0 n29 := t28.trans (.single d29)
  have fR29 : ∀ x, SvR B x → n29.mem x = M0 x := fun x hx => (fr29 x hx).trans (fR28 x hx)
  have E29 : SvCode n29.mem := E28.fr F fr29
  have V29 : SvSaves B n29.mem v := V28.same m29
  have g29_2 : reg n29 sp = B + 0x21A0 := by rw [u29.regs, g28_2]
  have g29_3 : reg n29 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u29.regs, g28_3]
  have g29_4 : reg n29 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u29.regs, g28_4]
  have g29_10 : reg n29 a0 = BitVec.ofNat 32 0x1 := by rw [u29.regs, g28_10]
  have g29_18 : reg n29 (18 : Fin 32) = out := by rw [u29.regs, g28_18]
  have g29_19 : reg n29 (19 : Fin 32) = bp := by rw [u29.regs, g28_19]
  have g29_20 : reg n29 (20 : Fin 32) = x20 := by rw [u29.regs, g28_20]
  have g29_21 : reg n29 (21 : Fin 32) = x21 := by rw [u29.regs, g28_21]
  have g29_22 : reg n29 (22 : Fin 32) = x22 := by rw [u29.regs, g28_22]
  have g29_23 : reg n29 (23 : Fin 32) = q := by rw [u29.regs, g28_23]
  have g29_24 : reg n29 (24 : Fin 32) = x24 := by rw [u29.regs, g28_24]
  have g29_26 : reg n29 (26 : Fin 32) = x26 := by rw [u29.regs, g28_26]
  have keep_kk29 : SvKeepL B n0.mem n29.mem [] := by rw [m29]; exact keep_kk28
  clear keep_kk28
  have w29_30 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m29]; exact w28_30
  have w29_34 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m29]; exact w28_34
  have w29_38 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m29]; exact w28_38
  have w29_3c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m29]; exact w28_3c
  have w29_40 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m29]; exact w28_40
  have w29_44 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m29]; exact w28_44
  have w29_48 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m29]; exact w28_48
  have w29_4c : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m29]; exact w28_4c
  have w29_50 : memLoad32 n29.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m29]; exact w28_50
  clear w28_50 w28_4c w28_48 w28_44 w28_40 w28_3c w28_38 w28_34 w28_30 g28_26 g28_24 g28_23 g28_22 g28_21 g28_20 g28_19 g28_18 g28_4 g28_3 g28_2 V28 E28 fR28 t28 fr28 K28 a0_28 rk28 s28 c28
  -- 0x9DC
  obtain ⟨n30, c30, u30⟩ := s29.block svDpv9dc E29.self svDpv9dc_end
    ⟨trivial, trivial⟩
  have m30 : n30.mem = n29.mem := u30.mem
  have s30 : St n30.mem SV n30 0x9DE (reg n30) := ⟨u30.pc, rfl, fun _ => rfl⟩
  have rb30 : ∀ q, reg n30 q = (runBlock svDpv9dc (n29.mem, reg n29)).2 q := fun q => by rw [u30.regs]
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
  have g30_18 : reg n30 (18 : Fin 32) = out := by
    rw [rb30, runBlock_reg _ _ _ (18 : Fin 32) s29.zero (by decide), g29_18]
  have g30_19 : reg n30 (19 : Fin 32) = bp := by
    rw [rb30, runBlock_reg _ _ _ (19 : Fin 32) s29.zero (by decide), g29_19]
  have g30_20 : reg n30 (20 : Fin 32) = x20 := by
    rw [rb30, runBlock_reg _ _ _ (20 : Fin 32) s29.zero (by decide), g29_20]
  have g30_21 : reg n30 (21 : Fin 32) = x21 := by
    rw [rb30, runBlock_reg _ _ _ (21 : Fin 32) s29.zero (by decide), g29_21]
  have g30_22 : reg n30 (22 : Fin 32) = x22 := by
    rw [rb30, runBlock_reg _ _ _ (22 : Fin 32) s29.zero (by decide), g29_22]
  have g30_23 : reg n30 (23 : Fin 32) = q := by
    rw [rb30, runBlock_reg _ _ _ (23 : Fin 32) s29.zero (by decide), g29_23]
  have g30_24 : reg n30 (24 : Fin 32) = x24 := by
    rw [rb30, runBlock_reg _ _ _ (24 : Fin 32) s29.zero (by decide), g29_24]
  have g30_26 : reg n30 (26 : Fin 32) = x26 := by
    rw [rb30, runBlock_reg _ _ _ (26 : Fin 32) s29.zero (by decide), g29_26]
  have g30_10 : reg n30 a0 = x21 := by
    rw [rb30]; simp +decide only [runBlock, BInstr.run, svDpv9dc, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g29_2, g29_3, g29_4, g29_10, g29_18, g29_19, g29_20, g29_21, g29_22, g29_23, g29_24, g29_26, s29.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk30 : SvKeepL B n0.mem n30.mem [] := by rw [m30]; exact keep_kk29
  clear keep_kk29
  have w30_30 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m30]; exact w29_30
  have w30_34 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m30]; exact w29_34
  have w30_38 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m30]; exact w29_38
  have w30_3c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m30]; exact w29_3c
  have w30_40 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m30]; exact w29_40
  have w30_44 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m30]; exact w29_44
  have w30_48 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m30]; exact w29_48
  have w30_4c : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m30]; exact w29_4c
  have w30_50 : memLoad32 n30.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m30]; exact w29_50
  clear w29_50 w29_4c w29_48 w29_44 w29_40 w29_3c w29_38 w29_34 w29_30 g29_26 g29_24 g29_23 g29_22 g29_21 g29_20 g29_19 g29_18 g29_10 g29_4 g29_3 g29_2 V29 E29 fR29 t29 fr29 m29 s29 u29 d29 g28_10
  -- 0x9DE: lw outside the stack
  obtain ⟨n31, d31, u31⟩ := s30.lw E30.self sv_at_9de (off' := 0x9E0) (by decide)
    (by rw [g30_10]; exact ae4p)
  have s31 : St n31.mem SV n31 0x9E0 (reg n31) := ⟨u31.pc, rfl, fun _ => rfl⟩
  have m31 : n31.mem = n30.mem := u31.mem
  have fr31 : ∀ x, SvR B x → n31.mem x = n30.mem x := fun x _ => by rw [m31]
  have t31 : Steps n0 n31 := t30.trans (.single d31)
  have fR31 : ∀ x, SvR B x → n31.mem x = M0 x := fun x hx => (fr31 x hx).trans (fR30 x hx)
  have E31 : SvCode n31.mem := E30.fr F fr31
  have V31 : SvSaves B n31.mem v := V30.same m31
  have g31_2 : reg n31 sp = B + 0x21A0 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_2]
  have g31_3 : reg n31 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_3]
  have g31_4 : reg n31 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u31.regs, upd_ne (by decide) (by decide), g30_4]
  have g31_10 : reg n31 a0 = x21 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_10]
  have g31_18 : reg n31 (18 : Fin 32) = out := by rw [u31.regs, upd_ne (by decide) (by decide), g30_18]
  have g31_19 : reg n31 (19 : Fin 32) = bp := by rw [u31.regs, upd_ne (by decide) (by decide), g30_19]
  have g31_20 : reg n31 (20 : Fin 32) = x20 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_20]
  have g31_21 : reg n31 (21 : Fin 32) = x21 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_21]
  have g31_22 : reg n31 (22 : Fin 32) = x22 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_22]
  have g31_23 : reg n31 (23 : Fin 32) = q := by rw [u31.regs, upd_ne (by decide) (by decide), g30_23]
  have g31_24 : reg n31 (24 : Fin 32) = x24 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_24]
  have g31_26 : reg n31 (26 : Fin 32) = x26 := by rw [u31.regs, upd_ne (by decide) (by decide), g30_26]
  have g31_12 : reg n31 a2 = e4p := by
    rw [u31.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g30_10, sv_ld fR30 he4p_in, he4p]
  have keep_kk31 : SvKeepL B n0.mem n31.mem [] := by rw [m31]; exact keep_kk30
  clear keep_kk30
  have w31_30 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m31]; exact w30_30
  have w31_34 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m31]; exact w30_34
  have w31_38 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m31]; exact w30_38
  have w31_3c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m31]; exact w30_3c
  have w31_40 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m31]; exact w30_40
  have w31_44 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m31]; exact w30_44
  have w31_48 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m31]; exact w30_48
  have w31_4c : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m31]; exact w30_4c
  have w31_50 : memLoad32 n31.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m31]; exact w30_50
  clear w30_50 w30_4c w30_48 w30_44 w30_40 w30_3c w30_38 w30_34 w30_30 g30_10 g30_26 g30_24 g30_23 g30_22 g30_21 g30_20 g30_19 g30_18 g30_4 g30_3 g30_2 V30 E30 fR30 t30 fr30 rb30 s30 m30 u30 c30
  -- 0x9E0: lw outside the stack
  obtain ⟨n32, d32, u32⟩ := s31.lw E31.self sv_at_9e0 (off' := 0x9E2) (by decide)
    (by rw [g31_10]; exact ae4l)
  have s32 : St n32.mem SV n32 0x9E2 (reg n32) := ⟨u32.pc, rfl, fun _ => rfl⟩
  have m32 : n32.mem = n31.mem := u32.mem
  have fr32 : ∀ x, SvR B x → n32.mem x = n31.mem x := fun x _ => by rw [m32]
  have t32 : Steps n0 n32 := t31.trans (.single d32)
  have fR32 : ∀ x, SvR B x → n32.mem x = M0 x := fun x hx => (fr32 x hx).trans (fR31 x hx)
  have E32 : SvCode n32.mem := E31.fr F fr32
  have V32 : SvSaves B n32.mem v := V31.same m32
  have g32_2 : reg n32 sp = B + 0x21A0 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_2]
  have g32_3 : reg n32 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_3]
  have g32_4 : reg n32 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u32.regs, upd_ne (by decide) (by decide), g31_4]
  have g32_10 : reg n32 a0 = x21 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_10]
  have g32_12 : reg n32 a2 = e4p := by rw [u32.regs, upd_ne (by decide) (by decide), g31_12]
  have g32_18 : reg n32 (18 : Fin 32) = out := by rw [u32.regs, upd_ne (by decide) (by decide), g31_18]
  have g32_19 : reg n32 (19 : Fin 32) = bp := by rw [u32.regs, upd_ne (by decide) (by decide), g31_19]
  have g32_20 : reg n32 (20 : Fin 32) = x20 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_20]
  have g32_21 : reg n32 (21 : Fin 32) = x21 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_21]
  have g32_22 : reg n32 (22 : Fin 32) = x22 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_22]
  have g32_23 : reg n32 (23 : Fin 32) = q := by rw [u32.regs, upd_ne (by decide) (by decide), g31_23]
  have g32_24 : reg n32 (24 : Fin 32) = x24 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_24]
  have g32_26 : reg n32 (26 : Fin 32) = x26 := by rw [u32.regs, upd_ne (by decide) (by decide), g31_26]
  have g32_13 : reg n32 a3 = e4l := by
    rw [u32.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g31_10, sv_ld fR31 he4l_in, he4l]
  have keep_kk32 : SvKeepL B n0.mem n32.mem [] := by rw [m32]; exact keep_kk31
  clear keep_kk31
  have w32_30 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m32]; exact w31_30
  have w32_34 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m32]; exact w31_34
  have w32_38 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m32]; exact w31_38
  have w32_3c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m32]; exact w31_3c
  have w32_40 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m32]; exact w31_40
  have w32_44 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m32]; exact w31_44
  have w32_48 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m32]; exact w31_48
  have w32_4c : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m32]; exact w31_4c
  have w32_50 : memLoad32 n32.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m32]; exact w31_50
  clear w31_50 w31_4c w31_48 w31_44 w31_40 w31_3c w31_38 w31_34 w31_30 g31_12 g31_26 g31_24 g31_23 g31_22 g31_21 g31_20 g31_19 g31_18 g31_10 g31_4 g31_3 g31_2 V31 E31 fR31 t31 fr31 m31 s31 u31 d31
  -- 0x9E2: lw
  obtain ⟨n33, d33, u33⟩ := s32.lw E32.self sv_at_9e2 (off' := 0x9E4) (by decide)
    (by rw [g32_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s33 : St n33.mem SV n33 0x9E4 (reg n33) := ⟨u33.pc, rfl, fun _ => rfl⟩
  have m33 : n33.mem = n32.mem := u33.mem
  have fr33 : ∀ x, SvR B x → n33.mem x = n32.mem x := fun x _ => by rw [m33]
  have t33 : Steps n0 n33 := t32.trans (.single d33)
  have fR33 : ∀ x, SvR B x → n33.mem x = M0 x := fun x hx => (fr33 x hx).trans (fR32 x hx)
  have E33 : SvCode n33.mem := E32.fr F fr33
  have V33 : SvSaves B n33.mem v := V32.same m33
  have g33_2 : reg n33 sp = B + 0x21A0 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_2]
  have g33_3 : reg n33 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u33.regs, upd_ne (by decide) (by decide), g32_3]
  have g33_4 : reg n33 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u33.regs, upd_ne (by decide) (by decide), g32_4]
  have g33_12 : reg n33 a2 = e4p := by rw [u33.regs, upd_ne (by decide) (by decide), g32_12]
  have g33_13 : reg n33 a3 = e4l := by rw [u33.regs, upd_ne (by decide) (by decide), g32_13]
  have g33_18 : reg n33 (18 : Fin 32) = out := by rw [u33.regs, upd_ne (by decide) (by decide), g32_18]
  have g33_19 : reg n33 (19 : Fin 32) = bp := by rw [u33.regs, upd_ne (by decide) (by decide), g32_19]
  have g33_20 : reg n33 (20 : Fin 32) = x20 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_20]
  have g33_21 : reg n33 (21 : Fin 32) = x21 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_21]
  have g33_22 : reg n33 (22 : Fin 32) = x22 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_22]
  have g33_23 : reg n33 (23 : Fin 32) = q := by rw [u33.regs, upd_ne (by decide) (by decide), g32_23]
  have g33_24 : reg n33 (24 : Fin 32) = x24 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_24]
  have g33_26 : reg n33 (26 : Fin 32) = x26 := by rw [u33.regs, upd_ne (by decide) (by decide), g32_26]
  have g33_10 : reg n33 a0 = w44 := by
    rw [u33.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g32_2, show B + 0x21A0 + 0x44 = B + 0x21A0 + BitVec.ofNat 32 0x44 by sv_addr, w32_44]
  have keep_kk33 : SvKeepL B n0.mem n33.mem [] := by rw [m33]; exact keep_kk32
  clear keep_kk32
  have w33_30 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m33]; exact w32_30
  have w33_34 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m33]; exact w32_34
  have w33_38 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m33]; exact w32_38
  have w33_3c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m33]; exact w32_3c
  have w33_40 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m33]; exact w32_40
  have w33_44 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m33]; exact w32_44
  have w33_48 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m33]; exact w32_48
  have w33_4c : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m33]; exact w32_4c
  have w33_50 : memLoad32 n33.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m33]; exact w32_50
  clear w32_50 w32_4c w32_48 w32_44 w32_40 w32_3c w32_38 w32_34 w32_30 g32_13 g32_26 g32_24 g32_23 g32_22 g32_21 g32_20 g32_19 g32_18 g32_12 g32_10 g32_4 g32_3 g32_2 V32 E32 fR32 t32 fr32 m32 s32 u32 d32
  -- 0x9E4: lw
  obtain ⟨n34, d34, u34⟩ := s33.lw E33.self sv_at_9e4 (off' := 0x9E6) (by decide)
    (by rw [g33_2, show B + 0x21A0 + 0x30 = B + 0x21A0 + BitVec.ofNat 32 0x30 by sv_addr]; exact sv_al F (by decide) (by decide))
  have s34 : St n34.mem SV n34 0x9E6 (reg n34) := ⟨u34.pc, rfl, fun _ => rfl⟩
  have m34 : n34.mem = n33.mem := u34.mem
  have fr34 : ∀ x, SvR B x → n34.mem x = n33.mem x := fun x _ => by rw [m34]
  have t34 : Steps n0 n34 := t33.trans (.single d34)
  have fR34 : ∀ x, SvR B x → n34.mem x = M0 x := fun x hx => (fr34 x hx).trans (fR33 x hx)
  have E34 : SvCode n34.mem := E33.fr F fr34
  have V34 : SvSaves B n34.mem v := V33.same m34
  have g34_2 : reg n34 sp = B + 0x21A0 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_2]
  have g34_3 : reg n34 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_3]
  have g34_4 : reg n34 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u34.regs, upd_ne (by decide) (by decide), g33_4]
  have g34_10 : reg n34 a0 = w44 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_10]
  have g34_12 : reg n34 a2 = e4p := by rw [u34.regs, upd_ne (by decide) (by decide), g33_12]
  have g34_13 : reg n34 a3 = e4l := by rw [u34.regs, upd_ne (by decide) (by decide), g33_13]
  have g34_18 : reg n34 (18 : Fin 32) = out := by rw [u34.regs, upd_ne (by decide) (by decide), g33_18]
  have g34_19 : reg n34 (19 : Fin 32) = bp := by rw [u34.regs, upd_ne (by decide) (by decide), g33_19]
  have g34_20 : reg n34 (20 : Fin 32) = x20 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_20]
  have g34_21 : reg n34 (21 : Fin 32) = x21 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_21]
  have g34_22 : reg n34 (22 : Fin 32) = x22 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_22]
  have g34_23 : reg n34 (23 : Fin 32) = q := by rw [u34.regs, upd_ne (by decide) (by decide), g33_23]
  have g34_24 : reg n34 (24 : Fin 32) = x24 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_24]
  have g34_26 : reg n34 (26 : Fin 32) = x26 := by rw [u34.regs, upd_ne (by decide) (by decide), g33_26]
  have g34_11 : reg n34 a1 = w30 := by
    rw [u34.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g33_2, show B + 0x21A0 + 0x30 = B + 0x21A0 + BitVec.ofNat 32 0x30 by sv_addr, w33_30]
  have keep_kk34 : SvKeepL B n0.mem n34.mem [] := by rw [m34]; exact keep_kk33
  clear keep_kk33
  have w34_30 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m34]; exact w33_30
  have w34_34 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m34]; exact w33_34
  have w34_38 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m34]; exact w33_38
  have w34_3c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m34]; exact w33_3c
  have w34_40 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m34]; exact w33_40
  have w34_44 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m34]; exact w33_44
  have w34_48 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m34]; exact w33_48
  have w34_4c : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m34]; exact w33_4c
  have w34_50 : memLoad32 n34.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m34]; exact w33_50
  clear w33_50 w33_4c w33_48 w33_44 w33_40 w33_3c w33_38 w33_34 w33_30 g33_10 g33_26 g33_24 g33_23 g33_22 g33_21 g33_20 g33_19 g33_18 g33_13 g33_12 g33_4 g33_3 g33_2 V33 E33 fR33 t33 fr33 m33 s33 u33 d33
  -- 0x9E6: sv_seqEqF
  obtain ⟨n35, c35, s35, rk35, a0_35, K35, fr35⟩ := sv_seqEqF (pl := w30.toNat) (ql := e4l.toNat)
    F E34 s34 sv_at_9e6 sv_at_9ea (by decide) (by decide) g34_2
    g34_10 (by rw [g34_11, ofNat_toNat_self]) g34_12 (by rw [g34_13, ofNat_toNat_self]) p4_in e4_in
  have t35 : Steps n0 n35 := t34.trans c35
  have fR35 : ∀ x, SvR B x → n35.mem x = M0 x := fun x hx => (fr35 x hx).trans (fR34 x hx)
  have E35 : SvCode n35.mem := E34.fr F fr35
  have V35 : SvSaves B n35.mem v := V34.keepL K35 (by decide)
  rw [sv_mbRo FW fR34 p4_in, sv_mbRo FW fR34 e4_in] at a0_35
  have g35_2 : reg n35 sp = B + 0x21A0 := by rw [rk35 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g34_2]
  have g35_3 : reg n35 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk35 (3 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g34_3]
  have g35_4 : reg n35 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk35 (4 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g34_4]
  have g35_18 : reg n35 (18 : Fin 32) = out := by rw [rk35 (18 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g34_18]
  have g35_19 : reg n35 (19 : Fin 32) = bp := by rw [rk35 (19 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g34_19]
  have g35_20 : reg n35 (20 : Fin 32) = x20 := by rw [rk35 (20 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g34_20]
  have g35_21 : reg n35 (21 : Fin 32) = x21 := by rw [rk35 (21 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g34_21]
  have g35_22 : reg n35 (22 : Fin 32) = x22 := by rw [rk35 (22 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g34_22]
  have g35_23 : reg n35 (23 : Fin 32) = q := by rw [rk35 (23 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g34_23]
  have g35_24 : reg n35 (24 : Fin 32) = x24 := by rw [rk35 (24 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g34_24]
  have g35_26 : reg n35 (26 : Fin 32) = x26 := by rw [rk35 (26 : Fin 32) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g34_26]
  have keep_kk35 : SvKeepL B n0.mem n35.mem [] := keep_kk34.trans K35
  clear keep_kk34
  have w35_30 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K35.w32 (by decide) (by decide)).trans w34_30
  have w35_34 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K35.w32 (by decide) (by decide)).trans w34_34
  have w35_38 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K35.w32 (by decide) (by decide)).trans w34_38
  have w35_3c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K35.w32 (by decide) (by decide)).trans w34_3c
  have w35_40 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K35.w32 (by decide) (by decide)).trans w34_40
  have w35_44 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K35.w32 (by decide) (by decide)).trans w34_44
  have w35_48 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K35.w32 (by decide) (by decide)).trans w34_48
  have w35_4c : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K35.w32 (by decide) (by decide)).trans w34_4c
  have w35_50 : memLoad32 n35.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K35.w32 (by decide) (by decide)).trans w34_50
  clear w34_50 w34_4c w34_48 w34_44 w34_40 w34_3c w34_38 w34_34 w34_30 g34_11 g34_26 g34_24 g34_23 g34_22 g34_21 g34_20 g34_19 g34_18 g34_13 g34_12 g34_10 g34_4 g34_3 g34_2 V34 E34 fR34 t34 fr34 m34 s34 u34 d34
  by_cases hq4 : memBytes M0 w44 w30.toNat = memBytes M0 e4p e4l.toNat
  rotate_left
  · have g35_10 : reg n35 a0 = BitVec.ofNat 32 0 := by rw [a0_35, ite_eq_right hq4]; rfl
    -- 0x9EE: branch, taken
    obtain ⟨n36, d36, u36⟩ := s35.taken E35.self 0xE46 sv_at_9ee
      (by decide) (by rw [g35_10, s35.zero]; decide)
    have s36 : St n36.mem SV n36 0xE46 (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
    have m36 : n36.mem = n35.mem := u36.mem
    have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
    have t36 : Steps n0 n36 := t35.trans (.single d36)
    have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
    have E36 : SvCode n36.mem := E35.fr F fr36
    have V36 : SvSaves B n36.mem v := V35.same m36
    have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, g35_2]
    have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, g35_3]
    have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, g35_4]
    have g36_10 : reg n36 a0 = BitVec.ofNat 32 0x0 := by rw [u36.regs, g35_10]
    have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, g35_18]
    have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, g35_19]
    have g36_20 : reg n36 (20 : Fin 32) = x20 := by rw [u36.regs, g35_20]
    have g36_21 : reg n36 (21 : Fin 32) = x21 := by rw [u36.regs, g35_21]
    have g36_22 : reg n36 (22 : Fin 32) = x22 := by rw [u36.regs, g35_22]
    have g36_23 : reg n36 (23 : Fin 32) = q := by rw [u36.regs, g35_23]
    have g36_24 : reg n36 (24 : Fin 32) = x24 := by rw [u36.regs, g35_24]
    have g36_26 : reg n36 (26 : Fin 32) = x26 := by rw [u36.regs, g35_26]
    have keep_kk36 : SvKeepL B n0.mem n36.mem [] := by rw [m36]; exact keep_kk35
    clear keep_kk35
    have w36_30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m36]; exact w35_30
    have w36_34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m36]; exact w35_34
    have w36_38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m36]; exact w35_38
    have w36_3c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m36]; exact w35_3c
    have w36_40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m36]; exact w35_40
    have w36_44 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m36]; exact w35_44
    have w36_48 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m36]; exact w35_48
    have w36_4c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m36]; exact w35_4c
    have w36_50 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m36]; exact w35_50
    clear w35_50 w35_4c w35_48 w35_44 w35_40 w35_3c w35_38 w35_34 w35_30 g35_26 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 K35 a0_35 rk35 s35 c35
    exact .inl ⟨(fun ⟨h0', h1', h2', h3', h4', h5', _⟩ => by exact hq4 h5'), sv_fail_e46 F E36 s36 t36 (fun x hx => (fR36 x hx).trans (fM x hx).symm) V36 hret g36_2 g36_18 hO g36_3 g36_4⟩
  have g35_10 : reg n35 a0 = BitVec.ofNat 32 1 := by rw [a0_35, ite_eq_left hq4]; rfl
  -- 0x9EE: branch, not taken
  obtain ⟨n36, d36, u36⟩ := s35.notTaken E35.self 0x9F2 sv_at_9ee
    (by decide) (by rw [g35_10, s35.zero]; decide)
  have s36 : St n36.mem SV n36 0x9F2 (reg n36) := ⟨u36.pc, rfl, fun _ => rfl⟩
  have m36 : n36.mem = n35.mem := u36.mem
  have fr36 : ∀ x, SvR B x → n36.mem x = n35.mem x := fun x _ => by rw [m36]
  have t36 : Steps n0 n36 := t35.trans (.single d36)
  have fR36 : ∀ x, SvR B x → n36.mem x = M0 x := fun x hx => (fr36 x hx).trans (fR35 x hx)
  have E36 : SvCode n36.mem := E35.fr F fr36
  have V36 : SvSaves B n36.mem v := V35.same m36
  have g36_2 : reg n36 sp = B + 0x21A0 := by rw [u36.regs, g35_2]
  have g36_3 : reg n36 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u36.regs, g35_3]
  have g36_4 : reg n36 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u36.regs, g35_4]
  have g36_10 : reg n36 a0 = BitVec.ofNat 32 0x1 := by rw [u36.regs, g35_10]
  have g36_18 : reg n36 (18 : Fin 32) = out := by rw [u36.regs, g35_18]
  have g36_19 : reg n36 (19 : Fin 32) = bp := by rw [u36.regs, g35_19]
  have g36_20 : reg n36 (20 : Fin 32) = x20 := by rw [u36.regs, g35_20]
  have g36_21 : reg n36 (21 : Fin 32) = x21 := by rw [u36.regs, g35_21]
  have g36_22 : reg n36 (22 : Fin 32) = x22 := by rw [u36.regs, g35_22]
  have g36_23 : reg n36 (23 : Fin 32) = q := by rw [u36.regs, g35_23]
  have g36_24 : reg n36 (24 : Fin 32) = x24 := by rw [u36.regs, g35_24]
  have g36_26 : reg n36 (26 : Fin 32) = x26 := by rw [u36.regs, g35_26]
  have keep_kk36 : SvKeepL B n0.mem n36.mem [] := by rw [m36]; exact keep_kk35
  clear keep_kk35
  have w36_30 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m36]; exact w35_30
  have w36_34 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m36]; exact w35_34
  have w36_38 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m36]; exact w35_38
  have w36_3c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m36]; exact w35_3c
  have w36_40 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m36]; exact w35_40
  have w36_44 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m36]; exact w35_44
  have w36_48 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m36]; exact w35_48
  have w36_4c : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m36]; exact w35_4c
  have w36_50 : memLoad32 n36.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m36]; exact w35_50
  clear w35_50 w35_4c w35_48 w35_44 w35_40 w35_3c w35_38 w35_34 w35_30 g35_26 g35_24 g35_23 g35_22 g35_21 g35_20 g35_19 g35_18 g35_4 g35_3 g35_2 V35 E35 fR35 t35 fr35 K35 a0_35 rk35 s35 c35
  -- 0x9F2
  obtain ⟨n37, c37, u37⟩ := s36.block svDpv9f2 E36.self svDpv9f2_end
    ⟨trivial, trivial⟩
  have m37 : n37.mem = n36.mem := u37.mem
  have s37 : St n37.mem SV n37 0x9F4 (reg n37) := ⟨u37.pc, rfl, fun _ => rfl⟩
  have rb37 : ∀ q, reg n37 q = (runBlock svDpv9f2 (n36.mem, reg n36)).2 q := fun q => by rw [u37.regs]
  have fr37 : ∀ x, SvR B x → n37.mem x = n36.mem x := fun x _ => by rw [m37]
  have t37 : Steps n0 n37 := t36.trans c37
  have fR37 : ∀ x, SvR B x → n37.mem x = M0 x := fun x hx => (fr37 x hx).trans (fR36 x hx)
  have E37 : SvCode n37.mem := E36.fr F fr37
  have V37 : SvSaves B n37.mem v := V36.same m37
  have g37_2 : reg n37 sp = B + 0x21A0 := by
    rw [rb37, runBlock_reg _ _ _ sp s36.zero (by decide), g36_2]
  have g37_3 : reg n37 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb37, runBlock_reg _ _ _ (3 : Fin 32) s36.zero (by decide), g36_3]
  have g37_4 : reg n37 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb37, runBlock_reg _ _ _ (4 : Fin 32) s36.zero (by decide), g36_4]
  have g37_18 : reg n37 (18 : Fin 32) = out := by
    rw [rb37, runBlock_reg _ _ _ (18 : Fin 32) s36.zero (by decide), g36_18]
  have g37_19 : reg n37 (19 : Fin 32) = bp := by
    rw [rb37, runBlock_reg _ _ _ (19 : Fin 32) s36.zero (by decide), g36_19]
  have g37_20 : reg n37 (20 : Fin 32) = x20 := by
    rw [rb37, runBlock_reg _ _ _ (20 : Fin 32) s36.zero (by decide), g36_20]
  have g37_21 : reg n37 (21 : Fin 32) = x21 := by
    rw [rb37, runBlock_reg _ _ _ (21 : Fin 32) s36.zero (by decide), g36_21]
  have g37_22 : reg n37 (22 : Fin 32) = x22 := by
    rw [rb37, runBlock_reg _ _ _ (22 : Fin 32) s36.zero (by decide), g36_22]
  have g37_23 : reg n37 (23 : Fin 32) = q := by
    rw [rb37, runBlock_reg _ _ _ (23 : Fin 32) s36.zero (by decide), g36_23]
  have g37_24 : reg n37 (24 : Fin 32) = x24 := by
    rw [rb37, runBlock_reg _ _ _ (24 : Fin 32) s36.zero (by decide), g36_24]
  have g37_26 : reg n37 (26 : Fin 32) = x26 := by
    rw [rb37, runBlock_reg _ _ _ (26 : Fin 32) s36.zero (by decide), g36_26]
  have g37_10 : reg n37 a0 = bp := by
    rw [rb37]; simp +decide only [runBlock, BInstr.run, svDpv9f2, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g36_2, g36_3, g36_4, g36_10, g36_18, g36_19, g36_20, g36_21, g36_22, g36_23, g36_24, g36_26, s36.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk37 : SvKeepL B n0.mem n37.mem [] := by rw [m37]; exact keep_kk36
  clear keep_kk36
  have w37_30 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m37]; exact w36_30
  have w37_34 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m37]; exact w36_34
  have w37_38 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m37]; exact w36_38
  have w37_3c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m37]; exact w36_3c
  have w37_40 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m37]; exact w36_40
  have w37_44 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m37]; exact w36_44
  have w37_48 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m37]; exact w36_48
  have w37_4c : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m37]; exact w36_4c
  have w37_50 : memLoad32 n37.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m37]; exact w36_50
  clear w36_50 w36_4c w36_48 w36_44 w36_40 w36_3c w36_38 w36_34 w36_30 g36_26 g36_24 g36_23 g36_22 g36_21 g36_20 g36_19 g36_18 g36_10 g36_4 g36_3 g36_2 V36 E36 fR36 t36 fr36 m36 s36 u36 d36 g35_10
  -- 0x9F4: lw outside the stack
  obtain ⟨n38, d38, u38⟩ := s37.lw E37.self sv_at_9f4 (off' := 0x9F6) (by decide)
    (by rw [g37_10]; exact asgp)
  have s38 : St n38.mem SV n38 0x9F6 (reg n38) := ⟨u38.pc, rfl, fun _ => rfl⟩
  have m38 : n38.mem = n37.mem := u38.mem
  have fr38 : ∀ x, SvR B x → n38.mem x = n37.mem x := fun x _ => by rw [m38]
  have t38 : Steps n0 n38 := t37.trans (.single d38)
  have fR38 : ∀ x, SvR B x → n38.mem x = M0 x := fun x hx => (fr38 x hx).trans (fR37 x hx)
  have E38 : SvCode n38.mem := E37.fr F fr38
  have V38 : SvSaves B n38.mem v := V37.same m38
  have g38_2 : reg n38 sp = B + 0x21A0 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_2]
  have g38_3 : reg n38 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_3]
  have g38_4 : reg n38 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u38.regs, upd_ne (by decide) (by decide), g37_4]
  have g38_10 : reg n38 a0 = bp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_10]
  have g38_18 : reg n38 (18 : Fin 32) = out := by rw [u38.regs, upd_ne (by decide) (by decide), g37_18]
  have g38_19 : reg n38 (19 : Fin 32) = bp := by rw [u38.regs, upd_ne (by decide) (by decide), g37_19]
  have g38_20 : reg n38 (20 : Fin 32) = x20 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_20]
  have g38_21 : reg n38 (21 : Fin 32) = x21 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_21]
  have g38_22 : reg n38 (22 : Fin 32) = x22 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_22]
  have g38_23 : reg n38 (23 : Fin 32) = q := by rw [u38.regs, upd_ne (by decide) (by decide), g37_23]
  have g38_24 : reg n38 (24 : Fin 32) = x24 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_24]
  have g38_26 : reg n38 (26 : Fin 32) = x26 := by rw [u38.regs, upd_ne (by decide) (by decide), g37_26]
  have g38_11 : reg n38 a1 = sgp := by
    rw [u38.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g37_10, sv_ld fR37 hsgp_in, hsgp]
  have keep_kk38 : SvKeepL B n0.mem n38.mem [] := by rw [m38]; exact keep_kk37
  clear keep_kk37
  have w38_30 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m38]; exact w37_30
  have w38_34 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m38]; exact w37_34
  have w38_38 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m38]; exact w37_38
  have w38_3c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m38]; exact w37_3c
  have w38_40 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m38]; exact w37_40
  have w38_44 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m38]; exact w37_44
  have w38_48 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m38]; exact w37_48
  have w38_4c : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m38]; exact w37_4c
  have w38_50 : memLoad32 n38.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m38]; exact w37_50
  clear w37_50 w37_4c w37_48 w37_44 w37_40 w37_3c w37_38 w37_34 w37_30 g37_10 g37_26 g37_24 g37_23 g37_22 g37_21 g37_20 g37_19 g37_18 g37_4 g37_3 g37_2 V37 E37 fR37 t37 fr37 rb37 s37 m37 u37 c37
  -- 0x9F6: lw outside the stack
  obtain ⟨n39, d39, u39⟩ := s38.lw E38.self sv_at_9f6 (off' := 0x9F8) (by decide)
    (by rw [g38_10]; exact asgl)
  have s39 : St n39.mem SV n39 0x9F8 (reg n39) := ⟨u39.pc, rfl, fun _ => rfl⟩
  have m39 : n39.mem = n38.mem := u39.mem
  have fr39 : ∀ x, SvR B x → n39.mem x = n38.mem x := fun x _ => by rw [m39]
  have t39 : Steps n0 n39 := t38.trans (.single d39)
  have fR39 : ∀ x, SvR B x → n39.mem x = M0 x := fun x hx => (fr39 x hx).trans (fR38 x hx)
  have E39 : SvCode n39.mem := E38.fr F fr39
  have V39 : SvSaves B n39.mem v := V38.same m39
  have g39_2 : reg n39 sp = B + 0x21A0 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_2]
  have g39_3 : reg n39 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u39.regs, upd_ne (by decide) (by decide), g38_3]
  have g39_4 : reg n39 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u39.regs, upd_ne (by decide) (by decide), g38_4]
  have g39_10 : reg n39 a0 = bp := by rw [u39.regs, upd_ne (by decide) (by decide), g38_10]
  have g39_11 : reg n39 a1 = sgp := by rw [u39.regs, upd_ne (by decide) (by decide), g38_11]
  have g39_18 : reg n39 (18 : Fin 32) = out := by rw [u39.regs, upd_ne (by decide) (by decide), g38_18]
  have g39_19 : reg n39 (19 : Fin 32) = bp := by rw [u39.regs, upd_ne (by decide) (by decide), g38_19]
  have g39_20 : reg n39 (20 : Fin 32) = x20 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_20]
  have g39_21 : reg n39 (21 : Fin 32) = x21 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_21]
  have g39_22 : reg n39 (22 : Fin 32) = x22 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_22]
  have g39_23 : reg n39 (23 : Fin 32) = q := by rw [u39.regs, upd_ne (by decide) (by decide), g38_23]
  have g39_24 : reg n39 (24 : Fin 32) = x24 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_24]
  have g39_26 : reg n39 (26 : Fin 32) = x26 := by rw [u39.regs, upd_ne (by decide) (by decide), g38_26]
  have g39_12 : reg n39 a2 = sgl := by
    rw [u39.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g38_10, sv_ld fR38 hsgl_in, hsgl]
  have keep_kk39 : SvKeepL B n0.mem n39.mem [] := by rw [m39]; exact keep_kk38
  clear keep_kk38
  have w39_30 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m39]; exact w38_30
  have w39_34 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m39]; exact w38_34
  have w39_38 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m39]; exact w38_38
  have w39_3c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m39]; exact w38_3c
  have w39_40 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m39]; exact w38_40
  have w39_44 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m39]; exact w38_44
  have w39_48 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m39]; exact w38_48
  have w39_4c : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m39]; exact w38_4c
  have w39_50 : memLoad32 n39.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m39]; exact w38_50
  clear w38_50 w38_4c w38_48 w38_44 w38_40 w38_3c w38_38 w38_34 w38_30 g38_11 g38_26 g38_24 g38_23 g38_22 g38_21 g38_20 g38_19 g38_18 g38_10 g38_4 g38_3 g38_2 V38 E38 fR38 t38 fr38 m38 s38 u38 d38
  -- 0x9F8
  obtain ⟨n40, c40, u40⟩ := s39.block svDpv9f8 E39.self svDpv9f8_end
    ⟨trivial, trivial⟩
  have m40 : n40.mem = n39.mem := u40.mem
  have s40 : St n40.mem SV n40 0x9FA (reg n40) := ⟨u40.pc, rfl, fun _ => rfl⟩
  have rb40 : ∀ q, reg n40 q = (runBlock svDpv9f8 (n39.mem, reg n39)).2 q := fun q => by rw [u40.regs]
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
  have g40_11 : reg n40 a1 = sgp := by
    rw [rb40, runBlock_reg _ _ _ a1 s39.zero (by decide), g39_11]
  have g40_12 : reg n40 a2 = sgl := by
    rw [rb40, runBlock_reg _ _ _ a2 s39.zero (by decide), g39_12]
  have g40_18 : reg n40 (18 : Fin 32) = out := by
    rw [rb40, runBlock_reg _ _ _ (18 : Fin 32) s39.zero (by decide), g39_18]
  have g40_19 : reg n40 (19 : Fin 32) = bp := by
    rw [rb40, runBlock_reg _ _ _ (19 : Fin 32) s39.zero (by decide), g39_19]
  have g40_20 : reg n40 (20 : Fin 32) = x20 := by
    rw [rb40, runBlock_reg _ _ _ (20 : Fin 32) s39.zero (by decide), g39_20]
  have g40_21 : reg n40 (21 : Fin 32) = x21 := by
    rw [rb40, runBlock_reg _ _ _ (21 : Fin 32) s39.zero (by decide), g39_21]
  have g40_22 : reg n40 (22 : Fin 32) = x22 := by
    rw [rb40, runBlock_reg _ _ _ (22 : Fin 32) s39.zero (by decide), g39_22]
  have g40_23 : reg n40 (23 : Fin 32) = q := by
    rw [rb40, runBlock_reg _ _ _ (23 : Fin 32) s39.zero (by decide), g39_23]
  have g40_24 : reg n40 (24 : Fin 32) = x24 := by
    rw [rb40, runBlock_reg _ _ _ (24 : Fin 32) s39.zero (by decide), g39_24]
  have g40_26 : reg n40 (26 : Fin 32) = x26 := by
    rw [rb40, runBlock_reg _ _ _ (26 : Fin 32) s39.zero (by decide), g39_26]
  have g40_10 : reg n40 a0 = B + 0x21A0 + BitVec.ofNat 32 0x170 := by
    rw [rb40]; simp +decide only [runBlock, BInstr.run, svDpv9f8, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g39_2, g39_3, g39_4, g39_10, g39_11, g39_12, g39_18, g39_19, g39_20, g39_21, g39_22, g39_23, g39_24, g39_26, s39.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk40 : SvKeepL B n0.mem n40.mem [] := by rw [m40]; exact keep_kk39
  clear keep_kk39
  have w40_30 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m40]; exact w39_30
  have w40_34 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m40]; exact w39_34
  have w40_38 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m40]; exact w39_38
  have w40_3c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m40]; exact w39_3c
  have w40_40 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m40]; exact w39_40
  have w40_44 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m40]; exact w39_44
  have w40_48 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m40]; exact w39_48
  have w40_4c : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m40]; exact w39_4c
  have w40_50 : memLoad32 n40.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m40]; exact w39_50
  clear w39_50 w39_4c w39_48 w39_44 w39_40 w39_3c w39_38 w39_34 w39_30 g39_12 g39_26 g39_24 g39_23 g39_22 g39_21 g39_20 g39_19 g39_18 g39_11 g39_10 g39_4 g39_3 g39_2 V39 E39 fR39 t39 fr39 m39 s39 u39 d39
  -- 0x9FA: sw
  obtain ⟨n41, d41, s41, fr41, K41, W41, rg41⟩ := sv_sw F E40 s40 sv_at_9fa (off' := 0x9FC) (c := 0x70)
    (by decide) (by rw [g40_2]; sv_addr) (by decide) (by decide)
  have t41 : Steps n0 n41 := t40.trans d41
  have fR41 : ∀ x, SvR B x → n41.mem x = M0 x := fun x hx => (fr41 x hx).trans (fR40 x hx)
  have E41 : SvCode n41.mem := E40.fr F fr41
  have V41 : SvSaves B n41.mem v := V40.keep K41 (by decide)
  have g41_2 : reg n41 sp = B + 0x21A0 := by rw [rg41 sp, g40_2]
  have g41_3 : reg n41 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg41 (3 : Fin 32), g40_3]
  have g41_4 : reg n41 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg41 (4 : Fin 32), g40_4]
  have g41_10 : reg n41 a0 = B + 0x21A0 + BitVec.ofNat 32 0x170 := by rw [rg41 a0, g40_10]
  have g41_11 : reg n41 a1 = sgp := by rw [rg41 a1, g40_11]
  have g41_12 : reg n41 a2 = sgl := by rw [rg41 a2, g40_12]
  have g41_18 : reg n41 (18 : Fin 32) = out := by rw [rg41 (18 : Fin 32), g40_18]
  have g41_19 : reg n41 (19 : Fin 32) = bp := by rw [rg41 (19 : Fin 32), g40_19]
  have g41_20 : reg n41 (20 : Fin 32) = x20 := by rw [rg41 (20 : Fin 32), g40_20]
  have g41_21 : reg n41 (21 : Fin 32) = x21 := by rw [rg41 (21 : Fin 32), g40_21]
  have g41_22 : reg n41 (22 : Fin 32) = x22 := by rw [rg41 (22 : Fin 32), g40_22]
  have g41_23 : reg n41 (23 : Fin 32) = q := by rw [rg41 (23 : Fin 32), g40_23]
  have g41_24 : reg n41 (24 : Fin 32) = x24 := by rw [rg41 (24 : Fin 32), g40_24]
  have g41_26 : reg n41 (26 : Fin 32) = x26 := by rw [rg41 (26 : Fin 32), g40_26]
  have keep_kk41 : SvKeepL B n0.mem n41.mem [(0x70, 0x4)] := keep_kk40.trans K41.toL
  clear keep_kk40
  have w41_30 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K41.w32 (by decide) (by decide)).trans w40_30
  have w41_34 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K41.w32 (by decide) (by decide)).trans w40_34
  have w41_38 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K41.w32 (by decide) (by decide)).trans w40_38
  have w41_3c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K41.w32 (by decide) (by decide)).trans w40_3c
  have w41_40 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K41.w32 (by decide) (by decide)).trans w40_40
  have w41_44 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K41.w32 (by decide) (by decide)).trans w40_44
  have w41_48 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K41.w32 (by decide) (by decide)).trans w40_48
  have w41_4c : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K41.w32 (by decide) (by decide)).trans w40_4c
  have w41_50 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K41.w32 (by decide) (by decide)).trans w40_50
  have w41_70 : memLoad32 n41.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = sgp := by rw [W41, g40_11]
  clear w40_50 w40_4c w40_48 w40_44 w40_40 w40_3c w40_38 w40_34 w40_30 g40_10 g40_26 g40_24 g40_23 g40_22 g40_21 g40_20 g40_19 g40_18 g40_12 g40_11 g40_4 g40_3 g40_2 V40 E40 fR40 t40 fr40 rb40 s40 m40 u40 c40
  -- 0x9FC: sw
  obtain ⟨n42, d42, s42, fr42, K42, W42, rg42⟩ := sv_sw F E41 s41 sv_at_9fc (off' := 0x9FE) (c := 0x68)
    (by decide) (by rw [g41_2]; sv_addr) (by decide) (by decide)
  have t42 : Steps n0 n42 := t41.trans d42
  have fR42 : ∀ x, SvR B x → n42.mem x = M0 x := fun x hx => (fr42 x hx).trans (fR41 x hx)
  have E42 : SvCode n42.mem := E41.fr F fr42
  have V42 : SvSaves B n42.mem v := V41.keep K42 (by decide)
  have g42_2 : reg n42 sp = B + 0x21A0 := by rw [rg42 sp, g41_2]
  have g42_3 : reg n42 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg42 (3 : Fin 32), g41_3]
  have g42_4 : reg n42 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg42 (4 : Fin 32), g41_4]
  have g42_10 : reg n42 a0 = B + 0x21A0 + BitVec.ofNat 32 0x170 := by rw [rg42 a0, g41_10]
  have g42_11 : reg n42 a1 = sgp := by rw [rg42 a1, g41_11]
  have g42_12 : reg n42 a2 = sgl := by rw [rg42 a2, g41_12]
  have g42_18 : reg n42 (18 : Fin 32) = out := by rw [rg42 (18 : Fin 32), g41_18]
  have g42_19 : reg n42 (19 : Fin 32) = bp := by rw [rg42 (19 : Fin 32), g41_19]
  have g42_20 : reg n42 (20 : Fin 32) = x20 := by rw [rg42 (20 : Fin 32), g41_20]
  have g42_21 : reg n42 (21 : Fin 32) = x21 := by rw [rg42 (21 : Fin 32), g41_21]
  have g42_22 : reg n42 (22 : Fin 32) = x22 := by rw [rg42 (22 : Fin 32), g41_22]
  have g42_23 : reg n42 (23 : Fin 32) = q := by rw [rg42 (23 : Fin 32), g41_23]
  have g42_24 : reg n42 (24 : Fin 32) = x24 := by rw [rg42 (24 : Fin 32), g41_24]
  have g42_26 : reg n42 (26 : Fin 32) = x26 := by rw [rg42 (26 : Fin 32), g41_26]
  have keep_kk42 : SvKeepL B n0.mem n42.mem [(0x70, 0x4), (0x68, 0x4)] := keep_kk41.trans K42.toL
  clear keep_kk41
  have w42_30 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K42.w32 (by decide) (by decide)).trans w41_30
  have w42_34 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K42.w32 (by decide) (by decide)).trans w41_34
  have w42_38 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K42.w32 (by decide) (by decide)).trans w41_38
  have w42_3c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K42.w32 (by decide) (by decide)).trans w41_3c
  have w42_40 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K42.w32 (by decide) (by decide)).trans w41_40
  have w42_44 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K42.w32 (by decide) (by decide)).trans w41_44
  have w42_48 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K42.w32 (by decide) (by decide)).trans w41_48
  have w42_4c : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K42.w32 (by decide) (by decide)).trans w41_4c
  have w42_50 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K42.w32 (by decide) (by decide)).trans w41_50
  have w42_70 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = sgp := (K42.w32 (by decide) (by decide)).trans w41_70
  have w42_68 : memLoad32 n42.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [W42, g41_12]
  clear w41_70 w41_50 w41_4c w41_48 w41_44 w41_40 w41_3c w41_38 w41_34 w41_30 g41_26 g41_24 g41_23 g41_22 g41_21 g41_20 g41_19 g41_18 g41_12 g41_11 g41_10 g41_4 g41_3 g41_2 V41 E41 fR41 t41 rg41 W41 K41 fr41 s41 d41
  -- 0x9FE: sv_es32F
  obtain ⟨n43, c43, s43, sp43, rk43, K43, R43, fr43⟩ := sv_es32F (oc := 0x170) (nl := sgl.toNat)
    F E42 s42 sv_at_9fe sv_at_a02 (by decide) (by decide) g42_2
    g42_10 g42_11 (by rw [g42_12, ofNat_toNat_self]) (by decide) sg_in
  have t43 : Steps n0 n43 := t42.trans c43
  have fR43 : ∀ x, SvR B x → n43.mem x = M0 x := fun x hx => (fr43 x hx).trans (fR42 x hx)
  have E43 : SvCode n43.mem := E42.fr F fr43
  have V43 : SvSaves B n43.mem v := V42.keepL K43 (by decide)
  rw [ecdsaSigOf_congr (sv_pt fR42 sg_in)] at R43
  have g43_3 : reg n43 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rk43 (3 : Fin 32) (by decide), g42_3]
  have g43_4 : reg n43 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rk43 (4 : Fin 32) (by decide), g42_4]
  have g43_18 : reg n43 (18 : Fin 32) = out := by rw [rk43 (18 : Fin 32) (by decide), g42_18]
  have g43_19 : reg n43 (19 : Fin 32) = bp := by rw [rk43 (19 : Fin 32) (by decide), g42_19]
  have g43_20 : reg n43 (20 : Fin 32) = x20 := by rw [rk43 (20 : Fin 32) (by decide), g42_20]
  have g43_21 : reg n43 (21 : Fin 32) = x21 := by rw [rk43 (21 : Fin 32) (by decide), g42_21]
  have g43_22 : reg n43 (22 : Fin 32) = x22 := by rw [rk43 (22 : Fin 32) (by decide), g42_22]
  have g43_23 : reg n43 (23 : Fin 32) = q := by rw [rk43 (23 : Fin 32) (by decide), g42_23]
  have g43_24 : reg n43 (24 : Fin 32) = x24 := by rw [rk43 (24 : Fin 32) (by decide), g42_24]
  have g43_26 : reg n43 (26 : Fin 32) = x26 := by rw [rk43 (26 : Fin 32) (by decide), g42_26]
  have g43_2 : reg n43 sp = B + 0x21A0 := sp43
  obtain ⟨r43, hr43⟩ : ∃ r, ecdsaSigOf 32 M0 (sgp) (sgl.toNat) = r := ⟨_, rfl⟩
  rcases r43 with eb43 | ⟨sr43, ss43⟩
  · rw [hr43] at R43
    obtain ⟨y0_43, y1_43⟩ := R43
    obtain ⟨ec_43, ey_43, hz_c43⟩ : ∃ b : BitVec 8, n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x171) = b ∧ b.toNat < 0x27 :=
      ⟨_, y1_43, by sv_eb hr43⟩
    have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x70, 0x4), (0x68, 0x4), (0x170, 0x41)] := keep_kk42.trans K43
    clear keep_kk42
    have w43_30 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K43.w32 (by decide) (by decide)).trans w42_30
    have w43_34 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K43.w32 (by decide) (by decide)).trans w42_34
    have w43_38 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K43.w32 (by decide) (by decide)).trans w42_38
    have w43_3c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K43.w32 (by decide) (by decide)).trans w42_3c
    have w43_40 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K43.w32 (by decide) (by decide)).trans w42_40
    have w43_44 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K43.w32 (by decide) (by decide)).trans w42_44
    have w43_48 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K43.w32 (by decide) (by decide)).trans w42_48
    have w43_4c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K43.w32 (by decide) (by decide)).trans w42_4c
    have w43_50 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K43.w32 (by decide) (by decide)).trans w42_50
    have w43_68 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K43.w32 (by decide) (by decide)).trans w42_68
    have w43_70 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = sgp := (K43.w32 (by decide) (by decide)).trans w42_70
    have b43_170 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = (1 : BitVec 8) := y0_43
    have b43_171 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x171) = ec_43 := ey_43
    clear w42_68 w42_70 w42_50 w42_4c w42_48 w42_44 w42_40 w42_3c w42_38 w42_34 w42_30 g42_26 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_12 g42_11 g42_10 g42_4 g42_3 g42_2 V42 E42 fR42 t42 rg42 W42 K42 fr42 s42 d42
    -- 0xA06: lbu
    obtain ⟨n44, d44, u44⟩ := s43.lbu E43.self sv_at_a06 (off' := 0xA0A) (by decide)
    have s44 : St n44.mem SV n44 0xA0A (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
    have m44 : n44.mem = n43.mem := u44.mem
    have fr44 : ∀ x, SvR B x → n44.mem x = n43.mem x := fun x _ => by rw [m44]
    have t44 : Steps n0 n44 := t43.trans (.single d44)
    have fR44 : ∀ x, SvR B x → n44.mem x = M0 x := fun x hx => (fr44 x hx).trans (fR43 x hx)
    have E44 : SvCode n44.mem := E43.fr F fr44
    have V44 : SvSaves B n44.mem v := V43.same m44
    have g44_2 : reg n44 sp = B + 0x21A0 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_2]
    have g44_3 : reg n44 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u44.regs, upd_ne (by decide) (by decide), g43_3]
    have g44_4 : reg n44 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u44.regs, upd_ne (by decide) (by decide), g43_4]
    have g44_18 : reg n44 (18 : Fin 32) = out := by rw [u44.regs, upd_ne (by decide) (by decide), g43_18]
    have g44_19 : reg n44 (19 : Fin 32) = bp := by rw [u44.regs, upd_ne (by decide) (by decide), g43_19]
    have g44_20 : reg n44 (20 : Fin 32) = x20 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_20]
    have g44_21 : reg n44 (21 : Fin 32) = x21 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_21]
    have g44_22 : reg n44 (22 : Fin 32) = x22 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_22]
    have g44_23 : reg n44 (23 : Fin 32) = q := by rw [u44.regs, upd_ne (by decide) (by decide), g43_23]
    have g44_24 : reg n44 (24 : Fin 32) = x24 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_24]
    have g44_26 : reg n44 (26 : Fin 32) = x26 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_26]
    have g44_10 : reg n44 a0 = ((1 : BitVec 8)).zeroExtend 32 := by
      rw [u44.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g43_2, show B + 0x21A0 + 0x170 = B + 0x21A0 + BitVec.ofNat 32 0x170 by sv_addr, b43_170]
    have keep_kk44 : SvKeepL B n0.mem n44.mem [(0x70, 0x4), (0x68, 0x4), (0x170, 0x41)] := by rw [m44]; exact keep_kk43
    clear keep_kk43
    have w44_30 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m44]; exact w43_30
    have w44_34 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m44]; exact w43_34
    have w44_38 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m44]; exact w43_38
    have w44_3c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m44]; exact w43_3c
    have w44_40 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m44]; exact w43_40
    have w44_44 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m44]; exact w43_44
    have w44_48 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m44]; exact w43_48
    have w44_4c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m44]; exact w43_4c
    have w44_50 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m44]; exact w43_50
    have w44_68 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m44]; exact w43_68
    have w44_70 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = sgp := by rw [m44]; exact w43_70
    have b44_170 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = (1 : BitVec 8) := by rw [m44]; exact b43_170
    have b44_171 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x171) = ec_43 := by rw [m44]; exact b43_171
    clear b43_171 b43_170 w43_70 w43_68 w43_50 w43_4c w43_48 w43_44 w43_40 w43_3c w43_38 w43_34 w43_30 ey_43 y1_43 y0_43
    -- 0xA0A: lbu
    obtain ⟨n45, d45, u45⟩ := s44.lbu E44.self sv_at_a0a (off' := 0xA0E) (by decide)
    have s45 : St n45.mem SV n45 0xA0E (reg n45) := ⟨u45.pc, rfl, fun _ => rfl⟩
    have m45 : n45.mem = n44.mem := u45.mem
    have fr45 : ∀ x, SvR B x → n45.mem x = n44.mem x := fun x _ => by rw [m45]
    have t45 : Steps n0 n45 := t44.trans (.single d45)
    have fR45 : ∀ x, SvR B x → n45.mem x = M0 x := fun x hx => (fr45 x hx).trans (fR44 x hx)
    have E45 : SvCode n45.mem := E44.fr F fr45
    have V45 : SvSaves B n45.mem v := V44.same m45
    have g45_2 : reg n45 sp = B + 0x21A0 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_2]
    have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u45.regs, upd_ne (by decide) (by decide), g44_3]
    have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u45.regs, upd_ne (by decide) (by decide), g44_4]
    have g45_10 : reg n45 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_10]
    have g45_18 : reg n45 (18 : Fin 32) = out := by rw [u45.regs, upd_ne (by decide) (by decide), g44_18]
    have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [u45.regs, upd_ne (by decide) (by decide), g44_19]
    have g45_20 : reg n45 (20 : Fin 32) = x20 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_20]
    have g45_21 : reg n45 (21 : Fin 32) = x21 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_21]
    have g45_22 : reg n45 (22 : Fin 32) = x22 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_22]
    have g45_23 : reg n45 (23 : Fin 32) = q := by rw [u45.regs, upd_ne (by decide) (by decide), g44_23]
    have g45_24 : reg n45 (24 : Fin 32) = x24 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_24]
    have g45_26 : reg n45 (26 : Fin 32) = x26 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_26]
    have g45_8 : reg n45 (8 : Fin 32) = (ec_43).zeroExtend 32 := by
      rw [u45.regs]; simp +decide only [upd, ↓reduceIte]
      rw [g44_2, show B + 0x21A0 + 0x171 = B + 0x21A0 + BitVec.ofNat 32 0x171 by sv_addr, b44_171]
    have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x70, 0x4), (0x68, 0x4), (0x170, 0x41)] := by rw [m45]; exact keep_kk44
    clear keep_kk44
    have w45_30 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m45]; exact w44_30
    have w45_34 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m45]; exact w44_34
    have w45_38 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m45]; exact w44_38
    have w45_3c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m45]; exact w44_3c
    have w45_40 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m45]; exact w44_40
    have w45_44 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m45]; exact w44_44
    have w45_48 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m45]; exact w44_48
    have w45_4c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m45]; exact w44_4c
    have w45_50 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m45]; exact w44_50
    have w45_68 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m45]; exact w44_68
    have w45_70 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = sgp := by rw [m45]; exact w44_70
    have b45_170 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = (1 : BitVec 8) := by rw [m45]; exact b44_170
    have b45_171 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x171) = ec_43 := by rw [m45]; exact b44_171
    clear b44_171 b44_170 w44_70 w44_68 w44_50 w44_4c w44_48 w44_44 w44_40 w44_3c w44_38 w44_34 w44_30 g44_10 g44_26 g44_24 g44_23 g44_22 g44_21 g44_20 g44_19 g44_18 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 m44 s44 u44 d44
    -- 0xA0E: branch, taken
    obtain ⟨n46, d46, u46⟩ := s45.taken E45.self 0x7A4 sv_at_a0e
      (by decide) (by rw [g45_10, s45.zero]; decide)
    have s46 : St n46.mem SV n46 0x7A4 (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
    have m46 : n46.mem = n45.mem := u46.mem
    have fr46 : ∀ x, SvR B x → n46.mem x = n45.mem x := fun x _ => by rw [m46]
    have t46 : Steps n0 n46 := t45.trans (.single d46)
    have fR46 : ∀ x, SvR B x → n46.mem x = M0 x := fun x hx => (fr46 x hx).trans (fR45 x hx)
    have E46 : SvCode n46.mem := E45.fr F fr46
    have V46 : SvSaves B n46.mem v := V45.same m46
    have g46_2 : reg n46 sp = B + 0x21A0 := by rw [u46.regs, g45_2]
    have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u46.regs, g45_3]
    have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u46.regs, g45_4]
    have g46_8 : reg n46 (8 : Fin 32) = (ec_43).zeroExtend 32 := by rw [u46.regs, g45_8]
    have g46_10 : reg n46 a0 = ((1 : BitVec 8)).zeroExtend 32 := by rw [u46.regs, g45_10]
    have g46_18 : reg n46 (18 : Fin 32) = out := by rw [u46.regs, g45_18]
    have g46_19 : reg n46 (19 : Fin 32) = bp := by rw [u46.regs, g45_19]
    have g46_20 : reg n46 (20 : Fin 32) = x20 := by rw [u46.regs, g45_20]
    have g46_21 : reg n46 (21 : Fin 32) = x21 := by rw [u46.regs, g45_21]
    have g46_22 : reg n46 (22 : Fin 32) = x22 := by rw [u46.regs, g45_22]
    have g46_23 : reg n46 (23 : Fin 32) = q := by rw [u46.regs, g45_23]
    have g46_24 : reg n46 (24 : Fin 32) = x24 := by rw [u46.regs, g45_24]
    have g46_26 : reg n46 (26 : Fin 32) = x26 := by rw [u46.regs, g45_26]
    have keep_kk46 : SvKeepL B n0.mem n46.mem [(0x70, 0x4), (0x68, 0x4), (0x170, 0x41)] := by rw [m46]; exact keep_kk45
    clear keep_kk45
    have w46_30 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m46]; exact w45_30
    have w46_34 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m46]; exact w45_34
    have w46_38 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m46]; exact w45_38
    have w46_3c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m46]; exact w45_3c
    have w46_40 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m46]; exact w45_40
    have w46_44 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m46]; exact w45_44
    have w46_48 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m46]; exact w45_48
    have w46_4c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m46]; exact w45_4c
    have w46_50 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m46]; exact w45_50
    have w46_68 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m46]; exact w45_68
    have w46_70 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = sgp := by rw [m46]; exact w45_70
    have b46_170 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = (1 : BitVec 8) := by rw [m46]; exact b45_170
    have b46_171 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x171) = ec_43 := by rw [m46]; exact b45_171
    clear b45_171 b45_170 w45_70 w45_68 w45_50 w45_4c w45_48 w45_44 w45_40 w45_3c w45_38 w45_34 w45_30 g45_8 g45_26 g45_24 g45_23 g45_22 g45_21 g45_20 g45_19 g45_18 g45_10 g45_4 g45_3 g45_2 V45 E45 fR45 t45 fr45 m45 s45 u45 d45
    exact .inl ⟨(fun ⟨h0', h1', h2', h3', h4', h5', sr43', ss43', h6', _⟩ => by rw [hr43] at h6'; cases h6'), sv_fail F E46 s46 t46 (fun x hx => (fR46 x hx).trans (fM x hx).symm) V46 hret g46_2 g46_18 hO g46_3 g46_4 (by rw [g46_8]; sv_code)⟩
  rw [hr43] at R43
  obtain ⟨y0_43, yr_43, ys_43⟩ := R43
  have q43_171 : ∀ j, j < 32 → n43.mem (B + 0x21A0 + BitVec.ofNat 32 (0x171 + j)) = BitVec.ofNat 8 ((sr43).getD j 0) := fun j hj => by rw [show 0x171 + j = 0x170 + 1 + j by omega]; exact yr_43 j hj
  have q43_191 : ∀ j, j < 32 → n43.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => by rw [show 0x191 + j = 0x170 + 33 + j by omega]; exact ys_43 j hj
  have keep_kk43 : SvKeepL B n0.mem n43.mem [(0x70, 0x4), (0x68, 0x4), (0x170, 0x41)] := keep_kk42.trans K43
  clear keep_kk42
  have w43_30 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K43.w32 (by decide) (by decide)).trans w42_30
  have w43_34 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K43.w32 (by decide) (by decide)).trans w42_34
  have w43_38 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K43.w32 (by decide) (by decide)).trans w42_38
  have w43_3c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K43.w32 (by decide) (by decide)).trans w42_3c
  have w43_40 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K43.w32 (by decide) (by decide)).trans w42_40
  have w43_44 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K43.w32 (by decide) (by decide)).trans w42_44
  have w43_48 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K43.w32 (by decide) (by decide)).trans w42_48
  have w43_4c : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K43.w32 (by decide) (by decide)).trans w42_4c
  have w43_50 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K43.w32 (by decide) (by decide)).trans w42_50
  have w43_68 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K43.w32 (by decide) (by decide)).trans w42_68
  have w43_70 : memLoad32 n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = sgp := (K43.w32 (by decide) (by decide)).trans w42_70
  have b43_170 : n43.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = (0 : BitVec 8) := y0_43
  clear w42_68 w42_70 w42_50 w42_4c w42_48 w42_44 w42_40 w42_3c w42_38 w42_34 w42_30 g42_26 g42_24 g42_23 g42_22 g42_21 g42_20 g42_19 g42_18 g42_12 g42_11 g42_10 g42_4 g42_3 g42_2 V42 E42 fR42 t42 rg42 W42 K42 fr42 s42 d42
  -- 0xA06: lbu
  obtain ⟨n44, d44, u44⟩ := s43.lbu E43.self sv_at_a06 (off' := 0xA0A) (by decide)
  have s44 : St n44.mem SV n44 0xA0A (reg n44) := ⟨u44.pc, rfl, fun _ => rfl⟩
  have m44 : n44.mem = n43.mem := u44.mem
  have fr44 : ∀ x, SvR B x → n44.mem x = n43.mem x := fun x _ => by rw [m44]
  have t44 : Steps n0 n44 := t43.trans (.single d44)
  have fR44 : ∀ x, SvR B x → n44.mem x = M0 x := fun x hx => (fr44 x hx).trans (fR43 x hx)
  have E44 : SvCode n44.mem := E43.fr F fr44
  have V44 : SvSaves B n44.mem v := V43.same m44
  have g44_2 : reg n44 sp = B + 0x21A0 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_2]
  have g44_3 : reg n44 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u44.regs, upd_ne (by decide) (by decide), g43_3]
  have g44_4 : reg n44 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u44.regs, upd_ne (by decide) (by decide), g43_4]
  have g44_18 : reg n44 (18 : Fin 32) = out := by rw [u44.regs, upd_ne (by decide) (by decide), g43_18]
  have g44_19 : reg n44 (19 : Fin 32) = bp := by rw [u44.regs, upd_ne (by decide) (by decide), g43_19]
  have g44_20 : reg n44 (20 : Fin 32) = x20 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_20]
  have g44_21 : reg n44 (21 : Fin 32) = x21 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_21]
  have g44_22 : reg n44 (22 : Fin 32) = x22 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_22]
  have g44_23 : reg n44 (23 : Fin 32) = q := by rw [u44.regs, upd_ne (by decide) (by decide), g43_23]
  have g44_24 : reg n44 (24 : Fin 32) = x24 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_24]
  have g44_26 : reg n44 (26 : Fin 32) = x26 := by rw [u44.regs, upd_ne (by decide) (by decide), g43_26]
  have g44_10 : reg n44 a0 = ((0 : BitVec 8)).zeroExtend 32 := by
    rw [u44.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g43_2, show B + 0x21A0 + 0x170 = B + 0x21A0 + BitVec.ofNat 32 0x170 by sv_addr, b43_170]
  have keep_kk44 : SvKeepL B n0.mem n44.mem [(0x70, 0x4), (0x68, 0x4), (0x170, 0x41)] := by rw [m44]; exact keep_kk43
  clear keep_kk43
  have w44_30 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m44]; exact w43_30
  have w44_34 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m44]; exact w43_34
  have w44_38 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m44]; exact w43_38
  have w44_3c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m44]; exact w43_3c
  have w44_40 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m44]; exact w43_40
  have w44_44 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m44]; exact w43_44
  have w44_48 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m44]; exact w43_48
  have w44_4c : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m44]; exact w43_4c
  have w44_50 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m44]; exact w43_50
  have w44_68 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m44]; exact w43_68
  have w44_70 : memLoad32 n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = sgp := by rw [m44]; exact w43_70
  have b44_170 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = (0 : BitVec 8) := by rw [m44]; exact b43_170
  have q44_171 : ∀ j, j < 32 → n44.mem (B + 0x21A0 + BitVec.ofNat 32 (0x171 + j)) = BitVec.ofNat 8 ((sr43).getD j 0) := fun j hj => by rw [m44]; exact q43_171 j hj
  have q44_191 : ∀ j, j < 32 → n44.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => by rw [m44]; exact q43_191 j hj
  clear b43_170 w43_70 w43_68 w43_50 w43_4c w43_48 w43_44 w43_40 w43_3c w43_38 w43_34 w43_30 q43_191 q43_171 ys_43 yr_43 y0_43 g43_2 g43_26 g43_24 g43_23 g43_22 g43_21 g43_20 g43_19 g43_18 g43_4 g43_3 V43 E43 fR43 t43 fr43 K43 rk43 sp43 s43 c43
  -- 0xA0A: lbu
  have b44_171 : n44.mem (B + 0x21A0 + BitVec.ofNat 32 0x171) = BitVec.ofNat 8 ((sr43).getD 0 0) := q44_171 0 (by decide)
  obtain ⟨n45, d45, u45⟩ := s44.lbu E44.self sv_at_a0a (off' := 0xA0E) (by decide)
  have s45 : St n45.mem SV n45 0xA0E (reg n45) := ⟨u45.pc, rfl, fun _ => rfl⟩
  have m45 : n45.mem = n44.mem := u45.mem
  have fr45 : ∀ x, SvR B x → n45.mem x = n44.mem x := fun x _ => by rw [m45]
  have t45 : Steps n0 n45 := t44.trans (.single d45)
  have fR45 : ∀ x, SvR B x → n45.mem x = M0 x := fun x hx => (fr45 x hx).trans (fR44 x hx)
  have E45 : SvCode n45.mem := E44.fr F fr45
  have V45 : SvSaves B n45.mem v := V44.same m45
  have g45_2 : reg n45 sp = B + 0x21A0 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_2]
  have g45_3 : reg n45 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u45.regs, upd_ne (by decide) (by decide), g44_3]
  have g45_4 : reg n45 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u45.regs, upd_ne (by decide) (by decide), g44_4]
  have g45_10 : reg n45 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_10]
  have g45_18 : reg n45 (18 : Fin 32) = out := by rw [u45.regs, upd_ne (by decide) (by decide), g44_18]
  have g45_19 : reg n45 (19 : Fin 32) = bp := by rw [u45.regs, upd_ne (by decide) (by decide), g44_19]
  have g45_20 : reg n45 (20 : Fin 32) = x20 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_20]
  have g45_21 : reg n45 (21 : Fin 32) = x21 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_21]
  have g45_22 : reg n45 (22 : Fin 32) = x22 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_22]
  have g45_23 : reg n45 (23 : Fin 32) = q := by rw [u45.regs, upd_ne (by decide) (by decide), g44_23]
  have g45_24 : reg n45 (24 : Fin 32) = x24 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_24]
  have g45_26 : reg n45 (26 : Fin 32) = x26 := by rw [u45.regs, upd_ne (by decide) (by decide), g44_26]
  have g45_8 : reg n45 (8 : Fin 32) = (BitVec.ofNat 8 ((sr43).getD 0 0)).zeroExtend 32 := by
    rw [u45.regs]; simp +decide only [upd, ↓reduceIte]
    rw [g44_2, show B + 0x21A0 + 0x171 = B + 0x21A0 + BitVec.ofNat 32 0x171 by sv_addr, b44_171]
  have keep_kk45 : SvKeepL B n0.mem n45.mem [(0x70, 0x4), (0x68, 0x4), (0x170, 0x41)] := by rw [m45]; exact keep_kk44
  clear keep_kk44
  have w45_30 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m45]; exact w44_30
  have w45_34 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m45]; exact w44_34
  have w45_38 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m45]; exact w44_38
  have w45_3c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m45]; exact w44_3c
  have w45_40 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m45]; exact w44_40
  have w45_44 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m45]; exact w44_44
  have w45_48 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m45]; exact w44_48
  have w45_4c : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m45]; exact w44_4c
  have w45_50 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m45]; exact w44_50
  have w45_68 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m45]; exact w44_68
  have w45_70 : memLoad32 n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = sgp := by rw [m45]; exact w44_70
  have b45_170 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = (0 : BitVec 8) := by rw [m45]; exact b44_170
  have b45_171 : n45.mem (B + 0x21A0 + BitVec.ofNat 32 0x171) = BitVec.ofNat 8 ((sr43).getD 0 0) := by rw [m45]; exact b44_171
  have q45_171 : ∀ j, j < 32 → n45.mem (B + 0x21A0 + BitVec.ofNat 32 (0x171 + j)) = BitVec.ofNat 8 ((sr43).getD j 0) := fun j hj => by rw [m45]; exact q44_171 j hj
  have q45_191 : ∀ j, j < 32 → n45.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => by rw [m45]; exact q44_191 j hj
  clear q44_191 q44_171 b44_170 w44_70 w44_68 w44_50 w44_4c w44_48 w44_44 w44_40 w44_3c w44_38 w44_34 w44_30 g44_10 g44_26 g44_24 g44_23 g44_22 g44_21 g44_20 g44_19 g44_18 g44_4 g44_3 g44_2 V44 E44 fR44 t44 fr44 m44 s44 u44 d44
  -- 0xA0E: branch, not taken
  obtain ⟨n46, d46, u46⟩ := s45.notTaken E45.self 0xA12 sv_at_a0e
    (by decide) (by rw [g45_10, s45.zero]; decide)
  have s46 : St n46.mem SV n46 0xA12 (reg n46) := ⟨u46.pc, rfl, fun _ => rfl⟩
  have m46 : n46.mem = n45.mem := u46.mem
  have fr46 : ∀ x, SvR B x → n46.mem x = n45.mem x := fun x _ => by rw [m46]
  have t46 : Steps n0 n46 := t45.trans (.single d46)
  have fR46 : ∀ x, SvR B x → n46.mem x = M0 x := fun x hx => (fr46 x hx).trans (fR45 x hx)
  have E46 : SvCode n46.mem := E45.fr F fr46
  have V46 : SvSaves B n46.mem v := V45.same m46
  have g46_2 : reg n46 sp = B + 0x21A0 := by rw [u46.regs, g45_2]
  have g46_3 : reg n46 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [u46.regs, g45_3]
  have g46_4 : reg n46 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [u46.regs, g45_4]
  have g46_8 : reg n46 (8 : Fin 32) = (BitVec.ofNat 8 ((sr43).getD 0 0)).zeroExtend 32 := by rw [u46.regs, g45_8]
  have g46_10 : reg n46 a0 = ((0 : BitVec 8)).zeroExtend 32 := by rw [u46.regs, g45_10]
  have g46_18 : reg n46 (18 : Fin 32) = out := by rw [u46.regs, g45_18]
  have g46_19 : reg n46 (19 : Fin 32) = bp := by rw [u46.regs, g45_19]
  have g46_20 : reg n46 (20 : Fin 32) = x20 := by rw [u46.regs, g45_20]
  have g46_21 : reg n46 (21 : Fin 32) = x21 := by rw [u46.regs, g45_21]
  have g46_22 : reg n46 (22 : Fin 32) = x22 := by rw [u46.regs, g45_22]
  have g46_23 : reg n46 (23 : Fin 32) = q := by rw [u46.regs, g45_23]
  have g46_24 : reg n46 (24 : Fin 32) = x24 := by rw [u46.regs, g45_24]
  have g46_26 : reg n46 (26 : Fin 32) = x26 := by rw [u46.regs, g45_26]
  have keep_kk46 : SvKeepL B n0.mem n46.mem [(0x70, 0x4), (0x68, 0x4), (0x170, 0x41)] := by rw [m46]; exact keep_kk45
  clear keep_kk45
  have w46_30 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m46]; exact w45_30
  have w46_34 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m46]; exact w45_34
  have w46_38 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m46]; exact w45_38
  have w46_3c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m46]; exact w45_3c
  have w46_40 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m46]; exact w45_40
  have w46_44 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m46]; exact w45_44
  have w46_48 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m46]; exact w45_48
  have w46_4c : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m46]; exact w45_4c
  have w46_50 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m46]; exact w45_50
  have w46_68 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m46]; exact w45_68
  have w46_70 : memLoad32 n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = sgp := by rw [m46]; exact w45_70
  have b46_170 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = (0 : BitVec 8) := by rw [m46]; exact b45_170
  have b46_171 : n46.mem (B + 0x21A0 + BitVec.ofNat 32 0x171) = BitVec.ofNat 8 ((sr43).getD 0 0) := by rw [m46]; exact b45_171
  have q46_171 : ∀ j, j < 32 → n46.mem (B + 0x21A0 + BitVec.ofNat 32 (0x171 + j)) = BitVec.ofNat 8 ((sr43).getD j 0) := fun j hj => by rw [m46]; exact q45_171 j hj
  have q46_191 : ∀ j, j < 32 → n46.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => by rw [m46]; exact q45_191 j hj
  clear q45_191 q45_171 b45_171 b45_170 w45_70 w45_68 w45_50 w45_4c w45_48 w45_44 w45_40 w45_3c w45_38 w45_34 w45_30 g45_8 g45_26 g45_24 g45_23 g45_22 g45_21 g45_20 g45_19 g45_18 g45_10 g45_4 g45_3 g45_2 V45 E45 fR45 t45 fr45 m45 s45 u45 d45 b44_171
  -- 0xA12
  obtain ⟨n47, c47, u47⟩ := s46.block svDpva12 E46.self svDpva12_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m47 : n47.mem = n46.mem := u47.mem
  have s47 : St n47.mem SV n47 0xA1E (reg n47) := ⟨u47.pc, rfl, fun _ => rfl⟩
  have rb47 : ∀ q, reg n47 q = (runBlock svDpva12 (n46.mem, reg n46)).2 q := fun q => by rw [u47.regs]
  have fr47 : ∀ x, SvR B x → n47.mem x = n46.mem x := fun x _ => by rw [m47]
  have t47 : Steps n0 n47 := t46.trans c47
  have fR47 : ∀ x, SvR B x → n47.mem x = M0 x := fun x hx => (fr47 x hx).trans (fR46 x hx)
  have E47 : SvCode n47.mem := E46.fr F fr47
  have V47 : SvSaves B n47.mem v := V46.same m47
  have g47_2 : reg n47 sp = B + 0x21A0 := by
    rw [rb47, runBlock_reg _ _ _ sp s46.zero (by decide), g46_2]
  have g47_3 : reg n47 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb47, runBlock_reg _ _ _ (3 : Fin 32) s46.zero (by decide), g46_3]
  have g47_4 : reg n47 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb47, runBlock_reg _ _ _ (4 : Fin 32) s46.zero (by decide), g46_4]
  have g47_8 : reg n47 (8 : Fin 32) = (BitVec.ofNat 8 ((sr43).getD 0 0)).zeroExtend 32 := by
    rw [rb47, runBlock_reg _ _ _ (8 : Fin 32) s46.zero (by decide), g46_8]
  have g47_18 : reg n47 (18 : Fin 32) = out := by
    rw [rb47, runBlock_reg _ _ _ (18 : Fin 32) s46.zero (by decide), g46_18]
  have g47_19 : reg n47 (19 : Fin 32) = bp := by
    rw [rb47, runBlock_reg _ _ _ (19 : Fin 32) s46.zero (by decide), g46_19]
  have g47_20 : reg n47 (20 : Fin 32) = x20 := by
    rw [rb47, runBlock_reg _ _ _ (20 : Fin 32) s46.zero (by decide), g46_20]
  have g47_21 : reg n47 (21 : Fin 32) = x21 := by
    rw [rb47, runBlock_reg _ _ _ (21 : Fin 32) s46.zero (by decide), g46_21]
  have g47_22 : reg n47 (22 : Fin 32) = x22 := by
    rw [rb47, runBlock_reg _ _ _ (22 : Fin 32) s46.zero (by decide), g46_22]
  have g47_23 : reg n47 (23 : Fin 32) = q := by
    rw [rb47, runBlock_reg _ _ _ (23 : Fin 32) s46.zero (by decide), g46_23]
  have g47_24 : reg n47 (24 : Fin 32) = x24 := by
    rw [rb47, runBlock_reg _ _ _ (24 : Fin 32) s46.zero (by decide), g46_24]
  have g47_26 : reg n47 (26 : Fin 32) = x26 := by
    rw [rb47, runBlock_reg _ _ _ (26 : Fin 32) s46.zero (by decide), g46_26]
  have g47_10 : reg n47 a0 = B + 0x21A0 + BitVec.ofNat 32 0x291 := by
    rw [rb47]; simp +decide only [runBlock, BInstr.run, svDpva12, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g46_2, g46_3, g46_4, g46_8, g46_10, g46_18, g46_19, g46_20, g46_21, g46_22, g46_23, g46_24, g46_26, s46.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g47_11 : reg n47 a1 = B + 0x21A0 + BitVec.ofNat 32 0x172 := by
    rw [rb47]; simp +decide only [runBlock, BInstr.run, svDpva12, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g46_2, g46_3, g46_4, g46_8, g46_10, g46_18, g46_19, g46_20, g46_21, g46_22, g46_23, g46_24, g46_26, s46.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g47_12 : reg n47 a2 = BitVec.ofNat 32 0x3F := by
    rw [rb47]; simp +decide only [runBlock, BInstr.run, svDpva12, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g46_2, g46_3, g46_4, g46_8, g46_10, g46_18, g46_19, g46_20, g46_21, g46_22, g46_23, g46_24, g46_26, s46.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk47 : SvKeepL B n0.mem n47.mem [(0x70, 0x4), (0x68, 0x4), (0x170, 0x41)] := by rw [m47]; exact keep_kk46
  clear keep_kk46
  have w47_30 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m47]; exact w46_30
  have w47_34 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m47]; exact w46_34
  have w47_38 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m47]; exact w46_38
  have w47_3c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m47]; exact w46_3c
  have w47_40 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m47]; exact w46_40
  have w47_44 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m47]; exact w46_44
  have w47_48 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m47]; exact w46_48
  have w47_4c : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m47]; exact w46_4c
  have w47_50 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m47]; exact w46_50
  have w47_68 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m47]; exact w46_68
  have w47_70 : memLoad32 n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = sgp := by rw [m47]; exact w46_70
  have b47_170 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = (0 : BitVec 8) := by rw [m47]; exact b46_170
  have b47_171 : n47.mem (B + 0x21A0 + BitVec.ofNat 32 0x171) = BitVec.ofNat 8 ((sr43).getD 0 0) := by rw [m47]; exact b46_171
  have q47_171 : ∀ j, j < 32 → n47.mem (B + 0x21A0 + BitVec.ofNat 32 (0x171 + j)) = BitVec.ofNat 8 ((sr43).getD j 0) := fun j hj => by rw [m47]; exact q46_171 j hj
  have q47_191 : ∀ j, j < 32 → n47.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => by rw [m47]; exact q46_191 j hj
  clear q46_191 q46_171 b46_171 b46_170 w46_70 w46_68 w46_50 w46_4c w46_48 w46_44 w46_40 w46_3c w46_38 w46_34 w46_30 g46_26 g46_24 g46_23 g46_22 g46_21 g46_20 g46_19 g46_18 g46_10 g46_8 g46_4 g46_3 g46_2 V46 E46 fR46 t46 fr46 m46 s46 u46 d46
  -- 0xA1E: memcpy
  obtain ⟨n48, P48, K48, X48⟩ := sv_mc (c := 0x291) (d := 0x172) (N := 0x3F) F E47 s47 sv_at_a1e sv_at_a22
    (by decide) (by decide) g47_2 g47_10 g47_11 g47_12
    (by decide) (by decide) (by decide)
  have s48 := P48.st
  have fr48 := P48.fr
  have t48 : Steps n0 n48 := t47.trans P48.steps
  have fR48 : ∀ x, SvR B x → n48.mem x = M0 x := fun x hx => (fr48 x hx).trans (fR47 x hx)
  have E48 : SvCode n48.mem := E47.fr F fr48
  have V48 : SvSaves B n48.mem v := V47.keep K48 (by decide)
  have g48_2 : reg n48 sp = B + 0x21A0 := by rw [P48.regs sp (by decide), g47_2]
  have g48_3 : reg n48 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P48.regs (3 : Fin 32) (by decide), g47_3]
  have g48_4 : reg n48 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P48.regs (4 : Fin 32) (by decide), g47_4]
  have g48_8 : reg n48 (8 : Fin 32) = (BitVec.ofNat 8 ((sr43).getD 0 0)).zeroExtend 32 := by rw [P48.regs (8 : Fin 32) (by decide), g47_8]
  have g48_18 : reg n48 (18 : Fin 32) = out := by rw [P48.regs (18 : Fin 32) (by decide), g47_18]
  have g48_19 : reg n48 (19 : Fin 32) = bp := by rw [P48.regs (19 : Fin 32) (by decide), g47_19]
  have g48_20 : reg n48 (20 : Fin 32) = x20 := by rw [P48.regs (20 : Fin 32) (by decide), g47_20]
  have g48_21 : reg n48 (21 : Fin 32) = x21 := by rw [P48.regs (21 : Fin 32) (by decide), g47_21]
  have g48_22 : reg n48 (22 : Fin 32) = x22 := by rw [P48.regs (22 : Fin 32) (by decide), g47_22]
  have g48_23 : reg n48 (23 : Fin 32) = q := by rw [P48.regs (23 : Fin 32) (by decide), g47_23]
  have g48_24 : reg n48 (24 : Fin 32) = x24 := by rw [P48.regs (24 : Fin 32) (by decide), g47_24]
  have g48_26 : reg n48 (26 : Fin 32) = x26 := by rw [P48.regs (26 : Fin 32) (by decide), g47_26]
  have keep_kk48 : SvKeepL B n0.mem n48.mem [(0x70, 0x4), (0x68, 0x4), (0x170, 0x41), (0x291, 0x3F)] := keep_kk47.trans K48.toL
  clear keep_kk47
  have w48_30 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K48.w32 (by decide) (by decide)).trans w47_30
  have w48_34 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K48.w32 (by decide) (by decide)).trans w47_34
  have w48_38 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K48.w32 (by decide) (by decide)).trans w47_38
  have w48_3c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K48.w32 (by decide) (by decide)).trans w47_3c
  have w48_40 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K48.w32 (by decide) (by decide)).trans w47_40
  have w48_44 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K48.w32 (by decide) (by decide)).trans w47_44
  have w48_48 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K48.w32 (by decide) (by decide)).trans w47_48
  have w48_4c : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K48.w32 (by decide) (by decide)).trans w47_4c
  have w48_50 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K48.w32 (by decide) (by decide)).trans w47_50
  have w48_68 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K48.w32 (by decide) (by decide)).trans w47_68
  have w48_70 : memLoad32 n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = sgp := (K48.w32 (by decide) (by decide)).trans w47_70
  have b48_170 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = (0 : BitVec 8) := (K48.b8 (by decide) (by decide)).trans b47_170
  have b48_171 : n48.mem (B + 0x21A0 + BitVec.ofNat 32 0x171) = BitVec.ofNat 8 ((sr43).getD 0 0) := (K48.b8 (by decide) (by decide)).trans b47_171
  have q48_171 : ∀ j, j < 32 → n48.mem (B + 0x21A0 + BitVec.ofNat 32 (0x171 + j)) = BitVec.ofNat 8 ((sr43).getD j 0) := fun j hj => (K48.range (by decide) (by decide) j hj).trans (q47_171 j hj)
  have q48_191 : ∀ j, j < 32 → n48.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => (K48.range (by decide) (by decide) j hj).trans (q47_191 j hj)
  have q48_291 : ∀ j, j < 31 → n48.mem (B + 0x21A0 + BitVec.ofNat 32 (0x291 + j)) = BitVec.ofNat 8 ((sr43).getD (1 + j) 0) := fun j hj => by
    rw [show 0x291 + j = 0x291 + (0x0 + j) by omega, X48 (0x0 + j) (by omega),
      show 0x172 + (0x0 + j) = 0x171 + (1 + j) by omega]; exact q47_171 (1 + j) (by omega)
  have q48_2b0 : ∀ j, j < 32 → n48.mem (B + 0x21A0 + BitVec.ofNat 32 (0x2B0 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => by
    rw [show 0x2B0 + j = 0x291 + (0x1F + j) by omega, X48 (0x1F + j) (by omega),
      show 0x172 + (0x1F + j) = 0x191 + j by omega]; exact q47_191 j (by omega)
  clear q47_191 q47_171 b47_171 b47_170 w47_70 w47_68 w47_50 w47_4c w47_48 w47_44 w47_40 w47_3c w47_38 w47_34 w47_30 g47_12 g47_11 g47_10 g47_26 g47_24 g47_23 g47_22 g47_21 g47_20 g47_19 g47_18 g47_8 g47_4 g47_3 g47_2 V47 E47 fR47 t47 fr47 rb47 s47 m47 u47 c47
  -- 0xA26: sb
  obtain ⟨n49, d49, s49, fr49, K49, W49, rg49⟩ := sv_sb F E48 s48 sv_at_a26 (off' := 0xA2A) (c := 0x130)
    (by decide) (by rw [g48_2]; sv_addr) (by decide)
  have t49 : Steps n0 n49 := t48.trans d49
  have fR49 : ∀ x, SvR B x → n49.mem x = M0 x := fun x hx => (fr49 x hx).trans (fR48 x hx)
  have E49 : SvCode n49.mem := E48.fr F fr49
  have V49 : SvSaves B n49.mem v := V48.keep K49 (by decide)
  have g49_2 : reg n49 sp = B + 0x21A0 := by rw [rg49 sp, g48_2]
  have g49_3 : reg n49 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [rg49 (3 : Fin 32), g48_3]
  have g49_4 : reg n49 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [rg49 (4 : Fin 32), g48_4]
  have g49_8 : reg n49 (8 : Fin 32) = (BitVec.ofNat 8 ((sr43).getD 0 0)).zeroExtend 32 := by rw [rg49 (8 : Fin 32), g48_8]
  have g49_18 : reg n49 (18 : Fin 32) = out := by rw [rg49 (18 : Fin 32), g48_18]
  have g49_19 : reg n49 (19 : Fin 32) = bp := by rw [rg49 (19 : Fin 32), g48_19]
  have g49_20 : reg n49 (20 : Fin 32) = x20 := by rw [rg49 (20 : Fin 32), g48_20]
  have g49_21 : reg n49 (21 : Fin 32) = x21 := by rw [rg49 (21 : Fin 32), g48_21]
  have g49_22 : reg n49 (22 : Fin 32) = x22 := by rw [rg49 (22 : Fin 32), g48_22]
  have g49_23 : reg n49 (23 : Fin 32) = q := by rw [rg49 (23 : Fin 32), g48_23]
  have g49_24 : reg n49 (24 : Fin 32) = x24 := by rw [rg49 (24 : Fin 32), g48_24]
  have g49_26 : reg n49 (26 : Fin 32) = x26 := by rw [rg49 (26 : Fin 32), g48_26]
  have keep_kk49 : SvKeepL B n0.mem n49.mem [(0x70, 0x4), (0x68, 0x4), (0x170, 0x41), (0x291, 0x3F), (0x130, 0x1)] := keep_kk48.trans K49.toL
  clear keep_kk48
  have w49_30 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K49.w32 (by decide) (by decide)).trans w48_30
  have w49_34 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K49.w32 (by decide) (by decide)).trans w48_34
  have w49_38 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K49.w32 (by decide) (by decide)).trans w48_38
  have w49_3c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K49.w32 (by decide) (by decide)).trans w48_3c
  have w49_40 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K49.w32 (by decide) (by decide)).trans w48_40
  have w49_44 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K49.w32 (by decide) (by decide)).trans w48_44
  have w49_48 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K49.w32 (by decide) (by decide)).trans w48_48
  have w49_4c : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K49.w32 (by decide) (by decide)).trans w48_4c
  have w49_50 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K49.w32 (by decide) (by decide)).trans w48_50
  have w49_68 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K49.w32 (by decide) (by decide)).trans w48_68
  have w49_70 : memLoad32 n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = sgp := (K49.w32 (by decide) (by decide)).trans w48_70
  have b49_170 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = (0 : BitVec 8) := (K49.b8 (by decide) (by decide)).trans b48_170
  have b49_171 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x171) = BitVec.ofNat 8 ((sr43).getD 0 0) := (K49.b8 (by decide) (by decide)).trans b48_171
  have b49_130 : n49.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = BitVec.ofNat 8 ((sr43).getD 0 0) := by rw [W49, g48_8, lbu_low]
  have q49_171 : ∀ j, j < 32 → n49.mem (B + 0x21A0 + BitVec.ofNat 32 (0x171 + j)) = BitVec.ofNat 8 ((sr43).getD j 0) := fun j hj => (K49.range (by decide) (by decide) j hj).trans (q48_171 j hj)
  have q49_191 : ∀ j, j < 32 → n49.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => (K49.range (by decide) (by decide) j hj).trans (q48_191 j hj)
  have q49_291 : ∀ j, j < 31 → n49.mem (B + 0x21A0 + BitVec.ofNat 32 (0x291 + j)) = BitVec.ofNat 8 ((sr43).getD (1 + j) 0) := fun j hj => (K49.range (by decide) (by decide) j hj).trans (q48_291 j hj)
  have q49_2b0 : ∀ j, j < 32 → n49.mem (B + 0x21A0 + BitVec.ofNat 32 (0x2B0 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => (K49.range (by decide) (by decide) j hj).trans (q48_2b0 j hj)
  clear q48_2b0 q48_291 q48_191 q48_171 b48_171 b48_170 w48_70 w48_68 w48_50 w48_4c w48_48 w48_44 w48_40 w48_3c w48_38 w48_34 w48_30 g48_26 g48_24 g48_23 g48_22 g48_21 g48_20 g48_19 g48_18 g48_8 g48_4 g48_3 g48_2 V48 E48 fR48 t48 fr48 s48 X48 K48 P48
  -- 0xA2A
  obtain ⟨n50, c50, u50⟩ := s49.block svDpva2a E49.self svDpva2a_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m50 : n50.mem = n49.mem := u50.mem
  have s50 : St n50.mem SV n50 0xA34 (reg n50) := ⟨u50.pc, rfl, fun _ => rfl⟩
  have rb50 : ∀ q, reg n50 q = (runBlock svDpva2a (n49.mem, reg n49)).2 q := fun q => by rw [u50.regs]
  have fr50 : ∀ x, SvR B x → n50.mem x = n49.mem x := fun x _ => by rw [m50]
  have t50 : Steps n0 n50 := t49.trans c50
  have fR50 : ∀ x, SvR B x → n50.mem x = M0 x := fun x hx => (fr50 x hx).trans (fR49 x hx)
  have E50 : SvCode n50.mem := E49.fr F fr50
  have V50 : SvSaves B n50.mem v := V49.same m50
  have g50_2 : reg n50 sp = B + 0x21A0 := by
    rw [rb50, runBlock_reg _ _ _ sp s49.zero (by decide), g49_2]
  have g50_3 : reg n50 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb50, runBlock_reg _ _ _ (3 : Fin 32) s49.zero (by decide), g49_3]
  have g50_4 : reg n50 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb50, runBlock_reg _ _ _ (4 : Fin 32) s49.zero (by decide), g49_4]
  have g50_8 : reg n50 (8 : Fin 32) = (BitVec.ofNat 8 ((sr43).getD 0 0)).zeroExtend 32 := by
    rw [rb50, runBlock_reg _ _ _ (8 : Fin 32) s49.zero (by decide), g49_8]
  have g50_18 : reg n50 (18 : Fin 32) = out := by
    rw [rb50, runBlock_reg _ _ _ (18 : Fin 32) s49.zero (by decide), g49_18]
  have g50_19 : reg n50 (19 : Fin 32) = bp := by
    rw [rb50, runBlock_reg _ _ _ (19 : Fin 32) s49.zero (by decide), g49_19]
  have g50_20 : reg n50 (20 : Fin 32) = x20 := by
    rw [rb50, runBlock_reg _ _ _ (20 : Fin 32) s49.zero (by decide), g49_20]
  have g50_21 : reg n50 (21 : Fin 32) = x21 := by
    rw [rb50, runBlock_reg _ _ _ (21 : Fin 32) s49.zero (by decide), g49_21]
  have g50_22 : reg n50 (22 : Fin 32) = x22 := by
    rw [rb50, runBlock_reg _ _ _ (22 : Fin 32) s49.zero (by decide), g49_22]
  have g50_23 : reg n50 (23 : Fin 32) = q := by
    rw [rb50, runBlock_reg _ _ _ (23 : Fin 32) s49.zero (by decide), g49_23]
  have g50_24 : reg n50 (24 : Fin 32) = x24 := by
    rw [rb50, runBlock_reg _ _ _ (24 : Fin 32) s49.zero (by decide), g49_24]
  have g50_26 : reg n50 (26 : Fin 32) = x26 := by
    rw [rb50, runBlock_reg _ _ _ (26 : Fin 32) s49.zero (by decide), g49_26]
  have g50_10 : reg n50 a0 = B + 0x21A0 + BitVec.ofNat 32 0x131 := by
    rw [rb50]; simp +decide only [runBlock, BInstr.run, svDpva2a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g49_2, g49_3, g49_4, g49_8, g49_18, g49_19, g49_20, g49_21, g49_22, g49_23, g49_24, g49_26, s49.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g50_11 : reg n50 a1 = B + 0x21A0 + BitVec.ofNat 32 0x291 := by
    rw [rb50]; simp +decide only [runBlock, BInstr.run, svDpva2a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g49_2, g49_3, g49_4, g49_8, g49_18, g49_19, g49_20, g49_21, g49_22, g49_23, g49_24, g49_26, s49.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g50_12 : reg n50 a2 = BitVec.ofNat 32 0x1F := by
    rw [rb50]; simp +decide only [runBlock, BInstr.run, svDpva2a, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g49_2, g49_3, g49_4, g49_8, g49_18, g49_19, g49_20, g49_21, g49_22, g49_23, g49_24, g49_26, s49.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk50 : SvKeepL B n0.mem n50.mem [(0x70, 0x4), (0x68, 0x4), (0x170, 0x41), (0x291, 0x3F), (0x130, 0x1)] := by rw [m50]; exact keep_kk49
  clear keep_kk49
  have w50_30 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m50]; exact w49_30
  have w50_34 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m50]; exact w49_34
  have w50_38 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m50]; exact w49_38
  have w50_3c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m50]; exact w49_3c
  have w50_40 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m50]; exact w49_40
  have w50_44 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m50]; exact w49_44
  have w50_48 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m50]; exact w49_48
  have w50_4c : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m50]; exact w49_4c
  have w50_50 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m50]; exact w49_50
  have w50_68 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m50]; exact w49_68
  have w50_70 : memLoad32 n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = sgp := by rw [m50]; exact w49_70
  have b50_130 : n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = BitVec.ofNat 8 ((sr43).getD 0 0) := by rw [m50]; exact b49_130
  have b50_170 : n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = (0 : BitVec 8) := by rw [m50]; exact b49_170
  have b50_171 : n50.mem (B + 0x21A0 + BitVec.ofNat 32 0x171) = BitVec.ofNat 8 ((sr43).getD 0 0) := by rw [m50]; exact b49_171
  have q50_171 : ∀ j, j < 32 → n50.mem (B + 0x21A0 + BitVec.ofNat 32 (0x171 + j)) = BitVec.ofNat 8 ((sr43).getD j 0) := fun j hj => by rw [m50]; exact q49_171 j hj
  have q50_191 : ∀ j, j < 32 → n50.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => by rw [m50]; exact q49_191 j hj
  have q50_291 : ∀ j, j < 31 → n50.mem (B + 0x21A0 + BitVec.ofNat 32 (0x291 + j)) = BitVec.ofNat 8 ((sr43).getD (1 + j) 0) := fun j hj => by rw [m50]; exact q49_291 j hj
  have q50_2b0 : ∀ j, j < 32 → n50.mem (B + 0x21A0 + BitVec.ofNat 32 (0x2B0 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => by rw [m50]; exact q49_2b0 j hj
  clear q49_2b0 q49_291 q49_191 q49_171 b49_130 b49_171 b49_170 w49_70 w49_68 w49_50 w49_4c w49_48 w49_44 w49_40 w49_3c w49_38 w49_34 w49_30 g49_26 g49_24 g49_23 g49_22 g49_21 g49_20 g49_19 g49_18 g49_8 g49_4 g49_3 g49_2 V49 E49 fR49 t49 rg49 W49 K49 fr49 s49 d49
  -- 0xA34: memcpy
  obtain ⟨n51, P51, K51, X51⟩ := sv_mc (c := 0x131) (d := 0x291) (N := 0x1F) F E50 s50 sv_at_a34 sv_at_a38
    (by decide) (by decide) g50_2 g50_10 g50_11 g50_12
    (by decide) (by decide) (by decide)
  have s51 := P51.st
  have fr51 := P51.fr
  have t51 : Steps n0 n51 := t50.trans P51.steps
  have fR51 : ∀ x, SvR B x → n51.mem x = M0 x := fun x hx => (fr51 x hx).trans (fR50 x hx)
  have E51 : SvCode n51.mem := E50.fr F fr51
  have V51 : SvSaves B n51.mem v := V50.keep K51 (by decide)
  have g51_2 : reg n51 sp = B + 0x21A0 := by rw [P51.regs sp (by decide), g50_2]
  have g51_3 : reg n51 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P51.regs (3 : Fin 32) (by decide), g50_3]
  have g51_4 : reg n51 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P51.regs (4 : Fin 32) (by decide), g50_4]
  have g51_8 : reg n51 (8 : Fin 32) = (BitVec.ofNat 8 ((sr43).getD 0 0)).zeroExtend 32 := by rw [P51.regs (8 : Fin 32) (by decide), g50_8]
  have g51_18 : reg n51 (18 : Fin 32) = out := by rw [P51.regs (18 : Fin 32) (by decide), g50_18]
  have g51_19 : reg n51 (19 : Fin 32) = bp := by rw [P51.regs (19 : Fin 32) (by decide), g50_19]
  have g51_20 : reg n51 (20 : Fin 32) = x20 := by rw [P51.regs (20 : Fin 32) (by decide), g50_20]
  have g51_21 : reg n51 (21 : Fin 32) = x21 := by rw [P51.regs (21 : Fin 32) (by decide), g50_21]
  have g51_22 : reg n51 (22 : Fin 32) = x22 := by rw [P51.regs (22 : Fin 32) (by decide), g50_22]
  have g51_23 : reg n51 (23 : Fin 32) = q := by rw [P51.regs (23 : Fin 32) (by decide), g50_23]
  have g51_24 : reg n51 (24 : Fin 32) = x24 := by rw [P51.regs (24 : Fin 32) (by decide), g50_24]
  have g51_26 : reg n51 (26 : Fin 32) = x26 := by rw [P51.regs (26 : Fin 32) (by decide), g50_26]
  have keep_kk51 : SvKeepL B n0.mem n51.mem [(0x70, 0x4), (0x68, 0x4), (0x170, 0x41), (0x291, 0x3F), (0x130, 0x1), (0x131, 0x1F)] := keep_kk50.trans K51.toL
  clear keep_kk50
  have w51_30 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K51.w32 (by decide) (by decide)).trans w50_30
  have w51_34 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K51.w32 (by decide) (by decide)).trans w50_34
  have w51_38 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K51.w32 (by decide) (by decide)).trans w50_38
  have w51_3c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K51.w32 (by decide) (by decide)).trans w50_3c
  have w51_40 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K51.w32 (by decide) (by decide)).trans w50_40
  have w51_44 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K51.w32 (by decide) (by decide)).trans w50_44
  have w51_48 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K51.w32 (by decide) (by decide)).trans w50_48
  have w51_4c : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K51.w32 (by decide) (by decide)).trans w50_4c
  have w51_50 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K51.w32 (by decide) (by decide)).trans w50_50
  have w51_68 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K51.w32 (by decide) (by decide)).trans w50_68
  have w51_70 : memLoad32 n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = sgp := (K51.w32 (by decide) (by decide)).trans w50_70
  have b51_130 : n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = BitVec.ofNat 8 ((sr43).getD 0 0) := (K51.b8 (by decide) (by decide)).trans b50_130
  have b51_170 : n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = (0 : BitVec 8) := (K51.b8 (by decide) (by decide)).trans b50_170
  have b51_171 : n51.mem (B + 0x21A0 + BitVec.ofNat 32 0x171) = BitVec.ofNat 8 ((sr43).getD 0 0) := (K51.b8 (by decide) (by decide)).trans b50_171
  have q51_171 : ∀ j, j < 32 → n51.mem (B + 0x21A0 + BitVec.ofNat 32 (0x171 + j)) = BitVec.ofNat 8 ((sr43).getD j 0) := fun j hj => (K51.range (by decide) (by decide) j hj).trans (q50_171 j hj)
  have q51_191 : ∀ j, j < 32 → n51.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => (K51.range (by decide) (by decide) j hj).trans (q50_191 j hj)
  have q51_291 : ∀ j, j < 31 → n51.mem (B + 0x21A0 + BitVec.ofNat 32 (0x291 + j)) = BitVec.ofNat 8 ((sr43).getD (1 + j) 0) := fun j hj => (K51.range (by decide) (by decide) j hj).trans (q50_291 j hj)
  have q51_2b0 : ∀ j, j < 32 → n51.mem (B + 0x21A0 + BitVec.ofNat 32 (0x2B0 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => (K51.range (by decide) (by decide) j hj).trans (q50_2b0 j hj)
  have q51_131 : ∀ j, j < 31 → n51.mem (B + 0x21A0 + BitVec.ofNat 32 (0x131 + j)) = BitVec.ofNat 8 ((sr43).getD (1 + j) 0) := fun j hj => by
    rw [show 0x131 + j = 0x131 + (0x0 + j) by omega, X51 (0x0 + j) (by omega),
      show 0x291 + (0x0 + j) = 0x291 + j by omega]; exact q50_291 j (by omega)
  clear q50_2b0 q50_291 q50_191 q50_171 b50_171 b50_170 b50_130 w50_70 w50_68 w50_50 w50_4c w50_48 w50_44 w50_40 w50_3c w50_38 w50_34 w50_30 g50_12 g50_11 g50_10 g50_26 g50_24 g50_23 g50_22 g50_21 g50_20 g50_19 g50_18 g50_8 g50_4 g50_3 g50_2 V50 E50 fR50 t50 fr50 rb50 s50 m50 u50 c50
  -- 0xA3C
  obtain ⟨n52, c52, u52⟩ := s51.block svDpva3c E51.self svDpva3c_end
    ⟨trivial, trivial, trivial, trivial⟩
  have m52 : n52.mem = n51.mem := u52.mem
  have s52 : St n52.mem SV n52 0xA44 (reg n52) := ⟨u52.pc, rfl, fun _ => rfl⟩
  have rb52 : ∀ q, reg n52 q = (runBlock svDpva3c (n51.mem, reg n51)).2 q := fun q => by rw [u52.regs]
  have fr52 : ∀ x, SvR B x → n52.mem x = n51.mem x := fun x _ => by rw [m52]
  have t52 : Steps n0 n52 := t51.trans c52
  have fR52 : ∀ x, SvR B x → n52.mem x = M0 x := fun x hx => (fr52 x hx).trans (fR51 x hx)
  have E52 : SvCode n52.mem := E51.fr F fr52
  have V52 : SvSaves B n52.mem v := V51.same m52
  have g52_2 : reg n52 sp = B + 0x21A0 := by
    rw [rb52, runBlock_reg _ _ _ sp s51.zero (by decide), g51_2]
  have g52_3 : reg n52 (3 : Fin 32) = reg n0 (3 : Fin 32) := by
    rw [rb52, runBlock_reg _ _ _ (3 : Fin 32) s51.zero (by decide), g51_3]
  have g52_4 : reg n52 (4 : Fin 32) = reg n0 (4 : Fin 32) := by
    rw [rb52, runBlock_reg _ _ _ (4 : Fin 32) s51.zero (by decide), g51_4]
  have g52_8 : reg n52 (8 : Fin 32) = (BitVec.ofNat 8 ((sr43).getD 0 0)).zeroExtend 32 := by
    rw [rb52, runBlock_reg _ _ _ (8 : Fin 32) s51.zero (by decide), g51_8]
  have g52_18 : reg n52 (18 : Fin 32) = out := by
    rw [rb52, runBlock_reg _ _ _ (18 : Fin 32) s51.zero (by decide), g51_18]
  have g52_19 : reg n52 (19 : Fin 32) = bp := by
    rw [rb52, runBlock_reg _ _ _ (19 : Fin 32) s51.zero (by decide), g51_19]
  have g52_20 : reg n52 (20 : Fin 32) = x20 := by
    rw [rb52, runBlock_reg _ _ _ (20 : Fin 32) s51.zero (by decide), g51_20]
  have g52_21 : reg n52 (21 : Fin 32) = x21 := by
    rw [rb52, runBlock_reg _ _ _ (21 : Fin 32) s51.zero (by decide), g51_21]
  have g52_22 : reg n52 (22 : Fin 32) = x22 := by
    rw [rb52, runBlock_reg _ _ _ (22 : Fin 32) s51.zero (by decide), g51_22]
  have g52_23 : reg n52 (23 : Fin 32) = q := by
    rw [rb52, runBlock_reg _ _ _ (23 : Fin 32) s51.zero (by decide), g51_23]
  have g52_24 : reg n52 (24 : Fin 32) = x24 := by
    rw [rb52, runBlock_reg _ _ _ (24 : Fin 32) s51.zero (by decide), g51_24]
  have g52_26 : reg n52 (26 : Fin 32) = x26 := by
    rw [rb52, runBlock_reg _ _ _ (26 : Fin 32) s51.zero (by decide), g51_26]
  have g52_10 : reg n52 a0 = B + 0x21A0 + BitVec.ofNat 32 0x150 := by
    rw [rb52]; simp +decide only [runBlock, BInstr.run, svDpva3c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g51_2, g51_3, g51_4, g51_8, g51_18, g51_19, g51_20, g51_21, g51_22, g51_23, g51_24, g51_26, s51.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g52_11 : reg n52 a1 = B + 0x21A0 + BitVec.ofNat 32 0x2B0 := by
    rw [rb52]; simp +decide only [runBlock, BInstr.run, svDpva3c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g51_2, g51_3, g51_4, g51_8, g51_18, g51_19, g51_20, g51_21, g51_22, g51_23, g51_24, g51_26, s51.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have g52_12 : reg n52 a2 = BitVec.ofNat 32 0x20 := by
    rw [rb52]; simp +decide only [runBlock, BInstr.run, svDpva3c, upd, ↓reduceIte, aluEval]
    all_goals (try simp only [g51_2, g51_3, g51_4, g51_8, g51_18, g51_19, g51_20, g51_21, g51_22, g51_23, g51_24, g51_26, s51.zero])
    all_goals first | with_reducible rfl | sv_addr | decide
  have keep_kk52 : SvKeepL B n0.mem n52.mem [(0x70, 0x4), (0x68, 0x4), (0x170, 0x41), (0x291, 0x3F), (0x130, 0x1), (0x131, 0x1F)] := by rw [m52]; exact keep_kk51
  clear keep_kk51
  have w52_30 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := by rw [m52]; exact w51_30
  have w52_34 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := by rw [m52]; exact w51_34
  have w52_38 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := by rw [m52]; exact w51_38
  have w52_3c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := by rw [m52]; exact w51_3c
  have w52_40 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := by rw [m52]; exact w51_40
  have w52_44 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := by rw [m52]; exact w51_44
  have w52_48 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m52]; exact w51_48
  have w52_4c : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m52]; exact w51_4c
  have w52_50 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := by rw [m52]; exact w51_50
  have w52_68 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := by rw [m52]; exact w51_68
  have w52_70 : memLoad32 n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = sgp := by rw [m52]; exact w51_70
  have b52_130 : n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = BitVec.ofNat 8 ((sr43).getD 0 0) := by rw [m52]; exact b51_130
  have b52_170 : n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = (0 : BitVec 8) := by rw [m52]; exact b51_170
  have b52_171 : n52.mem (B + 0x21A0 + BitVec.ofNat 32 0x171) = BitVec.ofNat 8 ((sr43).getD 0 0) := by rw [m52]; exact b51_171
  have q52_131 : ∀ j, j < 31 → n52.mem (B + 0x21A0 + BitVec.ofNat 32 (0x131 + j)) = BitVec.ofNat 8 ((sr43).getD (1 + j) 0) := fun j hj => by rw [m52]; exact q51_131 j hj
  have q52_171 : ∀ j, j < 32 → n52.mem (B + 0x21A0 + BitVec.ofNat 32 (0x171 + j)) = BitVec.ofNat 8 ((sr43).getD j 0) := fun j hj => by rw [m52]; exact q51_171 j hj
  have q52_191 : ∀ j, j < 32 → n52.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => by rw [m52]; exact q51_191 j hj
  have q52_291 : ∀ j, j < 31 → n52.mem (B + 0x21A0 + BitVec.ofNat 32 (0x291 + j)) = BitVec.ofNat 8 ((sr43).getD (1 + j) 0) := fun j hj => by rw [m52]; exact q51_291 j hj
  have q52_2b0 : ∀ j, j < 32 → n52.mem (B + 0x21A0 + BitVec.ofNat 32 (0x2B0 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => by rw [m52]; exact q51_2b0 j hj
  clear q51_131 q51_2b0 q51_291 q51_191 q51_171 b51_171 b51_170 b51_130 w51_70 w51_68 w51_50 w51_4c w51_48 w51_44 w51_40 w51_3c w51_38 w51_34 w51_30 g51_26 g51_24 g51_23 g51_22 g51_21 g51_20 g51_19 g51_18 g51_8 g51_4 g51_3 g51_2 V51 E51 fR51 t51 fr51 s51 X51 K51 P51
  -- 0xA44: memcpy
  obtain ⟨n53, P53, K53, X53⟩ := sv_mc (c := 0x150) (d := 0x2B0) (N := 0x20) F E52 s52 sv_at_a44 sv_at_a48
    (by decide) (by decide) g52_2 g52_10 g52_11 g52_12
    (by decide) (by decide) (by decide)
  have s53 := P53.st
  have fr53 := P53.fr
  have t53 : Steps n0 n53 := t52.trans P53.steps
  have fR53 : ∀ x, SvR B x → n53.mem x = M0 x := fun x hx => (fr53 x hx).trans (fR52 x hx)
  have E53 : SvCode n53.mem := E52.fr F fr53
  have V53 : SvSaves B n53.mem v := V52.keep K53 (by decide)
  have g53_2 : reg n53 sp = B + 0x21A0 := by rw [P53.regs sp (by decide), g52_2]
  have g53_3 : reg n53 (3 : Fin 32) = reg n0 (3 : Fin 32) := by rw [P53.regs (3 : Fin 32) (by decide), g52_3]
  have g53_4 : reg n53 (4 : Fin 32) = reg n0 (4 : Fin 32) := by rw [P53.regs (4 : Fin 32) (by decide), g52_4]
  have g53_8 : reg n53 (8 : Fin 32) = (BitVec.ofNat 8 ((sr43).getD 0 0)).zeroExtend 32 := by rw [P53.regs (8 : Fin 32) (by decide), g52_8]
  have g53_18 : reg n53 (18 : Fin 32) = out := by rw [P53.regs (18 : Fin 32) (by decide), g52_18]
  have g53_19 : reg n53 (19 : Fin 32) = bp := by rw [P53.regs (19 : Fin 32) (by decide), g52_19]
  have g53_20 : reg n53 (20 : Fin 32) = x20 := by rw [P53.regs (20 : Fin 32) (by decide), g52_20]
  have g53_21 : reg n53 (21 : Fin 32) = x21 := by rw [P53.regs (21 : Fin 32) (by decide), g52_21]
  have g53_22 : reg n53 (22 : Fin 32) = x22 := by rw [P53.regs (22 : Fin 32) (by decide), g52_22]
  have g53_23 : reg n53 (23 : Fin 32) = q := by rw [P53.regs (23 : Fin 32) (by decide), g52_23]
  have g53_24 : reg n53 (24 : Fin 32) = x24 := by rw [P53.regs (24 : Fin 32) (by decide), g52_24]
  have g53_26 : reg n53 (26 : Fin 32) = x26 := by rw [P53.regs (26 : Fin 32) (by decide), g52_26]
  have keep_kk53 : SvKeepL B n0.mem n53.mem [(0x70, 0x4), (0x68, 0x4), (0x170, 0x41), (0x291, 0x3F), (0x130, 0x1), (0x131, 0x1F), (0x150, 0x20)] := keep_kk52.trans K53.toL
  clear keep_kk52
  have w53_30 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 := (K53.w32 (by decide) (by decide)).trans w52_30
  have w53_34 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 := (K53.w32 (by decide) (by decide)).trans w52_34
  have w53_38 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 := (K53.w32 (by decide) (by decide)).trans w52_38
  have w53_3c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c := (K53.w32 (by decide) (by decide)).trans w52_3c
  have w53_40 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 := (K53.w32 (by decide) (by decide)).trans w52_40
  have w53_44 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 := (K53.w32 (by decide) (by decide)).trans w52_44
  have w53_48 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := (K53.w32 (by decide) (by decide)).trans w52_48
  have w53_4c : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := (K53.w32 (by decide) (by decide)).trans w52_4c
  have w53_50 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 := (K53.w32 (by decide) (by decide)).trans w52_50
  have w53_68 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = sgl := (K53.w32 (by decide) (by decide)).trans w52_68
  have w53_70 : memLoad32 n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = sgp := (K53.w32 (by decide) (by decide)).trans w52_70
  have b53_130 : n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = BitVec.ofNat 8 ((sr43).getD 0 0) := (K53.b8 (by decide) (by decide)).trans b52_130
  have b53_170 : n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = (0 : BitVec 8) := (K53.b8 (by decide) (by decide)).trans b52_170
  have b53_171 : n53.mem (B + 0x21A0 + BitVec.ofNat 32 0x171) = BitVec.ofNat 8 ((sr43).getD 0 0) := (K53.b8 (by decide) (by decide)).trans b52_171
  have q53_131 : ∀ j, j < 31 → n53.mem (B + 0x21A0 + BitVec.ofNat 32 (0x131 + j)) = BitVec.ofNat 8 ((sr43).getD (1 + j) 0) := fun j hj => (K53.range (by decide) (by decide) j hj).trans (q52_131 j hj)
  have q53_171 : ∀ j, j < 32 → n53.mem (B + 0x21A0 + BitVec.ofNat 32 (0x171 + j)) = BitVec.ofNat 8 ((sr43).getD j 0) := fun j hj => (K53.range (by decide) (by decide) j hj).trans (q52_171 j hj)
  have q53_191 : ∀ j, j < 32 → n53.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => (K53.range (by decide) (by decide) j hj).trans (q52_191 j hj)
  have q53_291 : ∀ j, j < 31 → n53.mem (B + 0x21A0 + BitVec.ofNat 32 (0x291 + j)) = BitVec.ofNat 8 ((sr43).getD (1 + j) 0) := fun j hj => (K53.range (by decide) (by decide) j hj).trans (q52_291 j hj)
  have q53_2b0 : ∀ j, j < 32 → n53.mem (B + 0x21A0 + BitVec.ofNat 32 (0x2B0 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => (K53.range (by decide) (by decide) j hj).trans (q52_2b0 j hj)
  have q53_150 : ∀ j, j < 32 → n53.mem (B + 0x21A0 + BitVec.ofNat 32 (0x150 + j)) = BitVec.ofNat 8 ((ss43).getD j 0) := fun j hj => by
    rw [show 0x150 + j = 0x150 + (0x0 + j) by omega, X53 (0x0 + j) (by omega),
      show 0x2B0 + (0x0 + j) = 0x2B0 + j by omega]; exact q52_2b0 j (by omega)
  clear q52_2b0 q52_291 q52_191 q52_171 q52_131 b52_171 b52_170 b52_130 w52_70 w52_68 w52_50 w52_4c w52_48 w52_44 w52_40 w52_3c w52_38 w52_34 w52_30 g52_12 g52_11 g52_10 g52_26 g52_24 g52_23 g52_22 g52_21 g52_20 g52_19 g52_18 g52_8 g52_4 g52_3 g52_2 V52 E52 fR52 t52 fr52 rb52 s52 m52 u52 c52
  exact .inr ⟨hpv, hq0, hq1, hq2, hq3, hq4, sr43, ss43, hr43, n53, t53, s53, E53, V53, fR53, g53_2, g53_3, g53_4, g53_18, g53_19, g53_20, g53_21, g53_22, g53_23, g53_24, g53_26, w53_30, w53_34, w53_38, w53_3c, w53_40, w53_44, w53_48, w53_4c, w53_50, w53_68, w53_70, b53_130, q53_131, q53_150, q53_171, q53_191, q53_291, q53_2b0, keep_kk53.mono (by decide)⟩

end C3.RV32.Sv
