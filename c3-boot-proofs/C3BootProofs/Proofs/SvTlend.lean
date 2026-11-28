import C3BootProofs.Proofs.SvSha2

/-!
# `sigstore::verify`: no TSA key left

The TSA loop at 0x1344 with no entries left: no listed TSA key has the timestamp's signer ID, and `sigstore::verify` fails.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


set_option maxHeartbeats 0 in
theorem sv_tlend {B out bp x20 x21 x22 x23 x24 x25 x26 x27 c q sid slen w4c w48 : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x1344 (reg n0))
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
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q)
    (hc : c = 0) :
    (¬ ((False) ∧ True) ∧ SvErrRet B out v n0) ∨
    ((False) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x1344 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        SvKeepL B n0.mem n'.mem []) := by
  have F := sv_frW FW
  have t0 : Steps n0 n0 := .refl n0
  have fR0 : ∀ x, SvR B x → n0.mem x = M0 x := fM
  have g0_3 : reg n0 (3 : Fin 32) = reg n0 (3 : Fin 32) := rfl
  have g0_4 : reg n0 (4 : Fin 32) = reg n0 (4 : Fin 32) := rfl
  by_cases hf : False
  rotate_left
  · -- 0x1344: branch, taken
    obtain ⟨n1, d1, u1⟩ := s0.taken E0.self 0x1388 sv_at_1344
      (by decide) (by rw [g0_8, s0.zero]; exact br_beq_t hc)
    have s1 : St n1.mem SV n1 0x1388 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
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
    have g1_18 : reg n1 (18 : Fin 32) = out := by rw [u1.regs, g0_18]
    have g1_19 : reg n1 (19 : Fin 32) = bp := by rw [u1.regs, g0_19]
    have g1_20 : reg n1 (20 : Fin 32) = x20 := by rw [u1.regs, g0_20]
    have g1_21 : reg n1 (21 : Fin 32) = x21 := by rw [u1.regs, g0_21]
    have g1_22 : reg n1 (22 : Fin 32) = x22 := by rw [u1.regs, g0_22]
    have g1_23 : reg n1 (23 : Fin 32) = x23 := by rw [u1.regs, g0_23]
    have g1_24 : reg n1 (24 : Fin 32) = x24 := by rw [u1.regs, g0_24]
    have g1_25 : reg n1 (25 : Fin 32) = x25 := by rw [u1.regs, g0_25]
    have g1_26 : reg n1 (26 : Fin 32) = x26 := by rw [u1.regs, g0_26]
    have g1_27 : reg n1 (27 : Fin 32) = x27 := by rw [u1.regs, g0_27]
    have keep_kk1 : SvKeepL B n0.mem n1.mem [] := by rw [m1]; exact (SvKeepL.refl : SvKeepL B n0.mem n0.mem [])
    have w1_48 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 := by rw [m1]; exact w0_48
    have w1_4c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c := by rw [m1]; exact w0_4c
    have w1_78 : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = q := by rw [m1]; exact w0_78
    exact .inl ⟨(fun ⟨h0', _⟩ => by exact hf h0'), sv_fail_1388 F E1 s1 t1 (fun x hx => (fR1 x hx).trans (fM x hx).symm) V1 hret g1_2 g1_18 hO g1_3 g1_4⟩
  exact hf.elim


end C3.RV32.Sv
