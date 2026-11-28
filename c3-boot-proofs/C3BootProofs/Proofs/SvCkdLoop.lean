import C3BootProofs.Proofs.SvSeg
import C3BootProofs.Proofs.SvCkd
import C3BootProofs.Proofs.SvCke

/-!
# `sigstore::verify`: The checkpoint's size, over `k` digits

Written by `scripts/gen-sv-loop.py` from `sv_ckd`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- The checkpoint's size, over `k` digits. -/
theorem sv_ckdloop {B out bp x20 x21 x22 x23 x26 rl rp : Word} {v : Nat → Word}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8) :
    ∀ (k : Nat) {c p w64 w74 : Word} {n0 : Machine},
    (E0 : SvCode n0.mem) →
    (V0 : SvSaves B n0.mem v) →
    (s0 : St n0.mem SV n0 0x14FE (reg n0)) →
    (fM : ∀ x, SvR B x → n0.mem x = M0 x) →
    (g0_2 : reg n0 sp = B + 0x21A0) →
    (g0_8 : reg n0 (8 : Fin 32) = c) →
    (g0_10 : reg n0 a0 = BitVec.ofNat 32 0xA) →
    (g0_18 : reg n0 (18 : Fin 32) = out) →
    (g0_19 : reg n0 (19 : Fin 32) = bp) →
    (g0_20 : reg n0 (20 : Fin 32) = x20) →
    (g0_21 : reg n0 (21 : Fin 32) = x21) →
    (g0_22 : reg n0 (22 : Fin 32) = x22) →
    (g0_23 : reg n0 (23 : Fin 32) = x23) →
    (g0_24 : reg n0 (24 : Fin 32) = p) →
    (g0_25 : reg n0 (25 : Fin 32) = rp) →
    (g0_26 : reg n0 (26 : Fin 32) = x26) →
    (g0_27 : reg n0 (27 : Fin 32) = rl) →
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64) →
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74) →
    (∀ i, i < k → ∀ c' p' w64' w74', (c', p', w64', w74') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, ((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))))) i (c, p, w64, w74) → (c' ≠ 0) ∧ (SvIn B p' c'.toNat)) →
    SvErrRet B out v n0 ∨ ∃ n' c' p' w64' w74', Steps n0 n' ∧ (c', p', w64', w74') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, ((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))))) k (c, p, w64, w74) ∧ (∀ i, i < k → ∀ c' p' w64' w74', (c', p', w64', w74') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, ((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))))) i (c, p, w64, w74) → ((((((M0 (p')).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF).toNat < (BitVec.ofNat 32 0xA).toNat)) ∧ (((aluEval .sltu ((aluEval .mul (w74') (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64') (BitVec.ofNat 32 0xA))) (aluEval .mulhu (w64') (BitVec.ofNat 32 0xA))) ||| (aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74') (BitVec.ofNat 32 0xA))) = 0)) ∧ (((aluEval .sltu (((((M0 (p')).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64') (BitVec.ofNat 32 0xA))) (aluEval .mul (w64') (BitVec.ofNat 32 0xA))) &&& (aluEval .sltu (((aluEval .mul (w74') (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64') (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p')).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64') (BitVec.ofNat 32 0xA))) (aluEval .mul (w64') (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74') (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64') (BitVec.ofNat 32 0xA)))) = 0))) ∧
      reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
      SvKeepL B n0.mem n'.mem [(0x64, 0x4), (0x74, 0x4)] ∧
      SvCode n'.mem ∧
      SvSaves B n'.mem v ∧
      St n'.mem SV n' 0x14FE (reg n') ∧
      (∀ x, SvR B x → n'.mem x = M0 x) ∧
      reg n' sp = B + 0x21A0 ∧
      reg n' (8 : Fin 32) = c' ∧
      reg n' a0 = BitVec.ofNat 32 0xA ∧
      reg n' (18 : Fin 32) = out ∧
      reg n' (19 : Fin 32) = bp ∧
      reg n' (20 : Fin 32) = x20 ∧
      reg n' (21 : Fin 32) = x21 ∧
      reg n' (22 : Fin 32) = x22 ∧
      reg n' (23 : Fin 32) = x23 ∧
      reg n' (24 : Fin 32) = p' ∧
      reg n' (25 : Fin 32) = rp ∧
      reg n' (26 : Fin 32) = x26 ∧
      reg n' (27 : Fin 32) = rl ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64' ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74' := by
  intro k
  induction k with
  | zero =>
    intro c p w64 w74 n0 E0 V0 s0 fM g0_2 g0_8 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_64 w0_74 _
    exact .inr ⟨n0, c, p, w64, w74, .refl _, (svIter_zero _ (c, p, w64, w74)).symm, fun i hi => absurd hi (Nat.not_lt_zero i), rfl, rfl, SvKeepL.refl.mono (by decide), E0, V0, s0, fM, g0_2, g0_8, g0_10, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, w0_64, w0_74⟩
  | succ k ih =>
    intro c p w64 w74 n0 E0 V0 s0 fM g0_2 g0_8 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_64 w0_74 H
    obtain ⟨hc, pin⟩ := H 0 (Nat.succ_pos k) c p w64 w74 (svIter_zero _ (c, p, w64, w74)).symm
    rcases sv_ckd (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x26 := x26) (c := c) (p := p) (rl := rl) (rp := rp) (w64 := w64) (w74 := w74) (v := v) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 rfl g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_64 w0_74 hc pin with ⟨-, e⟩ | ⟨x1_0, x1_1, x1_2, n1, c1, s1, E1, V1, fR1, r1_2, r1_3, r1_4, r1_8, r1_9, r1_a0, r1_18, r1_19, r1_20, r1_21, r1_22, r1_23, r1_24, r1_25, r1_26, r1_27, w1_64, w1_74, K1_L⟩
    · exact .inl e
    rcases ih E1 V1 s1 fR1 r1_2 r1_8 r1_a0 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 r1_24 r1_25 r1_26 r1_27 w1_64 w1_74 (fun i hi c' p' w64' w74' e0 => H (i + 1) (Nat.succ_lt_succ hi) c' p' w64' w74' (e0.trans (svIter_succ _ i (c, p, w64, w74)).symm)) with e | ⟨n', c', p', w64', w74', cs, e0, hsc, h3, h4, hk, rest⟩
    · exact .inl (SvErrRet.pre c1 r1_3 r1_4 (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
    · refine .inr ⟨n', c', p', w64', w74', c1.trans cs, (e0.trans (svIter_succ _ k (c, p, w64, w74)).symm), fun i hi c' p' w64' w74' e1 => ?_, h3.trans r1_3, h4.trans r1_4, (K1_L.trans hk).mono (by decide), rest⟩
      cases i with
      | zero => cases e1.trans (svIter_zero _ (c, p, w64, w74)); exact ⟨x1_0, x1_1, x1_2⟩
      | succ i => exact hsc i (by omega) c' p' w64' w74' (e1.trans (svIter_succ _ i (c, p, w64, w74)))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `N` iterations of `sv_ckdloop`, then `sv_cke`, as a stage. -/
theorem sv_ckdloop_st {B out bp x20 x21 x22 x23 x26 rl rp : Word} {v : Nat → Word} {N : Nat} {c p w64 w74 : Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8)
    (hz : ∀ c' p' w64' w74', (c', p', w64', w74') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, ((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))))) N (c, p, w64, w74) → c' = 0)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (s0 : St n0.mem SV n0 0x14FE (reg n0))
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = c)
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
    (H : ∀ i, i < N → ∀ c' p' w64' w74', (c', p', w64', w74') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, ((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))))) i (c, p, w64, w74) → (c' ≠ 0) ∧ (SvIn B p' c'.toNat))
    (CK0 : SvCkCode M0)
    (rt_in : SvIn B rp rl.toNat)
    :
    SvErrRet B out v n0 ∨
    (∃ c' p' w64' w74', (c', p', w64', w74') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, ((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))))) N (c, p, w64, w74) ∧ (∀ i, i < N → ∀ c' p' w64' w74', (c', p', w64', w74') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, ((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))))) i (c, p, w64, w74) → ((((((M0 (p')).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF).toNat < (BitVec.ofNat 32 0xA).toNat)) ∧ (((aluEval .sltu ((aluEval .mul (w74') (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64') (BitVec.ofNat 32 0xA))) (aluEval .mulhu (w64') (BitVec.ofNat 32 0xA))) ||| (aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74') (BitVec.ofNat 32 0xA))) = 0)) ∧ (((aluEval .sltu (((((M0 (p')).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64') (BitVec.ofNat 32 0xA))) (aluEval .mul (w64') (BitVec.ofNat 32 0xA))) &&& (aluEval .sltu (((aluEval .mul (w74') (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64') (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p')).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64') (BitVec.ofNat 32 0xA))) (aluEval .mul (w64') (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74') (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64') (BitVec.ofNat 32 0xA)))) = 0))) ∧
      (w74'.toNat < 2 ^ 31) ∧ ∃ bs7, base64Decode (memBytes M0 (rp) ((rl).toNat)) = some bs7 ∧ (bs7.length = 32) ∧
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
        reg n' (24 : Fin 32) = p' ∧
        reg n' (25 : Fin 32) = rp ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = rl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (bs7.getD 0 0)).zeroExtend 32 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (x21) + BitVec.ofNat 32 0x108 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = BitVec.ofNat 8 (bs7.getD 0 0) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (bs7.getD (1 + j) 0)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (bs7.getD j 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x64, 0x4), (0x74, 0x4), (0x420, 0x60), (0x400, 0x8), (0x20, 0x4), (0x3E0, 0x1F), (0x4C, 0x4)]) := by
  rcases sv_ckdloop (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x26 := x26) (rl := rl) (rp := rp) (v := v) FW hret hO M0 N E0 V0 s0 fM g0_2 g0_8 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_64 w0_74 H with e | ⟨n1, c', p', w64', w74', cs, e0, hsc, hr3, hr4, hkl, E0', V0', s0', fM', g0_2', g0_8', g0_10', g0_18', g0_19', g0_20', g0_21', g0_22', g0_23', g0_24', g0_25', g0_26', g0_27', w0_64', w0_74'⟩
  · exact .inl e
  rcases sv_cke (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x26 := x26) (c := c') (p := p') (rl := rl) (rp := rp) (w64 := w64') (w74 := w74') (v := v) FW E0' V0' hret hO s0' M0 fM' g0_2' g0_8' rfl g0_10' g0_18' g0_19' g0_20' g0_21' g0_22' g0_23' g0_24' g0_25' g0_26' g0_27' w0_64' w0_74' (hz c' p' w64' w74' e0) CK0 rt_in with ⟨-, e⟩ | ⟨h0, bs7, h1, h2, n2, c2, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r8, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w20, f_w4c, f_w64, f_w74, f_w404, f_b400, f_b420, f_q3e0, f_q420, f_KL⟩
  · exact .inl (SvErrRet.pre cs hr3 hr4 (fun x hx => (fM' x hx).trans (fM x hx).symm) e)
  exact .inr ⟨c', p', w64', w74', e0, hsc, h0, bs7, h1, h2, n2, cs.trans c2, f_ST, f_E, f_V, f_FR, f_r2, f_r3.trans hr3, f_r4.trans hr4, f_r8, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w20, f_w4c, f_w64, f_w74, f_w404, f_b400, f_b420, f_q3e0, f_q420, (hkl.trans f_KL).mono (by decide)⟩

set_option maxHeartbeats 16000000 in
/-- `sv_ckdloop_st` over every byte of the slice: `c` reaches 0 after `c.toNat` iterations. -/
theorem sv_ckdloop_run {B out bp x20 x21 x22 x23 x26 rl rp : Word} {v : Nat → Word} {c p w64 w74 : Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (s0 : St n0.mem SV n0 0x14FE (reg n0))
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = c)
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
    (pin : SvIn B p c.toNat)
    (rt_in : SvIn B rp rl.toNat)
    (CK0 : SvCkCode M0)
    :
    SvErrRet B out v n0 ∨
    (∃ c' p' w64' w74', (c', p', w64', w74') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, ((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))))) c.toNat (c, p, w64, w74) ∧ (∀ i, i < c.toNat → ∀ c' p' w64' w74', (c', p', w64', w74') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, ((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))))) i (c, p, w64, w74) → ((((((M0 (p')).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF).toNat < (BitVec.ofNat 32 0xA).toNat)) ∧ (((aluEval .sltu ((aluEval .mul (w74') (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64') (BitVec.ofNat 32 0xA))) (aluEval .mulhu (w64') (BitVec.ofNat 32 0xA))) ||| (aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74') (BitVec.ofNat 32 0xA))) = 0)) ∧ (((aluEval .sltu (((((M0 (p')).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64') (BitVec.ofNat 32 0xA))) (aluEval .mul (w64') (BitVec.ofNat 32 0xA))) &&& (aluEval .sltu (((aluEval .mul (w74') (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64') (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p')).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64') (BitVec.ofNat 32 0xA))) (aluEval .mul (w64') (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74') (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64') (BitVec.ofNat 32 0xA)))) = 0))) ∧
      (w74'.toNat < 2 ^ 31) ∧ ∃ bs7, base64Decode (memBytes M0 (rp) ((rl).toNat)) = some bs7 ∧ (bs7.length = 32) ∧
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
        reg n' (24 : Fin 32) = p' ∧
        reg n' (25 : Fin 32) = rp ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = rl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (bs7.getD 0 0)).zeroExtend 32 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (x21) + BitVec.ofNat 32 0x108 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x404) = BitVec.ofNat 32 bs7.length ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x400) = (0 : BitVec 8) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = BitVec.ofNat 8 (bs7.getD 0 0) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (bs7.getD (1 + j) 0)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 (bs7.getD j 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x64, 0x4), (0x74, 0x4), (0x420, 0x60), (0x400, 0x8), (0x20, 0x4), (0x3E0, 0x1F), (0x4C, 0x4)]) := by
  refine sv_ckdloop_st (N := c.toNat) FW hret hO M0 ?_ E0 V0 s0 fM g0_2 g0_8 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_64 w0_74 ?_ CK0 rt_in
  · intro c' p' w64' w74' e
    have h1 := congrArg (fun s => s.1) e
    simp only at h1
    rw [svIter_dec1 (F := (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, ((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)))))) (fun s : Word × Word × Word × Word => s.1) (fun s => rfl)] at h1
    simp only at h1
    rw [h1]; exact svSub_self_toNat c
  · intro i hi c' p' w64' w74' e
    have h1 := congrArg (fun s => s.1) e
    have h2 := congrArg (fun s => s.2.1) e
    simp only at h1 h2
    rw [svIter_dec1 (F := (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, ((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)))))) (fun s : Word × Word × Word × Word => s.1) (fun s => rfl)] at h1
    rw [svIter_add (F := (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, ((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)))))) (fun s : Word × Word × Word × Word => s.2.1) (d := 1) (fun s => rfl)] at h2
    simp only at h1 h2
    refine ⟨?_, ?_⟩
    · rw [h1]; bv_omega
    · rw [h1, h2, Nat.mul_one, svSub_toNat (by omega)]; exact pin.drop (by omega)

end C3.RV32.Sv
