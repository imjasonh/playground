import C3BootProofs.Proofs.SvSeg
import C3BootProofs.Proofs.SvClmiss
import C3BootProofs.Proofs.SvClhit
import C3BootProofs.Proofs.SvClend

/-!
# `sigstore::verify`: The search of the root's logs for the checkpoint's origin

Written by `scripts/gen-sv-search.py` from `sv_clmiss`, `sv_clhit`, and `sv_clend`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

/-- How `sv_clhit` ends from the entry that matches: its success condition, then the state at its end. -/
def sv_csearchOk (B out bp x20 x21 x22 x23 x24 x26 x27 w48 w44 : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (c' q' : Word) (nk : Machine) : Prop :=
  (((memLoad32 M0 (q' + 0x20)) ≠ 0) ∧
    ∃ n', Steps nk n' ∧
        St n'.mem SV n' 0x15F0 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg nk (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg nk (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = (c') + BitVec.ofNat 32 0xFFFFFFE0 ∧
        reg n' (9 : Fin 32) = (q') + BitVec.ofNat 32 0x20 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = x24 ∧
        reg n' (25 : Fin 32) = (memLoad32 M0 (q' + 0x24)) ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = x27 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = (memLoad32 M0 (q' + 0x20)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (q') + BitVec.ofNat 32 0x20 ∧
        SvKeepL B nk.mem n'.mem [(0x40, 0x4), (0x4C, 0x4)])

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- The search of the root's logs for the checkpoint's origin. -/
theorem sv_csearch {B out bp x20 x21 x22 x23 x24 x26 x27 w48 w44 : Word} {v : Nat → Word}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8) :
    ∀ (N : Nat) {c q : Word} {n0 : Machine},
    (hz : ∀ c' q', (c', q') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) N (c, q) → c' = 0) →
    (E0 : SvCode n0.mem) →
    (V0 : SvSaves B n0.mem v) →
    (s0 : St n0.mem SV n0 0x15C0 (reg n0)) →
    (fM : ∀ x, SvR B x → n0.mem x = M0 x) →
    (g0_2 : reg n0 sp = B + 0x21A0) →
    (g0_8 : reg n0 (8 : Fin 32) = c) →
    (g0_18 : reg n0 (18 : Fin 32) = out) →
    (g0_19 : reg n0 (19 : Fin 32) = bp) →
    (g0_20 : reg n0 (20 : Fin 32) = x20) →
    (g0_21 : reg n0 (21 : Fin 32) = x21) →
    (g0_22 : reg n0 (22 : Fin 32) = x22) →
    (g0_23 : reg n0 (23 : Fin 32) = x23) →
    (g0_24 : reg n0 (24 : Fin 32) = x24) →
    (g0_26 : reg n0 (26 : Fin 32) = x26) →
    (g0_27 : reg n0 (27 : Fin 32) = x27) →
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44) →
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48) →
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q) →
    (∀ i, i < N → ∀ c' q', (c', q') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i (c, q) → (c' ≠ 0) ∧ (SvIn B (q' + 0x20) 4) ∧ (SvIn B (q' + 0x24) 4) ∧ ((q' + 0x20).toNat % 4 = 0) ∧ ((q' + 0x24).toNat % 4 = 0) ∧ ((memLoad32 M0 (q' + 0x20)) ≠ 0 → SvIn B (memLoad32 M0 (q' + 0x20)) (memLoad32 M0 (q' + 0x24)).toNat) ∧ (SvIn B w48 w44.toNat)) →
    SvErrRet B out v n0 ∨ ∃ k, k < N ∧
      (∀ i, i < k → ∀ c' q', (c', q') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i (c, q) → ¬ (memBytes M0 (memLoad32 M0 (q' + 0x20)) (memLoad32 M0 (q' + 0x24)).toNat = memBytes M0 w48 w44.toNat)) ∧
      ∃ c' q', (c', q') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) k (c, q) ∧ (memBytes M0 (memLoad32 M0 (q' + 0x20)) (memLoad32 M0 (q' + 0x24)).toNat = memBytes M0 w48 w44.toNat) ∧
      ∃ nk, Steps n0 nk ∧ reg nk (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg nk (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
      SvKeepL B n0.mem nk.mem [(0x40, 0x4), (0x4C, 0x4)] ∧
      sv_csearchOk B out bp x20 x21 x22 x23 x24 x26 x27 w48 w44 v M0 c' q' nk := by
  intro N
  induction N with
  | zero =>
    intro c q n0 hz E0 V0 s0 fM g0_2 g0_8 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_26 g0_27 w0_44 w0_48 w0_4c _
    rcases sv_clend (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x26 := x26) (x27 := x27) (c := c) (q := q) (w48 := w48) (w44 := w44) (v := v) (op := 0) (ol := 0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 rfl g0_26 g0_27 w0_44 w0_48 w0_4c (hz c q (svIter_zero _ (c, q)).symm) with ⟨-, e⟩ | ⟨x1_0, -⟩
    · exact .inl e
    · exact x1_0.elim
  | succ N ih =>
    intro c q n0 hz E0 V0 s0 fM g0_2 g0_8 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_26 g0_27 w0_44 w0_48 w0_4c H
    obtain ⟨hc, eo_in, el_in, a_op, a_ol, o_in, l_in⟩ := H 0 (Nat.succ_pos N) c q (svIter_zero _ (c, q)).symm
    by_cases hm : memBytes M0 (memLoad32 M0 (q + 0x20)) (memLoad32 M0 (q + 0x24)).toNat = memBytes M0 w48 w44.toNat
    · rcases sv_clhit (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x26 := x26) (x27 := x27) (c := c) (q := q) (w48 := w48) (w44 := w44) (v := v) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 rfl g0_26 g0_27 w0_44 w0_48 w0_4c hc rfl rfl eo_in el_in a_op a_ol o_in l_in hm with ⟨-, e⟩ | okh
      · exact .inl e
      · exact .inr ⟨0, Nat.succ_pos _, fun i hi => absurd hi (Nat.not_lt_zero i), c, q, (svIter_zero _ (c, q)).symm, hm, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), okh⟩
    rcases sv_clmiss (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x26 := x26) (x27 := x27) (c := c) (q := q) (w48 := w48) (w44 := w44) (v := v) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 rfl g0_26 g0_27 w0_44 w0_48 w0_4c hc rfl rfl eo_in el_in a_op a_ol o_in l_in hm with ⟨-, e⟩ | ⟨x1_0, n1, c1, s1, E1, V1, fR1, r1_2, r1_3, r1_4, r1_8, r1_9, r1_18, r1_19, r1_20, r1_21, r1_22, r1_23, r1_24, r1_25, r1_26, r1_27, w1_40, w1_44, w1_48, w1_4c, K1_L⟩
    · exact .inl e
    rcases ih (fun c' q' e0 => hz c' q' (e0.trans (svIter_succ _ N (c, q)).symm)) E1 V1 s1 fR1 r1_2 r1_8 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 r1_24 r1_26 r1_27 w1_44 w1_48 w1_4c (fun i hi c' q' e0 => H (i + 1) (Nat.succ_lt_succ hi) c' q' (e0.trans (svIter_succ _ i (c, q)).symm)) with e | ⟨k, hk, hn, c', q', e0, hmk, nk, cs, h3, h4, hkl, okh⟩
    · exact .inl (SvErrRet.pre c1 r1_3 r1_4 (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
    · refine .inr ⟨k + 1, by omega, fun i hi c' q' e1 => ?_, c', q', (e0.trans (svIter_succ _ k (c, q)).symm), hmk, nk, c1.trans cs, h3.trans r1_3, h4.trans r1_4, (K1_L.trans hkl).mono (by decide), okh⟩
      cases i with
      | zero => cases e1.trans (svIter_zero _ (c, q)); exact hm
      | succ i => exact hn i (by omega) c' q' (e1.trans (svIter_succ _ i (c, q)))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `sv_csearch` as a stage. -/
theorem sv_csearch_st {B out bp x20 x21 x22 x23 x24 x26 x27 w48 w44 : Word} {v : Nat → Word} {N : Nat} {c q : Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8)
    (hz : ∀ c' q', (c', q') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) N (c, q) → c' = 0)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (s0 : St n0.mem SV n0 0x15C0 (reg n0))
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = c)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = x24)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = x27)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q)
    (H : ∀ i, i < N → ∀ c' q', (c', q') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i (c, q) → (c' ≠ 0) ∧ (SvIn B (q' + 0x20) 4) ∧ (SvIn B (q' + 0x24) 4) ∧ ((q' + 0x20).toNat % 4 = 0) ∧ ((q' + 0x24).toNat % 4 = 0) ∧ ((memLoad32 M0 (q' + 0x20)) ≠ 0 → SvIn B (memLoad32 M0 (q' + 0x20)) (memLoad32 M0 (q' + 0x24)).toNat) ∧ (SvIn B w48 w44.toNat)) :
    SvErrRet B out v n0 ∨
    (∃ k, k < N ∧
      (∀ i, i < k → ∀ c' q', (c', q') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i (c, q) → ¬ (memBytes M0 (memLoad32 M0 (q' + 0x20)) (memLoad32 M0 (q' + 0x24)).toNat = memBytes M0 w48 w44.toNat)) ∧
      ∃ c' q', (c', q') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) k (c, q) ∧ (memBytes M0 (memLoad32 M0 (q' + 0x20)) (memLoad32 M0 (q' + 0x24)).toNat = memBytes M0 w48 w44.toNat) ∧
      ((memLoad32 M0 (q' + 0x20)) ≠ 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x15F0 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = (c') + BitVec.ofNat 32 0xFFFFFFE0 ∧
        reg n' (9 : Fin 32) = (q') + BitVec.ofNat 32 0x20 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = x24 ∧
        reg n' (25 : Fin 32) = (memLoad32 M0 (q' + 0x24)) ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = x27 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = (memLoad32 M0 (q' + 0x20)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (q') + BitVec.ofNat 32 0x20 ∧
        SvKeepL B n0.mem n'.mem [(0x40, 0x4), (0x4C, 0x4)]) := by
  rcases sv_csearch (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x26 := x26) (x27 := x27) (w48 := w48) (w44 := w44) (v := v) FW hret hO M0 N hz E0 V0 s0 fM g0_2 g0_8 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_26 g0_27 w0_44 w0_48 w0_4c H with e | ⟨k, hk, hn, c', q', e0, hmk, nk, cs, hr3, hr4, hkl, okh⟩
  · exact .inl e
  unfold sv_csearchOk at okh
  obtain ⟨h0, n1, cn, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w40, f_w44, f_w48, f_w4c, f_KL⟩ := okh
  exact .inr ⟨k, hk, hn, c', q', e0, hmk, h0, n1, cs.trans cn, f_ST, f_E, f_V, f_FR, f_r2, f_r3.trans hr3, f_r4.trans hr4, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w40, f_w44, f_w48, f_w4c, (hkl.trans f_KL).mono (by decide)⟩

end C3.RV32.Sv
