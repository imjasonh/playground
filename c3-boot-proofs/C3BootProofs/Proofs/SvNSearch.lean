import C3BootProofs.Proofs.SvSeg
import C3BootProofs.Proofs.SvCnm
import C3BootProofs.Proofs.SvCns
import C3BootProofs.Proofs.SvCne

/-!
# `sigstore::verify`: The search of a signature line for the space after the signer's name

Written by `scripts/gen-sv-search.py` from `sv_cnm`, `sv_cns`, and `sv_cne`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

/-- How `sv_cns` ends from the entry that matches: its success condition, then the state at its end. -/
def sv_nsearchOk (B out bp x20 x21 x22 x23 x24 x25 x26 x27 f w38 w50 kh w48 w44 kp ckp bl np nl : Word) (sg : Bytes) (v : Nat → Word) (M0 : Word → BitVec 8) (ni' : Word) (nk : Machine) : Prop :=
  ((ni' ≠ 0) ∧
    (((nl) - ((ni') + BitVec.ofNat 32 0x1)) &&& BitVec.ofNat 32 0x3 = 0) ∧
    ∃ n', Steps nk n' ∧
        St n'.mem SV n' 0x16D4 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg nk (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg nk (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = nl ∧
        reg n' (9 : Fin 32) = (ni') + BitVec.ofNat 32 0x1 ∧
        reg n' a0 = (np) + ((ni') + BitVec.ofNat 32 0x1) ∧
        reg n' a1 = (np) + ((ni') + BitVec.ofNat 32 0x1) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = BitVec.ofNat 32 0x0 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = ni' ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = (nl) - ((ni') + BitVec.ofNat 32 0x1) ∧
        reg n' (27 : Fin 32) = np ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = (aluEval .sll (((nl) - ((ni') + BitVec.ofNat 32 0x1)) >>> 2) (BitVec.ofNat 32 0x2)) + ((np) + ((ni') + BitVec.ofNat 32 0x1)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = ((nl) - ((ni') + BitVec.ofNat 32 0x1)) >>> 2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = (np) + ((ni') + BitVec.ofNat 32 0x1) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0)) ∧
        SvKeepL B nk.mem n'.mem [(0xC, 0x4), (0x8, 0x4), (0x10, 0x4)])

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- The search of a signature line for the space after the signer's name. -/
theorem sv_nsearch {B out bp x20 x21 x22 x23 x24 x25 x26 x27 f w38 w50 kh w48 w44 kp ckp bl np nl : Word} {sg : Bytes} {v : Nat → Word}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8) :
    ∀ (N : Nat) {ni : Word} {n0 : Machine},
    (hz : ∀ ni', ni' = svIter (fun s => (s) + BitVec.ofNat 32 0x1) N ni → nl = ni' + BitVec.ofNat 32 0x1) →
    (E0 : SvCode n0.mem) →
    (V0 : SvSaves B n0.mem v) →
    (s0 : St n0.mem SV n0 0x1694 (reg n0)) →
    (fM : ∀ x, SvR B x → n0.mem x = M0 x) →
    (g0_2 : reg n0 sp = B + 0x21A0) →
    (g0_18 : reg n0 (18 : Fin 32) = out) →
    (g0_19 : reg n0 (19 : Fin 32) = bp) →
    (g0_20 : reg n0 (20 : Fin 32) = x20) →
    (g0_21 : reg n0 (21 : Fin 32) = x21) →
    (g0_22 : reg n0 (22 : Fin 32) = x22) →
    (g0_23 : reg n0 (23 : Fin 32) = x23) →
    (g0_25 : reg n0 (25 : Fin 32) = x25) →
    (g0_26 : reg n0 (26 : Fin 32) = x26) →
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh) →
    (w0_24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl) →
    (w0_28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp) →
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f) →
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp) →
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38) →
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44) →
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48) →
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50) →
    (b0_14 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0)) →
    (q0_1fc : ∀ j, j < 63 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0)) →
    (g0_8 : reg n0 (8 : Fin 32) = nl) →
    (g0_24 : reg n0 (24 : Fin 32) = ni) →
    (g0_27 : reg n0 (27 : Fin 32) = np) →
    (∀ i, i < N + 1 → ∀ ni', ni' = svIter (fun s => (s) + BitVec.ofNat 32 0x1) i ni → (SvIn B (np + ni') 1)) →
    (∀ i, i < N → ∀ ni', ni' = svIter (fun s => (s) + BitVec.ofNat 32 0x1) i ni → nl ≠ ni' + BitVec.ofNat 32 0x1) →
    SvErrRet B out v n0 ∨ ∃ k, k < N + 1 ∧
      (∀ i, i < k → ∀ ni', ni' = svIter (fun s => (s) + BitVec.ofNat 32 0x1) i ni → ¬ (M0 (np + ni') = 0x20)) ∧
      ∃ ni', ni' = svIter (fun s => (s) + BitVec.ofNat 32 0x1) k ni ∧ (M0 (np + ni') = 0x20) ∧
      ∃ nk, Steps n0 nk ∧ reg nk (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg nk (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
      SvKeepL B n0.mem nk.mem [] ∧
      sv_nsearchOk B out bp x20 x21 x22 x23 x24 x25 x26 x27 f w38 w50 kh w48 w44 kp ckp bl np nl sg v M0 ni' nk := by
  intro N
  induction N with
  | zero =>
    intro ni n0 hz E0 V0 s0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_25 g0_26 w0_18 w0_24 w0_28 w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc g0_8 g0_24 g0_27 H _
    have pa_in := H 0 (Nat.succ_pos 0) ni (svIter_zero _ ni).symm
    by_cases hm : M0 (np + ni) = 0x20
    · rcases sv_cns (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (np := np) (ni := ni) (nl := nl) (sg := sg) (v := v) FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_25 g0_26 w0_18 w0_24 w0_28 w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc g0_8 g0_24 g0_27 pa_in hm with ⟨-, e⟩ | okh
      · exact .inl e
      · exact .inr ⟨0, Nat.succ_pos 0, fun i hi => absurd hi (Nat.not_lt_zero i), ni, (svIter_zero _ ni).symm, hm, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), okh⟩
    rcases sv_cne (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (np := np) (ni := ni) (nl := nl) (sg := sg) (v := v)  FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_25 g0_26 w0_18 w0_24 w0_28 w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc g0_8 g0_24 g0_27 pa_in hm (hz ni (svIter_zero _ ni).symm) with ⟨-, e⟩ | ⟨x1_0, -⟩
    · exact .inl e
    · exact x1_0.elim
  | succ N ih =>
    intro ni n0 hz E0 V0 s0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_25 g0_26 w0_18 w0_24 w0_28 w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc g0_8 g0_24 g0_27 H Hc
    have pa_in := H 0 (Nat.succ_pos _) ni (svIter_zero _ ni).symm
    have hne := Hc 0 (Nat.succ_pos N) ni (svIter_zero _ ni).symm
    by_cases hm : M0 (np + ni) = 0x20
    · rcases sv_cns (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (np := np) (ni := ni) (nl := nl) (sg := sg) (v := v) FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_25 g0_26 w0_18 w0_24 w0_28 w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc g0_8 g0_24 g0_27 pa_in hm with ⟨-, e⟩ | okh
      · exact .inl e
      · exact .inr ⟨0, Nat.succ_pos _, fun i hi => absurd hi (Nat.not_lt_zero i), ni, (svIter_zero _ ni).symm, hm, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), okh⟩
    rcases sv_cnm (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (np := np) (ni := ni) (nl := nl) (sg := sg) (v := v) FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_25 g0_26 w0_18 w0_24 w0_28 w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc g0_8 g0_24 g0_27 pa_in hm hne with ⟨-, e⟩ | ⟨n1, c1, s1, E1, V1, fR1, r1_2, r1_3, r1_4, r1_8, r1_18, r1_19, r1_20, r1_21, r1_22, r1_23, r1_24, r1_25, r1_26, r1_27, w1_18, w1_24, w1_28, w1_30, w1_34, w1_38, w1_44, w1_48, w1_50, b1_14, q1_1fc, K1_L⟩
    · exact .inl e
    rcases ih (fun ni' e0 => hz ni' (e0.trans (svIter_succ _ N ni).symm)) E1 V1 s1 fR1 r1_2 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 r1_25 r1_26 w1_18 w1_24 w1_28 w1_30 w1_34 w1_38 w1_44 w1_48 w1_50 b1_14 q1_1fc r1_8 r1_24 r1_27 (fun i hi ni' e0 => H (i + 1) (Nat.succ_lt_succ hi) ni' (e0.trans (svIter_succ _ i ni).symm)) (fun i hi ni' e0 => Hc (i + 1) (Nat.succ_lt_succ hi) ni' (e0.trans (svIter_succ _ i ni).symm)) with e | ⟨k, hk, hn, ni', e0, hmk, nk, cs, h3, h4, hkl, okh⟩
    · exact .inl (SvErrRet.pre c1 r1_3 r1_4 (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
    · refine .inr ⟨k + 1, by omega, fun i hi ni' e1 => ?_, ni', (e0.trans (svIter_succ _ k ni).symm), hmk, nk, c1.trans cs, h3.trans r1_3, h4.trans r1_4, (K1_L.trans hkl).mono (by decide), okh⟩
      cases i with
      | zero => cases e1.trans (svIter_zero _ ni); exact hm
      | succ i => exact hn i (by omega) ni' (e1.trans (svIter_succ _ i ni))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `sv_nsearch` as a stage. -/
theorem sv_nsearch_st {B out bp x20 x21 x22 x23 x24 x25 x26 x27 f w38 w50 kh w48 w44 kp ckp bl np nl : Word} {sg : Bytes} {v : Nat → Word} {N : Nat} {ni : Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8)
    (hz : ∀ ni', ni' = svIter (fun s => (s) + BitVec.ofNat 32 0x1) N ni → nl = ni' + BitVec.ofNat 32 0x1)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (s0 : St n0.mem SV n0 0x1694 (reg n0))
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh)
    (w0_24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl)
    (w0_28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
    (b0_14 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0))
    (q0_1fc : ∀ j, j < 63 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0))
    (g0_8 : reg n0 (8 : Fin 32) = nl)
    (g0_24 : reg n0 (24 : Fin 32) = ni)
    (g0_27 : reg n0 (27 : Fin 32) = np)
    (H : ∀ i, i < N + 1 → ∀ ni', ni' = svIter (fun s => (s) + BitVec.ofNat 32 0x1) i ni → (SvIn B (np + ni') 1))
    (Hc : ∀ i, i < N → ∀ ni', ni' = svIter (fun s => (s) + BitVec.ofNat 32 0x1) i ni → nl ≠ ni' + BitVec.ofNat 32 0x1) :
    SvErrRet B out v n0 ∨
    (∃ k, k < N + 1 ∧
      (∀ i, i < k → ∀ ni', ni' = svIter (fun s => (s) + BitVec.ofNat 32 0x1) i ni → ¬ (M0 (np + ni') = 0x20)) ∧
      ∃ ni', ni' = svIter (fun s => (s) + BitVec.ofNat 32 0x1) k ni ∧ (M0 (np + ni') = 0x20) ∧
      (ni' ≠ 0) ∧ (((nl) - ((ni') + BitVec.ofNat 32 0x1)) &&& BitVec.ofNat 32 0x3 = 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x16D4 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = nl ∧
        reg n' (9 : Fin 32) = (ni') + BitVec.ofNat 32 0x1 ∧
        reg n' a0 = (np) + ((ni') + BitVec.ofNat 32 0x1) ∧
        reg n' a1 = (np) + ((ni') + BitVec.ofNat 32 0x1) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = BitVec.ofNat 32 0x0 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = ni' ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = (nl) - ((ni') + BitVec.ofNat 32 0x1) ∧
        reg n' (27 : Fin 32) = np ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = (aluEval .sll (((nl) - ((ni') + BitVec.ofNat 32 0x1)) >>> 2) (BitVec.ofNat 32 0x2)) + ((np) + ((ni') + BitVec.ofNat 32 0x1)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = ((nl) - ((ni') + BitVec.ofNat 32 0x1)) >>> 2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = (np) + ((ni') + BitVec.ofNat 32 0x1) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0)) ∧
        SvKeepL B n0.mem n'.mem [(0xC, 0x4), (0x8, 0x4), (0x10, 0x4)]) := by
  rcases sv_nsearch (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (np := np) (nl := nl) (sg := sg) (v := v) FW hret hO M0 N hz E0 V0 s0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_25 g0_26 w0_18 w0_24 w0_28 w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc g0_8 g0_24 g0_27 H Hc with e | ⟨k, hk, hn, ni', e0, hmk, nk, cs, hr3, hr4, hkl, okh⟩
  · exact .inl e
  unfold sv_nsearchOk at okh
  obtain ⟨h0, h1, n1, cn, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r8, f_r9, f_ra0, f_ra1, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w8, f_wc, f_w10, f_w18, f_w24, f_w28, f_w30, f_w34, f_w38, f_w44, f_w48, f_w50, f_b14, f_q1fc, f_KL⟩ := okh
  exact .inr ⟨k, hk, hn, ni', e0, hmk, h0, h1, n1, cs.trans cn, f_ST, f_E, f_V, f_FR, f_r2, f_r3.trans hr3, f_r4.trans hr4, f_r8, f_r9, f_ra0, f_ra1, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w8, f_wc, f_w10, f_w18, f_w24, f_w28, f_w30, f_w34, f_w38, f_w44, f_w48, f_w50, f_b14, f_q1fc, (hkl.trans f_KL).mono (by decide)⟩

set_option maxHeartbeats 16000000 in
/-- `sv_nsearch_st` over every byte of the slice but its last: `ni` counts up from 0. -/
theorem sv_nsearch_run {B out bp x20 x21 x22 x23 x24 x25 x26 x27 f w38 w50 kh w48 w44 kp ckp bl np nl : Word} {sg : Bytes} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (s0 : St n0.mem SV n0 0x1694 (reg n0))
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh)
    (w0_24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl)
    (w0_28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
    (b0_14 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0))
    (q0_1fc : ∀ j, j < 63 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0))
    (g0_8 : reg n0 (8 : Fin 32) = nl)
    (g0_24 : reg n0 (24 : Fin 32) = (BitVec.ofNat 32 0x0))
    (g0_27 : reg n0 (27 : Fin 32) = np)
    (slice : SvIn B np nl.toNat) (hlen : nl ≠ 0) :
    SvErrRet B out v n0 ∨
    (∃ k, k < (nl.toNat - 1) + 1 ∧
      (∀ i, i < k → ∀ ni', ni' = svIter (fun s => (s) + BitVec.ofNat 32 0x1) i (BitVec.ofNat 32 0x0) → ¬ (M0 (np + ni') = 0x20)) ∧
      ∃ ni', ni' = svIter (fun s => (s) + BitVec.ofNat 32 0x1) k (BitVec.ofNat 32 0x0) ∧ (M0 (np + ni') = 0x20) ∧
      ni' = (BitVec.ofNat 32 0x0) + BitVec.ofNat 32 (k * 1) ∧
      (ni' ≠ 0) ∧ (((nl) - ((ni') + BitVec.ofNat 32 0x1)) &&& BitVec.ofNat 32 0x3 = 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x16D4 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = nl ∧
        reg n' (9 : Fin 32) = (ni') + BitVec.ofNat 32 0x1 ∧
        reg n' a0 = (np) + ((ni') + BitVec.ofNat 32 0x1) ∧
        reg n' a1 = (np) + ((ni') + BitVec.ofNat 32 0x1) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = BitVec.ofNat 32 0x0 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = ni' ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = (nl) - ((ni') + BitVec.ofNat 32 0x1) ∧
        reg n' (27 : Fin 32) = np ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = (aluEval .sll (((nl) - ((ni') + BitVec.ofNat 32 0x1)) >>> 2) (BitVec.ofNat 32 0x2)) + ((np) + ((ni') + BitVec.ofNat 32 0x1)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = ((nl) - ((ni') + BitVec.ofNat 32 0x1)) >>> 2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = (np) + ((ni') + BitVec.ofNat 32 0x1) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0)) ∧
        SvKeepL B n0.mem n'.mem [(0xC, 0x4), (0x8, 0x4), (0x10, 0x4)]) := by
  have hb := slice.fit
  have hl : nl.toNat ≠ 0 := fun h => hlen (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  have HZ : ∀ ni', ni' = svIter (fun s => (s) + BitVec.ofNat 32 0x1) (nl.toNat - 1) (BitVec.ofNat 32 0x0) → nl = ni' + BitVec.ofNat 32 0x1 := by
    intro ni' e
    rw [e, svIter_add (F := (fun s => (s) + BitVec.ofNat 32 0x1)) (fun s : Word => s) (d := 1) (fun s => rfl)]
    bv_omega
  have HH : ∀ i, i < (nl.toNat - 1) + 1 → ∀ ni', ni' = svIter (fun s => (s) + BitVec.ofNat 32 0x1) i (BitVec.ofNat 32 0x0) → (SvIn B (np + ni') 1) := by
    intro i hi ni' e
    rw [e, svIter_add (F := (fun s => (s) + BitVec.ofNat 32 0x1)) (fun s : Word => s) (d := 1) (fun s => rfl), BitVec.zero_add, Nat.mul_one]
    exact (slice.drop (k := i) (by omega)).shrink (by omega)
  have HC : ∀ i, i < (nl.toNat - 1) → ∀ ni', ni' = svIter (fun s => (s) + BitVec.ofNat 32 0x1) i (BitVec.ofNat 32 0x0) → nl ≠ ni' + BitVec.ofNat 32 0x1 := by
    intro i hi ni' e
    rw [e, svIter_add (F := (fun s => (s) + BitVec.ofNat 32 0x1)) (fun s : Word => s) (d := 1) (fun s => rfl), BitVec.zero_add, Nat.mul_one]
    bv_omega
  rcases sv_nsearch_st (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (np := np) (nl := nl) (sg := sg) (v := v) (ni := BitVec.ofNat 32 0x0) (N := (nl.toNat - 1)) FW hret hO M0 HZ E0 V0 s0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_25 g0_26 w0_18 w0_24 w0_28 w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc g0_8 g0_24 g0_27 HH HC with e | ⟨k, hk, hn, ni', e0, hmk, rest⟩
  · exact .inl e
  have h1 : ni' = (BitVec.ofNat 32 0x0) + BitVec.ofNat 32 (k * 1) := by rw [e0, svIter_add (F := (fun s => (s) + BitVec.ofNat 32 0x1)) (fun s : Word => s) (d := 1) (fun s => rfl)]
  exact .inr ⟨k, hk, hn, ni', e0, hmk, h1, rest⟩

end C3.RV32.Sv
