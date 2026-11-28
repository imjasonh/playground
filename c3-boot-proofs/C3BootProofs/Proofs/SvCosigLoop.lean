import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvSegCosig
import C3BootProofs.Proofs.SvCsx

/-!
# `sigstore::verify`: the checkpoint's signature loop

Written by `scripts/gen-sv-relloop.py` from `sv_seg_cosig` and `sv_csx`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option linter.unusedVariables false in
/-- One more signature line, from state `s` to `s'`: there are bytes left, and the next line is well formed. -/
def sv_cosigStep (B out bp x20 x22 x23 x25 kh w48 w44 kp ckp bl : Word) (v : Nat → Word) (M0 : Word → BitVec 8) : Word × Word × Word × Bytes → Word × Word × Word × Bytes → Prop :=
  fun s s' => s.2.2.1 ≠ 0 ∧ ∃ ix9_1, nlScan M0 ((s.2.1)) 0 (((s.2.2.1)).toNat) = some ix9_1 ∧ (4 ≤ ix9_1 ∧ memBytes M0 (s.2.1) 4 = memBytes M0 (BitVec.ofNat 32 (img% svDashAddress)) 4) ∧ (4 < ix9_1) ∧ ∃ k_2, k_2 < ((BitVec.ofNat 32 (ix9_1 - 4)).toNat - 1) + 1 ∧ (∀ i, i < k_2 → ∀ ni'_2, ni'_2 = svIter (fun s => (s) + BitVec.ofNat 32 0x1) i (BitVec.ofNat 32 0x0) → ¬ (M0 (((s.2.1) + BitVec.ofNat 32 4) + ni'_2) = 0x20)) ∧ ∃ ni'_2, ni'_2 = svIter (fun s => (s) + BitVec.ofNat 32 0x1) k_2 (BitVec.ofNat 32 0x0) ∧ (M0 (((s.2.1) + BitVec.ofNat 32 4) + ni'_2) = 0x20) ∧ ni'_2 = (BitVec.ofNat 32 0x0) + BitVec.ofNat 32 (k_2 * 1) ∧ (ni'_2 ≠ 0) ∧ ((((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)) &&& BitVec.ofNat 32 0x3 = 0) ∧ ∃ pg'_3 gi'_3, (pg'_3, gi'_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0x4, ((s.2)) + BitVec.ofNat 32 0x1)) (((((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)) >>> 2).toNat) (((((s.2.1) + BitVec.ofNat 32 4)) + ((ni'_2) + BitVec.ofNat 32 0x1)), (BitVec.ofNat 32 0x0)) ∧ (∀ i, i < (((((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)) >>> 2).toNat) → ∀ pg'_3 gi'_3, (pg'_3, gi'_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0x4, ((s.2)) + BitVec.ofNat 32 0x1)) i (((((s.2.1) + BitVec.ofNat 32 4)) + ((ni'_2) + BitVec.ofNat 32 0x1)), (BitVec.ofNat 32 0x0)) → ((((M0 (pg'_3) = 0x3D) ∧ ((gi'_3) + BitVec.ofNat 32 0x1 = ((((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)) >>> 2)) ∧ ∃ bq27, base64Decode (memBytes M0 pg'_3 4) = some bq27 ∧ (bq27.length ≤ 3)) ∨ ((¬ (M0 (pg'_3) = 0x3D)) ∧ (M0 ((pg'_3) + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi'_3) + BitVec.ofNat 32 0x1 = ((((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)) >>> 2)) ∧ ∃ bq33, base64Decode (memBytes M0 pg'_3 4) = some bq33 ∧ (bq33.length ≤ 3)) ∨ ((¬ (M0 (pg'_3) = 0x3D)) ∧ (¬ (M0 ((pg'_3) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (M0 (((pg'_3) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi'_3) + BitVec.ofNat 32 0x1 = ((((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)) >>> 2)) ∧ ∃ bq39, base64Decode (memBytes M0 pg'_3 4) = some bq39 ∧ (bq39.length ≤ 3)) ∨ ((¬ (M0 (pg'_3) = 0x3D)) ∧ (¬ (M0 ((pg'_3) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 (((pg'_3) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (M0 ((((pg'_3) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi'_3) + BitVec.ofNat 32 0x1 = ((((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)) >>> 2)) ∧ ∃ bq45, base64Decode (memBytes M0 pg'_3 4) = some bq45 ∧ (bq45.length ≤ 3)) ∨ ((¬ (M0 (pg'_3) = 0x3D)) ∧ (¬ (M0 ((pg'_3) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 (((pg'_3) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 ((((pg'_3) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ ∃ bq44, base64Decode (memBytes M0 pg'_3 4) = some bq44 ∧ (bq44.length ≤ 3))))) ∧ ∃ cm_sg_3 : Bytes, ∃ cm_w30_3 : Word, ((False) ∨ (False) ∨ (False) ∨ (∃ bs, base64Decode (memBytes M0 ((((s.2.1) + BitVec.ofNat 32 4)) + ((ni'_2) + BitVec.ofNat 32 0x1)) (((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)).toNat) = some bs ∧ (¬ ((BitVec.ofNat 32 (ix9_1 - 4)) = ((ni'_2) + BitVec.ofNat 32 0x1))) ∧ (memBytes M0 ((s.2.1) + BitVec.ofNat 32 4) ni'_2.toNat = memBytes M0 w48 w44.toNat) ∧ (¬ (base64Decode (memBytes M0 ((((s.2.1) + BitVec.ofNat 32 4)) + ((ni'_2) + BitVec.ofNat 32 0x1)) (((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)).toNat) = none)) ∧ (¬ (0x60 < bs.length)) ∧ (bs.length < 4) ∧ cm_sg_3 = (s.2.2.2) ∧ cm_w30_3 = (s.1)) ∨ (∃ bs, base64Decode (memBytes M0 ((((s.2.1) + BitVec.ofNat 32 4)) + ((ni'_2) + BitVec.ofNat 32 0x1)) (((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)).toNat) = some bs ∧ (¬ ((BitVec.ofNat 32 (ix9_1 - 4)) = ((ni'_2) + BitVec.ofNat 32 0x1))) ∧ (memBytes M0 ((s.2.1) + BitVec.ofNat 32 4) ni'_2.toNat = memBytes M0 w48 w44.toNat) ∧ (¬ (base64Decode (memBytes M0 ((((s.2.1) + BitVec.ofNat 32 4)) + ((ni'_2) + BitVec.ofNat 32 0x1)) (((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)).toNat) = none)) ∧ (¬ (0x60 < bs.length)) ∧ (¬ (bs.length < 4)) ∧ (le4 bs 0 = kh) ∧ (bs.length = 68) ∧ ((((s.1)) &&& BitVec.ofNat 32 0x1) = 0) ∧ cm_sg_3 = (bs.drop 4) ∧ cm_w30_3 = BitVec.ofNat 32 0x1) ∨ (False) ∨ (∃ bs, base64Decode (memBytes M0 ((((s.2.1) + BitVec.ofNat 32 4)) + ((ni'_2) + BitVec.ofNat 32 0x1)) (((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)).toNat) = some bs ∧ (¬ ((BitVec.ofNat 32 (ix9_1 - 4)) = ((ni'_2) + BitVec.ofNat 32 0x1))) ∧ (memBytes M0 ((s.2.1) + BitVec.ofNat 32 4) ni'_2.toNat = memBytes M0 w48 w44.toNat) ∧ (¬ (base64Decode (memBytes M0 ((((s.2.1) + BitVec.ofNat 32 4)) + ((ni'_2) + BitVec.ofNat 32 0x1)) (((BitVec.ofNat 32 (ix9_1 - 4))) - ((ni'_2) + BitVec.ofNat 32 0x1)).toNat) = none)) ∧ (¬ (0x60 < bs.length)) ∧ (¬ (bs.length < 4)) ∧ (¬ (le4 bs 0 = kh)) ∧ cm_sg_3 = (s.2.2.2) ∧ cm_w30_3 = (s.1)) ∨ ((¬ ((BitVec.ofNat 32 (ix9_1 - 4)) = ((ni'_2) + BitVec.ofNat 32 0x1))) ∧ (¬ (memBytes M0 ((s.2.1) + BitVec.ofNat 32 4) ni'_2.toNat = memBytes M0 w48 w44.toNat)) ∧ cm_sg_3 = (s.2.2.2) ∧ cm_w30_3 = (s.1))) ∧ s' = (cm_w30_3, ((s.2.1)) + BitVec.ofNat 32 (ix9_1 + 1), BitVec.ofNat 32 (((s.2.2.1)).toNat) - BitVec.ofNat 32 (ix9_1 + 1), cm_sg_3)

set_option linter.unusedVariables false in
/-- How `sv_csx` ends once `w50` is 0. -/
def sv_cosigloopOk (B out bp x20 x22 x23 x25 kh w48 w44 kp ckp bl : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (f' : Word) (w38' : Word) (w50' : Word) (sg' : Bytes) (nk : Machine) : Prop :=
  w50' = 0 ∧ ((((f') &&& BitVec.ofNat 32 0x1 ≠ 0) ∧
    (evSpec (sigMem M0 (B + 0x21A0 + BitVec.ofNat 32 0x420) sg') kp (B + 0x21A0 + BitVec.ofNat 32 0x420) ckp (bl).toNat = true) ∧
    ∃ n', Steps nk n' ∧
        St n'.mem SV n' 0x17F8 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg nk (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg nk (4 : Fin 32) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = (reg nk (21 : Fin 32)) ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = (reg nk (24 : Fin 32)) ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = (reg nk (26 : Fin 32)) ∧
        reg n' (27 : Fin 32) = (reg nk (27 : Fin 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f') &&& BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50' ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg'.getD (1 + j) 0)) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (sg'.getD (1 + j) 0)) ∧
        SvKeepL B nk.mem n'.mem [(0x2C, 0x4), (0x421, 0x3F), (0x420, 0x1)]))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- The checkpoint's signature loop: `k` more lines, then the end. -/
theorem sv_cosigloop {B out bp x20 x22 x23 x25 kh w48 w44 kp ckp bl : Word} {v : Nat → Word}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8) :
    ∀ (N : Nat) {f : Word} {w38 : Word} {w50 : Word} {sg : Bytes} {n0 : Machine},
    (hN : w50.toNat ≤ N) →
    (E0 : SvCode n0.mem) →
    (V0 : SvSaves B n0.mem v) →
    (s0 : St n0.mem SV n0 0x1642 (reg n0)) →
    (fM : ∀ x, SvR B x → n0.mem x = M0 x) →
    (g0_2 : reg n0 sp = B + 0x21A0) →
    (g0_18 : reg n0 (18 : Fin 32) = out) →
    (g0_19 : reg n0 (19 : Fin 32) = bp) →
    (g0_20 : reg n0 (20 : Fin 32) = x20) →
    (g0_22 : reg n0 (22 : Fin 32) = x22) →
    (g0_23 : reg n0 (23 : Fin 32) = x23) →
    (g0_25 : reg n0 (25 : Fin 32) = x25) →
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
    (sg_in : SvIn B w38 w50.toNat) →
    (CK0 : SvCkCode M0) →
    (l_in : SvIn B w48 w44.toNat) →
    (EE0 : EvEnv M0) →
    (RS : SvRoSep B) →
    (hiv : (s5Hv M0 (BitVec.ofNat 32 (img% sha512IVAddress))).toList = Sha512.h0) →
    (pk_in : SvIn B kp 32) →
    (msg_in : SvIn B ckp bl.toNat) →
    (hlen : bl.toNat < 2 ^ 31) →
    SvErrRet B out v n0 ∨ ∃ k f' w38' w50' sg', svChain (sv_cosigStep B out bp x20 x22 x23 x25 kh w48 w44 kp ckp bl v M0) k (f, w38, w50, sg) (f', w38', w50', sg') ∧
      ∃ nk, Steps n0 nk ∧ reg nk (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg nk (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
      SvKeepL B n0.mem nk.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x50, 0x4), (0xC, 0x4), (0x8, 0x4), (0x10, 0x4), (0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3), (0x420, 0x60), (0x400, 0x8), (0x14, 0x4), (0x1FC, 0x3F), (0x30, 0x4)] ∧ sv_cosigloopOk B out bp x20 x22 x23 x25 kh w48 w44 kp ckp bl v M0 f' w38' w50' sg' nk := by
  intro N
  induction N with
  | zero =>
    intro f w38 w50 sg n0 hN E0 V0 s0 fM g0_2 g0_18 g0_19 g0_20 g0_22 g0_23 g0_25 w0_18 w0_24 w0_28 w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc sg_in CK0 l_in EE0 RS hiv pk_in msg_in hlen
    have h0 : w50 = 0 := svRem_zero hN
    rcases sv_csx (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := reg n0 (21 : Fin 32)) (x22 := x22) (x23 := x23) (x24 := reg n0 (24 : Fin 32)) (x25 := x25) (x26 := reg n0 (26 : Fin 32)) (x27 := reg n0 (27 : Fin 32)) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (sg := sg) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 rfl g0_22 g0_23 rfl g0_25 rfl rfl w0_18 w0_24 w0_28 w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc h0 EE0 RS hiv pk_in msg_in hlen with ⟨-, e⟩ | okx
    · exact .inl e
    · exact .inr ⟨0, f, w38, w50, sg, svChain.nil, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), h0, okx⟩
  | succ N ih =>
    intro f w38 w50 sg n0 hN E0 V0 s0 fM g0_2 g0_18 g0_19 g0_20 g0_22 g0_23 g0_25 w0_18 w0_24 w0_28 w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc sg_in CK0 l_in EE0 RS hiv pk_in msg_in hlen
    by_cases h0 : w50 = 0
    · rcases sv_csx (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := reg n0 (21 : Fin 32)) (x22 := x22) (x23 := x23) (x24 := reg n0 (24 : Fin 32)) (x25 := x25) (x26 := reg n0 (26 : Fin 32)) (x27 := reg n0 (27 : Fin 32)) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (sg := sg) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 rfl g0_22 g0_23 rfl g0_25 rfl rfl w0_18 w0_24 w0_28 w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc h0 EE0 RS hiv pk_in msg_in hlen with ⟨-, e⟩ | okx
      · exact .inl e
      · exact .inr ⟨0, f, w38, w50, sg, svChain.nil, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), h0, okx⟩
    rcases sv_seg_cosig (B := B) (out := out) (bp := bp) (x20 := x20) (x22 := x22) (x23 := x23) (x25 := x25) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (sg := sg) (v := v) FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 rfl g0_22 g0_23 rfl g0_25 rfl rfl w0_18 w0_24 w0_28 w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc h0 sg_in CK0 l_in with e | ⟨x1_0ix9_1, x1_0, x1_1, x1_2, x1_3k_2, x1_3, x1_4, x1_5ni'_2, x1_5, x1_6, x1_7, x1_8, x1_9, x1_10pg'_3, x1_10gi'_3, x1_10, x1_11, x1_12cm_sg_3, x1_12cm_w30_3, x1_12, n1, c1, fR1, s1, E1, V1, r1_3, r1_4, r1_2, r1_8, r1_9, r1_18, r1_19, r1_20, r1_21, r1_22, r1_23, r1_24, r1_25, r1_26, r1_27, w1_8, w1_c, w1_10, w1_18, w1_24, w1_28, w1_2c, w1_30, w1_34, w1_38, w1_44, w1_48, w1_50, b1_14, q1_1fc, K1_L⟩
    · exact .inl e
    have hdec := svRem_le1 (a := x1_0ix9_1 + 1) (N := N) (by omega) (by have := (nlScan_lt _ _ _ x1_0).2; omega) hN
    rcases ih hdec E1 V1 s1 fR1 r1_2 r1_18 r1_19 r1_20 r1_22 r1_23 r1_25 w1_18 w1_24 w1_28 w1_30 w1_34 w1_38 w1_44 w1_48 w1_50 b1_14 q1_1fc (by rw [svSubOfNat_toNat (by have := (nlScan_lt _ _ _ x1_0).2; omega)]; exact (sg_in).nlRest x1_0) CK0 l_in EE0 RS hiv pk_in msg_in hlen with e | ⟨k, f', w38', w50', sg', chn, nk, cs, h3, h4, hk, okk⟩
    · exact .inl (SvErrRet.pre c1 r1_3 r1_4 (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
    · exact .inr ⟨k + 1, f', w38', w50', sg', svChain.cons ⟨h0, x1_0ix9_1, x1_0, x1_1, x1_2, x1_3k_2, x1_3, x1_4, x1_5ni'_2, x1_5, x1_6, x1_7, x1_8, x1_9, x1_10pg'_3, x1_10gi'_3, x1_10, x1_11, x1_12cm_sg_3, x1_12cm_w30_3, x1_12, rfl⟩ chn, nk, c1.trans cs, h3.trans r1_3, h4.trans r1_4, (K1_L.trans hk).mono (by decide), okk⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `sv_cosigloop` as a stage. -/
theorem sv_cosigloop_st {B out bp x20 x22 x23 x25 kh w48 w44 kp ckp bl : Word} {v : Nat → Word} {N : Nat} {f : Word} {w38 : Word} {w50 : Word} {sg : Bytes} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8)
    (hN : w50.toNat ≤ N)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (s0 : St n0.mem SV n0 0x1642 (reg n0))
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
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
    (sg_in : SvIn B w38 w50.toNat)
    (CK0 : SvCkCode M0)
    (l_in : SvIn B w48 w44.toNat)
    (EE0 : EvEnv M0)
    (RS : SvRoSep B)
    (hiv : (s5Hv M0 (BitVec.ofNat 32 (img% sha512IVAddress))).toList = Sha512.h0)
    (pk_in : SvIn B kp 32)
    (msg_in : SvIn B ckp bl.toNat)
    (hlen : bl.toNat < 2 ^ 31)
    :
    SvErrRet B out v n0 ∨
    (∃ k f' w38' w50' sg', svChain (sv_cosigStep B out bp x20 x22 x23 x25 kh w48 w44 kp ckp bl v M0) k (f, w38, w50, sg) (f', w38', w50', sg') ∧
      w50' = 0 ∧
      ((f') &&& BitVec.ofNat 32 0x1 ≠ 0) ∧ (evSpec (sigMem M0 (B + 0x21A0 + BitVec.ofNat 32 0x420) sg') kp (B + 0x21A0 + BitVec.ofNat 32 0x420) ckp (bl).toNat = true) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x17F8 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (25 : Fin 32) = x25 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f') &&& BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50' ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg'.getD (1 + j) 0)) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (sg'.getD (1 + j) 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x50, 0x4), (0xC, 0x4), (0x8, 0x4), (0x10, 0x4), (0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3), (0x420, 0x60), (0x400, 0x8), (0x14, 0x4), (0x1FC, 0x3F), (0x30, 0x4), (0x421, 0x3F), (0x420, 0x1)]) := by
  rcases sv_cosigloop (B := B) (out := out) (bp := bp) (x20 := x20) (x22 := x22) (x23 := x23) (x25 := x25) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (v := v) FW hret hO M0 N hN E0 V0 s0 fM g0_2 g0_18 g0_19 g0_20 g0_22 g0_23 g0_25 w0_18 w0_24 w0_28 w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc sg_in CK0 l_in EE0 RS hiv pk_in msg_in hlen with e | ⟨k, f', w38', w50', sg', chn, nk, cs, hr3, hr4, hkl, okh⟩
  · exact .inl e
  obtain ⟨hz, h0, h1, n1, cn, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r18, f_r19, f_r20, -, f_r22, f_r23, -, f_r25, -, -, f_w18, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w44, f_w48, f_w50, f_q1fc, f_q421, f_KL⟩ := okh
  exact .inr ⟨k, f', w38', w50', sg', chn, hz, h0, h1, n1, cs.trans cn, f_ST, f_E, f_V, f_FR, f_r2, f_r3.trans hr3, f_r4.trans hr4, f_r18, f_r19, f_r20, f_r22, f_r23, f_r25, f_w18, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w44, f_w48, f_w50, f_q1fc, f_q421, (hkl.trans f_KL).mono (by decide)⟩

/-- The signature that memory holds where the signature loop keeps a found one. -/
def svSigOf (M : Word → BitVec 8) (B : Word) : Bytes :=
  (M (B + 0x21A0 + BitVec.ofNat 32 0x14)).toNat :: memBytes M (B + 0x21A0 + BitVec.ofNat 32 0x1FC) 63

theorem svSigOf_at (M : Word → BitVec 8) (B : Word) :
    M (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 ((svSigOf M B).getD 0 0) ∧
    ∀ j, j < 63 → M (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 ((svSigOf M B).getD (1 + j) 0) := by
  refine ⟨BitVec.eq_of_toNat_eq ?_, fun j hj => BitVec.eq_of_toNat_eq ?_⟩
  · show _ = (BitVec.ofNat 8 (M (B + 0x21A0 + BitVec.ofNat 32 0x14)).toNat).toNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (M _).isLt]
  · rw [svSigOf, Nat.add_comm 1 j, List.getD_cons_succ, List.getD_eq_getElem?_getD, memBytes,
      List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.getD_some, add_ofNat_assoc,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (M _).isLt]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `sv_cosigloop_st` from the signature that memory holds where the loop keeps a found one: before any line, the loop has found none, so any value does. -/
theorem sv_cosigloop_st0 {B out bp x20 x22 x23 x25 kh w48 w44 kp ckp bl : Word} {v : Nat → Word} {N : Nat} {f : Word} {w38 : Word} {w50 : Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8)
    (hN : w50.toNat ≤ N)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (s0 : St n0.mem SV n0 0x1642 (reg n0))
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh)
    (w0_24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl)
    (w0_28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
    (sg_in : SvIn B w38 w50.toNat)
    (CK0 : SvCkCode M0)
    (l_in : SvIn B w48 w44.toNat)
    (EE0 : EvEnv M0)
    (RS : SvRoSep B)
    (hiv : (s5Hv M0 (BitVec.ofNat 32 (img% sha512IVAddress))).toList = Sha512.h0)
    (pk_in : SvIn B kp 32)
    (msg_in : SvIn B ckp bl.toNat)
    (hlen : bl.toNat < 2 ^ 31)
    :
    SvErrRet B out v n0 ∨
    (∃ sg, ∃ k f' w38' w50' sg', svChain (sv_cosigStep B out bp x20 x22 x23 x25 kh w48 w44 kp ckp bl v M0) k (f, w38, w50, sg) (f', w38', w50', sg') ∧
      w50' = 0 ∧
      ((f') &&& BitVec.ofNat 32 0x1 ≠ 0) ∧ (evSpec (sigMem M0 (B + 0x21A0 + BitVec.ofNat 32 0x420) sg') kp (B + 0x21A0 + BitVec.ofNat 32 0x420) ckp (bl).toNat = true) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x17F8 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (25 : Fin 32) = x25 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f') &&& BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50' ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg'.getD (1 + j) 0)) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 (sg'.getD (1 + j) 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x2C, 0x4), (0x420, 0x10), (0x38, 0x4), (0x50, 0x4), (0xC, 0x4), (0x8, 0x4), (0x10, 0x4), (0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3), (0x420, 0x60), (0x400, 0x8), (0x14, 0x4), (0x1FC, 0x3F), (0x30, 0x4), (0x421, 0x3F), (0x420, 0x1)]) := by
  rcases sv_cosigloop_st (sg := svSigOf n0.mem B) (b0_14 := (svSigOf_at n0.mem B).1) (q0_1fc := (svSigOf_at n0.mem B).2) (B := B) (out := out) (bp := bp) (x20 := x20) (x22 := x22) (x23 := x23) (x25 := x25) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (v := v) FW hret hO M0 hN E0 V0 s0 fM g0_2 g0_18 g0_19 g0_20 g0_22 g0_23 g0_25 w0_18 w0_24 w0_28 w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 sg_in CK0 l_in EE0 RS hiv pk_in msg_in hlen with e | h
  · exact .inl e
  · exact .inr ⟨_, h⟩

end C3.RV32.Sv
