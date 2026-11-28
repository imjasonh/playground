import C3BootProofs.Proofs.SvSeg
import C3BootProofs.Proofs.SvCg
import C3BootProofs.Proofs.SvCm

/-!
# `sigstore::verify`: A cosignature's base64, over `k` groups of four

Written by `scripts/gen-sv-loop.py` from `sv_cg`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- A cosignature's base64, over `k` groups of four. -/
theorem sv_cgloop {w2c B out bp x20 : Word} {x21 : Word} {x22 x23 : Word} {x24 : Word} {x25 : Word} {x26 x27 : Word} {f w38 w50 kh w48 w44 kp ckp bl nl ns1 ni ns10 np w8 wc w10 : Word} {sg : Bytes} {v : Nat → Word}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8) :
    ∀ (k : Nat) {pg gi : Word} {n0 : Machine},
    (E0 : SvCode n0.mem) →
    (V0 : SvSaves B n0.mem v) →
    (s0 : St n0.mem SV n0 0x16D4 (reg n0)) →
    (fM : ∀ x, SvR B x → n0.mem x = M0 x) →
    (g0_2 : reg n0 sp = B + 0x21A0) →
    (g0_8 : reg n0 (8 : Fin 32) = nl) →
    (g0_9 : reg n0 (9 : Fin 32) = ns1) →
    (g0_10 : reg n0 a0 = pg) →
    (g0_18 : reg n0 (18 : Fin 32) = out) →
    (g0_19 : reg n0 (19 : Fin 32) = bp) →
    (g0_20 : reg n0 (20 : Fin 32) = x20) →
    (g0_21 : reg n0 (21 : Fin 32) = gi) →
    (g0_22 : reg n0 (22 : Fin 32) = x22) →
    (g0_23 : reg n0 (23 : Fin 32) = x23) →
    (g0_24 : reg n0 (24 : Fin 32) = ni) →
    (g0_25 : reg n0 (25 : Fin 32) = x25) →
    (g0_26 : reg n0 (26 : Fin 32) = ns10) →
    (g0_27 : reg n0 (27 : Fin 32) = np) →
    (w0_8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8) →
    (w0_c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc) →
    (w0_10 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10) →
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh) →
    (w0_24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl) →
    (w0_28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp) →
    (w0_2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c) →
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f) →
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp) →
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38) →
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44) →
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48) →
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50) →
    (b0_14 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0)) →
    (q0_1fc : ∀ j, j < 63 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0)) →
    (∀ i, i < k → ∀ pg' gi', (pg', gi') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0x4, ((s.2)) + BitVec.ofNat 32 0x1)) i (pg, gi) → (pg' ≠ w8) ∧ (SvCkCode M0) ∧ (SvIn B pg' 4) ∧ (SvIn B (pg' + 0x1) 1) ∧ (SvIn B (pg' + 0x2) 1) ∧ (SvIn B (pg' + 0x3) 1) ∧ (SvIn B (pg') 1) ∧ (SvIn B ((pg') + BitVec.ofNat 32 0x1) 1) ∧ (SvIn B (((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) 1) ∧ (SvIn B ((((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) 1)) →
    SvErrRet B out v n0 ∨ ∃ n' pg' gi', Steps n0 n' ∧ (pg', gi') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0x4, ((s.2)) + BitVec.ofNat 32 0x1)) k (pg, gi) ∧ (∀ i, i < k → ∀ pg' gi', (pg', gi') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0x4, ((s.2)) + BitVec.ofNat 32 0x1)) i (pg, gi) → ((((M0 (pg') = 0x3D) ∧ ((gi') + BitVec.ofNat 32 0x1 = wc) ∧ ∃ bq27, base64Decode (memBytes M0 pg' 4) = some bq27 ∧ (bq27.length ≤ 3)) ∨ ((¬ (M0 (pg') = 0x3D)) ∧ (M0 ((pg') + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi') + BitVec.ofNat 32 0x1 = wc) ∧ ∃ bq33, base64Decode (memBytes M0 pg' 4) = some bq33 ∧ (bq33.length ≤ 3)) ∨ ((¬ (M0 (pg') = 0x3D)) ∧ (¬ (M0 ((pg') + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (M0 (((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi') + BitVec.ofNat 32 0x1 = wc) ∧ ∃ bq39, base64Decode (memBytes M0 pg' 4) = some bq39 ∧ (bq39.length ≤ 3)) ∨ ((¬ (M0 (pg') = 0x3D)) ∧ (¬ (M0 ((pg') + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 (((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (M0 ((((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi') + BitVec.ofNat 32 0x1 = wc) ∧ ∃ bq45, base64Decode (memBytes M0 pg' 4) = some bq45 ∧ (bq45.length ≤ 3)) ∨ ((¬ (M0 (pg') = 0x3D)) ∧ (¬ (M0 ((pg') + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 (((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 ((((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ ∃ bq44, base64Decode (memBytes M0 pg' 4) = some bq44 ∧ (bq44.length ≤ 3))))) ∧
      reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
      SvKeepL B n0.mem n'.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3)] ∧
      SvCode n'.mem ∧
      SvSaves B n'.mem v ∧
      St n'.mem SV n' 0x16D4 (reg n') ∧
      (∀ x, SvR B x → n'.mem x = M0 x) ∧
      reg n' sp = B + 0x21A0 ∧
      reg n' (8 : Fin 32) = nl ∧
      reg n' (9 : Fin 32) = ns1 ∧
      reg n' a0 = pg' ∧
      reg n' (18 : Fin 32) = out ∧
      reg n' (19 : Fin 32) = bp ∧
      reg n' (20 : Fin 32) = x20 ∧
      reg n' (21 : Fin 32) = gi' ∧
      reg n' (22 : Fin 32) = x22 ∧
      reg n' (23 : Fin 32) = x23 ∧
      reg n' (24 : Fin 32) = ni ∧
      reg n' (25 : Fin 32) = x25 ∧
      reg n' (26 : Fin 32) = ns10 ∧
      reg n' (27 : Fin 32) = np ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
      n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0) ∧
      (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0)) := by
  intro k
  induction k with
  | zero =>
    intro pg gi n0 E0 V0 s0 fM g0_2 g0_8 g0_9 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_10 w0_18 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc _
    exact .inr ⟨n0, pg, gi, .refl _, (svIter_zero _ (pg, gi)).symm, fun i hi => absurd hi (Nat.not_lt_zero i), rfl, rfl, SvKeepL.refl.mono (by decide), E0, V0, s0, fM, g0_2, g0_8, g0_9, g0_10, g0_18, g0_19, g0_20, g0_21, g0_22, g0_23, g0_24, g0_25, g0_26, g0_27, w0_8, w0_c, w0_10, w0_18, w0_24, w0_28, w0_2c, w0_30, w0_34, w0_38, w0_44, w0_48, w0_50, b0_14, q0_1fc⟩
  | succ k ih =>
    intro pg gi n0 E0 V0 s0 fM g0_2 g0_8 g0_9 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_10 w0_18 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc H
    obtain ⟨hne, CK0, pg_in, pb1, pb2, pb3, pc0, pc1, pc2, pc3⟩ := H 0 (Nat.succ_pos k) pg gi (svIter_zero _ (pg, gi)).symm
    rcases sv_cg (w2c := w2c) (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (pg := pg) (gi := gi) (nl := nl) (ns1 := ns1) (ni := ni) (ns10 := ns10) (np := np) (w8 := w8) (wc := wc) (w10 := w10) (sg := sg) (v := v) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_10 w0_18 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc hne CK0 pg_in pb1 pb2 pb3 pc0 pc1 pc2 pc3 with e | ⟨x1_0, n1, c1, s1, E1, V1, fR1, r1_2, r1_3, r1_4, r1_8, r1_9, r1_a0, r1_18, r1_19, r1_20, r1_21, r1_22, r1_23, r1_24, r1_25, r1_26, r1_27, w1_4, w1_8, w1_c, w1_10, w1_18, w1_24, w1_28, w1_2c, w1_30, w1_34, w1_38, w1_44, w1_48, w1_50, w1_400, b1_14, q1_1fc, K1_L⟩
    · exact .inl e
    rcases ih E1 V1 s1 fR1 r1_2 r1_8 r1_9 r1_a0 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 r1_24 r1_25 r1_26 r1_27 w1_8 w1_c w1_10 w1_18 w1_24 w1_28 w1_2c w1_30 w1_34 w1_38 w1_44 w1_48 w1_50 b1_14 q1_1fc (fun i hi pg' gi' e0 => H (i + 1) (Nat.succ_lt_succ hi) pg' gi' (e0.trans (svIter_succ _ i (pg, gi)).symm)) with e | ⟨n', pg', gi', cs, e0, hsc, h3, h4, hk, rest⟩
    · exact .inl (SvErrRet.pre c1 r1_3 r1_4 (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
    · refine .inr ⟨n', pg', gi', c1.trans cs, (e0.trans (svIter_succ _ k (pg, gi)).symm), fun i hi pg' gi' e1 => ?_, h3.trans r1_3, h4.trans r1_4, (K1_L.trans hk).mono (by decide), rest⟩
      cases i with
      | zero => cases e1.trans (svIter_zero _ (pg, gi)); exact x1_0
      | succ i => exact hsc i (by omega) pg' gi' (e1.trans (svIter_succ _ i (pg, gi)))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `N` iterations of `sv_cgloop`, then `sv_cm`, as a stage. -/
theorem sv_cgloop_st {w2c B out bp x20 : Word} {x21 : Word} {x22 x23 : Word} {x24 : Word} {x25 : Word} {x26 x27 : Word} {f w38 w50 kh w48 w44 kp ckp bl nl ns1 ni ns10 np w8 wc w10 : Word} {sg : Bytes} {v : Nat → Word} {N : Nat} {pg gi : Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8)
    (hz : ∀ pg' gi', (pg', gi') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0x4, ((s.2)) + BitVec.ofNat 32 0x1)) N (pg, gi) → pg' = w8)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (s0 : St n0.mem SV n0 0x16D4 (reg n0))
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = nl)
    (g0_9 : reg n0 (9 : Fin 32) = ns1)
    (g0_10 : reg n0 a0 = pg)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = gi)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = ni)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = ns10)
    (g0_27 : reg n0 (27 : Fin 32) = np)
    (w0_8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8)
    (w0_c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc)
    (w0_10 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10)
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh)
    (w0_24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl)
    (w0_28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp)
    (w0_2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
    (b0_14 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0))
    (q0_1fc : ∀ j, j < 63 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0))
    (H : ∀ i, i < N → ∀ pg' gi', (pg', gi') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0x4, ((s.2)) + BitVec.ofNat 32 0x1)) i (pg, gi) → (pg' ≠ w8) ∧ (SvCkCode M0) ∧ (SvIn B pg' 4) ∧ (SvIn B (pg' + 0x1) 1) ∧ (SvIn B (pg' + 0x2) 1) ∧ (SvIn B (pg' + 0x3) 1) ∧ (SvIn B (pg') 1) ∧ (SvIn B ((pg') + BitVec.ofNat 32 0x1) 1) ∧ (SvIn B (((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) 1) ∧ (SvIn B ((((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) 1))
    (nm_in : SvIn B np ni.toNat)
    (l_in : SvIn B w48 w44.toNat)
    (CK0 : SvCkCode M0)
    (b_in : SvIn B w10 ns10.toNat)
    :
    SvErrRet B out v n0 ∨
    (∃ pg' gi', (pg', gi') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0x4, ((s.2)) + BitVec.ofNat 32 0x1)) N (pg, gi) ∧ (∀ i, i < N → ∀ pg' gi', (pg', gi') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0x4, ((s.2)) + BitVec.ofNat 32 0x1)) i (pg, gi) → ((((M0 (pg') = 0x3D) ∧ ((gi') + BitVec.ofNat 32 0x1 = wc) ∧ ∃ bq27, base64Decode (memBytes M0 pg' 4) = some bq27 ∧ (bq27.length ≤ 3)) ∨ ((¬ (M0 (pg') = 0x3D)) ∧ (M0 ((pg') + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi') + BitVec.ofNat 32 0x1 = wc) ∧ ∃ bq33, base64Decode (memBytes M0 pg' 4) = some bq33 ∧ (bq33.length ≤ 3)) ∨ ((¬ (M0 (pg') = 0x3D)) ∧ (¬ (M0 ((pg') + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (M0 (((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi') + BitVec.ofNat 32 0x1 = wc) ∧ ∃ bq39, base64Decode (memBytes M0 pg' 4) = some bq39 ∧ (bq39.length ≤ 3)) ∨ ((¬ (M0 (pg') = 0x3D)) ∧ (¬ (M0 ((pg') + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 (((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (M0 ((((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi') + BitVec.ofNat 32 0x1 = wc) ∧ ∃ bq45, base64Decode (memBytes M0 pg' 4) = some bq45 ∧ (bq45.length ≤ 3)) ∨ ((¬ (M0 (pg') = 0x3D)) ∧ (¬ (M0 ((pg') + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 (((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 ((((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ ∃ bq44, base64Decode (memBytes M0 pg' 4) = some bq44 ∧ (bq44.length ≤ 3))))) ∧
      ∃ cm_sg : Bytes, ∃ cm_w30 : Word, ((False) ∨ (False) ∨ (False) ∨ (∃ bs, base64Decode (memBytes M0 w10 ns10.toNat) = some bs ∧ (¬ (nl = ns1)) ∧ (memBytes M0 np ni.toNat = memBytes M0 w48 w44.toNat) ∧ (¬ (base64Decode (memBytes M0 w10 ns10.toNat) = none)) ∧ (¬ (0x60 < bs.length)) ∧ (bs.length < 4) ∧ cm_sg = sg ∧ cm_w30 = f) ∨ (∃ bs, base64Decode (memBytes M0 w10 ns10.toNat) = some bs ∧ (¬ (nl = ns1)) ∧ (memBytes M0 np ni.toNat = memBytes M0 w48 w44.toNat) ∧ (¬ (base64Decode (memBytes M0 w10 ns10.toNat) = none)) ∧ (¬ (0x60 < bs.length)) ∧ (¬ (bs.length < 4)) ∧ (le4 bs 0 = kh) ∧ (bs.length = 68) ∧ (w2c = 0) ∧ cm_sg = (bs.drop 4) ∧ cm_w30 = BitVec.ofNat 32 0x1) ∨ (False) ∨ (∃ bs, base64Decode (memBytes M0 w10 ns10.toNat) = some bs ∧ (¬ (nl = ns1)) ∧ (memBytes M0 np ni.toNat = memBytes M0 w48 w44.toNat) ∧ (¬ (base64Decode (memBytes M0 w10 ns10.toNat) = none)) ∧ (¬ (0x60 < bs.length)) ∧ (¬ (bs.length < 4)) ∧ (¬ (le4 bs 0 = kh)) ∧ cm_sg = sg ∧ cm_w30 = f) ∨ ((¬ (nl = ns1)) ∧ (¬ (memBytes M0 np ni.toNat = memBytes M0 w48 w44.toNat)) ∧ cm_sg = sg ∧ cm_w30 = f)) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x1642 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = nl ∧
        reg n' (9 : Fin 32) = ns1 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = gi' ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = ni ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = ns10 ∧
        reg n' (27 : Fin 32) = np ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = cm_w30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (cm_sg.getD 0 0) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (cm_sg.getD (1 + j) 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3), (0x420, 0x60), (0x400, 0x8), (0x14, 0x4), (0x1FC, 0x3F), (0x30, 0x4)]) := by
  rcases sv_cgloop (w2c := w2c) (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (nl := nl) (ns1 := ns1) (ni := ni) (ns10 := ns10) (np := np) (w8 := w8) (wc := wc) (w10 := w10) (sg := sg) (v := v) FW hret hO M0 N E0 V0 s0 fM g0_2 g0_8 g0_9 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_10 w0_18 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc H with e | ⟨n1, pg', gi', cs, e0, hsc, hr3, hr4, hkl, E0', V0', s0', fM', g0_2', g0_8', g0_9', g0_10', g0_18', g0_19', g0_20', g0_21', g0_22', g0_23', g0_24', g0_25', g0_26', g0_27', w0_8', w0_c', w0_10', w0_18', w0_24', w0_28', w0_2c', w0_30', w0_34', w0_38', w0_44', w0_48', w0_50', b0_14', q0_1fc'⟩
  · exact .inl e
  rcases sv_cm (w2c := w2c) (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (pg := pg') (gi := gi') (nl := nl) (ns1 := ns1) (ni := ni) (ns10 := ns10) (np := np) (w8 := w8) (wc := wc) (w10 := w10) (sg := sg) (v := v) FW E0' V0' hret hO s0' M0 fM' g0_2' g0_8' g0_9' g0_10' g0_18' g0_19' g0_20' g0_21' g0_22' g0_23' g0_24' g0_25' g0_26' g0_27' w0_8' w0_c' w0_10' w0_18' w0_24' w0_28' w0_2c' w0_30' w0_34' w0_38' w0_44' w0_48' w0_50' b0_14' q0_1fc' (hz pg' gi' e0) nm_in l_in CK0 b_in with e | ⟨cm_sg, cm_w30, h0, n2, c2, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w8, f_wc, f_w10, f_w18, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w44, f_w48, f_w50, f_b14, f_q1fc, f_KL⟩
  · exact .inl (SvErrRet.pre cs hr3 hr4 (fun x hx => (fM' x hx).trans (fM x hx).symm) e)
  exact .inr ⟨pg', gi', e0, hsc, cm_sg, cm_w30, h0, n2, cs.trans c2, f_ST, f_E, f_V, f_FR, f_r2, f_r3.trans hr3, f_r4.trans hr4, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w8, f_wc, f_w10, f_w18, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w44, f_w48, f_w50, f_b14, f_q1fc, (hkl.trans f_KL).mono (by decide)⟩

set_option maxHeartbeats 16000000 in
/-- `sv_cgloop_st` over `N` groups of 4 bytes from `pg` to `w8`. -/
theorem sv_cgloop_run {w2c B out bp x20 : Word} {x21 : Word} {x22 x23 : Word} {x24 : Word} {x25 : Word} {x26 x27 : Word} {f w38 w50 kh w48 w44 kp ckp bl nl ns1 ni ns10 np w8 wc w10 : Word} {sg : Bytes} {v : Nat → Word} {N : Nat} {pg gi : Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (s0 : St n0.mem SV n0 0x16D4 (reg n0))
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = nl)
    (g0_9 : reg n0 (9 : Fin 32) = ns1)
    (g0_10 : reg n0 a0 = pg)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = gi)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = ni)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = ns10)
    (g0_27 : reg n0 (27 : Fin 32) = np)
    (w0_8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8)
    (w0_c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc)
    (w0_10 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10)
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh)
    (w0_24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl)
    (w0_28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp)
    (w0_2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
    (b0_14 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (sg.getD 0 0))
    (q0_1fc : ∀ j, j < 63 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (sg.getD (1 + j) 0))
    (hend : w8 = pg + BitVec.ofNat 32 (N * 4)) (slice : SvIn B pg (N * 4))
    (b_in : SvIn B w10 ns10.toNat)
    (CK0 : SvCkCode M0)
    (l_in : SvIn B w48 w44.toNat)
    (nm_in : SvIn B np ni.toNat)
    :
    SvErrRet B out v n0 ∨
    (∃ pg' gi', (pg', gi') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0x4, ((s.2)) + BitVec.ofNat 32 0x1)) N (pg, gi) ∧ (∀ i, i < N → ∀ pg' gi', (pg', gi') = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0x4, ((s.2)) + BitVec.ofNat 32 0x1)) i (pg, gi) → ((((M0 (pg') = 0x3D) ∧ ((gi') + BitVec.ofNat 32 0x1 = wc) ∧ ∃ bq27, base64Decode (memBytes M0 pg' 4) = some bq27 ∧ (bq27.length ≤ 3)) ∨ ((¬ (M0 (pg') = 0x3D)) ∧ (M0 ((pg') + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi') + BitVec.ofNat 32 0x1 = wc) ∧ ∃ bq33, base64Decode (memBytes M0 pg' 4) = some bq33 ∧ (bq33.length ≤ 3)) ∨ ((¬ (M0 (pg') = 0x3D)) ∧ (¬ (M0 ((pg') + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (M0 (((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi') + BitVec.ofNat 32 0x1 = wc) ∧ ∃ bq39, base64Decode (memBytes M0 pg' 4) = some bq39 ∧ (bq39.length ≤ 3)) ∨ ((¬ (M0 (pg') = 0x3D)) ∧ (¬ (M0 ((pg') + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 (((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (M0 ((((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D) ∧ ((gi') + BitVec.ofNat 32 0x1 = wc) ∧ ∃ bq45, base64Decode (memBytes M0 pg' 4) = some bq45 ∧ (bq45.length ≤ 3)) ∨ ((¬ (M0 (pg') = 0x3D)) ∧ (¬ (M0 ((pg') + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 (((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ (¬ (M0 ((((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = 0x3D)) ∧ ∃ bq44, base64Decode (memBytes M0 pg' 4) = some bq44 ∧ (bq44.length ≤ 3))))) ∧
      ∃ cm_sg : Bytes, ∃ cm_w30 : Word, ((False) ∨ (False) ∨ (False) ∨ (∃ bs, base64Decode (memBytes M0 w10 ns10.toNat) = some bs ∧ (¬ (nl = ns1)) ∧ (memBytes M0 np ni.toNat = memBytes M0 w48 w44.toNat) ∧ (¬ (base64Decode (memBytes M0 w10 ns10.toNat) = none)) ∧ (¬ (0x60 < bs.length)) ∧ (bs.length < 4) ∧ cm_sg = sg ∧ cm_w30 = f) ∨ (∃ bs, base64Decode (memBytes M0 w10 ns10.toNat) = some bs ∧ (¬ (nl = ns1)) ∧ (memBytes M0 np ni.toNat = memBytes M0 w48 w44.toNat) ∧ (¬ (base64Decode (memBytes M0 w10 ns10.toNat) = none)) ∧ (¬ (0x60 < bs.length)) ∧ (¬ (bs.length < 4)) ∧ (le4 bs 0 = kh) ∧ (bs.length = 68) ∧ (w2c = 0) ∧ cm_sg = (bs.drop 4) ∧ cm_w30 = BitVec.ofNat 32 0x1) ∨ (False) ∨ (∃ bs, base64Decode (memBytes M0 w10 ns10.toNat) = some bs ∧ (¬ (nl = ns1)) ∧ (memBytes M0 np ni.toNat = memBytes M0 w48 w44.toNat) ∧ (¬ (base64Decode (memBytes M0 w10 ns10.toNat) = none)) ∧ (¬ (0x60 < bs.length)) ∧ (¬ (bs.length < 4)) ∧ (¬ (le4 bs 0 = kh)) ∧ cm_sg = sg ∧ cm_w30 = f) ∨ ((¬ (nl = ns1)) ∧ (¬ (memBytes M0 np ni.toNat = memBytes M0 w48 w44.toNat)) ∧ cm_sg = sg ∧ cm_w30 = f)) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x1642 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = nl ∧
        reg n' (9 : Fin 32) = ns1 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = gi' ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = ni ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = ns10 ∧
        reg n' (27 : Fin 32) = np ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = kh ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = bl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = ckp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = cm_w30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = BitVec.ofNat 8 (cm_sg.getD 0 0) ∧
        (∀ j, j < 63 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1FC + j)) = BitVec.ofNat 8 (cm_sg.getD (1 + j) 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x4, 0x4), (0x400, 0x4), (0x420, 0x8), (0x370, 0x3), (0x420, 0x60), (0x400, 0x8), (0x14, 0x4), (0x1FC, 0x3F), (0x30, 0x4)]) := by
  have fit := slice.fit
  refine sv_cgloop_st (w2c := w2c) (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (f := f) (w38 := w38) (w50 := w50) (kh := kh) (w48 := w48) (w44 := w44) (kp := kp) (ckp := ckp) (bl := bl) (nl := nl) (ns1 := ns1) (ni := ni) (ns10 := ns10) (np := np) (w8 := w8) (wc := wc) (w10 := w10) (sg := sg) (v := v) (N := N) FW hret hO M0 ?_ E0 V0 s0 fM g0_2 g0_8 g0_9 g0_10 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_8 w0_c w0_10 w0_18 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_44 w0_48 w0_50 b0_14 q0_1fc ?_ nm_in l_in CK0 b_in
  · intro pg' gi' e
    have h1 := congrArg (fun s => s.1) e
    simp only at h1
    rw [svIter_add (F := (fun s => (((s.1)) + BitVec.ofNat 32 0x4, ((s.2)) + BitVec.ofNat 32 0x1))) (fun s : Word × Word => s.1) (d := 4) (fun s => rfl)] at h1
    simp only at h1
    rw [h1, hend, Nat.mul_comm]
  · intro i hi pg' gi' e
    have h2 := congrArg (fun s => s.1) e
    simp only at h2
    rw [svIter_add (F := (fun s => (((s.1)) + BitVec.ofNat 32 0x4, ((s.2)) + BitVec.ofNat 32 0x1))) (fun s : Word × Word => s.1) (d := 4) (fun s => rfl)] at h2
    simp only at h2
    have G : SvIn B pg' 4 := by rw [h2, Nat.mul_comm]; exact (slice.drop (k := 4 * i) (by omega)).shrink (by omega)
    exact ⟨(by rw [h2, hend]; bv_omega), (CK0), (G), (by rw [show (pg' + 0x1) = pg' + BitVec.ofNat 32 1 by bv_omega]; exact (G.drop (k := 1) (by omega)).shrink (by omega)), (by rw [show (pg' + 0x2) = pg' + BitVec.ofNat 32 2 by bv_omega]; exact (G.drop (k := 2) (by omega)).shrink (by omega)), (by rw [show (pg' + 0x3) = pg' + BitVec.ofNat 32 3 by bv_omega]; exact (G.drop (k := 3) (by omega)).shrink (by omega)), (by rw [show (pg') = pg' + BitVec.ofNat 32 0 by bv_omega]; exact (G.drop (k := 0) (by omega)).shrink (by omega)), (by rw [show ((pg') + BitVec.ofNat 32 0x1) = pg' + BitVec.ofNat 32 1 by bv_omega]; exact (G.drop (k := 1) (by omega)).shrink (by omega)), (by rw [show (((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = pg' + BitVec.ofNat 32 2 by bv_omega]; exact (G.drop (k := 2) (by omega)).shrink (by omega)), (by rw [show ((((pg') + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) + BitVec.ofNat 32 0x1) = pg' + BitVec.ofNat 32 3 by bv_omega]; exact (G.drop (k := 3) (by omega)).shrink (by omega))⟩

end C3.RV32.Sv
