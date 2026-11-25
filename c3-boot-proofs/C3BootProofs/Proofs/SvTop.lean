import C3BootProofs.Proofs.SvSegSv
import C3BootProofs.Proofs.SvOk

/-!
# `sigstore::verify` from 0x5C to its return

Written by `scripts/gen-sv-top.py` from `sv_seg_sv` and `sv_ok_1a9e`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.P2v

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
/-- **`sigstore::verify` from 0x5C to its return**: it returns `Err`, panics, or meets the success condition and returns `Ok`. -/
theorem sv_verify_5c {B out bp rootp dg lp ll : Word} {v : Nat → Word} {n0 : Machine} {sl5 : Word} {sl7 : Word} {sl9 : Word}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x5C (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_10 : reg n0 a0 = B + 0x21A0 + BitVec.ofNat 32 0x80)
    (g0_11 : reg n0 a1 = B + 0x21A0 + BitVec.ofNat 32 0x360)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = dg)
    (g0_21 : reg n0 (21 : Fin 32) = rootp)
    (g0_22 : reg n0 (22 : Fin 32) = ll)
    (g0_26 : reg n0 (26 : Fin 32) = lp)
    (w0_360 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp)
    (w0_364 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll)
    (w0_368 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = lp)
    (w0_36c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = ll)
    (lc_in : SvIn B lp ll.toNat)
    (D0 : P2Data M0)
    (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5)
    (w0_9c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7)
    (w0_a4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9)
    (SD0 : SvData M0)
    (H' : ∀ i, i < 8 → ∀ c'_4 q'_4, (c'_4, q'_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((rootp) + BitVec.ofNat 32 0x2C)) → (SvIn B (q'_4 + 0xFFFFFFFC) 4) ∧ (SvIn B (q'_4 + 0x0) 4) ∧ ((q'_4 + 0xFFFFFFFC).toNat % 4 = 0) ∧ ((q'_4 + 0x0).toNat % 4 = 0) ∧ ((memLoad32 M0 (q'_4 + 0xFFFFFFFC)) ≠ 0 → SvIn B (memLoad32 M0 (q'_4 + 0xFFFFFFFC)) (memLoad32 M0 (q'_4 + 0x0)).toNat))
    (HE0 : HfEnv M0)
    (RS : SvRoSep B)
    (PE0 : PvEnv7 M0)
    (pkp_in : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x2C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4) 4)
    (apk : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x2C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4).toNat % 4 = 0)
    (pk_in : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x2C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (memLoad32 M0 (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4)) 0x61)
    (side : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x2C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → ∀ M, PvSide M (memLoad32 M0 (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4)) (B + 0x21A0 + BitVec.ofNat 32 0x170) 48 (B + 0x21A0 + BitVec.ofNat 32 0xC8)
      (B + 0x21A0 + BitVec.ofNat 32 0xF8))
    (he0p_in : SvIn B (rootp + 0x0) 4)
    (he0l_in : SvIn B (rootp + 0x4) 4)
    (ae0p : (rootp + 0x0).toNat % 4 = 0)
    (ae0l : (rootp + 0x4).toNat % 4 = 0)
    (e0_in : SvRo B (memLoad32 M0 (rootp + 0x0)) (memLoad32 M0 (rootp + 0x4)).toNat)
    (he1p_in : SvIn B (rootp + 0x8) 4)
    (he1l_in : SvIn B (rootp + 0xC) 4)
    (ae1p : (rootp + 0x8).toNat % 4 = 0)
    (ae1l : (rootp + 0xC).toNat % 4 = 0)
    (e1_in : SvRo B (memLoad32 M0 (rootp + 0x8)) (memLoad32 M0 (rootp + 0xC)).toNat)
    (he2p_in : SvIn B (rootp + 0x10) 4)
    (he2l_in : SvIn B (rootp + 0x14) 4)
    (ae2p : (rootp + 0x10).toNat % 4 = 0)
    (ae2l : (rootp + 0x14).toNat % 4 = 0)
    (e2_in : SvRo B (memLoad32 M0 (rootp + 0x10)) (memLoad32 M0 (rootp + 0x14)).toNat)
    (he3p_in : SvIn B (rootp + 0x18) 4)
    (he3l_in : SvIn B (rootp + 0x1C) 4)
    (ae3p : (rootp + 0x18).toNat % 4 = 0)
    (ae3l : (rootp + 0x1C).toNat % 4 = 0)
    (e3_in : SvRo B (memLoad32 M0 (rootp + 0x18)) (memLoad32 M0 (rootp + 0x1C)).toNat)
    (he4p_in : SvIn B (rootp + 0x20) 4)
    (he4l_in : SvIn B (rootp + 0x24) 4)
    (ae4p : (rootp + 0x20).toNat % 4 = 0)
    (ae4l : (rootp + 0x24).toNat % 4 = 0)
    (e4_in : SvRo B (memLoad32 M0 (rootp + 0x20)) (memLoad32 M0 (rootp + 0x24)).toNat)
    (hsgp_in : SvIn B (bp + 0x8) 4)
    (hsgl_in : SvIn B (bp + 0xC) 4)
    (asgp : (bp + 0x8).toNat % 4 = 0)
    (asgl : (bp + 0xC).toNat % 4 = 0)
    (sg_in : SvIn B (memLoad32 M0 (bp + 0x8)) (memLoad32 M0 (bp + 0xC)).toNat)
    (PE0' : P2vEnv M0)
    (dg_in : SvIn B dg 32)
    (htsp_in : SvIn B (bp + 0x20) 4)
    (htsl_in : SvIn B (bp + 0x24) 4)
    (atsp : (bp + 0x20).toNat % 4 = 0)
    (atsl : (bp + 0x24).toNat % 4 = 0)
    (ts_in : SvIn B (memLoad32 M0 (bp + 0x20)) (memLoad32 M0 (bp + 0x24)).toNat)
    (D0' : SvData M0)
    (H'' : ∀ i, i < 8 → ∀ c'_6_3 q'_6_3, (c'_6_3, q'_6_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((rootp) + BitVec.ofNat 32 0x308)) → (SvIn B (q'_6_3 + 0x20) 4) ∧ (SvIn B (q'_6_3 + 0x24) 4) ∧ ((q'_6_3 + 0x20).toNat % 4 = 0) ∧ ((q'_6_3 + 0x24).toNat % 4 = 0) ∧ ((memLoad32 M0 (q'_6_3 + 0x20)) ≠ 0 → SvIn B (memLoad32 M0 (q'_6_3 + 0x20)) (memLoad32 M0 (q'_6_3 + 0x24)).toNat))
    (S2 : SvSha2Code M0)
    (pkp_in' : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x308)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x18) 4)
    (apk' : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x308)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x18).toNat % 4 = 0)
    (pk_in' : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x308)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (memLoad32 M0 (((y1) + BitVec.ofNat 32 0x20) + 0x18)) 0x61)
    (side' : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x308)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → ∀ M, PvSide M (memLoad32 M0 (((y1) + BitVec.ofNat 32 0x20) + 0x18)) (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 (B + 0x21A0 + BitVec.ofNat 32 0x190)
      (B + 0x21A0 + BitVec.ofNat 32 0x1C0))
    (CK0 : SvCkCode M0)
    (ckp_in4 : SvIn B (bp + 0x18) 4)
    (ckl_in4 : SvIn B (bp + 0x1C) 4)
    (a_ckp : (bp + 0x18).toNat % 4 = 0)
    (a_ckl : (bp + 0x1C).toNat % 4 = 0)
    (ck_in : SvIn B (memLoad32 M0 (bp + 0x18)) (memLoad32 M0 (bp + 0x1C)).toNat)
    (H''' : ∀ i, i < 16 → ∀ c'_3_4 q'_3_4, (c'_3_4, q'_3_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), ((rootp) + BitVec.ofNat 32 0x108)) → (SvIn B (q'_3_4 + 0x20) 4) ∧ (SvIn B (q'_3_4 + 0x24) 4) ∧ ((q'_3_4 + 0x20).toNat % 4 = 0) ∧ ((q'_3_4 + 0x24).toNat % 4 = 0) ∧ ((memLoad32 M0 (q'_3_4 + 0x20)) ≠ 0 → SvIn B (memLoad32 M0 (q'_3_4 + 0x20)) (memLoad32 M0 (q'_3_4 + 0x24)).toNat))
    (kp_in4 : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), (rootp + BitVec.ofNat 32 0x108)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x18) 4)
    (kw_in4 : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), (rootp + BitVec.ofNat 32 0x108)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x1C) 4)
    (a_kp : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), (rootp + BitVec.ofNat 32 0x108)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x18).toNat % 4 = 0)
    (a_kw : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), (rootp + BitVec.ofNat 32 0x108)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x1C).toNat % 4 = 0)
    (kp_in : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), (rootp + BitVec.ofNat 32 0x108)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (memLoad32 M0 (((y1) + BitVec.ofNat 32 0x20) + 0x18)) 32)
    (EE0 : EvEnv M0)
    (hiv : (s5Hv M0 (BitVec.ofNat 32 (img% sha512IVAddress))).toList = Sha512.h0)
    (pk_in'' : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), (rootp + BitVec.ofNat 32 0x108)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (memLoad32 M0 (((y1) + BitVec.ofNat 32 0x20) + 0x18)) 32)
    (lid_in : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), (rootp + BitVec.ofNat 32 0x108)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + BitVec.ofNat 32 0x5) 19)
    (lih_in : SvIn B (bp + 0x2C) 4)
    (lil_in : SvIn B (bp + 0x28) 4)
    (a_lih : (bp + 0x2C).toNat % 4 = 0)
    (a_lil : (bp + 0x28).toNat % 4 = 0)
    (RK0 : SvRkCode M0)
    (dgi_in : SvIn B dg 32)
    (pp_in4 : SvIn B (bp + 0x10) 4)
    (pl_in4 : SvIn B (bp + 0x14) 4)
    (a_pp : (bp + 0x10).toNat % 4 = 0)
    (a_pl : (bp + 0x14).toNat % 4 = 0)
    (pp_in : SvIn B (memLoad32 M0 (bp + 0x10)) (memLoad32 M0 (bp + 0x14)).toNat)
    (ii2h : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x2C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8) 4)
    (ai2h : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x2C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8).toNat % 4 = 0)
    (ii2l : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x2C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE4) 4)
    (ai2l : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x2C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE4).toNat % 4 = 0)
    (ii3h : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x2C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0) 4)
    (ai3h : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x2C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0).toNat % 4 = 0)
    (ii3l : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x2C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFEC) 4)
    (ai3l : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x2C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFEC).toNat % 4 = 0)
    (it4h : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x308)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xC) 4)
    (at4h : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x308)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xC).toNat % 4 = 0)
    (it4l : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x308)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x8) 4)
    (at4l : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x308)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x8).toNat % 4 = 0)
    (it5h : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x308)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x14) 4)
    (at5h : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x308)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x14).toNat % 4 = 0)
    (it5l : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x308)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x10) 4)
    (at5l : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x308)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x10).toNat % 4 = 0)
    (hOk : SvOutOk B out) :
    SvErrRet B out v n0 ∨ Panics n0 ∨
    (∃ t_1_1_1, derElement 0x30 (memBytes M0 lp ll.toNat) = .ok t_1_1_1 ∧ ll - BitVec.ofNat 32 (t_1_1_1.header + t_1_1_1.len) = 0 ∧
      ∃ tl1_2_1_1, derElement 0x30 (memBytes M0 ((lp + BitVec.ofNat 32 t_1_1_1.header)) ((BitVec.ofNat 32 t_1_1_1.len)).toNat) = .ok tl1_2_1_1 ∧
      ∃ tl8_2_1_1, derElement 0x30 (memBytes M0 (((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) (((BitVec.ofNat 32 t_1_1_1.len)) - BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)).toNat) = .ok tl8_2_1_1 ∧
      ∃ tl16_2_1_1, derElement 3 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) + BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) ((((BitVec.ofNat 32 t_1_1_1.len)) - BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) - BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)).toNat) = .ok tl16_2_1_1 ∧
      ∃ bp16_2_1_1 bl16_2_1_1, derBitsOf (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) + BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) ((((BitVec.ofNat 32 t_1_1_1.len)) - BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) - BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)).toNat) ((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) + BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) (.ok tl16_2_1_1) = .ok (bp16_2_1_1, bl16_2_1_1) ∧
      (((((BitVec.ofNat 32 t_1_1_1.len)) - BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) - BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) - BitVec.ofNat 32 (tl16_2_1_1.header + tl16_2_1_1.len) = 0) ∧
      ∃ tl28_2_1_1, derOptRes 0xA0 (memBytes M0 (((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) (BitVec.ofNat 32 tl1_2_1_1.len).toNat) = some (.ok tl28_2_1_1) ∧
      derIntIsOf M0 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 tl28_2_1_1.header) (BitVec.ofNat 32 tl28_2_1_1.len).toNat) ((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 tl28_2_1_1.header) (derElement 2 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 tl28_2_1_1.header) (BitVec.ofNat 32 tl28_2_1_1.len).toNat)) ((BitVec.ofNat 32 0x2).extractLsb' 0 8) = .ok true ∧
      ∃ te41_2_1_1, derElement 2 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 tl28_2_1_1.header) (BitVec.ofNat 32 tl28_2_1_1.len).toNat) = .ok te41_2_1_1 ∧
      ((BitVec.ofNat 32 tl28_2_1_1.len) - BitVec.ofNat 32 (te41_2_1_1.header + te41_2_1_1.len) = 0) ∧
      ∃ tl1_3_1_1, derElement 2 (memBytes M0 (((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) (((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))).toNat) = .ok tl1_3_1_1 ∧
      ∃ ip1_3_1_1 il1_3_1_1, derPosIntOf (memBytes M0 (((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) (((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))).toNat) (((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) (.ok tl1_3_1_1) = .ok (ip1_3_1_1, il1_3_1_1) ∧
      ((il1_3_1_1).toNat ≤ 20) ∧
      ∃ tl8_3_1_1, derElement 0x30 (memBytes M0 ((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) ((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) - BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)).toNat) = .ok tl8_3_1_1 ∧
      ∃ op21_3_1_1 ol21_3_1_1, derAlgOf M0 ((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) (tl8_3_1_1.header + tl8_3_1_1.len) = .ok ((op21_3_1_1, ol21_3_1_1), none) ∧
      (memBytes M0 op21_3_1_1 ol21_3_1_1 = memBytes M0 (BitVec.ofNat 32 (img% svOidEcdsaSha384Address)) 8) ∧
      ∃ tl3_4_1_1, derElement 0x30 (memBytes M0 ((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) ((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) - BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) - BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))).toNat) = .ok tl3_4_1_1 ∧
      ∃ tl11_4_1_1, derElement 0x30 (memBytes M0 (((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) (((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) - BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) - BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) - BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)).toNat) = .ok tl11_4_1_1 ∧
      ∃ tm20_4_1_1 rs20_4_1_1, readTime (memBytes M0 ((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 tl11_4_1_1.header) (tl11_4_1_1.len)) = some (tm20_4_1_1, rs20_4_1_1) ∧
      ∃ tm28_4_1_1 rs28_4_1_1, readTime rs20_4_1_1 = some (tm28_4_1_1, rs28_4_1_1) ∧
      (rs28_4_1_1 = []) ∧
      ∃ tl2_5_1_1, derElement 0x30 (memBytes M0 (((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) (((((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) - BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) - BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) - BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) - BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))).toNat) = .ok tl2_5_1_1 ∧
      ∃ tl6_5_1_1, derElement 0x30 (memBytes M0 ((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) ((((((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) - BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) - BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) - BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) - BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) - BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)).toNat) = .ok tl6_5_1_1 ∧
      ∃ op15_5_1_1 ol15_5_1_1 prp15_5_1_1 pu15_5_1_1, derAlgOf M0 (((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) (tl6_5_1_1.len) = .ok ((op15_5_1_1, ol15_5_1_1), some (prp15_5_1_1, pu15_5_1_1)) ∧
      ∃ ta15_5_1_1, derElement 0x30 (memBytes M0 (((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) (tl6_5_1_1.len)) = .ok ta15_5_1_1 ∧
      (BitVec.ofNat 8 pu15_5_1_1.tag = BitVec.ofNat 8 6) ∧
      (memBytes M0 (prp15_5_1_1 + BitVec.ofNat 32 pu15_5_1_1.header) pu15_5_1_1.len = memBytes M0 (BitVec.ofNat 32 (img% svOidPrime256v1Address)) 8) ∧
      (memBytes M0 op15_5_1_1 ol15_5_1_1 = memBytes M0 (BitVec.ofNat 32 (img% svOidEcPublicKeyAddress)) 7) ∧
      ∃ tl35_5_1_1, derElement 3 (memBytes M0 ((((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) + BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)) ((BitVec.ofNat 32 (tl6_5_1_1.len)) - BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)).toNat) = .ok tl35_5_1_1 ∧
      ∃ bp35_5_1_1 bl35_5_1_1, derBitsOf (memBytes M0 ((((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) + BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)) ((BitVec.ofNat 32 (tl6_5_1_1.len)) - BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)).toNat) ((((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) + BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)) (.ok tl35_5_1_1) = .ok (bp35_5_1_1, bl35_5_1_1) ∧
      (bl35_5_1_1 = BitVec.ofNat 32 0x41) ∧
      (((BitVec.ofNat 32 (tl6_5_1_1.len)) - BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)) - BitVec.ofNat 32 (tl35_5_1_1.header + tl35_5_1_1.len) = 0) ∧
      (M0 bp35_5_1_1 = BitVec.ofNat 8 4) ∧
      (GsOk M0 bp35_5_1_1) ∧
      ∃ tl9_6_1_1, derOptRes 0xA3 (memBytes M0 ((((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) ((((((((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) - BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) - BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) - BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) - BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) - BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) - BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))).toNat) = some (.ok tl9_6_1_1) ∧
      (((((((((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) - BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) - BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) - BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) - BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) - BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) - BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) - BitVec.ofNat 32 (tl9_6_1_1.header + tl9_6_1_1.len) = 0) ∧
      ∃ tl24_6_1_1, derElement 0x30 (memBytes M0 (((((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) + BitVec.ofNat 32 tl9_6_1_1.header) (BitVec.ofNat 32 tl9_6_1_1.len).toNat) = .ok tl24_6_1_1 ∧
      ((BitVec.ofNat 32 tl9_6_1_1.len) - BitVec.ofNat 32 (tl24_6_1_1.header + tl24_6_1_1.len) = 0) ∧
      ∃ u0_1 u1_1 u2_1, ∃ k_2_1 f2c'_2_1 f30'_2_1 rem'_2_1 sl0'_2_1 sl1'_2_1 sl2'_2_1 sl3'_2_1 sl4'_2_1 sl5'_2_1 sl6'_2_1 sl7'_2_1 sl8'_2_1 sl9'_2_1 cur'_2_1, svChain (sv_extStep B out bp (lp + BitVec.ofNat 32 t_1_1_1.header) dg rootp ll bp16_2_1_1 bp35_5_1_1 bl16_2_1_1 (BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) ((((((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) + BitVec.ofNat 32 tl9_6_1_1.header) + BitVec.ofNat 32 tl24_6_1_1.header) (BitVec.ofNat 32 tl24_6_1_1.len) (BitVec.ofNat 32 (tm28_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm28_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm20_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm20_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) (((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len)) lp (BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len)) ((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) (BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) (((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) v M0) k_2_1 ((BitVec.ofNat 32 0x0), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 tl24_6_1_1.len), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 tl24_6_1_1.len), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 (tl24_6_1_1.header + tl24_6_1_1.len)), (BitVec.ofNat 32 0x0), (u0_1), (BitVec.ofNat 32 0x0), (u1_1), (BitVec.ofNat 32 0x0), (u2_1), ((((((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) + BitVec.ofNat 32 tl9_6_1_1.header) + BitVec.ofNat 32 tl24_6_1_1.header)) (f2c'_2_1, f30'_2_1, rem'_2_1, sl0'_2_1, sl1'_2_1, sl2'_2_1, sl3'_2_1, sl4'_2_1, sl5'_2_1, sl6'_2_1, sl7'_2_1, sl8'_2_1, sl9'_2_1, cur'_2_1) ∧
      rem'_2_1 = 0 ∧ (sl0'_2_1 = 0 ∨ SvIn B sl0'_2_1 sl1'_2_1.toNat) ∧ (sl2'_2_1 = 0 ∨ SvIn B sl2'_2_1 sl3'_2_1.toNat) ∧ (sl4'_2_1 = 0 ∨ SvIn B sl4'_2_1 sl5'_2_1.toNat) ∧ (sl6'_2_1 = 0 ∨ SvIn B sl6'_2_1 sl7'_2_1.toNat) ∧ (sl8'_2_1 = 0 ∨ SvIn B sl8'_2_1 sl9'_2_1.toNat) ∧
      (sl0'_2_1 ≠ 0) ∧ (sl2'_2_1 ≠ 0) ∧ (sl4'_2_1 ≠ 0) ∧ (sl6'_2_1 ≠ 0) ∧ ((if BitVec.ult 0 (sl8'_2_1) then (1 : Word) else 0) &&& ((f2c'_2_1) &&& (f30'_2_1)) ≠ 0) ∧ (memBytes M0 (((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) ((BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)).toNat) = memBytes M0 ((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) ((BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len)).toNat)) ∧ ∃ sr40_2_1 ss40_2_1, ecdsaSigOf 48 M0 (bp16_2_1_1) ((bl16_2_1_1.toNat)) = .ok (sr40_2_1, ss40_2_1) ∧
      ∃ k_4_1, k_4_1 < 8 ∧
      (∀ i, i < k_4_1 → ∀ c'_4_1 q'_4_1, (c'_4_1, q'_4_1) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((rootp) + BitVec.ofNat 32 0x2C)) → ¬ (memBytes M0 (memLoad32 M0 (q'_4_1 + 0xFFFFFFFC)) (memLoad32 M0 (q'_4_1 + 0x0)).toNat = memBytes M0 (((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len)) (BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)).toNat)) ∧
      ∃ c'_4_1 q'_4_1, (c'_4_1, q'_4_1) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) k_4_1 ((BitVec.ofNat 32 0x100), ((rootp) + BitVec.ofNat 32 0x2C)) ∧ (memBytes M0 (memLoad32 M0 (q'_4_1 + 0xFFFFFFFC)) (memLoad32 M0 (q'_4_1 + 0x0)).toNat = memBytes M0 (((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len)) (BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)).toNat) ∧
      ((memLoad32 M0 (q'_4_1 + 0xFFFFFFFC)) ≠ 0) ∧
      ∃ pv_5_1, SvPvRes M0 (memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4)) (B + 0x21A0 + BitVec.ofNat 32 0x170) 48 (sha384 (memBytes M0 (lp + BitVec.ofNat 32 t_1_1_1.header) (BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)).toNat)) (B + 0x21A0 + BitVec.ofNat 32 0xC8) (B + 0x21A0 + BitVec.ofNat 32 0xF8) sr40_2_1 ss40_2_1 (some pv_5_1) ∧
      (pv_5_1 ≠ 0) ∧
      (memBytes M0 sl0'_2_1 sl1'_2_1.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x0)) (memLoad32 M0 (rootp + 0x4)).toNat) ∧
      (memBytes M0 sl2'_2_1 sl3'_2_1.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x8)) (memLoad32 M0 (rootp + 0xC)).toNat) ∧
      (memBytes M0 sl4'_2_1 sl5'_2_1.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x10)) (memLoad32 M0 (rootp + 0x14)).toNat) ∧
      (memBytes M0 sl6'_2_1 sl7'_2_1.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x18)) (memLoad32 M0 (rootp + 0x1C)).toNat) ∧
      (memBytes M0 sl8'_2_1 sl9'_2_1.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x20)) (memLoad32 M0 (rootp + 0x24)).toNat) ∧
      ∃ sr43_6_1 ss43_6_1, ecdsaSigOf 32 M0 ((memLoad32 M0 (bp + 0x8))) ((memLoad32 M0 (bp + 0xC)).toNat) = .ok (sr43_6_1, ss43_6_1) ∧
      SvP256Facts M0 bp35_5_1_1 dg (b32 sr43_6_1) (b32 ss43_6_1) ∧
      ∃ tl10_1_1_3, derElement 0x30 (memBytes M0 ((memLoad32 M0 (bp + 0x20))) ((memLoad32 M0 (bp + 0x24))).toNat) = .ok tl10_1_1_3 ∧
      (((memLoad32 M0 (bp + 0x24))) - BitVec.ofNat 32 (tl10_1_1_3.header + tl10_1_1_3.len) = 0) ∧
      ∃ tl21_1_1_3, derElement 0x30 (memBytes M0 (((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) (BitVec.ofNat 32 tl10_1_1_3.len).toNat) = .ok tl21_1_1_3 ∧
      derIntIsOf M0 (memBytes M0 ((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 tl21_1_1_3.header) (BitVec.ofNat 32 tl21_1_1_3.len).toNat) ((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 tl21_1_1_3.header) (derElement 2 (memBytes M0 ((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 tl21_1_1_3.header) (BitVec.ofNat 32 tl21_1_1_3.len).toNat)) ((BitVec.ofNat 32 0x0).extractLsb' 0 8) = .ok true ∧
      ∃ te30_1_1_3, derElement 2 (memBytes M0 ((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 tl21_1_1_3.header) (BitVec.ofNat 32 tl21_1_1_3.len).toNat) = .ok te30_1_1_3 ∧
      ((BitVec.ofNat 32 tl21_1_1_3.len) - BitVec.ofNat 32 (te30_1_1_3.header + te30_1_1_3.len) = 0) ∧
      ∃ tl2_2_1_3, derElement 0x30 (memBytes M0 (((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) (((BitVec.ofNat 32 tl10_1_1_3.len) - BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))).toNat) = .ok tl2_2_1_3 ∧
      ((((BitVec.ofNat 32 tl10_1_1_3.len) - BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) - BitVec.ofNat 32 (tl2_2_1_3.header + tl2_2_1_3.len) = 0) ∧
      ∃ op13_2_1_3 ol13_2_1_3, derContent ((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) (derOid (memBytes M0 ((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) (BitVec.ofNat 32 tl2_2_1_3.len).toNat)) = .ok (op13_2_1_3, ol13_2_1_3) ∧
      ∃ to13_2_1_3, derOid (memBytes M0 ((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) (BitVec.ofNat 32 tl2_2_1_3.len).toNat) = .ok to13_2_1_3 ∧
      (memBytes M0 op13_2_1_3 ol13_2_1_3.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress)) 9) ∧
      ∃ tl21_2_1_3, derElement 0xA0 (memBytes M0 (((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) ((BitVec.ofNat 32 tl2_2_1_3.len) - BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)).toNat) = .ok tl21_2_1_3 ∧
      (((BitVec.ofNat 32 tl2_2_1_3.len) - BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) - BitVec.ofNat 32 (tl21_2_1_3.header + tl21_2_1_3.len) = 0) ∧
      ∃ tl32_2_1_3, derElement 0x30 (memBytes M0 ((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) (BitVec.ofNat 32 tl21_2_1_3.len).toNat) = .ok tl32_2_1_3 ∧
      ((BitVec.ofNat 32 tl21_2_1_3.len) - BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len) = 0) ∧
      derIntIsOf M0 (memBytes M0 (((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) (BitVec.ofNat 32 tl32_2_1_3.len).toNat) (((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) (derElement 2 (memBytes M0 (((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) (BitVec.ofNat 32 tl32_2_1_3.len).toNat)) ((BitVec.ofNat 32 0x3).extractLsb' 0 8) = .ok true ∧
      ∃ te43_2_1_3, derElement 2 (memBytes M0 (((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) (BitVec.ofNat 32 tl32_2_1_3.len).toNat) = .ok te43_2_1_3 ∧
      ∃ tl2_3_1_3, derElement 0x31 (memBytes M0 (((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) (((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))).toNat) = .ok tl2_3_1_3 ∧
      isSha256Of M0 ((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 tl2_3_1_3.header) (BitVec.ofNat 32 tl2_3_1_3.len).toNat = .ok true ∧
      ∃ te11_3_1_3, derElement 0x30 (memBytes M0 ((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 tl2_3_1_3.header) (BitVec.ofNat 32 tl2_3_1_3.len).toNat) = .ok te11_3_1_3 ∧
      ((BitVec.ofNat 32 tl2_3_1_3.len) - BitVec.ofNat 32 (te11_3_1_3.header + te11_3_1_3.len) = 0) ∧
      ∃ tl19_3_1_3, derElement 0x30 (memBytes M0 ((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) ((((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) - BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)).toNat) = .ok tl19_3_1_3 ∧
      ∃ op28_3_1_3 ol28_3_1_3, derContent (((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 tl19_3_1_3.header) (derOid (memBytes M0 (((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 tl19_3_1_3.header) (BitVec.ofNat 32 tl19_3_1_3.len).toNat)) = .ok (op28_3_1_3, ol28_3_1_3) ∧
      ∃ to28_3_1_3, derOid (memBytes M0 (((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 tl19_3_1_3.header) (BitVec.ofNat 32 tl19_3_1_3.len).toNat) = .ok to28_3_1_3 ∧
      (memBytes M0 op28_3_1_3 ol28_3_1_3.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x9)) 11) ∧
      ∃ tl2_4_1_3, derOptRes 0xA0 (memBytes M0 (((((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 tl19_3_1_3.header) + BitVec.ofNat 32 (to28_3_1_3.header + to28_3_1_3.len))) (((BitVec.ofNat 32 tl19_3_1_3.len) - BitVec.ofNat 32 (to28_3_1_3.header + to28_3_1_3.len))).toNat) = some (.ok tl2_4_1_3) ∧
      ((((BitVec.ofNat 32 tl19_3_1_3.len) - BitVec.ofNat 32 (to28_3_1_3.header + to28_3_1_3.len))) - BitVec.ofNat 32 (tl2_4_1_3.header + tl2_4_1_3.len) = 0) ∧
      ∃ vp23_4_1_3 vl23_4_1_3, derContent ((((((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 tl19_3_1_3.header) + BitVec.ofNat 32 (to28_3_1_3.header + to28_3_1_3.len))) + BitVec.ofNat 32 tl2_4_1_3.header) (derElement 4 (memBytes M0 ((((((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 tl19_3_1_3.header) + BitVec.ofNat 32 (to28_3_1_3.header + to28_3_1_3.len))) + BitVec.ofNat 32 tl2_4_1_3.header) (BitVec.ofNat 32 tl2_4_1_3.len).toNat)) = .ok (vp23_4_1_3, vl23_4_1_3) ∧
      ∃ te23_4_1_3, derElement 4 (memBytes M0 ((((((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 tl19_3_1_3.header) + BitVec.ofNat 32 (to28_3_1_3.header + to28_3_1_3.len))) + BitVec.ofNat 32 tl2_4_1_3.header) (BitVec.ofNat 32 tl2_4_1_3.len).toNat) = .ok te23_4_1_3 ∧
      ((BitVec.ofNat 32 tl2_4_1_3.len) - BitVec.ofNat 32 (te23_4_1_3.header + te23_4_1_3.len) = 0) ∧
      ∃ tr5_w328_5_1_3 : Word, ∃ tr5_w32c_5_1_3 : Word, (((derOptRes 0xA0 (memBytes M0 ((((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))) ((((((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) - BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) - BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))).toNat) = none) ∧ ((((((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) - BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) - BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len)) = 0 ∨ (M0 ((((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len)))).toNat ≠ 0xA1) ∧ tr5_w328_5_1_3 = (((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len)) ∧ tr5_w32c_5_1_3 = (((((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) - BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) - BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))) ∨ ((¬ (derOptRes 0xA0 (memBytes M0 ((((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))) ((((((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) - BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) - BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))).toNat) = none)) ∧ ∃ tl2, derOptRes 0xA0 (memBytes M0 ((((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))) ((((((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) - BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) - BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))).toNat) = some (.ok tl2) ∧ (((((((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) - BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) - BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0 ∨ (M0 (((((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))) + BitVec.ofNat 32 (tl2.header + tl2.len))).toNat ≠ 0xA1) ∧ tr5_w328_5_1_3 = ((((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tr5_w32c_5_1_3 = ((((((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) - BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) - BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tr5_w328_5_1_3 tr5_w32c_5_1_3.toNat ∧
      ∃ tl2_6_1_3, derElement 0x31 (memBytes M0 (tr5_w328_5_1_3) (tr5_w32c_5_1_3).toNat) = .ok tl2_6_1_3 ∧
      ((tr5_w32c_5_1_3) - BitVec.ofNat 32 (tl2_6_1_3.header + tl2_6_1_3.len) = 0) ∧
      ∃ tl13_6_1_3, derElement 0x30 (memBytes M0 ((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) (BitVec.ofNat 32 tl2_6_1_3.len).toNat) = .ok tl13_6_1_3 ∧
      ((BitVec.ofNat 32 tl2_6_1_3.len) - BitVec.ofNat 32 (tl13_6_1_3.header + tl13_6_1_3.len) = 0) ∧
      derIntIsOf M0 (memBytes M0 (((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) (BitVec.ofNat 32 tl13_6_1_3.len).toNat) (((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) (derElement 2 (memBytes M0 (((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) (BitVec.ofNat 32 tl13_6_1_3.len).toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = .ok true ∧
      ∃ te25_6_1_3, derElement 2 (memBytes M0 (((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) (BitVec.ofNat 32 tl13_6_1_3.len).toNat) = .ok te25_6_1_3 ∧
      ∃ tl31_6_1_3, derElement 0x30 (memBytes M0 ((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) ((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)).toNat) = .ok tl31_6_1_3 ∧
      isSha256Of M0 (((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) (((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) - BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)).toNat = .ok true ∧
      ∃ te39_6_1_3, derElement 0x30 (memBytes M0 (((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) (((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) - BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)).toNat) = .ok te39_6_1_3 ∧
      ∃ tl45_6_1_3, derOptRes 0xA0 (memBytes M0 ((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) ((((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) - BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) - BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)).toNat) = some (.ok tl45_6_1_3) ∧
      ((BitVec.ofNat 32 tl45_6_1_3.len) ≠ 0) ∧
      (((BitVec.ofNat 32 tl45_6_1_3.len)).toNat ≤ ((BitVec.ofNat 32 tl45_6_1_3.len)).toNat) ∧
      ∃ tl6_1_2_3, derElement 0x30 (memBytes M0 ((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) ((BitVec.ofNat 32 tl45_6_1_3.len)).toNat) = .ok tl6_1_2_3 ∧
      ∃ op15_1_2_3 ol15_1_2_3, derContent (((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) (derOid (memBytes M0 (((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) (BitVec.ofNat 32 tl6_1_2_3.len).toNat)) = .ok (op15_1_2_3, ol15_1_2_3) ∧
      ∃ to15_1_2_3, derOid (memBytes M0 (((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) (BitVec.ofNat 32 tl6_1_2_3.len).toNat) = .ok to15_1_2_3 ∧
      ∃ tl20_1_2_3, derElement 0x31 (memBytes M0 ((((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) ((BitVec.ofNat 32 tl6_1_2_3.len) - BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)).toNat) = .ok tl20_1_2_3 ∧
      (((BitVec.ofNat 32 tl6_1_2_3.len) - BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) - BitVec.ofNat 32 (tl20_1_2_3.header + tl20_1_2_3.len) = 0) ∧
      listsOidOf M0 (((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header) (((BitVec.ofNat 32 tl45_6_1_3.len)) - ((BitVec.ofNat 32 tl45_6_1_3.len))).toNat (memBytes M0 op15_1_2_3 ol15_1_2_3.toNat) = .ok false ∧
      ∃ trv_w64_2_2_3 : Word, ∃ trv_w7c_2_2_3 : Word, (((memBytes M0 op15_1_2_3 ol15_1_2_3.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9) ∧ ∃ op5 ol5, derContent ((((((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) (derOid (memBytes M0 ((((((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat)) = .ok (op5, ol5) ∧ ∃ to5, derOid (memBytes M0 ((((((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat) = .ok to5 ∧ (memBytes M0 op5 ol5.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x9)) 11) ∧ (((BitVec.ofNat 32 tl20_1_2_3.len)) - BitVec.ofNat 32 (to5.header + to5.len) = 0) ∧ trv_w64_2_2_3 = (BitVec.ofNat 32 0x0) ∧ trv_w7c_2_2_3 = BitVec.ofNat 32 0x1) ∨ ((¬ (memBytes M0 op15_1_2_3 ol15_1_2_3.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9)) ∧ (memBytes M0 op15_1_2_3 ol15_1_2_3.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x1E)) 9) ∧ ∃ vp8 vl8, derContent ((((((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) (derElement 4 (memBytes M0 ((((((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat)) = .ok (vp8, vl8) ∧ ∃ te8, derElement 4 (memBytes M0 ((((((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat) = .ok te8 ∧ (vl8 = 32) ∧ (((BitVec.ofNat 32 tl20_1_2_3.len)) - BitVec.ofNat 32 (te8.header + te8.len) = 0) ∧ trv_w64_2_2_3 = vp8 ∧ trv_w7c_2_2_3 = (BitVec.ofNat 32 0x0)) ∨ ((¬ (memBytes M0 op15_1_2_3 ol15_1_2_3.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9)) ∧ (¬ (memBytes M0 op15_1_2_3 ol15_1_2_3.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x1E)) 9)) ∧ trv_w64_2_2_3 = (BitVec.ofNat 32 0x0) ∧ trv_w7c_2_2_3 = (BitVec.ofNat 32 0x0))) ∧ (trv_w64_2_2_3 = 0 ∨ SvIn B trv_w64_2_2_3 32) ∧
      ∃ k_3_3 dg'_3_3 flag'_3_3 cp'_3_3 rem'_3_3, svChain (sv_attrStep B out bp dg rootp ll ((q'_4_1) + BitVec.ofNat 32 0x20) (((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header) (BitVec.ofNat 32 tl45_6_1_3.len) (((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len)) (((((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) - BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) - BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) - BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len)) v M0) k_3_3 (trv_w64_2_2_3, trv_w7c_2_2_3, (((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 (tl6_1_2_3.header + tl6_1_2_3.len)), (((BitVec.ofNat 32 tl45_6_1_3.len)) - BitVec.ofNat 32 (tl6_1_2_3.header + tl6_1_2_3.len))) (dg'_3_3, flag'_3_3, cp'_3_3, rem'_3_3) ∧
      rem'_3_3 = 0 ∧ (dg'_3_3 = 0 ∨ SvIn B dg'_3_3 32) ∧
      (dg'_3_3 ≠ 0 ∧ flag'_3_3 = 1) ∧ ∃ op9_3_3 ol9_3_3, derAlgOf M0 ((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))) (((((((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) - BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) - BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) - BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))).toNat) = .ok ((op9_3_3, ol9_3_3), none) ∧ ∃ te9_3_3, derElement 0x30 (memBytes M0 ((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))) ((((((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) - BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) - BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) - BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))).toNat) = .ok te9_3_3 ∧ (memBytes M0 op9_3_3 ol9_3_3 = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress)) 8) ∧ ∃ vp20_3_3 vl20_3_3, derContent (((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))) + BitVec.ofNat 32 (te9_3_3.header + te9_3_3.len)) (derElement 4 (memBytes M0 (((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))) + BitVec.ofNat 32 (te9_3_3.header + te9_3_3.len)) (((((((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) - BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) - BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) - BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))) - BitVec.ofNat 32 (te9_3_3.header + te9_3_3.len)).toNat)) = .ok (vp20_3_3, vl20_3_3) ∧ ∃ te20_3_3, derElement 4 (memBytes M0 (((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))) + BitVec.ofNat 32 (te9_3_3.header + te9_3_3.len)) (((((((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) - BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) - BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) - BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))) - BitVec.ofNat 32 (te9_3_3.header + te9_3_3.len)).toNat) = .ok te20_3_3 ∧ ∃ sr25_3_3 ss25_3_3, ecdsaSigOf 48 M0 (vp20_3_3) ((vl20_3_3).toNat) = .ok (sr25_3_3, ss25_3_3) ∧ ((((((((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) - BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) - BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) - BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))) - BitVec.ofNat 32 (te9_3_3.header + te9_3_3.len)) - BitVec.ofNat 32 (te20_3_3.header + te20_3_3.len) = 0) ∧
      ∃ tl9_1_4_3, derElement 0x30 (memBytes M0 (vp23_4_1_3) (vl23_4_1_3).toNat) = .ok tl9_1_4_3 ∧
      ((vl23_4_1_3) - BitVec.ofNat 32 (tl9_1_4_3.header + tl9_1_4_3.len) = 0) ∧
      derIntIsOf M0 (memBytes M0 ((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) (BitVec.ofNat 32 tl9_1_4_3.len).toNat) ((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) (derElement 2 (memBytes M0 ((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) (BitVec.ofNat 32 tl9_1_4_3.len).toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = .ok true ∧
      ∃ te20_1_4_3, derElement 2 (memBytes M0 ((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) (BitVec.ofNat 32 tl9_1_4_3.len).toNat) = .ok te20_1_4_3 ∧
      ∃ op26_1_4_3 ol26_1_4_3, derContent (((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) (derOid (memBytes M0 (((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) ((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)).toNat)) = .ok (op26_1_4_3, ol26_1_4_3) ∧
      ∃ to26_1_4_3, derOid (memBytes M0 (((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) ((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)).toNat) = .ok to26_1_4_3 ∧
      ∃ tl30_1_4_3, derElement 0x30 (memBytes M0 ((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) (((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) - BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)).toNat) = .ok tl30_1_4_3 ∧
      isSha256Of M0 (((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 tl30_1_4_3.header) (BitVec.ofNat 32 tl30_1_4_3.len).toNat = .ok true ∧
      ∃ te39_1_4_3, derElement 0x30 (memBytes M0 (((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 tl30_1_4_3.header) (BitVec.ofNat 32 tl30_1_4_3.len).toNat) = .ok te39_1_4_3 ∧
      ∃ vp45_1_4_3 vl45_1_4_3, derContent ((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 tl30_1_4_3.header) + BitVec.ofNat 32 (te39_1_4_3.header + te39_1_4_3.len)) (derElement 4 (memBytes M0 ((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 tl30_1_4_3.header) + BitVec.ofNat 32 (te39_1_4_3.header + te39_1_4_3.len)) ((BitVec.ofNat 32 tl30_1_4_3.len) - BitVec.ofNat 32 (te39_1_4_3.header + te39_1_4_3.len)).toNat)) = .ok (vp45_1_4_3, vl45_1_4_3) ∧
      ∃ te45_1_4_3, derElement 4 (memBytes M0 ((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 tl30_1_4_3.header) + BitVec.ofNat 32 (te39_1_4_3.header + te39_1_4_3.len)) ((BitVec.ofNat 32 tl30_1_4_3.len) - BitVec.ofNat 32 (te39_1_4_3.header + te39_1_4_3.len)).toNat) = .ok te45_1_4_3 ∧
      (vl45_1_4_3 = 32) ∧
      (((BitVec.ofNat 32 tl30_1_4_3.len) - BitVec.ofNat 32 (te39_1_4_3.header + te39_1_4_3.len)) - BitVec.ofNat 32 (te45_1_4_3.header + te45_1_4_3.len) = 0) ∧
      ∃ tl2_2_4_3, derElement 2 (memBytes M0 ((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) (((((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) - BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) - BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))).toNat) = .ok tl2_2_4_3 ∧
      ∃ ip2_2_4_3 il2_2_4_3, derPosIntOf (memBytes M0 ((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) (((((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) - BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) - BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))).toNat) ((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) (.ok tl2_2_4_3) = .ok (ip2_2_4_3, il2_2_4_3) ∧
      (((il2_2_4_3) - (aluEval .sltu ((M0 (ip2_2_4_3)).zeroExtend 32) 1)).toNat ≤ 20) ∧
      ∃ tl13_2_4_3, derElement 0x18 (memBytes M0 (((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) ((((((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) - BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) - BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)).toNat) = .ok tl13_2_4_3 ∧
      ∃ tm18_2_4_3, generalizedTime (memBytes M0 ((((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 tl13_2_4_3.header) ((BitVec.ofNat 32 tl13_2_4_3.len).toNat)) = some tm18_2_4_3 ∧
      ∃ tt3_w264_3_4_3 : Word, ∃ tt3_w268_3_4_3 : Word, (((derOptRes 0x30 (memBytes M0 (((((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) ((((((((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) - BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) - BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))).toNat) = none) ∧ tt3_w264_3_4_3 = ((((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len)) ∧ tt3_w268_3_4_3 = (((((((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) - BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) - BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) ∨ ((¬ (derOptRes 0x30 (memBytes M0 (((((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) ((((((((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) - BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) - BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))).toNat) = none)) ∧ ∃ tl2, derOptRes 0x30 (memBytes M0 (((((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) ((((((((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) - BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) - BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))).toNat) = some (.ok tl2) ∧ tt3_w264_3_4_3 = (((((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tt3_w268_3_4_3 = ((((((((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) - BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) - BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tt3_w264_3_4_3 tt3_w268_3_4_3.toNat ∧
      ∃ tt4_w264_4_4_3 : Word, ∃ tt4_w268_4_4_3 : Word, (((tt3_w268_3_4_3 = 0) ∧ tt4_w264_4_4_3 = tt3_w264_3_4_3 ∧ tt4_w268_4_4_3 = tt3_w268_3_4_3) ∨ ((¬ (tt3_w268_3_4_3 = 0)) ∧ (M0 tt3_w264_3_4_3 = BitVec.ofNat 8 1) ∧ derBoolOf (memBytes M0 (tt3_w264_3_4_3) (tt3_w268_3_4_3).toNat) (derElement 1 (memBytes M0 (tt3_w264_3_4_3) (tt3_w268_3_4_3).toNat)) = .ok () ∧ ∃ tb8_1, derElement 1 (memBytes M0 (tt3_w264_3_4_3) (tt3_w268_3_4_3).toNat) = .ok tb8_1 ∧ ∃ tt4b_w264_2 : Word, ∃ tt4b_w268_2 : Word, (((((tt3_w268_3_4_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = 0) ∧ tt4b_w264_2 = ((tt3_w264_3_4_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) ∧ tt4b_w268_2 = ((tt3_w268_3_4_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) ∨ ((¬ (((tt3_w268_3_4_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = 0)) ∧ ∃ tt4n_w264_2 : Word, ∃ tt4n_w268_2 : Word, (((M0 ((tt3_w264_3_4_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = BitVec.ofNat 8 2) ∧ ∃ ip4 il4, derIntOf (memBytes M0 (((tt3_w264_3_4_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (((tt3_w268_3_4_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))).toNat) (((tt3_w264_3_4_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (derElement 2 (memBytes M0 (((tt3_w264_3_4_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (((tt3_w268_3_4_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))).toNat)) = .ok (ip4, il4) ∧ ∃ ti4, derElement 2 (memBytes M0 (((tt3_w264_3_4_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (((tt3_w268_3_4_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))).toNat) = .ok ti4 ∧ tt4n_w264_2 = (((tt3_w264_3_4_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) + BitVec.ofNat 32 (ti4.header + ti4.len) ∧ tt4n_w268_2 = (((tt3_w268_3_4_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) - BitVec.ofNat 32 (ti4.header + ti4.len)) ∨ ((¬ (M0 ((tt3_w264_3_4_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = BitVec.ofNat 8 2)) ∧ tt4n_w264_2 = ((tt3_w264_3_4_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) ∧ tt4n_w268_2 = ((tt3_w268_3_4_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len)))) ∧ SvIn B tt4n_w264_2 tt4n_w268_2.toNat ∧ tt4b_w264_2 = tt4n_w264_2 ∧ tt4b_w268_2 = tt4n_w268_2)) ∧ SvIn B tt4b_w264_2 tt4b_w268_2.toNat ∧ tt4_w264_4_4_3 = tt4b_w264_2 ∧ tt4_w268_4_4_3 = tt4b_w268_2) ∨ ((¬ (tt3_w268_3_4_3 = 0)) ∧ (¬ (M0 tt3_w264_3_4_3 = BitVec.ofNat 8 1)) ∧ ∃ tt4n_w264_2 : Word, ∃ tt4n_w268_2 : Word, (((M0 tt3_w264_3_4_3 = BitVec.ofNat 8 2) ∧ ∃ ip4 il4, derIntOf (memBytes M0 (tt3_w264_3_4_3) (tt3_w268_3_4_3).toNat) (tt3_w264_3_4_3) (derElement 2 (memBytes M0 (tt3_w264_3_4_3) (tt3_w268_3_4_3).toNat)) = .ok (ip4, il4) ∧ ∃ ti4, derElement 2 (memBytes M0 (tt3_w264_3_4_3) (tt3_w268_3_4_3).toNat) = .ok ti4 ∧ tt4n_w264_2 = (tt3_w264_3_4_3) + BitVec.ofNat 32 (ti4.header + ti4.len) ∧ tt4n_w268_2 = (tt3_w268_3_4_3) - BitVec.ofNat 32 (ti4.header + ti4.len)) ∨ ((¬ (M0 tt3_w264_3_4_3 = BitVec.ofNat 8 2)) ∧ tt4n_w264_2 = tt3_w264_3_4_3 ∧ tt4n_w268_2 = tt3_w268_3_4_3)) ∧ SvIn B tt4n_w264_2 tt4n_w268_2.toNat ∧ tt4_w264_4_4_3 = tt4n_w264_2 ∧ tt4_w268_4_4_3 = tt4n_w268_2)) ∧ SvIn B tt4_w264_4_4_3 tt4_w268_4_4_3.toNat ∧
      ∃ tt5_w264_5_4_3 : Word, ∃ tt5_w268_5_4_3 : Word, (((derOptRes 0xA0 (memBytes M0 (tt4_w264_4_4_3) (tt4_w268_4_4_3).toNat) = none) ∧ tt5_w264_5_4_3 = tt4_w264_4_4_3 ∧ tt5_w268_5_4_3 = tt4_w268_4_4_3) ∨ ((¬ (derOptRes 0xA0 (memBytes M0 (tt4_w264_4_4_3) (tt4_w268_4_4_3).toNat) = none)) ∧ ∃ tl2, derOptRes 0xA0 (memBytes M0 (tt4_w264_4_4_3) (tt4_w268_4_4_3).toNat) = some (.ok tl2) ∧ tt5_w264_5_4_3 = (tt4_w264_4_4_3) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tt5_w268_5_4_3 = (tt4_w268_4_4_3) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tt5_w264_5_4_3 tt5_w268_5_4_3.toNat ∧
      ∃ tt6_w264_6_4_3 : Word, ∃ tt6_w268_6_4_3 : Word, (((derOptRes 0xA1 (memBytes M0 (tt5_w264_5_4_3) (tt5_w268_5_4_3).toNat) = none) ∧ (tt5_w268_5_4_3 = 0) ∧ tt6_w264_6_4_3 = tt5_w264_5_4_3 ∧ tt6_w268_6_4_3 = tt5_w268_5_4_3) ∨ ((¬ (derOptRes 0xA1 (memBytes M0 (tt5_w264_5_4_3) (tt5_w268_5_4_3).toNat) = none)) ∧ ∃ tl2, derOptRes 0xA1 (memBytes M0 (tt5_w264_5_4_3) (tt5_w268_5_4_3).toNat) = some (.ok tl2) ∧ ((tt5_w268_5_4_3) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0) ∧ tt6_w264_6_4_3 = (tt5_w264_5_4_3) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tt6_w268_6_4_3 = (tt5_w268_5_4_3) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tt6_w264_6_4_3 tt6_w268_6_4_3.toNat ∧
      ∃ k_6_3, k_6_3 < 8 ∧
      (∀ i, i < k_6_3 → ∀ c'_6_3 q'_6_3, (c'_6_3, q'_6_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((rootp) + BitVec.ofNat 32 0x308)) → ¬ (memBytes M0 (memLoad32 M0 (q'_6_3 + 0x20)) (memLoad32 M0 (q'_6_3 + 0x24)).toNat = memBytes M0 ((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) (BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)).toNat)) ∧
      ∃ c'_6_3 q'_6_3, (c'_6_3, q'_6_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) k_6_3 ((BitVec.ofNat 32 0x100), ((rootp) + BitVec.ofNat 32 0x308)) ∧ (memBytes M0 (memLoad32 M0 (q'_6_3 + 0x20)) (memLoad32 M0 (q'_6_3 + 0x24)).toNat = memBytes M0 ((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) (BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)).toNat) ∧
      ((memLoad32 M0 (q'_6_3 + 0x20)) ≠ 0) ∧
      (sha256 (memBytes M0 (vp23_4_1_3) (vl23_4_1_3).toNat) = memBytes M0 dg'_3_3 32) ∧
      (sha256 (memBytes M0 ((memLoad32 M0 (bp + 0x8))) ((memLoad32 M0 (bp + 0xC))).toNat) = memBytes M0 vp45_1_4_3 32) ∧
      ((BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len)) ≠ 0) ∧
      ∃ pv_8_3, SvPvRes M0 (memLoad32 M0 (((q'_6_3) + BitVec.ofNat 32 0x20) + 0x18)) (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 (sha256 (memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x14)) (1) ++ memBytes M0 ((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len))) + BitVec.ofNat 32 0x1) ((((BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))) + BitVec.ofNat 32 0xFFFFFFFF).toNat))) (B + 0x21A0 + BitVec.ofNat 32 0x190) (B + 0x21A0 + BitVec.ofNat 32 0x1C0) sr25_3_3 ss25_3_3 (some pv_8_3) ∧
      (pv_8_3 ≠ 0) ∧
      ∃ ix8_1_1_4, nlScan M0 ((memLoad32 M0 (bp + 0x18))) 0 (((memLoad32 M0 (bp + 0x1C))).toNat) = some ix8_1_1_4 ∧
      ∃ ix18_1_1_4, nlScan M0 (((memLoad32 M0 (bp + 0x18))) + BitVec.ofNat 32 (ix8_1_1_4 + 1)) 0 ((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix8_1_1_4 + 1)) = some ix18_1_1_4 ∧
      ∃ ix26_1_1_4, nlScan M0 ((((memLoad32 M0 (bp + 0x18))) + BitVec.ofNat 32 (ix8_1_1_4 + 1)) + BitVec.ofNat 32 (ix18_1_1_4 + 1)) 0 (((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) = some ix26_1_1_4 ∧
      ∃ ix34_1_1_4, nlScan M0 (((((memLoad32 M0 (bp + 0x18))) + BitVec.ofNat 32 (ix8_1_1_4 + 1)) + BitVec.ofNat 32 (ix18_1_1_4 + 1)) + BitVec.ofNat 32 (ix26_1_1_4 + 1)) 0 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1)) = some ix34_1_1_4 ∧
      (BitVec.ofNat 32 ix34_1_1_4 = 0) ∧
      (BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1)) - BitVec.ofNat 32 (ix34_1_1_4 + 1) ≠ 0) ∧
      (((1 < (BitVec.ofNat 32 ix18_1_1_4).toNat) ∧ ((BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1)) - BitVec.ofNat 32 (ix34_1_1_4 + 1)).toNat < (memLoad32 M0 (bp + 0x1C)).toNat) ∧ (¬ ((memLoad32 M0 (bp + 0x1C))).toNat < ((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1)) - BitVec.ofNat 32 (ix34_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 M0 (bp + 0x1C)))).toNat) ∧ (¬ (((BitVec.ofNat 32 ix18_1_1_4)) + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat) ∧ (M0 (((memLoad32 M0 (bp + 0x18))) + BitVec.ofNat 32 (ix8_1_1_4 + 1)) ≠ 0x30)) ∨ ((¬ (1 < (BitVec.ofNat 32 ix18_1_1_4).toNat)) ∧ ((BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1)) - BitVec.ofNat 32 (ix34_1_1_4 + 1)).toNat < (memLoad32 M0 (bp + 0x1C)).toNat) ∧ (¬ ((memLoad32 M0 (bp + 0x1C))).toNat < ((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1)) - BitVec.ofNat 32 (ix34_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 M0 (bp + 0x1C)))).toNat) ∧ (¬ (((BitVec.ofNat 32 ix18_1_1_4)) + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat))) ∧
      ∃ c'_2_4 p'_2_4 w64'_2_4 w74'_2_4, (c'_2_4, p'_2_4, w64'_2_4, w74'_2_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, ((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))))) (BitVec.ofNat 32 ix18_1_1_4).toNat ((BitVec.ofNat 32 ix18_1_1_4), (((memLoad32 M0 (bp + 0x18))) + BitVec.ofNat 32 (ix8_1_1_4 + 1)), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 0x0)) ∧ (∀ i, i < (BitVec.ofNat 32 ix18_1_1_4).toNat → ∀ c'_2_4 p'_2_4 w64'_2_4 w74'_2_4, (c'_2_4, p'_2_4, w64'_2_4, w74'_2_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, ((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))))) i ((BitVec.ofNat 32 ix18_1_1_4), (((memLoad32 M0 (bp + 0x18))) + BitVec.ofNat 32 (ix8_1_1_4 + 1)), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 0x0)) → ((((((M0 (p'_2_4)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF).toNat < (BitVec.ofNat 32 0xA).toNat)) ∧ (((aluEval .sltu ((aluEval .mul (w74'_2_4) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64'_2_4) (BitVec.ofNat 32 0xA))) (aluEval .mulhu (w64'_2_4) (BitVec.ofNat 32 0xA))) ||| (aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74'_2_4) (BitVec.ofNat 32 0xA))) = 0)) ∧ (((aluEval .sltu (((((M0 (p'_2_4)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64'_2_4) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64'_2_4) (BitVec.ofNat 32 0xA))) &&& (aluEval .sltu (((aluEval .mul (w74'_2_4) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64'_2_4) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p'_2_4)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64'_2_4) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64'_2_4) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74'_2_4) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64'_2_4) (BitVec.ofNat 32 0xA)))) = 0))) ∧
      (w74'_2_4.toNat < 2 ^ 31) ∧ ∃ bs7_2_4, base64Decode (memBytes M0 (((((memLoad32 M0 (bp + 0x18))) + BitVec.ofNat 32 (ix8_1_1_4 + 1)) + BitVec.ofNat 32 (ix18_1_1_4 + 1))) (((BitVec.ofNat 32 ix26_1_1_4)).toNat)) = some bs7_2_4 ∧ (bs7_2_4.length = 32) ∧
      ∃ k_3_4, k_3_4 < 16 ∧
      (∀ i, i < k_3_4 → ∀ c'_3_4 q'_3_4, (c'_3_4, q'_3_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), ((rootp) + BitVec.ofNat 32 0x108)) → ¬ (memBytes M0 (memLoad32 M0 (q'_3_4 + 0x20)) (memLoad32 M0 (q'_3_4 + 0x24)).toNat = memBytes M0 (memLoad32 M0 (bp + 0x18)) (BitVec.ofNat 32 ix8_1_1_4).toNat)) ∧
      ∃ c'_3_4 q'_3_4, (c'_3_4, q'_3_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) k_3_4 ((BitVec.ofNat 32 0x200), ((rootp) + BitVec.ofNat 32 0x108)) ∧ (memBytes M0 (memLoad32 M0 (q'_3_4 + 0x20)) (memLoad32 M0 (q'_3_4 + 0x24)).toNat = memBytes M0 (memLoad32 M0 (bp + 0x18)) (BitVec.ofNat 32 ix8_1_1_4).toNat) ∧
      ((memLoad32 M0 (q'_3_4 + 0x20)) ≠ 0) ∧
      ∃ sg_5_4, ∃ k_5_4 f'_5_4 w38'_5_4 w50'_5_4 sg'_5_4, svChain (sv_cosigStep B out bp dg ll ((q'_4_1) + BitVec.ofNat 32 0x20) (memLoad32 M0 (q'_3_4 + 0x24)) (le4 (sha256 (memBytes M0 ((memLoad32 M0 (bp + 0x18))) (((BitVec.ofNat 32 ix8_1_1_4)).toNat) ++ memBytes M0 (BitVec.ofNat 32 (img% svNewlineAddress)) (1) ++ memBytes M0 (BitVec.ofNat 32 (img% merklePrefixAddress)) (1) ++ memBytes M0 ((memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18))) (32))) 0) (memLoad32 M0 (bp + 0x18)) (BitVec.ofNat 32 ix8_1_1_4) (memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18)) (memLoad32 M0 (bp + 0x18)) ((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1)) - BitVec.ofNat 32 (ix34_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 M0 (bp + 0x1C)))) v M0) k_5_4 ((BitVec.ofNat 32 0x0), ((((((memLoad32 M0 (bp + 0x18))) + BitVec.ofNat 32 (ix8_1_1_4 + 1)) + BitVec.ofNat 32 (ix18_1_1_4 + 1)) + BitVec.ofNat 32 (ix26_1_1_4 + 1)) + BitVec.ofNat 32 (ix34_1_1_4 + 1)), (BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1)) - BitVec.ofNat 32 (ix34_1_1_4 + 1)), sg_5_4) (f'_5_4, w38'_5_4, w50'_5_4, sg'_5_4) ∧
      w50'_5_4 = 0 ∧
      ((f'_5_4) &&& BitVec.ofNat 32 0x1 ≠ 0) ∧ (evSpec (sigMem M0 (B + 0x21A0 + BitVec.ofNat 32 0x420) sg'_5_4) (memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18)) (B + 0x21A0 + BitVec.ofNat 32 0x420) (memLoad32 M0 (bp + 0x18)) (((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1)) - BitVec.ofNat 32 (ix34_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 M0 (bp + 0x1C))))).toNat = true) ∧
      ((((memLoad32 M0 (bp + 0x2C)) = w74'_2_4) ∧ (aluEval .sltu ((memLoad32 M0 (bp + 0x28))) (w64'_2_4) ≠ 0)) ∨ ((¬ ((memLoad32 M0 (bp + 0x2C)) = w74'_2_4)) ∧ (aluEval .sltu ((memLoad32 M0 (bp + 0x2C))) (w74'_2_4) ≠ 0))) ∧
      ∃ root6_3_6_4, rootFromInclusion (pair64 ((memLoad32 M0 (bp + 0x28))) ((memLoad32 M0 (bp + 0x2C)))) (pair64 (w64'_2_4) (w74'_2_4)) ((sha256 ([] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (dg) (32)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B) ++ base64Encode (memBytes M0 ((memLoad32 M0 (bp + 0x8))) (((memLoad32 M0 (bp + 0xC))).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid2Address)) (0x54) ++ base64Encode (memBytes M0 (lp) ((ll).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPostAddress)) (0x7)))) (memBytes M0 ((memLoad32 M0 (bp + 0x10))) (((memLoad32 M0 (bp + 0x14))).toNat)) = some root6_3_6_4 ∧
      (b32 root6_3_6_4 = b32 bs7_2_4) ∧
      ((((BitVec.ofNat 32 (tm20_4_1_1 / 2 ^ 32)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((BitVec.ofNat 32 (tm20_4_1_1 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm20_4_1_1 / 2 ^ 32)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((BitVec.ofNat 32 (tm20_4_1_1 / 2 ^ 32))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (BitVec.ofNat 32 (tm28_4_1_1 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm28_4_1_1 % 2 ^ 32))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (BitVec.ofNat 32 (tm28_4_1_1 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm28_4_1_1 / 2 ^ 32))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
      ((((memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE4))) = 0)) ∨ ((¬ ((memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0))) ∧ (aluEval .sltu ((memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFEC))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0)))) ∧ (aluEval .sltu ((memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
      ((((memLoad32 M0 (((q'_6_3) + BitVec.ofNat 32 0x20) + 0xC)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((memLoad32 M0 (((q'_6_3) + BitVec.ofNat 32 0x20) + 0x8))) = 0)) ∨ ((¬ ((memLoad32 M0 (((q'_6_3) + BitVec.ofNat 32 0x20) + 0xC)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((memLoad32 M0 (((q'_6_3) + BitVec.ofNat 32 0x20) + 0xC))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 M0 (((q'_6_3) + BitVec.ofNat 32 0x20) + 0x14))) ∧ (aluEval .sltu ((memLoad32 M0 (((q'_6_3) + BitVec.ofNat 32 0x20) + 0x10))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 M0 (((q'_6_3) + BitVec.ofNat 32 0x20) + 0x14)))) ∧ (aluEval .sltu ((memLoad32 M0 (((q'_6_3) + BitVec.ofNat 32 0x20) + 0x14))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
      ((((memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 3))) = 0)) ∨ ((¬ ((memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15))) ∧ (aluEval .sltu ((memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 11))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15)))) ∧ (aluEval .sltu ((memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
      SvOkRet B out v n0 (BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32)) (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) (memLoad32 M0 (bp + 0x28)) (memLoad32 M0 (bp + 0x2C))) := by
  rcases sv_seg_sv FW E0 V0 hret hO s0 M0 fM g0_2 g0_10 g0_11 g0_18 g0_19 g0_20 g0_21 g0_22 g0_26 w0_360 w0_364 w0_368 w0_36c lc_in D0 w0_94 w0_9c w0_a4 SD0 H' HE0 RS PE0 pkp_in apk pk_in side he0p_in he0l_in ae0p ae0l e0_in he1p_in he1l_in ae1p ae1l e1_in he2p_in he2l_in ae2p ae2l e2_in he3p_in he3l_in ae3p ae3l e3_in he4p_in he4l_in ae4p ae4l e4_in hsgp_in hsgl_in asgp asgl sg_in PE0' dg_in htsp_in htsl_in atsp atsl ts_in D0' H'' S2 pkp_in' apk' pk_in' side' CK0 ckp_in4 ckl_in4 a_ckp a_ckl ck_in H''' kp_in4 kw_in4 a_kp a_kw kp_in EE0 hiv pk_in'' lid_in lih_in lil_in a_lih a_lil RK0 dgi_in pp_in4 pl_in4 a_pp a_pl pp_in ii2h ai2h ii2l ai2l ii3h ai3h ii3l ai3l it4h at4h it4l at4l it5h at5h it5l at5l with e | e | hx
  · exact .inl e
  · exact .inr (.inl e)
  obtain ⟨t_1_1_1, hx⟩ := hx
  obtain ⟨h0, hx⟩ := hx
  obtain ⟨h1, hx⟩ := hx
  obtain ⟨tl1_2_1_1, hx⟩ := hx
  obtain ⟨h2, hx⟩ := hx
  obtain ⟨tl8_2_1_1, hx⟩ := hx
  obtain ⟨h3, hx⟩ := hx
  obtain ⟨tl16_2_1_1, hx⟩ := hx
  obtain ⟨h4, hx⟩ := hx
  obtain ⟨bp16_2_1_1, hx⟩ := hx
  obtain ⟨bl16_2_1_1, hx⟩ := hx
  obtain ⟨h5, hx⟩ := hx
  obtain ⟨h6, hx⟩ := hx
  obtain ⟨tl28_2_1_1, hx⟩ := hx
  obtain ⟨h7, hx⟩ := hx
  obtain ⟨h8, hx⟩ := hx
  obtain ⟨te41_2_1_1, hx⟩ := hx
  obtain ⟨h9, hx⟩ := hx
  obtain ⟨h10, hx⟩ := hx
  obtain ⟨tl1_3_1_1, hx⟩ := hx
  obtain ⟨h11, hx⟩ := hx
  obtain ⟨ip1_3_1_1, hx⟩ := hx
  obtain ⟨il1_3_1_1, hx⟩ := hx
  obtain ⟨h12, hx⟩ := hx
  obtain ⟨h13, hx⟩ := hx
  obtain ⟨tl8_3_1_1, hx⟩ := hx
  obtain ⟨h14, hx⟩ := hx
  obtain ⟨op21_3_1_1, hx⟩ := hx
  obtain ⟨ol21_3_1_1, hx⟩ := hx
  obtain ⟨h15, hx⟩ := hx
  obtain ⟨h16, hx⟩ := hx
  obtain ⟨tl3_4_1_1, hx⟩ := hx
  obtain ⟨h17, hx⟩ := hx
  obtain ⟨tl11_4_1_1, hx⟩ := hx
  obtain ⟨h18, hx⟩ := hx
  obtain ⟨tm20_4_1_1, hx⟩ := hx
  obtain ⟨rs20_4_1_1, hx⟩ := hx
  obtain ⟨h19, hx⟩ := hx
  obtain ⟨tm28_4_1_1, hx⟩ := hx
  obtain ⟨rs28_4_1_1, hx⟩ := hx
  obtain ⟨h20, hx⟩ := hx
  obtain ⟨h21, hx⟩ := hx
  obtain ⟨tl2_5_1_1, hx⟩ := hx
  obtain ⟨h22, hx⟩ := hx
  obtain ⟨tl6_5_1_1, hx⟩ := hx
  obtain ⟨h23, hx⟩ := hx
  obtain ⟨op15_5_1_1, hx⟩ := hx
  obtain ⟨ol15_5_1_1, hx⟩ := hx
  obtain ⟨prp15_5_1_1, hx⟩ := hx
  obtain ⟨pu15_5_1_1, hx⟩ := hx
  obtain ⟨h24, hx⟩ := hx
  obtain ⟨ta15_5_1_1, hx⟩ := hx
  obtain ⟨h25, hx⟩ := hx
  obtain ⟨h26, hx⟩ := hx
  obtain ⟨h27, hx⟩ := hx
  obtain ⟨h28, hx⟩ := hx
  obtain ⟨tl35_5_1_1, hx⟩ := hx
  obtain ⟨h29, hx⟩ := hx
  obtain ⟨bp35_5_1_1, hx⟩ := hx
  obtain ⟨bl35_5_1_1, hx⟩ := hx
  obtain ⟨h30, hx⟩ := hx
  obtain ⟨h31, hx⟩ := hx
  obtain ⟨h32, hx⟩ := hx
  obtain ⟨h33, hx⟩ := hx
  obtain ⟨h34, hx⟩ := hx
  obtain ⟨tl9_6_1_1, hx⟩ := hx
  obtain ⟨h35, hx⟩ := hx
  obtain ⟨h36, hx⟩ := hx
  obtain ⟨tl24_6_1_1, hx⟩ := hx
  obtain ⟨h37, hx⟩ := hx
  obtain ⟨h38, hx⟩ := hx
  obtain ⟨u0_1, hx⟩ := hx
  obtain ⟨u1_1, hx⟩ := hx
  obtain ⟨u2_1, hx⟩ := hx
  obtain ⟨k_2_1, hx⟩ := hx
  obtain ⟨f2c'_2_1, hx⟩ := hx
  obtain ⟨f30'_2_1, hx⟩ := hx
  obtain ⟨rem'_2_1, hx⟩ := hx
  obtain ⟨sl0'_2_1, hx⟩ := hx
  obtain ⟨sl1'_2_1, hx⟩ := hx
  obtain ⟨sl2'_2_1, hx⟩ := hx
  obtain ⟨sl3'_2_1, hx⟩ := hx
  obtain ⟨sl4'_2_1, hx⟩ := hx
  obtain ⟨sl5'_2_1, hx⟩ := hx
  obtain ⟨sl6'_2_1, hx⟩ := hx
  obtain ⟨sl7'_2_1, hx⟩ := hx
  obtain ⟨sl8'_2_1, hx⟩ := hx
  obtain ⟨sl9'_2_1, hx⟩ := hx
  obtain ⟨cur'_2_1, hx⟩ := hx
  obtain ⟨h39, hx⟩ := hx
  obtain ⟨h40, hx⟩ := hx
  obtain ⟨h41, hx⟩ := hx
  obtain ⟨h42, hx⟩ := hx
  obtain ⟨h43, hx⟩ := hx
  obtain ⟨h44, hx⟩ := hx
  obtain ⟨h45, hx⟩ := hx
  obtain ⟨h46, hx⟩ := hx
  obtain ⟨h47, hx⟩ := hx
  obtain ⟨h48, hx⟩ := hx
  obtain ⟨h49, hx⟩ := hx
  obtain ⟨h50, hx⟩ := hx
  obtain ⟨h51, hx⟩ := hx
  obtain ⟨sr40_2_1, hx⟩ := hx
  obtain ⟨ss40_2_1, hx⟩ := hx
  obtain ⟨h52, hx⟩ := hx
  obtain ⟨k_4_1, hx⟩ := hx
  obtain ⟨h53, hx⟩ := hx
  obtain ⟨h54, hx⟩ := hx
  obtain ⟨c'_4_1, hx⟩ := hx
  obtain ⟨q'_4_1, hx⟩ := hx
  obtain ⟨h55, hx⟩ := hx
  obtain ⟨h56, hx⟩ := hx
  obtain ⟨h57, hx⟩ := hx
  obtain ⟨pv_5_1, hx⟩ := hx
  obtain ⟨h58, hx⟩ := hx
  obtain ⟨h59, hx⟩ := hx
  obtain ⟨h60, hx⟩ := hx
  obtain ⟨h61, hx⟩ := hx
  obtain ⟨h62, hx⟩ := hx
  obtain ⟨h63, hx⟩ := hx
  obtain ⟨h64, hx⟩ := hx
  obtain ⟨sr43_6_1, hx⟩ := hx
  obtain ⟨ss43_6_1, hx⟩ := hx
  obtain ⟨h65, hx⟩ := hx
  obtain ⟨h66, hx⟩ := hx
  obtain ⟨tl10_1_1_3, hx⟩ := hx
  obtain ⟨h67, hx⟩ := hx
  obtain ⟨h68, hx⟩ := hx
  obtain ⟨tl21_1_1_3, hx⟩ := hx
  obtain ⟨h69, hx⟩ := hx
  obtain ⟨h70, hx⟩ := hx
  obtain ⟨te30_1_1_3, hx⟩ := hx
  obtain ⟨h71, hx⟩ := hx
  obtain ⟨h72, hx⟩ := hx
  obtain ⟨tl2_2_1_3, hx⟩ := hx
  obtain ⟨h73, hx⟩ := hx
  obtain ⟨h74, hx⟩ := hx
  obtain ⟨op13_2_1_3, hx⟩ := hx
  obtain ⟨ol13_2_1_3, hx⟩ := hx
  obtain ⟨h75, hx⟩ := hx
  obtain ⟨to13_2_1_3, hx⟩ := hx
  obtain ⟨h76, hx⟩ := hx
  obtain ⟨h77, hx⟩ := hx
  obtain ⟨tl21_2_1_3, hx⟩ := hx
  obtain ⟨h78, hx⟩ := hx
  obtain ⟨h79, hx⟩ := hx
  obtain ⟨tl32_2_1_3, hx⟩ := hx
  obtain ⟨h80, hx⟩ := hx
  obtain ⟨h81, hx⟩ := hx
  obtain ⟨h82, hx⟩ := hx
  obtain ⟨te43_2_1_3, hx⟩ := hx
  obtain ⟨h83, hx⟩ := hx
  obtain ⟨tl2_3_1_3, hx⟩ := hx
  obtain ⟨h84, hx⟩ := hx
  obtain ⟨h85, hx⟩ := hx
  obtain ⟨te11_3_1_3, hx⟩ := hx
  obtain ⟨h86, hx⟩ := hx
  obtain ⟨h87, hx⟩ := hx
  obtain ⟨tl19_3_1_3, hx⟩ := hx
  obtain ⟨h88, hx⟩ := hx
  obtain ⟨op28_3_1_3, hx⟩ := hx
  obtain ⟨ol28_3_1_3, hx⟩ := hx
  obtain ⟨h89, hx⟩ := hx
  obtain ⟨to28_3_1_3, hx⟩ := hx
  obtain ⟨h90, hx⟩ := hx
  obtain ⟨h91, hx⟩ := hx
  obtain ⟨tl2_4_1_3, hx⟩ := hx
  obtain ⟨h92, hx⟩ := hx
  obtain ⟨h93, hx⟩ := hx
  obtain ⟨vp23_4_1_3, hx⟩ := hx
  obtain ⟨vl23_4_1_3, hx⟩ := hx
  obtain ⟨h94, hx⟩ := hx
  obtain ⟨te23_4_1_3, hx⟩ := hx
  obtain ⟨h95, hx⟩ := hx
  obtain ⟨h96, hx⟩ := hx
  obtain ⟨tr5_w328_5_1_3, hx⟩ := hx
  obtain ⟨tr5_w32c_5_1_3, hx⟩ := hx
  obtain ⟨h97, hx⟩ := hx
  obtain ⟨h98, hx⟩ := hx
  obtain ⟨tl2_6_1_3, hx⟩ := hx
  obtain ⟨h99, hx⟩ := hx
  obtain ⟨h100, hx⟩ := hx
  obtain ⟨tl13_6_1_3, hx⟩ := hx
  obtain ⟨h101, hx⟩ := hx
  obtain ⟨h102, hx⟩ := hx
  obtain ⟨h103, hx⟩ := hx
  obtain ⟨te25_6_1_3, hx⟩ := hx
  obtain ⟨h104, hx⟩ := hx
  obtain ⟨tl31_6_1_3, hx⟩ := hx
  obtain ⟨h105, hx⟩ := hx
  obtain ⟨h106, hx⟩ := hx
  obtain ⟨te39_6_1_3, hx⟩ := hx
  obtain ⟨h107, hx⟩ := hx
  obtain ⟨tl45_6_1_3, hx⟩ := hx
  obtain ⟨h108, hx⟩ := hx
  obtain ⟨h109, hx⟩ := hx
  obtain ⟨h110, hx⟩ := hx
  obtain ⟨tl6_1_2_3, hx⟩ := hx
  obtain ⟨h111, hx⟩ := hx
  obtain ⟨op15_1_2_3, hx⟩ := hx
  obtain ⟨ol15_1_2_3, hx⟩ := hx
  obtain ⟨h112, hx⟩ := hx
  obtain ⟨to15_1_2_3, hx⟩ := hx
  obtain ⟨h113, hx⟩ := hx
  obtain ⟨tl20_1_2_3, hx⟩ := hx
  obtain ⟨h114, hx⟩ := hx
  obtain ⟨h115, hx⟩ := hx
  obtain ⟨h116, hx⟩ := hx
  obtain ⟨trv_w64_2_2_3, hx⟩ := hx
  obtain ⟨trv_w7c_2_2_3, hx⟩ := hx
  obtain ⟨h117, hx⟩ := hx
  obtain ⟨h118, hx⟩ := hx
  obtain ⟨k_3_3, hx⟩ := hx
  obtain ⟨dg'_3_3, hx⟩ := hx
  obtain ⟨flag'_3_3, hx⟩ := hx
  obtain ⟨cp'_3_3, hx⟩ := hx
  obtain ⟨rem'_3_3, hx⟩ := hx
  obtain ⟨h119, hx⟩ := hx
  obtain ⟨h120, hx⟩ := hx
  obtain ⟨h121, hx⟩ := hx
  obtain ⟨h122, hx⟩ := hx
  obtain ⟨op9_3_3, hx⟩ := hx
  obtain ⟨ol9_3_3, hx⟩ := hx
  obtain ⟨h123, hx⟩ := hx
  obtain ⟨te9_3_3, hx⟩ := hx
  obtain ⟨h124, hx⟩ := hx
  obtain ⟨h125, hx⟩ := hx
  obtain ⟨vp20_3_3, hx⟩ := hx
  obtain ⟨vl20_3_3, hx⟩ := hx
  obtain ⟨h126, hx⟩ := hx
  obtain ⟨te20_3_3, hx⟩ := hx
  obtain ⟨h127, hx⟩ := hx
  obtain ⟨sr25_3_3, hx⟩ := hx
  obtain ⟨ss25_3_3, hx⟩ := hx
  obtain ⟨h128, hx⟩ := hx
  obtain ⟨h129, hx⟩ := hx
  obtain ⟨tl9_1_4_3, hx⟩ := hx
  obtain ⟨h130, hx⟩ := hx
  obtain ⟨h131, hx⟩ := hx
  obtain ⟨h132, hx⟩ := hx
  obtain ⟨te20_1_4_3, hx⟩ := hx
  obtain ⟨h133, hx⟩ := hx
  obtain ⟨op26_1_4_3, hx⟩ := hx
  obtain ⟨ol26_1_4_3, hx⟩ := hx
  obtain ⟨h134, hx⟩ := hx
  obtain ⟨to26_1_4_3, hx⟩ := hx
  obtain ⟨h135, hx⟩ := hx
  obtain ⟨tl30_1_4_3, hx⟩ := hx
  obtain ⟨h136, hx⟩ := hx
  obtain ⟨h137, hx⟩ := hx
  obtain ⟨te39_1_4_3, hx⟩ := hx
  obtain ⟨h138, hx⟩ := hx
  obtain ⟨vp45_1_4_3, hx⟩ := hx
  obtain ⟨vl45_1_4_3, hx⟩ := hx
  obtain ⟨h139, hx⟩ := hx
  obtain ⟨te45_1_4_3, hx⟩ := hx
  obtain ⟨h140, hx⟩ := hx
  obtain ⟨h141, hx⟩ := hx
  obtain ⟨h142, hx⟩ := hx
  obtain ⟨tl2_2_4_3, hx⟩ := hx
  obtain ⟨h143, hx⟩ := hx
  obtain ⟨ip2_2_4_3, hx⟩ := hx
  obtain ⟨il2_2_4_3, hx⟩ := hx
  obtain ⟨h144, hx⟩ := hx
  obtain ⟨h145, hx⟩ := hx
  obtain ⟨tl13_2_4_3, hx⟩ := hx
  obtain ⟨h146, hx⟩ := hx
  obtain ⟨tm18_2_4_3, hx⟩ := hx
  obtain ⟨h147, hx⟩ := hx
  obtain ⟨tt3_w264_3_4_3, hx⟩ := hx
  obtain ⟨tt3_w268_3_4_3, hx⟩ := hx
  obtain ⟨h148, hx⟩ := hx
  obtain ⟨h149, hx⟩ := hx
  obtain ⟨tt4_w264_4_4_3, hx⟩ := hx
  obtain ⟨tt4_w268_4_4_3, hx⟩ := hx
  obtain ⟨h150, hx⟩ := hx
  obtain ⟨h151, hx⟩ := hx
  obtain ⟨tt5_w264_5_4_3, hx⟩ := hx
  obtain ⟨tt5_w268_5_4_3, hx⟩ := hx
  obtain ⟨h152, hx⟩ := hx
  obtain ⟨h153, hx⟩ := hx
  obtain ⟨tt6_w264_6_4_3, hx⟩ := hx
  obtain ⟨tt6_w268_6_4_3, hx⟩ := hx
  obtain ⟨h154, hx⟩ := hx
  obtain ⟨h155, hx⟩ := hx
  obtain ⟨k_6_3, hx⟩ := hx
  obtain ⟨h156, hx⟩ := hx
  obtain ⟨h157, hx⟩ := hx
  obtain ⟨c'_6_3, hx⟩ := hx
  obtain ⟨q'_6_3, hx⟩ := hx
  obtain ⟨h158, hx⟩ := hx
  obtain ⟨h159, hx⟩ := hx
  obtain ⟨h160, hx⟩ := hx
  obtain ⟨h161, hx⟩ := hx
  obtain ⟨h162, hx⟩ := hx
  obtain ⟨h163, hx⟩ := hx
  obtain ⟨pv_8_3, hx⟩ := hx
  obtain ⟨h164, hx⟩ := hx
  obtain ⟨h165, hx⟩ := hx
  obtain ⟨ix8_1_1_4, hx⟩ := hx
  obtain ⟨h166, hx⟩ := hx
  obtain ⟨ix18_1_1_4, hx⟩ := hx
  obtain ⟨h167, hx⟩ := hx
  obtain ⟨ix26_1_1_4, hx⟩ := hx
  obtain ⟨h168, hx⟩ := hx
  obtain ⟨ix34_1_1_4, hx⟩ := hx
  obtain ⟨h169, hx⟩ := hx
  obtain ⟨h170, hx⟩ := hx
  obtain ⟨h171, hx⟩ := hx
  obtain ⟨h172, hx⟩ := hx
  obtain ⟨c'_2_4, hx⟩ := hx
  obtain ⟨p'_2_4, hx⟩ := hx
  obtain ⟨w64'_2_4, hx⟩ := hx
  obtain ⟨w74'_2_4, hx⟩ := hx
  obtain ⟨h173, hx⟩ := hx
  obtain ⟨h174, hx⟩ := hx
  obtain ⟨h175, hx⟩ := hx
  obtain ⟨bs7_2_4, hx⟩ := hx
  obtain ⟨h176, hx⟩ := hx
  obtain ⟨h177, hx⟩ := hx
  obtain ⟨k_3_4, hx⟩ := hx
  obtain ⟨h178, hx⟩ := hx
  obtain ⟨h179, hx⟩ := hx
  obtain ⟨c'_3_4, hx⟩ := hx
  obtain ⟨q'_3_4, hx⟩ := hx
  obtain ⟨h180, hx⟩ := hx
  obtain ⟨h181, hx⟩ := hx
  obtain ⟨h182, hx⟩ := hx
  obtain ⟨sg_5_4, hx⟩ := hx
  obtain ⟨k_5_4, hx⟩ := hx
  obtain ⟨f'_5_4, hx⟩ := hx
  obtain ⟨w38'_5_4, hx⟩ := hx
  obtain ⟨w50'_5_4, hx⟩ := hx
  obtain ⟨sg'_5_4, hx⟩ := hx
  obtain ⟨h183, hx⟩ := hx
  obtain ⟨h184, hx⟩ := hx
  obtain ⟨h185, hx⟩ := hx
  obtain ⟨h186, hx⟩ := hx
  obtain ⟨h187, hx⟩ := hx
  obtain ⟨root6_3_6_4, hx⟩ := hx
  obtain ⟨h188, hx⟩ := hx
  obtain ⟨h189, hx⟩ := hx
  obtain ⟨h190, hx⟩ := hx
  obtain ⟨h191, hx⟩ := hx
  obtain ⟨h192, hx⟩ := hx
  obtain ⟨h193, hx⟩ := hx
  obtain ⟨h194, hx⟩ := hx
  obtain ⟨h195, hx⟩ := hx
  obtain ⟨h196, hx⟩ := hx
  obtain ⟨h197, hx⟩ := hx
  obtain ⟨n1, hx⟩ := hx
  obtain ⟨c1, hx⟩ := hx
  obtain ⟨fR1, hx⟩ := hx
  obtain ⟨s1, hx⟩ := hx
  obtain ⟨E1, hx⟩ := hx
  obtain ⟨V1, hx⟩ := hx
  obtain ⟨r1_3, hx⟩ := hx
  obtain ⟨r1_4, hx⟩ := hx
  obtain ⟨r1_2, hx⟩ := hx
  obtain ⟨r1_18, hx⟩ := hx
  obtain ⟨r1_19, hx⟩ := hx
  obtain ⟨r1_20, hx⟩ := hx
  obtain ⟨r1_21, hx⟩ := hx
  obtain ⟨r1_22, hx⟩ := hx
  obtain ⟨r1_23, hx⟩ := hx
  obtain ⟨r1_24, hx⟩ := hx
  obtain ⟨r1_25, hx⟩ := hx
  obtain ⟨w1_3c, hx⟩ := hx
  obtain ⟨w1_54, hx⟩ := hx
  obtain ⟨w1_58, hx⟩ := hx
  obtain ⟨w1_5c, hx⟩ := hx
  obtain ⟨w1_60, hx⟩ := hx
  obtain ⟨w1_78, hx⟩ := hx
  obtain ⟨w1_7c, hx⟩ := hx
  obtain ⟨w1_388, hx⟩ := hx
  obtain ⟨w1_38c, hx⟩ := hx
  obtain ⟨w1_390, hx⟩ := hx
  obtain ⟨w1_394, hx⟩ := hx
  obtain ⟨w1_1c, hx⟩ := hx
  obtain ⟨w1_20, hx⟩ := hx
  obtain ⟨w1_34, hx⟩ := hx
  obtain ⟨w1_40, hx⟩ := hx
  obtain ⟨w1_4c, hx⟩ := hx
  obtain ⟨w1_64, hx⟩ := hx
  obtain ⟨w1_74, hx⟩ := hx
  obtain ⟨q1_3e0, hx⟩ := hx
  obtain ⟨w1_380, hx⟩ := hx
  obtain ⟨w1_398, hx⟩ := hx
  obtain ⟨w1_39c, hx⟩ := hx
  obtain ⟨w1_3a0, hx⟩ := hx
  obtain ⟨w1_3a4, hx⟩ := hx
  obtain ⟨b1_384, hx⟩ := hx
  obtain ⟨b1_3a8, hx⟩ := hx
  obtain ⟨w1_68, hx⟩ := hx
  obtain ⟨w1_6c, hx⟩ := hx
  obtain ⟨w1_70, hx⟩ := hx
  obtain ⟨b1_1fc, hx⟩ := hx
  obtain ⟨b1_420, hx⟩ := hx
  obtain ⟨b1_421, hx⟩ := hx
  obtain ⟨w1_24, hx⟩ := hx
  obtain ⟨w1_38, hx⟩ := hx
  obtain ⟨w1_50, hx⟩ := hx
  obtain ⟨w1_28, hx⟩ := hx
  obtain ⟨w1_44, hx⟩ := hx
  obtain ⟨w1_48, hx⟩ := hx
  obtain ⟨w1_18, hx⟩ := hx
  obtain ⟨w1_30, hx⟩ := hx
  obtain ⟨w1_2c, hx⟩ := hx
  obtain ⟨w1_94, hx⟩ := hx
  obtain ⟨w1_9c, hx⟩ := hx
  obtain ⟨w1_a4, hx⟩ := hx
  obtain ⟨b1_130, hx⟩ := hx
  obtain ⟨w1_80, hx⟩ := hx
  obtain ⟨w1_84, hx⟩ := hx
  obtain ⟨w1_88, hx⟩ := hx
  obtain ⟨w1_8c, hx⟩ := hx
  obtain ⟨w1_90, hx⟩ := hx
  obtain ⟨w1_98, hx⟩ := hx
  obtain ⟨w1_a0, hx⟩ := hx
  obtain ⟨w1_a8, hx⟩ := hx
  obtain ⟨w1_ac, hx⟩ := hx
  obtain ⟨w1_b0, hx⟩ := hx
  obtain ⟨w1_b4, hx⟩ := hx
  obtain ⟨w1_b8, hx⟩ := hx
  obtain ⟨w1_bc, hx⟩ := hx
  obtain ⟨w1_c0, hx⟩ := hx
  obtain ⟨w1_c4, hx⟩ := hx
  obtain ⟨w1_128, hx⟩ := hx
  obtain ⟨b1_c8, hx⟩ := hx
  obtain ⟨w1_170, hx⟩ := hx
  obtain ⟨w1_174, hx⟩ := hx
  obtain ⟨w1_178, hx⟩ := hx
  obtain ⟨w1_17c, hx⟩ := hx
  obtain ⟨w1_180, hx⟩ := hx
  obtain ⟨w1_184, hx⟩ := hx
  obtain ⟨w1_188, hx⟩ := hx
  obtain ⟨w1_18c, hx⟩ := hx
  obtain ⟨w1_1f0, hx⟩ := hx
  obtain ⟨w1_1f4, hx⟩ := hx
  obtain ⟨b1_190, hx⟩ := hx
  have K1_L := hx
  exact .inr (.inr ⟨t_1_1_1, h0, h1, tl1_2_1_1, h2, tl8_2_1_1, h3, tl16_2_1_1, h4, bp16_2_1_1, bl16_2_1_1, h5, h6, tl28_2_1_1, h7, h8, te41_2_1_1, h9, h10, tl1_3_1_1, h11, ip1_3_1_1, il1_3_1_1, h12, h13, tl8_3_1_1, h14, op21_3_1_1, ol21_3_1_1, h15, h16, tl3_4_1_1, h17, tl11_4_1_1, h18, tm20_4_1_1, rs20_4_1_1, h19, tm28_4_1_1, rs28_4_1_1, h20, h21, tl2_5_1_1, h22, tl6_5_1_1, h23, op15_5_1_1, ol15_5_1_1, prp15_5_1_1, pu15_5_1_1, h24, ta15_5_1_1, h25, h26, h27, h28, tl35_5_1_1, h29, bp35_5_1_1, bl35_5_1_1, h30, h31, h32, h33, h34, tl9_6_1_1, h35, h36, tl24_6_1_1, h37, h38, u0_1, u1_1, u2_1, k_2_1, f2c'_2_1, f30'_2_1, rem'_2_1, sl0'_2_1, sl1'_2_1, sl2'_2_1, sl3'_2_1, sl4'_2_1, sl5'_2_1, sl6'_2_1, sl7'_2_1, sl8'_2_1, sl9'_2_1, cur'_2_1, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, sr40_2_1, ss40_2_1, h52, k_4_1, h53, h54, c'_4_1, q'_4_1, h55, h56, h57, pv_5_1, h58, h59, h60, h61, h62, h63, h64, sr43_6_1, ss43_6_1, h65, h66, tl10_1_1_3, h67, h68, tl21_1_1_3, h69, h70, te30_1_1_3, h71, h72, tl2_2_1_3, h73, h74, op13_2_1_3, ol13_2_1_3, h75, to13_2_1_3, h76, h77, tl21_2_1_3, h78, h79, tl32_2_1_3, h80, h81, h82, te43_2_1_3, h83, tl2_3_1_3, h84, h85, te11_3_1_3, h86, h87, tl19_3_1_3, h88, op28_3_1_3, ol28_3_1_3, h89, to28_3_1_3, h90, h91, tl2_4_1_3, h92, h93, vp23_4_1_3, vl23_4_1_3, h94, te23_4_1_3, h95, h96, tr5_w328_5_1_3, tr5_w32c_5_1_3, h97, h98, tl2_6_1_3, h99, h100, tl13_6_1_3, h101, h102, h103, te25_6_1_3, h104, tl31_6_1_3, h105, h106, te39_6_1_3, h107, tl45_6_1_3, h108, h109, h110, tl6_1_2_3, h111, op15_1_2_3, ol15_1_2_3, h112, to15_1_2_3, h113, tl20_1_2_3, h114, h115, h116, trv_w64_2_2_3, trv_w7c_2_2_3, h117, h118, k_3_3, dg'_3_3, flag'_3_3, cp'_3_3, rem'_3_3, h119, h120, h121, h122, op9_3_3, ol9_3_3, h123, te9_3_3, h124, h125, vp20_3_3, vl20_3_3, h126, te20_3_3, h127, sr25_3_3, ss25_3_3, h128, h129, tl9_1_4_3, h130, h131, h132, te20_1_4_3, h133, op26_1_4_3, ol26_1_4_3, h134, to26_1_4_3, h135, tl30_1_4_3, h136, h137, te39_1_4_3, h138, vp45_1_4_3, vl45_1_4_3, h139, te45_1_4_3, h140, h141, h142, tl2_2_4_3, h143, ip2_2_4_3, il2_2_4_3, h144, h145, tl13_2_4_3, h146, tm18_2_4_3, h147, tt3_w264_3_4_3, tt3_w268_3_4_3, h148, h149, tt4_w264_4_4_3, tt4_w268_4_4_3, h150, h151, tt5_w264_5_4_3, tt5_w268_5_4_3, h152, h153, tt6_w264_6_4_3, tt6_w268_6_4_3, h154, h155, k_6_3, h156, h157, c'_6_3, q'_6_3, h158, h159, h160, h161, h162, h163, pv_8_3, h164, h165, ix8_1_1_4, h166, ix18_1_1_4, h167, ix26_1_1_4, h168, ix34_1_1_4, h169, h170, h171, h172, c'_2_4, p'_2_4, w64'_2_4, w74'_2_4, h173, h174, h175, bs7_2_4, h176, h177, k_3_4, h178, h179, c'_3_4, q'_3_4, h180, h181, h182, sg_5_4, k_5_4, f'_5_4, w38'_5_4, w50'_5_4, sg'_5_4, h183, h184, h185, h186, h187, root6_3_6_4, h188, h189, h190, h191, h192, h193, h194, h195, h196, h197, sv_ok_1a9e (sv_frW FW) E1 s1 c1 (fun x hx => (fR1 x hx).trans (fM x hx).symm) V1 hret r1_2 r1_18 hOk r1_3 r1_4 w1_3c w1_7c r1_21 r1_24⟩)

end C3.RV32.Sv
