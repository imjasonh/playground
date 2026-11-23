import C3BootProofs.Proofs.SvSegSv
import C3BootProofs.Proofs.SvOk

/-!
# `sigstore::verify` from 0x72 to its return

Written by `scripts/gen-sv-top.py` from `sv_seg_sv` and `sv_ok_3264`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Gd

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
/-- **`sigstore::verify` from 0x72 to its return**: it returns `Err`, panics, or meets the success condition and returns `Ok`. -/
theorem sv_verify_72 {B out bp rootp dg lp ll : Word} {v : Nat → Word} {n0 : Machine} {sl5 : Word} {sl7 : Word} {sl9 : Word} {wd0 : Word} {wd4 : Word} {wd8 : Word} {wdc : Word} {we0 : Word} {we4 : Word} {we8 : Word} {wec : Word} {wf0 : Word} {wf4 : Word} {wf8 : Word} {wfc : Word} {w100 : Word} {w104 : Word} {w108 : Word} {w10c : Word} {w110 : Word} {w114 : Word} {w118 : Word} {w11c : Word} {w120 : Word} {w124 : Word} {w128 : Word} {w12c : Word} {w8 : Word} {wc : Word} {w10 : Word} {w14 : Word} {w18 : Word} {w1c : Word}
    (F : Fr B 0x3830)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x72 (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_10 : reg n0 a0 = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (g0_11 : reg n0 a1 = B + 0x21A0 + BitVec.ofNat 32 0x2E0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = lp)
    (g0_22 : reg n0 (22 : Fin 32) = dg)
    (g0_25 : reg n0 (25 : Fin 32) = rootp)
    (g0_26 : reg n0 (26 : Fin 32) = ll)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_2e0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp)
    (w0_2e4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll)
    (w0_2e8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = lp)
    (w0_2ec : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = ll)
    (lc_in : SvIn B lp ll.toNat)
    (D0 : P2Data M0)
    (w0_a34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5)
    (w0_a3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7)
    (w0_a44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9)
    (SD0 : SvData M0)
    (H' : ∀ i, i < 4 → ∀ c'_4 q'_4, (c'_4, q'_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((rootp) + BitVec.ofNat 32 0x3C)) → (SvIn B (q'_4 + 0xFFFFFFFC) 4) ∧ (SvIn B (q'_4 + 0x0) 4) ∧ ((q'_4 + 0xFFFFFFFC).toNat % 4 = 0) ∧ ((q'_4 + 0x0).toNat % 4 = 0) ∧ ((memLoad32 M0 (q'_4 + 0xFFFFFFFC)) ≠ 0 → SvIn B (memLoad32 M0 (q'_4 + 0xFFFFFFFC)) (memLoad32 M0 (q'_4 + 0x0)).toNat))
    (SH0 : SvShaCode M0)
    (KS : SvKSep B)
    (PE0 : PvEnv7 M0)
    (pkp_in : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x3C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4) 4)
    (apk : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x3C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4).toNat % 4 = 0)
    (pk_in : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x3C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (memLoad32 M0 (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4)) 0x61)
    (side : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x3C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → ∀ M, PvSide M (memLoad32 M0 (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4)) (B + 0x21A0 + BitVec.ofNat 32 0x1020) 48 (B + 0x21A0 + BitVec.ofNat 32 0xD0)
      (B + 0x21A0 + BitVec.ofNat 32 0x100))
    (w0_d0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0)
    (w0_d4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4)
    (w0_d8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8)
    (w0_dc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc)
    (w0_e0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0)
    (w0_e4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4)
    (w0_e8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8)
    (w0_ec : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec)
    (w0_f0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0)
    (w0_f4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4)
    (w0_f8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8)
    (w0_fc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc)
    (w0_100 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100)
    (w0_104 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104)
    (w0_108 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108)
    (w0_10c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c)
    (w0_110 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110)
    (w0_114 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114)
    (w0_118 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118)
    (w0_11c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c)
    (w0_120 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120)
    (w0_124 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124)
    (w0_128 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128)
    (w0_12c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c)
    (ts_in : SvIn B ((memLoad32 M0 (bp + 0x8))) ((memLoad32 M0 (bp + 0xC))).toNat)
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
    (htsp_in : SvIn B (bp + 0x8) 4)
    (htsl_in : SvIn B (bp + 0xC) 4)
    (atsp : (bp + 0x8).toNat % 4 = 0)
    (atsl : (bp + 0xC).toNat % 4 = 0)
    (EC0 : SvEcCode M0)
    (IC0 : SvIvCode M0)
    (UC0 : SvUpCode M0)
    (BG0 : BGEnv M0)
    (RS : SvRoSep B)
    (BY0 : BYEnv M0)
    (dg_in : SvIn B dg 32)
    (UE0 : CodeIn M0 (BitVec.ofNat 32 uint8EqAddress) uint8EqCode)
    (N80 : CodeIn M0 (BitVec.ofNat 32 norm8Address) norm8Code)
    (PM0 : CodeIn M0 (BitVec.ofNat 32 p256ScalarMulAddress) p256ScalarMulCode)
    (WM0 : CodeIn M0 (BitVec.ofNat 32 wideMulAddress) wideMulCode)
    (PT0 : SvPtCode M0)
    (WN0 : SvWnCode M0)
    (ME : MlEnv M0)
    (P2C0 : P2Code M0)
    (GDC0 : C3.RV32.Gd.GdCode M0)
    (P2D0 : P2Data M0)
    (SC0 : CodeIn M0 (BitVec.ofNat 32 p256ScalarCtEqAddress) p256ScalarCtEqCode)
    (hidC : CodeIn M0 (BitVec.ofNat 32 p256IdentityAddress) p256IdentityData)
    (GD : CodeIn M0 (BitVec.ofNat 32 p256GMontAddress) p256GMontData)
    (OD : CodeIn M0 (BitVec.ofNat 32 p256MontOneAddress) p256MontOneData)
    (AD : CodeIn M0 (BitVec.ofNat 32 p256AffineIdXAddress) p256AffineIdXData)
    (hzi : ∀ Z τd_2 τf_2 Dz_2 Fz_2, τd_2 ≤ 1 → τf_2 ≤ 1 → sgnVal τf_2 Fz_2 = (p256Sz M0 Z).f → sgnVal τd_2 Dz_2 = (p256Sz M0 Z).d →
        normVal8 τd_2 τf_2 Dz_2 (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8) < p256)
    (c0_in : SvIn B ((memLoad32 M0 (bp + 0x20))) ((memLoad32 M0 (bp + 0x24))).toNat)
    (hc0p_in : SvIn B (bp + 0x20) 4)
    (hc0l_in : SvIn B (bp + 0x24) 4)
    (ac0p : (bp + 0x20).toNat % 4 = 0)
    (ac0l : (bp + 0x24).toNat % 4 = 0)
    (D0' : SvData M0)
    (H'' : ∀ i, i < 4 → ∀ c'_5_3 q'_5_3, (c'_5_3, q'_5_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((rootp) + BitVec.ofNat 32 0x198)) → (SvIn B (q'_5_3 + 0x20) 4) ∧ (SvIn B (q'_5_3 + 0x24) 4) ∧ ((q'_5_3 + 0x20).toNat % 4 = 0) ∧ ((q'_5_3 + 0x24).toNat % 4 = 0) ∧ ((memLoad32 M0 (q'_5_3 + 0x20)) ≠ 0 → SvIn B (memLoad32 M0 (q'_5_3 + 0x20)) (memLoad32 M0 (q'_5_3 + 0x24)).toNat))
    (S2 : SvSha2Code M0)
    (KS' : SvK2Sep B)
    (pkp_in' : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x198)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x18) 4)
    (apk' : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x198)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x18).toNat % 4 = 0)
    (pk_in' : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x198)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (memLoad32 M0 (((y1) + BitVec.ofNat 32 0x20) + 0x18)) 0x61)
    (side' : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x198)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → ∀ M, PvSide M (memLoad32 M0 (((y1) + BitVec.ofNat 32 0x20) + 0x18)) (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 (B + 0x21A0 + BitVec.ofNat 32 0xA40)
      (B + 0x21A0 + BitVec.ofNat 32 0xA70))
    (w0_8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8)
    (w0_c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc)
    (w0_10 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = w10)
    (w0_14 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = w14)
    (w0_18 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = w18)
    (w0_1c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c)
    (CK0 : SvCkCode M0)
    (ckp_in4 : SvIn B (bp + 0x18) 4)
    (ckl_in4 : SvIn B (bp + 0x1C) 4)
    (a_ckp : (bp + 0x18).toNat % 4 = 0)
    (a_ckl : (bp + 0x1C).toNat % 4 = 0)
    (ck_in : SvIn B (memLoad32 M0 (bp + 0x18)) (memLoad32 M0 (bp + 0x1C)).toNat)
    (H''' : ∀ i, i < 8 → ∀ c'_3_4 q'_3_4 w80'_3_4, (c'_3_4, q'_3_4, w80'_3_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2.1)) + BitVec.ofNat 32 0x20, (memLoad32 M0 ((s.2.1) + 0x20)))) i ((BitVec.ofNat 32 0x100), ((rootp) + BitVec.ofNat 32 0x98), rootp) → (SvIn B (q'_3_4 + 0x20) 4) ∧ (SvIn B (q'_3_4 + 0x24) 4) ∧ ((q'_3_4 + 0x20).toNat % 4 = 0) ∧ ((q'_3_4 + 0x24).toNat % 4 = 0) ∧ ((memLoad32 M0 (q'_3_4 + 0x20)) ≠ 0 → SvIn B (memLoad32 M0 (q'_3_4 + 0x20)) (memLoad32 M0 (q'_3_4 + 0x24)).toNat))
    (KS'' : SvK2Sep B)
    (kp_in4 : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 M0 (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), ((rootp) + BitVec.ofNat 32 0x98), rootp) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x18) 4)
    (kw_in4 : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 M0 (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), ((rootp) + BitVec.ofNat 32 0x98), rootp) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x1C) 4)
    (a_kp : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 M0 (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), ((rootp) + BitVec.ofNat 32 0x98), rootp) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x18).toNat % 4 = 0)
    (a_kw : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 M0 (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), ((rootp) + BitVec.ofNat 32 0x98), rootp) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x1C).toNat % 4 = 0)
    (kp_in : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 M0 (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), ((rootp) + BitVec.ofNat 32 0x98), rootp) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (memLoad32 M0 (((y1) + BitVec.ofNat 32 0x20) + 0x18)) 32)
    (EE0 : EvEnv M0)
    (hiv : (s5Hv M0 (BitVec.ofNat 32 0x3FCC4AF8)).toList = Sha512.h0)
    (pk_in'' : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 M0 (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), ((rootp) + BitVec.ofNat 32 0x98), rootp) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (memLoad32 M0 (((y1) + BitVec.ofNat 32 0x20) + 0x18)) 32)
    (lid_in : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 M0 (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), ((rootp) + BitVec.ofNat 32 0x98), rootp) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + BitVec.ofNat 32 0x5) 19)
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
    (ii2h : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x3C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8) 4)
    (ai2h : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x3C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8).toNat % 4 = 0)
    (ii2l : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x3C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE4) 4)
    (ai2l : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x3C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE4).toNat % 4 = 0)
    (ii3h : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x3C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0) 4)
    (ai3h : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x3C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0).toNat % 4 = 0)
    (ii3l : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x3C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFEC) 4)
    (ai3l : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x3C)) → (memLoad32 M0 (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFEC).toNat % 4 = 0)
    (it4h : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x198)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xC) 4)
    (at4h : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x198)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xC).toNat % 4 = 0)
    (it4l : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x198)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x8) 4)
    (at4l : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x198)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x8).toNat % 4 = 0)
    (it5h : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x198)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x14) 4)
    (at5h : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x198)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x14).toNat % 4 = 0)
    (it5l : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x198)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x10) 4)
    (at5l : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x198)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x10).toNat % 4 = 0)
    (hOk : SvOutOk B out) :
    SvErrRet B out v n0 ∨ Panics n0 ∨
    (∃ t_1_1_1, derElement 0x30 (memBytes M0 lp ll.toNat) = .ok t_1_1_1 ∧ ll - BitVec.ofNat 32 (t_1_1_1.header + t_1_1_1.len) = 0 ∧
      ∃ tl1_2_1_1, derElement 0x30 (memBytes M0 ((lp + BitVec.ofNat 32 t_1_1_1.header)) ((BitVec.ofNat 32 t_1_1_1.len)).toNat) = .ok tl1_2_1_1 ∧
      ∃ tl8_2_1_1, derElement 0x30 (memBytes M0 (((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) (((BitVec.ofNat 32 t_1_1_1.len)) - BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)).toNat) = .ok tl8_2_1_1 ∧
      ∃ tl16_2_1_1, derElement 3 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) + BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) ((((BitVec.ofNat 32 t_1_1_1.len)) - BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) - BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)).toNat) = .ok tl16_2_1_1 ∧
      ∃ bp16_2_1_1 bl16_2_1_1, derBitsOf (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) + BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) ((((BitVec.ofNat 32 t_1_1_1.len)) - BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) - BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)).toNat) ((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) + BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) (.ok tl16_2_1_1) = .ok (bp16_2_1_1, bl16_2_1_1) ∧
      (((((BitVec.ofNat 32 t_1_1_1.len)) - BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) - BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) - BitVec.ofNat 32 (tl16_2_1_1.header + tl16_2_1_1.len) = 0) ∧
      ∃ tl29_2_1_1, derOptRes 0xA0 (memBytes M0 (((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) (BitVec.ofNat 32 tl1_2_1_1.len).toNat) = some (.ok tl29_2_1_1) ∧
      derIntIsOf M0 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 tl29_2_1_1.header) (BitVec.ofNat 32 tl29_2_1_1.len).toNat) ((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 tl29_2_1_1.header) (derElement 2 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 tl29_2_1_1.header) (BitVec.ofNat 32 tl29_2_1_1.len).toNat)) ((BitVec.ofNat 32 0x2).extractLsb' 0 8) = .ok true ∧
      ∃ te43_2_1_1, derElement 2 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 tl29_2_1_1.header) (BitVec.ofNat 32 tl29_2_1_1.len).toNat) = .ok te43_2_1_1 ∧
      ((BitVec.ofNat 32 tl29_2_1_1.len) - BitVec.ofNat 32 (te43_2_1_1.header + te43_2_1_1.len) = 0) ∧
      ∃ tl2_3_1_1, derElement 2 (memBytes M0 (((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) (((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))).toNat) = .ok tl2_3_1_1 ∧
      ∃ ip2_3_1_1 il2_3_1_1, derPosIntOf (memBytes M0 (((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) (((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))).toNat) (((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) (.ok tl2_3_1_1) = .ok (ip2_3_1_1, il2_3_1_1) ∧
      ((il2_3_1_1).toNat ≤ 20) ∧
      ∃ tl9_3_1_1, derElement 0x30 (memBytes M0 ((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) ((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) - BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)).toNat) = .ok tl9_3_1_1 ∧
      ∃ op19_3_1_1 ol19_3_1_1, derAlgOf M0 ((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) (tl9_3_1_1.header + tl9_3_1_1.len) = .ok ((op19_3_1_1, ol19_3_1_1), none) ∧
      (memBytes M0 op19_3_1_1 ol19_3_1_1 = memBytes M0 (BitVec.ofNat 32 0x3FCC4840) 8) ∧
      ∃ tl6_4_1_1, derElement 0x30 (memBytes M0 ((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) ((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) - BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) - BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))).toNat) = .ok tl6_4_1_1 ∧
      ∃ tl13_4_1_1, derElement 0x30 (memBytes M0 (((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) (((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) - BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) - BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) - BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)).toNat) = .ok tl13_4_1_1 ∧
      ∃ tm22_4_1_1 rs22_4_1_1, readTime (memBytes M0 ((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 tl13_4_1_1.header) (tl13_4_1_1.len)) = some (tm22_4_1_1, rs22_4_1_1) ∧
      ∃ tm31_4_1_1 rs31_4_1_1, readTime rs22_4_1_1 = some (tm31_4_1_1, rs31_4_1_1) ∧
      (rs31_4_1_1 = []) ∧
      ∃ tl2_5_1_1, derElement 0x30 (memBytes M0 (((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) (((((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) - BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) - BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) - BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) - BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))).toNat) = .ok tl2_5_1_1 ∧
      ∃ tl6_5_1_1, derElement 0x30 (memBytes M0 ((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) ((((((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) - BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) - BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) - BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) - BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) - BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)).toNat) = .ok tl6_5_1_1 ∧
      ∃ op15_5_1_1 ol15_5_1_1 prp15_5_1_1 pu15_5_1_1, derAlgOf M0 (((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) (tl6_5_1_1.len) = .ok ((op15_5_1_1, ol15_5_1_1), some (prp15_5_1_1, pu15_5_1_1)) ∧
      ∃ ta15_5_1_1, derElement 0x30 (memBytes M0 (((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) (tl6_5_1_1.len)) = .ok ta15_5_1_1 ∧
      (BitVec.ofNat 8 pu15_5_1_1.tag = BitVec.ofNat 8 6) ∧
      (memBytes M0 (prp15_5_1_1 + BitVec.ofNat 32 pu15_5_1_1.header) pu15_5_1_1.len = memBytes M0 (BitVec.ofNat 32 0x3FCC4848) 8) ∧
      (memBytes M0 op15_5_1_1 ol15_5_1_1 = memBytes M0 (BitVec.ofNat 32 0x3FCC4914) 7) ∧
      ∃ tl35_5_1_1, derElement 3 (memBytes M0 ((((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) + BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)) ((BitVec.ofNat 32 (tl6_5_1_1.len)) - BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)).toNat) = .ok tl35_5_1_1 ∧
      ∃ bp35_5_1_1 bl35_5_1_1, derBitsOf (memBytes M0 ((((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) + BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)) ((BitVec.ofNat 32 (tl6_5_1_1.len)) - BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)).toNat) ((((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) + BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)) (.ok tl35_5_1_1) = .ok (bp35_5_1_1, bl35_5_1_1) ∧
      (bl35_5_1_1 = BitVec.ofNat 32 0x41) ∧
      (((BitVec.ofNat 32 (tl6_5_1_1.len)) - BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)) - BitVec.ofNat 32 (tl35_5_1_1.header + tl35_5_1_1.len) = 0) ∧
      (M0 bp35_5_1_1 = BitVec.ofNat 8 4) ∧
      (GsOk M0 bp35_5_1_1) ∧
      ∃ tl9_6_1_1, derOptRes 0xA3 (memBytes M0 ((((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) ((((((((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) - BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) - BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) - BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) - BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) - BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) - BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))).toNat) = some (.ok tl9_6_1_1) ∧
      (((((((((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) - BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) - BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) - BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) - BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) - BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) - BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) - BitVec.ofNat 32 (tl9_6_1_1.header + tl9_6_1_1.len) = 0) ∧
      ∃ tl25_6_1_1, derElement 0x30 (memBytes M0 (((((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) + BitVec.ofNat 32 tl9_6_1_1.header) (BitVec.ofNat 32 tl9_6_1_1.len).toNat) = .ok tl25_6_1_1 ∧
      ((BitVec.ofNat 32 tl9_6_1_1.len) - BitVec.ofNat 32 (tl25_6_1_1.header + tl25_6_1_1.len) = 0) ∧
      ∃ u0_1 u1_1 u2_1, ∃ k_2_1 f30'_2_1 f34'_2_1 rem'_2_1 cur'_2_1 sl0'_2_1 sl1'_2_1 sl2'_2_1 sl3'_2_1 sl4'_2_1 sl5'_2_1 sl6'_2_1 sl7'_2_1 sl8'_2_1 sl9'_2_1, svChain (sv_extStep B out bp (lp + BitVec.ofNat 32 t_1_1_1.header) bp35_5_1_1 (BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) ll ((((((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) + BitVec.ofNat 32 tl9_6_1_1.header) + BitVec.ofNat 32 tl25_6_1_1.header) (BitVec.ofNat 32 tl25_6_1_1.len) (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 % 2 ^ 32)) (((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len)) (((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) (BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) bl16_2_1_1 lp ((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) (BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len)) (BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) bp16_2_1_1 rootp dg v M0) k_2_1 ((BitVec.ofNat 32 0x0), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 tl25_6_1_1.len), ((((((((((((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) + BitVec.ofNat 32 tl9_6_1_1.header) + BitVec.ofNat 32 tl25_6_1_1.header), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 tl25_6_1_1.len), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 (tl25_6_1_1.header + tl25_6_1_1.len)), (BitVec.ofNat 32 0x0), (u0_1), (BitVec.ofNat 32 0x0), (u1_1), (BitVec.ofNat 32 0x0), (u2_1)) (f30'_2_1, f34'_2_1, rem'_2_1, cur'_2_1, sl0'_2_1, sl1'_2_1, sl2'_2_1, sl3'_2_1, sl4'_2_1, sl5'_2_1, sl6'_2_1, sl7'_2_1, sl8'_2_1, sl9'_2_1) ∧
      rem'_2_1 = 0 ∧ (sl0'_2_1 = 0 ∨ SvIn B sl0'_2_1 sl1'_2_1.toNat) ∧ (sl2'_2_1 = 0 ∨ SvIn B sl2'_2_1 sl3'_2_1.toNat) ∧ (sl4'_2_1 = 0 ∨ SvIn B sl4'_2_1 sl5'_2_1.toNat) ∧ (sl6'_2_1 = 0 ∨ SvIn B sl6'_2_1 sl7'_2_1.toNat) ∧ (sl8'_2_1 = 0 ∨ SvIn B sl8'_2_1 sl9'_2_1.toNat) ∧
      (sl0'_2_1 ≠ 0) ∧ (sl2'_2_1 ≠ 0) ∧ (sl4'_2_1 ≠ 0) ∧ (sl6'_2_1 ≠ 0) ∧ ((if BitVec.ult 0 (sl8'_2_1) then (1 : Word) else 0) &&& ((f30'_2_1) &&& (f34'_2_1)) ≠ 0) ∧ (memBytes M0 (((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) ((BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)).toNat) = memBytes M0 ((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) ((BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len)).toNat)) ∧ ∃ sr43_2_1 ss43_2_1, ecdsaSigOf 48 M0 (bp16_2_1_1) ((bl16_2_1_1.toNat)) = .ok (sr43_2_1, ss43_2_1) ∧
      ∃ k_4_1, k_4_1 < 4 ∧
      (∀ i, i < k_4_1 → ∀ c'_4_1 q'_4_1, (c'_4_1, q'_4_1) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((rootp) + BitVec.ofNat 32 0x3C)) → ¬ (memBytes M0 (memLoad32 M0 (q'_4_1 + 0xFFFFFFFC)) (memLoad32 M0 (q'_4_1 + 0x0)).toNat = memBytes M0 (((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len)) (BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)).toNat)) ∧
      ∃ c'_4_1 q'_4_1, (c'_4_1, q'_4_1) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) k_4_1 ((BitVec.ofNat 32 0x80), ((rootp) + BitVec.ofNat 32 0x3C)) ∧ (memBytes M0 (memLoad32 M0 (q'_4_1 + 0xFFFFFFFC)) (memLoad32 M0 (q'_4_1 + 0x0)).toNat = memBytes M0 (((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len)) (BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)).toNat) ∧
      ((memLoad32 M0 (q'_4_1 + 0xFFFFFFFC)) ≠ 0) ∧
      ∃ pv_5_1, SvPvRes M0 (memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4)) (B + 0x21A0 + BitVec.ofNat 32 0x1020) 48 (sha384 (memBytes M0 (lp + BitVec.ofNat 32 t_1_1_1.header) (BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)).toNat)) (B + 0x21A0 + BitVec.ofNat 32 0xD0) (B + 0x21A0 + BitVec.ofNat 32 0x100) sr43_2_1 ss43_2_1 (some pv_5_1) ∧
      (pv_5_1 ≠ 0) ∧
      (memBytes M0 sl0'_2_1 sl1'_2_1.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x0)) (memLoad32 M0 (rootp + 0x4)).toNat) ∧
      (memBytes M0 sl2'_2_1 sl3'_2_1.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x8)) (memLoad32 M0 (rootp + 0xC)).toNat) ∧
      (memBytes M0 sl4'_2_1 sl5'_2_1.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x10)) (memLoad32 M0 (rootp + 0x14)).toNat) ∧
      (memBytes M0 sl6'_2_1 sl7'_2_1.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x18)) (memLoad32 M0 (rootp + 0x1C)).toNat) ∧
      (memBytes M0 sl8'_2_1 sl9'_2_1.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x20)) (memLoad32 M0 (rootp + 0x24)).toNat) ∧
      ∃ tl49_1_6_1, derElement 0x30 (memBytes M0 ((memLoad32 M0 (bp + 0x8))) ((memLoad32 M0 (bp + 0xC))).toNat) = .ok tl49_1_6_1 ∧
      (((memLoad32 M0 (bp + 0xC))) - BitVec.ofNat 32 (tl49_1_6_1.header + tl49_1_6_1.len) = 0) ∧
      ∃ bs9_2_6_1, derScalarOf 32 (memBytes M0 (((memLoad32 M0 (bp + 0x8))) + BitVec.ofNat 32 tl49_1_6_1.header) (BitVec.ofNat 32 tl49_1_6_1.len).toNat) (((memLoad32 M0 (bp + 0x8))) + BitVec.ofNat 32 tl49_1_6_1.header) (derElement 2 (memBytes M0 (((memLoad32 M0 (bp + 0x8))) + BitVec.ofNat 32 tl49_1_6_1.header) (BitVec.ofNat 32 tl49_1_6_1.len).toNat)) = .ok bs9_2_6_1 ∧
      ∃ te9_2_6_1, derElement 2 (memBytes M0 (((memLoad32 M0 (bp + 0x8))) + BitVec.ofNat 32 tl49_1_6_1.header) (BitVec.ofNat 32 tl49_1_6_1.len).toNat) = .ok te9_2_6_1 ∧
      ∃ bs16_2_6_1, derScalarOf 32 (memBytes M0 ((((memLoad32 M0 (bp + 0x8))) + BitVec.ofNat 32 tl49_1_6_1.header) + BitVec.ofNat 32 (te9_2_6_1.header + te9_2_6_1.len)) ((BitVec.ofNat 32 tl49_1_6_1.len) - BitVec.ofNat 32 (te9_2_6_1.header + te9_2_6_1.len)).toNat) ((((memLoad32 M0 (bp + 0x8))) + BitVec.ofNat 32 tl49_1_6_1.header) + BitVec.ofNat 32 (te9_2_6_1.header + te9_2_6_1.len)) (derElement 2 (memBytes M0 ((((memLoad32 M0 (bp + 0x8))) + BitVec.ofNat 32 tl49_1_6_1.header) + BitVec.ofNat 32 (te9_2_6_1.header + te9_2_6_1.len)) ((BitVec.ofNat 32 tl49_1_6_1.len) - BitVec.ofNat 32 (te9_2_6_1.header + te9_2_6_1.len)).toNat)) = .ok bs16_2_6_1 ∧
      ∃ te16_2_6_1, derElement 2 (memBytes M0 ((((memLoad32 M0 (bp + 0x8))) + BitVec.ofNat 32 tl49_1_6_1.header) + BitVec.ofNat 32 (te9_2_6_1.header + te9_2_6_1.len)) ((BitVec.ofNat 32 tl49_1_6_1.len) - BitVec.ofNat 32 (te9_2_6_1.header + te9_2_6_1.len)).toNat) = .ok te16_2_6_1 ∧
      (((BitVec.ofNat 32 tl49_1_6_1.len) - BitVec.ofNat 32 (te9_2_6_1.header + te9_2_6_1.len)) - BitVec.ofNat 32 (te16_2_6_1.header + te16_2_6_1.len) = 0) ∧
      (((inScalarRange (b32 bs9_2_6_1) (memBytes M0 (BitVec.ofNat 32 0x3FCC4288) 32) = true) ∧ (inScalarRange (b32 bs16_2_6_1) (memBytes M0 (BitVec.ofNat 32 0x3FCC4288) 32) = true) ∧ (M0 bp35_5_1_1 = 4) ∧ True) ∧ ((GsOk M0 bp35_5_1_1) ∧ (beNat (b32 bs9_2_6_1) < C3.p256.n) ∧ (beNat (b32 bs16_2_6_1) < C3.p256.n) ∧ (beNat (b32 bs9_2_6_1) ≠ 0) ∧ (beNat (b32 bs16_2_6_1) ≠ 0) ∧ True)) ∧
      ∃ σd_2 σf_2 Dv_2 Fv_2, σd_2 ≤ 1 ∧ σf_2 ≤ 1 ∧ sgnVal σf_2 Fv_2 = (p256Sf M0 bs16_2_6_1).f ∧ sgnVal σd_2 Dv_2 = (p256Sf M0 bs16_2_6_1).d ∧
      (((Fv_2 = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8)) ∧ True) ∧ ∃ stm_2, mlMain2 (tbl2 (accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x0) 8, accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x20) 8, accV M0 (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x40) 8)) (tbl2 ((gsVal M0 bp35_5_1_1 1 * 2 ^ 256 % p256), (gsVal M0 bp35_5_1_1 0x21 * 2 ^ 256 % p256), (accV M0 (BitVec.ofNat 32 0x3FCC43A8) 8))) (wnafBytes (wnafGo ((psmVal (((beNat (memBytes M0 (dg) 32) % C3.p256.n)) * ((normVal8 σd_2 σf_2 Dv_2 (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0) 0x101) (wnafBytes (wnafGo ((psmVal (((beNat (b32 bs9_2_6_1))) * ((normVal8 σd_2 σf_2 Dv_2 (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0) 0x101) (max (wnafGo ((psmVal (((beNat (memBytes M0 (dg) 32) % C3.p256.n)) * ((normVal8 σd_2 σf_2 Dv_2 (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length (wnafGo ((psmVal (((beNat (b32 bs9_2_6_1))) * ((normVal8 σd_2 σf_2 Dv_2 (accV M0 (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length) = some stm_2 ∧
      ∃ τd_2 τf_2 Dz_2 Fz_2, τd_2 ≤ 1 ∧ τf_2 ≤ 1 ∧ sgnVal τf_2 Fz_2 = (p256Sz M0 stm_2.1.2.2).f ∧ sgnVal τd_2 Dz_2 = (p256Sz M0 stm_2.1.2.2).d ∧
      ((((beNat (b32 bs9_2_6_1)) = (p2fm ((if (((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm ((stm_2.1.1)) ((if ((((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV M0 (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 τd_2 τf_2 Dz_2 (accV M0 (BitVec.ofNat 32 0x3FCC4B38) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 0x3FCC442C) 8)) 1) % C3.p256.n)) ∧ True) ∧
      ∃ tl10_1_1_3, derElement 0x30 (memBytes M0 ((memLoad32 M0 (bp + 0x20))) ((memLoad32 M0 (bp + 0x24))).toNat) = .ok tl10_1_1_3 ∧
      (((memLoad32 M0 (bp + 0x24))) - BitVec.ofNat 32 (tl10_1_1_3.header + tl10_1_1_3.len) = 0) ∧
      ∃ tl22_1_1_3, derElement 0x30 (memBytes M0 (((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) (BitVec.ofNat 32 tl10_1_1_3.len).toNat) = .ok tl22_1_1_3 ∧
      derIntIsOf M0 (memBytes M0 ((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 tl22_1_1_3.header) (BitVec.ofNat 32 tl22_1_1_3.len).toNat) ((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 tl22_1_1_3.header) (derElement 2 (memBytes M0 ((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 tl22_1_1_3.header) (BitVec.ofNat 32 tl22_1_1_3.len).toNat)) ((BitVec.ofNat 32 0x0).extractLsb' 0 8) = .ok true ∧
      ∃ te33_1_1_3, derElement 2 (memBytes M0 ((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 tl22_1_1_3.header) (BitVec.ofNat 32 tl22_1_1_3.len).toNat) = .ok te33_1_1_3 ∧
      ((BitVec.ofNat 32 tl22_1_1_3.len) - BitVec.ofNat 32 (te33_1_1_3.header + te33_1_1_3.len) = 0) ∧
      ∃ tl41_1_1_3, derElement 0x30 (memBytes M0 ((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) ((BitVec.ofNat 32 tl10_1_1_3.len) - BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)).toNat) = .ok tl41_1_1_3 ∧
      (((BitVec.ofNat 32 tl10_1_1_3.len) - BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) - BitVec.ofNat 32 (tl41_1_1_3.header + tl41_1_1_3.len) = 0) ∧
      ∃ op53_1_1_3 ol53_1_1_3, derContent (((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) (derOid (memBytes M0 (((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) (BitVec.ofNat 32 tl41_1_1_3.len).toNat)) = .ok (op53_1_1_3, ol53_1_1_3) ∧
      ∃ to53_1_1_3, derOid (memBytes M0 (((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) (BitVec.ofNat 32 tl41_1_1_3.len).toNat) = .ok to53_1_1_3 ∧
      (memBytes M0 op53_1_1_3 ol53_1_1_3.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC4859) 9) ∧
      ∃ tl2_2_1_3, derElement 0xA0 (memBytes M0 (((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) (((BitVec.ofNat 32 tl41_1_1_3.len) - BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))).toNat) = .ok tl2_2_1_3 ∧
      ((((BitVec.ofNat 32 tl41_1_1_3.len) - BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) - BitVec.ofNat 32 (tl2_2_1_3.header + tl2_2_1_3.len) = 0) ∧
      ∃ tl15_2_1_3, derElement 0x30 (memBytes M0 ((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) (BitVec.ofNat 32 tl2_2_1_3.len).toNat) = .ok tl15_2_1_3 ∧
      ((BitVec.ofNat 32 tl2_2_1_3.len) - BitVec.ofNat 32 (tl15_2_1_3.header + tl15_2_1_3.len) = 0) ∧
      derIntIsOf M0 (memBytes M0 (((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) (BitVec.ofNat 32 tl15_2_1_3.len).toNat) (((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) (derElement 2 (memBytes M0 (((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) (BitVec.ofNat 32 tl15_2_1_3.len).toNat)) ((BitVec.ofNat 32 0x3).extractLsb' 0 8) = .ok true ∧
      ∃ te26_2_1_3, derElement 2 (memBytes M0 (((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) (BitVec.ofNat 32 tl15_2_1_3.len).toNat) = .ok te26_2_1_3 ∧
      ∃ tl32_2_1_3, derElement 0x31 (memBytes M0 ((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) ((BitVec.ofNat 32 tl15_2_1_3.len) - BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)).toNat) = .ok tl32_2_1_3 ∧
      isSha256Of M0 (((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 tl32_2_1_3.header) (BitVec.ofNat 32 tl32_2_1_3.len).toNat = .ok true ∧
      ∃ te41_2_1_3, derElement 0x30 (memBytes M0 (((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 tl32_2_1_3.header) (BitVec.ofNat 32 tl32_2_1_3.len).toNat) = .ok te41_2_1_3 ∧
      ((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te41_2_1_3.header + te41_2_1_3.len) = 0) ∧
      ∃ tl49_2_1_3, derElement 0x30 (memBytes M0 (((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) (((BitVec.ofNat 32 tl15_2_1_3.len) - BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) - BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)).toNat) = .ok tl49_2_1_3 ∧
      ∃ op58_2_1_3 ol58_2_1_3, derContent ((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 tl49_2_1_3.header) (derOid (memBytes M0 ((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 tl49_2_1_3.header) (BitVec.ofNat 32 tl49_2_1_3.len).toNat)) = .ok (op58_2_1_3, ol58_2_1_3) ∧
      ∃ to58_2_1_3, derOid (memBytes M0 ((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 tl49_2_1_3.header) (BitVec.ofNat 32 tl49_2_1_3.len).toNat) = .ok to58_2_1_3 ∧
      (memBytes M0 op58_2_1_3 ol58_2_1_3.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC4862) 11) ∧
      ∃ tl2_3_1_3, derOptRes 0xA0 (memBytes M0 ((((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 tl49_2_1_3.header) + BitVec.ofNat 32 (to58_2_1_3.header + to58_2_1_3.len))) (((BitVec.ofNat 32 tl49_2_1_3.len) - BitVec.ofNat 32 (to58_2_1_3.header + to58_2_1_3.len))).toNat) = some (.ok tl2_3_1_3) ∧
      ((((BitVec.ofNat 32 tl49_2_1_3.len) - BitVec.ofNat 32 (to58_2_1_3.header + to58_2_1_3.len))) - BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len) = 0) ∧
      ∃ vp23_3_1_3 vl23_3_1_3, derContent (((((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 tl49_2_1_3.header) + BitVec.ofNat 32 (to58_2_1_3.header + to58_2_1_3.len))) + BitVec.ofNat 32 tl2_3_1_3.header) (derElement 4 (memBytes M0 (((((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 tl49_2_1_3.header) + BitVec.ofNat 32 (to58_2_1_3.header + to58_2_1_3.len))) + BitVec.ofNat 32 tl2_3_1_3.header) (BitVec.ofNat 32 tl2_3_1_3.len).toNat)) = .ok (vp23_3_1_3, vl23_3_1_3) ∧
      ∃ te23_3_1_3, derElement 4 (memBytes M0 (((((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 tl49_2_1_3.header) + BitVec.ofNat 32 (to58_2_1_3.header + to58_2_1_3.len))) + BitVec.ofNat 32 tl2_3_1_3.header) (BitVec.ofNat 32 tl2_3_1_3.len).toNat) = .ok te23_3_1_3 ∧
      ((BitVec.ofNat 32 tl2_3_1_3.len) - BitVec.ofNat 32 (te23_3_1_3.header + te23_3_1_3.len) = 0) ∧
      ∃ tsa4_w2a8_4_1_3 : Word, ∃ tsa4_w2ac_4_1_3 : Word, (((derOptRes 0xA0 (memBytes M0 (((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))) (((((BitVec.ofNat 32 tl15_2_1_3.len) - BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) - BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) - BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))).toNat) = none) ∧ (((((BitVec.ofNat 32 tl15_2_1_3.len) - BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) - BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) - BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len)) = 0 ∨ (M0 (((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len)))).toNat ≠ 0xA1) ∧ tsa4_w2a8_4_1_3 = ((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len)) ∧ tsa4_w2ac_4_1_3 = ((((BitVec.ofNat 32 tl15_2_1_3.len) - BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) - BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) - BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))) ∨ ((¬ (derOptRes 0xA0 (memBytes M0 (((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))) (((((BitVec.ofNat 32 tl15_2_1_3.len) - BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) - BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) - BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))).toNat) = none)) ∧ ∃ tl2, derOptRes 0xA0 (memBytes M0 (((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))) (((((BitVec.ofNat 32 tl15_2_1_3.len) - BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) - BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) - BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))).toNat) = some (.ok tl2) ∧ ((((((BitVec.ofNat 32 tl15_2_1_3.len) - BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) - BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) - BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0 ∨ (M0 ((((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))) + BitVec.ofNat 32 (tl2.header + tl2.len))).toNat ≠ 0xA1) ∧ tsa4_w2a8_4_1_3 = (((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tsa4_w2ac_4_1_3 = (((((BitVec.ofNat 32 tl15_2_1_3.len) - BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) - BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) - BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tsa4_w2a8_4_1_3 tsa4_w2ac_4_1_3.toNat ∧
      ∃ tl2_5_1_3, derElement 0x31 (memBytes M0 (tsa4_w2a8_4_1_3) (tsa4_w2ac_4_1_3).toNat) = .ok tl2_5_1_3 ∧
      ((tsa4_w2ac_4_1_3) - BitVec.ofNat 32 (tl2_5_1_3.header + tl2_5_1_3.len) = 0) ∧
      ∃ tl13_5_1_3, derElement 0x30 (memBytes M0 ((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) (BitVec.ofNat 32 tl2_5_1_3.len).toNat) = .ok tl13_5_1_3 ∧
      ((BitVec.ofNat 32 tl2_5_1_3.len) - BitVec.ofNat 32 (tl13_5_1_3.header + tl13_5_1_3.len) = 0) ∧
      derIntIsOf M0 (memBytes M0 (((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) (BitVec.ofNat 32 tl13_5_1_3.len).toNat) (((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) (derElement 2 (memBytes M0 (((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) (BitVec.ofNat 32 tl13_5_1_3.len).toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = .ok true ∧
      ∃ te25_5_1_3, derElement 2 (memBytes M0 (((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) (BitVec.ofNat 32 tl13_5_1_3.len).toNat) = .ok te25_5_1_3 ∧
      ∃ tl31_5_1_3, derElement 0x30 (memBytes M0 ((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) ((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)).toNat) = .ok tl31_5_1_3 ∧
      isSha256Of M0 (((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) (((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)).toNat = .ok true ∧
      ∃ te39_5_1_3, derElement 0x30 (memBytes M0 (((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) (((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)).toNat) = .ok te39_5_1_3 ∧
      ∃ tl45_5_1_3, derOptRes 0xA0 (memBytes M0 ((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) ((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)).toNat) = some (.ok tl45_5_1_3) ∧
      (BitVec.ofNat 32 tl45_5_1_3.len ≠ 0) ∧
      (((BitVec.ofNat 32 tl45_5_1_3.len)).toNat ≤ ((BitVec.ofNat 32 tl45_5_1_3.len)).toNat) ∧
      ∃ tl6_1_2_3, derElement 0x30 (memBytes M0 ((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) ((BitVec.ofNat 32 tl45_5_1_3.len)).toNat) = .ok tl6_1_2_3 ∧
      ∃ op15_1_2_3 ol15_1_2_3, derContent (((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) (derOid (memBytes M0 (((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) (BitVec.ofNat 32 tl6_1_2_3.len).toNat)) = .ok (op15_1_2_3, ol15_1_2_3) ∧
      ∃ to15_1_2_3, derOid (memBytes M0 (((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) (BitVec.ofNat 32 tl6_1_2_3.len).toNat) = .ok to15_1_2_3 ∧
      ∃ tl20_1_2_3, derElement 0x31 (memBytes M0 ((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) ((BitVec.ofNat 32 tl6_1_2_3.len) - BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)).toNat) = .ok tl20_1_2_3 ∧
      (((BitVec.ofNat 32 tl6_1_2_3.len) - BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) - BitVec.ofNat 32 (tl20_1_2_3.header + tl20_1_2_3.len) = 0) ∧
      listsOidOf M0 (((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header) (((BitVec.ofNat 32 tl45_5_1_3.len)) - ((BitVec.ofNat 32 tl45_5_1_3.len))).toNat (memBytes M0 op15_1_2_3 ol15_1_2_3.toNat) = .ok false ∧
      ∃ tsav_r24_2_2_3 : Word, ∃ tsav_w78_2_2_3 : Word, ∃ tsav_w1388_2_2_3 : Word, ∃ tsav_w138c_2_2_3 : Word, (((memBytes M0 op15_1_2_3 ol15_1_2_3.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC486E) 9) ∧ ∃ op5 ol5, derContent ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) (derOid (memBytes M0 ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat)) = .ok (op5, ol5) ∧ ∃ to5, derOid (memBytes M0 ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat) = .ok to5 ∧ (memBytes M0 op5 ol5.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC4862) 11) ∧ (((BitVec.ofNat 32 tl20_1_2_3.len)) - BitVec.ofNat 32 (to5.header + to5.len) = 0) ∧ tsav_r24_2_2_3 = (BitVec.ofNat 32 0x0) ∧ tsav_w78_2_2_3 = BitVec.ofNat 32 0x1 ∧ tsav_w1388_2_2_3 = ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) + BitVec.ofNat 32 (to5.header + to5.len) ∧ tsav_w138c_2_2_3 = ((BitVec.ofNat 32 tl20_1_2_3.len)) - BitVec.ofNat 32 (to5.header + to5.len)) ∨ ((¬ (memBytes M0 op15_1_2_3 ol15_1_2_3.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC486E) 9)) ∧ (memBytes M0 op15_1_2_3 ol15_1_2_3.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC4877) 9) ∧ ∃ vp8 vl8, derContent ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) (derElement 4 (memBytes M0 ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat)) = .ok (vp8, vl8) ∧ ∃ te8, derElement 4 (memBytes M0 ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat) = .ok te8 ∧ (vl8 = 32) ∧ (((BitVec.ofNat 32 tl20_1_2_3.len)) - BitVec.ofNat 32 (te8.header + te8.len) = 0) ∧ tsav_r24_2_2_3 = vp8 ∧ tsav_w78_2_2_3 = (BitVec.ofNat 32 0x0) ∧ tsav_w1388_2_2_3 = ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) + BitVec.ofNat 32 (te8.header + te8.len) ∧ tsav_w138c_2_2_3 = ((BitVec.ofNat 32 tl20_1_2_3.len)) - BitVec.ofNat 32 (te8.header + te8.len)) ∨ ((¬ (memBytes M0 op15_1_2_3 ol15_1_2_3.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC486E) 9)) ∧ (¬ (memBytes M0 op15_1_2_3 ol15_1_2_3.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC4877) 9)) ∧ tsav_r24_2_2_3 = (BitVec.ofNat 32 0x0) ∧ tsav_w78_2_2_3 = (BitVec.ofNat 32 0x0) ∧ tsav_w1388_2_2_3 = (((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header) ∧ tsav_w138c_2_2_3 = (BitVec.ofNat 32 tl20_1_2_3.len))) ∧ SvIn B tsav_w1388_2_2_3 tsav_w138c_2_2_3.toNat ∧ (tsav_r24_2_2_3 = 0 ∨ SvIn B tsav_r24_2_2_3 32) ∧
      ∃ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31, ∃ k_3_3 dg'_3_3 flag'_3_3 cp'_3_3 rem'_3_3, svChain (sv_attrStep B out bp vl23_3_1_3 ll (((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header) (BitVec.ofNat 32 tl45_5_1_3.len) (((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len)) (((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) - BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len)) (u0) (u1) (u2) (u3) (u4) (u5) (u6) (u7) ((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) (BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 % 2 ^ 32)) ((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) (BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len)) (memLoad32 M0 (bp + 0xC)) (memLoad32 M0 (bp + 0x8)) lp vp23_3_1_3 ((q'_4_1) + BitVec.ofNat 32 0x20) rootp dg (lp + BitVec.ofNat 32 t_1_1_1.header) (BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) (((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len)) (BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) sl0'_2_1 sl1'_2_1 sl2'_2_1 sl3'_2_1 sl4'_2_1 sl5'_2_1 sl6'_2_1 sl7'_2_1 sl8'_2_1 sl9'_2_1 (BitVec.ofNat 32 (tm22_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32)) (u8) (u9) (u10) (u11) (u12) (u13) (u14) (u15) (u16) (u17) (u18) (u19) (u20) (u21) (u22) (u23) (u24) (u25) (u26) (u27) (u28) (u29) (u30) (u31) bp35_5_1_1 v M0) k_3_3 (tsav_r24_2_2_3, tsav_w78_2_2_3, (((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 (tl6_1_2_3.header + tl6_1_2_3.len)), (((BitVec.ofNat 32 tl45_5_1_3.len)) - BitVec.ofNat 32 (tl6_1_2_3.header + tl6_1_2_3.len))) (dg'_3_3, flag'_3_3, cp'_3_3, rem'_3_3) ∧
      rem'_3_3 = 0 ∧ (dg'_3_3 = 0 ∨ SvIn B dg'_3_3 32) ∧
      (dg'_3_3 ≠ 0 ∧ flag'_3_3 = 1) ∧ ∃ op8_3_3 ol8_3_3, derAlgOf M0 ((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) (((((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) - BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))).toNat) = .ok ((op8_3_3, ol8_3_3), none) ∧ ∃ te8_3_3, derElement 0x30 (memBytes M0 ((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) ((((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) - BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))).toNat) = .ok te8_3_3 ∧ (memBytes M0 op8_3_3 ol8_3_3 = memBytes M0 (BitVec.ofNat 32 0x3FCC4818) 8) ∧ ∃ vp19_3_3 vl19_3_3, derContent (((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) + BitVec.ofNat 32 (te8_3_3.header + te8_3_3.len)) (derElement 4 (memBytes M0 (((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) + BitVec.ofNat 32 (te8_3_3.header + te8_3_3.len)) (((((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) - BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) - BitVec.ofNat 32 (te8_3_3.header + te8_3_3.len)).toNat)) = .ok (vp19_3_3, vl19_3_3) ∧ ∃ te19_3_3, derElement 4 (memBytes M0 (((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) + BitVec.ofNat 32 (te8_3_3.header + te8_3_3.len)) (((((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) - BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) - BitVec.ofNat 32 (te8_3_3.header + te8_3_3.len)).toNat) = .ok te19_3_3 ∧ ∃ sr24_3_3 ss24_3_3, ecdsaSigOf 48 M0 (vp19_3_3) ((vl19_3_3).toNat) = .ok (sr24_3_3, ss24_3_3) ∧
      (((((((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) - BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) - BitVec.ofNat 32 (te8_3_3.header + te8_3_3.len)) - BitVec.ofNat 32 (te19_3_3.header + te19_3_3.len)) = 0) ∧
      ∃ tl13_1_4_3, derElement 0x30 (memBytes M0 (vp23_3_1_3) (vl23_3_1_3).toNat) = .ok tl13_1_4_3 ∧
      ((vl23_3_1_3) - BitVec.ofNat 32 (tl13_1_4_3.header + tl13_1_4_3.len) = 0) ∧
      derIntIsOf M0 (memBytes M0 ((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) (BitVec.ofNat 32 tl13_1_4_3.len).toNat) ((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) (derElement 2 (memBytes M0 ((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) (BitVec.ofNat 32 tl13_1_4_3.len).toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = .ok true ∧
      ∃ te26_1_4_3, derElement 2 (memBytes M0 ((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) (BitVec.ofNat 32 tl13_1_4_3.len).toNat) = .ok te26_1_4_3 ∧
      ∃ op32_1_4_3 ol32_1_4_3, derContent (((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) (derOid (memBytes M0 (((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) ((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)).toNat)) = .ok (op32_1_4_3, ol32_1_4_3) ∧
      ∃ to32_1_4_3, derOid (memBytes M0 (((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) ((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)).toNat) = .ok to32_1_4_3 ∧
      ∃ tl36_1_4_3, derElement 0x30 (memBytes M0 ((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) (((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) - BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)).toNat) = .ok tl36_1_4_3 ∧
      isSha256Of M0 (((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 tl36_1_4_3.header) (BitVec.ofNat 32 tl36_1_4_3.len).toNat = .ok true ∧
      ∃ te45_1_4_3, derElement 0x30 (memBytes M0 (((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 tl36_1_4_3.header) (BitVec.ofNat 32 tl36_1_4_3.len).toNat) = .ok te45_1_4_3 ∧
      ∃ vp51_1_4_3 vl51_1_4_3, derContent ((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 tl36_1_4_3.header) + BitVec.ofNat 32 (te45_1_4_3.header + te45_1_4_3.len)) (derElement 4 (memBytes M0 ((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 tl36_1_4_3.header) + BitVec.ofNat 32 (te45_1_4_3.header + te45_1_4_3.len)) ((BitVec.ofNat 32 tl36_1_4_3.len) - BitVec.ofNat 32 (te45_1_4_3.header + te45_1_4_3.len)).toNat)) = .ok (vp51_1_4_3, vl51_1_4_3) ∧
      ∃ te51_1_4_3, derElement 4 (memBytes M0 ((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 tl36_1_4_3.header) + BitVec.ofNat 32 (te45_1_4_3.header + te45_1_4_3.len)) ((BitVec.ofNat 32 tl36_1_4_3.len) - BitVec.ofNat 32 (te45_1_4_3.header + te45_1_4_3.len)).toNat) = .ok te51_1_4_3 ∧
      (vl51_1_4_3 = 32) ∧
      (((BitVec.ofNat 32 tl36_1_4_3.len) - BitVec.ofNat 32 (te45_1_4_3.header + te45_1_4_3.len)) - BitVec.ofNat 32 (te51_1_4_3.header + te51_1_4_3.len) = 0) ∧
      ∃ tl2_2_4_3, derElement 2 (memBytes M0 ((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) (((((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) - BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) - BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))).toNat) = .ok tl2_2_4_3 ∧
      ∃ ip2_2_4_3 il2_2_4_3, derPosIntOf (memBytes M0 ((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) (((((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) - BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) - BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))).toNat) ((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) (.ok tl2_2_4_3) = .ok (ip2_2_4_3, il2_2_4_3) ∧
      (((il2_2_4_3) - (aluEval .sltu ((M0 (ip2_2_4_3)).zeroExtend 32) 1)).toNat ≤ 20) ∧
      ∃ tl13_2_4_3, derElement 0x18 (memBytes M0 (((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) ((((((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) - BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) - BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)).toNat) = .ok tl13_2_4_3 ∧
      ∃ tm18_2_4_3, generalizedTime (memBytes M0 ((((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 tl13_2_4_3.header) ((BitVec.ofNat 32 tl13_2_4_3.len).toNat)) = some tm18_2_4_3 ∧
      ∃ tst3_w1328_3_4_3 : Word, ∃ tst3_w132c_3_4_3 : Word, (((derOptRes 0x30 (memBytes M0 (((((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) ((((((((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) - BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) - BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))).toNat) = none) ∧ tst3_w1328_3_4_3 = ((((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len)) ∧ tst3_w132c_3_4_3 = (((((((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) - BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) - BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) ∨ ((¬ (derOptRes 0x30 (memBytes M0 (((((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) ((((((((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) - BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) - BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))).toNat) = none)) ∧ ∃ tl2, derOptRes 0x30 (memBytes M0 (((((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) ((((((((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) - BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) - BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))).toNat) = some (.ok tl2) ∧ tst3_w1328_3_4_3 = (((((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tst3_w132c_3_4_3 = ((((((((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) - BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) - BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tst3_w1328_3_4_3 tst3_w132c_3_4_3.toNat ∧
      ∃ tst4_r8_4_4_3 : Word, ∃ tst4_w1328_4_4_3 : Word, ∃ tst4_w132c_4_4_3 : Word, (((tst3_w132c_3_4_3 = 0) ∧ tst4_r8_4_4_3 = BitVec.ofNat 32 0x18 ∧ tst4_w1328_4_4_3 = tst3_w1328_3_4_3 ∧ tst4_w132c_4_4_3 = tst3_w132c_3_4_3) ∨ ((¬ (tst3_w132c_3_4_3 = 0)) ∧ (M0 tst3_w1328_3_4_3 = BitVec.ofNat 8 1) ∧ derBoolOf (memBytes M0 (tst3_w1328_3_4_3) (tst3_w132c_3_4_3).toNat) (derElement 1 (memBytes M0 (tst3_w1328_3_4_3) (tst3_w132c_3_4_3).toNat)) = .ok () ∧ ∃ tb10_1, derElement 1 (memBytes M0 (tst3_w1328_3_4_3) (tst3_w132c_3_4_3).toNat) = .ok tb10_1 ∧ ∃ tst4b_w1328_2 : Word, ∃ tst4b_w132c_2 : Word, (((((tst3_w132c_3_4_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len)) = 0) ∧ tst4b_w1328_2 = ((tst3_w1328_3_4_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len)) ∧ tst4b_w132c_2 = ((tst3_w132c_3_4_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) ∨ ((¬ (((tst3_w132c_3_4_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len)) = 0)) ∧ ∃ tst4n_w1328_2 : Word, ∃ tst4n_w132c_2 : Word, (((M0 ((tst3_w1328_3_4_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len)) = BitVec.ofNat 8 2) ∧ ∃ ip4 il4, derIntOf (memBytes M0 (((tst3_w1328_3_4_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) (((tst3_w132c_3_4_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len))).toNat) (((tst3_w1328_3_4_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) (derElement 2 (memBytes M0 (((tst3_w1328_3_4_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) (((tst3_w132c_3_4_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len))).toNat)) = .ok (ip4, il4) ∧ ∃ ti4, derElement 2 (memBytes M0 (((tst3_w1328_3_4_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) (((tst3_w132c_3_4_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len))).toNat) = .ok ti4 ∧ tst4n_w1328_2 = (((tst3_w1328_3_4_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) + BitVec.ofNat 32 (ti4.header + ti4.len) ∧ tst4n_w132c_2 = (((tst3_w132c_3_4_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) - BitVec.ofNat 32 (ti4.header + ti4.len)) ∨ ((¬ (M0 ((tst3_w1328_3_4_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len)) = BitVec.ofNat 8 2)) ∧ tst4n_w1328_2 = ((tst3_w1328_3_4_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len)) ∧ tst4n_w132c_2 = ((tst3_w132c_3_4_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len)))) ∧ SvIn B tst4n_w1328_2 tst4n_w132c_2.toNat ∧ tst4b_w1328_2 = tst4n_w1328_2 ∧ tst4b_w132c_2 = tst4n_w132c_2)) ∧ SvIn B tst4b_w1328_2 tst4b_w132c_2.toNat ∧ tst4_r8_4_4_3 = (BitVec.ofNat 32 0xFFFFFFFF) ∧ tst4_w1328_4_4_3 = tst4b_w1328_2 ∧ tst4_w132c_4_4_3 = tst4b_w132c_2) ∨ ((¬ (tst3_w132c_3_4_3 = 0)) ∧ (¬ (M0 tst3_w1328_3_4_3 = BitVec.ofNat 8 1)) ∧ ∃ tst4n_w1328_2 : Word, ∃ tst4n_w132c_2 : Word, (((M0 tst3_w1328_3_4_3 = BitVec.ofNat 8 2) ∧ ∃ ip4 il4, derIntOf (memBytes M0 (tst3_w1328_3_4_3) (tst3_w132c_3_4_3).toNat) (tst3_w1328_3_4_3) (derElement 2 (memBytes M0 (tst3_w1328_3_4_3) (tst3_w132c_3_4_3).toNat)) = .ok (ip4, il4) ∧ ∃ ti4, derElement 2 (memBytes M0 (tst3_w1328_3_4_3) (tst3_w132c_3_4_3).toNat) = .ok ti4 ∧ tst4n_w1328_2 = (tst3_w1328_3_4_3) + BitVec.ofNat 32 (ti4.header + ti4.len) ∧ tst4n_w132c_2 = (tst3_w132c_3_4_3) - BitVec.ofNat 32 (ti4.header + ti4.len)) ∨ ((¬ (M0 tst3_w1328_3_4_3 = BitVec.ofNat 8 2)) ∧ tst4n_w1328_2 = tst3_w1328_3_4_3 ∧ tst4n_w132c_2 = tst3_w132c_3_4_3)) ∧ SvIn B tst4n_w1328_2 tst4n_w132c_2.toNat ∧ tst4_r8_4_4_3 = (BitVec.ofNat 32 0x18) ∧ tst4_w1328_4_4_3 = tst4n_w1328_2 ∧ tst4_w132c_4_4_3 = tst4n_w132c_2)) ∧ SvIn B tst4_w1328_4_4_3 tst4_w132c_4_4_3.toNat ∧
      ∃ tst5_w1328_5_4_3 : Word, ∃ tst5_w132c_5_4_3 : Word, (((derOptRes 0xA0 (memBytes M0 (tst4_w1328_4_4_3) (tst4_w132c_4_4_3).toNat) = none) ∧ tst5_w1328_5_4_3 = tst4_w1328_4_4_3 ∧ tst5_w132c_5_4_3 = tst4_w132c_4_4_3) ∨ ((¬ (derOptRes 0xA0 (memBytes M0 (tst4_w1328_4_4_3) (tst4_w132c_4_4_3).toNat) = none)) ∧ ∃ tl2, derOptRes 0xA0 (memBytes M0 (tst4_w1328_4_4_3) (tst4_w132c_4_4_3).toNat) = some (.ok tl2) ∧ tst5_w1328_5_4_3 = (tst4_w1328_4_4_3) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tst5_w132c_5_4_3 = (tst4_w132c_4_4_3) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tst5_w1328_5_4_3 tst5_w132c_5_4_3.toNat ∧
      ∃ tst6_w1328_6_4_3 : Word, ∃ tst6_w132c_6_4_3 : Word, (((derOptRes 0xA1 (memBytes M0 (tst5_w1328_5_4_3) (tst5_w132c_5_4_3).toNat) = none) ∧ (tst5_w132c_5_4_3 = 0) ∧ tst6_w1328_6_4_3 = tst5_w1328_5_4_3 ∧ tst6_w132c_6_4_3 = tst5_w132c_5_4_3) ∨ ((¬ (derOptRes 0xA1 (memBytes M0 (tst5_w1328_5_4_3) (tst5_w132c_5_4_3).toNat) = none)) ∧ ∃ tl2, derOptRes 0xA1 (memBytes M0 (tst5_w1328_5_4_3) (tst5_w132c_5_4_3).toNat) = some (.ok tl2) ∧ ((tst5_w132c_5_4_3) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0) ∧ tst6_w1328_6_4_3 = (tst5_w1328_5_4_3) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tst6_w132c_6_4_3 = (tst5_w132c_5_4_3) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tst6_w1328_6_4_3 tst6_w132c_6_4_3.toNat ∧
      ∃ k_5_3, k_5_3 < 4 ∧
      (∀ i, i < k_5_3 → ∀ c'_5_3 q'_5_3, (c'_5_3, q'_5_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((rootp) + BitVec.ofNat 32 0x198)) → ¬ (memBytes M0 (memLoad32 M0 (q'_5_3 + 0x20)) (memLoad32 M0 (q'_5_3 + 0x24)).toNat = memBytes M0 ((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) (BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)).toNat)) ∧
      ∃ c'_5_3 q'_5_3, (c'_5_3, q'_5_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) k_5_3 ((BitVec.ofNat 32 0x80), ((rootp) + BitVec.ofNat 32 0x198)) ∧ (memBytes M0 (memLoad32 M0 (q'_5_3 + 0x20)) (memLoad32 M0 (q'_5_3 + 0x24)).toNat = memBytes M0 ((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) (BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)).toNat) ∧
      ((memLoad32 M0 (q'_5_3 + 0x20)) ≠ 0) ∧
      (sha256 (memBytes M0 (vp23_3_1_3) (vl23_3_1_3).toNat) = memBytes M0 dg'_3_3 32) ∧
      (sha256 (memBytes M0 ((memLoad32 M0 (bp + 0x8))) ((memLoad32 M0 (bp + 0xC))).toNat) = memBytes M0 vp51_1_4_3 32) ∧
      ((BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len)) ≠ 0) ∧
      ∃ pv_7_3, SvPvRes M0 (memLoad32 M0 (((q'_5_3) + BitVec.ofNat 32 0x20) + 0x18)) (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 (sha256 (memBytes M0 (BitVec.ofNat 32 0x3FCC486D) (1) ++ memBytes M0 ((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len))) + BitVec.ofNat 32 0x1) ((((BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) + BitVec.ofNat 32 0xFFFFFFFF).toNat))) (B + 0x21A0 + BitVec.ofNat 32 0xA40) (B + 0x21A0 + BitVec.ofNat 32 0xA70) sr24_3_3 ss24_3_3 (some pv_7_3) ∧
      (pv_7_3 ≠ 0) ∧
      ∃ ix7_1_1_4, nlScan M0 ((memLoad32 M0 (bp + 0x18))) 0 (((memLoad32 M0 (bp + 0x1C))).toNat) = some ix7_1_1_4 ∧
      ∃ ix17_1_1_4, nlScan M0 (((memLoad32 M0 (bp + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)) 0 ((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix7_1_1_4 + 1)) = some ix17_1_1_4 ∧
      ∃ ix25_1_1_4, nlScan M0 ((((memLoad32 M0 (bp + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)) + BitVec.ofNat 32 (ix17_1_1_4 + 1)) 0 (((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) = some ix25_1_1_4 ∧
      ∃ ix33_1_1_4, nlScan M0 (((((memLoad32 M0 (bp + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)) + BitVec.ofNat 32 (ix17_1_1_4 + 1)) + BitVec.ofNat 32 (ix25_1_1_4 + 1)) 0 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) = some ix33_1_1_4 ∧
      (BitVec.ofNat 32 ix33_1_1_4 = 0) ∧
      (BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1) ≠ 0) ∧
      (((1 < (BitVec.ofNat 32 ix17_1_1_4).toNat) ∧ ((BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1)).toNat < (memLoad32 M0 (bp + 0x1C)).toNat) ∧ (¬ ((memLoad32 M0 (bp + 0x1C))).toNat < ((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 M0 (bp + 0x1C)))).toNat) ∧ (¬ (((BitVec.ofNat 32 ix17_1_1_4)) + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat) ∧ (M0 (((memLoad32 M0 (bp + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)) ≠ 0x30)) ∨ ((¬ (1 < (BitVec.ofNat 32 ix17_1_1_4).toNat)) ∧ ((BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1)).toNat < (memLoad32 M0 (bp + 0x1C)).toNat) ∧ (¬ ((memLoad32 M0 (bp + 0x1C))).toNat < ((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 M0 (bp + 0x1C)))).toNat) ∧ (¬ (((BitVec.ofNat 32 ix17_1_1_4)) + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat))) ∧
      ∃ c'_2_4 p'_2_4 x21'_2_4 w60'_2_4 w70'_2_4, (c'_2_4, p'_2_4, x21'_2_4, w60'_2_4, w70'_2_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, (s.2.2.2.2), ((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.2.1)) (BitVec.ofNat 32 0xA))))) (BitVec.ofNat 32 ix17_1_1_4).toNat ((BitVec.ofNat 32 ix17_1_1_4), (((memLoad32 M0 (bp + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)), vl23_3_1_3, (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 0x0)) ∧ (∀ i, i < (BitVec.ofNat 32 ix17_1_1_4).toNat → ∀ c'_2_4 p'_2_4 x21'_2_4 w60'_2_4 w70'_2_4, (c'_2_4, p'_2_4, x21'_2_4, w60'_2_4, w70'_2_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, (s.2.2.2.2), ((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.2.1)) (BitVec.ofNat 32 0xA))))) i ((BitVec.ofNat 32 ix17_1_1_4), (((memLoad32 M0 (bp + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)), vl23_3_1_3, (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 0x0)) → ((((((M0 (p'_2_4)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF).toNat < (BitVec.ofNat 32 0xA).toNat)) ∧ (((aluEval .sltu ((aluEval .mul (w70'_2_4) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w60'_2_4) (BitVec.ofNat 32 0xA))) (aluEval .mulhu (w60'_2_4) (BitVec.ofNat 32 0xA))) ||| (aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w70'_2_4) (BitVec.ofNat 32 0xA))) = 0)) ∧ (((aluEval .sltu (((((M0 (p'_2_4)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w60'_2_4) (BitVec.ofNat 32 0xA))) (aluEval .mul (w60'_2_4) (BitVec.ofNat 32 0xA))) &&& (aluEval .sltu (((aluEval .mul (w70'_2_4) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w60'_2_4) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((M0 (p'_2_4)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w60'_2_4) (BitVec.ofNat 32 0xA))) (aluEval .mul (w60'_2_4) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w70'_2_4) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w60'_2_4) (BitVec.ofNat 32 0xA)))) = 0))) ∧
      (w70'_2_4.toNat < 2 ^ 31) ∧ ∃ bs7_2_4, base64Decode (memBytes M0 (((((memLoad32 M0 (bp + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)) + BitVec.ofNat 32 (ix17_1_1_4 + 1))) (((BitVec.ofNat 32 ix25_1_1_4)).toNat)) = some bs7_2_4 ∧ (bs7_2_4.length = 32) ∧
      ∃ k_3_4, k_3_4 < 8 ∧
      (∀ i, i < k_3_4 → ∀ c'_3_4 q'_3_4 w80'_3_4, (c'_3_4, q'_3_4, w80'_3_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2.1)) + BitVec.ofNat 32 0x20, (memLoad32 M0 ((s.2.1) + 0x20)))) i ((BitVec.ofNat 32 0x100), ((rootp) + BitVec.ofNat 32 0x98), rootp) → ¬ (memBytes M0 (memLoad32 M0 (q'_3_4 + 0x20)) (memLoad32 M0 (q'_3_4 + 0x24)).toNat = memBytes M0 (memLoad32 M0 (bp + 0x18)) (BitVec.ofNat 32 ix7_1_1_4).toNat)) ∧
      ∃ c'_3_4 q'_3_4 w80'_3_4, (c'_3_4, q'_3_4, w80'_3_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2.1)) + BitVec.ofNat 32 0x20, (memLoad32 M0 ((s.2.1) + 0x20)))) k_3_4 ((BitVec.ofNat 32 0x100), ((rootp) + BitVec.ofNat 32 0x98), rootp) ∧ (memBytes M0 (memLoad32 M0 (q'_3_4 + 0x20)) (memLoad32 M0 (q'_3_4 + 0x24)).toNat = memBytes M0 (memLoad32 M0 (bp + 0x18)) (BitVec.ofNat 32 ix7_1_1_4).toNat) ∧
      ((memLoad32 M0 (q'_3_4 + 0x20)) ≠ 0) ∧
      ∃ u32 u33 u34 u35 u36 u37 u38 u39 u40 u41 u42 u43 u44 u45 u46 u47 u48 u49 u50 u51 u52 u53 u54 u55 u56 u57 u58 u59 u60, ∃ sg_5_4, ∃ k_5_4 c'_5_4 x21'_5_4 rl'_5_4 rp'_5_4 dg'_5_4 w8'_5_4 wc'_5_4 w28'_5_4 w2c'_5_4 w30'_5_4 w38'_5_4 w40'_5_4 w5c'_5_4 sg'_5_4, svChain (sv_cosigStep vp51_1_4_3 B out bp ll ((q'_3_4) + BitVec.ofNat 32 0x20) bs7_2_4 (le4 (sha256 (memBytes M0 ((memLoad32 M0 (bp + 0x18))) (((BitVec.ofNat 32 ix7_1_1_4)).toNat) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC4850) (1) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC47D7) (1) ++ memBytes M0 ((memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18))) (32))) 0) (memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x1C)) ((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 M0 (bp + 0x1C)))) (memLoad32 M0 (bp + 0x18)) (memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18)) (BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32)) (BitVec.ofNat 32 ix7_1_1_4) (memLoad32 M0 (bp + 0x18)) (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 % 2 ^ 32)) w60'_2_4 (memLoad32 M0 (bp + 0xC)) (memLoad32 M0 (bp + 0x8)) lp w70'_2_4 (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) ((q'_4_1) + BitVec.ofNat 32 0x20) (memLoad32 M0 (q'_3_4 + 0x20)) dg (lp + BitVec.ofNat 32 t_1_1_1.header) (BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) (((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len)) (BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) sl0'_2_1 sl1'_2_1 sl2'_2_1 sl3'_2_1 sl4'_2_1 sl5'_2_1 sl6'_2_1 sl7'_2_1 sl8'_2_1 sl9'_2_1 (BitVec.ofNat 32 (tm22_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32)) (u32) (u33) (u34) (u35) (u36) (u37) (u38) (u39) (u40) (u41) (u42) (u43) (u44) (u45) (u46) (u47) (u48) (u49) (u50) (u51) (u52) (u53) (u54) (u55) bp35_5_1_1 vp23_3_1_3 vl23_3_1_3 ((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) (BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) ((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) (BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len)) (BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32)) (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) dg'_3_3 v 0 0 0 M0) k_5_4 (((c'_3_4) + BitVec.ofNat 32 0xFFFFFFE0), x21'_2_4, (BitVec.ofNat 32 ix25_1_1_4), ((((memLoad32 M0 (bp + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)) + BitVec.ofNat 32 (ix17_1_1_4 + 1)), dg'_3_3, (u56), (u57), (u58), (u59), (BitVec.ofNat 32 0x0), ((((((memLoad32 M0 (bp + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)) + BitVec.ofNat 32 (ix17_1_1_4 + 1)) + BitVec.ofNat 32 (ix25_1_1_4 + 1)) + BitVec.ofNat 32 (ix33_1_1_4 + 1)), (u60), (BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1)), sg_5_4) (c'_5_4, x21'_5_4, rl'_5_4, rp'_5_4, dg'_5_4, w8'_5_4, wc'_5_4, w28'_5_4, w2c'_5_4, w30'_5_4, w38'_5_4, w40'_5_4, w5c'_5_4, sg'_5_4) ∧
      w5c'_5_4 = 0 ∧
      ((w30'_5_4) &&& BitVec.ofNat 32 0x1 ≠ 0) ∧ (evSpec (sigMem M0 (B + 0x21A0 + BitVec.ofNat 32 0x420) sg'_5_4) (memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18)) (B + 0x21A0 + BitVec.ofNat 32 0x420) (memLoad32 M0 (bp + 0x18)) (((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 M0 (bp + 0x1C))))).toNat = true) ∧
      ((((memLoad32 M0 (bp + 0x2C)) = w70'_2_4) ∧ (aluEval .sltu ((memLoad32 M0 (bp + 0x28))) (w60'_2_4) ≠ 0)) ∨ ((¬ ((memLoad32 M0 (bp + 0x2C)) = w70'_2_4)) ∧ (aluEval .sltu ((memLoad32 M0 (bp + 0x2C))) (w70'_2_4) ≠ 0))) ∧
      ∃ root6_3_6_4, rootFromInclusion (pair64 ((memLoad32 M0 (bp + 0x28))) ((memLoad32 M0 (bp + 0x2C)))) (pair64 (w60'_2_4) (w70'_2_4)) ((sha256 ([] ++ memBytes M0 (BitVec.ofNat 32 0x3FCC4106) (0x1) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC46F0) (0x71) ++ base64Encode (memBytes M0 (dg) (32)) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC4761) (0x1B) ++ base64Encode (memBytes M0 ((memLoad32 M0 (bp + 0x8))) (((memLoad32 M0 (bp + 0xC))).toNat)) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC477C) (0x54) ++ base64Encode (memBytes M0 (lp) ((ll).toNat)) ++ memBytes M0 (BitVec.ofNat 32 0x3FCC47D0) (0x7)))) (memBytes M0 ((memLoad32 M0 (bp + 0x10))) (((memLoad32 M0 (bp + 0x14))).toNat)) = some root6_3_6_4 ∧
      (b32 root6_3_6_4 = b32 bs7_2_4) ∧
      ((((BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((BitVec.ofNat 32 (tm22_4_1_1 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm31_4_1_1 % 2 ^ 32))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
      ((((memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE4))) = 0)) ∨ ((¬ ((memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0))) ∧ (aluEval .sltu ((memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFEC))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0)))) ∧ (aluEval .sltu ((memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
      ((((memLoad32 M0 (((q'_5_3) + BitVec.ofNat 32 0x20) + 0xC)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((memLoad32 M0 (((q'_5_3) + BitVec.ofNat 32 0x20) + 0x8))) = 0)) ∨ ((¬ ((memLoad32 M0 (((q'_5_3) + BitVec.ofNat 32 0x20) + 0xC)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((memLoad32 M0 (((q'_5_3) + BitVec.ofNat 32 0x20) + 0xC))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 M0 (((q'_5_3) + BitVec.ofNat 32 0x20) + 0x14))) ∧ (aluEval .sltu ((memLoad32 M0 (((q'_5_3) + BitVec.ofNat 32 0x20) + 0x10))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 M0 (((q'_5_3) + BitVec.ofNat 32 0x20) + 0x14)))) ∧ (aluEval .sltu ((memLoad32 M0 (((q'_5_3) + BitVec.ofNat 32 0x20) + 0x14))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
      ((((memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 3))) = 0)) ∨ ((¬ ((memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15))) ∧ (aluEval .sltu ((memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 11))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15)))) ∧ (aluEval .sltu ((memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
      SvOkRet B out v n0 (BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32)) (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) (memLoad32 M0 (bp + 0x28)) (memLoad32 M0 (bp + 0x2C))) := by
  rcases sv_seg_sv F E0 V0 hret hO s0 M0 fM g0_2 g0_10 g0_11 g0_18 g0_19 g0_21 g0_22 g0_25 g0_26 g0_27 w0_2e0 w0_2e4 w0_2e8 w0_2ec lc_in D0 w0_a34 w0_a3c w0_a44 SD0 H' SH0 KS PE0 pkp_in apk pk_in side w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c ts_in he0p_in he0l_in ae0p ae0l e0_in he1p_in he1l_in ae1p ae1l e1_in he2p_in he2l_in ae2p ae2l e2_in he3p_in he3l_in ae3p ae3l e3_in he4p_in he4l_in ae4p ae4l e4_in htsp_in htsl_in atsp atsl EC0 IC0 UC0 BG0 RS BY0 dg_in UE0 N80 PM0 WM0 PT0 WN0 ME P2C0 GDC0 P2D0 SC0 hidC GD OD AD hzi c0_in hc0p_in hc0l_in ac0p ac0l D0' H'' S2 KS' pkp_in' apk' pk_in' side' w0_8 w0_c w0_10 w0_14 w0_18 w0_1c CK0 ckp_in4 ckl_in4 a_ckp a_ckl ck_in H''' KS'' kp_in4 kw_in4 a_kp a_kw kp_in EE0 hiv pk_in'' lid_in lih_in lil_in a_lih a_lil RK0 dgi_in pp_in4 pl_in4 a_pp a_pl pp_in ii2h ai2h ii2l ai2l ii3h ai3h ii3l ai3l it4h at4h it4l at4l it5h at5h it5l at5l with e | e | hx
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
  obtain ⟨tl29_2_1_1, hx⟩ := hx
  obtain ⟨h7, hx⟩ := hx
  obtain ⟨h8, hx⟩ := hx
  obtain ⟨te43_2_1_1, hx⟩ := hx
  obtain ⟨h9, hx⟩ := hx
  obtain ⟨h10, hx⟩ := hx
  obtain ⟨tl2_3_1_1, hx⟩ := hx
  obtain ⟨h11, hx⟩ := hx
  obtain ⟨ip2_3_1_1, hx⟩ := hx
  obtain ⟨il2_3_1_1, hx⟩ := hx
  obtain ⟨h12, hx⟩ := hx
  obtain ⟨h13, hx⟩ := hx
  obtain ⟨tl9_3_1_1, hx⟩ := hx
  obtain ⟨h14, hx⟩ := hx
  obtain ⟨op19_3_1_1, hx⟩ := hx
  obtain ⟨ol19_3_1_1, hx⟩ := hx
  obtain ⟨h15, hx⟩ := hx
  obtain ⟨h16, hx⟩ := hx
  obtain ⟨tl6_4_1_1, hx⟩ := hx
  obtain ⟨h17, hx⟩ := hx
  obtain ⟨tl13_4_1_1, hx⟩ := hx
  obtain ⟨h18, hx⟩ := hx
  obtain ⟨tm22_4_1_1, hx⟩ := hx
  obtain ⟨rs22_4_1_1, hx⟩ := hx
  obtain ⟨h19, hx⟩ := hx
  obtain ⟨tm31_4_1_1, hx⟩ := hx
  obtain ⟨rs31_4_1_1, hx⟩ := hx
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
  obtain ⟨tl25_6_1_1, hx⟩ := hx
  obtain ⟨h37, hx⟩ := hx
  obtain ⟨h38, hx⟩ := hx
  obtain ⟨u0_1, hx⟩ := hx
  obtain ⟨u1_1, hx⟩ := hx
  obtain ⟨u2_1, hx⟩ := hx
  obtain ⟨k_2_1, hx⟩ := hx
  obtain ⟨f30'_2_1, hx⟩ := hx
  obtain ⟨f34'_2_1, hx⟩ := hx
  obtain ⟨rem'_2_1, hx⟩ := hx
  obtain ⟨cur'_2_1, hx⟩ := hx
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
  obtain ⟨sr43_2_1, hx⟩ := hx
  obtain ⟨ss43_2_1, hx⟩ := hx
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
  obtain ⟨tl49_1_6_1, hx⟩ := hx
  obtain ⟨h65, hx⟩ := hx
  obtain ⟨h66, hx⟩ := hx
  obtain ⟨bs9_2_6_1, hx⟩ := hx
  obtain ⟨h67, hx⟩ := hx
  obtain ⟨te9_2_6_1, hx⟩ := hx
  obtain ⟨h68, hx⟩ := hx
  obtain ⟨bs16_2_6_1, hx⟩ := hx
  obtain ⟨h69, hx⟩ := hx
  obtain ⟨te16_2_6_1, hx⟩ := hx
  obtain ⟨h70, hx⟩ := hx
  obtain ⟨h71, hx⟩ := hx
  obtain ⟨h72, hx⟩ := hx
  obtain ⟨σd_2, hx⟩ := hx
  obtain ⟨σf_2, hx⟩ := hx
  obtain ⟨Dv_2, hx⟩ := hx
  obtain ⟨Fv_2, hx⟩ := hx
  obtain ⟨h73, hx⟩ := hx
  obtain ⟨h74, hx⟩ := hx
  obtain ⟨h75, hx⟩ := hx
  obtain ⟨h76, hx⟩ := hx
  obtain ⟨h77, hx⟩ := hx
  obtain ⟨stm_2, hx⟩ := hx
  obtain ⟨h78, hx⟩ := hx
  obtain ⟨τd_2, hx⟩ := hx
  obtain ⟨τf_2, hx⟩ := hx
  obtain ⟨Dz_2, hx⟩ := hx
  obtain ⟨Fz_2, hx⟩ := hx
  obtain ⟨h79, hx⟩ := hx
  obtain ⟨h80, hx⟩ := hx
  obtain ⟨h81, hx⟩ := hx
  obtain ⟨h82, hx⟩ := hx
  obtain ⟨h83, hx⟩ := hx
  obtain ⟨tl10_1_1_3, hx⟩ := hx
  obtain ⟨h84, hx⟩ := hx
  obtain ⟨h85, hx⟩ := hx
  obtain ⟨tl22_1_1_3, hx⟩ := hx
  obtain ⟨h86, hx⟩ := hx
  obtain ⟨h87, hx⟩ := hx
  obtain ⟨te33_1_1_3, hx⟩ := hx
  obtain ⟨h88, hx⟩ := hx
  obtain ⟨h89, hx⟩ := hx
  obtain ⟨tl41_1_1_3, hx⟩ := hx
  obtain ⟨h90, hx⟩ := hx
  obtain ⟨h91, hx⟩ := hx
  obtain ⟨op53_1_1_3, hx⟩ := hx
  obtain ⟨ol53_1_1_3, hx⟩ := hx
  obtain ⟨h92, hx⟩ := hx
  obtain ⟨to53_1_1_3, hx⟩ := hx
  obtain ⟨h93, hx⟩ := hx
  obtain ⟨h94, hx⟩ := hx
  obtain ⟨tl2_2_1_3, hx⟩ := hx
  obtain ⟨h95, hx⟩ := hx
  obtain ⟨h96, hx⟩ := hx
  obtain ⟨tl15_2_1_3, hx⟩ := hx
  obtain ⟨h97, hx⟩ := hx
  obtain ⟨h98, hx⟩ := hx
  obtain ⟨h99, hx⟩ := hx
  obtain ⟨te26_2_1_3, hx⟩ := hx
  obtain ⟨h100, hx⟩ := hx
  obtain ⟨tl32_2_1_3, hx⟩ := hx
  obtain ⟨h101, hx⟩ := hx
  obtain ⟨h102, hx⟩ := hx
  obtain ⟨te41_2_1_3, hx⟩ := hx
  obtain ⟨h103, hx⟩ := hx
  obtain ⟨h104, hx⟩ := hx
  obtain ⟨tl49_2_1_3, hx⟩ := hx
  obtain ⟨h105, hx⟩ := hx
  obtain ⟨op58_2_1_3, hx⟩ := hx
  obtain ⟨ol58_2_1_3, hx⟩ := hx
  obtain ⟨h106, hx⟩ := hx
  obtain ⟨to58_2_1_3, hx⟩ := hx
  obtain ⟨h107, hx⟩ := hx
  obtain ⟨h108, hx⟩ := hx
  obtain ⟨tl2_3_1_3, hx⟩ := hx
  obtain ⟨h109, hx⟩ := hx
  obtain ⟨h110, hx⟩ := hx
  obtain ⟨vp23_3_1_3, hx⟩ := hx
  obtain ⟨vl23_3_1_3, hx⟩ := hx
  obtain ⟨h111, hx⟩ := hx
  obtain ⟨te23_3_1_3, hx⟩ := hx
  obtain ⟨h112, hx⟩ := hx
  obtain ⟨h113, hx⟩ := hx
  obtain ⟨tsa4_w2a8_4_1_3, hx⟩ := hx
  obtain ⟨tsa4_w2ac_4_1_3, hx⟩ := hx
  obtain ⟨h114, hx⟩ := hx
  obtain ⟨h115, hx⟩ := hx
  obtain ⟨tl2_5_1_3, hx⟩ := hx
  obtain ⟨h116, hx⟩ := hx
  obtain ⟨h117, hx⟩ := hx
  obtain ⟨tl13_5_1_3, hx⟩ := hx
  obtain ⟨h118, hx⟩ := hx
  obtain ⟨h119, hx⟩ := hx
  obtain ⟨h120, hx⟩ := hx
  obtain ⟨te25_5_1_3, hx⟩ := hx
  obtain ⟨h121, hx⟩ := hx
  obtain ⟨tl31_5_1_3, hx⟩ := hx
  obtain ⟨h122, hx⟩ := hx
  obtain ⟨h123, hx⟩ := hx
  obtain ⟨te39_5_1_3, hx⟩ := hx
  obtain ⟨h124, hx⟩ := hx
  obtain ⟨tl45_5_1_3, hx⟩ := hx
  obtain ⟨h125, hx⟩ := hx
  obtain ⟨h126, hx⟩ := hx
  obtain ⟨h127, hx⟩ := hx
  obtain ⟨tl6_1_2_3, hx⟩ := hx
  obtain ⟨h128, hx⟩ := hx
  obtain ⟨op15_1_2_3, hx⟩ := hx
  obtain ⟨ol15_1_2_3, hx⟩ := hx
  obtain ⟨h129, hx⟩ := hx
  obtain ⟨to15_1_2_3, hx⟩ := hx
  obtain ⟨h130, hx⟩ := hx
  obtain ⟨tl20_1_2_3, hx⟩ := hx
  obtain ⟨h131, hx⟩ := hx
  obtain ⟨h132, hx⟩ := hx
  obtain ⟨h133, hx⟩ := hx
  obtain ⟨tsav_r24_2_2_3, hx⟩ := hx
  obtain ⟨tsav_w78_2_2_3, hx⟩ := hx
  obtain ⟨tsav_w1388_2_2_3, hx⟩ := hx
  obtain ⟨tsav_w138c_2_2_3, hx⟩ := hx
  obtain ⟨h134, hx⟩ := hx
  obtain ⟨h135, hx⟩ := hx
  obtain ⟨h136, hx⟩ := hx
  obtain ⟨u0, hx⟩ := hx
  obtain ⟨u1, hx⟩ := hx
  obtain ⟨u2, hx⟩ := hx
  obtain ⟨u3, hx⟩ := hx
  obtain ⟨u4, hx⟩ := hx
  obtain ⟨u5, hx⟩ := hx
  obtain ⟨u6, hx⟩ := hx
  obtain ⟨u7, hx⟩ := hx
  obtain ⟨u8, hx⟩ := hx
  obtain ⟨u9, hx⟩ := hx
  obtain ⟨u10, hx⟩ := hx
  obtain ⟨u11, hx⟩ := hx
  obtain ⟨u12, hx⟩ := hx
  obtain ⟨u13, hx⟩ := hx
  obtain ⟨u14, hx⟩ := hx
  obtain ⟨u15, hx⟩ := hx
  obtain ⟨u16, hx⟩ := hx
  obtain ⟨u17, hx⟩ := hx
  obtain ⟨u18, hx⟩ := hx
  obtain ⟨u19, hx⟩ := hx
  obtain ⟨u20, hx⟩ := hx
  obtain ⟨u21, hx⟩ := hx
  obtain ⟨u22, hx⟩ := hx
  obtain ⟨u23, hx⟩ := hx
  obtain ⟨u24, hx⟩ := hx
  obtain ⟨u25, hx⟩ := hx
  obtain ⟨u26, hx⟩ := hx
  obtain ⟨u27, hx⟩ := hx
  obtain ⟨u28, hx⟩ := hx
  obtain ⟨u29, hx⟩ := hx
  obtain ⟨u30, hx⟩ := hx
  obtain ⟨u31, hx⟩ := hx
  obtain ⟨k_3_3, hx⟩ := hx
  obtain ⟨dg'_3_3, hx⟩ := hx
  obtain ⟨flag'_3_3, hx⟩ := hx
  obtain ⟨cp'_3_3, hx⟩ := hx
  obtain ⟨rem'_3_3, hx⟩ := hx
  obtain ⟨h137, hx⟩ := hx
  obtain ⟨h138, hx⟩ := hx
  obtain ⟨h139, hx⟩ := hx
  obtain ⟨h140, hx⟩ := hx
  obtain ⟨op8_3_3, hx⟩ := hx
  obtain ⟨ol8_3_3, hx⟩ := hx
  obtain ⟨h141, hx⟩ := hx
  obtain ⟨te8_3_3, hx⟩ := hx
  obtain ⟨h142, hx⟩ := hx
  obtain ⟨h143, hx⟩ := hx
  obtain ⟨vp19_3_3, hx⟩ := hx
  obtain ⟨vl19_3_3, hx⟩ := hx
  obtain ⟨h144, hx⟩ := hx
  obtain ⟨te19_3_3, hx⟩ := hx
  obtain ⟨h145, hx⟩ := hx
  obtain ⟨sr24_3_3, hx⟩ := hx
  obtain ⟨ss24_3_3, hx⟩ := hx
  obtain ⟨h146, hx⟩ := hx
  obtain ⟨h147, hx⟩ := hx
  obtain ⟨tl13_1_4_3, hx⟩ := hx
  obtain ⟨h148, hx⟩ := hx
  obtain ⟨h149, hx⟩ := hx
  obtain ⟨h150, hx⟩ := hx
  obtain ⟨te26_1_4_3, hx⟩ := hx
  obtain ⟨h151, hx⟩ := hx
  obtain ⟨op32_1_4_3, hx⟩ := hx
  obtain ⟨ol32_1_4_3, hx⟩ := hx
  obtain ⟨h152, hx⟩ := hx
  obtain ⟨to32_1_4_3, hx⟩ := hx
  obtain ⟨h153, hx⟩ := hx
  obtain ⟨tl36_1_4_3, hx⟩ := hx
  obtain ⟨h154, hx⟩ := hx
  obtain ⟨h155, hx⟩ := hx
  obtain ⟨te45_1_4_3, hx⟩ := hx
  obtain ⟨h156, hx⟩ := hx
  obtain ⟨vp51_1_4_3, hx⟩ := hx
  obtain ⟨vl51_1_4_3, hx⟩ := hx
  obtain ⟨h157, hx⟩ := hx
  obtain ⟨te51_1_4_3, hx⟩ := hx
  obtain ⟨h158, hx⟩ := hx
  obtain ⟨h159, hx⟩ := hx
  obtain ⟨h160, hx⟩ := hx
  obtain ⟨tl2_2_4_3, hx⟩ := hx
  obtain ⟨h161, hx⟩ := hx
  obtain ⟨ip2_2_4_3, hx⟩ := hx
  obtain ⟨il2_2_4_3, hx⟩ := hx
  obtain ⟨h162, hx⟩ := hx
  obtain ⟨h163, hx⟩ := hx
  obtain ⟨tl13_2_4_3, hx⟩ := hx
  obtain ⟨h164, hx⟩ := hx
  obtain ⟨tm18_2_4_3, hx⟩ := hx
  obtain ⟨h165, hx⟩ := hx
  obtain ⟨tst3_w1328_3_4_3, hx⟩ := hx
  obtain ⟨tst3_w132c_3_4_3, hx⟩ := hx
  obtain ⟨h166, hx⟩ := hx
  obtain ⟨h167, hx⟩ := hx
  obtain ⟨tst4_r8_4_4_3, hx⟩ := hx
  obtain ⟨tst4_w1328_4_4_3, hx⟩ := hx
  obtain ⟨tst4_w132c_4_4_3, hx⟩ := hx
  obtain ⟨h168, hx⟩ := hx
  obtain ⟨h169, hx⟩ := hx
  obtain ⟨tst5_w1328_5_4_3, hx⟩ := hx
  obtain ⟨tst5_w132c_5_4_3, hx⟩ := hx
  obtain ⟨h170, hx⟩ := hx
  obtain ⟨h171, hx⟩ := hx
  obtain ⟨tst6_w1328_6_4_3, hx⟩ := hx
  obtain ⟨tst6_w132c_6_4_3, hx⟩ := hx
  obtain ⟨h172, hx⟩ := hx
  obtain ⟨h173, hx⟩ := hx
  obtain ⟨k_5_3, hx⟩ := hx
  obtain ⟨h174, hx⟩ := hx
  obtain ⟨h175, hx⟩ := hx
  obtain ⟨c'_5_3, hx⟩ := hx
  obtain ⟨q'_5_3, hx⟩ := hx
  obtain ⟨h176, hx⟩ := hx
  obtain ⟨h177, hx⟩ := hx
  obtain ⟨h178, hx⟩ := hx
  obtain ⟨h179, hx⟩ := hx
  obtain ⟨h180, hx⟩ := hx
  obtain ⟨h181, hx⟩ := hx
  obtain ⟨pv_7_3, hx⟩ := hx
  obtain ⟨h182, hx⟩ := hx
  obtain ⟨h183, hx⟩ := hx
  obtain ⟨ix7_1_1_4, hx⟩ := hx
  obtain ⟨h184, hx⟩ := hx
  obtain ⟨ix17_1_1_4, hx⟩ := hx
  obtain ⟨h185, hx⟩ := hx
  obtain ⟨ix25_1_1_4, hx⟩ := hx
  obtain ⟨h186, hx⟩ := hx
  obtain ⟨ix33_1_1_4, hx⟩ := hx
  obtain ⟨h187, hx⟩ := hx
  obtain ⟨h188, hx⟩ := hx
  obtain ⟨h189, hx⟩ := hx
  obtain ⟨h190, hx⟩ := hx
  obtain ⟨c'_2_4, hx⟩ := hx
  obtain ⟨p'_2_4, hx⟩ := hx
  obtain ⟨x21'_2_4, hx⟩ := hx
  obtain ⟨w60'_2_4, hx⟩ := hx
  obtain ⟨w70'_2_4, hx⟩ := hx
  obtain ⟨h191, hx⟩ := hx
  obtain ⟨h192, hx⟩ := hx
  obtain ⟨h193, hx⟩ := hx
  obtain ⟨bs7_2_4, hx⟩ := hx
  obtain ⟨h194, hx⟩ := hx
  obtain ⟨h195, hx⟩ := hx
  obtain ⟨k_3_4, hx⟩ := hx
  obtain ⟨h196, hx⟩ := hx
  obtain ⟨h197, hx⟩ := hx
  obtain ⟨c'_3_4, hx⟩ := hx
  obtain ⟨q'_3_4, hx⟩ := hx
  obtain ⟨w80'_3_4, hx⟩ := hx
  obtain ⟨h198, hx⟩ := hx
  obtain ⟨h199, hx⟩ := hx
  obtain ⟨h200, hx⟩ := hx
  obtain ⟨u32, hx⟩ := hx
  obtain ⟨u33, hx⟩ := hx
  obtain ⟨u34, hx⟩ := hx
  obtain ⟨u35, hx⟩ := hx
  obtain ⟨u36, hx⟩ := hx
  obtain ⟨u37, hx⟩ := hx
  obtain ⟨u38, hx⟩ := hx
  obtain ⟨u39, hx⟩ := hx
  obtain ⟨u40, hx⟩ := hx
  obtain ⟨u41, hx⟩ := hx
  obtain ⟨u42, hx⟩ := hx
  obtain ⟨u43, hx⟩ := hx
  obtain ⟨u44, hx⟩ := hx
  obtain ⟨u45, hx⟩ := hx
  obtain ⟨u46, hx⟩ := hx
  obtain ⟨u47, hx⟩ := hx
  obtain ⟨u48, hx⟩ := hx
  obtain ⟨u49, hx⟩ := hx
  obtain ⟨u50, hx⟩ := hx
  obtain ⟨u51, hx⟩ := hx
  obtain ⟨u52, hx⟩ := hx
  obtain ⟨u53, hx⟩ := hx
  obtain ⟨u54, hx⟩ := hx
  obtain ⟨u55, hx⟩ := hx
  obtain ⟨u56, hx⟩ := hx
  obtain ⟨u57, hx⟩ := hx
  obtain ⟨u58, hx⟩ := hx
  obtain ⟨u59, hx⟩ := hx
  obtain ⟨u60, hx⟩ := hx
  obtain ⟨sg_5_4, hx⟩ := hx
  obtain ⟨k_5_4, hx⟩ := hx
  obtain ⟨c'_5_4, hx⟩ := hx
  obtain ⟨x21'_5_4, hx⟩ := hx
  obtain ⟨rl'_5_4, hx⟩ := hx
  obtain ⟨rp'_5_4, hx⟩ := hx
  obtain ⟨dg'_5_4, hx⟩ := hx
  obtain ⟨w8'_5_4, hx⟩ := hx
  obtain ⟨wc'_5_4, hx⟩ := hx
  obtain ⟨w28'_5_4, hx⟩ := hx
  obtain ⟨w2c'_5_4, hx⟩ := hx
  obtain ⟨w30'_5_4, hx⟩ := hx
  obtain ⟨w38'_5_4, hx⟩ := hx
  obtain ⟨w40'_5_4, hx⟩ := hx
  obtain ⟨w5c'_5_4, hx⟩ := hx
  obtain ⟨sg'_5_4, hx⟩ := hx
  obtain ⟨h201, hx⟩ := hx
  obtain ⟨h202, hx⟩ := hx
  obtain ⟨h203, hx⟩ := hx
  obtain ⟨h204, hx⟩ := hx
  obtain ⟨h205, hx⟩ := hx
  obtain ⟨root6_3_6_4, hx⟩ := hx
  obtain ⟨h206, hx⟩ := hx
  obtain ⟨h207, hx⟩ := hx
  obtain ⟨h208, hx⟩ := hx
  obtain ⟨h209, hx⟩ := hx
  obtain ⟨h210, hx⟩ := hx
  obtain ⟨h211, hx⟩ := hx
  obtain ⟨h212, hx⟩ := hx
  obtain ⟨h213, hx⟩ := hx
  obtain ⟨h214, hx⟩ := hx
  obtain ⟨h215, hx⟩ := hx
  obtain ⟨n1, hx⟩ := hx
  obtain ⟨c1, hx⟩ := hx
  obtain ⟨fR1, hx⟩ := hx
  obtain ⟨s1, hx⟩ := hx
  obtain ⟨E1, hx⟩ := hx
  obtain ⟨V1, hx⟩ := hx
  obtain ⟨r1_3, hx⟩ := hx
  obtain ⟨r1_4, hx⟩ := hx
  obtain ⟨r1_2, hx⟩ := hx
  obtain ⟨r1_8, hx⟩ := hx
  obtain ⟨r1_9, hx⟩ := hx
  obtain ⟨r1_18, hx⟩ := hx
  obtain ⟨r1_19, hx⟩ := hx
  obtain ⟨r1_21, hx⟩ := hx
  obtain ⟨r1_22, hx⟩ := hx
  obtain ⟨r1_23, hx⟩ := hx
  obtain ⟨r1_24, hx⟩ := hx
  obtain ⟨r1_25, hx⟩ := hx
  obtain ⟨r1_26, hx⟩ := hx
  obtain ⟨r1_27, hx⟩ := hx
  obtain ⟨w1_8, hx⟩ := hx
  obtain ⟨w1_c, hx⟩ := hx
  obtain ⟨w1_14, hx⟩ := hx
  obtain ⟨w1_18, hx⟩ := hx
  obtain ⟨w1_1c, hx⟩ := hx
  obtain ⟨w1_20, hx⟩ := hx
  obtain ⟨w1_24, hx⟩ := hx
  obtain ⟨w1_28, hx⟩ := hx
  obtain ⟨w1_2c, hx⟩ := hx
  obtain ⟨w1_30, hx⟩ := hx
  obtain ⟨w1_34, hx⟩ := hx
  obtain ⟨w1_38, hx⟩ := hx
  obtain ⟨w1_3c, hx⟩ := hx
  obtain ⟨w1_40, hx⟩ := hx
  obtain ⟨w1_44, hx⟩ := hx
  obtain ⟨w1_48, hx⟩ := hx
  obtain ⟨w1_4c, hx⟩ := hx
  obtain ⟨w1_50, hx⟩ := hx
  obtain ⟨w1_54, hx⟩ := hx
  obtain ⟨w1_58, hx⟩ := hx
  obtain ⟨w1_5c, hx⟩ := hx
  obtain ⟨w1_60, hx⟩ := hx
  obtain ⟨w1_64, hx⟩ := hx
  obtain ⟨w1_68, hx⟩ := hx
  obtain ⟨w1_6c, hx⟩ := hx
  obtain ⟨w1_70, hx⟩ := hx
  obtain ⟨w1_74, hx⟩ := hx
  obtain ⟨w1_78, hx⟩ := hx
  obtain ⟨w1_7c, hx⟩ := hx
  obtain ⟨w1_80, hx⟩ := hx
  obtain ⟨w1_84, hx⟩ := hx
  obtain ⟨w1_88, hx⟩ := hx
  obtain ⟨w1_8c, hx⟩ := hx
  obtain ⟨w1_90, hx⟩ := hx
  obtain ⟨w1_94, hx⟩ := hx
  obtain ⟨w1_98, hx⟩ := hx
  obtain ⟨w1_9c, hx⟩ := hx
  obtain ⟨w1_a0, hx⟩ := hx
  obtain ⟨w1_a4, hx⟩ := hx
  obtain ⟨w1_a8, hx⟩ := hx
  obtain ⟨w1_ac, hx⟩ := hx
  obtain ⟨w1_b0, hx⟩ := hx
  obtain ⟨w1_b4, hx⟩ := hx
  obtain ⟨w1_b8, hx⟩ := hx
  obtain ⟨w1_bc, hx⟩ := hx
  obtain ⟨w1_c0, hx⟩ := hx
  obtain ⟨w1_c4, hx⟩ := hx
  obtain ⟨w1_c8, hx⟩ := hx
  obtain ⟨w1_cc, hx⟩ := hx
  obtain ⟨w1_130, hx⟩ := hx
  obtain ⟨w1_a20, hx⟩ := hx
  obtain ⟨w1_a24, hx⟩ := hx
  obtain ⟨w1_a28, hx⟩ := hx
  obtain ⟨w1_a2c, hx⟩ := hx
  obtain ⟨w1_a30, hx⟩ := hx
  obtain ⟨w1_a34, hx⟩ := hx
  obtain ⟨w1_a38, hx⟩ := hx
  obtain ⟨w1_a3c, hx⟩ := hx
  obtain ⟨w1_aa0, hx⟩ := hx
  obtain ⟨w1_aa4, hx⟩ := hx
  obtain ⟨w1_1028, hx⟩ := hx
  obtain ⟨w1_102c, hx⟩ := hx
  obtain ⟨w1_1030, hx⟩ := hx
  obtain ⟨w1_1034, hx⟩ := hx
  obtain ⟨b1_10, hx⟩ := hx
  obtain ⟨b1_1048, hx⟩ := hx
  obtain ⟨q1_320, hx⟩ := hx
  obtain ⟨q1_1049, hx⟩ := hx
  obtain ⟨w1_1020, hx⟩ := hx
  obtain ⟨w1_1038, hx⟩ := hx
  obtain ⟨w1_103c, hx⟩ := hx
  obtain ⟨w1_1040, hx⟩ := hx
  obtain ⟨w1_1044, hx⟩ := hx
  obtain ⟨b1_420, hx⟩ := hx
  obtain ⟨b1_421, hx⟩ := hx
  obtain ⟨b1_1480, hx⟩ := hx
  obtain ⟨w1_2e0, hx⟩ := hx
  obtain ⟨w1_2e4, hx⟩ := hx
  obtain ⟨w1_2e8, hx⟩ := hx
  obtain ⟨w1_2ec, hx⟩ := hx
  obtain ⟨w1_1588, hx⟩ := hx
  obtain ⟨w1_178, hx⟩ := hx
  obtain ⟨w1_17c, hx⟩ := hx
  obtain ⟨w1_180, hx⟩ := hx
  obtain ⟨w1_184, hx⟩ := hx
  obtain ⟨w1_204, hx⟩ := hx
  obtain ⟨w1_208, hx⟩ := hx
  obtain ⟨w1_20c, hx⟩ := hx
  obtain ⟨w1_2a8, hx⟩ := hx
  obtain ⟨w1_2ac, hx⟩ := hx
  obtain ⟨w1_1608, hx⟩ := hx
  obtain ⟨w1_160c, hx⟩ := hx
  obtain ⟨w1_1610, hx⟩ := hx
  obtain ⟨w1_1614, hx⟩ := hx
  obtain ⟨w1_1618, hx⟩ := hx
  obtain ⟨w1_161c, hx⟩ := hx
  obtain ⟨w1_1620, hx⟩ := hx
  obtain ⟨w1_1624, hx⟩ := hx
  obtain ⟨w1_1628, hx⟩ := hx
  obtain ⟨w1_162c, hx⟩ := hx
  obtain ⟨w1_1630, hx⟩ := hx
  obtain ⟨w1_1634, hx⟩ := hx
  obtain ⟨w1_1638, hx⟩ := hx
  obtain ⟨w1_163c, hx⟩ := hx
  obtain ⟨w1_1640, hx⟩ := hx
  obtain ⟨w1_1644, hx⟩ := hx
  obtain ⟨w1_2a0, hx⟩ := hx
  obtain ⟨w1_2a4, hx⟩ := hx
  obtain ⟨w1_2c0, hx⟩ := hx
  obtain ⟨w1_2c4, hx⟩ := hx
  obtain ⟨w1_2c8, hx⟩ := hx
  obtain ⟨w1_2cc, hx⟩ := hx
  obtain ⟨w1_1648, hx⟩ := hx
  obtain ⟨w1_164c, hx⟩ := hx
  obtain ⟨w1_1650, hx⟩ := hx
  obtain ⟨w1_1654, hx⟩ := hx
  obtain ⟨w1_158c, hx⟩ := hx
  obtain ⟨w1_1590, hx⟩ := hx
  obtain ⟨w1_1594, hx⟩ := hx
  obtain ⟨b1_a40, hx⟩ := hx
  have K1_L := hx
  exact .inr (.inr ⟨t_1_1_1, h0, h1, tl1_2_1_1, h2, tl8_2_1_1, h3, tl16_2_1_1, h4, bp16_2_1_1, bl16_2_1_1, h5, h6, tl29_2_1_1, h7, h8, te43_2_1_1, h9, h10, tl2_3_1_1, h11, ip2_3_1_1, il2_3_1_1, h12, h13, tl9_3_1_1, h14, op19_3_1_1, ol19_3_1_1, h15, h16, tl6_4_1_1, h17, tl13_4_1_1, h18, tm22_4_1_1, rs22_4_1_1, h19, tm31_4_1_1, rs31_4_1_1, h20, h21, tl2_5_1_1, h22, tl6_5_1_1, h23, op15_5_1_1, ol15_5_1_1, prp15_5_1_1, pu15_5_1_1, h24, ta15_5_1_1, h25, h26, h27, h28, tl35_5_1_1, h29, bp35_5_1_1, bl35_5_1_1, h30, h31, h32, h33, h34, tl9_6_1_1, h35, h36, tl25_6_1_1, h37, h38, u0_1, u1_1, u2_1, k_2_1, f30'_2_1, f34'_2_1, rem'_2_1, cur'_2_1, sl0'_2_1, sl1'_2_1, sl2'_2_1, sl3'_2_1, sl4'_2_1, sl5'_2_1, sl6'_2_1, sl7'_2_1, sl8'_2_1, sl9'_2_1, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, sr43_2_1, ss43_2_1, h52, k_4_1, h53, h54, c'_4_1, q'_4_1, h55, h56, h57, pv_5_1, h58, h59, h60, h61, h62, h63, h64, tl49_1_6_1, h65, h66, bs9_2_6_1, h67, te9_2_6_1, h68, bs16_2_6_1, h69, te16_2_6_1, h70, h71, h72, σd_2, σf_2, Dv_2, Fv_2, h73, h74, h75, h76, h77, stm_2, h78, τd_2, τf_2, Dz_2, Fz_2, h79, h80, h81, h82, h83, tl10_1_1_3, h84, h85, tl22_1_1_3, h86, h87, te33_1_1_3, h88, h89, tl41_1_1_3, h90, h91, op53_1_1_3, ol53_1_1_3, h92, to53_1_1_3, h93, h94, tl2_2_1_3, h95, h96, tl15_2_1_3, h97, h98, h99, te26_2_1_3, h100, tl32_2_1_3, h101, h102, te41_2_1_3, h103, h104, tl49_2_1_3, h105, op58_2_1_3, ol58_2_1_3, h106, to58_2_1_3, h107, h108, tl2_3_1_3, h109, h110, vp23_3_1_3, vl23_3_1_3, h111, te23_3_1_3, h112, h113, tsa4_w2a8_4_1_3, tsa4_w2ac_4_1_3, h114, h115, tl2_5_1_3, h116, h117, tl13_5_1_3, h118, h119, h120, te25_5_1_3, h121, tl31_5_1_3, h122, h123, te39_5_1_3, h124, tl45_5_1_3, h125, h126, h127, tl6_1_2_3, h128, op15_1_2_3, ol15_1_2_3, h129, to15_1_2_3, h130, tl20_1_2_3, h131, h132, h133, tsav_r24_2_2_3, tsav_w78_2_2_3, tsav_w1388_2_2_3, tsav_w138c_2_2_3, h134, h135, h136, u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15, u16, u17, u18, u19, u20, u21, u22, u23, u24, u25, u26, u27, u28, u29, u30, u31, k_3_3, dg'_3_3, flag'_3_3, cp'_3_3, rem'_3_3, h137, h138, h139, h140, op8_3_3, ol8_3_3, h141, te8_3_3, h142, h143, vp19_3_3, vl19_3_3, h144, te19_3_3, h145, sr24_3_3, ss24_3_3, h146, h147, tl13_1_4_3, h148, h149, h150, te26_1_4_3, h151, op32_1_4_3, ol32_1_4_3, h152, to32_1_4_3, h153, tl36_1_4_3, h154, h155, te45_1_4_3, h156, vp51_1_4_3, vl51_1_4_3, h157, te51_1_4_3, h158, h159, h160, tl2_2_4_3, h161, ip2_2_4_3, il2_2_4_3, h162, h163, tl13_2_4_3, h164, tm18_2_4_3, h165, tst3_w1328_3_4_3, tst3_w132c_3_4_3, h166, h167, tst4_r8_4_4_3, tst4_w1328_4_4_3, tst4_w132c_4_4_3, h168, h169, tst5_w1328_5_4_3, tst5_w132c_5_4_3, h170, h171, tst6_w1328_6_4_3, tst6_w132c_6_4_3, h172, h173, k_5_3, h174, h175, c'_5_3, q'_5_3, h176, h177, h178, h179, h180, h181, pv_7_3, h182, h183, ix7_1_1_4, h184, ix17_1_1_4, h185, ix25_1_1_4, h186, ix33_1_1_4, h187, h188, h189, h190, c'_2_4, p'_2_4, x21'_2_4, w60'_2_4, w70'_2_4, h191, h192, h193, bs7_2_4, h194, h195, k_3_4, h196, h197, c'_3_4, q'_3_4, w80'_3_4, h198, h199, h200, u32, u33, u34, u35, u36, u37, u38, u39, u40, u41, u42, u43, u44, u45, u46, u47, u48, u49, u50, u51, u52, u53, u54, u55, u56, u57, u58, u59, u60, sg_5_4, k_5_4, c'_5_4, x21'_5_4, rl'_5_4, rp'_5_4, dg'_5_4, w8'_5_4, wc'_5_4, w28'_5_4, w2c'_5_4, w30'_5_4, w38'_5_4, w40'_5_4, w5c'_5_4, sg'_5_4, h201, h202, h203, h204, h205, root6_3_6_4, h206, h207, h208, h209, h210, h211, h212, h213, h214, h215, sv_ok_3264 F E1 s1 c1 (fun x hx => (fR1 x hx).trans (fM x hx).symm) V1 hret r1_2 r1_18 hOk r1_3 r1_4 w1_3c w1_78 r1_25 r1_23⟩)

end C3.RV32.Sv
