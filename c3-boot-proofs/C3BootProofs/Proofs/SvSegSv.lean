import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvSegCert
import C3BootProofs.Proofs.SvP256St
import C3BootProofs.Proofs.SvSegTs
import C3BootProofs.Proofs.SvSegLog
import C3BootProofs.Image.BootloaderData6

/-!
# `sigstore::verify`: `sigstore::verify` to its successful exit

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Gd

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **`sigstore::verify` to its successful exit**: from 0x72 to 0x3264: the leaf certificate and its issuer, the P-256 check of the artifact's signature, the timestamp, and the transparency log entry. -/
theorem sv_seg_sv {B out bp rootp dg lp ll : Word} {v : Nat → Word} {n0 : Machine} {sl5 : Word} {sl7 : Word} {sl9 : Word} {wd0 : Word} {wd4 : Word} {wd8 : Word} {wdc : Word} {we0 : Word} {we4 : Word} {we8 : Word} {wec : Word} {wf0 : Word} {wf4 : Word} {wf8 : Word} {wfc : Word} {w100 : Word} {w104 : Word} {w108 : Word} {w10c : Word} {w110 : Word} {w114 : Word} {w118 : Word} {w11c : Word} {w120 : Word} {w124 : Word} {w128 : Word} {w12c : Word} {w8 : Word} {wc : Word} {w10 : Word} {w14 : Word} {w18 : Word} {w1c : Word}
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
        normVal8 τd_2 τf_2 Dz_2 (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) < p256)
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
    (hiv : (s5Hv M0 (BitVec.ofNat 32 (img% sha512IVAddress))).toList = Sha512.h0)
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
    (at5l : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (rootp + BitVec.ofNat 32 0x198)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x10).toNat % 4 = 0) :
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
      (memBytes M0 op19_3_1_1 ol19_3_1_1 = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x28)) 8) ∧
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
      (memBytes M0 (prp15_5_1_1 + BitVec.ofNat 32 pu15_5_1_1.header) pu15_5_1_1.len = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x30)) 8) ∧
      (memBytes M0 op15_5_1_1 ol15_5_1_1 = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xFC)) 7) ∧
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
      (((inScalarRange (b32 bs9_2_6_1) (memBytes M0 (BitVec.ofNat 32 (img% p256OrderBeAddress)) 32) = true) ∧ (inScalarRange (b32 bs16_2_6_1) (memBytes M0 (BitVec.ofNat 32 (img% p256OrderBeAddress)) 32) = true) ∧ (M0 bp35_5_1_1 = 4) ∧ True) ∧ ((GsOk M0 bp35_5_1_1) ∧ (beNat (b32 bs9_2_6_1) < C3.p256.n) ∧ (beNat (b32 bs16_2_6_1) < C3.p256.n) ∧ (beNat (b32 bs9_2_6_1) ≠ 0) ∧ (beNat (b32 bs16_2_6_1) ≠ 0) ∧ True)) ∧
      ∃ σd_2 σf_2 Dv_2 Fv_2, σd_2 ≤ 1 ∧ σf_2 ≤ 1 ∧ sgnVal σf_2 Fv_2 = (p256Sf M0 bs16_2_6_1).f ∧ sgnVal σd_2 Dv_2 = (p256Sf M0 bs16_2_6_1).d ∧
      (((Fv_2 = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8)) ∧ True) ∧ ∃ stm_2, mlMain2 (tbl2 (accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8, accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8, accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8)) (tbl2 ((gsVal M0 bp35_5_1_1 1 * 2 ^ 256 % p256), (gsVal M0 bp35_5_1_1 0x21 * 2 ^ 256 % p256), (accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8))) (wnafBytes (wnafGo ((psmVal (((beNat (memBytes M0 (dg) 32) % C3.p256.n)) * ((normVal8 σd_2 σf_2 Dv_2 (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0) 0x101) (wnafBytes (wnafGo ((psmVal (((beNat (b32 bs9_2_6_1))) * ((normVal8 σd_2 σf_2 Dv_2 (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0) 0x101) (max (wnafGo ((psmVal (((beNat (memBytes M0 (dg) 32) % C3.p256.n)) * ((normVal8 σd_2 σf_2 Dv_2 (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0).length (wnafGo ((psmVal (((beNat (b32 bs9_2_6_1))) * ((normVal8 σd_2 σf_2 Dv_2 (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0).length) = some stm_2 ∧
      ∃ τd_2 τf_2 Dz_2 Fz_2, τd_2 ≤ 1 ∧ τf_2 ≤ 1 ∧ sgnVal τf_2 Fz_2 = (p256Sz M0 stm_2.1.2.2).f ∧ sgnVal τd_2 Dz_2 = (p256Sz M0 stm_2.1.2.2).d ∧
      ((((beNat (b32 bs9_2_6_1)) = (p2fm ((if (((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm ((stm_2.1.1)) ((if ((((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 τd_2 τf_2 Dz_2 (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M0 (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1) % C3.p256.n)) ∧ True) ∧
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
      (memBytes M0 op53_1_1_3 ol53_1_1_3.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x41)) 9) ∧
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
      (memBytes M0 op58_2_1_3 ol58_2_1_3.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x4A)) 11) ∧
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
      ∃ tsav_r24_2_2_3 : Word, ∃ tsav_w78_2_2_3 : Word, ∃ tsav_w1388_2_2_3 : Word, ∃ tsav_w138c_2_2_3 : Word, (((memBytes M0 op15_1_2_3 ol15_1_2_3.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x56)) 9) ∧ ∃ op5 ol5, derContent ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) (derOid (memBytes M0 ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat)) = .ok (op5, ol5) ∧ ∃ to5, derOid (memBytes M0 ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat) = .ok to5 ∧ (memBytes M0 op5 ol5.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x4A)) 11) ∧ (((BitVec.ofNat 32 tl20_1_2_3.len)) - BitVec.ofNat 32 (to5.header + to5.len) = 0) ∧ tsav_r24_2_2_3 = (BitVec.ofNat 32 0x0) ∧ tsav_w78_2_2_3 = BitVec.ofNat 32 0x1 ∧ tsav_w1388_2_2_3 = ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) + BitVec.ofNat 32 (to5.header + to5.len) ∧ tsav_w138c_2_2_3 = ((BitVec.ofNat 32 tl20_1_2_3.len)) - BitVec.ofNat 32 (to5.header + to5.len)) ∨ ((¬ (memBytes M0 op15_1_2_3 ol15_1_2_3.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x56)) 9)) ∧ (memBytes M0 op15_1_2_3 ol15_1_2_3.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x5F)) 9) ∧ ∃ vp8 vl8, derContent ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) (derElement 4 (memBytes M0 ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat)) = .ok (vp8, vl8) ∧ ∃ te8, derElement 4 (memBytes M0 ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat) = .ok te8 ∧ (vl8 = 32) ∧ (((BitVec.ofNat 32 tl20_1_2_3.len)) - BitVec.ofNat 32 (te8.header + te8.len) = 0) ∧ tsav_r24_2_2_3 = vp8 ∧ tsav_w78_2_2_3 = (BitVec.ofNat 32 0x0) ∧ tsav_w1388_2_2_3 = ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) + BitVec.ofNat 32 (te8.header + te8.len) ∧ tsav_w138c_2_2_3 = ((BitVec.ofNat 32 tl20_1_2_3.len)) - BitVec.ofNat 32 (te8.header + te8.len)) ∨ ((¬ (memBytes M0 op15_1_2_3 ol15_1_2_3.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x56)) 9)) ∧ (¬ (memBytes M0 op15_1_2_3 ol15_1_2_3.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x5F)) 9)) ∧ tsav_r24_2_2_3 = (BitVec.ofNat 32 0x0) ∧ tsav_w78_2_2_3 = (BitVec.ofNat 32 0x0) ∧ tsav_w1388_2_2_3 = (((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header) ∧ tsav_w138c_2_2_3 = (BitVec.ofNat 32 tl20_1_2_3.len))) ∧ SvIn B tsav_w1388_2_2_3 tsav_w138c_2_2_3.toNat ∧ (tsav_r24_2_2_3 = 0 ∨ SvIn B tsav_r24_2_2_3 32) ∧
      ∃ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31, ∃ k_3_3 dg'_3_3 flag'_3_3 cp'_3_3 rem'_3_3, svChain (sv_attrStep B out bp vl23_3_1_3 ll (((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header) (BitVec.ofNat 32 tl45_5_1_3.len) (((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len)) (((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) - BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len)) (u0) (u1) (u2) (u3) (u4) (u5) (u6) (u7) ((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) (BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 % 2 ^ 32)) ((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) (BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len)) (memLoad32 M0 (bp + 0xC)) (memLoad32 M0 (bp + 0x8)) lp vp23_3_1_3 ((q'_4_1) + BitVec.ofNat 32 0x20) rootp dg (lp + BitVec.ofNat 32 t_1_1_1.header) (BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) (((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len)) (BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) sl0'_2_1 sl1'_2_1 sl2'_2_1 sl3'_2_1 sl4'_2_1 sl5'_2_1 sl6'_2_1 sl7'_2_1 sl8'_2_1 sl9'_2_1 (BitVec.ofNat 32 (tm22_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32)) (u8) (u9) (u10) (u11) (u12) (u13) (u14) (u15) (u16) (u17) (u18) (u19) (u20) (u21) (u22) (u23) (u24) (u25) (u26) (u27) (u28) (u29) (u30) (u31) bp35_5_1_1 v M0) k_3_3 (tsav_r24_2_2_3, tsav_w78_2_2_3, (((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 (tl6_1_2_3.header + tl6_1_2_3.len)), (((BitVec.ofNat 32 tl45_5_1_3.len)) - BitVec.ofNat 32 (tl6_1_2_3.header + tl6_1_2_3.len))) (dg'_3_3, flag'_3_3, cp'_3_3, rem'_3_3) ∧
      rem'_3_3 = 0 ∧ (dg'_3_3 = 0 ∨ SvIn B dg'_3_3 32) ∧
      (dg'_3_3 ≠ 0 ∧ flag'_3_3 = 1) ∧ ∃ op8_3_3 ol8_3_3, derAlgOf M0 ((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) (((((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) - BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))).toNat) = .ok ((op8_3_3, ol8_3_3), none) ∧ ∃ te8_3_3, derElement 0x30 (memBytes M0 ((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) ((((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) - BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))).toNat) = .ok te8_3_3 ∧ (memBytes M0 op8_3_3 ol8_3_3 = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress)) 8) ∧ ∃ vp19_3_3 vl19_3_3, derContent (((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) + BitVec.ofNat 32 (te8_3_3.header + te8_3_3.len)) (derElement 4 (memBytes M0 (((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) + BitVec.ofNat 32 (te8_3_3.header + te8_3_3.len)) (((((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) - BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) - BitVec.ofNat 32 (te8_3_3.header + te8_3_3.len)).toNat)) = .ok (vp19_3_3, vl19_3_3) ∧ ∃ te19_3_3, derElement 4 (memBytes M0 (((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) + BitVec.ofNat 32 (te8_3_3.header + te8_3_3.len)) (((((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) - BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) - BitVec.ofNat 32 (te8_3_3.header + te8_3_3.len)).toNat) = .ok te19_3_3 ∧ ∃ sr24_3_3 ss24_3_3, ecdsaSigOf 48 M0 (vp19_3_3) ((vl19_3_3).toNat) = .ok (sr24_3_3, ss24_3_3) ∧
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
      ∃ pv_7_3, SvPvRes M0 (memLoad32 M0 (((q'_5_3) + BitVec.ofNat 32 0x20) + 0x18)) (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 (sha256 (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x55)) (1) ++ memBytes M0 ((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len))) + BitVec.ofNat 32 0x1) ((((BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) + BitVec.ofNat 32 0xFFFFFFFF).toNat))) (B + 0x21A0 + BitVec.ofNat 32 0xA40) (B + 0x21A0 + BitVec.ofNat 32 0xA70) sr24_3_3 ss24_3_3 (some pv_7_3) ∧
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
      ∃ u32 u33 u34 u35 u36 u37 u38 u39 u40 u41 u42 u43 u44 u45 u46 u47 u48 u49 u50 u51 u52 u53 u54 u55 u56 u57 u58 u59 u60, ∃ sg_5_4, ∃ k_5_4 c'_5_4 x21'_5_4 rl'_5_4 rp'_5_4 dg'_5_4 w8'_5_4 wc'_5_4 w28'_5_4 w2c'_5_4 w30'_5_4 w38'_5_4 w40'_5_4 w5c'_5_4 sg'_5_4, svChain (sv_cosigStep vp51_1_4_3 B out bp ll ((q'_3_4) + BitVec.ofNat 32 0x20) bs7_2_4 (le4 (sha256 (memBytes M0 ((memLoad32 M0 (bp + 0x18))) (((BitVec.ofNat 32 ix7_1_1_4)).toNat) ++ memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x38)) (1) ++ memBytes M0 (BitVec.ofNat 32 (img% merklePrefixAddress)) (1) ++ memBytes M0 ((memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18))) (32))) 0) (memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x1C)) ((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 M0 (bp + 0x1C)))) (memLoad32 M0 (bp + 0x18)) (memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18)) (BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32)) (BitVec.ofNat 32 ix7_1_1_4) (memLoad32 M0 (bp + 0x18)) (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 % 2 ^ 32)) w60'_2_4 (memLoad32 M0 (bp + 0xC)) (memLoad32 M0 (bp + 0x8)) lp w70'_2_4 (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) ((q'_4_1) + BitVec.ofNat 32 0x20) (memLoad32 M0 (q'_3_4 + 0x20)) dg (lp + BitVec.ofNat 32 t_1_1_1.header) (BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) (((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len)) (BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) sl0'_2_1 sl1'_2_1 sl2'_2_1 sl3'_2_1 sl4'_2_1 sl5'_2_1 sl6'_2_1 sl7'_2_1 sl8'_2_1 sl9'_2_1 (BitVec.ofNat 32 (tm22_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32)) (u32) (u33) (u34) (u35) (u36) (u37) (u38) (u39) (u40) (u41) (u42) (u43) (u44) (u45) (u46) (u47) (u48) (u49) (u50) (u51) (u52) (u53) (u54) (u55) bp35_5_1_1 vp23_3_1_3 vl23_3_1_3 ((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) (BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) ((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) (BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len)) (BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32)) (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) dg'_3_3 v 0 0 0 M0) k_5_4 (((c'_3_4) + BitVec.ofNat 32 0xFFFFFFE0), x21'_2_4, (BitVec.ofNat 32 ix25_1_1_4), ((((memLoad32 M0 (bp + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)) + BitVec.ofNat 32 (ix17_1_1_4 + 1)), dg'_3_3, (u56), (u57), (u58), (u59), (BitVec.ofNat 32 0x0), ((((((memLoad32 M0 (bp + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)) + BitVec.ofNat 32 (ix17_1_1_4 + 1)) + BitVec.ofNat 32 (ix25_1_1_4 + 1)) + BitVec.ofNat 32 (ix33_1_1_4 + 1)), (u60), (BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1)), sg_5_4) (c'_5_4, x21'_5_4, rl'_5_4, rp'_5_4, dg'_5_4, w8'_5_4, wc'_5_4, w28'_5_4, w2c'_5_4, w30'_5_4, w38'_5_4, w40'_5_4, w5c'_5_4, sg'_5_4) ∧
      w5c'_5_4 = 0 ∧
      ((w30'_5_4) &&& BitVec.ofNat 32 0x1 ≠ 0) ∧ (evSpec (sigMem M0 (B + 0x21A0 + BitVec.ofNat 32 0x420) sg'_5_4) (memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18)) (B + 0x21A0 + BitVec.ofNat 32 0x420) (memLoad32 M0 (bp + 0x18)) (((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 M0 (bp + 0x1C))))).toNat = true) ∧
      ((((memLoad32 M0 (bp + 0x2C)) = w70'_2_4) ∧ (aluEval .sltu ((memLoad32 M0 (bp + 0x28))) (w60'_2_4) ≠ 0)) ∨ ((¬ ((memLoad32 M0 (bp + 0x2C)) = w70'_2_4)) ∧ (aluEval .sltu ((memLoad32 M0 (bp + 0x2C))) (w70'_2_4) ≠ 0))) ∧
      ∃ root6_3_6_4, rootFromInclusion (pair64 ((memLoad32 M0 (bp + 0x28))) ((memLoad32 M0 (bp + 0x2C)))) (pair64 (w60'_2_4) (w70'_2_4)) ((sha256 ([] ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes M0 (dg) (32)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B) ++ base64Encode (memBytes M0 ((memLoad32 M0 (bp + 0x8))) (((memLoad32 M0 (bp + 0xC))).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorMid2Address)) (0x54) ++ base64Encode (memBytes M0 (lp) ((ll).toNat)) ++ memBytes M0 (BitVec.ofNat 32 (img% svRekorPostAddress)) (0x7)))) (memBytes M0 ((memLoad32 M0 (bp + 0x10))) (((memLoad32 M0 (bp + 0x14))).toNat)) = some root6_3_6_4 ∧
      (b32 root6_3_6_4 = b32 bs7_2_4) ∧
      ((((BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((BitVec.ofNat 32 (tm22_4_1_1 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm31_4_1_1 % 2 ^ 32))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
      ((((memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE4))) = 0)) ∨ ((¬ ((memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0))) ∧ (aluEval .sltu ((memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFEC))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0)))) ∧ (aluEval .sltu ((memLoad32 M0 (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
      ((((memLoad32 M0 (((q'_5_3) + BitVec.ofNat 32 0x20) + 0xC)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((memLoad32 M0 (((q'_5_3) + BitVec.ofNat 32 0x20) + 0x8))) = 0)) ∨ ((¬ ((memLoad32 M0 (((q'_5_3) + BitVec.ofNat 32 0x20) + 0xC)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((memLoad32 M0 (((q'_5_3) + BitVec.ofNat 32 0x20) + 0xC))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 M0 (((q'_5_3) + BitVec.ofNat 32 0x20) + 0x14))) ∧ (aluEval .sltu ((memLoad32 M0 (((q'_5_3) + BitVec.ofNat 32 0x20) + 0x10))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 M0 (((q'_5_3) + BitVec.ofNat 32 0x20) + 0x14)))) ∧ (aluEval .sltu ((memLoad32 M0 (((q'_5_3) + BitVec.ofNat 32 0x20) + 0x14))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
      ((((memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 3))) = 0)) ∨ ((¬ ((memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15))) ∧ (aluEval .sltu ((memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 11))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15)))) ∧ (aluEval .sltu ((memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0x3264 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1048 ∧
        reg n' (9 : Fin 32) = ((BitVec.ofNat 8 (root6_3_6_4.getD 0 0)).zeroExtend 32) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (21 : Fin 32) = x21'_5_4 ∧
        reg n' (22 : Fin 32) = rl'_5_4 ∧
        reg n' (23 : Fin 32) = (memLoad32 M0 (bp + 0x2C)) ∧
        reg n' (24 : Fin 32) = dg'_5_4 ∧
        reg n' (25 : Fin 32) = (memLoad32 M0 (bp + 0x28)) ∧
        reg n' (26 : Fin 32) = ll ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8) = w8'_5_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC) = wc'_5_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x14) = (le4 (sha256 (memBytes M0 ((memLoad32 M0 (bp + 0x18))) (((BitVec.ofNat 32 ix7_1_1_4)).toNat) ++ memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x38)) (1) ++ memBytes M0 (BitVec.ofNat 32 (img% merklePrefixAddress)) (1) ++ memBytes M0 ((memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18))) (32))) 0) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = (memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x1C)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (BitVec.ofNat 8 (bs7_2_4.getD 0 0)).zeroExtend 32 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = ((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 M0 (bp + 0x1C)))) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (memLoad32 M0 (bp + 0x18)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28'_5_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = ((w30'_5_4) &&& BitVec.ofNat 32 0x1) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30'_5_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = (memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38'_5_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = (BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40'_5_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (BitVec.ofNat 32 ix7_1_1_4) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = (memLoad32 M0 (bp + 0x18)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = (BitVec.ofNat 32 (tm31_4_1_1 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = (BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = (BitVec.ofNat 32 (tm22_4_1_1 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c'_5_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60'_2_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = (memLoad32 M0 (bp + 0xC)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = (memLoad32 M0 (bp + 0x8)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70'_2_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ((q'_5_3) + BitVec.ofNat 32 0x20) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = ((q'_4_1) + BitVec.ofNat 32 0x20) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (memLoad32 M0 (q'_3_4 + 0x20)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (lp + BitVec.ofNat 32 t_1_1_1.header) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = (((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = (BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl0'_2_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl1'_2_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl2'_2_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl3'_2_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = sl4'_2_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = sl5'_2_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = sl6'_2_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = sl7'_2_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = sl8'_2_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = sl9'_2_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = (BitVec.ofNat 32 (tm22_4_1_1 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = (BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = (BitVec.ofNat 32 (tm31_4_1_1 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = bp35_5_1_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = vp23_3_1_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = vl23_3_1_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = ((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = (BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = ((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = (BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = (BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = vp51_1_4_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA4) = dg'_3_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1028) = (memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 3)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x102C) = (memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1030) = (memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 11)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1034) = (memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15)) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10) = BitVec.ofNat 8 (sg'_5_4.getD 0 0) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1048) = ((BitVec.ofNat 8 (bs7_2_4.getD 0 0)).zeroExtend 32).extractLsb' 0 8 ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x320 + j)) = BitVec.ofNat 8 (bs7_2_4.getD (1 + j) 0)) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1049 + j)) = BitVec.ofNat 8 (bs7_2_4.getD (1 + j) 0)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) = (memLoad32 M0 (q'_3_4 + 0x20)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1038) = (memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x103C) = (memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x1C)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1040) = w60'_2_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1044) = w70'_2_4 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 (root6_3_6_4.getD 0 0) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1480) = BitVec.ofNat 8 (root6_3_6_4.getD 0 0) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = (((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 tl49_2_1_3.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = BitVec.ofNat 32 tl49_2_1_3.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = ((((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 tl49_2_1_3.header) + BitVec.ofNat 32 (to58_2_1_3.header + to58_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = (((BitVec.ofNat 32 tl49_2_1_3.len) - BitVec.ofNat 32 (to58_2_1_3.header + to58_2_1_3.len))) - BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) = ((((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 tl49_2_1_3.header) + BitVec.ofNat 32 (to58_2_1_3.header + to58_2_1_3.len))) + BitVec.ofNat 32 tl2_3_1_3.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = (tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl2_5_1_3.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 (tl13_5_1_3.header + tl13_5_1_3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 tl2_5_1_3.len) - BitVec.ofNat 32 (tl13_5_1_3.header + tl13_5_1_3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x204) = BitVec.ofNat 32 tl13_5_1_3.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = ((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) + BitVec.ofNat 32 (te8_3_3.header + te8_3_3.len)) + BitVec.ofNat 32 (te19_3_3.header + te19_3_3.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20C) = ((((((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) - BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) - BitVec.ofNat 32 (te8_3_3.header + te8_3_3.len)) - BitVec.ofNat 32 (te19_3_3.header + te19_3_3.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A8) = (tsa4_w2a8_4_1_3) + BitVec.ofNat 32 (tl2_5_1_3.header + tl2_5_1_3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2AC) = (tsa4_w2ac_4_1_3) - BitVec.ofNat 32 (tl2_5_1_3.header + tl2_5_1_3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1608) = (memLoad32 M0 (bp + 0x20)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x160C) = (memLoad32 M0 (bp + 0x24)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1610) = ((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 (tl10_1_1_3.header + tl10_1_1_3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1614) = ((memLoad32 M0 (bp + 0x24))) - BitVec.ofNat 32 (tl10_1_1_3.header + tl10_1_1_3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1618) = ((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x161C) = BitVec.ofNat 32 tl10_1_1_3.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1620) = ((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 (tl41_1_1_3.header + tl41_1_1_3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1624) = ((BitVec.ofNat 32 tl10_1_1_3.len) - BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) - BitVec.ofNat 32 (tl41_1_1_3.header + tl41_1_1_3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1628) = (((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 tl22_1_1_3.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x162C) = BitVec.ofNat 32 tl22_1_1_3.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1630) = ((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 tl22_1_1_3.header) + BitVec.ofNat 32 (te33_1_1_3.header + te33_1_1_3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1634) = (BitVec.ofNat 32 tl22_1_1_3.len) - BitVec.ofNat 32 (te33_1_1_3.header + te33_1_1_3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1638) = ((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x163C) = BitVec.ofNat 32 tl41_1_1_3.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1640) = (((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 (tl2_2_1_3.header + tl2_2_1_3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1644) = (((BitVec.ofNat 32 tl41_1_1_3.len) - BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) - BitVec.ofNat 32 (tl2_2_1_3.header + tl2_2_1_3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A0) = ((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2A4) = BitVec.ofNat 32 tl15_2_1_3.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C0) = ((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 tl32_2_1_3.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C4) = BitVec.ofNat 32 tl32_2_1_3.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C8) = (((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te41_2_1_3.header + te41_2_1_3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2CC) = (BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te41_2_1_3.header + te41_2_1_3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1648) = (((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x164C) = BitVec.ofNat 32 tl2_2_1_3.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1650) = ((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (tl15_2_1_3.header + tl15_2_1_3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1654) = (BitVec.ofNat 32 tl2_2_1_3.len) - BitVec.ofNat 32 (tl15_2_1_3.header + tl15_2_1_3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158C) = BitVec.ofNat 32 tl2_3_1_3.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1590) = (((((((((((((((memLoad32 M0 (bp + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 tl49_2_1_3.header) + BitVec.ofNat 32 (to58_2_1_3.header + to58_2_1_3.len))) + BitVec.ofNat 32 tl2_3_1_3.header) + BitVec.ofNat 32 (te23_3_1_3.header + te23_3_1_3.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1594) = (BitVec.ofNat 32 tl2_3_1_3.len) - BitVec.ofNat 32 (te23_3_1_3.header + te23_3_1_3.len) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (sr24_3_3.getD 0 0) ∧
        SvKeepL B n0.mem n'.mem [(0xA20, 0x10), (0x2E8, 0x8), (0x158D, 0xB), (0x1588, 0x4), (0x158C, 0x1), (0xA20, 0x11), (0x1590, 0x8), (0xA20, 0x11), (0x1590, 0x8), (0x80, 0x4), (0x84, 0x4), (0xA20, 0x8), (0x1590, 0x8), (0x7C, 0x4), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0xA20, 0x18), (0x180, 0x8), (0x78, 0x4), (0x200, 0x4), (0x204, 0x4), (0x208, 0x4), (0x20C, 0x4), (0x208, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4), (0x68, 0x4), (0x64, 0x4), (0x60, 0x4), (0x6C, 0x4), (0x5C, 0x4), (0x245, 0xB), (0x240, 0x4), (0x244, 0x1), (0x248, 0x8), (0x58, 0x4), (0x54, 0x4), (0x248, 0x8), (0x50, 0x4), (0x4C, 0x4), (0x1025, 0xB), (0x1024, 0x1), (0xA20, 0x48), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1328, 0x8), (0x88, 0x4), (0x8C, 0x4), (0x90, 0x4), (0x40, 0x4), (0x94, 0x4), (0xA20, 0x4), (0xA28, 0x4), (0xA30, 0x4), (0xA38, 0x4), (0xA40, 0x4), (0x34, 0x4), (0x30, 0x4), (0x1020, 0x10), (0x90, 0x8), (0x44, 0x4), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x1020, 0x8), (0x328, 0x8), (0x48, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0x1380, 0x4), (0x1384, 0x4), (0x1388, 0x4), (0x138C, 0x4), (0x1388, 0x8), (0x1485, 0xB), (0x1484, 0x1), (0xA24, 0x4), (0xA2C, 0x4), (0xA34, 0x4), (0xA3C, 0x4), (0xA44, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4), (0xA20, 0x61), (0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1), (0xD1, 0x5F), (0x8C, 0x1), (0xC0, 0x4), (0xC4, 0x4), (0xC8, 0x4), (0xCC, 0x4), (0x130, 0x4), (0x74, 0x8), (0x420, 0xD0), (0xA20, 0xD0), (0x1020, 0x40), (0x1480, 0x30), (0xA20, 0x21), (0x1020, 0x1F), (0xA20, 0x21), (0x420, 0x1F), (0x1480, 0x1F), (0x1380, 0x1F), (0x139, 0x1F), (0x159, 0x1F), (0x138, 0x1), (0x158, 0x1), (0x0, 0x1690), (0x1608, 0x4), (0x160C, 0x4), (0x1610, 0x4), (0x1614, 0x4), (0x420, 0x10), (0x1610, 0x8), (0x161D, 0xB), (0x1618, 0x4), (0x161C, 0x1), (0x420, 0x10), (0x1620, 0x8), (0x162D, 0xB), (0x1628, 0x4), (0x162C, 0x1), (0x1630, 0x8), (0x420, 0x10), (0x1620, 0x8), (0x163D, 0xB), (0x1638, 0x4), (0x163C, 0x1), (0x420, 0x8), (0x1640, 0x8), (0x164D, 0xB), (0x1648, 0x4), (0x164C, 0x1), (0x1650, 0x8), (0x2A5, 0xB), (0x2A0, 0x4), (0x2A4, 0x1), (0x2A8, 0x8), (0x2A8, 0x8), (0x2C5, 0xB), (0x2C0, 0x4), (0x2C4, 0x1), (0x2C8, 0x8), (0x2A8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x18), (0x158D, 0x1), (0x158E, 0x1), (0x158F, 0x1), (0x1590, 0x4), (0x1594, 0x4), (0x17D, 0xB), (0x17C, 0x1), (0x205, 0xB), (0x204, 0x1), (0x420, 0x11), (0x1385, 0xB), (0x1384, 0x1), (0x420, 0x1C), (0x1380, 0x8), (0x420, 0x61), (0x1020, 0x5F), (0x244, 0x4), (0x248, 0x4), (0x24C, 0x4), (0x1325, 0xB), (0x1324, 0x1), (0x1380, 0x10), (0x1480, 0x5F), (0xA25, 0x1), (0xA26, 0x1), (0xA27, 0x1), (0xA40, 0x1), (0xA41, 0x5F), (0xAA0, 0x4), (0xAA4, 0x4), (0xA24, 0x1), (0x420, 0x20), (0x420, 0x20), (0x420, 0x20), (0x20, 0x4), (0x420, 0x60), (0x1C, 0x4), (0x320, 0x1F), (0x18, 0x4), (0x420, 0x4), (0x424, 0x4), (0x428, 0x4), (0x42C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x438, 0x4), (0x43C, 0x4), (0x1380, 0x20), (0x14, 0x4), (0xC, 0x4), (0x8, 0x4), (0x200, 0x3), (0x10, 0x4), (0x1480, 0x3F), (0x421, 0x3F), (0x420, 0x1), (0x240, 0x13), (0x1320, 0x1F), (0x1025, 0x13), (0x1038, 0x4), (0x103C, 0x4), (0x1048, 0x1), (0x1049, 0x1F), (0x1040, 0x4), (0x1044, 0x4), (0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x21), (0x1481, 0x1F), (0x1480, 0x1)]) := by
  rcases sv_seg_cert F E0 V0 hret hO s0 M0 fM g0_2 g0_10 g0_11 g0_18 g0_19 g0_21 g0_22 g0_25 g0_26 g0_27 w0_2e0 w0_2e4 w0_2e8 w0_2ec lc_in D0 w0_a34 w0_a3c w0_a44 SD0 H' SH0 KS PE0 pkp_in apk pk_in side w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c ts_in he0p_in he0l_in ae0p ae0l e0_in he1p_in he1l_in ae1p ae1l e1_in he2p_in he2l_in ae2p ae2l e2_in he3p_in he3l_in ae3p ae3l e3_in he4p_in he4l_in ae4p ae4l e4_in htsp_in htsl_in atsp atsl with e | e | hx1
  · exact .inl e
  · exact .inr (.inl e)
  obtain ⟨t_1_1_1, hx1⟩ := hx1
  obtain ⟨x1_0, hx1⟩ := hx1
  obtain ⟨x1_1, hx1⟩ := hx1
  obtain ⟨tl1_2_1_1, hx1⟩ := hx1
  obtain ⟨x1_2, hx1⟩ := hx1
  obtain ⟨tl8_2_1_1, hx1⟩ := hx1
  obtain ⟨x1_3, hx1⟩ := hx1
  obtain ⟨tl16_2_1_1, hx1⟩ := hx1
  obtain ⟨x1_4, hx1⟩ := hx1
  obtain ⟨bp16_2_1_1, hx1⟩ := hx1
  obtain ⟨bl16_2_1_1, hx1⟩ := hx1
  obtain ⟨x1_5, hx1⟩ := hx1
  obtain ⟨x1_6, hx1⟩ := hx1
  obtain ⟨tl29_2_1_1, hx1⟩ := hx1
  obtain ⟨x1_7, hx1⟩ := hx1
  obtain ⟨x1_8, hx1⟩ := hx1
  obtain ⟨te43_2_1_1, hx1⟩ := hx1
  obtain ⟨x1_9, hx1⟩ := hx1
  obtain ⟨x1_10, hx1⟩ := hx1
  obtain ⟨tl2_3_1_1, hx1⟩ := hx1
  obtain ⟨x1_11, hx1⟩ := hx1
  obtain ⟨ip2_3_1_1, hx1⟩ := hx1
  obtain ⟨il2_3_1_1, hx1⟩ := hx1
  obtain ⟨x1_12, hx1⟩ := hx1
  obtain ⟨x1_13, hx1⟩ := hx1
  obtain ⟨tl9_3_1_1, hx1⟩ := hx1
  obtain ⟨x1_14, hx1⟩ := hx1
  obtain ⟨op19_3_1_1, hx1⟩ := hx1
  obtain ⟨ol19_3_1_1, hx1⟩ := hx1
  obtain ⟨x1_15, hx1⟩ := hx1
  obtain ⟨x1_16, hx1⟩ := hx1
  obtain ⟨tl6_4_1_1, hx1⟩ := hx1
  obtain ⟨x1_17, hx1⟩ := hx1
  obtain ⟨tl13_4_1_1, hx1⟩ := hx1
  obtain ⟨x1_18, hx1⟩ := hx1
  obtain ⟨tm22_4_1_1, hx1⟩ := hx1
  obtain ⟨rs22_4_1_1, hx1⟩ := hx1
  obtain ⟨x1_19, hx1⟩ := hx1
  obtain ⟨tm31_4_1_1, hx1⟩ := hx1
  obtain ⟨rs31_4_1_1, hx1⟩ := hx1
  obtain ⟨x1_20, hx1⟩ := hx1
  obtain ⟨x1_21, hx1⟩ := hx1
  obtain ⟨tl2_5_1_1, hx1⟩ := hx1
  obtain ⟨x1_22, hx1⟩ := hx1
  obtain ⟨tl6_5_1_1, hx1⟩ := hx1
  obtain ⟨x1_23, hx1⟩ := hx1
  obtain ⟨op15_5_1_1, hx1⟩ := hx1
  obtain ⟨ol15_5_1_1, hx1⟩ := hx1
  obtain ⟨prp15_5_1_1, hx1⟩ := hx1
  obtain ⟨pu15_5_1_1, hx1⟩ := hx1
  obtain ⟨x1_24, hx1⟩ := hx1
  obtain ⟨ta15_5_1_1, hx1⟩ := hx1
  obtain ⟨x1_25, hx1⟩ := hx1
  obtain ⟨x1_26, hx1⟩ := hx1
  obtain ⟨x1_27, hx1⟩ := hx1
  obtain ⟨x1_28, hx1⟩ := hx1
  obtain ⟨tl35_5_1_1, hx1⟩ := hx1
  obtain ⟨x1_29, hx1⟩ := hx1
  obtain ⟨bp35_5_1_1, hx1⟩ := hx1
  obtain ⟨bl35_5_1_1, hx1⟩ := hx1
  obtain ⟨x1_30, hx1⟩ := hx1
  obtain ⟨x1_31, hx1⟩ := hx1
  obtain ⟨x1_32, hx1⟩ := hx1
  obtain ⟨x1_33, hx1⟩ := hx1
  obtain ⟨x1_34, hx1⟩ := hx1
  obtain ⟨tl9_6_1_1, hx1⟩ := hx1
  obtain ⟨x1_35, hx1⟩ := hx1
  obtain ⟨x1_36, hx1⟩ := hx1
  obtain ⟨tl25_6_1_1, hx1⟩ := hx1
  obtain ⟨x1_37, hx1⟩ := hx1
  obtain ⟨x1_38, hx1⟩ := hx1
  obtain ⟨u0_1, hx1⟩ := hx1
  obtain ⟨u1_1, hx1⟩ := hx1
  obtain ⟨u2_1, hx1⟩ := hx1
  obtain ⟨k_2_1, hx1⟩ := hx1
  obtain ⟨f30'_2_1, hx1⟩ := hx1
  obtain ⟨f34'_2_1, hx1⟩ := hx1
  obtain ⟨rem'_2_1, hx1⟩ := hx1
  obtain ⟨cur'_2_1, hx1⟩ := hx1
  obtain ⟨sl0'_2_1, hx1⟩ := hx1
  obtain ⟨sl1'_2_1, hx1⟩ := hx1
  obtain ⟨sl2'_2_1, hx1⟩ := hx1
  obtain ⟨sl3'_2_1, hx1⟩ := hx1
  obtain ⟨sl4'_2_1, hx1⟩ := hx1
  obtain ⟨sl5'_2_1, hx1⟩ := hx1
  obtain ⟨sl6'_2_1, hx1⟩ := hx1
  obtain ⟨sl7'_2_1, hx1⟩ := hx1
  obtain ⟨sl8'_2_1, hx1⟩ := hx1
  obtain ⟨sl9'_2_1, hx1⟩ := hx1
  obtain ⟨x1_39, hx1⟩ := hx1
  obtain ⟨x1_40, hx1⟩ := hx1
  obtain ⟨x1_41, hx1⟩ := hx1
  obtain ⟨x1_42, hx1⟩ := hx1
  obtain ⟨x1_43, hx1⟩ := hx1
  obtain ⟨x1_44, hx1⟩ := hx1
  obtain ⟨x1_45, hx1⟩ := hx1
  obtain ⟨x1_46, hx1⟩ := hx1
  obtain ⟨x1_47, hx1⟩ := hx1
  obtain ⟨x1_48, hx1⟩ := hx1
  obtain ⟨x1_49, hx1⟩ := hx1
  obtain ⟨x1_50, hx1⟩ := hx1
  obtain ⟨x1_51, hx1⟩ := hx1
  obtain ⟨sr43_2_1, hx1⟩ := hx1
  obtain ⟨ss43_2_1, hx1⟩ := hx1
  obtain ⟨x1_52, hx1⟩ := hx1
  obtain ⟨k_4_1, hx1⟩ := hx1
  obtain ⟨x1_53, hx1⟩ := hx1
  obtain ⟨x1_54, hx1⟩ := hx1
  obtain ⟨c'_4_1, hx1⟩ := hx1
  obtain ⟨q'_4_1, hx1⟩ := hx1
  obtain ⟨x1_55, hx1⟩ := hx1
  obtain ⟨x1_56, hx1⟩ := hx1
  obtain ⟨x1_57, hx1⟩ := hx1
  obtain ⟨pv_5_1, hx1⟩ := hx1
  obtain ⟨x1_58, hx1⟩ := hx1
  obtain ⟨x1_59, hx1⟩ := hx1
  obtain ⟨x1_60, hx1⟩ := hx1
  obtain ⟨x1_61, hx1⟩ := hx1
  obtain ⟨x1_62, hx1⟩ := hx1
  obtain ⟨x1_63, hx1⟩ := hx1
  obtain ⟨x1_64, hx1⟩ := hx1
  obtain ⟨tl49_1_6_1, hx1⟩ := hx1
  obtain ⟨x1_65, hx1⟩ := hx1
  obtain ⟨x1_66, hx1⟩ := hx1
  obtain ⟨bs9_2_6_1, hx1⟩ := hx1
  obtain ⟨x1_67, hx1⟩ := hx1
  obtain ⟨te9_2_6_1, hx1⟩ := hx1
  obtain ⟨x1_68, hx1⟩ := hx1
  obtain ⟨bs16_2_6_1, hx1⟩ := hx1
  obtain ⟨x1_69, hx1⟩ := hx1
  obtain ⟨te16_2_6_1, hx1⟩ := hx1
  obtain ⟨x1_70, hx1⟩ := hx1
  obtain ⟨x1_71, hx1⟩ := hx1
  obtain ⟨n1, hx1⟩ := hx1
  obtain ⟨c1, hx1⟩ := hx1
  obtain ⟨fR1, hx1⟩ := hx1
  obtain ⟨s1, hx1⟩ := hx1
  obtain ⟨E1, hx1⟩ := hx1
  obtain ⟨V1, hx1⟩ := hx1
  obtain ⟨r1_3, hx1⟩ := hx1
  obtain ⟨r1_4, hx1⟩ := hx1
  obtain ⟨r1_2, hx1⟩ := hx1
  obtain ⟨r1_8, hx1⟩ := hx1
  obtain ⟨r1_9, hx1⟩ := hx1
  obtain ⟨r1_18, hx1⟩ := hx1
  obtain ⟨r1_19, hx1⟩ := hx1
  obtain ⟨r1_20, hx1⟩ := hx1
  obtain ⟨r1_21, hx1⟩ := hx1
  obtain ⟨r1_22, hx1⟩ := hx1
  obtain ⟨r1_26, hx1⟩ := hx1
  obtain ⟨r1_27, hx1⟩ := hx1
  obtain ⟨w1_24, hx1⟩ := hx1
  obtain ⟨w1_28, hx1⟩ := hx1
  obtain ⟨w1_2c, hx1⟩ := hx1
  obtain ⟨w1_30, hx1⟩ := hx1
  obtain ⟨w1_34, hx1⟩ := hx1
  obtain ⟨w1_38, hx1⟩ := hx1
  obtain ⟨w1_3c, hx1⟩ := hx1
  obtain ⟨w1_40, hx1⟩ := hx1
  obtain ⟨w1_44, hx1⟩ := hx1
  obtain ⟨w1_48, hx1⟩ := hx1
  obtain ⟨w1_4c, hx1⟩ := hx1
  obtain ⟨w1_50, hx1⟩ := hx1
  obtain ⟨w1_54, hx1⟩ := hx1
  obtain ⟨w1_58, hx1⟩ := hx1
  obtain ⟨w1_5c, hx1⟩ := hx1
  obtain ⟨w1_60, hx1⟩ := hx1
  obtain ⟨w1_64, hx1⟩ := hx1
  obtain ⟨w1_68, hx1⟩ := hx1
  obtain ⟨w1_6c, hx1⟩ := hx1
  obtain ⟨w1_70, hx1⟩ := hx1
  obtain ⟨w1_7c, hx1⟩ := hx1
  obtain ⟨w1_80, hx1⟩ := hx1
  obtain ⟨w1_84, hx1⟩ := hx1
  obtain ⟨w1_88, hx1⟩ := hx1
  obtain ⟨w1_8c, hx1⟩ := hx1
  obtain ⟨w1_90, hx1⟩ := hx1
  obtain ⟨w1_94, hx1⟩ := hx1
  obtain ⟨w1_98, hx1⟩ := hx1
  obtain ⟨w1_9c, hx1⟩ := hx1
  obtain ⟨w1_a0, hx1⟩ := hx1
  obtain ⟨w1_a4, hx1⟩ := hx1
  obtain ⟨w1_a8, hx1⟩ := hx1
  obtain ⟨w1_ac, hx1⟩ := hx1
  obtain ⟨w1_b0, hx1⟩ := hx1
  obtain ⟨w1_b4, hx1⟩ := hx1
  obtain ⟨w1_b8, hx1⟩ := hx1
  obtain ⟨w1_bc, hx1⟩ := hx1
  obtain ⟨w1_c0, hx1⟩ := hx1
  obtain ⟨w1_c4, hx1⟩ := hx1
  obtain ⟨w1_c8, hx1⟩ := hx1
  obtain ⟨w1_cc, hx1⟩ := hx1
  obtain ⟨w1_130, hx1⟩ := hx1
  obtain ⟨w1_320, hx1⟩ := hx1
  obtain ⟨w1_324, hx1⟩ := hx1
  obtain ⟨w1_328, hx1⟩ := hx1
  obtain ⟨w1_32c, hx1⟩ := hx1
  obtain ⟨w1_1320, hx1⟩ := hx1
  obtain ⟨w1_1324, hx1⟩ := hx1
  obtain ⟨w1_1328, hx1⟩ := hx1
  obtain ⟨w1_132c, hx1⟩ := hx1
  obtain ⟨b1_138, hx1⟩ := hx1
  obtain ⟨b1_158, hx1⟩ := hx1
  obtain ⟨b1_a20, hx1⟩ := hx1
  obtain ⟨b1_a21, hx1⟩ := hx1
  obtain ⟨q1_139, hx1⟩ := hx1
  obtain ⟨q1_159, hx1⟩ := hx1
  obtain ⟨q1_420, hx1⟩ := hx1
  obtain ⟨q1_a21, hx1⟩ := hx1
  obtain ⟨q1_1020, hx1⟩ := hx1
  obtain ⟨q1_1380, hx1⟩ := hx1
  obtain ⟨q1_1480, hx1⟩ := hx1
  obtain ⟨w1_2e0, hx1⟩ := hx1
  obtain ⟨w1_2e4, hx1⟩ := hx1
  obtain ⟨w1_2e8, hx1⟩ := hx1
  obtain ⟨w1_2ec, hx1⟩ := hx1
  obtain ⟨w1_1588, hx1⟩ := hx1
  obtain ⟨b1_158c, hx1⟩ := hx1
  obtain ⟨b1_158d, hx1⟩ := hx1
  obtain ⟨b1_158e, hx1⟩ := hx1
  obtain ⟨b1_158f, hx1⟩ := hx1
  obtain ⟨w1_178, hx1⟩ := hx1
  obtain ⟨w1_17c, hx1⟩ := hx1
  obtain ⟨b1_d0, hx1⟩ := hx1
  have K1_L := hx1
  rcases sv_p256_st F E1 V1 hret hO s1 M0 fR1 r1_2 r1_18 r1_19 r1_20 r1_21 r1_26 r1_27 b1_138 q1_139 b1_158 q1_159 EC0 IC0 UC0 D0 BG0 RS BY0 ((show SvIn B (bp35_5_1_1) 0x41 from by have h := SvIn.bitsW (((((((((((((lc_in).content x1_0).ofNatLen).content x1_2).ofNatLen).restW (opt_ok_elem x1_7)).restW x1_11).restW x1_14).restW x1_17).restW x1_18).restW x1_22).content x1_23).restN x1_25) x1_29 x1_30; rw [x1_31] at h; exact h).shrink (by decide)) (by have h := SvIn.bitsW (((((((((((((lc_in).content x1_0).ofNatLen).content x1_2).ofNatLen).restW (opt_ok_elem x1_7)).restW x1_11).restW x1_14).restW x1_17).restW x1_18).restW x1_22).content x1_23).restN x1_25) x1_29 x1_30; rw [x1_31] at h; exact h) w1_84 dg_in UE0 N80 PM0 WM0 PT0 WN0 ME P2C0 GDC0 P2D0 SC0 hidC GD OD AD hzi w1_4c w1_50 w1_54 w1_58 w1_64 w1_68 w1_6c w1_7c w1_80 w1_88 w1_8c w1_90 w1_94 w1_98 w1_9c w1_a0 w1_a4 w1_a8 w1_ac w1_b0 w1_b4 w1_b8 w1_bc w1_c0 w1_c4 w1_c8 w1_cc rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl w1_130 with e | e | hx2
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  · exact .inr (.inl (Panics.of_steps (c1) e))
  obtain ⟨x2_0, hx2⟩ := hx2
  obtain ⟨σd_2, hx2⟩ := hx2
  obtain ⟨σf_2, hx2⟩ := hx2
  obtain ⟨Dv_2, hx2⟩ := hx2
  obtain ⟨Fv_2, hx2⟩ := hx2
  obtain ⟨x2_1, hx2⟩ := hx2
  obtain ⟨x2_2, hx2⟩ := hx2
  obtain ⟨x2_3, hx2⟩ := hx2
  obtain ⟨x2_4, hx2⟩ := hx2
  obtain ⟨x2_5, hx2⟩ := hx2
  obtain ⟨stm_2, hx2⟩ := hx2
  obtain ⟨x2_6, hx2⟩ := hx2
  obtain ⟨τd_2, hx2⟩ := hx2
  obtain ⟨τf_2, hx2⟩ := hx2
  obtain ⟨Dz_2, hx2⟩ := hx2
  obtain ⟨Fz_2, hx2⟩ := hx2
  obtain ⟨x2_7, hx2⟩ := hx2
  obtain ⟨x2_8, hx2⟩ := hx2
  obtain ⟨x2_9, hx2⟩ := hx2
  obtain ⟨x2_10, hx2⟩ := hx2
  obtain ⟨x2_11, hx2⟩ := hx2
  obtain ⟨n2, hx2⟩ := hx2
  obtain ⟨c2, hx2⟩ := hx2
  obtain ⟨fR2, hx2⟩ := hx2
  obtain ⟨s2, hx2⟩ := hx2
  obtain ⟨E2, hx2⟩ := hx2
  obtain ⟨V2, hx2⟩ := hx2
  obtain ⟨r2_3, hx2⟩ := hx2
  obtain ⟨r2_4, hx2⟩ := hx2
  obtain ⟨r2_2, hx2⟩ := hx2
  obtain ⟨r2_18, hx2⟩ := hx2
  obtain ⟨r2_19, hx2⟩ := hx2
  obtain ⟨r2_26, hx2⟩ := hx2
  obtain ⟨r2_27, hx2⟩ := hx2
  obtain ⟨w2_20, hx2⟩ := hx2
  obtain ⟨w2_4c, hx2⟩ := hx2
  obtain ⟨w2_50, hx2⟩ := hx2
  obtain ⟨w2_54, hx2⟩ := hx2
  obtain ⟨w2_58, hx2⟩ := hx2
  obtain ⟨w2_64, hx2⟩ := hx2
  obtain ⟨w2_68, hx2⟩ := hx2
  obtain ⟨w2_6c, hx2⟩ := hx2
  obtain ⟨w2_78, hx2⟩ := hx2
  obtain ⟨w2_7c, hx2⟩ := hx2
  obtain ⟨w2_80, hx2⟩ := hx2
  obtain ⟨w2_84, hx2⟩ := hx2
  obtain ⟨w2_88, hx2⟩ := hx2
  obtain ⟨w2_8c, hx2⟩ := hx2
  obtain ⟨w2_90, hx2⟩ := hx2
  obtain ⟨w2_94, hx2⟩ := hx2
  obtain ⟨w2_98, hx2⟩ := hx2
  obtain ⟨w2_9c, hx2⟩ := hx2
  obtain ⟨w2_a0, hx2⟩ := hx2
  obtain ⟨w2_a4, hx2⟩ := hx2
  obtain ⟨w2_a8, hx2⟩ := hx2
  obtain ⟨w2_ac, hx2⟩ := hx2
  obtain ⟨w2_b0, hx2⟩ := hx2
  obtain ⟨w2_b4, hx2⟩ := hx2
  obtain ⟨w2_b8, hx2⟩ := hx2
  obtain ⟨w2_bc, hx2⟩ := hx2
  obtain ⟨w2_c0, hx2⟩ := hx2
  obtain ⟨w2_c4, hx2⟩ := hx2
  obtain ⟨w2_c8, hx2⟩ := hx2
  obtain ⟨w2_cc, hx2⟩ := hx2
  obtain ⟨w2_d0, hx2⟩ := hx2
  obtain ⟨w2_d4, hx2⟩ := hx2
  obtain ⟨w2_d8, hx2⟩ := hx2
  obtain ⟨w2_dc, hx2⟩ := hx2
  obtain ⟨w2_e0, hx2⟩ := hx2
  obtain ⟨w2_e4, hx2⟩ := hx2
  obtain ⟨w2_e8, hx2⟩ := hx2
  obtain ⟨w2_ec, hx2⟩ := hx2
  obtain ⟨w2_f0, hx2⟩ := hx2
  obtain ⟨w2_f4, hx2⟩ := hx2
  obtain ⟨w2_f8, hx2⟩ := hx2
  obtain ⟨w2_fc, hx2⟩ := hx2
  obtain ⟨w2_100, hx2⟩ := hx2
  obtain ⟨w2_104, hx2⟩ := hx2
  obtain ⟨w2_108, hx2⟩ := hx2
  obtain ⟨w2_10c, hx2⟩ := hx2
  obtain ⟨w2_110, hx2⟩ := hx2
  obtain ⟨w2_114, hx2⟩ := hx2
  obtain ⟨w2_118, hx2⟩ := hx2
  obtain ⟨w2_11c, hx2⟩ := hx2
  obtain ⟨w2_120, hx2⟩ := hx2
  obtain ⟨w2_124, hx2⟩ := hx2
  obtain ⟨w2_128, hx2⟩ := hx2
  obtain ⟨w2_12c, hx2⟩ := hx2
  obtain ⟨w2_130, hx2⟩ := hx2
  obtain ⟨w2_464, hx2⟩ := hx2
  obtain ⟨b2_a60, hx2⟩ := hx2
  obtain ⟨a2_2a0, hx2⟩ := hx2
  obtain ⟨a2_2c0, hx2⟩ := hx2
  obtain ⟨a2_2e0, hx2⟩ := hx2
  obtain ⟨a2_15a8, hx2⟩ := hx2
  obtain ⟨a2_15c8, hx2⟩ := hx2
  have K2_L := hx2
  rcases sv_seg_ts F E2 V2 hret hO s2 M0 fR2 r2_2 r2_18 r2_19 rfl r2_26 r2_27 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl w2_4c w2_50 w2_54 w2_58 rfl rfl w2_64 w2_68 w2_6c rfl w2_7c w2_80 w2_84 w2_88 w2_8c w2_90 w2_94 w2_98 w2_9c w2_a0 w2_a4 w2_a8 w2_ac w2_b0 w2_b4 w2_b8 w2_bc w2_c0 w2_c4 w2_c8 w2_cc w2_d0 w2_d4 w2_d8 w2_dc w2_e0 w2_e4 w2_e8 w2_ec w2_f0 w2_f4 w2_f8 w2_fc w2_100 w2_104 w2_108 w2_10c w2_110 w2_114 w2_118 w2_11c w2_120 w2_124 w2_128 w2_12c w2_130 c0_in rfl rfl hc0p_in hc0l_in ac0p ac0l D0' (fun i hi c'_5_3 q'_5_3 h => ⟨(H'' i hi c'_5_3 q'_5_3 h).1, (H'' i hi c'_5_3 q'_5_3 h).2.1, (H'' i hi c'_5_3 q'_5_3 h).2.2.1, (H'' i hi c'_5_3 q'_5_3 h).2.2.2.1, (H'' i hi c'_5_3 q'_5_3 h).2.2.2.2⟩) S2 KS' (ts_in) PE0 pkp_in' apk' pk_in' side' with e | e | hx3
  · exact .inl (SvErrRet.pre (c1.trans (c2)) (by rw [r2_3, r1_3]) (by rw [r2_4, r1_4])
      (fun x hx => (fR2 x hx).trans (fM x hx).symm) e)
  · exact .inr (.inl (Panics.of_steps (c1.trans (c2)) e))
  obtain ⟨tl10_1_1_3, hx3⟩ := hx3
  obtain ⟨x3_0, hx3⟩ := hx3
  obtain ⟨x3_1, hx3⟩ := hx3
  obtain ⟨tl22_1_1_3, hx3⟩ := hx3
  obtain ⟨x3_2, hx3⟩ := hx3
  obtain ⟨x3_3, hx3⟩ := hx3
  obtain ⟨te33_1_1_3, hx3⟩ := hx3
  obtain ⟨x3_4, hx3⟩ := hx3
  obtain ⟨x3_5, hx3⟩ := hx3
  obtain ⟨tl41_1_1_3, hx3⟩ := hx3
  obtain ⟨x3_6, hx3⟩ := hx3
  obtain ⟨x3_7, hx3⟩ := hx3
  obtain ⟨op53_1_1_3, hx3⟩ := hx3
  obtain ⟨ol53_1_1_3, hx3⟩ := hx3
  obtain ⟨x3_8, hx3⟩ := hx3
  obtain ⟨to53_1_1_3, hx3⟩ := hx3
  obtain ⟨x3_9, hx3⟩ := hx3
  obtain ⟨x3_10, hx3⟩ := hx3
  obtain ⟨tl2_2_1_3, hx3⟩ := hx3
  obtain ⟨x3_11, hx3⟩ := hx3
  obtain ⟨x3_12, hx3⟩ := hx3
  obtain ⟨tl15_2_1_3, hx3⟩ := hx3
  obtain ⟨x3_13, hx3⟩ := hx3
  obtain ⟨x3_14, hx3⟩ := hx3
  obtain ⟨x3_15, hx3⟩ := hx3
  obtain ⟨te26_2_1_3, hx3⟩ := hx3
  obtain ⟨x3_16, hx3⟩ := hx3
  obtain ⟨tl32_2_1_3, hx3⟩ := hx3
  obtain ⟨x3_17, hx3⟩ := hx3
  obtain ⟨x3_18, hx3⟩ := hx3
  obtain ⟨te41_2_1_3, hx3⟩ := hx3
  obtain ⟨x3_19, hx3⟩ := hx3
  obtain ⟨x3_20, hx3⟩ := hx3
  obtain ⟨tl49_2_1_3, hx3⟩ := hx3
  obtain ⟨x3_21, hx3⟩ := hx3
  obtain ⟨op58_2_1_3, hx3⟩ := hx3
  obtain ⟨ol58_2_1_3, hx3⟩ := hx3
  obtain ⟨x3_22, hx3⟩ := hx3
  obtain ⟨to58_2_1_3, hx3⟩ := hx3
  obtain ⟨x3_23, hx3⟩ := hx3
  obtain ⟨x3_24, hx3⟩ := hx3
  obtain ⟨tl2_3_1_3, hx3⟩ := hx3
  obtain ⟨x3_25, hx3⟩ := hx3
  obtain ⟨x3_26, hx3⟩ := hx3
  obtain ⟨vp23_3_1_3, hx3⟩ := hx3
  obtain ⟨vl23_3_1_3, hx3⟩ := hx3
  obtain ⟨x3_27, hx3⟩ := hx3
  obtain ⟨te23_3_1_3, hx3⟩ := hx3
  obtain ⟨x3_28, hx3⟩ := hx3
  obtain ⟨x3_29, hx3⟩ := hx3
  obtain ⟨tsa4_w2a8_4_1_3, hx3⟩ := hx3
  obtain ⟨tsa4_w2ac_4_1_3, hx3⟩ := hx3
  obtain ⟨x3_30, hx3⟩ := hx3
  obtain ⟨x3_31, hx3⟩ := hx3
  obtain ⟨tl2_5_1_3, hx3⟩ := hx3
  obtain ⟨x3_32, hx3⟩ := hx3
  obtain ⟨x3_33, hx3⟩ := hx3
  obtain ⟨tl13_5_1_3, hx3⟩ := hx3
  obtain ⟨x3_34, hx3⟩ := hx3
  obtain ⟨x3_35, hx3⟩ := hx3
  obtain ⟨x3_36, hx3⟩ := hx3
  obtain ⟨te25_5_1_3, hx3⟩ := hx3
  obtain ⟨x3_37, hx3⟩ := hx3
  obtain ⟨tl31_5_1_3, hx3⟩ := hx3
  obtain ⟨x3_38, hx3⟩ := hx3
  obtain ⟨x3_39, hx3⟩ := hx3
  obtain ⟨te39_5_1_3, hx3⟩ := hx3
  obtain ⟨x3_40, hx3⟩ := hx3
  obtain ⟨tl45_5_1_3, hx3⟩ := hx3
  obtain ⟨x3_41, hx3⟩ := hx3
  obtain ⟨x3_42, hx3⟩ := hx3
  obtain ⟨x3_43, hx3⟩ := hx3
  obtain ⟨tl6_1_2_3, hx3⟩ := hx3
  obtain ⟨x3_44, hx3⟩ := hx3
  obtain ⟨op15_1_2_3, hx3⟩ := hx3
  obtain ⟨ol15_1_2_3, hx3⟩ := hx3
  obtain ⟨x3_45, hx3⟩ := hx3
  obtain ⟨to15_1_2_3, hx3⟩ := hx3
  obtain ⟨x3_46, hx3⟩ := hx3
  obtain ⟨tl20_1_2_3, hx3⟩ := hx3
  obtain ⟨x3_47, hx3⟩ := hx3
  obtain ⟨x3_48, hx3⟩ := hx3
  obtain ⟨x3_49, hx3⟩ := hx3
  obtain ⟨tsav_r24_2_2_3, hx3⟩ := hx3
  obtain ⟨tsav_w78_2_2_3, hx3⟩ := hx3
  obtain ⟨tsav_w1388_2_2_3, hx3⟩ := hx3
  obtain ⟨tsav_w138c_2_2_3, hx3⟩ := hx3
  obtain ⟨x3_50, hx3⟩ := hx3
  obtain ⟨x3_51, hx3⟩ := hx3
  obtain ⟨x3_52, hx3⟩ := hx3
  obtain ⟨k_3_3, hx3⟩ := hx3
  obtain ⟨dg'_3_3, hx3⟩ := hx3
  obtain ⟨flag'_3_3, hx3⟩ := hx3
  obtain ⟨cp'_3_3, hx3⟩ := hx3
  obtain ⟨rem'_3_3, hx3⟩ := hx3
  obtain ⟨x3_53, hx3⟩ := hx3
  obtain ⟨x3_54, hx3⟩ := hx3
  obtain ⟨x3_55, hx3⟩ := hx3
  obtain ⟨x3_56, hx3⟩ := hx3
  obtain ⟨op8_3_3, hx3⟩ := hx3
  obtain ⟨ol8_3_3, hx3⟩ := hx3
  obtain ⟨x3_57, hx3⟩ := hx3
  obtain ⟨te8_3_3, hx3⟩ := hx3
  obtain ⟨x3_58, hx3⟩ := hx3
  obtain ⟨x3_59, hx3⟩ := hx3
  obtain ⟨vp19_3_3, hx3⟩ := hx3
  obtain ⟨vl19_3_3, hx3⟩ := hx3
  obtain ⟨x3_60, hx3⟩ := hx3
  obtain ⟨te19_3_3, hx3⟩ := hx3
  obtain ⟨x3_61, hx3⟩ := hx3
  obtain ⟨sr24_3_3, hx3⟩ := hx3
  obtain ⟨ss24_3_3, hx3⟩ := hx3
  obtain ⟨x3_62, hx3⟩ := hx3
  obtain ⟨x3_63, hx3⟩ := hx3
  obtain ⟨tl13_1_4_3, hx3⟩ := hx3
  obtain ⟨x3_64, hx3⟩ := hx3
  obtain ⟨x3_65, hx3⟩ := hx3
  obtain ⟨x3_66, hx3⟩ := hx3
  obtain ⟨te26_1_4_3, hx3⟩ := hx3
  obtain ⟨x3_67, hx3⟩ := hx3
  obtain ⟨op32_1_4_3, hx3⟩ := hx3
  obtain ⟨ol32_1_4_3, hx3⟩ := hx3
  obtain ⟨x3_68, hx3⟩ := hx3
  obtain ⟨to32_1_4_3, hx3⟩ := hx3
  obtain ⟨x3_69, hx3⟩ := hx3
  obtain ⟨tl36_1_4_3, hx3⟩ := hx3
  obtain ⟨x3_70, hx3⟩ := hx3
  obtain ⟨x3_71, hx3⟩ := hx3
  obtain ⟨te45_1_4_3, hx3⟩ := hx3
  obtain ⟨x3_72, hx3⟩ := hx3
  obtain ⟨vp51_1_4_3, hx3⟩ := hx3
  obtain ⟨vl51_1_4_3, hx3⟩ := hx3
  obtain ⟨x3_73, hx3⟩ := hx3
  obtain ⟨te51_1_4_3, hx3⟩ := hx3
  obtain ⟨x3_74, hx3⟩ := hx3
  obtain ⟨x3_75, hx3⟩ := hx3
  obtain ⟨x3_76, hx3⟩ := hx3
  obtain ⟨tl2_2_4_3, hx3⟩ := hx3
  obtain ⟨x3_77, hx3⟩ := hx3
  obtain ⟨ip2_2_4_3, hx3⟩ := hx3
  obtain ⟨il2_2_4_3, hx3⟩ := hx3
  obtain ⟨x3_78, hx3⟩ := hx3
  obtain ⟨x3_79, hx3⟩ := hx3
  obtain ⟨tl13_2_4_3, hx3⟩ := hx3
  obtain ⟨x3_80, hx3⟩ := hx3
  obtain ⟨tm18_2_4_3, hx3⟩ := hx3
  obtain ⟨x3_81, hx3⟩ := hx3
  obtain ⟨tst3_w1328_3_4_3, hx3⟩ := hx3
  obtain ⟨tst3_w132c_3_4_3, hx3⟩ := hx3
  obtain ⟨x3_82, hx3⟩ := hx3
  obtain ⟨x3_83, hx3⟩ := hx3
  obtain ⟨tst4_r8_4_4_3, hx3⟩ := hx3
  obtain ⟨tst4_w1328_4_4_3, hx3⟩ := hx3
  obtain ⟨tst4_w132c_4_4_3, hx3⟩ := hx3
  obtain ⟨x3_84, hx3⟩ := hx3
  obtain ⟨x3_85, hx3⟩ := hx3
  obtain ⟨tst5_w1328_5_4_3, hx3⟩ := hx3
  obtain ⟨tst5_w132c_5_4_3, hx3⟩ := hx3
  obtain ⟨x3_86, hx3⟩ := hx3
  obtain ⟨x3_87, hx3⟩ := hx3
  obtain ⟨tst6_w1328_6_4_3, hx3⟩ := hx3
  obtain ⟨tst6_w132c_6_4_3, hx3⟩ := hx3
  obtain ⟨x3_88, hx3⟩ := hx3
  obtain ⟨x3_89, hx3⟩ := hx3
  obtain ⟨k_5_3, hx3⟩ := hx3
  obtain ⟨x3_90, hx3⟩ := hx3
  obtain ⟨x3_91, hx3⟩ := hx3
  obtain ⟨c'_5_3, hx3⟩ := hx3
  obtain ⟨q'_5_3, hx3⟩ := hx3
  obtain ⟨x3_92, hx3⟩ := hx3
  obtain ⟨x3_93, hx3⟩ := hx3
  obtain ⟨x3_94, hx3⟩ := hx3
  obtain ⟨x3_95, hx3⟩ := hx3
  obtain ⟨x3_96, hx3⟩ := hx3
  obtain ⟨x3_97, hx3⟩ := hx3
  obtain ⟨pv_7_3, hx3⟩ := hx3
  obtain ⟨x3_98, hx3⟩ := hx3
  obtain ⟨n3, hx3⟩ := hx3
  obtain ⟨c3, hx3⟩ := hx3
  obtain ⟨fR3, hx3⟩ := hx3
  obtain ⟨s3, hx3⟩ := hx3
  obtain ⟨E3, hx3⟩ := hx3
  obtain ⟨V3, hx3⟩ := hx3
  obtain ⟨r3_3, hx3⟩ := hx3
  obtain ⟨r3_4, hx3⟩ := hx3
  obtain ⟨r3_2, hx3⟩ := hx3
  obtain ⟨r3_a0, hx3⟩ := hx3
  obtain ⟨r3_18, hx3⟩ := hx3
  obtain ⟨r3_19, hx3⟩ := hx3
  obtain ⟨r3_21, hx3⟩ := hx3
  obtain ⟨r3_22, hx3⟩ := hx3
  obtain ⟨r3_23, hx3⟩ := hx3
  obtain ⟨r3_24, hx3⟩ := hx3
  obtain ⟨r3_26, hx3⟩ := hx3
  obtain ⟨r3_27, hx3⟩ := hx3
  obtain ⟨w3_24, hx3⟩ := hx3
  obtain ⟨w3_28, hx3⟩ := hx3
  obtain ⟨w3_2c, hx3⟩ := hx3
  obtain ⟨w3_30, hx3⟩ := hx3
  obtain ⟨w3_34, hx3⟩ := hx3
  obtain ⟨w3_38, hx3⟩ := hx3
  obtain ⟨w3_3c, hx3⟩ := hx3
  obtain ⟨w3_40, hx3⟩ := hx3
  obtain ⟨w3_44, hx3⟩ := hx3
  obtain ⟨w3_48, hx3⟩ := hx3
  obtain ⟨w3_4c, hx3⟩ := hx3
  obtain ⟨w3_50, hx3⟩ := hx3
  obtain ⟨w3_54, hx3⟩ := hx3
  obtain ⟨w3_58, hx3⟩ := hx3
  obtain ⟨w3_5c, hx3⟩ := hx3
  obtain ⟨w3_60, hx3⟩ := hx3
  obtain ⟨w3_64, hx3⟩ := hx3
  obtain ⟨w3_68, hx3⟩ := hx3
  obtain ⟨w3_6c, hx3⟩ := hx3
  obtain ⟨w3_70, hx3⟩ := hx3
  obtain ⟨w3_7c, hx3⟩ := hx3
  obtain ⟨w3_80, hx3⟩ := hx3
  obtain ⟨w3_84, hx3⟩ := hx3
  obtain ⟨w3_88, hx3⟩ := hx3
  obtain ⟨w3_8c, hx3⟩ := hx3
  obtain ⟨w3_90, hx3⟩ := hx3
  obtain ⟨w3_94, hx3⟩ := hx3
  obtain ⟨w3_98, hx3⟩ := hx3
  obtain ⟨w3_9c, hx3⟩ := hx3
  obtain ⟨w3_a0, hx3⟩ := hx3
  obtain ⟨w3_a4, hx3⟩ := hx3
  obtain ⟨w3_a8, hx3⟩ := hx3
  obtain ⟨w3_ac, hx3⟩ := hx3
  obtain ⟨w3_b0, hx3⟩ := hx3
  obtain ⟨w3_b4, hx3⟩ := hx3
  obtain ⟨w3_b8, hx3⟩ := hx3
  obtain ⟨w3_bc, hx3⟩ := hx3
  obtain ⟨w3_c0, hx3⟩ := hx3
  obtain ⟨w3_c4, hx3⟩ := hx3
  obtain ⟨w3_c8, hx3⟩ := hx3
  obtain ⟨w3_cc, hx3⟩ := hx3
  obtain ⟨w3_d0, hx3⟩ := hx3
  obtain ⟨w3_d4, hx3⟩ := hx3
  obtain ⟨w3_d8, hx3⟩ := hx3
  obtain ⟨w3_dc, hx3⟩ := hx3
  obtain ⟨w3_e0, hx3⟩ := hx3
  obtain ⟨w3_e4, hx3⟩ := hx3
  obtain ⟨w3_e8, hx3⟩ := hx3
  obtain ⟨w3_ec, hx3⟩ := hx3
  obtain ⟨w3_f0, hx3⟩ := hx3
  obtain ⟨w3_f4, hx3⟩ := hx3
  obtain ⟨w3_f8, hx3⟩ := hx3
  obtain ⟨w3_fc, hx3⟩ := hx3
  obtain ⟨w3_100, hx3⟩ := hx3
  obtain ⟨w3_104, hx3⟩ := hx3
  obtain ⟨w3_108, hx3⟩ := hx3
  obtain ⟨w3_10c, hx3⟩ := hx3
  obtain ⟨w3_110, hx3⟩ := hx3
  obtain ⟨w3_114, hx3⟩ := hx3
  obtain ⟨w3_118, hx3⟩ := hx3
  obtain ⟨w3_11c, hx3⟩ := hx3
  obtain ⟨w3_120, hx3⟩ := hx3
  obtain ⟨w3_124, hx3⟩ := hx3
  obtain ⟨w3_128, hx3⟩ := hx3
  obtain ⟨w3_12c, hx3⟩ := hx3
  obtain ⟨w3_130, hx3⟩ := hx3
  obtain ⟨w3_78, hx3⟩ := hx3
  obtain ⟨w3_178, hx3⟩ := hx3
  obtain ⟨w3_17c, hx3⟩ := hx3
  obtain ⟨w3_180, hx3⟩ := hx3
  obtain ⟨w3_184, hx3⟩ := hx3
  obtain ⟨w3_200, hx3⟩ := hx3
  obtain ⟨w3_204, hx3⟩ := hx3
  obtain ⟨w3_208, hx3⟩ := hx3
  obtain ⟨w3_20c, hx3⟩ := hx3
  obtain ⟨w3_2a8, hx3⟩ := hx3
  obtain ⟨w3_2ac, hx3⟩ := hx3
  obtain ⟨w3_1320, hx3⟩ := hx3
  obtain ⟨w3_1324, hx3⟩ := hx3
  obtain ⟨w3_1328, hx3⟩ := hx3
  obtain ⟨w3_132c, hx3⟩ := hx3
  obtain ⟨w3_1608, hx3⟩ := hx3
  obtain ⟨w3_160c, hx3⟩ := hx3
  obtain ⟨w3_1610, hx3⟩ := hx3
  obtain ⟨w3_1614, hx3⟩ := hx3
  obtain ⟨w3_1618, hx3⟩ := hx3
  obtain ⟨w3_161c, hx3⟩ := hx3
  obtain ⟨w3_1620, hx3⟩ := hx3
  obtain ⟨w3_1624, hx3⟩ := hx3
  obtain ⟨w3_1628, hx3⟩ := hx3
  obtain ⟨w3_162c, hx3⟩ := hx3
  obtain ⟨w3_1630, hx3⟩ := hx3
  obtain ⟨w3_1634, hx3⟩ := hx3
  obtain ⟨w3_1638, hx3⟩ := hx3
  obtain ⟨w3_163c, hx3⟩ := hx3
  obtain ⟨w3_1640, hx3⟩ := hx3
  obtain ⟨w3_1644, hx3⟩ := hx3
  obtain ⟨w3_2a0, hx3⟩ := hx3
  obtain ⟨w3_2a4, hx3⟩ := hx3
  obtain ⟨w3_2c0, hx3⟩ := hx3
  obtain ⟨w3_2c4, hx3⟩ := hx3
  obtain ⟨w3_2c8, hx3⟩ := hx3
  obtain ⟨w3_2cc, hx3⟩ := hx3
  obtain ⟨w3_2e0, hx3⟩ := hx3
  obtain ⟨w3_2e4, hx3⟩ := hx3
  obtain ⟨w3_2e8, hx3⟩ := hx3
  obtain ⟨w3_2ec, hx3⟩ := hx3
  obtain ⟨w3_1648, hx3⟩ := hx3
  obtain ⟨w3_164c, hx3⟩ := hx3
  obtain ⟨w3_1650, hx3⟩ := hx3
  obtain ⟨w3_1654, hx3⟩ := hx3
  obtain ⟨w3_1588, hx3⟩ := hx3
  obtain ⟨w3_158c, hx3⟩ := hx3
  obtain ⟨w3_1590, hx3⟩ := hx3
  obtain ⟨w3_1594, hx3⟩ := hx3
  obtain ⟨w3_74, hx3⟩ := hx3
  obtain ⟨w3_1388, hx3⟩ := hx3
  obtain ⟨w3_138c, hx3⟩ := hx3
  obtain ⟨w3_320, hx3⟩ := hx3
  obtain ⟨w3_324, hx3⟩ := hx3
  obtain ⟨w3_328, hx3⟩ := hx3
  obtain ⟨w3_32c, hx3⟩ := hx3
  obtain ⟨w3_a20, hx3⟩ := hx3
  obtain ⟨w3_a24, hx3⟩ := hx3
  obtain ⟨w3_a28, hx3⟩ := hx3
  obtain ⟨w3_a2c, hx3⟩ := hx3
  obtain ⟨w3_a30, hx3⟩ := hx3
  obtain ⟨w3_a34, hx3⟩ := hx3
  obtain ⟨w3_a38, hx3⟩ := hx3
  obtain ⟨w3_a3c, hx3⟩ := hx3
  obtain ⟨w3_aa0, hx3⟩ := hx3
  obtain ⟨w3_aa4, hx3⟩ := hx3
  obtain ⟨b3_a40, hx3⟩ := hx3
  obtain ⟨w3_240, hx3⟩ := hx3
  obtain ⟨w3_244, hx3⟩ := hx3
  obtain ⟨w3_248, hx3⟩ := hx3
  obtain ⟨w3_24c, hx3⟩ := hx3
  obtain ⟨b3_1380, hx3⟩ := hx3
  obtain ⟨w3_1020, hx3⟩ := hx3
  obtain ⟨w3_1024, hx3⟩ := hx3
  obtain ⟨w3_1028, hx3⟩ := hx3
  obtain ⟨w3_102c, hx3⟩ := hx3
  have K3_L := hx3
  rcases sv_seg_log F E3 V3 hret hO s3 M0 fR3 r3_2 r3_a0 r3_18 r3_19 r3_21 r3_22 r3_23 r3_24 r3_26 r3_27 w3_24 w3_28 w3_2c w3_30 w3_34 w3_38 w3_3c w3_40 w3_44 w3_48 w3_4c w3_50 w3_54 w3_58 w3_5c w3_60 w3_64 w3_68 w3_6c w3_70 w3_74 w3_78 w3_7c w3_80 w3_84 w3_88 w3_8c w3_90 w3_94 w3_98 w3_9c w3_a0 w3_a4 w3_a8 w3_ac w3_b0 w3_b4 w3_b8 w3_bc w3_c0 w3_c4 w3_c8 w3_cc w3_d0 w3_d4 w3_d8 w3_dc w3_e0 w3_e4 w3_e8 w3_ec w3_f0 w3_f4 w3_f8 w3_fc w3_100 w3_104 w3_108 w3_10c w3_110 w3_114 w3_118 w3_11c w3_120 w3_124 w3_128 w3_12c w3_130 w3_a20 w3_a24 w3_a28 w3_a2c w3_a30 w3_a34 w3_a38 w3_a3c w3_aa0 w3_aa4 CK0 rfl rfl ckp_in4 ckl_in4 a_ckp a_ckl ck_in rfl rfl rfl rfl rfl rfl (fun i hi c'_3_4 q'_3_4 w80'_3_4 h => ⟨(H''' i hi c'_3_4 q'_3_4 w80'_3_4 h).1, (H''' i hi c'_3_4 q'_3_4 w80'_3_4 h).2.1, (H''' i hi c'_3_4 q'_3_4 w80'_3_4 h).2.2.1, (H''' i hi c'_3_4 q'_3_4 w80'_3_4 h).2.2.2.1, (H''' i hi c'_3_4 q'_3_4 w80'_3_4 h).2.2.2.2⟩) S2 KS'' kp_in4 kw_in4 a_kp a_kw kp_in EE0 RS hiv pk_in'' lid_in lih_in lil_in a_lih a_lil RK0 dgi_in (ts_in) (lc_in) pp_in4 pl_in4 a_pp a_pl pp_in (ii2h k_4_1 x1_53 c'_4_1 q'_4_1 x1_55 x1_57) (ai2h k_4_1 x1_53 c'_4_1 q'_4_1 x1_55 x1_57) (ii2l k_4_1 x1_53 c'_4_1 q'_4_1 x1_55 x1_57) (ai2l k_4_1 x1_53 c'_4_1 q'_4_1 x1_55 x1_57) (ii3h k_4_1 x1_53 c'_4_1 q'_4_1 x1_55 x1_57) (ai3h k_4_1 x1_53 c'_4_1 q'_4_1 x1_55 x1_57) (ii3l k_4_1 x1_53 c'_4_1 q'_4_1 x1_55 x1_57) (ai3l k_4_1 x1_53 c'_4_1 q'_4_1 x1_55 x1_57) (it4h k_5_3 x3_90 c'_5_3 q'_5_3 x3_92 x3_94) (at4h k_5_3 x3_90 c'_5_3 q'_5_3 x3_92 x3_94) (it4l k_5_3 x3_90 c'_5_3 q'_5_3 x3_92 x3_94) (at4l k_5_3 x3_90 c'_5_3 q'_5_3 x3_92 x3_94) (it5h k_5_3 x3_90 c'_5_3 q'_5_3 x3_92 x3_94) (at5h k_5_3 x3_90 c'_5_3 q'_5_3 x3_92 x3_94) (it5l k_5_3 x3_90 c'_5_3 q'_5_3 x3_92 x3_94) (at5l k_5_3 x3_90 c'_5_3 q'_5_3 x3_92 x3_94) with e | hx4
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3))) (by rw [r3_3, r2_3, r1_3]) (by rw [r3_4, r2_4, r1_4])
      (fun x hx => (fR3 x hx).trans (fM x hx).symm) e)
  obtain ⟨x4_0, hx4⟩ := hx4
  obtain ⟨ix7_1_1_4, hx4⟩ := hx4
  obtain ⟨x4_1, hx4⟩ := hx4
  obtain ⟨ix17_1_1_4, hx4⟩ := hx4
  obtain ⟨x4_2, hx4⟩ := hx4
  obtain ⟨ix25_1_1_4, hx4⟩ := hx4
  obtain ⟨x4_3, hx4⟩ := hx4
  obtain ⟨ix33_1_1_4, hx4⟩ := hx4
  obtain ⟨x4_4, hx4⟩ := hx4
  obtain ⟨x4_5, hx4⟩ := hx4
  obtain ⟨x4_6, hx4⟩ := hx4
  obtain ⟨x4_7, hx4⟩ := hx4
  obtain ⟨c'_2_4, hx4⟩ := hx4
  obtain ⟨p'_2_4, hx4⟩ := hx4
  obtain ⟨x21'_2_4, hx4⟩ := hx4
  obtain ⟨w60'_2_4, hx4⟩ := hx4
  obtain ⟨w70'_2_4, hx4⟩ := hx4
  obtain ⟨x4_8, hx4⟩ := hx4
  obtain ⟨x4_9, hx4⟩ := hx4
  obtain ⟨x4_10, hx4⟩ := hx4
  obtain ⟨bs7_2_4, hx4⟩ := hx4
  obtain ⟨x4_11, hx4⟩ := hx4
  obtain ⟨x4_12, hx4⟩ := hx4
  obtain ⟨k_3_4, hx4⟩ := hx4
  obtain ⟨x4_13, hx4⟩ := hx4
  obtain ⟨x4_14, hx4⟩ := hx4
  obtain ⟨c'_3_4, hx4⟩ := hx4
  obtain ⟨q'_3_4, hx4⟩ := hx4
  obtain ⟨w80'_3_4, hx4⟩ := hx4
  obtain ⟨x4_15, hx4⟩ := hx4
  obtain ⟨x4_16, hx4⟩ := hx4
  obtain ⟨x4_17, hx4⟩ := hx4
  obtain ⟨sg_5_4, hx4⟩ := hx4
  obtain ⟨k_5_4, hx4⟩ := hx4
  obtain ⟨c'_5_4, hx4⟩ := hx4
  obtain ⟨x21'_5_4, hx4⟩ := hx4
  obtain ⟨rl'_5_4, hx4⟩ := hx4
  obtain ⟨rp'_5_4, hx4⟩ := hx4
  obtain ⟨dg'_5_4, hx4⟩ := hx4
  obtain ⟨w8'_5_4, hx4⟩ := hx4
  obtain ⟨wc'_5_4, hx4⟩ := hx4
  obtain ⟨w28'_5_4, hx4⟩ := hx4
  obtain ⟨w2c'_5_4, hx4⟩ := hx4
  obtain ⟨w30'_5_4, hx4⟩ := hx4
  obtain ⟨w38'_5_4, hx4⟩ := hx4
  obtain ⟨w40'_5_4, hx4⟩ := hx4
  obtain ⟨w5c'_5_4, hx4⟩ := hx4
  obtain ⟨sg'_5_4, hx4⟩ := hx4
  obtain ⟨x4_18, hx4⟩ := hx4
  obtain ⟨x4_19, hx4⟩ := hx4
  obtain ⟨x4_20, hx4⟩ := hx4
  obtain ⟨x4_21, hx4⟩ := hx4
  obtain ⟨x4_22, hx4⟩ := hx4
  obtain ⟨root6_3_6_4, hx4⟩ := hx4
  obtain ⟨x4_23, hx4⟩ := hx4
  obtain ⟨x4_24, hx4⟩ := hx4
  obtain ⟨x4_25, hx4⟩ := hx4
  obtain ⟨x4_26, hx4⟩ := hx4
  obtain ⟨x4_27, hx4⟩ := hx4
  obtain ⟨x4_28, hx4⟩ := hx4
  obtain ⟨x4_29, hx4⟩ := hx4
  obtain ⟨x4_30, hx4⟩ := hx4
  obtain ⟨x4_31, hx4⟩ := hx4
  obtain ⟨x4_32, hx4⟩ := hx4
  obtain ⟨n4, hx4⟩ := hx4
  obtain ⟨c4, hx4⟩ := hx4
  obtain ⟨fR4, hx4⟩ := hx4
  obtain ⟨s4, hx4⟩ := hx4
  obtain ⟨E4, hx4⟩ := hx4
  obtain ⟨V4, hx4⟩ := hx4
  obtain ⟨r4_3, hx4⟩ := hx4
  obtain ⟨r4_4, hx4⟩ := hx4
  obtain ⟨r4_2, hx4⟩ := hx4
  obtain ⟨r4_8, hx4⟩ := hx4
  obtain ⟨r4_9, hx4⟩ := hx4
  obtain ⟨r4_18, hx4⟩ := hx4
  obtain ⟨r4_19, hx4⟩ := hx4
  obtain ⟨r4_21, hx4⟩ := hx4
  obtain ⟨r4_22, hx4⟩ := hx4
  obtain ⟨r4_23, hx4⟩ := hx4
  obtain ⟨r4_24, hx4⟩ := hx4
  obtain ⟨r4_25, hx4⟩ := hx4
  obtain ⟨r4_26, hx4⟩ := hx4
  obtain ⟨r4_27, hx4⟩ := hx4
  obtain ⟨w4_8, hx4⟩ := hx4
  obtain ⟨w4_c, hx4⟩ := hx4
  obtain ⟨w4_14, hx4⟩ := hx4
  obtain ⟨w4_18, hx4⟩ := hx4
  obtain ⟨w4_1c, hx4⟩ := hx4
  obtain ⟨w4_20, hx4⟩ := hx4
  obtain ⟨w4_24, hx4⟩ := hx4
  obtain ⟨w4_28, hx4⟩ := hx4
  obtain ⟨w4_2c, hx4⟩ := hx4
  obtain ⟨w4_30, hx4⟩ := hx4
  obtain ⟨w4_34, hx4⟩ := hx4
  obtain ⟨w4_38, hx4⟩ := hx4
  obtain ⟨w4_3c, hx4⟩ := hx4
  obtain ⟨w4_40, hx4⟩ := hx4
  obtain ⟨w4_44, hx4⟩ := hx4
  obtain ⟨w4_48, hx4⟩ := hx4
  obtain ⟨w4_4c, hx4⟩ := hx4
  obtain ⟨w4_50, hx4⟩ := hx4
  obtain ⟨w4_54, hx4⟩ := hx4
  obtain ⟨w4_58, hx4⟩ := hx4
  obtain ⟨w4_5c, hx4⟩ := hx4
  obtain ⟨w4_60, hx4⟩ := hx4
  obtain ⟨w4_64, hx4⟩ := hx4
  obtain ⟨w4_68, hx4⟩ := hx4
  obtain ⟨w4_6c, hx4⟩ := hx4
  obtain ⟨w4_70, hx4⟩ := hx4
  obtain ⟨w4_74, hx4⟩ := hx4
  obtain ⟨w4_78, hx4⟩ := hx4
  obtain ⟨w4_7c, hx4⟩ := hx4
  obtain ⟨w4_80, hx4⟩ := hx4
  obtain ⟨w4_84, hx4⟩ := hx4
  obtain ⟨w4_88, hx4⟩ := hx4
  obtain ⟨w4_8c, hx4⟩ := hx4
  obtain ⟨w4_90, hx4⟩ := hx4
  obtain ⟨w4_94, hx4⟩ := hx4
  obtain ⟨w4_98, hx4⟩ := hx4
  obtain ⟨w4_9c, hx4⟩ := hx4
  obtain ⟨w4_a0, hx4⟩ := hx4
  obtain ⟨w4_a4, hx4⟩ := hx4
  obtain ⟨w4_a8, hx4⟩ := hx4
  obtain ⟨w4_ac, hx4⟩ := hx4
  obtain ⟨w4_b0, hx4⟩ := hx4
  obtain ⟨w4_b4, hx4⟩ := hx4
  obtain ⟨w4_b8, hx4⟩ := hx4
  obtain ⟨w4_bc, hx4⟩ := hx4
  obtain ⟨w4_c0, hx4⟩ := hx4
  obtain ⟨w4_c4, hx4⟩ := hx4
  obtain ⟨w4_c8, hx4⟩ := hx4
  obtain ⟨w4_cc, hx4⟩ := hx4
  obtain ⟨w4_d0, hx4⟩ := hx4
  obtain ⟨w4_d4, hx4⟩ := hx4
  obtain ⟨w4_d8, hx4⟩ := hx4
  obtain ⟨w4_dc, hx4⟩ := hx4
  obtain ⟨w4_e0, hx4⟩ := hx4
  obtain ⟨w4_e4, hx4⟩ := hx4
  obtain ⟨w4_e8, hx4⟩ := hx4
  obtain ⟨w4_ec, hx4⟩ := hx4
  obtain ⟨w4_f0, hx4⟩ := hx4
  obtain ⟨w4_f4, hx4⟩ := hx4
  obtain ⟨w4_f8, hx4⟩ := hx4
  obtain ⟨w4_fc, hx4⟩ := hx4
  obtain ⟨w4_100, hx4⟩ := hx4
  obtain ⟨w4_104, hx4⟩ := hx4
  obtain ⟨w4_108, hx4⟩ := hx4
  obtain ⟨w4_10c, hx4⟩ := hx4
  obtain ⟨w4_110, hx4⟩ := hx4
  obtain ⟨w4_114, hx4⟩ := hx4
  obtain ⟨w4_118, hx4⟩ := hx4
  obtain ⟨w4_11c, hx4⟩ := hx4
  obtain ⟨w4_120, hx4⟩ := hx4
  obtain ⟨w4_124, hx4⟩ := hx4
  obtain ⟨w4_128, hx4⟩ := hx4
  obtain ⟨w4_12c, hx4⟩ := hx4
  obtain ⟨w4_130, hx4⟩ := hx4
  obtain ⟨w4_a20, hx4⟩ := hx4
  obtain ⟨w4_a24, hx4⟩ := hx4
  obtain ⟨w4_a28, hx4⟩ := hx4
  obtain ⟨w4_a2c, hx4⟩ := hx4
  obtain ⟨w4_a30, hx4⟩ := hx4
  obtain ⟨w4_a34, hx4⟩ := hx4
  obtain ⟨w4_a38, hx4⟩ := hx4
  obtain ⟨w4_a3c, hx4⟩ := hx4
  obtain ⟨w4_aa0, hx4⟩ := hx4
  obtain ⟨w4_aa4, hx4⟩ := hx4
  obtain ⟨w4_1028, hx4⟩ := hx4
  obtain ⟨w4_102c, hx4⟩ := hx4
  obtain ⟨w4_1030, hx4⟩ := hx4
  obtain ⟨w4_1034, hx4⟩ := hx4
  obtain ⟨b4_10, hx4⟩ := hx4
  obtain ⟨b4_1048, hx4⟩ := hx4
  obtain ⟨q4_320, hx4⟩ := hx4
  obtain ⟨q4_1049, hx4⟩ := hx4
  obtain ⟨w4_1020, hx4⟩ := hx4
  obtain ⟨w4_1038, hx4⟩ := hx4
  obtain ⟨w4_103c, hx4⟩ := hx4
  obtain ⟨w4_1040, hx4⟩ := hx4
  obtain ⟨w4_1044, hx4⟩ := hx4
  obtain ⟨b4_420, hx4⟩ := hx4
  obtain ⟨b4_421, hx4⟩ := hx4
  obtain ⟨b4_1480, hx4⟩ := hx4
  have K4_L := hx4
  exact .inr (.inr ⟨t_1_1_1, x1_0, x1_1, tl1_2_1_1, x1_2, tl8_2_1_1, x1_3, tl16_2_1_1, x1_4, bp16_2_1_1, bl16_2_1_1, x1_5, x1_6, tl29_2_1_1, x1_7, x1_8, te43_2_1_1, x1_9, x1_10, tl2_3_1_1, x1_11, ip2_3_1_1, il2_3_1_1, x1_12, x1_13, tl9_3_1_1, x1_14, op19_3_1_1, ol19_3_1_1, x1_15, x1_16, tl6_4_1_1, x1_17, tl13_4_1_1, x1_18, tm22_4_1_1, rs22_4_1_1, x1_19, tm31_4_1_1, rs31_4_1_1, x1_20, x1_21, tl2_5_1_1, x1_22, tl6_5_1_1, x1_23, op15_5_1_1, ol15_5_1_1, prp15_5_1_1, pu15_5_1_1, x1_24, ta15_5_1_1, x1_25, x1_26, x1_27, x1_28, tl35_5_1_1, x1_29, bp35_5_1_1, bl35_5_1_1, x1_30, x1_31, x1_32, x1_33, x1_34, tl9_6_1_1, x1_35, x1_36, tl25_6_1_1, x1_37, x1_38, u0_1, u1_1, u2_1, k_2_1, f30'_2_1, f34'_2_1, rem'_2_1, cur'_2_1, sl0'_2_1, sl1'_2_1, sl2'_2_1, sl3'_2_1, sl4'_2_1, sl5'_2_1, sl6'_2_1, sl7'_2_1, sl8'_2_1, sl9'_2_1, x1_39, x1_40, x1_41, x1_42, x1_43, x1_44, x1_45, x1_46, x1_47, x1_48, x1_49, x1_50, x1_51, sr43_2_1, ss43_2_1, x1_52, k_4_1, x1_53, x1_54, c'_4_1, q'_4_1, x1_55, x1_56, x1_57, pv_5_1, x1_58, x1_59, x1_60, x1_61, x1_62, x1_63, x1_64, tl49_1_6_1, x1_65, x1_66, bs9_2_6_1, x1_67, te9_2_6_1, x1_68, bs16_2_6_1, x1_69, te16_2_6_1, x1_70, x1_71, x2_0, σd_2, σf_2, Dv_2, Fv_2, x2_1, x2_2, x2_3, x2_4, x2_5, stm_2, x2_6, τd_2, τf_2, Dz_2, Fz_2, x2_7, x2_8, x2_9, x2_10, x2_11, tl10_1_1_3, x3_0, x3_1, tl22_1_1_3, x3_2, x3_3, te33_1_1_3, x3_4, x3_5, tl41_1_1_3, x3_6, x3_7, op53_1_1_3, ol53_1_1_3, x3_8, to53_1_1_3, x3_9, x3_10, tl2_2_1_3, x3_11, x3_12, tl15_2_1_3, x3_13, x3_14, x3_15, te26_2_1_3, x3_16, tl32_2_1_3, x3_17, x3_18, te41_2_1_3, x3_19, x3_20, tl49_2_1_3, x3_21, op58_2_1_3, ol58_2_1_3, x3_22, to58_2_1_3, x3_23, x3_24, tl2_3_1_3, x3_25, x3_26, vp23_3_1_3, vl23_3_1_3, x3_27, te23_3_1_3, x3_28, x3_29, tsa4_w2a8_4_1_3, tsa4_w2ac_4_1_3, x3_30, x3_31, tl2_5_1_3, x3_32, x3_33, tl13_5_1_3, x3_34, x3_35, x3_36, te25_5_1_3, x3_37, tl31_5_1_3, x3_38, x3_39, te39_5_1_3, x3_40, tl45_5_1_3, x3_41, x3_42, x3_43, tl6_1_2_3, x3_44, op15_1_2_3, ol15_1_2_3, x3_45, to15_1_2_3, x3_46, tl20_1_2_3, x3_47, x3_48, x3_49, tsav_r24_2_2_3, tsav_w78_2_2_3, tsav_w1388_2_2_3, tsav_w138c_2_2_3, x3_50, x3_51, x3_52, (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x24)), (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x28)), (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C)), (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x30)), (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x34)), (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x38)), (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C)), (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x100)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x104)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x108)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x110)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x114)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x118)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x120)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x124)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x128)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C)), k_3_3, dg'_3_3, flag'_3_3, cp'_3_3, rem'_3_3, x3_53, x3_54, x3_55, x3_56, op8_3_3, ol8_3_3, x3_57, te8_3_3, x3_58, x3_59, vp19_3_3, vl19_3_3, x3_60, te19_3_3, x3_61, sr24_3_3, ss24_3_3, x3_62, x3_63, tl13_1_4_3, x3_64, x3_65, x3_66, te26_1_4_3, x3_67, op32_1_4_3, ol32_1_4_3, x3_68, to32_1_4_3, x3_69, tl36_1_4_3, x3_70, x3_71, te45_1_4_3, x3_72, vp51_1_4_3, vl51_1_4_3, x3_73, te51_1_4_3, x3_74, x3_75, x3_76, tl2_2_4_3, x3_77, ip2_2_4_3, il2_2_4_3, x3_78, x3_79, tl13_2_4_3, x3_80, tm18_2_4_3, x3_81, tst3_w1328_3_4_3, tst3_w132c_3_4_3, x3_82, x3_83, tst4_r8_4_4_3, tst4_w1328_4_4_3, tst4_w132c_4_4_3, x3_84, x3_85, tst5_w1328_5_4_3, tst5_w132c_5_4_3, x3_86, x3_87, tst6_w1328_6_4_3, tst6_w132c_6_4_3, x3_88, x3_89, k_5_3, x3_90, x3_91, c'_5_3, q'_5_3, x3_92, x3_93, x3_94, x3_95, x3_96, x3_97, pv_7_3, x3_98, x4_0, ix7_1_1_4, x4_1, ix17_1_1_4, x4_2, ix25_1_1_4, x4_3, ix33_1_1_4, x4_4, x4_5, x4_6, x4_7, c'_2_4, p'_2_4, x21'_2_4, w60'_2_4, w70'_2_4, x4_8, x4_9, x4_10, bs7_2_4, x4_11, x4_12, k_3_4, x4_13, x4_14, c'_3_4, q'_3_4, w80'_3_4, x4_15, x4_16, x4_17, (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x100)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x104)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x108)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x110)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x114)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x118)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x120)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x124)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x128)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C)), (memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x8)), (memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0xC)), (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x28)), (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C)), (memLoad32 n2.mem (B + 0x21A0 + BitVec.ofNat 32 0x40)), sg_5_4, k_5_4, c'_5_4, x21'_5_4, rl'_5_4, rp'_5_4, dg'_5_4, w8'_5_4, wc'_5_4, w28'_5_4, w2c'_5_4, w30'_5_4, w38'_5_4, w40'_5_4, w5c'_5_4, sg'_5_4, x4_18, x4_19, x4_20, x4_21, x4_22, root6_3_6_4, x4_23, x4_24, x4_25, x4_26, x4_27, x4_28, x4_29, x4_30, x4_31, x4_32, n4, c1.trans (c2.trans (c3.trans (c4))), fR4, s4, E4, V4,
    by rw [r4_3, r3_3, r2_3, r1_3], by rw [r4_4, r3_4, r2_4, r1_4], r4_2, r4_8, r4_9, r4_18, r4_19, r4_21, r4_22, r4_23, r4_24, r4_25, r4_26, r4_27, w4_8, w4_c, w4_14, w4_18, w4_1c, w4_20, w4_24, w4_28, w4_2c, w4_30, w4_34, w4_38, w4_3c, w4_40, w4_44, w4_48, w4_4c, w4_50, w4_54, w4_58, w4_5c, w4_60, w4_64, w4_68, w4_6c, w4_70, w4_74, w4_78, w4_7c, w4_80, w4_84, w4_88, w4_8c, w4_90, w4_94, w4_98, w4_9c, w4_a0, w4_a4, w4_a8, w4_ac, w4_b0, w4_b4, w4_b8, w4_bc, w4_c0, w4_c4, w4_c8, w4_cc, w4_130, w4_a20, w4_a24, w4_a28, w4_a2c, w4_a30, w4_a34, w4_a38, w4_a3c, w4_aa0, w4_aa4, w4_1028, w4_102c, w4_1030, w4_1034, b4_10, b4_1048, q4_320, q4_1049, w4_1020, w4_1038, w4_103c, w4_1040, w4_1044, b4_420, b4_421, b4_1480, ((K4_L.w32 (by decide) (by decide)).trans w3_2e0), ((K4_L.w32 (by decide) (by decide)).trans w3_2e4), ((K4_L.w32 (by decide) (by decide)).trans w3_2e8), ((K4_L.w32 (by decide) (by decide)).trans w3_2ec), ((K4_L.w32 (by decide) (by decide)).trans w3_1588), ((K4_L.w32 (by decide) (by decide)).trans w3_178), ((K4_L.w32 (by decide) (by decide)).trans w3_17c), ((K4_L.w32 (by decide) (by decide)).trans w3_180), ((K4_L.w32 (by decide) (by decide)).trans w3_184), ((K4_L.w32 (by decide) (by decide)).trans w3_204), ((K4_L.w32 (by decide) (by decide)).trans w3_208), ((K4_L.w32 (by decide) (by decide)).trans w3_20c), ((K4_L.w32 (by decide) (by decide)).trans w3_2a8), ((K4_L.w32 (by decide) (by decide)).trans w3_2ac), ((K4_L.w32 (by decide) (by decide)).trans w3_1608), ((K4_L.w32 (by decide) (by decide)).trans w3_160c), ((K4_L.w32 (by decide) (by decide)).trans w3_1610), ((K4_L.w32 (by decide) (by decide)).trans w3_1614), ((K4_L.w32 (by decide) (by decide)).trans w3_1618), ((K4_L.w32 (by decide) (by decide)).trans w3_161c), ((K4_L.w32 (by decide) (by decide)).trans w3_1620), ((K4_L.w32 (by decide) (by decide)).trans w3_1624), ((K4_L.w32 (by decide) (by decide)).trans w3_1628), ((K4_L.w32 (by decide) (by decide)).trans w3_162c), ((K4_L.w32 (by decide) (by decide)).trans w3_1630), ((K4_L.w32 (by decide) (by decide)).trans w3_1634), ((K4_L.w32 (by decide) (by decide)).trans w3_1638), ((K4_L.w32 (by decide) (by decide)).trans w3_163c), ((K4_L.w32 (by decide) (by decide)).trans w3_1640), ((K4_L.w32 (by decide) (by decide)).trans w3_1644), ((K4_L.w32 (by decide) (by decide)).trans w3_2a0), ((K4_L.w32 (by decide) (by decide)).trans w3_2a4), ((K4_L.w32 (by decide) (by decide)).trans w3_2c0), ((K4_L.w32 (by decide) (by decide)).trans w3_2c4), ((K4_L.w32 (by decide) (by decide)).trans w3_2c8), ((K4_L.w32 (by decide) (by decide)).trans w3_2cc), ((K4_L.w32 (by decide) (by decide)).trans w3_1648), ((K4_L.w32 (by decide) (by decide)).trans w3_164c), ((K4_L.w32 (by decide) (by decide)).trans w3_1650), ((K4_L.w32 (by decide) (by decide)).trans w3_1654), ((K4_L.w32 (by decide) (by decide)).trans w3_158c), ((K4_L.w32 (by decide) (by decide)).trans w3_1590), ((K4_L.w32 (by decide) (by decide)).trans w3_1594), ((K4_L.b8 (by decide) (by decide)).trans b3_a40), ((((K1_L).trans K2_L).trans K3_L).trans K4_L).mono (by decide)⟩)

end C3.RV32.Sv
