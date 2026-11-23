import C3BootProofs.Proofs.SvEntry

/-!
# `sigstore::verify` from its entry to its return

Written by `scripts/gen-sv-entry.py` from `sv_pro` and `sv_verify_72`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Gd

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
/-- **`sigstore::verify`**: called with the bundle at `a1`, the trust root at `a2`, the artifact's digest at `a3`, and the result at `a0`, it returns `Err`, panics, or meets the success condition and returns `Ok`. -/
theorem sv_verify {Me : Word → BitVec 8} {n : Machine} {B : Word}
    (C : CodeIn Me SV sigstoreVerifyCode) (E : SvCode Me) (F : Fr B 0x3830) (s : St Me SV n 0 (reg n))
    (rsp : reg n sp = B + 0x3830) (hb : (reg n a1).toNat % 4 = 0)
    (sb : Sep (reg n a1) 8 (B + BitVec.ofNat 32 0x37FC) 0x34)
    (hret : ((fun k => reg n (savedReg k))) 0 &&& ~~~1 = ((fun k => reg n (savedReg k))) 0)
    (hO : SvOut B (reg n a0))
    (lc_in : SvIn B (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4)).toNat)
    (D0 : P2Data Me)
    (SD0 : SvData Me)
    (H' : ∀ i, i < 4 → ∀ c'_4 q'_4, (c'_4, q'_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (((reg n a2)) + BitVec.ofNat 32 0x3C)) → (SvIn B (q'_4 + 0xFFFFFFFC) 4) ∧ (SvIn B (q'_4 + 0x0) 4) ∧ ((q'_4 + 0xFFFFFFFC).toNat % 4 = 0) ∧ ((q'_4 + 0x0).toNat % 4 = 0) ∧ ((memLoad32 Me (q'_4 + 0xFFFFFFFC)) ≠ 0 → SvIn B (memLoad32 Me (q'_4 + 0xFFFFFFFC)) (memLoad32 Me (q'_4 + 0x0)).toNat))
    (SH0 : SvShaCode Me)
    (KS : SvKSep B)
    (PE0 : PvEnv7 Me)
    (pkp_in : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x3C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4) 4)
    (apk : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x3C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4).toNat % 4 = 0)
    (pk_in : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x3C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (memLoad32 Me (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4)) 0x61)
    (side : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x3C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → ∀ M, PvSide M (memLoad32 Me (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4)) (B + 0x21A0 + BitVec.ofNat 32 0x1020) 48 (B + 0x21A0 + BitVec.ofNat 32 0xD0)
      (B + 0x21A0 + BitVec.ofNat 32 0x100))
    (ts_in : SvIn B ((memLoad32 Me ((reg n a1) + 0x8))) ((memLoad32 Me ((reg n a1) + 0xC))).toNat)
    (he0p_in : SvIn B ((reg n a2) + 0x0) 4)
    (he0l_in : SvIn B ((reg n a2) + 0x4) 4)
    (ae0p : ((reg n a2) + 0x0).toNat % 4 = 0)
    (ae0l : ((reg n a2) + 0x4).toNat % 4 = 0)
    (e0_in : SvRo B (memLoad32 Me ((reg n a2) + 0x0)) (memLoad32 Me ((reg n a2) + 0x4)).toNat)
    (he1p_in : SvIn B ((reg n a2) + 0x8) 4)
    (he1l_in : SvIn B ((reg n a2) + 0xC) 4)
    (ae1p : ((reg n a2) + 0x8).toNat % 4 = 0)
    (ae1l : ((reg n a2) + 0xC).toNat % 4 = 0)
    (e1_in : SvRo B (memLoad32 Me ((reg n a2) + 0x8)) (memLoad32 Me ((reg n a2) + 0xC)).toNat)
    (he2p_in : SvIn B ((reg n a2) + 0x10) 4)
    (he2l_in : SvIn B ((reg n a2) + 0x14) 4)
    (ae2p : ((reg n a2) + 0x10).toNat % 4 = 0)
    (ae2l : ((reg n a2) + 0x14).toNat % 4 = 0)
    (e2_in : SvRo B (memLoad32 Me ((reg n a2) + 0x10)) (memLoad32 Me ((reg n a2) + 0x14)).toNat)
    (he3p_in : SvIn B ((reg n a2) + 0x18) 4)
    (he3l_in : SvIn B ((reg n a2) + 0x1C) 4)
    (ae3p : ((reg n a2) + 0x18).toNat % 4 = 0)
    (ae3l : ((reg n a2) + 0x1C).toNat % 4 = 0)
    (e3_in : SvRo B (memLoad32 Me ((reg n a2) + 0x18)) (memLoad32 Me ((reg n a2) + 0x1C)).toNat)
    (he4p_in : SvIn B ((reg n a2) + 0x20) 4)
    (he4l_in : SvIn B ((reg n a2) + 0x24) 4)
    (ae4p : ((reg n a2) + 0x20).toNat % 4 = 0)
    (ae4l : ((reg n a2) + 0x24).toNat % 4 = 0)
    (e4_in : SvRo B (memLoad32 Me ((reg n a2) + 0x20)) (memLoad32 Me ((reg n a2) + 0x24)).toNat)
    (htsp_in : SvIn B ((reg n a1) + 0x8) 4)
    (htsl_in : SvIn B ((reg n a1) + 0xC) 4)
    (atsp : ((reg n a1) + 0x8).toNat % 4 = 0)
    (atsl : ((reg n a1) + 0xC).toNat % 4 = 0)
    (EC0 : SvEcCode Me)
    (IC0 : SvIvCode Me)
    (UC0 : SvUpCode Me)
    (BG0 : BGEnv Me)
    (RS : SvRoSep B)
    (BY0 : BYEnv Me)
    (dg_in : SvIn B (reg n a3) 32)
    (UE0 : CodeIn Me (BitVec.ofNat 32 uint8EqAddress) uint8EqCode)
    (N80 : CodeIn Me (BitVec.ofNat 32 norm8Address) norm8Code)
    (PM0 : CodeIn Me (BitVec.ofNat 32 p256ScalarMulAddress) p256ScalarMulCode)
    (WM0 : CodeIn Me (BitVec.ofNat 32 wideMulAddress) wideMulCode)
    (PT0 : SvPtCode Me)
    (WN0 : SvWnCode Me)
    (ME : MlEnv Me)
    (P2C0 : P2Code Me)
    (GDC0 : C3.RV32.Gd.GdCode Me)
    (P2D0 : P2Data Me)
    (SC0 : CodeIn Me (BitVec.ofNat 32 p256ScalarCtEqAddress) p256ScalarCtEqCode)
    (hidC : CodeIn Me (BitVec.ofNat 32 p256IdentityAddress) p256IdentityData)
    (GD : CodeIn Me (BitVec.ofNat 32 p256GMontAddress) p256GMontData)
    (OD : CodeIn Me (BitVec.ofNat 32 p256MontOneAddress) p256MontOneData)
    (AD : CodeIn Me (BitVec.ofNat 32 p256AffineIdXAddress) p256AffineIdXData)
    (hzi : ∀ Z τd_2 τf_2 Dz_2 Fz_2, τd_2 ≤ 1 → τf_2 ≤ 1 → sgnVal τf_2 Fz_2 = (p256Sz Me Z).f → sgnVal τd_2 Dz_2 = (p256Sz Me Z).d →
        normVal8 τd_2 τf_2 Dz_2 (accV Me (BitVec.ofNat 32 0x3FCC4B38) 8) < p256)
    (c0_in : SvIn B ((memLoad32 Me ((reg n a1) + 0x20))) ((memLoad32 Me ((reg n a1) + 0x24))).toNat)
    (hc0p_in : SvIn B ((reg n a1) + 0x20) 4)
    (hc0l_in : SvIn B ((reg n a1) + 0x24) 4)
    (ac0p : ((reg n a1) + 0x20).toNat % 4 = 0)
    (ac0l : ((reg n a1) + 0x24).toNat % 4 = 0)
    (D0' : SvData Me)
    (H'' : ∀ i, i < 4 → ∀ c'_5_3 q'_5_3, (c'_5_3, q'_5_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (((reg n a2)) + BitVec.ofNat 32 0x198)) → (SvIn B (q'_5_3 + 0x20) 4) ∧ (SvIn B (q'_5_3 + 0x24) 4) ∧ ((q'_5_3 + 0x20).toNat % 4 = 0) ∧ ((q'_5_3 + 0x24).toNat % 4 = 0) ∧ ((memLoad32 Me (q'_5_3 + 0x20)) ≠ 0 → SvIn B (memLoad32 Me (q'_5_3 + 0x20)) (memLoad32 Me (q'_5_3 + 0x24)).toNat))
    (S2 : SvSha2Code Me)
    (KS' : SvK2Sep B)
    (pkp_in' : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x198)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x18) 4)
    (apk' : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x198)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x18).toNat % 4 = 0)
    (pk_in' : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x198)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (memLoad32 Me (((y1) + BitVec.ofNat 32 0x20) + 0x18)) 0x61)
    (side' : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x198)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → ∀ M, PvSide M (memLoad32 Me (((y1) + BitVec.ofNat 32 0x20) + 0x18)) (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 (B + 0x21A0 + BitVec.ofNat 32 0xA40)
      (B + 0x21A0 + BitVec.ofNat 32 0xA70))
    (CK0 : SvCkCode Me)
    (ckp_in4 : SvIn B ((reg n a1) + 0x18) 4)
    (ckl_in4 : SvIn B ((reg n a1) + 0x1C) 4)
    (a_ckp : ((reg n a1) + 0x18).toNat % 4 = 0)
    (a_ckl : ((reg n a1) + 0x1C).toNat % 4 = 0)
    (ck_in : SvIn B (memLoad32 Me ((reg n a1) + 0x18)) (memLoad32 Me ((reg n a1) + 0x1C)).toNat)
    (H''' : ∀ i, i < 8 → ∀ c'_3_4 q'_3_4 w80'_3_4, (c'_3_4, q'_3_4, w80'_3_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2.1)) + BitVec.ofNat 32 0x20, (memLoad32 Me ((s.2.1) + 0x20)))) i ((BitVec.ofNat 32 0x100), (((reg n a2)) + BitVec.ofNat 32 0x98), (reg n a2)) → (SvIn B (q'_3_4 + 0x20) 4) ∧ (SvIn B (q'_3_4 + 0x24) 4) ∧ ((q'_3_4 + 0x20).toNat % 4 = 0) ∧ ((q'_3_4 + 0x24).toNat % 4 = 0) ∧ ((memLoad32 Me (q'_3_4 + 0x20)) ≠ 0 → SvIn B (memLoad32 Me (q'_3_4 + 0x20)) (memLoad32 Me (q'_3_4 + 0x24)).toNat))
    (KS'' : SvK2Sep B)
    (kp_in4 : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 Me (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), (((reg n a2)) + BitVec.ofNat 32 0x98), (reg n a2)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x18) 4)
    (kw_in4 : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 Me (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), (((reg n a2)) + BitVec.ofNat 32 0x98), (reg n a2)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x1C) 4)
    (a_kp : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 Me (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), (((reg n a2)) + BitVec.ofNat 32 0x98), (reg n a2)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x18).toNat % 4 = 0)
    (a_kw : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 Me (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), (((reg n a2)) + BitVec.ofNat 32 0x98), (reg n a2)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x1C).toNat % 4 = 0)
    (kp_in : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 Me (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), (((reg n a2)) + BitVec.ofNat 32 0x98), (reg n a2)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (memLoad32 Me (((y1) + BitVec.ofNat 32 0x20) + 0x18)) 32)
    (EE0 : EvEnv Me)
    (hiv : (s5Hv Me (BitVec.ofNat 32 0x3FCC4AF8)).toList = Sha512.h0)
    (pk_in'' : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 Me (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), (((reg n a2)) + BitVec.ofNat 32 0x98), (reg n a2)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (memLoad32 Me (((y1) + BitVec.ofNat 32 0x20) + 0x18)) 32)
    (lid_in : ∀ i, i < 8 → ∀ y0 y1 y2, (y0, y1, y2) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2.1 + BitVec.ofNat 32 0x20, (memLoad32 Me (s.2.1 + 0x20)))) i ((BitVec.ofNat 32 0x100), (((reg n a2)) + BitVec.ofNat 32 0x98), (reg n a2)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + BitVec.ofNat 32 0x5) 19)
    (lih_in : SvIn B ((reg n a1) + 0x2C) 4)
    (lil_in : SvIn B ((reg n a1) + 0x28) 4)
    (a_lih : ((reg n a1) + 0x2C).toNat % 4 = 0)
    (a_lil : ((reg n a1) + 0x28).toNat % 4 = 0)
    (RK0 : SvRkCode Me)
    (dgi_in : SvIn B (reg n a3) 32)
    (pp_in4 : SvIn B ((reg n a1) + 0x10) 4)
    (pl_in4 : SvIn B ((reg n a1) + 0x14) 4)
    (a_pp : ((reg n a1) + 0x10).toNat % 4 = 0)
    (a_pl : ((reg n a1) + 0x14).toNat % 4 = 0)
    (pp_in : SvIn B (memLoad32 Me ((reg n a1) + 0x10)) (memLoad32 Me ((reg n a1) + 0x14)).toNat)
    (ii2h : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x3C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8) 4)
    (ai2h : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x3C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8).toNat % 4 = 0)
    (ii2l : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x3C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE4) 4)
    (ai2l : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x3C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE4).toNat % 4 = 0)
    (ii3h : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x3C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0) 4)
    (ai3h : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x3C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0).toNat % 4 = 0)
    (ii3l : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x3C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFEC) 4)
    (ai3l : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x3C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFEC).toNat % 4 = 0)
    (it4h : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x198)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xC) 4)
    (at4h : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x198)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xC).toNat % 4 = 0)
    (it4l : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x198)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x8) 4)
    (at4l : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x198)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x8).toNat % 4 = 0)
    (it5h : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x198)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x14) 4)
    (at5h : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x198)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x14).toNat % 4 = 0)
    (it5l : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x198)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x10) 4)
    (at5l : ∀ i, i < 4 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((reg n a2) + BitVec.ofNat 32 0x198)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x10).toNat % 4 = 0)
    (hOk : SvOutOk B (reg n a0)) :
    SvErrRet B (reg n a0) (fun k => reg n (savedReg k)) n ∨ Panics n ∨
    (∃ t_1_1_1, derElement 0x30 (memBytes Me (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4)).toNat) = .ok t_1_1_1 ∧ (memLoad32 Me (reg n a1 + 4)) - BitVec.ofNat 32 (t_1_1_1.header + t_1_1_1.len) = 0 ∧
      ∃ tl1_2_1_1, derElement 0x30 (memBytes Me (((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) ((BitVec.ofNat 32 t_1_1_1.len)).toNat) = .ok tl1_2_1_1 ∧
      ∃ tl8_2_1_1, derElement 0x30 (memBytes Me ((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) (((BitVec.ofNat 32 t_1_1_1.len)) - BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)).toNat) = .ok tl8_2_1_1 ∧
      ∃ tl16_2_1_1, derElement 3 (memBytes Me (((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) + BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) ((((BitVec.ofNat 32 t_1_1_1.len)) - BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) - BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)).toNat) = .ok tl16_2_1_1 ∧
      ∃ bp16_2_1_1 bl16_2_1_1, derBitsOf (memBytes Me (((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) + BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) ((((BitVec.ofNat 32 t_1_1_1.len)) - BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) - BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)).toNat) (((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) + BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) (.ok tl16_2_1_1) = .ok (bp16_2_1_1, bl16_2_1_1) ∧
      (((((BitVec.ofNat 32 t_1_1_1.len)) - BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) - BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) - BitVec.ofNat 32 (tl16_2_1_1.header + tl16_2_1_1.len) = 0) ∧
      ∃ tl29_2_1_1, derOptRes 0xA0 (memBytes Me ((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) (BitVec.ofNat 32 tl1_2_1_1.len).toNat) = some (.ok tl29_2_1_1) ∧
      derIntIsOf Me (memBytes Me (((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 tl29_2_1_1.header) (BitVec.ofNat 32 tl29_2_1_1.len).toNat) (((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 tl29_2_1_1.header) (derElement 2 (memBytes Me (((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 tl29_2_1_1.header) (BitVec.ofNat 32 tl29_2_1_1.len).toNat)) ((BitVec.ofNat 32 0x2).extractLsb' 0 8) = .ok true ∧
      ∃ te43_2_1_1, derElement 2 (memBytes Me (((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 tl29_2_1_1.header) (BitVec.ofNat 32 tl29_2_1_1.len).toNat) = .ok te43_2_1_1 ∧
      ((BitVec.ofNat 32 tl29_2_1_1.len) - BitVec.ofNat 32 (te43_2_1_1.header + te43_2_1_1.len) = 0) ∧
      ∃ tl2_3_1_1, derElement 2 (memBytes Me ((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) (((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))).toNat) = .ok tl2_3_1_1 ∧
      ∃ ip2_3_1_1 il2_3_1_1, derPosIntOf (memBytes Me ((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) (((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))).toNat) ((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) (.ok tl2_3_1_1) = .ok (ip2_3_1_1, il2_3_1_1) ∧
      ((il2_3_1_1).toNat ≤ 20) ∧
      ∃ tl9_3_1_1, derElement 0x30 (memBytes Me (((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) ((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) - BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)).toNat) = .ok tl9_3_1_1 ∧
      ∃ op19_3_1_1 ol19_3_1_1, derAlgOf Me (((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) (tl9_3_1_1.header + tl9_3_1_1.len) = .ok ((op19_3_1_1, ol19_3_1_1), none) ∧
      (memBytes Me op19_3_1_1 ol19_3_1_1 = memBytes Me (BitVec.ofNat 32 0x3FCC4840) 8) ∧
      ∃ tl6_4_1_1, derElement 0x30 (memBytes Me (((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) ((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) - BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) - BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))).toNat) = .ok tl6_4_1_1 ∧
      ∃ tl13_4_1_1, derElement 0x30 (memBytes Me ((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) (((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) - BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) - BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) - BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)).toNat) = .ok tl13_4_1_1 ∧
      ∃ tm22_4_1_1 rs22_4_1_1, readTime (memBytes Me (((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 tl13_4_1_1.header) (tl13_4_1_1.len)) = some (tm22_4_1_1, rs22_4_1_1) ∧
      ∃ tm31_4_1_1 rs31_4_1_1, readTime rs22_4_1_1 = some (tm31_4_1_1, rs31_4_1_1) ∧
      (rs31_4_1_1 = []) ∧
      ∃ tl2_5_1_1, derElement 0x30 (memBytes Me ((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) (((((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) - BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) - BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) - BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) - BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))).toNat) = .ok tl2_5_1_1 ∧
      ∃ tl6_5_1_1, derElement 0x30 (memBytes Me (((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) ((((((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) - BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) - BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) - BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) - BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) - BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)).toNat) = .ok tl6_5_1_1 ∧
      ∃ op15_5_1_1 ol15_5_1_1 prp15_5_1_1 pu15_5_1_1, derAlgOf Me ((((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) (tl6_5_1_1.len) = .ok ((op15_5_1_1, ol15_5_1_1), some (prp15_5_1_1, pu15_5_1_1)) ∧
      ∃ ta15_5_1_1, derElement 0x30 (memBytes Me ((((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) (tl6_5_1_1.len)) = .ok ta15_5_1_1 ∧
      (BitVec.ofNat 8 pu15_5_1_1.tag = BitVec.ofNat 8 6) ∧
      (memBytes Me (prp15_5_1_1 + BitVec.ofNat 32 pu15_5_1_1.header) pu15_5_1_1.len = memBytes Me (BitVec.ofNat 32 0x3FCC4848) 8) ∧
      (memBytes Me op15_5_1_1 ol15_5_1_1 = memBytes Me (BitVec.ofNat 32 0x3FCC4914) 7) ∧
      ∃ tl35_5_1_1, derElement 3 (memBytes Me (((((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) + BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)) ((BitVec.ofNat 32 (tl6_5_1_1.len)) - BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)).toNat) = .ok tl35_5_1_1 ∧
      ∃ bp35_5_1_1 bl35_5_1_1, derBitsOf (memBytes Me (((((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) + BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)) ((BitVec.ofNat 32 (tl6_5_1_1.len)) - BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)).toNat) (((((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) + BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)) (.ok tl35_5_1_1) = .ok (bp35_5_1_1, bl35_5_1_1) ∧
      (bl35_5_1_1 = BitVec.ofNat 32 0x41) ∧
      (((BitVec.ofNat 32 (tl6_5_1_1.len)) - BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)) - BitVec.ofNat 32 (tl35_5_1_1.header + tl35_5_1_1.len) = 0) ∧
      (Me bp35_5_1_1 = BitVec.ofNat 8 4) ∧
      (GsOk Me bp35_5_1_1) ∧
      ∃ tl9_6_1_1, derOptRes 0xA3 (memBytes Me (((((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) ((((((((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) - BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) - BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) - BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) - BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) - BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) - BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))).toNat) = some (.ok tl9_6_1_1) ∧
      (((((((((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) - BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) - BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) - BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) - BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) - BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) - BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) - BitVec.ofNat 32 (tl9_6_1_1.header + tl9_6_1_1.len) = 0) ∧
      ∃ tl25_6_1_1, derElement 0x30 (memBytes Me ((((((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) + BitVec.ofNat 32 tl9_6_1_1.header) (BitVec.ofNat 32 tl9_6_1_1.len).toNat) = .ok tl25_6_1_1 ∧
      ((BitVec.ofNat 32 tl9_6_1_1.len) - BitVec.ofNat 32 (tl25_6_1_1.header + tl25_6_1_1.len) = 0) ∧
      ∃ u0_1 u1_1 u2_1, ∃ k_2_1 f30'_2_1 f34'_2_1 rem'_2_1 cur'_2_1 sl0'_2_1 sl1'_2_1 sl2'_2_1 sl3'_2_1 sl4'_2_1 sl5'_2_1 sl6'_2_1 sl7'_2_1 sl8'_2_1 sl9'_2_1, svChain (sv_extStep B (reg n a0) (reg n a1) ((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header) bp35_5_1_1 (BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) (memLoad32 Me (reg n a1 + 4)) (((((((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) + BitVec.ofNat 32 tl9_6_1_1.header) + BitVec.ofNat 32 tl25_6_1_1.header) (BitVec.ofNat 32 tl25_6_1_1.len) (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 % 2 ^ 32)) ((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len)) ((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) (BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) bl16_2_1_1 (memLoad32 Me (reg n a1)) (((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) (BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len)) (BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) bp16_2_1_1 (reg n a2) (reg n a3) ((fun k => reg n (savedReg k))) Me) k_2_1 ((BitVec.ofNat 32 0x0), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 tl25_6_1_1.len), (((((((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len))) + BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) + BitVec.ofNat 32 (tl13_4_1_1.header + tl13_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) + BitVec.ofNat 32 tl9_6_1_1.header) + BitVec.ofNat 32 tl25_6_1_1.header), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 tl25_6_1_1.len), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 (tl25_6_1_1.header + tl25_6_1_1.len)), (BitVec.ofNat 32 0x0), (u0_1), (BitVec.ofNat 32 0x0), (u1_1), (BitVec.ofNat 32 0x0), (u2_1)) (f30'_2_1, f34'_2_1, rem'_2_1, cur'_2_1, sl0'_2_1, sl1'_2_1, sl2'_2_1, sl3'_2_1, sl4'_2_1, sl5'_2_1, sl6'_2_1, sl7'_2_1, sl8'_2_1, sl9'_2_1) ∧
      rem'_2_1 = 0 ∧ (sl0'_2_1 = 0 ∨ SvIn B sl0'_2_1 sl1'_2_1.toNat) ∧ (sl2'_2_1 = 0 ∨ SvIn B sl2'_2_1 sl3'_2_1.toNat) ∧ (sl4'_2_1 = 0 ∨ SvIn B sl4'_2_1 sl5'_2_1.toNat) ∧ (sl6'_2_1 = 0 ∨ SvIn B sl6'_2_1 sl7'_2_1.toNat) ∧ (sl8'_2_1 = 0 ∨ SvIn B sl8'_2_1 sl9'_2_1.toNat) ∧
      (sl0'_2_1 ≠ 0) ∧ (sl2'_2_1 ≠ 0) ∧ (sl4'_2_1 ≠ 0) ∧ (sl6'_2_1 ≠ 0) ∧ ((if BitVec.ult 0 (sl8'_2_1) then (1 : Word) else 0) &&& ((f30'_2_1) &&& (f34'_2_1)) ≠ 0) ∧ (memBytes Me ((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) ((BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)).toNat) = memBytes Me (((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) ((BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len)).toNat)) ∧ ∃ sr43_2_1 ss43_2_1, ecdsaSigOf 48 Me (bp16_2_1_1) ((bl16_2_1_1.toNat)) = .ok (sr43_2_1, ss43_2_1) ∧
      ∃ k_4_1, k_4_1 < 4 ∧
      (∀ i, i < k_4_1 → ∀ c'_4_1 q'_4_1, (c'_4_1, q'_4_1) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (((reg n a2)) + BitVec.ofNat 32 0x3C)) → ¬ (memBytes Me (memLoad32 Me (q'_4_1 + 0xFFFFFFFC)) (memLoad32 Me (q'_4_1 + 0x0)).toNat = memBytes Me ((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len)) (BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)).toNat)) ∧
      ∃ c'_4_1 q'_4_1, (c'_4_1, q'_4_1) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) k_4_1 ((BitVec.ofNat 32 0x80), (((reg n a2)) + BitVec.ofNat 32 0x3C)) ∧ (memBytes Me (memLoad32 Me (q'_4_1 + 0xFFFFFFFC)) (memLoad32 Me (q'_4_1 + 0x0)).toNat = memBytes Me ((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len)) (BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)).toNat) ∧
      ((memLoad32 Me (q'_4_1 + 0xFFFFFFFC)) ≠ 0) ∧
      ∃ pv_5_1, SvPvRes Me (memLoad32 Me (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4)) (B + 0x21A0 + BitVec.ofNat 32 0x1020) 48 (sha384 (memBytes Me ((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header) (BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)).toNat)) (B + 0x21A0 + BitVec.ofNat 32 0xD0) (B + 0x21A0 + BitVec.ofNat 32 0x100) sr43_2_1 ss43_2_1 (some pv_5_1) ∧
      (pv_5_1 ≠ 0) ∧
      (memBytes Me sl0'_2_1 sl1'_2_1.toNat = memBytes Me (memLoad32 Me ((reg n a2) + 0x0)) (memLoad32 Me ((reg n a2) + 0x4)).toNat) ∧
      (memBytes Me sl2'_2_1 sl3'_2_1.toNat = memBytes Me (memLoad32 Me ((reg n a2) + 0x8)) (memLoad32 Me ((reg n a2) + 0xC)).toNat) ∧
      (memBytes Me sl4'_2_1 sl5'_2_1.toNat = memBytes Me (memLoad32 Me ((reg n a2) + 0x10)) (memLoad32 Me ((reg n a2) + 0x14)).toNat) ∧
      (memBytes Me sl6'_2_1 sl7'_2_1.toNat = memBytes Me (memLoad32 Me ((reg n a2) + 0x18)) (memLoad32 Me ((reg n a2) + 0x1C)).toNat) ∧
      (memBytes Me sl8'_2_1 sl9'_2_1.toNat = memBytes Me (memLoad32 Me ((reg n a2) + 0x20)) (memLoad32 Me ((reg n a2) + 0x24)).toNat) ∧
      ∃ tl49_1_6_1, derElement 0x30 (memBytes Me ((memLoad32 Me ((reg n a1) + 0x8))) ((memLoad32 Me ((reg n a1) + 0xC))).toNat) = .ok tl49_1_6_1 ∧
      (((memLoad32 Me ((reg n a1) + 0xC))) - BitVec.ofNat 32 (tl49_1_6_1.header + tl49_1_6_1.len) = 0) ∧
      ∃ bs9_2_6_1, derScalarOf 32 (memBytes Me (((memLoad32 Me ((reg n a1) + 0x8))) + BitVec.ofNat 32 tl49_1_6_1.header) (BitVec.ofNat 32 tl49_1_6_1.len).toNat) (((memLoad32 Me ((reg n a1) + 0x8))) + BitVec.ofNat 32 tl49_1_6_1.header) (derElement 2 (memBytes Me (((memLoad32 Me ((reg n a1) + 0x8))) + BitVec.ofNat 32 tl49_1_6_1.header) (BitVec.ofNat 32 tl49_1_6_1.len).toNat)) = .ok bs9_2_6_1 ∧
      ∃ te9_2_6_1, derElement 2 (memBytes Me (((memLoad32 Me ((reg n a1) + 0x8))) + BitVec.ofNat 32 tl49_1_6_1.header) (BitVec.ofNat 32 tl49_1_6_1.len).toNat) = .ok te9_2_6_1 ∧
      ∃ bs16_2_6_1, derScalarOf 32 (memBytes Me ((((memLoad32 Me ((reg n a1) + 0x8))) + BitVec.ofNat 32 tl49_1_6_1.header) + BitVec.ofNat 32 (te9_2_6_1.header + te9_2_6_1.len)) ((BitVec.ofNat 32 tl49_1_6_1.len) - BitVec.ofNat 32 (te9_2_6_1.header + te9_2_6_1.len)).toNat) ((((memLoad32 Me ((reg n a1) + 0x8))) + BitVec.ofNat 32 tl49_1_6_1.header) + BitVec.ofNat 32 (te9_2_6_1.header + te9_2_6_1.len)) (derElement 2 (memBytes Me ((((memLoad32 Me ((reg n a1) + 0x8))) + BitVec.ofNat 32 tl49_1_6_1.header) + BitVec.ofNat 32 (te9_2_6_1.header + te9_2_6_1.len)) ((BitVec.ofNat 32 tl49_1_6_1.len) - BitVec.ofNat 32 (te9_2_6_1.header + te9_2_6_1.len)).toNat)) = .ok bs16_2_6_1 ∧
      ∃ te16_2_6_1, derElement 2 (memBytes Me ((((memLoad32 Me ((reg n a1) + 0x8))) + BitVec.ofNat 32 tl49_1_6_1.header) + BitVec.ofNat 32 (te9_2_6_1.header + te9_2_6_1.len)) ((BitVec.ofNat 32 tl49_1_6_1.len) - BitVec.ofNat 32 (te9_2_6_1.header + te9_2_6_1.len)).toNat) = .ok te16_2_6_1 ∧
      (((BitVec.ofNat 32 tl49_1_6_1.len) - BitVec.ofNat 32 (te9_2_6_1.header + te9_2_6_1.len)) - BitVec.ofNat 32 (te16_2_6_1.header + te16_2_6_1.len) = 0) ∧
      (((inScalarRange (b32 bs9_2_6_1) (memBytes Me (BitVec.ofNat 32 0x3FCC4288) 32) = true) ∧ (inScalarRange (b32 bs16_2_6_1) (memBytes Me (BitVec.ofNat 32 0x3FCC4288) 32) = true) ∧ (Me bp35_5_1_1 = 4) ∧ True) ∧ ((GsOk Me bp35_5_1_1) ∧ (beNat (b32 bs9_2_6_1) < C3.p256.n) ∧ (beNat (b32 bs16_2_6_1) < C3.p256.n) ∧ (beNat (b32 bs9_2_6_1) ≠ 0) ∧ (beNat (b32 bs16_2_6_1) ≠ 0) ∧ True)) ∧
      ∃ σd_2 σf_2 Dv_2 Fv_2, σd_2 ≤ 1 ∧ σf_2 ≤ 1 ∧ sgnVal σf_2 Fv_2 = (p256Sf Me bs16_2_6_1).f ∧ sgnVal σd_2 Dv_2 = (p256Sf Me bs16_2_6_1).d ∧
      (((Fv_2 = accV Me (BitVec.ofNat 32 0x3FCC42E8) 8)) ∧ True) ∧ ∃ stm_2, mlMain2 (tbl2 (accV Me (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x0) 8, accV Me (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x20) 8, accV Me (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x40) 8)) (tbl2 ((gsVal Me bp35_5_1_1 1 * 2 ^ 256 % p256), (gsVal Me bp35_5_1_1 0x21 * 2 ^ 256 % p256), (accV Me (BitVec.ofNat 32 0x3FCC43A8) 8))) (wnafBytes (wnafGo ((psmVal (((beNat (memBytes Me ((reg n a3)) 32) % C3.p256.n)) * ((normVal8 σd_2 σf_2 Dv_2 (accV Me (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0) 0x101) (wnafBytes (wnafGo ((psmVal (((beNat (b32 bs9_2_6_1))) * ((normVal8 σd_2 σf_2 Dv_2 (accV Me (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0) 0x101) (max (wnafGo ((psmVal (((beNat (memBytes Me ((reg n a3)) 32) % C3.p256.n)) * ((normVal8 σd_2 σf_2 Dv_2 (accV Me (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length (wnafGo ((psmVal (((beNat (b32 bs9_2_6_1))) * ((normVal8 σd_2 σf_2 Dv_2 (accV Me (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length) = some stm_2 ∧
      ∃ τd_2 τf_2 Dz_2 Fz_2, τd_2 ≤ 1 ∧ τf_2 ≤ 1 ∧ sgnVal τf_2 Fz_2 = (p256Sz Me stm_2.1.2.2).f ∧ sgnVal τd_2 Dz_2 = (p256Sz Me stm_2.1.2.2).d ∧
      ((((beNat (b32 bs9_2_6_1)) = (p2fm ((if (((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV Me (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm ((stm_2.1.1)) ((if ((((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV Me (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV Me (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV Me (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 τd_2 τf_2 Dz_2 (accV Me (BitVec.ofNat 32 0x3FCC4B38) 8) else 0) else 0) else 0)) else accV Me (BitVec.ofNat 32 0x3FCC442C) 8)) 1) % C3.p256.n)) ∧ True) ∧
      ∃ tl10_1_1_3, derElement 0x30 (memBytes Me ((memLoad32 Me ((reg n a1) + 0x20))) ((memLoad32 Me ((reg n a1) + 0x24))).toNat) = .ok tl10_1_1_3 ∧
      (((memLoad32 Me ((reg n a1) + 0x24))) - BitVec.ofNat 32 (tl10_1_1_3.header + tl10_1_1_3.len) = 0) ∧
      ∃ tl22_1_1_3, derElement 0x30 (memBytes Me (((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) (BitVec.ofNat 32 tl10_1_1_3.len).toNat) = .ok tl22_1_1_3 ∧
      derIntIsOf Me (memBytes Me ((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 tl22_1_1_3.header) (BitVec.ofNat 32 tl22_1_1_3.len).toNat) ((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 tl22_1_1_3.header) (derElement 2 (memBytes Me ((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 tl22_1_1_3.header) (BitVec.ofNat 32 tl22_1_1_3.len).toNat)) ((BitVec.ofNat 32 0x0).extractLsb' 0 8) = .ok true ∧
      ∃ te33_1_1_3, derElement 2 (memBytes Me ((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 tl22_1_1_3.header) (BitVec.ofNat 32 tl22_1_1_3.len).toNat) = .ok te33_1_1_3 ∧
      ((BitVec.ofNat 32 tl22_1_1_3.len) - BitVec.ofNat 32 (te33_1_1_3.header + te33_1_1_3.len) = 0) ∧
      ∃ tl41_1_1_3, derElement 0x30 (memBytes Me ((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) ((BitVec.ofNat 32 tl10_1_1_3.len) - BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)).toNat) = .ok tl41_1_1_3 ∧
      (((BitVec.ofNat 32 tl10_1_1_3.len) - BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) - BitVec.ofNat 32 (tl41_1_1_3.header + tl41_1_1_3.len) = 0) ∧
      ∃ op53_1_1_3 ol53_1_1_3, derContent (((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) (derOid (memBytes Me (((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) (BitVec.ofNat 32 tl41_1_1_3.len).toNat)) = .ok (op53_1_1_3, ol53_1_1_3) ∧
      ∃ to53_1_1_3, derOid (memBytes Me (((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) (BitVec.ofNat 32 tl41_1_1_3.len).toNat) = .ok to53_1_1_3 ∧
      (memBytes Me op53_1_1_3 ol53_1_1_3.toNat = memBytes Me (BitVec.ofNat 32 0x3FCC4859) 9) ∧
      ∃ tl2_2_1_3, derElement 0xA0 (memBytes Me (((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) (((BitVec.ofNat 32 tl41_1_1_3.len) - BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))).toNat) = .ok tl2_2_1_3 ∧
      ((((BitVec.ofNat 32 tl41_1_1_3.len) - BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) - BitVec.ofNat 32 (tl2_2_1_3.header + tl2_2_1_3.len) = 0) ∧
      ∃ tl15_2_1_3, derElement 0x30 (memBytes Me ((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) (BitVec.ofNat 32 tl2_2_1_3.len).toNat) = .ok tl15_2_1_3 ∧
      ((BitVec.ofNat 32 tl2_2_1_3.len) - BitVec.ofNat 32 (tl15_2_1_3.header + tl15_2_1_3.len) = 0) ∧
      derIntIsOf Me (memBytes Me (((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) (BitVec.ofNat 32 tl15_2_1_3.len).toNat) (((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) (derElement 2 (memBytes Me (((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) (BitVec.ofNat 32 tl15_2_1_3.len).toNat)) ((BitVec.ofNat 32 0x3).extractLsb' 0 8) = .ok true ∧
      ∃ te26_2_1_3, derElement 2 (memBytes Me (((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) (BitVec.ofNat 32 tl15_2_1_3.len).toNat) = .ok te26_2_1_3 ∧
      ∃ tl32_2_1_3, derElement 0x31 (memBytes Me ((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) ((BitVec.ofNat 32 tl15_2_1_3.len) - BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)).toNat) = .ok tl32_2_1_3 ∧
      isSha256Of Me (((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 tl32_2_1_3.header) (BitVec.ofNat 32 tl32_2_1_3.len).toNat = .ok true ∧
      ∃ te41_2_1_3, derElement 0x30 (memBytes Me (((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 tl32_2_1_3.header) (BitVec.ofNat 32 tl32_2_1_3.len).toNat) = .ok te41_2_1_3 ∧
      ((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te41_2_1_3.header + te41_2_1_3.len) = 0) ∧
      ∃ tl49_2_1_3, derElement 0x30 (memBytes Me (((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) (((BitVec.ofNat 32 tl15_2_1_3.len) - BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) - BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)).toNat) = .ok tl49_2_1_3 ∧
      ∃ op58_2_1_3 ol58_2_1_3, derContent ((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 tl49_2_1_3.header) (derOid (memBytes Me ((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 tl49_2_1_3.header) (BitVec.ofNat 32 tl49_2_1_3.len).toNat)) = .ok (op58_2_1_3, ol58_2_1_3) ∧
      ∃ to58_2_1_3, derOid (memBytes Me ((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 tl49_2_1_3.header) (BitVec.ofNat 32 tl49_2_1_3.len).toNat) = .ok to58_2_1_3 ∧
      (memBytes Me op58_2_1_3 ol58_2_1_3.toNat = memBytes Me (BitVec.ofNat 32 0x3FCC4862) 11) ∧
      ∃ tl2_3_1_3, derOptRes 0xA0 (memBytes Me ((((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 tl49_2_1_3.header) + BitVec.ofNat 32 (to58_2_1_3.header + to58_2_1_3.len))) (((BitVec.ofNat 32 tl49_2_1_3.len) - BitVec.ofNat 32 (to58_2_1_3.header + to58_2_1_3.len))).toNat) = some (.ok tl2_3_1_3) ∧
      ((((BitVec.ofNat 32 tl49_2_1_3.len) - BitVec.ofNat 32 (to58_2_1_3.header + to58_2_1_3.len))) - BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len) = 0) ∧
      ∃ vp23_3_1_3 vl23_3_1_3, derContent (((((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 tl49_2_1_3.header) + BitVec.ofNat 32 (to58_2_1_3.header + to58_2_1_3.len))) + BitVec.ofNat 32 tl2_3_1_3.header) (derElement 4 (memBytes Me (((((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 tl49_2_1_3.header) + BitVec.ofNat 32 (to58_2_1_3.header + to58_2_1_3.len))) + BitVec.ofNat 32 tl2_3_1_3.header) (BitVec.ofNat 32 tl2_3_1_3.len).toNat)) = .ok (vp23_3_1_3, vl23_3_1_3) ∧
      ∃ te23_3_1_3, derElement 4 (memBytes Me (((((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 tl49_2_1_3.header) + BitVec.ofNat 32 (to58_2_1_3.header + to58_2_1_3.len))) + BitVec.ofNat 32 tl2_3_1_3.header) (BitVec.ofNat 32 tl2_3_1_3.len).toNat) = .ok te23_3_1_3 ∧
      ((BitVec.ofNat 32 tl2_3_1_3.len) - BitVec.ofNat 32 (te23_3_1_3.header + te23_3_1_3.len) = 0) ∧
      ∃ tsa4_w2a8_4_1_3 : Word, ∃ tsa4_w2ac_4_1_3 : Word, (((derOptRes 0xA0 (memBytes Me (((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))) (((((BitVec.ofNat 32 tl15_2_1_3.len) - BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) - BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) - BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))).toNat) = none) ∧ (((((BitVec.ofNat 32 tl15_2_1_3.len) - BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) - BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) - BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len)) = 0 ∨ (Me (((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len)))).toNat ≠ 0xA1) ∧ tsa4_w2a8_4_1_3 = ((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len)) ∧ tsa4_w2ac_4_1_3 = ((((BitVec.ofNat 32 tl15_2_1_3.len) - BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) - BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) - BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))) ∨ ((¬ (derOptRes 0xA0 (memBytes Me (((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))) (((((BitVec.ofNat 32 tl15_2_1_3.len) - BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) - BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) - BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))).toNat) = none)) ∧ ∃ tl2, derOptRes 0xA0 (memBytes Me (((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))) (((((BitVec.ofNat 32 tl15_2_1_3.len) - BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) - BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) - BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))).toNat) = some (.ok tl2) ∧ ((((((BitVec.ofNat 32 tl15_2_1_3.len) - BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) - BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) - BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0 ∨ (Me ((((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))) + BitVec.ofNat 32 (tl2.header + tl2.len))).toNat ≠ 0xA1) ∧ tsa4_w2a8_4_1_3 = (((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl22_1_1_3.header + tl22_1_1_3.len)) + BitVec.ofNat 32 tl41_1_1_3.header) + BitVec.ofNat 32 (to53_1_1_3.header + to53_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 tl15_2_1_3.header) + BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) + BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) + BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tsa4_w2ac_4_1_3 = (((((BitVec.ofNat 32 tl15_2_1_3.len) - BitVec.ofNat 32 (te26_2_1_3.header + te26_2_1_3.len)) - BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len)) - BitVec.ofNat 32 (tl49_2_1_3.header + tl49_2_1_3.len))) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tsa4_w2a8_4_1_3 tsa4_w2ac_4_1_3.toNat ∧
      ∃ tl2_5_1_3, derElement 0x31 (memBytes Me (tsa4_w2a8_4_1_3) (tsa4_w2ac_4_1_3).toNat) = .ok tl2_5_1_3 ∧
      ((tsa4_w2ac_4_1_3) - BitVec.ofNat 32 (tl2_5_1_3.header + tl2_5_1_3.len) = 0) ∧
      ∃ tl13_5_1_3, derElement 0x30 (memBytes Me ((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) (BitVec.ofNat 32 tl2_5_1_3.len).toNat) = .ok tl13_5_1_3 ∧
      ((BitVec.ofNat 32 tl2_5_1_3.len) - BitVec.ofNat 32 (tl13_5_1_3.header + tl13_5_1_3.len) = 0) ∧
      derIntIsOf Me (memBytes Me (((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) (BitVec.ofNat 32 tl13_5_1_3.len).toNat) (((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) (derElement 2 (memBytes Me (((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) (BitVec.ofNat 32 tl13_5_1_3.len).toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = .ok true ∧
      ∃ te25_5_1_3, derElement 2 (memBytes Me (((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) (BitVec.ofNat 32 tl13_5_1_3.len).toNat) = .ok te25_5_1_3 ∧
      ∃ tl31_5_1_3, derElement 0x30 (memBytes Me ((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) ((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)).toNat) = .ok tl31_5_1_3 ∧
      isSha256Of Me (((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) (((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)).toNat = .ok true ∧
      ∃ te39_5_1_3, derElement 0x30 (memBytes Me (((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) (((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)).toNat) = .ok te39_5_1_3 ∧
      ∃ tl45_5_1_3, derOptRes 0xA0 (memBytes Me ((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) ((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)).toNat) = some (.ok tl45_5_1_3) ∧
      (BitVec.ofNat 32 tl45_5_1_3.len ≠ 0) ∧
      (((BitVec.ofNat 32 tl45_5_1_3.len)).toNat ≤ ((BitVec.ofNat 32 tl45_5_1_3.len)).toNat) ∧
      ∃ tl6_1_2_3, derElement 0x30 (memBytes Me ((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) ((BitVec.ofNat 32 tl45_5_1_3.len)).toNat) = .ok tl6_1_2_3 ∧
      ∃ op15_1_2_3 ol15_1_2_3, derContent (((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) (derOid (memBytes Me (((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) (BitVec.ofNat 32 tl6_1_2_3.len).toNat)) = .ok (op15_1_2_3, ol15_1_2_3) ∧
      ∃ to15_1_2_3, derOid (memBytes Me (((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) (BitVec.ofNat 32 tl6_1_2_3.len).toNat) = .ok to15_1_2_3 ∧
      ∃ tl20_1_2_3, derElement 0x31 (memBytes Me ((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) ((BitVec.ofNat 32 tl6_1_2_3.len) - BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)).toNat) = .ok tl20_1_2_3 ∧
      (((BitVec.ofNat 32 tl6_1_2_3.len) - BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) - BitVec.ofNat 32 (tl20_1_2_3.header + tl20_1_2_3.len) = 0) ∧
      listsOidOf Me (((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header) (((BitVec.ofNat 32 tl45_5_1_3.len)) - ((BitVec.ofNat 32 tl45_5_1_3.len))).toNat (memBytes Me op15_1_2_3 ol15_1_2_3.toNat) = .ok false ∧
      ∃ tsav_r24_2_2_3 : Word, ∃ tsav_w78_2_2_3 : Word, ∃ tsav_w1388_2_2_3 : Word, ∃ tsav_w138c_2_2_3 : Word, (((memBytes Me op15_1_2_3 ol15_1_2_3.toNat = memBytes Me (BitVec.ofNat 32 0x3FCC486E) 9) ∧ ∃ op5 ol5, derContent ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) (derOid (memBytes Me ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat)) = .ok (op5, ol5) ∧ ∃ to5, derOid (memBytes Me ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat) = .ok to5 ∧ (memBytes Me op5 ol5.toNat = memBytes Me (BitVec.ofNat 32 0x3FCC4862) 11) ∧ (((BitVec.ofNat 32 tl20_1_2_3.len)) - BitVec.ofNat 32 (to5.header + to5.len) = 0) ∧ tsav_r24_2_2_3 = (BitVec.ofNat 32 0x0) ∧ tsav_w78_2_2_3 = BitVec.ofNat 32 0x1 ∧ tsav_w1388_2_2_3 = ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) + BitVec.ofNat 32 (to5.header + to5.len) ∧ tsav_w138c_2_2_3 = ((BitVec.ofNat 32 tl20_1_2_3.len)) - BitVec.ofNat 32 (to5.header + to5.len)) ∨ ((¬ (memBytes Me op15_1_2_3 ol15_1_2_3.toNat = memBytes Me (BitVec.ofNat 32 0x3FCC486E) 9)) ∧ (memBytes Me op15_1_2_3 ol15_1_2_3.toNat = memBytes Me (BitVec.ofNat 32 0x3FCC4877) 9) ∧ ∃ vp8 vl8, derContent ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) (derElement 4 (memBytes Me ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat)) = .ok (vp8, vl8) ∧ ∃ te8, derElement 4 (memBytes Me ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat) = .ok te8 ∧ (vl8 = 32) ∧ (((BitVec.ofNat 32 tl20_1_2_3.len)) - BitVec.ofNat 32 (te8.header + te8.len) = 0) ∧ tsav_r24_2_2_3 = vp8 ∧ tsav_w78_2_2_3 = (BitVec.ofNat 32 0x0) ∧ tsav_w1388_2_2_3 = ((((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) + BitVec.ofNat 32 (te8.header + te8.len) ∧ tsav_w138c_2_2_3 = ((BitVec.ofNat 32 tl20_1_2_3.len)) - BitVec.ofNat 32 (te8.header + te8.len)) ∨ ((¬ (memBytes Me op15_1_2_3 ol15_1_2_3.toNat = memBytes Me (BitVec.ofNat 32 0x3FCC486E) 9)) ∧ (¬ (memBytes Me op15_1_2_3 ol15_1_2_3.toNat = memBytes Me (BitVec.ofNat 32 0x3FCC4877) 9)) ∧ tsav_r24_2_2_3 = (BitVec.ofNat 32 0x0) ∧ tsav_w78_2_2_3 = (BitVec.ofNat 32 0x0) ∧ tsav_w1388_2_2_3 = (((((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header) ∧ tsav_w138c_2_2_3 = (BitVec.ofNat 32 tl20_1_2_3.len))) ∧ SvIn B tsav_w1388_2_2_3 tsav_w138c_2_2_3.toNat ∧ (tsav_r24_2_2_3 = 0 ∨ SvIn B tsav_r24_2_2_3 32) ∧
      ∃ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31, ∃ k_3_3 dg'_3_3 flag'_3_3 cp'_3_3 rem'_3_3, svChain (sv_attrStep B (reg n a0) (reg n a1) vl23_3_1_3 (memLoad32 Me (reg n a1 + 4)) (((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header) (BitVec.ofNat 32 tl45_5_1_3.len) (((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len)) (((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) - BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len)) (u0) (u1) (u2) (u3) (u4) (u5) (u6) (u7) ((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) (BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 % 2 ^ 32)) ((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) (BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len)) (memLoad32 Me ((reg n a1) + 0xC)) (memLoad32 Me ((reg n a1) + 0x8)) (memLoad32 Me (reg n a1)) vp23_3_1_3 ((q'_4_1) + BitVec.ofNat 32 0x20) (reg n a2) (reg n a3) ((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header) (BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) ((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len)) (BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) sl0'_2_1 sl1'_2_1 sl2'_2_1 sl3'_2_1 sl4'_2_1 sl5'_2_1 sl6'_2_1 sl7'_2_1 sl8'_2_1 sl9'_2_1 (BitVec.ofNat 32 (tm22_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32)) (u8) (u9) (u10) (u11) (u12) (u13) (u14) (u15) (u16) (u17) (u18) (u19) (u20) (u21) (u22) (u23) (u24) (u25) (u26) (u27) (u28) (u29) (u30) (u31) bp35_5_1_1 ((fun k => reg n (savedReg k))) Me) k_3_3 (tsav_r24_2_2_3, tsav_w78_2_2_3, (((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 tl45_5_1_3.header)) + BitVec.ofNat 32 (tl6_1_2_3.header + tl6_1_2_3.len)), (((BitVec.ofNat 32 tl45_5_1_3.len)) - BitVec.ofNat 32 (tl6_1_2_3.header + tl6_1_2_3.len))) (dg'_3_3, flag'_3_3, cp'_3_3, rem'_3_3) ∧
      rem'_3_3 = 0 ∧ (dg'_3_3 = 0 ∨ SvIn B dg'_3_3 32) ∧
      (dg'_3_3 ≠ 0 ∧ flag'_3_3 = 1) ∧ ∃ op8_3_3 ol8_3_3, derAlgOf Me ((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) (((((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) - BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))).toNat) = .ok ((op8_3_3, ol8_3_3), none) ∧ ∃ te8_3_3, derElement 0x30 (memBytes Me ((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) ((((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) - BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))).toNat) = .ok te8_3_3 ∧ (memBytes Me op8_3_3 ol8_3_3 = memBytes Me (BitVec.ofNat 32 0x3FCC4818) 8) ∧ ∃ vp19_3_3 vl19_3_3, derContent (((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) + BitVec.ofNat 32 (te8_3_3.header + te8_3_3.len)) (derElement 4 (memBytes Me (((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) + BitVec.ofNat 32 (te8_3_3.header + te8_3_3.len)) (((((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) - BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) - BitVec.ofNat 32 (te8_3_3.header + te8_3_3.len)).toNat)) = .ok (vp19_3_3, vl19_3_3) ∧ ∃ te19_3_3, derElement 4 (memBytes Me (((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) + BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) + BitVec.ofNat 32 (te8_3_3.header + te8_3_3.len)) (((((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) - BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) - BitVec.ofNat 32 (te8_3_3.header + te8_3_3.len)).toNat) = .ok te19_3_3 ∧ ∃ sr24_3_3 ss24_3_3, ecdsaSigOf 48 Me (vp19_3_3) ((vl19_3_3).toNat) = .ok (sr24_3_3, ss24_3_3) ∧
      (((((((((BitVec.ofNat 32 tl13_5_1_3.len) - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) - BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) - BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) - BitVec.ofNat 32 (te8_3_3.header + te8_3_3.len)) - BitVec.ofNat 32 (te19_3_3.header + te19_3_3.len)) = 0) ∧
      ∃ tl13_1_4_3, derElement 0x30 (memBytes Me (vp23_3_1_3) (vl23_3_1_3).toNat) = .ok tl13_1_4_3 ∧
      ((vl23_3_1_3) - BitVec.ofNat 32 (tl13_1_4_3.header + tl13_1_4_3.len) = 0) ∧
      derIntIsOf Me (memBytes Me ((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) (BitVec.ofNat 32 tl13_1_4_3.len).toNat) ((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) (derElement 2 (memBytes Me ((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) (BitVec.ofNat 32 tl13_1_4_3.len).toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = .ok true ∧
      ∃ te26_1_4_3, derElement 2 (memBytes Me ((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) (BitVec.ofNat 32 tl13_1_4_3.len).toNat) = .ok te26_1_4_3 ∧
      ∃ op32_1_4_3 ol32_1_4_3, derContent (((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) (derOid (memBytes Me (((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) ((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)).toNat)) = .ok (op32_1_4_3, ol32_1_4_3) ∧
      ∃ to32_1_4_3, derOid (memBytes Me (((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) ((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)).toNat) = .ok to32_1_4_3 ∧
      ∃ tl36_1_4_3, derElement 0x30 (memBytes Me ((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) (((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) - BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)).toNat) = .ok tl36_1_4_3 ∧
      isSha256Of Me (((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 tl36_1_4_3.header) (BitVec.ofNat 32 tl36_1_4_3.len).toNat = .ok true ∧
      ∃ te45_1_4_3, derElement 0x30 (memBytes Me (((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 tl36_1_4_3.header) (BitVec.ofNat 32 tl36_1_4_3.len).toNat) = .ok te45_1_4_3 ∧
      ∃ vp51_1_4_3 vl51_1_4_3, derContent ((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 tl36_1_4_3.header) + BitVec.ofNat 32 (te45_1_4_3.header + te45_1_4_3.len)) (derElement 4 (memBytes Me ((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 tl36_1_4_3.header) + BitVec.ofNat 32 (te45_1_4_3.header + te45_1_4_3.len)) ((BitVec.ofNat 32 tl36_1_4_3.len) - BitVec.ofNat 32 (te45_1_4_3.header + te45_1_4_3.len)).toNat)) = .ok (vp51_1_4_3, vl51_1_4_3) ∧
      ∃ te51_1_4_3, derElement 4 (memBytes Me ((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 tl36_1_4_3.header) + BitVec.ofNat 32 (te45_1_4_3.header + te45_1_4_3.len)) ((BitVec.ofNat 32 tl36_1_4_3.len) - BitVec.ofNat 32 (te45_1_4_3.header + te45_1_4_3.len)).toNat) = .ok te51_1_4_3 ∧
      (vl51_1_4_3 = 32) ∧
      (((BitVec.ofNat 32 tl36_1_4_3.len) - BitVec.ofNat 32 (te45_1_4_3.header + te45_1_4_3.len)) - BitVec.ofNat 32 (te51_1_4_3.header + te51_1_4_3.len) = 0) ∧
      ∃ tl2_2_4_3, derElement 2 (memBytes Me ((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) (((((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) - BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) - BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))).toNat) = .ok tl2_2_4_3 ∧
      ∃ ip2_2_4_3 il2_2_4_3, derPosIntOf (memBytes Me ((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) (((((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) - BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) - BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))).toNat) ((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) (.ok tl2_2_4_3) = .ok (ip2_2_4_3, il2_2_4_3) ∧
      (((il2_2_4_3) - (aluEval .sltu ((Me (ip2_2_4_3)).zeroExtend 32) 1)).toNat ≤ 20) ∧
      ∃ tl13_2_4_3, derElement 0x18 (memBytes Me (((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) ((((((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) - BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) - BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)).toNat) = .ok tl13_2_4_3 ∧
      ∃ tm18_2_4_3, generalizedTime (memBytes Me ((((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 tl13_2_4_3.header) ((BitVec.ofNat 32 tl13_2_4_3.len).toNat)) = some tm18_2_4_3 ∧
      ∃ tst3_w1328_3_4_3 : Word, ∃ tst3_w132c_3_4_3 : Word, (((derOptRes 0x30 (memBytes Me (((((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) ((((((((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) - BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) - BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))).toNat) = none) ∧ tst3_w1328_3_4_3 = ((((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len)) ∧ tst3_w132c_3_4_3 = (((((((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) - BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) - BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) ∨ ((¬ (derOptRes 0x30 (memBytes Me (((((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) ((((((((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) - BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) - BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))).toNat) = none)) ∧ ∃ tl2, derOptRes 0x30 (memBytes Me (((((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) ((((((((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) - BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) - BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))).toNat) = some (.ok tl2) ∧ tst3_w1328_3_4_3 = (((((((((vp23_3_1_3) + BitVec.ofNat 32 tl13_1_4_3.header) + BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) + BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) + BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tst3_w132c_3_4_3 = ((((((((BitVec.ofNat 32 tl13_1_4_3.len) - BitVec.ofNat 32 (te26_1_4_3.header + te26_1_4_3.len)) - BitVec.ofNat 32 (to32_1_4_3.header + to32_1_4_3.len)) - BitVec.ofNat 32 (tl36_1_4_3.header + tl36_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tst3_w1328_3_4_3 tst3_w132c_3_4_3.toNat ∧
      ∃ tst4_r8_4_4_3 : Word, ∃ tst4_w1328_4_4_3 : Word, ∃ tst4_w132c_4_4_3 : Word, (((tst3_w132c_3_4_3 = 0) ∧ tst4_r8_4_4_3 = BitVec.ofNat 32 0x18 ∧ tst4_w1328_4_4_3 = tst3_w1328_3_4_3 ∧ tst4_w132c_4_4_3 = tst3_w132c_3_4_3) ∨ ((¬ (tst3_w132c_3_4_3 = 0)) ∧ (Me tst3_w1328_3_4_3 = BitVec.ofNat 8 1) ∧ derBoolOf (memBytes Me (tst3_w1328_3_4_3) (tst3_w132c_3_4_3).toNat) (derElement 1 (memBytes Me (tst3_w1328_3_4_3) (tst3_w132c_3_4_3).toNat)) = .ok () ∧ ∃ tb10_1, derElement 1 (memBytes Me (tst3_w1328_3_4_3) (tst3_w132c_3_4_3).toNat) = .ok tb10_1 ∧ ∃ tst4b_w1328_2 : Word, ∃ tst4b_w132c_2 : Word, (((((tst3_w132c_3_4_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len)) = 0) ∧ tst4b_w1328_2 = ((tst3_w1328_3_4_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len)) ∧ tst4b_w132c_2 = ((tst3_w132c_3_4_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) ∨ ((¬ (((tst3_w132c_3_4_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len)) = 0)) ∧ ∃ tst4n_w1328_2 : Word, ∃ tst4n_w132c_2 : Word, (((Me ((tst3_w1328_3_4_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len)) = BitVec.ofNat 8 2) ∧ ∃ ip4 il4, derIntOf (memBytes Me (((tst3_w1328_3_4_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) (((tst3_w132c_3_4_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len))).toNat) (((tst3_w1328_3_4_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) (derElement 2 (memBytes Me (((tst3_w1328_3_4_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) (((tst3_w132c_3_4_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len))).toNat)) = .ok (ip4, il4) ∧ ∃ ti4, derElement 2 (memBytes Me (((tst3_w1328_3_4_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) (((tst3_w132c_3_4_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len))).toNat) = .ok ti4 ∧ tst4n_w1328_2 = (((tst3_w1328_3_4_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) + BitVec.ofNat 32 (ti4.header + ti4.len) ∧ tst4n_w132c_2 = (((tst3_w132c_3_4_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len))) - BitVec.ofNat 32 (ti4.header + ti4.len)) ∨ ((¬ (Me ((tst3_w1328_3_4_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len)) = BitVec.ofNat 8 2)) ∧ tst4n_w1328_2 = ((tst3_w1328_3_4_3) + BitVec.ofNat 32 (tb10_1.header + tb10_1.len)) ∧ tst4n_w132c_2 = ((tst3_w132c_3_4_3) - BitVec.ofNat 32 (tb10_1.header + tb10_1.len)))) ∧ SvIn B tst4n_w1328_2 tst4n_w132c_2.toNat ∧ tst4b_w1328_2 = tst4n_w1328_2 ∧ tst4b_w132c_2 = tst4n_w132c_2)) ∧ SvIn B tst4b_w1328_2 tst4b_w132c_2.toNat ∧ tst4_r8_4_4_3 = (BitVec.ofNat 32 0xFFFFFFFF) ∧ tst4_w1328_4_4_3 = tst4b_w1328_2 ∧ tst4_w132c_4_4_3 = tst4b_w132c_2) ∨ ((¬ (tst3_w132c_3_4_3 = 0)) ∧ (¬ (Me tst3_w1328_3_4_3 = BitVec.ofNat 8 1)) ∧ ∃ tst4n_w1328_2 : Word, ∃ tst4n_w132c_2 : Word, (((Me tst3_w1328_3_4_3 = BitVec.ofNat 8 2) ∧ ∃ ip4 il4, derIntOf (memBytes Me (tst3_w1328_3_4_3) (tst3_w132c_3_4_3).toNat) (tst3_w1328_3_4_3) (derElement 2 (memBytes Me (tst3_w1328_3_4_3) (tst3_w132c_3_4_3).toNat)) = .ok (ip4, il4) ∧ ∃ ti4, derElement 2 (memBytes Me (tst3_w1328_3_4_3) (tst3_w132c_3_4_3).toNat) = .ok ti4 ∧ tst4n_w1328_2 = (tst3_w1328_3_4_3) + BitVec.ofNat 32 (ti4.header + ti4.len) ∧ tst4n_w132c_2 = (tst3_w132c_3_4_3) - BitVec.ofNat 32 (ti4.header + ti4.len)) ∨ ((¬ (Me tst3_w1328_3_4_3 = BitVec.ofNat 8 2)) ∧ tst4n_w1328_2 = tst3_w1328_3_4_3 ∧ tst4n_w132c_2 = tst3_w132c_3_4_3)) ∧ SvIn B tst4n_w1328_2 tst4n_w132c_2.toNat ∧ tst4_r8_4_4_3 = (BitVec.ofNat 32 0x18) ∧ tst4_w1328_4_4_3 = tst4n_w1328_2 ∧ tst4_w132c_4_4_3 = tst4n_w132c_2)) ∧ SvIn B tst4_w1328_4_4_3 tst4_w132c_4_4_3.toNat ∧
      ∃ tst5_w1328_5_4_3 : Word, ∃ tst5_w132c_5_4_3 : Word, (((derOptRes 0xA0 (memBytes Me (tst4_w1328_4_4_3) (tst4_w132c_4_4_3).toNat) = none) ∧ tst5_w1328_5_4_3 = tst4_w1328_4_4_3 ∧ tst5_w132c_5_4_3 = tst4_w132c_4_4_3) ∨ ((¬ (derOptRes 0xA0 (memBytes Me (tst4_w1328_4_4_3) (tst4_w132c_4_4_3).toNat) = none)) ∧ ∃ tl2, derOptRes 0xA0 (memBytes Me (tst4_w1328_4_4_3) (tst4_w132c_4_4_3).toNat) = some (.ok tl2) ∧ tst5_w1328_5_4_3 = (tst4_w1328_4_4_3) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tst5_w132c_5_4_3 = (tst4_w132c_4_4_3) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tst5_w1328_5_4_3 tst5_w132c_5_4_3.toNat ∧
      ∃ tst6_w1328_6_4_3 : Word, ∃ tst6_w132c_6_4_3 : Word, (((derOptRes 0xA1 (memBytes Me (tst5_w1328_5_4_3) (tst5_w132c_5_4_3).toNat) = none) ∧ (tst5_w132c_5_4_3 = 0) ∧ tst6_w1328_6_4_3 = tst5_w1328_5_4_3 ∧ tst6_w132c_6_4_3 = tst5_w132c_5_4_3) ∨ ((¬ (derOptRes 0xA1 (memBytes Me (tst5_w1328_5_4_3) (tst5_w132c_5_4_3).toNat) = none)) ∧ ∃ tl2, derOptRes 0xA1 (memBytes Me (tst5_w1328_5_4_3) (tst5_w132c_5_4_3).toNat) = some (.ok tl2) ∧ ((tst5_w132c_5_4_3) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0) ∧ tst6_w1328_6_4_3 = (tst5_w1328_5_4_3) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tst6_w132c_6_4_3 = (tst5_w132c_5_4_3) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tst6_w1328_6_4_3 tst6_w132c_6_4_3.toNat ∧
      ∃ k_5_3, k_5_3 < 4 ∧
      (∀ i, i < k_5_3 → ∀ c'_5_3 q'_5_3, (c'_5_3, q'_5_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), (((reg n a2)) + BitVec.ofNat 32 0x198)) → ¬ (memBytes Me (memLoad32 Me (q'_5_3 + 0x20)) (memLoad32 Me (q'_5_3 + 0x24)).toNat = memBytes Me ((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) (BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)).toNat)) ∧
      ∃ c'_5_3 q'_5_3, (c'_5_3, q'_5_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) k_5_3 ((BitVec.ofNat 32 0x80), (((reg n a2)) + BitVec.ofNat 32 0x198)) ∧ (memBytes Me (memLoad32 Me (q'_5_3 + 0x20)) (memLoad32 Me (q'_5_3 + 0x24)).toNat = memBytes Me ((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) (BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)).toNat) ∧
      ((memLoad32 Me (q'_5_3 + 0x20)) ≠ 0) ∧
      (sha256 (memBytes Me (vp23_3_1_3) (vl23_3_1_3).toNat) = memBytes Me dg'_3_3 32) ∧
      (sha256 (memBytes Me ((memLoad32 Me ((reg n a1) + 0x8))) ((memLoad32 Me ((reg n a1) + 0xC))).toNat) = memBytes Me vp51_1_4_3 32) ∧
      ((BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len)) ≠ 0) ∧
      ∃ pv_7_3, SvPvRes Me (memLoad32 Me (((q'_5_3) + BitVec.ofNat 32 0x20) + 0x18)) (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 (sha256 (memBytes Me (BitVec.ofNat 32 0x3FCC486D) (1) ++ memBytes Me ((((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len))) + BitVec.ofNat 32 0x1) ((((BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len))) + BitVec.ofNat 32 0xFFFFFFFF).toNat))) (B + 0x21A0 + BitVec.ofNat 32 0xA40) (B + 0x21A0 + BitVec.ofNat 32 0xA70) sr24_3_3 ss24_3_3 (some pv_7_3) ∧
      (pv_7_3 ≠ 0) ∧
      ∃ ix7_1_1_4, nlScan Me ((memLoad32 Me ((reg n a1) + 0x18))) 0 (((memLoad32 Me ((reg n a1) + 0x1C))).toNat) = some ix7_1_1_4 ∧
      ∃ ix17_1_1_4, nlScan Me (((memLoad32 Me ((reg n a1) + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)) 0 ((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix7_1_1_4 + 1)) = some ix17_1_1_4 ∧
      ∃ ix25_1_1_4, nlScan Me ((((memLoad32 Me ((reg n a1) + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)) + BitVec.ofNat 32 (ix17_1_1_4 + 1)) 0 (((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) = some ix25_1_1_4 ∧
      ∃ ix33_1_1_4, nlScan Me (((((memLoad32 Me ((reg n a1) + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)) + BitVec.ofNat 32 (ix17_1_1_4 + 1)) + BitVec.ofNat 32 (ix25_1_1_4 + 1)) 0 ((((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) = some ix33_1_1_4 ∧
      (BitVec.ofNat 32 ix33_1_1_4 = 0) ∧
      (BitVec.ofNat 32 ((((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1) ≠ 0) ∧
      (((1 < (BitVec.ofNat 32 ix17_1_1_4).toNat) ∧ ((BitVec.ofNat 32 ((((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1)).toNat < (memLoad32 Me ((reg n a1) + 0x1C)).toNat) ∧ (¬ ((memLoad32 Me ((reg n a1) + 0x1C))).toNat < ((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 Me ((reg n a1) + 0x1C)))).toNat) ∧ (¬ (((BitVec.ofNat 32 ix17_1_1_4)) + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat) ∧ (Me (((memLoad32 Me ((reg n a1) + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)) ≠ 0x30)) ∨ ((¬ (1 < (BitVec.ofNat 32 ix17_1_1_4).toNat)) ∧ ((BitVec.ofNat 32 ((((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1)).toNat < (memLoad32 Me ((reg n a1) + 0x1C)).toNat) ∧ (¬ ((memLoad32 Me ((reg n a1) + 0x1C))).toNat < ((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 Me ((reg n a1) + 0x1C)))).toNat) ∧ (¬ (((BitVec.ofNat 32 ix17_1_1_4)) + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat))) ∧
      ∃ c'_2_4 p'_2_4 x21'_2_4 w60'_2_4 w70'_2_4, (c'_2_4, p'_2_4, x21'_2_4, w60'_2_4, w70'_2_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, (s.2.2.2.2), ((((Me ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((Me ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.2.1)) (BitVec.ofNat 32 0xA))))) (BitVec.ofNat 32 ix17_1_1_4).toNat ((BitVec.ofNat 32 ix17_1_1_4), (((memLoad32 Me ((reg n a1) + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)), vl23_3_1_3, (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 0x0)) ∧ (∀ i, i < (BitVec.ofNat 32 ix17_1_1_4).toNat → ∀ c'_2_4 p'_2_4 x21'_2_4 w60'_2_4 w70'_2_4, (c'_2_4, p'_2_4, x21'_2_4, w60'_2_4, w70'_2_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, (s.2.2.2.2), ((((Me ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((Me ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.2.1)) (BitVec.ofNat 32 0xA))))) i ((BitVec.ofNat 32 ix17_1_1_4), (((memLoad32 Me ((reg n a1) + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)), vl23_3_1_3, (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 0x0)) → ((((((Me (p'_2_4)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF).toNat < (BitVec.ofNat 32 0xA).toNat)) ∧ (((aluEval .sltu ((aluEval .mul (w70'_2_4) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w60'_2_4) (BitVec.ofNat 32 0xA))) (aluEval .mulhu (w60'_2_4) (BitVec.ofNat 32 0xA))) ||| (aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w70'_2_4) (BitVec.ofNat 32 0xA))) = 0)) ∧ (((aluEval .sltu (((((Me (p'_2_4)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w60'_2_4) (BitVec.ofNat 32 0xA))) (aluEval .mul (w60'_2_4) (BitVec.ofNat 32 0xA))) &&& (aluEval .sltu (((aluEval .mul (w70'_2_4) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w60'_2_4) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((Me (p'_2_4)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w60'_2_4) (BitVec.ofNat 32 0xA))) (aluEval .mul (w60'_2_4) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w70'_2_4) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w60'_2_4) (BitVec.ofNat 32 0xA)))) = 0))) ∧
      (w70'_2_4.toNat < 2 ^ 31) ∧ ∃ bs7_2_4, base64Decode (memBytes Me (((((memLoad32 Me ((reg n a1) + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)) + BitVec.ofNat 32 (ix17_1_1_4 + 1))) (((BitVec.ofNat 32 ix25_1_1_4)).toNat)) = some bs7_2_4 ∧ (bs7_2_4.length = 32) ∧
      ∃ k_3_4, k_3_4 < 8 ∧
      (∀ i, i < k_3_4 → ∀ c'_3_4 q'_3_4 w80'_3_4, (c'_3_4, q'_3_4, w80'_3_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2.1)) + BitVec.ofNat 32 0x20, (memLoad32 Me ((s.2.1) + 0x20)))) i ((BitVec.ofNat 32 0x100), (((reg n a2)) + BitVec.ofNat 32 0x98), (reg n a2)) → ¬ (memBytes Me (memLoad32 Me (q'_3_4 + 0x20)) (memLoad32 Me (q'_3_4 + 0x24)).toNat = memBytes Me (memLoad32 Me ((reg n a1) + 0x18)) (BitVec.ofNat 32 ix7_1_1_4).toNat)) ∧
      ∃ c'_3_4 q'_3_4 w80'_3_4, (c'_3_4, q'_3_4, w80'_3_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2.1)) + BitVec.ofNat 32 0x20, (memLoad32 Me ((s.2.1) + 0x20)))) k_3_4 ((BitVec.ofNat 32 0x100), (((reg n a2)) + BitVec.ofNat 32 0x98), (reg n a2)) ∧ (memBytes Me (memLoad32 Me (q'_3_4 + 0x20)) (memLoad32 Me (q'_3_4 + 0x24)).toNat = memBytes Me (memLoad32 Me ((reg n a1) + 0x18)) (BitVec.ofNat 32 ix7_1_1_4).toNat) ∧
      ((memLoad32 Me (q'_3_4 + 0x20)) ≠ 0) ∧
      ∃ u32 u33 u34 u35 u36 u37 u38 u39 u40 u41 u42 u43 u44 u45 u46 u47 u48 u49 u50 u51 u52 u53 u54 u55 u56 u57 u58 u59 u60, ∃ sg_5_4, ∃ k_5_4 c'_5_4 x21'_5_4 rl'_5_4 rp'_5_4 dg'_5_4 w8'_5_4 wc'_5_4 w28'_5_4 w2c'_5_4 w30'_5_4 w38'_5_4 w40'_5_4 w5c'_5_4 sg'_5_4, svChain (sv_cosigStep vp51_1_4_3 B (reg n a0) (reg n a1) (memLoad32 Me (reg n a1 + 4)) ((q'_3_4) + BitVec.ofNat 32 0x20) bs7_2_4 (le4 (sha256 (memBytes Me ((memLoad32 Me ((reg n a1) + 0x18))) (((BitVec.ofNat 32 ix7_1_1_4)).toNat) ++ memBytes Me (BitVec.ofNat 32 0x3FCC4850) (1) ++ memBytes Me (BitVec.ofNat 32 0x3FCC47D7) (1) ++ memBytes Me ((memLoad32 Me (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18))) (32))) 0) (memLoad32 Me (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x1C)) ((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 Me ((reg n a1) + 0x1C)))) (memLoad32 Me ((reg n a1) + 0x18)) (memLoad32 Me (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18)) (BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32)) (BitVec.ofNat 32 ix7_1_1_4) (memLoad32 Me ((reg n a1) + 0x18)) (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 % 2 ^ 32)) w60'_2_4 (memLoad32 Me ((reg n a1) + 0xC)) (memLoad32 Me ((reg n a1) + 0x8)) (memLoad32 Me (reg n a1)) w70'_2_4 (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) ((q'_4_1) + BitVec.ofNat 32 0x20) (memLoad32 Me (q'_3_4 + 0x20)) (reg n a3) ((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header) (BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) ((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl29_2_1_1.header + tl29_2_1_1.len))) + BitVec.ofNat 32 (tl2_3_1_1.header + tl2_3_1_1.len)) + BitVec.ofNat 32 (tl9_3_1_1.header + tl9_3_1_1.len)) (BitVec.ofNat 32 (tl6_4_1_1.header + tl6_4_1_1.len)) sl0'_2_1 sl1'_2_1 sl2'_2_1 sl3'_2_1 sl4'_2_1 sl5'_2_1 sl6'_2_1 sl7'_2_1 sl8'_2_1 sl9'_2_1 (BitVec.ofNat 32 (tm22_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32)) (u32) (u33) (u34) (u35) (u36) (u37) (u38) (u39) (u40) (u41) (u42) (u43) (u44) (u45) (u46) (u47) (u48) (u49) (u50) (u51) (u52) (u53) (u54) (u55) bp35_5_1_1 vp23_3_1_3 vl23_3_1_3 ((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) (BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) ((((((tsa4_w2a8_4_1_3) + BitVec.ofNat 32 tl2_5_1_3.header) + BitVec.ofNat 32 tl13_5_1_3.header) + BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len)) + BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len)) + BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)) (BitVec.ofNat 32 (tl45_5_1_3.header + tl45_5_1_3.len)) (BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32)) (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) dg'_3_3 ((fun k => reg n (savedReg k))) 0 0 0 Me) k_5_4 (((c'_3_4) + BitVec.ofNat 32 0xFFFFFFE0), x21'_2_4, (BitVec.ofNat 32 ix25_1_1_4), ((((memLoad32 Me ((reg n a1) + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)) + BitVec.ofNat 32 (ix17_1_1_4 + 1)), dg'_3_3, (u56), (u57), (u58), (u59), (BitVec.ofNat 32 0x0), ((((((memLoad32 Me ((reg n a1) + 0x18))) + BitVec.ofNat 32 (ix7_1_1_4 + 1)) + BitVec.ofNat 32 (ix17_1_1_4 + 1)) + BitVec.ofNat 32 (ix25_1_1_4 + 1)) + BitVec.ofNat 32 (ix33_1_1_4 + 1)), (u60), (BitVec.ofNat 32 ((((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1)), sg_5_4) (c'_5_4, x21'_5_4, rl'_5_4, rp'_5_4, dg'_5_4, w8'_5_4, wc'_5_4, w28'_5_4, w2c'_5_4, w30'_5_4, w38'_5_4, w40'_5_4, w5c'_5_4, sg'_5_4) ∧
      w5c'_5_4 = 0 ∧
      ((w30'_5_4) &&& BitVec.ofNat 32 0x1 ≠ 0) ∧ (evSpec (sigMem Me (B + 0x21A0 + BitVec.ofNat 32 0x420) sg'_5_4) (memLoad32 Me (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18)) (B + 0x21A0 + BitVec.ofNat 32 0x420) (memLoad32 Me ((reg n a1) + 0x18)) (((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (ix33_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 Me ((reg n a1) + 0x1C))))).toNat = true) ∧
      ((((memLoad32 Me ((reg n a1) + 0x2C)) = w70'_2_4) ∧ (aluEval .sltu ((memLoad32 Me ((reg n a1) + 0x28))) (w60'_2_4) ≠ 0)) ∨ ((¬ ((memLoad32 Me ((reg n a1) + 0x2C)) = w70'_2_4)) ∧ (aluEval .sltu ((memLoad32 Me ((reg n a1) + 0x2C))) (w70'_2_4) ≠ 0))) ∧
      ∃ root6_3_6_4, rootFromInclusion (pair64 ((memLoad32 Me ((reg n a1) + 0x28))) ((memLoad32 Me ((reg n a1) + 0x2C)))) (pair64 (w60'_2_4) (w70'_2_4)) ((sha256 ([] ++ memBytes Me (BitVec.ofNat 32 0x3FCC4106) (0x1) ++ memBytes Me (BitVec.ofNat 32 0x3FCC46F0) (0x71) ++ base64Encode (memBytes Me ((reg n a3)) (32)) ++ memBytes Me (BitVec.ofNat 32 0x3FCC4761) (0x1B) ++ base64Encode (memBytes Me ((memLoad32 Me ((reg n a1) + 0x8))) (((memLoad32 Me ((reg n a1) + 0xC))).toNat)) ++ memBytes Me (BitVec.ofNat 32 0x3FCC477C) (0x54) ++ base64Encode (memBytes Me ((memLoad32 Me (reg n a1))) (((memLoad32 Me (reg n a1 + 4))).toNat)) ++ memBytes Me (BitVec.ofNat 32 0x3FCC47D0) (0x7)))) (memBytes Me ((memLoad32 Me ((reg n a1) + 0x10))) (((memLoad32 Me ((reg n a1) + 0x14))).toNat)) = some root6_3_6_4 ∧
      (b32 root6_3_6_4 = b32 bs7_2_4) ∧
      ((((BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((BitVec.ofNat 32 (tm22_4_1_1 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((BitVec.ofNat 32 (tm22_4_1_1 / 2 ^ 32))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm31_4_1_1 % 2 ^ 32))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm31_4_1_1 / 2 ^ 32))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
      ((((memLoad32 Me (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((memLoad32 Me (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE4))) = 0)) ∨ ((¬ ((memLoad32 Me (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((memLoad32 Me (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 Me (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0))) ∧ (aluEval .sltu ((memLoad32 Me (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFEC))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 Me (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0)))) ∧ (aluEval .sltu ((memLoad32 Me (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
      ((((memLoad32 Me (((q'_5_3) + BitVec.ofNat 32 0x20) + 0xC)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((memLoad32 Me (((q'_5_3) + BitVec.ofNat 32 0x20) + 0x8))) = 0)) ∨ ((¬ ((memLoad32 Me (((q'_5_3) + BitVec.ofNat 32 0x20) + 0xC)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((memLoad32 Me (((q'_5_3) + BitVec.ofNat 32 0x20) + 0xC))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 Me (((q'_5_3) + BitVec.ofNat 32 0x20) + 0x14))) ∧ (aluEval .sltu ((memLoad32 Me (((q'_5_3) + BitVec.ofNat 32 0x20) + 0x10))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 Me (((q'_5_3) + BitVec.ofNat 32 0x20) + 0x14)))) ∧ (aluEval .sltu ((memLoad32 Me (((q'_5_3) + BitVec.ofNat 32 0x20) + 0x14))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
      ((((memLoad32 Me (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((memLoad32 Me (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 3))) = 0)) ∨ ((¬ ((memLoad32 Me (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((memLoad32 Me (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 Me (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15))) ∧ (aluEval .sltu ((memLoad32 Me (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 11))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 Me (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15)))) ∧ (aluEval .sltu ((memLoad32 Me (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
      SvOkRet B (reg n a0) ((fun k => reg n (savedReg k))) n (BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32)) (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) (memLoad32 Me ((reg n a1) + 0x28)) (memLoad32 Me ((reg n a1) + 0x2C))) := by
  obtain ⟨n1, c1, s1, sp1, r18, r19, r25, r22, r21, r26, r27, ra0, ra1, rk⟩ := sv_pro C F s rsp hb sb
  have fM1 : ∀ x, SvR B x → n1.mem x = Me x := fun x hx => by rw [s1.mem]; exact svProMem_out hx
  have hm : ∀ x, SvR B x → n1.mem x = n.mem x := fun x hx => by rw [fM1 x hx, s.mem]
  rcases sv_verify_72 (B := B) (out := reg n a0) (bp := reg n a1) (rootp := reg n a2) (dg := reg n a3) (lp := memLoad32 Me (reg n a1)) (ll := memLoad32 Me (reg n a1 + 4)) (v := (fun k => reg n (savedReg k))) (sl5 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0xA34)) (sl7 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0xA3C)) (sl9 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0xA44)) (wd0 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0xD0)) (wd4 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0xD4)) (wd8 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0xD8)) (wdc := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0xDC)) (we0 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0xE0)) (we4 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0xE4)) (we8 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0xE8)) (wec := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0xEC)) (wf0 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0xF0)) (wf4 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0xF4)) (wf8 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0xF8)) (wfc := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0xFC)) (w100 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0x100)) (w104 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0x104)) (w108 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0x108)) (w10c := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0x10C)) (w110 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0x110)) (w114 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0x114)) (w118 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0x118)) (w11c := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0x11C)) (w120 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0x120)) (w124 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0x124)) (w128 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0x128)) (w12c := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0x12C)) (w8 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0x8)) (wc := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0xC)) (w10 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0x10)) (w14 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0x14)) (w18 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0x18)) (w1c := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0x1C)) (n0 := n1) F (E.fr F fM1) (by rw [s1.mem]; exact svProMem_saves) hret hO (by rw [s1.mem]; exact s1) Me fM1 sp1 (ra0.trans (by rw [BitVec.add_assoc]; rfl)) (ra1.trans (by rw [BitVec.add_assoc]; rfl)) r18 r19 r21 r22 r25 r26 (r27.trans (by rw [BitVec.add_assoc]; rfl)) (by rw [s1.mem]; exact svProMem_reader.1) (by rw [s1.mem]; exact svProMem_reader.2.1) (by rw [s1.mem]; exact svProMem_reader.2.2.1) (by rw [s1.mem]; exact svProMem_reader.2.2.2) lc_in D0 (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) SD0 H' SH0 KS PE0 pkp_in apk pk_in side (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) ts_in he0p_in he0l_in ae0p ae0l e0_in he1p_in he1l_in ae1p ae1l e1_in he2p_in he2l_in ae2p ae2l e2_in he3p_in he3l_in ae3p ae3l e3_in he4p_in he4l_in ae4p ae4l e4_in htsp_in htsl_in atsp atsl EC0 IC0 UC0 BG0 RS BY0 dg_in UE0 N80 PM0 WM0 PT0 WN0 ME P2C0 GDC0 P2D0 SC0 hidC GD OD AD hzi c0_in hc0p_in hc0l_in ac0p ac0l D0' H'' S2 KS' pkp_in' apk' pk_in' side' (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) CK0 ckp_in4 ckl_in4 a_ckp a_ckl ck_in H''' KS'' kp_in4 kw_in4 a_kp a_kw kp_in EE0 hiv pk_in'' lid_in lih_in lil_in a_lih a_lil RK0 dgi_in pp_in4 pl_in4 a_pp a_pl pp_in ii2h ai2h ii2l ai2l ii3h ai3h ii3l ai3l it4h at4h it4l at4l it5h at5h it5l at5l hOk with e | e | hx
  · exact .inl (SvErrRet.pre c1 (rk _ (by decide)) (rk _ (by decide)) hm e)
  · exact .inr (.inl (Panics.of_steps c1 e))
  obtain ⟨t_1_1_1, hx⟩ := hx
  obtain ⟨p1, hx⟩ := hx
  obtain ⟨p2, hx⟩ := hx
  obtain ⟨tl1_2_1_1, hx⟩ := hx
  obtain ⟨p4, hx⟩ := hx
  obtain ⟨tl8_2_1_1, hx⟩ := hx
  obtain ⟨p6, hx⟩ := hx
  obtain ⟨tl16_2_1_1, hx⟩ := hx
  obtain ⟨p8, hx⟩ := hx
  obtain ⟨bp16_2_1_1, hx⟩ := hx
  obtain ⟨bl16_2_1_1, hx⟩ := hx
  obtain ⟨p11, hx⟩ := hx
  obtain ⟨p12, hx⟩ := hx
  obtain ⟨tl29_2_1_1, hx⟩ := hx
  obtain ⟨p14, hx⟩ := hx
  obtain ⟨p15, hx⟩ := hx
  obtain ⟨te43_2_1_1, hx⟩ := hx
  obtain ⟨p17, hx⟩ := hx
  obtain ⟨p18, hx⟩ := hx
  obtain ⟨tl2_3_1_1, hx⟩ := hx
  obtain ⟨p20, hx⟩ := hx
  obtain ⟨ip2_3_1_1, hx⟩ := hx
  obtain ⟨il2_3_1_1, hx⟩ := hx
  obtain ⟨p23, hx⟩ := hx
  obtain ⟨p24, hx⟩ := hx
  obtain ⟨tl9_3_1_1, hx⟩ := hx
  obtain ⟨p26, hx⟩ := hx
  obtain ⟨op19_3_1_1, hx⟩ := hx
  obtain ⟨ol19_3_1_1, hx⟩ := hx
  obtain ⟨p29, hx⟩ := hx
  obtain ⟨p30, hx⟩ := hx
  obtain ⟨tl6_4_1_1, hx⟩ := hx
  obtain ⟨p32, hx⟩ := hx
  obtain ⟨tl13_4_1_1, hx⟩ := hx
  obtain ⟨p34, hx⟩ := hx
  obtain ⟨tm22_4_1_1, hx⟩ := hx
  obtain ⟨rs22_4_1_1, hx⟩ := hx
  obtain ⟨p37, hx⟩ := hx
  obtain ⟨tm31_4_1_1, hx⟩ := hx
  obtain ⟨rs31_4_1_1, hx⟩ := hx
  obtain ⟨p40, hx⟩ := hx
  obtain ⟨p41, hx⟩ := hx
  obtain ⟨tl2_5_1_1, hx⟩ := hx
  obtain ⟨p43, hx⟩ := hx
  obtain ⟨tl6_5_1_1, hx⟩ := hx
  obtain ⟨p45, hx⟩ := hx
  obtain ⟨op15_5_1_1, hx⟩ := hx
  obtain ⟨ol15_5_1_1, hx⟩ := hx
  obtain ⟨prp15_5_1_1, hx⟩ := hx
  obtain ⟨pu15_5_1_1, hx⟩ := hx
  obtain ⟨p50, hx⟩ := hx
  obtain ⟨ta15_5_1_1, hx⟩ := hx
  obtain ⟨p52, hx⟩ := hx
  obtain ⟨p53, hx⟩ := hx
  obtain ⟨p54, hx⟩ := hx
  obtain ⟨p55, hx⟩ := hx
  obtain ⟨tl35_5_1_1, hx⟩ := hx
  obtain ⟨p57, hx⟩ := hx
  obtain ⟨bp35_5_1_1, hx⟩ := hx
  obtain ⟨bl35_5_1_1, hx⟩ := hx
  obtain ⟨p60, hx⟩ := hx
  obtain ⟨p61, hx⟩ := hx
  obtain ⟨p62, hx⟩ := hx
  obtain ⟨p63, hx⟩ := hx
  obtain ⟨p64, hx⟩ := hx
  obtain ⟨tl9_6_1_1, hx⟩ := hx
  obtain ⟨p66, hx⟩ := hx
  obtain ⟨p67, hx⟩ := hx
  obtain ⟨tl25_6_1_1, hx⟩ := hx
  obtain ⟨p69, hx⟩ := hx
  obtain ⟨p70, hx⟩ := hx
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
  obtain ⟨p89, hx⟩ := hx
  obtain ⟨p90, hx⟩ := hx
  obtain ⟨p91, hx⟩ := hx
  obtain ⟨p92, hx⟩ := hx
  obtain ⟨p93, hx⟩ := hx
  obtain ⟨p94, hx⟩ := hx
  obtain ⟨p95, hx⟩ := hx
  obtain ⟨p96, hx⟩ := hx
  obtain ⟨p97, hx⟩ := hx
  obtain ⟨p98, hx⟩ := hx
  obtain ⟨p99, hx⟩ := hx
  obtain ⟨p100, hx⟩ := hx
  obtain ⟨p101, hx⟩ := hx
  obtain ⟨sr43_2_1, hx⟩ := hx
  obtain ⟨ss43_2_1, hx⟩ := hx
  obtain ⟨p104, hx⟩ := hx
  obtain ⟨k_4_1, hx⟩ := hx
  obtain ⟨p106, hx⟩ := hx
  obtain ⟨p107, hx⟩ := hx
  obtain ⟨c'_4_1, hx⟩ := hx
  obtain ⟨q'_4_1, hx⟩ := hx
  obtain ⟨p110, hx⟩ := hx
  obtain ⟨p111, hx⟩ := hx
  obtain ⟨p112, hx⟩ := hx
  obtain ⟨pv_5_1, hx⟩ := hx
  obtain ⟨p114, hx⟩ := hx
  obtain ⟨p115, hx⟩ := hx
  obtain ⟨p116, hx⟩ := hx
  obtain ⟨p117, hx⟩ := hx
  obtain ⟨p118, hx⟩ := hx
  obtain ⟨p119, hx⟩ := hx
  obtain ⟨p120, hx⟩ := hx
  obtain ⟨tl49_1_6_1, hx⟩ := hx
  obtain ⟨p122, hx⟩ := hx
  obtain ⟨p123, hx⟩ := hx
  obtain ⟨bs9_2_6_1, hx⟩ := hx
  obtain ⟨p125, hx⟩ := hx
  obtain ⟨te9_2_6_1, hx⟩ := hx
  obtain ⟨p127, hx⟩ := hx
  obtain ⟨bs16_2_6_1, hx⟩ := hx
  obtain ⟨p129, hx⟩ := hx
  obtain ⟨te16_2_6_1, hx⟩ := hx
  obtain ⟨p131, hx⟩ := hx
  obtain ⟨p132, hx⟩ := hx
  obtain ⟨p133, hx⟩ := hx
  obtain ⟨σd_2, hx⟩ := hx
  obtain ⟨σf_2, hx⟩ := hx
  obtain ⟨Dv_2, hx⟩ := hx
  obtain ⟨Fv_2, hx⟩ := hx
  obtain ⟨p138, hx⟩ := hx
  obtain ⟨p139, hx⟩ := hx
  obtain ⟨p140, hx⟩ := hx
  obtain ⟨p141, hx⟩ := hx
  obtain ⟨p142, hx⟩ := hx
  obtain ⟨stm_2, hx⟩ := hx
  obtain ⟨p144, hx⟩ := hx
  obtain ⟨τd_2, hx⟩ := hx
  obtain ⟨τf_2, hx⟩ := hx
  obtain ⟨Dz_2, hx⟩ := hx
  obtain ⟨Fz_2, hx⟩ := hx
  obtain ⟨p149, hx⟩ := hx
  obtain ⟨p150, hx⟩ := hx
  obtain ⟨p151, hx⟩ := hx
  obtain ⟨p152, hx⟩ := hx
  obtain ⟨p153, hx⟩ := hx
  obtain ⟨tl10_1_1_3, hx⟩ := hx
  obtain ⟨p155, hx⟩ := hx
  obtain ⟨p156, hx⟩ := hx
  obtain ⟨tl22_1_1_3, hx⟩ := hx
  obtain ⟨p158, hx⟩ := hx
  obtain ⟨p159, hx⟩ := hx
  obtain ⟨te33_1_1_3, hx⟩ := hx
  obtain ⟨p161, hx⟩ := hx
  obtain ⟨p162, hx⟩ := hx
  obtain ⟨tl41_1_1_3, hx⟩ := hx
  obtain ⟨p164, hx⟩ := hx
  obtain ⟨p165, hx⟩ := hx
  obtain ⟨op53_1_1_3, hx⟩ := hx
  obtain ⟨ol53_1_1_3, hx⟩ := hx
  obtain ⟨p168, hx⟩ := hx
  obtain ⟨to53_1_1_3, hx⟩ := hx
  obtain ⟨p170, hx⟩ := hx
  obtain ⟨p171, hx⟩ := hx
  obtain ⟨tl2_2_1_3, hx⟩ := hx
  obtain ⟨p173, hx⟩ := hx
  obtain ⟨p174, hx⟩ := hx
  obtain ⟨tl15_2_1_3, hx⟩ := hx
  obtain ⟨p176, hx⟩ := hx
  obtain ⟨p177, hx⟩ := hx
  obtain ⟨p178, hx⟩ := hx
  obtain ⟨te26_2_1_3, hx⟩ := hx
  obtain ⟨p180, hx⟩ := hx
  obtain ⟨tl32_2_1_3, hx⟩ := hx
  obtain ⟨p182, hx⟩ := hx
  obtain ⟨p183, hx⟩ := hx
  obtain ⟨te41_2_1_3, hx⟩ := hx
  obtain ⟨p185, hx⟩ := hx
  obtain ⟨p186, hx⟩ := hx
  obtain ⟨tl49_2_1_3, hx⟩ := hx
  obtain ⟨p188, hx⟩ := hx
  obtain ⟨op58_2_1_3, hx⟩ := hx
  obtain ⟨ol58_2_1_3, hx⟩ := hx
  obtain ⟨p191, hx⟩ := hx
  obtain ⟨to58_2_1_3, hx⟩ := hx
  obtain ⟨p193, hx⟩ := hx
  obtain ⟨p194, hx⟩ := hx
  obtain ⟨tl2_3_1_3, hx⟩ := hx
  obtain ⟨p196, hx⟩ := hx
  obtain ⟨p197, hx⟩ := hx
  obtain ⟨vp23_3_1_3, hx⟩ := hx
  obtain ⟨vl23_3_1_3, hx⟩ := hx
  obtain ⟨p200, hx⟩ := hx
  obtain ⟨te23_3_1_3, hx⟩ := hx
  obtain ⟨p202, hx⟩ := hx
  obtain ⟨p203, hx⟩ := hx
  obtain ⟨tsa4_w2a8_4_1_3, hx⟩ := hx
  obtain ⟨tsa4_w2ac_4_1_3, hx⟩ := hx
  obtain ⟨p206, hx⟩ := hx
  obtain ⟨p207, hx⟩ := hx
  obtain ⟨tl2_5_1_3, hx⟩ := hx
  obtain ⟨p209, hx⟩ := hx
  obtain ⟨p210, hx⟩ := hx
  obtain ⟨tl13_5_1_3, hx⟩ := hx
  obtain ⟨p212, hx⟩ := hx
  obtain ⟨p213, hx⟩ := hx
  obtain ⟨p214, hx⟩ := hx
  obtain ⟨te25_5_1_3, hx⟩ := hx
  obtain ⟨p216, hx⟩ := hx
  obtain ⟨tl31_5_1_3, hx⟩ := hx
  obtain ⟨p218, hx⟩ := hx
  obtain ⟨p219, hx⟩ := hx
  obtain ⟨te39_5_1_3, hx⟩ := hx
  obtain ⟨p221, hx⟩ := hx
  obtain ⟨tl45_5_1_3, hx⟩ := hx
  obtain ⟨p223, hx⟩ := hx
  obtain ⟨p224, hx⟩ := hx
  obtain ⟨p225, hx⟩ := hx
  obtain ⟨tl6_1_2_3, hx⟩ := hx
  obtain ⟨p227, hx⟩ := hx
  obtain ⟨op15_1_2_3, hx⟩ := hx
  obtain ⟨ol15_1_2_3, hx⟩ := hx
  obtain ⟨p230, hx⟩ := hx
  obtain ⟨to15_1_2_3, hx⟩ := hx
  obtain ⟨p232, hx⟩ := hx
  obtain ⟨tl20_1_2_3, hx⟩ := hx
  obtain ⟨p234, hx⟩ := hx
  obtain ⟨p235, hx⟩ := hx
  obtain ⟨p236, hx⟩ := hx
  obtain ⟨tsav_r24_2_2_3, hx⟩ := hx
  obtain ⟨tsav_w78_2_2_3, hx⟩ := hx
  obtain ⟨tsav_w1388_2_2_3, hx⟩ := hx
  obtain ⟨tsav_w138c_2_2_3, hx⟩ := hx
  obtain ⟨p241, hx⟩ := hx
  obtain ⟨p242, hx⟩ := hx
  obtain ⟨p243, hx⟩ := hx
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
  obtain ⟨p281, hx⟩ := hx
  obtain ⟨p282, hx⟩ := hx
  obtain ⟨p283, hx⟩ := hx
  obtain ⟨p284, hx⟩ := hx
  obtain ⟨op8_3_3, hx⟩ := hx
  obtain ⟨ol8_3_3, hx⟩ := hx
  obtain ⟨p287, hx⟩ := hx
  obtain ⟨te8_3_3, hx⟩ := hx
  obtain ⟨p289, hx⟩ := hx
  obtain ⟨p290, hx⟩ := hx
  obtain ⟨vp19_3_3, hx⟩ := hx
  obtain ⟨vl19_3_3, hx⟩ := hx
  obtain ⟨p293, hx⟩ := hx
  obtain ⟨te19_3_3, hx⟩ := hx
  obtain ⟨p295, hx⟩ := hx
  obtain ⟨sr24_3_3, hx⟩ := hx
  obtain ⟨ss24_3_3, hx⟩ := hx
  obtain ⟨p298, hx⟩ := hx
  obtain ⟨p299, hx⟩ := hx
  obtain ⟨tl13_1_4_3, hx⟩ := hx
  obtain ⟨p301, hx⟩ := hx
  obtain ⟨p302, hx⟩ := hx
  obtain ⟨p303, hx⟩ := hx
  obtain ⟨te26_1_4_3, hx⟩ := hx
  obtain ⟨p305, hx⟩ := hx
  obtain ⟨op32_1_4_3, hx⟩ := hx
  obtain ⟨ol32_1_4_3, hx⟩ := hx
  obtain ⟨p308, hx⟩ := hx
  obtain ⟨to32_1_4_3, hx⟩ := hx
  obtain ⟨p310, hx⟩ := hx
  obtain ⟨tl36_1_4_3, hx⟩ := hx
  obtain ⟨p312, hx⟩ := hx
  obtain ⟨p313, hx⟩ := hx
  obtain ⟨te45_1_4_3, hx⟩ := hx
  obtain ⟨p315, hx⟩ := hx
  obtain ⟨vp51_1_4_3, hx⟩ := hx
  obtain ⟨vl51_1_4_3, hx⟩ := hx
  obtain ⟨p318, hx⟩ := hx
  obtain ⟨te51_1_4_3, hx⟩ := hx
  obtain ⟨p320, hx⟩ := hx
  obtain ⟨p321, hx⟩ := hx
  obtain ⟨p322, hx⟩ := hx
  obtain ⟨tl2_2_4_3, hx⟩ := hx
  obtain ⟨p324, hx⟩ := hx
  obtain ⟨ip2_2_4_3, hx⟩ := hx
  obtain ⟨il2_2_4_3, hx⟩ := hx
  obtain ⟨p327, hx⟩ := hx
  obtain ⟨p328, hx⟩ := hx
  obtain ⟨tl13_2_4_3, hx⟩ := hx
  obtain ⟨p330, hx⟩ := hx
  obtain ⟨tm18_2_4_3, hx⟩ := hx
  obtain ⟨p332, hx⟩ := hx
  obtain ⟨tst3_w1328_3_4_3, hx⟩ := hx
  obtain ⟨tst3_w132c_3_4_3, hx⟩ := hx
  obtain ⟨p335, hx⟩ := hx
  obtain ⟨p336, hx⟩ := hx
  obtain ⟨tst4_r8_4_4_3, hx⟩ := hx
  obtain ⟨tst4_w1328_4_4_3, hx⟩ := hx
  obtain ⟨tst4_w132c_4_4_3, hx⟩ := hx
  obtain ⟨p340, hx⟩ := hx
  obtain ⟨p341, hx⟩ := hx
  obtain ⟨tst5_w1328_5_4_3, hx⟩ := hx
  obtain ⟨tst5_w132c_5_4_3, hx⟩ := hx
  obtain ⟨p344, hx⟩ := hx
  obtain ⟨p345, hx⟩ := hx
  obtain ⟨tst6_w1328_6_4_3, hx⟩ := hx
  obtain ⟨tst6_w132c_6_4_3, hx⟩ := hx
  obtain ⟨p348, hx⟩ := hx
  obtain ⟨p349, hx⟩ := hx
  obtain ⟨k_5_3, hx⟩ := hx
  obtain ⟨p351, hx⟩ := hx
  obtain ⟨p352, hx⟩ := hx
  obtain ⟨c'_5_3, hx⟩ := hx
  obtain ⟨q'_5_3, hx⟩ := hx
  obtain ⟨p355, hx⟩ := hx
  obtain ⟨p356, hx⟩ := hx
  obtain ⟨p357, hx⟩ := hx
  obtain ⟨p358, hx⟩ := hx
  obtain ⟨p359, hx⟩ := hx
  obtain ⟨p360, hx⟩ := hx
  obtain ⟨pv_7_3, hx⟩ := hx
  obtain ⟨p362, hx⟩ := hx
  obtain ⟨p363, hx⟩ := hx
  obtain ⟨ix7_1_1_4, hx⟩ := hx
  obtain ⟨p365, hx⟩ := hx
  obtain ⟨ix17_1_1_4, hx⟩ := hx
  obtain ⟨p367, hx⟩ := hx
  obtain ⟨ix25_1_1_4, hx⟩ := hx
  obtain ⟨p369, hx⟩ := hx
  obtain ⟨ix33_1_1_4, hx⟩ := hx
  obtain ⟨p371, hx⟩ := hx
  obtain ⟨p372, hx⟩ := hx
  obtain ⟨p373, hx⟩ := hx
  obtain ⟨p374, hx⟩ := hx
  obtain ⟨c'_2_4, hx⟩ := hx
  obtain ⟨p'_2_4, hx⟩ := hx
  obtain ⟨x21'_2_4, hx⟩ := hx
  obtain ⟨w60'_2_4, hx⟩ := hx
  obtain ⟨w70'_2_4, hx⟩ := hx
  obtain ⟨p380, hx⟩ := hx
  obtain ⟨p381, hx⟩ := hx
  obtain ⟨p382, hx⟩ := hx
  obtain ⟨bs7_2_4, hx⟩ := hx
  obtain ⟨p384, hx⟩ := hx
  obtain ⟨p385, hx⟩ := hx
  obtain ⟨k_3_4, hx⟩ := hx
  obtain ⟨p387, hx⟩ := hx
  obtain ⟨p388, hx⟩ := hx
  obtain ⟨c'_3_4, hx⟩ := hx
  obtain ⟨q'_3_4, hx⟩ := hx
  obtain ⟨w80'_3_4, hx⟩ := hx
  obtain ⟨p392, hx⟩ := hx
  obtain ⟨p393, hx⟩ := hx
  obtain ⟨p394, hx⟩ := hx
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
  obtain ⟨p440, hx⟩ := hx
  obtain ⟨p441, hx⟩ := hx
  obtain ⟨p442, hx⟩ := hx
  obtain ⟨p443, hx⟩ := hx
  obtain ⟨p444, hx⟩ := hx
  obtain ⟨root6_3_6_4, hx⟩ := hx
  obtain ⟨p446, hx⟩ := hx
  obtain ⟨p447, hx⟩ := hx
  obtain ⟨p448, hx⟩ := hx
  obtain ⟨p449, hx⟩ := hx
  obtain ⟨p450, hx⟩ := hx
  obtain ⟨p451, hx⟩ := hx
  obtain ⟨p452, hx⟩ := hx
  obtain ⟨p453, hx⟩ := hx
  obtain ⟨p454, hx⟩ := hx
  obtain ⟨p455, hx⟩ := hx
  refine .inr (.inr ?_)
  refine ⟨t_1_1_1, ?_⟩
  refine ⟨p1, ?_⟩
  refine ⟨p2, ?_⟩
  refine ⟨tl1_2_1_1, ?_⟩
  refine ⟨p4, ?_⟩
  refine ⟨tl8_2_1_1, ?_⟩
  refine ⟨p6, ?_⟩
  refine ⟨tl16_2_1_1, ?_⟩
  refine ⟨p8, ?_⟩
  refine ⟨bp16_2_1_1, ?_⟩
  refine ⟨bl16_2_1_1, ?_⟩
  refine ⟨p11, ?_⟩
  refine ⟨p12, ?_⟩
  refine ⟨tl29_2_1_1, ?_⟩
  refine ⟨p14, ?_⟩
  refine ⟨p15, ?_⟩
  refine ⟨te43_2_1_1, ?_⟩
  refine ⟨p17, ?_⟩
  refine ⟨p18, ?_⟩
  refine ⟨tl2_3_1_1, ?_⟩
  refine ⟨p20, ?_⟩
  refine ⟨ip2_3_1_1, ?_⟩
  refine ⟨il2_3_1_1, ?_⟩
  refine ⟨p23, ?_⟩
  refine ⟨p24, ?_⟩
  refine ⟨tl9_3_1_1, ?_⟩
  refine ⟨p26, ?_⟩
  refine ⟨op19_3_1_1, ?_⟩
  refine ⟨ol19_3_1_1, ?_⟩
  refine ⟨p29, ?_⟩
  refine ⟨p30, ?_⟩
  refine ⟨tl6_4_1_1, ?_⟩
  refine ⟨p32, ?_⟩
  refine ⟨tl13_4_1_1, ?_⟩
  refine ⟨p34, ?_⟩
  refine ⟨tm22_4_1_1, ?_⟩
  refine ⟨rs22_4_1_1, ?_⟩
  refine ⟨p37, ?_⟩
  refine ⟨tm31_4_1_1, ?_⟩
  refine ⟨rs31_4_1_1, ?_⟩
  refine ⟨p40, ?_⟩
  refine ⟨p41, ?_⟩
  refine ⟨tl2_5_1_1, ?_⟩
  refine ⟨p43, ?_⟩
  refine ⟨tl6_5_1_1, ?_⟩
  refine ⟨p45, ?_⟩
  refine ⟨op15_5_1_1, ?_⟩
  refine ⟨ol15_5_1_1, ?_⟩
  refine ⟨prp15_5_1_1, ?_⟩
  refine ⟨pu15_5_1_1, ?_⟩
  refine ⟨p50, ?_⟩
  refine ⟨ta15_5_1_1, ?_⟩
  refine ⟨p52, ?_⟩
  refine ⟨p53, ?_⟩
  refine ⟨p54, ?_⟩
  refine ⟨p55, ?_⟩
  refine ⟨tl35_5_1_1, ?_⟩
  refine ⟨p57, ?_⟩
  refine ⟨bp35_5_1_1, ?_⟩
  refine ⟨bl35_5_1_1, ?_⟩
  refine ⟨p60, ?_⟩
  refine ⟨p61, ?_⟩
  refine ⟨p62, ?_⟩
  refine ⟨p63, ?_⟩
  refine ⟨p64, ?_⟩
  refine ⟨tl9_6_1_1, ?_⟩
  refine ⟨p66, ?_⟩
  refine ⟨p67, ?_⟩
  refine ⟨tl25_6_1_1, ?_⟩
  refine ⟨p69, ?_⟩
  refine ⟨p70, ?_⟩
  refine ⟨u0_1, ?_⟩
  refine ⟨u1_1, ?_⟩
  refine ⟨u2_1, ?_⟩
  refine ⟨k_2_1, ?_⟩
  refine ⟨f30'_2_1, ?_⟩
  refine ⟨f34'_2_1, ?_⟩
  refine ⟨rem'_2_1, ?_⟩
  refine ⟨cur'_2_1, ?_⟩
  refine ⟨sl0'_2_1, ?_⟩
  refine ⟨sl1'_2_1, ?_⟩
  refine ⟨sl2'_2_1, ?_⟩
  refine ⟨sl3'_2_1, ?_⟩
  refine ⟨sl4'_2_1, ?_⟩
  refine ⟨sl5'_2_1, ?_⟩
  refine ⟨sl6'_2_1, ?_⟩
  refine ⟨sl7'_2_1, ?_⟩
  refine ⟨sl8'_2_1, ?_⟩
  refine ⟨sl9'_2_1, ?_⟩
  refine ⟨p89, ?_⟩
  refine ⟨p90, ?_⟩
  refine ⟨p91, ?_⟩
  refine ⟨p92, ?_⟩
  refine ⟨p93, ?_⟩
  refine ⟨p94, ?_⟩
  refine ⟨p95, ?_⟩
  refine ⟨p96, ?_⟩
  refine ⟨p97, ?_⟩
  refine ⟨p98, ?_⟩
  refine ⟨p99, ?_⟩
  refine ⟨p100, ?_⟩
  refine ⟨p101, ?_⟩
  refine ⟨sr43_2_1, ?_⟩
  refine ⟨ss43_2_1, ?_⟩
  refine ⟨p104, ?_⟩
  refine ⟨k_4_1, ?_⟩
  refine ⟨p106, ?_⟩
  refine ⟨p107, ?_⟩
  refine ⟨c'_4_1, ?_⟩
  refine ⟨q'_4_1, ?_⟩
  refine ⟨p110, ?_⟩
  refine ⟨p111, ?_⟩
  refine ⟨p112, ?_⟩
  refine ⟨pv_5_1, ?_⟩
  refine ⟨p114, ?_⟩
  refine ⟨p115, ?_⟩
  refine ⟨p116, ?_⟩
  refine ⟨p117, ?_⟩
  refine ⟨p118, ?_⟩
  refine ⟨p119, ?_⟩
  refine ⟨p120, ?_⟩
  refine ⟨tl49_1_6_1, ?_⟩
  refine ⟨p122, ?_⟩
  refine ⟨p123, ?_⟩
  refine ⟨bs9_2_6_1, ?_⟩
  refine ⟨p125, ?_⟩
  refine ⟨te9_2_6_1, ?_⟩
  refine ⟨p127, ?_⟩
  refine ⟨bs16_2_6_1, ?_⟩
  refine ⟨p129, ?_⟩
  refine ⟨te16_2_6_1, ?_⟩
  refine ⟨p131, ?_⟩
  refine ⟨p132, ?_⟩
  refine ⟨p133, ?_⟩
  refine ⟨σd_2, ?_⟩
  refine ⟨σf_2, ?_⟩
  refine ⟨Dv_2, ?_⟩
  refine ⟨Fv_2, ?_⟩
  refine ⟨p138, ?_⟩
  refine ⟨p139, ?_⟩
  refine ⟨p140, ?_⟩
  refine ⟨p141, ?_⟩
  refine ⟨p142, ?_⟩
  refine ⟨stm_2, ?_⟩
  refine ⟨p144, ?_⟩
  refine ⟨τd_2, ?_⟩
  refine ⟨τf_2, ?_⟩
  refine ⟨Dz_2, ?_⟩
  refine ⟨Fz_2, ?_⟩
  refine ⟨p149, ?_⟩
  refine ⟨p150, ?_⟩
  refine ⟨p151, ?_⟩
  refine ⟨p152, ?_⟩
  refine ⟨p153, ?_⟩
  refine ⟨tl10_1_1_3, ?_⟩
  refine ⟨p155, ?_⟩
  refine ⟨p156, ?_⟩
  refine ⟨tl22_1_1_3, ?_⟩
  refine ⟨p158, ?_⟩
  refine ⟨p159, ?_⟩
  refine ⟨te33_1_1_3, ?_⟩
  refine ⟨p161, ?_⟩
  refine ⟨p162, ?_⟩
  refine ⟨tl41_1_1_3, ?_⟩
  refine ⟨p164, ?_⟩
  refine ⟨p165, ?_⟩
  refine ⟨op53_1_1_3, ?_⟩
  refine ⟨ol53_1_1_3, ?_⟩
  refine ⟨p168, ?_⟩
  refine ⟨to53_1_1_3, ?_⟩
  refine ⟨p170, ?_⟩
  refine ⟨p171, ?_⟩
  refine ⟨tl2_2_1_3, ?_⟩
  refine ⟨p173, ?_⟩
  refine ⟨p174, ?_⟩
  refine ⟨tl15_2_1_3, ?_⟩
  refine ⟨p176, ?_⟩
  refine ⟨p177, ?_⟩
  refine ⟨p178, ?_⟩
  refine ⟨te26_2_1_3, ?_⟩
  refine ⟨p180, ?_⟩
  refine ⟨tl32_2_1_3, ?_⟩
  refine ⟨p182, ?_⟩
  refine ⟨p183, ?_⟩
  refine ⟨te41_2_1_3, ?_⟩
  refine ⟨p185, ?_⟩
  refine ⟨p186, ?_⟩
  refine ⟨tl49_2_1_3, ?_⟩
  refine ⟨p188, ?_⟩
  refine ⟨op58_2_1_3, ?_⟩
  refine ⟨ol58_2_1_3, ?_⟩
  refine ⟨p191, ?_⟩
  refine ⟨to58_2_1_3, ?_⟩
  refine ⟨p193, ?_⟩
  refine ⟨p194, ?_⟩
  refine ⟨tl2_3_1_3, ?_⟩
  refine ⟨p196, ?_⟩
  refine ⟨p197, ?_⟩
  refine ⟨vp23_3_1_3, ?_⟩
  refine ⟨vl23_3_1_3, ?_⟩
  refine ⟨p200, ?_⟩
  refine ⟨te23_3_1_3, ?_⟩
  refine ⟨p202, ?_⟩
  refine ⟨p203, ?_⟩
  refine ⟨tsa4_w2a8_4_1_3, ?_⟩
  refine ⟨tsa4_w2ac_4_1_3, ?_⟩
  refine ⟨p206, ?_⟩
  refine ⟨p207, ?_⟩
  refine ⟨tl2_5_1_3, ?_⟩
  refine ⟨p209, ?_⟩
  refine ⟨p210, ?_⟩
  refine ⟨tl13_5_1_3, ?_⟩
  refine ⟨p212, ?_⟩
  refine ⟨p213, ?_⟩
  refine ⟨p214, ?_⟩
  refine ⟨te25_5_1_3, ?_⟩
  refine ⟨p216, ?_⟩
  refine ⟨tl31_5_1_3, ?_⟩
  refine ⟨p218, ?_⟩
  refine ⟨p219, ?_⟩
  refine ⟨te39_5_1_3, ?_⟩
  refine ⟨p221, ?_⟩
  refine ⟨tl45_5_1_3, ?_⟩
  refine ⟨p223, ?_⟩
  refine ⟨p224, ?_⟩
  refine ⟨p225, ?_⟩
  refine ⟨tl6_1_2_3, ?_⟩
  refine ⟨p227, ?_⟩
  refine ⟨op15_1_2_3, ?_⟩
  refine ⟨ol15_1_2_3, ?_⟩
  refine ⟨p230, ?_⟩
  refine ⟨to15_1_2_3, ?_⟩
  refine ⟨p232, ?_⟩
  refine ⟨tl20_1_2_3, ?_⟩
  refine ⟨p234, ?_⟩
  refine ⟨p235, ?_⟩
  refine ⟨p236, ?_⟩
  refine ⟨tsav_r24_2_2_3, ?_⟩
  refine ⟨tsav_w78_2_2_3, ?_⟩
  refine ⟨tsav_w1388_2_2_3, ?_⟩
  refine ⟨tsav_w138c_2_2_3, ?_⟩
  refine ⟨p241, ?_⟩
  refine ⟨p242, ?_⟩
  refine ⟨p243, ?_⟩
  refine ⟨u0, ?_⟩
  refine ⟨u1, ?_⟩
  refine ⟨u2, ?_⟩
  refine ⟨u3, ?_⟩
  refine ⟨u4, ?_⟩
  refine ⟨u5, ?_⟩
  refine ⟨u6, ?_⟩
  refine ⟨u7, ?_⟩
  refine ⟨u8, ?_⟩
  refine ⟨u9, ?_⟩
  refine ⟨u10, ?_⟩
  refine ⟨u11, ?_⟩
  refine ⟨u12, ?_⟩
  refine ⟨u13, ?_⟩
  refine ⟨u14, ?_⟩
  refine ⟨u15, ?_⟩
  refine ⟨u16, ?_⟩
  refine ⟨u17, ?_⟩
  refine ⟨u18, ?_⟩
  refine ⟨u19, ?_⟩
  refine ⟨u20, ?_⟩
  refine ⟨u21, ?_⟩
  refine ⟨u22, ?_⟩
  refine ⟨u23, ?_⟩
  refine ⟨u24, ?_⟩
  refine ⟨u25, ?_⟩
  refine ⟨u26, ?_⟩
  refine ⟨u27, ?_⟩
  refine ⟨u28, ?_⟩
  refine ⟨u29, ?_⟩
  refine ⟨u30, ?_⟩
  refine ⟨u31, ?_⟩
  refine ⟨k_3_3, ?_⟩
  refine ⟨dg'_3_3, ?_⟩
  refine ⟨flag'_3_3, ?_⟩
  refine ⟨cp'_3_3, ?_⟩
  refine ⟨rem'_3_3, ?_⟩
  refine ⟨p281, ?_⟩
  refine ⟨p282, ?_⟩
  refine ⟨p283, ?_⟩
  refine ⟨p284, ?_⟩
  refine ⟨op8_3_3, ?_⟩
  refine ⟨ol8_3_3, ?_⟩
  refine ⟨p287, ?_⟩
  refine ⟨te8_3_3, ?_⟩
  refine ⟨p289, ?_⟩
  refine ⟨p290, ?_⟩
  refine ⟨vp19_3_3, ?_⟩
  refine ⟨vl19_3_3, ?_⟩
  refine ⟨p293, ?_⟩
  refine ⟨te19_3_3, ?_⟩
  refine ⟨p295, ?_⟩
  refine ⟨sr24_3_3, ?_⟩
  refine ⟨ss24_3_3, ?_⟩
  refine ⟨p298, ?_⟩
  refine ⟨p299, ?_⟩
  refine ⟨tl13_1_4_3, ?_⟩
  refine ⟨p301, ?_⟩
  refine ⟨p302, ?_⟩
  refine ⟨p303, ?_⟩
  refine ⟨te26_1_4_3, ?_⟩
  refine ⟨p305, ?_⟩
  refine ⟨op32_1_4_3, ?_⟩
  refine ⟨ol32_1_4_3, ?_⟩
  refine ⟨p308, ?_⟩
  refine ⟨to32_1_4_3, ?_⟩
  refine ⟨p310, ?_⟩
  refine ⟨tl36_1_4_3, ?_⟩
  refine ⟨p312, ?_⟩
  refine ⟨p313, ?_⟩
  refine ⟨te45_1_4_3, ?_⟩
  refine ⟨p315, ?_⟩
  refine ⟨vp51_1_4_3, ?_⟩
  refine ⟨vl51_1_4_3, ?_⟩
  refine ⟨p318, ?_⟩
  refine ⟨te51_1_4_3, ?_⟩
  refine ⟨p320, ?_⟩
  refine ⟨p321, ?_⟩
  refine ⟨p322, ?_⟩
  refine ⟨tl2_2_4_3, ?_⟩
  refine ⟨p324, ?_⟩
  refine ⟨ip2_2_4_3, ?_⟩
  refine ⟨il2_2_4_3, ?_⟩
  refine ⟨p327, ?_⟩
  refine ⟨p328, ?_⟩
  refine ⟨tl13_2_4_3, ?_⟩
  refine ⟨p330, ?_⟩
  refine ⟨tm18_2_4_3, ?_⟩
  refine ⟨p332, ?_⟩
  refine ⟨tst3_w1328_3_4_3, ?_⟩
  refine ⟨tst3_w132c_3_4_3, ?_⟩
  refine ⟨p335, ?_⟩
  refine ⟨p336, ?_⟩
  refine ⟨tst4_r8_4_4_3, ?_⟩
  refine ⟨tst4_w1328_4_4_3, ?_⟩
  refine ⟨tst4_w132c_4_4_3, ?_⟩
  refine ⟨p340, ?_⟩
  refine ⟨p341, ?_⟩
  refine ⟨tst5_w1328_5_4_3, ?_⟩
  refine ⟨tst5_w132c_5_4_3, ?_⟩
  refine ⟨p344, ?_⟩
  refine ⟨p345, ?_⟩
  refine ⟨tst6_w1328_6_4_3, ?_⟩
  refine ⟨tst6_w132c_6_4_3, ?_⟩
  refine ⟨p348, ?_⟩
  refine ⟨p349, ?_⟩
  refine ⟨k_5_3, ?_⟩
  refine ⟨p351, ?_⟩
  refine ⟨p352, ?_⟩
  refine ⟨c'_5_3, ?_⟩
  refine ⟨q'_5_3, ?_⟩
  refine ⟨p355, ?_⟩
  refine ⟨p356, ?_⟩
  refine ⟨p357, ?_⟩
  refine ⟨p358, ?_⟩
  refine ⟨p359, ?_⟩
  refine ⟨p360, ?_⟩
  refine ⟨pv_7_3, ?_⟩
  refine ⟨p362, ?_⟩
  refine ⟨p363, ?_⟩
  refine ⟨ix7_1_1_4, ?_⟩
  refine ⟨p365, ?_⟩
  refine ⟨ix17_1_1_4, ?_⟩
  refine ⟨p367, ?_⟩
  refine ⟨ix25_1_1_4, ?_⟩
  refine ⟨p369, ?_⟩
  refine ⟨ix33_1_1_4, ?_⟩
  refine ⟨p371, ?_⟩
  refine ⟨p372, ?_⟩
  refine ⟨p373, ?_⟩
  refine ⟨p374, ?_⟩
  refine ⟨c'_2_4, ?_⟩
  refine ⟨p'_2_4, ?_⟩
  refine ⟨x21'_2_4, ?_⟩
  refine ⟨w60'_2_4, ?_⟩
  refine ⟨w70'_2_4, ?_⟩
  refine ⟨p380, ?_⟩
  refine ⟨p381, ?_⟩
  refine ⟨p382, ?_⟩
  refine ⟨bs7_2_4, ?_⟩
  refine ⟨p384, ?_⟩
  refine ⟨p385, ?_⟩
  refine ⟨k_3_4, ?_⟩
  refine ⟨p387, ?_⟩
  refine ⟨p388, ?_⟩
  refine ⟨c'_3_4, ?_⟩
  refine ⟨q'_3_4, ?_⟩
  refine ⟨w80'_3_4, ?_⟩
  refine ⟨p392, ?_⟩
  refine ⟨p393, ?_⟩
  refine ⟨p394, ?_⟩
  refine ⟨u32, ?_⟩
  refine ⟨u33, ?_⟩
  refine ⟨u34, ?_⟩
  refine ⟨u35, ?_⟩
  refine ⟨u36, ?_⟩
  refine ⟨u37, ?_⟩
  refine ⟨u38, ?_⟩
  refine ⟨u39, ?_⟩
  refine ⟨u40, ?_⟩
  refine ⟨u41, ?_⟩
  refine ⟨u42, ?_⟩
  refine ⟨u43, ?_⟩
  refine ⟨u44, ?_⟩
  refine ⟨u45, ?_⟩
  refine ⟨u46, ?_⟩
  refine ⟨u47, ?_⟩
  refine ⟨u48, ?_⟩
  refine ⟨u49, ?_⟩
  refine ⟨u50, ?_⟩
  refine ⟨u51, ?_⟩
  refine ⟨u52, ?_⟩
  refine ⟨u53, ?_⟩
  refine ⟨u54, ?_⟩
  refine ⟨u55, ?_⟩
  refine ⟨u56, ?_⟩
  refine ⟨u57, ?_⟩
  refine ⟨u58, ?_⟩
  refine ⟨u59, ?_⟩
  refine ⟨u60, ?_⟩
  refine ⟨sg_5_4, ?_⟩
  refine ⟨k_5_4, ?_⟩
  refine ⟨c'_5_4, ?_⟩
  refine ⟨x21'_5_4, ?_⟩
  refine ⟨rl'_5_4, ?_⟩
  refine ⟨rp'_5_4, ?_⟩
  refine ⟨dg'_5_4, ?_⟩
  refine ⟨w8'_5_4, ?_⟩
  refine ⟨wc'_5_4, ?_⟩
  refine ⟨w28'_5_4, ?_⟩
  refine ⟨w2c'_5_4, ?_⟩
  refine ⟨w30'_5_4, ?_⟩
  refine ⟨w38'_5_4, ?_⟩
  refine ⟨w40'_5_4, ?_⟩
  refine ⟨w5c'_5_4, ?_⟩
  refine ⟨sg'_5_4, ?_⟩
  refine ⟨p440, ?_⟩
  refine ⟨p441, ?_⟩
  refine ⟨p442, ?_⟩
  refine ⟨p443, ?_⟩
  refine ⟨p444, ?_⟩
  refine ⟨root6_3_6_4, ?_⟩
  refine ⟨p446, ?_⟩
  refine ⟨p447, ?_⟩
  refine ⟨p448, ?_⟩
  refine ⟨p449, ?_⟩
  refine ⟨p450, ?_⟩
  refine ⟨p451, ?_⟩
  refine ⟨p452, ?_⟩
  refine ⟨p453, ?_⟩
  refine ⟨p454, ?_⟩
  refine ⟨p455, ?_⟩
  exact SvOkRet.pre c1 (rk _ (by decide)) (rk _ (by decide)) hm hx

end C3.RV32.Sv
