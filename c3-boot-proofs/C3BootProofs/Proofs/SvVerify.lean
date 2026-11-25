import C3BootProofs.Proofs.SvEntry

/-!
# `sigstore::verify` from its entry to its return

Written by `scripts/gen-sv-entry.py` from `sv_pro` and `sv_verify_5c`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.P2v

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
/-- **`sigstore::verify`**: called with the bundle at `a1`, the trust root at `a2`, the artifact's digest at `a3`, and the result at `a0`, it returns `Err`, panics, or meets the success condition and returns `Ok`. -/
theorem sv_verify {Me : Word → BitVec 8} {n : Machine} {B : Word}
    (C : CodeIn Me SV sigstoreVerifyCode) (E : SvCode Me) (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (s : St Me SV n 0 (reg n)) (rsp : reg n sp = B + 0x2660) (hb : (reg n a1).toNat % 4 = 0)
    (sb : Sep (reg n a1) 8 (B + BitVec.ofNat 32 0x262C) 0x34)
    (hret : ((fun k => reg n (savedReg k))) 0 &&& ~~~1 = ((fun k => reg n (savedReg k))) 0)
    (hO : SvOut B (reg n a0))
    (lc_in : SvIn B (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4)).toNat)
    (D0 : P2Data Me)
    (SD0 : SvData Me)
    (H' : ∀ i, i < 8 → ∀ c'_4 q'_4, (c'_4, q'_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (((reg n a2)) + BitVec.ofNat 32 0x2C)) → (SvIn B (q'_4 + 0xFFFFFFFC) 4) ∧ (SvIn B (q'_4 + 0x0) 4) ∧ ((q'_4 + 0xFFFFFFFC).toNat % 4 = 0) ∧ ((q'_4 + 0x0).toNat % 4 = 0) ∧ ((memLoad32 Me (q'_4 + 0xFFFFFFFC)) ≠ 0 → SvIn B (memLoad32 Me (q'_4 + 0xFFFFFFFC)) (memLoad32 Me (q'_4 + 0x0)).toNat))
    (HE0 : HfEnv Me)
    (RS : SvRoSep B)
    (PE0 : PvEnv7 Me)
    (pkp_in : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x2C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4) 4)
    (apk : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x2C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4).toNat % 4 = 0)
    (pk_in : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x2C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (memLoad32 Me (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4)) 0x61)
    (side : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x2C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → ∀ M, PvSide M (memLoad32 Me (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4)) (B + 0x21A0 + BitVec.ofNat 32 0x170) 48 (B + 0x21A0 + BitVec.ofNat 32 0xC8)
      (B + 0x21A0 + BitVec.ofNat 32 0xF8))
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
    (hsgp_in : SvIn B ((reg n a1) + 0x8) 4)
    (hsgl_in : SvIn B ((reg n a1) + 0xC) 4)
    (asgp : ((reg n a1) + 0x8).toNat % 4 = 0)
    (asgl : ((reg n a1) + 0xC).toNat % 4 = 0)
    (sg_in : SvIn B (memLoad32 Me ((reg n a1) + 0x8)) (memLoad32 Me ((reg n a1) + 0xC)).toNat)
    (PE0' : P2vEnv Me)
    (dg_in : SvIn B (reg n a3) 32)
    (htsp_in : SvIn B ((reg n a1) + 0x20) 4)
    (htsl_in : SvIn B ((reg n a1) + 0x24) 4)
    (atsp : ((reg n a1) + 0x20).toNat % 4 = 0)
    (atsl : ((reg n a1) + 0x24).toNat % 4 = 0)
    (ts_in : SvIn B (memLoad32 Me ((reg n a1) + 0x20)) (memLoad32 Me ((reg n a1) + 0x24)).toNat)
    (D0' : SvData Me)
    (H'' : ∀ i, i < 8 → ∀ c'_6_3 q'_6_3, (c'_6_3, q'_6_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (((reg n a2)) + BitVec.ofNat 32 0x308)) → (SvIn B (q'_6_3 + 0x20) 4) ∧ (SvIn B (q'_6_3 + 0x24) 4) ∧ ((q'_6_3 + 0x20).toNat % 4 = 0) ∧ ((q'_6_3 + 0x24).toNat % 4 = 0) ∧ ((memLoad32 Me (q'_6_3 + 0x20)) ≠ 0 → SvIn B (memLoad32 Me (q'_6_3 + 0x20)) (memLoad32 Me (q'_6_3 + 0x24)).toNat))
    (S2 : SvSha2Code Me)
    (pkp_in' : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x308)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x18) 4)
    (apk' : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x308)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x18).toNat % 4 = 0)
    (pk_in' : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x308)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (memLoad32 Me (((y1) + BitVec.ofNat 32 0x20) + 0x18)) 0x61)
    (side' : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x308)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → ∀ M, PvSide M (memLoad32 Me (((y1) + BitVec.ofNat 32 0x20) + 0x18)) (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 (B + 0x21A0 + BitVec.ofNat 32 0x190)
      (B + 0x21A0 + BitVec.ofNat 32 0x1C0))
    (CK0 : SvCkCode Me)
    (ckp_in4 : SvIn B ((reg n a1) + 0x18) 4)
    (ckl_in4 : SvIn B ((reg n a1) + 0x1C) 4)
    (a_ckp : ((reg n a1) + 0x18).toNat % 4 = 0)
    (a_ckl : ((reg n a1) + 0x1C).toNat % 4 = 0)
    (ck_in : SvIn B (memLoad32 Me ((reg n a1) + 0x18)) (memLoad32 Me ((reg n a1) + 0x1C)).toNat)
    (H''' : ∀ i, i < 16 → ∀ c'_3_4 q'_3_4, (c'_3_4, q'_3_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), (((reg n a2)) + BitVec.ofNat 32 0x108)) → (SvIn B (q'_3_4 + 0x20) 4) ∧ (SvIn B (q'_3_4 + 0x24) 4) ∧ ((q'_3_4 + 0x20).toNat % 4 = 0) ∧ ((q'_3_4 + 0x24).toNat % 4 = 0) ∧ ((memLoad32 Me (q'_3_4 + 0x20)) ≠ 0 → SvIn B (memLoad32 Me (q'_3_4 + 0x20)) (memLoad32 Me (q'_3_4 + 0x24)).toNat))
    (kp_in4 : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), ((reg n a2) + BitVec.ofNat 32 0x108)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x18) 4)
    (kw_in4 : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), ((reg n a2) + BitVec.ofNat 32 0x108)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x1C) 4)
    (a_kp : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), ((reg n a2) + BitVec.ofNat 32 0x108)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x18).toNat % 4 = 0)
    (a_kw : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), ((reg n a2) + BitVec.ofNat 32 0x108)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x1C).toNat % 4 = 0)
    (kp_in : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), ((reg n a2) + BitVec.ofNat 32 0x108)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (memLoad32 Me (((y1) + BitVec.ofNat 32 0x20) + 0x18)) 32)
    (EE0 : EvEnv Me)
    (hiv : (s5Hv Me (BitVec.ofNat 32 (img% sha512IVAddress))).toList = Sha512.h0)
    (pk_in'' : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), ((reg n a2) + BitVec.ofNat 32 0x108)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (memLoad32 Me (((y1) + BitVec.ofNat 32 0x20) + 0x18)) 32)
    (lid_in : ∀ i, i < 16 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), ((reg n a2) + BitVec.ofNat 32 0x108)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + BitVec.ofNat 32 0x5) 19)
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
    (ii2h : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x2C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8) 4)
    (ai2h : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x2C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8).toNat % 4 = 0)
    (ii2l : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x2C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE4) 4)
    (ai2l : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x2C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE4).toNat % 4 = 0)
    (ii3h : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x2C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0) 4)
    (ai3h : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x2C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0).toNat % 4 = 0)
    (ii3l : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x2C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFEC) 4)
    (ai3l : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x2C)) → (memLoad32 Me (y1 + 0xFFFFFFFC)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xFFFFFFEC).toNat % 4 = 0)
    (it4h : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x308)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0xC) 4)
    (at4h : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x308)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0xC).toNat % 4 = 0)
    (it4l : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x308)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x8) 4)
    (at4l : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x308)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x8).toNat % 4 = 0)
    (it5h : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x308)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x14) 4)
    (at5h : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x308)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x14).toNat % 4 = 0)
    (it5l : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x308)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x10) 4)
    (at5l : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((reg n a2) + BitVec.ofNat 32 0x308)) → (memLoad32 Me (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x10).toNat % 4 = 0)
    (hOk : SvOutOk B (reg n a0)) :
    SvErrRet B (reg n a0) (fun k => reg n (savedReg k)) n ∨ Panics n ∨
    (∃ t_1_1_1, derElement 0x30 (memBytes Me (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4)).toNat) = .ok t_1_1_1 ∧ (memLoad32 Me (reg n a1 + 4)) - BitVec.ofNat 32 (t_1_1_1.header + t_1_1_1.len) = 0 ∧
      ∃ tl1_2_1_1, derElement 0x30 (memBytes Me (((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) ((BitVec.ofNat 32 t_1_1_1.len)).toNat) = .ok tl1_2_1_1 ∧
      ∃ tl8_2_1_1, derElement 0x30 (memBytes Me ((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) (((BitVec.ofNat 32 t_1_1_1.len)) - BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)).toNat) = .ok tl8_2_1_1 ∧
      ∃ tl16_2_1_1, derElement 3 (memBytes Me (((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) + BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) ((((BitVec.ofNat 32 t_1_1_1.len)) - BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) - BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)).toNat) = .ok tl16_2_1_1 ∧
      ∃ bp16_2_1_1 bl16_2_1_1, derBitsOf (memBytes Me (((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) + BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) ((((BitVec.ofNat 32 t_1_1_1.len)) - BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) - BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)).toNat) (((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) + BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) (.ok tl16_2_1_1) = .ok (bp16_2_1_1, bl16_2_1_1) ∧
      (((((BitVec.ofNat 32 t_1_1_1.len)) - BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) - BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) - BitVec.ofNat 32 (tl16_2_1_1.header + tl16_2_1_1.len) = 0) ∧
      ∃ tl28_2_1_1, derOptRes 0xA0 (memBytes Me ((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) (BitVec.ofNat 32 tl1_2_1_1.len).toNat) = some (.ok tl28_2_1_1) ∧
      derIntIsOf Me (memBytes Me (((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 tl28_2_1_1.header) (BitVec.ofNat 32 tl28_2_1_1.len).toNat) (((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 tl28_2_1_1.header) (derElement 2 (memBytes Me (((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 tl28_2_1_1.header) (BitVec.ofNat 32 tl28_2_1_1.len).toNat)) ((BitVec.ofNat 32 0x2).extractLsb' 0 8) = .ok true ∧
      ∃ te41_2_1_1, derElement 2 (memBytes Me (((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 tl28_2_1_1.header) (BitVec.ofNat 32 tl28_2_1_1.len).toNat) = .ok te41_2_1_1 ∧
      ((BitVec.ofNat 32 tl28_2_1_1.len) - BitVec.ofNat 32 (te41_2_1_1.header + te41_2_1_1.len) = 0) ∧
      ∃ tl1_3_1_1, derElement 2 (memBytes Me ((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) (((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))).toNat) = .ok tl1_3_1_1 ∧
      ∃ ip1_3_1_1 il1_3_1_1, derPosIntOf (memBytes Me ((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) (((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))).toNat) ((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) (.ok tl1_3_1_1) = .ok (ip1_3_1_1, il1_3_1_1) ∧
      ((il1_3_1_1).toNat ≤ 20) ∧
      ∃ tl8_3_1_1, derElement 0x30 (memBytes Me (((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) ((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) - BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)).toNat) = .ok tl8_3_1_1 ∧
      ∃ op21_3_1_1 ol21_3_1_1, derAlgOf Me (((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) (tl8_3_1_1.header + tl8_3_1_1.len) = .ok ((op21_3_1_1, ol21_3_1_1), none) ∧
      (memBytes Me op21_3_1_1 ol21_3_1_1 = memBytes Me (BitVec.ofNat 32 (img% svOidEcdsaSha384Address)) 8) ∧
      ∃ tl3_4_1_1, derElement 0x30 (memBytes Me (((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) ((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) - BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) - BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))).toNat) = .ok tl3_4_1_1 ∧
      ∃ tl11_4_1_1, derElement 0x30 (memBytes Me ((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) (((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) - BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) - BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) - BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)).toNat) = .ok tl11_4_1_1 ∧
      ∃ tm20_4_1_1 rs20_4_1_1, readTime (memBytes Me (((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 tl11_4_1_1.header) (tl11_4_1_1.len)) = some (tm20_4_1_1, rs20_4_1_1) ∧
      ∃ tm28_4_1_1 rs28_4_1_1, readTime rs20_4_1_1 = some (tm28_4_1_1, rs28_4_1_1) ∧
      (rs28_4_1_1 = []) ∧
      ∃ tl2_5_1_1, derElement 0x30 (memBytes Me ((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) (((((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) - BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) - BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) - BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) - BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))).toNat) = .ok tl2_5_1_1 ∧
      ∃ tl6_5_1_1, derElement 0x30 (memBytes Me (((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) ((((((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) - BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) - BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) - BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) - BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) - BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)).toNat) = .ok tl6_5_1_1 ∧
      ∃ op15_5_1_1 ol15_5_1_1 prp15_5_1_1 pu15_5_1_1, derAlgOf Me ((((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) (tl6_5_1_1.len) = .ok ((op15_5_1_1, ol15_5_1_1), some (prp15_5_1_1, pu15_5_1_1)) ∧
      ∃ ta15_5_1_1, derElement 0x30 (memBytes Me ((((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) (tl6_5_1_1.len)) = .ok ta15_5_1_1 ∧
      (BitVec.ofNat 8 pu15_5_1_1.tag = BitVec.ofNat 8 6) ∧
      (memBytes Me (prp15_5_1_1 + BitVec.ofNat 32 pu15_5_1_1.header) pu15_5_1_1.len = memBytes Me (BitVec.ofNat 32 (img% svOidPrime256v1Address)) 8) ∧
      (memBytes Me op15_5_1_1 ol15_5_1_1 = memBytes Me (BitVec.ofNat 32 (img% svOidEcPublicKeyAddress)) 7) ∧
      ∃ tl35_5_1_1, derElement 3 (memBytes Me (((((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) + BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)) ((BitVec.ofNat 32 (tl6_5_1_1.len)) - BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)).toNat) = .ok tl35_5_1_1 ∧
      ∃ bp35_5_1_1 bl35_5_1_1, derBitsOf (memBytes Me (((((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) + BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)) ((BitVec.ofNat 32 (tl6_5_1_1.len)) - BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)).toNat) (((((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 tl6_5_1_1.header) + BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)) (.ok tl35_5_1_1) = .ok (bp35_5_1_1, bl35_5_1_1) ∧
      (bl35_5_1_1 = BitVec.ofNat 32 0x41) ∧
      (((BitVec.ofNat 32 (tl6_5_1_1.len)) - BitVec.ofNat 32 (ta15_5_1_1.header + ta15_5_1_1.len)) - BitVec.ofNat 32 (tl35_5_1_1.header + tl35_5_1_1.len) = 0) ∧
      (Me bp35_5_1_1 = BitVec.ofNat 8 4) ∧
      (GsOk Me bp35_5_1_1) ∧
      ∃ tl9_6_1_1, derOptRes 0xA3 (memBytes Me (((((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) ((((((((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) - BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) - BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) - BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) - BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) - BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) - BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))).toNat) = some (.ok tl9_6_1_1) ∧
      (((((((((((((BitVec.ofNat 32 tl1_2_1_1.len) - BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) - BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) - BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) - BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) - BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) - BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) - BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) - BitVec.ofNat 32 (tl9_6_1_1.header + tl9_6_1_1.len) = 0) ∧
      ∃ tl24_6_1_1, derElement 0x30 (memBytes Me ((((((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) + BitVec.ofNat 32 tl9_6_1_1.header) (BitVec.ofNat 32 tl9_6_1_1.len).toNat) = .ok tl24_6_1_1 ∧
      ((BitVec.ofNat 32 tl9_6_1_1.len) - BitVec.ofNat 32 (tl24_6_1_1.header + tl24_6_1_1.len) = 0) ∧
      ∃ u0_1 u1_1 u2_1, ∃ k_2_1 f2c'_2_1 f30'_2_1 rem'_2_1 sl0'_2_1 sl1'_2_1 sl2'_2_1 sl3'_2_1 sl4'_2_1 sl5'_2_1 sl6'_2_1 sl7'_2_1 sl8'_2_1 sl9'_2_1 cur'_2_1, svChain (sv_extStep B (reg n a0) (reg n a1) ((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header) (reg n a3) (reg n a2) (memLoad32 Me (reg n a1 + 4)) bp16_2_1_1 bp35_5_1_1 bl16_2_1_1 (BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) (((((((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) + BitVec.ofNat 32 tl9_6_1_1.header) + BitVec.ofNat 32 tl24_6_1_1.header) (BitVec.ofNat 32 tl24_6_1_1.len) (BitVec.ofNat 32 (tm28_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm28_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm20_4_1_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm20_4_1_1 % 2 ^ 32)) (BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) ((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len)) (memLoad32 Me (reg n a1)) (BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len)) (((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) (BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)) ((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) ((fun k => reg n (savedReg k))) Me) k_2_1 ((BitVec.ofNat 32 0x0), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 tl24_6_1_1.len), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 tl24_6_1_1.len), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 (tl24_6_1_1.header + tl24_6_1_1.len)), (BitVec.ofNat 32 0x0), (u0_1), (BitVec.ofNat 32 0x0), (u1_1), (BitVec.ofNat 32 0x0), (u2_1), (((((((((((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len))) + BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) + BitVec.ofNat 32 (tl11_4_1_1.header + tl11_4_1_1.len))) + BitVec.ofNat 32 (tl2_5_1_1.header + tl2_5_1_1.len)) + BitVec.ofNat 32 (tl6_5_1_1.header + tl6_5_1_1.len))) + BitVec.ofNat 32 tl9_6_1_1.header) + BitVec.ofNat 32 tl24_6_1_1.header)) (f2c'_2_1, f30'_2_1, rem'_2_1, sl0'_2_1, sl1'_2_1, sl2'_2_1, sl3'_2_1, sl4'_2_1, sl5'_2_1, sl6'_2_1, sl7'_2_1, sl8'_2_1, sl9'_2_1, cur'_2_1) ∧
      rem'_2_1 = 0 ∧ (sl0'_2_1 = 0 ∨ SvIn B sl0'_2_1 sl1'_2_1.toNat) ∧ (sl2'_2_1 = 0 ∨ SvIn B sl2'_2_1 sl3'_2_1.toNat) ∧ (sl4'_2_1 = 0 ∨ SvIn B sl4'_2_1 sl5'_2_1.toNat) ∧ (sl6'_2_1 = 0 ∨ SvIn B sl6'_2_1 sl7'_2_1.toNat) ∧ (sl8'_2_1 = 0 ∨ SvIn B sl8'_2_1 sl9'_2_1.toNat) ∧
      (sl0'_2_1 ≠ 0) ∧ (sl2'_2_1 ≠ 0) ∧ (sl4'_2_1 ≠ 0) ∧ (sl6'_2_1 ≠ 0) ∧ ((if BitVec.ult 0 (sl8'_2_1) then (1 : Word) else 0) &&& ((f2c'_2_1) &&& (f30'_2_1)) ≠ 0) ∧ (memBytes Me ((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) ((BitVec.ofNat 32 (tl8_2_1_1.header + tl8_2_1_1.len)).toNat) = memBytes Me (((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) ((BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len)).toNat)) ∧ ∃ sr40_2_1 ss40_2_1, ecdsaSigOf 48 Me (bp16_2_1_1) ((bl16_2_1_1.toNat)) = .ok (sr40_2_1, ss40_2_1) ∧
      ∃ k_4_1, k_4_1 < 8 ∧
      (∀ i, i < k_4_1 → ∀ c'_4_1 q'_4_1, (c'_4_1, q'_4_1) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (((reg n a2)) + BitVec.ofNat 32 0x2C)) → ¬ (memBytes Me (memLoad32 Me (q'_4_1 + 0xFFFFFFFC)) (memLoad32 Me (q'_4_1 + 0x0)).toNat = memBytes Me ((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len)) (BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)).toNat)) ∧
      ∃ c'_4_1 q'_4_1, (c'_4_1, q'_4_1) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) k_4_1 ((BitVec.ofNat 32 0x100), (((reg n a2)) + BitVec.ofNat 32 0x2C)) ∧ (memBytes Me (memLoad32 Me (q'_4_1 + 0xFFFFFFFC)) (memLoad32 Me (q'_4_1 + 0x0)).toNat = memBytes Me ((((((((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len)) (BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)).toNat) ∧
      ((memLoad32 Me (q'_4_1 + 0xFFFFFFFC)) ≠ 0) ∧
      ∃ pv_5_1, SvPvRes Me (memLoad32 Me (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4)) (B + 0x21A0 + BitVec.ofNat 32 0x170) 48 (sha384 (memBytes Me ((memLoad32 Me (reg n a1)) + BitVec.ofNat 32 t_1_1_1.header) (BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)).toNat)) (B + 0x21A0 + BitVec.ofNat 32 0xC8) (B + 0x21A0 + BitVec.ofNat 32 0xF8) sr40_2_1 ss40_2_1 (some pv_5_1) ∧
      (pv_5_1 ≠ 0) ∧
      (memBytes Me sl0'_2_1 sl1'_2_1.toNat = memBytes Me (memLoad32 Me ((reg n a2) + 0x0)) (memLoad32 Me ((reg n a2) + 0x4)).toNat) ∧
      (memBytes Me sl2'_2_1 sl3'_2_1.toNat = memBytes Me (memLoad32 Me ((reg n a2) + 0x8)) (memLoad32 Me ((reg n a2) + 0xC)).toNat) ∧
      (memBytes Me sl4'_2_1 sl5'_2_1.toNat = memBytes Me (memLoad32 Me ((reg n a2) + 0x10)) (memLoad32 Me ((reg n a2) + 0x14)).toNat) ∧
      (memBytes Me sl6'_2_1 sl7'_2_1.toNat = memBytes Me (memLoad32 Me ((reg n a2) + 0x18)) (memLoad32 Me ((reg n a2) + 0x1C)).toNat) ∧
      (memBytes Me sl8'_2_1 sl9'_2_1.toNat = memBytes Me (memLoad32 Me ((reg n a2) + 0x20)) (memLoad32 Me ((reg n a2) + 0x24)).toNat) ∧
      ∃ sr43_6_1 ss43_6_1, ecdsaSigOf 32 Me ((memLoad32 Me ((reg n a1) + 0x8))) ((memLoad32 Me ((reg n a1) + 0xC)).toNat) = .ok (sr43_6_1, ss43_6_1) ∧
      SvP256Facts Me bp35_5_1_1 (reg n a3) (b32 sr43_6_1) (b32 ss43_6_1) ∧
      ∃ tl10_1_1_3, derElement 0x30 (memBytes Me ((memLoad32 Me ((reg n a1) + 0x20))) ((memLoad32 Me ((reg n a1) + 0x24))).toNat) = .ok tl10_1_1_3 ∧
      (((memLoad32 Me ((reg n a1) + 0x24))) - BitVec.ofNat 32 (tl10_1_1_3.header + tl10_1_1_3.len) = 0) ∧
      ∃ tl21_1_1_3, derElement 0x30 (memBytes Me (((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) (BitVec.ofNat 32 tl10_1_1_3.len).toNat) = .ok tl21_1_1_3 ∧
      derIntIsOf Me (memBytes Me ((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 tl21_1_1_3.header) (BitVec.ofNat 32 tl21_1_1_3.len).toNat) ((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 tl21_1_1_3.header) (derElement 2 (memBytes Me ((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 tl21_1_1_3.header) (BitVec.ofNat 32 tl21_1_1_3.len).toNat)) ((BitVec.ofNat 32 0x0).extractLsb' 0 8) = .ok true ∧
      ∃ te30_1_1_3, derElement 2 (memBytes Me ((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 tl21_1_1_3.header) (BitVec.ofNat 32 tl21_1_1_3.len).toNat) = .ok te30_1_1_3 ∧
      ((BitVec.ofNat 32 tl21_1_1_3.len) - BitVec.ofNat 32 (te30_1_1_3.header + te30_1_1_3.len) = 0) ∧
      ∃ tl2_2_1_3, derElement 0x30 (memBytes Me (((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) (((BitVec.ofNat 32 tl10_1_1_3.len) - BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))).toNat) = .ok tl2_2_1_3 ∧
      ((((BitVec.ofNat 32 tl10_1_1_3.len) - BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) - BitVec.ofNat 32 (tl2_2_1_3.header + tl2_2_1_3.len) = 0) ∧
      ∃ op13_2_1_3 ol13_2_1_3, derContent ((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) (derOid (memBytes Me ((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) (BitVec.ofNat 32 tl2_2_1_3.len).toNat)) = .ok (op13_2_1_3, ol13_2_1_3) ∧
      ∃ to13_2_1_3, derOid (memBytes Me ((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) (BitVec.ofNat 32 tl2_2_1_3.len).toNat) = .ok to13_2_1_3 ∧
      (memBytes Me op13_2_1_3 ol13_2_1_3.toNat = memBytes Me (BitVec.ofNat 32 (img% svConstCmsAddress)) 9) ∧
      ∃ tl21_2_1_3, derElement 0xA0 (memBytes Me (((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) ((BitVec.ofNat 32 tl2_2_1_3.len) - BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)).toNat) = .ok tl21_2_1_3 ∧
      (((BitVec.ofNat 32 tl2_2_1_3.len) - BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) - BitVec.ofNat 32 (tl21_2_1_3.header + tl21_2_1_3.len) = 0) ∧
      ∃ tl32_2_1_3, derElement 0x30 (memBytes Me ((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) (BitVec.ofNat 32 tl21_2_1_3.len).toNat) = .ok tl32_2_1_3 ∧
      ((BitVec.ofNat 32 tl21_2_1_3.len) - BitVec.ofNat 32 (tl32_2_1_3.header + tl32_2_1_3.len) = 0) ∧
      derIntIsOf Me (memBytes Me (((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) (BitVec.ofNat 32 tl32_2_1_3.len).toNat) (((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) (derElement 2 (memBytes Me (((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) (BitVec.ofNat 32 tl32_2_1_3.len).toNat)) ((BitVec.ofNat 32 0x3).extractLsb' 0 8) = .ok true ∧
      ∃ te43_2_1_3, derElement 2 (memBytes Me (((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) (BitVec.ofNat 32 tl32_2_1_3.len).toNat) = .ok te43_2_1_3 ∧
      ∃ tl2_3_1_3, derElement 0x31 (memBytes Me (((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) (((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))).toNat) = .ok tl2_3_1_3 ∧
      isSha256Of Me ((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 tl2_3_1_3.header) (BitVec.ofNat 32 tl2_3_1_3.len).toNat = .ok true ∧
      ∃ te11_3_1_3, derElement 0x30 (memBytes Me ((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 tl2_3_1_3.header) (BitVec.ofNat 32 tl2_3_1_3.len).toNat) = .ok te11_3_1_3 ∧
      ((BitVec.ofNat 32 tl2_3_1_3.len) - BitVec.ofNat 32 (te11_3_1_3.header + te11_3_1_3.len) = 0) ∧
      ∃ tl19_3_1_3, derElement 0x30 (memBytes Me ((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) ((((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) - BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)).toNat) = .ok tl19_3_1_3 ∧
      ∃ op28_3_1_3 ol28_3_1_3, derContent (((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 tl19_3_1_3.header) (derOid (memBytes Me (((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 tl19_3_1_3.header) (BitVec.ofNat 32 tl19_3_1_3.len).toNat)) = .ok (op28_3_1_3, ol28_3_1_3) ∧
      ∃ to28_3_1_3, derOid (memBytes Me (((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 tl19_3_1_3.header) (BitVec.ofNat 32 tl19_3_1_3.len).toNat) = .ok to28_3_1_3 ∧
      (memBytes Me op28_3_1_3 ol28_3_1_3.toNat = memBytes Me (BitVec.ofNat 32 (img% svConstCmsAddress + 0x9)) 11) ∧
      ∃ tl2_4_1_3, derOptRes 0xA0 (memBytes Me (((((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 tl19_3_1_3.header) + BitVec.ofNat 32 (to28_3_1_3.header + to28_3_1_3.len))) (((BitVec.ofNat 32 tl19_3_1_3.len) - BitVec.ofNat 32 (to28_3_1_3.header + to28_3_1_3.len))).toNat) = some (.ok tl2_4_1_3) ∧
      ((((BitVec.ofNat 32 tl19_3_1_3.len) - BitVec.ofNat 32 (to28_3_1_3.header + to28_3_1_3.len))) - BitVec.ofNat 32 (tl2_4_1_3.header + tl2_4_1_3.len) = 0) ∧
      ∃ vp23_4_1_3 vl23_4_1_3, derContent ((((((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 tl19_3_1_3.header) + BitVec.ofNat 32 (to28_3_1_3.header + to28_3_1_3.len))) + BitVec.ofNat 32 tl2_4_1_3.header) (derElement 4 (memBytes Me ((((((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 tl19_3_1_3.header) + BitVec.ofNat 32 (to28_3_1_3.header + to28_3_1_3.len))) + BitVec.ofNat 32 tl2_4_1_3.header) (BitVec.ofNat 32 tl2_4_1_3.len).toNat)) = .ok (vp23_4_1_3, vl23_4_1_3) ∧
      ∃ te23_4_1_3, derElement 4 (memBytes Me ((((((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 tl19_3_1_3.header) + BitVec.ofNat 32 (to28_3_1_3.header + to28_3_1_3.len))) + BitVec.ofNat 32 tl2_4_1_3.header) (BitVec.ofNat 32 tl2_4_1_3.len).toNat) = .ok te23_4_1_3 ∧
      ((BitVec.ofNat 32 tl2_4_1_3.len) - BitVec.ofNat 32 (te23_4_1_3.header + te23_4_1_3.len) = 0) ∧
      ∃ tr5_w328_5_1_3 : Word, ∃ tr5_w32c_5_1_3 : Word, (((derOptRes 0xA0 (memBytes Me ((((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))) ((((((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) - BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) - BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))).toNat) = none) ∧ ((((((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) - BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) - BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len)) = 0 ∨ (Me ((((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len)))).toNat ≠ 0xA1) ∧ tr5_w328_5_1_3 = (((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len)) ∧ tr5_w32c_5_1_3 = (((((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) - BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) - BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))) ∨ ((¬ (derOptRes 0xA0 (memBytes Me ((((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))) ((((((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) - BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) - BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))).toNat) = none)) ∧ ∃ tl2, derOptRes 0xA0 (memBytes Me ((((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))) ((((((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) - BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) - BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))).toNat) = some (.ok tl2) ∧ (((((((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) - BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) - BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0 ∨ (Me (((((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))) + BitVec.ofNat 32 (tl2.header + tl2.len))).toNat ≠ 0xA1) ∧ tr5_w328_5_1_3 = ((((((((((((((memLoad32 Me ((reg n a1) + 0x20))) + BitVec.ofNat 32 tl10_1_1_3.header) + BitVec.ofNat 32 (tl21_1_1_3.header + tl21_1_1_3.len))) + BitVec.ofNat 32 tl2_2_1_3.header) + BitVec.ofNat 32 (to13_2_1_3.header + to13_2_1_3.len)) + BitVec.ofNat 32 tl21_2_1_3.header) + BitVec.ofNat 32 tl32_2_1_3.header) + BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) + BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) + BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tr5_w32c_5_1_3 = ((((((BitVec.ofNat 32 tl32_2_1_3.len) - BitVec.ofNat 32 (te43_2_1_3.header + te43_2_1_3.len))) - BitVec.ofNat 32 (tl2_3_1_3.header + tl2_3_1_3.len)) - BitVec.ofNat 32 (tl19_3_1_3.header + tl19_3_1_3.len))) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tr5_w328_5_1_3 tr5_w32c_5_1_3.toNat ∧
      ∃ tl2_6_1_3, derElement 0x31 (memBytes Me (tr5_w328_5_1_3) (tr5_w32c_5_1_3).toNat) = .ok tl2_6_1_3 ∧
      ((tr5_w32c_5_1_3) - BitVec.ofNat 32 (tl2_6_1_3.header + tl2_6_1_3.len) = 0) ∧
      ∃ tl13_6_1_3, derElement 0x30 (memBytes Me ((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) (BitVec.ofNat 32 tl2_6_1_3.len).toNat) = .ok tl13_6_1_3 ∧
      ((BitVec.ofNat 32 tl2_6_1_3.len) - BitVec.ofNat 32 (tl13_6_1_3.header + tl13_6_1_3.len) = 0) ∧
      derIntIsOf Me (memBytes Me (((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) (BitVec.ofNat 32 tl13_6_1_3.len).toNat) (((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) (derElement 2 (memBytes Me (((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) (BitVec.ofNat 32 tl13_6_1_3.len).toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = .ok true ∧
      ∃ te25_6_1_3, derElement 2 (memBytes Me (((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) (BitVec.ofNat 32 tl13_6_1_3.len).toNat) = .ok te25_6_1_3 ∧
      ∃ tl31_6_1_3, derElement 0x30 (memBytes Me ((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) ((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)).toNat) = .ok tl31_6_1_3 ∧
      isSha256Of Me (((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) (((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) - BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)).toNat = .ok true ∧
      ∃ te39_6_1_3, derElement 0x30 (memBytes Me (((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) (((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) - BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)).toNat) = .ok te39_6_1_3 ∧
      ∃ tl45_6_1_3, derOptRes 0xA0 (memBytes Me ((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) ((((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) - BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) - BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)).toNat) = some (.ok tl45_6_1_3) ∧
      ((BitVec.ofNat 32 tl45_6_1_3.len) ≠ 0) ∧
      (((BitVec.ofNat 32 tl45_6_1_3.len)).toNat ≤ ((BitVec.ofNat 32 tl45_6_1_3.len)).toNat) ∧
      ∃ tl6_1_2_3, derElement 0x30 (memBytes Me ((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) ((BitVec.ofNat 32 tl45_6_1_3.len)).toNat) = .ok tl6_1_2_3 ∧
      ∃ op15_1_2_3 ol15_1_2_3, derContent (((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) (derOid (memBytes Me (((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) (BitVec.ofNat 32 tl6_1_2_3.len).toNat)) = .ok (op15_1_2_3, ol15_1_2_3) ∧
      ∃ to15_1_2_3, derOid (memBytes Me (((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) (BitVec.ofNat 32 tl6_1_2_3.len).toNat) = .ok to15_1_2_3 ∧
      ∃ tl20_1_2_3, derElement 0x31 (memBytes Me ((((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) ((BitVec.ofNat 32 tl6_1_2_3.len) - BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)).toNat) = .ok tl20_1_2_3 ∧
      (((BitVec.ofNat 32 tl6_1_2_3.len) - BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) - BitVec.ofNat 32 (tl20_1_2_3.header + tl20_1_2_3.len) = 0) ∧
      listsOidOf Me (((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header) (((BitVec.ofNat 32 tl45_6_1_3.len)) - ((BitVec.ofNat 32 tl45_6_1_3.len))).toNat (memBytes Me op15_1_2_3 ol15_1_2_3.toNat) = .ok false ∧
      ∃ trv_w64_2_2_3 : Word, ∃ trv_w7c_2_2_3 : Word, (((memBytes Me op15_1_2_3 ol15_1_2_3.toNat = memBytes Me (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9) ∧ ∃ op5 ol5, derContent ((((((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) (derOid (memBytes Me ((((((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat)) = .ok (op5, ol5) ∧ ∃ to5, derOid (memBytes Me ((((((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat) = .ok to5 ∧ (memBytes Me op5 ol5.toNat = memBytes Me (BitVec.ofNat 32 (img% svConstCmsAddress + 0x9)) 11) ∧ (((BitVec.ofNat 32 tl20_1_2_3.len)) - BitVec.ofNat 32 (to5.header + to5.len) = 0) ∧ trv_w64_2_2_3 = (BitVec.ofNat 32 0x0) ∧ trv_w7c_2_2_3 = BitVec.ofNat 32 0x1) ∨ ((¬ (memBytes Me op15_1_2_3 ol15_1_2_3.toNat = memBytes Me (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9)) ∧ (memBytes Me op15_1_2_3 ol15_1_2_3.toNat = memBytes Me (BitVec.ofNat 32 (img% svConstCmsAddress + 0x1E)) 9) ∧ ∃ vp8 vl8, derContent ((((((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) (derElement 4 (memBytes Me ((((((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat)) = .ok (vp8, vl8) ∧ ∃ te8, derElement 4 (memBytes Me ((((((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 tl6_1_2_3.header) + BitVec.ofNat 32 (to15_1_2_3.header + to15_1_2_3.len)) + BitVec.ofNat 32 tl20_1_2_3.header)) ((BitVec.ofNat 32 tl20_1_2_3.len)).toNat) = .ok te8 ∧ (vl8 = 32) ∧ (((BitVec.ofNat 32 tl20_1_2_3.len)) - BitVec.ofNat 32 (te8.header + te8.len) = 0) ∧ trv_w64_2_2_3 = vp8 ∧ trv_w7c_2_2_3 = (BitVec.ofNat 32 0x0)) ∨ ((¬ (memBytes Me op15_1_2_3 ol15_1_2_3.toNat = memBytes Me (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9)) ∧ (¬ (memBytes Me op15_1_2_3 ol15_1_2_3.toNat = memBytes Me (BitVec.ofNat 32 (img% svConstCmsAddress + 0x1E)) 9)) ∧ trv_w64_2_2_3 = (BitVec.ofNat 32 0x0) ∧ trv_w7c_2_2_3 = (BitVec.ofNat 32 0x0))) ∧ (trv_w64_2_2_3 = 0 ∨ SvIn B trv_w64_2_2_3 32) ∧
      ∃ k_3_3 dg'_3_3 flag'_3_3 cp'_3_3 rem'_3_3, svChain (sv_attrStep B (reg n a0) (reg n a1) (reg n a3) (reg n a2) (memLoad32 Me (reg n a1 + 4)) ((q'_4_1) + BitVec.ofNat 32 0x20) (((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header) (BitVec.ofNat 32 tl45_6_1_3.len) (((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len)) (((((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) - BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) - BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) - BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len)) ((fun k => reg n (savedReg k))) Me) k_3_3 (trv_w64_2_2_3, trv_w7c_2_2_3, (((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 tl45_6_1_3.header)) + BitVec.ofNat 32 (tl6_1_2_3.header + tl6_1_2_3.len)), (((BitVec.ofNat 32 tl45_6_1_3.len)) - BitVec.ofNat 32 (tl6_1_2_3.header + tl6_1_2_3.len))) (dg'_3_3, flag'_3_3, cp'_3_3, rem'_3_3) ∧
      rem'_3_3 = 0 ∧ (dg'_3_3 = 0 ∨ SvIn B dg'_3_3 32) ∧
      (dg'_3_3 ≠ 0 ∧ flag'_3_3 = 1) ∧ ∃ op9_3_3 ol9_3_3, derAlgOf Me ((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))) (((((((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) - BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) - BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) - BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))).toNat) = .ok ((op9_3_3, ol9_3_3), none) ∧ ∃ te9_3_3, derElement 0x30 (memBytes Me ((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))) ((((((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) - BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) - BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) - BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))).toNat) = .ok te9_3_3 ∧ (memBytes Me op9_3_3 ol9_3_3 = memBytes Me (BitVec.ofNat 32 (img% svConstAddress)) 8) ∧ ∃ vp20_3_3 vl20_3_3, derContent (((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))) + BitVec.ofNat 32 (te9_3_3.header + te9_3_3.len)) (derElement 4 (memBytes Me (((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))) + BitVec.ofNat 32 (te9_3_3.header + te9_3_3.len)) (((((((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) - BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) - BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) - BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))) - BitVec.ofNat 32 (te9_3_3.header + te9_3_3.len)).toNat)) = .ok (vp20_3_3, vl20_3_3) ∧ ∃ te20_3_3, derElement 4 (memBytes Me (((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) + BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))) + BitVec.ofNat 32 (te9_3_3.header + te9_3_3.len)) (((((((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) - BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) - BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) - BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))) - BitVec.ofNat 32 (te9_3_3.header + te9_3_3.len)).toNat) = .ok te20_3_3 ∧ ∃ sr25_3_3 ss25_3_3, ecdsaSigOf 48 Me (vp20_3_3) ((vl20_3_3).toNat) = .ok (sr25_3_3, ss25_3_3) ∧ ((((((((BitVec.ofNat 32 tl13_6_1_3.len) - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) - BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) - BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) - BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))) - BitVec.ofNat 32 (te9_3_3.header + te9_3_3.len)) - BitVec.ofNat 32 (te20_3_3.header + te20_3_3.len) = 0) ∧
      ∃ tl9_1_4_3, derElement 0x30 (memBytes Me (vp23_4_1_3) (vl23_4_1_3).toNat) = .ok tl9_1_4_3 ∧
      ((vl23_4_1_3) - BitVec.ofNat 32 (tl9_1_4_3.header + tl9_1_4_3.len) = 0) ∧
      derIntIsOf Me (memBytes Me ((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) (BitVec.ofNat 32 tl9_1_4_3.len).toNat) ((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) (derElement 2 (memBytes Me ((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) (BitVec.ofNat 32 tl9_1_4_3.len).toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = .ok true ∧
      ∃ te20_1_4_3, derElement 2 (memBytes Me ((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) (BitVec.ofNat 32 tl9_1_4_3.len).toNat) = .ok te20_1_4_3 ∧
      ∃ op26_1_4_3 ol26_1_4_3, derContent (((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) (derOid (memBytes Me (((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) ((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)).toNat)) = .ok (op26_1_4_3, ol26_1_4_3) ∧
      ∃ to26_1_4_3, derOid (memBytes Me (((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) ((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)).toNat) = .ok to26_1_4_3 ∧
      ∃ tl30_1_4_3, derElement 0x30 (memBytes Me ((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) (((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) - BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)).toNat) = .ok tl30_1_4_3 ∧
      isSha256Of Me (((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 tl30_1_4_3.header) (BitVec.ofNat 32 tl30_1_4_3.len).toNat = .ok true ∧
      ∃ te39_1_4_3, derElement 0x30 (memBytes Me (((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 tl30_1_4_3.header) (BitVec.ofNat 32 tl30_1_4_3.len).toNat) = .ok te39_1_4_3 ∧
      ∃ vp45_1_4_3 vl45_1_4_3, derContent ((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 tl30_1_4_3.header) + BitVec.ofNat 32 (te39_1_4_3.header + te39_1_4_3.len)) (derElement 4 (memBytes Me ((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 tl30_1_4_3.header) + BitVec.ofNat 32 (te39_1_4_3.header + te39_1_4_3.len)) ((BitVec.ofNat 32 tl30_1_4_3.len) - BitVec.ofNat 32 (te39_1_4_3.header + te39_1_4_3.len)).toNat)) = .ok (vp45_1_4_3, vl45_1_4_3) ∧
      ∃ te45_1_4_3, derElement 4 (memBytes Me ((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 tl30_1_4_3.header) + BitVec.ofNat 32 (te39_1_4_3.header + te39_1_4_3.len)) ((BitVec.ofNat 32 tl30_1_4_3.len) - BitVec.ofNat 32 (te39_1_4_3.header + te39_1_4_3.len)).toNat) = .ok te45_1_4_3 ∧
      (vl45_1_4_3 = 32) ∧
      (((BitVec.ofNat 32 tl30_1_4_3.len) - BitVec.ofNat 32 (te39_1_4_3.header + te39_1_4_3.len)) - BitVec.ofNat 32 (te45_1_4_3.header + te45_1_4_3.len) = 0) ∧
      ∃ tl2_2_4_3, derElement 2 (memBytes Me ((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) (((((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) - BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) - BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))).toNat) = .ok tl2_2_4_3 ∧
      ∃ ip2_2_4_3 il2_2_4_3, derPosIntOf (memBytes Me ((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) (((((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) - BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) - BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))).toNat) ((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) (.ok tl2_2_4_3) = .ok (ip2_2_4_3, il2_2_4_3) ∧
      (((il2_2_4_3) - (aluEval .sltu ((Me (ip2_2_4_3)).zeroExtend 32) 1)).toNat ≤ 20) ∧
      ∃ tl13_2_4_3, derElement 0x18 (memBytes Me (((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) ((((((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) - BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) - BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)).toNat) = .ok tl13_2_4_3 ∧
      ∃ tm18_2_4_3, generalizedTime (memBytes Me ((((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 tl13_2_4_3.header) ((BitVec.ofNat 32 tl13_2_4_3.len).toNat)) = some tm18_2_4_3 ∧
      ∃ tt3_w264_3_4_3 : Word, ∃ tt3_w268_3_4_3 : Word, (((derOptRes 0x30 (memBytes Me (((((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) ((((((((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) - BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) - BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))).toNat) = none) ∧ tt3_w264_3_4_3 = ((((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len)) ∧ tt3_w268_3_4_3 = (((((((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) - BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) - BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) ∨ ((¬ (derOptRes 0x30 (memBytes Me (((((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) ((((((((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) - BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) - BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))).toNat) = none)) ∧ ∃ tl2, derOptRes 0x30 (memBytes Me (((((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) ((((((((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) - BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) - BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))).toNat) = some (.ok tl2) ∧ tt3_w264_3_4_3 = (((((((((vp23_4_1_3) + BitVec.ofNat 32 tl9_1_4_3.header) + BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) + BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) + BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) + BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) + BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tt3_w268_3_4_3 = ((((((((BitVec.ofNat 32 tl9_1_4_3.len) - BitVec.ofNat 32 (te20_1_4_3.header + te20_1_4_3.len)) - BitVec.ofNat 32 (to26_1_4_3.header + to26_1_4_3.len)) - BitVec.ofNat 32 (tl30_1_4_3.header + tl30_1_4_3.len))) - BitVec.ofNat 32 (tl2_2_4_3.header + tl2_2_4_3.len)) - BitVec.ofNat 32 (tl13_2_4_3.header + tl13_2_4_3.len))) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tt3_w264_3_4_3 tt3_w268_3_4_3.toNat ∧
      ∃ tt4_w264_4_4_3 : Word, ∃ tt4_w268_4_4_3 : Word, (((tt3_w268_3_4_3 = 0) ∧ tt4_w264_4_4_3 = tt3_w264_3_4_3 ∧ tt4_w268_4_4_3 = tt3_w268_3_4_3) ∨ ((¬ (tt3_w268_3_4_3 = 0)) ∧ (Me tt3_w264_3_4_3 = BitVec.ofNat 8 1) ∧ derBoolOf (memBytes Me (tt3_w264_3_4_3) (tt3_w268_3_4_3).toNat) (derElement 1 (memBytes Me (tt3_w264_3_4_3) (tt3_w268_3_4_3).toNat)) = .ok () ∧ ∃ tb8_1, derElement 1 (memBytes Me (tt3_w264_3_4_3) (tt3_w268_3_4_3).toNat) = .ok tb8_1 ∧ ∃ tt4b_w264_2 : Word, ∃ tt4b_w268_2 : Word, (((((tt3_w268_3_4_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = 0) ∧ tt4b_w264_2 = ((tt3_w264_3_4_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) ∧ tt4b_w268_2 = ((tt3_w268_3_4_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) ∨ ((¬ (((tt3_w268_3_4_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = 0)) ∧ ∃ tt4n_w264_2 : Word, ∃ tt4n_w268_2 : Word, (((Me ((tt3_w264_3_4_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = BitVec.ofNat 8 2) ∧ ∃ ip4 il4, derIntOf (memBytes Me (((tt3_w264_3_4_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (((tt3_w268_3_4_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))).toNat) (((tt3_w264_3_4_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (derElement 2 (memBytes Me (((tt3_w264_3_4_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (((tt3_w268_3_4_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))).toNat)) = .ok (ip4, il4) ∧ ∃ ti4, derElement 2 (memBytes Me (((tt3_w264_3_4_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (((tt3_w268_3_4_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))).toNat) = .ok ti4 ∧ tt4n_w264_2 = (((tt3_w264_3_4_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) + BitVec.ofNat 32 (ti4.header + ti4.len) ∧ tt4n_w268_2 = (((tt3_w268_3_4_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) - BitVec.ofNat 32 (ti4.header + ti4.len)) ∨ ((¬ (Me ((tt3_w264_3_4_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = BitVec.ofNat 8 2)) ∧ tt4n_w264_2 = ((tt3_w264_3_4_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) ∧ tt4n_w268_2 = ((tt3_w268_3_4_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len)))) ∧ SvIn B tt4n_w264_2 tt4n_w268_2.toNat ∧ tt4b_w264_2 = tt4n_w264_2 ∧ tt4b_w268_2 = tt4n_w268_2)) ∧ SvIn B tt4b_w264_2 tt4b_w268_2.toNat ∧ tt4_w264_4_4_3 = tt4b_w264_2 ∧ tt4_w268_4_4_3 = tt4b_w268_2) ∨ ((¬ (tt3_w268_3_4_3 = 0)) ∧ (¬ (Me tt3_w264_3_4_3 = BitVec.ofNat 8 1)) ∧ ∃ tt4n_w264_2 : Word, ∃ tt4n_w268_2 : Word, (((Me tt3_w264_3_4_3 = BitVec.ofNat 8 2) ∧ ∃ ip4 il4, derIntOf (memBytes Me (tt3_w264_3_4_3) (tt3_w268_3_4_3).toNat) (tt3_w264_3_4_3) (derElement 2 (memBytes Me (tt3_w264_3_4_3) (tt3_w268_3_4_3).toNat)) = .ok (ip4, il4) ∧ ∃ ti4, derElement 2 (memBytes Me (tt3_w264_3_4_3) (tt3_w268_3_4_3).toNat) = .ok ti4 ∧ tt4n_w264_2 = (tt3_w264_3_4_3) + BitVec.ofNat 32 (ti4.header + ti4.len) ∧ tt4n_w268_2 = (tt3_w268_3_4_3) - BitVec.ofNat 32 (ti4.header + ti4.len)) ∨ ((¬ (Me tt3_w264_3_4_3 = BitVec.ofNat 8 2)) ∧ tt4n_w264_2 = tt3_w264_3_4_3 ∧ tt4n_w268_2 = tt3_w268_3_4_3)) ∧ SvIn B tt4n_w264_2 tt4n_w268_2.toNat ∧ tt4_w264_4_4_3 = tt4n_w264_2 ∧ tt4_w268_4_4_3 = tt4n_w268_2)) ∧ SvIn B tt4_w264_4_4_3 tt4_w268_4_4_3.toNat ∧
      ∃ tt5_w264_5_4_3 : Word, ∃ tt5_w268_5_4_3 : Word, (((derOptRes 0xA0 (memBytes Me (tt4_w264_4_4_3) (tt4_w268_4_4_3).toNat) = none) ∧ tt5_w264_5_4_3 = tt4_w264_4_4_3 ∧ tt5_w268_5_4_3 = tt4_w268_4_4_3) ∨ ((¬ (derOptRes 0xA0 (memBytes Me (tt4_w264_4_4_3) (tt4_w268_4_4_3).toNat) = none)) ∧ ∃ tl2, derOptRes 0xA0 (memBytes Me (tt4_w264_4_4_3) (tt4_w268_4_4_3).toNat) = some (.ok tl2) ∧ tt5_w264_5_4_3 = (tt4_w264_4_4_3) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tt5_w268_5_4_3 = (tt4_w268_4_4_3) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tt5_w264_5_4_3 tt5_w268_5_4_3.toNat ∧
      ∃ tt6_w264_6_4_3 : Word, ∃ tt6_w268_6_4_3 : Word, (((derOptRes 0xA1 (memBytes Me (tt5_w264_5_4_3) (tt5_w268_5_4_3).toNat) = none) ∧ (tt5_w268_5_4_3 = 0) ∧ tt6_w264_6_4_3 = tt5_w264_5_4_3 ∧ tt6_w268_6_4_3 = tt5_w268_5_4_3) ∨ ((¬ (derOptRes 0xA1 (memBytes Me (tt5_w264_5_4_3) (tt5_w268_5_4_3).toNat) = none)) ∧ ∃ tl2, derOptRes 0xA1 (memBytes Me (tt5_w264_5_4_3) (tt5_w268_5_4_3).toNat) = some (.ok tl2) ∧ ((tt5_w268_5_4_3) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0) ∧ tt6_w264_6_4_3 = (tt5_w264_5_4_3) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tt6_w268_6_4_3 = (tt5_w268_5_4_3) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tt6_w264_6_4_3 tt6_w268_6_4_3.toNat ∧
      ∃ k_6_3, k_6_3 < 8 ∧
      (∀ i, i < k_6_3 → ∀ c'_6_3 q'_6_3, (c'_6_3, q'_6_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (((reg n a2)) + BitVec.ofNat 32 0x308)) → ¬ (memBytes Me (memLoad32 Me (q'_6_3 + 0x20)) (memLoad32 Me (q'_6_3 + 0x24)).toNat = memBytes Me ((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) (BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)).toNat)) ∧
      ∃ c'_6_3 q'_6_3, (c'_6_3, q'_6_3) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) k_6_3 ((BitVec.ofNat 32 0x100), (((reg n a2)) + BitVec.ofNat 32 0x308)) ∧ (memBytes Me (memLoad32 Me (q'_6_3 + 0x20)) (memLoad32 Me (q'_6_3 + 0x24)).toNat = memBytes Me ((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) (BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)).toNat) ∧
      ((memLoad32 Me (q'_6_3 + 0x20)) ≠ 0) ∧
      (sha256 (memBytes Me (vp23_4_1_3) (vl23_4_1_3).toNat) = memBytes Me dg'_3_3 32) ∧
      (sha256 (memBytes Me ((memLoad32 Me ((reg n a1) + 0x8))) ((memLoad32 Me ((reg n a1) + 0xC))).toNat) = memBytes Me vp45_1_4_3 32) ∧
      ((BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len)) ≠ 0) ∧
      ∃ pv_8_3, SvPvRes Me (memLoad32 Me (((q'_6_3) + BitVec.ofNat 32 0x20) + 0x18)) (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 (sha256 (memBytes Me (BitVec.ofNat 32 (img% svConstCmsAddress + 0x14)) (1) ++ memBytes Me ((((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len))) + BitVec.ofNat 32 0x1) ((((BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len))) + BitVec.ofNat 32 0xFFFFFFFF).toNat))) (B + 0x21A0 + BitVec.ofNat 32 0x190) (B + 0x21A0 + BitVec.ofNat 32 0x1C0) sr25_3_3 ss25_3_3 (some pv_8_3) ∧
      (pv_8_3 ≠ 0) ∧
      ∃ ix8_1_1_4, nlScan Me ((memLoad32 Me ((reg n a1) + 0x18))) 0 (((memLoad32 Me ((reg n a1) + 0x1C))).toNat) = some ix8_1_1_4 ∧
      ∃ ix18_1_1_4, nlScan Me (((memLoad32 Me ((reg n a1) + 0x18))) + BitVec.ofNat 32 (ix8_1_1_4 + 1)) 0 ((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix8_1_1_4 + 1)) = some ix18_1_1_4 ∧
      ∃ ix26_1_1_4, nlScan Me ((((memLoad32 Me ((reg n a1) + 0x18))) + BitVec.ofNat 32 (ix8_1_1_4 + 1)) + BitVec.ofNat 32 (ix18_1_1_4 + 1)) 0 (((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) = some ix26_1_1_4 ∧
      ∃ ix34_1_1_4, nlScan Me (((((memLoad32 Me ((reg n a1) + 0x18))) + BitVec.ofNat 32 (ix8_1_1_4 + 1)) + BitVec.ofNat 32 (ix18_1_1_4 + 1)) + BitVec.ofNat 32 (ix26_1_1_4 + 1)) 0 ((((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1)) = some ix34_1_1_4 ∧
      (BitVec.ofNat 32 ix34_1_1_4 = 0) ∧
      (BitVec.ofNat 32 ((((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1)) - BitVec.ofNat 32 (ix34_1_1_4 + 1) ≠ 0) ∧
      (((1 < (BitVec.ofNat 32 ix18_1_1_4).toNat) ∧ ((BitVec.ofNat 32 ((((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1)) - BitVec.ofNat 32 (ix34_1_1_4 + 1)).toNat < (memLoad32 Me ((reg n a1) + 0x1C)).toNat) ∧ (¬ ((memLoad32 Me ((reg n a1) + 0x1C))).toNat < ((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1)) - BitVec.ofNat 32 (ix34_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 Me ((reg n a1) + 0x1C)))).toNat) ∧ (¬ (((BitVec.ofNat 32 ix18_1_1_4)) + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat) ∧ (Me (((memLoad32 Me ((reg n a1) + 0x18))) + BitVec.ofNat 32 (ix8_1_1_4 + 1)) ≠ 0x30)) ∨ ((¬ (1 < (BitVec.ofNat 32 ix18_1_1_4).toNat)) ∧ ((BitVec.ofNat 32 ((((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1)) - BitVec.ofNat 32 (ix34_1_1_4 + 1)).toNat < (memLoad32 Me ((reg n a1) + 0x1C)).toNat) ∧ (¬ ((memLoad32 Me ((reg n a1) + 0x1C))).toNat < ((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1)) - BitVec.ofNat 32 (ix34_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 Me ((reg n a1) + 0x1C)))).toNat) ∧ (¬ (((BitVec.ofNat 32 ix18_1_1_4)) + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat))) ∧
      ∃ c'_2_4 p'_2_4 w64'_2_4 w74'_2_4, (c'_2_4, p'_2_4, w64'_2_4, w74'_2_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, ((((Me ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((Me ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))))) (BitVec.ofNat 32 ix18_1_1_4).toNat ((BitVec.ofNat 32 ix18_1_1_4), (((memLoad32 Me ((reg n a1) + 0x18))) + BitVec.ofNat 32 (ix8_1_1_4 + 1)), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 0x0)) ∧ (∀ i, i < (BitVec.ofNat 32 ix18_1_1_4).toNat → ∀ c'_2_4 p'_2_4 w64'_2_4 w74'_2_4, (c'_2_4, p'_2_4, w64'_2_4, w74'_2_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFFF, ((s.2.1)) + BitVec.ofNat 32 0x1, ((((Me ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA)), ((aluEval .mul ((s.2.2.2)) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu ((s.2.2.1)) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((Me ((s.2.1))).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))) (aluEval .mul ((s.2.2.1)) (BitVec.ofNat 32 0xA))))) i ((BitVec.ofNat 32 ix18_1_1_4), (((memLoad32 Me ((reg n a1) + 0x18))) + BitVec.ofNat 32 (ix8_1_1_4 + 1)), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 0x0)) → ((((((Me (p'_2_4)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF).toNat < (BitVec.ofNat 32 0xA).toNat)) ∧ (((aluEval .sltu ((aluEval .mul (w74'_2_4) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64'_2_4) (BitVec.ofNat 32 0xA))) (aluEval .mulhu (w64'_2_4) (BitVec.ofNat 32 0xA))) ||| (aluEval .sltu (BitVec.ofNat 32 0x0) (aluEval .mulhu (w74'_2_4) (BitVec.ofNat 32 0xA))) = 0)) ∧ (((aluEval .sltu (((((Me (p'_2_4)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64'_2_4) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64'_2_4) (BitVec.ofNat 32 0xA))) &&& (aluEval .sltu (((aluEval .mul (w74'_2_4) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64'_2_4) (BitVec.ofNat 32 0xA))) + (aluEval .sltu (((((Me (p'_2_4)).zeroExtend 32) + BitVec.ofNat 32 0xFFFFFFD0) &&& BitVec.ofNat 32 0xFF) + (aluEval .mul (w64'_2_4) (BitVec.ofNat 32 0xA))) (aluEval .mul (w64'_2_4) (BitVec.ofNat 32 0xA)))) ((aluEval .mul (w74'_2_4) (BitVec.ofNat 32 0xA)) + (aluEval .mulhu (w64'_2_4) (BitVec.ofNat 32 0xA)))) = 0))) ∧
      (w74'_2_4.toNat < 2 ^ 31) ∧ ∃ bs7_2_4, base64Decode (memBytes Me (((((memLoad32 Me ((reg n a1) + 0x18))) + BitVec.ofNat 32 (ix8_1_1_4 + 1)) + BitVec.ofNat 32 (ix18_1_1_4 + 1))) (((BitVec.ofNat 32 ix26_1_1_4)).toNat)) = some bs7_2_4 ∧ (bs7_2_4.length = 32) ∧
      ∃ k_3_4, k_3_4 < 16 ∧
      (∀ i, i < k_3_4 → ∀ c'_3_4 q'_3_4, (c'_3_4, q'_3_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x200), (((reg n a2)) + BitVec.ofNat 32 0x108)) → ¬ (memBytes Me (memLoad32 Me (q'_3_4 + 0x20)) (memLoad32 Me (q'_3_4 + 0x24)).toNat = memBytes Me (memLoad32 Me ((reg n a1) + 0x18)) (BitVec.ofNat 32 ix8_1_1_4).toNat)) ∧
      ∃ c'_3_4 q'_3_4, (c'_3_4, q'_3_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) k_3_4 ((BitVec.ofNat 32 0x200), (((reg n a2)) + BitVec.ofNat 32 0x108)) ∧ (memBytes Me (memLoad32 Me (q'_3_4 + 0x20)) (memLoad32 Me (q'_3_4 + 0x24)).toNat = memBytes Me (memLoad32 Me ((reg n a1) + 0x18)) (BitVec.ofNat 32 ix8_1_1_4).toNat) ∧
      ((memLoad32 Me (q'_3_4 + 0x20)) ≠ 0) ∧
      ∃ sg_5_4, ∃ k_5_4 f'_5_4 w38'_5_4 w50'_5_4 sg'_5_4, svChain (sv_cosigStep B (reg n a0) (reg n a1) (reg n a3) (memLoad32 Me (reg n a1 + 4)) ((q'_4_1) + BitVec.ofNat 32 0x20) (memLoad32 Me (q'_3_4 + 0x24)) (le4 (sha256 (memBytes Me ((memLoad32 Me ((reg n a1) + 0x18))) (((BitVec.ofNat 32 ix8_1_1_4)).toNat) ++ memBytes Me (BitVec.ofNat 32 (img% svNewlineAddress)) (1) ++ memBytes Me (BitVec.ofNat 32 (img% merklePrefixAddress)) (1) ++ memBytes Me ((memLoad32 Me (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18))) (32))) 0) (memLoad32 Me ((reg n a1) + 0x18)) (BitVec.ofNat 32 ix8_1_1_4) (memLoad32 Me (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18)) (memLoad32 Me ((reg n a1) + 0x18)) ((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1)) - BitVec.ofNat 32 (ix34_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 Me ((reg n a1) + 0x1C)))) ((fun k => reg n (savedReg k))) Me) k_5_4 ((BitVec.ofNat 32 0x0), ((((((memLoad32 Me ((reg n a1) + 0x18))) + BitVec.ofNat 32 (ix8_1_1_4 + 1)) + BitVec.ofNat 32 (ix18_1_1_4 + 1)) + BitVec.ofNat 32 (ix26_1_1_4 + 1)) + BitVec.ofNat 32 (ix34_1_1_4 + 1)), (BitVec.ofNat 32 ((((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1)) - BitVec.ofNat 32 (ix34_1_1_4 + 1)), sg_5_4) (f'_5_4, w38'_5_4, w50'_5_4, sg'_5_4) ∧
      w50'_5_4 = 0 ∧
      ((f'_5_4) &&& BitVec.ofNat 32 0x1 ≠ 0) ∧ (evSpec (sigMem Me (B + 0x21A0 + BitVec.ofNat 32 0x420) sg'_5_4) (memLoad32 Me (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18)) (B + 0x21A0 + BitVec.ofNat 32 0x420) (memLoad32 Me ((reg n a1) + 0x18)) (((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 Me ((reg n a1) + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1)) - BitVec.ofNat 32 (ix34_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 Me ((reg n a1) + 0x1C))))).toNat = true) ∧
      ((((memLoad32 Me ((reg n a1) + 0x2C)) = w74'_2_4) ∧ (aluEval .sltu ((memLoad32 Me ((reg n a1) + 0x28))) (w64'_2_4) ≠ 0)) ∨ ((¬ ((memLoad32 Me ((reg n a1) + 0x2C)) = w74'_2_4)) ∧ (aluEval .sltu ((memLoad32 Me ((reg n a1) + 0x2C))) (w74'_2_4) ≠ 0))) ∧
      ∃ root6_3_6_4, rootFromInclusion (pair64 ((memLoad32 Me ((reg n a1) + 0x28))) ((memLoad32 Me ((reg n a1) + 0x2C)))) (pair64 (w64'_2_4) (w74'_2_4)) ((sha256 ([] ++ memBytes Me (BitVec.ofNat 32 (img% svRekorLeafAddress)) (0x1) ++ memBytes Me (BitVec.ofNat 32 (img% svRekorPreAddress)) (0x71) ++ base64Encode (memBytes Me ((reg n a3)) (32)) ++ memBytes Me (BitVec.ofNat 32 (img% svRekorMid1Address)) (0x1B) ++ base64Encode (memBytes Me ((memLoad32 Me ((reg n a1) + 0x8))) (((memLoad32 Me ((reg n a1) + 0xC))).toNat)) ++ memBytes Me (BitVec.ofNat 32 (img% svRekorMid2Address)) (0x54) ++ base64Encode (memBytes Me ((memLoad32 Me (reg n a1))) (((memLoad32 Me (reg n a1 + 4))).toNat)) ++ memBytes Me (BitVec.ofNat 32 (img% svRekorPostAddress)) (0x7)))) (memBytes Me ((memLoad32 Me ((reg n a1) + 0x10))) (((memLoad32 Me ((reg n a1) + 0x14))).toNat)) = some root6_3_6_4 ∧
      (b32 root6_3_6_4 = b32 bs7_2_4) ∧
      ((((BitVec.ofNat 32 (tm20_4_1_1 / 2 ^ 32)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((BitVec.ofNat 32 (tm20_4_1_1 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm20_4_1_1 / 2 ^ 32)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((BitVec.ofNat 32 (tm20_4_1_1 / 2 ^ 32))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (BitVec.ofNat 32 (tm28_4_1_1 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm28_4_1_1 % 2 ^ 32))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (BitVec.ofNat 32 (tm28_4_1_1 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm28_4_1_1 / 2 ^ 32))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
      ((((memLoad32 Me (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((memLoad32 Me (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE4))) = 0)) ∨ ((¬ ((memLoad32 Me (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((memLoad32 Me (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFE8))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 Me (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0))) ∧ (aluEval .sltu ((memLoad32 Me (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFEC))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 Me (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0)))) ∧ (aluEval .sltu ((memLoad32 Me (((q'_4_1) + BitVec.ofNat 32 0x20) + 0xFFFFFFF0))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
      ((((memLoad32 Me (((q'_6_3) + BitVec.ofNat 32 0x20) + 0xC)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((memLoad32 Me (((q'_6_3) + BitVec.ofNat 32 0x20) + 0x8))) = 0)) ∨ ((¬ ((memLoad32 Me (((q'_6_3) + BitVec.ofNat 32 0x20) + 0xC)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((memLoad32 Me (((q'_6_3) + BitVec.ofNat 32 0x20) + 0xC))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 Me (((q'_6_3) + BitVec.ofNat 32 0x20) + 0x14))) ∧ (aluEval .sltu ((memLoad32 Me (((q'_6_3) + BitVec.ofNat 32 0x20) + 0x10))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 Me (((q'_6_3) + BitVec.ofNat 32 0x20) + 0x14)))) ∧ (aluEval .sltu ((memLoad32 Me (((q'_6_3) + BitVec.ofNat 32 0x20) + 0x14))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
      ((((memLoad32 Me (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) ((memLoad32 Me (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 3))) = 0)) ∨ ((¬ ((memLoad32 Me (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7)) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)))) ∧ (aluEval .sltu ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) ((memLoad32 Me (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7))) = 0))) ∧
      ((((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 Me (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15))) ∧ (aluEval .sltu ((memLoad32 Me (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 11))) ((BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32))) = 0)) ∨ ((¬ ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) = (memLoad32 Me (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15)))) ∧ (aluEval .sltu ((memLoad32 Me (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15))) ((BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32))) = 0))) ∧
      SvOkRet B (reg n a0) ((fun k => reg n (savedReg k))) n (BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32)) (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) (memLoad32 Me ((reg n a1) + 0x28)) (memLoad32 Me ((reg n a1) + 0x2C))) := by
  have F := sv_frW FW
  obtain ⟨n1, c1, s1, sp1, r18, r19, r21, r20, r26, r22, ra0, ra1, rk⟩ := sv_pro C F s rsp hb sb
  have fM1 : ∀ x, SvR B x → n1.mem x = Me x := fun x hx => by rw [s1.mem]; exact svProMem_out hx
  have hm : ∀ x, SvR B x → n1.mem x = n.mem x := fun x hx => by rw [fM1 x hx, s.mem]
  rcases sv_verify_5c (B := B) (out := reg n a0) (bp := reg n a1) (rootp := reg n a2) (dg := reg n a3) (lp := memLoad32 Me (reg n a1)) (ll := memLoad32 Me (reg n a1 + 4)) (v := (fun k => reg n (savedReg k))) (sl5 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0x94)) (sl7 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0x9C)) (sl9 := memLoad32 (svProMem Me B n (memLoad32 Me (reg n a1)) (memLoad32 Me (reg n a1 + 4))) (B + 0x21A0 + BitVec.ofNat 32 0xA4)) (n0 := n1) FW (E.fr F fM1) (by rw [s1.mem]; exact svProMem_saves) hret hO (by rw [s1.mem]; exact s1) Me fM1 sp1 (ra0.trans (by rw [BitVec.add_assoc]; rfl)) (ra1.trans (by rw [BitVec.add_assoc]; rfl)) r18 r19 r20 r21 r22 r26 (by rw [s1.mem]; exact svProMem_reader.1) (by rw [s1.mem]; exact svProMem_reader.2.1) (by rw [s1.mem]; exact svProMem_reader.2.2.1) (by rw [s1.mem]; exact svProMem_reader.2.2.2) lc_in D0 (by rw [s1.mem]) (by rw [s1.mem]) (by rw [s1.mem]) SD0 H' HE0 RS PE0 pkp_in apk pk_in side he0p_in he0l_in ae0p ae0l e0_in he1p_in he1l_in ae1p ae1l e1_in he2p_in he2l_in ae2p ae2l e2_in he3p_in he3l_in ae3p ae3l e3_in he4p_in he4l_in ae4p ae4l e4_in hsgp_in hsgl_in asgp asgl sg_in PE0' dg_in htsp_in htsl_in atsp atsl ts_in D0' H'' S2 pkp_in' apk' pk_in' side' CK0 ckp_in4 ckl_in4 a_ckp a_ckl ck_in H''' kp_in4 kw_in4 a_kp a_kw kp_in EE0 hiv pk_in'' lid_in lih_in lil_in a_lih a_lil RK0 dgi_in pp_in4 pl_in4 a_pp a_pl pp_in ii2h ai2h ii2l ai2l ii3h ai3h ii3l ai3l it4h at4h it4l at4l it5h at5h it5l at5l hOk with e | e | hx
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
  obtain ⟨tl28_2_1_1, hx⟩ := hx
  obtain ⟨p14, hx⟩ := hx
  obtain ⟨p15, hx⟩ := hx
  obtain ⟨te41_2_1_1, hx⟩ := hx
  obtain ⟨p17, hx⟩ := hx
  obtain ⟨p18, hx⟩ := hx
  obtain ⟨tl1_3_1_1, hx⟩ := hx
  obtain ⟨p20, hx⟩ := hx
  obtain ⟨ip1_3_1_1, hx⟩ := hx
  obtain ⟨il1_3_1_1, hx⟩ := hx
  obtain ⟨p23, hx⟩ := hx
  obtain ⟨p24, hx⟩ := hx
  obtain ⟨tl8_3_1_1, hx⟩ := hx
  obtain ⟨p26, hx⟩ := hx
  obtain ⟨op21_3_1_1, hx⟩ := hx
  obtain ⟨ol21_3_1_1, hx⟩ := hx
  obtain ⟨p29, hx⟩ := hx
  obtain ⟨p30, hx⟩ := hx
  obtain ⟨tl3_4_1_1, hx⟩ := hx
  obtain ⟨p32, hx⟩ := hx
  obtain ⟨tl11_4_1_1, hx⟩ := hx
  obtain ⟨p34, hx⟩ := hx
  obtain ⟨tm20_4_1_1, hx⟩ := hx
  obtain ⟨rs20_4_1_1, hx⟩ := hx
  obtain ⟨p37, hx⟩ := hx
  obtain ⟨tm28_4_1_1, hx⟩ := hx
  obtain ⟨rs28_4_1_1, hx⟩ := hx
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
  obtain ⟨tl24_6_1_1, hx⟩ := hx
  obtain ⟨p69, hx⟩ := hx
  obtain ⟨p70, hx⟩ := hx
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
  obtain ⟨sr40_2_1, hx⟩ := hx
  obtain ⟨ss40_2_1, hx⟩ := hx
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
  obtain ⟨sr43_6_1, hx⟩ := hx
  obtain ⟨ss43_6_1, hx⟩ := hx
  obtain ⟨p123, hx⟩ := hx
  obtain ⟨p124, hx⟩ := hx
  obtain ⟨tl10_1_1_3, hx⟩ := hx
  obtain ⟨p126, hx⟩ := hx
  obtain ⟨p127, hx⟩ := hx
  obtain ⟨tl21_1_1_3, hx⟩ := hx
  obtain ⟨p129, hx⟩ := hx
  obtain ⟨p130, hx⟩ := hx
  obtain ⟨te30_1_1_3, hx⟩ := hx
  obtain ⟨p132, hx⟩ := hx
  obtain ⟨p133, hx⟩ := hx
  obtain ⟨tl2_2_1_3, hx⟩ := hx
  obtain ⟨p135, hx⟩ := hx
  obtain ⟨p136, hx⟩ := hx
  obtain ⟨op13_2_1_3, hx⟩ := hx
  obtain ⟨ol13_2_1_3, hx⟩ := hx
  obtain ⟨p139, hx⟩ := hx
  obtain ⟨to13_2_1_3, hx⟩ := hx
  obtain ⟨p141, hx⟩ := hx
  obtain ⟨p142, hx⟩ := hx
  obtain ⟨tl21_2_1_3, hx⟩ := hx
  obtain ⟨p144, hx⟩ := hx
  obtain ⟨p145, hx⟩ := hx
  obtain ⟨tl32_2_1_3, hx⟩ := hx
  obtain ⟨p147, hx⟩ := hx
  obtain ⟨p148, hx⟩ := hx
  obtain ⟨p149, hx⟩ := hx
  obtain ⟨te43_2_1_3, hx⟩ := hx
  obtain ⟨p151, hx⟩ := hx
  obtain ⟨tl2_3_1_3, hx⟩ := hx
  obtain ⟨p153, hx⟩ := hx
  obtain ⟨p154, hx⟩ := hx
  obtain ⟨te11_3_1_3, hx⟩ := hx
  obtain ⟨p156, hx⟩ := hx
  obtain ⟨p157, hx⟩ := hx
  obtain ⟨tl19_3_1_3, hx⟩ := hx
  obtain ⟨p159, hx⟩ := hx
  obtain ⟨op28_3_1_3, hx⟩ := hx
  obtain ⟨ol28_3_1_3, hx⟩ := hx
  obtain ⟨p162, hx⟩ := hx
  obtain ⟨to28_3_1_3, hx⟩ := hx
  obtain ⟨p164, hx⟩ := hx
  obtain ⟨p165, hx⟩ := hx
  obtain ⟨tl2_4_1_3, hx⟩ := hx
  obtain ⟨p167, hx⟩ := hx
  obtain ⟨p168, hx⟩ := hx
  obtain ⟨vp23_4_1_3, hx⟩ := hx
  obtain ⟨vl23_4_1_3, hx⟩ := hx
  obtain ⟨p171, hx⟩ := hx
  obtain ⟨te23_4_1_3, hx⟩ := hx
  obtain ⟨p173, hx⟩ := hx
  obtain ⟨p174, hx⟩ := hx
  obtain ⟨tr5_w328_5_1_3, hx⟩ := hx
  obtain ⟨tr5_w32c_5_1_3, hx⟩ := hx
  obtain ⟨p177, hx⟩ := hx
  obtain ⟨p178, hx⟩ := hx
  obtain ⟨tl2_6_1_3, hx⟩ := hx
  obtain ⟨p180, hx⟩ := hx
  obtain ⟨p181, hx⟩ := hx
  obtain ⟨tl13_6_1_3, hx⟩ := hx
  obtain ⟨p183, hx⟩ := hx
  obtain ⟨p184, hx⟩ := hx
  obtain ⟨p185, hx⟩ := hx
  obtain ⟨te25_6_1_3, hx⟩ := hx
  obtain ⟨p187, hx⟩ := hx
  obtain ⟨tl31_6_1_3, hx⟩ := hx
  obtain ⟨p189, hx⟩ := hx
  obtain ⟨p190, hx⟩ := hx
  obtain ⟨te39_6_1_3, hx⟩ := hx
  obtain ⟨p192, hx⟩ := hx
  obtain ⟨tl45_6_1_3, hx⟩ := hx
  obtain ⟨p194, hx⟩ := hx
  obtain ⟨p195, hx⟩ := hx
  obtain ⟨p196, hx⟩ := hx
  obtain ⟨tl6_1_2_3, hx⟩ := hx
  obtain ⟨p198, hx⟩ := hx
  obtain ⟨op15_1_2_3, hx⟩ := hx
  obtain ⟨ol15_1_2_3, hx⟩ := hx
  obtain ⟨p201, hx⟩ := hx
  obtain ⟨to15_1_2_3, hx⟩ := hx
  obtain ⟨p203, hx⟩ := hx
  obtain ⟨tl20_1_2_3, hx⟩ := hx
  obtain ⟨p205, hx⟩ := hx
  obtain ⟨p206, hx⟩ := hx
  obtain ⟨p207, hx⟩ := hx
  obtain ⟨trv_w64_2_2_3, hx⟩ := hx
  obtain ⟨trv_w7c_2_2_3, hx⟩ := hx
  obtain ⟨p210, hx⟩ := hx
  obtain ⟨p211, hx⟩ := hx
  obtain ⟨k_3_3, hx⟩ := hx
  obtain ⟨dg'_3_3, hx⟩ := hx
  obtain ⟨flag'_3_3, hx⟩ := hx
  obtain ⟨cp'_3_3, hx⟩ := hx
  obtain ⟨rem'_3_3, hx⟩ := hx
  obtain ⟨p217, hx⟩ := hx
  obtain ⟨p218, hx⟩ := hx
  obtain ⟨p219, hx⟩ := hx
  obtain ⟨p220, hx⟩ := hx
  obtain ⟨op9_3_3, hx⟩ := hx
  obtain ⟨ol9_3_3, hx⟩ := hx
  obtain ⟨p223, hx⟩ := hx
  obtain ⟨te9_3_3, hx⟩ := hx
  obtain ⟨p225, hx⟩ := hx
  obtain ⟨p226, hx⟩ := hx
  obtain ⟨vp20_3_3, hx⟩ := hx
  obtain ⟨vl20_3_3, hx⟩ := hx
  obtain ⟨p229, hx⟩ := hx
  obtain ⟨te20_3_3, hx⟩ := hx
  obtain ⟨p231, hx⟩ := hx
  obtain ⟨sr25_3_3, hx⟩ := hx
  obtain ⟨ss25_3_3, hx⟩ := hx
  obtain ⟨p234, hx⟩ := hx
  obtain ⟨p235, hx⟩ := hx
  obtain ⟨tl9_1_4_3, hx⟩ := hx
  obtain ⟨p237, hx⟩ := hx
  obtain ⟨p238, hx⟩ := hx
  obtain ⟨p239, hx⟩ := hx
  obtain ⟨te20_1_4_3, hx⟩ := hx
  obtain ⟨p241, hx⟩ := hx
  obtain ⟨op26_1_4_3, hx⟩ := hx
  obtain ⟨ol26_1_4_3, hx⟩ := hx
  obtain ⟨p244, hx⟩ := hx
  obtain ⟨to26_1_4_3, hx⟩ := hx
  obtain ⟨p246, hx⟩ := hx
  obtain ⟨tl30_1_4_3, hx⟩ := hx
  obtain ⟨p248, hx⟩ := hx
  obtain ⟨p249, hx⟩ := hx
  obtain ⟨te39_1_4_3, hx⟩ := hx
  obtain ⟨p251, hx⟩ := hx
  obtain ⟨vp45_1_4_3, hx⟩ := hx
  obtain ⟨vl45_1_4_3, hx⟩ := hx
  obtain ⟨p254, hx⟩ := hx
  obtain ⟨te45_1_4_3, hx⟩ := hx
  obtain ⟨p256, hx⟩ := hx
  obtain ⟨p257, hx⟩ := hx
  obtain ⟨p258, hx⟩ := hx
  obtain ⟨tl2_2_4_3, hx⟩ := hx
  obtain ⟨p260, hx⟩ := hx
  obtain ⟨ip2_2_4_3, hx⟩ := hx
  obtain ⟨il2_2_4_3, hx⟩ := hx
  obtain ⟨p263, hx⟩ := hx
  obtain ⟨p264, hx⟩ := hx
  obtain ⟨tl13_2_4_3, hx⟩ := hx
  obtain ⟨p266, hx⟩ := hx
  obtain ⟨tm18_2_4_3, hx⟩ := hx
  obtain ⟨p268, hx⟩ := hx
  obtain ⟨tt3_w264_3_4_3, hx⟩ := hx
  obtain ⟨tt3_w268_3_4_3, hx⟩ := hx
  obtain ⟨p271, hx⟩ := hx
  obtain ⟨p272, hx⟩ := hx
  obtain ⟨tt4_w264_4_4_3, hx⟩ := hx
  obtain ⟨tt4_w268_4_4_3, hx⟩ := hx
  obtain ⟨p275, hx⟩ := hx
  obtain ⟨p276, hx⟩ := hx
  obtain ⟨tt5_w264_5_4_3, hx⟩ := hx
  obtain ⟨tt5_w268_5_4_3, hx⟩ := hx
  obtain ⟨p279, hx⟩ := hx
  obtain ⟨p280, hx⟩ := hx
  obtain ⟨tt6_w264_6_4_3, hx⟩ := hx
  obtain ⟨tt6_w268_6_4_3, hx⟩ := hx
  obtain ⟨p283, hx⟩ := hx
  obtain ⟨p284, hx⟩ := hx
  obtain ⟨k_6_3, hx⟩ := hx
  obtain ⟨p286, hx⟩ := hx
  obtain ⟨p287, hx⟩ := hx
  obtain ⟨c'_6_3, hx⟩ := hx
  obtain ⟨q'_6_3, hx⟩ := hx
  obtain ⟨p290, hx⟩ := hx
  obtain ⟨p291, hx⟩ := hx
  obtain ⟨p292, hx⟩ := hx
  obtain ⟨p293, hx⟩ := hx
  obtain ⟨p294, hx⟩ := hx
  obtain ⟨p295, hx⟩ := hx
  obtain ⟨pv_8_3, hx⟩ := hx
  obtain ⟨p297, hx⟩ := hx
  obtain ⟨p298, hx⟩ := hx
  obtain ⟨ix8_1_1_4, hx⟩ := hx
  obtain ⟨p300, hx⟩ := hx
  obtain ⟨ix18_1_1_4, hx⟩ := hx
  obtain ⟨p302, hx⟩ := hx
  obtain ⟨ix26_1_1_4, hx⟩ := hx
  obtain ⟨p304, hx⟩ := hx
  obtain ⟨ix34_1_1_4, hx⟩ := hx
  obtain ⟨p306, hx⟩ := hx
  obtain ⟨p307, hx⟩ := hx
  obtain ⟨p308, hx⟩ := hx
  obtain ⟨p309, hx⟩ := hx
  obtain ⟨c'_2_4, hx⟩ := hx
  obtain ⟨p'_2_4, hx⟩ := hx
  obtain ⟨w64'_2_4, hx⟩ := hx
  obtain ⟨w74'_2_4, hx⟩ := hx
  obtain ⟨p314, hx⟩ := hx
  obtain ⟨p315, hx⟩ := hx
  obtain ⟨p316, hx⟩ := hx
  obtain ⟨bs7_2_4, hx⟩ := hx
  obtain ⟨p318, hx⟩ := hx
  obtain ⟨p319, hx⟩ := hx
  obtain ⟨k_3_4, hx⟩ := hx
  obtain ⟨p321, hx⟩ := hx
  obtain ⟨p322, hx⟩ := hx
  obtain ⟨c'_3_4, hx⟩ := hx
  obtain ⟨q'_3_4, hx⟩ := hx
  obtain ⟨p325, hx⟩ := hx
  obtain ⟨p326, hx⟩ := hx
  obtain ⟨p327, hx⟩ := hx
  obtain ⟨sg_5_4, hx⟩ := hx
  obtain ⟨k_5_4, hx⟩ := hx
  obtain ⟨f'_5_4, hx⟩ := hx
  obtain ⟨w38'_5_4, hx⟩ := hx
  obtain ⟨w50'_5_4, hx⟩ := hx
  obtain ⟨sg'_5_4, hx⟩ := hx
  obtain ⟨p334, hx⟩ := hx
  obtain ⟨p335, hx⟩ := hx
  obtain ⟨p336, hx⟩ := hx
  obtain ⟨p337, hx⟩ := hx
  obtain ⟨p338, hx⟩ := hx
  obtain ⟨root6_3_6_4, hx⟩ := hx
  obtain ⟨p340, hx⟩ := hx
  obtain ⟨p341, hx⟩ := hx
  obtain ⟨p342, hx⟩ := hx
  obtain ⟨p343, hx⟩ := hx
  obtain ⟨p344, hx⟩ := hx
  obtain ⟨p345, hx⟩ := hx
  obtain ⟨p346, hx⟩ := hx
  obtain ⟨p347, hx⟩ := hx
  obtain ⟨p348, hx⟩ := hx
  obtain ⟨p349, hx⟩ := hx
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
  refine ⟨tl28_2_1_1, ?_⟩
  refine ⟨p14, ?_⟩
  refine ⟨p15, ?_⟩
  refine ⟨te41_2_1_1, ?_⟩
  refine ⟨p17, ?_⟩
  refine ⟨p18, ?_⟩
  refine ⟨tl1_3_1_1, ?_⟩
  refine ⟨p20, ?_⟩
  refine ⟨ip1_3_1_1, ?_⟩
  refine ⟨il1_3_1_1, ?_⟩
  refine ⟨p23, ?_⟩
  refine ⟨p24, ?_⟩
  refine ⟨tl8_3_1_1, ?_⟩
  refine ⟨p26, ?_⟩
  refine ⟨op21_3_1_1, ?_⟩
  refine ⟨ol21_3_1_1, ?_⟩
  refine ⟨p29, ?_⟩
  refine ⟨p30, ?_⟩
  refine ⟨tl3_4_1_1, ?_⟩
  refine ⟨p32, ?_⟩
  refine ⟨tl11_4_1_1, ?_⟩
  refine ⟨p34, ?_⟩
  refine ⟨tm20_4_1_1, ?_⟩
  refine ⟨rs20_4_1_1, ?_⟩
  refine ⟨p37, ?_⟩
  refine ⟨tm28_4_1_1, ?_⟩
  refine ⟨rs28_4_1_1, ?_⟩
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
  refine ⟨tl24_6_1_1, ?_⟩
  refine ⟨p69, ?_⟩
  refine ⟨p70, ?_⟩
  refine ⟨u0_1, ?_⟩
  refine ⟨u1_1, ?_⟩
  refine ⟨u2_1, ?_⟩
  refine ⟨k_2_1, ?_⟩
  refine ⟨f2c'_2_1, ?_⟩
  refine ⟨f30'_2_1, ?_⟩
  refine ⟨rem'_2_1, ?_⟩
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
  refine ⟨cur'_2_1, ?_⟩
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
  refine ⟨sr40_2_1, ?_⟩
  refine ⟨ss40_2_1, ?_⟩
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
  refine ⟨sr43_6_1, ?_⟩
  refine ⟨ss43_6_1, ?_⟩
  refine ⟨p123, ?_⟩
  refine ⟨p124, ?_⟩
  refine ⟨tl10_1_1_3, ?_⟩
  refine ⟨p126, ?_⟩
  refine ⟨p127, ?_⟩
  refine ⟨tl21_1_1_3, ?_⟩
  refine ⟨p129, ?_⟩
  refine ⟨p130, ?_⟩
  refine ⟨te30_1_1_3, ?_⟩
  refine ⟨p132, ?_⟩
  refine ⟨p133, ?_⟩
  refine ⟨tl2_2_1_3, ?_⟩
  refine ⟨p135, ?_⟩
  refine ⟨p136, ?_⟩
  refine ⟨op13_2_1_3, ?_⟩
  refine ⟨ol13_2_1_3, ?_⟩
  refine ⟨p139, ?_⟩
  refine ⟨to13_2_1_3, ?_⟩
  refine ⟨p141, ?_⟩
  refine ⟨p142, ?_⟩
  refine ⟨tl21_2_1_3, ?_⟩
  refine ⟨p144, ?_⟩
  refine ⟨p145, ?_⟩
  refine ⟨tl32_2_1_3, ?_⟩
  refine ⟨p147, ?_⟩
  refine ⟨p148, ?_⟩
  refine ⟨p149, ?_⟩
  refine ⟨te43_2_1_3, ?_⟩
  refine ⟨p151, ?_⟩
  refine ⟨tl2_3_1_3, ?_⟩
  refine ⟨p153, ?_⟩
  refine ⟨p154, ?_⟩
  refine ⟨te11_3_1_3, ?_⟩
  refine ⟨p156, ?_⟩
  refine ⟨p157, ?_⟩
  refine ⟨tl19_3_1_3, ?_⟩
  refine ⟨p159, ?_⟩
  refine ⟨op28_3_1_3, ?_⟩
  refine ⟨ol28_3_1_3, ?_⟩
  refine ⟨p162, ?_⟩
  refine ⟨to28_3_1_3, ?_⟩
  refine ⟨p164, ?_⟩
  refine ⟨p165, ?_⟩
  refine ⟨tl2_4_1_3, ?_⟩
  refine ⟨p167, ?_⟩
  refine ⟨p168, ?_⟩
  refine ⟨vp23_4_1_3, ?_⟩
  refine ⟨vl23_4_1_3, ?_⟩
  refine ⟨p171, ?_⟩
  refine ⟨te23_4_1_3, ?_⟩
  refine ⟨p173, ?_⟩
  refine ⟨p174, ?_⟩
  refine ⟨tr5_w328_5_1_3, ?_⟩
  refine ⟨tr5_w32c_5_1_3, ?_⟩
  refine ⟨p177, ?_⟩
  refine ⟨p178, ?_⟩
  refine ⟨tl2_6_1_3, ?_⟩
  refine ⟨p180, ?_⟩
  refine ⟨p181, ?_⟩
  refine ⟨tl13_6_1_3, ?_⟩
  refine ⟨p183, ?_⟩
  refine ⟨p184, ?_⟩
  refine ⟨p185, ?_⟩
  refine ⟨te25_6_1_3, ?_⟩
  refine ⟨p187, ?_⟩
  refine ⟨tl31_6_1_3, ?_⟩
  refine ⟨p189, ?_⟩
  refine ⟨p190, ?_⟩
  refine ⟨te39_6_1_3, ?_⟩
  refine ⟨p192, ?_⟩
  refine ⟨tl45_6_1_3, ?_⟩
  refine ⟨p194, ?_⟩
  refine ⟨p195, ?_⟩
  refine ⟨p196, ?_⟩
  refine ⟨tl6_1_2_3, ?_⟩
  refine ⟨p198, ?_⟩
  refine ⟨op15_1_2_3, ?_⟩
  refine ⟨ol15_1_2_3, ?_⟩
  refine ⟨p201, ?_⟩
  refine ⟨to15_1_2_3, ?_⟩
  refine ⟨p203, ?_⟩
  refine ⟨tl20_1_2_3, ?_⟩
  refine ⟨p205, ?_⟩
  refine ⟨p206, ?_⟩
  refine ⟨p207, ?_⟩
  refine ⟨trv_w64_2_2_3, ?_⟩
  refine ⟨trv_w7c_2_2_3, ?_⟩
  refine ⟨p210, ?_⟩
  refine ⟨p211, ?_⟩
  refine ⟨k_3_3, ?_⟩
  refine ⟨dg'_3_3, ?_⟩
  refine ⟨flag'_3_3, ?_⟩
  refine ⟨cp'_3_3, ?_⟩
  refine ⟨rem'_3_3, ?_⟩
  refine ⟨p217, ?_⟩
  refine ⟨p218, ?_⟩
  refine ⟨p219, ?_⟩
  refine ⟨p220, ?_⟩
  refine ⟨op9_3_3, ?_⟩
  refine ⟨ol9_3_3, ?_⟩
  refine ⟨p223, ?_⟩
  refine ⟨te9_3_3, ?_⟩
  refine ⟨p225, ?_⟩
  refine ⟨p226, ?_⟩
  refine ⟨vp20_3_3, ?_⟩
  refine ⟨vl20_3_3, ?_⟩
  refine ⟨p229, ?_⟩
  refine ⟨te20_3_3, ?_⟩
  refine ⟨p231, ?_⟩
  refine ⟨sr25_3_3, ?_⟩
  refine ⟨ss25_3_3, ?_⟩
  refine ⟨p234, ?_⟩
  refine ⟨p235, ?_⟩
  refine ⟨tl9_1_4_3, ?_⟩
  refine ⟨p237, ?_⟩
  refine ⟨p238, ?_⟩
  refine ⟨p239, ?_⟩
  refine ⟨te20_1_4_3, ?_⟩
  refine ⟨p241, ?_⟩
  refine ⟨op26_1_4_3, ?_⟩
  refine ⟨ol26_1_4_3, ?_⟩
  refine ⟨p244, ?_⟩
  refine ⟨to26_1_4_3, ?_⟩
  refine ⟨p246, ?_⟩
  refine ⟨tl30_1_4_3, ?_⟩
  refine ⟨p248, ?_⟩
  refine ⟨p249, ?_⟩
  refine ⟨te39_1_4_3, ?_⟩
  refine ⟨p251, ?_⟩
  refine ⟨vp45_1_4_3, ?_⟩
  refine ⟨vl45_1_4_3, ?_⟩
  refine ⟨p254, ?_⟩
  refine ⟨te45_1_4_3, ?_⟩
  refine ⟨p256, ?_⟩
  refine ⟨p257, ?_⟩
  refine ⟨p258, ?_⟩
  refine ⟨tl2_2_4_3, ?_⟩
  refine ⟨p260, ?_⟩
  refine ⟨ip2_2_4_3, ?_⟩
  refine ⟨il2_2_4_3, ?_⟩
  refine ⟨p263, ?_⟩
  refine ⟨p264, ?_⟩
  refine ⟨tl13_2_4_3, ?_⟩
  refine ⟨p266, ?_⟩
  refine ⟨tm18_2_4_3, ?_⟩
  refine ⟨p268, ?_⟩
  refine ⟨tt3_w264_3_4_3, ?_⟩
  refine ⟨tt3_w268_3_4_3, ?_⟩
  refine ⟨p271, ?_⟩
  refine ⟨p272, ?_⟩
  refine ⟨tt4_w264_4_4_3, ?_⟩
  refine ⟨tt4_w268_4_4_3, ?_⟩
  refine ⟨p275, ?_⟩
  refine ⟨p276, ?_⟩
  refine ⟨tt5_w264_5_4_3, ?_⟩
  refine ⟨tt5_w268_5_4_3, ?_⟩
  refine ⟨p279, ?_⟩
  refine ⟨p280, ?_⟩
  refine ⟨tt6_w264_6_4_3, ?_⟩
  refine ⟨tt6_w268_6_4_3, ?_⟩
  refine ⟨p283, ?_⟩
  refine ⟨p284, ?_⟩
  refine ⟨k_6_3, ?_⟩
  refine ⟨p286, ?_⟩
  refine ⟨p287, ?_⟩
  refine ⟨c'_6_3, ?_⟩
  refine ⟨q'_6_3, ?_⟩
  refine ⟨p290, ?_⟩
  refine ⟨p291, ?_⟩
  refine ⟨p292, ?_⟩
  refine ⟨p293, ?_⟩
  refine ⟨p294, ?_⟩
  refine ⟨p295, ?_⟩
  refine ⟨pv_8_3, ?_⟩
  refine ⟨p297, ?_⟩
  refine ⟨p298, ?_⟩
  refine ⟨ix8_1_1_4, ?_⟩
  refine ⟨p300, ?_⟩
  refine ⟨ix18_1_1_4, ?_⟩
  refine ⟨p302, ?_⟩
  refine ⟨ix26_1_1_4, ?_⟩
  refine ⟨p304, ?_⟩
  refine ⟨ix34_1_1_4, ?_⟩
  refine ⟨p306, ?_⟩
  refine ⟨p307, ?_⟩
  refine ⟨p308, ?_⟩
  refine ⟨p309, ?_⟩
  refine ⟨c'_2_4, ?_⟩
  refine ⟨p'_2_4, ?_⟩
  refine ⟨w64'_2_4, ?_⟩
  refine ⟨w74'_2_4, ?_⟩
  refine ⟨p314, ?_⟩
  refine ⟨p315, ?_⟩
  refine ⟨p316, ?_⟩
  refine ⟨bs7_2_4, ?_⟩
  refine ⟨p318, ?_⟩
  refine ⟨p319, ?_⟩
  refine ⟨k_3_4, ?_⟩
  refine ⟨p321, ?_⟩
  refine ⟨p322, ?_⟩
  refine ⟨c'_3_4, ?_⟩
  refine ⟨q'_3_4, ?_⟩
  refine ⟨p325, ?_⟩
  refine ⟨p326, ?_⟩
  refine ⟨p327, ?_⟩
  refine ⟨sg_5_4, ?_⟩
  refine ⟨k_5_4, ?_⟩
  refine ⟨f'_5_4, ?_⟩
  refine ⟨w38'_5_4, ?_⟩
  refine ⟨w50'_5_4, ?_⟩
  refine ⟨sg'_5_4, ?_⟩
  refine ⟨p334, ?_⟩
  refine ⟨p335, ?_⟩
  refine ⟨p336, ?_⟩
  refine ⟨p337, ?_⟩
  refine ⟨p338, ?_⟩
  refine ⟨root6_3_6_4, ?_⟩
  refine ⟨p340, ?_⟩
  refine ⟨p341, ?_⟩
  refine ⟨p342, ?_⟩
  refine ⟨p343, ?_⟩
  refine ⟨p344, ?_⟩
  refine ⟨p345, ?_⟩
  refine ⟨p346, ?_⟩
  refine ⟨p347, ?_⟩
  refine ⟨p348, ?_⟩
  refine ⟨p349, ?_⟩
  exact SvOkRet.pre c1 (rk _ (by decide)) (rk _ (by decide)) hm hx

end C3.RV32.Sv
