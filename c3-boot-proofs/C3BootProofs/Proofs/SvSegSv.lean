import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvSegCert
import C3BootProofs.Proofs.SvP2St
import C3BootProofs.Proofs.SvSegTs
import C3BootProofs.Proofs.SvSegLog

/-!
# `sigstore::verify`: `sigstore::verify` to its successful exit

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.P2v

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **`sigstore::verify` to its successful exit**: from 0x5C to 0x1A9E: the leaf certificate and its issuer, the P-256 check of the artifact's signature, the timestamp, and the transparency log entry. -/
theorem sv_seg_sv {B out bp rootp dg lp ll : Word} {v : Nat → Word} {n0 : Machine} {sl5 : Word} {sl7 : Word} {sl9 : Word}
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
    (at5l : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (rootp + BitVec.ofNat 32 0x308)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x10).toNat % 4 = 0) :
    SvErrRet B out v n0 ∨ PanicIf n0 ∨
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
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0x1A9E (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = BitVec.ofNat 32 0x1E ∧
        reg n' (21 : Fin 32) = (memLoad32 M0 (bp + 0x28)) ∧
        reg n' (22 : Fin 32) = ll ∧
        reg n' (23 : Fin 32) = ((q'_4_1) + BitVec.ofNat 32 0x20) ∧
        reg n' (24 : Fin 32) = (memLoad32 M0 (bp + 0x2C)) ∧
        reg n' (25 : Fin 32) = (memLoad32 M0 (q'_3_4 + 0x24)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = (BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = (BitVec.ofNat 32 (tm28_4_1_1 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = (BitVec.ofNat 32 (tm28_4_1_1 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = (BitVec.ofNat 32 (tm20_4_1_1 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = (BitVec.ofNat 32 (tm20_4_1_1 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ((q'_6_3) + BitVec.ofNat 32 0x20) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 3)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = (memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 7)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x390) = (memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 11)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x394) = (memLoad32 M0 (((((q'_3_4) + BitVec.ofNat 32 0x20)) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 15)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = (memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x1C)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (bs7_2_4.getD 0 0)).zeroExtend 32 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = (memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = (memLoad32 M0 (q'_3_4 + 0x20)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = ((q'_3_4) + BitVec.ofNat 32 0x20) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64'_2_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74'_2_4 ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (bs7_2_4.getD (1 + j) 0)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = (memLoad32 M0 (q'_3_4 + 0x20)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = (memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = (memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x1C)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A0) = w64'_2_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A4) = w74'_2_4 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = ((memLoad32 M0 (q'_3_4 + 0x24))).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (bs7_2_4.getD 0 0)).zeroExtend 32).extractLsb' 0 8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = (memLoad32 M0 (bp + 0xC)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (memLoad32 M0 (bp + 0x8)) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1FC) = BitVec.ofNat 8 (root6_3_6_4.getD 0 0) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 (root6_3_6_4.getD 0 0) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = ((aluEval .xor ((BitVec.ofNat 32 ((((((memLoad32 M0 (bp + 0x1C))).toNat) - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1)) - BitVec.ofNat 32 (ix34_1_1_4 + 1))) (BitVec.ofNat 32 0xFFFFFFFF)) + ((memLoad32 M0 (bp + 0x1C)))) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38'_5_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50'_5_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = (memLoad32 M0 (bp + 0x18)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = (BitVec.ofNat 32 ix8_1_1_4) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = (memLoad32 M0 (bp + 0x18)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18) = (le4 (sha256 (memBytes M0 ((memLoad32 M0 (bp + 0x18))) (((BitVec.ofNat 32 ix8_1_1_4)).toNat) ++ memBytes M0 (BitVec.ofNat 32 (img% svNewlineAddress)) (1) ++ memBytes M0 (BitVec.ofNat 32 (img% merklePrefixAddress)) (1) ++ memBytes M0 ((memLoad32 M0 (((q'_3_4) + BitVec.ofNat 32 0x20) + 0x18))) (32))) 0) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f'_5_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = (f'_5_4) &&& BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl1'_2_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl3'_2_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl5'_2_1 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = BitVec.ofNat 8 ((sr43_6_1).getD 0 0) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (lp + BitVec.ofNat 32 t_1_1_1.header) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 (tl1_2_1_1.header + tl1_2_1_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (((((((lp + BitVec.ofNat 32 t_1_1_1.header)) + BitVec.ofNat 32 tl1_2_1_1.header) + BitVec.ofNat 32 (tl28_2_1_1.header + tl28_2_1_1.len))) + BitVec.ofNat 32 (tl1_3_1_1.header + tl1_3_1_1.len)) + BitVec.ofNat 32 (tl8_3_1_1.header + tl8_3_1_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (BitVec.ofNat 32 (tl3_4_1_1.header + tl3_4_1_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl0'_2_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl2'_2_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl4'_2_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = sl6'_2_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = sl7'_2_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = sl8'_2_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = sl9'_2_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = (BitVec.ofNat 32 (tm20_4_1_1 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = (BitVec.ofNat 32 (tm20_4_1_1 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = (BitVec.ofNat 32 (tm28_4_1_1 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = (BitVec.ofNat 32 (tm28_4_1_1 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = bp35_5_1_1 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = BitVec.ofNat 8 (sr40_2_1.getD 0 0) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = vp23_4_1_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = vl23_4_1_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = ((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = (BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((((((tr5_w328_5_1_3) + BitVec.ofNat 32 tl2_6_1_3.header) + BitVec.ofNat 32 tl13_6_1_3.header) + BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len)) + BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len)) + BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 (tl45_6_1_3.header + tl45_6_1_3.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x188) = (BitVec.ofNat 32 (tm18_2_4_3 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18C) = (BitVec.ofNat 32 (tm18_2_4_3 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F0) = vp45_1_4_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F4) = dg'_3_3 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr25_3_3.getD 0 0) ∧
        SvKeepL B n0.mem n'.mem [(0x80, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8), (0x6C, 0x4), (0x68, 0x4), (0x64, 0x4), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x3E8, 0x8), (0x58, 0x4), (0x54, 0x4), (0x425, 0xB), (0x424, 0x1), (0x80, 0x48), (0x130, 0x4), (0x134, 0x4), (0x138, 0x4), (0x13C, 0x4), (0x138, 0x8), (0x150, 0x4), (0x154, 0x4), (0x158, 0x4), (0x50, 0x4), (0x15C, 0x4), (0x80, 0x4), (0x88, 0x4), (0x90, 0x4), (0x98, 0x4), (0xA0, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x38, 0x4), (0x34, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x1FC, 0x4), (0x200, 0x4), (0x204, 0x4), (0x208, 0x4), (0x204, 0x8), (0x385, 0xB), (0x384, 0x1), (0x84, 0x4), (0x8C, 0x4), (0x94, 0x4), (0x9C, 0x4), (0xA4, 0x4), (0x80, 0x61), (0x170, 0x5F), (0x85, 0x1), (0x86, 0x1), (0x87, 0x1), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xC8, 0x1), (0xC9, 0x5F), (0x84, 0x1), (0xB8, 0x4), (0xBC, 0x4), (0xC0, 0x4), (0xC4, 0x4), (0x128, 0x4), (0x170, 0x30), (0x170, 0x41), (0x291, 0x3F), (0x130, 0x1), (0x131, 0x1F), (0x150, 0x20), (0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x308, 0x8), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1), (0x348, 0x8), (0x420, 0x18), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4), (0x358, 0x8), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x420, 0x1C), (0x400, 0x8), (0x420, 0x61), (0x380, 0x5F), (0x261, 0xB), (0x260, 0x1), (0x400, 0x10), (0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1), (0x191, 0x5F), (0x1F0, 0x4), (0x1F4, 0x4), (0x170, 0x4), (0x174, 0x1), (0x188, 0x4), (0x18C, 0x4), (0x420, 0x20), (0x420, 0x20), (0x420, 0x20), (0x28, 0x4), (0x24, 0x4), (0x420, 0x60), (0x20, 0x4), (0x3E0, 0x1F), (0x1C, 0x4), (0x430, 0x4), (0x434, 0x4), (0x438, 0x4), (0x43C, 0x4), (0x400, 0x20), (0x18, 0x4), (0xC, 0x4), (0x8, 0x4), (0x10, 0x4), (0x4, 0x4), (0x370, 0x3), (0x14, 0x4), (0x1FC, 0x3F), (0x421, 0x3F), (0x420, 0x1), (0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F), (0x3A0, 0x4), (0x3A4, 0x4), (0x45F, 0x1), (0x460, 0x20), (0x480, 0x4), (0x484, 0x4), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x68), (0x420, 0x21), (0x1FD, 0x1F), (0x1FC, 0x1)]) := by
  rcases sv_seg_cert FW E0 V0 hret hO s0 M0 fM g0_2 g0_10 g0_11 g0_18 g0_19 g0_20 g0_21 g0_22 g0_26 w0_360 w0_364 w0_368 w0_36c lc_in D0 w0_94 w0_9c w0_a4 SD0 H' HE0 RS PE0 pkp_in apk pk_in side he0p_in he0l_in ae0p ae0l e0_in he1p_in he1l_in ae1p ae1l e1_in he2p_in he2l_in ae2p ae2l e2_in he3p_in he3l_in ae3p ae3l e3_in he4p_in he4l_in ae4p ae4l e4_in hsgp_in hsgl_in asgp asgl sg_in with e | e | hx1
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
  obtain ⟨tl28_2_1_1, hx1⟩ := hx1
  obtain ⟨x1_7, hx1⟩ := hx1
  obtain ⟨x1_8, hx1⟩ := hx1
  obtain ⟨te41_2_1_1, hx1⟩ := hx1
  obtain ⟨x1_9, hx1⟩ := hx1
  obtain ⟨x1_10, hx1⟩ := hx1
  obtain ⟨tl1_3_1_1, hx1⟩ := hx1
  obtain ⟨x1_11, hx1⟩ := hx1
  obtain ⟨ip1_3_1_1, hx1⟩ := hx1
  obtain ⟨il1_3_1_1, hx1⟩ := hx1
  obtain ⟨x1_12, hx1⟩ := hx1
  obtain ⟨x1_13, hx1⟩ := hx1
  obtain ⟨tl8_3_1_1, hx1⟩ := hx1
  obtain ⟨x1_14, hx1⟩ := hx1
  obtain ⟨op21_3_1_1, hx1⟩ := hx1
  obtain ⟨ol21_3_1_1, hx1⟩ := hx1
  obtain ⟨x1_15, hx1⟩ := hx1
  obtain ⟨x1_16, hx1⟩ := hx1
  obtain ⟨tl3_4_1_1, hx1⟩ := hx1
  obtain ⟨x1_17, hx1⟩ := hx1
  obtain ⟨tl11_4_1_1, hx1⟩ := hx1
  obtain ⟨x1_18, hx1⟩ := hx1
  obtain ⟨tm20_4_1_1, hx1⟩ := hx1
  obtain ⟨rs20_4_1_1, hx1⟩ := hx1
  obtain ⟨x1_19, hx1⟩ := hx1
  obtain ⟨tm28_4_1_1, hx1⟩ := hx1
  obtain ⟨rs28_4_1_1, hx1⟩ := hx1
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
  obtain ⟨tl24_6_1_1, hx1⟩ := hx1
  obtain ⟨x1_37, hx1⟩ := hx1
  obtain ⟨x1_38, hx1⟩ := hx1
  obtain ⟨u0_1, hx1⟩ := hx1
  obtain ⟨u1_1, hx1⟩ := hx1
  obtain ⟨u2_1, hx1⟩ := hx1
  obtain ⟨k_2_1, hx1⟩ := hx1
  obtain ⟨f2c'_2_1, hx1⟩ := hx1
  obtain ⟨f30'_2_1, hx1⟩ := hx1
  obtain ⟨rem'_2_1, hx1⟩ := hx1
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
  obtain ⟨cur'_2_1, hx1⟩ := hx1
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
  obtain ⟨sr40_2_1, hx1⟩ := hx1
  obtain ⟨ss40_2_1, hx1⟩ := hx1
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
  obtain ⟨sr43_6_1, hx1⟩ := hx1
  obtain ⟨ss43_6_1, hx1⟩ := hx1
  obtain ⟨x1_65, hx1⟩ := hx1
  obtain ⟨n1, hx1⟩ := hx1
  obtain ⟨c1, hx1⟩ := hx1
  obtain ⟨fR1, hx1⟩ := hx1
  obtain ⟨s1, hx1⟩ := hx1
  obtain ⟨E1, hx1⟩ := hx1
  obtain ⟨V1, hx1⟩ := hx1
  obtain ⟨r1_3, hx1⟩ := hx1
  obtain ⟨r1_4, hx1⟩ := hx1
  obtain ⟨r1_2, hx1⟩ := hx1
  obtain ⟨r1_18, hx1⟩ := hx1
  obtain ⟨r1_19, hx1⟩ := hx1
  obtain ⟨r1_20, hx1⟩ := hx1
  obtain ⟨r1_21, hx1⟩ := hx1
  obtain ⟨r1_22, hx1⟩ := hx1
  obtain ⟨r1_23, hx1⟩ := hx1
  obtain ⟨r1_24, hx1⟩ := hx1
  obtain ⟨r1_26, hx1⟩ := hx1
  obtain ⟨w1_30, hx1⟩ := hx1
  obtain ⟨w1_34, hx1⟩ := hx1
  obtain ⟨w1_38, hx1⟩ := hx1
  obtain ⟨w1_3c, hx1⟩ := hx1
  obtain ⟨w1_40, hx1⟩ := hx1
  obtain ⟨w1_44, hx1⟩ := hx1
  obtain ⟨w1_48, hx1⟩ := hx1
  obtain ⟨w1_4c, hx1⟩ := hx1
  obtain ⟨w1_50, hx1⟩ := hx1
  obtain ⟨w1_68, hx1⟩ := hx1
  obtain ⟨w1_70, hx1⟩ := hx1
  obtain ⟨b1_130, hx1⟩ := hx1
  obtain ⟨q1_131, hx1⟩ := hx1
  obtain ⟨q1_150, hx1⟩ := hx1
  obtain ⟨q1_171, hx1⟩ := hx1
  obtain ⟨q1_191, hx1⟩ := hx1
  obtain ⟨q1_291, hx1⟩ := hx1
  obtain ⟨q1_2b0, hx1⟩ := hx1
  obtain ⟨w1_360, hx1⟩ := hx1
  obtain ⟨w1_364, hx1⟩ := hx1
  obtain ⟨w1_368, hx1⟩ := hx1
  obtain ⟨w1_36c, hx1⟩ := hx1
  obtain ⟨w1_80, hx1⟩ := hx1
  obtain ⟨w1_84, hx1⟩ := hx1
  obtain ⟨w1_88, hx1⟩ := hx1
  obtain ⟨w1_8c, hx1⟩ := hx1
  obtain ⟨w1_90, hx1⟩ := hx1
  obtain ⟨w1_98, hx1⟩ := hx1
  obtain ⟨w1_a0, hx1⟩ := hx1
  obtain ⟨w1_370, hx1⟩ := hx1
  obtain ⟨b1_374, hx1⟩ := hx1
  obtain ⟨b1_375, hx1⟩ := hx1
  obtain ⟨b1_376, hx1⟩ := hx1
  obtain ⟨b1_377, hx1⟩ := hx1
  obtain ⟨w1_78, hx1⟩ := hx1
  obtain ⟨w1_7c, hx1⟩ := hx1
  obtain ⟨w1_27c, hx1⟩ := hx1
  obtain ⟨w1_280, hx1⟩ := hx1
  obtain ⟨w1_74, hx1⟩ := hx1
  obtain ⟨w1_54, hx1⟩ := hx1
  obtain ⟨w1_58, hx1⟩ := hx1
  obtain ⟨w1_5c, hx1⟩ := hx1
  obtain ⟨w1_60, hx1⟩ := hx1
  obtain ⟨w1_64, hx1⟩ := hx1
  obtain ⟨w1_6c, hx1⟩ := hx1
  obtain ⟨w1_94, hx1⟩ := hx1
  obtain ⟨w1_9c, hx1⟩ := hx1
  obtain ⟨w1_a4, hx1⟩ := hx1
  obtain ⟨w1_a8, hx1⟩ := hx1
  obtain ⟨w1_ac, hx1⟩ := hx1
  obtain ⟨w1_b0, hx1⟩ := hx1
  obtain ⟨w1_b4, hx1⟩ := hx1
  obtain ⟨w1_b8, hx1⟩ := hx1
  obtain ⟨w1_bc, hx1⟩ := hx1
  obtain ⟨w1_c0, hx1⟩ := hx1
  obtain ⟨w1_c4, hx1⟩ := hx1
  obtain ⟨w1_128, hx1⟩ := hx1
  obtain ⟨b1_c8, hx1⟩ := hx1
  have K1_L := hx1
  rcases sv_p2st FW E1 V1 hret hO s1 M0 fR1 r1_2 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 r1_24 r1_26 b1_130 q1_131 q1_150 PE0' RS (by have h := SvIn.bitsW (((((((((((((lc_in).content x1_0).ofNatLen).content x1_2).ofNatLen).restW (opt_ok_elem x1_7)).restW x1_11).restW x1_14).restW x1_17).restW x1_18).restW x1_22).content x1_23).restN x1_25) x1_29 x1_30; rw [x1_31] at h; exact h) dg_in with e | e | hx2
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  · exact .inr (.inl (PanicIf.of_steps (c1) e))
  obtain ⟨x2_0, hx2⟩ := hx2
  obtain ⟨n2, hx2⟩ := hx2
  obtain ⟨c2, hx2⟩ := hx2
  obtain ⟨s2, hx2⟩ := hx2
  obtain ⟨E2, hx2⟩ := hx2
  obtain ⟨V2, hx2⟩ := hx2
  obtain ⟨fR2, hx2⟩ := hx2
  obtain ⟨r2_2, hx2⟩ := hx2
  obtain ⟨r2_3, hx2⟩ := hx2
  obtain ⟨r2_4, hx2⟩ := hx2
  obtain ⟨r2_18, hx2⟩ := hx2
  obtain ⟨r2_19, hx2⟩ := hx2
  obtain ⟨r2_20, hx2⟩ := hx2
  obtain ⟨r2_21, hx2⟩ := hx2
  obtain ⟨r2_22, hx2⟩ := hx2
  obtain ⟨r2_23, hx2⟩ := hx2
  obtain ⟨r2_24, hx2⟩ := hx2
  obtain ⟨r2_26, hx2⟩ := hx2
  have K2_L := hx2
  rcases sv_seg_ts FW E2 V2 hret hO s2 M0 fR2 r2_2 r2_18 r2_19 r2_20 r2_21 r2_22 r2_23 r2_24 rfl r2_26 rfl rfl rfl htsp_in htsl_in atsp atsl ts_in D0' (fun i hi c'_6_3 q'_6_3 h => ⟨(H'' i hi c'_6_3 q'_6_3 h).1, (H'' i hi c'_6_3 q'_6_3 h).2.1, (H'' i hi c'_6_3 q'_6_3 h).2.2.1, (H'' i hi c'_6_3 q'_6_3 h).2.2.2.1, (H'' i hi c'_6_3 q'_6_3 h).2.2.2.2⟩) ((K2_L.w32 (by decide) (by decide)).trans w1_68) ((K2_L.w32 (by decide) (by decide)).trans w1_70) S2 RS (sg_in) PE0 pkp_in' apk' pk_in' side' with e | e | hx3
  · exact .inl (SvErrRet.pre (c1.trans (c2)) (by rw [r2_3, r1_3]) (by rw [r2_4, r1_4])
      (fun x hx => (fR2 x hx).trans (fM x hx).symm) e)
  · exact .inr (.inl (PanicIf.of_steps (c1.trans (c2)) e))
  obtain ⟨tl10_1_1_3, hx3⟩ := hx3
  obtain ⟨x3_0, hx3⟩ := hx3
  obtain ⟨x3_1, hx3⟩ := hx3
  obtain ⟨tl21_1_1_3, hx3⟩ := hx3
  obtain ⟨x3_2, hx3⟩ := hx3
  obtain ⟨x3_3, hx3⟩ := hx3
  obtain ⟨te30_1_1_3, hx3⟩ := hx3
  obtain ⟨x3_4, hx3⟩ := hx3
  obtain ⟨x3_5, hx3⟩ := hx3
  obtain ⟨tl2_2_1_3, hx3⟩ := hx3
  obtain ⟨x3_6, hx3⟩ := hx3
  obtain ⟨x3_7, hx3⟩ := hx3
  obtain ⟨op13_2_1_3, hx3⟩ := hx3
  obtain ⟨ol13_2_1_3, hx3⟩ := hx3
  obtain ⟨x3_8, hx3⟩ := hx3
  obtain ⟨to13_2_1_3, hx3⟩ := hx3
  obtain ⟨x3_9, hx3⟩ := hx3
  obtain ⟨x3_10, hx3⟩ := hx3
  obtain ⟨tl21_2_1_3, hx3⟩ := hx3
  obtain ⟨x3_11, hx3⟩ := hx3
  obtain ⟨x3_12, hx3⟩ := hx3
  obtain ⟨tl32_2_1_3, hx3⟩ := hx3
  obtain ⟨x3_13, hx3⟩ := hx3
  obtain ⟨x3_14, hx3⟩ := hx3
  obtain ⟨x3_15, hx3⟩ := hx3
  obtain ⟨te43_2_1_3, hx3⟩ := hx3
  obtain ⟨x3_16, hx3⟩ := hx3
  obtain ⟨tl2_3_1_3, hx3⟩ := hx3
  obtain ⟨x3_17, hx3⟩ := hx3
  obtain ⟨x3_18, hx3⟩ := hx3
  obtain ⟨te11_3_1_3, hx3⟩ := hx3
  obtain ⟨x3_19, hx3⟩ := hx3
  obtain ⟨x3_20, hx3⟩ := hx3
  obtain ⟨tl19_3_1_3, hx3⟩ := hx3
  obtain ⟨x3_21, hx3⟩ := hx3
  obtain ⟨op28_3_1_3, hx3⟩ := hx3
  obtain ⟨ol28_3_1_3, hx3⟩ := hx3
  obtain ⟨x3_22, hx3⟩ := hx3
  obtain ⟨to28_3_1_3, hx3⟩ := hx3
  obtain ⟨x3_23, hx3⟩ := hx3
  obtain ⟨x3_24, hx3⟩ := hx3
  obtain ⟨tl2_4_1_3, hx3⟩ := hx3
  obtain ⟨x3_25, hx3⟩ := hx3
  obtain ⟨x3_26, hx3⟩ := hx3
  obtain ⟨vp23_4_1_3, hx3⟩ := hx3
  obtain ⟨vl23_4_1_3, hx3⟩ := hx3
  obtain ⟨x3_27, hx3⟩ := hx3
  obtain ⟨te23_4_1_3, hx3⟩ := hx3
  obtain ⟨x3_28, hx3⟩ := hx3
  obtain ⟨x3_29, hx3⟩ := hx3
  obtain ⟨tr5_w328_5_1_3, hx3⟩ := hx3
  obtain ⟨tr5_w32c_5_1_3, hx3⟩ := hx3
  obtain ⟨x3_30, hx3⟩ := hx3
  obtain ⟨x3_31, hx3⟩ := hx3
  obtain ⟨tl2_6_1_3, hx3⟩ := hx3
  obtain ⟨x3_32, hx3⟩ := hx3
  obtain ⟨x3_33, hx3⟩ := hx3
  obtain ⟨tl13_6_1_3, hx3⟩ := hx3
  obtain ⟨x3_34, hx3⟩ := hx3
  obtain ⟨x3_35, hx3⟩ := hx3
  obtain ⟨x3_36, hx3⟩ := hx3
  obtain ⟨te25_6_1_3, hx3⟩ := hx3
  obtain ⟨x3_37, hx3⟩ := hx3
  obtain ⟨tl31_6_1_3, hx3⟩ := hx3
  obtain ⟨x3_38, hx3⟩ := hx3
  obtain ⟨x3_39, hx3⟩ := hx3
  obtain ⟨te39_6_1_3, hx3⟩ := hx3
  obtain ⟨x3_40, hx3⟩ := hx3
  obtain ⟨tl45_6_1_3, hx3⟩ := hx3
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
  obtain ⟨trv_w64_2_2_3, hx3⟩ := hx3
  obtain ⟨trv_w7c_2_2_3, hx3⟩ := hx3
  obtain ⟨x3_50, hx3⟩ := hx3
  obtain ⟨x3_51, hx3⟩ := hx3
  obtain ⟨k_3_3, hx3⟩ := hx3
  obtain ⟨dg'_3_3, hx3⟩ := hx3
  obtain ⟨flag'_3_3, hx3⟩ := hx3
  obtain ⟨cp'_3_3, hx3⟩ := hx3
  obtain ⟨rem'_3_3, hx3⟩ := hx3
  obtain ⟨x3_52, hx3⟩ := hx3
  obtain ⟨x3_53, hx3⟩ := hx3
  obtain ⟨x3_54, hx3⟩ := hx3
  obtain ⟨x3_55, hx3⟩ := hx3
  obtain ⟨op9_3_3, hx3⟩ := hx3
  obtain ⟨ol9_3_3, hx3⟩ := hx3
  obtain ⟨x3_56, hx3⟩ := hx3
  obtain ⟨te9_3_3, hx3⟩ := hx3
  obtain ⟨x3_57, hx3⟩ := hx3
  obtain ⟨x3_58, hx3⟩ := hx3
  obtain ⟨vp20_3_3, hx3⟩ := hx3
  obtain ⟨vl20_3_3, hx3⟩ := hx3
  obtain ⟨x3_59, hx3⟩ := hx3
  obtain ⟨te20_3_3, hx3⟩ := hx3
  obtain ⟨x3_60, hx3⟩ := hx3
  obtain ⟨sr25_3_3, hx3⟩ := hx3
  obtain ⟨ss25_3_3, hx3⟩ := hx3
  obtain ⟨x3_61, hx3⟩ := hx3
  obtain ⟨x3_62, hx3⟩ := hx3
  obtain ⟨tl9_1_4_3, hx3⟩ := hx3
  obtain ⟨x3_63, hx3⟩ := hx3
  obtain ⟨x3_64, hx3⟩ := hx3
  obtain ⟨x3_65, hx3⟩ := hx3
  obtain ⟨te20_1_4_3, hx3⟩ := hx3
  obtain ⟨x3_66, hx3⟩ := hx3
  obtain ⟨op26_1_4_3, hx3⟩ := hx3
  obtain ⟨ol26_1_4_3, hx3⟩ := hx3
  obtain ⟨x3_67, hx3⟩ := hx3
  obtain ⟨to26_1_4_3, hx3⟩ := hx3
  obtain ⟨x3_68, hx3⟩ := hx3
  obtain ⟨tl30_1_4_3, hx3⟩ := hx3
  obtain ⟨x3_69, hx3⟩ := hx3
  obtain ⟨x3_70, hx3⟩ := hx3
  obtain ⟨te39_1_4_3, hx3⟩ := hx3
  obtain ⟨x3_71, hx3⟩ := hx3
  obtain ⟨vp45_1_4_3, hx3⟩ := hx3
  obtain ⟨vl45_1_4_3, hx3⟩ := hx3
  obtain ⟨x3_72, hx3⟩ := hx3
  obtain ⟨te45_1_4_3, hx3⟩ := hx3
  obtain ⟨x3_73, hx3⟩ := hx3
  obtain ⟨x3_74, hx3⟩ := hx3
  obtain ⟨x3_75, hx3⟩ := hx3
  obtain ⟨tl2_2_4_3, hx3⟩ := hx3
  obtain ⟨x3_76, hx3⟩ := hx3
  obtain ⟨ip2_2_4_3, hx3⟩ := hx3
  obtain ⟨il2_2_4_3, hx3⟩ := hx3
  obtain ⟨x3_77, hx3⟩ := hx3
  obtain ⟨x3_78, hx3⟩ := hx3
  obtain ⟨tl13_2_4_3, hx3⟩ := hx3
  obtain ⟨x3_79, hx3⟩ := hx3
  obtain ⟨tm18_2_4_3, hx3⟩ := hx3
  obtain ⟨x3_80, hx3⟩ := hx3
  obtain ⟨tt3_w264_3_4_3, hx3⟩ := hx3
  obtain ⟨tt3_w268_3_4_3, hx3⟩ := hx3
  obtain ⟨x3_81, hx3⟩ := hx3
  obtain ⟨x3_82, hx3⟩ := hx3
  obtain ⟨tt4_w264_4_4_3, hx3⟩ := hx3
  obtain ⟨tt4_w268_4_4_3, hx3⟩ := hx3
  obtain ⟨x3_83, hx3⟩ := hx3
  obtain ⟨x3_84, hx3⟩ := hx3
  obtain ⟨tt5_w264_5_4_3, hx3⟩ := hx3
  obtain ⟨tt5_w268_5_4_3, hx3⟩ := hx3
  obtain ⟨x3_85, hx3⟩ := hx3
  obtain ⟨x3_86, hx3⟩ := hx3
  obtain ⟨tt6_w264_6_4_3, hx3⟩ := hx3
  obtain ⟨tt6_w268_6_4_3, hx3⟩ := hx3
  obtain ⟨x3_87, hx3⟩ := hx3
  obtain ⟨x3_88, hx3⟩ := hx3
  obtain ⟨k_6_3, hx3⟩ := hx3
  obtain ⟨x3_89, hx3⟩ := hx3
  obtain ⟨x3_90, hx3⟩ := hx3
  obtain ⟨c'_6_3, hx3⟩ := hx3
  obtain ⟨q'_6_3, hx3⟩ := hx3
  obtain ⟨x3_91, hx3⟩ := hx3
  obtain ⟨x3_92, hx3⟩ := hx3
  obtain ⟨x3_93, hx3⟩ := hx3
  obtain ⟨x3_94, hx3⟩ := hx3
  obtain ⟨x3_95, hx3⟩ := hx3
  obtain ⟨x3_96, hx3⟩ := hx3
  obtain ⟨pv_8_3, hx3⟩ := hx3
  obtain ⟨x3_97, hx3⟩ := hx3
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
  obtain ⟨r3_20, hx3⟩ := hx3
  obtain ⟨r3_21, hx3⟩ := hx3
  obtain ⟨r3_22, hx3⟩ := hx3
  obtain ⟨r3_23, hx3⟩ := hx3
  obtain ⟨r3_24, hx3⟩ := hx3
  obtain ⟨r3_25, hx3⟩ := hx3
  obtain ⟨r3_26, hx3⟩ := hx3
  obtain ⟨r3_27, hx3⟩ := hx3
  obtain ⟨w3_44, hx3⟩ := hx3
  obtain ⟨w3_50, hx3⟩ := hx3
  obtain ⟨w3_64, hx3⟩ := hx3
  obtain ⟨w3_7c, hx3⟩ := hx3
  obtain ⟨w3_264, hx3⟩ := hx3
  obtain ⟨w3_268, hx3⟩ := hx3
  obtain ⟨w3_74, hx3⟩ := hx3
  obtain ⟨w3_78, hx3⟩ := hx3
  obtain ⟨w3_48, hx3⟩ := hx3
  obtain ⟨w3_4c, hx3⟩ := hx3
  obtain ⟨w3_3c, hx3⟩ := hx3
  obtain ⟨w3_170, hx3⟩ := hx3
  obtain ⟨w3_174, hx3⟩ := hx3
  obtain ⟨w3_178, hx3⟩ := hx3
  obtain ⟨w3_17c, hx3⟩ := hx3
  obtain ⟨w3_180, hx3⟩ := hx3
  obtain ⟨w3_184, hx3⟩ := hx3
  obtain ⟨w3_188, hx3⟩ := hx3
  obtain ⟨w3_18c, hx3⟩ := hx3
  obtain ⟨w3_1f0, hx3⟩ := hx3
  obtain ⟨w3_1f4, hx3⟩ := hx3
  obtain ⟨b3_190, hx3⟩ := hx3
  obtain ⟨w3_68, hx3⟩ := hx3
  obtain ⟨w3_70, hx3⟩ := hx3
  obtain ⟨w3_380, hx3⟩ := hx3
  obtain ⟨w3_384, hx3⟩ := hx3
  obtain ⟨w3_388, hx3⟩ := hx3
  obtain ⟨w3_38c, hx3⟩ := hx3
  have K3_L := hx3
  rcases sv_seg_log FW E3 V3 hret hO s3 M0 fR3 r3_2 r3_a0 r3_18 r3_19 r3_20 r3_21 r3_22 r3_23 r3_24 r3_25 r3_26 r3_27 CK0 rfl rfl ckp_in4 ckl_in4 a_ckp a_ckl ck_in (fun i hi c'_3_4 q'_3_4 h => ⟨(H''' i hi c'_3_4 q'_3_4 h).1, (H''' i hi c'_3_4 q'_3_4 h).2.1, (H''' i hi c'_3_4 q'_3_4 h).2.2.1, (H''' i hi c'_3_4 q'_3_4 h).2.2.2.1, (H''' i hi c'_3_4 q'_3_4 h).2.2.2.2⟩) S2 RS kp_in4 kw_in4 a_kp a_kw kp_in EE0 hiv pk_in'' w3_68 ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_6c)) w3_70 w3_3c ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_54)) ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_58)) ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_5c)) ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_60)) w3_78 w3_7c lid_in lih_in lil_in a_lih a_lil RK0 dgi_in (sg_in) (lc_in) pp_in4 pl_in4 a_pp a_pl pp_in (ii2h k_4_1 x1_53 c'_4_1 q'_4_1 x1_55 x1_57) (ai2h k_4_1 x1_53 c'_4_1 q'_4_1 x1_55 x1_57) (ii2l k_4_1 x1_53 c'_4_1 q'_4_1 x1_55 x1_57) (ai2l k_4_1 x1_53 c'_4_1 q'_4_1 x1_55 x1_57) (ii3h k_4_1 x1_53 c'_4_1 q'_4_1 x1_55 x1_57) (ai3h k_4_1 x1_53 c'_4_1 q'_4_1 x1_55 x1_57) (ii3l k_4_1 x1_53 c'_4_1 q'_4_1 x1_55 x1_57) (ai3l k_4_1 x1_53 c'_4_1 q'_4_1 x1_55 x1_57) (it4h k_6_3 x3_89 c'_6_3 q'_6_3 x3_91 x3_93) (at4h k_6_3 x3_89 c'_6_3 q'_6_3 x3_91 x3_93) (it4l k_6_3 x3_89 c'_6_3 q'_6_3 x3_91 x3_93) (at4l k_6_3 x3_89 c'_6_3 q'_6_3 x3_91 x3_93) (it5h k_6_3 x3_89 c'_6_3 q'_6_3 x3_91 x3_93) (at5h k_6_3 x3_89 c'_6_3 q'_6_3 x3_91 x3_93) (it5l k_6_3 x3_89 c'_6_3 q'_6_3 x3_91 x3_93) (at5l k_6_3 x3_89 c'_6_3 q'_6_3 x3_91 x3_93) with e | hx4
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3))) (by rw [r3_3, r2_3, r1_3]) (by rw [r3_4, r2_4, r1_4])
      (fun x hx => (fR3 x hx).trans (fM x hx).symm) e)
  obtain ⟨x4_0, hx4⟩ := hx4
  obtain ⟨ix8_1_1_4, hx4⟩ := hx4
  obtain ⟨x4_1, hx4⟩ := hx4
  obtain ⟨ix18_1_1_4, hx4⟩ := hx4
  obtain ⟨x4_2, hx4⟩ := hx4
  obtain ⟨ix26_1_1_4, hx4⟩ := hx4
  obtain ⟨x4_3, hx4⟩ := hx4
  obtain ⟨ix34_1_1_4, hx4⟩ := hx4
  obtain ⟨x4_4, hx4⟩ := hx4
  obtain ⟨x4_5, hx4⟩ := hx4
  obtain ⟨x4_6, hx4⟩ := hx4
  obtain ⟨x4_7, hx4⟩ := hx4
  obtain ⟨c'_2_4, hx4⟩ := hx4
  obtain ⟨p'_2_4, hx4⟩ := hx4
  obtain ⟨w64'_2_4, hx4⟩ := hx4
  obtain ⟨w74'_2_4, hx4⟩ := hx4
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
  obtain ⟨x4_15, hx4⟩ := hx4
  obtain ⟨x4_16, hx4⟩ := hx4
  obtain ⟨x4_17, hx4⟩ := hx4
  obtain ⟨sg_5_4, hx4⟩ := hx4
  obtain ⟨k_5_4, hx4⟩ := hx4
  obtain ⟨f'_5_4, hx4⟩ := hx4
  obtain ⟨w38'_5_4, hx4⟩ := hx4
  obtain ⟨w50'_5_4, hx4⟩ := hx4
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
  obtain ⟨r4_18, hx4⟩ := hx4
  obtain ⟨r4_19, hx4⟩ := hx4
  obtain ⟨r4_20, hx4⟩ := hx4
  obtain ⟨r4_21, hx4⟩ := hx4
  obtain ⟨r4_22, hx4⟩ := hx4
  obtain ⟨r4_23, hx4⟩ := hx4
  obtain ⟨r4_24, hx4⟩ := hx4
  obtain ⟨r4_25, hx4⟩ := hx4
  obtain ⟨w4_3c, hx4⟩ := hx4
  obtain ⟨w4_54, hx4⟩ := hx4
  obtain ⟨w4_58, hx4⟩ := hx4
  obtain ⟨w4_5c, hx4⟩ := hx4
  obtain ⟨w4_60, hx4⟩ := hx4
  obtain ⟨w4_78, hx4⟩ := hx4
  obtain ⟨w4_7c, hx4⟩ := hx4
  obtain ⟨w4_388, hx4⟩ := hx4
  obtain ⟨w4_38c, hx4⟩ := hx4
  obtain ⟨w4_390, hx4⟩ := hx4
  obtain ⟨w4_394, hx4⟩ := hx4
  obtain ⟨w4_1c, hx4⟩ := hx4
  obtain ⟨w4_20, hx4⟩ := hx4
  obtain ⟨w4_34, hx4⟩ := hx4
  obtain ⟨w4_40, hx4⟩ := hx4
  obtain ⟨w4_4c, hx4⟩ := hx4
  obtain ⟨w4_64, hx4⟩ := hx4
  obtain ⟨w4_74, hx4⟩ := hx4
  obtain ⟨q4_3e0, hx4⟩ := hx4
  obtain ⟨w4_380, hx4⟩ := hx4
  obtain ⟨w4_398, hx4⟩ := hx4
  obtain ⟨w4_39c, hx4⟩ := hx4
  obtain ⟨w4_3a0, hx4⟩ := hx4
  obtain ⟨w4_3a4, hx4⟩ := hx4
  obtain ⟨b4_384, hx4⟩ := hx4
  obtain ⟨b4_3a8, hx4⟩ := hx4
  obtain ⟨w4_68, hx4⟩ := hx4
  obtain ⟨w4_6c, hx4⟩ := hx4
  obtain ⟨w4_70, hx4⟩ := hx4
  obtain ⟨b4_1fc, hx4⟩ := hx4
  obtain ⟨b4_420, hx4⟩ := hx4
  obtain ⟨b4_421, hx4⟩ := hx4
  obtain ⟨w4_24, hx4⟩ := hx4
  obtain ⟨w4_38, hx4⟩ := hx4
  obtain ⟨w4_50, hx4⟩ := hx4
  obtain ⟨w4_28, hx4⟩ := hx4
  obtain ⟨w4_44, hx4⟩ := hx4
  obtain ⟨w4_48, hx4⟩ := hx4
  obtain ⟨w4_18, hx4⟩ := hx4
  obtain ⟨w4_30, hx4⟩ := hx4
  obtain ⟨w4_2c, hx4⟩ := hx4
  have K4_L := hx4
  exact .inr (.inr ⟨t_1_1_1, x1_0, x1_1, tl1_2_1_1, x1_2, tl8_2_1_1, x1_3, tl16_2_1_1, x1_4, bp16_2_1_1, bl16_2_1_1, x1_5, x1_6, tl28_2_1_1, x1_7, x1_8, te41_2_1_1, x1_9, x1_10, tl1_3_1_1, x1_11, ip1_3_1_1, il1_3_1_1, x1_12, x1_13, tl8_3_1_1, x1_14, op21_3_1_1, ol21_3_1_1, x1_15, x1_16, tl3_4_1_1, x1_17, tl11_4_1_1, x1_18, tm20_4_1_1, rs20_4_1_1, x1_19, tm28_4_1_1, rs28_4_1_1, x1_20, x1_21, tl2_5_1_1, x1_22, tl6_5_1_1, x1_23, op15_5_1_1, ol15_5_1_1, prp15_5_1_1, pu15_5_1_1, x1_24, ta15_5_1_1, x1_25, x1_26, x1_27, x1_28, tl35_5_1_1, x1_29, bp35_5_1_1, bl35_5_1_1, x1_30, x1_31, x1_32, x1_33, x1_34, tl9_6_1_1, x1_35, x1_36, tl24_6_1_1, x1_37, x1_38, u0_1, u1_1, u2_1, k_2_1, f2c'_2_1, f30'_2_1, rem'_2_1, sl0'_2_1, sl1'_2_1, sl2'_2_1, sl3'_2_1, sl4'_2_1, sl5'_2_1, sl6'_2_1, sl7'_2_1, sl8'_2_1, sl9'_2_1, cur'_2_1, x1_39, x1_40, x1_41, x1_42, x1_43, x1_44, x1_45, x1_46, x1_47, x1_48, x1_49, x1_50, x1_51, sr40_2_1, ss40_2_1, x1_52, k_4_1, x1_53, x1_54, c'_4_1, q'_4_1, x1_55, x1_56, x1_57, pv_5_1, x1_58, x1_59, x1_60, x1_61, x1_62, x1_63, x1_64, sr43_6_1, ss43_6_1, x1_65, x2_0, tl10_1_1_3, x3_0, x3_1, tl21_1_1_3, x3_2, x3_3, te30_1_1_3, x3_4, x3_5, tl2_2_1_3, x3_6, x3_7, op13_2_1_3, ol13_2_1_3, x3_8, to13_2_1_3, x3_9, x3_10, tl21_2_1_3, x3_11, x3_12, tl32_2_1_3, x3_13, x3_14, x3_15, te43_2_1_3, x3_16, tl2_3_1_3, x3_17, x3_18, te11_3_1_3, x3_19, x3_20, tl19_3_1_3, x3_21, op28_3_1_3, ol28_3_1_3, x3_22, to28_3_1_3, x3_23, x3_24, tl2_4_1_3, x3_25, x3_26, vp23_4_1_3, vl23_4_1_3, x3_27, te23_4_1_3, x3_28, x3_29, tr5_w328_5_1_3, tr5_w32c_5_1_3, x3_30, x3_31, tl2_6_1_3, x3_32, x3_33, tl13_6_1_3, x3_34, x3_35, x3_36, te25_6_1_3, x3_37, tl31_6_1_3, x3_38, x3_39, te39_6_1_3, x3_40, tl45_6_1_3, x3_41, x3_42, x3_43, tl6_1_2_3, x3_44, op15_1_2_3, ol15_1_2_3, x3_45, to15_1_2_3, x3_46, tl20_1_2_3, x3_47, x3_48, x3_49, trv_w64_2_2_3, trv_w7c_2_2_3, x3_50, x3_51, k_3_3, dg'_3_3, flag'_3_3, cp'_3_3, rem'_3_3, x3_52, x3_53, x3_54, x3_55, op9_3_3, ol9_3_3, x3_56, te9_3_3, x3_57, x3_58, vp20_3_3, vl20_3_3, x3_59, te20_3_3, x3_60, sr25_3_3, ss25_3_3, x3_61, x3_62, tl9_1_4_3, x3_63, x3_64, x3_65, te20_1_4_3, x3_66, op26_1_4_3, ol26_1_4_3, x3_67, to26_1_4_3, x3_68, tl30_1_4_3, x3_69, x3_70, te39_1_4_3, x3_71, vp45_1_4_3, vl45_1_4_3, x3_72, te45_1_4_3, x3_73, x3_74, x3_75, tl2_2_4_3, x3_76, ip2_2_4_3, il2_2_4_3, x3_77, x3_78, tl13_2_4_3, x3_79, tm18_2_4_3, x3_80, tt3_w264_3_4_3, tt3_w268_3_4_3, x3_81, x3_82, tt4_w264_4_4_3, tt4_w268_4_4_3, x3_83, x3_84, tt5_w264_5_4_3, tt5_w268_5_4_3, x3_85, x3_86, tt6_w264_6_4_3, tt6_w268_6_4_3, x3_87, x3_88, k_6_3, x3_89, x3_90, c'_6_3, q'_6_3, x3_91, x3_92, x3_93, x3_94, x3_95, x3_96, pv_8_3, x3_97, x4_0, ix8_1_1_4, x4_1, ix18_1_1_4, x4_2, ix26_1_1_4, x4_3, ix34_1_1_4, x4_4, x4_5, x4_6, x4_7, c'_2_4, p'_2_4, w64'_2_4, w74'_2_4, x4_8, x4_9, x4_10, bs7_2_4, x4_11, x4_12, k_3_4, x4_13, x4_14, c'_3_4, q'_3_4, x4_15, x4_16, x4_17, sg_5_4, k_5_4, f'_5_4, w38'_5_4, w50'_5_4, sg'_5_4, x4_18, x4_19, x4_20, x4_21, x4_22, root6_3_6_4, x4_23, x4_24, x4_25, x4_26, x4_27, x4_28, x4_29, x4_30, x4_31, x4_32, n4, c1.trans (c2.trans (c3.trans (c4))), fR4, s4, E4, V4,
    by rw [r4_3, r3_3, r2_3, r1_3], by rw [r4_4, r3_4, r2_4, r1_4], r4_2, r4_18, r4_19, r4_20, r4_21, r4_22, r4_23, r4_24, r4_25, w4_3c, w4_54, w4_58, w4_5c, w4_60, w4_78, w4_7c, w4_388, w4_38c, w4_390, w4_394, w4_1c, w4_20, w4_34, w4_40, w4_4c, w4_64, w4_74, q4_3e0, w4_380, w4_398, w4_39c, w4_3a0, w4_3a4, b4_384, b4_3a8, w4_68, w4_6c, w4_70, b4_1fc, b4_420, b4_421, w4_24, w4_38, w4_50, w4_28, w4_44, w4_48, w4_18, w4_30, w4_2c, ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_94))), ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_9c))), ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_a4))), ((K4_L.b8 (by decide) (by decide)).trans ((K3_L.b8 (by decide) (by decide)).trans ((K2_L.b8 (by decide) (by decide)).trans b1_130))), ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_80))), ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_84))), ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_88))), ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_8c))), ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_90))), ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_98))), ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_a0))), ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_a8))), ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_ac))), ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_b0))), ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_b4))), ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_b8))), ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_bc))), ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_c0))), ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_c4))), ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_128))), ((K4_L.b8 (by decide) (by decide)).trans ((K3_L.b8 (by decide) (by decide)).trans ((K2_L.b8 (by decide) (by decide)).trans b1_c8))), ((K4_L.w32 (by decide) (by decide)).trans w3_170), ((K4_L.w32 (by decide) (by decide)).trans w3_174), ((K4_L.w32 (by decide) (by decide)).trans w3_178), ((K4_L.w32 (by decide) (by decide)).trans w3_17c), ((K4_L.w32 (by decide) (by decide)).trans w3_180), ((K4_L.w32 (by decide) (by decide)).trans w3_184), ((K4_L.w32 (by decide) (by decide)).trans w3_188), ((K4_L.w32 (by decide) (by decide)).trans w3_18c), ((K4_L.w32 (by decide) (by decide)).trans w3_1f0), ((K4_L.w32 (by decide) (by decide)).trans w3_1f4), ((K4_L.b8 (by decide) (by decide)).trans b3_190), ((((K1_L).trans K2_L).trans K3_L).trans K4_L).mono (by decide)⟩)

end C3.RV32.Sv
