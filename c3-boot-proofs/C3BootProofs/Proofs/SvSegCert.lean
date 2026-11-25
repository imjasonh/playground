import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvSegLeaf
import C3BootProofs.Proofs.SvExtLoop
import C3BootProofs.Proofs.SvL8a
import C3BootProofs.Proofs.SvISearch
import C3BootProofs.Proofs.SvLh
import C3BootProofs.Proofs.SvDpv

/-!
# `sigstore::verify`: The leaf certificate and its issuer

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **The leaf certificate and its issuer**: from 0x5C to the P-256 check at 0xA4C: the leaf, its extensions, the intermediate that issued it, the leaf's signature, and the policy. -/
theorem sv_seg_cert {B out bp rootp dg lp ll : Word} {v : Nat → Word} {n0 : Machine} {sl5 : Word} {sl7 : Word} {sl9 : Word}
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
    (sg_in : SvIn B (memLoad32 M0 (bp + 0x8)) (memLoad32 M0 (bp + 0xC)).toNat) :
    SvErrRet B out v n0 ∨ Panics n0 ∨
    (∃ t_1_1, derElement 0x30 (memBytes M0 lp ll.toNat) = .ok t_1_1 ∧ ll - BitVec.ofNat 32 (t_1_1.header + t_1_1.len) = 0 ∧
      ∃ tl1_2_1, derElement 0x30 (memBytes M0 ((lp + BitVec.ofNat 32 t_1_1.header)) ((BitVec.ofNat 32 t_1_1.len)).toNat) = .ok tl1_2_1 ∧
      ∃ tl8_2_1, derElement 0x30 (memBytes M0 (((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) (((BitVec.ofNat 32 t_1_1.len)) - BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)).toNat) = .ok tl8_2_1 ∧
      ∃ tl16_2_1, derElement 3 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) + BitVec.ofNat 32 (tl8_2_1.header + tl8_2_1.len)) ((((BitVec.ofNat 32 t_1_1.len)) - BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) - BitVec.ofNat 32 (tl8_2_1.header + tl8_2_1.len)).toNat) = .ok tl16_2_1 ∧
      ∃ bp16_2_1 bl16_2_1, derBitsOf (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) + BitVec.ofNat 32 (tl8_2_1.header + tl8_2_1.len)) ((((BitVec.ofNat 32 t_1_1.len)) - BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) - BitVec.ofNat 32 (tl8_2_1.header + tl8_2_1.len)).toNat) ((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) + BitVec.ofNat 32 (tl8_2_1.header + tl8_2_1.len)) (.ok tl16_2_1) = .ok (bp16_2_1, bl16_2_1) ∧
      (((((BitVec.ofNat 32 t_1_1.len)) - BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) - BitVec.ofNat 32 (tl8_2_1.header + tl8_2_1.len)) - BitVec.ofNat 32 (tl16_2_1.header + tl16_2_1.len) = 0) ∧
      ∃ tl28_2_1, derOptRes 0xA0 (memBytes M0 (((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) (BitVec.ofNat 32 tl1_2_1.len).toNat) = some (.ok tl28_2_1) ∧
      derIntIsOf M0 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 tl28_2_1.header) (BitVec.ofNat 32 tl28_2_1.len).toNat) ((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 tl28_2_1.header) (derElement 2 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 tl28_2_1.header) (BitVec.ofNat 32 tl28_2_1.len).toNat)) ((BitVec.ofNat 32 0x2).extractLsb' 0 8) = .ok true ∧
      ∃ te41_2_1, derElement 2 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 tl28_2_1.header) (BitVec.ofNat 32 tl28_2_1.len).toNat) = .ok te41_2_1 ∧
      ((BitVec.ofNat 32 tl28_2_1.len) - BitVec.ofNat 32 (te41_2_1.header + te41_2_1.len) = 0) ∧
      ∃ tl1_3_1, derElement 2 (memBytes M0 (((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) (((BitVec.ofNat 32 tl1_2_1.len) - BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))).toNat) = .ok tl1_3_1 ∧
      ∃ ip1_3_1 il1_3_1, derPosIntOf (memBytes M0 (((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) (((BitVec.ofNat 32 tl1_2_1.len) - BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))).toNat) (((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) (.ok tl1_3_1) = .ok (ip1_3_1, il1_3_1) ∧
      ((il1_3_1).toNat ≤ 20) ∧
      ∃ tl8_3_1, derElement 0x30 (memBytes M0 ((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) ((((BitVec.ofNat 32 tl1_2_1.len) - BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) - BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)).toNat) = .ok tl8_3_1 ∧
      ∃ op21_3_1 ol21_3_1, derAlgOf M0 ((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) (tl8_3_1.header + tl8_3_1.len) = .ok ((op21_3_1, ol21_3_1), none) ∧
      (memBytes M0 op21_3_1 ol21_3_1 = memBytes M0 (BitVec.ofNat 32 (img% svOidEcdsaSha384Address)) 8) ∧
      ∃ tl3_4_1, derElement 0x30 (memBytes M0 ((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) + BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))) ((((((BitVec.ofNat 32 tl1_2_1.len) - BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) - BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) - BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))).toNat) = .ok tl3_4_1 ∧
      ∃ tl11_4_1, derElement 0x30 (memBytes M0 (((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) + BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))) + BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) (((((((BitVec.ofNat 32 tl1_2_1.len) - BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) - BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) - BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))) - BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)).toNat) = .ok tl11_4_1 ∧
      ∃ tm20_4_1 rs20_4_1, readTime (memBytes M0 ((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) + BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))) + BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) + BitVec.ofNat 32 tl11_4_1.header) (tl11_4_1.len)) = some (tm20_4_1, rs20_4_1) ∧
      ∃ tm28_4_1 rs28_4_1, readTime rs20_4_1 = some (tm28_4_1, rs28_4_1) ∧
      (rs28_4_1 = []) ∧
      ∃ tl2_5_1, derElement 0x30 (memBytes M0 (((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) + BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))) + BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) + BitVec.ofNat 32 (tl11_4_1.header + tl11_4_1.len))) (((((((((BitVec.ofNat 32 tl1_2_1.len) - BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) - BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) - BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))) - BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) - BitVec.ofNat 32 (tl11_4_1.header + tl11_4_1.len))).toNat) = .ok tl2_5_1 ∧
      ∃ tl6_5_1, derElement 0x30 (memBytes M0 ((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) + BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))) + BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) + BitVec.ofNat 32 (tl11_4_1.header + tl11_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) ((((((((((BitVec.ofNat 32 tl1_2_1.len) - BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) - BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) - BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))) - BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) - BitVec.ofNat 32 (tl11_4_1.header + tl11_4_1.len))) - BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)).toNat) = .ok tl6_5_1 ∧
      ∃ op15_5_1 ol15_5_1 prp15_5_1 pu15_5_1, derAlgOf M0 (((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) + BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))) + BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) + BitVec.ofNat 32 (tl11_4_1.header + tl11_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) + BitVec.ofNat 32 tl6_5_1.header) (tl6_5_1.len) = .ok ((op15_5_1, ol15_5_1), some (prp15_5_1, pu15_5_1)) ∧
      ∃ ta15_5_1, derElement 0x30 (memBytes M0 (((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) + BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))) + BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) + BitVec.ofNat 32 (tl11_4_1.header + tl11_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) + BitVec.ofNat 32 tl6_5_1.header) (tl6_5_1.len)) = .ok ta15_5_1 ∧
      (BitVec.ofNat 8 pu15_5_1.tag = BitVec.ofNat 8 6) ∧
      (memBytes M0 (prp15_5_1 + BitVec.ofNat 32 pu15_5_1.header) pu15_5_1.len = memBytes M0 (BitVec.ofNat 32 (img% svOidPrime256v1Address)) 8) ∧
      (memBytes M0 op15_5_1 ol15_5_1 = memBytes M0 (BitVec.ofNat 32 (img% svOidEcPublicKeyAddress)) 7) ∧
      ∃ tl35_5_1, derElement 3 (memBytes M0 ((((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) + BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))) + BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) + BitVec.ofNat 32 (tl11_4_1.header + tl11_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) + BitVec.ofNat 32 tl6_5_1.header) + BitVec.ofNat 32 (ta15_5_1.header + ta15_5_1.len)) ((BitVec.ofNat 32 (tl6_5_1.len)) - BitVec.ofNat 32 (ta15_5_1.header + ta15_5_1.len)).toNat) = .ok tl35_5_1 ∧
      ∃ bp35_5_1 bl35_5_1, derBitsOf (memBytes M0 ((((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) + BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))) + BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) + BitVec.ofNat 32 (tl11_4_1.header + tl11_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) + BitVec.ofNat 32 tl6_5_1.header) + BitVec.ofNat 32 (ta15_5_1.header + ta15_5_1.len)) ((BitVec.ofNat 32 (tl6_5_1.len)) - BitVec.ofNat 32 (ta15_5_1.header + ta15_5_1.len)).toNat) ((((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) + BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))) + BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) + BitVec.ofNat 32 (tl11_4_1.header + tl11_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) + BitVec.ofNat 32 tl6_5_1.header) + BitVec.ofNat 32 (ta15_5_1.header + ta15_5_1.len)) (.ok tl35_5_1) = .ok (bp35_5_1, bl35_5_1) ∧
      (bl35_5_1 = BitVec.ofNat 32 0x41) ∧
      (((BitVec.ofNat 32 (tl6_5_1.len)) - BitVec.ofNat 32 (ta15_5_1.header + ta15_5_1.len)) - BitVec.ofNat 32 (tl35_5_1.header + tl35_5_1.len) = 0) ∧
      (M0 bp35_5_1 = BitVec.ofNat 8 4) ∧
      (GsOk M0 bp35_5_1) ∧
      ∃ tl9_6_1, derOptRes 0xA3 (memBytes M0 ((((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) + BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))) + BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) + BitVec.ofNat 32 (tl11_4_1.header + tl11_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) + BitVec.ofNat 32 (tl6_5_1.header + tl6_5_1.len))) ((((((((((((BitVec.ofNat 32 tl1_2_1.len) - BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) - BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) - BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))) - BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) - BitVec.ofNat 32 (tl11_4_1.header + tl11_4_1.len))) - BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) - BitVec.ofNat 32 (tl6_5_1.header + tl6_5_1.len))).toNat) = some (.ok tl9_6_1) ∧
      (((((((((((((BitVec.ofNat 32 tl1_2_1.len) - BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) - BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) - BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))) - BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) - BitVec.ofNat 32 (tl11_4_1.header + tl11_4_1.len))) - BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) - BitVec.ofNat 32 (tl6_5_1.header + tl6_5_1.len))) - BitVec.ofNat 32 (tl9_6_1.header + tl9_6_1.len) = 0) ∧
      ∃ tl24_6_1, derElement 0x30 (memBytes M0 (((((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) + BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))) + BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) + BitVec.ofNat 32 (tl11_4_1.header + tl11_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) + BitVec.ofNat 32 (tl6_5_1.header + tl6_5_1.len))) + BitVec.ofNat 32 tl9_6_1.header) (BitVec.ofNat 32 tl9_6_1.len).toNat) = .ok tl24_6_1 ∧
      ((BitVec.ofNat 32 tl9_6_1.len) - BitVec.ofNat 32 (tl24_6_1.header + tl24_6_1.len) = 0) ∧
      ∃ u0 u1 u2, ∃ k_2 f2c'_2 f30'_2 rem'_2 sl0'_2 sl1'_2 sl2'_2 sl3'_2 sl4'_2 sl5'_2 sl6'_2 sl7'_2 sl8'_2 sl9'_2 cur'_2, svChain (sv_extStep B out bp (lp + BitVec.ofNat 32 t_1_1.header) dg rootp ll bp16_2_1 bp35_5_1 bl16_2_1 (BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) ((((((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) + BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))) + BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) + BitVec.ofNat 32 (tl11_4_1.header + tl11_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) + BitVec.ofNat 32 (tl6_5_1.header + tl6_5_1.len))) + BitVec.ofNat 32 tl9_6_1.header) + BitVec.ofNat 32 tl24_6_1.header) (BitVec.ofNat 32 tl24_6_1.len) (BitVec.ofNat 32 (tm28_4_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm28_4_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm20_4_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm20_4_1 % 2 ^ 32)) (BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) (((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) + BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len)) lp (BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len)) ((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) (BitVec.ofNat 32 (tl8_2_1.header + tl8_2_1.len)) (((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) v M0) k_2 ((BitVec.ofNat 32 0x0), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 tl24_6_1.len), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 tl24_6_1.len), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 (tl24_6_1.header + tl24_6_1.len)), (BitVec.ofNat 32 0x0), (u0), (BitVec.ofNat 32 0x0), (u1), (BitVec.ofNat 32 0x0), (u2), ((((((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) + BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len))) + BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) + BitVec.ofNat 32 (tl11_4_1.header + tl11_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) + BitVec.ofNat 32 (tl6_5_1.header + tl6_5_1.len))) + BitVec.ofNat 32 tl9_6_1.header) + BitVec.ofNat 32 tl24_6_1.header)) (f2c'_2, f30'_2, rem'_2, sl0'_2, sl1'_2, sl2'_2, sl3'_2, sl4'_2, sl5'_2, sl6'_2, sl7'_2, sl8'_2, sl9'_2, cur'_2) ∧
      rem'_2 = 0 ∧ (sl0'_2 = 0 ∨ SvIn B sl0'_2 sl1'_2.toNat) ∧ (sl2'_2 = 0 ∨ SvIn B sl2'_2 sl3'_2.toNat) ∧ (sl4'_2 = 0 ∨ SvIn B sl4'_2 sl5'_2.toNat) ∧ (sl6'_2 = 0 ∨ SvIn B sl6'_2 sl7'_2.toNat) ∧ (sl8'_2 = 0 ∨ SvIn B sl8'_2 sl9'_2.toNat) ∧
      (sl0'_2 ≠ 0) ∧ (sl2'_2 ≠ 0) ∧ (sl4'_2 ≠ 0) ∧ (sl6'_2 ≠ 0) ∧ ((if BitVec.ult 0 (sl8'_2) then (1 : Word) else 0) &&& ((f2c'_2) &&& (f30'_2)) ≠ 0) ∧ (memBytes M0 (((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) ((BitVec.ofNat 32 (tl8_2_1.header + tl8_2_1.len)).toNat) = memBytes M0 ((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) ((BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len)).toNat)) ∧ ∃ sr40_2 ss40_2, ecdsaSigOf 48 M0 (bp16_2_1) ((bl16_2_1.toNat)) = .ok (sr40_2, ss40_2) ∧
      ∃ k_4, k_4 < 8 ∧
      (∀ i, i < k_4 → ∀ c'_4 q'_4, (c'_4, q'_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((rootp) + BitVec.ofNat 32 0x2C)) → ¬ (memBytes M0 (memLoad32 M0 (q'_4 + 0xFFFFFFFC)) (memLoad32 M0 (q'_4 + 0x0)).toNat = memBytes M0 (((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) + BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len)) (BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)).toNat)) ∧
      ∃ c'_4 q'_4, (c'_4, q'_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) k_4 ((BitVec.ofNat 32 0x100), ((rootp) + BitVec.ofNat 32 0x2C)) ∧ (memBytes M0 (memLoad32 M0 (q'_4 + 0xFFFFFFFC)) (memLoad32 M0 (q'_4 + 0x0)).toNat = memBytes M0 (((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) + BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len)) (BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)).toNat) ∧
      ((memLoad32 M0 (q'_4 + 0xFFFFFFFC)) ≠ 0) ∧
      ∃ pv_5, SvPvRes M0 (memLoad32 M0 (((q'_4) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4)) (B + 0x21A0 + BitVec.ofNat 32 0x170) 48 (sha384 (memBytes M0 (lp + BitVec.ofNat 32 t_1_1.header) (BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)).toNat)) (B + 0x21A0 + BitVec.ofNat 32 0xC8) (B + 0x21A0 + BitVec.ofNat 32 0xF8) sr40_2 ss40_2 (some pv_5) ∧
      (pv_5 ≠ 0) ∧
      (memBytes M0 sl0'_2 sl1'_2.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x0)) (memLoad32 M0 (rootp + 0x4)).toNat) ∧
      (memBytes M0 sl2'_2 sl3'_2.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x8)) (memLoad32 M0 (rootp + 0xC)).toNat) ∧
      (memBytes M0 sl4'_2 sl5'_2.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x10)) (memLoad32 M0 (rootp + 0x14)).toNat) ∧
      (memBytes M0 sl6'_2 sl7'_2.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x18)) (memLoad32 M0 (rootp + 0x1C)).toNat) ∧
      (memBytes M0 sl8'_2 sl9'_2.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x20)) (memLoad32 M0 (rootp + 0x24)).toNat) ∧
      ∃ sr43_6 ss43_6, ecdsaSigOf 32 M0 ((memLoad32 M0 (bp + 0x8))) ((memLoad32 M0 (bp + 0xC)).toNat) = .ok (sr43_6, ss43_6) ∧
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0xA4C (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = dg ∧
        reg n' (21 : Fin 32) = rootp ∧
        reg n' (22 : Fin 32) = ll ∧
        reg n' (23 : Fin 32) = ((q'_4) + BitVec.ofNat 32 0x20) ∧
        reg n' (24 : Fin 32) = bp35_5_1 ∧
        reg n' (26 : Fin 32) = sl0'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl9'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl7'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl5'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl3'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl1'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl8'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl6'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = sl4'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = sl2'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = (memLoad32 M0 (bp + 0xC)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = (memLoad32 M0 (bp + 0x8)) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = BitVec.ofNat 8 ((sr43_6).getD 0 0) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x131 + j)) = BitVec.ofNat 8 ((sr43_6).getD (1 + j) 0)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x150 + j)) = BitVec.ofNat 8 ((ss43_6).getD j 0)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x171 + j)) = BitVec.ofNat 8 ((sr43_6).getD j 0)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x191 + j)) = BitVec.ofNat 8 ((ss43_6).getD j 0)) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x291 + j)) = BitVec.ofNat 8 ((sr43_6).getD (1 + j) 0)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x2B0 + j)) = BitVec.ofNat 8 ((ss43_6).getD j 0)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x360) = lp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x364) = ll ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x368) = lp + BitVec.ofNat 32 (t_1_1.header + t_1_1.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x36C) = ll - BitVec.ofNat 32 (t_1_1.header + t_1_1.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = (lp + BitVec.ofNat 32 t_1_1.header) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = (BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) + BitVec.ofNat 32 (tl8_3_1.header + tl8_3_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl0'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl2'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl4'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x370) = lp + BitVec.ofNat 32 t_1_1.header ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x374) = (BitVec.ofNat 32 t_1_1.len).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x375) = (BitVec.ofNat 32 t_1_1.len).extractLsb' 8 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x376) = (BitVec.ofNat 32 t_1_1.len).extractLsb' 16 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x377) = (BitVec.ofNat 32 t_1_1.len).extractLsb' 24 8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = (BitVec.ofNat 32 ((BitVec.ofNat 32 (tl8_2_1.header + tl8_2_1.len)).toNat)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x27C) = ((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x280) = BitVec.ofNat 32 tl1_2_1.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = ((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl28_2_1.header + tl28_2_1.len))) + BitVec.ofNat 32 (tl1_3_1.header + tl1_3_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = (BitVec.ofNat 32 (tm28_4_1 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = (BitVec.ofNat 32 (tm28_4_1 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = (BitVec.ofNat 32 (tm20_4_1 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = (BitVec.ofNat 32 (tm20_4_1 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = (BitVec.ofNat 32 (tl3_4_1.header + tl3_4_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl1'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl3'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl5'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = sl6'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = sl7'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = sl8'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = sl9'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = (BitVec.ofNat 32 (tm20_4_1 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = (BitVec.ofNat 32 (tm20_4_1 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = (BitVec.ofNat 32 (tm28_4_1 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = (BitVec.ofNat 32 (tm28_4_1 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = bp35_5_1 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = BitVec.ofNat 8 (sr40_2.getD 0 0) ∧
        SvKeepL B n0.mem n'.mem [(0x80, 0x10), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x80, 0x11), (0x378, 0x8), (0x80, 0x11), (0x378, 0x8), (0x7C, 0x4), (0x78, 0x4), (0x80, 0x8), (0x378, 0x8), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x80, 0x18), (0x284, 0x8), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x264, 0x8), (0x420, 0x4), (0x424, 0x4), (0x74, 0x4), (0x428, 0x4), (0x70, 0x4), (0x42C, 0x4), (0x80, 0x1C), (0x428, 0x8), (0x6C, 0x4), (0x68, 0x4), (0x64, 0x4), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x60, 0x4), (0x5C, 0x4), (0x3E8, 0x8), (0x58, 0x4), (0x54, 0x4), (0x425, 0xB), (0x424, 0x1), (0x80, 0x48), (0x130, 0x4), (0x134, 0x4), (0x138, 0x4), (0x13C, 0x4), (0x138, 0x8), (0x150, 0x4), (0x154, 0x4), (0x158, 0x4), (0x50, 0x4), (0x15C, 0x4), (0x80, 0x4), (0x88, 0x4), (0x90, 0x4), (0x98, 0x4), (0xA0, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x38, 0x4), (0x34, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x1FC, 0x4), (0x200, 0x4), (0x204, 0x4), (0x208, 0x4), (0x204, 0x8), (0x385, 0xB), (0x384, 0x1), (0x84, 0x4), (0x8C, 0x4), (0x94, 0x4), (0x9C, 0x4), (0xA4, 0x4), (0x80, 0x61), (0x170, 0x5F), (0x85, 0x1), (0x86, 0x1), (0x87, 0x1), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xC8, 0x1), (0xC9, 0x5F), (0x84, 0x1), (0xB8, 0x4), (0xBC, 0x4), (0xC0, 0x4), (0xC4, 0x4), (0x128, 0x4), (0x170, 0x30), (0x170, 0x41), (0x291, 0x3F), (0x130, 0x1), (0x131, 0x1F), (0x150, 0x20)]) := by
  rcases sv_seg_leaf FW E0 V0 hret hO s0 M0 fM g0_2 g0_10 g0_11 g0_18 g0_19 g0_20 g0_21 g0_22 g0_26 w0_360 w0_364 w0_368 w0_36c lc_in D0 with e | hx1
  · exact .inl e
  obtain ⟨t_1_1, hx1⟩ := hx1
  obtain ⟨x1_0, hx1⟩ := hx1
  obtain ⟨x1_1, hx1⟩ := hx1
  obtain ⟨tl1_2_1, hx1⟩ := hx1
  obtain ⟨x1_2, hx1⟩ := hx1
  obtain ⟨tl8_2_1, hx1⟩ := hx1
  obtain ⟨x1_3, hx1⟩ := hx1
  obtain ⟨tl16_2_1, hx1⟩ := hx1
  obtain ⟨x1_4, hx1⟩ := hx1
  obtain ⟨bp16_2_1, hx1⟩ := hx1
  obtain ⟨bl16_2_1, hx1⟩ := hx1
  obtain ⟨x1_5, hx1⟩ := hx1
  obtain ⟨x1_6, hx1⟩ := hx1
  obtain ⟨tl28_2_1, hx1⟩ := hx1
  obtain ⟨x1_7, hx1⟩ := hx1
  obtain ⟨x1_8, hx1⟩ := hx1
  obtain ⟨te41_2_1, hx1⟩ := hx1
  obtain ⟨x1_9, hx1⟩ := hx1
  obtain ⟨x1_10, hx1⟩ := hx1
  obtain ⟨tl1_3_1, hx1⟩ := hx1
  obtain ⟨x1_11, hx1⟩ := hx1
  obtain ⟨ip1_3_1, hx1⟩ := hx1
  obtain ⟨il1_3_1, hx1⟩ := hx1
  obtain ⟨x1_12, hx1⟩ := hx1
  obtain ⟨x1_13, hx1⟩ := hx1
  obtain ⟨tl8_3_1, hx1⟩ := hx1
  obtain ⟨x1_14, hx1⟩ := hx1
  obtain ⟨op21_3_1, hx1⟩ := hx1
  obtain ⟨ol21_3_1, hx1⟩ := hx1
  obtain ⟨x1_15, hx1⟩ := hx1
  obtain ⟨x1_16, hx1⟩ := hx1
  obtain ⟨tl3_4_1, hx1⟩ := hx1
  obtain ⟨x1_17, hx1⟩ := hx1
  obtain ⟨tl11_4_1, hx1⟩ := hx1
  obtain ⟨x1_18, hx1⟩ := hx1
  obtain ⟨tm20_4_1, hx1⟩ := hx1
  obtain ⟨rs20_4_1, hx1⟩ := hx1
  obtain ⟨x1_19, hx1⟩ := hx1
  obtain ⟨tm28_4_1, hx1⟩ := hx1
  obtain ⟨rs28_4_1, hx1⟩ := hx1
  obtain ⟨x1_20, hx1⟩ := hx1
  obtain ⟨x1_21, hx1⟩ := hx1
  obtain ⟨tl2_5_1, hx1⟩ := hx1
  obtain ⟨x1_22, hx1⟩ := hx1
  obtain ⟨tl6_5_1, hx1⟩ := hx1
  obtain ⟨x1_23, hx1⟩ := hx1
  obtain ⟨op15_5_1, hx1⟩ := hx1
  obtain ⟨ol15_5_1, hx1⟩ := hx1
  obtain ⟨prp15_5_1, hx1⟩ := hx1
  obtain ⟨pu15_5_1, hx1⟩ := hx1
  obtain ⟨x1_24, hx1⟩ := hx1
  obtain ⟨ta15_5_1, hx1⟩ := hx1
  obtain ⟨x1_25, hx1⟩ := hx1
  obtain ⟨x1_26, hx1⟩ := hx1
  obtain ⟨x1_27, hx1⟩ := hx1
  obtain ⟨x1_28, hx1⟩ := hx1
  obtain ⟨tl35_5_1, hx1⟩ := hx1
  obtain ⟨x1_29, hx1⟩ := hx1
  obtain ⟨bp35_5_1, hx1⟩ := hx1
  obtain ⟨bl35_5_1, hx1⟩ := hx1
  obtain ⟨x1_30, hx1⟩ := hx1
  obtain ⟨x1_31, hx1⟩ := hx1
  obtain ⟨x1_32, hx1⟩ := hx1
  obtain ⟨x1_33, hx1⟩ := hx1
  obtain ⟨x1_34, hx1⟩ := hx1
  obtain ⟨tl9_6_1, hx1⟩ := hx1
  obtain ⟨x1_35, hx1⟩ := hx1
  obtain ⟨x1_36, hx1⟩ := hx1
  obtain ⟨tl24_6_1, hx1⟩ := hx1
  obtain ⟨x1_37, hx1⟩ := hx1
  obtain ⟨x1_38, hx1⟩ := hx1
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
  obtain ⟨r1_23, hx1⟩ := hx1
  obtain ⟨r1_24, hx1⟩ := hx1
  obtain ⟨r1_25, hx1⟩ := hx1
  obtain ⟨r1_26, hx1⟩ := hx1
  obtain ⟨r1_27, hx1⟩ := hx1
  obtain ⟨w1_2c, hx1⟩ := hx1
  obtain ⟨w1_30, hx1⟩ := hx1
  obtain ⟨w1_50, hx1⟩ := hx1
  obtain ⟨w1_80, hx1⟩ := hx1
  obtain ⟨w1_84, hx1⟩ := hx1
  obtain ⟨w1_88, hx1⟩ := hx1
  obtain ⟨w1_8c, hx1⟩ := hx1
  obtain ⟨w1_90, hx1⟩ := hx1
  obtain ⟨w1_98, hx1⟩ := hx1
  obtain ⟨w1_a0, hx1⟩ := hx1
  obtain ⟨w1_150, hx1⟩ := hx1
  obtain ⟨w1_154, hx1⟩ := hx1
  obtain ⟨w1_158, hx1⟩ := hx1
  obtain ⟨w1_15c, hx1⟩ := hx1
  obtain ⟨w1_360, hx1⟩ := hx1
  obtain ⟨w1_364, hx1⟩ := hx1
  obtain ⟨w1_368, hx1⟩ := hx1
  obtain ⟨w1_36c, hx1⟩ := hx1
  obtain ⟨w1_370, hx1⟩ := hx1
  obtain ⟨b1_374, hx1⟩ := hx1
  obtain ⟨b1_375, hx1⟩ := hx1
  obtain ⟨b1_376, hx1⟩ := hx1
  obtain ⟨b1_377, hx1⟩ := hx1
  obtain ⟨w1_78, hx1⟩ := hx1
  obtain ⟨w1_7c, hx1⟩ := hx1
  obtain ⟨w1_27c, hx1⟩ := hx1
  obtain ⟨w1_280, hx1⟩ := hx1
  obtain ⟨w1_70, hx1⟩ := hx1
  obtain ⟨w1_74, hx1⟩ := hx1
  obtain ⟨w1_54, hx1⟩ := hx1
  obtain ⟨w1_58, hx1⟩ := hx1
  obtain ⟨w1_5c, hx1⟩ := hx1
  obtain ⟨w1_60, hx1⟩ := hx1
  obtain ⟨w1_64, hx1⟩ := hx1
  obtain ⟨w1_68, hx1⟩ := hx1
  obtain ⟨w1_6c, hx1⟩ := hx1
  have K1_L := hx1
  rcases sv_extloop_st FW hret hO M0 (Nat.le_refl _) E1 V1 s1 fR1 r1_2 r1_8 r1_9 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 r1_24 r1_25 r1_27 w1_2c w1_30 w1_50 w1_54 w1_58 w1_5c w1_60 w1_64 w1_68 w1_6c w1_70 w1_74 w1_78 w1_7c w1_80 w1_84 w1_88 w1_8c w1_90 rfl w1_98 rfl w1_a0 rfl w1_150 w1_154 w1_158 w1_15c ((((((((((((((((lc_in).content x1_0).ofNatLen).content x1_2).ofNatLen).restW (opt_ok_elem x1_7)).restW x1_11).restW x1_14).restW x1_17).restW x1_18).restW x1_22).restW x1_23).content (opt_ok_elem x1_35)).ofNatLen).content x1_37).ofNatLen) SD0 (.inl rfl) (.inl rfl) (.inl rfl) (.inl rfl) (.inl rfl) ((((((((((((((((lc_in).content x1_0).ofNatLen).content x1_2).ofNatLen).restW (opt_ok_elem x1_7)).restW x1_11).restW x1_14).restW x1_17).restW x1_18).restW x1_22).restW x1_23).content (opt_ok_elem x1_35)).ofNatLen).content x1_37).ofNatLen) (((((lc_in).content x1_0).ofNatLen).restW x1_2).rawW x1_3) ((((((((lc_in).content x1_0).ofNatLen).content x1_2).ofNatLen).restW (opt_ok_elem x1_7)).restW x1_11).rawW x1_14) (SvIn.bitsW (((((lc_in).content x1_0).ofNatLen).restW x1_2).restW x1_3) x1_4 x1_5) with e | hx2
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  obtain ⟨k_2, hx2⟩ := hx2
  obtain ⟨f2c'_2, hx2⟩ := hx2
  obtain ⟨f30'_2, hx2⟩ := hx2
  obtain ⟨rem'_2, hx2⟩ := hx2
  obtain ⟨sl0'_2, hx2⟩ := hx2
  obtain ⟨sl1'_2, hx2⟩ := hx2
  obtain ⟨sl2'_2, hx2⟩ := hx2
  obtain ⟨sl3'_2, hx2⟩ := hx2
  obtain ⟨sl4'_2, hx2⟩ := hx2
  obtain ⟨sl5'_2, hx2⟩ := hx2
  obtain ⟨sl6'_2, hx2⟩ := hx2
  obtain ⟨sl7'_2, hx2⟩ := hx2
  obtain ⟨sl8'_2, hx2⟩ := hx2
  obtain ⟨sl9'_2, hx2⟩ := hx2
  obtain ⟨cur'_2, hx2⟩ := hx2
  obtain ⟨x2_0, hx2⟩ := hx2
  obtain ⟨x2_1, hx2⟩ := hx2
  obtain ⟨x2_2, hx2⟩ := hx2
  obtain ⟨x2_3, hx2⟩ := hx2
  obtain ⟨x2_4, hx2⟩ := hx2
  obtain ⟨x2_5, hx2⟩ := hx2
  obtain ⟨x2_6, hx2⟩ := hx2
  obtain ⟨x2_7, hx2⟩ := hx2
  obtain ⟨x2_8, hx2⟩ := hx2
  obtain ⟨x2_9, hx2⟩ := hx2
  obtain ⟨x2_10, hx2⟩ := hx2
  obtain ⟨x2_11, hx2⟩ := hx2
  obtain ⟨x2_12, hx2⟩ := hx2
  obtain ⟨sr40_2, hx2⟩ := hx2
  obtain ⟨ss40_2, hx2⟩ := hx2
  obtain ⟨x2_13, hx2⟩ := hx2
  obtain ⟨n2, hx2⟩ := hx2
  obtain ⟨c2, hx2⟩ := hx2
  obtain ⟨s2, hx2⟩ := hx2
  obtain ⟨E2, hx2⟩ := hx2
  obtain ⟨V2, hx2⟩ := hx2
  obtain ⟨fR2, hx2⟩ := hx2
  obtain ⟨r2_2, hx2⟩ := hx2
  obtain ⟨r2_3, hx2⟩ := hx2
  obtain ⟨r2_4, hx2⟩ := hx2
  obtain ⟨r2_8, hx2⟩ := hx2
  obtain ⟨r2_9, hx2⟩ := hx2
  obtain ⟨r2_18, hx2⟩ := hx2
  obtain ⟨r2_19, hx2⟩ := hx2
  obtain ⟨r2_20, hx2⟩ := hx2
  obtain ⟨r2_21, hx2⟩ := hx2
  obtain ⟨r2_22, hx2⟩ := hx2
  obtain ⟨r2_24, hx2⟩ := hx2
  obtain ⟨r2_26, hx2⟩ := hx2
  obtain ⟨r2_27, hx2⟩ := hx2
  obtain ⟨w2_30, hx2⟩ := hx2
  obtain ⟨w2_34, hx2⟩ := hx2
  obtain ⟨w2_38, hx2⟩ := hx2
  obtain ⟨w2_3c, hx2⟩ := hx2
  obtain ⟨w2_40, hx2⟩ := hx2
  obtain ⟨w2_44, hx2⟩ := hx2
  obtain ⟨w2_48, hx2⟩ := hx2
  obtain ⟨w2_4c, hx2⟩ := hx2
  obtain ⟨w2_50, hx2⟩ := hx2
  obtain ⟨w2_54, hx2⟩ := hx2
  obtain ⟨w2_58, hx2⟩ := hx2
  obtain ⟨w2_5c, hx2⟩ := hx2
  obtain ⟨w2_60, hx2⟩ := hx2
  obtain ⟨w2_64, hx2⟩ := hx2
  obtain ⟨w2_68, hx2⟩ := hx2
  obtain ⟨w2_6c, hx2⟩ := hx2
  obtain ⟨w2_70, hx2⟩ := hx2
  obtain ⟨w2_74, hx2⟩ := hx2
  obtain ⟨w2_78, hx2⟩ := hx2
  obtain ⟨w2_7c, hx2⟩ := hx2
  obtain ⟨q2_81, hx2⟩ := hx2
  obtain ⟨q2_b1, hx2⟩ := hx2
  have K2_L := hx2
  rcases sv_l8a FW E2 V2 hret hO s2 M0 fR2 r2_2 r2_8 r2_9 r2_18 r2_19 r2_20 r2_21 r2_22 r2_24 r2_26 r2_27 w2_30 w2_34 w2_38 w2_3c w2_40 w2_44 w2_48 w2_4c w2_50 w2_54 w2_58 w2_5c w2_60 w2_64 w2_68 w2_6c w2_70 w2_74 w2_78 w2_7c q2_81 q2_b1 with ⟨-, e⟩ | hx3
  · exact .inl (SvErrRet.pre (c1.trans (c2)) (by rw [r2_3, r1_3]) (by rw [r2_4, r1_4])
      (fun x hx => (fR2 x hx).trans (fM x hx).symm) e)
  obtain ⟨n3, hx3⟩ := hx3
  obtain ⟨c3, hx3⟩ := hx3
  obtain ⟨s3, hx3⟩ := hx3
  obtain ⟨E3, hx3⟩ := hx3
  obtain ⟨V3, hx3⟩ := hx3
  obtain ⟨fR3, hx3⟩ := hx3
  obtain ⟨r3_2, hx3⟩ := hx3
  obtain ⟨r3_3, hx3⟩ := hx3
  obtain ⟨r3_4, hx3⟩ := hx3
  obtain ⟨r3_8, hx3⟩ := hx3
  obtain ⟨r3_9, hx3⟩ := hx3
  obtain ⟨r3_18, hx3⟩ := hx3
  obtain ⟨r3_19, hx3⟩ := hx3
  obtain ⟨r3_20, hx3⟩ := hx3
  obtain ⟨r3_21, hx3⟩ := hx3
  obtain ⟨r3_22, hx3⟩ := hx3
  obtain ⟨r3_23, hx3⟩ := hx3
  obtain ⟨r3_24, hx3⟩ := hx3
  obtain ⟨r3_26, hx3⟩ := hx3
  obtain ⟨r3_27, hx3⟩ := hx3
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
  obtain ⟨w3_74, hx3⟩ := hx3
  obtain ⟨w3_78, hx3⟩ := hx3
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
  obtain ⟨w3_128, hx3⟩ := hx3
  obtain ⟨b3_c8, hx3⟩ := hx3
  obtain ⟨q3_c9, hx3⟩ := hx3
  obtain ⟨q3_f8, hx3⟩ := hx3
  obtain ⟨q3_170, hx3⟩ := hx3
  obtain ⟨q3_19f, hx3⟩ := hx3
  have K3_L := hx3
  rcases sv_isearch_st FW hret hO M0 (fun _ _ h => svCnt_zero Prod.fst (BitVec.ofNat 32 0x100) 0xFFFFFFE0 (by intro _; rfl) rfl (by decide) (congrArg Prod.fst h)) E3 V3 s3 fR3 r3_2 r3_8 r3_9 r3_18 r3_19 r3_20 r3_21 r3_22 r3_23 r3_24 r3_26 w3_30 w3_34 w3_38 w3_3c w3_40 w3_44 w3_48 w3_4c w3_50 w3_54 w3_58 w3_5c w3_60 w3_64 w3_68 w3_6c w3_70 w3_74 w3_78 w3_7c w3_80 w3_84 w3_88 w3_8c w3_90 w3_94 w3_98 w3_9c w3_a0 w3_a4 w3_a8 w3_ac w3_b0 w3_b4 w3_b8 w3_bc w3_c0 w3_c4 w3_128 b3_c8 q3_c9 q3_f8 (fun i hi c'_4 q'_4 h => ⟨(svCnt_ne Prod.fst (BitVec.ofNat 32 0x100) 0xFFFFFFE0 (by intro _; rfl) rfl (by decide) hi (congrArg Prod.fst h)), (H' i hi c'_4 q'_4 h).1, (H' i hi c'_4 q'_4 h).2.1, (H' i hi c'_4 q'_4 h).2.2.1, (H' i hi c'_4 q'_4 h).2.2.2.1, (H' i hi c'_4 q'_4 h).2.2.2.2, (((((((((lc_in).content x1_0).ofNatLen).content x1_2).ofNatLen).restW (opt_ok_elem x1_7)).restW x1_11).restW x1_14).rawW x1_17)⟩) with e | hx4
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3))) (by rw [r3_3, r2_3, r1_3]) (by rw [r3_4, r2_4, r1_4])
      (fun x hx => (fR3 x hx).trans (fM x hx).symm) e)
  obtain ⟨k_4, hx4⟩ := hx4
  obtain ⟨x4_0, hx4⟩ := hx4
  obtain ⟨x4_1, hx4⟩ := hx4
  obtain ⟨c'_4, hx4⟩ := hx4
  obtain ⟨q'_4, hx4⟩ := hx4
  obtain ⟨x4_2, hx4⟩ := hx4
  obtain ⟨x4_3, hx4⟩ := hx4
  obtain ⟨x4_4, hx4⟩ := hx4
  obtain ⟨n4, hx4⟩ := hx4
  obtain ⟨c4, hx4⟩ := hx4
  obtain ⟨s4, hx4⟩ := hx4
  obtain ⟨E4, hx4⟩ := hx4
  obtain ⟨V4, hx4⟩ := hx4
  obtain ⟨fR4, hx4⟩ := hx4
  obtain ⟨r4_2, hx4⟩ := hx4
  obtain ⟨r4_3, hx4⟩ := hx4
  obtain ⟨r4_4, hx4⟩ := hx4
  obtain ⟨r4_8, hx4⟩ := hx4
  obtain ⟨r4_9, hx4⟩ := hx4
  obtain ⟨r4_18, hx4⟩ := hx4
  obtain ⟨r4_19, hx4⟩ := hx4
  obtain ⟨r4_20, hx4⟩ := hx4
  obtain ⟨r4_21, hx4⟩ := hx4
  obtain ⟨r4_22, hx4⟩ := hx4
  obtain ⟨r4_23, hx4⟩ := hx4
  obtain ⟨r4_24, hx4⟩ := hx4
  obtain ⟨r4_25, hx4⟩ := hx4
  obtain ⟨r4_26, hx4⟩ := hx4
  obtain ⟨r4_27, hx4⟩ := hx4
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
  obtain ⟨w4_128, hx4⟩ := hx4
  obtain ⟨b4_c8, hx4⟩ := hx4
  obtain ⟨q4_c9, hx4⟩ := hx4
  obtain ⟨q4_f8, hx4⟩ := hx4
  have K4_L := hx4
  rcases sv_lh FW E4 V4 hret hO s4 M0 fR4 r4_2 r4_9 r4_18 r4_19 r4_20 r4_21 r4_22 r4_23 r4_24 r4_26 w4_84 b4_c8 q4_c9 q4_f8 HE0 RS ((((lc_in).content x1_0).ofNatLen).rawW x1_2) PE0 rfl (pkp_in k_4 x4_0 c'_4 q'_4 x4_2 x4_4) (apk k_4 x4_0 c'_4 q'_4 x4_2 x4_4) (pk_in k_4 x4_0 c'_4 q'_4 x4_2 x4_4) (side k_4 x4_0 c'_4 q'_4 x4_2 x4_4) with ⟨-, e⟩ | hx5
  · exact .inr (.inl (Panics.of_steps (c1.trans (c2.trans (c3.trans (c4)))) e))
  obtain ⟨pv_5, hx5⟩ := hx5
  obtain ⟨x5_0, hx5⟩ := hx5
  obtain ⟨n5, hx5⟩ := hx5
  obtain ⟨c5, hx5⟩ := hx5
  obtain ⟨s5, hx5⟩ := hx5
  obtain ⟨E5, hx5⟩ := hx5
  obtain ⟨V5, hx5⟩ := hx5
  obtain ⟨fR5, hx5⟩ := hx5
  obtain ⟨r5_2, hx5⟩ := hx5
  obtain ⟨r5_3, hx5⟩ := hx5
  obtain ⟨r5_4, hx5⟩ := hx5
  obtain ⟨r5_a0, hx5⟩ := hx5
  obtain ⟨r5_18, hx5⟩ := hx5
  obtain ⟨r5_19, hx5⟩ := hx5
  obtain ⟨r5_20, hx5⟩ := hx5
  obtain ⟨r5_21, hx5⟩ := hx5
  obtain ⟨r5_22, hx5⟩ := hx5
  obtain ⟨r5_23, hx5⟩ := hx5
  obtain ⟨r5_24, hx5⟩ := hx5
  obtain ⟨r5_26, hx5⟩ := hx5
  obtain ⟨mb5_170, hx5⟩ := hx5
  have K5_L := hx5
  rcases sv_dpv FW E5 V5 hret hO s5 M0 fR5 r5_2 r5_a0 r5_18 r5_19 r5_20 r5_21 r5_22 r5_23 r5_24 r5_26 ((K5_L.w32 (by decide) (by decide)).trans w4_30) ((K5_L.w32 (by decide) (by decide)).trans w4_34) ((K5_L.w32 (by decide) (by decide)).trans w4_38) ((K5_L.w32 (by decide) (by decide)).trans w4_3c) ((K5_L.w32 (by decide) (by decide)).trans w4_40) ((K5_L.w32 (by decide) (by decide)).trans w4_44) ((K5_L.w32 (by decide) (by decide)).trans w4_48) ((K5_L.w32 (by decide) (by decide)).trans w4_4c) ((K5_L.w32 (by decide) (by decide)).trans w4_50) rfl rfl he0p_in he0l_in ae0p ae0l (.inl ((x2_2.resolve_left x2_7))) e0_in rfl rfl he1p_in he1l_in ae1p ae1l (.inl ((x2_3.resolve_left x2_8))) e1_in rfl rfl he2p_in he2l_in ae2p ae2l (.inl ((x2_4.resolve_left x2_9))) e2_in rfl rfl he3p_in he3l_in ae3p ae3l (.inl ((x2_5.resolve_left x2_10))) e3_in rfl rfl he4p_in he4l_in ae4p ae4l (.inl ((x2_6.resolve_left (fun hx => x2_11 (by rw [hx]; exact BitVec.zero_and))))) e4_in rfl rfl hsgp_in hsgl_in asgp asgl sg_in with ⟨-, e⟩ | hx6
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5))))) (by rw [r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR5 x hx).trans (fM x hx).symm) e)
  obtain ⟨x6_0, hx6⟩ := hx6
  obtain ⟨x6_1, hx6⟩ := hx6
  obtain ⟨x6_2, hx6⟩ := hx6
  obtain ⟨x6_3, hx6⟩ := hx6
  obtain ⟨x6_4, hx6⟩ := hx6
  obtain ⟨x6_5, hx6⟩ := hx6
  obtain ⟨sr43_6, hx6⟩ := hx6
  obtain ⟨ss43_6, hx6⟩ := hx6
  obtain ⟨x6_6, hx6⟩ := hx6
  obtain ⟨n6, hx6⟩ := hx6
  obtain ⟨c6, hx6⟩ := hx6
  obtain ⟨s6, hx6⟩ := hx6
  obtain ⟨E6, hx6⟩ := hx6
  obtain ⟨V6, hx6⟩ := hx6
  obtain ⟨fR6, hx6⟩ := hx6
  obtain ⟨r6_2, hx6⟩ := hx6
  obtain ⟨r6_3, hx6⟩ := hx6
  obtain ⟨r6_4, hx6⟩ := hx6
  obtain ⟨r6_18, hx6⟩ := hx6
  obtain ⟨r6_19, hx6⟩ := hx6
  obtain ⟨r6_20, hx6⟩ := hx6
  obtain ⟨r6_21, hx6⟩ := hx6
  obtain ⟨r6_22, hx6⟩ := hx6
  obtain ⟨r6_23, hx6⟩ := hx6
  obtain ⟨r6_24, hx6⟩ := hx6
  obtain ⟨r6_26, hx6⟩ := hx6
  obtain ⟨w6_30, hx6⟩ := hx6
  obtain ⟨w6_34, hx6⟩ := hx6
  obtain ⟨w6_38, hx6⟩ := hx6
  obtain ⟨w6_3c, hx6⟩ := hx6
  obtain ⟨w6_40, hx6⟩ := hx6
  obtain ⟨w6_44, hx6⟩ := hx6
  obtain ⟨w6_48, hx6⟩ := hx6
  obtain ⟨w6_4c, hx6⟩ := hx6
  obtain ⟨w6_50, hx6⟩ := hx6
  obtain ⟨w6_68, hx6⟩ := hx6
  obtain ⟨w6_70, hx6⟩ := hx6
  obtain ⟨b6_130, hx6⟩ := hx6
  obtain ⟨q6_131, hx6⟩ := hx6
  obtain ⟨q6_150, hx6⟩ := hx6
  obtain ⟨q6_171, hx6⟩ := hx6
  obtain ⟨q6_191, hx6⟩ := hx6
  obtain ⟨q6_291, hx6⟩ := hx6
  obtain ⟨q6_2b0, hx6⟩ := hx6
  have K6_L := hx6
  exact .inr (.inr ⟨t_1_1, x1_0, x1_1, tl1_2_1, x1_2, tl8_2_1, x1_3, tl16_2_1, x1_4, bp16_2_1, bl16_2_1, x1_5, x1_6, tl28_2_1, x1_7, x1_8, te41_2_1, x1_9, x1_10, tl1_3_1, x1_11, ip1_3_1, il1_3_1, x1_12, x1_13, tl8_3_1, x1_14, op21_3_1, ol21_3_1, x1_15, x1_16, tl3_4_1, x1_17, tl11_4_1, x1_18, tm20_4_1, rs20_4_1, x1_19, tm28_4_1, rs28_4_1, x1_20, x1_21, tl2_5_1, x1_22, tl6_5_1, x1_23, op15_5_1, ol15_5_1, prp15_5_1, pu15_5_1, x1_24, ta15_5_1, x1_25, x1_26, x1_27, x1_28, tl35_5_1, x1_29, bp35_5_1, bl35_5_1, x1_30, x1_31, x1_32, x1_33, x1_34, tl9_6_1, x1_35, x1_36, tl24_6_1, x1_37, x1_38, (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x94)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4)), k_2, f2c'_2, f30'_2, rem'_2, sl0'_2, sl1'_2, sl2'_2, sl3'_2, sl4'_2, sl5'_2, sl6'_2, sl7'_2, sl8'_2, sl9'_2, cur'_2, x2_0, x2_1, x2_2, x2_3, x2_4, x2_5, x2_6, x2_7, x2_8, x2_9, x2_10, x2_11, x2_12, sr40_2, ss40_2, x2_13, k_4, x4_0, x4_1, c'_4, q'_4, x4_2, x4_3, x4_4, pv_5, x5_0, x6_0, x6_1, x6_2, x6_3, x6_4, x6_5, sr43_6, ss43_6, x6_6, n6, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6))))), fR6, s6, E6, V6,
    by rw [r6_3, r5_3, r4_3, r3_3, r2_3, r1_3], by rw [r6_4, r5_4, r4_4, r3_4, r2_4, r1_4], r6_2, r6_18, r6_19, r6_20, r6_21, r6_22, r6_23, r6_24, r6_26, w6_30, w6_34, w6_38, w6_3c, w6_40, w6_44, w6_48, w6_4c, w6_50, w6_68, w6_70, b6_130, q6_131, q6_150, q6_171, q6_191, q6_291, q6_2b0, ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_360))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_364))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_368))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_36c))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_80)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_84)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_88)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_8c)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_90)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_98)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_a0)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_370))))), ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans ((K4_L.b8 (by decide) (by decide)).trans ((K3_L.b8 (by decide) (by decide)).trans ((K2_L.b8 (by decide) (by decide)).trans b1_374))))), ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans ((K4_L.b8 (by decide) (by decide)).trans ((K3_L.b8 (by decide) (by decide)).trans ((K2_L.b8 (by decide) (by decide)).trans b1_375))))), ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans ((K4_L.b8 (by decide) (by decide)).trans ((K3_L.b8 (by decide) (by decide)).trans ((K2_L.b8 (by decide) (by decide)).trans b1_376))))), ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans ((K4_L.b8 (by decide) (by decide)).trans ((K3_L.b8 (by decide) (by decide)).trans ((K2_L.b8 (by decide) (by decide)).trans b1_377))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_78)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_7c)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_27c))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_280))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_74)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_54)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_58)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_5c)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_60)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_64)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_6c)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_94)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_9c)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_a4)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_a8)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_ac)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_b0)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_b4)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_b8)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_bc)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_c0)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_c4)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_128)), ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans b4_c8)), ((((((K1_L).trans K2_L).trans K3_L).trans K4_L).trans K5_L).trans K6_L).mono (by decide)⟩)

end C3.RV32.Sv
