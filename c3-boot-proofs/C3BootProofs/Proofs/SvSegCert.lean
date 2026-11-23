import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvSegLeaf
import C3BootProofs.Proofs.SvExtLoop
import C3BootProofs.Proofs.SvL8a
import C3BootProofs.Proofs.SvISearch
import C3BootProofs.Proofs.SvLh
import C3BootProofs.Proofs.SvSegDpv

/-!
# `sigstore::verify`: The leaf certificate and its issuer

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **The leaf certificate and its issuer**: from 0x72 to the P-256 check at 0xFBA: the leaf, its extensions, the intermediate that issued it, the leaf's signature, and the policy. -/
theorem sv_seg_cert {B out bp rootp dg lp ll : Word} {v : Nat → Word} {n0 : Machine} {sl5 : Word} {sl7 : Word} {sl9 : Word} {wd0 : Word} {wd4 : Word} {wd8 : Word} {wdc : Word} {we0 : Word} {we4 : Word} {we8 : Word} {wec : Word} {wf0 : Word} {wf4 : Word} {wf8 : Word} {wfc : Word} {w100 : Word} {w104 : Word} {w108 : Word} {w10c : Word} {w110 : Word} {w114 : Word} {w118 : Word} {w11c : Word} {w120 : Word} {w124 : Word} {w128 : Word} {w12c : Word}
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
    (atsl : (bp + 0xC).toNat % 4 = 0) :
    SvErrRet B out v n0 ∨ Panics n0 ∨
    (∃ t_1_1, derElement 0x30 (memBytes M0 lp ll.toNat) = .ok t_1_1 ∧ ll - BitVec.ofNat 32 (t_1_1.header + t_1_1.len) = 0 ∧
      ∃ tl1_2_1, derElement 0x30 (memBytes M0 ((lp + BitVec.ofNat 32 t_1_1.header)) ((BitVec.ofNat 32 t_1_1.len)).toNat) = .ok tl1_2_1 ∧
      ∃ tl8_2_1, derElement 0x30 (memBytes M0 (((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) (((BitVec.ofNat 32 t_1_1.len)) - BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)).toNat) = .ok tl8_2_1 ∧
      ∃ tl16_2_1, derElement 3 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) + BitVec.ofNat 32 (tl8_2_1.header + tl8_2_1.len)) ((((BitVec.ofNat 32 t_1_1.len)) - BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) - BitVec.ofNat 32 (tl8_2_1.header + tl8_2_1.len)).toNat) = .ok tl16_2_1 ∧
      ∃ bp16_2_1 bl16_2_1, derBitsOf (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) + BitVec.ofNat 32 (tl8_2_1.header + tl8_2_1.len)) ((((BitVec.ofNat 32 t_1_1.len)) - BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) - BitVec.ofNat 32 (tl8_2_1.header + tl8_2_1.len)).toNat) ((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) + BitVec.ofNat 32 (tl8_2_1.header + tl8_2_1.len)) (.ok tl16_2_1) = .ok (bp16_2_1, bl16_2_1) ∧
      (((((BitVec.ofNat 32 t_1_1.len)) - BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) - BitVec.ofNat 32 (tl8_2_1.header + tl8_2_1.len)) - BitVec.ofNat 32 (tl16_2_1.header + tl16_2_1.len) = 0) ∧
      ∃ tl29_2_1, derOptRes 0xA0 (memBytes M0 (((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) (BitVec.ofNat 32 tl1_2_1.len).toNat) = some (.ok tl29_2_1) ∧
      derIntIsOf M0 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 tl29_2_1.header) (BitVec.ofNat 32 tl29_2_1.len).toNat) ((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 tl29_2_1.header) (derElement 2 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 tl29_2_1.header) (BitVec.ofNat 32 tl29_2_1.len).toNat)) ((BitVec.ofNat 32 0x2).extractLsb' 0 8) = .ok true ∧
      ∃ te43_2_1, derElement 2 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 tl29_2_1.header) (BitVec.ofNat 32 tl29_2_1.len).toNat) = .ok te43_2_1 ∧
      ((BitVec.ofNat 32 tl29_2_1.len) - BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len) = 0) ∧
      ∃ tl2_3_1, derElement 2 (memBytes M0 (((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) (((BitVec.ofNat 32 tl1_2_1.len) - BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))).toNat) = .ok tl2_3_1 ∧
      ∃ ip2_3_1 il2_3_1, derPosIntOf (memBytes M0 (((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) (((BitVec.ofNat 32 tl1_2_1.len) - BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))).toNat) (((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) (.ok tl2_3_1) = .ok (ip2_3_1, il2_3_1) ∧
      ((il2_3_1).toNat ≤ 20) ∧
      ∃ tl9_3_1, derElement 0x30 (memBytes M0 ((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) ((((BitVec.ofNat 32 tl1_2_1.len) - BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) - BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)).toNat) = .ok tl9_3_1 ∧
      ∃ op19_3_1 ol19_3_1, derAlgOf M0 ((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) (tl9_3_1.header + tl9_3_1.len) = .ok ((op19_3_1, ol19_3_1), none) ∧
      (memBytes M0 op19_3_1 ol19_3_1 = memBytes M0 (BitVec.ofNat 32 0x3FCC4840) 8) ∧
      ∃ tl6_4_1, derElement 0x30 (memBytes M0 ((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))) ((((((BitVec.ofNat 32 tl1_2_1.len) - BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) - BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) - BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))).toNat) = .ok tl6_4_1 ∧
      ∃ tl13_4_1, derElement 0x30 (memBytes M0 (((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))) + BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)) (((((((BitVec.ofNat 32 tl1_2_1.len) - BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) - BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) - BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))) - BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)).toNat) = .ok tl13_4_1 ∧
      ∃ tm22_4_1 rs22_4_1, readTime (memBytes M0 ((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))) + BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)) + BitVec.ofNat 32 tl13_4_1.header) (tl13_4_1.len)) = some (tm22_4_1, rs22_4_1) ∧
      ∃ tm31_4_1 rs31_4_1, readTime rs22_4_1 = some (tm31_4_1, rs31_4_1) ∧
      (rs31_4_1 = []) ∧
      ∃ tl2_5_1, derElement 0x30 (memBytes M0 (((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))) + BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)) + BitVec.ofNat 32 (tl13_4_1.header + tl13_4_1.len))) (((((((((BitVec.ofNat 32 tl1_2_1.len) - BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) - BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) - BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))) - BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)) - BitVec.ofNat 32 (tl13_4_1.header + tl13_4_1.len))).toNat) = .ok tl2_5_1 ∧
      ∃ tl6_5_1, derElement 0x30 (memBytes M0 ((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))) + BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)) + BitVec.ofNat 32 (tl13_4_1.header + tl13_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) ((((((((((BitVec.ofNat 32 tl1_2_1.len) - BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) - BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) - BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))) - BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)) - BitVec.ofNat 32 (tl13_4_1.header + tl13_4_1.len))) - BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)).toNat) = .ok tl6_5_1 ∧
      ∃ op15_5_1 ol15_5_1 prp15_5_1 pu15_5_1, derAlgOf M0 (((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))) + BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)) + BitVec.ofNat 32 (tl13_4_1.header + tl13_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) + BitVec.ofNat 32 tl6_5_1.header) (tl6_5_1.len) = .ok ((op15_5_1, ol15_5_1), some (prp15_5_1, pu15_5_1)) ∧
      ∃ ta15_5_1, derElement 0x30 (memBytes M0 (((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))) + BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)) + BitVec.ofNat 32 (tl13_4_1.header + tl13_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) + BitVec.ofNat 32 tl6_5_1.header) (tl6_5_1.len)) = .ok ta15_5_1 ∧
      (BitVec.ofNat 8 pu15_5_1.tag = BitVec.ofNat 8 6) ∧
      (memBytes M0 (prp15_5_1 + BitVec.ofNat 32 pu15_5_1.header) pu15_5_1.len = memBytes M0 (BitVec.ofNat 32 0x3FCC4848) 8) ∧
      (memBytes M0 op15_5_1 ol15_5_1 = memBytes M0 (BitVec.ofNat 32 0x3FCC4914) 7) ∧
      ∃ tl35_5_1, derElement 3 (memBytes M0 ((((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))) + BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)) + BitVec.ofNat 32 (tl13_4_1.header + tl13_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) + BitVec.ofNat 32 tl6_5_1.header) + BitVec.ofNat 32 (ta15_5_1.header + ta15_5_1.len)) ((BitVec.ofNat 32 (tl6_5_1.len)) - BitVec.ofNat 32 (ta15_5_1.header + ta15_5_1.len)).toNat) = .ok tl35_5_1 ∧
      ∃ bp35_5_1 bl35_5_1, derBitsOf (memBytes M0 ((((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))) + BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)) + BitVec.ofNat 32 (tl13_4_1.header + tl13_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) + BitVec.ofNat 32 tl6_5_1.header) + BitVec.ofNat 32 (ta15_5_1.header + ta15_5_1.len)) ((BitVec.ofNat 32 (tl6_5_1.len)) - BitVec.ofNat 32 (ta15_5_1.header + ta15_5_1.len)).toNat) ((((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))) + BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)) + BitVec.ofNat 32 (tl13_4_1.header + tl13_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) + BitVec.ofNat 32 tl6_5_1.header) + BitVec.ofNat 32 (ta15_5_1.header + ta15_5_1.len)) (.ok tl35_5_1) = .ok (bp35_5_1, bl35_5_1) ∧
      (bl35_5_1 = BitVec.ofNat 32 0x41) ∧
      (((BitVec.ofNat 32 (tl6_5_1.len)) - BitVec.ofNat 32 (ta15_5_1.header + ta15_5_1.len)) - BitVec.ofNat 32 (tl35_5_1.header + tl35_5_1.len) = 0) ∧
      (M0 bp35_5_1 = BitVec.ofNat 8 4) ∧
      (GsOk M0 bp35_5_1) ∧
      ∃ tl9_6_1, derOptRes 0xA3 (memBytes M0 ((((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))) + BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)) + BitVec.ofNat 32 (tl13_4_1.header + tl13_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) + BitVec.ofNat 32 (tl6_5_1.header + tl6_5_1.len))) ((((((((((((BitVec.ofNat 32 tl1_2_1.len) - BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) - BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) - BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))) - BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)) - BitVec.ofNat 32 (tl13_4_1.header + tl13_4_1.len))) - BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) - BitVec.ofNat 32 (tl6_5_1.header + tl6_5_1.len))).toNat) = some (.ok tl9_6_1) ∧
      (((((((((((((BitVec.ofNat 32 tl1_2_1.len) - BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) - BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) - BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))) - BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)) - BitVec.ofNat 32 (tl13_4_1.header + tl13_4_1.len))) - BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) - BitVec.ofNat 32 (tl6_5_1.header + tl6_5_1.len))) - BitVec.ofNat 32 (tl9_6_1.header + tl9_6_1.len) = 0) ∧
      ∃ tl25_6_1, derElement 0x30 (memBytes M0 (((((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))) + BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)) + BitVec.ofNat 32 (tl13_4_1.header + tl13_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) + BitVec.ofNat 32 (tl6_5_1.header + tl6_5_1.len))) + BitVec.ofNat 32 tl9_6_1.header) (BitVec.ofNat 32 tl9_6_1.len).toNat) = .ok tl25_6_1 ∧
      ((BitVec.ofNat 32 tl9_6_1.len) - BitVec.ofNat 32 (tl25_6_1.header + tl25_6_1.len) = 0) ∧
      ∃ u0 u1 u2, ∃ k_2 f30'_2 f34'_2 rem'_2 cur'_2 sl0'_2 sl1'_2 sl2'_2 sl3'_2 sl4'_2 sl5'_2 sl6'_2 sl7'_2 sl8'_2 sl9'_2, svChain (sv_extStep B out bp (lp + BitVec.ofNat 32 t_1_1.header) bp35_5_1 (BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)) ll ((((((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))) + BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)) + BitVec.ofNat 32 (tl13_4_1.header + tl13_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) + BitVec.ofNat 32 (tl6_5_1.header + tl6_5_1.len))) + BitVec.ofNat 32 tl9_6_1.header) + BitVec.ofNat 32 tl25_6_1.header) (BitVec.ofNat 32 tl25_6_1.len) (BitVec.ofNat 32 (tm31_4_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm31_4_1 % 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1 / 2 ^ 32)) (BitVec.ofNat 32 (tm22_4_1 % 2 ^ 32)) (((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len)) (((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) (BitVec.ofNat 32 (tl8_2_1.header + tl8_2_1.len)) bl16_2_1 lp ((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) (BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len)) (BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) bp16_2_1 rootp dg v M0) k_2 ((BitVec.ofNat 32 0x0), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 tl25_6_1.len), ((((((((((((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len))) + BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)) + BitVec.ofNat 32 (tl13_4_1.header + tl13_4_1.len))) + BitVec.ofNat 32 (tl2_5_1.header + tl2_5_1.len)) + BitVec.ofNat 32 (tl6_5_1.header + tl6_5_1.len))) + BitVec.ofNat 32 tl9_6_1.header) + BitVec.ofNat 32 tl25_6_1.header), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 tl25_6_1.len), (BitVec.ofNat 32 0x0), (BitVec.ofNat 32 (tl25_6_1.header + tl25_6_1.len)), (BitVec.ofNat 32 0x0), (u0), (BitVec.ofNat 32 0x0), (u1), (BitVec.ofNat 32 0x0), (u2)) (f30'_2, f34'_2, rem'_2, cur'_2, sl0'_2, sl1'_2, sl2'_2, sl3'_2, sl4'_2, sl5'_2, sl6'_2, sl7'_2, sl8'_2, sl9'_2) ∧
      rem'_2 = 0 ∧ (sl0'_2 = 0 ∨ SvIn B sl0'_2 sl1'_2.toNat) ∧ (sl2'_2 = 0 ∨ SvIn B sl2'_2 sl3'_2.toNat) ∧ (sl4'_2 = 0 ∨ SvIn B sl4'_2 sl5'_2.toNat) ∧ (sl6'_2 = 0 ∨ SvIn B sl6'_2 sl7'_2.toNat) ∧ (sl8'_2 = 0 ∨ SvIn B sl8'_2 sl9'_2.toNat) ∧
      (sl0'_2 ≠ 0) ∧ (sl2'_2 ≠ 0) ∧ (sl4'_2 ≠ 0) ∧ (sl6'_2 ≠ 0) ∧ ((if BitVec.ult 0 (sl8'_2) then (1 : Word) else 0) &&& ((f30'_2) &&& (f34'_2)) ≠ 0) ∧ (memBytes M0 (((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) ((BitVec.ofNat 32 (tl8_2_1.header + tl8_2_1.len)).toNat) = memBytes M0 ((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) ((BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len)).toNat)) ∧ ∃ sr43_2 ss43_2, ecdsaSigOf 48 M0 (bp16_2_1) ((bl16_2_1.toNat)) = .ok (sr43_2, ss43_2) ∧
      ∃ k_4, k_4 < 4 ∧
      (∀ i, i < k_4 → ∀ c'_4 q'_4, (c'_4, q'_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x80), ((rootp) + BitVec.ofNat 32 0x3C)) → ¬ (memBytes M0 (memLoad32 M0 (q'_4 + 0xFFFFFFFC)) (memLoad32 M0 (q'_4 + 0x0)).toNat = memBytes M0 (((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len)) (BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)).toNat)) ∧
      ∃ c'_4 q'_4, (c'_4, q'_4) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) k_4 ((BitVec.ofNat 32 0x80), ((rootp) + BitVec.ofNat 32 0x3C)) ∧ (memBytes M0 (memLoad32 M0 (q'_4 + 0xFFFFFFFC)) (memLoad32 M0 (q'_4 + 0x0)).toNat = memBytes M0 (((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len)) (BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)).toNat) ∧
      ((memLoad32 M0 (q'_4 + 0xFFFFFFFC)) ≠ 0) ∧
      ∃ pv_5, SvPvRes M0 (memLoad32 M0 (((q'_4) + BitVec.ofNat 32 0x20) + 0xFFFFFFF4)) (B + 0x21A0 + BitVec.ofNat 32 0x1020) 48 (sha384 (memBytes M0 (lp + BitVec.ofNat 32 t_1_1.header) (BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)).toNat)) (B + 0x21A0 + BitVec.ofNat 32 0xD0) (B + 0x21A0 + BitVec.ofNat 32 0x100) sr43_2 ss43_2 (some pv_5) ∧
      (pv_5 ≠ 0) ∧
      (memBytes M0 sl0'_2 sl1'_2.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x0)) (memLoad32 M0 (rootp + 0x4)).toNat) ∧
      (memBytes M0 sl2'_2 sl3'_2.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x8)) (memLoad32 M0 (rootp + 0xC)).toNat) ∧
      (memBytes M0 sl4'_2 sl5'_2.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x10)) (memLoad32 M0 (rootp + 0x14)).toNat) ∧
      (memBytes M0 sl6'_2 sl7'_2.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x18)) (memLoad32 M0 (rootp + 0x1C)).toNat) ∧
      (memBytes M0 sl8'_2 sl9'_2.toNat = memBytes M0 (memLoad32 M0 (rootp + 0x20)) (memLoad32 M0 (rootp + 0x24)).toNat) ∧
      ∃ tl49_1_6, derElement 0x30 (memBytes M0 ((memLoad32 M0 (bp + 0x8))) ((memLoad32 M0 (bp + 0xC))).toNat) = .ok tl49_1_6 ∧
      (((memLoad32 M0 (bp + 0xC))) - BitVec.ofNat 32 (tl49_1_6.header + tl49_1_6.len) = 0) ∧
      ∃ bs9_2_6, derScalarOf 32 (memBytes M0 (((memLoad32 M0 (bp + 0x8))) + BitVec.ofNat 32 tl49_1_6.header) (BitVec.ofNat 32 tl49_1_6.len).toNat) (((memLoad32 M0 (bp + 0x8))) + BitVec.ofNat 32 tl49_1_6.header) (derElement 2 (memBytes M0 (((memLoad32 M0 (bp + 0x8))) + BitVec.ofNat 32 tl49_1_6.header) (BitVec.ofNat 32 tl49_1_6.len).toNat)) = .ok bs9_2_6 ∧
      ∃ te9_2_6, derElement 2 (memBytes M0 (((memLoad32 M0 (bp + 0x8))) + BitVec.ofNat 32 tl49_1_6.header) (BitVec.ofNat 32 tl49_1_6.len).toNat) = .ok te9_2_6 ∧
      ∃ bs16_2_6, derScalarOf 32 (memBytes M0 ((((memLoad32 M0 (bp + 0x8))) + BitVec.ofNat 32 tl49_1_6.header) + BitVec.ofNat 32 (te9_2_6.header + te9_2_6.len)) ((BitVec.ofNat 32 tl49_1_6.len) - BitVec.ofNat 32 (te9_2_6.header + te9_2_6.len)).toNat) ((((memLoad32 M0 (bp + 0x8))) + BitVec.ofNat 32 tl49_1_6.header) + BitVec.ofNat 32 (te9_2_6.header + te9_2_6.len)) (derElement 2 (memBytes M0 ((((memLoad32 M0 (bp + 0x8))) + BitVec.ofNat 32 tl49_1_6.header) + BitVec.ofNat 32 (te9_2_6.header + te9_2_6.len)) ((BitVec.ofNat 32 tl49_1_6.len) - BitVec.ofNat 32 (te9_2_6.header + te9_2_6.len)).toNat)) = .ok bs16_2_6 ∧
      ∃ te16_2_6, derElement 2 (memBytes M0 ((((memLoad32 M0 (bp + 0x8))) + BitVec.ofNat 32 tl49_1_6.header) + BitVec.ofNat 32 (te9_2_6.header + te9_2_6.len)) ((BitVec.ofNat 32 tl49_1_6.len) - BitVec.ofNat 32 (te9_2_6.header + te9_2_6.len)).toNat) = .ok te16_2_6 ∧
      (((BitVec.ofNat 32 tl49_1_6.len) - BitVec.ofNat 32 (te9_2_6.header + te9_2_6.len)) - BitVec.ofNat 32 (te16_2_6.header + te16_2_6.len) = 0) ∧
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0xFBA (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 0x1 ∧
        reg n' (9 : Fin 32) = (BitVec.ofNat 8 ((bs16_2_6).getD 0 0)).zeroExtend 32 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 ∧
        reg n' (21 : Fin 32) = bp35_5_1 ∧
        reg n' (22 : Fin 32) = (BitVec.ofNat 8 ((bs9_2_6).getD 0 0)).zeroExtend 32 ∧
        reg n' (26 : Fin 32) = ll ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (BitVec.ofNat 32 (tm31_4_1 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = (BitVec.ofNat 32 (tm31_4_1 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = (BitVec.ofNat 32 (tm22_4_1 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = (BitVec.ofNat 32 (tm22_4_1 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = (((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = (((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = (memLoad32 M0 (bp + 0xC)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = (memLoad32 M0 (bp + 0x8)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = ((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = ((q'_4) + BitVec.ofNat 32 0x20) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (lp + BitVec.ofNat 32 t_1_1.header) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = (BitVec.ofNat 32 (tl1_2_1.header + tl1_2_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = (((((((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header) + BitVec.ofNat 32 (tl29_2_1.header + tl29_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl9_3_1.header + tl9_3_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = (BitVec.ofNat 32 (tl6_4_1.header + tl6_4_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl0'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl1'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl2'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl3'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = sl4'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = sl5'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = sl6'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = sl7'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = sl8'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = sl9'_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = (BitVec.ofNat 32 (tm22_4_1 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = (BitVec.ofNat 32 (tm22_4_1 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = (BitVec.ofNat 32 (tm31_4_1 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = (BitVec.ofNat 32 (tm31_4_1 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = bp35_5_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x320) = ((memLoad32 M0 (bp + 0x8))) + BitVec.ofNat 32 tl49_1_6.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x324) = BitVec.ofNat 32 tl49_1_6.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x328) = ((((memLoad32 M0 (bp + 0x8))) + BitVec.ofNat 32 tl49_1_6.header) + BitVec.ofNat 32 (te9_2_6.header + te9_2_6.len)) + BitVec.ofNat 32 (te16_2_6.header + te16_2_6.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x32C) = ((BitVec.ofNat 32 tl49_1_6.len) - BitVec.ofNat 32 (te9_2_6.header + te9_2_6.len)) - BitVec.ofNat 32 (te16_2_6.header + te16_2_6.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = (memLoad32 M0 (bp + 0x8)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = (memLoad32 M0 (bp + 0xC)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = ((memLoad32 M0 (bp + 0x8))) + BitVec.ofNat 32 (tl49_1_6.header + tl49_1_6.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = ((memLoad32 M0 (bp + 0xC))) - BitVec.ofNat 32 (tl49_1_6.header + tl49_1_6.len) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x138) = BitVec.ofNat 8 ((bs9_2_6).getD 0 0) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = BitVec.ofNat 8 ((bs16_2_6).getD 0 0) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = (0 : BitVec 8) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA21) = BitVec.ofNat 8 ((bs16_2_6).getD 0 0) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x139 + j)) = BitVec.ofNat 8 ((bs9_2_6).getD (1 + j) 0)) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x159 + j)) = BitVec.ofNat 8 ((bs16_2_6).getD (1 + j) 0)) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x420 + j)) = BitVec.ofNat 8 ((bs16_2_6).getD (1 + j) 0)) ∧
        (∀ j, j < 32 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 ((bs16_2_6).getD j 0)) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + j)) = BitVec.ofNat 8 ((bs9_2_6).getD (1 + j) 0)) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1380 + j)) = BitVec.ofNat 8 ((bs16_2_6).getD (1 + j) 0)) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1480 + j)) = BitVec.ofNat 8 ((bs9_2_6).getD (1 + j) 0)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = lp + BitVec.ofNat 32 (t_1_1.header + t_1_1.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = ll - BitVec.ofNat 32 (t_1_1.header + t_1_1.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) = lp + BitVec.ofNat 32 t_1_1.header ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158C) = (BitVec.ofNat 32 t_1_1.len).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158D) = (BitVec.ofNat 32 t_1_1.len).extractLsb' 8 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158E) = (BitVec.ofNat 32 t_1_1.len).extractLsb' 16 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158F) = (BitVec.ofNat 32 t_1_1.len).extractLsb' 24 8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = ((lp + BitVec.ofNat 32 t_1_1.header)) + BitVec.ofNat 32 tl1_2_1.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1_2_1.len ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr43_2.getD 0 0) ∧
        SvKeepL B n0.mem n'.mem [(0xA20, 0x10), (0x2E8, 0x8), (0x158D, 0xB), (0x1588, 0x4), (0x158C, 0x1), (0xA20, 0x11), (0x1590, 0x8), (0xA20, 0x11), (0x1590, 0x8), (0x80, 0x4), (0x84, 0x4), (0xA20, 0x8), (0x1590, 0x8), (0x7C, 0x4), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0xA20, 0x18), (0x180, 0x8), (0x78, 0x4), (0x200, 0x4), (0x204, 0x4), (0x208, 0x4), (0x20C, 0x4), (0x208, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4), (0x68, 0x4), (0x64, 0x4), (0x60, 0x4), (0x6C, 0x4), (0x5C, 0x4), (0x245, 0xB), (0x240, 0x4), (0x244, 0x1), (0x248, 0x8), (0x58, 0x4), (0x54, 0x4), (0x248, 0x8), (0x50, 0x4), (0x4C, 0x4), (0x1025, 0xB), (0x1024, 0x1), (0xA20, 0x48), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1328, 0x8), (0x88, 0x4), (0x8C, 0x4), (0x90, 0x4), (0x40, 0x4), (0x94, 0x4), (0xA20, 0x4), (0xA28, 0x4), (0xA30, 0x4), (0xA38, 0x4), (0xA40, 0x4), (0x34, 0x4), (0x30, 0x4), (0x1020, 0x10), (0x90, 0x8), (0x44, 0x4), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x1020, 0x8), (0x328, 0x8), (0x48, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0x1380, 0x4), (0x1384, 0x4), (0x1388, 0x4), (0x138C, 0x4), (0x1388, 0x8), (0x1485, 0xB), (0x1484, 0x1), (0xA24, 0x4), (0xA2C, 0x4), (0xA34, 0x4), (0xA3C, 0x4), (0xA44, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4), (0xA20, 0x61), (0x420, 0x5F), (0x8D, 0x1), (0x8E, 0x1), (0x8F, 0x1), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0xA8, 0x4), (0xAC, 0x4), (0xB0, 0x4), (0xB4, 0x4), (0xB8, 0x4), (0xBC, 0x4), (0xD0, 0x1), (0xD1, 0x5F), (0x8C, 0x1), (0xC0, 0x4), (0xC4, 0x4), (0xC8, 0x4), (0xCC, 0x4), (0x130, 0x4), (0x74, 0x8), (0x420, 0xD0), (0xA20, 0xD0), (0x1020, 0x40), (0x1480, 0x30), (0xA20, 0x21), (0x1020, 0x1F), (0xA20, 0x21), (0x420, 0x1F), (0x1480, 0x1F), (0x1380, 0x1F), (0x139, 0x1F), (0x159, 0x1F), (0x138, 0x1), (0x158, 0x1)]) := by
  rcases sv_seg_leaf F E0 V0 hret hO s0 M0 fM g0_2 g0_10 g0_11 g0_18 g0_19 g0_21 g0_22 g0_25 g0_26 g0_27 w0_2e0 w0_2e4 w0_2e8 w0_2ec lc_in D0 with e | hx1
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
  obtain ⟨tl29_2_1, hx1⟩ := hx1
  obtain ⟨x1_7, hx1⟩ := hx1
  obtain ⟨x1_8, hx1⟩ := hx1
  obtain ⟨te43_2_1, hx1⟩ := hx1
  obtain ⟨x1_9, hx1⟩ := hx1
  obtain ⟨x1_10, hx1⟩ := hx1
  obtain ⟨tl2_3_1, hx1⟩ := hx1
  obtain ⟨x1_11, hx1⟩ := hx1
  obtain ⟨ip2_3_1, hx1⟩ := hx1
  obtain ⟨il2_3_1, hx1⟩ := hx1
  obtain ⟨x1_12, hx1⟩ := hx1
  obtain ⟨x1_13, hx1⟩ := hx1
  obtain ⟨tl9_3_1, hx1⟩ := hx1
  obtain ⟨x1_14, hx1⟩ := hx1
  obtain ⟨op19_3_1, hx1⟩ := hx1
  obtain ⟨ol19_3_1, hx1⟩ := hx1
  obtain ⟨x1_15, hx1⟩ := hx1
  obtain ⟨x1_16, hx1⟩ := hx1
  obtain ⟨tl6_4_1, hx1⟩ := hx1
  obtain ⟨x1_17, hx1⟩ := hx1
  obtain ⟨tl13_4_1, hx1⟩ := hx1
  obtain ⟨x1_18, hx1⟩ := hx1
  obtain ⟨tm22_4_1, hx1⟩ := hx1
  obtain ⟨rs22_4_1, hx1⟩ := hx1
  obtain ⟨x1_19, hx1⟩ := hx1
  obtain ⟨tm31_4_1, hx1⟩ := hx1
  obtain ⟨rs31_4_1, hx1⟩ := hx1
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
  obtain ⟨tl25_6_1, hx1⟩ := hx1
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
  obtain ⟨w1_30, hx1⟩ := hx1
  obtain ⟨w1_34, hx1⟩ := hx1
  obtain ⟨w1_40, hx1⟩ := hx1
  obtain ⟨w1_88, hx1⟩ := hx1
  obtain ⟨w1_8c, hx1⟩ := hx1
  obtain ⟨w1_90, hx1⟩ := hx1
  obtain ⟨w1_94, hx1⟩ := hx1
  obtain ⟨w1_a20, hx1⟩ := hx1
  obtain ⟨w1_a24, hx1⟩ := hx1
  obtain ⟨w1_a28, hx1⟩ := hx1
  obtain ⟨w1_a2c, hx1⟩ := hx1
  obtain ⟨w1_a30, hx1⟩ := hx1
  obtain ⟨w1_a38, hx1⟩ := hx1
  obtain ⟨w1_a40, hx1⟩ := hx1
  obtain ⟨w1_2e0, hx1⟩ := hx1
  obtain ⟨w1_2e4, hx1⟩ := hx1
  obtain ⟨w1_2e8, hx1⟩ := hx1
  obtain ⟨w1_2ec, hx1⟩ := hx1
  obtain ⟨w1_1588, hx1⟩ := hx1
  obtain ⟨b1_158c, hx1⟩ := hx1
  obtain ⟨b1_158d, hx1⟩ := hx1
  obtain ⟨b1_158e, hx1⟩ := hx1
  obtain ⟨b1_158f, hx1⟩ := hx1
  obtain ⟨w1_78, hx1⟩ := hx1
  obtain ⟨w1_7c, hx1⟩ := hx1
  obtain ⟨w1_80, hx1⟩ := hx1
  obtain ⟨w1_84, hx1⟩ := hx1
  obtain ⟨w1_178, hx1⟩ := hx1
  obtain ⟨w1_17c, hx1⟩ := hx1
  obtain ⟨w1_70, hx1⟩ := hx1
  obtain ⟨w1_74, hx1⟩ := hx1
  obtain ⟨w1_4c, hx1⟩ := hx1
  obtain ⟨w1_50, hx1⟩ := hx1
  obtain ⟨w1_54, hx1⟩ := hx1
  obtain ⟨w1_58, hx1⟩ := hx1
  obtain ⟨w1_5c, hx1⟩ := hx1
  obtain ⟨w1_60, hx1⟩ := hx1
  obtain ⟨w1_64, hx1⟩ := hx1
  obtain ⟨w1_68, hx1⟩ := hx1
  obtain ⟨w1_6c, hx1⟩ := hx1
  have K1_L := hx1
  rcases sv_extloop_st F hret hO M0 (Nat.le_refl _) E1 V1 s1 fR1 r1_2 r1_9 r1_18 r1_19 r1_21 r1_25 r1_26 r1_27 w1_30 w1_34 w1_40 w1_4c w1_50 w1_54 w1_58 w1_5c w1_60 w1_64 w1_68 w1_6c w1_70 w1_74 w1_78 w1_7c w1_80 w1_84 w1_88 w1_8c w1_90 w1_94 w1_a20 w1_a24 w1_a28 w1_a2c w1_a30 rfl w1_a38 rfl w1_a40 rfl ((((((((((((((((lc_in).content x1_0).ofNatLen).content x1_2).ofNatLen).restW (opt_ok_elem x1_7)).restW x1_11).restW x1_14).restW x1_17).restW x1_18).restW x1_22).restW x1_23).content (opt_ok_elem x1_35)).ofNatLen).content x1_37).ofNatLen) SD0 (.inl rfl) (.inl rfl) (.inl rfl) (.inl rfl) (.inl rfl) ((((((((((((((((lc_in).content x1_0).ofNatLen).content x1_2).ofNatLen).restW (opt_ok_elem x1_7)).restW x1_11).restW x1_14).restW x1_17).restW x1_18).restW x1_22).restW x1_23).content (opt_ok_elem x1_35)).ofNatLen).content x1_37).ofNatLen) (((((lc_in).content x1_0).ofNatLen).restW x1_2).rawW x1_3) ((((((((lc_in).content x1_0).ofNatLen).content x1_2).ofNatLen).restW (opt_ok_elem x1_7)).restW x1_11).rawW x1_14) (SvIn.bitsW (((((lc_in).content x1_0).ofNatLen).restW x1_2).restW x1_3) x1_4 x1_5) with e | hx2
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  obtain ⟨k_2, hx2⟩ := hx2
  obtain ⟨f30'_2, hx2⟩ := hx2
  obtain ⟨f34'_2, hx2⟩ := hx2
  obtain ⟨rem'_2, hx2⟩ := hx2
  obtain ⟨cur'_2, hx2⟩ := hx2
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
  obtain ⟨sr43_2, hx2⟩ := hx2
  obtain ⟨ss43_2, hx2⟩ := hx2
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
  obtain ⟨r2_9, hx2⟩ := hx2
  obtain ⟨r2_18, hx2⟩ := hx2
  obtain ⟨r2_19, hx2⟩ := hx2
  obtain ⟨r2_20, hx2⟩ := hx2
  obtain ⟨r2_21, hx2⟩ := hx2
  obtain ⟨r2_25, hx2⟩ := hx2
  obtain ⟨r2_26, hx2⟩ := hx2
  obtain ⟨r2_27, hx2⟩ := hx2
  obtain ⟨w2_24, hx2⟩ := hx2
  obtain ⟨w2_28, hx2⟩ := hx2
  obtain ⟨w2_2c, hx2⟩ := hx2
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
  obtain ⟨w2_80, hx2⟩ := hx2
  obtain ⟨w2_84, hx2⟩ := hx2
  obtain ⟨w2_88, hx2⟩ := hx2
  obtain ⟨w2_8c, hx2⟩ := hx2
  obtain ⟨w2_90, hx2⟩ := hx2
  obtain ⟨w2_94, hx2⟩ := hx2
  obtain ⟨q2_a21, hx2⟩ := hx2
  obtain ⟨q2_a51, hx2⟩ := hx2
  have K2_L := hx2
  rcases sv_l8a F E2 V2 hret hO s2 M0 fR2 r2_2 r2_9 r2_18 r2_19 r2_20 r2_21 r2_25 r2_26 r2_27 w2_24 w2_28 w2_2c w2_30 w2_34 w2_38 w2_3c w2_40 w2_44 w2_48 w2_4c w2_50 w2_54 w2_58 w2_5c w2_60 w2_64 w2_68 w2_6c w2_70 w2_74 w2_78 w2_7c w2_80 w2_84 q2_a21 q2_a51 with ⟨-, e⟩ | hx3
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
  obtain ⟨r3_9, hx3⟩ := hx3
  obtain ⟨r3_18, hx3⟩ := hx3
  obtain ⟨r3_19, hx3⟩ := hx3
  obtain ⟨r3_20, hx3⟩ := hx3
  obtain ⟨r3_21, hx3⟩ := hx3
  obtain ⟨r3_24, hx3⟩ := hx3
  obtain ⟨r3_25, hx3⟩ := hx3
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
  obtain ⟨w3_c8, hx3⟩ := hx3
  obtain ⟨w3_cc, hx3⟩ := hx3
  obtain ⟨w3_130, hx3⟩ := hx3
  obtain ⟨b3_d0, hx3⟩ := hx3
  obtain ⟨q3_d1, hx3⟩ := hx3
  obtain ⟨q3_100, hx3⟩ := hx3
  obtain ⟨q3_420, hx3⟩ := hx3
  obtain ⟨q3_44f, hx3⟩ := hx3
  obtain ⟨q3_a21, hx3⟩ := hx3
  obtain ⟨q3_a51, hx3⟩ := hx3
  have K3_L := hx3
  rcases sv_isearch_st F hret hO M0 (fun _ _ h => svCnt_zero Prod.fst (BitVec.ofNat 32 0x80) 0xFFFFFFE0 (by intro _; rfl) rfl (by decide) (congrArg Prod.fst h)) E3 V3 s3 fR3 r3_2 r3_9 r3_18 r3_19 r3_20 r3_21 r3_25 r3_26 r3_27 w3_24 w3_28 w3_2c w3_30 w3_34 w3_38 w3_3c w3_40 w3_44 w3_48 w3_4c w3_50 w3_54 w3_58 w3_5c w3_60 w3_64 w3_68 w3_6c w3_70 w3_74 w3_78 w3_7c w3_80 w3_84 w3_88 w3_8c w3_90 w3_94 w3_98 w3_9c w3_a0 w3_a4 w3_a8 w3_ac w3_b0 w3_b4 w3_b8 w3_bc w3_c0 w3_c4 w3_c8 w3_cc w3_130 b3_d0 q3_d1 q3_100 (fun i hi c'_4 q'_4 h => ⟨(svCnt_ne Prod.fst (BitVec.ofNat 32 0x80) 0xFFFFFFE0 (by intro _; rfl) rfl (by decide) hi (congrArg Prod.fst h)), (H' i hi c'_4 q'_4 h).1, (H' i hi c'_4 q'_4 h).2.1, (H' i hi c'_4 q'_4 h).2.2.1, (H' i hi c'_4 q'_4 h).2.2.2.1, (H' i hi c'_4 q'_4 h).2.2.2.2, (((((((((lc_in).content x1_0).ofNatLen).content x1_2).ofNatLen).restW (opt_ok_elem x1_7)).restW x1_11).restW x1_14).rawW x1_17)⟩) with e | hx4
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
  obtain ⟨r4_21, hx4⟩ := hx4
  obtain ⟨r4_22, hx4⟩ := hx4
  obtain ⟨r4_23, hx4⟩ := hx4
  obtain ⟨r4_25, hx4⟩ := hx4
  obtain ⟨r4_26, hx4⟩ := hx4
  obtain ⟨r4_27, hx4⟩ := hx4
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
  obtain ⟨w4_130, hx4⟩ := hx4
  obtain ⟨b4_d0, hx4⟩ := hx4
  obtain ⟨q4_d1, hx4⟩ := hx4
  obtain ⟨q4_100, hx4⟩ := hx4
  have K4_L := hx4
  rcases sv_lh F E4 V4 hret hO s4 M0 fR4 r4_2 r4_9 r4_18 r4_19 r4_21 r4_26 r4_27 w4_7c w4_8c b4_d0 q4_d1 q4_100 SH0 KS ((((lc_in).content x1_0).ofNatLen).rawW x1_2) PE0 rfl (pkp_in k_4 x4_0 c'_4 q'_4 x4_2 x4_4) (apk k_4 x4_0 c'_4 q'_4 x4_2 x4_4) (pk_in k_4 x4_0 c'_4 q'_4 x4_2 x4_4) (side k_4 x4_0 c'_4 q'_4 x4_2 x4_4) with ⟨-, e⟩ | hx5
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
  obtain ⟨r5_21, hx5⟩ := hx5
  obtain ⟨r5_26, hx5⟩ := hx5
  obtain ⟨r5_27, hx5⟩ := hx5
  obtain ⟨mb5_1020, hx5⟩ := hx5
  have K5_L := hx5
  rcases sv_seg_dpv F E5 V5 hret hO s5 M0 fR5 r5_2 r5_a0 r5_18 r5_19 r5_21 r5_26 r5_27 ((K5_L.w32 (by decide) (by decide)).trans w4_24) ((K5_L.w32 (by decide) (by decide)).trans w4_28) ((K5_L.w32 (by decide) (by decide)).trans w4_2c) ((K5_L.w32 (by decide) (by decide)).trans w4_30) ((K5_L.w32 (by decide) (by decide)).trans w4_34) ((K5_L.w32 (by decide) (by decide)).trans w4_38) ((K5_L.w32 (by decide) (by decide)).trans w4_3c) ((K5_L.w32 (by decide) (by decide)).trans w4_40) ((K5_L.w32 (by decide) (by decide)).trans w4_44) ((K5_L.w32 (by decide) (by decide)).trans w4_48) ((K5_L.w32 (by decide) (by decide)).trans w4_4c) ((K5_L.w32 (by decide) (by decide)).trans w4_50) ((K5_L.w32 (by decide) (by decide)).trans w4_54) ((K5_L.w32 (by decide) (by decide)).trans w4_58) ((K5_L.w32 (by decide) (by decide)).trans w4_5c) ((K5_L.w32 (by decide) (by decide)).trans w4_60) ((K5_L.w32 (by decide) (by decide)).trans w4_64) ((K5_L.w32 (by decide) (by decide)).trans w4_68) ((K5_L.w32 (by decide) (by decide)).trans w4_6c) ((K5_L.w32 (by decide) (by decide)).trans w4_70) ((K5_L.w32 (by decide) (by decide)).trans w4_7c) ((K5_L.w32 (by decide) (by decide)).trans w4_80) ((K5_L.w32 (by decide) (by decide)).trans w4_84) ((K5_L.w32 (by decide) (by decide)).trans w4_88) ((K5_L.w32 (by decide) (by decide)).trans w4_8c) ((K5_L.w32 (by decide) (by decide)).trans w4_90) ((K5_L.w32 (by decide) (by decide)).trans w4_94) ((K5_L.w32 (by decide) (by decide)).trans w4_98) ((K5_L.w32 (by decide) (by decide)).trans w4_9c) ((K5_L.w32 (by decide) (by decide)).trans w4_a0) ((K5_L.w32 (by decide) (by decide)).trans w4_a4) ((K5_L.w32 (by decide) (by decide)).trans w4_a8) ((K5_L.w32 (by decide) (by decide)).trans w4_ac) ((K5_L.w32 (by decide) (by decide)).trans w4_b0) ((K5_L.w32 (by decide) (by decide)).trans w4_b4) ((K5_L.w32 (by decide) (by decide)).trans w4_b8) ((K5_L.w32 (by decide) (by decide)).trans w4_bc) ((K5_L.w32 (by decide) (by decide)).trans w4_c0) ((K5_L.w32 (by decide) (by decide)).trans w4_c4) ((K5_L.w32 (by decide) (by decide)).trans w4_c8) ((K5_L.w32 (by decide) (by decide)).trans w4_cc) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl ((K5_L.w32 (by decide) (by decide)).trans w4_130) ts_in rfl rfl he0p_in he0l_in ae0p ae0l (.inl ((x2_2.resolve_left x2_7))) e0_in rfl rfl he1p_in he1l_in ae1p ae1l (.inl ((x2_3.resolve_left x2_8))) e1_in rfl rfl he2p_in he2l_in ae2p ae2l (.inl ((x2_4.resolve_left x2_9))) e2_in rfl rfl he3p_in he3l_in ae3p ae3l (.inl ((x2_5.resolve_left x2_10))) e3_in rfl rfl he4p_in he4l_in ae4p ae4l (.inl ((x2_6.resolve_left (fun hx => x2_11 (by rw [hx]; exact BitVec.zero_and))))) e4_in rfl rfl htsp_in htsl_in atsp atsl with e | hx6
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5))))) (by rw [r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR5 x hx).trans (fM x hx).symm) e)
  obtain ⟨x6_0, hx6⟩ := hx6
  obtain ⟨x6_1, hx6⟩ := hx6
  obtain ⟨x6_2, hx6⟩ := hx6
  obtain ⟨x6_3, hx6⟩ := hx6
  obtain ⟨x6_4, hx6⟩ := hx6
  obtain ⟨x6_5, hx6⟩ := hx6
  obtain ⟨tl49_1_6, hx6⟩ := hx6
  obtain ⟨x6_6, hx6⟩ := hx6
  obtain ⟨x6_7, hx6⟩ := hx6
  obtain ⟨bs9_2_6, hx6⟩ := hx6
  obtain ⟨x6_8, hx6⟩ := hx6
  obtain ⟨te9_2_6, hx6⟩ := hx6
  obtain ⟨x6_9, hx6⟩ := hx6
  obtain ⟨bs16_2_6, hx6⟩ := hx6
  obtain ⟨x6_10, hx6⟩ := hx6
  obtain ⟨te16_2_6, hx6⟩ := hx6
  obtain ⟨x6_11, hx6⟩ := hx6
  obtain ⟨x6_12, hx6⟩ := hx6
  obtain ⟨n6, hx6⟩ := hx6
  obtain ⟨c6, hx6⟩ := hx6
  obtain ⟨fR6, hx6⟩ := hx6
  obtain ⟨s6, hx6⟩ := hx6
  obtain ⟨E6, hx6⟩ := hx6
  obtain ⟨V6, hx6⟩ := hx6
  obtain ⟨r6_3, hx6⟩ := hx6
  obtain ⟨r6_4, hx6⟩ := hx6
  obtain ⟨r6_2, hx6⟩ := hx6
  obtain ⟨r6_8, hx6⟩ := hx6
  obtain ⟨r6_9, hx6⟩ := hx6
  obtain ⟨r6_18, hx6⟩ := hx6
  obtain ⟨r6_19, hx6⟩ := hx6
  obtain ⟨r6_20, hx6⟩ := hx6
  obtain ⟨r6_21, hx6⟩ := hx6
  obtain ⟨r6_22, hx6⟩ := hx6
  obtain ⟨r6_26, hx6⟩ := hx6
  obtain ⟨r6_27, hx6⟩ := hx6
  obtain ⟨w6_24, hx6⟩ := hx6
  obtain ⟨w6_28, hx6⟩ := hx6
  obtain ⟨w6_2c, hx6⟩ := hx6
  obtain ⟨w6_30, hx6⟩ := hx6
  obtain ⟨w6_34, hx6⟩ := hx6
  obtain ⟨w6_38, hx6⟩ := hx6
  obtain ⟨w6_3c, hx6⟩ := hx6
  obtain ⟨w6_40, hx6⟩ := hx6
  obtain ⟨w6_44, hx6⟩ := hx6
  obtain ⟨w6_48, hx6⟩ := hx6
  obtain ⟨w6_4c, hx6⟩ := hx6
  obtain ⟨w6_50, hx6⟩ := hx6
  obtain ⟨w6_54, hx6⟩ := hx6
  obtain ⟨w6_58, hx6⟩ := hx6
  obtain ⟨w6_5c, hx6⟩ := hx6
  obtain ⟨w6_60, hx6⟩ := hx6
  obtain ⟨w6_64, hx6⟩ := hx6
  obtain ⟨w6_68, hx6⟩ := hx6
  obtain ⟨w6_6c, hx6⟩ := hx6
  obtain ⟨w6_70, hx6⟩ := hx6
  obtain ⟨w6_7c, hx6⟩ := hx6
  obtain ⟨w6_80, hx6⟩ := hx6
  obtain ⟨w6_84, hx6⟩ := hx6
  obtain ⟨w6_88, hx6⟩ := hx6
  obtain ⟨w6_8c, hx6⟩ := hx6
  obtain ⟨w6_90, hx6⟩ := hx6
  obtain ⟨w6_94, hx6⟩ := hx6
  obtain ⟨w6_98, hx6⟩ := hx6
  obtain ⟨w6_9c, hx6⟩ := hx6
  obtain ⟨w6_a0, hx6⟩ := hx6
  obtain ⟨w6_a4, hx6⟩ := hx6
  obtain ⟨w6_a8, hx6⟩ := hx6
  obtain ⟨w6_ac, hx6⟩ := hx6
  obtain ⟨w6_b0, hx6⟩ := hx6
  obtain ⟨w6_b4, hx6⟩ := hx6
  obtain ⟨w6_b8, hx6⟩ := hx6
  obtain ⟨w6_bc, hx6⟩ := hx6
  obtain ⟨w6_c0, hx6⟩ := hx6
  obtain ⟨w6_c4, hx6⟩ := hx6
  obtain ⟨w6_c8, hx6⟩ := hx6
  obtain ⟨w6_cc, hx6⟩ := hx6
  obtain ⟨w6_d0, hx6⟩ := hx6
  obtain ⟨w6_d4, hx6⟩ := hx6
  obtain ⟨w6_d8, hx6⟩ := hx6
  obtain ⟨w6_dc, hx6⟩ := hx6
  obtain ⟨w6_e0, hx6⟩ := hx6
  obtain ⟨w6_e4, hx6⟩ := hx6
  obtain ⟨w6_e8, hx6⟩ := hx6
  obtain ⟨w6_ec, hx6⟩ := hx6
  obtain ⟨w6_f0, hx6⟩ := hx6
  obtain ⟨w6_f4, hx6⟩ := hx6
  obtain ⟨w6_f8, hx6⟩ := hx6
  obtain ⟨w6_fc, hx6⟩ := hx6
  obtain ⟨w6_100, hx6⟩ := hx6
  obtain ⟨w6_104, hx6⟩ := hx6
  obtain ⟨w6_108, hx6⟩ := hx6
  obtain ⟨w6_10c, hx6⟩ := hx6
  obtain ⟨w6_110, hx6⟩ := hx6
  obtain ⟨w6_114, hx6⟩ := hx6
  obtain ⟨w6_118, hx6⟩ := hx6
  obtain ⟨w6_11c, hx6⟩ := hx6
  obtain ⟨w6_120, hx6⟩ := hx6
  obtain ⟨w6_124, hx6⟩ := hx6
  obtain ⟨w6_128, hx6⟩ := hx6
  obtain ⟨w6_12c, hx6⟩ := hx6
  obtain ⟨w6_130, hx6⟩ := hx6
  obtain ⟨w6_320, hx6⟩ := hx6
  obtain ⟨w6_324, hx6⟩ := hx6
  obtain ⟨w6_328, hx6⟩ := hx6
  obtain ⟨w6_32c, hx6⟩ := hx6
  obtain ⟨w6_1320, hx6⟩ := hx6
  obtain ⟨w6_1324, hx6⟩ := hx6
  obtain ⟨w6_1328, hx6⟩ := hx6
  obtain ⟨w6_132c, hx6⟩ := hx6
  obtain ⟨b6_138, hx6⟩ := hx6
  obtain ⟨b6_158, hx6⟩ := hx6
  obtain ⟨b6_a20, hx6⟩ := hx6
  obtain ⟨b6_a21, hx6⟩ := hx6
  obtain ⟨q6_139, hx6⟩ := hx6
  obtain ⟨q6_159, hx6⟩ := hx6
  obtain ⟨q6_420, hx6⟩ := hx6
  obtain ⟨q6_a21, hx6⟩ := hx6
  obtain ⟨q6_1020, hx6⟩ := hx6
  obtain ⟨q6_1380, hx6⟩ := hx6
  obtain ⟨q6_1480, hx6⟩ := hx6
  have K6_L := hx6
  exact .inr (.inr ⟨t_1_1, x1_0, x1_1, tl1_2_1, x1_2, tl8_2_1, x1_3, tl16_2_1, x1_4, bp16_2_1, bl16_2_1, x1_5, x1_6, tl29_2_1, x1_7, x1_8, te43_2_1, x1_9, x1_10, tl2_3_1, x1_11, ip2_3_1, il2_3_1, x1_12, x1_13, tl9_3_1, x1_14, op19_3_1, ol19_3_1, x1_15, x1_16, tl6_4_1, x1_17, tl13_4_1, x1_18, tm22_4_1, rs22_4_1, x1_19, tm31_4_1, rs31_4_1, x1_20, x1_21, tl2_5_1, x1_22, tl6_5_1, x1_23, op15_5_1, ol15_5_1, prp15_5_1, pu15_5_1, x1_24, ta15_5_1, x1_25, x1_26, x1_27, x1_28, tl35_5_1, x1_29, bp35_5_1, bl35_5_1, x1_30, x1_31, x1_32, x1_33, x1_34, tl9_6_1, x1_35, x1_36, tl25_6_1, x1_37, x1_38, (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C)), (memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44)), k_2, f30'_2, f34'_2, rem'_2, cur'_2, sl0'_2, sl1'_2, sl2'_2, sl3'_2, sl4'_2, sl5'_2, sl6'_2, sl7'_2, sl8'_2, sl9'_2, x2_0, x2_1, x2_2, x2_3, x2_4, x2_5, x2_6, x2_7, x2_8, x2_9, x2_10, x2_11, x2_12, sr43_2, ss43_2, x2_13, k_4, x4_0, x4_1, c'_4, q'_4, x4_2, x4_3, x4_4, pv_5, x5_0, x6_0, x6_1, x6_2, x6_3, x6_4, x6_5, tl49_1_6, x6_6, x6_7, bs9_2_6, x6_8, te9_2_6, x6_9, bs16_2_6, x6_10, te16_2_6, x6_11, x6_12, n6, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6))))), fR6, s6, E6, V6,
    by rw [r6_3, r5_3, r4_3, r3_3, r2_3, r1_3], by rw [r6_4, r5_4, r4_4, r3_4, r2_4, r1_4], r6_2, r6_8, r6_9, r6_18, r6_19, r6_20, r6_21, r6_22, r6_26, r6_27, w6_24, w6_28, w6_2c, w6_30, w6_34, w6_38, w6_3c, w6_40, w6_44, w6_48, w6_4c, w6_50, w6_54, w6_58, w6_5c, w6_60, w6_64, w6_68, w6_6c, w6_70, w6_7c, w6_80, w6_84, w6_88, w6_8c, w6_90, w6_94, w6_98, w6_9c, w6_a0, w6_a4, w6_a8, w6_ac, w6_b0, w6_b4, w6_b8, w6_bc, w6_c0, w6_c4, w6_c8, w6_cc, w6_130, w6_320, w6_324, w6_328, w6_32c, w6_1320, w6_1324, w6_1328, w6_132c, b6_138, b6_158, b6_a20, b6_a21, q6_139, q6_159, q6_420, q6_a21, q6_1020, q6_1380, q6_1480, ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_2e0))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_2e4))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_2e8))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_2ec))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_1588))))), ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans ((K4_L.b8 (by decide) (by decide)).trans ((K3_L.b8 (by decide) (by decide)).trans ((K2_L.b8 (by decide) (by decide)).trans b1_158c))))), ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans ((K4_L.b8 (by decide) (by decide)).trans ((K3_L.b8 (by decide) (by decide)).trans ((K2_L.b8 (by decide) (by decide)).trans b1_158d))))), ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans ((K4_L.b8 (by decide) (by decide)).trans ((K3_L.b8 (by decide) (by decide)).trans ((K2_L.b8 (by decide) (by decide)).trans b1_158e))))), ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans ((K4_L.b8 (by decide) (by decide)).trans ((K3_L.b8 (by decide) (by decide)).trans ((K2_L.b8 (by decide) (by decide)).trans b1_158f))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_178))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_17c))))), ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans b4_d0)), ((((((K1_L).trans K2_L).trans K3_L).trans K4_L).trans K5_L).trans K6_L).mono (by decide)⟩)

end C3.RV32.Sv
