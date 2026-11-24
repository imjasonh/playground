import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvL1
import C3BootProofs.Proofs.SvL2
import C3BootProofs.Proofs.SvL3
import C3BootProofs.Proofs.SvL4
import C3BootProofs.Proofs.SvL5
import C3BootProofs.Proofs.SvL6

/-!
# `sigstore::verify`: The leaf certificate up to its extensions

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **The leaf certificate up to its extensions**: from 0x72 to the extensions loop at 0x4EA, `sv_l1` to `sv_l6`. -/
theorem sv_seg_leaf {B out bp rootp dg lp ll : Word} {v : Nat → Word} {n0 : Machine}
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
    (D0 : P2Data M0) :
    SvErrRet B out v n0 ∨
    (∃ t_1, derElement 0x30 (memBytes M0 lp ll.toNat) = .ok t_1 ∧ ll - BitVec.ofNat 32 (t_1.header + t_1.len) = 0 ∧
      ∃ tl1_2, derElement 0x30 (memBytes M0 ((lp + BitVec.ofNat 32 t_1.header)) ((BitVec.ofNat 32 t_1.len)).toNat) = .ok tl1_2 ∧
      ∃ tl8_2, derElement 0x30 (memBytes M0 (((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 (tl1_2.header + tl1_2.len)) (((BitVec.ofNat 32 t_1.len)) - BitVec.ofNat 32 (tl1_2.header + tl1_2.len)).toNat) = .ok tl8_2 ∧
      ∃ tl16_2, derElement 3 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 (tl1_2.header + tl1_2.len)) + BitVec.ofNat 32 (tl8_2.header + tl8_2.len)) ((((BitVec.ofNat 32 t_1.len)) - BitVec.ofNat 32 (tl1_2.header + tl1_2.len)) - BitVec.ofNat 32 (tl8_2.header + tl8_2.len)).toNat) = .ok tl16_2 ∧
      ∃ bp16_2 bl16_2, derBitsOf (memBytes M0 ((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 (tl1_2.header + tl1_2.len)) + BitVec.ofNat 32 (tl8_2.header + tl8_2.len)) ((((BitVec.ofNat 32 t_1.len)) - BitVec.ofNat 32 (tl1_2.header + tl1_2.len)) - BitVec.ofNat 32 (tl8_2.header + tl8_2.len)).toNat) ((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 (tl1_2.header + tl1_2.len)) + BitVec.ofNat 32 (tl8_2.header + tl8_2.len)) (.ok tl16_2) = .ok (bp16_2, bl16_2) ∧
      (((((BitVec.ofNat 32 t_1.len)) - BitVec.ofNat 32 (tl1_2.header + tl1_2.len)) - BitVec.ofNat 32 (tl8_2.header + tl8_2.len)) - BitVec.ofNat 32 (tl16_2.header + tl16_2.len) = 0) ∧
      ∃ tl29_2, derOptRes 0xA0 (memBytes M0 (((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) (BitVec.ofNat 32 tl1_2.len).toNat) = some (.ok tl29_2) ∧
      derIntIsOf M0 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 tl29_2.header) (BitVec.ofNat 32 tl29_2.len).toNat) ((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 tl29_2.header) (derElement 2 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 tl29_2.header) (BitVec.ofNat 32 tl29_2.len).toNat)) ((BitVec.ofNat 32 0x2).extractLsb' 0 8) = .ok true ∧
      ∃ te43_2, derElement 2 (memBytes M0 ((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 tl29_2.header) (BitVec.ofNat 32 tl29_2.len).toNat) = .ok te43_2 ∧
      ((BitVec.ofNat 32 tl29_2.len) - BitVec.ofNat 32 (te43_2.header + te43_2.len) = 0) ∧
      ∃ tl2_3, derElement 2 (memBytes M0 (((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) (((BitVec.ofNat 32 tl1_2.len) - BitVec.ofNat 32 (tl29_2.header + tl29_2.len))).toNat) = .ok tl2_3 ∧
      ∃ ip2_3 il2_3, derPosIntOf (memBytes M0 (((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) (((BitVec.ofNat 32 tl1_2.len) - BitVec.ofNat 32 (tl29_2.header + tl29_2.len))).toNat) (((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) (.ok tl2_3) = .ok (ip2_3, il2_3) ∧
      ((il2_3).toNat ≤ 20) ∧
      ∃ tl9_3, derElement 0x30 (memBytes M0 ((((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) ((((BitVec.ofNat 32 tl1_2.len) - BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) - BitVec.ofNat 32 (tl2_3.header + tl2_3.len)).toNat) = .ok tl9_3 ∧
      ∃ op19_3 ol19_3, derAlgOf M0 ((((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) (tl9_3.header + tl9_3.len) = .ok ((op19_3, ol19_3), none) ∧
      (memBytes M0 op19_3 ol19_3 = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x28)) 8) ∧
      ∃ tl6_4, derElement 0x30 (memBytes M0 ((((((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl9_3.header + tl9_3.len))) ((((((BitVec.ofNat 32 tl1_2.len) - BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) - BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) - BitVec.ofNat 32 (tl9_3.header + tl9_3.len))).toNat) = .ok tl6_4 ∧
      ∃ tl13_4, derElement 0x30 (memBytes M0 (((((((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl9_3.header + tl9_3.len))) + BitVec.ofNat 32 (tl6_4.header + tl6_4.len)) (((((((BitVec.ofNat 32 tl1_2.len) - BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) - BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) - BitVec.ofNat 32 (tl9_3.header + tl9_3.len))) - BitVec.ofNat 32 (tl6_4.header + tl6_4.len)).toNat) = .ok tl13_4 ∧
      ∃ tm22_4 rs22_4, readTime (memBytes M0 ((((((((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl9_3.header + tl9_3.len))) + BitVec.ofNat 32 (tl6_4.header + tl6_4.len)) + BitVec.ofNat 32 tl13_4.header) (tl13_4.len)) = some (tm22_4, rs22_4) ∧
      ∃ tm31_4 rs31_4, readTime rs22_4 = some (tm31_4, rs31_4) ∧
      (rs31_4 = []) ∧
      ∃ tl2_5, derElement 0x30 (memBytes M0 (((((((((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl9_3.header + tl9_3.len))) + BitVec.ofNat 32 (tl6_4.header + tl6_4.len)) + BitVec.ofNat 32 (tl13_4.header + tl13_4.len))) (((((((((BitVec.ofNat 32 tl1_2.len) - BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) - BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) - BitVec.ofNat 32 (tl9_3.header + tl9_3.len))) - BitVec.ofNat 32 (tl6_4.header + tl6_4.len)) - BitVec.ofNat 32 (tl13_4.header + tl13_4.len))).toNat) = .ok tl2_5 ∧
      ∃ tl6_5, derElement 0x30 (memBytes M0 ((((((((((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl9_3.header + tl9_3.len))) + BitVec.ofNat 32 (tl6_4.header + tl6_4.len)) + BitVec.ofNat 32 (tl13_4.header + tl13_4.len))) + BitVec.ofNat 32 (tl2_5.header + tl2_5.len)) ((((((((((BitVec.ofNat 32 tl1_2.len) - BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) - BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) - BitVec.ofNat 32 (tl9_3.header + tl9_3.len))) - BitVec.ofNat 32 (tl6_4.header + tl6_4.len)) - BitVec.ofNat 32 (tl13_4.header + tl13_4.len))) - BitVec.ofNat 32 (tl2_5.header + tl2_5.len)).toNat) = .ok tl6_5 ∧
      ∃ op15_5 ol15_5 prp15_5 pu15_5, derAlgOf M0 (((((((((((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl9_3.header + tl9_3.len))) + BitVec.ofNat 32 (tl6_4.header + tl6_4.len)) + BitVec.ofNat 32 (tl13_4.header + tl13_4.len))) + BitVec.ofNat 32 (tl2_5.header + tl2_5.len)) + BitVec.ofNat 32 tl6_5.header) (tl6_5.len) = .ok ((op15_5, ol15_5), some (prp15_5, pu15_5)) ∧
      ∃ ta15_5, derElement 0x30 (memBytes M0 (((((((((((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl9_3.header + tl9_3.len))) + BitVec.ofNat 32 (tl6_4.header + tl6_4.len)) + BitVec.ofNat 32 (tl13_4.header + tl13_4.len))) + BitVec.ofNat 32 (tl2_5.header + tl2_5.len)) + BitVec.ofNat 32 tl6_5.header) (tl6_5.len)) = .ok ta15_5 ∧
      (BitVec.ofNat 8 pu15_5.tag = BitVec.ofNat 8 6) ∧
      (memBytes M0 (prp15_5 + BitVec.ofNat 32 pu15_5.header) pu15_5.len = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x30)) 8) ∧
      (memBytes M0 op15_5 ol15_5 = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xFC)) 7) ∧
      ∃ tl35_5, derElement 3 (memBytes M0 ((((((((((((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl9_3.header + tl9_3.len))) + BitVec.ofNat 32 (tl6_4.header + tl6_4.len)) + BitVec.ofNat 32 (tl13_4.header + tl13_4.len))) + BitVec.ofNat 32 (tl2_5.header + tl2_5.len)) + BitVec.ofNat 32 tl6_5.header) + BitVec.ofNat 32 (ta15_5.header + ta15_5.len)) ((BitVec.ofNat 32 (tl6_5.len)) - BitVec.ofNat 32 (ta15_5.header + ta15_5.len)).toNat) = .ok tl35_5 ∧
      ∃ bp35_5 bl35_5, derBitsOf (memBytes M0 ((((((((((((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl9_3.header + tl9_3.len))) + BitVec.ofNat 32 (tl6_4.header + tl6_4.len)) + BitVec.ofNat 32 (tl13_4.header + tl13_4.len))) + BitVec.ofNat 32 (tl2_5.header + tl2_5.len)) + BitVec.ofNat 32 tl6_5.header) + BitVec.ofNat 32 (ta15_5.header + ta15_5.len)) ((BitVec.ofNat 32 (tl6_5.len)) - BitVec.ofNat 32 (ta15_5.header + ta15_5.len)).toNat) ((((((((((((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl9_3.header + tl9_3.len))) + BitVec.ofNat 32 (tl6_4.header + tl6_4.len)) + BitVec.ofNat 32 (tl13_4.header + tl13_4.len))) + BitVec.ofNat 32 (tl2_5.header + tl2_5.len)) + BitVec.ofNat 32 tl6_5.header) + BitVec.ofNat 32 (ta15_5.header + ta15_5.len)) (.ok tl35_5) = .ok (bp35_5, bl35_5) ∧
      (bl35_5 = BitVec.ofNat 32 0x41) ∧
      (((BitVec.ofNat 32 (tl6_5.len)) - BitVec.ofNat 32 (ta15_5.header + ta15_5.len)) - BitVec.ofNat 32 (tl35_5.header + tl35_5.len) = 0) ∧
      (M0 bp35_5 = BitVec.ofNat 8 4) ∧
      (GsOk M0 bp35_5) ∧
      ∃ tl9_6, derOptRes 0xA3 (memBytes M0 ((((((((((((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl9_3.header + tl9_3.len))) + BitVec.ofNat 32 (tl6_4.header + tl6_4.len)) + BitVec.ofNat 32 (tl13_4.header + tl13_4.len))) + BitVec.ofNat 32 (tl2_5.header + tl2_5.len)) + BitVec.ofNat 32 (tl6_5.header + tl6_5.len))) ((((((((((((BitVec.ofNat 32 tl1_2.len) - BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) - BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) - BitVec.ofNat 32 (tl9_3.header + tl9_3.len))) - BitVec.ofNat 32 (tl6_4.header + tl6_4.len)) - BitVec.ofNat 32 (tl13_4.header + tl13_4.len))) - BitVec.ofNat 32 (tl2_5.header + tl2_5.len)) - BitVec.ofNat 32 (tl6_5.header + tl6_5.len))).toNat) = some (.ok tl9_6) ∧
      (((((((((((((BitVec.ofNat 32 tl1_2.len) - BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) - BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) - BitVec.ofNat 32 (tl9_3.header + tl9_3.len))) - BitVec.ofNat 32 (tl6_4.header + tl6_4.len)) - BitVec.ofNat 32 (tl13_4.header + tl13_4.len))) - BitVec.ofNat 32 (tl2_5.header + tl2_5.len)) - BitVec.ofNat 32 (tl6_5.header + tl6_5.len))) - BitVec.ofNat 32 (tl9_6.header + tl9_6.len) = 0) ∧
      ∃ tl25_6, derElement 0x30 (memBytes M0 (((((((((((((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl9_3.header + tl9_3.len))) + BitVec.ofNat 32 (tl6_4.header + tl6_4.len)) + BitVec.ofNat 32 (tl13_4.header + tl13_4.len))) + BitVec.ofNat 32 (tl2_5.header + tl2_5.len)) + BitVec.ofNat 32 (tl6_5.header + tl6_5.len))) + BitVec.ofNat 32 tl9_6.header) (BitVec.ofNat 32 tl9_6.len).toNat) = .ok tl25_6 ∧
      ((BitVec.ofNat 32 tl9_6.len) - BitVec.ofNat 32 (tl25_6.header + tl25_6.len) = 0) ∧
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0x4EA (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (8 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 ∧
        reg n' (9 : Fin 32) = (lp + BitVec.ofNat 32 t_1.header) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = BitVec.ofNat 32 0x15 ∧
        reg n' (21 : Fin 32) = bp35_5 ∧
        reg n' (22 : Fin 32) = (BitVec.ofNat 32 0x0) ∧
        reg n' (23 : Fin 32) = ((((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) ∧
        reg n' (24 : Fin 32) = bl16_2 ∧
        reg n' (25 : Fin 32) = (BitVec.ofNat 32 (tl6_4.header + tl6_4.len)) ∧
        reg n' (26 : Fin 32) = ll ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = BitVec.ofNat 32 tl25_6.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = (((((((((((((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl9_3.header + tl9_3.len))) + BitVec.ofNat 32 (tl6_4.header + tl6_4.len)) + BitVec.ofNat 32 (tl13_4.header + tl13_4.len))) + BitVec.ofNat 32 (tl2_5.header + tl2_5.len)) + BitVec.ofNat 32 (tl6_5.header + tl6_5.len))) + BitVec.ofNat 32 tl9_6.header) + BitVec.ofNat 32 tl25_6.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 tl25_6.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = (((((((((((((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl9_3.header + tl9_3.len))) + BitVec.ofNat 32 (tl6_4.header + tl6_4.len)) + BitVec.ofNat 32 (tl13_4.header + tl13_4.len))) + BitVec.ofNat 32 (tl2_5.header + tl2_5.len)) + BitVec.ofNat 32 (tl6_5.header + tl6_5.len))) + BitVec.ofNat 32 tl9_6.header) + BitVec.ofNat 32 tl25_6.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = BitVec.ofNat 32 tl25_6.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = BitVec.ofNat 32 tl25_6.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = BitVec.ofNat 32 (tl25_6.header + tl25_6.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) = lp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E4) = ll ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E8) = lp + BitVec.ofNat 32 (t_1.header + t_1.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2EC) = ll - BitVec.ofNat 32 (t_1.header + t_1.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1588) = lp + BitVec.ofNat 32 t_1.header ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158C) = (BitVec.ofNat 32 t_1.len).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158D) = (BitVec.ofNat 32 t_1.len).extractLsb' 8 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158E) = (BitVec.ofNat 32 t_1.len).extractLsb' 16 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158F) = (BitVec.ofNat 32 t_1.len).extractLsb' 24 8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = (BitVec.ofNat 32 (tl1_2.header + tl1_2.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = bp16_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = rootp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = dg ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = ((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = BitVec.ofNat 32 tl1_2.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = ((((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = (BitVec.ofNat 32 (tl9_3.header + tl9_3.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = BitVec.ofNat 32 (tm31_4 / 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = BitVec.ofNat 32 (tm31_4 % 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = BitVec.ofNat 32 (tm22_4 / 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = BitVec.ofNat 32 (tm22_4 % 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = (((((((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 tl1_2.header) + BitVec.ofNat 32 (tl29_2.header + tl29_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl9_3.header + tl9_3.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = (((lp + BitVec.ofNat 32 t_1.header)) + BitVec.ofNat 32 (tl1_2.header + tl1_2.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = (BitVec.ofNat 32 (tl8_2.header + tl8_2.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = bl16_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = lp ∧
        SvKeepL B n0.mem n'.mem [(0xA20, 0x10), (0x2E8, 0x8), (0x158D, 0xB), (0x1588, 0x4), (0x158C, 0x1), (0xA20, 0x11), (0x1590, 0x8), (0xA20, 0x11), (0x1590, 0x8), (0x80, 0x4), (0x84, 0x4), (0xA20, 0x8), (0x1590, 0x8), (0x7C, 0x4), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0xA20, 0x18), (0x180, 0x8), (0x78, 0x4), (0x200, 0x4), (0x204, 0x4), (0x208, 0x4), (0x20C, 0x4), (0x208, 0x8), (0x1020, 0x4), (0x1024, 0x4), (0x1028, 0x4), (0x102C, 0x4), (0xA20, 0x1C), (0x1028, 0x8), (0x74, 0x4), (0x70, 0x4), (0x68, 0x4), (0x64, 0x4), (0x60, 0x4), (0x6C, 0x4), (0x5C, 0x4), (0x245, 0xB), (0x240, 0x4), (0x244, 0x1), (0x248, 0x8), (0x58, 0x4), (0x54, 0x4), (0x248, 0x8), (0x50, 0x4), (0x4C, 0x4), (0x1025, 0xB), (0x1024, 0x1), (0xA20, 0x48), (0x1320, 0x4), (0x1324, 0x4), (0x1328, 0x4), (0x132C, 0x4), (0x1328, 0x8), (0x88, 0x4), (0x8C, 0x4), (0x90, 0x4), (0x40, 0x4), (0x94, 0x4), (0xA20, 0x4), (0xA28, 0x4), (0xA30, 0x4), (0xA38, 0x4), (0xA40, 0x4), (0x34, 0x4), (0x30, 0x4)]) := by
  rcases sv_l1 F E0 V0 hret hO s0 M0 fM g0_2 g0_10 g0_11 g0_18 g0_19 g0_21 g0_22 g0_25 g0_26 g0_27 w0_2e0 w0_2e4 w0_2e8 w0_2ec lc_in with ⟨-, e⟩ | hx1
  · exact .inl e
  obtain ⟨t_1, hx1⟩ := hx1
  obtain ⟨x1_0, hx1⟩ := hx1
  obtain ⟨x1_1, hx1⟩ := hx1
  obtain ⟨n1, hx1⟩ := hx1
  obtain ⟨c1, hx1⟩ := hx1
  obtain ⟨s1, hx1⟩ := hx1
  obtain ⟨E1, hx1⟩ := hx1
  obtain ⟨V1, hx1⟩ := hx1
  obtain ⟨fR1, hx1⟩ := hx1
  obtain ⟨r1_2, hx1⟩ := hx1
  obtain ⟨r1_3, hx1⟩ := hx1
  obtain ⟨r1_4, hx1⟩ := hx1
  obtain ⟨r1_a0, hx1⟩ := hx1
  obtain ⟨r1_a1, hx1⟩ := hx1
  obtain ⟨r1_a2, hx1⟩ := hx1
  obtain ⟨r1_18, hx1⟩ := hx1
  obtain ⟨r1_19, hx1⟩ := hx1
  obtain ⟨r1_21, hx1⟩ := hx1
  obtain ⟨r1_22, hx1⟩ := hx1
  obtain ⟨r1_25, hx1⟩ := hx1
  obtain ⟨r1_26, hx1⟩ := hx1
  obtain ⟨r1_27, hx1⟩ := hx1
  obtain ⟨w1_2e0, hx1⟩ := hx1
  obtain ⟨w1_2e4, hx1⟩ := hx1
  obtain ⟨w1_2e8, hx1⟩ := hx1
  obtain ⟨w1_2ec, hx1⟩ := hx1
  obtain ⟨w1_a20, hx1⟩ := hx1
  obtain ⟨w1_a24, hx1⟩ := hx1
  obtain ⟨w1_a28, hx1⟩ := hx1
  obtain ⟨w1_a2c, hx1⟩ := hx1
  obtain ⟨w1_1588, hx1⟩ := hx1
  obtain ⟨w1_1590, hx1⟩ := hx1
  obtain ⟨w1_1594, hx1⟩ := hx1
  obtain ⟨b1_a24, hx1⟩ := hx1
  obtain ⟨b1_a25, hx1⟩ := hx1
  obtain ⟨b1_a26, hx1⟩ := hx1
  obtain ⟨b1_a27, hx1⟩ := hx1
  obtain ⟨b1_158c, hx1⟩ := hx1
  obtain ⟨b1_158d, hx1⟩ := hx1
  obtain ⟨b1_158e, hx1⟩ := hx1
  obtain ⟨b1_158f, hx1⟩ := hx1
  have K1_L := hx1
  rcases sv_l2 F E1 V1 hret hO s1 M0 fR1 r1_2 r1_a0 r1_a1 r1_a2 r1_18 r1_19 r1_21 r1_22 r1_25 r1_26 r1_27 w1_1590 w1_1594 (((lc_in).content x1_0).ofNatLen) with ⟨-, e⟩ | hx2
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  obtain ⟨tl1_2, hx2⟩ := hx2
  obtain ⟨x2_0, hx2⟩ := hx2
  obtain ⟨tl8_2, hx2⟩ := hx2
  obtain ⟨x2_1, hx2⟩ := hx2
  obtain ⟨tl16_2, hx2⟩ := hx2
  obtain ⟨x2_2, hx2⟩ := hx2
  obtain ⟨bp16_2, hx2⟩ := hx2
  obtain ⟨bl16_2, hx2⟩ := hx2
  obtain ⟨x2_3, hx2⟩ := hx2
  obtain ⟨x2_4, hx2⟩ := hx2
  obtain ⟨tl29_2, hx2⟩ := hx2
  obtain ⟨x2_5, hx2⟩ := hx2
  obtain ⟨x2_6, hx2⟩ := hx2
  obtain ⟨te43_2, hx2⟩ := hx2
  obtain ⟨x2_7, hx2⟩ := hx2
  obtain ⟨x2_8, hx2⟩ := hx2
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
  obtain ⟨r2_23, hx2⟩ := hx2
  obtain ⟨r2_24, hx2⟩ := hx2
  obtain ⟨r2_25, hx2⟩ := hx2
  obtain ⟨r2_26, hx2⟩ := hx2
  obtain ⟨r2_27, hx2⟩ := hx2
  obtain ⟨w2_78, hx2⟩ := hx2
  obtain ⟨w2_7c, hx2⟩ := hx2
  obtain ⟨w2_80, hx2⟩ := hx2
  obtain ⟨w2_84, hx2⟩ := hx2
  obtain ⟨w2_178, hx2⟩ := hx2
  obtain ⟨w2_17c, hx2⟩ := hx2
  obtain ⟨w2_180, hx2⟩ := hx2
  obtain ⟨w2_184, hx2⟩ := hx2
  have K2_L := hx2
  rcases sv_l3 F E2 V2 hret hO s2 M0 fR2 r2_2 r2_8 r2_9 r2_18 r2_19 r2_21 r2_22 r2_23 r2_24 r2_25 r2_26 r2_27 w2_78 w2_7c w2_80 w2_84 w2_180 w2_184 ((((((lc_in).content x1_0).ofNatLen).content x2_0).ofNatLen).restW (opt_ok_elem x2_5)) with ⟨-, e⟩ | hx3
  · exact .inl (SvErrRet.pre (c1.trans (c2)) (by rw [r2_3, r1_3]) (by rw [r2_4, r1_4])
      (fun x hx => (fR2 x hx).trans (fM x hx).symm) e)
  obtain ⟨tl2_3, hx3⟩ := hx3
  obtain ⟨x3_0, hx3⟩ := hx3
  obtain ⟨ip2_3, hx3⟩ := hx3
  obtain ⟨il2_3, hx3⟩ := hx3
  obtain ⟨x3_1, hx3⟩ := hx3
  obtain ⟨x3_2, hx3⟩ := hx3
  obtain ⟨tl9_3, hx3⟩ := hx3
  obtain ⟨x3_3, hx3⟩ := hx3
  obtain ⟨op19_3, hx3⟩ := hx3
  obtain ⟨ol19_3, hx3⟩ := hx3
  obtain ⟨x3_4, hx3⟩ := hx3
  obtain ⟨x3_5, hx3⟩ := hx3
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
  obtain ⟨r3_21, hx3⟩ := hx3
  obtain ⟨r3_22, hx3⟩ := hx3
  obtain ⟨r3_23, hx3⟩ := hx3
  obtain ⟨r3_24, hx3⟩ := hx3
  obtain ⟨r3_25, hx3⟩ := hx3
  obtain ⟨r3_26, hx3⟩ := hx3
  obtain ⟨r3_27, hx3⟩ := hx3
  obtain ⟨w3_70, hx3⟩ := hx3
  obtain ⟨w3_74, hx3⟩ := hx3
  obtain ⟨w3_78, hx3⟩ := hx3
  obtain ⟨w3_7c, hx3⟩ := hx3
  obtain ⟨w3_80, hx3⟩ := hx3
  obtain ⟨w3_84, hx3⟩ := hx3
  obtain ⟨w3_180, hx3⟩ := hx3
  obtain ⟨w3_184, hx3⟩ := hx3
  obtain ⟨w3_a20, hx3⟩ := hx3
  obtain ⟨w3_a24, hx3⟩ := hx3
  obtain ⟨w3_a28, hx3⟩ := hx3
  obtain ⟨w3_1020, hx3⟩ := hx3
  obtain ⟨w3_1024, hx3⟩ := hx3
  have K3_L := hx3
  rcases sv_l4 F E3 V3 hret hO s3 M0 fR3 r3_2 r3_8 r3_9 r3_18 r3_19 r3_21 r3_22 r3_23 r3_24 r3_25 r3_26 r3_27 w3_70 w3_74 w3_78 w3_7c w3_80 w3_84 w3_180 w3_184 ((((((((lc_in).content x1_0).ofNatLen).content x2_0).ofNatLen).restW (opt_ok_elem x2_5)).restW x3_0).restW x3_3) with ⟨-, e⟩ | hx4
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3))) (by rw [r3_3, r2_3, r1_3]) (by rw [r3_4, r2_4, r1_4])
      (fun x hx => (fR3 x hx).trans (fM x hx).symm) e)
  obtain ⟨tl6_4, hx4⟩ := hx4
  obtain ⟨x4_0, hx4⟩ := hx4
  obtain ⟨tl13_4, hx4⟩ := hx4
  obtain ⟨x4_1, hx4⟩ := hx4
  obtain ⟨tm22_4, hx4⟩ := hx4
  obtain ⟨rs22_4, hx4⟩ := hx4
  obtain ⟨x4_2, hx4⟩ := hx4
  obtain ⟨tm31_4, hx4⟩ := hx4
  obtain ⟨rs31_4, hx4⟩ := hx4
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
  obtain ⟨w4_180, hx4⟩ := hx4
  obtain ⟨w4_184, hx4⟩ := hx4
  have K4_L := hx4
  rcases sv_l5 (rootp := 0) (dg := 0) F E4 V4 hret hO s4 M0 fR4 r4_2 r4_8 r4_9 r4_18 r4_19 r4_21 r4_22 r4_23 r4_24 r4_25 r4_26 r4_27 w4_180 w4_184 ((((((((((lc_in).content x1_0).ofNatLen).content x2_0).ofNatLen).restW (opt_ok_elem x2_5)).restW x3_0).restW x3_3).restW x4_0).restW x4_1) with ⟨-, e⟩ | hx5
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4)))) (by rw [r4_3, r3_3, r2_3, r1_3]) (by rw [r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR4 x hx).trans (fM x hx).symm) e)
  obtain ⟨tl2_5, hx5⟩ := hx5
  obtain ⟨x5_0, hx5⟩ := hx5
  obtain ⟨tl6_5, hx5⟩ := hx5
  obtain ⟨x5_1, hx5⟩ := hx5
  obtain ⟨op15_5, hx5⟩ := hx5
  obtain ⟨ol15_5, hx5⟩ := hx5
  obtain ⟨prp15_5, hx5⟩ := hx5
  obtain ⟨pu15_5, hx5⟩ := hx5
  obtain ⟨x5_2, hx5⟩ := hx5
  obtain ⟨ta15_5, hx5⟩ := hx5
  obtain ⟨x5_3, hx5⟩ := hx5
  obtain ⟨x5_4, hx5⟩ := hx5
  obtain ⟨x5_5, hx5⟩ := hx5
  obtain ⟨x5_6, hx5⟩ := hx5
  obtain ⟨tl35_5, hx5⟩ := hx5
  obtain ⟨x5_7, hx5⟩ := hx5
  obtain ⟨bp35_5, hx5⟩ := hx5
  obtain ⟨bl35_5, hx5⟩ := hx5
  obtain ⟨x5_8, hx5⟩ := hx5
  obtain ⟨x5_9, hx5⟩ := hx5
  obtain ⟨x5_10, hx5⟩ := hx5
  obtain ⟨n5, hx5⟩ := hx5
  obtain ⟨c5, hx5⟩ := hx5
  obtain ⟨s5, hx5⟩ := hx5
  obtain ⟨E5, hx5⟩ := hx5
  obtain ⟨V5, hx5⟩ := hx5
  obtain ⟨fR5, hx5⟩ := hx5
  obtain ⟨r5_2, hx5⟩ := hx5
  obtain ⟨r5_3, hx5⟩ := hx5
  obtain ⟨r5_4, hx5⟩ := hx5
  obtain ⟨r5_8, hx5⟩ := hx5
  obtain ⟨r5_9, hx5⟩ := hx5
  obtain ⟨r5_18, hx5⟩ := hx5
  obtain ⟨r5_19, hx5⟩ := hx5
  obtain ⟨r5_20, hx5⟩ := hx5
  obtain ⟨r5_21, hx5⟩ := hx5
  obtain ⟨r5_22, hx5⟩ := hx5
  obtain ⟨r5_23, hx5⟩ := hx5
  obtain ⟨r5_24, hx5⟩ := hx5
  obtain ⟨r5_25, hx5⟩ := hx5
  obtain ⟨r5_26, hx5⟩ := hx5
  obtain ⟨r5_27, hx5⟩ := hx5
  obtain ⟨w5_180, hx5⟩ := hx5
  obtain ⟨w5_184, hx5⟩ := hx5
  have K5_L := hx5
  rcases sv_l6 (rootp := 0) (dg := 0) (lp := 0) F E5 V5 hret hO s5 M0 fR5 r5_2 r5_8 r5_9 r5_18 r5_19 r5_21 r5_22 r5_23 r5_24 r5_25 r5_26 r5_27 w5_180 w5_184 ((((((((((((lc_in).content x1_0).ofNatLen).content x2_0).ofNatLen).restW (opt_ok_elem x2_5)).restW x3_0).restW x3_3).restW x4_0).restW x4_1).restW x5_0).restW x5_1) (by have h := SvIn.bitsW (((((((((((((lc_in).content x1_0).ofNatLen).content x2_0).ofNatLen).restW (opt_ok_elem x2_5)).restW x3_0).restW x3_3).restW x4_0).restW x4_1).restW x5_0).content x5_1).restN x5_3) x5_7 x5_8; rw [x5_9] at h; exact h) D0 with ⟨-, e⟩ | hx6
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5))))) (by rw [r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR5 x hx).trans (fM x hx).symm) e)
  obtain ⟨x6_0, hx6⟩ := hx6
  obtain ⟨x6_1, hx6⟩ := hx6
  obtain ⟨tl9_6, hx6⟩ := hx6
  obtain ⟨x6_2, hx6⟩ := hx6
  obtain ⟨x6_3, hx6⟩ := hx6
  obtain ⟨tl25_6, hx6⟩ := hx6
  obtain ⟨x6_4, hx6⟩ := hx6
  obtain ⟨x6_5, hx6⟩ := hx6
  obtain ⟨n6, hx6⟩ := hx6
  obtain ⟨c6, hx6⟩ := hx6
  obtain ⟨s6, hx6⟩ := hx6
  obtain ⟨E6, hx6⟩ := hx6
  obtain ⟨V6, hx6⟩ := hx6
  obtain ⟨fR6, hx6⟩ := hx6
  obtain ⟨r6_2, hx6⟩ := hx6
  obtain ⟨r6_3, hx6⟩ := hx6
  obtain ⟨r6_4, hx6⟩ := hx6
  obtain ⟨r6_8, hx6⟩ := hx6
  obtain ⟨r6_9, hx6⟩ := hx6
  obtain ⟨r6_18, hx6⟩ := hx6
  obtain ⟨r6_19, hx6⟩ := hx6
  obtain ⟨r6_20, hx6⟩ := hx6
  obtain ⟨r6_21, hx6⟩ := hx6
  obtain ⟨r6_22, hx6⟩ := hx6
  obtain ⟨r6_23, hx6⟩ := hx6
  obtain ⟨r6_24, hx6⟩ := hx6
  obtain ⟨r6_25, hx6⟩ := hx6
  obtain ⟨r6_26, hx6⟩ := hx6
  obtain ⟨r6_27, hx6⟩ := hx6
  obtain ⟨w6_30, hx6⟩ := hx6
  obtain ⟨w6_34, hx6⟩ := hx6
  obtain ⟨w6_40, hx6⟩ := hx6
  obtain ⟨w6_88, hx6⟩ := hx6
  obtain ⟨w6_8c, hx6⟩ := hx6
  obtain ⟨w6_90, hx6⟩ := hx6
  obtain ⟨w6_94, hx6⟩ := hx6
  obtain ⟨w6_a20, hx6⟩ := hx6
  obtain ⟨w6_a24, hx6⟩ := hx6
  obtain ⟨w6_a28, hx6⟩ := hx6
  obtain ⟨w6_a2c, hx6⟩ := hx6
  obtain ⟨w6_a30, hx6⟩ := hx6
  obtain ⟨w6_a38, hx6⟩ := hx6
  obtain ⟨w6_a40, hx6⟩ := hx6
  have K6_L := hx6
  exact .inr ⟨t_1, x1_0, x1_1, tl1_2, x2_0, tl8_2, x2_1, tl16_2, x2_2, bp16_2, bl16_2, x2_3, x2_4, tl29_2, x2_5, x2_6, te43_2, x2_7, x2_8, tl2_3, x3_0, ip2_3, il2_3, x3_1, x3_2, tl9_3, x3_3, op19_3, ol19_3, x3_4, x3_5, tl6_4, x4_0, tl13_4, x4_1, tm22_4, rs22_4, x4_2, tm31_4, rs31_4, x4_3, x4_4, tl2_5, x5_0, tl6_5, x5_1, op15_5, ol15_5, prp15_5, pu15_5, x5_2, ta15_5, x5_3, x5_4, x5_5, x5_6, tl35_5, x5_7, bp35_5, bl35_5, x5_8, x5_9, x5_10, x6_0, x6_1, tl9_6, x6_2, x6_3, tl25_6, x6_4, x6_5, n6, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6))))), fR6, s6, E6, V6,
    by rw [r6_3, r5_3, r4_3, r3_3, r2_3, r1_3], by rw [r6_4, r5_4, r4_4, r3_4, r2_4, r1_4], r6_2, r6_8, r6_9, r6_18, r6_19, r6_20, r6_21, r6_22, r6_23, r6_24, r6_25, r6_26, r6_27, w6_30, w6_34, w6_40, w6_88, w6_8c, w6_90, w6_94, w6_a20, w6_a24, w6_a28, w6_a2c, w6_a30, w6_a38, w6_a40, ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_2e0))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_2e4))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_2e8))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_2ec))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_1588))))), ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans ((K4_L.b8 (by decide) (by decide)).trans ((K3_L.b8 (by decide) (by decide)).trans ((K2_L.b8 (by decide) (by decide)).trans b1_158c))))), ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans ((K4_L.b8 (by decide) (by decide)).trans ((K3_L.b8 (by decide) (by decide)).trans ((K2_L.b8 (by decide) (by decide)).trans b1_158d))))), ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans ((K4_L.b8 (by decide) (by decide)).trans ((K3_L.b8 (by decide) (by decide)).trans ((K2_L.b8 (by decide) (by decide)).trans b1_158e))))), ((K6_L.b8 (by decide) (by decide)).trans ((K5_L.b8 (by decide) (by decide)).trans ((K4_L.b8 (by decide) (by decide)).trans ((K3_L.b8 (by decide) (by decide)).trans ((K2_L.b8 (by decide) (by decide)).trans b1_158f))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_78)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_7c)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_80)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_84)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans w2_178)))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans w2_17c)))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_70)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_74)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_4c)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_50)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_54)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_58)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_5c)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_60)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_64)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_68)), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_6c)), ((((((K1_L).trans K2_L).trans K3_L).trans K4_L).trans K5_L).trans K6_L).mono (by decide)⟩

end C3.RV32.Sv
