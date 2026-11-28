import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvTr1
import C3BootProofs.Proofs.SvTr2
import C3BootProofs.Proofs.SvTr3
import C3BootProofs.Proofs.SvTr4
import C3BootProofs.Proofs.SvTr5
import C3BootProofs.Proofs.SvTr6
import C3BootProofs.Proofs.SvTr7

/-!
# `sigstore::verify`: The timestamp up to its signed attributes

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **The timestamp up to its signed attributes**: from 0xA60 to the attributes loop at 0xEA0, `sv_tr1` to `sv_tr7`. -/
theorem sv_seg_tr {B out bp x20 x21 x22 x23 x24 x25 x26 x27 tsp tsl : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0xA60 (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = x24)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = x27)
    (htsp : memLoad32 M0 (bp + 0x20) = tsp)
    (htsl : memLoad32 M0 (bp + 0x24) = tsl)
    (htsp_in : SvIn B (bp + 0x20) 4)
    (htsl_in : SvIn B (bp + 0x24) 4)
    (atsp : (bp + 0x20).toNat % 4 = 0)
    (atsl : (bp + 0x24).toNat % 4 = 0)
    (ts_in : SvIn B tsp tsl.toNat)
    (D0 : SvData M0) :
    SvErrRet B out v n0 ∨
    (∃ tl10_1, derElement 0x30 (memBytes M0 (tsp) (tsl).toNat) = .ok tl10_1 ∧
      ((tsl) - BitVec.ofNat 32 (tl10_1.header + tl10_1.len) = 0) ∧
      ∃ tl21_1, derElement 0x30 (memBytes M0 ((tsp) + BitVec.ofNat 32 tl10_1.header) (BitVec.ofNat 32 tl10_1.len).toNat) = .ok tl21_1 ∧
      derIntIsOf M0 (memBytes M0 (((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 tl21_1.header) (BitVec.ofNat 32 tl21_1.len).toNat) (((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 tl21_1.header) (derElement 2 (memBytes M0 (((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 tl21_1.header) (BitVec.ofNat 32 tl21_1.len).toNat)) ((BitVec.ofNat 32 0x0).extractLsb' 0 8) = .ok true ∧
      ∃ te30_1, derElement 2 (memBytes M0 (((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 tl21_1.header) (BitVec.ofNat 32 tl21_1.len).toNat) = .ok te30_1 ∧
      ((BitVec.ofNat 32 tl21_1.len) - BitVec.ofNat 32 (te30_1.header + te30_1.len) = 0) ∧
      ∃ tl2_2, derElement 0x30 (memBytes M0 ((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) (((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (tl21_1.header + tl21_1.len))).toNat) = .ok tl2_2 ∧
      ((((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) - BitVec.ofNat 32 (tl2_2.header + tl2_2.len) = 0) ∧
      ∃ op13_2 ol13_2, derContent (((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) (derOid (memBytes M0 (((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) (BitVec.ofNat 32 tl2_2.len).toNat)) = .ok (op13_2, ol13_2) ∧
      ∃ to13_2, derOid (memBytes M0 (((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) (BitVec.ofNat 32 tl2_2.len).toNat) = .ok to13_2 ∧
      (memBytes M0 op13_2 ol13_2.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress)) 9) ∧
      ∃ tl21_2, derElement 0xA0 (memBytes M0 ((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) ((BitVec.ofNat 32 tl2_2.len) - BitVec.ofNat 32 (to13_2.header + to13_2.len)).toNat) = .ok tl21_2 ∧
      (((BitVec.ofNat 32 tl2_2.len) - BitVec.ofNat 32 (to13_2.header + to13_2.len)) - BitVec.ofNat 32 (tl21_2.header + tl21_2.len) = 0) ∧
      ∃ tl32_2, derElement 0x30 (memBytes M0 (((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) (BitVec.ofNat 32 tl21_2.len).toNat) = .ok tl32_2 ∧
      ((BitVec.ofNat 32 tl21_2.len) - BitVec.ofNat 32 (tl32_2.header + tl32_2.len) = 0) ∧
      derIntIsOf M0 (memBytes M0 ((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) (BitVec.ofNat 32 tl32_2.len).toNat) ((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) (derElement 2 (memBytes M0 ((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) (BitVec.ofNat 32 tl32_2.len).toNat)) ((BitVec.ofNat 32 0x3).extractLsb' 0 8) = .ok true ∧
      ∃ te43_2, derElement 2 (memBytes M0 ((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) (BitVec.ofNat 32 tl32_2.len).toNat) = .ok te43_2 ∧
      ∃ tl2_3, derElement 0x31 (memBytes M0 ((((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) + BitVec.ofNat 32 (te43_2.header + te43_2.len))) (((BitVec.ofNat 32 tl32_2.len) - BitVec.ofNat 32 (te43_2.header + te43_2.len))).toNat) = .ok tl2_3 ∧
      isSha256Of M0 (((((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) + BitVec.ofNat 32 (te43_2.header + te43_2.len))) + BitVec.ofNat 32 tl2_3.header) (BitVec.ofNat 32 tl2_3.len).toNat = .ok true ∧
      ∃ te11_3, derElement 0x30 (memBytes M0 (((((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) + BitVec.ofNat 32 (te43_2.header + te43_2.len))) + BitVec.ofNat 32 tl2_3.header) (BitVec.ofNat 32 tl2_3.len).toNat) = .ok te11_3 ∧
      ((BitVec.ofNat 32 tl2_3.len) - BitVec.ofNat 32 (te11_3.header + te11_3.len) = 0) ∧
      ∃ tl19_3, derElement 0x30 (memBytes M0 (((((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) + BitVec.ofNat 32 (te43_2.header + te43_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) ((((BitVec.ofNat 32 tl32_2.len) - BitVec.ofNat 32 (te43_2.header + te43_2.len))) - BitVec.ofNat 32 (tl2_3.header + tl2_3.len)).toNat) = .ok tl19_3 ∧
      ∃ op28_3 ol28_3, derContent ((((((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) + BitVec.ofNat 32 (te43_2.header + te43_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 tl19_3.header) (derOid (memBytes M0 ((((((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) + BitVec.ofNat 32 (te43_2.header + te43_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 tl19_3.header) (BitVec.ofNat 32 tl19_3.len).toNat)) = .ok (op28_3, ol28_3) ∧
      ∃ to28_3, derOid (memBytes M0 ((((((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) + BitVec.ofNat 32 (te43_2.header + te43_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 tl19_3.header) (BitVec.ofNat 32 tl19_3.len).toNat) = .ok to28_3 ∧
      (memBytes M0 op28_3 ol28_3.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x9)) 11) ∧
      ∃ tl2_4, derOptRes 0xA0 (memBytes M0 ((((((((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) + BitVec.ofNat 32 (te43_2.header + te43_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 tl19_3.header) + BitVec.ofNat 32 (to28_3.header + to28_3.len))) (((BitVec.ofNat 32 tl19_3.len) - BitVec.ofNat 32 (to28_3.header + to28_3.len))).toNat) = some (.ok tl2_4) ∧
      ((((BitVec.ofNat 32 tl19_3.len) - BitVec.ofNat 32 (to28_3.header + to28_3.len))) - BitVec.ofNat 32 (tl2_4.header + tl2_4.len) = 0) ∧
      ∃ vp23_4 vl23_4, derContent (((((((((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) + BitVec.ofNat 32 (te43_2.header + te43_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 tl19_3.header) + BitVec.ofNat 32 (to28_3.header + to28_3.len))) + BitVec.ofNat 32 tl2_4.header) (derElement 4 (memBytes M0 (((((((((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) + BitVec.ofNat 32 (te43_2.header + te43_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 tl19_3.header) + BitVec.ofNat 32 (to28_3.header + to28_3.len))) + BitVec.ofNat 32 tl2_4.header) (BitVec.ofNat 32 tl2_4.len).toNat)) = .ok (vp23_4, vl23_4) ∧
      ∃ te23_4, derElement 4 (memBytes M0 (((((((((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) + BitVec.ofNat 32 (te43_2.header + te43_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 tl19_3.header) + BitVec.ofNat 32 (to28_3.header + to28_3.len))) + BitVec.ofNat 32 tl2_4.header) (BitVec.ofNat 32 tl2_4.len).toNat) = .ok te23_4 ∧
      ((BitVec.ofNat 32 tl2_4.len) - BitVec.ofNat 32 (te23_4.header + te23_4.len) = 0) ∧
      ∃ tr5_w328_5 : Word, ∃ tr5_w32c_5 : Word, (((derOptRes 0xA0 (memBytes M0 (((((((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) + BitVec.ofNat 32 (te43_2.header + te43_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl19_3.header + tl19_3.len))) ((((((BitVec.ofNat 32 tl32_2.len) - BitVec.ofNat 32 (te43_2.header + te43_2.len))) - BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) - BitVec.ofNat 32 (tl19_3.header + tl19_3.len))).toNat) = none) ∧ ((((((BitVec.ofNat 32 tl32_2.len) - BitVec.ofNat 32 (te43_2.header + te43_2.len))) - BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) - BitVec.ofNat 32 (tl19_3.header + tl19_3.len)) = 0 ∨ (M0 (((((((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) + BitVec.ofNat 32 (te43_2.header + te43_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl19_3.header + tl19_3.len)))).toNat ≠ 0xA1) ∧ tr5_w328_5 = ((((((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) + BitVec.ofNat 32 (te43_2.header + te43_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl19_3.header + tl19_3.len)) ∧ tr5_w32c_5 = (((((BitVec.ofNat 32 tl32_2.len) - BitVec.ofNat 32 (te43_2.header + te43_2.len))) - BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) - BitVec.ofNat 32 (tl19_3.header + tl19_3.len))) ∨ ((¬ (derOptRes 0xA0 (memBytes M0 (((((((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) + BitVec.ofNat 32 (te43_2.header + te43_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl19_3.header + tl19_3.len))) ((((((BitVec.ofNat 32 tl32_2.len) - BitVec.ofNat 32 (te43_2.header + te43_2.len))) - BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) - BitVec.ofNat 32 (tl19_3.header + tl19_3.len))).toNat) = none)) ∧ ∃ tl2, derOptRes 0xA0 (memBytes M0 (((((((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) + BitVec.ofNat 32 (te43_2.header + te43_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl19_3.header + tl19_3.len))) ((((((BitVec.ofNat 32 tl32_2.len) - BitVec.ofNat 32 (te43_2.header + te43_2.len))) - BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) - BitVec.ofNat 32 (tl19_3.header + tl19_3.len))).toNat) = some (.ok tl2) ∧ (((((((BitVec.ofNat 32 tl32_2.len) - BitVec.ofNat 32 (te43_2.header + te43_2.len))) - BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) - BitVec.ofNat 32 (tl19_3.header + tl19_3.len))) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0 ∨ (M0 ((((((((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) + BitVec.ofNat 32 (te43_2.header + te43_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl19_3.header + tl19_3.len))) + BitVec.ofNat 32 (tl2.header + tl2.len))).toNat ≠ 0xA1) ∧ tr5_w328_5 = (((((((((((((tsp) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (tl21_1.header + tl21_1.len))) + BitVec.ofNat 32 tl2_2.header) + BitVec.ofNat 32 (to13_2.header + to13_2.len)) + BitVec.ofNat 32 tl21_2.header) + BitVec.ofNat 32 tl32_2.header) + BitVec.ofNat 32 (te43_2.header + te43_2.len))) + BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) + BitVec.ofNat 32 (tl19_3.header + tl19_3.len))) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tr5_w32c_5 = ((((((BitVec.ofNat 32 tl32_2.len) - BitVec.ofNat 32 (te43_2.header + te43_2.len))) - BitVec.ofNat 32 (tl2_3.header + tl2_3.len)) - BitVec.ofNat 32 (tl19_3.header + tl19_3.len))) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tr5_w328_5 tr5_w32c_5.toNat ∧
      ∃ tl2_6, derElement 0x31 (memBytes M0 (tr5_w328_5) (tr5_w32c_5).toNat) = .ok tl2_6 ∧
      ((tr5_w32c_5) - BitVec.ofNat 32 (tl2_6.header + tl2_6.len) = 0) ∧
      ∃ tl13_6, derElement 0x30 (memBytes M0 ((tr5_w328_5) + BitVec.ofNat 32 tl2_6.header) (BitVec.ofNat 32 tl2_6.len).toNat) = .ok tl13_6 ∧
      ((BitVec.ofNat 32 tl2_6.len) - BitVec.ofNat 32 (tl13_6.header + tl13_6.len) = 0) ∧
      derIntIsOf M0 (memBytes M0 (((tr5_w328_5) + BitVec.ofNat 32 tl2_6.header) + BitVec.ofNat 32 tl13_6.header) (BitVec.ofNat 32 tl13_6.len).toNat) (((tr5_w328_5) + BitVec.ofNat 32 tl2_6.header) + BitVec.ofNat 32 tl13_6.header) (derElement 2 (memBytes M0 (((tr5_w328_5) + BitVec.ofNat 32 tl2_6.header) + BitVec.ofNat 32 tl13_6.header) (BitVec.ofNat 32 tl13_6.len).toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = .ok true ∧
      ∃ te25_6, derElement 2 (memBytes M0 (((tr5_w328_5) + BitVec.ofNat 32 tl2_6.header) + BitVec.ofNat 32 tl13_6.header) (BitVec.ofNat 32 tl13_6.len).toNat) = .ok te25_6 ∧
      ∃ tl31_6, derElement 0x30 (memBytes M0 ((((tr5_w328_5) + BitVec.ofNat 32 tl2_6.header) + BitVec.ofNat 32 tl13_6.header) + BitVec.ofNat 32 (te25_6.header + te25_6.len)) ((BitVec.ofNat 32 tl13_6.len) - BitVec.ofNat 32 (te25_6.header + te25_6.len)).toNat) = .ok tl31_6 ∧
      isSha256Of M0 (((((tr5_w328_5) + BitVec.ofNat 32 tl2_6.header) + BitVec.ofNat 32 tl13_6.header) + BitVec.ofNat 32 (te25_6.header + te25_6.len)) + BitVec.ofNat 32 (tl31_6.header + tl31_6.len)) (((BitVec.ofNat 32 tl13_6.len) - BitVec.ofNat 32 (te25_6.header + te25_6.len)) - BitVec.ofNat 32 (tl31_6.header + tl31_6.len)).toNat = .ok true ∧
      ∃ te39_6, derElement 0x30 (memBytes M0 (((((tr5_w328_5) + BitVec.ofNat 32 tl2_6.header) + BitVec.ofNat 32 tl13_6.header) + BitVec.ofNat 32 (te25_6.header + te25_6.len)) + BitVec.ofNat 32 (tl31_6.header + tl31_6.len)) (((BitVec.ofNat 32 tl13_6.len) - BitVec.ofNat 32 (te25_6.header + te25_6.len)) - BitVec.ofNat 32 (tl31_6.header + tl31_6.len)).toNat) = .ok te39_6 ∧
      ∃ tl45_6, derOptRes 0xA0 (memBytes M0 ((((((tr5_w328_5) + BitVec.ofNat 32 tl2_6.header) + BitVec.ofNat 32 tl13_6.header) + BitVec.ofNat 32 (te25_6.header + te25_6.len)) + BitVec.ofNat 32 (tl31_6.header + tl31_6.len)) + BitVec.ofNat 32 (te39_6.header + te39_6.len)) ((((BitVec.ofNat 32 tl13_6.len) - BitVec.ofNat 32 (te25_6.header + te25_6.len)) - BitVec.ofNat 32 (tl31_6.header + tl31_6.len)) - BitVec.ofNat 32 (te39_6.header + te39_6.len)).toNat) = some (.ok tl45_6) ∧
      ((BitVec.ofNat 32 tl45_6.len) ≠ 0) ∧
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0xEA0 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = (BitVec.ofNat 32 tl45_6.len) ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = x27 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((((((tr5_w328_5) + BitVec.ofNat 32 tl2_6.header) + BitVec.ofNat 32 tl13_6.header) + BitVec.ofNat 32 (te25_6.header + te25_6.len)) + BitVec.ofNat 32 (tl31_6.header + tl31_6.len)) + BitVec.ofNat 32 (te39_6.header + te39_6.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = (BitVec.ofNat 32 (tl45_6.header + tl45_6.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = (((((((tr5_w328_5) + BitVec.ofNat 32 tl2_6.header) + BitVec.ofNat 32 tl13_6.header) + BitVec.ofNat 32 (te25_6.header + te25_6.len)) + BitVec.ofNat 32 (tl31_6.header + tl31_6.len)) + BitVec.ofNat 32 (te39_6.header + te39_6.len)) + BitVec.ofNat 32 tl45_6.header) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = (BitVec.ofNat 32 tl45_6.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = (((((((tr5_w328_5) + BitVec.ofNat 32 tl2_6.header) + BitVec.ofNat 32 tl13_6.header) + BitVec.ofNat 32 (te25_6.header + te25_6.len)) + BitVec.ofNat 32 (tl31_6.header + tl31_6.len)) + BitVec.ofNat 32 (te39_6.header + te39_6.len)) + BitVec.ofNat 32 tl45_6.header) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = (BitVec.ofNat 32 tl45_6.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = (((((((tr5_w328_5) + BitVec.ofNat 32 tl2_6.header) + BitVec.ofNat 32 tl13_6.header) + BitVec.ofNat 32 (te25_6.header + te25_6.len)) + BitVec.ofNat 32 (tl31_6.header + tl31_6.len)) + BitVec.ofNat 32 (te39_6.header + te39_6.len)) + BitVec.ofNat 32 (tl45_6.header + tl45_6.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = (((((BitVec.ofNat 32 tl13_6.len) - BitVec.ofNat 32 (te25_6.header + te25_6.len)) - BitVec.ofNat 32 (tl31_6.header + tl31_6.len)) - BitVec.ofNat 32 (te39_6.header + te39_6.len)) - BitVec.ofNat 32 (tl45_6.header + tl45_6.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = vp23_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = vl23_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = BitVec.ofNat 32 (tl31_6.header + tl31_6.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = (((tr5_w328_5) + BitVec.ofNat 32 tl2_6.header) + BitVec.ofNat 32 tl13_6.header) + BitVec.ofNat 32 (te25_6.header + te25_6.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x424) = ((((((tr5_w328_5) + BitVec.ofNat 32 tl2_6.header) + BitVec.ofNat 32 tl13_6.header) + BitVec.ofNat 32 (te25_6.header + te25_6.len)) + BitVec.ofNat 32 (tl31_6.header + tl31_6.len)) + BitVec.ofNat 32 (te39_6.header + te39_6.len)) + BitVec.ofNat 32 tl45_6.header ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = BitVec.ofNat 32 tl45_6.len ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x42C) = (((((tr5_w328_5) + BitVec.ofNat 32 tl2_6.header) + BitVec.ofNat 32 tl13_6.header) + BitVec.ofNat 32 (te25_6.header + te25_6.len)) + BitVec.ofNat 32 (tl31_6.header + tl31_6.len)) + BitVec.ofNat 32 (te39_6.header + te39_6.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x430) = BitVec.ofNat 32 (tl45_6.header + tl45_6.len) ∧
        SvKeepL B n0.mem n'.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1), (0x348, 0x8), (0x420, 0x18), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4), (0x358, 0x8), (0x74, 0x4), (0x78, 0x4), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8), (0x378, 0x8), (0x64, 0x4), (0x7C, 0x4), (0x44, 0x4), (0x50, 0x4), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4)]) := by
  rcases sv_tr1 FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 htsp htsl htsp_in htsl_in atsp atsl ts_in with ⟨-, e⟩ | hx1
  · exact .inl e
  obtain ⟨tl10_1, hx1⟩ := hx1
  obtain ⟨x1_0, hx1⟩ := hx1
  obtain ⟨x1_1, hx1⟩ := hx1
  obtain ⟨tl21_1, hx1⟩ := hx1
  obtain ⟨x1_2, hx1⟩ := hx1
  obtain ⟨x1_3, hx1⟩ := hx1
  obtain ⟨te30_1, hx1⟩ := hx1
  obtain ⟨x1_4, hx1⟩ := hx1
  obtain ⟨x1_5, hx1⟩ := hx1
  obtain ⟨n1, hx1⟩ := hx1
  obtain ⟨c1, hx1⟩ := hx1
  obtain ⟨s1, hx1⟩ := hx1
  obtain ⟨E1, hx1⟩ := hx1
  obtain ⟨V1, hx1⟩ := hx1
  obtain ⟨fR1, hx1⟩ := hx1
  obtain ⟨r1_2, hx1⟩ := hx1
  obtain ⟨r1_3, hx1⟩ := hx1
  obtain ⟨r1_4, hx1⟩ := hx1
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
  obtain ⟨w1_2e8, hx1⟩ := hx1
  obtain ⟨w1_2ec, hx1⟩ := hx1
  have K1_L := hx1
  rcases sv_tr2 FW E1 V1 hret hO s1 M0 fR1 r1_2 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 r1_24 r1_25 r1_26 r1_27 w1_2e8 w1_2ec ((((ts_in).content x1_0).ofNatLen).restW x1_2) with ⟨-, e⟩ | hx2
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  obtain ⟨tl2_2, hx2⟩ := hx2
  obtain ⟨x2_0, hx2⟩ := hx2
  obtain ⟨x2_1, hx2⟩ := hx2
  obtain ⟨op13_2, hx2⟩ := hx2
  obtain ⟨ol13_2, hx2⟩ := hx2
  obtain ⟨x2_2, hx2⟩ := hx2
  obtain ⟨to13_2, hx2⟩ := hx2
  obtain ⟨x2_3, hx2⟩ := hx2
  obtain ⟨x2_4, hx2⟩ := hx2
  obtain ⟨tl21_2, hx2⟩ := hx2
  obtain ⟨x2_5, hx2⟩ := hx2
  obtain ⟨x2_6, hx2⟩ := hx2
  obtain ⟨tl32_2, hx2⟩ := hx2
  obtain ⟨x2_7, hx2⟩ := hx2
  obtain ⟨x2_8, hx2⟩ := hx2
  obtain ⟨x2_9, hx2⟩ := hx2
  obtain ⟨te43_2, hx2⟩ := hx2
  obtain ⟨x2_10, hx2⟩ := hx2
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
  obtain ⟨r2_25, hx2⟩ := hx2
  obtain ⟨r2_26, hx2⟩ := hx2
  obtain ⟨r2_27, hx2⟩ := hx2
  obtain ⟨w2_328, hx2⟩ := hx2
  obtain ⟨w2_32c, hx2⟩ := hx2
  have K2_L := hx2
  rcases sv_tr3 FW E2 V2 hret hO s2 M0 fR2 r2_2 r2_18 r2_19 r2_20 r2_21 r2_22 r2_23 r2_24 r2_25 r2_26 r2_27 w2_328 w2_32c ((((((((((((ts_in).content x1_0).ofNatLen).restW x1_2).content x2_0).ofNatLen).restW (derOid_ok_elem x2_3)).content x2_5).ofNatLen).content x2_7).ofNatLen).restW x2_10) D0 with ⟨-, e⟩ | hx3
  · exact .inl (SvErrRet.pre (c1.trans (c2)) (by rw [r2_3, r1_3]) (by rw [r2_4, r1_4])
      (fun x hx => (fR2 x hx).trans (fM x hx).symm) e)
  obtain ⟨tl2_3, hx3⟩ := hx3
  obtain ⟨x3_0, hx3⟩ := hx3
  obtain ⟨x3_1, hx3⟩ := hx3
  obtain ⟨te11_3, hx3⟩ := hx3
  obtain ⟨x3_2, hx3⟩ := hx3
  obtain ⟨x3_3, hx3⟩ := hx3
  obtain ⟨tl19_3, hx3⟩ := hx3
  obtain ⟨x3_4, hx3⟩ := hx3
  obtain ⟨op28_3, hx3⟩ := hx3
  obtain ⟨ol28_3, hx3⟩ := hx3
  obtain ⟨x3_5, hx3⟩ := hx3
  obtain ⟨to28_3, hx3⟩ := hx3
  obtain ⟨x3_6, hx3⟩ := hx3
  obtain ⟨x3_7, hx3⟩ := hx3
  obtain ⟨n3, hx3⟩ := hx3
  obtain ⟨c3, hx3⟩ := hx3
  obtain ⟨s3, hx3⟩ := hx3
  obtain ⟨E3, hx3⟩ := hx3
  obtain ⟨V3, hx3⟩ := hx3
  obtain ⟨fR3, hx3⟩ := hx3
  obtain ⟨r3_2, hx3⟩ := hx3
  obtain ⟨r3_3, hx3⟩ := hx3
  obtain ⟨r3_4, hx3⟩ := hx3
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
  obtain ⟨w3_328, hx3⟩ := hx3
  obtain ⟨w3_32c, hx3⟩ := hx3
  obtain ⟨w3_348, hx3⟩ := hx3
  obtain ⟨w3_34c, hx3⟩ := hx3
  have K3_L := hx3
  rcases sv_tr4 FW E3 V3 hret hO s3 M0 fR3 r3_2 r3_18 r3_19 r3_20 r3_21 r3_22 r3_23 r3_24 r3_25 r3_26 r3_27 w3_328 w3_32c w3_348 w3_34c ((((((((((((((ts_in).content x1_0).ofNatLen).restW x1_2).content x2_0).ofNatLen).restW (derOid_ok_elem x2_3)).content x2_5).ofNatLen).content x2_7).ofNatLen).restW x2_10).restW x3_0).restW x3_4) ((((((((((((((((ts_in).content x1_0).ofNatLen).restW x1_2).content x2_0).ofNatLen).restW (derOid_ok_elem x2_3)).content x2_5).ofNatLen).content x2_7).ofNatLen).restW x2_10).restW x3_0).content x3_4).ofNatLen).restW (derOid_ok_elem x3_6)) with ⟨-, e⟩ | hx4
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3))) (by rw [r3_3, r2_3, r1_3]) (by rw [r3_4, r2_4, r1_4])
      (fun x hx => (fR3 x hx).trans (fM x hx).symm) e)
  obtain ⟨tl2_4, hx4⟩ := hx4
  obtain ⟨x4_0, hx4⟩ := hx4
  obtain ⟨x4_1, hx4⟩ := hx4
  obtain ⟨vp23_4, hx4⟩ := hx4
  obtain ⟨vl23_4, hx4⟩ := hx4
  obtain ⟨x4_2, hx4⟩ := hx4
  obtain ⟨te23_4, hx4⟩ := hx4
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
  obtain ⟨w4_74, hx4⟩ := hx4
  obtain ⟨w4_78, hx4⟩ := hx4
  obtain ⟨w4_328, hx4⟩ := hx4
  obtain ⟨w4_32c, hx4⟩ := hx4
  have K4_L := hx4
  rcases sv_tr5 FW E4 V4 hret hO s4 M0 fR4 r4_2 r4_18 r4_19 r4_20 r4_21 r4_22 r4_23 r4_24 r4_25 r4_26 r4_27 w4_74 w4_78 w4_328 w4_32c ((((((((((((((ts_in).content x1_0).ofNatLen).restW x1_2).content x2_0).ofNatLen).restW (derOid_ok_elem x2_3)).content x2_5).ofNatLen).content x2_7).ofNatLen).restW x2_10).restW x3_0).restW x3_4) with e | hx5
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4)))) (by rw [r4_3, r3_3, r2_3, r1_3]) (by rw [r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR4 x hx).trans (fM x hx).symm) e)
  obtain ⟨tr5_w328_5, hx5⟩ := hx5
  obtain ⟨tr5_w32c_5, hx5⟩ := hx5
  obtain ⟨x5_0, hx5⟩ := hx5
  obtain ⟨x5_1, hx5⟩ := hx5
  obtain ⟨n5, hx5⟩ := hx5
  obtain ⟨c5, hx5⟩ := hx5
  obtain ⟨s5, hx5⟩ := hx5
  obtain ⟨E5, hx5⟩ := hx5
  obtain ⟨V5, hx5⟩ := hx5
  obtain ⟨fR5, hx5⟩ := hx5
  obtain ⟨r5_2, hx5⟩ := hx5
  obtain ⟨r5_3, hx5⟩ := hx5
  obtain ⟨r5_4, hx5⟩ := hx5
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
  obtain ⟨w5_74, hx5⟩ := hx5
  obtain ⟨w5_78, hx5⟩ := hx5
  obtain ⟨w5_328, hx5⟩ := hx5
  obtain ⟨w5_32c, hx5⟩ := hx5
  have K5_L := hx5
  rcases sv_tr6 FW E5 V5 hret hO s5 M0 fR5 r5_2 r5_18 r5_19 r5_20 r5_21 r5_22 r5_23 r5_24 r5_25 r5_26 r5_27 w5_74 w5_78 w5_328 w5_32c x5_1 D0 with ⟨-, e⟩ | hx6
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5))))) (by rw [r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR5 x hx).trans (fM x hx).symm) e)
  obtain ⟨tl2_6, hx6⟩ := hx6
  obtain ⟨x6_0, hx6⟩ := hx6
  obtain ⟨x6_1, hx6⟩ := hx6
  obtain ⟨tl13_6, hx6⟩ := hx6
  obtain ⟨x6_2, hx6⟩ := hx6
  obtain ⟨x6_3, hx6⟩ := hx6
  obtain ⟨x6_4, hx6⟩ := hx6
  obtain ⟨te25_6, hx6⟩ := hx6
  obtain ⟨x6_5, hx6⟩ := hx6
  obtain ⟨tl31_6, hx6⟩ := hx6
  obtain ⟨x6_6, hx6⟩ := hx6
  obtain ⟨x6_7, hx6⟩ := hx6
  obtain ⟨te39_6, hx6⟩ := hx6
  obtain ⟨x6_8, hx6⟩ := hx6
  obtain ⟨tl45_6, hx6⟩ := hx6
  obtain ⟨x6_9, hx6⟩ := hx6
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
  obtain ⟨r6_a0, hx6⟩ := hx6
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
  obtain ⟨w6_48, hx6⟩ := hx6
  obtain ⟨w6_4c, hx6⟩ := hx6
  obtain ⟨w6_74, hx6⟩ := hx6
  obtain ⟨w6_78, hx6⟩ := hx6
  obtain ⟨w6_378, hx6⟩ := hx6
  obtain ⟨w6_37c, hx6⟩ := hx6
  obtain ⟨w6_424, hx6⟩ := hx6
  obtain ⟨w6_428, hx6⟩ := hx6
  obtain ⟨w6_42c, hx6⟩ := hx6
  obtain ⟨w6_430, hx6⟩ := hx6
  have K6_L := hx6
  rcases sv_tr7 FW E6 V6 hret hO s6 M0 fR6 r6_2 r6_a0 r6_18 r6_19 r6_20 r6_21 r6_22 r6_23 r6_24 r6_25 r6_26 r6_27 w6_378 w6_37c w6_424 w6_428 w6_42c w6_430 ((((((((((x5_1).content x6_0).ofNatLen).content x6_2).ofNatLen).restW x6_5).restW x6_6).restW x6_8).content (opt_ok_elem x6_9)).ofNatLen) (((((((((x5_1).content x6_0).ofNatLen).content x6_2).ofNatLen).restW x6_5).restW x6_6).restW x6_8).restW (opt_ok_elem x6_9)) with ⟨-, e⟩ | hx7
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6)))))) (by rw [r6_3, r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r6_4, r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR6 x hx).trans (fM x hx).symm) e)
  obtain ⟨x7_0, hx7⟩ := hx7
  obtain ⟨n7, hx7⟩ := hx7
  obtain ⟨c7, hx7⟩ := hx7
  obtain ⟨s7, hx7⟩ := hx7
  obtain ⟨E7, hx7⟩ := hx7
  obtain ⟨V7, hx7⟩ := hx7
  obtain ⟨fR7, hx7⟩ := hx7
  obtain ⟨r7_2, hx7⟩ := hx7
  obtain ⟨r7_3, hx7⟩ := hx7
  obtain ⟨r7_4, hx7⟩ := hx7
  obtain ⟨r7_18, hx7⟩ := hx7
  obtain ⟨r7_19, hx7⟩ := hx7
  obtain ⟨r7_20, hx7⟩ := hx7
  obtain ⟨r7_21, hx7⟩ := hx7
  obtain ⟨r7_22, hx7⟩ := hx7
  obtain ⟨r7_23, hx7⟩ := hx7
  obtain ⟨r7_24, hx7⟩ := hx7
  obtain ⟨r7_25, hx7⟩ := hx7
  obtain ⟨r7_26, hx7⟩ := hx7
  obtain ⟨r7_27, hx7⟩ := hx7
  obtain ⟨w7_44, hx7⟩ := hx7
  obtain ⟨w7_50, hx7⟩ := hx7
  obtain ⟨w7_64, hx7⟩ := hx7
  obtain ⟨w7_7c, hx7⟩ := hx7
  obtain ⟨w7_25c, hx7⟩ := hx7
  obtain ⟨w7_260, hx7⟩ := hx7
  obtain ⟨w7_264, hx7⟩ := hx7
  obtain ⟨w7_268, hx7⟩ := hx7
  obtain ⟨w7_378, hx7⟩ := hx7
  obtain ⟨w7_37c, hx7⟩ := hx7
  have K7_L := hx7
  exact .inr ⟨tl10_1, x1_0, x1_1, tl21_1, x1_2, x1_3, te30_1, x1_4, x1_5, tl2_2, x2_0, x2_1, op13_2, ol13_2, x2_2, to13_2, x2_3, x2_4, tl21_2, x2_5, x2_6, tl32_2, x2_7, x2_8, x2_9, te43_2, x2_10, tl2_3, x3_0, x3_1, te11_3, x3_2, x3_3, tl19_3, x3_4, op28_3, ol28_3, x3_5, to28_3, x3_6, x3_7, tl2_4, x4_0, x4_1, vp23_4, vl23_4, x4_2, te23_4, x4_3, x4_4, tr5_w328_5, tr5_w32c_5, x5_0, x5_1, tl2_6, x6_0, x6_1, tl13_6, x6_2, x6_3, x6_4, te25_6, x6_5, tl31_6, x6_6, x6_7, te39_6, x6_8, tl45_6, x6_9, x7_0, n7, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7)))))), fR7, s7, E7, V7,
    by rw [r7_3, r6_3, r5_3, r4_3, r3_3, r2_3, r1_3], by rw [r7_4, r6_4, r5_4, r4_4, r3_4, r2_4, r1_4], r7_2, r7_18, r7_19, r7_20, r7_21, r7_22, r7_23, r7_24, r7_25, r7_26, r7_27, w7_44, w7_50, w7_64, w7_7c, w7_25c, w7_260, w7_264, w7_268, w7_378, w7_37c, ((K7_L.w32 (by decide) (by decide)).trans w6_74), ((K7_L.w32 (by decide) (by decide)).trans w6_78), ((K7_L.w32 (by decide) (by decide)).trans w6_48), ((K7_L.w32 (by decide) (by decide)).trans w6_4c), ((K7_L.w32 (by decide) (by decide)).trans w6_424), ((K7_L.w32 (by decide) (by decide)).trans w6_428), ((K7_L.w32 (by decide) (by decide)).trans w6_42c), ((K7_L.w32 (by decide) (by decide)).trans w6_430), (((((((K1_L).trans K2_L).trans K3_L).trans K4_L).trans K5_L).trans K6_L).trans K7_L).mono (by decide)⟩

end C3.RV32.Sv
