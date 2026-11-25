import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvSegTr
import C3BootProofs.Proofs.SvSegAttrPre
import C3BootProofs.Proofs.SvAttrLoop
import C3BootProofs.Proofs.SvSegTt
import C3BootProofs.Proofs.SvTsv
import C3BootProofs.Proofs.SvTSearch
import C3BootProofs.Proofs.SvTsig
import C3BootProofs.Proofs.SvTp

/-!
# `sigstore::verify`: The timestamp

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **The timestamp**: from 0xA60 to the checkpoint at 0x142E: the timestamp response, its signed attributes, the `TSTInfo`, the TSA that signed it, and its signature. -/
theorem sv_seg_ts {B out bp x20 x21 x22 x23 x24 x25 x26 x27 tsp tsl : Word} {v : Nat → Word} {n0 : Machine} {w68 : Word} {w70 : Word}
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
    (D0 : SvData M0)
    (H' : ∀ i, i < 8 → ∀ c'_6 q'_6, (c'_6, q'_6) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((x21) + BitVec.ofNat 32 0x308)) → (SvIn B (q'_6 + 0x20) 4) ∧ (SvIn B (q'_6 + 0x24) 4) ∧ ((q'_6 + 0x20).toNat % 4 = 0) ∧ ((q'_6 + 0x24).toNat % 4 = 0) ∧ ((memLoad32 M0 (q'_6 + 0x20)) ≠ 0 → SvIn B (memLoad32 M0 (q'_6 + 0x20)) (memLoad32 M0 (q'_6 + 0x24)).toNat))
    (w0_68 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68)
    (w0_70 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70)
    (S2 : SvSha2Code M0)
    (RS : SvRoSep B)
    (sig_in : SvIn B w70 w68.toNat)
    (PE0 : PvEnv7 M0)
    (pkp_in : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (x21 + BitVec.ofNat 32 0x308)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (((y1) + BitVec.ofNat 32 0x20) + 0x18) 4)
    (apk : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (x21 + BitVec.ofNat 32 0x308)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → (((y1) + BitVec.ofNat 32 0x20) + 0x18).toNat % 4 = 0)
    (pk_in : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (x21 + BitVec.ofNat 32 0x308)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → SvIn B (memLoad32 M0 (((y1) + BitVec.ofNat 32 0x20) + 0x18)) 0x61)
    (side : ∀ i, i < 8 → ∀ y0 y1, (y0, y1) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), (x21 + BitVec.ofNat 32 0x308)) → (memLoad32 M0 (y1 + 0x20)) ≠ 0 → ∀ M, PvSide M (memLoad32 M0 (((y1) + BitVec.ofNat 32 0x20) + 0x18)) (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 (B + 0x21A0 + BitVec.ofNat 32 0x190)
      (B + 0x21A0 + BitVec.ofNat 32 0x1C0)) :
    SvErrRet B out v n0 ∨ Panics n0 ∨
    (∃ tl10_1_1, derElement 0x30 (memBytes M0 (tsp) (tsl).toNat) = .ok tl10_1_1 ∧
      ((tsl) - BitVec.ofNat 32 (tl10_1_1.header + tl10_1_1.len) = 0) ∧
      ∃ tl21_1_1, derElement 0x30 (memBytes M0 ((tsp) + BitVec.ofNat 32 tl10_1_1.header) (BitVec.ofNat 32 tl10_1_1.len).toNat) = .ok tl21_1_1 ∧
      derIntIsOf M0 (memBytes M0 (((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 tl21_1_1.header) (BitVec.ofNat 32 tl21_1_1.len).toNat) (((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 tl21_1_1.header) (derElement 2 (memBytes M0 (((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 tl21_1_1.header) (BitVec.ofNat 32 tl21_1_1.len).toNat)) ((BitVec.ofNat 32 0x0).extractLsb' 0 8) = .ok true ∧
      ∃ te30_1_1, derElement 2 (memBytes M0 (((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 tl21_1_1.header) (BitVec.ofNat 32 tl21_1_1.len).toNat) = .ok te30_1_1 ∧
      ((BitVec.ofNat 32 tl21_1_1.len) - BitVec.ofNat 32 (te30_1_1.header + te30_1_1.len) = 0) ∧
      ∃ tl2_2_1, derElement 0x30 (memBytes M0 ((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) (((BitVec.ofNat 32 tl10_1_1.len) - BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))).toNat) = .ok tl2_2_1 ∧
      ((((BitVec.ofNat 32 tl10_1_1.len) - BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) - BitVec.ofNat 32 (tl2_2_1.header + tl2_2_1.len) = 0) ∧
      ∃ op13_2_1 ol13_2_1, derContent (((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) (derOid (memBytes M0 (((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) (BitVec.ofNat 32 tl2_2_1.len).toNat)) = .ok (op13_2_1, ol13_2_1) ∧
      ∃ to13_2_1, derOid (memBytes M0 (((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) (BitVec.ofNat 32 tl2_2_1.len).toNat) = .ok to13_2_1 ∧
      (memBytes M0 op13_2_1 ol13_2_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress)) 9) ∧
      ∃ tl21_2_1, derElement 0xA0 (memBytes M0 ((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) ((BitVec.ofNat 32 tl2_2_1.len) - BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)).toNat) = .ok tl21_2_1 ∧
      (((BitVec.ofNat 32 tl2_2_1.len) - BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) - BitVec.ofNat 32 (tl21_2_1.header + tl21_2_1.len) = 0) ∧
      ∃ tl32_2_1, derElement 0x30 (memBytes M0 (((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) (BitVec.ofNat 32 tl21_2_1.len).toNat) = .ok tl32_2_1 ∧
      ((BitVec.ofNat 32 tl21_2_1.len) - BitVec.ofNat 32 (tl32_2_1.header + tl32_2_1.len) = 0) ∧
      derIntIsOf M0 (memBytes M0 ((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) (BitVec.ofNat 32 tl32_2_1.len).toNat) ((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) (derElement 2 (memBytes M0 ((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) (BitVec.ofNat 32 tl32_2_1.len).toNat)) ((BitVec.ofNat 32 0x3).extractLsb' 0 8) = .ok true ∧
      ∃ te43_2_1, derElement 2 (memBytes M0 ((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) (BitVec.ofNat 32 tl32_2_1.len).toNat) = .ok te43_2_1 ∧
      ∃ tl2_3_1, derElement 0x31 (memBytes M0 ((((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) + BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) (((BitVec.ofNat 32 tl32_2_1.len) - BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))).toNat) = .ok tl2_3_1 ∧
      isSha256Of M0 (((((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) + BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) + BitVec.ofNat 32 tl2_3_1.header) (BitVec.ofNat 32 tl2_3_1.len).toNat = .ok true ∧
      ∃ te11_3_1, derElement 0x30 (memBytes M0 (((((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) + BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) + BitVec.ofNat 32 tl2_3_1.header) (BitVec.ofNat 32 tl2_3_1.len).toNat) = .ok te11_3_1 ∧
      ((BitVec.ofNat 32 tl2_3_1.len) - BitVec.ofNat 32 (te11_3_1.header + te11_3_1.len) = 0) ∧
      ∃ tl19_3_1, derElement 0x30 (memBytes M0 (((((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) + BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) ((((BitVec.ofNat 32 tl32_2_1.len) - BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) - BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)).toNat) = .ok tl19_3_1 ∧
      ∃ op28_3_1 ol28_3_1, derContent ((((((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) + BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 tl19_3_1.header) (derOid (memBytes M0 ((((((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) + BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 tl19_3_1.header) (BitVec.ofNat 32 tl19_3_1.len).toNat)) = .ok (op28_3_1, ol28_3_1) ∧
      ∃ to28_3_1, derOid (memBytes M0 ((((((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) + BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 tl19_3_1.header) (BitVec.ofNat 32 tl19_3_1.len).toNat) = .ok to28_3_1 ∧
      (memBytes M0 op28_3_1 ol28_3_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x9)) 11) ∧
      ∃ tl2_4_1, derOptRes 0xA0 (memBytes M0 ((((((((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) + BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 tl19_3_1.header) + BitVec.ofNat 32 (to28_3_1.header + to28_3_1.len))) (((BitVec.ofNat 32 tl19_3_1.len) - BitVec.ofNat 32 (to28_3_1.header + to28_3_1.len))).toNat) = some (.ok tl2_4_1) ∧
      ((((BitVec.ofNat 32 tl19_3_1.len) - BitVec.ofNat 32 (to28_3_1.header + to28_3_1.len))) - BitVec.ofNat 32 (tl2_4_1.header + tl2_4_1.len) = 0) ∧
      ∃ vp23_4_1 vl23_4_1, derContent (((((((((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) + BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 tl19_3_1.header) + BitVec.ofNat 32 (to28_3_1.header + to28_3_1.len))) + BitVec.ofNat 32 tl2_4_1.header) (derElement 4 (memBytes M0 (((((((((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) + BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 tl19_3_1.header) + BitVec.ofNat 32 (to28_3_1.header + to28_3_1.len))) + BitVec.ofNat 32 tl2_4_1.header) (BitVec.ofNat 32 tl2_4_1.len).toNat)) = .ok (vp23_4_1, vl23_4_1) ∧
      ∃ te23_4_1, derElement 4 (memBytes M0 (((((((((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) + BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 tl19_3_1.header) + BitVec.ofNat 32 (to28_3_1.header + to28_3_1.len))) + BitVec.ofNat 32 tl2_4_1.header) (BitVec.ofNat 32 tl2_4_1.len).toNat) = .ok te23_4_1 ∧
      ((BitVec.ofNat 32 tl2_4_1.len) - BitVec.ofNat 32 (te23_4_1.header + te23_4_1.len) = 0) ∧
      ∃ tr5_w328_5_1 : Word, ∃ tr5_w32c_5_1 : Word, (((derOptRes 0xA0 (memBytes M0 (((((((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) + BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl19_3_1.header + tl19_3_1.len))) ((((((BitVec.ofNat 32 tl32_2_1.len) - BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) - BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) - BitVec.ofNat 32 (tl19_3_1.header + tl19_3_1.len))).toNat) = none) ∧ ((((((BitVec.ofNat 32 tl32_2_1.len) - BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) - BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) - BitVec.ofNat 32 (tl19_3_1.header + tl19_3_1.len)) = 0 ∨ (M0 (((((((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) + BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl19_3_1.header + tl19_3_1.len)))).toNat ≠ 0xA1) ∧ tr5_w328_5_1 = ((((((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) + BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl19_3_1.header + tl19_3_1.len)) ∧ tr5_w32c_5_1 = (((((BitVec.ofNat 32 tl32_2_1.len) - BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) - BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) - BitVec.ofNat 32 (tl19_3_1.header + tl19_3_1.len))) ∨ ((¬ (derOptRes 0xA0 (memBytes M0 (((((((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) + BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl19_3_1.header + tl19_3_1.len))) ((((((BitVec.ofNat 32 tl32_2_1.len) - BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) - BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) - BitVec.ofNat 32 (tl19_3_1.header + tl19_3_1.len))).toNat) = none)) ∧ ∃ tl2, derOptRes 0xA0 (memBytes M0 (((((((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) + BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl19_3_1.header + tl19_3_1.len))) ((((((BitVec.ofNat 32 tl32_2_1.len) - BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) - BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) - BitVec.ofNat 32 (tl19_3_1.header + tl19_3_1.len))).toNat) = some (.ok tl2) ∧ (((((((BitVec.ofNat 32 tl32_2_1.len) - BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) - BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) - BitVec.ofNat 32 (tl19_3_1.header + tl19_3_1.len))) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0 ∨ (M0 ((((((((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) + BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl19_3_1.header + tl19_3_1.len))) + BitVec.ofNat 32 (tl2.header + tl2.len))).toNat ≠ 0xA1) ∧ tr5_w328_5_1 = (((((((((((((tsp) + BitVec.ofNat 32 tl10_1_1.header) + BitVec.ofNat 32 (tl21_1_1.header + tl21_1_1.len))) + BitVec.ofNat 32 tl2_2_1.header) + BitVec.ofNat 32 (to13_2_1.header + to13_2_1.len)) + BitVec.ofNat 32 tl21_2_1.header) + BitVec.ofNat 32 tl32_2_1.header) + BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) + BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) + BitVec.ofNat 32 (tl19_3_1.header + tl19_3_1.len))) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tr5_w32c_5_1 = ((((((BitVec.ofNat 32 tl32_2_1.len) - BitVec.ofNat 32 (te43_2_1.header + te43_2_1.len))) - BitVec.ofNat 32 (tl2_3_1.header + tl2_3_1.len)) - BitVec.ofNat 32 (tl19_3_1.header + tl19_3_1.len))) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tr5_w328_5_1 tr5_w32c_5_1.toNat ∧
      ∃ tl2_6_1, derElement 0x31 (memBytes M0 (tr5_w328_5_1) (tr5_w32c_5_1).toNat) = .ok tl2_6_1 ∧
      ((tr5_w32c_5_1) - BitVec.ofNat 32 (tl2_6_1.header + tl2_6_1.len) = 0) ∧
      ∃ tl13_6_1, derElement 0x30 (memBytes M0 ((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) (BitVec.ofNat 32 tl2_6_1.len).toNat) = .ok tl13_6_1 ∧
      ((BitVec.ofNat 32 tl2_6_1.len) - BitVec.ofNat 32 (tl13_6_1.header + tl13_6_1.len) = 0) ∧
      derIntIsOf M0 (memBytes M0 (((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) (BitVec.ofNat 32 tl13_6_1.len).toNat) (((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) (derElement 2 (memBytes M0 (((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) (BitVec.ofNat 32 tl13_6_1.len).toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = .ok true ∧
      ∃ te25_6_1, derElement 2 (memBytes M0 (((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) (BitVec.ofNat 32 tl13_6_1.len).toNat) = .ok te25_6_1 ∧
      ∃ tl31_6_1, derElement 0x30 (memBytes M0 ((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) ((BitVec.ofNat 32 tl13_6_1.len) - BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)).toNat) = .ok tl31_6_1 ∧
      isSha256Of M0 (((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) (((BitVec.ofNat 32 tl13_6_1.len) - BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) - BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)).toNat = .ok true ∧
      ∃ te39_6_1, derElement 0x30 (memBytes M0 (((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) (((BitVec.ofNat 32 tl13_6_1.len) - BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) - BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)).toNat) = .ok te39_6_1 ∧
      ∃ tl45_6_1, derOptRes 0xA0 (memBytes M0 ((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) ((((BitVec.ofNat 32 tl13_6_1.len) - BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) - BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) - BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)).toNat) = some (.ok tl45_6_1) ∧
      ((BitVec.ofNat 32 tl45_6_1.len) ≠ 0) ∧
      (((BitVec.ofNat 32 tl45_6_1.len)).toNat ≤ ((BitVec.ofNat 32 tl45_6_1.len)).toNat) ∧
      ∃ tl6_1_2, derElement 0x30 (memBytes M0 ((((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 tl45_6_1.header)) ((BitVec.ofNat 32 tl45_6_1.len)).toNat) = .ok tl6_1_2 ∧
      ∃ op15_1_2 ol15_1_2, derContent (((((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 tl45_6_1.header)) + BitVec.ofNat 32 tl6_1_2.header) (derOid (memBytes M0 (((((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 tl45_6_1.header)) + BitVec.ofNat 32 tl6_1_2.header) (BitVec.ofNat 32 tl6_1_2.len).toNat)) = .ok (op15_1_2, ol15_1_2) ∧
      ∃ to15_1_2, derOid (memBytes M0 (((((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 tl45_6_1.header)) + BitVec.ofNat 32 tl6_1_2.header) (BitVec.ofNat 32 tl6_1_2.len).toNat) = .ok to15_1_2 ∧
      ∃ tl20_1_2, derElement 0x31 (memBytes M0 ((((((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 tl45_6_1.header)) + BitVec.ofNat 32 tl6_1_2.header) + BitVec.ofNat 32 (to15_1_2.header + to15_1_2.len)) ((BitVec.ofNat 32 tl6_1_2.len) - BitVec.ofNat 32 (to15_1_2.header + to15_1_2.len)).toNat) = .ok tl20_1_2 ∧
      (((BitVec.ofNat 32 tl6_1_2.len) - BitVec.ofNat 32 (to15_1_2.header + to15_1_2.len)) - BitVec.ofNat 32 (tl20_1_2.header + tl20_1_2.len) = 0) ∧
      listsOidOf M0 (((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 tl45_6_1.header) (((BitVec.ofNat 32 tl45_6_1.len)) - ((BitVec.ofNat 32 tl45_6_1.len))).toNat (memBytes M0 op15_1_2 ol15_1_2.toNat) = .ok false ∧
      ∃ trv_w64_2_2 : Word, ∃ trv_w7c_2_2 : Word, (((memBytes M0 op15_1_2 ol15_1_2.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9) ∧ ∃ op5 ol5, derContent ((((((((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 tl45_6_1.header)) + BitVec.ofNat 32 tl6_1_2.header) + BitVec.ofNat 32 (to15_1_2.header + to15_1_2.len)) + BitVec.ofNat 32 tl20_1_2.header)) (derOid (memBytes M0 ((((((((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 tl45_6_1.header)) + BitVec.ofNat 32 tl6_1_2.header) + BitVec.ofNat 32 (to15_1_2.header + to15_1_2.len)) + BitVec.ofNat 32 tl20_1_2.header)) ((BitVec.ofNat 32 tl20_1_2.len)).toNat)) = .ok (op5, ol5) ∧ ∃ to5, derOid (memBytes M0 ((((((((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 tl45_6_1.header)) + BitVec.ofNat 32 tl6_1_2.header) + BitVec.ofNat 32 (to15_1_2.header + to15_1_2.len)) + BitVec.ofNat 32 tl20_1_2.header)) ((BitVec.ofNat 32 tl20_1_2.len)).toNat) = .ok to5 ∧ (memBytes M0 op5 ol5.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x9)) 11) ∧ (((BitVec.ofNat 32 tl20_1_2.len)) - BitVec.ofNat 32 (to5.header + to5.len) = 0) ∧ trv_w64_2_2 = (BitVec.ofNat 32 0x0) ∧ trv_w7c_2_2 = BitVec.ofNat 32 0x1) ∨ ((¬ (memBytes M0 op15_1_2 ol15_1_2.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9)) ∧ (memBytes M0 op15_1_2 ol15_1_2.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x1E)) 9) ∧ ∃ vp8 vl8, derContent ((((((((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 tl45_6_1.header)) + BitVec.ofNat 32 tl6_1_2.header) + BitVec.ofNat 32 (to15_1_2.header + to15_1_2.len)) + BitVec.ofNat 32 tl20_1_2.header)) (derElement 4 (memBytes M0 ((((((((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 tl45_6_1.header)) + BitVec.ofNat 32 tl6_1_2.header) + BitVec.ofNat 32 (to15_1_2.header + to15_1_2.len)) + BitVec.ofNat 32 tl20_1_2.header)) ((BitVec.ofNat 32 tl20_1_2.len)).toNat)) = .ok (vp8, vl8) ∧ ∃ te8, derElement 4 (memBytes M0 ((((((((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 tl45_6_1.header)) + BitVec.ofNat 32 tl6_1_2.header) + BitVec.ofNat 32 (to15_1_2.header + to15_1_2.len)) + BitVec.ofNat 32 tl20_1_2.header)) ((BitVec.ofNat 32 tl20_1_2.len)).toNat) = .ok te8 ∧ (vl8 = 32) ∧ (((BitVec.ofNat 32 tl20_1_2.len)) - BitVec.ofNat 32 (te8.header + te8.len) = 0) ∧ trv_w64_2_2 = vp8 ∧ trv_w7c_2_2 = (BitVec.ofNat 32 0x0)) ∨ ((¬ (memBytes M0 op15_1_2 ol15_1_2.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9)) ∧ (¬ (memBytes M0 op15_1_2 ol15_1_2.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x1E)) 9)) ∧ trv_w64_2_2 = (BitVec.ofNat 32 0x0) ∧ trv_w7c_2_2 = (BitVec.ofNat 32 0x0))) ∧ (trv_w64_2_2 = 0 ∨ SvIn B trv_w64_2_2 32) ∧
      ∃ k_3 dg'_3 flag'_3 cp'_3 rem'_3, svChain (sv_attrStep B out bp x20 x21 x22 x23 (((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 tl45_6_1.header) (BitVec.ofNat 32 tl45_6_1.len) (((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 (tl45_6_1.header + tl45_6_1.len)) (((((BitVec.ofNat 32 tl13_6_1.len) - BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) - BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) - BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) - BitVec.ofNat 32 (tl45_6_1.header + tl45_6_1.len)) v M0) k_3 (trv_w64_2_2, trv_w7c_2_2, (((((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 tl45_6_1.header)) + BitVec.ofNat 32 (tl6_1_2.header + tl6_1_2.len)), (((BitVec.ofNat 32 tl45_6_1.len)) - BitVec.ofNat 32 (tl6_1_2.header + tl6_1_2.len))) (dg'_3, flag'_3, cp'_3, rem'_3) ∧
      rem'_3 = 0 ∧ (dg'_3 = 0 ∨ SvIn B dg'_3 32) ∧
      (dg'_3 ≠ 0 ∧ flag'_3 = 1) ∧ ∃ op9_3 ol9_3, derAlgOf M0 ((((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 (tl45_6_1.header + tl45_6_1.len))) (((((((BitVec.ofNat 32 tl13_6_1.len) - BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) - BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) - BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) - BitVec.ofNat 32 (tl45_6_1.header + tl45_6_1.len))).toNat) = .ok ((op9_3, ol9_3), none) ∧ ∃ te9_3, derElement 0x30 (memBytes M0 ((((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 (tl45_6_1.header + tl45_6_1.len))) ((((((BitVec.ofNat 32 tl13_6_1.len) - BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) - BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) - BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) - BitVec.ofNat 32 (tl45_6_1.header + tl45_6_1.len))).toNat) = .ok te9_3 ∧ (memBytes M0 op9_3 ol9_3 = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress)) 8) ∧ ∃ vp20_3 vl20_3, derContent (((((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 (tl45_6_1.header + tl45_6_1.len))) + BitVec.ofNat 32 (te9_3.header + te9_3.len)) (derElement 4 (memBytes M0 (((((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 (tl45_6_1.header + tl45_6_1.len))) + BitVec.ofNat 32 (te9_3.header + te9_3.len)) (((((((BitVec.ofNat 32 tl13_6_1.len) - BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) - BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) - BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) - BitVec.ofNat 32 (tl45_6_1.header + tl45_6_1.len))) - BitVec.ofNat 32 (te9_3.header + te9_3.len)).toNat)) = .ok (vp20_3, vl20_3) ∧ ∃ te20_3, derElement 4 (memBytes M0 (((((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) + BitVec.ofNat 32 (tl45_6_1.header + tl45_6_1.len))) + BitVec.ofNat 32 (te9_3.header + te9_3.len)) (((((((BitVec.ofNat 32 tl13_6_1.len) - BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) - BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) - BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) - BitVec.ofNat 32 (tl45_6_1.header + tl45_6_1.len))) - BitVec.ofNat 32 (te9_3.header + te9_3.len)).toNat) = .ok te20_3 ∧ ∃ sr25_3 ss25_3, ecdsaSigOf 48 M0 (vp20_3) ((vl20_3).toNat) = .ok (sr25_3, ss25_3) ∧ ((((((((BitVec.ofNat 32 tl13_6_1.len) - BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) - BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) - BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) - BitVec.ofNat 32 (tl45_6_1.header + tl45_6_1.len))) - BitVec.ofNat 32 (te9_3.header + te9_3.len)) - BitVec.ofNat 32 (te20_3.header + te20_3.len) = 0) ∧
      ∃ tl9_1_4, derElement 0x30 (memBytes M0 (vp23_4_1) (vl23_4_1).toNat) = .ok tl9_1_4 ∧
      ((vl23_4_1) - BitVec.ofNat 32 (tl9_1_4.header + tl9_1_4.len) = 0) ∧
      derIntIsOf M0 (memBytes M0 ((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) (BitVec.ofNat 32 tl9_1_4.len).toNat) ((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) (derElement 2 (memBytes M0 ((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) (BitVec.ofNat 32 tl9_1_4.len).toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = .ok true ∧
      ∃ te20_1_4, derElement 2 (memBytes M0 ((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) (BitVec.ofNat 32 tl9_1_4.len).toNat) = .ok te20_1_4 ∧
      ∃ op26_1_4 ol26_1_4, derContent (((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) + BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) (derOid (memBytes M0 (((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) + BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) ((BitVec.ofNat 32 tl9_1_4.len) - BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)).toNat)) = .ok (op26_1_4, ol26_1_4) ∧
      ∃ to26_1_4, derOid (memBytes M0 (((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) + BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) ((BitVec.ofNat 32 tl9_1_4.len) - BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)).toNat) = .ok to26_1_4 ∧
      ∃ tl30_1_4, derElement 0x30 (memBytes M0 ((((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) + BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) + BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) (((BitVec.ofNat 32 tl9_1_4.len) - BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) - BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)).toNat) = .ok tl30_1_4 ∧
      isSha256Of M0 (((((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) + BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) + BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) + BitVec.ofNat 32 tl30_1_4.header) (BitVec.ofNat 32 tl30_1_4.len).toNat = .ok true ∧
      ∃ te39_1_4, derElement 0x30 (memBytes M0 (((((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) + BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) + BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) + BitVec.ofNat 32 tl30_1_4.header) (BitVec.ofNat 32 tl30_1_4.len).toNat) = .ok te39_1_4 ∧
      ∃ vp45_1_4 vl45_1_4, derContent ((((((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) + BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) + BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) + BitVec.ofNat 32 tl30_1_4.header) + BitVec.ofNat 32 (te39_1_4.header + te39_1_4.len)) (derElement 4 (memBytes M0 ((((((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) + BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) + BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) + BitVec.ofNat 32 tl30_1_4.header) + BitVec.ofNat 32 (te39_1_4.header + te39_1_4.len)) ((BitVec.ofNat 32 tl30_1_4.len) - BitVec.ofNat 32 (te39_1_4.header + te39_1_4.len)).toNat)) = .ok (vp45_1_4, vl45_1_4) ∧
      ∃ te45_1_4, derElement 4 (memBytes M0 ((((((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) + BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) + BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) + BitVec.ofNat 32 tl30_1_4.header) + BitVec.ofNat 32 (te39_1_4.header + te39_1_4.len)) ((BitVec.ofNat 32 tl30_1_4.len) - BitVec.ofNat 32 (te39_1_4.header + te39_1_4.len)).toNat) = .ok te45_1_4 ∧
      (vl45_1_4 = 32) ∧
      (((BitVec.ofNat 32 tl30_1_4.len) - BitVec.ofNat 32 (te39_1_4.header + te39_1_4.len)) - BitVec.ofNat 32 (te45_1_4.header + te45_1_4.len) = 0) ∧
      ∃ tl2_2_4, derElement 2 (memBytes M0 ((((((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) + BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) + BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) + BitVec.ofNat 32 (tl30_1_4.header + tl30_1_4.len))) (((((BitVec.ofNat 32 tl9_1_4.len) - BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) - BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) - BitVec.ofNat 32 (tl30_1_4.header + tl30_1_4.len))).toNat) = .ok tl2_2_4 ∧
      ∃ ip2_2_4 il2_2_4, derPosIntOf (memBytes M0 ((((((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) + BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) + BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) + BitVec.ofNat 32 (tl30_1_4.header + tl30_1_4.len))) (((((BitVec.ofNat 32 tl9_1_4.len) - BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) - BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) - BitVec.ofNat 32 (tl30_1_4.header + tl30_1_4.len))).toNat) ((((((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) + BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) + BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) + BitVec.ofNat 32 (tl30_1_4.header + tl30_1_4.len))) (.ok tl2_2_4) = .ok (ip2_2_4, il2_2_4) ∧
      (((il2_2_4) - (aluEval .sltu ((M0 (ip2_2_4)).zeroExtend 32) 1)).toNat ≤ 20) ∧
      ∃ tl13_2_4, derElement 0x18 (memBytes M0 (((((((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) + BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) + BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) + BitVec.ofNat 32 (tl30_1_4.header + tl30_1_4.len))) + BitVec.ofNat 32 (tl2_2_4.header + tl2_2_4.len)) ((((((BitVec.ofNat 32 tl9_1_4.len) - BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) - BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) - BitVec.ofNat 32 (tl30_1_4.header + tl30_1_4.len))) - BitVec.ofNat 32 (tl2_2_4.header + tl2_2_4.len)).toNat) = .ok tl13_2_4 ∧
      ∃ tm18_2_4, generalizedTime (memBytes M0 ((((((((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) + BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) + BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) + BitVec.ofNat 32 (tl30_1_4.header + tl30_1_4.len))) + BitVec.ofNat 32 (tl2_2_4.header + tl2_2_4.len)) + BitVec.ofNat 32 tl13_2_4.header) ((BitVec.ofNat 32 tl13_2_4.len).toNat)) = some tm18_2_4 ∧
      ∃ tt3_w264_3_4 : Word, ∃ tt3_w268_3_4 : Word, (((derOptRes 0x30 (memBytes M0 (((((((((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) + BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) + BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) + BitVec.ofNat 32 (tl30_1_4.header + tl30_1_4.len))) + BitVec.ofNat 32 (tl2_2_4.header + tl2_2_4.len)) + BitVec.ofNat 32 (tl13_2_4.header + tl13_2_4.len))) ((((((((BitVec.ofNat 32 tl9_1_4.len) - BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) - BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) - BitVec.ofNat 32 (tl30_1_4.header + tl30_1_4.len))) - BitVec.ofNat 32 (tl2_2_4.header + tl2_2_4.len)) - BitVec.ofNat 32 (tl13_2_4.header + tl13_2_4.len))).toNat) = none) ∧ tt3_w264_3_4 = ((((((((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) + BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) + BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) + BitVec.ofNat 32 (tl30_1_4.header + tl30_1_4.len))) + BitVec.ofNat 32 (tl2_2_4.header + tl2_2_4.len)) + BitVec.ofNat 32 (tl13_2_4.header + tl13_2_4.len)) ∧ tt3_w268_3_4 = (((((((BitVec.ofNat 32 tl9_1_4.len) - BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) - BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) - BitVec.ofNat 32 (tl30_1_4.header + tl30_1_4.len))) - BitVec.ofNat 32 (tl2_2_4.header + tl2_2_4.len)) - BitVec.ofNat 32 (tl13_2_4.header + tl13_2_4.len))) ∨ ((¬ (derOptRes 0x30 (memBytes M0 (((((((((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) + BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) + BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) + BitVec.ofNat 32 (tl30_1_4.header + tl30_1_4.len))) + BitVec.ofNat 32 (tl2_2_4.header + tl2_2_4.len)) + BitVec.ofNat 32 (tl13_2_4.header + tl13_2_4.len))) ((((((((BitVec.ofNat 32 tl9_1_4.len) - BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) - BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) - BitVec.ofNat 32 (tl30_1_4.header + tl30_1_4.len))) - BitVec.ofNat 32 (tl2_2_4.header + tl2_2_4.len)) - BitVec.ofNat 32 (tl13_2_4.header + tl13_2_4.len))).toNat) = none)) ∧ ∃ tl2, derOptRes 0x30 (memBytes M0 (((((((((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) + BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) + BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) + BitVec.ofNat 32 (tl30_1_4.header + tl30_1_4.len))) + BitVec.ofNat 32 (tl2_2_4.header + tl2_2_4.len)) + BitVec.ofNat 32 (tl13_2_4.header + tl13_2_4.len))) ((((((((BitVec.ofNat 32 tl9_1_4.len) - BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) - BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) - BitVec.ofNat 32 (tl30_1_4.header + tl30_1_4.len))) - BitVec.ofNat 32 (tl2_2_4.header + tl2_2_4.len)) - BitVec.ofNat 32 (tl13_2_4.header + tl13_2_4.len))).toNat) = some (.ok tl2) ∧ tt3_w264_3_4 = (((((((((vp23_4_1) + BitVec.ofNat 32 tl9_1_4.header) + BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) + BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) + BitVec.ofNat 32 (tl30_1_4.header + tl30_1_4.len))) + BitVec.ofNat 32 (tl2_2_4.header + tl2_2_4.len)) + BitVec.ofNat 32 (tl13_2_4.header + tl13_2_4.len))) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tt3_w268_3_4 = ((((((((BitVec.ofNat 32 tl9_1_4.len) - BitVec.ofNat 32 (te20_1_4.header + te20_1_4.len)) - BitVec.ofNat 32 (to26_1_4.header + to26_1_4.len)) - BitVec.ofNat 32 (tl30_1_4.header + tl30_1_4.len))) - BitVec.ofNat 32 (tl2_2_4.header + tl2_2_4.len)) - BitVec.ofNat 32 (tl13_2_4.header + tl13_2_4.len))) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tt3_w264_3_4 tt3_w268_3_4.toNat ∧
      ∃ tt4_w264_4_4 : Word, ∃ tt4_w268_4_4 : Word, (((tt3_w268_3_4 = 0) ∧ tt4_w264_4_4 = tt3_w264_3_4 ∧ tt4_w268_4_4 = tt3_w268_3_4) ∨ ((¬ (tt3_w268_3_4 = 0)) ∧ (M0 tt3_w264_3_4 = BitVec.ofNat 8 1) ∧ derBoolOf (memBytes M0 (tt3_w264_3_4) (tt3_w268_3_4).toNat) (derElement 1 (memBytes M0 (tt3_w264_3_4) (tt3_w268_3_4).toNat)) = .ok () ∧ ∃ tb8_1, derElement 1 (memBytes M0 (tt3_w264_3_4) (tt3_w268_3_4).toNat) = .ok tb8_1 ∧ ∃ tt4b_w264_2 : Word, ∃ tt4b_w268_2 : Word, (((((tt3_w268_3_4) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = 0) ∧ tt4b_w264_2 = ((tt3_w264_3_4) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) ∧ tt4b_w268_2 = ((tt3_w268_3_4) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) ∨ ((¬ (((tt3_w268_3_4) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = 0)) ∧ ∃ tt4n_w264_2 : Word, ∃ tt4n_w268_2 : Word, (((M0 ((tt3_w264_3_4) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = BitVec.ofNat 8 2) ∧ ∃ ip4 il4, derIntOf (memBytes M0 (((tt3_w264_3_4) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (((tt3_w268_3_4) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))).toNat) (((tt3_w264_3_4) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (derElement 2 (memBytes M0 (((tt3_w264_3_4) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (((tt3_w268_3_4) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))).toNat)) = .ok (ip4, il4) ∧ ∃ ti4, derElement 2 (memBytes M0 (((tt3_w264_3_4) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (((tt3_w268_3_4) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))).toNat) = .ok ti4 ∧ tt4n_w264_2 = (((tt3_w264_3_4) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) + BitVec.ofNat 32 (ti4.header + ti4.len) ∧ tt4n_w268_2 = (((tt3_w268_3_4) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) - BitVec.ofNat 32 (ti4.header + ti4.len)) ∨ ((¬ (M0 ((tt3_w264_3_4) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = BitVec.ofNat 8 2)) ∧ tt4n_w264_2 = ((tt3_w264_3_4) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) ∧ tt4n_w268_2 = ((tt3_w268_3_4) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len)))) ∧ SvIn B tt4n_w264_2 tt4n_w268_2.toNat ∧ tt4b_w264_2 = tt4n_w264_2 ∧ tt4b_w268_2 = tt4n_w268_2)) ∧ SvIn B tt4b_w264_2 tt4b_w268_2.toNat ∧ tt4_w264_4_4 = tt4b_w264_2 ∧ tt4_w268_4_4 = tt4b_w268_2) ∨ ((¬ (tt3_w268_3_4 = 0)) ∧ (¬ (M0 tt3_w264_3_4 = BitVec.ofNat 8 1)) ∧ ∃ tt4n_w264_2 : Word, ∃ tt4n_w268_2 : Word, (((M0 tt3_w264_3_4 = BitVec.ofNat 8 2) ∧ ∃ ip4 il4, derIntOf (memBytes M0 (tt3_w264_3_4) (tt3_w268_3_4).toNat) (tt3_w264_3_4) (derElement 2 (memBytes M0 (tt3_w264_3_4) (tt3_w268_3_4).toNat)) = .ok (ip4, il4) ∧ ∃ ti4, derElement 2 (memBytes M0 (tt3_w264_3_4) (tt3_w268_3_4).toNat) = .ok ti4 ∧ tt4n_w264_2 = (tt3_w264_3_4) + BitVec.ofNat 32 (ti4.header + ti4.len) ∧ tt4n_w268_2 = (tt3_w268_3_4) - BitVec.ofNat 32 (ti4.header + ti4.len)) ∨ ((¬ (M0 tt3_w264_3_4 = BitVec.ofNat 8 2)) ∧ tt4n_w264_2 = tt3_w264_3_4 ∧ tt4n_w268_2 = tt3_w268_3_4)) ∧ SvIn B tt4n_w264_2 tt4n_w268_2.toNat ∧ tt4_w264_4_4 = tt4n_w264_2 ∧ tt4_w268_4_4 = tt4n_w268_2)) ∧ SvIn B tt4_w264_4_4 tt4_w268_4_4.toNat ∧
      ∃ tt5_w264_5_4 : Word, ∃ tt5_w268_5_4 : Word, (((derOptRes 0xA0 (memBytes M0 (tt4_w264_4_4) (tt4_w268_4_4).toNat) = none) ∧ tt5_w264_5_4 = tt4_w264_4_4 ∧ tt5_w268_5_4 = tt4_w268_4_4) ∨ ((¬ (derOptRes 0xA0 (memBytes M0 (tt4_w264_4_4) (tt4_w268_4_4).toNat) = none)) ∧ ∃ tl2, derOptRes 0xA0 (memBytes M0 (tt4_w264_4_4) (tt4_w268_4_4).toNat) = some (.ok tl2) ∧ tt5_w264_5_4 = (tt4_w264_4_4) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tt5_w268_5_4 = (tt4_w268_4_4) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tt5_w264_5_4 tt5_w268_5_4.toNat ∧
      ∃ tt6_w264_6_4 : Word, ∃ tt6_w268_6_4 : Word, (((derOptRes 0xA1 (memBytes M0 (tt5_w264_5_4) (tt5_w268_5_4).toNat) = none) ∧ (tt5_w268_5_4 = 0) ∧ tt6_w264_6_4 = tt5_w264_5_4 ∧ tt6_w268_6_4 = tt5_w268_5_4) ∨ ((¬ (derOptRes 0xA1 (memBytes M0 (tt5_w264_5_4) (tt5_w268_5_4).toNat) = none)) ∧ ∃ tl2, derOptRes 0xA1 (memBytes M0 (tt5_w264_5_4) (tt5_w268_5_4).toNat) = some (.ok tl2) ∧ ((tt5_w268_5_4) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0) ∧ tt6_w264_6_4 = (tt5_w264_5_4) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tt6_w268_6_4 = (tt5_w268_5_4) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tt6_w264_6_4 tt6_w268_6_4.toNat ∧
      ∃ k_6, k_6 < 8 ∧
      (∀ i, i < k_6 → ∀ c'_6 q'_6, (c'_6, q'_6) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) i ((BitVec.ofNat 32 0x100), ((x21) + BitVec.ofNat 32 0x308)) → ¬ (memBytes M0 (memLoad32 M0 (q'_6 + 0x20)) (memLoad32 M0 (q'_6 + 0x24)).toNat = memBytes M0 ((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) (BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)).toNat)) ∧
      ∃ c'_6 q'_6, (c'_6, q'_6) = svIter (fun s => (((s.1)) + BitVec.ofNat 32 0xFFFFFFE0, ((s.2)) + BitVec.ofNat 32 0x20)) k_6 ((BitVec.ofNat 32 0x100), ((x21) + BitVec.ofNat 32 0x308)) ∧ (memBytes M0 (memLoad32 M0 (q'_6 + 0x20)) (memLoad32 M0 (q'_6 + 0x24)).toNat = memBytes M0 ((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) (BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)).toNat) ∧
      ((memLoad32 M0 (q'_6 + 0x20)) ≠ 0) ∧
      (sha256 (memBytes M0 (vp23_4_1) (vl23_4_1).toNat) = memBytes M0 dg'_3 32) ∧
      (sha256 (memBytes M0 (w70) (w68).toNat) = memBytes M0 vp45_1_4 32) ∧
      ((BitVec.ofNat 32 (tl45_6_1.header + tl45_6_1.len)) ≠ 0) ∧
      ∃ pv_8, SvPvRes M0 (memLoad32 M0 (((q'_6) + BitVec.ofNat 32 0x20) + 0x18)) (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 (sha256 (memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x14)) (1) ++ memBytes M0 ((((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len))) + BitVec.ofNat 32 0x1) ((((BitVec.ofNat 32 (tl45_6_1.header + tl45_6_1.len))) + BitVec.ofNat 32 0xFFFFFFFF).toNat))) (B + 0x21A0 + BitVec.ofNat 32 0x190) (B + 0x21A0 + BitVec.ofNat 32 0x1C0) sr25_3 ss25_3 (some pv_8) ∧
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0x142E (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' a0 = pv_8 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = (memLoad32 M0 (q'_6 + 0x20)) ∧
        reg n' (25 : Fin 32) = (memLoad32 M0 (q'_6 + 0x24)) ∧
        reg n' (26 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x190 ∧
        reg n' (27 : Fin 32) = vp45_1_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = ((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = (BitVec.ofNat 32 (tl45_6_1.header + tl45_6_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg'_3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = (BitVec.ofNat 32 (tm18_2_4 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = tt6_w264_6_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = tt6_w268_6_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = vp23_4_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = ((q'_6) + BitVec.ofNat 32 0x20) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = (BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = ((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = (BitVec.ofNat 32 (tm18_2_4 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) = vp23_4_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x174) = vl23_4_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x178) = ((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x17C) = (BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x180) = ((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x184) = (BitVec.ofNat 32 (tl45_6_1.header + tl45_6_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x188) = (BitVec.ofNat 32 (tm18_2_4 % 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x18C) = (BitVec.ofNat 32 (tm18_2_4 / 2 ^ 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F0) = vp45_1_4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1F4) = dg'_3 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x190) = BitVec.ofNat 8 (sr25_3.getD 0 0) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = BitVec.ofNat 32 (img% svConstCmsAddress + 0x14) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = (((((((tr5_w328_5_1) + BitVec.ofNat 32 tl2_6_1.header) + BitVec.ofNat 32 tl13_6_1.header) + BitVec.ofNat 32 (te25_6_1.header + te25_6_1.len)) + BitVec.ofNat 32 (tl31_6_1.header + tl31_6_1.len)) + BitVec.ofNat 32 (te39_6_1.header + te39_6_1.len))) + BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = ((BitVec.ofNat 32 (tl45_6_1.header + tl45_6_1.len))) + BitVec.ofNat 32 0xFFFFFFFF ∧
        SvKeepL B n0.mem n'.mem [(0x2D0, 0x4), (0x2D4, 0x4), (0x2D8, 0x4), (0x2DC, 0x4), (0x420, 0x10), (0x2D8, 0x8), (0x2E5, 0xB), (0x2E0, 0x4), (0x2E4, 0x1), (0x420, 0x10), (0x2E8, 0x8), (0x2F5, 0xB), (0x2F0, 0x4), (0x2F4, 0x1), (0x2F8, 0x8), (0x305, 0xB), (0x300, 0x4), (0x304, 0x1), (0x420, 0x8), (0x308, 0x8), (0x308, 0x8), (0x315, 0xB), (0x310, 0x4), (0x314, 0x1), (0x318, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x328, 0x8), (0x335, 0xB), (0x330, 0x4), (0x334, 0x1), (0x338, 0x8), (0x345, 0xB), (0x340, 0x4), (0x344, 0x1), (0x348, 0x8), (0x420, 0x18), (0x350, 0x4), (0x354, 0x1), (0x355, 0x1), (0x356, 0x1), (0x357, 0x1), (0x358, 0x4), (0x35C, 0x4), (0x358, 0x8), (0x74, 0x4), (0x78, 0x4), (0x365, 0xB), (0x360, 0x4), (0x364, 0x1), (0x368, 0x8), (0x375, 0xB), (0x370, 0x4), (0x374, 0x1), (0x378, 0x8), (0x420, 0x11), (0x378, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x378, 0x8), (0x378, 0x8), (0x64, 0x4), (0x7C, 0x4), (0x44, 0x4), (0x50, 0x4), (0x25C, 0x4), (0x260, 0x4), (0x264, 0x4), (0x268, 0x4), (0x40, 0x4), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x408, 0x8), (0x420, 0x1C), (0x400, 0x8), (0x420, 0x61), (0x380, 0x5F), (0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x284, 0x8), (0x261, 0xB), (0x260, 0x1), (0x400, 0x10), (0x3C, 0x4), (0x1FC, 0x5F), (0x175, 0x1), (0x176, 0x1), (0x177, 0x1), (0x178, 0x4), (0x17C, 0x4), (0x180, 0x4), (0x184, 0x4), (0x190, 0x1), (0x191, 0x5F), (0x1F0, 0x4), (0x1F4, 0x4), (0x170, 0x4), (0x174, 0x1), (0x188, 0x4), (0x18C, 0x4), (0x420, 0x20), (0x420, 0x20), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x20)]) := by
  rcases sv_seg_tr FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 htsp htsl htsp_in htsl_in atsp atsl ts_in D0 with e | hx1
  · exact .inl e
  obtain ⟨tl10_1_1, hx1⟩ := hx1
  obtain ⟨x1_0, hx1⟩ := hx1
  obtain ⟨x1_1, hx1⟩ := hx1
  obtain ⟨tl21_1_1, hx1⟩ := hx1
  obtain ⟨x1_2, hx1⟩ := hx1
  obtain ⟨x1_3, hx1⟩ := hx1
  obtain ⟨te30_1_1, hx1⟩ := hx1
  obtain ⟨x1_4, hx1⟩ := hx1
  obtain ⟨x1_5, hx1⟩ := hx1
  obtain ⟨tl2_2_1, hx1⟩ := hx1
  obtain ⟨x1_6, hx1⟩ := hx1
  obtain ⟨x1_7, hx1⟩ := hx1
  obtain ⟨op13_2_1, hx1⟩ := hx1
  obtain ⟨ol13_2_1, hx1⟩ := hx1
  obtain ⟨x1_8, hx1⟩ := hx1
  obtain ⟨to13_2_1, hx1⟩ := hx1
  obtain ⟨x1_9, hx1⟩ := hx1
  obtain ⟨x1_10, hx1⟩ := hx1
  obtain ⟨tl21_2_1, hx1⟩ := hx1
  obtain ⟨x1_11, hx1⟩ := hx1
  obtain ⟨x1_12, hx1⟩ := hx1
  obtain ⟨tl32_2_1, hx1⟩ := hx1
  obtain ⟨x1_13, hx1⟩ := hx1
  obtain ⟨x1_14, hx1⟩ := hx1
  obtain ⟨x1_15, hx1⟩ := hx1
  obtain ⟨te43_2_1, hx1⟩ := hx1
  obtain ⟨x1_16, hx1⟩ := hx1
  obtain ⟨tl2_3_1, hx1⟩ := hx1
  obtain ⟨x1_17, hx1⟩ := hx1
  obtain ⟨x1_18, hx1⟩ := hx1
  obtain ⟨te11_3_1, hx1⟩ := hx1
  obtain ⟨x1_19, hx1⟩ := hx1
  obtain ⟨x1_20, hx1⟩ := hx1
  obtain ⟨tl19_3_1, hx1⟩ := hx1
  obtain ⟨x1_21, hx1⟩ := hx1
  obtain ⟨op28_3_1, hx1⟩ := hx1
  obtain ⟨ol28_3_1, hx1⟩ := hx1
  obtain ⟨x1_22, hx1⟩ := hx1
  obtain ⟨to28_3_1, hx1⟩ := hx1
  obtain ⟨x1_23, hx1⟩ := hx1
  obtain ⟨x1_24, hx1⟩ := hx1
  obtain ⟨tl2_4_1, hx1⟩ := hx1
  obtain ⟨x1_25, hx1⟩ := hx1
  obtain ⟨x1_26, hx1⟩ := hx1
  obtain ⟨vp23_4_1, hx1⟩ := hx1
  obtain ⟨vl23_4_1, hx1⟩ := hx1
  obtain ⟨x1_27, hx1⟩ := hx1
  obtain ⟨te23_4_1, hx1⟩ := hx1
  obtain ⟨x1_28, hx1⟩ := hx1
  obtain ⟨x1_29, hx1⟩ := hx1
  obtain ⟨tr5_w328_5_1, hx1⟩ := hx1
  obtain ⟨tr5_w32c_5_1, hx1⟩ := hx1
  obtain ⟨x1_30, hx1⟩ := hx1
  obtain ⟨x1_31, hx1⟩ := hx1
  obtain ⟨tl2_6_1, hx1⟩ := hx1
  obtain ⟨x1_32, hx1⟩ := hx1
  obtain ⟨x1_33, hx1⟩ := hx1
  obtain ⟨tl13_6_1, hx1⟩ := hx1
  obtain ⟨x1_34, hx1⟩ := hx1
  obtain ⟨x1_35, hx1⟩ := hx1
  obtain ⟨x1_36, hx1⟩ := hx1
  obtain ⟨te25_6_1, hx1⟩ := hx1
  obtain ⟨x1_37, hx1⟩ := hx1
  obtain ⟨tl31_6_1, hx1⟩ := hx1
  obtain ⟨x1_38, hx1⟩ := hx1
  obtain ⟨x1_39, hx1⟩ := hx1
  obtain ⟨te39_6_1, hx1⟩ := hx1
  obtain ⟨x1_40, hx1⟩ := hx1
  obtain ⟨tl45_6_1, hx1⟩ := hx1
  obtain ⟨x1_41, hx1⟩ := hx1
  obtain ⟨x1_42, hx1⟩ := hx1
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
  obtain ⟨r1_25, hx1⟩ := hx1
  obtain ⟨r1_26, hx1⟩ := hx1
  obtain ⟨r1_27, hx1⟩ := hx1
  obtain ⟨w1_44, hx1⟩ := hx1
  obtain ⟨w1_50, hx1⟩ := hx1
  obtain ⟨w1_64, hx1⟩ := hx1
  obtain ⟨w1_7c, hx1⟩ := hx1
  obtain ⟨w1_25c, hx1⟩ := hx1
  obtain ⟨w1_260, hx1⟩ := hx1
  obtain ⟨w1_264, hx1⟩ := hx1
  obtain ⟨w1_268, hx1⟩ := hx1
  obtain ⟨w1_378, hx1⟩ := hx1
  obtain ⟨w1_37c, hx1⟩ := hx1
  obtain ⟨w1_74, hx1⟩ := hx1
  obtain ⟨w1_78, hx1⟩ := hx1
  obtain ⟨w1_48, hx1⟩ := hx1
  obtain ⟨w1_4c, hx1⟩ := hx1
  obtain ⟨w1_424, hx1⟩ := hx1
  obtain ⟨w1_428, hx1⟩ := hx1
  obtain ⟨w1_42c, hx1⟩ := hx1
  obtain ⟨w1_430, hx1⟩ := hx1
  have K1_L := hx1
  rcases sv_seg_attr_pre FW E1 V1 hret hO s1 M0 fR1 r1_2 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 r1_24 r1_25 r1_26 r1_27 w1_64 w1_7c w1_25c w1_260 w1_264 w1_268 w1_378 w1_37c ((((((((((x1_31).content x1_32).ofNatLen).content x1_34).ofNatLen).restW x1_37).restW x1_38).restW x1_40).content (opt_ok_elem x1_41)).ofNatLen) ((((((((((x1_31).content x1_32).ofNatLen).content x1_34).ofNatLen).restW x1_37).restW x1_38).restW x1_40).content (opt_ok_elem x1_41)).ofNatLen) (((((((((x1_31).content x1_32).ofNatLen).content x1_34).ofNatLen).restW x1_37).restW x1_38).restW x1_40).restW (opt_ok_elem x1_41)) (.inl rfl) with e | hx2
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  obtain ⟨x2_0, hx2⟩ := hx2
  obtain ⟨tl6_1_2, hx2⟩ := hx2
  obtain ⟨x2_1, hx2⟩ := hx2
  obtain ⟨op15_1_2, hx2⟩ := hx2
  obtain ⟨ol15_1_2, hx2⟩ := hx2
  obtain ⟨x2_2, hx2⟩ := hx2
  obtain ⟨to15_1_2, hx2⟩ := hx2
  obtain ⟨x2_3, hx2⟩ := hx2
  obtain ⟨tl20_1_2, hx2⟩ := hx2
  obtain ⟨x2_4, hx2⟩ := hx2
  obtain ⟨x2_5, hx2⟩ := hx2
  obtain ⟨x2_6, hx2⟩ := hx2
  obtain ⟨trv_w64_2_2, hx2⟩ := hx2
  obtain ⟨trv_w7c_2_2, hx2⟩ := hx2
  obtain ⟨x2_7, hx2⟩ := hx2
  obtain ⟨x2_8, hx2⟩ := hx2
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
  obtain ⟨r2_20, hx2⟩ := hx2
  obtain ⟨r2_21, hx2⟩ := hx2
  obtain ⟨r2_22, hx2⟩ := hx2
  obtain ⟨r2_23, hx2⟩ := hx2
  obtain ⟨r2_24, hx2⟩ := hx2
  obtain ⟨r2_25, hx2⟩ := hx2
  obtain ⟨r2_26, hx2⟩ := hx2
  obtain ⟨r2_27, hx2⟩ := hx2
  obtain ⟨w2_64, hx2⟩ := hx2
  obtain ⟨w2_7c, hx2⟩ := hx2
  obtain ⟨w2_25c, hx2⟩ := hx2
  obtain ⟨w2_260, hx2⟩ := hx2
  obtain ⟨w2_264, hx2⟩ := hx2
  obtain ⟨w2_268, hx2⟩ := hx2
  obtain ⟨w2_378, hx2⟩ := hx2
  obtain ⟨w2_37c, hx2⟩ := hx2
  have K2_L := hx2
  rcases sv_attrloop_st FW hret hO M0 (Nat.le_refl _) (by rcases x2_7 with ⟨_, _, _, _, _, _, _, _, _, hd0⟩ | ⟨_, _, _, _, _, _, _, _, _, _, hd0⟩ | ⟨_, _, _, hd0⟩ <;> rw [hd0] <;> decide) E2 V2 s2 fR2 r2_2 r2_18 r2_19 r2_20 r2_21 r2_22 r2_23 w2_64 w2_7c w2_25c w2_260 w2_264 w2_268 w2_378 w2_37c (((((((((((x1_31).content x1_32).ofNatLen).content x1_34).ofNatLen).restW x1_37).restW x1_38).restW x1_40).content (opt_ok_elem x1_41)).ofNatLen).restW x2_1) ((((((((((x1_31).content x1_32).ofNatLen).content x1_34).ofNatLen).restW x1_37).restW x1_38).restW x1_40).content (opt_ok_elem x1_41)).ofNatLen) (((((((((x1_31).content x1_32).ofNatLen).content x1_34).ofNatLen).restW x1_37).restW x1_38).restW x1_40).restW (opt_ok_elem x1_41)) x2_8 with e | hx3
  · exact .inl (SvErrRet.pre (c1.trans (c2)) (by rw [r2_3, r1_3]) (by rw [r2_4, r1_4])
      (fun x hx => (fR2 x hx).trans (fM x hx).symm) e)
  obtain ⟨k_3, hx3⟩ := hx3
  obtain ⟨dg'_3, hx3⟩ := hx3
  obtain ⟨flag'_3, hx3⟩ := hx3
  obtain ⟨cp'_3, hx3⟩ := hx3
  obtain ⟨rem'_3, hx3⟩ := hx3
  obtain ⟨x3_0, hx3⟩ := hx3
  obtain ⟨x3_1, hx3⟩ := hx3
  obtain ⟨x3_2, hx3⟩ := hx3
  obtain ⟨x3_3, hx3⟩ := hx3
  obtain ⟨op9_3, hx3⟩ := hx3
  obtain ⟨ol9_3, hx3⟩ := hx3
  obtain ⟨x3_4, hx3⟩ := hx3
  obtain ⟨te9_3, hx3⟩ := hx3
  obtain ⟨x3_5, hx3⟩ := hx3
  obtain ⟨x3_6, hx3⟩ := hx3
  obtain ⟨vp20_3, hx3⟩ := hx3
  obtain ⟨vl20_3, hx3⟩ := hx3
  obtain ⟨x3_7, hx3⟩ := hx3
  obtain ⟨te20_3, hx3⟩ := hx3
  obtain ⟨x3_8, hx3⟩ := hx3
  obtain ⟨sr25_3, hx3⟩ := hx3
  obtain ⟨ss25_3, hx3⟩ := hx3
  obtain ⟨x3_9, hx3⟩ := hx3
  obtain ⟨x3_10, hx3⟩ := hx3
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
  obtain ⟨w3_64, hx3⟩ := hx3
  obtain ⟨q3_380, hx3⟩ := hx3
  obtain ⟨q3_3af, hx3⟩ := hx3
  obtain ⟨q3_421, hx3⟩ := hx3
  obtain ⟨q3_451, hx3⟩ := hx3
  have K3_L := hx3
  rcases sv_seg_tt FW E3 V3 hret hO s3 M0 fR3 r3_2 r3_18 r3_19 r3_20 r3_21 r3_22 r3_23 r3_24 r3_25 rfl rfl ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_74)) ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_78)) (((((((((((((((((((ts_in).content x1_0).ofNatLen).restW x1_2).content x1_6).ofNatLen).restW (derOid_ok_elem x1_9)).content x1_11).ofNatLen).content x1_13).ofNatLen).restW x1_16).restW x1_17).content x1_21).ofNatLen).restW (derOid_ok_elem x1_23)).content (opt_ok_elem x1_25)).ofNatLen).contentIn x1_27) D0 with e | hx4
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3))) (by rw [r3_3, r2_3, r1_3]) (by rw [r3_4, r2_4, r1_4])
      (fun x hx => (fR3 x hx).trans (fM x hx).symm) e)
  obtain ⟨tl9_1_4, hx4⟩ := hx4
  obtain ⟨x4_0, hx4⟩ := hx4
  obtain ⟨x4_1, hx4⟩ := hx4
  obtain ⟨x4_2, hx4⟩ := hx4
  obtain ⟨te20_1_4, hx4⟩ := hx4
  obtain ⟨x4_3, hx4⟩ := hx4
  obtain ⟨op26_1_4, hx4⟩ := hx4
  obtain ⟨ol26_1_4, hx4⟩ := hx4
  obtain ⟨x4_4, hx4⟩ := hx4
  obtain ⟨to26_1_4, hx4⟩ := hx4
  obtain ⟨x4_5, hx4⟩ := hx4
  obtain ⟨tl30_1_4, hx4⟩ := hx4
  obtain ⟨x4_6, hx4⟩ := hx4
  obtain ⟨x4_7, hx4⟩ := hx4
  obtain ⟨te39_1_4, hx4⟩ := hx4
  obtain ⟨x4_8, hx4⟩ := hx4
  obtain ⟨vp45_1_4, hx4⟩ := hx4
  obtain ⟨vl45_1_4, hx4⟩ := hx4
  obtain ⟨x4_9, hx4⟩ := hx4
  obtain ⟨te45_1_4, hx4⟩ := hx4
  obtain ⟨x4_10, hx4⟩ := hx4
  obtain ⟨x4_11, hx4⟩ := hx4
  obtain ⟨x4_12, hx4⟩ := hx4
  obtain ⟨tl2_2_4, hx4⟩ := hx4
  obtain ⟨x4_13, hx4⟩ := hx4
  obtain ⟨ip2_2_4, hx4⟩ := hx4
  obtain ⟨il2_2_4, hx4⟩ := hx4
  obtain ⟨x4_14, hx4⟩ := hx4
  obtain ⟨x4_15, hx4⟩ := hx4
  obtain ⟨tl13_2_4, hx4⟩ := hx4
  obtain ⟨x4_16, hx4⟩ := hx4
  obtain ⟨tm18_2_4, hx4⟩ := hx4
  obtain ⟨x4_17, hx4⟩ := hx4
  obtain ⟨tt3_w264_3_4, hx4⟩ := hx4
  obtain ⟨tt3_w268_3_4, hx4⟩ := hx4
  obtain ⟨x4_18, hx4⟩ := hx4
  obtain ⟨x4_19, hx4⟩ := hx4
  obtain ⟨tt4_w264_4_4, hx4⟩ := hx4
  obtain ⟨tt4_w268_4_4, hx4⟩ := hx4
  obtain ⟨x4_20, hx4⟩ := hx4
  obtain ⟨x4_21, hx4⟩ := hx4
  obtain ⟨tt5_w264_5_4, hx4⟩ := hx4
  obtain ⟨tt5_w268_5_4, hx4⟩ := hx4
  obtain ⟨x4_22, hx4⟩ := hx4
  obtain ⟨x4_23, hx4⟩ := hx4
  obtain ⟨tt6_w264_6_4, hx4⟩ := hx4
  obtain ⟨tt6_w268_6_4, hx4⟩ := hx4
  obtain ⟨x4_24, hx4⟩ := hx4
  obtain ⟨x4_25, hx4⟩ := hx4
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
  obtain ⟨r4_26, hx4⟩ := hx4
  obtain ⟨r4_27, hx4⟩ := hx4
  obtain ⟨w4_264, hx4⟩ := hx4
  obtain ⟨w4_268, hx4⟩ := hx4
  obtain ⟨w4_74, hx4⟩ := hx4
  obtain ⟨w4_78, hx4⟩ := hx4
  obtain ⟨w4_3c, hx4⟩ := hx4
  obtain ⟨w4_7c, hx4⟩ := hx4
  have K4_L := hx4
  rcases sv_tsv FW E4 V4 hret hO s4 M0 fR4 r4_2 r4_18 r4_19 r4_20 r4_21 r4_22 r4_23 r4_24 r4_25 r4_26 r4_27 w4_3c ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_44))) ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_48))) ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_4c))) ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans w1_50))) ((K4_L.w32 (by decide) (by decide)).trans w3_64) w4_74 w4_78 w4_7c (fun j hj => (K4_L.range (by decide) (by decide) j hj).trans (q3_380 j hj)) (fun j hj => (K4_L.range (by decide) (by decide) j hj).trans (q3_3af j hj)) ((((((((((((((((((((ts_in).content x1_0).ofNatLen).restW x1_2).content x1_6).ofNatLen).restW (derOid_ok_elem x1_9)).content x1_11).ofNatLen).content x1_13).ofNatLen).restW x1_16).restW x1_17).content x1_21).ofNatLen).restW (derOid_ok_elem x1_23)).content (opt_ok_elem x1_25)).ofNatLen).contentIn x1_27).pos_ne) with ⟨-, e⟩ | hx5
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4)))) (by rw [r4_3, r3_3, r2_3, r1_3]) (by rw [r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR4 x hx).trans (fM x hx).symm) e)
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
  obtain ⟨w5_3c, hx5⟩ := hx5
  obtain ⟨w5_44, hx5⟩ := hx5
  obtain ⟨w5_48, hx5⟩ := hx5
  obtain ⟨w5_4c, hx5⟩ := hx5
  obtain ⟨w5_50, hx5⟩ := hx5
  obtain ⟨w5_64, hx5⟩ := hx5
  obtain ⟨w5_74, hx5⟩ := hx5
  obtain ⟨w5_78, hx5⟩ := hx5
  obtain ⟨w5_7c, hx5⟩ := hx5
  obtain ⟨w5_170, hx5⟩ := hx5
  obtain ⟨w5_174, hx5⟩ := hx5
  obtain ⟨w5_178, hx5⟩ := hx5
  obtain ⟨w5_17c, hx5⟩ := hx5
  obtain ⟨w5_180, hx5⟩ := hx5
  obtain ⟨w5_184, hx5⟩ := hx5
  obtain ⟨w5_188, hx5⟩ := hx5
  obtain ⟨w5_18c, hx5⟩ := hx5
  obtain ⟨w5_1f0, hx5⟩ := hx5
  obtain ⟨w5_1f4, hx5⟩ := hx5
  obtain ⟨b5_190, hx5⟩ := hx5
  obtain ⟨q5_191, hx5⟩ := hx5
  obtain ⟨q5_1c0, hx5⟩ := hx5
  obtain ⟨q5_1fc, hx5⟩ := hx5
  obtain ⟨q5_22b, hx5⟩ := hx5
  obtain ⟨q5_380, hx5⟩ := hx5
  obtain ⟨q5_3af, hx5⟩ := hx5
  have K5_L := hx5
  rcases sv_tsearch_st FW hret hO M0 (fun _ _ h => svCnt_zero Prod.fst (BitVec.ofNat 32 0x100) 0xFFFFFFE0 (by intro _; rfl) rfl (by decide) (congrArg Prod.fst h)) E5 V5 s5 fR5 r5_2 r5_8 r5_18 r5_19 r5_20 r5_21 r5_22 r5_23 r5_26 r5_27 w5_48 w5_4c w5_78 (fun i hi c'_6 q'_6 h => ⟨(svCnt_ne Prod.fst (BitVec.ofNat 32 0x100) 0xFFFFFFE0 (by intro _; rfl) rfl (by decide) hi (congrArg Prod.fst h)), (H' i hi c'_6 q'_6 h).1, (H' i hi c'_6 q'_6 h).2.1, (H' i hi c'_6 q'_6 h).2.2.1, (H' i hi c'_6 q'_6 h).2.2.2.1, (H' i hi c'_6 q'_6 h).2.2.2.2, (((((((x1_31).content x1_32).ofNatLen).content x1_34).ofNatLen).restW x1_37).rawW x1_38)⟩) with e | hx6
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5))))) (by rw [r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR5 x hx).trans (fM x hx).symm) e)
  obtain ⟨k_6, hx6⟩ := hx6
  obtain ⟨x6_0, hx6⟩ := hx6
  obtain ⟨x6_1, hx6⟩ := hx6
  obtain ⟨c'_6, hx6⟩ := hx6
  obtain ⟨q'_6, hx6⟩ := hx6
  obtain ⟨x6_2, hx6⟩ := hx6
  obtain ⟨x6_3, hx6⟩ := hx6
  obtain ⟨x6_4, hx6⟩ := hx6
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
  obtain ⟨r6_25, hx6⟩ := hx6
  obtain ⟨r6_26, hx6⟩ := hx6
  obtain ⟨r6_27, hx6⟩ := hx6
  obtain ⟨w6_48, hx6⟩ := hx6
  obtain ⟨w6_4c, hx6⟩ := hx6
  obtain ⟨w6_78, hx6⟩ := hx6
  have K6_L := hx6
  rcases sv_tsig FW E6 V6 hret hO s6 M0 fR6 r6_2 r6_18 r6_19 r6_20 r6_21 r6_22 r6_23 r6_24 r6_25 r6_26 r6_27 ((K6_L.w32 (by decide) (by decide)).trans w5_44) ((K6_L.w32 (by decide) (by decide)).trans w5_50) ((K6_L.w32 (by decide) (by decide)).trans w5_64) ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_68)))))) ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_70)))))) ((K6_L.w32 (by decide) (by decide)).trans w5_74) w6_78 ((K6_L.w32 (by decide) (by decide)).trans w5_174) S2 RS (((((((((((((((((((ts_in).content x1_0).ofNatLen).restW x1_2).content x1_6).ofNatLen).restW (derOid_ok_elem x1_9)).content x1_11).ofNatLen).content x1_13).ofNatLen).restW x1_16).restW x1_17).content x1_21).ofNatLen).restW (derOid_ok_elem x1_23)).content (opt_ok_elem x1_25)).ofNatLen).contentIn x1_27) (x3_2.resolve_left x3_3.1) sig_in (by have h := ((((((((((((((((((((((((((ts_in).content x1_0).ofNatLen).restW x1_2).content x1_6).ofNatLen).restW (derOid_ok_elem x1_9)).content x1_11).ofNatLen).content x1_13).ofNatLen).restW x1_16).restW x1_17).content x1_21).ofNatLen).restW (derOid_ok_elem x1_23)).content (opt_ok_elem x1_25)).ofNatLen).contentIn x1_27).content x4_0).ofNatLen).restW x4_3).restW (derOid_ok_elem x4_5)).content x4_6).ofNatLen).restW x4_8).contentIn x4_9; rw [x4_11] at h; exact h) (((((((((x1_31).content x1_32).ofNatLen).content x1_34).ofNatLen).restW x1_37).restW x1_38).restW x1_40).rawW (opt_ok_elem x1_41)) with ⟨-, e⟩ | hx7
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6)))))) (by rw [r6_3, r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r6_4, r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR6 x hx).trans (fM x hx).symm) e)
  obtain ⟨x7_0, hx7⟩ := hx7
  obtain ⟨x7_1, hx7⟩ := hx7
  obtain ⟨x7_2, hx7⟩ := hx7
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
  obtain ⟨w7_68, hx7⟩ := hx7
  obtain ⟨w7_70, hx7⟩ := hx7
  obtain ⟨w7_74, hx7⟩ := hx7
  obtain ⟨w7_78, hx7⟩ := hx7
  obtain ⟨w7_174, hx7⟩ := hx7
  obtain ⟨w7_380, hx7⟩ := hx7
  obtain ⟨w7_384, hx7⟩ := hx7
  obtain ⟨w7_388, hx7⟩ := hx7
  obtain ⟨w7_38c, hx7⟩ := hx7
  obtain ⟨mb7_420, hx7⟩ := hx7
  have K7_L := hx7
  rcases sv_tp FW E7 V7 hret hO s7 M0 fR7 r7_2 r7_18 r7_19 r7_20 r7_21 r7_22 r7_23 r7_24 r7_25 r7_26 r7_27 w7_78 mb7_420 ((K7_L.b8 (by decide) (by decide)).trans ((K6_L.b8 (by decide) (by decide)).trans b5_190)) (fun j hj => (K7_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K6_L.range (by decide) (by decide) j hj).trans (q5_191 j hj)) j hj)) (fun j hj => (K7_L.range (by decide) (by decide) j hj).trans ((fun j hj => (K6_L.range (by decide) (by decide) j hj).trans (q5_1c0 j hj)) j hj)) PE0 rfl (pkp_in k_6 x6_0 c'_6 q'_6 x6_2 x6_4) (apk k_6 x6_0 c'_6 q'_6 x6_2 x6_4) (pk_in k_6 x6_0 c'_6 q'_6 x6_2 x6_4) (side k_6 x6_0 c'_6 q'_6 x6_2 x6_4) with ⟨-, e⟩ | hx8
  · exact .inr (.inl (Panics.of_steps (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7))))))) e))
  obtain ⟨pv_8, hx8⟩ := hx8
  obtain ⟨x8_0, hx8⟩ := hx8
  obtain ⟨n8, hx8⟩ := hx8
  obtain ⟨c8, hx8⟩ := hx8
  obtain ⟨s8, hx8⟩ := hx8
  obtain ⟨E8, hx8⟩ := hx8
  obtain ⟨V8, hx8⟩ := hx8
  obtain ⟨fR8, hx8⟩ := hx8
  obtain ⟨r8_2, hx8⟩ := hx8
  obtain ⟨r8_3, hx8⟩ := hx8
  obtain ⟨r8_4, hx8⟩ := hx8
  obtain ⟨r8_a0, hx8⟩ := hx8
  obtain ⟨r8_18, hx8⟩ := hx8
  obtain ⟨r8_19, hx8⟩ := hx8
  obtain ⟨r8_20, hx8⟩ := hx8
  obtain ⟨r8_21, hx8⟩ := hx8
  obtain ⟨r8_22, hx8⟩ := hx8
  obtain ⟨r8_23, hx8⟩ := hx8
  obtain ⟨r8_24, hx8⟩ := hx8
  obtain ⟨r8_25, hx8⟩ := hx8
  obtain ⟨r8_26, hx8⟩ := hx8
  obtain ⟨r8_27, hx8⟩ := hx8
  have K8_L := hx8
  exact .inr (.inr ⟨tl10_1_1, x1_0, x1_1, tl21_1_1, x1_2, x1_3, te30_1_1, x1_4, x1_5, tl2_2_1, x1_6, x1_7, op13_2_1, ol13_2_1, x1_8, to13_2_1, x1_9, x1_10, tl21_2_1, x1_11, x1_12, tl32_2_1, x1_13, x1_14, x1_15, te43_2_1, x1_16, tl2_3_1, x1_17, x1_18, te11_3_1, x1_19, x1_20, tl19_3_1, x1_21, op28_3_1, ol28_3_1, x1_22, to28_3_1, x1_23, x1_24, tl2_4_1, x1_25, x1_26, vp23_4_1, vl23_4_1, x1_27, te23_4_1, x1_28, x1_29, tr5_w328_5_1, tr5_w32c_5_1, x1_30, x1_31, tl2_6_1, x1_32, x1_33, tl13_6_1, x1_34, x1_35, x1_36, te25_6_1, x1_37, tl31_6_1, x1_38, x1_39, te39_6_1, x1_40, tl45_6_1, x1_41, x1_42, x2_0, tl6_1_2, x2_1, op15_1_2, ol15_1_2, x2_2, to15_1_2, x2_3, tl20_1_2, x2_4, x2_5, x2_6, trv_w64_2_2, trv_w7c_2_2, x2_7, x2_8, k_3, dg'_3, flag'_3, cp'_3, rem'_3, x3_0, x3_1, x3_2, x3_3, op9_3, ol9_3, x3_4, te9_3, x3_5, x3_6, vp20_3, vl20_3, x3_7, te20_3, x3_8, sr25_3, ss25_3, x3_9, x3_10, tl9_1_4, x4_0, x4_1, x4_2, te20_1_4, x4_3, op26_1_4, ol26_1_4, x4_4, to26_1_4, x4_5, tl30_1_4, x4_6, x4_7, te39_1_4, x4_8, vp45_1_4, vl45_1_4, x4_9, te45_1_4, x4_10, x4_11, x4_12, tl2_2_4, x4_13, ip2_2_4, il2_2_4, x4_14, x4_15, tl13_2_4, x4_16, tm18_2_4, x4_17, tt3_w264_3_4, tt3_w268_3_4, x4_18, x4_19, tt4_w264_4_4, tt4_w268_4_4, x4_20, x4_21, tt5_w264_5_4, tt5_w268_5_4, x4_22, x4_23, tt6_w264_6_4, tt6_w268_6_4, x4_24, x4_25, k_6, x6_0, x6_1, c'_6, q'_6, x6_2, x6_3, x6_4, x7_0, x7_1, x7_2, pv_8, x8_0, n8, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8))))))), fR8, s8, E8, V8,
    by rw [r8_3, r7_3, r6_3, r5_3, r4_3, r3_3, r2_3, r1_3], by rw [r8_4, r7_4, r6_4, r5_4, r4_4, r3_4, r2_4, r1_4], r8_2, r8_a0, r8_18, r8_19, r8_20, r8_21, r8_22, r8_23, r8_24, r8_25, r8_26, r8_27, ((K8_L.w32 (by decide) (by decide)).trans w7_44), ((K8_L.w32 (by decide) (by decide)).trans w7_50), ((K8_L.w32 (by decide) (by decide)).trans w7_64), ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans w5_7c))), ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_264)))), ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans w4_268)))), ((K8_L.w32 (by decide) (by decide)).trans w7_74), ((K8_L.w32 (by decide) (by decide)).trans w7_78), ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans w6_48)), ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans w6_4c)), ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans w5_3c))), ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans w5_170))), ((K8_L.w32 (by decide) (by decide)).trans w7_174), ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans w5_178))), ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans w5_17c))), ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans w5_180))), ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans w5_184))), ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans w5_188))), ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans w5_18c))), ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans w5_1f0))), ((K8_L.w32 (by decide) (by decide)).trans ((K7_L.w32 (by decide) (by decide)).trans ((K6_L.w32 (by decide) (by decide)).trans w5_1f4))), ((K8_L.b8 (by decide) (by decide)).trans ((K7_L.b8 (by decide) (by decide)).trans ((K6_L.b8 (by decide) (by decide)).trans b5_190))), ((K8_L.w32 (by decide) (by decide)).trans w7_68), ((K8_L.w32 (by decide) (by decide)).trans w7_70), ((K8_L.w32 (by decide) (by decide)).trans w7_380), ((K8_L.w32 (by decide) (by decide)).trans w7_384), ((K8_L.w32 (by decide) (by decide)).trans w7_388), ((K8_L.w32 (by decide) (by decide)).trans w7_38c), ((((((((K1_L).trans K2_L).trans K3_L).trans K4_L).trans K5_L).trans K6_L).trans K7_L).trans K8_L).mono (by decide)⟩)

end C3.RV32.Sv
