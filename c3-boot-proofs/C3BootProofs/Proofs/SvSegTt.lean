import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvTt1
import C3BootProofs.Proofs.SvTt2
import C3BootProofs.Proofs.SvTt3
import C3BootProofs.Proofs.SvTt4
import C3BootProofs.Proofs.SvTt5
import C3BootProofs.Proofs.SvTt6

/-!
# `sigstore::verify`: The `TSTInfo`

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **The `TSTInfo`**: from 0x10A4 to the timestamp's signature at 0x12BE, `sv_tt1` to `sv_tt6`. -/
theorem sv_seg_tt {B out bp x20 x21 x22 x23 x24 x25 x26 x27 tp tl : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x10A4 (reg n0))
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
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl)
    (tst_in : SvIn B (tp) (tl).toNat)
    (D0 : SvData M0) :
    SvErrRet B out v n0 ∨
    (∃ tl9_1, derElement 0x30 (memBytes M0 (tp) (tl).toNat) = .ok tl9_1 ∧
      ((tl) - BitVec.ofNat 32 (tl9_1.header + tl9_1.len) = 0) ∧
      derIntIsOf M0 (memBytes M0 ((tp) + BitVec.ofNat 32 tl9_1.header) (BitVec.ofNat 32 tl9_1.len).toNat) ((tp) + BitVec.ofNat 32 tl9_1.header) (derElement 2 (memBytes M0 ((tp) + BitVec.ofNat 32 tl9_1.header) (BitVec.ofNat 32 tl9_1.len).toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = .ok true ∧
      ∃ te20_1, derElement 2 (memBytes M0 ((tp) + BitVec.ofNat 32 tl9_1.header) (BitVec.ofNat 32 tl9_1.len).toNat) = .ok te20_1 ∧
      ∃ op26_1 ol26_1, derContent (((tp) + BitVec.ofNat 32 tl9_1.header) + BitVec.ofNat 32 (te20_1.header + te20_1.len)) (derOid (memBytes M0 (((tp) + BitVec.ofNat 32 tl9_1.header) + BitVec.ofNat 32 (te20_1.header + te20_1.len)) ((BitVec.ofNat 32 tl9_1.len) - BitVec.ofNat 32 (te20_1.header + te20_1.len)).toNat)) = .ok (op26_1, ol26_1) ∧
      ∃ to26_1, derOid (memBytes M0 (((tp) + BitVec.ofNat 32 tl9_1.header) + BitVec.ofNat 32 (te20_1.header + te20_1.len)) ((BitVec.ofNat 32 tl9_1.len) - BitVec.ofNat 32 (te20_1.header + te20_1.len)).toNat) = .ok to26_1 ∧
      ∃ tl30_1, derElement 0x30 (memBytes M0 ((((tp) + BitVec.ofNat 32 tl9_1.header) + BitVec.ofNat 32 (te20_1.header + te20_1.len)) + BitVec.ofNat 32 (to26_1.header + to26_1.len)) (((BitVec.ofNat 32 tl9_1.len) - BitVec.ofNat 32 (te20_1.header + te20_1.len)) - BitVec.ofNat 32 (to26_1.header + to26_1.len)).toNat) = .ok tl30_1 ∧
      isSha256Of M0 (((((tp) + BitVec.ofNat 32 tl9_1.header) + BitVec.ofNat 32 (te20_1.header + te20_1.len)) + BitVec.ofNat 32 (to26_1.header + to26_1.len)) + BitVec.ofNat 32 tl30_1.header) (BitVec.ofNat 32 tl30_1.len).toNat = .ok true ∧
      ∃ te39_1, derElement 0x30 (memBytes M0 (((((tp) + BitVec.ofNat 32 tl9_1.header) + BitVec.ofNat 32 (te20_1.header + te20_1.len)) + BitVec.ofNat 32 (to26_1.header + to26_1.len)) + BitVec.ofNat 32 tl30_1.header) (BitVec.ofNat 32 tl30_1.len).toNat) = .ok te39_1 ∧
      ∃ vp45_1 vl45_1, derContent ((((((tp) + BitVec.ofNat 32 tl9_1.header) + BitVec.ofNat 32 (te20_1.header + te20_1.len)) + BitVec.ofNat 32 (to26_1.header + to26_1.len)) + BitVec.ofNat 32 tl30_1.header) + BitVec.ofNat 32 (te39_1.header + te39_1.len)) (derElement 4 (memBytes M0 ((((((tp) + BitVec.ofNat 32 tl9_1.header) + BitVec.ofNat 32 (te20_1.header + te20_1.len)) + BitVec.ofNat 32 (to26_1.header + to26_1.len)) + BitVec.ofNat 32 tl30_1.header) + BitVec.ofNat 32 (te39_1.header + te39_1.len)) ((BitVec.ofNat 32 tl30_1.len) - BitVec.ofNat 32 (te39_1.header + te39_1.len)).toNat)) = .ok (vp45_1, vl45_1) ∧
      ∃ te45_1, derElement 4 (memBytes M0 ((((((tp) + BitVec.ofNat 32 tl9_1.header) + BitVec.ofNat 32 (te20_1.header + te20_1.len)) + BitVec.ofNat 32 (to26_1.header + to26_1.len)) + BitVec.ofNat 32 tl30_1.header) + BitVec.ofNat 32 (te39_1.header + te39_1.len)) ((BitVec.ofNat 32 tl30_1.len) - BitVec.ofNat 32 (te39_1.header + te39_1.len)).toNat) = .ok te45_1 ∧
      (vl45_1 = 32) ∧
      (((BitVec.ofNat 32 tl30_1.len) - BitVec.ofNat 32 (te39_1.header + te39_1.len)) - BitVec.ofNat 32 (te45_1.header + te45_1.len) = 0) ∧
      ∃ tl2_2, derElement 2 (memBytes M0 ((((((tp) + BitVec.ofNat 32 tl9_1.header) + BitVec.ofNat 32 (te20_1.header + te20_1.len)) + BitVec.ofNat 32 (to26_1.header + to26_1.len)) + BitVec.ofNat 32 (tl30_1.header + tl30_1.len))) (((((BitVec.ofNat 32 tl9_1.len) - BitVec.ofNat 32 (te20_1.header + te20_1.len)) - BitVec.ofNat 32 (to26_1.header + to26_1.len)) - BitVec.ofNat 32 (tl30_1.header + tl30_1.len))).toNat) = .ok tl2_2 ∧
      ∃ ip2_2 il2_2, derPosIntOf (memBytes M0 ((((((tp) + BitVec.ofNat 32 tl9_1.header) + BitVec.ofNat 32 (te20_1.header + te20_1.len)) + BitVec.ofNat 32 (to26_1.header + to26_1.len)) + BitVec.ofNat 32 (tl30_1.header + tl30_1.len))) (((((BitVec.ofNat 32 tl9_1.len) - BitVec.ofNat 32 (te20_1.header + te20_1.len)) - BitVec.ofNat 32 (to26_1.header + to26_1.len)) - BitVec.ofNat 32 (tl30_1.header + tl30_1.len))).toNat) ((((((tp) + BitVec.ofNat 32 tl9_1.header) + BitVec.ofNat 32 (te20_1.header + te20_1.len)) + BitVec.ofNat 32 (to26_1.header + to26_1.len)) + BitVec.ofNat 32 (tl30_1.header + tl30_1.len))) (.ok tl2_2) = .ok (ip2_2, il2_2) ∧
      (((il2_2) - (aluEval .sltu ((M0 (ip2_2)).zeroExtend 32) 1)).toNat ≤ 20) ∧
      ∃ tl13_2, derElement 0x18 (memBytes M0 (((((((tp) + BitVec.ofNat 32 tl9_1.header) + BitVec.ofNat 32 (te20_1.header + te20_1.len)) + BitVec.ofNat 32 (to26_1.header + to26_1.len)) + BitVec.ofNat 32 (tl30_1.header + tl30_1.len))) + BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) ((((((BitVec.ofNat 32 tl9_1.len) - BitVec.ofNat 32 (te20_1.header + te20_1.len)) - BitVec.ofNat 32 (to26_1.header + to26_1.len)) - BitVec.ofNat 32 (tl30_1.header + tl30_1.len))) - BitVec.ofNat 32 (tl2_2.header + tl2_2.len)).toNat) = .ok tl13_2 ∧
      ∃ tm18_2, generalizedTime (memBytes M0 ((((((((tp) + BitVec.ofNat 32 tl9_1.header) + BitVec.ofNat 32 (te20_1.header + te20_1.len)) + BitVec.ofNat 32 (to26_1.header + to26_1.len)) + BitVec.ofNat 32 (tl30_1.header + tl30_1.len))) + BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) + BitVec.ofNat 32 tl13_2.header) ((BitVec.ofNat 32 tl13_2.len).toNat)) = some tm18_2 ∧
      ∃ tt3_w264_3 : Word, ∃ tt3_w268_3 : Word, (((derOptRes 0x30 (memBytes M0 (((((((((tp) + BitVec.ofNat 32 tl9_1.header) + BitVec.ofNat 32 (te20_1.header + te20_1.len)) + BitVec.ofNat 32 (to26_1.header + to26_1.len)) + BitVec.ofNat 32 (tl30_1.header + tl30_1.len))) + BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) + BitVec.ofNat 32 (tl13_2.header + tl13_2.len))) ((((((((BitVec.ofNat 32 tl9_1.len) - BitVec.ofNat 32 (te20_1.header + te20_1.len)) - BitVec.ofNat 32 (to26_1.header + to26_1.len)) - BitVec.ofNat 32 (tl30_1.header + tl30_1.len))) - BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) - BitVec.ofNat 32 (tl13_2.header + tl13_2.len))).toNat) = none) ∧ tt3_w264_3 = ((((((((tp) + BitVec.ofNat 32 tl9_1.header) + BitVec.ofNat 32 (te20_1.header + te20_1.len)) + BitVec.ofNat 32 (to26_1.header + to26_1.len)) + BitVec.ofNat 32 (tl30_1.header + tl30_1.len))) + BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) + BitVec.ofNat 32 (tl13_2.header + tl13_2.len)) ∧ tt3_w268_3 = (((((((BitVec.ofNat 32 tl9_1.len) - BitVec.ofNat 32 (te20_1.header + te20_1.len)) - BitVec.ofNat 32 (to26_1.header + to26_1.len)) - BitVec.ofNat 32 (tl30_1.header + tl30_1.len))) - BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) - BitVec.ofNat 32 (tl13_2.header + tl13_2.len))) ∨ ((¬ (derOptRes 0x30 (memBytes M0 (((((((((tp) + BitVec.ofNat 32 tl9_1.header) + BitVec.ofNat 32 (te20_1.header + te20_1.len)) + BitVec.ofNat 32 (to26_1.header + to26_1.len)) + BitVec.ofNat 32 (tl30_1.header + tl30_1.len))) + BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) + BitVec.ofNat 32 (tl13_2.header + tl13_2.len))) ((((((((BitVec.ofNat 32 tl9_1.len) - BitVec.ofNat 32 (te20_1.header + te20_1.len)) - BitVec.ofNat 32 (to26_1.header + to26_1.len)) - BitVec.ofNat 32 (tl30_1.header + tl30_1.len))) - BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) - BitVec.ofNat 32 (tl13_2.header + tl13_2.len))).toNat) = none)) ∧ ∃ tl2, derOptRes 0x30 (memBytes M0 (((((((((tp) + BitVec.ofNat 32 tl9_1.header) + BitVec.ofNat 32 (te20_1.header + te20_1.len)) + BitVec.ofNat 32 (to26_1.header + to26_1.len)) + BitVec.ofNat 32 (tl30_1.header + tl30_1.len))) + BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) + BitVec.ofNat 32 (tl13_2.header + tl13_2.len))) ((((((((BitVec.ofNat 32 tl9_1.len) - BitVec.ofNat 32 (te20_1.header + te20_1.len)) - BitVec.ofNat 32 (to26_1.header + to26_1.len)) - BitVec.ofNat 32 (tl30_1.header + tl30_1.len))) - BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) - BitVec.ofNat 32 (tl13_2.header + tl13_2.len))).toNat) = some (.ok tl2) ∧ tt3_w264_3 = (((((((((tp) + BitVec.ofNat 32 tl9_1.header) + BitVec.ofNat 32 (te20_1.header + te20_1.len)) + BitVec.ofNat 32 (to26_1.header + to26_1.len)) + BitVec.ofNat 32 (tl30_1.header + tl30_1.len))) + BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) + BitVec.ofNat 32 (tl13_2.header + tl13_2.len))) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tt3_w268_3 = ((((((((BitVec.ofNat 32 tl9_1.len) - BitVec.ofNat 32 (te20_1.header + te20_1.len)) - BitVec.ofNat 32 (to26_1.header + to26_1.len)) - BitVec.ofNat 32 (tl30_1.header + tl30_1.len))) - BitVec.ofNat 32 (tl2_2.header + tl2_2.len)) - BitVec.ofNat 32 (tl13_2.header + tl13_2.len))) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tt3_w264_3 tt3_w268_3.toNat ∧
      ∃ tt4_w264_4 : Word, ∃ tt4_w268_4 : Word, (((tt3_w268_3 = 0) ∧ tt4_w264_4 = tt3_w264_3 ∧ tt4_w268_4 = tt3_w268_3) ∨ ((¬ (tt3_w268_3 = 0)) ∧ (M0 tt3_w264_3 = BitVec.ofNat 8 1) ∧ derBoolOf (memBytes M0 (tt3_w264_3) (tt3_w268_3).toNat) (derElement 1 (memBytes M0 (tt3_w264_3) (tt3_w268_3).toNat)) = .ok () ∧ ∃ tb8_1, derElement 1 (memBytes M0 (tt3_w264_3) (tt3_w268_3).toNat) = .ok tb8_1 ∧ ∃ tt4b_w264_2 : Word, ∃ tt4b_w268_2 : Word, (((((tt3_w268_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = 0) ∧ tt4b_w264_2 = ((tt3_w264_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) ∧ tt4b_w268_2 = ((tt3_w268_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) ∨ ((¬ (((tt3_w268_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = 0)) ∧ ∃ tt4n_w264_2 : Word, ∃ tt4n_w268_2 : Word, (((M0 ((tt3_w264_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = BitVec.ofNat 8 2) ∧ ∃ ip4 il4, derIntOf (memBytes M0 (((tt3_w264_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (((tt3_w268_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))).toNat) (((tt3_w264_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (derElement 2 (memBytes M0 (((tt3_w264_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (((tt3_w268_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))).toNat)) = .ok (ip4, il4) ∧ ∃ ti4, derElement 2 (memBytes M0 (((tt3_w264_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (((tt3_w268_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))).toNat) = .ok ti4 ∧ tt4n_w264_2 = (((tt3_w264_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) + BitVec.ofNat 32 (ti4.header + ti4.len) ∧ tt4n_w268_2 = (((tt3_w268_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) - BitVec.ofNat 32 (ti4.header + ti4.len)) ∨ ((¬ (M0 ((tt3_w264_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = BitVec.ofNat 8 2)) ∧ tt4n_w264_2 = ((tt3_w264_3) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) ∧ tt4n_w268_2 = ((tt3_w268_3) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len)))) ∧ SvIn B tt4n_w264_2 tt4n_w268_2.toNat ∧ tt4b_w264_2 = tt4n_w264_2 ∧ tt4b_w268_2 = tt4n_w268_2)) ∧ SvIn B tt4b_w264_2 tt4b_w268_2.toNat ∧ tt4_w264_4 = tt4b_w264_2 ∧ tt4_w268_4 = tt4b_w268_2) ∨ ((¬ (tt3_w268_3 = 0)) ∧ (¬ (M0 tt3_w264_3 = BitVec.ofNat 8 1)) ∧ ∃ tt4n_w264_2 : Word, ∃ tt4n_w268_2 : Word, (((M0 tt3_w264_3 = BitVec.ofNat 8 2) ∧ ∃ ip4 il4, derIntOf (memBytes M0 (tt3_w264_3) (tt3_w268_3).toNat) (tt3_w264_3) (derElement 2 (memBytes M0 (tt3_w264_3) (tt3_w268_3).toNat)) = .ok (ip4, il4) ∧ ∃ ti4, derElement 2 (memBytes M0 (tt3_w264_3) (tt3_w268_3).toNat) = .ok ti4 ∧ tt4n_w264_2 = (tt3_w264_3) + BitVec.ofNat 32 (ti4.header + ti4.len) ∧ tt4n_w268_2 = (tt3_w268_3) - BitVec.ofNat 32 (ti4.header + ti4.len)) ∨ ((¬ (M0 tt3_w264_3 = BitVec.ofNat 8 2)) ∧ tt4n_w264_2 = tt3_w264_3 ∧ tt4n_w268_2 = tt3_w268_3)) ∧ SvIn B tt4n_w264_2 tt4n_w268_2.toNat ∧ tt4_w264_4 = tt4n_w264_2 ∧ tt4_w268_4 = tt4n_w268_2)) ∧ SvIn B tt4_w264_4 tt4_w268_4.toNat ∧
      ∃ tt5_w264_5 : Word, ∃ tt5_w268_5 : Word, (((derOptRes 0xA0 (memBytes M0 (tt4_w264_4) (tt4_w268_4).toNat) = none) ∧ tt5_w264_5 = tt4_w264_4 ∧ tt5_w268_5 = tt4_w268_4) ∨ ((¬ (derOptRes 0xA0 (memBytes M0 (tt4_w264_4) (tt4_w268_4).toNat) = none)) ∧ ∃ tl2, derOptRes 0xA0 (memBytes M0 (tt4_w264_4) (tt4_w268_4).toNat) = some (.ok tl2) ∧ tt5_w264_5 = (tt4_w264_4) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tt5_w268_5 = (tt4_w268_4) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tt5_w264_5 tt5_w268_5.toNat ∧
      ∃ tt6_w264_6 : Word, ∃ tt6_w268_6 : Word, (((derOptRes 0xA1 (memBytes M0 (tt5_w264_5) (tt5_w268_5).toNat) = none) ∧ (tt5_w268_5 = 0) ∧ tt6_w264_6 = tt5_w264_5 ∧ tt6_w268_6 = tt5_w268_5) ∨ ((¬ (derOptRes 0xA1 (memBytes M0 (tt5_w264_5) (tt5_w268_5).toNat) = none)) ∧ ∃ tl2, derOptRes 0xA1 (memBytes M0 (tt5_w264_5) (tt5_w268_5).toNat) = some (.ok tl2) ∧ ((tt5_w268_5) - BitVec.ofNat 32 (tl2.header + tl2.len) = 0) ∧ tt6_w264_6 = (tt5_w264_5) + BitVec.ofNat 32 (tl2.header + tl2.len) ∧ tt6_w268_6 = (tt5_w268_5) - BitVec.ofNat 32 (tl2.header + tl2.len))) ∧ SvIn B tt6_w264_6 tt6_w268_6.toNat ∧
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0x12BE (reg n') ∧
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
        reg n' (24 : Fin 32) = x24 ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = vp45_1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = tt6_w264_6 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = tt6_w268_6 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = tp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = tl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = BitVec.ofNat 32 (tm18_2 % 2 ^ 32) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = BitVec.ofNat 32 (tm18_2 / 2 ^ 32) ∧
        SvKeepL B n0.mem n'.mem [(0x27C, 0x4), (0x280, 0x4), (0x284, 0x4), (0x288, 0x4), (0x420, 0x10), (0x284, 0x8), (0x261, 0xB), (0x25C, 0x4), (0x260, 0x1), (0x264, 0x8), (0x420, 0x8), (0x264, 0x8), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x3E8, 0x8), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x11), (0x400, 0x10), (0x3C, 0x4), (0x7C, 0x4), (0x420, 0x18)]) := by
  rcases sv_tt1 FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_74 w0_78 tst_in D0 with ⟨-, e⟩ | hx1
  · exact .inl e
  obtain ⟨tl9_1, hx1⟩ := hx1
  obtain ⟨x1_0, hx1⟩ := hx1
  obtain ⟨x1_1, hx1⟩ := hx1
  obtain ⟨x1_2, hx1⟩ := hx1
  obtain ⟨te20_1, hx1⟩ := hx1
  obtain ⟨x1_3, hx1⟩ := hx1
  obtain ⟨op26_1, hx1⟩ := hx1
  obtain ⟨ol26_1, hx1⟩ := hx1
  obtain ⟨x1_4, hx1⟩ := hx1
  obtain ⟨to26_1, hx1⟩ := hx1
  obtain ⟨x1_5, hx1⟩ := hx1
  obtain ⟨tl30_1, hx1⟩ := hx1
  obtain ⟨x1_6, hx1⟩ := hx1
  obtain ⟨x1_7, hx1⟩ := hx1
  obtain ⟨te39_1, hx1⟩ := hx1
  obtain ⟨x1_8, hx1⟩ := hx1
  obtain ⟨vp45_1, hx1⟩ := hx1
  obtain ⟨vl45_1, hx1⟩ := hx1
  obtain ⟨x1_9, hx1⟩ := hx1
  obtain ⟨te45_1, hx1⟩ := hx1
  obtain ⟨x1_10, hx1⟩ := hx1
  obtain ⟨x1_11, hx1⟩ := hx1
  obtain ⟨x1_12, hx1⟩ := hx1
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
  obtain ⟨w1_264, hx1⟩ := hx1
  obtain ⟨w1_268, hx1⟩ := hx1
  have K1_L := hx1
  rcases sv_tt2 FW E1 V1 hret hO s1 M0 fR1 r1_2 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 r1_24 r1_25 r1_26 r1_27 w1_264 w1_268 ((((((tst_in).content x1_0).ofNatLen).restW x1_3).restW (derOid_ok_elem x1_5)).restW x1_6) D0 with ⟨-, e⟩ | hx2
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  obtain ⟨tl2_2, hx2⟩ := hx2
  obtain ⟨x2_0, hx2⟩ := hx2
  obtain ⟨ip2_2, hx2⟩ := hx2
  obtain ⟨il2_2, hx2⟩ := hx2
  obtain ⟨x2_1, hx2⟩ := hx2
  obtain ⟨x2_2, hx2⟩ := hx2
  obtain ⟨tl13_2, hx2⟩ := hx2
  obtain ⟨x2_3, hx2⟩ := hx2
  obtain ⟨tm18_2, hx2⟩ := hx2
  obtain ⟨x2_4, hx2⟩ := hx2
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
  obtain ⟨w2_3c, hx2⟩ := hx2
  obtain ⟨w2_7c, hx2⟩ := hx2
  obtain ⟨w2_264, hx2⟩ := hx2
  obtain ⟨w2_268, hx2⟩ := hx2
  have K2_L := hx2
  rcases sv_tt3 FW E2 V2 hret hO s2 M0 fR2 r2_2 r2_18 r2_19 r2_20 r2_21 r2_22 r2_23 r2_24 r2_25 r2_26 r2_27 w2_264 w2_268 ((((((((tst_in).content x1_0).ofNatLen).restW x1_3).restW (derOid_ok_elem x1_5)).restW x1_6).restW x2_0).restW x2_3) D0 with e | hx3
  · exact .inl (SvErrRet.pre (c1.trans (c2)) (by rw [r2_3, r1_3]) (by rw [r2_4, r1_4])
      (fun x hx => (fR2 x hx).trans (fM x hx).symm) e)
  obtain ⟨tt3_w264_3, hx3⟩ := hx3
  obtain ⟨tt3_w268_3, hx3⟩ := hx3
  obtain ⟨x3_0, hx3⟩ := hx3
  obtain ⟨x3_1, hx3⟩ := hx3
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
  obtain ⟨w3_264, hx3⟩ := hx3
  obtain ⟨w3_268, hx3⟩ := hx3
  have K3_L := hx3
  rcases sv_tt4 FW E3 V3 hret hO s3 M0 fR3 r3_2 r3_18 r3_19 r3_20 r3_21 r3_22 r3_23 r3_24 r3_25 r3_26 r3_27 w3_264 w3_268 x3_1 D0 with e | hx4
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3))) (by rw [r3_3, r2_3, r1_3]) (by rw [r3_4, r2_4, r1_4])
      (fun x hx => (fR3 x hx).trans (fM x hx).symm) e)
  obtain ⟨tt4_w264_4, hx4⟩ := hx4
  obtain ⟨tt4_w268_4, hx4⟩ := hx4
  obtain ⟨x4_0, hx4⟩ := hx4
  obtain ⟨x4_1, hx4⟩ := hx4
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
  obtain ⟨w4_264, hx4⟩ := hx4
  obtain ⟨w4_268, hx4⟩ := hx4
  have K4_L := hx4
  rcases sv_tt5 FW E4 V4 hret hO s4 M0 fR4 r4_2 r4_18 r4_19 r4_20 r4_21 r4_22 r4_23 r4_24 r4_25 r4_26 r4_27 w4_264 w4_268 x4_1 D0 with e | hx5
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4)))) (by rw [r4_3, r3_3, r2_3, r1_3]) (by rw [r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR4 x hx).trans (fM x hx).symm) e)
  obtain ⟨tt5_w264_5, hx5⟩ := hx5
  obtain ⟨tt5_w268_5, hx5⟩ := hx5
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
  obtain ⟨w5_264, hx5⟩ := hx5
  obtain ⟨w5_268, hx5⟩ := hx5
  have K5_L := hx5
  rcases sv_tt6 FW E5 V5 hret hO s5 M0 fR5 r5_2 r5_18 r5_19 r5_20 r5_21 r5_22 r5_23 r5_24 r5_25 r5_26 r5_27 w5_264 w5_268 x5_1 D0 with e | hx6
  · exact .inl (SvErrRet.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5))))) (by rw [r5_3, r4_3, r3_3, r2_3, r1_3]) (by rw [r5_4, r4_4, r3_4, r2_4, r1_4])
      (fun x hx => (fR5 x hx).trans (fM x hx).symm) e)
  obtain ⟨tt6_w264_6, hx6⟩ := hx6
  obtain ⟨tt6_w268_6, hx6⟩ := hx6
  obtain ⟨x6_0, hx6⟩ := hx6
  obtain ⟨x6_1, hx6⟩ := hx6
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
  obtain ⟨w6_264, hx6⟩ := hx6
  obtain ⟨w6_268, hx6⟩ := hx6
  have K6_L := hx6
  exact .inr ⟨tl9_1, x1_0, x1_1, x1_2, te20_1, x1_3, op26_1, ol26_1, x1_4, to26_1, x1_5, tl30_1, x1_6, x1_7, te39_1, x1_8, vp45_1, vl45_1, x1_9, te45_1, x1_10, x1_11, x1_12, tl2_2, x2_0, ip2_2, il2_2, x2_1, x2_2, tl13_2, x2_3, tm18_2, x2_4, tt3_w264_3, tt3_w268_3, x3_0, x3_1, tt4_w264_4, tt4_w268_4, x4_0, x4_1, tt5_w264_5, tt5_w268_5, x5_0, x5_1, tt6_w264_6, tt6_w268_6, x6_0, x6_1, n6, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6))))), fR6, s6, E6, V6,
    by rw [r6_3, r5_3, r4_3, r3_3, r2_3, r1_3], by rw [r6_4, r5_4, r4_4, r3_4, r2_4, r1_4], r6_2, r6_18, r6_19, r6_20, r6_21, r6_22, r6_23, r6_24, r6_25, r6_26, r6_27, w6_264, w6_268, ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_74)))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans ((K2_L.w32 (by decide) (by decide)).trans ((K1_L.w32 (by decide) (by decide)).trans w0_78)))))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans w2_3c)))), ((K6_L.w32 (by decide) (by decide)).trans ((K5_L.w32 (by decide) (by decide)).trans ((K4_L.w32 (by decide) (by decide)).trans ((K3_L.w32 (by decide) (by decide)).trans w2_7c)))), ((((((K1_L).trans K2_L).trans K3_L).trans K4_L).trans K5_L).trans K6_L).mono (by decide)⟩

end C3.RV32.Sv
