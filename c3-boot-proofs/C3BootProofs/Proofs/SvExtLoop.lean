import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvSegExt
import C3BootProofs.Proofs.SvL7

/-!
# `sigstore::verify`: the leaf's extensions

Written by `scripts/gen-sv-relloop.py` from `sv_seg_ext` and `sv_l7`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option linter.unusedVariables false in
/-- One more extension of the leaf, from state `s` to `s'`: there are bytes left, and the next extension is one `sigstore::verify` accepts. -/
def sv_extStep (B out bp tbp dg rootp ll sgp kp sgl tbl p0 L w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c : Word) (v : Nat → Word) (M0 : Word → BitVec 8) : Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word → Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word → Prop :=
  fun s s' => s.2.2.1 ≠ 0 ∧ ((s.2.2.1).toNat ≤ L.toNat) ∧ ∃ tl10_1, derElement 0x30 (memBytes M0 ((s.2.2.2.2.2.2.2.2.2.2.2.2.2)) ((s.2.2.1)).toNat) = .ok tl10_1 ∧ ∃ op21_1 ol21_1, derContent (((s.2.2.2.2.2.2.2.2.2.2.2.2.2)) + BitVec.ofNat 32 tl10_1.header) (derOid (memBytes M0 (((s.2.2.2.2.2.2.2.2.2.2.2.2.2)) + BitVec.ofNat 32 tl10_1.header) (BitVec.ofNat 32 tl10_1.len).toNat)) = .ok (op21_1, ol21_1) ∧ ∃ to21_1, derOid (memBytes M0 (((s.2.2.2.2.2.2.2.2.2.2.2.2.2)) + BitVec.ofNat 32 tl10_1.header) (BitVec.ofNat 32 tl10_1.len).toNat) = .ok to21_1 ∧ ∃ x2_w34_2 : Word, ∃ x2_w38_2 : Word, ((False) ∨ ((¬ (((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len)) = 0)) ∧ (M0 ((((s.2.2.2.2.2.2.2.2.2.2.2.2.2)) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len)) = BitVec.ofNat 8 1) ∧ derBoolOf (memBytes M0 (((((s.2.2.2.2.2.2.2.2.2.2.2.2.2)) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len))) (((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len))).toNat) (derElement 1 (memBytes M0 (((((s.2.2.2.2.2.2.2.2.2.2.2.2.2)) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len))) (((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len))).toNat)) = .ok () ∧ ∃ tb7_1, derElement 1 (memBytes M0 (((((s.2.2.2.2.2.2.2.2.2.2.2.2.2)) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len))) (((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len))).toNat) = .ok tb7_1 ∧ ∃ vp14_1 vl14_1, derContent ((((((s.2.2.2.2.2.2.2.2.2.2.2.2.2)) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len))) + BitVec.ofNat 32 (tb7_1.header + tb7_1.len)) (derElement 4 (memBytes M0 ((((((s.2.2.2.2.2.2.2.2.2.2.2.2.2)) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len))) + BitVec.ofNat 32 (tb7_1.header + tb7_1.len)) ((((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len))) - BitVec.ofNat 32 (tb7_1.header + tb7_1.len)).toNat)) = .ok (vp14_1, vl14_1) ∧ ∃ te14_1, derElement 4 (memBytes M0 ((((((s.2.2.2.2.2.2.2.2.2.2.2.2.2)) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len))) + BitVec.ofNat 32 (tb7_1.header + tb7_1.len)) ((((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len))) - BitVec.ofNat 32 (tb7_1.header + tb7_1.len)).toNat) = .ok te14_1 ∧ (((((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len))) - BitVec.ofNat 32 (tb7_1.header + tb7_1.len)) - BitVec.ofNat 32 (te14_1.header + te14_1.len) = 0) ∧ listsOidOf M0 p0 (L.toNat - (s.2.2.1).toNat) (memBytes M0 op21_1 ol21_1.toNat) = .ok false ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3 = memBytes M0 op21_1 ol21_1.toNat ∨ memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x3)) 3 = memBytes M0 op21_1 ol21_1.toNat ∨ memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3 = memBytes M0 op21_1 ol21_1.toNat ∨ memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3 = memBytes M0 op21_1 ol21_1.toNat) ∧ x2_w34_2 = vl14_1 ∧ x2_w38_2 = vp14_1) ∨ ((¬ (((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len)) = 0)) ∧ (¬ (M0 ((((s.2.2.2.2.2.2.2.2.2.2.2.2.2)) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len)) = BitVec.ofNat 8 1)) ∧ ∃ vp8 vl8, derContent (((((s.2.2.2.2.2.2.2.2.2.2.2.2.2)) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len))) (derElement 4 (memBytes M0 (((((s.2.2.2.2.2.2.2.2.2.2.2.2.2)) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len))) (((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len))).toNat)) = .ok (vp8, vl8) ∧ ∃ te8, derElement 4 (memBytes M0 (((((s.2.2.2.2.2.2.2.2.2.2.2.2.2)) + BitVec.ofNat 32 tl10_1.header) + BitVec.ofNat 32 (to21_1.header + to21_1.len))) (((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len))).toNat) = .ok te8 ∧ ((((BitVec.ofNat 32 tl10_1.len) - BitVec.ofNat 32 (to21_1.header + to21_1.len))) - BitVec.ofNat 32 (te8.header + te8.len) = 0) ∧ listsOidOf M0 p0 (L.toNat - (s.2.2.1).toNat) (memBytes M0 op21_1 ol21_1.toNat) = .ok false ∧ x2_w34_2 = vl8 ∧ x2_w38_2 = vp8)) ∧ SvIn B x2_w38_2 x2_w34_2.toNat ∧ ∃ d_w2c_3 : Word, ∃ d_w30_3 : Word, ∃ d_w80_3 : Word, ∃ d_w84_3 : Word, ∃ d_w88_3 : Word, ∃ d_w8c_3 : Word, ∃ d_w90_3 : Word, ∃ d_w94_3 : Word, ∃ d_w98_3 : Word, ∃ d_w9c_3 : Word, ∃ d_wa0_3 : Word, ∃ d_wa4_3 : Word, (((memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3) ∧ ∃ tl15_1, derElement 0x3 (memBytes M0 (x2_w38_2) (x2_w34_2).toNat) = .ok tl15_1 ∧ (2 ≤ (BitVec.ofNat 32 tl15_1.len).toNat) ∧ (BitVec.ofNat 32 (kuUnused (M0 (((((x2_w38_2) + BitVec.ofNat 32 tl15_1.header)) + ((BitVec.ofNat 32 tl15_1.len))) + BitVec.ofNat 32 0xFFFFFFFF))) = (M0 ((x2_w38_2) + BitVec.ofNat 32 tl15_1.header)).zeroExtend 32) ∧ (((x2_w34_2) - BitVec.ofNat 32 (tl15_1.header + tl15_1.len)) = 0) ∧ (¬ (M0 (((x2_w38_2) + BitVec.ofNat 32 tl15_1.header) + 0x1)).toNat < 0x80) ∧ d_w2c_3 = (s.1) ∧ d_w30_3 = BitVec.ofNat 32 0x1 ∧ d_w80_3 = (s.2.2.2.1) ∧ d_w84_3 = (s.2.2.2.2.1) ∧ d_w88_3 = (s.2.2.2.2.2.1) ∧ d_w8c_3 = (s.2.2.2.2.2.2.1) ∧ d_w90_3 = (s.2.2.2.2.2.2.2.1) ∧ d_w94_3 = (s.2.2.2.2.2.2.2.2.1) ∧ d_w98_3 = (s.2.2.2.2.2.2.2.2.2.1) ∧ d_w9c_3 = (s.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa0_3 = (s.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa4_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.1)) ∨ ((¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3) ∧ ∃ tl21_1, derElement 0x30 (memBytes M0 (x2_w38_2) (x2_w34_2).toNat) = .ok tl21_1 ∧ ((x2_w34_2) - BitVec.ofNat 32 (tl21_1.header + tl21_1.len) = 0) ∧ ∃ k_2 cp'_2 cl'_2 found'_2, svChain (sv_ekuStep B out bp tbp dg rootp ll sgp kp sgl tbl (s.1) (s.2.1) 0 p0 L (((s.2.2.2.2.2.2.2.2.2.2.2.2.2)) + BitVec.ofNat 32 (tl10_1.header + tl10_1.len)) (s.2.2.2.1) (s.2.2.2.2.1) (s.2.2.2.2.2.1) (s.2.2.2.2.2.2.1) (s.2.2.2.2.2.2.2.1) (s.2.2.2.2.2.2.2.2.1) (s.2.2.2.2.2.2.2.2.2.1) (s.2.2.2.2.2.2.2.2.2.2.1) (s.2.2.2.2.2.2.2.2.2.2.2.1) (s.2.2.2.2.2.2.2.2.2.2.2.2.1) w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c (((s.2.2.1)) - BitVec.ofNat 32 (tl10_1.header + tl10_1.len)) v M0) k_2 (((x2_w38_2) + BitVec.ofNat 32 tl21_1.header), (BitVec.ofNat 32 tl21_1.len), (BitVec.ofNat 32 0x0)) (cp'_2, cl'_2, found'_2) ∧ cl'_2 = 0 ∧ (found'_2 &&& BitVec.ofNat 32 0x1 ≠ 0) ∧ d_w2c_3 = BitVec.ofNat 32 0x1 ∧ d_w30_3 = (s.2.1) ∧ d_w80_3 = (s.2.2.2.1) ∧ d_w84_3 = (s.2.2.2.2.1) ∧ d_w88_3 = (s.2.2.2.2.2.1) ∧ d_w8c_3 = (s.2.2.2.2.2.2.1) ∧ d_w90_3 = (s.2.2.2.2.2.2.2.1) ∧ d_w94_3 = (s.2.2.2.2.2.2.2.2.1) ∧ d_w98_3 = (s.2.2.2.2.2.2.2.2.2.1) ∧ d_w9c_3 = (s.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa0_3 = (s.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa4_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.1)) ∨ ((¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3) ∧ ∃ tl27_1, derElement 0x30 (memBytes M0 (x2_w38_2) (x2_w34_2).toNat) = .ok tl27_1 ∧ ((x2_w34_2) - BitVec.ofNat 32 (tl27_1.header + tl27_1.len) = 0) ∧ ((((BitVec.ofNat 32 tl27_1.len) = 0)) ∨ ((¬ ((BitVec.ofNat 32 tl27_1.len) = 0)) ∧ (M0 ((x2_w38_2) + BitVec.ofNat 32 tl27_1.header) ≠ BitVec.ofNat 8 1) ∧ (M0 ((x2_w38_2) + BitVec.ofNat 32 tl27_1.header) = BitVec.ofNat 8 2) ∧ ∃ ip10 il10, derIntOf (memBytes M0 (((x2_w38_2) + BitVec.ofNat 32 tl27_1.header)) ((BitVec.ofNat 32 tl27_1.len)).toNat) (((x2_w38_2) + BitVec.ofNat 32 tl27_1.header)) (derElement 2 (memBytes M0 (((x2_w38_2) + BitVec.ofNat 32 tl27_1.header)) ((BitVec.ofNat 32 tl27_1.len)).toNat)) = .ok (ip10, il10) ∧ ∃ ti10, derElement 2 (memBytes M0 (((x2_w38_2) + BitVec.ofNat 32 tl27_1.header)) ((BitVec.ofNat 32 tl27_1.len)).toNat) = .ok ti10 ∧ (((BitVec.ofNat 32 tl27_1.len)) - BitVec.ofNat 32 (ti10.header + ti10.len) = 0))) ∧ d_w2c_3 = (s.1) ∧ d_w30_3 = (s.2.1) ∧ d_w80_3 = (s.2.2.2.1) ∧ d_w84_3 = (s.2.2.2.2.1) ∧ d_w88_3 = (s.2.2.2.2.2.1) ∧ d_w8c_3 = (s.2.2.2.2.2.2.1) ∧ d_w90_3 = (s.2.2.2.2.2.2.2.1) ∧ d_w94_3 = (s.2.2.2.2.2.2.2.2.1) ∧ d_w98_3 = (s.2.2.2.2.2.2.2.2.2.1) ∧ d_w9c_3 = (s.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa0_3 = (s.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa4_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.1)) ∨ ((¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op21_1 ol21_1.toNat) ∧ ∃ tl43, derTlv (memBytes M0 (x2_w38_2) (x2_w34_2).toNat) = .ok tl43 ∧ (BitVec.ofNat 8 tl43.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w34_2) - BitVec.ofNat 32 (tl43.header + tl43.len) = 0) ∧ d_w2c_3 = (s.1) ∧ d_w30_3 = (s.2.1) ∧ d_w80_3 = (x2_w38_2) + BitVec.ofNat 32 tl43.header ∧ d_w84_3 = BitVec.ofNat 32 tl43.len ∧ d_w88_3 = (s.2.2.2.2.2.1) ∧ d_w8c_3 = (s.2.2.2.2.2.2.1) ∧ d_w90_3 = (s.2.2.2.2.2.2.2.1) ∧ d_w94_3 = (s.2.2.2.2.2.2.2.2.1) ∧ d_w98_3 = (s.2.2.2.2.2.2.2.2.2.1) ∧ d_w9c_3 = (s.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa0_3 = (s.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa4_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.1)) ∨ ((¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x37)) 10 = memBytes M0 op21_1 ol21_1.toNat) ∧ ∃ tl56, derTlv (memBytes M0 (x2_w38_2) (x2_w34_2).toNat) = .ok tl56 ∧ (BitVec.ofNat 8 tl56.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w34_2) - BitVec.ofNat 32 (tl56.header + tl56.len) = 0) ∧ d_w2c_3 = (s.1) ∧ d_w30_3 = (s.2.1) ∧ d_w80_3 = (s.2.2.2.1) ∧ d_w84_3 = (s.2.2.2.2.1) ∧ d_w88_3 = (x2_w38_2) + BitVec.ofNat 32 tl56.header ∧ d_w8c_3 = BitVec.ofNat 32 tl56.len ∧ d_w90_3 = (s.2.2.2.2.2.2.2.1) ∧ d_w94_3 = (s.2.2.2.2.2.2.2.2.1) ∧ d_w98_3 = (s.2.2.2.2.2.2.2.2.2.1) ∧ d_w9c_3 = (s.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa0_3 = (s.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa4_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.1)) ∨ ((¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x37)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x41)) 10 = memBytes M0 op21_1 ol21_1.toNat) ∧ ∃ tl69, derTlv (memBytes M0 (x2_w38_2) (x2_w34_2).toNat) = .ok tl69 ∧ (BitVec.ofNat 8 tl69.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w34_2) - BitVec.ofNat 32 (tl69.header + tl69.len) = 0) ∧ d_w2c_3 = (s.1) ∧ d_w30_3 = (s.2.1) ∧ d_w80_3 = (s.2.2.2.1) ∧ d_w84_3 = (s.2.2.2.2.1) ∧ d_w88_3 = (s.2.2.2.2.2.1) ∧ d_w8c_3 = (s.2.2.2.2.2.2.1) ∧ d_w90_3 = (x2_w38_2) + BitVec.ofNat 32 tl69.header ∧ d_w94_3 = BitVec.ofNat 32 tl69.len ∧ d_w98_3 = (s.2.2.2.2.2.2.2.2.2.1) ∧ d_w9c_3 = (s.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa0_3 = (s.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa4_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.1)) ∨ ((¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x37)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x41)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x4B)) 10 = memBytes M0 op21_1 ol21_1.toNat) ∧ ∃ tl82, derTlv (memBytes M0 (x2_w38_2) (x2_w34_2).toNat) = .ok tl82 ∧ (BitVec.ofNat 8 tl82.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w34_2) - BitVec.ofNat 32 (tl82.header + tl82.len) = 0) ∧ d_w2c_3 = (s.1) ∧ d_w30_3 = (s.2.1) ∧ d_w80_3 = (s.2.2.2.1) ∧ d_w84_3 = (s.2.2.2.2.1) ∧ d_w88_3 = (s.2.2.2.2.2.1) ∧ d_w8c_3 = (s.2.2.2.2.2.2.1) ∧ d_w90_3 = (s.2.2.2.2.2.2.2.1) ∧ d_w94_3 = (s.2.2.2.2.2.2.2.2.1) ∧ d_w98_3 = (x2_w38_2) + BitVec.ofNat 32 tl82.header ∧ d_w9c_3 = BitVec.ofNat 32 tl82.len ∧ d_wa0_3 = (s.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa4_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.1)) ∨ ((¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x37)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x41)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x4B)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x55)) 10 = memBytes M0 op21_1 ol21_1.toNat) ∧ ∃ tl95, derTlv (memBytes M0 (x2_w38_2) (x2_w34_2).toNat) = .ok tl95 ∧ (BitVec.ofNat 8 tl95.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w34_2) - BitVec.ofNat 32 (tl95.header + tl95.len) = 0) ∧ d_w2c_3 = (s.1) ∧ d_w30_3 = (s.2.1) ∧ d_w80_3 = (s.2.2.2.1) ∧ d_w84_3 = (s.2.2.2.2.1) ∧ d_w88_3 = (s.2.2.2.2.2.1) ∧ d_w8c_3 = (s.2.2.2.2.2.2.1) ∧ d_w90_3 = (s.2.2.2.2.2.2.2.1) ∧ d_w94_3 = (s.2.2.2.2.2.2.2.2.1) ∧ d_w98_3 = (s.2.2.2.2.2.2.2.2.2.1) ∧ d_w9c_3 = (s.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa0_3 = (x2_w38_2) + BitVec.ofNat 32 tl95.header ∧ d_wa4_3 = BitVec.ofNat 32 tl95.len) ∨ ((¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3)) ∧ (¬ (memBytes M0 op21_1 ol21_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x2D)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x37)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x41)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x4B)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x55)) 10 = memBytes M0 op21_1 ol21_1.toNat)) ∧ d_w2c_3 = (s.1) ∧ d_w30_3 = (s.2.1) ∧ d_w80_3 = (s.2.2.2.1) ∧ d_w84_3 = (s.2.2.2.2.1) ∧ d_w88_3 = (s.2.2.2.2.2.1) ∧ d_w8c_3 = (s.2.2.2.2.2.2.1) ∧ d_w90_3 = (s.2.2.2.2.2.2.2.1) ∧ d_w94_3 = (s.2.2.2.2.2.2.2.2.1) ∧ d_w98_3 = (s.2.2.2.2.2.2.2.2.2.1) ∧ d_w9c_3 = (s.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa0_3 = (s.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa4_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.1))) ∧ (d_w80_3 = 0 ∨ SvIn B d_w80_3 d_w84_3.toNat) ∧ (d_w88_3 = 0 ∨ SvIn B d_w88_3 d_w8c_3.toNat) ∧ (d_w90_3 = 0 ∨ SvIn B d_w90_3 d_w94_3.toNat) ∧ (d_w98_3 = 0 ∨ SvIn B d_w98_3 d_w9c_3.toNat) ∧ (d_wa0_3 = 0 ∨ SvIn B d_wa0_3 d_wa4_3.toNat) ∧ s' = (d_w2c_3, d_w30_3, ((s.2.2.1)) - BitVec.ofNat 32 (tl10_1.header + tl10_1.len), d_w80_3, d_w84_3, d_w88_3, d_w8c_3, d_w90_3, d_w94_3, d_w98_3, d_w9c_3, d_wa0_3, d_wa4_3, ((s.2.2.2.2.2.2.2.2.2.2.2.2.2)) + BitVec.ofNat 32 (tl10_1.header + tl10_1.len))

set_option linter.unusedVariables false in
/-- How `sv_l7` ends once `rem` is 0. -/
def sv_extloopOk (B out bp tbp dg rootp ll sgp kp sgl tbl p0 L w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (f2c' : Word) (f30' : Word) (rem' : Word) (sl0' : Word) (sl1' : Word) (sl2' : Word) (sl3' : Word) (sl4' : Word) (sl5' : Word) (sl6' : Word) (sl7' : Word) (sl8' : Word) (sl9' : Word) (cur' : Word) (nk : Machine) : Prop :=
  rem' = 0 ∧ (sl0' = 0 ∨ SvIn B sl0' sl1'.toNat) ∧ (sl2' = 0 ∨ SvIn B sl2' sl3'.toNat) ∧ (sl4' = 0 ∨ SvIn B sl4' sl5'.toNat) ∧ (sl6' = 0 ∨ SvIn B sl6' sl7'.toNat) ∧ (sl8' = 0 ∨ SvIn B sl8' sl9'.toNat) ∧ (((sl0' ≠ 0) ∧
    (sl2' ≠ 0) ∧
    (sl4' ≠ 0) ∧
    (sl6' ≠ 0) ∧
    ((if BitVec.ult 0 (sl8') then (1 : Word) else 0) &&& ((f2c') &&& (f30')) ≠ 0) ∧
    (memBytes M0 w7c (w78.toNat) = memBytes M0 w74 (w70.toNat)) ∧
    ∃ sr40 ss40, ecdsaSigOf 48 M0 (sgp) ((sgl.toNat)) = .ok (sr40, ss40) ∧
    ∃ n', Steps nk n' ∧
        St n'.mem SV n' 0x86A (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg nk (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg nk (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = (BitVec.ofNat 8 ((sr40).getD 0 0)).zeroExtend 32 ∧
        reg n' (9 : Fin 32) = tbp ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = dg ∧
        reg n' (21 : Fin 32) = rootp ∧
        reg n' (22 : Fin 32) = ll ∧
        reg n' (24 : Fin 32) = kp ∧
        reg n' (26 : Fin 32) = sl0' ∧
        reg n' (27 : Fin 32) = tbl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl9' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl7' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl5' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl3' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl1' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl8' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl6' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = sl4' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = sl2' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (w70.toNat) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (w78.toNat) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x81 + j)) = BitVec.ofNat 8 ((sr40).getD j 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xB1 + j)) = BitVec.ofNat 8 ((ss40).getD j 0)) ∧
        SvKeepL B nk.mem n'.mem [(0x50, 0x4), (0x4C, 0x4), (0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x80, 0x61)]))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- The extensions loop: `k` more extensions, then the end. -/
theorem sv_extloop {B out bp tbp dg rootp ll sgp kp sgl tbl p0 L w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c : Word} {v : Nat → Word}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8) :
    ∀ (N : Nat) {f2c : Word} {f30 : Word} {rem : Word} {sl0 : Word} {sl1 : Word} {sl2 : Word} {sl3 : Word} {sl4 : Word} {sl5 : Word} {sl6 : Word} {sl7 : Word} {sl8 : Word} {sl9 : Word} {cur : Word} {n0 : Machine},
    (hN : rem.toNat ≤ N) →
    (E0 : SvCode n0.mem) →
    (V0 : SvSaves B n0.mem v) →
    (s0 : St n0.mem SV n0 0x3B8 (reg n0)) →
    (fM : ∀ x, SvR B x → n0.mem x = M0 x) →
    (g0_2 : reg n0 sp = B + 0x21A0) →
    (g0_8 : reg n0 (8 : Fin 32) = BitVec.ofNat 32 0x15) →
    (g0_9 : reg n0 (9 : Fin 32) = tbp) →
    (g0_18 : reg n0 (18 : Fin 32) = out) →
    (g0_19 : reg n0 (19 : Fin 32) = bp) →
    (g0_20 : reg n0 (20 : Fin 32) = dg) →
    (g0_21 : reg n0 (21 : Fin 32) = rootp) →
    (g0_22 : reg n0 (22 : Fin 32) = ll) →
    (g0_23 : reg n0 (23 : Fin 32) = sgp) →
    (g0_24 : reg n0 (24 : Fin 32) = kp) →
    (g0_25 : reg n0 (25 : Fin 32) = sgl) →
    (g0_27 : reg n0 (27 : Fin 32) = tbl) →
    (w0_2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c) →
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30) →
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem) →
    (w0_54 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54) →
    (w0_58 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58) →
    (w0_5c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c) →
    (w0_60 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60) →
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64) →
    (w0_68 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68) →
    (w0_6c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c) →
    (w0_70 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70) →
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74) →
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78) →
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c) →
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0) →
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1) →
    (w0_88 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2) →
    (w0_8c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3) →
    (w0_90 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4) →
    (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5) →
    (w0_98 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6) →
    (w0_9c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7) →
    (w0_a0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8) →
    (w0_a4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9) →
    (w0_150 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0) →
    (w0_154 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L) →
    (w0_158 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur) →
    (w0_15c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rem) →
    (xl_in : SvIn B (cur) (rem).toNat) →
    (SD0 : SvData M0) →
    (sl0_or0 : sl0 = 0 ∨ SvIn B sl0 sl1.toNat) →
    (sl2_or0 : sl2 = 0 ∨ SvIn B sl2 sl3.toNat) →
    (sl4_or0 : sl4 = 0 ∨ SvIn B sl4 sl5.toNat) →
    (sl6_or0 : sl6 = 0 ∨ SvIn B sl6 sl7.toNat) →
    (sl8_or0 : sl8 = 0 ∨ SvIn B sl8 sl9.toNat) →
    (el_in : SvIn B p0 L.toNat) →
    (or_in : SvIn B w7c (w78.toNat)) →
    (ar_in : SvIn B w74 (w70.toNat)) →
    (sg_in : SvIn B sgp (sgl.toNat)) →
    SvErrRet B out v n0 ∨ ∃ k f2c' f30' rem' sl0' sl1' sl2' sl3' sl4' sl5' sl6' sl7' sl8' sl9' cur', svChain (sv_extStep B out bp tbp dg rootp ll sgp kp sgl tbl p0 L w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c v M0) k (f2c, f30, rem, sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, cur) (f2c', f30', rem', sl0', sl1', sl2', sl3', sl4', sl5', sl6', sl7', sl8', sl9', cur') ∧
      ∃ nk, Steps n0 nk ∧ reg nk (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg nk (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
      SvKeepL B n0.mem nk.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x38, 0x4), (0x34, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x30, 0x4), (0x1FC, 0x4), (0x200, 0x4), (0x204, 0x4), (0x208, 0x4), (0x204, 0x8), (0x385, 0xB), (0x384, 0x1), (0x2C, 0x4), (0x80, 0x4), (0x84, 0x4), (0x88, 0x4), (0x8C, 0x4), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4)] ∧ sv_extloopOk B out bp tbp dg rootp ll sgp kp sgl tbl p0 L w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c v M0 f2c' f30' rem' sl0' sl1' sl2' sl3' sl4' sl5' sl6' sl7' sl8' sl9' cur' nk := by
  intro N
  induction N with
  | zero =>
    intro f2c f30 rem sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 cur n0 hN E0 V0 s0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_158 w0_15c xl_in SD0 sl0_or0 sl2_or0 sl4_or0 sl6_or0 sl8_or0 el_in or_in ar_in sg_in
    have h0 : rem = 0 := svRem_zero hN
    rcases sv_l7 (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (tbl := tbl) (f2c := f2c) (f30 := f30) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (orp := w7c) (arp := w74) (orl := w78.toNat) (arl := w70.toNat) (sgl := sgl.toNat) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 (g0_25.trans (ofNat_toNat_self _).symm) g0_27 w0_2c w0_30 w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_158 w0_15c w0_7c (w0_78.trans (ofNat_toNat_self _).symm) w0_74 (w0_70.trans (ofNat_toNat_self _).symm) h0 or_in ar_in sg_in with ⟨-, e⟩ | okx
    · exact .inl e
    · exact .inr ⟨0, f2c, f30, rem, sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, cur, svChain.nil, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), h0, sl0_or0, sl2_or0, sl4_or0, sl6_or0, sl8_or0, okx⟩
  | succ N ih =>
    intro f2c f30 rem sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 cur n0 hN E0 V0 s0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_158 w0_15c xl_in SD0 sl0_or0 sl2_or0 sl4_or0 sl6_or0 sl8_or0 el_in or_in ar_in sg_in
    by_cases h0 : rem = 0
    · rcases sv_l7 (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (tbl := tbl) (f2c := f2c) (f30 := f30) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (orp := w7c) (arp := w74) (orl := w78.toNat) (arl := w70.toNat) (sgl := sgl.toNat) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 (g0_25.trans (ofNat_toNat_self _).symm) g0_27 w0_2c w0_30 w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_158 w0_15c w0_7c (w0_78.trans (ofNat_toNat_self _).symm) w0_74 (w0_70.trans (ofNat_toNat_self _).symm) h0 or_in ar_in sg_in with ⟨-, e⟩ | okx
      · exact .inl e
      · exact .inr ⟨0, f2c, f30, rem, sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, cur, svChain.nil, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), h0, sl0_or0, sl2_or0, sl4_or0, sl6_or0, sl8_or0, okx⟩
    rcases sv_seg_ext (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (sgl := sgl) (tbl := tbl) (f2c := f2c) (f30 := f30) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (v := v) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_158 w0_15c xl_in ((el_in).shrink (by omega)) h0 SD0 sl0_or0 sl2_or0 sl4_or0 sl6_or0 sl8_or0 with e | ⟨x1_0, x1_1tl10_1, x1_1, x1_2op21_1, x1_2ol21_1, x1_2, x1_3to21_1, x1_3, x1_4x2_w34_2, x1_4x2_w38_2, x1_4, x1_5, x1_6d_w2c_3, x1_6d_w30_3, x1_6d_w80_3, x1_6d_w84_3, x1_6d_w88_3, x1_6d_w8c_3, x1_6d_w90_3, x1_6d_w94_3, x1_6d_w98_3, x1_6d_w9c_3, x1_6d_wa0_3, x1_6d_wa4_3, x1_6, x1_7, x1_8, x1_9, x1_10, x1_11, n1, c1, fR1, s1, E1, V1, r1_3, r1_4, r1_2, r1_8, r1_9, r1_18, r1_19, r1_20, r1_21, r1_22, r1_23, r1_24, r1_25, r1_27, w1_2c, w1_30, w1_50, w1_54, w1_58, w1_5c, w1_60, w1_64, w1_68, w1_6c, w1_70, w1_74, w1_78, w1_7c, w1_80, w1_84, w1_88, w1_8c, w1_90, w1_94, w1_98, w1_9c, w1_a0, w1_a4, w1_150, w1_154, w1_158, w1_15c, w1_3c, w1_40, w1_44, w1_48, w1_4c, w1_400, w1_34, w1_38, K1_L⟩
    · exact .inl e
    have hdec := svRem_elem x1_1 hN
    rcases ih hdec E1 V1 s1 fR1 r1_2 r1_8 r1_9 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 r1_24 r1_25 r1_27 w1_2c w1_30 w1_50 w1_54 w1_58 w1_5c w1_60 w1_64 w1_68 w1_6c w1_70 w1_74 w1_78 w1_7c w1_80 w1_84 w1_88 w1_8c w1_90 w1_94 w1_98 w1_9c w1_a0 w1_a4 w1_150 w1_154 w1_158 w1_15c ((xl_in).restW x1_1) SD0 x1_7 x1_8 x1_9 x1_10 x1_11 el_in or_in ar_in sg_in with e | ⟨k, f2c', f30', rem', sl0', sl1', sl2', sl3', sl4', sl5', sl6', sl7', sl8', sl9', cur', chn, nk, cs, h3, h4, hk, okk⟩
    · exact .inl (SvErrRet.pre c1 r1_3 r1_4 (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
    · exact .inr ⟨k + 1, f2c', f30', rem', sl0', sl1', sl2', sl3', sl4', sl5', sl6', sl7', sl8', sl9', cur', svChain.cons ⟨h0, x1_0, x1_1tl10_1, x1_1, x1_2op21_1, x1_2ol21_1, x1_2, x1_3to21_1, x1_3, x1_4x2_w34_2, x1_4x2_w38_2, x1_4, x1_5, x1_6d_w2c_3, x1_6d_w30_3, x1_6d_w80_3, x1_6d_w84_3, x1_6d_w88_3, x1_6d_w8c_3, x1_6d_w90_3, x1_6d_w94_3, x1_6d_w98_3, x1_6d_w9c_3, x1_6d_wa0_3, x1_6d_wa4_3, x1_6, x1_7, x1_8, x1_9, x1_10, x1_11, rfl⟩ chn, nk, c1.trans cs, h3.trans r1_3, h4.trans r1_4, (K1_L.trans hk).mono (by decide), okk⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `sv_extloop` as a stage. -/
theorem sv_extloop_st {B out bp tbp dg rootp ll sgp kp sgl tbl p0 L w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c : Word} {v : Nat → Word} {N : Nat} {f2c : Word} {f30 : Word} {rem : Word} {sl0 : Word} {sl1 : Word} {sl2 : Word} {sl3 : Word} {sl4 : Word} {sl5 : Word} {sl6 : Word} {sl7 : Word} {sl8 : Word} {sl9 : Word} {cur : Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8)
    (hN : rem.toNat ≤ N)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (s0 : St n0.mem SV n0 0x3B8 (reg n0))
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = BitVec.ofNat 32 0x15)
    (g0_9 : reg n0 (9 : Fin 32) = tbp)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = dg)
    (g0_21 : reg n0 (21 : Fin 32) = rootp)
    (g0_22 : reg n0 (22 : Fin 32) = ll)
    (g0_23 : reg n0 (23 : Fin 32) = sgp)
    (g0_24 : reg n0 (24 : Fin 32) = kp)
    (g0_25 : reg n0 (25 : Fin 32) = sgl)
    (g0_27 : reg n0 (27 : Fin 32) = tbl)
    (w0_2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rem)
    (w0_54 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54)
    (w0_58 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58)
    (w0_5c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c)
    (w0_60 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64)
    (w0_68 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68)
    (w0_6c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c)
    (w0_70 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c)
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0)
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1)
    (w0_88 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2)
    (w0_8c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3)
    (w0_90 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4)
    (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5)
    (w0_98 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6)
    (w0_9c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7)
    (w0_a0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8)
    (w0_a4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9)
    (w0_150 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0)
    (w0_154 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L)
    (w0_158 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur)
    (w0_15c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rem)
    (xl_in : SvIn B (cur) (rem).toNat)
    (SD0 : SvData M0)
    (sl0_or0 : sl0 = 0 ∨ SvIn B sl0 sl1.toNat)
    (sl2_or0 : sl2 = 0 ∨ SvIn B sl2 sl3.toNat)
    (sl4_or0 : sl4 = 0 ∨ SvIn B sl4 sl5.toNat)
    (sl6_or0 : sl6 = 0 ∨ SvIn B sl6 sl7.toNat)
    (sl8_or0 : sl8 = 0 ∨ SvIn B sl8 sl9.toNat)
    (el_in : SvIn B p0 L.toNat)
    (or_in : SvIn B w7c (w78.toNat))
    (ar_in : SvIn B w74 (w70.toNat))
    (sg_in : SvIn B sgp (sgl.toNat))
    :
    SvErrRet B out v n0 ∨
    (∃ k f2c' f30' rem' sl0' sl1' sl2' sl3' sl4' sl5' sl6' sl7' sl8' sl9' cur', svChain (sv_extStep B out bp tbp dg rootp ll sgp kp sgl tbl p0 L w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c v M0) k (f2c, f30, rem, sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, cur) (f2c', f30', rem', sl0', sl1', sl2', sl3', sl4', sl5', sl6', sl7', sl8', sl9', cur') ∧
      rem' = 0 ∧ (sl0' = 0 ∨ SvIn B sl0' sl1'.toNat) ∧ (sl2' = 0 ∨ SvIn B sl2' sl3'.toNat) ∧ (sl4' = 0 ∨ SvIn B sl4' sl5'.toNat) ∧ (sl6' = 0 ∨ SvIn B sl6' sl7'.toNat) ∧ (sl8' = 0 ∨ SvIn B sl8' sl9'.toNat) ∧
      (sl0' ≠ 0) ∧ (sl2' ≠ 0) ∧ (sl4' ≠ 0) ∧ (sl6' ≠ 0) ∧ ((if BitVec.ult 0 (sl8') then (1 : Word) else 0) &&& ((f2c') &&& (f30')) ≠ 0) ∧ (memBytes M0 w7c (w78.toNat) = memBytes M0 w74 (w70.toNat)) ∧ ∃ sr40 ss40, ecdsaSigOf 48 M0 (sgp) ((sgl.toNat)) = .ok (sr40, ss40) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x86A (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = (BitVec.ofNat 8 ((sr40).getD 0 0)).zeroExtend 32 ∧
        reg n' (9 : Fin 32) = tbp ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = dg ∧
        reg n' (21 : Fin 32) = rootp ∧
        reg n' (22 : Fin 32) = ll ∧
        reg n' (24 : Fin 32) = kp ∧
        reg n' (26 : Fin 32) = sl0' ∧
        reg n' (27 : Fin 32) = tbl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl9' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl7' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl5' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl3' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl1' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl8' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl6' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = sl4' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = sl2' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = BitVec.ofNat 32 (w70.toNat) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = BitVec.ofNat 32 (w78.toNat) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x81 + j)) = BitVec.ofNat 8 ((sr40).getD j 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xB1 + j)) = BitVec.ofNat 8 ((ss40).getD j 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x40, 0x4), (0x3C, 0x4), (0x420, 0x10), (0x158, 0x8), (0x44, 0x4), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x420, 0x8), (0x408, 0x8), (0x4C, 0x4), (0x48, 0x4), (0x38, 0x4), (0x34, 0x4), (0x50, 0x4), (0x380, 0x4), (0x384, 0x4), (0x388, 0x4), (0x38C, 0x4), (0x420, 0x11), (0x388, 0x8), (0x30, 0x4), (0x1FC, 0x4), (0x200, 0x4), (0x204, 0x4), (0x208, 0x4), (0x204, 0x8), (0x385, 0xB), (0x384, 0x1), (0x2C, 0x4), (0x80, 0x4), (0x84, 0x4), (0x88, 0x4), (0x8C, 0x4), (0x90, 0x4), (0x94, 0x4), (0x98, 0x4), (0x9C, 0x4), (0xA0, 0x4), (0xA4, 0x4), (0x80, 0x61)]) := by
  rcases sv_extloop (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (sgl := sgl) (tbl := tbl) (p0 := p0) (L := L) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (v := v) FW hret hO M0 N hN E0 V0 s0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_158 w0_15c xl_in SD0 sl0_or0 sl2_or0 sl4_or0 sl6_or0 sl8_or0 el_in or_in ar_in sg_in with e | ⟨k, f2c', f30', rem', sl0', sl1', sl2', sl3', sl4', sl5', sl6', sl7', sl8', sl9', cur', chn, nk, cs, hr3, hr4, hkl, okh⟩
  · exact .inl e
  obtain ⟨hz, iv0, iv1, iv2, iv3, iv4, h0, h1, h2, h3, h4, h5, sr40, ss40, h6, n1, cn, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r24, f_r26, f_r27, f_w30, f_w34, f_w38, f_w3c, f_w40, f_w44, f_w48, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_q81, f_qb1, f_KL⟩ := okh
  exact .inr ⟨k, f2c', f30', rem', sl0', sl1', sl2', sl3', sl4', sl5', sl6', sl7', sl8', sl9', cur', chn, hz, iv0, iv1, iv2, iv3, iv4, h0, h1, h2, h3, h4, h5, sr40, ss40, h6, n1, cs.trans cn, f_ST, f_E, f_V, f_FR, f_r2, f_r3.trans hr3, f_r4.trans hr4, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r24, f_r26, f_r27, f_w30, f_w34, f_w38, f_w3c, f_w40, f_w44, f_w48, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_q81, f_qb1, (hkl.trans f_KL).mono (by decide)⟩

end C3.RV32.Sv
