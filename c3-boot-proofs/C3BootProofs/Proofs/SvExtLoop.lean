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
def sv_extStep (B out bp x9 x21 x25 x26 p0 L w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 : Word) (v : Nat → Word) (M0 : Word → BitVec 8) : Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word → Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word × Word → Prop :=
  fun s s' => s.2.2.1 ≠ 0 ∧ ((s.2.2.1).toNat ≤ L.toNat) ∧ ∃ tl8_1, derElement 0x30 (memBytes M0 ((s.2.2.2.1)) ((s.2.2.1)).toNat) = .ok tl8_1 ∧ ∃ op19_1 ol19_1, derContent (((s.2.2.2.1)) + BitVec.ofNat 32 tl8_1.header) (derOid (memBytes M0 (((s.2.2.2.1)) + BitVec.ofNat 32 tl8_1.header) (BitVec.ofNat 32 tl8_1.len).toNat)) = .ok (op19_1, ol19_1) ∧ ∃ to19_1, derOid (memBytes M0 (((s.2.2.2.1)) + BitVec.ofNat 32 tl8_1.header) (BitVec.ofNat 32 tl8_1.len).toNat) = .ok to19_1 ∧ ∃ x2_w38_2 : Word, ∃ x2_w3c_2 : Word, ((False) ∨ ((¬ (((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len)) = 0)) ∧ (M0 ((((s.2.2.2.1)) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len)) = BitVec.ofNat 8 1) ∧ derBoolOf (memBytes M0 (((((s.2.2.2.1)) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len))) (((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len))).toNat) (derElement 1 (memBytes M0 (((((s.2.2.2.1)) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len))) (((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len))).toNat)) = .ok () ∧ ∃ tb7, derElement 1 (memBytes M0 (((((s.2.2.2.1)) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len))) (((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len))).toNat) = .ok tb7 ∧ ∃ vp14 vl14, derContent ((((((s.2.2.2.1)) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len))) + BitVec.ofNat 32 (tb7.header + tb7.len)) (derElement 4 (memBytes M0 ((((((s.2.2.2.1)) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len))) + BitVec.ofNat 32 (tb7.header + tb7.len)) ((((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len))) - BitVec.ofNat 32 (tb7.header + tb7.len)).toNat)) = .ok (vp14, vl14) ∧ ∃ te14, derElement 4 (memBytes M0 ((((((s.2.2.2.1)) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len))) + BitVec.ofNat 32 (tb7.header + tb7.len)) ((((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len))) - BitVec.ofNat 32 (tb7.header + tb7.len)).toNat) = .ok te14 ∧ (((((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len))) - BitVec.ofNat 32 (tb7.header + tb7.len)) - BitVec.ofNat 32 (te14.header + te14.len) = 0) ∧ listsOidOf M0 p0 (L.toNat - (s.2.2.1).toNat) (memBytes M0 op19_1 ol19_1.toNat) = .ok false ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x71)) 3 = memBytes M0 op19_1 ol19_1.toNat ∨ memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x74)) 3 = memBytes M0 op19_1 ol19_1.toNat ∨ memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x77)) 3 = memBytes M0 op19_1 ol19_1.toNat ∨ memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x7A)) 3 = memBytes M0 op19_1 ol19_1.toNat) ∧ x2_w38_2 = vl14 ∧ x2_w3c_2 = vp14) ∨ ((¬ (((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len)) = 0)) ∧ (¬ (M0 ((((s.2.2.2.1)) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len)) = BitVec.ofNat 8 1)) ∧ ∃ vp8 vl8, derContent (((((s.2.2.2.1)) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len))) (derElement 4 (memBytes M0 (((((s.2.2.2.1)) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len))) (((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len))).toNat)) = .ok (vp8, vl8) ∧ ∃ te8, derElement 4 (memBytes M0 (((((s.2.2.2.1)) + BitVec.ofNat 32 tl8_1.header) + BitVec.ofNat 32 (to19_1.header + to19_1.len))) (((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len))).toNat) = .ok te8 ∧ ((((BitVec.ofNat 32 tl8_1.len) - BitVec.ofNat 32 (to19_1.header + to19_1.len))) - BitVec.ofNat 32 (te8.header + te8.len) = 0) ∧ listsOidOf M0 p0 (L.toNat - (s.2.2.1).toNat) (memBytes M0 op19_1 ol19_1.toNat) = .ok false ∧ x2_w38_2 = vl8 ∧ x2_w3c_2 = vp8)) ∧ SvIn B x2_w3c_2 x2_w38_2.toNat ∧ ∃ d_w30_3 : Word, ∃ d_w34_3 : Word, ∃ d_wa20_3 : Word, ∃ d_wa24_3 : Word, ∃ d_wa28_3 : Word, ∃ d_wa2c_3 : Word, ∃ d_wa30_3 : Word, ∃ d_wa34_3 : Word, ∃ d_wa38_3 : Word, ∃ d_wa3c_3 : Word, ∃ d_wa40_3 : Word, ∃ d_wa44_3 : Word, (((memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x71)) 3) ∧ ∃ tl16_1, derElement 0x3 (memBytes M0 (x2_w3c_2) (x2_w38_2).toNat) = .ok tl16_1 ∧ (2 ≤ (BitVec.ofNat 32 tl16_1.len).toNat) ∧ (BitVec.ofNat 32 (kuUnused (M0 (((((x2_w3c_2) + BitVec.ofNat 32 tl16_1.header)) + ((BitVec.ofNat 32 tl16_1.len))) + BitVec.ofNat 32 0xFFFFFFFF))) = (M0 ((x2_w3c_2) + BitVec.ofNat 32 tl16_1.header)).zeroExtend 32) ∧ (((x2_w38_2) - BitVec.ofNat 32 (tl16_1.header + tl16_1.len)) = 0) ∧ (¬ (M0 (((x2_w3c_2) + BitVec.ofNat 32 tl16_1.header) + 0x1)).toNat < 0x80) ∧ d_w30_3 = (s.1) ∧ d_w34_3 = BitVec.ofNat 32 0x1 ∧ d_wa20_3 = (s.2.2.2.2.1) ∧ d_wa24_3 = (s.2.2.2.2.2.1) ∧ d_wa28_3 = (s.2.2.2.2.2.2.1) ∧ d_wa2c_3 = (s.2.2.2.2.2.2.2.1) ∧ d_wa30_3 = (s.2.2.2.2.2.2.2.2.1) ∧ d_wa34_3 = (s.2.2.2.2.2.2.2.2.2.1) ∧ d_wa38_3 = (s.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa3c_3 = (s.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa40_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa44_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.2)) ∨ ((¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x71)) 3)) ∧ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x7A)) 3) ∧ ∃ tl19_1, derElement 0x30 (memBytes M0 (x2_w3c_2) (x2_w38_2).toNat) = .ok tl19_1 ∧ ((x2_w38_2) - BitVec.ofNat 32 (tl19_1.header + tl19_1.len) = 0) ∧ ∃ k_2 found'_2 cp'_2 cl'_2, svChain (sv_ekuStep B out bp x9 x21 x25 x26 (s.1) (s.2.1) (s.2.2.1) p0 L (((s.2.2.2.1)) + BitVec.ofNat 32 (tl8_1.header + tl8_1.len)) (s.2.2.2.2.1) (s.2.2.2.2.2.1) (s.2.2.2.2.2.2.1) (s.2.2.2.2.2.2.2.1) (s.2.2.2.2.2.2.2.2.1) (s.2.2.2.2.2.2.2.2.2.1) (s.2.2.2.2.2.2.2.2.2.2.1) (s.2.2.2.2.2.2.2.2.2.2.2.1) (s.2.2.2.2.2.2.2.2.2.2.2.2.1) (s.2.2.2.2.2.2.2.2.2.2.2.2.2) w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 (((s.2.2.1)) - BitVec.ofNat 32 (tl8_1.header + tl8_1.len)) v M0) k_2 ((BitVec.ofNat 32 0x0), ((x2_w3c_2) + BitVec.ofNat 32 tl19_1.header), (BitVec.ofNat 32 tl19_1.len)) (found'_2, cp'_2, cl'_2) ∧ cl'_2 = 0 ∧ (found'_2 &&& BitVec.ofNat 32 0x1 ≠ 0) ∧ d_w30_3 = BitVec.ofNat 32 0x1 ∧ d_w34_3 = (s.2.1) ∧ d_wa20_3 = (s.2.2.2.2.1) ∧ d_wa24_3 = (s.2.2.2.2.2.1) ∧ d_wa28_3 = (s.2.2.2.2.2.2.1) ∧ d_wa2c_3 = (s.2.2.2.2.2.2.2.1) ∧ d_wa30_3 = (s.2.2.2.2.2.2.2.2.1) ∧ d_wa34_3 = (s.2.2.2.2.2.2.2.2.2.1) ∧ d_wa38_3 = (s.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa3c_3 = (s.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa40_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa44_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.2)) ∨ ((¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x71)) 3)) ∧ (¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x7A)) 3)) ∧ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x77)) 3) ∧ ∃ tl24_1, derElement 0x30 (memBytes M0 (x2_w3c_2) (x2_w38_2).toNat) = .ok tl24_1 ∧ ((x2_w38_2) - BitVec.ofNat 32 (tl24_1.header + tl24_1.len) = 0) ∧ ((((BitVec.ofNat 32 tl24_1.len) = 0)) ∨ ((¬ ((BitVec.ofNat 32 tl24_1.len) = 0)) ∧ (M0 ((x2_w3c_2) + BitVec.ofNat 32 tl24_1.header) ≠ BitVec.ofNat 8 1) ∧ (M0 ((x2_w3c_2) + BitVec.ofNat 32 tl24_1.header) = BitVec.ofNat 8 2) ∧ ∃ ip10 il10, derIntOf (memBytes M0 (((x2_w3c_2) + BitVec.ofNat 32 tl24_1.header)) ((BitVec.ofNat 32 tl24_1.len)).toNat) (((x2_w3c_2) + BitVec.ofNat 32 tl24_1.header)) (derElement 2 (memBytes M0 (((x2_w3c_2) + BitVec.ofNat 32 tl24_1.header)) ((BitVec.ofNat 32 tl24_1.len)).toNat)) = .ok (ip10, il10) ∧ ∃ ti10, derElement 2 (memBytes M0 (((x2_w3c_2) + BitVec.ofNat 32 tl24_1.header)) ((BitVec.ofNat 32 tl24_1.len)).toNat) = .ok ti10 ∧ (((BitVec.ofNat 32 tl24_1.len)) - BitVec.ofNat 32 (ti10.header + ti10.len) = 0))) ∧ d_w30_3 = (s.1) ∧ d_w34_3 = (s.2.1) ∧ d_wa20_3 = (s.2.2.2.2.1) ∧ d_wa24_3 = (s.2.2.2.2.2.1) ∧ d_wa28_3 = (s.2.2.2.2.2.2.1) ∧ d_wa2c_3 = (s.2.2.2.2.2.2.2.1) ∧ d_wa30_3 = (s.2.2.2.2.2.2.2.2.1) ∧ d_wa34_3 = (s.2.2.2.2.2.2.2.2.2.1) ∧ d_wa38_3 = (s.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa3c_3 = (s.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa40_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa44_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.2)) ∨ ((¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x71)) 3)) ∧ (¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x7A)) 3)) ∧ (¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x77)) 3)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xA0)) 10 = memBytes M0 op19_1 ol19_1.toNat) ∧ ∃ tl35, derTlv (memBytes M0 (x2_w3c_2) (x2_w38_2).toNat) = .ok tl35 ∧ (BitVec.ofNat 8 tl35.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w38_2) - BitVec.ofNat 32 (tl35.header + tl35.len) = 0) ∧ d_w30_3 = (s.1) ∧ d_w34_3 = (s.2.1) ∧ d_wa20_3 = (x2_w3c_2) + BitVec.ofNat 32 tl35.header ∧ d_wa24_3 = BitVec.ofNat 32 tl35.len ∧ d_wa28_3 = (s.2.2.2.2.2.2.1) ∧ d_wa2c_3 = (s.2.2.2.2.2.2.2.1) ∧ d_wa30_3 = (s.2.2.2.2.2.2.2.2.1) ∧ d_wa34_3 = (s.2.2.2.2.2.2.2.2.2.1) ∧ d_wa38_3 = (s.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa3c_3 = (s.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa40_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa44_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.2)) ∨ ((¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x71)) 3)) ∧ (¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x7A)) 3)) ∧ (¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x77)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xA0)) 10 = memBytes M0 op19_1 ol19_1.toNat)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xAA)) 10 = memBytes M0 op19_1 ol19_1.toNat) ∧ ∃ tl43, derTlv (memBytes M0 (x2_w3c_2) (x2_w38_2).toNat) = .ok tl43 ∧ (BitVec.ofNat 8 tl43.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w38_2) - BitVec.ofNat 32 (tl43.header + tl43.len) = 0) ∧ d_w30_3 = (s.1) ∧ d_w34_3 = (s.2.1) ∧ d_wa20_3 = (s.2.2.2.2.1) ∧ d_wa24_3 = (s.2.2.2.2.2.1) ∧ d_wa28_3 = (x2_w3c_2) + BitVec.ofNat 32 tl43.header ∧ d_wa2c_3 = BitVec.ofNat 32 tl43.len ∧ d_wa30_3 = (s.2.2.2.2.2.2.2.2.1) ∧ d_wa34_3 = (s.2.2.2.2.2.2.2.2.2.1) ∧ d_wa38_3 = (s.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa3c_3 = (s.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa40_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa44_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.2)) ∨ ((¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x71)) 3)) ∧ (¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x7A)) 3)) ∧ (¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x77)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xA0)) 10 = memBytes M0 op19_1 ol19_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xAA)) 10 = memBytes M0 op19_1 ol19_1.toNat)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xB4)) 10 = memBytes M0 op19_1 ol19_1.toNat) ∧ ∃ tl51, derTlv (memBytes M0 (x2_w3c_2) (x2_w38_2).toNat) = .ok tl51 ∧ (BitVec.ofNat 8 tl51.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w38_2) - BitVec.ofNat 32 (tl51.header + tl51.len) = 0) ∧ d_w30_3 = (s.1) ∧ d_w34_3 = (s.2.1) ∧ d_wa20_3 = (s.2.2.2.2.1) ∧ d_wa24_3 = (s.2.2.2.2.2.1) ∧ d_wa28_3 = (s.2.2.2.2.2.2.1) ∧ d_wa2c_3 = (s.2.2.2.2.2.2.2.1) ∧ d_wa30_3 = (x2_w3c_2) + BitVec.ofNat 32 tl51.header ∧ d_wa34_3 = BitVec.ofNat 32 tl51.len ∧ d_wa38_3 = (s.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa3c_3 = (s.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa40_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa44_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.2)) ∨ ((¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x71)) 3)) ∧ (¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x7A)) 3)) ∧ (¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x77)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xA0)) 10 = memBytes M0 op19_1 ol19_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xAA)) 10 = memBytes M0 op19_1 ol19_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xB4)) 10 = memBytes M0 op19_1 ol19_1.toNat)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xBE)) 10 = memBytes M0 op19_1 ol19_1.toNat) ∧ ∃ tl59, derTlv (memBytes M0 (x2_w3c_2) (x2_w38_2).toNat) = .ok tl59 ∧ (BitVec.ofNat 8 tl59.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w38_2) - BitVec.ofNat 32 (tl59.header + tl59.len) = 0) ∧ d_w30_3 = (s.1) ∧ d_w34_3 = (s.2.1) ∧ d_wa20_3 = (s.2.2.2.2.1) ∧ d_wa24_3 = (s.2.2.2.2.2.1) ∧ d_wa28_3 = (s.2.2.2.2.2.2.1) ∧ d_wa2c_3 = (s.2.2.2.2.2.2.2.1) ∧ d_wa30_3 = (s.2.2.2.2.2.2.2.2.1) ∧ d_wa34_3 = (s.2.2.2.2.2.2.2.2.2.1) ∧ d_wa38_3 = (x2_w3c_2) + BitVec.ofNat 32 tl59.header ∧ d_wa3c_3 = BitVec.ofNat 32 tl59.len ∧ d_wa40_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa44_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.2)) ∨ ((¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x71)) 3)) ∧ (¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x7A)) 3)) ∧ (¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x77)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xA0)) 10 = memBytes M0 op19_1 ol19_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xAA)) 10 = memBytes M0 op19_1 ol19_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xB4)) 10 = memBytes M0 op19_1 ol19_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xBE)) 10 = memBytes M0 op19_1 ol19_1.toNat)) ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xC8)) 10 = memBytes M0 op19_1 ol19_1.toNat) ∧ ∃ tl67, derTlv (memBytes M0 (x2_w3c_2) (x2_w38_2).toNat) = .ok tl67 ∧ (BitVec.ofNat 8 tl67.tag = BitVec.ofNat 8 0xC) ∧ ((x2_w38_2) - BitVec.ofNat 32 (tl67.header + tl67.len) = 0) ∧ d_w30_3 = (s.1) ∧ d_w34_3 = (s.2.1) ∧ d_wa20_3 = (s.2.2.2.2.1) ∧ d_wa24_3 = (s.2.2.2.2.2.1) ∧ d_wa28_3 = (s.2.2.2.2.2.2.1) ∧ d_wa2c_3 = (s.2.2.2.2.2.2.2.1) ∧ d_wa30_3 = (s.2.2.2.2.2.2.2.2.1) ∧ d_wa34_3 = (s.2.2.2.2.2.2.2.2.2.1) ∧ d_wa38_3 = (s.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa3c_3 = (s.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa40_3 = (x2_w3c_2) + BitVec.ofNat 32 tl67.header ∧ d_wa44_3 = BitVec.ofNat 32 tl67.len) ∨ ((¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x71)) 3)) ∧ (¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x7A)) 3)) ∧ (¬ (memBytes M0 op19_1 ol19_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x77)) 3)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xA0)) 10 = memBytes M0 op19_1 ol19_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xAA)) 10 = memBytes M0 op19_1 ol19_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xB4)) 10 = memBytes M0 op19_1 ol19_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xBE)) 10 = memBytes M0 op19_1 ol19_1.toNat)) ∧ (¬ (memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0xC8)) 10 = memBytes M0 op19_1 ol19_1.toNat)) ∧ d_w30_3 = (s.1) ∧ d_w34_3 = (s.2.1) ∧ d_wa20_3 = (s.2.2.2.2.1) ∧ d_wa24_3 = (s.2.2.2.2.2.1) ∧ d_wa28_3 = (s.2.2.2.2.2.2.1) ∧ d_wa2c_3 = (s.2.2.2.2.2.2.2.1) ∧ d_wa30_3 = (s.2.2.2.2.2.2.2.2.1) ∧ d_wa34_3 = (s.2.2.2.2.2.2.2.2.2.1) ∧ d_wa38_3 = (s.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa3c_3 = (s.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa40_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.1) ∧ d_wa44_3 = (s.2.2.2.2.2.2.2.2.2.2.2.2.2))) ∧ (d_wa20_3 = 0 ∨ SvIn B d_wa20_3 d_wa24_3.toNat) ∧ (d_wa28_3 = 0 ∨ SvIn B d_wa28_3 d_wa2c_3.toNat) ∧ (d_wa30_3 = 0 ∨ SvIn B d_wa30_3 d_wa34_3.toNat) ∧ (d_wa38_3 = 0 ∨ SvIn B d_wa38_3 d_wa3c_3.toNat) ∧ (d_wa40_3 = 0 ∨ SvIn B d_wa40_3 d_wa44_3.toNat) ∧ s' = (d_w30_3, d_w34_3, ((s.2.2.1)) - BitVec.ofNat 32 (tl8_1.header + tl8_1.len), ((s.2.2.2.1)) + BitVec.ofNat 32 (tl8_1.header + tl8_1.len), d_wa20_3, d_wa24_3, d_wa28_3, d_wa2c_3, d_wa30_3, d_wa34_3, d_wa38_3, d_wa3c_3, d_wa40_3, d_wa44_3)

set_option linter.unusedVariables false in
/-- How `sv_l7` ends once `rem` is 0. -/
def sv_extloopOk (B out bp x9 x21 x25 x26 p0 L w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (f30' : Word) (f34' : Word) (rem' : Word) (cur' : Word) (sl0' : Word) (sl1' : Word) (sl2' : Word) (sl3' : Word) (sl4' : Word) (sl5' : Word) (sl6' : Word) (sl7' : Word) (sl8' : Word) (sl9' : Word) (nk : Machine) : Prop :=
  rem' = 0 ∧ (sl0' = 0 ∨ SvIn B sl0' sl1'.toNat) ∧ (sl2' = 0 ∨ SvIn B sl2' sl3'.toNat) ∧ (sl4' = 0 ∨ SvIn B sl4' sl5'.toNat) ∧ (sl6' = 0 ∨ SvIn B sl6' sl7'.toNat) ∧ (sl8' = 0 ∨ SvIn B sl8' sl9'.toNat) ∧ (((sl0' ≠ 0) ∧
    (sl2' ≠ 0) ∧
    (sl4' ≠ 0) ∧
    (sl6' ≠ 0) ∧
    ((if BitVec.ult 0 (sl8') then (1 : Word) else 0) &&& ((f30') &&& (f34')) ≠ 0) ∧
    (memBytes M0 w60 (w64.toNat) = memBytes M0 w70 (w74.toNat)) ∧
    ∃ sr43 ss43, ecdsaSigOf 48 M0 (w7c) ((w68.toNat)) = .ok (sr43, ss43) ∧
    ∃ n', Steps nk n' ∧
        St n'.mem SV n' 0xA44 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg nk (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg nk (4 : Fin 32) ∧
        reg n' (9 : Fin 32) = x9 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = (BitVec.ofNat 8 ((sr43).getD 0 0)).zeroExtend 32 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (w64.toNat) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 (w68.toNat) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (w74.toNat) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem' ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 ((sr43).getD j 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 ((ss43).getD j 0)) ∧
        SvKeepL B nk.mem n'.mem [(0x48, 0x4), (0x44, 0x4), (0x40, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x34, 0x4), (0x30, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4), (0xA20, 0x61)]))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- The extensions loop: `k` more extensions, then the end. -/
theorem sv_extloop {B out bp x9 x21 x25 x26 p0 L w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 : Word} {v : Nat → Word}
    (F : Fr B 0x3830) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8) :
    ∀ (N : Nat) {f30 : Word} {f34 : Word} {rem : Word} {cur : Word} {sl0 : Word} {sl1 : Word} {sl2 : Word} {sl3 : Word} {sl4 : Word} {sl5 : Word} {sl6 : Word} {sl7 : Word} {sl8 : Word} {sl9 : Word} {n0 : Machine},
    (hN : rem.toNat ≤ N) →
    (E0 : SvCode n0.mem) →
    (V0 : SvSaves B n0.mem v) →
    (s0 : St n0.mem SV n0 0x4EA (reg n0)) →
    (fM : ∀ x, SvR B x → n0.mem x = M0 x) →
    (g0_2 : reg n0 sp = B + 0x21A0) →
    (g0_9 : reg n0 (9 : Fin 32) = x9) →
    (g0_18 : reg n0 (18 : Fin 32) = out) →
    (g0_19 : reg n0 (19 : Fin 32) = bp) →
    (g0_21 : reg n0 (21 : Fin 32) = x21) →
    (g0_25 : reg n0 (25 : Fin 32) = x25) →
    (g0_26 : reg n0 (26 : Fin 32) = x26) →
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20) →
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30) →
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34) →
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem) →
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c) →
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50) →
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
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80) →
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84) →
    (w0_88 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0) →
    (w0_8c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L) →
    (w0_90 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur) →
    (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem) →
    (w0_a20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0) →
    (w0_a24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1) →
    (w0_a28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2) →
    (w0_a2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3) →
    (w0_a30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4) →
    (w0_a34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5) →
    (w0_a38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6) →
    (w0_a3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7) →
    (w0_a40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8) →
    (w0_a44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9) →
    (xl_in : SvIn B (cur) (rem).toNat) →
    (SD0 : SvData M0) →
    (sl0_or0 : sl0 = 0 ∨ SvIn B sl0 sl1.toNat) →
    (sl2_or0 : sl2 = 0 ∨ SvIn B sl2 sl3.toNat) →
    (sl4_or0 : sl4 = 0 ∨ SvIn B sl4 sl5.toNat) →
    (sl6_or0 : sl6 = 0 ∨ SvIn B sl6 sl7.toNat) →
    (sl8_or0 : sl8 = 0 ∨ SvIn B sl8 sl9.toNat) →
    (el_in : SvIn B p0 L.toNat) →
    (or_in : SvIn B w60 (w64.toNat)) →
    (ar_in : SvIn B w70 (w74.toNat)) →
    (sg_in : SvIn B w7c (w68.toNat)) →
    SvErrRet B out v n0 ∨ ∃ k f30' f34' rem' cur' sl0' sl1' sl2' sl3' sl4' sl5' sl6' sl7' sl8' sl9', svChain (sv_extStep B out bp x9 x21 x25 x26 p0 L w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 v M0) k (f30, f34, rem, cur, sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9) (f30', f34', rem', cur', sl0', sl1', sl2', sl3', sl4', sl5', sl6', sl7', sl8', sl9') ∧
      ∃ nk, Steps n0 nk ∧ reg nk (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg nk (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
      SvKeepL B n0.mem nk.mem [(0x1020, 0x10), (0x90, 0x8), (0x44, 0x4), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x1020, 0x8), (0x328, 0x8), (0x48, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0x34, 0x4), (0x40, 0x4), (0x1380, 0x4), (0x1384, 0x4), (0x1388, 0x4), (0x138C, 0x4), (0x1388, 0x8), (0x1485, 0xB), (0x1484, 0x1), (0x30, 0x4), (0xA20, 0x4), (0xA24, 0x4), (0xA28, 0x4), (0xA2C, 0x4), (0xA30, 0x4), (0xA34, 0x4), (0xA38, 0x4), (0xA3C, 0x4), (0xA40, 0x4), (0xA44, 0x4)] ∧ sv_extloopOk B out bp x9 x21 x25 x26 p0 L w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 v M0 f30' f34' rem' cur' sl0' sl1' sl2' sl3' sl4' sl5' sl6' sl7' sl8' sl9' nk := by
  intro N
  induction N with
  | zero =>
    intro f30 f34 rem cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 n0 hN E0 V0 s0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_25 g0_26 g0_27 w0_30 w0_34 w0_40 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_a40 w0_a44 xl_in SD0 sl0_or0 sl2_or0 sl4_or0 sl6_or0 sl8_or0 el_in or_in ar_in sg_in
    have h0 : rem = 0 := svRem_zero hN
    rcases sv_l7 (B := B) (out := out) (bp := bp) (x9 := x9) (x21 := x21) (x25 := x25) (x26 := x26) (f30 := f30) (f34 := f34) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (orp := w60) (arp := w70) (sgp := w7c) (orl := w64.toNat) (arl := w74.toNat) (sgl := w68.toNat) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_25 g0_26 g0_27 w0_30 w0_34 w0_40 w0_4c w0_50 w0_54 w0_58 w0_5c w0_6c w0_78 w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_a40 w0_a44 w0_60 (w0_64.trans (ofNat_toNat_self _).symm) w0_70 (w0_74.trans (ofNat_toNat_self _).symm) w0_7c (w0_68.trans (ofNat_toNat_self _).symm) h0 or_in ar_in sg_in with ⟨-, e⟩ | okx
    · exact .inl e
    · exact .inr ⟨0, f30, f34, rem, cur, sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, svChain.nil, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), h0, sl0_or0, sl2_or0, sl4_or0, sl6_or0, sl8_or0, okx⟩
  | succ N ih =>
    intro f30 f34 rem cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 n0 hN E0 V0 s0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_25 g0_26 g0_27 w0_30 w0_34 w0_40 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_a40 w0_a44 xl_in SD0 sl0_or0 sl2_or0 sl4_or0 sl6_or0 sl8_or0 el_in or_in ar_in sg_in
    by_cases h0 : rem = 0
    · rcases sv_l7 (B := B) (out := out) (bp := bp) (x9 := x9) (x21 := x21) (x25 := x25) (x26 := x26) (f30 := f30) (f34 := f34) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (orp := w60) (arp := w70) (sgp := w7c) (orl := w64.toNat) (arl := w74.toNat) (sgl := w68.toNat) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_25 g0_26 g0_27 w0_30 w0_34 w0_40 w0_4c w0_50 w0_54 w0_58 w0_5c w0_6c w0_78 w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_a40 w0_a44 w0_60 (w0_64.trans (ofNat_toNat_self _).symm) w0_70 (w0_74.trans (ofNat_toNat_self _).symm) w0_7c (w0_68.trans (ofNat_toNat_self _).symm) h0 or_in ar_in sg_in with ⟨-, e⟩ | okx
      · exact .inl e
      · exact .inr ⟨0, f30, f34, rem, cur, sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, svChain.nil, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), h0, sl0_or0, sl2_or0, sl4_or0, sl6_or0, sl8_or0, okx⟩
    rcases sv_seg_ext (B := B) (out := out) (bp := bp) (x9 := x9) (x21 := x21) (x25 := x25) (x26 := x26) (f30 := f30) (f34 := f34) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (v := v) F E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_25 g0_26 g0_27 w0_30 w0_34 w0_40 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_a40 w0_a44 xl_in ((el_in).shrink (by omega)) h0 SD0 sl0_or0 sl2_or0 sl4_or0 sl6_or0 sl8_or0 with e | ⟨x1_0, x1_1tl8_1, x1_1, x1_2op19_1, x1_2ol19_1, x1_2, x1_3to19_1, x1_3, x1_4x2_w38_2, x1_4x2_w3c_2, x1_4, x1_5, x1_6d_w30_3, x1_6d_w34_3, x1_6d_wa20_3, x1_6d_wa24_3, x1_6d_wa28_3, x1_6d_wa2c_3, x1_6d_wa30_3, x1_6d_wa34_3, x1_6d_wa38_3, x1_6d_wa3c_3, x1_6d_wa40_3, x1_6d_wa44_3, x1_6, x1_7, x1_8, x1_9, x1_10, x1_11, n1, c1, fR1, s1, E1, V1, r1_3, r1_4, r1_2, r1_9, r1_18, r1_19, r1_21, r1_25, r1_26, r1_27, w1_30, w1_34, w1_40, w1_4c, w1_50, w1_54, w1_58, w1_5c, w1_60, w1_64, w1_68, w1_6c, w1_70, w1_74, w1_78, w1_7c, w1_80, w1_84, w1_88, w1_8c, w1_90, w1_94, w1_a20, w1_a24, w1_a28, w1_a2c, w1_a30, w1_a34, w1_a38, w1_a3c, w1_a40, w1_a44, w1_48, w1_320, w1_38, w1_3c, K1_L⟩
    · exact .inl e
    have hdec := svRem_elem x1_1 hN
    rcases ih hdec E1 V1 s1 fR1 r1_2 r1_9 r1_18 r1_19 r1_21 r1_25 r1_26 r1_27 w1_30 w1_34 w1_40 w1_4c w1_50 w1_54 w1_58 w1_5c w1_60 w1_64 w1_68 w1_6c w1_70 w1_74 w1_78 w1_7c w1_80 w1_84 w1_88 w1_8c w1_90 w1_94 w1_a20 w1_a24 w1_a28 w1_a2c w1_a30 w1_a34 w1_a38 w1_a3c w1_a40 w1_a44 ((xl_in).restW x1_1) SD0 x1_7 x1_8 x1_9 x1_10 x1_11 el_in or_in ar_in sg_in with e | ⟨k, f30', f34', rem', cur', sl0', sl1', sl2', sl3', sl4', sl5', sl6', sl7', sl8', sl9', chn, nk, cs, h3, h4, hk, okk⟩
    · exact .inl (SvErrRet.pre c1 r1_3 r1_4 (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
    · exact .inr ⟨k + 1, f30', f34', rem', cur', sl0', sl1', sl2', sl3', sl4', sl5', sl6', sl7', sl8', sl9', svChain.cons ⟨h0, x1_0, x1_1tl8_1, x1_1, x1_2op19_1, x1_2ol19_1, x1_2, x1_3to19_1, x1_3, x1_4x2_w38_2, x1_4x2_w3c_2, x1_4, x1_5, x1_6d_w30_3, x1_6d_w34_3, x1_6d_wa20_3, x1_6d_wa24_3, x1_6d_wa28_3, x1_6d_wa2c_3, x1_6d_wa30_3, x1_6d_wa34_3, x1_6d_wa38_3, x1_6d_wa3c_3, x1_6d_wa40_3, x1_6d_wa44_3, x1_6, x1_7, x1_8, x1_9, x1_10, x1_11, rfl⟩ chn, nk, c1.trans cs, h3.trans r1_3, h4.trans r1_4, (K1_L.trans hk).mono (by decide), okk⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `sv_extloop` as a stage. -/
theorem sv_extloop_st {B out bp x9 x21 x25 x26 p0 L w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 : Word} {v : Nat → Word} {N : Nat} {f30 : Word} {f34 : Word} {rem : Word} {cur : Word} {sl0 : Word} {sl1 : Word} {sl2 : Word} {sl3 : Word} {sl4 : Word} {sl5 : Word} {sl6 : Word} {sl7 : Word} {sl8 : Word} {sl9 : Word} {n0 : Machine}
    (F : Fr B 0x3830) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8)
    (hN : rem.toNat ≤ N)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (s0 : St n0.mem SV n0 0x4EA (reg n0))
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_9 : reg n0 (9 : Fin 32) = x9)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = f34)
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = rem)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
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
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80)
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84)
    (w0_88 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0)
    (w0_8c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L)
    (w0_90 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur)
    (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem)
    (w0_a20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) = sl0)
    (w0_a24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA24) = sl1)
    (w0_a28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA28) = sl2)
    (w0_a2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA2C) = sl3)
    (w0_a30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA30) = sl4)
    (w0_a34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA34) = sl5)
    (w0_a38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA38) = sl6)
    (w0_a3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA3C) = sl7)
    (w0_a40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = sl8)
    (w0_a44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA44) = sl9)
    (xl_in : SvIn B (cur) (rem).toNat)
    (SD0 : SvData M0)
    (sl0_or0 : sl0 = 0 ∨ SvIn B sl0 sl1.toNat)
    (sl2_or0 : sl2 = 0 ∨ SvIn B sl2 sl3.toNat)
    (sl4_or0 : sl4 = 0 ∨ SvIn B sl4 sl5.toNat)
    (sl6_or0 : sl6 = 0 ∨ SvIn B sl6 sl7.toNat)
    (sl8_or0 : sl8 = 0 ∨ SvIn B sl8 sl9.toNat)
    (el_in : SvIn B p0 L.toNat)
    (or_in : SvIn B w60 (w64.toNat))
    (ar_in : SvIn B w70 (w74.toNat))
    (sg_in : SvIn B w7c (w68.toNat))
    :
    SvErrRet B out v n0 ∨
    (∃ k f30' f34' rem' cur' sl0' sl1' sl2' sl3' sl4' sl5' sl6' sl7' sl8' sl9', svChain (sv_extStep B out bp x9 x21 x25 x26 p0 L w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c w80 w84 v M0) k (f30, f34, rem, cur, sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9) (f30', f34', rem', cur', sl0', sl1', sl2', sl3', sl4', sl5', sl6', sl7', sl8', sl9') ∧
      rem' = 0 ∧ (sl0' = 0 ∨ SvIn B sl0' sl1'.toNat) ∧ (sl2' = 0 ∨ SvIn B sl2' sl3'.toNat) ∧ (sl4' = 0 ∨ SvIn B sl4' sl5'.toNat) ∧ (sl6' = 0 ∨ SvIn B sl6' sl7'.toNat) ∧ (sl8' = 0 ∨ SvIn B sl8' sl9'.toNat) ∧
      (sl0' ≠ 0) ∧ (sl2' ≠ 0) ∧ (sl4' ≠ 0) ∧ (sl6' ≠ 0) ∧ ((if BitVec.ult 0 (sl8') then (1 : Word) else 0) &&& ((f30') &&& (f34')) ≠ 0) ∧ (memBytes M0 w60 (w64.toNat) = memBytes M0 w70 (w74.toNat)) ∧ ∃ sr43 ss43, ecdsaSigOf 48 M0 (w7c) ((w68.toNat)) = .ok (sr43, ss43) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0xA44 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (9 : Fin 32) = x9 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = (BitVec.ofNat 8 ((sr43).getD 0 0)).zeroExtend 32 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = sl9' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = sl7' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = sl5' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = sl3' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = sl1' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sl8' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = sl6' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = sl4' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = sl2' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = sl0' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 (w64.toNat) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = BitVec.ofNat 32 (w68.toNat) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 (w74.toNat) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = L ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = cur' ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = rem' ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA21 + j)) = BitVec.ofNat 8 ((sr43).getD j 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA51 + j)) = BitVec.ofNat 8 ((ss43).getD j 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x1020, 0x10), (0x90, 0x8), (0x44, 0x4), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x1020, 0x8), (0x328, 0x8), (0x48, 0x4), (0x3C, 0x4), (0x38, 0x4), (0x1480, 0x4), (0x1484, 0x4), (0x1488, 0x4), (0x148C, 0x4), (0x1020, 0x11), (0x1488, 0x8), (0x34, 0x4), (0x40, 0x4), (0x1380, 0x4), (0x1384, 0x4), (0x1388, 0x4), (0x138C, 0x4), (0x1388, 0x8), (0x1485, 0xB), (0x1484, 0x1), (0x30, 0x4), (0xA20, 0x4), (0xA24, 0x4), (0xA28, 0x4), (0xA2C, 0x4), (0xA30, 0x4), (0xA34, 0x4), (0xA38, 0x4), (0xA3C, 0x4), (0xA40, 0x4), (0xA44, 0x4), (0x2C, 0x4), (0x28, 0x4), (0x24, 0x4), (0xA20, 0x61)]) := by
  rcases sv_extloop (B := B) (out := out) (bp := bp) (x9 := x9) (x21 := x21) (x25 := x25) (x26 := x26) (p0 := p0) (L := L) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (w80 := w80) (w84 := w84) (v := v) F hret hO M0 N hN E0 V0 s0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_25 g0_26 g0_27 w0_30 w0_34 w0_40 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_a20 w0_a24 w0_a28 w0_a2c w0_a30 w0_a34 w0_a38 w0_a3c w0_a40 w0_a44 xl_in SD0 sl0_or0 sl2_or0 sl4_or0 sl6_or0 sl8_or0 el_in or_in ar_in sg_in with e | ⟨k, f30', f34', rem', cur', sl0', sl1', sl2', sl3', sl4', sl5', sl6', sl7', sl8', sl9', chn, nk, cs, hr3, hr4, hkl, okh⟩
  · exact .inl e
  obtain ⟨hz, iv0, iv1, iv2, iv3, iv4, h0, h1, h2, h3, h4, h5, sr43, ss43, h6, n1, cn, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r9, f_r18, f_r19, f_r20, f_r21, f_r25, f_r26, f_r27, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w3c, f_w40, f_w44, f_w48, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_qa21, f_qa51, f_KL⟩ := okh
  exact .inr ⟨k, f30', f34', rem', cur', sl0', sl1', sl2', sl3', sl4', sl5', sl6', sl7', sl8', sl9', chn, hz, iv0, iv1, iv2, iv3, iv4, h0, h1, h2, h3, h4, h5, sr43, ss43, h6, n1, cs.trans cn, f_ST, f_E, f_V, f_FR, f_r2, f_r3.trans hr3, f_r4.trans hr4, f_r9, f_r18, f_r19, f_r20, f_r21, f_r25, f_r26, f_r27, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w3c, f_w40, f_w44, f_w48, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_qa21, f_qa51, (hkl.trans f_KL).mono (by decide)⟩

end C3.RV32.Sv
