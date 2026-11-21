import C3BootProofs.Proofs.SvSeg
import C3BootProofs.Proofs.SvSegAttr
import C3BootProofs.Proofs.SvTsax

/-!
# `sigstore::verify`: the signed attributes loop

Written by `scripts/gen-sv-attrloop.py` from `sv_seg_attr` and `sv_tsax`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

/-- One more signed attribute, from state `s` to `s'` (`dg`, the content-type flag, and the attributes left): there are some, and the next one is well formed. -/
def sv_attrStep (B out bp x21 x26 p0 L0 sip sil w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 : Word) (v : Nat → Word) (M0 : Word → BitVec 8) : Word × Word × Word × Word → Word × Word × Word × Word → Prop :=
  fun s s' => s.2.2.2 ≠ 0 ∧ (((s.2.2.2)).toNat ≤ (L0).toNat) ∧ ∃ tl6_2, derElement 0x30 (memBytes M0 ((s.2.2.1)) ((s.2.2.2)).toNat) = .ok tl6_2 ∧ ∃ op15_2 ol15_2, derContent (((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) (derOid (memBytes M0 (((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) (BitVec.ofNat 32 tl6_2.len).toNat)) = .ok (op15_2, ol15_2) ∧ ∃ to15_2, derOid (memBytes M0 (((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) (BitVec.ofNat 32 tl6_2.len).toNat) = .ok to15_2 ∧ ∃ tl20_2, derElement 0x31 (memBytes M0 ((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) ((BitVec.ofNat 32 tl6_2.len) - BitVec.ofNat 32 (to15_2.header + to15_2.len)).toNat) = .ok tl20_2 ∧ (((BitVec.ofNat 32 tl6_2.len) - BitVec.ofNat 32 (to15_2.header + to15_2.len)) - BitVec.ofNat 32 (tl20_2.header + tl20_2.len) = 0) ∧ listsOidOf M0 p0 ((L0) - ((s.2.2.2))).toNat (memBytes M0 op15_2 ol15_2.toNat) = .ok false ∧ ∃ tsav_r24_3 : Word, ∃ tsav_w78_3 : Word, ∃ tsav_w1388_3 : Word, ∃ tsav_w138c_3 : Word, ((∃ op5 ol5, derContent ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) (derOid (memBytes M0 ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) ((BitVec.ofNat 32 tl20_2.len)).toNat)) = .ok (op5, ol5) ∧ ∃ to5, derOid (memBytes M0 ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) ((BitVec.ofNat 32 tl20_2.len)).toNat) = .ok to5 ∧ (memBytes M0 op5 ol5.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC4862) 11) ∧ (((BitVec.ofNat 32 tl20_2.len)) - BitVec.ofNat 32 (to5.header + to5.len) = 0) ∧ tsav_r24_3 = (s.1) ∧ tsav_w78_3 = BitVec.ofNat 32 0x1 ∧ tsav_w1388_3 = ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) + BitVec.ofNat 32 (to5.header + to5.len) ∧ tsav_w138c_3 = ((BitVec.ofNat 32 tl20_2.len)) - BitVec.ofNat 32 (to5.header + to5.len)) ∨ (∃ vp8 vl8, derContent ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) (derElement 4 (memBytes M0 ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) ((BitVec.ofNat 32 tl20_2.len)).toNat)) = .ok (vp8, vl8) ∧ ∃ te8, derElement 4 (memBytes M0 ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) ((BitVec.ofNat 32 tl20_2.len)).toNat) = .ok te8 ∧ (vl8 = 32) ∧ (((BitVec.ofNat 32 tl20_2.len)) - BitVec.ofNat 32 (te8.header + te8.len) = 0) ∧ tsav_r24_3 = vp8 ∧ tsav_w78_3 = (s.2.1) ∧ tsav_w1388_3 = ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) + BitVec.ofNat 32 (te8.header + te8.len) ∧ tsav_w138c_3 = ((BitVec.ofNat 32 tl20_2.len)) - BitVec.ofNat 32 (te8.header + te8.len)) ∨ (tsav_r24_3 = (s.1) ∧ tsav_w78_3 = (s.2.1) ∧ tsav_w1388_3 = (((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header) ∧ tsav_w138c_3 = (BitVec.ofNat 32 tl20_2.len))) ∧ SvIn B tsav_w1388_3 tsav_w138c_3.toNat ∧ s' = (tsav_r24_3, tsav_w78_3, ((s.2.2.1)) + BitVec.ofNat 32 (tl6_2.header + tl6_2.len), ((s.2.2.2)) - BitVec.ofNat 32 (tl6_2.header + tl6_2.len))

/-- How `sv_tsax` ends once no attributes are left. -/
def sv_attrloopOk (B out bp x21 x26 p0 L0 sip sil w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (dg' flag' cp' rem' : Word) (nk : Machine) : Prop :=
  rem' = 0 ∧ ((((dg') ≠ 0 ∧ (flag') = 1) ∧
    ∃ op8 ol8, derAlgOf M0 (sip) ((sil).toNat) = .ok ((op8, ol8), none) ∧
    ∃ te8, derElement 0x30 (memBytes M0 (sip) (sil).toNat) = .ok te8 ∧
    (memBytes M0 op8 ol8 = memBytes M0 (BitVec.ofNat 32 0x3FCC4818) 8) ∧
    ∃ vp19 vl19, derContent ((sip) + BitVec.ofNat 32 (te8.header + te8.len)) (derElement 4 (memBytes M0 ((sip) + BitVec.ofNat 32 (te8.header + te8.len)) ((sil) - BitVec.ofNat 32 (te8.header + te8.len)).toNat)) = .ok (vp19, vl19) ∧
    ∃ te19, derElement 4 (memBytes M0 ((sip) + BitVec.ofNat 32 (te8.header + te8.len)) ((sil) - BitVec.ofNat 32 (te8.header + te8.len)).toNat) = .ok te19 ∧
    ∃ sr24 ss24, ecdsaSigOf 48 M0 (vp19) ((vl19).toNat) = .ok (sr24, ss24) ∧
    ∃ n', Steps nk n' ∧
        St n'.mem SV n' 0x2704 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg nk (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg nk (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 0x18 ∧
        reg n' (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (24 : Fin 32) = (dg') ∧
        reg n' (25 : Fin 32) = (BitVec.ofNat 8 ((sr24).getD 0 0)).zeroExtend 32 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = (flag') ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = ((sip) + BitVec.ofNat 32 (te8.header + te8.len)) + BitVec.ofNat 32 (te19.header + te19.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20C) = ((sil) - BitVec.ofNat 32 (te8.header + te8.len)) - BitVec.ofNat 32 (te19.header + te19.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = L0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = (cp') ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (rem') ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) = vp19 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1384) = vl19 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 ((sr24).getD 0 0) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 ((sr24).getD j 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x451 + j)) = BitVec.ofNat 8 ((ss24).getD j 0)) ∧
        SvKeepL B nk.mem n'.mem [(0x420, 0x1C), (0x208, 0x8), (0x1380, 0x8), (0x208, 0x8), (0x420, 0x61)]))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- The signed attributes loop: `k` more attributes, then the end. -/
theorem sv_attrloop {B out bp x21 x26 p0 L0 sip sil w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 : Word} {v : Nat → Word}
    (F : Fr B 0x3830) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8) :
    ∀ (N : Nat) {dg flag cp rem : Word} {n0 : Machine},
    (hN : rem.toNat ≤ N) → (hflag : flag = 0 ∨ flag = 1) →
    (E0 : SvCode n0.mem) →
    (V0 : SvSaves B n0.mem v) →
    (s0 : St n0.mem SV n0 0x267A (reg n0)) →
    (fM : ∀ x, SvR B x → n0.mem x = M0 x) →
    (g0_2 : reg n0 sp = B + 0x21A0) →
    (g0_9 : reg n0 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320) →
    (g0_18 : reg n0 (18 : Fin 32) = out) →
    (g0_19 : reg n0 (19 : Fin 32) = bp) →
    (g0_21 : reg n0 (21 : Fin 32) = x21) →
    (g0_24 : reg n0 (24 : Fin 32) = dg) →
    (g0_26 : reg n0 (26 : Fin 32) = x26) →
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20) →
    (w0_24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24) →
    (w0_28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28) →
    (w0_2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c) →
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30) →
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34) →
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38) →
    (w0_3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c) →
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40) →
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44) →
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48) →
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
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = flag) →
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c) →
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80) →
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84) →
    (w0_88 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88) →
    (w0_8c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c) →
    (w0_90 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90) →
    (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94) →
    (w0_98 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98) →
    (w0_9c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c) →
    (w0_a0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0) →
    (w0_a4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4) →
    (w0_a8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8) →
    (w0_ac : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac) →
    (w0_b0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0) →
    (w0_b4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4) →
    (w0_b8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8) →
    (w0_bc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc) →
    (w0_c0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0) →
    (w0_c4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4) →
    (w0_c8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8) →
    (w0_cc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc) →
    (w0_d0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0) →
    (w0_d4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4) →
    (w0_d8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8) →
    (w0_dc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc) →
    (w0_e0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0) →
    (w0_e4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4) →
    (w0_e8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8) →
    (w0_ec : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec) →
    (w0_f0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0) →
    (w0_f4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4) →
    (w0_f8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8) →
    (w0_fc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc) →
    (w0_100 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100) →
    (w0_104 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104) →
    (w0_108 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108) →
    (w0_10c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c) →
    (w0_110 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110) →
    (w0_114 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114) →
    (w0_118 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118) →
    (w0_11c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c) →
    (w0_120 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120) →
    (w0_124 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124) →
    (w0_128 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128) →
    (w0_12c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c) →
    (w0_130 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130) →
    (w0_208 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = sip) →
    (w0_20c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x20C) = sil) →
    (w0_1320 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = p0) →
    (w0_1324 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = L0) →
    (w0_1328 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = cp) →
    (w0_132c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = rem) →
    (cr_in : SvIn B (cp) (rem).toNat) →
    (p0_in : SvIn B (p0) (L0).toNat) →
    (si_in : SvIn B (sip) (sil).toNat) →
    SvErrRet B out v n0 ∨ ∃ k dg' flag' cp' rem', svChain (sv_attrStep B out bp x21 x26 p0 L0 sip sil w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 v M0) k (dg, flag, cp, rem) (dg', flag', cp', rem') ∧
      ∃ nk, Steps n0 nk ∧ reg nk (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg nk (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
      SvKeepL B n0.mem nk.mem [(0x74, 0x4), (0x420, 0x10), (0x1328, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x420, 0x8), (0x328, 0x8), (0x420, 0x10), (0x328, 0x8), (0x1385, 0xB), (0x1380, 0x4), (0x1384, 0x1), (0x1388, 0x8), (0x78, 0x4)] ∧ sv_attrloopOk B out bp x21 x26 p0 L0 sip sil w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 v M0 dg' flag' cp' rem' nk := by
  intro N
  induction N with
  | zero =>
    intro dg flag cp rem n0 hN hflag E0 V0 s0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_24 g0_26 g0_27 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_208 w0_20c w0_1320 w0_1324 w0_1328 w0_132c cr_in p0_in si_in
    have h0 : rem = 0 := svRem_zero hN
    rcases sv_tsax (B := B) (out := out) (bp := bp) (x21 := x21) (x26 := x26) (dg := dg) (p0 := p0) (L0 := L0) (cp := cp) (rem := rem) (sip := sip) (sil := sil) (flag := flag) (w24 := w24) (w28 := w28) (w2c := w2c) (w30 := w30) (w34 := w34) (w38 := w38) (w3c := w3c) (w40 := w40) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w7c := w7c) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_24 g0_26 g0_27 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_208 w0_20c w0_1320 w0_1324 w0_1328 w0_132c cr_in p0_in si_in h0 hflag with ⟨-, e⟩ | okx
    · exact .inl e
    · exact .inr ⟨0, dg, flag, cp, rem, svChain.nil, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), h0, okx⟩
  | succ N ih =>
    intro dg flag cp rem n0 hN hflag E0 V0 s0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_24 g0_26 g0_27 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_208 w0_20c w0_1320 w0_1324 w0_1328 w0_132c cr_in p0_in si_in
    by_cases h0 : rem = 0
    · rcases sv_tsax (B := B) (out := out) (bp := bp) (x21 := x21) (x26 := x26) (dg := dg) (p0 := p0) (L0 := L0) (cp := cp) (rem := rem) (sip := sip) (sil := sil) (flag := flag) (w24 := w24) (w28 := w28) (w2c := w2c) (w30 := w30) (w34 := w34) (w38 := w38) (w3c := w3c) (w40 := w40) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w7c := w7c) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (v := v) (n0 := n0) F E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_24 g0_26 g0_27 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_208 w0_20c w0_1320 w0_1324 w0_1328 w0_132c cr_in p0_in si_in h0 hflag with ⟨-, e⟩ | okx
      · exact .inl e
      · exact .inr ⟨0, dg, flag, cp, rem, svChain.nil, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), h0, okx⟩
    rcases sv_seg_attr (B := B) (out := out) (bp := bp) (x21 := x21) (x26 := x26) (dg := dg) (p0 := p0) (L0 := L0) (cp := cp) (rem := rem) (sip := sip) (sil := sil) (flag := flag) (w24 := w24) (w28 := w28) (w2c := w2c) (w30 := w30) (w34 := w34) (w38 := w38) (w3c := w3c) (w40 := w40) (w44 := w44) (w48 := w48) (w4c := w4c) (w50 := w50) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w7c := w7c) (w80 := w80) (w84 := w84) (w88 := w88) (w8c := w8c) (w90 := w90) (w94 := w94) (w98 := w98) (w9c := w9c) (wa0 := wa0) (wa4 := wa4) (wa8 := wa8) (wac := wac) (wb0 := wb0) (wb4 := wb4) (wb8 := wb8) (wbc := wbc) (wc0 := wc0) (wc4 := wc4) (wc8 := wc8) (wcc := wcc) (wd0 := wd0) (wd4 := wd4) (wd8 := wd8) (wdc := wdc) (we0 := we0) (we4 := we4) (we8 := we8) (wec := wec) (wf0 := wf0) (wf4 := wf4) (wf8 := wf8) (wfc := wfc) (w100 := w100) (w104 := w104) (w108 := w108) (w10c := w10c) (w110 := w110) (w114 := w114) (w118 := w118) (w11c := w11c) (w120 := w120) (w124 := w124) (w128 := w128) (w12c := w12c) (w130 := w130) (v := v) F E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_24 g0_26 g0_27 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_208 w0_20c w0_1320 w0_1324 w0_1328 w0_132c cr_in p0_in si_in h0 with e | ⟨x1_0, x1_1tl6_2, x1_1, x1_2op15_2, x1_2ol15_2, x1_2, x1_3to15_2, x1_3, x1_4tl20_2, x1_4, x1_5, x1_6, x1_7tsav_r24_3, x1_7tsav_w78_3, x1_7tsav_w1388_3, x1_7tsav_w138c_3, x1_7, x1_8, n1, c1, fR1, s1, E1, V1, r1_3, r1_4, r1_2, r1_9, r1_18, r1_19, r1_20, r1_21, r1_24, r1_25, r1_26, r1_27, w1_24, w1_28, w1_2c, w1_30, w1_34, w1_38, w1_3c, w1_40, w1_44, w1_48, w1_4c, w1_50, w1_54, w1_58, w1_5c, w1_60, w1_64, w1_68, w1_6c, w1_70, w1_74, w1_78, w1_7c, w1_80, w1_84, w1_88, w1_8c, w1_90, w1_94, w1_98, w1_9c, w1_a0, w1_a4, w1_a8, w1_ac, w1_b0, w1_b4, w1_b8, w1_bc, w1_c0, w1_c4, w1_c8, w1_cc, w1_d0, w1_d4, w1_d8, w1_dc, w1_e0, w1_e4, w1_e8, w1_ec, w1_f0, w1_f4, w1_f8, w1_fc, w1_100, w1_104, w1_108, w1_10c, w1_110, w1_114, w1_118, w1_11c, w1_120, w1_124, w1_128, w1_12c, w1_130, w1_1320, w1_1324, w1_1328, w1_132c, w1_1388, w1_138c, w1_208, w1_20c, K1_L⟩
    · exact .inl e
    have hdec := svRem_le (a := x1_1tl6_2.header + x1_1tl6_2.len) (N := N) (by have := derElement_header x1_1; omega)
      (by have := derElement_bound x1_1; rw [memBytes_length] at this; exact this) hN
    have hflag' : x1_7tsav_w78_3 = 0 ∨ x1_7tsav_w78_3 = 1 := by
      rcases x1_7 with ⟨op5', ol5', h0', to5', h1', h2', h3', e0, e1, e2, e3⟩ | ⟨vp8', vl8', h0', te8', h1', h2', h3', e0, e1, e2, e3⟩ | ⟨e0, e1, e2, e3⟩
      · exact .inr e1
      · rw [e1]; exact hflag
      · rw [e1]; exact hflag
    rcases ih hdec hflag' E1 V1 s1 fR1 r1_2 r1_9 r1_18 r1_19 r1_21 r1_24 r1_26 r1_27 w1_24 w1_28 w1_2c w1_30 w1_34 w1_38 w1_3c w1_40 w1_44 w1_48 w1_4c w1_50 w1_54 w1_58 w1_5c w1_60 w1_64 w1_68 w1_6c w1_70 w1_78 w1_7c w1_80 w1_84 w1_88 w1_8c w1_90 w1_94 w1_98 w1_9c w1_a0 w1_a4 w1_a8 w1_ac w1_b0 w1_b4 w1_b8 w1_bc w1_c0 w1_c4 w1_c8 w1_cc w1_d0 w1_d4 w1_d8 w1_dc w1_e0 w1_e4 w1_e8 w1_ec w1_f0 w1_f4 w1_f8 w1_fc w1_100 w1_104 w1_108 w1_10c w1_110 w1_114 w1_118 w1_11c w1_120 w1_124 w1_128 w1_12c w1_130 w1_208 w1_20c w1_1320 w1_1324 w1_1328 w1_132c ((cr_in).restW x1_1) p0_in si_in with e | ⟨k, dg', flag', cp', rem', chn, nk, cs, h3, h4, hk, okk⟩
    · exact .inl (SvErrRet.pre c1 r1_3 r1_4 (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
    · exact .inr ⟨k + 1, dg', flag', cp', rem', svChain.cons ⟨h0, x1_0, x1_1tl6_2, x1_1, x1_2op15_2, x1_2ol15_2, x1_2, x1_3to15_2, x1_3, x1_4tl20_2, x1_4, x1_5, x1_6, x1_7tsav_r24_3, x1_7tsav_w78_3, x1_7tsav_w1388_3, x1_7tsav_w138c_3, x1_7, x1_8, rfl⟩ chn, nk, c1.trans cs, h3.trans r1_3, h4.trans r1_4, (K1_L.trans hk).mono (by decide), okk⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `sv_attrloop` as a stage. -/
theorem sv_attrloop_st {B out bp x21 x26 p0 L0 sip sil w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 : Word} {v : Nat → Word} {N : Nat} {dg flag cp rem : Word} {n0 : Machine}
    (F : Fr B 0x3830) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8)
    (hN : rem.toNat ≤ N) (hflag : flag = 0 ∨ flag = 1)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (s0 : St n0.mem SV n0 0x267A (reg n0))
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_9 : reg n0 (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_24 : reg n0 (24 : Fin 32) = dg)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_24 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24)
    (w0_28 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28)
    (w0_2c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c)
    (w0_30 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34)
    (w0_38 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38)
    (w0_3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c)
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40)
    (w0_44 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48)
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
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = flag)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c)
    (w0_80 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80)
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84)
    (w0_88 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88)
    (w0_8c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c)
    (w0_90 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90)
    (w0_94 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94)
    (w0_98 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98)
    (w0_9c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c)
    (w0_a0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0)
    (w0_a4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4)
    (w0_a8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8)
    (w0_ac : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac)
    (w0_b0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0)
    (w0_b4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4)
    (w0_b8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8)
    (w0_bc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc)
    (w0_c0 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0)
    (w0_c4 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4)
    (w0_c8 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8)
    (w0_cc : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc)
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
    (w0_130 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130)
    (w0_208 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = sip)
    (w0_20c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x20C) = sil)
    (w0_1320 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = p0)
    (w0_1324 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = L0)
    (w0_1328 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = cp)
    (w0_132c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = rem)
    (cr_in : SvIn B (cp) (rem).toNat)
    (p0_in : SvIn B (p0) (L0).toNat)
    (si_in : SvIn B (sip) (sil).toNat)
    :
    SvErrRet B out v n0 ∨
    (∃ k dg' flag' cp' rem', svChain (sv_attrStep B out bp x21 x26 p0 L0 sip sil w24 w28 w2c w30 w34 w38 w3c w40 w44 w48 w4c w50 w54 w58 w5c w60 w64 w68 w6c w70 w7c w80 w84 w88 w8c w90 w94 w98 w9c wa0 wa4 wa8 wac wb0 wb4 wb8 wbc wc0 wc4 wc8 wcc wd0 wd4 wd8 wdc we0 we4 we8 wec wf0 wf4 wf8 wfc w100 w104 w108 w10c w110 w114 w118 w11c w120 w124 w128 w12c w130 v M0) k (dg, flag, cp, rem) (dg', flag', cp', rem') ∧
      rem' = 0 ∧
      ((dg') ≠ 0 ∧ (flag') = 1) ∧ ∃ op8 ol8, derAlgOf M0 (sip) ((sil).toNat) = .ok ((op8, ol8), none) ∧ ∃ te8, derElement 0x30 (memBytes M0 (sip) (sil).toNat) = .ok te8 ∧ (memBytes M0 op8 ol8 = memBytes M0 (BitVec.ofNat 32 0x3FCC4818) 8) ∧ ∃ vp19 vl19, derContent ((sip) + BitVec.ofNat 32 (te8.header + te8.len)) (derElement 4 (memBytes M0 ((sip) + BitVec.ofNat 32 (te8.header + te8.len)) ((sil) - BitVec.ofNat 32 (te8.header + te8.len)).toNat)) = .ok (vp19, vl19) ∧ ∃ te19, derElement 4 (memBytes M0 ((sip) + BitVec.ofNat 32 (te8.header + te8.len)) ((sil) - BitVec.ofNat 32 (te8.header + te8.len)).toNat) = .ok te19 ∧ ∃ sr24 ss24, ecdsaSigOf 48 M0 (vp19) ((vl19).toNat) = .ok (sr24, ss24) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x2704 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 0x18 ∧
        reg n' (9 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0x1320 ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (24 : Fin 32) = (dg') ∧
        reg n' (25 : Fin 32) = (BitVec.ofNat 8 ((sr24).getD 0 0)).zeroExtend 32 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = w24 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x28) = w28 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = w2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = w30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = w34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = w38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = w44 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = w48 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = w4c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = (flag') ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = w80 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = w88 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = w90 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = w94 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = w98 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = w9c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = wa0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = wa4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA8) = wa8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAC) = wac ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB0) = wb0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB4) = wb4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xB8) = wb8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xBC) = wbc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC0) = wc0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC4) = wc4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = wc8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xCC) = wcc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = wd0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD4) = wd4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xD8) = wd8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xDC) = wdc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE0) = we0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE4) = we4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xE8) = we8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xEC) = wec ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF0) = wf0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF4) = wf4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xF8) = wf8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xFC) = wfc ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x100) = w100 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x104) = w104 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x108) = w108 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x10C) = w10c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x110) = w110 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x114) = w114 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x118) = w118 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x11C) = w11c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x120) = w120 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x124) = w124 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x128) = w128 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x12C) = w12c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = w130 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x208) = ((sip) + BitVec.ofNat 32 (te8.header + te8.len)) + BitVec.ofNat 32 (te19.header + te19.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20C) = ((sil) - BitVec.ofNat 32 (te8.header + te8.len)) - BitVec.ofNat 32 (te19.header + te19.len) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1320) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1324) = L0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1328) = (cp') ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x132C) = (rem') ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1380) = vp19 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1384) = vl19 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) = (0 : BitVec 8) ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x421) = BitVec.ofNat 8 ((sr24).getD 0 0) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 ((sr24).getD j 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x451 + j)) = BitVec.ofNat 8 ((ss24).getD j 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x74, 0x4), (0x420, 0x10), (0x1328, 0x8), (0x325, 0xB), (0x320, 0x4), (0x324, 0x1), (0x420, 0x8), (0x328, 0x8), (0x1385, 0xB), (0x1380, 0x4), (0x1384, 0x1), (0x1388, 0x8), (0x78, 0x4), (0x420, 0x1C), (0x208, 0x8), (0x1380, 0x8), (0x420, 0x61)]) := by
  rcases sv_attrloop F hret hO M0 N hN hflag E0 V0 s0 fM g0_2 g0_9 g0_18 g0_19 g0_21 g0_24 g0_26 g0_27 w0_24 w0_28 w0_2c w0_30 w0_34 w0_38 w0_3c w0_40 w0_44 w0_48 w0_4c w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_a8 w0_ac w0_b0 w0_b4 w0_b8 w0_bc w0_c0 w0_c4 w0_c8 w0_cc w0_d0 w0_d4 w0_d8 w0_dc w0_e0 w0_e4 w0_e8 w0_ec w0_f0 w0_f4 w0_f8 w0_fc w0_100 w0_104 w0_108 w0_10c w0_110 w0_114 w0_118 w0_11c w0_120 w0_124 w0_128 w0_12c w0_130 w0_208 w0_20c w0_1320 w0_1324 w0_1328 w0_132c cr_in p0_in si_in with e | ⟨k, dg', flag', cp', rem', chn, nk, cs, hr3, hr4, hkl, okh⟩
  · exact .inl e
  obtain ⟨hz, h0, op8, ol8, h1, te8, h2, h3, vp19, vl19, h4, te19, h5, sr24, ss24, h6, n1, cn, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r8, f_r9, f_r18, f_r19, f_r21, f_r24, f_r25, f_r26, f_r27, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w3c, f_w40, f_w44, f_w48, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_wa8, f_wac, f_wb0, f_wb4, f_wb8, f_wbc, f_wc0, f_wc4, f_wc8, f_wcc, f_wd0, f_wd4, f_wd8, f_wdc, f_we0, f_we4, f_we8, f_wec, f_wf0, f_wf4, f_wf8, f_wfc, f_w100, f_w104, f_w108, f_w10c, f_w110, f_w114, f_w118, f_w11c, f_w120, f_w124, f_w128, f_w12c, f_w130, f_w208, f_w20c, f_w1320, f_w1324, f_w1328, f_w132c, f_w1380, f_w1384, f_b420, f_b421, f_q421, f_q451, f_KL⟩ := okh
  exact .inr ⟨k, dg', flag', cp', rem', chn, hz, h0, op8, ol8, h1, te8, h2, h3, vp19, vl19, h4, te19, h5, sr24, ss24, h6, n1, cs.trans cn, f_ST, f_E, f_V, f_FR, f_r2, f_r3.trans hr3, f_r4.trans hr4, f_r8, f_r9, f_r18, f_r19, f_r21, f_r24, f_r25, f_r26, f_r27, f_w24, f_w28, f_w2c, f_w30, f_w34, f_w38, f_w3c, f_w40, f_w44, f_w48, f_w4c, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_wa8, f_wac, f_wb0, f_wb4, f_wb8, f_wbc, f_wc0, f_wc4, f_wc8, f_wcc, f_wd0, f_wd4, f_wd8, f_wdc, f_we0, f_we4, f_we8, f_wec, f_wf0, f_wf4, f_wf8, f_wfc, f_w100, f_w104, f_w108, f_w10c, f_w110, f_w114, f_w118, f_w11c, f_w120, f_w124, f_w128, f_w12c, f_w130, f_w208, f_w20c, f_w1320, f_w1324, f_w1328, f_w132c, f_w1380, f_w1384, f_b420, f_b421, f_q421, f_q451, (hkl.trans f_KL).mono (by decide)⟩

end C3.RV32.Sv
