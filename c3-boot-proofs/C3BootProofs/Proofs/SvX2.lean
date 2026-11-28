import C3BootProofs.Proofs.SvX2z
import C3BootProofs.Proofs.SvSegX2c
import C3BootProofs.Proofs.SvX2n

/-!
# `sigstore::verify`: An extension's criticality and value.

Written by `scripts/gen-sv-segs.py` from `sv_x2z`, `sv_seg_x2c`, and `sv_x2n`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxHeartbeats 16000000 in
/-- An extension's criticality and value. -/
theorem sv_x2 {B out bp tbp dg rootp ll sgp kp sgl tbl f2c f30 rem p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c rem2 ol op rest rp2 : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x42C (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = BitVec.ofNat 32 0x15)
    (g0_9 : reg n0 (9 : Fin 32) = tbp)
    (g0_10 : reg n0 a0 = rem2)
    (g0_11 : reg n0 a1 = ol)
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
    (w0_3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0)
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L)
    (w0_48 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op)
    (w0_158 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur)
    (w0_15c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest)
    (w0_408 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = rp2)
    (w0_40c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = rem2)
    (in2 : SvIn B rp2 rem2.toNat)
    (oid_in : SvIn B op ol.toNat)
    (ea_in : SvIn B p0 (L.toNat - rem.toNat))
    (hle : rem.toNat ≤ L.toNat)
    (SD0 : SvData M0) :
    SvErrRet B out v n0 ∨
    (∃ x2_w34 : Word, ∃ x2_w38 : Word, ((False) ∨ ((¬ (rem2 = 0)) ∧ (M0 rp2 = BitVec.ofNat 8 1) ∧ derBoolOf (memBytes M0 (rp2) (rem2).toNat) (derElement 1 (memBytes M0 (rp2) (rem2).toNat)) = .ok () ∧ ∃ tb7_1, derElement 1 (memBytes M0 (rp2) (rem2).toNat) = .ok tb7_1 ∧ ∃ vp14_1 vl14_1, derContent ((rp2) + BitVec.ofNat 32 (tb7_1.header + tb7_1.len)) (derElement 4 (memBytes M0 ((rp2) + BitVec.ofNat 32 (tb7_1.header + tb7_1.len)) ((rem2) - BitVec.ofNat 32 (tb7_1.header + tb7_1.len)).toNat)) = .ok (vp14_1, vl14_1) ∧ ∃ te14_1, derElement 4 (memBytes M0 ((rp2) + BitVec.ofNat 32 (tb7_1.header + tb7_1.len)) ((rem2) - BitVec.ofNat 32 (tb7_1.header + tb7_1.len)).toNat) = .ok te14_1 ∧ (((rem2) - BitVec.ofNat 32 (tb7_1.header + tb7_1.len)) - BitVec.ofNat 32 (te14_1.header + te14_1.len) = 0) ∧ listsOidOf M0 p0 (L.toNat - rem.toNat) (memBytes M0 op ol.toNat) = .ok false ∧ (memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress)) 3 = memBytes M0 op ol.toNat ∨ memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x3)) 3 = memBytes M0 op ol.toNat ∨ memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x6)) 3 = memBytes M0 op ol.toNat ∨ memBytes M0 (BitVec.ofNat 32 (img% svConstExtAddress + 0x9)) 3 = memBytes M0 op ol.toNat) ∧ x2_w34 = vl14_1 ∧ x2_w38 = vp14_1) ∨ ((¬ (rem2 = 0)) ∧ (¬ (M0 rp2 = BitVec.ofNat 8 1)) ∧ ∃ vp8 vl8, derContent (rp2) (derElement 4 (memBytes M0 (rp2) (rem2).toNat)) = .ok (vp8, vl8) ∧ ∃ te8, derElement 4 (memBytes M0 (rp2) (rem2).toNat) = .ok te8 ∧ ((rem2) - BitVec.ofNat 32 (te8.header + te8.len) = 0) ∧ listsOidOf M0 p0 (L.toNat - rem.toNat) (memBytes M0 op ol.toNat) = .ok false ∧ x2_w34 = vl8 ∧ x2_w38 = vp8)) ∧ SvIn B x2_w38 x2_w34.toNat ∧
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0x4E2 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 0x15 ∧
        reg n' (9 : Fin 32) = tbp ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = dg ∧
        reg n' (21 : Fin 32) = rootp ∧
        reg n' (22 : Fin 32) = ll ∧
        reg n' (23 : Fin 32) = sgp ∧
        reg n' (24 : Fin 32) = kp ∧
        reg n' (25 : Fin 32) = sgl ∧
        reg n' (27 : Fin 32) = tbl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = f2c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = x2_w34 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = x2_w38 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x44) = BitVec.ofNat 32 0x16 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x48) = ol ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = op ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x68) = w68 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x6C) = w6c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x70) = w70 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x80) = sl0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = sl1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x88) = sl2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = sl3 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x90) = sl4 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x94) = sl5 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x98) = sl6 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x9C) = sl7 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA0) = sl8 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA4) = sl9 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x154) = L ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x158) = cur ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = L ∧
        SvKeepL B n0.mem n'.mem [(0x408, 0x8), (0x44, 0x4), (0x420, 0x8), (0x408, 0x8), (0x38, 0x4), (0x34, 0x4), (0x44, 0x4), (0x44, 0x4), (0x50, 0x4)]) := by
  by_cases hb : rem2 = 0
  · rcases sv_x2z (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (sgl := sgl) (tbl := tbl) (f2c := f2c) (f30 := f30) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (rem2 := rem2) (ol := ol) (op := op) (rest := rest) (rp2 := rp2) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_10 g0_11 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_3c w0_40 w0_48 w0_4c w0_158 w0_15c w0_408 w0_40c in2 oid_in ea_in hle hb with ⟨-, e⟩ | ⟨hf, -⟩
    · exact .inl e
    · exact hf.elim
  · by_cases hb2 : M0 rp2 = BitVec.ofNat 8 1
    · rcases sv_seg_x2c (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (sgl := sgl) (tbl := tbl) (f2c := f2c) (f30 := f30) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (rem2 := rem2) (ol := ol) (op := op) (rest := rest) (rp2 := rp2) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_10 g0_11 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_3c w0_40 w0_48 w0_4c w0_158 w0_15c w0_408 w0_40c in2 oid_in ea_in hle hb hb2 SD0 with e | ⟨h0, tb7_1, h1, vp14_1, vl14_1, h2, te14_1, h3, h4, h5, h6, rest⟩
      · exact .inl e
      · exact .inr ⟨vl14_1, vp14_1, .inr (.inl ⟨hb, hb2, h0, tb7_1, h1, vp14_1, vl14_1, h2, te14_1, h3, h4, h5, h6, rfl, rfl⟩), ((in2).restW h1).contentIn h2, rest.imp (fun _ => fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun k => k.mono (by decide)))))))))))))))))))))))))))))))))))))))))))))))))))))))⟩
    · rcases sv_x2n (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (sgl := sgl) (tbl := tbl) (f2c := f2c) (f30 := f30) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (rem2 := rem2) (ol := ol) (op := op) (rest := rest) (rp2 := rp2) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_10 g0_11 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_50 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_3c w0_40 w0_48 w0_4c w0_158 w0_15c w0_408 w0_40c in2 oid_in ea_in hle hb hb2 with ⟨-, e⟩ | ⟨vp8, vl8, h0, te8, h1, h2, h3, rest⟩
      · exact .inl e
      · obtain ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w34, f_w38, f_w3c, f_w40, f_w44, f_w48, f_w4c, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_KL⟩ := rest
        exact .inr ⟨vl8, vp8, .inr (.inr ⟨hb, hb2, vp8, vl8, h0, te8, h1, h2, h3, rfl, rfl⟩), (in2).contentIn h0, ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r8, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w34, f_w38, f_w44, f_w48, f_w4c, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_w3c, f_w40, f_KL.mono (by decide)⟩⟩

end C3.RV32.Sv
