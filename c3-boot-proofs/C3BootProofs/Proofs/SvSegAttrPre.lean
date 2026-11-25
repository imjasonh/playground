import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvTra
import C3BootProofs.Proofs.SvTrv

/-!
# `sigstore::verify`: The first signed attribute

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **The first signed attribute**: from 0xEA0 to the attributes loop's branch at 0xFF8. -/
theorem sv_seg_attr_pre {B out bp x20 x21 x22 x23 x25 dg flag p0 L0 cp rem sip sil : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0xEA0 (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = rem)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = x27)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag)
    (w0_25c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0)
    (w0_260 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0)
    (w0_264 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp)
    (w0_268 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem)
    (w0_378 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip)
    (w0_37c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil)
    (cr_in : SvIn B (cp) (rem).toNat)
    (p0_in : SvIn B (p0) (L0).toNat)
    (si_in : SvIn B (sip) (sil).toNat)
    (dg_or0 : dg = 0 ∨ SvIn B dg 32) :
    SvErrRet B out v n0 ∨
    (((rem).toNat ≤ (L0).toNat) ∧
      ∃ tl6_1, derElement 0x30 (memBytes M0 (cp) (rem).toNat) = .ok tl6_1 ∧
      ∃ op15_1 ol15_1, derContent ((cp) + BitVec.ofNat 32 tl6_1.header) (derOid (memBytes M0 ((cp) + BitVec.ofNat 32 tl6_1.header) (BitVec.ofNat 32 tl6_1.len).toNat)) = .ok (op15_1, ol15_1) ∧
      ∃ to15_1, derOid (memBytes M0 ((cp) + BitVec.ofNat 32 tl6_1.header) (BitVec.ofNat 32 tl6_1.len).toNat) = .ok to15_1 ∧
      ∃ tl20_1, derElement 0x31 (memBytes M0 (((cp) + BitVec.ofNat 32 tl6_1.header) + BitVec.ofNat 32 (to15_1.header + to15_1.len)) ((BitVec.ofNat 32 tl6_1.len) - BitVec.ofNat 32 (to15_1.header + to15_1.len)).toNat) = .ok tl20_1 ∧
      (((BitVec.ofNat 32 tl6_1.len) - BitVec.ofNat 32 (to15_1.header + to15_1.len)) - BitVec.ofNat 32 (tl20_1.header + tl20_1.len) = 0) ∧
      listsOidOf M0 p0 ((L0) - (rem)).toNat (memBytes M0 op15_1 ol15_1.toNat) = .ok false ∧
      ∃ trv_w64_2 : Word, ∃ trv_w7c_2 : Word, (((memBytes M0 op15_1 ol15_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9) ∧ ∃ op5 ol5, derContent (((((cp) + BitVec.ofNat 32 tl6_1.header) + BitVec.ofNat 32 (to15_1.header + to15_1.len)) + BitVec.ofNat 32 tl20_1.header)) (derOid (memBytes M0 (((((cp) + BitVec.ofNat 32 tl6_1.header) + BitVec.ofNat 32 (to15_1.header + to15_1.len)) + BitVec.ofNat 32 tl20_1.header)) ((BitVec.ofNat 32 tl20_1.len)).toNat)) = .ok (op5, ol5) ∧ ∃ to5, derOid (memBytes M0 (((((cp) + BitVec.ofNat 32 tl6_1.header) + BitVec.ofNat 32 (to15_1.header + to15_1.len)) + BitVec.ofNat 32 tl20_1.header)) ((BitVec.ofNat 32 tl20_1.len)).toNat) = .ok to5 ∧ (memBytes M0 op5 ol5.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x9)) 11) ∧ (((BitVec.ofNat 32 tl20_1.len)) - BitVec.ofNat 32 (to5.header + to5.len) = 0) ∧ trv_w64_2 = dg ∧ trv_w7c_2 = BitVec.ofNat 32 0x1) ∨ ((¬ (memBytes M0 op15_1 ol15_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9)) ∧ (memBytes M0 op15_1 ol15_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x1E)) 9) ∧ ∃ vp8 vl8, derContent (((((cp) + BitVec.ofNat 32 tl6_1.header) + BitVec.ofNat 32 (to15_1.header + to15_1.len)) + BitVec.ofNat 32 tl20_1.header)) (derElement 4 (memBytes M0 (((((cp) + BitVec.ofNat 32 tl6_1.header) + BitVec.ofNat 32 (to15_1.header + to15_1.len)) + BitVec.ofNat 32 tl20_1.header)) ((BitVec.ofNat 32 tl20_1.len)).toNat)) = .ok (vp8, vl8) ∧ ∃ te8, derElement 4 (memBytes M0 (((((cp) + BitVec.ofNat 32 tl6_1.header) + BitVec.ofNat 32 (to15_1.header + to15_1.len)) + BitVec.ofNat 32 tl20_1.header)) ((BitVec.ofNat 32 tl20_1.len)).toNat) = .ok te8 ∧ (vl8 = 32) ∧ (((BitVec.ofNat 32 tl20_1.len)) - BitVec.ofNat 32 (te8.header + te8.len) = 0) ∧ trv_w64_2 = vp8 ∧ trv_w7c_2 = flag) ∨ ((¬ (memBytes M0 op15_1 ol15_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9)) ∧ (¬ (memBytes M0 op15_1 ol15_1.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x1E)) 9)) ∧ trv_w64_2 = dg ∧ trv_w7c_2 = flag)) ∧ (trv_w64_2 = 0 ∨ SvIn B trv_w64_2 32) ∧
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0xFF8 (reg n') ∧
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
        reg n' (24 : Fin 32) = rem ∧
        reg n' (25 : Fin 32) = ((((cp) + BitVec.ofNat 32 tl6_1.header) + BitVec.ofNat 32 (to15_1.header + to15_1.len)) + BitVec.ofNat 32 tl20_1.header) ∧
        reg n' (26 : Fin 32) = ol15_1 ∧
        reg n' (27 : Fin 32) = L0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = trv_w64_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = trv_w7c_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = ((cp) + BitVec.ofNat 32 (tl6_1.header + tl6_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = ((rem) - BitVec.ofNat 32 (tl6_1.header + tl6_1.len)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil ∧
        SvKeepL B n0.mem n'.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x408, 0x8), (0x7C, 0x4), (0x64, 0x4)]) := by
  rcases sv_tra FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_64 w0_7c w0_25c w0_260 w0_264 w0_268 w0_378 w0_37c cr_in p0_in si_in with ⟨-, e⟩ | hx1
  · exact .inl e
  obtain ⟨x1_0, hx1⟩ := hx1
  obtain ⟨tl6_1, hx1⟩ := hx1
  obtain ⟨x1_1, hx1⟩ := hx1
  obtain ⟨op15_1, hx1⟩ := hx1
  obtain ⟨ol15_1, hx1⟩ := hx1
  obtain ⟨x1_2, hx1⟩ := hx1
  obtain ⟨to15_1, hx1⟩ := hx1
  obtain ⟨x1_3, hx1⟩ := hx1
  obtain ⟨tl20_1, hx1⟩ := hx1
  obtain ⟨x1_4, hx1⟩ := hx1
  obtain ⟨x1_5, hx1⟩ := hx1
  obtain ⟨x1_6, hx1⟩ := hx1
  obtain ⟨n1, hx1⟩ := hx1
  obtain ⟨c1, hx1⟩ := hx1
  obtain ⟨s1, hx1⟩ := hx1
  obtain ⟨E1, hx1⟩ := hx1
  obtain ⟨V1, hx1⟩ := hx1
  obtain ⟨fR1, hx1⟩ := hx1
  obtain ⟨r1_2, hx1⟩ := hx1
  obtain ⟨r1_3, hx1⟩ := hx1
  obtain ⟨r1_4, hx1⟩ := hx1
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
  obtain ⟨w1_64, hx1⟩ := hx1
  obtain ⟨w1_7c, hx1⟩ := hx1
  obtain ⟨w1_25c, hx1⟩ := hx1
  obtain ⟨w1_260, hx1⟩ := hx1
  obtain ⟨w1_264, hx1⟩ := hx1
  obtain ⟨w1_268, hx1⟩ := hx1
  obtain ⟨w1_378, hx1⟩ := hx1
  obtain ⟨w1_37c, hx1⟩ := hx1
  obtain ⟨w1_408, hx1⟩ := hx1
  obtain ⟨w1_40c, hx1⟩ := hx1
  have K1_L := hx1
  rcases sv_trv FW E1 V1 hret hO s1 M0 fR1 r1_2 r1_9 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 r1_24 r1_25 r1_26 r1_27 w1_64 w1_7c w1_25c w1_260 w1_264 w1_268 w1_378 w1_37c w1_408 w1_40c ((cr_in).restW x1_1) p0_in si_in ((((((cr_in).content x1_1).ofNatLen).restW (derOid_ok_elem x1_3)).content x1_4).ofNatLen) ((((cr_in).content x1_1).ofNatLen).oidIn x1_2) dg_or0 with e | hx2
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  obtain ⟨trv_w64_2, hx2⟩ := hx2
  obtain ⟨trv_w7c_2, hx2⟩ := hx2
  obtain ⟨x2_0, hx2⟩ := hx2
  obtain ⟨x2_1, hx2⟩ := hx2
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
  obtain ⟨w2_64, hx2⟩ := hx2
  obtain ⟨w2_7c, hx2⟩ := hx2
  obtain ⟨w2_25c, hx2⟩ := hx2
  obtain ⟨w2_260, hx2⟩ := hx2
  obtain ⟨w2_264, hx2⟩ := hx2
  obtain ⟨w2_268, hx2⟩ := hx2
  obtain ⟨w2_378, hx2⟩ := hx2
  obtain ⟨w2_37c, hx2⟩ := hx2
  have K2_L := hx2
  exact .inr ⟨x1_0, tl6_1, x1_1, op15_1, ol15_1, x1_2, to15_1, x1_3, tl20_1, x1_4, x1_5, x1_6, trv_w64_2, trv_w7c_2, x2_0, x2_1, n2, c1.trans (c2), fR2, s2, E2, V2,
    by rw [r2_3, r1_3], by rw [r2_4, r1_4], r2_2, r2_18, r2_19, r2_20, r2_21, r2_22, r2_23, r2_24, r2_25, r2_26, r2_27, w2_64, w2_7c, w2_25c, w2_260, w2_264, w2_268, w2_378, w2_37c, ((K1_L).trans K2_L).mono (by decide)⟩

end C3.RV32.Sv
