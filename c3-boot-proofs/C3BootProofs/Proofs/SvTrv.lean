import C3BootProofs.Proofs.SvTrvct
import C3BootProofs.Proofs.SvTrvmd
import C3BootProofs.Proofs.SvTrvother

/-!
# `sigstore::verify`: One signed attribute's value: the content type, the message digest, or another.

Written by `scripts/gen-sv-segs.py` from `sv_trvct`, `sv_trvmd`, and `sv_trvother`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxHeartbeats 16000000 in
/-- One signed attribute's value: the content type, the message digest, or another. -/
theorem sv_trv {B out bp x20 x21 x22 x23 x25 dg flag p0 L0 op ol vcp vcl x24 cp rem sip sil : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0xF5C (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_9 : reg n0 (9 : Fin 32) = op)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = x24)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = ol)
    (g0_27 : reg n0 (27 : Fin 32) = L0)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag)
    (w0_25c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0)
    (w0_260 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0)
    (w0_264 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp)
    (w0_268 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem)
    (w0_378 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip)
    (w0_37c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil)
    (w0_408 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x408) = vcp)
    (w0_40c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40C) = vcl)
    (cr_in : SvIn B (cp) (rem).toNat)
    (p0_in : SvIn B (p0) (L0).toNat)
    (si_in : SvIn B (sip) (sil).toNat)
    (vc_in : SvIn B (vcp) (vcl).toNat)
    (oid_in : SvIn B op ol.toNat)
    (dg_or0 : dg = 0 ∨ SvIn B dg 32) :
    SvErrRet B out v n0 ∨
    (∃ trv_w64 : Word, ∃ trv_w7c : Word, (((memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9) ∧ ∃ op5 ol5, derContent (vcp) (derOid (memBytes M0 (vcp) (vcl).toNat)) = .ok (op5, ol5) ∧ ∃ to5, derOid (memBytes M0 (vcp) (vcl).toNat) = .ok to5 ∧ (memBytes M0 op5 ol5.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x9)) 11) ∧ ((vcl) - BitVec.ofNat 32 (to5.header + to5.len) = 0) ∧ trv_w64 = dg ∧ trv_w7c = BitVec.ofNat 32 0x1) ∨ ((¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9)) ∧ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x1E)) 9) ∧ ∃ vp8 vl8, derContent (vcp) (derElement 4 (memBytes M0 (vcp) (vcl).toNat)) = .ok (vp8, vl8) ∧ ∃ te8, derElement 4 (memBytes M0 (vcp) (vcl).toNat) = .ok te8 ∧ (vl8 = 32) ∧ ((vcl) - BitVec.ofNat 32 (te8.header + te8.len) = 0) ∧ trv_w64 = vp8 ∧ trv_w7c = flag) ∨ ((¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9)) ∧ (¬ (memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x1E)) 9)) ∧ trv_w64 = dg ∧ trv_w7c = flag)) ∧ (trv_w64 = 0 ∨ SvIn B trv_w64 32) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0xFF8 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = x24 ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = ol ∧
        reg n' (27 : Fin 32) = L0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = trv_w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = trv_w7c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x8), (0x408, 0x8), (0x7C, 0x4), (0x64, 0x4)]) := by
  by_cases hb : memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9
  · rcases sv_trvct (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x25 := x25) (dg := dg) (flag := flag) (p0 := p0) (L0 := L0) (op := op) (ol := ol) (vcp := vcp) (vcl := vcl) (x24 := x24) (cp := cp) (rem := rem) (sip := sip) (sil := sil) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_64 w0_7c w0_25c w0_260 w0_264 w0_268 w0_378 w0_37c w0_408 w0_40c cr_in p0_in si_in vc_in oid_in hb with ⟨-, e⟩ | ⟨op5, ol5, h0, to5, h1, h2, h3, rest⟩
    · exact .inl e
    · exact .inr ⟨dg, BitVec.ofNat 32 0x1, .inl ⟨hb, op5, ol5, h0, to5, h1, h2, h3, rfl, rfl⟩, dg_or0, rest.imp (fun _ => fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun k => k.mono (by decide))))))))))))))))))))))))))))⟩
  · by_cases hb2 : memBytes M0 op ol.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x1E)) 9
    · rcases sv_trvmd (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x25 := x25) (dg := dg) (flag := flag) (p0 := p0) (L0 := L0) (op := op) (ol := ol) (vcp := vcp) (vcl := vcl) (x24 := x24) (cp := cp) (rem := rem) (sip := sip) (sil := sil) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_64 w0_7c w0_25c w0_260 w0_264 w0_268 w0_378 w0_37c w0_408 w0_40c cr_in p0_in si_in vc_in oid_in hb hb2 with ⟨-, e⟩ | ⟨vp8, vl8, h0, te8, h1, h2, h3, rest⟩
      · exact .inl e
      · exact .inr ⟨vp8, flag, .inr (.inl ⟨hb, hb2, vp8, vl8, h0, te8, h1, h2, h3, rfl, rfl⟩), .inr (by have h := (vc_in).contentIn h0; rw [h2] at h; exact h), rest.imp (fun _ => fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun k => k.mono (by decide))))))))))))))))))))))))))))⟩
    · rcases sv_trvother (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x25 := x25) (dg := dg) (flag := flag) (p0 := p0) (L0 := L0) (op := op) (ol := ol) (vcp := vcp) (vcl := vcl) (x24 := x24) (cp := cp) (rem := rem) (sip := sip) (sil := sil) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_64 w0_7c w0_25c w0_260 w0_264 w0_268 w0_378 w0_37c w0_408 w0_40c cr_in p0_in si_in vc_in oid_in hb hb2 with ⟨-, e⟩ | rest
      · exact .inl e
      · exact .inr ⟨dg, flag, .inr (.inr ⟨hb, hb2, rfl, rfl⟩), dg_or0, rest.imp (fun _ => fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun k => k.mono (by decide))))))))))))))))))))))))))))⟩

end C3.RV32.Sv
