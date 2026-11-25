import C3BootProofs.Proofs.SvSeg
import C3BootProofs.Proofs.SvSegAttr
import C3BootProofs.Proofs.SvTrx

/-!
# `sigstore::verify`: the signed attributes loop

Written by `scripts/gen-sv-attrloop.py` from `sv_seg_attr` and `sv_trx`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

/-- One more signed attribute, from state `s` to `s'` (`dg`, the content-type flag, and the attributes left): there are some, and the next one is well formed. -/
def sv_attrStep (B out bp x20 x21 x22 x23 p0 L0 sip sil : Word) (v : Nat → Word) (M0 : Word → BitVec 8) : Word × Word × Word × Word → Word × Word × Word × Word → Prop :=
  fun s s' => s.2.2.2 ≠ 0 ∧ (((s.2.2.2)).toNat ≤ (L0).toNat) ∧ ∃ tl6_2, derElement 0x30 (memBytes M0 ((s.2.2.1)) ((s.2.2.2)).toNat) = .ok tl6_2 ∧ ∃ op15_2 ol15_2, derContent (((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) (derOid (memBytes M0 (((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) (BitVec.ofNat 32 tl6_2.len).toNat)) = .ok (op15_2, ol15_2) ∧ ∃ to15_2, derOid (memBytes M0 (((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) (BitVec.ofNat 32 tl6_2.len).toNat) = .ok to15_2 ∧ ∃ tl20_2, derElement 0x31 (memBytes M0 ((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) ((BitVec.ofNat 32 tl6_2.len) - BitVec.ofNat 32 (to15_2.header + to15_2.len)).toNat) = .ok tl20_2 ∧ (((BitVec.ofNat 32 tl6_2.len) - BitVec.ofNat 32 (to15_2.header + to15_2.len)) - BitVec.ofNat 32 (tl20_2.header + tl20_2.len) = 0) ∧ listsOidOf M0 p0 ((L0) - ((s.2.2.2))).toNat (memBytes M0 op15_2 ol15_2.toNat) = .ok false ∧ ∃ trv_w64_3 : Word, ∃ trv_w7c_3 : Word, (((memBytes M0 op15_2 ol15_2.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9) ∧ ∃ op5 ol5, derContent ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) (derOid (memBytes M0 ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) ((BitVec.ofNat 32 tl20_2.len)).toNat)) = .ok (op5, ol5) ∧ ∃ to5, derOid (memBytes M0 ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) ((BitVec.ofNat 32 tl20_2.len)).toNat) = .ok to5 ∧ (memBytes M0 op5 ol5.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x9)) 11) ∧ (((BitVec.ofNat 32 tl20_2.len)) - BitVec.ofNat 32 (to5.header + to5.len) = 0) ∧ trv_w64_3 = (s.1) ∧ trv_w7c_3 = BitVec.ofNat 32 0x1) ∨ ((¬ (memBytes M0 op15_2 ol15_2.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9)) ∧ (memBytes M0 op15_2 ol15_2.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x1E)) 9) ∧ ∃ vp8 vl8, derContent ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) (derElement 4 (memBytes M0 ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) ((BitVec.ofNat 32 tl20_2.len)).toNat)) = .ok (vp8, vl8) ∧ ∃ te8, derElement 4 (memBytes M0 ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) ((BitVec.ofNat 32 tl20_2.len)).toNat) = .ok te8 ∧ (vl8 = 32) ∧ (((BitVec.ofNat 32 tl20_2.len)) - BitVec.ofNat 32 (te8.header + te8.len) = 0) ∧ trv_w64_3 = vp8 ∧ trv_w7c_3 = (s.2.1)) ∨ ((¬ (memBytes M0 op15_2 ol15_2.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x15)) 9)) ∧ (¬ (memBytes M0 op15_2 ol15_2.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstCmsAddress + 0x1E)) 9)) ∧ trv_w64_3 = (s.1) ∧ trv_w7c_3 = (s.2.1))) ∧ (trv_w64_3 = 0 ∨ SvIn B trv_w64_3 32) ∧ s' = (trv_w64_3, trv_w7c_3, ((s.2.2.1)) + BitVec.ofNat 32 (tl6_2.header + tl6_2.len), ((s.2.2.2)) - BitVec.ofNat 32 (tl6_2.header + tl6_2.len))

/-- How `sv_trx` ends once no attributes are left. -/
def sv_attrloopOk (B out bp x20 x21 x22 x23 p0 L0 sip sil : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (dg' flag' cp' rem' : Word) (nk : Machine) : Prop :=
  rem' = 0 ∧ (dg' = 0 ∨ SvIn B dg' 32) ∧ (((dg' ≠ 0 ∧ flag' = 1) ∧
    ∃ op9 ol9, derAlgOf M0 (sip) ((sil).toNat) = .ok ((op9, ol9), none) ∧
    ∃ te9, derElement 0x30 (memBytes M0 (sip) (sil).toNat) = .ok te9 ∧
    (memBytes M0 op9 ol9 = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress)) 8) ∧
    ∃ vp20 vl20, derContent ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) (derElement 4 (memBytes M0 ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) ((sil) - BitVec.ofNat 32 (te9.header + te9.len)).toNat)) = .ok (vp20, vl20) ∧
    ∃ te20, derElement 4 (memBytes M0 ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) ((sil) - BitVec.ofNat 32 (te9.header + te9.len)).toNat) = .ok te20 ∧
    ∃ sr25 ss25, ecdsaSigOf 48 M0 (vp20) ((vl20).toNat) = .ok (sr25, ss25) ∧
    (((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) = 0) ∧
    ∃ n', Steps nk n' ∧
        St n'.mem SV n' 0x10A4 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg nk (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg nk (4 : Fin 32) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = rem' ∧
        reg n' (25 : Fin 32) = (BitVec.ofNat 8 ((sr25).getD 0 0)).zeroExtend 32 ∧
        reg n' (26 : Fin 32) = (reg nk (26 : Fin 32)) ∧
        reg n' (27 : Fin 32) = (reg nk (27 : Fin 32)) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg' ∧
        (∀ j, j < 47 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 ((sr25).getD (1 + j) 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 ((ss25).getD j 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 ((sr25).getD j 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x451 + j)) = BitVec.ofNat 8 ((ss25).getD j 0)) ∧
        SvKeepL B nk.mem n'.mem [(0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x378, 0x8), (0x420, 0x61), (0x380, 0x5F)]))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- The signed attributes loop: `k` more attributes, then the end. -/
theorem sv_attrloop {B out bp x20 x21 x22 x23 p0 L0 sip sil : Word} {v : Nat → Word}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8) :
    ∀ (N : Nat) {dg flag cp rem : Word} {n0 : Machine},
    (hN : rem.toNat ≤ N) → (hflag : flag = 0 ∨ flag = 1) →
    (E0 : SvCode n0.mem) →
    (V0 : SvSaves B n0.mem v) →
    (s0 : St n0.mem SV n0 0xFF8 (reg n0)) →
    (fM : ∀ x, SvR B x → n0.mem x = M0 x) →
    (g0_2 : reg n0 sp = B + 0x21A0) →
    (g0_18 : reg n0 (18 : Fin 32) = out) →
    (g0_19 : reg n0 (19 : Fin 32) = bp) →
    (g0_20 : reg n0 (20 : Fin 32) = x20) →
    (g0_21 : reg n0 (21 : Fin 32) = x21) →
    (g0_22 : reg n0 (22 : Fin 32) = x22) →
    (g0_23 : reg n0 (23 : Fin 32) = x23) →
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg) →
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = flag) →
    (w0_25c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x25C) = p0) →
    (w0_260 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) = L0) →
    (w0_264 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = cp) →
    (w0_268 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rem) →
    (w0_378 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x378) = sip) →
    (w0_37c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x37C) = sil) →
    (cr_in : SvIn B (cp) (rem).toNat) →
    (p0_in : SvIn B (p0) (L0).toNat) →
    (si_in : SvIn B (sip) (sil).toNat) →
    (dg_or0 : dg = 0 ∨ SvIn B dg 32) →
    SvErrRet B out v n0 ∨ ∃ k dg' flag' cp' rem', svChain (sv_attrStep B out bp x20 x21 x22 x23 p0 L0 sip sil v M0) k (dg, flag, cp, rem) (dg', flag', cp', rem') ∧
      ∃ nk, Steps n0 nk ∧ reg nk (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg nk (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
      SvKeepL B n0.mem nk.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x420, 0x10), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x408, 0x8), (0x7C, 0x4), (0x64, 0x4)] ∧ sv_attrloopOk B out bp x20 x21 x22 x23 p0 L0 sip sil v M0 dg' flag' cp' rem' nk := by
  intro N
  induction N with
  | zero =>
    intro dg flag cp rem n0 hN hflag E0 V0 s0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 w0_64 w0_7c w0_25c w0_260 w0_264 w0_268 w0_378 w0_37c cr_in p0_in si_in dg_or0
    have h0 : rem = 0 := svRem_zero hN
    rcases sv_trx (x26 := reg n0 (26 : Fin 32)) (x27 := reg n0 (27 : Fin 32)) (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := reg n0 (24 : Fin 32)) (x25 := reg n0 (25 : Fin 32)) (dg := dg) (flag := flag) (p0 := p0) (L0 := L0) (cp := cp) (rem := rem) (sip := sip) (sil := sil) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 rfl rfl rfl rfl w0_64 w0_7c w0_25c w0_260 w0_264 w0_268 w0_378 w0_37c cr_in p0_in si_in h0 hflag with ⟨-, e⟩ | okx
    · exact .inl e
    · exact .inr ⟨0, dg, flag, cp, rem, svChain.nil, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), h0, dg_or0, okx⟩
  | succ N ih =>
    intro dg flag cp rem n0 hN hflag E0 V0 s0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 w0_64 w0_7c w0_25c w0_260 w0_264 w0_268 w0_378 w0_37c cr_in p0_in si_in dg_or0
    by_cases h0 : rem = 0
    · rcases sv_trx (x26 := reg n0 (26 : Fin 32)) (x27 := reg n0 (27 : Fin 32)) (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := reg n0 (24 : Fin 32)) (x25 := reg n0 (25 : Fin 32)) (dg := dg) (flag := flag) (p0 := p0) (L0 := L0) (cp := cp) (rem := rem) (sip := sip) (sil := sil) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 rfl rfl rfl rfl w0_64 w0_7c w0_25c w0_260 w0_264 w0_268 w0_378 w0_37c cr_in p0_in si_in h0 hflag with ⟨-, e⟩ | okx
      · exact .inl e
      · exact .inr ⟨0, dg, flag, cp, rem, svChain.nil, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), h0, dg_or0, okx⟩
    rcases sv_seg_attr (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (dg := dg) (flag := flag) (p0 := p0) (L0 := L0) (cp := cp) (rem := rem) (sip := sip) (sil := sil) (v := v) FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 rfl rfl rfl rfl w0_64 w0_7c w0_25c w0_260 w0_264 w0_268 w0_378 w0_37c cr_in p0_in si_in h0 dg_or0 with e | ⟨x1_0, x1_1tl6_2, x1_1, x1_2op15_2, x1_2ol15_2, x1_2, x1_3to15_2, x1_3, x1_4tl20_2, x1_4, x1_5, x1_6, x1_7trv_w64_3, x1_7trv_w7c_3, x1_7, x1_8, n1, c1, fR1, s1, E1, V1, r1_3, r1_4, r1_2, r1_18, r1_19, r1_20, r1_21, r1_22, r1_23, r1_24, r1_25, r1_26, r1_27, w1_64, w1_7c, w1_25c, w1_260, w1_264, w1_268, w1_378, w1_37c, K1_L⟩
    · exact .inl e
    have hdec := svRem_le (a := x1_1tl6_2.header + x1_1tl6_2.len) (N := N) (by have := derElement_header x1_1; omega)
      (by have := derElement_bound x1_1; rw [memBytes_length] at this; exact this) hN
    have hflag' : x1_7trv_w7c_3 = 0 ∨ x1_7trv_w7c_3 = 1 := by
      rcases x1_7 with ⟨pc0', op5', ol5', h0', to5', h1', h2', h3', e0, e1⟩ | ⟨pc0', pc1', vp8', vl8', h0', te8', h1', h2', h3', e0, e1⟩ | ⟨pc0', pc1', e0, e1⟩
      · exact .inr e1
      · rw [e1]; exact hflag
      · rw [e1]; exact hflag
    rcases ih hdec hflag' E1 V1 s1 fR1 r1_2 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 w1_64 w1_7c w1_25c w1_260 w1_264 w1_268 w1_378 w1_37c ((cr_in).restW x1_1) p0_in si_in x1_8 with e | ⟨k, dg', flag', cp', rem', chn, nk, cs, h3, h4, hk, okk⟩
    · exact .inl (SvErrRet.pre c1 r1_3 r1_4 (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
    · exact .inr ⟨k + 1, dg', flag', cp', rem', svChain.cons ⟨h0, x1_0, x1_1tl6_2, x1_1, x1_2op15_2, x1_2ol15_2, x1_2, x1_3to15_2, x1_3, x1_4tl20_2, x1_4, x1_5, x1_6, x1_7trv_w64_3, x1_7trv_w7c_3, x1_7, x1_8, rfl⟩ chn, nk, c1.trans cs, h3.trans r1_3, h4.trans r1_4, (K1_L.trans hk).mono (by decide), okk⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `sv_attrloop` as a stage. -/
theorem sv_attrloop_st {B out bp x20 x21 x22 x23 p0 L0 sip sil : Word} {v : Nat → Word} {N : Nat} {dg flag cp rem : Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8)
    (hN : rem.toNat ≤ N) (hflag : flag = 0 ∨ flag = 1)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (s0 : St n0.mem SV n0 0xFF8 (reg n0))
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
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
    (dg_or0 : dg = 0 ∨ SvIn B dg 32)
    :
    SvErrRet B out v n0 ∨
    (∃ k dg' flag' cp' rem', svChain (sv_attrStep B out bp x20 x21 x22 x23 p0 L0 sip sil v M0) k (dg, flag, cp, rem) (dg', flag', cp', rem') ∧
      rem' = 0 ∧ (dg' = 0 ∨ SvIn B dg' 32) ∧
      (dg' ≠ 0 ∧ flag' = 1) ∧ ∃ op9 ol9, derAlgOf M0 (sip) ((sil).toNat) = .ok ((op9, ol9), none) ∧ ∃ te9, derElement 0x30 (memBytes M0 (sip) (sil).toNat) = .ok te9 ∧ (memBytes M0 op9 ol9 = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress)) 8) ∧ ∃ vp20 vl20, derContent ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) (derElement 4 (memBytes M0 ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) ((sil) - BitVec.ofNat 32 (te9.header + te9.len)).toNat)) = .ok (vp20, vl20) ∧ ∃ te20, derElement 4 (memBytes M0 ((sip) + BitVec.ofNat 32 (te9.header + te9.len)) ((sil) - BitVec.ofNat 32 (te9.header + te9.len)).toNat) = .ok te20 ∧ ∃ sr25 ss25, ecdsaSigOf 48 M0 (vp20) ((vl20).toNat) = .ok (sr25, ss25) ∧ (((sil) - BitVec.ofNat 32 (te9.header + te9.len)) - BitVec.ofNat 32 (te20.header + te20.len) = 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x10A4 (reg n') ∧
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
        reg n' (24 : Fin 32) = rem' ∧
        reg n' (25 : Fin 32) = (BitVec.ofNat 8 ((sr25).getD 0 0)).zeroExtend 32 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = dg' ∧
        (∀ j, j < 47 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x380 + j)) = BitVec.ofNat 8 ((sr25).getD (1 + j) 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3AF + j)) = BitVec.ofNat 8 ((ss25).getD j 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x421 + j)) = BitVec.ofNat 8 ((sr25).getD j 0)) ∧
        (∀ j, j < 48 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x451 + j)) = BitVec.ofNat 8 ((ss25).getD j 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x40, 0x4), (0x420, 0x10), (0x264, 0x8), (0x3E5, 0xB), (0x3E0, 0x4), (0x3E4, 0x1), (0x420, 0x8), (0x3E8, 0x8), (0x405, 0xB), (0x400, 0x4), (0x404, 0x1), (0x408, 0x8), (0x7C, 0x4), (0x64, 0x4), (0x420, 0x1C), (0x378, 0x8), (0x400, 0x8), (0x420, 0x61), (0x380, 0x5F)]) := by
  rcases sv_attrloop FW hret hO M0 N hN hflag E0 V0 s0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 w0_64 w0_7c w0_25c w0_260 w0_264 w0_268 w0_378 w0_37c cr_in p0_in si_in dg_or0 with e | ⟨k, dg', flag', cp', rem', chn, nk, cs, hr3, hr4, hkl, okh⟩
  · exact .inl e
  obtain ⟨hz, iv0, h0, op9, ol9, h1, te9, h2, h3, vp20, vl20, h4, te20, h5, sr25, ss25, h6, h7, n1, cn, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, -, -, f_w64, f_q380, f_q3af, f_q421, f_q451, f_KL⟩ := okh
  exact .inr ⟨k, dg', flag', cp', rem', chn, hz, iv0, h0, op9, ol9, h1, te9, h2, h3, vp20, vl20, h4, te20, h5, sr25, ss25, h6, h7, n1, cs.trans cn, f_ST, f_E, f_V, f_FR, f_r2, f_r3.trans hr3, f_r4.trans hr4, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_w64, f_q380, f_q3af, f_q421, f_q451, (hkl.trans f_KL).mono (by decide)⟩

end C3.RV32.Sv
