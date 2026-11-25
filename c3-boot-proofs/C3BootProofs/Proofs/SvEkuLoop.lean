import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvDeku2
import C3BootProofs.Proofs.SvDeku3

/-!
# `sigstore::verify`: an `ExtKeyUsage` value's OIDs

Written by `scripts/gen-sv-relloop.py` from `sv_deku2` and `sv_deku3`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option linter.unusedVariables false in
/-- One more `ExtKeyUsage` OID, from state `s` to `s'`: there are bytes left, and the next entry is an OID. -/
def sv_ekuStep (B out bp tbp dg rootp ll sgp kp sgl tbl f2c f30 : Word) (rem : Word) (p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c rest : Word) (v : Nat → Word) (M0 : Word → BitVec 8) : Word × Word × Word → Word × Word × Word → Prop :=
  fun s s' => s.2.1 ≠ 0 ∧ ∃ op4 ol4, derContent ((s.1)) (derOid (memBytes M0 ((s.1)) ((s.2.1)).toNat)) = .ok (op4, ol4) ∧ ∃ to4, derOid (memBytes M0 ((s.1)) ((s.2.1)).toNat) = .ok to4 ∧ s' = (((s.1)) + BitVec.ofNat 32 (to4.header + to4.len), ((s.2.1)) - BitVec.ofNat 32 (to4.header + to4.len), ((s.2.2)) ||| (if memBytes M0 op4 ol4.toNat = memBytes M0 (BitVec.ofNat 32 (img% svConstAddress + 0x8)) 8 then BitVec.ofNat 32 1 else BitVec.ofNat 32 0))

set_option linter.unusedVariables false in
/-- How `sv_deku3` ends once `cl` is 0. -/
def sv_ekuloopOk (B out bp tbp dg rootp ll sgp kp sgl tbl f2c f30 : Word) (rem : Word) (p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c rest : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (cp' : Word) (cl' : Word) (found' : Word) (nk : Machine) : Prop :=
  cl' = 0 ∧ (((found' &&& BitVec.ofNat 32 0x1 ≠ 0) ∧
    ∃ n', Steps nk n' ∧
        St n'.mem SV n' 0x3B8 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg nk (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg nk (4 : Fin 32) ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rest ∧
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
        SvKeepL B nk.mem n'.mem [(0x2C, 0x4), (0x50, 0x4)]))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- The `ExtKeyUsage` loop: `k` more OIDs, then the end. -/
theorem sv_ekuloop {B out bp tbp dg rootp ll sgp kp sgl tbl f2c f30 : Word} {rem : Word} {p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c rest : Word} {v : Nat → Word}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8) :
    ∀ (N : Nat) {cp : Word} {cl : Word} {found : Word} {n0 : Machine},
    (hN : cl.toNat ≤ N) →
    (E0 : SvCode n0.mem) →
    (V0 : SvSaves B n0.mem v) →
    (s0 : St n0.mem SV n0 0x5DC (reg n0)) →
    (fM : ∀ x, SvR B x → n0.mem x = M0 x) →
    (g0_2 : reg n0 sp = B + 0x21A0) →
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
    (w0_15c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest) →
    (w0_388 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = cp) →
    (w0_38c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = cl) →
    (g0_26 : reg n0 (26 : Fin 32) = found) →
    (c_in : SvIn B cp cl.toNat) →
    (SD0 : SvData M0) →
    SvErrRet B out v n0 ∨ ∃ k cp' cl' found', svChain (sv_ekuStep B out bp tbp dg rootp ll sgp kp sgl tbl f2c f30 rem p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c rest v M0) k (cp, cl, found) (cp', cl', found') ∧
      ∃ nk, Steps n0 nk ∧ reg nk (3 : Fin 32) = reg n0 (3 : Fin 32) ∧ reg nk (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
      SvKeepL B n0.mem nk.mem [(0x420, 0x8), (0x388, 0x8)] ∧ sv_ekuloopOk B out bp tbp dg rootp ll sgp kp sgl tbl f2c f30 rem p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c rest v M0 cp' cl' found' nk := by
  intro N
  induction N with
  | zero =>
    intro cp cl found n0 hN E0 V0 s0 fM g0_2 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_158 w0_15c w0_388 w0_38c g0_26 c_in SD0 
    have h0 : cl = 0 := svRem_zero hN
    rcases sv_deku3 (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (sgl := sgl) (tbl := tbl) (f2c := f2c) (f30 := f30) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (cp := cp) (cl := cl) (rest := rest) (found := found) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_158 w0_15c w0_388 w0_38c g0_26 c_in h0 with ⟨-, e⟩ | okx
    · exact .inl e
    · exact .inr ⟨0, cp, cl, found, svChain.nil, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), h0, okx⟩
  | succ N ih =>
    intro cp cl found n0 hN E0 V0 s0 fM g0_2 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_158 w0_15c w0_388 w0_38c g0_26 c_in SD0 
    by_cases h0 : cl = 0
    · rcases sv_deku3 (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (sgl := sgl) (tbl := tbl) (f2c := f2c) (f30 := f30) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (cp := cp) (cl := cl) (rest := rest) (found := found) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_158 w0_15c w0_388 w0_38c g0_26 c_in h0 with ⟨-, e⟩ | okx
      · exact .inl e
      · exact .inr ⟨0, cp, cl, found, svChain.nil, n0, .refl _, rfl, rfl, SvKeepL.refl.mono (by decide), h0, okx⟩
    rcases sv_deku2 (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (sgl := sgl) (tbl := tbl) (f2c := f2c) (f30 := f30) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (cp := cp) (cl := cl) (rest := rest) (found := found) (v := v) FW E0 V0 hret hO s0 M0 fM g0_2 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_158 w0_15c w0_388 w0_38c g0_26 c_in h0 SD0 with ⟨-, e⟩ | ⟨x1_0op4, x1_0ol4, x1_0, x1_1to4, x1_1, n1, c1, s1, E1, V1, fR1, r1_2, r1_3, r1_4, r1_9, r1_18, r1_19, r1_20, r1_21, r1_22, r1_23, r1_24, r1_25, r1_26, r1_27, w1_2c, w1_30, w1_54, w1_58, w1_5c, w1_60, w1_64, w1_68, w1_6c, w1_70, w1_74, w1_78, w1_7c, w1_80, w1_84, w1_88, w1_8c, w1_90, w1_94, w1_98, w1_9c, w1_a0, w1_a4, w1_150, w1_154, w1_158, w1_15c, w1_388, w1_38c, K1_L⟩
    · exact .inl e
    have hdec := svRem_elem (derOid_ok_elem x1_1) hN
    rcases ih hdec E1 V1 s1 fR1 r1_2 r1_9 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 r1_24 r1_25 r1_27 w1_2c w1_30 w1_54 w1_58 w1_5c w1_60 w1_64 w1_68 w1_6c w1_70 w1_74 w1_78 w1_7c w1_80 w1_84 w1_88 w1_8c w1_90 w1_94 w1_98 w1_9c w1_a0 w1_a4 w1_150 w1_154 w1_158 w1_15c w1_388 w1_38c r1_26 ((c_in).restW (derOid_ok_elem x1_1)) SD0 with e | ⟨k, cp', cl', found', chn, nk, cs, h3, h4, hk, okk⟩
    · exact .inl (SvErrRet.pre c1 r1_3 r1_4 (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
    · exact .inr ⟨k + 1, cp', cl', found', svChain.cons ⟨h0, x1_0op4, x1_0ol4, x1_0, x1_1to4, x1_1, rfl⟩ chn, nk, c1.trans cs, h3.trans r1_3, h4.trans r1_4, (K1_L.trans hk).mono (by decide), okk⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `sv_ekuloop` as a stage. -/
theorem sv_ekuloop_st {B out bp tbp dg rootp ll sgp kp sgl tbl f2c f30 : Word} {rem : Word} {p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c rest : Word} {v : Nat → Word} {N : Nat} {cp : Word} {cl : Word} {found : Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (hret : v 0 &&& ~~~1 = v 0) (hO : SvOut B out) (M0 : Word → BitVec 8)
    (hN : cl.toNat ≤ N)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (s0 : St n0.mem SV n0 0x5DC (reg n0))
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
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
    (w0_15c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x15C) = rest)
    (w0_388 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = cp)
    (w0_38c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = cl)
    (g0_26 : reg n0 (26 : Fin 32) = found)
    (c_in : SvIn B cp cl.toNat)
    (SD0 : SvData M0)
    :
    SvErrRet B out v n0 ∨
    (∃ k cp' cl' found', svChain (sv_ekuStep B out bp tbp dg rootp ll sgp kp sgl tbl f2c f30 rem p0 L cur sl0 sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 sl9 w54 w58 w5c w60 w64 w68 w6c w70 w74 w78 w7c rest v M0) k (cp, cl, found) (cp', cl', found') ∧
      cl' = 0 ∧
      (found' &&& BitVec.ofNat 32 0x1 ≠ 0) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x3B8 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
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
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x2C) = BitVec.ofNat 32 0x1 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x30) = f30 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = rest ∧
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
        SvKeepL B n0.mem n'.mem [(0x420, 0x8), (0x388, 0x8), (0x2C, 0x4), (0x50, 0x4)]) := by
  rcases sv_ekuloop (B := B) (out := out) (bp := bp) (tbp := tbp) (dg := dg) (rootp := rootp) (ll := ll) (sgp := sgp) (kp := kp) (sgl := sgl) (tbl := tbl) (f2c := f2c) (f30 := f30) (rem := rem) (p0 := p0) (L := L) (cur := cur) (sl0 := sl0) (sl1 := sl1) (sl2 := sl2) (sl3 := sl3) (sl4 := sl4) (sl5 := sl5) (sl6 := sl6) (sl7 := sl7) (sl8 := sl8) (sl9 := sl9) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w64 := w64) (w68 := w68) (w6c := w6c) (w70 := w70) (w74 := w74) (w78 := w78) (w7c := w7c) (rest := rest) (v := v) FW hret hO M0 N hN E0 V0 s0 fM g0_2 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_27 w0_2c w0_30 w0_54 w0_58 w0_5c w0_60 w0_64 w0_68 w0_6c w0_70 w0_74 w0_78 w0_7c w0_80 w0_84 w0_88 w0_8c w0_90 w0_94 w0_98 w0_9c w0_a0 w0_a4 w0_150 w0_154 w0_158 w0_15c w0_388 w0_38c g0_26 c_in SD0  with e | ⟨k, cp', cl', found', chn, nk, cs, hr3, hr4, hkl, okh⟩
  · exact .inl e
  obtain ⟨hz, h0, n1, cn, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, f_KL⟩ := okh
  exact .inr ⟨k, cp', cl', found', chn, hz, h0, n1, cs.trans cn, f_ST, f_E, f_V, f_FR, f_r2, f_r3.trans hr3, f_r4.trans hr4, f_r9, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r27, f_w2c, f_w30, f_w50, f_w54, f_w58, f_w5c, f_w60, f_w64, f_w68, f_w6c, f_w70, f_w74, f_w78, f_w7c, f_w80, f_w84, f_w88, f_w8c, f_w90, f_w94, f_w98, f_w9c, f_wa0, f_wa4, f_w150, f_w154, f_w158, f_w15c, (hkl.trans f_KL).mono (by decide)⟩

end C3.RV32.Sv
