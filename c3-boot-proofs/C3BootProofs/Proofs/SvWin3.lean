import C3BootProofs.Proofs.SvWin3e
import C3BootProofs.Proofs.SvWin3n

/-!
# `sigstore::verify`: Validity-window check 3, whichever way its high words compare.

Written by `scripts/gen-sv-segs.py` from `sv_win3e` and `sv_win3n`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxHeartbeats 16000000 in
/-- Validity-window check 3, whichever way its high words compare. -/
theorem sv_win3 {B out bp x21 x22 x23 x24 x25 x26 x27 w3c w54 w58 w5c w60 w78 w7c k88 k8c k90 k94 : Word} {i2h i2l : Word} {i3h i3l : Word} {t4h t4l t5h t5l : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x1A1C (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = BitVec.ofNat 32 0x1E)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = x24)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = x27)
    (w0_3c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c)
    (w0_54 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54)
    (w0_58 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58)
    (w0_5c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c)
    (w0_60 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60)
    (w0_78 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c)
    (w0_388 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = k88)
    (w0_38c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = k8c)
    (w0_390 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x390) = k90)
    (w0_394 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x394) = k94)
    (hi3h : memLoad32 M0 (x23 + 0xFFFFFFF0) = i3h)
    (ii3h : SvIn B (x23 + 0xFFFFFFF0) 4)
    (ai3h : (x23 + 0xFFFFFFF0).toNat % 4 = 0)
    (hi3l : memLoad32 M0 (x23 + 0xFFFFFFEC) = i3l)
    (ii3l : SvIn B (x23 + 0xFFFFFFEC) 4)
    (ai3l : (x23 + 0xFFFFFFEC).toNat % 4 = 0) :
    SvErrRet B out v n0 ∨
    ((((w7c = i3h) ∧ (aluEval .sltu (i3l) (w3c) = 0)) ∨ ((¬ (w7c = i3h)) ∧ (aluEval .sltu (i3h) (w7c) = 0))) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x1A36 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = BitVec.ofNat 32 0x1E ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = x24 ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = x27 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3C) = w3c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x54) = w54 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x58) = w58 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x5C) = w5c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x60) = w60 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = w78 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = w7c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x388) = k88 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38C) = k8c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x390) = k90 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x394) = k94 ∧
        SvKeepL B n0.mem n'.mem []) := by
  by_cases hb : w7c = i3h
  · rcases sv_win3e (B := B) (out := out) (bp := bp) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (w3c := w3c) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w78 := w78) (w7c := w7c) (k88 := k88) (k8c := k8c) (k90 := k90) (k94 := k94) (i2h := i2h) (i2l := i2l) (i3h := i3h) (i3l := i3l) (t4h := t4h) (t4l := t4l) (t5h := t5h) (t5l := t5l) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_3c w0_54 w0_58 w0_5c w0_60 w0_78 w0_7c w0_388 w0_38c w0_390 w0_394 hi3h ii3h ai3h hb hi3l ii3l ai3l with ⟨-, e⟩ | ⟨h0, rest⟩
    · exact .inl e
    · exact .inr ⟨.inl ⟨hb, h0⟩, rest⟩
  · rcases sv_win3n (B := B) (out := out) (bp := bp) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (w3c := w3c) (w54 := w54) (w58 := w58) (w5c := w5c) (w60 := w60) (w78 := w78) (w7c := w7c) (k88 := k88) (k8c := k8c) (k90 := k90) (k94 := k94) (i2h := i2h) (i2l := i2l) (i3h := i3h) (i3l := i3l) (t4h := t4h) (t4l := t4l) (t5h := t5h) (t5l := t5l) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_3c w0_54 w0_58 w0_5c w0_60 w0_78 w0_7c w0_388 w0_38c w0_390 w0_394 hi3h ii3h ai3h hb with ⟨-, e⟩ | ⟨h0, rest⟩
    · exact .inl e
    · exact .inr ⟨.inr ⟨hb, h0⟩, rest⟩

end C3.RV32.Sv
