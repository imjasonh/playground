import C3BootProofs.Proofs.SvCr1e
import C3BootProofs.Proofs.SvCr1n

/-!
# `sigstore::verify`: The entry's index against the checkpoint's size, whichever way the high words compare.

Written by `scripts/gen-sv-segs.py` from `sv_cr1e` and `sv_cr1n`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxHeartbeats 16000000 in
/-- The entry's index against the checkpoint's size, whichever way the high words compare. -/
theorem sv_cr1 {B out bp x20 x21 x22 x23 x24 x25 x26 x27 kp w1c w40 q w64 w74 lih lil : Word} {rt : Bytes} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x17F8 (reg n0))
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
    (w0_1c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c)
    (w0_20 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32)
    (w0_34 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp)
    (w0_40 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40)
    (w0_4c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q)
    (w0_64 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74)
    (q0_3e0 : ∀ j, j < 31 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0))
    (RS : SvRoSep B)
    (lid_in : SvIn B (q + BitVec.ofNat 32 0x5) 19)
    (h40 : w40 ≠ 0)
    (hlih : memLoad32 M0 (bp + 0x2C) = lih)
    (hlil : memLoad32 M0 (bp + 0x28) = lil)
    (lih_in : SvIn B (bp + 0x2C) 4)
    (lil_in : SvIn B (bp + 0x28) 4)
    (a_lih : (bp + 0x2C).toNat % 4 = 0)
    (a_lil : (bp + 0x28).toNat % 4 = 0) :
    SvErrRet B out v n0 ∨
    ((((lih = w74) ∧ (aluEval .sltu (lil) (w64) ≠ 0)) ∨ ((¬ (lih = w74)) ∧ (aluEval .sltu (lih) (w74) ≠ 0))) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x189A (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = lil ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = lih ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = x27 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1C) = w1c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x20) = (BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x34) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x40) = w40 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x4C) = q ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = w74 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x380) = w40 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x398) = kp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x39C) = w1c ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A0) = w64 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A4) = w74 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x384) = (x25).extractLsb' 0 8 ∧
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x3A8) = ((BitVec.ofNat 8 (rt.getD 0 0)).zeroExtend 32).extractLsb' 0 8 ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x25C + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0)) ∧
        (∀ j, j < 19 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x27C + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 19 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x385 + j)) = M0 (((q) + BitVec.ofNat 32 0x5) + BitVec.ofNat 32 j)) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3A9 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0)) ∧
        (∀ j, j < 31 → n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x3E0 + j)) = BitVec.ofNat 8 (rt.getD (1 + j) 0)) ∧
        SvKeepL B n0.mem n'.mem [(0x27C, 0x13), (0x25C, 0x1F), (0x385, 0x13), (0x398, 0x4), (0x39C, 0x4), (0x3A8, 0x1), (0x3A9, 0x1F), (0x380, 0x4), (0x384, 0x1), (0x3A0, 0x4), (0x3A4, 0x4)]) := by
  by_cases hb : lih = w74
  · rcases sv_cr1e (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (kp := kp) (w1c := w1c) (w40 := w40) (q := q) (w64 := w64) (w74 := w74) (lih := lih) (lil := lil) (rt := rt) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_1c w0_20 w0_34 w0_40 w0_4c w0_64 w0_74 q0_3e0 RS lid_in h40 hlih hlil lih_in lil_in a_lih a_lil hb with ⟨-, e⟩ | ⟨h0, rest⟩
    · exact .inl e
    · exact .inr ⟨.inl ⟨hb, h0⟩, rest⟩
  · rcases sv_cr1n (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (kp := kp) (w1c := w1c) (w40 := w40) (q := q) (w64 := w64) (w74 := w74) (lih := lih) (lil := lil) (rt := rt) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_1c w0_20 w0_34 w0_40 w0_4c w0_64 w0_74 q0_3e0 RS lid_in h40 hlih hlil lih_in lil_in a_lih a_lil hb with ⟨-, e⟩ | ⟨h0, rest⟩
    · exact .inl e
    · exact .inr ⟨.inr ⟨hb, h0⟩, rest⟩

end C3.RV32.Sv
