import C3BootProofs.Proofs.SvCk2b
import C3BootProofs.Proofs.SvCk2a

/-!
# `sigstore::verify`: The checkpoint's size line, one digit or more.

Written by `scripts/gen-sv-segs.py` from `sv_ck2b` and `sv_ck2a`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxHeartbeats 16000000 in
/-- The checkpoint's size line, one digit or more. -/
theorem sv_ck2 {B out bp x20 x21 x22 x23 x26 ckl sl sp1 rl rp sgp w50 : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x14C2 (reg n0))
    (M0 : Word → BitVec 8)
    (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = sl)
    (g0_9 : reg n0 (9 : Fin 32) = ckl)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = x23)
    (g0_24 : reg n0 (24 : Fin 32) = sp1)
    (g0_25 : reg n0 (25 : Fin 32) = rp)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = rl)
    (w0_50 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50)
    (w0_428 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp)
    (sz_in : SvIn B sp1 sl.toNat) :
    SvErrRet B out v n0 ∨
    ((((1 < sl.toNat) ∧ (w50.toNat < ckl.toNat) ∧ (¬ (ckl).toNat < ((aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl)).toNat) ∧ (¬ ((sl) + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat) ∧ (M0 sp1 ≠ 0x30)) ∨ ((¬ (1 < sl.toNat)) ∧ (w50.toNat < ckl.toNat) ∧ (¬ (ckl).toNat < ((aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl)).toNat) ∧ (¬ ((sl) + BitVec.ofNat 32 0xFFFFFFEC).toNat < (BitVec.ofNat 32 0xFFFFFFED).toNat))) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x14FE (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = sl ∧
        reg n' (9 : Fin 32) = ckl ∧
        reg n' a0 = BitVec.ofNat 32 0xA ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = x23 ∧
        reg n' (24 : Fin 32) = sp1 ∧
        reg n' (25 : Fin 32) = rp ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = rl ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x24) = (aluEval .xor (w50) (BitVec.ofNat 32 0xFFFFFFFF)) + (ckl) ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x38) = sgp ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x50) = w50 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x64) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = BitVec.ofNat 32 0x0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x428) = sgp ∧
        SvKeepL B n0.mem n'.mem [(0x24, 0x4), (0x38, 0x4), (0x64, 0x4), (0x74, 0x4)]) := by
  by_cases hb : 1 < sl.toNat
  · rcases sv_ck2b (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x26 := x26) (ckl := ckl) (sl := sl) (sp1 := sp1) (rl := rl) (rp := rp) (sgp := sgp) (w50 := w50) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_50 w0_428 sz_in hb with ⟨-, e⟩ | ⟨h0, h1, h2, h3, rest⟩
    · exact .inl e
    · exact .inr ⟨.inl ⟨hb, h0, h1, h2, h3⟩, rest⟩
  · rcases sv_ck2a (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x26 := x26) (ckl := ckl) (sl := sl) (sp1 := sp1) (rl := rl) (rp := rp) (sgp := sgp) (w50 := w50) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_8 g0_9 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_50 w0_428 sz_in hb with ⟨-, e⟩ | ⟨h0, h1, h2, rest⟩
    · exact .inl e
    · exact .inr ⟨.inr ⟨hb, h0, h1, h2⟩, rest⟩

end C3.RV32.Sv
