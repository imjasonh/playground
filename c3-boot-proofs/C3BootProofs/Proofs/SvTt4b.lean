import C3BootProofs.Proofs.SvTt4e1
import C3BootProofs.Proofs.SvSegTt4x1

/-!
# `sigstore::verify`: After the `ordering` boolean, the end of the `TSTInfo` or more.

Written by `scripts/gen-sv-segs.py` from `sv_tt4e1` and `sv_seg_tt4x1`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxHeartbeats 16000000 in
/-- After the `ordering` boolean, the end of the `TSTInfo` or more. -/
theorem sv_tt4b {B out bp x20 x21 x22 x23 x24 x25 x26 x27 rp rl : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x124A (reg n0))
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
    (w0_264 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = rp)
    (w0_268 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = rl)
    (rd_in : SvIn B (rp) (rl).toNat)
    (D0 : SvData M0) :
    SvErrRet B out v n0 ∨
    (∃ tt4b_w264 : Word, ∃ tt4b_w268 : Word, (((rl = 0) ∧ tt4b_w264 = rp ∧ tt4b_w268 = rl) ∨ ((¬ (rl = 0)) ∧ ∃ tt4n_w264_2 : Word, ∃ tt4n_w268_2 : Word, (((M0 rp = BitVec.ofNat 8 2) ∧ ∃ ip4 il4, derIntOf (memBytes M0 (rp) (rl).toNat) (rp) (derElement 2 (memBytes M0 (rp) (rl).toNat)) = .ok (ip4, il4) ∧ ∃ ti4, derElement 2 (memBytes M0 (rp) (rl).toNat) = .ok ti4 ∧ tt4n_w264_2 = (rp) + BitVec.ofNat 32 (ti4.header + ti4.len) ∧ tt4n_w268_2 = (rl) - BitVec.ofNat 32 (ti4.header + ti4.len)) ∨ ((¬ (M0 rp = BitVec.ofNat 8 2)) ∧ tt4n_w264_2 = rp ∧ tt4n_w268_2 = rl)) ∧ SvIn B tt4n_w264_2 tt4n_w268_2.toNat ∧ tt4b_w264 = tt4n_w264_2 ∧ tt4b_w268 = tt4n_w268_2)) ∧ SvIn B tt4b_w264 tt4b_w268.toNat ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x1272 (reg n') ∧
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
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = x27 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = tt4b_w264 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = tt4b_w268 ∧
        SvKeepL B n0.mem n'.mem [(0x420, 0x8), (0x264, 0x8)]) := by
  by_cases hb : rl = 0
  · rcases sv_tt4e1 (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (rp := rp) (rl := rl) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_264 w0_268 rd_in D0 hb with ⟨-, e⟩ | rest
    · exact .inl e
    · exact .inr ⟨rp, rl, .inl ⟨hb, rfl, rfl⟩, rd_in, rest.imp (fun _ => fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun h => h.imp_right (fun k => k.mono (by decide))))))))))))))))))))))⟩
  · rcases sv_seg_tt4x1 (B := B) (out := out) (bp := bp) (x20 := x20) (x21 := x21) (x22 := x22) (x23 := x23) (x24 := x24) (x25 := x25) (x26 := x26) (x27 := x27) (rp := rp) (rl := rl) (v := v) (n0 := n0) FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_264 w0_268 rd_in D0 hb with e | ⟨tt4n_w264_2, tt4n_w268_2, h0, h1, rest⟩
    · exact .inl e
    · obtain ⟨n', fc, f_FR, f_ST, f_E, f_V, f_r3, f_r4, f_r2, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w264, f_w268, f_KL⟩ := rest
      exact .inr ⟨tt4n_w264_2, tt4n_w268_2, .inr ⟨hb, tt4n_w264_2, tt4n_w268_2, h0, h1, rfl, rfl⟩, h1, ⟨n', fc, f_ST, f_E, f_V, f_FR, f_r2, f_r3, f_r4, f_r18, f_r19, f_r20, f_r21, f_r22, f_r23, f_r24, f_r25, f_r26, f_r27, f_w264, f_w268, f_KL.mono (by decide)⟩⟩

end C3.RV32.Sv
