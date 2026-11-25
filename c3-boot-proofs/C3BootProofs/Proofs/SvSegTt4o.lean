import C3BootProofs.Proofs.SvSegCk
import C3BootProofs.Proofs.SvTt4o
import C3BootProofs.Proofs.SvTt4b

/-!
# `sigstore::verify`: The `ordering` boolean and what follows it

Composed from generated stages by `scripts/gen-sv-segs.py`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2

set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
/-- **The `ordering` boolean and what follows it**: from 0x121E to 0x1272. -/
theorem sv_seg_tt4o {B out bp x20 x21 x22 x23 x24 x25 x26 x27 rp rl : Word} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (E0 : SvCode n0.mem)
    (V0 : SvSaves B n0.mem v)
    (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out)
    (s0 : St n0.mem SV n0 0x121E (reg n0))
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
    (D0 : SvData M0)
    (hrl : rl ≠ 0)
    (hb1 : M0 rp = BitVec.ofNat 8 1) :
    SvErrRet B out v n0 ∨
    (derBoolOf (memBytes M0 (rp) (rl).toNat) (derElement 1 (memBytes M0 (rp) (rl).toNat)) = .ok () ∧
      ∃ tb8_1, derElement 1 (memBytes M0 (rp) (rl).toNat) = .ok tb8_1 ∧
      ∃ tt4b_w264_2 : Word, ∃ tt4b_w268_2 : Word, (((((rl) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = 0) ∧ tt4b_w264_2 = ((rp) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) ∧ tt4b_w268_2 = ((rl) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) ∨ ((¬ (((rl) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = 0)) ∧ ∃ tt4n_w264_2 : Word, ∃ tt4n_w268_2 : Word, (((M0 ((rp) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = BitVec.ofNat 8 2) ∧ ∃ ip4 il4, derIntOf (memBytes M0 (((rp) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (((rl) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))).toNat) (((rp) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (derElement 2 (memBytes M0 (((rp) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (((rl) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))).toNat)) = .ok (ip4, il4) ∧ ∃ ti4, derElement 2 (memBytes M0 (((rp) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) (((rl) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))).toNat) = .ok ti4 ∧ tt4n_w264_2 = (((rp) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) + BitVec.ofNat 32 (ti4.header + ti4.len) ∧ tt4n_w268_2 = (((rl) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len))) - BitVec.ofNat 32 (ti4.header + ti4.len)) ∨ ((¬ (M0 ((rp) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) = BitVec.ofNat 8 2)) ∧ tt4n_w264_2 = ((rp) + BitVec.ofNat 32 (tb8_1.header + tb8_1.len)) ∧ tt4n_w268_2 = ((rl) - BitVec.ofNat 32 (tb8_1.header + tb8_1.len)))) ∧ SvIn B tt4n_w264_2 tt4n_w268_2.toNat ∧ tt4b_w264_2 = tt4n_w264_2 ∧ tt4b_w268_2 = tt4n_w268_2)) ∧ SvIn B tt4b_w264_2 tt4b_w268_2.toNat ∧
    ∃ n', Steps n0 n' ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        St n'.mem SV n' 0x1272 (reg n') ∧
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
        reg n' (24 : Fin 32) = x24 ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = x27 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x264) = tt4b_w264_2 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x268) = tt4b_w268_2 ∧
        SvKeepL B n0.mem n'.mem [(0x264, 0x8), (0x420, 0x8)]) := by
  rcases sv_tt4o FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 g0_19 g0_20 g0_21 g0_22 g0_23 g0_24 g0_25 g0_26 g0_27 w0_264 w0_268 rd_in D0 hrl hb1 with ⟨-, e⟩ | hx1
  · exact .inl e
  obtain ⟨x1_0, hx1⟩ := hx1
  obtain ⟨tb8_1, hx1⟩ := hx1
  obtain ⟨x1_1, hx1⟩ := hx1
  obtain ⟨n1, hx1⟩ := hx1
  obtain ⟨c1, hx1⟩ := hx1
  obtain ⟨s1, hx1⟩ := hx1
  obtain ⟨E1, hx1⟩ := hx1
  obtain ⟨V1, hx1⟩ := hx1
  obtain ⟨fR1, hx1⟩ := hx1
  obtain ⟨r1_2, hx1⟩ := hx1
  obtain ⟨r1_3, hx1⟩ := hx1
  obtain ⟨r1_4, hx1⟩ := hx1
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
  obtain ⟨w1_264, hx1⟩ := hx1
  obtain ⟨w1_268, hx1⟩ := hx1
  have K1_L := hx1
  rcases sv_tt4b FW E1 V1 hret hO s1 M0 fR1 r1_2 r1_18 r1_19 r1_20 r1_21 r1_22 r1_23 r1_24 r1_25 r1_26 r1_27 w1_264 w1_268 ((rd_in).restW x1_1) D0 with e | hx2
  · exact .inl (SvErrRet.pre (c1) (by rw [r1_3]) (by rw [r1_4])
      (fun x hx => (fR1 x hx).trans (fM x hx).symm) e)
  obtain ⟨tt4b_w264_2, hx2⟩ := hx2
  obtain ⟨tt4b_w268_2, hx2⟩ := hx2
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
  obtain ⟨w2_264, hx2⟩ := hx2
  obtain ⟨w2_268, hx2⟩ := hx2
  have K2_L := hx2
  exact .inr ⟨x1_0, tb8_1, x1_1, tt4b_w264_2, tt4b_w268_2, x2_0, x2_1, n2, c1.trans (c2), fR2, s2, E2, V2,
    by rw [r2_3, r1_3], by rw [r2_4, r1_4], r2_2, r2_18, r2_19, r2_20, r2_21, r2_22, r2_23, r2_24, r2_25, r2_26, r2_27, w2_264, w2_268, ((K1_L).trans K2_L).mono (by decide)⟩

end C3.RV32.Sv
