import C3BootProofs.Proofs.SvPvModel
import C3BootProofs.Proofs.SvTpv

/-!
# `sigstore::verify`: the timestamp's signature check, as a stage

`sv_tp` restates `sv_tpv` in the form the composed stages use, from the
timestamp's signature at 0x2B16 to the checkpoint at 0x2B34.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxHeartbeats 4000000 in
set_option linter.unusedVariables false in
/-- **The timestamp's signature check**: from 0x2B16 to 0x2B34,
`p384_verify_prehash` checks the timestamp's signature on the digest at
0x420 with the TSA's key, which leaves the result in `a0` or panics. -/
theorem sv_tp {B out bp x8 x9 x20 x21 x22 x24 x25 x26 q pk : Word} {h sr ss : Bytes} {v : Nat → Word}
    {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x2B16 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_8 : reg n0 (8 : Fin 32) = x8)
    (g0_9 : reg n0 (9 : Fin 32) = x9)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40)
    (g0_24 : reg n0 (24 : Fin 32) = x24)
    (g0_25 : reg n0 (25 : Fin 32) = x25)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_74 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = q)
    (mb0_420 : memBytes n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 = h)
    (b0_a40 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xA40) = BitVec.ofNat 8 (sr.getD 0 0))
    (q0_a41 : ∀ j, j < 47 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA41 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0))
    (q0_a70 : ∀ j, j < 48 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA70 + j)) = BitVec.ofNat 8 (ss.getD j 0))
    (PE0 : PvEnv7 M0) (hpk : memLoad32 M0 (q + 0x18) = pk) (pkp_in : SvIn B (q + 0x18) 4)
    (apk : (q + 0x18).toNat % 4 = 0) (pk_in : SvIn B pk 0x61)
    (side : ∀ M, PvSide M pk (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 (B + 0x21A0 + BitVec.ofNat 32 0xA40)
      (B + 0x21A0 + BitVec.ofNat 32 0xA70)) :
    (¬ (∃ pv, SvPvRes M0 pk (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 h (B + 0x21A0 + BitVec.ofNat 32 0xA40) (B + 0x21A0 + BitVec.ofNat 32 0xA70) sr ss (some pv)) ∧ Panics n0) ∨
    (∃ pv, SvPvRes M0 pk (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 h (B + 0x21A0 + BitVec.ofNat 32 0xA40) (B + 0x21A0 + BitVec.ofNat 32 0xA70) sr ss (some pv) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x2B34 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (8 : Fin 32) = x8 ∧
        reg n' (9 : Fin 32) = x9 ∧
        reg n' a0 = pv ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA40 ∧
        reg n' (24 : Fin 32) = x24 ∧
        reg n' (25 : Fin 32) = x25 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        SvKeepL B n0.mem n'.mem []) := by
  have hpk0 : memLoad32 n0.mem (q + 0x18) = pk :=
    (memLoad32_congr fun j hj => (sv_pt fM pkp_in j hj).symm).symm.trans hpk
  have At : SvPvAt M0 n0.mem pk (B + 0x21A0 + BitVec.ofNat 32 0x420) 32 h (B + 0x21A0 + BitVec.ofNat 32 0xA40)
      (B + 0x21A0 + BitVec.ofNat 32 0xA70) sr ss :=
    ⟨sv_mb fM pk_in, sv_mbRo F fM (.inr ⟨by decide, by decide⟩), mb0_420, memBytes_frame1 b0_a40 q0_a41,
      memBytes_frame q0_a70⟩
  rcases sv_tpv F E0 (PvEnv7.sv F PE0 fM) s0 g0_2 g0_23 w0_74 hpk0 apk pk_in (side n0.mem) with
    ⟨hn, pn⟩ | ⟨pv, hv, n1, c1, s1, sp1, rk1, a1, K1, fr1⟩
  · refine .inl ⟨fun ⟨pv, hpv⟩ => ?_, pn⟩
    have := hpv _ At
    rw [hn] at this
    cases this
  · exact .inr ⟨pv, hv ▸ SvPvRes.of At, n1, c1, s1, E0.fr F fr1, V0.keepL K1 (by decide),
      fun x hx => (fr1 x hx).trans (fM x hx), sp1, rk1 _ (by decide), rk1 _ (by decide),
      (rk1 _ (by decide)).trans g0_8, (rk1 _ (by decide)).trans g0_9, a1,
      (rk1 _ (by decide)).trans g0_18, (rk1 _ (by decide)).trans g0_19, (rk1 _ (by decide)).trans g0_20,
      (rk1 _ (by decide)).trans g0_21, (rk1 _ (by decide)).trans g0_22, (rk1 _ (by decide)).trans g0_23,
      (rk1 _ (by decide)).trans g0_24, (rk1 _ (by decide)).trans g0_25, (rk1 _ (by decide)).trans g0_26,
      (rk1 _ (by decide)).trans g0_27, K1⟩

end C3.RV32.Sv
