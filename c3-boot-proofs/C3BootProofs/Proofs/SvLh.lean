import C3BootProofs.Proofs.SvPvModel

/-!
# `sigstore::verify`: the leaf's hash and signature check, as a stage

`sv_lhash` and `sv_lpv` state what they need and leave in their own terms.
`sv_lh` restates the two in the form the composed stages use, so a segment
can run from the intermediates search's end at 0xB56 to the policy check at
0xDE6.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxHeartbeats 4000000 in
set_option linter.unusedVariables false in
/-- **The leaf's hash and signature check**: from 0xB56 to 0xDE6, `sv_lhash`
hashes the leaf's `tbsCertificate` with SHA-384 into 0x1020, and `sv_lpv`
checks the leaf's signature with the issuer's key, which leaves the result in
`a0` or panics. -/
theorem sv_lh {B out bp x9 x21 x26 q w8c pk : Word} {sr ss : Bytes} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3830) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0xB56 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_9 : reg n0 (9 : Fin 32) = x9)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (g0_27 : reg n0 (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (w0_7c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = q)
    (w0_8c : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = w8c)
    (b0_d0 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xD0) = BitVec.ofNat 8 (sr.getD 0 0))
    (q0_d1 : ∀ j, j < 47 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xD1 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0))
    (q0_100 : ∀ j, j < 48 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x100 + j)) = BitVec.ofNat 8 (ss.getD j 0))
    (SH0 : SvShaCode M0) (KS : SvKSep B) (lf_in : SvIn B x9 w8c.toNat)
    (PE0 : PvEnv7 M0) (hpk : memLoad32 M0 (q + 0xFFFFFFF4) = pk) (pkp_in : SvIn B (q + 0xFFFFFFF4) 4)
    (apk : (q + 0xFFFFFFF4).toNat % 4 = 0) (pk_in : SvIn B pk 0x61)
    (side : ∀ M, PvSide M pk (B + 0x21A0 + BitVec.ofNat 32 0x1020) 48 (B + 0x21A0 + BitVec.ofNat 32 0xD0)
      (B + 0x21A0 + BitVec.ofNat 32 0x100)) :
    (¬ (∃ pv, SvPvRes B M0 pk (sha384 (memBytes M0 x9 w8c.toNat)) sr ss (some pv)) ∧ Panics n0) ∨
    (∃ pv, SvPvRes B M0 pk (sha384 (memBytes M0 x9 w8c.toNat)) sr ss (some pv) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0xDE6 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' a0 = pv ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (26 : Fin 32) = x26 ∧
        reg n' (27 : Fin 32) = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧
        memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 48 = sha384 (memBytes M0 x9 w8c.toNat) ∧
        SvKeepL B n0.mem n'.mem [(0x74, 0x8), (0x420, 0xD0), (0xA20, 0xD0), (0x1020, 0x40), (0x1480, 0x30)]) := by
  have SH : SvShaCode n0.mem := SvShaCode.sv F KS SH0 fM
  obtain ⟨n1, c1, s1, sp1, rk1, sh1, K1, fr1⟩ :=
    sv_lhash F E0 SH KS s0 g0_2 g0_9 g0_27 (w0_8c.trans (ofNat_toNat_self _).symm) lf_in
  rw [sv_mb fM lf_in] at sh1
  have fR1 : ∀ x, SvR B x → n1.mem x = M0 x := fun x hx => (fr1 x hx).trans (fM x hx)
  have E1 : SvCode n1.mem := E0.fr F fr1
  have V1 : SvSaves B n1.mem v := V0.keepL K1 (by decide)
  have w1_7c : memLoad32 n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x7C) = q :=
    (K1.w32 (by decide) (by decide)).trans w0_7c
  have hpk1 : memLoad32 n1.mem (q + 0xFFFFFFF4) = pk :=
    (memLoad32_congr fun j hj => (sv_pt fR1 pkp_in j hj).symm).symm.trans hpk
  have At : SvPvAt B M0 n1.mem pk (sha384 (memBytes M0 x9 w8c.toNat)) sr ss := by
    refine ⟨sv_mb fR1 pk_in, sv_mbRo F fR1 (.inr ⟨by decide, by decide⟩), sh1,
      memBytes_svBytes fun j hj => ?_, memBytes_svBytes fun j hj => ?_⟩
    · rw [add_ofNat_assoc]
      rcases j with _ | i
      · exact (K1.b8 (by decide) (by decide)).trans b0_d0
      · rw [show 0xD0 + (i + 1) = 0xD1 + i by omega, show i + 1 = 1 + i by omega]
        exact (K1.range (s := 0xD1) (n := 47) (by decide) (by decide) i (by omega)).trans (q0_d1 i (by omega))
    · rw [add_ofNat_assoc]
      exact (K1.range (s := 0x100) (n := 48) (by decide) (by decide) j hj).trans (q0_100 j hj)
  rcases sv_lpv F E1 (PvEnv7.sv F PE0 fR1) s1 sp1 w1_7c hpk1 apk pk_in (side n1.mem) with
    ⟨hn, pn⟩ | ⟨pv, hv, n2, c2, s2, sp2, rk2, a2, K2, fr2⟩
  · refine .inl ⟨fun ⟨pv, hpv⟩ => ?_, Panics.of_steps c1 pn⟩
    have := hpv _ At
    rw [hn] at this
    cases this
  · refine .inr ⟨pv, hv ▸ SvPvRes.of At, n2, c1.trans c2, s2, E1.fr F fr2, V1.keepL K2 (by decide),
      fun x hx => (fr2 x hx).trans (fR1 x hx), sp2, (rk2 _ (by decide)).trans (rk1 _ (by decide)),
      (rk2 _ (by decide)).trans (rk1 _ (by decide)), a2,
      (rk2 _ (by decide)).trans ((rk1 _ (by decide)).trans g0_18),
      (rk2 _ (by decide)).trans ((rk1 _ (by decide)).trans g0_19),
      (rk2 _ (by decide)).trans ((rk1 _ (by decide)).trans g0_21),
      (rk2 _ (by decide)).trans ((rk1 _ (by decide)).trans g0_26),
      (rk2 _ (by decide)).trans ((rk1 _ (by decide)).trans g0_27), ?_, (K1.trans K2).mono (by decide)⟩
    rw [← sh1]
    exact memBytes_congr fun j hj => by
      rw [add_ofNat_assoc]; exact K2.range (s := 0x1020) (n := 48) (by decide) (by decide) j hj

end C3.RV32.Sv
