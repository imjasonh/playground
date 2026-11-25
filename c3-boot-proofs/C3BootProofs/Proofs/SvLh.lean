import C3BootProofs.Proofs.SvPv

/-!
# `sigstore::verify`: the leaf's hash and signature check

`sv_lh` runs from the intermediates search's hit at 0x95C to the result's
check at 0x980: it hashes the leaf's `tbsCertificate` with `sha384` into
offset 0x170 and checks the leaf's signature with `p384_verify_prehash` on
the issuer's key, which leaves the result in `a0` or panics.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

def svLh1 : List BInstr := [.lw a2 sp 0x84, .aluImm .add a0 sp 0x170, .alu .add a1 x0 (9 : Fin 32)]

theorem svLh1_end : blockEnd sigstoreVerifyCode 0x95C svLh1 = some 0x962 := by decide

def svLh2 : List BInstr :=
  [.lw a0 (23 : Fin 32) 0xFFFFFFF4, .aluImm .add a4 sp 0xF8, .aluImm .add a1 sp 0x170, .aluImm .add a2 x0 0x30,
    .aluImm .add a3 sp 0xC8]

theorem svLh2_end : blockEnd sigstoreVerifyCode 0x96A svLh2 = some 0x978 := by decide

set_option maxHeartbeats 16000000 in
set_option linter.unusedVariables false in
/-- **The leaf's hash and signature check**: from 0x95C to 0x980. -/
theorem sv_lh {B out bp x9 x20 x21 x22 x24 x26 q w84 pk : Word} {sr ss : Bytes} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0x95C (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_9 : reg n0 (9 : Fin 32) = x9)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = q)
    (g0_24 : reg n0 (24 : Fin 32) = x24)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (w0_84 : memLoad32 n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x84) = w84)
    (b0_c8 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xC8) = BitVec.ofNat 8 (sr.getD 0 0))
    (q0_c9 : ∀ j, j < 47 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xC9 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0))
    (q0_f8 : ∀ j, j < 48 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0xF8 + j)) = BitVec.ofNat 8 (ss.getD j 0))
    (HE0 : HfEnv M0) (RS : SvRoSep B) (lf_in : SvIn B x9 w84.toNat)
    (PE0 : PvEnv7 M0) (hpk : memLoad32 M0 (q + 0xFFFFFFF4) = pk) (pkp_in : SvIn B (q + 0xFFFFFFF4) 4)
    (apk : (q + 0xFFFFFFF4).toNat % 4 = 0) (pk_in : SvIn B pk 0x61)
    (side : ∀ M, PvSide M pk (B + 0x21A0 + BitVec.ofNat 32 0x170) 48 (B + 0x21A0 + BitVec.ofNat 32 0xC8)
      (B + 0x21A0 + BitVec.ofNat 32 0xF8)) :
    (¬ (∃ pv, SvPvRes M0 pk (B + 0x21A0 + BitVec.ofNat 32 0x170) 48 (sha384 (memBytes M0 x9 w84.toNat))
      (B + 0x21A0 + BitVec.ofNat 32 0xC8) (B + 0x21A0 + BitVec.ofNat 32 0xF8) sr ss (some pv)) ∧ Panics n0) ∨
    (∃ pv, SvPvRes M0 pk (B + 0x21A0 + BitVec.ofNat 32 0x170) 48 (sha384 (memBytes M0 x9 w84.toNat))
      (B + 0x21A0 + BitVec.ofNat 32 0xC8) (B + 0x21A0 + BitVec.ofNat 32 0xF8) sr ss (some pv) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0x980 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' a0 = pv ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = q ∧
        reg n' (24 : Fin 32) = x24 ∧
        reg n' (26 : Fin 32) = x26 ∧
        memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x170) 48 = sha384 (memBytes M0 x9 w84.toNat) ∧
        SvKeepL B n0.mem n'.mem [(0x170, 0x30)]) := by
  have F := sv_frW FW
  have hFh := F.hi
  obtain ⟨n1, c1, u1⟩ := s0.block svLh1 E0.self svLh1_end (by
    simp +decide only [svLh1, BlockOk, BInstr.ok, BInstr.run, upd, ↓reduceIte, and_true]
    rw [g0_2]; exact sv_al F (c := 0x84) (by decide) (by decide))
  have m1 : n1.mem = n0.mem := u1.mem
  have s1 : St n1.mem SV n1 0x962 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26] → reg n1 q = reg n0 q :=
    fun q hq => by rw [u1.regs, runBlock_reg _ _ _ q s0.zero (by revert hq; revert q; decide)]
  rw [m1] at s1
  obtain ⟨n2, c2, s2, sp2, k2, K2, dg2, f2⟩ := sv_sha384F (oc := 0x170) (p := x9) (nl := w84.toNat)
    FW E0 (HfEnv.sv FW RS HE0 fM) RS s1 sv_at_962 sv_at_966 (by decide) (by decide)
    (by rw [k1 sp (by decide), g0_2])
    (by rw [u1.regs]; simp +decide only [svLh1, runBlock, BInstr.run, upd, ↓reduceIte]; rw [g0_2]; rfl)
    (by rw [u1.regs]; simp +decide only [svLh1, runBlock, BInstr.run, upd, ↓reduceIte]
        simp only [aluEval]; rw [g0_9]; exact BitVec.zero_add _)
    (by rw [u1.regs]; simp +decide only [svLh1, runBlock, BInstr.run, upd, ↓reduceIte]; rw [g0_2]
        rw [show memLoad32 n0.mem (B + 0x21A0 + 0x84) = w84 from w0_84, ofNat_toNat_self])
    (by decide) (.inl lf_in)
  rw [sv_mb fM lf_in] at dg2
  have fR2 : ∀ x, SvR B x → n2.mem x = M0 x := fun x hx => (f2 x hx).trans (fM x hx)
  have r23 : reg n2 (23 : Fin 32) = q := by rw [k2 _ (by decide), k1 _ (by decide), g0_23]
  obtain ⟨n3, c3, u3⟩ := s2.block svLh2 (E0.fr F f2).self svLh2_end (by
    simp +decide only [svLh2, BlockOk, BInstr.ok, BInstr.run, upd, ↓reduceIte, and_true]
    rw [r23]; exact apk)
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem SV n3 0x978 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have k3 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n3 q = reg n2 q :=
    fun q hq => by rw [u3.regs, runBlock_reg _ _ _ q s2.zero (by revert hq; revert q; decide)]
  have hpk2 : memLoad32 n2.mem (q + 0xFFFFFFF4) = pk :=
    (memLoad32_congr fun j hj => (sv_pt fR2 pkp_in j hj).symm).symm.trans hpk
  have E3 : SvCode n3.mem := by rw [m3]; exact E0.fr F f2
  have fR3 : ∀ x, SvR B x → n3.mem x = M0 x := by rw [m3]; exact fR2
  have At : SvPvAt M0 n3.mem pk (B + 0x21A0 + BitVec.ofNat 32 0x170) 48 (sha384 (memBytes M0 x9 w84.toNat))
      (B + 0x21A0 + BitVec.ofNat 32 0xC8) (B + 0x21A0 + BitVec.ofNat 32 0xF8) sr ss := by
    rw [m3]
    exact ⟨sv_mb fR2 pk_in, sv_mbRo FW fR2 (.inr ⟨by decide, by decide⟩), dg2,
      memBytes_frame1 ((K2.b8 (by decide) (by decide)).trans b0_c8)
        fun j hj => (K2.range (s := 0xC9) (n := 47) (by decide) (by decide) j hj).trans (q0_c9 j hj),
      memBytes_frame fun j hj => (K2.range (s := 0xF8) (n := 48) (by decide) (by decide) j hj).trans (q0_f8 j hj)⟩
  rcases sv_pvF (pk := pk) (ph := B + 0x21A0 + BitVec.ofNat 32 0x170) (len := 48)
      (rp := B + 0x21A0 + BitVec.ofNat 32 0xC8) (sp' := B + 0x21A0 + BitVec.ofNat 32 0xF8)
      F E3 (PvEnv7.sv FW PE0 fR3) s3 sv_at_978 sv_at_97c (by decide) (by decide)
      (by rw [k3 sp (by decide), sp2])
      (by rw [u3.regs]; simp +decide only [svLh2, runBlock, BInstr.run, upd, ↓reduceIte]; rw [r23]; exact hpk2)
      (by rw [u3.regs]; simp +decide only [svLh2, runBlock, BInstr.run, upd, ↓reduceIte]; rw [sp2]; rfl)
      (by rw [u3.regs]; simp +decide only [svLh2, runBlock, BInstr.run, upd, ↓reduceIte])
      (by rw [u3.regs]; simp +decide only [svLh2, runBlock, BInstr.run, upd, ↓reduceIte]; rw [sp2]; rfl)
      (by rw [u3.regs]; simp +decide only [svLh2, runBlock, BInstr.run, upd, ↓reduceIte]; rw [sp2]; rfl)
      pk_in.pvSep (by have := pk_in.lo; omega) (sv_pvSep F (by decide)) (sv_pvSep F (by decide))
      (sv_pvSep F (by decide)) (by rw [sv_at F _ (by decide)]; omega) (side n3.mem) with
    ⟨hn, hp⟩ | ⟨pv, hv, n4, c4, s4, sp4, k4, a4, K4, f4⟩
  · refine .inl ⟨fun ⟨pv, hpv⟩ => ?_, Panics.of_steps (c1.trans (c2.trans c3)) hp⟩
    have := hpv _ At
    rw [hn] at this
    cases this
  · have rk : ∀ r : Fin 32, r.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26] → reg n4 r = reg n0 r :=
      fun r hr => by
        rw [k4 r (by revert hr; revert r; decide), k3 r (by revert hr; revert r; decide), k2 r hr,
          k1 r (by revert hr; revert r; decide)]
    refine .inr ⟨pv, hv ▸ SvPvRes.of At, n4, c1.trans (c2.trans (c3.trans c4)), s4, E3.fr F f4,
      V0.keepL (K2.trans (by rw [← m3]; exact K4)) (by decide),
      fun x hx => (f4 x hx).trans (fR3 x hx), sp4, rk _ (by decide), rk _ (by decide), a4,
      (rk _ (by decide)).trans g0_18, (rk _ (by decide)).trans g0_19, (rk _ (by decide)).trans g0_20,
      (rk _ (by decide)).trans g0_21, (rk _ (by decide)).trans g0_22, (rk _ (by decide)).trans g0_23,
      (rk _ (by decide)).trans g0_24, (rk _ (by decide)).trans g0_26, ?_,
      (K2.trans (by rw [← m3]; exact K4)).mono (by decide)⟩
    rw [← dg2]
    exact memBytes_congr fun j hj => by
      rw [add_ofNat_assoc, ← m3]; exact K4 _ (by omega) (fun _ h => by simp at h)

end C3.RV32.Sv
