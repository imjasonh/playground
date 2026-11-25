import C3BootProofs.Proofs.Pv384Main
import C3BootProofs.Models.EcdsaWnaf
import C3BootProofs.Models.SafegcdP384

/-!
# `p384_verify_prehash` doesn't panic

`p384VerifyPrehash_correct` panics exactly when `pvModel` is `none`. That
happens in two places:

* At 0x11D0, `NonZeroScalar::invert_vartime`'s `unwrap` (elliptic-curve
  0.14.3, `src/scalar/nonzero.rs:229`) when the inversion of `s` ends with
  `|f| ≠ 1`.
* At 0x11E0, the bounds check on the main loop's table index, when a wNAF
  digit byte is not one that `DigOk` allows.

The digits always pass (`pvnp_loop`). The inversion's `f` ends at ±1 when
its 886 divsteps bring `g` to zero, which is safegcd's bound on the number
of divsteps (`P384InvBound`). Given that bound, `pvModel` is never `none`
(`pvnp_model`), so `p384VerifyPrehash_correct_np` drops the panic.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.Models

/-- **Safegcd's divstep bound** for `p384_verify_prehash`'s inversion of
`s`: for every `x` in `[1, n)`, `ivLoop`'s 886 divsteps from `f = n` and
`g = x` end with `|f| = 1`. crypto-bigint 0.7.11 runs
`(45907·384 + 30179) / 19929 = 886` divsteps (`safegcd.rs`, `iterations`),
which is the bound from <https://github.com/sipa/safegcd-bounds>. That
bound is checked by computer search, not proved here. -/
def P384InvBound : Prop :=
  ∀ x : Nat, 0 < x → x < n384 → (ivLoop 0x376 (ivInit x)).f.natAbs = 1

theorem pvnp_add {T : Nat → Pt} {acc : Pt} {b : Nat} (h : DigOk b) : ∃ o, mlAdd T acc b = some o := by
  unfold mlAdd
  rcases h with rfl | ⟨_, h2⟩ | ⟨_, h2, h3⟩
  · exact ⟨_, rfl⟩
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]; exact ⟨_, rfl⟩
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; exact ⟨_, rfl⟩

theorem pvnp_pair {T : Nat → Pt} {D : List Nat} {k : Nat} (st : Pt × Bool) (h : DigOk (D.getD k 0)) :
    ∃ st', mlPair T D k st = some st' := by
  unfold mlPair
  by_cases hk : 0x181 < k + 1
  · rw [ite_eq_left hk]; exact ⟨_, rfl⟩
  · rw [ite_eq_right hk]
    obtain ⟨o, e⟩ := pvnp_add (T := T) (acc := st.1) h
    rw [e]
    cases o
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- The main loop never fails on digits that `DigOk` allows. -/
theorem pvnp_loop {T0 T1 : Nat → Pt} {D0 D1 : List Nat} (h0 : ∀ k, DigOk (D0.getD k 0))
    (h1 : ∀ k, DigOk (D1.getD k 0)) : ∀ k st, ∃ st', mlLoop T0 T1 D0 D1 k st = some st'
  | 0, st => ⟨st, rfl⟩
  | k + 1, st => by
    obtain ⟨a, ea⟩ := pvnp_pair (T := T0) (if st.2 then ptDblT st.1 else st.1, st.2) (h0 k)
    obtain ⟨b, eb⟩ := pvnp_pair (T := T1) a (h1 k)
    obtain ⟨c, ec⟩ := pvnp_loop h0 h1 k b
    exact ⟨c, by rw [mlLoop, mlIter, ea, Option.bind_some, eb, Option.bind_some, ec]⟩

theorem pvnp_dig (U : Nat) : ∀ k, DigOk ((pvD U).getD k 0) :=
  wnafBytes_digOk (wnafGo_dig _ _ _ (Nat.zero_le _)) 0x181

theorem pvnp_sum (QX QY RM ZM W : Nat) : ∃ P, pvSum QX QY RM ZM W = some P := by
  unfold pvSum mlRun
  by_cases hL : max (pvL (n3fm ZM W)) (pvL (n3fm RM W)) = 0
  · rw [ite_eq_left hL]; exact ⟨_, rfl⟩
  · rw [ite_eq_right hL]
    obtain ⟨c, ec⟩ := pvnp_loop (T0 := tblPt pvG) (T1 := tblPt (QX, QY, dataVal p384MontOneData 0 12))
      (pvnp_dig _) (pvnp_dig _) (max (pvL (n3fm ZM W)) (pvL (n3fm RM W))) (idPt, false)
    rw [ec]; exact ⟨_, rfl⟩

set_option exponentiation.threshold 400 in
/-- `s` in Montgomery form is nonzero: `n` is odd, so it divides `s·2³⁸⁴`
only when it divides `s`. -/
theorem pvnp_mont {s : Nat} (h0 : s ≠ 0) (h1 : s < n384) : 0 < s * 2 ^ 384 % n384 := by
  apply Nat.pos_of_ne_zero
  intro h
  have hc : Nat.Coprime n384 (2 ^ 384) := Nat.Coprime.pow_right _ (by unfold n384; decide)
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (hc.dvd_of_dvd_mul_right (Nat.dvd_of_mod_eq_zero h))
  omega

/-- Given safegcd's bound, `pvModel` is never `none`. -/
theorem pvnp_model (hB : P384InvBound) (M : Word → BitVec 8) (pk ph : Word) (len : Nat) (rp sp' : Word) :
    ∃ v, pvModel M pk ph len rp sp' = some v := by
  unfold pvModel
  by_cases hc : PvCk1 M pk rp sp' ∧ PvCk2 M rp sp'
  · have hW : (pvW M sp').f.natAbs = 1 :=
      hB _ (pvnp_mont hc.2.2.2.2 hc.2.2.1) (Nat.mod_lt _ (by unfold n384; decide))
    rw [ite_eq_left hc, ite_eq_left hW]
    obtain ⟨P, hP⟩ := pvnp_sum (Fs.fsVal M pk 1 * 2 ^ 384 % p384) (Fs.fsVal M pk 0x31 * 2 ^ 384 % p384)
      (beNat (memBytes M rp 48) * 2 ^ 384 % n384) (beNat (memBytes M ph (min len 48)) * 2 ^ 384 % n384)
      (pvInv (pvW M sp'))
    rw [pvSumM, hP]; exact ⟨_, rfl⟩
  · rw [ite_eq_right hc]; exact ⟨0, rfl⟩

set_option maxHeartbeats 4000000 in
/-- **`p384_verify_prehash` without the panic**: given safegcd's divstep
bound, it returns `pvModel` of the inputs. It returns with `sp`, `ra`, `s0`
to `s11`, `gp`, and `tp` as they were, and changes no memory outside its
frame. -/
theorem p384VerifyPrehash_correct_np (m : Machine) {B pk ph rp sp' retAddr : Word} {len : Nat}
    (E : PvEnv7 m.mem) (F : Fr B 0x21A0) (hpc : m.pc = PV) (hsp : reg m sp = B + 0x21A0)
    (ha0 : reg m a0 = pk) (ha1 : reg m a1 = ph) (ha2 : reg m a2 = BitVec.ofNat 32 len) (ha3 : reg m a3 = rp)
    (ha4 : reg m a4 = sp') (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (sPK : Sep pk 0x61 (B + 0xFFFFFE60) 0x2340) (hPK : pk.toNat + 0x61 ≤ 0x40000000)
    (sR : Sep rp 48 (B + 0xFFFFFE60) 0x2340) (sS : Sep sp' 48 (B + 0xFFFFFE60) 0x2340)
    (sph : Sep ph len (B + 0xFFFFFE60) 0x2340) (hph : ph.toNat + len < 2 ^ 32) (hB : P384InvBound) :
    ∃ v, pvModel m.mem pk ph len rp sp' = some v ∧
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = B + 0x21A0 ∧
        (∀ k, k < 13 → reg m' (savedReg k) = reg m (savedReg k)) ∧
        reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧ reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧ reg m' a0 = v ∧
        PvOut B m.mem m'.mem := by
  rcases p384VerifyPrehash_correct m E F hpc hsp ha0 ha1 ha2 ha3 ha4 hra hret sPK hPK sR sS sph hph
      (Safegcd.pvSide_holds _ _ _ _ _ _) with ⟨hn, -⟩ | h
  · obtain ⟨v, hv⟩ := pvnp_model hB m.mem pk ph len rp sp'
    rw [hv] at hn; cases hn
  · exact h

end C3.RV32.Pv
