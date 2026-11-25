import C3BootProofs.Proofs.TufRoleKeysMetSpec

/-!
# What a caller of `RoleKeys::met` branches on

`RoleKeys::met` returns a `Result<bool, TufError>` in `a0` (the tag) and
`a1` (the payload). A caller tests bit 0 of the tag, and then either the
payload's truth or its low byte, the error code it rejects with.
`tufRoleKeysMet_result` is `tufRoleKeysMet_spec` with what
`tufRoleKeysMet_ret` says of `a0` and `a1` in that form: with bit 0 of `a0`
clear, `a0` is zero and a nonzero `a1` means `thresholdMet` holds, and with
bit 0 set, the low byte of `a1` is below 0x27. `rmr_okBit` turns a nonzero
`a1` into its bit 0, for a caller that tests that bit.
-/

namespace C3.RV32

open C3.Image C3.Json

theorem rmr_okBit {a1 : Word} {P : Prop} (h : a1 ≠ 0 → P) : a1 &&& 1 ≠ 0 → P :=
  fun h1 => h fun h0 => h1 (by rw [h0]; rfl)

theorem rmr_tag {a0 : Word} (h : a0 = 0 ∨ a0 = 1) : (a0 &&& 1 = 0 → a0 = 0) ∧ (a0 &&& 1 ≠ 0 → a0 ≠ 0) := by
  rcases h with h | h <;> subst h <;> decide

/-- `tufRoleKeysMet_spec`, with what `RoleKeys::met` returns in `a0` and
`a1` in the form a caller branches on. -/
theorem tufRoleKeysMet_result (m : Machine) {retAddr s R A MP SP : Word} {ML SL t : Nat}
    {md : Meta} {dj sj : Json} {role : Bytes} {es : List (Bytes × Option TufKey)}
    {M : Word → BitVec 8} {DP : Word} {DL : Nat}
    (hpc : m.pc = TRM) (ha0 : reg m a0 = R) (ha1 : reg m a1 = A) (hsp : reg m sp = s + BitVec.ofNat 32 0x3920)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hal : s.toNat % 16 = 0)
    (hlo : 0x3FC80000 ≤ s.toNat) (hhi : s.toNat + 0x3920 ≤ 0x3FCE0000)
    (hds : Sep s 0x3920 (BitVec.ofNat 32 (img% dataWindowAddress)) (img% dataWindowSize))
    (hro : Sep s 0x3920 (BitVec.ofNat 32 (img% roWindowAddress)) (img% roWindowSize))
    (hc : ∀ M : Word → BitVec 8, (∀ x, Sep x 1 s 0x3920 → M x = m.mem x) → RmCode M)
    (halR : R.toNat % 4 = 0) (hRw : R.toNat + 0x540 ≤ 0x40000000) (hSR : Sep s 0x3920 R 0x540)
    (hMw : MP.toNat + ML ≤ 0x40000000) (hML : ML < 2 ^ 31) (hSM : Sep s 0x3920 MP ML)
    (hS0 : SP.toNat ≠ 0) (hSw : SP.toNat + SL ≤ 0x40000000) (hSL : SL < 2 ^ 31) (hSS : Sep s 0x3920 SP SL)
    (halA : A.toNat % 4 = 0) (hSA : Sep s 0x3920 A 16) (hA0 : memLoad32 m.mem A = MP)
    (hA4 : memLoad32 m.mem (A + BitVec.ofNat 32 4) = BitVec.ofNat 32 ML)
    (hA8 : memLoad32 m.mem (A + BitVec.ofNat 32 8) = SP)
    (hAC : memLoad32 m.mem (A + BitVec.ofNat 32 12) = BitVec.ofNat 32 SL)
    (hrk : roleKeys dj role = some (t, es)) (hdj : JVal true (memBytes M DP DL) dj)
    (hR : RkAt m.mem R t (es.map C3.Json.rkTag)) (hw : RkWf (es.map C3.Json.rkTag)) (hmsg : memBytes m.mem MP ML = encode md.signed)
    (hsj : JVal true (memBytes m.mem SP SL) sj) (hps : (sj.asArr >>= List.mapM sigPair) = some md.sigs) :
    ∃ m', Steps m m' ∧
      (rmH m'.pc m'.mem (reg m') ∨
        (m'.pc = retAddr ∧ (∀ x, Sep x 1 s 0x3920 → m'.mem x = m.mem x) ∧ (∀ r, r ∉ jClob → reg m' r = reg m r) ∧
          (reg m' a0 &&& 1 = 0 → reg m' a0 = 0 ∧ (reg m' a1 ≠ 0 → thresholdMet md dj role = some true)) ∧
          (reg m' a0 &&& 1 ≠ 0 → (reg m' a1 &&& 0xFF).toNat < 0x27))) := by
  obtain ⟨m', st, q⟩ := tufRoleKeysMet_ret m hpc ha0 ha1 hsp hra hret hal hlo hhi hds hro hc halR hRw hSR hMw
    hML hSM hS0 hSw hSL hSS halA hSA hA0 hA4 hA8 hAC hR hw
  refine ⟨m', st, ?_⟩
  rcases q with h | ⟨hp, hM, hr, hS, h01, hE⟩
  · exact .inl h
  · obtain ⟨t0, t1⟩ := rmr_tag h01
    refine .inr ⟨hp, hM, hr, fun hb => ⟨t0 hb, fun h1 => ?_⟩, fun hb => hE (t1 hb)⟩
    have hS := hS (t0 hb) h1
    rw [hmsg] at hS
    exact tlmr_thresholdMet hrk (rkBytes_of_mem hrk hdj) (metLookup_spec hsj hps) hS

end C3.RV32
