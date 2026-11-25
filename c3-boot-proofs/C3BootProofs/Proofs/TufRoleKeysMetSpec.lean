import C3BootProofs.Proofs.TufRoleKeysMet
import C3BootProofs.Models.TufLinkMet
import C3BootProofs.Proofs.TufRoleKeysBytes

/-!
# `tufRoleKeysMet` against `Spec/Tuf.lean`

`tufRoleKeysMet_spec` is `tufRoleKeysMet_correct` with the spec on the
other side: when `RoleKeys::met` returns `Ok(true)` on the keys that
`roleKeys` lists for a role, the message `encode md.signed`, and the
signatures array of `md`, `thresholdMet` holds for that role.

Memory holds each byte of a key ID and a key modulo 256, so the lift needs
the bytes of the listed key IDs and keys to be below 256. They are when the
delegator `dj` is parsed from memory (`rkBytes_of_roleKeys`).
-/

namespace C3.Json

open C3.RV32 (Word)

/-- Every byte of each key ID and key of `es` is below 256. -/
def RkBytes (es : List (Bytes × Option TufKey)) : Prop :=
  ∀ e ∈ es, (∀ x ∈ e.1, x < 256) ∧ ∀ k, e.2 = some k → ∀ x ∈ (keyTag k).2, x < 256

theorem tlmr_nb {l : Bytes} (h : ∀ x ∈ l, x < 256) : nb l = l := by
  unfold nb
  conv => rhs; rw [← List.map_id l]
  exact List.map_congr_left fun x hx => Nat.mod_eq_of_lt (h x hx)

theorem tlmr_nbE {es : List (Bytes × Option TufKey)} (h : RkBytes es) : (es.map rkTag).map nbE = es.map rkTag := by
  rw [List.map_map]
  refine List.map_congr_left fun e he => ?_
  obtain ⟨h1, h2⟩ := h e he
  rcases e with ⟨id, _ | k⟩
  · show (nb id, none) = (id, none)
    rw [tlmr_nb h1]
  · show (nb id, some ((keyTag k).1, nb (keyTag k).2)) = (id, some (keyTag k))
    rw [tlmr_nb h1, tlmr_nb (h2 k rfl)]

/-- The key IDs and keys that `roleKeys` lists for a role of a value whose
strings and keys are bytes below 256 are bytes below 256. -/
theorem rkBytes_of_roleKeys {dj : Json} {role : Bytes} {t : Nat} {es : List (Bytes × Option TufKey)}
    (hr : roleKeys dj role = some (t, es)) (hj : JBytes dj) : RkBytes es := by
  unfold roleKeys at hr
  obtain ⟨r, hr0, h⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨keys, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨items, hi, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ids, hids, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  obtain ⟨roles, h1, h2⟩ := Option.bind_eq_some_iff.mp hr0
  have hrj := trb_field (trb_field hj h1) h2
  obtain ⟨kj, h3, h4⟩ := Option.bind_eq_some_iff.mp hi
  have hid := trb_mapM (trb_asArr (trb_field hrj h3) h4) hids
  intro e he
  obtain ⟨id, hm, rfl⟩ := List.mem_map.mp he
  refine ⟨hid id hm, fun k hk => ?_⟩
  obtain ⟨_, -, hd⟩ := Option.bind_eq_some_iff.mp hk
  exact decodeKey_lt hd

/-- `rkBytes_of_roleKeys` for a delegator parsed from memory. -/
theorem rkBytes_of_mem {M : Word → BitVec 8} {D : Word} {L : Nat} {dj : Json} {role : Bytes} {t : Nat}
    {es : List (Bytes × Option TufKey)} (hr : roleKeys dj role = some (t, es))
    (hd : JVal true (C3.RV32.memBytes M D L) dj) : RkBytes es :=
  rkBytes_of_roleKeys hr (JVal_bytes hd C3.RV32.memBytes_mem_lt)

/-- `MetSound` on the listed keys of `roleKeys` gives `thresholdMet`. -/
theorem tlmr_thresholdMet {md : Meta} {dj : Json} {role a : Bytes} {t : Nat} {es : List (Bytes × Option TufKey)}
    (hr : roleKeys dj role = some (t, es)) (hB : RkBytes es)
    (hl : ∀ id, metLookup a id = some (md.sigs.lookup id))
    (h : MetSound a (encode md.signed) t ((es.map rkTag).map nbE)) : thresholdMet md dj role = some true := by
  rw [tlmr_nbE hB] at h
  rw [thresholdMet_roleKeys, hr]
  show some (metOf md t es) = some true
  rw [metOf_of_sound hl h]

end C3.Json

namespace C3.RV32

open C3.Image C3.Json

/-- `tufRoleKeysMet_correct` against the spec. The `RoleKeys` at `R` holds
the threshold `t` and the keys `es` that `roleKeys dj role` gives, where
`dj` is parsed from the bytes at `DP` in some memory `M`. The message is
`encode md.signed`, and the signatures array is the JSON value `sj` whose
items `sigPair` reads as `md.sigs`. When `RoleKeys::met` returns `Ok(true)`,
`thresholdMet md dj role` is `some true`. -/
theorem tufRoleKeysMet_spec (m : Machine) {retAddr s R A MP SP : Word} {ML SL t : Nat}
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
          (reg m' a0 = 0 → reg m' a1 ≠ 0 → thresholdMet md dj role = some true))) := by
  obtain ⟨m', st, q⟩ := tufRoleKeysMet_correct m hpc ha0 ha1 hsp hra hret hal hlo hhi hds hro hc halR hRw hSR hMw
    hML hSM hS0 hSw hSL hSS halA hSA hA0 hA4 hA8 hAC hR hw
  refine ⟨m', st, ?_⟩
  rcases q with h | ⟨hp, hM, hr, hS⟩
  · exact .inl h
  · refine .inr ⟨hp, hM, hr, fun h0 h1 => ?_⟩
    have hS := hS h0 h1
    rw [hmsg] at hS
    exact tlmr_thresholdMet hrk (rkBytes_of_mem hrk hdj) (metLookup_spec hsj hps) hS

end C3.RV32
