import C3BootProofs.Proofs.AcceptSpecEnd

/-!
# `boot_main`'s first closure: from 0x1816 to the return

The bundle stage, then the last stage: what holds at 0x1816 (`AcsAt1816`)
ends the closure.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.BootMainContract

/-- **At 0x1816**: what the bundle and the last stage need, with `s5`, `s9`,
and `s11` holding what the image stage left. `sp + 0x20` holds a time no
later than the expiry `ex` that `verifyTuf` gives. -/
structure AcsAt1816 (X : AcsCtx) (mf : Manifest) (header : ImageHeader) (parts : TufParts) (ver ex : Nat)
    (fs : List FulcioKey) (ls : List LogKey) (ts : List TsaKey) (n : Machine) : Prop where
  st : St n.mem AC n 0x1816 (reg n)
  inv : AcInv X.B X.Bf X.g X.t X.v X.M0 n
  img : AcsImg X mf header n.mem (reg n (21 : Fin 32)) (reg n (25 : Fin 32)) (reg n (27 : Fin 32))
  tuf : decodeTufParts (flashBytes X.flash (acBase X.slot + mf.tuf.offset) mf.tuf.length) = some parts
  ver : verifyTuf X.pinned parts = some (ver, ex)
  root : extractTrustedRoot parts.trustedRoot X.policy = some ⟨fs, ls, ts, X.policy⟩
  keys : ∃ fp : Word, fp.toNat ≤ X.Bf.toNat + 0xB840 ∧ AceKeysIn X.Bf fp n.mem (acSlot X.B 0xDF3) fs ls ts
  pol : memBytes n.mem (acSlot X.B 0xDD0) 0x23 = memBytes X.M0 (img% acPolicyAddress) 0x23
  exp : ∃ e, e ≤ ex ∧ Sv.SvU64At n.mem (acSlot X.B 0x20) e
  bf : memLoad32 n.mem (acSlot X.B 0x34) = X.Bf
  len : memLoad32 n.mem (acSlot X.B 0x38) = BitVec.ofNat 32 mf.bundle.length
  hL : mf.bundle.length ≤ 0x4000
  bundle : memBytes n.mem X.Bf mf.bundle.length =
    flashBytes X.flash (acBase X.slot + mf.bundle.offset) mf.bundle.length
  res : memLoad32 n.mem (acSlot X.B 0x40) = X.r
  a0 : reg n a0 = acSlot X.B 0x1875
  a1 : reg n a1 = acSlot X.B 0xDD0
  a2 : reg n a2 = 0x423
  ra : reg n ra = AC + BitVec.ofNat 32 0x1812 + 0x15000

theorem acs_mb_pt {M M' : Word → BitVec 8} {a b : Word} {n : Nat} (h : memBytes M a n = memBytes M' b n)
    {i : Nat} (hi : i < n) : M (a + BitVec.ofNat 32 i) = M' (b + BitVec.ofNat 32 i) := by
  have := congrArg (fun l => l[i]?) h
  simp only [memBytes, List.getElem?_map, List.getElem?_range hi, Option.map_some] at this
  exact BitVec.eq_of_toNat_eq (Option.some.inj this)

theorem acs_u64 {M M' : Word → BitVec 8} {a : Word} {x : Nat} (h : Sv.SvU64At M a x)
    (e1 : memLoad32 M' a = memLoad32 M a) (e2 : memLoad32 M' (a + 4) = memLoad32 M (a + 4)) :
    Sv.SvU64At M' a x :=
  ⟨h.1, e1.trans h.2.1, e2.trans h.2.2⟩

theorem acs_bunOut {B : Word} {c l : Nat} (hW : ∀ p ∈ acbW, p.1 + p.2 ≤ c ∨ c + l ≤ p.1)
    (hc : c + l ≤ 0x5A70) {j : Nat} (hj : j < l) : AcbOut acbW B (B + BitVec.ofNat 32 (c + j)) :=
  acb_at hW (by omega) (by decide) hj

/-- The bundle stage doesn't write the frame slots the result is made from. -/
theorem acs_bunWin {B : Word} {k : Nat} (hk : AcsWin k) : AcbOut acbW B (acSlot B k) := by
  rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := acs_bunOut (B := B) (c := 0x3A90) (l := 8) (by decide) (by decide) (j := k - 0x40) (by omega)
    rwa [show 0x3A90 + (k - 0x40) = 0x3A50 + k by omega] at this
  · have := acs_bunOut (B := B) (c := 0x3B58) (l := 0x13C) (by decide) (by decide) (j := k - 0x108) (by omega)
    rwa [show 0x3B58 + (k - 0x108) = 0x3A50 + k by omega] at this

/-- The trust root's struct is outside `sigstore::verify`'s stack. -/
theorem acs_rootIn {B : Word} (F : Fr B 0x5A70) : Sv.SvIn (B + 0x13F0) (acSlot B 0x1870) 0x428 := by
  have e1 : (acSlot B 0x1870).toNat = B.toNat + 0x52C0 := F.at _ (by decide)
  have := F.lo; have := F.hi
  have e2 : (B + 0x13F0 + 0xFFFFEA70).toNat = B.toNat - 0x1A0 := by
    rw [BitVec.toNat_add, BitVec.toNat_add]; simp only [BitVec.reduceToNat]; omega
  exact ⟨(sep_of_le (by rw [e2, e1]; omega) (by rw [e1]; omega)).symm, by rw [e1]; omega, by rw [e1]; omega⟩

/-- **From 0x1816**: the closure panics or returns with `AcsRes`. -/
theorem acs_bun (hFx : AcsFinishBad) {X : AcsCtx} (ok : X.Ok) {n : Machine}
    {mf : Manifest} {header : ImageHeader} {parts : TufParts} {ver ex : Nat} {fs : List FulcioKey}
    {ls : List LogKey} {ts : List TsaKey} (S : AcsAt1816 X mf header parts ver ex fs ls ts n) : X.End n := by
  have E := ok.envsAt S.inv
  have M0E := ok.env X.M0 fun _ _ => rfl
  have sv : Sv.SvIn (X.B + 0x13F0) X.Bf 0x4000 := by
    have h := ok.svBf.sub (c := 0) (l := 0x4000) (by decide)
    rwa [add_ofNat_zero] at h
  refine acs_stage S.inv (acBundleStage n X.B X.Bf X.g X.t X.r X.v X.M0 mf.bundle.length E.ac E.bun ok.F ok.sB S.st S.inv
    S.res ⟨S.bf, S.len, S.hL, sv, S.a0, S.a1, S.a2, S.ra⟩) (fun _ => ok.fail) fun n' I' hpc ⟨P, rk⟩ => ?_
  obtain ⟨b, hbd, hbAt⟩ := P.bundle
  rw [S.bundle] at hbd
  have A : AcsImg X mf header n'.mem (reg n' (21 : Fin 32)) (reg n' (25 : Fin 32)) (reg n' (27 : Fin 32)) := by
    rw [rk 21 (by decide), rk 25 (by decide), rk 27 (by decide)]
    exact S.img.keep fun k hk => P.keep _ (acs_bunWin hk)
  obtain ⟨fp, hfp, hk⟩ := S.keys
  have e28 : acSlot X.B 0x1870 + 0x28 = acSlot X.B 0x1898 := acf_slot_add X.B 0x1870 0x28
  have hk' : AceKeysIn X.Bf fp n'.mem (acSlot X.B 0x1870 + 0x28) fs ls ts := by
    rw [e28]
    refine hk.move (fun c hc => ?_)
      (fun y h1 h2 => P.keep y (acb_stack (by decide) (ok.inBf (by omega) (by rw [show acBufLen = 0xB954 from rfl]; omega))))
    have := acs_mb_pt P.root (i := 0x23 + c) (by omega)
    rw [acf_slot_add, acf_slot_add] at this ⊢
    rwa [show 0x1875 + (0x23 + c) = 0x1898 + c by omega, show 0xDD0 + (0x23 + c) = 0xDF3 + c by omega] at this
  obtain ⟨hf, hl, ht⟩ := hk'.sv ok.svBf hfp
  have hpol : memBytes n'.mem (acSlot X.B 0x1870 + 5) 0x23 = memBytes X.M0 (img% acPolicyAddress) 0x23 := by
    rw [← S.pol]
    refine ace_memBytes_ext fun i hi => ?_
    rw [show acSlot X.B 0x1870 + 5 = acSlot X.B 0x1875 from acf_slot_add X.B 0x1870 5]
    exact acs_mb_pt P.root (by omega)
  have Pol := M0E.pol X.B (acSlot X.B 0x1870) n'.mem ok.blo ok.bhi
    (fun x hx => I'.out x (ok.outRam hx).1 (ok.outRam hx).2) P.rootHdr.1
    (by rw [show acSlot X.B 0x1870 + 4 = acSlot X.B 0x1874 from acf_slot_add X.B 0x1870 4]; exact P.rootHdr.2)
    hpol
  have hW : ∀ c, c + 4 ≤ 0x3A78 → 0x3A70 ≤ c → memLoad32 n'.mem (X.B + BitVec.ofNat 32 c) =
      memLoad32 n.mem (X.B + BitVec.ofNat 32 c) := fun c h1 h2 =>
    acb_ld P.keep (fun p hp => by
      simp only [acbW, acbV, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact .inr (by omega)
      · exact .inl (by omega)
      · exact .inl (by omega)
      all_goals exact .inr (by omega)) (by omega) (by decide)
  obtain ⟨e, hle, he⟩ := S.exp
  have hexp : Sv.SvU64At n'.mem (acSlot X.B 0x20) e :=
    acs_u64 he (hW 0x3A70 (by decide) (by decide))
      (by rw [show acSlot X.B 0x20 + 4 = X.B + BitVec.ofNat 32 0x3A74 from acf_slot_add X.B 0x20 4]
          exact hW 0x3A74 (by decide) (by decide))
  have hres : memLoad32 n'.mem (acSlot X.B 0x40) = X.r := by
    rw [← S.res]
    exact memLoad32_congr fun j hj => by rw [acf_slot_add]; exact P.keep _ (acs_bunWin (.inl ⟨by omega, by omega⟩))
  exact acs_fin hFx ok I'
    ⟨⟨hpc, rfl, fun _ => rfl⟩, P.ra, P.a0, P.a1, P.a2, P.a3, hbAt,
      ⟨acb_al ok.F (0x3A50 + 0x1870) (by decide) (by decide), acs_rootIn ok.F, Pol.issuer, Pol.buildSignerUri,
        Pol.repositoryId, Pol.ownerId, Pol.trigger, hf, hl, ht⟩,
      hexp, hres, ok.svRo, ok.rS, ok.ra, ok.rhi⟩ hle
    A S.tuf S.ver S.root hbd

end C3.RV32.Ac
