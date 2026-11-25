import C3BootProofs.Proofs.AcceptSpecLib

/-!
# `boot_main`'s first closure: from 0x1A46 to the return

What the image stage leaves for the result (`AcsImg`), and the last stage's
step to the closure's return: `sigstore::verify` and the result.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.BootMainContract

/-- The frame offsets that hold what the result is made from: the result
pointer and the image's flash address, the digest, and the copied header
bytes. -/
def AcsWin (k : Nat) : Prop := 0x40 ≤ k ∧ k < 0x48 ∨ 0x108 ≤ k ∧ k < 0x244

/-- **What the image stage leaves for the result**, in memory `M` with
`s5`, `s9`, and `s11` at `x21`, `x25`, and `x27`: the manifest and the
header decode, the security version is at least the level, and the result
`image::parse` wrote, in memory `Mh`, is where the result's bytes come
from. -/
structure AcsImg (X : AcsCtx) (mf : Manifest) (header : ImageHeader) (M : Word → BitVec 8) (x21 x25 x27 : Word) :
    Prop where
  man : decodeManifest (flashBytes X.flash (acBase X.slot) 32) = some mf
  dec : decodeImageHeader (flashBytes X.flash (acBase X.slot + mf.image.offset) mf.image.length)
    mf.image.length = some header
  lev : X.level.toNat ≤ header.securityVersion
  r27 : x27 = BitVec.ofNat 32 header.securityVersion
  out : ∃ (Mh : Word → BitVec 8) (sv : BitVec 8) (entry : Word) (cnt : BitVec 8) (segs : List SegW),
    header = toHdr (BitVec.ofNat 32 mf.image.length) (sv, entry, cnt, segs) ∧
    OutOk Mh (acSlot X.B 0x1870) sv entry cnt (BitVec.ofNat 32 mf.image.length) segs ∧
    segs.length = cnt.toNat ∧ 0 < segs.length ∧ (∀ s ∈ segs, (3 : BitVec 8).ult s.kind = false) ∧
    x21 = (Mh (acSlot X.B 0x1870)).zeroExtend 32 ∧ x25 = (Mh (acSlot X.B 0x187C)).zeroExtend 32 ∧
    (∀ i, i < 11 → M (acSlot X.B (0x238 + i)) = Mh (acSlot X.B (0x1871 + i))) ∧
    (∀ i, i < 0xFF → M (acSlot X.B (0x139 + i)) = Mh (acSlot X.B (0x187D + i)))
  addr : memLoad32 M (acSlot X.B 0x44) = BitVec.ofNat 32 (acBase X.slot + mf.image.offset)
  digest : memBytes M (acSlot X.B 0x108) 32 =
    sha256 (flashBytes X.flash (acBase X.slot + mf.image.offset) mf.image.length)

/-- `AcsImg` holds in memory that agrees on `AcsWin`. -/
theorem AcsImg.keep {X : AcsCtx} {mf : Manifest} {header : ImageHeader} {M M' : Word → BitVec 8}
    {x21 x25 x27 : Word} (A : AcsImg X mf header M x21 x25 x27)
    (h : ∀ k, AcsWin k → M' (acSlot X.B k) = M (acSlot X.B k)) : AcsImg X mf header M' x21 x25 x27 := by
  obtain ⟨Mh, sv, entry, cnt, segs, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := A.out
  refine ⟨A.man, A.dec, A.lev, A.r27, ⟨Mh, sv, entry, cnt, segs, e1, e2, e3, e4, e5, e6, e7,
    fun i hi => (h _ (.inr ⟨by omega, by omega⟩)).trans (e8 i hi),
    fun i hi => (h _ (.inr ⟨by omega, by omega⟩)).trans (e9 i hi)⟩, ?_, ?_⟩
  · rw [← A.addr]
    exact memLoad32_congr fun j hj => by rw [acf_slot_add]; exact h _ (.inl ⟨by omega, by omega⟩)
  · rw [← A.digest]
    unfold memBytes
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    rw [acf_slot_add, h _ (.inr ⟨by omega, by omega⟩)]

/-- The exit at 0x7D6 with a code of 0x27 or more returns `None`. -/
def AcsFinishBad : Prop :=
  ∀ (X : AcsCtx), X.Ok → ∀ n, AcFinishInv X.B X.Bf X.g X.t X.v X.M0 n → AcFinishBad X.B X.r n → X.End n

theorem acs_lo8 (b : BitVec 8) : (b.zeroExtend 32).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, Nat.shiftRight_zero]
  have := b.isLt; omega

theorem acs_byte (v : Nat) : (BitVec.ofNat 32 v).extractLsb' 0 8 = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  exact Nat.mod_mod_of_dvd v (by decide)

theorem acs_ne_ff : ∀ k : BitVec 8, (3 : BitVec 8).ult k = false → k ≠ 0xFF := by decide

/-- **The result** from what the finish stage returns with. -/
theorem acs_good {X : AcsCtx} {n : Machine} {M' : Word → BitVec 8} {mf : Manifest} {header : ImageHeader}
    {parts : TufParts} {ver ex ex' : Nat} {root : SigstoreRoot} {b : Bundle}
    (A : AcsImg X mf header n.mem (reg n (21 : Fin 32)) (reg n (25 : Fin 32)) (reg n (27 : Fin 32)))
    (hp : decodeTufParts (flashBytes X.flash (acBase X.slot + mf.tuf.offset) mf.tuf.length) = some parts)
    (hv : verifyTuf X.pinned parts = some (ver, ex))
    (hx : extractTrustedRoot parts.trustedRoot X.policy = some root)
    (hb : decodeBundle (flashBytes X.flash (acBase X.slot + mf.bundle.offset) mf.bundle.length) = some b)
    (hle : ex' ≤ ex) (R : AcFinishRes X.B X.Bf X.r X.M0 b root ex' n M') :
    AcsGood X.flash X.pinned X.policy X.level.toNat X.slot X.r M' := by
  obtain ⟨vv, hsv, hte, b0, b1, bC, bD, -, -, -, -, -, a120, b128, -⟩ := R
  rw [A.digest] at hsv
  obtain ⟨Mh, sv, entry, cnt, segs, hH, O, hl, hp0, hk, h21, h25, hb1, hb2⟩ := A.out
  have hk0 : Mh (acSlot X.B 0x187C) = segs[0].kind := by
    have := (O.1 0 hp0).2.2.2
    rwa [acf_slot_add] at this
  refine ⟨mf, header.securityVersion, vv.signedTime, acs_accept A.man A.dec A.lev hp hv hx hb hsv (Nat.le_trans hte hle), ?_, ?_,
    a120.trans A.addr, fun h hd => ?_⟩
  · rw [bC, h25, acs_lo8, hk0]; exact acs_ne_ff _ (hk _ (List.getElem_mem hp0))
  · rw [b128, A.r27, acs_byte]
  have e : h = header := Option.some.inj (hd.symm.trans A.dec)
  subst e
  have hb : ∀ i, i < 0x10C → M' (X.r + BitVec.ofNat 32 i) = Mh (acSlot X.B 0x1870 + BitVec.ofNat 32 i) := by
    intro i hi
    rw [acf_slot_add]
    rcases Nat.lt_or_ge i 1 with h0 | h0
    · obtain rfl : i = 0 := by omega
      rw [add_ofNat_zero, b0, h21, acs_lo8]
    rcases Nat.lt_or_ge i 12 with h1 | h1
    · have := b1 (i - 1) (by omega)
      rw [show 1 + (i - 1) = i by omega, hb1 _ (by omega), show 0x1871 + (i - 1) = 0x1870 + i by omega] at this
      exact this
    rcases Nat.lt_or_ge i 13 with h2 | h2
    · obtain rfl : i = 12 := by omega
      exact bC.trans (by rw [h25, acs_lo8])
    · have := bD (i - 13) (by omega)
      rw [show 0xD + (i - 13) = i by omega, hb2 _ (by omega), show 0x187D + (i - 13) = 0x1870 + i by omega]
        at this
      exact this
  have h16 := (bmc_decode A.dec).1
  rw [hH] at h16 ⊢
  simp only [toHdr, List.length_map] at h16
  exact acs_hdr O hl h16 hk hb

/-- **From 0x1A46**, with what the earlier stages leave: the closure panics
or returns with `AcsRes`. -/
theorem acs_fin (hFx : AcsFinishBad) {X : AcsCtx} (ok : X.Ok) {n : Machine} {mf : Manifest}
    {header : ImageHeader} {parts : TufParts} {ver ex ex' : Nat} {root : SigstoreRoot} {b : Bundle}
    (I : AcInv X.B X.Bf X.g X.t X.v X.M0 n) (P : AcFinishPre X.B X.r b root ex' n) (hle : ex' ≤ ex)
    (A : AcsImg X mf header n.mem (reg n (21 : Fin 32)) (reg n (25 : Fin 32)) (reg n (27 : Fin 32)))
    (hp : decodeTufParts (flashBytes X.flash (acBase X.slot + mf.tuf.offset) mf.tuf.length) = some parts)
    (hv : verifyTuf X.pinned parts = some (ver, ex))
    (hx : extractTrustedRoot parts.trustedRoot X.policy = some root)
    (hb : decodeBundle (flashBytes X.flash (acBase X.slot + mf.bundle.offset) mf.bundle.length) = some b) :
    X.End n := by
  have E := ok.envsAt I
  obtain ⟨n', s, h⟩ := ac_finish_stage n X.B X.Bf X.g X.t X.r X.v X.M0 b root ex'
    (fun M hM => (ok.envs hM).fin) E.ac ok.F ok.ret I P
  rcases h with h | ⟨FI, h⟩ | ⟨pc, sp', sv, r3, r4, R⟩
  · exact .inl ⟨n', s, h⟩
  · exact acs_end_pre s (by rw [FI.gp, I.gp]) (by rw [FI.tp, I.tp])
      (h.elim (ok.failW FI) (hFx X ok n' FI))
  · refine .inr ⟨n', s, pc, sp', sv, by rw [r3, I.gp], by rw [r4, I.tp], fun x h1 h2 h3 => ?_,
      .inr (acs_good A hp hv hx hb hle R)⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, fr⟩ := R
    exact fr x h1 h2 h3

end C3.RV32.Ac
