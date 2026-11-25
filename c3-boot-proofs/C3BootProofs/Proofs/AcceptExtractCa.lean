import C3BootProofs.Proofs.AcceptExtractCaLib

/-!
# The certificate-authority loop, 0xD8C to 0xEBA

`ace_ca` proves `AceCaStage`. Each pass from 0xD8C takes the next item of
`certificateAuthorities` with `next_element`, reads its chain with
`read_chain`, and, when the first certificate has a P-384 key, stores
the key's entry at the end of the Fulcio array at `sp + 0x1ED0`. A ninth
key exits with code 5. When the items run out, `aceca_e2e` runs the tail
to 0xEBA.

The loop invariant is `AceCaInv`: the items `rest` left, the cursor at
`sp + 0x1310` that walks them, and the keys `fs` of the items done, which
`AceProg` states as `aceKeys aceCa` of those items. That is
`extractTrustedRoot`'s `cas.mapM` followed by `filterMap id`, one item at a
time (`AceProg.step`). The keys are the entries of the array.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3 C3.RV32.Sv C3.Json

set_option maxRecDepth 100000

/-! ## Tools -/

theorem aceca_slotC (B : Word) (s c : Nat) : acSlot B s + BitVec.ofNat 32 c = acSlot B (s + c) := by
  unfold acSlot; rw [add_ofNat_assoc, Nat.add_assoc]

theorem aceca_ofMod (x : Nat) : BitVec.ofNat 32 (x % 2 ^ 32) = BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, Nat.mod_mod]

/-- `read_chain`'s P-384 frame, 0x1A0 bytes into its stack region. -/
theorem aceca_fr384 {B : Word} (F : Fr B 0x5A70) : Fr (B + BitVec.ofNat 32 0x34B0) 0x420 := by
  have e := F.at 0x34B0 (by decide)
  have hal := F.al
  have hlo := F.lo
  have hhi := F.hi
  refine ⟨by rw [e]; omega, by rw [e]; omega, by rw [e]; omega, ?_⟩
  have h := F.dsep.sub (c := 0x34B0) (l := 0x5C0) (by decide)
  rwa [show B + 0xFFFFFE60 + BitVec.ofNat 32 0x34B0 = B + BitVec.ofNat 32 0x34B0 + 0xFFFFFE60 by bv_omega] at h

/-- `next_element`'s frame is apart from `read_item`'s code. -/
theorem aceca_riSep {X : AceCtx} (O : X.Ok) : RiSep (X.B + BitVec.ofNat 32 0x39BC) 148 (RJN + 0xFFFFF7E0) := by
  have F := O.lay.fr
  have hh := F.hi
  have hw : (X.B + BitVec.ofNat 32 0x39BC).toNat + 148 ≤ 0x40000000 := by rw [F.at _ (by decide)]; omega
  have hro : Sep (X.B + BitVec.ofNat 32 0x39BC) 148 TVF_RO 0x1400 := O.lay.ro.sub (by decide)
  exact ⟨lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide),
    lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide), lowSep hw (by decide) (by decide),
    lowSep hw (by decide) (by decide), rc_roSub hro (by decide), rc_roSub hro (by decide)⟩

/-- What `read_chain` leaves alone outside `AcaV`'s ranges. -/
theorem aceca_rcV {X : AceCtx} (O : X.Ok) {M M' : Word → BitVec 8} {fp : Word}
    {r : Except (Option Nat) (RcCert × RcSt)}
    (h : rcMem M (X.B + BitVec.ofNat 32 0x3310) (acSlot X.B 0x1320) (acSlot X.B 0x1FDC) fp
      (X.Bf.toNat + 0xB840 - fp.toNat) r M') (hfp : fp.toNat ≤ X.Bf.toNat + 0xB840) :
    ∀ x, AcaV X.B X.Bf fp x → M' x = M x := by
  intro x hx
  have F := O.lay.fr
  have hb := O.lay.hi
  unfold acBufLen at hb
  refine h.2 x (hx.1.sep F (c := 0x3310) (n := 0x740) (.inl ⟨by decide, by decide⟩)).symm
    (hx.1.sep F (c := 0x3A50 + 0x1320) (n := 0x40) (.inr (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩)))))).symm
    ?_ ?_
  · refine (ace_sepX F (c := 0x3A50 + 0x1FDC) (n := 8) (by decide) ?_).symm
    rcases hx.2.1 with h' | h'
    · exact .inl (by omega)
    · exact .inr (by omega)
  · have hx' := x.isLt
    rcases hx.2.2 with h' | h'
    · exact (sep_of_le (a := x) (n := 1) (by omega) (by omega)).symm
    · exact sep_of_le (by omega) (by omega)

/-- A word of the frame that `read_chain` leaves alone. -/
theorem aceca_rcSlot {X : AceCtx} (O : X.Ok) {M M' : Word → BitVec 8} {fp : Word}
    {r : Except (Option Nat) (RcCert × RcSt)}
    (h : rcMem M (X.B + BitVec.ofNat 32 0x3310) (acSlot X.B 0x1320) (acSlot X.B 0x1FDC) fp
      (X.Bf.toNat + 0xB840 - fp.toNat) r M') (hfp : X.Bf.toNat ≤ fp.toNat)
    (hfph : fp.toNat ≤ X.Bf.toNat + 0xB840) {k : Nat} (hk : 0x3A50 + k + 4 ≤ 0x5A70)
    (h2 : 0x3A50 + k + 4 ≤ 0x4D70 ∨ 0x4DB0 ≤ 0x3A50 + k) (h3 : 0x3A50 + k + 4 ≤ 0x5A2C ∨ 0x5A34 ≤ 0x3A50 + k) :
    memLoad32 M' (acSlot X.B k) = memLoad32 M (acSlot X.B k) := by
  have F := O.lay.fr
  have hb := O.lay.hi
  unfold acBufLen at hb
  refine ace_load_eq fun j hj => ?_
  rw [ace_slot]
  refine h.2 _ (ace_sepB' F (c := 0x3310) (n := 0x740) (.inl (by omega)) (by decide) (by omega))
    (ace_sepB' F (c := 0x3A50 + 0x1320) (n := 0x40) ?_ (by decide) (by omega))
    (ace_sepB' F (c := 0x3A50 + 0x1FDC) (n := 8) ?_ (by decide) (by omega))
    (aceca_bufSep O (c := 0x3A50 + k + j) (k := 1) (by omega) hfp (by unfold acBufLen; omega)).symm
  · rcases h2 with h2 | h2
    · exact .inr (by omega)
    · exact .inl (by omega)
  · rcases h3 with h3 | h3
    · exact .inr (by omega)
    · exact .inl (by omega)

theorem aceca_bytesMove {Bf fp : Word} {M M' : Word → BitVec 8} {p : Word} {l : Nat} {bs : Bytes}
    (hb : ∀ y : Word, Bf.toNat + 0x4000 ≤ y.toNat → y.toNat < fp.toNat → M' y = M y)
    (h : AceBytesIn Bf fp M p l bs) : AceBytesIn Bf fp M' p l bs := by
  obtain ⟨h1, h2, h3⟩ := h
  have hf := fp.isLt
  refine ⟨h1, h2, (ace_memBytes_ext fun i hi => hb _ ?_ ?_).trans h3⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem aceca_entryMono {Bf fp fp' : Word} {M : Word → BitVec 8} {e : Word} {name key : Bytes} {n : Nat}
    {w : Window} (h : AceEntryIn Bf fp M e name key n w) (hle : fp.toNat ≤ fp'.toNat) :
    AceEntryIn Bf fp' M e name key n w :=
  ⟨⟨h.name.1, by have := h.name.2.1; omega, h.name.2.2⟩, h.notBefore, h.notAfter,
    ⟨h.key.1, by have := h.key.2.1; omega, h.key.2.2⟩⟩

theorem aceca_fulcioMono {Bf fp fp' : Word} {M : Word → BitVec 8} {a : Word} {fs : List FulcioKey}
    (h : AceFulcioAt Bf fp M a fs) (hle : fp.toNat ≤ fp'.toNat) : AceFulcioAt Bf fp' M a fs :=
  ⟨h.1, fun i hi => aceca_entryMono (h.2.1 i hi) hle, h.2.2⟩

/-- Seven words stored from `e`, as 0xE12 to 0xE20 store a Fulcio entry. -/
def acaSt7 (M : Word → BitVec 8) (e w0 w1 w2 w3 w4 w5 w6 : Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M
    (e + BitVec.ofNat 32 0) w0) (e + BitVec.ofNat 32 4) w1) (e + BitVec.ofNat 32 8) w2)
    (e + BitVec.ofNat 32 0xC) w3) (e + BitVec.ofNat 32 0x10) w4) (e + BitVec.ofNat 32 0x14) w5)
    (e + BitVec.ofNat 32 0x18) w6

theorem aceca_st7 (M : Word → BitVec 8) (e w0 w1 w2 w3 w4 w5 w6 : Word) :
    (∀ x, Sep x 1 e 0x1C → acaSt7 M e w0 w1 w2 w3 w4 w5 w6 x = M x) ∧
    memLoad32 (acaSt7 M e w0 w1 w2 w3 w4 w5 w6) (e + BitVec.ofNat 32 0) = w0 ∧
    memLoad32 (acaSt7 M e w0 w1 w2 w3 w4 w5 w6) (e + BitVec.ofNat 32 4) = w1 ∧
    memLoad32 (acaSt7 M e w0 w1 w2 w3 w4 w5 w6) (e + BitVec.ofNat 32 8) = w2 ∧
    memLoad32 (acaSt7 M e w0 w1 w2 w3 w4 w5 w6) (e + BitVec.ofNat 32 0xC) = w3 ∧
    memLoad32 (acaSt7 M e w0 w1 w2 w3 w4 w5 w6) (e + BitVec.ofNat 32 0x10) = w4 ∧
    memLoad32 (acaSt7 M e w0 w1 w2 w3 w4 w5 w6) (e + BitVec.ofNat 32 0x14) = w5 ∧
    memLoad32 (acaSt7 M e w0 w1 w2 w3 w4 w5 w6) (e + BitVec.ofNat 32 0x18) = w6 := by
  have s : ∀ a b, a + 4 ≤ b ∨ b + 4 ≤ a → a ≤ 0x18 → b ≤ 0x18 →
      Sep (e + BitVec.ofNat 32 a) 4 (e + BitVec.ofNat 32 b) 4 :=
    fun a b h _ _ => sep_offsets e h (by omega) (by omega)
  unfold acaSt7
  refine ⟨fun x hx => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have q : ∀ c, c + 4 ≤ 0x1C → Sep (e + BitVec.ofNat 32 c) 4 x 1 := fun c hc =>
      (hx.subR (c := c) (l := 4) hc).symm
    rw [memStore32_get_sep (q 0x18 (by decide)), memStore32_get_sep (q 0x14 (by decide)),
      memStore32_get_sep (q 0x10 (by decide)), memStore32_get_sep (q 0xC (by decide)),
      memStore32_get_sep (q 8 (by decide)), memStore32_get_sep (q 4 (by decide)),
      memStore32_get_sep (q 0 (by decide))]
  · rw [memLoad32_store32_sep (s 0x18 0 (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (s 0x14 0 (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (s 0x10 0 (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (s 0xC 0 (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (s 8 0 (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (s 4 0 (by decide) (by decide) (by decide)), memLoad32_store32_same]
  · rw [memLoad32_store32_sep (s 0x18 4 (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (s 0x14 4 (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (s 0x10 4 (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (s 0xC 4 (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (s 8 4 (by decide) (by decide) (by decide)), memLoad32_store32_same]
  · rw [memLoad32_store32_sep (s 0x18 8 (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (s 0x14 8 (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (s 0x10 8 (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (s 0xC 8 (by decide) (by decide) (by decide)), memLoad32_store32_same]
  · rw [memLoad32_store32_sep (s 0x18 0xC (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (s 0x14 0xC (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (s 0x10 0xC (by decide) (by decide) (by decide)), memLoad32_store32_same]
  · rw [memLoad32_store32_sep (s 0x18 0x10 (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (s 0x14 0x10 (by decide) (by decide) (by decide)), memLoad32_store32_same]
  · rw [memLoad32_store32_sep (s 0x18 0x14 (by decide) (by decide) (by decide)), memLoad32_store32_same]
  · rw [memLoad32_store32_same]

/-! ## The call of `read_chain` at 0xDCA -/

set_option maxHeartbeats 4000000 in
/-- `read_chain` on the `l` bytes at `p` of the document, with the result
at `sp + 0x1320` and `keys`'s free part, `fl` bytes from `fp`, in the
slice at `sp + 0x1FDC`. -/
theorem aceca_rc (hrc : AcaRcErr) {X : AceCtx} (O : X.Ok) {Q : Post} {M : Word → BitVec 8}
    {f : Fin 32 → Word} {fp p : Word} {l fl : Nat} (hfl : fl = X.Bf.toNat + 0xB840 - fp.toNat)
    (hfp1 : X.Bf.toNat + 0x6800 ≤ fp.toNat) (hfp2 : fp.toNat ≤ X.Bf.toNat + 0xB840)
    (hsp : f sp = X.B + 0x3A50) (h0 : f a0 = acSlot X.B 0x1320) (h1 : f a1 = p)
    (h2 : f a2 = BitVec.ofNat 32 l) (h3 : f a3 = acSlot X.B 0x1FDC) (hc : RcCode M)
    (hw0 : memLoad32 M (acSlot X.B 0x1FDC) = fp) (hw1 : memLoad32 M (acSlot X.B 0x1FDC + 4) = BitVec.ofNat 32 fl)
    (hp1 : X.D.toNat ≤ p.toNat) (hp2 : p.toNat + l ≤ X.D.toNat + X.json.length)
    (k : ∀ m2 : Machine,
      rcMem M (X.B + BitVec.ofNat 32 0x3310) (acSlot X.B 0x1320) (acSlot X.B 0x1FDC) fp fl
        (readChainPos M p l fp fl) m2.mem →
      (∀ e, readChainPos M p l fp fl = .error e → (m2.mem (acSlot X.B 0x1320 + 4)).toNat < 0x27) →
      WP bootMainClosure0Code AC Q m2.mem (0xDCA + 8) (clob (upd f ra (AC + BitVec.ofNat 32 (0xDCA + 8))) m2 jClob)) :
    WP bootMainClosure0Code AC Q M 0xDCA f := by
  have F := O.lay.fr
  have hh := F.hi
  have hal := F.al
  have hlo := F.lo
  have hb := O.lay.hi
  unfold acBufLen at hb
  have hD := O.pre.docLo
  have hJ := O.pre.docHi
  have eG : X.B + 0x3A50 + 0xFFFFF8C0 = X.B + BitVec.ofNat 32 0x3310 := by bv_omega
  have e384 : X.B + 0x3A50 + 0xFFFFF8C0 + BitVec.ofNat 32 0x1A0 = X.B + BitVec.ofNat 32 0x34B0 := by bv_omega
  have esp : (X.B + 0x3A50 : Word).toNat = X.B.toNat + 0x3A50 := F.at 0x3A50 (by decide)
  have efp : X.Bf + BitVec.ofNat 32 (fp.toNat - X.Bf.toNat) = fp := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := fp.isLt; omega
  have eG' : (X.B + BitVec.ofNat 32 0x3310).toNat = X.B.toNat + 0x3310 := F.at _ (by decide)
  have eO : (acSlot X.B 0x1320).toNat = X.B.toNat + 0x4D70 := F.at _ (by decide)
  have eR : (acSlot X.B 0x1FDC).toNat = X.B.toNat + 0x5A2C := F.at _ (by decide)
  have sFR : Sep fp fl TVF_RO 0x1400 := by
    have := O.lay.roBuf.sub (c := fp.toNat - X.Bf.toNat) (l := fl) (by unfold acBufLen; omega)
    rwa [efp] at this
  refine WP.trCallSaved (tb := TRC)
    (P := fun m2 => rcMem M (X.B + BitVec.ofNat 32 0x3310) (acSlot X.B 0x1320) (acSlot X.B 0x1FDC) fp fl
      (readChainPos M p l fp fl) m2.mem ∧
      ∀ e, readChainPos M p l fp fl = .error e → (m2.mem (acSlot X.B 0x1320 + 4)).toNat < 0x27)
    ac_at_dca ac_at_dce (by decide) (fun m1 hpc1 hmem1 hreg1 hbe => ?_) (fun m2 hP hcd => ?_)
    (fun m2 hP => k m2 hP.1 hP.2)
  · unfold AcaRcErr at hrc
    obtain ⟨m', hs, hpc', hsp', hk, hR, hE⟩ := hrc m1 (sp0 := X.B + 0x3A50) (out := acSlot X.B 0x1320)
      (p := p) (fr := acSlot X.B 0x1FDC) (fp := fp) (n := l) (fl := fl)
      (retAddr := AC + BitVec.ofNat 32 (0xDCA + 8)) (by rw [hmem1]; exact hc) hpc1
      (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact h1) (by rw [hreg1]; rsimp; exact h2)
      (by rw [hreg1]; rsimp; exact h3) (by rw [hreg1]; rsimp) (by decide) (by rw [hreg1]; rsimp; exact hsp)
      (by rw [esp]; omega) (by rw [esp]; omega) (by rw [esp]; omega)
      (by rw [e384]; exact aceca_fr384 F)
      (by rw [eG]; exact O.lay.ro.sub (c := 0x3310) (l := 0x740) (by decide))
      (ace_al4 F (c := 0x3A50 + 0x1320) (by decide) (by decide)) (by rw [eO]; omega)
      (by rw [eG]; exact ace_sepB' F (c := 0x3A50 + 0x1320) (.inr (by decide)) (by decide) (by decide))
      (ace_sepB' F (c := 0x3A50 + 0x1320) (k := 0x3A50 + 0x1FDC) (.inl (by decide)) (by decide) (by decide))
      (aceca_bufSep O (c := 0x3A50 + 0x1320) (by decide) (by omega) (by unfold acBufLen; omega))
      (ace_al4 F (c := 0x3A50 + 0x1FDC) (by decide) (by decide)) (by rw [eR]; omega)
      (by rw [eG]; exact ace_sepB' F (c := 0x3A50 + 0x1FDC) (.inr (by decide)) (by decide) (by decide))
      (O.lay.ro.sub (c := 0x3A50 + 0x1FDC) (l := 8) (by decide))
      (aceca_bufSep O (c := 0x3A50 + 0x1FDC) (by decide) (by omega) (by unfold acBufLen; omega))
      (by omega) (by omega)
      (by rw [eG]; exact (aceca_bufSep O (c := 0x3310) (k := 0x740) (by decide) (by omega)
        (by unfold acBufLen; omega)).symm)
      sFR (by rw [hmem1]; exact hw0) (by rw [hmem1]; exact hw1) (by omega) (by omega)
      (by rw [eG]; exact (aceca_bufSep O (c := 0x3310) (k := 0x740) (by decide) (by omega)
        (by unfold acBufLen; omega)).symm)
      ((aceca_bufSep O (c := 0x3A50 + 0x1FDC) (k := 8) (by decide) (by omega)
        (by unfold acBufLen; omega)).symm)
      (sep_of_le (by omega) (by have := fp.isLt; omega))
    rw [hmem1, eG] at hR
    rw [hmem1] at hE
    exact ⟨m', hs, hpc', ⟨hR, hE⟩, by rw [hsp', hreg1]; rsimp; exact hsp.symm, hk⟩
  · refine hcd.hi (fun x hx => hP.1.2 x ?_ ?_ ?_ ?_) (by decide) (by decide)
    · exact lowSep (by rw [eG']; omega) hx (by have := x.isLt; omega)
    · exact lowSep (by rw [eO]; omega) hx (by have := x.isLt; omega)
    · exact lowSep (by rw [eR]; omega) hx (by have := x.isLt; omega)
    · exact lowSep (by omega) hx (by have := x.isLt; omega)

/-! ## Back at 0xD8C -/

/-- Back at 0xD8C with `rest'` left, the keys `fs'`, and `keys`'s free part
from `fp'`. -/
theorem aceca_back {X : AceCtx} (O : X.Ok) {n0 : Machine} {fp fp' : Word} {jr j : Json} {rest' : List Json}
    {fs fs' : List FulcioKey} (A : AceAt X n0 0xD8C fp) (I : AceCaInv X n0 fp jr (j :: rest') fs)
    {M : Word → BitVec 8} {f : Fin 32 → Word} (R : AceHR X f)
    (hm : ∀ x, AcaU X.B X.Bf fp x → M x = n0.mem x)
    (hp1 : memLoad32 M (acSlot X.B 0x1FDC) = fp')
    (hp2 : memLoad32 M (acSlot X.B 0x1FE0) = BitVec.ofNat 32 (X.Bf.toNat + 0xB840 - fp'.toNat))
    (hle : fp.toNat ≤ fp'.toNat) (hhi : fp'.toNat ≤ X.Bf.toNat + 0xB840)
    (hprog : AceProg jr (ascii!"certificateAuthorities") aceCa rest' fs')
    (hcur : AceCur X.D X.json M (acSlot X.B 0x1310) rest') (hful : AceFulcioAt X.Bf fp' M (acSlot X.B 0x1ED0) fs')
    (h26 : f 26 = reg n0 26) (h9 : f 9 = acSlot X.B 0x1310) (h18 : f 18 = 7) (h20 : f 20 = acSlot X.B 0x1ED0)
    (h22 : f 22 = BitVec.ofNat 32 fs'.length) :
    WP bootMainClosure0Code AC (acaQ X (acaP X jr) (acaL X jr (j :: rest'))) M 0xD8C f := by
  have hflo := A.fr.lo
  refine WP.here fun n hpc hn hrg => ?_
  have hst : St n.mem AC n 0xD8C (reg n) := ⟨hpc, rfl, fun _ => rfl⟩
  have II := aceca_inv O A hm hn (by rw [hrg]; exact R.rsp) (by rw [hrg]; exact R.rgp) (by rw [hrg]; exact R.rtp)
  refine ⟨II, .inr (.inr ⟨hpc, j, rest', fp', fs', rfl,
    ⟨by rw [hn]; exact aceca_code O A hm, hst, II,
      ⟨by rw [hn]; exact hp1, by rw [hn]; exact hp2, by omega, hhi⟩,
      ⟨by rw [hn]; exact aceca_kept O A hm, ?_⟩, aceca_exp O A hm hn⟩,
    ⟨I.root, ?_, hprog, by rw [hn]; exact hcur, by rw [hn]; exact hful, by rw [hrg]; exact h9,
      by rw [hrg]; exact h18, by rw [hrg]; exact R.r19, by rw [hrg]; exact h20, by rw [hrg]; exact h22⟩⟩)⟩
  · intro q hq
    have : q = 21 ∨ q = 25 ∨ q = 27 := by revert hq; revert q; decide
    rcases this with rfl | rfl | rfl <;> rw [hrg]
    · exact R.r21
    · exact R.r25
    · exact R.r27
  · have ho := I.obj
    unfold AceObj at ho ⊢
    rw [hrg, h26, hn, aceca_slotEq O A hm (k := 0x30) (.inr ⟨by omega, by omega⟩)]
    exact ho

/-! ## The new entry, 0xE12 to 0xE24 -/

set_option maxHeartbeats 8000000 in
/-- From 0xE12, with the new key's fields in `a1` to `a6` and `a0` and its
entry's address in `s0`: the seven stores, then back to 0xD8C. -/
theorem aceca_e12 {X : AceCtx} (O : X.Ok) {n0 : Machine} {fp fp' : Word} {jr j : Json} {rest' : List Json}
    {fs : List FulcioKey} (A : AceAt X n0 0xD8C fp) (I : AceCaInv X n0 fp jr (j :: rest') fs)
    {M : Word → BitVec 8} {f : Fin 32 → Word} (R : AceHR X f) (h26 : f 26 = reg n0 26)
    (h9 : f 9 = acSlot X.B 0x1310) (h18 : f 18 = 7) (h20 : f 20 = acSlot X.B 0x1ED0)
    (h22 : f 22 = BitVec.ofNat 32 fs.length) (hlen : fs.length ≤ 7)
    (hv : ∀ x, AcaV X.B X.Bf fp x → M x = n0.mem x) (hcur : AceCur X.D X.json M (acSlot X.B 0x1310) rest')
    (hp1 : memLoad32 M (acSlot X.B 0x1FDC) = fp')
    (hp2 : memLoad32 M (acSlot X.B 0x1FE0) = BitVec.ofNat 32 (X.Bf.toNat + 0xB840 - fp'.toNat))
    (hle : fp.toNat ≤ fp'.toNat) (hhi : fp'.toNat ≤ X.Bf.toNat + 0xB840)
    {fk : FulcioKey} (hprog : AceProg jr (ascii!"certificateAuthorities") aceCa rest' (fs ++ [fk]))
    (h8 : f 8 = acSlot X.B 0x1ED0 + BitVec.ofNat 32 (0x20 * fs.length))
    {sub key : Word} {sl : Nat} (h11 : f 11 = sub) (h12 : f 12 = BitVec.ofNat 32 sl) (hsl : sl < 2 ^ 32)
    (hsub : AceBytesIn X.Bf fp' M sub sl fk.subject)
    (h13 : f 13 = BitVec.ofNat 32 fk.window.notBefore)
    (h14 : f 14 = BitVec.ofNat 32 (fk.window.notBefore / 2 ^ 32))
    (h15 : f 15 = BitVec.ofNat 32 fk.window.notAfter)
    (h16 : f 16 = BitVec.ofNat 32 (fk.window.notAfter / 2 ^ 32))
    (hnb : fk.window.notBefore < 2 ^ 64) (hna : fk.window.notAfter < 2 ^ 64)
    (h10 : f 10 = key) (hkey : AceBytesIn X.Bf fp' M key 0x61 fk.publicKey) :
    WP bootMainClosure0Code AC (acaQ X (acaP X jr) (acaL X jr (j :: rest'))) M 0xE12 f := by
  have F := O.lay.fr
  have hh := F.hi
  have hbh := O.lay.hi
  unfold acBufLen at hbh
  have hbf := aceca_bf A
  obtain ⟨E, hE⟩ : ∃ E, E = acSlot X.B 0x1ED0 + BitVec.ofNat 32 (0x20 * fs.length) := ⟨_, rfl⟩
  rw [← hE] at h8
  have ee : E = X.B + BitVec.ofNat 32 (0x5920 + 0x20 * fs.length) := by
    rw [hE, ace_slot]
  have hal : ∀ c, c % 4 = 0 → c + 4 ≤ 0x20 → (E + BitVec.ofNat 32 c).toNat % 4 = 0 := by
    intro c h1 h2; rw [ee, add_ofNat_assoc]; exact ace_al4 F (by omega) (by omega)
  have hcs : ∀ c, c + 4 ≤ 0x20 → Sep (E + BitVec.ofNat 32 c) 4 AC bootMainClosure0Code.length := by
    intro c h; rw [ee, add_ofNat_assoc]; exact ace_cs F (by omega)
  refine WP.sw ac_at_e12 (by (try rsimp); rw [h8]; exact hal 0 rfl (by decide)) (by (try rsimp); rw [h8]; exact hcs 0 (by decide)) ?_; wn
  refine WP.sw ac_at_e14 (by (try rsimp); rw [h8]; exact hal 4 rfl (by decide)) (by (try rsimp); rw [h8]; exact hcs 4 (by decide)) ?_; wn
  refine WP.sw ac_at_e16 (by (try rsimp); rw [h8]; exact hal 8 rfl (by decide)) (by (try rsimp); rw [h8]; exact hcs 8 (by decide)) ?_; wn
  refine WP.sw ac_at_e18 (by (try rsimp); rw [h8]; exact hal 0xC rfl (by decide)) (by (try rsimp); rw [h8]; exact hcs 0xC (by decide)) ?_
  wn
  refine WP.sw ac_at_e1a (by (try rsimp); rw [h8]; exact hal 0x10 rfl (by decide)) (by (try rsimp); rw [h8]; exact hcs 0x10 (by decide)) ?_
  wn
  refine WP.sw ac_at_e1c (by (try rsimp); rw [h8]; exact hal 0x14 rfl (by decide)) (by (try rsimp); rw [h8]; exact hcs 0x14 (by decide)) ?_
  wn
  refine WP.sw ac_at_e20 (by (try rsimp); rw [h8]; exact hal 0x18 rfl (by decide)) (by (try rsimp); rw [h8]; exact hcs 0x18 (by decide)) ?_
  wn
  refine WP.aluImm ac_at_e22 ?_; wn
  refine WP.jal ac_at_e24 (by decide) ?_; wn
  rw [h8, h10, h11, h12, h13, h14, h15, h16]
  show WP bootMainClosure0Code AC _ (acaSt7 M E sub (BitVec.ofNat 32 sl)
    (BitVec.ofNat 32 fk.window.notBefore) (BitVec.ofNat 32 (fk.window.notBefore / 2 ^ 32))
    (BitVec.ofNat 32 fk.window.notAfter) (BitVec.ofNat 32 (fk.window.notAfter / 2 ^ 32)) key) _ _
  obtain ⟨sF, s0, s4, s8, sC, s10, s14, s18⟩ := aceca_st7 M E sub (BitVec.ofNat 32 sl)
    (BitVec.ofNat 32 fk.window.notBefore) (BitVec.ofNat 32 (fk.window.notBefore / 2 ^ 32))
    (BitVec.ofNat 32 fk.window.notAfter) (BitVec.ofNat 32 (fk.window.notAfter / 2 ^ 32)) key
  generalize acaSt7 M E sub (BitVec.ofNat 32 sl)
    (BitVec.ofNat 32 fk.window.notBefore) (BitVec.ofNat 32 (fk.window.notBefore / 2 ^ 32))
    (BitVec.ofNat 32 fk.window.notAfter) (BitVec.ofNat 32 (fk.window.notAfter / 2 ^ 32)) key = M5 at sF s0 s4 s8 sC s10 s14 s18 ⊢
  rw [ee] at sF
  have hstk : ∀ k, k < 0x5A70 → (k + 1 ≤ 0x5920 + 0x20 * fs.length ∨ 0x5920 + 0x20 * fs.length + 0x1C ≤ k) →
      M5 (X.B + BitVec.ofNat 32 k) = M (X.B + BitVec.ofNat 32 k) := fun k hk h =>
    sF _ (ace_sepB' F (by rcases h with h | h; exact .inl h; exact .inr h) (by omega) (by omega))
  have hbuf : ∀ y : Word, X.Bf.toNat ≤ y.toNat → y.toNat < X.Bf.toNat + acBufLen → M5 y = M y :=
    fun y h1 h2 => sF y ((ace_bufOut O.lay h1 h2).subR (c := 0x5920 + 0x20 * fs.length) (l := 0x1C) (by omega))
  have hm5 : ∀ x, AcaU X.B X.Bf fp x → M5 x = n0.mem x := by
    intro x hx
    refine (sF x (ace_sepX F (by omega) ?_)).trans (hv x hx.1)
    rcases hx.2 with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  have hbf5 : ∀ y : Word, X.Bf.toNat + 0x4000 ≤ y.toNat → y.toNat < fp'.toNat → M5 y = M y :=
    fun y h1 h2 => hbuf y (by omega) (by unfold acBufLen; omega)
  have hld : ∀ k, 0x3A50 + k + 4 ≤ 0x5A70 →
      (0x3A50 + k + 4 ≤ 0x5920 + 0x20 * fs.length ∨ 0x5920 + 0x20 * fs.length + 0x1C ≤ 0x3A50 + k) →
      memLoad32 M5 (acSlot X.B k) = memLoad32 M (acSlot X.B k) := fun k hk h =>
    ace_load_eq fun i hi => by
      rw [ace_slot]
      exact hstk _ (by omega) (by rcases h with h | h; exact .inl (by omega); exact .inr (by omega))
  have e4 : acSlot X.B 0x1310 + 4 = acSlot X.B 0x1314 := aceca_slotC X.B 0x1310 4
  have e8 : acSlot X.B 0x1310 + 8 = acSlot X.B 0x1318 := aceca_slotC X.B 0x1310 8
  obtain ⟨cp, cl, cpos, c0, c4, c8, hcp, hcD, hcl, hcE⟩ := hcur
  rw [e4] at c4
  rw [e8] at c8
  refine aceca_back O A I (fp' := fp') (fs' := fs ++ [fk]) (by hr) hm5
    (by rw [hld 0x1FDC (by decide) (.inr (by omega))]; exact hp1)
    (by rw [hld 0x1FE0 (by decide) (.inr (by omega))]; exact hp2) hle hhi hprog
    ⟨cp, cl, cpos, by rw [hld 0x1310 (by decide) (.inl (by omega))]; exact c0,
      by rw [e4, hld 0x1314 (by decide) (.inl (by omega))]; exact c4,
      by rw [e8, hld 0x1318 (by decide) (.inl (by omega))]; exact c8, hcp, hcD, hcl, hcE⟩ ?_
    (by rsimp; exact h26) (by rsimp; exact h9) (by rsimp; exact h18) (by rsimp; exact h20) ?_
  · refine ⟨by simp only [List.length_append, List.length_singleton]; omega, fun i hi => ?_, fun i hi1 hi2 => ?_⟩
    · simp only [List.length_append, List.length_singleton] at hi
      rcases Nat.lt_or_ge i fs.length with hl | hl
      · rw [List.getElem_append_left hl]
        refine aceca_entryMono (AceEntryIn.move (I.fulcio.2.1 i hl) (fun c hc => ?_) ?_) hle
        · rw [add_ofNat_assoc, ace_slot]
          refine (hstk _ (by omega) (.inl (by omega))).trans (hv _ ?_)
          exact aceca_V_at O.lay hbf (F.at _ (by omega)) (.inr (.inr (.inl ⟨by omega, by omega⟩)))
        · intro y h1 h2
          exact (hbuf y (by omega) (by have := A.fr.hi; unfold acBufLen; omega)).trans (aceca_buf O A hv y h1 h2)
      · have hi' : i = fs.length := by omega
        subst hi'
        rw [List.getElem_append_right (Nat.le_refl _), List.getElem_singleton, ← hE]
        have q0 : memLoad32 M5 E = sub := by rw [← s0, add_ofNat_zero]
        have q4 : memLoad32 M5 (E + 4) = BitVec.ofNat 32 sl := s4
        have q8 : memLoad32 M5 (E + 8) = BitVec.ofNat 32 fk.window.notBefore := s8
        have qC : memLoad32 M5 (E + 8 + 4) = BitVec.ofNat 32 (fk.window.notBefore / 2 ^ 32) := by
          rw [show E + 8 + 4 = E + BitVec.ofNat 32 0xC from add_ofNat_assoc E 8 4]; exact sC
        have q10 : memLoad32 M5 (E + 0x10) = BitVec.ofNat 32 fk.window.notAfter := s10
        have q14 : memLoad32 M5 (E + 0x10 + 4) = BitVec.ofNat 32 (fk.window.notAfter / 2 ^ 32) := by
          rw [show E + 0x10 + 4 = E + BitVec.ofNat 32 0x14 from add_ofNat_assoc E 0x10 4]; exact s14
        have q18 : memLoad32 M5 (E + 0x18) = key := s18
        refine ⟨?_, ⟨hnb, q8, qC⟩, ⟨hna, q10, q14⟩, ?_⟩
        · rw [q0, q4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsl]
          exact aceca_bytesMove hbf5 hsub
        · rw [q18]; exact aceca_bytesMove hbf5 hkey
    · simp only [List.length_append, List.length_singleton] at hi1
      refine (ace_load_eq fun c hc => ?_).trans (I.fulcio.2.2 i (by omega) hi2)
      rw [add_ofNat_assoc, ace_slot]
      refine (hstk _ (by omega) (.inr (by omega))).trans (hv _ ?_)
      exact aceca_V_at O.lay hbf (F.at _ (by omega)) (.inr (.inr (.inl ⟨by omega, by omega⟩)))
  · rsimp
    rw [h22, ev_add, List.length_append, List.length_singleton]
    apply BitVec.eq_of_toNat_eq
    have : (1 : Word).toNat = 1 := rfl
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, this]
    omega

/-! ## After `read_chain`, from 0xDD2 -/

theorem aceca_sll : ∀ k, k < 8 → aluEval .sll (BitVec.ofNat 32 k) 5 = BitVec.ofNat 32 (0x20 * k) := by decide

theorem aceca_bltu : ∀ k, k < 8 → branchTaken .bltu (7 : Word) (BitVec.ofNat 32 k) = false := by decide

set_option maxHeartbeats 8000000 in
/-- From 0xDD2, with `read_chain`'s result `r` at `sp + 0x1320`: an error
exits, a first certificate without a P-384 key goes back to 0xD8C, and a
key is stored when the array has room and exits with code 5 when not. -/
theorem aceca_dd2 {X : AceCtx} (O : X.Ok) {n0 : Machine} {fp : Word} {jr j : Json} {rest' : List Json}
    {fs : List FulcioKey} (A : AceAt X n0 0xD8C fp) (I : AceCaInv X n0 fp jr (j :: rest') fs)
    {M : Word → BitVec 8} {f : Fin 32 → Word} (R : AceHR X f) (h26 : f 26 = reg n0 26)
    (h8 : f 8 = acSlot X.B 0x1310) (h18 : f 18 = 7) (h20 : f 20 = acSlot X.B 0x1ED0)
    (h22 : f 22 = BitVec.ofNat 32 fs.length)
    (hv : ∀ x, AcaV X.B X.Bf fp x → M x = n0.mem x) (hcur : AceCur X.D X.json M (acSlot X.B 0x1310) rest')
    {r : Except (Option Nat) (RcCert × RcSt)}
    (hr : RcOut M (acSlot X.B 0x1320) (acSlot X.B 0x1FDC) fp (X.Bf.toNat + 0xB840 - fp.toNat) r)
    (he : ∀ e, r = .error e → (M (acSlot X.B 0x1320 + 4)).toNat < 0x27)
    (hs : ∀ c s, r = .ok (c, s) → ∃ info, readChain j = some (info, ⟨s.nb, s.na⟩) ∧ RcInfo s.dec fp c info) :
    WP bootMainClosure0Code AC (acaQ X (acaP X jr) (acaL X jr (j :: rest'))) M 0xDD2 f := by
  have F := O.lay.fr
  have hh := F.hi
  have hbh := O.lay.hi
  unfold acBufLen at hbh
  have hbf := aceca_bf A
  have hflo := A.fr.lo
  have hfhi := A.fr.hi
  have hfw := fp.isLt
  have hmU : ∀ x, AcaU X.B X.Bf fp x → M x = n0.mem x := fun x hx => hv x hx.1
  refine WP.lui ac_at_dd2 ?_; wn
  refine WP.aluImm ac_at_dd4 ?_; wn
  refine WP.alu ac_at_dd8 ?_; wn
  simp only [ev_add]
  rcases r with e | ⟨c, s⟩
  · obtain ⟨t0, -⟩ := hr
    refine WP.lw ac_at_ddc (aceca_al O 0x1320 (by decide) (by decide)
      (by rsimp; rw [h8]; simp only [acSlot]; bv_omega)) ?_; wn
    refine WP.branch ac_at_dde (fun _ => ?_) (fun eb => ?_) <;> wn
    · refine WP.lbu ac_at_119e ?_; wn
      refine WP.jal ac_at_11a2 (by decide) ?_; wn
      refine aceca_f1A6A O A hmU (by hr) ?_
      rsimp
      rw [show f sp + (4096 + 784) + 20 = acSlot X.B 0x1320 + 4 by rw [R.rsp]; simp only [acSlot]; bv_omega,
        ace_zeAnd]
      exact he e rfl
    · exfalso; rsimp at eb
      rw [show f 8 + 16 = acSlot X.B 0x1320 by rw [h8]; simp only [acSlot]; bv_omega, t0] at eb
      exact absurd eb (by decide)
  obtain ⟨o0, o4, o8, oC, o10, o14, o18, o1C, o20, o24, o28, o30, o34, o38, o3C, bnb, bna, bsnb, bsna,
    hdl, hfr, hfl, hdec⟩ := hr
  obtain ⟨info, hrcj, RI⟩ := hs c s rfl
  obtain ⟨as, hsa, has, -⟩ := RI.serial
  have hfpa : ∀ a, a ≤ s.dec.length → (fp + BitVec.ofNat 32 a).toNat = fp.toNat + a := fun a ha => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hfp0 : fp.toNat ≠ 0 := by omega
  have hser : c.serial ≠ 0 := by rw [hsa]; exact trch_addNe hfp0 (by omega)
  have hfp' := hfpa s.dec.length (Nat.le_refl _)
  have eR4 : acSlot X.B 0x1FDC + 4 = acSlot X.B 0x1FE0 := aceca_slotC X.B 0x1FDC 4
  rw [eR4] at hfl
  have hp2 : memLoad32 M (acSlot X.B 0x1FE0) =
      BitVec.ofNat 32 (X.Bf.toNat + 0xB840 - (fp + BitVec.ofNat 32 s.dec.length).toNat) := by
    rw [hfl, hfp']; congr 1; omega
  have hle : fp.toNat ≤ (fp + BitVec.ofNat 32 s.dec.length).toNat := by omega
  have hhi : (fp + BitVec.ofNat 32 s.dec.length).toNat ≤ X.Bf.toNat + 0xB840 := by omega
  have eK : acSlot X.B 0x1320 + 0x28 = acSlot X.B 0x1348 := aceca_slotC X.B 0x1320 0x28
  rw [eK] at o28
  have h9 : ∀ g : Fin 32 → Word, g sp = X.B + 0x3A50 → g sp + (4096 + 784) = acSlot X.B 0x1310 := fun g hg => by
    rw [hg]; simp only [acSlot]; bv_omega
  refine WP.lw ac_at_ddc (aceca_al O 0x1320 (by decide) (by decide)
    (by rsimp; rw [h8]; simp only [acSlot]; bv_omega)) ?_; wn
  refine WP.branch ac_at_dde (fun eb => ?_) (fun _ => ?_) <;> wn
  · exfalso; rsimp at eb
    rw [show f 8 + 16 = acSlot X.B 0x1320 by rw [h8]; simp only [acSlot]; bv_omega, o0] at eb
    exact hser (by simpa [branchTaken] using eb)
  refine WP.lw ac_at_de2 (aceca_al O 0x1348 (by decide) (by decide)
    (by rsimp; rw [R.rsp]; simp only [acSlot]; bv_omega)) ?_; wn
  have eK' : f sp + (4096 + 784) + 56 = acSlot X.B 0x1348 := by rw [R.rsp]; simp only [acSlot]; bv_omega
  rcases RI.key with ⟨ak, hk, hak, hpk⟩ | ⟨hk, hpk⟩
  · have hkey0 : c.key ≠ 0 := by rw [hk]; exact trch_addNe hfp0 (by omega)
    refine WP.branch ac_at_de4 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; rsimp at eb; rw [eK', o28] at eb
      exact hkey0 (by simpa [branchTaken] using eb)
    have hcj : aceCa j = some (some ⟨info.subject, rcView s.dec (ak, 0x61), ⟨s.nb, s.na⟩⟩) := by
      simp [aceCa, hrcj, hpk]
    rcases Nat.lt_or_ge fs.length 8 with hl8 | hl8
    · refine WP.branch ac_at_de6 (fun eb => ?_) (fun _ => ?_) <;> wn
      · exfalso; rsimp at eb; rw [h18, h22, aceca_bltu _ hl8] at eb; exact absurd eb (by decide)
      refine WP.lui ac_at_dea ?_; wn
      refine WP.aluImm ac_at_dec ?_; wn
      refine WP.alu ac_at_df0 ?_; wn
      refine WP.lw ac_at_df4 (aceca_al O 0x1330 (by decide) (by decide)
        (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)) ?_; wn
      refine WP.lw ac_at_df6 (aceca_al O 0x1334 (by decide) (by decide)
        (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)) ?_; wn
      refine WP.lw ac_at_df8 (aceca_al O 0x1350 (by decide) (by decide)
        (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)) ?_; wn
      refine WP.lw ac_at_dfa (aceca_al O 0x1354 (by decide) (by decide)
        (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)) ?_; wn
      refine WP.lw ac_at_dfc (aceca_al O 0x1358 (by decide) (by decide)
        (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)) ?_; wn
      refine WP.lui ac_at_dfe ?_; wn
      refine WP.aluImm ac_at_e00 ?_; wn
      refine WP.alu ac_at_e04 ?_; wn
      refine WP.lw ac_at_e08 (aceca_al O 0x135C (by decide) (by decide)
        (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)) ?_; wn
      refine WP.aluImm ac_at_e0c ?_; wn
      refine WP.alu ac_at_e10 ?_; wn
      obtain ⟨asb, hsbA, hsbL, hsbV⟩ := RI.subject
      have hsl : c.subjectLen < 2 ^ 32 := by omega
      refine aceca_e12 O A I (fp' := fp + BitVec.ofNat 32 s.dec.length)
        (fk := ⟨info.subject, rcView s.dec (ak, 0x61), ⟨s.nb, s.na⟩⟩) (by hr) (by rsimp; exact h26)
        (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega) (by rsimp; exact h18)
        (by rsimp; exact h20) (by rsimp; exact h22) (by omega) hv hcur hfr hp2 hle hhi (I.cas.step hcj)
        (by rsimp; rw [h22, h20, aceca_sll _ hl8]; exact BitVec.add_comm _ _)
        (by rsimp; exact aceca_ldAt (by rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega) o10)
        (by rsimp; exact aceca_ldAt (by rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega) o14) hsl
        ⟨by rw [hsbA, hfpa asb (by omega)]; omega, by rw [hsbA, hfpa asb (by omega), hfp']; omega,
          by rw [hsbA, hsbV, trch_viewMem hdec hsbL]⟩
        (by rsimp; rw [← aceca_ofMod]
            exact aceca_ldAt (by rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega) o30)
        (by rsimp; exact aceca_ldAt (by rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega) o34)
        (by rsimp; rw [← aceca_ofMod]
            exact aceca_ldAt (by rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega) o38)
        (by rsimp; exact aceca_ldAt (by rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega) o3C)
        bsnb bsna (by rsimp; exact aceca_ldAt eK' o28)
        ⟨by rw [hk, hfpa ak (by omega)]; omega, by rw [hk, hfpa ak (by omega), hfp']; omega,
          by rw [hk, trch_viewMem hdec hak]⟩
    · have hl8' : fs.length = 8 := Nat.le_antisymm I.fulcio.1 hl8
      refine WP.branch ac_at_de6 (fun _ => ?_) (fun eb => ?_) <;> wn
      · refine WP.aluImm ac_at_1424 ?_; wn
        refine WP.jal ac_at_1426 (by decide) ?_; wn
        refine aceca_f1A6A O A hmU (by hr) ?_
        rsimp
      · exfalso; rsimp at eb; rw [h18, h22, hl8'] at eb; exact absurd eb (by decide)
  · refine WP.branch ac_at_de4 (fun _ => ?_) (fun eb => ?_) <;> wn
    · have hcj : aceCa j = some none := by simp [aceCa, hrcj, hpk]
      have hprog := I.cas.step hcj
      rw [show fs ++ (none : Option FulcioKey).toList = fs from List.append_nil fs] at hprog
      exact aceca_back O A I (fp' := fp + BitVec.ofNat 32 s.dec.length) (by hr) hmU hfr hp2 hle hhi hprog hcur
        (aceca_fulcioMono (ace_array_move I.fulcio (aceca_arr O A hv) (aceca_buf O A hv)) hle)
        (by rsimp; exact h26) (by rsimp; exact h9 f R.rsp) (by rsimp; exact h18) (by rsimp; exact h20)
        (by rsimp; exact h22)
    · exfalso; rsimp at eb; rw [eK', o28, hk] at eb; exact absurd eb (by decide)

/-! ## One pass from 0xD8C -/

/-- What `next_element` leaves alone of the frame. -/
theorem aceca_erSlot {X : AceCtx} (O : X.Ok) {M M2 : Word → BitVec 8}
    (hf : ∀ x, Sep x 1 (acSlot X.B 0x1320) 12 → Sep x 1 (acSlot X.B 0x1310 + 8) 4 →
      Sep x 1 (X.B + BitVec.ofNat 32 0x39BC) 148 → M2 x = M x)
    {k : Nat} (hk : 0x3A50 + k + 4 ≤ 0x5A70) (h1 : k + 4 ≤ 0x1318 ∨ 0x132C ≤ k) :
    memLoad32 M2 (acSlot X.B k) = memLoad32 M (acSlot X.B k) := by
  have F := O.lay.fr
  have e8 : acSlot X.B 0x1310 + 8 = X.B + BitVec.ofNat 32 (0x3A50 + 0x1318) := aceca_slotC X.B 0x1310 8
  refine ace_load_eq fun j hj => ?_
  rw [ace_slot]
  refine hf _ (ace_sepB' F (c := 0x3A50 + k + j) (n := 1) (k := 0x3A50 + 0x1320) (l := 12) ?_ (by omega)
    (by decide)) ?_ (ace_sepB' F (.inr (by omega)) (by omega) (by decide))
  · rcases h1 with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)
  · rw [e8]
    refine ace_sepB' F ?_ (by omega) (by decide)
    rcases h1 with h | h
    · exact .inl (by omega)
    · exact .inr (by omega)

set_option maxHeartbeats 8000000 in
/-- One pass of the loop from 0xD8C. -/
theorem aceca_pass (hrc : AcaRcErr) {X : AceCtx} (O : X.Ok) {n0 : Machine} {fp : Word} {jr : Json}
    {rest : List Json} {fs : List FulcioKey} (A : AceAt X n0 0xD8C fp) (I : AceCaInv X n0 fp jr rest fs) :
    WP bootMainClosure0Code AC (acaQ X (acaP X jr) (acaL X jr rest)) n0.mem 0xD8C (reg n0) := by
  have F := O.lay.fr
  have hh := F.hi
  have hbh := O.lay.hi
  unfold acBufLen at hbh
  have hbf := aceca_bf A
  have hflo := A.fr.lo
  have hfhi := A.fr.hi
  have hD0 := O.pre.docLo
  have hJ0 := O.pre.docHi
  have R : AceHR X (reg n0) := ⟨rfl, A.inv.sp, A.inv.gp, A.inv.tp, I.r19, A.keep.regs 21 (by decide),
    A.keep.regs 25 (by decide), A.keep.regs 27 (by decide)⟩
  have E := aceca_env O A (fun _ _ => rfl)
  obtain ⟨p, l, pos, c0, c4, c8, hpos, hp1, hpl, hEl⟩ := I.cur
  have e4 : acSlot X.B 0x1310 + 4 = acSlot X.B 0x1314 := aceca_slotC X.B 0x1310 4
  have e8 : acSlot X.B 0x1310 + 8 = acSlot X.B 0x1318 := aceca_slotC X.B 0x1310 8
  refine WP.lui ac_at_d8c ?_; wn
  refine WP.aluImm ac_at_d8e ?_; wn
  refine WP.alu ac_at_d92 ?_; wn
  refine WP.lui ac_at_d94 ?_; wn
  refine WP.aluImm ac_at_d96 ?_; wn
  refine WP.alu ac_at_d9a ?_; wn
  have hdoc : memBytes n0.mem p l = (X.json.drop (p.toNat - X.D.toNat)).take l :=
    aceca_docBytes O A (fun _ _ => rfl) hp1 (by omega)
  have hvl : ((X.json.drop (p.toNat - X.D.toNat)).take l).length = l := by
    simp only [List.length_take, List.length_drop]; omega
  refine WP.callNextElement (tb := RJN) (out := acSlot X.B 0x1320) (c := acSlot X.B 0x1310)
    (s := X.B + BitVec.ofNat 32 0x39BC) (p := p) (n := l) (pos := pos) ac_at_d9c ac_at_da0 (by decide)
    (by decide) (by decide) E.next E.item
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
    (by rsimp; rw [R.rsp]; bv_omega)
    (ace_al4 F (by decide) (by decide)) (ace_al4 (c := 0x3A50 + 0x1320) F (by decide) (by decide))
    (ace_al4 (c := 0x3A50 + 0x1310) F (by decide) (by decide)) c0 c4 c8 (by omega) hpos (by omega) (by omega)
    (aceca_riSep O) (ace_hs F (by decide) (by decide) (by decide))
    (aceca_bufSep O (c := 0x39BC) (by decide) (by omega) (by unfold acBufLen; omega))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 _ _ from
      ace_sepB' F (.inr (by decide)) (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1310)) 12 _ _ from
      ace_sepB' F (.inr (by decide)) (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 _ _ from
      ace_sepB' F (.inr (by decide)) (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 _ _ from ace_hs F (by decide) (by decide) (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1310)) 12 _ _ from ace_hs F (by decide) (by decide) (by decide))
    (ace_cs F (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1320)) 12 _ _ from ace_cs F (by decide))
    (show Sep (X.B + BitVec.ofNat 32 (0x3A50 + 0x1310)) 12 _ _ from ace_cs F (by decide)) fun m2 hR => ?_
  wn
  rw [hdoc] at hR
  generalize m2.mem = M2 at hR
  obtain ⟨M1, hO1, hER⟩ := hR
  have hf2 : ∀ x, Sep x 1 (acSlot X.B 0x1320) 12 → Sep x 1 (acSlot X.B 0x1310 + 8) 4 →
      Sep x 1 (X.B + BitVec.ofNat 32 0x39BC) 148 → M2 x = n0.mem x := fun x h1 h2 h3 =>
    (hER.out h1 h2).trans (hO1 x h3)
  have hW2 : ∀ x, AcaW X.B x → M2 x = n0.mem x := fun x hx =>
    hf2 x (hx.sep F (c := 0x3A50 + 0x1320) (n := 12) (.inr (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩))))))
      (by
        rw [e8]
        exact hx.sep F (c := 0x3A50 + 0x1318) (n := 4) (.inr (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩))))))
      (hx.sep F (c := 0x39BC) (n := 148) (.inl ⟨by decide, by decide⟩))
  have T2 : AcaT X n0 fp M2 := (⟨fun _ _ => rfl, rfl, rfl⟩ : AcaT X n0 fp n0.mem).mono F hW2
  have hm2 : ∀ x, AcaU X.B X.Bf fp x → M2 x = n0.mem x := fun x hx => T2.mem x hx.1
  have eO : acSlot X.B 0x1310 + 16 = acSlot X.B 0x1320 := aceca_slotC X.B 0x1310 16
  have eO4 : acSlot X.B 0x1310 + 20 = acSlot X.B 0x1320 + 4 := by
    exact (aceca_slotC X.B 0x1310 20).trans (aceca_slotC X.B 0x1320 4).symm
  cases rest with
  | nil =>
    have hne : nextElement ((X.json.drop (p.toNat - X.D.toNat)).take l) pos = some none := hEl
    rw [hne] at hER
    simp only [elemRes, Option.map_some] at hER
    obtain ⟨-, t0, t4⟩ := hER
    refine WP.lbu ac_at_da4 ?_; wn
    refine WP.branch ac_at_da8 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; rsimp at eb; rw [I.r9, eO, t0] at eb; exact absurd eb (by decide)
    refine WP.lw ac_at_daa (aceca_al O 0x1324 (by decide) (by decide)
      (by rsimp; rw [I.r9]; simp only [acSlot]; bv_omega)) ?_; wn
    refine WP.branch ac_at_dac (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact aceca_e2e O A I T2 (by hr) (by rsimp <;> rfl)
    · exfalso; rsimp at eb; rw [I.r9, eO4, t4] at eb; exact absurd eb (by decide)
  | cons j rest' =>
    obtain ⟨el, a, hne, hden, hEl'⟩ := hEl
    obtain ⟨-, hpa, hel0, hpel, hal⟩ := nextElement_lt hne
    rw [hvl] at hpel hal
    rw [hne] at hER
    simp only [elemRes, Option.map_some] at hER
    obtain ⟨-, t0, t4, t8, tc⟩ := hER
    have hq : (p + BitVec.ofNat 32 pos).toNat = p.toNat + pos := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hq0 : p + BitVec.ofNat 32 pos ≠ 0 := by
      intro h; have := congrArg BitVec.toNat h; rw [hq] at this
      have : (0 : Word).toNat = 0 := rfl
      omega
    refine WP.lbu ac_at_da4 ?_; wn
    refine WP.branch ac_at_da8 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; rsimp at eb; rw [I.r9, eO, t0] at eb; exact absurd eb (by decide)
    refine WP.lw ac_at_daa (aceca_al O 0x1324 (by decide) (by decide)
      (by rsimp; rw [I.r9]; simp only [acSlot]; bv_omega)) ?_; wn
    refine WP.branch ac_at_dac (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; rsimp at eb; rw [I.r9, eO4, t4] at eb
      exact hq0 (by simpa [branchTaken] using eb)
    refine WP.lui ac_at_dae ?_; wn
    refine WP.aluImm ac_at_db0 ?_; wn
    refine WP.alu ac_at_db4 ?_; wn
    refine WP.lw ac_at_db8 (aceca_al O 0x1328 (by decide) (by decide)
      (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)) ?_; wn
    refine WP.lui ac_at_dba ?_; wn
    refine WP.aluImm ac_at_dbc ?_; wn
    refine WP.alu ac_at_dc0 ?_; wn
    refine WP.lui ac_at_dc2 ?_; wn
    refine WP.aluImm ac_at_dc4 ?_; wn
    refine WP.alu ac_at_dc8 ?_; wn
    have hq1 : X.D.toNat ≤ (p + BitVec.ofNat 32 pos).toNat := by omega
    have hq2 : (p + BitVec.ofNat 32 pos).toNat + el ≤ X.D.toNat + X.json.length := by omega
    have E2 := aceca_env O A hm2
    have eR4 : acSlot X.B 0x1FDC + 4 = acSlot X.B 0x1FE0 := aceca_slotC X.B 0x1FDC 4
    refine aceca_rc hrc O (fp := fp) (p := p + BitVec.ofNat 32 pos) (l := el) rfl hflo hfhi
      (by rsimp; exact R.rsp) (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega)
      (by rsimp; exact aceca_ldAt (by rw [I.r9]; simp only [acSlot]; bv_omega) t4)
      (by rsimp; exact aceca_ldAt (by rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega) t8)
      (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega) E2.chain (T2.fp.trans A.fr.ptr)
      (by rw [eR4, T2.fl]; exact A.fr.len) hq1 hq2 fun m3 hR3 hE3 => ?_
    generalize m3.mem = M3 at hR3 hE3
    have hj : JVal false (memBytes M2 (p + BitVec.ofNat 32 pos) el) j := by
      rw [aceca_docBytes O A hm2 hq1 hq2,
        show (p + BitVec.ofNat 32 pos).toNat - X.D.toNat = p.toNat - X.D.toNat + pos by rw [hq]; omega]
      exact (ace_den (by omega) hden).2
    have hv3 : ∀ x, AcaV X.B X.Bf fp x → M3 x = n0.mem x := fun x hx =>
      (aceca_rcV O hR3 hfhi x hx).trans (T2.mem x hx)
    rw [e4] at c4
    rw [e8] at c8 tc
    refine aceca_dd2 O A I (by hr) (by rsimp <;> rfl)
      (by rsimp; rw [R.rsp]; simp only [ev_add, acSlot]; bv_omega) (by rsimp; exact I.r18)
      (by rsimp; exact I.r20) (by rsimp; exact I.r22) hv3
      ⟨p, l, a, ?_, ?_, ?_, by omega, hp1, hpl, hEl'⟩ hR3.1 hE3
      (fun c s h => readChainPos_spec hj h)
    · rw [aceca_rcSlot O hR3 hbf hfhi (k := 0x1310) (by decide) (.inl (by decide)) (.inl (by decide)),
        aceca_erSlot O hf2 (k := 0x1310) (by decide) (.inl (by decide))]
      exact c0
    · rw [e4, aceca_rcSlot O hR3 hbf hfhi (k := 0x1314) (by decide) (.inl (by decide)) (.inl (by decide)),
        aceca_erSlot O hf2 (k := 0x1314) (by decide) (.inl (by decide))]
      exact c4
    · rw [e8, aceca_rcSlot O hR3 hbf hfhi (k := 0x1318) (by decide) (.inl (by decide)) (.inl (by decide))]
      exact tc

/-! ## The loop -/

/-- **The certificate-authority loop, 0xD8C to 0xEBA.** Given the error
bound on `read_chain` that `AcaRcErr` states. -/
theorem ace_ca (hrc : AcaRcErr) : AceCaStage := by
  intro X O n fp jr rest fs A I
  induction rest generalizing n fp fs with
  | nil =>
    obtain ⟨m', c, q⟩ := aceca_pass hrc O A I (by decide) A.code n A.st
    obtain ⟨inv, hq⟩ := q m' rfl rfl fun _ => rfl
    refine ⟨m', c, .inr ⟨inv, ?_⟩⟩
    rcases hq with hf | ⟨hpc, hp⟩ | ⟨-, j, rest', -, -, h, -⟩
    · exact .inl hf
    · exact .inr ⟨hpc, hp⟩
    · cases h
  | cons j rest ih =>
    obtain ⟨m', c, q⟩ := aceca_pass hrc O A I (by decide) A.code n A.st
    obtain ⟨inv, hq⟩ := q m' rfl rfl fun _ => rfl
    rcases hq with hf | ⟨hpc, hp⟩ | ⟨-, j', rest', fp', fs', h, A', I'⟩
    · exact ⟨m', c, .inr ⟨inv, .inl hf⟩⟩
    · exact ⟨m', c, .inr ⟨inv, .inr ⟨hpc, hp⟩⟩⟩
    · obtain ⟨-, rfl⟩ := List.cons.inj h
      obtain ⟨m'', c', q'⟩ := ih _ _ _ A' I'
      exact ⟨m'', c.trans c', q'⟩

end C3.RV32.Ac
