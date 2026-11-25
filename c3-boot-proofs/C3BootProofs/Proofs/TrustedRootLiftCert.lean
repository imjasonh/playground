import C3BootProofs.Proofs.TrustedRootLiftKey

/-!
# `parse_cert`'s model and the spec's `parseCert`

`rcParse` reads a certificate with readers, pairs of an offset and a
length into the certificate bytes `L`. When it accepts `L`, the spec's
`parseCert` accepts `L` too, with the serial number, issuer, subject,
validity, and P-384 key that `rcParse`'s offsets, lengths, and key address
name (`RcInfo`).
-/

namespace C3.RV32

open C3

/-- The certificate `c` that `rcParse` returned for bytes at `p` names
the fields of the spec's `info`: each field is the `rcView` of `D` at an
offset `a` with `c`'s address `p + a`, the window is `c`'s times, and the
key is the 97 bytes at `c`'s key address, or `none` when that address is
0. -/
structure RcInfo (D : Bytes) (p : Word) (c : RcCert) (info : CertInfo) : Prop where
  serial : ∃ a, c.serial = p + BitVec.ofNat 32 a ∧ a + c.serialLen ≤ D.length ∧
    info.serial = rcView D (a, c.serialLen)
  issuer : ∃ a, c.issuer = p + BitVec.ofNat 32 a ∧ a + c.issuerLen ≤ D.length ∧
    info.issuer = rcView D (a, c.issuerLen)
  subject : ∃ a, c.subject = p + BitVec.ofNat 32 a ∧ a + c.subjectLen ≤ D.length ∧
    info.subject = rcView D (a, c.subjectLen)
  window : info.window = ⟨c.notBefore, c.notAfter⟩
  key : TrkKey D p c.key info.p384Key

theorem rcSubj_spec {L : Bytes} {p : Word} {sr ir : RcRd} {nb na : Nat} {t : RcRd} {c : RcCert}
    (h : rcSubj L p sr ir nb na t = .ok c) :
    ∃ s k, derTlv (rcView L t) = .ok s ∧ derTlv (rcView L (rcAdv t s)) = .ok k ∧
      readElem 0x30 (rcView L t) = some (⟨0x30, rcView L (rcIn t s), rcView L (rcRaw t s)⟩, rcView L (rcAdv t s)) ∧
      readElem 0x30 (rcView L (rcAdv t s)) = some (⟨0x30, rcView L (rcIn (rcAdv t s) k),
        rcView L (rcRaw (rcAdv t s) k)⟩, rcView L (rcAdv (rcAdv t s) k)) ∧
      c = ⟨p + BitVec.ofNat 32 sr.1, sr.2, p + BitVec.ofNat 32 ir.1, ir.2, p + BitVec.ofNat 32 t.1,
        s.header + s.len, nb, na, rcKey L p (rcRaw (rcAdv t s) k)⟩ := by
  unfold rcSubj at h
  split at h
  · cases h
  rename_i s hs
  split at h
  · cases h
  rename_i k hk
  cases h
  have e1 := trc_rcElem hs
  have e2 := trc_rcElem hk
  exact ⟨s, k, Sv.derElement_tlv e1, Sv.derElement_tlv e2, trc_elem e1, trc_elem e2, rfl⟩


/-- `parseCert` from the serial number on. -/
def trcFromSerial (t : Bytes) : Option CertInfo := do
  let (serial, t) ← readElem 2 t
  let (_, t) ← readElem 0x30 t
  let (issuer, t) ← readElem 0x30 t
  let (validity, t) ← readElem 0x30 t
  let (notBefore, v) ← readTime validity.content
  let (notAfter, v) ← readTime v
  require v.isEmpty
  let (subject, t) ← readElem 0x30 t
  let (spki, _) ← readElem 0x30 t
  pure ⟨serial.raw, issuer.raw, subject.raw, ⟨notBefore, notAfter⟩, spkiP384 spki.raw⟩

theorem rcSerial_spec {L : Bytes} {p : Word} {t : RcRd} {c : RcCert} (h : rcSerial L p t = .ok c) :
    ∃ info, trcFromSerial (rcView L t) = some info ∧ RcInfo L p c info := by
  unfold rcSerial at h
  split at h
  · cases h
  rename_i s hs
  split at h
  · cases h
  rename_i a ha
  split at h
  · cases h
  rename_i i hi
  split at h
  · cases h
  rename_i v hv
  have es := trc_rcElem hs
  have ea := trc_rcElem ha
  have ei := trc_rcElem hi
  have ev := trc_rcElem hv
  unfold rcTimes at h
  split at h
  · cases h
  rename_i nb r1 h1
  split at h
  · cases h
  rename_i na r2 h2
  by_cases hr : r2.length ≠ 0
  · rw [ite_eq_left hr] at h; cases h
  rw [ite_eq_right hr] at h
  obtain ⟨s2, k, es2, ek, eS, eK, rfl⟩ := rcSubj_spec h
  have hlen := trc_inLen (Sv.derElement_tlv ev)
  have hr1 := trc_time2 hlen h1
  refine ⟨⟨rcView L (rcRaw t s), rcView L (rcRaw (rcAdv (rcAdv t s) a) i),
    rcView L (rcRaw (rcAdv (rcAdv (rcAdv (rcAdv t s) a) i) v) s2), ⟨nb, na⟩,
    spkiP384 (rcView L (rcRaw (rcAdv (rcAdv (rcAdv (rcAdv (rcAdv t s) a) i) v) s2) k))⟩, ?_, ?_⟩
  · unfold trcFromSerial
    rw [trc_elem es]
    dsimp only [bind, Option.bind]
    rw [trc_elem ea]
    dsimp only [bind, Option.bind]
    rw [trc_elem ei]
    dsimp only [bind, Option.bind]
    rw [trc_elem ev]
    dsimp only [bind, Option.bind]
    rw [h1]
    dsimp only [bind, Option.bind]
    rw [hr1, h2]
    dsimp only [bind, Option.bind]
    rw [List.eq_nil_of_length_eq_zero (Decidable.of_not_not hr)]
    rw [eS]
    dsimp only [bind, Option.bind]
    rw [eK]
    rfl
  · exact ⟨⟨_, rfl, trc_bound' (r := t) (Sv.derElement_tlv es), rfl⟩,
      ⟨_, rfl, trc_bound' (r := rcAdv (rcAdv t s) a) (Sv.derElement_tlv ei), rfl⟩,
      ⟨_, rfl, trc_bound' (r := rcAdv (rcAdv (rcAdv (rcAdv t s) a) i) v) es2, rfl⟩, rfl,
      rcKey_spec (r := rcRaw (rcAdv (rcAdv (rcAdv (rcAdv (rcAdv t s) a) i) v) s2) k)
        (trc_bound' (r := rcAdv (rcAdv (rcAdv (rcAdv (rcAdv t s) a) i) v) s2) ek)⟩


/-- When `rcParse` accepts the certificate bytes `L` at `p`, `parseCert`
accepts them too, with the fields that `rcParse`'s certificate names. -/
theorem rcParse_spec {L : Bytes} {p : Word} {c : RcCert} (h : rcParse L p = .ok c) :
    ∃ info, parseCert L = some info ∧ RcInfo L p c info := by
  unfold rcParse at h
  split at h
  · cases h
  rename_i ce hce
  have e0 := trc_elem (trc_rcElem hce)
  rw [trc_whole] at e0
  by_cases hl : L.length - (ce.header + ce.len) ≠ 0
  · rw [ite_eq_left hl] at h; cases h
  rw [ite_eq_right hl] at h
  unfold rcBody at h
  split at h
  · cases h
  rename_i tbs htbs
  split at h
  · cases h
  rename_i a ha
  split at h
  · cases h
  rename_i b hb
  by_cases hbits : ¬(b.len ≠ 0 ∧
      (rcView L (rcAdv (rcAdv (rcIn (0, L.length) ce) tbs) a)).getD b.header 0 = 0)
  · rw [ite_eq_left hbits] at h; cases h
  rw [ite_eq_right hbits] at h
  have hbits' := Decidable.of_not_not hbits
  by_cases hrest : (rcAdv (rcAdv (rcAdv (rcIn (0, L.length) ce) tbs) a) b).2 ≠ 0
  · rw [ite_eq_left hrest] at h; cases h
  rw [ite_eq_right hrest] at h
  have eT := trc_elem (trc_rcElem htbs)
  have eA := trc_elem (trc_rcElem ha)
  have eB := trc_bitString (trc_rcElem hb) hbits'.1 hbits'.2
  have hpre : parseCert L = (readOptional 0xA0 (rcView L (rcIn (rcIn (0, L.length) ce) tbs))) >>=
      fun x => trcFromSerial x.2 := by
    unfold parseCert
    rw [e0]
    dsimp only [bind, Option.bind]
    rw [trc_empty L (r := rcAdv (0, L.length) ce) (Decidable.of_not_not hl)]
    rw [eT]
    dsimp only [bind, Option.bind]
    rw [eA]
    dsimp only [bind, Option.bind]
    rw [eB]
    dsimp only [bind, Option.bind]
    rw [trc_empty L (r := rcAdv (rcAdv (rcAdv (rcIn (0, L.length) ce) tbs) a) b) (Decidable.of_not_not hrest)]
    rfl
  unfold rcTbs at h
  split at h
  · cases h
  · rename_i u hu
    obtain ⟨info, hs, hi⟩ := rcSerial_spec h
    obtain ⟨e, he⟩ := trc_opt hu
    refine ⟨info, ?_, hi⟩
    rw [hpre, he]
    exact hs
  · rename_i hu
    obtain ⟨info, hs, hi⟩ := rcSerial_spec h
    refine ⟨info, ?_, hi⟩
    rw [hpre, Sv.readOptional_none hu]
    exact hs

end C3.RV32
