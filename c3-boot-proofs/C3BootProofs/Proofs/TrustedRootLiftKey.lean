import C3BootProofs.Proofs.TrustedRootLiftDer
import C3BootProofs.Models.P384Model

/-!
# `p384_key`'s model and the spec's `spkiP384`

`rcKey L p r` is the address of the P-384 point in the
`SubjectPublicKeyInfo` that reader `r` names, or 0. `rcKey_spec` relates it
to the spec's `spkiP384` of the same bytes in both directions: when the
address isn't 0, `spkiP384` returns the 97 bytes at that address, and when
it is 0, `spkiP384` returns `none` (`TrkKey`).

The curve check is `from_sec1_bytes`'s: `rcFsOk` holds for 97 bytes exactly
when the spec's `p384.decodePoint` accepts them (`trk_decode`,
`trk_decodeNone`). The curve equation in Montgomery form follows from
`dqAlpha_mont`, which `fs_decode` uses for `sigstoreVerify`'s keys.
-/

namespace C3.RV32

open C3 C3.Models C3.RV32.Dq

/-! ## The curve check -/

set_option exponentiation.threshold 800 in
/-- The curve equation in Montgomery form, as `from_sec1_bytes` checks it,
holds exactly when `y² ≡ x³ + ax + b` modulo `p`. -/
theorem trk_mont (x y : Nat) :
    p3fm (y * 2 ^ 384 % p384) (y * 2 ^ 384 % p384) = dqAlpha (x * 2 ^ 384 % p384) ↔
      y * y % C3.p384.p = (x * x % C3.p384.p * x + C3.p384.a * x + C3.p384.b) % C3.p384.p := by
  have hYY : p3fm (y * 2 ^ 384 % p384) (y * 2 ^ 384 % p384) = y * y * 2 ^ 384 % p384 :=
    mont_mul p3_rinv' (Nat.mod_mod _ _) (Nat.mod_mod _ _)
  have h1 : x * x % p384 * x % p384 = x * x * x % p384 := Nat.mod_mul_mod _ _ _
  have h2 : (x * x % p384 * x + (p384 - 3) * x) % p384 = (x * x * x + (p384 - 3) * x) % p384 := by
    rw [Nat.add_mod, h1, ← Nat.add_mod]
  have h3 : (x * x % p384 * x + (p384 - 3) * x + C3.p384.b) % p384 =
      (x * x * x + (p384 - 3) * x + C3.p384.b) % p384 := by
    rw [Nat.add_mod (x * x % p384 * x + (p384 - 3) * x), h2, ← Nat.add_mod]
  rw [hYY, dqAlpha_mont, p384_p, show C3.p384.a = p384 - 3 by rw [← p384_p]; rfl, h3]
  constructor
  · exact mont_cancel p3_rinv'
  · intro h
    exact (Nat.mul_mod _ _ _).trans
      ((congrArg (fun z => z * (2 ^ 384 % p384) % p384) h).trans (Nat.mul_mod _ _ _).symm)

theorem trk_and {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

theorem trk_yEq {B : Bytes} (hl : B.length = 97) : (B.drop 0x31).take 48 = B.drop 49 :=
  List.take_of_length_le (by rw [List.length_drop, hl]; exact Nat.le_refl _)

/-- 97 bytes that `from_sec1_bytes` accepts decode to the same point. -/
theorem trk_decode {B : Bytes} (hl : B.length = 97) (h : rcFsOk B) :
    C3.p384.decodePoint B = some (beNat ((B.drop 1).take 48), beNat ((B.drop 0x31).take 48)) := by
  obtain ⟨h4, hx, hy, he⟩ := h
  refine decode_some (by rw [hl]; rfl) ?_ rfl ?_ (p384_p ▸ hx) (p384_p ▸ hy) ((trk_mont _ _).1 he)
  · cases B with
    | nil => cases hl
    | cons b bs => exact congrArg some h4
  · rw [trk_yEq hl]
    rfl

/-- 97 bytes that `from_sec1_bytes` rejects don't decode. -/
theorem trk_decodeNone {B : Bytes} (hl : B.length = 97) (h : ¬rcFsOk B) : C3.p384.decodePoint B = none := by
  unfold Curve.decodePoint require
  simp only [Option.bind_eq_bind]
  split
  · rename_i h1
    rw [Option.bind_some]
    split
    · rename_i h2
      exfalso
      apply h
      have h4 : B.head? = some 4 := beq_iff_eq.mp (trk_and h1).2
      obtain ⟨h23, he⟩ := trk_and h2
      obtain ⟨hx, hy⟩ := trk_and h23
      have hx' : beNat ((B.drop 1).take 48) < C3.p384.p := of_decide_eq_true hx
      have hy' : beNat ((B.drop 0x31).take 48) < C3.p384.p := by
        rw [trk_yEq hl]; exact of_decide_eq_true hy
      have he' : beNat ((B.drop 0x31).take 48) * beNat ((B.drop 0x31).take 48) % C3.p384.p =
          (beNat ((B.drop 1).take 48) * beNat ((B.drop 1).take 48) % C3.p384.p * beNat ((B.drop 1).take 48) +
            C3.p384.a * beNat ((B.drop 1).take 48) + C3.p384.b) % C3.p384.p := by
        rw [trk_yEq hl]; exact beq_iff_eq.mp he
      unfold rcFsOk
      refine ⟨?_, p384_p ▸ hx', p384_p ▸ hy', (trk_mont _ _).2 he'⟩
      cases B with
      | nil => cases h4
      | cons b bs => exact Option.some.inj h4
    · rfl
  · rfl

/-! ## Readers that fit -/

theorem trk_viewLen {L : Bytes} {r : RcRd} (hf : r.1 + r.2 ≤ L.length) : (rcView L r).length = r.2 := by
  unfold rcView
  rw [List.length_take, List.length_drop]
  exact Nat.min_eq_left (by omega)

theorem trk_ne {L : Bytes} {r : RcRd} (hf : r.1 + r.2 ≤ L.length) (h : r.2 ≠ 0) :
    (rcView L r).isEmpty = false := by
  have hl := trk_viewLen hf
  revert hl
  cases rcView L r with
  | nil => intro hl; exact absurd hl.symm h
  | cons _ _ => intro _; rfl

theorem trk_fitIn {L : Bytes} {r : RcRd} {t : DerTlv} (h : derTlv (rcView L r) = .ok t) :
    (rcIn r t).1 + (rcIn r t).2 ≤ L.length := by
  have := trc_bound' h
  show r.1 + t.header + t.len ≤ L.length
  omega

theorem trk_fitAdv {L : Bytes} {r : RcRd} {t : DerTlv} (hf : r.1 + r.2 ≤ L.length)
    (h : derTlv (rcView L r) = .ok t) : (rcAdv r t).1 + (rcAdv r t).2 ≤ L.length := by
  have := trc_bound h
  show r.1 + (t.header + t.len) + (r.2 - (t.header + t.len)) ≤ L.length
  omega

theorem trk_tail (L : Bytes) (q n : Nat) : (rcView L (q, n)).tail = rcView L (q + 1, n - 1) := by
  unfold rcView
  dsimp only
  rw [← List.tail_drop]
  generalize L.drop q = X
  cases n with
  | zero => cases X <;> rfl
  | succ n =>
    rw [Nat.add_sub_cancel]
    cases X with
    | nil => exact List.take_nil.symm
    | cons x xs => rfl

/-! ## The DER reads that fail -/

theorem trk_tlvNone {X : Bytes} {e : DerError} (h : derTlv X = .error e) : readTlv X = none := by
  unfold readTlv
  rw [h]

theorem trk_elemNone {tag : Nat} {X : Bytes} {e : DerError} (h : derElement tag X = .error e) :
    readElem tag X = none := by
  unfold readElem
  cases X with
  | nil => rfl
  | cons b rest =>
    change (if b = tag then derTlv (b :: rest) else .error .badDer) = _ at h
    by_cases hb : b = tag
    · rw [ite_eq_left hb] at h
      rw [show ((b :: rest).head? == some tag) = true by rw [hb]; exact Sv.some_beq_self tag, ite_eq_left rfl]
      exact trk_tlvNone h
    · rw [show ((b :: rest).head? == some tag) = false from beq_false_of_ne (fun e => hb (Option.some.inj e))]
      rfl

theorem trk_oidTlv {X : Bytes} {o : DerTlv} (h : derOid X = .ok o) : derTlv X = .ok o := by
  unfold derOid at h
  split at h
  · cases h
  · rename_i t he
    split at h
    · cases h
      exact Sv.derElement_tlv he
    · cases h

theorem trk_oidNone {X : Bytes} {e : DerError} (h : derOid X = .error e) : readOid X = none := by
  unfold derOid at h
  split at h
  · rename_i e' he
    unfold readOid
    rw [trk_elemNone he]
    rfl
  · rename_i t he
    by_cases hok : derOidOk (t.content X) = true
    · rw [ite_eq_left hok] at h
      cases h
    · unfold readOid
      rw [Sv.readElem_of he]
      simp only [Sv.elemOf, Option.bind_eq_bind, Option.bind_some]
      unfold require
      rw [ite_eq_right hok]
      rfl

theorem trk_oid {L : Bytes} {r : RcRd} {o : DerTlv} (h : derOid (rcView L r) = .ok o) :
    readOid (rcView L r) = some (rcView L (rcIn r o), rcView L (rcAdv r o)) := by
  have ht := trk_oidTlv h
  rw [Sv.readOid_of h]
  unfold Sv.elemOf
  dsimp only
  rw [trc_content ht, trc_adv]
  rfl

/-! ## The algorithm -/

/-- The parameters of an algorithm as the spec's `readAlgorithm` returns
them, for the parameters `rcAlg` returns. -/
def trkPar (L : Bytes) : Option (Nat × DerTlv) → Option Elem
  | none => none
  | some (q, u) => some ⟨u.tag, rcView L (q + u.header, u.len), rcView L (q, u.header + u.len)⟩

theorem trk_any (L : Bytes) (par : Option (Nat × DerTlv)) :
    (trkPar L par).any (fun p => p.tag == 6 && p.content == oidSecp384r1) = rcCurveOk L par := by
  cases par with
  | none => rfl
  | some qu => rfl

theorem trk_alg {L : Bytes} {r : RcRd} {a : DerTlv} {oo ol : Nat} {par : Option (Nat × DerTlv)}
    (ha : derElement 0x30 (rcView L r) = .ok a) (h : rcAlg L r = .ok ((oo, ol), par)) :
    readAlgorithm (rcView L r) = some ((rcView L (oo, ol), trkPar L par), rcView L (rcAdv r a)) := by
  unfold rcAlg at h
  split at h
  · cases h
  rename_i t ht
  have hat : a = t := Except.ok.inj (ha.symm.trans ht)
  subst hat
  split at h
  · cases h
  rename_i o ho
  have eO : readOid (rcView L (rcIn r a)) = some (rcView L (rcIn (rcIn r a) o), rcView L (rcAdv (rcIn r a) o)) :=
    trk_oid ho
  have hfo : (rcAdv (rcIn r a) o).1 + (rcAdv (rcIn r a) o).2 ≤ L.length :=
    trk_fitAdv (trk_fitIn (Sv.derElement_tlv ha)) (trk_oidTlv ho)
  unfold readAlgorithm
  rw [trc_elem ha]
  dsimp only [bind, Option.bind]
  rw [eO]
  dsimp only [bind, Option.bind]
  by_cases hz : a.len - (o.header + o.len) = 0
  · rw [ite_eq_left hz] at h
    cases h
    rw [trc_empty L (r := rcAdv (rcIn r a) o) hz]
    rfl
  rw [ite_eq_right hz] at h
  split at h
  · cases h
  rename_i u hu
  by_cases hu2 : u.header + u.len = a.len - (o.header + o.len)
  · rw [ite_eq_left hu2] at h
    cases h
    have eU : readTlv (rcView L (rcAdv (rcIn r a) o)) =
        some (⟨u.tag, rcView L (rcIn (rcAdv (rcIn r a) o) u), rcView L (rcRaw (rcAdv (rcIn r a) o) u)⟩,
          rcView L (rcAdv (rcAdv (rcIn r a) o) u)) := trc_tlv hu
    rw [trk_ne hfo hz, ite_eq_right Bool.false_ne_true, eU]
    dsimp only [bind, Option.bind]
    rw [trc_empty L (r := rcAdv (rcAdv (rcIn r a) o) u)
      (by show a.len - (o.header + o.len) - (u.header + u.len) = 0; omega)]
    rfl
  · rw [ite_eq_right hu2] at h
    cases h

theorem trk_algNone {L : Bytes} {r : RcRd} (h : rcAlg L r = .error ()) : readAlgorithm (rcView L r) = none := by
  unfold rcAlg at h
  split at h
  · rename_i e he
    unfold readAlgorithm
    rw [trk_elemNone he]
    rfl
  rename_i a ha
  unfold readAlgorithm
  rw [trc_elem ha]
  dsimp only [bind, Option.bind]
  split at h
  · rename_i e ho
    rw [trk_oidNone (X := rcView L (rcIn r a)) ho]
  rename_i o ho
  have eO : readOid (rcView L (rcIn r a)) = some (rcView L (rcIn (rcIn r a) o), rcView L (rcAdv (rcIn r a) o)) :=
    trk_oid ho
  have hfo : (rcAdv (rcIn r a) o).1 + (rcAdv (rcIn r a) o).2 ≤ L.length :=
    trk_fitAdv (trk_fitIn (Sv.derElement_tlv ha)) (trk_oidTlv ho)
  rw [eO]
  dsimp only [bind, Option.bind]
  by_cases hz : a.len - (o.header + o.len) = 0
  · rw [ite_eq_left hz] at h
    cases h
  rw [ite_eq_right hz] at h
  rw [trk_ne hfo hz, ite_eq_right Bool.false_ne_true]
  split at h
  · rename_i e hu
    rw [trk_tlvNone (X := rcView L (rcAdv (rcIn r a) o)) hu]
  rename_i u hu
  by_cases hu2 : u.header + u.len = a.len - (o.header + o.len)
  · rw [ite_eq_left hu2] at h
    cases h
  have eU : readTlv (rcView L (rcAdv (rcIn r a) o)) =
      some (⟨u.tag, rcView L (rcIn (rcAdv (rcIn r a) o) u), rcView L (rcRaw (rcAdv (rcIn r a) o) u)⟩,
        rcView L (rcAdv (rcAdv (rcIn r a) o) u)) := trc_tlv hu
  have hb : u.header + u.len ≤ a.len - (o.header + o.len) := trc_bound hu
  rw [eU]
  dsimp only [bind, Option.bind]
  rw [trk_ne (trk_fitAdv hfo hu) (by show a.len - (o.header + o.len) - (u.header + u.len) ≠ 0; omega)]
  rfl

/-! ## The key -/

/-- `spkiP384` after its outer `SEQUENCE`. -/
def trkInner (seq : Bytes) : Option Bytes := do
  let ((alg, params), inner) ← readAlgorithm seq
  require (alg == oidEcPublicKey && params.any (fun p => p.tag == 6 && p.content == oidSecp384r1))
  let (point, inner) ← readBitString inner
  require (point.length == 97 && inner.isEmpty && (C3.p384.decodePoint point).isSome)
  pure point

/-- `spkiP384` after its algorithm. -/
def trkPoint (bits : Bytes) : Option Bytes := do
  let (point, inner) ← readBitString bits
  require (point.length == 97 && inner.isEmpty && (C3.p384.decodePoint point).isSome)
  pure point

theorem trk_bitsNone {L : Bytes} {b : RcRd} {bt : DerTlv} (hb : derElement 3 (rcView L b) = .ok bt)
    (h : ¬(bt.len ≠ 0 ∧ (rcView L b).getD bt.header 0 = 0)) : readBitString (rcView L b) = none := by
  have ht := Sv.derElement_tlv hb
  have hl := Sv.tlv_content_length (derTlv_bound ht)
  unfold readBitString
  rw [trc_elem hb]
  dsimp only [bind, Option.bind]
  rw [← trc_content ht]
  revert hl
  cases e : bt.content (rcView L b) with
  | nil => intro _; rfl
  | cons y ys =>
    intro hl
    have hg := Sv.tlv_content_getD (L := rcView L b) (t := bt) (i := 0) (by rw [← hl]; exact Nat.succ_pos _)
    rw [e, Nat.add_zero] at hg
    cases y with
    | zero => exact absurd ⟨by rw [← hl]; exact Nat.succ_ne_zero _, hg.symm⟩ h
    | succ y => rfl

/-- The key a certificate's `SubjectPublicKeyInfo` holds: the address `p + a`
of the 97 bytes at `a` in `L` that `spkiP384` returns, or 0 when
`spkiP384` returns `none`. -/
def TrkKey (L : Bytes) (p : Word) (key : Word) (pk : Option Bytes) : Prop :=
  (∃ a, key = p + BitVec.ofNat 32 a ∧ a + 0x61 ≤ L.length ∧ pk = some (rcView L (a, 0x61))) ∨
    (key = 0 ∧ pk = none)

/-- `p384_key`'s model on a `SubjectPublicKeyInfo` that fits in `L` agrees
with the spec's `spkiP384`: a key address that isn't 0 names the point
`spkiP384` returns, and 0 means that `spkiP384` returns `none`. -/
theorem rcKey_spec {L : Bytes} {p : Word} {r : RcRd} (hf : r.1 + r.2 ≤ L.length) :
    TrkKey L p (rcKey L p r) (spkiP384 (rcView L r)) := by
  unfold rcKey
  split
  · rename_i e he
    refine Or.inr ⟨rfl, ?_⟩
    unfold spkiP384
    rw [trk_elemNone he]
    rfl
  rename_i s hs
  have tS := Sv.derElement_tlv hs
  by_cases h1 : r.2 - (s.header + s.len) ≠ 0
  · rw [ite_eq_left h1]
    refine Or.inr ⟨rfl, ?_⟩
    unfold spkiP384
    rw [trc_elem hs]
    dsimp only [bind, Option.bind]
    rw [trk_ne (trk_fitAdv hf tS) h1]
    rfl
  rw [ite_eq_right h1]
  have hsp : spkiP384 (rcView L r) = trkInner (rcView L (rcIn r s)) := by
    unfold spkiP384 trkInner
    rw [trc_elem hs]
    dsimp only [bind, Option.bind]
    rw [trc_empty L (r := rcAdv r s) (Decidable.of_not_not h1)]
    rfl
  rw [hsp]
  have hfi := trk_fitIn tS
  split
  · rename_i e he
    refine Or.inr ⟨rfl, ?_⟩
    unfold trkInner readAlgorithm
    rw [trk_elemNone he]
    rfl
  rename_i a ha
  split
  · rename_i hal
    refine Or.inr ⟨rfl, ?_⟩
    unfold trkInner
    rw [trk_algNone hal]
    rfl
  rename_i oo ol par hal
  have eA := trk_alg ha hal
  by_cases hc : rcCurveOk L par = false
  · rw [ite_eq_left hc]
    refine Or.inr ⟨rfl, ?_⟩
    unfold trkInner
    rw [eA]
    dsimp only [bind, Option.bind]
    rw [trk_any, hc, Bool.and_false]
    rfl
  rw [ite_eq_right hc]
  by_cases ho : rcView L (oo, ol) ≠ oidEcPublicKey
  · rw [ite_eq_left ho]
    refine Or.inr ⟨rfl, ?_⟩
    unfold trkInner
    rw [eA]
    dsimp only [bind, Option.bind]
    rw [beq_false_of_ne ho, Bool.false_and]
    rfl
  rw [ite_eq_right ho]
  have hcT : rcCurveOk L par = true := by
    cases e : rcCurveOk L par
    · exact absurd e hc
    · rfl
  have hpt : trkInner (rcView L (rcIn r s)) = trkPoint (rcView L (rcAdv (rcIn r s) a)) := by
    unfold trkInner trkPoint
    rw [eA]
    dsimp only [bind, Option.bind]
    rw [trk_any, hcT, Decidable.of_not_not ho]
    rfl
  rw [hpt]
  have hfb := trk_fitAdv hfi (Sv.derElement_tlv ha)
  try dsimp only
  split
  · rename_i e he
    refine Or.inr ⟨rfl, ?_⟩
    unfold trkPoint readBitString
    rw [trk_elemNone he]
    rfl
  rename_i bt hbt
  have tB := Sv.derElement_tlv hbt
  have hbB := trc_bound' tB
  by_cases hb1 : ¬(bt.len ≠ 0 ∧ (rcView L (rcAdv (rcIn r s) a)).getD bt.header 0 = 0)
  · rw [ite_eq_left hb1]
    refine Or.inr ⟨rfl, ?_⟩
    unfold trkPoint
    rw [trk_bitsNone hbt hb1]
    rfl
  rw [ite_eq_right hb1]
  have hb1' := Decidable.of_not_not hb1
  have eB := trc_bitString hbt hb1'.1 hb1'.2
  rw [show rcIn (rcAdv (rcIn r s) a) bt = ((rcAdv (rcIn r s) a).1 + bt.header, bt.len) from rfl,
    trk_tail] at eB
  have hfp : (rcAdv (rcIn r s) a).1 + bt.header + 1 + (bt.len - 1) ≤ L.length := by
    have := hb1'.1
    omega
  by_cases hb2 : bt.len - 1 ≠ 0x61
  · rw [ite_eq_left hb2]
    refine Or.inr ⟨rfl, ?_⟩
    unfold trkPoint
    rw [eB]
    dsimp only [bind, Option.bind]
    rw [trk_viewLen hfp, beq_false_of_ne hb2, Bool.false_and, Bool.false_and]
    rfl
  rw [ite_eq_right hb2]
  have h97 := Decidable.of_not_not hb2
  rw [h97] at eB hfp
  by_cases hb3 : (rcAdv (rcIn r s) a).2 - (bt.header + bt.len) ≠ 0
  · rw [ite_eq_left hb3]
    refine Or.inr ⟨rfl, ?_⟩
    unfold trkPoint
    rw [eB]
    dsimp only [bind, Option.bind]
    rw [trk_viewLen hfp, trk_ne (trk_fitAdv hfb tB) hb3]
    rfl
  rw [ite_eq_right hb3]
  have hE := trc_empty L (r := rcAdv (rcAdv (rcIn r s) a) bt) (Decidable.of_not_not hb3)
  by_cases hfs : rcFsOk (rcView L ((rcAdv (rcIn r s) a).1 + bt.header + 1, 0x61))
  · rw [ite_eq_left hfs]
    refine Or.inl ⟨_, rfl, hfp, ?_⟩
    unfold trkPoint
    rw [eB]
    dsimp only [bind, Option.bind]
    rw [trk_viewLen hfp, hE, trk_decode (trk_viewLen hfp) hfs]
    rfl
  · rw [ite_eq_right hfs]
    refine Or.inr ⟨rfl, ?_⟩
    unfold trkPoint
    rw [eB]
    dsimp only [bind, Option.bind]
    rw [trk_viewLen hfp, hE, trk_decodeNone (trk_viewLen hfp) hfs]
    rfl

end C3.RV32
