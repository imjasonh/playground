import C3BootProofs.Proofs.TrustedRootReadChainModel
import C3BootProofs.Proofs.SvDerBridge
import C3BootProofs.Spec.TrustedRoot

/-!
# Readers and the spec's DER reads

`read_chain`'s model reads DER with readers, pairs of an offset and a
length into the certificate bytes `L`, and `rcView L r` is the bytes that
reader `r` names. The lemmas here turn the model's reads into the spec's
`readTlv`, `readElem`, `readOptional`, `readTime`, and `readBitString` on
those views.
-/

namespace C3.RV32

open C3

theorem trc_dropTake : ∀ (i j : Nat) (l : Bytes), (l.take j).drop i = (l.drop i).take (j - i)
  | 0, j, l => by rw [List.drop_zero, List.drop_zero, Nat.sub_zero]
  | i + 1, 0, l => by rw [List.take_zero, List.drop_nil, Nat.zero_sub, List.take_zero]
  | i + 1, j + 1, [] => by simp only [List.take_nil, List.drop_nil]
  | i + 1, j + 1, x :: xs => by
    rw [List.take_succ_cons, List.drop_succ_cons, List.drop_succ_cons, Nat.add_sub_add_right]
    exact trc_dropTake i j xs

theorem trc_viewLen (L : Bytes) (r : RcRd) : (rcView L r).length ≤ r.2 := by
  unfold rcView
  rw [List.length_take]
  exact Nat.min_le_left _ _

theorem trc_viewLen' (L : Bytes) (r : RcRd) : (rcView L r).length ≤ L.length - r.1 := by
  unfold rcView
  rw [List.length_take, List.length_drop]
  exact Nat.min_le_right _ _

theorem trc_bound {L : Bytes} {r : RcRd} {t : DerTlv} (h : derTlv (rcView L r) = .ok t) :
    t.header + t.len ≤ r.2 :=
  Nat.le_trans (derTlv_bound h) (trc_viewLen L r)

theorem trc_bound' {L : Bytes} {r : RcRd} {t : DerTlv} (h : derTlv (rcView L r) = .ok t) :
    r.1 + (t.header + t.len) ≤ L.length := by
  have h1 := derTlv_bound h
  have h2 := trc_viewLen' L r
  have h3 : rcView L r ≠ [] := fun e => by rw [e] at h; cases h
  have h4 : 0 < (rcView L r).length := List.length_pos_iff.mpr h3
  omega

theorem trc_content {L : Bytes} {r : RcRd} {t : DerTlv} (h : derTlv (rcView L r) = .ok t) :
    t.content (rcView L r) = rcView L (rcIn r t) := by
  have hb := trc_bound h
  unfold DerTlv.content rcView rcIn
  rw [trc_dropTake, List.drop_drop, List.take_take]
  exact congrArg (fun k => List.take k _) (Nat.min_eq_left (by omega))

theorem trc_raw {L : Bytes} {r : RcRd} {t : DerTlv} (h : derTlv (rcView L r) = .ok t) :
    (rcView L r).take (t.header + t.len) = rcView L (rcRaw r t) := by
  have hb := trc_bound h
  unfold rcView rcRaw
  rw [List.take_take]
  exact congrArg (fun k => List.take k _) (Nat.min_eq_left hb)

theorem trc_adv (L : Bytes) (r : RcRd) (k : Nat) :
    (rcView L r).drop k = rcView L (r.1 + k, r.2 - k) := by
  unfold rcView
  rw [trc_dropTake, List.drop_drop]

theorem trc_tlv {L : Bytes} {r : RcRd} {t : DerTlv} (h : derTlv (rcView L r) = .ok t) :
    readTlv (rcView L r) = some (⟨t.tag, rcView L (rcIn r t), rcView L (rcRaw r t)⟩, rcView L (rcAdv r t)) := by
  rw [Sv.readTlv_of h]
  unfold Sv.elemOf
  rw [trc_content h, trc_raw h, trc_adv]
  rfl

theorem trc_elem {L : Bytes} {tag : Nat} {r : RcRd} {t : DerTlv} (h : derElement tag (rcView L r) = .ok t) :
    readElem tag (rcView L r) =
      some (⟨tag, rcView L (rcIn r t), rcView L (rcRaw r t)⟩, rcView L (rcAdv r t)) := by
  rw [Sv.readElem_of h]
  unfold Sv.elemOf
  rw [trc_content (Sv.derElement_tlv h), trc_raw (Sv.derElement_tlv h), trc_adv, Sv.derElement_tag_eq h]
  rfl

theorem trc_rcElem {L : Bytes} {tag : Nat} {r : RcRd} {t : DerTlv} (h : rcElem L tag r = .ok t) :
    derElement tag (rcView L r) = .ok t := by
  unfold rcElem at h
  split at h
  · cases h
  · rename_i t' ht
    cases h
    exact ht

theorem trc_empty (L : Bytes) {r : RcRd} (h : r.2 = 0) : rcView L r = [] := by
  unfold rcView
  rw [h]
  rfl

theorem trc_timeSuffix {X r : Bytes} {n : Nat} (h : readTime X = some (n, r)) : ∃ k, r = X.drop k := by
  unfold readTime at h
  cases ht : readTlv X with
  | none => rw [ht] at h; cases h
  | some er =>
    obtain ⟨e, r'⟩ := er
    have hr' : ∃ k, r' = X.drop k := by
      unfold readTlv at ht; split at ht
      · cases ht; exact ⟨_, rfl⟩
      · cases ht
    rw [ht] at h
    dsimp only [bind, Option.bind] at h
    split at h
    · split at h
      · cases h
      · cases h; exact hr'
    · split at h
      · split at h
        · cases h
        · cases h; exact hr'
      · cases h

theorem trc_inLen {L : Bytes} {r : RcRd} {t : DerTlv} (h : derTlv (rcView L r) = .ok t) :
    (rcView L (rcIn r t)).length = t.len := by
  rw [← trc_content h]
  exact Sv.tlv_content_length (derTlv_bound h)

theorem trc_suffix {L : Bytes} {r : RcRd} (k : Nat) (hlen : (rcView L r).length = r.2) :
    (rcView L r).drop k =
      rcView L (r.1 + (r.2 - ((rcView L r).drop k).length), ((rcView L r).drop k).length) := by
  rw [List.length_drop, hlen]
  by_cases hk : k ≤ r.2
  · rw [show r.2 - (r.2 - k) = k from by omega]
    exact trc_adv L r k
  · rw [show r.2 - k = 0 from by omega, trc_empty L (rfl : (r.1 + (r.2 - 0), 0).2 = 0)]
    exact List.drop_eq_nil_of_le (by omega)

theorem trc_time2 {L : Bytes} {r : RcRd} {n : Nat} {r1 : Bytes} (hlen : (rcView L r).length = r.2)
    (h : readTime (rcView L r) = some (n, r1)) : r1 = rcView L (r.1 + (r.2 - r1.length), r1.length) := by
  obtain ⟨k, rfl⟩ := trc_timeSuffix h
  exact trc_suffix k hlen

theorem trc_opt {L : Bytes} {r : RcRd} {u : DerTlv} (h : derOptRes 0xA0 (rcView L r) = some (.ok u)) :
    ∃ e, readOptional 0xA0 (rcView L r) = some (some e, rcView L (rcAdv r u)) := by
  revert h
  generalize hX : rcView L r = X
  intro h
  cases X with
  | nil => cases h
  | cons b rest =>
    change (if b = 0xA0 then some (derTlv (b :: rest)) else none) = _ at h
    by_cases hb : b = 0xA0
    · rw [ite_eq_left hb] at h
      have ht : derTlv (rcView L r) = .ok u := by rw [hX]; exact Option.some.inj h
      have := trc_tlv ht
      rw [hX] at this
      refine ⟨⟨u.tag, rcView L (rcIn r u), rcView L (rcRaw r u)⟩, ?_⟩
      unfold readOptional
      subst hb
      rw [show ((0xA0 :: rest).head? == some 0xA0) = true from Sv.some_beq_self 0xA0, ite_eq_left rfl, this]
      rfl
    · rw [ite_eq_right hb] at h
      cases h

theorem trc_bits {X : Bytes} {t : DerTlv} (hB : t.header + t.len ≤ X.length) (h0 : t.len ≠ 0)
    (hg : X.getD t.header 0 = 0) : t.content X = 0 :: (t.content X).tail := by
  have hl := Sv.tlv_content_length hB
  have hg' := Sv.tlv_content_getD (L := X) (t := t) (i := 0) (Nat.pos_of_ne_zero h0)
  rw [Nat.add_zero, hg] at hg'
  revert hl hg'
  generalize t.content X = Y
  intro hl hg'
  cases Y with
  | nil => exact absurd hl.symm h0
  | cons y ys => cases hg'; rfl

theorem trc_whole (L : Bytes) : rcView L (0, L.length) = L := by
  unfold rcView
  rw [List.drop_zero, List.take_length]


theorem trc_bitString {L : Bytes} {r : RcRd} {b : DerTlv} (hb : derElement 3 (rcView L r) = .ok b)
    (h0 : b.len ≠ 0) (hg : (rcView L r).getD b.header 0 = 0) :
    readBitString (rcView L r) = some ((rcView L (rcIn r b)).tail, rcView L (rcAdv r b)) := by
  have ht := Sv.derElement_tlv hb
  have hc := trc_bits (derTlv_bound ht) h0 hg
  rw [trc_content ht] at hc
  unfold readBitString
  rw [trc_elem hb]
  dsimp only [bind, Option.bind]
  rw [hc]
  rfl

end C3.RV32
