import C3BootProofs.Proofs.SvVerifyAt
import C3BootProofs.Spec.DerRead

/-!
# `sigstore::verify` against `sigstoreVerify`: the DER readers

The stages state what the code parsed with the element reader of
`Spec/Der.lean` (`derElement`, `derOid`, `derContent`); `sigstoreVerify`
reads with the `Der` helpers of `Spec/DerRead.lean`, which are built on the
same reader. These lemmas turn the first into the second.
-/

namespace C3.RV32.Sv

/-- What `readTlv` returns for an element `derTlv` read. -/
def elemOf (t : DerTlv) (L : Bytes) : Elem × Bytes :=
  (⟨t.tag, t.content L, L.take (t.header + t.len)⟩, L.drop (t.header + t.len))

theorem readTlv_of {L : Bytes} {t : DerTlv} (h : derTlv L = .ok t) : readTlv L = some (elemOf t L) := by
  unfold readTlv elemOf; rw [h]

theorem derElement_tag {tag : Nat} {L : Bytes} {t : DerTlv} (h : derElement tag L = .ok t) :
    L.head? = some tag := by
  unfold derElement at h
  split at h
  · cases h
  · rename_i a l
    split at h
    · rename_i ha
      rw [ha]; rfl
    · cases h

theorem derElement_tlv {tag : Nat} {L : Bytes} {t : DerTlv} (h : derElement tag L = .ok t) : derTlv L = .ok t := by
  unfold derElement at h
  split at h
  · cases h
  · split at h
    · exact h
    · cases h

theorem some_beq_self (n : Nat) : (some n == some n) = true := decide_eq_true rfl

theorem readElem_of {tag : Nat} {L : Bytes} {t : DerTlv} (h : derElement tag L = .ok t) :
    readElem tag L = some (elemOf t L) := by
  unfold readElem
  rw [derElement_tag h, ite_eq_left (some_beq_self tag)]
  exact readTlv_of (derElement_tlv h)

theorem readOid_of {L : Bytes} {t : DerTlv} (h : derOid L = .ok t) :
    readOid L = some ((elemOf t L).1.content, (elemOf t L).2) := by
  unfold derOid at h
  split at h
  · cases h
  · rename_i t' he
    split at h
    · rename_i hok
      cases h
      unfold readOid
      rw [readElem_of he]
      simp only [elemOf, Option.bind_eq_bind, Option.bind_some]
      unfold require
      rw [ite_eq_left hok]
      rfl
    · cases h

end C3.RV32.Sv
