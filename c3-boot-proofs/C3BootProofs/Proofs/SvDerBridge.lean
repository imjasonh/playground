import C3BootProofs.Proofs.IsSha256
import C3BootProofs.Proofs.EcdsaSig
import C3BootProofs.Proofs.ListsOid
import C3BootProofs.Proofs.IntegerIs
import C3BootProofs.Proofs.X509ReadTime
import C3BootProofs.Spec.DerRead

/-!
# The code's DER results as the `Der` helpers'

The stages of `sigstore::verify` state what the code parsed with the element
reader of `Spec/Der.lean` (`derElement`, `derOid`) and with what each
compiled `Der` helper returns for bytes in memory (`derContent`,
`derBitsOf`, `derIntOf`, `derAlgOf`, and so on). `sigstoreVerify` reads with
the `Der` helpers of `Spec/DerRead.lean`, which are built on the same
element reader. These lemmas turn the first into the second, for the `l`
bytes at `p`: an element `t` read there has its contents at
`p + t.header` and leaves the bytes at `p + (t.header + t.len)`.
-/

namespace C3.RV32.Sv

open C3.Image

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

theorem ofNat_toNat_lt {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k).toNat = k := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem subK_toNat {l : Word} {k : Nat} (h : k ≤ l.toNat) :
    (l - BitVec.ofNat 32 k).toNat = l.toNat - k := by
  have hl := l.isLt
  rw [BitVec.toNat_sub, ofNat_toNat_lt (by omega)]
  omega

/-- The element `t` at the front of the `l` bytes at `p`. -/
def elemAt (M : Word → BitVec 8) (p : Word) (t : DerTlv) : Elem :=
  ⟨t.tag, memBytes M (p + BitVec.ofNat 32 t.header) (BitVec.ofNat 32 t.len).toNat,
    memBytes M p (BitVec.ofNat 32 (t.header + t.len)).toNat⟩

/-- The bytes after the element `t` at the front of the `l` bytes at `p`. -/
def restAt (M : Word → BitVec 8) (p l : Word) (t : DerTlv) : Bytes :=
  memBytes M (p + BitVec.ofNat 32 (t.header + t.len)) (l - BitVec.ofNat 32 (t.header + t.len)).toNat

theorem derTlv_mem_bound {M : Word → BitVec 8} {p l : Word} {t : DerTlv} (h : derTlv (memBytes M p l.toNat) = .ok t) :
    t.header + t.len ≤ l.toNat := by
  have := derTlv_bound h
  rwa [memBytes_length] at this

theorem memBytes_dropK' (M : Word → BitVec 8) (p : Word) {k n : Nat} (h : k ≤ n) :
    (memBytes M p n).drop k = memBytes M (p + BitVec.ofNat 32 k) (n - k) := by
  have := memBytes_split M p k (n - k)
  rw [show k + (n - k) = n by omega] at this
  rw [this, List.drop_left' (memBytes_length M p k)]

theorem elemOf_mem {M : Word → BitVec 8} {p l : Word} {t : DerTlv} (h : t.header + t.len ≤ l.toNat) :
    elemOf t (memBytes M p l.toNat) = (elemAt M p t, restAt M p l t) := by
  have hl := l.isLt
  unfold elemOf elemAt restAt DerTlv.content
  rw [memBytes_drop_take h, memBytes_take' h, memBytes_dropK' M p h, subK_toNat h, ofNat_toNat_lt (by omega),
    ofNat_toNat_lt (by omega)]

theorem readTlv_mem {M : Word → BitVec 8} {p l : Word} {t : DerTlv} (h : derTlv (memBytes M p l.toNat) = .ok t) :
    readTlv (memBytes M p l.toNat) = some (elemAt M p t, restAt M p l t) := by
  rw [readTlv_of h, elemOf_mem (derTlv_mem_bound h)]

theorem readElem_mem {M : Word → BitVec 8} {p l : Word} {tag : Nat} {t : DerTlv}
    (h : derElement tag (memBytes M p l.toNat) = .ok t) :
    readElem tag (memBytes M p l.toNat) = some (elemAt M p t, restAt M p l t) := by
  rw [readElem_of h, elemOf_mem (derTlv_mem_bound (derElement_tlv h))]

theorem derElement_tag_eq {tag : Nat} {L : Bytes} {t : DerTlv} (h : derElement tag L = .ok t) : t.tag = tag := by
  unfold derElement at h
  split at h
  · cases h
  · rename_i a l
    split at h
    · rename_i ha
      subst ha
      exact derTlv_tag h
    · cases h

theorem readOid_mem {M : Word → BitVec 8} {p l : Word} {t : DerTlv} (h : derOid (memBytes M p l.toNat) = .ok t) :
    readOid (memBytes M p l.toNat) =
      some (memBytes M (p + BitVec.ofNat 32 t.header) (BitVec.ofNat 32 t.len).toNat, restAt M p l t) := by
  rw [readOid_of h, elemOf_mem (derTlv_mem_bound (derElement_tlv (derOid_ok_elem h)))]
  rfl

theorem derContent_ok {rp a b : Word} {r : Except DerError DerTlv} {t : DerTlv} (ht : r = .ok t)
    (h : derContent rp r = .ok (a, b)) : a = rp + BitVec.ofNat 32 t.header ∧ b = BitVec.ofNat 32 t.len := by
  subst ht
  cases h
  exact ⟨rfl, rfl⟩

theorem readOptional_mem {M : Word → BitVec 8} {p l : Word} {tag : Nat} {t : DerTlv}
    (h : derOptRes tag (memBytes M p l.toNat) = some (.ok t)) :
    readOptional tag (memBytes M p l.toNat) = some (some (elemAt M p t), restAt M p l t) := by
  have ht : derTlv (memBytes M p l.toNat) = .ok t := by
    revert h
    generalize memBytes M p l.toNat = L
    intro h
    cases L with
    | nil => cases h
    | cons b rest =>
      change (if b = tag then some (derTlv (b :: rest)) else none) = _ at h
      by_cases hb : b = tag
      · rw [ite_eq_left hb] at h
        exact Option.some.inj h
      · rw [ite_eq_right hb] at h
        cases h
  have hh : (memBytes M p l.toNat).head? = some tag := by
    revert h
    generalize memBytes M p l.toNat = L
    intro h
    cases L with
    | nil => cases h
    | cons b rest =>
      change (if b = tag then some (derTlv (b :: rest)) else none) = _ at h
      by_cases hb : b = tag
      · rw [hb]; rfl
      · rw [ite_eq_right hb] at h
        cases h
  unfold readOptional
  rw [hh, ite_eq_left (some_beq_self tag), readTlv_mem ht]
  rfl

theorem readOptional_none {tag : Nat} {L : Bytes} (h : derOptRes tag L = none) :
    readOptional tag L = some (none, L) := by
  cases L with
  | nil => rfl
  | cons b rest =>
    change (if b = tag then some (derTlv (b :: rest)) else none) = _ at h
    by_cases hb : b = tag
    · rw [ite_eq_left hb] at h
      cases h
    · unfold readOptional
      refine ite_eq_right fun e => hb ?_
      have := of_decide_eq_true e
      exact this

theorem readOctetString_mem {M : Word → BitVec 8} {p l : Word} {t : DerTlv}
    (h : derElement 4 (memBytes M p l.toNat) = .ok t) :
    readOctetString (memBytes M p l.toNat) =
      some (memBytes M (p + BitVec.ofNat 32 t.header) (BitVec.ofNat 32 t.len).toNat, restAt M p l t) := by
  unfold readOctetString
  rw [readElem_mem h]
  rfl

/-- The contents of the element `t` at `p`, as `memBytes` reads them, byte by byte. -/
theorem content_getD {M : Word → BitVec 8} {p l : Word} {t : DerTlv} (hB : t.header + t.len ≤ l.toNat) {i : Nat}
    (hi : i < t.len) :
    (memBytes M (p + BitVec.ofNat 32 t.header) (BitVec.ofNat 32 t.len).toNat).getD i 0 =
      (memBytes M p l.toNat).getD (t.header + i) 0 := by
  have hl := l.isLt
  rw [ofNat_toNat_lt (by omega), memBytes_getD hi, memBytes_getD (by omega), add_ofNat_assoc]

theorem readBitString_mem {M : Word → BitVec 8} {p l bp bl : Word} {t : DerTlv}
    (h : derElement 3 (memBytes M p l.toNat) = .ok t)
    (hb : derBitsOf (memBytes M p l.toNat) p (.ok t) = .ok (bp, bl)) :
    readBitString (memBytes M p l.toNat) = some (memBytes M bp bl.toNat, restAt M p l t) := by
  have hl := l.isLt
  have hB := derTlv_mem_bound (derElement_tlv h)
  simp only [derBitsOf] at hb
  by_cases hc : t.len ≠ 0 ∧ (memBytes M p l.toNat).getD t.header 0 = 0
  · rw [ite_eq_left hc] at hb
    cases hb
    have h0 : (M (p + BitVec.ofNat 32 t.header)).toNat = 0 := by
      rw [← hc.2, memBytes_getD (by omega)]
    have hc' : memBytes M (p + BitVec.ofNat 32 t.header) (BitVec.ofNat 32 t.len).toNat =
        0 :: memBytes M (p + BitVec.ofNat 32 (t.header + 1)) (BitVec.ofNat 32 (t.len - 1)).toNat := by
      rw [ofNat_toNat_lt (by omega), ofNat_toNat_lt (by omega)]
      obtain ⟨k, hk⟩ : ∃ k, t.len = k + 1 := ⟨t.len - 1, by omega⟩
      rw [hk, memBytes_succ, h0, Nat.add_sub_cancel, ← add_ofNat_assoc]
      rfl
    unfold readBitString
    rw [readElem_mem h]
    show (match memBytes M (p + BitVec.ofNat 32 t.header) (BitVec.ofNat 32 t.len).toNat with
      | 0 :: bits => some (bits, restAt M p l t)
      | _ => none) = _
    rw [hc']
    rfl
  · rw [ite_eq_right hc] at hb
    cases hb

/-- `Der::integer` for an element whose contents are not empty and not a
redundant sign byte. -/
theorem readInteger_of {L r : Bytes} {e : Elem} (h : readElem 2 L = some (e, r)) (hne : e.content ≠ [])
    (hc : ¬ (2 ≤ e.content.length ∧ ((e.content.getD 0 0 = 0 ∧ e.content.getD 1 0 < 0x80) ∨
      (e.content.getD 0 0 = 0xFF ∧ 0x80 ≤ e.content.getD 1 0)))) :
    readInteger L = some (e.content, r) := by
  unfold readInteger
  rw [h]
  show (match e.content with
    | [] => none
    | 0x00 :: next :: _ => if next < 0x80 then none else some (e.content, r)
    | 0xff :: next :: _ => if next ≥ 0x80 then none else some (e.content, r)
    | _ => some (e.content, r)) = _
  split
  · rename_i he; exact absurd he hne
  · rename_i next tl he
    rw [he] at hc
    refine ite_eq_right fun hn => hc ⟨by simp only [List.length_cons]; omega, .inl ⟨rfl, hn⟩⟩
  · rename_i next tl he
    rw [he] at hc
    refine ite_eq_right fun hn => hc ⟨by simp only [List.length_cons]; omega, .inr ⟨rfl, hn⟩⟩
  · rfl

theorem readInteger_mem {M : Word → BitVec 8} {p l ip il : Word} {t : DerTlv}
    (h : derElement 2 (memBytes M p l.toNat) = .ok t)
    (hi : derIntOf (memBytes M p l.toNat) p (.ok t) = .ok (ip, il)) :
    readInteger (memBytes M p l.toNat) = some (memBytes M ip il.toNat, restAt M p l t) ∧
      ip = p + BitVec.ofNat 32 t.header ∧ il = BitVec.ofNat 32 t.len := by
  have hl := l.isLt
  have hB := derTlv_mem_bound (derElement_tlv h)
  simp only [derIntOf] at hi
  by_cases h0 : t.len = 0
  · rw [ite_eq_left h0] at hi; cases hi
  rw [ite_eq_right h0] at hi
  by_cases h2 : 2 ≤ t.len ∧ (((memBytes M p l.toNat).getD t.header 0 = 0 ∧
      (memBytes M p l.toNat).getD (t.header + 1) 0 < 0x80) ∨
      ((memBytes M p l.toNat).getD t.header 0 = 0xFF ∧ 0x80 ≤ (memBytes M p l.toNat).getD (t.header + 1) 0))
  · rw [ite_eq_left h2] at hi; cases hi
  rw [ite_eq_right h2] at hi
  cases hi
  refine ⟨?_, rfl, rfl⟩
  have hlen : (elemAt M p t).content.length = t.len := by
    show (memBytes M (p + BitVec.ofNat 32 t.header) (BitVec.ofNat 32 t.len).toNat).length = _
    rw [memBytes_length, ofNat_toNat_lt (by omega)]
  have hget : ∀ i, i < t.len → (elemAt M p t).content.getD i 0 = (memBytes M p l.toNat).getD (t.header + i) 0 :=
    fun i hi => content_getD hB hi
  exact readInteger_of (readElem_mem h) (fun he => h0 (by rw [← hlen, he]; rfl))
    (fun ⟨hl2, hc⟩ => h2 ⟨by omega, by rw [hget 0 (by omega), hget 1 (by omega), Nat.add_zero] at hc; exact hc⟩)

theorem tlv_content_getD {L : Bytes} {t : DerTlv} {i : Nat} (hi : i < t.len) :
    (t.content L).getD i 0 = L.getD (t.header + i) 0 := by
  unfold DerTlv.content
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi, List.getElem?_drop]

theorem tlv_content_length {L : Bytes} {t : DerTlv} (hB : t.header + t.len ≤ L.length) :
    (t.content L).length = t.len := by
  unfold DerTlv.content
  rw [List.length_take, List.length_drop]
  omega

/-- `Der::integer` on bytes where `derIntOf` returned the contents. -/
theorem readInteger_tlv {L : Bytes} {rp ip il : Word} {t : DerTlv} (h : derElement 2 L = .ok t)
    (hi : derIntOf L rp (.ok t) = .ok (ip, il)) :
    readInteger L = some (t.content L, L.drop (t.header + t.len)) ∧
      ip = rp + BitVec.ofNat 32 t.header ∧ il = BitVec.ofNat 32 t.len := by
  have hB := derElement_bound h
  simp only [derIntOf] at hi
  by_cases h0 : t.len = 0
  · rw [ite_eq_left h0] at hi; cases hi
  rw [ite_eq_right h0] at hi
  by_cases h2 : 2 ≤ t.len ∧ ((L.getD t.header 0 = 0 ∧ L.getD (t.header + 1) 0 < 0x80) ∨
      (L.getD t.header 0 = 0xFF ∧ 0x80 ≤ L.getD (t.header + 1) 0))
  · rw [ite_eq_left h2] at hi; cases hi
  rw [ite_eq_right h2] at hi
  cases hi
  refine ⟨?_, rfl, rfl⟩
  have hlen := tlv_content_length (L := L) hB
  exact readInteger_of (e := (elemOf t L).1) (readElem_of h)
    (fun he => h0 (by rw [← hlen]; exact congrArg List.length he))
    (fun ⟨hl2, hc⟩ => h2 ⟨by rw [← hlen]; exact hl2, by
      have hl2' : 2 ≤ t.len := by rw [← hlen]; exact hl2
      rw [show (elemOf t L).1.content = t.content L from rfl, tlv_content_getD (L := L) (t := t) (i := 0) (by omega),
        tlv_content_getD (L := L) (t := t) (i := 1) (by omega), Nat.add_zero] at hc
      exact hc⟩)

theorem derIntOf_len {L : Bytes} {rp : Word} {t : DerTlv} {x : Word × Word} (h : derIntOf L rp (.ok t) = .ok x) :
    t.len ≠ 0 := by
  intro h0
  simp only [derIntOf, h0, ↓reduceIte] at h
  cases h

/-- `Der::positive_integer` on bytes where `derPosIntOf` returned the contents. -/
theorem readPositiveInteger_tlv {L : Bytes} {rp ip il : Word} {t : DerTlv} (h : derElement 2 L = .ok t)
    (hp : derPosIntOf L rp (.ok t) = .ok (ip, il)) :
    readPositiveInteger L = some (t.content L, L.drop (t.header + t.len)) ∧
      ip = rp + BitVec.ofNat 32 t.header ∧ il = BitVec.ofNat 32 t.len := by
  have hB := derElement_bound h
  cases hI : derIntOf L rp (.ok t) with
  | error e =>
    rw [derPosIntOf_err hI] at hp; cases hp
  | ok pl =>
    have hp' := hp
    simp only [derPosIntOf, hI] at hp'
    by_cases hc : (t.len = 1 ∧ L.getD t.header 0 = 0) ∨ 0x80 ≤ L.getD t.header 0
    · rw [ite_eq_left hc] at hp'; cases hp'
    rw [ite_eq_right hc] at hp'
    cases hp'
    obtain ⟨hr, e1, e2⟩ := readInteger_tlv h hI
    refine ⟨?_, e1, e2⟩
    have hlen := tlv_content_length (L := L) hB
    have h0 := tlv_content_getD (L := L) (t := t) (i := 0)
    rw [Nat.add_zero] at h0
    unfold readPositiveInteger
    rw [hr]
    show (match t.content L with
      | [0x00] => none
      | first :: _ => if first ≥ 0x80 then none else some (t.content L, L.drop (t.header + t.len))
      | [] => none) = _
    split
    · rename_i he
      have h1 : t.len = 1 := by rw [← hlen, he]; rfl
      exact absurd (.inl ⟨h1, by rw [← h0 (by omega), he]; rfl⟩) hc
    · rename_i first tl he
      have hl0 : 0 < t.len := by rw [← hlen, he]; exact Nat.succ_pos _
      refine ite_eq_right fun hf => hc (.inr ?_)
      rw [← h0 hl0, he]
      exact hf
    · rename_i he
      have : t.len = 0 := by rw [← hlen, he]; rfl
      exact absurd this (derIntOf_len hI)

theorem mag_eq (c : Bytes) :
    (match c with
      | 0x00 :: m => m
      | _ => c) = (if c.head? = some 0 then c.drop 1 else c) := by
  cases c with
  | nil => rfl
  | cons a m =>
    by_cases ha : a = 0
    · subst ha; rfl
    · rw [List.head?_cons, ite_eq_right (fun e => ha (Option.some.inj e))]
      split
      · rename_i m' he
        cases he
        exact absurd rfl ha
      · rfl

/-- `der::scalar::<N>`'s value as `readSigScalar`'s. -/
theorem readSigScalar_tlv {N : Nat} {L : Bytes} {rp : Word} {t : DerTlv} {r : Bytes} (h : derElement 2 L = .ok t)
    (hs : derScalarOf N L rp (.ok t) = .ok r) :
    readSigScalar N L = some (r, L.drop (t.header + t.len)) := by
  cases hP : derPosIntOf L rp (.ok t) with
  | error e =>
    simp only [derScalarOf, hP] at hs
    cases hs
  | ok pl =>
    obtain ⟨ip, il⟩ := pl
    obtain ⟨hr, -, -⟩ := readPositiveInteger_tlv h hP
    simp only [derScalarOf, hP] at hs
    unfold readSigScalar
    rw [hr]
    show (do
      require ((match t.content L with
        | 0x00 :: m => m
        | _ => t.content L).length ≤ N)
      pure (List.replicate (N - (match t.content L with
        | 0x00 :: m => m
        | _ => t.content L).length) 0 ++ (match t.content L with
        | 0x00 :: m => m
        | _ => t.content L), L.drop (t.header + t.len))) = _
    rw [mag_eq]
    by_cases hn : N < (if (t.content L).head? = some 0 then (t.content L).drop 1 else t.content L).length
    · rw [ite_eq_left hn] at hs; cases hs
    · rw [ite_eq_right hn] at hs
      cases hs
      unfold require
      rw [ite_eq_left (decide_eq_true (Nat.not_lt.mp hn))]
      rfl

theorem derUsed_ok {r : Except DerError DerTlv} {t : DerTlv} (h : r = .ok t) : derUsed r = t.header + t.len := by
  subst h; rfl

/-- `der::ecdsa_signature::<N>`'s value as `ecdsaSignature`'s. -/
theorem ecdsaSignature_mem {N : Nat} {M : Word → BitVec 8} {p : Word} {n : Nat} {r s : Bytes}
    (h : ecdsaSigOf N M p n = .ok (r, s)) : ecdsaSignature N (memBytes M p n) = some (r, s) := by
  unfold ecdsaSigOf at h
  cases hE : derElement 0x30 (memBytes M p n) with
  | error e => rw [hE] at h; cases h
  | ok t =>
    rw [hE] at h
    simp only at h
    by_cases hn : t.header + t.len = n
    · rw [ite_eq_left hn] at h
      have hc : memBytes M (p + BitVec.ofNat 32 t.header) t.len = t.content (memBytes M p n) := by
        unfold DerTlv.content; rw [memBytes_drop_take (by omega)]
      rw [hc] at h
      generalize hC : t.content (memBytes M p n) = C at h
      cases hE2 : derElement 2 C with
      | error e =>
        rw [hE2] at h
        simp only [derScalarOf] at h
        cases h
      | ok u =>
        rw [hE2] at h
        cases hR : derScalarOf N C (p + BitVec.ofNat 32 t.header) (.ok u) with
        | error b => rw [hR] at h; cases h
        | ok r' =>
          rw [hR] at h
          simp only at h
          have hBu := derElement_bound hE2
          have hClen : C.length = t.len := by rw [← hC]; exact tlv_content_length (by rw [memBytes_length]; omega)
          have hd : memBytes M (p + BitVec.ofNat 32 (t.header + (u.header + u.len))) (t.len - (u.header + u.len)) =
              C.drop (u.header + u.len) := by
            rw [← hC, ← hc, memBytes_dropK' M _ (by omega), add_ofNat_assoc]
          rw [derUsed_ok rfl, hd] at h
          generalize hD : C.drop (u.header + u.len) = D at h
          cases hE3 : derElement 2 D with
          | error e =>
            rw [hE3] at h
            simp only [derScalarOf] at h
            cases h
          | ok w =>
            rw [hE3] at h
            cases hS : derScalarOf N D (p + BitVec.ofNat 32 (t.header + (u.header + u.len))) (.ok w) with
            | error b => rw [hS] at h; cases h
            | ok s' =>
              rw [hS] at h
              simp only at h
              rw [derUsed_ok rfl] at h
              by_cases hw : w.header + w.len = t.len - (u.header + u.len)
              · rw [ite_eq_left hw] at h
                cases h
                unfold ecdsaSignature
                rw [readElem_of hE]
                show (do
                  require ((memBytes M p n).drop (t.header + t.len)).isEmpty
                  let (r, rest) ← readSigScalar N (t.content (memBytes M p n))
                  let (s, rest) ← readSigScalar N rest
                  require rest.isEmpty
                  pure (r, s)) = _
                have he1 : ((memBytes M p n).drop (t.header + t.len)).isEmpty = true := by
                  rw [List.isEmpty_iff, ← List.length_eq_zero_iff, List.length_drop, memBytes_length]; omega
                unfold require
                rw [ite_eq_left he1, hC, readSigScalar_tlv hE2 hR]
                simp only [Option.bind_eq_bind, Option.bind_some]
                rw [hD, readSigScalar_tlv hE3 hS]
                have he2 : (D.drop (w.header + w.len)).isEmpty = true := by
                  rw [List.isEmpty_iff, ← List.length_eq_zero_iff, List.length_drop, ← hD, List.length_drop, hClen]
                  omega
                simp only [Option.bind_some]
                rw [ite_eq_left he2]
                rfl
              · rw [ite_eq_right hw] at h; cases h
    · rw [ite_eq_right hn] at h; cases h

end C3.RV32.Sv
