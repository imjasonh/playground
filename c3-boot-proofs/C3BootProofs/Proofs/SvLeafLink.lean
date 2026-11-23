import C3BootProofs.Proofs.SvDerBridge

/-!
# The leaf certificate the code parsed, as `parseLeaf`

`parseLeaf_code` takes what `sigstore::verify`'s success condition says the
code read from the leaf certificate, one `Der` call at a time, and gives
`parseLeaf` of the certificate's bytes. Each pointer and length the code
reads at is a variable with the equation that defines it. The extensions'
contents (`readExtensions`) and the subject key's place on the curve
(`p256.decodePoint`) are separate hypotheses.
-/

namespace C3.RV32.Sv

open C3.Image

theorem require_true : require true = some () := rfl

theorem require_isEmpty_nil : require ([] : Bytes).isEmpty = some () := rfl

theorem bound_lt {l : Word} {k : Nat} (h : k ≤ l.toNat) : k < 2 ^ 32 := Nat.lt_of_le_of_lt h l.isLt

theorem tag_of_byte {n : Nat} (hl : n < 256) (h : BitVec.ofNat 8 n = BitVec.ofNat 8 6) : n = 6 := by
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl] at this
  exact this

/-- The subject's `SubjectPublicKeyInfo` the code parsed, as `readP256Spki`. -/
theorem readP256Spki_code {M : Word → BitVec 8} {p23 l23 pk lk op15 prp15 bp35 bl35 : Word} {ol15 : Nat}
    {tl6s ta15 pu15 tl35 : DerTlv}
    (h23 : derElement 0x30 (memBytes M p23 l23.toNat) = .ok tl6s)
    (epk : pk = p23 + BitVec.ofNat 32 tl6s.header) (elk : lk = BitVec.ofNat 32 tl6s.len)
    (h24 : derAlgOf M pk tl6s.len = .ok ((op15, ol15), some (prp15, pu15)))
    (h25 : derElement 0x30 (memBytes M pk tl6s.len) = .ok ta15)
    (h26 : BitVec.ofNat 8 pu15.tag = BitVec.ofNat 8 6)
    (h27 : memBytes M (prp15 + BitVec.ofNat 32 pu15.header) pu15.len = oidPrime256v1)
    (h28 : memBytes M op15 ol15 = oidEcPublicKey)
    (h29 : derElement 3 (memBytes M (pk + BitVec.ofNat 32 (ta15.header + ta15.len)) (lk - BitVec.ofNat 32 (ta15.header + ta15.len)).toNat) = .ok tl35)
    (h30 : derBitsOf (memBytes M (pk + BitVec.ofNat 32 (ta15.header + ta15.len)) (lk - BitVec.ofNat 32 (ta15.header + ta15.len)).toNat)
      (pk + BitVec.ofNat 32 (ta15.header + ta15.len)) (.ok tl35) = .ok (bp35, bl35))
    (h31 : bl35 = BitVec.ofNat 32 0x41)
    (h32 : (lk - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) = 0)
    (hpt : (C3.p256.decodePoint (memBytes M bp35 65)).isSome = true) :
    readP256Spki (memBytes M p23 l23.toNat) = some (memBytes M bp35 bl35.toNat, restAt M p23 l23 tl6s) := by
  have b23 := derTlv_mem_bound (derElement_tlv h23)
  have hlk : lk.toNat = tl6s.len := by rw [elk]; exact ofNat_toNat_lt (by have := bound_lt b23; omega)
  obtain ⟨t', prm, ht', hA, hP⟩ := readAlgorithm_mem h24
  have e' : t' = ta15 := Except.ok.inj (ht'.symm.trans h25)
  subst e'
  have bA : t'.header + t'.len ≤ tl6s.len := by have := derElement_bound h25; rwa [memBytes_length] at this
  rw [memBytes_dropK' M pk bA, ← hlk, ← subK_toNat (l := lk) (by omega)] at hA
  cases prm with
  | none => cases hP
  | some e =>
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hP
  have htag : e.tag = 6 := hP.1.trans (tag_of_byte (derAlgOf_tag h24) h26)
  unfold readP256Spki
  rw [readElem_mem h23]
  simp only [Option.bind_eq_bind, Option.bind_some, elemAt]
  rw [← epk, ← elk, hA]
  simp only [Option.bind_some]
  rw [h28, show (oidEcPublicKey == oidEcPublicKey &&
    (some e).any (fun p => p.tag == 6 && p.content == oidPrime256v1)) = true from by
      rw [Option.any_some, htag, hP.2, h27]; decide, require_true]
  simp only [Option.bind_some]
  rw [readBitString_mem h29 h30, restAt_nil h32]
  simp only [Option.bind_some]
  rw [h31, show (BitVec.ofNat 32 0x41).toNat = 65 by decide, memBytes_length, hpt,
    show ((65 == 65 && ([] : Bytes).isEmpty) && true) = true by decide, require_true]
  rfl

set_option maxHeartbeats 4000000 in
theorem parseLeaf_code {M : Word → BitVec 8}
    {p0 l0 pc lc pa la ps ls pt lt pv lv p11 l11 p14 l14 p17 l17 p18 l18 p22 l22 p23 l23 pk lk p35 l35 : Word}
    {bp16 bl16 ip2 il2 op19 op15 prp15 bp35 bl35 : Word} {ol19 ol15 tm22 tm31 : Nat}
    {t tl1 tl8 tl16 tl29 te43 tl2 tl9 tl6 tl13 tl2s tl6s ta15 pu15 tl35 tl9e : DerTlv}
    {rs22 rs31 sr ss : Bytes} {ids : List Bytes}
    (h0 : derElement 0x30 (memBytes M p0 l0.toNat) = .ok t)
    (h1 : l0 - BitVec.ofNat 32 (t.header + t.len) = 0)
    (epc : pc = p0 + BitVec.ofNat 32 t.header) (elc : lc = BitVec.ofNat 32 t.len)
    (h2 : derElement 0x30 (memBytes M pc lc.toNat) = .ok tl1)
    (epa : pa = pc + BitVec.ofNat 32 (tl1.header + tl1.len)) (ela : la = lc - BitVec.ofNat 32 (tl1.header + tl1.len))
    (h3 : derElement 0x30 (memBytes M pa la.toNat) = .ok tl8)
    (eps : ps = pa + BitVec.ofNat 32 (tl8.header + tl8.len)) (els : ls = la - BitVec.ofNat 32 (tl8.header + tl8.len))
    (h4 : derElement 3 (memBytes M ps ls.toNat) = .ok tl16)
    (h5 : derBitsOf (memBytes M ps ls.toNat) ps (.ok tl16) = .ok (bp16, bl16))
    (h6 : ls - BitVec.ofNat 32 (tl16.header + tl16.len) = 0)
    (ept : pt = pc + BitVec.ofNat 32 tl1.header) (elt : lt = BitVec.ofNat 32 tl1.len)
    (h7 : derOptRes 0xA0 (memBytes M pt lt.toNat) = some (.ok tl29))
    (epv : pv = pt + BitVec.ofNat 32 tl29.header) (elv : lv = BitVec.ofNat 32 tl29.len)
    (h8 : derIntIsOf M (memBytes M pv lv.toNat) pv (derElement 2 (memBytes M pv lv.toNat)) ((BitVec.ofNat 32 0x2).extractLsb' 0 8) = .ok true)
    (h9 : derElement 2 (memBytes M pv lv.toNat) = .ok te43)
    (h10 : lv - BitVec.ofNat 32 (te43.header + te43.len) = 0)
    (ep11 : p11 = pt + BitVec.ofNat 32 (tl29.header + tl29.len)) (el11 : l11 = lt - BitVec.ofNat 32 (tl29.header + tl29.len))
    (h11 : derElement 2 (memBytes M p11 l11.toNat) = .ok tl2)
    (h12 : derPosIntOf (memBytes M p11 l11.toNat) p11 (.ok tl2) = .ok (ip2, il2))
    (h13 : il2.toNat ≤ 20)
    (ep14 : p14 = p11 + BitVec.ofNat 32 (tl2.header + tl2.len)) (el14 : l14 = l11 - BitVec.ofNat 32 (tl2.header + tl2.len))
    (h14 : derElement 0x30 (memBytes M p14 l14.toNat) = .ok tl9)
    (h15 : derAlgOf M p14 (tl9.header + tl9.len) = .ok ((op19, ol19), none))
    (h16 : memBytes M op19 ol19 = oidEcdsaSha384)
    (ep17 : p17 = p14 + BitVec.ofNat 32 (tl9.header + tl9.len)) (el17 : l17 = l14 - BitVec.ofNat 32 (tl9.header + tl9.len))
    (h17 : derElement 0x30 (memBytes M p17 l17.toNat) = .ok tl6)
    (ep18 : p18 = p17 + BitVec.ofNat 32 (tl6.header + tl6.len)) (el18 : l18 = l17 - BitVec.ofNat 32 (tl6.header + tl6.len))
    (h18 : derElement 0x30 (memBytes M p18 l18.toNat) = .ok tl13)
    (h19 : readTime (memBytes M (p18 + BitVec.ofNat 32 tl13.header) tl13.len) = some (tm22, rs22))
    (h20 : readTime rs22 = some (tm31, rs31))
    (h21 : rs31 = [])
    (ep22 : p22 = p18 + BitVec.ofNat 32 (tl13.header + tl13.len)) (el22 : l22 = l18 - BitVec.ofNat 32 (tl13.header + tl13.len))
    (h22 : derElement 0x30 (memBytes M p22 l22.toNat) = .ok tl2s)
    (ep23 : p23 = p22 + BitVec.ofNat 32 (tl2s.header + tl2s.len)) (el23 : l23 = l22 - BitVec.ofNat 32 (tl2s.header + tl2s.len))
    (h23 : derElement 0x30 (memBytes M p23 l23.toNat) = .ok tl6s)
    (epk : pk = p23 + BitVec.ofNat 32 tl6s.header) (elk : lk = BitVec.ofNat 32 tl6s.len)
    (h24 : derAlgOf M pk tl6s.len = .ok ((op15, ol15), some (prp15, pu15)))
    (h25 : derElement 0x30 (memBytes M pk tl6s.len) = .ok ta15)
    (h26 : BitVec.ofNat 8 pu15.tag = BitVec.ofNat 8 6)
    (h27 : memBytes M (prp15 + BitVec.ofNat 32 pu15.header) pu15.len = oidPrime256v1)
    (h28 : memBytes M op15 ol15 = oidEcPublicKey)
    (h29 : derElement 3 (memBytes M (pk + BitVec.ofNat 32 (ta15.header + ta15.len)) (lk - BitVec.ofNat 32 (ta15.header + ta15.len)).toNat) = .ok tl35)
    (h30 : derBitsOf (memBytes M (pk + BitVec.ofNat 32 (ta15.header + ta15.len)) (lk - BitVec.ofNat 32 (ta15.header + ta15.len)).toNat)
      (pk + BitVec.ofNat 32 (ta15.header + ta15.len)) (.ok tl35) = .ok (bp35, bl35))
    (h31 : bl35 = BitVec.ofNat 32 0x41)
    (h32 : (lk - BitVec.ofNat 32 (ta15.header + ta15.len)) - BitVec.ofNat 32 (tl35.header + tl35.len) = 0)
    (hpt : (C3.p256.decodePoint (memBytes M bp35 65)).isSome = true)
    (ep35 : p35 = p23 + BitVec.ofNat 32 (tl6s.header + tl6s.len)) (el35 : l35 = l23 - BitVec.ofNat 32 (tl6s.header + tl6s.len))
    (h35 : derOptRes 0xA3 (memBytes M p35 l35.toNat) = some (.ok tl9e))
    (h36 : l35 - BitVec.ofNat 32 (tl9e.header + tl9e.len) = 0)
    (hext : readExtensions (memBytes M (p35 + BitVec.ofNat 32 tl9e.header) (BitVec.ofNat 32 tl9e.len).toNat) = some ids)
    (h51 : memBytes M pa (BitVec.ofNat 32 (tl8.header + tl8.len)).toNat = memBytes M p14 (BitVec.ofNat 32 (tl9.header + tl9.len)).toNat)
    (h52 : ecdsaSigOf 48 M bp16 bl16.toNat = .ok (sr, ss)) :
    parseLeaf (memBytes M p0 l0.toNat) = some ⟨memBytes M pc (BitVec.ofNat 32 (tl1.header + tl1.len)).toNat,
      memBytes M p17 (BitVec.ofNat 32 (tl6.header + tl6.len)).toNat, tm22, tm31, memBytes M bp35 bl35.toNat, sr, ss, ids⟩ := by
  unfold parseLeaf
  rw [readElem_mem h0, restAt_nil h1]
  simp only [Option.bind_eq_bind, Option.bind_some, elemAt]
  rw [← epc, ← elc, readElem_mem h2]
  simp only [Option.bind_some, elemAt, restAt]
  rw [← epa, ← ela, readElem_mem h3]
  simp only [Option.bind_some, elemAt, restAt]
  rw [← eps, ← els, readBitString_mem h4 h5, restAt_nil h6]
  simp only [Option.bind_some, require_isEmpty_nil]
  rw [← ept, ← elt, readOptional_mem h7]
  simp only [Option.bind_some, elemAt]
  rw [← epv, ← elv, readInteger_is_mem h9 h8, restAt_nil h10,
    show ((BitVec.ofNat 32 0x2).extractLsb' 0 8).toNat = 2 by decide]
  simp only [Option.bind_some]
  rw [show ([2] == [2] && ([] : Bytes).isEmpty) = true by decide, require_true]
  simp only [Option.bind_some, restAt]
  rw [← ep11, ← el11, readPositiveInteger_mem h11 h12]
  simp only [Option.bind_some]
  rw [memBytes_length, decide_eq_true h13, require_true]
  simp only [Option.bind_some, restAt]
  rw [← ep14, ← el14, readElem_mem h14]
  simp only [Option.bind_some, elemAt, restAt]
  have b14 := derTlv_mem_bound (derElement_tlv h14)
  obtain ⟨t9, prm, -, hA, hP⟩ := readAlgorithm_mem h15
  cases prm with
  | some _ => cases hP
  | none =>
  rw [← ofNat_toNat_lt (bound_lt b14)] at hA
  rw [hA]
  simp only [Option.bind_some]
  rw [h16, show (oidEcdsaSha384 == oidEcdsaSha384 && (none : Option Elem).isNone) = true by decide, require_true]
  simp only [Option.bind_some]
  rw [← ep17, ← el17, readElem_mem h17]
  simp only [Option.bind_some, elemAt, restAt]
  rw [← ep18, ← el18, readElem_mem h18]
  simp only [Option.bind_some, elemAt, restAt]
  have b18 := derTlv_mem_bound (derElement_tlv h18)
  rw [ofNat_toNat_lt (k := tl13.len) (by have := bound_lt b18; omega), h19]
  simp only [Option.bind_some]
  rw [h20]
  simp only [Option.bind_some]
  rw [h21, require_isEmpty_nil]
  simp only [Option.bind_some]
  rw [← ep22, ← el22, readElem_mem h22]
  simp only [Option.bind_some, restAt]
  rw [← ep23, ← el23, readP256Spki_code h23 epk elk h24 h25 h26 h27 h28 h29 h30 h31 h32 hpt]
  simp only [Option.bind_some, restAt]
  rw [← ep35, ← el35, readOptional_mem h35, restAt_nil h36]
  simp only [Option.bind_some, require_isEmpty_nil, elemAt]
  rw [hext]
  simp only [Option.bind_some]
  rw [h51, beq_iff_eq.mpr rfl, require_true]
  simp only [Option.bind_some]
  rw [ecdsaSignature_mem h52]
  rfl

end C3.RV32.Sv
