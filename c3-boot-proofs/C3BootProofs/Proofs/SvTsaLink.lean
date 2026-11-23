import C3BootProofs.Proofs.SvCkptLink
import C3BootProofs.Spec.Tsa

/-!
# The timestamp the code read, as `parseTimestamp` reads it

Starting with the signed attributes: the code's loop over them, as
`readSignedAttributes`.
-/

namespace C3.RV32.Sv

open C3.Image

/-- One pass of the code's loop over the signed attributes, over the state
(message digest pointer, `contentType` flag, pointer, bytes left): the body
of `sv_attrStep`. -/
def attrBody (B p0 L0 : Word) (M0 : Word → BitVec 8) : Word × Word × Word × Word → Word × Word × Word × Word → Prop :=
  fun s s' => s.2.2.2 ≠ 0 ∧ (((s.2.2.2)).toNat ≤ (L0).toNat) ∧ ∃ tl6_2, derElement 0x30 (memBytes M0 ((s.2.2.1)) ((s.2.2.2)).toNat) = .ok tl6_2 ∧ ∃ op15_2 ol15_2, derContent (((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) (derOid (memBytes M0 (((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) (BitVec.ofNat 32 tl6_2.len).toNat)) = .ok (op15_2, ol15_2) ∧ ∃ to15_2, derOid (memBytes M0 (((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) (BitVec.ofNat 32 tl6_2.len).toNat) = .ok to15_2 ∧ ∃ tl20_2, derElement 0x31 (memBytes M0 ((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) ((BitVec.ofNat 32 tl6_2.len) - BitVec.ofNat 32 (to15_2.header + to15_2.len)).toNat) = .ok tl20_2 ∧ (((BitVec.ofNat 32 tl6_2.len) - BitVec.ofNat 32 (to15_2.header + to15_2.len)) - BitVec.ofNat 32 (tl20_2.header + tl20_2.len) = 0) ∧ listsOidOf M0 p0 ((L0) - ((s.2.2.2))).toNat (memBytes M0 op15_2 ol15_2.toNat) = .ok false ∧ ∃ tsav_r24_3 : Word, ∃ tsav_w78_3 : Word, ∃ tsav_w1388_3 : Word, ∃ tsav_w138c_3 : Word, (((memBytes M0 op15_2 ol15_2.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC486E) 9) ∧ ∃ op5 ol5, derContent ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) (derOid (memBytes M0 ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) ((BitVec.ofNat 32 tl20_2.len)).toNat)) = .ok (op5, ol5) ∧ ∃ to5, derOid (memBytes M0 ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) ((BitVec.ofNat 32 tl20_2.len)).toNat) = .ok to5 ∧ (memBytes M0 op5 ol5.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC4862) 11) ∧ (((BitVec.ofNat 32 tl20_2.len)) - BitVec.ofNat 32 (to5.header + to5.len) = 0) ∧ tsav_r24_3 = (s.1) ∧ tsav_w78_3 = BitVec.ofNat 32 0x1 ∧ tsav_w1388_3 = ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) + BitVec.ofNat 32 (to5.header + to5.len) ∧ tsav_w138c_3 = ((BitVec.ofNat 32 tl20_2.len)) - BitVec.ofNat 32 (to5.header + to5.len)) ∨ ((¬ (memBytes M0 op15_2 ol15_2.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC486E) 9)) ∧ (memBytes M0 op15_2 ol15_2.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC4877) 9) ∧ ∃ vp8 vl8, derContent ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) (derElement 4 (memBytes M0 ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) ((BitVec.ofNat 32 tl20_2.len)).toNat)) = .ok (vp8, vl8) ∧ ∃ te8, derElement 4 (memBytes M0 ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) ((BitVec.ofNat 32 tl20_2.len)).toNat) = .ok te8 ∧ (vl8 = 32) ∧ (((BitVec.ofNat 32 tl20_2.len)) - BitVec.ofNat 32 (te8.header + te8.len) = 0) ∧ tsav_r24_3 = vp8 ∧ tsav_w78_3 = (s.2.1) ∧ tsav_w1388_3 = ((((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header)) + BitVec.ofNat 32 (te8.header + te8.len) ∧ tsav_w138c_3 = ((BitVec.ofNat 32 tl20_2.len)) - BitVec.ofNat 32 (te8.header + te8.len)) ∨ ((¬ (memBytes M0 op15_2 ol15_2.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC486E) 9)) ∧ (¬ (memBytes M0 op15_2 ol15_2.toNat = memBytes M0 (BitVec.ofNat 32 0x3FCC4877) 9)) ∧ tsav_r24_3 = (s.1) ∧ tsav_w78_3 = (s.2.1) ∧ tsav_w1388_3 = (((((s.2.2.1)) + BitVec.ofNat 32 tl6_2.header) + BitVec.ofNat 32 (to15_2.header + to15_2.len)) + BitVec.ofNat 32 tl20_2.header) ∧ tsav_w138c_3 = (BitVec.ofNat 32 tl20_2.len))) ∧ SvIn B tsav_w1388_3 tsav_w138c_3.toNat ∧ (tsav_r24_3 = 0 ∨ SvIn B tsav_r24_3 32) ∧ s' = (tsav_r24_3, tsav_w78_3, ((s.2.2.1)) + BitVec.ofNat 32 (tl6_2.header + tl6_2.len), ((s.2.2.2)) - BitVec.ofNat 32 (tl6_2.header + tl6_2.len))

theorem attrGo_nil {a : Bytes} {fuel : Nat} {ct : Bool} {md : Option Bytes} :
    readSignedAttributes.go a fuel [] ct md = some (ct, md) := by
  cases fuel <;> rfl

theorem attrGo_cons {a L : Bytes} {fuel : Nat} {ct : Bool} {md : Option Bytes} (hne : L ≠ []) :
    readSignedAttributes.go a (fuel + 1) L ct md = (do
      let (attr, r) ← readElem 48 L
      let (oid, inner) ← readOid attr.content
      let (values, inner) ← readElem 49 inner
      require (List.isEmpty inner)
      let dup ← listsOid oid (List.length a) a
      require !dup
      if (oid == oidContentType) = true then do
          let (t, vr) ← readOid values.content
          require (t == oidTstInfo && List.isEmpty vr)
          readSignedAttributes.go (a ++ attr.raw) fuel r true md
        else
          if (oid == oidMessageDigest) = true then do
            let (d, vr) ← readOctetString values.content
            require (List.length d == 32 && List.isEmpty vr)
            readSignedAttributes.go (a ++ attr.raw) fuel r ct (some d)
          else readSignedAttributes.go (a ++ attr.raw) fuel r ct md) := by
  cases L with
  | nil => exact absurd rfl hne
  | cons _ _ => rfl

/-- The bytes read so far, one element more. -/
theorem memBytes_earlier {M : Word → BitVec 8} {p0 L0 rem : Word} {k : Nat} (hle : rem.toNat ≤ L0.toNat)
    (hk : k ≤ rem.toNat) :
    memBytes M p0 (L0 - rem).toNat ++ memBytes M (p0 + (L0 - rem)) (BitVec.ofNat 32 k).toNat =
      memBytes M p0 (L0 - (rem - BitVec.ofNat 32 k)).toNat := by
  have hr := rem.isLt
  have e1 : (L0 - rem).toNat = L0.toNat - rem.toNat := by rw [BitVec.toNat_sub]; omega
  have e2 : (L0 - (rem - BitVec.ofNat 32 k)).toNat = L0.toNat - rem.toNat + k := by
    rw [BitVec.toNat_sub, BitVec.toNat_sub, ofNat_toNat_lt (by omega)]; omega
  rw [ofNat_toNat_lt (by omega), e2, memBytes_split, e1, ← e1, ofNat_toNat_self]

theorem ptr_step {p p0 L0 rem : Word} (k : Word) (hp : p = p0 + (L0 - rem)) : p + k = p0 + (L0 - (rem - k)) := by
  subst hp
  rw [BitVec.add_assoc]
  congr 1
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.sub_eq_add_neg,
    BitVec.neg_neg, BitVec.add_assoc]

theorem ne_of_beq_false {a b c : Bytes} (h : ¬ a = b) (hb : b = c) : (a == c) = false :=
  Bool.eq_false_iff.mpr fun e => h (hb ▸ beq_iff_eq.mp e)

set_option maxHeartbeats 4000000 in
/-- The code's loop over the signed attributes, a run of `k` passes that
reads every byte, as `readSignedAttributes.go`: a set flag means a
`contentType` attribute was read, and a message digest pointer that isn't
null points at the digest it read. -/
theorem attrGo_chain {M : Word → BitVec 8} {B p0 L0 : Word}
    (hct : memBytes M (BitVec.ofNat 32 0x3FCC486E) 9 = oidContentType)
    (htst : memBytes M (BitVec.ofNat 32 0x3FCC4862) 11 = oidTstInfo)
    (hmd : memBytes M (BitVec.ofNat 32 0x3FCC4877) 9 = oidMessageDigest) :
    ∀ k {r24 w78 p rem r24' w78' p' : Word} {fuel : Nat} {ct : Bool} {md : Option Bytes},
      svChain (attrBody B p0 L0 M) k (r24, w78, p, rem) (r24', w78', p', 0) →
      rem.toNat ≤ fuel → rem.toNat ≤ L0.toNat → p = p0 + (L0 - rem) →
      (w78 = 1 → ct = true) → (r24 ≠ 0 → md = some (memBytes M r24 32)) →
      ∃ ct' md', readSignedAttributes.go (memBytes M p0 (L0 - rem).toNat) fuel (memBytes M p rem.toNat) ct md =
        some (ct', md') ∧ (w78' = 1 → ct' = true) ∧ (r24' ≠ 0 → md' = some (memBytes M r24' 32)) := by
  intro k
  induction k with
  | zero =>
    intro r24 w78 p rem r24' w78' p' fuel ct md h _ _ _ hw hr
    cases h
    exact ⟨ct, md, attrGo_nil, hw, hr⟩
  | succ k ih =>
    intro r24 w78 p rem r24' w78' p' fuel ct md h hf hle hp hw hr
    obtain ⟨m, hm, hc⟩ := h
    obtain ⟨hne, -, tl6, h6, op15, ol15, hc15, to15, ho15, tl20, h20, hz20, hlo, r24n, w78n, w1388, w138c, hbr, -, -, hs⟩ := hm
    subst hs
    simp only at hne h6 hc15 ho15 h20 hz20 hlo hbr hc
    have hB6 := derTlv_mem_bound (derElement_tlv h6)
    have h26 := derTlv_header (derElement_tlv h6)
    have hrem : rem.toNat ≠ 0 := fun e => hne (BitVec.eq_of_toNat_eq e)
    obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
    have hL : memBytes M p rem.toNat ≠ [] := by
      intro e
      have := congrArg List.length e
      rw [memBytes_length, List.length_nil] at this
      exact hrem this
    rw [ho15] at hc15
    obtain ⟨e15a, e15b⟩ := derContent_ok rfl hc15
    have hrest : (rem - BitVec.ofNat 32 (tl6.header + tl6.len)).toNat ≤ fuel' := by
      rw [subK_toNat hB6]; omega
    have hle' : (rem - BitVec.ofNat 32 (tl6.header + tl6.len)).toNat ≤ L0.toNat := by
      rw [subK_toNat hB6]; omega
    have hp' := ptr_step (BitVec.ofNat 32 (tl6.header + tl6.len)) hp
    have hearl := memBytes_earlier (M := M) (p0 := p0) hle hB6
    rw [attrGo_cons hL, readElem_mem h6]
    simp only [Option.bind_eq_bind, Option.bind_some, elemAt]
    rw [readOid_mem ho15]
    simp only [Option.bind_some, restAt]
    rw [readElem_mem h20, restAt_nil hz20]
    simp only [Option.bind_some, require_isEmpty_nil, elemAt]
    rw [memBytes_length, ← e15a, ← e15b, listsOid_mem hlo]
    simp only [Option.bind_some, Bool.not_false, require_true]
    rw [← hp] at hearl
    rw [hearl]
    rcases hbr with ⟨hctc, op5, ol5, hc5, to5, ho5, h5eq, hz5, er24, ew78, -, -⟩ |
      ⟨hnct, hmdc, vp8, vl8, hc8, te8, h8, hvl, hz8, er24, ew78, -, -⟩ | ⟨hnct, hnmd, er24, ew78, -, -⟩
    · rw [ite_eq_left (beq_iff_eq.mpr (hctc.trans hct))]
      rw [ho5] at hc5
      obtain ⟨e5a, e5b⟩ := derContent_ok rfl hc5
      rw [readOid_mem ho5, restAt_nil hz5]
      simp only [Option.bind_some]
      rw [← e5a, ← e5b, h5eq, htst, show (oidTstInfo == oidTstInfo && ([] : Bytes).isEmpty) = true by decide, require_true]
      simp only [Option.bind_some]
      subst er24 ew78
      rw [hp'] at hc ⊢
      exact ih hc hrest hle' rfl (fun _ => rfl) hr
    · rw [ite_eq_right (by rw [ne_of_beq_false hnct hct]; exact Bool.false_ne_true),
        ite_eq_left (beq_iff_eq.mpr (hmdc.trans hmd))]
      rw [h8] at hc8
      obtain ⟨e8a, e8b⟩ := derContent_ok rfl hc8
      rw [readOctetString_mem h8, restAt_nil hz8]
      simp only [Option.bind_some]
      rw [← e8a, ← e8b, memBytes_length, hvl, show ((32 : Word).toNat == 32 && ([] : Bytes).isEmpty) = true by decide,
        require_true]
      simp only [Option.bind_some]
      subst ew78
      rw [hp'] at hc ⊢
      refine ih hc hrest hle' rfl hw (fun _ => ?_)
      rw [er24]
      rfl
    · rw [ite_eq_right (by rw [ne_of_beq_false hnct hct]; exact Bool.false_ne_true),
        ite_eq_right (by rw [ne_of_beq_false hnmd hmd]; exact Bool.false_ne_true)]
      subst er24 ew78
      rw [hp'] at hc ⊢
      exact ih hc hrest hle' rfl hw hr

/-- The signed attributes the code read, as `readSignedAttributes`: the
message digest is the 32 bytes at the pointer the loop ends with. -/
theorem readSignedAttributes_code {M : Word → BitVec 8} {B p0 L0 dg' flag' cp' : Word} {k : Nat}
    (hct : memBytes M (BitVec.ofNat 32 0x3FCC486E) 9 = oidContentType)
    (htst : memBytes M (BitVec.ofNat 32 0x3FCC4862) 11 = oidTstInfo)
    (hmd : memBytes M (BitVec.ofNat 32 0x3FCC4877) 9 = oidMessageDigest)
    (h : svChain (attrBody B p0 L0 M) k (BitVec.ofNat 32 0, BitVec.ofNat 32 0, p0, L0) (dg', flag', cp', 0))
    (hdg : dg' ≠ 0) (hflag : flag' = 1) :
    readSignedAttributes (memBytes M p0 L0.toNat) = some (memBytes M dg' 32) := by
  have hp : p0 = p0 + (L0 - L0) := by rw [BitVec.sub_self, BitVec.add_zero]
  obtain ⟨ct', md', hgo, hct', hmd'⟩ := attrGo_chain hct htst hmd k h (fuel := (memBytes M p0 L0.toNat).length)
    (Nat.le_of_eq (memBytes_length _ _ _).symm) (Nat.le_refl _) hp (fun e => absurd e (by decide)) (fun e => absurd rfl e)
  rw [BitVec.sub_self, show (0#32 : Word).toNat = 0 from rfl, memBytes_zero] at hgo
  unfold readSignedAttributes
  rw [hgo]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [hct' hflag, require_true]
  simp only [Option.bind_some]
  exact hmd' hdg

/-- The optional `certificates` field and the check that no `crls` follow,
as the code reads them: the bytes left after it. -/
theorem tsa4_code {M : Word → BitVec 8} {p l q ql : Word}
    (h : ((derOptRes 0xA0 (memBytes M p l.toNat) = none) ∧ (l = 0 ∨ (M p).toNat ≠ 0xA1) ∧ q = p ∧ ql = l) ∨
      ((¬ (derOptRes 0xA0 (memBytes M p l.toNat) = none)) ∧ ∃ t, derOptRes 0xA0 (memBytes M p l.toNat) = some (.ok t) ∧
        (l - BitVec.ofNat 32 (t.header + t.len) = 0 ∨ (M (p + BitVec.ofNat 32 (t.header + t.len))).toNat ≠ 0xA1) ∧
        q = p + BitVec.ofNat 32 (t.header + t.len) ∧ ql = l - BitVec.ofNat 32 (t.header + t.len))) :
    ∃ e, readOptional 0xa0 (memBytes M p l.toNat) = some (e, memBytes M q ql.toNat) ∧
      ((memBytes M q ql.toNat).head? != some 0xa1) = true := by
  have hd : ∀ {r rl : Word}, (rl = 0 ∨ (M r).toNat ≠ 0xA1) → ((memBytes M r rl.toNat).head? != some 0xa1) = true := by
    intro r rl hh
    rcases hh with hz | hn
    · subst hz; rfl
    · rcases hc : rl.toNat with _ | n
      · rfl
      · rw [memBytes_succ, List.head?_cons, bne]
        rw [show (some (M r).toNat == some 0xa1) = false from Bool.eq_false_iff.mpr fun e =>
          hn (Option.some.inj (beq_iff_eq.mp e))]
        rfl
  rcases h with ⟨hn, hh, rfl, rfl⟩ | ⟨-, t, ht, hh, rfl, rfl⟩
  · exact ⟨none, readOptional_none hn, hd hh⟩
  · exact ⟨some (elemAt M p t), readOptional_mem ht, hd hh⟩

theorem readSha256Alg_code {M : Word → BitVec 8} {p l : Word} {t : DerTlv} (h : isSha256Of M p l.toNat = .ok true)
    (he : derElement 0x30 (memBytes M p l.toNat) = .ok t) :
    readSha256Alg (memBytes M p l.toNat) = some (restAt M p l t) := by
  obtain ⟨t', ht', hr⟩ := readSha256Alg_mem h
  have e : t' = t := Except.ok.inj (ht'.symm.trans he)
  subst e
  rw [hr, memBytes_rest (derTlv_mem_bound (derElement_tlv he))]

set_option maxHeartbeats 8000000 in
/-- The timestamp token the code parsed, as `parseTimestamp`. The signed
attributes and the `TSTInfo` are separate hypotheses. -/
theorem parseTimestamp_code {M : Word → BitVec 8}
    {p0 l0 pr lr ps ls pa la pc lc pe le pd ld pq lq pg lg pn ln pk lk pt lt pv lv psd lsd q ql pi li pj lj pw lw px lx
      py ly pz lz op53 ol53 op58 ol58 vp23 vl23 vp19 vl19 : Word} {op8 ol8 gt : Nat}
    {tl10 tl22 te33 tl41 to53 tl2a tl15 te26 tl32 te41 tl49 to58 tl2b te23 tl2c tl13 te25 tl31 te39 tl45 te8 te19 : DerTlv}
    {md imp sr ss : Bytes}
    (hsd : memBytes M (BitVec.ofNat 32 0x3FCC4859) 9 = oidSignedData)
    (hti : memBytes M (BitVec.ofNat 32 0x3FCC4862) 11 = oidTstInfo)
    (hes : memBytes M (BitVec.ofNat 32 0x3FCC4818) 8 = oidEcdsaSha256)
    (h84 : derElement 0x30 (memBytes M p0 l0.toNat) = .ok tl10)
    (h85 : l0 - BitVec.ofNat 32 (tl10.header + tl10.len) = 0)
    (epr : pr = p0 + BitVec.ofNat 32 tl10.header) (elr : lr = BitVec.ofNat 32 tl10.len)
    (h86 : derElement 0x30 (memBytes M pr lr.toNat) = .ok tl22)
    (eps : ps = pr + BitVec.ofNat 32 tl22.header) (els : ls = BitVec.ofNat 32 tl22.len)
    (h87 : derIntIsOf M (memBytes M ps ls.toNat) ps (derElement 2 (memBytes M ps ls.toNat)) ((BitVec.ofNat 32 0x0).extractLsb' 0 8) = .ok true)
    (h88 : derElement 2 (memBytes M ps ls.toNat) = .ok te33)
    (h89 : ls - BitVec.ofNat 32 (te33.header + te33.len) = 0)
    (epa : pa = pr + BitVec.ofNat 32 (tl22.header + tl22.len)) (ela : la = lr - BitVec.ofNat 32 (tl22.header + tl22.len))
    (h90 : derElement 0x30 (memBytes M pa la.toNat) = .ok tl41)
    (h91 : la - BitVec.ofNat 32 (tl41.header + tl41.len) = 0)
    (epc : pc = pa + BitVec.ofNat 32 tl41.header) (elc : lc = BitVec.ofNat 32 tl41.len)
    (h92 : derContent pc (derOid (memBytes M pc lc.toNat)) = .ok (op53, ol53))
    (h93 : derOid (memBytes M pc lc.toNat) = .ok to53)
    (h94 : memBytes M op53 ol53.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4859) 9)
    (epe : pe = pc + BitVec.ofNat 32 (to53.header + to53.len)) (ele : le = lc - BitVec.ofNat 32 (to53.header + to53.len))
    (h95 : derElement 0xA0 (memBytes M pe le.toNat) = .ok tl2a)
    (h96 : le - BitVec.ofNat 32 (tl2a.header + tl2a.len) = 0)
    (epd : pd = pe + BitVec.ofNat 32 tl2a.header) (eld : ld = BitVec.ofNat 32 tl2a.len)
    (h97 : derElement 0x30 (memBytes M pd ld.toNat) = .ok tl15)
    (h98 : ld - BitVec.ofNat 32 (tl15.header + tl15.len) = 0)
    (epq : pq = pd + BitVec.ofNat 32 tl15.header) (elq : lq = BitVec.ofNat 32 tl15.len)
    (h99 : derIntIsOf M (memBytes M pq lq.toNat) pq (derElement 2 (memBytes M pq lq.toNat)) ((BitVec.ofNat 32 0x3).extractLsb' 0 8) = .ok true)
    (h100 : derElement 2 (memBytes M pq lq.toNat) = .ok te26)
    (epg : pg = pq + BitVec.ofNat 32 (te26.header + te26.len)) (elg : lg = lq - BitVec.ofNat 32 (te26.header + te26.len))
    (h101 : derElement 0x31 (memBytes M pg lg.toNat) = .ok tl32)
    (h102 : isSha256Of M (pg + BitVec.ofNat 32 tl32.header) (BitVec.ofNat 32 tl32.len).toNat = .ok true)
    (h103 : derElement 0x30 (memBytes M (pg + BitVec.ofNat 32 tl32.header) (BitVec.ofNat 32 tl32.len).toNat) = .ok te41)
    (h104 : BitVec.ofNat 32 tl32.len - BitVec.ofNat 32 (te41.header + te41.len) = 0)
    (epn : pn = pg + BitVec.ofNat 32 (tl32.header + tl32.len)) (eln : ln = lg - BitVec.ofNat 32 (tl32.header + tl32.len))
    (h105 : derElement 0x30 (memBytes M pn ln.toNat) = .ok tl49)
    (epk : pk = pn + BitVec.ofNat 32 tl49.header) (elk : lk = BitVec.ofNat 32 tl49.len)
    (h106 : derContent pk (derOid (memBytes M pk lk.toNat)) = .ok (op58, ol58))
    (h107 : derOid (memBytes M pk lk.toNat) = .ok to58)
    (h108 : memBytes M op58 ol58.toNat = memBytes M (BitVec.ofNat 32 0x3FCC4862) 11)
    (ept : pt = pk + BitVec.ofNat 32 (to58.header + to58.len)) (elt : lt = lk - BitVec.ofNat 32 (to58.header + to58.len))
    (h109 : derOptRes 0xA0 (memBytes M pt lt.toNat) = some (.ok tl2b))
    (h110 : lt - BitVec.ofNat 32 (tl2b.header + tl2b.len) = 0)
    (epv : pv = pt + BitVec.ofNat 32 tl2b.header) (elv : lv = BitVec.ofNat 32 tl2b.len)
    (h111 : derContent pv (derElement 4 (memBytes M pv lv.toNat)) = .ok (vp23, vl23))
    (h112 : derElement 4 (memBytes M pv lv.toNat) = .ok te23)
    (h113 : lv - BitVec.ofNat 32 (te23.header + te23.len) = 0)
    (epsd : psd = pn + BitVec.ofNat 32 (tl49.header + tl49.len)) (elsd : lsd = ln - BitVec.ofNat 32 (tl49.header + tl49.len))
    (h114 : ∃ e, readOptional 0xa0 (memBytes M psd lsd.toNat) = some (e, memBytes M q ql.toNat) ∧
      ((memBytes M q ql.toNat).head? != some 0xa1) = true)
    (h116 : derElement 0x31 (memBytes M q ql.toNat) = .ok tl2c)
    (h117 : ql - BitVec.ofNat 32 (tl2c.header + tl2c.len) = 0)
    (epi : pi = q + BitVec.ofNat 32 tl2c.header) (eli : li = BitVec.ofNat 32 tl2c.len)
    (h118 : derElement 0x30 (memBytes M pi li.toNat) = .ok tl13)
    (h119 : li - BitVec.ofNat 32 (tl13.header + tl13.len) = 0)
    (epj : pj = pi + BitVec.ofNat 32 tl13.header) (elj : lj = BitVec.ofNat 32 tl13.len)
    (h120 : derIntIsOf M (memBytes M pj lj.toNat) pj (derElement 2 (memBytes M pj lj.toNat)) ((BitVec.ofNat 32 0x1).extractLsb' 0 8) = .ok true)
    (h121 : derElement 2 (memBytes M pj lj.toNat) = .ok te25)
    (epw : pw = pj + BitVec.ofNat 32 (te25.header + te25.len)) (elw : lw = lj - BitVec.ofNat 32 (te25.header + te25.len))
    (h122 : derElement 0x30 (memBytes M pw lw.toNat) = .ok tl31)
    (h123 : isSha256Of M (pw + BitVec.ofNat 32 (tl31.header + tl31.len)) (lw - BitVec.ofNat 32 (tl31.header + tl31.len)).toNat = .ok true)
    (h124 : derElement 0x30 (memBytes M (pw + BitVec.ofNat 32 (tl31.header + tl31.len))
      (lw - BitVec.ofNat 32 (tl31.header + tl31.len)).toNat) = .ok te39)
    (epx : px = pw + BitVec.ofNat 32 (tl31.header + tl31.len) + BitVec.ofNat 32 (te39.header + te39.len))
    (elx : lx = lw - BitVec.ofNat 32 (tl31.header + tl31.len) - BitVec.ofNat 32 (te39.header + te39.len))
    (h125 : derOptRes 0xA0 (memBytes M px lx.toNat) = some (.ok tl45))
    (hsa : readSignedAttributes (memBytes M (px + BitVec.ofNat 32 tl45.header) (BitVec.ofNat 32 tl45.len).toNat) = some md)
    (epy : py = px + BitVec.ofNat 32 (tl45.header + tl45.len)) (ely : ly = lx - BitVec.ofNat 32 (tl45.header + tl45.len))
    (h140 : derAlgOf M py ly.toNat = .ok ((op8, ol8), none))
    (h141 : derElement 0x30 (memBytes M py ly.toNat) = .ok te8)
    (h142 : memBytes M op8 ol8 = memBytes M (BitVec.ofNat 32 0x3FCC4818) 8)
    (epz : pz = py + BitVec.ofNat 32 (te8.header + te8.len)) (elz : lz = ly - BitVec.ofNat 32 (te8.header + te8.len))
    (h143 : derContent pz (derElement 4 (memBytes M pz lz.toNat)) = .ok (vp19, vl19))
    (h144 : derElement 4 (memBytes M pz lz.toNat) = .ok te19)
    (h145 : ecdsaSigOf 48 M vp19 vl19.toNat = .ok (sr, ss))
    (h146 : lz - BitVec.ofNat 32 (te19.header + te19.len) = 0)
    (htst : readTstInfo (memBytes M vp23 vl23.toNat) = some (gt, imp)) :
    parseTimestamp (memBytes M p0 l0.toNat) = some ⟨gt, imp, memBytes M vp23 vl23.toNat, md,
      memBytes M pw (BitVec.ofNat 32 (tl31.header + tl31.len)).toNat, memBytes M px (BitVec.ofNat 32 (tl45.header + tl45.len)).toNat,
      sr, ss⟩ := by
  rw [h93] at h92
  obtain ⟨e92a, e92b⟩ := derContent_ok rfl h92
  rw [h107] at h106
  obtain ⟨e106a, e106b⟩ := derContent_ok rfl h106
  rw [h112] at h111
  obtain ⟨e111a, e111b⟩ := derContent_ok rfl h111
  rw [h144] at h143
  obtain ⟨e143a, e143b⟩ := derContent_ok rfl h143
  unfold parseTimestamp
  rw [readElem_mem h84, restAt_nil h85]
  simp only [Option.bind_eq_bind, Option.bind_some, require_isEmpty_nil, elemAt]
  rw [← epr, ← elr, readElem_mem h86]
  simp only [Option.bind_some, elemAt]
  have hI0 := readIntegerIs_mem h88 h87
  rw [show ((BitVec.ofNat 32 0x0).extractLsb' 0 8).toNat = 0 by decide] at hI0
  have hI3 := readIntegerIs_mem h100 h99
  rw [show ((BitVec.ofNat 32 0x3).extractLsb' 0 8).toNat = 3 by decide] at hI3
  have hI1 := readIntegerIs_mem h121 h120
  rw [show ((BitVec.ofNat 32 0x1).extractLsb' 0 8).toNat = 1 by decide] at hI1
  rw [← eps, ← els, hI0, restAt_nil h89]
  simp only [Option.bind_some, require_isEmpty_nil, restAt]
  rw [← epa, ← ela, readElem_mem h90, restAt_nil h91]
  simp only [Option.bind_some, require_isEmpty_nil, elemAt]
  rw [← epc, ← elc, readOid_mem h93]
  simp only [Option.bind_some, restAt]
  rw [← e92a, ← e92b, h94, hsd, beq_iff_eq.mpr rfl, require_true]
  simp only [Option.bind_some]
  rw [← epe, ← ele, readElem_mem h95, restAt_nil h96]
  simp only [Option.bind_some, require_isEmpty_nil, elemAt]
  rw [← epd, ← eld, readElem_mem h97, restAt_nil h98]
  simp only [Option.bind_some, require_isEmpty_nil, elemAt]
  rw [← epq, ← elq, hI3]
  simp only [Option.bind_some, restAt]
  rw [← epg, ← elg, readElem_mem h101]
  simp only [Option.bind_some, elemAt]
  rw [readSha256Alg_code h102 h103, restAt_nil h104]
  simp only [Option.bind_some, require_isEmpty_nil, restAt]
  rw [← epn, ← eln, readElem_mem h105]
  simp only [Option.bind_some, elemAt]
  rw [← epk, ← elk, readOid_mem h107]
  simp only [Option.bind_some, restAt]
  rw [← e106a, ← e106b, h108, hti, beq_iff_eq.mpr rfl, require_true]
  simp only [Option.bind_some]
  rw [← ept, ← elt, readOptional_mem h109, restAt_nil h110]
  simp only [Option.bind_some, require_isEmpty_nil, elemAt]
  rw [← epv, ← elv, readOctetString_mem h112, restAt_nil h113]
  simp only [Option.bind_some, require_isEmpty_nil]
  rw [← e111a, ← e111b]
  obtain ⟨e114, h114a, h114b⟩ := h114
  rw [← epsd, ← elsd, h114a]
  simp only [Option.bind_some]
  rw [h114b, require_true]
  simp only [Option.bind_some]
  rw [readElem_mem h116, restAt_nil h117]
  simp only [Option.bind_some, require_isEmpty_nil, elemAt]
  rw [← epi, ← eli, readElem_mem h118, restAt_nil h119]
  simp only [Option.bind_some, require_isEmpty_nil, elemAt]
  rw [← epj, ← elj, hI1]
  simp only [Option.bind_some, restAt]
  rw [← epw, ← elw, readElem_mem h122]
  simp only [Option.bind_some, restAt]
  rw [readSha256Alg_code h123 h124]
  simp only [Option.bind_some, restAt]
  rw [← epx, ← elx, readOptional_mem h125]
  simp only [Option.bind_some, elemAt]
  rw [hsa]
  simp only [Option.bind_some, restAt]
  rw [← epy, ← ely]
  obtain ⟨t8, prm, ht8, hA, hP⟩ := readAlgorithm_mem h140
  have e8 : t8 = te8 := Except.ok.inj (ht8.symm.trans h141)
  subst e8
  cases prm with
  | some _ => cases hP
  | none =>
  rw [hA, memBytes_rest (derTlv_mem_bound (derElement_tlv h141))]
  simp only [Option.bind_some]
  rw [h142, hes, show (oidEcdsaSha256 == oidEcdsaSha256 && (none : Option Elem).isNone) = true by decide, require_true]
  simp only [Option.bind_some, restAt]
  rw [← epz, ← elz, readOctetString_mem h144, restAt_nil h146]
  simp only [Option.bind_some]
  rw [← e143a, ← e143b, ecdsaSignature_mem h145]
  simp only [Option.bind_some, require_isEmpty_nil]
  rw [htst]
  rfl

end C3.RV32.Sv
