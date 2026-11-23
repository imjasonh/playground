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

end C3.RV32.Sv
