import C3BootProofs.Models.JsonLinkFilter
import C3BootProofs.Models.TufLinkKeys
import C3BootProofs.Proofs.SvCosigLink
import C3BootProofs.Proofs.TufHexDecode

/-!
# Bytes below 256 in parsed JSON and decoded keys

Memory holds bytes, so the bytes that a proof reads from memory are below
256. These lemmas carry that bound through the spec's parsers:

- `parseValue_bytes`, `JVal_bytes`, and `parseJson_bytes`: every string and
  key of a value parsed from bytes below 256 is below 256 (`JBytes`).
- `parseHex_lt` and `decodeKey_lt`: decoded keys are bytes below 256
  whatever their text, because hex digits and base64 groups decode to bytes.
-/

namespace C3.Json

open C3

/-- Every element of `l` is below 256. -/
def Lt256 (l : Bytes) : Prop := ∀ x ∈ l, x < 256

/-- Every byte of each string and key in `j` is below 256, which is to say
every byte of `encode j` is. -/
def JBytes (j : Json) : Prop := Lt256 (encode j)

theorem trb_nil : Lt256 [] := fun _ h => nomatch h

theorem trb_app {a b : Bytes} : Lt256 (a ++ b) ↔ Lt256 a ∧ Lt256 b :=
  ⟨fun h => ⟨fun x hx => h x (List.mem_append.mpr (.inl hx)), fun x hx => h x (List.mem_append.mpr (.inr hx))⟩,
    fun h x hx => (List.mem_append.mp hx).elim (h.1 x) (h.2 x)⟩

theorem trb_cons {x : Nat} {l : Bytes} : Lt256 (x :: l) ↔ x < 256 ∧ Lt256 l :=
  ⟨fun h => ⟨h x (List.mem_cons.mpr (.inl rfl)), fun y hy => h y (List.mem_cons.mpr (.inr hy))⟩,
    fun h y hy => (List.mem_cons.mp hy).elim (fun e => e ▸ h.1) (h.2 y)⟩

theorem trb_suf {s x r : Bytes} (e : s = x ++ r) (h : Lt256 s) : Lt256 r := (trb_app.mp (e ▸ h)).2

theorem trb_pre {s x r : Bytes} (e : s = x ++ r) (h : Lt256 s) : Lt256 x := (trb_app.mp (e ▸ h)).1

theorem trb_ws (c : Bool) {s : Bytes} (h : Lt256 s) : Lt256 (ws c s) :=
  let ⟨_, e⟩ := jls_ws_suf c s
  trb_suf e h

theorem trb_drop : ∀ (n : Nat) {s : Bytes}, Lt256 s → Lt256 (s.drop n)
  | 0, _, h => h
  | _ + 1, [], h => h
  | n + 1, _ :: _, h => trb_drop n (trb_cons.mp h).2

theorem trb_decimal : ∀ f n, Lt256 (decimal f n)
  | 0, _ => trb_nil
  | f + 1, n => by
    rw [decimal, trb_app]
    refine ⟨?_, trb_cons.mpr ⟨by omega, trb_nil⟩⟩
    split
    · exact trb_nil
    · exact trb_decimal f _

theorem trb_str {s : Bytes} : JBytes (.str s) ↔ Lt256 s := by
  unfold JBytes
  rw [encode, trb_app, trb_app]
  exact ⟨fun h => h.1.2, fun h => ⟨⟨trb_cons.mpr ⟨by decide, trb_nil⟩, h⟩, trb_cons.mpr ⟨by decide, trb_nil⟩⟩⟩

theorem trb_obj {ms : List (Bytes × Json)} : JBytes (.obj ms) ↔ Lt256 (encodeMembers ms) := by
  unfold JBytes
  rw [encode, trb_app, trb_app]
  exact ⟨fun h => h.1.2, fun h => ⟨⟨trb_cons.mpr ⟨by decide, trb_nil⟩, h⟩, trb_cons.mpr ⟨by decide, trb_nil⟩⟩⟩

theorem trb_arr {js : List Json} : JBytes (.arr js) ↔ Lt256 (encodeElems js) := by
  unfold JBytes
  rw [encode, trb_app, trb_app]
  exact ⟨fun h => h.1.2, fun h => ⟨⟨trb_cons.mpr ⟨by decide, trb_nil⟩, h⟩, trb_cons.mpr ⟨by decide, trb_nil⟩⟩⟩

theorem trb_num (n : Nat) : JBytes (.num n) := by
  unfold JBytes; rw [encode]; exact trb_decimal _ _

theorem trb_bool (b : Bool) : JBytes (.bool b) := by
  unfold JBytes; cases b <;> (rw [encode]; unfold Lt256; decide)

theorem trb_null : JBytes .null := by
  unfold JBytes; rw [encode]; unfold Lt256; decide

theorem trb_mcons {k : Bytes} {v : Json} {more : List (Bytes × Json)} (hk : Lt256 k) (hv : JBytes v)
    (hm : Lt256 (encodeMembers more)) : Lt256 (encodeMembers ((k, v) :: more)) := by
  have q : Lt256 [0x22] := by unfold Lt256; decide
  have q2 : Lt256 [0x22, 0x3A] := by unfold Lt256; decide
  have q3 : Lt256 [0x2C] := by unfold Lt256; decide
  cases more with
  | nil =>
    rw [encodeMembers]
    exact trb_app.mpr ⟨trb_app.mpr ⟨trb_app.mpr ⟨q, hk⟩, q2⟩, hv⟩
  | cons p more =>
    obtain ⟨k', v'⟩ := p
    rw [encodeMembers]
    · exact trb_app.mpr ⟨trb_app.mpr ⟨trb_app.mpr ⟨trb_app.mpr ⟨trb_app.mpr ⟨q, hk⟩, q2⟩, hv⟩, q3⟩, hm⟩
    · intro e; cases e

theorem trb_econs {v : Json} {more : List Json} (hv : JBytes v) (hm : Lt256 (encodeElems more)) :
    Lt256 (encodeElems (v :: more)) := by
  have q3 : Lt256 [0x2C] := by unfold Lt256; decide
  cases more with
  | nil => rw [encodeElems]; exact hv
  | cons w more =>
    rw [encodeElems]
    · exact trb_app.mpr ⟨trb_app.mpr ⟨hv, q3⟩, hm⟩
    · intro e; cases e

theorem trb_mmem : ∀ {ms : List (Bytes × Json)}, Lt256 (encodeMembers ms) → ∀ p ∈ ms, Lt256 p.1 ∧ JBytes p.2
  | [], _, _, hp => nomatch hp
  | [(k, v)], h, p, hp => by
    rw [encodeMembers] at h
    obtain ⟨⟨⟨-, hk⟩, -⟩, hv⟩ := And.imp_left (And.imp_left trb_app.mp ∘ trb_app.mp) (trb_app.mp h)
    rcases List.mem_singleton.mp hp with rfl
    exact ⟨hk, hv⟩
  | (k, v) :: q :: more, h, p, hp => by
    rw [encodeMembers] at h
    rotate_left
    · intro e; cases e
    obtain ⟨h, hm⟩ := trb_app.mp h
    obtain ⟨h, -⟩ := trb_app.mp h
    obtain ⟨h, hv⟩ := trb_app.mp h
    obtain ⟨h, -⟩ := trb_app.mp h
    obtain ⟨-, hk⟩ := trb_app.mp h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨hk, hv⟩
    · exact trb_mmem hm p hp

theorem trb_emem : ∀ {js : List Json}, Lt256 (encodeElems js) → ∀ v ∈ js, JBytes v
  | [], _, _, hv => nomatch hv
  | [w], h, v, hv => by
    rw [encodeElems] at h
    rcases List.mem_singleton.mp hv with rfl
    exact h
  | w :: q :: more, h, v, hv => by
    rw [encodeElems] at h
    rotate_left
    · intro e; cases e
    obtain ⟨h, hm⟩ := trb_app.mp h
    obtain ⟨hw, -⟩ := trb_app.mp h
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hw
    · exact trb_emem hm v hv

theorem trb_lookup {key : Bytes} {v : Json} : ∀ {ms : List (Bytes × Json)}, ms.lookup key = some v → ∃ k, (k, v) ∈ ms
  | [], h => nomatch h
  | (k, w) :: ms, h => by
    unfold List.lookup at h
    split at h
    · cases h; exact ⟨k, List.mem_cons.mpr (.inl rfl)⟩
    · obtain ⟨k', hk⟩ := trb_lookup h
      exact ⟨k', List.mem_cons.mpr (.inr hk)⟩

/-! ## Reading values -/

theorem trb_field {j v : Json} {key : Bytes} (hj : JBytes j) (h : j.field key = some v) : JBytes v := by
  cases j with
  | obj ms =>
    obtain ⟨k, hk⟩ := trb_lookup (key := key) (ms := ms) h
    exact (trb_mmem (trb_obj.mp hj) _ hk).2
  | _ => cases h

theorem trb_asStr {j : Json} {s : Bytes} (hj : JBytes j) (h : j.asStr = some s) : Lt256 s := by
  cases j with
  | str s' => cases h; exact trb_str.mp hj
  | _ => cases h

theorem trb_asArr {j : Json} {js : List Json} (hj : JBytes j) (h : j.asArr = some js) : ∀ v ∈ js, JBytes v := by
  cases j with
  | arr js' => cases h; exact trb_emem (trb_arr.mp hj)
  | _ => cases h

theorem trb_mapM : ∀ {js : List Json} {ids : List Bytes}, (∀ v ∈ js, JBytes v) → js.mapM Json.asStr = some ids →
    ∀ id ∈ ids, Lt256 id
  | [], ids, _, h => by
    rw [List.mapM_nil] at h
    cases h
    intro _ h; nomatch h
  | v :: js, ids, hj, h => by
    rw [List.mapM_cons] at h
    obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ss, hss, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    intro id hid
    rcases List.mem_cons.mp hid with rfl | hid
    · exact trb_asStr (hj v (List.mem_cons.mpr (.inl rfl))) hs
    · exact trb_mapM (fun w hw => hj w (List.mem_cons.mpr (.inr hw))) hss id hid

/-! ## Parsing -/

theorem trb_numJ {s r : Bytes} {j : Json} (h : parseNumber s = some (j, r)) : JBytes j := by
  rw [jls_num_eq] at h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact trb_num _

theorem trb_litJ {s r : Bytes} {j : Json} (h : parseLiteral s = some (j, r)) : JBytes j := by
  rcases jls_lit_inv h with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩
  · exact trb_bool _
  · exact trb_bool _
  · exact trb_null

/-- The lax grammar of `JsonLinkLax.lean` reads only bytes below 256 into a
value from bytes below 256. -/
theorem trb_lax (c : Bool) : ∀ f,
    (∀ {dep s j r}, jlxValue c f dep s = some (j, r) → Lt256 s → JBytes j) ∧
    (∀ {dep s ms r}, jlxMembers c f dep s = some (ms, r) → Lt256 s → Lt256 (encodeMembers ms)) ∧
    (∀ {dep s js r}, jlxElems c f dep s = some (js, r) → Lt256 s → Lt256 (encodeElems js))
  | 0 => by
    refine ⟨fun h _ => ?_, fun h _ => ?_, fun h _ => ?_⟩
    · rw [jls_pv_zero] at h; cases h
    · rw [jls_pm_zero] at h; cases h
    · rw [jls_pe_zero] at h; cases h
  | f + 1 => by
    obtain ⟨ihv, ihm, ihe⟩ := trb_lax c f
    refine ⟨fun {dep s j r} h hs => ?_, fun {dep s ms r} h hs => ?_, fun {dep s js r} h hs => ?_⟩
    · rcases jls_pv_inv h with ⟨rest, rfl, -, ⟨rfl, -⟩ | ⟨ms, rfl, -, hm, -⟩⟩ |
          ⟨rest, rfl, -, ⟨rfl, -⟩ | ⟨it, rfl, -, he⟩⟩ |
          ⟨rest, st, rfl, rfl, hst⟩ | ⟨b, tl, rfl, -, -, -, -, hn⟩ | ⟨b, tl, rfl, -, -, -, -, hl⟩
      · exact trb_obj.mpr (by rw [encodeMembers]; exact trb_nil)
      · exact trb_obj.mpr (ihm hm (trb_ws c (trb_cons.mp hs).2))
      · exact trb_arr.mpr (by rw [encodeElems]; exact trb_nil)
      · exact trb_arr.mpr (ihe he (trb_ws c (trb_cons.mp hs).2))
      · exact trb_str.mpr (trb_pre (jls_str_suf c hst) (trb_cons.mp hs).2)
      · exact trb_numJ hn
      · exact trb_litJ hl
    · obtain ⟨rest, k, r1, r2, v, r3, rfl, h1, h2, h3, h4⟩ := jls_pm_inv h
      have e1 := jls_str_suf c h1
      have hrest := (trb_cons.mp hs).2
      have hk := trb_pre e1 hrest
      have hr1 := trb_ws c (trb_cons.mp (trb_suf e1 hrest)).2
      have hr2 := trb_ws c (trb_suf (jls_readExpect_suf h2) hr1)
      have hv := ihv h3 hr2
      obtain ⟨x3, -, e3⟩ := jls_pv_suf h3
      have hr3 := trb_ws c (trb_suf e3 hr2)
      rcases jls_mt_inv h4 with ⟨s', more, hs', hm, rfl⟩ | ⟨-, rfl⟩
      · rw [hs'] at hr3
        exact trb_mcons hk hv (ihm hm (trb_ws c (trb_cons.mp hr3).2))
      · exact trb_mcons hk hv (by rw [encodeMembers]; exact trb_nil)
    · obtain ⟨v, r1, h1, h2⟩ := jls_pe_inv h
      have hv := ihv h1 hs
      obtain ⟨x1, -, e1⟩ := jls_pv_suf h1
      have hr1 := trb_ws c (trb_suf e1 hs)
      rcases jls_et_inv h2 with ⟨s', more, hs', hm, rfl⟩ | ⟨-, rfl⟩
      · rw [hs'] at hr1
        exact trb_econs hv (ihe hm (trb_ws c (trb_cons.mp hr1).2))
      · exact trb_econs hv (by rw [encodeElems]; exact trb_nil)

/-- A value that `parseValue` reads from bytes below 256 has its strings and
keys below 256, and so do the bytes after it. -/
theorem parseValue_bytes {c : Bool} {f dep : Nat} {s r : Bytes} {j : Json}
    (h : parseValue c f dep s = some (j, r)) (hs : Lt256 s) : JBytes j ∧ Lt256 r := by
  have h' := (jlf_val.mp h).1
  obtain ⟨x, -, e⟩ := jls_pv_suf h'
  exact ⟨(trb_lax c f).1 h' hs, trb_suf e hs⟩

theorem JVal_bytes {c : Bool} {v : Bytes} {j : Json} (h : JVal c v j) (hv : Lt256 v) : JBytes j :=
  let ⟨_, _, h⟩ := h
  (parseValue_bytes h hv).1

theorem parseJson_bytes {c : Bool} {d : Bytes} {j : Json} (h : parseJson c d = some j) (hd : Lt256 d) :
    JBytes j := by
  unfold parseJson at h
  obtain ⟨⟨v, r⟩, hv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact (parseValue_bytes hv (trb_ws c hd)).1

/-! ## Keys -/

theorem parseHex_lt : ∀ {s k : Bytes}, parseHex s = some k → Lt256 k
  | [], k, h => by unfold parseHex at h; cases h; exact trb_nil
  | [_], _, h => by unfold parseHex at h; cases h
  | a :: b :: rest, k, h => by
    unfold parseHex at h
    obtain ⟨hi, hh, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨lo, hl, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    have := C3.RV32.thd_digit hh
    have := C3.RV32.thd_digit hl
    exact trb_cons.mpr ⟨by omega, parseHex_lt hr⟩

theorem pemSpki_lt {pem der : Bytes} (h : pemSpki pem = some der) : Lt256 der := by
  unfold pemSpki at h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  exact C3.RV32.Sv.base64Decode_lt h

theorem trb_spki {pem p pfx : Bytes} {kl : Nat} (h : (pemSpki pem >>= spkiPoint pfx kl) = some p) : Lt256 p := by
  obtain ⟨der, hd, hp⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨-, -, rfl⟩ := tlk_spki_len hp
  exact trb_drop _ (pemSpki_lt hd)

/-- A key that `decodeKey` accepts is bytes below 256, for any JSON value. -/
theorem decodeKey_lt {key : Json} {k : TufKey} (h : decodeKey key = some k) : Lt256 (keyTag k).2 := by
  unfold decodeKey at h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨pk, -, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · rcases hq : (pemSpki pk >>= spkiPoint p256SpkiPrefix 65) with _ | p
    · rw [hq] at h; cases h
    · rw [hq] at h
      cases (Option.some.inj h : TufKey.p256 p = k)
      exact trb_spki hq
  split at h
  · rcases hq : (pemSpki pk >>= spkiPoint p384SpkiPrefix 97) with _ | p
    · rw [hq] at h; cases h
    · rw [hq] at h
      cases (Option.some.inj h : TufKey.p384 p = k)
      exact trb_spki hq
  split at h
  · obtain ⟨k', hk, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact parseHex_lt hk
  · cases h

end C3.Json
