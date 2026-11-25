import C3BootProofs.Models.JsonLink
import C3BootProofs.Models.JsonLinkSpec
import C3BootProofs.Models.JsonLinkPos

/-!
# Canonical values are their encoding

In canonical mode, the bytes that `parseValue` reads are `encode` of the
value it returns.
-/

namespace C3.Json

theorem jlc_dv_ge : ∀ (acc : Nat) (l : Bytes), acc ≤ l.foldl (fun n d => 10 * n + (d - 48)) acc
  | _, [] => Nat.le_refl _
  | acc, d :: l => Nat.le_trans (by omega : acc ≤ 10 * acc + (d - 48)) (jlc_dv_ge _ l)

theorem jlc_dv_snoc (l : Bytes) (d : Nat) : digitsValue (l ++ [d]) = 10 * digitsValue l + (d - 48) := by
  unfold digitsValue; rw [List.foldl_append]; rfl

theorem jlc_digit {b : Nat} (h : isDigit b = true) : 48 ≤ b ∧ b ≤ 57 := by
  unfold isDigit at h; rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at h; exact h

/-- `decimal` writes back the digits of a number with no leading zero. -/
theorem jlc_decimal : ∀ (n : Nat) (ds : Bytes), ds.length = n + 1 → ds.all isDigit = true →
    (n = 0 ∨ ds.head? ≠ some 48) → n ≤ digitsValue ds ∧ ∀ F, n + 1 ≤ F → decimal F (digitsValue ds) = ds
  | 0, ds, hl, hd, _ => by
    match ds, hl with
    | [a], _ =>
      have ha := jlc_digit (by simpa only [List.all_cons, List.all_nil, Bool.and_true] using hd)
      have hv : digitsValue [a] = a - 48 := by unfold digitsValue; show 10 * 0 + (a - 48) = a - 48; omega
      refine ⟨Nat.zero_le _, fun F hF => ?_⟩
      obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      rw [hv, decimal, jlp_if_pos (by omega), List.nil_append, Nat.mod_eq_of_lt (by omega)]
      rw [show 48 + (a - 48) = a by omega]
  | n + 1, ds, hl, hd, hh => by
    rcases List.eq_nil_or_concat ds with rfl | ⟨L, b, rfl⟩
    · cases hl
    rw [List.concat_eq_append] at hl hd hh ⊢
    rw [List.length_append, List.length_singleton] at hl
    rw [List.all_append, Bool.and_eq_true] at hd
    have hb := jlc_digit (by simpa only [List.all_cons, List.all_nil, Bool.and_true] using hd.2)
    have hL : L ≠ [] := fun h => by rw [h, List.length_nil] at hl; omega
    obtain ⟨a0, L0, hL0⟩ := List.exists_cons_of_ne_nil hL
    have hh' : L.head? ≠ some 48 := by
      rw [hL0] at hh ⊢; rcases hh with h | h; omega; exact h
    have ih := jlc_decimal n L (by omega) hd.1 (.inr hh')
    have hv1 : 1 ≤ digitsValue L := by
      have hdl := hd.1
      rw [hL0, List.all_cons, Bool.and_eq_true] at hdl
      have ha := jlc_digit hdl.1
      have ha' : a0 ≠ 48 := fun h => hh' (by rw [hL0, h]; rfl)
      have := jlc_dv_ge (10 * 0 + (a0 - 48)) L0
      rw [hL0]; unfold digitsValue
      exact Nat.le_trans (by omega) this
    rw [jlc_dv_snoc]
    refine ⟨by omega, fun F hF => ?_⟩
    obtain ⟨F, rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    rw [decimal, jlp_if_neg (by omega), show (10 * digitsValue L + (b - 48)) / 10 = digitsValue L by omega,
      ih.2 F (by omega), show (10 * digitsValue L + (b - 48)) % 10 = b - 48 by omega,
      show 48 + (b - 48) = b by omega]

theorem jlc_num {s r : Bytes} {j : Json} (h : parseNumber s = some (j, r)) : s = encode j ++ r := by
  rw [jls_num_eq] at h
  obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  have h1 := require_eq_some.mp hu
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, Bool.or_eq_true] at h1
  obtain ⟨⟨hlo, hhi⟩, hz⟩ := h1
  have hall : (s.takeWhile isDigit).all isDigit = true := List.all_takeWhile
  have hpre : s.takeWhile isDigit = s.take (s.takeWhile isDigit).length :=
    List.prefix_iff_eq_take.mp (List.takeWhile_prefix isDigit)
  have hz' : (s.takeWhile isDigit).length - 1 = 0 ∨ (s.takeWhile isDigit).head? ≠ some 48 := by
    rcases hz with hz | hz
    · exact .inl (by rw [beq_iff_eq.mp hz])
    · exact .inr (bne_iff_ne.mp hz)
  have hdec := (jlc_decimal _ _ (by omega) hall hz').2 (digitsValue (s.takeWhile isDigit) + 1)
    (by have := (jlc_decimal _ _ (by omega) hall hz').1; omega)
  show s = decimal (digitsValue (s.takeWhile isDigit) + 1) (digitsValue (s.takeWhile isDigit)) ++
    s.drop (s.takeWhile isDigit).length
  rw [hdec]
  conv => lhs; rw [← List.take_append_drop (s.takeWhile isDigit).length s]
  rw [← hpre]

theorem jlc_lit {s r : Bytes} {j : Json} (h : parseLiteral s = some (j, r)) : s = encode j ++ r := by
  rcases jls_lit_inv h with ⟨h1, rfl⟩ | ⟨-, h1, rfl⟩ | ⟨-, -, h1, rfl⟩ <;> exact jls_readExpect_suf h1

/-- Canonical parses read the encoding of what they return. -/
def jlcEnc (f : Nat) : Prop :=
  (∀ {dep : Nat} {s r : Bytes} {j : Json}, parseValue true f dep s = some (j, r) → s = encode j ++ r) ∧
  (∀ {dep : Nat} {s r : Bytes} {ms : List (Bytes × Json)}, parseMembers true f dep s = some (ms, r) →
    ms ≠ [] ∧ s = encodeMembers ms ++ 125 :: r) ∧
  (∀ {dep : Nat} {s r : Bytes} {js : List Json}, parseElems true f dep s = some (js, r) →
    js ≠ [] ∧ s = encodeElems js ++ 93 :: r)

theorem jlc_ws (s : Bytes) : ws true s = s := rfl

theorem jlc_all : ∀ f, jlcEnc f
  | 0 => ⟨fun h => (by rw [jls_pv_zero] at h; cases h), fun h => (by rw [jls_pm_zero] at h; cases h),
      fun h => (by rw [jls_pe_zero] at h; cases h)⟩
  | f + 1 => by
    have ih := jlc_all f
    refine ⟨fun {dep s r j} h => ?_, fun {dep s r ms} h => ?_, fun {dep s r js} h => ?_⟩
    · rcases jls_pv_inv h with ⟨rest, rfl, -, ⟨rfl, hw⟩ | ⟨ms, rfl, -, hm, -⟩⟩ |
          ⟨rest, rfl, -, ⟨rfl, hw⟩ | ⟨js, rfl, -, hm⟩⟩ | ⟨rest, st, rfl, rfl, hs⟩ |
          ⟨b, tl, rfl, -, -, -, -, hn⟩ | ⟨b, tl, rfl, -, -, -, -, hn⟩
      · rw [jlc_ws] at hw; rw [hw]; rfl
      · obtain ⟨-, hr⟩ := ih.2.1 hm
        rw [jlc_ws] at hr; rw [hr]
        show 123 :: (encodeMembers ms ++ 125 :: r) = ([123] ++ encodeMembers ms ++ [125]) ++ r
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      · rw [jlc_ws] at hw; rw [hw]; rfl
      · obtain ⟨-, hr⟩ := ih.2.2 hm
        rw [jlc_ws] at hr; rw [hr]
        show 91 :: (encodeElems js ++ 93 :: r) = ([91] ++ encodeElems js ++ [93]) ++ r
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      · rw [jls_str_suf true hs]
        show 34 :: (st ++ 34 :: r) = ([34] ++ st ++ [34]) ++ r
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      · exact jlc_num hn
      · exact jlc_lit hn
    · obtain ⟨rest, k, r1, r2, v, r3, rfl, hk, hc, hv, ht⟩ := jls_pm_inv h
      rw [jls_str_suf true hk]
      rw [jlc_ws] at hc
      rw [jls_readExpect_suf hc]
      rw [jlc_ws] at hv
      rw [ih.1 hv]
      rcases jls_mt_inv ht with ⟨s', more, hs1, hm, rfl⟩ | ⟨hs1, rfl⟩
      · rw [jlc_ws] at hs1; rw [hs1]
        obtain ⟨hne, hr⟩ := ih.2.1 hm
        rw [jlc_ws] at hr; rw [hr]
        match more, hne with
        | m :: more', _ =>
          refine ⟨List.cons_ne_nil _ _, ?_⟩
          show 34 :: (k ++ 34 :: ([58] ++ (encode v ++ 44 :: (encodeMembers (m :: more') ++ 125 :: r)))) =
            ([34] ++ k ++ [34, 58] ++ encode v ++ [44] ++ encodeMembers (m :: more')) ++ 125 :: r
          simp only [List.append_assoc, List.cons_append, List.nil_append]
      · rw [jlc_ws] at hs1; rw [hs1]
        refine ⟨List.cons_ne_nil _ _, ?_⟩
        show 34 :: (k ++ 34 :: ([58] ++ (encode v ++ 125 :: r))) = ([34] ++ k ++ [34, 58] ++ encode v) ++ 125 :: r
        simp only [List.append_assoc, List.cons_append, List.nil_append]
    · obtain ⟨v, r1, hv, ht⟩ := jls_pe_inv h
      rw [ih.1 hv]
      rcases jls_et_inv ht with ⟨s', more, hs1, hm, rfl⟩ | ⟨hs1, rfl⟩
      · rw [jlc_ws] at hs1; rw [hs1]
        obtain ⟨hne, hr⟩ := ih.2.2 hm
        rw [jlc_ws] at hr; rw [hr]
        match more, hne with
        | m :: more', _ =>
          refine ⟨List.cons_ne_nil _ _, ?_⟩
          show encode v ++ 44 :: (encodeElems (m :: more') ++ 93 :: r) =
            (encode v ++ [44] ++ encodeElems (m :: more')) ++ 93 :: r
          simp only [List.append_assoc, List.cons_append, List.nil_append]
      · rw [jlc_ws] at hs1; rw [hs1]
        exact ⟨List.cons_ne_nil _ _, rfl⟩

theorem CanonEncode : CanonEncodeStmt := fun _ _ ⟨f, _, h⟩ => by
  have := (jlc_all f).1 h
  rwa [List.append_nil] at this

end C3.Json
