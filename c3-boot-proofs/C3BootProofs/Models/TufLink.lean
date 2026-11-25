import C3BootProofs.Models.JsonLinkParse
import C3BootProofs.Models.JsonLinkWalk
import C3BootProofs.Models.JsonLinkValue
import C3BootProofs.Proofs.TufExpires
import C3BootProofs.Proofs.TufPemSpki

/-!
# The TUF position models and `Spec/Tuf.lean`

The machine-code theorems for `c3_verify::tuf` are stated with position
models: `expiresModel`, `pemSpkiModel`, `pmModel`, `prModel`, and
`rkModel`. This file relates them to the functions in `Spec/Tuf.lean`,
through the JSON link theorems in `Models/JsonLink.lean`.
-/

namespace C3.Json

open C3.RV32 (Word strRes)

theorem tl_strBody_res (v : Bytes) (p : Word) :
    strBody v = (strRes p v).map (fun _ => slice v 1 (v.length - 2)) := by
  unfold strBody strRes
  by_cases h1 : v.length < 2
  · rw [if_pos h1, if_pos h1]; rfl
  rw [if_neg h1, if_neg h1]
  by_cases h2 : v.getD 0 0 ≠ 34
  · rw [if_pos h2, if_pos h2]; rfl
  rw [if_neg h2, if_neg h2]
  by_cases h3 : v.getD (v.length - 1) 0 ≠ 34
  · rw [if_pos h3, if_pos h3]; rfl
  rw [if_neg h3, if_neg h3]; rfl

theorem tl_strRes_len {v : Bytes} {p q : Word} {l : Nat} (h : strRes p v = some (q, l)) : l = v.length - 2 := by
  unfold strRes at h
  by_cases h1 : v.length < 2
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : v.getD 0 0 ≠ 34
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  by_cases h3 : v.getD (v.length - 1) 0 ≠ 34
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3] at h
  cases h; rfl

/-- `strBody` on a value is `Json.asStr`. -/
theorem tl_strBody {c : Bool} {v : Bytes} {j : Json} (h : JVal c v j) : strBody v = j.asStr := by
  obtain ⟨h1, h2⟩ := StrRes c v j 0 h
  rw [tl_strBody_res v 0, h1]
  rcases hs : j.asStr with _ | s
  · rfl
  rw [hs] at h1
  have hl := tl_strRes_len h1
  simp only [Option.map] at h1 ⊢
  rw [← hl]; exact congrArg some (h2 s hs)

/-- `tuf::expires` on the `signed` value is `expires`: the model's `.ok`
time is the spec's, and its error is the spec's `none`. -/
theorem expiresModel_spec {c : Bool} {d : Bytes} {md : Meta} (h : JVal c d md.signed) :
    (expiresModel d).toOption = expires md := by
  unfold expiresModel expires
  have hf := ObjField c d md.signed (ascii!"expires") h
  rcases hj : md.signed.field (ascii!"expires") with _ | j'
  · rw [hj] at hf; simp only at hf; rw [hf]; rfl
  rw [hj] at hf; simp only at hf
  obtain ⟨vp, vl, ho, hd⟩ := hf
  rw [ho]; simp only
  rw [tl_strBody hd.2]
  change _ = (j'.asStr).bind rfc3339
  rcases j'.asStr with _ | t
  · rfl
  change _ = rfc3339 t
  simp only
  rcases rfc3339 t with _ | v <;> rfl

theorem tl_pem_lines (pem : Bytes) :
    pemSpki pem =
      if pem.take 27 = ascii!"-----BEGIN PUBLIC KEY-----\n" ∧ 52 ≤ pem.length ∧
          pem.drop (pem.length - 25) = ascii!"-----END PUBLIC KEY-----\n" then
        base64Decode (pemNoLf (slice pem 27 (pem.length - 52)))
      else none := by
  unfold pemSpki readExpect
  rw [show (ascii!"-----BEGIN PUBLIC KEY-----\n").length = 27 from rfl]
  by_cases hh : pem.take 27 = ascii!"-----BEGIN PUBLIC KEY-----\n" ∧ 27 ≤ pem.length
  · rw [if_pos (by rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]; exact hh)]
    change (require _).bind _ = _
    rw [show (ascii!"-----END PUBLIC KEY-----\n").length = 25 from rfl]
    have hd : (pem.drop 27).length = pem.length - 27 := List.length_drop
    by_cases hf : 52 ≤ pem.length ∧ pem.drop (pem.length - 25) = ascii!"-----END PUBLIC KEY-----\n"
    · rw [if_pos ⟨hh.1, hf⟩]
      have hs : List.isSuffixOf (ascii!"-----END PUBLIC KEY-----\n") (pem.drop 27) = true := by
        rw [List.isSuffixOf_iff_suffix, List.suffix_iff_eq_drop, List.drop_drop, hd,
          show (ascii!"-----END PUBLIC KEY-----\n").length = 25 from rfl,
          show 27 + (pem.length - 27 - 25) = pem.length - 25 by omega]
        exact hf.2.symm
      rw [hs]
      change base64Decode _ = _
      rw [hd, show pem.length - 27 - 25 = pem.length - 52 by omega]; rfl
    · rw [if_neg (fun h => hf h.2)]
      have hs : List.isSuffixOf (ascii!"-----END PUBLIC KEY-----\n") (pem.drop 27) = false := by
        rcases hb : List.isSuffixOf (ascii!"-----END PUBLIC KEY-----\n") (pem.drop 27) with _ | _
        · rfl
        rw [List.isSuffixOf_iff_suffix, List.suffix_iff_eq_drop, List.drop_drop, hd,
          show (ascii!"-----END PUBLIC KEY-----\n").length = 25 from rfl] at hb
        have hl := congrArg List.length hb
        rw [List.length_drop] at hl
        change 25 = pem.length - (27 + (pem.length - 27 - 25)) at hl
        exact absurd ⟨by omega, by rw [hb, show 27 + (pem.length - 27 - 25) = pem.length - 25 by omega]⟩ hf
      rw [hs]; rfl
  · rw [if_neg (by rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]; exact hh)]
    rw [if_neg (fun h => hh ⟨h.1, by omega⟩)]; rfl

/-- `pem_spki` decodes the spec's key, under its two limits: the text
between the lines has at most 192 bytes without its line feeds, and the
key has at most 128 bytes. -/
theorem pemSpkiModel_spec (pem k : Bytes) :
    pemSpkiModel pem = some k ↔
      pemSpki pem = some k ∧ (pemNoLf (slice pem 27 (pem.length - 52))).length ≤ 192 ∧ k.length ≤ 128 := by
  rw [tl_pem_lines]
  unfold pemSpkiModel
  by_cases H : pem.take 27 = ascii!"-----BEGIN PUBLIC KEY-----\n" ∧ 52 ≤ pem.length ∧
      pem.drop (pem.length - 25) = ascii!"-----END PUBLIC KEY-----\n"
  · rw [if_pos H, if_pos H]
    unfold pemDecode
    change (if (pemNoLf (slice pem 27 (pem.length - 52))).length ≤ 192 then _ else none) = some k ↔ _
    by_cases hl : (pemNoLf (slice pem 27 (pem.length - 52))).length ≤ 192
    · rw [if_pos hl]
      rcases base64Decode (pemNoLf (slice pem 27 (pem.length - 52))) with _ | bs
      · exact ⟨fun h => (nomatch h), fun h => (nomatch h.1)⟩
      change (if bs.length ≤ 128 then some bs else none) = some k ↔ _
      by_cases hb : bs.length ≤ 128
      · rw [if_pos hb]
        exact ⟨fun h => ⟨h, hl, (by cases h; exact hb)⟩, fun h => h.1⟩
      · rw [if_neg hb]
        exact ⟨fun h => (nomatch h), fun h => (by cases h.1; exact absurd h.2.2 hb)⟩
    · rw [if_neg hl]
      exact ⟨fun h => (nomatch h), fun h => absurd h.2.1 hl⟩
  · rw [if_neg H, if_neg H]
    exact ⟨fun h => (nomatch h), fun h => (nomatch h.1)⟩

end C3.Json
