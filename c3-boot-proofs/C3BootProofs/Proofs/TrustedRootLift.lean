import C3BootProofs.Proofs.TrustedRootValidFor
import C3BootProofs.Models.JsonLinkWalk
import C3BootProofs.Models.JsonLinkValue
import C3BootProofs.Spec.TrustedRoot

/-!
# `valid_for` and `Spec/TrustedRoot.lean`

`trustedRootValidFor_correct` states `valid_for` with the position model
`validForPos` on the bytes of a `Value`. When those bytes are one JSON
value `j` (`JVal`), `validForPos` is the spec's `validFor j`: an `.ok`
window is `validFor`'s window, and an error is `validFor j = none`.
`trustedRootValidFor_spec` states the machine-level theorem that way.
-/

namespace C3.RV32

open C3 C3.Json

/-- `tvfStr` is `Value::str`'s result, sliced. -/
theorem trl_str (v : Bytes) : tvfStr v = (strRes 0 v).map (fun x => slice v 1 x.2) := by
  unfold tvfStr strRes
  by_cases h1 : v.length < 2
  · rw [ite_eq_left h1, ite_eq_left h1]; rfl
  rw [ite_eq_right h1, ite_eq_right h1]
  by_cases h2 : v.getD 0 0 ≠ 34
  · rw [ite_eq_left h2, ite_eq_left h2]; rfl
  rw [ite_eq_right h2, ite_eq_right h2]
  by_cases h3 : v.getD (v.length - 1) 0 ≠ 34
  · rw [ite_eq_left h3, ite_eq_left h3]; rfl
  rw [ite_eq_right h3, ite_eq_right h3]
  rfl

/-- On a value, `tvfStr` is `Json.asStr`. -/
theorem trl_strJ {c : Bool} {v : Bytes} {j : Json} (h : JVal c v j) : tvfStr v = j.asStr := by
  obtain ⟨h1, h2⟩ := StrRes c v j 0 h
  rw [trl_str, h1]
  cases hs : j.asStr with
  | none => rfl
  | some s => exact congrArg some (h2 s hs)

/-- On a value, `tvfTime` is `Json.asStr` then `rfc3339`. -/
theorem trl_time {c : Bool} {v : Bytes} {j : Json} (h : JVal c v j) :
    (tvfTime v).toOption = (j.asStr >>= rfc3339) := by
  unfold tvfTime
  rw [trl_strJ h]
  cases j.asStr with
  | none => rfl
  | some s =>
    show (match rfc3339 s with
      | none => Except.error 25
      | some t => Except.ok t).toOption = rfc3339 s
    cases rfc3339 s <;> rfl

/-- `tvfRest` on the object whose members are `ms`. -/
theorem trl_rest {c : Bool} {d : Bytes} {ms : List (Bytes × Json)} (h : JVal c d (.obj ms)) (t : Nat) :
    (tvfRest d t).toOption =
      (match ms.lookup (ascii!"end") with
        | none => pure u64Max
        | some e => e.asStr >>= rfc3339).map (fun u => (t, u)) := by
  have hG := ObjGet c d (.obj ms) (ascii!"end") h
  dsimp only [Json.asObj] at hG
  unfold tvfRest
  revert hG
  cases ms.lookup (ascii!"end") with
  | none =>
    intro hG
    rw [hG]
    rfl
  | some e =>
    intro hG
    obtain ⟨vp, vl, hg, -, hv⟩ := hG
    rw [hg]
    have ht := trl_time hv
    show (match tvfTime (slice d vp vl) with
      | .error e => .error e
      | .ok u => .ok (t, u) : Except Nat (Nat × Nat)).toOption = _
    revert ht
    cases tvfTime (slice d vp vl) with
    | error _ => intro ht; exact congrArg (Option.map fun u => (t, u)) ht
    | ok u => intro ht; exact congrArg (Option.map fun u => (t, u)) ht

/-- `validFor` on an object, with its lookups in order. -/
theorem trl_vf (ms : List (Bytes × Json)) :
    validFor (.obj ms) = (ms.lookup (ascii!"start") >>= Json.asStr >>= rfc3339).bind fun start =>
      (match ms.lookup (ascii!"end") with
        | none => some u64Max
        | some e => e.asStr >>= rfc3339).map fun stop => (⟨start, stop⟩ : Window) := by
  unfold validFor
  dsimp only [Json.field]
  cases ms.lookup (ascii!"end") with
  | none => cases (ms.lookup (ascii!"start") >>= Json.asStr >>= rfc3339) <;> rfl
  | some e =>
    dsimp only
    cases (ms.lookup (ascii!"start") >>= Json.asStr >>= rfc3339) <;> cases (e.asStr >>= rfc3339) <;> rfl

/-- `valid_for`'s position model is the spec's `validFor` on the value its
bytes hold: the same window, or an error exactly when `validFor` is
`none`. -/
theorem validForPos_spec {c : Bool} {d : Bytes} {j : Json} (h : JVal c d j) :
    (validForPos d).toOption.map (fun x => (⟨x.1, x.2⟩ : Window)) = validFor j := by
  have hF := ObjField c d j (ascii!"start") h
  revert hF
  cases hs : j.field (ascii!"start") with
  | none =>
    intro hF
    unfold validForPos validFor
    rw [hF, hs]
    rfl
  | some js =>
    intro hF
    obtain ⟨vp, vl, hof, -, hv⟩ := hF
    obtain ⟨ms, rfl⟩ : ∃ ms, j = .obj ms := by
      cases j with
      | obj ms => exact ⟨ms, rfl⟩
      | _ => cases hs
    have hl : ms.lookup (ascii!"start") = some js := hs
    rw [trl_vf, hl]
    unfold validForPos
    rw [hof]
    have ht := trl_time hv
    have hr := trl_rest h
    show (match tvfTime (slice d vp vl) with
      | .error e => .error e
      | .ok t => tvfRest d t : Except Nat (Nat × Nat)).toOption.map _ = _
    revert ht
    cases tvfTime (slice d vp vl) with
    | error _ =>
      intro ht
      rw [show (some js >>= Json.asStr >>= rfc3339) = none from ht.symm]
      rfl
    | ok t =>
      intro ht
      rw [show (some js >>= Json.asStr >>= rfc3339) = some t from ht.symm]
      show (tvfRest d t).toOption.map _ = _
      rw [hr t]
      cases ms.lookup (ascii!"end") with
      | none => rfl
      | some e =>
        dsimp only
        cases (e.asStr >>= rfc3339) <;> rfl

/-- `trustedRootValidFor_correct` in the spec's terms: when the `n` bytes
at `p` are one JSON value `j`, `valid_for` writes `Ok` with
`validFor j`'s window, or `Err` when `validFor j` is `none`. -/
theorem trustedRootValidFor_spec (m : Machine) {sp0 out p retAddr : Word} {n : Nat} {c : Bool} {j : Json}
    (hc : TvfCode m.mem) (hpc : m.pc = TVF) (ha0 : reg m a0 = out) (ha1 : reg m a1 = p)
    (ha2 : reg m a2 = BitVec.ofNat 32 n) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = sp0) (hsa : sp0.toNat % 4 = 0) (hsl : 0x144 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000)
    (hoa : out.toNat % 4 = 0) (how : out.toNat + 0x18 ≤ 0x40000000) (hpw : p.toNat + n + 4 ≤ 0x40000000)
    (hp0 : p.toNat ≠ 0) (sOG : Sep out 0x18 (sp0 + 0xFFFFFEBC) 0x144) (sPG : Sep p (n + 4) (sp0 + 0xFFFFFEBC) 0x144)
    (sRO : Sep (sp0 + 0xFFFFFEBC) 0x144 TVF_RO 0x1400)
    (hks : memBytes m.mem tvfStartKey 5 = ascii!"start") (hke : memBytes m.mem tvfEndKey 3 = ascii!"end")
    (hj : JVal c (memBytes m.mem p n) j) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q : Fin 32, q.val ∈ trSaved → reg m' q = reg m q) ∧
      ∃ r, tvfMem m.mem (sp0 + 0xFFFFFEBC) out r m'.mem ∧
        r.toOption.map (fun x => (⟨x.1, x.2⟩ : Window)) = validFor j := by
  obtain ⟨m', hs, hpc', hsp', hk, hR⟩ := trustedRootValidFor_correct m hc hpc ha0 ha1 ha2 hra hret hsp hsa hsl
    hsw hoa how hpw hp0 sOG sPG sRO hks hke
  exact ⟨m', hs, hpc', hsp', hk, _, hR, validForPos_spec hj⟩

end C3.RV32
