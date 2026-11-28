import C3BootProofs.Proofs.TufParseRoot
import C3BootProofs.Proofs.TufRoleKeys
import C3BootProofs.Proofs.TufExpires

/-!
# The error bytes of the pinned root's checks

The closure's rejection table has entries for the `TufError` codes up to
`Read` (0x26) only, so a stage that rejects with the error byte of
`parse_root`, `RoleKeys::read`, or `expires` has to know that byte is below
0x27. Each model here returns `0x19`, `0x20`, `0x21`, or the error of a
model it calls.
-/

namespace C3.RV32.Ac

open C3.Json

set_option hygiene false in
/-- Splits `h : f … = .error e` until each case is a literal error or a
call's error. -/
macro "acp_go" : tactic =>
  `(tactic| repeat' (first | (cases h; done) | (cases h; decide) | split at h))

theorem acp_objGet (d key : Bytes) : ∀ e, objGet d key = .error e → e < 0x27 := by
  intro e h
  unfold objGet getOut at h
  acp_go

theorem acp_objField (d key : Bytes) : ∀ e, objField d key = .error e → e < 0x27 := by
  intro e h
  unfold objField at h
  acp_go
  all_goals (cases h; exact acp_objGet _ _ _ ‹_›)

theorem acp_keysUnique (o key : Bytes) : ∀ k u pos e, keysUnique o key k u pos = .error e → e < 0x27
  | 0, _, _, _, h => by cases h
  | k + 1, u, pos, e, h => by
    simp only [keysUnique] at h
    acp_go
    all_goals exact acp_keysUnique o key k _ _ e h

theorem acp_keysStrict (o : Bytes) : ∀ k pos e, keysStrict o k pos = .error e → e < 0x27
  | 0, _, _, h => by cases h
  | k + 1, pos, e, h => by
    simp only [keysStrict] at h
    acp_go
    all_goals first
      | exact acp_keysStrict o k _ e h
      | (cases h; exact acp_keysUnique _ _ _ _ _ _ ‹_›)

theorem acp_keysCanon (o : Bytes) : ∀ k prev pos e, keysCanon o k prev pos = .error e → e < 0x27
  | 0, _, _, _, h => by cases h
  | k + 1, prev, pos, e, h => by
    simp only [keysCanon] at h
    acp_go
    all_goals exact acp_keysCanon o k _ _ e h

theorem acp_checkKeys (c : Bool) (o : Bytes) : ∀ e, checkKeys c o = .error e → e < 0x27 := by
  intro e h
  unfold checkKeys at h
  acp_go
  all_goals first
    | exact acp_keysCanon _ _ _ _ e h
    | exact acp_keysStrict _ _ _ e h

theorem acp_closeLoop (c : Bool) (d : Bytes) (start : Nat) :
    ∀ j stk pos e, closeLoop c d start j stk pos = .error e → e < 0x27
  | 0, _, _, _, h => by cases h
  | j + 1, stk, pos, e, h => by
    simp only [closeLoop] at h
    acp_go
    all_goals first
      | exact acp_closeLoop c d start j _ _ e h
      | (cases h; exact acp_checkKeys _ _ _ ‹_›)

theorem acp_afterClose {r : Except Nat PStep} {next : List (Bool × Nat) → Nat → Except Nat (Nat × Nat)}
    (hr : ∀ e, r = .error e → e < 0x27) (hn : ∀ stk p e, next stk p = .error e → e < 0x27) :
    ∀ e, afterClose r next = .error e → e < 0x27 := by
  intro e h
  unfold afterClose at h
  acp_go
  all_goals first
    | (cases h; exact hr _ ‹_›)
    | (cases h; exact hr _ rfl)
    | exact hn _ _ e h

theorem acp_parseLoop (c : Bool) (d : Bytes) (start : Nat) :
    ∀ k stk pos e, parseLoop c d start k stk pos = .error e → e < 0x27
  | 0, _, _, _, h => by cases h; decide
  | k + 1, stk, pos, e, h => by
    simp only [parseLoop] at h
    acp_go
    all_goals first
      | exact acp_parseLoop c d start k _ _ e h
      | exact acp_afterClose (acp_closeLoop c d start _ _ _) (acp_parseLoop c d start k) e h

theorem acp_parseModel (c : Bool) (d : Bytes) : ∀ e, parseModel c d = .error e → e < 0x27 := by
  intro e h
  exact acp_parseLoop _ _ _ _ _ _ e h

theorem acp_pmThen {α : Type} {r : Except Nat Unit} {k : Except Nat α} (hr : ∀ e, r = .error e → e < 0x27)
    (hk : ∀ e, k = .error e → e < 0x27) : ∀ e, pmThen r k = .error e → e < 0x27 := by
  intro e h
  unfold pmThen at h
  acp_go
  all_goals first
    | (cases h; exact hr _ ‹_›)
    | (cases h; exact hr _ rfl)
    | exact hk e h

theorem acp_pmLater (a kid : Bytes) : ∀ k pos e, pmLater a kid k pos = .error e → e < 0x27
  | 0, _, _, h => by cases h; decide
  | k + 1, pos, e, h => by
    simp only [pmLater] at h
    acp_go
    all_goals first
      | exact acp_pmLater a kid k _ e h
      | (cases h; exact acp_objField _ _ _ ‹_›)

theorem acp_pmSigs (a : Bytes) : ∀ k pos e, pmSigs a k pos = .error e → e < 0x27
  | 0, _, _, h => by cases h; decide
  | k + 1, pos, e, h => by
    simp only [pmSigs] at h
    acp_go
    all_goals first
      | exact acp_pmThen (acp_pmLater _ _ _ _) (acp_pmSigs a k _) e h
      | (cases h; exact acp_objField _ _ _ ‹_›)

theorem acp_pmArr (a : Bytes) : ∀ e, pmArr a = .error e → e < 0x27 := by
  intro e h
  unfold pmArr at h
  acp_go
  all_goals exact acp_pmSigs _ _ _ e h

theorem acp_pmTy (v a kind : Bytes) : ∀ e, pmTy v a kind = .error e → e < 0x27 := by
  intro e h
  unfold pmTy at h
  acp_go
  all_goals first
    | exact acp_pmArr _ e h
    | (cases h; exact acp_objField _ _ _ ‹_›)

theorem acp_pmRest (t kind : Bytes) (a2 v1p v1l v2p v2l : Nat) :
    ∀ e, pmRest t kind a2 v1p v1l v2p v2l = .error e → e < 0x27 := by
  intro e h
  unfold pmRest at h
  acp_go
  all_goals exact acp_pmTy _ _ _ e h

theorem acp_pmTwo (t kind : Bytes) (a1 k1p k1l v1p v1l : Nat) :
    ∀ e, pmTwo t kind a1 k1p k1l v1p v1l = .error e → e < 0x27 := by
  intro e h
  unfold pmTwo at h
  acp_go
  all_goals exact acp_pmThen (acp_pmRest _ _ _ _ _ _ _) (fun _ h' => by cases h') e h

theorem acp_pmObj (t kind : Bytes) : ∀ e, pmObj t kind = .error e → e < 0x27 := by
  intro e h
  unfold pmObj pmMembers at h
  acp_go
  all_goals exact acp_pmTwo _ _ _ _ _ _ _ e h

theorem acp_pmModel (d kind : Bytes) : ∀ e, pmModel d kind = .error e → e < 0x27 := by
  intro e h
  unfold pmModel at h
  acp_go
  all_goals first
    | (cases h; exact acp_parseModel _ _ _ ‹_›)
    | (cases h; exact acp_pmObj _ _ _ ‹_›)

/-- `parse_root`'s error byte is a `TufError` code. -/
theorem acp_prModel (d : Bytes) : ∀ e, prModel d = .error e → e < 0x27 := by
  intro e h
  unfold prModel at h
  acp_go
  all_goals first
    | (cases h; exact acp_pmModel _ _ _ ‹_›)
    | (cases h; exact acp_objField _ _ _ ‹_›)

theorem acp_rkLoop (a kv : Bytes) : ∀ k pos e, rkLoop a kv k pos = .error e → e < 0x27
  | 0, pos, e, h => by
    rw [rkLoop] at h
    try simp only at h
    acp_go
  | k + 1, pos, e, h => by
    rw [rkLoop] at h
    try simp only at h
    acp_go
    all_goals first
      | (cases h; exact acp_objGet _ _ _ ‹_›)
      | (cases h; exact acp_rkLoop a kv k _ _ ‹_›)

theorem acp_rkRole (r kv : Bytes) : ∀ e, rkRole r kv = .error e → e < 0x27 := by
  intro e h
  unfold rkRole rkIds at h
  acp_go
  all_goals first
    | exact acp_rkLoop _ _ _ _ e h
    | (cases h; exact acp_objField _ _ _ ‹_›)

/-- `RoleKeys::read`'s error byte is a `TufError` code. -/
theorem acp_rkModel (d role : Bytes) : ∀ e, rkModel d role = .error e → e < 0x27 := by
  intro e h
  unfold rkModel at h
  acp_go
  all_goals first
    | (cases h; exact acp_objField _ _ _ ‹_›)
    | (cases h; exact acp_rkRole _ _ _ ‹_›)

/-- `expires`'s error byte is a `TufError` code. -/
theorem acp_expiresModel (d : Bytes) : ∀ e, expiresModel d = .error e → e < 0x27 := by
  intro e h
  unfold expiresModel at h
  acp_go
  all_goals (cases h; exact acp_objField _ _ _ ‹_›)

end C3.RV32.Ac
