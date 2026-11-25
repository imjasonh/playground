import C3BootProofs.Proofs.TufParseMetadata
import C3BootProofs.Proofs.TufExpires

/-!
# The error bytes of the `targets.json` checks

`AcceptTargets` hands each error byte that `parse_metadata`, `expires`, and
`Value::field` return to the rejection table, which takes codes below
`0x27`. These lemmas bound every error byte of the models of those
functions: each one is `0x19`, `0x20`, or `0x21`.
-/

namespace C3.Json

/-- Every error byte of `r` is below `0x27`. -/
def ActEB {α : Type} (r : Except Nat α) : Prop := ∀ e, r = .error e → e < 0x27

theorem act_eb_objGet (d key : Bytes) : ActEB (objGet d key) := by
  intro e h
  unfold objGet getOut at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; decide)

theorem act_eb_objField (d key : Bytes) : ActEB (objField d key) := by
  intro e h
  unfold objField at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; decide)
    | (cases h; exact act_eb_objGet d key _ ‹_›)

theorem act_eb_keysUnique (o key : Bytes) : ∀ k u pos, ActEB (keysUnique o key k u pos)
  | 0, _, _ => by intro e h; cases h
  | k + 1, u, pos => by
    intro e h
    simp only [keysUnique] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (cases h; decide)
      | exact act_eb_keysUnique o key k _ _ e h

theorem act_eb_keysStrict (o : Bytes) : ∀ k pos, ActEB (keysStrict o k pos)
  | 0, _ => by intro e h; cases h
  | k + 1, pos => by
    intro e h
    simp only [keysStrict] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (cases h; decide)
      | exact act_eb_keysStrict o k _ e h
      | (cases h; apply act_eb_keysUnique; assumption)

theorem act_eb_keysCanon (o : Bytes) : ∀ k prev pos, ActEB (keysCanon o k prev pos)
  | 0, _, _ => by intro e h; cases h
  | k + 1, prev, pos => by
    intro e h
    simp only [keysCanon] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (cases h; decide)
      | exact act_eb_keysCanon o k _ _ e h

theorem act_eb_checkKeys (c : Bool) (o : Bytes) : ActEB (checkKeys c o) := by
  intro e h
  unfold checkKeys at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; decide)
    | exact act_eb_keysCanon _ _ _ _ e h
    | exact act_eb_keysStrict _ _ _ e h

theorem act_eb_closeLoop (c : Bool) (d : Bytes) (start : Nat) :
    ∀ j stk pos, ActEB (closeLoop c d start j stk pos)
  | 0, _, _ => by intro e h; cases h
  | j + 1, stk, pos => by
    intro e h
    simp only [closeLoop] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (cases h; decide)
      | exact act_eb_closeLoop c d start j _ _ e h
      | (cases h; apply act_eb_checkKeys; assumption)

theorem act_eb_afterClose {r : Except Nat PStep} {next : List (Bool × Nat) → Nat → Except Nat (Nat × Nat)}
    (hr : ActEB r) (hn : ∀ stk p, ActEB (next stk p)) : ActEB (afterClose r next) := by
  intro e h
  unfold afterClose at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; apply hr; assumption)
    | (cases h; exact hr _ rfl)
    | exact hn _ _ e h

theorem act_eb_parseLoop (c : Bool) (d : Bytes) (start : Nat) :
    ∀ k stk pos, ActEB (parseLoop c d start k stk pos)
  | 0, _, _ => by intro e h; cases h; decide
  | k + 1, stk, pos => by
    intro e h
    simp only [parseLoop] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (cases h; decide)
      | exact act_eb_parseLoop c d start k _ _ e h
      | exact act_eb_afterClose (act_eb_closeLoop _ _ _ _ _ _) (act_eb_parseLoop c d start k) e h

theorem act_eb_parseModel (c : Bool) (d : Bytes) : ActEB (parseModel c d) :=
  act_eb_parseLoop _ _ _ _ _ _

theorem act_eb_pmLater (a kid : Bytes) : ∀ k pos, ActEB (pmLater a kid k pos)
  | 0, _ => by intro e h; cases h; decide
  | k + 1, pos => by
    intro e h
    simp only [pmLater] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (cases h; decide)
      | exact act_eb_pmLater a kid k _ e h
      | (cases h; apply act_eb_objField; assumption)

theorem act_eb_pmThen {α : Type} {r : Except Nat Unit} {k : Except Nat α} (hr : ActEB r) (hk : ActEB k) :
    ActEB (pmThen r k) := by
  intro e h
  unfold pmThen at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; apply hr; assumption)
    | (cases h; exact hr _ rfl)
    | exact hk e h

theorem act_eb_pmSigs (a : Bytes) : ∀ k pos, ActEB (pmSigs a k pos)
  | 0, _ => by intro e h; cases h; decide
  | k + 1, pos => by
    intro e h
    simp only [pmSigs] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (cases h; decide)
      | (cases h; apply act_eb_objField; assumption)
      | exact act_eb_pmThen (act_eb_pmLater _ _ _ _) (act_eb_pmSigs a k _) e h

theorem act_eb_pmObj (t kind : Bytes) : ActEB (pmObj t kind) := by
  intro e h
  unfold pmObj pmMembers pmTwo pmRest pmTy pmArr at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; decide)
    | (cases h; apply act_eb_objField; assumption)
    | exact act_eb_pmThen (act_eb_pmSigs _ _ _) (fun _ h => by cases h) e h
    | exact act_eb_pmThen (act_eb_pmSigs _ _ _) (fun _ h => by cases h) e h

theorem act_eb_pmModel (d kind : Bytes) : ActEB (pmModel d kind) := by
  intro e h
  unfold pmModel at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; apply act_eb_parseModel; assumption)
    | (cases h; apply act_eb_pmObj; assumption)

theorem act_eb_expiresModel (d : Bytes) : ActEB (expiresModel d) := by
  intro e h
  unfold expiresModel at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; decide)
    | (cases h; apply act_eb_objField; assumption)

end C3.Json
