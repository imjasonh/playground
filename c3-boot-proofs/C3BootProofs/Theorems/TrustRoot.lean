import C3BootProofs.Spec.TrustRoot
import C3BootProofs.Theorems.Trace

/-!
# Trust-root monotonicity

The plan's `trust_root_monotone`: every slot the bootloader jumps to has a
key-set chain authorized from the genesis keys, a blob that the chain's last
key set signed, a chain level at most the blob's level, an image security
version equal to the blob's level, and a blob level at least the eFuse
level. The trace's slot results must come from `acceptContents` over the
flash contents at each step.
-/

namespace C3

variable {Key Msg Sig : Type} [DecidableEq Key]

/-- Each link is signed by two distinct keys of the set before it, at a
strictly higher level, starting from `keys` at `lvl` and ending at
`keys'` at `lvl'`. -/
inductive Authorized (verify : Key → Msg → Sig → Bool) :
    List Key → Nat → List (Link Key Msg Sig) → List Key → Nat → Prop where
  | nil (keys : List Key) (lvl : Nat) : Authorized verify keys lvl [] keys lvl
  | cons {keys : List Key} {lvl : Nat} {l : Link Key Msg Sig} {rest : List (Link Key Msg Sig)}
      {keys' : List Key} {lvl' : Nat}
      (hlt : lvl < l.level) (hmax : l.level ≤ maxLevel) (hkeys : validKeySet l.keys = true)
      (hsig : thresholdSigned verify keys l.msg l.sigs = true)
      (hrest : Authorized verify l.keys l.level rest keys' lvl') :
      Authorized verify keys lvl (l :: rest) keys' lvl'

theorem chainTip_authorized (verify : Key → Msg → Sig → Bool) :
    ∀ (links : List (Link Key Msg Sig)) (keys : List Key) (lvl : Nat) (keys' : List Key)
      (lvl' : Nat), chainTip verify keys lvl links = some (keys', lvl') →
        Authorized verify keys lvl links keys' lvl'
  | [], keys, lvl, keys', lvl', h => by
    simp only [chainTip, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .nil keys lvl
  | l :: rest, keys, lvl, keys', lvl', h => by
    unfold chainTip at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hlt, hmax⟩, hkeys⟩, hsig⟩ := hc
      exact .cons hlt hmax hkeys hsig (chainTip_authorized verify rest l.keys l.level keys' lvl' h)
    · simp at h

/-- The slot results that a device's flash contents give, before the level
rules against the eFuses. -/
def slotsOf (verify : Key → Msg → Sig → Bool) (genesis : List Key)
    (flash : Slot → Option (Contents Key Msg Sig)) (s : Slot) : Option Nat :=
  (flash s).bind (acceptContents verify genesis 0)

theorem trust_root_monotone (verify : Key → Msg → Sig → Bool) (genesis : List Key)
    {es : List Event} (h : Admissible es) (flash : Nat → Slot → Option (Contents Key Msg Sig))
    (hf : ∀ (j : Nat) (hj : j < es.length),
      (es[j]'hj).before.slots = slotsOf verify genesis (flash j))
    {j : Nat} (hj : j < es.length) {slot : Slot} {l : Nat}
    (hjump : (es[j]'hj).jump = some (slot, l)) :
    ∃ c keys tipLevel, flash j slot = some c ∧
      Authorized verify genesis 0 c.links keys tipLevel ∧
      thresholdSigned verify keys c.blob.msg c.blob.sigs = true ∧
      tipLevel ≤ c.blob.level ∧
      c.securityVersion = c.blob.level ∧
      level (es[j]'hj).before.fuses ≤ c.blob.level ∧
      l = c.blob.level := by
  have hs := h.step j hj
  rw [hjump] at hs
  obtain ⟨hl, _⟩ := hs.jump_facts
  obtain ⟨hslots, hle, _⟩ := accepted_some hl
  rw [hf j hj] at hslots
  unfold slotsOf at hslots
  cases hc : flash j slot with
  | none => rw [hc] at hslots; simp at hslots
  | some c =>
    rw [hc] at hslots
    simp only [Option.bind_some] at hslots
    unfold acceptContents at hslots
    split at hslots
    · rename_i keys tipLevel htip
      split at hslots
      · rename_i hcond
        simp only [Option.some.injEq] at hslots
        subst hslots
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        obtain ⟨⟨⟨_, hsig⟩, hcheck⟩, _⟩ := hcond
        unfold checkSlot at hcheck
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcheck
        obtain ⟨⟨⟨_, hsv⟩, htl⟩, _⟩ := hcheck
        exact ⟨c, keys, tipLevel, rfl, chainTip_authorized verify _ _ _ _ _ htip, hsig, htl,
          hsv, hle, rfl⟩
      · simp at hslots
    · simp at hslots

end C3
