import C3BootProofs.Proofs.ImageTopCur
import C3BootProofs.Proofs.ImageSpecSegs

/-!
# What `accept_slot` reads from `image::parse`'s result

`accept_slot` logs `image::parse`'s error code, so the code must be one the
log table has, and it reads byte 0xC of the result as the success marker, so
a successful parse must not leave 0xFF there. `aci_imgW_err` says that every
error `imgW` decides is below 12, and `aci_imgW_ok` says that a successful
parse has at least one segment and every segment's kind is at most 3.
-/

namespace C3

open C3.RV32

/-- Every error that `x` can return is below 12. -/
def aci_EB {α : Type} (x : Except (BitVec 8) α) : Prop := ∀ e, x = .error e → e.toNat < 12

theorem aci_eb_ok {α : Type} (a : α) : aci_EB (.ok a : Except (BitVec 8) α) := fun _ h => nomatch h

theorem aci_eb_pure {α : Type} (a : α) : aci_EB (pure a : Except (BitVec 8) α) := fun _ h => nomatch h

theorem aci_eb_error {α : Type} (e : BitVec 8) (h : e.toNat < 12) :
    aci_EB (.error e : Except (BitVec 8) α) := fun _ h' => by cases h'; exact h

theorem aci_eb_throw {α : Type} (e : BitVec 8) (h : e.toNat < 12) :
    aci_EB (throw e : Except (BitVec 8) α) := fun _ h' => by cases h'; exact h

theorem aci_eb_bind {α β : Type} {x : Except (BitVec 8) α} {f : α → Except (BitVec 8) β} (hx : aci_EB x)
    (hf : ∀ a, aci_EB (f a)) : aci_EB (x >>= f) := fun e h => by
  cases x with
  | error e' => cases h; exact hx _ rfl
  | ok a => exact hf a e h

theorem aci_eb_ite {α : Type} {c : Prop} [Decidable c] {x y : Except (BitVec 8) α} (hx : aci_EB x) (hy : aci_EB y) :
    aci_EB (if c then x else y) := by
  by_cases h : c
  · rw [ite_eq_left h]; exact hx
  · rw [ite_eq_right h]; exact hy

set_option hygiene false in
/-- Peels binds, `if`s, and matches off an `Except` computation until every
leaf is `ok`, a throw of a literal below 12, or a computation already known.
Hygiene is off so that the lemmas named here can follow the macro. -/
macro "aci_eb" : tactic => `(tactic| repeat' (first
  | with_reducible exact aci_eb_ok _
  | with_reducible exact aci_eb_pure _
  | with_reducible exact aci_eb_throw _ (by decide)
  | with_reducible exact aci_eb_error _ (by decide)
  | with_reducible exact aci_eb_rdB _ _ _ _
  | with_reducible exact aci_eb_rdU8 _ _ _ _
  | with_reducible exact aci_eb_rdU16 _ _ _ _
  | with_reducible exact aci_eb_rdU32 _ _ _ _
  | with_reducible exact aci_eb_rdRes _ _ _ _ _
  | with_reducible exact aci_eb_rdMagic _ _ _ _ _
  | with_reducible exact aci_eb_rdVer1 _ _ _ _
  | with_reducible exact aci_eb_readSegW _ _ _ _
  | with_reducible exact aci_eb_checkSegW _ _ _
  | with_reducible exact aci_eb_readSegsW _ _ _ _ _ _ _
  | with_reducible exact aci_eb_physW _
  | with_reducible exact aci_eb_pairW _ _ _ _
  | with_reducible exact aci_eb_innerW _ _ _ _
  | with_reducible exact aci_eb_overlapW _
  | with_reducible exact aci_eb_entryW _ _
  | with_reducible exact aci_eb_hdrW _ _ _ _
  | with_reducible apply aci_eb_bind
  | with_reducible apply aci_eb_ite
  | split
  | intro _
  | dsimp only))

section Errors

variable (M : Word → BitVec 8) (ptr len : Word)

theorem aci_eb_rdB (n pos : Word) : aci_EB (rdB ptr len n pos) := by unfold rdB; aci_eb
theorem aci_eb_rdU8 (pos : Word) : aci_EB (rdU8 M ptr len pos) := by unfold rdU8; aci_eb
theorem aci_eb_rdU32 (pos : Word) : aci_EB (rdU32 M ptr len pos) := by unfold rdU32; aci_eb
theorem aci_eb_rdU16 (pos : Word) : aci_EB (rdU16 M ptr len pos) := by unfold rdU16; aci_eb
theorem aci_eb_rdRes (n pos : Word) : aci_EB (rdRes M ptr len n pos) := by unfold rdRes; aci_eb
theorem aci_eb_rdMagic (k pos : Word) : aci_EB (rdMagic M ptr len k pos) := by unfold rdMagic; aci_eb
theorem aci_eb_rdVer1 (pos : Word) : aci_EB (rdVer1 M ptr len pos) := by unfold rdVer1; aci_eb

theorem aci_eb_readSegW (pos : Word) : aci_EB (readSegW M ptr len pos) := by
  unfold readSegW segA segO segL; aci_eb

theorem aci_eb_checkSegW (ilen prev : Word) (s : SegW) : aci_EB (checkSegW ilen prev s) := by
  unfold checkSegW; aci_eb

theorem aci_eb_readSegsW (M : Word → BitVec 8) (ptr len ilen : Word) :
    ∀ n pos prev, aci_EB (readSegsW M ptr len ilen n pos prev)
  | 0, _, _ => aci_eb_ok _
  | n + 1, pos, prev => by
    unfold readSegsW
    aci_eb

theorem aci_eb_physW (s : SegW) : aci_EB (physW s) := by unfold physW; aci_eb

theorem aci_eb_pairW (a : SegW) (sa : BitVec 8) (xa : Word) (b : SegW) : aci_EB (pairW a sa xa b) := by
  unfold pairW pairChk; aci_eb

theorem aci_eb_innerW (a : SegW) (sa : BitVec 8) (xa : Word) : ∀ l, aci_EB (innerW a sa xa l)
  | [] => aci_eb_ok _
  | b :: bs => by
    unfold innerW
    aci_eb

theorem aci_eb_overlapW : ∀ l, aci_EB (overlapW l)
  | [] => aci_eb_ok _
  | a :: rest => by
    unfold overlapW
    aci_eb

theorem aci_eb_entryW (entry : Word) (segs : List SegW) : aci_EB (entryW entry segs) := by
  unfold entryW; aci_eb

theorem aci_eb_hdrW (ilen : Word) : aci_EB (hdrW M ptr len ilen) := by
  unfold hdrW hdrChip hdrSv hdrCnt hdrLen hdrLn; aci_eb

/-- **Every error `imgW` decides is below 12.** -/
theorem aci_imgW_err (ilen : Word) {e : BitVec 8} (h : imgW M ptr len ilen = .error e) : e.toNat < 12 := by
  refine (?_ : aci_EB (imgW M ptr len ilen)) e h
  unfold imgW; aci_eb

end Errors

theorem aci_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {v : β} (h : (x >>= f) = .ok v) :
    ∃ a, x = .ok a ∧ f a = .ok v := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem aci_readSegsW_ne {M : Word → BitVec 8} {ptr len ilen : Word} {n : Nat} {pos prev : Word}
    {segs : List SegW} {q : Word × Word} (hn : 1 ≤ n) (h : readSegsW M ptr len ilen n pos prev = .ok (segs, q)) :
    segs ≠ [] := by
  match n, hn with
  | k + 1, _ =>
    obtain ⟨⟨s, p1⟩, -, h1⟩ := aci_bind_ok h
    obtain ⟨p2, -, h2⟩ := aci_bind_ok h1
    obtain ⟨⟨rest, p3⟩, -, h3⟩ := aci_bind_ok h2
    cases h3
    exact List.cons_ne_nil _ _

theorem aci_readSegsW_len {M : Word → BitVec 8} {ptr len ilen : Word} :
    ∀ {n : Nat} {pos prev : Word} {segs : List SegW} {q : Word × Word},
      readSegsW M ptr len ilen n pos prev = .ok (segs, q) → segs.length = n
  | 0, _, _, _, _, h => by cases h; rfl
  | k + 1, _, _, _, _, h => by
    obtain ⟨⟨s, p1⟩, -, h1⟩ := aci_bind_ok h
    obtain ⟨p2, -, h2⟩ := aci_bind_ok h1
    obtain ⟨⟨rest, p3⟩, h3, h4⟩ := aci_bind_ok h2
    cases h4
    rw [List.length_cons, aci_readSegsW_len h3]

/-- **A successful parse has one to 16 segments, and every kind is at most 3.** -/
theorem aci_imgW_ok {M : Word → BitVec 8} {ptr len ilen : Word} {sv cnt : BitVec 8} {entry : Word}
    {segs : List SegW} (h : imgW M ptr len ilen = .ok (sv, entry, cnt, segs)) :
    segs ≠ [] ∧ segs.length ≤ 16 ∧ ∀ s ∈ segs, (3 : BitVec 8).ult s.kind = false := by
  unfold imgW at h
  obtain ⟨⟨sv', cnt', entry', pos⟩, hh, h1⟩ := aci_bind_ok h
  have hc := hdrW_cnt hh
  obtain ⟨⟨segs', pos', prev⟩, hr, h2⟩ := aci_bind_ok h1
  have hs : segs' = segs := by
    dsimp only at h2
    split at h2
    · obtain ⟨_, h3, -⟩ := aci_bind_ok h2
      cases h3
    · obtain ⟨_, -, h3⟩ := aci_bind_ok h2
      obtain ⟨_, -, h4⟩ := aci_bind_ok h3
      cases h4; rfl
  subst hs
  have S := segs_rel (M := M) (ptr := ptr) (len := len) ilen cnt'.toNat pos (cnt'.zeroExtend 32 <<< 4 + 0x14)
  rw [hr] at S
  exact ⟨aci_readSegsW_ne hc.1 hr, by rw [aci_readSegsW_len hr]; exact hc.2, S.2.2.2⟩

end C3
