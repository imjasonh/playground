import C3BootProofs.Proofs.TrustedRootReadChainModel
import C3BootProofs.Proofs.AcceptPinnedErr

/-!
# The error bytes of `read_chain`

`readChainPos` fails only with an `Error` or `TufError` byte below 0x27:
`Der::element`'s, `readTimeErr`, `bdiErr`, a JSON reader's, `valid_for`'s,
or one of the literals 1, 0x14, 0x20, and 0x21. The closure's rejection
table has entries only up to `Read` (0x26), so a caller that rejects with
`read_chain`'s byte needs `rce_readChainPos`.
-/

namespace C3.RV32

open C3.Json

/-- An error of the model that names its byte, and that byte is below
0x27. -/
abbrev RcErrOk (e : Option Nat) : Prop := ∃ b, e = some b ∧ b < 0x27

theorem rce_derErrByte (e : DerError) : (derErrByte e).toNat < 0x27 := by
  cases e <;> decide

theorem rce_readTimeErr (L : Bytes) : readTimeErr L < 0x27 := by
  unfold readTimeErr
  repeat' split
  all_goals first | decide | exact rce_derErrByte _

theorem rce_bdiErrAt (L : Nat) : ∀ (w : Nat) (T : Bytes), bdiErrAt L w T < 0x27
  | w, c0 :: c1 :: c2 :: c3 :: rest => by
    rw [bdiErrAt.eq_1]
    cases b64Group c0 c1 c2 c3 (bdiPad rest.isEmpty c2 c3) with
    | none => exact (by decide : (0x1C : Nat) < 0x27)
    | some g =>
      dsimp only [Option.elim]
      split
      · exact (by decide : (0x13 : Nat) < 0x27)
      · exact rce_bdiErrAt L _ rest
  | _, [] | _, [_] | _, [_, _] | _, [_, _, _] => by first | (unfold bdiErrAt; decide) | simp [bdiErrAt]

theorem rce_bdiErr (T : Bytes) (L : Nat) : bdiErr T L < 0x27 := by
  unfold bdiErr
  split
  · exact rce_bdiErrAt _ _ _
  · decide

theorem rce_tvfTime (v : Bytes) : ∀ e, tvfTime v = .error e → e < 0x27 := by
  intro e h
  unfold tvfTime at h
  repeat' (first | (cases h; done) | split at h)
  all_goals (cases h; decide)

theorem rce_validFor (d : Bytes) : ∀ e, validForPos d = .error e → e < 0x27 := by
  intro e h
  unfold validForPos tvfRest at h
  repeat' (first | (cases h; done) | split at h)
  all_goals (cases h; first
    | exact Ac.acp_objField _ _ _ (by assumption)
    | exact Ac.acp_objGet _ _ _ (by assumption)
    | exact rce_tvfTime _ _ (by assumption))

set_option hygiene false in
/-- Closes `RcErrOk e` from a literal, a byte function's bound, or a
callee's error. -/
macro "rce_close" : tactic => `(tactic| first
  | exact ⟨_, rfl, by decide⟩
  | exact ⟨_, rfl, rce_derErrByte _⟩
  | exact ⟨_, rfl, rce_readTimeErr _⟩
  | exact ⟨_, rfl, rce_bdiErr _ _⟩
  | exact ⟨_, rfl, Ac.acp_objField _ _ _ (by assumption)⟩
  | exact ⟨_, rfl, rce_validFor _ _ (by assumption)⟩
  | (apply rce_elem; assumption)
  | (apply rce_subj; assumption)
  | (apply rce_times; assumption)
  | (apply rce_serial; assumption)
  | (apply rce_tbs; assumption)
  | (apply rce_body; assumption)
  | (apply rce_parse; assumption)
  | (apply rce_step; assumption)
  | (apply rce_loop; assumption)
  | (apply rce_finish; assumption)
  | (apply rce_chain; assumption))

set_option hygiene false in
/-- Splits `h : f … = .error e` and closes each case with `rce_close`. -/
macro "rce_go" : tactic => `(tactic| (
  repeat' (first | (cases h; done) | split at h)
  all_goals first | rce_close | (cases h; rce_close)))

theorem rce_elem {L : Bytes} {tag : Nat} {r : RcRd} {e : Option Nat} (h : rcElem L tag r = .error e) :
    RcErrOk e := by
  unfold rcElem at h; rce_go

theorem rce_subj {L : Bytes} {p : Word} {sr ir : RcRd} {nb na : Nat} {t : RcRd} {e : Option Nat}
    (h : rcSubj L p sr ir nb na t = .error e) : RcErrOk e := by
  unfold rcSubj at h; rce_go

theorem rce_times {L : Bytes} {p : Word} {sr ir v t : RcRd} {e : Option Nat}
    (h : rcTimes L p sr ir v t = .error e) : RcErrOk e := by
  unfold rcTimes at h; rce_go

theorem rce_serial {L : Bytes} {p : Word} {t : RcRd} {e : Option Nat} (h : rcSerial L p t = .error e) :
    RcErrOk e := by
  unfold rcSerial at h; rce_go

theorem rce_tbs {L : Bytes} {p : Word} {t : RcRd} {e : Option Nat} (h : rcTbs L p t = .error e) :
    RcErrOk e := by
  unfold rcTbs at h; rce_go

theorem rce_body {L : Bytes} {p : Word} {c : RcRd} {e : Option Nat} (h : rcBody L p c = .error e) :
    RcErrOk e := by
  unfold rcBody at h; rce_go

theorem rce_parse {L : Bytes} {p : Word} {e : Option Nat} (h : rcParse L p = .error e) : RcErrOk e := by
  unfold rcParse at h; rce_go

theorem rce_step {M0 : Word → BitVec 8} {fp : Word} {fl : Nat} {q : Word} {l after : Nat} {s : RcSt}
    {e : Option Nat} (h : rcStep M0 fp fl q l after s = .error e) : RcErrOk e := by
  unfold rcStep at h; rce_go

theorem rce_loop {M0 : Word → BitVec 8} {fp : Word} {fl : Nat} {ap : Word} {an : Nat} :
    ∀ {k : Nat} {s : RcSt} {e : Option Nat}, rcLoop M0 fp fl ap an k s = .error e → RcErrOk e
  | 0, s, e, h => by simp [rcLoop] at h
  | k + 1, s, e, h => by
    rw [rcLoop] at h
    repeat' (first | (cases h; done) | split at h)
    all_goals first
      | (cases h; first | exact ⟨_, rfl, by decide⟩ | (apply rce_step; assumption))
      | exact rce_loop h

theorem rce_finish {M0 : Word → BitVec 8} {ap : Word} {an : Nat} {s : RcSt} {e : Option Nat}
    (h : rcFinish M0 ap an s = .error e) : RcErrOk e := by
  unfold rcFinish at h; rce_go

theorem rce_chain {M0 : Word → BitVec 8} {fp : Word} {fl : Nat} {ap : Word} {an nb na : Nat}
    {e : Option Nat} (h : rcChain M0 fp fl ap an nb na = .error e) : RcErrOk e := by
  unfold rcChain at h; rce_go

/-- `read_chain` fails only with a byte below 0x27. -/
theorem rce_readChainPos {M0 : Word → BitVec 8} {p : Word} {n : Nat} {fp : Word} {fl : Nat} {e : Option Nat}
    (h : readChainPos M0 p n fp fl = .error e) : RcErrOk e := by
  unfold readChainPos at h; rce_go

end C3.RV32
