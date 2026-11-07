/-
What `blinky` does on an ESP32-C3. `blinkyEvents` and the statement of
`blinky_on_esp32c3` are the spec: review those, not the proofs.
-/
import VerifiedFw.EndToEnd
import VerifiedFw.Examples.Blinky

namespace VerifiedFw.Examples.Blinky

open VerifiedFw.RiscV VerifiedFw.Lang VerifiedFw.Compiler

/-- Every device store, in order: unlock and disable the three watchdogs,
route GPIO8 to the output register, then turn the LED on and off `blinks`
times. Noncomputable so no executable builds the list, which has about 8.6
billion entries. -/
noncomputable def blinkyEvents : List Event :=
  [⟨0x600080A8, wdtKey⟩, ⟨0x60008090, 0⟩, ⟨0x600080A8, 0⟩,
   ⟨0x600080B0, 0x8F1D312A⟩, ⟨0x600080AC, 0x80000000⟩, ⟨0x600080B0, 0⟩,
   ⟨0x6001F064, wdtKey⟩, ⟨0x6001F048, 0x00400000⟩, ⟨0x6001F064, 0⟩,
   ⟨0x60020064, wdtKey⟩, ⟨0x60020048, 0x00400000⟩, ⟨0x60020064, 0⟩,
   ⟨0x60009024, 0x1800⟩, ⟨0x60004574, 0x80⟩, ⟨0x60004024, ledBit⟩] ++
  (List.replicate blinks [⟨0x6000400C, ledBit⟩, ⟨0x60004008, ledBit⟩]).flatten

theorem blinky_wf : blinky.wf Targets.esp32c3 = true := by decide

theorem repeat_id (n : Nat) (s : State) : Nat.repeat (fun x => x) n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.repeat, ih]

theorem repeat_appends (f : State → State) (l : List Event)
    (hf : ∀ s, f s = { s with trace := s.trace ++ l }) (n : Nat) (s : State) :
    Nat.repeat f n s = { s with trace := s.trace ++ (List.replicate n l).flatten } := by
  induction n with
  | zero => simp [Nat.repeat]
  | succ n ih =>
    simp only [Nat.repeat, ih, hf, List.replicate_succ', List.flatten_append,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

/-- The delay loop changes nothing. The count is generalized first so the
kernel never unfolds `Nat.repeat` two million times. -/
theorem delay_run (s : State) : delay.run s = s := by
  unfold delay
  generalize (2000000 : Nat) = n
  simp only [Stmt.run, repeat_id]

/-- Rewrites only, so the kernel never unfolds the two-million-iteration delay. -/
theorem blink_run (s : State) : blink.run s =
    { s with trace := s.trace ++ [⟨0x6000400C, ledBit⟩, ⟨0x60004008, ledBit⟩] } := by
  show (Stmt.seq ledOn (.seq delay (.seq ledOff delay))).run s = _
  rw [Stmt.run, Stmt.run, Stmt.run, delay_run, delay_run]
  simp only [ledOn, ledOff, set, Stmt.run, Expr.eval, List.append_assoc, List.cons_append,
    List.nil_append]

theorem blinky_body : blinky.body = .seq disableWatchdogs (.seq setupLed (.loop blinks blink)) :=
  rfl

/-- Rewrites only, so the kernel never unfolds the `blinks`-iteration loop. -/
theorem blinky_trace : blinky.trace = blinkyEvents := by
  rw [Program.trace, blinky_body, Stmt.run, Stmt.run, Stmt.run, repeat_appends _ _ blink_run]
  simp only [disableWatchdogs, setupLed, seqs, set, Stmt.run, Expr.eval, State.init,
    blinkyEvents, List.nil_append, List.cons_append]

/-- Flashed as `Image.esp32c3 blinky` and booted, the chip makes exactly the
device stores in `blinkyEvents`, then does nothing more. -/
theorem blinky_on_esp32c3 (m : Machine)
    (himem : m.imem = Loader.imemOf 0x42000000 (Image.esp32c3 blinky))
    (hpc : m.pc = 0x42000008) (htr : m.trace = []) :
    ∃ m', Star Targets.esp32c3.platform m m' ∧ m'.trace = blinkyEvents ∧
      step Targets.esp32c3.platform m' = some m' := by
  obtain ⟨m', hs, htr', hfix⟩ := esp32c3_correct blinky blinky_wf m himem hpc htr
  exact ⟨m', hs, htr'.trans blinky_trace, hfix⟩

end VerifiedFw.Examples.Blinky
