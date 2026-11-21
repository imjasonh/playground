import C3BootProofs

/-!
Prints the specification's answers for every input in a fixed grid, in the
format of `c3-boot/verify/examples/spec_vectors.rs`, so that CI can compare
the two line by line.
-/

open C3

def showSlot : Slot → String
  | .a => "A"
  | .b => "B"

def showOpt : Option Nat → String
  | some n => toString n
  | none => "-"

def showTrial : Option Trial → String
  | some t => showSlot t.slot ++ toString t.bootsLeft
  | none => "-"

def showState (s : State) : String :=
  s!"g={s.generation} p={showSlot s.preferred} t={showTrial s.trial} c={s.confirmed}"

def showWrite : Option State → String
  | some s => showState s
  | none => "-"

def showOutcome : Outcome → String
  | .boot s t => s!"boot {showSlot s} {t}"
  | .halt => "halt"

def showBool (b : Bool) : String := if b then "1" else "0"

def levels : List Nat := List.range (maxLevel + 1)

def main : IO Unit := do
  let out ← IO.getStdout
  for v in List.range (2 ^ 16) do
    let f := Fuses.ofNat v
    let mask := match firstClear f with
      | some i => toString (2 ^ i)
      | none => "-"
    out.putStrLn s!"level {v} {level f} {mask}"
  for c in levels do
    for b in levels do
      for s in levels do
        for e in levels do
          out.putStrLn s!"check {c} {b} {s} {e} {showBool (checkSlot c b s e)}"
  for l in levels do
    for c in [false, true] do
      for e in levels do
        out.putStrLn s!"target {l} {showBool c} {e} {burnTarget l c e}"
  let trials : List (Option Trial) :=
    none :: ([Slot.a, Slot.b].flatMap fun s => (List.range 4).map fun n => some ⟨s, n⟩)
  let slotLevels : List (Option Nat) := [none, some 0, some 1, some 5, some 16]
  for g in [0, 7, maxGeneration] do
    for p in [Slot.a, Slot.b] do
      for t in trials do
        for c in List.range 4 do
          let st : State := ⟨g, p, t, c⟩
          for e in [0, 1, 5, 16] do
            for la in slotLevels do
              for lb in slotLevels do
                let slots : Slot → Option Nat := fun
                  | .a => la
                  | .b => lb
                let d := decideBoot st e (accepted slots e)
                out.putStrLn
                  s!"decide {showState st} e={e} a={showOpt la} b={showOpt lb} | {showWrite d.write} | {showOutcome d.outcome}"
