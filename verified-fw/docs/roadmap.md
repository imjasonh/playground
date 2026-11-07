# Roadmap

Version 0 proves straight-line code, `if`, and bounded loops end to end, with
no interrupts. Each step in this list keeps the same rule: the trusted files
stay small, and every new feature arrives with its proof.

## 1. Run on hardware

- Flash `esp32c3-blinky.bin` on an ESP32-C3 and confirm the watchdog and
  GPIO register values in `Examples/Blinky.lean`.
- Add a differential test that runs random instruction sequences on the
  model, in Spike, and on the chip, and compares registers and memory.

## 2. Close the emitter gap

`lake exe emit` runs compiled Lean code, so the Lean compiler sits between the
proofs and the image file. To remove it, generate a Lean file that states
`Image.esp32c3 blinky = [ ... bytes ... ]`, prove it with `decide` so the
kernel computes the bytes, and have the emitter write that literal list. CI
regenerates the file and fails on any difference.

## 3. Device reads and time

- Loads from device registers return values the program doesn't control.
  Model them as inputs: the trace records each read with its value, and a
  spec says which input sequences are possible.
- Model the ESP32-C3 system timer, so a delay is "until the timer passes T"
  instead of a loop count.

## 4. Interrupts

This step has the most new work:

- Extend the machine model with `mstatus.MIE`, `mtvec`, `mepc`, `mcause`, the
  `csrrw`, `csrrs`, and `mret` instructions, and a trap step that can happen
  between any two instructions while interrupts are enabled. Then model the
  ESP32-C3 interrupt matrix and its priority threshold register.
- Add handlers to the language. Each handler has a fixed priority and runs to
  completion. Shared globals are reachable only inside
  `lock v { ... }`, which raises the interrupt threshold to the highest
  priority of any handler that uses `v`. This is the Stack Resource Policy
  that RTIC uses.
- Prove the theorem that makes per-program proofs easy: every interleaving
  that preemption allows is equivalent to one where each handler and each
  locked block runs atomically. After that, a program's proof only reasons
  about atomic state changes.
- Prove the trap entry and exit code that the compiler emits, and a maximum
  stack depth.

## 5. A Rust front end

Accept a strict subset of `no_std` Rust as the source syntax:

- Use Charon, the front end of the Aeneas project, to export the crate's MIR
  as LLBC, and import that into a Lean term of this language.
- The image still comes from the Lean term, never from `rustc`, so an
  importer bug can't put unproven code on the chip.
- The same source also builds with `rustc` against RTIC for host tests and
  quick experiments, and CI compares those runs with the verified build.

## 6. Trust less

- Generate `RiscV/Machine.lean` and `RiscV/Decode.lean` from the official
  Sail RISC-V model, or prove them equivalent to it.
- Bound the cycle count of each handler. Code that runs from internal RAM
  has predictable timing; code that runs from flash through the cache doesn't.
- Add the ESP32-C6's low-power core as a second, independent hart.
