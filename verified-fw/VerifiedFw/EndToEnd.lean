/-
End-to-end theorems: from the bytes the emitter writes to the device stores
the chip sees.
-/
import VerifiedFw.Compiler.Correct
import VerifiedFw.Compiler.Image

namespace VerifiedFw

open VerifiedFw.RiscV VerifiedFw.Lang VerifiedFw.Compiler

/-- QEMU `virt`: load `Image.qemuVirt prog` at `0x80000000` and start there.
The run makes exactly `prog.trace`'s device stores, then stays put. -/
theorem qemuVirt_correct (prog : Program) (hwf : prog.wf Targets.qemuVirt = true)
    (m : Machine) (himem : m.imem = Loader.imemOf 0x80000000 (Image.qemuVirt prog))
    (hpc : m.pc = 0x80000000) (htr : m.trace = []) :
    ∃ m', Star Targets.qemuVirt.platform m m' ∧ m'.trace = prog.trace ∧
      step Targets.qemuVirt.platform m' = some m' := by
  apply compile_correct _ prog hwf m _ hpc htr
  have hlen : (compile Targets.qemuVirt prog).length < 2 ^ 17 := by
    simp only [Program.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf; exact hwf.1.1.1.2
  have := codeAt_image 0x80000000 [] (compile Targets.qemuVirt prog) (by simp; omega)
  rw [himem]
  simpa [Image.qemuVirt, Targets.qemuVirt] using this

/-- ESP32-C3 direct boot: flash `Image.esp32c3 prog` at offset 0, which the ROM
maps at `0x42000000`, and start at `0x42000008`. The run makes exactly
`prog.trace`'s device stores, then stays put. -/
theorem esp32c3_correct (prog : Program) (hwf : prog.wf Targets.esp32c3 = true)
    (m : Machine) (himem : m.imem = Loader.imemOf 0x42000000 (Image.esp32c3 prog))
    (hpc : m.pc = 0x42000008) (htr : m.trace = []) :
    ∃ m', Star Targets.esp32c3.platform m m' ∧ m'.trace = prog.trace ∧
      step Targets.esp32c3.platform m' = some m' := by
  apply compile_correct _ prog hwf m _ hpc htr
  have hlen : (compile Targets.esp32c3 prog).length < 2 ^ 17 := by
    simp only [Program.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf; exact hwf.1.1.1.2
  have := codeAt_image 0x42000000 (Image.wordBytes 0xAEDB041D ++ Image.wordBytes 0xAEDB041D)
    (compile Targets.esp32c3 prog) (by simp; omega)
  rw [himem]
  simpa [Image.esp32c3, Targets.esp32c3] using this

end VerifiedFw
