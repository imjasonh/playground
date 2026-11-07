/-
What `counter` does on QEMU. The statement of `counter_on_qemu` is the spec:
review it, not the proofs.
-/
import VerifiedFw.EndToEnd
import VerifiedFw.Examples.Counter

namespace VerifiedFw.Examples

open VerifiedFw.RiscV VerifiedFw.Lang VerifiedFw.Compiler VerifiedFw.Targets.QemuVirt

theorem counter_wf : counter.wf Targets.qemuVirt = true := by decide

theorem counter_uart : uartText counter.trace = "verified-fw: 01*23*45*67*89*\n" := by decide

theorem counter_last : counter.trace.getLast? = some ⟨finisher, finishPass⟩ := by decide

/-- Booted from `Image.qemuVirt counter`, QEMU's UART prints
`verified-fw: 01*23*45*67*89*` and a newline, the last device store tells QEMU
to exit with status 0, and nothing happens after that. -/
theorem counter_on_qemu (m : Machine)
    (himem : m.imem = Loader.imemOf 0x80000000 (Image.qemuVirt counter))
    (hpc : m.pc = 0x80000000) (htr : m.trace = []) :
    ∃ m', Star Targets.qemuVirt.platform m m' ∧
      uartText m'.trace = "verified-fw: 01*23*45*67*89*\n" ∧
      m'.trace.getLast? = some ⟨finisher, finishPass⟩ ∧
      step Targets.qemuVirt.platform m' = some m' := by
  obtain ⟨m', hs, htr', hfix⟩ := qemuVirt_correct counter counter_wf m himem hpc htr
  exact ⟨m', hs, htr' ▸ counter_uart, htr' ▸ counter_last, hfix⟩

end VerifiedFw.Examples
