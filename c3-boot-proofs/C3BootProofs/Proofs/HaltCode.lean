import C3BootProofs.Proofs.Panic

/-!
# Halt codes

`halt` passes its code to the ROM's `printf` in `a1`. `HaltCode m c` says
that `m` is at that call with code `c`, and `HaltsWith m c` that the
machine gets there from `m`. The deliberate `halt` calls in `boot_main`
and `boot` pass 0xE1 to 0xE5 (`Deliberate`); `rust_begin_unwind` passes
`panicHaltCode`, 0xEF. `PanicFree.lean` uses these to say how the
bootloader stops.
-/

namespace C3.RV32

open C3.Image

/-- The machine is entering the ROM's `printf` from `halt` with `halt`'s
code `c`, which `halt` moved to `a1`. -/
def HaltCode (m : Machine) (c : Word) : Prop := Halting m ∧ reg m a1 = c

/-- The codes of the deliberate `halt` calls: 0xE1 to 0xE5. -/
def deliberateCodes : List Word := [0xE1, 0xE2, 0xE3, 0xE4, 0xE5]

/-- `c` is the code of a deliberate `halt` call. -/
def Deliberate (c : Word) : Prop := c ∈ deliberateCodes

/-- The code that `rust_begin_unwind` passes to `halt`. -/
def panicHaltCode : Word := 0xEF

theorem panicHaltCode_not_deliberate : ¬ Deliberate panicHaltCode :=
  show panicHaltCode ∉ deliberateCodes by decide

/-- From `m`, the machine reaches `halt`'s ROM call with code `c`. -/
def HaltsWith (m : Machine) (c : Word) : Prop := ∃ m', Steps m m' ∧ HaltCode m' c

/-- From `m`, the machine reaches `halt`'s ROM call with a deliberate code. -/
def HaltsDeliberately (m : Machine) : Prop := ∃ c, Deliberate c ∧ HaltsWith m c

theorem HaltsWith.panics {m : Machine} {c : Word} (h : HaltsWith m c) : Panics m :=
  let ⟨m', s, hh, _⟩ := h; ⟨m', s, hh⟩

theorem HaltsWith.of_steps {m m' : Machine} {c : Word} (s : Steps m m') (h : HaltsWith m' c) : HaltsWith m c :=
  let ⟨m'', s', hh⟩ := h; ⟨m'', s.trans s', hh⟩

theorem HaltsDeliberately.panics {m : Machine} (h : HaltsDeliberately m) : Panics m :=
  let ⟨_, _, hw⟩ := h; hw.panics

theorem HaltsDeliberately.of_steps {m m' : Machine} (s : Steps m m') (h : HaltsDeliberately m') :
    HaltsDeliberately m :=
  let ⟨c, hc, hw⟩ := h; ⟨c, hc, hw.of_steps s⟩

theorem HaltsDeliberately.of_e1 {m : Machine} (h : HaltsWith m 0xE1) : HaltsDeliberately m :=
  ⟨0xE1, show (0xE1 : Word) ∈ deliberateCodes by decide, h⟩

theorem HaltsDeliberately.of_e2 {m : Machine} (h : HaltsWith m 0xE2) : HaltsDeliberately m :=
  ⟨0xE2, show (0xE2 : Word) ∈ deliberateCodes by decide, h⟩

theorem HaltsDeliberately.of_e4 {m : Machine} (h : HaltsWith m 0xE4) : HaltsDeliberately m :=
  ⟨0xE4, show (0xE4 : Word) ∈ deliberateCodes by decide, h⟩

theorem HaltsDeliberately.of_e5 {m : Machine} (h : HaltsWith m 0xE5) : HaltsDeliberately m :=
  ⟨0xE5, show (0xE5 : Word) ∈ deliberateCodes by decide, h⟩

set_option maxRecDepth 20000 in
/-- **`halt`** with its code `reg m a0` reaches the ROM's `printf` with that
code in `a1`. -/
theorem halt_haltCode (m : Machine) (hP : PanicCode m.mem) (hpc : m.pc = haltBase)
    (hR : Room (reg m sp) 16) : HaltsWith m (reg m a0) := by
  have hc := haltCode_in hP
  have st0 : St m.mem haltBase m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, reg m sp = S := ⟨_, rfl⟩
  rw [hS] at hR
  obtain ⟨mA, cA, uA⟩ := St.block hltA st0 hc hltA_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, hltA, upd_app, ↓reduceIte, and_true]
    simp only [ev_add]; rw [hS]
    repeat' apply And.intro
    all_goals first | exact True.intro | (refine aligned_add (aligned_add hR.1 ?_) ?_ <;> decide) |
      exact hR.sep (o := 0xC) (by decide) (by decide) (by decide) (by decide))
  simp only [runBlock, BInstr.run, hltA] at uA
  have hPA : PanicCode mA.mem := by
    rw [uA.mem]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add]; rw [hS]
    exact hP.store32 (hR.slot (o := 0xC) (by decide) (by decide))
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := uA.self.callRa (by rw [← uA.mem]; exact haltCode_in hPA) hlt_at_e hlt_at_12
    (cb := romPrintfEntry) (by decide) (by decide)
  refine ⟨n1, cA.trans c1, ⟨pc1, ?_, by rw [mem1, ← uA.mem]; exact hPA⟩, ?_⟩
  · rw [regs1]; simp +decide only [upd_app, ↓reduceIte]
  · rw [regs1, upd_ne (by decide) (by decide), uA.regs]; simp +decide only [upd_app, ↓reduceIte]
    simp only [aluEval]; exact BitVec.zero_add _

/-- **`rust_begin_unwind`** reaches the ROM's `printf` from `halt` with code
0xEF. -/
theorem beginUnwind_haltCode (m : Machine) (hP : PanicCode m.mem) (hpc : m.pc = BitVec.ofNat 32 beginUnwindAddress)
    (hR : Room (reg m sp) 16) : HaltsWith m panicHaltCode := by
  have hc := unwindCode_in hP
  have st0 : St m.mem (BitVec.ofNat 32 beginUnwindAddress) m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  obtain ⟨m1, e1, s1⟩ := st0.aluImm hc unw_at_0 (off' := 4) (by decide)
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s1.self.callRa hc unw_at_4 unw_at_8 (cb := haltBase) (by decide)
    (by decide)
  have h := halt_haltCode n1 (by rw [mem1]; exact hP) pc1 (by
    rw [regs1, upd_ne (by decide) (by decide), s1.regs]
    simp +decide only [upd_app, ↓reduceIte]; exact hR)
  have e : reg n1 a0 = panicHaltCode := by
    rw [regs1, upd_ne (by decide) (by decide), s1.regs]
    simp +decide only [upd_app, ↓reduceIte]; rfl
  rw [e] at h
  exact h.of_steps (.cons e1 c1)

end C3.RV32
