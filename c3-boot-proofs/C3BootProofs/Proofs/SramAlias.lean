import C3BootProofs.Proof.Code

/-!
# The SRAM's two views

`Machine` gives each address its own byte. On the ESP32-C3, the 384 KiB
of internal SRAM that the bootloader uses appears twice: at 0x3FC80000 to
0x3FCE0000 on the data bus, and at 0x40380000 to 0x403E0000 on the
instruction bus, so the instruction-bus address `x` and the data-bus
address `x - 0x700000` are the same byte. A store through one view changes
what a read through the other returns, which `Machine` doesn't model.

`Chip` is the same machine with that aliasing: its memory is indexed by
`sramCanon`, which sends an instruction-bus SRAM address to its data-bus
alias. `chip_steps` proves that a `Chip` runs the same instructions as a
`Machine` and ends with the same registers, program counter, and bytes at
every `Coherent` address, as long as the `Machine` run meets the
**SRAM alias obligation** `AliasOk`:

* every byte that an instruction fetches or loads is `Coherent`: outside
  the instruction bus's view of SRAM, or in the bootloader's IRAM at
  0x403A0000 to 0x403C4000; and
* every byte that a store writes is `StoreOk`: outside the instruction
  bus's view of SRAM, and outside 0x3FCA0000 to 0x3FCC4000, the data-bus
  view of the bootloader's IRAM.

The model's memory at reset is the chip's, read through `sramCanon`
(`chipSim_init`), so both views of each SRAM byte start equal.
`aliasOk_regions` proves from the memory map that the regions the
bootloader's proofs show it writes, its stack and data, the application RAM
region, flash and the ROM, and the peripheral registers, are `StoreOk`, and
that the image's code and read-only data are `Coherent`. That each step of
the run from reset stores and reads only there is the obligation; the
proofs bound what a run changes, not each step's addresses.
-/

namespace C3.RV32

/-- The instruction bus's view of the SRAM that the data bus sees at
0x3FC80000 to 0x3FCE0000. -/
def IBusSram (a : Nat) : Prop := 0x40380000 ≤ a ∧ a < 0x403E0000

instance (a : Nat) : Decidable (IBusSram a) := inferInstanceAs (Decidable (_ ∧ _))

/-- The address that the chip stores the byte at `a` under: the data-bus
alias of an instruction-bus SRAM address, and `a` otherwise. -/
def sramCanon (a : Word) : Word := if IBusSram a.toNat then a - 0x700000 else a

/-- An address where the model's byte is the chip's: outside the
instruction bus's view of SRAM, or in the bootloader's IRAM, whose data-bus
alias no store reaches. -/
def Coherent (a : Word) : Prop :=
  ¬ IBusSram a.toNat ∨ (0x403A0000 ≤ a.toNat ∧ a.toNat < 0x403C4000)

/-- An address that a store may write: through the data bus or outside
SRAM, and not the data-bus alias of the bootloader's IRAM. -/
def StoreOk (a : Word) : Prop :=
  ¬ IBusSram a.toNat ∧ ¬ (0x3FCA0000 ≤ a.toNat ∧ a.toNat < 0x3FCC4000)

/-- The ESP32-C3 as `RV32` sees it, with the SRAM's two views as one byte. -/
structure Chip where
  regs : Fin 32 → Word
  pc : Word
  mem : Word → BitVec 8

instance : Arch Chip where
  getReg c r := c.regs r
  setReg c r v := { c with regs := fun i => if i = r then v else c.regs i }
  getPc c := c.pc
  setPc c v := { c with pc := v }
  read8 c a := c.mem (sramCanon a)
  write8 c a v := { c with mem := fun x => if x = sramCanon a then v else c.mem x }

/-- The chip `c` and the model `m` agree: the same registers and program
counter, and the same byte at every `Coherent` address. -/
def ChipSim (c : Chip) (m : Machine) : Prop :=
  c.regs = m.regs ∧ c.pc = m.pc ∧ ∀ a, Coherent a → c.mem (sramCanon a) = m.mem a

/-- `P` holds of the `n` bytes from `a`, for the access sizes 1, 2, and 4. -/
def AllBytes (P : Word → Prop) (a : Word) : Nat → Prop
  | 1 => P a
  | 2 => P a ∧ P (a + 1)
  | 4 => P a ∧ P (a + 1) ∧ P (a + 2) ∧ P (a + 3)
  | _ => True

/-- What the instruction `i` at `m` reads and writes is allowed. -/
def ExecOk (m : Machine) : Instr → Prop
  | .load op _ rs1 off => AllBytes Coherent (reg m rs1 + off) (loadSize op)
  | .store op rs1 _ off => AllBytes StoreOk (reg m rs1 + off) (storeSize op)
  | _ => True

/-- The SRAM alias obligation for one step from `m`: the four bytes at the
program counter are `Coherent`, and so are the decoded instruction's loads,
and its stores are `StoreOk`. -/
def StepOk (m : Machine) : Prop :=
  AllBytes Coherent m.pc 4 ∧ ∀ i len, fetch m = some (i, len) → ExecOk m i

/-- **The SRAM alias obligation** for a run from `m` to `m'`: every step
meets `StepOk`. -/
def AliasOk (m m' : Machine) : Prop :=
  ∀ m₁ m₂, Steps m m₁ → RV32.step m₁ = some m₂ → Steps m₂ m' → StepOk m₁

section Sim

variable {c : Chip} {m : Machine}

theorem chip_reg (h : ChipSim c m) (r : Fin 32) : reg c r = reg m r := by
  show (if r.val = 0 then 0 else c.regs r) = (if r.val = 0 then 0 else m.regs r)
  rw [h.1]

theorem chip_load8 (h : ChipSim c m) {a : Word} (ha : Coherent a) : load8 c a = load8 m a := h.2.2 a ha

theorem chip_load16 (h : ChipSim c m) {a : Word} (ha : AllBytes Coherent a 2) : load16 c a = load16 m a := by
  unfold load16; rw [chip_load8 h ha.1, chip_load8 h ha.2]

theorem chip_load32 (h : ChipSim c m) {a : Word} (ha : AllBytes Coherent a 4) : load32 c a = load32 m a := by
  unfold load32; rw [chip_load8 h ha.1, chip_load8 h ha.2.1, chip_load8 h ha.2.2.1, chip_load8 h ha.2.2.2]

theorem chip_writeReg (h : ChipSim c m) (rd : Fin 32) (v : Word) : ChipSim (writeReg c rd v) (writeReg m rd v) := by
  unfold writeReg
  split
  · exact h
  · refine ⟨?_, h.2.1, h.2.2⟩
    show (fun i => if i = rd then v else c.regs i) = (fun i => if i = rd then v else m.regs i)
    rw [h.1]

theorem chip_setPc (h : ChipSim c m) (v : Word) : ChipSim (Arch.setPc c v) (Arch.setPc m v) :=
  ⟨h.1, rfl, h.2.2⟩

theorem canon_of_not (a : Word) (h : ¬ IBusSram a.toNat) : sramCanon a = a := by
  unfold sramCanon; rw [ite_eq_right h]

theorem chip_store8 (h : ChipSim c m) {a : Word} (ha : StoreOk a) (v : BitVec 8) :
    ChipSim (store8 c a v) (store8 m a v) := by
  refine ⟨h.1, h.2.1, fun g hg => ?_⟩
  show (if sramCanon g = sramCanon a then v else c.mem (sramCanon g)) = (if g = a then v else m.mem g)
  rw [canon_of_not a ha.1]
  rcases hg with hg | hg
  · have hm := h.2.2 g (.inl hg)
    rw [canon_of_not g hg] at hm ⊢
    split
    · rfl
    · exact hm
  · have hc : sramCanon g = g - 0x700000 := by
      unfold sramCanon; rw [ite_eq_left ⟨by omega, by omega⟩]
    have hgc : (g - 0x700000 : Word).toNat = g.toNat - 0x700000 := by
      rw [BitVec.toNat_sub, show (0x700000 : Word).toNat = 0x700000 from rfl]; omega
    have h1 : sramCanon g ≠ a := fun e => ha.2 (by rw [← e, hc, hgc]; exact ⟨by omega, by omega⟩)
    have h2 : g ≠ a := fun e => ha.1 (by rw [← e]; exact ⟨by omega, by omega⟩)
    rw [ite_eq_right h1, ite_eq_right h2]
    exact h.2.2 g (.inr hg)

theorem chip_store16 (h : ChipSim c m) {a : Word} (ha : AllBytes StoreOk a 2) (v : BitVec 16) :
    ChipSim (store16 c a v) (store16 m a v) :=
  chip_store8 (chip_store8 h ha.1 _) ha.2 _

theorem chip_store32 (h : ChipSim c m) {a : Word} (ha : AllBytes StoreOk a 4) (v : Word) :
    ChipSim (store32 c a v) (store32 m a v) :=
  chip_store8 (chip_store8 (chip_store8 (chip_store8 h ha.1 _) ha.2.1 _) ha.2.2.1 _) ha.2.2.2 _

theorem chip_fetch (h : ChipSim c m) (hf : AllBytes Coherent m.pc 4) : fetch c = fetch m := by
  have hp : Arch.getPc c = Arch.getPc m := h.2.1
  have h16 : load16 c (Arch.getPc m) = load16 m (Arch.getPc m) := chip_load16 h ⟨hf.1, hf.2.1⟩
  have h32 : load32 c (Arch.getPc m) = load32 m (Arch.getPc m) := chip_load32 h hf
  unfold fetch
  simp only [hp, h16, h32]

theorem chip_exec (h : ChipSim c m) {i : Instr} {len : Word} (ok : ExecOk m i) {m' : Machine}
    (e : exec m i len = some m') : ∃ c', exec c i len = some c' ∧ ChipSim c' m' := by
  have hp : Arch.getPc c = Arch.getPc m := h.2.1
  have hr := chip_reg h
  cases i with
  | lui rd imm =>
    exact ⟨_, rfl, by cases e; rw [hp]; exact chip_setPc (chip_writeReg h _ _) _⟩
  | auipc rd imm =>
    exact ⟨_, rfl, by cases e; rw [hp]; exact chip_setPc (chip_writeReg h _ _) _⟩
  | jal rd off =>
    dsimp only [exec] at e ⊢
    rw [hp]
    revert e
    split
    · intro e; cases e
    · intro e; cases e; exact ⟨_, rfl, chip_setPc (chip_writeReg h _ _) _⟩
  | jalr rd rs1 off =>
    exact ⟨_, rfl, by cases e; rw [hp, hr]; exact chip_setPc (chip_writeReg h _ _) _⟩
  | branch op rs1 rs2 off =>
    exact ⟨_, rfl, by cases e; rw [hp, hr, hr]; exact chip_setPc h _⟩
  | load op rd rs1 off =>
    dsimp only [exec] at e ⊢
    rw [hp, hr]
    revert e
    split
    · intro e; cases e
    · intro e
      cases e
      refine ⟨_, rfl, ?_⟩
      cases op
      · rw [chip_load8 h ok]; exact chip_setPc (chip_writeReg h _ _) _
      · rw [chip_load16 h ok]; exact chip_setPc (chip_writeReg h _ _) _
      · rw [chip_load32 h ok]; exact chip_setPc (chip_writeReg h _ _) _
      · rw [chip_load8 h ok]; exact chip_setPc (chip_writeReg h _ _) _
      · rw [chip_load16 h ok]; exact chip_setPc (chip_writeReg h _ _) _
  | store op rs1 rs2 off =>
    dsimp only [exec] at e ⊢
    rw [hp, hr, hr]
    revert e
    split
    · intro e; cases e
    · intro e
      cases e
      refine ⟨_, rfl, ?_⟩
      cases op
      · exact chip_setPc (chip_store8 h ok _) _
      · exact chip_setPc (chip_store16 h ok _) _
      · exact chip_setPc (chip_store32 h ok _) _
  | aluImm op rd rs1 imm =>
    exact ⟨_, rfl, by cases e; rw [hp, hr]; exact chip_setPc (chip_writeReg h _ _) _⟩
  | alu op rd rs1 rs2 =>
    exact ⟨_, rfl, by cases e; rw [hp, hr, hr]; exact chip_setPc (chip_writeReg h _ _) _⟩
  | fence =>
    exact ⟨_, rfl, by cases e; rw [hp]; exact chip_setPc h _⟩

/-- One step: the chip takes the step the model takes. -/
theorem chip_step (h : ChipSim c m) (ok : StepOk m) {m' : Machine} (e : RV32.step m = some m') :
    ∃ c', RV32.step c = some c' ∧ ChipSim c' m' := by
  unfold RV32.step at e ⊢
  rw [chip_fetch h ok.1]
  revert e
  cases hf : fetch m with
  | none => intro e; cases e
  | some p =>
    obtain ⟨i, len⟩ := p
    intro e
    exact chip_exec h (ok.2 i len hf) e

end Sim

/-- **The chip runs the model's run.** When the model's run from `m` to
`m'` meets the SRAM alias obligation, the chip, started in agreement with
`m`, reaches a state that agrees with `m'`. -/
theorem chip_steps {m m' : Machine} (s : Steps m m') (ok : AliasOk m m') :
    ∀ {c : Chip}, ChipSim c m → ∃ c', Steps c c' ∧ ChipSim c' m' := by
  induction s with
  | refl => intro c h; exact ⟨c, .refl c, h⟩
  | @cons a b d e s ih =>
    intro c h
    obtain ⟨c₁, e₁, h₁⟩ := chip_step h (ok a b (.refl a) e s) e
    obtain ⟨c', s', h'⟩ := ih (fun m₁ m₂ s₁ e₂ s₂ => ok m₁ m₂ (.cons e s₁) e₂ s₂) h₁
    exact ⟨c', .cons e₁ s', h'⟩

/-- A property of the end of a model run carries to the chip: for any run
of the model from `m` that meets the obligation and ends in a state with
property `P`, such as `reset_correct`'s jump or a halt, the chip reaches a
state that agrees with it. -/
theorem chip_run {m : Machine} {c : Chip} {P : Machine → Prop} (h : ∃ m', Steps m m' ∧ P m')
    (ok : ∀ m', Steps m m' → AliasOk m m') (hc : ChipSim c m) :
    ∃ m', Steps m m' ∧ P m' ∧ ∃ c', Steps c c' ∧ ChipSim c' m' :=
  let ⟨m', s, p⟩ := h
  ⟨m', s, p, chip_steps s (ok m' s) hc⟩

/-- The model of the chip with registers `regs`, program counter `pc`, and
SRAM and devices `C`: each address reads the byte the chip has there. -/
def chipModel (regs : Fin 32 → Word) (pc : Word) (C : Word → BitVec 8) : Machine :=
  ⟨regs, pc, fun a => C (sramCanon a)⟩

theorem chipSim_init (regs : Fin 32 → Word) (pc : Word) (C : Word → BitVec 8) :
    ChipSim ⟨regs, pc, C⟩ (chipModel regs pc C) :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

/-- **The memory map meets the obligation's address conditions.** The
bootloader's stack and data at 0x3FCC8000 to 0x3FCE0000, the application
RAM region at 0x3FC80000 to 0x3FCA0000 on the data bus, where `boot` copies
RAM code through its data-bus alias, and everything at or above 0x40000000
except SRAM's instruction-bus view (the ROM, the flash windows, and the
peripheral registers) are `StoreOk`. The image's code and read-only data,
at 0x403A0000 to 0x403C4000 and 0x3FCC4000 to 0x3FCC8000, are `Coherent`. -/
theorem aliasOk_regions (a : Word) :
    ((0x3FCC8000 ≤ a.toNat ∧ a.toNat < 0x3FCE0000) ∨ (0x3FC80000 ≤ a.toNat ∧ a.toNat < 0x3FCA0000) ∨
        (0x3C000000 ≤ a.toNat ∧ a.toNat < 0x3C800000) ∨
        (0x40000000 ≤ a.toNat ∧ a.toNat < 0x40380000) ∨ 0x403E0000 ≤ a.toNat → StoreOk a) ∧
    ((0x403A0000 ≤ a.toNat ∧ a.toNat < 0x403C4000) ∨ (0x3FCC4000 ≤ a.toNat ∧ a.toNat < 0x3FCC8000) →
      Coherent a) := by
  refine ⟨fun h => ⟨fun hi => ?_, fun hd => ?_⟩, fun h => ?_⟩
  · unfold IBusSram at hi
    rcases h with h | h | h | h | h <;> omega
  · rcases h with h | h | h | h | h <;> omega
  · unfold Coherent IBusSram
    rcases h with h | h
    · exact .inr h
    · exact .inl fun hi => by omega

end C3.RV32
