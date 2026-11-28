import C3BootProofs.Image.Bootloader
import C3BootProofs.Image.BootloaderReset
import C3BootProofs.Proofs.Parse

/-!
# From the reset vector to `boot_main`

The ROM jumps to `_start` at 0x403A0000. `_start` sets the stack pointer
to 0x3FCDC710, zeroes `.bss` (empty in the pinned image, so the loop
exits at once), and calls `setup`. `setup` pushes its return address,
calls `watchdog_arm`, which disables the RTC watchdog and arms timer
group 0's watchdog, then `clock_run_160`, which switches the CPU clock,
and tail-calls `boot_main` with the stack pointer at 0x3FCDC700.

The model treats the timer groups and the system registers as memory:
each MMIO store writes four bytes, and each MMIO load reads them back.
`rst_path` proves that this path reaches `boot_main` with memory equal to
`resetMem M0`: the reset memory plus the saved return address and the
stores of the two device routines. `resetMem_out` says that memory
outside the stack word and those device registers is unchanged.
-/

namespace C3.RV32.Cur

open C3.Image

/-- The ROM's jump target: `_start`. -/
abbrev RST : Word := BitVec.ofNat 32 startEntryAddress
/-- `setup`, which `_start` calls. -/
abbrev SUP : Word := BitVec.ofNat 32 setupFnAddress
/-- `watchdog_arm`. -/
abbrev WDG : Word := BitVec.ofNat 32 watchdogArmAddress
/-- `clock_run_160`. -/
abbrev CLK : Word := BitVec.ofNat 32 clockRun160Address

set_option maxRecDepth 20000

theorem rst_at_0 : fetchRel startEntryCode 0x0 = some (.auipc sp 0xFF93C000, 4) := by decide
theorem rst_at_4 : fetchRel startEntryCode 0x4 = some (.aluImm .add sp sp 0x710, 4) := by decide
theorem rst_at_8 : fetchRel startEntryCode 0x8 = some (.auipc (5 : Fin 32) 0xFF926000, 4) := by decide
theorem rst_at_c : fetchRel startEntryCode 0xC = some (.aluImm .add (5 : Fin 32) (5 : Fin 32) 0x730, 4) := by decide
theorem rst_at_10 : fetchRel startEntryCode 0x10 = some (.auipc (6 : Fin 32) 0xFF926000, 4) := by decide
theorem rst_at_14 : fetchRel startEntryCode 0x14 = some (.aluImm .add (6 : Fin 32) (6 : Fin 32) 0x728, 4) := by decide
theorem rst_at_18 : fetchRel startEntryCode 0x18 = some (.branch .bgeu (5 : Fin 32) (6 : Fin 32) 0xC, 4) := by decide
theorem rst_at_24 : fetchRel startEntryCode 0x24 = some (.auipc ra 0x17000, 4) := by decide
theorem rst_at_28 : fetchRel startEntryCode 0x28 = some (.jalr ra ra 0x1B4, 4) := by decide

theorem sup_at_0 : fetchRel setupFnCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem sup_at_2 : fetchRel setupFnCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem sup_at_4 : fetchRel setupFnCode 0x4 = some (.auipc ra 0x0, 4) := by decide
theorem sup_at_8 : fetchRel setupFnCode 0x8 = some (.jalr ra ra 0xFFFFFFB6, 4) := by decide
theorem sup_at_c : fetchRel setupFnCode 0xC = some (.auipc ra 0x0, 4) := by decide
theorem sup_at_10 : fetchRel setupFnCode 0x10 = some (.jalr ra ra 0xFFFFFF94, 4) := by decide
theorem sup_at_14 : fetchRel setupFnCode 0x14 = some (.auipc ra 0x0, 4) := by decide
theorem sup_at_18 : fetchRel setupFnCode 0x18 = some (.jalr ra ra 0xFFFFFC0A, 4) := by decide

theorem wdg_at_0 : fetchRel watchdogArmCode 0x0 = some (.lui a0 0x60020000, 4) := by decide
theorem wdg_at_4 : fetchRel watchdogArmCode 0x4 = some (.lui a1 0x50D84000, 4) := by decide
theorem wdg_at_8 : fetchRel watchdogArmCode 0x8 = some (.lui a2 0x400000, 4) := by decide
theorem wdg_at_c : fetchRel watchdogArmCode 0xC = some (.aluImm .add a1 a1 0xFFFFFAA1, 4) := by decide
theorem wdg_at_10 : fetchRel watchdogArmCode 0x10 = some (.store .sw a0 a1 0x64, 2) := by decide
theorem wdg_at_12 : fetchRel watchdogArmCode 0x12 = some (.aluImm .add a4 x0 0x0, 2) := by decide
theorem wdg_at_14 : fetchRel watchdogArmCode 0x14 = some (.store .sw a0 a4 0x48, 2) := by decide
theorem wdg_at_16 : fetchRel watchdogArmCode 0x16 = some (.store .sw a0 a2 0x48, 2) := by decide
theorem wdg_at_18 : fetchRel watchdogArmCode 0x18 = some (.lui a3 0x6001F000, 4) := by decide
theorem wdg_at_1c : fetchRel watchdogArmCode 0x1C = some (.store .sw a0 a4 0x64, 2) := by decide
theorem wdg_at_1e : fetchRel watchdogArmCode 0x1E = some (.store .sw a3 a1 0x64, 2) := by decide
theorem wdg_at_20 : fetchRel watchdogArmCode 0x20 = some (.store .sw a3 a4 0x48, 2) := by decide
theorem wdg_at_22 : fetchRel watchdogArmCode 0x22 = some (.store .sw a3 a2 0x48, 2) := by decide
theorem wdg_at_24 : fetchRel watchdogArmCode 0x24 = some (.lui a0 0x9C400000, 4) := by decide
theorem wdg_at_28 : fetchRel watchdogArmCode 0x28 = some (.lui a1 0x2000, 2) := by decide
theorem wdg_at_2a : fetchRel watchdogArmCode 0x2A = some (.store .sw a3 a0 0x4C, 2) := by decide
theorem wdg_at_2c : fetchRel watchdogArmCode 0x2C = some (.aluImm .add a0 a1 0x710, 4) := by decide
theorem wdg_at_30 : fetchRel watchdogArmCode 0x30 = some (.store .sw a3 a0 0x50, 2) := by decide
theorem wdg_at_32 : fetchRel watchdogArmCode 0x32 = some (.lui a0 0xE03F8000, 4) := by decide
theorem wdg_at_36 : fetchRel watchdogArmCode 0x36 = some (.store .sw a3 a0 0x48, 2) := by decide
theorem wdg_at_38 : fetchRel watchdogArmCode 0x38 = some (.lui a0 0xE07F8000, 4) := by decide
theorem wdg_at_3c : fetchRel watchdogArmCode 0x3C = some (.store .sw a3 a0 0x48, 2) := by decide
theorem wdg_at_3e : fetchRel watchdogArmCode 0x3E = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem wdg_at_40 : fetchRel watchdogArmCode 0x40 = some (.store .sw a3 a0 0x60, 2) := by decide
theorem wdg_at_42 : fetchRel watchdogArmCode 0x42 = some (.store .sw a3 a4 0x64, 2) := by decide
theorem wdg_at_44 : fetchRel watchdogArmCode 0x44 = some (.jalr x0 ra 0x0, 2) := by decide

theorem clk_at_0 : fetchRel clockRun160Code 0x0 = some (.lui a0 0x600C0000, 4) := by decide
theorem clk_at_4 : fetchRel clockRun160Code 0x4 = some (.load .lw a1 a0 0x8, 2) := by decide
theorem clk_at_6 : fetchRel clockRun160Code 0x6 = some (.aluImm .and a1 a1 0xFFFFFFFC, 2) := by decide
theorem clk_at_8 : fetchRel clockRun160Code 0x8 = some (.aluImm .add a1 a1 0x1, 2) := by decide
theorem clk_at_a : fetchRel clockRun160Code 0xA = some (.store .sw a0 a1 0x8, 2) := by decide
theorem clk_at_c : fetchRel clockRun160Code 0xC = some (.load .lw a1 a0 0x58, 2) := by decide
theorem clk_at_e : fetchRel clockRun160Code 0xE = some (.lui a2 0xFFFFF000, 2) := by decide
theorem clk_at_10 : fetchRel clockRun160Code 0x10 = some (.alu .and a1 a1 a2, 2) := by decide
theorem clk_at_12 : fetchRel clockRun160Code 0x12 = some (.aluImm .add a1 a1 0x400, 4) := by decide
theorem clk_at_16 : fetchRel clockRun160Code 0x16 = some (.store .sw a0 a1 0x58, 2) := by decide
theorem clk_at_18 : fetchRel clockRun160Code 0x18 = some (.jalr x0 ra 0x0, 2) := by decide

/-- Stores `l` in order, four bytes each. -/
def rstStoreAll : (Word → BitVec 8) → List (Word × Word) → Word → BitVec 8
  | M, [] => M
  | M, (a, v) :: l => rstStoreAll (memStore32 M a v) l

/-- `watchdog_arm`'s stores, in program order: unlock, disable, and lock
the RTC watchdog (0x600200xx), then unlock timer group 0's watchdog
(0x6001F0xx), set its prescaler and stage-0 timeout, enable it, feed it,
and lock it. -/
def rstWdg : List (Word × Word) :=
  [(0x60020064, 0x50D83AA1), (0x60020048, 0), (0x60020048, 0x400000), (0x60020064, 0),
   (0x6001F064, 0x50D83AA1), (0x6001F048, 0), (0x6001F048, 0x400000), (0x6001F04C, 0x9C400000),
   (0x6001F050, 0x2710), (0x6001F048, 0xE03F8000), (0x6001F048, 0xE07F8000), (0x6001F060, 1),
   (0x6001F064, 0)]

/-- Memory after `watchdog_arm`. -/
def wdgMem (M : Word → BitVec 8) : Word → BitVec 8 := rstStoreAll M rstWdg

/-- Memory after `clock_run_160`: two read-modify-write stores to the
system registers at 0x600C0008 and 0x600C0058. The model reads the
second register after the first store. -/
def clkMem (M : Word → BitVec 8) : Word → BitVec 8 :=
  memStore32 (memStore32 M 0x600C0008 ((memLoad32 M 0x600C0008 &&& 0xFFFFFFFC) + 1)) 0x600C0058
    ((memLoad32 (memStore32 M 0x600C0008 ((memLoad32 M 0x600C0008 &&& 0xFFFFFFFC) + 1))
      0x600C0058 &&& 0xFFFFF000) + 0x400)

/-- Memory when `boot_main` starts, from memory `M0` at the reset vector:
`setup` saved `_start`'s return address 0x403A002C at 0x3FCDC70C, then the
watchdog and clock routines stored to their device registers. -/
def resetMem (M0 : Word → BitVec 8) : Word → BitVec 8 :=
  clkMem (wdgMem (memStore32 M0 0x3FCDC70C 0x403A002C))

/-- The reset path's code in memory: `_start`, `setup`, and the two device
routines, at their link addresses. -/
structure RstCode (M : Word → BitVec 8) : Prop where
  start : CodeIn M RST startEntryCode
  setup : CodeIn M SUP setupFnCode
  wdg : CodeIn M WDG watchdogArmCode
  clk : CodeIn M CLK clockRun160Code

theorem rst_storeAll_out {x : Word} :
    ∀ (M : Word → BitVec 8) (l : List (Word × Word)), (∀ p ∈ l, Sep p.1 4 x 1) →
      rstStoreAll M l x = M x
  | _, [], _ => rfl
  | M, (a, v) :: l, h => by
    show rstStoreAll (memStore32 M a v) l x = M x
    rw [rst_storeAll_out _ l (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    exact memStore32_get_sep (h _ List.mem_cons_self)

theorem rst_wdgHi : ∀ p ∈ rstWdg, 0x6001F000 ≤ p.1.toNat ∧ p.1.toNat + 4 ≤ 0x60021000 := by
  decide

/-- `watchdog_arm` changes only the timer groups' registers. -/
theorem wdgMem_out (M : Word → BitVec 8) (x : Word)
    (hx : x.toNat < 0x6001F000 ∨ 0x60021000 ≤ x.toNat) : wdgMem M x = M x :=
  rst_storeAll_out M rstWdg fun p hp => by
    have h := rst_wdgHi p hp
    rcases hx with hx | hx
    · exact (sep_of_le (a := x) (n := 1) (by omega) (by omega)).symm
    · exact sep_of_le (by omega) (by omega)

/-- `clock_run_160` changes only the system registers at 0x600C0008 and
0x600C0058. -/
theorem clkMem_out (M : Word → BitVec 8) (x : Word)
    (hx : x.toNat < 0x600C0000 ∨ 0x600C1000 ≤ x.toNat) : clkMem M x = M x := by
  have h : ∀ a : Word, 0x600C0000 ≤ a.toNat → a.toNat + 4 ≤ 0x600C1000 → Sep a 4 x 1 := by
    intro a h1 h2
    rcases hx with hx | hx
    · exact (sep_of_le (a := x) (n := 1) (by omega) (by omega)).symm
    · exact sep_of_le (by omega) (by omega)
  unfold clkMem
  rw [memStore32_get_sep (h _ (by decide) (by decide)), memStore32_get_sep (h _ (by decide) (by decide))]

/-- Memory when `boot_main` starts agrees with the reset memory outside
the stack word at 0x3FCDC70C, the timer groups (0x6001F000 to
0x60021000), and the system registers (0x600C0000 to 0x600C1000). -/
theorem resetMem_out (M0 : Word → BitVec 8) (x : Word)
    (hs : x.toNat < 0x3FCDC70C ∨ 0x3FCDC710 ≤ x.toNat)
    (hw : x.toNat < 0x6001F000 ∨ 0x60021000 ≤ x.toNat)
    (hk : x.toNat < 0x600C0000 ∨ 0x600C1000 ≤ x.toNat) : resetMem M0 x = M0 x := by
  unfold resetMem
  rw [clkMem_out _ x hk, wdgMem_out _ x hw]
  have e : (0x3FCDC70C : Word).toNat = 0x3FCDC70C := rfl
  rcases hs with hs | hs
  · exact memStore32_get_sep (sep_of_le (a := x) (n := 1) (by rw [e]; omega) (by decide)).symm
  · exact memStore32_get_sep (sep_of_le (by rw [e]; omega) (by omega))

theorem rst_code {M M' : Word → BitVec 8} {b : Word} {code : List Nat} (hc : CodeIn M b code)
    (h : ∀ x : Word, x.toNat < 0x6001F000 → M' x = M x) (hl : b.toNat + code.length ≤ 0x6001F000) :
    CodeIn M' b code := fun i hi => by
  rw [h _ (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]; exact hc i hi

def wdgBlk : List BInstr :=
  [.lui a0 0x60020000, .lui a1 0x50D84000, .lui a2 0x400000, .aluImm .add a1 a1 0xFFFFFAA1,
   .sw a0 a1 0x64, .aluImm .add a4 x0 0x0, .sw a0 a4 0x48, .sw a0 a2 0x48, .lui a3 0x6001F000,
   .sw a0 a4 0x64, .sw a3 a1 0x64, .sw a3 a4 0x48, .sw a3 a2 0x48, .lui a0 0x9C400000,
   .lui a1 0x2000, .sw a3 a0 0x4C, .aluImm .add a0 a1 0x710, .sw a3 a0 0x50, .lui a0 0xE03F8000,
   .sw a3 a0 0x48, .lui a0 0xE07F8000, .sw a3 a0 0x48, .aluImm .add a0 x0 0x1, .sw a3 a0 0x60,
   .sw a3 a4 0x64]

theorem wdgBlk_end : blockEnd watchdogArmCode 0x0 wdgBlk = some 0x44 :=
  (blockEnd_cons' (off' := 0x4) wdg_at_0 rfl (blockEnd_cons' (off' := 0x8) wdg_at_4 rfl (blockEnd_cons' (off' := 0xC) wdg_at_8 rfl (blockEnd_cons' (off' := 0x10) wdg_at_c rfl (blockEnd_cons' (off' := 0x12) wdg_at_10 rfl (blockEnd_cons' (off' := 0x14) wdg_at_12 rfl (blockEnd_cons' (off' := 0x16) wdg_at_14 rfl (blockEnd_cons' (off' := 0x18) wdg_at_16 rfl (blockEnd_cons' (off' := 0x1C) wdg_at_18 rfl (blockEnd_cons' (off' := 0x1E) wdg_at_1c rfl (blockEnd_cons' (off' := 0x20) wdg_at_1e rfl (blockEnd_cons' (off' := 0x22) wdg_at_20 rfl (blockEnd_cons' (off' := 0x24) wdg_at_22 rfl (blockEnd_cons' (off' := 0x28) wdg_at_24 rfl (blockEnd_cons' (off' := 0x2A) wdg_at_28 rfl (blockEnd_cons' (off' := 0x2C) wdg_at_2a rfl (blockEnd_cons' (off' := 0x30) wdg_at_2c rfl (blockEnd_cons' (off' := 0x32) wdg_at_30 rfl (blockEnd_cons' (off' := 0x36) wdg_at_32 rfl (blockEnd_cons' (off' := 0x38) wdg_at_36 rfl (blockEnd_cons' (off' := 0x3C) wdg_at_38 rfl (blockEnd_cons' (off' := 0x3E) wdg_at_3c rfl (blockEnd_cons' (off' := 0x40) wdg_at_3e rfl (blockEnd_cons' (off' := 0x42) wdg_at_40 rfl (blockEnd_cons' (off' := 0x44) wdg_at_42 rfl rfl)))))))))))))))))))))))))

def clkBlk : List BInstr :=
  [.lui a0 0x600C0000, .lw a1 a0 0x8, .aluImm .and a1 a1 0xFFFFFFFC, .aluImm .add a1 a1 0x1,
   .sw a0 a1 0x8, .lw a1 a0 0x58, .lui a2 0xFFFFF000, .alu .and a1 a1 a2, .aluImm .add a1 a1 0x400,
   .sw a0 a1 0x58]

theorem clkBlk_end : blockEnd clockRun160Code 0x0 clkBlk = some 0x18 :=
  (blockEnd_cons' (off' := 0x4) clk_at_0 rfl (blockEnd_cons' (off' := 0x6) clk_at_4 rfl (blockEnd_cons' (off' := 0x8) clk_at_6 rfl (blockEnd_cons' (off' := 0xA) clk_at_8 rfl (blockEnd_cons' (off' := 0xC) clk_at_a rfl (blockEnd_cons' (off' := 0xE) clk_at_c rfl (blockEnd_cons' (off' := 0x10) clk_at_e rfl (blockEnd_cons' (off' := 0x12) clk_at_10 rfl (blockEnd_cons' (off' := 0x16) clk_at_12 rfl (blockEnd_cons' (off' := 0x18) clk_at_16 rfl rfl))))))))))

def supBlk : List BInstr := [.aluImm .add sp sp 0xFFFFFFF0, .sw sp ra 0xC]

theorem supBlk_end : blockEnd setupFnCode 0x0 supBlk = some 0x4 :=
  (blockEnd_cons' (off' := 0x2) sup_at_0 rfl (blockEnd_cons' (off' := 0x4) sup_at_2 rfl rfl))

/-- `watchdog_arm` performs its thirteen stores and returns. -/
theorem wdg_correct {M : Word → BitVec 8} {m : Machine} (hc : CodeIn M WDG watchdogArmCode)
    (s : St M WDG m 0 (reg m)) :
    ∃ m', Steps m m' ∧ m'.pc = reg m ra &&& ~~~1 ∧ m'.mem = wdgMem M ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m' r = reg m r := by
  have sep : ∀ a : Word, WDG.toNat + 0x46 ≤ a.toNat → a.toNat + 4 ≤ 2 ^ 32 →
      Sep a 4 WDG watchdogArmCode.length := fun a h1 h2 =>
    (sep_of_le (by rw [show watchdogArmCode.length = 0x46 from rfl]; exact h1) h2).symm
  obtain ⟨n1, c1, u1⟩ := s.block wdgBlk hc wdgBlk_end
    (by
      simp only [BlockOk, BInstr.ok, BInstr.run, wdgBlk]
      simp +decide only [upd, ↓reduceIte, true_and, and_true]
      repeat' constructor
      all_goals first | decide | exact sep _ (by decide) (by decide))
  have hz := s.zero
  have e1 : (runBlock wdgBlk (M, reg m)).1 = wdgMem M := by
    simp +decide only [runBlock, BInstr.run, wdgBlk, upd, ↓reduceIte] <;> rfl
  rw [e1] at u1
  have hc1 : CodeIn (wdgMem M) WDG watchdogArmCode :=
    rst_code hc (fun x hx => wdgMem_out M x (Or.inl hx)) (by decide)
  obtain ⟨n2, d2, pc2, mem2, regs2⟩ := u1.jalr hc1 wdg_at_44
  have q : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 →
      (runBlock wdgBlk (M, reg m)).2 r = reg m r := fun r h0 h1 h2 h3 h4 =>
    runBlock_reg _ _ _ r hz (by simp only [wdgBlk]; revert h0 h1 h2 h3 h4; revert r; decide)
  refine ⟨n2, c1.trans (.single d2), ?_, mem2, fun r h0 h1 h2 h3 h4 => ?_⟩
  · rw [pc2, q ra (by decide) (by decide) (by decide) (by decide) (by decide), add_lit_zero]
  · rw [regs2, q r h0 h1 h2 h3 h4]

/-- `clock_run_160` performs its two read-modify-write stores and
returns. -/
theorem clk_correct {M : Word → BitVec 8} {m : Machine} (hc : CodeIn M CLK clockRun160Code)
    (s : St M CLK m 0 (reg m)) :
    ∃ m', Steps m m' ∧ m'.pc = reg m ra &&& ~~~1 ∧ m'.mem = clkMem M ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → reg m' r = reg m r := by
  have sep : ∀ a : Word, CLK.toNat + 0x1A ≤ a.toNat → a.toNat + 4 ≤ 2 ^ 32 →
      Sep a 4 CLK clockRun160Code.length := fun a h1 h2 =>
    (sep_of_le (by rw [show clockRun160Code.length = 0x1A from rfl]; exact h1) h2).symm
  obtain ⟨n1, c1, u1⟩ := s.block clkBlk hc clkBlk_end
    (by
      simp only [BlockOk, BInstr.ok, BInstr.run, clkBlk]
      simp +decide only [upd, ↓reduceIte, true_and, and_true]
      repeat' constructor
      all_goals first | decide | exact sep _ (by decide) (by decide))
  have hz := s.zero
  have e1 : (runBlock clkBlk (M, reg m)).1 = clkMem M := by
    simp +decide only [runBlock, BInstr.run, clkBlk, upd, ↓reduceIte] <;> rfl
  rw [e1] at u1
  have hc1 : CodeIn (clkMem M) CLK clockRun160Code :=
    rst_code hc (fun x hx => clkMem_out M x (Or.inl (by omega))) (by decide)
  obtain ⟨n2, d2, pc2, mem2, regs2⟩ := u1.jalr hc1 clk_at_18
  have q : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → (runBlock clkBlk (M, reg m)).2 r = reg m r :=
    fun r h0 h1 h2 =>
      runBlock_reg _ _ _ r hz (by simp only [clkBlk]; revert h0 h1 h2; revert r; decide)
  refine ⟨n2, c1.trans (.single d2), ?_, mem2, fun r h0 h1 h2 => ?_⟩
  · rw [pc2, q ra (by decide) (by decide) (by decide), add_lit_zero]
  · rw [regs2, q r h0 h1 h2]

/-- From the reset vector, `_start` and `setup` reach `boot_main` with
the stack pointer at 0x3FCDC700 and memory `resetMem M0`, whatever the
registers held. -/
theorem rst_path {M0 : Word → BitVec 8} (E : RstCode M0) {m : Machine} (hm : m.mem = M0)
    (hpc : m.pc = RST) :
    ∃ n, Steps m n ∧ n.pc = BitVec.ofNat 32 bootMainAddress ∧ n.mem = resetMem M0 ∧
      reg n sp = 0x3FCDC700 := by
  have s0 : St M0 RST m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], hm, fun _ => rfl⟩
  obtain ⟨n1, d1, u1⟩ := s0.auipc E.start rst_at_0 (off' := 4) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.aluImm E.start rst_at_4 (off' := 8) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.auipc E.start rst_at_8 (off' := 0xC) (by decide)
  obtain ⟨n4, d4, u4⟩ := u3.aluImm E.start rst_at_c (off' := 0x10) (by decide)
  obtain ⟨n5, d5, u5⟩ := u4.auipc E.start rst_at_10 (off' := 0x14) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5.aluImm E.start rst_at_14 (off' := 0x18) (by decide)
  obtain ⟨n7, d7, u7⟩ := u6.taken E.start 0x24 rst_at_18 (by decide)
    (by simp +decide only [upd, ↓reduceIte])
  obtain ⟨n8, c8, pc8, mem8, regs8⟩ := u7.callRa (cb := SUP) E.start rst_at_24 rst_at_28
    (by decide) (by decide)
  have hsp8 : reg n8 sp = 0x3FCDC710 := by
    rw [regs8]; simp +decide only [upd, ↓reduceIte]
  have hra8 : reg n8 ra = 0x403A002C := by
    rw [regs8]; simp +decide only [upd, ↓reduceIte]
  -- `setup`: push the return address.
  have s8 : St M0 SUP n8 0 (reg n8) := ⟨by rw [pc8, add_ofNat_zero], mem8, fun _ => rfl⟩
  obtain ⟨n9, c9, u9⟩ := s8.block supBlk E.setup supBlk_end
    (by
      simp only [BlockOk, BInstr.ok, BInstr.run, supBlk]
      simp +decide only [upd, ↓reduceIte, true_and, and_true, hsp8]
      repeat' constructor
      all_goals first | decide | exact sep_of_le (by decide) (by decide))
  have e9 : (runBlock supBlk (M0, reg n8)).1 = memStore32 M0 0x3FCDC70C 0x403A002C := by
    simp +decide only [runBlock, BInstr.run, supBlk, upd, ↓reduceIte, hsp8, hra8] <;> rfl
  have hsp9 : reg n9 sp = 0x3FCDC700 := by
    rw [u9.regs]; simp +decide only [runBlock, BInstr.run, supBlk, upd, ↓reduceIte, hsp8]
  rw [e9] at u9
  have stk : ∀ (b : Word) (code : List Nat), b.toNat + code.length ≤ 2 ^ 32 →
      0x3FCDC710 ≤ b.toNat → CodeIn M0 b code →
      CodeIn (memStore32 M0 0x3FCDC70C 0x403A002C) b code := fun b code h1 h2 hc =>
    hc.store32 (sep_of_le (by rw [show (0x3FCDC70C : Word).toNat = 0x3FCDC70C from rfl]; omega) h1)
  have hS1 := stk _ _ (by decide) (by decide) E.setup
  have hW1 := stk _ _ (by decide) (by decide) E.wdg
  have hC1 := stk _ _ (by decide) (by decide) E.clk
  -- `watchdog_arm`.
  obtain ⟨n10, c10, pc10, mem10, regs10⟩ := u9.callRa (cb := WDG) hS1 sup_at_4 sup_at_8
    (by decide) (by decide)
  obtain ⟨n11, c11, pc11, mem11, k11⟩ := wdg_correct hW1
    ⟨by rw [pc10, add_ofNat_zero], mem10, fun _ => rfl⟩
  have hS2 : CodeIn (wdgMem (memStore32 M0 0x3FCDC70C 0x403A002C)) SUP setupFnCode :=
    rst_code hS1 (fun x hx => wdgMem_out _ x (Or.inl hx)) (by decide)
  have hC2 : CodeIn (wdgMem (memStore32 M0 0x3FCDC70C 0x403A002C)) CLK clockRun160Code :=
    rst_code hC1 (fun x hx => wdgMem_out _ x (Or.inl hx)) (by decide)
  have s11 : St (wdgMem (memStore32 M0 0x3FCDC70C 0x403A002C)) SUP n11 0xC (reg n11) :=
    ⟨by rw [pc11, regs10]; simp +decide only [upd, ↓reduceIte], mem11, fun _ => rfl⟩
  -- `clock_run_160`.
  obtain ⟨n12, c12, pc12, mem12, regs12⟩ := s11.callRa (cb := CLK) hS2 sup_at_c sup_at_10
    (by decide) (by decide)
  obtain ⟨n13, c13, pc13, mem13, k13⟩ := clk_correct hC2
    ⟨by rw [pc12, add_ofNat_zero], mem12, fun _ => rfl⟩
  have hS3 : CodeIn (resetMem M0) SUP setupFnCode :=
    rst_code hS2 (fun x hx => clkMem_out _ x (Or.inl (by omega))) (by decide)
  have s13 : St (resetMem M0) SUP n13 0x14 (reg n13) :=
    ⟨by rw [pc13, regs12]; simp +decide only [upd, ↓reduceIte], mem13, fun _ => rfl⟩
  -- The tail call to `boot_main`.
  obtain ⟨n14, c14, pc14, mem14, regs14⟩ := s13.callRa (cb := BitVec.ofNat 32 bootMainAddress)
    hS3 sup_at_14 sup_at_18 (by decide) (by decide)
  refine ⟨n14, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7
    (c8.trans (c9.trans (c10.trans (c11.trans (c12.trans (c13.trans c14)))))))))))),
    pc14, mem14, ?_⟩
  rw [regs14, updz s13.zero (by decide), k13 _ (by decide) (by decide) (by decide), regs12,
    updz s11.zero (by decide), k11 _ (by decide) (by decide) (by decide) (by decide) (by decide),
    regs10, updz u9.zero (by decide)]
  exact (u9.regs sp).symm.trans hsp9

end C3.RV32.Cur
