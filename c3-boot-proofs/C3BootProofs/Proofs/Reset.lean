import C3BootProofs.Proofs.ResetPath
import C3BootProofs.Proofs.BootMainStart

/-!
# From the reset vector

`reset_correct` joins `rst_path`, from the ROM's jump into `_start` to the
entry of `boot_main`, with `bootMain_correct`, from that entry to the jump
into an application or a halt. The reset path changes only the stack word
that `setup` pushes and the watchdog and clock registers, so the eFuse
level word that `boot_main` reads is the one the ROM left (`reset_word`).
-/

namespace C3.RV32.Cur

open C3 C3.Image C3.RV32.BootMainContract

/-- The reset path leaves the eFuse level word alone. -/
theorem reset_word (M0 : Word → BitVec 8) : memLoad32 (resetMem M0) efuseRd = memLoad32 M0 efuseRd :=
  memLoad32_congr fun j hj => by
    have e : (efuseRd + BitVec.ofNat 32 j).toNat = 0x6000883C + j := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, show efuseRd.toNat = 0x6000883C from rfl]; omega
    exact resetMem_out M0 (efuseRd + BitVec.ofNat 32 j) (.inr (by omega)) (.inl (by omega)) (.inl (by omega))

/-- The level that `boot_main` reads at its entry is the level at reset. -/
theorem reset_level (M0 : Word → BitVec 8) : bmLevel (resetMem M0) = bmLevel M0 := by
  unfold bmLevel; rw [reset_word]

/-- **The bootloader boots only what `decideBoot` boots, from reset.**

The ROM jumps to `_start` (`RST`, 0x403A0000) with memory `M0` and any
register values. `_start`, `setup`, `watchdog_arm`, and `clock_run_160`
then run as `rst_path` proves and enter `boot_main` with the stack pointer
at 0x3FCDC700 and memory `resetMem M0`. From there, the bootloader halts
(including every panic), or it jumps to the entry point of the image in a
slot `slot` that `decideBoot` boots at level `target`, given the boot-state
records in flash and the eFuse level at reset. At the jump, `target` is at
most the eFuse level then, `Spec/Level`'s `level` of the `SECURE_VERSION`
field that the controller reads back, and that word is its value at reset
with some bits set. Memory outside `boot_main`'s stack and the peripheral
registers is what `boot` loads, as in `bootMain_correct`.

What the theorem assumes of the hardware:

* The ROM has loaded the bootloader's segments: the reset path's code is
  at its link addresses (`RstCode M0`), and `resetMem M0` meets `BmHyp`
  at the stack pointer 0x3FCDC700. `BmHyp` holds the rest of the code,
  the free stack, the ROM routines' contracts (`RomFn`), and the ROM's
  flash reads. `resetMem_out` says `resetMem M0` equals `M0` outside the
  stack word at 0x3FCDC70C and the device registers that the reset path
  writes, so these are facts about the image the ROM loaded.
* The CPU executes the RV32IMC instructions as `RV32` models them, at any
  clock speed. The clock switch in `clock_run_160` doesn't change what an
  instruction does.
* A store to a device register is a memory write, and a load reads what
  the last store there wrote. What the device does with the write, such
  as arming timer group 0's watchdog or switching the CPU clock, is
  outside the memory that the theorem talks about. A watchdog reset, or
  any other reset, restarts the ROM and ends this run, so it boots nothing
  that this theorem doesn't cover.
* The eFuse controller meets `EfuseCtl` through `efuse_program_run`
  (`BmEnv.epr`): each call returns, keeps the registers that the calling
  convention saves, writes only the controller's registers, and leaves the
  level word at its old value with some bits set. That's all the theorem
  assumes of eFuse burning; the loop in `boot` that burns until the level
  read back reaches the target, or halts after three failed tries, is
  proved. -/
theorem reset_correct {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy}
    {M0 : Word → BitVec 8} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop} (C : RstCode M0)
    (X : BmHyp flash pinned policy (resetMem M0) 0x3FCDC700 R romStack stack0 romBase romCode E)
    (m : Machine) (hm : m.mem = M0) (hpc : m.pc = RST) :
    Panics m ∨ ∃ m', Steps m m' ∧
      ∃ (slot : Slot) (target : Nat) (mf : Manifest) (sv t : Nat) (h : ImageHeader) (Mb : Word → BitVec 8),
        (decideBoot (bmRecs flash).1 (bmLevel M0) fun s =>
          (bmcAccept flash pinned policy (bmLevel M0) (BitVec.ofNat 32 (bmSlotNum s))).map (·.2.1)).outcome =
          .boot slot target ∧
        bmcAccept flash pinned policy (bmLevel M0) (BitVec.ofNat 32 (bmSlotNum slot)) = some (mf, sv, t) ∧
        decodeImageHeader (bmcImage flash (BitVec.ofNat 32 (bmSlotNum slot)) mf) mf.image.length = some h ∧
        target ≤ level (Fuses.ofNat (((memLoad32 m'.mem efuseRd).toNat >>> 14) % 65536)) ∧
        (∃ X, memLoad32 m'.mem efuseRd = memLoad32 M0 efuseRd ||| X) ∧
        m'.pc = BitVec.ofNat 32 h.entryPoint &&& ~~~1 ∧
        reg m' a0 = BitVec.ofNat 32 (bmSlotNum slot) ∧
        BmKeep (resetMem M0) Mb (0x3FCDC700 - BitVec.ofNat 32 (bmK R romStack stack0))
          (bmK R romStack stack0) ∧
        HdrAt Mb (bmAcc 0x3FCDC700) h ∧
        ∀ x, Sep (0x3FCDC700 - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) x 1 →
          (x.toNat < 0x60000000 ∨ 0x600C4000 ≤ x.toNat) →
          m'.mem x = bootMem flash Mb (bmAcc 0x3FCDC700)
            (BitVec.ofNat 32 (bmcBase (BitVec.ofNat 32 (bmSlotNum slot)) + mf.image.offset)) x := by
  obtain ⟨n, c, pc, mem, sp⟩ := rst_path C hm hpc
  rcases bootMain_correct X n mem pc sp with hp | ⟨m', c', rest⟩
  · exact .inl (Panics.of_steps c hp)
  · rw [reset_level, reset_word] at rest
    exact .inr ⟨m', c.trans c', rest⟩

end C3.RV32.Cur
