import C3BootProofs.Headline

/-!
# Headline axiom audit and satisfiability witness

This file gives a concise, readable audit of the headline theorems:

1. `exists_reset_loaded_hyp` constructs a concrete memory (`witnessMem`),
   eFuse contract (`efuseCtl_plain`), and ROM stub (`romStub`) satisfying all
   four hardware hypotheses of `reset_correct_loaded` / `headline_boot`
   simultaneously (`Loaded M0`, `EfuseCtl efuseProgramRunCode`, `RomHyp`, and
   the stack bound `0x3FCC8000 + bmK R romStack 0x5C10 ≤ 0x3FCDC700`), proving
   that the hypotheses are jointly consistent and non-vacuous.
2. `#guard_msgs in #print axioms` verifies that the headline theorems, the
   specification theorems, and the satisfiability witness depend only on
   `[propext, Quot.sound]`.
-/

namespace C3.Headline

open C3 C3.Image C3.RV32 C3.RV32.Cur

/-- Bytes of the 4-byte ROM stub `c.li a0, 1; c.ret` (`0x4505`, `0x8082`). -/
def romStubByte (i : Nat) : Nat :=
  match i % 4 with
  | 0 => 0x05
  | 1 => 0x45
  | 2 => 0x82
  | _ => 0x80

/-- A 0x540-byte ROM image at `0x40000000..0x40000540` repeating `c.li a0, 1; c.ret`. -/
def romStub : List Nat := (List.range 0x540).map romStubByte

theorem romStub_len : romStub.length = 0x540 := by
  unfold romStub; rw [List.length_map, List.length_range]

theorem romStub_byteAt (i : Nat) (hi : i < 0x540) :
    byteAt romStub i = BitVec.ofNat 8 (romStubByte i) := by
  unfold byteAt romStub
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem dec_c_li_a0_1 : decode16 (((0x45 : BitVec 8) ++ (0x05 : BitVec 8)).toNat) = some (.aluImm .add a0 x0 1) := by
  decide

theorem dec_c_ret : decode16 (((0x80 : BitVec 8) ++ (0x82 : BitVec 8)).toNat) = some (.jalr x0 ra 0) := by
  decide

theorem romStub_bytes (m : Machine) {addr : Word} (hc : CodeIn m.mem 0x40000000 romStub)
    (hlo : 0x40000000 ≤ addr.toNat) (hhi : addr.toNat + 4 ≤ 0x40000540) (hal : addr.toNat % 4 = 0) :
    m.mem addr = 0x05 ∧ m.mem (addr + 1) = 0x45 ∧ m.mem (addr + 2) = 0x82 ∧ m.mem (addr + 3) = 0x80 := by
  obtain ⟨off, hoff⟩ : ∃ off, addr.toNat - 0x40000000 = off := ⟨_, rfl⟩
  have hoff4 : off % 4 = 0 := by omega
  have hbyte : ∀ j, j < 4 → m.mem (addr + BitVec.ofNat 32 j) = BitVec.ofNat 8 (romStubByte (off + j)) := by
    intro j hj
    have heq : addr + BitVec.ofNat 32 j = (0x40000000 : Word) + BitVec.ofNat 32 (off + j) :=
      BitVec.eq_of_toNat_eq (by
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          show (0x40000000 : Word).toNat = 0x40000000 from rfl]; omega)
    rw [heq]
    have hci := hc (off + j) (Nat.lt_of_lt_of_eq (by omega) romStub_len.symm)
    rw [romStub_byteAt (off + j) (by omega)] at hci
    exact hci
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hbyte 0 (by decide)
    rw [add_ofNat_zero] at h
    rw [h]; unfold romStubByte; rw [show (off + 0) % 4 = 0 by omega]; rfl
  · rw [show addr + 1 = addr + BitVec.ofNat 32 1 from rfl, hbyte 1 (by decide)]
    unfold romStubByte; rw [show (off + 1) % 4 = 1 by omega]; rfl
  · rw [show addr + 2 = addr + BitVec.ofNat 32 2 from rfl, hbyte 2 (by decide)]
    unfold romStubByte; rw [show (off + 2) % 4 = 2 by omega]; rfl
  · rw [show addr + 3 = addr + BitVec.ofNat 32 3 from rfl, hbyte 3 (by decide)]
    unfold romStubByte; rw [show (off + 3) % 4 = 3 by omega]; rfl

theorem romStub_step (m : Machine) {addr : Word} (hc : CodeIn m.mem 0x40000000 romStub)
    (hpc : m.pc = addr) (hlo : 0x40000000 ≤ addr.toNat) (hhi : addr.toNat + 4 ≤ 0x40000540)
    (hal : addr.toNat % 4 = 0) :
    ∃ m', Steps m m' ∧ m'.pc = reg m ra &&& ~~~1 ∧
      reg m' a0 = 1 ∧
      (∀ q, q ≠ a0 → reg m' q = reg m q) ∧
      m'.mem = m.mem := by
  obtain ⟨b0, b1, b2, b3⟩ := romStub_bytes m hc hlo hhi hal
  have hl1 : load16 m addr = (0x45 : BitVec 8) ++ (0x05 : BitVec 8) := by
    show m.mem (addr + 1) ++ m.mem addr = (0x45 : BitVec 8) ++ (0x05 : BitVec 8); rw [b0, b1]
  have hf1 : fetch m = some (.aluImm .add a0 x0 1, 2) := by
    unfold fetch; dsimp only
    rw [show Arch.getPc m = addr from hpc, hl1]
    rw [show (((0x45 : BitVec 8) ++ (0x05 : BitVec 8)).toNat % 4 == 3) = false from rfl]
    simp only [Bool.false_eq_true, ↓reduceIte, dec_c_li_a0_1, Option.map_some]
  have hs1 : RV32.step m = some (Arch.setPc (writeReg m a0 1) (addr + 2)) := by
    unfold RV32.step
    rw [hf1]
    show some (Arch.setPc (writeReg m a0 (aluEval .add (reg m x0) 1)) (Arch.getPc m + 2)) = _
    rw [show Arch.getPc m = addr from hpc, show reg m x0 = 0 from rfl,
      show aluEval .add 0 1 = 1 from rfl]
  let m1 := Arch.setPc (writeReg m a0 1) (addr + 2)
  have hl2 : load16 m1 (addr + 2) = (0x80 : BitVec 8) ++ (0x82 : BitVec 8) := by
    show m.mem (addr + 2 + 1) ++ m.mem (addr + 2) = (0x80 : BitVec 8) ++ (0x82 : BitVec 8)
    rw [show addr + 2 + 1 = addr + 3 from BitVec.add_assoc addr 2 1, b2, b3]
  have hf2 : fetch m1 = some (.jalr x0 ra 0, 2) := by
    unfold fetch; dsimp only
    rw [show Arch.getPc m1 = addr + 2 from rfl, hl2]
    rw [show (((0x80 : BitVec 8) ++ (0x82 : BitVec 8)).toNat % 4 == 3) = false from rfl]
    simp only [Bool.false_eq_true, ↓reduceIte, dec_c_ret, Option.map_some]
  have hs2 : RV32.step m1 = some (Arch.setPc (writeReg m1 x0 (addr + 2 + 2)) (reg m1 ra &&& ~~~1)) := by
    unfold RV32.step
    rw [hf2]
    show some (Arch.setPc (writeReg m1 x0 (addr + 2 + 2)) ((reg m1 ra + 0) &&& ~~~1)) = _
    rw [add_lit_zero]
  refine ⟨Arch.setPc (writeReg m1 x0 (addr + 2 + 2)) (reg m1 ra &&& ~~~1),
    .cons hs1 (.single hs2), ?_, ?_, ?_, rfl⟩
  · show reg m1 ra &&& ~~~1 = reg m ra &&& ~~~1
    have hra : reg m1 ra = reg m ra := by
      show (if ra.val = 0 then 0 else if ra = a0 then 1 else m.regs ra) = (if ra.val = 0 then 0 else m.regs ra)
      rfl
    rw [hra]
  · show (if a0.val = 0 then 0 else if a0 = a0 then 1 else m.regs a0) = 1
    rfl
  · intro q hq
    show (if q.val = 0 then 0 else if q = a0 then 1 else m.regs q) = (if q.val = 0 then 0 else m.regs q)
    rw [ite_eq_right hq]

theorem romStub_romFn {addr : Word} {pre : Machine → Prop}
    (hlo : 0x40000000 ≤ addr.toNat) (hhi : addr.toNat + 4 ≤ 0x40000540) (hal : addr.toNat % 4 = 0) :
    RomFn 0x40000000 romStub addr 16 pre := by
  intro m hc hpc _ _
  obtain ⟨m', hs, pc', _, hq, hm⟩ := romStub_step m hc hpc hlo hhi hal
  refine ⟨m', hs, pc', fun q hkeep => hq q (by intro h; subst h; exact absurd hkeep (by decide)),
    fun x _ => by rw [hm]⟩

theorem romStub_romRead (flash : Nat → BitVec 8) : RomRead flash 0 0x40000000 romStub := by
  intro m _ _ _ hc hpc _ _ _ _ _ _ _ _
  obtain ⟨m', hs, pc', ha0, hq, hm⟩ := romStub_step m hc hpc (by decide) (by decide) (by decide)
  refine ⟨m', hs, pc', fun q hkeep => hq q (by intro h; subst h; exact absurd hkeep (by decide)),
    fun h0 => absurd (ha0.symm.trans h0) (by decide),
    fun x _ _ => by rw [hm]⟩

/-- Reset memory combining the pinned bootloader image (`imageMem`), the ROM
stub at `0x40000000..0x40000540`, and a valid flash-chip pointer at `bmPtr`. -/
def witnessMem : Word → BitVec 8 :=
  fun x =>
    if 0x40000000 ≤ x.toNat ∧ x.toNat < 0x40000540 then
      BitVec.ofNat 8 (romStubByte (x.toNat - 0x40000000))
    else
      memStore32 imageMem 0x3FCDFFF0 0x3FCDC800 x

theorem loaded_witnessMem : Loaded witnessMem :=
  loaded_imageMem.congr fun x hx => by
    unfold witnessMem
    rw [ite_eq_right (by rcases hx with hx | hx <;> omega)]
    have hp : (0x3FCDFFF0 : Word).toNat = 0x3FCDFFF0 := rfl
    exact memStore32_get_sep (by
      rcases hx with hx | hx
      · exact (sep_of_le (by rw [hp]; omega) (by rw [hp]; omega)).symm
      · exact sep_of_le (by rw [hp]; omega) (by have := x.isLt; omega))

theorem codeIn_witnessMem_rom : CodeIn witnessMem 0x40000000 romStub := by
  intro i hi
  rw [romStub_len] at hi
  rw [romStub_byteAt i hi]
  unfold witnessMem
  have e : ((0x40000000 : Word) + BitVec.ofNat 32 i).toNat = 0x40000000 + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0x40000000 : Word).toNat = 0x40000000 from rfl]; omega
  rw [ite_eq_left ⟨by omega, by omega⟩, e, Nat.add_sub_cancel_left]

theorem witnessMem_bmPtr : memLoad32 witnessMem 0x3FCDFFF0 = 0x3FCDC800 := by
  have h : memLoad32 witnessMem 0x3FCDFFF0 = memLoad32 (memStore32 imageMem 0x3FCDFFF0 0x3FCDC800) 0x3FCDFFF0 :=
    memLoad32_congr fun j hj => by
      unfold witnessMem
      have e : ((0x3FCDFFF0 : Word) + BitVec.ofNat 32 j).toNat = 0x3FCDFFF0 + j := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0x3FCDFFF0 : Word).toNat = 0x3FCDFFF0 from rfl]; omega
      rw [ite_eq_right (by omega)]
  rw [h, memLoad32_store32_same]

/-- **Joint satisfiability of `reset_correct_loaded`'s hypotheses.** There
exist a reset memory `M0`, eFuse contract, ROM code, and stack parameters
that simultaneously satisfy `Loaded M0`, `EfuseCtl efuseProgramRunCode`,
`RomHyp`, and the stack bound. -/
theorem exists_reset_loaded_hyp :
    ∃ (flash : Nat → BitVec 8) (M0 : Word → BitVec 8) (R romStack : Nat)
      (romBase : Word) (romCode : List Nat),
      Loaded M0 ∧
      EfuseCtl efuseProgramRunCode ∧
      RomHyp flash acPinnedRootData Ac.imagePolicy M0 R romStack romBase romCode ∧
      0x3FCC8000 + bmK R romStack 0x5C10 ≤ 0x3FCDC700 := by
  refine ⟨fun _ => 0, witnessMem, 0, 16, 0x40000000, romStub,
    loaded_witnessMem, efuseCtl_plain, ?_, by decide⟩
  exact {
    code := codeIn_witnessMem_rom
    hrb := by decide
    hrl := by rw [romStub_len]; decide
    read := romStub_romRead (fun _ => 0)
    log := romStub_romFn (by decide) (by decide) (by decide)
    unlock := romStub_romFn (by decide) (by decide) (by decide)
    erase := romStub_romFn (by decide) (by decide) (by decide)
    write := romStub_romFn (by decide) (by decide) (by decide)
    suspend := romStub_romFn (by decide) (by decide) (by decide)
    invalidate := romStub_romFn (by decide) (by decide) (by decide)
    resume := romStub_romFn (by decide) (by decide) (by decide)
    hR := by decide
    hrs := by decide
    hrs4 := by decide
    hpa := by rw [witnessMem_bmPtr]; decide
    hpl := by rw [witnessMem_bmPtr]; decide
    hph := by rw [witnessMem_bmPtr]; decide
  }

/-- info: 'C3.Headline.headline_boot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Headline.headline_boot

/-- info: 'C3.Headline.headline_chip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Headline.headline_chip

/-- info: 'C3.Headline.exists_reset_loaded_hyp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.Headline.exists_reset_loaded_hyp

/-- info: 'C3.RV32.Cur.reset_correct_loaded_np' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.reset_correct_loaded_np

/-- info: 'C3.RV32.Cur.reset_correct_loaded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.RV32.Cur.reset_correct_loaded

/-- info: 'C3.efuse_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.efuse_monotone

/-- info: 'C3.rollback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.rollback

/-- info: 'C3.boots_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.boots_safe

/-- info: 'C3.mapped_pages_signed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.mapped_pages_signed

/-- info: 'C3.decodeImageHeader_entryPoint_even' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms C3.decodeImageHeader_entryPoint_even

end C3.Headline
