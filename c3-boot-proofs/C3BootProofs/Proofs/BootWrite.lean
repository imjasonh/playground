import C3BootProofs.Proofs.RomCalls
import C3BootProofs.Proofs.BsDecode
import C3BootProofs.Image.BootloaderData

/-!
# `boot_main`'s boot-state writer, as compiled

`boot_main` passes `write_state` a closure that encodes a `State` and writes
it to the record copy not in use. The compiled closure takes the copy in
`a0` and the state in `a1`: the generation at offset 0, the trial slot at 4
(2 for no trial), the trial boots left at 5, the confirmed bits at 6, and
the preferred slot at 7. It builds the 32-byte record on its stack, packs
it into words, and calls the ROM to unlock the flash, erase the sector,
unlock again, and write the words, then logs a failure through `ets_printf`.

`bwRec` is the record, `bwAddr` the flash address it goes to.
`bootWrite_correct` proves the closure returns with the callee-saved
registers and the memory outside its stack as they were, and that it calls
the ROM's erase on that address's sector and the ROM's write with that
address and those 32 bytes, as the contracts it takes as hypotheses
require.
-/

namespace C3.RV32.Cur

open C3.Image

/-- The flash address of the record copy `write_state` writes: 0x29000 when
the low byte of `copy` is 0, and 0x28000 otherwise. -/
def bwAddr (copy : Word) : Word := if copy &&& 0xFF = 0 then 0x29000 else 0x28000

/-- The record's trial-slot byte: 0xFF for no trial, which the state holds as 2. -/
abbrev bwTrial (M : Word → BitVec 8) (st : Word) : BitVec 8 := if M (st + 4) = 2 then 0xFF else M (st + 4)

/-- The record's boots-left byte: 0 with no trial. -/
abbrev bwBoots (M : Word → BitVec 8) (st : Word) : BitVec 8 := if M (st + 4) = 2 then 0 else M (st + 5)

/-- Byte `i` of the record body that `encode` makes from the state at `st`:
the magic `C3BS`, version 1, two reserved bytes, the generation, the
preferred slot, the trial slot, the boots left, the confirmed bits, and
twelve reserved bytes. -/
def bwBody (M : Word → BitVec 8) (st : Word) (i : Nat) : BitVec 8 :=
  if i = 0 then 0x43 else if i = 1 then 0x33 else if i = 2 then 0x42 else if i = 3 then 0x53
  else if i = 4 then 1 else if i < 8 then 0
  else if i < 12 then (memLoad32 M st).extractLsb' (8 * (i - 8)) 8
  else if i = 12 then M (st + 7) else if i = 13 then bwTrial M st else if i = 14 then bwBoots M st
  else if i = 15 then M (st + 6) else 0

/-- The record's checksum: CRC-32 over the 28 body bytes. -/
def bwCrc (M : Word → BitVec 8) (st : Word) : Word := crcBits ((List.range 28).map (bwBody M st))

/-- Byte `i` of the 32-byte record: the body, then the checksum, least
significant byte first. -/
def bwRec (M : Word → BitVec 8) (st : Word) (i : Nat) : BitVec 8 :=
  if i < 28 then bwBody M st i else (bwCrc M st).extractLsb' (8 * (i - 28)) 8

/-- Where the image puts the closure. -/
abbrev BW : Word := BitVec.ofNat 32 bootMainClosure1Address

/-- The functions and data the closure uses, where the image puts them. -/
structure BWCode (M : Word → BitVec 8) : Prop where
  self : CodeIn M BW bootMainClosure1Code
  memset : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode
  copy : CodeIn M (BitVec.ofNat 32 copyFromSliceU8Address) copyFromSliceU8Code
  stub : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  body : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  crc : CodeIn M (BitVec.ofNat 32 crc32Address) crc32Code
  magic : CodeIn M (BitVec.ofNat 32 bsMagicAddress) bsMagicData
  version : CodeIn M (BitVec.ofNat 32 bsVersionAddress) bsVersionData


/-! ## Reading frame memory at literal offsets

The closure's stores and copies all sit at literal offsets from the frame
base. These lemmas read memory at a literal offset past one such write; the
side conditions are about literals, so `decide` discharges them. -/

theorem ofNat_toNat_w (x : Word) : BitVec.ofNat 32 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])

theorem ld_st32_off {M : Word → BitVec 8} {b v c d : Word}
    (h : (c.toNat + 4 ≤ d.toNat ∨ d.toNat + 4 ≤ c.toNat) ∧ c.toNat + 4 ≤ 2 ^ 32 ∧ d.toNat + 4 ≤ 2 ^ 32) :
    memLoad32 (memStore32 M (b + c) v) (b + d) = memLoad32 M (b + d) := by
  have := memLoad32_store32_sep (M := M) (v := v) (sep_offsets b h.1 h.2.1 h.2.2)
  rwa [ofNat_toNat_w, ofNat_toNat_w] at this

theorem ld_st8_off {M : Word → BitVec 8} {b c d : Word} {v : BitVec 8}
    (h : (c.toNat + 1 ≤ d.toNat ∨ d.toNat + 4 ≤ c.toNat) ∧ c.toNat + 1 ≤ 2 ^ 32 ∧ d.toNat + 4 ≤ 2 ^ 32) :
    memLoad32 (memStore8 M (b + c) v) (b + d) = memLoad32 M (b + d) := by
  have := memLoad32_store8_sep (M := M) (v := v) (sep_offsets b h.1 h.2.1 h.2.2)
  rwa [ofNat_toNat_w, ofNat_toNat_w] at this

theorem get_st32_off {M : Word → BitVec 8} {b v c d : Word}
    (h : (c.toNat + 4 ≤ d.toNat ∨ d.toNat + 1 ≤ c.toNat) ∧ c.toNat + 4 ≤ 2 ^ 32 ∧ d.toNat + 1 ≤ 2 ^ 32) :
    memStore32 M (b + c) v (b + d) = M (b + d) := by
  have := memStore32_get_sep (M := M) (v := v) (sep_offsets b h.1 h.2.1 h.2.2)
  rwa [ofNat_toNat_w, ofNat_toNat_w] at this

theorem get_st8_off {M : Word → BitVec 8} {b c d : Word} {v : BitVec 8} (h : c ≠ d) :
    memStore8 M (b + c) v (b + d) = M (b + d) :=
  memStore8_ne fun e => h (by
    have := congrArg (· - b) e
    rw [BitVec.add_comm b d, BitVec.add_comm b c, BitVec.add_sub_cancel, BitVec.add_sub_cancel] at this
    exact this.symm)

theorem and_ff32 (x : Word) : x &&& 0xFFFFFFFF = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and]
  by_cases h : i < 32
  · have hf : ∀ j, j < 32 → Nat.testBit 4294967295 j = true := by decide
    rw [hf i h, Bool.and_true]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega))),
      Bool.false_and]

theorem sub_add_add (b c d : Word) : b + d - (b + c) = d - c := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add]
  have := b.isLt; have := c.isLt; have := d.isLt
  omega

theorem get_fill {M : Word → BitVec 8} {b d : Word} {v : BitVec 8} {n : Nat} :
    fillBytes M b v n (b + d) = if d.toNat < n then v else M (b + d) := by
  unfold fillBytes; rw [BitVec.add_comm b d, BitVec.add_sub_cancel]

theorem get_copy {M : Word → BitVec 8} {b c d src : Word} {k : Nat} :
    copyBytes M (b + c) src k (b + d) = if (d - c).toNat < k then M (src + (d - c)) else M (b + d) := by
  unfold copyBytes; rw [sub_add_add]

theorem add_ne_add {a : Word} {j k : Nat} (h : j ≠ k) (hj : j < 4) (hk : k < 4) :
    a + BitVec.ofNat 32 j ≠ a + BitVec.ofNat 32 k := add_ofNat_ne a (by omega) (by omega) h

theorem st32_at0 (M : Word → BitVec 8) (a v : Word) : memStore32 M a v a = v.extractLsb' 0 8 := by
  have h : ∀ k, 0 < k → k < 4 → a ≠ a + BitVec.ofNat 32 k := fun k h1 h2 => by
    have := add_ne_add (a := a) (j := 0) (k := k) (by omega) (by omega) h2
    rwa [add_ofNat_zero] at this
  unfold memStore32
  rw [memStore8_ne (a := a + 3) (x := a) (h 3 (by decide) (by decide)),
    memStore8_ne (a := a + 2) (x := a) (h 2 (by decide) (by decide)),
    memStore8_ne (a := a + 1) (x := a) (h 1 (by decide) (by decide)), memStore8_same]

theorem st32_at1 (M : Word → BitVec 8) (a v : Word) : memStore32 M a v (a + 1) = v.extractLsb' 8 8 := by
  unfold memStore32
  rw [memStore8_ne (a := a + 3) (x := a + 1) (add_ne_add (j := 1) (k := 3) (by decide) (by decide) (by decide)),
    memStore8_ne (a := a + 2) (x := a + 1) (add_ne_add (j := 1) (k := 2) (by decide) (by decide) (by decide)),
    memStore8_same]

theorem st32_at2 (M : Word → BitVec 8) (a v : Word) : memStore32 M a v (a + 2) = v.extractLsb' 16 8 := by
  unfold memStore32
  rw [memStore8_ne (a := a + 3) (x := a + 2) (add_ne_add (j := 2) (k := 3) (by decide) (by decide) (by decide)),
    memStore8_same]

theorem st32_at3 (M : Word → BitVec 8) (a v : Word) : memStore32 M a v (a + 3) = v.extractLsb' 24 8 := by
  unfold memStore32; rw [memStore8_same]

theorem get_st32_j {M : Word → BitVec 8} {b v c d : Word} (j : Nat) (hj : j < 4) (h : d = c + BitVec.ofNat 32 j) :
    memStore32 M (b + c) v (b + d) = v.extractLsb' (8 * j) 8 := by
  rw [h, ← BitVec.add_assoc]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · rw [add_ofNat_zero]; exact st32_at0 _ _ _
  · exact st32_at1 _ _ _
  · exact st32_at2 _ _ _
  · exact st32_at3 _ _ _


/-- The closure from 0x48 to 0xB4: the state's fields copied to the stack and
the table of the six fields `encode` copies. -/
def bwBlk : List BInstr :=
  [.lw a3 (9 : Fin 32) 0x0,
   .lbu a4 (9 : Fin 32) 0x7,
   .lbu a5 (9 : Fin 32) 0x6,
   .sb sp a2 0x26,
   .lui a2 0x3FCC4000,
   .aluImm .add a2 a2 0x75E,
   .sw sp a3 0x20,
   .aluImm .add (9 : Fin 32) sp 0x38,
   .sb sp a4 0x24,
   .sb sp a1 0x25,
   .sb sp a5 0x27,
   .aluImm .add a1 x0 0x4,
   .sw sp x0 0x30,
   .sw sp a2 0x34,
   .sw sp a1 0x38,
   .sw sp a1 0x3C,
   .lui a2 0x3FCC4000,
   .aluImm .add a2 a2 0x6B6,
   .aluImm .add a3 x0 0x8,
   .aluImm .add a4 sp 0x20,
   .sw sp a2 0x40,
   .sw sp a0 0x44,
   .sw sp a3 0x48,
   .sw sp a4 0x4C,
   .aluImm .add a2 x0 0xC,
   .aluImm .add a3 sp 0x24,
   .sw sp a1 0x50,
   .sw sp a2 0x54,
   .sw sp a3 0x58,
   .sw sp a0 0x5C,
   .aluImm .add a0 x0 0xE,
   .aluImm .add a1 sp 0x26,
   .aluImm .add a2 x0 0x1,
   .aluImm .add a3 x0 0xF,
   .aluImm .add a4 sp 0x27,
   .sw sp a0 0x60,
   .sw sp a1 0x64,
   .sw sp a2 0x68,
   .sw sp a3 0x6C,
   .sw sp a4 0x70,
   .sw sp a2 0x74,
   .aluImm .add (8 : Fin 32) x0 0x6]

set_option maxRecDepth 20000 in
theorem bwBlk_end : blockEnd bootMainClosure1Code 0x48 bwBlk = some 0xB4 := by decide

section
set_option maxRecDepth 20000
theorem bw_at_0 : fetchRel bootMainClosure1Code 0x0 = some (.aluImm .add sp sp 0xFFFFFF70, 2) := by decide
theorem bw_at_2 : fetchRel bootMainClosure1Code 0x2 = some (.store .sw sp ra 0x8C, 2) := by decide
theorem bw_at_4 : fetchRel bootMainClosure1Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x88, 2) := by decide
theorem bw_at_6 : fetchRel bootMainClosure1Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x84, 2) := by decide
theorem bw_at_8 : fetchRel bootMainClosure1Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x80, 2) := by decide
theorem bw_at_a : fetchRel bootMainClosure1Code 0xA = some (.store .sw sp (19 : Fin 32) 0x7C, 2) := by decide
theorem bw_at_c : fetchRel bootMainClosure1Code 0xC = some (.store .sw sp (20 : Fin 32) 0x78, 2) := by decide
theorem bw_at_e : fetchRel bootMainClosure1Code 0xE = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem bw_at_10 : fetchRel bootMainClosure1Code 0x10 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem bw_at_12 : fetchRel bootMainClosure1Code 0x12 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem bw_at_14 : fetchRel bootMainClosure1Code 0x14 = some (.alu .add a0 x0 sp, 2) := by decide
theorem bw_at_16 : fetchRel bootMainClosure1Code 0x16 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem bw_at_1a : fetchRel bootMainClosure1Code 0x1A = some (.alu .add (19 : Fin 32) x0 sp, 2) := by decide
theorem bw_at_1c : fetchRel bootMainClosure1Code 0x1C = some (.aluImm .add (20 : Fin 32) x0 0x20, 4) := by decide
theorem bw_at_20 : fetchRel bootMainClosure1Code 0x20 = some (.auipc ra 0x15000, 4) := by decide
theorem bw_at_24 : fetchRel bootMainClosure1Code 0x24 = some (.jalr ra ra 0xFFFFFB8E, 4) := by decide
theorem bw_at_28 : fetchRel bootMainClosure1Code 0x28 = some (.load .lbu a1 (9 : Fin 32) 0x4, 4) := by decide
theorem bw_at_2c : fetchRel bootMainClosure1Code 0x2C = some (.load .lbu a2 (9 : Fin 32) 0x5, 4) := by decide
theorem bw_at_30 : fetchRel bootMainClosure1Code 0x30 = some (.aluImm .add a0 a1 0xFFFFFFFE, 4) := by decide
theorem bw_at_34 : fetchRel bootMainClosure1Code 0x34 = some (.aluImm .sltu a0 a0 0x1, 4) := by decide
theorem bw_at_38 : fetchRel bootMainClosure1Code 0x38 = some (.aluImm .add a3 a0 0xFFFFFFFF, 4) := by decide
theorem bw_at_3c : fetchRel bootMainClosure1Code 0x3C = some (.aluImm .add a0 x0 0x2, 2) := by decide
theorem bw_at_3e : fetchRel bootMainClosure1Code 0x3E = some (.alu .and a2 a2 a3, 2) := by decide
theorem bw_at_40 : fetchRel bootMainClosure1Code 0x40 = some (.branch .bne a1 a0 0x8, 4) := by decide
theorem bw_at_44 : fetchRel bootMainClosure1Code 0x44 = some (.aluImm .add a1 x0 0xFF, 4) := by decide
theorem bw_at_48 : fetchRel bootMainClosure1Code 0x48 = some (.load .lw a3 (9 : Fin 32) 0x0, 2) := by decide
theorem bw_at_4a : fetchRel bootMainClosure1Code 0x4A = some (.load .lbu a4 (9 : Fin 32) 0x7, 4) := by decide
theorem bw_at_4e : fetchRel bootMainClosure1Code 0x4E = some (.load .lbu a5 (9 : Fin 32) 0x6, 4) := by decide
theorem bw_at_52 : fetchRel bootMainClosure1Code 0x52 = some (.store .sb sp a2 0x26, 4) := by decide
theorem bw_at_56 : fetchRel bootMainClosure1Code 0x56 = some (.lui a2 0x3FCC4000, 4) := by decide
theorem bw_at_5a : fetchRel bootMainClosure1Code 0x5A = some (.aluImm .add a2 a2 0x75E, 4) := by decide
theorem bw_at_5e : fetchRel bootMainClosure1Code 0x5E = some (.store .sw sp a3 0x20, 2) := by decide
theorem bw_at_60 : fetchRel bootMainClosure1Code 0x60 = some (.aluImm .add (9 : Fin 32) sp 0x38, 2) := by decide
theorem bw_at_62 : fetchRel bootMainClosure1Code 0x62 = some (.store .sb sp a4 0x24, 4) := by decide
theorem bw_at_66 : fetchRel bootMainClosure1Code 0x66 = some (.store .sb sp a1 0x25, 4) := by decide
theorem bw_at_6a : fetchRel bootMainClosure1Code 0x6A = some (.store .sb sp a5 0x27, 4) := by decide
theorem bw_at_6e : fetchRel bootMainClosure1Code 0x6E = some (.aluImm .add a1 x0 0x4, 2) := by decide
theorem bw_at_70 : fetchRel bootMainClosure1Code 0x70 = some (.store .sw sp x0 0x30, 2) := by decide
theorem bw_at_72 : fetchRel bootMainClosure1Code 0x72 = some (.store .sw sp a2 0x34, 2) := by decide
theorem bw_at_74 : fetchRel bootMainClosure1Code 0x74 = some (.store .sw sp a1 0x38, 2) := by decide
theorem bw_at_76 : fetchRel bootMainClosure1Code 0x76 = some (.store .sw sp a1 0x3C, 2) := by decide
theorem bw_at_78 : fetchRel bootMainClosure1Code 0x78 = some (.lui a2 0x3FCC4000, 4) := by decide
theorem bw_at_7c : fetchRel bootMainClosure1Code 0x7C = some (.aluImm .add a2 a2 0x6B6, 4) := by decide
theorem bw_at_80 : fetchRel bootMainClosure1Code 0x80 = some (.aluImm .add a3 x0 0x8, 2) := by decide
theorem bw_at_82 : fetchRel bootMainClosure1Code 0x82 = some (.aluImm .add a4 sp 0x20, 2) := by decide
theorem bw_at_84 : fetchRel bootMainClosure1Code 0x84 = some (.store .sw sp a2 0x40, 2) := by decide
theorem bw_at_86 : fetchRel bootMainClosure1Code 0x86 = some (.store .sw sp a0 0x44, 2) := by decide
theorem bw_at_88 : fetchRel bootMainClosure1Code 0x88 = some (.store .sw sp a3 0x48, 2) := by decide
theorem bw_at_8a : fetchRel bootMainClosure1Code 0x8A = some (.store .sw sp a4 0x4C, 2) := by decide
theorem bw_at_8c : fetchRel bootMainClosure1Code 0x8C = some (.aluImm .add a2 x0 0xC, 2) := by decide
theorem bw_at_8e : fetchRel bootMainClosure1Code 0x8E = some (.aluImm .add a3 sp 0x24, 2) := by decide
theorem bw_at_90 : fetchRel bootMainClosure1Code 0x90 = some (.store .sw sp a1 0x50, 2) := by decide
theorem bw_at_92 : fetchRel bootMainClosure1Code 0x92 = some (.store .sw sp a2 0x54, 2) := by decide
theorem bw_at_94 : fetchRel bootMainClosure1Code 0x94 = some (.store .sw sp a3 0x58, 2) := by decide
theorem bw_at_96 : fetchRel bootMainClosure1Code 0x96 = some (.store .sw sp a0 0x5C, 2) := by decide
theorem bw_at_98 : fetchRel bootMainClosure1Code 0x98 = some (.aluImm .add a0 x0 0xE, 2) := by decide
theorem bw_at_9a : fetchRel bootMainClosure1Code 0x9A = some (.aluImm .add a1 sp 0x26, 4) := by decide
theorem bw_at_9e : fetchRel bootMainClosure1Code 0x9E = some (.aluImm .add a2 x0 0x1, 2) := by decide
theorem bw_at_a0 : fetchRel bootMainClosure1Code 0xA0 = some (.aluImm .add a3 x0 0xF, 2) := by decide
theorem bw_at_a2 : fetchRel bootMainClosure1Code 0xA2 = some (.aluImm .add a4 sp 0x27, 4) := by decide
theorem bw_at_a6 : fetchRel bootMainClosure1Code 0xA6 = some (.store .sw sp a0 0x60, 2) := by decide
theorem bw_at_a8 : fetchRel bootMainClosure1Code 0xA8 = some (.store .sw sp a1 0x64, 2) := by decide
theorem bw_at_aa : fetchRel bootMainClosure1Code 0xAA = some (.store .sw sp a2 0x68, 2) := by decide
theorem bw_at_ac : fetchRel bootMainClosure1Code 0xAC = some (.store .sw sp a3 0x6C, 2) := by decide
theorem bw_at_ae : fetchRel bootMainClosure1Code 0xAE = some (.store .sw sp a4 0x70, 2) := by decide
theorem bw_at_b0 : fetchRel bootMainClosure1Code 0xB0 = some (.store .sw sp a2 0x74, 2) := by decide
theorem bw_at_b2 : fetchRel bootMainClosure1Code 0xB2 = some (.aluImm .add (8 : Fin 32) x0 0x6, 2) := by decide
theorem bw_at_b4 : fetchRel bootMainClosure1Code 0xB4 = some (.branch .beq (8 : Fin 32) x0 0x36, 2) := by decide
theorem bw_at_b6 : fetchRel bootMainClosure1Code 0xB6 = some (.load .lw a2 (9 : Fin 32) 0xFFFFFFFC, 4) := by decide
theorem bw_at_ba : fetchRel bootMainClosure1Code 0xBA = some (.branch .beq a2 x0 0x30, 2) := by decide
theorem bw_at_bc : fetchRel bootMainClosure1Code 0xBC = some (.load .lw a1 (9 : Fin 32) 0xFFFFFFF8, 4) := by decide
theorem bw_at_c0 : fetchRel bootMainClosure1Code 0xC0 = some (.load .lw a3 (9 : Fin 32) 0x0, 2) := by decide
theorem bw_at_c2 : fetchRel bootMainClosure1Code 0xC2 = some (.alu .add a0 a1 a3, 4) := by decide
theorem bw_at_c6 : fetchRel bootMainClosure1Code 0xC6 = some (.alu .sltu a4 a0 a1, 4) := by decide
theorem bw_at_ca : fetchRel bootMainClosure1Code 0xCA = some (.alu .sub a4 x0 a4, 4) := by decide
theorem bw_at_ce : fetchRel bootMainClosure1Code 0xCE = some (.alu .or a4 a4 a0, 2) := by decide
theorem bw_at_d0 : fetchRel bootMainClosure1Code 0xD0 = some (.branch .bltu (20 : Fin 32) a4 0x14, 4) := by decide
theorem bw_at_d4 : fetchRel bootMainClosure1Code 0xD4 = some (.alu .add a0 (19 : Fin 32) a1, 4) := by decide
theorem bw_at_d8 : fetchRel bootMainClosure1Code 0xD8 = some (.alu .sub a1 a4 a1, 4) := by decide
theorem bw_at_dc : fetchRel bootMainClosure1Code 0xDC = some (.auipc ra 0xD000, 4) := by decide
theorem bw_at_e0 : fetchRel bootMainClosure1Code 0xE0 = some (.jalr ra ra 0x51C, 4) := by decide
theorem bw_at_e4 : fetchRel bootMainClosure1Code 0xE4 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xC, 2) := by decide
theorem bw_at_e6 : fetchRel bootMainClosure1Code 0xE6 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem bw_at_e8 : fetchRel bootMainClosure1Code 0xE8 = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFCE, 2) := by decide
theorem bw_at_ea : fetchRel bootMainClosure1Code 0xEA = some (.alu .add a0 x0 sp, 2) := by decide
theorem bw_at_ec : fetchRel bootMainClosure1Code 0xEC = some (.alu .add (8 : Fin 32) x0 sp, 2) := by decide
theorem bw_at_ee : fetchRel bootMainClosure1Code 0xEE = some (.auipc ra 0xD000, 4) := by decide
theorem bw_at_f2 : fetchRel bootMainClosure1Code 0xF2 = some (.jalr ra ra 0x4CE, 4) := by decide
theorem bw_at_f6 : fetchRel bootMainClosure1Code 0xF6 = some (.aluImm .srl a1 a0 0x18, 4) := by decide
theorem bw_at_fa : fetchRel bootMainClosure1Code 0xFA = some (.aluImm .srl a2 a0 0x10, 4) := by decide
theorem bw_at_fe : fetchRel bootMainClosure1Code 0xFE = some (.aluImm .srl a3 a0 0x8, 4) := by decide
theorem bw_at_102 : fetchRel bootMainClosure1Code 0x102 = some (.store .sb sp a0 0x1C, 4) := by decide
theorem bw_at_106 : fetchRel bootMainClosure1Code 0x106 = some (.store .sb sp a3 0x1D, 4) := by decide
theorem bw_at_10a : fetchRel bootMainClosure1Code 0x10A = some (.store .sb sp a2 0x1E, 4) := by decide
theorem bw_at_10e : fetchRel bootMainClosure1Code 0x10E = some (.store .sb sp a1 0x1F, 4) := by decide
theorem bw_at_112 : fetchRel bootMainClosure1Code 0x112 = some (.aluImm .add a0 sp 0x28, 2) := by decide
theorem bw_at_114 : fetchRel bootMainClosure1Code 0x114 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem bw_at_118 : fetchRel bootMainClosure1Code 0x118 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem bw_at_11a : fetchRel bootMainClosure1Code 0x11A = some (.aluImm .add (9 : Fin 32) sp 0x28, 2) := by decide
theorem bw_at_11c : fetchRel bootMainClosure1Code 0x11C = some (.auipc ra 0x15000, 4) := by decide
theorem bw_at_120 : fetchRel bootMainClosure1Code 0x120 = some (.jalr ra ra 0xFFFFFA92, 4) := by decide
theorem bw_at_124 : fetchRel bootMainClosure1Code 0x124 = some (.aluImm .add a0 x0 0x8, 2) := by decide
theorem bw_at_126 : fetchRel bootMainClosure1Code 0x126 = some (.branch .beq a0 x0 0x28, 2) := by decide
theorem bw_at_128 : fetchRel bootMainClosure1Code 0x128 = some (.load .lbu a1 (8 : Fin 32) 0x1, 4) := by decide
theorem bw_at_12c : fetchRel bootMainClosure1Code 0x12C = some (.load .lbu a2 (8 : Fin 32) 0x2, 4) := by decide
theorem bw_at_130 : fetchRel bootMainClosure1Code 0x130 = some (.load .lbu a3 (8 : Fin 32) 0x3, 4) := by decide
theorem bw_at_134 : fetchRel bootMainClosure1Code 0x134 = some (.load .lbu a4 (8 : Fin 32) 0x0, 4) := by decide
theorem bw_at_138 : fetchRel bootMainClosure1Code 0x138 = some (.aluImm .sll a1 a1 0x8, 2) := by decide
theorem bw_at_13a : fetchRel bootMainClosure1Code 0x13A = some (.aluImm .sll a2 a2 0x10, 2) := by decide
theorem bw_at_13c : fetchRel bootMainClosure1Code 0x13C = some (.aluImm .sll a3 a3 0x18, 2) := by decide
theorem bw_at_13e : fetchRel bootMainClosure1Code 0x13E = some (.alu .or a1 a1 a4, 2) := by decide
theorem bw_at_140 : fetchRel bootMainClosure1Code 0x140 = some (.alu .or a2 a2 a3, 2) := by decide
theorem bw_at_142 : fetchRel bootMainClosure1Code 0x142 = some (.alu .or a1 a1 a2, 2) := by decide
theorem bw_at_144 : fetchRel bootMainClosure1Code 0x144 = some (.store .sw (9 : Fin 32) a1 0x0, 2) := by decide
theorem bw_at_146 : fetchRel bootMainClosure1Code 0x146 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem bw_at_148 : fetchRel bootMainClosure1Code 0x148 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem bw_at_14a : fetchRel bootMainClosure1Code 0x14A = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem bw_at_14c : fetchRel bootMainClosure1Code 0x14C = some (.branch .bne a0 x0 0xFFFFFFDC, 2) := by decide
theorem bw_at_14e : fetchRel bootMainClosure1Code 0x14E = some (.aluImm .and a0 (18 : Fin 32) 0xFF, 4) := by decide
theorem bw_at_152 : fetchRel bootMainClosure1Code 0x152 = some (.lui (8 : Fin 32) 0x29000, 4) := by decide
theorem bw_at_156 : fetchRel bootMainClosure1Code 0x156 = some (.branch .beq a0 x0 0x6, 2) := by decide
theorem bw_at_158 : fetchRel bootMainClosure1Code 0x158 = some (.lui (8 : Fin 32) 0x28000, 4) := by decide
theorem bw_at_15c : fetchRel bootMainClosure1Code 0x15C = some (.auipc ra 0xFFC5E000, 4) := by decide
theorem bw_at_160 : fetchRel bootMainClosure1Code 0x160 = some (.jalr ra ra 0x43E, 4) := by decide
theorem bw_at_164 : fetchRel bootMainClosure1Code 0x164 = some (.branch .bne a0 x0 0x2C, 2) := by decide
theorem bw_at_166 : fetchRel bootMainClosure1Code 0x166 = some (.aluImm .srl a0 (8 : Fin 32) 0xC, 4) := by decide
theorem bw_at_16a : fetchRel bootMainClosure1Code 0x16A = some (.auipc ra 0xFFC5E000, 4) := by decide
theorem bw_at_16e : fetchRel bootMainClosure1Code 0x16E = some (.jalr ra ra 0x418, 4) := by decide
theorem bw_at_172 : fetchRel bootMainClosure1Code 0x172 = some (.branch .bne a0 x0 0x1E, 2) := by decide
theorem bw_at_174 : fetchRel bootMainClosure1Code 0x174 = some (.auipc ra 0xFFC5E000, 4) := by decide
theorem bw_at_178 : fetchRel bootMainClosure1Code 0x178 = some (.jalr ra ra 0x426, 4) := by decide
theorem bw_at_17c : fetchRel bootMainClosure1Code 0x17C = some (.branch .bne a0 x0 0x14, 2) := by decide
theorem bw_at_17e : fetchRel bootMainClosure1Code 0x17E = some (.aluImm .add a1 sp 0x28, 2) := by decide
theorem bw_at_180 : fetchRel bootMainClosure1Code 0x180 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem bw_at_184 : fetchRel bootMainClosure1Code 0x184 = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem bw_at_186 : fetchRel bootMainClosure1Code 0x186 = some (.auipc ra 0xFFC5E000, 4) := by decide
theorem bw_at_18a : fetchRel bootMainClosure1Code 0x18A = some (.jalr ra ra 0x400, 4) := by decide
theorem bw_at_18e : fetchRel bootMainClosure1Code 0x18E = some (.branch .beq a0 x0 0x14, 2) := by decide
theorem bw_at_190 : fetchRel bootMainClosure1Code 0x190 = some (.lui a0 0x3FCC6000, 4) := by decide
theorem bw_at_194 : fetchRel bootMainClosure1Code 0x194 = some (.aluImm .add a0 a0 0x671, 4) := by decide
theorem bw_at_198 : fetchRel bootMainClosure1Code 0x198 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem bw_at_19a : fetchRel bootMainClosure1Code 0x19A = some (.auipc ra 0xFFC5E000, 4) := by decide
theorem bw_at_19e : fetchRel bootMainClosure1Code 0x19E = some (.jalr ra ra 0x300, 4) := by decide
theorem bw_at_1a2 : fetchRel bootMainClosure1Code 0x1A2 = some (.load .lw ra sp 0x8C, 2) := by decide
theorem bw_at_1a4 : fetchRel bootMainClosure1Code 0x1A4 = some (.load .lw (8 : Fin 32) sp 0x88, 2) := by decide
theorem bw_at_1a6 : fetchRel bootMainClosure1Code 0x1A6 = some (.load .lw (9 : Fin 32) sp 0x84, 2) := by decide
theorem bw_at_1a8 : fetchRel bootMainClosure1Code 0x1A8 = some (.load .lw (18 : Fin 32) sp 0x80, 2) := by decide
theorem bw_at_1aa : fetchRel bootMainClosure1Code 0x1AA = some (.load .lw (19 : Fin 32) sp 0x7C, 2) := by decide
theorem bw_at_1ac : fetchRel bootMainClosure1Code 0x1AC = some (.load .lw (20 : Fin 32) sp 0x78, 2) := by decide
theorem bw_at_1ae : fetchRel bootMainClosure1Code 0x1AE = some (.aluImm .add sp sp 0x90, 2) := by decide
theorem bw_at_1b0 : fetchRel bootMainClosure1Code 0x1B0 = some (.jalr x0 ra 0x0, 2) := by decide
end

theorem ult_ofNat_false {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    (BitVec.ofNat 32 a).ult (BitVec.ofNat 32 b) = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : b < 2 ^ 32)]
  exact decide_eq_false (by omega)

theorem ofNat_add_neg {c d : Nat} (h : d ≤ c) (hc : c < 2 ^ 32) (w : Word) (hw : w.toNat = 2 ^ 32 - d) :
    BitVec.ofNat 32 c + w = BitVec.ofNat 32 (c - d) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hw, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt (by omega : c - d < 2 ^ 32)]
  omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- One iteration of the closure's field loop, from 0xB6 to the `bnez` at
0xE8: entry `k` of the table at `G + 0x30` says to copy `len` bytes from
`ptr` to offset `at` of the record at `G`, and `copy_from_slice` does. -/
theorem bw_field {Mx : Word → BitVec 8} {G ptr : Word} {n : Machine} {g : Fin 32 → Word} {k off len : Nat}
    (s : St Mx BW n 0xB6 g) (hc : CodeIn Mx BW bootMainClosure1Code)
    (hcp : CodeIn Mx (BitVec.ofNat 32 copyFromSliceU8Address) copyFromSliceU8Code)
    (hcs : CodeIn Mx (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode)
    (hcb : CodeIn Mx (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode)
    (hsp : g sp = G) (h9 : g 9 = G + BitVec.ofNat 32 (0x38 + 12 * k)) (h19 : g 19 = G) (h20 : g 20 = 0x20)
    (hG : G.toNat % 4 = 0) (hGl : 16 ≤ G.toNat) (hGh : G.toNat + 0x90 ≤ 0x40000000) (hk : k < 6)
    (hat : memLoad32 Mx (G + BitVec.ofNat 32 (0x30 + 12 * k)) = BitVec.ofNat 32 off)
    (hptr : memLoad32 Mx (G + BitVec.ofNat 32 (0x34 + 12 * k)) = ptr)
    (hlen : memLoad32 Mx (G + BitVec.ofNat 32 (0x38 + 12 * k)) = BitVec.ofNat 32 len)
    (hal : off + len ≤ 32) (hp0 : ptr ≠ 0)
    (sD : Sep (G + BitVec.ofNat 32 off) len ptr len) (sS : Sep ptr len (G + 0xFFFFFFF0) 16)
    (hpw : ptr.toNat + len < 2 ^ 32) :
    ∃ n', Steps n n' ∧ St n'.mem BW n' 0xE8 (reg n') ∧
      (∀ x, Sep (G + 0xFFFFFFF0) 16 x 1 → n'.mem x = copyBytes Mx (G + BitVec.ofNat 32 off) ptr len x) ∧
      reg n' sp = G ∧ reg n' 9 = G + BitVec.ofNat 32 (0x38 + 12 * (k + 1)) ∧ reg n' 8 = g 8 + 0xFFFFFFFF ∧
      reg n' 19 = G ∧ reg n' 20 = 0x20 ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
        r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ ra → r ≠ 8 → r ≠ 9 →
        reg n' r = g r := by
  have hz := s.zero
  have ea : g 9 + 0xFFFFFFFC = G + BitVec.ofNat 32 (0x34 + 12 * k) := by
    rw [h9, BitVec.add_assoc, ofNat_add_neg (d := 4) (by omega) (by omega) _ rfl]
    congr 2; omega
  have eb : g 9 + 0xFFFFFFF8 = G + BitVec.ofNat 32 (0x30 + 12 * k) := by
    rw [h9, BitVec.add_assoc, ofNat_add_neg (d := 8) (by omega) (by omega) _ rfl]
    congr 2; omega
  have al : ∀ c, c % 4 = 0 → (G + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h => aligned_add hG h
  obtain ⟨n1, d1, u1⟩ := s.lw hc bw_at_b6 (off' := 0xBA) (by decide) (by rw [ea]; exact al _ (by omega))
  rw [ea, hptr] at u1
  have v1 := u1.self
  obtain ⟨n2, d2, u2⟩ := v1.notTaken hc 0xBC bw_at_ba (by decide)
    (by
      show (reg n1 a2 == reg n1 x0) = false
      rw [u1.regs, u1.regs]; simp +decide only [upd, ite_true, ite_false]
      exact beq_eq_false_iff_ne.mpr hp0)
  have q2 : ∀ r, reg n2 r = reg n1 r := u2.regs
  have r1 : ∀ r, r ≠ a2 → reg n1 r = g r := fun r h => by rw [u1.regs]; exact updz hz h
  have p1 : reg n1 a2 = ptr := by rw [u1.regs]; simp +decide only [upd, ite_true, ite_false]
  obtain ⟨n3, d3, u3⟩ := u2.lw hc bw_at_bc (off' := 0xC0) (by decide)
    (by rw [r1 9 (by decide), eb]; exact al _ (by omega))
  rw [r1 9 (by decide), eb, hat] at u3
  have v3 := u3.self
  obtain ⟨n4, d4, u4⟩ := v3.lw hc bw_at_c0 (off' := 0xC2) (by decide)
    (by
      rw [u3.regs, updz v1.zero (by decide), r1 9 (by decide), h9, add_lit_zero]; exact al _ (by omega))
  rw [u3.regs, updz v1.zero (by decide), r1 9 (by decide), h9, add_lit_zero, hlen] at u4
  have v4 := u4.self
  obtain ⟨n5, d5, u5⟩ := v4.alu hc bw_at_c2 (off' := 0xC6) (by decide)
  have v5 := u5.self
  obtain ⟨n6, d6, u6⟩ := v5.alu hc bw_at_c6 (off' := 0xCA) (by decide)
  have v6 := u6.self
  obtain ⟨n7, d7, u7⟩ := v6.alu hc bw_at_ca (off' := 0xCE) (by decide)
  have v7 := u7.self
  obtain ⟨n8, d8, u8⟩ := v7.alu hc bw_at_ce (off' := 0xD0) (by decide)
  have v8 := u8.self
  have a1_8 : reg n8 a1 = BitVec.ofNat 32 off := by
    simp +decide only [u8.regs, u7.regs, u6.regs, u5.regs, u4.regs, upd, ite_true, ite_false]
    rw [u3.regs]; simp +decide only [upd, ite_true, ite_false]
  have e8 : reg n8 a4 = BitVec.ofNat 32 (off + len) := by
    simp +decide only [u8.regs, u7.regs, u6.regs, u5.regs, u4.regs, upd, ite_true, ite_false]
    rw [u3.regs]; simp +decide only [upd, ite_true, ite_false, aluEval]
    rw [ofNat_add_ofNat, ult_ofNat_false (by omega) (by omega)]
    simp only [Bool.false_eq_true, ite_false]
    rw [BitVec.sub_self, BitVec.zero_or]
  have r8 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a3 → r ≠ a4 → reg n8 r = reg n1 r := fun r h0 h1 h3 h4 => by
    rw [u8.regs, updz v7.zero h4, u7.regs, updz v6.zero h4, u6.regs, updz v5.zero h4, u5.regs, updz v4.zero h0,
      u4.regs, updz v3.zero h3, u3.regs, updz v1.zero h1]
  obtain ⟨n9, d9, u9⟩ := v8.notTaken hc 0xD4 bw_at_d0 (by decide)
    (by
      rw [e8, r8 20 (by decide) (by decide) (by decide) (by decide), r1 20 (by decide), h20]
      exact ult_ofNat_false (a := 0x20) (by omega) (by omega))
  obtain ⟨n10, d10, u10⟩ := u9.alu hc bw_at_d4 (off' := 0xD8) (by decide)
  have v10 := u10.self
  obtain ⟨n11, d11, u11⟩ := v10.alu hc bw_at_d8 (off' := 0xDC) (by decide)
  have v11 := u11.self
  have a0_11 : reg n11 a0 = G + BitVec.ofNat 32 off := by
    rw [u11.regs, updz v10.zero (by decide), u10.regs]; simp +decide only [upd, ite_true, ite_false, aluEval]
    rw [r8 19 (by decide) (by decide) (by decide) (by decide), r1 19 (by decide), h19, a1_8]
  have a1_11 : reg n11 a1 = BitVec.ofNat 32 len := by
    rw [u11.regs]; simp +decide only [upd, ite_true, ite_false, aluEval]
    rw [u10.regs, updz v8.zero (by decide), u10.regs, updz v8.zero (by decide), e8, a1_8]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : off + len < 2 ^ 32), Nat.mod_eq_of_lt (by omega : off < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : len < 2 ^ 32)]
    omega
  have g11 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg n11 r = g r := fun r h0 h1 h2 h3 h4 => by
    rw [u11.regs, updz v10.zero h1, u10.regs, updz v8.zero h0, r8 r h0 h1 h3 h4, r1 r h2]
  have a2_11 : reg n11 a2 = ptr := by
    rw [u11.regs, updz v10.zero (by decide), u10.regs, updz v8.zero (by decide),
      r8 a2 (by decide) (by decide) (by decide) (by decide)]; exact p1
  have a3_11 : reg n11 a3 = BitVec.ofNat 32 len := by
    rw [u11.regs, updz v10.zero (by decide), u10.regs, updz v8.zero (by decide)]
    simp +decide only [u8.regs, u7.regs, u6.regs, u5.regs, u4.regs, upd, ite_true, ite_false]
  have sp11 : reg n11 sp = G := by
    rw [g11 sp (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hsp
  obtain ⟨n12, c12, pc12, mem12, regs12⟩ := v11.callRa (cb := BitVec.ofNat 32 copyFromSliceU8Address) hc
    bw_at_dc bw_at_e0 (by decide) (by decide)
  have r12 : ∀ r, r ≠ ra → reg n12 r = reg n11 r := fun r h => by rw [regs12]; exact updz v11.zero h
  have hlo : (G + 0xFFFFFFF0).toNat = G.toNat - 16 := by
    rw [BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 2 ^ 32 - 16 from rfl]; omega
  have hGo : (G + BitVec.ofNat 32 off).toNat = G.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega)]; omega
  obtain ⟨n13, c13, pc13, sp13, a013, mem13, k13⟩ := copyFromSliceU8_correct n12
    (W := BitVec.ofNat 32 copyFromSliceU8Address) (retAddr := BW + BitVec.ofNat 32 (0xDC + 8))
    (dst := G + BitVec.ofNat 32 off) (src := ptr) (n := len) (by decide)
    (by rw [mem12]; exact hcp)
    (by rw [mem12, show (BitVec.ofNat 32 copyFromSliceU8Address + 0x761E : Word) =
      BitVec.ofNat 32 memcpyStubAddress from by decide]; exact hcs)
    pc12 (by rw [r12 a0 (by decide)]; exact a0_11) (by rw [r12 a1 (by decide)]; exact a1_11)
    (by rw [r12 a2 (by decide)]; exact a2_11) (by rw [r12 a3 (by decide)]; exact a3_11)
    (by rw [regs12]; simp +decide only [upd, ite_true, ite_false]) (even_clear _ (by decide))
    (by
      rw [r12 sp (by decide), sp11, mem12, show (BitVec.ofNat 32 copyFromSliceU8Address + 0x761E + 8 : Word) =
        BitVec.ofNat 32 memcpyStubAddress + 8 from by decide]
      exact ⟨hcb, lowSep (by rw [hGo]; omega) (by decide) (by decide),
        lowSep (by rw [hlo]; omega) (by decide) (by decide),
        sep_of_le (by rw [hlo]; omega) (by rw [hGo]; omega) |>.symm, sS, sD,
        by rw [hlo]; omega, by rw [hlo]; omega, by rw [hGo]; omega, hpw⟩)
  rw [r12 sp (by decide), sp11, mem12] at mem13
  have hc' : CodeIn n13.mem BW bootMainClosure1Code := fun i hi => by
    rw [mem13 _ (lowSep (by rw [hlo]; omega) (code_hi (by decide) (by decide) hi)
      (by have := (BW + BitVec.ofNat 32 i).isLt; omega))]
    rw [copyBytes_sep (n := len) (lowSep (by rw [hGo]; omega) (code_hi (by decide) (by decide) hi)
      (by have := (BW + BitVec.ofNat 32 i).isLt; omega)) (Nat.le_refl _)]
    exact hc i hi
  have t13 : St n13.mem BW n13 0xE4 (reg n13) := ⟨by rw [pc13], rfl, fun _ => rfl⟩
  obtain ⟨n14, d14, u14⟩ := t13.aluImm hc' bw_at_e4 (off' := 0xE6) (by decide)
  have v14 := u14.self
  obtain ⟨n15, d15, u15⟩ := v14.aluImm hc' bw_at_e6 (off' := 0xE8) (by decide)
  have g13 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp → r ≠ ra →
      reg n13 r = reg n11 r := fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hs hr => by
    rw [k13 r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hs, r12 r hr]
  refine ⟨n15, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10
    (.cons d11 (c12.trans (c13.trans (.cons d14 (.single d15)))))))))))))), ⟨u15.pc, rfl, fun _ => rfl⟩,
    fun x hx => by rw [u15.mem]; exact mem13 x hx, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u15.regs, updz v14.zero (by decide), u14.regs, updz t13.zero (by decide), sp13, r12 sp (by decide)]
    exact sp11
  · rw [u15.regs, updz v14.zero (by decide), u14.regs]; simp +decide only [upd, ite_true, ite_false, aluEval]
    rw [g13 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g11 9 (by decide) (by decide) (by decide) (by decide) (by decide), h9, BitVec.add_assoc,
      show (12 : Word) = BitVec.ofNat 32 12 from rfl, ofNat_add_ofNat,
      show 56 + 12 * k + 12 = 56 + 12 * (k + 1) by omega]
  · rw [u15.regs]; simp +decide only [upd, ite_true, ite_false, aluEval]
    rw [u14.regs, updz t13.zero (by decide),
      g13 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g11 8 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [u15.regs, updz v14.zero (by decide), u14.regs, updz t13.zero (by decide),
      g13 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g11 19 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h19
  · rw [u15.regs, updz v14.zero (by decide), u14.regs, updz t13.zero (by decide),
      g13 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g11 20 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h20
  · intro r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9' h10 h11 h12 h13 hr h8' h9''
    rw [u15.regs, updz v14.zero h8', u14.regs, updz t13.zero h9'']
    by_cases hs : r = sp
    · subst hs; rw [sp13, r12 sp (by decide), sp11, hsp]
    · rw [g13 r h1 h2 h3 h4 h5 h6 h7 h8 h9' h10 h11 h12 h13 hs hr, g11 r h0 h1 h2 h3 h4]

/-- What the field loop keeps, from the memory `Mx` before it: the record at
`G` holds the body's bytes below `e` and zeros above, and memory outside the
record and the 16 bytes below it, where `copy_from_slice` keeps its frame, is
as it was. -/
structure BWInv (Mx M' : Word → BitVec 8) (G : Word) (B : Nat → BitVec 8) (e : Nat) : Prop where
  body : ∀ i, i < 32 → M' (G + BitVec.ofNat 32 i) = if i < e then B i else 0
  out : ∀ x, Sep (G + 0xFFFFFFF0) 0x30 x 1 → M' x = Mx x

theorem bw_hi {Mx M' : Word → BitVec 8} {G : Word} (hGl : 16 ≤ G.toNat) (hGh : G.toNat + 0x90 ≤ 0x40000000)
    (h : ∀ x, Sep (G + 0xFFFFFFF0) 0x30 x 1 → M' x = Mx x) : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = Mx x :=
  fun x hx => h x (sep_of_le (by
    rw [BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 2 ^ 32 - 16 from rfl]; omega)
    (by have := x.isLt; omega))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- One pass of the field loop, from 0xB6 to the `bnez` at 0xE8, in terms
of `BWInv`: entry `k` copies the body's bytes `off` to `off + len` from
`ptr`. -/
theorem bw_step {Mx M' : Word → BitVec 8} {G ptr : Word} {B : Nat → BitVec 8} {n : Machine} {g : Fin 32 → Word}
    {k off len e : Nat} (s : St M' BW n 0xB6 g) (hc : CodeIn Mx BW bootMainClosure1Code)
    (hcp : CodeIn Mx (BitVec.ofNat 32 copyFromSliceU8Address) copyFromSliceU8Code)
    (hcs : CodeIn Mx (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode)
    (hcb : CodeIn Mx (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode)
    (hsp : g sp = G) (h9 : g 9 = G + BitVec.ofNat 32 (0x38 + 12 * k)) (h19 : g 19 = G) (h20 : g 20 = 0x20)
    (hG : G.toNat % 4 = 0) (hGl : 16 ≤ G.toNat) (hGh : G.toNat + 0x90 ≤ 0x40000000) (hk : k < 6)
    (I : BWInv Mx M' G B e) (he : e ≤ off) (hal : off + len ≤ 16) (hgap : ∀ i, e ≤ i → i < off → B i = 0)
    (hat : memLoad32 Mx (G + BitVec.ofNat 32 (0x30 + 12 * k)) = BitVec.ofNat 32 off)
    (hptr : memLoad32 Mx (G + BitVec.ofNat 32 (0x34 + 12 * k)) = ptr)
    (hlen : memLoad32 Mx (G + BitVec.ofNat 32 (0x38 + 12 * k)) = BitVec.ofNat 32 len)
    (hsrc : ∀ j, j < len → Mx (ptr + BitVec.ofNat 32 j) = B (off + j))
    (hp0 : ptr ≠ 0) (sP : Sep ptr len (G + 0xFFFFFFF0) 0x30) (hpw : ptr.toNat + len < 2 ^ 32) :
    ∃ n', Steps n n' ∧ St n'.mem BW n' 0xE8 (reg n') ∧ BWInv Mx n'.mem G B (off + len) ∧
      reg n' sp = G ∧ reg n' 9 = G + BitVec.ofNat 32 (0x38 + 12 * (k + 1)) ∧ reg n' 8 = g 8 + 0xFFFFFFFF ∧
      reg n' 19 = G ∧ reg n' 20 = 0x20 ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
        r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ ra → r ≠ 8 → r ≠ 9 →
        reg n' r = g r := by
  have hhi := bw_hi hGl hGh I.out
  have hlo : (G + 0xFFFFFFF0).toNat = G.toNat - 16 := by
    rw [BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 2 ^ 32 - 16 from rfl]; omega
  have tab : ∀ c, 0x30 ≤ c → c + 4 ≤ 0x90 → memLoad32 M' (G + BitVec.ofNat 32 c) = memLoad32 Mx (G + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => I.out _ (sep_of_le (by
      rw [hlo, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)
      (by have := (G + BitVec.ofNat 32 c + BitVec.ofNat 32 j).isLt; omega))
  have sP' : ∀ j, j < len → Sep (G + 0xFFFFFFF0) 0x30 (ptr + BitVec.ofNat 32 j) 1 := fun j hj =>
    (sP.sub (c := j) (l := 1) (by omega)).symm
  have hoff : G + 0xFFFFFFF0 + BitVec.ofNat 32 (16 + off) = G + BitVec.ofNat 32 off := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (0xFFFFFFF0 : Word).toNat = 2 ^ 32 - 16 from rfl]
    have := G.isLt; omega
  have sD : Sep (G + BitVec.ofNat 32 off) len ptr len := by
    have := sP.symm.sub (c := 16 + off) (l := len) (by omega)
    rwa [hoff] at this
  have sS : Sep ptr len (G + 0xFFFFFFF0) 16 := sP.subR (c := 0) (l := 16) (by omega) |> fun h => by
    rwa [add_ofNat_zero] at h
  obtain ⟨n', c', s', mem', sp', r9', r8', r19', r20', kp'⟩ := bw_field s (hc.hi hhi (by decide) (by decide))
    (hcp.hi hhi (by decide) (by decide)) (hcs.hi hhi (by decide) (by decide)) (hcb.hi hhi (by decide) (by decide))
    hsp h9 h19 h20 hG hGl hGh hk
    ((tab _ (by omega) (by omega)).trans hat) ((tab _ (by omega) (by omega)).trans hptr)
    ((tab _ (by omega) (by omega)).trans hlen) (by omega) hp0 sD sS hpw
  refine ⟨n', c', s', ⟨fun i hi => ?_, fun x hx => ?_⟩, sp', r9', r8', r19', r20', kp'⟩
  · have hx : Sep (G + 0xFFFFFFF0) 16 (G + BitVec.ofNat 32 i) 1 := sep_of_le (by
      rw [hlo, BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by have := (G + BitVec.ofNat 32 i).isLt; omega)
    rw [mem' _ hx, get_copy]
    have hsub : (BitVec.ofNat 32 i - BitVec.ofNat 32 off).toNat = if off ≤ i then i - off else 2 ^ 32 - (off - i) := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; split <;> omega
    by_cases h1 : off ≤ i
    · rw [ite_eq_left h1] at hsub
      by_cases h2 : i < off + len
      · rw [ite_eq_left (by omega), I.out _ (by
          have := sP' (i - off) (by omega)
          rwa [show BitVec.ofNat 32 i - BitVec.ofNat 32 off = BitVec.ofNat 32 (i - off) from by
            apply BitVec.eq_of_toNat_eq; rw [hsub, BitVec.toNat_ofNat]; omega]),
          show BitVec.ofNat 32 i - BitVec.ofNat 32 off = BitVec.ofNat 32 (i - off) from by
            apply BitVec.eq_of_toNat_eq; rw [hsub, BitVec.toNat_ofNat]; omega,
          hsrc _ (by omega), ite_eq_left h2, show off + (i - off) = i by omega]
      · rw [ite_eq_right (by omega), I.body i hi, ite_eq_right (by omega), ite_eq_right h2]
    · rw [ite_eq_right (by rw [ite_eq_right h1] at hsub; omega), I.body i hi]
      by_cases h3 : i < e
      · rw [ite_eq_left h3, ite_eq_left (by omega)]
      · rw [ite_eq_right h3, ite_eq_left (by omega), hgap i (by omega) (by omega)]
  · have hx16 : Sep (G + 0xFFFFFFF0) 16 x 1 := fun i hi j hj => hx i (by omega) j hj
    have hxd : Sep (G + BitVec.ofNat 32 off) len x 1 := by
      have := hx.sub (c := 16 + off) (l := len) (by omega)
      rwa [hoff] at this
    rw [mem' x hx16, copyBytes_sep hxd (Nat.le_refl _)]
    exact I.out x hx


/-- Entry `k` of the field table `encode` builds: the record offset, the
length, and where the bytes come from. -/
def bwOff : Nat → Nat
  | 0 => 0 | 1 => 4 | 2 => 8 | 3 => 12 | 4 => 14 | _ => 15

def bwLen : Nat → Nat
  | 0 => 4 | 1 => 2 | 2 => 4 | 3 => 2 | _ => 1

def bwPtr (G : Word) : Nat → Word
  | 0 => BitVec.ofNat 32 bsMagicAddress | 1 => BitVec.ofNat 32 bsVersionAddress | 2 => G + BitVec.ofNat 32 0x20
  | 3 => G + BitVec.ofNat 32 0x24 | 4 => G + BitVec.ofNat 32 0x26 | _ => G + BitVec.ofNat 32 0x27

/-- How many record bytes the first `k` entries have filled. -/
def bwEnd : Nat → Nat
  | 0 => 0 | 1 => 4 | 2 => 6 | 3 => 12 | 4 => 14 | 5 => 15 | _ => 16

theorem bwEnd_le : ∀ k, k < 6 → bwEnd k ≤ bwOff k := by decide
theorem bwEnd_succ : ∀ k, k < 6 → bwOff k + bwLen k = bwEnd (k + 1) := by decide
theorem bwOff_len : ∀ k, k < 6 → bwOff k + bwLen k ≤ 16 := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The field loop from the head of pass `k` to its exit at 0xEA. -/
theorem bw_loop {Mx : Word → BitVec 8} {G : Word} {B : Nat → BitVec 8} {R : Fin 32 → Word}
    (hc : CodeIn Mx BW bootMainClosure1Code)
    (hcp : CodeIn Mx (BitVec.ofNat 32 copyFromSliceU8Address) copyFromSliceU8Code)
    (hcs : CodeIn Mx (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode)
    (hcb : CodeIn Mx (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode)
    (hG : G.toNat % 4 = 0) (hGl : 16 ≤ G.toNat) (hGh : G.toNat + 0x90 ≤ 0x40000000)
    (hT : ∀ k, k < 6 → memLoad32 Mx (G + BitVec.ofNat 32 (0x30 + 12 * k)) = BitVec.ofNat 32 (bwOff k) ∧
      memLoad32 Mx (G + BitVec.ofNat 32 (0x34 + 12 * k)) = bwPtr G k ∧
      memLoad32 Mx (G + BitVec.ofNat 32 (0x38 + 12 * k)) = BitVec.ofNat 32 (bwLen k))
    (hS : ∀ k, k < 6 → ∀ j, j < bwLen k → Mx (bwPtr G k + BitVec.ofNat 32 j) = B (bwOff k + j))
    (hP : ∀ k, k < 6 → bwPtr G k ≠ 0 ∧ Sep (bwPtr G k) (bwLen k) (G + 0xFFFFFFF0) 0x30 ∧
      (bwPtr G k).toNat + bwLen k < 2 ^ 32)
    (hB6 : B 6 = 0) (hB7 : B 7 = 0) :
    ∀ d k {M' : Word → BitVec 8} {n : Machine}, k + d = 6 → k < 6 → St M' BW n 0xB6 (reg n) →
      BWInv Mx M' G B (bwEnd k) → reg n sp = G → reg n 9 = G + BitVec.ofNat 32 (0x38 + 12 * k) →
      reg n 8 = BitVec.ofNat 32 (6 - k) → reg n 19 = G → reg n 20 = 0x20 →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
        r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ ra → r ≠ 8 → r ≠ 9 →
        reg n r = R r) →
      ∃ n', Steps n n' ∧ St n'.mem BW n' 0xEA (reg n') ∧ BWInv Mx n'.mem G B 16 ∧ reg n' sp = G ∧
        reg n' 19 = G ∧ reg n' 20 = 0x20 ∧
        ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
          r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ ra → r ≠ 8 → r ≠ 9 →
          reg n' r = R r
  | 0, k, _, _, hk, hk6, _, _, _, _, _, _, _, _ => absurd hk (by omega)
  | d + 1, k, M', n, hk, hk6, s, I, hsp, h9, h8, h19, h20, hR => by
    obtain ⟨hat, hptr, hlen⟩ := hT k hk6
    obtain ⟨hp0, sP, hpw⟩ := hP k hk6
    have hgap : ∀ i, bwEnd k ≤ i → i < bwOff k → B i = 0 := fun i h1 h2 => by
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [bwEnd, bwOff] at h1 h2 <;> first | omega | (rcases (show i = 6 ∨ i = 7 by omega) with rfl | rfl <;> assumption)
    obtain ⟨n1, c1, s1, I1, sp1, r91, r81, r191, r201, kp1⟩ := bw_step (k := k) s hc hcp hcs hcb hsp h9 h19 h20 hG hGl
      hGh hk6 I (bwEnd_le k hk6) (bwOff_len k hk6) hgap hat hptr hlen (hS k hk6) hp0 sP hpw
    rw [bwEnd_succ k hk6] at I1
    have v8 : reg n1 8 = BitVec.ofNat 32 (6 - (k + 1)) := by
      rw [r81, h8]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 from rfl]
      omega
    have hR1 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
        r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ ra → r ≠ 8 → r ≠ 9 →
        reg n1 r = R r := fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 => by
      rw [kp1 r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16]
      exact hR r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
    have hc1 := (hc.hi (bw_hi hGl hGh I1.out) (by decide) (by decide))
    by_cases hl : k + 1 < 6
    · obtain ⟨n2, d2, u2⟩ := s1.taken hc1 0xB6 bw_at_e8 (by decide) (by
        show (reg n1 8 != reg n1 x0) = true
        rw [v8, s1.zero]
        exact bne_iff_ne.mpr fun e => by
          have := congrArg BitVec.toNat e
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          exact absurd this (by show 6 - (k + 1) ≠ 0; omega))
      have s2 : St n1.mem BW n2 0xB6 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
      obtain ⟨n', c', rest⟩ := bw_loop (R := R) hc hcp hcs hcb hG hGl hGh hT hS hP hB6 hB7 d (k + 1) (by omega) hl
        s2 I1
        (by rw [u2.regs]; exact sp1) (by rw [u2.regs]; exact r91) (by rw [u2.regs]; exact v8)
        (by rw [u2.regs]; exact r191) (by rw [u2.regs]; exact r201)
        (fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 => by
          rw [u2.regs]; exact hR1 r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16)
      exact ⟨n', c1.trans (.cons d2 c'), rest⟩
    · have e6 : k + 1 = 6 := by omega
      obtain ⟨n2, d2, u2⟩ := s1.notTaken hc1 0xEA bw_at_e8 (by decide) (by
        show (reg n1 8 != reg n1 x0) = false
        rw [v8, s1.zero, e6]; rfl)
      rw [e6] at I1
      exact ⟨n2, c1.trans (.single d2), ⟨u2.pc, rfl, fun _ => rfl⟩, by rw [u2.mem]; exact I1,
        by rw [u2.regs]; exact sp1, by rw [u2.regs]; exact r191, by rw [u2.regs]; exact r201,
        fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 => by
          rw [u2.regs]; exact hR1 r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16⟩

set_option maxRecDepth 10000 in
set_option linter.unusedSimpArgs false in
/-- The word the pack loop assembles from 4 bytes holds them little-endian. -/
theorem pack4 (b0 b1 b2 b3 : BitVec 8) :
    let w := aluEval .or (aluEval .or (aluEval .sll (b1.zeroExtend 32) 0x8) (b0.zeroExtend 32))
      (aluEval .or (aluEval .sll (b2.zeroExtend 32) 0x10) (aluEval .sll (b3.zeroExtend 32) 0x18))
    w.extractLsb' 0 8 = b0 ∧ w.extractLsb' 8 8 = b1 ∧ w.extractLsb' 16 8 = b2 ∧ w.extractLsb' 24 8 = b3 := by
  intro w
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> apply lt8_cases <;>
    simp +decide [w, aluEval, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_setWidth, -BitVec.getLsbD_eq_getElem]

def bwPackBlk : List BInstr :=
  [.lbu a1 (8 : Fin 32) 0x1, .lbu a2 (8 : Fin 32) 0x2, .lbu a3 (8 : Fin 32) 0x3, .lbu a4 (8 : Fin 32) 0x0,
   .aluImm .sll a1 a1 0x8, .aluImm .sll a2 a2 0x10, .aluImm .sll a3 a3 0x18, .alu .or a1 a1 a4,
   .alu .or a2 a2 a3, .alu .or a1 a1 a2, .sw (9 : Fin 32) a1 0x0, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, .aluImm .add a0 a0 0xFFFFFFFF]

theorem bwPackBlk_end : blockEnd bootMainClosure1Code 0x128 bwPackBlk = some 0x14C :=
  (blockEnd_cons' (off' := 0x12C) bw_at_128 rfl (blockEnd_cons' (off' := 0x130) bw_at_12c rfl (blockEnd_cons' (off' := 0x134) bw_at_130 rfl (blockEnd_cons' (off' := 0x138) bw_at_134 rfl (blockEnd_cons' (off' := 0x13A) bw_at_138 rfl (blockEnd_cons' (off' := 0x13C) bw_at_13a rfl (blockEnd_cons' (off' := 0x13E) bw_at_13c rfl (blockEnd_cons' (off' := 0x140) bw_at_13e rfl (blockEnd_cons' (off' := 0x142) bw_at_140 rfl (blockEnd_cons' (off' := 0x144) bw_at_142 rfl (blockEnd_cons' (off' := 0x146) bw_at_144 rfl (blockEnd_cons' (off' := 0x148) bw_at_146 rfl (blockEnd_cons' (off' := 0x14A) bw_at_148 rfl (blockEnd_cons' (off' := 0x14C) bw_at_14a rfl rfl))))))))))))))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- The pack loop from the head of pass `k` at 0x128 to its exit at 0x14E:
the 32-byte record at `G` copied into words at `G + 0x28`. -/
theorem bw_pack {Mr : Word → BitVec 8} {G : Word} {R : Fin 32 → Word} (hc : CodeIn Mr BW bootMainClosure1Code)
    (hG : G.toNat % 4 = 0) (hGh : G.toNat + 0x90 ≤ 0x40000000) :
    ∀ d k {M' : Word → BitVec 8} {n : Machine}, k + d = 8 → k < 8 → St M' BW n 0x128 (reg n) →
      reg n 8 = G + BitVec.ofNat 32 (4 * k) → reg n 9 = G + BitVec.ofNat 32 (0x28 + 4 * k) →
      reg n a0 = BitVec.ofNat 32 (8 - k) →
      (∀ i, i < 4 * k → M' (G + BitVec.ofNat 32 (0x28 + i)) = Mr (G + BitVec.ofNat 32 i)) →
      (∀ x, Sep (G + BitVec.ofNat 32 0x28) 0x20 x 1 → M' x = Mr x) →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ 8 → r ≠ 9 → reg n r = R r) →
      ∃ n', Steps n n' ∧ St n'.mem BW n' 0x14E (reg n') ∧
        (∀ i, i < 32 → n'.mem (G + BitVec.ofNat 32 (0x28 + i)) = Mr (G + BitVec.ofNat 32 i)) ∧
        (∀ x, Sep (G + BitVec.ofNat 32 0x28) 0x20 x 1 → n'.mem x = Mr x) ∧
        ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ 8 → r ≠ 9 → reg n' r = R r
  | 0, k, _, _, hk, hk8, _, _, _, _, _, _, _ => absurd hk (by omega)
  | d + 1, k, M', n, hk, hk8, s, h8, h9, ha0, hW, hO, hR => by
    have hc' : CodeIn M' BW bootMainClosure1Code := hc.hi (fun x hx => hO x (sep_of_le (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by have := x.isLt; omega))) (by decide) (by decide)
    have hdst : (G + BitVec.ofNat 32 (0x28 + 4 * k)).toNat = G.toNat + 0x28 + 4 * k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    obtain ⟨n1, c1, u1⟩ := s.block bwPackBlk hc' bwPackBlk_end (by
      simp only [BlockOk, BInstr.ok, BInstr.run, bwPackBlk]
      simp +decide only [upd, ↓reduceIte, true_and, and_true]
      rw [h9, add_lit_zero]
      exact ⟨by rw [hdst]; omega, lowSep (by rw [hdst]; omega) (by decide) (by decide)⟩)
    have hsrc : ∀ j, j < 4 → M' (G + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 j) = Mr (G + BitVec.ofNat 32 (4 * k + j)) :=
      fun j hj => by
        rw [add_ofNat_assoc]; exact hO _ (sep_offsets G (Or.inr (by omega)) (by omega) (by omega))
    obtain ⟨w, hw⟩ : ∃ w, aluEval .or (aluEval .or (aluEval .sll ((M' (G + BitVec.ofNat 32 (4 * k) + 1)).zeroExtend 32) 0x8)
        ((M' (G + BitVec.ofNat 32 (4 * k) + 0)).zeroExtend 32))
        (aluEval .or (aluEval .sll ((M' (G + BitVec.ofNat 32 (4 * k) + 2)).zeroExtend 32) 0x10)
          (aluEval .sll ((M' (G + BitVec.ofNat 32 (4 * k) + 3)).zeroExtend 32) 0x18)) = w := ⟨_, rfl⟩
    have hmem : n1.mem = memStore32 M' (G + BitVec.ofNat 32 (0x28 + 4 * k)) w := by
      rw [u1.mem]; simp +decide only [runBlock, BInstr.run, bwPackBlk, upd, ↓reduceIte]
      rw [h9, h8, add_lit_zero, ← hw]
    have hwb := pack4 (M' (G + BitVec.ofNat 32 (4 * k) + 0)) (M' (G + BitVec.ofNat 32 (4 * k) + 1))
      (M' (G + BitVec.ofNat 32 (4 * k) + 2)) (M' (G + BitVec.ofNat 32 (4 * k) + 3))
    simp only [hw] at hwb
    obtain ⟨w0, w1, w2, w3⟩ := hwb
    have rg : ∀ r, reg n1 r = (runBlock bwPackBlk (M', reg n)).2 r := fun r => by rw [u1.regs]
    have v8 : reg n1 8 = G + BitVec.ofNat 32 (4 * (k + 1)) := by
      rw [rg]; simp +decide only [runBlock, BInstr.run, bwPackBlk, upd, ↓reduceIte]
      rw [h8]; exact add_sp G (b := 4) (by omega)
    have v9 : reg n1 9 = G + BitVec.ofNat 32 (0x28 + 4 * (k + 1)) := by
      rw [rg]; simp +decide only [runBlock, BInstr.run, bwPackBlk, upd, ↓reduceIte]
      rw [h9]; exact add_sp G (b := 4) (by omega)
    have va0 : reg n1 a0 = BitVec.ofNat 32 (8 - (k + 1)) := by
      rw [rg]; simp +decide only [runBlock, BInstr.run, bwPackBlk, upd, ↓reduceIte]
      rw [ha0]; apply BitVec.eq_of_toNat_eq
      show (BitVec.ofNat 32 (8 - k) + 0xFFFFFFFF).toNat = _
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 from rfl]
      omega
    have hR1 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ 8 → r ≠ 9 → reg n1 r = R r :=
      fun r h0 h1 h2 h3 h4 h8' h9' => by
        rw [rg, runBlock_reg _ _ _ r s.zero (by revert h0 h1 h2 h3 h4 h8' h9'; revert r; decide)]
        exact hR r h0 h1 h2 h3 h4 h8' h9'
    have hW1 : ∀ i, i < 4 * (k + 1) → n1.mem (G + BitVec.ofNat 32 (0x28 + i)) = Mr (G + BitVec.ofNat 32 i) := by
      intro i hi
      rw [hmem]
      by_cases hik : i < 4 * k
      · rw [memStore32_get_sep (sep_offsets G (c := 0x28 + 4 * k) (n := 4) (d := 0x28 + i) (k := 1)
          (Or.inr (by omega)) (by omega) (by omega))]
        exact hW i hik
      · obtain ⟨j, rfl⟩ : ∃ j, i = 4 * k + j := ⟨i - 4 * k, by omega⟩
        have hj : j < 4 := by omega
        rw [show G + BitVec.ofNat 32 (0x28 + (4 * k + j)) = G + BitVec.ofNat 32 (0x28 + 4 * k) + BitVec.ofNat 32 j
          from by rw [add_ofNat_assoc, Nat.add_assoc]]
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
        · rw [add_ofNat_zero, st32_at0, w0, ← hsrc 0 (by decide)]; rfl
        · rw [show BitVec.ofNat 32 1 = (1 : Word) from rfl, st32_at1, w1, ← hsrc 1 (by decide)]; rfl
        · rw [show BitVec.ofNat 32 2 = (2 : Word) from rfl, st32_at2, w2, ← hsrc 2 (by decide)]; rfl
        · rw [show BitVec.ofNat 32 3 = (3 : Word) from rfl, st32_at3, w3, ← hsrc 3 (by decide)]; rfl
    have hO1 : ∀ x, Sep (G + BitVec.ofNat 32 0x28) 0x20 x 1 → n1.mem x = Mr x := fun x hx => by
      rw [hmem, memStore32_get_sep (by
        have := hx.sub (c := 4 * k) (l := 4) (by omega)
        rwa [add_ofNat_assoc] at this), hO x hx]
    have hc1 : CodeIn n1.mem BW bootMainClosure1Code := hc.hi (fun x hx => hO1 x (sep_of_le (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by have := x.isLt; omega))) (by decide) (by decide)
    have s1 : St n1.mem BW n1 0x14C (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
    by_cases hl : k + 1 < 8
    · obtain ⟨n2, d2, u2⟩ := s1.taken hc1 0x128 bw_at_14c (by decide) (by
        show (reg n1 a0 != reg n1 x0) = true
        rw [va0, s1.zero]
        exact bne_iff_ne.mpr fun e => by
          have := congrArg BitVec.toNat e
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          exact absurd this (by show 8 - (k + 1) ≠ 0; omega))
      obtain ⟨n', c', rest⟩ := bw_pack (R := R) hc hG hGh d (k + 1) (by omega) hl
        (⟨u2.pc, u2.mem, fun _ => rfl⟩ : St n1.mem BW n2 0x128 (reg n2)) (by rw [u2.regs]; exact v8)
        (by rw [u2.regs]; exact v9) (by rw [u2.regs]; exact va0) hW1 hO1
        (fun r h0 h1 h2 h3 h4 h8' h9' => by rw [u2.regs]; exact hR1 r h0 h1 h2 h3 h4 h8' h9')
      exact ⟨n', c1.trans (.cons d2 c'), rest⟩
    · have e8 : k + 1 = 8 := by omega
      obtain ⟨n2, d2, u2⟩ := s1.notTaken hc1 0x14E bw_at_14c (by decide) (by
        show (reg n1 a0 != reg n1 x0) = false
        rw [va0, s1.zero, e8]; rfl)
      rw [e8] at hW1
      exact ⟨n2, c1.trans (.single d2), ⟨u2.pc, rfl, fun _ => rfl⟩, by rw [u2.mem]; exact hW1,
        by rw [u2.mem]; exact hO1, fun r h0 h1 h2 h3 h4 h8' h9' => by rw [u2.regs]; exact hR1 r h0 h1 h2 h3 h4 h8' h9'⟩

/-- The 32-byte record from body bytes `B`: the 28 bytes, then their CRC-32,
least significant byte first. -/
def bwRecB (B : Nat → BitVec 8) (i : Nat) : BitVec 8 :=
  if i < 28 then B i else (crcBits ((List.range 28).map B)).extractLsb' (8 * (i - 28)) 8

set_option maxRecDepth 10000 in
theorem srl_lsb8 (x : Word) (s : Nat) (hs : s + 8 ≤ 32) :
    (aluEval .srl x (BitVec.ofNat 32 s)).extractLsb' 0 8 = x.extractLsb' s 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [aluEval, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : s < 2 ^ 32), Nat.mod_eq_of_lt (by omega : s < 32)]
  simp [show i < 8 from hi, Nat.add_comm]

def bwCrcBlk : List BInstr :=
  [.aluImm .srl a1 a0 0x18, .aluImm .srl a2 a0 0x10, .aluImm .srl a3 a0 0x8, .sb sp a0 0x1C, .sb sp a3 0x1D,
   .sb sp a2 0x1E, .sb sp a1 0x1F, .aluImm .add a0 sp 0x28, .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0x0,
   .aluImm .add (9 : Fin 32) sp 0x28]

theorem bwCrcBlk_end : blockEnd bootMainClosure1Code 0xF6 bwCrcBlk = some 0x11C :=
  (blockEnd_cons' (off' := 0xFA) bw_at_f6 rfl (blockEnd_cons' (off' := 0xFE) bw_at_fa rfl (blockEnd_cons' (off' := 0x102) bw_at_fe rfl (blockEnd_cons' (off' := 0x106) bw_at_102 rfl (blockEnd_cons' (off' := 0x10A) bw_at_106 rfl (blockEnd_cons' (off' := 0x10E) bw_at_10a rfl (blockEnd_cons' (off' := 0x112) bw_at_10e rfl (blockEnd_cons' (off' := 0x114) bw_at_112 rfl (blockEnd_cons' (off' := 0x118) bw_at_114 rfl (blockEnd_cons' (off' := 0x11A) bw_at_118 rfl (blockEnd_cons' (off' := 0x11C) bw_at_11a rfl rfl)))))))))))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- From 0xEA to 0x14E: CRC-32 over the 28 body bytes at `G`, the checksum
stored after them, and the 32-byte record copied into words at `G + 0x28`. -/
theorem bw_crc {M : Word → BitVec 8} {G : Word} {B : Nat → BitVec 8} {n : Machine}
    (s : St M BW n 0xEA (reg n)) (hc : CodeIn M BW bootMainClosure1Code)
    (hcrc : CodeIn M (BitVec.ofNat 32 crc32Address) crc32Code)
    (hms : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode)
    (hsp : reg n sp = G) (hG : G.toNat % 4 = 0) (hGh : G.toNat + 0x90 ≤ 0x40000000)
    (hB : ∀ i, i < 28 → M (G + BitVec.ofNat 32 i) = B i) :
    ∃ n', Steps n n' ∧ St n'.mem BW n' 0x14E (reg n') ∧
      (∀ i, i < 32 → n'.mem (G + BitVec.ofNat 32 (0x28 + i)) = bwRecB B i) ∧
      (∀ x, Sep G 0x48 x 1 → n'.mem x = M x) ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 8 → r ≠ 9 → r ≠ ra →
        reg n' r = reg n r := by
  have hz := s.zero
  have glo : ∀ c, c + 1 ≤ 0x90 → Sep (G + BitVec.ofNat 32 c) 1 BW bootMainClosure1Code.length := fun c h =>
    lowSep (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by decide) (by decide)
  -- mv a0, sp; mv s0, sp; crc32
  obtain ⟨n1, c1, u1⟩ := s.block [.alu .add a0 x0 sp, .alu .add (8 : Fin 32) x0 sp] hc
    (blockEnd_cons' (off' := 0xEC) bw_at_ea rfl (blockEnd_cons' (off' := 0xEE) bw_at_ec rfl rfl)) ⟨trivial, trivial, trivial⟩
  have t1 : St M BW n1 0xEE (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have r1 : ∀ r, reg n1 r = (runBlock [.alu .add a0 x0 sp, .alu .add (8 : Fin 32) x0 sp] (M, reg n)).2 r :=
    fun r => by rw [u1.regs]
  have a01 : reg n1 a0 = G := by rw [r1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [hz]); rw [hsp]; exact BitVec.zero_add _
  have s01 : reg n1 8 = G := by rw [r1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [hz]); rw [hsp]; exact BitVec.zero_add _
  have k1 : ∀ r, r ≠ a0 → r ≠ 8 → reg n1 r = reg n r := fun r h0 h8 => by
    rw [r1, runBlock_reg _ _ _ r hz (by revert h0 h8; revert r; decide)]
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := t1.callRa (cb := BitVec.ofNat 32 crc32Address) hc bw_at_ee bw_at_f2
    (by decide) (by decide)
  obtain ⟨n3, c3, pc3, mem3, a03, k3⟩ := crc32_correct n2 (BitVec.ofNat 32 crc32Address) (BW + BitVec.ofNat 32 (0xEE + 8))
    (fun i hi => by rw [mem2]; exact hcrc i hi) pc2 (by rw [regs2]; simp +decide [upd]) (even_clear _ (by decide))
  have r2 : ∀ r, r ≠ ra → reg n2 r = reg n1 r := fun r h => by rw [regs2]; exact updz t1.zero h
  have hcrcv : reg n3 a0 = crcBits ((List.range 28).map B) := by
    rw [a03, r2 a0 (by decide), a01]
    unfold bytesAt
    exact congrArg crcBits (List.map_congr_left fun i hi => by rw [mem2]; exact hB i (List.mem_range.mp hi))
  have t3 : St M BW n3 0xF6 (reg n3) := ⟨by rw [pc3], by rw [mem3, mem2], fun _ => rfl⟩
  have sp3 : reg n3 sp = G := by
    rw [k3 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r2 sp (by decide),
      k1 sp (by decide) (by decide), hsp]
  -- the checksum's bytes, then memset(G + 0x28, 0, 32)
  obtain ⟨n4, c4, u4⟩ := t3.block bwCrcBlk hc bwCrcBlk_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, bwCrcBlk]
    simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp3]
    exact ⟨glo 0x1C (by decide), glo 0x1D (by decide), glo 0x1E (by decide), glo 0x1F (by decide)⟩)
  obtain ⟨M4, hM4⟩ : ∃ M4, memStore8 (memStore8 (memStore8 (memStore8 M (G + BitVec.ofNat 32 0x1C)
      ((crcBits ((List.range 28).map B)).extractLsb' 0 8)) (G + BitVec.ofNat 32 0x1D)
      ((crcBits ((List.range 28).map B)).extractLsb' 8 8)) (G + BitVec.ofNat 32 0x1E)
      ((crcBits ((List.range 28).map B)).extractLsb' 16 8)) (G + BitVec.ofNat 32 0x1F)
      ((crcBits ((List.range 28).map B)).extractLsb' 24 8) = M4 := ⟨_, rfl⟩
  have m4 : n4.mem = M4 := by
    rw [u4.mem, ← hM4]; simp +decide only [runBlock, BInstr.run, bwCrcBlk, upd, ↓reduceIte]
    have e8 : (aluEval .srl (crcBits ((List.range 28).map B)) 8).extractLsb' 0 8 =
        (crcBits ((List.range 28).map B)).extractLsb' 8 8 := srl_lsb8 _ 8 (by decide)
    have e16 : (aluEval .srl (crcBits ((List.range 28).map B)) 0x10).extractLsb' 0 8 =
        (crcBits ((List.range 28).map B)).extractLsb' 16 8 := srl_lsb8 _ 16 (by decide)
    have e24 : (aluEval .srl (crcBits ((List.range 28).map B)) 0x18).extractLsb' 0 8 =
        (crcBits ((List.range 28).map B)).extractLsb' 24 8 := srl_lsb8 _ 24 (by decide)
    rw [sp3, hcrcv, e8, e16, e24]; rfl
  have r4 : ∀ r, reg n4 r = (runBlock bwCrcBlk (M, reg n3)).2 r := fun r => by rw [u4.regs]
  have t4 : St M4 BW n4 0x11C (reg n4) := ⟨u4.pc, m4, fun _ => rfl⟩
  have nes : ∀ (a x : Word), Sep a 1 x 1 → x ≠ a := fun a x h e =>
    h 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)
  have M4o : ∀ x, Sep G 0x48 x 1 → M4 x = M x := fun x hx => by
    rw [← hM4, memStore8_ne (nes _ _ (hx.sub (c := 0x1F) (l := 1) (by decide))),
      memStore8_ne (nes _ _ (hx.sub (c := 0x1E) (l := 1) (by decide))),
      memStore8_ne (nes _ _ (hx.sub (c := 0x1D) (l := 1) (by decide))),
      memStore8_ne (nes _ _ (hx.sub (c := 0x1C) (l := 1) (by decide)))]
  have hhi4 : ∀ x : Word, 0x40000000 ≤ x.toNat → M4 x = M x := fun x hx => M4o x (sep_of_le (by omega)
    (by have := x.isLt; omega))
  have hc4 := hc.hi hhi4 (by decide) (by decide)
  have hms4 := hms.hi hhi4 (by decide) (by decide)
  have a04 : reg n4 a0 = G + BitVec.ofNat 32 0x28 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, bwCrcBlk, upd, ↓reduceIte]; rw [sp3]; rfl
  have a14 : reg n4 a1 = 0 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, bwCrcBlk, upd, ↓reduceIte]; (try rw [t3.zero]); try rfl
  have a24 : reg n4 a2 = BitVec.ofNat 32 32 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, bwCrcBlk, upd, ↓reduceIte]; (try rw [t3.zero]); try rfl
  have s14 : reg n4 9 = G + BitVec.ofNat 32 0x28 := by
    rw [r4]; simp +decide only [runBlock, BInstr.run, bwCrcBlk, upd, ↓reduceIte]; rw [sp3]; rfl
  have k4 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ 9 → reg n4 r = reg n3 r := fun r h0 h1 h2 h3 h9 => by
    rw [r4, runBlock_reg _ _ _ r t3.zero (by simp only [bwCrcBlk]; revert h0 h1 h2 h3 h9; revert r; decide)]
  obtain ⟨n5, c5, pc5, mem5, regs5⟩ := t4.callRa (cb := BitVec.ofNat 32 memsetAddress) hc4 bw_at_11c bw_at_120
    (by decide) (by decide)
  have r5 : ∀ r, r ≠ ra → reg n5 r = reg n4 r := fun r h => by rw [regs5]; exact updz t4.zero h
  obtain ⟨n6, c6, pc6, mem6, a06, k6⟩ := memset_correct n5 (BitVec.ofNat 32 memsetAddress)
    (BW + BitVec.ofNat 32 (0x11C + 8)) (G + BitVec.ofNat 32 0x28) 0 32 (fun i hi => by rw [mem5]; exact hms4 i hi)
    (by decide) pc5 (by rw [r5 a0 (by decide)]; exact a04) (by rw [r5 a1 (by decide)]; exact a14)
    (by rw [r5 a2 (by decide)]; exact a24) (by rw [regs5]; simp +decide [upd]) (even_clear _ (by decide))
    (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (lowSep (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by decide) (by decide))
  rw [mem5] at mem6
  obtain ⟨M6, hM6⟩ : ∃ M6, fillBytes M4 (G + BitVec.ofNat 32 0x28) ((0 : Word).extractLsb' 0 8) 32 = M6 := ⟨_, rfl⟩
  rw [hM6] at mem6
  have M6o : ∀ x, Sep (G + BitVec.ofNat 32 0x28) 0x20 x 1 → M6 x = M4 x := fun x hx => by
    rw [← hM6]; exact fillBytes_sep hx (Nat.le_refl _)
  have hc6 : CodeIn M6 BW bootMainClosure1Code := hc4.hi (fun x hx => M6o x (sep_of_le (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by have := x.isLt; omega))) (by decide) (by decide)
  have t6 : St M6 BW n6 0x124 (reg n6) := ⟨by rw [pc6], mem6, fun _ => rfl⟩
  -- li a0, 8; beqz a0 (not taken); the pack loop
  obtain ⟨n7, c7, u7⟩ := t6.block [.aluImm .add a0 x0 0x8] hc6 (blockEnd_cons' (off' := 0x126) bw_at_124 rfl rfl)
    ⟨trivial, trivial⟩
  have t7 : St M6 BW n7 0x126 (reg n7) := ⟨u7.pc, u7.mem, fun _ => rfl⟩
  have r7 : ∀ r, r ≠ a0 → reg n7 r = reg n6 r := fun r h => by
    rw [u7.regs]; simp only [runBlock, BInstr.run]; exact updz t6.zero h
  have a07 : reg n7 a0 = 8 := by rw [u7.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [t6.zero]; rfl
  obtain ⟨n8, d8, u8⟩ := t7.notTaken hc6 0x128 bw_at_126 (by decide) (by
    show (reg n7 a0 == reg n7 x0) = false; rw [a07, t7.zero]; rfl)
  have ss : ∀ r, r ≠ a0 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ ra → reg n7 r = reg n4 r :=
    fun r h0 h2 h3 h4 h5 h6 hr => by rw [r7 r h0, k6 r h2 h3 h4 h5 h6, r5 r hr]
  obtain ⟨n', c', s', hW', hO', hR'⟩ := bw_pack (Mr := M4) (R := reg n7) hc4 hG hGh 8 0 rfl (by decide)
    (⟨u8.pc, u8.mem, fun _ => rfl⟩ : St M6 BW n8 0x128 (reg n8))
    (by rw [u8.regs, ss 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k4 8 (by decide) (by decide) (by decide) (by decide) (by decide),
      k3 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r2 8 (by decide), s01]
        exact (add_ofNat_zero G).symm)
    (by rw [u8.regs, ss 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s14])
    (by rw [u8.regs, a07]; rfl) (fun i hi => absurd hi (by omega)) (fun x hx => M6o x hx)
    (fun r _ _ _ _ _ _ _ => by rw [u8.regs])
  refine ⟨n', c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (.cons d8 c'))))))), s',
    fun i hi => ?_, fun x hx => ?_, fun r h0 h1 h2 h3 h4 h5 h6 h8 h9 hr => ?_⟩
  · have neq : ∀ c d : Nat, c < 2 ^ 32 → d < 2 ^ 32 → c ≠ d → BitVec.ofNat 32 c ≠ BitVec.ofNat 32 d :=
      fun c d hc hd h e => by
        have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega
    rw [hW' i hi, ← hM4]
    unfold bwRecB
    by_cases h28 : i < 28
    · rw [ite_eq_left h28]
      rw [get_st8_off (neq 0x1F i (by decide) (by omega) (by omega)), get_st8_off (neq 0x1E i (by decide) (by omega) (by omega)),
        get_st8_off (neq 0x1D i (by decide) (by omega) (by omega)), get_st8_off (neq 0x1C i (by decide) (by omega) (by omega))]
      exact hB i h28
    · rw [ite_eq_right h28]
      rcases (show i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 by omega) with rfl | rfl | rfl | rfl
      · rw [get_st8_off (by decide), get_st8_off (by decide), get_st8_off (by decide), memStore8_same]
      · rw [get_st8_off (by decide), get_st8_off (by decide), memStore8_same]
      · rw [get_st8_off (by decide), memStore8_same]
      · rw [memStore8_same]
  · rw [hO' x (hx.sub (c := 0x28) (l := 0x20) (by decide)), M4o x hx]
  · rw [hR' r h0 h1 h2 h3 h4 h8 h9, ss r h0 h2 h3 h4 h5 h6 hr, k4 r h0 h1 h2 h3 h9,
      k3 r h0 h1 h2 h3 h4 h5 h6, r2 r hr, k1 r h0 h8]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **`boot_main`'s boot-state writer, as compiled**: with the functions and
data it uses where the image puts them, the ROM's code above `0x40000000`,
`0x90` bytes of stack below `sp` plus `romStack` for the ROM (below
`0x40000000` and apart from the two constants it copies), and the 8-byte
state at `st` apart from that stack, it returns to `ra` with `sp`, `gp`,
`tp`, and `s0` through `s11` restored and memory outside its stack as it
was. On the way it calls the ROM's erase with `bwAddr copy`'s sector and the
ROM's write with `bwAddr copy` and the 32 bytes `bwRec` gives, which the
contracts require. -/
theorem bootWrite_correct (m : Machine) {retAddr copy st romBase : Word} {romCode : List Nat} {romStack : Nat}
    (code : BWCode m.mem) (hrom : CodeIn m.mem romBase romCode)
    (hrb : 0x40000000 ≤ romBase.toNat) (hrl : romBase.toNat + romCode.length ≤ 2 ^ 32)
    (hpc : m.pc = BW) (ha0 : reg m a0 = copy) (ha1 : reg m a1 = st) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : (reg m sp).toNat % 16 = 0) (hrs : 16 ≤ romStack) (hrs4 : romStack % 4 = 0)
    (hsl : 0x90 + romStack ≤ (reg m sp).toNat) (hsw : (reg m sp).toNat ≤ 0x40000000)
    (hSm : Sep (reg m sp - BitVec.ofNat 32 (0x90 + romStack)) (0x90 + romStack) (BitVec.ofNat 32 bsMagicAddress) 4)
    (hSv : Sep (reg m sp - BitVec.ofNat 32 (0x90 + romStack)) (0x90 + romStack) (BitVec.ofNat 32 bsVersionAddress) 2)
    (hst : Sep st 8 (reg m sp - BitVec.ofNat 32 (0x90 + romStack)) (0x90 + romStack)) (hsta : st.toNat % 4 = 0)
    (unlock : RomFn romBase romCode 0x40000140 romStack fun _ => True)
    (erase : RomFn romBase romCode 0x40000128 romStack fun n => reg n a0 = bwAddr copy >>> 12)
    (write : RomFn romBase romCode 0x4000012C romStack fun n =>
      reg n a0 = bwAddr copy ∧ reg n a2 = 32 ∧
        ∀ i, i < 32 → n.mem (reg n a1 + BitVec.ofNat 32 i) = bwRec m.mem st i)
    (log : RomFn romBase romCode 0x40000040 romStack fun _ => True) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ (∀ q, romKeep q = true → reg m' q = reg m q) ∧
      ∀ x, Sep (reg m sp - BitVec.ofNat 32 (0x90 + romStack)) (0x90 + romStack) x 1 → m'.mem x = m.mem x := by
  obtain ⟨S, hSd⟩ : ∃ S, reg m sp - BitVec.ofNat 32 (0x90 + romStack) = S := ⟨_, rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G, reg m sp + 0xFFFFFF70 = G := ⟨_, rfl⟩
  rw [hSd] at hSm hSv hst ⊢
  have hSn : S.toNat = (reg m sp).toNat - (0x90 + romStack) := by
    rw [← hSd, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 0x90 + romStack) (by omega)]; omega
  have hGn : G.toNat = (reg m sp).toNat - 0x90 := by
    rw [← hGd, BitVec.toNat_add, show (0xFFFFFF70 : Word).toNat = 2 ^ 32 - 0x90 from rfl]; omega
  have hGS : G = S + BitVec.ofNat 32 romStack := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hGn, hSn, Nat.mod_eq_of_lt (a := romStack) (by omega)]; omega)
  have hspG : G + 0x90 = reg m sp := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, show (0x90 : Word).toNat = 0x90 from rfl, hGn]; omega)
  have hGa : G.toNat % 4 = 0 := by omega
  have hc := code.self
  have fr : ∀ c l, c + l ≤ 0x90 → ∀ (x : Word) (n : Nat), Sep S (0x90 + romStack) x n →
      Sep (G + BitVec.ofNat 32 c) l x n :=
    fun c l h x n hx => by rw [hGS, add_ofNat_assoc]; exact hx.sub (c := romStack + c) (l := l) (by omega)
  have gLow : ∀ c, c + 4 ≤ 0x90 → (G + BitVec.ofNat 32 c).toNat + 4 ≤ 0x40000000 := fun c h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hiS : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep S (0x90 + romStack) x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have s0' : St m.mem BW m 0 (reg m) := ⟨by rw [hpc]; rfl, rfl, fun _ => rfl⟩
  have hz := s0'.zero
  obtain ⟨m1, e1, t1⟩ := s0'.aluImm hc bw_at_0 (off' := 2) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFF70 = G from hGd] at t1
  have u1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  have f1 : ∀ r, r ≠ sp → upd (reg m) sp G r = reg m r := fun r h => updz hz h
  obtain ⟨m2, e2, t2⟩ := t1.sw hc bw_at_2 (off' := 0x4) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x8C) (by decide))
  rw [u1sp, f1 ra (by decide)] at t2
  have hc2 := hc.store32 (v := reg m ra) (lowSep (gLow 0x8C (by omega)) (by decide) (by decide))
  obtain ⟨m3, e3, t3⟩ := t2.sw hc2 bw_at_4 (off' := 0x6) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x88) (by decide))
  rw [u1sp, f1 8 (by decide)] at t3
  have hc3 := hc2.store32 (v := reg m 8) (lowSep (gLow 0x88 (by omega)) (by decide) (by decide))
  obtain ⟨m4, e4, t4⟩ := t3.sw hc3 bw_at_6 (off' := 0x8) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x84) (by decide))
  rw [u1sp, f1 9 (by decide)] at t4
  have hc4 := hc3.store32 (v := reg m 9) (lowSep (gLow 0x84 (by omega)) (by decide) (by decide))
  obtain ⟨m5, e5, t5⟩ := t4.sw hc4 bw_at_8 (off' := 0xA) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x80) (by decide))
  rw [u1sp, f1 18 (by decide)] at t5
  have hc5 := hc4.store32 (v := reg m 18) (lowSep (gLow 0x80 (by omega)) (by decide) (by decide))
  obtain ⟨m6, e6, t6⟩ := t5.sw hc5 bw_at_a (off' := 0xC) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x7C) (by decide))
  rw [u1sp, f1 19 (by decide)] at t6
  have hc6 := hc5.store32 (v := reg m 19) (lowSep (gLow 0x7C (by omega)) (by decide) (by decide))
  obtain ⟨m7, e7, t7⟩ := t6.sw hc6 bw_at_c (off' := 0xE) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0x78) (by decide))
  rw [u1sp, f1 20 (by decide)] at t7
  have hc7 := hc6.store32 (v := reg m 20) (lowSep (gLow 0x78 (by omega)) (by decide) (by decide))
  obtain ⟨M6, hM6⟩ : ∃ M6, memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (m.mem) (G + 0x8C) (reg m ra)) (G + 0x88) (reg m 8)) (G + 0x84) (reg m 9)) (G + 0x80) (reg m 18)) (G + 0x7C) (reg m 19)) (G + 0x78) (reg m 20) = M6 := ⟨_, rfl⟩
  have hM6' : memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (m.mem) (G + BitVec.ofNat 32 0x8C) (reg m ra)) (G + BitVec.ofNat 32 0x88) (reg m 8)) (G + BitVec.ofNat 32 0x84) (reg m 9)) (G + BitVec.ofNat 32 0x80) (reg m 18)) (G + BitVec.ofNat 32 0x7C) (reg m 19)) (G + BitVec.ofNat 32 0x78) (reg m 20) = M6 := hM6
  rw [hM6] at t7
  have hcM : CodeIn M6 BW bootMainClosure1Code := by rw [← hM6]; exact hc7
  have M6out : ∀ x, Sep S (0x90 + romStack) x 1 → M6 x = m.mem x := fun x hx => by
    rw [← hM6']
    rw [memStore32_get_sep (fr 0x78 4 (by omega) x 1 hx), memStore32_get_sep (fr 0x7C 4 (by omega) x 1 hx), memStore32_get_sep (fr 0x80 4 (by omega) x 1 hx), memStore32_get_sep (fr 0x84 4 (by omega) x 1 hx), memStore32_get_sep (fr 0x88 4 (by omega) x 1 hx), memStore32_get_sep (fr 0x8C 4 (by omega) x 1 hx)]
  have fl8c : memLoad32 M6 (G + 0x8C) = reg m ra := by
    rw [← hM6]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x78) (n := 4) (d := 0x8C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x7C) (n := 4) (d := 0x8C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x80) (n := 4) (d := 0x8C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x84) (n := 4) (d := 0x8C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x88) (n := 4) (d := 0x8C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl88 : memLoad32 M6 (G + 0x88) = reg m 8 := by
    rw [← hM6]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x78) (n := 4) (d := 0x88) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x7C) (n := 4) (d := 0x88) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x80) (n := 4) (d := 0x88) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x84) (n := 4) (d := 0x88) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl84 : memLoad32 M6 (G + 0x84) = reg m 9 := by
    rw [← hM6]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x78) (n := 4) (d := 0x84) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x7C) (n := 4) (d := 0x84) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x80) (n := 4) (d := 0x84) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl80 : memLoad32 M6 (G + 0x80) = reg m 18 := by
    rw [← hM6]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x78) (n := 4) (d := 0x80) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x7C) (n := 4) (d := 0x80) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl7c : memLoad32 M6 (G + 0x7C) = reg m 19 := by
    rw [← hM6]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x78) (n := 4) (d := 0x7C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl78 : memLoad32 M6 (G + 0x78) = reg m 20 := by
    rw [← hM6]
    exact memLoad32_store32_same _ _ _
  have codeOf : ∀ Mx : Word → BitVec 8, (∀ x, Sep S (0x90 + romStack) x 1 → Mx x = m.mem x) → BWCode Mx := by
    intro Mx hO
    have h : ∀ x : Word, 0x40000000 ≤ x.toNat → Mx x = m.mem x := fun x hx => hO x (hiS x hx)
    exact ⟨code.self.hi h (by decide) (by decide), code.memset.hi h (by decide) (by decide),
      code.copy.hi h (by decide) (by decide), code.stub.hi h (by decide) (by decide),
      code.body.hi h (by decide) (by decide), code.crc.hi h (by decide) (by decide),
      fun i hi => by
        have hi' : i < 4 := hi
        rw [hO _ (hSm.subR (c := i) (l := 1) (by omega))]; exact code.magic i hi,
      fun i hi => by
        have hi' : i < 2 := hi
        rw [hO _ (hSv.subR (c := i) (l := 1) (by omega))]; exact code.version i hi⟩
  have romOf : ∀ Mx : Word → BitVec 8, (∀ x, Sep S (0x90 + romStack) x 1 → Mx x = m.mem x) →
      CodeIn Mx romBase romCode := fun Mx hO => hrom.hi (fun x hx => hO x (hiS x hx)) hrb hrl
  have stb : ∀ i, i < 8 → Sep S (0x90 + romStack) (st + BitVec.ofNat 32 i) 1 := fun i hi =>
    (hst.sub (c := i) (l := 1) (by omega)).symm
  -- 0x0E to 0x1C, then `memset` of the record at `G`.
  obtain ⟨m8, e8, t8⟩ := t7.alu hcM bw_at_e (off' := 0x10) (by decide)
  have u8 := t8.self
  obtain ⟨m9, e9, t9⟩ := u8.alu hcM bw_at_10 (off' := 0x12) (by decide)
  have u9 := t9.self
  obtain ⟨m10, e10, t10⟩ := u9.aluImm hcM bw_at_12 (off' := 0x14) (by decide)
  have u10 := t10.self
  obtain ⟨m11, e11, t11⟩ := u10.alu hcM bw_at_14 (off' := 0x16) (by decide)
  have u11 := t11.self
  obtain ⟨m12, e12, t12⟩ := u11.aluImm hcM bw_at_16 (off' := 0x1A) (by decide)
  have u12 := t12.self
  obtain ⟨m13, e13, t13⟩ := u12.alu hcM bw_at_1a (off' := 0x1C) (by decide)
  have u13 := t13.self
  obtain ⟨m14, e14, t14⟩ := u13.aluImm hcM bw_at_1c (off' := 0x20) (by decide)
  have u14 := t14.self
  have v14 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ sp → reg m14 r = reg m r :=
    fun r h0 h1 h2 h9 h18 h19 h20 hs => by
      rw [t14.regs, updz u13.zero h20, t13.regs, updz u12.zero h19, t12.regs, updz u11.zero h2, t11.regs,
        updz u10.zero h0, t10.regs, updz u9.zero h1, t9.regs, updz u8.zero h18, t8.regs, updz t7.zero h9, f1 r hs]
  have sp14 : reg m14 sp = G := by
    simp +decide only [t14.regs, t13.regs, t12.regs, t11.regs, t10.regs, t9.regs, t8.regs, upd, ite_true, ite_false]
  have s1_14 : reg m14 9 = st := by
    simp +decide only [t14.regs, t13.regs, t12.regs, t11.regs, t10.regs, t9.regs, t8.regs, upd, ite_true, ite_false]
    rw [ha1]; exact BitVec.zero_add st
  have s2_14 : reg m14 18 = copy := by
    simp +decide only [t14.regs, t13.regs, t12.regs, t11.regs, t10.regs, t9.regs, upd, ite_true, ite_false]
    rw [show reg m8 x0 = 0 from u8.zero, t8.regs, updz t7.zero (by decide), f1 a0 (by decide), ha0]
    exact BitVec.zero_add copy
  have a0_14 : reg m14 a0 = G := by
    simp +decide only [t14.regs, t13.regs, t12.regs, t11.regs, upd, ite_true, ite_false]
    rw [show reg m10 x0 = 0 from u10.zero, t10.regs, updz u9.zero (by decide), t9.regs, updz u8.zero (by decide),
      t8.regs, updz t7.zero (by decide)]
    rw [u1sp]; exact BitVec.zero_add G
  have a1_14 : reg m14 a1 = 0 := by
    simp +decide only [t14.regs, t13.regs, t12.regs, t11.regs, t10.regs, upd, ite_true, ite_false]
    rw [show reg m9 x0 = 0 from u9.zero]; rfl
  have a2_14 : reg m14 a2 = BitVec.ofNat 32 32 := by
    simp +decide only [t14.regs, t13.regs, t12.regs, upd, ite_true, ite_false]
    rw [show reg m11 x0 = 0 from u11.zero]; rfl
  have s3_14 : reg m14 19 = G := by
    simp +decide only [t14.regs, t13.regs, upd, ite_true, ite_false]
    rw [show reg m12 x0 = 0 from u12.zero, t12.regs, updz u11.zero (by decide), t11.regs, updz u10.zero (by decide),
      t10.regs, updz u9.zero (by decide), t9.regs, updz u8.zero (by decide), t8.regs, updz t7.zero (by decide)]
    rw [u1sp]; exact BitVec.zero_add G
  have s4_14 : reg m14 20 = 0x20 := by
    simp +decide only [t14.regs, upd, ite_true, ite_false]; rw [show reg m13 x0 = 0 from u13.zero]; rfl
  have pre14 : Steps m m14 := .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8
    (.cons e9 (.cons e10 (.cons e11 (.cons e12 (.cons e13 (.single e14)))))))))))))
  obtain ⟨m15, c15, pc15, mem15, regs15⟩ := u14.callRa (cb := BitVec.ofNat 32 memsetAddress) hcM bw_at_20 bw_at_24
    (by decide) (by decide)
  have r15 : ∀ r, r ≠ ra → reg m15 r = reg m14 r := fun r h => by rw [regs15]; exact updz u14.zero h
  obtain ⟨m16, c16, pc16, mem16, a016, k16⟩ := memset_correct m15 (BitVec.ofNat 32 memsetAddress)
    (BW + BitVec.ofNat 32 (0x20 + 8)) G 0 32 (fun i hi => by rw [mem15]; exact (codeOf M6 M6out).memset i hi)
    (by decide) pc15 (by rw [r15 a0 (by decide)]; exact a0_14) (by rw [r15 a1 (by decide)]; exact a1_14)
    (by rw [r15 a2 (by decide)]; exact a2_14) (by rw [regs15]; simp +decide [upd]) (even_clear _ (by decide))
    (by omega) (lowSep (by omega) (by decide) (by decide))
  rw [mem15, show (0 : Word).extractLsb' 0 8 = (0 : BitVec 8) from rfl] at mem16
  obtain ⟨M7, hM7⟩ : ∃ M7, fillBytes M6 G 0 32 = M7 := ⟨_, rfl⟩
  rw [hM7] at mem16
  have M7out : ∀ x, Sep S (0x90 + romStack) x 1 → M7 x = m.mem x := fun x hx => by
    rw [← hM7, fillBytes_sep (n := 32) (by have := fr 0 32 (by omega) x 1 hx; rwa [add_ofNat_zero] at this)
      (Nat.le_refl _)]
    exact M6out x hx
  have t16 : St M7 BW m16 0x28 (reg m16) := ⟨by rw [pc16], mem16, fun _ => rfl⟩
  have g16 : ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ ra → reg m16 r = reg m14 r :=
    fun r h2 h3 h4 h5 h6 hr => by rw [k16 r h2 h3 h4 h5 h6, r15 r hr]
  have hcM7 := (codeOf M7 M7out).self
  have tb : M7 (st + 4) = m.mem (st + 4) := M7out _ (stb 4 (by omega))
  have bb : M7 (st + 5) = m.mem (st + 5) := M7out _ (stb 5 (by omega))
  have cont48 : ∀ (n : Machine) (g : Fin 32 → Word), Steps m n → St M7 BW n 0x48 g → g sp = G → g 9 = st →
      g 18 = copy → g 19 = G → g 20 = 0x20 → g a0 = 2 → g a1 = (bwTrial m.mem st).zeroExtend 32 →
      g a2 = (bwBoots m.mem st).zeroExtend 32 →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 20 →
        r ≠ sp → r ≠ ra → g r = reg m r) →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ (∀ q, romKeep q = true → reg m' q = reg m q) ∧
        ∀ x, Sep S (0x90 + romStack) x 1 → m'.mem x = m.mem x := by
    intro n g hn s hsp h9 h18 h19 h20 hga0 hga1 hga2 hk
    have gal : ∀ c : Word, c.toNat % 4 = 0 → (G + c).toNat % 4 = 0 := fun c h => by
      have := aligned_add hGa (k := c.toNat) h; rwa [ofNat_toNat_w] at this
    have hOP : ∀ Mx : Word → BitVec 8, (∀ x, Sep S (romStack + 0x78) x 1 → Mx x = M6 x) →
        ∀ x, Sep S (0x90 + romStack) x 1 → Mx x = m.mem x := fun Mx hP x hx =>
      (hP x (fun i hi j hj => hx i (by omega) j hj)).trans (M6out x hx)
    have hGt : G.toNat = S.toNat + romStack := by rw [hGn, hSn]; omega
    have hiP : ∀ c j, 0x78 ≤ c → c + j < 0x90 →
        Sep S (romStack + 0x78) (G + BitVec.ofNat 32 c + BitVec.ofNat 32 j) 1 := fun c j h1 h2 =>
      sep_of_le (by rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)
        (by have := (G + BitVec.ofNat 32 c + BitVec.ofNat 32 j).isLt; omega)
    have sl : ∀ Mx : Word → BitVec 8, (∀ x, Sep S (romStack + 0x78) x 1 → Mx x = M6 x) → ∀ c, 0x78 ≤ c →
        c + 4 ≤ 0x90 → memLoad32 Mx (G + BitVec.ofNat 32 c) = memLoad32 M6 (G + BitVec.ofNat 32 c) :=
      fun Mx hP c h1 h2 => memLoad32_congr fun j hj => hP _ (hiP c j h1 (by omega))
    have epi : ∀ (n : Machine) (Mx : Word → BitVec 8) (g : Fin 32 → Word), Steps m n → St Mx BW n 0x1A2 g →
        g sp = G → (∀ x, Sep S (romStack + 0x78) x 1 → Mx x = M6 x) → (∀ r, r ≠ sp → r ≠ ra → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 20 → romKeep r = true → g r = reg m r) → (∃ m', Steps m m' ∧ m'.pc = retAddr ∧ (∀ q, romKeep q = true → reg m' q = reg m q) ∧
          ∀ x, Sep S (0x90 + romStack) x 1 → m'.mem x = m.mem x) := by
      intro n Mx g hn s hgs hP hk
      have hc := (codeOf Mx (hOP Mx hP)).self
      obtain ⟨n1, d1, u1⟩ := s.lwE hc bw_at_1a2 (off' := 0x1A4) (by decide) (by rw [hgs]; exact gal _ (by decide))
        (v := reg m ra) (by rw [hgs]; exact (sl Mx hP 0x8C (by omega) (by omega)).trans fl8c)
      obtain ⟨n2, d2, u2⟩ := u1.lwE hc bw_at_1a4 (off' := 0x1A6) (by decide)
        (by simp +decide only [upd, ite_true, ite_false]; rw [hgs]; exact gal _ (by decide)) (v := reg m 8)
        (by simp +decide only [upd, ite_true, ite_false]; rw [hgs]; exact (sl Mx hP 0x88 (by omega) (by omega)).trans fl88)
      obtain ⟨n3, d3, u3⟩ := u2.lwE hc bw_at_1a6 (off' := 0x1A8) (by decide)
        (by simp +decide only [upd, ite_true, ite_false]; rw [hgs]; exact gal _ (by decide)) (v := reg m 9)
        (by simp +decide only [upd, ite_true, ite_false]; rw [hgs]; exact (sl Mx hP 0x84 (by omega) (by omega)).trans fl84)
      obtain ⟨n4, d4, u4⟩ := u3.lwE hc bw_at_1a8 (off' := 0x1AA) (by decide)
        (by simp +decide only [upd, ite_true, ite_false]; rw [hgs]; exact gal _ (by decide)) (v := reg m 18)
        (by simp +decide only [upd, ite_true, ite_false]; rw [hgs]; exact (sl Mx hP 0x80 (by omega) (by omega)).trans fl80)
      obtain ⟨n5, d5, u5⟩ := u4.lwE hc bw_at_1aa (off' := 0x1AC) (by decide)
        (by simp +decide only [upd, ite_true, ite_false]; rw [hgs]; exact gal _ (by decide)) (v := reg m 19)
        (by simp +decide only [upd, ite_true, ite_false]; rw [hgs]; exact (sl Mx hP 0x7C (by omega) (by omega)).trans fl7c)
      obtain ⟨n6, d6, u6⟩ := u5.lwE hc bw_at_1ac (off' := 0x1AE) (by decide)
        (by simp +decide only [upd, ite_true, ite_false]; rw [hgs]; exact gal _ (by decide)) (v := reg m 20)
        (by simp +decide only [upd, ite_true, ite_false]; rw [hgs]; exact (sl Mx hP 0x78 (by omega) (by omega)).trans fl78)
      obtain ⟨n7, d7, u7⟩ := u6.aluImm hc bw_at_1ae (off' := 0x1B0) (by decide)
      obtain ⟨n8, d8, pc8, mem8, regs8⟩ := u7.jalr hc bw_at_1b0
      refine ⟨n8, hn.trans (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.single d8)))))))),
        ?_, ?_, ?_⟩
      · rw [pc8]; simp +decide only [upd, ite_true, ite_false]
        rw [show reg m ra + 0 = reg m ra from BitVec.add_zero _, hra]; exact hret
      · intro q hq
        have hr : q ≠ ra := by rintro rfl; exact absurd hq (by decide)
        rw [regs8]
        by_cases e0 : q = sp
        · subst e0; simp +decide only [upd, ite_true, ite_false, aluEval]; rw [hgs]; exact hspG
        by_cases e1 : q = 8
        · subst e1; simp +decide only [upd, ite_true, ite_false]
        by_cases e2 : q = 9
        · subst e2; simp +decide only [upd, ite_true, ite_false]
        by_cases e3 : q = 18
        · subst e3; simp +decide only [upd, ite_true, ite_false]
        by_cases e4 : q = 19
        · subst e4; simp +decide only [upd, ite_true, ite_false]
        by_cases e5 : q = 20
        · subst e5; simp +decide only [upd, ite_true, ite_false]
        simp only [upd, e0, e1, e2, e3, e4, e5, hr, if_false]
        split
        · rename_i h; rw [show q = 0 from Fin.ext h]; exact hz.symm
        · exact hk q e0 hr e1 e2 e3 e4 e5 hq
      · intro x hx; rw [mem8]; exact hOP Mx hP x hx
    have romcall : ∀ (F : Word) (pre : Machine → Prop) (n : Machine) (Mx : Word → BitVec 8) (g : Fin 32 → Word)
        (off : Nat) (imm o : Word), RomFn romBase romCode F romStack pre → St Mx BW n off g → g sp = G →
        (∀ x, Sep S (0x90 + romStack) x 1 → Mx x = m.mem x) →
        fetchRel bootMainClosure1Code off = some (.auipc ra imm, 4) →
        fetchRel bootMainClosure1Code (off + 4) = some (.jalr ra ra o, 4) →
        BW + BitVec.ofNat 32 off + imm + o = F → F.toNat % 2 = 0 → (BW + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0 →
        (∀ n1 : Machine, n1.mem = Mx → (∀ r, reg n1 r = upd g ra (BW + BitVec.ofNat 32 (off + 8)) r) → pre n1) →
        ∃ n', Steps n n' ∧ St n'.mem BW n' (off + 8) (reg n') ∧
          (∀ x, Sep S romStack x 1 → n'.mem x = Mx x) ∧ (∀ q, romKeep q = true → reg n' q = g q) := by
      intro F pre n Mx g off imm o hF s hgs hO h1 h2 hb he he8 hpre
      obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa (codeOf Mx hO).self h1 h2 hb he
      have sp1 : reg n1 sp = G := by rw [regs1, updz s.zero (by decide)]; exact hgs
      obtain ⟨n2, c2, pc2, keep2, mem2⟩ := hF n1 (by rw [mem1]; exact romOf Mx hO) pc1 (hpre n1 mem1 regs1)
        (by rw [sp1, hGt]; omega)
      have hS : reg n1 sp - BitVec.ofNat 32 romStack = S := by rw [sp1, hGS, BitVec.add_sub_cancel]
      refine ⟨n2, c1.trans c2, ⟨?_, rfl, fun _ => rfl⟩, fun x hx => ?_, fun q hq => ?_⟩
      · rw [pc2, regs1]; simp +decide only [upd, ite_true, ite_false]; exact even_clear _ he8
      · rw [mem2 x (by rw [hS]; exact hx), mem1]
      · rw [keep2 q hq, regs1]; exact updz s.zero (by rintro rfl; exact absurd hq (by decide))
    have logp : ∀ (n : Machine) (Mx : Word → BitVec 8) (g : Fin 32 → Word), Steps m n → St Mx BW n 0x190 g →
        g sp = G → (∀ x, Sep S (romStack + 0x78) x 1 → Mx x = M6 x) → (∀ r, r ≠ sp → r ≠ ra → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 20 → romKeep r = true → g r = reg m r) → (∃ m', Steps m m' ∧ m'.pc = retAddr ∧ (∀ q, romKeep q = true → reg m' q = reg m q) ∧
          ∀ x, Sep S (0x90 + romStack) x 1 → m'.mem x = m.mem x) := by
      intro n Mx g hn s hgs hP hk
      have hc := (codeOf Mx (hOP Mx hP)).self
      obtain ⟨n1, d1, u1⟩ := s.lui hc bw_at_190 (off' := 0x194) (by decide)
      obtain ⟨n2, d2, u2⟩ := u1.aluImm hc bw_at_194 (off' := 0x198) (by decide)
      obtain ⟨n3, d3, u3⟩ := u2.aluImm hc bw_at_198 (off' := 0x19A) (by decide)
      obtain ⟨n4, c4, t4, mem4, keep4⟩ := romcall 0x40000040 _ n3 Mx _ 0x19A _ _ log u3
        (by simp +decide only [upd, ite_true, ite_false]; exact hgs) (hOP Mx hP) bw_at_19a bw_at_19e
        (by decide) (by decide) (by decide) (fun _ _ _ => trivial)
      refine epi n4 n4.mem (reg n4) (hn.trans (.cons d1 (.cons d2 (.cons d3 c4)))) t4 ?_ ?_ ?_
      · rw [keep4 sp (by decide)]; simp +decide only [upd, ite_true, ite_false]; exact hgs
      · intro x hx; rw [mem4 x (fun i hi j hj => hx i (by omega) j hj)]; exact hP x hx
      · intro r h0 h1 h2 h3 h4 h5 h6 hq
        have ra0 : r ≠ a0 := by rintro rfl; exact absurd hq (by decide)
        have ra1 : r ≠ a1 := by rintro rfl; exact absurd hq (by decide)
        rw [keep4 r hq, updz (upd_zero _ _ _) ra1, updz (upd_zero _ _ _) ra0, updz s.zero ra0]
        exact hk r h0 h1 h2 h3 h4 h5 h6 hq
    have recSep : ∀ i, i < 32 → Sep S romStack (G + 0x28 + BitVec.ofNat 32 i) 1 := fun i hi =>
      sep_of_le (by
          rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, show (0x28 : Word).toNat = 0x28 from rfl]
          omega)
        (by have := (G + 0x28 + BitVec.ofNat 32 i).isLt; omega)
    have rtail : ∀ (n : Machine) (Mx : Word → BitVec 8) (g : Fin 32 → Word), Steps m n → St Mx BW n 0x14E g →
        g sp = G → g 18 = copy → (∀ x, Sep S (romStack + 0x78) x 1 → Mx x = M6 x) →
        (∀ i, i < 32 → Mx (G + 0x28 + BitVec.ofNat 32 i) = bwRec m.mem st i) → (∀ r, r ≠ sp → r ≠ ra → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 20 → romKeep r = true → g r = reg m r) → (∃ m', Steps m m' ∧ m'.pc = retAddr ∧ (∀ q, romKeep q = true → reg m' q = reg m q) ∧
          ∀ x, Sep S (0x90 + romStack) x 1 → m'.mem x = m.mem x) := by
      intro n Mx g hn s hgs h18 hP hR hk
      have hO := hOP Mx hP
      have hc := (codeOf Mx hO).self
      have at15c : ∀ (n' : Machine) (g' : Fin 32 → Word), Steps m n' → St Mx BW n' 0x15C g' → g' sp = G →
          g' 8 = bwAddr copy → (∀ r, r ≠ sp → r ≠ ra → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 20 → romKeep r = true → g' r = reg m r) → (∃ m', Steps m m' ∧ m'.pc = retAddr ∧ (∀ q, romKeep q = true → reg m' q = reg m q) ∧
          ∀ x, Sep S (0x90 + romStack) x 1 → m'.mem x = m.mem x) := by
        intro n' g' hn' s' hgs' h8 hk'
        -- unlock
        obtain ⟨n1, c1, t1, mem1, keep1⟩ := romcall 0x40000140 _ n' Mx g' 0x15C _ _ unlock s' hgs' hO
          bw_at_15c bw_at_160 (by decide) (by decide) (by decide) (fun _ _ _ => trivial)
        have sp1 : reg n1 sp = G := (keep1 sp (by decide)).trans hgs'
        have s01 : reg n1 8 = bwAddr copy := (keep1 8 (by decide)).trans h8
        have P1 : ∀ x, Sep S (romStack + 0x78) x 1 → n1.mem x = M6 x := fun x hx => by
          rw [mem1 x (fun i hi j hj => hx i (by omega) j hj)]; exact hP x hx
        have k1 : (∀ r, r ≠ sp → r ≠ ra → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 20 → romKeep r = true → (reg n1) r = reg m r) := fun r h0 h1 h2 h3 h4 h5 h6 hq =>
          (keep1 r hq).trans (hk' r h0 h1 h2 h3 h4 h5 h6 hq)
        have hc1 := (codeOf n1.mem (hOP n1.mem P1)).self
        by_cases e1 : reg n1 a0 ≠ 0
        · obtain ⟨n2, d2, u2⟩ := t1.taken hc1 0x190 bw_at_164 (by decide)
            (by show (reg n1 a0 != reg n1 x0) = true; rw [t1.zero]; exact bne_iff_ne.mpr e1)
          exact logp n2 n1.mem (reg n1) (hn'.trans (c1.trans (.single d2))) u2 sp1 P1 k1
        obtain ⟨n2, d2, u2⟩ := t1.notTaken hc1 0x166 bw_at_164 (by decide)
          (by show (reg n1 a0 != reg n1 x0) = false; rw [t1.zero, Decidable.not_not.mp e1]; rfl)
        obtain ⟨n3, d3, u3⟩ := u2.aluImm hc1 bw_at_166 (off' := 0x16A) (by decide)
        -- erase
        obtain ⟨n4, c4, t4, mem4, keep4⟩ := romcall 0x40000128 _ n3 n1.mem _ 0x16A _ _ erase u3
          (by rw [updz t1.zero (by decide)]; exact sp1) (hOP n1.mem P1) bw_at_16a bw_at_16e (by decide) (by decide)
          (by decide) (fun n5 _ hr => by
            rw [hr]; simp +decide only [upd, ite_true, ite_false, aluEval]; rw [s01]; rfl)
        have sp4 : reg n4 sp = G := by rw [keep4 sp (by decide), updz t1.zero (by decide)]; exact sp1
        have s04 : reg n4 8 = bwAddr copy := by rw [keep4 8 (by decide), updz t1.zero (by decide)]; exact s01
        have M4 : ∀ x, Sep S romStack x 1 → n4.mem x = Mx x := fun x hx => by rw [mem4 x hx, mem1 x hx]
        have P4 : ∀ x, Sep S (romStack + 0x78) x 1 → n4.mem x = M6 x := fun x hx => by
          rw [M4 x (fun i hi j hj => hx i (by omega) j hj)]; exact hP x hx
        have k4 : (∀ r, r ≠ sp → r ≠ ra → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 20 → romKeep r = true → (reg n4) r = reg m r) := fun r h0 h1 h2 h3 h4 h5 h6 hq => by
          rw [keep4 r hq, updz t1.zero (by rintro rfl; exact absurd hq (by decide))]; exact k1 r h0 h1 h2 h3 h4 h5 h6 hq
        have hc4 := (codeOf n4.mem (hOP n4.mem P4)).self
        by_cases e4 : reg n4 a0 ≠ 0
        · obtain ⟨n5, d5, u5⟩ := t4.taken hc4 0x190 bw_at_172 (by decide)
            (by show (reg n4 a0 != reg n4 x0) = true; rw [t4.zero]; exact bne_iff_ne.mpr e4)
          exact logp n5 n4.mem (reg n4) (hn'.trans (c1.trans (.cons d2 (.cons d3 (c4.trans (.single d5)))))) u5 sp4 P4 k4
        obtain ⟨n5, d5, u5⟩ := t4.notTaken hc4 0x174 bw_at_172 (by decide)
          (by show (reg n4 a0 != reg n4 x0) = false; rw [t4.zero, Decidable.not_not.mp e4]; rfl)
        -- unlock again
        obtain ⟨n6, c6, t6, mem6, keep6⟩ := romcall 0x40000140 _ n5 n4.mem (reg n4) 0x174 _ _ unlock u5 sp4
          (hOP n4.mem P4) bw_at_174 bw_at_178 (by decide) (by decide) (by decide) (fun _ _ _ => trivial)
        have sp6 : reg n6 sp = G := (keep6 sp (by decide)).trans sp4
        have s06 : reg n6 8 = bwAddr copy := (keep6 8 (by decide)).trans s04
        have M6' : ∀ x, Sep S romStack x 1 → n6.mem x = Mx x := fun x hx => by rw [mem6 x hx, M4 x hx]
        have P6 : ∀ x, Sep S (romStack + 0x78) x 1 → n6.mem x = M6 x := fun x hx => by
          rw [M6' x (fun i hi j hj => hx i (by omega) j hj)]; exact hP x hx
        have k6 : (∀ r, r ≠ sp → r ≠ ra → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 20 → romKeep r = true → (reg n6) r = reg m r) := fun r h0 h1 h2 h3 h4 h5 h6 hq =>
          (keep6 r hq).trans (k4 r h0 h1 h2 h3 h4 h5 h6 hq)
        have hc6 := (codeOf n6.mem (hOP n6.mem P6)).self
        have pre6 : Steps m n6 := hn'.trans (c1.trans (.cons d2 (.cons d3 (c4.trans (.cons d5 c6)))))
        by_cases e6 : reg n6 a0 ≠ 0
        · obtain ⟨n7, d7, u7⟩ := t6.taken hc6 0x190 bw_at_17c (by decide)
            (by show (reg n6 a0 != reg n6 x0) = true; rw [t6.zero]; exact bne_iff_ne.mpr e6)
          exact logp n7 n6.mem (reg n6) (pre6.trans (.single d7)) u7 sp6 P6 k6
        obtain ⟨n7, d7, u7⟩ := t6.notTaken hc6 0x17E bw_at_17c (by decide)
          (by show (reg n6 a0 != reg n6 x0) = false; rw [t6.zero, Decidable.not_not.mp e6]; rfl)
        obtain ⟨n8, d8, u8⟩ := u7.aluImm hc6 bw_at_17e (off' := 0x180) (by decide)
        obtain ⟨n9, d9, u9⟩ := u8.aluImm hc6 bw_at_180 (off' := 0x184) (by decide)
        obtain ⟨n10, d10, u10⟩ := u9.alu hc6 bw_at_184 (off' := 0x186) (by decide)
        -- write
        obtain ⟨n11, c11, t11, mem11, keep11⟩ := romcall 0x4000012C _ n10 n6.mem _ 0x186 _ _ write u10
          (by simp +decide only [upd, ite_true, ite_false]; exact sp6) (hOP n6.mem P6) bw_at_186 bw_at_18a
          (by decide) (by decide) (by decide) (fun n12 hm hr => by
            refine ⟨?_, ?_, fun i hi => ?_⟩
            · rw [hr]; simp +decide only [upd, ite_true, ite_false, aluEval]; rw [s06]; exact BitVec.zero_add _
            · rw [hr]; simp +decide only [upd, ite_true, ite_false, aluEval]
            · rw [hm, hr]; simp +decide only [upd, ite_true, ite_false, aluEval]; rw [sp6, M6' _ (recSep i hi)]
              exact hR i hi)
        have kk : ∀ q, romKeep q = true → reg n11 q = reg n6 q := fun q hq => by
          have ra0 : q ≠ a0 := by rintro rfl; exact absurd hq (by decide)
          have ra1 : q ≠ a1 := by rintro rfl; exact absurd hq (by decide)
          have ra2 : q ≠ a2 := by rintro rfl; exact absurd hq (by decide)
          rw [keep11 q hq, updz (upd_zero _ _ _) ra0, updz (upd_zero _ _ _) ra2, updz t6.zero ra1]
        have sp11 : reg n11 sp = G := (kk sp (by decide)).trans sp6
        have P11 : ∀ x, Sep S (romStack + 0x78) x 1 → n11.mem x = M6 x := fun x hx => by
          rw [mem11 x (fun i hi j hj => hx i (by omega) j hj)]; exact P6 x hx
        have k11 : (∀ r, r ≠ sp → r ≠ ra → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 20 → romKeep r = true → (reg n11) r = reg m r) := fun r h0 h1 h2 h3 h4 h5 h6 hq =>
          (kk r hq).trans (k6 r h0 h1 h2 h3 h4 h5 h6 hq)
        have hc11 := (codeOf n11.mem (hOP n11.mem P11)).self
        have pre11 : Steps m n11 := pre6.trans (.cons d7 (.cons d8 (.cons d9 (.cons d10 c11))))
        by_cases e11 : reg n11 a0 = 0
        · obtain ⟨n12, d12, u12⟩ := t11.taken hc11 0x1A2 bw_at_18e (by decide)
            (by show (reg n11 a0 == reg n11 x0) = true; rw [t11.zero, e11]; rfl)
          exact epi n12 n11.mem (reg n11) (pre11.trans (.single d12)) u12 sp11 P11 k11
        · obtain ⟨n12, d12, u12⟩ := t11.notTaken hc11 0x190 bw_at_18e (by decide)
            (by show (reg n11 a0 == reg n11 x0) = false; rw [t11.zero]; exact beq_eq_false_iff_ne.mpr e11)
          exact logp n12 n11.mem (reg n11) (pre11.trans (.single d12)) u12 sp11 P11 k11
      obtain ⟨n1, d1, u1⟩ := s.aluImm hc bw_at_14e (off' := 0x152) (by decide)
      obtain ⟨n2, d2, u2⟩ := u1.lui hc bw_at_152 (off' := 0x156) (by decide)
      have kk : ∀ v w : Word, (∀ r, r ≠ sp → r ≠ ra → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 20 → romKeep r = true → (upd (upd g a0 v) 8 w) r = reg m r) := fun v w r h0 h1 h2 h3 h4 h5 h6 hq => by
        rw [updz (upd_zero _ _ _) h2, updz s.zero (by rintro rfl; exact absurd hq (by decide))]
        exact hk r h0 h1 h2 h3 h4 h5 h6 hq
      by_cases ec : copy &&& 0xFF = 0
      · obtain ⟨n3, d3, u3⟩ := u2.taken hc 0x15C bw_at_156 (by decide)
          (by simp +decide only [upd, ite_true, ite_false, aluEval]; rw [h18, ec]; rfl)
        refine at15c n3 _ (hn.trans (.cons d1 (.cons d2 (.single d3)))) u3 ?_ ?_ (kk _ _)
        · simp +decide only [upd, ite_true, ite_false]; exact hgs
        · simp +decide only [upd, ite_true, ite_false, bwAddr, ec]
      · obtain ⟨n3, d3, u3⟩ := u2.notTaken hc 0x158 bw_at_156 (by decide)
          (by simp +decide only [upd, ite_true, ite_false, aluEval]; rw [h18]; exact beq_eq_false_iff_ne.mpr ec)
        obtain ⟨n4, d4, u4⟩ := u3.lui hc bw_at_158 (off' := 0x15C) (by decide)
        refine at15c n4 _ (hn.trans (.cons d1 (.cons d2 (.cons d3 (.single d4))))) u4 ?_ ?_ ?_
        · simp +decide only [upd, ite_true, ite_false]; exact hgs
        · simp +decide only [upd, ite_true, ite_false, bwAddr, ec]
        · intro r h0 h1 h2 h3 h4 h5 h6 hq
          rw [updz (upd_zero _ _ _) h2]; exact kk _ _ r h0 h1 h2 h3 h4 h5 h6 hq
    have glo : ∀ c k, c + 4 ≤ 0x90 → k ≤ 4 → Sep (G + BitVec.ofNat 32 c) k BW bootMainClosure1Code.length :=
      fun c k h hk => lowSep (by have := gLow c h; omega) (by decide) (by decide)
    have glo' : ∀ (c : Word) k, c.toNat + 4 ≤ 0x90 → k ≤ 4 → Sep (G + c) k BW bootMainClosure1Code.length :=
      fun c k h hk => by have := glo c.toNat k h hk; rwa [ofNat_toNat_w] at this
    have gal' : ∀ c : Word, c.toNat % 4 = 0 → (G + c).toNat % 4 = 0 := fun c h => by
      have := aligned_add hGa (k := c.toNat) h; rwa [ofNat_toNat_w] at this
    obtain ⟨n1, d1, u1⟩ := s.block bwBlk hcM7 bwBlk_end (by
      simp only [BlockOk, BInstr.ok, BInstr.run, bwBlk]
      simp +decide only [upd, ↓reduceIte]
      rw [hsp, h9]
      refine ⟨by rw [add_lit_zero]; exact hsta, ?_⟩
      repeat' (first | exact trivial | constructor)
      all_goals first
        | exact gal' _ (by decide)
        | exact glo' _ _ (by decide) (by decide))
    have hm := u1.mem
    simp only [runBlock, BInstr.run, bwBlk] at hm
    simp +decide only [upd, ↓reduceIte] at hm
    rw [hsp, h9] at hm
    have hr : ∀ r, reg n1 r = (runBlock bwBlk (M7, g)).2 r := fun r => by rw [u1.regs]
    have fr78 : ∀ c l, c + l ≤ 0x78 → ∀ (x : Word), Sep S (romStack + 0x78) x 1 → Sep (G + BitVec.ofNat 32 c) l x 1 :=
      fun c l h x hx => by rw [hGS, add_ofNat_assoc]; exact hx.sub (c := romStack + c) (l := l) (by omega)
    have fr78w : ∀ (c : Word) l, c.toNat + l ≤ 0x78 → ∀ (x : Word), Sep S (romStack + 0x78) x 1 → Sep (G + c) l x 1 :=
      fun c l h x hx => by have := fr78 c.toNat l h x hx; rwa [ofNat_toNat_w] at this
    have st8o : ∀ (Mx : Word → BitVec 8) (a x : Word) (v : BitVec 8), Sep a 1 x 1 → memStore8 Mx a v x = Mx x :=
      fun Mx a x v h => memStore8_ne fun e => h 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)
    have hO1 : ∀ x, Sep S (romStack + 0x78) x 1 → n1.mem x = M7 x := fun x hx => by
      rw [hm]
      simp (disch := first | exact fr78w _ 4 (by decide) x hx | exact fr78w _ 1 (by decide) x hx) only
        [memStore32_get_sep, st8o]
    have kb : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 8 → r ≠ 9 → reg n1 r = g r :=
      fun r h0 h1 h2 h3 h4 h5 h8 h9' => by
        rw [hr, runBlock_reg _ _ _ r s.zero (by simp only [bwBlk]; revert h0 h1 h2 h3 h4 h5 h8 h9'; revert r; decide)]
    have v8 : reg n1 8 = 6 := by
      rw [hr]; simp +decide only [runBlock, BInstr.run, bwBlk, upd, ↓reduceIte]; (try rw [s.zero]); try rfl
    have v9 : reg n1 9 = G + BitVec.ofNat 32 0x38 := by
      rw [hr]; simp +decide only [runBlock, BInstr.run, bwBlk, upd, ↓reduceIte]; rw [hsp]; rfl
    have hOm1 : ∀ x, Sep S (0x90 + romStack) x 1 → n1.mem x = m.mem x := fun x hx =>
      (hO1 x (fun i hi j hj => hx i (by omega) j hj)).trans (M7out x hx)
    have cd1 := codeOf n1.mem hOm1
    have t1 : St n1.mem BW n1 0xB4 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
    obtain ⟨n2, d2, u2⟩ := t1.notTaken cd1.self 0xB6 bw_at_b4 (by decide)
      (by show (reg n1 8 == reg n1 x0) = false; rw [v8, t1.zero]; rfl)
    have t2 : St n1.mem BW n2 0xB6 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
    have hT : ∀ k, k < 6 → memLoad32 n1.mem (G + BitVec.ofNat 32 (0x30 + 12 * k)) = BitVec.ofNat 32 (bwOff k) ∧
        memLoad32 n1.mem (G + BitVec.ofNat 32 (0x34 + 12 * k)) = bwPtr G k ∧
        memLoad32 n1.mem (G + BitVec.ofNat 32 (0x38 + 12 * k)) = BitVec.ofNat 32 (bwLen k) := by
      intro k hk
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨?_, ?_, ?_⟩
        · show memLoad32 n1.mem (G + (0x30 : Word)) = _; rw [hm]; simp (disch := decide) only [ld_st32_off, ld_st8_off, memLoad32_store32_same]; first | rfl | (rw [hga0]; rfl)
        · show memLoad32 n1.mem (G + (0x34 : Word)) = _; rw [hm]; simp (disch := decide) only [ld_st32_off, ld_st8_off, memLoad32_store32_same]; first | rfl | (rw [hga0]; rfl)
        · show memLoad32 n1.mem (G + (0x38 : Word)) = _; rw [hm]; simp (disch := decide) only [ld_st32_off, ld_st8_off, memLoad32_store32_same]; first | rfl | (rw [hga0]; rfl)
      · refine ⟨?_, ?_, ?_⟩
        · show memLoad32 n1.mem (G + (0x3C : Word)) = _; rw [hm]; simp (disch := decide) only [ld_st32_off, ld_st8_off, memLoad32_store32_same]; first | rfl | (rw [hga0]; rfl)
        · show memLoad32 n1.mem (G + (0x40 : Word)) = _; rw [hm]; simp (disch := decide) only [ld_st32_off, ld_st8_off, memLoad32_store32_same]; first | rfl | (rw [hga0]; rfl)
        · show memLoad32 n1.mem (G + (0x44 : Word)) = _; rw [hm]; simp (disch := decide) only [ld_st32_off, ld_st8_off, memLoad32_store32_same]; first | rfl | (rw [hga0]; rfl)
      · refine ⟨?_, ?_, ?_⟩
        · show memLoad32 n1.mem (G + (0x48 : Word)) = _; rw [hm]; simp (disch := decide) only [ld_st32_off, ld_st8_off, memLoad32_store32_same]; first | rfl | (rw [hga0]; rfl)
        · show memLoad32 n1.mem (G + (0x4C : Word)) = _; rw [hm]; simp (disch := decide) only [ld_st32_off, ld_st8_off, memLoad32_store32_same]; first | rfl | (rw [hga0]; rfl)
        · show memLoad32 n1.mem (G + (0x50 : Word)) = _; rw [hm]; simp (disch := decide) only [ld_st32_off, ld_st8_off, memLoad32_store32_same]; first | rfl | (rw [hga0]; rfl)
      · refine ⟨?_, ?_, ?_⟩
        · show memLoad32 n1.mem (G + (0x54 : Word)) = _; rw [hm]; simp (disch := decide) only [ld_st32_off, ld_st8_off, memLoad32_store32_same]; first | rfl | (rw [hga0]; rfl)
        · show memLoad32 n1.mem (G + (0x58 : Word)) = _; rw [hm]; simp (disch := decide) only [ld_st32_off, ld_st8_off, memLoad32_store32_same]; first | rfl | (rw [hga0]; rfl)
        · show memLoad32 n1.mem (G + (0x5C : Word)) = _; rw [hm]; simp (disch := decide) only [ld_st32_off, ld_st8_off, memLoad32_store32_same]; first | rfl | (rw [hga0]; rfl)
      · refine ⟨?_, ?_, ?_⟩
        · show memLoad32 n1.mem (G + (0x60 : Word)) = _; rw [hm]; simp (disch := decide) only [ld_st32_off, ld_st8_off, memLoad32_store32_same]; first | rfl | (rw [hga0]; rfl)
        · show memLoad32 n1.mem (G + (0x64 : Word)) = _; rw [hm]; simp (disch := decide) only [ld_st32_off, ld_st8_off, memLoad32_store32_same]; first | rfl | (rw [hga0]; rfl)
        · show memLoad32 n1.mem (G + (0x68 : Word)) = _; rw [hm]; simp (disch := decide) only [ld_st32_off, ld_st8_off, memLoad32_store32_same]; first | rfl | (rw [hga0]; rfl)
      · refine ⟨?_, ?_, ?_⟩
        · show memLoad32 n1.mem (G + (0x6C : Word)) = _; rw [hm]; simp (disch := decide) only [ld_st32_off, ld_st8_off, memLoad32_store32_same]; first | rfl | (rw [hga0]; rfl)
        · show memLoad32 n1.mem (G + (0x70 : Word)) = _; rw [hm]; simp (disch := decide) only [ld_st32_off, ld_st8_off, memLoad32_store32_same]; first | rfl | (rw [hga0]; rfl)
        · show memLoad32 n1.mem (G + (0x74 : Word)) = _; rw [hm]; simp (disch := decide) only [ld_st32_off, ld_st8_off, memLoad32_store32_same]; first | rfl | (rw [hga0]; rfl)
    have zx : ∀ x : BitVec 8, (x.zeroExtend 32).extractLsb' 0 8 = x := fun x => by
      apply BitVec.eq_of_toNat_eq
      rw [byte_toNat, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.isLt; omega)]
      have := x.isLt; omega
    have stv : ∀ i, i < 8 → M7 (st + BitVec.ofNat 32 i) = m.mem (st + BitVec.ofNat 32 i) := fun i hi => M7out _ (stb i hi)
    have ldst : memLoad32 M7 (st + 0) = memLoad32 m.mem st := by
      rw [add_lit_zero]; exact memLoad32_congr fun j hj => stv j (by omega)
    have hlS : ∀ (a : Word) (k : Nat), Sep S (0x90 + romStack) a k → ∀ j, j < k → Sep S (romStack + 0x78) (a + BitVec.ofNat 32 j) 1 :=
      fun a k h j hj => fun i hi j' hj' => (h.symm.sub (c := j) (l := 1) hj |>.symm) i (by omega) j' hj'
    have hS : ∀ k, k < 6 → ∀ j, j < bwLen k → n1.mem (bwPtr G k + BitVec.ofNat 32 j) = bwBody m.mem st (bwOff k + j) := by
      intro k hk j hj
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [bwLen] at hj
        show n1.mem (BitVec.ofNat 32 bsMagicAddress + BitVec.ofNat 32 j) = _
        rw [hO1 _ (hlS _ 4 hSm j hj), M7out _ (fun i hi j' hj' => (hSm.symm.sub (c := j) (l := 1) hj |>.symm) i hi j' hj'),
          code.magic j hj]
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
      · simp only [bwLen] at hj
        show n1.mem (BitVec.ofNat 32 bsVersionAddress + BitVec.ofNat 32 j) = _
        rw [hO1 _ (hlS _ 2 hSv j hj), M7out _ (fun i hi j' hj' => (hSv.symm.sub (c := j) (l := 1) hj |>.symm) i hi j' hj'),
          code.version j hj]
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> rfl
      · simp only [bwLen] at hj
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
        · simp only [bwPtr]; rw [add_ofNat_assoc]
          show n1.mem (G + (0x20 : Word)) = _
          rw [hm]; simp (disch := decide) only [get_st32_off, get_st8_off]
          rw [get_st32_j 0 (by decide) (by decide), ldst]; rfl
        · simp only [bwPtr]; rw [add_ofNat_assoc]
          show n1.mem (G + (0x21 : Word)) = _
          rw [hm]; simp (disch := decide) only [get_st32_off, get_st8_off]
          rw [get_st32_j 1 (by decide) (by decide), ldst]; rfl
        · simp only [bwPtr]; rw [add_ofNat_assoc]
          show n1.mem (G + (0x22 : Word)) = _
          rw [hm]; simp (disch := decide) only [get_st32_off, get_st8_off]
          rw [get_st32_j 2 (by decide) (by decide), ldst]; rfl
        · simp only [bwPtr]; rw [add_ofNat_assoc]
          show n1.mem (G + (0x23 : Word)) = _
          rw [hm]; simp (disch := decide) only [get_st32_off, get_st8_off]
          rw [get_st32_j 3 (by decide) (by decide), ldst]; rfl
      · simp only [bwLen] at hj
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
        · simp only [bwPtr]; rw [add_ofNat_assoc]
          show n1.mem (G + (0x24 : Word)) = _
          rw [hm]; simp (disch := decide) only [get_st32_off, get_st8_off, memStore8_same]
          rw [zx, show M7 (st + 7) = m.mem (st + 7) from stv 7 (by decide)]; rfl
        · simp only [bwPtr]; rw [add_ofNat_assoc]
          show n1.mem (G + (0x25 : Word)) = _
          rw [hm]; simp (disch := decide) only [get_st32_off, get_st8_off, memStore8_same]
          rw [hga1, zx]; rfl
      · simp only [bwLen] at hj
        obtain rfl : j = 0 := by omega
        simp only [bwPtr]; rw [add_ofNat_assoc]
        show n1.mem (G + (0x26 : Word)) = _
        rw [hm]; simp (disch := decide) only [get_st32_off, get_st8_off, memStore8_same]
        rw [hga2, zx]; rfl
      · simp only [bwLen] at hj
        obtain rfl : j = 0 := by omega
        simp only [bwPtr]; rw [add_ofNat_assoc]
        show n1.mem (G + (0x27 : Word)) = _
        rw [hm]; simp (disch := decide) only [get_st32_off, get_st8_off, memStore8_same]
        rw [zx, show M7 (st + 6) = m.mem (st + 6) from stv 6 (by decide)]; rfl
    have hGl : 16 ≤ G.toNat := by omega
    have hGh : G.toNat + 0x90 ≤ 0x40000000 := by omega
    have hGc : ∀ c, c ≤ 0x90 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c h => by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hlo : (G + 0xFFFFFFF0).toNat = G.toNat - 16 := by
      rw [BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 2 ^ 32 - 16 from rfl]; omega
    have hG16 : S + BitVec.ofNat 32 (romStack - 16) = G + 0xFFFFFFF0 := BitVec.eq_of_toNat_eq (by
      rw [hlo, BitVec.toNat_add, BitVec.toNat_ofNat, hSn, hGn]; omega)
    have inR : ∀ x, Sep S (romStack + 0x78) x 1 → Sep (G + 0xFFFFFFF0) 0x30 x 1 := fun x hx => by
      have := hx.sub (c := romStack - 16) (l := 0x30) (by omega); rwa [hG16] at this
    have hP : ∀ k, k < 6 → bwPtr G k ≠ 0 ∧ Sep (bwPtr G k) (bwLen k) (G + 0xFFFFFFF0) 0x30 ∧
        (bwPtr G k).toNat + bwLen k < 2 ^ 32 := by
      have gp : ∀ c l, 0x20 ≤ c → c + l ≤ 0x28 → G + BitVec.ofNat 32 c ≠ 0 ∧
          Sep (G + BitVec.ofNat 32 c) l (G + 0xFFFFFFF0) 0x30 ∧ (G + BitVec.ofNat 32 c).toNat + l < 2 ^ 32 :=
        fun c l h1 h2 => ⟨fun e => by have := congrArg BitVec.toNat e; rw [hGc c (by omega)] at this; simp at this; omega,
          (sep_of_le (by rw [hlo, hGc c (by omega)]; omega) (by rw [hGc c (by omega)]; omega)).symm,
          by rw [hGc c (by omega)]; omega⟩
      have rp : ∀ (a : Word) (l : Nat), Sep S (0x90 + romStack) a l → Sep a l (G + 0xFFFFFFF0) 0x30 := fun a l h => by
        have := h.sub (c := romStack - 16) (l := 0x30) (by omega); rw [hG16] at this; exact this.symm
      intro k hk
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨show BitVec.ofNat 32 bsMagicAddress ≠ 0 by decide, rp _ _ hSm,
          show (BitVec.ofNat 32 bsMagicAddress).toNat + 4 < 2 ^ 32 by decide⟩
      · exact ⟨show BitVec.ofNat 32 bsVersionAddress ≠ 0 by decide, rp _ _ hSv,
          show (BitVec.ofNat 32 bsVersionAddress).toNat + 2 < 2 ^ 32 by decide⟩
      · exact gp 0x20 4 (by decide) (by decide)
      · exact gp 0x24 2 (by decide) (by decide)
      · exact gp 0x26 1 (by decide) (by decide)
      · exact gp 0x27 1 (by decide) (by decide)
    have I0 : BWInv n1.mem n1.mem G (bwBody m.mem st) 0 := ⟨fun i hi => by
        rw [ite_eq_right (by omega)]
        have ofs : ∀ (c : Word) l, 32 ≤ c.toNat → c.toNat + l ≤ 0x90 → Sep (G + c) l (G + BitVec.ofNat 32 i) 1 :=
          fun c l h1 h2 => by
            have := sep_offsets G (c := c.toNat) (n := l) (d := i) (k := 1) (Or.inr (by omega)) (by omega) (by omega)
            rwa [ofNat_toNat_w] at this
        rw [hm]
        simp (disch := first | exact ofs _ 4 (by decide) (by decide) | exact ofs _ 1 (by decide) (by decide)) only
          [memStore32_get_sep, st8o]
        rw [← hM7, get_fill, BitVec.toNat_ofNat, ite_eq_left (by omega)], fun _ _ => rfl⟩
    have kn2 : ∀ r, reg n2 r = reg n1 r := u2.regs
    obtain ⟨n3, c3, s3, I3, sp3, r193, r203, kp3⟩ := bw_loop (Mx := n1.mem) (B := bwBody m.mem st) (R := reg n2)
      cd1.self cd1.copy cd1.stub cd1.body hGa hGl hGh hT hS hP rfl rfl 6 0 rfl (by decide) t2 I0
      (by rw [kn2, kb sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hsp])
      (by rw [kn2, v9]; try rfl) (by rw [kn2, v8]; try rfl)
      (by rw [kn2, kb 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h19])
      (by rw [kn2, kb 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h20])
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
    have hO3 : ∀ x, Sep S (0x90 + romStack) x 1 → n3.mem x = m.mem x := fun x hx =>
      (I3.out x (inR x (fun i hi j hj => hx i (by omega) j hj))).trans (hOm1 x hx)
    have cd3 := codeOf n3.mem hO3
    have bhi : ∀ i, 16 ≤ i → bwBody m.mem st i = 0 := fun i h => by
      unfold bwBody
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    obtain ⟨n4, c4, s4, hW4, hO4, k4⟩ := bw_crc (B := bwBody m.mem st) s3 cd3.self cd3.crc cd3.memset sp3 hGa hGh (fun i hi => by
      rw [I3.body i (by omega)]
      by_cases h16 : i < 16
      · rw [ite_eq_left h16]
      · rw [ite_eq_right h16, bhi i (by omega)])
    refine rtail n4 n4.mem (reg n4) (hn.trans (d1.trans (.cons d2 (c3.trans c4)))) s4 ?_ ?_ ?_ ?_ ?_
    · rw [k4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]; exact sp3
    · rw [k4 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), kp3 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), kn2, kb 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]; exact h18
    · intro x hx
      have hG48 : Sep G 0x48 x 1 := by have := fr78 0 0x48 (by decide) x hx; rwa [add_ofNat_zero] at this
      have hG32 : Sep G 32 x 1 := by have := fr78 0 32 (by decide) x hx; rwa [add_ofNat_zero] at this
      rw [hO4 x hG48, I3.out x (inR x hx), hO1 x hx, ← hM7, fillBytes_sep hG32 (Nat.le_refl _)]
    · intro i hi
      rw [show G + 0x28 + BitVec.ofNat 32 i = G + BitVec.ofNat 32 (0x28 + i) from add_ofNat_assoc G 0x28 i, hW4 i hi]
      rfl
    · intro r h0 h1 h2 h3 h4 h5 h6 hq
      rw [k4 r (by revert hq; revert r; decide) (by revert hq; revert r; decide) (by revert hq; revert r; decide)
          (by revert hq; revert r; decide) (by revert hq; revert r; decide) (by revert hq; revert r; decide)
          (by revert hq; revert r; decide) h2 h3 h1,
        kp3 r (by revert hq; revert r; decide) (by revert hq; revert r; decide) (by revert hq; revert r; decide)
          (by revert hq; revert r; decide) (by revert hq; revert r; decide) (by revert hq; revert r; decide)
          (by revert hq; revert r; decide) (by revert hq; revert r; decide) (by revert hq; revert r; decide)
          (by revert hq; revert r; decide) (by revert hq; revert r; decide) (by revert hq; revert r; decide)
          (by revert hq; revert r; decide) (by revert hq; revert r; decide) h1 h2 h3,
        kn2, kb r (by revert hq; revert r; decide) (by revert hq; revert r; decide) (by revert hq; revert r; decide)
          (by revert hq; revert r; decide) (by revert hq; revert r; decide) (by revert hq; revert r; decide) h2 h3]
      exact hk r (by revert hq; revert r; decide) (by revert hq; revert r; decide) (by revert hq; revert r; decide)
        (by revert hq; revert r; decide) (by revert hq; revert r; decide) (by revert hq; revert r; decide)
        (by revert hq; revert r; decide) h3 h4 h5 h6 h0 h1
  -- 0x28 to 0x44: the trial slot and boots left as the record holds them.
  obtain ⟨m17, e17, t17⟩ := t16.lbu hcM7 bw_at_28 (off' := 0x2C) (by decide)
  have u17 := t17.self
  obtain ⟨m18, e18, t18⟩ := u17.lbu hcM7 bw_at_2c (off' := 0x30) (by decide)
  have u18 := t18.self
  obtain ⟨m19, e19, t19⟩ := u18.aluImm hcM7 bw_at_30 (off' := 0x34) (by decide)
  have u19 := t19.self
  obtain ⟨m20, e20, t20⟩ := u19.aluImm hcM7 bw_at_34 (off' := 0x38) (by decide)
  have u20 := t20.self
  obtain ⟨m21, e21, t21⟩ := u20.aluImm hcM7 bw_at_38 (off' := 0x3C) (by decide)
  have u21 := t21.self
  obtain ⟨m22, e22, t22⟩ := u21.aluImm hcM7 bw_at_3c (off' := 0x3E) (by decide)
  have u22 := t22.self
  obtain ⟨m23, e23, t23⟩ := u22.alu hcM7 bw_at_3e (off' := 0x40) (by decide)
  have u23 := t23.self
  have g23 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → reg m23 r = reg m16 r := fun r h0 h1 h2 h3 => by
    rw [t23.regs, updz u22.zero h2, t22.regs, updz u21.zero h0, t21.regs, updz u20.zero h3, t20.regs,
      updz u19.zero h0, t19.regs, updz u18.zero h0, t18.regs, updz u17.zero h2, t17.regs, updz t16.zero h1]
  have st16 : reg m16 9 = st := by
    rw [g16 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact s1_14
  have a1_23 : reg m23 a1 = (m.mem (st + 4)).zeroExtend 32 := by
    simp +decide only [t23.regs, t22.regs, t21.regs, t20.regs, t19.regs, t18.regs, t17.regs, upd, ite_true,
      ite_false]
    rw [st16, tb]
  have a2_23 : reg m23 a2 = (m.mem (st + 5)).zeroExtend 32 &&&
      aluEval .add (aluEval .sltu ((m.mem (st + 4)).zeroExtend 32 + 0xFFFFFFFE) 1) 0xFFFFFFFF := by
    simp +decide only [t23.regs, t22.regs, t21.regs, t20.regs, t19.regs, t18.regs, t17.regs, upd, ite_true,
      ite_false]
    rw [st16, tb, bb]; rfl
  have a0_23 : reg m23 a0 = 2 := by
    simp +decide only [t23.regs, t22.regs, upd, ite_true, ite_false]; rw [show reg m21 x0 = 0 from u21.zero]; rfl
  have pre23 : Steps m m23 := pre14.trans (c15.trans (c16.trans (.cons e17 (.cons e18 (.cons e19 (.cons e20
    (.cons e21 (.cons e22 (.single e23)))))))))
  have z2 : ∀ x : Word, x + 0xFFFFFFFE = 0 → x = 2 := fun x e => by
    have := congrArg (· + 2) e
    simp only [BitVec.add_assoc] at this
    rw [show (0xFFFFFFFE : Word) + 2 = 0 from rfl] at this
    exact (BitVec.add_zero _).symm.trans (this.trans (BitVec.zero_add _))
  have zinj : ∀ b : BitVec 8, b.zeroExtend 32 = 2 → b = 2 := fun b e => by
    have := congrArg (fun w : Word => w.extractLsb' 0 8) e
    rw [zextByte_lo] at this; exact this
  have keep23 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ 9 → r ≠ 18 → r ≠ 19 →
      r ≠ 20 → r ≠ sp → r ≠ ra → reg m23 r = reg m r := fun r h0 h1 h2 h3 h4 h5 h6 h9 h18 h19 h20 hs hr => by
    rw [g23 r h0 h1 h2 h3, g16 r h2 h3 h4 h5 h6 hr, v14 r h0 h1 h2 h9 h18 h19 h20 hs]
  have v23 : ∀ r, r = sp ∨ r = 9 ∨ r = 18 ∨ r = 19 ∨ r = 20 → reg m23 r = reg m14 r := fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [g23 _ (by decide) (by decide) (by decide) (by decide), g16 _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
  by_cases ht : m.mem (st + 4) = 2
  · obtain ⟨m24, e24, t24⟩ := u23.notTaken hcM7 0x44 bw_at_40 (by decide)
      (by rw [a1_23, a0_23, ht]; decide)
    obtain ⟨m25, e25, t25⟩ := t24.aluImm hcM7 bw_at_44 (off' := 0x48) (by decide)
    refine cont48 m25 _ (pre23.trans (.cons e24 (.single e25))) t25 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [updz u23.zero (by decide), v23 sp (Or.inl rfl)]; exact sp14
    · rw [updz u23.zero (by decide), v23 9 (Or.inr (Or.inl rfl))]; exact s1_14
    · rw [updz u23.zero (by decide), v23 18 (Or.inr (Or.inr (Or.inl rfl)))]; exact s2_14
    · rw [updz u23.zero (by decide), v23 19 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact s3_14
    · rw [updz u23.zero (by decide), v23 20 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]; exact s4_14
    · rw [updz u23.zero (by decide)]; exact a0_23
    · simp +decide only [upd, ite_true, ite_false]; rw [u23.zero]; unfold bwTrial; rw [ite_eq_left ht]; rfl
    · rw [updz u23.zero (by decide), a2_23]; unfold bwBoots; rw [ite_eq_left ht, ht]
      rw [show aluEval .add (aluEval .sltu ((2 : BitVec 8).zeroExtend 32 + 0xFFFFFFFE) 1) 0xFFFFFFFF = 0
        from by decide]; exact BitVec.and_zero
    · intro r h0 h1 h2 h3 h4 h5 h6 h9 h18 h19 h20 hs hr
      rw [updz u23.zero h1]; exact keep23 r h0 h1 h2 h3 h4 h5 h6 h9 h18 h19 h20 hs hr
  · obtain ⟨m24, e24, t24⟩ := u23.taken hcM7 0x48 bw_at_40 (by decide)
      (by rw [a1_23, a0_23]; exact bne_iff_ne.mpr fun e => ht (zinj _ e))
    refine cont48 m24 _ (pre23.trans (.single e24)) t24 ?_ ?_ ?_ ?_ ?_ a0_23 ?_ ?_ ?_
    · rw [v23 sp (Or.inl rfl)]; exact sp14
    · rw [v23 9 (Or.inr (Or.inl rfl))]; exact s1_14
    · rw [v23 18 (Or.inr (Or.inr (Or.inl rfl)))]; exact s2_14
    · rw [v23 19 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact s3_14
    · rw [v23 20 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]; exact s4_14
    · rw [a1_23]; unfold bwTrial; rw [ite_eq_right ht]
    · rw [a2_23]; unfold bwBoots; rw [ite_eq_right ht]
      have hne : (m.mem (st + 4)).zeroExtend 32 + 0xFFFFFFFE ≠ 0 := fun e => ht (zinj _ (z2 _ e))
      rcases sltu1_cases ((m.mem (st + 4)).zeroExtend 32 + 0xFFFFFFFE) with ⟨_, h⟩ | ⟨h1, _⟩
      · exact absurd h hne
      · rw [h1]; exact and_ff32 _
    · exact keep23

end C3.RV32.Cur





