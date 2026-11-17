import C3BootProofs.Proofs.BootWrite
import C3BootProofs.Proofs.Panic

/-!
# `c3_bootloader::boot`: the specification and its loops

`boot` copies each RAM segment of the accepted image from flash, writes
the cache's MMU table so that it maps each flash segment, enables the
cache buses, and jumps to the entry point with the slot index in `a0`.
This file states that work over the bytes of the accepted header and of
flash, and proves the code's loops.

Segment `j` of the header at `acc` is the 16 bytes at `acc + 16 * j`: the
load address, the offset in the image, and the length as words, then the
kind as the byte at offset 12. Kinds 0 and 1 are flash code and data, and
kinds 2 and 3 are RAM code and data.
-/

namespace C3.RV32.Cur

open C3.Image

/-- Where `boot` is in the image. -/
abbrev BT : Word := BitVec.ofNat 32 bootFnAddress

def sgPtr (acc : Word) (j : Nat) : Word := acc + BitVec.ofNat 32 (16 * j)
def sgAddr (M : Word → BitVec 8) (acc : Word) (j : Nat) : Word := memLoad32 M (sgPtr acc j + 0)
def sgOff (M : Word → BitVec 8) (acc : Word) (j : Nat) : Word := memLoad32 M (sgPtr acc j + 4)
def sgLen (M : Word → BitVec 8) (acc : Word) (j : Nat) : Word := memLoad32 M (sgPtr acc j + 8)
/-- The length's upper half, which is the number of 64 KiB flash pages. -/
def sgPages (M : Word → BitVec 8) (acc : Word) (j : Nat) : Word :=
  (M (sgPtr acc j + 0xA + 1) ++ M (sgPtr acc j + 0xA)).zeroExtend 32
def sgKind (M : Word → BitVec 8) (acc : Word) (j : Nat) : BitVec 8 := M (sgPtr acc j + 0xC)

/-- How many segments `boot` walks: the header's count, or none when the
count is above 16. -/
def sgCount (M : Word → BitVec 8) (acc : Word) : Nat :=
  if (memLoad32 M (acc + 0x108)).toNat ≤ 16 then (memLoad32 M (acc + 0x108)).toNat else 0

/-- Where a RAM segment is copied: RAM code goes to its data-bus alias. -/
def sgDest (M : Word → BitVec 8) (acc : Word) (j : Nat) : Word :=
  if sgKind M acc j = 2 then sgAddr M acc j + 0xFF900000 else sgAddr M acc j

/-- The flash address of a segment of the image at `imgf`. -/
def sgSrc (M : Word → BitVec 8) (acc imgf : Word) (j : Nat) : Word := sgOff M acc j + imgf

/-- The bytes a RAM segment copies: its length rounded down to words. -/
def sgBytes (M : Word → BitVec 8) (acc : Word) (j : Nat) : Nat := 4 * (sgLen M acc j >>> 2).toNat

/-- `M` with the `n` bytes at `dst` set from `bytes`. -/
def copyIn (M : Word → BitVec 8) (dst : Word) (n : Nat) (bytes : Nat → BitVec 8) : Word → BitVec 8 :=
  fun x => if (x - dst).toNat < n then bytes (x - dst).toNat else M x

/-- Memory after the first `j` segments' RAM copies. -/
def ramLoad (flash : Nat → BitVec 8) (M0 : Word → BitVec 8) (acc imgf : Word) : Nat → Word → BitVec 8
  | 0 => M0
  | j + 1 =>
    if 2 ≤ (sgKind M0 acc j).toNat then
      copyIn (ramLoad flash M0 acc imgf j) (sgDest M0 acc j) (sgBytes M0 acc j)
        fun i => flash ((sgSrc M0 acc imgf j).toNat + i)
    else ramLoad flash M0 acc imgf j

/-- The cache's MMU table: 128 words. -/
abbrev mmuBase : Word := 0x600C5000

/-- `M` with the first `k` MMU entries set to invalid (0x100). -/
def mmuInv (M : Word → BitVec 8) (k : Nat) : Word → BitVec 8 :=
  fun x => if (x - mmuBase).toNat < 4 * k then (0x100 : Word).extractLsb' (8 * ((x - mmuBase).toNat % 4)) 8 else M x

/-- `k` MMU entries from entry `e`, mapping flash pages from `v`. An entry
past the table's 128 is skipped. -/
def mapSeg (M : Word → BitVec 8) (e v : Word) : Nat → Word → BitVec 8
  | 0 => M
  | k + 1 => mapSeg (if e.toNat ≤ 127 then memStore32 M ((e <<< 2) + mmuBase) (v &&& 0xFF) else M) (e + 1) (v + 1) k

/-- The first MMU entry of a flash segment: its offset in the code window
at 0x42000000 or the data window at 0x3C000000, in pages. -/
def sgEntry (M : Word → BitVec 8) (acc : Word) (j : Nat) : Word :=
  ((if sgKind M acc j = 0 then 0xBE000000 else 0xC4000000) + sgAddr M acc j) >>> 16

/-- The first flash page of a segment of the image at `imgf`. -/
def sgPage (M : Word → BitVec 8) (acc imgf : Word) (j : Nat) : Word := sgSrc M acc imgf j >>> 16

/-- `M` after the first `j` segments' MMU entries. -/
def mmuMap (M0 : Word → BitVec 8) (acc imgf : Word) (M : Word → BitVec 8) : Nat → Word → BitVec 8
  | 0 => M
  | j + 1 =>
    if (sgKind M0 acc j).toNat < 2 then
      mapSeg (mmuMap M0 acc imgf M j) (sgEntry M0 acc j) (sgPage M0 acc imgf j) (sgPages M0 acc j).toNat
    else mmuMap M0 acc imgf M j

/-- The cache controller's bus-shutdown register. -/
abbrev icacheCtrl1 : Word := 0x600C4004

/-- `M` with both cache buses enabled. -/
def busOn (M : Word → BitVec 8) : Word → BitVec 8 :=
  memStore32 M icacheCtrl1 (memLoad32 M icacheCtrl1 &&& 0xFFFFFFFC)

/-- Memory as `boot` leaves it outside its stack. -/
def bootMem (flash : Nat → BitVec 8) (M0 : Word → BitVec 8) (acc imgf : Word) : Word → BitVec 8 :=
  busOn (mmuMap M0 acc imgf (mmuInv (ramLoad flash M0 acc imgf (sgCount M0 acc)) 128) (sgCount M0 acc))

set_option maxRecDepth 20000

theorem bt_at_0 : fetchRel bootFnCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem bt_at_2 : fetchRel bootFnCode 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem bt_at_4 : fetchRel bootFnCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x28, 2) := by decide
theorem bt_at_6 : fetchRel bootFnCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x24, 2) := by decide
theorem bt_at_8 : fetchRel bootFnCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x20, 2) := by decide
theorem bt_at_a : fetchRel bootFnCode 0xA = some (.store .sw sp (19 : Fin 32) 0x1C, 2) := by decide
theorem bt_at_c : fetchRel bootFnCode 0xC = some (.store .sw sp (20 : Fin 32) 0x18, 2) := by decide
theorem bt_at_e : fetchRel bootFnCode 0xE = some (.store .sw sp (21 : Fin 32) 0x14, 2) := by decide
theorem bt_at_10 : fetchRel bootFnCode 0x10 = some (.store .sw sp (22 : Fin 32) 0x10, 2) := by decide
theorem bt_at_12 : fetchRel bootFnCode 0x12 = some (.store .sw sp (23 : Fin 32) 0xC, 2) := by decide
theorem bt_at_14 : fetchRel bootFnCode 0x14 = some (.store .sw sp (24 : Fin 32) 0x8, 2) := by decide
theorem bt_at_16 : fetchRel bootFnCode 0x16 = some (.alu .add (21 : Fin 32) x0 a2, 2) := by decide
theorem bt_at_18 : fetchRel bootFnCode 0x18 = some (.alu .add (20 : Fin 32) x0 a1, 2) := by decide
theorem bt_at_1a : fetchRel bootFnCode 0x1A = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem bt_at_1c : fetchRel bootFnCode 0x1C = some (.branch .bgeu a4 a3 0x16, 4) := by decide
theorem bt_at_20 : fetchRel bootFnCode 0x20 = some (.lui a0 0x3FCC4000, 4) := by decide
theorem bt_at_24 : fetchRel bootFnCode 0x24 = some (.aluImm .add a0 a0 0x198, 4) := by decide
theorem bt_at_28 : fetchRel bootFnCode 0x28 = some (.alu .add a1 x0 a3, 2) := by decide
theorem bt_at_2a : fetchRel bootFnCode 0x2A = some (.auipc ra 0xFFC5F000, 4) := by decide
theorem bt_at_2e : fetchRel bootFnCode 0x2E = some (.jalr ra ra 0xFFFFFA7C, 4) := by decide
theorem bt_at_32 : fetchRel bootFnCode 0x32 = some (.load .lw a0 (20 : Fin 32) 0x108, 4) := by decide
theorem bt_at_36 : fetchRel bootFnCode 0x36 = some (.aluImm .add a2 x0 0x10, 2) := by decide
theorem bt_at_38 : fetchRel bootFnCode 0x38 = some (.aluImm .sltu a1 a0 0x11, 4) := by decide
theorem bt_at_3c : fetchRel bootFnCode 0x3C = some (.alu .add (24 : Fin 32) x0 (20 : Fin 32), 2) := by decide
theorem bt_at_3e : fetchRel bootFnCode 0x3E = some (.branch .bgeu a2 a0 0x6, 4) := by decide
theorem bt_at_42 : fetchRel bootFnCode 0x42 = some (.aluImm .add (24 : Fin 32) x0 0x4, 2) := by decide
theorem bt_at_44 : fetchRel bootFnCode 0x44 = some (.alu .sub a1 x0 a1, 4) := by decide
theorem bt_at_48 : fetchRel bootFnCode 0x48 = some (.alu .and a0 a0 a1, 2) := by decide
theorem bt_at_4a : fetchRel bootFnCode 0x4A = some (.aluImm .sll (8 : Fin 32) a0 0x4, 4) := by decide
theorem bt_at_4e : fetchRel bootFnCode 0x4E = some (.aluImm .add (19 : Fin 32) x0 0x2, 2) := by decide
theorem bt_at_50 : fetchRel bootFnCode 0x50 = some (.alu .add (22 : Fin 32) (24 : Fin 32) (8 : Fin 32), 4) := by decide
theorem bt_at_54 : fetchRel bootFnCode 0x54 = some (.lui (23 : Fin 32) 0xFF900000, 4) := by decide
theorem bt_at_58 : fetchRel bootFnCode 0x58 = some (.alu .add (9 : Fin 32) x0 (24 : Fin 32), 2) := by decide
theorem bt_at_5a : fetchRel bootFnCode 0x5A = some (.branch .beq (8 : Fin 32) x0 0x2E, 2) := by decide
theorem bt_at_5c : fetchRel bootFnCode 0x5C = some (.load .lbu a0 (9 : Fin 32) 0xC, 4) := by decide
theorem bt_at_60 : fetchRel bootFnCode 0x60 = some (.branch .bltu a0 (19 : Fin 32) 0x22, 4) := by decide
theorem bt_at_64 : fetchRel bootFnCode 0x64 = some (.branch .bne a0 (19 : Fin 32) 0xA, 4) := by decide
theorem bt_at_68 : fetchRel bootFnCode 0x68 = some (.load .lw a1 (9 : Fin 32) 0x0, 2) := by decide
theorem bt_at_6a : fetchRel bootFnCode 0x6A = some (.alu .add a1 a1 (23 : Fin 32), 2) := by decide
theorem bt_at_6c : fetchRel bootFnCode 0x6C = some (.jal x0 0x4, 2) := by decide
theorem bt_at_6e : fetchRel bootFnCode 0x6E = some (.load .lw a1 (9 : Fin 32) 0x0, 2) := by decide
theorem bt_at_70 : fetchRel bootFnCode 0x70 = some (.load .lw a0 (9 : Fin 32) 0x4, 2) := by decide
theorem bt_at_72 : fetchRel bootFnCode 0x72 = some (.load .lw a2 (9 : Fin 32) 0x8, 2) := by decide
theorem bt_at_74 : fetchRel bootFnCode 0x74 = some (.alu .add a0 a0 (21 : Fin 32), 2) := by decide
theorem bt_at_76 : fetchRel bootFnCode 0x76 = some (.aluImm .srl a2 a2 0x2, 2) := by decide
theorem bt_at_78 : fetchRel bootFnCode 0x78 = some (.auipc ra 0x0, 4) := by decide
theorem bt_at_7c : fetchRel bootFnCode 0x7C = some (.jalr ra ra 0x11E, 4) := by decide
theorem bt_at_80 : fetchRel bootFnCode 0x80 = some (.branch .beq a0 x0 0xB6, 2) := by decide
theorem bt_at_82 : fetchRel bootFnCode 0x82 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x10, 2) := by decide
theorem bt_at_84 : fetchRel bootFnCode 0x84 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFF0, 2) := by decide
theorem bt_at_86 : fetchRel bootFnCode 0x86 = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFD6, 2) := by decide
theorem bt_at_88 : fetchRel bootFnCode 0x88 = some (.lui (8 : Fin 32) 0x600C5000, 4) := by decide
theorem bt_at_8c : fetchRel bootFnCode 0x8C = some (.aluImm .add (9 : Fin 32) x0 0x80, 4) := by decide
theorem bt_at_90 : fetchRel bootFnCode 0x90 = some (.auipc ra 0xFFC5F000, 4) := by decide
theorem bt_at_94 : fetchRel bootFnCode 0x94 = some (.jalr ra ra 0xFFFFFEFA, 4) := by decide
theorem bt_at_98 : fetchRel bootFnCode 0x98 = some (.alu .add (19 : Fin 32) x0 a0, 2) := by decide
theorem bt_at_9a : fetchRel bootFnCode 0x9A = some (.aluImm .add a0 x0 0x100, 4) := by decide
theorem bt_at_9e : fetchRel bootFnCode 0x9E = some (.branch .beq (9 : Fin 32) x0 0xA, 2) := by decide
theorem bt_at_a0 : fetchRel bootFnCode 0xA0 = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem bt_at_a2 : fetchRel bootFnCode 0xA2 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem bt_at_a4 : fetchRel bootFnCode 0xA4 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem bt_at_a6 : fetchRel bootFnCode 0xA6 = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFFA, 2) := by decide
theorem bt_at_a8 : fetchRel bootFnCode 0xA8 = some (.aluImm .add a0 x0 0x2, 2) := by decide
theorem bt_at_aa : fetchRel bootFnCode 0xAA = some (.lui (9 : Fin 32) 0x600C5000, 4) := by decide
theorem bt_at_ae : fetchRel bootFnCode 0xAE = some (.aluImm .add a2 x0 0x7F, 4) := by decide
theorem bt_at_b2 : fetchRel bootFnCode 0xB2 = some (.branch .beq (24 : Fin 32) (22 : Fin 32) 0x4E, 4) := by decide
theorem bt_at_b6 : fetchRel bootFnCode 0xB6 = some (.alu .add a3 x0 (24 : Fin 32), 2) := by decide
theorem bt_at_b8 : fetchRel bootFnCode 0xB8 = some (.load .lbu a4 (24 : Fin 32) 0xC, 4) := by decide
theorem bt_at_bc : fetchRel bootFnCode 0xBC = some (.aluImm .add a5 a4 0xFFFFFFFE, 4) := by decide
theorem bt_at_c0 : fetchRel bootFnCode 0xC0 = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0x10, 2) := by decide
theorem bt_at_c2 : fetchRel bootFnCode 0xC2 = some (.lui a1 0xBE000000, 4) := by decide
theorem bt_at_c6 : fetchRel bootFnCode 0xC6 = some (.branch .bltu a5 a0 0xFFFFFFEC, 4) := by decide
theorem bt_at_ca : fetchRel bootFnCode 0xCA = some (.branch .beq a4 x0 0x6, 2) := by decide
theorem bt_at_cc : fetchRel bootFnCode 0xCC = some (.lui a1 0xC4000000, 4) := by decide
theorem bt_at_d0 : fetchRel bootFnCode 0xD0 = some (.load .lw a4 a3 0x0, 2) := by decide
theorem bt_at_d2 : fetchRel bootFnCode 0xD2 = some (.load .lw a5 a3 0x4, 2) := by decide
theorem bt_at_d4 : fetchRel bootFnCode 0xD4 = some (.load .lhu a3 a3 0xA, 4) := by decide
theorem bt_at_d8 : fetchRel bootFnCode 0xD8 = some (.alu .add a1 a1 a4, 2) := by decide
theorem bt_at_da : fetchRel bootFnCode 0xDA = some (.aluImm .srl a4 a1 0x10, 4) := by decide
theorem bt_at_de : fetchRel bootFnCode 0xDE = some (.alu .add a5 a5 (21 : Fin 32), 2) := by decide
theorem bt_at_e0 : fetchRel bootFnCode 0xE0 = some (.aluImm .sll a1 a4 0x2, 4) := by decide
theorem bt_at_e4 : fetchRel bootFnCode 0xE4 = some (.aluImm .srl a5 a5 0x10, 2) := by decide
theorem bt_at_e6 : fetchRel bootFnCode 0xE6 = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem bt_at_e8 : fetchRel bootFnCode 0xE8 = some (.branch .beq a3 x0 0xFFFFFFCA, 2) := by decide
theorem bt_at_ea : fetchRel bootFnCode 0xEA = some (.branch .bltu a2 a4 0xA, 4) := by decide
theorem bt_at_ee : fetchRel bootFnCode 0xEE = some (.aluImm .and (8 : Fin 32) a5 0xFF, 4) := by decide
theorem bt_at_f2 : fetchRel bootFnCode 0xF2 = some (.store .sw a1 (8 : Fin 32) 0x0, 2) := by decide
theorem bt_at_f4 : fetchRel bootFnCode 0xF4 = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem bt_at_f6 : fetchRel bootFnCode 0xF6 = some (.aluImm .add a4 a4 0x1, 2) := by decide
theorem bt_at_f8 : fetchRel bootFnCode 0xF8 = some (.aluImm .add a5 a5 0x1, 2) := by decide
theorem bt_at_fa : fetchRel bootFnCode 0xFA = some (.aluImm .add a3 a3 0xFFFFFFFF, 2) := by decide
theorem bt_at_fc : fetchRel bootFnCode 0xFC = some (.branch .beq a3 x0 0xFFFFFFB6, 2) := by decide
theorem bt_at_fe : fetchRel bootFnCode 0xFE = some (.jal x0 0xFFFFFFEC, 2) := by decide
theorem bt_at_100 : fetchRel bootFnCode 0x100 = some (.lui a0 0x600C4000, 4) := by decide
theorem bt_at_104 : fetchRel bootFnCode 0x104 = some (.load .lw a1 a0 0x4, 2) := by decide
theorem bt_at_106 : fetchRel bootFnCode 0x106 = some (.aluImm .and a1 a1 0xFFFFFFFC, 2) := by decide
theorem bt_at_108 : fetchRel bootFnCode 0x108 = some (.store .sw a0 a1 0x4, 2) := by decide
theorem bt_at_10a : fetchRel bootFnCode 0x10A = some (.auipc ra 0xFFC5F000, 4) := by decide
theorem bt_at_10e : fetchRel bootFnCode 0x10E = some (.jalr ra ra 0xFFFFFE34, 4) := by decide
theorem bt_at_112 : fetchRel bootFnCode 0x112 = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem bt_at_114 : fetchRel bootFnCode 0x114 = some (.auipc ra 0xFFC5F000, 4) := by decide
theorem bt_at_118 : fetchRel bootFnCode 0x118 = some (.jalr ra ra 0xFFFFFE7A, 4) := by decide
theorem bt_at_11c : fetchRel bootFnCode 0x11C = some (.load .lw (8 : Fin 32) (20 : Fin 32) 0x100, 4) := by decide
theorem bt_at_120 : fetchRel bootFnCode 0x120 = some (.lui a0 0x3FCC4000, 4) := by decide
theorem bt_at_124 : fetchRel bootFnCode 0x124 = some (.aluImm .add a0 a0 0x14E, 4) := by decide
theorem bt_at_128 : fetchRel bootFnCode 0x128 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem bt_at_12a : fetchRel bootFnCode 0x12A = some (.auipc ra 0xFFC5F000, 4) := by decide
theorem bt_at_12e : fetchRel bootFnCode 0x12E = some (.jalr ra ra 0xFFFFF97C, 4) := by decide
theorem bt_at_132 : fetchRel bootFnCode 0x132 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem bt_at_134 : fetchRel bootFnCode 0x134 = some (.jalr ra (8 : Fin 32) 0x0, 2) := by decide
theorem bt_at_136 : fetchRel bootFnCode 0x136 = some (.aluImm .add a0 x0 0xE2, 4) := by decide
theorem bt_at_13a : fetchRel bootFnCode 0x13A = some (.auipc ra 0x0, 4) := by decide
theorem bt_at_13e : fetchRel bootFnCode 0x13E = some (.jalr ra ra 0x8, 4) := by decide

section Step
variable {M : Word → BitVec 8} {base : Word} {m : Machine} {off : Nat} {f : Fin 32 → Word} {code : List Nat}

theorem _root_.C3.RV32.St.lhu (s : St M base m off f) (hc : CodeIn M base code)
    {rd rs1 : Fin 32} {o len : Word} {off' : Nat}
    (hf : fetchRel code off = some (.load .lhu rd rs1 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (hal : (f rs1 + o).toNat % 2 = 0) :
    ∃ m1, step m = some m1 ∧
      St M base m1 off' (upd f rd ((M (f rs1 + o + 1) ++ M (f rs1 + o)).zeroExtend 32)) := by
  refine ⟨_, ?_, s.write (v := (M (f rs1 + o + 1) ++ M (f rs1 + o)).zeroExtend 32) (rd := rd) hn⟩
  have ha : aligned (loadSize .lhu) (reg m rs1 + o) = true := by
    unfold aligned loadSize; rw [s.regs, hal]; rfl
  rw [step_code (s.codeAt hc) s.pc hf, ← s.regs rs1, ← s.mem]
  unfold exec
  simp only [ha, Bool.not_true]
  rfl

end Step

theorem st32_read (M : Word → BitVec 8) (a v x : Word) :
    memStore32 M a v x = if (x - a).toNat < 4 then v.extractLsb' (8 * (x - a).toNat) 8 else M x := by
  by_cases h : (x - a).toNat < 4
  · rw [ite_eq_left h]
    have hx : x = a + BitVec.ofNat 32 (x - a).toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    obtain ⟨d, hd⟩ : ∃ d, (x - a).toNat = d := ⟨_, rfl⟩
    rw [hd] at h hx ⊢
    subst hx
    rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [add_ofNat_zero, st32_at0]
    · exact st32_at1 M a v
    · exact st32_at2 M a v
    · exact st32_at3 M a v
  · rw [ite_eq_right h]
    exact memStore32_get_sep fun i hi j hj e => h (by
      have : x - a = BitVec.ofNat 32 i := by
        rw [show j = 0 by omega, add_ofNat_zero] at e; rw [← e, BitVec.add_comm, BitVec.add_sub_cancel]
      rw [this, BitVec.toNat_ofNat]; omega)

theorem codeKeep {M M' : Word → BitVec 8} {b : Word} {code : List Nat} (hc : CodeIn M b code)
    (hb : b.toNat + code.length ≤ 0x600C4000) (h : ∀ x : Word, x.toNat < 0x600C4000 → M' x = M x) :
    CodeIn M' b code := fun i hi => by
  rw [h _ (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]; exact hc i hi

theorem sub_add_toNat (x b : Word) (c : Nat) (hc : c < 2 ^ 32) :
    (x - (b + BitVec.ofNat 32 c)).toNat = ((x - b).toNat + (2 ^ 32 - c)) % 2 ^ 32 := by
  rw [show x - (b + BitVec.ofNat 32 c) = x - b - BitVec.ofNat 32 c by rw [BitVec.sub_sub], BitVec.toNat_sub,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
  omega

theorem mmuInv_step (M : Word → BitVec 8) (k : Nat) (hk : k < 128) :
    memStore32 (mmuInv M k) (mmuBase + BitVec.ofNat 32 (4 * k) + 0) 0x100 = mmuInv M (k + 1) := by
  funext x
  rw [add_lit_zero, st32_read, sub_add_toNat _ _ _ (by omega)]
  unfold mmuInv
  have hd := (x - mmuBase).isLt
  by_cases h2 : (x - mmuBase).toNat < 4 * k
  · rw [ite_eq_right (by omega), ite_eq_left h2, ite_eq_left (by omega)]
  · by_cases h3 : (x - mmuBase).toNat < 4 * k + 4
    · rw [ite_eq_left (by omega), ite_eq_left (by omega),
        show ((x - mmuBase).toNat + (2 ^ 32 - 4 * k)) % 2 ^ 32 = (x - mmuBase).toNat % 4 by omega]
    · rw [ite_eq_right (by omega), ite_eq_right h2, ite_eq_right (by omega)]

def btInvBlk : List BInstr :=
  [.sw (8 : Fin 32) a0 0x0, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF]

theorem btInvBlk_end : blockEnd bootFnCode 0xA0 btInvBlk = some 0xA6 :=
  (blockEnd_cons' (off' := 0xA2) bt_at_a0 rfl (blockEnd_cons' (off' := 0xA4) bt_at_a2 rfl (blockEnd_cons' (off' := 0xA6) bt_at_a4 rfl rfl)))

set_option maxHeartbeats 4000000 in
/-- The loop that sets all 128 MMU entries to invalid, from the head of
pass `k` at 0xA0 to its exit at 0xA8. -/
theorem bt_inv {M : Word → BitVec 8} (hc : CodeIn M BT bootFnCode) :
    ∀ d k {n : Machine}, k + d = 128 → k < 128 → St (mmuInv M k) BT n 0xA0 (reg n) →
      reg n 8 = mmuBase + BitVec.ofNat 32 (4 * k) → reg n 9 = BitVec.ofNat 32 (128 - k) → reg n a0 = 0x100 →
      ∃ n', Steps n n' ∧ St (mmuInv M 128) BT n' 0xA8 (reg n') ∧ ∀ r, r ≠ 8 → r ≠ 9 → reg n' r = reg n r
  | 0, k, _, hk, hk8, _, _, _, _ => absurd hk (by omega)
  | d + 1, k, n, hk, hk8, s, h8, h9, ha0 => by
    have hbt : BT.toNat + bootFnCode.length ≤ 0x600C4000 := by decide
    have hck : ∀ j, j ≤ 128 → CodeIn (mmuInv M j) BT bootFnCode := fun j hj => codeKeep hc hbt fun x hx => by
      unfold mmuInv
      rw [ite_eq_right]
      rw [BitVec.toNat_sub, show (mmuBase).toNat = 0x600C5000 from rfl]; omega
    have ha : (mmuBase + BitVec.ofNat 32 (4 * k)).toNat = 0x600C5000 + 4 * k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (mmuBase).toNat = 0x600C5000 from rfl]; omega
    obtain ⟨n1, c1, u1⟩ := s.block btInvBlk (hck k (by omega)) btInvBlk_end (by
      simp only [BlockOk, BInstr.ok, BInstr.run, btInvBlk]
      simp +decide only [upd, ↓reduceIte, true_and, and_true]
      rw [h8, add_lit_zero]
      exact ⟨by rw [ha]; omega, (sep_of_le (by rw [ha]; omega) (by rw [ha]; omega)).symm⟩)
    have m1 : (runBlock btInvBlk (mmuInv M k, reg n)).1 = mmuInv M (k + 1) := by
      simp +decide only [runBlock, BInstr.run, btInvBlk, upd, ↓reduceIte]
      rw [h8, ha0]; exact mmuInv_step M k hk8
    have r1 : ∀ r, reg n1 r = (runBlock btInvBlk (mmuInv M k, reg n)).2 r := fun r => by rw [u1.regs]
    have v8 : reg n1 8 = mmuBase + BitVec.ofNat 32 (4 * (k + 1)) := by
      rw [r1]; simp +decide only [runBlock, BInstr.run, btInvBlk, upd, ↓reduceIte]
      rw [h8]; show mmuBase + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 4 = _
      rw [add_ofNat_assoc, show 4 * k + 4 = 4 * (k + 1) by omega]
    have v9 : reg n1 9 = BitVec.ofNat 32 (128 - (k + 1)) := by
      rw [r1]; simp +decide only [runBlock, BInstr.run, btInvBlk, upd, ↓reduceIte]
      rw [h9]; apply BitVec.eq_of_toNat_eq
      show (BitVec.ofNat 32 (128 - k) + 0xFFFFFFFF).toNat = _
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 from rfl]
      omega
    have k1 : ∀ r, r ≠ 8 → r ≠ 9 → reg n1 r = reg n r := fun r h8' h9' => by
      rw [r1, runBlock_reg _ _ _ r s.zero (by simp only [btInvBlk]; revert h8' h9'; revert r; decide)]
    have s1 : St (mmuInv M (k + 1)) BT n1 0xA6 (reg n1) := ⟨u1.pc, by rw [u1.mem, m1], fun _ => rfl⟩
    by_cases hl : k + 1 < 128
    · obtain ⟨n2, d2, u2⟩ := s1.taken (hck _ (by omega)) 0xA0 bt_at_a6 (by decide) (by
        show (reg n1 9 != reg n1 x0) = true
        rw [v9, s1.zero]
        exact bne_iff_ne.mpr fun e => by
          have := congrArg BitVec.toNat e
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          exact absurd this (by show 128 - (k + 1) ≠ 0; omega))
      obtain ⟨n', c', s', k'⟩ := bt_inv hc d (k + 1) (by omega) hl
        (⟨u2.pc, u2.mem, fun _ => rfl⟩ : St (mmuInv M (k + 1)) BT n2 0xA0 (reg n2))
        (by rw [u2.regs]; exact v8) (by rw [u2.regs]; exact v9) (by rw [u2.regs, k1 a0 (by decide) (by decide)]; exact ha0)
      exact ⟨n', c1.trans (.cons d2 c'), s', fun r h8' h9' => by rw [k' r h8' h9', u2.regs, k1 r h8' h9']⟩
    · have e : k + 1 = 128 := by omega
      obtain ⟨n2, d2, u2⟩ := s1.notTaken (hck _ (by omega)) 0xA8 bt_at_a6 (by decide) (by
        show (reg n1 9 != reg n1 x0) = false
        rw [v9, s1.zero, e]; rfl)
      rw [e] at u2
      exact ⟨n2, c1.trans (.single d2), ⟨u2.pc, u2.mem, fun _ => rfl⟩, fun r h8' h9' => by rw [u2.regs, k1 r h8' h9']⟩

theorem st32_low (M : Word → BitVec 8) {a x : Word} (v : Word) (ha : 0x600C4000 ≤ a.toNat)
    (ha4 : a.toNat + 4 ≤ 2 ^ 32) (hx : x.toNat < 0x600C4000) : memStore32 M a v x = M x := by
  rw [st32_read, ite_eq_right]
  rw [BitVec.toNat_sub]; have := a.isLt; omega

theorem shl2_toNat (e : Word) (he : e.toNat ≤ 127) : ((e <<< 2) + mmuBase).toNat = 0x600C5000 + 4 * e.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show (mmuBase).toNat = 0x600C5000 from rfl]
  omega

theorem shl2_succ (e : Word) : ((e + 1) <<< 2) + mmuBase = (e <<< 2) + mmuBase + 4 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft,
    BitVec.toNat_add, Nat.shiftLeft_eq, Nat.shiftLeft_eq, show (1 : Word).toNat = 1 from rfl,
    show (4 : Word).toNat = 4 from rfl]
  have := e.isLt; omega

theorem mapSeg_low : ∀ (k : Nat) (M : Word → BitVec 8) (e v : Word) (x : Word), x.toNat < 0x600C4000 →
    mapSeg M e v k x = M x
  | 0, _, _, _, _, _ => rfl
  | k + 1, M, e, v, x, hx => by
    rw [mapSeg, mapSeg_low k _ _ _ x hx]
    by_cases he : e.toNat ≤ 127
    · rw [ite_eq_left he]; exact st32_low M _ (by rw [shl2_toNat e he]; omega) (by rw [shl2_toNat e he]; omega) hx
    · rw [ite_eq_right he]

def btSegBlk : List BInstr :=
  [.aluImm .and (8 : Fin 32) a5 0xFF, .sw a1 (8 : Fin 32) 0x0, .aluImm .add a1 a1 0x4, .aluImm .add a4 a4 0x1,
   .aluImm .add a5 a5 0x1, .aluImm .add a3 a3 0xFFFFFFFF]

theorem btSegBlk_end : blockEnd bootFnCode 0xEE btSegBlk = some 0xFC :=
  (blockEnd_cons' (off' := 0xF2) bt_at_ee rfl (blockEnd_cons' (off' := 0xF4) bt_at_f2 rfl (blockEnd_cons' (off' := 0xF6) bt_at_f4 rfl (blockEnd_cons' (off' := 0xF8) bt_at_f6 rfl (blockEnd_cons' (off' := 0xFA) bt_at_f8 rfl (blockEnd_cons' (off' := 0xFC) bt_at_fa rfl rfl))))))

def btSkipBlk : List BInstr :=
  [.aluImm .add a1 a1 0x4, .aluImm .add a4 a4 0x1, .aluImm .add a5 a5 0x1, .aluImm .add a3 a3 0xFFFFFFFF]

theorem btSkipBlk_end : blockEnd bootFnCode 0xF4 btSkipBlk = some 0xFC :=
  (blockEnd_cons' (off' := 0xF6) bt_at_f4 rfl (blockEnd_cons' (off' := 0xF8) bt_at_f6 rfl (blockEnd_cons' (off' := 0xFA) bt_at_f8 rfl (blockEnd_cons' (off' := 0xFC) bt_at_fa rfl rfl))))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- The loop that writes one flash segment's `k` MMU entries, from 0xEA to
the outer loop's head at 0xB2. -/
theorem bt_seg (hbt : BT.toNat + bootFnCode.length ≤ 0x600C4000) :
    ∀ k {M : Word → BitVec 8} {e v : Word} {n : Machine}, 0 < k → k < 2 ^ 32 → CodeIn M BT bootFnCode →
      St M BT n 0xEA (reg n) → reg n a4 = e → reg n a5 = v → reg n a3 = BitVec.ofNat 32 k →
      reg n a1 = (e <<< 2) + mmuBase → reg n a2 = 127 →
      ∃ n', Steps n n' ∧ St (mapSeg M e v k) BT n' 0xB2 (reg n') ∧
        ∀ r, r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 8 → reg n' r = reg n r
  | 0, _, _, _, _, hk, _, _, _, _, _, _, _, _ => absurd hk (by omega)
  | k + 1, M, e, v, n, _, hk, hc, s, h4, h5, h3, h1, h2 => by
    -- one pass: the store when `e` is in the table, then the increments
    obtain ⟨n1, c1, s1, M1, hM1, r1, k1⟩ : ∃ n1, Steps n n1 ∧ ∃ (_ : St (if e.toNat ≤ 127 then
        memStore32 M ((e <<< 2) + mmuBase) (v &&& 0xFF) else M) BT n1 0xFC (reg n1)), True ∧ True ∧
        (reg n1 a1 = ((e + 1) <<< 2) + mmuBase ∧ reg n1 a4 = e + 1 ∧ reg n1 a5 = v + 1 ∧
          reg n1 a3 = BitVec.ofNat 32 k) ∧
        ∀ r, r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 8 → reg n1 r = reg n r := by
      have hinc : ∀ (f : Fin 32 → Word), f a1 = (e <<< 2) + mmuBase → f a4 = e → f a5 = v →
          f a3 = BitVec.ofNat 32 (k + 1) →
          aluEval .add (f a1) 0x4 = ((e + 1) <<< 2) + mmuBase ∧ aluEval .add (f a4) 0x1 = e + 1 ∧
            aluEval .add (f a5) 0x1 = v + 1 ∧ aluEval .add (f a3) 0xFFFFFFFF = BitVec.ofNat 32 k := by
        intro f e1 e4 e5 e3
        refine ⟨by rw [e1, shl2_succ]; rfl, by rw [e4]; rfl, by rw [e5]; rfl, ?_⟩
        rw [e3]; apply BitVec.eq_of_toNat_eq
        show (BitVec.ofNat 32 (k + 1) + 0xFFFFFFFF).toNat = _
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 from rfl]
        omega
      by_cases he : e.toNat ≤ 127
      · obtain ⟨n0, d0, u0⟩ := s.notTaken hc 0xEE bt_at_ea (by decide) (by
          show (reg n a2).ult (reg n a4) = false
          rw [h2, h4]; simp only [BitVec.ult, BitVec.toNat_ofNat]; exact decide_eq_false (by
            show ¬ 127 < e.toNat; omega))
        have t0 : St M BT n0 0xEE (reg n0) := ⟨u0.pc, u0.mem, fun _ => rfl⟩
        have ha := shl2_toNat e he
        obtain ⟨n1, c1, u1⟩ := t0.block btSegBlk hc btSegBlk_end (by
          simp only [BlockOk, BInstr.ok, BInstr.run, btSegBlk]
          simp +decide only [upd, ↓reduceIte, true_and, and_true]
          rw [u0.regs, h1, add_lit_zero]
          exact ⟨by rw [ha]; omega, (sep_of_le (by rw [ha]; omega) (by rw [ha]; omega)).symm⟩)
        have rr : ∀ r, reg n1 r = (runBlock btSegBlk (M, reg n0)).2 r := fun r => by rw [u1.regs]
        obtain ⟨i1, i4, i5, i3⟩ := hinc (reg n0) (by rw [u0.regs]; exact h1) (by rw [u0.regs]; exact h4)
          (by rw [u0.regs]; exact h5) (by rw [u0.regs]; exact h3)
        refine ⟨n1, .cons d0 c1, ⟨u1.pc, ?_, fun _ => rfl⟩, trivial, trivial, ⟨?_, ?_, ?_, ?_⟩, fun r h1' h3' h4' h5' h8' => ?_⟩
        · rw [u1.mem, ite_eq_left he]
          simp +decide only [runBlock, BInstr.run, btSegBlk, upd, ↓reduceIte]
          rw [u0.regs, u0.regs, h1, h5, add_lit_zero]; rfl
        · rw [rr]; simp +decide only [runBlock, BInstr.run, btSegBlk, upd, ↓reduceIte]; exact i1
        · rw [rr]; simp +decide only [runBlock, BInstr.run, btSegBlk, upd, ↓reduceIte]; exact i4
        · rw [rr]; simp +decide only [runBlock, BInstr.run, btSegBlk, upd, ↓reduceIte]; exact i5
        · rw [rr]; simp +decide only [runBlock, BInstr.run, btSegBlk, upd, ↓reduceIte]; exact i3
        · rw [rr, runBlock_reg _ _ _ r t0.zero (by simp only [btSegBlk]; revert h1' h3' h4' h5' h8'; revert r; decide),
            u0.regs]
      · obtain ⟨n0, d0, u0⟩ := s.taken hc 0xF4 bt_at_ea (by decide) (by
          show (reg n a2).ult (reg n a4) = true
          rw [h2, h4]; simp only [BitVec.ult, BitVec.toNat_ofNat]; exact decide_eq_true (by
            show 127 < e.toNat; omega))
        have t0 : St M BT n0 0xF4 (reg n0) := ⟨u0.pc, u0.mem, fun _ => rfl⟩
        obtain ⟨n1, c1, u1⟩ := t0.block btSkipBlk hc btSkipBlk_end ⟨trivial, trivial, trivial, trivial, trivial⟩
        have rr : ∀ r, reg n1 r = (runBlock btSkipBlk (M, reg n0)).2 r := fun r => by rw [u1.regs]
        obtain ⟨i1, i4, i5, i3⟩ := hinc (reg n0) (by rw [u0.regs]; exact h1) (by rw [u0.regs]; exact h4)
          (by rw [u0.regs]; exact h5) (by rw [u0.regs]; exact h3)
        refine ⟨n1, .cons d0 c1, ⟨u1.pc, by rw [u1.mem, ite_eq_right he]; rfl, fun _ => rfl⟩, trivial, trivial,
          ⟨?_, ?_, ?_, ?_⟩, fun r h1' h3' h4' h5' h8' => ?_⟩
        · rw [rr]; simp +decide only [runBlock, BInstr.run, btSkipBlk, upd, ↓reduceIte]; exact i1
        · rw [rr]; simp +decide only [runBlock, BInstr.run, btSkipBlk, upd, ↓reduceIte]; exact i4
        · rw [rr]; simp +decide only [runBlock, BInstr.run, btSkipBlk, upd, ↓reduceIte]; exact i5
        · rw [rr]; simp +decide only [runBlock, BInstr.run, btSkipBlk, upd, ↓reduceIte]; exact i3
        · rw [rr, runBlock_reg _ _ _ r t0.zero (by simp only [btSkipBlk]; revert h1' h3' h4' h5' h8'; revert r; decide),
            u0.regs]
    obtain ⟨v1, v4, v5, v3⟩ := r1
    have hc1 : CodeIn (if e.toNat ≤ 127 then memStore32 M ((e <<< 2) + mmuBase) (v &&& 0xFF) else M) BT bootFnCode :=
      codeKeep hc hbt fun x hx => by
        by_cases he : e.toNat ≤ 127
        · rw [ite_eq_left he]; exact st32_low M _ (by rw [shl2_toNat e he]; omega) (by rw [shl2_toNat e he]; omega) hx
        · rw [ite_eq_right he]
    by_cases hk0 : k = 0
    · subst hk0
      obtain ⟨n2, d2, u2⟩ := s1.taken hc1 0xB2 bt_at_fc (by decide) (by
        show (reg n1 a3 == reg n1 x0) = true; rw [v3, s1.zero]; rfl)
      exact ⟨n2, c1.trans (.single d2), ⟨u2.pc, u2.mem, fun _ => rfl⟩, fun r h1' h3' h4' h5' h8' => by
        rw [u2.regs, k1 r h1' h3' h4' h5' h8']⟩
    · obtain ⟨n2, d2, u2⟩ := s1.notTaken hc1 0xFE bt_at_fc (by decide) (by
        show (reg n1 a3 == reg n1 x0) = false; rw [v3, s1.zero]
        exact decide_eq_false fun e' => hk0 (by
          have := congrArg BitVec.toNat e'; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; exact this))
      have t2 : St _ BT n2 0xFE (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
      obtain ⟨n3, d3, u3⟩ := t2.jump hc1 bt_at_fe (off' := 0xEA) (by decide) (by rw [t2.pc]; decide)
      obtain ⟨n', c', s', k'⟩ := bt_seg hbt k (e := e + 1) (v := v + 1) (by omega) (by omega) hc1
        (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St _ BT n3 0xEA (reg n3))
        (by rw [u3.regs, u2.regs]; exact v4) (by rw [u3.regs, u2.regs]; exact v5) (by rw [u3.regs, u2.regs]; exact v3)
        (by rw [u3.regs, u2.regs]; exact v1)
        (by rw [u3.regs, u2.regs, k1 a2 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h2)
      refine ⟨n', c1.trans (.cons d2 (.cons d3 c')), ?_, fun r h1' h3' h4' h5' h8' => ?_⟩
      · rw [mapSeg]; exact s'
      · rw [k' r h1' h3' h4' h5' h8', u3.regs, u2.regs, k1 r h1' h3' h4' h5' h8']

theorem mmuMap_low {M0 : Word → BitVec 8} {acc imgf : Word} {M : Word → BitVec 8} :
    ∀ (j : Nat) (x : Word), x.toNat < 0x600C4000 → mmuMap M0 acc imgf M j x = M x
  | 0, _, _ => rfl
  | j + 1, x, hx => by
    rw [mmuMap]
    by_cases h : (sgKind M0 acc j).toNat < 2
    · rw [ite_eq_left h, mapSeg_low _ _ _ _ x hx, mmuMap_low j x hx]
    · rw [ite_eq_right h, mmuMap_low j x hx]

theorem kind4 (k : BitVec 8) (h : k.toNat ≤ 3) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
  rcases (show k.toNat = 0 ∨ k.toNat = 1 ∨ k.toNat = 2 ∨ k.toNat = 3 by omega) with e | e | e | e
  · exact Or.inl (BitVec.eq_of_toNat_eq e)
  · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq e))
  · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq e)))
  · exact Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq e)))

def btMapA : List BInstr :=
  [.alu .add a3 x0 (24 : Fin 32), .lbu a4 (24 : Fin 32) 0xC, .aluImm .add a5 a4 0xFFFFFFFE,
   .aluImm .add (24 : Fin 32) (24 : Fin 32) 0x10, .lui a1 0xBE000000]

theorem btMapA_end : blockEnd bootFnCode 0xB6 btMapA = some 0xC6 :=
  (blockEnd_cons' (off' := 0xB8) bt_at_b6 rfl (blockEnd_cons' (off' := 0xBC) bt_at_b8 rfl (blockEnd_cons' (off' := 0xC0) bt_at_bc rfl (blockEnd_cons' (off' := 0xC2) bt_at_c0 rfl (blockEnd_cons' (off' := 0xC6) bt_at_c2 rfl rfl)))))

def btMapB : List BInstr := [.lw a4 a3 0x0, .lw a5 a3 0x4]

theorem btMapB_end : blockEnd bootFnCode 0xD0 btMapB = some 0xD4 :=
  (blockEnd_cons' (off' := 0xD2) bt_at_d0 rfl (blockEnd_cons' (off' := 0xD4) bt_at_d2 rfl rfl))

def btMapC : List BInstr :=
  [.alu .add a1 a1 a4, .aluImm .srl a4 a1 0x10, .alu .add a5 a5 (21 : Fin 32), .aluImm .sll a1 a4 0x2,
   .aluImm .srl a5 a5 0x10, .alu .add a1 a1 (9 : Fin 32)]

theorem btMapC_end : blockEnd bootFnCode 0xD8 btMapC = some 0xE8 :=
  (blockEnd_cons' (off' := 0xDA) bt_at_d8 rfl (blockEnd_cons' (off' := 0xDE) bt_at_da rfl (blockEnd_cons' (off' := 0xE0) bt_at_de rfl (blockEnd_cons' (off' := 0xE4) bt_at_e0 rfl (blockEnd_cons' (off' := 0xE6) bt_at_e4 rfl (blockEnd_cons' (off' := 0xE8) bt_at_e6 rfl rfl))))))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- The loop over the segments that writes each flash segment's MMU
entries, from the head of pass `j` at 0xB2 to its exit at 0x100. -/
theorem bt_map (hbt : BT.toNat + bootFnCode.length ≤ 0x600C4000) {M0 Mi : Word → BitVec 8} {acc imgf : Word}
    {N : Nat} (hN : N ≤ 16) (hacc : acc.toNat % 4 = 0) (hal : acc.toNat + 0x10C ≤ 0x40000000)
    (hkind : ∀ j, j < N → (sgKind M0 acc j).toNat ≤ 3)
    (hT : ∀ i, i < 0x10C → Mi (acc + BitVec.ofNat 32 i) = M0 (acc + BitVec.ofNat 32 i))
    (hci : CodeIn Mi BT bootFnCode) :
    ∀ d j {n : Machine}, j + d = N → j ≤ N → St (mmuMap M0 acc imgf Mi j) BT n 0xB2 (reg n) →
      reg n 24 = sgPtr acc j → reg n 22 = sgPtr acc N → reg n a0 = 2 → reg n a2 = 127 → reg n 9 = mmuBase →
      reg n 21 = imgf →
      ∃ n', Steps n n' ∧ St (mmuMap M0 acc imgf Mi N) BT n' 0x100 (reg n') ∧
        ∀ r, r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 8 → r ≠ 24 → reg n' r = reg n r
  | 0, j, n, hj, _, s, h24, h22, _, _, _, _ => by
    obtain rfl : j = N := by omega
    have hc := codeKeep (M' := mmuMap M0 acc imgf Mi j) hci hbt fun x hx => mmuMap_low j x hx
    obtain ⟨n1, d1, u1⟩ := s.taken hc 0x100 bt_at_b2 (by decide) (by
      show (reg n 24 == reg n 22) = true; rw [h24, h22]; exact decide_eq_true rfl)
    exact ⟨n1, .single d1, ⟨u1.pc, u1.mem, fun _ => rfl⟩, fun r _ _ _ _ _ _ => by rw [u1.regs]⟩
  | d + 1, j, n, hj, hjN, s, h24, h22, ha0, ha2, h9, h21 => by
    have hjl : j < N := by omega
    have hc := codeKeep (M' := mmuMap M0 acc imgf Mi j) hci hbt fun x hx => mmuMap_low j x hx
    have hp : (sgPtr acc j).toNat = acc.toNat + 16 * j := by
      unfold sgPtr; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hF : ∀ c, c < 16 → mmuMap M0 acc imgf Mi j (sgPtr acc j + BitVec.ofNat 32 c) =
        M0 (sgPtr acc j + BitVec.ofNat 32 c) := fun c hc' => by
      rw [mmuMap_low j _ (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, hp]; omega)]
      unfold sgPtr; rw [add_ofNat_assoc]; exact hT _ (by omega)
    have hL : ∀ c, c ≤ 12 → memLoad32 (mmuMap M0 acc imgf Mi j) (sgPtr acc j + BitVec.ofNat 32 c) =
        memLoad32 M0 (sgPtr acc j + BitVec.ofNat 32 c) := fun c hc' =>
      memLoad32_congr fun i hi => by rw [add_ofNat_assoc]; exact hF _ (by omega)
    obtain ⟨n1, d1, u1⟩ := s.notTaken hc 0xB6 bt_at_b2 (by decide) (by
      show (reg n 24 == reg n 22) = false; rw [h24, h22]
      exact decide_eq_false fun e => by
        have := congrArg BitVec.toNat e; unfold sgPtr at this
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega)
    have t1 : St (mmuMap M0 acc imgf Mi j) BT n1 0xB6 (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
    obtain ⟨n2, c2, u2⟩ := t1.block btMapA hc btMapA_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
    have r2 : ∀ r, reg n2 r = (runBlock btMapA (mmuMap M0 acc imgf Mi j, reg n1)).2 r := fun r => by rw [u2.regs]
    have t2 : St (mmuMap M0 acc imgf Mi j) BT n2 0xC6 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
    have hkd : (mmuMap M0 acc imgf Mi j (reg n1 24 + 0xC)) = sgKind M0 acc j := by
      rw [u1.regs, h24]; exact hF 12 (by decide)
    have v4 : reg n2 a4 = (sgKind M0 acc j).zeroExtend 32 := by
      rw [r2]; simp +decide only [runBlock, BInstr.run, btMapA, upd, ↓reduceIte]; rw [hkd]
    have v5 : reg n2 a5 = (sgKind M0 acc j).zeroExtend 32 + 0xFFFFFFFE := by
      rw [r2]; simp +decide only [runBlock, BInstr.run, btMapA, upd, ↓reduceIte]; rw [hkd]; rfl
    have v3 : reg n2 a3 = sgPtr acc j := by
      rw [r2]; simp +decide only [runBlock, BInstr.run, btMapA, upd, ↓reduceIte]; rw [t1.zero, u1.regs, h24]
      exact BitVec.zero_add _
    have v24 : reg n2 24 = sgPtr acc (j + 1) := by
      rw [r2]; simp +decide only [runBlock, BInstr.run, btMapA, upd, ↓reduceIte]; rw [u1.regs, h24]
      unfold sgPtr; show acc + BitVec.ofNat 32 (16 * j) + BitVec.ofNat 32 16 = _
      rw [add_ofNat_assoc]; rfl
    have v1 : reg n2 a1 = 0xBE000000 := by
      rw [r2]; simp +decide only [runBlock, BInstr.run, btMapA, upd, ↓reduceIte]
    have k2 : ∀ r, r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 24 → reg n2 r = reg n r := fun r h1 h3 h4 h5 h24' => by
      rw [r2, runBlock_reg _ _ _ r t1.zero (by simp only [btMapA]; revert h1 h3 h4 h5 h24'; revert r; decide), u1.regs]
    -- the rest of the loop from 0xB2, after this segment
    have next : ∀ {n' : Machine}, St (mmuMap M0 acc imgf Mi (j + 1)) BT n' 0xB2 (reg n') →
        (∀ r, r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 8 → r ≠ 24 → reg n' r = reg n r) → reg n' 24 = sgPtr acc (j + 1) →
        ∃ n'', Steps n' n'' ∧ St (mmuMap M0 acc imgf Mi N) BT n'' 0x100 (reg n'') ∧
          ∀ r, r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 8 → r ≠ 24 → reg n'' r = reg n r := by
      intro n' s' k' h24'
      obtain ⟨n'', c'', s'', k''⟩ := bt_map hbt hN hacc hal hkind hT hci d (j + 1) (by omega) (by omega) s' h24'
        (by rw [k' 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h22)
        (by rw [k' a0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ha0)
        (by rw [k' a2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ha2)
        (by rw [k' 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h9)
        (by rw [k' 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h21)
      exact ⟨n'', c'', s'', fun r h1 h3 h4 h5 h8 h24'' => by rw [k'' r h1 h3 h4 h5 h8 h24'', k' r h1 h3 h4 h5 h8 h24'']⟩
    have hk3 := hkind j hjl
    by_cases hram : 2 ≤ (sgKind M0 acc j).toNat
    · -- a RAM segment: no entries
      obtain ⟨n3, d3, u3⟩ := t2.taken hc 0xB2 bt_at_c6 (by decide) (by
        show (reg n2 a5).ult (reg n2 a0) = true
        rw [v5, k2 a0 (by decide) (by decide) (by decide) (by decide) (by decide), ha0]
        rcases kind4 _ hk3 with e | e | e | e <;> rw [e] at hram ⊢ <;> first | exact absurd hram (by decide) | rfl)
      have hm : mmuMap M0 acc imgf Mi (j + 1) = mmuMap M0 acc imgf Mi j := by
        rw [mmuMap, ite_eq_right (by omega)]
      obtain ⟨n', c', s', k'⟩ := next (n' := n3) (by rw [hm]; exact ⟨u3.pc, u3.mem, fun _ => rfl⟩)
        (fun r h1 h3 h4 h5 _ h24' => by rw [u3.regs, k2 r h1 h3 h4 h5 h24']) (by rw [u3.regs]; exact v24)
      exact ⟨n', .cons d1 (c2.trans (.cons d3 c')), s', k'⟩
    · obtain ⟨n3, d3, u3⟩ := t2.notTaken hc 0xCA bt_at_c6 (by decide) (by
        show (reg n2 a5).ult (reg n2 a0) = false
        rw [v5, k2 a0 (by decide) (by decide) (by decide) (by decide) (by decide), ha0]
        rcases kind4 _ hk3 with e | e | e | e <;> rw [e] at hram ⊢ <;> first | exact absurd hram (by decide) | rfl)
      have t3 : St (mmuMap M0 acc imgf Mi j) BT n3 0xCA (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
      -- the window base for flash code or flash data, at 0xD0
      obtain ⟨n4, c4, t4, v14, k4⟩ : ∃ n4, Steps n3 n4 ∧ St (mmuMap M0 acc imgf Mi j) BT n4 0xD0 (reg n4) ∧
          reg n4 a1 = (if sgKind M0 acc j = 0 then 0xBE000000 else 0xC4000000) ∧
          ∀ r, r ≠ a1 → reg n4 r = reg n2 r := by
        rcases kind4 _ hk3 with e | e | e | e
        · obtain ⟨n4, d4, u4⟩ := t3.taken hc 0xD0 bt_at_ca (by decide) (by
            show (reg n3 a4 == reg n3 x0) = true; rw [u3.regs, u3.regs, v4, t2.zero, e]; rfl)
          exact ⟨n4, .single d4, ⟨u4.pc, u4.mem, fun _ => rfl⟩, by rw [u4.regs, u3.regs, v1, ite_eq_left e],
            fun r _ => by rw [u4.regs, u3.regs]⟩
        · obtain ⟨n4, d4, u4⟩ := t3.notTaken hc 0xCC bt_at_ca (by decide) (by
            show (reg n3 a4 == reg n3 x0) = false; rw [u3.regs, u3.regs, v4, t2.zero, e]; rfl)
          have t4 : St (mmuMap M0 acc imgf Mi j) BT n4 0xCC (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
          obtain ⟨n5, d5, u5⟩ := t4.lui hc bt_at_cc (off' := 0xD0) (by decide)
          refine ⟨n5, .cons d4 (.single d5), ⟨u5.pc, u5.mem, fun _ => rfl⟩, ?_, fun r h => ?_⟩
          · rw [u5.regs, ite_eq_right (by rw [e]; decide)]; simp +decide only [upd, ↓reduceIte]
          · rw [u5.regs, updz t4.zero h, u4.regs, u3.regs]
        · rw [e] at hram; exact absurd hram (by decide)
        · rw [e] at hram; exact absurd hram (by decide)
      have a3_4 : reg n4 a3 = sgPtr acc j := by rw [k4 a3 (by decide)]; exact v3
      obtain ⟨n5, c5, u5⟩ := t4.block btMapB hc btMapB_end (by
        simp only [BlockOk, BInstr.ok, BInstr.run, btMapB]
        simp +decide only [upd, ↓reduceIte, true_and, and_true]
        rw [a3_4]
        refine ⟨?_, ?_⟩ <;> rw [BitVec.toNat_add, hp] <;> simp <;> omega)
      have t5 : St (mmuMap M0 acc imgf Mi j) BT n5 0xD4 (reg n5) := ⟨u5.pc, u5.mem, fun _ => rfl⟩
      have r5 : ∀ r, reg n5 r = (runBlock btMapB (mmuMap M0 acc imgf Mi j, reg n4)).2 r := fun r => by rw [u5.regs]
      have v4_5 : reg n5 a4 = sgAddr M0 acc j := by
        rw [r5]; simp +decide only [runBlock, BInstr.run, btMapB, upd, ↓reduceIte]; rw [a3_4]
        exact hL 0 (by decide)
      have v5_5 : reg n5 a5 = sgOff M0 acc j := by
        rw [r5]; simp +decide only [runBlock, BInstr.run, btMapB, upd, ↓reduceIte]; rw [a3_4]
        exact hL 4 (by decide)
      have k5 : ∀ r, r ≠ a4 → r ≠ a5 → reg n5 r = reg n4 r := fun r h4 h5 => by
        rw [r5, runBlock_reg _ _ _ r t4.zero (by simp only [btMapB]; revert h4 h5; revert r; decide)]
      obtain ⟨n6, d6, u6⟩ := t5.lhu hc bt_at_d4 (off' := 0xD8) (by decide) (by
        rw [k5 a3 (by decide) (by decide), a3_4, BitVec.toNat_add, hp]; simp; omega)
      have t6 : St (mmuMap M0 acc imgf Mi j) BT n6 0xD8 (reg n6) := ⟨u6.pc, u6.mem, fun _ => rfl⟩
      have v3_6 : reg n6 a3 = sgPages M0 acc j := by
        rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
        rw [k5 a3 (by decide) (by decide), a3_4]; unfold sgPages
        rw [show sgPtr acc j + 0xA + 1 = sgPtr acc j + BitVec.ofNat 32 11 by rw [BitVec.add_assoc]; rfl,
          show sgPtr acc j + 0xA = sgPtr acc j + BitVec.ofNat 32 10 from rfl, hF 11 (by decide), hF 10 (by decide)]
      have k6 : ∀ r, r ≠ a3 → reg n6 r = reg n5 r := fun r h => by rw [u6.regs]; exact updz t5.zero h
      obtain ⟨n7, c7, u7⟩ := t6.block btMapC hc btMapC_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
      have t7 : St (mmuMap M0 acc imgf Mi j) BT n7 0xE8 (reg n7) := ⟨u7.pc, u7.mem, fun _ => rfl⟩
      have r7 : ∀ r, reg n7 r = (runBlock btMapC (mmuMap M0 acc imgf Mi j, reg n6)).2 r := fun r => by rw [u7.regs]
      have g4 : reg n6 a4 = sgAddr M0 acc j := by rw [k6 a4 (by decide)]; exact v4_5
      have g5 : reg n6 a5 = sgOff M0 acc j := by rw [k6 a5 (by decide)]; exact v5_5
      have g1 : reg n6 a1 = (if sgKind M0 acc j = 0 then 0xBE000000 else 0xC4000000) := by
        rw [k6 a1 (by decide), k5 a1 (by decide) (by decide)]; exact v14
      have g21 : reg n6 21 = imgf := by
        rw [k6 21 (by decide), k5 21 (by decide) (by decide), k4 21 (by decide),
          k2 21 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h21
      have g9 : reg n6 9 = mmuBase := by
        rw [k6 9 (by decide), k5 9 (by decide) (by decide), k4 9 (by decide),
          k2 9 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h9
      have w4 : reg n7 a4 = sgEntry M0 acc j := by
        rw [r7]; simp +decide only [runBlock, BInstr.run, btMapC, upd, ↓reduceIte]; rw [g1, g4]; rfl
      have w5 : reg n7 a5 = sgPage M0 acc imgf j := by
        rw [r7]; simp +decide only [runBlock, BInstr.run, btMapC, upd, ↓reduceIte]; rw [g5, g21]; rfl
      have w1 : reg n7 a1 = (sgEntry M0 acc j <<< 2) + mmuBase := by
        rw [r7]; simp +decide only [runBlock, BInstr.run, btMapC, upd, ↓reduceIte]; rw [g1, g4, g9]; rfl
      have w3 : reg n7 a3 = sgPages M0 acc j := by
        rw [r7, runBlock_reg _ _ _ a3 t6.zero (by decide)]; exact v3_6
      have k7 : ∀ r, r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 24 → reg n7 r = reg n r := fun r h1 h3 h4 h5 h24' => by
        rw [r7, runBlock_reg _ _ _ r t6.zero (by simp only [btMapC]; revert h1 h4 h5; revert r; decide), k6 r h3,
          k5 r h4 h5, k4 r h1, k2 r h1 h3 h4 h5 h24']
      have hm : mmuMap M0 acc imgf Mi (j + 1) = mapSeg (mmuMap M0 acc imgf Mi j) (sgEntry M0 acc j)
          (sgPage M0 acc imgf j) (sgPages M0 acc j).toNat := by
        rw [mmuMap, ite_eq_left (by omega)]
      have hpg : (sgPages M0 acc j).toNat < 2 ^ 16 := by
        unfold sgPages; rw [BitVec.toNat_setWidth]; have := (M0 (sgPtr acc j + 0xA + 1) ++ M0 (sgPtr acc j + 0xA)).isLt
        omega
      by_cases hz : (sgPages M0 acc j).toNat = 0
      · obtain ⟨n8, d8, u8⟩ := t7.taken hc 0xB2 bt_at_e8 (by decide) (by
          show (reg n7 a3 == reg n7 x0) = true
          rw [w3, t7.zero, show sgPages M0 acc j = 0 from BitVec.eq_of_toNat_eq hz]; rfl)
        rw [hz, mapSeg] at hm
        obtain ⟨n', c', s', k'⟩ := next (n' := n8) (by rw [hm]; exact ⟨u8.pc, u8.mem, fun _ => rfl⟩)
          (fun r h1 h3 h4 h5 _ h24' => by rw [u8.regs, k7 r h1 h3 h4 h5 h24'])
          (by rw [u8.regs, r7, runBlock_reg _ _ _ 24 t6.zero (by decide), k6 24 (by decide),
            k5 24 (by decide) (by decide), k4 24 (by decide)]; exact v24)
        exact ⟨n', .cons d1 (c2.trans (.cons d3 (c4.trans (c5.trans (.cons d6 (c7.trans (.cons d8 c'))))))), s', k'⟩
      · obtain ⟨n8, d8, u8⟩ := t7.notTaken hc 0xEA bt_at_e8 (by decide) (by
          show (reg n7 a3 == reg n7 x0) = false
          rw [w3, t7.zero]; exact decide_eq_false fun e => hz (by rw [e]; rfl))
        have hc' := codeKeep (M' := mmuMap M0 acc imgf Mi j) hci hbt fun x hx => mmuMap_low j x hx
        obtain ⟨n9, c9, s9, k9⟩ := bt_seg hbt (sgPages M0 acc j).toNat (M := mmuMap M0 acc imgf Mi j)
          (e := sgEntry M0 acc j) (v := sgPage M0 acc imgf j) (by omega) (by omega) hc'
          (⟨u8.pc, u8.mem, fun _ => rfl⟩ : St _ BT n8 0xEA (reg n8)) (by rw [u8.regs]; exact w4)
          (by rw [u8.regs]; exact w5) (by rw [u8.regs, w3, BitVec.ofNat_toNat, BitVec.setWidth_eq])
          (by rw [u8.regs]; exact w1)
          (by rw [u8.regs, k7 a2 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ha2)
        rw [← hm] at s9
        obtain ⟨n', c', s', k'⟩ := next s9
          (fun r h1 h3 h4 h5 h8 h24' => by rw [k9 r h1 h3 h4 h5 h8, u8.regs, k7 r h1 h3 h4 h5 h24'])
          (by rw [k9 24 (by decide) (by decide) (by decide) (by decide) (by decide), u8.regs, r7,
            runBlock_reg _ _ _ 24 t6.zero (by decide), k6 24 (by decide), k5 24 (by decide) (by decide),
            k4 24 (by decide)]; exact v24)
        exact ⟨n', .cons d1 (c2.trans (.cons d3 (c4.trans (c5.trans (.cons d6 (c7.trans (.cons d8 (c9.trans c')))))))),
          s', k'⟩

/-- The stack `boot` and its callees use: its own 0x30 bytes, then
`flash_read_words`' 16 and the ROM's `R` below them, and `romStack` for the
other ROM routines. -/
def btK (R romStack : Nat) : Nat := 0x30 + 16 + R + romStack

/-- `M` matches `M0` from the start of the ROM to the MMU registers, where
the code `boot` runs and calls is. -/
def BtHi (M0 M : Word → BitVec 8) : Prop := ∀ x : Word, 0x40000000 ≤ x.toNat → x.toNat < 0x600C4000 → M x = M0 x

/-- What `boot` needs of its arguments and memory: the stack in data RAM,
the accepted header below the ROM and apart from the stack, segment kinds
0 to 3, and each RAM segment word-aligned, below the ROM, and apart from
the header and the stack. -/
structure BtCtx (M0 : Word → BitVec 8) (top acc imgf : Word) (R romStack : Nat) (romBase : Word)
    (romCode : List Nat) : Prop where
  code : CodeIn M0 BT bootFnCode
  rfw : CodeIn M0 (BitVec.ofNat 32 romFlashReadWordsAddress) romFlashReadWordsCode
  panic : PanicCode M0
  rom : CodeIn M0 romBase romCode
  hrb : 0x40000000 ≤ romBase.toNat
  hrl : romBase.toNat + romCode.length ≤ 0x600C4000
  hsp : top.toNat % 16 = 0
  hspl : 0x3FC80000 + 0x40 + btK R romStack ≤ top.toNat
  hsph : top.toNat ≤ dramEnd
  hR : R % 4 = 0
  hacc : acc.toNat % 4 = 0
  haccl : acc.toNat + 0x10C ≤ 0x40000000
  sAS : Sep acc 0x10C (top - BitVec.ofNat 32 (btK R romStack)) (btK R romStack)
  kind : ∀ j, j < sgCount M0 acc → (sgKind M0 acc j).toNat ≤ 3
  ram : ∀ j, j < sgCount M0 acc → 2 ≤ (sgKind M0 acc j).toNat →
    (sgDest M0 acc j).toNat % 4 = 0 ∧ (sgDest M0 acc j).toNat + sgBytes M0 acc j ≤ 0x40000000 ∧
    Sep (sgDest M0 acc j) (sgBytes M0 acc j) acc 0x10C ∧
    Sep (sgDest M0 acc j) (sgBytes M0 acc j) (top - BitVec.ofNat 32 (btK R romStack)) (btK R romStack) ∧
    (sgSrc M0 acc imgf j).toNat % 4 = 0

theorem sgCount_le (M : Word → BitVec 8) (acc : Word) : sgCount M acc ≤ 16 := by
  unfold sgCount; split <;> omega

theorem copyIn_out {M : Word → BitVec 8} {dst x : Word} {n : Nat} {b : Nat → BitVec 8} (h : Sep dst n x 1) :
    copyIn M dst n b x = M x := by
  unfold copyIn
  rw [ite_eq_right fun hl => h _ hl 0 (by decide) (by
    rw [add_ofNat_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel])]

theorem ramLoad_out {flash : Nat → BitVec 8} {M0 : Word → BitVec 8} {acc imgf : Word} (x : Word) :
    ∀ j, (∀ i, i < j → 2 ≤ (sgKind M0 acc i).toNat → Sep (sgDest M0 acc i) (sgBytes M0 acc i) x 1) →
      ramLoad flash M0 acc imgf j x = M0 x
  | 0, _ => rfl
  | j + 1, h => by
    rw [ramLoad]
    by_cases hk : 2 ≤ (sgKind M0 acc j).toNat
    · rw [ite_eq_left hk, copyIn_out (h j (by omega) hk), ramLoad_out x j fun i hi => h i (by omega)]
    · rw [ite_eq_right hk, ramLoad_out x j fun i hi => h i (by omega)]

theorem sep_hi {a x : Word} {n : Nat} (h : a.toNat + n ≤ 0x40000000) (hx : 0x40000000 ≤ x.toNat) : Sep a n x 1 :=
  sep_of_le (by omega) (by have := x.isLt; omega)

theorem panicFns_mid : ∀ p ∈ panicFns, 0x40000000 ≤ p.1 ∧ p.1 + p.2.length ≤ 0x600C4000 := by decide

theorem panicKeep {M0 M : Word → BitVec 8} (hP : PanicCode M0) (h : BtHi M0 M) : PanicCode M := fun p hp i hi => by
  have := panicFns_mid p hp
  rw [h _ (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)
    (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)]
  exact hP p hp i hi

theorem hiKeep {M0 M : Word → BitVec 8} {b : Word} {code : List Nat} (hc : CodeIn M0 b code) (h : BtHi M0 M)
    (hb : 0x40000000 ≤ b.toNat) (hl : b.toNat + code.length ≤ 0x600C4000) : CodeIn M b code := fun i hi => by
  rw [h _ (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
  exact hc i hi

def btCopyB : List BInstr := [.lw a0 (9 : Fin 32) 0x4, .lw a2 (9 : Fin 32) 0x8, .alu .add a0 a0 (21 : Fin 32), .aluImm .srl a2 a2 0x2]

theorem btCopyB_end : blockEnd bootFnCode 0x70 btCopyB = some 0x78 :=
  (blockEnd_cons' (off' := 0x72) bt_at_70 rfl (blockEnd_cons' (off' := 0x74) bt_at_72 rfl (blockEnd_cons' (off' := 0x76) bt_at_74 rfl (blockEnd_cons' (off' := 0x78) bt_at_76 rfl rfl))))

def btNextB : List BInstr := [.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x10, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFF0]

theorem btNextB_end : blockEnd bootFnCode 0x82 btNextB = some 0x86 :=
  (blockEnd_cons' (off' := 0x84) bt_at_82 rfl (blockEnd_cons' (off' := 0x86) bt_at_84 rfl rfl))

section Copy
variable {flash : Nat → BitVec 8} {M0 : Word → BitVec 8} {top acc imgf romBase : Word} {R romStack : Nat}
  {romCode : List Nat}

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- The loop that copies each RAM segment from flash, from the head of
pass `j` at 0x5C to its exit at 0x88, or to `halt` when a read fails. -/
theorem bt_copy (C : BtCtx M0 top acc imgf R romStack romBase romCode) (hROM : RomRead flash R romBase romCode) :
    ∀ d j {n : Machine}, j + d = sgCount M0 acc → j < sgCount M0 acc → St n.mem BT n 0x5C (reg n) →
      BtHi M0 n.mem →
      (∀ x, Sep (top - BitVec.ofNat 32 (btK R romStack)) (btK R romStack) x 1 →
        n.mem x = ramLoad flash M0 acc imgf j x) →
      reg n sp = top + 0xFFFFFFD0 → reg n 9 = sgPtr acc j → reg n 8 = BitVec.ofNat 32 (16 * (sgCount M0 acc - j)) →
      reg n 19 = 2 → reg n 23 = 0xFF900000 → reg n 21 = imgf →
      (∃ n', Steps n n' ∧ St n'.mem BT n' 0x88 (reg n') ∧ BtHi M0 n'.mem ∧
        (∀ x, Sep (top - BitVec.ofNat 32 (btK R romStack)) (btK R romStack) x 1 →
          n'.mem x = ramLoad flash M0 acc imgf (sgCount M0 acc) x) ∧
        ∀ r, romKeep r = true → r ≠ 8 → r ≠ 9 → reg n' r = reg n r) ∨ Panics n
  | 0, j, _, hj, hjN, _, _, _, _, _, _, _, _, _ => absurd hj (by omega)
  | d + 1, j, n, hj, hjN, s, hH, hM, hsp, h9, h8, h19, h23, h21 => by
    have hN16 := sgCount_le M0 acc
    have hc : CodeIn n.mem BT bootFnCode := hiKeep C.code hH (by decide) (by decide)
    have hKv : btK R romStack = 0x30 + 16 + R + romStack := rfl
    have hspl := C.hspl; have hsph := C.hsph; have htop := C.hsp; have hR4 := C.hR
    rw [hKv] at hspl; unfold dramEnd at hsph
    have hSn : (top - BitVec.ofNat 32 (btK R romStack)).toNat = top.toNat - btK R romStack := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, hKv]; omega
    have tb : ∀ i, i < 0x10C → n.mem (acc + BitVec.ofNat 32 i) = M0 (acc + BitVec.ofNat 32 i) := fun i hi => by
      rw [hM _ (C.sAS.sub (c := i) (l := 1) (by omega)).symm]
      exact ramLoad_out _ j fun i' hi' hk => ((C.ram i' (by omega) hk).2.2.1.symm.sub (c := i) (l := 1) (by omega)).symm
    have hF : ∀ c, c < 16 → n.mem (sgPtr acc j + BitVec.ofNat 32 c) = M0 (sgPtr acc j + BitVec.ofNat 32 c) :=
      fun c hc' => by unfold sgPtr; rw [add_ofNat_assoc]; exact tb _ (by omega)
    have hL : ∀ c, c ≤ 12 → memLoad32 n.mem (sgPtr acc j + BitVec.ofNat 32 c) = memLoad32 M0 (sgPtr acc j + BitVec.ofNat 32 c) :=
      fun c hc' => memLoad32_congr fun i hi => by rw [add_ofNat_assoc]; exact hF _ (by omega)
    have hp : (sgPtr acc j).toNat = acc.toNat + 16 * j := by
      unfold sgPtr; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := C.haccl; omega
    have hacc := C.hacc
    -- the rest of the loop once this segment is done
    have tail : ∀ {n' : Machine}, Steps n n' → St n'.mem BT n' 0x82 (reg n') → BtHi M0 n'.mem →
        (∀ x, Sep (top - BitVec.ofNat 32 (btK R romStack)) (btK R romStack) x 1 →
          n'.mem x = ramLoad flash M0 acc imgf (j + 1) x) → (∀ r, romKeep r = true → reg n' r = reg n r) →
        (∃ n'', Steps n n'' ∧ St n''.mem BT n'' 0x88 (reg n'') ∧ BtHi M0 n''.mem ∧
          (∀ x, Sep (top - BitVec.ofNat 32 (btK R romStack)) (btK R romStack) x 1 →
            n''.mem x = ramLoad flash M0 acc imgf (sgCount M0 acc) x) ∧
          ∀ r, romKeep r = true → r ≠ 8 → r ≠ 9 → reg n'' r = reg n r) ∨ Panics n := by
      intro n' c' s' hH' hM' k'
      have hc' : CodeIn n'.mem BT bootFnCode := hiKeep C.code hH' (by decide) (by decide)
      obtain ⟨n2, c2, u2⟩ := s'.block btNextB hc' btNextB_end ⟨trivial, trivial, trivial⟩
      have r2 : ∀ r, reg n2 r = (runBlock btNextB (n'.mem, reg n')).2 r := fun r => by rw [u2.regs]
      have v9 : reg n2 9 = sgPtr acc (j + 1) := by
        rw [r2]; simp +decide only [runBlock, BInstr.run, btNextB, upd, ↓reduceIte]
        rw [k' 9 (by decide), h9]; unfold sgPtr
        show acc + BitVec.ofNat 32 (16 * j) + BitVec.ofNat 32 16 = _
        rw [add_ofNat_assoc, show 16 * j + 16 = 16 * (j + 1) by omega]
      have v8 : reg n2 8 = BitVec.ofNat 32 (16 * (sgCount M0 acc - (j + 1))) := by
        rw [r2]; simp +decide only [runBlock, BInstr.run, btNextB, upd, ↓reduceIte]
        rw [k' 8 (by decide), h8]; apply BitVec.eq_of_toNat_eq
        show (BitVec.ofNat 32 (16 * (sgCount M0 acc - j)) + 0xFFFFFFF0).toNat = _
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFF0 : Word).toNat = 2 ^ 32 - 16 from rfl]
        omega
      have k2 : ∀ r, r ≠ 8 → r ≠ 9 → reg n2 r = reg n' r := fun r h8' h9' => by
        rw [r2, runBlock_reg _ _ _ r s'.zero (by simp only [btNextB]; revert h8' h9'; revert r; decide)]
      have t2 : St n'.mem BT n2 0x86 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
      by_cases hl : j + 1 < sgCount M0 acc
      · obtain ⟨n3, d3, u3⟩ := t2.taken hc' 0x5C bt_at_86 (by decide) (by
          show (reg n2 8 != reg n2 x0) = true
          rw [v8, t2.zero]
          exact bne_iff_ne.mpr fun e => by
            have := congrArg BitVec.toNat e
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
            exact absurd this (by show 16 * (sgCount M0 acc - (j + 1)) ≠ 0; omega))
        have kk : ∀ r, romKeep r = true → r ≠ 8 → r ≠ 9 → reg n3 r = reg n r := fun r hr h8' h9' => by
          rw [u3.regs, k2 r h8' h9', k' r hr]
        rcases bt_copy C hROM d (j + 1) (by omega) hl (⟨u3.pc, by rw [u3.mem], fun _ => rfl⟩ :
            St n3.mem BT n3 0x5C (reg n3)) (by rw [u3.mem]; exact hH')
            (fun x hx => by rw [u3.mem]; exact hM' x hx)
            (by rw [kk sp (by decide) (by decide) (by decide)]; exact hsp) (by rw [u3.regs]; exact v9)
            (by rw [u3.regs]; exact v8) (by rw [kk 19 (by decide) (by decide) (by decide)]; exact h19)
            (by rw [kk 23 (by decide) (by decide) (by decide)]; exact h23)
            (by rw [kk 21 (by decide) (by decide) (by decide)]; exact h21) with ⟨n'', c'', s'', hH'', hM'', k''⟩ | hp'
        · exact Or.inl ⟨n'', c'.trans (c2.trans (.cons d3 c'')), s'', hH'', hM'', fun r hr h8' h9' => by
            rw [k'' r hr h8' h9', kk r hr h8' h9']⟩
        · exact Or.inr (Panics.of_steps (c'.trans (c2.trans (.single d3))) hp')
      · have e : j + 1 = sgCount M0 acc := by omega
        obtain ⟨n3, d3, u3⟩ := t2.notTaken hc' 0x88 bt_at_86 (by decide) (by
          show (reg n2 8 != reg n2 x0) = false
          rw [v8, t2.zero, ← e, Nat.sub_self]; rfl)
        rw [e] at hM'
        exact Or.inl ⟨n3, c'.trans (c2.trans (.single d3)), ⟨u3.pc, rfl, fun _ => rfl⟩,
          by rw [u3.mem]; exact hH', fun x hx => by rw [u3.mem]; exact hM' x hx,
          fun r hr h8' h9' => by rw [u3.regs, k2 r h8' h9', k' r hr]⟩
    -- the kind
    obtain ⟨n1, d1, u1⟩ := s.lbu hc bt_at_5c (off' := 0x60) (by decide)
    have t1 := u1.self
    have v0 : reg n1 a0 = (sgKind M0 acc j).zeroExtend 32 := by
      rw [u1.regs]; simp +decide only [upd, ↓reduceIte]; rw [h9]; exact congrArg (·.zeroExtend 32) (hF 12 (by decide))
    have k1 : ∀ r, r ≠ a0 → reg n1 r = reg n r := fun r h => by rw [u1.regs]; exact updz s.zero h
    have hk3 := C.kind j hjN
    by_cases hram : 2 ≤ (sgKind M0 acc j).toNat
    · obtain ⟨hda, hdl, sDA, sDS, hsa⟩ := C.ram j hjN hram
      obtain ⟨n2, d2, u2⟩ := t1.notTaken hc 0x64 bt_at_60 (by decide) (by
        show (reg n1 a0).ult (reg n1 19) = false
        rw [v0, k1 19 (by decide), h19]
        rcases kind4 _ hk3 with e | e | e | e <;> rw [e] at hram ⊢ <;> first | exact absurd hram (by decide) | rfl)
      have t2 : St n.mem BT n2 0x64 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
      have a9 : ∀ {f : Fin 32 → Word}, (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ ra → f r = reg n r) → f 9 = sgPtr acc j :=
        fun h => by rw [h 9 (by decide) (by decide) (by decide) (by decide)]; exact h9
      -- the destination, at 0x70
      obtain ⟨n5, c5, t5, v1, k5⟩ : ∃ n5, Steps n2 n5 ∧ St n.mem BT n5 0x70 (reg n5) ∧
          reg n5 a1 = sgDest M0 acc j ∧ ∀ r, r ≠ a1 → reg n5 r = reg n2 r := by
        have ld : memLoad32 n.mem (reg n2 9 + 0x0) = sgAddr M0 acc j := by
          rw [u2.regs, k1 9 (by decide), h9]; exact hL 0 (by decide)
        rcases kind4 _ hk3 with e | e | e | e
        · rw [e] at hram; exact absurd hram (by decide)
        · rw [e] at hram; exact absurd hram (by decide)
        · obtain ⟨n3, d3, u3⟩ := t2.notTaken hc 0x68 bt_at_64 (by decide) (by
            show (reg n2 a0 != reg n2 19) = false
            rw [u2.regs, u2.regs, v0, k1 19 (by decide), h19, e]; rfl)
          have t3 : St n.mem BT n3 0x68 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
          obtain ⟨n4, d4, u4⟩ := t3.lw hc bt_at_68 (off' := 0x6A) (by decide)
            (by rw [u3.regs, u2.regs, k1 9 (by decide), h9, add_lit_zero, hp]; omega)
          have t4 := u4.self
          obtain ⟨n5, d5, u5⟩ := t4.alu hc bt_at_6a (off' := 0x6C) (by decide)
          have t5 := u5.self
          obtain ⟨n6, d6, u6⟩ := t5.jump hc bt_at_6c (off' := 0x70) (by decide) (by rw [t5.pc]; decide)
          refine ⟨n6, .cons d3 (.cons d4 (.cons d5 (.single d6))), ⟨u6.pc, u6.mem, fun _ => rfl⟩, ?_, fun r h => ?_⟩
          · have r23 : reg n4 23 = 0xFF900000 := by
              rw [u4.regs, updz t3.zero (by decide), u3.regs, u2.regs, k1 23 (by decide), h23]
            have r1 : reg n4 a1 = sgAddr M0 acc j := by
              rw [u4.regs]; simp +decide only [upd, ↓reduceIte]; rw [u3.regs, ld]
            rw [u6.regs, u5.regs]; simp +decide only [upd, ↓reduceIte]
            rw [r1, r23]; unfold sgDest; rw [ite_eq_left e]; rfl
          · rw [u6.regs, u5.regs, updz t4.zero h, u4.regs, updz t3.zero h, u3.regs]
        · obtain ⟨n3, d3, u3⟩ := t2.taken hc 0x6E bt_at_64 (by decide) (by
            show (reg n2 a0 != reg n2 19) = true
            rw [u2.regs, u2.regs, v0, k1 19 (by decide), h19, e]; rfl)
          have t3 : St n.mem BT n3 0x6E (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
          obtain ⟨n4, d4, u4⟩ := t3.lw hc bt_at_6e (off' := 0x70) (by decide)
            (by rw [u3.regs, u2.regs, k1 9 (by decide), h9, add_lit_zero, hp]; omega)
          refine ⟨n4, .cons d3 (.single d4), ⟨u4.pc, u4.mem, fun _ => rfl⟩, ?_, fun r h => ?_⟩
          · rw [u4.regs]; simp +decide only [upd, ↓reduceIte]
            rw [u3.regs, ld]; unfold sgDest; rw [ite_eq_right (by rw [e]; decide)]
          · rw [u4.regs, updz t3.zero h, u3.regs]
      have k25 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ ra → reg n5 r = reg n r := fun r h0 h1 _ _ => by
        rw [k5 r h1, u2.regs, k1 r h0]
      -- the source and the word count, then the call
      obtain ⟨n6, c6, u6⟩ := t5.block btCopyB hc btCopyB_end (by
        simp only [BlockOk, BInstr.ok, BInstr.run, btCopyB]
        simp +decide only [upd, ↓reduceIte, true_and, and_true]
        rw [a9 k25]
        refine ⟨?_, ?_⟩ <;> rw [BitVec.toNat_add, hp] <;> simp <;> omega)
      have r6 : ∀ r, reg n6 r = (runBlock btCopyB (n.mem, reg n5)).2 r := fun r => by rw [u6.regs]
      have t6 : St n.mem BT n6 0x78 (reg n6) := ⟨u6.pc, u6.mem, fun _ => rfl⟩
      have w0 : reg n6 a0 = sgSrc M0 acc imgf j := by
        rw [r6]; simp +decide only [runBlock, BInstr.run, btCopyB, upd, ↓reduceIte]
        rw [a9 k25, show memLoad32 n.mem (sgPtr acc j + 4) = memLoad32 M0 (sgPtr acc j + 4) from hL 4 (by decide), k25 21 (by decide) (by decide) (by decide) (by decide), h21]; rfl
      have w2 : reg n6 a2 = sgLen M0 acc j >>> 2 := by
        rw [r6]; simp +decide only [runBlock, BInstr.run, btCopyB, upd, ↓reduceIte]
        rw [a9 k25, show memLoad32 n.mem (sgPtr acc j + 8) = memLoad32 M0 (sgPtr acc j + 8) from hL 8 (by decide)]; rfl
      have w1 : reg n6 a1 = sgDest M0 acc j := by
        rw [r6, runBlock_reg _ _ _ a1 t5.zero (by decide)]; exact v1
      have k6 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ ra → reg n6 r = reg n r := fun r h0 h1 h2 hr => by
        rw [r6, runBlock_reg _ _ _ r t5.zero (by simp only [btCopyB]; revert h0 h2; revert r; decide)]
        exact k25 r h0 h1 h2 hr
      obtain ⟨n7, c7, pc7, mem7, regs7⟩ := t6.callRa (cb := BitVec.ofNat 32 romFlashReadWordsAddress) hc
        bt_at_78 bt_at_7c (by decide) (by decide)
      have k7 : ∀ r, r ≠ ra → reg n7 r = reg n6 r := fun r h => by rw [regs7]; exact updz t6.zero h
      obtain ⟨G, hG⟩ : ∃ G, top - BitVec.ofNat 32 (0x30 + 16 + R) = G := ⟨_, rfl⟩
      have hGn : G.toNat = top.toNat - (0x30 + 16 + R) := by
        rw [← hG, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      have hGsp : G + BitVec.ofNat 32 (16 + R) = top + 0xFFFFFFD0 := BitVec.eq_of_toNat_eq (by
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, hGn, show (0xFFFFFFD0 : Word).toNat = 2 ^ 32 - 0x30 from rfl]
        omega)
      have hGS : (top - BitVec.ofNat 32 (btK R romStack)) + BitVec.ofNat 32 romStack = G := BitVec.eq_of_toNat_eq (by
        rw [BitVec.toNat_add, hSn, BitVec.toNat_ofNat, hGn, hKv]; omega)
      have sGx : ∀ x, Sep (top - BitVec.ofNat 32 (btK R romStack)) (btK R romStack) x 1 → Sep G (16 + R) x 1 :=
        fun x hx => by have := hx.sub (c := romStack) (l := 16 + R) (by rw [hKv]; omega); rwa [hGS] at this
      have hdn := hdl; unfold sgBytes at hdn
      obtain ⟨n8, c8, pc8, sp8, keep8, a08, cp8, fr8⟩ := romFlashReadWords_correct hROM n7
        (P := BitVec.ofNat 32 romFlashReadWordsAddress) (G := G) (dst := sgDest M0 acc j)
        (w := sgLen M0 acc j >>> 2) (src := sgSrc M0 acc imgf j) (retAddr := BT + BitVec.ofNat 32 (0x78 + 8))
        ⟨rfl, by rw [mem7]; exact hiKeep C.rfw hH (by decide) (by decide), by rw [hGn]; omega, hR4,
          by rw [hGn]; omega, hda, by omega,
          sep_of_le (by rw [hGn, show (BitVec.ofNat 32 romFlashReadWordsAddress).toNat = 0x403A1730 from rfl]; omega) (by decide),
          sep_of_le (by show _ ≤ (BitVec.ofNat 32 romFlashReadWordsAddress).toNat; rw [show (BitVec.ofNat 32 romFlashReadWordsAddress).toNat = 0x403A1730 from rfl]; omega) (by decide),
          sDS.subR (c := romStack) (l := 16 + R) (by rw [hKv]; omega) |> fun h => by rwa [hGS] at h⟩
        pc7 (by rw [k7 a0 (by decide)]; exact w0) (by rw [k7 a1 (by decide)]; exact w1)
        (by rw [k7 a2 (by decide)]; exact w2) (by rw [regs7]; simp +decide only [upd, ↓reduceIte])
        (even_clear _ (by decide))
        (by rw [k7 sp (by decide), k6 sp (by decide) (by decide) (by decide) (by decide), hsp, hGsp]) hsa
        (by rw [mem7]; exact hiKeep C.rom hH C.hrb C.hrl)
        (sep_of_le (by rw [hGn]; have := C.hrb; omega) (by have := C.hrl; omega))
      have k8 : ∀ r, romKeep r = true → reg n8 r = reg n r := fun r hr => by
        have h0 : r ≠ a0 := by rintro rfl; exact absurd hr (by decide)
        have h1 : r ≠ a1 := by rintro rfl; exact absurd hr (by decide)
        have h2 : r ≠ a2 := by rintro rfl; exact absurd hr (by decide)
        have hra : r ≠ ra := by rintro rfl; exact absurd hr (by decide)
        rw [keep8 r hr, k7 r hra, k6 r h0 h1 h2 hra]
      have hH8 : BtHi M0 n8.mem := fun x h1 h2 => by
        rw [fr8 x (sep_of_le (by rw [hGn]; omega) (by have := x.isLt; omega)) (sep_hi hdn h1), mem7]; exact hH x h1 h2
      have hc8 : CodeIn n8.mem BT bootFnCode := hiKeep C.code hH8 (by decide) (by decide)
      have t8 : St n8.mem BT n8 0x80 (reg n8) := ⟨by rw [pc8], rfl, fun _ => rfl⟩
      rcases a08 with a0z | a0o
      · -- the read failed: halt(0xE2)
        obtain ⟨n9, d9, u9⟩ := t8.taken hc8 0x136 bt_at_80 (by decide) (by
          show (reg n8 a0 == reg n8 x0) = true; rw [a0z, t8.zero]; rfl)
        have t9 : St n8.mem BT n9 0x136 (reg n9) := ⟨u9.pc, u9.mem, fun _ => rfl⟩
        obtain ⟨n10, d10, u10⟩ := t9.aluImm hc8 bt_at_136 (off' := 0x13A) (by decide)
        obtain ⟨n11, c11, pc11, mem11, regs11⟩ := u10.self.callRa (cb := haltBase) hc8 bt_at_13a bt_at_13e
          (by decide) (by decide)
        have sp11 : reg n11 sp = top + 0xFFFFFFD0 := by
          rw [regs11, updz u10.self.zero (by decide), u10.regs, updz t9.zero (by decide), u9.regs,
            k8 sp (by decide), hsp]
        have hspn : (top + 0xFFFFFFD0).toNat = top.toNat - 0x30 := by
          rw [BitVec.toNat_add, show (0xFFFFFFD0 : Word).toNat = 2 ^ 32 - 0x30 from rfl]; omega
        refine Or.inr (Panics.of_steps (.cons d1 (.cons d2 (c5.trans (c6.trans (c7.trans (c8.trans
          (.cons d9 (.cons d10 c11)))))))) (halt_panics n11 (by rw [mem11]; exact panicKeep C.panic hH8) pc11 ?_))
        rw [sp11]; refine ⟨by rw [hspn]; omega, by rw [hspn]; omega, by rw [hspn]; unfold dramEnd; omega⟩
      · obtain ⟨n9, d9, u9⟩ := t8.notTaken hc8 0x82 bt_at_80 (by decide) (by
          show (reg n8 a0 == reg n8 x0) = false; rw [a0o, t8.zero]; rfl)
        refine tail (.cons d1 (.cons d2 (c5.trans (c6.trans (c7.trans (c8.trans (.single d9)))))))
          ⟨u9.pc, rfl, fun _ => rfl⟩ (by rw [u9.mem]; exact hH8) (fun x hx => ?_) (fun r hr => by rw [u9.regs, k8 r hr])
        rw [u9.mem, ramLoad, ite_eq_left hram]
        unfold copyIn
        by_cases hin : (x - sgDest M0 acc j).toNat < sgBytes M0 acc j
        · rw [ite_eq_left hin]
          have hx : x = sgDest M0 acc j + BitVec.ofNat 32 (x - sgDest M0 acc j).toNat := by
            rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
          conv => lhs; rw [hx]
          exact cp8 a0o _ hin
        · rw [ite_eq_right hin, fr8 x (sGx x hx) (fun i hi j' hj' e => hin (by
            rw [show j' = 0 by omega, add_ofNat_zero] at e; rw [← e, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; unfold sgBytes; omega)),
            mem7, hM x hx]
    · obtain ⟨n2, d2, u2⟩ := t1.taken hc 0x82 bt_at_60 (by decide) (by
        show (reg n1 a0).ult (reg n1 19) = true
        rw [v0, k1 19 (by decide), h19]
        rcases kind4 _ hk3 with e | e | e | e <;> rw [e] at hram ⊢ <;> first | exact absurd hram (by decide) | rfl)
      exact tail (.cons d1 (.single d2)) ⟨u2.pc, by rw [u2.mem], fun _ => rfl⟩
        (by rw [u2.mem]; exact hH)
        (fun x hx => by rw [u2.mem, hM x hx, ramLoad, ite_eq_right hram])
        (fun r hr => by rw [u2.regs, k1 r (by rintro rfl; exact absurd hr (by decide))])

end Copy

end C3.RV32.Cur
