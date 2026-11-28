import C3BootProofs.Proofs.BootWrite
import C3BootProofs.Proofs.HaltCode

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

/-- The eFuse peripheral's PMS region registers after `efuse::lock()`:
region 0 spans `0x60008800..0x60009000` (split addresses shifted right by 2:
`0x18002200` at `0x600C1110` and `0x18002400` at the 7 words from `0x600C1114`),
its permission field at `0x600C1108` has low 2 bits `2`, and the PMS lock
register at `0x600C1104` is `1`. -/
def EfuseLocked (M : Word → BitVec 8) : Prop :=
  memLoad32 M 0x600C1110 = 0x18002200 ∧
  (∀ i, i < 7 → memLoad32 M (0x600C1114 + BitVec.ofNat 32 (4 * i)) = 0x18002400) ∧
  memLoad32 M 0x600C1108 &&& 3 = 2 ∧
  memLoad32 M 0x600C1104 = 1

theorem efuse_perm_bits (w : Word) : ((w &&& 0xFFFFFFFC) + 2) &&& 3 = 2 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_and]
  have hm : (0xFFFFFFFC : Word).toNat = 0xFFFFFFFC := rfl
  have h2 : (2 : Word).toNat = 2 := rfl
  have h3 : (3 : Word).toNat = 3 := rfl
  rw [hm, h2, h3]
  have ha : ∀ x : Nat, x &&& 3 = x % 4 := fun x => by
    have h1 : x &&& 3 < 2 ^ 2 := Nat.and_lt_two_pow x (by decide : 3 < 2 ^ 2)
    rw [← Nat.mod_eq_of_lt h1, Nat.and_mod_two_pow]
    have k : ∀ y, y < 4 → y &&& 3 % 4 = y := by decide
    exact k _ (Nat.mod_lt x (by decide))
  have hmod : (w.toNat &&& 0xFFFFFFFC) % 4 = 0 := by
    rw [← ha, Nat.and_assoc, show (0xFFFFFFFC &&& 3 : Nat) = 0 from rfl, Nat.and_zero]
  rw [ha]
  omega

theorem EfuseLocked.congr {M M' : Word → BitVec 8} (h : EfuseLocked M)
    (heq : ∀ x : Word, 0x600C1104 ≤ x.toNat → x.toNat < 0x600C1130 → M' x = M x) :
    EfuseLocked M' := by
  have hload : ∀ a : Word, 0x600C1104 ≤ a.toNat → a.toNat + 4 ≤ 0x600C1130 → memLoad32 M' a = memLoad32 M a :=
    fun a h1 h2 => memLoad32_congr fun j hj => by
      have e : (a + BitVec.ofNat 32 j).toNat = a.toNat + j := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      exact heq _ (by omega) (by omega)
  refine ⟨(hload 0x600C1110 (by decide) (by decide)).trans h.1, fun i hi => ?_, ?_,
    (hload 0x600C1104 (by decide) (by decide)).trans h.2.2.2⟩
  · have e : (0x600C1114 + BitVec.ofNat 32 (4 * i) : Word).toNat = 0x600C1114 + 4 * i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0x600C1114 : Word).toNat = 0x600C1114 from rfl]; omega
    exact (hload _ (by omega) (by omega)).trans (h.2.1 i hi)
  · rw [hload 0x600C1108 (by decide) (by decide)]; exact h.2.2.1

theorem efuseLocked_of_stores {M4 M7 : Word → BitVec 8}
    (h7out : ∀ x : Word, (x.toNat < 0x600C1114 ∨ 0x600C1114 + 4 * 7 ≤ x.toNat) →
      M7 x = memStore32 M4 0x600C1110 0x18002200 x)
    (h7in : ∀ i, i < 7 → memLoad32 M7 (0x600C1114 + BitVec.ofNat 32 (4 * i)) = 0x18002400) :
    EfuseLocked (memStore32 (memStore32 M7 0x600C1108 ((memLoad32 M7 0x600C1108 &&& 0xFFFFFFFC) + 2))
      0x600C1104 1) := by
  refine ⟨?_, fun i hi => ?_, ?_, ?_⟩
  · rw [memLoad32_store32_sep (sep_of_le (by decide) (by decide)),
      memLoad32_store32_sep (sep_of_le (by decide) (by decide))]
    have h10 : memLoad32 M7 0x600C1110 = memLoad32 (memStore32 M4 0x600C1110 0x18002200) 0x600C1110 :=
      memLoad32_congr fun j hj => by
        have e : (0x600C1110 + BitVec.ofNat 32 j : Word).toNat = 0x600C1110 + j := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0x600C1110 : Word).toNat = 0x600C1110 from rfl]; omega
        exact h7out _ (.inl (by omega))
    rw [h10, memLoad32_store32_same]
  · have e : (0x600C1114 + BitVec.ofNat 32 (4 * i) : Word).toNat = 0x600C1114 + 4 * i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0x600C1114 : Word).toNat = 0x600C1114 from rfl]; omega
    rw [memLoad32_store32_sep (sep_of_le (by rw [show (0x600C1104 : Word).toNat = 0x600C1104 from rfl]; omega) (by omega)),
      memLoad32_store32_sep (sep_of_le (by rw [show (0x600C1108 : Word).toNat = 0x600C1108 from rfl]; omega) (by omega))]
    exact h7in i hi
  · rw [memLoad32_store32_sep (sep_of_le (by decide) (by decide)), memLoad32_store32_same]
    exact efuse_perm_bits _
  · exact memLoad32_store32_same _ _ _

set_option maxRecDepth 20000
theorem bt_at_0 : fetchRel bootFnCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem bt_at_2 : fetchRel bootFnCode 0x2 = some (.store .sw sp ra 0x3C, 2) := by decide
theorem bt_at_4 : fetchRel bootFnCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x38, 2) := by decide
theorem bt_at_6 : fetchRel bootFnCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x34, 2) := by decide
theorem bt_at_8 : fetchRel bootFnCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x30, 2) := by decide
theorem bt_at_a : fetchRel bootFnCode 0xA = some (.store .sw sp (19 : Fin 32) 0x2C, 2) := by decide
theorem bt_at_c : fetchRel bootFnCode 0xC = some (.store .sw sp (20 : Fin 32) 0x28, 2) := by decide
theorem bt_at_e : fetchRel bootFnCode 0xE = some (.store .sw sp (21 : Fin 32) 0x24, 2) := by decide
theorem bt_at_10 : fetchRel bootFnCode 0x10 = some (.store .sw sp (22 : Fin 32) 0x20, 2) := by decide
theorem bt_at_12 : fetchRel bootFnCode 0x12 = some (.store .sw sp (23 : Fin 32) 0x1C, 2) := by decide
theorem bt_at_14 : fetchRel bootFnCode 0x14 = some (.store .sw sp (24 : Fin 32) 0x18, 2) := by decide
theorem bt_at_16 : fetchRel bootFnCode 0x16 = some (.store .sw sp (25 : Fin 32) 0x14, 2) := by decide
theorem bt_at_18 : fetchRel bootFnCode 0x18 = some (.store .sw sp (26 : Fin 32) 0x10, 2) := by decide
theorem bt_at_1a : fetchRel bootFnCode 0x1A = some (.store .sw sp (27 : Fin 32) 0xC, 2) := by decide
theorem bt_at_1c : fetchRel bootFnCode 0x1C = some (.alu .add (20 : Fin 32) x0 a2, 2) := by decide
theorem bt_at_1e : fetchRel bootFnCode 0x1E = some (.store .sw sp a1 0x8, 2) := by decide
theorem bt_at_20 : fetchRel bootFnCode 0x20 = some (.store .sw sp a0 0x4, 2) := by decide
theorem bt_at_22 : fetchRel bootFnCode 0x22 = some (.branch .bgeu a4 a3 0x134, 4) := by decide
theorem bt_at_26 : fetchRel bootFnCode 0x26 = some (.alu .add (22 : Fin 32) x0 a3, 2) := by decide
theorem bt_at_28 : fetchRel bootFnCode 0x28 = some (.lui (9 : Fin 32) 0x60009000, 4) := by decide
theorem bt_at_2c : fetchRel bootFnCode 0x2C = some (.lui a0 0x3FCC6000, 4) := by decide
theorem bt_at_30 : fetchRel bootFnCode 0x30 = some (.aluImm .add a0 a0 0x6DF, 4) := by decide
theorem bt_at_34 : fetchRel bootFnCode 0x34 = some (.alu .add a1 x0 a3, 2) := by decide
theorem bt_at_36 : fetchRel bootFnCode 0x36 = some (.auipc ra 0xFFC49000, 4) := by decide
theorem bt_at_3a : fetchRel bootFnCode 0x3A = some (.jalr ra ra 0x66C, 4) := by decide
theorem bt_at_3e : fetchRel bootFnCode 0x3E = some (.aluImm .add (8 : Fin 32) x0 0x0, 2) := by decide
theorem bt_at_40 : fetchRel bootFnCode 0x40 = some (.lui a0 0x5000, 2) := by decide
theorem bt_at_42 : fetchRel bootFnCode 0x42 = some (.lui a1 0x3000, 2) := by decide
theorem bt_at_44 : fetchRel bootFnCode 0x44 = some (.aluImm .add (24 : Fin 32) a0 0x555, 4) := by decide
theorem bt_at_48 : fetchRel bootFnCode 0x48 = some (.aluImm .add (25 : Fin 32) a1 0x333, 4) := by decide
theorem bt_at_4c : fetchRel bootFnCode 0x4C = some (.lui (27 : Fin 32) 0x20000, 4) := by decide
theorem bt_at_50 : fetchRel bootFnCode 0x50 = some (.aluImm .add (27 : Fin 32) (27 : Fin 32) 0xFFFFFE00, 4) := by decide
theorem bt_at_54 : fetchRel bootFnCode 0x54 = some (.lui (18 : Fin 32) 0xFF000000, 4) := by decide
theorem bt_at_58 : fetchRel bootFnCode 0x58 = some (.aluImm .add (18 : Fin 32) (18 : Fin 32) 0xFF, 4) := by decide
theorem bt_at_5c : fetchRel bootFnCode 0x5C = some (.aluImm .add (19 : Fin 32) (9 : Fin 32) 0xFFFFF800, 4) := by decide
theorem bt_at_60 : fetchRel bootFnCode 0x60 = some (.lui a0 0x6000, 2) := by decide
theorem bt_at_62 : fetchRel bootFnCode 0x62 = some (.aluImm .add (23 : Fin 32) a0 0xFFFFFA5A, 4) := by decide
theorem bt_at_66 : fetchRel bootFnCode 0x66 = some (.aluImm .add (21 : Fin 32) a0 0xFFFFFAA5, 4) := by decide
theorem bt_at_6a : fetchRel bootFnCode 0x6A = some (.load .lw a0 (9 : Fin 32) 0xFFFFF83C, 4) := by decide
theorem bt_at_6e : fetchRel bootFnCode 0x6E = some (.aluImm .srl a1 a0 0xF, 4) := by decide
theorem bt_at_72 : fetchRel bootFnCode 0x72 = some (.aluImm .srl a0 a0 0xE, 2) := by decide
theorem bt_at_74 : fetchRel bootFnCode 0x74 = some (.alu .and a1 a1 (24 : Fin 32), 4) := by decide
theorem bt_at_78 : fetchRel bootFnCode 0x78 = some (.alu .sub a1 a0 a1, 4) := by decide
theorem bt_at_7c : fetchRel bootFnCode 0x7C = some (.aluImm .srl a2 a1 0x2, 4) := by decide
theorem bt_at_80 : fetchRel bootFnCode 0x80 = some (.alu .and a1 a1 (25 : Fin 32), 4) := by decide
theorem bt_at_84 : fetchRel bootFnCode 0x84 = some (.alu .and a2 a2 (25 : Fin 32), 4) := by decide
theorem bt_at_88 : fetchRel bootFnCode 0x88 = some (.alu .add a1 a1 a2, 2) := by decide
theorem bt_at_8a : fetchRel bootFnCode 0x8A = some (.aluImm .srl a2 a1 0x4, 4) := by decide
theorem bt_at_8e : fetchRel bootFnCode 0x8E = some (.alu .add a1 a1 a2, 2) := by decide
theorem bt_at_90 : fetchRel bootFnCode 0x90 = some (.aluImm .sll a2 a1 0x14, 4) := by decide
theorem bt_at_94 : fetchRel bootFnCode 0x94 = some (.aluImm .and a1 a1 0xF, 2) := by decide
theorem bt_at_96 : fetchRel bootFnCode 0x96 = some (.aluImm .srl a2 a2 0x1C, 2) := by decide
theorem bt_at_98 : fetchRel bootFnCode 0x98 = some (.alu .add a1 a1 a2, 2) := by decide
theorem bt_at_9a : fetchRel bootFnCode 0x9A = some (.branch .bgeu a1 (22 : Fin 32) 0xBC, 4) := by decide
theorem bt_at_9e : fetchRel bootFnCode 0x9E = some (.aluImm .and a1 (8 : Fin 32) 0xFF, 4) := by decide
theorem bt_at_a2 : fetchRel bootFnCode 0xA2 = some (.aluImm .add a2 x0 0x2, 2) := by decide
theorem bt_at_a4 : fetchRel bootFnCode 0xA4 = some (.branch .bltu a2 a1 0x1F8, 4) := by decide
theorem bt_at_a8 : fetchRel bootFnCode 0xA8 = some (.aluImm .xor a1 a0 0xFFFFFFFF, 4) := by decide
theorem bt_at_ac : fetchRel bootFnCode 0xAC = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem bt_at_ae : fetchRel bootFnCode 0xAE = some (.alu .and (26 : Fin 32) a0 a1, 4) := by decide
theorem bt_at_b2 : fetchRel bootFnCode 0xB2 = some (.aluImm .sll a0 (26 : Fin 32) 0x10, 4) := by decide
theorem bt_at_b6 : fetchRel bootFnCode 0xB6 = some (.branch .beq a0 x0 0x1E6, 4) := by decide
theorem bt_at_ba : fetchRel bootFnCode 0xBA = some (.aluImm .add a3 (9 : Fin 32) 0xFFFFF980, 4) := by decide
theorem bt_at_be : fetchRel bootFnCode 0xBE = some (.load .lw a1 a3 0x68, 2) := by decide
theorem bt_at_c0 : fetchRel bootFnCode 0xC0 = some (.aluImm .and a1 a1 0xFFFFFF00, 4) := by decide
theorem bt_at_c4 : fetchRel bootFnCode 0xC4 = some (.aluImm .add a1 a1 0x28, 4) := by decide
theorem bt_at_c8 : fetchRel bootFnCode 0xC8 = some (.store .sw a3 a1 0x68, 2) := by decide
theorem bt_at_ca : fetchRel bootFnCode 0xCA = some (.load .lw a1 a3 0x68, 2) := by decide
theorem bt_at_cc : fetchRel bootFnCode 0xCC = some (.alu .or a1 a1 (27 : Fin 32), 4) := by decide
theorem bt_at_d0 : fetchRel bootFnCode 0xD0 = some (.store .sw a3 a1 0x68, 2) := by decide
theorem bt_at_d2 : fetchRel bootFnCode 0xD2 = some (.load .lw a1 a3 0x70, 2) := by decide
theorem bt_at_d4 : fetchRel bootFnCode 0xD4 = some (.alu .and a1 a1 (18 : Fin 32), 4) := by decide
theorem bt_at_d8 : fetchRel bootFnCode 0xD8 = some (.lui a2 0x300000, 4) := by decide
theorem bt_at_dc : fetchRel bootFnCode 0xDC = some (.alu .or a1 a1 a2, 2) := by decide
theorem bt_at_de : fetchRel bootFnCode 0xDE = some (.store .sw a3 a1 0x70, 2) := by decide
theorem bt_at_e0 : fetchRel bootFnCode 0xE0 = some (.load .lw a1 a3 0x74, 2) := by decide
theorem bt_at_e2 : fetchRel bootFnCode 0xE2 = some (.lui a2 0xFFFF0000, 2) := by decide
theorem bt_at_e4 : fetchRel bootFnCode 0xE4 = some (.alu .and a1 a1 a2, 2) := by decide
theorem bt_at_e6 : fetchRel bootFnCode 0xE6 = some (.aluImm .add a1 a1 0x190, 4) := by decide
theorem bt_at_ea : fetchRel bootFnCode 0xEA = some (.store .sw a3 a1 0x74, 2) := by decide
theorem bt_at_ec : fetchRel bootFnCode 0xEC = some (.aluImm .add a1 x0 0x8, 2) := by decide
theorem bt_at_ee : fetchRel bootFnCode 0xEE = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem bt_at_f0 : fetchRel bootFnCode 0xF0 = some (.branch .beq a1 x0 0xC, 2) := by decide
theorem bt_at_f2 : fetchRel bootFnCode 0xF2 = some (.store .sw a2 x0 0x0, 4) := by decide
theorem bt_at_f6 : fetchRel bootFnCode 0xF6 = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem bt_at_f8 : fetchRel bootFnCode 0xF8 = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem bt_at_fa : fetchRel bootFnCode 0xFA = some (.branch .bne a1 x0 0xFFFFFFF8, 2) := by decide
theorem bt_at_fc : fetchRel bootFnCode 0xFC = some (.aluImm .add a1 x0 0x3, 2) := by decide
theorem bt_at_fe : fetchRel bootFnCode 0xFE = some (.aluImm .add a2 (9 : Fin 32) 0xFFFFF820, 4) := by decide
theorem bt_at_102 : fetchRel bootFnCode 0x102 = some (.branch .beq a1 x0 0xC, 2) := by decide
theorem bt_at_104 : fetchRel bootFnCode 0x104 = some (.store .sw a2 x0 0x0, 4) := by decide
theorem bt_at_108 : fetchRel bootFnCode 0x108 = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem bt_at_10a : fetchRel bootFnCode 0x10A = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem bt_at_10c : fetchRel bootFnCode 0x10C = some (.branch .bne a1 x0 0xFFFFFFF8, 2) := by decide
theorem bt_at_10e : fetchRel bootFnCode 0x10E = some (.aluImm .srl a0 a0 0x2, 2) := by decide
theorem bt_at_110 : fetchRel bootFnCode 0x110 = some (.store .sw (9 : Fin 32) a0 0xFFFFF810, 4) := by decide
theorem bt_at_114 : fetchRel bootFnCode 0x114 = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem bt_at_116 : fetchRel bootFnCode 0x116 = some (.alu .add a0 x0 (23 : Fin 32), 2) := by decide
theorem bt_at_118 : fetchRel bootFnCode 0x118 = some (.auipc ra 0x0, 4) := by decide
theorem bt_at_11c : fetchRel bootFnCode 0x11C = some (.jalr ra ra 0x2E2, 4) := by decide
theorem bt_at_120 : fetchRel bootFnCode 0x120 = some (.aluImm .add a1 x0 0x8, 2) := by decide
theorem bt_at_122 : fetchRel bootFnCode 0x122 = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem bt_at_124 : fetchRel bootFnCode 0x124 = some (.branch .beq a1 x0 0xC, 2) := by decide
theorem bt_at_126 : fetchRel bootFnCode 0x126 = some (.store .sw a2 x0 0x0, 4) := by decide
theorem bt_at_12a : fetchRel bootFnCode 0x12A = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem bt_at_12c : fetchRel bootFnCode 0x12C = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem bt_at_12e : fetchRel bootFnCode 0x12E = some (.branch .bne a1 x0 0xFFFFFFF8, 2) := by decide
theorem bt_at_130 : fetchRel bootFnCode 0x130 = some (.branch .beq a0 x0 0xE, 2) := by decide
theorem bt_at_132 : fetchRel bootFnCode 0x132 = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem bt_at_134 : fetchRel bootFnCode 0x134 = some (.alu .add a0 x0 (21 : Fin 32), 2) := by decide
theorem bt_at_136 : fetchRel bootFnCode 0x136 = some (.auipc ra 0x0, 4) := by decide
theorem bt_at_13a : fetchRel bootFnCode 0x13A = some (.jalr ra ra 0x2C4, 4) := by decide
theorem bt_at_13e : fetchRel bootFnCode 0x13E = some (.load .lw a0 (9 : Fin 32) 0xFFFFF83C, 4) := by decide
theorem bt_at_142 : fetchRel bootFnCode 0x142 = some (.aluImm .srl a0 a0 0xE, 2) := by decide
theorem bt_at_144 : fetchRel bootFnCode 0x144 = some (.alu .and a0 (26 : Fin 32) a0, 4) := by decide
theorem bt_at_148 : fetchRel bootFnCode 0x148 = some (.aluImm .sll a0 a0 0x10, 2) := by decide
theorem bt_at_14a : fetchRel bootFnCode 0x14A = some (.alu .sltu a0 x0 a0, 4) := by decide
theorem bt_at_14e : fetchRel bootFnCode 0x14E = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x1, 2) := by decide
theorem bt_at_150 : fetchRel bootFnCode 0x150 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem bt_at_152 : fetchRel bootFnCode 0x152 = some (.alu .and (8 : Fin 32) (8 : Fin 32) a0, 2) := by decide
theorem bt_at_154 : fetchRel bootFnCode 0x154 = some (.jal x0 0xFFFFFF16, 2) := by decide
theorem bt_at_156 : fetchRel bootFnCode 0x156 = some (.lui a1 0x18002000, 4) := by decide
theorem bt_at_15a : fetchRel bootFnCode 0x15A = some (.lui a0 0x600C1000, 4) := by decide
theorem bt_at_15e : fetchRel bootFnCode 0x15E = some (.aluImm .add a3 a1 0x200, 4) := by decide
theorem bt_at_162 : fetchRel bootFnCode 0x162 = some (.aluImm .add a1 x0 0x7, 2) := by decide
theorem bt_at_164 : fetchRel bootFnCode 0x164 = some (.store .sw a0 a3 0x110, 4) := by decide
theorem bt_at_168 : fetchRel bootFnCode 0x168 = some (.aluImm .add a2 a0 0x114, 4) := by decide
theorem bt_at_16c : fetchRel bootFnCode 0x16C = some (.aluImm .add a3 a3 0x200, 4) := by decide
theorem bt_at_170 : fetchRel bootFnCode 0x170 = some (.load .lw (23 : Fin 32) sp 0x8, 2) := by decide
theorem bt_at_172 : fetchRel bootFnCode 0x172 = some (.branch .beq a1 x0 0xA, 2) := by decide
theorem bt_at_174 : fetchRel bootFnCode 0x174 = some (.store .sw a2 a3 0x0, 2) := by decide
theorem bt_at_176 : fetchRel bootFnCode 0x176 = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem bt_at_178 : fetchRel bootFnCode 0x178 = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem bt_at_17a : fetchRel bootFnCode 0x17A = some (.branch .bne a1 x0 0xFFFFFFFA, 2) := by decide
theorem bt_at_17c : fetchRel bootFnCode 0x17C = some (.aluImm .add a3 a0 0x100, 4) := by decide
theorem bt_at_180 : fetchRel bootFnCode 0x180 = some (.load .lw a1 a3 0x8, 2) := by decide
theorem bt_at_182 : fetchRel bootFnCode 0x182 = some (.aluImm .and a1 a1 0xFFFFFFFC, 2) := by decide
theorem bt_at_184 : fetchRel bootFnCode 0x184 = some (.aluImm .add a1 a1 0x2, 2) := by decide
theorem bt_at_186 : fetchRel bootFnCode 0x186 = some (.aluImm .add a2 x0 0x1, 2) := by decide
theorem bt_at_188 : fetchRel bootFnCode 0x188 = some (.store .sw a3 a1 0x8, 2) := by decide
theorem bt_at_18a : fetchRel bootFnCode 0x18A = some (.store .sw a3 a2 0x4, 2) := by decide
theorem bt_at_18c : fetchRel bootFnCode 0x18C = some (.load .lw a0 (23 : Fin 32) 0x108, 4) := by decide
theorem bt_at_190 : fetchRel bootFnCode 0x190 = some (.aluImm .add a2 x0 0x10, 2) := by decide
theorem bt_at_192 : fetchRel bootFnCode 0x192 = some (.aluImm .sltu a1 a0 0x11, 4) := by decide
theorem bt_at_196 : fetchRel bootFnCode 0x196 = some (.alu .add (22 : Fin 32) x0 (23 : Fin 32), 2) := by decide
theorem bt_at_198 : fetchRel bootFnCode 0x198 = some (.branch .bgeu a2 a0 0x6, 4) := by decide
theorem bt_at_19c : fetchRel bootFnCode 0x19C = some (.aluImm .add (22 : Fin 32) x0 0x4, 2) := by decide
theorem bt_at_19e : fetchRel bootFnCode 0x19E = some (.alu .sub a1 x0 a1, 4) := by decide
theorem bt_at_1a2 : fetchRel bootFnCode 0x1A2 = some (.alu .and a0 a0 a1, 2) := by decide
theorem bt_at_1a4 : fetchRel bootFnCode 0x1A4 = some (.aluImm .sll (8 : Fin 32) a0 0x4, 4) := by decide
theorem bt_at_1a8 : fetchRel bootFnCode 0x1A8 = some (.aluImm .add (19 : Fin 32) x0 0x2, 2) := by decide
theorem bt_at_1aa : fetchRel bootFnCode 0x1AA = some (.alu .add (18 : Fin 32) (22 : Fin 32) (8 : Fin 32), 4) := by decide
theorem bt_at_1ae : fetchRel bootFnCode 0x1AE = some (.lui (21 : Fin 32) 0xFF900000, 4) := by decide
theorem bt_at_1b2 : fetchRel bootFnCode 0x1B2 = some (.alu .add (9 : Fin 32) x0 (22 : Fin 32), 2) := by decide
theorem bt_at_1b4 : fetchRel bootFnCode 0x1B4 = some (.branch .beq (8 : Fin 32) x0 0x2E, 2) := by decide
theorem bt_at_1b6 : fetchRel bootFnCode 0x1B6 = some (.load .lbu a0 (9 : Fin 32) 0xC, 4) := by decide
theorem bt_at_1ba : fetchRel bootFnCode 0x1BA = some (.branch .bltu a0 (19 : Fin 32) 0x22, 4) := by decide
theorem bt_at_1be : fetchRel bootFnCode 0x1BE = some (.branch .bne a0 (19 : Fin 32) 0xA, 4) := by decide
theorem bt_at_1c2 : fetchRel bootFnCode 0x1C2 = some (.load .lw a1 (9 : Fin 32) 0x0, 2) := by decide
theorem bt_at_1c4 : fetchRel bootFnCode 0x1C4 = some (.alu .add a1 a1 (21 : Fin 32), 2) := by decide
theorem bt_at_1c6 : fetchRel bootFnCode 0x1C6 = some (.jal x0 0x4, 2) := by decide
theorem bt_at_1c8 : fetchRel bootFnCode 0x1C8 = some (.load .lw a1 (9 : Fin 32) 0x0, 2) := by decide
theorem bt_at_1ca : fetchRel bootFnCode 0x1CA = some (.load .lw a0 (9 : Fin 32) 0x4, 2) := by decide
theorem bt_at_1cc : fetchRel bootFnCode 0x1CC = some (.load .lw a2 (9 : Fin 32) 0x8, 2) := by decide
theorem bt_at_1ce : fetchRel bootFnCode 0x1CE = some (.alu .add a0 a0 (20 : Fin 32), 2) := by decide
theorem bt_at_1d0 : fetchRel bootFnCode 0x1D0 = some (.aluImm .srl a2 a2 0x2, 2) := by decide
theorem bt_at_1d2 : fetchRel bootFnCode 0x1D2 = some (.auipc ra 0x0, 4) := by decide
theorem bt_at_1d6 : fetchRel bootFnCode 0x1D6 = some (.jalr ra ra 0xF2, 4) := by decide
theorem bt_at_1da : fetchRel bootFnCode 0x1DA = some (.branch .beq a0 x0 0xB6, 2) := by decide
theorem bt_at_1dc : fetchRel bootFnCode 0x1DC = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x10, 2) := by decide
theorem bt_at_1de : fetchRel bootFnCode 0x1DE = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFF0, 2) := by decide
theorem bt_at_1e0 : fetchRel bootFnCode 0x1E0 = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFD6, 2) := by decide
theorem bt_at_1e2 : fetchRel bootFnCode 0x1E2 = some (.lui (8 : Fin 32) 0x600C5000, 4) := by decide
theorem bt_at_1e6 : fetchRel bootFnCode 0x1E6 = some (.aluImm .add (9 : Fin 32) x0 0x80, 4) := by decide
theorem bt_at_1ea : fetchRel bootFnCode 0x1EA = some (.auipc ra 0xFFC4A000, 4) := by decide
theorem bt_at_1ee : fetchRel bootFnCode 0x1EE = some (.jalr ra ra 0xFFFFF99C, 4) := by decide
theorem bt_at_1f2 : fetchRel bootFnCode 0x1F2 = some (.alu .add (21 : Fin 32) x0 a0, 2) := by decide
theorem bt_at_1f4 : fetchRel bootFnCode 0x1F4 = some (.aluImm .add a0 x0 0x100, 4) := by decide
theorem bt_at_1f8 : fetchRel bootFnCode 0x1F8 = some (.branch .beq (9 : Fin 32) x0 0xA, 2) := by decide
theorem bt_at_1fa : fetchRel bootFnCode 0x1FA = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem bt_at_1fc : fetchRel bootFnCode 0x1FC = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem bt_at_1fe : fetchRel bootFnCode 0x1FE = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem bt_at_200 : fetchRel bootFnCode 0x200 = some (.branch .bne (9 : Fin 32) x0 0xFFFFFFFA, 2) := by decide
theorem bt_at_202 : fetchRel bootFnCode 0x202 = some (.aluImm .add a0 x0 0x2, 2) := by decide
theorem bt_at_204 : fetchRel bootFnCode 0x204 = some (.lui (9 : Fin 32) 0x600C5000, 4) := by decide
theorem bt_at_208 : fetchRel bootFnCode 0x208 = some (.aluImm .add a2 x0 0x7F, 4) := by decide
theorem bt_at_20c : fetchRel bootFnCode 0x20C = some (.branch .beq (22 : Fin 32) (18 : Fin 32) 0x4E, 4) := by decide
theorem bt_at_210 : fetchRel bootFnCode 0x210 = some (.alu .add a3 x0 (22 : Fin 32), 2) := by decide
theorem bt_at_212 : fetchRel bootFnCode 0x212 = some (.load .lbu a4 (22 : Fin 32) 0xC, 4) := by decide
theorem bt_at_216 : fetchRel bootFnCode 0x216 = some (.aluImm .add a5 a4 0xFFFFFFFE, 4) := by decide
theorem bt_at_21a : fetchRel bootFnCode 0x21A = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0x10, 2) := by decide
theorem bt_at_21c : fetchRel bootFnCode 0x21C = some (.lui a1 0xBE000000, 4) := by decide
theorem bt_at_220 : fetchRel bootFnCode 0x220 = some (.branch .bltu a5 a0 0xFFFFFFEC, 4) := by decide
theorem bt_at_224 : fetchRel bootFnCode 0x224 = some (.branch .beq a4 x0 0x6, 2) := by decide
theorem bt_at_226 : fetchRel bootFnCode 0x226 = some (.lui a1 0xC4000000, 4) := by decide
theorem bt_at_22a : fetchRel bootFnCode 0x22A = some (.load .lw a4 a3 0x0, 2) := by decide
theorem bt_at_22c : fetchRel bootFnCode 0x22C = some (.load .lw a5 a3 0x4, 2) := by decide
theorem bt_at_22e : fetchRel bootFnCode 0x22E = some (.load .lhu a3 a3 0xA, 4) := by decide
theorem bt_at_232 : fetchRel bootFnCode 0x232 = some (.alu .add a1 a1 a4, 2) := by decide
theorem bt_at_234 : fetchRel bootFnCode 0x234 = some (.aluImm .srl a4 a1 0x10, 4) := by decide
theorem bt_at_238 : fetchRel bootFnCode 0x238 = some (.alu .add a5 a5 (20 : Fin 32), 2) := by decide
theorem bt_at_23a : fetchRel bootFnCode 0x23A = some (.aluImm .sll a1 a4 0x2, 4) := by decide
theorem bt_at_23e : fetchRel bootFnCode 0x23E = some (.aluImm .srl a5 a5 0x10, 2) := by decide
theorem bt_at_240 : fetchRel bootFnCode 0x240 = some (.alu .add a1 a1 (9 : Fin 32), 2) := by decide
theorem bt_at_242 : fetchRel bootFnCode 0x242 = some (.branch .beq a3 x0 0xFFFFFFCA, 2) := by decide
theorem bt_at_244 : fetchRel bootFnCode 0x244 = some (.branch .bltu a2 a4 0xA, 4) := by decide
theorem bt_at_248 : fetchRel bootFnCode 0x248 = some (.aluImm .and (8 : Fin 32) a5 0xFF, 4) := by decide
theorem bt_at_24c : fetchRel bootFnCode 0x24C = some (.store .sw a1 (8 : Fin 32) 0x0, 2) := by decide
theorem bt_at_24e : fetchRel bootFnCode 0x24E = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem bt_at_250 : fetchRel bootFnCode 0x250 = some (.aluImm .add a4 a4 0x1, 2) := by decide
theorem bt_at_252 : fetchRel bootFnCode 0x252 = some (.aluImm .add a5 a5 0x1, 2) := by decide
theorem bt_at_254 : fetchRel bootFnCode 0x254 = some (.aluImm .add a3 a3 0xFFFFFFFF, 2) := by decide
theorem bt_at_256 : fetchRel bootFnCode 0x256 = some (.branch .beq a3 x0 0xFFFFFFB6, 2) := by decide
theorem bt_at_258 : fetchRel bootFnCode 0x258 = some (.jal x0 0xFFFFFFEC, 2) := by decide
theorem bt_at_25a : fetchRel bootFnCode 0x25A = some (.lui a0 0x600C4000, 4) := by decide
theorem bt_at_25e : fetchRel bootFnCode 0x25E = some (.load .lw a1 a0 0x4, 2) := by decide
theorem bt_at_260 : fetchRel bootFnCode 0x260 = some (.aluImm .and a1 a1 0xFFFFFFFC, 2) := by decide
theorem bt_at_262 : fetchRel bootFnCode 0x262 = some (.store .sw a0 a1 0x4, 2) := by decide
theorem bt_at_264 : fetchRel bootFnCode 0x264 = some (.auipc ra 0xFFC4A000, 4) := by decide
theorem bt_at_268 : fetchRel bootFnCode 0x268 = some (.jalr ra ra 0xFFFFF8D6, 4) := by decide
theorem bt_at_26c : fetchRel bootFnCode 0x26C = some (.alu .add a0 x0 (21 : Fin 32), 2) := by decide
theorem bt_at_26e : fetchRel bootFnCode 0x26E = some (.auipc ra 0xFFC4A000, 4) := by decide
theorem bt_at_272 : fetchRel bootFnCode 0x272 = some (.jalr ra ra 0xFFFFF91C, 4) := by decide
theorem bt_at_276 : fetchRel bootFnCode 0x276 = some (.load .lw (8 : Fin 32) (23 : Fin 32) 0x100, 4) := by decide
theorem bt_at_27a : fetchRel bootFnCode 0x27A = some (.lui a0 0x3FCC6000, 4) := by decide
theorem bt_at_27e : fetchRel bootFnCode 0x27E = some (.aluImm .add a0 a0 0x696, 4) := by decide
theorem bt_at_282 : fetchRel bootFnCode 0x282 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem bt_at_284 : fetchRel bootFnCode 0x284 = some (.auipc ra 0xFFC49000, 4) := by decide
theorem bt_at_288 : fetchRel bootFnCode 0x288 = some (.jalr ra ra 0x41E, 4) := by decide
theorem bt_at_28c : fetchRel bootFnCode 0x28C = some (.load .lw a0 sp 0x4, 2) := by decide
theorem bt_at_28e : fetchRel bootFnCode 0x28E = some (.jalr ra (8 : Fin 32) 0x0, 2) := by decide
theorem bt_at_290 : fetchRel bootFnCode 0x290 = some (.aluImm .add a0 x0 0xE2, 4) := by decide
theorem bt_at_294 : fetchRel bootFnCode 0x294 = some (.auipc ra 0x0, 4) := by decide
theorem bt_at_298 : fetchRel bootFnCode 0x298 = some (.jalr ra ra 0x14, 4) := by decide
theorem bt_at_29c : fetchRel bootFnCode 0x29C = some (.aluImm .add a0 x0 0xE1, 4) := by decide
theorem bt_at_2a0 : fetchRel bootFnCode 0x2A0 = some (.auipc ra 0x0, 4) := by decide
theorem bt_at_2a4 : fetchRel bootFnCode 0x2A4 = some (.jalr ra ra 0x8, 4) := by decide

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

theorem btInvBlk_end : blockEnd bootFnCode 0x1FA btInvBlk = some 0x200 :=
  (blockEnd_cons' (off' := 0x1FC) bt_at_1fa rfl (blockEnd_cons' (off' := 0x1FE) bt_at_1fc rfl (blockEnd_cons' (off' := 0x200) bt_at_1fe rfl rfl)))

set_option maxHeartbeats 4000000 in
/-- The loop that sets all 128 MMU entries to invalid, from the head of
pass `k` at 0x1FA to its exit at 0x202. -/
theorem bt_inv {M : Word → BitVec 8} (hc : CodeIn M BT bootFnCode) :
    ∀ d k {n : Machine}, k + d = 128 → k < 128 → St (mmuInv M k) BT n 0x1FA (reg n) →
      reg n 8 = mmuBase + BitVec.ofNat 32 (4 * k) → reg n 9 = BitVec.ofNat 32 (128 - k) → reg n a0 = 0x100 →
      ∃ n', Steps n n' ∧ St (mmuInv M 128) BT n' 0x202 (reg n') ∧ ∀ r, r ≠ 8 → r ≠ 9 → reg n' r = reg n r
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
    have s1 : St (mmuInv M (k + 1)) BT n1 0x200 (reg n1) := ⟨u1.pc, by rw [u1.mem, m1], fun _ => rfl⟩
    by_cases hl : k + 1 < 128
    · obtain ⟨n2, d2, u2⟩ := s1.taken (hck _ (by omega)) 0x1FA bt_at_200 (by decide) (by
        show (reg n1 9 != reg n1 x0) = true
        rw [v9, s1.zero]
        exact bne_iff_ne.mpr fun e => by
          have := congrArg BitVec.toNat e
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          exact absurd this (by show 128 - (k + 1) ≠ 0; omega))
      obtain ⟨n', c', s', k'⟩ := bt_inv hc d (k + 1) (by omega) hl
        (⟨u2.pc, u2.mem, fun _ => rfl⟩ : St (mmuInv M (k + 1)) BT n2 0x1FA (reg n2))
        (by rw [u2.regs]; exact v8) (by rw [u2.regs]; exact v9) (by rw [u2.regs, k1 a0 (by decide) (by decide)]; exact ha0)
      exact ⟨n', c1.trans (.cons d2 c'), s', fun r h8' h9' => by rw [k' r h8' h9', u2.regs, k1 r h8' h9']⟩
    · have e : k + 1 = 128 := by omega
      obtain ⟨n2, d2, u2⟩ := s1.notTaken (hck _ (by omega)) 0x202 bt_at_200 (by decide) (by
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

theorem btSegBlk_end : blockEnd bootFnCode 0x248 btSegBlk = some 0x256 :=
  (blockEnd_cons' (off' := 0x24C) bt_at_248 rfl (blockEnd_cons' (off' := 0x24E) bt_at_24c rfl (blockEnd_cons' (off' := 0x250) bt_at_24e rfl (blockEnd_cons' (off' := 0x252) bt_at_250 rfl (blockEnd_cons' (off' := 0x254) bt_at_252 rfl (blockEnd_cons' (off' := 0x256) bt_at_254 rfl rfl))))))

def btSkipBlk : List BInstr :=
  [.aluImm .add a1 a1 0x4, .aluImm .add a4 a4 0x1, .aluImm .add a5 a5 0x1, .aluImm .add a3 a3 0xFFFFFFFF]

theorem btSkipBlk_end : blockEnd bootFnCode 0x24E btSkipBlk = some 0x256 :=
  (blockEnd_cons' (off' := 0x250) bt_at_24e rfl (blockEnd_cons' (off' := 0x252) bt_at_250 rfl (blockEnd_cons' (off' := 0x254) bt_at_252 rfl (blockEnd_cons' (off' := 0x256) bt_at_254 rfl rfl))))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- The loop that writes one flash segment's `k` MMU entries, from 0x244 to
the outer loop's head at 0x20C. -/
theorem bt_seg (hbt : BT.toNat + bootFnCode.length ≤ 0x600C4000) :
    ∀ k {M : Word → BitVec 8} {e v : Word} {n : Machine}, 0 < k → k < 2 ^ 32 → CodeIn M BT bootFnCode →
      St M BT n 0x244 (reg n) → reg n a4 = e → reg n a5 = v → reg n a3 = BitVec.ofNat 32 k →
      reg n a1 = (e <<< 2) + mmuBase → reg n a2 = 127 →
      ∃ n', Steps n n' ∧ St (mapSeg M e v k) BT n' 0x20C (reg n') ∧
        ∀ r, r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 8 → reg n' r = reg n r
  | 0, _, _, _, _, hk, _, _, _, _, _, _, _, _ => absurd hk (by omega)
  | k + 1, M, e, v, n, _, hk, hc, s, h4, h5, h3, h1, h2 => by
    -- one pass: the store when `e` is in the table, then the increments
    obtain ⟨n1, c1, s1, M1, hM1, r1, k1⟩ : ∃ n1, Steps n n1 ∧ ∃ (_ : St (if e.toNat ≤ 127 then
        memStore32 M ((e <<< 2) + mmuBase) (v &&& 0xFF) else M) BT n1 0x256 (reg n1)), True ∧ True ∧
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
      · obtain ⟨n0, d0, u0⟩ := s.notTaken hc 0x248 bt_at_244 (by decide) (by
          show (reg n a2).ult (reg n a4) = false
          rw [h2, h4]; simp only [BitVec.ult, BitVec.toNat_ofNat]; exact decide_eq_false (by
            show ¬ 127 < e.toNat; omega))
        have t0 : St M BT n0 0x248 (reg n0) := ⟨u0.pc, u0.mem, fun _ => rfl⟩
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
      · obtain ⟨n0, d0, u0⟩ := s.taken hc 0x24E bt_at_244 (by decide) (by
          show (reg n a2).ult (reg n a4) = true
          rw [h2, h4]; simp only [BitVec.ult, BitVec.toNat_ofNat]; exact decide_eq_true (by
            show 127 < e.toNat; omega))
        have t0 : St M BT n0 0x24E (reg n0) := ⟨u0.pc, u0.mem, fun _ => rfl⟩
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
      obtain ⟨n2, d2, u2⟩ := s1.taken hc1 0x20C bt_at_256 (by decide) (by
        show (reg n1 a3 == reg n1 x0) = true; rw [v3, s1.zero]; rfl)
      exact ⟨n2, c1.trans (.single d2), ⟨u2.pc, u2.mem, fun _ => rfl⟩, fun r h1' h3' h4' h5' h8' => by
        rw [u2.regs, k1 r h1' h3' h4' h5' h8']⟩
    · obtain ⟨n2, d2, u2⟩ := s1.notTaken hc1 0x258 bt_at_256 (by decide) (by
        show (reg n1 a3 == reg n1 x0) = false; rw [v3, s1.zero]
        exact decide_eq_false fun e' => hk0 (by
          have := congrArg BitVec.toNat e'; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; exact this))
      have t2 : St _ BT n2 0x258 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
      obtain ⟨n3, d3, u3⟩ := t2.jump hc1 bt_at_258 (off' := 0x244) (by decide) (by rw [t2.pc]; decide)
      obtain ⟨n', c', s', k'⟩ := bt_seg hbt k (e := e + 1) (v := v + 1) (by omega) (by omega) hc1
        (⟨u3.pc, u3.mem, fun _ => rfl⟩ : St _ BT n3 0x244 (reg n3))
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

theorem btKind4 (k : BitVec 8) (h : k.toNat ≤ 3) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
  rcases (show k.toNat = 0 ∨ k.toNat = 1 ∨ k.toNat = 2 ∨ k.toNat = 3 by omega) with e | e | e | e
  · exact Or.inl (BitVec.eq_of_toNat_eq e)
  · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq e))
  · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq e)))
  · exact Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq e)))

def btMapA : List BInstr :=
  [.alu .add a3 x0 (22 : Fin 32), .lbu a4 (22 : Fin 32) 0xC, .aluImm .add a5 a4 0xFFFFFFFE,
   .aluImm .add (22 : Fin 32) (22 : Fin 32) 0x10, .lui a1 0xBE000000]

theorem btMapA_end : blockEnd bootFnCode 0x210 btMapA = some 0x220 :=
  (blockEnd_cons' (off' := 0x212) bt_at_210 rfl (blockEnd_cons' (off' := 0x216) bt_at_212 rfl (blockEnd_cons' (off' := 0x21A) bt_at_216 rfl (blockEnd_cons' (off' := 0x21C) bt_at_21a rfl (blockEnd_cons' (off' := 0x220) bt_at_21c rfl rfl)))))

def btMapB : List BInstr := [.lw a4 a3 0x0, .lw a5 a3 0x4]

theorem btMapB_end : blockEnd bootFnCode 0x22A btMapB = some 0x22E :=
  (blockEnd_cons' (off' := 0x22C) bt_at_22a rfl (blockEnd_cons' (off' := 0x22E) bt_at_22c rfl rfl))

def btMapC : List BInstr :=
  [.alu .add a1 a1 a4, .aluImm .srl a4 a1 0x10, .alu .add a5 a5 (20 : Fin 32), .aluImm .sll a1 a4 0x2,
   .aluImm .srl a5 a5 0x10, .alu .add a1 a1 (9 : Fin 32)]

theorem btMapC_end : blockEnd bootFnCode 0x232 btMapC = some 0x242 :=
  (blockEnd_cons' (off' := 0x234) bt_at_232 rfl (blockEnd_cons' (off' := 0x238) bt_at_234 rfl (blockEnd_cons' (off' := 0x23A) bt_at_238 rfl (blockEnd_cons' (off' := 0x23E) bt_at_23a rfl (blockEnd_cons' (off' := 0x240) bt_at_23e rfl (blockEnd_cons' (off' := 0x242) bt_at_240 rfl rfl))))))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- The loop over the segments that writes each flash segment's MMU
entries, from the head of pass `j` at 0x20C to its exit at 0x25A. -/
theorem bt_map (hbt : BT.toNat + bootFnCode.length ≤ 0x600C4000) {M0 Mi : Word → BitVec 8} {acc imgf : Word}
    {N : Nat} (hN : N ≤ 16) (hacc : acc.toNat % 4 = 0) (hal : acc.toNat + 0x10C ≤ 0x40000000)
    (hkind : ∀ j, j < N → (sgKind M0 acc j).toNat ≤ 3)
    (hT : ∀ i, i < 0x10C → Mi (acc + BitVec.ofNat 32 i) = M0 (acc + BitVec.ofNat 32 i))
    (hci : CodeIn Mi BT bootFnCode) :
    ∀ d j {n : Machine}, j + d = N → j ≤ N → St (mmuMap M0 acc imgf Mi j) BT n 0x20C (reg n) →
      reg n 22 = sgPtr acc j → reg n 18 = sgPtr acc N → reg n a0 = 2 → reg n a2 = 127 → reg n 9 = mmuBase →
      reg n 20 = imgf →
      ∃ n', Steps n n' ∧ St (mmuMap M0 acc imgf Mi N) BT n' 0x25A (reg n') ∧
        ∀ r, r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 8 → r ≠ 22 → reg n' r = reg n r
  | 0, j, n, hj, _, s, h24, h22, _, _, _, _ => by
    obtain rfl : j = N := by omega
    have hc := codeKeep (M' := mmuMap M0 acc imgf Mi j) hci hbt fun x hx => mmuMap_low j x hx
    obtain ⟨n1, d1, u1⟩ := s.taken hc 0x25A bt_at_20c (by decide) (by
      show (reg n 22 == reg n 18) = true; rw [h24, h22]; exact decide_eq_true rfl)
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
    obtain ⟨n1, d1, u1⟩ := s.notTaken hc 0x210 bt_at_20c (by decide) (by
      show (reg n 22 == reg n 18) = false; rw [h24, h22]
      exact decide_eq_false fun e => by
        have := congrArg BitVec.toNat e; unfold sgPtr at this
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega)
    have t1 : St (mmuMap M0 acc imgf Mi j) BT n1 0x210 (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
    obtain ⟨n2, c2, u2⟩ := t1.block btMapA hc btMapA_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
    have r2 : ∀ r, reg n2 r = (runBlock btMapA (mmuMap M0 acc imgf Mi j, reg n1)).2 r := fun r => by rw [u2.regs]
    have t2 : St (mmuMap M0 acc imgf Mi j) BT n2 0x220 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
    have hkd : (mmuMap M0 acc imgf Mi j (reg n1 22 + 0xC)) = sgKind M0 acc j := by
      rw [u1.regs, h24]; exact hF 12 (by decide)
    have v4 : reg n2 a4 = (sgKind M0 acc j).zeroExtend 32 := by
      rw [r2]; simp +decide only [runBlock, BInstr.run, btMapA, upd, ↓reduceIte]; rw [hkd]
    have v5 : reg n2 a5 = (sgKind M0 acc j).zeroExtend 32 + 0xFFFFFFFE := by
      rw [r2]; simp +decide only [runBlock, BInstr.run, btMapA, upd, ↓reduceIte]; rw [hkd]; rfl
    have v3 : reg n2 a3 = sgPtr acc j := by
      rw [r2]; simp +decide only [runBlock, BInstr.run, btMapA, upd, ↓reduceIte]; rw [t1.zero, u1.regs, h24]
      exact BitVec.zero_add _
    have v24 : reg n2 22 = sgPtr acc (j + 1) := by
      rw [r2]; simp +decide only [runBlock, BInstr.run, btMapA, upd, ↓reduceIte]; rw [u1.regs, h24]
      unfold sgPtr; show acc + BitVec.ofNat 32 (16 * j) + BitVec.ofNat 32 16 = _
      rw [add_ofNat_assoc]; rfl
    have v1 : reg n2 a1 = 0xBE000000 := by
      rw [r2]; simp +decide only [runBlock, BInstr.run, btMapA, upd, ↓reduceIte]
    have k2 : ∀ r, r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 22 → reg n2 r = reg n r := fun r h1 h3 h4 h5 h24' => by
      rw [r2, runBlock_reg _ _ _ r t1.zero (by simp only [btMapA]; revert h1 h3 h4 h5 h24'; revert r; decide), u1.regs]
    -- the rest of the loop from 0x20C, after this segment
    have next : ∀ {n' : Machine}, St (mmuMap M0 acc imgf Mi (j + 1)) BT n' 0x20C (reg n') →
        (∀ r, r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 8 → r ≠ 22 → reg n' r = reg n r) → reg n' 22 = sgPtr acc (j + 1) →
        ∃ n'', Steps n' n'' ∧ St (mmuMap M0 acc imgf Mi N) BT n'' 0x25A (reg n'') ∧
          ∀ r, r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 8 → r ≠ 22 → reg n'' r = reg n r := by
      intro n' s' k' h24'
      obtain ⟨n'', c'', s'', k''⟩ := bt_map hbt hN hacc hal hkind hT hci d (j + 1) (by omega) (by omega) s' h24'
        (by rw [k' 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h22)
        (by rw [k' a0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ha0)
        (by rw [k' a2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ha2)
        (by rw [k' 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h9)
        (by rw [k' 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h21)
      exact ⟨n'', c'', s'', fun r h1 h3 h4 h5 h8 h24'' => by rw [k'' r h1 h3 h4 h5 h8 h24'', k' r h1 h3 h4 h5 h8 h24'']⟩
    have hk3 := hkind j hjl
    by_cases hram : 2 ≤ (sgKind M0 acc j).toNat
    · -- a RAM segment: no entries
      obtain ⟨n3, d3, u3⟩ := t2.taken hc 0x20C bt_at_220 (by decide) (by
        show (reg n2 a5).ult (reg n2 a0) = true
        rw [v5, k2 a0 (by decide) (by decide) (by decide) (by decide) (by decide), ha0]
        rcases btKind4 _ hk3 with e | e | e | e <;> rw [e] at hram ⊢ <;> first | exact absurd hram (by decide) | rfl)
      have hm : mmuMap M0 acc imgf Mi (j + 1) = mmuMap M0 acc imgf Mi j := by
        rw [mmuMap, ite_eq_right (by omega)]
      obtain ⟨n', c', s', k'⟩ := next (n' := n3) (by rw [hm]; exact ⟨u3.pc, u3.mem, fun _ => rfl⟩)
        (fun r h1 h3 h4 h5 _ h24' => by rw [u3.regs, k2 r h1 h3 h4 h5 h24']) (by rw [u3.regs]; exact v24)
      exact ⟨n', .cons d1 (c2.trans (.cons d3 c')), s', k'⟩
    · obtain ⟨n3, d3, u3⟩ := t2.notTaken hc 0x224 bt_at_220 (by decide) (by
        show (reg n2 a5).ult (reg n2 a0) = false
        rw [v5, k2 a0 (by decide) (by decide) (by decide) (by decide) (by decide), ha0]
        rcases btKind4 _ hk3 with e | e | e | e <;> rw [e] at hram ⊢ <;> first | exact absurd hram (by decide) | rfl)
      have t3 : St (mmuMap M0 acc imgf Mi j) BT n3 0x224 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
      -- the window base for flash code or flash data, at 0x22A
      obtain ⟨n4, c4, t4, v14, k4⟩ : ∃ n4, Steps n3 n4 ∧ St (mmuMap M0 acc imgf Mi j) BT n4 0x22A (reg n4) ∧
          reg n4 a1 = (if sgKind M0 acc j = 0 then 0xBE000000 else 0xC4000000) ∧
          ∀ r, r ≠ a1 → reg n4 r = reg n2 r := by
        rcases btKind4 _ hk3 with e | e | e | e
        · obtain ⟨n4, d4, u4⟩ := t3.taken hc 0x22A bt_at_224 (by decide) (by
            show (reg n3 a4 == reg n3 x0) = true; rw [u3.regs, u3.regs, v4, t2.zero, e]; rfl)
          exact ⟨n4, .single d4, ⟨u4.pc, u4.mem, fun _ => rfl⟩, by rw [u4.regs, u3.regs, v1, ite_eq_left e],
            fun r _ => by rw [u4.regs, u3.regs]⟩
        · obtain ⟨n4, d4, u4⟩ := t3.notTaken hc 0x226 bt_at_224 (by decide) (by
            show (reg n3 a4 == reg n3 x0) = false; rw [u3.regs, u3.regs, v4, t2.zero, e]; rfl)
          have t4 : St (mmuMap M0 acc imgf Mi j) BT n4 0x226 (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
          obtain ⟨n5, d5, u5⟩ := t4.lui hc bt_at_226 (off' := 0x22A) (by decide)
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
      have t5 : St (mmuMap M0 acc imgf Mi j) BT n5 0x22E (reg n5) := ⟨u5.pc, u5.mem, fun _ => rfl⟩
      have r5 : ∀ r, reg n5 r = (runBlock btMapB (mmuMap M0 acc imgf Mi j, reg n4)).2 r := fun r => by rw [u5.regs]
      have v4_5 : reg n5 a4 = sgAddr M0 acc j := by
        rw [r5]; simp +decide only [runBlock, BInstr.run, btMapB, upd, ↓reduceIte]; rw [a3_4]
        exact hL 0 (by decide)
      have v5_5 : reg n5 a5 = sgOff M0 acc j := by
        rw [r5]; simp +decide only [runBlock, BInstr.run, btMapB, upd, ↓reduceIte]; rw [a3_4]
        exact hL 4 (by decide)
      have k5 : ∀ r, r ≠ a4 → r ≠ a5 → reg n5 r = reg n4 r := fun r h4 h5 => by
        rw [r5, runBlock_reg _ _ _ r t4.zero (by simp only [btMapB]; revert h4 h5; revert r; decide)]
      obtain ⟨n6, d6, u6⟩ := t5.lhu hc bt_at_22e (off' := 0x232) (by decide) (by
        rw [k5 a3 (by decide) (by decide), a3_4, BitVec.toNat_add, hp]; simp; omega)
      have t6 : St (mmuMap M0 acc imgf Mi j) BT n6 0x232 (reg n6) := ⟨u6.pc, u6.mem, fun _ => rfl⟩
      have v3_6 : reg n6 a3 = sgPages M0 acc j := by
        rw [u6.regs]; simp +decide only [upd, ↓reduceIte]
        rw [k5 a3 (by decide) (by decide), a3_4]; unfold sgPages
        rw [show sgPtr acc j + 0xA + 1 = sgPtr acc j + BitVec.ofNat 32 11 by rw [BitVec.add_assoc]; rfl,
          show sgPtr acc j + 0xA = sgPtr acc j + BitVec.ofNat 32 10 from rfl, hF 11 (by decide), hF 10 (by decide)]
      have k6 : ∀ r, r ≠ a3 → reg n6 r = reg n5 r := fun r h => by rw [u6.regs]; exact updz t5.zero h
      obtain ⟨n7, c7, u7⟩ := t6.block btMapC hc btMapC_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
      have t7 : St (mmuMap M0 acc imgf Mi j) BT n7 0x242 (reg n7) := ⟨u7.pc, u7.mem, fun _ => rfl⟩
      have r7 : ∀ r, reg n7 r = (runBlock btMapC (mmuMap M0 acc imgf Mi j, reg n6)).2 r := fun r => by rw [u7.regs]
      have g4 : reg n6 a4 = sgAddr M0 acc j := by rw [k6 a4 (by decide)]; exact v4_5
      have g5 : reg n6 a5 = sgOff M0 acc j := by rw [k6 a5 (by decide)]; exact v5_5
      have g1 : reg n6 a1 = (if sgKind M0 acc j = 0 then 0xBE000000 else 0xC4000000) := by
        rw [k6 a1 (by decide), k5 a1 (by decide) (by decide)]; exact v14
      have g21 : reg n6 20 = imgf := by
        rw [k6 20 (by decide), k5 20 (by decide) (by decide), k4 20 (by decide),
          k2 20 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h21
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
      have k7 : ∀ r, r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ 22 → reg n7 r = reg n r := fun r h1 h3 h4 h5 h24' => by
        rw [r7, runBlock_reg _ _ _ r t6.zero (by simp only [btMapC]; revert h1 h4 h5; revert r; decide), k6 r h3,
          k5 r h4 h5, k4 r h1, k2 r h1 h3 h4 h5 h24']
      have hm : mmuMap M0 acc imgf Mi (j + 1) = mapSeg (mmuMap M0 acc imgf Mi j) (sgEntry M0 acc j)
          (sgPage M0 acc imgf j) (sgPages M0 acc j).toNat := by
        rw [mmuMap, ite_eq_left (by omega)]
      have hpg : (sgPages M0 acc j).toNat < 2 ^ 16 := by
        unfold sgPages; rw [BitVec.toNat_setWidth]; have := (M0 (sgPtr acc j + 0xA + 1) ++ M0 (sgPtr acc j + 0xA)).isLt
        omega
      by_cases hz : (sgPages M0 acc j).toNat = 0
      · obtain ⟨n8, d8, u8⟩ := t7.taken hc 0x20C bt_at_242 (by decide) (by
          show (reg n7 a3 == reg n7 x0) = true
          rw [w3, t7.zero, show sgPages M0 acc j = 0 from BitVec.eq_of_toNat_eq hz]; rfl)
        rw [hz, mapSeg] at hm
        obtain ⟨n', c', s', k'⟩ := next (n' := n8) (by rw [hm]; exact ⟨u8.pc, u8.mem, fun _ => rfl⟩)
          (fun r h1 h3 h4 h5 _ h24' => by rw [u8.regs, k7 r h1 h3 h4 h5 h24'])
          (by rw [u8.regs, r7, runBlock_reg _ _ _ 22 t6.zero (by decide), k6 22 (by decide),
            k5 22 (by decide) (by decide), k4 22 (by decide)]; exact v24)
        exact ⟨n', .cons d1 (c2.trans (.cons d3 (c4.trans (c5.trans (.cons d6 (c7.trans (.cons d8 c'))))))), s', k'⟩
      · obtain ⟨n8, d8, u8⟩ := t7.notTaken hc 0x244 bt_at_242 (by decide) (by
          show (reg n7 a3 == reg n7 x0) = false
          rw [w3, t7.zero]; exact decide_eq_false fun e => hz (by rw [e]; rfl))
        have hc' := codeKeep (M' := mmuMap M0 acc imgf Mi j) hci hbt fun x hx => mmuMap_low j x hx
        obtain ⟨n9, c9, s9, k9⟩ := bt_seg hbt (sgPages M0 acc j).toNat (M := mmuMap M0 acc imgf Mi j)
          (e := sgEntry M0 acc j) (v := sgPage M0 acc imgf j) (by omega) (by omega) hc'
          (⟨u8.pc, u8.mem, fun _ => rfl⟩ : St _ BT n8 0x244 (reg n8)) (by rw [u8.regs]; exact w4)
          (by rw [u8.regs]; exact w5) (by rw [u8.regs, w3, BitVec.ofNat_toNat, BitVec.setWidth_eq])
          (by rw [u8.regs]; exact w1)
          (by rw [u8.regs, k7 a2 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ha2)
        rw [← hm] at s9
        obtain ⟨n', c', s', k'⟩ := next s9
          (fun r h1 h3 h4 h5 h8 h24' => by rw [k9 r h1 h3 h4 h5 h8, u8.regs, k7 r h1 h3 h4 h5 h24'])
          (by rw [k9 22 (by decide) (by decide) (by decide) (by decide) (by decide), u8.regs, r7,
            runBlock_reg _ _ _ 22 t6.zero (by decide), k6 22 (by decide), k5 22 (by decide) (by decide),
            k4 22 (by decide)]; exact v24)
        exact ⟨n', .cons d1 (c2.trans (.cons d3 (c4.trans (c5.trans (.cons d6 (c7.trans (.cons d8 (c9.trans c')))))))),
          s', k'⟩

/-! ## The eFuse controller -/

/-- The entry of `efuse_program_run`. -/
abbrev EPR : Word := BitVec.ofNat 32 efuseProgramRunAddress

/-- The eFuse word that `boot` counts the security level from: block 0's
read register that holds `SECURE_VERSION` in bits 14 to 29. -/
abbrev efuseRd : Word := 0x6000883C

/-- `M` agrees with `Mb` outside the eFuse controller's registers
0x60008800 to 0x600089FF. -/
def EfOut (Mb M : Word → BitVec 8) : Prop :=
  ∀ x : Word, (x.toNat < 0x60008800 ∨ 0x60008A00 ≤ x.toNat) → M x = Mb x

/-- **The eFuse controller's contract**, for the code `code` at `EPR`.

`boot` programs a bit by writing the timing registers and the data word,
then calling `efuse_program_run(0x5A5A, 2)`, which writes the command and
polls until the controller clears it or a timeout passes. It then zeroes
the data registers and, when that call returned nonzero, calls
`efuse_program_run(0x5AA5, 1)` to reload the read registers. After both,
it reads the level word again and counts the attempt as failed unless the
bit it programmed is set.

A call with `a1` equal to 1 or 2 returns to `ra` and keeps every register
other than `a0` to `a5`. Memory outside the controller's registers is
unchanged, and the level word at `efuseRd` reads as its old value with
some bits set: eFuse bits only go from 0 to 1, and a read register shows
blown bits or nothing new. Which bits, and whether the burn worked, is
left open: `boot` detects a burn that didn't set the bit by reading the
word back, and the proof covers every outcome. A plain-memory model of the
controller meets this contract (`eprAt_of_code`). -/
structure EfuseCtl (code : List Nat) : Prop where
  run : ∀ m : Machine, CodeIn m.mem EPR code → m.pc = EPR → (reg m a1 = 1 ∨ reg m a1 = 2) →
    ∃ m', Steps m m' ∧ m'.pc = reg m ra &&& ~~~1 ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧
      EfOut m.mem m'.mem ∧ ∃ X, memLoad32 m'.mem efuseRd = memLoad32 m.mem efuseRd ||| X

/-- Memory `M` holds code at `EPR`, below the peripheral registers, that
meets the eFuse controller's contract. -/
def EprAt (M : Word → BitVec 8) : Prop :=
  ∃ code : List Nat, CodeIn M EPR code ∧ EPR.toNat + code.length ≤ 0x60000000 ∧ EfuseCtl code

theorem EprAt.code {M M' : Word → BitVec 8} (h : EprAt M)
    (hx : ∀ x : Word, 0x40000000 ≤ x.toNat → x.toNat < 0x60000000 → M' x = M x) : EprAt M' := by
  obtain ⟨code, hc, hl, hF⟩ := h
  refine ⟨code, fun i hi => ?_, hl, hF⟩
  have hE : EPR.toNat = (img% efuseProgramRunAddress) := rfl
  rw [hE] at hl
  have e : (EPR + BitVec.ofNat 32 i).toNat = (img% efuseProgramRunAddress) + i := by
    rw [BitVec.toNat_add, hE, BitVec.toNat_ofNat]; omega
  rw [hx _ (by rw [e]; omega) (by rw [e]; omega)]; exact hc i hi

/-- The stack `boot` and its callees use: its own 0x40 bytes, then
`flash_read_words`' 16 and the ROM's `R` below them, and `romStack` for the
other ROM routines. -/
def btK (R romStack : Nat) : Nat := 0x40 + 16 + R + romStack

/-- `M` matches `M0` from the start of the ROM to the peripheral registers
at 0x60000000, where the code `boot` runs and calls is. -/
def BtHi (M0 M : Word → BitVec 8) : Prop := ∀ x : Word, 0x40000000 ≤ x.toNat → x.toNat < 0x60000000 → M x = M0 x

/-- What `boot` needs of its arguments and memory: the stack in data RAM,
the accepted header below the ROM and apart from the stack, segment kinds
0 to 3, and each RAM segment word-aligned, below the ROM, and apart from
the header and the stack. -/
structure BtCtx (M0 : Word → BitVec 8) (top acc imgf : Word) (R romStack : Nat) (romBase : Word)
    (romCode : List Nat) : Prop where
  code : CodeIn M0 BT bootFnCode
  rfw : CodeIn M0 (BitVec.ofNat 32 romFlashReadWordsAddress) romFlashReadWordsCode
  epr : EprAt M0
  panic : PanicCode M0
  rom : CodeIn M0 romBase romCode
  hrb : 0x40000000 ≤ romBase.toNat
  hrl : romBase.toNat + romCode.length ≤ 0x60000000
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

theorem panicFns_mid : ∀ p ∈ panicFns, 0x40000000 ≤ p.1 ∧ p.1 + p.2.length ≤ 0x60000000 := by decide

theorem panicKeep {M0 M : Word → BitVec 8} (hP : PanicCode M0) (h : BtHi M0 M) : PanicCode M := fun p hp i hi => by
  have := panicFns_mid p hp
  rw [h _ (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)
    (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)]
  exact hP p hp i hi

theorem hiKeep {M0 M : Word → BitVec 8} {b : Word} {code : List Nat} (hc : CodeIn M0 b code) (h : BtHi M0 M)
    (hb : 0x40000000 ≤ b.toNat) (hl : b.toNat + code.length ≤ 0x60000000) : CodeIn M b code := fun i hi => by
  rw [h _ (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
  exact hc i hi

def btCopyB : List BInstr := [.lw a0 (9 : Fin 32) 0x4, .lw a2 (9 : Fin 32) 0x8, .alu .add a0 a0 (20 : Fin 32), .aluImm .srl a2 a2 0x2]

theorem btCopyB_end : blockEnd bootFnCode 0x1CA btCopyB = some 0x1D2 :=
  (blockEnd_cons' (off' := 0x1CC) bt_at_1ca rfl (blockEnd_cons' (off' := 0x1CE) bt_at_1cc rfl (blockEnd_cons' (off' := 0x1D0) bt_at_1ce rfl (blockEnd_cons' (off' := 0x1D2) bt_at_1d0 rfl rfl))))

def btNextB : List BInstr := [.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x10, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFF0]

theorem btNextB_end : blockEnd bootFnCode 0x1DC btNextB = some 0x1E0 :=
  (blockEnd_cons' (off' := 0x1DE) bt_at_1dc rfl (blockEnd_cons' (off' := 0x1E0) bt_at_1de rfl rfl))

section Copy
variable {flash : Nat → BitVec 8} {M0 : Word → BitVec 8} {top acc imgf romBase : Word} {R romStack : Nat}
  {romCode : List Nat}

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- The loop that copies each RAM segment from flash, from the head of
pass `j` at 0x1B6 to its exit at 0x1E2, or to `halt` when a read fails. -/
theorem bt_copy (C : BtCtx M0 top acc imgf R romStack romBase romCode) (hROM : RomRead flash R romBase romCode) :
    ∀ d j {n : Machine}, j + d = sgCount M0 acc → j < sgCount M0 acc → St n.mem BT n 0x1B6 (reg n) →
      BtHi M0 n.mem →
      (∀ x, Sep (top - BitVec.ofNat 32 (btK R romStack)) (btK R romStack) x 1 →
        n.mem x = ramLoad flash M0 acc imgf j x) →
      reg n sp = top + 0xFFFFFFC0 → reg n 9 = sgPtr acc j → reg n 8 = BitVec.ofNat 32 (16 * (sgCount M0 acc - j)) →
      reg n 19 = 2 → reg n 21 = 0xFF900000 → reg n 20 = imgf →
      (∃ n', Steps n n' ∧ St n'.mem BT n' 0x1E2 (reg n') ∧ BtHi M0 n'.mem ∧
        (∀ i, i < 0x40 → n'.mem (top + 0xFFFFFFC0 + BitVec.ofNat 32 i) = n.mem (top + 0xFFFFFFC0 + BitVec.ofNat 32 i)) ∧
        (∀ x, Sep (top - BitVec.ofNat 32 (btK R romStack)) (btK R romStack) x 1 →
          n'.mem x = ramLoad flash M0 acc imgf (sgCount M0 acc) x) ∧
        ∀ r, romKeep r = true → r ≠ 8 → r ≠ 9 → reg n' r = reg n r) ∨ HaltsWith n 0xE2
  | 0, j, _, hj, hjN, _, _, _, _, _, _, _, _, _ => absurd hj (by omega)
  | d + 1, j, n, hj, hjN, s, hH, hM, hsp, h9, h8, h19, h23, h21 => by
    have hN16 := sgCount_le M0 acc
    have hc : CodeIn n.mem BT bootFnCode := hiKeep C.code hH (by decide) (by decide)
    have hKv : btK R romStack = 0x40 + 16 + R + romStack := rfl
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
    have tail : ∀ {n' : Machine}, Steps n n' → St n'.mem BT n' 0x1DC (reg n') → BtHi M0 n'.mem →
        (∀ x, Sep (top - BitVec.ofNat 32 (btK R romStack)) (btK R romStack) x 1 →
          n'.mem x = ramLoad flash M0 acc imgf (j + 1) x) → (∀ r, romKeep r = true → reg n' r = reg n r) →
        (∀ i, i < 0x40 → n'.mem (top + 0xFFFFFFC0 + BitVec.ofNat 32 i) = n.mem (top + 0xFFFFFFC0 + BitVec.ofNat 32 i)) →
        (∃ n'', Steps n n'' ∧ St n''.mem BT n'' 0x1E2 (reg n'') ∧ BtHi M0 n''.mem ∧
          (∀ i, i < 0x40 → n''.mem (top + 0xFFFFFFC0 + BitVec.ofNat 32 i) = n.mem (top + 0xFFFFFFC0 + BitVec.ofNat 32 i)) ∧
          (∀ x, Sep (top - BitVec.ofNat 32 (btK R romStack)) (btK R romStack) x 1 →
            n''.mem x = ramLoad flash M0 acc imgf (sgCount M0 acc) x) ∧
          ∀ r, romKeep r = true → r ≠ 8 → r ≠ 9 → reg n'' r = reg n r) ∨ HaltsWith n 0xE2 := by
      intro n' c' s' hH' hM' k' fr'
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
      have t2 : St n'.mem BT n2 0x1E0 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
      by_cases hl : j + 1 < sgCount M0 acc
      · obtain ⟨n3, d3, u3⟩ := t2.taken hc' 0x1B6 bt_at_1e0 (by decide) (by
          show (reg n2 8 != reg n2 x0) = true
          rw [v8, t2.zero]
          exact bne_iff_ne.mpr fun e => by
            have := congrArg BitVec.toNat e
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
            exact absurd this (by show 16 * (sgCount M0 acc - (j + 1)) ≠ 0; omega))
        have kk : ∀ r, romKeep r = true → r ≠ 8 → r ≠ 9 → reg n3 r = reg n r := fun r hr h8' h9' => by
          rw [u3.regs, k2 r h8' h9', k' r hr]
        rcases bt_copy C hROM d (j + 1) (by omega) hl (⟨u3.pc, by rw [u3.mem], fun _ => rfl⟩ :
            St n3.mem BT n3 0x1B6 (reg n3)) (by rw [u3.mem]; exact hH')
            (fun x hx => by rw [u3.mem]; exact hM' x hx)
            (by rw [kk sp (by decide) (by decide) (by decide)]; exact hsp) (by rw [u3.regs]; exact v9)
            (by rw [u3.regs]; exact v8) (by rw [kk 19 (by decide) (by decide) (by decide)]; exact h19)
            (by rw [kk 21 (by decide) (by decide) (by decide)]; exact h23)
            (by rw [kk 20 (by decide) (by decide) (by decide)]; exact h21) with ⟨n'', c'', s'', hH'', fr'', hM'', k''⟩ | hp'
        · exact Or.inl ⟨n'', c'.trans (c2.trans (.cons d3 c'')), s'', hH'',
            fun i hi => by rw [fr'' i hi, u3.mem]; exact fr' i hi, hM'', fun r hr h8' h9' => by
            rw [k'' r hr h8' h9', kk r hr h8' h9']⟩
        · exact Or.inr (HaltsWith.of_steps (c'.trans (c2.trans (.single d3))) hp')
      · have e : j + 1 = sgCount M0 acc := by omega
        obtain ⟨n3, d3, u3⟩ := t2.notTaken hc' 0x1E2 bt_at_1e0 (by decide) (by
          show (reg n2 8 != reg n2 x0) = false
          rw [v8, t2.zero, ← e, Nat.sub_self]; rfl)
        rw [e] at hM'
        exact Or.inl ⟨n3, c'.trans (c2.trans (.single d3)), ⟨u3.pc, rfl, fun _ => rfl⟩,
          by rw [u3.mem]; exact hH', fun i hi => by rw [u3.mem]; exact fr' i hi,
          fun x hx => by rw [u3.mem]; exact hM' x hx,
          fun r hr h8' h9' => by rw [u3.regs, k2 r h8' h9', k' r hr]⟩
    -- the kind
    obtain ⟨n1, d1, u1⟩ := s.lbu hc bt_at_1b6 (off' := 0x1BA) (by decide)
    have t1 := u1.self
    have v0 : reg n1 a0 = (sgKind M0 acc j).zeroExtend 32 := by
      rw [u1.regs]; simp +decide only [upd, ↓reduceIte]; rw [h9]; exact congrArg (·.zeroExtend 32) (hF 12 (by decide))
    have k1 : ∀ r, r ≠ a0 → reg n1 r = reg n r := fun r h => by rw [u1.regs]; exact updz s.zero h
    have hk3 := C.kind j hjN
    by_cases hram : 2 ≤ (sgKind M0 acc j).toNat
    · obtain ⟨hda, hdl, sDA, sDS, hsa⟩ := C.ram j hjN hram
      obtain ⟨n2, d2, u2⟩ := t1.notTaken hc 0x1BE bt_at_1ba (by decide) (by
        show (reg n1 a0).ult (reg n1 19) = false
        rw [v0, k1 19 (by decide), h19]
        rcases btKind4 _ hk3 with e | e | e | e <;> rw [e] at hram ⊢ <;> first | exact absurd hram (by decide) | rfl)
      have t2 : St n.mem BT n2 0x1BE (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
      have a9 : ∀ {f : Fin 32 → Word}, (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ ra → f r = reg n r) → f 9 = sgPtr acc j :=
        fun h => by rw [h 9 (by decide) (by decide) (by decide) (by decide)]; exact h9
      -- the destination, at 0x1CA
      obtain ⟨n5, c5, t5, v1, k5⟩ : ∃ n5, Steps n2 n5 ∧ St n.mem BT n5 0x1CA (reg n5) ∧
          reg n5 a1 = sgDest M0 acc j ∧ ∀ r, r ≠ a1 → reg n5 r = reg n2 r := by
        have ld : memLoad32 n.mem (reg n2 9 + 0x0) = sgAddr M0 acc j := by
          rw [u2.regs, k1 9 (by decide), h9]; exact hL 0 (by decide)
        rcases btKind4 _ hk3 with e | e | e | e
        · rw [e] at hram; exact absurd hram (by decide)
        · rw [e] at hram; exact absurd hram (by decide)
        · obtain ⟨n3, d3, u3⟩ := t2.notTaken hc 0x1C2 bt_at_1be (by decide) (by
            show (reg n2 a0 != reg n2 19) = false
            rw [u2.regs, u2.regs, v0, k1 19 (by decide), h19, e]; rfl)
          have t3 : St n.mem BT n3 0x1C2 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
          obtain ⟨n4, d4, u4⟩ := t3.lw hc bt_at_1c2 (off' := 0x1C4) (by decide)
            (by rw [u3.regs, u2.regs, k1 9 (by decide), h9, add_lit_zero, hp]; omega)
          have t4 := u4.self
          obtain ⟨n5, d5, u5⟩ := t4.alu hc bt_at_1c4 (off' := 0x1C6) (by decide)
          have t5 := u5.self
          obtain ⟨n6, d6, u6⟩ := t5.jump hc bt_at_1c6 (off' := 0x1CA) (by decide) (by rw [t5.pc]; decide)
          refine ⟨n6, .cons d3 (.cons d4 (.cons d5 (.single d6))), ⟨u6.pc, u6.mem, fun _ => rfl⟩, ?_, fun r h => ?_⟩
          · have r23 : reg n4 21 = 0xFF900000 := by
              rw [u4.regs, updz t3.zero (by decide), u3.regs, u2.regs, k1 21 (by decide), h23]
            have r1 : reg n4 a1 = sgAddr M0 acc j := by
              rw [u4.regs]; simp +decide only [upd, ↓reduceIte]; rw [u3.regs, ld]
            rw [u6.regs, u5.regs]; simp +decide only [upd, ↓reduceIte]
            rw [r1, r23]; unfold sgDest; rw [ite_eq_left e]; rfl
          · rw [u6.regs, u5.regs, updz t4.zero h, u4.regs, updz t3.zero h, u3.regs]
        · obtain ⟨n3, d3, u3⟩ := t2.taken hc 0x1C8 bt_at_1be (by decide) (by
            show (reg n2 a0 != reg n2 19) = true
            rw [u2.regs, u2.regs, v0, k1 19 (by decide), h19, e]; rfl)
          have t3 : St n.mem BT n3 0x1C8 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
          obtain ⟨n4, d4, u4⟩ := t3.lw hc bt_at_1c8 (off' := 0x1CA) (by decide)
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
      have t6 : St n.mem BT n6 0x1D2 (reg n6) := ⟨u6.pc, u6.mem, fun _ => rfl⟩
      have w0 : reg n6 a0 = sgSrc M0 acc imgf j := by
        rw [r6]; simp +decide only [runBlock, BInstr.run, btCopyB, upd, ↓reduceIte]
        rw [a9 k25, show memLoad32 n.mem (sgPtr acc j + 4) = memLoad32 M0 (sgPtr acc j + 4) from hL 4 (by decide), k25 20 (by decide) (by decide) (by decide) (by decide), h21]; rfl
      have w2 : reg n6 a2 = sgLen M0 acc j >>> 2 := by
        rw [r6]; simp +decide only [runBlock, BInstr.run, btCopyB, upd, ↓reduceIte]
        rw [a9 k25, show memLoad32 n.mem (sgPtr acc j + 8) = memLoad32 M0 (sgPtr acc j + 8) from hL 8 (by decide)]; rfl
      have w1 : reg n6 a1 = sgDest M0 acc j := by
        rw [r6, runBlock_reg _ _ _ a1 t5.zero (by decide)]; exact v1
      have k6 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ ra → reg n6 r = reg n r := fun r h0 h1 h2 hr => by
        rw [r6, runBlock_reg _ _ _ r t5.zero (by simp only [btCopyB]; revert h0 h2; revert r; decide)]
        exact k25 r h0 h1 h2 hr
      obtain ⟨n7, c7, pc7, mem7, regs7⟩ := t6.callRa (cb := BitVec.ofNat 32 romFlashReadWordsAddress) hc
        bt_at_1d2 bt_at_1d6 (by decide) (by decide)
      have k7 : ∀ r, r ≠ ra → reg n7 r = reg n6 r := fun r h => by rw [regs7]; exact updz t6.zero h
      obtain ⟨G, hG⟩ : ∃ G, top - BitVec.ofNat 32 (0x40 + 16 + R) = G := ⟨_, rfl⟩
      have hGn : G.toNat = top.toNat - (0x40 + 16 + R) := by
        rw [← hG, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      have hGsp : G + BitVec.ofNat 32 (16 + R) = top + 0xFFFFFFC0 := BitVec.eq_of_toNat_eq (by
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, hGn, show (0xFFFFFFC0 : Word).toNat = 2 ^ 32 - 0x40 from rfl]
        omega)
      have hGS : (top - BitVec.ofNat 32 (btK R romStack)) + BitVec.ofNat 32 romStack = G := BitVec.eq_of_toNat_eq (by
        rw [BitVec.toNat_add, hSn, BitVec.toNat_ofNat, hGn, hKv]; omega)
      have sGx : ∀ x, Sep (top - BitVec.ofNat 32 (btK R romStack)) (btK R romStack) x 1 → Sep G (16 + R) x 1 :=
        fun x hx => by have := hx.sub (c := romStack) (l := 16 + R) (by rw [hKv]; omega); rwa [hGS] at this
      have hdn := hdl; unfold sgBytes at hdn
      obtain ⟨n8, c8, pc8, sp8, keep8, a08, cp8, fr8⟩ := romFlashReadWords_correct hROM n7
        (P := BitVec.ofNat 32 romFlashReadWordsAddress) (G := G) (dst := sgDest M0 acc j)
        (w := sgLen M0 acc j >>> 2) (src := sgSrc M0 acc imgf j) (retAddr := BT + BitVec.ofNat 32 (0x1D2 + 8))
        ⟨rfl, by rw [mem7]; exact hiKeep C.rfw hH (by decide) (by decide), by rw [hGn]; omega, hR4,
          by rw [hGn]; omega, hda, by omega,
          sep_of_le (by rw [hGn, show (BitVec.ofNat 32 romFlashReadWordsAddress).toNat = (img% romFlashReadWordsAddress) from rfl]; omega) (by decide),
          sep_of_le (by show _ ≤ (BitVec.ofNat 32 romFlashReadWordsAddress).toNat; rw [show (BitVec.ofNat 32 romFlashReadWordsAddress).toNat = (img% romFlashReadWordsAddress) from rfl]; omega) (by decide),
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
      have t8 : St n8.mem BT n8 0x1DA (reg n8) := ⟨by rw [pc8], rfl, fun _ => rfl⟩
      rcases a08 with a0z | a0o
      · -- the read failed: halt(0xE2)
        obtain ⟨n9, d9, u9⟩ := t8.taken hc8 0x290 bt_at_1da (by decide) (by
          show (reg n8 a0 == reg n8 x0) = true; rw [a0z, t8.zero]; rfl)
        have t9 : St n8.mem BT n9 0x290 (reg n9) := ⟨u9.pc, u9.mem, fun _ => rfl⟩
        obtain ⟨n10, d10, u10⟩ := t9.aluImm hc8 bt_at_290 (off' := 0x294) (by decide)
        obtain ⟨n11, c11, pc11, mem11, regs11⟩ := u10.self.callRa (cb := haltBase) hc8 bt_at_294 bt_at_298
          (by decide) (by decide)
        have sp11 : reg n11 sp = top + 0xFFFFFFC0 := by
          rw [regs11, updz u10.self.zero (by decide), u10.regs, updz t9.zero (by decide), u9.regs,
            k8 sp (by decide), hsp]
        have hspn : (top + 0xFFFFFFC0).toNat = top.toNat - 0x40 := by
          rw [BitVec.toNat_add, show (0xFFFFFFC0 : Word).toNat = 2 ^ 32 - 0x40 from rfl]; omega
        have a011 : reg n11 a0 = 0xE2 := by
          rw [regs11, updz u10.self.zero (by decide), u10.regs]; simp +decide only [upd_app, ↓reduceIte]
          rw [t9.zero]; rfl
        have hR11 : Room (reg n11 sp) 16 := by
          rw [sp11]; refine ⟨by rw [hspn]; omega, by rw [hspn]; omega, by rw [hspn]; unfold dramEnd; omega⟩
        have hh := halt_haltCode n11 (by rw [mem11]; exact panicKeep C.panic hH8) pc11 hR11
        rw [a011] at hh
        exact Or.inr (HaltsWith.of_steps (.cons d1 (.cons d2 (c5.trans (c6.trans (c7.trans (c8.trans
          (.cons d9 (.cons d10 c11)))))))) hh)
      · obtain ⟨n9, d9, u9⟩ := t8.notTaken hc8 0x1DC bt_at_1da (by decide) (by
          show (reg n8 a0 == reg n8 x0) = false; rw [a0o, t8.zero]; rfl)
        refine tail (.cons d1 (.cons d2 (c5.trans (c6.trans (c7.trans (c8.trans (.single d9)))))))
          ⟨u9.pc, rfl, fun _ => rfl⟩ (by rw [u9.mem]; exact hH8) (fun x hx => ?_) (fun r hr => by rw [u9.regs, k8 r hr]) (fun i hi => ?_)
        rotate_left
        · have hFn : (top + 0xFFFFFFC0 + BitVec.ofNat 32 i).toNat = top.toNat - 0x40 + i := by
            rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
              show (0xFFFFFFC0 : Word).toNat = 2 ^ 32 - 0x40 from rfl]; omega
          have hFe : top + 0xFFFFFFC0 + BitVec.ofNat 32 i =
              (top - BitVec.ofNat 32 (btK R romStack)) + BitVec.ofNat 32 (btK R romStack - 0x40 + i) :=
            BitVec.eq_of_toNat_eq (by
              rw [hFn, BitVec.toNat_add, hSn, BitVec.toNat_ofNat, hKv]; omega)
          rw [u9.mem, fr8 _ (sep_of_le (by rw [hGn, hFn]; omega) (by omega))
            (by rw [hFe]; exact sDS.subR (by rw [hKv]; omega)), mem7]
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
    · obtain ⟨n2, d2, u2⟩ := t1.taken hc 0x1DC bt_at_1ba (by decide) (by
        show (reg n1 a0).ult (reg n1 19) = true
        rw [v0, k1 19 (by decide), h19]
        rcases btKind4 _ hk3 with e | e | e | e <;> rw [e] at hram ⊢ <;> first | exact absurd hram (by decide) | rfl)
      exact tail (.cons d1 (.single d2)) ⟨u2.pc, by rw [u2.mem], fun _ => rfl⟩
        (by rw [u2.mem]; exact hH)
        (fun x hx => by rw [u2.mem, hM x hx, ramLoad, ite_eq_right hram])
        (fun r hr => by rw [u2.regs, k1 r (by rintro rfl; exact absurd hr (by decide))])
        (fun i hi => by rw [u2.mem])

end Copy

section Agree
variable {O : Word → Prop} {X Y : Word → BitVec 8}

theorem mmuInv_agree (h : ∀ x, O x → X x = Y x) (k : Nat) : ∀ x, O x → mmuInv X k x = mmuInv Y k x :=
  fun x hx => by unfold mmuInv; rw [h x hx]

theorem st32_agree (h : ∀ x, O x → X x = Y x) (a v : Word) : ∀ x, O x → memStore32 X a v x = memStore32 Y a v x :=
  fun x hx => by rw [st32_read, st32_read, h x hx]

theorem mapSeg_agree : ∀ (k : Nat) {X Y : Word → BitVec 8} (e v : Word), (∀ x, O x → X x = Y x) →
    ∀ x, O x → mapSeg X e v k x = mapSeg Y e v k x
  | 0, _, _, _, _, h => h
  | k + 1, X, Y, e, v, h => by
    simp only [mapSeg]
    refine mapSeg_agree k (e + 1) (v + 1) fun x hx => ?_
    by_cases he : e.toNat ≤ 127
    · rw [ite_eq_left he, ite_eq_left he]; exact st32_agree h _ _ x hx
    · rw [ite_eq_right he, ite_eq_right he]; exact h x hx

theorem mmuMap_agree {M0 : Word → BitVec 8} {acc imgf : Word} (h : ∀ x, O x → X x = Y x) :
    ∀ j, ∀ x, O x → mmuMap M0 acc imgf X j x = mmuMap M0 acc imgf Y j x
  | 0 => h
  | j + 1 => by
    simp only [mmuMap]
    by_cases hk : (sgKind M0 acc j).toNat < 2
    · rw [ite_eq_left hk, ite_eq_left hk]; exact mapSeg_agree _ _ _ (mmuMap_agree h j)
    · rw [ite_eq_right hk, ite_eq_right hk]; exact mmuMap_agree h j

theorem busOn_agree (h : ∀ x, O x → X x = Y x) (hc : ∀ i, i < 4 → O (icacheCtrl1 + BitVec.ofNat 32 i)) :
    ∀ x, O x → busOn X x = busOn Y x := fun x hx => by
  unfold busOn
  rw [memLoad32_congr (M := Y) (M' := X) fun i hi => h _ (hc i hi)]
  exact st32_agree h _ _ x hx

end Agree

theorem saveMem_sep {M : Word → BitVec 8} {G : Word} {f : Fin 32 → Word} {x : Word} :
    ∀ ps : List (Fin 32 × Word), (∀ p ∈ ps, Sep (G + p.2) 4 x 1) → saveMem M G f ps x = M x
  | [], _ => rfl
  | p :: ps, h => by
    simp only [saveMem]
    rw [saveMem_sep ps fun q hq => h q (List.mem_cons_of_mem _ hq), memStore32_get_sep (h p (List.mem_cons_self ..))]

section Congr
variable {M M' : Word → BitVec 8} {acc imgf : Word}

/-- `M` and `M'` hold the same accepted header at `acc`. -/
def HdrEq (M M' : Word → BitVec 8) (acc : Word) : Prop :=
  ∀ i, i < 0x10C → M (acc + BitVec.ofNat 32 i) = M' (acc + BitVec.ofNat 32 i)

theorem HdrEq.byte (h : HdrEq M M' acc) {j c : Nat} (hj : j < 16) (hc : c < 16) :
    M (sgPtr acc j + BitVec.ofNat 32 c) = M' (sgPtr acc j + BitVec.ofNat 32 c) := by
  unfold sgPtr; rw [add_ofNat_assoc]; exact h _ (by omega)

theorem HdrEq.word (h : HdrEq M M' acc) {j c : Nat} (hj : j < 16) (hc : c ≤ 12) :
    memLoad32 M (sgPtr acc j + BitVec.ofNat 32 c) = memLoad32 M' (sgPtr acc j + BitVec.ofNat 32 c) :=
  memLoad32_congr fun i hi => by rw [add_ofNat_assoc]; exact h.byte hj (by omega)

theorem HdrEq.count (h : HdrEq M M' acc) : sgCount M acc = sgCount M' acc := by
  have e : memLoad32 M (acc + 0x108) = memLoad32 M' (acc + 0x108) := memLoad32_congr fun i hi => by
    rw [show acc + 0x108 + BitVec.ofNat 32 i = acc + BitVec.ofNat 32 (0x108 + i) from add_ofNat_assoc acc 0x108 i]
    exact h _ (by omega)
  unfold sgCount; rw [e]

theorem HdrEq.kind (h : HdrEq M M' acc) {j : Nat} (hj : j < 16) : sgKind M acc j = sgKind M' acc j :=
  h.byte hj (c := 12) (by omega)

theorem HdrEq.addr (h : HdrEq M M' acc) {j : Nat} (hj : j < 16) : sgAddr M acc j = sgAddr M' acc j :=
  h.word hj (c := 0) (by omega)

theorem HdrEq.off (h : HdrEq M M' acc) {j : Nat} (hj : j < 16) : sgOff M acc j = sgOff M' acc j :=
  h.word hj (c := 4) (by omega)

theorem HdrEq.len (h : HdrEq M M' acc) {j : Nat} (hj : j < 16) : sgLen M acc j = sgLen M' acc j :=
  h.word hj (c := 8) (by omega)

theorem HdrEq.pages (h : HdrEq M M' acc) {j : Nat} (hj : j < 16) : sgPages M acc j = sgPages M' acc j := by
  unfold sgPages
  rw [show sgPtr acc j + 0xA + 1 = sgPtr acc j + BitVec.ofNat 32 11 from add_ofNat_assoc _ 10 1,
    show sgPtr acc j + (0xA : Word) = sgPtr acc j + BitVec.ofNat 32 10 from rfl,
    h.byte hj (c := 11) (by omega), h.byte hj (c := 10) (by omega)]

theorem HdrEq.dest (h : HdrEq M M' acc) {j : Nat} (hj : j < 16) : sgDest M acc j = sgDest M' acc j := by
  unfold sgDest; rw [h.kind hj, h.addr hj]

theorem HdrEq.src (h : HdrEq M M' acc) {j : Nat} (hj : j < 16) : sgSrc M acc imgf j = sgSrc M' acc imgf j := by
  unfold sgSrc; rw [h.off hj]

theorem HdrEq.bytes (h : HdrEq M M' acc) {j : Nat} (hj : j < 16) : sgBytes M acc j = sgBytes M' acc j := by
  unfold sgBytes; rw [h.len hj]

theorem HdrEq.entry (h : HdrEq M M' acc) {j : Nat} (hj : j < 16) : sgEntry M acc j = sgEntry M' acc j := by
  unfold sgEntry; rw [h.kind hj, h.addr hj]

theorem HdrEq.page (h : HdrEq M M' acc) {j : Nat} (hj : j < 16) : sgPage M acc imgf j = sgPage M' acc imgf j := by
  unfold sgPage; rw [h.src hj]

variable {flash : Nat → BitVec 8} {O : Word → Prop}

theorem HdrEq.ramLoad (h : HdrEq M M' acc) (hO : ∀ x, O x → M x = M' x) :
    ∀ j, j ≤ 16 → ∀ x, O x → ramLoad flash M acc imgf j x = ramLoad flash M' acc imgf j x
  | 0, _, x, hx => hO x hx
  | j + 1, hj, x, hx => by
    simp only [C3.RV32.Cur.ramLoad]
    rw [h.kind (by omega)]
    by_cases hk : 2 ≤ (sgKind M' acc j).toNat
    · rw [if_pos hk, if_pos hk]; unfold copyIn
      rw [h.dest (by omega), h.bytes (by omega), h.src (by omega), HdrEq.ramLoad h hO j (by omega) x hx]
    · rw [if_neg hk, if_neg hk]; exact HdrEq.ramLoad h hO j (by omega) x hx

theorem HdrEq.mmuMap (h : HdrEq M M' acc) {X Y : Word → BitVec 8} (hO : ∀ x, O x → X x = Y x) :
    ∀ j, j ≤ 16 → ∀ x, O x → mmuMap M acc imgf X j x = mmuMap M' acc imgf Y j x
  | 0, _, x, hx => hO x hx
  | j + 1, hj, x, hx => by
    simp only [C3.RV32.Cur.mmuMap]
    rw [h.kind (by omega), h.entry (by omega), h.page (by omega), h.pages (by omega)]
    by_cases hk : (sgKind M' acc j).toNat < 2
    · rw [if_pos hk, if_pos hk]; exact mapSeg_agree _ _ _ (HdrEq.mmuMap h hO j (by omega)) x hx
    · rw [if_neg hk, if_neg hk]; exact HdrEq.mmuMap h hO j (by omega) x hx

/-- `bootMem` reads its memory only at the header and at `O`. -/
theorem HdrEq.bootMem (h : HdrEq M M' acc) (hO : ∀ x, O x → M x = M' x)
    (hic : ∀ i, i < 4 → O (icacheCtrl1 + BitVec.ofNat 32 i)) :
    ∀ x, O x → bootMem flash M acc imgf x = bootMem flash M' acc imgf x := by
  unfold C3.RV32.Cur.bootMem; rw [h.count]
  have hN := sgCount_le M' acc
  exact busOn_agree (h.mmuMap (mmuInv_agree (h.ramLoad hO _ hN) 128) _ hN) hic

end Congr

/-- `BtCtx` holds of memory that keeps the code and the header. -/
theorem BtCtx.transfer {M M' : Word → BitVec 8} {top acc imgf romBase : Word} {R romStack : Nat}
    {romCode : List Nat} (C : BtCtx M top acc imgf R romStack romBase romCode) (hH : BtHi M M')
    (hh : HdrEq M M' acc) : BtCtx M' top acc imgf R romStack romBase romCode := by
  have hN := sgCount_le M acc
  refine ⟨hiKeep C.code hH (by decide) (by decide), hiKeep C.rfw hH (by decide) (by decide),
    C.epr.code hH, panicKeep C.panic hH, hiKeep C.rom hH C.hrb C.hrl, C.hrb, C.hrl,
    C.hsp, C.hspl, C.hsph, C.hR, C.hacc, C.haccl, C.sAS, fun j hj => ?_, fun j hj hk => ?_⟩
  · rw [← hh.count] at hj; rw [← hh.kind (by omega)]; exact C.kind j hj
  · rw [← hh.count] at hj; rw [← hh.kind (by omega)] at hk
    rw [← hh.dest (by omega), ← hh.bytes (by omega), ← hh.src (by omega)]; exact C.ram j hj hk

end C3.RV32.Cur
