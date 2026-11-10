/-!
# The security level

The security level is the number of set bits in the 16-bit `SECURE_VERSION`
eFuse field. eFuse bits only go from 0 to 1, so the level never decreases.
These definitions follow `c3-boot/verify/src/level.rs` and the bootloader's
`efuse::raise_level`.
-/

namespace C3

/-- The `SECURE_VERSION` eFuse field, bit 0 first. A device has 16 bits. -/
abbrev Fuses := List Bool

/-- The highest security level, and the highest security version an image
can carry. -/
def maxLevel : Nat := 16

/-- The security level: the number of set bits. -/
def level : Fuses → Nat
  | [] => 0
  | b :: f => (if b then 1 else 0) + level f

/-- The bits left set after programming the bits set in `m`. -/
def burn : Fuses → Fuses → Fuses
  | [], _ => []
  | f, [] => f
  | a :: f, b :: m => (a || b) :: burn f m

/-- The index of the lowest clear bit, which the bootloader programs next. -/
def firstClear : Fuses → Option Nat
  | [] => none
  | false :: _ => some 0
  | true :: f => (firstClear f).map (· + 1)

/-- The field after programming its lowest clear bit. -/
def setFirstClear : Fuses → Fuses
  | [] => []
  | false :: f => true :: f
  | true :: f => true :: setFirstClear f

/-- Raises the level to `target` one bit at a time, lowest clear bit first,
as the bootloader does when every bit programs and reads back. -/
def raise (f : Fuses) (target : Nat) : Fuses :=
  go f.length f
where
  /-- At most `n` more bits. -/
  go : Nat → Fuses → Fuses
    | 0, f => f
    | n + 1, f => if target ≤ level f then f else go n (setFirstClear f)

/-- The level the bootloader must reach before it jumps to a slot: the
slot's level if the boot-state record marks the slot confirmed and its level
is higher, and the current level otherwise. -/
def burnTarget (slotLevel : Nat) (confirmed : Bool) (efuseLevel : Nat) : Nat :=
  if confirmed && efuseLevel < slotLevel then slotLevel else efuseLevel

/-- The level rules for one slot: the image's security version is at most
16 and equals the trust-root blob's level, which is at least the key-set
chain's level and at least the eFuse level. -/
def checkSlot (chainLevel blobLevel securityVersion efuseLevel : Nat) : Bool :=
  securityVersion ≤ maxLevel && securityVersion == blobLevel &&
    chainLevel ≤ blobLevel && efuseLevel ≤ blobLevel

/-- The field as the bootloader reads it from `SECURE_VERSION`. -/
def Fuses.ofNat (v : Nat) : Fuses :=
  (List.range maxLevel).map v.testBit

end C3
