/-
TRUSTED. Changes to this file need human review.

How an image's bytes appear as instruction memory once it is loaded at
`base`: QEMU's `-device loader`, or the ESP32-C3 flash mapping. Words are
little-endian. Addresses outside the image read as zero, which decodes to no
instruction, so running off the image faults in the model.
-/
import VerifiedFw.RiscV.Machine

namespace VerifiedFw.Loader

open VerifiedFw.RiscV

def leWord (b0 b1 b2 b3 : UInt8) : Word :=
  .ofNat 32 (b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat)

def imemOf (base : Word) (image : List UInt8) (a : Word) : Word :=
  let off := (a - base).toNat
  if h : off + 4 ≤ image.length then
    leWord image[off] image[off + 1] image[off + 2] image[off + 3]
  else 0

end VerifiedFw.Loader
