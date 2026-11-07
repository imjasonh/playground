/-
Turning compiled code into the bytes that go on the chip.
-/
import VerifiedFw.Targets

namespace VerifiedFw.Image

open VerifiedFw.RiscV VerifiedFw.Compiler VerifiedFw.Lang

/-- RISC-V is little-endian: least significant byte first. -/
def wordBytes (w : Word) : List UInt8 :=
  [0, 8, 16, 24].map fun s => (w >>> s).toNat.toUInt8

def codeBytes (code : List Instr) : List UInt8 :=
  code.flatMap fun i => wordBytes (encode i)

/-- A raw image for QEMU's `virt` board, loaded at `0x80000000`. -/
def qemuVirt (p : Program) : List UInt8 :=
  codeBytes (compile Targets.qemuVirt p)

/-- An ESP32-C3 direct-boot image, written to flash offset 0. -/
def esp32c3 (p : Program) : List UInt8 :=
  wordBytes 0xAEDB041D ++ wordBytes 0xAEDB041D ++ codeBytes (compile Targets.esp32c3 p)

end VerifiedFw.Image
