/-
TRUSTED. Changes to this file need human review.

Address maps for the chips the compiler targets. A wrong entry here makes the
proofs describe a different chip, so each one cites its source.
-/
import VerifiedFw.Compiler.Compile

namespace VerifiedFw.Targets

open VerifiedFw.RiscV VerifiedFw.Compiler

private def inRange (a : Word) (lo hi : Nat) : Bool := lo ≤ a.toNat && a.toNat < hi

/-- QEMU's `virt` board (`qemu-system-riscv32 -machine virt`), from
`hw/riscv/virt.c`: the SiFive test device at `0x100000` ends the run, and a
16550 UART sits at `0x10000000`. With `-bios none`, the reset code jumps to the
start of RAM at `0x80000000`. -/
def qemuVirt : Target where
  platform := {
    isMmio := fun a => inRange a 0x100000 0x101000 || inRange a 0x10000000 0x10000100
  }
  codeBase := 0x80000000
  dataBase := 0x80100000

namespace QemuVirt

/-- Transmit holding register of the UART. A store sends its low byte. -/
def uartTx : Word := 0x10000000

/-- The SiFive test device. Storing `0x5555` stops QEMU with exit status 0. -/
def finisher : Word := 0x100000
def finishPass : Word := 0x5555

end QemuVirt

/-- ESP32-C3, booted with the ROM's direct boot. The ESP32-C3 Technical
Reference Manual's "System and Memory" chapter puts peripherals at
`0x60000000`-`0x600D0FFF` and internal data RAM at `0x3FC80000`-`0x3FCDFFFF`.
In direct boot, the ROM maps flash at `0x42000000` and jumps to offset 8 when
the image starts with the magic word `0xAEDB041D` twice.

Not yet tested on hardware. -/
def esp32c3 : Target where
  platform := { isMmio := fun a => inRange a 0x60000000 0x600D1000 }
  codeBase := 0x42000008
  dataBase := 0x3FC80000

end VerifiedFw.Targets
