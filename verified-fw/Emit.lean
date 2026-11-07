/-
Writes the example images to a directory (default `out`):

* `qemu-counter.bin`: raw image for QEMU's `virt` board.
* `qemu-counter.expected`: what the UART must print, from the source semantics.
* `esp32c3-blinky.bin`: direct-boot image for flash offset 0.
* `encode-vectors.txt`: one instruction per line, checked against GNU objdump.
-/
import VerifiedFw

open VerifiedFw VerifiedFw.RiscV VerifiedFw.Examples

def writeBytes (path : System.FilePath) (bytes : List UInt8) : IO Unit :=
  IO.FS.writeBinFile path (ByteArray.mk bytes.toArray)

/-- Instructions with operands at the edges of their fields, in the syntax
GNU objdump prints, so a mismatch shows up as a text diff. -/
def vectors : List (Instr × String) :=
  [(.lui 1 0xFFFFF, "lui\tra,0xfffff"),
   (.addi 31 2 0x800, "addi\tt6,sp,-2048"),
   (.addi 5 5 0x7FF, "addi\tt0,t0,2047"),
   (.add 10 11 12, "add\ta0,a1,a2"),
   (.sub 31 30 29, "sub\tt6,t5,t4"),
   (.and 1 2 3, "and\tra,sp,gp"),
   (.or 4 5 6, "or\ttp,t0,t1"),
   (.xor 7 8 9, "xor\tt2,s0,s1"),
   (.sll 10 11 12, "sll\ta0,a1,a2"),
   (.srl 13 14 15, "srl\ta3,a4,a5"),
   (.sltu 16 17 18, "sltu\ta6,a7,s2"),
   (.lw 5 3 0x7FC, "lw\tt0,2044(gp)"),
   (.lw 6 3 0x800, "lw\tt1,-2048(gp)"),
   (.sw 5 3 0x7FC, "sw\tt0,2044(gp)"),
   (.sw 31 30 0x801, "sw\tt6,-2047(t5)"),
   (.beq 10 11 0x7FF, "beq\ta0,a1,0x103a"),
   (.bne 5 0 4, "bne\tt0,zero,0x48"),
   (.jal 1 0x7FFFF, "jal\tra,0x100042"),
   (.jal 0 (Compiler.jumpBy (-18)), "jal\tzero,0x0")]

def main (args : List String) : IO Unit := do
  let dir : System.FilePath := args.headD "out"
  IO.FS.createDirAll dir
  writeBytes (dir / "qemu-counter.bin") (Image.qemuVirt counter)
  IO.FS.writeFile (dir / "qemu-counter.expected") (uartText counter.trace)
  writeBytes (dir / "esp32c3-blinky.bin") (Image.esp32c3 Blinky.blinky)
  writeBytes (dir / "encode-vectors.bin") (Image.codeBytes (vectors.map (·.1)))
  IO.FS.writeFile (dir / "encode-vectors.txt")
    (String.intercalate "\n" (vectors.map (·.2)) ++ "\n")
