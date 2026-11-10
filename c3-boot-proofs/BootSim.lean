import C3BootProofs
import Std.Data.HashMap

/-!
Boots the c3-boot bootloader image on the Lean RV32 model and prints the
ROM calls it makes, for `c3-boot/qemu/boot-lockstep.sh` to compare with the
same boot in QEMU.

Usage: `boot-sim FLASH EFUSE HALT_ADDRESS [OUT_FLASH]`

With `OUT_FLASH`, it writes the flash as the boot left it, to compare with
the flash file QEMU wrote.

It loads the ESP image at flash offset 0 the way the ROM does and jumps to
its entry point. Calls into the ROM functions the bootloader links against
run as hooks: flash reads, writes, and erases act on the flash file, and the
cache and print functions do nothing. eFuse read registers return block 0
of the eFuse file. Each ROM call prints `call ADDRESS ARGS...` with the
arguments it takes: for `ets_printf`, the format string's address and one
argument per conversion. The run
ends with `halt CODE` when the program counter reaches `HALT_ADDRESS`, with
`jump ADDRESS A0` when it leaves the bootloader, or with `trap ADDRESS` if
the model traps, or `fuel ADDRESS` if it runs out of instructions.
-/

open C3.RV32

/-- Internal SRAM through its data-bus addresses; the instruction bus sees
the same bytes 0x700000 higher. -/
def sramBase : Nat := 0x3FC80000
def sramLen : Nat := 0x60000
def iramOffset : Nat := 0x700000
def efuseRead : Nat := 0x6000882C

/-- The bootloader's code region, where the instruction bus fetches it. -/
def codeBase : Nat := 0x403A0000
def codeLen : Nat := 0x24000

structure Sim where
  regs : Array Word
  pc : Word
  sram : ByteArray
  other : Std.HashMap Nat UInt8
  efuse : ByteArray
  /-- Decoded instructions in the code region, by halfword. A store into
  the region clears the entries that could cover the stored byte. -/
  decoded : Array (Option (Instr × Word))

/-- The offset into SRAM of an address, through either bus. -/
@[inline] def sramIndex (n : Nat) : Option Nat :=
  if sramBase ≤ n ∧ n < sramBase + sramLen then some (n - sramBase)
  else if sramBase + iramOffset ≤ n ∧ n < sramBase + iramOffset + sramLen then
    some (n - sramBase - iramOffset)
  else none

instance : Arch Sim where
  getReg s r := s.regs[r.val]!
  setReg s r v := { s with regs := s.regs.set! r.val v }
  getPc s := s.pc
  setPc s v := { s with pc := v }
  read8 s a :=
    let n := a.toNat
    match sramIndex n with
    | some i => BitVec.ofNat 8 (s.sram.get! i).toNat
    | none =>
      if efuseRead ≤ n ∧ n < efuseRead + 24 then BitVec.ofNat 8 (s.efuse.get! (n - efuseRead)).toNat
      else BitVec.ofNat 8 (s.other.getD n 0).toNat
  write8 s a v :=
    let n := a.toNat
    match sramIndex n with
    | some i =>
      let code := i + sramBase + iramOffset
      let decoded :=
        if codeBase ≤ code + 3 ∧ code < codeBase + codeLen then
          let h := (code - codeBase) / 2
          ((s.decoded.set! h none).set! (h - 1) none)
        else s.decoded
      { s with sram := s.sram.set! i v.toNat.toUInt8, decoded := decoded }
    | none => { s with other := s.other.insert n v.toNat.toUInt8 }

def u32At (b : ByteArray) (i : Nat) : Nat :=
  (b.get! i).toNat + 256 * ((b.get! (i + 1)).toNat + 256 * ((b.get! (i + 2)).toNat +
    256 * (b.get! (i + 3)).toNat))

/-- Loads the ESP image at flash offset 0: a 24-byte header with the
segment count at byte 1 and the entry point at byte 4, then each segment's
load address, length, and data. -/
def loadImage (flash : ByteArray) (s : Sim) : Sim := Id.run do
  let count := (flash.get! 1).toNat
  let mut pos := 24
  let mut s := s
  for _ in [0:count] do
    let addr := u32At flash pos
    let len := u32At flash (pos + 4)
    for i in [0:len] do
      s := store8 s (BitVec.ofNat 32 (addr + i)) (BitVec.ofNat 8 (flash.get! (pos + 8 + i)).toNat)
    pos := pos + 8 + len
  pure { s with pc := BitVec.ofNat 32 (u32At flash 4) }

def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def a (s : Sim) (i : Nat) : Word := reg s (regOf (10 + i))

def romPrintf : Nat := 0x40000040
def romErase : Nat := 0x40000128
def romWrite : Nat := 0x4000012C
def romRead : Nat := 0x40000130
def romUnlock : Nat := 0x40000140
def romInvalidate : Nat := 0x400004D8
def romSuspend : Nat := 0x40000524
def romResume : Nat := 0x40000528

def roms : List Nat :=
  [romPrintf, romErase, romWrite, romRead, romUnlock, romInvalidate, romSuspend, romResume]

/-- The C string at `addr`, up to 256 bytes. -/
def cString (s : Sim) (addr : Nat) : List Nat := Id.run do
  let mut out := []
  for i in [0:256] do
    let b := (load8 s (BitVec.ofNat 32 (addr + i))).toNat
    if b == 0 then break
    out := out ++ [b]
  pure out

/-- The number of arguments a format string consumes: one per `%`
conversion, not counting `%%`. -/
def formatArgs : List Nat → Nat
  | 37 :: 37 :: rest => formatArgs rest
  | 37 :: rest => 1 + formatArgs rest
  | _ :: rest => formatArgs rest
  | [] => 0

/-- How many argument registers a ROM call reads. -/
def argCount (fn : Nat) (s : Sim) : Nat :=
  if fn == romPrintf then 1 + formatArgs (cString s (a s 0).toNat)
  else if fn == romRead || fn == romWrite then 3
  else if fn == romErase || fn == romResume then 1
  else 0

/-- Returns from a ROM call with `a0 = result`. -/
def ret (s : Sim) (result : Nat) : Sim :=
  Arch.setPc (writeReg s (regOf 10) (BitVec.ofNat 32 result)) (reg s (regOf 1))

/-- Runs a ROM call's effect on the state and the flash. -/
def romCall (fn : Nat) (s : Sim) (flash : ByteArray) : Sim × ByteArray := Id.run do
  let a0 := (a s 0).toNat
  let a1 := (a s 1).toNat
  let a2 := (a s 2).toNat
  if fn == romRead then
    let mut s := s
    for i in [0:a2] do
      s := store8 s (BitVec.ofNat 32 (a1 + i)) (BitVec.ofNat 8 (flash.get! (a0 + i)).toNat)
    return (ret s 0, flash)
  if fn == romWrite then
    let mut flash := flash
    for i in [0:a2] do
      flash := flash.set! (a0 + i) (load8 s (BitVec.ofNat 32 (a1 + i))).toNat.toUInt8
    return (ret s 0, flash)
  if fn == romErase then
    let mut flash := flash
    for i in [0:4096] do
      flash := flash.set! (a0 * 4096 + i) 0xFF
    return (ret s 0, flash)
  return (ret s 0, flash)

def inBootloader (pc : Nat) : Bool := codeBase ≤ pc && pc < codeBase + codeLen

/-- `step`, with the decode of each code-region instruction cached. -/
def cachedStep (s : Sim) : Option Sim :=
  let pc := s.pc.toNat
  if inBootloader pc then
    let h := (pc - codeBase) / 2
    match s.decoded[h]! with
    | some (i, len) => exec s i len
    | none =>
      match fetch s with
      | some (i, len) => exec { s with decoded := s.decoded.set! h (some (i, len)) } i len
      | none => none
  else step s

/-- The most instructions a boot may run before the simulator gives up. -/
def fuel : Nat := 2_000_000_000

partial def run (halt : Nat) (s : Sim) (flash : ByteArray) (count : Nat)
    (out : IO.FS.Stream) : IO (Nat × ByteArray) := do
  let pc := s.pc.toNat
  if roms.contains pc then
    let args := (List.range (argCount pc s)).map fun i => " " ++ hex (a s i).toNat
    out.putStrLn s!"call {hex pc}{String.join args}"
    let (s, flash) := romCall pc s flash
    run halt s flash count out
  else if pc == halt then
    out.putStrLn s!"halt {hex (a s 0).toNat}"
    pure (count, flash)
  else if !inBootloader pc then
    out.putStrLn s!"jump {hex pc} {hex (a s 0).toNat}"
    pure (count, flash)
  else if count ≥ fuel then
    out.putStrLn s!"fuel {hex pc}"
    pure (count, flash)
  else
    match cachedStep s with
    | some s' => run halt s' flash (count + 1) out
    | none =>
      out.putStrLn s!"trap {hex pc}"
      pure (count, flash)

def parseHexNat (s : String) : Option Nat :=
  (s.toList.dropWhile (· == '0') |>.drop 0).foldlM (fun acc c =>
    if '0' ≤ c && c ≤ '9' then some (16 * acc + (c.toNat - '0'.toNat))
    else if 'a' ≤ c && c ≤ 'f' then some (16 * acc + (c.toNat - 'a'.toNat + 10))
    else if c == 'x' then some 0
    else none) 0

def main (args : List String) : IO UInt32 := do
  let (flashPath, efusePath, haltHex, outPath) ← match args with
    | [f, e, h] => pure (f, e, h, none)
    | [f, e, h, o] => pure (f, e, h, some o)
    | _ => do IO.eprintln "usage: boot-sim FLASH EFUSE HALT_ADDRESS [OUT_FLASH]"; return 2
  let some halt := parseHexNat haltHex | IO.eprintln "bad halt address"; return 2
  let flash ← IO.FS.readBinFile flashPath
  let efuse ← IO.FS.readBinFile efusePath
  let s0 : Sim := {
    regs := Array.replicate 32 0
    pc := 0
    sram := ByteArray.mk (Array.replicate sramLen 0)
    other := {}
    efuse := efuse
    decoded := Array.replicate (codeLen / 2) none }
  let s := loadImage flash s0
  let (n, flash) ← run halt s flash 0 (← IO.getStdout)
  if let some o := outPath then IO.FS.writeBinFile o flash
  IO.eprintln s!"boot-sim: {n} instructions"
  return 0
