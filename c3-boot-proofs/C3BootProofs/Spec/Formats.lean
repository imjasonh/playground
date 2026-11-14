import C3BootProofs.Spec.BootState

/-!
# Byte formats

Executable decoders for the boot-state record, the slot manifest, and the
image header, following `c3-boot/docs/formats.md` and `c3_verify::bootstate`,
`manifest`, and `image`. Bytes are natural numbers below 256, and every
32-bit sum that Rust computes with `checked_add` is checked against `2 ^ 32`
here.
-/

namespace C3

/-- Bytes, each below 256. -/
abbrev Bytes := List Nat

def u32Limit : Nat := 2 ^ 32

/-- Continues only when `b` holds. -/
def require (b : Bool) : Option Unit := if b then some () else none

@[simp] theorem require_eq_some {b : Bool} {u : Unit} : require b = some u ↔ b = true := by
  unfold require
  split <;> simp_all

/-- Reads one byte. -/
def readU8 : Bytes → Option (Nat × Bytes)
  | b :: rest => some (b, rest)
  | [] => none

/-- Reads a little-endian 16-bit integer. -/
def readU16 : Bytes → Option (Nat × Bytes)
  | a :: b :: rest => some (a + 256 * b, rest)
  | _ => none

/-- Reads a little-endian 32-bit integer. -/
def readU32 : Bytes → Option (Nat × Bytes)
  | a :: b :: c :: d :: rest => some (a + 256 * (b + 256 * (c + 256 * d)), rest)
  | _ => none

/-- Reads `n` bytes that must all be zero. -/
def readZeros (n : Nat) (bytes : Bytes) : Option Bytes :=
  if bytes.length < n then none
  else if (bytes.take n).all (· == 0) then some (bytes.drop n) else none

/-- Reads the given bytes exactly. -/
def readExpect (want : Bytes) (bytes : Bytes) : Option Bytes :=
  if bytes.take want.length == want && want.length ≤ bytes.length then
    some (bytes.drop want.length)
  else none

/-- The magic numbers, as ASCII bytes. Lean's `String` functions depend on
`Classical.choice`, which the axiom audit forbids, so these are spelled out. -/
def magicRecord : Bytes := [0x43, 0x33, 0x42, 0x53]
def magicManifest : Bytes := [0x43, 0x33, 0x53, 0x4C]
def magicImage : Bytes := [0x43, 0x33, 0x49, 0x4D]

/-- Reads a magic number and format version 1. -/
def readHeader (magic : Bytes) (bytes : Bytes) : Option Bytes := do
  let rest ← readExpect magic bytes
  let (version, rest) ← readU16 rest
  require (version == 1)
  pure rest

/-! ## Boot-state record -/

/-- CRC-32 with the IEEE 802.3 polynomial, as zlib computes it. -/
def crc32 (bytes : Bytes) : Nat :=
  let step (c : Nat) : Nat := if c % 2 == 1 then (c / 2) ^^^ 0xEDB88320 else c / 2
  let crc := bytes.foldl (fun c b => (List.range 8).foldl (fun c _ => step c) (c ^^^ b)) 0xFFFFFFFF
  crc ^^^ 0xFFFFFFFF

def slotOfByte : Nat → Option Slot
  | 0 => some .a
  | 1 => some .b
  | _ => none

/-- Decodes one 32-byte copy of the boot-state record. -/
def decodeRecord (bytes : Bytes) : Option State := do
  require (bytes.length == 32)
  let body := bytes.take 28
  let (crc, _) ← readU32 (bytes.drop 28)
  require (crc32 body == crc)
  let rest ← readHeader magicRecord body
  let rest ← readZeros 2 rest
  let (generation, rest) ← readU32 rest
  let (preferredByte, rest) ← readU8 rest
  let preferred ← slotOfByte preferredByte
  let (trialByte, rest) ← readU8 rest
  let (bootsLeft, rest) ← readU8 rest
  let (confirmed, rest) ← readU8 rest
  let rest ← readZeros 12 rest
  require rest.isEmpty
  require (bootsLeft ≤ 3 && confirmed &&& 0xFC == 0)
  let trial ← if trialByte == 0xFF then
      (if bootsLeft == 0 then some none else none)
    else (slotOfByte trialByte).map fun s => some ⟨s, bootsLeft⟩
  pure ⟨generation, preferred, trial, confirmed⟩

/-- Which copy holds the state in use, or `none` for the default state. -/
def readRecords (a b : Bytes) : State × Option Slot :=
  match decodeRecord a, decodeRecord b with
  | some sa, some sb => if sa.generation < sb.generation then (sb, some .b) else (sa, some .a)
  | some sa, none => (sa, some .a)
  | none, some sb => (sb, some .b)
  | none, none => (State.default, none)

/-! ## Slot manifest -/

structure Part where
  offset : Nat
  length : Nat
  deriving DecidableEq, Repr

structure Manifest where
  image : Part
  bundle : Part
  chain : Part
  blob : Part
  deriving DecidableEq, Repr

def slotSize : Nat := 0x1E0000
def imageOffset : Nat := 0x10000

def readPart (lo hi : Nat) (bytes : Bytes) : Option (Part × Bytes) := do
  let (offset, rest) ← readU32 bytes
  let (length, rest) ← readU32 rest
  require (lo ≤ length && length ≤ hi)
  pure (⟨offset, length⟩, rest)

def Part.endOf (p : Part) : Nat := p.offset + p.length

/-- Decodes a 40-byte slot manifest. -/
def decodeManifest (bytes : Bytes) : Option Manifest := do
  let rest ← readHeader magicManifest bytes
  let rest ← readZeros 2 rest
  let (image, rest) ← readPart 37 0x1D0000 rest
  let (bundle, rest) ← readPart 49 16384 rest
  let (chain, rest) ← readPart 8 2048 rest
  let (blob, rest) ← readPart 443 4096 rest
  require rest.isEmpty
  require (image.offset == imageOffset)
  require ([image, bundle, chain, blob].all (·.endOf < u32Limit))
  require (image.endOf ≤ bundle.offset && bundle.endOf ≤ chain.offset &&
    chain.endOf ≤ blob.offset && blob.endOf ≤ slotSize)
  pure ⟨image, bundle, chain, blob⟩

/-! ## Image header -/

inductive SegmentKind where
  | flashCode
  | flashData
  | ramCode
  | ramData
  deriving DecidableEq, Repr

def SegmentKind.ofByte : Nat → Option SegmentKind
  | 1 => some .flashCode
  | 2 => some .flashData
  | 3 => some .ramCode
  | 4 => some .ramData
  | _ => none

/-- The addresses a segment of this kind may occupy, `start` to `end`
exclusive. -/
def SegmentKind.region : SegmentKind → Nat × Nat
  | .flashCode => (0x42000000, 0x42800000)
  | .flashData => (0x3C000000, 0x3C800000)
  | .ramCode => (0x40380000, 0x403A0000)
  | .ramData => (0x3FC80000, 0x3FCA0000)

def SegmentKind.isFlash : SegmentKind → Bool
  | .flashCode | .flashData => true
  | _ => false

def SegmentKind.isExecutable : SegmentKind → Bool
  | .flashCode | .ramCode => true
  | _ => false

structure Segment where
  kind : SegmentKind
  address : Nat
  offset : Nat
  length : Nat
  deriving DecidableEq, Repr

structure ImageHeader where
  securityVersion : Nat
  entryPoint : Nat
  imageLength : Nat
  segments : List Segment
  deriving DecidableEq, Repr

def flashPage : Nat := 0x10000

def readSegment (bytes : Bytes) : Option (Segment × Bytes) := do
  let (kindByte, rest) ← readU8 bytes
  let kind ← SegmentKind.ofByte kindByte
  let rest ← readZeros 3 rest
  let (address, rest) ← readU32 rest
  let (offset, rest) ← readU32 rest
  let (length, rest) ← readU32 rest
  pure (⟨kind, address, offset, length⟩, rest)

def readSegments : Nat → Bytes → Option (List Segment)
  | 0, _ => some []
  | n + 1, bytes => do
    let (s, rest) ← readSegment bytes
    let more ← readSegments n rest
    pure (s :: more)

/-- The rules for one segment on its own. -/
def segmentOk (imageLength : Nat) (s : Segment) : Bool :=
  let (lo, hi) := s.kind.region
  0 < s.length && s.offset + s.length < u32Limit && s.offset + s.length ≤ imageLength &&
    s.address + s.length < u32Limit && lo ≤ s.address && s.address + s.length ≤ hi &&
    (if s.kind.isFlash then
      s.offset % flashPage == 0 && s.address % flashPage == 0 && s.length % flashPage == 0
    else s.offset % 4 == 0 && s.address % 4 == 0 && s.length % 4 == 0)

/-- Each segment's data starts at or after the end of the previous one's,
starting after the table, and the last ends at `imageLength`. -/
def segmentsOrdered (tableEnd imageLength : Nat) : List Segment → Bool
  | [] => tableEnd == imageLength
  | s :: rest => tableEnd ≤ s.offset && segmentsOrdered (s.offset + s.length) imageLength rest

/-- The address space a segment occupies, and its start in that space: the
two flash windows share the cache's linear space, and RAM code uses its
data-bus alias. -/
def Segment.physical (s : Segment) : Bool × Nat :=
  match s.kind with
  | .flashCode => (true, s.address - 0x42000000)
  | .flashData => (true, s.address - 0x3C000000)
  | .ramData => (false, s.address)
  | .ramCode => (false, s.address - 0x700000)

def Segment.overlaps (a b : Segment) : Bool :=
  let (sa, xa) := a.physical
  let (sb, xb) := b.physical
  sa == sb && xa < xb + b.length && xb < xa + a.length

def noOverlaps : List Segment → Bool
  | [] => true
  | s :: rest => rest.all (fun t => !s.overlaps t) && noOverlaps rest

/-- Decodes and checks an image header and segment table. Bytes after the
table are ignored. -/
def decodeImageHeader (bytes : Bytes) (imageLength : Nat) : Option ImageHeader := do
  let rest ← readHeader magicImage bytes
  let (chip, rest) ← readU16 rest
  require (chip == 5)
  let (sv, rest) ← readU8 rest
  require (sv ≤ 16)
  let (count, rest) ← readU8 rest
  require (0 < count && count ≤ 16)
  let rest ← readZeros 2 rest
  let (entry, rest) ← readU32 rest
  let (length, rest) ← readU32 rest
  require (length == imageLength)
  let segments ← readSegments count rest
  require (segments.all (segmentOk imageLength))
  require (segmentsOrdered (20 + 16 * count) imageLength segments)
  require (noOverlaps segments)
  require (entry % 2 == 0 && segments.any fun s =>
    s.kind.isExecutable && s.address ≤ entry && entry < s.address + s.length)
  pure ⟨sv, entry, imageLength, segments⟩

end C3
