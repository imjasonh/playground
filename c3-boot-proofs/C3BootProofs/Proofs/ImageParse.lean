import C3BootProofs.Proofs.Block
import C3BootProofs.Proofs.ImageHelpers

/-!
# `c3_verify::image::parse`, as compiled

`image::parse` saves `ra` and `s0` through `s11` in a 0x160-byte frame and
returns through one epilogue, at offset 0xC0, on every path: it points `a0`
at the frame's top quarter, calls an outlined helper that loads `ra` and `s0`
through `s6` relative to `a0`, loads `s7` through `s11` itself, frees the
frame, and returns. `image_epilogue` proves that epilogue.
-/

namespace C3.RV32

open C3.ImageV0

set_option maxRecDepth 20000

theorem ip_at_c0 : fetchRel imageParseCode 0xC0 = some (.aluImm .add a0 sp 0x100, 2) := by decide
theorem ip_at_c2 : fetchRel imageParseCode 0xC2 = some (.auipc t0 0x16000, 4) := by decide
theorem ip_at_c6 : fetchRel imageParseCode 0xC6 = some (.jalr t0 t0 0x340, 4) := by decide
theorem ip_at_e0 : fetchRel imageParseCode 0xE0 = some (.jalr x0 ra 0x0, 2) := by decide
theorem ir_at_1c : fetchRel imageRestoreCode 0x1C = some (.jalr x0 t0 0x0, 2) := by decide

/-- The helper's loads: `ra` and `s0` through `s6`, relative to `a0`. -/
def irBlock : List BInstr :=
  [.lw ra a0 0x5C, .lw s0 a0 0x58, .lw s1 a0 0x54, .lw s2 a0 0x50, .lw s3 a0 0x4C,
   .lw s4 a0 0x48, .lw s5 a0 0x44, .lw s6 a0 0x40]

/-- After the helper: `s7` through `s11`, then the frame freed. -/
def ipTailBlock : List BInstr :=
  [.lw s7 a0 0x3C, .lw s8 a0 0x38, .lw s9 a0 0x34, .lw s10 a0 0x30, .lw s11 a0 0x2C,
   .aluImm .add sp sp 0x160]

theorem irBlock_end : blockEnd imageRestoreCode 0 irBlock = some 0x1C := by decide
theorem ipTailBlock_end : blockEnd imageParseCode 0xCA ipTailBlock = some 0xE0 := by decide

/-! ## What the compiled function decides

The reader reads the `len` bytes at `ptr`; each function takes its position
and returns the error byte the compiled code reports, or what it read and the
new position. -/

section Spec

variable (M : Word → BitVec 8) (ptr len : Word)

def rdB (n pos : Word) : Except (BitVec 8) (Word × Word) :=
  match bytesResult ptr len pos n with
  | none => .error 0
  | some r => .ok r

def rdU8 (pos : Word) : Except (BitVec 8) (BitVec 8 × Word) := do
  let (p, e) ← rdB ptr len 1 pos
  pure (M p, e)

def rdU32 (pos : Word) : Except (BitVec 8) (Word × Word) := do
  let (p, e) ← rdB ptr len 4 pos
  pure (memLoad32 M p, e)

/-- A 16-bit little-endian value, as `Reader::u16` leaves it in the high half
of `a0`, shifted down. -/
def rdU16 (pos : Word) : Except (BitVec 8) (Word × Word) := do
  let (p, e) ← rdB ptr len 2 pos
  pure (((M (p + 1)).zeroExtend 32 <<< 24 ||| (M p).zeroExtend 32 <<< 16 : Word) >>> 16, e)

def rdRes (n pos : Word) : Except (BitVec 8) Word := do
  let (p, e) ← rdB ptr len n pos
  if allZero M p n.toNat then pure e else throw 4

def rdMagic (k pos : Word) : Except (BitVec 8) Word := do
  let (p, e) ← rdB ptr len 4 pos
  if memLoad32 M p == k then pure e else throw 2

def rdVer1 (pos : Word) : Except (BitVec 8) Word := do
  let (v, e) ← rdU16 M ptr len pos
  if v == 1 then pure e else throw 3

/-- A segment as the compiled code keeps it: the kind's Rust discriminant (0
flash code, 1 flash data, 2 RAM code, 3 RAM data), address, offset, length. -/
structure SegW where
  kind : BitVec 8
  addr : Word
  off : Word
  len : Word

/-- The region table entries for a kind, as the image's data holds them. -/
def regionLo (k : BitVec 8) : Word :=
  if k = 0 then 0x42000000 else if k = 1 then 0x3C000000 else if k = 2 then 0x40380000 else 0x3FC80000

def regionHi (k : BitVec 8) : Word :=
  if k = 0 then 0x42800000 else if k = 1 then 0x3C800000 else if k = 2 then 0x403A0000 else 0x3FCA0000

def segL (pos : Word) (k : BitVec 8) (a o : Word) : Except (BitVec 8) (SegW × Word) := do
  let (l, pos) ← rdU32 M ptr len pos
  pure (⟨k, a, o, l⟩, pos)

def segO (pos : Word) (k : BitVec 8) (a : Word) : Except (BitVec 8) (SegW × Word) := do
  let (o, pos) ← rdU32 M ptr len pos
  segL M ptr len pos k a o

def segA (pos : Word) (k : BitVec 8) : Except (BitVec 8) (SegW × Word) := do
  let (a, pos) ← rdU32 M ptr len pos
  segO M ptr len pos k a

/-- `read_segment`: the kind byte, three zero bytes, and the address, offset,
and length. -/
def readSegW (pos : Word) : Except (BitVec 8) (SegW × Word) := do
  let (b, pos) ← rdU8 M ptr len pos
  let k := b - 1
  if (3 : BitVec 8).ult k then throw 9
  let pos ← rdRes M ptr len 3 pos
  segA M ptr len pos k

/-- The alignment checks: flash segments (kinds 0 and 1) map whole 64 KiB
MMU pages, and RAM segments (kinds 2 and 3) are word aligned. -/
def alignOk (s : SegW) : Bool :=
  let x := s.addr ||| s.off
  (if (x &&& 0xFFFF) != 0 then !s.kind.ult 2 else !(s.kind.ult 2 && (s.len &&& 0xFFFF) != 0)) &&
  (if (x &&& 3) != 0 then !(1 : BitVec 8).ult s.kind
   else !((1 : BitVec 8).ult s.kind && (s.len &&& 3) != 0))

/-- `check_segment` and the order check, in the compiled code's order; the
new previous end. -/
def checkSegW (ilen prev : Word) (s : SegW) : Except (BitVec 8) Word := do
  if s.len == 0 then throw 9
  let e := s.off + s.len
  if e.ult s.off then throw 6
  if ilen.ult e then throw 9
  if (regionHi s.kind).ult (s.addr + s.len) then throw 9
  if (s.addr + s.len).ult s.addr then throw 9
  if s.addr.ult (regionLo s.kind) then throw 9
  if !alignOk s then throw 9
  if s.off.ult prev then throw 9
  pure e

/-- The segment loop: `n` segments read and checked, the position, and the
previous end. -/
def readSegsW (ilen : Word) : Nat → Word → Word → Except (BitVec 8) (List SegW × Word × Word)
  | 0, pos, prev => pure ([], pos, prev)
  | n + 1, pos, prev => do
    let (s, pos) ← readSegW M ptr len pos
    let prev ← checkSegW ilen prev s
    let (rest, pos, prev) ← readSegsW ilen n pos prev
    pure (s :: rest, pos, prev)

end Spec

def physW (s : SegW) : Except (BitVec 8) (BitVec 8 × Word) :=
  match physResult s.kind s.addr with
  | none => throw 9
  | some r => pure r

/-- `ranges_overlap` for `a` at `xa` and `b` at `xb` in one address space. -/
def pairChk (a : SegW) (xa : Word) (b : SegW) (xb : Word) : Except (BitVec 8) Unit :=
  if (a.len + xa).ult a.len then .error 10
  else if (b.len + xb).ult b.len then .error 10
  else if xa.ult (b.len + xb) && xb.ult (a.len + xa) then .error 10
  else .ok ()

/-- `ranges_overlap` for `a`, already placed at `xa` in space `sa`, and `b`. -/
def pairW (a : SegW) (sa : BitVec 8) (xa : Word) (b : SegW) : Except (BitVec 8) Unit :=
  match physResult b.kind b.addr with
  | none => .error 9
  | some (sb, xb) => if sa = sb then pairChk a xa b xb else .ok ()

def innerW (a : SegW) (sa : BitVec 8) (xa : Word) : List SegW → Except (BitVec 8) Unit
  | [] => pure ()
  | b :: bs => do pairW a sa xa b; innerW a sa xa bs

/-- The overlap check: each segment against every later one. -/
def overlapW : List SegW → Except (BitVec 8) Unit
  | [] => pure ()
  | a :: rest => do
    let (sa, xa) ← physW a
    innerW a sa xa rest
    overlapW rest

/-- Some executable segment holds the entry point. -/
def entryIn (entry : Word) : List SegW → Bool
  | [] => false
  | s :: rest => ((s.kind &&& 1) == 0 && !entry.ult s.addr && (entry - s.addr).ult s.len) || entryIn entry rest

def entryW (entry : Word) (segs : List SegW) : Except (BitVec 8) Unit :=
  if (entry &&& 1) != 0 then throw 11 else if entryIn entry segs then pure () else throw 11

/-- The header's image length, which must be `ilen`. -/
def hdrLn (M : Word → BitVec 8) (ptr len ilen : Word) (sv cnt : BitVec 8) (entry pos : Word) :
    Except (BitVec 8) (BitVec 8 × BitVec 8 × Word × Word) := do
  let (ln, pos) ← rdU32 M ptr len pos
  if ln != ilen then throw 7
  pure (sv, cnt, entry, pos)

/-- The header from the entry point on. -/
def hdrLen (M : Word → BitVec 8) (ptr len ilen : Word) (sv cnt : BitVec 8) (pos : Word) :
    Except (BitVec 8) (BitVec 8 × BitVec 8 × Word × Word) := do
  let (entry, pos) ← rdU32 M ptr len pos
  hdrLn M ptr len ilen sv cnt entry pos

/-- The header from the segment count on. -/
def hdrCnt (M : Word → BitVec 8) (ptr len ilen : Word) (sv : BitVec 8) (pos : Word) :
    Except (BitVec 8) (BitVec 8 × BitVec 8 × Word × Word) := do
  let (cnt, pos) ← rdU8 M ptr len pos
  if cnt.toNat = 0 ∨ 16 < cnt.toNat then throw 5
  let pos ← rdRes M ptr len 2 pos
  hdrLen M ptr len ilen sv cnt pos

/-- The fixed header, through the image-length check: the security version,
the segment count, the entry point, and the reader's position after it. -/
def hdrSv (M : Word → BitVec 8) (ptr len ilen : Word) (pos : Word) :
    Except (BitVec 8) (BitVec 8 × BitVec 8 × Word × Word) := do
  let (sv, pos) ← rdU8 M ptr len pos
  if 16 < sv.toNat then throw 5
  hdrCnt M ptr len ilen sv pos

def hdrChip (M : Word → BitVec 8) (ptr len ilen : Word) (pos : Word) :
    Except (BitVec 8) (BitVec 8 × BitVec 8 × Word × Word) := do
  let (chip, pos) ← rdU16 M ptr len pos
  if chip != 5 then throw 8
  hdrSv M ptr len ilen pos

def hdrW (M : Word → BitVec 8) (ptr len ilen : Word) :
    Except (BitVec 8) (BitVec 8 × BitVec 8 × Word × Word) := do
  let pos ← rdMagic M ptr len 0x4D493343 0
  let pos ← rdVer1 M ptr len pos
  hdrChip M ptr len ilen pos

/-- **What the compiled `image::parse` decides** for the `len` bytes at `ptr`
and an image of `ilen` bytes: the error byte, or the security version, entry
point, segment count, and segments. -/
def imgW (M : Word → BitVec 8) (ptr len ilen : Word) :
    Except (BitVec 8) (BitVec 8 × Word × BitVec 8 × List SegW) := do
  let (sv, cnt, entry, pos) ← hdrW M ptr len ilen
  let (segs, _, prev) ← readSegsW M ptr len ilen cnt.toNat pos (cnt.zeroExtend 32 <<< 4 + 0x14)
  if prev != ilen then throw 9
  overlapW segs
  entryW entry segs
  pure (sv, entry, cnt, segs)

/-! ## Layout -/

/-- The code window: from `Reader::magic`, the lowest function `image::parse`
reaches, to the end of `memcpy`'s body, the highest. -/
abbrev ipWindow (P : Word) : Word := P + 0xFFFFFD52

abbrev ipWindowLen : Nat := 0x16D04

/-- The functions `image::parse` runs, and the region tables it reads, where
the image puts them. -/
structure ICode (M : Word → BitVec 8) (P : Word) : Prop where
  parse : CodeIn M P imageParseCode
  restore : CodeIn M (P + 0x16402) imageRestoreCode
  magic : CodeIn M (P + 0xFFFFFD52) readerMagicCode
  load : CodeIn M (P + 0x16556) magicLoadCode
  version : CodeIn M (P + 0xFFFFFD94) readerVersion1Code
  u8 : CodeIn M (P + 0xFFFFFDBE) readerU8Code
  reserved : CodeIn M (P + 0xFFFFFDF8) readerReservedCode
  bytes : CodeIn M (P + 0xFFFFFE94) readerBytesCode
  u16 : CodeIn M (P + 0xFFFFFEBA) readerU16Code
  array4 : CodeIn M (P + 0xFFFFFEFE) readerArray4Code
  u32 : CodeIn M (P + 0x420) readerU32Code
  physical : CodeIn M (P + 0x470) segmentPhysicalCode
  stub : CodeIn M (P + 0x168C8) memcpyStubCode
  body : CodeIn M (P + 0x168D0) memcpyBodyCode
  ends : CodeIn M 0x3FCC5240 regionEndsData
  starts : CodeIn M 0x3FCC5250 regionStartsData

theorem ip_wq (P x : Word) (c : Nat) (h : x = 0xFFFFFD52 + BitVec.ofNat 32 c) :
    P + x = ipWindow P + BitVec.ofNat 32 c := by rw [h, ← BitVec.add_assoc]

theorem ip_wP (P : Word) : P = ipWindow P + BitVec.ofNat 32 0x2AE := by
  show P = P + 0xFFFFFD52 + BitVec.ofNat 32 0x2AE
  rw [BitVec.add_assoc, show (0xFFFFFD52 : Word) + BitVec.ofNat 32 0x2AE = 0 from rfl]
  exact (BitVec.add_zero P).symm

theorem CodeIn.of_ipWindow {M M' : Word → BitVec 8} {P b : Word} {code : List Nat} (c : Nat)
    (hb : b = ipWindow P + BitVec.ofNat 32 c) (hl : c + code.length ≤ ipWindowLen)
    (hc : CodeIn M b code)
    (h : ∀ k, k < ipWindowLen → M' (ipWindow P + BitVec.ofNat 32 k) = M (ipWindow P + BitVec.ofNat 32 k)) :
    CodeIn M' b code := fun i hi => by
  have e : b + BitVec.ofNat 32 i = ipWindow P + BitVec.ofNat 32 (c + i) := by rw [hb, add_ofNat_assoc]
  rw [e, h _ (by omega), ← e]; exact hc i hi

theorem CodeIn.of_same {M M' : Word → BitVec 8} {b : Word} {code : List Nat} (hc : CodeIn M b code)
    (h : ∀ i, i < code.length → M' (b + BitVec.ofNat 32 i) = M (b + BitVec.ofNat 32 i)) :
    CodeIn M' b code := fun i hi => by rw [h i hi]; exact hc i hi

/-- `ICode` holds in any memory that agrees on the code window and the tables. -/
theorem ICode.of_agree {M M' : Word → BitVec 8} {P : Word} (hc : ICode M P)
    (h : ∀ k, k < ipWindowLen → M' (ipWindow P + BitVec.ofNat 32 k) = M (ipWindow P + BitVec.ofNat 32 k))
    (ht : ∀ k, k < 32 → M' (0x3FCC5240 + BitVec.ofNat 32 k) = M (0x3FCC5240 + BitVec.ofNat 32 k)) :
    ICode M' P where
  parse := hc.parse.of_ipWindow 0x2AE (ip_wP P) (by decide) h
  restore := hc.restore.of_ipWindow 0x166B0 (ip_wq P _ _ (by decide)) (by decide) h
  magic := hc.magic.of_ipWindow 0 (ip_wq P _ _ (by decide)) (by decide) h
  load := hc.load.of_ipWindow 0x16804 (ip_wq P _ _ (by decide)) (by decide) h
  version := hc.version.of_ipWindow 0x42 (ip_wq P _ _ (by decide)) (by decide) h
  u8 := hc.u8.of_ipWindow 0x6C (ip_wq P _ _ (by decide)) (by decide) h
  reserved := hc.reserved.of_ipWindow 0xA6 (ip_wq P _ _ (by decide)) (by decide) h
  bytes := hc.bytes.of_ipWindow 0x142 (ip_wq P _ _ (by decide)) (by decide) h
  u16 := hc.u16.of_ipWindow 0x168 (ip_wq P _ _ (by decide)) (by decide) h
  array4 := hc.array4.of_ipWindow 0x1AC (ip_wq P _ _ (by decide)) (by decide) h
  u32 := hc.u32.of_ipWindow 0x6CE (ip_wq P _ _ (by decide)) (by decide) h
  physical := hc.physical.of_ipWindow 0x71E (ip_wq P _ _ (by decide)) (by decide) h
  stub := hc.stub.of_ipWindow 0x16B76 (ip_wq P _ _ (by decide)) (by decide) h
  body := hc.body.of_ipWindow 0x16B7E (ip_wq P _ _ (by decide)) (by decide) h
  ends := hc.ends.of_same fun i hi => ht i (by simp [regionEndsData] at hi; omega)
  starts := hc.starts.of_same fun i hi => by
    have := ht (16 + i) (by simp [regionStartsData] at hi; omega)
    rwa [← add_ofNat_assoc] at this

/-- `image::parse`'s layout: the 0x190 bytes of stack at `R` (its 0x160-byte
frame at `G = R + 0x30` and 48 bytes for its callees), the code window and
the region tables, the header buffer of `len` bytes at `ptr`, and the
0x110-byte result at `out`. -/
structure IEnv (P R G ptr len out : Word) : Prop where
  hP : P.toNat % 2 = 0
  hRG : G = R + BitVec.ofNat 32 0x30
  hG : G.toNat % 4 = 0
  hout : out.toNat % 4 = 0
  hwrap : out.toNat + 0x110 ≤ 2 ^ 32
  hbuf : ptr ≠ 0 ∧ ptr.toNat + len.toNat ≤ 2 ^ 32
  hSW : Sep R 0x190 (ipWindow P) ipWindowLen
  hST : Sep R 0x190 0x3FCC5240 32
  hOW : Sep out 0x110 (ipWindow P) ipWindowLen
  hOS : Sep out 0x110 R 0x190
  hBS : Sep ptr len.toNat R 0x190
  /-- The stack region doesn't wrap past address 0, so no pointer into it is null. -/
  hRw : R.toNat + 0x190 ≤ 2 ^ 32

namespace IEnv

variable {P R G ptr len out : Word}

theorem g_ofs (env : IEnv P R G ptr len out) (c : Nat) :
    G + BitVec.ofNat 32 c = R + BitVec.ofNat 32 (0x30 + c) := by
  rw [env.hRG, add_ofNat_assoc]

/-- No address in the frame above `G` is null. -/
theorem g_ne0 (env : IEnv P R G ptr len out) (c : Nat) (h0 : 0 < c) (hc : c < 0x160) :
    G + BitVec.ofNat 32 c ≠ 0 := fun e => by
  have hw := env.hRw
  have h := congrArg BitVec.toNat e
  rw [env.g_ofs, BitVec.toNat_add, BitVec.toNat_ofNat] at h
  have : (0 : Word).toNat = 0 := rfl
  rw [this, Nat.mod_eq_of_lt (by omega : 0x30 + c < 2 ^ 32), Nat.mod_eq_of_lt (by omega)] at h
  omega

theorem stack_code (env : IEnv P R G ptr len out) (c n : Nat) (hn : c + n ≤ 0x190) (d l : Nat)
    (hl : d + l ≤ ipWindowLen) : Sep (R + BitVec.ofNat 32 c) n (ipWindow P + BitVec.ofNat 32 d) l :=
  (env.hSW.sub (c := c) (l := n) hn).subR (c := d) (l := l) hl

theorem stack_buf (env : IEnv P R G ptr len out) (c n : Nat) (hn : c + n ≤ 0x190) :
    Sep ptr len.toNat (R + BitVec.ofNat 32 c) n :=
  env.hBS.subR (c := c) (l := n) hn

theorem stack_stack (_env : IEnv P R G ptr len out) (c n d l : Nat) (hn : c + n ≤ 0x190)
    (hl : d + l ≤ 0x190) (h : c + n ≤ d ∨ d + l ≤ c) :
    Sep (R + BitVec.ofNat 32 c) n (R + BitVec.ofNat 32 d) l :=
  sep_offsets R h (by omega) (by omega)

theorem r_eqs (env : IEnv P R G ptr len out) :
    G + 0xFFFFFFD0 = R ∧ G + 0xFFFFFFE0 = R + BitVec.ofNat 32 16 ∧
    G + 0xFFFFFFF0 = R + BitVec.ofNat 32 32 ∧ G + 0x18 = R + BitVec.ofNat 32 0x48 ∧
    G + 0x18 + 8 = R + BitVec.ofNat 32 0x50 ∧ G + 0x24 = R + BitVec.ofNat 32 0x54 ∧
    G + 0x124 = R + BitVec.ofNat 32 0x154 := by
  rw [env.hRG]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [BitVec.add_assoc] <;> try rfl
  exact BitVec.add_zero R

end IEnv

/-- The registers the epilogue restores, and the offset of each one's slot
from the frame's base `G`. -/
abbrev ipSlots : List (Fin 32 × Nat) :=
  [(ra, 0x15C), (s0, 0x158), (s1, 0x154), (s2, 0x150), (s3, 0x14C), (s4, 0x148), (s5, 0x144),
   (s6, 0x140), (s7, 0x13C), (s8, 0x138), (s9, 0x134), (s10, 0x130), (s11, 0x12C)]

/-- **`image::parse`'s epilogue.** From offset 0xC0 with the frame at `G`, it
restores `ra` and `s0` through `s11` from their slots, frees the frame, and
returns to the restored `ra`; of the other registers only `a0` and `t0`
change. -/
theorem image_epilogue {Mx : Word → BitVec 8} {P G : Word} {m : Machine} {f : Fin 32 → Word}
    (s : St Mx P m 0xC0 f) (hc : CodeIn Mx P imageParseCode)
    (hr : CodeIn Mx (P + 0x16402) imageRestoreCode) (hP : P.toNat % 2 = 0) (hsp : f sp = G)
    (hG : G.toNat % 4 = 0) :
    ∃ m', Steps m m' ∧ m'.pc = memLoad32 Mx (G + 0x15C) &&& ~~~1 ∧ m'.mem = Mx ∧
      reg m' sp = G + 0x160 ∧
      (∀ p, p ∈ ipSlots → reg m' p.1 = memLoad32 Mx (G + BitVec.ofNat 32 p.2)) ∧
      ∀ r, r ≠ a0 → r ≠ t0 → r ≠ sp → (∀ p, p ∈ ipSlots → r ≠ p.1) → reg m' r = f r := by
  have hz := s.zero
  obtain ⟨m1, e1, t1⟩ := s.aluImm hc ip_at_c0 (off' := 0xC2) (by decide)
  obtain ⟨m2, e2, t2⟩ := t1.auipc hc ip_at_c2 (off' := 0xC6) (by decide)
  obtain ⟨m3, e3, pc3, mem3, regs3⟩ := t2.call hc ip_at_c6
  have ga : ∀ c, c % 4 = 0 → (G + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h => aligned_add hG h
  have hR : (P + 0x16402).toNat % 2 = 0 := even_at P hP 0x16402 (by decide)
  have pc3' : m3.pc = P + 0x16402 + BitVec.ofNat 32 0 := by
    rw [pc3]; simp +decide only [upd, ite_true, ite_false]
    rw [show P + BitVec.ofNat 32 0xC2 + 0x16000 + 0x340 = P + 0x16402 by
      simp only [BitVec.add_assoc]; rfl, even_clear _ hR, add_ofNat_zero]
  have a03 : reg m3 a0 = G + 0x100 := by
    rw [regs3]; simp +decide only [upd, aluEval, ↓reduceIte]; rw [hsp]
  have u3 : St Mx (P + 0x16402) m3 0 (reg m3) := ⟨pc3', mem3, fun _ => rfl⟩
  obtain ⟨m4, c4, t4⟩ := u3.block irBlock hr irBlock_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, irBlock]
    simp +decide only [upd, ite_false]
    rw [a03]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
      (rw [BitVec.add_assoc]; exact ga _ (by decide)))
  obtain ⟨m5, e5, pc5, mem5, regs5⟩ := t4.jalr hr ir_at_1c
  have t0v : (runBlock irBlock (Mx, reg m3)).2 t0 = P + 0xCA := by
    simp only [runBlock, irBlock, BInstr.run]; simp +decide only [upd, ↓reduceIte]
    rw [regs3]; simp +decide only [upd, ↓reduceIte]
    rw [show P + BitVec.ofNat 32 0xC6 + 4 = P + 0xCA by rw [BitVec.add_assoc]; rfl]
  have mem4 : (runBlock irBlock (Mx, reg m3)).1 = Mx := by simp only [runBlock, irBlock, BInstr.run]
  have hCA : (P + 0xCA).toNat % 2 = 0 := even_at P hP 0xCA (by decide)
  have u5 : St Mx P m5 0xCA (reg m5) := by
    refine ⟨?_, by rw [mem5, mem4], fun _ => rfl⟩
    rw [pc5, t0v, add_lit_zero, even_clear _ hCA]; rfl
  have a05 : reg m5 a0 = G + 0x100 := by
    rw [regs5]; simp only [runBlock, irBlock, BInstr.run]; simp +decide only [upd, ↓reduceIte]; exact a03
  obtain ⟨m6, c6, t6⟩ := u5.block ipTailBlock hc ipTailBlock_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, ipTailBlock]
    simp +decide only [upd, ↓reduceIte]
    rw [a05]
    refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
      (rw [BitVec.add_assoc]; exact ga _ (by decide)))
  obtain ⟨m7, e7, pc7, mem7, regs7⟩ := t6.jalr hc ip_at_e0
  have r3 : ∀ r, r ≠ t0 → r ≠ a0 → reg m3 r = f r := fun r h1 h2 => by
    rw [regs3]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, h1, h2]
  have r5 : ∀ r, reg m5 r = (runBlock irBlock (Mx, reg m3)).2 r := regs5
  -- The value of every register after the epilogue.
  have F : ∀ r, (runBlock ipTailBlock (Mx, reg m5)).2 r =
      upd (upd (upd (upd (upd (upd (reg m5) s7 (memLoad32 Mx (G + 0x100 + 0x3C)))
        s8 (memLoad32 Mx (G + 0x100 + 0x38))) s9 (memLoad32 Mx (G + 0x100 + 0x34)))
        s10 (memLoad32 Mx (G + 0x100 + 0x30))) s11 (memLoad32 Mx (G + 0x100 + 0x2C)))
        sp (reg m5 sp + 0x160) r := by
    intro r; simp only [runBlock, ipTailBlock, BInstr.run, aluEval]
    simp +decide only [upd, ↓reduceIte, a05]
  have G5 : ∀ r, reg m5 r =
      upd (upd (upd (upd (upd (upd (upd (upd (reg m3) ra (memLoad32 Mx (G + 0x100 + 0x5C)))
        s0 (memLoad32 Mx (G + 0x100 + 0x58))) s1 (memLoad32 Mx (G + 0x100 + 0x54)))
        s2 (memLoad32 Mx (G + 0x100 + 0x50))) s3 (memLoad32 Mx (G + 0x100 + 0x4C)))
        s4 (memLoad32 Mx (G + 0x100 + 0x48))) s5 (memLoad32 Mx (G + 0x100 + 0x44)))
        s6 (memLoad32 Mx (G + 0x100 + 0x40)) r := by
    intro r; rw [r5]; simp only [runBlock, irBlock, BInstr.run]
    simp +decide only [upd, ↓reduceIte, a03]
  have sp3 : reg m3 sp = G := by rw [r3 sp (by decide) (by decide), hsp]
  have g7 : ∀ r, reg m7 r = (runBlock ipTailBlock (Mx, reg m5)).2 r := regs7
  have ad : ∀ a b : Word, G + a + b = G + (a + b) := fun a b => BitVec.add_assoc _ _ _
  refine ⟨m7, .cons e1 (.cons e2 (.cons e3 (c4.trans (.cons e5 (c6.trans (.single e7)))))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc7, F]; simp +decide only [upd, ↓reduceIte]; rw [G5]; simp +decide only [upd, ↓reduceIte]
    rw [add_lit_zero, ad]; rfl
  · rw [mem7]; simp only [runBlock, ipTailBlock, BInstr.run]
  · rw [g7, F]; simp +decide only [upd, ↓reduceIte]; rw [G5]; simp +decide only [upd, ↓reduceIte]
    rw [sp3]
  · intro p hp
    simp only [ipSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (rw [g7, F]; simp +decide only [upd, ↓reduceIte]
       first
       | (rw [ad]; rfl)
       | (rw [G5]; simp +decide only [upd, ↓reduceIte]; rw [ad]; rfl))
  · intro r h1 h2 h3 hs
    have n : ∀ q, q ∈ ipSlots.map Prod.fst → r ≠ q := fun q hq => by
      simp only [List.mem_map] at hq; obtain ⟨p, hp, rfl⟩ := hq; exact hs p hp
    rw [g7, F]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp only [upd, h0, ↓reduceIte, n s7 (by decide), n s8 (by decide), n s9 (by decide),
        n s10 (by decide), n s11 (by decide), h3]
      rw [G5]
      simp only [upd, h0, ↓reduceIte, n ra (by decide), n s0 (by decide), n s1 (by decide),
        n s2 (by decide), n s3 (by decide), n s4 (by decide), n s5 (by decide), n s6 (by decide)]
      exact r3 r h2 h1

end C3.RV32
