import C3BootProofs.Proofs.Boot
import C3BootProofs.Spec.Accept
import C3BootProofs.Theorems.Formats

/-!
# The contract of `boot_main`'s first closure

`boot_main` calls its first closure, `bootMainClosure0` at 0x403a00a6, once
for each slot it tries, at offsets 0x208 and 0x262. The closure is
`|slot| check(slot, efuse_level, &mut buffers)`, and its specification is
`acceptTufSlot`. `Closure0Contract` states what `boot_main`'s proof assumes
of the call, so that proof can take the closure's theorem as a hypothesis.

The call's arguments:

* `a0` is the result, an `Option<(Accepted, u32)>` of 0x12C bytes. The byte
  at +0xC is 0xFF for `None`. `Accepted` is the first 0x120 bytes, which
  `boot_main` copies and passes to `boot`; the word at +0x120 is the image's
  flash address, and the byte at +0x128 is the image's security version.
  `Accepted` starts with the image header that `image::parse` decoded: 16
  segment entries of 16 bytes (the address, the offset, and the length as
  words, then the kind byte), the entry point at +0x100, and the segment
  count at +0x108. `boot` reads the entry point, the count, and the first
  count entries, and `AccOk` states that they hold the header that
  `decodeImageHeader` decodes from the slot's image.
* `a1` is the eFuse level.
* `a2` is the `Buffers`, 0xB954 bytes.
* `a3` is the slot: 0 for slot A and 1 for slot B.
-/

namespace C3.RV32.BootMainContract
open C3 C3.Image C3.RV32.Cur

/-- The flash address of slot `slot`'s first byte. -/
def bmcBase (slot : Word) : Nat := if slot = 0 then 0x30000 else 0x210000

/-- `len` bytes of flash from `a`. -/
def bmcFlash (flash : Nat → BitVec 8) (a len : Nat) : Bytes :=
  (List.range len).map fun i => (flash (a + i)).toNat

/-- What `acceptTufSlot` says of slot `slot` at eFuse level `level`: the
slot's manifest, then the image's security version and signing time, or
`none` when the manifest doesn't decode or the slot is rejected. -/
def bmcAccept (flash : Nat → BitVec 8) (pinned : Bytes) (policy : Policy) (level : Nat)
    (slot : Word) : Option (Manifest × Nat × Nat) := do
  let mf ← decodeManifest (bmcFlash flash (bmcBase slot) 32)
  let part (p : Part) := bmcFlash flash (bmcBase slot + p.offset) p.length
  let r ← acceptTufSlot (part mf.image) (part mf.bundle) (part mf.tuf) pinned policy level
  pure (mf, r)

/-- Slot `slot`'s image part, as manifest `mf` places it. -/
def bmcImage (flash : Nat → BitVec 8) (slot : Word) (mf : Manifest) : Bytes :=
  bmcFlash flash (bmcBase slot + mf.image.offset) mf.image.length

/-- A segment kind as `image::parse` stores it in the header's kind byte. -/
def bmcKind : SegmentKind → BitVec 8
  | .flashCode => 0
  | .flashData => 1
  | .ramCode => 2
  | .ramData => 3

/-- The header bytes at `acc` hold `h`: the entry point at +0x100, the
segment count at +0x108, and, for each segment `j`, its address, offset, and
length as words at `16 * j`, `16 * j + 4`, and `16 * j + 8`, and its kind
byte at `16 * j + 12`. -/
def HdrAt (M : Word → BitVec 8) (acc : Word) (h : ImageHeader) : Prop :=
  memLoad32 M (acc + 0x100) = BitVec.ofNat 32 h.entryPoint ∧
  memLoad32 M (acc + 0x108) = BitVec.ofNat 32 h.segments.length ∧
  ∀ j (hj : j < h.segments.length),
    memLoad32 M (acc + BitVec.ofNat 32 (16 * j)) = BitVec.ofNat 32 h.segments[j].address ∧
    memLoad32 M (acc + BitVec.ofNat 32 (16 * j + 4)) = BitVec.ofNat 32 h.segments[j].offset ∧
    memLoad32 M (acc + BitVec.ofNat 32 (16 * j + 8)) = BitVec.ofNat 32 h.segments[j].length ∧
    M (acc + BitVec.ofNat 32 (16 * j + 12)) = bmcKind h.segments[j].kind

/-- **What `boot` needs of the `Accepted` bytes at `acc`**: they hold the
header that `decodeImageHeader` decodes from slot `slot`'s image part, which
manifest `mf` places, at the image's length. `acceptTufSlot` decodes the
same bytes, so when `bmcAccept` returns `mf`, that header exists. -/
def AccOk (flash : Nat → BitVec 8) (slot : Word) (mf : Manifest) (M : Word → BitVec 8) (acc : Word) : Prop :=
  ∀ h, decodeImageHeader (bmcImage flash slot mf) mf.image.length = some h → HdrAt M acc h

/-- Where the call puts things: the stack pointer `sp` 16-byte aligned with
`stack` bytes of RAM below it, the result `res` and the `Buffers` `bufs`
word-aligned in RAM, `bufs` at or above `sp` with 14 bytes after it, the
eFuse level below 256, and an even return address `ra`. -/
structure C0Args (stack : Nat) (sp res bufs level ra : Word) : Prop where
  spa : sp.toNat % 16 = 0
  splo : 0x3FCC8000 + stack ≤ sp.toNat
  sphi : sp.toNat ≤ 0x3FCE0000
  resa : res.toNat % 4 = 0
  reslo : 0x3FCC8000 ≤ res.toNat
  reshi : res.toNat + 0x12C ≤ 0x40000000
  bufa : bufs.toNat % 4 = 0
  bufsp : sp.toNat ≤ bufs.toNat
  bufhi : bufs.toNat + 0xB954 + 14 ≤ 0x40000000
  lev : level.toNat < 256
  ra : ra &&& ~~~1 = ra

/-- **The closure's contract.** Called at its entry with the closure's code
in memory, memory that satisfies `E` (the callees' code and data), at least
`stack` bytes of stack, the result, the `Buffers`, and the stack apart, and
the arguments placed as `C0Args` says:
the closure returns to `ra` with the registers that `romKeep` names kept and
memory unchanged outside the stack, the result, and the `Buffers`, or it
panics. On return, the result is `None` when `bmcAccept` is `none`.
Otherwise it holds the image's flash address and security version, and its
`Accepted` part holds the slot's decoded image header (`AccOk`). -/
def Closure0Contract (flash : Nat → BitVec 8) (R : Nat) (romBase : Word) (romCode : List Nat)
    (pinned : Bytes) (policy : Policy) (stack : Nat) (E : (Word → BitVec 8) → Prop) : Prop :=
  RomRead flash R romBase romCode →
  ∀ (m : Machine) (res bufs slot level : Word),
    CodeIn m.mem (BitVec.ofNat 32 bootMainClosure0Address) bootMainClosure0Code → E m.mem →
    m.pc = BitVec.ofNat 32 bootMainClosure0Address → stack ≤ (reg m sp).toNat →
    reg m a0 = res → reg m a1 = level → reg m a2 = bufs → reg m a3 = slot → slot.toNat < 2 →
    C0Args stack (reg m sp) res bufs level (reg m ra) →
    Sep res 0x12C bufs 0xB954 → Sep res 0x12C (reg m sp - BitVec.ofNat 32 stack) stack →
    Sep bufs 0xB954 (reg m sp - BitVec.ofNat 32 stack) stack →
    (∃ m', Steps m m' ∧ m'.pc = reg m ra &&& ~~~1 ∧ (∀ q, romKeep q = true → reg m' q = reg m q) ∧
      (∀ x, Sep (reg m sp - BitVec.ofNat 32 stack) stack x 1 → Sep res 0x12C x 1 →
        Sep bufs 0xB954 x 1 → m'.mem x = m.mem x) ∧
      match bmcAccept flash pinned policy level.toNat slot with
      | none => m'.mem (res + 0xC) = 0xFF
      | some (mf, sv, _) =>
        m'.mem (res + 0xC) ≠ 0xFF ∧ m'.mem (res + 0x128) = BitVec.ofNat 8 sv ∧
          memLoad32 m'.mem (res + 0x120) = BitVec.ofNat 32 (bmcBase slot + mf.image.offset) ∧
          AccOk flash slot mf m'.mem res) ∨
    Panics m

/-! ## From `AccOk` to `boot`'s needs -/

theorem bmc_segs_len : ∀ (n : Nat) (b : Bytes) (ss : List Segment), readSegments n b = some ss → ss.length = n
  | 0, _, ss, h => by simp only [readSegments, Option.some.injEq] at h; subst h; rfl
  | n + 1, b, ss, h => by
    simp only [readSegments, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨⟨s, rest⟩, _, more, hm, rfl⟩ := h
    simp only [List.length_cons, bmc_segs_len n rest more hm]

/-- An accepted header has at most 16 segments, each of which passes
`segmentOk`, and a security version of at most 16. -/
theorem bmc_decode {bytes : Bytes} {n : Nat} {h : ImageHeader} (hd : decodeImageHeader bytes n = some h) :
    h.segments.length ≤ 16 ∧ (∀ s ∈ h.segments, segmentOk n s = true) ∧ h.securityVersion ≤ 16 := by
  refine ⟨?_, (decodeImageHeader_ok hd).2.1, ?_⟩ <;>
  · unfold decodeImageHeader at hd
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, require_eq_some, Option.pure_def,
      Option.some.injEq, exists_const] at hd
    obtain ⟨_, _, _, _, _, _, _, hsv, _, _, hc, _, _, _, _, _, _, _, _, hsegs, _, _, _, _, rfl⟩ := hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc hsv
    first
      | (rw [bmc_segs_len _ _ _ hsegs]; exact hc.2)
      | exact hsv

theorem bmc_kind_le (k : SegmentKind) : (bmcKind k).toNat ≤ 3 := by cases k <;> decide

theorem bmc_ptr (acc : Word) (j c : Nat) (e : Word) (he : e = BitVec.ofNat 32 c) :
    sgPtr acc j + e = acc + BitVec.ofNat 32 (16 * j + c) := by
  subst he; unfold sgPtr; exact add_ofNat_assoc acc (16 * j) c

/-- **`boot`'s needs from the header.** When the bytes at `acc` hold an
accepted header `h`, `boot` walks `h`'s segments, every kind byte is 0 to 3,
and each RAM segment is word-aligned below 0x3FCA0000, so apart from any
range at or above 0x3FCA0000, with a word-aligned flash source when `imgf`
is word-aligned. -/
theorem bmc_hdr {M : Word → BitVec 8} {acc imgf : Word} {h : ImageHeader} {il : Nat}
    (hH : HdrAt M acc h) (hl : h.segments.length ≤ 16) (hok : ∀ s ∈ h.segments, segmentOk il s = true)
    (hi : imgf.toNat % 4 = 0) :
    sgCount M acc = h.segments.length ∧
    (∀ j, j < sgCount M acc → (sgKind M acc j).toNat ≤ 3) ∧
    ∀ j, j < sgCount M acc → 2 ≤ (sgKind M acc j).toNat →
      (sgDest M acc j).toNat % 4 = 0 ∧ (sgDest M acc j).toNat + sgBytes M acc j ≤ 0x3FCA0000 ∧
      (sgSrc M acc imgf j).toNat % 4 = 0 := by
  obtain ⟨_, hcnt, hseg⟩ := hH
  have hlt : h.segments.length < 2 ^ 32 := by omega
  have hc : sgCount M acc = h.segments.length := by
    unfold sgCount; rw [hcnt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; simp [hl]
  refine ⟨hc, fun j hj => ?_, fun j hj hk => ?_⟩
  · rw [hc] at hj
    unfold sgKind; rw [bmc_ptr acc j 12 0xC rfl, (hseg j hj).2.2.2]; exact bmc_kind_le _
  · rw [hc] at hj
    obtain ⟨ea, eo, el, ek⟩ := hseg j hj
    have hsk : sgKind M acc j = bmcKind h.segments[j].kind := by unfold sgKind; rw [bmc_ptr acc j 12 0xC rfl, ek]
    have hsa : sgAddr M acc j = BitVec.ofNat 32 h.segments[j].address := by
      unfold sgAddr; rw [bmc_ptr acc j 0 0 rfl, Nat.add_zero, ea]
    have hso : sgOff M acc j = BitVec.ofNat 32 h.segments[j].offset := by unfold sgOff; rw [bmc_ptr acc j 4 4 rfl, eo]
    have hsl : sgLen M acc j = BitVec.ofNat 32 h.segments[j].length := by unfold sgLen; rw [bmc_ptr acc j 8 8 rfl, el]
    have ok := hok _ (List.getElem_mem hj)
    generalize h.segments[j] = sg at hsk hsa hso hsl ok
    obtain ⟨knd, addr, off, len⟩ := sg
    dsimp only at hsk hsa hso hsl ok
    have hb : sgBytes M acc j ≤ len % 2 ^ 32 := by
      unfold sgBytes; rw [hsl, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]; omega
    unfold segmentOk at ok
    cases knd with
    | flashCode => rw [hsk] at hk; exact absurd hk (by decide)
    | flashData => rw [hsk] at hk; exact absurd hk (by decide)
    | ramCode =>
      simp only [SegmentKind.region, SegmentKind.isFlash, Bool.false_eq_true, Bool.and_eq_true,
        decide_eq_true_eq, u32Limit, flashPage, ite_false, beq_iff_eq] at ok
      obtain ⟨⟨⟨⟨⟨⟨_, ho1⟩, _⟩, ha1⟩, hlo⟩, hhi⟩, ⟨hoa, haa⟩, hla⟩ := ok
      replace ho1 := of_decide_eq_true ho1; replace ha1 := of_decide_eq_true ha1
      replace hlo := of_decide_eq_true hlo; replace hhi := of_decide_eq_true hhi
      have hd : (sgDest M acc j).toNat = addr - 0x700000 := by
        unfold sgDest; rw [hsk, show bmcKind SegmentKind.ramCode = 2 from rfl, ite_eq_left rfl, hsa, BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [show (0xFF900000 : Word).toNat = 0xFF900000 from rfl]; omega
      refine ⟨by rw [hd]; omega, by rw [hd]; omega, ?_⟩
      unfold sgSrc; rw [hso, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    | ramData =>
      simp only [SegmentKind.region, SegmentKind.isFlash, Bool.false_eq_true, Bool.and_eq_true,
        decide_eq_true_eq, u32Limit, flashPage, ite_false, beq_iff_eq] at ok
      obtain ⟨⟨⟨⟨⟨⟨_, ho1⟩, _⟩, ha1⟩, hlo⟩, hhi⟩, ⟨hoa, haa⟩, hla⟩ := ok
      replace ho1 := of_decide_eq_true ho1; replace ha1 := of_decide_eq_true ha1
      replace hlo := of_decide_eq_true hlo; replace hhi := of_decide_eq_true hhi
      have hd : (sgDest M acc j).toNat = addr := by
        unfold sgDest; rw [hsk, ite_eq_right (show ¬bmcKind SegmentKind.ramData = 2 by decide), hsa, BitVec.toNat_ofNat]; omega
      refine ⟨by rw [hd]; omega, by rw [hd]; omega, ?_⟩
      unfold sgSrc; rw [hso, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem bmc_flash_len (flash : Nat → BitVec 8) (a len : Nat) : (bmcFlash flash a len).length = len := by
  unfold bmcFlash; rw [List.length_map, List.length_range]

/-- **What an accepted slot gives `boot_main`.** When `bmcAccept` returns
`(mf, sv, t)`, the image part starts at offset 0x10000, and it decodes to a
header whose security version is `sv`, at least the eFuse level and at most
16. -/
theorem bmc_accept {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {level : Nat} {slot : Word}
    {mf : Manifest} {sv t : Nat} (hA : bmcAccept flash pinned policy level slot = some (mf, sv, t)) :
    mf.image.offset = 0x10000 ∧ level ≤ sv ∧ sv ≤ 16 ∧
      ∃ h, decodeImageHeader (bmcImage flash slot mf) mf.image.length = some h ∧ h.securityVersion = sv := by
  unfold bmcAccept at hA
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hA
  obtain ⟨mf', hm, r, hr, he⟩ := hA
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  unfold acceptTufSlot at hr
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, require_eq_some, Option.pure_def,
    Option.some.injEq, exists_const] at hr
  obtain ⟨h, hd, hge, _, _, _, _, _, _, _, _, _, _, _, hr'⟩ := hr
  simp only [Prod.mk.injEq] at hr'
  obtain ⟨rfl, rfl⟩ := hr'
  unfold decodeManifest at hm
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, require_eq_some, Option.pure_def,
    Option.some.injEq, exists_const] at hm
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hoff, _, _, rfl⟩ := hm
  rw [bmc_flash_len] at hd
  refine ⟨?_, of_decide_eq_true hge, (bmc_decode hd).2.2, h, hd, rfl⟩
  simp only [beq_iff_eq, imageOffset] at hoff
  exact hoff

end C3.RV32.BootMainContract
