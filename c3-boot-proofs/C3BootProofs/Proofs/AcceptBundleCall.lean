import C3BootProofs.Proofs.AcceptBundleLib

/-!
# `boot_main`'s first closure: the bundle stage's calls

The callees' code (`AcBundleEnv`), the frame slots the stage writes, and one
lemma for each kind of call it makes: `memcpy` of the trust root,
`Reader::magic`, `Reader::version_1`, and `bundle::field`, each on the
reader at `sp + 0xDD0` over the bundle's bytes.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3

/-- The code the bundle stage calls, where the image puts it. -/
structure AcBundleEnv (M : Word → BitVec 8) : Prop where
  memcpyStub : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  memcpyBody : CodeIn M (BitVec.ofNat 32 memcpyBodyAddress) memcpyBodyCode
  magic : CodeIn M (BitVec.ofNat 32 readerMagicAddress) readerMagicCode
  array4 : CodeIn M (BitVec.ofNat 32 readerArray4Address) readerArray4Code
  bytes : CodeIn M (BitVec.ofNat 32 readerBytesAddress) readerBytesCode
  version : CodeIn M (BitVec.ofNat 32 readerVersion1Address) readerVersion1Code
  u16 : CodeIn M (BitVec.ofNat 32 readerU16Address) readerU16Code
  u32 : CodeIn M (BitVec.ofNat 32 readerU32Address) readerU32Code
  field : CodeIn M (BitVec.ofNat 32 bundleFieldAddress) bundleFieldCode

theorem acb_codeHi {M M' : Word → BitVec 8} {b : Word} {code : List Nat} (hc : CodeIn M b code)
    (hb : 0x40000000 ≤ b.toNat) (hl : b.toNat + code.length ≤ 2 ^ 32)
    (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) : CodeIn M' b code := fun i hi => by
  rw [h _ (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]; exact hc i hi

set_option maxRecDepth 8000 in
theorem AcBundleEnv.hi {M M' : Word → BitVec 8} (c : AcBundleEnv M)
    (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) : AcBundleEnv M' :=
  ⟨acb_codeHi c.memcpyStub (by decide) (by decide) h, acb_codeHi c.memcpyBody (by decide) (by decide) h,
    acb_codeHi c.magic (by decide) (by decide) h, acb_codeHi c.array4 (by decide) (by decide) h,
    acb_codeHi c.bytes (by decide) (by decide) h, acb_codeHi c.version (by decide) (by decide) h,
    acb_codeHi c.u16 (by decide) (by decide) h, acb_codeHi c.u32 (by decide) (by decide) h,
    acb_codeHi c.field (by decide) (by decide) h⟩

/-! ## The frame -/

/-- The frame slots, as offsets from `B` and lengths, that the stage writes
before the trust root: the callees' stack below `sp`, the spilled bytes at
`sp + 0x14` and `sp + 0x28`, the field result at `sp + 0x350`, the reader at
`sp + 0xDD0`, and the bundle at `sp + 0x1320`. -/
def acbV : List (Nat × Nat) :=
  [(0, 0x3A50), (0x3A64, 0xC), (0x3A78, 0x14), (0x3DA0, 8), (0x4820, 0xC), (0x4D70, 0x30)]

/-- Every frame slot the stage writes: `acbV` and the trust root at
`sp + 0x1870`. -/
def acbW : List (Nat × Nat) := (0x52C0, 0x428) :: acbV

/-- What a call to `bundle::field` writes: its stack, the result, and the
reader's position. -/
def acbFc : List (Nat × Nat) := [(0, 0x3A50), (0x3DA0, 8), (0x4828, 4)]

/-- `x` is outside each slot of `W`. -/
def AcbOut (W : List (Nat × Nat)) (B x : Word) : Prop := ∀ p ∈ W, Sep (B + BitVec.ofNat 32 p.1) p.2 x 1

theorem acb_sep {W : List (Nat × Nat)} {B x : Word} (h : AcbOut W B x) {p : Nat × Nat} (hp : p ∈ W)
    {c l : Nat} (h1 : p.1 ≤ c) (h2 : c + l ≤ p.1 + p.2) : Sep (B + BitVec.ofNat 32 c) l x 1 := by
  have := (h p hp).sub (c := c - p.1) (l := l) (by omega)
  rwa [add_ofNat_assoc, show p.1 + (c - p.1) = c by omega] at this

theorem acb_mono {W W' : List (Nat × Nat)} {B x : Word}
    (hm : ∀ p ∈ W', ∃ q ∈ W, q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2) (h : AcbOut W B x) : AcbOut W' B x :=
  fun p hp => by
    obtain ⟨q, hq, h1, h2⟩ := hm p hp
    exact acb_sep h hq h1 h2

theorem acb_VW {B x : Word} (h : AcbOut acbW B x) : AcbOut acbV B x :=
  acb_mono (by decide) h

theorem acb_FcV {B x : Word} (h : AcbOut acbV B x) : AcbOut acbFc B x :=
  acb_mono (by decide) h

theorem acb_stack {W : List (Nat × Nat)} {B x : Word} (hW : ∀ p ∈ W, p.1 + p.2 ≤ 0x5A70)
    (h : Sep x 1 B 0x5A70) : AcbOut W B x :=
  fun p hp => h.symm.sub (c := p.1) (l := p.2) (hW p hp)

theorem acb_hi {W : List (Nat × Nat)} {B x : Word} (F : Fr B 0x5A70) (hW : ∀ p ∈ W, p.1 + p.2 ≤ 0x5A70)
    (hx : 0x40000000 ≤ x.toNat) : AcbOut W B x :=
  fun p hp => F.hiOut (hW p hp) hx

theorem acb_buf {W : List (Nat × Nat)} {B Bf : Word} (hW : ∀ p ∈ W, p.1 + p.2 ≤ 0x5A70)
    (hs : Sep B 0x5A70 Bf acBufLen) {j : Nat} (hj : j < acBufLen) : AcbOut W B (Bf + BitVec.ofNat 32 j) :=
  fun p hp => (hs.sub (c := p.1) (l := p.2) (hW p hp)).subR (c := j) (l := 1) (by omega)

theorem acb_at {W : List (Nat × Nat)} {B : Word} {c l : Nat} (hW : ∀ p ∈ W, p.1 + p.2 ≤ c ∨ c + l ≤ p.1)
    (hc : c + l ≤ 2 ^ 32) (hW2 : ∀ p ∈ W, p.1 + p.2 ≤ 2 ^ 32) {j : Nat} (hj : j < l) :
    AcbOut W B (B + BitVec.ofNat 32 (c + j)) := fun p hp =>
  sep_offsets B (by have := hW p hp; omega) (hW2 p hp) (by omega)

theorem acb_ld {W : List (Nat × Nat)} {B : Word} {M M' : Word → BitVec 8} (h : ∀ x, AcbOut W B x → M' x = M x)
    {c : Nat} (hW : ∀ p ∈ W, p.1 + p.2 ≤ c ∨ c + 4 ≤ p.1) (hc : c + 4 ≤ 2 ^ 32)
    (hW2 : ∀ p ∈ W, p.1 + p.2 ≤ 2 ^ 32) : memLoad32 M' (B + BitVec.ofNat 32 c) = memLoad32 M (B + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h _ (acb_at hW hc hW2 hj)

theorem acb_ldBuf {W : List (Nat × Nat)} {B Bf : Word} {M M' : Word → BitVec 8} (h : ∀ x, AcbOut W B x → M' x = M x)
    (hW : ∀ p ∈ W, p.1 + p.2 ≤ 0x5A70) (hs : Sep B 0x5A70 Bf acBufLen) {c : Nat} (hc : c + 4 ≤ acBufLen) :
    memLoad32 M' (Bf + BitVec.ofNat 32 c) = memLoad32 M (Bf + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h _ (acb_buf hW hs (by omega))

theorem acb_bytesBuf {W : List (Nat × Nat)} {B Bf : Word} {M M' : Word → BitVec 8}
    (h : ∀ x, AcbOut W B x → M' x = M x) (hW : ∀ p ∈ W, p.1 + p.2 ≤ 0x5A70) (hs : Sep B 0x5A70 Bf acBufLen)
    {c l : Nat} (hc : c + l ≤ acBufLen) :
    memBytes M' (Bf + BitVec.ofNat 32 c) l = memBytes M (Bf + BitVec.ofNat 32 c) l :=
  memBytes_congr fun j hj => by rw [add_ofNat_assoc]; exact h _ (acb_buf hW hs (by omega))

theorem acb_al {B : Word} (F : Fr B 0x5A70) (c : Nat) (hc : c ≤ 0x5A70) (h4 : c % 4 = 0) :
    (B + BitVec.ofNat 32 c).toNat % 4 = 0 := by
  rw [F.at c hc]; have := F.al; omega

theorem acb_spAl {B : Word} (F : Fr B 0x5A70) : (B + 0x3A50).toNat % 4 = 0 :=
  acb_al F 0x3A50 (by decide) (by decide)

/-- `x` outside a 4-byte word at `a` in the callees' stack at `S`. -/
theorem acb_ldS {S a : Word} {n : Nat} {M M' : Word → BitVec 8} (h : ∀ x, Sep S n x 1 → M' x = M x)
    (hs : Sep a 4 S n) : memLoad32 M' a = memLoad32 M a :=
  memLoad32_congr fun j hj => h _ (hs.symm.subR (c := j) (l := 1) (by omega))

theorem acb_ofNat {L : Nat} (h : L < 2 ^ 32) : (BitVec.ofNat 32 L).toNat = L := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem acb_sub0 {a b : Word} {n k l : Nat} (h : Sep a n b k) (hl : l ≤ n) : Sep a l b k := by
  have := h.sub (c := 0) (l := l) (by omega); rwa [add_ofNat_zero] at this

theorem acb_ne {q : Fin 32} {L : List Nat} (h : q.val ∉ L) {r : Fin 32} (hr : r.val ∈ L := by decide) : q ≠ r :=
  fun e => h (e ▸ hr)

/-- The callees' stack below `sp`, apart from the closure's code. -/
theorem acb_stackCode {B : Word} (F : Fr B 0x5A70) {c n : Nat} (h : c + n ≤ 0x5A70) {b : Word} {len : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hl : b.toNat + len ≤ 2 ^ 32) : Sep (B + BitVec.ofNat 32 c) n b len :=
  F.sepHi h hb hl

/-- The reader's bytes are the bundle's, apart from the frame. -/
theorem acb_bufSep {B Bf : Word} (hs : Sep B 0x5A70 Bf acBufLen) {c n : Nat} (hc : c + n ≤ 0x5A70)
    {L : Nat} (hL : L ≤ acBufLen) : Sep Bf L (B + BitVec.ofNat 32 c) n := by
  have := (hs.sub (c := c) (l := n) hc).subR (c := 0) (l := L) (by omega)
  rw [add_ofNat_zero] at this; exact this.symm

/-! ## `bundle::field`'s memory -/

theorem acb_os {out self : Word} (h : Sep out 8 self 12) {c l d k : Nat} (hc : c + l ≤ 8) (hd : d + k ≤ 12) :
    Sep (out + BitVec.ofNat 32 c) l (self + BitVec.ofNat 32 d) k :=
  (h.sub hc).subR hd

/-- What `bundle::field` leaves, for the reader at `self` over the `L` bytes
at `Bf`, at position `q`: the bytes it does not write, the reader's pointer
and length, and either a failure (a zero pointer and a code below 0x27) or
the field's bytes and the reader's new position. -/
theorem acb_fieldMem {M : Word → BitVec 8} {out self Bf lo hi : Word} {L q : Nat} (hL : L < 2 ^ 32)
    (hq : q < 2 ^ 32) (r0 : memLoad32 M self = Bf) (r1 : memLoad32 M (self + 4) = BitVec.ofNat 32 L)
    (r2 : memLoad32 M (self + 8) = BitVec.ofNat 32 q) (hOS : Sep out 8 self 12) :
    (∀ x, Sep out 8 x 1 → Sep (self + 8) 4 x 1 → fieldMem M out self lo hi x = M x) ∧
    memLoad32 (fieldMem M out self lo hi) self = Bf ∧
    memLoad32 (fieldMem M out self lo hi) (self + 4) = BitVec.ofNat 32 L ∧
    ((memLoad32 (fieldMem M out self lo hi) out = 0 ∧ (fieldMem M out self lo hi (out + 4)).toNat < 0x27) ∨
     (q + 4 + (memLoad32 M (Bf + BitVec.ofNat 32 q)).toNat ≤ L ∧
      lo.toNat ≤ (memLoad32 M (Bf + BitVec.ofNat 32 q)).toNat ∧
      (memLoad32 M (Bf + BitVec.ofNat 32 q)).toNat ≤ hi.toNat ∧
      memLoad32 (fieldMem M out self lo hi) out = Bf + BitVec.ofNat 32 (q + 4) ∧
      memLoad32 (fieldMem M out self lo hi) (out + 4) = memLoad32 M (Bf + BitVec.ofNat 32 q) ∧
      memLoad32 (fieldMem M out self lo hi) (self + 8) =
        BitVec.ofNat 32 (q + 4 + (memLoad32 M (Bf + BitVec.ofNat 32 q)).toNat))) := by
  have z : ∀ a : Word, a + BitVec.ofNat 32 0 = a := add_ofNat_zero
  have o00 : Sep out 4 self 4 := by have := acb_os hOS (c := 0) (l := 4) (d := 0) (k := 4) (by omega) (by omega); rwa [z, z] at this
  have o04 : Sep out 4 (self + 4) 4 := by have := acb_os hOS (c := 0) (l := 4) (d := 4) (k := 4) (by omega) (by omega); rwa [z] at this
  have o08 : Sep out 4 (self + 8) 4 := by have := acb_os hOS (c := 0) (l := 4) (d := 8) (k := 4) (by omega) (by omega); rwa [z] at this
  have o40 : Sep (out + 4) 4 self 4 := by have := acb_os hOS (c := 4) (l := 4) (d := 0) (k := 4) (by omega) (by omega); rwa [z] at this
  have o44 : Sep (out + 4) 4 (self + 4) 4 := acb_os hOS (c := 4) (l := 4) (d := 4) (k := 4) (by omega) (by omega)
  have o48 : Sep (out + 4) 4 (self + 8) 4 := acb_os hOS (c := 4) (l := 4) (d := 8) (k := 4) (by omega) (by omega)
  have s80 : Sep (self + 8) 4 self 4 := by
    have := sep_offsets self (c := 8) (n := 4) (d := 0) (k := 4) (by omega) (by omega) (by omega); rwa [z] at this
  have s84 : Sep (self + 8) 4 (self + 4) 4 :=
    sep_offsets self (c := 8) (n := 4) (d := 4) (k := 4) (by omega) (by omega) (by omega)
  have u40 : Sep (out + 4) 4 out 4 := by
    have := sep_offsets out (c := 4) (n := 4) (d := 0) (k := 4) (by omega) (by omega) (by omega); rwa [z] at this
  have e4 : (4 : Word).toNat = 4 := rfl
  have tq := acb_ofNat hq; have tL := acb_ofNat hL
  have hq4 : BitVec.ofNat 32 q + 4 = BitVec.ofNat 32 (q + 4) := BitVec.ofNat_add_ofNat ..
  have eR : bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 4 =
      if q + 4 ≤ L then some (Bf + BitVec.ofNat 32 q, BitVec.ofNat 32 (q + 4)) else none := by
    rw [r0, r1, r2, bytesResult_eq, tq, tL, e4, hq4]
  -- A failure leaves the result's pointer zero and its code byte.
  have fail : ∀ (M1 : Word → BitVec 8) (b : BitVec 8), b.toNat < 0x27 →
      memLoad32 M1 self = Bf → memLoad32 M1 (self + 4) = BitVec.ofNat 32 L →
      (∀ x, Sep (self + 8) 4 x 1 → M1 x = M x) →
      (∀ x, Sep out 8 x 1 → Sep (self + 8) 4 x 1 → memStore8 (memStore32 M1 out 0) (out + 4) b x = M x) ∧
      memLoad32 (memStore8 (memStore32 M1 out 0) (out + 4) b) self = Bf ∧
      memLoad32 (memStore8 (memStore32 M1 out 0) (out + 4) b) (self + 4) = BitVec.ofNat 32 L ∧
      memLoad32 (memStore8 (memStore32 M1 out 0) (out + 4) b) out = 0 ∧
      (memStore8 (memStore32 M1 out 0) (out + 4) b (out + 4)).toNat < 0x27 := by
    intro M1 b hb m0 m1 mk
    refine ⟨fun x hx hx8 => ?_, ?_, ?_, ?_, ?_⟩
    · have h4 := hx 4 (by omega) 0 (by omega)
      rw [add_ofNat_zero] at h4
      have h4' : x ≠ out + 4 := fun e => h4 e.symm
      rw [memStore8_ne h4', memStore32_get_sep (acb_sub0 hx (by omega)), mk x hx8]
    · rw [memLoad32_store8_sep (acb_sub0 o40 (by omega)), memLoad32_store32_sep o00, m0]
    · rw [memLoad32_store8_sep (acb_sub0 o44 (by omega)), memLoad32_store32_sep o04, m1]
    · rw [memLoad32_store8_sep (acb_sub0 u40 (by omega)), memLoad32_store32_same]
    · rw [memStore8_same]; exact hb
  unfold fieldMem
  rw [eR]
  by_cases h4 : q + 4 ≤ L
  · rw [ite_eq_left h4]
    dsimp only
    -- `M1`: the reader's position moved past the length.
    have m10 : memLoad32 (memStore32 M (self + 8) (BitVec.ofNat 32 (q + 4))) self = Bf := by
      rw [memLoad32_store32_sep s80, r0]
    have m11 : memLoad32 (memStore32 M (self + 8) (BitVec.ofNat 32 (q + 4))) (self + 4) = BitVec.ofNat 32 L := by
      rw [memLoad32_store32_sep s84, r1]
    have m1k : ∀ x, Sep (self + 8) 4 x 1 →
        memStore32 M (self + 8) (BitVec.ofNat 32 (q + 4)) x = M x := fun x hx => memStore32_get_sep hx
    by_cases hr : lo.toNat ≤ (memLoad32 M (Bf + BitVec.ofNat 32 q)).toNat ∧
        (memLoad32 M (Bf + BitVec.ofNat 32 q)).toNat ≤ hi.toNat
    · rw [ite_eq_left hr]
      unfold bytesMem
      have hq4' : q + 4 < 2 ^ 32 := by omega
      have eB : bytesResult (memLoad32 (memStore32 M (self + 8) (BitVec.ofNat 32 (q + 4))) self)
          (memLoad32 (memStore32 M (self + 8) (BitVec.ofNat 32 (q + 4))) (self + 4))
          (memLoad32 (memStore32 M (self + 8) (BitVec.ofNat 32 (q + 4))) (self + 8))
          (memLoad32 M (Bf + BitVec.ofNat 32 q)) =
          if q + 4 + (memLoad32 M (Bf + BitVec.ofNat 32 q)).toNat ≤ L then
            some (Bf + BitVec.ofNat 32 (q + 4),
              BitVec.ofNat 32 (q + 4 + (memLoad32 M (Bf + BitVec.ofNat 32 q)).toNat)) else none := by
        rw [m10, m11, memLoad32_store32_same, bytesResult_eq, acb_ofNat hq4', tL]
        congr 3
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega
      rw [eB]
      by_cases h5 : q + 4 + (memLoad32 M (Bf + BitVec.ofNat 32 q)).toNat ≤ L
      · rw [ite_eq_left h5]
        dsimp only
        refine ⟨fun x hx hx8 => ?_, ?_, ?_, Or.inr ⟨h5, hr.1, hr.2, ?_, ?_, ?_⟩⟩
        · rw [memStore32_get_sep (show Sep (out + 4) 4 x 1 from hx.sub (c := 4) (l := 4) (by omega)),
            memStore32_get_sep (acb_sub0 hx (by omega)), memStore32_get_sep hx8, m1k x hx8]
        · rw [memLoad32_store32_sep o40, memLoad32_store32_sep o00, memLoad32_store32_sep s80, m10]
        · rw [memLoad32_store32_sep o44, memLoad32_store32_sep o04, memLoad32_store32_sep s84, m11]
        · rw [memLoad32_store32_sep u40, memLoad32_store32_same]
        · rw [memLoad32_store32_same]
        · rw [memLoad32_store32_sep o48, memLoad32_store32_sep o08, memLoad32_store32_same]
      · rw [ite_eq_right h5]
        dsimp only
        obtain ⟨a, b, c, d, e⟩ := fail (memStore32 M (self + 8) (BitVec.ofNat 32 (q + 4))) 0 (by decide)
          m10 m11 m1k
        exact ⟨a, b, c, Or.inl ⟨d, e⟩⟩
    · rw [ite_eq_right hr]
      obtain ⟨a, b, c, d, e⟩ := fail (memStore32 M (self + 8) (BitVec.ofNat 32 (q + 4))) 5 (by decide)
        m10 m11 m1k
      exact ⟨a, b, c, Or.inl ⟨d, e⟩⟩
  · rw [ite_eq_right h4]
    dsimp only
    obtain ⟨a, b, c, d, e⟩ := fail M 0 (by decide) r0 r1 (fun _ _ => rfl)
    exact ⟨a, b, c, Or.inl ⟨d, e⟩⟩

/-! ## The calls -/

theorem acb_s4 (B : Word) : acSlot B 0xDD0 + 4 = acSlot B 0xDD4 := add_ofNat_assoc _ _ _
theorem acb_s8 (B : Word) : acSlot B 0xDD0 + 8 = acSlot B 0xDD8 := add_ofNat_assoc _ _ _
theorem acb_o4 (B : Word) : acSlot B 0x350 + 4 = acSlot B 0x354 := add_ofNat_assoc _ _ _

/-- The reader's three words. -/
structure AcbRd (B Bf : Word) (L q : Nat) (M : Word → BitVec 8) : Prop where
  ptr : memLoad32 M (acSlot B 0xDD0) = Bf
  len : memLoad32 M (acSlot B 0xDD4) = BitVec.ofNat 32 L
  pos : memLoad32 M (acSlot B 0xDD8) = BitVec.ofNat 32 q

/-- What the reader's callees need of it: the bundle's `L` bytes at `Bf`,
apart from the frame and the code. -/
structure AcbBuf (B Bf : Word) (L : Nat) : Prop where
  fr : Fr B 0x5A70
  hs : Sep B 0x5A70 Bf acBufLen
  sv : Sv.SvIn (B + 0x13F0) Bf 0x4000
  hL : L ≤ 0x4000

theorem AcbBuf.hbuf {B Bf : Word} {L : Nat} (Y : AcbBuf B Bf L) {M : Word → BitVec 8} {q : Nat}
    (R : AcbRd B Bf L q M) :
    memLoad32 M (acSlot B 0xDD0) ≠ 0 ∧
      (memLoad32 M (acSlot B 0xDD0)).toNat + (memLoad32 M (acSlot B 0xDD0 + 4)).toNat ≤ 2 ^ 32 := by
  have hp := Y.sv.pos; have hl := Y.sv.lo; have := Y.hL
  rw [acb_s4, R.ptr, R.len, acb_ofNat (by omega)]
  refine ⟨fun h => ?_, by omega⟩
  rw [h] at hp; exact absurd hp (by decide)

theorem AcbBuf.bs {B Bf : Word} {L : Nat} (Y : AcbBuf B Bf L) {M : Word → BitVec 8} {q : Nat}
    (R : AcbRd B Bf L q M) {c n : Nat} (hc : c + n ≤ 0x5A70) {a : Word} (ha : a = B + BitVec.ofNat 32 c) :
    Sep (memLoad32 M (acSlot B 0xDD0)) (memLoad32 M (acSlot B 0xDD0 + 4)).toNat a n := by
  have := Y.hL
  rw [acb_s4, R.ptr, R.len, acb_ofNat (by omega), ha]
  exact acb_bufSep Y.hs hc (by unfold acBufLen; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **A call to `bundle::field`** from offset `o`, writing its result at
`sp + 0x350` from the reader at `sp + 0xDD0` at position `q`. -/
theorem acb_fcall {n : Machine} {B Bf : Word} {o : Nat} {imm off lo hi : Word} {L q : Nat}
    (s : St n.mem AC n o (reg n)) (C : CodeIn n.mem AC bootMainClosure0Code) (E : AcBundleEnv n.mem)
    (Y : AcbBuf B Bf L) (R : AcbRd B Bf L q n.mem) (hq : q ≤ L)
    (h1 : fetchRel bootMainClosure0Code o = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (o + 4) = some (.jalr ra ra off, 4))
    (hb : AC + BitVec.ofNat 32 o + imm + off = BitVec.ofNat 32 bundleFieldAddress)
    (hl : (AC + BitVec.ofNat 32 (o + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x3A50) (ra0 : reg n a0 = acSlot B 0x350) (ra1 : reg n a1 = acSlot B 0xDD0)
    (ra2 : reg n a2 = lo) (ra3 : reg n a3 = hi) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (o + 8) (reg n') ∧
      (∀ x : Fin 32, x.val ∉ [1, 6, 10, 11, 12, 13, 14, 15] → reg n' x = reg n x) ∧
      (∀ x, AcbOut acbFc B x → n'.mem x = n.mem x) ∧
      memLoad32 n'.mem (acSlot B 0xDD0) = Bf ∧ memLoad32 n'.mem (acSlot B 0xDD4) = BitVec.ofNat 32 L ∧
      ((memLoad32 n'.mem (acSlot B 0x350) = 0 ∧ (n'.mem (acSlot B 0x354)).toNat < 0x27) ∨
       (q + 4 + (memLoad32 n.mem (Bf + BitVec.ofNat 32 q)).toNat ≤ L ∧
        lo.toNat ≤ (memLoad32 n.mem (Bf + BitVec.ofNat 32 q)).toNat ∧
        (memLoad32 n.mem (Bf + BitVec.ofNat 32 q)).toNat ≤ hi.toNat ∧
        memLoad32 n'.mem (acSlot B 0x350) = Bf + BitVec.ofNat 32 (q + 4) ∧
        memLoad32 n'.mem (acSlot B 0x354) = memLoad32 n.mem (Bf + BitVec.ofNat 32 q) ∧
        memLoad32 n'.mem (acSlot B 0xDD8) =
          BitVec.ofNat 32 (q + 4 + (memLoad32 n.mem (Bf + BitVec.ofNat 32 q)).toNat))) := by
  have F := Y.fr
  have hL := Y.hL
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa C h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg m1 r = reg n r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg m1 sp = B + 0x3A50 := by rw [r1 sp (by decide), rsp]
  have hS : B + 0x3A50 + 0xFFFFFFB0 = B + BitVec.ofNat 32 0x3A00 := by rw [BitVec.add_assoc]; rfl
  have R1 : AcbRd B Bf L q m1.mem := by rw [mem1]; exact R
  obtain ⟨m2, c2, pc2, sp2, fr2, mem2⟩ := bundleField_correct m1 (base := BitVec.ofNat 32 bundleFieldAddress)
    (retAddr := AC + BitVec.ofNat 32 (o + 8)) (out := acSlot B 0x350) (self := acSlot B 0xDD0) (lo := lo)
    (hi := hi)
    (by rw [mem1]; exact E.field)
    (by
      rw [mem1, show (BitVec.ofNat 32 bundleFieldAddress + 0xFFFFCFB0 : Word) = BitVec.ofNat 32 readerU32Address
        from by decide]
      exact E.u32)
    (by
      rw [mem1, show (BitVec.ofNat 32 bundleFieldAddress + 0xFFFFCFB0 + 0x50 : Word) =
        BitVec.ofNat 32 readerArray4Address from by decide]
      exact E.array4)
    (by
      rw [mem1, show (BitVec.ofNat 32 bundleFieldAddress + 0xFFFFCF8A : Word) =
        BitVec.ofNat 32 readerBytesAddress from by decide]
      exact E.bytes)
    (by decide) pc1 (by rw [r1 a0 (by decide), ra0]) (by rw [r1 a1 (by decide), ra1])
    (by rw [r1 a2 (by decide), ra2]) (by rw [r1 a3 (by decide), ra3])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) (by rw [sp1]; exact acb_spAl F)
    (acb_al F _ (by decide) (by decide)) (acb_al F _ (by decide) (by decide))
    (Y.hbuf R1)
    (by rw [sp1, hS]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [sp1, hS]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [sp1, hS]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [sp1, hS]; exact F.sepHi (by decide) (by decide) (by decide))
    (F.sepHi (by decide) (by decide) (by decide)) (F.sepHi (by decide) (by decide) (by decide))
    (by rw [acb_s8]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [acb_s8]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [acb_s8]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [acb_s8]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [sp1, hS]; exact sep_offsets B (by decide) (by decide) (by decide))
    (by rw [sp1, hS]; exact sep_offsets B (by decide) (by decide) (by decide))
    (Y.bs R1 (c := 0x3A00) (n := 80) (by decide) (by rw [sp1, hS]))
    (Y.bs R1 (c := 0x3A50 + 0xDD8) (n := 4) (by decide) (acb_s8 B))
  rw [sp1, hS, mem1] at mem2
  have FM := acb_fieldMem (M := n.mem) (out := acSlot B 0x350) (self := acSlot B 0xDD0) (lo := lo) (hi := hi)
    (L := L) (q := q) (by omega) (by omega) R.ptr (by rw [acb_s4]; exact R.len) (by rw [acb_s8]; exact R.pos)
    (sep_offsets B (by decide) (by decide) (by decide))
  rw [acb_s4, acb_s8, acb_o4] at FM
  obtain ⟨Ffr, F0, F1, Fres⟩ := FM
  have st : ∀ c, 0x3A50 ≤ c → c + 4 ≤ 0x5A70 → Sep (B + BitVec.ofNat 32 c) 4 (B + BitVec.ofNat 32 0x3A00) 80 :=
    fun c h1 h2 => sep_offsets B (by omega) (by omega) (by omega)
  have ld : ∀ c, 0x3A50 ≤ c → c + 4 ≤ 0x5A70 →
      memLoad32 m2.mem (B + BitVec.ofNat 32 c) = memLoad32 (fieldMem n.mem (acSlot B 0x350) (acSlot B 0xDD0) lo hi)
        (B + BitVec.ofNat 32 c) := fun c h1 h2 => acb_ldS mem2 (st c h1 h2)
  refine ⟨m2, c1.trans c2, ⟨pc2, rfl, fun _ => rfl⟩, fun x hx => ?_, fun x hx => ?_, ?_, ?_, ?_⟩
  · rw [fr2 x (acb_ne hx) (acb_ne hx) (acb_ne hx) (acb_ne hx) (acb_ne hx) (acb_ne hx) (acb_ne hx),
      r1 x (acb_ne hx)]
  · rw [mem2 x (acb_sep hx (p := (0, 0x3A50)) (by decide) (by decide) (by decide)),
      Ffr x (acb_sep hx (p := (0x3DA0, 8)) (by decide) (by decide) (by decide))
        (acb_sep hx (p := (0x4828, 4)) (by decide) (by decide) (by decide))]
  · rw [ld _ (by decide) (by decide)]; exact F0
  · rw [ld _ (by decide) (by decide)]; exact F1
  · rcases Fres with ⟨f0, f4⟩ | ⟨g1, g2, g3, g4, g5, g6⟩
    · refine Or.inl ⟨by rw [ld _ (by decide) (by decide)]; exact f0, ?_⟩
      rw [mem2 _ (acb_sub0 (st (0x3A50 + 0x354) (by decide) (by decide)) (by decide)).symm]
      exact f4
    · refine Or.inr ⟨g1, g2, g3, ?_, ?_, ?_⟩
      · rw [ld _ (by decide) (by decide)]; exact g4
      · rw [ld _ (by decide) (by decide)]; exact g5
      · rw [ld _ (by decide) (by decide)]; exact g6

theorem acb_magicR {M : Word → BitVec 8} {self Bf : Word} {L : Nat} (hL : L < 2 ^ 32)
    (r0 : memLoad32 M self = Bf) (r1 : memLoad32 M (self + 4) = BitVec.ofNat 32 L)
    (r2 : memLoad32 M (self + 8) = BitVec.ofNat 32 0) (k : Word) :
    magicResult M self k = (if 4 ≤ L then (if memLoad32 M Bf == k then 0xFFFFFFFF else 2) else 0) ∧
    magicMem M self = (if 4 ≤ L then memStore32 M (self + 8) 4 else M) := by
  have e : bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 4 =
      if 4 ≤ L then some (Bf, 4) else none := by
    rw [r0, r1, r2, bytesResult_eq, acb_ofNat hL, add_ofNat_zero,
      show (BitVec.ofNat 32 0).toNat + (4 : Word).toNat = 4 from rfl,
      show BitVec.ofNat 32 0 + (4 : Word) = 4 from rfl]
  unfold magicResult magicMem
  rw [e]
  by_cases h : 4 ≤ L
  · simp only [h, ↓reduceIte, and_self]
  · simp only [h, ↓reduceIte, and_self]

theorem acb_versionR {M : Word → BitVec 8} {self Bf : Word} {L : Nat} (hL : L < 2 ^ 32)
    (r0 : memLoad32 M self = Bf) (r1 : memLoad32 M (self + 4) = BitVec.ofNat 32 L)
    (r2 : memLoad32 M (self + 8) = BitVec.ofNat 32 4) :
    version1Result M self = (if 6 ≤ L then
      (if (M (Bf + 4)).toNat + 256 * (M (Bf + 4 + 1)).toNat = 1 then 0xFFFFFFFF else 3) else 0) ∧
    u16Mem M self = (if 6 ≤ L then memStore32 M (self + 8) 6 else M) := by
  have e : bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 2 =
      if 6 ≤ L then some (Bf + 4, 6) else none := by
    rw [r0, r1, r2, bytesResult_eq, acb_ofNat hL,
      show (BitVec.ofNat 32 4).toNat + (2 : Word).toNat = 6 from rfl,
      show BitVec.ofNat 32 4 + (2 : Word) = 6 from rfl]
    rfl
  unfold version1Result u16Mem u16Result
  rw [e]
  by_cases h : 6 ≤ L
  · simp only [h, ↓reduceIte, and_true]
    have cv : (((M (Bf + 4 + 1)).zeroExtend 32 <<< 24 ||| (M (Bf + 4)).zeroExtend 32 <<< 16 : Word) >>> 16 == 1) =
        decide ((M (Bf + 4)).toNat + 256 * (M (Bf + 4 + 1)).toNat = 1) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, version_toNat]; rfl
    rw [cv]
    by_cases hv : (M (Bf + 4)).toNat + 256 * (M (Bf + 4 + 1)).toNat = 1
    · simp only [hv, decide_true, ↓reduceIte]
    · simp only [hv, decide_false, ↓reduceIte]; rfl
  · simp only [h, ↓reduceIte, and_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The call to `Reader::magic`** for `C3BN` on the reader at `sp + 0xDD0`. -/
theorem acb_mcall {n : Machine} {B Bf : Word} {o : Nat} {imm off : Word} {L : Nat}
    (s : St n.mem AC n o (reg n)) (C : CodeIn n.mem AC bootMainClosure0Code) (E : AcBundleEnv n.mem)
    (Y : AcbBuf B Bf L) (R : AcbRd B Bf L 0 n.mem)
    (h1 : fetchRel bootMainClosure0Code o = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (o + 4) = some (.jalr ra ra off, 4))
    (hb : AC + BitVec.ofNat 32 o + imm + off = BitVec.ofNat 32 readerMagicAddress)
    (hl : (AC + BitVec.ofNat 32 (o + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x3A50) (ra0 : reg n a0 = acSlot B 0xDD0) (ra1 : reg n a1 = 0x4E423343) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (o + 8) (reg n') ∧
      (∀ x : Fin 32, x.val ∉ [1, 5, 10, 11, 12, 13, 14, 15] → reg n' x = reg n x) ∧
      (∀ x, AcbOut acbFc B x → n'.mem x = n.mem x) ∧
      (reg n' a0 = 0 ∨ reg n' a0 = 2 ∨
        (reg n' a0 = 0xFFFFFFFF ∧ 4 ≤ L ∧ memLoad32 n.mem Bf = 0x4E423343 ∧ AcbRd B Bf L 4 n'.mem)) := by
  have F := Y.fr
  have hL := Y.hL
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa C h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg m1 r = reg n r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg m1 sp = B + 0x3A50 := by rw [r1 sp (by decide), rsp]
  have hS : B + 0x3A50 + 0xFFFFFFD0 = B + BitVec.ofNat 32 0x3A20 := by rw [BitVec.add_assoc]; rfl
  have R1 : AcbRd B Bf L 0 m1.mem := by rw [mem1]; exact R
  obtain ⟨m2, c2, pc2, sp2, a02, fr2, mem2⟩ := Cur.readerMagic_correct m1 (BitVec.ofNat 32 readerMagicAddress)
    (AC + BitVec.ofNat 32 (o + 8)) (acSlot B 0xDD0) 0x4E423343
    (fun i hi => by rw [mem1]; exact E.magic i hi)
    (fun i hi => by
      rw [mem1, show (BitVec.ofNat 32 readerMagicAddress + 0xFFFFFFBA : Word) = BitVec.ofNat 32 readerArray4Address
        from by decide]
      exact E.array4 i hi)
    (fun i hi => by
      rw [mem1, show (BitVec.ofNat 32 readerMagicAddress + 0xFFFFFFBA + 0xFFFFFF8A : Word) =
        BitVec.ofNat 32 readerBytesAddress from by decide]
      exact E.bytes i hi)
    (by decide) pc1 (by rw [r1 a0 (by decide), ra0]) (by rw [r1 a1 (by decide), ra1])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) (by rw [sp1]; exact acb_spAl F)
    (acb_al F _ (by decide) (by decide))
    (Y.hbuf R1)
    (by rw [sp1, hS]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [sp1, hS]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [sp1, hS]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [acb_s8]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [acb_s8]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [acb_s8]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [sp1, hS]; exact sep_offsets B (by decide) (by decide) (by decide))
    (Y.bs R1 (c := 0x3A20) (n := 48) (by decide) (by rw [sp1, hS]))
    (Y.bs R1 (c := 0x3A50 + 0xDD8) (n := 4) (by decide) (acb_s8 B))
  rw [sp1, hS, mem1] at mem2
  rw [mem1] at a02
  obtain ⟨eA, eM⟩ := acb_magicR (M := n.mem) (L := L) (by omega) R.ptr (by rw [acb_s4]; exact R.len)
    (by rw [acb_s8]; exact R.pos) 0x4E423343
  rw [eA] at a02
  rw [eM] at mem2
  have st : ∀ c, 0x3A50 ≤ c → c + 4 ≤ 0x5A70 → Sep (B + BitVec.ofNat 32 c) 4 (B + BitVec.ofNat 32 0x3A20) 48 :=
    fun c h1 h2 => sep_offsets B (by omega) (by omega) (by omega)
  have s8 : ∀ x, AcbOut acbFc B x → Sep (acSlot B 0xDD0 + 8) 4 x 1 := fun x hx => by
    rw [acb_s8]; exact acb_sep hx (p := (0x4828, 4)) (by decide) (by decide) (by decide)
  refine ⟨m2, c1.trans c2, ⟨pc2, rfl, fun _ => rfl⟩, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · rw [fr2 x (acb_ne hx) (acb_ne hx) (acb_ne hx) (acb_ne hx) (acb_ne hx) (acb_ne hx) (acb_ne hx),
      r1 x (acb_ne hx)]
  · rw [mem2 x (acb_sep hx (p := (0, 0x3A50)) (by decide) (by decide) (by decide))]
    split
    · exact memStore32_get_sep (s8 x hx)
    · rfl
  · by_cases h4 : 4 ≤ L
    · rw [ite_eq_left h4] at a02 mem2
      by_cases hk : memLoad32 n.mem Bf = 0x4E423343
      · rw [ite_eq_left (by rw [hk]; rfl)] at a02
        have ld : ∀ c, 0x3A50 ≤ c → c + 4 ≤ 0x5A70 → memLoad32 m2.mem (B + BitVec.ofNat 32 c) =
            memLoad32 (memStore32 n.mem (acSlot B 0xDD0 + 8) 4) (B + BitVec.ofNat 32 c) :=
          fun c h1 h2 => acb_ldS mem2 (st c h1 h2)
        refine Or.inr (Or.inr ⟨a02, h4, hk, ?_, ?_, ?_⟩)
        · rw [ld _ (by decide) (by decide), acb_s8,
            memLoad32_store32_sep (sep_offsets B (by decide) (by decide) (by decide))]; exact R.ptr
        · rw [ld _ (by decide) (by decide), acb_s8,
            memLoad32_store32_sep (sep_offsets B (by decide) (by decide) (by decide))]; exact R.len
        · rw [ld _ (by decide) (by decide), acb_s8, memLoad32_store32_same]; rfl
      · rw [ite_eq_right (by rw [beq_iff_eq]; exact hk)] at a02
        exact Or.inr (Or.inl a02)
    · rw [ite_eq_right h4] at a02
      exact Or.inl a02

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The call to `Reader::version_1`** on the reader at `sp + 0xDD0`. -/
theorem acb_vcall {n : Machine} {B Bf : Word} {o : Nat} {imm off : Word} {L : Nat}
    (s : St n.mem AC n o (reg n)) (C : CodeIn n.mem AC bootMainClosure0Code) (E : AcBundleEnv n.mem)
    (Y : AcbBuf B Bf L) (R : AcbRd B Bf L 4 n.mem)
    (h1 : fetchRel bootMainClosure0Code o = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (o + 4) = some (.jalr ra ra off, 4))
    (hb : AC + BitVec.ofNat 32 o + imm + off = BitVec.ofNat 32 readerVersion1Address)
    (hl : (AC + BitVec.ofNat 32 (o + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x3A50) (ra0 : reg n a0 = acSlot B 0xDD0) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (o + 8) (reg n') ∧
      (∀ x : Fin 32, x.val ∉ [1, 10, 11, 12, 13, 14, 15] → reg n' x = reg n x) ∧
      (∀ x, AcbOut acbFc B x → n'.mem x = n.mem x) ∧
      (reg n' a0 = 0 ∨ reg n' a0 = 3 ∨
        (reg n' a0 = 0xFFFFFFFF ∧ 6 ≤ L ∧ (n.mem (Bf + 4)).toNat + 256 * (n.mem (Bf + 4 + 1)).toNat = 1 ∧
          AcbRd B Bf L 6 n'.mem)) := by
  have F := Y.fr
  have hL := Y.hL
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa C h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg m1 r = reg n r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg m1 sp = B + 0x3A50 := by rw [r1 sp (by decide), rsp]
  have hS : B + 0x3A50 + 0xFFFFFFE0 = B + BitVec.ofNat 32 0x3A30 := by rw [BitVec.add_assoc]; rfl
  have R1 : AcbRd B Bf L 4 m1.mem := by rw [mem1]; exact R
  obtain ⟨m2, c2, pc2, sp2, a02, fr2, mem2⟩ := readerVersion1_correct m1
    (BitVec.ofNat 32 readerVersion1Address) (AC + BitVec.ofNat 32 (o + 8)) (acSlot B 0xDD0)
    (fun i hi => by rw [mem1]; exact E.version i hi)
    (fun i hi => by
      rw [mem1, show (BitVec.ofNat 32 readerVersion1Address + 0xFFFFD054 : Word) = BitVec.ofNat 32 readerU16Address
        from by decide]
      exact E.u16 i hi)
    (fun i hi => by
      rw [mem1, show (BitVec.ofNat 32 readerVersion1Address + 0xFFFFD054 + 0x44 : Word) =
        BitVec.ofNat 32 readerBytesAddress from by decide]
      exact E.bytes i hi)
    (by decide) pc1 (by rw [r1 a0 (by decide), ra0])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) (by rw [sp1]; exact acb_spAl F)
    (acb_al F _ (by decide) (by decide))
    (Y.hbuf R1)
    (by rw [sp1, hS]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [sp1, hS]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [sp1, hS]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [acb_s8]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [acb_s8]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [acb_s8]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [sp1, hS]; exact sep_offsets B (by decide) (by decide) (by decide))
    (Y.bs R1 (c := 0x3A30) (n := 32) (by decide) (by rw [sp1, hS]))
    (Y.bs R1 (c := 0x3A50 + 0xDD8) (n := 4) (by decide) (acb_s8 B))
  rw [sp1, hS, mem1] at mem2
  rw [mem1] at a02
  obtain ⟨eA, eM⟩ := acb_versionR (M := n.mem) (L := L) (by omega) R.ptr (by rw [acb_s4]; exact R.len)
    (by rw [acb_s8]; exact R.pos)
  rw [eA] at a02
  rw [eM] at mem2
  have st : ∀ c, 0x3A50 ≤ c → c + 4 ≤ 0x5A70 → Sep (B + BitVec.ofNat 32 c) 4 (B + BitVec.ofNat 32 0x3A30) 32 :=
    fun c h1 h2 => sep_offsets B (by omega) (by omega) (by omega)
  have s8 : ∀ x, AcbOut acbFc B x → Sep (acSlot B 0xDD0 + 8) 4 x 1 := fun x hx => by
    rw [acb_s8]; exact acb_sep hx (p := (0x4828, 4)) (by decide) (by decide) (by decide)
  refine ⟨m2, c1.trans c2, ⟨pc2, rfl, fun _ => rfl⟩, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · rw [fr2 x (acb_ne hx) (acb_ne hx) (acb_ne hx) (acb_ne hx) (acb_ne hx) (acb_ne hx), r1 x (acb_ne hx)]
  · rw [mem2 x (acb_sep hx (p := (0, 0x3A50)) (by decide) (by decide) (by decide))]
    split
    · exact memStore32_get_sep (s8 x hx)
    · rfl
  · by_cases h6 : 6 ≤ L
    · rw [ite_eq_left h6] at a02 mem2
      by_cases hv : (n.mem (Bf + 4)).toNat + 256 * (n.mem (Bf + 4 + 1)).toNat = 1
      · rw [ite_eq_left hv] at a02
        have ld : ∀ c, 0x3A50 ≤ c → c + 4 ≤ 0x5A70 → memLoad32 m2.mem (B + BitVec.ofNat 32 c) =
            memLoad32 (memStore32 n.mem (acSlot B 0xDD0 + 8) 6) (B + BitVec.ofNat 32 c) :=
          fun c h1 h2 => acb_ldS mem2 (st c h1 h2)
        refine Or.inr (Or.inr ⟨a02, h6, hv, ?_, ?_, ?_⟩)
        · rw [ld _ (by decide) (by decide), acb_s8,
            memLoad32_store32_sep (sep_offsets B (by decide) (by decide) (by decide))]; exact R.ptr
        · rw [ld _ (by decide) (by decide), acb_s8,
            memLoad32_store32_sep (sep_offsets B (by decide) (by decide) (by decide))]; exact R.len
        · rw [ld _ (by decide) (by decide), acb_s8, memLoad32_store32_same]; rfl
      · rw [ite_eq_right hv] at a02
        exact Or.inr (Or.inl a02)
    · rw [ite_eq_right h6] at a02
      exact Or.inl a02

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The call to `memcpy` at 0x1816**: the trust root's last 0x423 bytes
from `sp + 0xDD0` to `sp + 0x1875`. -/
theorem acb_cpy {n : Machine} {B : Word}
    (s : St n.mem AC n 0x1816 (reg n)) (C : CodeIn n.mem AC bootMainClosure0Code) (E : AcBundleEnv n.mem)
    (F : Fr B 0x5A70) (rsp : reg n sp = B + 0x3A50)
    (ra0 : reg n a0 = acSlot B 0x1875) (ra1 : reg n a1 = acSlot B 0xDD0) (ra2 : reg n a2 = 0x423)
    (hra : reg n ra = AC + BitVec.ofNat 32 0x1812 + 0x15000) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' 0x181A (reg n') ∧
      (∀ x : Fin 32, x.val ∉ [1, 2, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30] → reg n' x = reg n x) ∧
      (∀ x, Sep (B + BitVec.ofNat 32 0x3A40) 16 x 1 →
        n'.mem x = copyBytes n.mem (acSlot B 0x1875) (acSlot B 0xDD0) 0x423 x) := by
  have hz := s.zero
  obtain ⟨m1, e1, pc1, mem1, regs1⟩ := s.call C ac_at_1816
  have r1 : ∀ r, r ≠ ra → reg m1 r = reg n r := fun r h => by rw [regs1]; exact updz hz h
  have eS : B + 0x3A50 + 0xFFFFFFF0 = B + BitVec.ofNat 32 0x3A40 := by rw [BitVec.add_assoc]; rfl
  have E' : McEnv m1.mem (BitVec.ofNat 32 memcpyStubAddress + 8) (acSlot B 0x1875) (acSlot B 0xDD0)
      (reg m1 sp + 0xFFFFFFF0) 0x423 := by
    rw [mem1, r1 sp (by decide), rsp, eS,
      show (BitVec.ofNat 32 memcpyStubAddress + 8 : Word) = BitVec.ofNat 32 memcpyBodyAddress from by decide]
    have hB := F.hi
    exact { code := E.memcpyBody
            hDC := F.sepHi (by decide) (by decide) (by decide)
            hFC := F.sepHi (by decide) (by decide) (by decide)
            hdF := sep_offsets B (by decide) (by decide) (by decide)
            hsF := sep_offsets B (by decide) (by decide) (by decide)
            hsep := sep_offsets B (by decide) (by decide) (by decide)
            hF := acb_al F _ (by decide) (by decide)
            hFw := by rw [F.at _ (by decide)]; omega
            hdw := by show (B + BitVec.ofNat 32 (0x3A50 + 0x1875)).toNat + 0x423 < 2 ^ 32
                      rw [F.at _ (by decide)]; omega
            hsw := by show (B + BitVec.ofNat 32 (0x3A50 + 0xDD0)).toNat + 0x423 < 2 ^ 32
                      rw [F.at _ (by decide)]; omega }
  obtain ⟨m2, c2, pc2, sp2, _, f2, k2⟩ := memcpy_correct m1 (BitVec.ofNat 32 memcpyStubAddress)
    (AC + BitVec.ofNat 32 0x1816 + 4) (acSlot B 0x1875) (acSlot B 0xDD0) 0x423
    (fun i hi => by rw [mem1]; exact E.memcpyStub i hi) (by decide)
    (by rw [pc1, hra]; decide)
    (by rw [r1 a0 (by decide), ra0]) (by rw [r1 a1 (by decide), ra1]) (by rw [r1 a2 (by decide), ra2]; rfl)
    (by rw [regs1]; simp +decide [upd]) (by decide) E'
  rw [mem1, r1 sp (by decide), rsp, eS] at f2
  refine ⟨m2, .cons e1 c2, ⟨by rw [pc2, BitVec.add_assoc]; rfl, rfl, fun _ => rfl⟩, fun x hx => ?_, f2⟩
  by_cases hs : x = sp
  · subst hs; rw [sp2, r1 sp (by decide)]
  · rw [k2 x (acb_ne hx) (acb_ne hx) (acb_ne hx) (acb_ne hx) (acb_ne hx) (acb_ne hx) (acb_ne hx) (acb_ne hx)
      (acb_ne hx) (acb_ne hx) (acb_ne hx) (acb_ne hx) (acb_ne hx) hs, r1 x (acb_ne hx)]

/-! ## The way out on a rejected bundle -/

theorem acb_zb (b : BitVec 8) : ((b.zeroExtend 32 : Word) &&& 0xFF).toNat = b.toNat := by
  revert b; decide

/-- From 0x1A6A: `s5 := s0`, then the jump to the reject exit at 0x7D6. -/
theorem acb_t6a {n : Machine} (s : St n.mem AC n 0x1A6A (reg n)) (C : CodeIn n.mem AC bootMainClosure0Code) :
    ∃ n', Steps n n' ∧ n'.pc = AC + 0x7D6 ∧ n'.mem = n.mem ∧
      (∀ x : Fin 32, x.val ≠ 21 → reg n' x = reg n x) ∧ reg n' (21 : Fin 32) = reg n (8 : Fin 32) := by
  have hz := s.zero
  obtain ⟨n1, e1, s1⟩ := s.alu C ac_at_1a6a (off' := 0x1A6C) (by decide)
  obtain ⟨n2, e2, s2⟩ := s1.jump C ac_at_1a6c (off' := 0x7D6) (by decide) (by rw [s1.pc]; decide)
  refine ⟨n2, .cons e1 (.single e2), s2.pc, s2.mem, fun x hx => ?_, ?_⟩
  · rw [s2.regs x, updz hz (fun e => hx (congrArg Fin.val e))]
  · rw [s2.regs, upd_same (by decide), hz]; exact BitVec.zero_add _

/-- From 0x1A66: `s0 := [sp + 0x354]`, the field's error code, then 0x1A6A. -/
theorem acb_t66 {n : Machine} {B : Word} (s : St n.mem AC n 0x1A66 (reg n))
    (C : CodeIn n.mem AC bootMainClosure0Code) (rsp : reg n sp = B + 0x3A50) :
    ∃ n', Steps n n' ∧ n'.pc = AC + 0x7D6 ∧ n'.mem = n.mem ∧
      (∀ x : Fin 32, x.val ∉ [8, 21] → reg n' x = reg n x) ∧
      reg n' (21 : Fin 32) = (n.mem (acSlot B 0x354)).zeroExtend 32 := by
  have hz := s.zero
  obtain ⟨n1, e1, s1⟩ := s.lbu C ac_at_1a66 (off' := 0x1A6A) (by decide)
  obtain ⟨n2, c2, pc2, mem2, r2, r21⟩ := acb_t6a ⟨s1.pc, rfl, fun _ => rfl⟩ (by rw [s1.mem]; exact C)
  have e : ∀ x, reg n1 x = upd (reg n) 8 ((n.mem (reg n sp + 0x354)).zeroExtend 32) x := fun x => s1.regs x
  refine ⟨n2, .cons e1 c2, pc2, by rw [mem2, s1.mem], fun x hx => ?_, ?_⟩
  · rw [r2 x (fun h => hx (by simp [h])), e, updz hz (acb_ne hx (r := 8))]
  · rw [r21, e, upd_same (by decide), rsp, BitVec.add_assoc]; rfl

end C3.RV32.Ac
