import C3BootProofs.Proofs.TufIndex
import C3BootProofs.Proofs.FlashPart

/-!
# `tuf::read_doc`, as compiled

`read_doc(src, index, i, buf)` reads document `i` of a TUF part into the
front of `buf`. It asks `Index::doc` for the document's offset and length,
fails with `Error::ScratchTooSmall` when the length is over 0x2800 bytes, the
size of `buf`, and reads the bytes through `<FlashPart as Source>::read`.
The compiled function takes the `Result<&[u8], TufError>` slot in `a0`, the
partition in `a1` and `a2`, the index in `a3`, `i` in `a4`, and `buf` in
`a5`.

`Err` is a null pointer followed by the error in one byte at offset 4.
`Check(e)` is the discriminant of `e`, so `ScratchTooSmall` is 0x13 and the
`Index::doc` errors are 5 and 6, and `Read` is 0x26.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem trd_at_0 : fetchRel tufReadDocCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem trd_at_2 : fetchRel tufReadDocCode 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem trd_at_4 : fetchRel tufReadDocCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x28, 2) := by decide
theorem trd_at_6 : fetchRel tufReadDocCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x24, 2) := by decide
theorem trd_at_8 : fetchRel tufReadDocCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x20, 2) := by decide
theorem trd_at_a : fetchRel tufReadDocCode 0xA = some (.store .sw sp (19 : Fin 32) 0x1C, 2) := by decide
theorem trd_at_c : fetchRel tufReadDocCode 0xC = some (.store .sw sp (20 : Fin 32) 0x18, 2) := by decide
theorem trd_at_e : fetchRel tufReadDocCode 0xE = some (.alu .add (18 : Fin 32) x0 a5, 2) := by decide
theorem trd_at_10 : fetchRel tufReadDocCode 0x10 = some (.alu .add (19 : Fin 32) x0 a2, 2) := by decide
theorem trd_at_12 : fetchRel tufReadDocCode 0x12 = some (.alu .add (20 : Fin 32) x0 a1, 2) := by decide
theorem trd_at_14 : fetchRel tufReadDocCode 0x14 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem trd_at_16 : fetchRel tufReadDocCode 0x16 = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem trd_at_18 : fetchRel tufReadDocCode 0x18 = some (.alu .add a1 x0 a3, 2) := by decide
theorem trd_at_1a : fetchRel tufReadDocCode 0x1A = some (.alu .add a2 x0 a4, 2) := by decide
theorem trd_at_1c : fetchRel tufReadDocCode 0x1C = some (.auipc ra 0xB000, 4) := by decide
theorem trd_at_20 : fetchRel tufReadDocCode 0x20 = some (.jalr ra ra 0x36C, 4) := by decide
theorem trd_at_24 : fetchRel tufReadDocCode 0x24 = some (.load .lbu a0 sp 0xC, 4) := by decide
theorem trd_at_28 : fetchRel tufReadDocCode 0x28 = some (.branch .beq a0 x0 0x8, 2) := by decide
theorem trd_at_2a : fetchRel tufReadDocCode 0x2A = some (.load .lbu a0 sp 0xD, 4) := by decide
theorem trd_at_2e : fetchRel tufReadDocCode 0x2E = some (.jal x0 0x32, 2) := by decide
theorem trd_at_30 : fetchRel tufReadDocCode 0x30 = some (.load .lw (9 : Fin 32) sp 0x14, 2) := by decide
theorem trd_at_32 : fetchRel tufReadDocCode 0x32 = some (.lui a0 0x3000, 2) := by decide
theorem trd_at_34 : fetchRel tufReadDocCode 0x34 = some (.aluImm .add a0 a0 0xFFFFF801, 4) := by decide
theorem trd_at_38 : fetchRel tufReadDocCode 0x38 = some (.branch .bltu (9 : Fin 32) a0 0x8, 4) := by decide
theorem trd_at_3c : fetchRel tufReadDocCode 0x3C = some (.aluImm .add a0 x0 0x13, 2) := by decide
theorem trd_at_3e : fetchRel tufReadDocCode 0x3E = some (.jal x0 0x22, 2) := by decide
theorem trd_at_40 : fetchRel tufReadDocCode 0x40 = some (.load .lw a2 sp 0x10, 2) := by decide
theorem trd_at_42 : fetchRel tufReadDocCode 0x42 = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem trd_at_44 : fetchRel tufReadDocCode 0x44 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem trd_at_46 : fetchRel tufReadDocCode 0x46 = some (.alu .add a3 x0 (18 : Fin 32), 2) := by decide
theorem trd_at_48 : fetchRel tufReadDocCode 0x48 = some (.alu .add a4 x0 (9 : Fin 32), 2) := by decide
theorem trd_at_4a : fetchRel tufReadDocCode 0x4A = some (.auipc ra 0x17000, 4) := by decide
theorem trd_at_4e : fetchRel tufReadDocCode 0x4E = some (.jalr ra ra 0xFFFFFD5A, 4) := by decide
theorem trd_at_52 : fetchRel tufReadDocCode 0x52 = some (.branch .beq a0 x0 0xA, 2) := by decide
theorem trd_at_54 : fetchRel tufReadDocCode 0x54 = some (.store .sw (8 : Fin 32) (18 : Fin 32) 0x0, 4) := by decide
theorem trd_at_58 : fetchRel tufReadDocCode 0x58 = some (.store .sw (8 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem trd_at_5a : fetchRel tufReadDocCode 0x5A = some (.jal x0 0xE, 2) := by decide
theorem trd_at_5c : fetchRel tufReadDocCode 0x5C = some (.aluImm .add a0 x0 0x26, 4) := by decide
theorem trd_at_60 : fetchRel tufReadDocCode 0x60 = some (.store .sw (8 : Fin 32) x0 0x0, 4) := by decide
theorem trd_at_64 : fetchRel tufReadDocCode 0x64 = some (.store .sb (8 : Fin 32) a0 0x4, 4) := by decide
theorem trd_at_68 : fetchRel tufReadDocCode 0x68 = some (.load .lw ra sp 0x2C, 2) := by decide
theorem trd_at_6a : fetchRel tufReadDocCode 0x6A = some (.load .lw (8 : Fin 32) sp 0x28, 2) := by decide
theorem trd_at_6c : fetchRel tufReadDocCode 0x6C = some (.load .lw (9 : Fin 32) sp 0x24, 2) := by decide
theorem trd_at_6e : fetchRel tufReadDocCode 0x6E = some (.load .lw (18 : Fin 32) sp 0x20, 2) := by decide
theorem trd_at_70 : fetchRel tufReadDocCode 0x70 = some (.load .lw (19 : Fin 32) sp 0x1C, 2) := by decide
theorem trd_at_72 : fetchRel tufReadDocCode 0x72 = some (.load .lw (20 : Fin 32) sp 0x18, 2) := by decide
theorem trd_at_74 : fetchRel tufReadDocCode 0x74 = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem trd_at_76 : fetchRel tufReadDocCode 0x76 = some (.jalr x0 ra 0x0, 2) := by decide
end

theorem idxLen_congr {M M' : Word → BitVec 8} {idx : Word}
    (h : ∀ j, j < 0x10C → M' (idx + BitVec.ofNat 32 j) = M (idx + BitVec.ofNat 32 j)) {j : Nat} (hj : j ≤ 66) :
    idxLen M' idx j = idxLen M idx j := by
  unfold idxLen
  rw [memLoad32_congr (M := M) (M' := M') (b := idx + BitVec.ofNat 32 (4 * j))
    (fun t ht => by rw [add_ofNat_assoc]; exact h _ (by omega))]

theorem idxSum_congr {M M' : Word → BitVec 8} {idx : Word}
    (h : ∀ j, j < 0x10C → M' (idx + BitVec.ofNat 32 j) = M (idx + BitVec.ofNat 32 j)) :
    ∀ f j acc, j + f ≤ 66 → idxSum M' idx j acc f = idxSum M idx j acc f
  | 0, _, _, _ => rfl
  | f + 1, j, acc, hf => by
    simp only [idxSum]
    rw [idxLen_congr h (j := j) (by omega), idxSum_congr h f (j + 1) _ (by omega)]

/-- `Index::doc` reads only the 0x10C bytes of the index. -/
theorem tufIndexDocSpec_congr {M M' : Word → BitVec 8} {idx : Word}
    (h : ∀ j, j < 0x10C → M' (idx + BitVec.ofNat 32 j) = M (idx + BitVec.ofNat 32 j)) (i : Nat) :
    tufIndexDocSpec M' idx i = tufIndexDocSpec M idx i := by
  have hc : memLoad32 M' (idx + 0x108) = memLoad32 M (idx + 0x108) :=
    memLoad32_congr fun t ht => by
      rw [show (0x108 : Word) = BitVec.ofNat 32 0x108 from rfl, add_ofNat_assoc]; exact h _ (by omega)
  unfold tufIndexDocSpec
  rw [hc]
  by_cases h1 : 0x3FFFFFFC ≤ (memLoad32 M (idx + 0x108)).toNat
  · rw [if_pos h1, if_pos h1]
  rw [if_neg h1, if_neg h1]
  by_cases h2 : 67 ≤ i
  · rw [if_pos h2, if_pos h2]
  rw [if_neg h2, if_neg h2, idxSum_congr h i 0 _ (by omega)]
  generalize idxSum M idx 0 _ i = s
  cases s with
  | none => rfl
  | some off =>
    simp only [tidTail]
    by_cases h3 : 66 < (memLoad32 M (idx + 0x108)).toNat + 2 ∨ (memLoad32 M (idx + 0x108)).toNat + 2 ≤ i
    · rw [if_pos h3, if_pos h3]
    · obtain ⟨h4, h5⟩ := not_or.mp h3
      rw [if_neg h3, if_neg h3, idxLen_congr h (j := i) (by have := Nat.lt_of_not_le h5; omega)]

theorem idxSum_lt {M : Word → BitVec 8} {idx : Word} :
    ∀ f j acc o, acc < 2 ^ 32 → idxSum M idx j acc f = some o → o < 2 ^ 32
  | 0, _, _, _, ha, h => by cases h; exact ha
  | f + 1, j, acc, o, _, h => by
    simp only [idxSum] at h
    by_cases hs : acc + idxLen M idx j < 2 ^ 32
    · rw [if_pos hs] at h; exact idxSum_lt f (j + 1) _ o hs h
    · rw [if_neg hs] at h; cases h

/-- The offset and length `Index::doc` returns fit in a word. -/
theorem tufIndexDocSpec_ok_lt {M : Word → BitVec 8} {idx : Word} {i o l : Nat}
    (h : tufIndexDocSpec M idx i = .ok (o, l)) : o < 2 ^ 32 ∧ l < 2 ^ 32 := by
  unfold tufIndexDocSpec at h
  by_cases h1 : 0x3FFFFFFC ≤ (memLoad32 M (idx + 0x108)).toNat
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : 67 ≤ i
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  have hn := Nat.lt_of_not_le h1
  cases hs : idxSum M idx 0 (8 + 4 * ((memLoad32 M (idx + 0x108)).toNat + 2)) i with
  | none => rw [hs] at h; cases h
  | some off =>
    rw [hs] at h
    simp only [tidTail] at h
    by_cases h3 : 66 < (memLoad32 M (idx + 0x108)).toNat + 2 ∨ (memLoad32 M (idx + 0x108)).toNat + 2 ≤ i
    · rw [if_pos h3] at h; cases h
    · rw [if_neg h3] at h
      obtain ⟨ho, hl⟩ := Prod.mk.inj (Except.ok.inj h)
      refine ⟨ho ▸ idxSum_lt i 0 _ off (by omega) hs, ?_⟩
      rw [← hl]; exact (memLoad32 M _).isLt

/-- An `FRdEnv` holds in memory that matches outside a range apart from
the code it names. -/
theorem FRdEnv.congr {M M' : Word → BitVec 8} {P G out len romBase : Word} {R : Nat} {romCode : List Nat}
    (env : FRdEnv M P G out len R romBase romCode) {F : Word} {k : Nat} (hM : ∀ x, Sep F k x 1 → M' x = M x)
    (s1 : Sep F k P flashReadCode.length)
    (s2 : Sep F k (P + (img% memsetAddress + 0x100000000 - flashReadAddress)) memsetCode.length)
    (s3 : Sep F k (P + 0xFFFFFFE8) romFlashReadWordsCode.length) (s4 : Sep F k romBase romCode.length) :
    FRdEnv M' P G out len R romBase romCode :=
  { env with
    code := fun i hi => by rw [hM _ (s1.subR (c := i) (l := 1) hi)]; exact env.code i hi
    mset := fun i hi => by rw [hM _ (s2.subR (c := i) (l := 1) hi)]; exact env.mset i hi
    fw := fun i hi => by rw [hM _ (s3.subR (c := i) (l := 1) hi)]; exact env.fw i hi
    rom := fun i hi => by rw [hM _ (s4.subR (c := i) (l := 1) hi)]; exact env.rom i hi }

theorem sep_front {a b : Word} {n l k : Nat} (h : Sep a n b k) (hl : l ≤ n) : Sep a l b k := by
  have := h.sub (c := 0) (l := l) (by omega); rwa [add_ofNat_zero] at this

/-- An `FRdEnv` for a buffer holds for its front. -/
theorem FRdEnv.shrink {M : Word → BitVec 8} {P G out len len' romBase : Word} {R : Nat} {romCode : List Nat}
    (env : FRdEnv M P G out len R romBase romCode) (hl : len'.toNat ≤ len.toNat) :
    FRdEnv M P G out len' R romBase romCode :=
  { env with
    hlen := by have := env.hlen; omega
    sOC := sep_front env.sOC hl
    sOW := sep_front env.sOW hl
    sOG := sep_front env.sOG hl
    sOR := sep_front env.sOR hl }

theorem trd_zx8 : ∀ b : BitVec 8, (b.zeroExtend 32).extractLsb' 0 8 = b := by decide

/-- The `Result<&[u8], TufError>` at `res` is `Err` with the error byte `e`. -/
def trdErr (M : Word → BitVec 8) (res : Word) (e : Nat) : Prop :=
  memLoad32 M res = 0 ∧ M (res + 4) = BitVec.ofNat 8 e

/-- What `tuf::read_doc` leaves at `res` when `Index::doc` returned `r`: the
`Index::doc` error, `ScratchTooSmall` (0x13) for a document over 0x2800
bytes, and then either `Read` (0x26) or `Ok` of the front of `buf` holding
the document's bytes from flash. -/
def TrdOut (flash : Nat → BitVec 8) (M : Word → BitVec 8) (res buf start plen : Word) :
    Except Nat (Nat × Nat) → Prop
  | .error e => trdErr M res e
  | .ok (o, l) => if 0x2800 < l then trdErr M res 0x13 else
      trdErr M res 0x26 ∨ (memLoad32 M res = buf ∧ memLoad32 M (res + 4) = BitVec.ofNat 32 l ∧
        o + l ≤ plen.toNat ∧ start.toNat + o < 2 ^ 32 ∧
        ∀ j, j < l → M (buf + BitVec.ofNat 32 j) = flash (start.toNat + o + j))

/-- The registers `tuf::read_doc` keeps without saving them. -/
def trKeep (q : Fin 32) : Bool :=
  romKeep q && !(q.val == 2 || q.val == 8 || q.val == 9 || (18 ≤ q.val && q.val ≤ 20))

theorem trKeep_rom : ∀ q : Fin 32, trKeep q = true → romKeep q = true := by decide

theorem trKeep_tid : ∀ q : Fin 32, trKeep q = true → tidKeep q = true := by decide

theorem trKeep_cover : ∀ q : Fin 32, romKeep q = true →
    trKeep q = true ∨ q = sp ∨ q = 8 ∨ q = 9 ∨ q = 18 ∨ q = 19 ∨ q = 20 := by decide

/-- `tuf::read_doc` returns from `n` to `retAddr` with the result for
`Index::doc`'s answer `r` at `res`. -/
def TrdPost (flash : Nat → BitVec 8) (m n : Machine) (retAddr G : Word) (R : Nat) (res buf start plen : Word)
    (r : Except Nat (Nat × Nat)) : Prop :=
  ∃ m', Steps n m' ∧ m'.pc = retAddr ∧ (∀ q, romKeep q = true → reg m' q = reg m q) ∧
    TrdOut flash m'.mem res buf start plen r ∧
    ∀ x, Sep G (0x180 + R) x 1 → Sep buf 0x2800 x 1 → Sep res 8 x 1 → m'.mem x = m.mem x

theorem TrdPost.pre {flash : Nat → BitVec 8} {m n n2 : Machine} {retAddr G : Word} {R : Nat}
    {res buf start plen : Word} {r : Except Nat (Nat × Nat)}
    (h : TrdPost flash m n2 retAddr G R res buf start plen r) (c : Steps n n2) :
    TrdPost flash m n retAddr G R res buf start plen r := by
  obtain ⟨n', c', rest⟩ := h
  exact ⟨n', c.trans c', rest⟩

/-- `tuf::read_doc` at `base`, with `Index::doc` at `base + 0xB388` and
`<FlashPart as Source>::read` at `base + 0x16DA4`, called with `sp` 0x180
bytes plus the ROM's stack above `G`. It leaves `TrdOut` for
`tufIndexDocSpec` of the index at `res`, keeps the registers the ROM call
keeps, and writes only below `sp`, `buf`, and the 8 bytes at `res`. The flash
reads follow the ROM contract `RomRead`, as in `flashPartRead_correct`. -/
theorem tufReadDoc_correct {flash : Nat → BitVec 8} {R : Nat} {romBase : Word} {romCode : List Nat}
    (hROM : RomRead flash R romBase romCode) (m : Machine)
    {base G res start plen idx iw buf retAddr : Word}
    (hc : CodeIn m.mem base tufReadDocCode) (hI : CodeIn m.mem (base + 0xB388) tufIndexDocCode)
    (hF : CodeIn m.mem (base + 0x16DA4) flashPartReadCode)
    (env : FRdEnv m.mem (base + 0x16DA4 + 0xFFFFFEA8) G buf 0x2800 R romBase romCode)
    (hbase : base.toNat % 2 = 0) (hpc : m.pc = base)
    (ha0 : reg m a0 = res) (ha1 : reg m a1 = start) (ha2 : reg m a2 = plen) (ha3 : reg m a3 = idx)
    (ha4 : reg m a4 = iw) (ha5 : reg m a5 = buf) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = G + BitVec.ofNat 32 (0x180 + R)) (hGt : G.toNat + 0x180 + R ≤ 2 ^ 32)
    (hres : res.toNat % 4 = 0) (hidx : idx.toNat % 4 = 0)
    (sGC : Sep G (0x180 + R) base tufReadDocCode.length)
    (sGI : Sep G (0x180 + R) (base + 0xB388) tufIndexDocCode.length)
    (sGF : Sep G (0x180 + R) (base + 0x16DA4) flashPartReadCode.length)
    (sGP : Sep G (0x180 + R) (base + 0x16DA4 + 0xFFFFFEA8) flashReadCode.length)
    (sGM : Sep G (0x180 + R) (base + 0x16DA4 + 0xFFFFFEA8 + (img% memsetAddress + 0x100000000 - flashReadAddress))
      memsetCode.length)
    (sGW : Sep G (0x180 + R) (base + 0x16DA4 + 0xFFFFFEA8 + 0xFFFFFFE8) romFlashReadWordsCode.length)
    (sGR : Sep G (0x180 + R) romBase romCode.length)
    (sGX : Sep G (0x180 + R) idx 0x10C) (sGO : Sep G (0x180 + R) buf 0x2800) (sGS : Sep G (0x180 + R) res 8)
    (sOC : Sep buf 0x2800 base tufReadDocCode.length) (sSC : Sep res 8 base tufReadDocCode.length)
    (sSO : Sep res 8 buf 0x2800) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ (∀ q, romKeep q = true → reg m' q = reg m q) ∧
      TrdOut flash m'.mem res buf start plen (tufIndexDocSpec m.mem idx iw.toNat) ∧
      ∀ x, Sep G (0x180 + R) x 1 → Sep buf 0x2800 x 1 → Sep res 8 x 1 → m'.mem x = m.mem x := by
  obtain ⟨F, hF0⟩ : ∃ F, G + BitVec.ofNat 32 (0x150 + R) = F := ⟨_, rfl⟩
  have hspF : reg m sp + 0xFFFFFFD0 = F := by
    rw [hsp, ← hF0, BitVec.add_assoc, show (0xFFFFFFD0 : Word) = BitVec.ofNat 32 4294967248 from rfl,
      ofNat_add_ofNat]
    rw [show BitVec.ofNat 32 (0x180 + R + 4294967248) = BitVec.ofNat 32 (0x150 + R) from
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)]
  have hspB : F + 0x30 = reg m sp := by
    rw [← hF0, show (0x30 : Word) = BitVec.ofNat 32 0x30 from rfl, add_ofNat_assoc, hsp,
      show 0x150 + R + 0x30 = 0x180 + R by omega]
  have hFa : F.toNat % 4 = 0 := by rw [← hF0]; exact aligned_add env.hG (by have := env.hR; omega)
  have al : ∀ c, c % 4 = 0 → (F + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h => aligned_add hFa h
  have fr : ∀ {b : Word} {k : Nat}, Sep G (0x180 + R) b k → Sep F 0x30 b k := fun h => by
    have := h.sub (c := 0x150 + R) (l := 0x30) (by omega); rwa [hF0] at this
  have gs : ∀ {b : Word} {k : Nat}, Sep G (0x180 + R) b k → Sep G (0x150 + R) b k := fun h => sep_front h (by omega)
  have sGFr : Sep G (0x150 + R) F 0x30 := by
    have := sep_offsets G (c := 0) (n := 0x150 + R) (d := 0x150 + R) (k := 0x30) (Or.inl (by omega)) (by omega)
      (by omega)
    rwa [add_ofNat_zero, hF0] at this
  have stF : ∀ {M : Word → BitVec 8} (c : Nat) (v : Word), c + 4 ≤ 0x30 →
      (∀ x, Sep F 0x30 x 1 → M x = m.mem x) →
      ∀ x, Sep F 0x30 x 1 → memStore32 M (F + BitVec.ofNat 32 c) v x = m.mem x :=
    fun c _ hc4 hM x hx => by rw [memStore32_get_sep (hx.sub (c := c) (l := 4) hc4)]; exact hM x hx
  have cM : ∀ {M : Word → BitVec 8}, (∀ x, Sep F 0x30 x 1 → M x = m.mem x) → CodeIn M base tufReadDocCode :=
    fun hM i hi => by rw [hM _ ((fr sGC).subR (c := i) (l := 1) hi)]; exact hc i hi
  have ps : ∀ c d, d + 4 ≤ c → c + 4 ≤ 0x30 → Sep (F + BitVec.ofNat 32 d) 4 (F + BitVec.ofNat 32 c) 4 :=
    fun c d h1 h2 => sep_offsets F (Or.inl h1) (by omega) (by omega)
  -- the prologue saves `ra` and `s0` through `s4`
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc trd_at_0 (off' := 2) (by decide)
  have g1 : reg n1 sp = F := by rw [ls_get u1 (by decide), ← hspF]; rfl
  have k1 : ∀ q, q ≠ sp → reg n1 q = reg m q := fun q h => ls_oth u1 h
  obtain ⟨n2, d2, u2⟩ := u1.self.sw hc trd_at_2 (off' := 4) (by decide) (by rw [g1]; exact al 44 (by decide))
  rw [g1, k1 ra (by decide), hra, show (0x2C : Word) = BitVec.ofNat 32 44 from rfl] at u2
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 m.mem (F + BitVec.ofNat 32 44) retAddr = M1 := ⟨_, rfl⟩
  rw [hM1] at u2
  have f1 : ∀ x, Sep F 0x30 x 1 → M1 x = m.mem x := by rw [← hM1]; exact stF 44 _ (by decide) (fun _ _ => rfl)
  obtain ⟨n3, d3, u3⟩ := u2.sw (cM f1) trd_at_4 (off' := 6) (by decide) (by rw [g1]; exact al 40 (by decide))
  rw [g1, k1 8 (by decide), show (0x28 : Word) = BitVec.ofNat 32 40 from rfl] at u3
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore32 M1 (F + BitVec.ofNat 32 40) (reg m 8) = M2 := ⟨_, rfl⟩
  rw [hM2] at u3
  have f2 : ∀ x, Sep F 0x30 x 1 → M2 x = m.mem x := by rw [← hM2]; exact stF 40 _ (by decide) f1
  obtain ⟨n4, d4, u4⟩ := u3.sw (cM f2) trd_at_6 (off' := 8) (by decide) (by rw [g1]; exact al 36 (by decide))
  rw [g1, k1 9 (by decide), show (0x24 : Word) = BitVec.ofNat 32 36 from rfl] at u4
  obtain ⟨M3, hM3⟩ : ∃ M3, memStore32 M2 (F + BitVec.ofNat 32 36) (reg m 9) = M3 := ⟨_, rfl⟩
  rw [hM3] at u4
  have f3 : ∀ x, Sep F 0x30 x 1 → M3 x = m.mem x := by rw [← hM3]; exact stF 36 _ (by decide) f2
  obtain ⟨n5, d5, u5⟩ := u4.sw (cM f3) trd_at_8 (off' := 0xA) (by decide) (by rw [g1]; exact al 32 (by decide))
  rw [g1, k1 18 (by decide), show (0x20 : Word) = BitVec.ofNat 32 32 from rfl] at u5
  obtain ⟨M4, hM4⟩ : ∃ M4, memStore32 M3 (F + BitVec.ofNat 32 32) (reg m 18) = M4 := ⟨_, rfl⟩
  rw [hM4] at u5
  have f4 : ∀ x, Sep F 0x30 x 1 → M4 x = m.mem x := by rw [← hM4]; exact stF 32 _ (by decide) f3
  obtain ⟨n6, d6, u6⟩ := u5.sw (cM f4) trd_at_a (off' := 0xC) (by decide) (by rw [g1]; exact al 28 (by decide))
  rw [g1, k1 19 (by decide), show (0x1C : Word) = BitVec.ofNat 32 28 from rfl] at u6
  obtain ⟨M5, hM5⟩ : ∃ M5, memStore32 M4 (F + BitVec.ofNat 32 28) (reg m 19) = M5 := ⟨_, rfl⟩
  rw [hM5] at u6
  have f5 : ∀ x, Sep F 0x30 x 1 → M5 x = m.mem x := by rw [← hM5]; exact stF 28 _ (by decide) f4
  obtain ⟨n7, d7, u7⟩ := u6.sw (cM f5) trd_at_c (off' := 0xE) (by decide) (by rw [g1]; exact al 24 (by decide))
  rw [g1, k1 20 (by decide), show (0x18 : Word) = BitVec.ofNat 32 24 from rfl] at u7
  obtain ⟨M6, hM6⟩ : ∃ M6, memStore32 M5 (F + BitVec.ofNat 32 24) (reg m 20) = M6 := ⟨_, rfl⟩
  rw [hM6] at u7
  have f6 : ∀ x, Sep F 0x30 x 1 → M6 x = m.mem x := by rw [← hM6]; exact stF 24 _ (by decide) f5
  have l44 : memLoad32 M6 (F + BitVec.ofNat 32 44) = retAddr := by
    rw [← hM6, memLoad32_store32_sep (ps 44 24 (by decide) (by decide)), ← hM5,
      memLoad32_store32_sep (ps 44 28 (by decide) (by decide)), ← hM4,
      memLoad32_store32_sep (ps 44 32 (by decide) (by decide)), ← hM3,
      memLoad32_store32_sep (ps 44 36 (by decide) (by decide)), ← hM2,
      memLoad32_store32_sep (ps 44 40 (by decide) (by decide)), ← hM1, memLoad32_store32_same]
  have l40 : memLoad32 M6 (F + BitVec.ofNat 32 40) = reg m 8 := by
    rw [← hM6, memLoad32_store32_sep (ps 40 24 (by decide) (by decide)), ← hM5,
      memLoad32_store32_sep (ps 40 28 (by decide) (by decide)), ← hM4,
      memLoad32_store32_sep (ps 40 32 (by decide) (by decide)), ← hM3,
      memLoad32_store32_sep (ps 40 36 (by decide) (by decide)), ← hM2, memLoad32_store32_same]
  have l36 : memLoad32 M6 (F + BitVec.ofNat 32 36) = reg m 9 := by
    rw [← hM6, memLoad32_store32_sep (ps 36 24 (by decide) (by decide)), ← hM5,
      memLoad32_store32_sep (ps 36 28 (by decide) (by decide)), ← hM4,
      memLoad32_store32_sep (ps 36 32 (by decide) (by decide)), ← hM3, memLoad32_store32_same]
  have l32 : memLoad32 M6 (F + BitVec.ofNat 32 32) = reg m 18 := by
    rw [← hM6, memLoad32_store32_sep (ps 32 24 (by decide) (by decide)), ← hM5,
      memLoad32_store32_sep (ps 32 28 (by decide) (by decide)), ← hM4, memLoad32_store32_same]
  have l28 : memLoad32 M6 (F + BitVec.ofNat 32 28) = reg m 19 := by
    rw [← hM6, memLoad32_store32_sep (ps 28 24 (by decide) (by decide)), ← hM5, memLoad32_store32_same]
  have l24 : memLoad32 M6 (F + BitVec.ofNat 32 24) = reg m 20 := by
    rw [← hM6, memLoad32_store32_same]
  -- setup: `s2 = buf`, `s3 = plen`, `s4 = start`, `s0 = res`, then the `Index::doc` arguments
  have kk1 : ∀ q, trKeep q = true → reg n1 q = reg m q := ls_kst u1 (by decide) (fun _ _ => rfl)
  have hc6 := cM f6
  obtain ⟨n8, d8, u8⟩ := u7.alu hc6 trd_at_e (off' := 0x10) (by decide)
  obtain ⟨n9, d9, u9⟩ := u8.self.alu hc6 trd_at_10 (off' := 0x12) (by decide)
  obtain ⟨n10, d10, u10⟩ := u9.self.alu hc6 trd_at_12 (off' := 0x14) (by decide)
  obtain ⟨n11, d11, u11⟩ := u10.self.alu hc6 trd_at_14 (off' := 0x16) (by decide)
  obtain ⟨n12, d12, u12⟩ := u11.self.aluImm hc6 trd_at_16 (off' := 0x18) (by decide)
  obtain ⟨n13, d13, u13⟩ := u12.self.alu hc6 trd_at_18 (off' := 0x1A) (by decide)
  obtain ⟨n14, d14, u14⟩ := u13.self.alu hc6 trd_at_1a (off' := 0x1C) (by decide)
  have kk14 : ∀ q, trKeep q = true → reg n14 q = reg m q :=
    ls_kst u14 (by decide) (ls_kst u13 (by decide) (ls_kst u12 (by decide) (ls_kst u11 (by decide)
      (ls_kst u10 (by decide) (ls_kst u9 (by decide) (ls_kst u8 (by decide) kk1))))))
  have r14sp : reg n14 sp = F := by
    rw [ls_oth u14 (show sp ≠ a2 by decide), ls_oth u13 (show sp ≠ a1 by decide),
      ls_oth u12 (show sp ≠ a0 by decide), ls_oth u11 (show sp ≠ 8 by decide), ls_oth u10 (show sp ≠ 20 by decide),
      ls_oth u9 (show sp ≠ 19 by decide), ls_oth u8 (show sp ≠ 18 by decide), g1]
  have r14s0 : reg n14 8 = res := by
    rw [ls_oth u14 (show (8 : Fin 32) ≠ a2 by decide), ls_oth u13 (show (8 : Fin 32) ≠ a1 by decide),
      ls_oth u12 (show (8 : Fin 32) ≠ a0 by decide), ls_get u11 (by decide), ls_r0,
      ls_oth u10 (show a0 ≠ 20 by decide), ls_oth u9 (show a0 ≠ 19 by decide), ls_oth u8 (show a0 ≠ 18 by decide),
      k1 a0 (by decide), ha0]
    exact BitVec.zero_add _
  have r14s2 : reg n14 18 = buf := by
    rw [ls_oth u14 (show (18 : Fin 32) ≠ a2 by decide), ls_oth u13 (show (18 : Fin 32) ≠ a1 by decide),
      ls_oth u12 (show (18 : Fin 32) ≠ a0 by decide), ls_oth u11 (show (18 : Fin 32) ≠ 8 by decide),
      ls_oth u10 (show (18 : Fin 32) ≠ 20 by decide), ls_oth u9 (show (18 : Fin 32) ≠ 19 by decide),
      ls_get u8 (by decide), ls_r0, k1 a5 (by decide), ha5]
    exact BitVec.zero_add _
  have r14s3 : reg n14 19 = plen := by
    rw [ls_oth u14 (show (19 : Fin 32) ≠ a2 by decide), ls_oth u13 (show (19 : Fin 32) ≠ a1 by decide),
      ls_oth u12 (show (19 : Fin 32) ≠ a0 by decide), ls_oth u11 (show (19 : Fin 32) ≠ 8 by decide),
      ls_oth u10 (show (19 : Fin 32) ≠ 20 by decide), ls_get u9 (by decide), ls_r0,
      ls_oth u8 (show a2 ≠ 18 by decide), k1 a2 (by decide), ha2]
    exact BitVec.zero_add _
  have r14s4 : reg n14 20 = start := by
    rw [ls_oth u14 (show (20 : Fin 32) ≠ a2 by decide), ls_oth u13 (show (20 : Fin 32) ≠ a1 by decide),
      ls_oth u12 (show (20 : Fin 32) ≠ a0 by decide), ls_oth u11 (show (20 : Fin 32) ≠ 8 by decide),
      ls_get u10 (by decide), ls_r0, ls_oth u9 (show a1 ≠ 19 by decide), ls_oth u8 (show a1 ≠ 18 by decide),
      k1 a1 (by decide), ha1]
    exact BitVec.zero_add _
  have r14a0 : reg n14 a0 = F + BitVec.ofNat 32 12 := by
    rw [ls_oth u14 (show a0 ≠ a2 by decide), ls_oth u13 (show a0 ≠ a1 by decide), ls_get u12 (by decide),
      ls_oth u11 (show sp ≠ 8 by decide), ls_oth u10 (show sp ≠ 20 by decide),
      ls_oth u9 (show sp ≠ 19 by decide), ls_oth u8 (show sp ≠ 18 by decide), g1]
    rfl
  have r14a1 : reg n14 a1 = idx := by
    rw [ls_oth u14 (show a1 ≠ a2 by decide), ls_get u13 (by decide), ls_r0,
      ls_oth u12 (show a3 ≠ a0 by decide), ls_oth u11 (show a3 ≠ 8 by decide), ls_oth u10 (show a3 ≠ 20 by decide),
      ls_oth u9 (show a3 ≠ 19 by decide), ls_oth u8 (show a3 ≠ 18 by decide), k1 a3 (by decide), ha3]
    exact BitVec.zero_add _
  have r14a2 : reg n14 a2 = iw := by
    rw [ls_get u14 (by decide), ls_r0, ls_oth u13 (show a4 ≠ a1 by decide),
      ls_oth u12 (show a4 ≠ a0 by decide), ls_oth u11 (show a4 ≠ 8 by decide), ls_oth u10 (show a4 ≠ 20 by decide),
      ls_oth u9 (show a4 ≠ 19 by decide), ls_oth u8 (show a4 ≠ 18 by decide), k1 a4 (by decide), ha4]
    exact BitVec.zero_add _
  -- the call of `Index::doc`
  obtain ⟨c1, e1, pc1, mem1, regs1⟩ := u14.self.callRa hc6 trd_at_1c trd_at_20
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hbase 0xB388 (by decide))
  have q1 := PEnv.reg1 regs1 u14.self.zero
  have hX6 : ∀ j, j < 0x10C → M6 (idx + BitVec.ofNat 32 j) = m.mem (idx + BitVec.ofNat 32 j) :=
    fun j hj => f6 _ ((fr sGX).subR (c := j) (l := 1) hj)
  obtain ⟨m3, e3, pc3, kt3, mem3, out3⟩ := tufIndexDoc_correct c1 (base := base + 0xB388)
    (by rw [mem1]; exact fun i hi => by rw [f6 _ ((fr sGI).subR (c := i) (l := 1) hi)]; exact hI i hi)
    (even_at base hbase 0xB388 (by decide)) pc1
    (by rw [q1 a0 (by decide), r14a0]) (by rw [q1 a1 (by decide), r14a1]) (by rw [q1 a2 (by decide), r14a2])
    (al 12 (by decide)) hidx ((fr sGI).sub (c := 12) (l := 12) (by decide))
    (by rw [regs1]; simp +decide [upd]) (even_clear _ (even_at base hbase (0x1C + 8) (by decide)))
  rw [mem1, tufIndexDocSpec_congr hX6] at out3
  rw [mem1] at mem3
  obtain ⟨M7, hM7⟩ : ∃ M7, m3.mem = M7 := ⟨_, rfl⟩
  rw [hM7] at mem3 out3
  have fM7 : ∀ x, Sep F 0x30 x 1 → M7 x = m.mem x := fun x hx => by
    rw [mem3 x (hx.sub (c := 12) (l := 12) (by decide)), f6 x hx]
  have sl7 : ∀ c, 24 ≤ c → c + 4 ≤ 0x30 →
      memLoad32 M7 (F + BitVec.ofNat 32 c) = memLoad32 M6 (F + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]
      exact mem3 _ (sep_offsets F (c := 12) (n := 12) (d := c + j) (k := 1) (Or.inl (by omega)) (by omega) (by omega))
  have st3 : St M7 base m3 0x24 (reg m3) := ⟨by rw [pc3], hM7, fun _ => rfl⟩
  have q3 : ∀ q, trKeep q = true → reg m3 q = reg n14 q := fun q hq => by
    rw [kt3 q (trKeep_tid q hq), q1 q (fun e => by subst e; exact absurd hq (by decide))]
  have r3 : ∀ q : Fin 32, q.val < 11 → q ≠ ra → reg m3 q = reg n14 q := fun q h1 h2 => by
    rw [kt3 q (by simp [tidKeep, h1]), q1 q h2]
  -- the epilogue at 0x68
  have tail : ∀ {n : Machine} {M : Word → BitVec 8}, CodeIn M base tufReadDocCode →
      (∀ c, 24 ≤ c → c + 4 ≤ 0x30 → memLoad32 M (F + BitVec.ofNat 32 c) = memLoad32 M7 (F + BitVec.ofNat 32 c)) →
      St M base n 0x68 (reg n) → reg n sp = F → (∀ q, trKeep q = true → reg n q = reg m q) →
      ∃ n', Steps n n' ∧ n'.pc = retAddr ∧ n'.mem = M ∧ ∀ q, romKeep q = true → reg n' q = reg m q := by
    intro n M hcM sS st hs kk
    have sl : ∀ c, 24 ≤ c → c + 4 ≤ 0x30 →
        memLoad32 M (F + BitVec.ofNat 32 c) = memLoad32 M6 (F + BitVec.ofNat 32 c) :=
      fun c h1 h2 => (sS c h1 h2).trans (sl7 c h1 h2)
    obtain ⟨t1, e1, v1⟩ := st.lw hcM trd_at_68 (off' := 0x6A) (by decide) (by rw [hs]; exact al 44 (by decide))
    rw [hs, show (0x2C : Word) = BitVec.ofNat 32 44 from rfl, sl 44 (by decide) (by decide), l44] at v1
    have w1 : reg t1 sp = F := by rw [ls_oth v1 (show sp ≠ ra by decide), hs]
    obtain ⟨t2, e2, v2⟩ := v1.self.lw hcM trd_at_6a (off' := 0x6C) (by decide) (by rw [w1]; exact al 40 (by decide))
    rw [w1, show (0x28 : Word) = BitVec.ofNat 32 40 from rfl, sl 40 (by decide) (by decide), l40] at v2
    have w2 : reg t2 sp = F := by rw [ls_oth v2 (show sp ≠ 8 by decide), w1]
    obtain ⟨t3, e3, v3⟩ := v2.self.lw hcM trd_at_6c (off' := 0x6E) (by decide) (by rw [w2]; exact al 36 (by decide))
    rw [w2, show (0x24 : Word) = BitVec.ofNat 32 36 from rfl, sl 36 (by decide) (by decide), l36] at v3
    have w3 : reg t3 sp = F := by rw [ls_oth v3 (show sp ≠ 9 by decide), w2]
    obtain ⟨t4, e4, v4⟩ := v3.self.lw hcM trd_at_6e (off' := 0x70) (by decide) (by rw [w3]; exact al 32 (by decide))
    rw [w3, show (0x20 : Word) = BitVec.ofNat 32 32 from rfl, sl 32 (by decide) (by decide), l32] at v4
    have w4 : reg t4 sp = F := by rw [ls_oth v4 (show sp ≠ 18 by decide), w3]
    obtain ⟨t5, e5, v5⟩ := v4.self.lw hcM trd_at_70 (off' := 0x72) (by decide) (by rw [w4]; exact al 28 (by decide))
    rw [w4, show (0x1C : Word) = BitVec.ofNat 32 28 from rfl, sl 28 (by decide) (by decide), l28] at v5
    have w5 : reg t5 sp = F := by rw [ls_oth v5 (show sp ≠ 19 by decide), w4]
    obtain ⟨t6, e6, v6⟩ := v5.self.lw hcM trd_at_72 (off' := 0x74) (by decide) (by rw [w5]; exact al 24 (by decide))
    rw [w5, show (0x18 : Word) = BitVec.ofNat 32 24 from rfl, sl 24 (by decide) (by decide), l24] at v6
    obtain ⟨t7, e7, v7⟩ := v6.self.aluImm hcM trd_at_74 (off' := 0x76) (by decide)
    have w7 : reg t7 sp = reg m sp := by
      rw [ls_get v7 (by decide), ls_oth v6 (show sp ≠ 20 by decide), w5, ← hspB]; rfl
    obtain ⟨t8, e8, pc8, mem8, regs8⟩ := v7.self.jalr hcM trd_at_76
    have kk7 : ∀ q, trKeep q = true → reg t7 q = reg m q :=
      ls_kst v7 (by decide) (ls_kst v6 (by decide) (ls_kst v5 (by decide) (ls_kst v4 (by decide)
        (ls_kst v3 (by decide) (ls_kst v2 (by decide) (ls_kst v1 (by decide) kk))))))
    refine ⟨t8, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.single e8))))))), ?_, mem8,
      fun q hq => ?_⟩
    · rw [pc8, ls_oth v7 (show ra ≠ sp by decide), ls_oth v6 (show ra ≠ 20 by decide),
        ls_oth v5 (show ra ≠ 19 by decide), ls_oth v4 (show ra ≠ 18 by decide), ls_oth v3 (show ra ≠ 9 by decide),
        ls_oth v2 (show ra ≠ 8 by decide), ls_get v1 (by decide), add_lit_zero, hret]
    rw [regs8]
    rcases trKeep_cover q hq with h | rfl | rfl | rfl | rfl | rfl | rfl
    · exact kk7 q h
    · exact w7
    · rw [ls_oth v7 (show (8 : Fin 32) ≠ sp by decide), ls_oth v6 (show (8 : Fin 32) ≠ 20 by decide),
        ls_oth v5 (show (8 : Fin 32) ≠ 19 by decide), ls_oth v4 (show (8 : Fin 32) ≠ 18 by decide),
        ls_oth v3 (show (8 : Fin 32) ≠ 9 by decide), ls_get v2 (by decide)]
    · rw [ls_oth v7 (show (9 : Fin 32) ≠ sp by decide), ls_oth v6 (show (9 : Fin 32) ≠ 20 by decide),
        ls_oth v5 (show (9 : Fin 32) ≠ 19 by decide), ls_oth v4 (show (9 : Fin 32) ≠ 18 by decide),
        ls_get v3 (by decide)]
    · rw [ls_oth v7 (show (18 : Fin 32) ≠ sp by decide), ls_oth v6 (show (18 : Fin 32) ≠ 20 by decide),
        ls_oth v5 (show (18 : Fin 32) ≠ 19 by decide), ls_get v4 (by decide)]
    · rw [ls_oth v7 (show (19 : Fin 32) ≠ sp by decide), ls_oth v6 (show (19 : Fin 32) ≠ 20 by decide),
        ls_get v5 (by decide)]
    · rw [ls_oth v7 (show (20 : Fin 32) ≠ sp by decide), ls_get v6 (by decide)]
  -- `res` and the frame
  have rF : ∀ c d l, c + l ≤ 8 → d + 4 ≤ 0x30 → Sep (res + BitVec.ofNat 32 c) l (F + BitVec.ofNat 32 d) 4 :=
    fun c d l h1 h2 => ((fr sGS).symm.sub (c := c) (l := l) h1).subR (c := d) (l := 4) h2
  have rF0 : ∀ d, d + 4 ≤ 0x30 → Sep res 4 (F + BitVec.ofNat 32 d) 4 := fun d h => by
    have := rF 0 d 4 (by decide) h; rwa [add_ofNat_zero] at this
  have r40 : Sep (res + BitVec.ofNat 32 4) 4 res 4 := by
    have := sep_offsets res (c := 4) (n := 4) (d := 0) (k := 4) (Or.inr (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have cAg : ∀ {M : Word → BitVec 8}, (∀ x, Sep G (0x180 + R) x 1 → Sep buf 0x2800 x 1 → M x = m.mem x) →
      CodeIn M base tufReadDocCode := fun hAg i hi => by
    rw [hAg _ (sGC.subR (c := i) (l := 1) hi) (sOC.subR (c := i) (l := 1) hi)]; exact hc i hi
  -- the `Err` exit at 0x60, with the error byte in `a0`
  have errX : ∀ {n : Machine} {M : Word → BitVec 8} {w : Word} {r : Except Nat (Nat × Nat)} (e : Nat),
      (∀ M', trdErr M' res e → TrdOut flash M' res buf start plen r) →
      (∀ x, Sep G (0x180 + R) x 1 → Sep buf 0x2800 x 1 → M x = m.mem x) →
      (∀ c, 24 ≤ c → c + 4 ≤ 0x30 → memLoad32 M (F + BitVec.ofNat 32 c) = memLoad32 M7 (F + BitVec.ofNat 32 c)) →
      St M base n 0x60 (reg n) → reg n sp = F → reg n 8 = res → reg n a0 = w →
      w.extractLsb' 0 8 = BitVec.ofNat 8 e → (∀ q, trKeep q = true → reg n q = reg m q) →
      TrdPost flash m n retAddr G R res buf start plen r := by
    intro n M w r e hout hAg sS st hs h8 hw hwe kk
    have hcM := cAg hAg
    obtain ⟨n1, d1, u1⟩ := st.sw hcM trd_at_60 (off' := 0x64) (by decide) (by rw [h8, add_lit_zero]; exact hres)
    rw [h8, add_lit_zero, ls_r0] at u1
    obtain ⟨n2, d2, u2⟩ := u1.sb (hcM.store32 (sep_front sSC (by decide))) trd_at_64 (off' := 0x68) (by decide)
    rw [h8, hw, hwe, show (0x4 : Word) = BitVec.ofNat 32 4 from rfl] at u2
    have hc2 : CodeIn (memStore8 (memStore32 M res 0) (res + BitVec.ofNat 32 4) (BitVec.ofNat 8 e)) base
        tufReadDocCode := (hcM.store32 (sep_front sSC (by decide))).store8 (sSC.sub (c := 4) (l := 1) (by decide))
    obtain ⟨n', c', pc', mem', kr'⟩ := tail hc2 (fun c h1 h2 => by
        rw [memLoad32_store8_sep (rF 4 c 1 (by decide) h2), memLoad32_store32_sep (rF0 c h2)]; exact sS c h1 h2)
      u2.self (by rw [u2.regs, hs]) (ls_kbr u2 kk)
    refine ⟨n', .cons d1 (.cons d2 c'), pc', kr', hout _ ⟨?_, ?_⟩, fun x h1 h2 h3 => ?_⟩
    · rw [mem', memLoad32_store8_sep (sep_front r40 (by decide)), memLoad32_store32_same]
    · rw [mem']; exact memStore8_same _ _ _
    · rw [mem', memStore8_ne (ls_sep_ne h3 (i := 4) (by decide)), memStore32_get_sep (sep_front h3 (by decide))]
      exact hAg x h1 h2
  have pre : Steps m m3 := (Steps.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8
    (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.single d14)))))))))))))).trans (e1.trans e3)
  refine TrdPost.pre ?_ pre
  have hs3 : reg m3 sp = F := by rw [r3 sp (by decide) (by decide), r14sp]
  have r3s0 : reg m3 8 = res := by rw [r3 8 (by decide) (by decide), r14s0]
  have r3s2 : reg m3 18 = buf := by rw [kt3 18 (by decide), q1 18 (by decide), r14s2]
  have r3s3 : reg m3 19 = plen := by rw [kt3 19 (by decide), q1 19 (by decide), r14s3]
  have r3s4 : reg m3 20 = start := by rw [kt3 20 (by decide), q1 20 (by decide), r14s4]
  have kk3 : ∀ q, trKeep q = true → reg m3 q = reg m q := fun q hq => by rw [q3 q hq, kk14 q hq]
  have ag7 : ∀ x, Sep G (0x180 + R) x 1 → Sep buf 0x2800 x 1 → M7 x = m.mem x := fun x h1 _ => fM7 x (fr h1)
  have hc7 := cM fM7
  -- the tag of `Index::doc`'s result
  obtain ⟨t1, z1, y1⟩ := st3.lbu hc7 trd_at_24 (off' := 0x28) (by decide)
  rw [hs3, show (0xC : Word) = BitVec.ofNat 32 12 from rfl] at y1
  have w1 : ∀ q, q ≠ a0 → reg t1 q = reg m3 q := fun q h => ls_oth y1 h
  have kk1' : ∀ q, trKeep q = true → reg t1 q = reg m q := ls_kst y1 (by decide) kk3
  generalize hr : tufIndexDocSpec m.mem idx iw.toNat = r at out3
  cases r with
  | error e =>
    obtain ⟨h0, h1⟩ := out3
    rw [h0] at y1
    obtain ⟨t2, z2, y2⟩ := y1.self.notTaken hc7 0x2A trd_at_28 (by decide)
      (by rw [ls_get y1 (by decide), ls_r0]; rfl)
    obtain ⟨t3, z3, y3⟩ := y2.lbu hc7 trd_at_2a (off' := 0x2E) (by decide)
    rw [w1 sp (by decide), hs3, show F + (0xD : Word) = F + BitVec.ofNat 32 12 + 1 by rw [BitVec.add_assoc]; rfl,
      h1] at y3
    obtain ⟨t4, z4, y4⟩ := y3.self.jump hc7 trd_at_2e (off' := 0x60) (by decide)
      (by rw [y3.pc]; exact ls_even hbase 0x2E 0x32 0x60 (by decide) (by decide))
    exact TrdPost.pre (errX (w := (BitVec.ofNat 8 e).zeroExtend 32) e (fun _ h => h) ag7 (fun _ _ _ => rfl) y4.self
      (by rw [y4.regs, ls_oth y3 (show sp ≠ a0 by decide), w1 sp (by decide), hs3])
      (by rw [y4.regs, ls_oth y3 (show (8 : Fin 32) ≠ a0 by decide), w1 8 (by decide), r3s0])
      (by rw [y4.regs, ls_get y3 (by decide)]) (trd_zx8 _) (ls_kbr y4 (ls_kst y3 (by decide) kk1')))
      (.cons z1 (.cons z2 (.cons z3 (.single z4))))
  | ok ol =>
    obtain ⟨o, l⟩ := ol
    obtain ⟨h0, ho, hl⟩ := out3
    obtain ⟨ho32, hl32⟩ := tufIndexDocSpec_ok_lt hr
    rw [h0] at y1
    obtain ⟨t2, z2, y2⟩ := y1.self.taken hc7 0x30 trd_at_28 (by decide) (by rw [ls_get y1 (by decide), ls_r0]; rfl)
    obtain ⟨t3, z3, y3⟩ := y2.lw hc7 trd_at_30 (off' := 0x32) (by decide)
      (by rw [w1 sp (by decide), hs3]; exact al 20 (by decide))
    rw [w1 sp (by decide), hs3, show F + (0x14 : Word) = F + BitVec.ofNat 32 12 + 8 by rw [BitVec.add_assoc]; rfl,
      hl] at y3
    obtain ⟨t4, z4, y4⟩ := y3.self.lui hc7 trd_at_32 (off' := 0x34) (by decide)
    obtain ⟨t5, z5, y5⟩ := y4.self.aluImm hc7 trd_at_34 (off' := 0x38) (by decide)
    have w5a0 : reg t5 a0 = BitVec.ofNat 32 0x2801 := by rw [ls_get y5 (by decide), ls_get y4 (by decide)]; rfl
    have w5s1 : reg t5 9 = BitVec.ofNat 32 l := by
      rw [ls_oth y5 (show (9 : Fin 32) ≠ a0 by decide), ls_oth y4 (show (9 : Fin 32) ≠ a0 by decide),
        ls_get y3 (by decide)]
    have w5 : ∀ q, q ≠ a0 → q ≠ 9 → reg t5 q = reg m3 q := fun q h1 h2 => by
      rw [ls_oth y5 h1, ls_oth y4 h1, ls_oth y3 h2, w1 q h1]
    have kk5 : ∀ q, trKeep q = true → reg t5 q = reg m q :=
      ls_kst y5 (by decide) (ls_kst y4 (by decide) (ls_kst y3 (by decide) kk1'))
    by_cases hbig : 0x2800 < l
    · -- too long for `buf`
      obtain ⟨t6, z6, y6⟩ := y5.self.notTaken hc7 0x3C trd_at_38 (by decide) (by
        rw [ls_ult, w5s1, w5a0, ls_ofNat_toNat_lt hl32, ls_ofNat_toNat_lt (c := 0x2801) (by decide)]
        exact decide_eq_false (by omega))
      obtain ⟨t7, z7, y7⟩ := y6.aluImm hc7 trd_at_3c (off' := 0x3E) (by decide)
      obtain ⟨t8, z8, y8⟩ := y7.self.jump hc7 trd_at_3e (off' := 0x60) (by decide)
        (by rw [y7.pc]; exact ls_even hbase 0x3E 0x22 0x60 (by decide) (by decide))
      exact TrdPost.pre (errX (w := BitVec.ofNat 32 0x13) 0x13
        (fun M' h => by simp only [TrdOut]; rw [if_pos hbig]; exact h) ag7 (fun _ _ _ => rfl) y8.self
        (by rw [y8.regs, ls_oth y7 (show sp ≠ a0 by decide), w5 sp (by decide) (by decide), hs3])
        (by rw [y8.regs, ls_oth y7 (show (8 : Fin 32) ≠ a0 by decide), w5 8 (by decide) (by decide), r3s0])
        (by rw [y8.regs, ls_get y7 (by decide), ls_r0]; rfl) (ls_byte (by decide))
        (ls_kbr y8 (ls_kst y7 (by decide) kk5)))
        (.cons z1 (.cons z2 (.cons z3 (.cons z4 (.cons z5 (.cons z6 (.cons z7 (.single z8))))))))
    have hle : l ≤ 0x2800 := Nat.le_of_not_lt hbig
    obtain ⟨t6, z6, y6⟩ := y5.self.taken hc7 0x40 trd_at_38 (by decide) (by
      rw [ls_ult, w5s1, w5a0, ls_ofNat_toNat_lt hl32, ls_ofNat_toNat_lt (c := 0x2801) (by decide)]
      exact decide_eq_true (by omega))
    obtain ⟨t7, z7, y7⟩ := y6.lw hc7 trd_at_40 (off' := 0x42) (by decide)
      (by rw [w5 sp (by decide) (by decide), hs3]; exact al 16 (by decide))
    rw [w5 sp (by decide) (by decide), hs3,
      show F + (0x10 : Word) = F + BitVec.ofNat 32 12 + 4 by rw [BitVec.add_assoc]; rfl, ho] at y7
    obtain ⟨t8, z8, y8⟩ := y7.self.alu hc7 trd_at_42 (off' := 0x44) (by decide)
    obtain ⟨t9, z9, y9⟩ := y8.self.alu hc7 trd_at_44 (off' := 0x46) (by decide)
    obtain ⟨t10, z10, y10⟩ := y9.self.alu hc7 trd_at_46 (off' := 0x48) (by decide)
    obtain ⟨t11, z11, y11⟩ := y10.self.alu hc7 trd_at_48 (off' := 0x4A) (by decide)
    have w11 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → reg t11 q = reg t5 q :=
      fun q h0 h1 h2 h3 h4 => by rw [ls_oth y11 h4, ls_oth y10 h3, ls_oth y9 h1, ls_oth y8 h0, ls_oth y7 h2]
    have kk11 : ∀ q, trKeep q = true → reg t11 q = reg m q :=
      ls_kst y11 (by decide) (ls_kst y10 (by decide) (ls_kst y9 (by decide) (ls_kst y8 (by decide)
        (ls_kst y7 (by decide) kk5))))
    -- the call of `<FlashPart as Source>::read`
    obtain ⟨c2, f2, pc2, mem2, regs2⟩ := y11.self.callRa hc7 trd_at_4a trd_at_4e
      (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hbase 0x16DA4 (by decide))
    have q2 := PEnv.reg1 regs2 y11.self.zero
    have envL : FRdEnv c2.mem (base + 0x16DA4 + 0xFFFFFEA8) G buf (BitVec.ofNat 32 l) R romBase romCode := by
      rw [mem2]
      exact (env.congr fM7 (fr sGP) (fr sGM) (fr sGW) (fr sGR)).shrink (by rw [ls_ofNat_toNat_lt hl32]; exact hle)
    obtain ⟨m4, f4, pc4, -, kr4, a04, ok4, mem4⟩ := flashPartRead_correct hROM c2 (base := base + 0x16DA4)
      (start := start) (plen := plen) (off := BitVec.ofNat 32 o) (retAddr := base + BitVec.ofNat 32 (0x4A + 8))
      (by rw [mem2]; exact fun i hi => by rw [fM7 _ ((fr sGF).subR (c := i) (l := 1) hi)]; exact hF i hi)
      envL pc2
      (by rw [q2 a0 (by decide), ls_oth y11 (show a0 ≠ a4 by decide), ls_oth y10 (show a0 ≠ a3 by decide),
        ls_oth y9 (show a0 ≠ a1 by decide), ls_get y8 (by decide), ls_r0, ls_oth y7 (show (20 : Fin 32) ≠ a2 by decide),
        w5 20 (by decide) (by decide), r3s4]; exact BitVec.zero_add _)
      (by rw [q2 a1 (by decide), ls_oth y11 (show a1 ≠ a4 by decide), ls_oth y10 (show a1 ≠ a3 by decide),
        ls_get y9 (by decide), ls_r0, ls_oth y8 (show (19 : Fin 32) ≠ a0 by decide),
        ls_oth y7 (show (19 : Fin 32) ≠ a2 by decide), w5 19 (by decide) (by decide), r3s3]; exact BitVec.zero_add _)
      (by rw [q2 a2 (by decide), ls_oth y11 (show a2 ≠ a4 by decide), ls_oth y10 (show a2 ≠ a3 by decide),
        ls_oth y9 (show a2 ≠ a1 by decide), ls_oth y8 (show a2 ≠ a0 by decide), ls_get y7 (by decide)])
      (by rw [q2 a3 (by decide), ls_oth y11 (show a3 ≠ a4 by decide), ls_get y10 (by decide), ls_r0,
        ls_oth y9 (show (18 : Fin 32) ≠ a1 by decide), ls_oth y8 (show (18 : Fin 32) ≠ a0 by decide),
        ls_oth y7 (show (18 : Fin 32) ≠ a2 by decide), w5 18 (by decide) (by decide), r3s2]; exact BitVec.zero_add _)
      (by rw [q2 a4 (by decide), ls_get y11 (by decide), ls_r0, ls_oth y10 (show (9 : Fin 32) ≠ a3 by decide),
        ls_oth y9 (show (9 : Fin 32) ≠ a1 by decide), ls_oth y8 (show (9 : Fin 32) ≠ a0 by decide),
        ls_oth y7 (show (9 : Fin 32) ≠ a2 by decide), w5s1]; exact BitVec.zero_add _)
      (by rw [regs2]; simp +decide [upd]) (even_clear _ (even_at base hbase (0x4A + 8) (by decide)))
      (by rw [q2 sp (by decide), w11 sp (by decide) (by decide) (by decide) (by decide) (by decide),
        w5 sp (by decide) (by decide), hs3, hF0])
    rw [ls_ofNat_toNat_lt ho32, ls_ofNat_toNat_lt hl32] at ok4
    rw [ls_ofNat_toNat_lt hl32, mem2] at mem4
    have ag8 : ∀ x, Sep G (0x180 + R) x 1 → Sep buf 0x2800 x 1 → m4.mem x = m.mem x := fun x h1 h2 => by
      rw [mem4 x (gs h1) (sep_front h2 hle)]; exact fM7 x (fr h1)
    have sl8 : ∀ c, 24 ≤ c → c + 4 ≤ 0x30 →
        memLoad32 m4.mem (F + BitVec.ofNat 32 c) = memLoad32 M7 (F + BitVec.ofNat 32 c) :=
      fun c h1 h2 => memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]
        exact mem4 _ (sGFr.subR (c := c + j) (l := 1) (by omega))
          (sep_front ((fr sGO).symm.subR (c := c + j) (l := 1) (by omega)) hle)
    have st4 : St m4.mem base m4 0x52 (reg m4) := ⟨by rw [pc4], rfl, fun _ => rfl⟩
    have hc8 := cAg ag8
    have r4 : ∀ q, romKeep q = true → reg m4 q = reg t11 q := fun q hq => by
      rw [kr4 q hq, q2 q (fun e => by subst e; exact absurd hq (by decide))]
    have s4sp : reg m4 sp = F := by
      rw [r4 sp (by decide), w11 sp (by decide) (by decide) (by decide) (by decide) (by decide),
        w5 sp (by decide) (by decide), hs3]
    have s4s0 : reg m4 8 = res := by
      rw [r4 8 (by decide), w11 8 (by decide) (by decide) (by decide) (by decide) (by decide),
        w5 8 (by decide) (by decide), r3s0]
    have s4s2 : reg m4 18 = buf := by
      rw [r4 18 (by decide), w11 18 (by decide) (by decide) (by decide) (by decide) (by decide),
        w5 18 (by decide) (by decide), r3s2]
    have s4s1 : reg m4 9 = BitVec.ofNat 32 l := by
      rw [r4 9 (by decide), w11 9 (by decide) (by decide) (by decide) (by decide) (by decide), w5s1]
    have kk4 : ∀ q, trKeep q = true → reg m4 q = reg m q := fun q hq => by
      rw [r4 q (trKeep_rom q hq), kk11 q hq]
    have pre4 : Steps m3 m4 := (Steps.cons z1 (.cons z2 (.cons z3 (.cons z4 (.cons z5 (.cons z6 (.cons z7
      (.cons z8 (.cons z9 (.cons z10 (.cons z11 f2))))))))))).trans f4
    refine TrdPost.pre ?_ pre4
    rcases a04 with h | h
    · -- the read failed
      obtain ⟨t12, z12, y12⟩ := st4.taken hc8 0x5C trd_at_52 (by decide) (by rw [h, ls_r0]; rfl)
      obtain ⟨t13, z13, y13⟩ := y12.aluImm hc8 trd_at_5c (off' := 0x60) (by decide)
      exact TrdPost.pre (errX (w := BitVec.ofNat 32 0x26) 0x26
        (fun M' h => by simp only [TrdOut]; rw [if_neg hbig]; exact Or.inl h) ag8 sl8 y13.self
        (by rw [ls_oth y13 (show sp ≠ a0 by decide), s4sp])
        (by rw [ls_oth y13 (show (8 : Fin 32) ≠ a0 by decide), s4s0])
        (by rw [ls_get y13 (by decide), ls_r0]; rfl) (ls_byte (by decide)) (ls_kst y13 (by decide) kk4))
        (.cons z12 (.single z13))
    -- the read succeeded: `Ok(&buf[..l])`
    obtain ⟨hpl, hst, hby⟩ := ok4 h
    obtain ⟨t12, z12, y12⟩ := st4.notTaken hc8 0x54 trd_at_52 (by decide) (by rw [h, ls_r0]; rfl)
    obtain ⟨t13, z13, y13⟩ := y12.sw hc8 trd_at_54 (off' := 0x58) (by decide)
      (by rw [s4s0, add_lit_zero]; exact hres)
    rw [s4s0, add_lit_zero, s4s2] at y13
    have hc9a := hc8.store32 (a := res) (v := buf) (sep_front sSC (by decide))
    obtain ⟨t14, z14, y14⟩ := y13.sw hc9a trd_at_58 (off' := 0x5A) (by decide)
      (by rw [s4s0]; exact aligned_add hres (k := 4) (by decide))
    rw [s4s0, s4s1, show (0x4 : Word) = BitVec.ofNat 32 4 from rfl] at y14
    have hc9 := hc9a.store32 (a := res + BitVec.ofNat 32 4) (v := BitVec.ofNat 32 l)
      (sSC.sub (c := 4) (l := 4) (by decide))
    obtain ⟨t15, z15, y15⟩ := y14.jump hc9 trd_at_5a (off' := 0x68) (by decide)
      (by rw [y14.pc]; exact ls_even hbase 0x5A 0xE 0x68 (by decide) (by decide))
    obtain ⟨n', c', pc', mem', kr'⟩ := tail hc9 (fun c h1 h2 => by
        rw [memLoad32_store32_sep (rF 4 c 4 (by decide) h2), memLoad32_store32_sep (rF0 c h2)]; exact sl8 c h1 h2)
      y15.self (by rw [y15.regs, s4sp]) (ls_kbr y15 kk4)
    refine TrdPost.pre ⟨n', c', pc', kr', ?_, fun x h1 h2 h3 => ?_⟩
      (.cons z12 (.cons z13 (.cons z14 (.single z15))))
    · simp only [TrdOut]
      rw [if_neg hbig, mem']
      refine Or.inr ⟨?_, ?_, hpl, hst, fun j hj => ?_⟩
      · rw [memLoad32_store32_sep r40, memLoad32_store32_same]
      · exact memLoad32_store32_same _ _ _
      · rw [memStore32_get_sep ((sSO.sub (c := 4) (l := 4) (by decide)).subR (c := j) (l := 1) (by omega)),
          memStore32_get_sep ((sep_front sSO (by decide)).subR (c := j) (l := 1) (by omega))]
        exact hby j hj
    · rw [mem', memStore32_get_sep (h3.sub (c := 4) (l := 4) (by decide)),
        memStore32_get_sep (sep_front h3 (by decide))]
      exact ag8 x h1 h2
