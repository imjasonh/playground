import C3BootProofs.Proofs.AcceptStages
import C3BootProofs.Proofs.AcceptImageSpec
import C3BootProofs.Theorems.ImageTake

/-!
# `boot_main`'s first closure: the image header

`AcImageStage` is the stage from 0x1AA to 0x2A6, the start of the inlined
`accept_slot`. It copies the image's SHA-256 from `sp + 0xD4` to
`sp + 0x108`, calls `image::parse` on the header buffer, and goes to 0x7D6
when the header doesn't parse. Otherwise it copies the parsed header into
the frame, goes to 0x802 when the security version is below the eFuse level,
and reaches 0x2A6.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3

set_option maxRecDepth 100000

/-! ## The header the stage decodes -/

theorem aci_take_range_map {α : Type} (g : Nat → α) (n k : Nat) :
    ((List.range n).map g).take k = (List.range (min n k)).map g := by
  rw [← List.map_take, List.take_range, Nat.min_comm]

theorem aci_readPart_le {lo hi : Nat} {bs : Bytes} {p : Part} {rest : Bytes}
    (h : readPart lo hi bs = some (p, rest)) : p.length ≤ hi := by
  match bs, h with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: r, h =>
    simp only [readPart, readU32, Option.bind_eq_bind, Option.bind_some, require] at h
    split at h
    · rename_i hb
      cases h
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp hb).2
    · cases h

/-- A manifest that decodes names an image of at most 0x1D0000 bytes. -/
theorem aci_manifest_len {bs : Bytes} {mf : Manifest} (h : decodeManifest bs = some mf) :
    mf.image.length ≤ 0x1D0000 := by
  unfold decodeManifest at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, ⟨_, _⟩, -, h⟩ := h
  obtain ⟨_, -, h⟩ := h
  obtain ⟨_, -, ⟨_, _⟩, hp, h⟩ := h
  obtain ⟨⟨_, _⟩, -, h⟩ := h
  obtain ⟨⟨_, _⟩, -, h⟩ := h
  obtain ⟨_, -, h⟩ := h
  obtain ⟨_, -, h⟩ := h
  obtain ⟨_, -, h⟩ := h
  obtain ⟨_, -, h⟩ := h
  cases h
  exact aci_readPart_le hp

/-- The header buffer, as `image::parse` reads it, decodes as the whole
image's header does when it holds the image's first `min L 0x114` bytes. -/
theorem aci_decode {M : Word → BitVec 8} {p : Word} {flash : Nat → BitVec 8} {a L : Nat} (hL : L < 2 ^ 32)
    (hm : memBytes M p (min L 0x114) = flashBytes flash a (min L 0x114)) :
    decodeImageHeader (imageBytes M p (BitVec.ofNat 32 (min L 0x114))) (BitVec.ofNat 32 L).toNat =
      decodeImageHeader (flashBytes flash a L) L := by
  have h1 : (BitVec.ofNat 32 (min L 0x114)).toNat = min L 0x114 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have h2 : (BitVec.ofNat 32 L).toNat = L := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hL
  have h3 : imageBytes M p (BitVec.ofNat 32 (min L 0x114)) = memBytes M p (min L 0x114) := by
    show (List.range' 0 (_ - 0)).map _ = _
    rw [h1, Nat.sub_zero, ← List.range_eq_range']; rfl
  rw [h3, hm, h2, ← decodeImageHeader_take (flashBytes flash a L)]
  unfold flashBytes
  rw [aci_take_range_map]

/-! ## The stage -/

/-- The callees' code and data: `image::parse`, its readers and tables, and
`memcpy`. -/
def AcImageEnv (M : Word → BitVec 8) : Prop := Cur.ICode M (BitVec.ofNat 32 imageParseAddress)

/-- At 0x1AA, what the stage reads: the result pointer at `sp + 0x40`, the
header buffer's address and length in `s9` and `s6`, the image's length in
`s11`, `efuse_level` in `s10`, and the image's first `min length 0x114`
bytes in the header buffer. -/
def AcImagePre (flash : Nat → BitVec 8) (B Bf r slot level : Word) (mf : Manifest) (n : Machine) : Prop :=
  memLoad32 n.mem (acSlot B 0x40) = r ∧
  reg n (22 : Fin 32) = BitVec.ofNat 32 (min mf.image.length 0x114) ∧
  reg n (25 : Fin 32) = Bf + 0xB840 ∧
  reg n (26 : Fin 32) = level ∧
  reg n (27 : Fin 32) = BitVec.ofNat 32 mf.image.length ∧
  mf.image.length < 2 ^ 32 ∧
  memBytes n.mem (Bf + 0xB840) (min mf.image.length 0x114) =
    flashBytes flash (acBase slot + mf.image.offset) (min mf.image.length 0x114)

/-- At 0x2A6, from `n0` at 0x1AA: the image's header decodes, its security
version is at least the eFuse level's low byte and is in `s11`, and
`image::parse`'s result at `sp + 0x1870` holds it. `s5` and `s9` hold the
result's bytes 0 and 0xC, `s1` points `0x1310` past `sp`, and the frame holds
what the stage stored: the header buffer's address and length, the image's
length and SHA-256, and the bundle's and TUF metadata's lengths and offset,
and the result's bytes from 0xD at `sp + 0x139`. Nothing else outside the
callees' frames, `sp + 0xF4` to `sp + 0x243`, and the result changed. -/
def AcImagePost (flash : Nat → BitVec 8) (B slot level : Word) (mf : Manifest) (n0 n : Machine) : Prop :=
  (∃ header, decodeImageHeader (flashBytes flash (acBase slot + mf.image.offset) mf.image.length)
      mf.image.length = some header ∧
    (level &&& 0xFF).toNat ≤ header.securityVersion ∧
    reg n (27 : Fin 32) = BitVec.ofNat 32 header.securityVersion ∧
    ∃ sv entry cnt segs, header = toHdr (BitVec.ofNat 32 mf.image.length) (sv, entry, cnt, segs) ∧
      OutOk n.mem (acSlot B 0x1870) sv entry cnt (BitVec.ofNat 32 mf.image.length) segs ∧
      segs.length = cnt.toNat ∧ 0 < segs.length ∧ ∀ s ∈ segs, (3 : BitVec 8).ult s.kind = false) ∧
  reg n (9 : Fin 32) = acSlot B 0x1310 ∧
  reg n (20 : Fin 32) = reg n0 (20 : Fin 32) ∧
  reg n (21 : Fin 32) = (n.mem (acSlot B 0x1870)).zeroExtend 32 ∧
  reg n (23 : Fin 32) = reg n0 (9 : Fin 32) ∧
  reg n (24 : Fin 32) = reg n0 (24 : Fin 32) ∧
  reg n (25 : Fin 32) = (n.mem (acSlot B 0x187C)).zeroExtend 32 ∧
  reg n (26 : Fin 32) = level ∧
  memLoad32 n.mem (acSlot B 0xF4) = reg n0 (25 : Fin 32) ∧
  memLoad32 n.mem (acSlot B 0xF8) = reg n0 (22 : Fin 32) ∧
  memLoad32 n.mem (acSlot B 0xFC) = memLoad32 n0.mem (acSlot B 0x34) ∧
  memLoad32 n.mem (acSlot B 0x100) = reg n0 (8 : Fin 32) ∧
  memLoad32 n.mem (acSlot B 0x104) = reg n0 (27 : Fin 32) ∧
  memLoad32 n.mem (acSlot B 0x128) = reg n0 (24 : Fin 32) ∧
  memLoad32 n.mem (acSlot B 0x12C) = reg n0 (9 : Fin 32) ∧
  memLoad32 n.mem (acSlot B 0x130) = reg n0 (9 : Fin 32) ∧
  memBytes n.mem (acSlot B 0x108) 32 = memBytes n0.mem (acSlot B 0xD4) 32 ∧
  memBytes n.mem (acSlot B 0x139) 0xFF = memBytes n.mem (acSlot B 0x187D) 0xFF ∧
  (∀ i, i < 11 → n.mem (acSlot B (0x238 + i)) = n.mem (acSlot B (0x1871 + i))) ∧
  ∀ x, Sep B 0x3A50 x 1 → Sep (acSlot B 0xF4) 0x14F x 1 → Sep (acSlot B 0x1870) 0x110 x 1 →
    n.mem x = n0.mem x

/-- **The image stage**, from 0x1AA to 0x2A6, for the callees' code and data
`E` in memory that agrees with `M0` outside the stack and `Buffers`. -/
def AcImageStage (E : (Word → BitVec 8) → Prop) : Prop :=
  ∀ (flash : Nat → BitVec 8) (n : Machine) (B Bf g t r slot level : Word) (v : Nat → Word)
    (M0 : Word → BitVec 8) (mf : Manifest),
    (∀ M, (∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → M x = M0 x) → E M) →
    CodeIn n.mem AC bootMainClosure0Code → Fr B 0x5A70 → Sep B 0x5A70 Bf acBufLen →
    Bf.toNat + acBufLen ≤ 0x40000000 →
    St n.mem AC n 0x1AA (reg n) → AcInv B Bf g t v M0 n → AcImagePre flash B Bf r slot level mf n →
    AcStage B Bf g t r v M0 n 0x2A6 (AcImagePost flash B slot level mf n)

/-- `AcReadPost` gives `AcImagePre`. -/
theorem acImagePre_of_read {flash : Nat → BitVec 8} {B Bf r slot level : Word} {mf : Manifest} {n : Machine}
    (hm : decodeManifest (flashBytes flash (acBase slot) 32) = some mf)
    (h : AcReadPost flash B Bf r slot level mf n) : AcImagePre flash B Bf r slot level mf n := by
  obtain ⟨-, -, -, h40, -, -, -, -, h22, -, h25, h26, h27, -, hb, -, -⟩ := h
  exact ⟨h40, h22, h25, h26, h27, by have := aci_manifest_len hm; omega, hb⟩

/-! ## Addresses in the frame -/

theorem aci_in {B x : Word} {c n : Nat} (h : Sep (B + BitVec.ofNat 32 c) n x 1) {d l : Nat} (h1 : c ≤ d)
    (h2 : d + l ≤ c + n) : Sep (B + BitVec.ofNat 32 d) l x 1 := by
  have := h.sub (c := d - c) (l := l) (by omega)
  rwa [add_ofNat_assoc, show c + (d - c) = d by omega] at this

theorem aci_ne {a x : Word} (h : Sep a 1 x 1) : x ≠ a := fun e =>
  h 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero, e])

theorem aci_ne2 {a x : Word} (h : Sep a 2 x 1) : x ≠ a + 1 := fun e =>
  h 1 (by decide) 0 (by decide) (by rw [add_ofNat_zero, e]; rfl)

/-- `x` is outside what the stage writes: the callees' frames below `sp`,
`sp + 0xF4` to `sp + 0x243`, and `image::parse`'s result. -/
def aciW (B x : Word) : Prop :=
  Sep (B + BitVec.ofNat 32 0) 0x3A50 x 1 ∧ Sep (acSlot B 0xF4) 0x14F x 1 ∧ Sep (acSlot B 0x1870) 0x110 x 1

/-- `x` is outside what the stage writes after `image::parse` returns. -/
def aciL (B x : Word) : Prop := Sep (B + BitVec.ofNat 32 0) 0x3A50 x 1 ∧ Sep (acSlot B 0x136) 0x10D x 1

theorem aci_outW {B x : Word} (h : Sep x 1 B 0x5A70) : aciW B x := by
  have h0 : Sep (B + BitVec.ofNat 32 0) 0x5A70 x 1 := by rw [add_ofNat_zero]; exact h.symm
  exact ⟨aci_in h0 (by omega) (by omega), aci_in h0 (by omega) (by omega), aci_in h0 (by omega) (by omega)⟩

theorem aci_hiW {B x : Word} (F : Fr B 0x5A70) (hx : 0x40000000 ≤ x.toNat) : aciW B x := by
  have h := F.hiOut (c := 0) (n := 0x5A70) (by omega) hx
  rw [add_ofNat_zero] at h
  exact aci_outW h.symm

theorem aci_WL {B x : Word} (h : aciW B x) : aciL B x := ⟨h.1, aci_in h.2.1 (by omega) (by omega)⟩

theorem aci_pt {B : Word} {d : Nat} (h1 : 0x3A50 ≤ d) (h2 : d < 0x5A70)
    (h3 : d < 0x3A50 + 0xF4 ∨ (0x3A50 + 0x243 ≤ d ∧ d < 0x3A50 + 0x1870) ∨ 0x3A50 + 0x1980 ≤ d) :
    aciW B (B + BitVec.ofNat 32 d) :=
  ⟨sep_offsets B (by omega) (by omega) (by omega), sep_offsets B (by omega) (by omega) (by omega),
    sep_offsets B (by omega) (by omega) (by omega)⟩

theorem aci_ptL {B : Word} {d : Nat} (h1 : 0x3A50 ≤ d) (h2 : d < 0x5A70)
    (h3 : d < 0x3A50 + 0x136 ∨ 0x3A50 + 0x243 ≤ d) : aciL B (B + BitVec.ofNat 32 d) :=
  ⟨sep_offsets B (by omega) (by omega) (by omega), sep_offsets B (by omega) (by omega) (by omega)⟩

theorem aci_code {M M' : Word → BitVec 8} {B : Word} (F : Fr B 0x5A70) (C : CodeIn M AC bootMainClosure0Code)
    (h : ∀ x, aciW B x → M' x = M x) : CodeIn M' AC bootMainClosure0Code := fun i hi => by
  rw [h _ (aci_hiW F ?_)]
  · exact C i hi
  · have hl : bootMainClosure0Code.length < 0x10000 := by decide
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show bootMainClosure0Address = 0x403a00a6 from rfl]
    omega

theorem aci_env {M M0 : Word → BitVec 8} {B Bf : Word} {E : (Word → BitVec 8) → Prop}
    (hE : ∀ M, (∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → M x = M0 x) → E M) {n : Machine}
    (hO : ∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → n.mem x = M0 x)
    (h : ∀ x, aciW B x → M x = n.mem x) : E M :=
  hE M fun x h1 h2 => (h x (aci_outW h1)).trans (hO x h1 h2)

theorem aci_inv {B Bf g t : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {n n' : Machine}
    (I : AcInv B Bf g t v M0 n) (hsp : reg n' sp = B + 0x3A50) (h3 : reg n' (3 : Fin 32) = reg n (3 : Fin 32))
    (h4 : reg n' (4 : Fin 32) = reg n (4 : Fin 32)) (hm : ∀ x, aciW B x → n'.mem x = n.mem x) :
    AcInv B Bf g t v M0 n' where
  sp := hsp
  gp := h3.trans I.gp
  tp := h4.trans I.tp
  saves k hk := by
    rw [← I.saves k hk]
    apply memLoad32_congr
    intro j hj
    rw [add_ofNat_assoc]
    exact hm _ (aci_pt (by omega) (by omega) (by omega))
  out x h1 h2 := (hm x (aci_outW h1)).trans (I.out x h1 h2)

theorem aci_mb {M M' : Word → BitVec 8} {p p' : Word} {k : Nat}
    (h : ∀ i, i < k → M (p + BitVec.ofNat 32 i) = M' (p' + BitVec.ofNat 32 i)) : memBytes M p k = memBytes M' p' k := by
  unfold memBytes
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.mp hi)]

theorem aci_outok {M M' : Word → BitVec 8} {out : Word} {sv cnt : BitVec 8} {entry ilen : Word} {segs : List SegW}
    (O : OutOk M out sv entry cnt ilen segs) (hl : segs.length ≤ 16)
    (h : ∀ i, i < 0x110 → M' (out + BitVec.ofNat 32 i) = M (out + BitVec.ofNat 32 i)) :
    OutOk M' out sv entry cnt ilen segs := by
  have w : ∀ c, c + 4 ≤ 0x110 → memLoad32 M' (out + BitVec.ofNat 32 c) = memLoad32 M (out + BitVec.ofNat 32 c) :=
    fun c hc => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h _ (by omega)
  obtain ⟨O1, O2, O3, O4, O5, O6⟩ := O
  refine ⟨fun j hj => ?_, fun j h1 h2 k hk => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := O1 j hj
    exact ⟨(w _ (by omega)).trans a1, (w _ (by omega)).trans a2, (w _ (by omega)).trans a3,
      (h _ (by omega)).trans a4⟩
  · exact (w _ (by omega)).trans (O2 j h1 h2 k hk)
  · exact (w 0x100 (by decide)).trans O3
  · exact (w 0x104 (by decide)).trans O4
  · exact (w 0x108 (by decide)).trans O5
  · exact (h 0x10C (by decide)).trans O6

/-! ## Calls -/

theorem aci_fr (B : Word) : B + BitVec.ofNat 32 0x3A50 + 0xFFFFFFF0 = B + BitVec.ofNat 32 0x3A40 := by
  rw [BitVec.add_assoc] <;> rfl

theorem aci_spG (B : Word) :
    B + BitVec.ofNat 32 0x3A50 = B + BitVec.ofNat 32 0x38C0 + BitVec.ofNat 32 0x30 + 0x160 := by
  rw [BitVec.add_assoc, BitVec.add_assoc] <;> rfl

/-- `memcpy`'s stub. -/
abbrev aciMCS : Word := BitVec.ofNat 32 memcpyStubAddress

theorem aci_body : (BitVec.ofNat 32 imageParseAddress : Word) + 0x9B7E = aciMCS + 8 := by decide

theorem aci_stub : (BitVec.ofNat 32 imageParseAddress : Word) + 0x9B76 = aciMCS := by decide

theorem aci_mce {Mx : Word → BitVec 8} {B : Word} (F : Fr B 0x5A70) (K : AcImageEnv Mx) {c d N : Nat}
    (hc : 0x3A50 ≤ c) (hd : 0x3A50 ≤ d) (hc' : c + N ≤ 0x5A70) (hd' : d + N ≤ 0x5A70) (h : c + N ≤ d ∨ d + N ≤ c) :
    McEnv Mx (aciMCS + 8) (B + BitVec.ofNat 32 c) (B + BitVec.ofNat 32 d) (B + BitVec.ofNat 32 0x3A50 + 0xFFFFFFF0) N := by
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hb : (0x40000000 : Nat) ≤ (aciMCS + 8).toNat := by decide
  have hbl : (aciMCS + 8).toNat + memcpyBodyCode.length ≤ 2 ^ 32 := by decide
  rw [aci_fr]
  exact {
    code := by have := K.body; rwa [aci_body] at this
    hDC := F.sepHi (by omega) hb hbl
    hFC := F.sepHi (by omega) hb hbl
    hdF := sep_offsets B (.inr (by omega)) (by omega) (by omega)
    hsF := sep_offsets B (.inr (by omega)) (by omega) (by omega)
    hsep := sep_offsets B h (by omega) (by omega)
    hF := by rw [F.at _ (by omega)]; omega
    hFw := by rw [F.at _ (by omega)]; omega
    hdw := by rw [F.at _ (by omega)]; omega
    hsw := by rw [F.at _ (by omega)]; omega }

/-- The registers that `memcpy` keeps. -/
abbrev aciS : List Nat := [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 31]

theorem aci_S : ∀ r : Fin 32, r.val ∈ aciS →
    r ≠ a0 ∧ r ≠ a1 ∧ r ≠ a2 ∧ r ≠ a3 ∧ r ≠ a4 ∧ r ≠ a5 ∧ r ≠ a6 ∧ r ≠ a7 ∧ r ≠ t0 ∧ r ≠ t1 ∧
      r ≠ (7 : Fin 32) ∧ r ≠ (28 : Fin 32) ∧ r ≠ (29 : Fin 32) ∧ r ≠ (30 : Fin 32) ∧ r ≠ ra := by decide

/-- A call to `memcpy` from the closure, with `sp` at `S`. -/
theorem aci_mc {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o dst src S : Word}
    {N : Nat} (s : St Mx AC n off g) (hcd : CodeIn Mx AC bootMainClosure0Code) (hstub : CodeIn Mx aciMCS memcpyStubCode)
    (h1 : fetchRel bootMainClosure0Code off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainClosure0Code (off + 4) = some (.jalr ra ra o, 4))
    (hb : AC + BitVec.ofNat 32 off + imm + o = aciMCS) (he8 : (AC + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = dst) (ha1 : g a1 = src) (ha2 : g a2 = BitVec.ofNat 32 N)
    (E : McEnv Mx (aciMCS + 8) dst src (S + 0xFFFFFFF0) N) :
    ∃ n', Steps n n' ∧ St n'.mem AC n' (off + 8) (reg n') ∧
      (∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → n'.mem x = copyBytes Mx dst src N x) ∧
      ∀ r : Fin 32, r.val ∈ aciS → reg n' r = g r := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hcd h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  obtain ⟨n2, c2, pc2, sp2, -, mem2, k2⟩ := memcpy_correct n1 aciMCS (AC + BitVec.ofNat 32 (off + 8)) dst src N
    (fun i hi => by rw [mem1]; exact hstub i hi) (by decide) pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) (by rw [mem1, r1 sp (by decide), hsp]; exact E)
  rw [r1 sp (by decide), hsp, mem1] at mem2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, mem2, fun r hr => ?_⟩
  obtain ⟨_, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hra⟩ := aci_S r hr
  by_cases hs : r = sp
  · subst hs; rw [sp2, r1 sp (by decide)]
  · rw [k2 r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hs, r1 r hra]

/-! ## Straight-line blocks -/

/-- From 0x1AA: store `s9`, `s6`, and `s11`, and set up the copy of the
image's SHA-256. -/
def aciA : List BInstr :=
  [.sw sp (25 : Fin 32) 0xF4, .sw sp (22 : Fin 32) 0xF8, .sw sp (27 : Fin 32) 0x104,
   .aluImm .add a0 sp 0x108, .aluImm .add a1 sp 0xD4, .aluImm .add a2 x0 0x20]

theorem aciA_end : blockEnd bootMainClosure0Code 0x1AA aciA = some 0x1BA := by decide

/-- From 0x1C2: store the bundle's and TUF metadata's fields, and set up the
call to `image::parse`. -/
def aciB : List BInstr :=
  [.lw a0 sp 0x34, .sw sp a0 0xFC, .aluImm .add a0 sp 0x100, .sw a0 (8 : Fin 32) 0x0,
   .sw a0 (24 : Fin 32) 0x28, .sw a0 (9 : Fin 32) 0x2C, .alu .add (23 : Fin 32) x0 (9 : Fin 32),
   .sw a0 (9 : Fin 32) 0x30, .lui a0 0x2000, .aluImm .add a0 a0 0xFFFFF870, .alu .add a0 a0 sp,
   .alu .add a1 x0 (25 : Fin 32), .alu .add a2 x0 (22 : Fin 32), .alu .add a3 x0 (27 : Fin 32)]

theorem aciB_end : blockEnd bootMainClosure0Code 0x1C2 aciB = some 0x1E2 := by decide

/-- From 0x1EA: read the result's bytes 0xC and 0. -/
def aciC : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x310, .alu .add (9 : Fin 32) sp a0, .lbu (25 : Fin 32) (9 : Fin 32) 0x56C,
   .lbu (21 : Fin 32) (9 : Fin 32) 0x560, .aluImm .add a0 (25 : Fin 32) 0xFFFFFF01]

theorem aciC_end : blockEnd bootMainClosure0Code 0x1EA aciC = some 0x200 := by decide

/-- From 0x204: copy the result's bytes 1 to 8 to `sp + 0x238`. -/
def aciD : List BInstr :=
  [.lbu (17 : Fin 32) (9 : Fin 32) 0x569, .lbu a1 (9 : Fin 32) 0x56A, .lbu a6 (9 : Fin 32) 0x56B,
   .lbu (5 : Fin 32) (9 : Fin 32) 0x565, .lbu (6 : Fin 32) (9 : Fin 32) 0x566, .lbu a5 (9 : Fin 32) 0x561,
   .lbu (8 : Fin 32) (9 : Fin 32) 0x562, .lbu a2 (9 : Fin 32) 0x563, .lbu a0 (9 : Fin 32) 0x564,
   .aluImm .sll a1 a1 0x8, .alu .or (17 : Fin 32) a1 (17 : Fin 32), .lbu a3 (9 : Fin 32) 0x567,
   .lbu a4 (9 : Fin 32) 0x568, .aluImm .sll (6 : Fin 32) (6 : Fin 32) 0x8, .alu .or a1 (6 : Fin 32) (5 : Fin 32),
   .aluImm .sll (8 : Fin 32) (8 : Fin 32) 0x8, .aluImm .sll a2 a2 0x10, .aluImm .sll a0 a0 0x18,
   .alu .or a5 a5 (8 : Fin 32), .alu .or a0 a0 a2, .aluImm .sll a3 a3 0x10, .aluImm .sll a4 a4 0x18,
   .alu .or a3 a3 a4, .alu .or a0 a0 a5, .alu .or a1 a1 a3, .sw sp a0 0x238, .sw sp a1 0x23C]

theorem aciD_end : blockEnd bootMainClosure0Code 0x204 aciD = some 0x258 := by decide

/-- From 0x25C: store byte 0xB, and set up the copy of bytes 0xD to 0x10B. -/
def aciE : List BInstr :=
  [.sb sp a6 0x242, .lui a0 0x2000, .aluImm .add a0 a0 0xFFFFF87D, .alu .add a1 sp a0,
   .aluImm .add a0 sp 0x139, .aluImm .add a2 x0 0xFF]

theorem aciE_end : blockEnd bootMainClosure0Code 0x25C aciE = some 0x272 := by decide

/-- From 0x27A: read the security version and bytes 0x10D to 0x10F, and the
eFuse level's low byte. -/
def aciF : List BInstr :=
  [.lbu a0 (9 : Fin 32) 0x66E, .lbu a1 (9 : Fin 32) 0x66D, .lbu (27 : Fin 32) (9 : Fin 32) 0x66C,
   .lbu a2 (9 : Fin 32) 0x66F, .aluImm .sll a0 a0 0x8, .alu .or a0 a0 a1, .aluImm .and a1 (26 : Fin 32) 0xFF]

theorem aciF_end : blockEnd bootMainClosure0Code 0x27A aciF = some 0x292 := by decide

/-- At 0x296: store byte 0x10F. -/
def aciG : List BInstr := [.sb sp a2 0x138]

theorem aciG_end : blockEnd bootMainClosure0Code 0x296 aciG = some 0x29A := by decide

/-- From 0x29E: the code 0x12, and the result pointer and slot. -/
def aciH : List BInstr := [.aluImm .add (21 : Fin 32) x0 0x12, .lw (19 : Fin 32) sp 0x40, .lw (8 : Fin 32) sp 0x3C]

theorem aciH_end : blockEnd bootMainClosure0Code 0x29E aciH = some 0x2A4 := by decide


/-! ## Frame slots -/

/-- `_h` keeps `aci_norm` to literal offsets. -/
theorem aci_sl (B k : Word) (_h : 0x3A50 + k.toNat < 2 ^ 32) :
    B + BitVec.ofNat 32 0x3A50 + k = acSlot B k.toNat := by
  show _ = B + BitVec.ofNat 32 (0x3A50 + k.toNat)
  rw [BitVec.add_assoc]; congr 1

theorem aci_sl2 (B : Word) (k : Nat) (c : Word) (_h : 0x3A50 + k + c.toNat < 2 ^ 32) :
    acSlot B k + c = acSlot B (k + c.toNat) := by
  show B + BitVec.ofNat 32 (0x3A50 + k) + c = B + BitVec.ofNat 32 (0x3A50 + (k + c.toNat))
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; have := c.isLt; omega

theorem aci_cs (B k : Word) (_h : 0x3A50 + k.toNat < 2 ^ 32) :
    k + (B + BitVec.ofNat 32 0x3A50) = acSlot B k.toNat := by
  rw [BitVec.add_comm]; exact aci_sl B k _h

/-- Writes `sp + k` as `acSlot B k`. -/
macro "aci_norm" : tactic =>
  `(tactic| simp (disch := decide) only [aci_sl, aci_sl2, aci_cs, BitVec.reduceAdd, BitVec.reduceToNat,
    Nat.reduceAdd])

theorem aci_ad (B : Word) (k i : Nat) : acSlot B k + BitVec.ofNat 32 i = acSlot B (k + i) := by
  show B + BitVec.ofNat 32 (0x3A50 + k) + BitVec.ofNat 32 i = B + BitVec.ofNat 32 (0x3A50 + (k + i))
  rw [add_ofNat_assoc, Nat.add_assoc]

theorem aci_cp {M : Word → BitVec 8} {dst src : Word} {N i : Nat} (hi : i < N) (hN : N < 2 ^ 32) :
    copyBytes M dst src N (dst + BitVec.ofNat 32 i) = M (src + BitVec.ofNat 32 i) := by
  unfold copyBytes
  rw [BitVec.add_comm dst, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ite_eq_left hi]

theorem aci_al {B : Word} (F : Fr B 0x5A70) {c : Nat} (h : c + 4 ≤ 0x5A70) (hk : c % 4 = 0) :
    (B + BitVec.ofNat 32 c).toNat % 4 = 0 := by
  rw [F.at c (by omega)]; have := F.al; omega

theorem aci_al2 {B : Word} (F : Fr B 0x5A70) {c : Nat} (h : c + 2 ≤ 0x5A70) (hk : c % 2 = 0) :
    (B + BitVec.ofNat 32 c).toNat % 2 = 0 := by
  rw [F.at c (by omega)]; have := F.al; omega

theorem aci_sc {B : Word} (F : Fr B 0x5A70) {c n : Nat} (h : c + n ≤ 0x5A70) :
    Sep (B + BitVec.ofNat 32 c) n AC bootMainClosure0Code.length :=
  F.sepHi h (by decide) (by decide)

theorem aci_w32 {B x : Word} (hx : aciW B x) {M : Word → BitVec 8} {v : Word} (k : Nat) (h1 : 0xF4 ≤ k)
    (h2 : k + 4 ≤ 0x243) : memStore32 M (acSlot B k) v x = M x :=
  memStore32_get_sep (aci_in hx.2.1 (by omega) (by omega))

theorem aci_l32 {B x : Word} (hx : aciL B x) {M : Word → BitVec 8} {v : Word} (k : Nat) (h1 : 0x136 ≤ k)
    (h2 : k + 4 ≤ 0x243) : memStore32 M (acSlot B k) v x = M x :=
  memStore32_get_sep (aci_in hx.2 (by omega) (by omega))

theorem aci_l8 {B x : Word} (hx : aciL B x) {M : Word → BitVec 8} {v : BitVec 8} (k : Nat) (h1 : 0x136 ≤ k)
    (h2 : k + 1 ≤ 0x243) : memStore8 M (acSlot B k) v x = M x :=
  memStore8_ne (aci_ne (aci_in hx.2 (by omega) (by omega)))

theorem aci_lsep {M : Word → BitVec 8} {B v : Word} (k d : Nat) (h : k + 4 ≤ d ∨ d + 4 ≤ k)
    (hk : k + 4 ≤ 0x2000) (hd : d + 4 ≤ 0x2000) :
    memLoad32 (memStore32 M (acSlot B k) v) (acSlot B d) = memLoad32 M (acSlot B d) :=
  memLoad32_store32_sep (sep_offsets B (by omega) (by omega) (by omega))

theorem aci_s32 {M : Word → BitVec 8} {B v : Word} (k d : Nat) (h : k + 4 ≤ d ∨ d + 1 ≤ k)
    (hk : k + 4 ≤ 0x2000) (hd : d + 1 ≤ 0x2000) :
    memStore32 M (acSlot B k) v (acSlot B d) = M (acSlot B d) :=
  memStore32_get_sep (sep_offsets B (by omega) (by omega) (by omega))

theorem aci_s32i {M : Word → BitVec 8} {B v : Word} (k d i : Nat) (h : k + 4 ≤ d + i ∨ d + i + 1 ≤ k)
    (hk : k + 4 ≤ 0x2000) (hd : d + i + 1 ≤ 0x2000) :
    memStore32 M (acSlot B k) v (acSlot B d + BitVec.ofNat 32 i) = M (acSlot B d + BitVec.ofNat 32 i) := by
  rw [aci_ad]; exact aci_s32 k (d + i) h hk hd

theorem aci_s8i {M : Word → BitVec 8} {B : Word} {v : BitVec 8} (k d i : Nat) (h : k + 1 ≤ d + i ∨ d + i + 1 ≤ k)
    (hk : k + 1 ≤ 0x2000) (hd : d + i + 1 ≤ 0x2000) :
    memStore8 M (acSlot B k) v (acSlot B d + BitVec.ofNat 32 i) = M (acSlot B d + BitVec.ofNat 32 i) := by
  rw [aci_ad]; exact memStore8_ne (aci_ne (sep_offsets B (by omega) (by omega) (by omega)))

theorem aci_ldW {B : Word} {M M' : Word → BitVec 8} (h : ∀ x, aciW B x → M' x = M x) (k : Nat)
    (hk : k + 4 ≤ 0xF4) : memLoad32 M' (acSlot B k) = memLoad32 M (acSlot B k) :=
  memLoad32_congr fun j hj => by rw [aci_ad]; exact h _ (aci_pt (by omega) (by omega) (by omega))

theorem aci_ldL {B : Word} {M M' : Word → BitVec 8}
    (h : ∀ x, aciL B x → Sep (acSlot B 0x1870) 0x110 x 1 → M' x = M x) (k : Nat) (hk : k + 4 ≤ 0x136) :
    memLoad32 M' (acSlot B k) = memLoad32 M (acSlot B k) :=
  memLoad32_congr fun j hj => by
    rw [aci_ad]
    exact h _ (aci_ptL (by omega) (by omega) (by omega)) (sep_offsets B (by omega) (by omega) (by omega))

theorem aci_e (e : BitVec 8) (h : e.toNat < 12) : ((e.zeroExtend 32 : Word) &&& 0xFF).toNat < 0x27 := by
  rw [BitVec.toNat_and]
  have h1 := Nat.and_le_left (n := (e.zeroExtend 32 : Word).toNat) (m := (0xFF : Word).toNat)
  have h2 : (e.zeroExtend 32 : Word).toNat = e.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := e.isLt; omega)
  omega

theorem aci_kind (k : BitVec 8) (h : (3 : BitVec 8).ult k = false) :
    (k.zeroExtend 32 + 0xFFFFFF01 == (0 : Word)) = false := by
  have h2 : (k.zeroExtend 32 : Word).toNat = k.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := k.isLt; omega)
  have h3 : k.toNat ≤ 3 := by
    simp only [BitVec.ult, decide_eq_false_iff_not] at h; have : (3 : BitVec 8).toNat = 3 := rfl; omega
  rw [beq_eq_false_iff_ne]
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_add, h2] at this
  have : (0xFFFFFF01 : Word).toNat = 0xFFFFFF01 := rfl
  have : (0 : Word).toNat = 0 := rfl
  omega

theorem aci_ge (sv : BitVec 8) (y : Word) (h : (sv.zeroExtend 32 : Word).ult y = false) : y.toNat ≤ sv.toNat := by
  have h2 : (sv.zeroExtend 32 : Word).toNat = sv.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := sv.isLt; omega)
  simp only [BitVec.ult, decide_eq_false_iff_not] at h; omega

theorem aci_z (x : Word) : 0 + x = x := BitVec.zero_add x

/-! ## The stage -/

theorem acs_x4 (b0 b1 b2 b3 : BitVec 8) :
    (b3 ++ b2 ++ b1 ++ b0).extractLsb' 0 8 = b0 ∧ (b3 ++ b2 ++ b1 ++ b0).extractLsb' 8 8 = b1 ∧
      (b3 ++ b2 ++ b1 ++ b0).extractLsb' 16 8 = b2 ∧ (b3 ++ b2 ++ b1 ++ b0).extractLsb' 24 8 = b3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  · simp [show i < 8 from hi]
  · simp [show ¬ 8 + i < 8 by omega, show 8 + i - 8 = i by omega, hi]
  · simp [show ¬ 16 + i < 8 by omega, show ¬ 16 + i - 8 < 8 by omega, show 16 + i - 8 - 8 = i by omega, hi]
  · simp [show ¬ 24 + i < 8 by omega, show ¬ 24 + i - 8 < 8 by omega, show ¬ 24 + i - 8 - 8 < 8 by omega,
      show 24 + i - 8 - 8 - 8 = i by omega]

theorem acs_shA (b0 b1 b2 b3 : BitVec 8) :
    aluEval AluOp.or (aluEval AluOp.or (aluEval AluOp.sll (b3.zeroExtend 32) 24)
      (aluEval AluOp.sll (b2.zeroExtend 32) 16))
      (aluEval AluOp.or (b0.zeroExtend 32) (aluEval AluOp.sll (b1.zeroExtend 32) 8)) = b3 ++ b2 ++ b1 ++ b0 := by
  rw [← C3.RV32.Cur.or_assemble]; simp only [aluEval, BitVec.reduceToNat, Nat.reduceMod]
  rw [BitVec.or_comm _ (b0.zeroExtend 32 ||| _), BitVec.or_comm (b3.zeroExtend 32 <<< 24)]

theorem acs_shB (b0 b1 b2 b3 : BitVec 8) :
    aluEval AluOp.or (aluEval AluOp.or (aluEval AluOp.sll (b1.zeroExtend 32) 8) (b0.zeroExtend 32))
      (aluEval AluOp.or (aluEval AluOp.sll (b2.zeroExtend 32) 16) (aluEval AluOp.sll (b3.zeroExtend 32) 24)) =
      b3 ++ b2 ++ b1 ++ b0 := by
  rw [← C3.RV32.Cur.or_assemble]; simp only [aluEval, BitVec.reduceToNat, Nat.reduceMod]
  rw [BitVec.or_comm (b1.zeroExtend 32 <<< 8)]

theorem acs_x2 (b0 b1 : BitVec 8) :
    (aluEval AluOp.or (aluEval AluOp.sll (b1.zeroExtend 32) 8) (b0.zeroExtend 32)).extractLsb' 0 8 = b0 ∧
      (aluEval AluOp.or (aluEval AluOp.sll (b1.zeroExtend 32) 8) (b0.zeroExtend 32)).extractLsb' 8 8 = b1 := by
  simp only [aluEval, BitVec.reduceToNat, Nat.reduceMod]
  refine ⟨?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hi,
      decide_true, Bool.true_and]
  · simp [show i < 8 from hi]; intro; omega
  · simp [show 8 + i - 8 = i by omega, show 8 + i < 32 by omega, show ¬ 8 + i < 8 by omega,
      show i < 32 by omega]

theorem acs_ilo8 (b : BitVec 8) : (b.zeroExtend 32).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]; omega

theorem acs_st32a (M : Word → BitVec 8) (a v : Word) :
    memStore32 M a v a = v.extractLsb' 0 8 ∧ memStore32 M a v (a + 1) = v.extractLsb' 8 8 ∧
      memStore32 M a v (a + 2) = v.extractLsb' 16 8 ∧ memStore32 M a v (a + 3) = v.extractLsb' 24 8 := by
  have n : ∀ i j : Nat, i < 4 → j < 4 → i ≠ j → a + BitVec.ofNat 32 i ≠ a + BitVec.ofNat 32 j :=
    fun i j hi hj h => add_ofNat_ne a (by omega) (by omega) h
  have n0 : ∀ j : Nat, 0 < j → j < 4 → a ≠ a + BitVec.ofNat 32 j := fun j h1 h2 e =>
    n 0 j (by omega) h2 (by omega) (by rw [add_ofNat_zero]; exact e)
  unfold memStore32
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [memStore8_ne (x := a) (a := a + 3) (n0 3 (by omega) (by omega)),
      memStore8_ne (x := a) (a := a + 2) (n0 2 (by omega) (by omega)),
      memStore8_ne (x := a) (a := a + 1) (n0 1 (by omega) (by omega)), memStore8_same]
  · rw [memStore8_ne (x := a + 1) (a := a + 3) (n 1 3 (by omega) (by omega) (by omega)),
      memStore8_ne (x := a + 1) (a := a + 2) (n 1 2 (by omega) (by omega) (by omega)), memStore8_same]
  · rw [memStore8_ne (x := a + 2) (a := a + 3) (n 2 3 (by omega) (by omega) (by omega)), memStore8_same]
  · rw [memStore8_same]

theorem acs_st32 (M : Word → BitVec 8) (B v : Word) (k : Nat) :
    memStore32 M (acSlot B k) v (acSlot B k) = v.extractLsb' 0 8 ∧
      memStore32 M (acSlot B k) v (acSlot B (k + 1)) = v.extractLsb' 8 8 ∧
      memStore32 M (acSlot B k) v (acSlot B (k + 2)) = v.extractLsb' 16 8 ∧
      memStore32 M (acSlot B k) v (acSlot B (k + 3)) = v.extractLsb' 24 8 := by
  rw [← aci_ad B k 1, ← aci_ad B k 2, ← aci_ad B k 3]; exact acs_st32a M _ v

theorem acs_st2 (M M' : Word → BitVec 8) (B : Word) (k d i : Nat) (hi : i < 8) (hk : k + 8 ≤ 0x2000) :
    memStore32 (memStore32 M (acSlot B k) (M' (acSlot B (d + 3)) ++ M' (acSlot B (d + 2)) ++
      M' (acSlot B (d + 1)) ++ M' (acSlot B d))) (acSlot B (k + 4)) (M' (acSlot B (d + 7)) ++
      M' (acSlot B (d + 6)) ++ M' (acSlot B (d + 5)) ++ M' (acSlot B (d + 4))) (acSlot B (k + i)) =
      M' (acSlot B (d + i)) := by
  have L : ∀ j, j < 4 → memStore32 (memStore32 M (acSlot B k) (M' (acSlot B (d + 3)) ++ M' (acSlot B (d + 2)) ++
      M' (acSlot B (d + 1)) ++ M' (acSlot B d))) (acSlot B (k + 4)) (M' (acSlot B (d + 7)) ++
      M' (acSlot B (d + 6)) ++ M' (acSlot B (d + 5)) ++ M' (acSlot B (d + 4))) (acSlot B (k + j)) =
      memStore32 M (acSlot B k) (M' (acSlot B (d + 3)) ++ M' (acSlot B (d + 2)) ++
      M' (acSlot B (d + 1)) ++ M' (acSlot B d)) (acSlot B (k + j)) := fun j hj =>
    aci_s32 (k + 4) (k + j) (.inr (by omega)) (by omega) (by omega)
  have S0 := acs_st32 M B (M' (acSlot B (d + 3)) ++ M' (acSlot B (d + 2)) ++
      M' (acSlot B (d + 1)) ++ M' (acSlot B d)) k
  have S1 := acs_st32 (memStore32 M (acSlot B k) (M' (acSlot B (d + 3)) ++ M' (acSlot B (d + 2)) ++
      M' (acSlot B (d + 1)) ++ M' (acSlot B d))) B (M' (acSlot B (d + 7)) ++
      M' (acSlot B (d + 6)) ++ M' (acSlot B (d + 5)) ++ M' (acSlot B (d + 4))) (k + 4)
  have X0 := acs_x4 (M' (acSlot B d)) (M' (acSlot B (d + 1))) (M' (acSlot B (d + 2))) (M' (acSlot B (d + 3)))
  have X1 := acs_x4 (M' (acSlot B (d + 4))) (M' (acSlot B (d + 5))) (M' (acSlot B (d + 6)))
    (M' (acSlot B (d + 7)))
  match i, hi with
  | 0, _ => rw [L 0 (by omega)]; exact S0.1.trans X0.1
  | 1, _ => rw [L 1 (by omega)]; exact S0.2.1.trans X0.2.1
  | 2, _ => rw [L 2 (by omega)]; exact S0.2.2.1.trans X0.2.2.1
  | 3, _ => rw [L 3 (by omega)]; exact S0.2.2.2.trans X0.2.2.2
  | 4, _ => exact S1.1.trans X1.1
  | 5, _ => rw [show k + 5 = k + 4 + 1 by omega, show d + 5 = d + 4 + 1 by omega] at *; exact S1.2.1.trans X1.2.1
  | 6, _ => exact (show k + 6 = k + 4 + 2 by omega) ▸ S1.2.2.1.trans X1.2.2.1
  | 7, _ => exact (show k + 7 = k + 4 + 3 by omega) ▸ S1.2.2.2.trans X1.2.2.2

theorem acs_s8 {M : Word → BitVec 8} {B : Word} {v : BitVec 8} (k d : Nat) (h : k ≠ d)
    (hk : k + 1 ≤ 0x2000) (hd : d + 1 ≤ 0x2000) :
    memStore8 M (acSlot B k) v (acSlot B d) = M (acSlot B d) :=
  memStore8_ne (aci_ne (sep_offsets B (by omega) (by omega) (by omega)))

/-- `imgW`'s segment list has the header's count. -/
theorem acs_imgW_cnt {M : Word → BitVec 8} {ptr len ilen : Word} {sv cnt : BitVec 8} {entry : Word}
    {segs : List SegW} (h : imgW M ptr len ilen = .ok (sv, entry, cnt, segs)) : segs.length = cnt.toNat := by
  unfold imgW at h
  obtain ⟨⟨sv', cnt', entry', pos⟩, hh, h1⟩ := aci_bind_ok h
  obtain ⟨⟨segs', pos', prev⟩, hr, h2⟩ := aci_bind_ok h1
  dsimp only at h2
  split at h2
  · obtain ⟨_, h3, -⟩ := aci_bind_ok h2
    cases h3
  · obtain ⟨_, -, h3⟩ := aci_bind_ok h2
    obtain ⟨_, -, h4⟩ := aci_bind_ok h3
    cases h4; exact aci_readSegsW_len hr

set_option maxHeartbeats 8000000 in
/-- **From 0x1AA to 0x2A6.** -/
theorem acImage_stage : AcImageStage AcImageEnv := by
  intro flash n B Bf g t r slot level v M0 mf hE C F sBf hBf s I P
  obtain ⟨h40, h22, h25, h26, h27, hL, hhd⟩ := P
  have rsp : reg n sp = B + BitVec.ofNat 32 0x3A50 := I.sp
  have hz := s.zero
  have hBf' : Bf.toNat + 0xB954 ≤ 0x40000000 := hBf
  /- 0x1AA: store `s9`, `s6`, and `s11`. -/
  obtain ⟨n1, c1, u1⟩ := s.block aciA C aciA_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, aciA]
    simp +decide only [and_true]
    rw [rsp]; aci_norm
    exact ⟨⟨aci_al F (by decide) (by decide), aci_sc F (by decide)⟩,
      ⟨aci_al F (by decide) (by decide), aci_sc F (by decide)⟩,
      ⟨aci_al F (by decide) (by decide), aci_sc F (by decide)⟩⟩)
  have m1 : n1.mem = memStore32 (memStore32 (memStore32 n.mem (acSlot B 0xF4) (reg n 25)) (acSlot B 0xF8)
      (reg n 22)) (acSlot B 0x104) (reg n 27) := by
    rw [u1.mem]; simp only [runBlock, BInstr.run, aciA]; rw [rsp]; aci_norm
  have k1 : ∀ q : Fin 32, q.val ∉ [10, 11, 12] → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [aciA]; revert hq; revert q; decide)]
  have W1 : ∀ x, aciW B x → n1.mem x = n.mem x := fun x hx => by
    rw [m1, aci_w32 hx 0x104 (by decide) (by decide), aci_w32 hx 0xF8 (by decide) (by decide),
      aci_w32 hx 0xF4 (by decide) (by decide)]
  have a01 : reg n1 a0 = acSlot B 0x108 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, aciA, upd, ↓reduceIte, aluEval]; rw [rsp]; aci_norm
  have a11 : reg n1 a1 = acSlot B 0xD4 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, aciA, upd, ↓reduceIte, aluEval]; rw [rsp]; aci_norm
  have a21 : reg n1 a2 = BitVec.ofNat 32 32 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, aciA, upd, ↓reduceIte, aluEval]
  /- 0x1BA: copy the image's SHA-256. -/
  have s1 : St n1.mem AC n1 0x1BA (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have K1 : Cur.ICode n1.mem (BitVec.ofNat 32 imageParseAddress) := aci_env hE I.out W1
  obtain ⟨n2, c2, s2, mem2, k2⟩ := aci_mc (N := 32) (S := B + BitVec.ofNat 32 0x3A50) s1 (aci_code F C W1)
    (by have := K1.stub; rwa [aci_stub] at this) ac_at_1ba ac_at_1be (by decide) (by decide)
    (by rw [k1 sp (by decide), rsp]) a01 a11 a21
    (aci_mce F K1 (by omega) (by omega) (by omega) (by omega) (by omega))
  rw [aci_fr] at mem2
  have W21 : ∀ x, Sep (B + BitVec.ofNat 32 0) 0x3A50 x 1 → Sep (acSlot B 0x108) 32 x 1 → n2.mem x = n1.mem x :=
    fun x h1 h2 => by rw [mem2 x (aci_in h1 (by omega) (by omega)), copyBytes_sep h2 (Nat.le_refl 32)]
  have W2 : ∀ x, aciW B x → n2.mem x = n.mem x := fun x hx =>
    (W21 x hx.1 (aci_in hx.2.1 (by omega) (by omega))).trans (W1 x hx)
  have L21 : ∀ k, (k + 4 ≤ 0x108 ∨ 0x128 ≤ k) → k + 4 ≤ 0x2000 →
      memLoad32 n2.mem (acSlot B k) = memLoad32 n1.mem (acSlot B k) := fun k h1 h2 =>
    memLoad32_congr fun j hj => by
      rw [aci_ad]
      exact W21 _ (sep_offsets B (by omega) (by omega) (by omega)) (sep_offsets B (by omega) (by omega) (by omega))
  have P21 : ∀ i, i < 32 →
      n2.mem (acSlot B 0x108 + BitVec.ofNat 32 i) = n1.mem (acSlot B 0xD4 + BitVec.ofNat 32 i) := fun i hi => by
    rw [mem2 (acSlot B 0x108 + BitVec.ofNat 32 i)
      (by rw [aci_ad]; exact sep_offsets B (by omega) (by omega) (by omega))]
    exact aci_cp hi (by decide)
  /- 0x1C2: store the fields `accept_slot` keeps, and call `image::parse`. -/
  have rsp2 : reg n2 sp = B + BitVec.ofNat 32 0x3A50 := by rw [k2 sp (by decide), k1 sp (by decide), rsp]
  have hz2 := s2.zero
  obtain ⟨n3, c3, u3⟩ := s2.block aciB (aci_code F C W2) aciB_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, aciB]
    simp +decide only [upd, ↓reduceIte, true_and, and_true, aluEval]
    rw [rsp2]; aci_norm
    exact ⟨aci_al F (by decide) (by decide), ⟨aci_al F (by decide) (by decide), aci_sc F (by decide)⟩,
      ⟨aci_al F (by decide) (by decide), aci_sc F (by decide)⟩, ⟨aci_al F (by decide) (by decide), aci_sc F (by decide)⟩,
      ⟨aci_al F (by decide) (by decide), aci_sc F (by decide)⟩, ⟨aci_al F (by decide) (by decide), aci_sc F (by decide)⟩⟩)
  have m3 : n3.mem = memStore32 (memStore32 (memStore32 (memStore32 (memStore32 n2.mem (acSlot B 0xFC)
      (memLoad32 n2.mem (acSlot B 0x34))) (acSlot B 0x100) (reg n2 8)) (acSlot B 0x128) (reg n2 24))
      (acSlot B 0x12C) (reg n2 9)) (acSlot B 0x130) (reg n2 9) := by
    rw [u3.mem]; simp +decide only [runBlock, BInstr.run, aciB, upd, ↓reduceIte, aluEval]; rw [rsp2]; aci_norm
  have k3 : ∀ q : Fin 32, q.val ∉ [10, 11, 12, 13, 23] → reg n3 q = reg n2 q := fun q hq => by
    rw [u3.regs, runBlock_reg _ _ _ q hz2 (by simp only [aciB]; revert hq; revert q; decide)]
  have W3 : ∀ x, aciW B x → n3.mem x = n.mem x := fun x hx => by
    rw [m3, aci_w32 hx 0x130 (by decide) (by decide), aci_w32 hx 0x12C (by decide) (by decide),
      aci_w32 hx 0x128 (by decide) (by decide), aci_w32 hx 0x100 (by decide) (by decide),
      aci_w32 hx 0xFC (by decide) (by decide), W2 x hx]
  have a03 : reg n3 a0 = acSlot B 0x1870 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, aciB, upd, ↓reduceIte, aluEval]; rw [rsp2]; aci_norm
  have a13 : reg n3 a1 = reg n 25 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, aciB, upd, ↓reduceIte, aluEval]
    rw [aci_z, k2 25 (by decide), k1 25 (by decide)]
  have a23 : reg n3 a2 = reg n 22 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, aciB, upd, ↓reduceIte, aluEval]
    rw [aci_z, k2 22 (by decide), k1 22 (by decide)]
  have a33 : reg n3 a3 = reg n 27 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, aciB, upd, ↓reduceIte, aluEval]
    rw [aci_z, k2 27 (by decide), k1 27 (by decide)]
  have r233 : reg n3 (23 : Fin 32) = reg n 9 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, aciB, upd, ↓reduceIte, aluEval]
    rw [aci_z, k2 9 (by decide), k1 9 (by decide)]
  have K3 : Cur.ICode n3.mem (BitVec.ofNat 32 imageParseAddress) := aci_env hE I.out W3
  have s3 : St n3.mem AC n3 0x1E2 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  obtain ⟨m, cm, pcm, memm, regsm⟩ := s3.callRa (cb := BitVec.ofNat 32 imageParseAddress) (aci_code F C W3)
    ac_at_1e2 ac_at_1e6 (by decide) (by decide)
  have rm : ∀ q, q ≠ ra → reg m q = reg n3 q := fun q h => by rw [regsm]; exact updz s3.zero h
  have hlen : (BitVec.ofNat 32 (min mf.image.length 0x114)).toNat = min mf.image.length 0x114 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hpos : (Bf + 0xB840 : Word).toNat = Bf.toNat + 0xB840 := by
    rw [BitVec.toNat_add]; have : (0xB840 : Word).toNat = 0xB840 := rfl; rw [this]; omega
  have hFa := F.al; have hFh := F.hi
  have env : Cur.IEnv (BitVec.ofNat 32 imageParseAddress) (B + BitVec.ofNat 32 0x38C0)
      (B + BitVec.ofNat 32 0x38C0 + BitVec.ofNat 32 0x30) (reg n 25) (reg n 22) (acSlot B 0x1870) := {
    hP := by decide
    hRG := rfl
    hG := by rw [add_ofNat_assoc, F.at _ (by omega)]; omega
    hout := by
      show (B + BitVec.ofNat 32 (0x3A50 + 0x1870)).toNat % 4 = 0
      rw [F.at _ (by omega)]; omega
    hwrap := by
      show (B + BitVec.ofNat 32 (0x3A50 + 0x1870)).toNat + 0x110 ≤ 2 ^ 32
      rw [F.at _ (by omega)]; omega
    hbuf := by
      rw [h25, h22, hlen]
      refine ⟨fun e => ?_, by rw [hpos]; omega⟩
      have h0 := congrArg BitVec.toNat e
      rw [hpos] at h0; have : (0 : Word).toNat = 0 := rfl; omega
    hSW := F.sepHi (by omega) (by decide) (by decide)
    hST := F.bufData (by omega) (by decide) (by decide)
    hOW := F.sepHi (by omega) (by decide) (by decide)
    hOS := sep_offsets B (by omega) (by omega) (by omega)
    hBS := by
      rw [h25, h22, hlen]
      exact (sBf.symm.sub (c := 0xB840) (l := min mf.image.length 0x114) (by show _ ≤ 0xB954; omega)).subR
        (c := 0x38C0) (l := 0x190) (by omega)
    hRw := by rw [F.at _ (by omega)]; omega }
  have code : Cur.ICode m.mem (BitVec.ofNat 32 imageParseAddress) := by rw [memm]; exact K3
  have hsp : reg m sp = B + BitVec.ofNat 32 0x38C0 + BitVec.ofNat 32 0x30 + 0x160 := by
    rw [rm sp (by decide), k3 sp (by decide), rsp2]; exact aci_spG B
  have H := Cur.imageParse_correct (ilen := reg n 27) m env code pcm (by rw [rm a0 (by decide)]; exact a03)
    (by rw [rm a1 (by decide)]; exact a13) (by rw [rm a2 (by decide)]; exact a23)
    (by rw [rm a3 (by decide)]; exact a33) hsp
  obtain ⟨n4, c4, pc4, sp4, k4, mem4, res4⟩ : ∃ n4, Steps m n4 ∧ n4.pc = reg m ra &&& ~~~1 ∧
      reg n4 sp = B + BitVec.ofNat 32 0x38C0 + BitVec.ofNat 32 0x30 + 0x160 ∧
      (∀ r, r ∉ ipTmp → r ≠ sp → reg n4 r = reg m r) ∧
      (∀ x, Sep (B + BitVec.ofNat 32 0x38C0) 0x190 x 1 → Sep (acSlot B 0x1870) 0x110 x 1 → n4.mem x = m.mem x) ∧
      match imgW m.mem (reg n 25) (reg n 22) (reg n 27) with
      | .error e => n4.mem (acSlot B 0x1870) = e ∧ n4.mem (acSlot B 0x1870 + 0xC) = 0xFF
      | .ok (sv, entry, cnt, segs) => OutOk n4.mem (acSlot B 0x1870) sv entry cnt (reg n 27) segs := by
    revert H
    cases imgW m.mem (reg n 25) (reg n 22) (reg n 27) with
    | error e => exact fun ⟨n4, h1, h2, h3, h4, h5, h6, h7⟩ => ⟨n4, h1, h2, h3, h4, h5, h6, h7⟩
    | ok res =>
      obtain ⟨sv, entry, cnt, segs⟩ := res
      exact fun ⟨n4, h1, h2, h3, h4, h5, h6⟩ => ⟨n4, h1, h2, h3, h4, h5, h6⟩
  have pc4' : n4.pc = AC + BitVec.ofNat 32 0x1EA := by
    rw [pc4, regsm]; simp +decide only [upd, ↓reduceIte]
  have rsp4 : reg n4 sp = B + BitVec.ofNat 32 0x3A50 := by rw [sp4]; exact (aci_spG B).symm
  have k4' : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
      reg n4 q = reg n3 q := fun q hq => by
    rw [k4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      rm q (by revert hq; revert q; decide)]
  have W4 : ∀ x, aciW B x → n4.mem x = n.mem x := fun x hx => by
    rw [mem4 x (aci_in hx.1 (by omega) (by omega)) hx.2.2, memm, W3 x hx]
  have WL4 : ∀ x, aciL B x → Sep (acSlot B 0x1870) 0x110 x 1 → n4.mem x = n3.mem x := fun x hx ho => by
    rw [mem4 x (aci_in hx.1 (by omega) (by omega)) ho, memm]
  /- 0x1EA: read the result's first byte and byte 0xC. -/
  have s4 : St n4.mem AC n4 0x1EA (reg n4) := ⟨pc4', rfl, fun _ => rfl⟩
  have C4 := aci_code F C W4
  obtain ⟨n5, c5, u5⟩ := s4.block aciC C4 aciC_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := by rw [u5.mem]; rfl
  have k5 : ∀ q : Fin 32, q.val ∉ [9, 10, 21, 25] → reg n5 q = reg n4 q := fun q hq => by
    rw [u5.regs, runBlock_reg _ _ _ q s4.zero (by simp only [aciC]; revert hq; revert q; decide)]
  have r95 : reg n5 (9 : Fin 32) = acSlot B 0x1310 := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, aciC, upd, ↓reduceIte, aluEval]; rw [rsp4]; aci_norm
  have r255 : reg n5 (25 : Fin 32) = (n4.mem (acSlot B 0x187C)).zeroExtend 32 := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, aciC, upd, ↓reduceIte, aluEval]; rw [rsp4]; aci_norm
  have r215 : reg n5 (21 : Fin 32) = (n4.mem (acSlot B 0x1870)).zeroExtend 32 := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, aciC, upd, ↓reduceIte, aluEval]; rw [rsp4]; aci_norm
  have ra05 : reg n5 a0 = (n4.mem (acSlot B 0x187C)).zeroExtend 32 + 0xFFFFFF01 := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, aciC, upd, ↓reduceIte, aluEval]; rw [rsp4]; aci_norm
  have s5 : St n5.mem AC n5 0x200 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have C5 : CodeIn n5.mem AC bootMainClosure0Code := by rw [m5]; exact C4
  have rsp5 : reg n5 sp = B + BitVec.ofNat 32 0x3A50 := by rw [k5 sp (by decide), rsp4]
  have T5 : Steps n n5 := c1.trans (c2.trans (c3.trans (cm.trans (c4.trans c5))))
  have g5 : ∀ q : Fin 32, q.val ∈ [3, 4, 20, 24, 26] → reg n5 q = reg n q := fun q hq => by
    rw [k5 q (by revert hq; revert q; decide), k4' q (by revert hq; revert q; decide),
      k3 q (by revert hq; revert q; decide), k2 q (by revert hq; revert q; decide),
      k1 q (by revert hq; revert q; decide)]
  have Rr := imgW_rel (M := m.mem) (ptr := reg n 25) (len := reg n 22) (ilen := reg n 27)
  cases hi : imgW m.mem (reg n 25) (reg n 22) (reg n 27) with
  | error e =>
    /- The header doesn't parse: go to 0x7D6. -/
    rw [hi] at res4
    obtain ⟨he0, heC⟩ := res4
    have heC' : n4.mem (acSlot B 0x187C) = 0xFF := by
      rwa [show acSlot B 0x1870 + (0xC : Word) = acSlot B 0x187C from aci_ad B 0x1870 0xC] at heC
    obtain ⟨n6, e6, s6⟩ := s5.taken C5 0x7D6 ac_at_200 (by decide) (by
      show (reg n5 a0 == reg n5 x0) = true
      rw [ra05, heC', s5.zero]; decide)
    refine ⟨n6, T5.trans (.single e6), Or.inr ⟨aci_inv I ?_ ?_ ?_ ?_,
      Or.inl (Or.inr (Or.inr (Or.inl ⟨s6.pc, ?_, ?_⟩)))⟩⟩
    · rw [s6.regs, rsp5] <;> rfl
    · rw [s6.regs, g5 3 (by decide)]
    · rw [s6.regs, g5 4 (by decide)]
    · intro x hx; rw [s6.mem, m5, W4 x hx]
    · rw [s6.mem, m5, ← h40]; exact aci_ldW W4 0x40 (by decide)
    · rw [s6.regs, r215, he0]; exact aci_e e (aci_imgW_err _ _ _ _ hi)
  | ok res =>
    obtain ⟨sv, entry, cnt, segs⟩ := res
    rw [hi] at res4 Rr
    rw [h27] at res4
    obtain ⟨hne, hl16, hkind⟩ := aci_imgW_ok hi
    have hp0 : 0 < segs.length := by
      cases segs with
      | nil => exact absurd rfl hne
      | cons _ _ => exact Nat.succ_pos _
    have hk0 : n4.mem (acSlot B 0x187C) = segs[0].kind := by
      have := (res4.1 0 hp0).2.2.2
      rwa [show acSlot B 0x1870 + BitVec.ofNat 32 (16 * 0 + 12) = acSlot B 0x187C from aci_ad B 0x1870 _] at this
    have hsv : n4.mem (acSlot B 0x197C) = sv := by
      have := res4.2.2.2.2.2
      rwa [show acSlot B 0x1870 + (0x10C : Word) = acSlot B 0x197C from aci_ad B 0x1870 0x10C] at this
    have hbuf3 : memBytes n3.mem (Bf + 0xB840) (min mf.image.length 0x114) =
        flashBytes flash (acBase slot + mf.image.offset) (min mf.image.length 0x114) := by
      rw [← hhd]; apply aci_mb; intro i hi
      have h1 := sBf.symm.sub (c := 0xB840 + i) (l := 1) (by show _ ≤ 0xB954; omega)
      rw [← add_ofNat_assoc] at h1
      exact W3 _ (aci_outW h1)
    have Dd : decodeImageHeader (flashBytes flash (acBase slot + mf.image.offset) mf.image.length)
        mf.image.length = some (toHdr (BitVec.ofNat 32 mf.image.length) (sv, entry, cnt, segs)) := by
      rw [← aci_decode hL hbuf3, ← h22, ← h25, ← h27, ← memm]; exact Rr
    /- 0x204: the result's first segment is a known kind; copy bytes 1 to 0xB. -/
    obtain ⟨n6, e6, s6⟩ := s5.notTaken C5 0x204 ac_at_200 (by decide) (by
      show (reg n5 a0 == reg n5 x0) = false
      rw [ra05, hk0, s5.zero]; exact aci_kind _ (hkind _ (List.getElem_mem hp0)))
    obtain ⟨n7, c7, u7⟩ := s6.block aciD C5 aciD_end (by
      simp only [BlockOk, BInstr.ok, BInstr.run, aciD]
      simp +decide only [upd, ↓reduceIte, true_and, and_true]
      rw [rsp5]; aci_norm
      exact ⟨⟨aci_al F (by decide) (by decide), aci_sc F (by decide)⟩,
        ⟨aci_al F (by decide) (by decide), aci_sc F (by decide)⟩⟩)
    have W7 : ∀ x, aciL B x → n7.mem x = n5.mem x := fun x hx => by
      rw [u7.mem]; simp only [runBlock, BInstr.run, aciD]; simp +decide only [upd, ↓reduceIte]
      rw [rsp5]; aci_norm; simp (disch := decide) only [aci_l32 hx]
    have k7 : ∀ q : Fin 32, q.val ∉ [5, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17] → reg n7 q = reg n5 q :=
      fun q hq => by
        rw [u7.regs, runBlock_reg _ _ _ q s5.zero (by simp only [aciD]; revert hq; revert q; decide)]
    have s7 : St n7.mem AC n7 0x258 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
    have P7 : ∀ i, i < 8 → n7.mem (acSlot B (0x238 + i)) = n5.mem (acSlot B (0x1871 + i)) := fun i hi => by
      rw [u7.mem]; simp only [runBlock, BInstr.run, aciD]; simp +decide only [upd, ↓reduceIte]; rw [rsp5, r95]; aci_norm
      rw [acs_shA, acs_shB]; exact acs_st2 n5.mem n5.mem B 0x238 0x1871 i hi (by decide)
    have r177 : reg n7 (17 : Fin 32) = aluEval AluOp.or (aluEval AluOp.sll ((n5.mem (acSlot B 0x187A)).zeroExtend 32) 8)
        ((n5.mem (acSlot B 0x1879)).zeroExtend 32) := by
      rw [u7.regs]; simp +decide only [runBlock, BInstr.run, aciD, upd, ↓reduceIte]; rw [r95]; aci_norm
    have ra67 : reg n7 a6 = (n5.mem (acSlot B 0x187B)).zeroExtend 32 := by
      rw [u7.regs]; simp +decide only [runBlock, BInstr.run, aciD, upd, ↓reduceIte]; rw [r95]; aci_norm
    have rsp7 : reg n7 sp = B + BitVec.ofNat 32 0x3A50 := by rw [k7 sp (by decide), rsp5]
    have WW7 : ∀ x, aciW B x → n7.mem x = n.mem x := fun x hx => by rw [W7 x (aci_WL hx), m5, W4 x hx]
    obtain ⟨n8, e8, s8⟩ := s7.sh (off' := 0x25C) (aci_code F C WW7) ac_at_258 (by decide)
      (by rw [rsp7]; aci_norm; exact aci_al2 F (by decide) (by decide))
    have W8 : ∀ x, aciL B x → n8.mem x = n7.mem x := fun x hx => by
      rw [s8.mem, rsp7]; aci_norm; simp (disch := decide) only [aci_l8 hx]
    /- 0x25C: copy bytes 0xB to 0x10B. -/
    have s8' : St n8.mem AC n8 0x25C (reg n8) := ⟨s8.pc, rfl, fun _ => rfl⟩
    have rsp8 : reg n8 sp = B + BitVec.ofNat 32 0x3A50 := by rw [s8.regs, rsp7]
    have WW8 : ∀ x, aciW B x → n8.mem x = n.mem x := fun x hx => by rw [W8 x (aci_WL hx), WW7 x hx]
    obtain ⟨n9, c9, u9⟩ := s8'.block aciE (aci_code F C WW8) aciE_end (by
      simp only [BlockOk, BInstr.ok, aciE]
      simp +decide only [and_true]
      rw [rsp8]; aci_norm; exact aci_sc F (by decide))
    have W9 : ∀ x, aciL B x → n9.mem x = n8.mem x := fun x hx => by
      rw [u9.mem]; simp only [runBlock, BInstr.run, aciE]; rw [rsp8]; aci_norm
      simp (disch := decide) only [aci_l8 hx]
    have k9 : ∀ q : Fin 32, q.val ∉ [10, 11, 12] → reg n9 q = reg n8 q := fun q hq => by
      rw [u9.regs, runBlock_reg _ _ _ q s8'.zero (by simp only [aciE]; revert hq; revert q; decide)]
    have rsp9 : reg n9 sp = B + BitVec.ofNat 32 0x3A50 := by rw [k9 sp (by decide), rsp8]
    have P9 : ∀ i, i < 11 → n9.mem (acSlot B (0x238 + i)) = n5.mem (acSlot B (0x1871 + i)) := fun i hi => by
      have E9 : ∀ j, j < 10 → n9.mem (acSlot B (0x238 + j)) = n8.mem (acSlot B (0x238 + j)) := fun j hj => by
        rw [u9.mem]; simp only [runBlock, BInstr.run, aciE]; rw [rsp8]; aci_norm
        exact acs_s8 0x242 (0x238 + j) (by omega) (by decide) (by omega)
      have E8 : ∀ j, j < 8 → n8.mem (acSlot B (0x238 + j)) = n7.mem (acSlot B (0x238 + j)) := fun j hj => by
        rw [s8.mem, rsp7]; aci_norm
        rw [acs_s8 0x241 (0x238 + j) (by omega) (by decide) (by omega),
          acs_s8 0x240 (0x238 + j) (by omega) (by decide) (by omega)]
      rcases Nat.lt_or_ge i 8 with h | h
      · rw [E9 i (by omega), E8 i h, P7 i h]
      · obtain ⟨j, rfl⟩ : ∃ j, i = 8 + j := ⟨i - 8, by omega⟩
        match j, hi with
        | 0, _ =>
          refine (E9 8 (by omega)).trans ?_
          show n8.mem (acSlot B 0x240) = n5.mem (acSlot B 0x1879)
          rw [s8.mem, rsp7]; aci_norm
          rw [acs_s8 0x241 0x240 (by omega) (by decide) (by omega), memStore8_same, r177]; exact (acs_x2 _ _).1
        | 1, _ =>
          refine (E9 9 (by omega)).trans ?_
          show n8.mem (acSlot B 0x241) = n5.mem (acSlot B 0x187A)
          rw [s8.mem, rsp7]; aci_norm
          rw [memStore8_same, r177]; exact (acs_x2 _ _).2
        | 2, _ =>
          show n9.mem (acSlot B 0x242) = n5.mem (acSlot B 0x187B)
          rw [u9.mem]; simp only [runBlock, BInstr.run, aciE]; rw [rsp8]; aci_norm
          rw [memStore8_same, s8.regs, ra67]; exact acs_ilo8 _
        | j + 3, h => exact absurd h (by omega)
    have a09 : reg n9 a0 = acSlot B 0x139 := by
      rw [u9.regs]; simp +decide only [runBlock, BInstr.run, aciE, upd, ↓reduceIte, aluEval]; rw [rsp8]; aci_norm
    have a19 : reg n9 a1 = acSlot B 0x187D := by
      rw [u9.regs]; simp +decide only [runBlock, BInstr.run, aciE, upd, ↓reduceIte, aluEval]; rw [rsp8]; aci_norm
    have a29 : reg n9 a2 = BitVec.ofNat 32 0xFF := by
      rw [u9.regs]; simp +decide only [runBlock, BInstr.run, aciE, upd, ↓reduceIte, aluEval]
    have WW9 : ∀ x, aciW B x → n9.mem x = n.mem x := fun x hx => by rw [W9 x (aci_WL hx), WW8 x hx]
    have K9 : Cur.ICode n9.mem (BitVec.ofNat 32 imageParseAddress) := aci_env hE I.out WW9
    have s9 : St n9.mem AC n9 0x272 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    obtain ⟨n10, c10, s10, mem10, k10⟩ := aci_mc (N := 0xFF) (S := B + BitVec.ofNat 32 0x3A50) s9
      (aci_code F C WW9) (by have := K9.stub; rwa [aci_stub] at this) ac_at_272 ac_at_276 (by decide)
      (by decide) rsp9 a09 a19 a29 (aci_mce F K9 (by omega) (by omega) (by omega) (by omega) (by omega))
    rw [aci_fr] at mem10
    have W109 : ∀ x, aciL B x → n10.mem x = n9.mem x := fun x hx => by
      rw [mem10 x (aci_in hx.1 (by omega) (by omega)),
        copyBytes_sep (dst := acSlot B 0x139) (n := 0xFF) (aci_in hx.2 (by omega) (by omega)) (Nat.le_refl _)]
    have L10 : ∀ x, aciL B x → n10.mem x = n4.mem x := fun x hx => by
      rw [W109 x hx, W9 x hx, W8 x hx, W7 x hx, m5]
    /- 0x27A: read the security version and the eFuse level. -/
    have r910 : reg n10 (9 : Fin 32) = acSlot B 0x1310 := by
      rw [k10 9 (by decide), k9 9 (by decide), s8.regs, k7 9 (by decide), r95]
    have WW10 : ∀ x, aciW B x → n10.mem x = n.mem x := fun x hx => by rw [W109 x (aci_WL hx), WW9 x hx]
    obtain ⟨n11, c11, u11⟩ := s10.block aciF (aci_code F C WW10) aciF_end
      ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
    have m11 : n11.mem = n10.mem := by rw [u11.mem]; rfl
    have k11 : ∀ q : Fin 32, q.val ∉ [10, 11, 12, 27] → reg n11 q = reg n10 q := fun q hq => by
      rw [u11.regs, runBlock_reg _ _ _ q s10.zero (by simp only [aciF]; revert hq; revert q; decide)]
    have r2711 : reg n11 (27 : Fin 32) = (n10.mem (acSlot B 0x197C)).zeroExtend 32 := by
      rw [u11.regs]; simp +decide only [runBlock, BInstr.run, aciF, upd, ↓reduceIte, aluEval]; rw [r910]; aci_norm
    have ra111 : reg n11 a1 = reg n10 (26 : Fin 32) &&& 0xFF := by
      rw [u11.regs]; simp +decide only [runBlock, BInstr.run, aciF, upd, ↓reduceIte, aluEval]
    have s11 : St n11.mem AC n11 0x292 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have rsp11 : reg n11 sp = B + BitVec.ofNat 32 0x3A50 := by
      rw [k11 sp (by decide), k10 sp (by decide), k9 sp (by decide), rsp8]
    have WW11 : ∀ x, aciW B x → n11.mem x = n.mem x := fun x hx => by rw [m11, WW10 x hx]
    obtain ⟨n12, e12, s12⟩ := s11.sh (off' := 0x296) (aci_code F C WW11) ac_at_292 (by decide)
      (by rw [rsp11]; aci_norm; exact aci_al2 F (by decide) (by decide))
    have W12 : ∀ x, aciL B x → n12.mem x = n11.mem x := fun x hx => by
      rw [s12.mem, rsp11]; aci_norm; simp (disch := decide) only [aci_l8 hx]
    have s12' : St n12.mem AC n12 0x296 (reg n12) := ⟨s12.pc, rfl, fun _ => rfl⟩
    have rsp12 : reg n12 sp = B + BitVec.ofNat 32 0x3A50 := by rw [s12.regs, rsp11]
    have WW12 : ∀ x, aciW B x → n12.mem x = n.mem x := fun x hx => by rw [W12 x (aci_WL hx), WW11 x hx]
    obtain ⟨n13, c13, u13⟩ := s12'.block aciG (aci_code F C WW12) aciG_end (by
      simp only [BlockOk, BInstr.ok, aciG, and_true]; rw [rsp12]; aci_norm; exact aci_sc F (by decide))
    have W13 : ∀ x, aciL B x → n13.mem x = n12.mem x := fun x hx => by
      rw [u13.mem]; simp only [runBlock, BInstr.run, aciG]; rw [rsp12]; aci_norm
      simp (disch := decide) only [aci_l8 hx]
    have r13 : ∀ q, reg n13 q = reg n11 q := fun q => by rw [u13.regs]; exact s12.regs q
    have L13 : ∀ x, aciL B x → n13.mem x = n4.mem x := fun x hx => by
      rw [W13 x hx, W12 x hx, m11, L10 x hx]
    have WW13 : ∀ x, aciW B x → n13.mem x = n.mem x := fun x hx => by rw [L13 x (aci_WL hx), W4 x hx]
    have E13 : ∀ x, aciL B x → Sep (acSlot B 0x1870) 0x110 x 1 → n13.mem x = n3.mem x := fun x hx ho => by
      rw [L13 x hx, WL4 x hx ho]
    have g13 : ∀ q : Fin 32, q.val ∈ [3, 4, 20, 24, 26] → reg n13 q = reg n q := fun q hq => by
      rw [r13, k11 q (by revert hq; revert q; decide), k10 q (by revert hq; revert q; decide),
        k9 q (by revert hq; revert q; decide), s8.regs, k7 q (by revert hq; revert q; decide), g5 q hq]
    have rsp13 : reg n13 sp = B + BitVec.ofNat 32 0x3A50 := by rw [r13, rsp11]
    have r2713 : reg n13 (27 : Fin 32) = sv.zeroExtend 32 := by
      rw [r13, r2711, L10 (acSlot B 0x197C) (aci_ptL (by decide) (by decide) (by decide)), hsv]
    have ra113 : reg n13 a1 = level &&& 0xFF := by
      rw [r13, ra111, k10 26 (by decide), k9 26 (by decide), s8.regs, k7 26 (by decide), g5 26 (by decide), h26]
    have s13 : St n13.mem AC n13 0x29A (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
    have C13 := aci_code F C WW13
    have T13 : Steps n n13 := T5.trans ((Steps.single e6).trans (c7.trans ((Steps.single e8).trans
      (c9.trans (c10.trans (c11.trans ((Steps.single e12).trans c13)))))))
    cases hb : (sv.zeroExtend 32 : Word).ult (level &&& 0xFF) with
    | true =>
      /- The security version is below the eFuse level: go to 0x802. -/
      obtain ⟨n14, e14, s14⟩ := s13.notTaken C13 0x29E ac_at_29a (by decide) (by
        show (!(reg n13 (27 : Fin 32)).ult (reg n13 a1)) = false
        rw [r2713, ra113, hb]; rfl)
      obtain ⟨n15, c15, u15⟩ := s14.block aciH C13 aciH_end (by
        simp only [BlockOk, BInstr.ok, BInstr.run, aciH]
        simp +decide only [upd, ↓reduceIte, true_and, and_true]
        rw [rsp13]; aci_norm
        exact ⟨aci_al F (by decide) (by decide), aci_al F (by decide) (by decide)⟩)
      obtain ⟨n16, e16, s16⟩ := u15.jump (off' := 0x802) C13 ac_at_2a4 (by decide) (by rw [u15.pc]; decide)
      refine ⟨n16, T13.trans ((Steps.single e14).trans (c15.trans (.single e16))),
        Or.inr ⟨aci_inv I ?_ ?_ ?_ ?_, Or.inl (Or.inr (Or.inr (Or.inr ⟨s16.pc, ?_⟩)))⟩⟩
      · rw [s16.regs]; simp +decide only [runBlock, BInstr.run, aciH, upd, ↓reduceIte]; rw [rsp13] <;> rfl
      · rw [s16.regs]; simp +decide only [runBlock, BInstr.run, aciH, upd, ↓reduceIte]; rw [g13 3 (by decide)]
      · rw [s16.regs]; simp +decide only [runBlock, BInstr.run, aciH, upd, ↓reduceIte]; rw [g13 4 (by decide)]
      · intro x hx; rw [s16.mem]; exact WW13 x hx
      · rw [s16.regs]; simp +decide only [runBlock, BInstr.run, aciH, upd, ↓reduceIte]; rw [rsp13]; aci_norm
        rw [aci_ldW WW13 0x40 (by decide)]; exact h40
    | false =>
      /- 0x2A6: the image's header decodes, and its security version is at least the eFuse level. -/
      obtain ⟨n14, e14, s14⟩ := s13.taken C13 0x2A6 ac_at_29a (by decide) (by
        show (!(reg n13 (27 : Fin 32)).ult (reg n13 a1)) = true
        rw [r2713, ra113, hb]; rfl)
      have Q13 : ∀ i, i < 0xFF →
          n13.mem (acSlot B 0x139 + BitVec.ofNat 32 i) = n10.mem (acSlot B 0x139 + BitVec.ofNat 32 i) :=
        fun i hi => by
          rw [u13.mem]; simp only [runBlock, BInstr.run, aciG]; rw [rsp12]; aci_norm
          rw [aci_s8i 0x138 0x139 i (by omega) (by decide) (by omega), s12.mem, rsp11]; aci_norm
          rw [aci_s8i 0x137 0x139 i (by omega) (by decide) (by omega),
            aci_s8i 0x136 0x139 i (by omega) (by decide) (by omega), m11]
      have L13w : ∀ k, k + 4 ≤ 0x136 → memLoad32 n13.mem (acSlot B k) = memLoad32 n3.mem (acSlot B k) :=
        fun k hk => aci_ldL E13 k hk
      have P13 : ∀ i, i < 11 → n13.mem (acSlot B (0x238 + i)) = n4.mem (acSlot B (0x1871 + i)) :=
        fun i hi => by
          rw [u13.mem]; simp only [runBlock, BInstr.run, aciG]; rw [rsp12]; aci_norm
          rw [acs_s8 0x138 (0x238 + i) (by omega) (by decide) (by omega), s12.mem, rsp11]; aci_norm
          rw [acs_s8 0x137 (0x238 + i) (by omega) (by decide) (by omega),
            acs_s8 0x136 (0x238 + i) (by omega) (by decide) (by omega), m11,
            mem10 _ (sep_offsets B (by omega) (by omega) (by omega)),
            copyBytes_sep (dst := acSlot B 0x139) (n := 0xFF) (sep_offsets B (by omega) (by omega) (by omega))
              (Nat.le_refl _), P9 i hi, m5]
      have e14m : n14.mem = n13.mem := s14.mem
      have e14r : ∀ q, reg n14 q = reg n13 q := s14.regs
      refine ⟨n14, T13.trans (.single e14), Or.inr ⟨aci_inv I ?_ ?_ ?_ ?_, Or.inr ⟨s14.pc, ?_⟩⟩⟩
      · rw [e14r, rsp13] <;> rfl
      · rw [e14r, g13 3 (by decide)]
      · rw [e14r, g13 4 (by decide)]
      · intro x hx; rw [e14m]; exact WW13 x hx
      simp only [AcImagePost, e14m, e14r]
      refine ⟨⟨_, Dd, aci_ge sv _ hb, ?_, sv, entry, cnt, segs, rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [r2713]; exact (BitVec.ofNat_toNat 32 sv).symm
      · exact ⟨aci_outok res4 hl16 fun i hi => by
          rw [aci_ad]; exact L13 _ (aci_ptL (by omega) (by omega) (by omega)), acs_imgW_cnt hi, hp0, hkind⟩
      · rw [r13, k11 9 (by decide), r910]
      · exact g13 20 (by decide)
      · rw [r13, k11 21 (by decide), k10 21 (by decide), k9 21 (by decide), s8.regs, k7 21 (by decide), r215,
          L13 (acSlot B 0x1870) (aci_ptL (by decide) (by decide) (by decide))]
      · rw [r13, k11 23 (by decide), k10 23 (by decide), k9 23 (by decide), s8.regs, k7 23 (by decide),
          k5 23 (by decide), k4' 23 (by decide), r233]
      · exact g13 24 (by decide)
      · rw [r13, k11 25 (by decide), k10 25 (by decide), k9 25 (by decide), s8.regs, k7 25 (by decide), r255,
          L13 (acSlot B 0x187C) (aci_ptL (by decide) (by decide) (by decide))]
      · rw [g13 26 (by decide), h26]
      · rw [L13w 0xF4 (by decide), m3]; simp (disch := decide) only [aci_lsep]
        rw [L21 0xF4 (by decide) (by decide), m1]; simp (disch := decide) only [aci_lsep, memLoad32_store32_same]
      · rw [L13w 0xF8 (by decide), m3]; simp (disch := decide) only [aci_lsep]
        rw [L21 0xF8 (by decide) (by decide), m1]; simp (disch := decide) only [aci_lsep, memLoad32_store32_same]
      · rw [L13w 0xFC (by decide), m3]; simp (disch := decide) only [aci_lsep, memLoad32_store32_same]
        rw [L21 0x34 (by decide) (by decide), m1]; simp (disch := decide) only [aci_lsep]
      · rw [L13w 0x100 (by decide), m3]; simp (disch := decide) only [aci_lsep, memLoad32_store32_same]
        rw [k2 8 (by decide), k1 8 (by decide)]
      · rw [L13w 0x104 (by decide), m3]; simp (disch := decide) only [aci_lsep]
        rw [L21 0x104 (by decide) (by decide), m1]; simp (disch := decide) only [memLoad32_store32_same]
      · rw [L13w 0x128 (by decide), m3]; simp (disch := decide) only [aci_lsep, memLoad32_store32_same]
        rw [k2 24 (by decide), k1 24 (by decide)]
      · rw [L13w 0x12C (by decide), m3]; simp (disch := decide) only [aci_lsep, memLoad32_store32_same]
        rw [k2 9 (by decide), k1 9 (by decide)]
      · rw [L13w 0x130 (by decide), m3]; simp (disch := decide) only [memLoad32_store32_same]
        rw [k2 9 (by decide), k1 9 (by decide)]
      · apply aci_mb; intro i hi
        rw [E13 (acSlot B 0x108 + BitVec.ofNat 32 i) (by rw [aci_ad]; exact aci_ptL (by omega) (by omega) (by omega))
          (by rw [aci_ad]; exact sep_offsets B (by omega) (by omega) (by omega)), m3]
        simp (disch := omega) only [aci_s32i]
        rw [P21 i hi, m1]
        simp (disch := omega) only [aci_s32i]
      · apply aci_mb; intro i hi
        have hp : aciL B (acSlot B 0x187D + BitVec.ofNat 32 i) := by
          rw [aci_ad]; exact aci_ptL (by omega) (by omega) (by omega)
        rw [Q13 i hi, mem10 (acSlot B 0x139 + BitVec.ofNat 32 i)
          (by rw [aci_ad]; exact sep_offsets B (by omega) (by omega) (by omega)), aci_cp hi (by decide),
          L13 _ hp, W9 _ hp, W8 _ hp, W7 _ hp, m5]
      · intro i hi
        rw [P13 i hi, L13 _ (aci_ptL (by omega) (by omega) (.inr (by omega)))]
      · intro x h1 h2 h3
        exact WW13 x ⟨by rw [add_ofNat_zero]; exact h1, h2, h3⟩

end C3.RV32.Ac
