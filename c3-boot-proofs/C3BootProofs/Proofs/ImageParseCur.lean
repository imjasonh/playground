import C3BootProofs.Proofs.ImageTop
import C3BootProofs.Proofs.MagicCur

/-!
# `c3_verify::image::parse` on the current image: code, layout, epilogue

The current image compiles `image::parse` as V0 did, with one difference:
its epilogue loads `ra` and `s0` through `s11` inline instead of through an
outlined helper, so every instruction after the epilogue sits 0x14 bytes
later. The spec is V0's `imgW`. This file gives the code window and layout
the proofs use, the decoded instructions, and the inline epilogue, with the
same names and shapes as V0's so the stage proofs carry over.
-/

namespace C3.RV32.Cur

open C3.Image

set_option maxRecDepth 20000

/-- `image::parse`'s code window: from `Reader::magic`, the lowest function it
reaches, to the end of `memcpy`, the highest. -/
abbrev ipWindow (P : Word) : Word := P + 0xFFFFFD2E

abbrev ipWindowLen : Nat := 0xBA46

/-- The functions `image::parse` runs, and the region tables it reads, where
the image puts them relative to it. -/
structure ICode (M : Word → BitVec 8) (P : Word) : Prop where
  parse : CodeIn M P imageParseCode
  magic : CodeIn M (P + 0xFFFFFD2E) readerMagicCode
  version : CodeIn M (P + 0xFFFFFD80) readerVersion1Code
  u8 : CodeIn M (P + 0xFFFFFDAA) readerU8Code
  reserved : CodeIn M (P + 0xFFFFFDE4) readerReservedCode
  bytes : CodeIn M (P + 0xFFFFFE80) readerBytesCode
  u16 : CodeIn M (P + 0xFFFFFEA6) readerU16Code
  array4 : CodeIn M (P + 0xFFFFFEEA) readerArray4Code
  u32 : CodeIn M (P + 0x434) readerU32Code
  physical : CodeIn M (P + 0x484) segmentPhysicalCode
  stub : CodeIn M (P + 0xB5E6) memcpyStubCode
  body : CodeIn M (P + 0xB5EE) memcpyBodyCode
  ends : CodeIn M 0x3FCC5240 regionEndsData
  starts : CodeIn M 0x3FCC5250 regionStartsData

theorem ip_wq (P x : Word) (c : Nat) (h : x = 0xFFFFFD2E + BitVec.ofNat 32 c) :
    P + x = ipWindow P + BitVec.ofNat 32 c := by rw [h, ← BitVec.add_assoc]

theorem ip_wP (P : Word) : P = ipWindow P + BitVec.ofNat 32 0x2D2 := by
  show P = P + 0xFFFFFD2E + BitVec.ofNat 32 0x2D2
  rw [BitVec.add_assoc, show (0xFFFFFD2E : Word) + BitVec.ofNat 32 0x2D2 = 0 from rfl]
  exact (BitVec.add_zero P).symm

theorem codeIn_of_ipWindow {M M' : Word → BitVec 8} {P b : Word} {code : List Nat} (c : Nat)
    (hb : b = ipWindow P + BitVec.ofNat 32 c) (hl : c + code.length ≤ ipWindowLen)
    (hc : CodeIn M b code)
    (h : ∀ k, k < ipWindowLen → M' (ipWindow P + BitVec.ofNat 32 k) = M (ipWindow P + BitVec.ofNat 32 k)) :
    CodeIn M' b code := fun i hi => by
  have e : b + BitVec.ofNat 32 i = ipWindow P + BitVec.ofNat 32 (c + i) := by rw [hb, add_ofNat_assoc]
  rw [e, h _ (by omega), ← e]; exact hc i hi

set_option maxRecDepth 8000 in
/-- `ICode` holds in any memory that agrees on the code window and the tables. -/
theorem ICode.of_agree {M M' : Word → BitVec 8} {P : Word} (hc : ICode M P)
    (h : ∀ k, k < ipWindowLen → M' (ipWindow P + BitVec.ofNat 32 k) = M (ipWindow P + BitVec.ofNat 32 k))
    (ht : ∀ k, k < 32 → M' (0x3FCC5240 + BitVec.ofNat 32 k) = M (0x3FCC5240 + BitVec.ofNat 32 k)) :
    ICode M' P where
  parse := codeIn_of_ipWindow 0x2D2 (ip_wP P) (by decide) hc.parse h
  magic := codeIn_of_ipWindow 0 (ip_wq P _ _ (by decide)) (by decide) hc.magic h
  version := codeIn_of_ipWindow 0x52 (ip_wq P _ _ (by decide)) (by decide) hc.version h
  u8 := codeIn_of_ipWindow 0x7C (ip_wq P _ _ (by decide)) (by decide) hc.u8 h
  reserved := codeIn_of_ipWindow 0xB6 (ip_wq P _ _ (by decide)) (by decide) hc.reserved h
  bytes := codeIn_of_ipWindow 0x152 (ip_wq P _ _ (by decide)) (by decide) hc.bytes h
  u16 := codeIn_of_ipWindow 0x178 (ip_wq P _ _ (by decide)) (by decide) hc.u16 h
  array4 := codeIn_of_ipWindow 0x1BC (ip_wq P _ _ (by decide)) (by decide) hc.array4 h
  u32 := codeIn_of_ipWindow 0x706 (ip_wq P _ _ (by decide)) (by decide) hc.u32 h
  physical := codeIn_of_ipWindow 0x756 (ip_wq P _ _ (by decide)) (by decide) hc.physical h
  stub := codeIn_of_ipWindow 0xB8B8 (ip_wq P _ _ (by decide)) (by decide) hc.stub h
  body := codeIn_of_ipWindow 0xB8C0 (ip_wq P _ _ (by decide)) (by decide) hc.body h
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

/-- The inline epilogue after `addi a0, sp, 0x100`: `ra` and `s0` through
`s11` relative to `a0`, then the frame freed. -/
def ipEpiBlock : List BInstr :=
  [.lw ra a0 0x5C, .lw s0 a0 0x58, .lw s1 a0 0x54, .lw s2 a0 0x50, .lw s3 a0 0x4C, .lw s4 a0 0x48, .lw s5 a0 0x44, .lw s6 a0 0x40, .lw s7 a0 0x3C, .lw s8 a0 0x38, .lw s9 a0 0x34, .lw s10 a0 0x30, .lw s11 a0 0x2C,
   .aluImm .add sp sp 0x160]

theorem ipEpiBlock_end : blockEnd imageParseCode 0xC2 ipEpiBlock = some 0xF4 := by decide

theorem ipc_at_c0' : fetchRel imageParseCode 0xC0 = some (.aluImm .add a0 sp 0x100, 2) := by decide
theorem ipc_at_f4' : fetchRel imageParseCode 0xF4 = some (.jalr x0 ra 0x0, 2) := by decide

/-- **`image::parse`'s epilogue.** From offset 0xC0 with the frame at `G`, it
restores `ra` and `s0` through `s11` from their slots, frees the frame, and
returns to the restored `ra`; of the other registers only `a0` changes. -/
theorem image_epilogue {Mx : Word → BitVec 8} {P G : Word} {m : Machine} {f : Fin 32 → Word}
    (s : St Mx P m 0xC0 f) (hc : CodeIn Mx P imageParseCode) (hsp : f sp = G) (hG : G.toNat % 4 = 0) :
    ∃ m', Steps m m' ∧ m'.pc = memLoad32 Mx (G + 0x15C) &&& ~~~1 ∧ m'.mem = Mx ∧
      reg m' sp = G + 0x160 ∧
      (∀ p, p ∈ ipSlots → reg m' p.1 = memLoad32 Mx (G + BitVec.ofNat 32 p.2)) ∧
      ∀ r, r ≠ a0 → r ≠ t0 → r ≠ sp → (∀ p, p ∈ ipSlots → r ≠ p.1) → reg m' r = f r := by
  have hz := s.zero
  obtain ⟨m1, e1, t1⟩ := s.aluImm hc ipc_at_c0' (off' := 0xC2) (by decide)
  have u1 := t1.self
  have ga : ∀ c, c % 4 = 0 → (G + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h => aligned_add hG h
  have a01 : reg m1 a0 = G + 0x100 := by rw [t1.regs]; simp +decide only [upd, aluEval, ↓reduceIte]; rw [hsp]
  have r1 : ∀ r, r ≠ a0 → reg m1 r = f r := fun r h => by rw [t1.regs]; exact updz hz h
  obtain ⟨m6, c6, t6⟩ := u1.block ipEpiBlock hc ipEpiBlock_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, ipEpiBlock]
    simp +decide only [upd, ↓reduceIte]
    rw [a01]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
      (rw [BitVec.add_assoc]; exact ga _ (by decide)))
  obtain ⟨m7, e7, pc7, mem7, regs7⟩ := t6.jalr hc ipc_at_f4'
  have F : ∀ r, (runBlock ipEpiBlock (Mx, reg m1)).2 r =
      upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (reg m1) ra (memLoad32 Mx (G + 0x100 + 0x5C))) s0 (memLoad32 Mx (G + 0x100 + 0x58))) s1 (memLoad32 Mx (G + 0x100 + 0x54))) s2 (memLoad32 Mx (G + 0x100 + 0x50))) s3 (memLoad32 Mx (G + 0x100 + 0x4C))) s4 (memLoad32 Mx (G + 0x100 + 0x48))) s5 (memLoad32 Mx (G + 0x100 + 0x44))) s6 (memLoad32 Mx (G + 0x100 + 0x40))) s7 (memLoad32 Mx (G + 0x100 + 0x3C))) s8 (memLoad32 Mx (G + 0x100 + 0x38))) s9 (memLoad32 Mx (G + 0x100 + 0x34))) s10 (memLoad32 Mx (G + 0x100 + 0x30))) s11 (memLoad32 Mx (G + 0x100 + 0x2C))) sp (reg m1 sp + 0x160) r := by
    intro r; simp only [runBlock, ipEpiBlock, BInstr.run, aluEval]
    simp +decide only [upd, ↓reduceIte, a01]
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  have g7 : ∀ r, reg m7 r = (runBlock ipEpiBlock (Mx, reg m1)).2 r := regs7
  have ad : ∀ a b : Word, G + a + b = G + (a + b) := fun a b => BitVec.add_assoc _ _ _
  refine ⟨m7, .cons e1 (c6.trans (.single e7)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc7, F]; simp +decide only [upd, ↓reduceIte]
    rw [add_lit_zero, ad]; rfl
  · rw [mem7]; simp only [runBlock, ipEpiBlock, BInstr.run]
  · rw [g7, F]; simp +decide only [upd, ↓reduceIte]; rw [sp1]
  · intro p hp
    simp only [ipSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (rw [g7, F]; simp +decide only [upd, ↓reduceIte]; rw [ad]; rfl)
  · intro r h1 h2 h3 hs
    have n : ∀ q, q ∈ ipSlots.map Prod.fst → r ≠ q := fun q hq => by
      simp only [List.mem_map] at hq; obtain ⟨p, hp, rfl⟩ := hq; exact hs p hp
    rw [g7, F]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp only [upd, h0, ↓reduceIte, n s7 (by decide), n s8 (by decide), n s9 (by decide),
        n s10 (by decide), n s11 (by decide), h3, n ra (by decide), n s0 (by decide), n s1 (by decide),
        n s2 (by decide), n s3 (by decide), n s4 (by decide), n s5 (by decide), n s6 (by decide)]
      exact r1 r h1

end C3.RV32.Cur
