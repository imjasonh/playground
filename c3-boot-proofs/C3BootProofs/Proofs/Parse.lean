import C3BootProofs.Proofs.Part
import C3BootProofs.Proofs.Reserved
import C3BootProofs.Proofs.Block
import C3BootProofs.Image.BootloaderV0

/-!
# `c3_verify::manifest::parse`, as compiled

`parse` builds a `Reader` over the manifest on its stack and calls
`Reader::magic`, `Reader::version_1`, `Reader::reserved`, and
`manifest::part` four times, then checks the layout. LLVM specialized it to
its only caller, which passes the 40-byte manifest, so the compiled function
reads the bytes at `a1` and sets the reader's length to 40 without reading
`a2`. It returns `Result<Manifest, Error>` through `a0`: a tag byte (0 for
`Ok`, 1 for `Err`), the error byte at offset 1, and the four parts' offsets
and lengths from offset 4.

`parseErr` is what the compiled checks decide, in the code's own word
arithmetic, and `parseMem` is the memory they leave. `manifestParse_correct`
proves the function computes them, each call through the callee's theorem.
-/

namespace C3.RV32

open C3.ImageV0

/-- The word at byte `i` of the manifest at `bp`. -/
abbrev mw (M : Word → BitVec 8) (bp : Word) (i : Nat) : Word := memLoad32 M (bp + BitVec.ofNat 32 i)

/-- A part length outside `[lo, hi]`, as `part` tests it. -/
abbrev partOut (lo hi len : Word) : Bool := len.ult lo || hi.ult len

/-- The error the compiled `parse` returns for the 40 bytes at `bp`, or
`none` when it accepts them. -/
def parseErr (M : Word → BitVec 8) (bp : Word) : Option (BitVec 8) :=
  if !(mw M bp 0 == 0x4C533343) then some 2
  else if !(((M (bp + 5)).zeroExtend 32 <<< 24 ||| (M (bp + 4)).zeroExtend 32 <<< 16 : Word) >>> 16 == 1)
    then some 3
  else if !(allZero M (bp + 6) 2) then some 4
  else if partOut 37 0x1D0000 (mw M bp 12) then some 5
  else if partOut 49 0x4000 (mw M bp 20) then some 5
  else if partOut 8 0x800 (mw M bp 28) then some 5
  else if partOut 443 0x1000 (mw M bp 36) then some 5
  else if !(mw M bp 8 == 0x10000) then some 7
  else if (0xFFFEFFFF : Word).ult (mw M bp 12) then some 6
  else if (mw M bp 20 + mw M bp 16).ult (mw M bp 20) then some 6
  else if (mw M bp 28 + mw M bp 24).ult (mw M bp 28) then some 6
  else if (mw M bp 36 + mw M bp 32).ult (mw M bp 36) then some 6
  else if (mw M bp 16).ult (0x10000 + mw M bp 12) then some 7
  else if (mw M bp 24).ult (mw M bp 20 + mw M bp 16) then some 7
  else if (mw M bp 32).ult (mw M bp 28 + mw M bp 24) then some 7
  else if (0x1E0000 : Word).ult (mw M bp 36 + mw M bp 32) then some 7
  else none

/-- Memory after `parse` returns, outside the stack it uses. -/
def parseMem (M : Word → BitVec 8) (out bp : Word) : Word → BitVec 8 :=
  match parseErr M bp with
  | some e => memStore8 (memStore8 M (out + 1) e) out 1
  | none =>
    memStore8 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32
      (memStore32 M (out + 4) 0x10000) (out + 8) (mw M bp 12)) (out + 0x0C) (mw M bp 16))
      (out + 0x10) (mw M bp 20)) (out + 0x14) (mw M bp 24)) (out + 0x18) (mw M bp 28))
      (out + 0x1C) (mw M bp 32)) (out + 0x20) (mw M bp 36)) out 0

/-- An `auipc ra, imm; jalr ra, o(ra)` call at offset `off` of the code at
`base`, to `cb`. -/
theorem St.callRa {M : Word → BitVec 8} {base cb : Word} {code : List Nat} {m : Machine} {off : Nat}
    {f : Fin 32 → Word} (s : St M base m off f) (hc : CodeIn M base code) {imm o : Word}
    (h1 : fetchRel code off = some (.auipc ra imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = cb) (hbe : cb.toNat % 2 = 0) :
    ∃ m1, Steps m m1 ∧ m1.pc = cb ∧ m1.mem = M ∧
      ∀ r, reg m1 r = upd f ra (base + BitVec.ofNat 32 (off + 8)) r := by
  obtain ⟨m1, e1, t1⟩ := s.auipc hc h1 (off' := off + 4) (ofNat_add_ofNat off 4)
  obtain ⟨m2, e2, pc2, mem2, regs2⟩ := t1.call hc h2
  have hL : base + BitVec.ofNat 32 (off + 4) + 4 = base + BitVec.ofNat 32 (off + 8) := by
    rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
  refine ⟨m2, .cons e1 (.single e2), ?_, mem2, fun r => ?_⟩
  · rw [pc2, show upd f ra (base + BitVec.ofNat 32 off + imm) ra = base + BitVec.ofNat 32 off + imm from
      by simp +decide [upd], hb]; exact even_clear _ hbe
  · rw [regs2, hL]
    by_cases hr : r.val = 0
    · simp [upd, hr]
    · by_cases h : r = ra
      · subst h; simp [upd]
      · simp [upd, hr, h]

/-- `parse`'s code window: from `Reader::magic`, the lowest function it
reaches, to the end of `part`'s save helper, the highest. -/
abbrev parseWindow (P : Word) : Word := P + 0xFFFFC3E0

abbrev parseWindowLen : Nat := 0x16944

/-- The functions `parse` runs, where the image puts them relative to it. -/
structure PCode (M : Word → BitVec 8) (P : Word) : Prop where
  parse : CodeIn M P manifestParseCode
  save : CodeIn M (P + 0x12B98) parseSaveCode
  restore : CodeIn M (P + 0x12B8A) parseRestoreCode
  magic : CodeIn M (P + 0xFFFFC3E0) readerMagicCode
  load : CodeIn M (P + 0x12BE4) magicLoadCode
  version : CodeIn M (P + 0xFFFFC422) readerVersion1Code
  reserved : CodeIn M (P + 0xFFFFC486) readerReservedCode
  bytes : CodeIn M (P + 0xFFFFC522) readerBytesCode
  u16 : CodeIn M (P + 0xFFFFC548) readerU16Code
  array4 : CodeIn M (P + 0xFFFFC58C) readerArray4Code
  u32 : CodeIn M (P + 0xFFFFCAAE) readerU32Code
  part : CodeIn M (P + 0x162) manifestPartCode
  psave : CodeIn M (P + 0x12D18) partSaveCode
  prestore : CodeIn M (P + 0x12B56) partRestoreCode

theorem win_addr (P : Word) (d c : Nat) (h : P + BitVec.ofNat 32 d = parseWindow P + BitVec.ofNat 32 c)
    (i : Nat) : P + BitVec.ofNat 32 d + BitVec.ofNat 32 i = parseWindow P + BitVec.ofNat 32 (c + i) := by
  rw [h, add_ofNat_assoc]

theorem CodeIn.of_window {M M' : Word → BitVec 8} {P b : Word} {code : List Nat} (c : Nat)
    (hb : b = parseWindow P + BitVec.ofNat 32 c) (hl : c + code.length ≤ parseWindowLen)
    (hc : CodeIn M b code)
    (h : ∀ k, k < parseWindowLen → M' (parseWindow P + BitVec.ofNat 32 k) = M (parseWindow P + BitVec.ofNat 32 k)) :
    CodeIn M' b code := fun i hi => by
  have e : b + BitVec.ofNat 32 i = parseWindow P + BitVec.ofNat 32 (c + i) := by rw [hb, add_ofNat_assoc]
  rw [e, h _ (by omega), ← e]; exact hc i hi

set_option maxRecDepth 8000 in
/-- `PCode` holds in any memory that agrees on the code window. -/
theorem PCode.of_agree {M M' : Word → BitVec 8} {P : Word} (hc : PCode M P)
    (h : ∀ k, k < parseWindowLen → M' (parseWindow P + BitVec.ofNat 32 k) = M (parseWindow P + BitVec.ofNat 32 k)) :
    PCode M' P where
  parse := hc.parse.of_window 0x3C20 (by
    show P = P + 0xFFFFC3E0 + BitVec.ofNat 32 0x3C20
    rw [BitVec.add_assoc, show (0xFFFFC3E0 : Word) + BitVec.ofNat 32 0x3C20 = 0 from rfl]
    exact (BitVec.add_zero P).symm) (by decide) h
  save := hc.save.of_window 0x167B8 (by rw [BitVec.add_assoc]; rfl) (by decide) h
  restore := hc.restore.of_window 0x167AA (by rw [BitVec.add_assoc]; rfl) (by decide) h
  magic := hc.magic.of_window 0 (by rw [BitVec.add_assoc]; rfl) (by decide) h
  load := hc.load.of_window 0x16804 (by rw [BitVec.add_assoc]; rfl) (by decide) h
  version := hc.version.of_window 0x42 (by rw [BitVec.add_assoc]; rfl) (by decide) h
  reserved := hc.reserved.of_window 0xA6 (by rw [BitVec.add_assoc]; rfl) (by decide) h
  bytes := hc.bytes.of_window 0x142 (by rw [BitVec.add_assoc]; rfl) (by decide) h
  u16 := hc.u16.of_window 0x168 (by rw [BitVec.add_assoc]; rfl) (by decide) h
  array4 := hc.array4.of_window 0x1AC (by rw [BitVec.add_assoc]; rfl) (by decide) h
  u32 := hc.u32.of_window 0x6CE (by rw [BitVec.add_assoc]; rfl) (by decide) h
  part := hc.part.of_window 0x3D82 (by rw [BitVec.add_assoc]; rfl) (by decide) h
  psave := hc.psave.of_window 0x16938 (by rw [BitVec.add_assoc]; rfl) (by decide) h
  prestore := hc.prestore.of_window 0x16776 (by rw [BitVec.add_assoc]; rfl) (by decide) h

/-- `parse`'s layout: the 144 bytes of stack at `R` (its 64-byte frame at
`G = R + 80` and up to 80 bytes for its callees), the code window, the
manifest at `bp`, and the result at `out`, apart from each other. -/
structure PEnv (P R G bp out : Word) : Prop where
  hP : P.toNat % 2 = 0
  hRG : G = R + BitVec.ofNat 32 80
  hG : G.toNat % 4 = 0
  hout : out.toNat % 4 = 0
  hbp : bp ≠ 0 ∧ bp.toNat + 40 ≤ 2 ^ 32
  hSW : Sep R 144 (parseWindow P) parseWindowLen
  hOW : Sep out 36 (parseWindow P) parseWindowLen
  hOS : Sep out 36 R 144
  hBS : Sep bp 40 R 144

namespace PEnv

variable {P R G bp out : Word}

theorem g_ofs (env : PEnv P R G bp out) (c : Nat) : G + BitVec.ofNat 32 c = R + BitVec.ofNat 32 (80 + c) := by
  rw [env.hRG, add_ofNat_assoc]

/-- A range inside the stack region, apart from the code window. -/
theorem stack_code (env : PEnv P R G bp out) (c n : Nat) (hn : c + n ≤ 144) (d l : Nat) (hl : d + l ≤ parseWindowLen) :
    Sep (R + BitVec.ofNat 32 c) n (parseWindow P + BitVec.ofNat 32 d) l :=
  (env.hSW.sub (c := c) (l := n) hn).subR (c := d) (l := l) hl

theorem stack_buf (env : PEnv P R G bp out) (c n : Nat) (hn : c + n ≤ 144) (d l : Nat) (hl : d + l ≤ 40) :
    Sep (bp + BitVec.ofNat 32 d) l (R + BitVec.ofNat 32 c) n :=
  (env.hBS.sub (c := d) (l := l) hl).subR (c := c) (l := n) hn

theorem stack_stack (_env : PEnv P R G bp out) (c n d l : Nat) (hn : c + n ≤ 144) (hl : d + l ≤ 144) (h : c + n ≤ d ∨ d + l ≤ c) :
    Sep (R + BitVec.ofNat 32 c) n (R + BitVec.ofNat 32 d) l :=
  sep_offsets R h (by omega) (by omega)

end PEnv

theorem g8_eq {G : Word} : G + 8 + 4 = G + 12 := by rw [BitVec.add_assoc]; rfl

theorem PEnv.r_eqs {P R G bp out : Word} (env : PEnv P R G bp out) :
    G + 0xFFFFFFD0 = R + BitVec.ofNat 32 32 ∧ G + 0xFFFFFFE0 = R + BitVec.ofNat 32 48 ∧
    G + 0xFFFFFFF0 = R + BitVec.ofNat 32 64 ∧ G + 0xFFFFFFB0 = R ∧ G + 8 = R + BitVec.ofNat 32 88 ∧
    G + 8 + 8 = R + BitVec.ofNat 32 96 ∧ G + 0x14 = R + BitVec.ofNat 32 100 := by
  rw [env.hRG]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [BitVec.add_assoc] <;> try rfl
  exact BitVec.add_zero R

/-- A call from `parse` to `Reader::magic` on the reader at `G + 8`. -/
theorem parse_magic {P R G bp out : Word} (env : PEnv P R G bp out) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {k imm o : Word} (s : St Mx P m off f)
    (code : PCode Mx P)
    (h1 : fetchRel manifestParseCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel manifestParseCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xFFFFC3E0)
    (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 8) (ha1 : f a1 = k)
    (hrp : memLoad32 Mx (G + 8) = bp) (hrl : memLoad32 Mx (G + 8 + 4) = 40) :
    ∃ m', Steps m m' ∧ St m'.mem P m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      reg m' a0 = magicResult Mx (G + 8) k ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep (G + 0xFFFFFFD0) 48 x 1 → m'.mem x = magicMem Mx (G + 8) x := by
  obtain ⟨e32, -, -, -, e88, e96, -⟩ := env.r_eqs
  have hev : (P + 0xFFFFC3E0).toNat % 2 = 0 := even_at P env.hP 0xFFFFC3E0 (by decide)
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.parse h1 h2 hb hev
  have r1 : ∀ r, r ≠ ra → reg m1 r = f r := fun r h => by
    rw [regs1]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [upd]; exact s.zero.symm
    · simp [upd, hr, h]
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  have W0 : P + 0xFFFFC3E0 = parseWindow P + BitVec.ofNat 32 0 := (add_ofNat_zero _).symm
  have WA : P + 0xFFFFC3E0 + 0x1AC = parseWindow P + BitVec.ofNat 32 0x1AC := rfl
  have WB : P + 0xFFFFC3E0 + 0x1AC + 0xFFFFFF96 = parseWindow P + BitVec.ofNat 32 0x142 := by
    rw [BitVec.add_assoc (P + 0xFFFFC3E0) 0x1AC 0xFFFFFF96]; rfl
  have WL : P + 0xFFFFC3E0 + 0x16804 = parseWindow P + BitVec.ofNat 32 0x16804 := rfl
  obtain ⟨m2, c2, pc2, sp2, a02, fr2, mem2⟩ := readerMagic_correct m1 (P + 0xFFFFC3E0)
    (P + BitVec.ofNat 32 (off + 8)) (G + 8) k
    (fun i hi => by rw [mem1]; exact code.magic i hi)
    (fun i hi => by rw [mem1, show P + 0xFFFFC3E0 + 0x1AC = P + 0xFFFFC58C by rw [BitVec.add_assoc]; rfl]
                    exact code.array4 i hi)
    (fun i hi => by
      rw [mem1, show P + 0xFFFFC3E0 + 0x1AC + 0xFFFFFF96 = P + 0xFFFFC522 by simp only [BitVec.add_assoc]; rfl]
      exact code.bytes i hi)
    (fun i hi => by rw [mem1, show P + 0xFFFFC3E0 + 0x16804 = P + 0x12BE4 by rw [BitVec.add_assoc]; rfl]
                    exact code.load i hi)
    hev pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) (by rw [sp1]; exact env.hG)
    (aligned_add env.hG (k := 8) (by decide))
    (by rw [mem1, hrp, hrl]; exact ⟨env.hbp.1, by have := env.hbp.2; exact this⟩)
    (by rw [sp1, e32, W0]; exact env.stack_code 32 48 (by omega) 0 _ (by decide))
    (by rw [sp1, e32, WA]; exact env.stack_code 32 48 (by omega) 0x1AC _ (by decide))
    (by rw [sp1, e32, WB]; exact env.stack_code 32 48 (by omega) 0x142 _ (by decide))
    (by rw [sp1, e32, WL]; exact env.stack_code 32 48 (by omega) 0x16804 _ (by decide))
    (by rw [e96, W0]; exact env.stack_code 96 4 (by omega) 0 _ (by decide))
    (by rw [e96, WA]; exact env.stack_code 96 4 (by omega) 0x1AC _ (by decide))
    (by rw [e96, WB]; exact env.stack_code 96 4 (by omega) 0x142 _ (by decide))
    (by rw [e96, WL]; exact env.stack_code 96 4 (by omega) 0x16804 _ (by decide))
    (by rw [sp1, e32, e88]; exact env.stack_stack 88 12 32 48 (by omega) (by omega) (by omega))
    (by rw [mem1, hrp, hrl, sp1, e32]
        have := env.stack_buf 32 48 (by omega) 0 40 (by omega); rwa [add_ofNat_zero] at this)
    (by rw [mem1, hrp, hrl, e96]
        have := env.stack_buf 96 4 (by omega) 0 40 (by omega); rwa [add_ofNat_zero] at this)
  rw [mem1] at a02 mem2
  rw [sp1] at sp2 mem2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, a02, fun r h0 h1' h2' h3 h4 h5 h6 h7 => ?_, mem2⟩
  rw [fr2 r h0 h1' h2' h3 h4 h5 h6, r1 r h7]

theorem wq (P x : Word) (c : Nat) (h : x = 0xFFFFC3E0 + BitVec.ofNat 32 c) :
    P + x = parseWindow P + BitVec.ofNat 32 c := by rw [h, ← BitVec.add_assoc]

theorem PEnv.reg1 {f : Fin 32 → Word} {m1 : Machine} {L : Word}
    (regs : ∀ r, reg m1 r = upd f ra L r) (hz : f 0 = 0) : ∀ r, r ≠ ra → reg m1 r = f r := fun r h => by
  rw [regs]
  by_cases hr : r.val = 0
  · have : r = 0 := Fin.ext hr
    subst this; simp [upd]; exact hz.symm
  · simp [upd, hr, h]

/-- A call from `parse` to `Reader::version_1` on the reader at `G + 8`. -/
theorem parse_version {P R G bp out : Word} (env : PEnv P R G bp out) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {imm o : Word} (s : St Mx P m off f)
    (code : PCode Mx P)
    (h1 : fetchRel manifestParseCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel manifestParseCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xFFFFC422)
    (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 8)
    (hrp : memLoad32 Mx (G + 8) = bp) (hrl : memLoad32 Mx (G + 8 + 4) = 40) :
    ∃ m', Steps m m' ∧ St m'.mem P m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      reg m' a0 = version1Result Mx (G + 8) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep (G + 0xFFFFFFE0) 32 x 1 → m'.mem x = u16Mem Mx (G + 8) x := by
  obtain ⟨-, e48, -, -, e88, e96, -⟩ := env.r_eqs
  have hev : (P + 0xFFFFC422).toNat % 2 = 0 := even_at P env.hP 0xFFFFC422 (by decide)
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.parse h1 h2 hb hev
  have r1 := PEnv.reg1 regs1 s.zero
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  have WV : P + 0xFFFFC422 = parseWindow P + BitVec.ofNat 32 0x42 := wq P _ 0x42 (by decide)
  have WU : P + 0xFFFFC422 + 0x126 = parseWindow P + BitVec.ofNat 32 0x168 := by
    rw [BitVec.add_assoc]; exact wq P _ 0x168 (by decide)
  have WB : P + 0xFFFFC422 + 0x126 + 0xFFFFFFDA = parseWindow P + BitVec.ofNat 32 0x142 := by
    rw [BitVec.add_assoc (P + 0xFFFFC422) 0x126 0xFFFFFFDA, BitVec.add_assoc P]
    exact wq P _ 0x142 (by decide)
  obtain ⟨m2, c2, pc2, sp2, a02, fr2, mem2⟩ := readerVersion1_correct m1 (P + 0xFFFFC422)
    (P + BitVec.ofNat 32 (off + 8)) (G + 8)
    (fun i hi => by rw [mem1]; exact code.version i hi)
    (fun i hi => by rw [mem1, show P + 0xFFFFC422 + 0x126 = P + 0xFFFFC548 by
                      rw [BitVec.add_assoc]; rfl]; exact code.u16 i hi)
    (fun i hi => by
      rw [mem1, show P + 0xFFFFC422 + 0x126 + 0xFFFFFFDA = P + 0xFFFFC522 by simp only [BitVec.add_assoc]; rfl]
      exact code.bytes i hi)
    hev pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [regs1]; simp +decide [upd]) (even_clear _ hl)
    (by rw [sp1]; exact env.hG) (aligned_add env.hG (k := 8) (by decide))
    (by rw [mem1, hrp, hrl]; exact ⟨env.hbp.1, env.hbp.2⟩)
    (by rw [sp1, e48, WV]; exact env.stack_code 48 32 (by omega) 0x42 _ (by decide))
    (by rw [sp1, e48, WU]; exact env.stack_code 48 32 (by omega) 0x168 _ (by decide))
    (by rw [sp1, e48, WB]; exact env.stack_code 48 32 (by omega) 0x142 _ (by decide))
    (by rw [e96, WV]; exact env.stack_code 96 4 (by omega) 0x42 _ (by decide))
    (by rw [e96, WU]; exact env.stack_code 96 4 (by omega) 0x168 _ (by decide))
    (by rw [e96, WB]; exact env.stack_code 96 4 (by omega) 0x142 _ (by decide))
    (by rw [sp1, e48, e88]; exact env.stack_stack 88 12 48 32 (by omega) (by omega) (by omega))
    (by rw [mem1, hrp, hrl, sp1, e48]
        have := env.stack_buf 48 32 (by omega) 0 40 (by omega); rwa [add_ofNat_zero] at this)
    (by rw [mem1, hrp, hrl, e96]
        have := env.stack_buf 96 4 (by omega) 0 40 (by omega); rwa [add_ofNat_zero] at this)
  rw [mem1] at a02 mem2
  rw [sp1] at sp2 mem2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, a02, fun r h0 h1' h2' h3 h4 h5 h7 => ?_, mem2⟩
  rw [fr2 r h0 h1' h2' h3 h4 h5, r1 r h7]

/-- A call from `parse` to `Reader::reserved(2)` on the reader at `G + 8`. -/
theorem parse_reserved {P R G bp out : Word} (env : PEnv P R G bp out) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {imm o : Word} (s : St Mx P m off f)
    (code : PCode Mx P)
    (h1 : fetchRel manifestParseCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel manifestParseCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xFFFFC486)
    (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 8) (ha1 : f a1 = 2)
    (hrp : memLoad32 Mx (G + 8) = bp) (hrl : memLoad32 Mx (G + 8 + 4) = 40) :
    ∃ m', Steps m m' ∧ St m'.mem P m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      reg m' a0 = reservedResult Mx (G + 8) 2 ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep (G + 0xFFFFFFF0) 16 x 1 → m'.mem x = reservedMem Mx (G + 8) 2 x := by
  obtain ⟨-, -, e64, -, e88, e96, -⟩ := env.r_eqs
  have hev : (P + 0xFFFFC486).toNat % 2 = 0 := even_at P env.hP 0xFFFFC486 (by decide)
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.parse h1 h2 hb hev
  have r1 := PEnv.reg1 regs1 s.zero
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  have WR : P + 0xFFFFC486 = parseWindow P + BitVec.ofNat 32 0xA6 := wq P _ 0xA6 (by decide)
  have WB : P + 0xFFFFC486 + 0x9C = parseWindow P + BitVec.ofNat 32 0x142 := by
    rw [BitVec.add_assoc]; exact wq P _ 0x142 (by decide)
  obtain ⟨m2, c2, pc2, sp2, a02, fr2, mem2⟩ := readerReserved_correct m1 (P + 0xFFFFC486)
    (P + BitVec.ofNat 32 (off + 8)) (G + 8) 2
    (fun i hi => by rw [mem1]; exact code.reserved i hi)
    (fun i hi => by rw [mem1, show P + 0xFFFFC486 + 0x9C = P + 0xFFFFC522 by
                      rw [BitVec.add_assoc]; rfl]; exact code.bytes i hi)
    hev pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by decide)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl)
    (by rw [sp1]; exact env.hG) (aligned_add env.hG (k := 8) (by decide))
    (by rw [mem1, hrp, hrl]; exact ⟨env.hbp.1, env.hbp.2⟩)
    (by rw [sp1, e64, WR]; exact env.stack_code 64 16 (by omega) 0xA6 _ (by decide))
    (by rw [sp1, e64, WB]; exact env.stack_code 64 16 (by omega) 0x142 _ (by decide))
    (by rw [e96, WR]; exact env.stack_code 96 4 (by omega) 0xA6 _ (by decide))
    (by rw [e96, WB]; exact env.stack_code 96 4 (by omega) 0x142 _ (by decide))
    (by rw [sp1, e64, e88]; exact env.stack_stack 88 12 64 16 (by omega) (by omega) (by omega))
    (by rw [mem1, hrp, hrl, sp1, e64]
        have := env.stack_buf 64 16 (by omega) 0 40 (by omega); rwa [add_ofNat_zero] at this)
    (by rw [mem1, hrp, hrl, e96]
        have := env.stack_buf 96 4 (by omega) 0 40 (by omega); rwa [add_ofNat_zero] at this)
  rw [mem1] at a02 mem2
  rw [sp1] at sp2 mem2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, a02, fun r h0 h1' h2' h3 h4 h5 h7 => ?_, mem2⟩
  rw [fr2 r h0 h1' h2' h3 h4 h5, r1 r h7]

/-- A call from `parse` to `manifest::part` on the reader at `G + 8`, with
the result at `G + 0x14`. -/
theorem parse_part {P R G bp out : Word} (env : PEnv P R G bp out) {Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {imm o lo hi : Word} (s : St Mx P m off f)
    (code : PCode Mx P)
    (h1 : fetchRel manifestParseCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel manifestParseCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x162)
    (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 0x14) (ha1 : f a1 = G + 8) (ha2 : f a2 = lo) (ha3 : f a3 = hi)
    (hrp : memLoad32 Mx (G + 8) = bp) (hrl : memLoad32 Mx (G + 8 + 4) = 40) :
    ∃ m', Steps m m' ∧ St m'.mem P m' (off + 8) (reg m') ∧ reg m' sp = G ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → r ≠ ra → reg m' r = f r) ∧
      ∀ x, Sep R 80 x 1 → m'.mem x = partMem Mx (G + 0x14) (G + 8) lo hi x := by
  obtain ⟨-, -, -, eR, e88, e96, e100⟩ := env.r_eqs
  have hev : (P + 0x162).toNat % 2 = 0 := even_at P env.hP 0x162 (by decide)
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa code.parse h1 h2 hb hev
  have r1 := PEnv.reg1 regs1 s.zero
  have sp1 : reg m1 sp = G := by rw [r1 sp (by decide), hsp]
  have WPW : partWindow (P + 0x162) = parseWindow P + BitVec.ofNat 32 0x142 := by
    show P + 0x162 + 0xFFFFC3C0 = _
    rw [BitVec.add_assoc]; exact wq P _ 0x142 (by decide)
  have R0 : R = R + BitVec.ofNat 32 0 := (add_ofNat_zero R).symm
  obtain ⟨m2, c2, pc2, sp2, fr2, mem2⟩ := manifestPart_correct m1 (P + 0x162)
    (P + BitVec.ofNat 32 (off + 8)) (G + 0x14) (G + 8) lo hi
    (fun i hi' => by rw [mem1]; exact code.part i hi')
    (fun i hi' => by rw [mem1, show P + 0x162 + 0x12BB6 = P + 0x12D18 by rw [BitVec.add_assoc]; rfl]
                     exact code.psave i hi')
    (fun i hi' => by rw [mem1, show P + 0x162 + 0x129F4 = P + 0x12B56 by rw [BitVec.add_assoc]; rfl]
                     exact code.prestore i hi')
    (fun i hi' => by rw [mem1, show P + 0x162 + 0xFFFFC94C = P + 0xFFFFCAAE by rw [BitVec.add_assoc]; rfl]
                     exact code.u32 i hi')
    (fun i hi' => by
      rw [mem1, show P + 0x162 + 0xFFFFC94C + 0xFFFFFADE = P + 0xFFFFC58C by simp only [BitVec.add_assoc]; rfl]
      exact code.array4 i hi')
    (fun i hi' => by
      rw [mem1, show P + 0x162 + 0xFFFFC94C + 0xFFFFFADE + 0xFFFFFF96 = P + 0xFFFFC522 by
        simp only [BitVec.add_assoc]; rfl]
      exact code.bytes i hi')
    hev pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [r1 a2 (by decide), ha2]) (by rw [r1 a3 (by decide), ha3])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) (by rw [sp1]; exact env.hG)
    (aligned_add env.hG (k := 0x14) (by decide)) (aligned_add env.hG (k := 8) (by decide))
    (by rw [mem1, hrp, hrl]; exact ⟨env.hbp.1, env.hbp.2⟩)
    (by rw [sp1, eR, WPW, R0]; exact env.stack_code 0 80 (by omega) 0x142 _ (by decide))
    (by rw [e100, WPW]; exact env.stack_code 100 12 (by omega) 0x142 _ (by decide))
    (by rw [e96, WPW]; exact env.stack_code 96 4 (by omega) 0x142 _ (by decide))
    (by rw [sp1, eR, e88]
        have := env.stack_stack 88 12 0 80 (by omega) (by omega) (by omega); rwa [add_ofNat_zero] at this)
    (by rw [sp1, eR, e100]
        have := env.stack_stack 100 12 0 80 (by omega) (by omega) (by omega); rwa [add_ofNat_zero] at this)
    (by rw [mem1, hrp, hrl, sp1, eR]
        have := env.stack_buf 0 80 (by omega) 0 40 (by omega); rwa [add_ofNat_zero, add_ofNat_zero] at this)
    (by rw [mem1, hrp, hrl, e96]
        have := env.stack_buf 96 4 (by omega) 0 40 (by omega); rwa [add_ofNat_zero] at this)
  rw [mem1] at mem2
  rw [sp1, eR] at mem2
  rw [sp1] at sp2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun r h0 h1' h2' h3 h4 h5 h6 h7 => ?_, mem2⟩
  rw [fr2 r h0 h1' h2' h3 h4 h5 h6, r1 r h7]

section

set_option maxRecDepth 20000

theorem pa_0 : fetchRel manifestParseCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem pa_2 : fetchRel manifestParseCode 0x2 = some (.auipc t0 0x13000, 4) := by decide
theorem pa_6 : fetchRel manifestParseCode 0x6 = some (.jalr t0 t0 0xFFFFFB96, 4) := by decide
theorem pa_a : fetchRel manifestParseCode 0xA = some (.store .sw sp s5 0x24, 2) := by decide
theorem pa_c : fetchRel manifestParseCode 0xC = some (.store .sw sp s6 0x20, 2) := by decide
theorem pa_e : fetchRel manifestParseCode 0xE = some (.alu .add s0 x0 a0, 2) := by decide
theorem pa_10 : fetchRel manifestParseCode 0x10 = some (.aluImm .add a0 x0 0x28, 4) := by decide
theorem pa_14 : fetchRel manifestParseCode 0x14 = some (.store .sw sp a1 0x8, 2) := by decide
theorem pa_16 : fetchRel manifestParseCode 0x16 = some (.store .sw sp a0 0xC, 2) := by decide
theorem pa_18 : fetchRel manifestParseCode 0x18 = some (.store .sw sp x0 0x10, 2) := by decide
theorem pa_1a : fetchRel manifestParseCode 0x1A = some (.lui a1 0x4C533000, 4) := by decide
theorem pa_1e : fetchRel manifestParseCode 0x1E = some (.aluImm .add a1 a1 0x343, 4) := by decide
theorem pa_22 : fetchRel manifestParseCode 0x22 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem pa_24 : fetchRel manifestParseCode 0x24 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem pa_28 : fetchRel manifestParseCode 0x28 = some (.jalr ra ra 0x3BC, 4) := by decide
theorem pa_2c : fetchRel manifestParseCode 0x2C = some (.aluImm .and a1 a0 0xFF, 4) := by decide
theorem pa_30 : fetchRel manifestParseCode 0x30 = some (.aluImm .add a1 a1 0xFFFFFF01, 4) := by decide
theorem pa_34 : fetchRel manifestParseCode 0x34 = some (.branch .bne a1 x0 0x9E, 2) := by decide
theorem pa_36 : fetchRel manifestParseCode 0x36 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem pa_38 : fetchRel manifestParseCode 0x38 = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem pa_3c : fetchRel manifestParseCode 0x3C = some (.jalr ra ra 0x3EA, 4) := by decide
theorem pa_40 : fetchRel manifestParseCode 0x40 = some (.aluImm .and a1 a0 0xFF, 4) := by decide
theorem pa_44 : fetchRel manifestParseCode 0x44 = some (.aluImm .add a1 a1 0xFFFFFF01, 4) := by decide
theorem pa_48 : fetchRel manifestParseCode 0x48 = some (.branch .bne a1 x0 0x8A, 2) := by decide
theorem pa_4a : fetchRel manifestParseCode 0x4A = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem pa_4c : fetchRel manifestParseCode 0x4C = some (.aluImm .add a1 x0 0x2, 2) := by decide
theorem pa_4e : fetchRel manifestParseCode 0x4E = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem pa_52 : fetchRel manifestParseCode 0x52 = some (.jalr ra ra 0x438, 4) := by decide
theorem pa_56 : fetchRel manifestParseCode 0x56 = some (.aluImm .and a1 a0 0xFF, 4) := by decide
theorem pa_5a : fetchRel manifestParseCode 0x5A = some (.aluImm .add a1 a1 0xFFFFFF01, 4) := by decide
theorem pa_5e : fetchRel manifestParseCode 0x5E = some (.branch .bne a1 x0 0x74, 2) := by decide
theorem pa_60 : fetchRel manifestParseCode 0x60 = some (.aluImm .add a0 sp 0x14, 2) := by decide
theorem pa_62 : fetchRel manifestParseCode 0x62 = some (.aluImm .add a1 sp 0x8, 2) := by decide
theorem pa_64 : fetchRel manifestParseCode 0x64 = some (.aluImm .add a2 x0 0x25, 4) := by decide
theorem pa_68 : fetchRel manifestParseCode 0x68 = some (.lui a3 0x1D0000, 4) := by decide
theorem pa_6c : fetchRel manifestParseCode 0x6C = some (.auipc ra 0x0, 4) := by decide
theorem pa_70 : fetchRel manifestParseCode 0x70 = some (.jalr ra ra 0xF6, 4) := by decide
theorem pa_74 : fetchRel manifestParseCode 0x74 = some (.load .lbu a0 sp 0x14, 4) := by decide
theorem pa_78 : fetchRel manifestParseCode 0x78 = some (.branch .bne a0 x0 0x56, 2) := by decide
theorem pa_7a : fetchRel manifestParseCode 0x7A = some (.load .lw s1 sp 0x18, 2) := by decide
theorem pa_7c : fetchRel manifestParseCode 0x7C = some (.load .lw s6 sp 0x1C, 2) := by decide
theorem pa_7e : fetchRel manifestParseCode 0x7E = some (.aluImm .add a0 sp 0x14, 2) := by decide
theorem pa_80 : fetchRel manifestParseCode 0x80 = some (.aluImm .add a1 sp 0x8, 2) := by decide
theorem pa_82 : fetchRel manifestParseCode 0x82 = some (.aluImm .add a2 x0 0x31, 4) := by decide
theorem pa_86 : fetchRel manifestParseCode 0x86 = some (.lui a3 0x4000, 2) := by decide
theorem pa_88 : fetchRel manifestParseCode 0x88 = some (.auipc ra 0x0, 4) := by decide
theorem pa_8c : fetchRel manifestParseCode 0x8C = some (.jalr ra ra 0xDA, 4) := by decide
theorem pa_90 : fetchRel manifestParseCode 0x90 = some (.load .lbu a0 sp 0x14, 4) := by decide
theorem pa_94 : fetchRel manifestParseCode 0x94 = some (.branch .bne a0 x0 0x3A, 2) := by decide
theorem pa_96 : fetchRel manifestParseCode 0x96 = some (.load .lw s2 sp 0x18, 2) := by decide
theorem pa_98 : fetchRel manifestParseCode 0x98 = some (.load .lw s3 sp 0x1C, 2) := by decide
theorem pa_9a : fetchRel manifestParseCode 0x9A = some (.aluImm .add a3 x0 0x1, 2) := by decide
theorem pa_9c : fetchRel manifestParseCode 0x9C = some (.aluImm .sll a3 a3 0xB, 2) := by decide
theorem pa_9e : fetchRel manifestParseCode 0x9E = some (.aluImm .add a0 sp 0x14, 2) := by decide
theorem pa_a0 : fetchRel manifestParseCode 0xA0 = some (.aluImm .add a1 sp 0x8, 2) := by decide
theorem pa_a2 : fetchRel manifestParseCode 0xA2 = some (.aluImm .add a2 x0 0x8, 2) := by decide
theorem pa_a4 : fetchRel manifestParseCode 0xA4 = some (.auipc ra 0x0, 4) := by decide
theorem pa_a8 : fetchRel manifestParseCode 0xA8 = some (.jalr ra ra 0xBE, 4) := by decide
theorem pa_ac : fetchRel manifestParseCode 0xAC = some (.load .lbu a0 sp 0x14, 4) := by decide
theorem pa_b0 : fetchRel manifestParseCode 0xB0 = some (.branch .bne a0 x0 0x1E, 2) := by decide
theorem pa_b2 : fetchRel manifestParseCode 0xB2 = some (.load .lw s4 sp 0x18, 2) := by decide
theorem pa_b4 : fetchRel manifestParseCode 0xB4 = some (.load .lw s5 sp 0x1C, 2) := by decide
theorem pa_b6 : fetchRel manifestParseCode 0xB6 = some (.aluImm .add a0 sp 0x14, 2) := by decide
theorem pa_b8 : fetchRel manifestParseCode 0xB8 = some (.aluImm .add a1 sp 0x8, 2) := by decide
theorem pa_ba : fetchRel manifestParseCode 0xBA = some (.aluImm .add a2 x0 0x1BB, 4) := by decide
theorem pa_be : fetchRel manifestParseCode 0xBE = some (.lui a3 0x1000, 2) := by decide
theorem pa_c0 : fetchRel manifestParseCode 0xC0 = some (.auipc ra 0x0, 4) := by decide
theorem pa_c4 : fetchRel manifestParseCode 0xC4 = some (.jalr ra ra 0xA2, 4) := by decide
theorem pa_c8 : fetchRel manifestParseCode 0xC8 = some (.load .lbu a0 sp 0x14, 4) := by decide
theorem pa_cc : fetchRel manifestParseCode 0xCC = some (.branch .beq a0 x0 0x20, 2) := by decide
theorem pa_ce : fetchRel manifestParseCode 0xCE = some (.load .lbu a0 sp 0x15, 4) := by decide
theorem pa_d2 : fetchRel manifestParseCode 0xD2 = some (.store .sb s0 a0 0x1, 4) := by decide
theorem pa_d6 : fetchRel manifestParseCode 0xD6 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem pa_d8 : fetchRel manifestParseCode 0xD8 = some (.store .sb s0 a0 0x0, 4) := by decide
theorem pa_dc : fetchRel manifestParseCode 0xDC = some (.auipc t0 0x13000, 4) := by decide
theorem pa_e0 : fetchRel manifestParseCode 0xE0 = some (.jalr t0 t0 0xFFFFFAAE, 4) := by decide
theorem pa_e4 : fetchRel manifestParseCode 0xE4 = some (.load .lw s5 sp 0x24, 2) := by decide
theorem pa_e6 : fetchRel manifestParseCode 0xE6 = some (.load .lw s6 sp 0x20, 2) := by decide
theorem pa_e8 : fetchRel manifestParseCode 0xE8 = some (.aluImm .add sp sp 0x40, 2) := by decide
theorem pa_ea : fetchRel manifestParseCode 0xEA = some (.jalr x0 ra 0x0, 2) := by decide
theorem pa_ec : fetchRel manifestParseCode 0xEC = some (.load .lw a0 sp 0xC, 2) := by decide
theorem pa_ee : fetchRel manifestParseCode 0xEE = some (.load .lw a1 sp 0x10, 2) := by decide
theorem pa_f0 : fetchRel manifestParseCode 0xF0 = some (.branch .bne a1 a0 0x6A, 4) := by decide
theorem pa_f4 : fetchRel manifestParseCode 0xF4 = some (.lui a3 0x10000, 2) := by decide
theorem pa_f6 : fetchRel manifestParseCode 0xF6 = some (.branch .bne s1 a3 0x68, 4) := by decide
theorem pa_fa : fetchRel manifestParseCode 0xFA = some (.lui a0 0xFFFF0000, 2) := by decide
theorem pa_fc : fetchRel manifestParseCode 0xFC = some (.aluImm .add a1 a0 0xFFFFFFFF, 4) := by decide
theorem pa_100 : fetchRel manifestParseCode 0x100 = some (.aluImm .add a0 x0 0x6, 2) := by decide
theorem pa_102 : fetchRel manifestParseCode 0x102 = some (.branch .bltu a1 s6 0xFFFFFFD0, 4) := by decide
theorem pa_106 : fetchRel manifestParseCode 0x106 = some (.alu .add a4 s3 s2, 4) := by decide
theorem pa_10a : fetchRel manifestParseCode 0x10A = some (.branch .bltu a4 s3 0xFFFFFFC8, 4) := by decide
theorem pa_10e : fetchRel manifestParseCode 0x10E = some (.alu .add a5 s5 s4, 4) := by decide
theorem pa_112 : fetchRel manifestParseCode 0x112 = some (.branch .bltu a5 s5 0xFFFFFFC0, 4) := by decide
theorem pa_116 : fetchRel manifestParseCode 0x116 = some (.load .lw s1 sp 0x18, 2) := by decide
theorem pa_118 : fetchRel manifestParseCode 0x118 = some (.load .lw a2 sp 0x1C, 2) := by decide
theorem pa_11a : fetchRel manifestParseCode 0x11A = some (.alu .add a1 a2 s1, 4) := by decide
theorem pa_11e : fetchRel manifestParseCode 0x11E = some (.branch .bltu a1 a2 0xFFFFFFB4, 4) := by decide
theorem pa_122 : fetchRel manifestParseCode 0x122 = some (.alu .add a3 a3 s6, 2) := by decide
theorem pa_124 : fetchRel manifestParseCode 0x124 = some (.branch .bltu s2 a3 0x3A, 4) := by decide
theorem pa_128 : fetchRel manifestParseCode 0x128 = some (.branch .bltu s4 a4 0x36, 4) := by decide
theorem pa_12c : fetchRel manifestParseCode 0x12C = some (.branch .bltu s1 a5 0x32, 4) := by decide
theorem pa_130 : fetchRel manifestParseCode 0x130 = some (.lui a3 0x1E0000, 4) := by decide
theorem pa_134 : fetchRel manifestParseCode 0x134 = some (.aluImm .add a0 x0 0x7, 2) := by decide
theorem pa_136 : fetchRel manifestParseCode 0x136 = some (.branch .bltu a3 a1 0xFFFFFF9C, 4) := by decide
theorem pa_13a : fetchRel manifestParseCode 0x13A = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem pa_13c : fetchRel manifestParseCode 0x13C = some (.lui a1 0x10000, 2) := by decide
theorem pa_13e : fetchRel manifestParseCode 0x13E = some (.store .sw s0 a1 0x4, 2) := by decide
theorem pa_140 : fetchRel manifestParseCode 0x140 = some (.store .sw s0 s6 0x8, 4) := by decide
theorem pa_144 : fetchRel manifestParseCode 0x144 = some (.store .sw s0 s2 0xC, 4) := by decide
theorem pa_148 : fetchRel manifestParseCode 0x148 = some (.store .sw s0 s3 0x10, 4) := by decide
theorem pa_14c : fetchRel manifestParseCode 0x14C = some (.store .sw s0 s4 0x14, 4) := by decide
theorem pa_150 : fetchRel manifestParseCode 0x150 = some (.store .sw s0 s5 0x18, 4) := by decide
theorem pa_154 : fetchRel manifestParseCode 0x154 = some (.store .sw s0 s1 0x1C, 2) := by decide
theorem pa_156 : fetchRel manifestParseCode 0x156 = some (.store .sw s0 a2 0x20, 2) := by decide
theorem pa_158 : fetchRel manifestParseCode 0x158 = some (.jal x0 0xFFFFFF80, 2) := by decide
theorem pa_15a : fetchRel manifestParseCode 0x15A = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem pa_15c : fetchRel manifestParseCode 0x15C = some (.jal x0 0xFFFFFF76, 2) := by decide
theorem pa_15e : fetchRel manifestParseCode 0x15E = some (.aluImm .add a0 x0 0x7, 2) := by decide
theorem pa_160 : fetchRel manifestParseCode 0x160 = some (.jal x0 0xFFFFFF72, 2) := by decide

end

/-- What `parse`'s save helper stores, and where in the frame. -/
abbrev parseSavePs : List (Fin 32 × Word) :=
  [(ra, 0x3C), (s0, 0x38), (s1, 0x34), (s2, 0x30), (s3, 0x2C), (s4, 0x28)]

theorem parseSave_shape : SaveAt parseSaveCode 0 parseSavePs := by simp only [SaveAt]; decide

theorem parseRestore_shape : RestoreAt parseRestoreCode 0 parseSavePs := by simp only [RestoreAt]; decide

/-- `parse`'s epilogue from offset 0xD8: it stores the tag from `a0` at
`out`, restores `ra` and `s0` through `s4` with the restore helper and `s5`
and `s6` itself, frees the frame, and returns. -/
theorem parse_tail {Mx : Word → BitVec 8} {P G out : Word} {m : Machine} {f : Fin 32 → Word}
    (s : St Mx P m 0xD8 f) (hc : CodeIn Mx P manifestParseCode)
    (hr : CodeIn Mx (P + 0x12B8A) parseRestoreCode) (hP : P.toNat % 2 = 0) (hsp : f sp = G)
    (hG : G.toNat % 4 = 0) (hs0 : f s0 = out) (hOp : Sep out 1 P manifestParseCode.length)
    (hOr : Sep out 1 (P + 0x12B8A) parseRestoreCode.length) :
    ∃ m', Steps m m' ∧
      m'.pc = memLoad32 (memStore8 Mx out ((f a0).extractLsb' 0 8)) (G + 0x3C) &&& ~~~1 ∧
      m'.mem = memStore8 Mx out ((f a0).extractLsb' 0 8) ∧
      ∀ r, reg m' r = upd (upd (upd (restoreRegs (memStore8 Mx out ((f a0).extractLsb' 0 8)) G
        (upd f t0 (P + BitVec.ofNat 32 0xE4)) parseSavePs) s5
        (memLoad32 (memStore8 Mx out ((f a0).extractLsb' 0 8)) (G + 0x24))) s6
        (memLoad32 (memStore8 Mx out ((f a0).extractLsb' 0 8)) (G + 0x20))) sp (G + 0x40) r := by
  obtain ⟨m1, e1, t1⟩ := s.sb hc pa_d8 (off' := 0xDC) (by decide)
  rw [hs0, add_lit_zero] at t1
  have hc1 := hc.store8 (a := out) (v := (f a0).extractLsb' 0 8) hOp
  have hr1 := hr.store8 (a := out) (v := (f a0).extractLsb' 0 8) hOr
  obtain ⟨m2, c2, t2⟩ := t1.callRestore hc1 pa_dc pa_e0 (b := P + 0x12B8A)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP 0x12B8A (by decide))
    (even_at P hP (0xDC + 8) (by decide)) hr1 parseRestore_shape (by decide) (fun p hp => by
      rw [hsp]
      simp only [parseSavePs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x3C) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x38) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x34) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x30) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x2C) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x28) (by decide)⟩)
  rw [hsp] at t2
  have q : restoreRegs (memStore8 Mx out ((f a0).extractLsb' 0 8)) G
      (upd f t0 (P + BitVec.ofNat 32 (0xDC + 8))) parseSavePs sp = G := by
    simp +decide only [restoreRegs, upd, ite_false]; exact hsp
  obtain ⟨m3, e3, t3⟩ := t2.lw hc1 pa_e4 (off' := 0xE6) (by decide)
    (by rw [q]; exact aligned_add hG (k := 0x24) (by decide))
  rw [q] at t3
  obtain ⟨m4, e4, t4⟩ := t3.lw hc1 pa_e6 (off' := 0xE8) (by decide)
    (by rw [upd_ne (by decide) (by decide), q]; exact aligned_add hG (k := 0x20) (by decide))
  rw [upd_ne (by decide) (by decide), q] at t4
  obtain ⟨m5, e5, t5⟩ := t4.aluImm hc1 pa_e8 (off' := 0xEA) (by decide)
  rw [upd_ne (by decide) (by decide), upd_ne (by decide) (by decide), q,
    show aluEval .add G 0x40 = G + 0x40 from rfl] at t5
  obtain ⟨m6, e6, pc6, mem6, regs6⟩ := t5.jalr hc1 pa_ea
  refine ⟨m6, .cons e1 (c2.trans (.cons e3 (.cons e4 (.cons e5 (.single e6))))), ?_, mem6, regs6⟩
  rw [pc6, add_lit_zero]
  simp +decide only [restoreRegs, upd, ite_true, ite_false]

/-- From offset 0xD2: `parse` stores the error byte from `a0` at `out + 1`
and tag 1 at `out`, then runs `parse_tail`. -/
theorem parse_tail_err {Mx : Word → BitVec 8} {P G out : Word} {m : Machine} {f : Fin 32 → Word}
    (s : St Mx P m 0xD2 f) (hc : CodeIn Mx P manifestParseCode)
    (hr : CodeIn Mx (P + 0x12B8A) parseRestoreCode) (hP : P.toNat % 2 = 0) (hsp : f sp = G)
    (hG : G.toNat % 4 = 0) (hs0 : f s0 = out) (hOp : Sep out 2 P manifestParseCode.length)
    (hOr : Sep out 2 (P + 0x12B8A) parseRestoreCode.length) :
    ∃ m', Steps m m' ∧
      m'.pc = memLoad32 (memStore8 (memStore8 Mx (out + 1) ((f a0).extractLsb' 0 8)) out 1) (G + 0x3C)
        &&& ~~~1 ∧
      m'.mem = memStore8 (memStore8 Mx (out + 1) ((f a0).extractLsb' 0 8)) out 1 ∧
      ∀ r, reg m' r = upd (upd (upd (restoreRegs (memStore8 (memStore8 Mx (out + 1) ((f a0).extractLsb' 0 8)) out 1) G
        (upd (upd f a0 1) t0 (P + BitVec.ofNat 32 0xE4)) parseSavePs) s5
        (memLoad32 (memStore8 (memStore8 Mx (out + 1) ((f a0).extractLsb' 0 8)) out 1) (G + 0x24))) s6
        (memLoad32 (memStore8 (memStore8 Mx (out + 1) ((f a0).extractLsb' 0 8)) out 1) (G + 0x20)))
        sp (G + 0x40) r := by
  have hz := s.zero
  obtain ⟨m1, e1, t1⟩ := s.sb hc pa_d2 (off' := 0xD6) (by decide)
  rw [hs0] at t1
  have hc1 := hc.store8 (a := out + 1) (v := (f a0).extractLsb' 0 8) (hOp.sub (c := 1) (l := 1) (by omega))
  have hr1 := hr.store8 (a := out + 1) (v := (f a0).extractLsb' 0 8) (hOr.sub (c := 1) (l := 1) (by omega))
  obtain ⟨m2, e2, t2⟩ := t1.aluImm hc1 pa_d6 (off' := 0xD8) (by decide)
  rw [show aluEval .add (f x0) 1 = 1 by rw [hz]; rfl] at t2
  have h0p : Sep out 1 P manifestParseCode.length := by
    have := hOp.sub (c := 0) (l := 1) (by omega); rwa [add_ofNat_zero] at this
  have h0r : Sep out 1 (P + 0x12B8A) parseRestoreCode.length := by
    have := hOr.sub (c := 0) (l := 1) (by omega); rwa [add_ofNat_zero] at this
  obtain ⟨m3, c3, pc3, mem3, regs3⟩ := parse_tail t2 hc1 hr1 hP (by simp +decide [upd, hsp]) hG
    (by simp +decide [upd, hs0]) h0p h0r
  rw [show (upd f a0 1 a0).extractLsb' 0 8 = 1 by simp +decide [upd]] at pc3 mem3 regs3
  exact ⟨m3, .cons e1 (.cons e2 c3), pc3, mem3, regs3⟩

/-- After a call that only advances the reader's position (or writes below
the frame), the reader, the rest of memory, and the saved slots are as
before. -/
theorem PEnv.advance {P R G bp out : Word} (env : PEnv P R G bp out) {M0 M2 Mx My : Word → BitVec 8}
    {e : Word} {c N : Nat} (hcN : c + N ≤ 80)
    (hrp : memLoad32 Mx (G + 8) = bp) (hrl : memLoad32 Mx (G + 8 + 4) = 40)
    (hO : ∀ x, Sep R 144 x 1 → Mx x = M0 x)
    (hS : ∀ k, 0x20 ≤ k → k < 0x40 → Mx (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k))
    (hm : ∀ x, Sep (R + BitVec.ofNat 32 c) N x 1 → My x = memStore32 Mx (G + 8 + 8) e x) :
    memLoad32 My (G + 8) = bp ∧ memLoad32 My (G + 8 + 4) = 40 ∧ memLoad32 My (G + 8 + 8) = e ∧
    (∀ x, Sep R 144 x 1 → My x = M0 x) ∧
    (∀ k, 0x20 ≤ k → k < 0x40 → My (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k)) := by
  obtain ⟨-, -, -, -, e88, e96, -⟩ := env.r_eqs
  have fr : ∀ k, 8 ≤ k → k < 64 → Sep (R + BitVec.ofNat 32 c) N (G + BitVec.ofNat 32 k) 1 := fun k h1 h2 => by
    rw [env.g_ofs]; exact env.stack_stack c N (80 + k) 1 (by omega) (by omega) (by omega)
  have ld : ∀ k, 8 ≤ k → k + 4 ≤ 64 →
      memLoad32 My (G + BitVec.ofNat 32 k) = memLoad32 (memStore32 Mx (G + 8 + 8) e) (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact hm _ (fr (k + j) (by omega) (by omega))
  have p16 : G + 8 + 8 = G + BitVec.ofNat 32 16 := by rw [BitVec.add_assoc]; rfl
  refine ⟨?_, ?_, ?_, fun x hx => ?_, fun k h1 h2 => ?_⟩
  · rw [show G + 8 = G + BitVec.ofNat 32 8 from rfl, ld 8 (by omega) (by omega), p16,
      memLoad32_store32_sep (sep_offsets G (c := 16) (n := 4) (d := 8) (k := 4) (by omega) (by omega) (by omega))]
    exact hrp
  · rw [show G + 8 + 4 = G + BitVec.ofNat 32 12 from by rw [BitVec.add_assoc]; rfl, ld 12 (by omega) (by omega), p16,
      memLoad32_store32_sep (sep_offsets G (c := 16) (n := 4) (d := 12) (k := 4) (by omega) (by omega) (by omega)),
      show G + BitVec.ofNat 32 12 = G + 8 + 4 from by rw [BitVec.add_assoc]; rfl]
    exact hrl
  · rw [p16, ld 16 (by omega) (by omega), ← p16]; exact memLoad32_store32_same _ _ _
  · have hx' : Sep (R + BitVec.ofNat 32 c) N x 1 := (hx.sub (c := c) (l := N) (by omega))
    rw [hm x hx', memStore32_get_sep (by rw [e96]; exact hx.sub (c := 96) (l := 4) (by omega)), hO x hx]
  · rw [hm _ (fr k (by omega) (by omega)), p16,
      memStore32_get_sep (sep_offsets G (c := 16) (n := 4) (d := k) (k := 1) (by omega) (by omega) (by omega))]
    exact hS k h1 h2

/-- After an in-range `part`, as `PEnv.advance`, with the part in the frame
at `G + 0x14`. -/
theorem PEnv.advance_part_ok {P R G bp out : Word} (env : PEnv P R G bp out)
    {M0 M2 Mx My : Word → BitVec 8} {e v1 v2 : Word}
    (hrp : memLoad32 Mx (G + 8) = bp) (hrl : memLoad32 Mx (G + 8 + 4) = 40)
    (hO : ∀ x, Sep R 144 x 1 → Mx x = M0 x)
    (hS : ∀ k, 0x20 ≤ k → k < 0x40 → Mx (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k))
    (hm : ∀ x, Sep R 80 x 1 → My x = memStore8 (memStore32 (memStore32 (memStore32 Mx (G + 8 + 8) e)
      (G + 0x14 + 4) v1) (G + 0x14 + 8) v2) (G + 0x14) 0 x) :
    memLoad32 My (G + 8) = bp ∧ memLoad32 My (G + 8 + 4) = 40 ∧ memLoad32 My (G + 8 + 8) = e ∧
    (∀ x, Sep R 144 x 1 → My x = M0 x) ∧
    (∀ k, 0x20 ≤ k → k < 0x40 → My (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k)) ∧
    My (G + 0x14) = 0 ∧ memLoad32 My (G + 0x18) = v1 ∧ memLoad32 My (G + 0x1C) = v2 := by
  obtain ⟨-, -, -, -, -, e96, e100⟩ := env.r_eqs
  have fr : ∀ k, 8 ≤ k → k < 64 → Sep (R + BitVec.ofNat 32 0) 80 (G + BitVec.ofNat 32 k) 1 := fun k h1 h2 => by
    rw [env.g_ofs]; exact env.stack_stack 0 80 (80 + k) 1 (by omega) (by omega) (by omega)
  have fr' : ∀ k, 8 ≤ k → k < 64 → Sep R 80 (G + BitVec.ofNat 32 k) 1 := fun k h1 h2 => by
    have := fr k h1 h2; rwa [add_ofNat_zero] at this
  have eqs : G + 8 + 8 = G + BitVec.ofNat 32 16 ∧ G + 0x14 + 4 = G + BitVec.ofNat 32 0x18 ∧
      G + 0x14 + 8 = G + BitVec.ofNat 32 0x1C ∧ G + 0x14 = G + BitVec.ofNat 32 0x14 := by
    refine ⟨?_, ?_, ?_, rfl⟩ <;> (rw [BitVec.add_assoc]; rfl)
  obtain ⟨q16, q18, q1c, q14⟩ := eqs
  rw [q16, q18, q1c, q14] at hm
  -- The value of the store chain at a frame byte.
  have T : ∀ k, 8 ≤ k → k < 64 → My (G + BitVec.ofNat 32 k) =
      memStore8 (memStore32 (memStore32 (memStore32 Mx (G + BitVec.ofNat 32 16) e)
        (G + BitVec.ofNat 32 0x18) v1) (G + BitVec.ofNat 32 0x1C) v2) (G + BitVec.ofNat 32 0x14) 0
        (G + BitVec.ofNat 32 k) := fun k h1 h2 => hm _ (fr' k h1 h2)
  have so : ∀ a l b k, a + l ≤ b ∨ b + k ≤ a → a + l ≤ 64 → b + k ≤ 64 →
      Sep (G + BitVec.ofNat 32 a) l (G + BitVec.ofNat 32 b) k :=
    fun a l b k h h1 h2 => sep_offsets G h (by omega) (by omega)
  have ne : ∀ a b, a < 64 → b < 64 → a ≠ b → G + BitVec.ofNat 32 b ≠ G + BitVec.ofNat 32 a :=
    fun a b ha hb h => add_ofNat_ne G (by omega) (by omega) (Ne.symm h)
  have L : ∀ k, 8 ≤ k → k + 4 ≤ 64 → memLoad32 My (G + BitVec.ofNat 32 k) =
      memLoad32 (memStore8 (memStore32 (memStore32 (memStore32 Mx (G + BitVec.ofNat 32 16) e)
        (G + BitVec.ofNat 32 0x18) v1) (G + BitVec.ofNat 32 0x1C) v2) (G + BitVec.ofNat 32 0x14) 0)
        (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact T (k + j) (by omega) (by omega)
  refine ⟨?_, ?_, ?_, fun x hx => ?_, fun k h1 h2 => ?_, ?_, ?_, ?_⟩
  · rw [show G + 8 = G + BitVec.ofNat 32 8 from rfl, L 8 (by omega) (by omega),
      memLoad32_store8_sep (so 0x14 1 8 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x1C 4 8 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x18 4 8 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 16 4 8 4 (by omega) (by omega) (by omega))]
    exact hrp
  · rw [show G + 8 + 4 = G + BitVec.ofNat 32 12 from by rw [BitVec.add_assoc]; rfl, L 12 (by omega) (by omega),
      memLoad32_store8_sep (so 0x14 1 12 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x1C 4 12 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x18 4 12 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 16 4 12 4 (by omega) (by omega) (by omega)),
      show G + BitVec.ofNat 32 12 = G + 8 + 4 from by rw [BitVec.add_assoc]; rfl]
    exact hrl
  · rw [q16, L 16 (by omega) (by omega),
      memLoad32_store8_sep (so 0x14 1 16 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x1C 4 16 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x18 4 16 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_same]
  · have hx' : Sep R 80 x 1 := by have := hx.sub (c := 0) (l := 80) (by omega); rwa [add_ofNat_zero] at this
    have g : ∀ a l, 8 ≤ a → a + l ≤ 64 → Sep (G + BitVec.ofNat 32 a) l x 1 := fun a l h1 h2 => by
      rw [env.g_ofs]; exact hx.sub (c := 80 + a) (l := l) (by omega)
    have g1 : x ≠ G + BitVec.ofNat 32 0x14 := fun h => g 0x14 1 (by omega) (by omega) 0 (by omega) 0 (by omega)
      (by rw [add_ofNat_zero, add_ofNat_zero, h])
    rw [hm x hx', memStore8_ne g1, memStore32_get_sep (g 0x1C 4 (by omega) (by omega)),
      memStore32_get_sep (g 0x18 4 (by omega) (by omega)), memStore32_get_sep (g 16 4 (by omega) (by omega)),
      hO x hx]
  · rw [T k (by omega) h2, memStore8_ne (ne 0x14 k (by omega) h2 (by omega)),
      memStore32_get_sep (so 0x1C 4 k 1 (by omega) (by omega) (by omega)),
      memStore32_get_sep (so 0x18 4 k 1 (by omega) (by omega) (by omega)),
      memStore32_get_sep (so 16 4 k 1 (by omega) (by omega) (by omega))]
    exact hS k h1 h2
  · rw [q14, T 0x14 (by omega) (by omega), memStore8_same]
  · rw [show G + 0x18 = G + BitVec.ofNat 32 0x18 from rfl, L 0x18 (by omega) (by omega),
      memLoad32_store8_sep (so 0x14 1 0x18 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (so 0x1C 4 0x18 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_same]
  · rw [show G + 0x1C = G + BitVec.ofNat 32 0x1C from rfl, L 0x1C (by omega) (by omega),
      memLoad32_store8_sep (so 0x14 1 0x1C 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_same]

/-- After an out-of-range `part`: the tag and error byte in the frame, the
rest of memory, and the saved slots. -/
theorem PEnv.advance_part_err {P R G bp out : Word} (env : PEnv P R G bp out)
    {M0 M2 Mx My : Word → BitVec 8} {e : Word}
    (hO : ∀ x, Sep R 144 x 1 → Mx x = M0 x)
    (hS : ∀ k, 0x20 ≤ k → k < 0x40 → Mx (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k))
    (hm : ∀ x, Sep R 80 x 1 → My x = memStore8 (memStore8 (memStore32 Mx (G + 8 + 8) e)
      (G + 0x14 + 1) 5) (G + 0x14) 1 x) :
    (∀ x, Sep R 144 x 1 → My x = M0 x) ∧
    (∀ k, 0x20 ≤ k → k < 0x40 → My (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k)) ∧
    My (G + 0x14) = 1 ∧ My (G + 0x15) = 5 := by
  have fr' : ∀ k, 8 ≤ k → k < 64 → Sep R 80 (G + BitVec.ofNat 32 k) 1 := fun k h1 h2 => by
    rw [env.g_ofs]; have := env.stack_stack 0 80 (80 + k) 1 (by omega) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have q16 : G + 8 + 8 = G + BitVec.ofNat 32 16 := by rw [BitVec.add_assoc]; rfl
  have q15 : G + 0x14 + 1 = G + BitVec.ofNat 32 0x15 := by rw [BitVec.add_assoc]; rfl
  rw [q16, q15, show G + 0x14 = G + BitVec.ofNat 32 0x14 from rfl] at hm
  have ne : ∀ a b, a < 64 → b < 64 → a ≠ b → G + BitVec.ofNat 32 b ≠ G + BitVec.ofNat 32 a :=
    fun a b ha hb h => add_ofNat_ne G (by omega) (by omega) (Ne.symm h)
  refine ⟨fun x hx => ?_, fun k h1 h2 => ?_, ?_, ?_⟩
  · have hx' : Sep R 80 x 1 := by have := hx.sub (c := 0) (l := 80) (by omega); rwa [add_ofNat_zero] at this
    have g : ∀ a l, 8 ≤ a → a + l ≤ 64 → Sep (G + BitVec.ofNat 32 a) l x 1 := fun a l h1 h2 => by
      rw [env.g_ofs]; exact hx.sub (c := 80 + a) (l := l) (by omega)
    have gne : ∀ a, 8 ≤ a → a < 64 → x ≠ G + BitVec.ofNat 32 a := fun a h1 h2 h =>
      g a 1 h1 (by omega) 0 (by omega) 0 (by omega) (by rw [add_ofNat_zero, add_ofNat_zero, h])
    rw [hm x hx', memStore8_ne (gne 0x14 (by omega) (by omega)), memStore8_ne (gne 0x15 (by omega) (by omega)),
      memStore32_get_sep (g 16 4 (by omega) (by omega)), hO x hx]
  · rw [hm _ (fr' k (by omega) h2), memStore8_ne (ne 0x14 k (by omega) h2 (by omega)),
      memStore8_ne (ne 0x15 k (by omega) h2 (by omega)),
      memStore32_get_sep (sep_offsets G (c := 16) (n := 4) (d := k) (k := 1) (by omega) (by omega) (by omega))]
    exact hS k h1 h2
  · rw [show G + 0x14 = G + BitVec.ofNat 32 0x14 from rfl, hm _ (fr' 0x14 (by omega) (by omega)), memStore8_same]
  · rw [show G + 0x15 = G + BitVec.ofNat 32 0x15 from rfl, hm _ (fr' 0x15 (by omega) (by omega)),
      memStore8_ne (ne 0x14 0x15 (by omega) (by omega) (by omega)), memStore8_same]

/-- The registers `parse` writes before it restores the saved ones. -/
abbrev parseClob : List (Fin 32) := [a0, a1, a2, a3, a4, a5, t0, ra, sp, s0, s1, s2, s3, s4, s5, s6]

theorem keep_upd' {g h : Fin 32 → Word} {rd : Fin 32} {v : Word}
    (hk : ∀ r, r ∉ parseClob → g r = h r) (h0 : h 0 = 0) (hrd : rd ∈ parseClob) :
    ∀ r, r ∉ parseClob → upd g rd v r = h r := by
  intro r hr
  by_cases hr0 : r.val = 0
  · have : r = 0 := Fin.ext hr0
    subst this; simp [upd, h0]
  · have : r ≠ rd := fun e => hr (e ▸ hrd)
    simp [upd, hr0, this, hk r hr]

theorem parse_finish {Mf : Word → BitVec 8} {g h : Fin 32 → Word} {G L : Word}
    (hk : ∀ r, r ∉ parseClob → g r = h r) (h0 : h 0 = 0)
    (hra : memLoad32 Mf (G + 0x3C) = h ra) (hs0 : memLoad32 Mf (G + 0x38) = h s0)
    (hs1 : memLoad32 Mf (G + 0x34) = h s1) (hs2 : memLoad32 Mf (G + 0x30) = h s2)
    (hs3 : memLoad32 Mf (G + 0x2C) = h s3) (hs4 : memLoad32 Mf (G + 0x28) = h s4)
    (hs5 : memLoad32 Mf (G + 0x24) = h s5) (hs6 : memLoad32 Mf (G + 0x20) = h s6)
    (hsp : G + 0x40 = h sp) :
    ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 →
      upd (upd (upd (restoreRegs Mf G (upd g t0 L) parseSavePs) s5 (memLoad32 Mf (G + 0x24))) s6
        (memLoad32 Mf (G + 0x20))) sp (G + 0x40) r = h r := by
  intro r h1 h2 h3 h4 h5 h6 h7
  by_cases hr0 : r.val = 0
  · have : r = 0 := Fin.ext hr0
    subst this; simp [upd, h0]
  by_cases e : r = sp
  · subst e; simp +decide [upd]; exact hsp
  by_cases e1 : r = ra
  · subst e1; simp +decide [restoreRegs, upd]; exact hra
  by_cases e2 : r = s0
  · subst e2; simp +decide [restoreRegs, upd]; exact hs0
  by_cases e3 : r = s1
  · subst e3; simp +decide [restoreRegs, upd]; exact hs1
  by_cases e4 : r = s2
  · subst e4; simp +decide [restoreRegs, upd]; exact hs2
  by_cases e5 : r = s3
  · subst e5; simp +decide [restoreRegs, upd]; exact hs3
  by_cases e6 : r = s4
  · subst e6; simp +decide [restoreRegs, upd]; exact hs4
  by_cases e7 : r = s5
  · subst e7; simp +decide [upd]; exact hs5
  by_cases e8 : r = s6
  · subst e8; simp +decide [upd]; exact hs6
  have hr : r ∉ parseClob := by
    simp only [parseClob, List.mem_cons, List.not_mem_nil, or_false]
    intro hh
    rcases hh with hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh | hh <;>
      contradiction
  simp only [restoreRegs, upd, hr0, e, e1, e2, e3, e4, e5, e6, e7, e8, h7, ite_false]
  exact hk r hr

/-- The test `parse` makes after each check: `andi a1, a0, 0xFF; addi a1,
a1, -0xFF; bne a1, x0` continues when the low byte of `a0` is 0xFF and goes
to the error path at 0xD2 otherwise. -/
theorem check_branch {Mx : Word → BitVec 8} {base : Word} {m : Machine} {off : Nat} {f : Fin 32 → Word}
    {o : Word} (s : St Mx base m off f) (hc : CodeIn Mx base manifestParseCode)
    (h1 : fetchRel manifestParseCode off = some (.aluImm .and a1 a0 0xFF, 4))
    (h2 : fetchRel manifestParseCode (off + 4) = some (.aluImm .add a1 a1 0xFFFFFF01, 4))
    (h3 : fetchRel manifestParseCode (off + 8) = some (.branch .bne a1 x0 o, 2))
    (ho : BitVec.ofNat 32 (off + 8) + o = BitVec.ofNat 32 0xD2) :
    ∃ m' g, Steps m m' ∧ (∀ r, r ≠ a1 → g r = f r) ∧
      ((f a0 &&& 0xFF = 0xFF ∧ St Mx base m' (off + 10) g) ∨
       (f a0 &&& 0xFF ≠ 0xFF ∧ St Mx base m' 0xD2 g)) := by
  have hz := s.zero
  obtain ⟨m1, e1, t1⟩ := s.aluImm hc h1 (off' := off + 4) (ofNat_add_ofNat off 4)
  obtain ⟨m2, e2, t2⟩ := t1.aluImm hc h2 (off' := off + 8) (ofNat_add_ofNat (off + 4) 4)
  have g2 : ∀ r, r ≠ a1 → upd (upd f a1 (aluEval .and (f a0) 0xFF)) a1
      (aluEval .add (upd f a1 (aluEval .and (f a0) 0xFF) a1) 0xFFFFFF01) r = f r := fun r h => by
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [upd, hz]
    · simp [upd, hr, h]
  have v2 : upd (upd f a1 (aluEval .and (f a0) 0xFF)) a1
      (aluEval .add (upd f a1 (aluEval .and (f a0) 0xFF) a1) 0xFFFFFF01) a1 =
        (f a0 &&& 0xFF) + 0xFFFFFF01 := by simp +decide [upd, aluEval]
  have z2 : upd (upd f a1 (aluEval .and (f a0) 0xFF)) a1
      (aluEval .add (upd f a1 (aluEval .and (f a0) 0xFF) a1) 0xFFFFFF01) x0 = 0 := by simp [upd]
  by_cases h : f a0 &&& 0xFF = 0xFF
  · obtain ⟨m3, e3, t3⟩ := t2.notTaken hc (off + 10) h3 (ofNat_add_ofNat (off + 8) 2)
      (by rw [v2, z2, h]; decide)
    exact ⟨m3, _, .cons e1 (.cons e2 (.single e3)), g2, .inl ⟨h, t3⟩⟩
  · have hne : (f a0 &&& 0xFF) + 0xFFFFFF01 ≠ 0 := fun e => h (by
      have := congrArg (· + 0xFF) e
      simp only [BitVec.add_assoc] at this
      rw [show (0xFFFFFF01 : Word) + 0xFF = 0 from rfl] at this
      exact (BitVec.add_zero _).symm.trans (this.trans (BitVec.zero_add _)))
    obtain ⟨m3, e3, t3⟩ := t2.taken hc 0xD2 h3 ho (by rw [v2, z2]; exact bne_iff_ne.mpr hne)
    exact ⟨m3, _, .cons e1 (.cons e2 (.single e3)), g2, .inr ⟨h, t3⟩⟩

theorem version_val {Mx M : Word → BitVec 8} {self bp : Word} (hp : memLoad32 Mx self = bp)
    (hl : memLoad32 Mx (self + 4) = 40) (hq : memLoad32 Mx (self + 8) = 4)
    (h4 : Mx (bp + 4) = M (bp + 4)) (h5 : Mx (bp + 5) = M (bp + 5)) :
    version1Result Mx self =
      if ((M (bp + 5)).zeroExtend 32 <<< 24 ||| (M (bp + 4)).zeroExtend 32 <<< 16 : Word) >>> 16 == 1
      then 0xFFFFFFFF else 3 := by
  have hb : bytesResult bp 40 4 2 = some (bp + 4, 4 + 2) := rfl
  unfold version1Result u16Result
  rw [hp, hl, hq]
  have h5' : Mx (bp + 4 + 1) = M (bp + 5) := by
    rw [show bp + 4 + 1 = bp + 5 from by rw [BitVec.add_assoc]; rfl]; exact h5
  simp only [hb, h5', h4]

theorem u16Mem_val {Mx : Word → BitVec 8} {self bp : Word} (hp : memLoad32 Mx self = bp)
    (hl : memLoad32 Mx (self + 4) = 40) (hq : memLoad32 Mx (self + 8) = 4) (x : Word) :
    u16Mem Mx self x = memStore32 Mx (self + 8) 6 x := by
  have hb : bytesResult bp 40 4 2 = some (bp + 4, 6) := rfl
  unfold u16Mem; rw [hp, hl, hq]; simp only [hb]

theorem reserved_val {Mx M : Word → BitVec 8} {self bp : Word} (hp : memLoad32 Mx self = bp)
    (hl : memLoad32 Mx (self + 4) = 40) (hq : memLoad32 Mx (self + 8) = 6)
    (hz : allZero Mx (bp + 6) 2 = allZero M (bp + 6) 2) :
    reservedResult Mx self 2 = if allZero M (bp + 6) 2 then 0xFF else 4 := by
  have hb : bytesResult bp 40 6 2 = some (bp + 6, 8) := rfl
  unfold reservedResult; rw [hp, hl, hq]; simp only [hb]
  rw [show (2 : Word).toNat = 2 from rfl, hz]

theorem reservedMem_val {Mx : Word → BitVec 8} {self bp : Word} (hp : memLoad32 Mx self = bp)
    (hl : memLoad32 Mx (self + 4) = 40) (hq : memLoad32 Mx (self + 8) = 6) (x : Word) :
    reservedMem Mx self 2 x = memStore32 Mx (self + 8) 8 x := by
  have hb : bytesResult bp 40 6 2 = some (bp + 6, 8) := rfl
  unfold reservedMem; rw [hp, hl, hq]; simp only [hb]

theorem part_val {Mx : Word → BitVec 8} {o self lo hi bp : Word} (pos : Word)
    (hp : memLoad32 Mx self = bp) (hl : memLoad32 Mx (self + 4) = 40) (hq : memLoad32 Mx (self + 8) = pos)
    (h1 : bytesResult bp 40 pos 4 = some (bp + pos, pos + 4))
    (h2 : bytesResult bp 40 (pos + 4) 4 = some (bp + (pos + 4), pos + 4 + 4)) (x : Word) :
    partMem Mx o self lo hi x =
      if (memLoad32 Mx (bp + (pos + 4))).ult lo || hi.ult (memLoad32 Mx (bp + (pos + 4))) then
        memStore8 (memStore8 (memStore32 Mx (self + 8) (pos + 4 + 4)) (o + 1) 5) o 1 x
      else
        memStore8 (memStore32 (memStore32 (memStore32 Mx (self + 8) (pos + 4 + 4)) (o + 4)
          (memLoad32 Mx (bp + pos))) (o + 8) (memLoad32 Mx (bp + (pos + 4)))) o 0 x := by
  unfold partMem; rw [hp, hl, hq]; simp only [h1, h2]
  split <;> rfl

theorem upd_same {f : Fin 32 → Word} {rd : Fin 32} {v : Word} (h : rd.val ≠ 0) : upd f rd v rd = v := by
  simp [upd, h]

theorem reg_ne {m m' : Machine} {rd : Fin 32} {v : Word} (h : ∀ r, reg m' r = upd (reg m) rd v r)
    {r : Fin 32} (hr : r ≠ rd) : reg m' r = reg m r := by
  rw [h]
  by_cases h0 : r.val = 0
  · have : r = 0 := Fin.ext h0
    subst this; rfl
  · simp [upd, h0, hr]

theorem reg_eq {m m' : Machine} {rd : Fin 32} {v : Word} (h : ∀ r, reg m' r = upd (reg m) rd v r)
    (h0 : rd.val ≠ 0) : reg m' rd = v := by
  rw [h]; simp [upd, h0]

theorem keep_ne {m m' m0 : Machine} {rd : Fin 32} {v : Word} (h : ∀ r, reg m' r = upd (reg m) rd v r)
    (hrd : rd ∈ parseClob) (hk : ∀ r, r ∉ parseClob → reg m r = reg m0 r) :
    ∀ r, r ∉ parseClob → reg m' r = reg m0 r := fun r hr => by
  rw [reg_ne h (r := r) (fun e : r = rd => hr (e ▸ hrd))]; exact hk r hr

theorem bytesResult_at (bp : Word) (p n : Nat) (h : p + n ≤ 40) :
    bytesResult bp 40 (BitVec.ofNat 32 p) (BitVec.ofNat 32 n) =
      some (bp + BitVec.ofNat 32 p, BitVec.ofNat 32 p + BitVec.ofNat 32 n) := by
  rw [bytesResult_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), show (40 : Word).toNat = 40 from rfl]
  simp only [h, ↓reduceIte]

/-- One of `parse`'s calls to `part` at offset `off`, then `lbu a0, 0x14(sp)`:
the result's tag in `a0` and, for a length in range, the two words and the
reader advanced by 8. -/
theorem PEnv.part_step {P R G bp out : Word} (env : PEnv P R G bp out) {M0 M2 Mx : Word → BitVec 8}
    {m : Machine} {off : Nat} {f : Fin 32 → Word} {imm o lo hi : Word} (p : Nat) (hp : p + 8 ≤ 40)
    (s : St Mx P m off f)
    (h1 : fetchRel manifestParseCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel manifestParseCode (off + 4) = some (.jalr ra ra o, 4))
    (h3 : fetchRel manifestParseCode (off + 8) = some (.load .lbu a0 sp 0x14, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x162)
    (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = G) (ha0 : f a0 = G + 0x14) (ha1 : f a1 = G + 8) (ha2 : f a2 = lo) (ha3 : f a3 = hi)
    (hrp : memLoad32 Mx (G + 8) = bp) (hrl : memLoad32 Mx (G + 8 + 4) = 40)
    (hrq : memLoad32 Mx (G + 8 + 8) = BitVec.ofNat 32 p)
    (hO : ∀ x, Sep R 144 x 1 → Mx x = M0 x)
    (hS : ∀ k, 0x20 ≤ k → k < 0x40 → Mx (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k))
    (hcode : ∀ My : Word → BitVec 8, (∀ x, Sep R 144 x 1 → My x = M0 x) → PCode My P) :
    ∃ m' My, Steps m m' ∧ St My P m' (off + 12) (reg m') ∧ reg m' sp = G ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → r ≠ ra → reg m' r = f r) ∧
      (∀ x, Sep R 144 x 1 → My x = M0 x) ∧
      (∀ k, 0x20 ≤ k → k < 0x40 → My (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k)) ∧
      (if partOut lo hi (mw M0 bp (p + 4)) then reg m' a0 = 1 ∧ My (G + 0x15) = 5
       else reg m' a0 = 0 ∧ memLoad32 My (G + 8) = bp ∧ memLoad32 My (G + 8 + 4) = 40 ∧
         memLoad32 My (G + 8 + 8) = BitVec.ofNat 32 (p + 8) ∧
         memLoad32 My (G + 0x18) = mw M0 bp p ∧ memLoad32 My (G + 0x1C) = mw M0 bp (p + 4)) := by
  have code := hcode Mx hO
  obtain ⟨m1, c1, t1, sp1, fr1, mem1⟩ := parse_part env s code h1 h2 hb hl hsp ha0 ha1 ha2 ha3 hrp hrl
  have b1 := bytesResult_at bp p 4 (by omega)
  have b2 : bytesResult bp 40 (BitVec.ofNat 32 p + 4) 4 =
      some (bp + (BitVec.ofNat 32 p + 4), BitVec.ofNat 32 p + 4 + 4) := by
    rw [show BitVec.ofNat 32 p + 4 = BitVec.ofNat 32 (p + 4) from ofNat_add_ofNat p 4]
    exact bytesResult_at bp (p + 4) 4 (by omega)
  have buf : ∀ i, i + 4 ≤ 40 → memLoad32 Mx (bp + BitVec.ofNat 32 i) = mw M0 bp i := fun i hi =>
    memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact hO _ (env.hBS.sub (c := i + j) (l := 1) (by omega)).symm
  have hv1 : memLoad32 Mx (bp + BitVec.ofNat 32 p) = mw M0 bp p := buf p (by omega)
  have hv2 : memLoad32 Mx (bp + (BitVec.ofNat 32 p + 4)) = mw M0 bp (p + 4) := by
    rw [show BitVec.ofNat 32 p + 4 = BitVec.ofNat 32 (p + 4) from ofNat_add_ofNat p 4]; exact buf (p + 4) (by omega)
  have he : BitVec.ofNat 32 p + 4 + 4 = BitVec.ofNat 32 (p + 8) := by
    rw [show BitVec.ofNat 32 p + 4 = BitVec.ofNat 32 (p + 4) from ofNat_add_ofNat p 4]
    exact ofNat_add_ofNat (p + 4) 4
  have mem1' : ∀ x, Sep R 80 x 1 → m1.mem x =
      if partOut lo hi (mw M0 bp (p + 4)) then
        memStore8 (memStore8 (memStore32 Mx (G + 8 + 8) (BitVec.ofNat 32 (p + 8))) (G + 0x14 + 1) 5) (G + 0x14) 1 x
      else
        memStore8 (memStore32 (memStore32 (memStore32 Mx (G + 8 + 8) (BitVec.ofNat 32 (p + 8))) (G + 0x14 + 4)
          (mw M0 bp p)) (G + 0x14 + 8) (mw M0 bp (p + 4))) (G + 0x14) 0 x := fun x hx => by
    rw [mem1 x hx, part_val (BitVec.ofNat 32 p) hrp hrl hrq b1 b2 x, hv1, hv2, he]
  have t1' : St m1.mem P m1 (off + 8) (reg m1) := t1
  cases hc : partOut lo hi (mw M0 bp (p + 4))
  · simp only [hc, Bool.false_eq_true, ite_false] at mem1'
    obtain ⟨q1, q2, q3, O1, S1, tag, w1, w2⟩ := env.advance_part_ok (M0 := M0) (M2 := M2) (My := m1.mem)
      hrp hrl hO hS mem1'
    obtain ⟨m2, e2, t2⟩ := t1'.lbu (hcode _ O1).parse h3 (off' := off + 12) (ofNat_add_ofNat (off + 8) 4)
    rw [sp1, show G + 0x14 = G + 0x14 from rfl, tag] at t2
    refine ⟨m2, m1.mem, c1.trans (.single e2), t2.self, ?_, fun r h0 h1' h2' h3' h4 h5 h6 h7 => ?_, O1, S1,
      ⟨?_, q1, q2, q3, w1, w2⟩⟩
    · rw [t2.regs]; simp +decide [upd, sp1]
    · rw [t2.regs]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd]; exact s.zero.symm
      · simp [upd, hr, h0]; exact fr1 r h0 h1' h2' h3' h4 h5 h6 h7
    · rw [t2.regs]; simp +decide [upd]
  · simp only [hc, ite_true] at mem1'
    obtain ⟨O1, S1, tag, err⟩ := env.advance_part_err (M0 := M0) (M2 := M2) (My := m1.mem) hO hS mem1'
    obtain ⟨m2, e2, t2⟩ := t1'.lbu (hcode _ O1).parse h3 (off' := off + 12) (ofNat_add_ofNat (off + 8) 4)
    rw [sp1, tag] at t2
    refine ⟨m2, m1.mem, c1.trans (.single e2), t2.self, ?_, fun r h0 h1' h2' h3' h4 h5 h6 h7 => ?_, O1, S1,
      ⟨?_, err⟩⟩
    · rw [t2.regs]; simp +decide [upd, sp1]
    · rw [t2.regs]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd]; exact s.zero.symm
      · simp [upd, hr, h0]; exact fr1 r h0 h1' h2' h3' h4 h5 h6 h7
    · rw [t2.regs]; simp +decide [upd]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **The compiled `manifest::parse` is correct.** With the functions it
runs where the image puts them (`PCode`), the result address `out` in `a0`,
the 40-byte manifest at `bp` in `a1`, `sp` at `G + 0x40`, and the layout
`PEnv` describes, there is an execution that reaches the return address with
`sp` restored, every register but `a0` through `a5` and `t0` unchanged, and
memory outside the 144 bytes of stack below `sp` as `parseMem` says. -/
theorem manifestParse_correct (m : Machine) (P retAddr out bp R G : Word)
    (code : PCode m.mem P) (hpc : m.pc = P)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = bp) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hspG : reg m sp = G + 0x40)
    (env : PEnv P R G bp out) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → reg m' r = reg m r) ∧
      ∀ x, Sep R 144 x 1 → m'.mem x = parseMem m.mem out bp x := by
  have s0' : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0'.zero
  obtain ⟨e32, e48, e64, eR, e88, e96, e100⟩ := env.r_eqs
  have hG := env.hG
  -- Memory that agrees with `m.mem` outside the stack region holds the code.
  have pcode : ∀ Mx : Word → BitVec 8, (∀ x, Sep R 144 x 1 → Mx x = m.mem x) → PCode Mx P :=
    fun Mx h => code.of_agree fun k hk => h _ (env.hSW.subR (c := k) (l := 1) (by omega))
  have outSt : ∀ (Mx : Word → BitVec 8) (c : Nat) (v : Word), c + 4 ≤ 64 →
      (∀ x, Sep R 144 x 1 → Mx x = m.mem x) →
      ∀ x, Sep R 144 x 1 → memStore32 Mx (G + BitVec.ofNat 32 c) v x = m.mem x := fun Mx c v hc h x hx => by
    rw [memStore32_get_sep (by rw [env.g_ofs]; exact hx.sub (c := 80 + c) (l := 4) (by omega)), h x hx]
  have gsep : ∀ c, c + 4 ≤ 64 → ∀ b, ∀ l, b + l ≤ parseWindowLen →
      Sep (G + BitVec.ofNat 32 c) 4 (parseWindow P + BitVec.ofNat 32 b) l := fun c hc b l hl => by
    rw [env.g_ofs]; exact env.stack_code (80 + c) 4 (by omega) b l hl
  -- 0x00: allocate the frame.
  obtain ⟨m1, e1, t1⟩ := s0'.aluImm code.parse pa_0 (off' := 2) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFC0 = G by
    rw [hspG]; show G + 0x40 + 0xFFFFFFC0 = G; rw [BitVec.add_assoc]; exact BitVec.add_zero G] at t1
  have f1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  have f1 : ∀ r, r ≠ sp → upd (reg m) sp G r = reg m r := fun r h => by
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [upd, hz]
    · simp [upd, hr, h]
  -- 0x02: the save helper saves `ra` and `s0` through `s4`.
  have WS : P + 0x12B98 = parseWindow P + BitVec.ofNat 32 0x167B8 := wq P _ _ (by decide)
  obtain ⟨m2, c2, t2⟩ := t1.callSave code.parse pa_2 pa_6 (b := P + 0x12B98)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x12B98 (by decide))
    (even_at P env.hP (2 + 8) (by decide)) code.save parseSave_shape (by decide) (fun p hp => by
      rw [f1sp, WS]
      simp only [parseSavePs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨by decide, aligned_add hG (k := 0x3C) (by decide), gsep 0x3C (by omega) _ _ (by decide)⟩
      · exact ⟨by decide, aligned_add hG (k := 0x38) (by decide), gsep 0x38 (by omega) _ _ (by decide)⟩
      · exact ⟨by decide, aligned_add hG (k := 0x34) (by decide), gsep 0x34 (by omega) _ _ (by decide)⟩
      · exact ⟨by decide, aligned_add hG (k := 0x30) (by decide), gsep 0x30 (by omega) _ _ (by decide)⟩
      · exact ⟨by decide, aligned_add hG (k := 0x2C) (by decide), gsep 0x2C (by omega) _ _ (by decide)⟩
      · exact ⟨by decide, aligned_add hG (k := 0x28) (by decide), gsep 0x28 (by omega) _ _ (by decide)⟩)
  rw [f1sp] at t2
  obtain ⟨M1, hM1⟩ : ∃ M1, saveMem m.mem G (upd (reg m) sp G) parseSavePs = M1 := ⟨_, rfl⟩
  rw [hM1] at t2
  have M1out : ∀ x, Sep R 144 x 1 → M1 x = m.mem x := by
    rw [← hM1]; simp only [saveMem]
    exact outSt _ 0x28 _ (by omega) (outSt _ 0x2C _ (by omega) (outSt _ 0x30 _ (by omega)
      (outSt _ 0x34 _ (by omega) (outSt _ 0x38 _ (by omega) (outSt _ 0x3C _ (by omega) (fun _ _ => rfl))))))
  have F2 : ∀ r, r ≠ sp → r ≠ t0 → upd (upd (reg m) sp G) t0 (P + BitVec.ofNat 32 (2 + 8)) r = reg m r :=
    fun r h1 h2 => by
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h1, h2]
  have F2sp : upd (upd (reg m) sp G) t0 (P + BitVec.ofNat 32 (2 + 8)) sp = G := by simp +decide [upd]
  -- 0x0A, 0x0C: save `s5` and `s6`.
  obtain ⟨m3, e3, t3⟩ := t2.sw (pcode M1 M1out).parse pa_a (off' := 0xC) (by decide)
    (by rw [F2sp]; exact aligned_add hG (k := 0x24) (by decide))
  rw [F2sp, F2 s5 (by decide) (by decide)] at t3
  have M1'out := outSt M1 0x24 (reg m s5) (by omega) M1out
  obtain ⟨m4, e4, t4⟩ := t3.sw (pcode _ M1'out).parse pa_c (off' := 0xE) (by decide)
    (by rw [F2sp]; exact aligned_add hG (k := 0x20) (by decide))
  rw [F2sp, F2 s6 (by decide) (by decide)] at t4
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore32 (memStore32 M1 (G + 0x24) (reg m s5)) (G + 0x20) (reg m s6) = M2 :=
    ⟨_, rfl⟩
  rw [hM2] at t4
  have M2out : ∀ x, Sep R 144 x 1 → M2 x = m.mem x := by
    rw [← hM2]; exact outSt _ 0x20 _ (by omega) M1'out
  -- The saved values.
  have M2slots : memLoad32 M2 (G + 0x3C) = reg m ra ∧ memLoad32 M2 (G + 0x38) = reg m s0 ∧
      memLoad32 M2 (G + 0x34) = reg m s1 ∧ memLoad32 M2 (G + 0x30) = reg m s2 ∧
      memLoad32 M2 (G + 0x2C) = reg m s3 ∧ memLoad32 M2 (G + 0x28) = reg m s4 ∧
      memLoad32 M2 (G + 0x24) = reg m s5 ∧ memLoad32 M2 (G + 0x20) = reg m s6 := by
    have so : ∀ c d, c < 64 → d < 64 → c + 4 ≤ d ∨ d + 4 ≤ c →
        Sep (G + BitVec.ofNat 32 c) 4 (G + BitVec.ofNat 32 d) 4 :=
      fun c d hc hd h => sep_offsets G h (by omega) (by omega)
    rw [← hM2, ← hM1]; simp only [saveMem]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [memLoad32_store32_sep (show Sep (G + 32) 4 (G + 60) 4 from so 32 60 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 36) 4 (G + 60) 4 from so 36 60 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 40) 4 (G + 60) 4 from so 40 60 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 44) 4 (G + 60) 4 from so 44 60 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 48) 4 (G + 60) 4 from so 48 60 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 52) 4 (G + 60) 4 from so 52 60 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 56) 4 (G + 60) 4 from so 56 60 (by omega) (by omega) (by omega)),
        memLoad32_store32_same,
        f1 ra (by decide)]
    · rw [memLoad32_store32_sep (show Sep (G + 32) 4 (G + 56) 4 from so 32 56 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 36) 4 (G + 56) 4 from so 36 56 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 40) 4 (G + 56) 4 from so 40 56 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 44) 4 (G + 56) 4 from so 44 56 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 48) 4 (G + 56) 4 from so 48 56 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 52) 4 (G + 56) 4 from so 52 56 (by omega) (by omega) (by omega)),
        memLoad32_store32_same,
        f1 s0 (by decide)]
    · rw [memLoad32_store32_sep (show Sep (G + 32) 4 (G + 52) 4 from so 32 52 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 36) 4 (G + 52) 4 from so 36 52 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 40) 4 (G + 52) 4 from so 40 52 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 44) 4 (G + 52) 4 from so 44 52 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 48) 4 (G + 52) 4 from so 48 52 (by omega) (by omega) (by omega)),
        memLoad32_store32_same,
        f1 s1 (by decide)]
    · rw [memLoad32_store32_sep (show Sep (G + 32) 4 (G + 48) 4 from so 32 48 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 36) 4 (G + 48) 4 from so 36 48 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 40) 4 (G + 48) 4 from so 40 48 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 44) 4 (G + 48) 4 from so 44 48 (by omega) (by omega) (by omega)),
        memLoad32_store32_same,
        f1 s2 (by decide)]
    · rw [memLoad32_store32_sep (show Sep (G + 32) 4 (G + 44) 4 from so 32 44 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 36) 4 (G + 44) 4 from so 36 44 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 40) 4 (G + 44) 4 from so 40 44 (by omega) (by omega) (by omega)),
        memLoad32_store32_same,
        f1 s3 (by decide)]
    · rw [memLoad32_store32_sep (show Sep (G + 32) 4 (G + 40) 4 from so 32 40 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 36) 4 (G + 40) 4 from so 36 40 (by omega) (by omega) (by omega)),
        memLoad32_store32_same,
        f1 s4 (by decide)]
    · rw [memLoad32_store32_sep (show Sep (G + 32) 4 (G + 36) 4 from so 32 36 (by omega) (by omega) (by omega)),
        memLoad32_store32_same]
    · rw [memLoad32_store32_same]
  -- Every error path ends at offset 0xD2 with the error in `a0`.
  have WP : P = parseWindow P + BitVec.ofNat 32 0x3C20 := by
    show P = P + 0xFFFFC3E0 + BitVec.ofNat 32 0x3C20
    rw [BitVec.add_assoc, show (0xFFFFC3E0 : Word) + BitVec.ofNat 32 0x3C20 = 0 from rfl]
    exact (BitVec.add_zero P).symm
  have WRs : P + 0x12B8A = parseWindow P + BitVec.ofNat 32 0x167AA := wq P _ _ (by decide)
  have Oc : ∀ n, n ≤ 36 → Sep out n P manifestParseCode.length ∧ Sep out n (P + 0x12B8A) parseRestoreCode.length :=
    fun n hn => by
      have h0 : Sep out n (parseWindow P) parseWindowLen := by
        have := env.hOW.sub (c := 0) (l := n) (by omega); rwa [add_ofNat_zero] at this
      exact ⟨by rw [WP]; exact h0.subR (c := 0x3C20) (l := _) (by decide),
        by rw [WRs]; exact h0.subR (c := 0x167AA) (l := _) (by decide)⟩
  have outG : ∀ c, c < 64 → ∀ j, j < 36 → out + BitVec.ofNat 32 j ≠ G + BitVec.ofNat 32 c := fun c hc j hj h =>
    (env.hOS.sub (c := j) (l := 1) (by omega)) 0 (by omega) (80 + c) (by omega)
      (by rw [add_ofNat_zero, ← add_ofNat_assoc, ← env.hRG, h])
  have slotsOf : ∀ Mf : Word → BitVec 8,
      (∀ k, 0x20 ≤ k → k < 0x40 → Mf (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k)) →
      memLoad32 Mf (G + 0x3C) = reg m ra ∧ memLoad32 Mf (G + 0x38) = reg m s0 ∧
      memLoad32 Mf (G + 0x34) = reg m s1 ∧ memLoad32 Mf (G + 0x30) = reg m s2 ∧
      memLoad32 Mf (G + 0x2C) = reg m s3 ∧ memLoad32 Mf (G + 0x28) = reg m s4 ∧
      memLoad32 Mf (G + 0x24) = reg m s5 ∧ memLoad32 Mf (G + 0x20) = reg m s6 := by
    intro Mf h
    have e : ∀ c, 0x20 ≤ c → c + 4 ≤ 0x40 →
        memLoad32 Mf (G + BitVec.ofNat 32 c) = memLoad32 M2 (G + BitVec.ofNat 32 c) :=
      fun c h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h _ (by omega) (by omega)
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := M2slots
    exact ⟨(e 0x3C (by omega) (by omega)).trans q1, (e 0x38 (by omega) (by omega)).trans q2,
      (e 0x34 (by omega) (by omega)).trans q3, (e 0x30 (by omega) (by omega)).trans q4,
      (e 0x2C (by omega) (by omega)).trans q5, (e 0x28 (by omega) (by omega)).trans q6,
      (e 0x24 (by omega) (by omega)).trans q7, (e 0x20 (by omega) (by omega)).trans q8⟩
  have hsp0 : G + 0x40 = reg m sp := hspG.symm
  have errExit : ∀ (n : Machine) (Mx : Word → BitVec 8) (g : Fin 32 → Word) (e : BitVec 8),
      Steps m n → St Mx P n 0xD2 g → g sp = G → g s0 = out → (g a0).extractLsb' 0 8 = e →
      parseErr m.mem bp = some e → (∀ x, Sep R 144 x 1 → Mx x = m.mem x) →
      (∀ k, 0x20 ≤ k → k < 0x40 → Mx (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k)) →
      (∀ r, r ∉ parseClob → g r = reg m r) →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → reg m' r = reg m r) ∧
        ∀ x, Sep R 144 x 1 → m'.mem x = parseMem m.mem out bp x := by
    intro n Mx g e hn s hsp hs0 he hpe hO hS hk
    have cd := pcode Mx hO
    obtain ⟨n', c', pc', mem', regs'⟩ := parse_tail_err s cd.parse cd.restore env.hP hsp hG hs0
      (Oc 2 (by omega)).1 (Oc 2 (by omega)).2
    rw [he] at pc' mem' regs'
    have hS' : ∀ k, 0x20 ≤ k → k < 0x40 → memStore8 (memStore8 Mx (out + 1) e) out 1 (G + BitVec.ofNat 32 k) =
        M2 (G + BitVec.ofNat 32 k) := fun k h1 h2 => by
      rw [memStore8_ne (fun h => outG k (by omega) 0 (by omega) (by rw [add_ofNat_zero]; exact h.symm)),
        memStore8_ne (show G + BitVec.ofNat 32 k ≠ out + 1 from fun h => outG k (by omega) 1 (by omega) h.symm),
        hS k h1 h2]
    obtain ⟨sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8⟩ := slotsOf _ hS'
    have fin := parse_finish (L := P + BitVec.ofNat 32 0xE4)
      (keep_upd' (rd := a0) (v := 1) hk hz (by decide)) hz sl1 sl2 sl3 sl4 sl5 sl6 sl7 sl8 hsp0
    refine ⟨n', hn.trans c', by rw [pc', sl1, hra, hret], ?_, fun r h1 h2 h3 h4 h5 h6 h7 => by
      rw [regs']; exact fin r h1 h2 h3 h4 h5 h6 h7, fun x hx => ?_⟩
    · rw [regs']; exact fin sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [mem']; unfold parseMem; rw [hpe]; dsimp only
      exact memStore8_congr (memStore8_congr (hO x hx))
  -- 0x0E to 0x22: the reader over the 40 bytes at `bp`, position 0, and the magic.
  have cd2 := pcode M2 M2out
  obtain ⟨m5, e5, t5⟩ := t4.alu cd2.parse pa_e (off' := 0x10) (by decide)
  obtain ⟨m6, e6, t6⟩ := t5.aluImm cd2.parse pa_10 (off' := 0x14) (by decide)
  have q6 : reg m6 sp = G ∧ reg m6 a0 = 40 ∧ reg m6 a1 = bp ∧ reg m6 s0 = out := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp +decide [t6.regs, upd, aluEval, ha0, ha1]
  obtain ⟨q6sp, q6a0, q6a1, q6s0⟩ := q6
  have hz6 : reg m6 x0 = 0 := t6.self.zero
  obtain ⟨m7, e7, t7⟩ := t6.self.sw cd2.parse pa_14 (off' := 0x16) (by decide)
    (by rw [q6sp]; exact aligned_add hG (k := 8) (by decide))
  rw [q6sp, q6a1] at t7
  have c7 := pcode _ (outSt M2 8 bp (by omega) M2out)
  obtain ⟨m8, e8, t8⟩ := t7.sw c7.parse pa_16 (off' := 0x18) (by decide)
    (by rw [q6sp]; exact aligned_add hG (k := 0x0C) (by decide))
  rw [q6sp, q6a0] at t8
  have c8 := pcode _ (outSt _ 0x0C 40 (by omega) (outSt M2 8 bp (by omega) M2out))
  obtain ⟨m9, e9, t9⟩ := t8.sw c8.parse pa_18 (off' := 0x1A) (by decide)
    (by rw [q6sp]; exact aligned_add hG (k := 0x10) (by decide))
  rw [q6sp, hz6] at t9
  obtain ⟨M3, hM3⟩ : ∃ M3, memStore32 (memStore32 (memStore32 M2 (G + 8) bp) (G + 0x0C) 40) (G + 0x10) 0 = M3 :=
    ⟨_, rfl⟩
  rw [hM3] at t9
  have M3out : ∀ x, Sep R 144 x 1 → M3 x = m.mem x := by
    rw [← hM3]; exact outSt _ 0x10 _ (by omega) (outSt _ 0x0C 40 (by omega) (outSt M2 8 bp (by omega) M2out))
  have c3 := pcode M3 M3out
  obtain ⟨m10, e10, t10⟩ := t9.lui c3.parse pa_1a (off' := 0x1E) (by decide)
  obtain ⟨m11, e11, t11⟩ := t10.aluImm c3.parse pa_1e (off' := 0x22) (by decide)
  obtain ⟨m12, e12, t12⟩ := t11.aluImm c3.parse pa_22 (off' := 0x24) (by decide)
  have so : ∀ c d, c < 64 → d < 64 → c + 4 ≤ d ∨ d + 4 ≤ c →
      Sep (G + BitVec.ofNat 32 c) 4 (G + BitVec.ofNat 32 d) 4 :=
    fun c d hc hd h => sep_offsets G h (by omega) (by omega)
  have M3rd : memLoad32 M3 (G + 8) = bp ∧ memLoad32 M3 (G + 8 + 4) = 40 ∧ memLoad32 M3 (G + 8 + 8) = 0 := by
    rw [← hM3, g8_eq, show G + 8 + 8 = G + 0x10 from by rw [BitVec.add_assoc]; rfl]
    refine ⟨?_, ?_, memLoad32_store32_same _ _ _⟩
    · rw [memLoad32_store32_sep (show Sep (G + 0x10) 4 (G + 8) 4 from so 16 8 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x0C) 4 (G + 8) 4 from so 12 8 (by omega) (by omega) (by omega)),
        memLoad32_store32_same]
    · rw [memLoad32_store32_sep (show Sep (G + 0x10) 4 (G + 12) 4 from so 16 12 (by omega) (by omega) (by omega)),
        memLoad32_store32_same]
  have M3sl : ∀ k, 0x20 ≤ k → k < 0x40 → M3 (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k) :=
    fun k h1 h2 => by
      rw [← hM3]
      have g : ∀ c, c + 4 ≤ 0x20 → Sep (G + BitVec.ofNat 32 c) 4 (G + BitVec.ofNat 32 k) 1 := fun c hc =>
        sep_offsets G (by omega) (by omega) (by omega)
      rw [memStore32_get_sep (show Sep (G + 0x10) 4 _ 1 from g 16 (by omega)),
        memStore32_get_sep (show Sep (G + 0x0C) 4 _ 1 from g 12 (by omega)),
        memStore32_get_sep (show Sep (G + 8) 4 _ 1 from g 8 (by omega))]
  have q12 : reg m12 sp = G ∧ reg m12 a0 = G + 8 ∧ reg m12 a1 = 0x4C533343 ∧ reg m12 s0 = out ∧
      ∀ r, r ∉ parseClob → reg m12 r = reg m r := by
    refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_⟩
    · simp +decide [t12.regs, upd, q6sp]
    · simp +decide [t12.regs, upd, aluEval, q6sp]
    · simp +decide [t12.regs, upd, aluEval]
    · simp +decide [t12.regs, upd, q6s0]
    · rw [t12.regs]
      refine keep_upd' (keep_upd' (keep_upd' (fun r hr => ?_) hz (by decide)) hz (by decide)) hz (by decide) r hr
      rw [t6.regs]
      exact keep_upd' (keep_upd' (keep_upd' (keep_upd' (fun _ _ => rfl) hz (by decide)) hz (by decide)) hz
        (by decide)) hz (by decide) r hr
  obtain ⟨q12sp, q12a0, q12a1, q12s0, keep12⟩ := q12
  -- 0x24: `Reader::magic`.
  obtain ⟨m13, c13, t13, sp13, a013, fr13, mem13⟩ := parse_magic env t12.self c3 pa_24 pa_28
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x24 + 8) (by decide))
    q12sp q12a0 q12a1 M3rd.1 M3rd.2.1
  have bufLd : ∀ Mx : Word → BitVec 8, (∀ x, Sep R 144 x 1 → Mx x = m.mem x) → ∀ i, i + 4 ≤ 40 →
      memLoad32 Mx (bp + BitVec.ofNat 32 i) = mw m.mem bp i := fun Mx h i hi =>
    memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact h _ (env.hBS.sub (c := i + j) (l := 1) (by omega)).symm
  have bufB : ∀ Mx : Word → BitVec 8, (∀ x, Sep R 144 x 1 → Mx x = m.mem x) → ∀ i, i < 40 →
      Mx (bp + BitVec.ofNat 32 i) = m.mem (bp + BitVec.ofNat 32 i) := fun Mx h i hi =>
    h _ (env.hBS.sub (c := i) (l := 1) (by omega)).symm
  have hmag : reg m13 a0 = if mw m.mem bp 0 == 0x4C533343 then 0xFFFFFFFF else 2 := by
    rw [a013]; unfold magicResult; rw [M3rd.1, M3rd.2.1, M3rd.2.2,
      show bytesResult bp 40 0 4 = some (bp + 0, 0 + 4) from rfl]; dsimp only
    rw [show memLoad32 M3 (bp + 0) = mw m.mem bp 0 from bufLd M3 M3out 0 (by omega)]
  obtain ⟨r13p, r13l, r13q, O13, S13⟩ := env.advance (c := 32) (N := 48) (My := m13.mem) (e := 4) (by omega)
    M3rd.1 M3rd.2.1 M3out M3sl (fun x hx => by
      rw [mem13 x (by rw [e32]; exact hx)]; unfold magicMem
      rw [M3rd.1, M3rd.2.1, M3rd.2.2, show bytesResult bp 40 0 4 = some (bp + 0, 4) from rfl])
  have keep13 : ∀ r, r ∉ parseClob → reg m13 r = reg m r := fun r hr => by
    have n : ∀ q, q ∈ parseClob → r ≠ q := fun q hq e => hr (e ▸ hq)
    rw [fr13 r (n a0 (by decide)) (n a1 (by decide)) (n a2 (by decide)) (n a3 (by decide)) (n a4 (by decide))
      (n a5 (by decide)) (n t0 (by decide)) (n ra (by decide))]
    exact keep12 r hr
  have s13 : reg m13 s0 = out := by
    rw [fr13 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact q12s0
  have pre13 : Steps m m13 := .cons e1 (c2.trans (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8
    (.cons e9 (.cons e10 (.cons e11 (.cons e12 c13)))))))))))
  obtain ⟨m14, g14, c14, fg14, hb14⟩ := check_branch t13 (pcode _ O13).parse pa_2c pa_30 pa_34 (by decide)
  rcases hb14 with ⟨hok, t14⟩ | ⟨hbad, t14⟩
  · have hm0 : (mw m.mem bp 0 == 0x4C533343) = true := by
      cases hc : (mw m.mem bp 0 == 0x4C533343)
      · rw [hmag, hc] at hok; exact absurd hok (by decide)
      · rfl
    -- 0x36: `Reader::version_1`.
    have cd13 := pcode _ O13
    obtain ⟨m15, e15, t15⟩ := t14.aluImm cd13.parse pa_36 (off' := 0x38) (by decide)
    have g14sp : g14 sp = G := by rw [fg14 sp (by decide), sp13]
    obtain ⟨m16, c16, t16, sp16, a016, fr16, mem16⟩ := parse_version env t15.self cd13 pa_38 pa_3c
      (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x38 + 8) (by decide))
      (by rw [t15.regs]; simp +decide [upd, g14sp]) (by rw [t15.regs]; simp +decide [upd, aluEval, g14sp])
      r13p r13l
    have hver : reg m16 a0 =
        if ((m.mem (bp + 5)).zeroExtend 32 <<< 24 ||| (m.mem (bp + 4)).zeroExtend 32 <<< 16 : Word) >>> 16 == 1
        then 0xFFFFFFFF else 3 := by
      rw [a016]; exact version_val r13p r13l r13q (bufB _ O13 4 (by omega)) (bufB _ O13 5 (by omega))
    obtain ⟨r16p, r16l, r16q, O16, S16⟩ := env.advance (My := m16.mem) (c := 48) (N := 32) (e := 6) (by omega)
      r13p r13l O13 S13 (fun x hx => by
        rw [mem16 x (by rw [e48]; exact hx)]; exact u16Mem_val r13p r13l r13q x)
    have keep16 : ∀ r, r ∉ parseClob → reg m16 r = reg m r := fun r hr => by
      have n : ∀ q, q ∈ parseClob → r ≠ q := fun q hq e => hr (e ▸ hq)
      rw [fr16 r (n a0 (by decide)) (n a1 (by decide)) (n a2 (by decide)) (n a3 (by decide)) (n a4 (by decide))
        (n a5 (by decide)) (n ra (by decide)), t15.regs]
      exact keep_upd' (fun r hr => by
        rw [fg14 r (fun e => hr (e ▸ by decide))]; exact keep13 r hr) hz (by decide) r hr
    have s16 : reg m16 s0 = out := by
      rw [fr16 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), t15.regs,
        upd_ne (by decide) (by decide), fg14 s0 (by decide), s13]
    have pre16 : Steps m m16 := pre13.trans (c14.trans (.cons e15 c16))
    obtain ⟨m17, g17, c17, fg17, hb17⟩ := check_branch t16 (pcode _ O16).parse pa_40 pa_44 pa_48 (by decide)
    have hverC : ∀ b : Bool,
        (((m.mem (bp + 5)).zeroExtend 32 <<< 24 ||| (m.mem (bp + 4)).zeroExtend 32 <<< 16 : Word) >>> 16 == 1) = b →
        reg m16 a0 = if b then 0xFFFFFFFF else 3 := fun b h => by rw [hver, h]
    rcases hb17 with ⟨hok, t17⟩ | ⟨hbad, t17⟩
    · have hv0 : (((m.mem (bp + 5)).zeroExtend 32 <<< 24 ||| (m.mem (bp + 4)).zeroExtend 32 <<< 16 : Word) >>> 16
          == 1) = true := by
        cases hc : (((m.mem (bp + 5)).zeroExtend 32 <<< 24 ||| (m.mem (bp + 4)).zeroExtend 32 <<< 16 : Word) >>> 16
          == 1)
        · rw [hverC false hc] at hok; exact absurd hok (by decide)
        · rfl
      -- 0x4A: `Reader::reserved(2)`.
      have cd16 := pcode _ O16
      have g17sp : g17 sp = G := by rw [fg17 sp (by decide), sp16]
      obtain ⟨m18, e18, t18⟩ := t17.aluImm cd16.parse pa_4a (off' := 0x4C) (by decide)
      obtain ⟨m19, e19, t19⟩ := t18.aluImm cd16.parse pa_4c (off' := 0x4E) (by decide)
      obtain ⟨m20, c20, t20, sp20, a020, fr20, mem20⟩ := parse_reserved env t19.self cd16 pa_4e pa_52
        (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x4E + 8) (by decide))
        (by rw [t19.regs]; simp +decide [upd, g17sp]) (by rw [t19.regs]; simp +decide [upd, aluEval, g17sp])
        (by rw [t19.regs]; simp +decide [upd, aluEval])
        r16p r16l
      have hres : reg m20 a0 = if allZero m.mem (bp + 6) 2 then 0xFF else 4 := by
        rw [a020]; exact reserved_val r16p r16l r16q (allZero_congr 2 (bp + 6) fun i hi => by
          rw [show bp + 6 + BitVec.ofNat 32 i = bp + BitVec.ofNat 32 (6 + i) from add_ofNat_assoc bp 6 i]
          exact bufB _ O16 (6 + i) (by omega))
      obtain ⟨r20p, r20l, r20q, O20, S20⟩ := env.advance (My := m20.mem) (c := 64) (N := 16) (e := 8)
        (by omega) r16p r16l O16 S16 (fun x hx => by
          rw [mem20 x (by rw [e64]; exact hx)]; exact reservedMem_val r16p r16l r16q x)
      have keep20 : ∀ r, r ∉ parseClob → reg m20 r = reg m r := fun r hr => by
        have n : ∀ q, q ∈ parseClob → r ≠ q := fun q hq e => hr (e ▸ hq)
        rw [fr20 r (n a0 (by decide)) (n a1 (by decide)) (n a2 (by decide)) (n a3 (by decide)) (n a4 (by decide))
          (n a5 (by decide)) (n ra (by decide)), t19.regs]
        exact keep_upd' (keep_upd' (fun r hr => by
          rw [fg17 r (fun e => hr (e ▸ by decide))]; exact keep16 r hr) hz (by decide)) hz (by decide) r hr
      have s20 : reg m20 s0 = out := by
        rw [fr20 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), t19.regs]
        simp +decide only [upd, ite_false]; rw [fg17 s0 (by decide), s16]
      have pre20 : Steps m m20 := pre16.trans (c17.trans (.cons e18 (.cons e19 c20)))
      obtain ⟨m21, g21, c21, fg21, hb21⟩ := check_branch t20 (pcode _ O20).parse pa_56 pa_5a pa_5e (by decide)
      rcases hb21 with ⟨hok, t21⟩ | ⟨hbad, t21⟩
      · have hr0 : allZero m.mem (bp + 6) 2 = true := by
          cases hc : allZero m.mem (bp + 6) 2
          · rw [hres, hc] at hok; exact absurd hok (by decide)
          · rfl
        -- From here on, a part that is out of range ends at 0xCE.
        have partErrExit : ∀ (n : Machine) (Mx : Word → BitVec 8) (g : Fin 32 → Word),
            Steps m n → St Mx P n 0xCE g → g sp = G → g s0 = out → Mx (G + 0x15) = 5 →
            parseErr m.mem bp = some 5 → (∀ x, Sep R 144 x 1 → Mx x = m.mem x) →
            (∀ k, 0x20 ≤ k → k < 0x40 → Mx (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k)) →
            (∀ r, r ∉ parseClob → g r = reg m r) →
            ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
              (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → reg m' r = reg m r) ∧
              ∀ x, Sep R 144 x 1 → m'.mem x = parseMem m.mem out bp x := by
          intro n Mx g hn s hsp hs0 h5 hpe hO hS hk
          obtain ⟨n1, d1, u1⟩ := s.lbu (pcode Mx hO).parse pa_ce (off' := 0xD2) (by decide)
          rw [hsp, show G + 0x15 = G + 0x15 from rfl, h5] at u1
          exact errExit n1 Mx _ 5 (hn.trans (.single d1)) u1 (by simp +decide [upd, hsp])
            (by simp +decide [upd, hs0]) (by simp +decide [upd]) hpe hO hS
            (keep_upd' hk hz (by decide))
        -- 0x60: `part` for the image, at position 8.
        have cd20 := pcode _ O20
        have g21sp : g21 sp = G := by rw [fg21 sp (by decide), sp20]
        have keep21 : ∀ r, r ∉ parseClob → g21 r = reg m r := fun r hr => by
          rw [fg21 r (fun e => hr (e ▸ by decide))]; exact keep20 r hr
        have g21s0 : g21 s0 = out := by rw [fg21 s0 (by decide), s20]
        obtain ⟨m22, e22, t22⟩ := t21.aluImm cd20.parse pa_60 (off' := 0x62) (by decide)
        obtain ⟨m23, e23, t23⟩ := t22.aluImm cd20.parse pa_62 (off' := 0x64) (by decide)
        obtain ⟨m24, e24, t24⟩ := t23.aluImm cd20.parse pa_64 (off' := 0x68) (by decide)
        obtain ⟨m25, e25, t25⟩ := t24.lui cd20.parse pa_68 (off' := 0x6C) (by decide)
        obtain ⟨m26, My26, c26, t26, sp26, fr26, O26, S26, h26⟩ := env.part_step (M0 := m.mem) (M2 := M2) (lo := 37) (hi := 0x1D0000) 8
          (by omega) t25 pa_6c pa_70 pa_74 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
          (even_at P env.hP (0x6C + 8) (by decide))
          (by simp +decide [upd, g21sp]) (by simp +decide [upd, aluEval, g21sp])
          (by simp +decide [upd, aluEval, g21sp]) (by simp +decide [upd, aluEval]) (by simp +decide [upd])
          r20p r20l r20q O20 S20 pcode
        have keep26 : ∀ r, r ∉ parseClob → reg m26 r = reg m r := fun r hr => by
          have n : ∀ q, q ∈ parseClob → r ≠ q := fun q hq e => hr (e ▸ hq)
          rw [fr26 r (n a0 (by decide)) (n a1 (by decide)) (n a2 (by decide)) (n a3 (by decide))
            (n a4 (by decide)) (n a5 (by decide)) (n t0 (by decide)) (n ra (by decide))]
          exact keep_upd' (keep_upd' (keep_upd' (keep_upd' keep21 hz (by decide)) hz (by decide)) hz
            (by decide)) hz (by decide) r hr
        have s26 : reg m26 s0 = out := by
          rw [fr26 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide)]
          simp +decide only [upd, ite_false]; exact g21s0
        have pre26 : Steps m m26 := pre20.trans (c21.trans (.cons e22 (.cons e23 (.cons e24 (.cons e25 c26)))))
        have z26 : reg m26 x0 = 0 := t26.zero
        simp only [Nat.reduceAdd] at h26
        cases hp1 : partOut 37 0x1D0000 (mw m.mem bp 12)
        · simp only [hp1, Bool.false_eq_true, ite_false] at h26
          obtain ⟨tag, r26p, r26l, r26q, w8, w12⟩ := h26
          obtain ⟨m27, e27, t27⟩ := t26.notTaken (pcode _ O26).parse 0x7A pa_78 (by decide)
            (by rw [tag, z26]; decide)
          -- 0x7A: the image's offset and length to `s1` and `s6`.
          have cd26 := pcode _ O26
          have t27' : St My26 P m27 0x7A (reg m26) := t27
          obtain ⟨m28, e28, t28⟩ := t27'.lw cd26.parse pa_7a (off' := 0x7C) (by decide)
            (by rw [sp26]; exact aligned_add hG (k := 0x18) (by decide))
          have q28sp : reg m28 sp = G := by rw [t28.regs, upd_ne (by decide) (by decide), sp26]
          have q28s1 : reg m28 s1 = mw m.mem bp 8 := by rw [t28.regs, upd_same (by decide), sp26]; exact w8
          obtain ⟨m29, e29, t29⟩ := t28.self.lw cd26.parse pa_7c (off' := 0x7E) (by decide)
            (by rw [q28sp]; exact aligned_add hG (k := 0x1C) (by decide))
          have q29 : reg m29 sp = G ∧ reg m29 s0 = out ∧ reg m29 s1 = mw m.mem bp 8 ∧
              reg m29 s6 = mw m.mem bp 12 ∧ ∀ r, r ∉ parseClob → reg m29 r = reg m r := by
            refine ⟨by rw [t29.regs, upd_ne (by decide) (by decide), q28sp],
              by rw [t29.regs, upd_ne (by decide) (by decide), t28.regs, upd_ne (by decide) (by decide), s26],
              by rw [t29.regs, upd_ne (by decide) (by decide), q28s1],
              by rw [t29.regs, upd_same (by decide), q28sp]; exact w12, fun r hr => ?_⟩
            rw [t29.regs]
            exact keep_upd' (fun r hr => by rw [t28.regs]; exact keep_upd' keep26 hz (by decide) r hr) hz
              (by decide) r hr
          obtain ⟨q29sp, q29s0, q29s1, q29s6, keep29⟩ := q29
          -- 0x7E: `part` for the bundle, at position 16.
          obtain ⟨m30, e30, t30⟩ := t29.self.aluImm cd26.parse pa_7e (off' := 0x80) (by decide)
          obtain ⟨m31, e31, t31⟩ := t30.aluImm cd26.parse pa_80 (off' := 0x82) (by decide)
          obtain ⟨m32, e32', t32⟩ := t31.aluImm cd26.parse pa_82 (off' := 0x86) (by decide)
          obtain ⟨m33, e33, t33⟩ := t32.lui cd26.parse pa_86 (off' := 0x88) (by decide)
          obtain ⟨m34, My34, c34, t34, sp34, fr34, O34, S34, h34⟩ := env.part_step (M0 := m.mem) (M2 := M2)
            (lo := 49) (hi := 0x4000) 16 (by omega) t33 pa_88 pa_8c pa_90
            (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x88 + 8) (by decide))
            (by simp +decide [upd, q29sp]) (by simp +decide [upd, aluEval, q29sp])
            (by simp +decide [upd, aluEval, q29sp]) (by simp +decide [upd, aluEval])
            (by simp +decide [upd]) r26p r26l r26q O26 S26 pcode
          have fr34' : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → r ≠ ra →
              reg m34 r = reg m29 r := fun r h0 h1' h2' h3' h4 h5 h6 h7 => by
            rw [fr34 r h0 h1' h2' h3' h4 h5 h6 h7]
            by_cases hr : r.val = 0
            · have : r = 0 := Fin.ext hr
              subst this; simp [upd]; exact t29.self.zero.symm
            · simp [upd, hr, h0, h1', h2', h3']
          have keep34 : ∀ r, r ∉ parseClob → reg m34 r = reg m r := fun r hr => by
            have n : ∀ q, q ∈ parseClob → r ≠ q := fun q hq e => hr (e ▸ hq)
            rw [fr34' r (n a0 (by decide)) (n a1 (by decide)) (n a2 (by decide)) (n a3 (by decide))
              (n a4 (by decide)) (n a5 (by decide)) (n t0 (by decide)) (n ra (by decide))]
            exact keep29 r hr
          have s34 : reg m34 s0 = out := by
            rw [fr34' s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide)]; exact q29s0
          have pre34 : Steps m m34 := pre26.trans (.cons e27 (.cons e28 (.cons e29 (.cons e30 (.cons e31
            (.cons e32' (.cons e33 c34)))))))
          have z34 : reg m34 x0 = 0 := t34.zero
          simp only [Nat.reduceAdd] at h34
          cases hp2 : partOut 49 0x4000 (mw m.mem bp 20)
          · simp only [hp2, Bool.false_eq_true, ite_false] at h34
            obtain ⟨tag2, r34p, r34l, r34q, w16, w20⟩ := h34
            obtain ⟨m35, e35, t35⟩ := t34.notTaken (pcode _ O34).parse 0x96 pa_94 (by decide)
              (by rw [tag2, z34]; decide)
            -- 0x96: the bundle's offset and length to `s2` and `s3`.
            have cd34 := pcode _ O34
            have t35' : St My34 P m35 0x96 (reg m34) := t35
            obtain ⟨m36, e36, t36⟩ := t35'.lw cd34.parse pa_96 (off' := 0x98) (by decide)
              (by rw [sp34]; exact aligned_add hG (k := 0x18) (by decide))
            have q36sp : reg m36 sp = G := by rw [t36.regs, upd_ne (by decide) (by decide), sp34]
            have q36s2 : reg m36 s2 = mw m.mem bp 16 := by rw [t36.regs, upd_same (by decide), sp34]; exact w16
            obtain ⟨m37, e37, t37⟩ := t36.self.lw cd34.parse pa_98 (off' := 0x9A) (by decide)
              (by rw [q36sp]; exact aligned_add hG (k := 0x1C) (by decide))
            have v34 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → r ≠ ra →
                r ≠ s2 → r ≠ s3 → reg m37 r = reg m29 r := fun r h0 h1' h2' h3' h4 h5 h6 h7 h8 h9 => by
              by_cases hr : r.val = 0
              · have : r = 0 := Fin.ext hr
                subst this; exact t37.self.zero.trans t29.self.zero.symm
              · rw [t37.regs, upd_ne hr h9, t36.regs, upd_ne hr h8]
                exact fr34' r h0 h1' h2' h3' h4 h5 h6 h7
            have q37 : reg m37 sp = G ∧ reg m37 s0 = out ∧ reg m37 s1 = mw m.mem bp 8 ∧
                reg m37 s6 = mw m.mem bp 12 ∧ reg m37 s2 = mw m.mem bp 16 ∧ reg m37 s3 = mw m.mem bp 20 ∧
                ∀ r, r ∉ parseClob → reg m37 r = reg m r := by
              refine ⟨by rw [t37.regs, upd_ne (by decide) (by decide), q36sp],
                by rw [v34 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide)]; exact q29s0,
                by rw [v34 s1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide)]; exact q29s1,
                by rw [v34 s6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide)]; exact q29s6,
                by rw [t37.regs, upd_ne (by decide) (by decide), q36s2],
                by rw [t37.regs, upd_same (by decide), q36sp]; exact w20, fun r hr => ?_⟩
              have n : ∀ q, q ∈ parseClob → r ≠ q := fun q hq e => hr (e ▸ hq)
              rw [v34 r (n a0 (by decide)) (n a1 (by decide)) (n a2 (by decide)) (n a3 (by decide))
                (n a4 (by decide)) (n a5 (by decide)) (n t0 (by decide)) (n ra (by decide)) (n s2 (by decide))
                (n s3 (by decide))]
              exact keep29 r hr
            obtain ⟨q37sp, q37s0, q37s1, q37s6, q37s2, q37s3, keep37⟩ := q37
            -- 0x9A: `part` for the chain, at position 24.
            obtain ⟨m38, e38, t38⟩ := t37.self.aluImm cd34.parse pa_9a (off' := 0x9C) (by decide)
            obtain ⟨m39, e39, t39⟩ := t38.aluImm cd34.parse pa_9c (off' := 0x9E) (by decide)
            obtain ⟨m40, e40, t40⟩ := t39.aluImm cd34.parse pa_9e (off' := 0xA0) (by decide)
            obtain ⟨m41, e41, t41⟩ := t40.aluImm cd34.parse pa_a0 (off' := 0xA2) (by decide)
            obtain ⟨m42, e42, t42⟩ := t41.aluImm cd34.parse pa_a2 (off' := 0xA4) (by decide)
            obtain ⟨m43, My43, c43, t43, sp43, fr43, O43, S43, h43⟩ := env.part_step (M0 := m.mem) (M2 := M2)
              (lo := 8) (hi := 0x800) 24 (by omega) t42 pa_a4 pa_a8 pa_ac
              (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0xA4 + 8) (by decide))
              (by simp +decide [upd, q37sp]) (by simp +decide [upd, aluEval, q37sp])
              (by simp +decide [upd, aluEval, q37sp]) (by simp +decide [upd, aluEval])
              (by have := t37.self.zero; simp +decide [upd, aluEval, this]) r34p r34l r34q O34 S34 pcode
            have fr43' : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → r ≠ ra →
                reg m43 r = reg m37 r := fun r h0 h1' h2' h3' h4 h5 h6 h7 => by
              rw [fr43 r h0 h1' h2' h3' h4 h5 h6 h7]
              by_cases hr : r.val = 0
              · have : r = 0 := Fin.ext hr
                subst this; simp [upd]; exact t37.self.zero.symm
              · simp [upd, hr, h0, h1', h2', h3']
            have keep43 : ∀ r, r ∉ parseClob → reg m43 r = reg m r := fun r hr => by
              have n : ∀ q, q ∈ parseClob → r ≠ q := fun q hq e => hr (e ▸ hq)
              rw [fr43' r (n a0 (by decide)) (n a1 (by decide)) (n a2 (by decide)) (n a3 (by decide))
                (n a4 (by decide)) (n a5 (by decide)) (n t0 (by decide)) (n ra (by decide))]
              exact keep37 r hr
            have s43 : reg m43 s0 = out := by
              rw [fr43' s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide)]; exact q37s0
            have pre43 : Steps m m43 := pre34.trans (.cons e35 (.cons e36 (.cons e37 (.cons e38 (.cons e39
              (.cons e40 (.cons e41 (.cons e42 c43))))))))
            have z43 : reg m43 x0 = 0 := t43.zero
            simp only [Nat.reduceAdd] at h43
            cases hp3 : partOut 8 0x800 (mw m.mem bp 28)
            · simp only [hp3, Bool.false_eq_true, ite_false] at h43
              obtain ⟨tag3, r43p, r43l, r43q, w24, w28⟩ := h43
              obtain ⟨m44, e44, t44⟩ := t43.notTaken (pcode _ O43).parse 0xB2 pa_b0 (by decide)
                (by rw [tag3, z43]; decide)
              -- 0xB2: the chain's offset and length to `s4` and `s5`.
              have cd43 := pcode _ O43
              have t44' : St My43 P m44 0xB2 (reg m43) := t44
              obtain ⟨m45, e45, t45⟩ := t44'.lw cd43.parse pa_b2 (off' := 0xB4) (by decide)
                (by rw [sp43]; exact aligned_add hG (k := 0x18) (by decide))
              have q45sp : reg m45 sp = G := by rw [t45.regs, upd_ne (by decide) (by decide), sp43]
              have q45s4 : reg m45 s4 = mw m.mem bp 24 := by rw [t45.regs, upd_same (by decide), sp43]; exact w24
              obtain ⟨m46, e46, t46⟩ := t45.self.lw cd43.parse pa_b4 (off' := 0xB6) (by decide)
                (by rw [q45sp]; exact aligned_add hG (k := 0x1C) (by decide))
              have v43 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → r ≠ ra →
                  r ≠ s4 → r ≠ s5 → reg m46 r = reg m37 r := fun r h0 h1' h2' h3' h4 h5 h6 h7 h8 h9 => by
                by_cases hr : r.val = 0
                · have : r = 0 := Fin.ext hr
                  subst this; exact t46.self.zero.trans t37.self.zero.symm
                · rw [t46.regs, upd_ne hr h9, t45.regs, upd_ne hr h8]
                  exact fr43' r h0 h1' h2' h3' h4 h5 h6 h7
              have q46 : reg m46 sp = G ∧ reg m46 s0 = out ∧ reg m46 s1 = mw m.mem bp 8 ∧
                  reg m46 s6 = mw m.mem bp 12 ∧ reg m46 s2 = mw m.mem bp 16 ∧ reg m46 s3 = mw m.mem bp 20 ∧
                  reg m46 s4 = mw m.mem bp 24 ∧ reg m46 s5 = mw m.mem bp 28 ∧
                  ∀ r, r ∉ parseClob → reg m46 r = reg m r := by
                have v : ∀ r, r ∈ [s0, s1, s6, s2, s3] → reg m46 r = reg m37 r := fun r hr => by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
                    exact v43 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                      (by decide) (by decide) (by decide) (by decide)
                refine ⟨by rw [t46.regs, upd_ne (by decide) (by decide), q45sp],
                  by rw [v s0 (by decide)]; exact q37s0, by rw [v s1 (by decide)]; exact q37s1,
                  by rw [v s6 (by decide)]; exact q37s6, by rw [v s2 (by decide)]; exact q37s2,
                  by rw [v s3 (by decide)]; exact q37s3,
                  by rw [t46.regs, upd_ne (by decide) (by decide), q45s4],
                  by rw [t46.regs, upd_same (by decide), q45sp]; exact w28, fun r hr => ?_⟩
                have n : ∀ q, q ∈ parseClob → r ≠ q := fun q hq e => hr (e ▸ hq)
                rw [v43 r (n a0 (by decide)) (n a1 (by decide)) (n a2 (by decide)) (n a3 (by decide))
                  (n a4 (by decide)) (n a5 (by decide)) (n t0 (by decide)) (n ra (by decide)) (n s4 (by decide))
                  (n s5 (by decide))]
                exact keep37 r hr
              obtain ⟨q46sp, q46s0, q46s1, q46s6, q46s2, q46s3, q46s4, q46s5, keep46⟩ := q46
              -- 0xB6: `part` for the blob, at position 32.
              obtain ⟨m47, e47, t47⟩ := t46.self.aluImm cd43.parse pa_b6 (off' := 0xB8) (by decide)
              obtain ⟨m48, e48', t48⟩ := t47.aluImm cd43.parse pa_b8 (off' := 0xBA) (by decide)
              obtain ⟨m49, e49, t49⟩ := t48.aluImm cd43.parse pa_ba (off' := 0xBE) (by decide)
              obtain ⟨m50, e50, t50⟩ := t49.lui cd43.parse pa_be (off' := 0xC0) (by decide)
              obtain ⟨m51, My51, c51, t51, sp51, fr51, O51, S51, h51⟩ := env.part_step (M0 := m.mem) (M2 := M2)
                (lo := 443) (hi := 0x1000) 32 (by omega) t50 pa_c0 pa_c4 pa_c8
                (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0xC0 + 8) (by decide))
                (by simp +decide [upd, q46sp]) (by simp +decide [upd, aluEval, q46sp])
                (by simp +decide [upd, aluEval, q46sp]) (by simp +decide [upd, aluEval])
                (by simp +decide [upd]) r43p r43l r43q O43 S43 pcode
              have fr51' : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 → r ≠ ra →
                  reg m51 r = reg m46 r := fun r h0 h1' h2' h3' h4 h5 h6 h7 => by
                rw [fr51 r h0 h1' h2' h3' h4 h5 h6 h7]
                by_cases hr : r.val = 0
                · have : r = 0 := Fin.ext hr
                  subst this; simp [upd]; exact t46.self.zero.symm
                · simp [upd, hr, h0, h1', h2', h3']
              have keep51 : ∀ r, r ∉ parseClob → reg m51 r = reg m r := fun r hr => by
                have n : ∀ q, q ∈ parseClob → r ≠ q := fun q hq e => hr (e ▸ hq)
                rw [fr51' r (n a0 (by decide)) (n a1 (by decide)) (n a2 (by decide)) (n a3 (by decide))
                  (n a4 (by decide)) (n a5 (by decide)) (n t0 (by decide)) (n ra (by decide))]
                exact keep46 r hr
              have s51 : reg m51 s0 = out := by
                rw [fr51' s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                  (by decide)]; exact q46s0
              have pre51 : Steps m m51 := pre43.trans (.cons e44 (.cons e45 (.cons e46 (.cons e47 (.cons e48'
                (.cons e49 (.cons e50 c51)))))))
              have z51 : reg m51 x0 = 0 := t51.zero
              simp only [Nat.reduceAdd] at h51
              cases hp4 : partOut 443 0x1000 (mw m.mem bp 36)
              · simp only [hp4, Bool.false_eq_true, ite_false] at h51
                obtain ⟨tag4, r51p, r51l, r51q, w32, w36⟩ := h51
                obtain ⟨m52, e52, t52⟩ := t51.taken (pcode _ O51).parse 0xEC pa_cc (by decide)
                  (by rw [tag4, z51]; decide)
                -- 0xEC: the layout checks.
                have cd51 := pcode _ O51
                have v51 : reg m51 s1 = mw m.mem bp 8 ∧ reg m51 s6 = mw m.mem bp 12 ∧
                    reg m51 s2 = mw m.mem bp 16 ∧ reg m51 s3 = mw m.mem bp 20 ∧
                    reg m51 s4 = mw m.mem bp 24 ∧ reg m51 s5 = mw m.mem bp 28 := by
                  have f : ∀ r, r ∈ [s1, s6, s2, s3, s4, s5] → reg m51 r = reg m46 r := fun r hr => by
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
                      exact fr51' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                        (by decide) (by decide)
                  exact ⟨(f s1 (by decide)).trans q46s1, (f s6 (by decide)).trans q46s6,
                    (f s2 (by decide)).trans q46s2, (f s3 (by decide)).trans q46s3,
                    (f s4 (by decide)).trans q46s4, (f s5 (by decide)).trans q46s5⟩
                obtain ⟨v1, v6, v2, v3, v4, v5⟩ := v51
                have e7Exit : ∀ (n : Machine) (g : Fin 32 → Word), Steps m n → St My51 P n 0x15E g →
                    g sp = G → g s0 = out → (∀ r, r ∉ parseClob → g r = reg m r) →
                    parseErr m.mem bp = some 7 →
                    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
                      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 →
                        reg m' r = reg m r) ∧
                      ∀ x, Sep R 144 x 1 → m'.mem x = parseMem m.mem out bp x := by
                  intro n g hn s hsp hs0 hk hpe
                  have hz' := s.zero
                  obtain ⟨n1, d1, u1⟩ := s.aluImm cd51.parse pa_15e (off' := 0x160) (by decide)
                  obtain ⟨n2, d2, u2⟩ := u1.jump cd51.parse pa_160 (off' := 0xD2) (by decide)
                    (by rw [u1.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0xD2 (by decide)))
                  exact errExit n2 My51 _ 7 (hn.trans (.cons d1 (.single d2))) u2 (by simp +decide [upd, hsp])
                    (by simp +decide [upd, hs0]) (by simp +decide [upd, aluEval, hz']) hpe O51 S51
                    (keep_upd' hk hz (by decide))
                have t52' : St My51 P m52 0xEC (reg m51) := t52
                obtain ⟨m53, e53, t53⟩ := t52'.lw cd51.parse pa_ec (off' := 0xEE) (by decide)
                  (by rw [sp51]; exact aligned_add hG (k := 0x0C) (by decide))
                obtain ⟨m54, e54, t54⟩ := t53.lw cd51.parse pa_ee (off' := 0xF0) (by decide)
                  (by simp +decide only [upd, sp51, ite_false]; exact aligned_add hG (k := 0x10) (by decide))
                obtain ⟨m55, e55, t55⟩ := t54.notTaken cd51.parse 0xF4 pa_f0 (by decide) (by
                  simp +decide only [upd, sp51, ite_false, ite_true]
                  rw [show G + 0x10 = G + 8 + 8 from by rw [BitVec.add_assoc]; rfl, r51q,
                    show G + 0x0C = G + 8 + 4 from by rw [BitVec.add_assoc]; rfl, r51l]; decide)
                obtain ⟨m56, e56, t56⟩ := t55.lui cd51.parse pa_f4 (off' := 0xF6) (by decide)
                have keep56 : ∀ r, r ∉ parseClob → upd (upd (upd (reg m51) a0 (memLoad32 My51 (reg m51 sp + 0x0C)))
                    a1 (memLoad32 My51 (upd (reg m51) a0 (memLoad32 My51 (reg m51 sp + 0x0C)) sp + 0x10)))
                    a3 0x10000 r = reg m r :=
                  keep_upd' (keep_upd' (keep_upd' keep51 hz (by decide)) hz (by decide)) hz (by decide)
                have pre56 : Steps m m56 := pre51.trans (.cons e52 (.cons e53 (.cons e54 (.cons e55 (.single e56)))))
                cases hio : (mw m.mem bp 8 == 0x10000)
                · obtain ⟨m57, e57, t57⟩ := t56.taken cd51.parse 0x15E pa_f6 (by decide) (by
                    simp +decide only [upd, ite_false, ite_true, v1]
                    exact bne_iff_ne.mpr fun h => by rw [h] at hio; exact absurd hio (by decide))
                  exact e7Exit m57 _ (pre56.trans (.single e57)) t57 (by simp +decide [upd, sp51])
                    (by simp +decide [upd, s51]) keep56
                    (by simp only [parseErr, hm0, hv0, hr0, hp1, hp2, hp3, hp4, hio, Bool.not_true, Bool.not_false,
                      Bool.false_eq_true, ↓reduceIte])
                · obtain ⟨m57, e57, t57⟩ := t56.notTaken cd51.parse 0xFA pa_f6 (by decide) (by
                    simp +decide only [upd, ite_false, ite_true, v1]
                    rw [(beq_iff_eq.mp hio)]; rfl)
                  -- 0xFA: the overflow checks.
                  have t57' : St My51 P m57 0xFA (reg m57) := t57.self
                  have k57 : ∀ r, r ∉ parseClob → reg m57 r = reg m r := fun r hr => by
                    rw [t57.regs]; exact keep56 r hr
                  have w57 : ∀ r, r ∈ [sp, s0, s1, s2, s3, s4, s5, s6] → reg m57 r = reg m51 r := fun r hr => by
                    rw [t57.regs]
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [upd]
                  obtain ⟨m58, e58, t58⟩ := t57'.lui cd51.parse pa_fa (off' := 0xFC) (by decide)
                  obtain ⟨m59, e59, t59⟩ := t58.self.aluImm cd51.parse pa_fc (off' := 0x100) (by decide)
                  obtain ⟨m60, e60, t60⟩ := t59.self.aluImm cd51.parse pa_100 (off' := 0x102) (by decide)
                  have w60 : ∀ r, r ∈ [sp, s0, s1, s2, s3, s4, s5, s6] → reg m60 r = reg m51 r := fun r hr => by
                    have h1 : r ≠ a0 := fun e => by subst e; simp +decide at hr
                    have h2 : r ≠ a1 := fun e => by subst e; simp +decide at hr
                    rw [reg_ne t60.regs h1, reg_ne t59.regs h2, reg_ne t58.regs h1]; exact w57 r hr
                  have k60 : ∀ r, r ∉ parseClob → reg m60 r = reg m r :=
                    keep_ne t60.regs (by decide) (keep_ne t59.regs (by decide) (keep_ne t58.regs (by decide) k57))
                  have a060 : reg m60 a0 = 6 := by rw [reg_eq t60.regs (by decide)]; rfl
                  have a160 : reg m60 a1 = 0xFFFEFFFF := by
                    rw [reg_ne t60.regs (by decide), reg_eq t59.regs (by decide), reg_eq t58.regs (by decide)]; rfl
                  have sp60 : reg m60 sp = G := (w60 sp (by decide)).trans sp51
                  have s060 : reg m60 s0 = out := (w60 s0 (by decide)).trans s51
                  have pre60 : Steps m m60 := pre56.trans (.cons e57 (.cons e58 (.cons e59 (.single e60))))
                  have e6Exit : ∀ (n : Machine) (f : Fin 32 → Word), Steps m n → St My51 P n 0xD2 f →
                      f sp = G → f s0 = out → f a0 = 6 → (∀ r, r ∉ parseClob → f r = reg m r) →
                      parseErr m.mem bp = some 6 →
                      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
                        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ t0 →
                          reg m' r = reg m r) ∧
                        ∀ x, Sep R 144 x 1 → m'.mem x = parseMem m.mem out bp x :=
                    fun n f hn s hsp hs0 ha hk hpe =>
                      errExit n My51 f 6 hn s hsp hs0 (by rw [ha]; rfl) hpe O51 S51 hk
                  have t60' : St My51 P m60 0x102 (reg m60) := t60.self
                  cases ho1 : (0xFFFEFFFF : Word).ult (mw m.mem bp 12)
                  · obtain ⟨m61, e61, t61⟩ := t60'.notTaken cd51.parse 0x106 pa_102 (by decide) (by
                      show (reg m60 a1).ult (reg m60 s6) = false
                      rw [a160, w60 s6 (by decide), v6]; exact ho1)
                    have t61' : St My51 P m61 0x106 (reg m61) := t61.self
                    have r61 : ∀ r, reg m61 r = reg m60 r := fun r => (t61.regs r).symm ▸ rfl
                    obtain ⟨m62, e62, t62⟩ := t61'.alu cd51.parse pa_106 (off' := 0x10A) (by decide)
                    have w62 : ∀ r, r ∈ [sp, s0, s1, s2, s3, s4, s5, s6] → reg m62 r = reg m51 r := fun r hr => by
                      have h1 : r ≠ a4 := fun e => by subst e; simp +decide at hr
                      rw [reg_ne t62.regs h1, r61]; exact w60 r hr
                    have a462 : reg m62 a4 = mw m.mem bp 20 + mw m.mem bp 16 := by
                      rw [reg_eq t62.regs (by decide), r61, r61, w60 s3 (by decide), w60 s2 (by decide), v3, v2]; rfl
                    have k62 : ∀ r, r ∉ parseClob → reg m62 r = reg m r := keep_ne t62.regs (by decide)
                      (fun r hr => (r61 r).trans (k60 r hr))
                    have a062 : reg m62 a0 = 6 := by rw [reg_ne t62.regs (by decide), r61, a060]
                    have pre62 : Steps m m62 := pre60.trans (.cons e61 (.single e62))
                    have t62' : St My51 P m62 0x10A (reg m62) := t62.self
                    cases ho2 : (mw m.mem bp 20 + mw m.mem bp 16).ult (mw m.mem bp 20)
                    · obtain ⟨m63, e63, t63⟩ := t62'.notTaken cd51.parse 0x10E pa_10a (by decide) (by
                        show (reg m62 a4).ult (reg m62 s3) = false
                        rw [a462, w62 s3 (by decide), v3]; exact ho2)
                      have t63' : St My51 P m63 0x10E (reg m63) := t63.self
                      have r63 : ∀ r, reg m63 r = reg m62 r := fun r => (t63.regs r).symm ▸ rfl
                      obtain ⟨m64, e64, t64⟩ := t63'.alu cd51.parse pa_10e (off' := 0x112) (by decide)
                      have w64 : ∀ r, r ∈ [sp, s0, s1, s2, s3, s4, s5, s6] → reg m64 r = reg m51 r :=
                        fun r hr => by
                          have h1 : r ≠ a5 := fun e => by subst e; simp +decide at hr
                          rw [reg_ne t64.regs h1, r63]; exact w62 r hr
                      have a564 : reg m64 a5 = mw m.mem bp 28 + mw m.mem bp 24 := by
                        rw [reg_eq t64.regs (by decide), r63, r63, w62 s5 (by decide), w62 s4 (by decide), v5, v4]; rfl
                      have a464 : reg m64 a4 = mw m.mem bp 20 + mw m.mem bp 16 := by
                        rw [reg_ne t64.regs (by decide), r63, a462]
                      have k64 : ∀ r, r ∉ parseClob → reg m64 r = reg m r := keep_ne t64.regs (by decide)
                        (fun r hr => (r63 r).trans (k62 r hr))
                      have a064 : reg m64 a0 = 6 := by rw [reg_ne t64.regs (by decide), r63, a062]
                      have pre64 : Steps m m64 := pre62.trans (.cons e63 (.single e64))
                      have t64' : St My51 P m64 0x112 (reg m64) := t64.self
                      cases ho3 : (mw m.mem bp 28 + mw m.mem bp 24).ult (mw m.mem bp 28)
                      · obtain ⟨m65, e65, t65⟩ := t64'.notTaken cd51.parse 0x116 pa_112 (by decide) (by
                          show (reg m64 a5).ult (reg m64 s5) = false
                          rw [a564, w64 s5 (by decide), v5]; exact ho3)
                        have t65' : St My51 P m65 0x116 (reg m65) := t65.self
                        have r65 : ∀ r, reg m65 r = reg m64 r := fun r => (t65.regs r).symm ▸ rfl
                        have sp65 : reg m65 sp = G := by rw [r65, w64 sp (by decide), sp51]
                        obtain ⟨m66, e66, t66⟩ := t65'.lw cd51.parse pa_116 (off' := 0x118) (by decide)
                          (by rw [sp65]; exact aligned_add hG (k := 0x18) (by decide))
                        have sp66 : reg m66 sp = G := by rw [reg_ne t66.regs (by decide), sp65]
                        obtain ⟨m67, e67, t67⟩ := t66.self.lw cd51.parse pa_118 (off' := 0x11A) (by decide)
                          (by rw [sp66]; exact aligned_add hG (k := 0x1C) (by decide))
                        obtain ⟨m68, e68, t68⟩ := t67.self.alu cd51.parse pa_11a (off' := 0x11E) (by decide)
                        have s168 : reg m68 s1 = mw m.mem bp 32 := by
                          rw [reg_ne t68.regs (by decide), reg_ne t67.regs (by decide), reg_eq t66.regs (by decide),
                            sp65]; exact w32
                        have a268 : reg m68 a2 = mw m.mem bp 36 := by
                          rw [reg_ne t68.regs (by decide), reg_eq t67.regs (by decide), sp66]; exact w36
                        have a168 : reg m68 a1 = mw m.mem bp 36 + mw m.mem bp 32 := by
                          rw [reg_eq t68.regs (by decide), reg_eq t67.regs (by decide),
                            reg_ne t67.regs (by decide), reg_eq t66.regs (by decide), sp66, sp65, w32, w36]; rfl
                        have w68 : ∀ r, r ∈ [sp, s0, s2, s3, s4, s5, s6] → reg m68 r = reg m51 r := fun r hr => by
                          have h1 : r ≠ a1 := fun e => by subst e; simp +decide at hr
                          have h2 : r ≠ a2 := fun e => by subst e; simp +decide at hr
                          have h3 : r ≠ s1 := fun e => by subst e; simp +decide at hr
                          rw [reg_ne t68.regs h1, reg_ne t67.regs h2, reg_ne t66.regs h3, r65]
                          exact w64 r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega)
                        have a468 : reg m68 a4 = mw m.mem bp 20 + mw m.mem bp 16 := by
                          rw [reg_ne t68.regs (by decide), reg_ne t67.regs (by decide), reg_ne t66.regs (by decide),
                            r65, a464]
                        have a568 : reg m68 a5 = mw m.mem bp 28 + mw m.mem bp 24 := by
                          rw [reg_ne t68.regs (by decide), reg_ne t67.regs (by decide), reg_ne t66.regs (by decide),
                            r65, a564]
                        have a068 : reg m68 a0 = 6 := by
                          rw [reg_ne t68.regs (by decide), reg_ne t67.regs (by decide), reg_ne t66.regs (by decide),
                            r65, a064]
                        have k68 : ∀ r, r ∉ parseClob → reg m68 r = reg m r := keep_ne t68.regs (by decide)
                          (keep_ne t67.regs (by decide) (keep_ne t66.regs (by decide)
                            (fun r hr => (r65 r).trans (k64 r hr))))
                        have pre68 : Steps m m68 := pre64.trans (.cons e65 (.cons e66 (.cons e67 (.single e68))))
                        have t68' : St My51 P m68 0x11E (reg m68) := t68.self
                        cases ho4 : (mw m.mem bp 36 + mw m.mem bp 32).ult (mw m.mem bp 36)
                        · obtain ⟨m69, e69, t69⟩ := t68'.notTaken cd51.parse 0x122 pa_11e (by decide) (by
                            show (reg m68 a1).ult (reg m68 a2) = false
                            rw [a168, a268]; exact ho4)
                          -- 0x122: the order checks.
                          have a368 : reg m68 a3 = 0x10000 := by
                            rw [reg_ne t68.regs (by decide), reg_ne t67.regs (by decide), reg_ne t66.regs (by decide),
                              r65, reg_ne t64.regs (by decide), r63, reg_ne t62.regs (by decide), r61,
                              reg_ne t60.regs (by decide), reg_ne t59.regs (by decide), reg_ne t58.regs (by decide),
                              t57.regs]
                            simp +decide [upd]
                          have t69' : St My51 P m69 0x122 (reg m69) := t69.self
                          have r69 : ∀ r, reg m69 r = reg m68 r := fun r => (t69.regs r).symm ▸ rfl
                          obtain ⟨m70, e70, t70⟩ := t69'.alu cd51.parse pa_122 (off' := 0x124) (by decide)
                          have a370 : reg m70 a3 = 0x10000 + mw m.mem bp 12 := by
                            rw [reg_eq t70.regs (by decide), r69, r69, a368, w68 s6 (by decide), v6]; rfl
                          have q70 : ∀ r, r ≠ a3 → reg m70 r = reg m68 r := fun r h => by
                            rw [reg_ne t70.regs h, r69]
                          have k70 : ∀ r, r ∉ parseClob → reg m70 r = reg m r := keep_ne t70.regs (by decide)
                            (fun r hr => (r69 r).trans (k68 r hr))
                          have sp70 : reg m70 sp = G := by rw [q70 sp (by decide), w68 sp (by decide), sp51]
                          have s070 : reg m70 s0 = out := by rw [q70 s0 (by decide), w68 s0 (by decide), s51]
                          have pre70 : Steps m m70 := pre68.trans (.cons e69 (.single e70))
                          have t70' : St My51 P m70 0x124 (reg m70) := t70.self
                          cases hl1 : (mw m.mem bp 16).ult (0x10000 + mw m.mem bp 12)
                          · obtain ⟨m71, e71, t71⟩ := t70'.notTaken cd51.parse 0x128 pa_124 (by decide) (by
                              show (reg m70 s2).ult (reg m70 a3) = false
                              rw [a370, q70 s2 (by decide), w68 s2 (by decide), v2]; exact hl1)
                            have t71' : St My51 P m71 0x128 (reg m70) := t71
                            cases hl2 : (mw m.mem bp 24).ult (mw m.mem bp 20 + mw m.mem bp 16)
                            · obtain ⟨m72, e72, t72⟩ := t71'.notTaken cd51.parse 0x12C pa_128 (by decide) (by
                                show (reg m70 s4).ult (reg m70 a4) = false
                                rw [q70 a4 (by decide), a468, q70 s4 (by decide), w68 s4 (by decide), v4]; exact hl2)
                              cases hl3 : (mw m.mem bp 32).ult (mw m.mem bp 28 + mw m.mem bp 24)
                              · obtain ⟨m73, e73, t73⟩ := t72.notTaken cd51.parse 0x130 pa_12c (by decide) (by
                                  show (reg m70 s1).ult (reg m70 a5) = false
                                  rw [q70 a5 (by decide), a568, q70 s1 (by decide), s168]; exact hl3)
                                obtain ⟨m74, e74, t74⟩ := t73.lui cd51.parse pa_130 (off' := 0x134) (by decide)
                                obtain ⟨m75, e75, t75⟩ := t74.self.aluImm cd51.parse pa_134 (off' := 0x136) (by decide)
                                have r74 : ∀ r, r ≠ a3 → reg m74 r = reg m70 r := fun r h => by
                                  rw [t74.regs]
                                  by_cases h0 : r.val = 0
                                  · have : r = 0 := Fin.ext h0
                                    subst this; rfl
                                  · simp [upd, h0, h]
                                have a375 : reg m75 a3 = 0x1E0000 := by
                                  rw [reg_ne t75.regs (by decide), t74.regs]; simp +decide [upd]
                                have a175 : reg m75 a1 = mw m.mem bp 36 + mw m.mem bp 32 := by
                                  rw [reg_ne t75.regs (by decide), r74 a1 (by decide), q70 a1 (by decide), a168]
                                have a075 : reg m75 a0 = 7 := by rw [reg_eq t75.regs (by decide)]; rfl
                                have k75 : ∀ r, r ∉ parseClob → reg m75 r = reg m r := keep_ne t75.regs (by decide)
                                  (fun r hr => (r74 r (fun e => hr (e ▸ by decide))).trans (k70 r hr))
                                have q75 : ∀ r, r ≠ a0 → r ≠ a3 → reg m75 r = reg m70 r := fun r h1 h2 => by
                                  rw [reg_ne t75.regs h1, r74 r h2]
                                have pre75 : Steps m m75 :=
                                  pre70.trans (.cons e71 (.cons e72 (.cons e73 (.cons e74 (.single e75)))))
                                have t75' : St My51 P m75 0x136 (reg m75) := t75.self
                                cases hl4 : (0x1E0000 : Word).ult (mw m.mem bp 36 + mw m.mem bp 32)
                                · obtain ⟨m76, e76, t76⟩ := t75'.notTaken cd51.parse 0x13A pa_136 (by decide) (by
                                    show (reg m75 a3).ult (reg m75 a1) = false
                                    rw [a375, a175]; exact hl4)
                                  have hpe : parseErr m.mem bp = none := by
                                    simp only [parseErr, hm0, hv0, hr0, hp1, hp2, hp3, hp4, hio, ho1, ho2, ho3, ho4,
                                      hl1, hl2, hl3, hl4, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                                  -- 0x13A: store the four parts at `out` and return `Ok`.
                                  obtain ⟨m77, e77, t77⟩ := t76.aluImm cd51.parse pa_13a (off' := 0x13C) (by decide)
                                  obtain ⟨m78, e78, t78⟩ := t77.self.lui cd51.parse pa_13c (off' := 0x13E) (by decide)
                                  have q78 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a3 → reg m78 r = reg m68 r :=
                                    fun r h0 h1 h3 => by
                                      rw [reg_ne t78.regs h1, reg_ne t77.regs h0, q75 r h0 h3, q70 r h3]
                                  have s078 : reg m78 s0 = out := by
                                    rw [q78 s0 (by decide) (by decide) (by decide), w68 s0 (by decide), s51]
                                  have sp78 : reg m78 sp = G := by
                                    rw [q78 sp (by decide) (by decide) (by decide), w68 sp (by decide), sp51]
                                  have a078 : reg m78 a0 = 0 := by
                                    rw [reg_ne t78.regs (by decide), reg_eq t77.regs (by decide)]; rfl
                                  have a178 : reg m78 a1 = 0x10000 := reg_eq t78.regs (by decide)
                                  have vv : ∀ r, r ∈ [s2, s3, s4, s5, s6] → reg m78 r = reg m51 r := fun r hr => by
                                    have h0 : r ≠ a0 := fun e => by subst e; simp +decide at hr
                                    have h1 : r ≠ a1 := fun e => by subst e; simp +decide at hr
                                    have h3 : r ≠ a3 := fun e => by subst e; simp +decide at hr
                                    rw [q78 r h0 h1 h3]
                                    exact w68 r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega)
                                  have k78 : ∀ r, r ∉ parseClob → reg m78 r = reg m r := keep_ne t78.regs (by decide)
                                    (keep_ne t77.regs (by decide) k75)
                                  have sepO : ∀ o, o + 4 ≤ 36 →
                                      Sep (out + BitVec.ofNat 32 o) 4 P manifestParseCode.length ∧
                                      Sep (out + BitVec.ofNat 32 o) 4 (P + 0x12B8A) parseRestoreCode.length :=
                                    fun o ho => ⟨(Oc 36 (by omega)).1.sub (c := o) (l := 4) ho,
                                      (Oc 36 (by omega)).2.sub (c := o) (l := 4) ho⟩
                                  have al : ∀ o, o % 4 = 0 → o < 64 → (reg m78 s0 + BitVec.ofNat 32 o).toNat % 4 = 0 :=
                                    fun o h1 h2 => by rw [s078]; exact aligned_add env.hout h1
                                  have c0 := cd51.parse
                                  have r0 := cd51.restore
                                  obtain ⟨m79, e79, t79⟩ := t78.self.sw c0 pa_13e (off' := 0x140) (by decide)
                                    (al 4 (by decide) (by decide))
                                  rw [s078, a178] at t79
                                  have c1 := c0.store32 (a := out + 4) (v := 0x10000) (sepO 4 (by omega)).1
                                  have r1 := r0.store32 (a := out + 4) (v := 0x10000) (sepO 4 (by omega)).2
                                  obtain ⟨m80, e80, t80⟩ := t79.sw c1 pa_140 (off' := 0x144) (by decide)
                                    (al 8 (by decide) (by decide))
                                  rw [s078, vv s6 (by decide), v6] at t80
                                  have c2' := c1.store32 (a := out + 8) (v := mw m.mem bp 12) (sepO 8 (by omega)).1
                                  have r2 := r1.store32 (a := out + 8) (v := mw m.mem bp 12) (sepO 8 (by omega)).2
                                  obtain ⟨m81, e81, t81⟩ := t80.sw c2' pa_144 (off' := 0x148) (by decide)
                                    (al 0xC (by decide) (by decide))
                                  rw [s078, vv s2 (by decide), v2] at t81
                                  have c3' := c2'.store32 (a := out + 0xC) (v := mw m.mem bp 16) (sepO 12 (by omega)).1
                                  have r3 := r2.store32 (a := out + 0xC) (v := mw m.mem bp 16) (sepO 12 (by omega)).2
                                  obtain ⟨m82, e82, t82⟩ := t81.sw c3' pa_148 (off' := 0x14C) (by decide)
                                    (al 0x10 (by decide) (by decide))
                                  rw [s078, vv s3 (by decide), v3] at t82
                                  have c4 := c3'.store32 (a := out + 0x10) (v := mw m.mem bp 20) (sepO 16 (by omega)).1
                                  have r4 := r3.store32 (a := out + 0x10) (v := mw m.mem bp 20) (sepO 16 (by omega)).2
                                  obtain ⟨m83, e83, t83⟩ := t82.sw c4 pa_14c (off' := 0x150) (by decide)
                                    (al 0x14 (by decide) (by decide))
                                  rw [s078, vv s4 (by decide), v4] at t83
                                  have c5 := c4.store32 (a := out + 0x14) (v := mw m.mem bp 24) (sepO 20 (by omega)).1
                                  have r5 := r4.store32 (a := out + 0x14) (v := mw m.mem bp 24) (sepO 20 (by omega)).2
                                  obtain ⟨m84, e84, t84⟩ := t83.sw c5 pa_150 (off' := 0x154) (by decide)
                                    (al 0x18 (by decide) (by decide))
                                  rw [s078, vv s5 (by decide), v5] at t84
                                  have c6 := c5.store32 (a := out + 0x18) (v := mw m.mem bp 28) (sepO 24 (by omega)).1
                                  have r6 := r5.store32 (a := out + 0x18) (v := mw m.mem bp 28) (sepO 24 (by omega)).2
                                  obtain ⟨m85, e85, t85⟩ := t84.sw c6 pa_154 (off' := 0x156) (by decide)
                                    (al 0x1C (by decide) (by decide))
                                  rw [s078, q78 s1 (by decide) (by decide) (by decide), s168] at t85
                                  have c7 := c6.store32 (a := out + 0x1C) (v := mw m.mem bp 32) (sepO 28 (by omega)).1
                                  have r7 := r6.store32 (a := out + 0x1C) (v := mw m.mem bp 32) (sepO 28 (by omega)).2
                                  obtain ⟨m86, e86, t86⟩ := t85.sw c7 pa_156 (off' := 0x158) (by decide)
                                    (al 0x20 (by decide) (by decide))
                                  rw [s078, q78 a2 (by decide) (by decide) (by decide), a268] at t86
                                  have c8 := c7.store32 (a := out + 0x20) (v := mw m.mem bp 36) (sepO 32 (by omega)).1
                                  have r8 := r7.store32 (a := out + 0x20) (v := mw m.mem bp 36) (sepO 32 (by omega)).2
                                  obtain ⟨m87, e87, t87⟩ := t86.jump c8 pa_158 (off' := 0xD8) (by decide)
                                    (by rw [t86.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0xD8 (by decide)))
                                  obtain ⟨m88, c88, pc88, mem88, regs88⟩ := parse_tail t87 c8 r8 env.hP sp78 hG s078
                                    (Oc 1 (by omega)).1 (Oc 1 (by omega)).2
                                  rw [a078, show (0 : Word).extractLsb' 0 8 = 0 from rfl] at pc88 mem88 regs88
                                  have so : ∀ o k, o + 4 ≤ 36 → k < 64 → Sep (out + BitVec.ofNat 32 o) 4 (G + BitVec.ofNat 32 k) 1 :=
                                    fun o k h1 h2 => by
                                      rw [env.g_ofs]; exact (env.hOS.sub (c := o) (l := 4) h1).subR (c := 80 + k) (l := 1) (by omega)
                                  have hS' : ∀ k, 0x20 ≤ k → k < 0x40 → memStore8 (memStore32 (memStore32 (memStore32
                                      (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 My51 (out + 4) 0x10000)
                                      (out + 8) (mw m.mem bp 12)) (out + 0xC) (mw m.mem bp 16)) (out + 0x10) (mw m.mem bp 20))
                                      (out + 0x14) (mw m.mem bp 24)) (out + 0x18) (mw m.mem bp 28)) (out + 0x1C)
                                      (mw m.mem bp 32)) (out + 0x20) (mw m.mem bp 36)) out 0 (G + BitVec.ofNat 32 k) =
                                      M2 (G + BitVec.ofNat 32 k) := fun k h1 h2 => by
                                    rw [memStore8_ne (fun h => outG k (by omega) 0 (by omega) (by rw [add_ofNat_zero]; exact h.symm)),
                                      memStore32_get_sep (show Sep (out + 0x20) 4 _ 1 from so 0x20 k (by omega) (by omega)),
                                      memStore32_get_sep (show Sep (out + 0x1C) 4 _ 1 from so 0x1C k (by omega) (by omega)),
                                      memStore32_get_sep (show Sep (out + 0x18) 4 _ 1 from so 0x18 k (by omega) (by omega)),
                                      memStore32_get_sep (show Sep (out + 0x14) 4 _ 1 from so 0x14 k (by omega) (by omega)),
                                      memStore32_get_sep (show Sep (out + 0x10) 4 _ 1 from so 0x10 k (by omega) (by omega)),
                                      memStore32_get_sep (show Sep (out + 0xC) 4 _ 1 from so 0xC k (by omega) (by omega)),
                                      memStore32_get_sep (show Sep (out + 8) 4 _ 1 from so 8 k (by omega) (by omega)),
                                      memStore32_get_sep (show Sep (out + 4) 4 _ 1 from so 4 k (by omega) (by omega))]
                                    exact S51 k h1 h2
                                  obtain ⟨sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8⟩ := slotsOf _ hS'
                                  have fin := parse_finish (L := P + BitVec.ofNat 32 0xE4) k78 hz sl1 sl2 sl3 sl4 sl5
                                    sl6 sl7 sl8 hsp0
                                  refine ⟨m88, pre75.trans (.cons e76 (.cons e77 (.cons e78 (.cons e79 (.cons e80 (.cons e81 (.cons e82 (.cons e83 (.cons e84 (.cons e85 (.cons e86 (.cons e87 c88)))))))))))),
                                    by rw [pc88, sl1, hra, hret], ?_, fun r h1 h2 h3 h4 h5 h6 h7 => by
                                      rw [regs88]; exact fin r h1 h2 h3 h4 h5 h6 h7, fun x hx => ?_⟩
                                  · rw [regs88]
                                    exact fin sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                                      (by decide)
                                  · rw [mem88]; unfold parseMem; rw [hpe]; dsimp only
                                    exact memStore8_congr (memStore32_congr (memStore32_congr (memStore32_congr
                                      (memStore32_congr (memStore32_congr (memStore32_congr (memStore32_congr
                                      (memStore32_congr (O51 x hx)))))))))
                                · obtain ⟨m76, e76, t76⟩ := t75'.taken cd51.parse 0xD2 pa_136 (by decide) (by
                                    show (reg m75 a3).ult (reg m75 a1) = true
                                    rw [a375, a175]; exact hl4)
                                  exact errExit m76 My51 _ 7 (pre75.trans (.single e76)) t76
                                    (by rw [q75 sp (by decide) (by decide), sp70])
                                    (by rw [q75 s0 (by decide) (by decide), s070]) (by rw [a075]; rfl)
                                    (by simp only [parseErr, hm0, hv0, hr0, hp1, hp2, hp3, hp4, hio, ho1, ho2, ho3,
                                      ho4, hl1, hl2, hl3, hl4, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
                                    O51 S51 k75
                              · obtain ⟨m73, e73, t73⟩ := t72.taken cd51.parse 0x15E pa_12c (by decide) (by
                                  show (reg m70 s1).ult (reg m70 a5) = true
                                  rw [q70 a5 (by decide), a568, q70 s1 (by decide), s168]; exact hl3)
                                exact e7Exit m73 _ (pre70.trans (.cons e71 (.cons e72 (.single e73)))) t73 sp70 s070 k70
                                  (by simp only [parseErr, hm0, hv0, hr0, hp1, hp2, hp3, hp4, hio, ho1, ho2, ho3, ho4,
                                    hl1, hl2, hl3, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
                            · obtain ⟨m72, e72, t72⟩ := t71'.taken cd51.parse 0x15E pa_128 (by decide) (by
                                show (reg m70 s4).ult (reg m70 a4) = true
                                rw [q70 a4 (by decide), a468, q70 s4 (by decide), w68 s4 (by decide), v4]; exact hl2)
                              exact e7Exit m72 _ (pre70.trans (.cons e71 (.single e72))) t72 sp70 s070 k70
                                (by simp only [parseErr, hm0, hv0, hr0, hp1, hp2, hp3, hp4, hio, ho1, ho2, ho3, ho4,
                                  hl1, hl2, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
                          · obtain ⟨m71, e71, t71⟩ := t70'.taken cd51.parse 0x15E pa_124 (by decide) (by
                              show (reg m70 s2).ult (reg m70 a3) = true
                              rw [a370, q70 s2 (by decide), w68 s2 (by decide), v2]; exact hl1)
                            exact e7Exit m71 _ (pre70.trans (.single e71)) t71 sp70 s070 k70
                              (by simp only [parseErr, hm0, hv0, hr0, hp1, hp2, hp3, hp4, hio, ho1, ho2, ho3, ho4,
                                hl1, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
                        · obtain ⟨m69, e69, t69⟩ := t68'.taken cd51.parse 0xD2 pa_11e (by decide) (by
                            show (reg m68 a1).ult (reg m68 a2) = true
                            rw [a168, a268]; exact ho4)
                          exact e6Exit m69 _ (pre68.trans (.single e69)) t69
                            ((w68 sp (by decide)).trans sp51) ((w68 s0 (by decide)).trans s51) a068 k68
                            (by simp only [parseErr, hm0, hv0, hr0, hp1, hp2, hp3, hp4, hio, ho1, ho2, ho3, ho4,
                              Bool.not_true, Bool.false_eq_true, ↓reduceIte])
                      · obtain ⟨m65, e65, t65⟩ := t64'.taken cd51.parse 0xD2 pa_112 (by decide) (by
                          show (reg m64 a5).ult (reg m64 s5) = true
                          rw [a564, w64 s5 (by decide), v5]; exact ho3)
                        exact e6Exit m65 _ (pre64.trans (.single e65)) t65
                          ((w64 sp (by decide)).trans sp51) ((w64 s0 (by decide)).trans s51) a064 k64
                          (by simp only [parseErr, hm0, hv0, hr0, hp1, hp2, hp3, hp4, hio, ho1, ho2, ho3,
                            Bool.not_true, Bool.false_eq_true, ↓reduceIte])
                    · obtain ⟨m63, e63, t63⟩ := t62'.taken cd51.parse 0xD2 pa_10a (by decide) (by
                        show (reg m62 a4).ult (reg m62 s3) = true
                        rw [a462, w62 s3 (by decide), v3]; exact ho2)
                      exact e6Exit m63 _ (pre62.trans (.single e63)) t63
                        ((w62 sp (by decide)).trans sp51) ((w62 s0 (by decide)).trans s51) a062 k62
                        (by simp only [parseErr, hm0, hv0, hr0, hp1, hp2, hp3, hp4, hio, ho1, ho2,
                          Bool.not_true, Bool.false_eq_true, ↓reduceIte])
                  · obtain ⟨m61, e61, t61⟩ := t60'.taken cd51.parse 0xD2 pa_102 (by decide) (by
                      show (reg m60 a1).ult (reg m60 s6) = true
                      rw [a160, w60 s6 (by decide), v6]; exact ho1)
                    exact e6Exit m61 _ (pre60.trans (.single e61)) t61 sp60 s060 a060 k60
                      (by simp only [parseErr, hm0, hv0, hr0, hp1, hp2, hp3, hp4, hio, ho1, Bool.not_true,
                        Bool.false_eq_true, ↓reduceIte])
              · simp only [hp4, ite_true] at h51
                obtain ⟨tag4, err4⟩ := h51
                obtain ⟨m52, e52, t52⟩ := t51.notTaken (pcode _ O51).parse 0xCE pa_cc (by decide)
                  (by rw [tag4, z51]; decide)
                exact partErrExit m52 _ _ (pre51.trans (.single e52)) t52 sp51 s51 err4
                  (by simp only [parseErr, hm0, hv0, hr0, hp1, hp2, hp3, hp4, Bool.not_true, Bool.false_eq_true,
                    ↓reduceIte])
                  O51 S51 keep51
            · simp only [hp3, ite_true] at h43
              obtain ⟨tag3, err3⟩ := h43
              obtain ⟨m44, e44, t44⟩ := t43.taken (pcode _ O43).parse 0xCE pa_b0 (by decide)
                (by rw [tag3, z43]; decide)
              exact partErrExit m44 _ _ (pre43.trans (.single e44)) t44 sp43 s43 err3
                (by simp only [parseErr, hm0, hv0, hr0, hp1, hp2, hp3, Bool.not_true, Bool.false_eq_true,
                  ↓reduceIte])
                O43 S43 keep43
          · simp only [hp2, ite_true] at h34
            obtain ⟨tag2, err2⟩ := h34
            obtain ⟨m35, e35, t35⟩ := t34.taken (pcode _ O34).parse 0xCE pa_94 (by decide)
              (by rw [tag2, z34]; decide)
            exact partErrExit m35 _ _ (pre34.trans (.single e35)) t35 sp34 s34 err2
              (by simp only [parseErr, hm0, hv0, hr0, hp1, hp2, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
              O34 S34 keep34
        · simp only [hp1, ite_true] at h26
          obtain ⟨tag, err⟩ := h26
          obtain ⟨m27, e27, t27⟩ := t26.taken (pcode _ O26).parse 0xCE pa_78 (by decide)
            (by rw [tag, z26]; decide)
          exact partErrExit m27 _ _ (pre26.trans (.single e27)) t27 sp26 s26 err
            (by simp only [parseErr, hm0, hv0, hr0, hp1, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
            O26 S26 keep26
      · have hr0 : allZero m.mem (bp + 6) 2 = false := by
          cases hc : allZero m.mem (bp + 6) 2
          · rfl
          · rw [hres, hc] at hbad; exact absurd rfl hbad
        exact errExit m21 _ g21 4 (pre20.trans c21) t21
          (by rw [fg21 sp (by decide), sp20]) (by rw [fg21 s0 (by decide), s20])
          (by rw [fg21 a0 (by decide), hres, hr0]; rfl)
          (by simp only [parseErr, hm0, hv0, hr0, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
          O20 S20 (fun r hr => by rw [fg21 r (fun e => hr (e ▸ by decide)), keep20 r hr])
    · have hv0 : (((m.mem (bp + 5)).zeroExtend 32 <<< 24 ||| (m.mem (bp + 4)).zeroExtend 32 <<< 16 : Word) >>> 16
          == 1) = false := by
        cases hc : (((m.mem (bp + 5)).zeroExtend 32 <<< 24 ||| (m.mem (bp + 4)).zeroExtend 32 <<< 16 : Word) >>> 16
          == 1)
        · rfl
        · rw [hverC true hc] at hbad; exact absurd rfl hbad
      exact errExit m17 _ g17 3 (pre16.trans c17) t17
        (by rw [fg17 sp (by decide), sp16]) (by rw [fg17 s0 (by decide), s16])
        (by rw [fg17 a0 (by decide), hverC false hv0]; rfl)
        (by simp only [parseErr, hm0, hv0, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
        O16 S16 (fun r hr => by rw [fg17 r (fun e => hr (e ▸ by decide)), keep16 r hr])
  · have hm0 : (mw m.mem bp 0 == 0x4C533343) = false := by
      cases hc : (mw m.mem bp 0 == 0x4C533343)
      · rfl
      · rw [hmag, hc] at hbad; exact absurd rfl hbad
    exact errExit m14 _ g14 2 (pre13.trans c14) t14
      (by rw [fg14 sp (by decide), sp13]) (by rw [fg14 s0 (by decide), s13])
      (by rw [fg14 a0 (by decide), hmag, hm0]; rfl)
      (by simp only [parseErr, hm0, Bool.not_false, ↓reduceIte])
      O13 S13 (fun r hr => by rw [fg14 r (fun e => hr (e ▸ by decide)), keep13 r hr])

end C3.RV32
