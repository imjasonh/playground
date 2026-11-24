import C3BootProofs.Proofs.JsonReadItem

/-!
# `Elements::next_element`, as compiled

`next_element` on the cursor at `c`, whose words are the array's pointer
`p`, its length `n`, and the position `pos`, returns `Ok(None)` when the byte
at `pos` is `]`. Otherwise it calls `read_item` and returns `Ok(Some(value))`,
moving the cursor's position to the item's `after`, or `Err(Json)`.

The result has the layout `ElemRes` describes: a zero byte at `out` with
the value's pointer at `out + 4` (zero for `None`) and its length at
`out + 8`, or the byte `1` at `out` and the error byte `0x20` at `out + 1`.
The function saves `ra`, `s0`, and `s1` in a 32-byte frame, and `read_item`
uses 116 more bytes, so the stack region is the 148 bytes below `sp`.

`RiCode` and `RiSep` collect the code `read_item` runs and the ranges that
must stay apart from its stack, and `WP.callReadItem` steps over a call to
it. `jsonNextElement_correct` is the contract.
-/

namespace C3.Json

/-- `next_element` at `pos`: `some none` at the closing bracket, otherwise
the start, length, and `after` of the next item. -/
def nextElement (d : Bytes) (pos : Nat) : Option (Option (Nat × Nat × Nat)) :=
  if pos < d.length ∧ d.getD pos 0 = 93 then some none
  else (readItem d pos).map fun x => some (pos, x.1 - pos, x.2)

end C3.Json

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem nx_at_0 : fetchRel jsonNextElementCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem nx_at_2 : fetchRel jsonNextElementCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem nx_at_4 : fetchRel jsonNextElementCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem nx_at_6 : fetchRel jsonNextElementCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x14, 2) := by decide
theorem nx_at_8 : fetchRel jsonNextElementCode 0x8 = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem nx_at_a : fetchRel jsonNextElementCode 0xA = some (.load .lw a2 a1 0x4, 2) := by decide
theorem nx_at_c : fetchRel jsonNextElementCode 0xC = some (.load .lw a3 a1 0x8, 2) := by decide
theorem nx_at_e : fetchRel jsonNextElementCode 0xE = some (.load .lw a1 a1 0x0, 2) := by decide
theorem nx_at_10 : fetchRel jsonNextElementCode 0x10 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem nx_at_12 : fetchRel jsonNextElementCode 0x12 = some (.branch .bgeu a3 a2 0x18, 4) := by decide
theorem nx_at_16 : fetchRel jsonNextElementCode 0x16 = some (.alu .add a0 a1 a3, 4) := by decide
theorem nx_at_1a : fetchRel jsonNextElementCode 0x1A = some (.load .lbu a0 a0 0x0, 4) := by decide
theorem nx_at_1e : fetchRel jsonNextElementCode 0x1E = some (.aluImm .add a0 a0 0xFFFFFFA3, 4) := by decide
theorem nx_at_22 : fetchRel jsonNextElementCode 0x22 = some (.branch .bne a0 x0 0x8, 2) := by decide
theorem nx_at_24 : fetchRel jsonNextElementCode 0x24 = some (.store .sw (8 : Fin 32) x0 0x4, 4) := by decide
theorem nx_at_28 : fetchRel jsonNextElementCode 0x28 = some (.jal x0 0x28, 2) := by decide
theorem nx_at_2a : fetchRel jsonNextElementCode 0x2A = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem nx_at_2c : fetchRel jsonNextElementCode 0x2C = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem nx_at_30 : fetchRel jsonNextElementCode 0x30 = some (.jalr ra ra 0x7B4, 4) := by decide
theorem nx_at_34 : fetchRel jsonNextElementCode 0x34 = some (.load .lw a1 sp 0x8, 2) := by decide
theorem nx_at_36 : fetchRel jsonNextElementCode 0x36 = some (.branch .beq a1 x0 0x10, 2) := by decide
theorem nx_at_38 : fetchRel jsonNextElementCode 0x38 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem nx_at_3a : fetchRel jsonNextElementCode 0x3A = some (.load .lw a2 sp 0x10, 2) := by decide
theorem nx_at_3c : fetchRel jsonNextElementCode 0x3C = some (.load .lw a3 sp 0xC, 2) := by decide
theorem nx_at_3e : fetchRel jsonNextElementCode 0x3E = some (.store .sw (9 : Fin 32) a2 0x8, 2) := by decide
theorem nx_at_40 : fetchRel jsonNextElementCode 0x40 = some (.store .sw (8 : Fin 32) a1 0x4, 2) := by decide
theorem nx_at_42 : fetchRel jsonNextElementCode 0x42 = some (.store .sw (8 : Fin 32) a3 0x8, 2) := by decide
theorem nx_at_44 : fetchRel jsonNextElementCode 0x44 = some (.jal x0 0xC, 2) := by decide
theorem nx_at_46 : fetchRel jsonNextElementCode 0x46 = some (.load .lbu a0 sp 0xC, 4) := by decide
theorem nx_at_4a : fetchRel jsonNextElementCode 0x4A = some (.store .sb (8 : Fin 32) a0 0x1, 4) := by decide
theorem nx_at_4e : fetchRel jsonNextElementCode 0x4E = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem nx_at_50 : fetchRel jsonNextElementCode 0x50 = some (.store .sb (8 : Fin 32) a0 0x0, 4) := by decide
theorem nx_at_54 : fetchRel jsonNextElementCode 0x54 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem nx_at_56 : fetchRel jsonNextElementCode 0x56 = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem nx_at_58 : fetchRel jsonNextElementCode 0x58 = some (.load .lw (9 : Fin 32) sp 0x14, 2) := by decide
theorem nx_at_5a : fetchRel jsonNextElementCode 0x5A = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem nx_at_5c : fetchRel jsonNextElementCode 0x5C = some (.jalr x0 ra 0x0, 2) := by decide


/-- The code `read_item` at `rb` runs, and the literals `literal_end` reads. -/
structure RiCode (M : Word → BitVec 8) (rb : Word) : Prop where
  ri : CodeIn M rb jsonReadItemCode
  se : CodeIn M (rb + 0xFFFFFF0C) jsonStringEndCode
  le : CodeIn M (rb + 0x17E) jsonLiteralEndCode
  es : CodeIn M (rb + 0xFFFFF57E) equalSameLengthCode
  mc : CodeIn M (rb + 0xC93C) memcmpCode
  ne : CodeIn M (rb + 0x21A) jsonNumberEndCode
  sw : CodeIn M (rb + 0x288) jsonSkipWsCode
  lit : LitData M

/-- The `k` bytes at `s` are apart from `RiCode M rb`. -/
structure RiSep (s : Word) (k : Nat) (rb : Word) : Prop where
  ri : Sep s k rb jsonReadItemCode.length
  se : Sep s k (rb + 0xFFFFFF0C) jsonStringEndCode.length
  le : Sep s k (rb + 0x17E) jsonLiteralEndCode.length
  es : Sep s k (rb + 0xFFFFF57E) equalSameLengthCode.length
  mc : Sep s k (rb + 0xC93C) memcmpCode.length
  ne : Sep s k (rb + 0x21A) jsonNumberEndCode.length
  sw : Sep s k (rb + 0x288) jsonSkipWsCode.length
  ln : Sep s k 0x3FCC4766 8
  lf : Sep s k 0x3FCC48F2 5

theorem RiSep.sub {s rb : Word} {k : Nat} (h : RiSep s k rb) {c l : Nat} (hcl : c + l ≤ k) :
    RiSep (s + BitVec.ofNat 32 c) l rb :=
  ⟨h.ri.sub hcl, h.se.sub hcl, h.le.sub hcl, h.es.sub hcl, h.mc.sub hcl, h.ne.sub hcl, h.sw.sub hcl,
    h.ln.sub hcl, h.lf.sub hcl⟩

theorem RiSep.low {s rb : Word} {k : Nat} (h : RiSep s k rb) {l : Nat} (hl : l ≤ k) : RiSep s l rb := by
  have := h.sub (c := 0) (l := l) (by omega)
  rwa [add_ofNat_zero] at this

theorem RiCode.out {M M' : Word → BitVec 8} {rb s : Word} {k : Nat} (h : RiCode M rb) (hO : Out M M' s k)
    (hs : RiSep s k rb) : RiCode M' rb :=
  ⟨hO.codeIn h.ri hs.ri, hO.codeIn h.se hs.se, hO.codeIn h.le hs.le, hO.codeIn h.es hs.es,
    hO.codeIn h.mc hs.mc, hO.codeIn h.ne hs.ne, hO.codeIn h.sw hs.sw, h.lit.out hO hs.ln hs.lf⟩

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat}
  {f : Fin 32 → Word}

/-- A call to `read_item(doc, pos)` with the code at `tb`, its stack in the
116 bytes at `s`, storing its result at `out`. -/
theorem WP.callReadItem {hi lo tb p out s : Word} {n pos : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hrc : RiCode M tb) (hrs : RiSep s 116 tb)
    (h0 : f a0 = out) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n) (ha3 : f a3 = BitVec.ofNat 32 pos)
    (hsp : f sp = s + BitVec.ofNat 32 116) (hn : n < 2 ^ 32) (hpos : pos < 2 ^ 32) (hal : s.toNat % 4 = 0)
    (halo : out.toNat % 4 = 0) (hSp : Sep s 116 p n) (hso : Sep out 12 s 116)
    (hsc : Sep out 12 tb jsonReadItemCode.length) (hSb : Sep s 116 base code.length)
    (hsb : Sep out 12 base code.length)
    (k : ∀ m2 : Machine, CurResF M m2.mem out s 116 0x20 (itemRes p pos (readItem (memBytes M p n) pos)) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := jClob)
    (P := fun m2 => CurResF M m2.mem out s 116 0x20 (itemRes p pos (readItem (memBytes M p n) pos)))
    h1 h2 (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => by
      obtain ⟨M1, hO, hR⟩ := hP
      exact hR.out.codeIn (hO.codeIn hc hSb) hsb) k
  rw [← hmem1] at hrc
  obtain ⟨m2, c2, pc2, hR, hfr⟩ := jsonReadItem_correct m1 (base := tb) (out := out) (s := s) (p := p) (n := n)
    (pos := pos) htb hrc.ri hrc.se hrc.le hrc.es hrc.mc hrc.ne hrc.sw hrc.lit hpc1
    (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2)
    (by rw [hreg1]; rsimp; exact ha3) (by rw [hreg1]; rsimp; exact hsp) hn hpos hal halo
    (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev))
    hrs.ri hrs.se hrs.le hrs.es hrs.mc hrs.ne hrs.sw hSp hrs.ln hrs.lf hso hsc
  rw [hmem1] at hR
  exact ⟨m2, c2, pc2, hR, hfr⟩

end

/-- `out` holds `r` as a `Result<Option<Value>, TufError>`, and the
cursor at `c` holds the new position after an element. -/
def ElemRes (M M' : Word → BitVec 8) (out c : Word) : Option (Option (Word × Nat × Nat)) → Prop
  | none => (∀ x, Sep x 1 out 12 → M' x = M x) ∧ M' out = 1 ∧ M' (out + 1) = 0x20
  | some none => (∀ x, Sep x 1 out 12 → M' x = M x) ∧ M' out = 0 ∧ memLoad32 M' (out + 4) = 0
  | some (some (q, l, a)) => (∀ x, Sep x 1 out 12 → Sep x 1 (c + 8) 4 → M' x = M x) ∧ M' out = 0 ∧
      memLoad32 M' (out + 4) = q ∧ memLoad32 M' (out + 8) = BitVec.ofNat 32 l ∧
      memLoad32 M' (c + 8) = BitVec.ofNat 32 a

/-- `ElemRes` after a function that may also change the `k` bytes at `s`. -/
def ElemResF (M M' : Word → BitVec 8) (out c s : Word) (k : Nat) (r : Option (Option (Word × Nat × Nat))) :
    Prop :=
  ∃ M1, Out M M1 s k ∧ ElemRes M1 M' out c r

/-- The word-level result of `next_element` on the array at `p`. -/
def elemRes (p : Word) (r : Option (Option (Nat × Nat × Nat))) : Option (Option (Word × Nat × Nat)) :=
  r.map (Option.map fun x => (p + BitVec.ofNat 32 x.1, x.2.1, x.2.2))

theorem ElemRes.out {M M' : Word → BitVec 8} {out c x : Word} {r : Option (Option (Word × Nat × Nat))}
    (h : ElemRes M M' out c r) (ho : Sep x 1 out 12) (hc : Sep x 1 (c + 8) 4) : M' x = M x := by
  rcases r with _ | _ | ⟨_, _, _⟩
  · exact h.1 x ho
  · exact h.1 x ho
  · exact h.1 x ho hc

theorem ElemRes.load32 {M M' : Word → BitVec 8} {out c a : Word} {r : Option (Option (Word × Nat × Nat))}
    (h : ElemRes M M' out c r) (ho : Sep out 12 a 4) (hc : Sep (c + 8) 4 a 4) : memLoad32 M' a = memLoad32 M a :=
  memLoad32_congr fun _ hj => h.out (sep_pt ho hj) (sep_pt hc hj)

theorem ElemRes.slots {M M' M1 : Word → BitVec 8} {out c F : Word} {cs : List Nat}
    {r : Option (Option (Word × Nat × Nat))} (h : ElemRes M M' out c r) (hS : Slots cs F M1 M)
    (ho : ∀ d, d ∈ cs → Sep out 12 (F + BitVec.ofNat 32 d) 4)
    (hc : ∀ d, d ∈ cs → Sep (c + 8) 4 (F + BitVec.ofNat 32 d) 4) : Slots cs F M1 M' :=
  fun d hd => (h.load32 (ho d hd) (hc d hd)).trans (hS d hd)

theorem sep_o4 (out : Word) {d : Nat} (hd : 1 ≤ d) (hd2 : d + 4 ≤ 12) : Sep out 1 (out + BitVec.ofNat 32 d) 4 := by
  have := sep_offsets out (c := 0) (n := 1) (d := d) (k := 4) (Or.inl hd) (by decide) (by omega)
  rwa [add_ofNat_zero] at this

theorem elem_err (M : Word → BitVec 8) (out c : Word) :
    ElemRes M (memStore8 (memStore8 M (out + 1) 0x20) out 1) out c none := by
  refine ⟨fun x hx => ?_, memStore8_same _ _ _, ?_⟩
  · have h0 : Sep x 1 out 1 := by
      have := hx.subR (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
    rw [(out_store8 _ out 1) x h0]
    exact (out_store8 _ (out + 1) 0x20) x (hx.subR (c := 1) (l := 1) (by decide))
  · rw [memStore8_ne (ne_add_one out), memStore8_same]

theorem elem_end (M : Word → BitVec 8) (out c : Word) :
    ElemRes M (memStore8 (memStore32 M (out + 4) 0) out 0) out c (some none) := by
  refine ⟨fun x hx => ?_, memStore8_same _ _ _, ?_⟩
  · have h0 : Sep x 1 out 1 := by
      have := hx.subR (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
    rw [(out_store8 _ out 0) x h0]
    exact (out_store32 _ (out + 4) 0) x (hx.subR (c := 4) (l := 4) (by decide))
  · exact ((out_store8 _ out 0).load32 (sep_o4 out (d := 4) (by decide) (by decide))).trans
      (memLoad32_store32_same _ _ _)

theorem elem_ok (M : Word → BitVec 8) {out c : Word} (q : Word) (l a : Nat) (hoc : Sep out 12 c 12) :
    ElemRes M (memStore8 (memStore32 (memStore32 (memStore32 M (c + 8) (BitVec.ofNat 32 a)) (out + 4) q)
      (out + 8) (BitVec.ofNat 32 l)) out 0) out c (some (some (q, l, a))) := by
  have s48 : Sep (out + BitVec.ofNat 32 4) 4 (out + BitVec.ofNat 32 8) 4 :=
    sep_offsets out (Or.inl (by decide)) (by decide) (by decide)
  have sc4 : Sep (c + BitVec.ofNat 32 8) 4 (out + BitVec.ofNat 32 4) 4 :=
    ((hoc.sub (c := 4) (l := 4) (by decide)).subR (c := 8) (l := 4) (by decide)).symm
  have sc8 : Sep (c + BitVec.ofNat 32 8) 4 (out + BitVec.ofNat 32 8) 4 :=
    ((hoc.sub (c := 8) (l := 4) (by decide)).subR (c := 8) (l := 4) (by decide)).symm
  refine ⟨fun x hx hc => ?_, memStore8_same _ _ _, ?_, ?_, ?_⟩
  · have h0 : Sep x 1 out 1 := by
      have := hx.subR (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
    rw [(out_store8 _ out 0) x h0, (out_store32 _ (out + 8) _) x (hx.subR (c := 8) (l := 4) (by decide)),
      (out_store32 _ (out + 4) _) x (hx.subR (c := 4) (l := 4) (by decide)), (out_store32 _ (c + 8) _) x hc]
  · exact ((out_store8 _ out 0).load32 (sep_o4 out (d := 4) (by decide) (by decide))).trans
      ((memLoad32_store32_sep s48.symm).trans (memLoad32_store32_same _ _ _))
  · exact ((out_store8 _ out 0).load32 (sep_o4 out (d := 8) (by decide) (by decide))).trans
      (memLoad32_store32_same _ _ _)
  · have hc0 : Sep out 1 (c + BitVec.ofNat 32 8) 4 := by
      have := (hoc.sub (c := 0) (l := 1) (by decide)).subR (c := 8) (l := 4) (by decide)
      rwa [add_ofNat_zero] at this
    exact ((out_store8 _ out 0).load32 hc0).trans <| 
      (memLoad32_store32_sep sc8.symm).trans ((memLoad32_store32_sep sc4.symm).trans (memLoad32_store32_same _ _ _))

theorem readItem_bd {d : Bytes} {pos : Nat} {x : Nat × Nat} (h : readItem d pos = some x) :
    pos < x.1 ∧ x.1 ≤ d.length := by
  unfold readItem at h
  cases hv : valueEnd d pos with
  | none => rw [hv] at h; cases h
  | some e =>
    rw [hv] at h
    cases h
    unfold itemTail
    split <;> exact valueEnd_bd hv

/-- The registers `next_element` changes before its epilogue restores the saved ones. -/
abbrev nxE : List (Fin 32) := jClob ++ [ra, sp, 8, 9]

abbrev nxCs : List Nat := [0x14, 0x18, 0x1C]

/-- The saved registers in the frame at `F`. -/
def NxSaved (F : Word) (g0 : Fin 32 → Word) (M1 : Word → BitVec 8) : Prop :=
  memLoad32 M1 (F + BitVec.ofNat 32 0x1C) = g0 ra ∧ memLoad32 M1 (F + BitVec.ofNat 32 0x18) = g0 8 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x14) = g0 9

/-- Memory after the prologue. -/
def nxM1 (M : Word → BitVec 8) (F : Word) (g0 : Fin 32 → Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 M (F + 0x1C) (g0 ra)) (F + 0x18) (g0 8)) (F + 0x14) (g0 9)

theorem nx_pro (M : Word → BitVec 8) (F : Word) (g0 : Fin 32 → Word) :
    Out M (nxM1 M F g0) F 32 ∧ NxSaved F g0 (nxM1 M F g0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (((out_store32 _ _ _).widen (d := 0x1C) (by decide)).trans
      ((out_store32 _ _ _).widen (d := 0x18) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x14) (by decide))
  · exact ld_skip 0x1C 0x14 (by decide) (by decide) (by decide) (ld_skip 0x1C 0x18 (by decide) (by decide)
      (by decide) (memLoad32_store32_same _ _ _))
  · exact ld_skip 0x18 0x14 (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _)
  · exact memLoad32_store32_same _ _ _

section
variable {M M1 : Word → BitVec 8} {base F : Word} {f g0 : Fin 32 → Word}

theorem nx_epi {Mf : Word → BitVec 8} {R : (Word → BitVec 8) → Prop} (hsp : f sp = F)
    (hS : Slots nxCs F M1 Mf) (hv : NxSaved F g0 M1) (hsp0 : g0 sp = F + BitVec.ofNat 32 0x20)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ nxE → f x = g0 x) (hR : R Mf) :
    WP jsonNextElementCode base (RPost (g0 ra) R g0) Mf 0x54 f := by
  obtain ⟨v1, v2, v3⟩ := hv
  have e1 : memLoad32 Mf (F + 0x1C) = g0 ra := (hS 0x1C (by decide)).trans v1
  have e2 : memLoad32 Mf (F + 0x18) = g0 8 := (hS 0x18 (by decide)).trans v2
  have e3 : memLoad32 Mf (F + 0x14) = g0 9 := (hS 0x14 (by decide)).trans v3
  refine WP.lw nx_at_54 (by rw [hsp]; exact aligned_add hal (k := 0x1C) (by decide)) ?_; wn
  refine WP.lw nx_at_56 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x18) (by decide)) ?_; wn
  refine WP.lw nx_at_58 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0x14) (by decide)) ?_; wn
  refine WP.aluImm nx_at_5a ?_; wn
  refine WP.ret nx_at_5c ⟨?_, hR, ?_⟩
  · rsimp; rw [hsp, e1, add_lit_zero, hret]
  refine frame_of (L2 := [ra, sp, 8, 9]) (by keepz hz0) fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> rsimp
  · rw [hsp, e1]
  · rw [hsp, hsp0]; rfl
  · rw [hsp, e2]
  · rw [hsp, e3]

end

theorem sep_low {s a : Word} {k k' l : Nat} (h : Sep s k a l) (hk : k' ≤ k) : Sep s k' a l := by
  have := h.sub (c := 0) (l := k') (by omega)
  rwa [add_ofNat_zero] at this

/-- A word in the frame is apart from the 116 bytes below it. -/
theorem sep_below116 {s F : Word} (hF : s + BitVec.ofNat 32 116 = F) {c w : Nat} (hc : 116 + c + w ≤ 2 ^ 32) :
    Sep s 116 (F + BitVec.ofNat 32 c) w := by
  subst hF
  have := sep_offsets s (c := 0) (n := 116) (d := 116 + c) (k := w) (Or.inl (by omega)) (by omega) (by omega)
  rwa [add_ofNat_zero, ← add_ofNat_assoc] at this

theorem nxSepF {s F a : Word} {l c w : Nat} (hF : s + BitVec.ofNat 32 116 = F) (h : Sep s 148 a l)
    (hc : 116 + c + w ≤ 148) : Sep (F + BitVec.ofNat 32 c) w a l := by
  subst hF; rw [add_ofNat_assoc]; exact h.sub hc

theorem nx_rb' : ∀ b : BitVec 8,
    branchTaken .bne (aluEval .add (b.zeroExtend 32) 0xFFFFFFA3) 0 = !(b.toNat == 93) := by decide

theorem nx_rb0 : ((aluEval .add ((93 : BitVec 8).zeroExtend 32) 0xFFFFFFA3).extractLsb' 0 8) = 0 := by decide

theorem nx_q0 {p : Word} {n pos : Nat} (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n ≤ 2 ^ 32) (hlt : pos < n) :
    branchTaken .beq (p + BitVec.ofNat 32 pos) 0 = false := by
  have h : (p + BitVec.ofNat 32 pos).toNat = p.toNat + pos := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show pos < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hne : p + BitVec.ofNat 32 pos ≠ 0 := fun e => by
    rw [e] at h; exact absurd h (by rw [show (0 : Word).toNat = 0 from rfl]; omega)
  show (_ == _) = false
  exact beq_eq_false_iff_ne.mpr hne

section
variable {M M1 : Word → BitVec 8} {base out c s p F : Word} {g g0 : Fin 32 → Word}

/-- The call to `read_item` at `0x2a` and the rest of the function. -/
theorem nx_call {n pos : Nat} (hF : s + BitVec.ofNat 32 116 = F) (hb : base.toNat % 2 = 0)
    (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (halc : c.toNat % 4 = 0) (hn : n < 2 ^ 32)
    (hpos : pos < 2 ^ 32) (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n ≤ 2 ^ 32)
    (hrc : RiCode M (base + 0xFFFFF7E0)) (hrs : RiSep s 148 (base + 0xFFFFF7E0))
    (hSc : Sep s 148 base jsonNextElementCode.length) (hSp : Sep s 148 p n) (hso : Sep out 12 s 148)
    (hcs : Sep c 12 s 148) (hoc : Sep out 12 c 12) (hsc : Sep out 12 base jsonNextElementCode.length)
    (hcc : Sep c 12 base jsonNextElementCode.length) (hO1 : Out M M1 s 148) (hv : NxSaved F g0 M1)
    (h8 : g 8 = out) (h9 : g 9 = c) (ha1 : g a1 = p) (ha2 : g a2 = BitVec.ofNat 32 n)
    (ha3 : g a3 = BitVec.ofNat 32 pos) (hsp : g sp = F) (hsp0 : g0 sp = F + BitVec.ofNat 32 0x20)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ nxE → g x = g0 x) :
    WP jsonNextElementCode base (RPost (g0 ra) (fun M' => ElemResF M M' out c s 148
      (elemRes p ((readItem (memBytes M p n) pos).map fun x => some (pos, x.1 - pos, x.2)))) g0) M1 0x2A g := by
  refine WP.zero fun hz => ?_
  have halF : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add hal (k := 116) (by decide)
  have hF8 : F + 8 = s + BitVec.ofNat 32 124 := by rw [← hF, BitVec.add_assoc]; rfl
  have hd : memBytes M1 p n = memBytes M p n := hO1.bytes hSp
  have hS1 : Slots nxCs F M1 M1 := Slots.refl _ _ _
  refine WP.aluImm nx_at_2a ?_; wn
  refine WP.callReadItem (tb := base + 0xFFFFF7E0) (out := F + 8) (s := s) (p := p) (n := n) (pos := pos)
    nx_at_2c nx_at_30 (by simp only [BitVec.add_assoc]; rfl) (even_at base hb 0xFFFFF7E0 (by decide))
    (by decide) (hrc.out hO1 hrs) (hrs.low (by decide)) (by (try rsimp); rw [hsp, ev_add])
    (by (try rsimp); exact ha1) (by (try rsimp); exact ha2) (by (try rsimp); exact ha3)
    (by (try rsimp); rw [hsp, hF]) hn hpos hal (aligned_add halF (k := 8) (by decide)) (sep_low hSp (by decide))
    (by rw [hF8]; have := sep_offsets s (c := 124) (n := 12) (d := 0) (k := 116) (Or.inr (by decide)) (by decide)
          (by decide); rwa [add_ofNat_zero] at this)
    (by rw [hF8]; exact hrs.ri.sub (by decide)) (sep_low hSc (by decide)) (by rw [hF8]; exact hSc.sub (by decide))
    fun m2 hR => ?_
  rw [hd] at hR
  obtain ⟨Ma, hOa, hCR⟩ := hR
  have hO2 : Out M m2.mem s 148 := hO1.trans ((hOa.mono (by decide)).trans
    (Out.upK (c := 124) hF8.symm hCR.out (by decide)))
  have hcs1 : ∀ c, c ∈ nxCs → 116 + c + 4 ≤ 2 ^ 32 := by decide
  have hcs2 : ∀ c, c ∈ nxCs → (c + 4 ≤ 8 ∨ 8 + 12 ≤ c) ∧ c + 4 ≤ 2 ^ 32 := by decide
  have hS2 : Slots nxCs F M1 m2.mem :=
    (hS1.out hOa (fun c hc => sep_below116 hF (hcs1 c hc))).out hCR.out (slots_sep F hcs2 (by decide))
  have hso1 : Sep out 1 base jsonNextElementCode.length := sep_low hsc (by decide)
  have hsoF : Sep out 12 F 32 := by rw [← hF]; exact hso.subR (by decide)
  have hscF : Sep (c + 8) 4 F 32 := by rw [← hF]; exact (hcs.sub (c := 8) (l := 4) (by decide)).subR (by decide)
  have hcs3 : ∀ c, c ∈ nxCs → c + 4 ≤ 32 := by decide
  refine WP.zero fun hz2 => ?_
  refine WP.lw nx_at_34 (by (try rsimp); rw [hsp]; exact aligned_add halF (k := 8) (by decide)) ?_; wn
  generalize hri : readItem (memBytes M p n) pos = r at hCR ⊢
  rcases r with _ | ⟨ee, a⟩
  · obtain ⟨-, h0, h4⟩ := hCR
    refine WP.branch nx_at_36 (fun e => ?_) (fun e => ?_) <;> wn
    · refine WP.lbu nx_at_46 ?_; wn
      refine WP.sb nx_at_4a (by (try rsimp); rw [h8]; exact hsc.sub (c := 1) (by decide)) ?_; wn
      refine WP.aluImm nx_at_4e ?_; wn
      refine WP.sb nx_at_50 (by (try rsimp); rw [h8]; first | exact hso1 | exact hsc.sub (c := 0) (by decide)) ?_; wn
      have h4' : m2.mem (F + 12) = 32 := by rw [← h4, BitVec.add_assoc]; rfl
      rw [h8, hsp, add_lit_zero, h4', ri_ze, show (aluEval .add 0 1).extractLsb' 0 8 = (1 : BitVec 8) by decide]
      have hE := elem_err m2.mem out c
      exact nx_epi (by (try rsimp); exact hsp) (hE.slots hS2 (slots_sep_out hsoF hcs3) (slots_sep_out hscF hcs3))
        hv hsp0 hret halF hz0 (by keepz hz0) ⟨m2.mem, hO2, hE⟩
    · exfalso; (try rsimp at e); rw [hsp, h0] at e; exact absurd e (by decide)
  · obtain ⟨-, hq, hl, ha⟩ := hCR
    have hbd := readItem_bd hri
    rw [memBytes_length] at hbd
    have hl' : memLoad32 m2.mem (F + 12) = BitVec.ofNat 32 (ee - pos) := by rw [← hl, BitVec.add_assoc]; rfl
    have ha' : memLoad32 m2.mem (F + 16) = BitVec.ofNat 32 a := by rw [← ha, BitVec.add_assoc]; rfl
    refine WP.branch nx_at_36 (fun e => ?_) (fun e => ?_) <;> wn
    · exfalso; (try rsimp at e); rw [hsp, hq, nx_q0 hp0 hpn (by omega)] at e; exact absurd e (by decide)
    refine WP.aluImm nx_at_38 ?_; wn
    refine WP.lw nx_at_3a (by (try rsimp); rw [hsp]; exact aligned_add halF (k := 16) (by decide)) ?_; wn
    refine WP.lw nx_at_3c (by (try rsimp); rw [hsp]; exact aligned_add halF (k := 12) (by decide)) ?_; wn
    refine WP.sw nx_at_3e (by (try rsimp); rw [h9]; exact aligned_add halc (k := 8) (by decide))
      (by (try rsimp); rw [h9]; exact hcc.sub (c := 8) (by decide)) ?_; wn
    refine WP.sw nx_at_40 (by (try rsimp); rw [h8]; exact aligned_add halo (k := 4) (by decide))
      (by (try rsimp); rw [h8]; exact hsc.sub (c := 4) (by decide)) ?_; wn
    refine WP.sw nx_at_42 (by (try rsimp); rw [h8]; exact aligned_add halo (k := 8) (by decide))
      (by (try rsimp); rw [h8]; exact hsc.sub (c := 8) (by decide)) ?_; wn
    refine WP.jal nx_at_44 (by decide) ?_; wn
    refine WP.sb nx_at_50 (by (try rsimp); rw [h8]; first | exact hso1 | exact hsc.sub (c := 0) (by decide)) ?_; wn
    rw [h8, h9, hsp, add_lit_zero, hq, hl', ha', show (aluEval .add 0 0).extractLsb' 0 8 = (0 : BitVec 8) by decide]
    have hE := elem_ok m2.mem (p + BitVec.ofNat 32 pos) (ee - pos) a hoc
    exact nx_epi (by (try rsimp); exact hsp) (hE.slots hS2 (slots_sep_out hsoF hcs3) (slots_sep_out hscF hcs3))
      hv hsp0 hret halF hz0 (by keepz hz0) ⟨m2.mem, hO2, hE⟩

end

section
variable {M : Word → BitVec 8} {base out c s p : Word} {f : Fin 32 → Word}

theorem nx_wp {n pos : Nat} (h0 : f a0 = out) (h1 : f a1 = c) (hsp : f sp = s + BitVec.ofNat 32 148)
    (hret : f ra &&& ~~~1 = f ra) (hb : base.toNat % 2 = 0) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0)
    (halc : c.toNat % 4 = 0) (hmp : memLoad32 M c = p) (hmn : memLoad32 M (c + 4) = BitVec.ofNat 32 n)
    (hmq : memLoad32 M (c + 8) = BitVec.ofNat 32 pos) (hn : n < 2 ^ 32) (hpos : pos < 2 ^ 32)
    (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n ≤ 2 ^ 32)
    (hrc : RiCode M (base + 0xFFFFF7E0)) (hrs : RiSep s 148 (base + 0xFFFFF7E0))
    (hSc : Sep s 148 base jsonNextElementCode.length) (hSp : Sep s 148 p n) (hso : Sep out 12 s 148)
    (hcs : Sep c 12 s 148) (hoc : Sep out 12 c 12) (hsc : Sep out 12 base jsonNextElementCode.length)
    (hcc : Sep c 12 base jsonNextElementCode.length) :
    WP jsonNextElementCode base (RPost (f ra) (fun M' => ElemResF M M' out c s 148
      (elemRes p (nextElement (memBytes M p n) pos))) f) M 0 f := by
  refine WP.zero fun hz => ?_
  have esp : aluEval .add (f sp) 0xFFFFFFE0 = s + 116 := by rw [hsp, ev_add, BitVec.add_assoc]; rfl
  refine WP.aluImm nx_at_0 ?_; wn
  rw [esp]
  generalize hF : s + 116 = F
  have hF' : s + BitVec.ofNat 32 116 = F := hF
  have halF : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add hal (k := 116) (by decide)
  have hsp0 : f sp = F + BitVec.ofNat 32 0x20 := by rw [hsp, ← hF, BitVec.add_assoc]; rfl
  refine WP.sw nx_at_2 (by rsimp; exact aligned_add halF (k := 0x1C) (by decide))
    (by rsimp; exact nxSepF hF' hSc (by decide)) ?_; wn
  refine WP.sw nx_at_4 (by rsimp; exact aligned_add halF (k := 0x18) (by decide))
    (by rsimp; exact nxSepF hF' hSc (by decide)) ?_; wn
  refine WP.sw nx_at_6 (by rsimp; exact aligned_add halF (k := 0x14) (by decide))
    (by rsimp; exact nxSepF hF' hSc (by decide)) ?_; wn
  change WP jsonNextElementCode base _ (nxM1 M F f) 0x8 _
  obtain ⟨hO1, hv⟩ := nx_pro M F f
  have hO1' : Out M (nxM1 M F f) s 148 := Out.upK hF' hO1 (by decide)
  have hc4 : ∀ d, d + 4 ≤ 12 → Sep s 148 (c + BitVec.ofNat 32 d) 4 := fun d hd => (hcs.sub hd).symm
  have mp : memLoad32 (nxM1 M F f) c = p := by
    have := hO1'.load32 (hc4 0 (by decide)); rw [add_ofNat_zero] at this; rw [this, hmp]
  have mn : memLoad32 (nxM1 M F f) (c + 4) = BitVec.ofNat 32 n := (hO1'.load32 (hc4 4 (by decide))).trans hmn
  have mq : memLoad32 (nxM1 M F f) (c + 8) = BitVec.ofNat 32 pos := (hO1'.load32 (hc4 8 (by decide))).trans hmq
  have hlen : (memBytes M p n).length = n := memBytes_length M p n
  have hS : Slots nxCs F (nxM1 M F f) (nxM1 M F f) := Slots.refl _ _ _
  have hsoF : Sep out 12 F 32 := by rw [← hF]; exact hso.subR (by decide)
  have hscF : Sep (c + 8) 4 F 32 := by rw [← hF]; exact (hcs.sub (c := 8) (l := 4) (by decide)).subR (by decide)
  have hcs3 : ∀ c, c ∈ nxCs → c + 4 ≤ 32 := by decide
  refine WP.alu nx_at_8 ?_; wn
  refine WP.lw nx_at_a (by (try rsimp); rw [h1]; exact aligned_add halc (k := 4) (by decide)) ?_; wn
  refine WP.lw nx_at_c (by (try rsimp); rw [h1]; exact aligned_add halc (k := 8) (by decide)) ?_; wn
  refine WP.lw nx_at_e (by (try rsimp); rw [h1, add_lit_zero]; exact halc) ?_; wn
  refine WP.alu nx_at_10 ?_; wn
  refine WP.branch nx_at_12 (fun e => ?_) (fun e => ?_) <;> wn
  · (try rsimp at e); rw [h1, mq, mn, br_bgeu hpos hn] at e
    have hge : ¬ pos < n := not_dec_true e
    rw [nextElement, ite_eq_right_of_eq_false _ _ (eq_false (by rw [hlen]; exact fun h => hge h.1))]
    exact nx_call hF' hb hal halo halc hn hpos hp0 hpn hrc hrs hSc hSp hso hcs hoc hsc hcc hO1' hv
      (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h0)
      (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h1)
      (by (try rsimp); rw [h1, add_lit_zero, mp]) (by (try rsimp); rw [h1, mn]) (by (try rsimp); rw [h1, mq])
      (by rsimp) hsp0 hret hz (by keepz hz)
  (try rsimp at e); rw [h1, mq, mn, br_bgeu hpos hn] at e
  have hlt : pos < n := not_dec_false e
  have hbyte : nxM1 M F f (p + BitVec.ofNat 32 pos) = M (p + BitVec.ofNat 32 pos) := hO1'.byte hSp hlt
  have hgd : (memBytes M p n).getD pos 0 = (M (p + BitVec.ofNat 32 pos)).toNat := memBytes_getD hlt
  generalize hB : M (p + BitVec.ofNat 32 pos) = B at hbyte hgd
  refine WP.alu nx_at_16 ?_; wn
  refine WP.lbu nx_at_1a ?_; wn
  refine WP.aluImm nx_at_1e ?_; wn
  refine WP.branch nx_at_22 (fun e => ?_) (fun e => ?_) <;> wn
  · (try rsimp at e); rw [h1, add_lit_zero, add_lit_zero, mp, mq, ev_add p, hbyte, nx_rb'] at e
    have hq : B.toNat ≠ 93 := nbeq_true e
    rw [nextElement, ite_eq_right_of_eq_false _ _ (eq_false (by rw [hgd]; exact fun h => hq h.2))]
    exact nx_call hF' hb hal halo halc hn hpos hp0 hpn hrc hrs hSc hSp hso hcs hoc hsc hcc hO1' hv
      (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h0)
      (by (try rsimp); (try simp only [ev0, ev_mv hz]); exact h1)
      (by (try rsimp); rw [h1, add_lit_zero, mp]) (by (try rsimp); rw [h1, mn]) (by (try rsimp); rw [h1, mq])
      (by rsimp) hsp0 hret hz (by keepz hz)
  (try rsimp at e); rw [h1, add_lit_zero, add_lit_zero, mp, mq, ev_add p, hbyte, nx_rb'] at e
  have hq : B.toNat = 93 := nbeq_false e
  have hB93 : B = 93 := BitVec.eq_of_toNat_eq hq
  rw [nextElement, ite_eq_left_of_eq_true _ _ (eq_true ⟨by rw [hlen]; exact hlt, by rw [hgd, hq]⟩)]
  have hao4 : (out + 4).toNat % 4 = 0 := aligned_add halo (k := 4) (by decide)
  refine WP.sw nx_at_24 (by (try rsimp); (try simp only [ev0, ev_mv hz]); rw [h0]; exact hao4)
    (by (try rsimp); (try simp only [ev0, ev_mv hz]); rw [h0]; exact hsc.sub (c := 4) (by decide)) ?_; wn
  refine WP.jal nx_at_28 (by decide) ?_; wn
  have hso1 : Sep out 1 base jsonNextElementCode.length := sep_low hsc (by decide)
  refine WP.sb nx_at_50 (by (try rsimp); (try simp only [ev0, ev_mv hz]); rw [h0, add_lit_zero]; exact hso1) ?_; wn
  rw [ev0, h0, add_lit_zero, add_lit_zero, add_lit_zero, h1, mp, mq, ev_add p, hbyte, hB93, nx_rb0]
  have hE := elem_end (nxM1 M F f) out c
  exact nx_epi (by rsimp) (hE.slots hS (slots_sep_out hsoF hcs3) (slots_sep_out hscF hcs3)) hv hsp0 hret halF hz
    (by keepz hz) ⟨_, hO1', hE⟩

end

/-- `next_element` on the cursor at `c`, whose words are the array's pointer
`p`, its length `n`, and the position `pos`, with `sp = s + 148`, returns
with `out` holding `elemRes p (nextElement doc pos)` for the `n` bytes at `p`:
`Ok(None)` at a closing bracket, `Ok(Some(value))` with the cursor's position
moved past the value, or the error byte `0x20`. It changes memory only in
the 148 bytes at `s`, the 12 bytes at `out`, and the cursor's position word,
and keeps every register outside `jClob`. `read_item` and its callees are at
the offsets `RiCode` lists from `base + 0xFFFFF7E0`. -/
theorem jsonNextElement_correct (m : Machine) {base retAddr out c s p : Word} {n pos : Nat}
    (hb : base.toNat % 2 = 0) (hc : CodeIn m.mem base jsonNextElementCode)
    (hrc : RiCode m.mem (base + 0xFFFFF7E0)) (hpc : m.pc = base) (ha0 : reg m a0 = out) (ha1 : reg m a1 = c)
    (hsp : reg m sp = s + BitVec.ofNat 32 148) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (halc : c.toNat % 4 = 0)
    (hmp : memLoad32 m.mem c = p) (hmn : memLoad32 m.mem (c + 4) = BitVec.ofNat 32 n)
    (hmq : memLoad32 m.mem (c + 8) = BitVec.ofNat 32 pos) (hn : n < 2 ^ 32) (hpos : pos < 2 ^ 32)
    (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n ≤ 2 ^ 32) (hrs : RiSep s 148 (base + 0xFFFFF7E0))
    (hSc : Sep s 148 base jsonNextElementCode.length) (hSp : Sep s 148 p n) (hso : Sep out 12 s 148)
    (hcs : Sep c 12 s 148) (hoc : Sep out 12 c 12) (hsc : Sep out 12 base jsonNextElementCode.length)
    (hcc : Sep c 12 base jsonNextElementCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      ElemResF m.mem m'.mem out c s 148 (elemRes p (nextElement (memBytes m.mem p n) pos)) ∧
      ∀ r, r ∉ jClob → reg m' r = reg m r := by
  obtain ⟨m', st, hpc', hR, hfr⟩ := WP.run (nx_wp ha0 ha1 hsp (by rw [hra]; exact hret) hb hal halo halc hmp hmn
    hmq hn hpos hp0 hpn hrc hrs hSc hSp hso hcs hoc hsc hcc) hb hc hpc
  exact ⟨m', st, hpc'.trans hra, hR, hfr⟩

end C3.RV32
