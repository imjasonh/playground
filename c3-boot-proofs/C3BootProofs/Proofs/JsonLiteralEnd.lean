import C3BootProofs.Proofs.JsonCalls
import C3BootProofs.Proofs.SliceEq

/-!
# `json::literal_end`, as compiled

`literal_end(doc, pos)` stores `Ok` of the position after the `true`,
`false`, or `null` at `pos`, or `Err(Json)`, at `out`. It saves `ra` and
`s0`–`s6` in a 64-byte frame, builds a table of the three words there, and
compares each word that fits with `equal_same_length` at `base - 0xC00`.
That callee saves `ra` in the 4 bytes below the frame, so the stack region
is the 68 bytes below `sp`. The words are read-only data at `0x3FCC476A`,
`0x3FCC48F2`, and `0x3FCC4766`, which the extracted image does not hold:
callers supply them as `LitData`.
-/

namespace C3.Json

/-- The literals, in the order `literal_end` tries them. -/
def litWords : List Bytes := [ascii!"true", ascii!"false", ascii!"null"]

/-- The position after the first of `ws` that `rest`, the bytes from
`pos`, starts with. -/
def litScan (rest : Bytes) (pos : Nat) : List Bytes → Option Nat
  | [] => none
  | w :: ws => if w.length ≤ rest.length ∧ rest.take w.length = w then some (pos + w.length)
    else litScan rest pos ws

/-- `literal_end`: the position after the literal at `pos`. -/
def literalEnd (d : Bytes) (pos : Nat) : Option Nat :=
  if d.length < pos then none else litScan (d.drop pos) pos litWords

end C3.Json

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem le_at_0 : fetchRel jsonLiteralEndCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem le_at_2 : fetchRel jsonLiteralEndCode 0x2 = some (.store .sw sp ra 0x3C, 2) := by decide
theorem le_at_4 : fetchRel jsonLiteralEndCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x38, 2) := by decide
theorem le_at_6 : fetchRel jsonLiteralEndCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x34, 2) := by decide
theorem le_at_8 : fetchRel jsonLiteralEndCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x30, 2) := by decide
theorem le_at_a : fetchRel jsonLiteralEndCode 0xA = some (.store .sw sp (19 : Fin 32) 0x2C, 2) := by decide
theorem le_at_c : fetchRel jsonLiteralEndCode 0xC = some (.store .sw sp (20 : Fin 32) 0x28, 2) := by decide
theorem le_at_e : fetchRel jsonLiteralEndCode 0xE = some (.store .sw sp (21 : Fin 32) 0x24, 2) := by decide
theorem le_at_10 : fetchRel jsonLiteralEndCode 0x10 = some (.store .sw sp (22 : Fin 32) 0x20, 2) := by decide
theorem le_at_12 : fetchRel jsonLiteralEndCode 0x12 = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem le_at_14 : fetchRel jsonLiteralEndCode 0x14 = some (.branch .bgeu a2 a3 0x20, 4) := by decide
theorem le_at_18 : fetchRel jsonLiteralEndCode 0x18 = some (.lui a0 0x2000, 2) := by decide
theorem le_at_1a : fetchRel jsonLiteralEndCode 0x1A = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem le_at_1c : fetchRel jsonLiteralEndCode 0x1C = some (.store .sh (18 : Fin 32) a0 0x0, 4) := by decide
theorem le_at_20 : fetchRel jsonLiteralEndCode 0x20 = some (.load .lw ra sp 0x3C, 2) := by decide
theorem le_at_22 : fetchRel jsonLiteralEndCode 0x22 = some (.load .lw (8 : Fin 32) sp 0x38, 2) := by decide
theorem le_at_24 : fetchRel jsonLiteralEndCode 0x24 = some (.load .lw (9 : Fin 32) sp 0x34, 2) := by decide
theorem le_at_26 : fetchRel jsonLiteralEndCode 0x26 = some (.load .lw (18 : Fin 32) sp 0x30, 2) := by decide
theorem le_at_28 : fetchRel jsonLiteralEndCode 0x28 = some (.load .lw (19 : Fin 32) sp 0x2C, 2) := by decide
theorem le_at_2a : fetchRel jsonLiteralEndCode 0x2A = some (.load .lw (20 : Fin 32) sp 0x28, 2) := by decide
theorem le_at_2c : fetchRel jsonLiteralEndCode 0x2C = some (.load .lw (21 : Fin 32) sp 0x24, 2) := by decide
theorem le_at_2e : fetchRel jsonLiteralEndCode 0x2E = some (.load .lw (22 : Fin 32) sp 0x20, 2) := by decide
theorem le_at_30 : fetchRel jsonLiteralEndCode 0x30 = some (.aluImm .add sp sp 0x40, 2) := by decide
theorem le_at_32 : fetchRel jsonLiteralEndCode 0x32 = some (.jalr x0 ra 0x0, 2) := by decide
theorem le_at_34 : fetchRel jsonLiteralEndCode 0x34 = some (.alu .add (19 : Fin 32) x0 a3, 2) := by decide
theorem le_at_36 : fetchRel jsonLiteralEndCode 0x36 = some (.alu .sub (21 : Fin 32) a2 a3, 4) := by decide
theorem le_at_3a : fetchRel jsonLiteralEndCode 0x3A = some (.alu .add (20 : Fin 32) a1 a3, 4) := by decide
theorem le_at_3e : fetchRel jsonLiteralEndCode 0x3E = some (.lui a0 0x3FCC4000, 4) := by decide
theorem le_at_42 : fetchRel jsonLiteralEndCode 0x42 = some (.aluImm .add a0 a0 0x76A, 4) := by decide
theorem le_at_46 : fetchRel jsonLiteralEndCode 0x46 = some (.aluImm .add a1 x0 0x4, 2) := by decide
theorem le_at_48 : fetchRel jsonLiteralEndCode 0x48 = some (.lui a2 0x3FCC5000, 4) := by decide
theorem le_at_4c : fetchRel jsonLiteralEndCode 0x4C = some (.aluImm .add a2 a2 0xFFFFF8F2, 4) := by decide
theorem le_at_50 : fetchRel jsonLiteralEndCode 0x50 = some (.aluImm .add a3 x0 0x5, 2) := by decide
theorem le_at_52 : fetchRel jsonLiteralEndCode 0x52 = some (.store .sw sp a0 0x8, 2) := by decide
theorem le_at_54 : fetchRel jsonLiteralEndCode 0x54 = some (.store .sw sp a1 0xC, 2) := by decide
theorem le_at_56 : fetchRel jsonLiteralEndCode 0x56 = some (.store .sw sp a2 0x10, 2) := by decide
theorem le_at_58 : fetchRel jsonLiteralEndCode 0x58 = some (.store .sw sp a3 0x14, 2) := by decide
theorem le_at_5a : fetchRel jsonLiteralEndCode 0x5A = some (.lui a0 0x3FCC4000, 4) := by decide
theorem le_at_5e : fetchRel jsonLiteralEndCode 0x5E = some (.aluImm .add a0 a0 0x766, 4) := by decide
theorem le_at_62 : fetchRel jsonLiteralEndCode 0x62 = some (.aluImm .add (9 : Fin 32) sp 0xC, 2) := by decide
theorem le_at_64 : fetchRel jsonLiteralEndCode 0x64 = some (.store .sw sp a0 0x18, 2) := by decide
theorem le_at_66 : fetchRel jsonLiteralEndCode 0x66 = some (.store .sw sp a1 0x1C, 2) := by decide
theorem le_at_68 : fetchRel jsonLiteralEndCode 0x68 = some (.aluImm .add (22 : Fin 32) x0 0x3, 2) := by decide
theorem le_at_6a : fetchRel jsonLiteralEndCode 0x6A = some (.branch .beq (22 : Fin 32) x0 0xFFFFFFAE, 4) := by decide
theorem le_at_6e : fetchRel jsonLiteralEndCode 0x6E = some (.load .lw (8 : Fin 32) (9 : Fin 32) 0x0, 2) := by decide
theorem le_at_70 : fetchRel jsonLiteralEndCode 0x70 = some (.branch .bltu (21 : Fin 32) (8 : Fin 32) 0x16, 4) := by decide
theorem le_at_74 : fetchRel jsonLiteralEndCode 0x74 = some (.load .lw a0 (9 : Fin 32) 0xFFFFFFFC, 4) := by decide
theorem le_at_78 : fetchRel jsonLiteralEndCode 0x78 = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem le_at_7a : fetchRel jsonLiteralEndCode 0x7A = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem le_at_7c : fetchRel jsonLiteralEndCode 0x7C = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem le_at_80 : fetchRel jsonLiteralEndCode 0x80 = some (.jalr ra ra 0x384, 4) := by decide
theorem le_at_84 : fetchRel jsonLiteralEndCode 0x84 = some (.branch .bne a0 x0 0xC, 2) := by decide
theorem le_at_86 : fetchRel jsonLiteralEndCode 0x86 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x8, 2) := by decide
theorem le_at_88 : fetchRel jsonLiteralEndCode 0x88 = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem le_at_8a : fetchRel jsonLiteralEndCode 0x8A = some (.branch .bne (22 : Fin 32) x0 0xFFFFFFE4, 4) := by decide
theorem le_at_8e : fetchRel jsonLiteralEndCode 0x8E = some (.jal x0 0xFFFFFF8A, 2) := by decide
theorem le_at_90 : fetchRel jsonLiteralEndCode 0x90 = some (.alu .add (8 : Fin 32) (8 : Fin 32) (19 : Fin 32), 2) := by decide
theorem le_at_92 : fetchRel jsonLiteralEndCode 0x92 = some (.store .sb (18 : Fin 32) x0 0x0, 4) := by decide
theorem le_at_96 : fetchRel jsonLiteralEndCode 0x96 = some (.store .sw (18 : Fin 32) (8 : Fin 32) 0x4, 4) := by decide
theorem le_at_9a : fetchRel jsonLiteralEndCode 0x9A = some (.jal x0 0xFFFFFF86, 2) := by decide

/-- The literals' bytes at the addresses `literal_end` reads them from. -/
def LitData (M : Word → BitVec 8) : Prop :=
  memBytes M 0x3FCC476A 4 = ascii!"true" ∧ memBytes M 0x3FCC48F2 5 = ascii!"false" ∧
    memBytes M 0x3FCC4766 4 = ascii!"null"

/-- The registers `equal_same_length` may change. -/
abbrev eslClob : List (Fin 32) := [a0, a1, a2, a3, a4]

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat}
  {f : Fin 32 → Word}

/-- A call to `equal_same_length(q1, q2, l)` with the code at `tb`, whose
saved `ra` goes to the 4 bytes at `r`. -/
theorem WP.callEsl {hi lo tb q1 q2 r : Word} {l : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hct : CodeIn M tb equalSameLengthCode) (hcm : CodeIn M (tb + 0xD3BE) memcmpCode)
    (h0 : f a0 = q1) (ha1 : f a1 = q2) (ha2 : f a2 = BitVec.ofNat 32 l) (hl : l < 2 ^ 32)
    (hsp : f sp + 0xFFFFFFFC = r) (hal : (f sp).toNat % 4 = 0)
    (sSC : Sep r 4 tb equalSameLengthCode.length) (sSM : Sep r 4 (tb + 0xD3BE) memcmpCode.length)
    (sSP : Sep r 4 q1 l) (sSQ : Sep r 4 q2 l) (hsc : Sep r 4 base code.length)
    (k : ∀ m2 : Machine, reg m2 a0 = (if memBytes M q1 l = memBytes M q2 l then 1 else 0) → Out M m2.mem r 4 →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 eslClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := eslClob)
    (P := fun m2 => reg m2 a0 = (if memBytes M q1 l = memBytes M q2 l then 1 else 0) ∧ Out M m2.mem r 4)
    h1 h2 (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => hP.2.codeIn hc hsc) (fun m2 hP => k m2 hP.1 hP.2)
  have hs1 : reg m1 sp = f sp := by rw [hreg1]; rsimp
  obtain ⟨m2, c2, pc2, r0, hfr, hmf⟩ := equalSameLength_correct m1 (base := tb) (p := q1) (q := q2) (n := l) htb
    (by rw [hmem1]; exact hct) (by rw [hmem1]; exact hcm) hpc1 (by rw [hreg1]; rsimp; exact h0)
    (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2) hl
    (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev))
    (by rw [hs1]; exact hal) (by rw [hs1, hsp]; exact sSC) (by rw [hs1, hsp]; exact sSM)
    (by rw [hs1, hsp]; exact sSP) (by rw [hs1, hsp]; exact sSQ)
  rw [hmem1] at r0
  refine ⟨m2, c2, pc2, ⟨r0, fun x hx => ?_⟩, fun x hx => ?_⟩
  · rw [hmf x (by rw [hs1, hsp]; exact hx.symm), hmem1]
  · simp only [eslClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨n0, n1, n2, n3, n4⟩ := hx
    exact hfr x n0 n1 n2 n3 n4

end

theorem usizeRes_ok' (M : Word → BitVec 8) (out : Word) (v : Nat) :
    UsizeRes M (memStore32 (memStore8 M out 0) (out + 4) (BitVec.ofNat 32 v)) out (some v) := by
  have h4 : Sep out 1 (out + 4) 4 := by
    have := sep_offsets out (c := 0) (n := 1) (d := 4) (k := 4) (Or.inl (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  refine ⟨fun x hx => ?_, ?_, memLoad32_store32_same _ _ _⟩
  · rw [memStore32_get_sep, memStore8_ne (sep_byte0 hx (by decide))]
    intro i hi j hj e
    obtain rfl : j = 0 := by omega
    rw [add_ofNat_zero, show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc] at e
    exact sep_byte hx (j := 4 + i) (by omega) e.symm
  · rw [memStore32_get_sep h4.symm, memStore8_same]

/-- A word in the frame at `s + 4` is apart from the 4 bytes at `s`. -/
theorem sep_below {s F : Word} (hF : s + 4 = F) {c : Nat} (hc : 4 + c + 4 ≤ 2 ^ 32) :
    Sep s 4 (F + BitVec.ofNat 32 c) 4 := by
  subst hF
  have := sep_offsets s (c := 0) (n := 4) (d := 4 + c) (k := 4) (Or.inl (by omega)) (by omega) (by omega)
  rwa [add_ofNat_zero, ← add_ofNat_assoc] at this

theorem jmemBytes_take (M : Word → BitVec 8) (p : Word) {k n : Nat} (h : k ≤ n) :
    (memBytes M p n).take k = memBytes M p k := by
  unfold memBytes; rw [← List.map_take, List.take_range, Nat.min_eq_left h]

theorem sep68_4 {s x : Word} {l : Nat} (h : Sep s 68 x l) : Sep s 4 x l := by
  have := h.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this

theorem esl_mc (base : Word) : base + 0xFFFFF400 + 0xD3BE = base + 0xC7BE := by rw [BitVec.add_assoc]; rfl

theorem le_below (s : Word) : s + 4 + 0xFFFFFFFC = s := by
  rw [BitVec.add_assoc, show (4 : Word) + 0xFFFFFFFC = 0 from by decide]; exact BitVec.add_zero s

/-- The registers that `literal_end`'s loop changes in one iteration. -/
abbrev itL : List (Fin 32) := [8, ra, a0, a1, a2, a3, a4]

theorem itL_sub : ∀ x, x ∈ itL → x ∈ jClob ++ [ra, sp, 8, 9, 18, 19, 20, 21, 22] := by decide

/-- The registers that `literal_end`'s loop changes. -/
abbrev kL : List (Fin 32) := itL ++ [9, 22]

theorem kL_sub : ∀ x, x ∈ kL → x ∈ jClob ++ [ra, sp, 8, 9, 18, 19, 20, 21, 22] := by decide

theorem kL_comp {f g h g' : Fin 32 → Word} (hh : ∀ x, x ∉ kL → h x = f x) (hg : ∀ x, x ∉ itL → g x = h x)
    (eo : ∀ x, x ≠ 9 → x ≠ 22 → g' x = g x) : ∀ x, x ∉ kL → g' x = f x := by
  intro x hx
  have n9 : x ≠ 9 := by rintro rfl; exact hx (by decide)
  have n22 : x ≠ 22 := by rintro rfl; exact hx (by decide)
  have ni : x ∉ itL := fun h => hx (List.mem_append_left _ h)
  rw [eo x n9 n22, hg x ni, hh x hx]

theorem kL_comp1 {f g : Fin 32 → Word} (hg : ∀ x, x ∉ itL → g x = f x) : ∀ x, x ∉ kL → g x = f x :=
  fun x hx => hg x fun h => hx (List.mem_append_left _ h)

/-- The registers `literal_end` changes before its epilogue restores the saved ones. -/
abbrev litL : List (Fin 32) := jClob ++ [ra, sp, 8, 9, 18, 19, 20, 21, 22]

/-- The frame offsets of the saved registers. -/
abbrev leCs : List Nat := [0x20, 0x24, 0x28, 0x2C, 0x30, 0x34, 0x38, 0x3C]

theorem leCs_le : ∀ c, c ∈ leCs → 4 + c + 4 ≤ 2 ^ 32 := by decide

/-- The saved registers in the frame at `F`. -/
def LeSaved (F : Word) (g0 : Fin 32 → Word) (M1 : Word → BitVec 8) : Prop :=
  memLoad32 M1 (F + BitVec.ofNat 32 0x3C) = g0 ra ∧ memLoad32 M1 (F + BitVec.ofNat 32 0x38) = g0 8 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x34) = g0 9 ∧ memLoad32 M1 (F + BitVec.ofNat 32 0x30) = g0 18 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x2C) = g0 19 ∧ memLoad32 M1 (F + BitVec.ofNat 32 0x28) = g0 20 ∧
    memLoad32 M1 (F + BitVec.ofNat 32 0x24) = g0 21 ∧ memLoad32 M1 (F + BitVec.ofNat 32 0x20) = g0 22

/-- Memory after the prologue. -/
def leM1 (M : Word → BitVec 8) (F : Word) (g0 : Fin 32 → Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (M) (F + 0x3c) (g0 ra)) (F + 0x38) (g0 8)) (F + 0x34) (g0 9)) (F + 0x30) (g0 18)) (F + 0x2c) (g0 19)) (F + 0x28) (g0 20)) (F + 0x24) (g0 21)) (F + 0x20) (g0 22)

theorem le_pro (M : Word → BitVec 8) (F : Word) (g0 : Fin 32 → Word) :
    Out M (leM1 M F g0) F 64 ∧ LeSaved F g0 (leM1 M F g0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((((((((out_store32 _ _ _).widen (d := 0x3c) (by decide)).trans
      ((out_store32 _ _ _).widen (d := 0x38) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x34) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x30) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x2c) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x28) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x24) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x20) (by decide)))
  · exact (ld_skip 0x3c 0x20 (by decide) (by decide) (by decide) (ld_skip 0x3c 0x24 (by decide) (by decide) (by decide) (ld_skip 0x3c 0x28 (by decide) (by decide) (by decide) (ld_skip 0x3c 0x2c (by decide) (by decide) (by decide) (ld_skip 0x3c 0x30 (by decide) (by decide) (by decide) (ld_skip 0x3c 0x34 (by decide) (by decide) (by decide) (ld_skip 0x3c 0x38 (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _))))))))
  · exact (ld_skip 0x38 0x20 (by decide) (by decide) (by decide) (ld_skip 0x38 0x24 (by decide) (by decide) (by decide) (ld_skip 0x38 0x28 (by decide) (by decide) (by decide) (ld_skip 0x38 0x2c (by decide) (by decide) (by decide) (ld_skip 0x38 0x30 (by decide) (by decide) (by decide) (ld_skip 0x38 0x34 (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _)))))))
  · exact (ld_skip 0x34 0x20 (by decide) (by decide) (by decide) (ld_skip 0x34 0x24 (by decide) (by decide) (by decide) (ld_skip 0x34 0x28 (by decide) (by decide) (by decide) (ld_skip 0x34 0x2c (by decide) (by decide) (by decide) (ld_skip 0x34 0x30 (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _))))))
  · exact (ld_skip 0x30 0x20 (by decide) (by decide) (by decide) (ld_skip 0x30 0x24 (by decide) (by decide) (by decide) (ld_skip 0x30 0x28 (by decide) (by decide) (by decide) (ld_skip 0x30 0x2c (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _)))))
  · exact (ld_skip 0x2c 0x20 (by decide) (by decide) (by decide) (ld_skip 0x2c 0x24 (by decide) (by decide) (by decide) (ld_skip 0x2c 0x28 (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _))))
  · exact (ld_skip 0x28 0x20 (by decide) (by decide) (by decide) (ld_skip 0x28 0x24 (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _)))
  · exact (ld_skip 0x24 0x20 (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _))
  · exact (memLoad32_store32_same _ _ _)

theorem le_tbl {code : List Nat} {Q : Post} {off : Nat} {M0 : Word → BitVec 8} {base F a b c d e g : Word}
    {f : Fin 32 → Word}
    (k : ∀ M2 : Word → BitVec 8, Out M0 M2 F 64 → Slots leCs F M0 M2 →
      memLoad32 M2 (F + 8) = a → memLoad32 M2 (F + 0xC) = b → memLoad32 M2 (F + 0x10) = c →
      memLoad32 M2 (F + 0x14) = d → memLoad32 M2 (F + 0x18) = e → memLoad32 M2 (F + 0x1C) = g →
      WP code base Q M2 off f) :
    WP code base Q (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M0
      (F + 8) a) (F + 0xC) b) (F + 0x10) c) (F + 0x14) d) (F + 0x18) e) (F + 0x1C) g) off f := by
  have hO : Out M0 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M0
      (F + 8) a) (F + 0xC) b) (F + 0x10) c) (F + 0x14) d) (F + 0x18) e) (F + 0x1C) g) F 32 :=
    (((((((out_store32 _ _ _).widen (d := 8) (by decide)).trans
      ((out_store32 _ _ _).widen (d := 0xC) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x10) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x14) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x18) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0x1C) (by decide)))
  refine k _ (Out.widen (d := 0) (by rw [add_ofNat_zero]; exact hO) (by decide)) (fun c hc => hO.load32 ?_)
    (ld_skip 0x8 0x1c (by decide) (by decide) (by decide) (ld_skip 0x8 0x18 (by decide) (by decide) (by decide) (ld_skip 0x8 0x14 (by decide) (by decide) (by decide) (ld_skip 0x8 0x10 (by decide) (by decide) (by decide) (ld_skip 0x8 0xc (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _)))))) (ld_skip 0xc 0x1c (by decide) (by decide) (by decide) (ld_skip 0xc 0x18 (by decide) (by decide) (by decide) (ld_skip 0xc 0x14 (by decide) (by decide) (by decide) (ld_skip 0xc 0x10 (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _)))))
    (ld_skip 0x10 0x1c (by decide) (by decide) (by decide) (ld_skip 0x10 0x18 (by decide) (by decide) (by decide) (ld_skip 0x10 0x14 (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _)))) (ld_skip 0x14 0x1c (by decide) (by decide) (by decide) (ld_skip 0x14 0x18 (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _)))
    (ld_skip 0x18 0x1c (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _)) (memLoad32_store32_same _ _ _)
  have hc' : 32 ≤ c ∧ c + 4 ≤ 2 ^ 32 := by revert c; decide
  have := sep_offsets F (c := 0) (n := 32) (d := c) (k := 4) (Or.inl hc'.1) (by decide) hc'.2
  rwa [add_ofNat_zero] at this

theorem Out.up4 {M M' : Word → BitVec 8} {s F : Word} {l k : Nat} (hF : s + 4 = F) (h : Out M M' F l)
    (hl : 4 + l ≤ k) : Out M M' s k := by
  subst hF; exact h.widen (d := 4) hl

section
variable {M M1 M2 : Word → BitVec 8} {base out s F p : Word} {f g0 : Fin 32 → Word}

theorem le_epi {Mf : Word → BitVec 8} {r : Option Nat} (hsp : f sp = F) (hS : Slots leCs F M1 Mf)
    (hv : LeSaved F g0 M1) (hsp0 : g0 sp = F + BitVec.ofNat 32 0x40) (hret : g0 ra &&& ~~~1 = g0 ra)
    (hal : F.toNat % 4 = 0) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ litL → f x = g0 x)
    (hR : UsizeResF M Mf out s 68 r) :
    WP jsonLiteralEndCode base (FPost (g0 ra) M out s 68 r g0) Mf 0x20 f := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := hv
  have e1 : memLoad32 Mf (F + 0x3C) = g0 ra := (hS 0x3C (by decide)).trans v1
  have e2 : memLoad32 Mf (F + 0x38) = g0 8 := (hS 0x38 (by decide)).trans v2
  have e3 : memLoad32 Mf (F + 0x34) = g0 9 := (hS 0x34 (by decide)).trans v3
  have e4 : memLoad32 Mf (F + 0x30) = g0 18 := (hS 0x30 (by decide)).trans v4
  have e5 : memLoad32 Mf (F + 0x2C) = g0 19 := (hS 0x2C (by decide)).trans v5
  have e6 : memLoad32 Mf (F + 0x28) = g0 20 := (hS 0x28 (by decide)).trans v6
  have e7 : memLoad32 Mf (F + 0x24) = g0 21 := (hS 0x24 (by decide)).trans v7
  have e8 : memLoad32 Mf (F + 0x20) = g0 22 := (hS 0x20 (by decide)).trans v8
  refine WP.lw le_at_20 (by rw [hsp]; exact aligned_add hal (k := 0x3C) (by decide)) ?_; wn
  refine WP.lw le_at_22 (by rsimp; rw [hsp]; exact aligned_add hal (k := 0x38) (by decide)) ?_; wn
  refine WP.lw le_at_24 (by rsimp; rw [hsp]; exact aligned_add hal (k := 0x34) (by decide)) ?_; wn
  refine WP.lw le_at_26 (by rsimp; rw [hsp]; exact aligned_add hal (k := 0x30) (by decide)) ?_; wn
  refine WP.lw le_at_28 (by rsimp; rw [hsp]; exact aligned_add hal (k := 0x2C) (by decide)) ?_; wn
  refine WP.lw le_at_2a (by rsimp; rw [hsp]; exact aligned_add hal (k := 0x28) (by decide)) ?_; wn
  refine WP.lw le_at_2c (by rsimp; rw [hsp]; exact aligned_add hal (k := 0x24) (by decide)) ?_; wn
  refine WP.lw le_at_2e (by rsimp; rw [hsp]; exact aligned_add hal (k := 0x20) (by decide)) ?_; wn
  refine WP.aluImm le_at_30 ?_; wn
  refine WP.ret le_at_32 ⟨?_, hR, ?_⟩
  · rsimp; rw [hsp, e1, add_lit_zero, hret]
  refine frame_of (L2 := [ra, sp, 8, 9, 18, 19, 20, 21, 22]) (by keepz hz0) fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rsimp
  · rw [hsp, e1]
  · rw [hsp, hsp0]; rfl
  · rw [hsp, e2]
  · rw [hsp, e3]
  · rw [hsp, e4]
  · rw [hsp, e5]
  · rw [hsp, e6]
  · rw [hsp, e7]
  · rw [hsp, e8]

theorem le_err (h18 : f 18 = out) (hsp : f sp = F) (hO : Out M M2 s 68) (hS : Slots leCs F M1 M2)
    (hv : LeSaved F g0 M1) (hsp0 : g0 sp = F + BitVec.ofNat 32 0x40) (hret : g0 ra &&& ~~~1 = g0 ra)
    (hal : F.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ litL → f x = g0 x)
    (hsoF : Sep out 8 F 64) (hsc : Sep out 8 base jsonLiteralEndCode.length) :
    WP jsonLiteralEndCode base (FPost (g0 ra) M out s 68 none g0) M2 0x18 f := by
  refine WP.zero fun hz => ?_
  refine WP.lui le_at_18 ?_; wn
  refine WP.aluImm le_at_1a ?_; wn
  have h0 : Sep out 2 base jsonLiteralEndCode.length := by
    have := hsc.sub (c := 0) (l := 2) (by decide); rwa [add_ofNat_zero] at this
  refine WP.sh le_at_1c (by (try rsimp); rw [h18, add_lit_zero]; omega)
    (by (try rsimp); rw [h18, add_lit_zero]; exact h0) ?_; wn
  (try rsimp)
  rw [h18, add_lit_zero]
  have hU := usizeRes_err16 M2 out
  exact le_epi (by rsimp; exact hsp) (hS.out hU.out (slots_sep_out hsoF (by decide))) hv hsp0 hret hal hz0
    (by keepz hz0) ⟨M2, hO, hU⟩

theorem le_found {v pos : Nat} (h18 : f 18 = out) (hsp : f sp = F) (h8 : f 8 = BitVec.ofNat 32 v)
    (h19 : f 19 = BitVec.ofNat 32 pos) (hO : Out M M2 s 68) (hS : Slots leCs F M1 M2)
    (hv : LeSaved F g0 M1) (hsp0 : g0 sp = F + BitVec.ofNat 32 0x40) (hret : g0 ra &&& ~~~1 = g0 ra)
    (hal : F.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ litL → f x = g0 x)
    (hsoF : Sep out 8 F 64) (hsc : Sep out 8 base jsonLiteralEndCode.length) :
    WP jsonLiteralEndCode base (FPost (g0 ra) M out s 68 (some (pos + v)) g0) M2 0x90 f := by
  refine WP.zero fun hz => ?_
  refine WP.alu le_at_90 ?_; wn
  have h0 : Sep out 1 base jsonLiteralEndCode.length := by
    have := hsc.shift (c := 0) (by decide); rwa [add_ofNat_zero] at this
  refine WP.sb le_at_92 (by (try rsimp); rw [h18, add_lit_zero]; exact h0) ?_; wn
  refine WP.sw le_at_96 (by rsimp; rw [h18]; exact aligned_add halo (k := 4) (by decide))
    (by rsimp; rw [h18]; exact hsc.sub (c := 4) (by decide)) ?_; wn
  refine WP.jal le_at_9a (by decide) ?_; wn
  (try rsimp)
  rw [h18, add_lit_zero, h8, h19, ev_add, ofNat_add_ofNat, Nat.add_comm v pos, show BitVec.extractLsb' 0 8 (0 : Word) = 0 from by decide]
  have hU := usizeRes_ok' M2 out (pos + v)
  exact le_epi (by rsimp; exact hsp) (hS.out hU.out (slots_sep_out hsoF (by decide))) hv hsp0 hret hal hz0
    (by keepz hz0) ⟨M2, hO, hU⟩

theorem le_it {w : Bytes} {ws : List Bytes} {q wp : Word} {n pos : Nat}
    (h18 : f 18 = out) (h19 : f 19 = BitVec.ofNat 32 pos) (h20 : f 20 = p + BitVec.ofNat 32 pos)
    (h21 : f 21 = BitVec.ofNat 32 (n - pos)) (hsp : f sp = F) (h9 : f 9 = q) (hF : s + 4 = F)
    (hpn : pos ≤ n) (hn : n < 2 ^ 32)
    (hl : memLoad32 M2 q = BitVec.ofNat 32 w.length) (hp : memLoad32 M2 (q + 0xFFFFFFFC) = wp)
    (hw : memBytes M wp w.length = w) (hwl : w.length ≤ 5)
    (hq : q.toNat % 4 = 0) (hq4 : (q + 0xFFFFFFFC).toNat % 4 = 0)
    (hO : Out M M2 s 68) (hSp : Sep s 68 p n) (hSw : Sep s 68 wp w.length)
    (hS : Slots leCs F M1 M2) (hv : LeSaved F g0 M1) (hsp0 : g0 sp = F + BitVec.ofNat 32 0x40)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ litL → f x = g0 x) (hsoF : Sep out 8 F 64)
    (hsc : Sep out 8 base jsonLiteralEndCode.length) (hb : base.toNat % 2 = 0)
    (hce : CodeIn M (base + 0xFFFFF400) equalSameLengthCode) (hcm : CodeIn M (base + 0xC7BE) memcmpCode)
    (sC : Sep s 68 (base + 0xFFFFF400) equalSameLengthCode.length)
    (sM : Sep s 68 (base + 0xC7BE) memcmpCode.length) (sCo : Sep s 68 base jsonLiteralEndCode.length)
    (hK : ∀ (g : Fin 32 → Word) (M3 : Word → BitVec 8), Out M2 M3 s 4 → (∀ x, x ∉ itL → g x = f x) →
      WP jsonLiteralEndCode base (FPost (g0 ra) M out s 68 (litScan ((memBytes M p n).drop pos) pos ws) g0)
        M3 0x86 g) :
    WP jsonLiteralEndCode base (FPost (g0 ra) M out s 68 (litScan ((memBytes M p n).drop pos) pos (w :: ws)) g0)
      M2 0x6E f := by
  refine WP.zero fun hz => ?_
  have hrl : ((memBytes M p n).drop pos).length = n - pos := by rw [List.length_drop, memBytes_length]
  have hlen32 : w.length < 2 ^ 32 := by omega
  have hnp : n - pos < 2 ^ 32 := by omega
  refine WP.lw le_at_6e (by rw [h9, add_lit_zero]; exact hq) ?_; wn
  rw [h9, add_lit_zero, hl]
  refine WP.branch le_at_70 (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    rw [h21, br_bltu hnp hlen32] at e
    have hlt : n - pos < w.length := of_decide_eq_true e
    rw [litScan, ite_eq_right_of_eq_false _ _ (eq_false fun h => absurd h.1 (by omega))]
    exact hK _ M2 (Out.refl _ _ _) (by keepz hz)
  rsimp at e
  rw [h21, br_bltu hnp hlen32] at e
  have hge : w.length ≤ n - pos := by have := of_decide_eq_false e; omega
  refine WP.lw le_at_74 (by rsimp; rw [h9]; exact hq4) ?_; wn
  refine WP.alu le_at_78 ?_; wn
  refine WP.alu le_at_7a ?_; wn
  have hsub : Sep s 68 (p + BitVec.ofNat 32 pos) w.length := hSp.subR (c := pos) (l := w.length) (by omega)
  refine WP.callEsl (tb := base + 0xFFFFF400) (q1 := wp) (q2 := p + BitVec.ofNat 32 pos) (l := w.length) (r := s)
    le_at_7c le_at_80 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hb 0xFFFFF400 (by decide))
    (by decide) (hO.codeIn hce sC) (by rw [esl_mc]; exact hO.codeIn hcm sM)
    (by rsimp; rw [h9, hp]) (by rsimp; simp only [ev0, ev_mv hz, h20]) (by rsimp; simp only [ev0, ev_mv hz])
    hlen32 (by rsimp; rw [hsp, ← hF, le_below]) (by rsimp; rw [hsp]; exact hal)
    (sep68_4 sC) (by rw [esl_mc]; exact sep68_4 sM) (sep68_4 hSw) (sep68_4 hsub) (sep68_4 sCo) fun m3 r0 h3 => ?_
  have eW : memBytes M2 wp w.length = w := (hO.bytes hSw).trans hw
  have eD : memBytes M2 (p + BitVec.ofNat 32 pos) w.length = ((memBytes M p n).drop pos).take w.length := by
    rw [hO.bytes hsub, jmemBytes_drop, jmemBytes_take _ _ hge]
  rw [eW, eD] at r0
  have hO3 : Out M m3.mem s 68 := hO.trans (Out.widen (d := 0) (by rw [add_ofNat_zero]; exact h3) (by decide))
  have hS3 : Slots leCs F M1 m3.mem := hS.out h3 fun c hc => sep_below hF (leCs_le c hc)
  refine WP.branch le_at_84 (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    rw [r0] at e
    by_cases hc : w = ((memBytes M p n).drop pos).take w.length
    · rw [litScan, ite_eq_left_of_eq_true _ _ (eq_true ⟨hrl ▸ hge, hc.symm⟩)]
      exact le_found (v := w.length) (by rsimp; exact h18) (by rsimp; exact hsp) (by rsimp; try simp only [ev0, ev_mv hz])
        (by rsimp; try exact h19) hO3 hS3 hv hsp0 hret hal halo hz0 (by keepz hz0) hsoF hsc
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at e; exact absurd e (by decide)
  rsimp at e
  rw [r0] at e
  by_cases hc : w = ((memBytes M p n).drop pos).take w.length
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at e; exact absurd e (by decide)
  rw [litScan, ite_eq_right_of_eq_false _ _ (eq_false fun h => hc h.2.symm)]
  exact hK _ m3.mem h3 (by keepz hz)

theorem le_step {Q : Post} {v : Word} (h22 : f 22 = v) (hv : branchTaken .bne (v + 0xFFFFFFFF) 0 = true)
    (K : ∀ g : Fin 32 → Word, g 9 = f 9 + 8 → g 22 = v + 0xFFFFFFFF → (∀ x, x ≠ 9 → x ≠ 22 → g x = f x) →
      WP jsonLiteralEndCode base Q M2 0x6E g) :
    WP jsonLiteralEndCode base Q M2 0x86 f := by
  refine WP.zero fun hz => ?_
  refine WP.aluImm le_at_86 ?_; wn
  refine WP.aluImm le_at_88 ?_; wn
  refine WP.branch le_at_8a (fun _ => ?_) (fun e => ?_) <;> wn
  · refine K _ (by rsimp; exact ev_add _ _) (by rsimp; rw [h22]; exact ev_add _ _) (fun x h9 h22 => ?_)
    rsimp
    simp only [h9, h22, ↓reduceIte]
    split
    · next h0 => rw [show x = 0 from Fin.ext h0, hz]
    · rfl
  rsimp at e
  rw [h22, ev_add] at e
  try rw [hz] at e
  rw [hv] at e
  exact absurd e (by decide)

theorem le_last (h22 : f 22 = 1) (h18 : f 18 = out) (hsp : f sp = F) (hO : Out M M2 s 68)
    (hS : Slots leCs F M1 M2) (hv : LeSaved F g0 M1) (hsp0 : g0 sp = F + BitVec.ofNat 32 0x40)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ litL → f x = g0 x) (hsoF : Sep out 8 F 64) (hsc : Sep out 8 base jsonLiteralEndCode.length) :
    WP jsonLiteralEndCode base (FPost (g0 ra) M out s 68 none g0) M2 0x86 f := by
  refine WP.zero fun hz => ?_
  refine WP.aluImm le_at_86 ?_; wn
  refine WP.aluImm le_at_88 ?_; wn
  refine WP.branch le_at_8a (fun e => ?_) (fun _ => ?_) <;> wn
  · rsimp at e
    rw [h22, ev_add] at e
    try rw [hz] at e
    exact absurd e (by decide)
  refine WP.jal le_at_8e (by decide) ?_; wn
  exact le_err (by rsimp; exact h18) (by rsimp; exact hsp) hO hS hv hsp0 hret hal halo hz0 (by keepz hz0) hsoF hsc

theorem le_loop {n pos : Nat} (h18 : f 18 = out) (h19 : f 19 = BitVec.ofNat 32 pos)
    (h20 : f 20 = p + BitVec.ofNat 32 pos) (h21 : f 21 = BitVec.ofNat 32 (n - pos)) (hsp : f sp = F)
    (h9 : f 9 = F + 0xC) (h22 : f 22 = 3) (hF : s + 4 = F) (hpn : pos ≤ n) (hn : n < 2 ^ 32)
    (t1 : memLoad32 M2 (F + 8) = 0x3FCC476A) (t2 : memLoad32 M2 (F + 0xC) = 4)
    (t3 : memLoad32 M2 (F + 0x10) = 0x3FCC48F2) (t4 : memLoad32 M2 (F + 0x14) = 5)
    (t5 : memLoad32 M2 (F + 0x18) = 0x3FCC4766) (t6 : memLoad32 M2 (F + 0x1C) = 4)
    (hlit : LitData M) (hO : Out M M2 s 68) (hSp : Sep s 68 p n) (hSn : Sep s 68 0x3FCC4766 8)
    (hSf : Sep s 68 0x3FCC48F2 5) (hS : Slots leCs F M1 M2) (hv : LeSaved F g0 M1)
    (hsp0 : g0 sp = F + BitVec.ofNat 32 0x40) (hret : g0 ra &&& ~~~1 = g0 ra) (hal : F.toNat % 4 = 0)
    (halo : out.toNat % 4 = 0) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ litL → f x = g0 x) (hsoF : Sep out 8 F 64)
    (hsc : Sep out 8 base jsonLiteralEndCode.length) (hb : base.toNat % 2 = 0)
    (hce : CodeIn M (base + 0xFFFFF400) equalSameLengthCode) (hcm : CodeIn M (base + 0xC7BE) memcmpCode)
    (sC : Sep s 68 (base + 0xFFFFF400) equalSameLengthCode.length)
    (sM : Sep s 68 (base + 0xC7BE) memcmpCode.length) (sCo : Sep s 68 base jsonLiteralEndCode.length) :
    WP jsonLiteralEndCode base (FPost (g0 ra) M out s 68 (litScan ((memBytes M p n).drop pos) pos litWords) g0)
      M2 0x6E f := by
  obtain ⟨wT, wF, wN⟩ := hlit
  have eT : (0x3FCC4766 : Word) + BitVec.ofNat 32 4 = 0x3FCC476A := by decide
  have hST : Sep s 68 0x3FCC476A 4 := eT ▸ hSn.subR (c := 4) (l := 4) (by decide)
  have hSN : Sep s 68 0x3FCC4766 4 := by
    have := hSn.subR (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have hfrk : ∀ g : Fin 32 → Word, (∀ x, x ∉ kL → g x = f x) → ∀ x, x ∉ litL → g x = g0 x :=
    fun g hg x hx => (hg x fun h => hx (kL_sub x h)).trans (hfr x hx)
  have hOk : ∀ M3 : Word → BitVec 8, Out M2 M3 s 4 → Out M M3 s 68 := fun M3 h3 =>
    hO.trans (Out.widen (d := 0) (by rw [add_ofNat_zero]; exact h3) (by decide))
  have hSk : ∀ M3 : Word → BitVec 8, Out M2 M3 s 4 → Slots leCs F M1 M3 := fun M3 h3 =>
    hS.out h3 fun c hc => sep_below hF (leCs_le c hc)
  have lk : ∀ M3 : Word → BitVec 8, Out M2 M3 s 4 → ∀ c, 4 + c + 4 ≤ 2 ^ 32 →
      memLoad32 M3 (F + BitVec.ofNat 32 c) = memLoad32 M2 (F + BitVec.ofNat 32 c) :=
    fun M3 h3 c hc => h3.load32 (sep_below hF hc)
  have a1 : F + 0xC + 0xFFFFFFFC = F + 8 := by rw [BitVec.add_assoc]; rfl
  refine le_it (w := ascii!"true") (ws := [ascii!"false", ascii!"null"]) (q := F + 0xC) (wp := 0x3FCC476A)
    h18 h19 h20 h21 hsp h9 hF hpn hn t2 (by rw [a1]; exact t1) wT (by decide)
    (aligned_add hal (k := 0xC) (by decide)) (by rw [a1]; exact aligned_add hal (k := 8) (by decide)) hO hSp hST
    hS hv hsp0 hret hal halo hz0 hfr hsoF hsc hb hce hcm sC sM sCo fun g1 M3 h3 hg1 => ?_
  refine le_step (v := 3) (by rw [hg1 22 (by decide), h22]) (by decide) fun g2 e9 e22 eo => ?_
  have k2 : ∀ x, x ∉ kL → g2 x = f x := kL_comp (fun _ _ => rfl) hg1 eo
  have a2 : F + 0xC + 8 = F + 0x14 := by rw [BitVec.add_assoc]; rfl
  have a2' : F + 0xC + 8 + 0xFFFFFFFC = F + 0x10 := by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  refine le_it (w := ascii!"false") (ws := [ascii!"null"]) (q := F + 0xC + 8) (wp := 0x3FCC48F2)
    ((k2 18 (by decide)).trans h18) ((k2 19 (by decide)).trans h19) ((k2 20 (by decide)).trans h20)
    ((k2 21 (by decide)).trans h21) ((k2 sp (by decide)).trans hsp) (by rw [e9, hg1 9 (by decide), h9]) hF hpn hn
    (by rw [a2]; exact (lk M3 h3 0x14 (by decide)).trans t4) (by rw [a2']; exact (lk M3 h3 0x10 (by decide)).trans t3)
    wF (by decide) (by rw [a2]; exact aligned_add hal (k := 0x14) (by decide))
    (by rw [a2']; exact aligned_add hal (k := 0x10) (by decide)) (hOk M3 h3) hSp hSf (hSk M3 h3) hv hsp0 hret hal
    halo hz0 (hfrk g2 k2) hsoF hsc hb hce hcm sC sM sCo fun g3 M4 h4 hg3 => ?_
  refine le_step (v := 3 + 0xFFFFFFFF) (by rw [hg3 22 (by decide), e22]) (by decide) fun g4 e9' e22' eo' => ?_
  have k4 : ∀ x, x ∉ kL → g4 x = f x := kL_comp k2 hg3 eo'
  have h34 : Out M2 M4 s 4 := h3.trans h4
  have a3 : F + 0xC + 8 + 8 = F + 0x1C := by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have a3' : F + 0xC + 8 + 8 + 0xFFFFFFFC = F + 0x18 := by
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; rfl
  refine le_it (w := ascii!"null") (ws := []) (q := F + 0xC + 8 + 8) (wp := 0x3FCC4766)
    ((k4 18 (by decide)).trans h18) ((k4 19 (by decide)).trans h19) ((k4 20 (by decide)).trans h20)
    ((k4 21 (by decide)).trans h21) ((k4 sp (by decide)).trans hsp)
    (by rw [e9', hg3 9 (by decide), e9, hg1 9 (by decide), h9]) hF hpn hn
    (by rw [a3]; exact (lk M4 h34 0x1C (by decide)).trans t6) (by rw [a3']; exact (lk M4 h34 0x18 (by decide)).trans t5)
    wN (by decide) (by rw [a3]; exact aligned_add hal (k := 0x1C) (by decide))
    (by rw [a3']; exact aligned_add hal (k := 0x18) (by decide)) (hOk M4 h34) hSp hSN (hSk M4 h34) hv hsp0 hret hal
    halo hz0 (hfrk g4 k4) hsoF hsc hb hce hcm sC sM sCo fun g5 M5 h5 hg5 => ?_
  have k5 : ∀ x, x ∉ kL → g5 x = f x := fun x hx => (kL_comp1 hg5 x hx).trans (k4 x hx)
  have h35 : Out M2 M5 s 4 := h34.trans h5
  exact le_last (by rw [hg5 22 (by decide), e22']; decide) ((k5 18 (by decide)).trans h18)
    ((k5 sp (by decide)).trans hsp) (hOk M5 h35) (hSk M5 h35) hv hsp0 hret hal halo hz0 (hfrk g5 k5) hsoF hsc

theorem le_wp {n pos : Nat} (h0 : f a0 = out) (h1 : f a1 = p) (h2 : f a2 = BitVec.ofNat 32 n)
    (h3 : f a3 = BitVec.ofNat 32 pos) (hsp : f sp = s + BitVec.ofNat 32 68) (hn : n < 2 ^ 32)
    (hpos : pos < 2 ^ 32) (hret : f ra &&& ~~~1 = f ra) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0)
    (hb : base.toNat % 2 = 0) (hlit : LitData M)
    (hce : CodeIn M (base + 0xFFFFF400) equalSameLengthCode) (hcm : CodeIn M (base + 0xC7BE) memcmpCode)
    (hSc : Sep s 68 base jsonLiteralEndCode.length)
    (sC : Sep s 68 (base + 0xFFFFF400) equalSameLengthCode.length)
    (sM : Sep s 68 (base + 0xC7BE) memcmpCode.length) (hSp : Sep s 68 p n)
    (hSn : Sep s 68 0x3FCC4766 8) (hSf : Sep s 68 0x3FCC48F2 5) (hso : Sep out 8 s 68)
    (hsc : Sep out 8 base jsonLiteralEndCode.length) :
    WP jsonLiteralEndCode base (FPost (f ra) M out s 68 (literalEnd (memBytes M p n) pos) f) M 0 f := by
  refine WP.zero fun hz => ?_
  have esp : aluEval .add (f sp) 0xFFFFFFC0 = s + 4 := by rw [hsp, ev_add, BitVec.add_assoc]; rfl
  have hlen : (memBytes M p n).length = n := memBytes_length M p n
  refine WP.aluImm le_at_0 ?_; wn
  rw [esp]
  generalize hF : s + 4 = F
  have halF : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add hal (k := 4) (by decide)
  have hSF : Sep F 64 base jsonLiteralEndCode.length := by rw [← hF]; exact hSc.sub (c := 4) (l := 64) (by decide)
  have hsoF : Sep out 8 F 64 := by rw [← hF]; exact hso.subR (c := 4) (l := 64) (by decide)
  have hsp0 : f sp = F + BitVec.ofNat 32 0x40 := by rw [hsp, ← hF, BitVec.add_assoc]; rfl
  refine WP.sw le_at_2 (by rsimp; exact aligned_add halF (k := 0x3c) (by decide))
    (by rsimp; exact hSF.sub (c := 0x3c) (by decide)) ?_; wn
  refine WP.sw le_at_4 (by rsimp; exact aligned_add halF (k := 0x38) (by decide))
    (by rsimp; exact hSF.sub (c := 0x38) (by decide)) ?_; wn
  refine WP.sw le_at_6 (by rsimp; exact aligned_add halF (k := 0x34) (by decide))
    (by rsimp; exact hSF.sub (c := 0x34) (by decide)) ?_; wn
  refine WP.sw le_at_8 (by rsimp; exact aligned_add halF (k := 0x30) (by decide))
    (by rsimp; exact hSF.sub (c := 0x30) (by decide)) ?_; wn
  refine WP.sw le_at_a (by rsimp; exact aligned_add halF (k := 0x2c) (by decide))
    (by rsimp; exact hSF.sub (c := 0x2c) (by decide)) ?_; wn
  refine WP.sw le_at_c (by rsimp; exact aligned_add halF (k := 0x28) (by decide))
    (by rsimp; exact hSF.sub (c := 0x28) (by decide)) ?_; wn
  refine WP.sw le_at_e (by rsimp; exact aligned_add halF (k := 0x24) (by decide))
    (by rsimp; exact hSF.sub (c := 0x24) (by decide)) ?_; wn
  refine WP.sw le_at_10 (by rsimp; exact aligned_add halF (k := 0x20) (by decide))
    (by rsimp; exact hSF.sub (c := 0x20) (by decide)) ?_; wn
  change WP jsonLiteralEndCode base _ (leM1 M F f) 0x12 _
  obtain ⟨hO1, hv⟩ := le_pro M F f
  have hO1' : Out M (leM1 M F f) s 68 := Out.up4 hF hO1 (by decide)
  refine WP.alu le_at_12 ?_; wn
  refine WP.branch le_at_14 (fun e => ?_) (fun e => ?_) <;> wn
  rotate_left
  · rsimp at e
    rw [h2, h3, br_bgeu hn hpos] at e
    have hlt : n < pos := not_dec_false e
    rw [literalEnd, hlen, ite_eq_left_of_eq_true _ _ (eq_true hlt)]
    exact le_err (by rsimp; simp only [ev0, ev_mv hz, h0]) (by rsimp) hO1' (Slots.refl _ _ _) hv hsp0 hret halF
      halo hz (by keepz hz) hsoF hsc
  rsimp at e
  rw [h2, h3, br_bgeu hn hpos] at e
  have hpn : pos ≤ n := by have := not_dec_true e; omega
  rw [literalEnd, hlen, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  refine WP.alu le_at_34 ?_; wn
  refine WP.alu le_at_36 ?_; wn
  refine WP.alu le_at_3a ?_; wn
  refine WP.lui le_at_3e ?_; wn
  refine WP.aluImm le_at_42 ?_; wn
  refine WP.aluImm le_at_46 ?_; wn
  refine WP.lui le_at_48 ?_; wn
  refine WP.aluImm le_at_4c ?_; wn
  refine WP.aluImm le_at_50 ?_; wn
  refine WP.sw le_at_52 (by rsimp; exact aligned_add halF (k := 8) (by decide))
    (by rsimp; exact hSF.sub (c := 8) (by decide)) ?_; wn
  refine WP.sw le_at_54 (by rsimp; exact aligned_add halF (k := 0xC) (by decide))
    (by rsimp; exact hSF.sub (c := 0xC) (by decide)) ?_; wn
  refine WP.sw le_at_56 (by rsimp; exact aligned_add halF (k := 0x10) (by decide))
    (by rsimp; exact hSF.sub (c := 0x10) (by decide)) ?_; wn
  refine WP.sw le_at_58 (by rsimp; exact aligned_add halF (k := 0x14) (by decide))
    (by rsimp; exact hSF.sub (c := 0x14) (by decide)) ?_; wn
  refine WP.lui le_at_5a ?_; wn
  refine WP.aluImm le_at_5e ?_; wn
  refine WP.aluImm le_at_62 ?_; wn
  refine WP.sw le_at_64 (by rsimp; exact aligned_add halF (k := 0x18) (by decide))
    (by rsimp; exact hSF.sub (c := 0x18) (by decide)) ?_; wn
  refine WP.sw le_at_66 (by rsimp; exact aligned_add halF (k := 0x1C) (by decide))
    (by rsimp; exact hSF.sub (c := 0x1C) (by decide)) ?_; wn
  refine le_tbl fun M2 hOt hSt t1 t2 t3 t4 t5 t6 => ?_
  refine WP.aluImm le_at_68 ?_; wn
  refine WP.branch le_at_6a (fun e => ?_) (fun _ => ?_) <;> wn
  · rsimp at e
  exact le_loop (n := n) (pos := pos) (by rsimp; simp only [ev0, ev_mv hz, h0]) (by rsimp; simp only [ev0, ev_mv hz, h3])
    (by rsimp; rw [h1, h3]; rfl) (by rsimp; rw [h2, h3]; exact sub_ofNat_le hpn hn) (by rsimp) (by rsimp; rfl)
    (by rsimp) hF hpn hn (t1.trans (by decide)) (t2.trans (by rsimp))
    (t3.trans (by decide)) (t4.trans (by rsimp)) (t5.trans (by decide)) (t6.trans (by rsimp)) hlit
    (hO1'.trans (Out.up4 hF hOt (by decide))) hSp hSn hSf hSt hv hsp0 hret halF halo hz (by keepz hz) hsoF hsc hb
    hce hcm sC sM hSc

end

/-- `json::literal_end` stores `literalEnd` of the document at `out`. It
writes only the 68 bytes below `sp` and the result, and keeps every register
outside `jClob`. -/
theorem jsonLiteralEnd_correct (m : Machine) {base retAddr out s p : Word} {n pos : Nat}
    (hb : base.toNat % 2 = 0) (hc : CodeIn m.mem base jsonLiteralEndCode)
    (hce : CodeIn m.mem (base + 0xFFFFF400) equalSameLengthCode)
    (hcm : CodeIn m.mem (base + 0xC7BE) memcmpCode) (hlit : LitData m.mem)
    (hpc : m.pc = base) (ha0 : reg m a0 = out) (ha1 : reg m a1 = p) (ha2 : reg m a2 = BitVec.ofNat 32 n)
    (ha3 : reg m a3 = BitVec.ofNat 32 pos) (hsp : reg m sp = s + BitVec.ofNat 32 68)
    (hn : n < 2 ^ 32) (hpos : pos < 2 ^ 32) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hSc : Sep s 68 base jsonLiteralEndCode.length)
    (hSe : Sep s 68 (base + 0xFFFFF400) equalSameLengthCode.length)
    (hSm : Sep s 68 (base + 0xC7BE) memcmpCode.length) (hSp : Sep s 68 p n)
    (hSn : Sep s 68 0x3FCC4766 8) (hSf : Sep s 68 0x3FCC48F2 5) (hso : Sep out 8 s 68)
    (hsc : Sep out 8 base jsonLiteralEndCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      UsizeResF m.mem m'.mem out s 68 (literalEnd (memBytes m.mem p n) pos) ∧
      ∀ r, r ∉ jClob → reg m' r = reg m r := by
  obtain ⟨m', st, hpc', hR, hfr⟩ := WP.run (le_wp ha0 ha1 ha2 ha3 hsp hn hpos (by rw [hra]; exact hret) hal
    halo hb hlit hce hcm hSc hSe hSm hSp hSn hSf hso hsc) hb hc hpc
  exact ⟨m', st, hpc'.trans hra, hR, hfr⟩

end C3.RV32
