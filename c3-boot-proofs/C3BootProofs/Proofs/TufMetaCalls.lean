import C3BootProofs.Proofs.JsonParse
import C3BootProofs.Proofs.TufCalls

/-!
# More calls from the TUF metadata checks

Call lemmas for `json::parse`, `Value::elements`, and
`Elements::next_element`, in the style of `TufCalls`, and the bounds of an
element that `next_element` returns.
-/

namespace C3.Json

/-- An element starts at the position, ends inside the array, and moves the
position forward. -/
theorem nextElement_lt {d : Bytes} {pos ep el a : Nat} (h : nextElement d pos = some (some (ep, el, a))) :
    ep = pos ∧ pos < a ∧ 0 < el ∧ ep + el ≤ d.length ∧ a ≤ d.length := by
  unfold nextElement at h
  split at h
  · cases h
  cases hr : readItem d pos with
  | none => rw [hr] at h; cases h
  | some x =>
    rw [hr] at h
    cases h
    have h1 := C3.RV32.readItem_bd hr
    have h2 := readItem_after hr
    have h3 := readItem_after_le hr
    exact ⟨rfl, by omega, by omega, by omega, h3⟩

end C3.Json

namespace C3.RV32

open C3.Image C3.Json

theorem ElemRes.codeIn {M M' : Word → BitVec 8} {out c b : Word} {code : List Nat}
    {r : Option (Option (Word × Nat × Nat))} (h : ElemRes M M' out c r) (hc : CodeIn M b code)
    (ho : Sep out 12 b code.length) (hcb : Sep (c + 8) 4 b code.length) : CodeIn M' b code :=
  fun i hi => by rw [h.out (sep_pt ho hi) (sep_pt hcb hi)]; exact hc i hi

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

/-- A call to `json::parse` on the `n` bytes at `p` in mode `c`, with the
code at `tb`. -/
theorem WP.callParse {hi lo tb p out s : Word} {n : Nat} {c : Bool}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hct : ParseCode M tb) (h0 : f a0 = out) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n)
    (ha3 : f a3 = modeW c) (hsp : f sp = s + BitVec.ofNat 32 404) (hal : s.toNat % 4 = 0)
    (halo : out.toNat % 4 = 0) (hsw : s.toNat + 404 < 2 ^ 32) (hn : n < 2 ^ 31) (hp0 : p.toNat ≠ 0)
    (hpn : p.toNat + n < 2 ^ 32) (hps : ParseSep s 404 tb) (hSp : Sep s 404 p n) (hso : Sep out 8 s 404)
    (hsc : Sep out 8 tb jsonParseCode.length) (hSb : Sep s 404 base code.length)
    (hsb : Sep out 8 base code.length)
    (k : ∀ m2 : Machine, FieldResF M m2.mem out s 404 (fieldRes p (parseModel c (memBytes M p n))) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := jClob)
    (P := fun m2 => FieldResF M m2.mem out s 404 (fieldRes p (parseModel c (memBytes M p n))))
    h1 h2 (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => by
      obtain ⟨M1, hO, hU⟩ := hP
      exact hU.out.codeIn (hO.codeIn hc hSb) hsb) k
  obtain ⟨m2, c2, pc2, hU, hfr⟩ := jsonParse_correct m1 (base := tb) (out := out) (s := s) (p := p) (n := n)
    (c := c) htb (by rw [hmem1]; exact hct) hpc1 (by rw [hreg1]; rsimp; exact h0)
    (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2) (by rw [hreg1]; rsimp; exact ha3)
    (by rw [hreg1]; rsimp; exact hsp) (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp)
    (even_clear _ (even_at base hb _ hev)) hal halo hsw hn hp0 hpn hps hSp hso hsc
  rw [hmem1] at hU
  exact ⟨m2, c2, pc2, hU, hfr⟩

/-- A call to `elements()` on the `n` bytes at `p` with the code at `tb`. -/
theorem WP.callElements {hi lo tb p out s : Word} {n : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hct : CodeIn M tb jsonElementsCode) (hcw : CodeIn M (tb + 0xFFFFFAB2) jsonSkipWsCode)
    (h0 : f a0 = out) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n) (hsp : f sp = s + BitVec.ofNat 32 16)
    (hn : n < 2 ^ 32) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0)
    (hSc : Sep s 16 tb jsonElementsCode.length) (hSw : Sep s 16 (tb + 0xFFFFFAB2) jsonSkipWsCode.length)
    (hSp : Sep s 16 p n) (hso : Sep out 12 s 16) (hsc : Sep out 12 tb jsonElementsCode.length)
    (hSb : Sep s 16 base code.length) (hsb : Sep out 12 base code.length)
    (k : ∀ m2 : Machine, CurResF M m2.mem out s 16 0x21 (curOpen 91 p (memBytes M p n)) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := jClob)
    (P := fun m2 => CurResF M m2.mem out s 16 0x21 (curOpen 91 p (memBytes M p n)))
    h1 h2 (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => by
      obtain ⟨M1, hO, hU⟩ := hP
      exact hU.out.codeIn (hO.codeIn hc hSb) hsb) k
  obtain ⟨m2, c2, pc2, hU, hfr⟩ := jsonElements_correct m1 (base := tb) (out := out) (s := s) (p := p) (n := n)
    htb (by rw [hmem1]; exact hct) (by rw [hmem1]; exact hcw) hpc1 (by rw [hreg1]; rsimp; exact h0)
    (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2) (by rw [hreg1]; rsimp; exact hsp) hn hal halo
    (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev))
    hSc hSw hSp hso hsc
  rw [hmem1] at hU
  exact ⟨m2, c2, pc2, hU, hfr⟩

/-- A call to `next_element` on the cursor at `c` with the code at `tb`. -/
theorem WP.callNextElement {hi lo tb out c s p : Word} {n pos : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hct : CodeIn M tb jsonNextElementCode) (hrc : RiCode M (tb + 0xFFFFF7E0)) (h0 : f a0 = out)
    (ha1 : f a1 = c) (hsp : f sp = s + BitVec.ofNat 32 148) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0)
    (halc : c.toNat % 4 = 0) (hmp : memLoad32 M c = p) (hmn : memLoad32 M (c + 4) = BitVec.ofNat 32 n)
    (hmq : memLoad32 M (c + 8) = BitVec.ofNat 32 pos) (hn : n < 2 ^ 32) (hpos : pos < 2 ^ 32)
    (hp0 : p.toNat ≠ 0) (hpn : p.toNat + n ≤ 2 ^ 32) (hrs : RiSep s 148 (tb + 0xFFFFF7E0))
    (hSc : Sep s 148 tb jsonNextElementCode.length) (hSp : Sep s 148 p n) (hso : Sep out 12 s 148)
    (hcs : Sep c 12 s 148) (hoc : Sep out 12 c 12) (hsc : Sep out 12 tb jsonNextElementCode.length)
    (hcc : Sep c 12 tb jsonNextElementCode.length) (hSb : Sep s 148 base code.length)
    (hsb : Sep out 12 base code.length) (hcb : Sep c 12 base code.length)
    (k : ∀ m2 : Machine, ElemResF M m2.mem out c s 148 (elemRes p (nextElement (memBytes M p n) pos)) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := jClob)
    (P := fun m2 => ElemResF M m2.mem out c s 148 (elemRes p (nextElement (memBytes M p n) pos)))
    h1 h2 (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => by
      obtain ⟨M1, hO, hR⟩ := hP
      exact hR.codeIn (hO.codeIn hc hSb) hsb (hcb.sub (c := 8) (l := 4) (by decide))) k
  obtain ⟨m2, c2, pc2, hR, hfr⟩ := jsonNextElement_correct m1 (base := tb) (out := out) (c := c) (s := s) (p := p)
    (n := n) (pos := pos) htb (by rw [hmem1]; exact hct) (by rw [hmem1]; exact hrc) hpc1
    (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact hsp)
    (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev))
    hal halo halc (by rw [hmem1]; exact hmp) (by rw [hmem1]; exact hmn) (by rw [hmem1]; exact hmq) hn hpos hp0 hpn
    hrs hSc hSp hso hcs hoc hsc hcc
  rw [hmem1] at hR
  exact ⟨m2, c2, pc2, hR, hfr⟩

end

end C3.RV32
