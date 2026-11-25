import C3BootProofs.Proofs.JsonFrame
import C3BootProofs.Proofs.JsonSkipWs
import C3BootProofs.Proofs.JsonStringEnd
import C3BootProofs.Proofs.JsonNumberEnd

/-!
# Calls to the JSON scanners

`WP.callGen` steps over a call: given the callee's contract, the walk goes
on after the call with the registers the callee may change read from the
machine it returned, and the rest from before the call. The lemmas after
it apply `skip_ws`, `string_end`, and `number_end` through it.
-/

namespace C3.RV32

open C3.Image C3.Json

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat}
  {f : Fin 32 → Word}

theorem WP.callGen {cl : List (Fin 32)} {P : Machine → Prop} {hi lo tb : Word}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : (base + BitVec.ofNat 32 off + hi + lo) &&& ~~~1 = tb)
    (hcallee : ∀ m1 : Machine, m1.pc = tb → m1.mem = M →
      (∀ x, reg m1 x = upd f ra (base + BitVec.ofNat 32 (off + 8)) x) → base.toNat % 2 = 0 →
      ∃ m2, Steps m1 m2 ∧ m2.pc = base + BitVec.ofNat 32 (off + 8) ∧ P m2 ∧ ∀ x, x ∉ cl → reg m2 x = reg m1 x)
    (hcode : ∀ m2 : Machine, P m2 → CodeIn M base code → CodeIn m2.mem base code)
    (k : ∀ m2 : Machine, P m2 →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 cl)) :
    WP code base Q M off f := by
  refine WP.call h1 h2 fun m1 hpc1 hmem1 hreg1 hb hc => ?_
  obtain ⟨m2, c2, pc2, hP, hfr⟩ := hcallee m1 (by rw [hpc1, htgt]) hmem1 hreg1 hb
  refine WP.resume c2 pc2 (fun x => ?_) hb (hcode m2 hP hc) (k m2 hP)
  by_cases hx : x ∈ cl
  · simp only [clob_app, hx, ↓reduceIte]
  · simp only [clob_app, hx, ↓reduceIte]; rw [hfr x hx, hreg1]

/-- The registers `skip_ws` may change. -/
abbrev swClob : List (Fin 32) := [a0, a1, a3, a4, a5, a6]

/-- A call to `skip_ws(bytes, pos)` with the code at `tb`. -/
theorem WP.callSkipWs {hi lo tb p : Word} {n q : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hct : CodeIn M tb jsonSkipWsCode) (h0 : f a0 = p) (ha1 : f a1 = BitVec.ofNat 32 n)
    (ha2 : f a2 = BitVec.ofNat 32 q) (hn : n < 2 ^ 32) (hq : q < 2 ^ 32)
    (k : ∀ m2 : Machine, reg m2 a0 = BitVec.ofNat 32 (skipWs (memBytes M p n) q) →
      WP code base Q M (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 swClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := swClob) (P := fun m2 => m2.mem = M ∧
      reg m2 a0 = BitVec.ofNat 32 (skipWs (memBytes M p n) q)) h1 h2
    (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => by rw [hP.1]; exact hc) (fun m2 hP => by rw [hP.1]; exact k m2 hP.2)
  obtain ⟨m2, c2, pc2, mem2, r0, hfr⟩ := jsonSkipWs_correct m1 (base := tb) (p := p) (n := n) (pos := q) htb (by rw [hmem1]; exact hct)
    hpc1 (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2)
    hn hq (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp)
    (even_clear _ (even_at base hb _ hev))
  rw [hmem1] at mem2 r0
  refine ⟨m2, c2, pc2, ⟨mem2, r0⟩, fun x hx => ?_⟩
  simp only [swClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  obtain ⟨n0, n1, n3, n4, n5, n6⟩ := hx
  exact hfr x n0 n1 n3 n4 n5 n6

/-- A call to `string_end(doc, pos, mode)` with the code at `tb`, storing
its result at `out`. -/
theorem WP.callStringEnd {hi lo tb p out : Word} {n pos : Nat} {c : Bool}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hct : CodeIn M tb jsonStringEndCode) (h0 : f a0 = out) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n)
    (ha3 : f a3 = BitVec.ofNat 32 pos) (ha4 : f a4 = modeW c) (hn : n < 2 ^ 32) (hpos : pos < 2 ^ 32)
    (hal : out.toNat % 4 = 0) (hsep : Sep out 8 tb jsonStringEndCode.length) (hsc : Sep out 8 base code.length)
    (k : ∀ m2 : Machine, UsizeRes M m2.mem out (stringEnd c (memBytes M p n) pos) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 seClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := seClob) (P := fun m2 => UsizeRes M m2.mem out (stringEnd c (memBytes M p n) pos))
    h1 h2 (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => hP.out.codeIn hc hsc) k
  obtain ⟨m2, c2, pc2, hU, hfr⟩ := jsonStringEnd_correct m1 (base := tb) (out := out) (p := p) (n := n) (pos := pos) (c := c) htb (by rw [hmem1]; exact hct)
    hpc1 (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2)
    (by rw [hreg1]; rsimp; exact ha3) (by rw [hreg1]; rsimp; exact ha4) hn hpos hal hsep
    (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev))
  rw [hmem1] at hU
  exact ⟨m2, c2, pc2, hU, hfr⟩

/-- A call to `number_end(doc, pos)` with the code at `tb`, storing its
result at `out`. -/
theorem WP.callNumberEnd {hi lo tb p out : Word} {n pos : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = tb) (htb : tb.toNat % 2 = 0) (hev : (off + 8) % 2 = 0)
    (hct : CodeIn M tb jsonNumberEndCode) (h0 : f a0 = out) (ha1 : f a1 = p) (ha2 : f a2 = BitVec.ofNat 32 n)
    (ha3 : f a3 = BitVec.ofNat 32 pos) (hn : n < 2 ^ 32) (hpos : pos < 2 ^ 32)
    (hal : out.toNat % 4 = 0) (hsep : Sep out 8 tb jsonNumberEndCode.length) (hsc : Sep out 8 base code.length)
    (k : ∀ m2 : Machine, UsizeRes M m2.mem out (numberEnd (memBytes M p n) pos) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 neClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := tb) (cl := neClob) (P := fun m2 => UsizeRes M m2.mem out (numberEnd (memBytes M p n) pos))
    h1 h2 (by rw [htgt]; exact even_clear _ htb) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => hP.out.codeIn hc hsc) k
  obtain ⟨m2, c2, pc2, hU, hfr⟩ := jsonNumberEnd_correct m1 (base := tb) (out := out) (p := p) (n := n) (pos := pos) htb (by rw [hmem1]; exact hct)
    hpc1 (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2)
    (by rw [hreg1]; rsimp; exact ha3) hn hpos hal hsep
    (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev))
  rw [hmem1] at hU
  exact ⟨m2, c2, pc2, hU, hfr⟩

end

end C3.RV32
