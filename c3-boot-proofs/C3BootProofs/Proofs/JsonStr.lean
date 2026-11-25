import C3BootProofs.Proofs.JsonFrame
import C3BootProofs.Proofs.JsonModel

/-!
# `Value::str`, as compiled

`Value::str(&self)` stores `Ok` of the bytes between a string value's
quotes, or `Err(Schema)`, at `out`. It is a leaf with no frame. A
`Result<&[u8], TufError>` keeps the slice's pointer at `out` and its length
at `out + 4`; `Err` is a null pointer with the error byte at `out + 4`.

`SliceRes` describes that layout. `jsonField` and the navigation functions
built on it return values in the same layout.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

/-- `out` holds `r` as a `Result<&[u8], TufError>` whose error byte is `e`,
and only the 8 bytes at `out` changed. -/
def SliceRes (M M' : Word → BitVec 8) (out : Word) (e : BitVec 8) : Option (Word × Nat) → Prop
  | some (q, l) => (∀ x, Sep x 1 out 8 → M' x = M x) ∧ memLoad32 M' out = q ∧
      memLoad32 M' (out + 4) = BitVec.ofNat 32 l
  | none => (∀ x, Sep x 1 out 8 → M' x = M x) ∧ memLoad32 M' out = 0 ∧ M' (out + 4) = e

theorem sep_out04 (out : Word) : Sep out 4 (out + 4) 4 := by
  have := sep_offsets out (c := 0) (n := 4) (d := 4) (k := 4) (Or.inl (by decide)) (by decide) (by decide)
  rwa [add_ofNat_zero] at this

theorem sep_lo {x out : Word} (hx : Sep x 1 out 8) : Sep x 1 out 4 := by
  have := sep_in hx (d := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this

theorem sliceRes_ok (M : Word → BitVec 8) (out q : Word) (l : Nat) (e : BitVec 8) :
    SliceRes M (memStore32 (memStore32 M out q) (out + 4) (BitVec.ofNat 32 l)) out e (some (q, l)) := by
  refine ⟨fun x hx => ?_, ?_, memLoad32_store32_same _ _ _⟩
  · exact (out_store32 _ (out + BitVec.ofNat 32 4) _ x (sep_in hx (by decide))).trans
      (out_store32 _ _ _ x (sep_lo hx))
  · rw [memLoad32_store32_sep (sep_out04 out).symm, memLoad32_store32_same]

theorem sliceRes_err (M : Word → BitVec 8) (out : Word) (e : BitVec 8) :
    SliceRes M (memStore8 (memStore32 M out 0) (out + 4) e) out e none := by
  have h4 : Sep (out + 4) 1 out 4 := fun i hi j hj => (sep_out04 out).symm i (by omega) j hj
  refine ⟨fun x hx => ?_, ?_, memStore8_same _ _ _⟩
  · exact (out_store8 _ (out + BitVec.ofNat 32 4) _ x (sep_in hx (by decide))).trans
      (out_store32 _ _ _ x (sep_lo hx))
  · rw [memLoad32_store8_sep h4, memLoad32_store32_same]

theorem SliceRes.out {e : BitVec 8} {r : Option (Word × Nat)} (h : SliceRes M M' a e r) : Out M M' a 8 := by
  rcases r with _ | ⟨_, _⟩
  · exact h.1
  · exact h.1

/-- The body of the string value `d` at `p`: the bytes between its quotes. -/
def strRes (p : Word) (d : Bytes) : Option (Word × Nat) :=
  if d.length < 2 then none
  else if d.getD 0 0 ≠ 34 then none
  else if d.getD (d.length - 1) 0 ≠ 34 then none
  else some (p + 1, d.length - 2)

theorem str_at_0 : fetchRel jsonStrCode 0x0 = some (.aluImm .add a3 x0 0x1, 2) := by decide
theorem str_at_2 : fetchRel jsonStrCode 0x2 = some (.branch .bgeu a3 a2 0x26, 4) := by decide
theorem str_at_6 : fetchRel jsonStrCode 0x6 = some (.load .lbu a3 a1 0x0, 4) := by decide
theorem str_at_a : fetchRel jsonStrCode 0xA = some (.aluImm .add a3 a3 0xFFFFFFDE, 4) := by decide
theorem str_at_e : fetchRel jsonStrCode 0xE = some (.branch .bne a3 x0 0x1A, 2) := by decide
theorem str_at_10 : fetchRel jsonStrCode 0x10 = some (.alu .add a3 a1 a2, 4) := by decide
theorem str_at_14 : fetchRel jsonStrCode 0x14 = some (.load .lbu a3 a3 0xFFFFFFFF, 4) := by decide
theorem str_at_18 : fetchRel jsonStrCode 0x18 = some (.aluImm .add a3 a3 0xFFFFFFDE, 4) := by decide
theorem str_at_1c : fetchRel jsonStrCode 0x1C = some (.branch .bne a3 x0 0xC, 2) := by decide
theorem str_at_1e : fetchRel jsonStrCode 0x1E = some (.aluImm .add a1 a1 0x1, 2) := by decide
theorem str_at_20 : fetchRel jsonStrCode 0x20 = some (.aluImm .add a2 a2 0xFFFFFFFE, 2) := by decide
theorem str_at_22 : fetchRel jsonStrCode 0x22 = some (.store .sw a0 a1 0x0, 2) := by decide
theorem str_at_24 : fetchRel jsonStrCode 0x24 = some (.store .sw a0 a2 0x4, 2) := by decide
theorem str_at_26 : fetchRel jsonStrCode 0x26 = some (.jalr x0 ra 0x0, 2) := by decide
theorem str_at_28 : fetchRel jsonStrCode 0x28 = some (.aluImm .add a1 x0 0x21, 4) := by decide
theorem str_at_2c : fetchRel jsonStrCode 0x2C = some (.store .sw a0 x0 0x0, 4) := by decide
theorem str_at_30 : fetchRel jsonStrCode 0x30 = some (.store .sb a0 a1 0x4, 4) := by decide
theorem str_at_34 : fetchRel jsonStrCode 0x34 = some (.jalr x0 ra 0x0, 2) := by decide

theorem str_q : ∀ b : BitVec 8,
    branchTaken .bne (aluEval .add (b.zeroExtend 32) 0xFFFFFFDE) 0 = !(b.toNat == 34) := by decide

theorem js_dec1 (k : Nat) : BitVec.ofNat 32 (k + 1) + (0xFFFFFFFF : Word) = BitVec.ofNat 32 k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl]
  omega

theorem js_sub2 {k : Nat} (h : 2 ≤ k) (hk : k < 2 ^ 32) :
    BitVec.ofNat 32 k + (0xFFFFFFFE : Word) = BitVec.ofNat 32 (k - 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFE : Word).toNat = 4294967294 from rfl]
  omega

/-- The registers `str` may change. -/
abbrev strClob : List (Fin 32) := [a1, a2, a3]

/-- `str` returned to `ret` with `r` at `out`. -/
def strPost (ret : Word) (M : Word → BitVec 8) (out : Word) (r : Option (Word × Nat)) (g0 : Fin 32 → Word) :
    Post :=
  fun pc M' g => pc = ret ∧ SliceRes M M' out 0x21 r ∧ ∀ x, x ∉ strClob → g x = g0 x

section
variable {M : Word → BitVec 8} {base ret out : Word} {f g0 : Fin 32 → Word}

theorem str_err (h0 : f a0 = out) (hra : f ra = ret) (hret : ret &&& ~~~1 = ret) (hal : out.toNat % 4 = 0)
    (hsep : Sep out 8 base jsonStrCode.length) (hfr : ∀ x, x ∉ strClob → f x = g0 x) :
    WP jsonStrCode base (strPost ret M out none g0) M 0x28 f := by
  refine WP.zero fun hz => ?_
  refine WP.aluImm str_at_28 ?_; wn
  refine WP.sw str_at_2c (by rsimp; rw [h0]; exact aligned_add hal (k := 0) (by decide))
    (by rsimp; rw [h0]; exact hsep.sub (c := 0) (by decide)) ?_; wn
  refine WP.sb str_at_30 (by rsimp; rw [h0]; exact hsep.shift (c := 4) (by decide)) ?_; wn
  refine WP.ret str_at_34 ⟨?_, ?_, ?_⟩
  · rsimp; rw [hra, add_lit_zero, hret]
  · rw [h0, hz, add_lit_zero]; exact sliceRes_err M out _
  · keep hz

theorem str_wp {p : Word} {n : Nat} (hn : n < 2 ^ 32) (h0 : f a0 = out) (h1 : f a1 = p)
    (h2 : f a2 = BitVec.ofNat 32 n) (hra : f ra = ret) (hret : ret &&& ~~~1 = ret) (hal : out.toNat % 4 = 0)
    (hsep : Sep out 8 base jsonStrCode.length) :
    WP jsonStrCode base (strPost ret M out (strRes p (memBytes M p n)) f) M 0 f := by
  refine WP.zero fun hz => ?_
  have hlen : (memBytes M p n).length = n := memBytes_length M p n
  refine WP.aluImm str_at_0 ?_; wn
  refine WP.branch str_at_2 (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    rw [h2, ev_mv hz, show (1 : Word) = BitVec.ofNat 32 1 from rfl, br_bgeu (by decide) hn] at e
    have hlt : (memBytes M p n).length < 2 := by have := not_dec_true e; omega
    simp only [strRes, hlt, ↓reduceIte]
    exact str_err (by rsimp; exact h0) (by rsimp; exact hra) hret hal hsep (by keep hz)
  rsimp at e
  rw [h2, ev_mv hz, show (1 : Word) = BitVec.ofNat 32 1 from rfl, br_bgeu (by decide) hn] at e
  have h2le : 2 ≤ n := by have := not_dec_false e; omega
  have hlt : ¬(memBytes M p n).length < 2 := by omega
  refine WP.lbu str_at_6 ?_; wn
  refine WP.aluImm str_at_a ?_; wn
  rw [h1, add_lit_zero]
  have hb0 : (memBytes M p n).getD 0 0 = (M p).toNat := by
    rw [memBytes_getD (by omega), add_ofNat_zero]
  refine WP.branch str_at_e (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    rw [str_q] at e
    have hne : (memBytes M p n).getD 0 0 ≠ 34 := by rw [hb0]; exact nbeq_true e
    simp only [strRes, hlt, hne, ne_eq, not_false_eq_true, ↓reduceIte]
    exact str_err (by rsimp; exact h0) (by rsimp; exact hra) hret hal hsep (by keep hz)
  rsimp at e
  rw [str_q] at e
  have heq : (memBytes M p n).getD 0 0 = 34 := by rw [hb0]; exact nbeq_false e
  refine WP.alu str_at_10 ?_; wn
  refine WP.lbu str_at_14 ?_; wn
  refine WP.aluImm str_at_18 ?_; wn
  have hn1 : BitVec.ofNat 32 n = BitVec.ofNat 32 (n - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
  rw [h1, h2, ev_add p, BitVec.add_assoc, hn1, js_dec1]
  have hbl : (memBytes M p n).getD (n - 1) 0 = (M (p + BitVec.ofNat 32 (n - 1))).toNat :=
    memBytes_getD (by omega)
  refine WP.branch str_at_1c (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    rw [str_q] at e
    have hne : (memBytes M p n).getD ((memBytes M p n).length - 1) 0 ≠ 34 := by
      rw [hlen, hbl]; exact nbeq_true e
    simp only [strRes, hlt, heq, hne, ne_eq, not_false_eq_true, ↓reduceIte, not_true_eq_false]
    exact str_err (by rsimp; exact h0) (by rsimp; exact hra) hret hal hsep (by keep hz)
  rsimp at e
  rw [str_q] at e
  have heq2 : (memBytes M p n).getD (n - 1) 0 = 34 := by rw [hbl]; exact nbeq_false e
  simp only [strRes, hlen, show ¬n < 2 from by omega, heq, heq2, ne_eq, not_true_eq_false, ↓reduceIte]
  refine WP.aluImm str_at_1e ?_; wn
  refine WP.aluImm str_at_20 ?_; wn
  refine WP.sw str_at_22 (by rsimp; rw [h0]; exact aligned_add hal (k := 0) (by decide))
    (by rsimp; rw [h0]; exact hsep.sub (c := 0) (by decide)) ?_; wn
  refine WP.sw str_at_24 (by rsimp; rw [h0]; exact aligned_add hal (k := 4) (by decide))
    (by rsimp; rw [h0]; exact hsep.sub (c := 4) (by decide)) ?_; wn
  refine WP.ret str_at_26 ⟨?_, ?_, ?_⟩
  · rsimp; rw [hra, add_lit_zero, hret]
  · rw [h0, add_lit_zero, h1, h2, ev_add, ev_add, js_sub2 h2le hn]; exact sliceRes_ok M out _ _ _
  · keep hz

/-- `Value::str` on the `n` bytes at `p`: stores `strRes p` of them at `out`
as a `Result<&[u8], TufError>` with `Err(Schema)` (`0x21`), changes no other
memory, and keeps every register outside `strClob`. -/
theorem jsonStr_correct (m : Machine) {base retAddr out p : Word} {n : Nat}
    (hb : base.toNat % 2 = 0) (hc : CodeIn m.mem base jsonStrCode) (hpc : m.pc = base)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = p) (ha2 : reg m a2 = BitVec.ofNat 32 n) (hn : n < 2 ^ 32)
    (hal : out.toNat % 4 = 0) (hsep : Sep out 8 base jsonStrCode.length)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      SliceRes m.mem m'.mem out 0x21 (strRes p (memBytes m.mem p n)) ∧
      ∀ r, r ∉ strClob → reg m' r = reg m r :=
  WP.run (str_wp hn ha0 ha1 ha2 hra hret hal hsep) hb hc hpc

end

end C3.RV32
