import C3BootProofs.Proofs.JsonCalls

/-!
# `Value::members` and `Value::elements`, as compiled

`members(&self)` stores `Ok(Members { bytes, pos })`, with `pos` the
position after the opening brace and any whitespace, or `Err(Schema)`, at
`out`. `elements` does the same for an array. Each saves `ra` and `s0`–`s2`
in a 16-byte frame and calls `skip_ws`, so its stack region is the 16 bytes
below `sp`.

A `Result<Members, TufError>` keeps the slice's pointer at `out`, its length
at `out + 4`, and `pos` at `out + 8`; `Err` is a null pointer with the error
byte at `out + 4`. `CurRes` describes that layout, which `Elements` shares.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

/-- `out` holds `r` as a `Result` of a cursor (`Members` or `Elements`) whose
error byte is `e`, and only the 12 bytes at `out` changed. -/
def CurRes (M M' : Word → BitVec 8) (out : Word) (e : BitVec 8) : Option (Word × Nat × Nat) → Prop
  | some (q, l, k) => (∀ x, Sep x 1 out 12 → M' x = M x) ∧ memLoad32 M' out = q ∧
      memLoad32 M' (out + 4) = BitVec.ofNat 32 l ∧ memLoad32 M' (out + 8) = BitVec.ofNat 32 k
  | none => (∀ x, Sep x 1 out 12 → M' x = M x) ∧ memLoad32 M' out = 0 ∧ M' (out + 4) = e

theorem CurRes.out {M M' : Word → BitVec 8} {a : Word} {e : BitVec 8} {r : Option (Word × Nat × Nat)}
    (h : CurRes M M' a e r) : Out M M' a 12 := by
  rcases r with _ | ⟨_, _, _⟩
  · exact h.1
  · exact h.1

theorem curRes_ok (M : Word → BitVec 8) (out q : Word) (l k : Nat) (e : BitVec 8) :
    CurRes M (memStore32 (memStore32 (memStore32 M (out + 4) (BitVec.ofNat 32 l)) (out + 8)
      (BitVec.ofNat 32 k)) out q) out e (some (q, l, k)) := by
  have s04 : Sep (out + BitVec.ofNat 32 0) 4 (out + BitVec.ofNat 32 4) 4 :=
    sep_offsets out (Or.inl (by decide)) (by decide) (by decide)
  have s08 : Sep (out + BitVec.ofNat 32 0) 4 (out + BitVec.ofNat 32 8) 4 :=
    sep_offsets out (Or.inl (by decide)) (by decide) (by decide)
  have s48 : Sep (out + BitVec.ofNat 32 4) 4 (out + BitVec.ofNat 32 8) 4 :=
    sep_offsets out (Or.inl (by decide)) (by decide) (by decide)
  rw [add_ofNat_zero] at s04 s08
  refine ⟨fun x hx => ?_, memLoad32_store32_same _ _ _, ?_, ?_⟩
  · have h0 : Sep x 1 out 4 := by have := sep_in hx (d := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    exact ((out_store32 _ _ _ x h0).trans
      (out_store32 _ (out + BitVec.ofNat 32 8) _ x (sep_in hx (by decide)))).trans
      (out_store32 _ (out + BitVec.ofNat 32 4) _ x (sep_in hx (by decide)))
  · exact (memLoad32_store32_sep s04).trans ((memLoad32_store32_sep s48.symm).trans (memLoad32_store32_same _ _ _))
  · exact (memLoad32_store32_sep s08).trans (memLoad32_store32_same _ _ _)

theorem curRes_err (M : Word → BitVec 8) (out : Word) (e : BitVec 8) :
    CurRes M (memStore32 (memStore8 M (out + 4) e) out 0) out e none := by
  have s04 : Sep (out + BitVec.ofNat 32 0) 4 (out + BitVec.ofNat 32 4) 4 :=
    sep_offsets out (Or.inl (by decide)) (by decide) (by decide)
  rw [add_ofNat_zero] at s04
  refine ⟨fun x hx => ?_, memLoad32_store32_same _ _ _, ?_⟩
  · have h0 : Sep x 1 out 4 := by have := sep_in hx (d := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    exact (out_store32 _ _ _ x h0).trans (out_store8 _ (out + BitVec.ofNat 32 4) _ x (sep_in hx (by decide)))
  · exact (memStore32_get_sep (fun i hi j hj => s04 i hi j (by omega))).trans (memStore8_same _ _ _)

/-- A cursor result in a function whose stack region is `[s, s + k)`. -/
def CurResF (M M' : Word → BitVec 8) (out s : Word) (k : Nat) (e : BitVec 8) (r : Option (Word × Nat × Nat)) :
    Prop :=
  ∃ M1, Out M M1 s k ∧ CurRes M1 M' out e r

/-- The function returned to `ret` with `R` of its final memory, keeping the
registers outside `jClob`. -/
def RPost (ret : Word) (R : (Word → BitVec 8) → Prop) (g0 : Fin 32 → Word) : Post :=
  fun pc M' g => pc = ret ∧ R M' ∧ ∀ x, x ∉ jClob → g x = g0 x

/-- The cursor over the object or array `d` at `p` whose opening byte must
be `o`: its bytes and the position after the opening byte and whitespace. -/
def curOpen (o : Nat) (p : Word) (d : Bytes) : Option (Word × Nat × Nat) :=
  if d.length = 0 then none else if d.getD 0 0 ≠ o then none else some (p, d.length, skipWs d 1)

abbrev meL : List (Fin 32) := jClob ++ [ra, sp, 8, 9, 18]

abbrev meCs : List Nat := [0, 4, 8, 12]

/-- The saved registers in the frame at `s`. -/
def MeSaved (s : Word) (g0 : Fin 32 → Word) (M1 : Word → BitVec 8) : Prop :=
  memLoad32 M1 (s + BitVec.ofNat 32 12) = g0 ra ∧ memLoad32 M1 (s + BitVec.ofNat 32 8) = g0 8 ∧
    memLoad32 M1 (s + BitVec.ofNat 32 4) = g0 9 ∧ memLoad32 M1 (s + BitVec.ofNat 32 0) = g0 18

/-- Memory after the prologue. -/
def meM1 (M : Word → BitVec 8) (s : Word) (g0 : Fin 32 → Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 M (s + 12) (g0 ra)) (s + 8) (g0 8)) (s + 4) (g0 9)) (s + 0) (g0 18)

theorem me_pro (M : Word → BitVec 8) (s : Word) (g0 : Fin 32 → Word) :
    Out M (meM1 M s g0) s 16 ∧ MeSaved s g0 (meM1 M s g0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ((((out_store32 _ _ _).widen (d := 12) (by decide)).trans
      ((out_store32 _ _ _).widen (d := 8) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 4) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 0) (by decide))
  · exact ld_skip 12 0 (by decide) (by decide) (by decide) (ld_skip 12 4 (by decide) (by decide) (by decide)
      (ld_skip 12 8 (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _)))
  · exact ld_skip 8 0 (by decide) (by decide) (by decide) (ld_skip 8 4 (by decide) (by decide) (by decide)
      (memLoad32_store32_same _ _ _))
  · exact ld_skip 4 0 (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _)
  · exact memLoad32_store32_same _ _ _

theorem me_at_0 : fetchRel jsonMembersCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem me_at_2 : fetchRel jsonMembersCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem me_at_4 : fetchRel jsonMembersCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x8, 2) := by decide
theorem me_at_6 : fetchRel jsonMembersCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x4, 2) := by decide
theorem me_at_8 : fetchRel jsonMembersCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x0, 2) := by decide
theorem me_at_a : fetchRel jsonMembersCode 0xA = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem me_at_c : fetchRel jsonMembersCode 0xC = some (.branch .beq a2 x0 0x26, 2) := by decide
theorem me_at_e : fetchRel jsonMembersCode 0xE = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem me_at_10 : fetchRel jsonMembersCode 0x10 = some (.load .lbu a0 a1 0x0, 4) := by decide
theorem me_at_14 : fetchRel jsonMembersCode 0x14 = some (.aluImm .add a0 a0 0xFFFFFF85, 4) := by decide
theorem me_at_18 : fetchRel jsonMembersCode 0x18 = some (.branch .bne a0 x0 0x1A, 2) := by decide
theorem me_at_1a : fetchRel jsonMembersCode 0x1A = some (.alu .add (18 : Fin 32) x0 a2, 2) := by decide
theorem me_at_1c : fetchRel jsonMembersCode 0x1C = some (.aluImm .add a2 x0 0x1, 2) := by decide
theorem me_at_1e : fetchRel jsonMembersCode 0x1E = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem me_at_20 : fetchRel jsonMembersCode 0x20 = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem me_at_22 : fetchRel jsonMembersCode 0x22 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem me_at_26 : fetchRel jsonMembersCode 0x26 = some (.jalr ra ra 0x7D6, 4) := by decide
theorem me_at_2a : fetchRel jsonMembersCode 0x2A = some (.store .sw (8 : Fin 32) (18 : Fin 32) 0x4, 4) := by decide
theorem me_at_2e : fetchRel jsonMembersCode 0x2E = some (.store .sw (8 : Fin 32) a0 0x8, 2) := by decide
theorem me_at_30 : fetchRel jsonMembersCode 0x30 = some (.jal x0 0xC, 2) := by decide
theorem me_at_32 : fetchRel jsonMembersCode 0x32 = some (.aluImm .add (9 : Fin 32) x0 0x0, 2) := by decide
theorem me_at_34 : fetchRel jsonMembersCode 0x34 = some (.aluImm .add a0 x0 0x21, 4) := by decide
theorem me_at_38 : fetchRel jsonMembersCode 0x38 = some (.store .sb (8 : Fin 32) a0 0x4, 4) := by decide
theorem me_at_3c : fetchRel jsonMembersCode 0x3C = some (.store .sw (8 : Fin 32) (9 : Fin 32) 0x0, 2) := by decide
theorem me_at_3e : fetchRel jsonMembersCode 0x3E = some (.load .lw ra sp 0xC, 2) := by decide
theorem me_at_40 : fetchRel jsonMembersCode 0x40 = some (.load .lw (8 : Fin 32) sp 0x8, 2) := by decide
theorem me_at_42 : fetchRel jsonMembersCode 0x42 = some (.load .lw (9 : Fin 32) sp 0x4, 2) := by decide
theorem me_at_44 : fetchRel jsonMembersCode 0x44 = some (.load .lw (18 : Fin 32) sp 0x0, 2) := by decide
theorem me_at_46 : fetchRel jsonMembersCode 0x46 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem me_at_48 : fetchRel jsonMembersCode 0x48 = some (.jalr x0 ra 0x0, 2) := by decide

theorem me_open : ∀ b : BitVec 8,
    branchTaken .bne (aluEval .add (b.zeroExtend 32) 0xFFFFFF85) 0 = !(b.toNat == 123) := by decide

section
variable {M M1 Mp : Word → BitVec 8} {base out s p : Word} {f g0 : Fin 32 → Word}

theorem me_epi {Mf : Word → BitVec 8} {R : (Word → BitVec 8) → Prop} (hsp : f sp = s)
    (hS : Slots meCs s M1 Mf) (hv : MeSaved s g0 M1) (hsp0 : g0 sp = s + BitVec.ofNat 32 16)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hal : s.toNat % 4 = 0) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ meL → f x = g0 x) (hR : R Mf) :
    WP jsonMembersCode base (RPost (g0 ra) R g0) Mf 0x3E f := by
  obtain ⟨v1, v2, v3, v4⟩ := hv
  have e1 : memLoad32 Mf (s + 0xC) = g0 ra := (hS 12 (by decide)).trans v1
  have e2 : memLoad32 Mf (s + 0x8) = g0 8 := (hS 8 (by decide)).trans v2
  have e3 : memLoad32 Mf (s + 0x4) = g0 9 := (hS 4 (by decide)).trans v3
  have e4 : memLoad32 Mf (s + 0x0) = g0 18 := (hS 0 (by decide)).trans v4
  refine WP.lw me_at_3e (by rw [hsp]; exact aligned_add hal (k := 12) (by decide)) ?_; wn
  refine WP.lw me_at_40 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 8) (by decide)) ?_; wn
  refine WP.lw me_at_42 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 4) (by decide)) ?_; wn
  refine WP.lw me_at_44 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0) (by decide)) ?_; wn
  refine WP.aluImm me_at_46 ?_; wn
  refine WP.ret me_at_48 ⟨?_, hR, ?_⟩
  · rsimp; rw [hsp, e1, add_lit_zero, hret]
  refine frame_of (L2 := [ra, sp, 8, 9, 18]) (by keepz hz0) fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> rsimp
  · rw [hsp, e1]
  · rw [hsp, hsp0]; rfl
  · rw [hsp, e2]
  · rw [hsp, e3]
  · rw [hsp, e4]

theorem me_3c {q : Word} {M2 : Word → BitVec 8} {r : Option (Word × Nat × Nat)} (h8 : f 8 = out)
    (h9 : f 9 = q) (hsp : f sp = s) (hO : Out M M1 s 16) (hS : Slots meCs s Mp M1) (hv : MeSaved s g0 Mp)
    (hR : CurRes M1 (memStore32 M2 out q) out 0x21 r) (hsp0 : g0 sp = s + BitVec.ofNat 32 16)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ meL → f x = g0 x) (hso : Sep out 12 s 16) (hsc : Sep out 12 base jsonMembersCode.length) :
    WP jsonMembersCode base (RPost (g0 ra) (fun M' => CurResF M M' out s 16 0x21 r) g0) M2 0x3C f := by
  refine WP.zero fun hz => ?_
  refine WP.sw me_at_3c (by rw [h8]; exact aligned_add halo (k := 0) (by decide))
    (by rw [h8]; exact hsc.sub (c := 0) (by decide)) ?_; wn
  rw [h8, h9, add_lit_zero]
  exact me_epi (by (try rsimp); exact hsp) (hS.out hR.out (slots_sep_out hso (by decide))) hv hsp0 hret hal hz0
    (by keepz hz0) ⟨M1, hO, hR⟩

theorem me_err (h8 : f 8 = out) (hsp : f sp = s) (hO : Out M M1 s 16) (hS : Slots meCs s Mp M1)
    (hv : MeSaved s g0 Mp) (hsp0 : g0 sp = s + BitVec.ofNat 32 16) (hret : g0 ra &&& ~~~1 = g0 ra)
    (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ meL → f x = g0 x)
    (hso : Sep out 12 s 16) (hsc : Sep out 12 base jsonMembersCode.length) :
    WP jsonMembersCode base (RPost (g0 ra) (fun M' => CurResF M M' out s 16 0x21 none) g0) M1 0x32 f := by
  refine WP.zero fun hz => ?_
  refine WP.aluImm me_at_32 ?_; wn
  refine WP.aluImm me_at_34 ?_; wn
  refine WP.sb me_at_38 (by (try rsimp); rw [h8]; exact hsc.shift (c := 4) (by decide)) ?_; wn
  rw [h8]
  exact me_3c (q := 0) (by (try rsimp); exact h8) (by (try rsimp); simp only [ev0, ev_mv hz]) (by (try rsimp); exact hsp) hO hS hv (curRes_err M1 out 0x21)
    hsp0 hret hal halo hz0 (by keepz hz0) hso hsc

theorem me_ok {n k : Nat} (h8 : f 8 = out) (h9 : f 9 = p) (h18 : f 18 = BitVec.ofNat 32 n)
    (ha0 : f a0 = BitVec.ofNat 32 k) (hsp : f sp = s) (hO : Out M M1 s 16) (hS : Slots meCs s Mp M1)
    (hv : MeSaved s g0 Mp) (hsp0 : g0 sp = s + BitVec.ofNat 32 16) (hret : g0 ra &&& ~~~1 = g0 ra)
    (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ meL → f x = g0 x)
    (hso : Sep out 12 s 16) (hsc : Sep out 12 base jsonMembersCode.length) :
    WP jsonMembersCode base (RPost (g0 ra) (fun M' => CurResF M M' out s 16 0x21 (some (p, n, k))) g0) M1 0x2A f := by
  refine WP.zero fun hz => ?_
  refine WP.sw me_at_2a (by rw [h8]; exact aligned_add halo (k := 4) (by decide))
    (by rw [h8]; exact hsc.sub (c := 4) (by decide)) ?_; wn
  refine WP.sw me_at_2e (by (try rsimp); rw [h8]; exact aligned_add halo (k := 8) (by decide))
    (by (try rsimp); rw [h8]; exact hsc.sub (c := 8) (by decide)) ?_; wn
  refine WP.jal me_at_30 (by decide) ?_; wn
  rw [h8, h18, ha0]
  exact me_3c (by (try rsimp); exact h8) (by (try rsimp); exact h9) (by (try rsimp); exact hsp) hO hS hv
    (curRes_ok M1 out p n k 0x21) hsp0 hret hal halo hz0 (by keepz hz0) hso hsc

theorem me_wp {n : Nat} (h0 : f a0 = out) (h1 : f a1 = p) (h2 : f a2 = BitVec.ofNat 32 n)
    (hsp : f sp = s + BitVec.ofNat 32 16) (hn : n < 2 ^ 32) (hret : f ra &&& ~~~1 = f ra)
    (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hb : base.toNat % 2 = 0)
    (hcw : CodeIn M (base + 0xFFFFF7F8) jsonSkipWsCode) (hSc : Sep s 16 base jsonMembersCode.length)
    (hSw : Sep s 16 (base + 0xFFFFF7F8) jsonSkipWsCode.length) (hSp : Sep s 16 p n) (hso : Sep out 12 s 16)
    (hsc : Sep out 12 base jsonMembersCode.length) :
    WP jsonMembersCode base (RPost (f ra) (fun M' => CurResF M M' out s 16 0x21 (curOpen 123 p (memBytes M p n))) f)
      M 0 f := by
  refine WP.zero fun hz => ?_
  have esp : aluEval .add (f sp) 0xFFFFFFF0 = s := by
    rw [hsp, ev_add, BitVec.add_assoc, show BitVec.ofNat 32 16 + (0xFFFFFFF0 : Word) = 0 from by decide]
    exact BitVec.add_zero s
  have hlen : (memBytes M p n).length = n := memBytes_length M p n
  refine WP.aluImm me_at_0 ?_; wn
  rw [esp]
  refine WP.sw me_at_2 (by (try rsimp); exact aligned_add hal (k := 12) (by decide))
    (by (try rsimp); exact hSc.sub (c := 12) (by decide)) ?_; wn
  refine WP.sw me_at_4 (by (try rsimp); exact aligned_add hal (k := 8) (by decide))
    (by (try rsimp); exact hSc.sub (c := 8) (by decide)) ?_; wn
  refine WP.sw me_at_6 (by (try rsimp); exact aligned_add hal (k := 4) (by decide))
    (by (try rsimp); exact hSc.sub (c := 4) (by decide)) ?_; wn
  refine WP.sw me_at_8 (by (try rsimp); exact aligned_add hal (k := 0) (by decide))
    (by (try rsimp); exact hSc.sub (c := 0) (by decide)) ?_; wn
  change WP jsonMembersCode base _ (meM1 M s f) 0xA _
  obtain ⟨hO1, hv⟩ := me_pro M s f
  have hsp0 : f sp = s + BitVec.ofNat 32 16 := hsp
  refine WP.alu me_at_a ?_; wn
  refine WP.branch me_at_c (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    rw [h2, br_beq0 hn] at e
    have hl0 : (memBytes M p n).length = 0 := by have := of_decide_eq_true e; omega
    simp only [curOpen, hl0, ↓reduceIte]
    exact me_err (by (try rsimp); simp only [ev0, ev_mv hz, h0]) (by try rsimp) hO1 (Slots.refl _ _ _) hv hsp0 hret hal
      halo hz (by keepz hz) hso hsc
  rsimp at e
  rw [h2, br_beq0 hn] at e
  have hpos : 0 < n := by have := of_decide_eq_false e; omega
  have hl0 : ¬(memBytes M p n).length = 0 := by omega
  have hb0 : meM1 M s f p = M p := by
    have := hO1.byte hSp (i := 0) hpos; rwa [add_ofNat_zero] at this
  have hg0 : (memBytes M p n).getD 0 0 = (M p).toNat := by rw [memBytes_getD hpos, add_ofNat_zero]
  refine WP.alu me_at_e ?_; wn
  refine WP.lbu me_at_10 ?_; wn
  refine WP.aluImm me_at_14 ?_; wn
  rw [h1, add_lit_zero, hb0]
  refine WP.branch me_at_18 (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    rw [me_open] at e
    have hne : (memBytes M p n).getD 0 0 ≠ 123 := by rw [hg0]; exact nbeq_true e
    simp only [curOpen, hl0, hne, ne_eq, not_false_eq_true, ↓reduceIte]
    exact me_err (by (try rsimp); simp only [ev0, ev_mv hz, h0]) (by try rsimp) hO1 (Slots.refl _ _ _) hv hsp0 hret hal
      halo hz (by keepz hz) hso hsc
  rsimp at e
  rw [me_open] at e
  have heq : (memBytes M p n).getD 0 0 = 123 := by rw [hg0]; exact nbeq_false e
  simp only [curOpen, hl0, heq, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [hlen]
  refine WP.alu me_at_1a ?_; wn
  refine WP.aluImm me_at_1c ?_; wn
  refine WP.alu me_at_1e ?_; wn
  refine WP.alu me_at_20 ?_; wn
  refine WP.callSkipWs (tb := base + 0xFFFFF7F8) (p := p) (n := n) (q := 1) me_at_22 me_at_26
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hb 0xFFFFF7F8 (by decide)) (by decide)
    (hO1.codeIn hcw hSw) (by (try rsimp); simp only [ev0, ev_mv hz, h1]) (by (try rsimp); simp only [ev0, ev_mv hz, h2])
    (by (try rsimp); try rfl) hn (by decide) fun m3 r0 => ?_
  rw [hO1.bytes hSp] at r0
  exact me_ok (by (try rsimp); simp only [ev0, ev_mv hz, h0]) (by (try rsimp); simp only [ev0, ev_mv hz, h1])
    (by (try rsimp); simp only [ev0, ev_mv hz, h2]) (by (try rsimp); exact r0) (by try rsimp) hO1 (Slots.refl _ _ _) hv hsp0
    hret hal halo hz (by keepz hz) hso hsc

end

/-- `Value::members` on the `n` bytes at `p`: stores `curOpen 123 p` of them
at `out` as a `Result<Members, TufError>` with `Err(Schema)` (`0x21`), changes
no memory outside `out` and the 16 bytes below `sp`, and keeps every
register outside `jClob`. -/
theorem jsonMembers_correct (m : Machine) {base retAddr out s p : Word} {n : Nat}
    (hb : base.toNat % 2 = 0) (hc : CodeIn m.mem base jsonMembersCode)
    (hcw : CodeIn m.mem (base + 0xFFFFF7F8) jsonSkipWsCode) (hpc : m.pc = base) (ha0 : reg m a0 = out)
    (ha1 : reg m a1 = p) (ha2 : reg m a2 = BitVec.ofNat 32 n) (hsp : reg m sp = s + BitVec.ofNat 32 16)
    (hn : n < 2 ^ 32) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hSc : Sep s 16 base jsonMembersCode.length)
    (hSw : Sep s 16 (base + 0xFFFFF7F8) jsonSkipWsCode.length) (hSp : Sep s 16 p n) (hso : Sep out 12 s 16)
    (hsc : Sep out 12 base jsonMembersCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      CurResF m.mem m'.mem out s 16 0x21 (curOpen 123 p (memBytes m.mem p n)) ∧
      ∀ r, r ∉ jClob → reg m' r = reg m r := by
  obtain ⟨m', st, hpc', hR, hfr⟩ := WP.run (me_wp ha0 ha1 ha2 hsp hn (by rw [hra]; exact hret) hal halo hb hcw
    hSc hSw hSp hso hsc) hb hc hpc
  exact ⟨m', st, hpc'.trans hra, hR, hfr⟩

theorem el_at_0 : fetchRel jsonElementsCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem el_at_2 : fetchRel jsonElementsCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem el_at_4 : fetchRel jsonElementsCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x8, 2) := by decide
theorem el_at_6 : fetchRel jsonElementsCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x4, 2) := by decide
theorem el_at_8 : fetchRel jsonElementsCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x0, 2) := by decide
theorem el_at_a : fetchRel jsonElementsCode 0xA = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem el_at_c : fetchRel jsonElementsCode 0xC = some (.branch .beq a2 x0 0x26, 2) := by decide
theorem el_at_e : fetchRel jsonElementsCode 0xE = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem el_at_10 : fetchRel jsonElementsCode 0x10 = some (.load .lbu a0 a1 0x0, 4) := by decide
theorem el_at_14 : fetchRel jsonElementsCode 0x14 = some (.aluImm .add a0 a0 0xFFFFFFA5, 4) := by decide
theorem el_at_18 : fetchRel jsonElementsCode 0x18 = some (.branch .bne a0 x0 0x1A, 2) := by decide
theorem el_at_1a : fetchRel jsonElementsCode 0x1A = some (.alu .add (18 : Fin 32) x0 a2, 2) := by decide
theorem el_at_1c : fetchRel jsonElementsCode 0x1C = some (.aluImm .add a2 x0 0x1, 2) := by decide
theorem el_at_1e : fetchRel jsonElementsCode 0x1E = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem el_at_20 : fetchRel jsonElementsCode 0x20 = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem el_at_22 : fetchRel jsonElementsCode 0x22 = some (.auipc ra 0x0, 4) := by decide
theorem el_at_26 : fetchRel jsonElementsCode 0x26 = some (.jalr ra ra 0xFFFFFA90, 4) := by decide
theorem el_at_2a : fetchRel jsonElementsCode 0x2A = some (.store .sw (8 : Fin 32) (18 : Fin 32) 0x4, 4) := by decide
theorem el_at_2e : fetchRel jsonElementsCode 0x2E = some (.store .sw (8 : Fin 32) a0 0x8, 2) := by decide
theorem el_at_30 : fetchRel jsonElementsCode 0x30 = some (.jal x0 0xC, 2) := by decide
theorem el_at_32 : fetchRel jsonElementsCode 0x32 = some (.aluImm .add (9 : Fin 32) x0 0x0, 2) := by decide
theorem el_at_34 : fetchRel jsonElementsCode 0x34 = some (.aluImm .add a0 x0 0x21, 4) := by decide
theorem el_at_38 : fetchRel jsonElementsCode 0x38 = some (.store .sb (8 : Fin 32) a0 0x4, 4) := by decide
theorem el_at_3c : fetchRel jsonElementsCode 0x3C = some (.store .sw (8 : Fin 32) (9 : Fin 32) 0x0, 2) := by decide
theorem el_at_3e : fetchRel jsonElementsCode 0x3E = some (.load .lw ra sp 0xC, 2) := by decide
theorem el_at_40 : fetchRel jsonElementsCode 0x40 = some (.load .lw (8 : Fin 32) sp 0x8, 2) := by decide
theorem el_at_42 : fetchRel jsonElementsCode 0x42 = some (.load .lw (9 : Fin 32) sp 0x4, 2) := by decide
theorem el_at_44 : fetchRel jsonElementsCode 0x44 = some (.load .lw (18 : Fin 32) sp 0x0, 2) := by decide
theorem el_at_46 : fetchRel jsonElementsCode 0x46 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem el_at_48 : fetchRel jsonElementsCode 0x48 = some (.jalr x0 ra 0x0, 2) := by decide

theorem el_open : ∀ b : BitVec 8,
    branchTaken .bne (aluEval .add (b.zeroExtend 32) 0xFFFFFFA5) 0 = !(b.toNat == 91) := by decide

section
variable {M M1 Mp : Word → BitVec 8} {base out s p : Word} {f g0 : Fin 32 → Word}

theorem el_epi {Mf : Word → BitVec 8} {R : (Word → BitVec 8) → Prop} (hsp : f sp = s)
    (hS : Slots meCs s M1 Mf) (hv : MeSaved s g0 M1) (hsp0 : g0 sp = s + BitVec.ofNat 32 16)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hal : s.toNat % 4 = 0) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ meL → f x = g0 x) (hR : R Mf) :
    WP jsonElementsCode base (RPost (g0 ra) R g0) Mf 0x3E f := by
  obtain ⟨v1, v2, v3, v4⟩ := hv
  have e1 : memLoad32 Mf (s + 0xC) = g0 ra := (hS 12 (by decide)).trans v1
  have e2 : memLoad32 Mf (s + 0x8) = g0 8 := (hS 8 (by decide)).trans v2
  have e3 : memLoad32 Mf (s + 0x4) = g0 9 := (hS 4 (by decide)).trans v3
  have e4 : memLoad32 Mf (s + 0x0) = g0 18 := (hS 0 (by decide)).trans v4
  refine WP.lw el_at_3e (by rw [hsp]; exact aligned_add hal (k := 12) (by decide)) ?_; wn
  refine WP.lw el_at_40 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 8) (by decide)) ?_; wn
  refine WP.lw el_at_42 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 4) (by decide)) ?_; wn
  refine WP.lw el_at_44 (by (try rsimp); rw [hsp]; exact aligned_add hal (k := 0) (by decide)) ?_; wn
  refine WP.aluImm el_at_46 ?_; wn
  refine WP.ret el_at_48 ⟨?_, hR, ?_⟩
  · rsimp; rw [hsp, e1, add_lit_zero, hret]
  refine frame_of (L2 := [ra, sp, 8, 9, 18]) (by keepz hz0) fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> rsimp
  · rw [hsp, e1]
  · rw [hsp, hsp0]; rfl
  · rw [hsp, e2]
  · rw [hsp, e3]
  · rw [hsp, e4]

theorem el_3c {q : Word} {M2 : Word → BitVec 8} {r : Option (Word × Nat × Nat)} (h8 : f 8 = out)
    (h9 : f 9 = q) (hsp : f sp = s) (hO : Out M M1 s 16) (hS : Slots meCs s Mp M1) (hv : MeSaved s g0 Mp)
    (hR : CurRes M1 (memStore32 M2 out q) out 0x21 r) (hsp0 : g0 sp = s + BitVec.ofNat 32 16)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ meL → f x = g0 x) (hso : Sep out 12 s 16) (hsc : Sep out 12 base jsonElementsCode.length) :
    WP jsonElementsCode base (RPost (g0 ra) (fun M' => CurResF M M' out s 16 0x21 r) g0) M2 0x3C f := by
  refine WP.zero fun hz => ?_
  refine WP.sw el_at_3c (by rw [h8]; exact aligned_add halo (k := 0) (by decide))
    (by rw [h8]; exact hsc.sub (c := 0) (by decide)) ?_; wn
  rw [h8, h9, add_lit_zero]
  exact el_epi (by (try rsimp); exact hsp) (hS.out hR.out (slots_sep_out hso (by decide))) hv hsp0 hret hal hz0
    (by keepz hz0) ⟨M1, hO, hR⟩

theorem el_err (h8 : f 8 = out) (hsp : f sp = s) (hO : Out M M1 s 16) (hS : Slots meCs s Mp M1)
    (hv : MeSaved s g0 Mp) (hsp0 : g0 sp = s + BitVec.ofNat 32 16) (hret : g0 ra &&& ~~~1 = g0 ra)
    (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ meL → f x = g0 x)
    (hso : Sep out 12 s 16) (hsc : Sep out 12 base jsonElementsCode.length) :
    WP jsonElementsCode base (RPost (g0 ra) (fun M' => CurResF M M' out s 16 0x21 none) g0) M1 0x32 f := by
  refine WP.zero fun hz => ?_
  refine WP.aluImm el_at_32 ?_; wn
  refine WP.aluImm el_at_34 ?_; wn
  refine WP.sb el_at_38 (by (try rsimp); rw [h8]; exact hsc.shift (c := 4) (by decide)) ?_; wn
  rw [h8]
  exact el_3c (q := 0) (by (try rsimp); exact h8) (by (try rsimp); simp only [ev0, ev_mv hz]) (by (try rsimp); exact hsp) hO hS hv (curRes_err M1 out 0x21)
    hsp0 hret hal halo hz0 (by keepz hz0) hso hsc

theorem el_ok {n k : Nat} (h8 : f 8 = out) (h9 : f 9 = p) (h18 : f 18 = BitVec.ofNat 32 n)
    (ha0 : f a0 = BitVec.ofNat 32 k) (hsp : f sp = s) (hO : Out M M1 s 16) (hS : Slots meCs s Mp M1)
    (hv : MeSaved s g0 Mp) (hsp0 : g0 sp = s + BitVec.ofNat 32 16) (hret : g0 ra &&& ~~~1 = g0 ra)
    (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ meL → f x = g0 x)
    (hso : Sep out 12 s 16) (hsc : Sep out 12 base jsonElementsCode.length) :
    WP jsonElementsCode base (RPost (g0 ra) (fun M' => CurResF M M' out s 16 0x21 (some (p, n, k))) g0) M1 0x2A f := by
  refine WP.zero fun hz => ?_
  refine WP.sw el_at_2a (by rw [h8]; exact aligned_add halo (k := 4) (by decide))
    (by rw [h8]; exact hsc.sub (c := 4) (by decide)) ?_; wn
  refine WP.sw el_at_2e (by (try rsimp); rw [h8]; exact aligned_add halo (k := 8) (by decide))
    (by (try rsimp); rw [h8]; exact hsc.sub (c := 8) (by decide)) ?_; wn
  refine WP.jal el_at_30 (by decide) ?_; wn
  rw [h8, h18, ha0]
  exact el_3c (by (try rsimp); exact h8) (by (try rsimp); exact h9) (by (try rsimp); exact hsp) hO hS hv
    (curRes_ok M1 out p n k 0x21) hsp0 hret hal halo hz0 (by keepz hz0) hso hsc

theorem el_wp {n : Nat} (h0 : f a0 = out) (h1 : f a1 = p) (h2 : f a2 = BitVec.ofNat 32 n)
    (hsp : f sp = s + BitVec.ofNat 32 16) (hn : n < 2 ^ 32) (hret : f ra &&& ~~~1 = f ra)
    (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0) (hb : base.toNat % 2 = 0)
    (hcw : CodeIn M (base + 0xFFFFFAB2) jsonSkipWsCode) (hSc : Sep s 16 base jsonElementsCode.length)
    (hSw : Sep s 16 (base + 0xFFFFFAB2) jsonSkipWsCode.length) (hSp : Sep s 16 p n) (hso : Sep out 12 s 16)
    (hsc : Sep out 12 base jsonElementsCode.length) :
    WP jsonElementsCode base (RPost (f ra) (fun M' => CurResF M M' out s 16 0x21 (curOpen 91 p (memBytes M p n))) f)
      M 0 f := by
  refine WP.zero fun hz => ?_
  have esp : aluEval .add (f sp) 0xFFFFFFF0 = s := by
    rw [hsp, ev_add, BitVec.add_assoc, show BitVec.ofNat 32 16 + (0xFFFFFFF0 : Word) = 0 from by decide]
    exact BitVec.add_zero s
  have hlen : (memBytes M p n).length = n := memBytes_length M p n
  refine WP.aluImm el_at_0 ?_; wn
  rw [esp]
  refine WP.sw el_at_2 (by (try rsimp); exact aligned_add hal (k := 12) (by decide))
    (by (try rsimp); exact hSc.sub (c := 12) (by decide)) ?_; wn
  refine WP.sw el_at_4 (by (try rsimp); exact aligned_add hal (k := 8) (by decide))
    (by (try rsimp); exact hSc.sub (c := 8) (by decide)) ?_; wn
  refine WP.sw el_at_6 (by (try rsimp); exact aligned_add hal (k := 4) (by decide))
    (by (try rsimp); exact hSc.sub (c := 4) (by decide)) ?_; wn
  refine WP.sw el_at_8 (by (try rsimp); exact aligned_add hal (k := 0) (by decide))
    (by (try rsimp); exact hSc.sub (c := 0) (by decide)) ?_; wn
  change WP jsonElementsCode base _ (meM1 M s f) 0xA _
  obtain ⟨hO1, hv⟩ := me_pro M s f
  have hsp0 : f sp = s + BitVec.ofNat 32 16 := hsp
  refine WP.alu el_at_a ?_; wn
  refine WP.branch el_at_c (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    rw [h2, br_beq0 hn] at e
    have hl0 : (memBytes M p n).length = 0 := by have := of_decide_eq_true e; omega
    simp only [curOpen, hl0, ↓reduceIte]
    exact el_err (by (try rsimp); simp only [ev0, ev_mv hz, h0]) (by try rsimp) hO1 (Slots.refl _ _ _) hv hsp0 hret hal
      halo hz (by keepz hz) hso hsc
  rsimp at e
  rw [h2, br_beq0 hn] at e
  have hpos : 0 < n := by have := of_decide_eq_false e; omega
  have hl0 : ¬(memBytes M p n).length = 0 := by omega
  have hb0 : meM1 M s f p = M p := by
    have := hO1.byte hSp (i := 0) hpos; rwa [add_ofNat_zero] at this
  have hg0 : (memBytes M p n).getD 0 0 = (M p).toNat := by rw [memBytes_getD hpos, add_ofNat_zero]
  refine WP.alu el_at_e ?_; wn
  refine WP.lbu el_at_10 ?_; wn
  refine WP.aluImm el_at_14 ?_; wn
  rw [h1, add_lit_zero, hb0]
  refine WP.branch el_at_18 (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    rw [el_open] at e
    have hne : (memBytes M p n).getD 0 0 ≠ 91 := by rw [hg0]; exact nbeq_true e
    simp only [curOpen, hl0, hne, ne_eq, not_false_eq_true, ↓reduceIte]
    exact el_err (by (try rsimp); simp only [ev0, ev_mv hz, h0]) (by try rsimp) hO1 (Slots.refl _ _ _) hv hsp0 hret hal
      halo hz (by keepz hz) hso hsc
  rsimp at e
  rw [el_open] at e
  have heq : (memBytes M p n).getD 0 0 = 91 := by rw [hg0]; exact nbeq_false e
  simp only [curOpen, hl0, heq, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [hlen]
  refine WP.alu el_at_1a ?_; wn
  refine WP.aluImm el_at_1c ?_; wn
  refine WP.alu el_at_1e ?_; wn
  refine WP.alu el_at_20 ?_; wn
  refine WP.callSkipWs (tb := base + 0xFFFFFAB2) (p := p) (n := n) (q := 1) el_at_22 el_at_26
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hb 0xFFFFFAB2 (by decide)) (by decide)
    (hO1.codeIn hcw hSw) (by (try rsimp); simp only [ev0, ev_mv hz, h1]) (by (try rsimp); simp only [ev0, ev_mv hz, h2])
    (by (try rsimp); try rfl) hn (by decide) fun m3 r0 => ?_
  rw [hO1.bytes hSp] at r0
  exact el_ok (by (try rsimp); simp only [ev0, ev_mv hz, h0]) (by (try rsimp); simp only [ev0, ev_mv hz, h1])
    (by (try rsimp); simp only [ev0, ev_mv hz, h2]) (by (try rsimp); exact r0) (by try rsimp) hO1 (Slots.refl _ _ _) hv hsp0
    hret hal halo hz (by keepz hz) hso hsc

end

/-- `Value::elements` on the `n` bytes at `p`: stores `curOpen 91 p` of them
at `out` as a `Result<Elements, TufError>` with `Err(Schema)` (`0x21`), changes
no memory outside `out` and the 16 bytes below `sp`, and keeps every
register outside `jClob`. -/
theorem jsonElements_correct (m : Machine) {base retAddr out s p : Word} {n : Nat}
    (hb : base.toNat % 2 = 0) (hc : CodeIn m.mem base jsonElementsCode)
    (hcw : CodeIn m.mem (base + 0xFFFFFAB2) jsonSkipWsCode) (hpc : m.pc = base) (ha0 : reg m a0 = out)
    (ha1 : reg m a1 = p) (ha2 : reg m a2 = BitVec.ofNat 32 n) (hsp : reg m sp = s + BitVec.ofNat 32 16)
    (hn : n < 2 ^ 32) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hSc : Sep s 16 base jsonElementsCode.length)
    (hSw : Sep s 16 (base + 0xFFFFFAB2) jsonSkipWsCode.length) (hSp : Sep s 16 p n) (hso : Sep out 12 s 16)
    (hsc : Sep out 12 base jsonElementsCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      CurResF m.mem m'.mem out s 16 0x21 (curOpen 91 p (memBytes m.mem p n)) ∧
      ∀ r, r ∉ jClob → reg m' r = reg m r := by
  obtain ⟨m', st, hpc', hR, hfr⟩ := WP.run (el_wp ha0 ha1 ha2 hsp hn (by rw [hra]; exact hret) hal halo hb hcw
    hSc hSw hSp hso hsc) hb hc hpc
  exact ⟨m', st, hpc'.trans hra, hR, hfr⟩

end C3.RV32
