import C3BootProofs.Proofs.JsonCalls

/-!
# `json::key_end`, as compiled

`key_end(doc, pos, mode)` stores `Ok` of the position after an object key,
its colon, and in strict mode the whitespace around the colon, or
`Err(Json)`, at `out`. It saves `ra` and `s0`–`s3` in a 32-byte frame and
keeps `string_end`'s result in that frame, so its stack region is the 32
bytes below `sp`. `string_end` is at `base - 0x5A` and `skip_ws` at
`base + 0x322`.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

theorem ke_at_0 : fetchRel jsonKeyEndCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem ke_at_2 : fetchRel jsonKeyEndCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem ke_at_4 : fetchRel jsonKeyEndCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem ke_at_6 : fetchRel jsonKeyEndCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x14, 2) := by decide
theorem ke_at_8 : fetchRel jsonKeyEndCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x10, 2) := by decide
theorem ke_at_a : fetchRel jsonKeyEndCode 0xA = some (.store .sw sp (19 : Fin 32) 0xC, 2) := by decide
theorem ke_at_c : fetchRel jsonKeyEndCode 0xC = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem ke_at_e : fetchRel jsonKeyEndCode 0xE = some (.branch .bgeu a3 a2 0x70, 4) := by decide
theorem ke_at_12 : fetchRel jsonKeyEndCode 0x12 = some (.alu .add (18 : Fin 32) x0 a1, 2) := by decide
theorem ke_at_14 : fetchRel jsonKeyEndCode 0x14 = some (.alu .add a0 a1 a3, 4) := by decide
theorem ke_at_18 : fetchRel jsonKeyEndCode 0x18 = some (.load .lbu a0 a0 0x0, 4) := by decide
theorem ke_at_1c : fetchRel jsonKeyEndCode 0x1C = some (.aluImm .add a0 a0 0xFFFFFFDE, 4) := by decide
theorem ke_at_20 : fetchRel jsonKeyEndCode 0x20 = some (.branch .bne a0 x0 0x5E, 2) := by decide
theorem ke_at_22 : fetchRel jsonKeyEndCode 0x22 = some (.alu .add (19 : Fin 32) x0 a4, 2) := by decide
theorem ke_at_24 : fetchRel jsonKeyEndCode 0x24 = some (.alu .add (9 : Fin 32) x0 a2, 2) := by decide
theorem ke_at_26 : fetchRel jsonKeyEndCode 0x26 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem ke_at_28 : fetchRel jsonKeyEndCode 0x28 = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem ke_at_2a : fetchRel jsonKeyEndCode 0x2A = some (.auipc ra 0x0, 4) := by decide
theorem ke_at_2e : fetchRel jsonKeyEndCode 0x2E = some (.jalr ra ra 0xFFFFFF7C, 4) := by decide
theorem ke_at_32 : fetchRel jsonKeyEndCode 0x32 = some (.load .lbu a0 sp 0x4, 4) := by decide
theorem ke_at_36 : fetchRel jsonKeyEndCode 0x36 = some (.branch .beq a0 x0 0x8, 2) := by decide
theorem ke_at_38 : fetchRel jsonKeyEndCode 0x38 = some (.load .lbu a0 sp 0x5, 4) := by decide
theorem ke_at_3c : fetchRel jsonKeyEndCode 0x3C = some (.jal x0 0x46, 2) := by decide
theorem ke_at_3e : fetchRel jsonKeyEndCode 0x3E = some (.load .lw a2 sp 0x8, 2) := by decide
theorem ke_at_40 : fetchRel jsonKeyEndCode 0x40 = some (.branch .bne (19 : Fin 32) x0 0x12, 4) := by decide
theorem ke_at_44 : fetchRel jsonKeyEndCode 0x44 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem ke_at_46 : fetchRel jsonKeyEndCode 0x46 = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem ke_at_48 : fetchRel jsonKeyEndCode 0x48 = some (.auipc ra 0x0, 4) := by decide
theorem ke_at_4c : fetchRel jsonKeyEndCode 0x4C = some (.jalr ra ra 0x2DA, 4) := by decide
theorem ke_at_50 : fetchRel jsonKeyEndCode 0x50 = some (.alu .add a2 x0 a0, 2) := by decide
theorem ke_at_52 : fetchRel jsonKeyEndCode 0x52 = some (.branch .bgeu a2 (9 : Fin 32) 0x2C, 4) := by decide
theorem ke_at_56 : fetchRel jsonKeyEndCode 0x56 = some (.alu .add a0 (18 : Fin 32) a2, 4) := by decide
theorem ke_at_5a : fetchRel jsonKeyEndCode 0x5A = some (.load .lbu a0 a0 0x0, 4) := by decide
theorem ke_at_5e : fetchRel jsonKeyEndCode 0x5E = some (.aluImm .add a0 a0 0xFFFFFFC6, 4) := by decide
theorem ke_at_62 : fetchRel jsonKeyEndCode 0x62 = some (.branch .bne a0 x0 0x1C, 2) := by decide
theorem ke_at_64 : fetchRel jsonKeyEndCode 0x64 = some (.aluImm .add a2 a2 0x1, 2) := by decide
theorem ke_at_66 : fetchRel jsonKeyEndCode 0x66 = some (.branch .bne (19 : Fin 32) x0 0x12, 4) := by decide
theorem ke_at_6a : fetchRel jsonKeyEndCode 0x6A = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem ke_at_6c : fetchRel jsonKeyEndCode 0x6C = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem ke_at_6e : fetchRel jsonKeyEndCode 0x6E = some (.auipc ra 0x0, 4) := by decide
theorem ke_at_72 : fetchRel jsonKeyEndCode 0x72 = some (.jalr ra ra 0x2B4, 4) := by decide
theorem ke_at_76 : fetchRel jsonKeyEndCode 0x76 = some (.alu .add a2 x0 a0, 2) := by decide
theorem ke_at_78 : fetchRel jsonKeyEndCode 0x78 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem ke_at_7a : fetchRel jsonKeyEndCode 0x7A = some (.store .sw (8 : Fin 32) a2 0x4, 2) := by decide
theorem ke_at_7c : fetchRel jsonKeyEndCode 0x7C = some (.jal x0 0xC, 2) := by decide
theorem ke_at_7e : fetchRel jsonKeyEndCode 0x7E = some (.aluImm .add a0 x0 0x20, 4) := by decide
theorem ke_at_82 : fetchRel jsonKeyEndCode 0x82 = some (.store .sb (8 : Fin 32) a0 0x1, 4) := by decide
theorem ke_at_86 : fetchRel jsonKeyEndCode 0x86 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem ke_at_88 : fetchRel jsonKeyEndCode 0x88 = some (.store .sb (8 : Fin 32) a0 0x0, 4) := by decide
theorem ke_at_8c : fetchRel jsonKeyEndCode 0x8C = some (.load .lw ra sp 0x1C, 2) := by decide
theorem ke_at_8e : fetchRel jsonKeyEndCode 0x8E = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem ke_at_90 : fetchRel jsonKeyEndCode 0x90 = some (.load .lw (9 : Fin 32) sp 0x14, 2) := by decide
theorem ke_at_92 : fetchRel jsonKeyEndCode 0x92 = some (.load .lw (18 : Fin 32) sp 0x10, 2) := by decide
theorem ke_at_94 : fetchRel jsonKeyEndCode 0x94 = some (.load .lw (19 : Fin 32) sp 0xC, 2) := by decide
theorem ke_at_96 : fetchRel jsonKeyEndCode 0x96 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem ke_at_98 : fetchRel jsonKeyEndCode 0x98 = some (.jalr x0 ra 0x0, 2) := by decide

theorem ke_q : ∀ b : BitVec 8,
    branchTaken .bne (aluEval .add (b.zeroExtend 32) 0xFFFFFFDE) 0 = !(b.toNat == 34) := by decide

theorem ke_colon : ∀ b : BitVec 8,
    branchTaken .bne (aluEval .add (b.zeroExtend 32) 0xFFFFFFC6) 0 = !(b.toNat == 58) := by decide

/-- The registers `key_end` changes before its epilogue restores the saved ones. -/
abbrev keL : List (Fin 32) := jClob ++ [ra, sp, 8, 9, 18, 19]

/-- The frame offsets of the saved registers. -/
abbrev keCs : List Nat := [12, 16, 20, 24, 28]

/-- The saved registers in the frame at `s`. -/
def KeSaved (s : Word) (g0 : Fin 32 → Word) (M1 : Word → BitVec 8) : Prop :=
  memLoad32 M1 (s + BitVec.ofNat 32 28) = g0 ra ∧ memLoad32 M1 (s + BitVec.ofNat 32 24) = g0 8 ∧
    memLoad32 M1 (s + BitVec.ofNat 32 20) = g0 9 ∧ memLoad32 M1 (s + BitVec.ofNat 32 16) = g0 18 ∧
    memLoad32 M1 (s + BitVec.ofNat 32 12) = g0 19

/-- Memory after the prologue. -/
def keM1 (M : Word → BitVec 8) (s : Word) (g0 : Fin 32 → Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (s + 28) (g0 ra)) (s + 24) (g0 8))
    (s + 20) (g0 9)) (s + 16) (g0 18)) (s + 12) (g0 19)

theorem ke_pro (M : Word → BitVec 8) (s : Word) (g0 : Fin 32 → Word) :
    Out M (keM1 M s g0) s 32 ∧ KeSaved s g0 (keM1 M s g0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((((out_store32 _ _ _).widen (d := 28) (by decide)).trans
      ((out_store32 _ _ _).widen (d := 24) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 20) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 16) (by decide))).trans
      ((out_store32 _ _ _).widen (d := 12) (by decide))
  · exact ld_skip 28 12 (by decide) (by decide) (by decide) (ld_skip 28 16 (by decide) (by decide) (by decide)
      (ld_skip 28 20 (by decide) (by decide) (by decide) (ld_skip 28 24 (by decide) (by decide) (by decide)
      (memLoad32_store32_same _ _ _))))
  · exact ld_skip 24 12 (by decide) (by decide) (by decide) (ld_skip 24 16 (by decide) (by decide) (by decide)
      (ld_skip 24 20 (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _)))
  · exact ld_skip 20 12 (by decide) (by decide) (by decide) (ld_skip 20 16 (by decide) (by decide) (by decide)
      (memLoad32_store32_same _ _ _))
  · exact ld_skip 16 12 (by decide) (by decide) (by decide) (memLoad32_store32_same _ _ _)
  · exact memLoad32_store32_same _ _ _

section
variable {M M1 M2 : Word → BitVec 8} {base out s p : Word} {f g0 : Fin 32 → Word}

theorem ke_epi {Mf : Word → BitVec 8} {r : Option Nat} (hsp : f sp = s) (hS : Slots keCs s M1 Mf)
    (hv : KeSaved s g0 M1) (hsp0 : g0 sp = s + BitVec.ofNat 32 32) (hret : g0 ra &&& ~~~1 = g0 ra)
    (hal : s.toNat % 4 = 0) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ keL → f x = g0 x)
    (hR : UsizeResF M Mf out s 32 r) :
    WP jsonKeyEndCode base (FPost (g0 ra) M out s 32 r g0) Mf 0x8C f := by
  obtain ⟨v1, v2, v3, v4, v5⟩ := hv
  have e1 : memLoad32 Mf (s + 0x1C) = g0 ra := (hS 28 (by decide)).trans v1
  have e2 : memLoad32 Mf (s + 0x18) = g0 8 := (hS 24 (by decide)).trans v2
  have e3 : memLoad32 Mf (s + 0x14) = g0 9 := (hS 20 (by decide)).trans v3
  have e4 : memLoad32 Mf (s + 0x10) = g0 18 := (hS 16 (by decide)).trans v4
  have e5 : memLoad32 Mf (s + 0xC) = g0 19 := (hS 12 (by decide)).trans v5
  refine WP.lw ke_at_8c (by rw [hsp]; exact aligned_add hal (k := 28) (by decide)) ?_; wn
  refine WP.lw ke_at_8e (by rsimp; rw [hsp]; exact aligned_add hal (k := 24) (by decide)) ?_; wn
  refine WP.lw ke_at_90 (by rsimp; rw [hsp]; exact aligned_add hal (k := 20) (by decide)) ?_; wn
  refine WP.lw ke_at_92 (by rsimp; rw [hsp]; exact aligned_add hal (k := 16) (by decide)) ?_; wn
  refine WP.lw ke_at_94 (by rsimp; rw [hsp]; exact aligned_add hal (k := 12) (by decide)) ?_; wn
  refine WP.aluImm ke_at_96 ?_; wn
  refine WP.ret ke_at_98 ⟨?_, hR, ?_⟩
  · rsimp; rw [hsp, e1, add_lit_zero, hret]
  refine frame_of (L2 := [ra, sp, 8, 9, 18, 19]) (by keepz hz0) fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> rsimp
  · rw [hsp, e1]
  · rw [hsp, hsp0]; rfl
  · rw [hsp, e2]
  · rw [hsp, e3]
  · rw [hsp, e4]
  · rw [hsp, e5]

theorem ke_err20 (h8 : f 8 = out) (hsp : f sp = s) (ha0 : f a0 = 0x20) (hO : Out M M2 s 32)
    (hS : Slots keCs s M1 M2) (hv : KeSaved s g0 M1) (hsp0 : g0 sp = s + BitVec.ofNat 32 32)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hal : s.toNat % 4 = 0) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ keL → f x = g0 x) (hso : Sep out 8 s 32) (hsc : Sep out 8 base jsonKeyEndCode.length) :
    WP jsonKeyEndCode base (FPost (g0 ra) M out s 32 none g0) M2 0x82 f := by
  refine WP.zero fun hz => ?_
  refine WP.sb ke_at_82 (by rw [h8]; exact hsc.shift (c := 1) (by decide)) ?_; wn
  refine WP.aluImm ke_at_86 ?_; wn
  refine WP.sb ke_at_88 (by rsimp; rw [h8]; exact hsc.shift (c := 0) (by decide)) ?_; wn
  rw [h8, ha0, hz, add_lit_zero]
  have hU := usizeRes_err M2 out
  exact ke_epi (by rsimp; exact hsp) (hS.out hU.out (slots_sep_out hso (by decide))) hv hsp0 hret hal hz0
    (by keepz hz0) ⟨M2, hO, hU⟩

theorem ke_e7e (h8 : f 8 = out) (hsp : f sp = s) (hO : Out M M2 s 32)
    (hS : Slots keCs s M1 M2) (hv : KeSaved s g0 M1) (hsp0 : g0 sp = s + BitVec.ofNat 32 32)
    (hret : g0 ra &&& ~~~1 = g0 ra) (hal : s.toNat % 4 = 0) (hz0 : g0 0 = 0)
    (hfr : ∀ x, x ∉ keL → f x = g0 x) (hso : Sep out 8 s 32) (hsc : Sep out 8 base jsonKeyEndCode.length) :
    WP jsonKeyEndCode base (FPost (g0 ra) M out s 32 none g0) M2 0x7E f := by
  refine WP.zero fun hz => ?_
  refine WP.aluImm ke_at_7e ?_; wn
  exact ke_err20 (by rsimp; exact h8) (by rsimp; exact hsp) (by rsimp; simp only [ev0, ev_mv hz]) hO hS hv hsp0 hret
    hal hz0 (by keepz hz0) hso hsc

theorem ke_ok {v : Nat} (h8 : f 8 = out) (hsp : f sp = s) (ha2 : f a2 = BitVec.ofNat 32 v)
    (hO : Out M M2 s 32) (hS : Slots keCs s M1 M2) (hv : KeSaved s g0 M1)
    (hsp0 : g0 sp = s + BitVec.ofNat 32 32) (hret : g0 ra &&& ~~~1 = g0 ra) (hal : s.toNat % 4 = 0)
    (halo : out.toNat % 4 = 0) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ keL → f x = g0 x) (hso : Sep out 8 s 32)
    (hsc : Sep out 8 base jsonKeyEndCode.length) :
    WP jsonKeyEndCode base (FPost (g0 ra) M out s 32 (some v) g0) M2 0x78 f := by
  refine WP.zero fun hz => ?_
  refine WP.aluImm ke_at_78 ?_; wn
  refine WP.sw ke_at_7a (by rsimp; rw [h8]; exact aligned_add halo (k := 4) (by decide))
    (by rsimp; rw [h8]; exact hsc.sub (c := 4) (by decide)) ?_; wn
  refine WP.jal ke_at_7c (by decide) ?_; wn
  refine WP.sb ke_at_88 (by rsimp; rw [h8]; exact hsc.shift (c := 0) (by decide)) ?_; wn
  rw [h8, ha2, hz, add_lit_zero]
  have hU := usizeRes_ok M2 out v
  exact ke_epi (by rsimp; exact hsp) (hS.out hU.out (slots_sep_out hso (by decide))) hv hsp0 hret hal hz0
    (by keepz hz0) ⟨M2, hO, hU⟩

theorem ke_tail {c : Bool} {n q : Nat} (h8 : f 8 = out) (hsp : f sp = s) (h18 : f 18 = p)
    (h9 : f 9 = BitVec.ofNat 32 n) (h19 : f 19 = modeW c) (ha2 : f a2 = BitVec.ofNat 32 q) (hn : n < 2 ^ 32)
    (hq : q < 2 ^ 32) (hO : Out M M2 s 32) (hS : Slots keCs s M1 M2) (hv : KeSaved s g0 M1)
    (hsp0 : g0 sp = s + BitVec.ofNat 32 32) (hret : g0 ra &&& ~~~1 = g0 ra) (hal : s.toNat % 4 = 0)
    (halo : out.toNat % 4 = 0) (hz0 : g0 0 = 0) (hfr : ∀ x, x ∉ keL → f x = g0 x) (hso : Sep out 8 s 32)
    (hsc : Sep out 8 base jsonKeyEndCode.length) (hb : base.toNat % 2 = 0)
    (hcw : CodeIn M (base + 0x322) jsonSkipWsCode) (hSw : Sep s 32 (base + 0x322) jsonSkipWsCode.length)
    (hSp : Sep s 32 p n) :
    WP jsonKeyEndCode base (FPost (g0 ra) M out s 32
      (if n ≤ q then none else if (memBytes M p n).getD q 0 ≠ 58 then none
        else some (wsIn c (memBytes M p n) (q + 1))) g0) M2 0x52 f := by
  refine WP.zero fun hz => ?_
  refine WP.branch ke_at_52 (fun e => ?_) (fun e => ?_) <;> wn
  · rw [ha2, h9, br_bgeu hq hn] at e
    have hle : n ≤ q := by have := not_dec_true e; omega
    simp only [hle, ↓reduceIte]
    exact ke_e7e h8 hsp hO hS hv hsp0 hret hal hz0 hfr hso hsc
  rw [ha2, h9, br_bgeu hq hn] at e
  have hlt : q < n := not_dec_false e
  have hnq : ¬n ≤ q := by omega
  simp only [hnq, ↓reduceIte]
  refine WP.alu ke_at_56 ?_; wn
  refine WP.lbu ke_at_5a ?_; wn
  refine WP.aluImm ke_at_5e ?_; wn
  rw [h18, ha2, ev_add p, add_lit_zero, hO.byte hSp hlt]
  refine WP.branch ke_at_62 (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    rw [ke_colon] at e
    have hne : (memBytes M p n).getD q 0 ≠ 58 := by rw [memBytes_getD hlt]; exact nbeq_true e
    simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte]
    exact ke_e7e (by rsimp; exact h8) (by rsimp; exact hsp) hO hS hv hsp0 hret hal hz0 (by keepz hz0) hso hsc
  rsimp at e
  rw [ke_colon] at e
  have h58 : (memBytes M p n).getD q 0 = 58 := by rw [memBytes_getD hlt]; exact nbeq_false e
  simp only [h58, ne_eq, not_true_eq_false, ↓reduceIte]
  refine WP.aluImm ke_at_64 ?_; wn
  refine WP.branch ke_at_66 (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    rw [h19, br_mode] at e
    subst e
    exact ke_ok (by rsimp; exact h8) (by rsimp; exact hsp) (by rsimp; rw [ev_add, ha2, cl_succ]; rfl) hO hS hv hsp0 hret
      hal halo hz0 (by keepz hz0) hso hsc
  rsimp at e
  rw [h19, br_mode] at e
  subst e
  refine WP.alu ke_at_6a ?_; wn
  refine WP.alu ke_at_6c ?_; wn
  refine WP.callSkipWs (tb := base + 0x322) (p := p) (n := n) (q := q + 1) ke_at_6e ke_at_72
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hb 0x322 (by decide)) (by decide)
    (hO.codeIn hcw hSw) (by rsimp; simp only [ev0, ev_mv hz, h18]) (by rsimp; simp only [ev0, ev_mv hz, h9])
    (by rsimp; rw [ev_add, ha2, cl_succ]) hn (by omega) fun m3 r0 => ?_
  rw [hO.bytes hSp] at r0
  refine WP.alu ke_at_76 ?_; wn
  exact ke_ok (by rsimp; exact h8) (by rsimp; exact hsp) (by rsimp; simp only [ev0, ev_mv hz, r0]; rfl) hO hS hv hsp0
    hret hal halo hz0 (by keepz hz0) hso hsc

theorem ke_wp {n pos : Nat} {c : Bool} (h0 : f a0 = out) (h1 : f a1 = p) (h2 : f a2 = BitVec.ofNat 32 n)
    (h3 : f a3 = BitVec.ofNat 32 pos) (h4 : f a4 = modeW c) (hsp : f sp = s + BitVec.ofNat 32 32)
    (hn : n < 2 ^ 32) (hpos : pos < 2 ^ 32) (hret : f ra &&& ~~~1 = f ra) (hal : s.toNat % 4 = 0)
    (halo : out.toNat % 4 = 0) (hb : base.toNat % 2 = 0)
    (hcs : CodeIn M (base + 0xFFFFFFA6) jsonStringEndCode) (hcw : CodeIn M (base + 0x322) jsonSkipWsCode)
    (hSc : Sep s 32 base jsonKeyEndCode.length)
    (hSs : Sep s 32 (base + 0xFFFFFFA6) jsonStringEndCode.length)
    (hSw : Sep s 32 (base + 0x322) jsonSkipWsCode.length) (hSp : Sep s 32 p n) (hso : Sep out 8 s 32)
    (hsc : Sep out 8 base jsonKeyEndCode.length) :
    WP jsonKeyEndCode base (FPost (f ra) M out s 32 (keyEnd c (memBytes M p n) pos) f) M 0 f := by
  refine WP.zero fun hz => ?_
  have esp : aluEval .add (f sp) 0xFFFFFFE0 = s := by
    rw [hsp, ev_add, BitVec.add_assoc, show BitVec.ofNat 32 32 + (0xFFFFFFE0 : Word) = 0 from by decide]
    exact BitVec.add_zero s
  have hlen : (memBytes M p n).length = n := memBytes_length M p n
  refine WP.aluImm ke_at_0 ?_; wn
  rw [esp]
  refine WP.sw ke_at_2 (by rsimp; exact aligned_add hal (k := 28) (by decide))
    (by rsimp; exact hSc.sub (c := 28) (by decide)) ?_; wn
  refine WP.sw ke_at_4 (by rsimp; exact aligned_add hal (k := 24) (by decide))
    (by rsimp; exact hSc.sub (c := 24) (by decide)) ?_; wn
  refine WP.sw ke_at_6 (by rsimp; exact aligned_add hal (k := 20) (by decide))
    (by rsimp; exact hSc.sub (c := 20) (by decide)) ?_; wn
  refine WP.sw ke_at_8 (by rsimp; exact aligned_add hal (k := 16) (by decide))
    (by rsimp; exact hSc.sub (c := 16) (by decide)) ?_; wn
  refine WP.sw ke_at_a (by rsimp; exact aligned_add hal (k := 12) (by decide))
    (by rsimp; exact hSc.sub (c := 12) (by decide)) ?_; wn
  change WP jsonKeyEndCode base _ (keM1 M s f) 0xC _
  obtain ⟨hO1, hv⟩ := ke_pro M s f
  have hsp0 : f sp = s + BitVec.ofNat 32 32 := hsp
  refine WP.alu ke_at_c ?_; wn
  refine WP.branch ke_at_e (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    rw [h3, h2, br_bgeu hpos hn] at e
    have hle : (memBytes M p n).length ≤ pos := by have := not_dec_true e; omega
    simp only [keyEnd, hle, ↓reduceIte]
    exact ke_e7e (by rsimp; simp only [ev0, ev_mv hz, h0]) (by rsimp) hO1 (Slots.refl _ _ _) hv hsp0 hret hal hz
      (by keepz hz) hso hsc
  rsimp at e
  rw [h3, h2, br_bgeu hpos hn] at e
  have hlt : pos < n := not_dec_false e
  have hle : ¬(memBytes M p n).length ≤ pos := by omega
  refine WP.alu ke_at_12 ?_; wn
  refine WP.alu ke_at_14 ?_; wn
  refine WP.lbu ke_at_18 ?_; wn
  refine WP.aluImm ke_at_1c ?_; wn
  rw [h1, h3, ev_add p, add_lit_zero, hO1.byte hSp hlt]
  refine WP.branch ke_at_20 (fun e => ?_) (fun e => ?_) <;> wn
  · rsimp at e
    rw [ke_q] at e
    have hne : (memBytes M p n).getD pos 0 ≠ 34 := by rw [memBytes_getD hlt]; exact nbeq_true e
    simp only [keyEnd, hle, hne, ne_eq, not_false_eq_true, ↓reduceIte]
    exact ke_e7e (by rsimp; simp only [ev0, ev_mv hz, h0]) (by rsimp) hO1 (Slots.refl _ _ _) hv hsp0 hret hal hz
      (by keepz hz) hso hsc
  rsimp at e
  rw [ke_q] at e
  have h34 : (memBytes M p n).getD pos 0 = 34 := by rw [memBytes_getD hlt]; exact nbeq_false e
  simp only [keyEnd, hle, h34, ne_eq, not_true_eq_false, ↓reduceIte]
  refine WP.alu ke_at_22 ?_; wn
  refine WP.alu ke_at_24 ?_; wn
  refine WP.aluImm ke_at_26 ?_; wn
  refine WP.alu ke_at_28 ?_; wn
  refine WP.callStringEnd (tb := base + 0xFFFFFFA6) (out := s + 4) (p := p) (n := n) (pos := pos) (c := c)
    ke_at_2a ke_at_2e (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    (even_at base hb 0xFFFFFFA6 (by decide)) (by decide) (hO1.codeIn hcs hSs) (by rsimp; rfl)
    (by rsimp; simp only [ev0, ev_mv hz, h1]) (by rsimp; exact h2) (by rsimp; exact h3) (by rsimp; exact h4)
    hn hpos (aligned_add hal (k := 4) (by decide)) (hSs.sub (c := 4) (by decide))
    (hSc.sub (c := 4) (by decide)) fun m2 hU => ?_
  rw [hO1.bytes hSp] at hU
  generalize m2.mem = M2 at hU
  have hO2 : Out M M2 s 32 := hO1.trans (hU.out.widen (d := 4) (by decide))
  have hS2 : Slots keCs s (keM1 M s f) M2 :=
    (Slots.refl _ _ _).out hU.out (slots_sep s (by decide) (by decide))
  refine WP.lbu ke_at_32 ?_; wn
  rcases hse : stringEnd c (memBytes M p n) pos with _ | e
  · rw [hse] at hU
    obtain ⟨_, t1, t2⟩ := hU
    have t2' : M2 (s + 5) = 0x20 := by
      rw [show s + 5 = s + 4 + 1 by rw [BitVec.add_assoc]; rfl]; exact t2
    refine WP.branch ke_at_36 (fun e => ?_) (fun _ => ?_) <;> wn
    · rsimp at e; rw [t1] at e; exact absurd e (by decide)
    refine WP.lbu ke_at_38 ?_; wn
    refine WP.jal ke_at_3c (by decide) ?_; wn
    exact ke_err20 (by rsimp; simp only [ev0, ev_mv hz, h0]) (by rsimp) (by rsimp; rw [t2']; rfl) hO2 hS2 hv hsp0 hret
      hal hz (by keepz hz) hso hsc
  rw [hse] at hU
  obtain ⟨_, t1, t2⟩ := hU
  have hle' : e ≤ n := hlen ▸ stringEnd_le hse
  have t2' : memLoad32 M2 (s + 8) = BitVec.ofNat 32 e := by
    rw [show s + 8 = s + 4 + 4 by rw [BitVec.add_assoc]; rfl]; exact t2
  refine WP.branch ke_at_36 (fun _ => ?_) (fun e => by rsimp at e; rw [t1] at e; exact absurd e (by decide))
  wn
  refine WP.lw ke_at_3e (by rsimp; exact aligned_add hal (k := 8) (by decide)) ?_; wn
  rw [t2']
  have hq : wsIn c (memBytes M p n) e < 2 ^ 32 := by
    have := wsIn_le c (memBytes M p n) e; rw [hlen] at this; omega
  rw [hlen]
  refine WP.branch ke_at_40 (fun e3 => ?_) (fun e3 => ?_) <;> wn
  · rsimp at e3
    simp only [ev0, ev_mv hz, h4, br_mode] at e3
    subst e3
    exact ke_tail (q := e) (by rsimp; simp only [ev0, ev_mv hz, h0]) (by rsimp) (by rsimp; simp only [ev0, ev_mv hz, h1])
      (by rsimp; simp only [ev0, ev_mv hz, h2]) (by rsimp; simp only [ev0, ev_mv hz, h4]) (by rsimp) hn (by omega) hO2 hS2 hv hsp0
      hret hal halo hz (by keepz hz) hso hsc hb hcw hSw hSp
  rsimp at e3
  simp only [ev0, ev_mv hz, h4, br_mode] at e3
  subst e3
  refine WP.alu ke_at_44 ?_; wn
  refine WP.alu ke_at_46 ?_; wn
  refine WP.callSkipWs (tb := base + 0x322) (p := p) (n := n) (q := e) ke_at_48 ke_at_4c
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hb 0x322 (by decide)) (by decide)
    (hO2.codeIn hcw hSw) (by rsimp; simp only [ev0, ev_mv hz, h1]) (by rsimp; simp only [ev0, ev_mv hz, h2])
    (by rsimp) hn (by omega) fun m3 r0 => ?_
  rw [hO2.bytes hSp] at r0
  refine WP.alu ke_at_50 ?_; wn
  exact ke_tail (q := skipWs (memBytes M p n) e) (by rsimp; simp only [ev0, ev_mv hz, h0]) (by rsimp)
    (by rsimp; simp only [ev0, ev_mv hz, h1]) (by rsimp; simp only [ev0, ev_mv hz, h2]) (by rsimp; simp only [ev0, ev_mv hz, h4])
    (by rsimp; simp only [ev0, ev_mv hz, r0]) hn hq hO2 hS2 hv hsp0 hret hal halo hz (by keepz hz) hso hsc hb hcw hSw hSp

end

/-- `key_end(doc, pos, mode)` with `doc` the `n` bytes at `p`, `pos` in
`a3`, and `mode` in `a4`: stores `keyEnd` of them at `out` as a
`Result<usize, TufError>`, changes no memory outside `out` and the 32
bytes below `sp`, and keeps every register outside `jClob`. -/
theorem jsonKeyEnd_correct (m : Machine) {base retAddr out s p : Word} {n pos : Nat} {c : Bool}
    (hb : base.toNat % 2 = 0) (hc : CodeIn m.mem base jsonKeyEndCode)
    (hcs : CodeIn m.mem (base + 0xFFFFFFA6) jsonStringEndCode) (hcw : CodeIn m.mem (base + 0x322) jsonSkipWsCode)
    (hpc : m.pc = base) (ha0 : reg m a0 = out) (ha1 : reg m a1 = p) (ha2 : reg m a2 = BitVec.ofNat 32 n)
    (ha3 : reg m a3 = BitVec.ofNat 32 pos) (ha4 : reg m a4 = modeW c) (hsp : reg m sp = s + BitVec.ofNat 32 32)
    (hn : n < 2 ^ 32) (hpos : pos < 2 ^ 32) (hal : s.toNat % 4 = 0) (halo : out.toNat % 4 = 0)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hSc : Sep s 32 base jsonKeyEndCode.length)
    (hSs : Sep s 32 (base + 0xFFFFFFA6) jsonStringEndCode.length)
    (hSw : Sep s 32 (base + 0x322) jsonSkipWsCode.length) (hSp : Sep s 32 p n) (hso : Sep out 8 s 32)
    (hsc : Sep out 8 base jsonKeyEndCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      UsizeResF m.mem m'.mem out s 32 (keyEnd c (memBytes m.mem p n) pos) ∧
      ∀ r, r ∉ jClob → reg m' r = reg m r := by
  obtain ⟨m', st, hpc', hR, hfr⟩ := WP.run (ke_wp ha0 ha1 ha2 ha3 ha4 hsp hn hpos (by rw [hra]; exact hret) hal
    halo hb hcs hcw hSc hSs hSw hSp hso hsc) hb hc hpc
  exact ⟨m', st, hpc'.trans hra, hR, hfr⟩

end C3.RV32
