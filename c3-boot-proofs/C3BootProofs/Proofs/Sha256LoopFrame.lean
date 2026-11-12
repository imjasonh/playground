import C3BootProofs.Proofs.Sha256LoopLoad

/-!
# `compress256`, compact backend: the frame blocks

The straight-line blocks that move the hash state between `stp`, the frame,
and the round loop's registers: the setup after the prologue (0x1C..0x54),
the round setup (0xB6..0xD4), and the feed-forward after the rounds
(0x1EA..0x22C).
-/

namespace C3.RV32

open C3.Image

/-- A word load past a word store at another literal offset from the same
base. -/
theorem ls_lit {M : Word → BitVec 8} {b v c d : Word}
    (h : decide ((c.toNat + 4 ≤ d.toNat ∨ d.toNat + 4 ≤ c.toNat) ∧ c.toNat + 4 ≤ 2 ^ 32 ∧ d.toNat + 4 ≤ 2 ^ 32) = true) :
    memLoad32 (memStore32 M (b + c) v) (b + d) = memLoad32 M (b + d) := by
  simp only [decide_eq_true_eq] at h
  have := sep_offsets b (c := c.toNat) (n := 4) (d := d.toNat) (k := 4) h.1 h.2.1 h.2.2
  rw [ofNat_toNat_self, ofNat_toNat_self] at this
  exact memLoad32_store32_sep this

/-- A word load at the literal offset of the last word store. -/
theorem ls_same {M : Word → BitVec 8} {b v c d : Word} (h : c = d) :
    memLoad32 (memStore32 M (b + c) v) (b + d) = v := by
  subst h; exact memLoad32_store32_same _ _ _

/-- A word load past a word store into a range apart from the load's. -/
theorem ls_sep {M : Word → BitVec 8} {a b v c d : Word} {n k : Nat} (hs : Sep a n b k)
    (h : decide (c.toNat + 4 ≤ n ∧ d.toNat + 4 ≤ k) = true) :
    memLoad32 (memStore32 M (a + c) v) (b + d) = memLoad32 M (b + d) := by
  simp only [decide_eq_true_eq] at h
  have := (hs.sub (c := c.toNat) (l := 4) h.1).subR (c := d.toNat) (l := 4) h.2
  rw [ofNat_toNat_self, ofNat_toNat_self] at this
  exact memLoad32_store32_sep this

/-- A byte past a word store at a literal offset from a base whose range it
is apart from. -/
theorem st_get_sep {M : Word → BitVec 8} {a v c x : Word} {n : Nat} (hs : Sep a n x 1)
    (h : decide (c.toNat + 4 ≤ n) = true) : memStore32 M (a + c) v x = M x := by
  simp only [decide_eq_true_eq] at h
  have := hs.sub (c := c.toNat) (l := 4) h
  rw [ofNat_toNat_self] at this
  exact memStore32_get_sep this

theorem zero_lit_add (a : Word) : (0 : Word) + a = a := BitVec.zero_add a

theorem kcK_lit : (0x3FCC5000 : Word) + 0xFFFFFEBC = kcK := by decide

/-- The round setup, from 0xB6 to 0xD4: `e`, `a`, and `d` into the frame,
`b`, `c`, `f`, and `g` out of it, and the round constants' address. -/
def kcPre : List BInstr :=
  [.aluImm .add (8 : Fin 32) x0 0x0, .lui (7 : Fin 32) 0x3FCC5000, .aluImm .add (7 : Fin 32) (7 : Fin 32) 0xFFFFFEBC,
   .sw sp (26 : Fin 32) 0x10, .alu .add a0 x0 (26 : Fin 32), .sw sp (23 : Fin 32) 0x18, .alu .add a2 x0 (23 : Fin 32),
   .alu .add (26 : Fin 32) x0 (24 : Fin 32), .lw (17 : Fin 32) sp 0x1C, .lw (5 : Fin 32) sp 0x20,
   .sw sp (25 : Fin 32) 0x14, .lw a6 sp 0x24, .lw (29 : Fin 32) sp 0x28]

def kcPreKeep (q : Fin 32) : Bool := q.val ∉ [0, 5, 7, 8, 10, 12, 16, 17, 26, 29]

section
set_option maxRecDepth 20000
theorem kcPre_end : blockEnd sha256CompressCode 0xB6 kcPre = some 0xD4 := by decide
end

set_option maxRecDepth 20000 in
theorem kcPre_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock kcPre (M, f)).1 =
      memStore32 (memStore32 (memStore32 M (f sp + 0x10) (f 26)) (f sp + 0x18) (f 23)) (f sp + 0x14) (f 25) ∧
    (runBlock kcPre (M, f)).2 8 = 0 ∧ (runBlock kcPre (M, f)).2 7 = kcK ∧
    (runBlock kcPre (M, f)).2 a0 = f 26 ∧ (runBlock kcPre (M, f)).2 a2 = f 23 ∧
    (runBlock kcPre (M, f)).2 26 = f 24 ∧
    (runBlock kcPre (M, f)).2 17 = memLoad32 M (f sp + 0x1C) ∧
    (runBlock kcPre (M, f)).2 5 = memLoad32 M (f sp + 0x20) ∧
    (runBlock kcPre (M, f)).2 a6 = memLoad32 M (f sp + 0x24) ∧
    (runBlock kcPre (M, f)).2 29 = memLoad32 M (f sp + 0x28) ∧
    ∀ q, kcPreKeep q = true → (runBlock kcPre (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, kcPre, upd_app, ↓reduceIte]
  refine ⟨trivial, by rw [hz]; rfl, trivial, BitVec.zero_add _, BitVec.zero_add _, BitVec.zero_add _, ?_, ?_,
    ?_, ?_, fun q hq => ?_⟩
  · rw [ls_lit (by decide), ls_lit (by decide)]
  · rw [ls_lit (by decide), ls_lit (by decide)]
  · rw [ls_lit (by decide), ls_lit (by decide), ls_lit (by decide)]
  · rw [ls_lit (by decide), ls_lit (by decide), ls_lit (by decide)]
  by_cases h0 : q.val = 0
  · have : q = 0 := Fin.ext h0
    subst this; exact absurd hq (by decide)
  · simp only [h0, ite_false, pkeep_ne (r := 5) hq rfl, pkeep_ne (r := 7) hq rfl, pkeep_ne (r := 8) hq rfl,
      pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a2) hq rfl, pkeep_ne (r := a6) hq rfl,
      pkeep_ne (r := 17) hq rfl, pkeep_ne (r := 26) hq rfl, pkeep_ne (r := 29) hq rfl]

/-- The feed-forward, from 0x1EA to 0x22C: the working variables plus the
state, into the state and into the frame, and the next block's address. -/
def kcFinal : List BInstr :=
  [.lw (23 : Fin 32) sp 0x18, .alu .add (23 : Fin 32) (23 : Fin 32) (30 : Fin 32), .lw a0 sp 0x28,
   .alu .add a0 a0 (29 : Fin 32), .lw a1 sp 0x24, .alu .add a1 a1 a6, .lw a2 sp 0x14,
   .alu .add (25 : Fin 32) (25 : Fin 32) a2, .sw (18 : Fin 32) (23 : Fin 32) 0x0, .sw sp a0 0x28,
   .alu .add a3 x0 (18 : Fin 32), .sw a3 a0 0x4, .sw sp a1 0x24, .sw a3 a1 0x8, .sw (18 : Fin 32) (25 : Fin 32) 0xC,
   .lw a0 sp 0x10, .alu .add a0 a0 (6 : Fin 32), .lw a1 sp 0x20, .alu .add a1 a1 (5 : Fin 32), .lw a2 sp 0x1C,
   .alu .add a2 a2 (17 : Fin 32), .alu .add (24 : Fin 32) (24 : Fin 32) (26 : Fin 32), .alu .add (26 : Fin 32) x0 a0,
   .sw a3 a0 0x10, .sw sp a1 0x20, .sw a3 a1 0x14, .sw sp a2 0x1C, .sw a3 a2 0x18,
   .sw (18 : Fin 32) (24 : Fin 32) 0x1C, .lw (9 : Fin 32) sp 0xC]

def kcFinalKeep (q : Fin 32) : Bool := q.val ∉ [0, 9, 10, 11, 12, 13, 23, 24, 25, 26]

section
set_option maxRecDepth 20000
theorem kcFinal_end : blockEnd sha256CompressCode 0x1EA kcFinal = some 0x22C := by decide
end

/-- Memory after the feed-forward stores `A` to `H` into the state at `stp`
and `B`, `C`, `Fv`, and `G` into the frame at `F`. -/
def kcFinalMem (M : Word → BitVec 8) (F stp A B C D E Fv G H : Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32
    (memStore32 (memStore32 (memStore32 M (stp + 0) A) (F + 0x28) B) (stp + 0x4) B) (F + 0x24) C) (stp + 0x8) C)
    (stp + 0xC) D) (stp + 0x10) E) (F + 0x20) Fv) (stp + 0x14) Fv) (F + 0x1C) G) (stp + 0x18) G) (stp + 0x1C) H

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem kcFinal_run {M : Word → BitVec 8} {f : Fin 32 → Word} {F stp : Word} (hsp : f sp = F)
    (h18 : f 18 = stp) (hS : Sep stp 32 F 0xE0) :
    (runBlock kcFinal (M, f)).1 = kcFinalMem M F stp (memLoad32 M (F + 0x18) + f 30)
      (memLoad32 M (F + 0x28) + f 29) (memLoad32 M (F + 0x24) + f a6) (f 25 + memLoad32 M (F + 0x14))
      (memLoad32 M (F + 0x10) + f 6) (memLoad32 M (F + 0x20) + f 5) (memLoad32 M (F + 0x1C) + f 17)
      (f 24 + f 26) ∧
    (runBlock kcFinal (M, f)).2 23 = memLoad32 M (F + 0x18) + f 30 ∧
    (runBlock kcFinal (M, f)).2 25 = f 25 + memLoad32 M (F + 0x14) ∧
    (runBlock kcFinal (M, f)).2 26 = memLoad32 M (F + 0x10) + f 6 ∧
    (runBlock kcFinal (M, f)).2 24 = f 24 + f 26 ∧
    (runBlock kcFinal (M, f)).2 9 = memLoad32 M (F + 0xC) ∧
    ∀ q, kcFinalKeep q = true → (runBlock kcFinal (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, kcFinal, upd_app, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  rotate_left 6
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; exact absurd hq (by decide)
    · simp only [h0, ite_false, pkeep_ne (r := 9) hq rfl, pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a1) hq rfl,
        pkeep_ne (r := a2) hq rfl, pkeep_ne (r := a3) hq rfl, pkeep_ne (r := 23) hq rfl,
        pkeep_ne (r := 24) hq rfl, pkeep_ne (r := 25) hq rfl, pkeep_ne (r := 26) hq rfl]
  all_goals simp only [hsp, h18, ev_add, zero_lit_add]
  all_goals simp (disch := decide) only [ls_lit, ls_sep hS]
  all_goals rfl

/-- After the prologue's register saves, from 0x1C to 0x54: the state's
words into `s7`, `s9`, `s10`, `s8` and the frame, the end of the blocks at
`F + 8`, and the loop's constant registers. -/
def kcSetup : List BInstr :=
  [.alu .add (9 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .aluImm .sll a2 a2 0x6, .lw (23 : Fin 32) a0 0x0,
   .lw a0 a0 0x4, .sw sp a0 0x28, .alu .add a3 x0 (18 : Fin 32), .lw a0 a3 0x8, .sw sp a0 0x24,
   .lw (25 : Fin 32) (18 : Fin 32) 0xC, .lw (26 : Fin 32) (18 : Fin 32) 0x10, .lw a0 a3 0x14, .sw sp a0 0x20,
   .lw a0 a3 0x18, .sw sp a0 0x1C, .lw (24 : Fin 32) (18 : Fin 32) 0x1C, .alu .add a2 a2 a1, .sw sp a2 0x8,
   .aluImm .add (27 : Fin 32) sp 0x6C, .aluImm .add (19 : Fin 32) x0 0x10, .aluImm .add (20 : Fin 32) sp 0x2C,
   .aluImm .add (21 : Fin 32) x0 0x3]

def kcSetupKeep (q : Fin 32) : Bool := q.val ∉ [0, 9, 10, 12, 13, 18, 19, 20, 21, 23, 24, 25, 26, 27]

section
set_option maxRecDepth 20000
theorem kcSetup_end : blockEnd sha256CompressCode 0x1C kcSetup = some 0x54 := by decide
end

/-- Memory after the setup stores `b`, `c`, `f`, `g`, and the end of the
blocks into the frame. -/
def kcSetupMem (M : Word → BitVec 8) (F stp e : Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (F + 0x28) (memLoad32 M (stp + 0x4)))
    (F + 0x24) (memLoad32 M (stp + 0x8))) (F + 0x20) (memLoad32 M (stp + 0x14))) (F + 0x1C)
    (memLoad32 M (stp + 0x18))) (F + 0x8) e

theorem ev_sll6 (x : Word) : aluEval .sll x 0x6 = x <<< 6 := rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem kcSetup_run {M : Word → BitVec 8} {f : Fin 32 → Word} {F stp : Word} (hz : f 0 = 0) (hsp : f sp = F)
    (ha0 : f a0 = stp) (hS : Sep F 0xE0 stp 32) :
    (runBlock kcSetup (M, f)).1 = kcSetupMem M F stp ((f a2 <<< 6) + f a1) ∧
    (runBlock kcSetup (M, f)).2 9 = f a1 ∧ (runBlock kcSetup (M, f)).2 18 = stp ∧
    (runBlock kcSetup (M, f)).2 23 = memLoad32 M (stp + 0) ∧
    (runBlock kcSetup (M, f)).2 25 = memLoad32 M (stp + 0xC) ∧
    (runBlock kcSetup (M, f)).2 26 = memLoad32 M (stp + 0x10) ∧
    (runBlock kcSetup (M, f)).2 24 = memLoad32 M (stp + 0x1C) ∧
    (runBlock kcSetup (M, f)).2 27 = F + 0x6C ∧ (runBlock kcSetup (M, f)).2 19 = 0x10 ∧
    (runBlock kcSetup (M, f)).2 20 = F + 0x2C ∧ (runBlock kcSetup (M, f)).2 21 = 3 ∧
    ∀ q, kcSetupKeep q = true → (runBlock kcSetup (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, kcSetup, upd_app, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  rotate_left 11
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; exact absurd hq (by decide)
    · simp only [h0, ite_false, pkeep_ne (r := 9) hq rfl, pkeep_ne (r := a0) hq rfl, pkeep_ne (r := a2) hq rfl,
        pkeep_ne (r := a3) hq rfl, pkeep_ne (r := 18) hq rfl, pkeep_ne (r := 19) hq rfl,
        pkeep_ne (r := 20) hq rfl, pkeep_ne (r := 21) hq rfl, pkeep_ne (r := 23) hq rfl,
        pkeep_ne (r := 24) hq rfl, pkeep_ne (r := 25) hq rfl, pkeep_ne (r := 26) hq rfl, pkeep_ne (r := 27) hq rfl]
  all_goals simp only [hsp, ha0, hz, ev_add, ev_sll6, zero_lit_add]
  all_goals simp (disch := decide) only [ls_sep hS]
  all_goals rfl

theorem fr_al {F : Word} (hF : F.toNat % 4 = 0) {c : Word} (h : decide (c.toNat % 4 = 0) = true) :
    (F + c).toNat % 4 = 0 := by
  simp only [decide_eq_true_eq] at h
  have := aligned_add hF (k := c.toNat) h
  rwa [ofNat_toNat_self] at this

theorem frm_sep {F b : Word} {n k : Nat} (hs : Sep F n b k) {c : Word} (h : decide (c.toNat + 4 ≤ n) = true) :
    Sep (F + c) 4 b k := by
  simp only [decide_eq_true_eq] at h
  have := hs.sub (c := c.toNat) (l := 4) h
  rwa [ofNat_toNat_self] at this

set_option maxRecDepth 20000 in
theorem kcPre_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {F base : Word} {len : Nat} (hsp : f sp = F)
    (hF : F.toNat % 4 = 0) (hs : Sep F 0xE0 base len) : BlockOk base len kcPre (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, kcPre, upd_app, ↓reduceIte, and_true, true_and]
  simp only [hsp]
  simp (disch := decide) only [fr_al hF, frm_sep hs, and_self]

set_option maxRecDepth 20000 in
theorem kcFinal_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {F stp base : Word} {len : Nat} (hsp : f sp = F)
    (h18 : f 18 = stp) (hF : F.toNat % 4 = 0) (hst : stp.toNat % 4 = 0) (hs : Sep F 0xE0 base len)
    (hs' : Sep stp 32 base len) : BlockOk base len kcFinal (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, kcFinal, upd_app, ↓reduceIte, and_true, true_and]
  simp only [hsp, h18, ev_add, zero_lit_add]
  simp (disch := decide) only [fr_al hF, fr_al hst, frm_sep hs, frm_sep hs', and_self]

set_option maxRecDepth 20000 in
theorem kcSetup_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {F stp base : Word} {len : Nat} (hsp : f sp = F) (ha0 : f a0 = stp) (hF : F.toNat % 4 = 0) (hst : stp.toNat % 4 = 0) (hs : Sep F 0xE0 base len) :
    BlockOk base len kcSetup (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, kcSetup, upd_app, ↓reduceIte, and_true, true_and]
  simp only [hsp, ha0, ev_add, zero_lit_add]
  simp (disch := decide) only [fr_al hF, fr_al hst, frm_sep hs, and_self]

/-- The `memcpy` arguments, from 0xA0 to 0xAE, with the next block's address
saved at `F + 0xC`. -/
def kcCopy : List BInstr :=
  [.sw sp (22 : Fin 32) 0xC, .aluImm .add a0 sp 0x2C, .aluImm .add a1 sp 0x6C, .aluImm .add a2 x0 0x40,
   .aluImm .add (22 : Fin 32) sp 0x2C]

def kcBlkA : List BInstr := [.aluImm .add (8 : Fin 32) x0 0x0, .aluImm .add (22 : Fin 32) (9 : Fin 32) 0x40]

section
set_option maxRecDepth 20000
theorem kcCopy_end : blockEnd sha256CompressCode 0xA0 kcCopy = some 0xAE := by decide
theorem kcBlkA_end : blockEnd sha256CompressCode 0x5A kcBlkA = some 0x60 := by decide
end

theorem kcCopy_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {F base : Word} {len : Nat} (hsp : f sp = F)
    (hF : F.toNat % 4 = 0) (hs : Sep F 0xE0 base len) : BlockOk base len kcCopy (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, kcCopy, and_true]
  simp only [hsp]
  simp (disch := decide) only [fr_al hF, frm_sep hs, and_self]

end C3.RV32
