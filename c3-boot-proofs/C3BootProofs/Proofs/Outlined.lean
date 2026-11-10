import C3BootProofs.Proofs.ReaderU32

/-!
# Machine-outlined register saves and restores

LLVM's machine outliner moves prologue and epilogue sequences that many
functions share into functions of their own, which a caller enters with
`auipc t0, …; jalr t0, …(t0)` and which return with `jr t0`. They aren't
ABI calls: they read the caller's `sp` and leave `ra` alone.

`OUTLINED_FUNCTION_83` stores `ra` and `s0` through `s3` at offsets 0x1C
down to 0x0C of the caller's frame, and `OUTLINED_FUNCTION_57` loads `ra`
and `s0` through `s4` from offsets 0x1C down to 0x08. `St.callSave83` and
`St.callRestore57` run a caller's two-instruction entry and the whole helper as
one step of the caller's proof.
-/

namespace C3.RV32

open C3.Image

abbrev t0 : Fin 32 := 5
abbrev s2 : Fin 32 := 18
abbrev s3 : Fin 32 := 19
abbrev s4 : Fin 32 := 20

/-- Memory after `OUTLINED_FUNCTION_83` saves `f`'s `ra` and `s0` through
`s3` in the frame at `G`. -/
def save83 (M : Word → BitVec 8) (G : Word) (f : Fin 32 → Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M (G + 0x1C) (f ra)) (G + 0x18) (f s0))
    (G + 0x14) (f s1)) (G + 0x10) (f s2)) (G + 0x0C) (f s3)

/-- Registers after `OUTLINED_FUNCTION_57` loads `ra` and `s0` through
`s4` from the frame at `G` in `M`. -/
def restore57 (M : Word → BitVec 8) (G : Word) (f : Fin 32 → Word) : Fin 32 → Word :=
  upd (upd (upd (upd (upd (upd f ra (memLoad32 M (G + 0x1C))) s0 (memLoad32 M (G + 0x18)))
    s1 (memLoad32 M (G + 0x14))) s2 (memLoad32 M (G + 0x10))) s3 (memLoad32 M (G + 0x0C)))
    s4 (memLoad32 M (G + 8))

theorem upd_ne {f : Fin 32 → Word} {rd r : Fin 32} {v : Word} (h0 : r.val ≠ 0) (h : r ≠ rd) :
    upd f rd v r = f r := by simp [upd, h0, h]

theorem ofNat_add_ofNat (c k : Nat) :
    BitVec.ofNat 32 c + BitVec.ofNat 32 k = BitVec.ofNat 32 (c + k) :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    exact (Nat.add_mod _ _ _).symm)

theorem o83_at_00 : fetchRel outlined83Code 0x00 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem o83_at_02 : fetchRel outlined83Code 0x02 = some (.store .sw sp s0 0x18, 2) := by decide
theorem o83_at_04 : fetchRel outlined83Code 0x04 = some (.store .sw sp s1 0x14, 2) := by decide
theorem o83_at_06 : fetchRel outlined83Code 0x06 = some (.store .sw sp s2 0x10, 2) := by decide
theorem o83_at_08 : fetchRel outlined83Code 0x08 = some (.store .sw sp s3 0x0C, 2) := by decide
theorem o83_at_0a : fetchRel outlined83Code 0x0A = some (.jalr x0 t0 0, 2) := by decide

theorem o57_at_00 : fetchRel outlined57Code 0x00 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem o57_at_02 : fetchRel outlined57Code 0x02 = some (.load .lw s0 sp 0x18, 2) := by decide
theorem o57_at_04 : fetchRel outlined57Code 0x04 = some (.load .lw s1 sp 0x14, 2) := by decide
theorem o57_at_06 : fetchRel outlined57Code 0x06 = some (.load .lw s2 sp 0x10, 2) := by decide
theorem o57_at_08 : fetchRel outlined57Code 0x08 = some (.load .lw s3 sp 0x0C, 2) := by decide
theorem o57_at_0a : fetchRel outlined57Code 0x0A = some (.load .lw s4 sp 8, 2) := by decide
theorem o57_at_0c : fetchRel outlined57Code 0x0C = some (.jalr x0 t0 0, 2) := by decide

/-- **`OUTLINED_FUNCTION_83` is correct.** With its bytes at `b` apart from
the 32-byte frame at an aligned `sp`, it returns to `t0` (with bit 0
cleared, as `jalr` does) with every register unchanged and memory
`save83`. -/
theorem outlined83_correct {M : Word → BitVec 8} {b : Word} {m : Machine} {g : Fin 32 → Word}
    (s : St M b m 0 g) (hc : CodeIn M b outlined83Code) (hal : (g sp).toNat % 4 = 0)
    (hS : Sep (g sp) 32 b outlined83Code.length) :
    ∃ m', Steps m m' ∧ m'.pc = g t0 &&& ~~~1 ∧ m'.mem = save83 M (g sp) g ∧ ∀ r, reg m' r = g r := by
  have sl : ∀ c, c + 4 ≤ 32 → Sep (g sp + BitVec.ofNat 32 c) 4 b outlined83Code.length :=
    fun c h => hS.sub (c := c) (l := 4) h
  obtain ⟨m1, e1, t1⟩ := s.sw hc o83_at_00 (off' := 0x02) (by decide) (aligned_add hal (k := 0x1C) (by decide))
  have c1 := hc.store32 (v := g ra) (show Sep (g sp + 0x1C) 4 _ _ from sl 0x1C (by omega))
  obtain ⟨m2, e2, t2⟩ := t1.sw c1 o83_at_02 (off' := 0x04) (by decide) (aligned_add hal (k := 0x18) (by decide))
  have c2 := c1.store32 (v := g s0) (show Sep (g sp + 0x18) 4 _ _ from sl 0x18 (by omega))
  obtain ⟨m3, e3, t3⟩ := t2.sw c2 o83_at_04 (off' := 0x06) (by decide) (aligned_add hal (k := 0x14) (by decide))
  have c3 := c2.store32 (v := g s1) (show Sep (g sp + 0x14) 4 _ _ from sl 0x14 (by omega))
  obtain ⟨m4, e4, t4⟩ := t3.sw c3 o83_at_06 (off' := 0x08) (by decide) (aligned_add hal (k := 0x10) (by decide))
  have c4 := c3.store32 (v := g s2) (show Sep (g sp + 0x10) 4 _ _ from sl 0x10 (by omega))
  obtain ⟨m5, e5, t5⟩ := t4.sw c4 o83_at_08 (off' := 0x0A) (by decide) (aligned_add hal (k := 0x0C) (by decide))
  have c5 := c4.store32 (v := g s3) (show Sep (g sp + 0x0C) 4 _ _ from sl 0x0C (by omega))
  obtain ⟨m6, e6, pc6, mem6, regs6⟩ := t5.jalr c5 o83_at_0a
  exact ⟨m6, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.single e6))))),
    by rw [pc6, add_lit_zero], mem6, regs6⟩

/-- **`OUTLINED_FUNCTION_57` is correct.** With its bytes at `b` and an
aligned `sp`, it returns to `t0` (with bit 0 cleared) with memory unchanged
and registers `restore57`. -/
theorem outlined57_correct {M : Word → BitVec 8} {b : Word} {m : Machine} {g : Fin 32 → Word}
    (s : St M b m 0 g) (hc : CodeIn M b outlined57Code) (hal : (g sp).toNat % 4 = 0) :
    ∃ m', Steps m m' ∧ m'.pc = g t0 &&& ~~~1 ∧ m'.mem = M ∧
      ∀ r, reg m' r = restore57 M (g sp) g r := by
  obtain ⟨m1, e1, t1⟩ := s.lw hc o57_at_00 (off' := 0x02) (by decide) (aligned_add hal (k := 0x1C) (by decide))
  obtain ⟨m2, e2, t2⟩ := t1.lw hc o57_at_02 (off' := 0x04) (by decide)
    (by rw [upd_ne (by decide) (by decide)]; exact aligned_add hal (k := 0x18) (by decide))
  simp (disch := decide) only [upd_ne] at t2
  obtain ⟨m3, e3, t3⟩ := t2.lw hc o57_at_04 (off' := 0x06) (by decide)
    (by simp (disch := decide) only [upd_ne]; exact aligned_add hal (k := 0x14) (by decide))
  simp (disch := decide) only [upd_ne] at t3
  obtain ⟨m4, e4, t4⟩ := t3.lw hc o57_at_06 (off' := 0x08) (by decide)
    (by simp (disch := decide) only [upd_ne]; exact aligned_add hal (k := 0x10) (by decide))
  simp (disch := decide) only [upd_ne] at t4
  obtain ⟨m5, e5, t5⟩ := t4.lw hc o57_at_08 (off' := 0x0A) (by decide)
    (by simp (disch := decide) only [upd_ne]; exact aligned_add hal (k := 0x0C) (by decide))
  simp (disch := decide) only [upd_ne] at t5
  obtain ⟨m6, e6, t6⟩ := t5.lw hc o57_at_0a (off' := 0x0C) (by decide)
    (by simp (disch := decide) only [upd_ne]; exact aligned_add hal (k := 8) (by decide))
  simp (disch := decide) only [upd_ne] at t6
  obtain ⟨m7, e7, pc7, mem7, regs7⟩ := t6.jalr hc o57_at_0c
  refine ⟨m7, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.single e7)))))),
    ?_, mem7, fun r => by rw [regs7]; rfl⟩
  rw [pc7, add_lit_zero]; simp (disch := decide) only [upd_ne]

/-- A caller's `auipc t0, imm; jalr t0, o(t0)` into `OUTLINED_FUNCTION_83`,
and the helper, run from offset `off` to `off + 8` of the caller: `t0` holds
the link and memory is `save83`. -/
theorem St.callSave83 {M : Word → BitVec 8} {base b : Word} {code : List Nat} {m : Machine} {off : Nat}
    {f : Fin 32 → Word} (s : St M base m off f) (hc : CodeIn M base code) {imm o : Word}
    (h1 : fetchRel code off = some (.auipc t0 imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr t0 t0 o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = b) (hbe : b.toNat % 2 = 0)
    (hl : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (h83 : CodeIn M b outlined83Code) (hal : (f sp).toNat % 4 = 0)
    (hS : Sep (f sp) 32 b outlined83Code.length) :
    ∃ m', Steps m m' ∧
      St (save83 M (f sp) f) base m' (off + 8) (upd f t0 (base + BitVec.ofNat 32 (off + 8))) := by
  obtain ⟨m1, e1, t1⟩ := s.auipc hc h1 (off' := off + 4) (ofNat_add_ofNat off 4)
  obtain ⟨m2, e2, pc2, mem2, regs2⟩ := t1.call hc h2
  have hL : base + BitVec.ofNat 32 (off + 4) + 4 = base + BitVec.ofNat 32 (off + 8) := by
    rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
  let g := upd f t0 (base + BitVec.ofNat 32 (off + 8))
  have hg : ∀ r, reg m2 r = g r := fun r => by
    rw [regs2, hL]
    by_cases hr : r.val = 0
    · simp [g, upd, hr]
    · by_cases ht : r = t0
      · subst ht; simp [g, upd]
      · simp [g, upd, hr, ht]
  have hp2 : m2.pc = b := by
    rw [pc2, show upd f t0 (base + BitVec.ofNat 32 off + imm) t0 = base + BitVec.ofNat 32 off + imm from
      by simp +decide [upd], hb]; exact even_clear _ hbe
  have hz := s.zero
  have gs : ∀ r, r ≠ t0 → g r = f r := fun r h => by
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [g, hz]
    · simp [g, upd, hr, h]
  have gsp : g sp = f sp := gs sp (by decide)
  have u : St M b m2 0 g := ⟨by rw [hp2]; simp, mem2, hg⟩
  obtain ⟨m3, e3, pc3, mem3, regs3⟩ := outlined83_correct u h83 (by rw [gsp]; exact hal)
    (by rw [gsp]; exact hS)
  refine ⟨m3, .cons e1 (.cons e2 e3), ?_, ?_, regs3⟩
  · rw [pc3]; simp +decide only [g, upd]; exact even_clear _ hl
  · rw [mem3, gsp]; unfold save83
    rw [gs ra (by decide), gs s0 (by decide), gs s1 (by decide), gs s2 (by decide), gs s3 (by decide)]

/-- A caller's `auipc t0, imm; jalr t0, o(t0)` into `OUTLINED_FUNCTION_57`,
and the helper, run from offset `off` to `off + 8` of the caller: `t0` holds
the link and `ra` and `s0` through `s4` hold the frame's saved values. -/
theorem St.callRestore57 {M : Word → BitVec 8} {base b : Word} {code : List Nat} {m : Machine} {off : Nat}
    {f : Fin 32 → Word} (s : St M base m off f) (hc : CodeIn M base code) {imm o : Word}
    (h1 : fetchRel code off = some (.auipc t0 imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr t0 t0 o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = b) (hbe : b.toNat % 2 = 0)
    (hl : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (h57 : CodeIn M b outlined57Code) (hal : (f sp).toNat % 4 = 0) :
    ∃ m', Steps m m' ∧
      St M base m' (off + 8) (restore57 M (f sp) (upd f t0 (base + BitVec.ofNat 32 (off + 8)))) := by
  obtain ⟨m1, e1, t1⟩ := s.auipc hc h1 (off' := off + 4) (ofNat_add_ofNat off 4)
  obtain ⟨m2, e2, pc2, mem2, regs2⟩ := t1.call hc h2
  have hL : base + BitVec.ofNat 32 (off + 4) + 4 = base + BitVec.ofNat 32 (off + 8) := by
    rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
  let g := upd f t0 (base + BitVec.ofNat 32 (off + 8))
  have hg : ∀ r, reg m2 r = g r := fun r => by
    rw [regs2, hL]
    by_cases hr : r.val = 0
    · simp [g, upd, hr]
    · by_cases ht : r = t0
      · subst ht; simp [g, upd]
      · simp [g, upd, hr, ht]
  have hp2 : m2.pc = b := by
    rw [pc2, show upd f t0 (base + BitVec.ofNat 32 off + imm) t0 = base + BitVec.ofNat 32 off + imm from
      by simp +decide [upd], hb]; exact even_clear _ hbe
  have gsp : g sp = f sp := by simp +decide [g, upd]
  have u : St M b m2 0 g := ⟨by rw [hp2]; simp, mem2, hg⟩
  obtain ⟨m3, e3, pc3, mem3, regs3⟩ := outlined57_correct u h57 (by rw [gsp]; exact hal)
  refine ⟨m3, .cons e1 (.cons e2 e3), ?_, mem3, fun r => by rw [regs3, gsp]⟩
  rw [pc3]; simp +decide only [g, upd]; exact even_clear _ hl

end C3.RV32
