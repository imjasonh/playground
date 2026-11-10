import C3BootProofs.Proofs.ReaderU32

/-!
# Machine-outlined register saves and restores

LLVM's machine outliner moves prologue and epilogue sequences that many
functions share into functions of their own, which a caller enters with
`auipc t0, …; jalr t0, …(t0)` and which return with `jr t0`. They aren't
ABI calls: they read the caller's `sp` and leave `ra` alone.

A save helper is a run of `sw r, o(sp)` and a restore helper a run of
`lw r, o(sp)`, each ending in `jr t0`. `SaveAt` and `RestoreAt` say that
code has that shape for a list of registers and offsets, which `decide`
checks against a helper's bytes. `save_run` and `restore_run` prove every
such helper by induction on the list, and `St.callSave` and `St.callRestore`
run a caller's two-instruction entry and the whole helper as one step of the
caller's proof. The machine outliner numbers its helpers differently on
each rebuild, so nothing here depends on a helper's name.
-/

namespace C3.RV32

open C3.Image

abbrev t0 : Fin 32 := 5
abbrev s2 : Fin 32 := 18
abbrev s3 : Fin 32 := 19
abbrev s4 : Fin 32 := 20

theorem upd_ne {f : Fin 32 → Word} {rd r : Fin 32} {v : Word} (h0 : r.val ≠ 0) (h : r ≠ rd) :
    upd f rd v r = f r := by simp [upd, h0, h]

theorem ofNat_add_ofNat (c k : Nat) :
    BitVec.ofNat 32 c + BitVec.ofNat 32 k = BitVec.ofNat 32 (c + k) :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    exact (Nat.add_mod _ _ _).symm)

/-- Memory after a save helper stores `f`'s registers at the offsets `ps`
from `G`, in order. -/
def saveMem (M : Word → BitVec 8) (G : Word) (f : Fin 32 → Word) :
    List (Fin 32 × Word) → Word → BitVec 8
  | [] => M
  | (r, o) :: ps => saveMem (memStore32 M (G + o) (f r)) G f ps

/-- Registers after a restore helper loads the offsets `ps` from `G` in `M`,
in order. -/
def restoreRegs (M : Word → BitVec 8) (G : Word) :
    (Fin 32 → Word) → List (Fin 32 × Word) → Fin 32 → Word
  | f, [] => f
  | f, (r, o) :: ps => restoreRegs M G (upd f r (memLoad32 M (G + o))) ps

/-- `code` from offset `off` stores each register of `ps` at its offset from
`sp`, then returns with `jr t0`. -/
def SaveAt (code : List Nat) : Nat → List (Fin 32 × Word) → Prop
  | off, [] => fetchRel code off = some (.jalr x0 t0 0, 2)
  | off, (r, o) :: ps => fetchRel code off = some (.store .sw sp r o, 2) ∧ SaveAt code (off + 2) ps

/-- `code` from offset `off` loads each register of `ps` from its offset
from `sp`, then returns with `jr t0`. -/
def RestoreAt (code : List Nat) : Nat → List (Fin 32 × Word) → Prop
  | off, [] => fetchRel code off = some (.jalr x0 t0 0, 2)
  | off, (r, o) :: ps => fetchRel code off = some (.load .lw r sp o, 2) ∧ RestoreAt code (off + 2) ps

theorem save_run {b : Word} {code : List Nat} {g : Fin 32 → Word} :
    ∀ (ps : List (Fin 32 × Word)) (M : Word → BitVec 8) (m : Machine) (off : Nat),
      St M b m off g → CodeIn M b code → SaveAt code off ps → off + 2 * ps.length + 2 < 2 ^ 32 →
      (∀ p ∈ ps, (g sp + p.2).toNat % 4 = 0 ∧ Sep (g sp + p.2) 4 b code.length) →
      ∃ m', Steps m m' ∧ m'.pc = g t0 &&& ~~~1 ∧ m'.mem = saveMem M (g sp) g ps ∧
        ∀ r, reg m' r = g r
  | [], M, m, off, s, hc, h, _, _ => by
    obtain ⟨m1, e1, pc1, mem1, regs1⟩ := s.jalr hc h
    exact ⟨m1, .single e1, by rw [pc1, add_lit_zero], mem1, regs1⟩
  | (r, o) :: ps, M, m, off, s, hc, ⟨h1, h2⟩, hlen, hp => by
    obtain ⟨hal, hS⟩ := hp (r, o) (List.mem_cons_self ..)
    obtain ⟨m1, e1, t1⟩ := s.sw hc h1 (off' := off + 2) (ofNat_add_ofNat off 2) hal
    obtain ⟨m2, c2, pc2, mem2, regs2⟩ := save_run ps _ m1 (off + 2) t1 (hc.store32 hS) h2
      (by simp only [List.length_cons] at hlen; omega)
      (fun p hm => hp p (List.mem_cons_of_mem _ hm))
    exact ⟨m2, .cons e1 c2, pc2, mem2, regs2⟩

theorem restoreRegs_sp (M : Word → BitVec 8) (G : Word) :
    ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)), (∀ p ∈ ps, p.1 ≠ sp) →
      restoreRegs M G f ps sp = f sp
  | f, [], _ => rfl
  | f, (r, o) :: ps, h => by
    simp only [restoreRegs]
    rw [restoreRegs_sp M G _ ps (fun p hm => h p (List.mem_cons_of_mem _ hm))]
    exact upd_ne (by decide) (fun e => h (r, o) (List.mem_cons_self ..) e.symm)

theorem restore_run {b : Word} {code : List Nat} {M : Word → BitVec 8} :
    ∀ (ps : List (Fin 32 × Word)) (g : Fin 32 → Word) (m : Machine) (off : Nat),
      St M b m off g → CodeIn M b code → RestoreAt code off ps → off + 2 * ps.length + 2 < 2 ^ 32 →
      (∀ p ∈ ps, p.1 ≠ sp ∧ p.1 ≠ t0 ∧ (g sp + p.2).toNat % 4 = 0) →
      ∃ m', Steps m m' ∧ m'.pc = g t0 &&& ~~~1 ∧ m'.mem = M ∧
        ∀ r, reg m' r = restoreRegs M (g sp) g ps r
  | [], g, m, off, s, hc, h, _, _ => by
    obtain ⟨m1, e1, pc1, mem1, regs1⟩ := s.jalr hc h
    exact ⟨m1, .single e1, by rw [pc1, add_lit_zero], mem1, regs1⟩
  | (r, o) :: ps, g, m, off, s, hc, ⟨h1, h2⟩, hlen, hp => by
    obtain ⟨hsp, ht0, hal⟩ := hp (r, o) (List.mem_cons_self ..)
    obtain ⟨m1, e1, t1⟩ := s.lw hc h1 (off' := off + 2) (ofNat_add_ofNat off 2) hal
    have usp : upd g r (memLoad32 M (g sp + o)) sp = g sp :=
      upd_ne (by decide) (fun e => hsp e.symm)
    have ut0 : upd g r (memLoad32 M (g sp + o)) t0 = g t0 :=
      upd_ne (by decide) (fun e => ht0 e.symm)
    obtain ⟨m2, c2, pc2, mem2, regs2⟩ := restore_run ps _ m1 (off + 2) t1 hc h2
      (by simp only [List.length_cons] at hlen; omega)
      (fun p hm => by rw [usp]; exact hp p (List.mem_cons_of_mem _ hm))
    refine ⟨m2, .cons e1 c2, by rw [pc2, ut0], mem2, fun x => by rw [regs2, usp]; rfl⟩

theorem saveMem_congr (M : Word → BitVec 8) (G : Word) {f g : Fin 32 → Word} :
    ∀ (ps : List (Fin 32 × Word)), (∀ p ∈ ps, g p.1 = f p.1) → saveMem M G g ps = saveMem M G f ps
  | [], _ => rfl
  | (r, o) :: ps, h => by
    simp only [saveMem]
    rw [h (r, o) (List.mem_cons_self ..)]
    exact saveMem_congr _ G ps (fun p hm => h p (List.mem_cons_of_mem _ hm))

/-- A caller's `auipc t0, imm; jalr t0, o(t0)` into a save helper at `b`,
and the helper, run from offset `off` to `off + 8` of the caller: `t0` holds
the link and memory is `saveMem`. -/
theorem St.callSave {M : Word → BitVec 8} {base b : Word} {code hcode : List Nat} {m : Machine}
    {off : Nat} {f : Fin 32 → Word} {ps : List (Fin 32 × Word)} (s : St M base m off f)
    (hc : CodeIn M base code) {imm o : Word}
    (h1 : fetchRel code off = some (.auipc t0 imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr t0 t0 o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = b) (hbe : b.toNat % 2 = 0)
    (hl : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hh : CodeIn M b hcode) (hs : SaveAt hcode 0 ps) (hlen : 2 * ps.length + 2 < 2 ^ 32)
    (hp : ∀ p ∈ ps, p.1 ≠ t0 ∧ (f sp + p.2).toNat % 4 = 0 ∧ Sep (f sp + p.2) 4 b hcode.length) :
    ∃ m', Steps m m' ∧
      St (saveMem M (f sp) f ps) base m' (off + 8) (upd f t0 (base + BitVec.ofNat 32 (off + 8))) := by
  obtain ⟨m1, e1, t1⟩ := s.auipc hc h1 (off' := off + 4) (ofNat_add_ofNat off 4)
  obtain ⟨m2, e2, pc2, mem2, regs2⟩ := t1.call hc h2
  have hL : base + BitVec.ofNat 32 (off + 4) + 4 = base + BitVec.ofNat 32 (off + 8) := by
    rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
  let g := upd f t0 (base + BitVec.ofNat 32 (off + 8))
  have hz := s.zero
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
  have gs : ∀ r, r ≠ t0 → g r = f r := fun r h => by
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [g, hz]
    · simp [g, upd, hr, h]
  have gsp : g sp = f sp := gs sp (by decide)
  have u : St M b m2 0 g := ⟨by rw [hp2]; simp, mem2, hg⟩
  obtain ⟨m3, e3, pc3, mem3, regs3⟩ := save_run ps M m2 0 u hh hs (by omega)
    (fun p hm => by rw [gsp]; exact ⟨(hp p hm).2.1, (hp p hm).2.2⟩)
  refine ⟨m3, .cons e1 (.cons e2 e3), ?_, ?_, regs3⟩
  · rw [pc3]; simp +decide only [g, upd]; exact even_clear _ hl
  · rw [mem3, gsp]; exact saveMem_congr M _ ps (fun p hm => gs p.1 (hp p hm).1)

/-- A caller's `auipc t0, imm; jalr t0, o(t0)` into a restore helper at
`b`, and the helper, run from offset `off` to `off + 8` of the caller: `t0`
holds the link and the registers are `restoreRegs`. -/
theorem St.callRestore {M : Word → BitVec 8} {base b : Word} {code hcode : List Nat} {m : Machine}
    {off : Nat} {f : Fin 32 → Word} {ps : List (Fin 32 × Word)} (s : St M base m off f)
    (hc : CodeIn M base code) {imm o : Word}
    (h1 : fetchRel code off = some (.auipc t0 imm, 4))
    (h2 : fetchRel code (off + 4) = some (.jalr t0 t0 o, 4))
    (hb : base + BitVec.ofNat 32 off + imm + o = b) (hbe : b.toNat % 2 = 0)
    (hl : (base + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hh : CodeIn M b hcode) (hs : RestoreAt hcode 0 ps) (hlen : 2 * ps.length + 2 < 2 ^ 32)
    (hp : ∀ p ∈ ps, p.1 ≠ sp ∧ p.1 ≠ t0 ∧ (f sp + p.2).toNat % 4 = 0) :
    ∃ m', Steps m m' ∧
      St M base m' (off + 8) (restoreRegs M (f sp) (upd f t0 (base + BitVec.ofNat 32 (off + 8))) ps) := by
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
  obtain ⟨m3, e3, pc3, mem3, regs3⟩ := restore_run ps g m2 0 u hh hs (by omega)
    (fun p hm => by rw [gsp]; exact hp p hm)
  have pc3' : m3.pc = base + BitVec.ofNat 32 (off + 8) := by
    rw [pc3]; simp +decide only [g, upd]; exact even_clear _ hl
  refine ⟨m3, .cons e1 (.cons e2 e3), pc3', ?_, fun r => by rw [regs3, gsp]⟩
  rw [mem3]

end C3.RV32
