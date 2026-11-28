import C3BootProofs.Model.RV32

/-!
# Running code on the model

Tools for proofs about machine code on the RV32 model. `CodeAt` says that
memory holds a function's bytes from some base address. `fetch_code` turns
a fetch at `base + off` into `fetchRel`, which decodes from the byte list,
so the kernel can compute each instruction. `Steps` chains executions.
Nothing here is trusted: the theorems built on it are about `step`.
-/

namespace C3.RV32

/-- Byte `i` of `code`. -/
def byteAt (code : List Nat) (i : Nat) : BitVec 8 := BitVec.ofNat 8 (code.getD i 0)

/-- Memory holds `code` from `base`. -/
def CodeAt (m : Machine) (base : Word) (code : List Nat) : Prop :=
  ∀ i, i < code.length → m.mem (base + BitVec.ofNat 32 i) = byteAt code i

/-- The instruction at offset `off` of `code`, decoded the way `fetch` does,
or `none` if it runs past the end. -/
def fetchRel (code : List Nat) (off : Nat) : Option (Instr × Word) :=
  if off + 2 ≤ code.length then
    let lo := (byteAt code (off + 1) ++ byteAt code off).toNat
    if lo % 4 == 3 then
      if off + 4 ≤ code.length then
        (decode32 (byteAt code (off + 3) ++ byteAt code (off + 2) ++ byteAt code (off + 1) ++
          byteAt code off).toNat).map (·, 4)
      else none
    else (decode16 lo).map (·, 2)
  else none

theorem add_ofNat_assoc (base : Word) (off k : Nat) :
    base + BitVec.ofNat 32 off + BitVec.ofNat 32 k = base + BitVec.ofNat 32 (off + k) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem mem_code {m : Machine} {base : Word} {code : List Nat} (h : CodeAt m base code)
    {off k : Nat} (hk : off + k < code.length) :
    m.mem (base + BitVec.ofNat 32 off + BitVec.ofNat 32 k) = byteAt code (off + k) := by
  rw [add_ofNat_assoc]
  exact h _ hk

theorem fetch_code {m : Machine} {base : Word} {code : List Nat} {off : Nat}
    (hcode : CodeAt m base code) (hpc : m.pc = base + BitVec.ofNat 32 off)
    {r : Instr × Word} (h : fetchRel code off = some r) : fetch m = some r := by
  unfold fetchRel at h
  dsimp only at h
  by_cases h2 : off + 2 ≤ code.length
  · rw [ite_eq_left h2] at h
    have b0 : m.mem m.pc = byteAt code off := by
      rw [hpc]; exact hcode off (by omega)
    have b1 : m.mem (m.pc + 1) = byteAt code (off + 1) := by
      rw [hpc]; exact mem_code hcode (k := 1) (by omega)
    unfold fetch
    simp only [load16, load32, load8, Arch.getPc, Arch.read8, b0, b1]
    by_cases h3 : ((byteAt code (off + 1) ++ byteAt code off).toNat % 4 == 3) = true
    · rw [ite_eq_left h3] at h ⊢
      by_cases h4 : off + 4 ≤ code.length
      · rw [ite_eq_left h4] at h
        have b2 : m.mem (m.pc + 2) = byteAt code (off + 2) := by
          rw [hpc]; exact mem_code hcode (k := 2) (by omega)
        have b3 : m.mem (m.pc + 3) = byteAt code (off + 3) := by
          rw [hpc]; exact mem_code hcode (k := 3) (by omega)
        simp only [b2, b3]
        exact h
      · rw [ite_eq_right h4] at h; contradiction
    · rw [ite_eq_right h3] at h ⊢
      exact h
  · rw [ite_eq_right h2] at h; contradiction

/-- `m` runs to `m'` in zero or more steps. -/
inductive Steps {σ : Type} [Arch σ] : σ → σ → Prop
  | refl (s : σ) : Steps s s
  | cons {s s' s'' : σ} : RV32.step s = some s' → Steps s' s'' → Steps s s''

theorem Steps.trans {σ : Type} [Arch σ] {a b c : σ} (h1 : Steps a b) (h2 : Steps b c) :
    Steps a c := by
  induction h1 with
  | refl => exact h2
  | cons hs _ ih => exact .cons hs (ih h2)

theorem Steps.single {σ : Type} [Arch σ] {a b : σ} (h : step a = some b) : Steps a b :=
  .cons h (.refl b)

theorem step_code {m : Machine} {base : Word} {code : List Nat} {off : Nat}
    (hcode : CodeAt m base code) (hpc : m.pc = base + BitVec.ofNat 32 off)
    {i : Instr} {len : Word} (h : fetchRel code off = some (i, len)) :
    step m = exec m i len := by
  unfold step
  rw [fetch_code hcode hpc h]
  rfl

/-! ## The machine after a write -/

@[simp] theorem Machine.getPc_eq (m : Machine) : Arch.getPc m = m.pc := rfl
@[simp] theorem Machine.setPc_pc (m : Machine) (v : Word) : (Arch.setPc m v).pc = v := rfl
@[simp] theorem Machine.setPc_mem (m : Machine) (v : Word) : (Arch.setPc m v).mem = m.mem := rfl
@[simp] theorem reg_setPc (m : Machine) (v : Word) (r : Fin 32) :
    reg (Arch.setPc m v) r = reg m r := rfl

@[simp] theorem writeReg_pc (m : Machine) (rd : Fin 32) (v : Word) :
    (writeReg m rd v).pc = m.pc := by
  unfold writeReg; split <;> rfl

@[simp] theorem writeReg_mem (m : Machine) (rd : Fin 32) (v : Word) :
    (writeReg m rd v).mem = m.mem := by
  unfold writeReg; split <;> rfl

theorem reg_writeReg (m : Machine) (rd : Fin 32) (v : Word) (r : Fin 32) :
    reg (writeReg m rd v) r = if r.val = 0 then 0 else if r = rd then v else reg m r := by
  unfold writeReg reg
  by_cases h0 : r.val = 0
  · simp [h0]
  · by_cases hr : r = rd
    · subst hr; simp [h0, Arch.getReg, Arch.setReg]
    · by_cases hd : rd.val = 0
      · simp [h0, hr, hd]
      · simp [h0, hr, hd, Arch.getReg, Arch.setReg]

/-- `x8` through `x16`, the registers the pilot proofs use. -/
abbrev x0 : Fin 32 := 0
abbrev ra : Fin 32 := 1
abbrev a0 : Fin 32 := 10
abbrev a1 : Fin 32 := 11
abbrev a2 : Fin 32 := 12
abbrev a3 : Fin 32 := 13
abbrev a4 : Fin 32 := 14
abbrev a5 : Fin 32 := 15
abbrev a6 : Fin 32 := 16

end C3.RV32
