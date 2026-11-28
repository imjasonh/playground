import C3BootProofs.Proofs.DerCall

/-!
# `Der::set`, `Der::octet_string`, `Der::bit_string`, and `Der::integer`

`Der::set` tail-calls `Der::nested` with tag 0x31. The other three call
`Der::element` through the prologue in `DerCall.lean`, then turn its result
into a `Result<&[u8], Error>` at `out`: a pointer and a length, or a zero
pointer and the error's discriminant.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem dset_at_0 : fetchRel derSetCode 0x0 = some (.aluImm .add a2 x0 0x31, 4) := by decide
theorem dset_at_4 : fetchRel derSetCode 0x4 = some (.auipc (6 : Fin 32) 0xFFFFD000, 4) := by decide
theorem dset_at_8 : fetchRel derSetCode 0x8 = some (.jalr x0 (6 : Fin 32) 0xAC, 4) := by decide
theorem dos_at_0 : fetchRel derOctetStringCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem dos_at_2 : fetchRel derOctetStringCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem dos_at_4 : fetchRel derOctetStringCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem dos_at_6 : fetchRel derOctetStringCode 0x6 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem dos_at_8 : fetchRel derOctetStringCode 0x8 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem dos_at_a : fetchRel derOctetStringCode 0xA = some (.aluImm .add a2 x0 0x4, 2) := by decide
theorem dos_at_c : fetchRel derOctetStringCode 0xC = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dos_at_10 : fetchRel derOctetStringCode 0x10 = some (.jalr ra ra 0xFFFFFF4E, 4) := by decide
theorem dos_at_14 : fetchRel derOctetStringCode 0x14 = some (.load .lw a0 sp 0x4, 2) := by decide
theorem dos_at_16 : fetchRel derOctetStringCode 0x16 = some (.branch .beq a0 x0 0x8, 2) := by decide
theorem dos_at_18 : fetchRel derOctetStringCode 0x18 = some (.load .lw a1 sp 0x8, 2) := by decide
theorem dos_at_1a : fetchRel derOctetStringCode 0x1A = some (.store .sw (8 : Fin 32) a1 0x4, 2) := by decide
theorem dos_at_1c : fetchRel derOctetStringCode 0x1C = some (.jal x0 0xA, 2) := by decide
theorem dos_at_1e : fetchRel derOctetStringCode 0x1E = some (.load .lbu a1 sp 0x8, 4) := by decide
theorem dos_at_22 : fetchRel derOctetStringCode 0x22 = some (.store .sb (8 : Fin 32) a1 0x4, 4) := by decide
theorem dos_at_26 : fetchRel derOctetStringCode 0x26 = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem dos_at_28 : fetchRel derOctetStringCode 0x28 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem dos_at_2a : fetchRel derOctetStringCode 0x2A = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem dos_at_2c : fetchRel derOctetStringCode 0x2C = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem dos_at_2e : fetchRel derOctetStringCode 0x2E = some (.jalr x0 ra 0x0, 2) := by decide
theorem dbs_at_0 : fetchRel derBitStringCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem dbs_at_2 : fetchRel derBitStringCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem dbs_at_4 : fetchRel derBitStringCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem dbs_at_6 : fetchRel derBitStringCode 0x6 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem dbs_at_8 : fetchRel derBitStringCode 0x8 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem dbs_at_a : fetchRel derBitStringCode 0xA = some (.aluImm .add a2 x0 0x3, 2) := by decide
theorem dbs_at_c : fetchRel derBitStringCode 0xC = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dbs_at_10 : fetchRel derBitStringCode 0x10 = some (.jalr ra ra 0x394, 4) := by decide
theorem dbs_at_14 : fetchRel derBitStringCode 0x14 = some (.load .lw a0 sp 0x4, 2) := by decide
theorem dbs_at_16 : fetchRel derBitStringCode 0x16 = some (.branch .beq a0 x0 0x10, 2) := by decide
theorem dbs_at_18 : fetchRel derBitStringCode 0x18 = some (.load .lw a1 sp 0x8, 2) := by decide
theorem dbs_at_1a : fetchRel derBitStringCode 0x1A = some (.branch .beq a1 x0 0x8, 2) := by decide
theorem dbs_at_1c : fetchRel derBitStringCode 0x1C = some (.load .lbu a2 a0 0x0, 4) := by decide
theorem dbs_at_20 : fetchRel derBitStringCode 0x20 = some (.branch .beq a2 x0 0x1A, 2) := by decide
theorem dbs_at_22 : fetchRel derBitStringCode 0x22 = some (.aluImm .add a0 x0 0x14, 2) := by decide
theorem dbs_at_24 : fetchRel derBitStringCode 0x24 = some (.jal x0 0x6, 2) := by decide
theorem dbs_at_26 : fetchRel derBitStringCode 0x26 = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem dbs_at_2a : fetchRel derBitStringCode 0x2A = some (.store .sw (8 : Fin 32) x0 0x0, 4) := by decide
theorem dbs_at_2e : fetchRel derBitStringCode 0x2E = some (.store .sb (8 : Fin 32) a0 0x4, 4) := by decide
theorem dbs_at_32 : fetchRel derBitStringCode 0x32 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem dbs_at_34 : fetchRel derBitStringCode 0x34 = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem dbs_at_36 : fetchRel derBitStringCode 0x36 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem dbs_at_38 : fetchRel derBitStringCode 0x38 = some (.jalr x0 ra 0x0, 2) := by decide
theorem dbs_at_3a : fetchRel derBitStringCode 0x3A = some (.aluImm .add a1 a1 0xFFFFFFFF, 2) := by decide
theorem dbs_at_3c : fetchRel derBitStringCode 0x3C = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem dbs_at_3e : fetchRel derBitStringCode 0x3E = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem dbs_at_40 : fetchRel derBitStringCode 0x40 = some (.store .sw (8 : Fin 32) a1 0x4, 2) := by decide
theorem dbs_at_42 : fetchRel derBitStringCode 0x42 = some (.jal x0 0xFFFFFFF0, 2) := by decide
theorem dint_at_0 : fetchRel derIntegerCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem dint_at_2 : fetchRel derIntegerCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem dint_at_4 : fetchRel derIntegerCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem dint_at_6 : fetchRel derIntegerCode 0x6 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem dint_at_8 : fetchRel derIntegerCode 0x8 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem dint_at_a : fetchRel derIntegerCode 0xA = some (.aluImm .add a2 x0 0x2, 2) := by decide
theorem dint_at_c : fetchRel derIntegerCode 0xC = some (.auipc ra 0x0, 4) := by decide
theorem dint_at_10 : fetchRel derIntegerCode 0x10 = some (.jalr ra ra 0x52, 4) := by decide
theorem dint_at_14 : fetchRel derIntegerCode 0x14 = some (.load .lw a0 sp 0x4, 2) := by decide
theorem dint_at_16 : fetchRel derIntegerCode 0x16 = some (.branch .beq a0 x0 0x10, 2) := by decide
theorem dint_at_18 : fetchRel derIntegerCode 0x18 = some (.load .lw a1 sp 0x8, 2) := by decide
theorem dint_at_1a : fetchRel derIntegerCode 0x1A = some (.aluImm .add a2 x0 0x1, 2) := by decide
theorem dint_at_1c : fetchRel derIntegerCode 0x1C = some (.branch .beq a1 a2 0x36, 4) := by decide
theorem dint_at_20 : fetchRel derIntegerCode 0x20 = some (.branch .bne a1 x0 0x14, 2) := by decide
theorem dint_at_22 : fetchRel derIntegerCode 0x22 = some (.aluImm .add a0 x0 0x14, 2) := by decide
theorem dint_at_24 : fetchRel derIntegerCode 0x24 = some (.jal x0 0x6, 2) := by decide
theorem dint_at_26 : fetchRel derIntegerCode 0x26 = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem dint_at_2a : fetchRel derIntegerCode 0x2A = some (.store .sw (8 : Fin 32) x0 0x0, 4) := by decide
theorem dint_at_2e : fetchRel derIntegerCode 0x2E = some (.store .sb (8 : Fin 32) a0 0x4, 4) := by decide
theorem dint_at_32 : fetchRel derIntegerCode 0x32 = some (.jal x0 0x24, 2) := by decide
theorem dint_at_34 : fetchRel derIntegerCode 0x34 = some (.load .lbu a2 a0 0x0, 4) := by decide
theorem dint_at_38 : fetchRel derIntegerCode 0x38 = some (.aluImm .add a3 a2 0xFFFFFF01, 4) := by decide
theorem dint_at_3c : fetchRel derIntegerCode 0x3C = some (.branch .beq a3 x0 0xE, 2) := by decide
theorem dint_at_3e : fetchRel derIntegerCode 0x3E = some (.branch .bne a2 x0 0x14, 2) := by decide
theorem dint_at_40 : fetchRel derIntegerCode 0x40 = some (.load .lb a2 a0 0x1, 4) := by decide
theorem dint_at_44 : fetchRel derIntegerCode 0x44 = some (.branch .bge a2 x0 0xFFFFFFDE, 4) := by decide
theorem dint_at_48 : fetchRel derIntegerCode 0x48 = some (.jal x0 0xA, 2) := by decide
theorem dint_at_4a : fetchRel derIntegerCode 0x4A = some (.load .lb a2 a0 0x1, 4) := by decide
theorem dint_at_4e : fetchRel derIntegerCode 0x4E = some (.branch .blt a2 x0 0xFFFFFFD4, 4) := by decide
theorem dint_at_52 : fetchRel derIntegerCode 0x52 = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem dint_at_54 : fetchRel derIntegerCode 0x54 = some (.store .sw (8 : Fin 32) a1 0x4, 2) := by decide
theorem dint_at_56 : fetchRel derIntegerCode 0x56 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem dint_at_58 : fetchRel derIntegerCode 0x58 = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem dint_at_5a : fetchRel derIntegerCode 0x5A = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem dint_at_5c : fetchRel derIntegerCode 0x5C = some (.jalr x0 ra 0x0, 2) := by decide
theorem dbt_at_0 : fetchRel derBooleanTrueCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem dbt_at_2 : fetchRel derBooleanTrueCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem dbt_at_4 : fetchRel derBooleanTrueCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem dbt_at_6 : fetchRel derBooleanTrueCode 0x6 = some (.alu .add a1 x0 a0, 2) := by decide
theorem dbt_at_8 : fetchRel derBooleanTrueCode 0x8 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem dbt_at_a : fetchRel derBooleanTrueCode 0xA = some (.aluImm .add a2 x0 0x1, 2) := by decide
theorem dbt_at_c : fetchRel derBooleanTrueCode 0xC = some (.aluImm .add (8 : Fin 32) x0 0x1, 2) := by decide
theorem dbt_at_e : fetchRel derBooleanTrueCode 0xE = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem dbt_at_12 : fetchRel derBooleanTrueCode 0x12 = some (.jalr ra ra 0xFFFFFE84, 4) := by decide
theorem dbt_at_16 : fetchRel derBooleanTrueCode 0x16 = some (.load .lw a1 sp 0x4, 2) := by decide
theorem dbt_at_18 : fetchRel derBooleanTrueCode 0x18 = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem dbt_at_1c : fetchRel derBooleanTrueCode 0x1C = some (.branch .beq a1 x0 0x34, 2) := by decide
theorem dbt_at_1e : fetchRel derBooleanTrueCode 0x1E = some (.load .lbu a2 sp 0x9, 4) := by decide
theorem dbt_at_22 : fetchRel derBooleanTrueCode 0x22 = some (.load .lbu a3 sp 0xA, 4) := by decide
theorem dbt_at_26 : fetchRel derBooleanTrueCode 0x26 = some (.load .lbu a4 sp 0xB, 4) := by decide
theorem dbt_at_2a : fetchRel derBooleanTrueCode 0x2A = some (.aluImm .sll a2 a2 0x8, 2) := by decide
theorem dbt_at_2c : fetchRel derBooleanTrueCode 0x2C = some (.aluImm .sll a3 a3 0x10, 2) := by decide
theorem dbt_at_2e : fetchRel derBooleanTrueCode 0x2E = some (.aluImm .sll a4 a4 0x18, 2) := by decide
theorem dbt_at_30 : fetchRel derBooleanTrueCode 0x30 = some (.alu .or a2 a2 a3, 2) := by decide
theorem dbt_at_32 : fetchRel derBooleanTrueCode 0x32 = some (.alu .or a0 a0 a4, 2) := by decide
theorem dbt_at_34 : fetchRel derBooleanTrueCode 0x34 = some (.alu .or a0 a0 a2, 2) := by decide
theorem dbt_at_36 : fetchRel derBooleanTrueCode 0x36 = some (.branch .bne a0 (8 : Fin 32) 0x18, 4) := by decide
theorem dbt_at_3a : fetchRel derBooleanTrueCode 0x3A = some (.load .lbu a0 a1 0x0, 4) := by decide
theorem dbt_at_3e : fetchRel derBooleanTrueCode 0x3E = some (.aluImm .add a0 a0 0xFFFFFF01, 4) := by decide
theorem dbt_at_42 : fetchRel derBooleanTrueCode 0x42 = some (.alu .sltu a0 x0 a0, 4) := by decide
theorem dbt_at_46 : fetchRel derBooleanTrueCode 0x46 = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem dbt_at_48 : fetchRel derBooleanTrueCode 0x48 = some (.aluImm .or a0 a0 0x14, 4) := by decide
theorem dbt_at_4c : fetchRel derBooleanTrueCode 0x4C = some (.jal x0 0x4, 2) := by decide
theorem dbt_at_4e : fetchRel derBooleanTrueCode 0x4E = some (.aluImm .add a0 x0 0x14, 2) := by decide
theorem dbt_at_50 : fetchRel derBooleanTrueCode 0x50 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem dbt_at_52 : fetchRel derBooleanTrueCode 0x52 = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem dbt_at_54 : fetchRel derBooleanTrueCode 0x54 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem dbt_at_56 : fetchRel derBooleanTrueCode 0x56 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- **The compiled `Der::set`** is `Der::nested` for tag 0x31, which it
tail-calls at `Q + 0xFFFFD0B0`. -/
theorem derSet_correct (m : Machine) {Q sp0 out d retAddr : Word} (hQ : Q.toNat % 2 = 0)
    (hc : CodeIn m.mem Q derSetCode) (env : NestEnv m.mem (Q + 0xFFFFD0B0) sp0 out d)
    (hpc : m.pc = Q) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = d)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, oidKeep q = true → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 →
        m'.mem x = derNestedMem (derAdvance m.mem d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
          (derElement 0x31 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)))
          out (memLoad32 m.mem (d + 8))
          (derElement 0x31 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)) x := by
  have s0 : St m.mem Q m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc dset_at_0 (off' := 4) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.auipc hc dset_at_4 (off' := 8) (by decide)
  obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc dset_at_8
  have k3 : ∀ q, q ≠ a2 → q ≠ t1 → reg n3 q = reg m q := fun q h2 ht => by
    rw [regs3, updz (upd_zero _ _ _) ht, updz hz h2]
  have pcN : n3.pc = Q + 0xFFFFD0B0 := by
    rw [pc3]; simp +decide only [upd_app, ↓reduceIte]
    rw [show Q + BitVec.ofNat 32 4 + 0xFFFFD000 + 0xAC = Q + 0xFFFFD0B0 by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact even_clear _ (even_at Q hQ 0xFFFFD0B0 (by decide))
  obtain ⟨m4, c4, pc4, sp4, k4, f4⟩ := derNested_correct n3 (tag := 0x31) (by rw [mem3]; exact env) pcN
    (by rw [k3 sp (by decide) (by decide), hsp]) (by rw [k3 a0 (by decide) (by decide), ha0])
    (by rw [k3 a1 (by decide) (by decide), ha1])
    (by rw [regs3, updz (upd_zero _ _ _) (by decide)]; simp +decide only [upd_app, ↓reduceIte]; rw [hz]; rfl)
    (by decide) (by rw [k3 ra (by decide) (by decide), hra]) hret
  rw [mem3] at f4
  exact ⟨m4, .cons d1 (.cons d2 (.cons d3 c4)), pc4, sp4, fun q hq => by
    rw [k4 q hq, k3 q (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide))],
    f4⟩

/-- What a reader that returns `Result<&[u8], Error>` stores at `out`: the
slice's pointer and length, or a zero pointer and the error. -/
def derSliceMem (M : Word → BitVec 8) (out : Word) : Except DerError (Word × Word) → Word → BitVec 8
  | .error e => memStore8 (memStore32 M out 0) (out + 4) (derErrByte e)
  | .ok (p, l) => memStore32 (memStore32 M out p) (out + 4) l

/-- `x` is `out` plus a natural offset below `2 ^ 32`. -/
theorem off_of (out x : Word) : out + BitVec.ofNat 32 (x - out).toNat = x := by
  rw [ofNat_toNat_self, BitVec.add_comm, BitVec.sub_add_cancel]

/-- The word at `out` and the one at `out + 4` don't overlap, so their
stores commute. -/
theorem slice_ok_comm (M : Word → BitVec 8) (out p l x : Word) :
    memStore32 (memStore32 M (out + 4) l) out p x = memStore32 (memStore32 M out p) (out + 4) l x := by
  have hx := off_of out x
  have hk := (x - out).isLt
  generalize (x - out).toNat = k at hx hk
  subst hx
  by_cases h : k < 4
  · have s : Sep (out + 4) 4 (out + BitVec.ofNat 32 k) 1 :=
      sep_offsets out (c := 4) (n := 4) (d := k) (k := 1) (.inr (by omega)) (by omega) (by omega)
    rw [memStore32_pt (memStore32_get_sep s), memStore32_get_sep s]
  · have s : Sep out 4 (out + BitVec.ofNat 32 k) 1 := by
      have := sep_offsets out (c := 0) (n := 4) (d := k) (k := 1) (.inl (by omega)) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    rw [memStore32_get_sep s, memStore32_pt (memStore32_get_sep s)]

/-- The error byte at `out + 4` is outside the word at `out`. -/
theorem slice_err_comm (M : Word → BitVec 8) (out x : Word) (b : BitVec 8) :
    memStore32 (memStore8 M (out + 4) b) out 0 x = memStore8 (memStore32 M out 0) (out + 4) b x := by
  have hx := off_of out x
  have hk := (x - out).isLt
  generalize (x - out).toNat = k at hx hk
  subst hx
  by_cases h : k < 4
  · have s : Sep (out + 4) 1 (out + BitVec.ofNat 32 k) 1 :=
      sep_offsets out (c := 4) (n := 1) (d := k) (k := 1) (.inr (by omega)) (by omega) (by omega)
    have hne : out + BitVec.ofNat 32 k ≠ out + 4 := fun e =>
      s 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)
    rw [memStore32_pt (memStore8_ne hne), memStore8_ne hne]
  · have s : Sep out 4 (out + BitVec.ofNat 32 k) 1 := by
      have := sep_offsets out (c := 0) (n := 4) (d := k) (k := 1) (.inl (by omega)) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    rw [memStore32_get_sep s, memStore8_pt (memStore32_get_sep s)]

/-- An element's contents as a pointer and a length, for unread bytes at `rp`. -/
def derContent (rp : Word) : Except DerError DerTlv → Except DerError (Word × Word)
  | .error e => .error e
  | .ok t => .ok (rp + BitVec.ofNat 32 t.header, BitVec.ofNat 32 t.len)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `Der::octet_string`**: with the reader at `d`, whose
unread bytes start at `rp` and number `rl`, it stores the contents of
`derElement 4` of those bytes at `out`, or its error, and moves the reader
past the element. -/
theorem derOctetString_correct (m : Machine) {P sp0 out d retAddr : Word}
    (env : DerCallEnv m.mem derOctetStringCode P 0xFFFFCF5A sp0 out d 8)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = d)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, oidKeep q = true → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 →
        m'.mem x = derSliceMem (derAdvance m.mem d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
          (derElement 4 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat))) out
          (derContent (memLoad32 m.mem (d + 8))
            (derElement 4 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat))) x := by
  obtain ⟨m5, Msv, S5, u5, sp5, s85, k5, frSv, slR, sl8⟩ := derCall_pro m (tag := 4) env dos_at_0
    (by decide) (by decide) dos_at_c dos_at_10 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    hpc hsp ha0 ha1
  have hrp0 := env.hrp; have hrw := env.hrw
  generalize memLoad32 m.mem (d + 8) = rp at u5 hrp0 hrw ⊢
  generalize memLoad32 m.mem (d + 0xC) = rl at u5 hrw ⊢
  generalize hr : derElement 4 (memBytes m.mem rp rl.toNat) = r at u5 ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFE0 = F := ⟨_, rfl⟩
  have sFC := env.sFC; have sOF := env.sOF; have sDF := env.sDF
  rw [hF] at u5 sp5 frSv slR sl8 sFC sOF sDF ⊢
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add env.hsp (k := 0xFFFFFFE0) (by decide)
  have eS : F + 0x20 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have hc5 : CodeIn (derTlvMem Msv (F + 4) d rp rl r) P derOctetStringCode := fun i hi => by
    rw [derCall_outside r frSv (sFC.subR (c := i) (l := 1) (by omega)),
      derAdvance_outside r (env.sDC.subR (c := i) (l := 1) (by omega))]
    exact env.cod i hi
  have hF8 : F + 8 = F + 4 + 4 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n6, d6, u6⟩ := u5.lw hc5 dos_at_14 (off' := 0x16) (by decide)
    (by rw [sp5]; exact aligned_add hFa (k := 4) (by decide))
  rw [sp5] at u6
  have fin : ∀ {Mx : Word → BitVec 8} {n : Machine}, Steps m5 n → St Mx P n 0x28 (reg n) → CodeIn Mx P derOctetStringCode →
      (∀ x, Sep out 8 x 1 → Mx x = derTlvMem Msv (F + 4) d rp rl r x) → reg n sp = F →
      (∀ q, oidKeep q = true → reg n q = reg m5 q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ n'.mem = Mx ∧ reg n' sp = sp0 ∧
        ∀ q, oidKeep q = true → reg n' q = reg m q := by
    intro Mx n S s hc hMx rsp kq
    obtain ⟨n', c', pc', mem', sp', ra', s8', k'⟩ := derCall_epi s hc (by decide) dos_at_2c dos_at_2e hFa rsp
      (by rw [derCall_slot r sOF sDF (o := 0x1C) (by decide) hMx, slR, hra]) hret
    refine ⟨n', S5.trans (S.trans c'), pc', mem', by rw [sp', eS],
      derCall_keep hsp k5 (fun q hq h1 h8 hs => by rw [k' q h1 h8 hs, kq q hq]) (by rw [sp', eS])
        (by rw [ra', hra]) (by rw [s8', derCall_slot r sOF sDF (o := 0x18) (by decide) hMx, sl8])⟩
  cases r with
  | error e =>
    have h0 : memLoad32 (derTlvMem Msv (F + 4) d rp rl (.error e)) (F + 4) = 0 := derTlvMem_err0 e
    obtain ⟨n7, d7, u7⟩ := u6.taken hc5 0x1E dos_at_16 (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [h0]; rfl)
    obtain ⟨n8, d8, u8⟩ := u7.lbu hc5 dos_at_1e (off' := 0x22) (by decide)
    have eb : derTlvMem Msv (F + 4) d rp rl (.error e)
        (upd (reg m5) a0 (memLoad32 (derTlvMem Msv (F + 4) d rp rl (.error e)) (F + 4)) sp + 8) = derErrByte e := by
      rw [upd_ne (by decide) (by decide), sp5, hF8]; exact derTlvMem_err4 e
    rw [eb] at u8
    obtain ⟨n9, d9, u9⟩ := u8.sb hc5 dos_at_22 (off' := 0x26) (by decide)
    simp only [upd_app] at u9; simp +decide only [↓reduceIte] at u9
    rw [s85, tlv_zext] at u9
    have hc9 := CodeIn.store8 (v := derErrByte e) hc5 (env.sOC.sub (c := 4) (l := 1) (by decide))
    obtain ⟨n10, d10, u10⟩ := u9.sw hc9 dos_at_26 (off' := 0x28) (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [s85, add_lit_zero]; exact env.hout)
    simp only [upd_app] at u10; simp +decide only [↓reduceIte] at u10
    rw [s85, add_lit_zero, h0] at u10
    have hc10 := CodeIn.store32 (v := 0) hc9 (env.sOC.sub (c := 0) (l := 4) (by decide) |> fun h => by
      rwa [add_ofNat_zero] at h)
    obtain ⟨n', S', pc', mem', sp', k'⟩ := fin (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.single d10))))) u10.self hc10
      (fun x hx => by
        rw [memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h),
          memStore8_ne fun e' => hx 4 (by decide) 0 (by decide) (by rw [add_ofNat_zero]; exact e'.symm)])
      (by rw [u10.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp5)
      (fun q hq => by
        have h0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
        have h1 : q ≠ a1 := fun e => by subst e; exact absurd hq (by decide)
        rw [u10.regs]; simp only [upd_app]
        by_cases hq0 : q.val = 0
        · have : q = 0 := Fin.ext hq0
          subst this; simp; exact u5.zero.symm
        simp only [hq0, h0, h1, ite_false])
    refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
    rw [mem', slice_err_comm]; simp only [derSliceMem, derContent]
    exact memStore8_pt (memStore32_pt (derCall_outside _ frSv hx))
  | ok t =>
    have h0 : memLoad32 (derTlvMem Msv (F + 4) d rp rl (.ok t)) (F + 4) = rp + BitVec.ofNat 32 t.header :=
      derTlvMem_ok0 t
    have hb : t.header + t.len ≤ rl.toNat := by
      have := derElement_bound hr; rwa [memBytes_length] at this
    have hnz : rp + BitVec.ofNat 32 t.header ≠ 0 := fun h => by
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_add, ofNat_tn (by omega), Nat.mod_eq_of_lt (by omega)] at this
      change _ = 0 at this; omega
    obtain ⟨n7, d7, u7⟩ := u6.notTaken hc5 0x18 dos_at_16 (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [h0]
      exact beq_false_of_ne hnz)
    obtain ⟨n8, d8, u8⟩ := u7.lw hc5 dos_at_18 (off' := 0x1A) (by decide)
      (by rw [upd_ne (by decide) (by decide), sp5]; exact aligned_add hFa (k := 8) (by decide))
    have elen : memLoad32 (derTlvMem Msv (F + 4) d rp rl (.ok t))
        (upd (reg m5) a0 (memLoad32 (derTlvMem Msv (F + 4) d rp rl (.ok t)) (F + 4)) sp + 8) =
        BitVec.ofNat 32 t.len := by
      rw [upd_ne (by decide) (by decide), sp5, hF8]; exact derTlvMem_ok4 t
    rw [elen, h0] at u8
    obtain ⟨n9, d9, u9⟩ := u8.sw hc5 dos_at_1a (off' := 0x1C) (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [s85]; exact aligned_add env.hout (k := 4) (by decide))
    simp only [upd_app] at u9; simp +decide only [↓reduceIte] at u9
    rw [s85] at u9
    have hc9 := CodeIn.store32 (v := BitVec.ofNat 32 t.len) hc5 (env.sOC.sub (c := 4) (l := 4) (by decide))
    obtain ⟨n10, d10, u10⟩ := u9.jump hc9 dos_at_1c (off' := 0x26) (by decide) (by
      rw [u9.pc, show P + BitVec.ofNat 32 0x1C + 0xA = P + BitVec.ofNat 32 0x26 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P env.hP 0x26 (by decide)))
    obtain ⟨n11, d11, u11⟩ := u10.sw hc9 dos_at_26 (off' := 0x28) (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [s85, add_lit_zero]; exact env.hout)
    simp only [upd_app] at u11; simp +decide only [↓reduceIte] at u11
    rw [s85, add_lit_zero] at u11
    have hc11 := CodeIn.store32 (v := rp + BitVec.ofNat 32 t.header) hc9
      (env.sOC.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
    obtain ⟨n', S', pc', mem', sp', k'⟩ := fin (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10 (.single d11))))))
      u11.self hc11
      (fun x hx => by
        rw [memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h),
          memStore32_get_sep (a := out + 4) (hx.sub (c := 4) (l := 4) (by decide))])
      (by rw [u11.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp5)
      (fun q hq => by
        have h0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
        have h1 : q ≠ a1 := fun e => by subst e; exact absurd hq (by decide)
        rw [u11.regs]; simp only [upd_app]
        by_cases hq0 : q.val = 0
        · have : q = 0 := Fin.ext hq0
          subst this; simp; exact u5.zero.symm
        simp only [hq0, h0, h1, ite_false])
    refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
    rw [mem', slice_ok_comm]; simp only [derSliceMem, derContent]
    exact memStore32_pt (memStore32_pt (derCall_outside _ frSv hx))

/-- `Der::bit_string`'s result for the unread bytes `L` at `rp`: the
contents after their first byte, which counts the unused bits and must be 0. -/
def derBitsOf (L : Bytes) (rp : Word) : Except DerError DerTlv → Except DerError (Word × Word)
  | .error e => .error e
  | .ok t => if t.len ≠ 0 ∧ L.getD t.header 0 = 0 then
      .ok (rp + BitVec.ofNat 32 (t.header + 1), BitVec.ofNat 32 (t.len - 1)) else .error .badDer

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The compiled `Der::bit_string`**: with the reader at `d`, whose
unread bytes start at `rp` and number `rl` and don't overlap the reader, it
stores `derBitsOf` of `derElement 3` of those bytes at `out`, and moves the
reader past the element. -/
theorem derBitString_correct (m : Machine) {P sp0 out d retAddr : Word}
    (env : DerCallEnv m.mem derBitStringCode P 0xFFFFD3A0 sp0 out d 8)
    (sDR : Sep (d + 8) 8 (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = d)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, oidKeep q = true → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 →
        m'.mem x = derSliceMem (derAdvance m.mem d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
          (derElement 3 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat))) out
          (derBitsOf (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)
            (memLoad32 m.mem (d + 8))
            (derElement 3 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat))) x := by
  obtain ⟨m5, Msv, S5, u5, sp5, s85, k5, frSv, slR, sl8⟩ := derCall_pro m (tag := 3) env dbs_at_0
    (by decide) (by decide) dbs_at_c dbs_at_10 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    hpc hsp ha0 ha1
  have hrp0 := env.hrp; have hrw := env.hrw; have sRF := env.sRF
  generalize memLoad32 m.mem (d + 8) = rp at u5 hrp0 hrw sRF sDR ⊢
  generalize memLoad32 m.mem (d + 0xC) = rl at u5 hrw sRF sDR ⊢
  generalize hr : derElement 3 (memBytes m.mem rp rl.toNat) = r at u5 ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFE0 = F := ⟨_, rfl⟩
  have sFC := env.sFC; have sOF := env.sOF; have sDF := env.sDF
  rw [hF] at u5 sp5 frSv slR sl8 sFC sOF sDF sRF ⊢
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add env.hsp (k := 0xFFFFFFE0) (by decide)
  have eS : F + 0x20 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have hc5 : CodeIn (derTlvMem Msv (F + 4) d rp rl r) P derBitStringCode := fun i hi => by
    rw [derCall_outside r frSv (sFC.subR (c := i) (l := 1) (by omega)),
      derAdvance_outside r (env.sDC.subR (c := i) (l := 1) (by omega))]
    exact env.cod i hi
  have hF8 : F + 8 = F + 4 + 4 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n6, d6, u6⟩ := u5.lw hc5 dbs_at_14 (off' := 0x16) (by decide)
    (by rw [sp5]; exact aligned_add hFa (k := 4) (by decide))
  rw [sp5] at u6
  have hkk : ∀ q : Fin 32, oidKeep q = true → q.val ∉ [10, 11, 12] := by decide
  have kx : ∀ {f : Fin 32 → Word}, (∀ q, q.val ∉ [10, 11, 12] → f q = reg m5 q) →
      ∀ q, oidKeep q = true → f q = reg m5 q := fun hq q hk => hq q (hkk q hk)
  have fin : ∀ {Mx : Word → BitVec 8} {n : Machine}, Steps m5 n → St Mx P n 0x32 (reg n) →
      CodeIn Mx P derBitStringCode → (∀ x, Sep out 8 x 1 → Mx x = derTlvMem Msv (F + 4) d rp rl r x) →
      reg n sp = F → (∀ q, oidKeep q = true → reg n q = reg m5 q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ n'.mem = Mx ∧ reg n' sp = sp0 ∧
        ∀ q, oidKeep q = true → reg n' q = reg m q := by
    intro Mx n S s hc hMx rsp kq
    obtain ⟨n', c', pc', mem', sp', ra', s8', k'⟩ := derCall_epi s hc (by decide) dbs_at_36 dbs_at_38 hFa rsp
      (by rw [derCall_slot r sOF sDF (o := 0x1C) (by decide) hMx, slR, hra]) hret
    refine ⟨n', S5.trans (S.trans c'), pc', mem', by rw [sp', eS],
      derCall_keep hsp k5 (fun q hq h1 h8 hs => by rw [k' q h1 h8 hs, kq q hq]) (by rw [sp', eS])
        (by rw [ra', hra]) (by rw [s8', derCall_slot r sOF sDF (o := 0x18) (by decide) hMx, sl8])⟩
  -- the error exit at 0x2A, with the discriminant in `a0`
  have tail : ∀ {n : Machine}, Steps m5 n → St (derTlvMem Msv (F + 4) d rp rl r) P n 0x2A (reg n) →
      reg n 8 = out → reg n sp = F → (∀ q, oidKeep q = true → reg n q = reg m5 q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧
        n'.mem = memStore8 (memStore32 (derTlvMem Msv (F + 4) d rp rl r) out 0) (out + 4)
          ((reg n a0).extractLsb' 0 8) ∧ reg n' sp = sp0 ∧ ∀ q, oidKeep q = true → reg n' q = reg m q := by
    intro n S s r8 rsp kq
    obtain ⟨n1, d1, u1⟩ := s.sw hc5 dbs_at_2a (off' := 0x2E) (by decide) (by rw [r8, add_lit_zero]; exact env.hout)
    rw [r8, add_lit_zero, s.zero] at u1
    have hc1 := CodeIn.store32 (v := 0) hc5 (env.sOC.sub (c := 0) (l := 4) (by decide) |> fun h => by
      rwa [add_ofNat_zero] at h)
    obtain ⟨n2, d2, u2⟩ := u1.sb hc1 dbs_at_2e (off' := 0x32) (by decide)
    rw [r8] at u2
    have hc2 := CodeIn.store8 (v := (reg n a0).extractLsb' 0 8) hc1 (env.sOC.sub (c := 4) (l := 1) (by decide))
    obtain ⟨n', S', pc', mem', sp', k'⟩ := fin (S.trans (.cons d1 (.single d2))) u2.self hc2
      (fun x hx => by
        rw [memStore8_ne fun e' => hx 4 (by decide) 0 (by decide) (by rw [add_ofNat_zero]; exact e'.symm),
          memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)])
      (by rw [u2.regs]; exact rsp) (fun q hq => by rw [u2.regs]; exact kq q hq)
    exact ⟨n', S', pc', mem', sp', k'⟩
  cases r with
  | error e =>
    have h0 : memLoad32 (derTlvMem Msv (F + 4) d rp rl (.error e)) (F + 4) = 0 := derTlvMem_err0 e
    obtain ⟨n7, d7, u7⟩ := u6.taken hc5 0x26 dbs_at_16 (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [h0]; rfl)
    obtain ⟨n8, d8, u8⟩ := u7.lbu hc5 dbs_at_26 (off' := 0x2A) (by decide)
    have eb : derTlvMem Msv (F + 4) d rp rl (.error e)
        (upd (reg m5) a0 (memLoad32 (derTlvMem Msv (F + 4) d rp rl (.error e)) (F + 4)) sp + 8) = derErrByte e := by
      rw [upd_ne (by decide) (by decide), sp5, hF8]; exact derTlvMem_err4 e
    rw [eb] at u8
    obtain ⟨n', S', pc', mem', sp', k'⟩ := tail (.cons d6 (.cons d7 (.single d8))) u8.self
      (by rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]; exact s85)
      (by rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp5)
      (fun q hq => by rw [u8.regs]; exact kx (fun q h => by
        simp only [upd_app]
        by_cases hq0 : q.val = 0
        · have : q = 0 := Fin.ext hq0
          subst this; simp; exact u5.zero.symm
        have h0 : q ≠ a0 := fun e => h (by rw [e]; decide)
        simp only [hq0, h0, ite_false]) q hq)
    refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
    rw [mem', u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [tlv_zext]
    simp only [derSliceMem, derBitsOf]
    exact memStore8_pt (memStore32_pt (derCall_outside _ frSv hx))
  | ok t =>
    have hb : t.header + t.len ≤ rl.toNat := by
      have := derElement_bound hr; rwa [memBytes_length] at this
    have h0 : memLoad32 (derTlvMem Msv (F + 4) d rp rl (.ok t)) (F + 4) = rp + BitVec.ofNat 32 t.header :=
      derTlvMem_ok0 t
    have hcp : (rp + BitVec.ofNat 32 t.header).toNat = rp.toNat + t.header := by
      rw [BitVec.toNat_add, ofNat_tn (by omega)]; exact Nat.mod_eq_of_lt (by omega)
    have hnz : rp + BitVec.ofNat 32 t.header ≠ 0 := fun h => by
      have := congrArg BitVec.toNat h; rw [hcp] at this; change _ = 0 at this; omega
    obtain ⟨n7, d7, u7⟩ := u6.notTaken hc5 0x18 dbs_at_16 (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [h0]
      exact beq_false_of_ne hnz)
    obtain ⟨n8, d8, u8⟩ := u7.lw hc5 dbs_at_18 (off' := 0x1A) (by decide)
      (by rw [upd_ne (by decide) (by decide), sp5]; exact aligned_add hFa (k := 8) (by decide))
    have elen : memLoad32 (derTlvMem Msv (F + 4) d rp rl (.ok t))
        (upd (reg m5) a0 (memLoad32 (derTlvMem Msv (F + 4) d rp rl (.ok t)) (F + 4)) sp + 8) =
        BitVec.ofNat 32 t.len := by
      rw [upd_ne (by decide) (by decide), sp5, hF8]; exact derTlvMem_ok4 t
    rw [elen, h0] at u8
    have r8 : ∀ q, q ≠ a0 → q ≠ a1 → upd (upd (reg m5) a0 (rp + BitVec.ofNat 32 t.header)) a1
        (BitVec.ofNat 32 t.len) q = reg m5 q := fun q h0 h1 => by
      rw [upd_ne' h1 (by simp [upd]), upd_ne' h0 u5.zero]
    -- the BadDer exit through 0x22
    have bad : ∀ {n : Machine}, Steps m5 n → St (derTlvMem Msv (F + 4) d rp rl (.ok t)) P n 0x22 (reg n) →
        reg n 8 = out → reg n sp = F → (∀ q, oidKeep q = true → reg n q = reg m5 q) →
        ∃ n', Steps m n' ∧ n'.pc = retAddr ∧
          n'.mem = memStore8 (memStore32 (derTlvMem Msv (F + 4) d rp rl (.ok t)) out 0) (out + 4) 0x14 ∧
          reg n' sp = sp0 ∧ ∀ q, oidKeep q = true → reg n' q = reg m q := by
      intro n S s r8' rsp kq
      obtain ⟨n1, d1, u1⟩ := s.aluImm hc5 dbs_at_22 (off' := 0x24) (by decide)
      obtain ⟨n2, d2, u2⟩ := u1.jump hc5 dbs_at_24 (off' := 0x2A) (by decide) (by
        rw [u1.pc, show P + BitVec.ofNat 32 0x24 + 0x6 = P + BitVec.ofNat 32 0x2A by rw [BitVec.add_assoc]; rfl]
        exact even_bit0 (even_at P env.hP 0x2A (by decide)))
      obtain ⟨n', S', pc', mem', sp', k'⟩ := tail (S.trans (.cons d1 (.single d2))) u2.self
        (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; exact r8')
        (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; exact rsp)
        (fun q hq => by
          rw [u2.regs]; rw [upd_ne' (fun e => by subst e; exact absurd hq (by decide)) s.zero]; exact kq q hq)
      refine ⟨n', S', pc', ?_, sp', k'⟩
      rw [mem', u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [s.zero]; rfl
    have kq8 : ∀ q, oidKeep q = true → upd (upd (reg m5) a0 (rp + BitVec.ofNat 32 t.header)) a1
        (BitVec.ofNat 32 t.len) q = reg m5 q := fun q hq =>
      r8 q (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide))
    by_cases hl : t.len = 0
    · obtain ⟨n9, d9, u9⟩ := u8.taken hc5 0x22 dbs_at_1a (by decide) (by
        simp +decide only [upd_app, ↓reduceIte]; rw [hl]; rfl)
      obtain ⟨n', S', pc', mem', sp', k'⟩ := bad (.cons d6 (.cons d7 (.cons d8 (.single d9)))) u9.self
        (by rw [u9.regs, r8 8 (by decide) (by decide), s85]) (by rw [u9.regs, r8 sp (by decide) (by decide), sp5])
        (fun q hq => by rw [u9.regs]; exact kq8 q hq)
      refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
      rw [mem']; simp only [derSliceMem, derBitsOf, hl, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
      exact memStore8_pt (memStore32_pt (derCall_outside _ frSv hx))
    have hl1 : 1 ≤ t.len := Nat.one_le_iff_ne_zero.mpr hl
    have hL : t.len < 2 ^ 32 := by have := rl.isLt; omega
    obtain ⟨n9, d9, u9⟩ := u8.notTaken hc5 0x1C dbs_at_1a (by decide) (by
      simp +decide only [upd_app, ↓reduceIte]
      exact beq_false_of_ne fun h => hl (by
        have := congrArg BitVec.toNat h; rwa [ofNat_tn hL] at this))
    obtain ⟨n10, d10, u10⟩ := u9.lbu hc5 dbs_at_1c (off' := 0x20) (by decide)
    have ebyte : derTlvMem Msv (F + 4) d rp rl (.ok t)
        (upd (upd (reg m5) a0 (rp + BitVec.ofNat 32 t.header)) a1 (BitVec.ofNat 32 t.len) a0 + 0) =
        m.mem (rp + BitVec.ofNat 32 t.header) := by
      simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero]
      rw [derCall_outside _ frSv (sRF.symm.subR (c := t.header) (l := 1) (by omega)),
        derAdvance_outside _ (sDR.subR (c := t.header) (l := 1) (by omega))]
    rw [ebyte] at u10
    have hgd : (memBytes m.mem rp rl.toNat).getD t.header 0 = (m.mem (rp + BitVec.ofNat 32 t.header)).toNat :=
      memBytes_getD (by omega)
    by_cases hz : (m.mem (rp + BitVec.ofNat 32 t.header)).toNat = 0
    · obtain ⟨n11, d11, u11⟩ := u10.taken hc5 0x3A dbs_at_20 (by decide) (by
        simp +decide only [upd_app, ↓reduceIte]
        show ((m.mem (rp + BitVec.ofNat 32 t.header)).zeroExtend 32 == (0 : Word)) = true
        rw [show m.mem (rp + BitVec.ofNat 32 t.header) = 0 from BitVec.eq_of_toNat_eq hz]; rfl)
      obtain ⟨n12, d12, u12⟩ := u11.aluImm hc5 dbs_at_3a (off' := 0x3C) (by decide)
      obtain ⟨n13, d13, u13⟩ := u12.aluImm hc5 dbs_at_3c (off' := 0x3E) (by decide)
      have v13 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n13 q = reg m5 q := fun q h0 h1 h2 => by
        rw [u13.regs, upd_ne' h0 (by simp [upd]), upd_ne' h1 (by simp [upd]), upd_ne' h2 (by simp [upd]),
          r8 q h0 h1]
      have va0 : reg n13 a0 = rp + BitVec.ofNat 32 (t.header + 1) := by
        rw [u13.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [ev_add, BitVec.add_assoc, show (1 : Word) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat]
      have va1 : reg n13 a1 = BitVec.ofNat 32 (t.len - 1) := by
        rw [u13.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, ofNat_tn hL, ofNat_tn (by omega)]
        change (t.len + 4294967295) % 4294967296 = _; omega
      obtain ⟨n14, d14, u14⟩ := u13.self.sw hc5 dbs_at_3e (off' := 0x40) (by decide)
        (by rw [v13 8 (by decide) (by decide) (by decide), s85, add_lit_zero]; exact env.hout)
      rw [v13 8 (by decide) (by decide) (by decide), s85, add_lit_zero, va0] at u14
      have hc14 := CodeIn.store32 (v := rp + BitVec.ofNat 32 (t.header + 1)) hc5
        (env.sOC.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
      obtain ⟨n15, d15, u15⟩ := u14.sw hc14 dbs_at_40 (off' := 0x42) (by decide)
        (by rw [v13 8 (by decide) (by decide) (by decide), s85]; exact aligned_add env.hout (k := 4) (by decide))
      rw [v13 8 (by decide) (by decide) (by decide), s85, va1] at u15
      have hc15 := CodeIn.store32 (v := BitVec.ofNat 32 (t.len - 1)) hc14 (env.sOC.sub (c := 4) (l := 4) (by decide))
      obtain ⟨n16, d16, u16⟩ := u15.jump hc15 dbs_at_42 (off' := 0x32) (by decide) (by
        rw [u15.pc, show P + BitVec.ofNat 32 0x42 + 0xFFFFFFF0 = P + BitVec.ofNat 32 0x32 by
          rw [BitVec.add_assoc]; rfl]
        exact even_bit0 (even_at P env.hP 0x32 (by decide)))
      obtain ⟨n', S', pc', mem', sp', k'⟩ := fin
        (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14
          (.cons d15 (.single d16)))))))))))
        u16.self hc15
        (fun x hx => by
          rw [memStore32_get_sep (a := out + 4) (hx.sub (c := 4) (l := 4) (by decide)),
            memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)])
        (by rw [u16.regs, v13 sp (by decide) (by decide) (by decide), sp5])
        (fun q hq => by
          rw [u16.regs]
          exact v13 q (fun e => by subst e; exact absurd hq (by decide))
            (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide)))
      refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
      rw [mem']; simp only [derSliceMem, derBitsOf, hgd, hz, ne_eq, hl, not_false_eq_true, and_self, ↓reduceIte]
      exact memStore32_pt (memStore32_pt (derCall_outside _ frSv hx))
    · obtain ⟨n11, d11, u11⟩ := u10.notTaken hc5 0x22 dbs_at_20 (by decide) (by
        simp +decide only [upd_app, ↓reduceIte]
        exact beq_false_of_ne fun h => hz (by
          have := congrArg BitVec.toNat h
          rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (m.mem (rp + BitVec.ofNat 32 t.header)).isLt; omega)]
            at this))
      have v10 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n11 q = reg m5 q := fun q h0 h1 h2 => by
        rw [u11.regs, upd_ne' h2 (by simp [upd]), r8 q h0 h1]
      obtain ⟨n', S', pc', mem', sp', k'⟩ := bad
        (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10 (.single d11)))))) u11.self
        (by rw [v10 8 (by decide) (by decide) (by decide), s85]) (by rw [v10 sp (by decide) (by decide) (by decide), sp5])
        (fun q hq => v10 q (fun e => by subst e; exact absurd hq (by decide))
          (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide)))
      refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
      rw [mem']; simp only [derSliceMem, derBitsOf, hgd, hz, and_false, ↓reduceIte]
      exact memStore8_pt (memStore32_pt (derCall_outside _ frSv hx))

/-- `Der::integer`'s result for the unread bytes `L` at `rp`: the contents,
which must not be empty or start with a redundant sign byte. -/
def derIntOf (L : Bytes) (rp : Word) : Except DerError DerTlv → Except DerError (Word × Word)
  | .error e => .error e
  | .ok t =>
    if t.len = 0 then .error .badDer
    else if 2 ≤ t.len ∧ ((L.getD t.header 0 = 0 ∧ L.getD (t.header + 1) 0 < 0x80) ∨
        (L.getD t.header 0 = 0xFF ∧ 0x80 ≤ L.getD (t.header + 1) 0)) then .error .badDer
    else .ok (rp + BitVec.ofNat 32 t.header, BitVec.ofNat 32 t.len)

theorem int_ff : ∀ b : BitVec 8,
    branchTaken .beq (aluEval .add (b.zeroExtend 32) 0xFFFFFF01) 0 = decide (b.toNat = 255) := by decide
theorem int_nz : ∀ b : BitVec 8, branchTaken .bne (b.zeroExtend 32) 0 = !decide (b.toNat = 0) := by decide
theorem int_bge : ∀ b : BitVec 8, branchTaken .bge (b.signExtend 32) 0 = decide (b.toNat < 128) := by decide
theorem int_blt : ∀ b : BitVec 8, branchTaken .blt (b.signExtend 32) 0 = decide (128 ≤ b.toNat) := by decide

/-- Writing a register that `oidKeep` doesn't keep keeps the ones it does. -/
theorem okeep_upd {f g : Fin 32 → Word} {rd : Fin 32} {v : Word} (h0 : f 0 = 0) (hrd : oidKeep rd = false)
    (hf : ∀ q, oidKeep q = true → f q = g q) : ∀ q, oidKeep q = true → upd f rd v q = g q := fun q hq => by
  have hne : q ≠ rd := fun e => by subst e; rw [hrd] at hq; exact Bool.noConfusion hq
  rw [upd_ne' hne h0]; exact hf q hq

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `Der::integer`**: with the reader at `d`, whose unread
bytes start at `rp` and number `rl` and don't overlap the reader, it stores
`derIntOf` of `derElement 2` of those bytes at `out`, and moves the reader
past the element. -/
theorem derInteger_correct (m : Machine) {P sp0 out d retAddr : Word}
    (env : DerCallEnv m.mem derIntegerCode P 0x5E sp0 out d 8)
    (sDR : Sep (d + 8) 8 (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = d)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, oidKeep q = true → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 →
        m'.mem x = derSliceMem (derAdvance m.mem d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
          (derElement 2 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat))) out
          (derIntOf (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)
            (memLoad32 m.mem (d + 8))
            (derElement 2 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat))) x := by
  obtain ⟨m5, Msv, S5, u5, sp5, s85, k5, frSv, slR, sl8⟩ := derCall_pro m (tag := 2) env dint_at_0
    (by decide) (by decide) dint_at_c dint_at_10 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    hpc hsp ha0 ha1
  have hrp0 := env.hrp; have hrw := env.hrw; have sRF := env.sRF
  generalize memLoad32 m.mem (d + 8) = rp at u5 hrp0 hrw sRF sDR ⊢
  generalize memLoad32 m.mem (d + 0xC) = rl at u5 hrw sRF sDR ⊢
  generalize hr : derElement 2 (memBytes m.mem rp rl.toNat) = r at u5 ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFE0 = F := ⟨_, rfl⟩
  have sFC := env.sFC; have sOF := env.sOF; have sDF := env.sDF
  rw [hF] at u5 sp5 frSv slR sl8 sFC sOF sDF sRF ⊢
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add env.hsp (k := 0xFFFFFFE0) (by decide)
  have eS : F + 0x20 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have hc5 : CodeIn (derTlvMem Msv (F + 4) d rp rl r) P derIntegerCode := fun i hi => by
    rw [derCall_outside r frSv (sFC.subR (c := i) (l := 1) (by omega)),
      derAdvance_outside r (env.sDC.subR (c := i) (l := 1) (by omega))]
    exact env.cod i hi
  have hF8 : F + 8 = F + 4 + 4 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨n6, d6, u6⟩ := u5.lw hc5 dint_at_14 (off' := 0x16) (by decide)
    (by rw [sp5]; exact aligned_add hFa (k := 4) (by decide))
  rw [sp5] at u6
  have fin : ∀ {Mx : Word → BitVec 8} {n : Machine}, Steps m5 n → St Mx P n 0x56 (reg n) →
      CodeIn Mx P derIntegerCode → (∀ x, Sep out 8 x 1 → Mx x = derTlvMem Msv (F + 4) d rp rl r x) →
      reg n sp = F → (∀ q, oidKeep q = true → reg n q = reg m5 q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ n'.mem = Mx ∧ reg n' sp = sp0 ∧
        ∀ q, oidKeep q = true → reg n' q = reg m q := by
    intro Mx n S s hc hMx rsp kq
    obtain ⟨n', c', pc', mem', sp', ra', s8', k'⟩ := derCall_epi s hc (by decide) dint_at_5a dint_at_5c hFa rsp
      (by rw [derCall_slot r sOF sDF (o := 0x1C) (by decide) hMx, slR, hra]) hret
    refine ⟨n', S5.trans (S.trans c'), pc', mem', by rw [sp', eS],
      derCall_keep hsp k5 (fun q hq h1 h8 hs => by rw [k' q h1 h8 hs, kq q hq]) (by rw [sp', eS])
        (by rw [ra', hra]) (by rw [s8', derCall_slot r sOF sDF (o := 0x18) (by decide) hMx, sl8])⟩
  -- the error exit at 0x2A, with the discriminant in `a0`
  have tail : ∀ {n : Machine}, Steps m5 n → St (derTlvMem Msv (F + 4) d rp rl r) P n 0x2A (reg n) →
      reg n 8 = out → reg n sp = F → (∀ q, oidKeep q = true → reg n q = reg m5 q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧
        n'.mem = memStore8 (memStore32 (derTlvMem Msv (F + 4) d rp rl r) out 0) (out + 4)
          ((reg n a0).extractLsb' 0 8) ∧ reg n' sp = sp0 ∧ ∀ q, oidKeep q = true → reg n' q = reg m q := by
    intro n S s r8 rsp kq
    obtain ⟨n1, d1, u1⟩ := s.sw hc5 dint_at_2a (off' := 0x2E) (by decide) (by rw [r8, add_lit_zero]; exact env.hout)
    rw [r8, add_lit_zero, s.zero] at u1
    have hc1 := CodeIn.store32 (v := 0) hc5 (env.sOC.sub (c := 0) (l := 4) (by decide) |> fun h => by
      rwa [add_ofNat_zero] at h)
    obtain ⟨n2, d2, u2⟩ := u1.sb hc1 dint_at_2e (off' := 0x32) (by decide)
    rw [r8] at u2
    have hc2 := CodeIn.store8 (v := (reg n a0).extractLsb' 0 8) hc1 (env.sOC.sub (c := 4) (l := 1) (by decide))
    obtain ⟨n3, d3, u3⟩ := u2.jump hc2 dint_at_32 (off' := 0x56) (by decide) (by
      rw [u2.pc, show P + BitVec.ofNat 32 0x32 + 0x24 = P + BitVec.ofNat 32 0x56 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P env.hP 0x56 (by decide)))
    obtain ⟨n', S', pc', mem', sp', k'⟩ := fin (S.trans (.cons d1 (.cons d2 (.single d3)))) u3.self hc2
      (fun x hx => by
        rw [memStore8_ne fun e' => hx 4 (by decide) 0 (by decide) (by rw [add_ofNat_zero]; exact e'.symm),
          memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)])
      (by rw [u3.regs]; exact rsp) (fun q hq => by rw [u3.regs]; exact kq q hq)
    exact ⟨n', S', pc', mem', sp', k'⟩
  cases r with
  | error e =>
    have h0 : memLoad32 (derTlvMem Msv (F + 4) d rp rl (.error e)) (F + 4) = 0 := derTlvMem_err0 e
    obtain ⟨n7, d7, u7⟩ := u6.taken hc5 0x26 dint_at_16 (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [h0]; rfl)
    obtain ⟨n8, d8, u8⟩ := u7.lbu hc5 dint_at_26 (off' := 0x2A) (by decide)
    have eb : derTlvMem Msv (F + 4) d rp rl (.error e)
        (upd (reg m5) a0 (memLoad32 (derTlvMem Msv (F + 4) d rp rl (.error e)) (F + 4)) sp + 8) = derErrByte e := by
      rw [upd_ne (by decide) (by decide), sp5, hF8]; exact derTlvMem_err4 e
    rw [eb] at u8
    obtain ⟨n', S', pc', mem', sp', k'⟩ := tail (.cons d6 (.cons d7 (.single d8))) u8.self
      (by rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]; exact s85)
      (by rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp5)
      (fun q hq => by
        rw [u8.regs]
        exact okeep_upd (by simp [upd]) (by decide) (okeep_upd u5.zero (by decide) (fun _ _ => rfl)) q hq)
    refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
    rw [mem', u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [tlv_zext]
    simp only [derSliceMem, derIntOf]
    exact memStore8_pt (memStore32_pt (derCall_outside _ frSv hx))
  | ok t =>
    have hb : t.header + t.len ≤ rl.toNat := by
      have := derElement_bound hr; rwa [memBytes_length] at this
    have h0 : memLoad32 (derTlvMem Msv (F + 4) d rp rl (.ok t)) (F + 4) = rp + BitVec.ofNat 32 t.header :=
      derTlvMem_ok0 t
    have hcp : (rp + BitVec.ofNat 32 t.header).toNat = rp.toNat + t.header := by
      rw [BitVec.toNat_add, ofNat_tn (by omega)]; exact Nat.mod_eq_of_lt (by omega)
    have hnz : rp + BitVec.ofNat 32 t.header ≠ 0 := fun h => by
      have := congrArg BitVec.toNat h; rw [hcp] at this; change _ = 0 at this; omega
    have hL : t.len < 2 ^ 32 := by have := rl.isLt; omega
    obtain ⟨n7, d7, u7⟩ := u6.notTaken hc5 0x18 dint_at_16 (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [h0]
      exact beq_false_of_ne hnz)
    obtain ⟨n8, d8, u8⟩ := u7.lw hc5 dint_at_18 (off' := 0x1A) (by decide)
      (by rw [upd_ne (by decide) (by decide), sp5]; exact aligned_add hFa (k := 8) (by decide))
    have elen : memLoad32 (derTlvMem Msv (F + 4) d rp rl (.ok t))
        (upd (reg m5) a0 (memLoad32 (derTlvMem Msv (F + 4) d rp rl (.ok t)) (F + 4)) sp + 8) =
        BitVec.ofNat 32 t.len := by
      rw [upd_ne (by decide) (by decide), sp5, hF8]; exact derTlvMem_ok4 t
    rw [elen, h0] at u8
    obtain ⟨n9, d9, u9⟩ := u8.aluImm hc5 dint_at_1a (off' := 0x1C) (by decide)
    have K9 : ∀ q, oidKeep q = true → reg n9 q = reg m5 q := fun q hq => by
      rw [u9.regs]
      exact okeep_upd (by simp [upd]) (by decide) (okeep_upd (by simp [upd]) (by decide)
        (okeep_upd u5.zero (by decide) (fun _ _ => rfl))) q hq
    have v9 : reg n9 a0 = rp + BitVec.ofNat 32 t.header ∧ reg n9 a1 = BitVec.ofNat 32 t.len ∧
        reg n9 a2 = 1 ∧ reg n9 8 = out ∧ reg n9 sp = F := by
      rw [u9.regs, u9.regs, u9.regs, u9.regs, u9.regs]; simp +decide only [upd_app, ↓reduceIte]
      exact ⟨trivial, trivial, trivial, s85, sp5⟩
    obtain ⟨v9a0, v9a1, v9a2, v98, v9sp⟩ := v9
    -- the `Ok` exit at 0x52
    have okx : ∀ {n : Machine}, Steps m5 n → St (derTlvMem Msv (F + 4) d rp rl (.ok t)) P n 0x52 (reg n) →
        reg n a0 = rp + BitVec.ofNat 32 t.header → reg n a1 = BitVec.ofNat 32 t.len → reg n 8 = out →
        reg n sp = F → (∀ q, oidKeep q = true → reg n q = reg m5 q) →
        ∃ n', Steps m n' ∧ n'.pc = retAddr ∧
          n'.mem = memStore32 (memStore32 (derTlvMem Msv (F + 4) d rp rl (.ok t)) out
            (rp + BitVec.ofNat 32 t.header)) (out + 4) (BitVec.ofNat 32 t.len) ∧
          reg n' sp = sp0 ∧ ∀ q, oidKeep q = true → reg n' q = reg m q := by
      intro n S s ra0 ra1 r8 rsp kq
      obtain ⟨n1, d1, u1⟩ := s.sw hc5 dint_at_52 (off' := 0x54) (by decide) (by rw [r8, add_lit_zero]; exact env.hout)
      rw [r8, add_lit_zero, ra0] at u1
      have hc1 := CodeIn.store32 (v := rp + BitVec.ofNat 32 t.header) hc5
        (env.sOC.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
      obtain ⟨n2, d2, u2⟩ := u1.sw hc1 dint_at_54 (off' := 0x56) (by decide)
        (by rw [r8]; exact aligned_add env.hout (k := 4) (by decide))
      rw [r8, ra1] at u2
      have hc2 := CodeIn.store32 (v := BitVec.ofNat 32 t.len) hc1 (env.sOC.sub (c := 4) (l := 4) (by decide))
      obtain ⟨n', S', pc', mem', sp', k'⟩ := fin (S.trans (.cons d1 (.single d2))) u2.self hc2
        (fun x hx => by
          rw [memStore32_get_sep (a := out + 4) (hx.sub (c := 4) (l := 4) (by decide)),
            memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)])
        (by rw [u2.regs]; exact rsp) (fun q hq => by rw [u2.regs]; exact kq q hq)
      exact ⟨n', S', pc', mem', sp', k'⟩
    -- the `BadDer` exit through 0x22
    have bad : ∀ {n : Machine}, Steps m5 n → St (derTlvMem Msv (F + 4) d rp rl (.ok t)) P n 0x22 (reg n) →
        reg n 8 = out → reg n sp = F → (∀ q, oidKeep q = true → reg n q = reg m5 q) →
        ∃ n', Steps m n' ∧ n'.pc = retAddr ∧
          n'.mem = memStore8 (memStore32 (derTlvMem Msv (F + 4) d rp rl (.ok t)) out 0) (out + 4) 0x14 ∧
          reg n' sp = sp0 ∧ ∀ q, oidKeep q = true → reg n' q = reg m q := by
      intro n S s r8' rsp kq
      obtain ⟨n1, d1, u1⟩ := s.aluImm hc5 dint_at_22 (off' := 0x24) (by decide)
      obtain ⟨n2, d2, u2⟩ := u1.jump hc5 dint_at_24 (off' := 0x2A) (by decide) (by
        rw [u1.pc, show P + BitVec.ofNat 32 0x24 + 0x6 = P + BitVec.ofNat 32 0x2A by rw [BitVec.add_assoc]; rfl]
        exact even_bit0 (even_at P env.hP 0x2A (by decide)))
      obtain ⟨n', S', pc', mem', sp', k'⟩ := tail (S.trans (.cons d1 (.single d2))) u2.self
        (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; exact r8')
        (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; exact rsp)
        (fun q hq => by rw [u2.regs]; exact okeep_upd s.zero (by decide) kq q hq)
      refine ⟨n', S', pc', ?_, sp', k'⟩
      rw [mem', u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [s.zero]; rfl
    have S9 : Steps m5 n9 := .cons d6 (.cons d7 (.cons d8 (.single d9)))
    have outOk : ∀ {n' : Machine}, n'.mem = memStore32 (memStore32 (derTlvMem Msv (F + 4) d rp rl (.ok t)) out
        (rp + BitVec.ofNat 32 t.header)) (out + 4) (BitVec.ofNat 32 t.len) →
        derIntOf (memBytes m.mem rp rl.toNat) rp (.ok t) = .ok (rp + BitVec.ofNat 32 t.header, BitVec.ofNat 32 t.len) →
        ∀ x, Sep F 0x20 x 1 → n'.mem x = derSliceMem (derAdvance m.mem d rp rl (.ok t)) out
          (derIntOf (memBytes m.mem rp rl.toNat) rp (.ok t)) x := fun hm hs x hx => by
      rw [hm, hs]; simp only [derSliceMem]
      exact memStore32_pt (memStore32_pt (derCall_outside _ frSv hx))
    have outBad : ∀ {n' : Machine}, n'.mem = memStore8 (memStore32 (derTlvMem Msv (F + 4) d rp rl (.ok t)) out 0)
        (out + 4) 0x14 → derIntOf (memBytes m.mem rp rl.toNat) rp (.ok t) = .error .badDer →
        ∀ x, Sep F 0x20 x 1 → n'.mem x = derSliceMem (derAdvance m.mem d rp rl (.ok t)) out
          (derIntOf (memBytes m.mem rp rl.toNat) rp (.ok t)) x := fun hm hs x hx => by
      rw [hm, hs]; simp only [derSliceMem]
      exact memStore8_pt (memStore32_pt (derCall_outside _ frSv hx))
    by_cases hl1 : t.len = 1
    · obtain ⟨n10, d10, u10⟩ := u9.self.taken hc5 0x52 dint_at_1c (by decide) (by rw [v9a1, v9a2, hl1]; rfl)
      obtain ⟨n', S', pc', mem', sp', k'⟩ := okx (S9.trans (.single d10)) u10.self (by rw [u10.regs, v9a0])
        (by rw [u10.regs, v9a1]) (by rw [u10.regs, v98]) (by rw [u10.regs, v9sp])
        (fun q hq => by rw [u10.regs]; exact K9 q hq)
      refine ⟨n', S', pc', sp', k', outOk mem' ?_⟩
      simp only [derIntOf]
      rw [ite_eq_right (by omega), ite_eq_right (fun h => absurd h.1 (by omega))]
    obtain ⟨n10, d10, u10⟩ := u9.self.notTaken hc5 0x20 dint_at_1c (by decide) (by
      rw [v9a1, v9a2]
      exact beq_false_of_ne fun h => hl1 (by
        have := congrArg BitVec.toNat h; rwa [ofNat_tn hL] at this))
    have r10 : ∀ q, reg n10 q = reg n9 q := u10.regs
    by_cases hl0 : t.len = 0
    · obtain ⟨n11, d11, u11⟩ := u10.self.notTaken hc5 0x22 dint_at_20 (by decide) (by
        rw [r10, r10, v9a1, u9.self.zero, hl0]; rfl)
      obtain ⟨n', S', pc', mem', sp', k'⟩ := bad (S9.trans (.cons d10 (.single d11))) u11.self
        (by rw [u11.regs, r10, v98]) (by rw [u11.regs, r10, v9sp])
        (fun q hq => by rw [u11.regs, r10]; exact K9 q hq)
      refine ⟨n', S', pc', sp', k', outBad mem' ?_⟩
      simp only [derIntOf, hl0, ↓reduceIte]
    have hl2 : 2 ≤ t.len := by omega
    obtain ⟨n11, d11, u11⟩ := u10.self.taken hc5 0x34 dint_at_20 (by decide) (by
      rw [r10, r10, v9a1, u9.self.zero]
      exact bne_iff_ne.mpr fun h => hl0 (by have := congrArg BitVec.toNat h; rwa [ofNat_tn hL] at this))
    have r11 : ∀ q, reg n11 q = reg n9 q := fun q => by rw [u11.regs, r10]
    have eb0 : derTlvMem Msv (F + 4) d rp rl (.ok t) (rp + BitVec.ofNat 32 t.header) =
        m.mem (rp + BitVec.ofNat 32 t.header) := by
      rw [derCall_outside _ frSv (sRF.symm.subR (c := t.header) (l := 1) (by omega)),
        derAdvance_outside _ (sDR.subR (c := t.header) (l := 1) (by omega))]
    have eA1 : rp + BitVec.ofNat 32 t.header + 1 = rp + BitVec.ofNat 32 (t.header + 1) := by
      rw [BitVec.add_assoc, show (1 : Word) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat]
    have eb1 : derTlvMem Msv (F + 4) d rp rl (.ok t) (rp + BitVec.ofNat 32 t.header + 1) =
        m.mem (rp + BitVec.ofNat 32 (t.header + 1)) := by
      rw [eA1, derCall_outside _ frSv (sRF.symm.subR (c := t.header + 1) (l := 1) (by omega)),
        derAdvance_outside _ (sDR.subR (c := t.header + 1) (l := 1) (by omega))]
    have hg0 : (memBytes m.mem rp rl.toNat).getD t.header 0 = (m.mem (rp + BitVec.ofNat 32 t.header)).toNat :=
      memBytes_getD (by omega)
    have hg1 : (memBytes m.mem rp rl.toNat).getD (t.header + 1) 0 =
        (m.mem (rp + BitVec.ofNat 32 (t.header + 1))).toNat := memBytes_getD (by omega)
    obtain ⟨n12, d12, u12⟩ := u11.self.lbu hc5 dint_at_34 (off' := 0x38) (by decide)
    rw [r11, v9a0, add_lit_zero, eb0] at u12
    generalize hB0 : m.mem (rp + BitVec.ofNat 32 t.header) = b0 at u12 hg0
    generalize hB1 : m.mem (rp + BitVec.ofNat 32 (t.header + 1)) = b1 at eb1 hg1
    obtain ⟨n13, d13, u13⟩ := u12.self.aluImm hc5 dint_at_38 (off' := 0x3C) (by decide)
    have r12 : ∀ q, q ≠ a2 → reg n12 q = reg n9 q := fun q h => by
      rw [u12.regs, upd_ne' h u11.self.zero, r11]
    have r13 : ∀ q, q ≠ a2 → q ≠ a3 → reg n13 q = reg n9 q := fun q h2 h3 => by
      rw [u13.regs, upd_ne' h3 u12.self.zero, r12 q h2]
    have K13 : ∀ q, oidKeep q = true → reg n13 q = reg m5 q := fun q hq => by
      rw [r13 q (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide))]
      exact K9 q hq
    have v13a3 : reg n13 a3 = aluEval .add (b0.zeroExtend 32) 0xFFFFFF01 := by
      rw [u13.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u12.regs]; simp +decide only [upd_app, ↓reduceIte]
    have v13a2 : reg n13 a2 = b0.zeroExtend 32 := by
      rw [u13.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u12.regs]; simp +decide only [upd_app, ↓reduceIte]
    have z13 : reg n13 0 = 0 := u13.self.zero
    have S13 : Steps m5 n13 := S9.trans (.cons d10 (.cons d11 (.cons d12 (.single d13))))
    by_cases hff : b0.toNat = 255
    · obtain ⟨n14, d14, u14⟩ := u13.self.taken hc5 0x4A dint_at_3c (by decide) (by
        rw [v13a3, z13, int_ff, hff]; rfl)
      obtain ⟨n15, d15, u15⟩ := u14.self.lb hc5 dint_at_4a (off' := 0x4E) (by decide)
      rw [u14.regs, r13 a0 (by decide) (by decide), v9a0, eb1] at u15
      have r15 : ∀ q, q ≠ a2 → q ≠ a3 → reg n15 q = reg n9 q := fun q h2 h3 => by
        rw [u15.regs, upd_ne' h2 u14.self.zero, u14.regs, r13 q h2 h3]
      have K15 : ∀ q, oidKeep q = true → reg n15 q = reg m5 q := fun q hq => by
        rw [r15 q (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide))]
        exact K9 q hq
      have v15 : reg n15 a2 = b1.signExtend 32 := by rw [u15.regs]; simp +decide only [upd_app, ↓reduceIte]
      have z15 : reg n15 0 = 0 := u15.self.zero
      by_cases hn : 128 ≤ b1.toNat
      · obtain ⟨n16, d16, u16⟩ := u15.self.taken hc5 0x22 dint_at_4e (by decide) (by
          rw [v15, z15, int_blt]; exact decide_eq_true hn)
        obtain ⟨n', S', pc', mem', sp', k'⟩ := bad (S13.trans (.cons d14 (.cons d15 (.single d16)))) u16.self
          (by rw [u16.regs, r15 8 (by decide) (by decide), v98]) (by rw [u16.regs, r15 sp (by decide) (by decide), v9sp])
          (fun q hq => by rw [u16.regs]; exact K15 q hq)
        refine ⟨n', S', pc', sp', k', outBad mem' ?_⟩
        simp only [derIntOf]
        rw [ite_eq_right hl0, ite_eq_left ⟨hl2, .inr ⟨by rw [hg0]; exact hff, by rw [hg1]; exact hn⟩⟩]
      · obtain ⟨n16, d16, u16⟩ := u15.self.notTaken hc5 0x52 dint_at_4e (by decide) (by
          rw [v15, z15, int_blt]; exact decide_eq_false hn)
        obtain ⟨n', S', pc', mem', sp', k'⟩ := okx (S13.trans (.cons d14 (.cons d15 (.single d16)))) u16.self
          (by rw [u16.regs, r15 a0 (by decide) (by decide), v9a0])
          (by rw [u16.regs, r15 a1 (by decide) (by decide), v9a1])
          (by rw [u16.regs, r15 8 (by decide) (by decide), v98]) (by rw [u16.regs, r15 sp (by decide) (by decide), v9sp])
          (fun q hq => by rw [u16.regs]; exact K15 q hq)
        refine ⟨n', S', pc', sp', k', outOk mem' ?_⟩
        simp only [derIntOf]
        rw [ite_eq_right hl0, ite_eq_right fun ⟨_, h⟩ => h.elim (fun ⟨h1, _⟩ => by rw [hg0] at h1; omega)
          (fun ⟨_, h2⟩ => hn (by rw [hg1] at h2; exact h2))]
    obtain ⟨n14, d14, u14⟩ := u13.self.notTaken hc5 0x3E dint_at_3c (by decide) (by
      rw [v13a3, z13, int_ff]; exact decide_eq_false hff)
    by_cases hz : b0.toNat = 0
    · obtain ⟨n15, d15, u15⟩ := u14.self.notTaken hc5 0x40 dint_at_3e (by decide) (by
        rw [u14.regs, u14.regs, v13a2, z13, int_nz, hz]; rfl)
      obtain ⟨n16, d16, u16⟩ := u15.self.lb hc5 dint_at_40 (off' := 0x44) (by decide)
      rw [u15.regs, u14.regs, r13 a0 (by decide) (by decide), v9a0, eb1] at u16
      have r16 : ∀ q, q ≠ a2 → q ≠ a3 → reg n16 q = reg n9 q := fun q h2 h3 => by
        rw [u16.regs, upd_ne' h2 u15.self.zero, u15.regs, u14.regs, r13 q h2 h3]
      have K16 : ∀ q, oidKeep q = true → reg n16 q = reg m5 q := fun q hq => by
        rw [r16 q (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide))]
        exact K9 q hq
      have v16 : reg n16 a2 = b1.signExtend 32 := by rw [u16.regs]; simp +decide only [upd_app, ↓reduceIte]
      have z16 : reg n16 0 = 0 := u16.self.zero
      by_cases hp : b1.toNat < 128
      · obtain ⟨n17, d17, u17⟩ := u16.self.taken hc5 0x22 dint_at_44 (by decide) (by
          rw [v16, z16, int_bge]; exact decide_eq_true hp)
        obtain ⟨n', S', pc', mem', sp', k'⟩ := bad
          (S13.trans (.cons d14 (.cons d15 (.cons d16 (.single d17))))) u17.self
          (by rw [u17.regs, r16 8 (by decide) (by decide), v98]) (by rw [u17.regs, r16 sp (by decide) (by decide), v9sp])
          (fun q hq => by rw [u17.regs]; exact K16 q hq)
        refine ⟨n', S', pc', sp', k', outBad mem' ?_⟩
        simp only [derIntOf]
        rw [ite_eq_right hl0, ite_eq_left ⟨hl2, .inl ⟨by rw [hg0]; exact hz, by rw [hg1]; exact hp⟩⟩]
      · obtain ⟨n17, d17, u17⟩ := u16.self.notTaken hc5 0x48 dint_at_44 (by decide) (by
          rw [v16, z16, int_bge]; exact decide_eq_false hp)
        obtain ⟨n18, d18, u18⟩ := u17.self.jump hc5 dint_at_48 (off' := 0x52) (by decide) (by
          rw [u17.pc, show P + BitVec.ofNat 32 0x48 + 0xA = P + BitVec.ofNat 32 0x52 by rw [BitVec.add_assoc]; rfl]
          exact even_bit0 (even_at P env.hP 0x52 (by decide)))
        have r18 : ∀ q, reg n18 q = reg n16 q := fun q => by rw [u18.regs, u17.regs]
        obtain ⟨n', S', pc', mem', sp', k'⟩ := okx
          (S13.trans (.cons d14 (.cons d15 (.cons d16 (.cons d17 (.single d18)))))) u18.self
          (by rw [r18, r16 a0 (by decide) (by decide), v9a0]) (by rw [r18, r16 a1 (by decide) (by decide), v9a1])
          (by rw [r18, r16 8 (by decide) (by decide), v98]) (by rw [r18, r16 sp (by decide) (by decide), v9sp])
          (fun q hq => by rw [r18]; exact K16 q hq)
        refine ⟨n', S', pc', sp', k', outOk mem' ?_⟩
        simp only [derIntOf]
        rw [ite_eq_right hl0, ite_eq_right fun ⟨_, h⟩ => h.elim (fun ⟨_, h2⟩ => hp (by rw [hg1] at h2; exact h2))
          (fun ⟨h1, _⟩ => by rw [hg0] at h1; omega)]
    · obtain ⟨n15, d15, u15⟩ := u14.self.taken hc5 0x52 dint_at_3e (by decide) (by
        rw [u14.regs, u14.regs, v13a2, z13, int_nz]
        simp only [hz, decide_false, Bool.not_false])
      have r15 : ∀ q, reg n15 q = reg n13 q := fun q => by rw [u15.regs, u14.regs]
      obtain ⟨n', S', pc', mem', sp', k'⟩ := okx (S13.trans (.cons d14 (.single d15))) u15.self
        (by rw [r15, r13 a0 (by decide) (by decide), v9a0]) (by rw [r15, r13 a1 (by decide) (by decide), v9a1])
        (by rw [r15, r13 8 (by decide) (by decide), v98]) (by rw [r15, r13 sp (by decide) (by decide), v9sp])
        (fun q hq => by rw [r15]; exact K13 q hq)
      refine ⟨n', S', pc', sp', k', outOk mem' ?_⟩
      simp only [derIntOf]
      rw [ite_eq_right hl0, ite_eq_right fun ⟨_, h⟩ => h.elim (fun ⟨h1, _⟩ => hz (by rw [hg0] at h1; exact h1))
        (fun ⟨h1, _⟩ => hff (by rw [hg0] at h1; exact h1))]

theorem memLoad32_val (M : Word → BitVec 8) (a : Word) :
    (memLoad32 M a).toNat =
      (M a).toNat + (M (a + 1)).toNat * 2 ^ 8 + (M (a + 2)).toNat * 2 ^ 16 + (M (a + 3)).toNat * 2 ^ 24 := by
  unfold memLoad32
  have h0 := (M a).isLt; have h1 := (M (a + 1)).isLt; have h2 := (M (a + 2)).isLt
  simp only [BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt h0, ← Nat.shiftLeft_add_eq_or_of_lt h1,
    ← Nat.shiftLeft_add_eq_or_of_lt h2]
  simp only [Nat.shiftLeft_eq]
  omega

theorem bt_len (M : Word → BitVec 8) (a : Word) :
    aluEval .or (aluEval .or ((M a).zeroExtend 32) (aluEval .sll ((M (a + 3)).zeroExtend 32) 0x18))
      (aluEval .or (aluEval .sll ((M (a + 1)).zeroExtend 32) 0x8) (aluEval .sll ((M (a + 2)).zeroExtend 32) 0x10)) =
    memLoad32 M a := by
  simp only [ev_or, ev_sll8, ev_sll16, ev_sll24]
  rw [BitVec.or_assoc, ← BitVec.or_assoc ((M (a + 3)).zeroExtend 32 <<< 24),
    BitVec.or_comm ((M (a + 3)).zeroExtend 32 <<< 24) ((M (a + 1)).zeroExtend 32 <<< 8),
    BitVec.or_assoc ((M (a + 1)).zeroExtend 32 <<< 8), ← BitVec.or_assoc ((M a).zeroExtend 32), be32_assemble]
  apply BitVec.eq_of_toNat_eq
  have := (M a).isLt; have := (M (a + 1)).isLt; have := (M (a + 2)).isLt; have := (M (a + 3)).isLt
  rw [BitVec.toNat_ofNat, memLoad32_val, Nat.mod_eq_of_lt (by omega)]
  omega

theorem bt_res : ∀ b : BitVec 8,
    aluEval .or (aluEval .add (aluEval .sltu 0 (aluEval .add (b.zeroExtend 32) 0xFFFFFF01)) 0xFFFFFFFF) 0x14 =
      if b.toNat = 255 then 0xFFFFFFFF else 0x14 := by decide

/-- `Der::boolean_true`'s moves from 0x6 to the call at 0xE: the reader to
`a1`, the result's address to `a0`, the tag to `a2`, and 1 to `s0`. -/
def dbtMov : List BInstr :=
  [.alu .add a1 x0 a0, .aluImm .add a0 sp 0x4, .aluImm .add a2 x0 0x1, .aluImm .add (8 : Fin 32) x0 0x1]

/-- From 0x1E to 0x36: the element's content length from the frame's bytes. -/
def dbtLen : List BInstr :=
  [.lbu a2 sp 0x9, .lbu a3 sp 0xA, .lbu a4 sp 0xB, .aluImm .sll a2 a2 0x8, .aluImm .sll a3 a3 0x10,
   .aluImm .sll a4 a4 0x18, .alu .or a2 a2 a3, .alu .or a0 a0 a4, .alu .or a0 a0 a2]

/-- From 0x3A to 0x4C: `Ok(())` for a content byte of 0xFF, `BadDer` for
any other. -/
def dbtVal : List BInstr :=
  [.lbu a0 a1 0x0, .aluImm .add a0 a0 0xFFFFFF01, .alu .sltu a0 x0 a0, .aluImm .add a0 a0 0xFFFFFFFF,
   .aluImm .or a0 a0 0x14]

section
set_option maxRecDepth 20000
theorem dbtSave_end : blockEnd derBooleanTrueCode 2 (saveBlock dcPs) = some 6 := by decide
theorem dbtMov_end : blockEnd derBooleanTrueCode 6 dbtMov = some 0xE := by decide
theorem dbtLen_end : blockEnd derBooleanTrueCode 0x1E dbtLen = some 0x36 := by decide
theorem dbtVal_end : blockEnd derBooleanTrueCode 0x3A dbtVal = some 0x4C := by decide
end

/-- `Der::boolean_true`'s result, for the unread bytes `L`: the contents
must be the one byte 0xFF, DER's `TRUE`. -/
def derBoolOf (L : Bytes) : Except DerError DerTlv → Except DerError Unit
  | .error e => .error e
  | .ok t => if t.len = 1 ∧ L.getD t.header 0 = 0xFF then .ok () else .error .badDer

/-- How the compiled code returns `Result<(), Error>` in `a0`: the error's
discriminant, or a low byte of 0xFF for `Ok(())`, which is what its callers
test. -/
def derUnitWord : Except DerError Unit → Word
  | .ok () => 0xFFFFFFFF
  | .error e => (derErrByte e).zeroExtend 32

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- `Der::boolean_true`'s prologue and call, as `derCall_pro` for its moves:
the reader comes in `a0`, and `s0` holds 1. -/
theorem derBool_pro (m : Machine) {P sp0 d : Word}
    (env : DerCallEnv m.mem derBooleanTrueCode P 0xFFFFCE92 sp0 d d 0)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = d) :
    ∃ m5 Msv, Steps m m5 ∧
      St (derTlvMem Msv (sp0 + 0xFFFFFFE0 + 4) d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
        (derElement 1 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)))
        P m5 0x16 (reg m5) ∧
      reg m5 sp = sp0 + 0xFFFFFFE0 ∧ reg m5 8 = 1 ∧
      (∀ q, tlvClob q = false → q ≠ ra → q ≠ sp → q ≠ 8 → q ≠ a0 → reg m5 q = reg m q) ∧
      (∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 → Msv x = m.mem x) ∧
      memLoad32 Msv (sp0 + 0xFFFFFFE0 + 0x1C) = reg m ra ∧ memLoad32 Msv (sp0 + 0xFFFFFFE0 + 0x18) = reg m 8 := by
  obtain ⟨rp, hrp⟩ : ∃ rp, memLoad32 m.mem (d + 8) = rp := ⟨_, rfl⟩
  obtain ⟨rl, hrl⟩ : ∃ rl, memLoad32 m.mem (d + 0xC) = rl := ⟨_, rfl⟩
  have sRF := env.sRF
  rw [hrp, hrl] at sRF ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFE0 = F := ⟨_, rfl⟩
  have sFC := env.sFC; have sFE := env.sFE; have sFT := env.sFT; have sDF := env.sDF
  rw [hF] at sFC sFE sFT sDF sRF ⊢
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add env.hsp (k := 0xFFFFFFE0) (by decide)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep F 0x20 b code'.length → (∀ x, Sep F 0x20 x 1 → M' x = m.mem x) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod dbt_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock dcPs) u1 env.cod dbtSave_end (saveBlock_ok _ dcPs _ fun p hp => by
    rw [sp1]
    simp only [dcPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨fr_al' hFa (by decide), frm_sep' sFC (by decide)⟩
    · exact ⟨fr_al' hFa (by decide), frm_sep' sFC (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0)) dcPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep F 0x20 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside dcPs fun p hp => by
      simp only [dcPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact frm_sep' hx (by decide)
      · exact frm_sep' hx (by decide)
  have hslv : ∀ r o, (r, o) ∈ dcPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [dcPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ r, reg m2 r = upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) r := u2.regs
  obtain ⟨m3, c3, u3⟩ := St.block dbtMov u2.self (cIn env.cod sFC frSv) dbtMov_end
    (by simp [BlockOk, BInstr.ok, dbtMov])
  simp only [runBlock, BInstr.run, dbtMov] at u3
  have g3 : ∀ r, reg m3 r = _ := u3.regs
  have v3 : reg m3 sp = F ∧ reg m3 8 = 1 ∧ reg m3 a0 = F + 4 ∧ reg m3 a2 = 1 ∧ reg m3 a1 = d := by
    simp +decide only [g3, upd_app, ↓reduceIte, r2]
    simp only [ev_add, hsp, hF, ha0, zw]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl
  obtain ⟨v3sp, v38, v3a0, v3a2, v3a1⟩ := v3
  have k3 : ∀ q : Fin 32, q ≠ sp → q ≠ 8 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m3 q = reg m q :=
    fun q h1 h2 h3 h4 h5 => by
      rw [g3]
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz.symm
      simp only [upd_app, h0, h2, h3, h4, h5, ite_false]; rw [r2]; simp only [upd_app, h0, h1, ite_false]
  have hcS := cIn env.cod sFC frSv
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.self.callRa hcS dbt_at_e dbt_at_12
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) env.hE
  have r4 := PEnv.reg1 regs4 u3.self.zero
  have hF4 : F + 4 = F + BitVec.ofNat 32 4 := rfl
  obtain ⟨m5, c5, pc5, mem5, k5⟩ := derElement_correct m4 (tag := 1) env.hE
    (by rw [mem4]; exact cIn env.elem sFE frSv) (by rw [mem4]; exact cIn env.tlv sFT frSv) pc4
    (by rw [r4 a0 (by decide), v3a0]) (by rw [r4 a1 (by decide), v3a1]) (by rw [r4 a2 (by decide), v3a2]; rfl)
    (by decide) (by rw [regs4]; simp +decide [upd]) (even_clear _ (even_at P env.hP (0xE + 8) (by decide)))
    (by rw [hF4]; exact aligned_add hFa (by decide)) env.hd
    (by rw [hF4]; exact sFE.sub (by decide)) (by rw [hF4]; exact sFT.sub (by decide)) env.sDT
  rw [mem4] at mem5
  have eD8 : memLoad32 Msv (d + 8) = rp := by
    rw [← hrp]; exact memLoad32_congr fun j hj => frSv _ (sDF.symm.subR (c := j) (l := 1) (by omega))
  have eDC : memLoad32 Msv (d + 0xC) = rl := by
    rw [← hrl]; exact memLoad32_congr fun j hj => frSv _ (by
      rw [show d + 0xC = d + 8 + BitVec.ofNat 32 4 by rw [BitVec.add_assoc]; rfl, add_ofNat_assoc]
      exact sDF.symm.subR (by omega))
  rw [eD8, eDC] at mem5
  have eL : memBytes Msv rp rl.toNat = memBytes m.mem rp rl.toNat :=
    memBytes_congr fun i hi => frSv _ (sRF.symm.subR (c := i) (l := 1) (by omega))
  rw [eL] at mem5
  refine ⟨m5, Msv, .cons d1 (c2.trans (c3.trans (c4.trans c5))), ⟨by rw [pc5], mem5, fun _ => rfl⟩, ?_, ?_,
    fun q hq h1 h2 h3 h4 => ?_, frSv, hslv ra 0x1C (by decide), hslv 8 0x18 (by decide)⟩
  · rw [k5 sp (by decide), r4 sp (by decide), v3sp]
  · rw [k5 8 (by decide), r4 8 (by decide), v38]
  · have ha1 : q ≠ a1 := fun e => by subst e; exact absurd hq (by decide)
    have ha2 : q ≠ a2 := fun e => by subst e; exact absurd hq (by decide)
    rw [k5 q hq, r4 q h1, k3 q h2 h3 h4 ha1 ha2]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The compiled `Der::boolean_true`**: with the reader at `d`, whose
unread bytes start at `rp` and number `rl` and don't overlap the reader, it
returns `derBoolOf` of `derElement 1` of those bytes in `a0` and moves the
reader past the element. It has no result in memory, so its environment's
result is the reader itself with no bytes. -/
theorem derBooleanTrue_correct (m : Machine) {P sp0 d retAddr : Word}
    (env : DerCallEnv m.mem derBooleanTrueCode P 0xFFFFCE92 sp0 d d 0)
    (sDR : Sep (d + 8) 8 (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = d)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, oidKeep q = true → reg m' q = reg m q) ∧
      reg m' a0 = derUnitWord (derBoolOf (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)
        (derElement 1 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat))) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 →
        m'.mem x = derAdvance m.mem d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
          (derElement 1 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)) x := by
  obtain ⟨m5, Msv, S5, u5, sp5, s85, k5, frSv, slR, sl8⟩ := derBool_pro m env hpc hsp ha0
  have hrp0 := env.hrp; have hrw := env.hrw; have sRF := env.sRF
  generalize memLoad32 m.mem (d + 8) = rp at u5 hrp0 hrw sRF sDR ⊢
  generalize memLoad32 m.mem (d + 0xC) = rl at u5 hrw sRF sDR ⊢
  generalize hr : derElement 1 (memBytes m.mem rp rl.toNat) = r at u5 ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFE0 = F := ⟨_, rfl⟩
  have sFC := env.sFC; have sOF := env.sOF; have sDF := env.sDF
  rw [hF] at u5 sp5 frSv slR sl8 sFC sOF sDF sRF ⊢
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add env.hsp (k := 0xFFFFFFE0) (by decide)
  have eS : F + 0x20 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have hc5 : CodeIn (derTlvMem Msv (F + 4) d rp rl r) P derBooleanTrueCode := fun i hi => by
    rw [derCall_outside r frSv (sFC.subR (c := i) (l := 1) (by omega)),
      derAdvance_outside r (env.sDC.subR (c := i) (l := 1) (by omega))]
    exact env.cod i hi
  have hF8 : F + 8 = F + 4 + 4 := by rw [BitVec.add_assoc]; rfl
  have fin : ∀ {n : Machine}, Steps m5 n → St (derTlvMem Msv (F + 4) d rp rl r) P n 0x50 (reg n) →
      reg n sp = F → (∀ q, oidKeep q = true → reg n q = reg m5 q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ reg n' sp = sp0 ∧ (∀ q, oidKeep q = true → reg n' q = reg m q) ∧
        reg n' a0 = reg n a0 ∧ ∀ x, Sep F 0x20 x 1 → n'.mem x = derAdvance m.mem d rp rl r x := by
    intro n S s rsp kq
    have hMx : ∀ x, Sep d 0 x 1 → derTlvMem Msv (F + 4) d rp rl r x = derTlvMem Msv (F + 4) d rp rl r x :=
      fun _ _ => rfl
    obtain ⟨n', c', pc', mem', sp', ra', s8', k'⟩ := derCall_epi s hc5 (by decide) dbt_at_54 dbt_at_56 hFa rsp
      (by rw [derCall_slot r sOF sDF (o := 0x1C) (by decide) hMx, slR, hra]) hret
    refine ⟨n', S5.trans (S.trans c'), pc', by rw [sp', eS],
      derCall_keep hsp k5 (fun q hq h1 h8 hs => by rw [k' q h1 h8 hs, kq q hq]) (by rw [sp', eS])
        (by rw [ra', hra]) (by rw [s8', derCall_slot r sOF sDF (o := 0x18) (by decide) hMx, sl8]),
      k' a0 (by decide) (by decide) (by decide), fun x hx => by rw [mem']; exact derCall_outside r frSv hx⟩
  obtain ⟨n6, d6, u6⟩ := u5.lw hc5 dbt_at_16 (off' := 0x18) (by decide)
    (by rw [sp5]; exact aligned_add hFa (k := 4) (by decide))
  obtain ⟨n7, d7, u7⟩ := u6.self.lbu hc5 dbt_at_18 (off' := 0x1C) (by decide)
  have r7 : ∀ q, q ≠ a0 → q ≠ a1 → reg n7 q = reg m5 q := fun q h0 h1 => by
    rw [u7.regs, upd_ne' h0 u6.self.zero, u6.regs, upd_ne' h1 u5.zero]
  have v7a1 : reg n7 a1 = memLoad32 (derTlvMem Msv (F + 4) d rp rl r) (F + 4) := by
    rw [u7.regs, upd_ne' (by decide) u6.self.zero, u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5]
  have v7a0 : reg n7 a0 = (derTlvMem Msv (F + 4) d rp rl r (F + 8)).zeroExtend 32 := by
    rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u6.regs, upd_ne' (by decide) u5.zero, sp5]
  have K7 : ∀ q, oidKeep q = true → reg n7 q = reg m5 q := fun q hq =>
    r7 q (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide))
  have S7 : Steps m5 n7 := .cons d6 (.single d7)
  cases r with
  | error e =>
    obtain ⟨n8, d8, u8⟩ := u7.self.taken hc5 0x50 dbt_at_1c (by decide) (by
      rw [v7a1, derTlvMem_err0, u7.self.zero]; rfl)
    obtain ⟨n', S', pc', sp', k', a0', mem'⟩ := fin (S7.trans (.single d8)) u8.self
      (by rw [u8.regs, r7 sp (by decide) (by decide), sp5]) (fun q hq => by rw [u8.regs]; exact K7 q hq)
    refine ⟨n', S', pc', sp', k', ?_, mem'⟩
    rw [a0', u8.regs, v7a0, hF8, derTlvMem_err4]; rfl
  | ok t =>
    have hb : t.header + t.len ≤ rl.toNat := by
      have := derElement_bound hr; rwa [memBytes_length] at this
    have hcp : (rp + BitVec.ofNat 32 t.header).toNat = rp.toNat + t.header := by
      rw [BitVec.toNat_add, ofNat_tn (by omega)]; exact Nat.mod_eq_of_lt (by omega)
    have hnz : rp + BitVec.ofNat 32 t.header ≠ 0 := fun h => by
      have := congrArg BitVec.toNat h; rw [hcp] at this; change _ = 0 at this; omega
    have hL : t.len < 2 ^ 32 := by have := rl.isLt; omega
    obtain ⟨n8, d8, u8⟩ := u7.self.notTaken hc5 0x1E dbt_at_1c (by decide) (by
      rw [v7a1, derTlvMem_ok0, u7.self.zero]; exact beq_false_of_ne hnz)
    obtain ⟨n9, c9, u9⟩ := St.block dbtLen u8.self hc5 dbtLen_end (by simp [BlockOk, BInstr.ok, dbtLen])
    simp only [runBlock, BInstr.run, dbtLen] at u9
    have v9a0 : reg n9 a0 = BitVec.ofNat 32 t.len := by
      rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]
      simp only [u8.regs]; rw [v7a0, r7 sp (by decide) (by decide), sp5]
      rw [show F + 9 = F + 8 + 1 by rw [BitVec.add_assoc]; rfl, show F + 0xA = F + 8 + 2 by rw [BitVec.add_assoc]; rfl,
        show F + 0xB = F + 8 + 3 by rw [BitVec.add_assoc]; rfl, bt_len, hF8, derTlvMem_ok4]
    have r9 : ∀ q, q.val ∉ [10, 12, 13, 14] → reg n9 q = reg n7 q := fun q hq => by
      rw [u9.regs]
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd]; exact u7.self.zero.symm
      have n10 : q ≠ a0 := fun e => hq (by rw [e]; decide)
      have n12 : q ≠ a2 := fun e => hq (by rw [e]; decide)
      have n13 : q ≠ a3 := fun e => hq (by rw [e]; decide)
      have n14 : q ≠ a4 := fun e => hq (by rw [e]; decide)
      simp only [upd_app, h0, n10, n12, n13, n14, ite_false]; rw [u8.regs]
    have hkk : ∀ q : Fin 32, oidKeep q = true → q.val ∉ [10, 12, 13, 14] := by decide
    have S9 : Steps m5 n9 := S7.trans (.cons d8 c9)
    by_cases hl1 : t.len = 1
    · obtain ⟨n10, d10, u10⟩ := u9.self.notTaken hc5 0x3A dbt_at_36 (by decide) (by
        rw [v9a0, r9 8 (by decide), r7 8 (by decide) (by decide), s85, hl1]; rfl)
      obtain ⟨n11, c11, u11⟩ := St.block dbtVal u10.self hc5 dbtVal_end (by simp [BlockOk, BInstr.ok, dbtVal])
      simp only [runBlock, BInstr.run, dbtVal] at u11
      obtain ⟨n12, d12, u12⟩ := u11.jump hc5 dbt_at_4c (off' := 0x50) (by decide) (by
        rw [u11.pc, show P + BitVec.ofNat 32 0x4C + 0x4 = P + BitVec.ofNat 32 0x50 by rw [BitVec.add_assoc]; rfl]
        exact even_bit0 (even_at P env.hP 0x50 (by decide)))
      have eb : derTlvMem Msv (F + 4) d rp rl (.ok t) (reg n10 a1 + 0) = m.mem (rp + BitVec.ofNat 32 t.header) := by
        rw [u10.regs, r9 a1 (by decide), v7a1, derTlvMem_ok0, add_lit_zero,
          derCall_outside _ frSv (sRF.symm.subR (c := t.header) (l := 1) (by omega)),
          derAdvance_outside _ (sDR.subR (c := t.header) (l := 1) (by omega))]
      have hg0 : (memBytes m.mem rp rl.toNat).getD t.header 0 = (m.mem (rp + BitVec.ofNat 32 t.header)).toNat :=
        memBytes_getD (by omega)
      obtain ⟨n', S', pc', sp', k', a0', mem'⟩ := fin (S9.trans (.cons d10 (c11.trans (.single d12)))) u12.self
        (by rw [u12.regs]; simp +decide only [upd_app, ↓reduceIte]
            rw [u10.regs, r9 sp (by decide), r7 sp (by decide) (by decide), sp5])
        (fun q hq => by
          rw [u12.regs]
          have h0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
          rw [updz (by simp [upd]) h0, updz (by simp [upd]) h0, updz (by simp [upd]) h0, updz (by simp [upd]) h0,
            updz u10.self.zero h0, u10.regs, r9 q (hkk q hq)]
          exact K7 q hq)
      refine ⟨n', S', pc', sp', k', ?_, mem'⟩
      rw [a0', u12.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [eb, bt_res]
      simp only [derBoolOf, hl1, hg0, true_and]
      split <;> rfl
    · obtain ⟨n10, d10, u10⟩ := u9.self.taken hc5 0x4E dbt_at_36 (by decide) (by
        rw [v9a0, r9 8 (by decide), r7 8 (by decide) (by decide), s85]
        exact bne_iff_ne.mpr fun h => hl1 (by have := congrArg BitVec.toNat h; rwa [ofNat_tn hL] at this))
      obtain ⟨n11, d11, u11⟩ := u10.self.aluImm hc5 dbt_at_4e (off' := 0x50) (by decide)
      obtain ⟨n', S', pc', sp', k', a0', mem'⟩ := fin (S9.trans (.cons d10 (.single d11))) u11.self
        (by rw [u11.regs, upd_ne' (by decide) u10.self.zero, u10.regs, r9 sp (by decide),
            r7 sp (by decide) (by decide), sp5])
        (fun q hq => by
          rw [u11.regs, upd_ne' (fun e => by subst e; exact absurd hq (by decide)) u10.self.zero, u10.regs,
            r9 q (hkk q hq)]
          exact K7 q hq)
      refine ⟨n', S', pc', sp', k', ?_, mem'⟩
      rw [a0', u11.regs]; simp +decide only [upd_app, ↓reduceIte]
      simp only [derBoolOf, hl1, false_and, ↓reduceIte]; rfl

end C3.RV32
