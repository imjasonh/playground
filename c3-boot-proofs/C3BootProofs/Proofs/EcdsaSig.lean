import C3BootProofs.Proofs.DerScalar
import C3BootProofs.Proofs.DerNested

/-!
# `der::ecdsa_signature::<48>`, as compiled

`der::ecdsa_signature::<48>` reads a DER `SEQUENCE` that must fill its
input, then two 48-byte scalars `r` and `s` through the proved
`der::scalar::<48>`, and fails with `TrailingBytes` when bytes follow `s`
in the sequence. Its result is `Result<([u8; 48], [u8; 48]), Error>`: a tag
byte, then `r` at offset 1 and `s` at offset 49, or the error byte at
offset 1.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem es_at_0 : fetchRel ecdsaSignature48Code 0x0 = some (.aluImm .add sp sp 0xFFFFFF30, 2) := by decide
theorem es_at_2 : fetchRel ecdsaSignature48Code 0x2 = some (.store .sw sp ra 0xCC, 2) := by decide
theorem es_at_4 : fetchRel ecdsaSignature48Code 0x4 = some (.store .sw sp (8 : Fin 32) 0xC8, 2) := by decide
theorem es_at_6 : fetchRel ecdsaSignature48Code 0x6 = some (.store .sw sp (9 : Fin 32) 0xC4, 2) := by decide
theorem es_at_8 : fetchRel ecdsaSignature48Code 0x8 = some (.store .sw sp (18 : Fin 32) 0xC0, 2) := by decide
theorem es_at_a : fetchRel ecdsaSignature48Code 0xA = some (.store .sw sp (19 : Fin 32) 0xBC, 2) := by decide
theorem es_at_c : fetchRel ecdsaSignature48Code 0xC = some (.store .sw sp (20 : Fin 32) 0xB8, 2) := by decide
theorem es_at_e : fetchRel ecdsaSignature48Code 0xE = some (.alu .add (20 : Fin 32) x0 a0, 2) := by decide
theorem es_at_10 : fetchRel ecdsaSignature48Code 0x10 = some (.store .sw sp a1 0x8, 2) := by decide
theorem es_at_12 : fetchRel ecdsaSignature48Code 0x12 = some (.store .sw sp a2 0xC, 2) := by decide
theorem es_at_14 : fetchRel ecdsaSignature48Code 0x14 = some (.store .sw sp a1 0x10, 2) := by decide
theorem es_at_16 : fetchRel ecdsaSignature48Code 0x16 = some (.store .sw sp a2 0x14, 2) := by decide
theorem es_at_18 : fetchRel ecdsaSignature48Code 0x18 = some (.aluImm .add a0 sp 0x58, 2) := by decide
theorem es_at_1a : fetchRel ecdsaSignature48Code 0x1A = some (.aluImm .add a1 sp 0x8, 2) := by decide
theorem es_at_1c : fetchRel ecdsaSignature48Code 0x1C = some (.auipc ra 0x0, 4) := by decide
theorem es_at_20 : fetchRel ecdsaSignature48Code 0x20 = some (.jalr ra ra 0xFFFFFD3A, 4) := by decide
theorem es_at_24 : fetchRel ecdsaSignature48Code 0x24 = some (.load .lw (8 : Fin 32) sp 0x58, 2) := by decide
theorem es_at_26 : fetchRel ecdsaSignature48Code 0x26 = some (.load .lbu (9 : Fin 32) sp 0x5C, 4) := by decide
theorem es_at_2a : fetchRel ecdsaSignature48Code 0x2A = some (.branch .beq (8 : Fin 32) x0 0x40, 2) := by decide
theorem es_at_2c : fetchRel ecdsaSignature48Code 0x2C = some (.aluImm .add a1 sp 0x5D, 4) := by decide
theorem es_at_30 : fetchRel ecdsaSignature48Code 0x30 = some (.aluImm .add a0 sp 0x1D, 4) := by decide
theorem es_at_34 : fetchRel ecdsaSignature48Code 0x34 = some (.aluImm .add a2 x0 0xB, 2) := by decide
theorem es_at_36 : fetchRel ecdsaSignature48Code 0x36 = some (.auipc ra 0xC000, 4) := by decide
theorem es_at_3a : fetchRel ecdsaSignature48Code 0x3A = some (.jalr ra ra 0x6A4, 4) := by decide
theorem es_at_3e : fetchRel ecdsaSignature48Code 0x3E = some (.load .lw a2 sp 0x14, 2) := by decide
theorem es_at_40 : fetchRel ecdsaSignature48Code 0x40 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem es_at_42 : fetchRel ecdsaSignature48Code 0x42 = some (.store .sb sp (9 : Fin 32) 0x1C, 4) := by decide
theorem es_at_46 : fetchRel ecdsaSignature48Code 0x46 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem es_at_48 : fetchRel ecdsaSignature48Code 0x48 = some (.aluImm .add (9 : Fin 32) x0 0x1, 2) := by decide
theorem es_at_4a : fetchRel ecdsaSignature48Code 0x4A = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem es_at_4c : fetchRel ecdsaSignature48Code 0x4C = some (.branch .bne a2 x0 0x22, 2) := by decide
theorem es_at_4e : fetchRel ecdsaSignature48Code 0x4E = some (.aluImm .add a0 sp 0x58, 2) := by decide
theorem es_at_50 : fetchRel ecdsaSignature48Code 0x50 = some (.aluImm .add a1 sp 0x18, 2) := by decide
theorem es_at_52 : fetchRel ecdsaSignature48Code 0x52 = some (.auipc ra 0x0, 4) := by decide
theorem es_at_56 : fetchRel ecdsaSignature48Code 0x56 = some (.jalr ra ra 0xBA, 4) := by decide
theorem es_at_5a : fetchRel ecdsaSignature48Code 0x5A = some (.load .lbu a0 sp 0x58, 4) := by decide
theorem es_at_5e : fetchRel ecdsaSignature48Code 0x5E = some (.load .lbu (19 : Fin 32) sp 0x59, 4) := by decide
theorem es_at_62 : fetchRel ecdsaSignature48Code 0x62 = some (.branch .beq a0 x0 0x26, 2) := by decide
theorem es_at_64 : fetchRel ecdsaSignature48Code 0x64 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem es_at_66 : fetchRel ecdsaSignature48Code 0x66 = some (.alu .add (9 : Fin 32) x0 (19 : Fin 32), 2) := by decide
theorem es_at_68 : fetchRel ecdsaSignature48Code 0x68 = some (.jal x0 0x4, 2) := by decide
theorem es_at_6a : fetchRel ecdsaSignature48Code 0x6A = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem es_at_6c : fetchRel ecdsaSignature48Code 0x6C = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem es_at_6e : fetchRel ecdsaSignature48Code 0x6E = some (.alu .add a0 a0 (20 : Fin 32), 2) := by decide
theorem es_at_70 : fetchRel ecdsaSignature48Code 0x70 = some (.store .sb (20 : Fin 32) a1 0x0, 4) := by decide
theorem es_at_74 : fetchRel ecdsaSignature48Code 0x74 = some (.store .sb a0 (9 : Fin 32) 0x0, 4) := by decide
theorem es_at_78 : fetchRel ecdsaSignature48Code 0x78 = some (.load .lw ra sp 0xCC, 2) := by decide
theorem es_at_7a : fetchRel ecdsaSignature48Code 0x7A = some (.load .lw (8 : Fin 32) sp 0xC8, 2) := by decide
theorem es_at_7c : fetchRel ecdsaSignature48Code 0x7C = some (.load .lw (9 : Fin 32) sp 0xC4, 2) := by decide
theorem es_at_7e : fetchRel ecdsaSignature48Code 0x7E = some (.load .lw (18 : Fin 32) sp 0xC0, 2) := by decide
theorem es_at_80 : fetchRel ecdsaSignature48Code 0x80 = some (.load .lw (19 : Fin 32) sp 0xBC, 2) := by decide
theorem es_at_82 : fetchRel ecdsaSignature48Code 0x82 = some (.load .lw (20 : Fin 32) sp 0xB8, 2) := by decide
theorem es_at_84 : fetchRel ecdsaSignature48Code 0x84 = some (.aluImm .add sp sp 0xD0, 2) := by decide
theorem es_at_86 : fetchRel ecdsaSignature48Code 0x86 = some (.jalr x0 ra 0x0, 2) := by decide
theorem es_at_88 : fetchRel ecdsaSignature48Code 0x88 = some (.aluImm .add a1 sp 0x5A, 4) := by decide
theorem es_at_8c : fetchRel ecdsaSignature48Code 0x8C = some (.aluImm .add a0 sp 0x29, 4) := by decide
theorem es_at_90 : fetchRel ecdsaSignature48Code 0x90 = some (.aluImm .add a2 x0 0x2F, 4) := by decide
theorem es_at_94 : fetchRel ecdsaSignature48Code 0x94 = some (.auipc ra 0xC000, 4) := by decide
theorem es_at_98 : fetchRel ecdsaSignature48Code 0x98 = some (.jalr ra ra 0x646, 4) := by decide
theorem es_at_9c : fetchRel ecdsaSignature48Code 0x9C = some (.aluImm .add a0 sp 0x58, 2) := by decide
theorem es_at_9e : fetchRel ecdsaSignature48Code 0x9E = some (.aluImm .add a1 sp 0x18, 2) := by decide
theorem es_at_a0 : fetchRel ecdsaSignature48Code 0xA0 = some (.auipc ra 0x0, 4) := by decide
theorem es_at_a4 : fetchRel ecdsaSignature48Code 0xA4 = some (.jalr ra ra 0x6C, 4) := by decide
theorem es_at_a8 : fetchRel ecdsaSignature48Code 0xA8 = some (.load .lbu a0 sp 0x58, 4) := by decide
theorem es_at_ac : fetchRel ecdsaSignature48Code 0xAC = some (.load .lbu (18 : Fin 32) sp 0x59, 4) := by decide
theorem es_at_b0 : fetchRel ecdsaSignature48Code 0xB0 = some (.branch .beq a0 x0 0x8, 2) := by decide
theorem es_at_b2 : fetchRel ecdsaSignature48Code 0xB2 = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem es_at_b4 : fetchRel ecdsaSignature48Code 0xB4 = some (.alu .add (9 : Fin 32) x0 (18 : Fin 32), 2) := by decide
theorem es_at_b6 : fetchRel ecdsaSignature48Code 0xB6 = some (.jal x0 0xFFFFFFB6, 2) := by decide
theorem es_at_b8 : fetchRel ecdsaSignature48Code 0xB8 = some (.aluImm .add a1 sp 0x5A, 4) := by decide
theorem es_at_bc : fetchRel ecdsaSignature48Code 0xBC = some (.aluImm .add a0 sp 0x89, 4) := by decide
theorem es_at_c0 : fetchRel ecdsaSignature48Code 0xC0 = some (.aluImm .add a2 x0 0x2F, 4) := by decide
theorem es_at_c4 : fetchRel ecdsaSignature48Code 0xC4 = some (.auipc ra 0xC000, 4) := by decide
theorem es_at_c8 : fetchRel ecdsaSignature48Code 0xC8 = some (.jalr ra ra 0x616, 4) := by decide
theorem es_at_cc : fetchRel ecdsaSignature48Code 0xCC = some (.load .lw a2 sp 0x24, 2) := by decide
theorem es_at_ce : fetchRel ecdsaSignature48Code 0xCE = some (.aluImm .add a0 x0 0x1, 2) := by decide
theorem es_at_d0 : fetchRel ecdsaSignature48Code 0xD0 = some (.aluImm .add (9 : Fin 32) x0 0x1, 2) := by decide
theorem es_at_d2 : fetchRel ecdsaSignature48Code 0xD2 = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem es_at_d4 : fetchRel ecdsaSignature48Code 0xD4 = some (.branch .bne a2 x0 0xFFFFFF9A, 2) := by decide
theorem es_at_d6 : fetchRel ecdsaSignature48Code 0xD6 = some (.aluImm .add a0 (20 : Fin 32) 0x2, 4) := by decide
theorem es_at_da : fetchRel ecdsaSignature48Code 0xDA = some (.aluImm .add a1 sp 0x29, 4) := by decide
theorem es_at_de : fetchRel ecdsaSignature48Code 0xDE = some (.aluImm .add a2 x0 0x2F, 4) := by decide
theorem es_at_e2 : fetchRel ecdsaSignature48Code 0xE2 = some (.auipc ra 0xC000, 4) := by decide
theorem es_at_e6 : fetchRel ecdsaSignature48Code 0xE6 = some (.jalr ra ra 0x5F8, 4) := by decide
theorem es_at_ea : fetchRel ecdsaSignature48Code 0xEA = some (.aluImm .add a0 (20 : Fin 32) 0x32, 4) := by decide
theorem es_at_ee : fetchRel ecdsaSignature48Code 0xEE = some (.aluImm .add a1 sp 0x89, 4) := by decide
theorem es_at_f2 : fetchRel ecdsaSignature48Code 0xF2 = some (.aluImm .add a2 x0 0x2F, 4) := by decide
theorem es_at_f6 : fetchRel ecdsaSignature48Code 0xF6 = some (.auipc ra 0xC000, 4) := by decide
theorem es_at_fa : fetchRel ecdsaSignature48Code 0xFA = some (.jalr ra ra 0x5E4, 4) := by decide
theorem es_at_fe : fetchRel ecdsaSignature48Code 0xFE = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem es_at_100 : fetchRel ecdsaSignature48Code 0x100 = some (.store .sb (20 : Fin 32) (19 : Fin 32) 0x1, 4) := by decide
theorem es_at_104 : fetchRel ecdsaSignature48Code 0x104 = some (.aluImm .add a0 x0 0x31, 4) := by decide
theorem es_at_108 : fetchRel ecdsaSignature48Code 0x108 = some (.alu .add (9 : Fin 32) x0 (18 : Fin 32), 2) := by decide
theorem es_at_10a : fetchRel ecdsaSignature48Code 0x10A = some (.jal x0 0xFFFFFF64, 2) := by decide
end

/-- The bytes an element took from its reader: its header and contents, or
none when it failed. -/
def derUsed : Except DerError DerTlv → Nat
  | .ok t => t.header + t.len
  | .error _ => 0

/-- `der::ecdsa_signature::<N>`'s result for the `n` bytes at `p` in `M`:
the error byte, or `r` and `s`. -/
def ecdsaSigOf (N : Nat) (M : Word → BitVec 8) (p : Word) (n : Nat) : Except (BitVec 8) (Bytes × Bytes) :=
  match derElement 0x30 (memBytes M p n) with
  | .error e => .error (derErrByte e)
  | .ok t =>
    if t.header + t.len = n then
      match derScalarOf N (memBytes M (p + BitVec.ofNat 32 t.header) t.len) (p + BitVec.ofNat 32 t.header)
          (derElement 2 (memBytes M (p + BitVec.ofNat 32 t.header) t.len)) with
      | .error b => .error b
      | .ok r =>
        match derScalarOf N
            (memBytes M (p + BitVec.ofNat 32 (t.header +
              derUsed (derElement 2 (memBytes M (p + BitVec.ofNat 32 t.header) t.len))))
              (t.len - derUsed (derElement 2 (memBytes M (p + BitVec.ofNat 32 t.header) t.len))))
            (p + BitVec.ofNat 32 (t.header + derUsed (derElement 2 (memBytes M (p + BitVec.ofNat 32 t.header) t.len))))
            (derElement 2 (memBytes M (p + BitVec.ofNat 32 (t.header +
              derUsed (derElement 2 (memBytes M (p + BitVec.ofNat 32 t.header) t.len))))
              (t.len - derUsed (derElement 2 (memBytes M (p + BitVec.ofNat 32 t.header) t.len))))) with
        | .error b => .error b
        | .ok s =>
          if derUsed (derElement 2 (memBytes M (p + BitVec.ofNat 32 (t.header +
              derUsed (derElement 2 (memBytes M (p + BitVec.ofNat 32 t.header) t.len))))
              (t.len - derUsed (derElement 2 (memBytes M (p + BitVec.ofNat 32 t.header) t.len))))) =
            t.len - derUsed (derElement 2 (memBytes M (p + BitVec.ofNat 32 t.header) t.len)) then .ok (r, s)
          else .error 1
    else .error 1

/-- Where `der::ecdsa_signature::<48>` runs: its code and its callees', the
0x170 bytes of stack below `sp0`, the 97-byte result at `out`, and the `n`
signature bytes at `p`, apart from what each must not touch. -/
structure ESEnv (M : Word → BitVec 8) (P sp0 out p : Word) (n : Nat) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P ecdsaSignature48Code
  seq : CodeIn M (P + 0xFFFFFD56) derSequenceCode
  nst : CodeIn M (P + 0xFFFFFFCE) derNestedCode
  elem : CodeIn M (P + 0xFFFFFEEE) derElementCode
  tlv : CodeIn M (P + 0xFFFFFF14) derTlvCode
  pint : CodeIn M (P + 0xFFFFFE1E) derPositiveIntegerCode
  int : CodeIn M (P + 0xFFFFFE90) derIntegerCode
  zip : CodeIn M (P + 0xFFFFFE6E) zipSkipNextCode
  sc : CodeIn M (P + 0x10C) derScalar48Code
  mset : CodeIn M (P + 0xC672) memsetCode
  mcs : CodeIn M (P + 0xC6DA) memcpyStubCode
  mcb : CodeIn M (P + 0xC6E2) memcpyBodyCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x170 ≤ sp0.toNat
  how : out.toNat + 97 < 2 ^ 32
  hp : 0 < p.toNat
  hpn : p.toNat + n < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFE90) 0x170 P ecdsaSignature48Code.length
  sGQ : Sep (sp0 + 0xFFFFFE90) 0x170 (P + 0xFFFFFD56) derSequenceCode.length
  sGN : Sep (sp0 + 0xFFFFFE90) 0x170 (P + 0xFFFFFFCE) derNestedCode.length
  sGE : Sep (sp0 + 0xFFFFFE90) 0x170 (P + 0xFFFFFEEE) derElementCode.length
  sGT : Sep (sp0 + 0xFFFFFE90) 0x170 (P + 0xFFFFFF14) derTlvCode.length
  sGP : Sep (sp0 + 0xFFFFFE90) 0x170 (P + 0xFFFFFE1E) derPositiveIntegerCode.length
  sGI : Sep (sp0 + 0xFFFFFE90) 0x170 (P + 0xFFFFFE90) derIntegerCode.length
  sGZ : Sep (sp0 + 0xFFFFFE90) 0x170 (P + 0xFFFFFE6E) zipSkipNextCode.length
  sGS : Sep (sp0 + 0xFFFFFE90) 0x170 (P + 0x10C) derScalar48Code.length
  sGM : Sep (sp0 + 0xFFFFFE90) 0x170 (P + 0xC672) memsetCode.length
  sGU : Sep (sp0 + 0xFFFFFE90) 0x170 (P + 0xC6DA) memcpyStubCode.length
  sGB : Sep (sp0 + 0xFFFFFE90) 0x170 (P + 0xC6E2) memcpyBodyCode.length
  sOC : Sep out 97 P ecdsaSignature48Code.length
  sOB : Sep out 97 (P + 0xC6E2) memcpyBodyCode.length
  sOU : Sep out 97 (P + 0xC6DA) memcpyStubCode.length
  sOG : Sep out 97 (sp0 + 0xFFFFFE90) 0x170
  sDG : Sep p n (sp0 + 0xFFFFFE90) 0x170

/-- From 0xE to the call to `Der::sequence`: the result pointer to `s4`, the
input reader at `sp + 8`, and `Der::sequence`'s arguments. -/
def esIn : List BInstr :=
  [.alu .add (20 : Fin 32) x0 a0, .sw sp a1 0x8, .sw sp a2 0xC, .sw sp a1 0x10, .sw sp a2 0x14,
   .aluImm .add a0 sp 0x58, .aluImm .add a1 sp 0x8]

abbrev esPs : List (Fin 32 × Word) :=
  [(ra, 0xCC), ((8 : Fin 32), 0xC8), ((9 : Fin 32), 0xC4), ((18 : Fin 32), 0xC0), ((19 : Fin 32), 0xBC),
   ((20 : Fin 32), 0xB8)]

section
set_option maxRecDepth 20000
theorem esIn_end : blockEnd ecdsaSignature48Code 0xE esIn = some 0x1C := by decide
theorem esSave_end : blockEnd ecdsaSignature48Code 2 (saveBlock esPs) = some 0xE := by decide
theorem esRestore_end : blockEnd ecdsaSignature48Code 0x78 (restoreBlock esPs) = some 0x84 := by decide
end

theorem esIn_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock esIn (M, f)).1 = memStore32 (memStore32 (memStore32 (memStore32 M (f sp + 8) (f a1)) (f sp + 0xC) (f a2))
      (f sp + 0x10) (f a1)) (f sp + 0x14) (f a2) ∧
    (runBlock esIn (M, f)).2 (20 : Fin 32) = f a0 ∧ (runBlock esIn (M, f)).2 a0 = f sp + 0x58 ∧
    (runBlock esIn (M, f)).2 a1 = f sp + 8 ∧
    ∀ q, q ≠ (20 : Fin 32) → q ≠ a0 → q ≠ a1 → (runBlock esIn (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, esIn]
  have u : ∀ r : Fin 32, r ≠ (20 : Fin 32) → upd f 20 (aluEval .add (f x0) (f a0)) r = f r := fun r h => updz hz h
  simp only [u sp (by decide), u a1 (by decide), u a2 (by decide)]
  refine ⟨trivial, ?_, ?_, ?_, fun q q20 q0 q1 => ?_⟩
  · simp +decide only [upd_app, ↓reduceIte]; rw [hz]; exact zw _
  · simp +decide only [upd_app, ↓reduceIte]; rfl
  · simp +decide only [upd_app, ↓reduceIte]; rfl
  · rw [updz (upd_zero _ _ _) q1, updz (upd_zero _ _ _) q0, updz hz q20]

theorem sep_off0 (b : Word) {d k : Nat} (h : 4 ≤ d) (hd : d + k ≤ 2 ^ 32) : Sep b 4 (b + BitVec.ofNat 32 d) k := by
  have := sep_offsets b (c := 0) (n := 4) (d := d) (k := k) (.inl (by omega)) (by decide) hd
  rwa [add_ofNat_zero] at this

theorem nestedMem_outside {M : Word → BitVec 8} {out rp x : Word} (R : Except DerError DerTlv)
    (hx : Sep out 16 x 1) : derNestedMem M out rp R x = M x := by
  have h0 : Sep out 4 x 1 := by have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  cases R with
  | error e =>
    simp only [derNestedMem]
    rw [memStore32_get_sep h0, memStore8_ne fun e' => hx.point (i := 4) (j := 0) (by decide) (by decide)
      (by rw [add_ofNat_zero]; exact e'.symm)]
  | ok t =>
    simp only [derNestedMem]
    rw [memStore32_get_sep h0, memStore32_get_sep (a := out + 0xC) (hx.sub (c := 0xC) (l := 4) (by decide)),
      memStore32_get_sep (a := out + 4) (hx.sub (c := 4) (l := 4) (by decide)),
      memStore32_get_sep (a := out + 8) (hx.sub (c := 8) (l := 4) (by decide))]

theorem nestedMem_err {M : Word → BitVec 8} {out rp : Word} (e : DerError) :
    memLoad32 (derNestedMem M out rp (.error e)) out = 0 ∧ derNestedMem M out rp (.error e) (out + 4) = derErrByte e := by
  simp only [derNestedMem]
  refine ⟨memLoad32_store32_same _ _ _, ?_⟩
  rw [memStore32_get_sep (x := out + 4) (sep_off0 out (d := 4) (k := 1) (by decide) (by decide)), memStore8_same]

theorem nestedMem_ok {M : Word → BitVec 8} {out rp : Word} (t : DerTlv) :
    memLoad32 (derNestedMem M out rp (.ok t)) out = rp + BitVec.ofNat 32 t.header ∧
    memLoad32 (derNestedMem M out rp (.ok t)) (out + 4) = BitVec.ofNat 32 t.len ∧
    memLoad32 (derNestedMem M out rp (.ok t)) (out + 8) = rp + BitVec.ofNat 32 t.header ∧
    memLoad32 (derNestedMem M out rp (.ok t)) (out + 0xC) = BitVec.ofNat 32 t.len := by
  simp only [derNestedMem]
  have s48 : Sep (out + 4) 4 (out + 8) 4 := by
    have := sep_offsets out (c := 4) (n := 4) (d := 8) (k := 4) (.inl (by decide)) (by decide) (by decide); exact this
  have s4C : Sep (out + 0xC) 4 (out + 4) 4 := by
    have := sep_offsets out (c := 0xC) (n := 4) (d := 4) (k := 4) (.inr (by decide)) (by decide) (by decide); exact this
  have sC8 : Sep (out + 0xC) 4 (out + 8) 4 := by
    have := sep_offsets out (c := 0xC) (n := 4) (d := 8) (k := 4) (.inr (by decide)) (by decide) (by decide); exact this
  refine ⟨memLoad32_store32_same _ _ _, ?_, ?_, ?_⟩
  · rw [memLoad32_store32_sep (b := out + 4) (sep_off0 out (d := 4) (k := 4) (by decide) (by decide)), memLoad32_store32_sep s4C,
      memLoad32_store32_same]
  · rw [memLoad32_store32_sep (b := out + 8) (sep_off0 out (d := 8) (k := 4) (by decide) (by decide)), memLoad32_store32_sep sC8,
      memLoad32_store32_sep s48, memLoad32_store32_same]
  · rw [memLoad32_store32_sep (b := out + 0xC) (sep_off0 out (d := 0xC) (k := 4) (by decide) (by decide)), memLoad32_store32_same]

theorem derAdvance_ld {M : Word → BitVec 8} {d rp rl : Word} (t : DerTlv) :
    memLoad32 (derAdvance M d rp rl (.ok t)) (d + 8) = rp + BitVec.ofNat 32 (t.header + t.len) ∧
    memLoad32 (derAdvance M d rp rl (.ok t)) (d + 0xC) = rl - BitVec.ofNat 32 (t.header + t.len) := by
  simp only [derAdvance]
  refine ⟨?_, memLoad32_store32_same _ _ _⟩
  rw [memLoad32_store32_sep (a := d + 0xC) (b := d + 8)
    (sep_offsets d (c := 0xC) (n := 4) (d := 8) (k := 4) (.inr (by decide)) (by decide) (by decide)),
    memLoad32_store32_same]

theorem memLoad32_congr2 {M M' : Word → BitVec 8} {b b' : Word}
    (h : ∀ j, j < 4 → M (b + BitVec.ofNat 32 j) = M' (b' + BitVec.ofNat 32 j)) :
    memLoad32 M b = memLoad32 M' b' := by
  unfold memLoad32
  have h0 := h 0 (by decide)
  rw [add_ofNat_zero, add_ofNat_zero] at h0
  rw [h0, show b + 1 = b + BitVec.ofNat 32 1 from rfl, h 1 (by decide),
    show b + 2 = b + BitVec.ofNat 32 2 from rfl, h 2 (by decide),
    show b + 3 = b + BitVec.ofNat 32 3 from rfl, h 3 (by decide)]
  rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **The compiled `der::ecdsa_signature::<48>`**: with the `n` signature
bytes at `p`, it stores `ecdsaSigOf 48` of them in its
`Result<([u8; 48], [u8; 48]), Error>` at `out`: a zero tag, `r`, and `s`, or
a tag of 1 and the error byte. -/
theorem ecdsaSignature48_correct (m : Machine) {P sp0 out p retAddr : Word} {n : Nat}
    (env : ESEnv m.mem P sp0 out p n) (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out)
    (ha1 : reg m a1 = p) (ha2 : reg m a2 = BitVec.ofNat 32 n) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∀ x, Sep (sp0 + 0xFFFFFE90) 0x170 x 1 → Sep out 97 x 1 → m'.mem x = m.mem x) ∧
      match ecdsaSigOf 48 m.mem p n with
      | .ok (r, s) => m'.mem out = 0 ∧
          (∀ j, j < 48 → m'.mem (out + BitVec.ofNat 32 (1 + j)) = BitVec.ofNat 8 (r.getD j 0)) ∧
          ∀ j, j < 48 → m'.mem (out + BitVec.ofNat 32 (49 + j)) = BitVec.ofNat 8 (s.getD j 0)
      | .error b => m'.mem out = 1 ∧ m'.mem (out + 1) = b := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFE90 = G := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFF30 = F := ⟨_, rfl⟩
  have sGC := env.sGC; have sGQ := env.sGQ; have sGN := env.sGN; have sGE := env.sGE; have sGT := env.sGT
  have sGP := env.sGP; have sGI := env.sGI; have sGZ := env.sGZ; have sGS := env.sGS; have sGM := env.sGM
  have sGU := env.sGU; have sGB := env.sGB; have sOG := env.sOG; have sDG := env.sDG
  rw [hG] at sGC sGQ sGN sGE sGT sGP sGI sGZ sGS sGM sGU sGB sOG sDG ⊢
  have hn : n < 2 ^ 32 := by have := env.hpn; omega
  have hGF : G + 0xA0 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFE90) (by decide)
  have hFa : F.toNat % 4 = 0 := by rw [← hGF]; exact aligned_add hGa (k := 0xA0) (by decide)
  have hGw : G.toNat + 0x170 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFE90 : Word).toNat = 4294966928 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have hFn : F.toNat = G.toNat + 0xA0 := by
    rw [← hGF, BitVec.toNat_add, show (0xA0 : Word).toNat = 0xA0 from rfl]; omega
  have eS : F + 0xD0 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0xA0 + k) := fun k => by
    rw [← hGF, show (0xA0 : Word) = BitVec.ofNat 32 0xA0 from rfl, add_ofNat_assoc]
  have inF : ∀ {b : Word} {l : Nat}, Sep G 0x170 b l → Sep F 0xD0 b l := fun h => by
    rw [← hGF]; exact h.sub (c := 0xA0) (l := 0xD0) (by decide)
  have sepF : ∀ {c n k : Nat}, c + n ≤ k ∨ k + 1 ≤ c → c + n ≤ 0xD0 → k < 0xD0 →
      Sep (F + BitVec.ofNat 32 c) n (F + BitVec.ofNat 32 k) 1 := fun h h1 h2 => by
    rw [eFk, eFk]; exact sep_offsets G (by omega) (by omega) (by omega)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0x170 b code'.length → (∀ x, Sep G 0x170 x 1 → M' x = m.mem x) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod es_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF30) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock esPs) u1 env.cod esSave_end (saveBlock_ok _ esPs _ fun p hp => by
    rw [sp1]
    simp only [esPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨aligned_add hFa (by decide), (inF sGC).sub (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF30)) esPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep G 0x170 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside esPs fun p hp => by
      simp only [esPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact (inF hx).sub (by decide)
  have frLo : ∀ k, k < 0xB8 → Msv (F + BitVec.ofNat 32 k) = m.mem (F + BitVec.ofNat 32 k) := fun k hk => by
    rw [← hMsv]
    exact saveMem_outside esPs fun p hp => by
      simp only [esPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact sep_offsets F (.inr (by simp; omega)) (by simp) (by omega)
  have hslv : ∀ r o, (r, o) ∈ esPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [esPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  have hcS : CodeIn Msv P ecdsaSignature48Code := cIn env.cod sGC frSv
  -- the input reader and `Der::sequence`'s arguments
  have sInC : ∀ c, 8 ≤ c → c + 4 ≤ 0x18 → Sep (F + BitVec.ofNat 32 c) 4 P ecdsaSignature48Code.length :=
    fun c h1 h2 => (inF sGC).sub (by omega)
  obtain ⟨m3, c3, u3⟩ := St.block esIn u2.self hcS esIn_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, esIn, upd, ↓reduceIte, true_and, and_true]
    rw [sp2]
    exact ⟨⟨aligned_add hFa (k := 8) (by decide), sInC 8 (by decide) (by decide)⟩,
      ⟨aligned_add hFa (k := 0xC) (by decide), sInC 0xC (by decide) (by decide)⟩,
      ⟨aligned_add hFa (k := 0x10) (by decide), sInC 0x10 (by decide) (by decide)⟩,
      aligned_add hFa (k := 0x14) (by decide), sInC 0x14 (by decide) (by decide)⟩)
  obtain ⟨em3, e320, e3a0, e3a1, k3⟩ := esIn_run (M := Msv) (f := reg m2) u2.self.zero
  rw [em3] at u3
  rw [sp2, r2 a1 (by decide), r2 a2 (by decide), ha1, ha2] at u3
  obtain ⟨Mb, hMb⟩ : ∃ Mb, memStore32 (memStore32 (memStore32 (memStore32 Msv (F + 8) p) (F + 0xC) (BitVec.ofNat 32 n))
      (F + 0x10) p) (F + 0x14) (BitVec.ofNat 32 n) = Mb := ⟨_, rfl⟩
  rw [hMb] at u3
  have ss4 : ∀ c d : Nat, (c + 4 ≤ d ∨ d + 4 ≤ c) → c + 4 ≤ 0xD0 → d + 4 ≤ 0xD0 →
      Sep (F + BitVec.ofNat 32 c) 4 (F + BitVec.ofNat 32 d) 4 := fun c d h h1 h2 =>
    sep_offsets F h (by omega) (by omega)
  have frB : ∀ x, Sep (F + 8) 16 x 1 → Mb x = Msv x := fun x hx => by
    rw [← hMb]
    have h : ∀ c, 8 ≤ c → c + 4 ≤ 0x18 → Sep (F + BitVec.ofNat 32 c) 4 x 1 := fun c h1 h2 => by
      have := hx.sub (c := c - 8) (l := 4) (by omega)
      rwa [show (8 : Word) = BitVec.ofNat 32 8 from rfl, add_ofNat_assoc, show 8 + (c - 8) = c by omega] at this
    rw [memStore32_get_sep (a := F + 0x14) (h 0x14 (by decide) (by decide)),
      memStore32_get_sep (a := F + 0x10) (h 0x10 (by decide) (by decide)),
      memStore32_get_sep (a := F + 0xC) (h 0xC (by decide) (by decide)),
      memStore32_get_sep (a := F + 8) (h 8 (by decide) (by decide))]
  have lP : memLoad32 Mb (F + 8 + 8) = p := by
    rw [← hMb, show F + 8 + 8 = F + 0x10 by rw [BitVec.add_assoc]; rfl,
      memLoad32_store32_sep (a := F + 0x14) (b := F + 0x10) (ss4 0x14 0x10 (by decide) (by decide) (by decide)),
      memLoad32_store32_same]
  have lN : memLoad32 Mb (F + 8 + 0xC) = BitVec.ofNat 32 n := by
    rw [← hMb, show F + 8 + 0xC = F + 0x14 by rw [BitVec.add_assoc]; rfl, memLoad32_store32_same]
  have frBG : ∀ x, Sep G 0x170 x 1 → Mb x = m.mem x := fun x hx => by
    rw [frB x ((inF hx).sub (c := 8) (l := 16) (by decide)), frSv x hx]
  have hcB : ∀ {b : Word} {code' : List Nat}, CodeIn m.mem b code' → Sep G 0x170 b code'.length →
      CodeIn Mb b code' := fun hc hs => cIn hc hs frBG
  have hcB0 := hcB env.cod sGC
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.callRa hcB0 es_at_1c es_at_20 (cb := P + 0xFFFFFD56)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFFD56 (by decide))
  have r4 := PEnv.reg1 regs4 u3.zero
  have g3 : ∀ q, reg m3 q = (runBlock esIn (Msv, reg m2)).2 q := u3.regs
  have sp4 : reg m4 sp = F := by rw [r4 sp (by decide), k3 sp (by decide) (by decide) (by decide), sp2]
  have eN : P + 0xFFFFFD56 + 0x278 = P + 0xFFFFFFCE := by rw [BitVec.add_assoc]; rfl
  have eNF : F + 0xFFFFFFE0 = G + BitVec.ofNat 32 0x80 := by rw [← hGF, BitVec.add_assoc]; rfl
  have eGk : ∀ k, G + BitVec.ofNat 32 0xA0 + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0xA0 + k) := fun k =>
    add_ofNat_assoc G 0xA0 k
  have sFk : ∀ {b : Word} {l : Nat} (c k : Nat), c + k ≤ 0xD0 → Sep G 0x170 b l →
      Sep (F + BitVec.ofNat 32 c) k b l := fun c k h hs => (inF hs).sub (by omega)
  have hNE : NestEnv m4.mem (P + 0xFFFFFD56 + 0x278) F (F + 0x58) (F + 8) := by
    rw [mem4, eN]
    refine ⟨even_at P env.hP 0xFFFFFFCE (by decide), hcB env.nst sGN,
      by rw [BitVec.add_assoc]; exact hcB env.elem sGE, by rw [BitVec.add_assoc]; exact hcB env.tlv sGT,
      hFa, by omega, aligned_add hFa (k := 0x58) (by decide), aligned_add hFa (k := 8) (by decide),
      by rw [eNF]; exact sGN.sub (by decide),
      by rw [eNF, BitVec.add_assoc]; exact sGE.sub (by decide),
      by rw [eNF, BitVec.add_assoc]; exact sGT.sub (by decide),
      sFk 0x58 16 (by decide) sGN,
      by rw [BitVec.add_assoc]; exact sFk 0x10 8 (by decide) sGN,
      by rw [BitVec.add_assoc, BitVec.add_assoc]; exact sFk 0x10 8 (by decide) sGT,
      by rw [eNF, show F + 0x58 = F + BitVec.ofNat 32 0x58 from rfl, eFk]
         exact sep_offsets G (.inr (by decide)) (by decide) (by decide),
      by rw [eNF, BitVec.add_assoc, show F + (8 + 8) = F + BitVec.ofNat 32 0x10 from rfl, eFk]
         exact sep_offsets G (.inr (by decide)) (by decide) (by decide),
      by rw [lP, lN, ofNat_tn hn, eNF]; exact sDG.subR (by decide),
      by rw [lP]; exact env.hp,
      by rw [lP, lN, ofNat_tn hn]; exact env.hpn⟩
  have hpsp : ∀ p ∈ esPs, p.1 ≠ sp := by decide
  -- the epilogue, from 0x78
  have fin : ∀ {Mx : Word → BitVec 8} {n : Machine}, Steps m n → St Mx P n 0x78 (reg n) →
      CodeIn Mx P ecdsaSignature48Code →
      (∀ k, 0xB8 ≤ k → k < 0xD0 → Mx (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k)) → reg n sp = F →
      (∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg n q = reg m q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ n'.mem = Mx ∧ reg n' sp = sp0 ∧
        ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg m q := by
    intro Mx n S st hc hsl rsp kq
    have slotW : ∀ r o, (r, o) ∈ esPs → memLoad32 Mx (F + o) = reg m r := fun r o h => by
      have ho : 0xB8 ≤ o.toNat ∧ o.toNat + 4 ≤ 0xD0 := by
        simp only [esPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      rw [← hslv r o h]
      apply memLoad32_congr; intro j hj
      rw [← ofNat_toNat_self o, add_ofNat_assoc, hsl _ (by omega) (by omega)]
    obtain ⟨n1, c1, u1⟩ := St.block (restoreBlock esPs) st hc esRestore_end
      (restoreBlock_ok Mx F esPs (reg n) rsp hpsp fun q hq => by
        simp only [esPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
    simp only [restoreBlock_run Mx F esPs (reg n) rsp hpsp] at u1
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hc es_at_84 (off' := 0x86) (by decide)
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc es_at_86
    have rsp1 : restoreRegs Mx F (reg n) esPs sp = F := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact rsp
    have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
        restoreRegs Mx F f ps q = f q := by
      intro f ps q h0
      induction ps generalizing f with
      | nil => intro _; rfl
      | cons p ps ih =>
        intro h
        simp only [restoreRegs]
        rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
    have hreg : ∀ r o, (r, o) ∈ esPs → restoreRegs Mx F (reg n) esPs r = reg m r := fun r o hm => by
      simp only [esPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
        exact slotW _ _ (by decide)
    refine ⟨n3, S.trans (c1.trans (.cons d2 (.single d3))), ?_, mem3, ?_, fun q hq => ?_⟩
    · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [hreg ra 0xCC (by decide), hra, add_lit_zero, hret]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp1, eS]
    · rw [regs3]
      have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
          q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
          q = (20 : Fin 32) ∨ (q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧
            (∀ p ∈ esPs, p.1 ≠ q)) := by decide
      rcases key q hq with rfl | rfl | rfl | rfl | rfl | rfl | ⟨h1, h0, hs, hps⟩
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0xCC (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0xC8 (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0xC4 (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0xC0 (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0xBC (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0xB8 (by decide)
      · rw [upd_ne h0 hs, rr _ _ q h0 hps]; exact kq q h1
  have outF : ∀ k, k < 0xD0 → Sep out 97 (F + BitVec.ofNat 32 k) 1 := fun k hk => by
    rw [eFk]; exact sOG.subR (by omega)
  -- the result's stores, from 0x6E
  have tail : ∀ {Mx : Word → BitVec 8} {n : Machine} {k : Nat} {tag b : BitVec 8}, Steps m n →
      St Mx P n 0x6E (reg n) → CodeIn Mx P ecdsaSignature48Code →
      (∀ j, 0xB8 ≤ j → j < 0xD0 → Mx (F + BitVec.ofNat 32 j) = Msv (F + BitVec.ofNat 32 j)) → reg n sp = F →
      reg n 20 = out → reg n a0 = BitVec.ofNat 32 k → 0 < k → k < 97 → (reg n a1).extractLsb' 0 8 = tag →
      (reg n 9).extractLsb' 0 8 = b → (∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg n q = reg m q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ n'.mem = memStore8 (memStore8 Mx out tag) (out + BitVec.ofNat 32 k) b ∧
        reg n' sp = sp0 ∧ ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg m q := by
    intro Mx n k tag b S st hc hsl rsp r20 ra0 hk0 hk ra1 rs1 kq
    obtain ⟨n1, d1, u1⟩ := st.alu hc es_at_6e (off' := 0x70) (by decide)
    have k1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := fun q h => by rw [u1.regs, upd_ne' h st.zero]
    have v1 : reg n1 a0 = out + BitVec.ofNat 32 k := by
      rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, ra0, r20]; exact BitVec.add_comm _ _
    obtain ⟨n2, d2, u2⟩ := u1.self.sb hc es_at_70 (off' := 0x74) (by decide)
    rw [k1 20 (by decide), r20, k1 a1 (by decide), ra1, add_lit_zero] at u2
    have hc2 := CodeIn.store8 (v := tag) hc
      (env.sOC.sub (c := 0) (l := 1) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
    obtain ⟨n3, d3, u3⟩ := u2.sb hc2 es_at_74 (off' := 0x78) (by decide)
    rw [v1, k1 9 (by decide), rs1, add_lit_zero] at u3
    have hc3 := CodeIn.store8 (v := b) hc2 (env.sOC.sub (c := k) (l := 1) (by omega))
    have hne : ∀ j, j < 0xD0 → F + BitVec.ofNat 32 j ≠ out + BitVec.ofNat 32 k := fun j hj e =>
      outF j hj k (by omega) 0 (by decide) (by rw [add_ofNat_zero]; exact e.symm)
    have hne0 : ∀ j, j < 0xD0 → F + BitVec.ofNat 32 j ≠ out := fun j hj e =>
      outF j hj 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)
    obtain ⟨n', S', pc', mem', sp', k'⟩ := fin (S.trans (.cons d1 (.cons d2 (.single d3)))) u3.self hc3
      (fun j h1 h2 => by rw [memStore8_ne (hne j (by omega)), memStore8_ne (hne0 j (by omega))]; exact hsl j h1 h2)
      (by rw [u3.regs, k1 sp (by decide), rsp]) (fun q hq => by
        rw [u3.regs, k1 q (fun e => by subst e; revert hq; decide)]; exact kq q hq)
    exact ⟨n', S', pc', mem', sp', k'⟩
  obtain ⟨m5, c5, pc5, sp5, k5, f5⟩ := derSequence_correct m4 (even_at P env.hP 0xFFFFFD56 (by decide))
    (by rw [mem4]; exact hcB env.seq sGQ) hNE pc4 sp4 (by rw [r4 a0 (by decide), e3a0, sp2])
    (by rw [r4 a1 (by decide), e3a1, sp2]) (by rw [regs4]; simp +decide [upd])
    (even_clear _ (even_at P env.hP (0x1C + 8) (by decide)))
  have eL : memBytes Mb p n = memBytes m.mem p n :=
    memBytes_congr fun i hi => frBG _ (sDG.sub (c := i) (l := 1) (by omega)).symm
  rw [mem4, lP, lN, ofNat_tn hn, eL] at f5
  generalize hR : derElement 0x30 (memBytes m.mem p n) = R at f5
  have S5 : Steps m m5 := .cons d1 (c2.trans (c3.trans (c4.trans c5)))
  have K5 : ∀ q, q.val ∈ [3, 4, 9, 18, 19, 21, 22, 23, 24, 25, 26, 27] → reg m5 q = reg m q := fun q hq => by
    have ho : oidKeep q = true := by revert hq; revert q; decide
    have h : q ≠ ra ∧ q ≠ (20 : Fin 32) ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ sp := by revert hq; revert q; decide
    rw [k5 q ho, r4 q h.1, k3 q h.2.1 h.2.2.1 h.2.2.2.1, r2 q h.2.2.2.2]
  have s205 : reg m5 20 = out := by
    rw [k5 20 (by decide), r4 20 (by decide), e320, r2 a0 (by decide), ha0]
  have u5 : St m5.mem P m5 0x24 (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  have memN : ∀ x, Sep G 0x170 x 1 → m5.mem x = m.mem x := fun x hx => by
    rw [f5 x (by rw [eNF]; exact hx.sub (by decide)),
      nestedMem_outside (out := F + 0x58) R ((inF hx).sub (c := 0x58) (l := 16) (by decide)),
      derAdvance_outside R (by rw [BitVec.add_assoc]; exact (inF hx).sub (c := 0x10) (l := 8) (by decide)), frBG x hx]
  have hcN : ∀ {b : Word} {code' : List Nat}, CodeIn m.mem b code' → Sep G 0x170 b code'.length →
      CodeIn m5.mem b code' := fun hc hs => cIn hc hs memN
  have hc5 := hcN env.cod sGC
  -- the frame above `Der::sequence`'s and below the slots, by offset
  have f5k : ∀ k, k < 0xD0 → m5.mem (F + BitVec.ofNat 32 k) =
      derNestedMem (derAdvance Mb (F + 8) p (BitVec.ofNat 32 n) R) (F + 0x58) p R (F + BitVec.ofNat 32 k) :=
    fun k hk => f5 _ (by
      rw [eNF, eFk]; exact sep_offsets G (.inl (by omega)) (by decide) (by omega))
  have slot5 : ∀ j, 0xB8 ≤ j → j < 0xD0 → m5.mem (F + BitVec.ofNat 32 j) = Msv (F + BitVec.ofNat 32 j) :=
    fun j h1 h2 => by
      rw [f5k j h2, nestedMem_outside (out := F + 0x58) R (sepF (c := 0x58) (n := 16) (.inl (by omega)) (by omega) h2),
        derAdvance_outside R (by rw [BitVec.add_assoc]; exact sepF (c := 0x10) (n := 8) (.inl (by omega)) (by omega) h2),
        frB _ (sepF (c := 8) (n := 16) (.inl (by omega)) (by omega) h2)]
  obtain ⟨m6, d6, u6⟩ := u5.lw hc5 es_at_24 (off' := 0x26) (by decide) (by
    rw [sp5]; exact aligned_add hFa (k := 0x58) (by decide))
  obtain ⟨m7, d7, u7⟩ := u6.self.lbu hc5 es_at_26 (off' := 0x2A) (by decide)
  have l58 : memLoad32 m5.mem (F + 0x58) = memLoad32 (derNestedMem (derAdvance Mb (F + 8) p (BitVec.ofNat 32 n) R)
      (F + 0x58) p R) (F + 0x58) := memLoad32_congr fun j hj => by
    rw [show F + 0x58 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x58 + j) by rw [← add_ofNat_assoc]; rfl,
      f5k _ (by omega)]
  have v7s0 : reg m7 8 = memLoad32 m5.mem (F + 0x58) := by
    rw [u7.regs, upd_ne' (by decide) u6.self.zero, u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5]
  have v7s1 : reg m7 9 = (m5.mem (F + 0x5C)).zeroExtend 32 := by
    rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u6.regs, upd_ne' (by decide) u5.zero, sp5]
  have k7 : ∀ q, q ≠ 8 → q ≠ 9 → reg m7 q = reg m5 q := fun q h8 h9 => by
    rw [u7.regs, upd_ne' h9 u6.self.zero, u6.regs, upd_ne' h8 u5.zero]
  have h5C : m5.mem (F + 0x5C) = derNestedMem (derAdvance Mb (F + 8) p (BitVec.ofNat 32 n) R) (F + 0x58) p R
      (F + 0x58 + 4) := by
    rw [show F + 0x58 + 4 = F + BitVec.ofNat 32 0x5C by rw [BitVec.add_assoc]; rfl, ← f5k _ (by decide)]; rfl
  have eSc : F + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x90 := by rw [← hGF, BitVec.add_assoc]; rfl
  -- a call to `memcpy` through its stub
  have mcCall : ∀ {Mx : Word → BitVec 8} {n : Machine} {o : Nat} {imm oo dst src : Word} {N : Nat},
      St Mx P n o (reg n) → CodeIn Mx P ecdsaSignature48Code →
      fetchRel ecdsaSignature48Code o = some (.auipc ra imm, 4) →
      fetchRel ecdsaSignature48Code (o + 4) = some (.jalr ra ra oo, 4) →
      P + BitVec.ofNat 32 o + imm + oo = P + 0xC6DA → (o + 8) % 2 = 0 →
      CodeIn Mx (P + 0xC6DA) memcpyStubCode → CodeIn Mx (P + 0xC6E2) memcpyBodyCode →
      reg n sp = F → reg n a0 = dst → reg n a1 = src → reg n a2 = BitVec.ofNat 32 N →
      Sep dst N (P + 0xC6E2) memcpyBodyCode.length → Sep dst N (G + BitVec.ofNat 32 0x90) 16 →
      Sep src N (G + BitVec.ofNat 32 0x90) 16 → Sep dst N src N → dst.toNat + N < 2 ^ 32 → src.toNat + N < 2 ^ 32 →
      ∃ n', Steps n n' ∧ St n'.mem P n' (o + 8) (reg n') ∧ reg n' sp = F ∧
        (∀ x, Sep (G + BitVec.ofNat 32 0x90) 16 x 1 → n'.mem x = copyBytes Mx dst src N x) ∧
        ∀ r, r.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' r = reg n r := by
    intro Mx n o imm oo dst src N st hc h1 h2 hb ho hcs hcb rsp ra0 ra1 ra2 sDB sDF sSF sDS hdw hsw
    obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa hc h1 h2 (cb := P + 0xC6DA) hb (even_at P env.hP 0xC6DA (by decide))
    have r1 := PEnv.reg1 regs1 st.zero
    have sp1 : reg n1 sp = F := by rw [r1 sp (by decide), rsp]
    obtain ⟨n2, c2, pc2, sp2', a02, mem2, k2⟩ := memcpy_correct n1 (P + 0xC6DA) (P + BitVec.ofNat 32 (o + 8))
      dst src N (by show CodeIn n1.mem _ _; rw [mem1]; exact hcs) (even_at P env.hP 0xC6DA (by decide)) pc1
      (by rw [r1 a0 (by decide), ra0]) (by rw [r1 a1 (by decide), ra1]) (by rw [r1 a2 (by decide), ra2])
      (by rw [regs1]; simp +decide [upd]) (even_clear _ (even_at P env.hP (o + 8) ho))
      (by
        rw [mem1, sp1, eSc, show P + 0xC6DA + 8 = P + 0xC6E2 by rw [BitVec.add_assoc]; rfl]
        exact ⟨hcb, sDB, (sGB.sub (c := 0x90) (l := 16) (by decide)), sDF, sSF, sDS,
          aligned_add hGa (k := 0x90) (by decide), by rw [BitVec.toNat_add, ofNat_tn (by decide)]; omega, hdw, hsw⟩)
    refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2', sp1], fun x hx => ?_, fun r hr => ?_⟩
    · rw [mem2 x (by rw [sp1, eSc]; exact hx), mem1]
    · obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15⟩ :=
        (by decide : ∀ r : Fin 32, r.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
          r ≠ a1 ∧ r ≠ a2 ∧ r ≠ a3 ∧ r ≠ a4 ∧ r ≠ a5 ∧ r ≠ a6 ∧ r ≠ a7 ∧ r ≠ t0 ∧ r ≠ t1 ∧ r ≠ (7 : Fin 32) ∧
          r ≠ (28 : Fin 32) ∧ r ≠ (29 : Fin 32) ∧ r ≠ (30 : Fin 32) ∧ r ≠ sp ∧ r ≠ ra) r hr
      rw [k2 r q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14, r1 r q15]
  have eG' : F + 0xFFFFFF60 = G := by rw [← hGF, BitVec.add_assoc]; exact BitVec.add_zero G
  have inG : ∀ {b : Word} {l : Nat}, Sep G 0x170 b l → Sep G 0xA0 b l := fun h =>
    (h.sub (c := 0) (l := 0xA0) (by decide)) |> fun h' => by rwa [add_ofNat_zero] at h'
  have e20 : F + 0x18 + 8 = F + BitVec.ofNat 32 0x20 := by rw [BitVec.add_assoc]; rfl
  have e24 : F + 0x18 + 0xC = F + BitVec.ofNat 32 0x24 := by rw [BitVec.add_assoc]; rfl
  -- a call to `der::scalar::<48>` with the result at `sp + 0x58` and the reader at `sp + 0x18`
  have dsCall : ∀ {Mx : Word → BitVec 8} {nm : Machine} {o : Nat} {oo q : Word} {c k : Nat},
      St Mx P nm o (reg nm) → CodeIn Mx P ecdsaSignature48Code →
      fetchRel ecdsaSignature48Code o = some (.aluImm .add a0 sp 0x58, 2) →
      fetchRel ecdsaSignature48Code (o + 2) = some (.aluImm .add a1 sp 0x18, 2) →
      fetchRel ecdsaSignature48Code (o + 4) = some (.auipc ra 0, 4) →
      fetchRel ecdsaSignature48Code (o + 4 + 4) = some (.jalr ra ra oo, 4) →
      P + BitVec.ofNat 32 (o + 4) + 0 + oo = P + 0x10C → (o + 4 + 8) % 2 = 0 →
      (∀ x, Sep G 0x170 x 1 → Mx x = m.mem x) → reg nm sp = F →
      memLoad32 Mx (F + 0x18 + 8) = q → memLoad32 Mx (F + 0x18 + 0xC) = BitVec.ofNat 32 k →
      q = p + BitVec.ofNat 32 c → c + k ≤ n →
      ∃ n', Steps nm n' ∧ St n'.mem P n' (o + 4 + 8) (reg n') ∧ reg n' sp = F ∧
        (∀ r, r.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' r = reg nm r) ∧
        match derScalarOf 48 (memBytes m.mem q k) q (derElement 2 (memBytes m.mem q k)) with
        | .ok bs => n'.mem (F + 0x58) = 0 ∧
            (∀ j, j < 48 → n'.mem (F + 0x58 + BitVec.ofNat 32 (1 + j)) = BitVec.ofNat 8 (bs.getD j 0)) ∧
            ∀ x, Sep G 0xA0 x 1 → Sep (F + 0x58) 49 x 1 →
              n'.mem x = derAdvance Mx (F + 0x18) q (BitVec.ofNat 32 k) (derElement 2 (memBytes m.mem q k)) x
        | .error b => n'.mem (F + 0x58) = 1 ∧ n'.mem (F + 0x58 + 1) = b ∧
            ∀ x, Sep G 0xA0 x 1 → Sep (F + 0x58) 2 x 1 →
              n'.mem x = derAdvance Mx (F + 0x18) q (BitVec.ofNat 32 k) (derElement 2 (memBytes m.mem q k)) x := by
    intro Mx nm o oo q c k st hc h0 h1 h2 h3 hb ho hO rsp lq lk hq hck
    have hk : k < 2 ^ 32 := by omega
    have hqn : q.toNat = p.toNat + c := by
      rw [hq, BitVec.toNat_add, ofNat_tn (by omega)]; have := env.hpn; omega
    obtain ⟨n1, d1, u1⟩ := st.aluImm hc h0 (off' := o + 2) (ofNat_add_ofNat o 2)
    obtain ⟨n2, d2, u2⟩ := u1.self.aluImm hc h1 (off' := o + 4) (by rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, ofNat_add_ofNat])
    obtain ⟨n3, c3, pc3, mem3, regs3⟩ := u2.self.callRa hc h2 h3 (cb := P + 0x10C) hb
      (even_at P env.hP 0x10C (by decide))
    have r3 := PEnv.reg1 regs3 u2.self.zero
    have k2 : ∀ r, r ≠ a0 → r ≠ a1 → reg n2 r = reg nm r := fun r q0 q1 => by
      rw [u2.regs, upd_ne' q1 u1.self.zero, u1.regs, upd_ne' q0 st.zero]
    have sp3 : reg n3 sp = F := by rw [r3 sp (by decide), k2 sp (by decide) (by decide), rsp]
    have hDS : DSEnv n3.mem (P + 0x10C) F (F + 0x58) (F + 0x18) := by
      have sDq : Sep q k G 0x170 := by rw [hq]; exact sDG.sub (by omega)
      have toG : ∀ {b : Word} {l : Nat}, Sep G 0xA0 b l → Sep (F + 0xFFFFFF60) 0xA0 b l := fun h => by
        rw [eG']; exact h
      have toG' : ∀ {b : Word} {l : Nat}, Sep b l G 0xA0 → Sep b l (F + 0xFFFFFF60) 0xA0 := fun h => by
        rw [eG']; exact h
      rw [mem3]
      refine ⟨even_at P env.hP 0x10C (by decide), cIn env.sc sGS hO,
        by rw [BitVec.add_assoc]; exact cIn env.pint sGP hO,
        by rw [BitVec.add_assoc, BitVec.add_assoc]; exact cIn env.int sGI hO,
        by rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; exact cIn env.elem sGE hO,
        by rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; exact cIn env.tlv sGT hO,
        by rw [BitVec.add_assoc]; exact cIn env.zip sGZ hO,
        by rw [BitVec.add_assoc]; exact cIn env.mset sGM hO,
        by rw [BitVec.add_assoc]; exact cIn env.mcs sGU hO,
        by rw [BitVec.add_assoc]; exact cIn env.mcb sGB hO,
        hFa, by omega, aligned_add hFa (k := 0x18) (by decide),
        by rw [BitVec.toNat_add, show (0x58 : Word).toNat = 0x58 from rfl]; have := sp0.isLt; omega,
        toG (inG sGS), by rw [BitVec.add_assoc]; exact toG (inG sGP),
        by rw [BitVec.add_assoc, BitVec.add_assoc]; exact toG (inG sGI),
        by rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; exact toG (inG sGE),
        by rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; exact toG (inG sGT),
        by rw [BitVec.add_assoc]; exact toG (inG sGZ), by rw [BitVec.add_assoc]; exact toG (inG sGM),
        by rw [BitVec.add_assoc]; exact toG (inG sGU), by rw [BitVec.add_assoc]; exact toG (inG sGB),
        sFk 0x58 49 (by decide) sGS, by rw [BitVec.add_assoc]; exact sFk 0x58 49 (by decide) sGB,
        toG' (by
          rw [show F + 0x58 = F + BitVec.ofNat 32 0x58 from rfl, eFk]
          have := sep_offsets G (c := 0xF8) (n := 49) (d := 0) (k := 0xA0) (.inr (by decide)) (by decide) (by decide)
          rwa [add_ofNat_zero] at this),
        by rw [e20]; exact sFk 0x20 8 (by decide) sGS, by rw [e20, BitVec.add_assoc]; exact sFk 0x20 8 (by decide) sGZ,
        by rw [e20, BitVec.add_assoc]; exact sFk 0x20 8 (by decide) sGM,
        by rw [e20, BitVec.add_assoc]; exact sFk 0x20 8 (by decide) sGU,
        by rw [e20, BitVec.add_assoc]; exact sFk 0x20 8 (by decide) sGB,
        by rw [e20, BitVec.add_assoc]; exact sFk 0x20 8 (by decide) sGP,
        by rw [e20, BitVec.add_assoc, BitVec.add_assoc]; exact sFk 0x20 8 (by decide) sGI,
        by rw [e20, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]; exact sFk 0x20 8 (by decide) sGT,
        toG' (by
          rw [e20, eFk]
          have := sep_offsets G (c := 0xC0) (n := 8) (d := 0) (k := 0xA0) (.inr (by decide)) (by decide) (by decide)
          rwa [add_ofNat_zero] at this),
        by rw [lq, lk, ofNat_tn hk]; exact toG' (inG sDq.symm).symm,
        by rw [lq, lk, ofNat_tn hk, e20, eFk]; exact (sDq.subR (c := 0xA0 + 0x20) (l := 8) (by decide)).symm,
        by rw [lq]; have := env.hp; omega, by rw [lq, lk, ofNat_tn hk]; have := env.hpn; omega⟩
    obtain ⟨n4, c4, pc4, sp4, k4, h4⟩ := derScalar48_correct n3 hDS pc3 sp3
      (by rw [r3 a0 (by decide), u2.regs, upd_ne' (by decide) u1.self.zero, u1.regs]
          simp +decide only [upd_app, ↓reduceIte]; rw [rsp]; rfl)
      (by rw [r3 a1 (by decide), u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u1.regs, upd_ne' (by decide) st.zero, rsp]; rfl)
      (by rw [regs3]; simp +decide [upd]) (even_clear _ (even_at P env.hP (o + 4 + 8) ho))
    have eB : memBytes n3.mem q k = memBytes m.mem q k := by
      rw [mem3]; exact memBytes_congr fun i hi => by
        rw [hq, add_ofNat_assoc]; exact hO _ (sDG.sub (c := c + i) (l := 1) (by omega)).symm
    rw [mem3, eG', lq, lk, ofNat_tn hk, ← mem3, eB, mem3] at h4
    refine ⟨n4, .cons d1 (.cons d2 (c3.trans c4)), ⟨by rw [pc4], rfl, fun _ => rfl⟩, by rw [sp4],
      fun r hr => ?_, h4⟩
    · have h' : r ≠ ra ∧ r ≠ a0 ∧ r ≠ a1 := by revert hr; revert r; decide
      rw [k4 r (by revert hr; revert r; decide), r3 r h'.1, k2 r h'.2.1 h'.2.2]
  cases R with
  | error e =>
    obtain ⟨z0, z4⟩ := nestedMem_err (M := derAdvance Mb (F + 8) p (BitVec.ofNat 32 n) (.error e)) (out := F + 0x58)
      (rp := p) e
    obtain ⟨m8, d8, u8⟩ := u7.self.taken hc5 0x6A es_at_2a (by decide) (by rw [v7s0, l58, z0, u7.self.zero]; rfl)
    obtain ⟨m9, d9, u9⟩ := u8.self.aluImm hc5 es_at_6a (off' := 0x6C) (by decide)
    obtain ⟨m10, d10, u10⟩ := u9.self.aluImm hc5 es_at_6c (off' := 0x6E) (by decide)
    have k10 : ∀ q, q ≠ a0 → q ≠ a1 → reg m10 q = reg m7 q := fun q h0 h1 => by
      rw [u10.regs, upd_ne' h1 u9.self.zero, u9.regs, upd_ne' h0 u8.self.zero, u8.regs]
    obtain ⟨n', S', pc', mem', sp', k'⟩ := tail (k := 1) (tag := 1) (b := derErrByte e)
      (S5.trans (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.single d10)))))) u10.self hc5
      slot5
      (by rw [k10 sp (by decide) (by decide), k7 sp (by decide) (by decide), sp5])
      (by rw [k10 20 (by decide) (by decide), k7 20 (by decide) (by decide), s205])
      (by rw [u10.regs, upd_ne' (by decide) u9.self.zero, u9.regs]; simp +decide only [upd_app, ↓reduceIte];
          rw [u8.self.zero]; rfl) (by decide) (by decide)
      (by rw [u10.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u9.self.zero]; rfl)
      (by rw [k10 9 (by decide) (by decide), v7s1, h5C, z4, tlv_zext])
      (fun q hq => by
        rw [k10 q (fun e => by subst e; revert hq; decide) (fun e => by subst e; revert hq; decide),
          k7 q (fun e => by subst e; revert hq; decide) (fun e => by subst e; revert hq; decide)]
        exact K5 q (by revert hq; revert q; decide))
    have hspec : ecdsaSigOf 48 m.mem p n = .error (derErrByte e) := by unfold ecdsaSigOf; rw [hR]
    have h1 : out ≠ out + BitVec.ofNat 32 1 := fun h => by
      have := congrArg BitVec.toNat h; rw [BitVec.toNat_add, ofNat_tn (by decide)] at this; have := env.how; omega
    refine ⟨n', S', pc', sp', k', fun x hx ho => ?_, ?_⟩
    · rw [mem', memStore8_ne fun e' => ho.point (i := 1) (j := 0) (by decide) (by decide)
          (by rw [add_ofNat_zero]; exact e'.symm),
        memStore8_ne fun e' => ho.point (i := 0) (j := 0) (by decide) (by decide)
          (by rw [add_ofNat_zero, add_ofNat_zero]; exact e'.symm), memN x hx]
    · rw [hspec]
      exact ⟨by rw [mem', memStore8_ne h1, memStore8_same], by rw [mem']; exact memStore8_same _ _ _⟩
  | ok t =>
    obtain ⟨z0, z4, z8, zC⟩ := nestedMem_ok (M := derAdvance Mb (F + 8) p (BitVec.ofNat 32 n) (.ok t))
      (out := F + 0x58) (rp := p) t
    have hb : t.header + t.len ≤ n := by have := derElement_bound hR; rwa [memBytes_length] at this
    have hpH : (p + BitVec.ofNat 32 t.header).toNat = p.toNat + t.header := by
      rw [BitVec.toNat_add, ofNat_tn (by omega)]; have := env.hpn; omega
    have hp0 : p + BitVec.ofNat 32 t.header ≠ 0 := fun h => by
      have := congrArg BitVec.toNat h; rw [hpH, show (0 : Word).toNat = 0 from rfl] at this; have := env.hp; omega
    obtain ⟨m8, d8, u8⟩ := u7.self.notTaken hc5 0x2C es_at_2a (by decide) (by
      rw [v7s0, l58, z0, u7.self.zero]; exact beq_false_of_ne hp0)
    obtain ⟨m9, c9, u9⟩ := St.block [.aluImm .add a1 sp 0x5D, .aluImm .add a0 sp 0x1D, .aluImm .add a2 x0 0xB]
      u8.self hc5 (off' := 0x36) (by decide) (by simp [BlockOk, BInstr.ok])
    simp only [runBlock, BInstr.run] at u9
    have k9 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m9 q = reg m7 q := fun q h0 h1 h2 => by
      rw [u9.regs, updz ((updz (upd_zero _ _ _) (by decide)).trans (upd_zero _ _ _)) h2, updz (upd_zero _ _ _) h0,
        updz u8.self.zero h1, u8.regs]
    have sp9 : reg m9 sp = F := by rw [k9 sp (by decide) (by decide) (by decide), k7 sp (by decide) (by decide), sp5]
    obtain ⟨m10, c10, u10, sp10, f10, k10⟩ := mcCall (dst := F + 0x1D) (src := F + 0x5D) (N := 11) u9.self hc5
      es_at_36 es_at_3a (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (hcN env.mcs sGU)
      (hcN env.mcb sGB) sp9
      (by rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u8.regs, k7 sp (by decide) (by decide), sp5]; rfl)
      (by rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u8.regs, k7 sp (by decide) (by decide), sp5]; rfl)
      (by rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte])
      (sFk 0x1D 11 (by decide) sGB)
      (by rw [show F + 0x1D = F + BitVec.ofNat 32 0x1D from rfl, eFk]
          exact sep_offsets G (.inr (by decide)) (by decide) (by decide))
      (by rw [show F + 0x5D = F + BitVec.ofNat 32 0x5D from rfl, eFk]
          exact sep_offsets G (.inr (by decide)) (by decide) (by decide))
      (sep_offsets F (c := 0x1D) (n := 11) (d := 0x5D) (k := 11) (.inl (by decide)) (by decide) (by decide))
      (by rw [BitVec.toNat_add, show (0x1D : Word).toNat = 0x1D from rfl]; have := sp0.isLt; omega)
      (by rw [BitVec.toNat_add, show (0x5D : Word).toNat = 0x5D from rfl]; have := sp0.isLt; omega)
    have m10F : ∀ k, k < 0xD0 → m10.mem (F + BitVec.ofNat 32 k) =
        copyBytes m5.mem (F + 0x1D) (F + 0x5D) 11 (F + BitVec.ofNat 32 k) := fun k hk =>
      f10 _ (by rw [eFk]; exact sep_offsets G (.inl (by omega)) (by decide) (by omega))
    have m10O : ∀ x, Sep G 0x170 x 1 → m10.mem x = m.mem x := fun x hx => by
      rw [f10 x (hx.sub (c := 0x90) (l := 16) (by decide)), copyBytes_sep (dst := F + 0x1D) (n := 11) (sFk 0x1D 11 (by decide) hx) (Nat.le_refl _),
        memN x hx]
    have hc10 : CodeIn m10.mem P ecdsaSignature48Code := cIn env.cod sGC m10O
    obtain ⟨m11, d11, u11⟩ := u10.lw hc10 es_at_3e (off' := 0x40) (by decide) (by
      rw [sp10]; exact aligned_add hFa (k := 0x14) (by decide))
    have k11 : ∀ q, q ≠ a2 → reg m11 q = reg m10 q := fun q h => by rw [u11.regs, upd_ne' h u10.zero]
    have m5o : ∀ k, k < 0xD0 → (k + 1 ≤ 0x58 ∨ 0x68 ≤ k) → m5.mem (F + BitVec.ofNat 32 k) =
        derAdvance Mb (F + 8) p (BitVec.ofNat 32 n) (.ok t) (F + BitVec.ofNat 32 k) := fun k hk h => by
      rw [f5k k hk, nestedMem_outside (out := F + 0x58) (.ok t)
        (sepF (c := 0x58) (n := 16) (by omega) (by decide) hk)]
    have l14 : memLoad32 m10.mem (F + 0x14) = BitVec.ofNat 32 n - BitVec.ofNat 32 (t.header + t.len) := by
      rw [← (derAdvance_ld (M := Mb) (d := F + 8) (rp := p) (rl := BitVec.ofNat 32 n) t).2,
        show F + 8 + 0xC = F + 0x14 by rw [BitVec.add_assoc]; rfl]
      apply memLoad32_congr; intro j hj
      rw [show F + 0x14 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x14 + j) by rw [← add_ofNat_assoc]; rfl,
        m10F _ (by omega), copyBytes_sep (dst := F + 0x1D) (n := 11)
          (sepF (c := 0x1D) (n := 11) (k := 0x14 + j) (.inr (by omega)) (by decide) (by omega))
          (Nat.le_refl _), m5o _ (by omega) (.inl (by omega))]
    have v11 : reg m11 a2 = BitVec.ofNat 32 (n - (t.header + t.len)) := by
      rw [u11.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp10, l14]; exact sub_val hb hn
    have s8_10 : reg m10 8 = p + BitVec.ofNat 32 t.header := by
      rw [k10 8 (by decide), k9 8 (by decide) (by decide) (by decide), v7s0, l58, z0]
    have s9_10 : reg m10 9 = (m5.mem (F + 0x5C)).zeroExtend 32 := by
      rw [k10 9 (by decide), k9 9 (by decide) (by decide) (by decide), v7s1]
    obtain ⟨m12, d12, u12⟩ := u11.self.sw hc10 es_at_40 (off' := 0x42) (by decide) (by
      rw [k11 sp (by decide), sp10]; exact aligned_add hFa (k := 0x18) (by decide))
    rw [k11 sp (by decide), sp10, k11 8 (by decide), s8_10] at u12
    have hc12 := CodeIn.store32 (a := F + 0x18) (v := p + BitVec.ofNat 32 t.header) hc10
      ((inF sGC).sub (c := 0x18) (l := 4) (by decide))
    obtain ⟨m13, d13, u13⟩ := u12.sb hc12 es_at_42 (off' := 0x46) (by decide)
    rw [k11 sp (by decide), sp10, k11 9 (by decide), s9_10, tlv_zext] at u13
    obtain ⟨M13, hM13⟩ : ∃ M, memStore8 (memStore32 m10.mem (F + 0x18) (p + BitVec.ofNat 32 t.header)) (F + 0x1C)
        (m5.mem (F + 0x5C)) = M := ⟨_, rfl⟩
    rw [hM13] at u13
    have hc13 : CodeIn M13 P ecdsaSignature48Code := by
      rw [← hM13]; exact CodeIn.store8 hc12 ((inF sGC).sub (c := 0x1C) (l := 1) (by decide))
    have M13O : ∀ x, Sep G 0x170 x 1 → M13 x = m.mem x := fun x hx => by
      rw [← hM13, memStore8_ne fun e => (sFk 0x1C 1 (by decide) hx).point (i := 0) (j := 0) (by decide) (by decide)
          (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm),
        memStore32_get_sep (a := F + 0x18) (sFk 0x18 4 (by decide) hx), m10O x hx]
    obtain ⟨m14, c14, u14⟩ := St.block [.aluImm .add a0 x0 1, .aluImm .add (9 : Fin 32) x0 1, .aluImm .add a1 x0 1]
      u13.self hc13 (off' := 0x4C) (by decide) (by simp [BlockOk, BInstr.ok])
    simp only [runBlock, BInstr.run] at u14
    have k14 : ∀ q, q ≠ a0 → q ≠ (9 : Fin 32) → q ≠ a1 → reg m14 q = reg m11 q := fun q h0 h9 h1 => by
      rw [u14.regs, updz ((updz (upd_zero _ _ _) (by decide)).trans (upd_zero _ _ _)) h1, updz (upd_zero _ _ _) h9,
        updz u13.self.zero h0, u13.regs]
    have v14 : reg m14 a2 = BitVec.ofNat 32 (n - (t.header + t.len)) := by
      rw [k14 a2 (by decide) (by decide) (by decide), v11]
    have S14 : Steps m m14 := S5.trans (.cons d6 (.cons d7 (.cons d8 (c9.trans (c10.trans
      (.cons d11 (.cons d12 (.cons d13 c14))))))))
    have K14 : ∀ q, q.val ∈ [3, 4, 18, 19, 21, 22, 23, 24, 25, 26, 27] → reg m14 q = reg m q := fun q hq => by
      have h : q ≠ a0 ∧ q ≠ (9 : Fin 32) ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ (8 : Fin 32) := by revert hq; revert q; decide
      rw [k14 q h.1 h.2.1 h.2.2.1, k11 q h.2.2.2.1, k10 q (by revert hq; revert q; decide),
        k9 q h.1 h.2.2.1 h.2.2.2.1, k7 q h.2.2.2.2 h.2.1]
      exact K5 q (by revert hq; revert q; decide)
    have sp14 : reg m14 sp = F := by
      rw [k14 sp (by decide) (by decide) (by decide), k11 sp (by decide), sp10]
    have s20_14 : reg m14 20 = out := by
      rw [k14 20 (by decide) (by decide) (by decide), k11 20 (by decide), k10 20 (by decide),
        k9 20 (by decide) (by decide) (by decide), k7 20 (by decide) (by decide), s205]
    have slot13 : ∀ j, 0xB8 ≤ j → j < 0xD0 → M13 (F + BitVec.ofNat 32 j) = Msv (F + BitVec.ofNat 32 j) :=
      fun j h1 h2 => by
        rw [← hM13, memStore8_ne fun e => (sepF (c := 0x1C) (n := 1) (.inl (by omega)) (by decide) h2).point
            (i := 0) (j := 0) (by decide) (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm),
          memStore32_get_sep (a := F + 0x18) (sepF (c := 0x18) (n := 4) (.inl (by omega)) (by decide) h2), m10F j h2,
          copyBytes_sep (dst := F + 0x1D) (n := 11) (sepF (c := 0x1D) (n := 11) (.inl (by omega)) (by decide) h2) (Nat.le_refl _),
          slot5 j h1 h2]
    by_cases hfin : t.header + t.len = n
    · obtain ⟨m15, d15, u15⟩ := u14.self.notTaken hc13 0x4E es_at_4c (by decide) (by
        rw [v14, u14.self.zero, hfin, Nat.sub_self]; rfl)
      have cp : ∀ j, j < 8 → M13 (F + BitVec.ofNat 32 (0x20 + j)) = m5.mem (F + BitVec.ofNat 32 (0x60 + j)) :=
        fun j hj => by
          rw [← hM13, memStore8_ne fun e => (sepF (c := 0x1C) (n := 1) (k := 0x20 + j) (.inl (by omega)) (by decide)
              (by omega)).point (i := 0) (j := 0) (by decide) (by decide)
              (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm),
            memStore32_get_sep (a := F + 0x18) (sepF (c := 0x18) (n := 4) (k := 0x20 + j) (.inl (by omega)) (by decide)
              (by omega)), m10F _ (by omega),
            show F + BitVec.ofNat 32 (0x20 + j) = F + 0x1D + BitVec.ofNat 32 (3 + j) by
              rw [show (0x1D : Word) = BitVec.ofNat 32 0x1D from rfl, add_ofNat_assoc, show 0x1D + (3 + j) = 0x20 + j by omega],
            ds_copy_in (by omega) (by decide),
            show F + 0x5D + BitVec.ofNat 32 (3 + j) = F + BitVec.ofNat 32 (0x60 + j) by
              rw [show (0x5D : Word) = BitVec.ofNat 32 0x5D from rfl, add_ofNat_assoc, show 0x5D + (3 + j) = 0x60 + j by omega]]
      have lq : memLoad32 M13 (F + 0x18 + 8) = p + BitVec.ofNat 32 t.header := by
        rw [e20, ← z8]
        calc memLoad32 M13 (F + BitVec.ofNat 32 0x20) = memLoad32 m5.mem (F + BitVec.ofNat 32 0x60) :=
              memLoad32_congr2 fun jj hj => by rw [add_ofNat_assoc, add_ofNat_assoc, cp jj (by omega)]
          _ = _ := by
              rw [show F + 0x58 + 8 = F + BitVec.ofNat 32 0x60 by rw [BitVec.add_assoc]; rfl]
              exact memLoad32_congr fun jj hj => by rw [add_ofNat_assoc, f5k _ (by omega)]
      have lk : memLoad32 M13 (F + 0x18 + 0xC) = BitVec.ofNat 32 t.len := by
        rw [e24, ← zC]
        calc memLoad32 M13 (F + BitVec.ofNat 32 0x24) = memLoad32 m5.mem (F + BitVec.ofNat 32 0x64) :=
              memLoad32_congr2 fun jj hj => by
                rw [add_ofNat_assoc, add_ofNat_assoc, show 0x24 + jj = 0x20 + (4 + jj) by omega, cp _ (by omega),
                  show 0x60 + (4 + jj) = 0x64 + jj by omega]
          _ = _ := by
              rw [show F + 0x58 + 0xC = F + BitVec.ofNat 32 0x64 by rw [BitVec.add_assoc]; rfl]
              exact memLoad32_congr fun jj hj => by rw [add_ofNat_assoc, f5k _ (by omega)]
      obtain ⟨m16, c16, u16, sp16, k16, h16⟩ := dsCall (o := 0x4E) (c := t.header) u15.self hc13 es_at_4e es_at_50
        es_at_52 es_at_56 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) M13O
        (by rw [u15.regs, sp14]) lq lk rfl (by omega)
      have S16 : Steps m m16 := S14.trans (.cons d15 c16)
      have K16 : ∀ q, q.val ∈ [3, 4, 18, 19, 21, 22, 23, 24, 25, 26, 27] → reg m16 q = reg m q := fun q hq => by
        rw [k16 q (by revert hq; revert q; decide), u15.regs]; exact K14 q hq
      have s20_16 : reg m16 20 = out := by rw [k16 20 (by decide), u15.regs, s20_14]
      cases hS1 : derScalarOf 48 (memBytes m.mem (p + BitVec.ofNat 32 t.header) t.len) (p + BitVec.ofNat 32 t.header)
          (derElement 2 (memBytes m.mem (p + BitVec.ofNat 32 t.header) t.len)) with
      | error b1 =>
        rw [hS1] at h16
        obtain ⟨o0, o1, fr16⟩ := h16
        have fr16' : ∀ x, Sep G 0xA0 x 1 → Sep (F + 0x58) 2 x 1 → Sep (F + 0x20) 8 x 1 → m16.mem x = M13 x :=
          fun x h1 h2 h3 => by rw [fr16 x h1 h2, derAdvance_outside _ (by rw [e20]; exact h3)]
        have hc16 : CodeIn m16.mem P ecdsaSignature48Code := cIn env.cod sGC fun x hx => by
          rw [fr16' x (inG hx) (sFk 0x58 2 (by decide) hx) (sFk 0x20 8 (by decide) hx), M13O x hx]
        obtain ⟨m17, d17, u17⟩ := u16.lbu hc16 es_at_5a (off' := 0x5E) (by decide)
        obtain ⟨m18, d18, u18⟩ := u17.self.lbu hc16 es_at_5e (off' := 0x62) (by decide)
        have v18a0 : reg m18 a0 = (1 : BitVec 8).zeroExtend 32 := by
          rw [u18.regs, upd_ne' (by decide) u17.self.zero, u17.regs]; simp +decide only [upd_app, ↓reduceIte]
          rw [sp16, ← o0]
        have v18s3 : reg m18 19 = b1.zeroExtend 32 := by
          rw [u18.regs]; simp +decide only [upd_app, ↓reduceIte]
          rw [u17.regs, upd_ne' (by decide) u16.zero, sp16, show F + 0x59 = F + 0x58 + 1 by rw [BitVec.add_assoc]; rfl,
            o1]
        obtain ⟨m19, d19, u19⟩ := u18.self.notTaken hc16 0x64 es_at_62 (by decide) (by
          rw [v18a0, u18.self.zero]; decide)
        obtain ⟨m20, d20, u20⟩ := u19.self.aluImm hc16 es_at_64 (off' := 0x66) (by decide)
        obtain ⟨m21, d21, u21⟩ := u20.self.alu hc16 es_at_66 (off' := 0x68) (by decide)
        obtain ⟨m22, d22, u22⟩ := u21.self.jump hc16 es_at_68 (off' := 0x6C) (by decide) (by
          rw [u21.self.pc, show P + BitVec.ofNat 32 0x68 + 0x4 = P + BitVec.ofNat 32 0x6C by rw [BitVec.add_assoc]; rfl]
          exact even_bit0 (even_at P env.hP 0x6C (by decide)))
        obtain ⟨m23, d23, u23⟩ := u22.self.aluImm hc16 es_at_6c (off' := 0x6E) (by decide)
        have k23 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ (9 : Fin 32) → q ≠ (19 : Fin 32) → reg m23 q = reg m16 q :=
          fun q h0 h1 h9 h19 => by
            rw [u23.regs, upd_ne' h1 u22.self.zero, u22.regs, u21.regs, upd_ne' h9 u20.self.zero, u20.regs,
              upd_ne' h0 u19.self.zero, u19.regs, u18.regs, upd_ne' h19 u17.self.zero, u17.regs, upd_ne' h0 u16.zero]
        obtain ⟨n', S', pc', mem', sp', k'⟩ := tail (k := 1) (tag := 1) (b := b1)
          (S16.trans (.cons d17 (.cons d18 (.cons d19 (.cons d20 (.cons d21 (.cons d22 (.single d23)))))))) u23.self hc16
          (fun j h1 h2 => by
            rw [fr16' _ (by
                  rw [eFk]
                  have := sep_offsets G (c := 0) (n := 0xA0) (d := 0xA0 + j) (k := 1) (.inl (by omega)) (by decide)
                    (by omega)
                  rwa [add_ofNat_zero] at this)
                (sepF (c := 0x58) (n := 2) (.inl (by omega)) (by decide) h2)
                (sepF (c := 0x20) (n := 8) (.inl (by omega)) (by decide) h2)]
            exact slot13 j h1 h2)
          (by rw [k23 sp (by decide) (by decide) (by decide) (by decide), sp16])
          (by rw [k23 20 (by decide) (by decide) (by decide) (by decide), s20_16])
          (by rw [u23.regs, upd_ne' (by decide) u22.self.zero, u22.regs, u21.regs, upd_ne' (by decide) u20.self.zero,
                u20.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u19.self.zero]; rfl)
          (by decide) (by decide)
          (by rw [u23.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u22.self.zero]; rfl)
          (by rw [u23.regs, upd_ne' (by decide) u22.self.zero, u22.regs, u21.regs]
              simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, show reg m20 x0 = 0 from u20.self.zero, zw, u20.regs, upd_ne' (by decide) u19.self.zero,
                u19.regs, v18s3, tlv_zext])
          (fun q hq => by
            rw [k23 q (fun e => by subst e; revert hq; decide) (fun e => by subst e; revert hq; decide)
              (fun e => by subst e; revert hq; decide) (fun e => by subst e; revert hq; decide)]
            exact K16 q (by revert hq; revert q; decide))
        have hspec : ecdsaSigOf 48 m.mem p n = .error b1 := by
          unfold ecdsaSigOf; rw [hR]; dsimp only; rw [ite_eq_left hfin, hS1]
        have h1 : out ≠ out + BitVec.ofNat 32 1 := fun h => by
          have := congrArg BitVec.toNat h; rw [BitVec.toNat_add, ofNat_tn (by decide)] at this; have := env.how; omega
        refine ⟨n', S', pc', sp', k', fun x hx ho => ?_, ?_⟩
        · rw [mem', memStore8_ne fun e' => ho.point (i := 1) (j := 0) (by decide) (by decide)
              (by rw [add_ofNat_zero]; exact e'.symm),
            memStore8_ne fun e' => ho.point (i := 0) (j := 0) (by decide) (by decide)
              (by rw [add_ofNat_zero, add_ofNat_zero]; exact e'.symm),
            fr16' x (inG hx) (sFk 0x58 2 (by decide) hx) (sFk 0x20 8 (by decide) hx), M13O x hx]
        · rw [hspec]
          exact ⟨by rw [mem', memStore8_ne h1, memStore8_same], by rw [mem']; exact memStore8_same _ _ _⟩
      | ok bs1 =>
        rw [hS1] at h16
        obtain ⟨o0, oj, fr16⟩ := h16
        cases hE1 : derElement 2 (memBytes m.mem (p + BitVec.ofNat 32 t.header) t.len) with
        | error e1 =>
          exfalso; rw [hE1] at hS1; unfold derScalarOf at hS1
          split at hS1
          · rename_i h; cases h
          · cases hS1
          · cases hS1
        | ok t1 =>
        have hb1 : t1.header + t1.len ≤ t.len := by have := derElement_bound hE1; rwa [memBytes_length] at this
        rw [hE1] at fr16
        have fr16' : ∀ x, Sep G 0xA0 x 1 → Sep (F + 0x58) 49 x 1 → Sep (F + 0x20) 8 x 1 → m16.mem x = M13 x :=
          fun x h1 h2 h3 => by rw [fr16 x h1 h2, derAdvance_outside _ (by rw [e20]; exact h3)]
        have M16O : ∀ x, Sep G 0x170 x 1 → m16.mem x = m.mem x := fun x hx => by
          rw [fr16' x (inG hx) (sFk 0x58 49 (by decide) hx) (sFk 0x20 8 (by decide) hx), M13O x hx]
        have hc16 : CodeIn m16.mem P ecdsaSignature48Code := cIn env.cod sGC M16O
        have inA : ∀ j, j < 0xD0 → Sep G 0xA0 (F + BitVec.ofNat 32 j) 1 := fun j hj => by
          rw [eFk]
          have := sep_offsets G (c := 0) (n := 0xA0) (d := 0xA0 + j) (k := 1) (.inl (by omega)) (by decide) (by omega)
          rwa [add_ofNat_zero] at this
        obtain ⟨m17, d17, u17⟩ := u16.lbu hc16 es_at_5a (off' := 0x5E) (by decide)
        obtain ⟨m18, d18, u18⟩ := u17.self.lbu hc16 es_at_5e (off' := 0x62) (by decide)
        have v18a0 : reg m18 a0 = (0 : BitVec 8).zeroExtend 32 := by
          rw [u18.regs, upd_ne' (by decide) u17.self.zero, u17.regs]; simp +decide only [upd_app, ↓reduceIte]
          rw [sp16, ← o0]
        have v18s3 : reg m18 19 = (m16.mem (F + 0x58 + BitVec.ofNat 32 (1 + 0))).zeroExtend 32 := by
          rw [u18.regs]; simp +decide only [upd_app, ↓reduceIte]
          rw [u17.regs, upd_ne' (by decide) u16.zero, sp16,
            show F + 0x58 + BitVec.ofNat 32 (1 + 0) = F + 0x59 by rw [BitVec.add_assoc]; rfl]
        obtain ⟨m19, d19, u19⟩ := u18.self.taken hc16 0x88 es_at_62 (by decide) (by rw [v18a0, u18.self.zero]; decide)
        obtain ⟨m20, c20, u20⟩ := St.block [.aluImm .add a1 sp 0x5A, .aluImm .add a0 sp 0x29, .aluImm .add a2 x0 0x2F]
          u19.self hc16 (off' := 0x94) (by decide) (by simp [BlockOk, BInstr.ok])
        simp only [runBlock, BInstr.run] at u20
        have k20 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m20 q = reg m18 q := fun q h0 h1 h2 => by
          rw [u20.regs, updz ((updz (upd_zero _ _ _) (by decide)).trans (upd_zero _ _ _)) h2, updz (upd_zero _ _ _) h0,
            updz u19.self.zero h1, u19.regs]
        have k18 : ∀ q, q ≠ a0 → q ≠ (19 : Fin 32) → reg m18 q = reg m16 q := fun q h0 h19 => by
          rw [u18.regs, upd_ne' h19 u17.self.zero, u17.regs, upd_ne' h0 u16.zero]
        have sp20 : reg m20 sp = F := by
          rw [k20 sp (by decide) (by decide) (by decide), k18 sp (by decide) (by decide), sp16]
        obtain ⟨m21, c21, u21, sp21, f21, k21⟩ := mcCall (dst := F + 0x29) (src := F + 0x5A) (N := 47) u20.self hc16
          es_at_94 es_at_98 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (hcN env.mcs sGU |> fun h =>
            cIn env.mcs sGU M16O) (cIn env.mcb sGB M16O) sp20
          (by rw [u20.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u19.regs, k18 sp (by decide) (by decide), sp16]; rfl)
          (by rw [u20.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u19.regs, k18 sp (by decide) (by decide), sp16]; rfl)
          (by rw [u20.regs]; simp +decide only [upd_app, ↓reduceIte])
          (sFk 0x29 47 (by decide) sGB)
          (by rw [show F + 0x29 = F + BitVec.ofNat 32 0x29 from rfl, eFk]
              exact sep_offsets G (.inr (by decide)) (by decide) (by decide))
          (by rw [show F + 0x5A = F + BitVec.ofNat 32 0x5A from rfl, eFk]
              exact sep_offsets G (.inr (by decide)) (by decide) (by decide))
          (sep_offsets F (c := 0x29) (n := 47) (d := 0x5A) (k := 47) (.inl (by decide)) (by decide) (by decide))
          (by rw [BitVec.toNat_add, show (0x29 : Word).toNat = 0x29 from rfl]; have := sp0.isLt; omega)
          (by rw [BitVec.toNat_add, show (0x5A : Word).toNat = 0x5A from rfl]; have := sp0.isLt; omega)
        have m21F : ∀ k, k < 0xD0 → m21.mem (F + BitVec.ofNat 32 k) =
            copyBytes m16.mem (F + 0x29) (F + 0x5A) 47 (F + BitVec.ofNat 32 k) := fun k hk =>
          f21 _ (by rw [eFk]; exact sep_offsets G (.inl (by omega)) (by decide) (by omega))
        have M21O : ∀ x, Sep G 0x170 x 1 → m21.mem x = m.mem x := fun x hx => by
          rw [f21 x (hx.sub (c := 0x90) (l := 16) (by decide)),
            copyBytes_sep (dst := F + 0x29) (n := 47) (sFk 0x29 47 (by decide) hx) (Nat.le_refl _), M16O x hx]
        have hc21 : CodeIn m21.mem P ecdsaSignature48Code := cIn env.cod sGC M21O
        -- the reader after `r`
        have r21 : ∀ jj, jj < 8 → m21.mem (F + BitVec.ofNat 32 (0x20 + jj)) =
            derAdvance M13 (F + 0x18) (p + BitVec.ofNat 32 t.header) (BitVec.ofNat 32 t.len) (.ok t1)
              (F + BitVec.ofNat 32 (0x20 + jj)) := fun jj hj => by
          rw [m21F _ (by omega), copyBytes_sep (dst := F + 0x29) (n := 47)
              (sepF (c := 0x29) (n := 47) (k := 0x20 + jj) (.inr (by omega)) (by decide) (by omega)) (Nat.le_refl _),
            fr16 _ (inA _ (by omega)) (sepF (c := 0x58) (n := 49) (k := 0x20 + jj) (.inr (by omega)) (by decide) (by omega))]
        obtain ⟨al8, alC⟩ := derAdvance_ld (M := M13) (d := F + 0x18) (rp := p + BitVec.ofNat 32 t.header)
          (rl := BitVec.ofNat 32 t.len) t1
        have lq2 : memLoad32 m21.mem (F + 0x18 + 8) = p + BitVec.ofNat 32 (t.header + (t1.header + t1.len)) := by
          rw [← add_ofNat_assoc, ← al8, e20]
          exact memLoad32_congr fun jj hj => by rw [add_ofNat_assoc, r21 jj (by omega)]
        have lk2 : memLoad32 m21.mem (F + 0x18 + 0xC) = BitVec.ofNat 32 (t.len - (t1.header + t1.len)) := by
          rw [show BitVec.ofNat 32 (t.len - (t1.header + t1.len)) =
              BitVec.ofNat 32 t.len - BitVec.ofNat 32 (t1.header + t1.len) from (sub_val hb1 (by omega)).symm, ← alC, e24]
          exact memLoad32_congr fun jj hj => by
            rw [add_ofNat_assoc, show 0x24 + jj = 0x20 + (4 + jj) by omega, r21 _ (by omega)]
        obtain ⟨m22, c22, u22, sp22, k22, h22⟩ := dsCall (o := 0x9C) (c := t.header + (t1.header + t1.len)) u21 hc21
          es_at_9c es_at_9e es_at_a0 es_at_a4 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) M21O sp21
          lq2 lk2 rfl (by omega)
        have S22 : Steps m m22 := S16.trans (.cons d17 (.cons d18 (.cons d19 (c20.trans (c21.trans c22)))))
        have K22 : ∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg m22 q = reg m q := fun q hq => by
          have h : q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ (19 : Fin 32) := by revert hq; revert q; decide
          rw [k22 q (by revert hq; revert q; decide), k21 q (by revert hq; revert q; decide), k20 q h.1 h.2.1 h.2.2.1,
            k18 q h.1 h.2.2.2]
          exact K16 q (by revert hq; revert q; decide)
        have s19_22 : reg m22 19 = (m16.mem (F + 0x58 + BitVec.ofNat 32 (1 + 0))).zeroExtend 32 := by
          rw [k22 19 (by decide), k21 19 (by decide), k20 19 (by decide) (by decide) (by decide), v18s3]
        have s20_22 : reg m22 20 = out := by
          rw [k22 20 (by decide), k21 20 (by decide), k20 20 (by decide) (by decide) (by decide),
            k18 20 (by decide) (by decide), s20_16]
        -- the frame after the second call, below the result and the reader
        have slot21 : ∀ j, 0xB8 ≤ j → j < 0xD0 → m21.mem (F + BitVec.ofNat 32 j) = Msv (F + BitVec.ofNat 32 j) :=
          fun j h1 h2 => by
            rw [m21F j h2, copyBytes_sep (dst := F + 0x29) (n := 47) (sepF (c := 0x29) (n := 47) (.inl (by omega))
                (by decide) h2) (Nat.le_refl _),
              fr16' _ (inA j h2) (sepF (c := 0x58) (n := 49) (.inl (by omega)) (by decide) h2)
                (sepF (c := 0x20) (n := 8) (.inl (by omega)) (by decide) h2)]
            exact slot13 j h1 h2
        have hspecA : ecdsaSigOf 48 m.mem p n =
            match derScalarOf 48 (memBytes m.mem (p + BitVec.ofNat 32 (t.header + (t1.header + t1.len)))
                (t.len - (t1.header + t1.len))) (p + BitVec.ofNat 32 (t.header + (t1.header + t1.len)))
                (derElement 2 (memBytes m.mem (p + BitVec.ofNat 32 (t.header + (t1.header + t1.len)))
                  (t.len - (t1.header + t1.len)))) with
            | .error b => .error b
            | .ok s =>
              if derUsed (derElement 2 (memBytes m.mem (p + BitVec.ofNat 32 (t.header + (t1.header + t1.len)))
                  (t.len - (t1.header + t1.len)))) = t.len - (t1.header + t1.len) then .ok (bs1, s)
              else .error 1 := by
          unfold ecdsaSigOf; rw [hR]; dsimp only; rw [ite_eq_left hfin, hS1]; dsimp only; rw [hE1]; rfl
        have h1o : out ≠ out + BitVec.ofNat 32 1 := fun h => by
          have := congrArg BitVec.toNat h; rw [BitVec.toNat_add, ofNat_tn (by decide)] at this; have := env.how; omega
        cases hS2 : derScalarOf 48 (memBytes m.mem (p + BitVec.ofNat 32 (t.header + (t1.header + t1.len)))
            (t.len - (t1.header + t1.len))) (p + BitVec.ofNat 32 (t.header + (t1.header + t1.len)))
            (derElement 2 (memBytes m.mem (p + BitVec.ofNat 32 (t.header + (t1.header + t1.len)))
              (t.len - (t1.header + t1.len)))) with
        | error b2 =>
          rw [hS2] at h22 hspecA
          obtain ⟨p0, p1, fr22⟩ := h22
          have fr22' : ∀ x, Sep G 0xA0 x 1 → Sep (F + 0x58) 2 x 1 → Sep (F + 0x20) 8 x 1 → m22.mem x = m21.mem x :=
            fun x h1 h2 h3 => by rw [fr22 x h1 h2, derAdvance_outside _ (by rw [e20]; exact h3)]
          have M22O : ∀ x, Sep G 0x170 x 1 → m22.mem x = m.mem x := fun x hx => by
            rw [fr22' x (inG hx) (sFk 0x58 2 (by decide) hx) (sFk 0x20 8 (by decide) hx), M21O x hx]
          have hc22 : CodeIn m22.mem P ecdsaSignature48Code := cIn env.cod sGC M22O
          obtain ⟨m23, d23, u23⟩ := u22.lbu hc22 es_at_a8 (off' := 0xAC) (by decide)
          obtain ⟨m24, d24, u24⟩ := u23.self.lbu hc22 es_at_ac (off' := 0xB0) (by decide)
          have v24a0 : reg m24 a0 = (1 : BitVec 8).zeroExtend 32 := by
            rw [u24.regs, upd_ne' (by decide) u23.self.zero, u23.regs]; simp +decide only [upd_app, ↓reduceIte]
            rw [sp22, ← p0]
          have v24s2 : reg m24 18 = b2.zeroExtend 32 := by
            rw [u24.regs]; simp +decide only [upd_app, ↓reduceIte]
            rw [u23.regs, upd_ne' (by decide) u22.zero, sp22, show F + 0x59 = F + 0x58 + 1 by rw [BitVec.add_assoc]; rfl,
              p1]
          obtain ⟨m25, d25, u25⟩ := u24.self.notTaken hc22 0xB2 es_at_b0 (by decide) (by
            rw [v24a0, u24.self.zero]; decide)
          obtain ⟨m26, d26, u26⟩ := u25.self.aluImm hc22 es_at_b2 (off' := 0xB4) (by decide)
          obtain ⟨m27, d27, u27⟩ := u26.self.alu hc22 es_at_b4 (off' := 0xB6) (by decide)
          obtain ⟨m28, d28, u28⟩ := u27.self.jump hc22 es_at_b6 (off' := 0x6C) (by decide) (by
            rw [u27.self.pc, show P + BitVec.ofNat 32 0xB6 + 0xFFFFFFB6 = P + BitVec.ofNat 32 0x6C by
              rw [BitVec.add_assoc]; rfl]
            exact even_bit0 (even_at P env.hP 0x6C (by decide)))
          obtain ⟨m29, d29, u29⟩ := u28.self.aluImm hc22 es_at_6c (off' := 0x6E) (by decide)
          have k29 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) → reg m29 q = reg m22 q :=
            fun q h0 h1 h9 h18 => by
              rw [u29.regs, upd_ne' h1 u28.self.zero, u28.regs, u27.regs, upd_ne' h9 u26.self.zero, u26.regs,
                upd_ne' h0 u25.self.zero, u25.regs, u24.regs, upd_ne' h18 u23.self.zero, u23.regs, upd_ne' h0 u22.zero]
          obtain ⟨n', S', pc', mem', sp', k'⟩ := tail (k := 1) (tag := 1) (b := b2)
            (S22.trans (.cons d23 (.cons d24 (.cons d25 (.cons d26 (.cons d27 (.cons d28 (.single d29))))))))
            u29.self hc22
            (fun j h1 h2 => by
              rw [fr22' _ (inA j h2) (sepF (c := 0x58) (n := 2) (.inl (by omega)) (by decide) h2)
                (sepF (c := 0x20) (n := 8) (.inl (by omega)) (by decide) h2)]
              exact slot21 j h1 h2)
            (by rw [k29 sp (by decide) (by decide) (by decide) (by decide), sp22])
            (by rw [k29 20 (by decide) (by decide) (by decide) (by decide), s20_22])
            (by rw [u29.regs, upd_ne' (by decide) u28.self.zero, u28.regs, u27.regs, upd_ne' (by decide) u26.self.zero,
                  u26.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u25.self.zero]; rfl)
            (by decide) (by decide)
            (by rw [u29.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u28.self.zero]; rfl)
            (by rw [u29.regs, upd_ne' (by decide) u28.self.zero, u28.regs, u27.regs]
                simp +decide only [upd_app, ↓reduceIte]
                rw [ev_add, show reg m26 x0 = 0 from u26.self.zero, zw, u26.regs, upd_ne' (by decide) u25.self.zero,
                  u25.regs, v24s2, tlv_zext])
            (fun q hq => by
              rw [k29 q (fun e => by subst e; revert hq; decide) (fun e => by subst e; revert hq; decide)
                (fun e => by subst e; revert hq; decide) (fun e => by subst e; revert hq; decide)]
              exact K22 q (by revert hq; revert q; decide))
          refine ⟨n', S', pc', sp', k', fun x hx ho => ?_, ?_⟩
          · rw [mem', memStore8_ne fun e' => ho.point (i := 1) (j := 0) (by decide) (by decide)
                (by rw [add_ofNat_zero]; exact e'.symm),
              memStore8_ne fun e' => ho.point (i := 0) (j := 0) (by decide) (by decide)
                (by rw [add_ofNat_zero, add_ofNat_zero]; exact e'.symm), M22O x hx]
          · rw [hspecA]
            exact ⟨by rw [mem', memStore8_ne h1o, memStore8_same], by rw [mem']; exact memStore8_same _ _ _⟩
        | ok bs2 =>
          rw [hS2] at h22 hspecA
          obtain ⟨p0, pj, fr22⟩ := h22
          cases hE2 : derElement 2 (memBytes m.mem (p + BitVec.ofNat 32 (t.header + (t1.header + t1.len)))
              (t.len - (t1.header + t1.len))) with
          | error e2 =>
            exfalso; rw [hE2] at hS2; unfold derScalarOf at hS2
            split at hS2
            · rename_i h; cases h
            · cases hS2
            · cases hS2
          | ok t2 =>
          have hb2 : t2.header + t2.len ≤ t.len - (t1.header + t1.len) := by
            have := derElement_bound hE2; rwa [memBytes_length] at this
          rw [hE2] at fr22 hspecA
          have fr22' : ∀ x, Sep G 0xA0 x 1 → Sep (F + 0x58) 49 x 1 → Sep (F + 0x20) 8 x 1 → m22.mem x = m21.mem x :=
            fun x h1 h2 h3 => by rw [fr22 x h1 h2, derAdvance_outside _ (by rw [e20]; exact h3)]
          have M22O : ∀ x, Sep G 0x170 x 1 → m22.mem x = m.mem x := fun x hx => by
            rw [fr22' x (inG hx) (sFk 0x58 49 (by decide) hx) (sFk 0x20 8 (by decide) hx), M21O x hx]
          have hc22 : CodeIn m22.mem P ecdsaSignature48Code := cIn env.cod sGC M22O
          obtain ⟨m23, d23, u23⟩ := u22.lbu hc22 es_at_a8 (off' := 0xAC) (by decide)
          obtain ⟨m24, d24, u24⟩ := u23.self.lbu hc22 es_at_ac (off' := 0xB0) (by decide)
          have v24a0 : reg m24 a0 = (0 : BitVec 8).zeroExtend 32 := by
            rw [u24.regs, upd_ne' (by decide) u23.self.zero, u23.regs]; simp +decide only [upd_app, ↓reduceIte]
            rw [sp22, ← p0]
          have v24s2 : reg m24 18 = (m22.mem (F + 0x58 + BitVec.ofNat 32 (1 + 0))).zeroExtend 32 := by
            rw [u24.regs]; simp +decide only [upd_app, ↓reduceIte]
            rw [u23.regs, upd_ne' (by decide) u22.zero, sp22,
              show F + 0x58 + BitVec.ofNat 32 (1 + 0) = F + 0x59 by rw [BitVec.add_assoc]; rfl]
          have k24 : ∀ q, q ≠ a0 → q ≠ (18 : Fin 32) → reg m24 q = reg m22 q := fun q h0 h18 => by
            rw [u24.regs, upd_ne' h18 u23.self.zero, u23.regs, upd_ne' h0 u22.zero]
          obtain ⟨m25, d25, u25⟩ := u24.self.taken hc22 0xB8 es_at_b0 (by decide) (by rw [v24a0, u24.self.zero]; decide)
          obtain ⟨m26, c26, u26⟩ := St.block [.aluImm .add a1 sp 0x5A, .aluImm .add a0 sp 0x89, .aluImm .add a2 x0 0x2F]
            u25.self hc22 (off' := 0xC4) (by decide) (by simp [BlockOk, BInstr.ok])
          simp only [runBlock, BInstr.run] at u26
          have k26 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m26 q = reg m24 q := fun q h0 h1 h2 => by
            rw [u26.regs, updz ((updz (upd_zero _ _ _) (by decide)).trans (upd_zero _ _ _)) h2, updz (upd_zero _ _ _) h0,
              updz u25.self.zero h1, u25.regs]
          have sp26 : reg m26 sp = F := by
            rw [k26 sp (by decide) (by decide) (by decide), k24 sp (by decide) (by decide), sp22]
          obtain ⟨m27, c27, u27, sp27, f27, k27⟩ := mcCall (dst := F + 0x89) (src := F + 0x5A) (N := 47) u26.self hc22
            es_at_c4 es_at_c8 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (cIn env.mcs sGU M22O)
            (cIn env.mcb sGB M22O) sp26
            (by rw [u26.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u25.regs, k24 sp (by decide) (by decide), sp22]; rfl)
            (by rw [u26.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u25.regs, k24 sp (by decide) (by decide), sp22]; rfl)
            (by rw [u26.regs]; simp +decide only [upd_app, ↓reduceIte])
            (sFk 0x89 47 (by decide) sGB)
            (by rw [show F + 0x89 = F + BitVec.ofNat 32 0x89 from rfl, eFk]
                exact sep_offsets G (.inr (by decide)) (by decide) (by decide))
            (by rw [show F + 0x5A = F + BitVec.ofNat 32 0x5A from rfl, eFk]
                exact sep_offsets G (.inr (by decide)) (by decide) (by decide))
            (sep_offsets F (c := 0x89) (n := 47) (d := 0x5A) (k := 47) (.inr (by decide)) (by decide) (by decide))
            (by rw [BitVec.toNat_add, show (0x89 : Word).toNat = 0x89 from rfl]; have := sp0.isLt; omega)
            (by rw [BitVec.toNat_add, show (0x5A : Word).toNat = 0x5A from rfl]; have := sp0.isLt; omega)
          have m27F : ∀ k, k < 0xD0 → m27.mem (F + BitVec.ofNat 32 k) =
              copyBytes m22.mem (F + 0x89) (F + 0x5A) 47 (F + BitVec.ofNat 32 k) := fun k hk =>
            f27 _ (by rw [eFk]; exact sep_offsets G (.inl (by omega)) (by decide) (by omega))
          have M27O : ∀ x, Sep G 0x170 x 1 → m27.mem x = m.mem x := fun x hx => by
            rw [f27 x (hx.sub (c := 0x90) (l := 16) (by decide)),
              copyBytes_sep (dst := F + 0x89) (n := 47) (sFk 0x89 47 (by decide) hx) (Nat.le_refl _), M22O x hx]
          have hc27 : CodeIn m27.mem P ecdsaSignature48Code := cIn env.cod sGC M27O
          obtain ⟨m28, d28, u28⟩ := u27.lw hc27 es_at_cc (off' := 0xCE) (by decide) (by
            rw [sp27]; exact aligned_add hFa (k := 0x24) (by decide))
          obtain ⟨bl8, blC⟩ := derAdvance_ld (M := m21.mem) (d := F + 0x18)
            (rp := p + BitVec.ofNat 32 (t.header + (t1.header + t1.len)))
            (rl := BitVec.ofNat 32 (t.len - (t1.header + t1.len))) t2
          have l24 : memLoad32 m27.mem (F + 0x24) =
              BitVec.ofNat 32 (t.len - (t1.header + t1.len) - (t2.header + t2.len)) := by
            rw [← sub_val hb2 (by omega)]
            show _ = BitVec.ofNat 32 (t.len - (t1.header + t1.len)) - BitVec.ofNat 32 (t2.header + t2.len)
            rw [← blC, e24]
            exact memLoad32_congr fun jj hj => by
              rw [show F + 0x24 + BitVec.ofNat 32 jj = F + BitVec.ofNat 32 (0x24 + jj) by rw [← add_ofNat_assoc]; rfl,
                m27F _ (by omega), copyBytes_sep (dst := F + 0x89) (n := 47)
                  (sepF (c := 0x89) (n := 47) (k := 0x24 + jj) (.inr (by omega)) (by decide) (by omega)) (Nat.le_refl _),
                fr22 _ (inA _ (by omega)) (sepF (c := 0x58) (n := 49) (k := 0x24 + jj) (.inr (by omega)) (by decide)
                  (by omega))]
          have v28 : reg m28 a2 = BitVec.ofNat 32 (t.len - (t1.header + t1.len) - (t2.header + t2.len)) := by
            rw [u28.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp27, l24]
          obtain ⟨m29, c29, u29⟩ := St.block [.aluImm .add a0 x0 1, .aluImm .add (9 : Fin 32) x0 1, .aluImm .add a1 x0 1]
            u28.self hc27 (off' := 0xD4) (by decide) (by simp [BlockOk, BInstr.ok])
          simp only [runBlock, BInstr.run] at u29
          have k29 : ∀ q, q ≠ a0 → q ≠ (9 : Fin 32) → q ≠ a1 → reg m29 q = reg m28 q := fun q h0 h9 h1 => by
            rw [u29.regs, updz ((updz (upd_zero _ _ _) (by decide)).trans (upd_zero _ _ _)) h1, updz (upd_zero _ _ _) h9,
              updz u28.self.zero h0]
          have k28 : ∀ q, q ≠ a2 → reg m28 q = reg m27 q := fun q h => by rw [u28.regs, upd_ne' h u27.zero]
          have v29 : reg m29 a2 = BitVec.ofNat 32 (t.len - (t1.header + t1.len) - (t2.header + t2.len)) := by
            rw [k29 a2 (by decide) (by decide) (by decide), v28]
          have K29 : ∀ q, q.val ∈ [3, 4, 21, 22, 23, 24, 25, 26, 27] → reg m29 q = reg m q := fun q hq => by
            have h : q ≠ a0 ∧ q ≠ (9 : Fin 32) ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ (18 : Fin 32) := by revert hq; revert q; decide
            rw [k29 q h.1 h.2.1 h.2.2.1, k28 q h.2.2.2.1, k27 q (by revert hq; revert q; decide),
              k26 q h.1 h.2.2.1 h.2.2.2.1, k24 q h.1 h.2.2.2.2]
            exact K22 q hq
          have sp29 : reg m29 sp = F := by
            rw [k29 sp (by decide) (by decide) (by decide), k28 sp (by decide), sp27]
          have s20_29 : reg m29 20 = out := by
            rw [k29 20 (by decide) (by decide) (by decide), k28 20 (by decide), k27 20 (by decide),
              k26 20 (by decide) (by decide) (by decide), k24 20 (by decide) (by decide), s20_22]
          have slot27 : ∀ j, 0xB8 ≤ j → j < 0xD0 → m27.mem (F + BitVec.ofNat 32 j) = Msv (F + BitVec.ofNat 32 j) :=
            fun j h1 h2 => by
              rw [m27F j h2, copyBytes_sep (dst := F + 0x89) (n := 47) (sepF (c := 0x89) (n := 47) (.inl (by omega))
                  (by decide) h2) (Nat.le_refl _),
                fr22' _ (inA j h2) (sepF (c := 0x58) (n := 49) (.inl (by omega)) (by decide) h2)
                  (sepF (c := 0x20) (n := 8) (.inl (by omega)) (by decide) h2)]
              exact slot21 j h1 h2
          have S29 : Steps m m29 := S22.trans (.cons d23 (.cons d24 (.cons d25 (c26.trans (c27.trans (.cons d28 c29))))))
          by_cases hfin2 : t2.header + t2.len = t.len - (t1.header + t1.len)
          · obtain ⟨m30, d30, u30⟩ := u29.self.notTaken hc27 0xD6 es_at_d4 (by decide) (by
              rw [v29, u29.self.zero, hfin2, Nat.sub_self]; rfl)
            have outInj : ∀ a b, a < 97 → b < 97 → a ≠ b → out + BitVec.ofNat 32 a ≠ out + BitVec.ofNat 32 b :=
              fun a b ha hb hab h => by
                have := congrArg BitVec.toNat h
                rw [BitVec.toNat_add, BitVec.toNat_add, ofNat_tn (by omega), ofNat_tn (by omega)] at this
                have := env.how; omega
            have scrO : ∀ i, i < 97 → Sep (G + BitVec.ofNat 32 0x90) 16 (out + BitVec.ofNat 32 i) 1 := fun i hi =>
              (sOG.sub (c := i) (l := 1) (by omega)).symm.sub (by decide)
            have scrF : ∀ k, k < 0xD0 → Sep (G + BitVec.ofNat 32 0x90) 16 (F + BitVec.ofNat 32 k) 1 := fun k hk => by
              rw [eFk]; exact sep_offsets G (.inl (by omega)) (by decide) (by omega)
            have cOut : ∀ {b : Word} {l : Nat} {c n : Nat}, c + n ≤ 97 → Sep out 97 b l → Sep (out + BitVec.ofNat 32 c) n b l :=
              fun h hs => hs.sub h
            obtain ⟨m31, c31, u31⟩ := St.block [.aluImm .add a0 (20 : Fin 32) 2, .aluImm .add a1 sp 0x29,
              .aluImm .add a2 x0 0x2F] u30.self hc27 (off' := 0xE2) (by decide) (by simp [BlockOk, BInstr.ok])
            simp only [runBlock, BInstr.run] at u31
            have k31 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m31 q = reg m29 q := fun q h0 h1 h2 => by
              rw [u31.regs, updz ((updz (upd_zero _ _ _) (by decide)).trans (upd_zero _ _ _)) h2, updz (upd_zero _ _ _) h1,
                updz u30.self.zero h0, u30.regs]
            have sp31 : reg m31 sp = F := by rw [k31 sp (by decide) (by decide) (by decide), sp29]
            obtain ⟨m32, c32, u32, sp32, f32, k32⟩ := mcCall (dst := out + 2) (src := F + 0x29) (N := 47) u31.self hc27
              es_at_e2 es_at_e6 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) (cIn env.mcs sGU M27O)
              (cIn env.mcb sGB M27O) sp31
              (by rw [u31.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u30.regs, s20_29]; rfl)
              (by rw [u31.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u30.regs, sp29]; rfl)
              (by rw [u31.regs]; simp +decide only [upd_app, ↓reduceIte])
              (cOut (c := 2) (n := 47) (by decide) env.sOB)
              ((cOut (c := 2) (n := 47) (by decide) sOG).subR (by decide))
              (by rw [show F + 0x29 = F + BitVec.ofNat 32 0x29 from rfl, eFk]
                  exact sep_offsets G (.inr (by decide)) (by decide) (by decide))
              (by rw [show F + 0x29 = F + BitVec.ofNat 32 0x29 from rfl, eFk]
                  exact (cOut (c := 2) (n := 47) (by decide) sOG).subR (by decide))
              (by rw [BitVec.toNat_add, show (2 : Word).toNat = 2 from rfl]; have := env.how; omega)
              (by rw [BitVec.toNat_add, show (0x29 : Word).toNat = 0x29 from rfl]; have := sp0.isLt; omega)
            have back32 : ∀ x, Sep (G + BitVec.ofNat 32 0x90) 16 x 1 → Sep (out + 2) 47 x 1 → m32.mem x = m27.mem x :=
              fun x h1 h2 => by rw [f32 x h1, copyBytes_sep (dst := out + 2) (n := 47) h2 (Nat.le_refl _)]
            have hc32 : CodeIn m32.mem P ecdsaSignature48Code := fun i hi => by
              rw [back32 _ ((sGC.sub (c := 0x90) (l := 16) (by decide)).subR (c := i) (l := 1) (by omega))
                ((cOut (c := 2) (n := 47) (by decide) env.sOC).subR (c := i) (l := 1) (by omega))]
              exact hc27 i hi
            have hcU32 : CodeIn m32.mem (P + 0xC6DA) memcpyStubCode := fun i hi => by
              rw [back32 _ ((sGU.sub (c := 0x90) (l := 16) (by decide)).subR (c := i) (l := 1) (by omega))
                ((cOut (c := 2) (n := 47) (by decide) env.sOU).subR (c := i) (l := 1) (by omega))]
              exact cIn env.mcs sGU M27O i hi
            have hcB32 : CodeIn m32.mem (P + 0xC6E2) memcpyBodyCode := fun i hi => by
              rw [back32 _ ((sGB.sub (c := 0x90) (l := 16) (by decide)).subR (c := i) (l := 1) (by omega))
                ((cOut (c := 2) (n := 47) (by decide) env.sOB).subR (c := i) (l := 1) (by omega))]
              exact cIn env.mcb sGB M27O i hi
            obtain ⟨m33, c33, u33⟩ := St.block [.aluImm .add a0 (20 : Fin 32) 0x32, .aluImm .add a1 sp 0x89,
              .aluImm .add a2 x0 0x2F] u32 hc32 (off' := 0xF6) (by decide) (by simp [BlockOk, BInstr.ok])
            simp only [runBlock, BInstr.run] at u33
            have k33 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m33 q = reg m32 q := fun q h0 h1 h2 => by
              rw [u33.regs, updz ((updz (upd_zero _ _ _) (by decide)).trans (upd_zero _ _ _)) h2, updz (upd_zero _ _ _) h1,
                updz u32.zero h0]
            have K32 : ∀ q, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m32 q = reg m29 q := fun q hq => by
              have h : q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 := by revert hq; revert q; decide
              rw [k32 q (by revert hq; revert q; decide), k31 q h.1 h.2.1 h.2.2]
            have sp33 : reg m33 sp = F := by rw [k33 sp (by decide) (by decide) (by decide), sp32]
            obtain ⟨m34, c34, u34, sp34, f34, k34⟩ := mcCall (dst := out + 0x32) (src := F + 0x89) (N := 47) u33.self hc32
              es_at_f6 es_at_fa (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide) hcU32 hcB32 sp33
              (by rw [u33.regs]; simp +decide only [upd_app, ↓reduceIte]
                  rw [K32 20 (by decide), s20_29]; rfl)
              (by rw [u33.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp32]; rfl)
              (by rw [u33.regs]; simp +decide only [upd_app, ↓reduceIte])
              (cOut (c := 0x32) (n := 47) (by decide) env.sOB)
              ((cOut (c := 0x32) (n := 47) (by decide) sOG).subR (by decide))
              (by rw [show F + 0x89 = F + BitVec.ofNat 32 0x89 from rfl, eFk]
                  exact sep_offsets G (.inr (by decide)) (by decide) (by decide))
              (by rw [show F + 0x89 = F + BitVec.ofNat 32 0x89 from rfl, eFk]
                  exact (cOut (c := 0x32) (n := 47) (by decide) sOG).subR (by decide))
              (by rw [BitVec.toNat_add, show (0x32 : Word).toNat = 0x32 from rfl]; have := env.how; omega)
              (by rw [BitVec.toNat_add, show (0x89 : Word).toNat = 0x89 from rfl]; have := sp0.isLt; omega)
            have back34 : ∀ x, Sep (G + BitVec.ofNat 32 0x90) 16 x 1 → Sep (out + 0x32) 47 x 1 → m34.mem x = m32.mem x :=
              fun x h1 h2 => by rw [f34 x h1, copyBytes_sep (dst := out + 0x32) (n := 47) h2 (Nat.le_refl _)]
            have hc34 : CodeIn m34.mem P ecdsaSignature48Code := fun i hi => by
              rw [back34 _ ((sGC.sub (c := 0x90) (l := 16) (by decide)).subR (c := i) (l := 1) (by omega))
                ((cOut (c := 0x32) (n := 47) (by decide) env.sOC).subR (c := i) (l := 1) (by omega))]
              exact hc32 i hi
            have K34 : ∀ q, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m34 q = reg m29 q := fun q hq => by
              have h : q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 := by revert hq; revert q; decide
              rw [k34 q (by revert hq; revert q; decide), k33 q h.1 h.2.1 h.2.2, K32 q hq]
            have s20_34 : reg m34 20 = out := by rw [K34 20 (by decide), s20_29]
            obtain ⟨m35, d35, u35⟩ := u34.aluImm hc34 es_at_fe (off' := 0x100) (by decide)
            obtain ⟨m36, d36, u36⟩ := u35.self.sb hc34 es_at_100 (off' := 0x104) (by decide)
            have r35 : ∀ q, q ≠ a1 → reg m35 q = reg m34 q := fun q h => by rw [u35.regs, upd_ne' h u34.zero]
            have v19 : reg m34 19 = (m16.mem (F + 0x58 + BitVec.ofNat 32 (1 + 0))).zeroExtend 32 := by
              rw [K34 19 (by decide), k29 19 (by decide) (by decide) (by decide), k28 19 (by decide), k27 19 (by decide),
                k26 19 (by decide) (by decide) (by decide), k24 19 (by decide) (by decide), s19_22]
            rw [r35 20 (by decide), s20_34, r35 19 (by decide), v19, tlv_zext] at u36
            obtain ⟨Mx, hMx⟩ : ∃ M, memStore8 m34.mem (out + 1) (m16.mem (F + 0x58 + BitVec.ofNat 32 (1 + 0))) = M :=
              ⟨_, rfl⟩
            rw [hMx] at u36
            have hcX : CodeIn Mx P ecdsaSignature48Code := by
              rw [← hMx]; exact CodeIn.store8 hc34 (cOut (c := 1) (n := 1) (by decide) env.sOC)
            obtain ⟨m37, d37, u37⟩ := u36.aluImm hcX es_at_104 (off' := 0x108) (by decide)
            obtain ⟨m38, d38, u38⟩ := u37.self.alu hcX es_at_108 (off' := 0x10A) (by decide)
            obtain ⟨m39, d39, u39⟩ := u38.self.jump hcX es_at_10a (off' := 0x6E) (by decide) (by
              rw [u38.self.pc, show P + BitVec.ofNat 32 0x10A + 0xFFFFFF64 = P + BitVec.ofNat 32 0x6E by
                rw [BitVec.add_assoc]; rfl]
              exact even_bit0 (even_at P env.hP 0x6E (by decide)))
            have k39 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ (9 : Fin 32) → reg m39 q = reg m34 q := fun q h0 h1 h9 => by
              rw [u39.regs, u38.regs, upd_ne' h9 u37.self.zero, u37.regs, upd_ne' h0 u36.zero, r35 q h1]
            have v18 : reg m34 18 = (m22.mem (F + 0x58 + BitVec.ofNat 32 (1 + 0))).zeroExtend 32 := by
              rw [K34 18 (by decide), k29 18 (by decide) (by decide) (by decide), k28 18 (by decide), k27 18 (by decide),
                k26 18 (by decide) (by decide) (by decide), v24s2]
            have slotX : ∀ j, 0xB8 ≤ j → j < 0xD0 → Mx (F + BitVec.ofNat 32 j) = Msv (F + BitVec.ofNat 32 j) :=
              fun j h1 h2 => by
                rw [← hMx, memStore8_ne fun e => (outF j h2).point (i := 1) (j := 0) (by decide) (by decide)
                    (by rw [add_ofNat_zero]; exact e.symm),
                  back34 _ (scrF j h2) ((outF j h2).sub (c := 0x32) (l := 47) (by decide)),
                  back32 _ (scrF j h2) ((outF j h2).sub (c := 2) (l := 47) (by decide))]
                exact slot27 j h1 h2
            obtain ⟨n', S', pc', mem', sp', k'⟩ := tail (k := 0x31) (tag := 0)
              (b := m22.mem (F + 0x58 + BitVec.ofNat 32 (1 + 0)))
              (S29.trans (.cons d30 (c31.trans (c32.trans (c33.trans (c34.trans (.cons d35 (.cons d36 (.cons d37
                (.cons d38 (.single d39)))))))))))
              u39.self hcX slotX
              (by rw [k39 sp (by decide) (by decide) (by decide), sp34])
              (by rw [k39 20 (by decide) (by decide) (by decide), s20_34])
              (by rw [u39.regs, u38.regs, upd_ne' (by decide) u37.self.zero, u37.regs]
                  simp +decide only [upd_app, ↓reduceIte]; rw [u36.zero]; rfl)
              (by decide) (by decide)
              (by rw [u39.regs, u38.regs, upd_ne' (by decide) u37.self.zero, u37.regs, upd_ne' (by decide) u36.zero,
                    u35.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u34.zero]; rfl)
              (by rw [u39.regs, u38.regs]; simp +decide only [upd_app, ↓reduceIte]
                  rw [ev_add, show reg m37 x0 = 0 from u37.self.zero, zw, u37.regs, upd_ne' (by decide) u36.zero,
                    r35 18 (by decide), v18, tlv_zext])
              (fun q hq => by
                rw [k39 q (fun e => by subst e; revert hq; decide) (fun e => by subst e; revert hq; decide)
                  (fun e => by subst e; revert hq; decide), K34 q (by revert hq; revert q; decide)]
                exact K29 q hq)
            have hspec : ecdsaSigOf 48 m.mem p n = .ok (bs1, bs2) := by
              rw [hspecA]; exact ite_eq_left (show derUsed (.ok t2) = _ from hfin2)
            have n0_31 : out ≠ out + BitVec.ofNat 32 0x31 := by
              have := outInj 0 0x31 (by decide) (by decide) (by decide); rwa [add_ofNat_zero] at this
            refine ⟨n', S', pc', sp', k', fun x hx ho => ?_, ?_⟩
            · rw [mem', memStore8_ne fun e' => ho.point (i := 0x31) (j := 0) (by decide) (by decide)
                  (by rw [add_ofNat_zero]; exact e'.symm),
                memStore8_ne fun e' => ho.point (i := 0) (j := 0) (by decide) (by decide)
                  (by rw [add_ofNat_zero, add_ofNat_zero]; exact e'.symm),
                ← hMx, memStore8_ne fun e' => ho.point (i := 1) (j := 0) (by decide) (by decide)
                  (by rw [add_ofNat_zero]; exact e'.symm),
                back34 x (hx.sub (c := 0x90) (l := 16) (by decide)) (ho.sub (c := 0x32) (l := 47) (by decide)),
                back32 x (hx.sub (c := 0x90) (l := 16) (by decide)) (ho.sub (c := 2) (l := 47) (by decide)), M27O x hx]
            · rw [hspec]
              refine ⟨by rw [mem', memStore8_ne n0_31, memStore8_same], fun j hj => ?_, fun j hj => ?_⟩
              · rw [mem', memStore8_ne (outInj _ _ (by omega) (by decide) (by omega)),
                  memStore8_ne (by have := outInj (1 + j) 0 (by omega) (by decide) (by omega); rwa [add_ofNat_zero] at this),
                  ← hMx]
                rcases j with _ | j
                · rw [show out + BitVec.ofNat 32 (1 + 0) = out + 1 from rfl, memStore8_same]; exact oj 0 hj
                · rw [memStore8_ne (a := out + 1) (outInj (1 + (j + 1)) 1 (by omega) (by decide) (by omega)),
                    back34 _ (scrO _ (by omega)) (by
                      rw [show (0x32 : Word) = BitVec.ofNat 32 0x32 from rfl]
                      exact sep_offsets out (.inr (by omega)) (by decide) (by omega)),
                    show out + BitVec.ofNat 32 (1 + (j + 1)) = out + 2 + BitVec.ofNat 32 j by
                      rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, add_ofNat_assoc, show 2 + j = 1 + (j + 1) by omega],
                    f32 _ (by
                      rw [show (2 : Word) = BitVec.ofNat 32 2 from rfl, add_ofNat_assoc]; exact scrO _ (by omega)),
                    ds_copy_in (by omega) (by decide),
                    show F + 0x29 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x29 + j) by rw [← add_ofNat_assoc]; rfl,
                    m27F _ (by omega), copyBytes_sep (dst := F + 0x89) (n := 47)
                      (sepF (c := 0x89) (n := 47) (k := 0x29 + j) (.inr (by omega)) (by decide) (by omega)) (Nat.le_refl _),
                    fr22' _ (inA _ (by omega)) (sepF (c := 0x58) (n := 49) (k := 0x29 + j) (.inr (by omega)) (by decide)
                      (by omega)) (sepF (c := 0x20) (n := 8) (k := 0x29 + j) (.inl (by omega)) (by decide) (by omega)),
                    m21F _ (by omega),
                    show F + BitVec.ofNat 32 (0x29 + j) = F + 0x29 + BitVec.ofNat 32 j by rw [← add_ofNat_assoc]; rfl,
                    ds_copy_in (by omega) (by decide),
                    show F + 0x5A + BitVec.ofNat 32 j = F + 0x58 + BitVec.ofNat 32 (1 + (j + 1)) by
                      rw [show (0x5A : Word) = BitVec.ofNat 32 0x5A from rfl, show (0x58 : Word) = BitVec.ofNat 32 0x58 from rfl,
                        add_ofNat_assoc, add_ofNat_assoc, show 0x5A + j = 0x58 + (1 + (j + 1)) by omega]]
                  exact oj (j + 1) hj
              · rcases j with _ | j
                · rw [mem', show out + BitVec.ofNat 32 (49 + 0) = out + BitVec.ofNat 32 0x31 from rfl, memStore8_same]
                  exact pj 0 hj
                · rw [mem', memStore8_ne (outInj _ _ (by omega) (by decide) (by omega)),
                    memStore8_ne (by have := outInj (49 + (j + 1)) 0 (by omega) (by decide) (by omega)
                                     rwa [add_ofNat_zero] at this),
                    ← hMx, memStore8_ne (a := out + 1) (outInj (49 + (j + 1)) 1 (by omega) (by decide) (by omega)),
                    show out + BitVec.ofNat 32 (49 + (j + 1)) = out + 0x32 + BitVec.ofNat 32 j by
                      rw [show (0x32 : Word) = BitVec.ofNat 32 0x32 from rfl, add_ofNat_assoc,
                        show 0x32 + j = 49 + (j + 1) by omega],
                    f34 _ (by
                      rw [show (0x32 : Word) = BitVec.ofNat 32 0x32 from rfl, add_ofNat_assoc]; exact scrO _ (by omega)),
                    ds_copy_in (by omega) (by decide),
                    show F + 0x89 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x89 + j) by rw [← add_ofNat_assoc]; rfl,
                    back32 _ (scrF _ (by omega)) ((outF _ (by omega)).sub (c := 2) (l := 47) (by decide)),
                    m27F _ (by omega),
                    show F + BitVec.ofNat 32 (0x89 + j) = F + 0x89 + BitVec.ofNat 32 j by rw [← add_ofNat_assoc]; rfl,
                    ds_copy_in (by omega) (by decide),
                    show F + 0x5A + BitVec.ofNat 32 j = F + 0x58 + BitVec.ofNat 32 (1 + (j + 1)) by
                      rw [show (0x5A : Word) = BitVec.ofNat 32 0x5A from rfl, show (0x58 : Word) = BitVec.ofNat 32 0x58 from rfl,
                        add_ofNat_assoc, add_ofNat_assoc, show 0x5A + j = 0x58 + (1 + (j + 1)) by omega]]
                  exact pj (j + 1) hj
          · obtain ⟨m30, d30, u30⟩ := u29.self.taken hc27 0x6E es_at_d4 (by decide) (by
              rw [v29, u29.self.zero]; simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
              have := congrArg BitVec.toNat h; rw [ofNat_tn (by omega)] at this
              exact hfin2 (by change _ = 0 at this; omega))
            obtain ⟨n', S', pc', mem', sp', k'⟩ := tail (k := 1) (tag := 1) (b := 1) (S29.trans (.single d30)) u30.self
              hc27 slot27 (by rw [u30.regs, sp29]) (by rw [u30.regs, s20_29])
              (by rw [u30.regs, u29.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u28.self.zero]; rfl)
              (by decide) (by decide)
              (by rw [u30.regs, u29.regs]; simp +decide only [upd_app, ↓reduceIte])
              (by rw [u30.regs, u29.regs]; simp +decide only [upd_app, ↓reduceIte])
              (fun q hq => by rw [u30.regs]; exact K29 q hq)
            have hspec : ecdsaSigOf 48 m.mem p n = .error 1 := by
              rw [hspecA]; exact ite_eq_right hfin2
            refine ⟨n', S', pc', sp', k', fun x hx ho => ?_, ?_⟩
            · rw [mem', memStore8_ne fun e' => ho.point (i := 1) (j := 0) (by decide) (by decide)
                  (by rw [add_ofNat_zero]; exact e'.symm),
                memStore8_ne fun e' => ho.point (i := 0) (j := 0) (by decide) (by decide)
                  (by rw [add_ofNat_zero, add_ofNat_zero]; exact e'.symm), M27O x hx]
            · rw [hspec]
              exact ⟨by rw [mem', memStore8_ne h1o, memStore8_same], by rw [mem']; exact memStore8_same _ _ _⟩
    · obtain ⟨m15, d15, u15⟩ := u14.self.taken hc13 0x6E es_at_4c (by decide) (by
        rw [v14, u14.self.zero]; simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
        have := congrArg BitVec.toNat h; rw [ofNat_tn (by omega)] at this
        exact hfin (by change _ = 0 at this; omega))
      obtain ⟨n', S', pc', mem', sp', k'⟩ := tail (k := 1) (tag := 1) (b := 1) (S14.trans (.single d15)) u15.self
        hc13 slot13 (by rw [u15.regs, sp14]) (by rw [u15.regs, s20_14])
        (by rw [u15.regs, u14.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u13.self.zero]; rfl)
        (by decide) (by decide)
        (by rw [u15.regs, u14.regs]; simp +decide only [upd_app, ↓reduceIte])
        (by rw [u15.regs, u14.regs]; simp +decide only [upd_app, ↓reduceIte])
        (fun q hq => by rw [u15.regs]; exact K14 q (by revert hq; revert q; decide))
      have hspec : ecdsaSigOf 48 m.mem p n = .error 1 := by
        unfold ecdsaSigOf; rw [hR]; exact ite_eq_right hfin
      have h1 : out ≠ out + BitVec.ofNat 32 1 := fun h => by
        have := congrArg BitVec.toNat h; rw [BitVec.toNat_add, ofNat_tn (by decide)] at this; have := env.how; omega
      refine ⟨n', S', pc', sp', k', fun x hx ho => ?_, ?_⟩
      · rw [mem', memStore8_ne fun e' => ho.point (i := 1) (j := 0) (by decide) (by decide)
            (by rw [add_ofNat_zero]; exact e'.symm),
          memStore8_ne fun e' => ho.point (i := 0) (j := 0) (by decide) (by decide)
            (by rw [add_ofNat_zero, add_ofNat_zero]; exact e'.symm), M13O x hx]
      · rw [hspec]
        exact ⟨by rw [mem', memStore8_ne h1, memStore8_same], by rw [mem']; exact memStore8_same _ _ _⟩

end C3.RV32
