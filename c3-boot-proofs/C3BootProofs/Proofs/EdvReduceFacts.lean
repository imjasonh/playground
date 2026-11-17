import C3BootProofs.Proofs.EdVerifyDecode
import C3BootProofs.Proofs.ScalarMontFacts

/-!
# Facts for the generated proof of `ed25519_verify`'s inlined `Scalar::reduce`

The step lemma for an `addi` whose result the stepper names itself, the
separation of the frame's first 0x128 bytes from the input words above them,
and the eight input words as the generated definitions read them.
-/

namespace C3.RV32

section Step
variable {M : Word → BitVec 8} {base : Word} {m : Machine} {off : Nat} {f : Fin 32 → Word} {code : List Nat}

theorem St.aluImmE (s : St M base m off f) (hc : CodeIn M base code) {op : AluOp} {rd rs1 : Fin 32}
    {imm len : Word} {off' : Nat} (hf : fetchRel code off = some (.aluImm op rd rs1 imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') {v : Word} (hv : aluEval op (f rs1) imm = v) :
    ∃ m1, step m = some m1 ∧ St M base m1 off' (upd f rd v) := by
  subst hv; exact s.aluImm hc hf hn

end Step

theorem ev_sepIn (F : Word) (d : Nat) (h : 0x128 ≤ d) (h2 : d + 4 ≤ 2 ^ 32) :
    Sep F 0x128 (F + BitVec.ofNat 32 d) 4 := by
  have := sep_offsets F (c := 0) (n := 0x128) (d := d) (k := 4) (Or.inl (by omega)) (by decide) h2
  rwa [add_ofNat_zero] at this

/-- Word `i` of the eight at `F + 0x9F0`, and zero past them. -/
def evIn (M : Word → BitVec 8) (F : Word) (i : Nat) : Nat :=
  if i < 8 then (memLoad32 M (F + BitVec.ofNat 32 (0x9F0 + 4 * i))).toNat else 0

end C3.RV32
