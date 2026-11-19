import C3BootProofs.Proofs.SvData

/-!
# `sigstore::verify`: `KeyUsage`

What the extensions loop needs for a `KeyUsage` value: a signed byte load,
the count of trailing zero bits that the compiled code computes with a
population count, and branches on a byte's sign.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

theorem St.lb {M : Word → BitVec 8} {base : Word} {m : Machine} {off : Nat} {f : Fin 32 → Word} {code : List Nat}
    (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {rd rs1 : Fin 32} {o len : Word} {off' : Nat}
    (hf : fetchRel code off = some (.load .lb rd rs1 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') :
    ∃ m1, step m = some m1 ∧
      St M base m1 off' (upd f rd ((M (f rs1 + o)).signExtend 32)) := by
  refine ⟨_, ?_, s.write (v := (M (f rs1 + o)).signExtend 32) (rd := rd) hn⟩
  have ha : aligned (loadSize .lb) (reg m rs1 + o) = true := by
    unfold aligned loadSize; rw [Nat.mod_one]; rfl
  rw [step_code (s.codeAt hc) s.pc hf, ← s.regs rs1, ← s.mem]
  unfold exec
  simp only [ha, Bool.not_true]
  rfl

/-- What the code from 0x690 to 0x6BA leaves in `a4` for `x` in `a4`: the
number of ones in `!x & (x - 1)`, eight bits at a time. -/
def kuCtz (x : Word) : Word :=
  let a5 := x + 0xFFFFFFFF
  let a4 := (x ^^^ 0xFFFFFFFF) &&& a5
  let a5 := (a4 >>> 1) &&& 0x55
  let a4 := a4 - a5
  let a5 := a4 >>> 2
  let a4 := (a4 &&& 0x33) + (a5 &&& 0x33)
  let a5 := a4 >>> 4
  (a4 + a5) &&& 0xF

/-- The number of trailing zero bits of a nonzero byte. -/
def ctz8 (b : Nat) : Nat :=
  if b % 2 = 1 then 0 else if b % 4 = 2 then 1 else if b % 8 = 4 then 2 else if b % 16 = 8 then 3
  else if b % 32 = 16 then 4 else if b % 64 = 32 then 5 else if b % 128 = 64 then 6 else 7

set_option maxRecDepth 100000 in
theorem kuCtz_byte_n : ∀ n, n < 256 → n ≠ 0 →
    kuCtz ((BitVec.ofNat 8 n).zeroExtend 32) = BitVec.ofNat 32 (ctz8 n) := by decide

theorem kuCtz_byte {b : BitVec 8} (h : b ≠ 0) : kuCtz (b.zeroExtend 32) = BitVec.ofNat 32 (ctz8 b.toNat) := by
  have := kuCtz_byte_n b.toNat b.isLt (fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl)))
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

set_option maxRecDepth 100000 in
theorem bge_sext_n : ∀ n, n < 256 →
    branchTaken .bge ((BitVec.ofNat 8 n).signExtend 32) 0 = decide (n < 0x80) := by decide

/-- `bge x, zero` on a sign-extended byte: taken when its top bit is clear. -/
theorem br_bge_sext {b : BitVec 8} : branchTaken .bge (b.signExtend 32) 0 = decide (b.toNat < 0x80) := by
  have := bge_sext_n b.toNat b.isLt
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

theorem br_bge_sext_t {b : BitVec 8} (h : b.toNat < 0x80) : branchTaken .bge (b.signExtend 32) 0 = true := by
  rw [br_bge_sext]; exact decide_eq_true h

theorem br_bge_sext_f {b : BitVec 8} (h : ¬ b.toNat < 0x80) : branchTaken .bge (b.signExtend 32) 0 = false := by
  rw [br_bge_sext]; exact decide_eq_false h

/-- The unused bits a `KeyUsage` value's last byte allows: eight for a zero
byte, otherwise its trailing zero bits. -/
def kuUnused (b : BitVec 8) : Nat := if b = 0 then 8 else ctz8 b.toNat

theorem kuUnused_zero {b : BitVec 8} (h : b = 0) : BitVec.ofNat 32 0x8 = BitVec.ofNat 32 (kuUnused b) := by
  rw [kuUnused, ite_eq_left h]

theorem kuUnused_ne {b : BitVec 8} (h : ¬ b = 0) :
    kuCtz (b.zeroExtend 32) = BitVec.ofNat 32 (kuUnused b) := by
  rw [kuUnused, ite_eq_right h, kuCtz_byte h]

/-- A value's last byte, outside the stack. -/
theorem SvIn.lastIn {B p n : Word} (h : SvIn B p n.toNat) (h2 : 2 ≤ n.toNat) :
    SvIn B ((p + n) + BitVec.ofNat 32 0xFFFFFFFF) 1 := by
  have e : (p + n) + BitVec.ofNat 32 0xFFFFFFFF = p + BitVec.ofNat 32 (n.toNat - 1) := by
    rw [show BitVec.ofNat 32 0xFFFFFFFF = -1 from rfl, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      sub_ofNat_toNat (show (1 : Word).toNat ≤ n.toNat by rw [show (1 : Word).toNat = 1 from rfl]; omega),
      show (1 : Word).toNat = 1 from rfl]
  rw [e]; exact (h.drop (k := n.toNat - 1) (by omega)).shrink (by omega)

/-- A value's second byte, outside the stack. -/
theorem SvIn.secondIn {B p n : Word} (h : SvIn B p n.toNat) (h2 : 2 ≤ n.toNat) : SvIn B (p + 0x1) 1 :=
  (h.drop (k := 1) (by omega)).shrink (by omega)

theorem ne_one_of {n : Word} (h : 2 ≤ n.toNat) : n ≠ BitVec.ofNat 32 0x1 := fun e => by
  rw [e] at h; exact absurd h (by decide)

theorem ne_zero_of {n : Word} (h : 2 ≤ n.toNat) : n ≠ 0 := fun e => by
  rw [e] at h; exact absurd h (by decide)

theorem zext_ne_zero {b : BitVec 8} (h : ¬ b = 0) : b.zeroExtend 32 ≠ 0 := fun e => h (by
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_setWidth] at this
  rw [Nat.mod_eq_of_lt (by have := b.isLt; omega)] at this
  exact this)

end C3.RV32.Sv
