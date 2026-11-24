import C3BootProofs.Proofs.Ed25519VerifyCall
import C3BootProofs.Proofs.Arr32Eq
import C3BootProofs.Proofs.SmallFns
import C3BootProofs.Image.BootloaderData5
import C3BootProofs.Image.BootloaderData7

/-!
# `c3_verify::keys::KeySet::new`

`KeySet::new(keys)` takes one to four 32-byte Ed25519 public keys and checks
each, in order: `ed25519_public_key_ok` must accept it (else error 0xE), and
no later key may equal it (else 0xD). The length must be a multiple of 32
from 32 to 128 (else `OutOfRange`, 5). It returns `Result<KeySet, Error>`:
the keys' pointer and length, or a null pointer and the error byte.
-/

namespace C3.RV32

open C3.Image

abbrev KSN : Word := BitVec.ofNat 32 keySetNewAddress

/-- Whether `ed25519_public_key_ok` accepts the key at `p`. -/
def pkOkAt (M : Word → BitVec 8) (p : Word) : Bool :=
  pkOkSpec (memBytes M (BitVec.ofNat 32 (img% edPrimeAddress)) 32) (memBytes M (BitVec.ofNat 32 (img% p256OneAddress)) 32)
    (memBytes M (BitVec.ofNat 32 (img% edPm1Address)) 32) (feW M (BitVec.ofNat 32 edOneAddress))
    (feW M (BitVec.ofNat 32 edDAddress)) (feW M (BitVec.ofNat 32 edSqrtM1Address)) (memBytes M p 32)

/-- Whether the key at `a` equals one of the `k` keys after `p`. -/
def ksDup (M : Word → BitVec 8) (a : Word) : Word → Nat → Bool
  | _, 0 => false
  | p, k + 1 => decide (memBytes M a 32 = memBytes M (p + 0x20) 32) || ksDup M a (p + 0x20) k

/-- The error, if any, from checking `k` keys from `q`, with `r` keys after `q`. -/
def ksOuter (M : Word → BitVec 8) : Word → Nat → Nat → Option (BitVec 8)
  | _, _, 0 => none
  | q, r, k + 1 =>
    if pkOkAt M q then (if ksDup M q q r then some 0xD else ksOuter M (q + 0x20) (r - 1) k) else some 0xE

/-- Memory after `KeySet::new` returns, outside the stack it uses. -/
def keySetMem (M : Word → BitVec 8) (out keys len : Word) : Word → BitVec 8 :=
  if len.toNat % 32 = 0 ∧ len.toNat ≤ 0x9F ∧ 32 ≤ len.toNat then
    match ksOuter M keys (len.toNat / 32 - 1) (len.toNat / 32) with
    | none => memStore32 (memStore32 M out keys) (out + 4) len
    | some c => memStore8 (memStore32 M out 0) (out + 4) c
  else memStore8 (memStore32 M out 0) (out + 4) 5

set_option maxRecDepth 10000

theorem ksn_at_0 : fetchRel keySetNewCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem ksn_at_2 : fetchRel keySetNewCode 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem ksn_at_4 : fetchRel keySetNewCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x28, 2) := by decide
theorem ksn_at_6 : fetchRel keySetNewCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x24, 2) := by decide
theorem ksn_at_8 : fetchRel keySetNewCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x20, 2) := by decide
theorem ksn_at_a : fetchRel keySetNewCode 0xA = some (.store .sw sp (19 : Fin 32) 0x1C, 2) := by decide
theorem ksn_at_c : fetchRel keySetNewCode 0xC = some (.store .sw sp (20 : Fin 32) 0x18, 2) := by decide
theorem ksn_at_e : fetchRel keySetNewCode 0xE = some (.store .sw sp (21 : Fin 32) 0x14, 2) := by decide
theorem ksn_at_10 : fetchRel keySetNewCode 0x10 = some (.store .sw sp (22 : Fin 32) 0x10, 2) := by decide
theorem ksn_at_12 : fetchRel keySetNewCode 0x12 = some (.store .sw sp (23 : Fin 32) 0xC, 2) := by decide
theorem ksn_at_14 : fetchRel keySetNewCode 0x14 = some (.store .sw sp (24 : Fin 32) 0x8, 2) := by decide
theorem ksn_at_16 : fetchRel keySetNewCode 0x16 = some (.store .sw sp (25 : Fin 32) 0x4, 2) := by decide
theorem ksn_at_18 : fetchRel keySetNewCode 0x18 = some (.alu .add (18 : Fin 32) x0 a1, 2) := by decide
theorem ksn_at_1a : fetchRel keySetNewCode 0x1A = some (.aluImm .and a1 a2 0x1F, 4) := by decide
theorem ksn_at_1e : fetchRel keySetNewCode 0x1E = some (.alu .add (19 : Fin 32) x0 a0, 2) := by decide
theorem ksn_at_20 : fetchRel keySetNewCode 0x20 = some (.branch .beq a1 x0 0x26, 2) := by decide
theorem ksn_at_22 : fetchRel keySetNewCode 0x22 = some (.aluImm .add a0 x0 0x5, 2) := by decide
theorem ksn_at_24 : fetchRel keySetNewCode 0x24 = some (.store .sw (19 : Fin 32) x0 0x0, 4) := by decide
theorem ksn_at_28 : fetchRel keySetNewCode 0x28 = some (.store .sb (19 : Fin 32) a0 0x4, 4) := by decide
theorem ksn_at_2c : fetchRel keySetNewCode 0x2C = some (.load .lw ra sp 0x2C, 2) := by decide
theorem ksn_at_2e : fetchRel keySetNewCode 0x2E = some (.load .lw (8 : Fin 32) sp 0x28, 2) := by decide
theorem ksn_at_30 : fetchRel keySetNewCode 0x30 = some (.load .lw (9 : Fin 32) sp 0x24, 2) := by decide
theorem ksn_at_32 : fetchRel keySetNewCode 0x32 = some (.load .lw (18 : Fin 32) sp 0x20, 2) := by decide
theorem ksn_at_34 : fetchRel keySetNewCode 0x34 = some (.load .lw (19 : Fin 32) sp 0x1C, 2) := by decide
theorem ksn_at_36 : fetchRel keySetNewCode 0x36 = some (.load .lw (20 : Fin 32) sp 0x18, 2) := by decide
theorem ksn_at_38 : fetchRel keySetNewCode 0x38 = some (.load .lw (21 : Fin 32) sp 0x14, 2) := by decide
theorem ksn_at_3a : fetchRel keySetNewCode 0x3A = some (.load .lw (22 : Fin 32) sp 0x10, 2) := by decide
theorem ksn_at_3c : fetchRel keySetNewCode 0x3C = some (.load .lw (23 : Fin 32) sp 0xC, 2) := by decide
theorem ksn_at_3e : fetchRel keySetNewCode 0x3E = some (.load .lw (24 : Fin 32) sp 0x8, 2) := by decide
theorem ksn_at_40 : fetchRel keySetNewCode 0x40 = some (.load .lw (25 : Fin 32) sp 0x4, 2) := by decide
theorem ksn_at_42 : fetchRel keySetNewCode 0x42 = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem ksn_at_44 : fetchRel keySetNewCode 0x44 = some (.jalr x0 ra 0x0, 2) := by decide
theorem ksn_at_46 : fetchRel keySetNewCode 0x46 = some (.alu .add (20 : Fin 32) x0 a2, 2) := by decide
theorem ksn_at_48 : fetchRel keySetNewCode 0x48 = some (.aluImm .add a0 x0 0x9F, 4) := by decide
theorem ksn_at_4c : fetchRel keySetNewCode 0x4C = some (.branch .bltu a0 a2 0xFFFFFFD6, 4) := by decide
theorem ksn_at_50 : fetchRel keySetNewCode 0x50 = some (.aluImm .srl (21 : Fin 32) (20 : Fin 32) 0x5, 4) := by decide
theorem ksn_at_54 : fetchRel keySetNewCode 0x54 = some (.branch .beq (21 : Fin 32) x0 0xFFFFFFCE, 4) := by decide
theorem ksn_at_58 : fetchRel keySetNewCode 0x58 = some (.aluImm .add (22 : Fin 32) x0 0x0, 2) := by decide
theorem ksn_at_5a : fetchRel keySetNewCode 0x5A = some (.aluImm .sll (24 : Fin 32) (21 : Fin 32) 0x5, 4) := by decide
theorem ksn_at_5e : fetchRel keySetNewCode 0x5E = some (.alu .add (23 : Fin 32) (18 : Fin 32) (24 : Fin 32), 4) := by decide
theorem ksn_at_62 : fetchRel keySetNewCode 0x62 = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0xFFFFFFE0, 2) := by decide
theorem ksn_at_64 : fetchRel keySetNewCode 0x64 = some (.alu .add (25 : Fin 32) x0 (18 : Fin 32), 2) := by decide
theorem ksn_at_66 : fetchRel keySetNewCode 0x66 = some (.branch .beq (18 : Fin 32) (23 : Fin 32) 0x40, 4) := by decide
theorem ksn_at_6a : fetchRel keySetNewCode 0x6A = some (.alu .add a0 x0 (25 : Fin 32), 2) := by decide
theorem ksn_at_6c : fetchRel keySetNewCode 0x6C = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem ksn_at_70 : fetchRel keySetNewCode 0x70 = some (.jalr ra ra 0x5A6, 4) := by decide
theorem ksn_at_74 : fetchRel keySetNewCode 0x74 = some (.branch .beq a0 x0 0x40, 2) := by decide
theorem ksn_at_76 : fetchRel keySetNewCode 0x76 = some (.branch .bgeu (22 : Fin 32) (21 : Fin 32) 0x24, 4) := by decide
theorem ksn_at_7a : fetchRel keySetNewCode 0x7A = some (.aluImm .sll (9 : Fin 32) (22 : Fin 32) 0x5, 4) := by decide
theorem ksn_at_7e : fetchRel keySetNewCode 0x7E = some (.alu .add (9 : Fin 32) (9 : Fin 32) (18 : Fin 32), 2) := by decide
theorem ksn_at_80 : fetchRel keySetNewCode 0x80 = some (.alu .add (8 : Fin 32) x0 (24 : Fin 32), 2) := by decide
theorem ksn_at_82 : fetchRel keySetNewCode 0x82 = some (.branch .beq (8 : Fin 32) x0 0x18, 2) := by decide
theorem ksn_at_84 : fetchRel keySetNewCode 0x84 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x20, 4) := by decide
theorem ksn_at_88 : fetchRel keySetNewCode 0x88 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFE0, 2) := by decide
theorem ksn_at_8a : fetchRel keySetNewCode 0x8A = some (.alu .add a0 x0 (25 : Fin 32), 2) := by decide
theorem ksn_at_8c : fetchRel keySetNewCode 0x8C = some (.alu .add a1 x0 (9 : Fin 32), 2) := by decide
theorem ksn_at_8e : fetchRel keySetNewCode 0x8E = some (.auipc ra 0x0, 4) := by decide
theorem ksn_at_92 : fetchRel keySetNewCode 0x92 = some (.jalr ra ra 0x2A, 4) := by decide
theorem ksn_at_96 : fetchRel keySetNewCode 0x96 = some (.branch .beq a0 x0 0xFFFFFFEC, 2) := by decide
theorem ksn_at_98 : fetchRel keySetNewCode 0x98 = some (.jal x0 0x18, 2) := by decide
theorem ksn_at_9a : fetchRel keySetNewCode 0x9A = some (.aluImm .add (25 : Fin 32) (25 : Fin 32) 0x20, 4) := by decide
theorem ksn_at_9e : fetchRel keySetNewCode 0x9E = some (.aluImm .add (22 : Fin 32) (22 : Fin 32) 0x1, 2) := by decide
theorem ksn_at_a0 : fetchRel keySetNewCode 0xA0 = some (.aluImm .add (24 : Fin 32) (24 : Fin 32) 0xFFFFFFE0, 2) := by decide
theorem ksn_at_a2 : fetchRel keySetNewCode 0xA2 = some (.branch .bne (25 : Fin 32) (23 : Fin 32) 0xFFFFFFC8, 4) := by decide
theorem ksn_at_a6 : fetchRel keySetNewCode 0xA6 = some (.store .sw (19 : Fin 32) (18 : Fin 32) 0x0, 4) := by decide
theorem ksn_at_aa : fetchRel keySetNewCode 0xAA = some (.store .sw (19 : Fin 32) (20 : Fin 32) 0x4, 4) := by decide
theorem ksn_at_ae : fetchRel keySetNewCode 0xAE = some (.jal x0 0xFFFFFF7E, 2) := by decide
theorem ksn_at_b0 : fetchRel keySetNewCode 0xB0 = some (.aluImm .add a0 x0 0xD, 2) := by decide
theorem ksn_at_b2 : fetchRel keySetNewCode 0xB2 = some (.jal x0 0xFFFFFF72, 2) := by decide
theorem ksn_at_b4 : fetchRel keySetNewCode 0xB4 = some (.aluImm .add a0 x0 0xE, 2) := by decide
theorem ksn_at_b6 : fetchRel keySetNewCode 0xB6 = some (.jal x0 0xFFFFFF6E, 2) := by decide

theorem memBytes_eq_of {M M' : Word → BitVec 8} {p : Word} {n : Nat}
    (h : ∀ i, i < n → M (p + BitVec.ofNat 32 i) = M' (p + BitVec.ofNat 32 i)) : memBytes M p n = memBytes M' p n := by
  unfold memBytes; apply List.map_congr_left; intro i hi; rw [h i (List.mem_range.mp hi)]

theorem lowSep {a b : Word} {n k : Nat} (ha : a.toNat + n ≤ 0x40000000) (hb : 0x40000000 ≤ b.toNat)
    (hbk : b.toNat + k ≤ 2 ^ 32) : Sep a n b k := sep_of_le (by omega) hbk

theorem and31_mod (x : Nat) : x &&& 31 = x % 32 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, show (32 : Nat) = 2 ^ 5 from rfl, Nat.testBit_mod_two_pow]
  by_cases h : i < 5
  · have h31 : ∀ j, j < 5 → Nat.testBit 31 j = true := by decide
    rw [h31 i h, Bool.and_true, decide_eq_true h, Bool.true_and]
  · have h31 : Nat.testBit 31 i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 31 < 2 ^ 5) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [h31, Bool.and_false, decide_eq_false h, Bool.false_and]

theorem and1f_toNat (x : Word) : (aluEval .and x 0x1F).toNat = x.toNat % 32 := by
  show (x &&& 0x1F).toNat = _
  rw [BitVec.toNat_and, show (0x1F : Word).toNat = 31 from rfl, and31_mod]

theorem srl5_toNat (x : Word) : (aluEval .srl x 5).toNat = x.toNat / 32 := by
  show (x >>> ((5 : Word).toNat % 32)).toNat = _
  rw [show ((5 : Word).toNat % 32) = 5 from rfl, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem sll5_toNat (x : Word) : (aluEval .sll x 5).toNat = x.toNat * 32 % 2 ^ 32 := by
  show (x <<< ((5 : Word).toNat % 32)).toNat = _
  rw [show ((5 : Word).toNat % 32) = 5 from rfl, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem ksDup_congr {M M' : Word → BitVec 8} {a : Word} (ha : memBytes M a 32 = memBytes M' a 32) :
    ∀ (k : Nat) (p : Word), (∀ j, j < k → memBytes M (p + BitVec.ofNat 32 (32 * (j + 1))) 32 =
      memBytes M' (p + BitVec.ofNat 32 (32 * (j + 1))) 32) → ksDup M a p k = ksDup M' a p k
  | 0, _, _ => rfl
  | k + 1, p, h => by
    show (decide (memBytes M a 32 = memBytes M (p + 0x20) 32) || ksDup M a (p + 0x20) k) =
      (decide (memBytes M' a 32 = memBytes M' (p + 0x20) 32) || ksDup M' a (p + 0x20) k)
    have h0 : memBytes M (p + 0x20) 32 = memBytes M' (p + 0x20) 32 := h 0 (by omega)
    rw [ha, h0, ksDup_congr ha k (p + 0x20) fun j hj => by
      have := h (j + 1) (by omega)
      rwa [show p + BitVec.ofNat 32 (32 * (j + 1 + 1)) = p + 0x20 + BitVec.ofNat 32 (32 * (j + 1)) by
        rw [show (p + 0x20 : Word) = p + BitVec.ofNat 32 32 from rfl, add_ofNat_assoc]; congr 2; omega] at this]

set_option maxHeartbeats 16000000 in
/-- The loop that compares the key at `q` with the `k` keys after `p`. -/
theorem ksn_inner {G q : Word} {Mr : Word → BitVec 8}
    (hcK : CodeIn Mr KSN keySetNewCode) (hcA : CodeIn Mr (KSN + 0xB8) arr32EqCode)
    (hcM : CodeIn Mr (KSN + 0xB8 + 0xC0F0) memcmpCode)
    (hG : G.toNat % 4 = 0) (hGw : G.toNat ≤ 0x40000000) (hG4 : 4 ≤ G.toNat)
    (hq : Sep (G + 0xFFFFFFFC) 4 q 32) :
    ∀ (k : Nat) (mx : Machine) (p : Word), 32 * k < 2 ^ 32 → St mx.mem KSN mx 0x82 (reg mx) →
      (∀ x, Sep (G + 0xFFFFFFFC) 4 x 1 → mx.mem x = Mr x) → reg mx sp = G → reg mx 8 = BitVec.ofNat 32 (32 * k) →
      reg mx 9 = p → reg mx 25 = q → (∀ j, j < k → Sep (G + 0xFFFFFFFC) 4 (p + BitVec.ofNat 32 (32 * (j + 1))) 32) →
      ∃ mx', Steps mx mx' ∧ (∀ x, Sep (G + 0xFFFFFFFC) 4 x 1 → mx'.mem x = Mr x) ∧
        (∀ r, r ≠ ra → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ 8 → r ≠ 9 → reg mx' r = reg mx r) ∧
        (ksDup Mr q p k = true → St mx'.mem KSN mx' 0xB0 (reg mx')) ∧
        (ksDup Mr q p k = false → St mx'.mem KSN mx' 0x9A (reg mx')) := by
  have hGl : (G + 0xFFFFFFFC).toNat + 4 ≤ 0x40000000 := by
    rw [BitVec.toNat_add, show (0xFFFFFFFC : Word).toNat = 2 ^ 32 - 4 from rfl]; omega
  have codeT : ∀ {M : Word → BitVec 8} {b : Word} {code : List Nat}, 0x40000000 ≤ b.toNat → b.toNat + code.length ≤ 2 ^ 32 →
      (∀ x, Sep (G + 0xFFFFFFFC) 4 x 1 → M x = Mr x) → CodeIn Mr b code → CodeIn M b code := fun hb hbl hM hc i hi => by
    rw [hM _ ((lowSep hGl hb hbl).subR (c := i) (l := 1) (by omega))]; exact hc i hi
  intro k
  induction k with
  | zero =>
    intro mx p _ s hM hsp h8 _ _ _
    obtain ⟨m1, e1, t1⟩ := s.taken (codeT (by decide) (by decide) hM hcK) 0x9A ksn_at_82 (by decide)
      (by rw [h8, show reg mx x0 = 0 from s.zero]; decide)
    refine ⟨m1, .single e1, fun x hx => by rw [t1.mem]; exact hM x hx, fun r _ _ _ _ _ _ _ _ => t1.regs r,
      fun h => absurd h (by simp [ksDup]), fun _ => by rw [t1.mem]; exact t1.self⟩
  | succ k ih =>
    intro mx p hk s hM hsp h8 h9 h25 hpS
    have hz := s.zero
    have hcx := codeT (by decide) (by decide) hM hcK
    obtain ⟨m1, e1, t1⟩ := s.notTaken hcx 0x84 ksn_at_82 (by decide)
      (by
        rw [h8, show reg mx x0 = 0 from hz]
        refine beq_eq_false_iff_ne.mpr fun h => ?_
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
        exact absurd this (by show 32 * (k + 1) ≠ 0; omega))
    obtain ⟨m2, e2, t2⟩ := t1.aluImm hcx ksn_at_84 (off' := 0x88) (by decide)
    obtain ⟨m3, e3, t3⟩ := t2.aluImm hcx ksn_at_88 (off' := 0x8A) (by decide)
    obtain ⟨m4, e4, t4⟩ := t3.alu hcx ksn_at_8a (off' := 0x8C) (by decide)
    obtain ⟨m5, e5, t5⟩ := t4.alu hcx ksn_at_8c (off' := 0x8E) (by decide)
    obtain ⟨m6, c6, pc6, mem6, regs6⟩ := t5.callRa (cb := KSN + 0xB8) hcx ksn_at_8e ksn_at_92
      (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    have sp6 : reg m6 sp = G := by rw [regs6]; simp +decide only [upd, ite_true, ite_false]; exact hsp
    have a06 : reg m6 a0 = q := by
      rw [regs6]; simp +decide only [upd, ite_true, ite_false]; rw [h25]; exact BitVec.zero_add q
    have a16 : reg m6 a1 = p + 0x20 := by
      rw [regs6]; simp +decide only [upd, ite_true, ite_false]; rw [h9]; exact BitVec.zero_add _
    have s06 : reg m6 8 = BitVec.ofNat 32 (32 * k) := by
      rw [regs6]; simp +decide only [upd, ite_true, ite_false]; rw [h8]
      apply BitVec.eq_of_toNat_eq
      show (BitVec.ofNat 32 (32 * (k + 1)) + 0xFFFFFFE0).toNat = (BitVec.ofNat 32 (32 * k)).toNat
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFE0 : Word).toNat = 4294967264 from rfl]
      omega
    have s16 : reg m6 9 = p + 0x20 := by rw [regs6]; simp +decide only [upd, ite_true, ite_false]; rw [h9]; rfl
    have s96 : reg m6 25 = q := by rw [regs6]; simp +decide only [upd, ite_true, ite_false]; exact h25
    have ra6 : reg m6 ra = KSN + BitVec.ofNat 32 (0x8E + 8) := by rw [regs6]; simp +decide only [upd, ite_true, ite_false]
    have k6 : ∀ r, r ≠ ra → r ≠ a0 → r ≠ a1 → r ≠ 8 → r ≠ 9 → reg m6 r = reg mx r := fun r h1 h2 h3 h4 h5 => by
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; rw [regs6]; simp [upd, hz]
      rw [regs6]; simp only [upd, hr, h1, h2, h3, h4, h5, ↓reduceIte]
    have mem6' : m6.mem = mx.mem := mem6
    have hM6 : ∀ x, Sep (G + 0xFFFFFFFC) 4 x 1 → m6.mem x = Mr x := fun x hx => by rw [mem6']; exact hM x hx
    have hpS0 : Sep (G + 0xFFFFFFFC) 4 (p + 0x20) 32 := hpS 0 (by omega)
    obtain ⟨m7, c7, pc7, a07, k7, mem7⟩ := arr32Eq_correct m6 (base := KSN + 0xB8) (by decide)
      (codeT (by decide) (by decide) hM6 hcA) (codeT (by decide) (by decide) hM6 hcM) pc6 a06 a16 ra6
      (even_clear _ (by decide)) (by rw [sp6]; exact hG) (by rw [sp6]; exact lowSep hGl (by decide) (by decide))
      (by rw [sp6]; exact lowSep hGl (by decide) (by decide)) (by rw [sp6]; exact hq) (by rw [sp6]; exact hpS0)
    rw [sp6] at mem7
    have hM7 : ∀ x, Sep (G + 0xFFFFFFFC) 4 x 1 → m7.mem x = Mr x := fun x hx => by rw [mem7 x hx]; exact hM6 x hx
    have mbq : memBytes m6.mem q 32 = memBytes Mr q 32 :=
      memBytes_eq_of fun i hi => hM6 _ ((hq.symm.sub (c := i) (l := 1) hi).symm)
    have mbp : memBytes m6.mem (p + 0x20) 32 = memBytes Mr (p + 0x20) 32 :=
      memBytes_eq_of fun i hi => hM6 _ ((hpS0.symm.sub (c := i) (l := 1) hi).symm)
    rw [mbq, mbp] at a07
    have t7 : St m7.mem KSN m7 0x96 (reg m7) := ⟨by rw [pc7], rfl, fun _ => rfl⟩
    have hc7 := codeT (by decide) (by decide) hM7 hcK
    have k7' : ∀ r, r ≠ ra → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ 8 → r ≠ 9 → reg m7 r = reg mx r :=
      fun r h1 h2 h3 h4 h5 h6 h8' h9' => (k7 r h2 h3 h4 h5 h6).trans (k6 r h1 h2 h3 h8' h9')
    have pre7 : Steps mx m7 := .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (c6.trans c7)))))
    by_cases heq : memBytes Mr q 32 = memBytes Mr (p + 0x20) 32
    · rw [ite_eq_left heq] at a07
      obtain ⟨m8, e8, t8⟩ := t7.notTaken hc7 0x98 ksn_at_96 (by decide)
        (by rw [a07, show reg m7 x0 = 0 from t7.zero]; decide)
      obtain ⟨m9, e9, t9⟩ := t8.jump hc7 ksn_at_98 (off' := 0xB0) (by decide) (by rw [t8.pc]; decide)
      have hdup : ksDup Mr q p (k + 1) = true := by
        show (decide (memBytes Mr q 32 = memBytes Mr (p + 0x20) 32) || ksDup Mr q (p + 0x20) k) = true
        rw [decide_eq_true heq]; rfl
      refine ⟨m9, pre7.trans (.cons e8 (.single e9)), fun x hx => by rw [t9.mem]; exact hM7 x hx,
        fun r h1 h2 h3 h4 h5 h6 h8' h9' => by rw [t9.regs]; exact k7' r h1 h2 h3 h4 h5 h6 h8' h9',
        fun _ => by rw [t9.mem]; exact t9.self, fun h => absurd hdup (by rw [h]; decide)⟩
    · rw [ite_eq_right heq] at a07
      obtain ⟨m8, e8, t8⟩ := t7.taken hc7 0x82 ksn_at_96 (by decide)
        (by rw [a07, show reg m7 x0 = 0 from t7.zero]; decide)
      have hM8 : ∀ x, Sep (G + 0xFFFFFFFC) 4 x 1 → m8.mem x = Mr x := fun x hx => by rw [t8.mem]; exact hM7 x hx
      have t8' : St m8.mem KSN m8 0x82 (reg m8) := by rw [t8.mem]; exact t8.self
      have kv : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ ra → reg m8 r = reg m6 r := fun r h2 h3 h4 h5 h6 h1 =>
        by rw [t8.regs]; exact k7 r h2 h3 h4 h5 h6
      obtain ⟨mx', cx, hMx, kx, h1x, h2x⟩ := ih m8 (p + 0x20) (by omega) t8' hM8
        (by rw [kv sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp6)
        (by rw [kv 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact s06)
        (by rw [kv 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact s16)
        (by rw [kv 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact s96)
        (fun j hj => by
          have := hpS (j + 1) (by omega)
          rwa [show p + BitVec.ofNat 32 (32 * (j + 1 + 1)) = p + 0x20 + BitVec.ofNat 32 (32 * (j + 1)) by
            rw [show (p + 0x20 : Word) = p + BitVec.ofNat 32 32 from rfl, add_ofNat_assoc]; congr 2; omega] at this)
      have hrec : ksDup Mr q p (k + 1) = ksDup Mr q (p + 0x20) k := by
        show (decide (memBytes Mr q 32 = memBytes Mr (p + 0x20) 32) || ksDup Mr q (p + 0x20) k) = _
        rw [decide_eq_false heq]; rfl
      refine ⟨mx', pre7.trans (.cons e8 cx), hMx, fun r h1 h2 h3 h4 h5 h6 h8' h9' => ?_, fun h => h1x (hrec ▸ h),
        fun h => h2x (hrec ▸ h)⟩
      rw [kx r h1 h2 h3 h4 h5 h6 h8' h9', t8.regs]; exact k7' r h1 h2 h3 h4 h5 h6 h8' h9'

set_option maxRecDepth 40000 in
set_option maxHeartbeats 32000000 in
/-- **`KeySet::new`, as compiled**: with `ed25519_public_key_ok`, the 32-byte
equality, and `memcmp` where the image puts them, keys apart from the
0x970 bytes of stack below `sp` (which lie below 0x40000000), the constant
tables apart from that stack, and a result address `out`, it returns to `ra`
with `sp`, `gp`, `tp`, and `s0` through `s11` restored, and memory outside
its stack as `keySetMem` says. -/
theorem keySetNew_correct (m : Machine) {retAddr out keys len : Word} (E : PkEnv m.mem)
    (hc : CodeIn m.mem KSN keySetNewCode) (ha : CodeIn m.mem (KSN + 0xB8) arr32EqCode)
    (hm : CodeIn m.mem (KSN + 0xB8 + 0xC0F0) memcmpCode)
    (hpc : m.pc = KSN) (ha0 : reg m a0 = out) (ha1 : reg m a1 = keys) (ha2 : reg m a2 = len)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : (reg m sp).toNat % 4 = 0) (hsl : 0x970 ≤ (reg m sp).toNat) (hsw : (reg m sp).toNat ≤ 0x40000000)
    (hout : out.toNat % 4 = 0) (hkw : keys.toNat + len.toNat < 2 ^ 32) (sOc : Sep out 8 KSN keySetNewCode.length)
    (sK : Sep keys len.toNat (reg m sp + 0xFFFFF690) 0x970) (sO : Sep out 8 (reg m sp + 0xFFFFF690) 0x970)
    (sOne : Sep (BitVec.ofNat 32 edOneAddress) 40 (reg m sp + 0xFFFFF690) 0x970)
    (sD : Sep (BitVec.ofNat 32 edDAddress) 40 (reg m sp + 0xFFFFF690) 0x970)
    (sS : Sep (BitVec.ofNat 32 edSqrtM1Address) 40 (reg m sp + 0xFFFFF690) 0x970)
    (sPc : Sep (BitVec.ofNat 32 (img% edPrimeAddress)) 32 (reg m sp + 0xFFFFF690) 0x970)
    (sE1 : Sep (BitVec.ofNat 32 (img% p256OneAddress)) 32 (reg m sp + 0xFFFFF690) 0x970)
    (sE2 : Sep (BitVec.ofNat 32 (img% edPm1Address)) 32 (reg m sp + 0xFFFFF690) 0x970) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      (∀ q, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      ∀ x, Sep (reg m sp + 0xFFFFF690) 0x970 x 1 → m'.mem x = keySetMem m.mem out keys len x := by
  obtain ⟨S, hSd⟩ : ∃ S, reg m sp + 0xFFFFF690 = S := ⟨_, rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G, reg m sp + 0xFFFFFFD0 = G := ⟨_, rfl⟩
  rw [hSd] at sK sO sOne sD sS sPc sE1 sE2 ⊢
  have hSn : S.toNat = (reg m sp).toNat - 0x970 := by
    rw [← hSd, BitVec.toNat_add, show (0xFFFFF690 : Word).toNat = 2 ^ 32 - 0x970 from rfl]; omega
  have hGn : G.toNat = (reg m sp).toNat - 0x30 := by
    rw [← hGd, BitVec.toNat_add, show (0xFFFFFFD0 : Word).toNat = 2 ^ 32 - 0x30 from rfl]; omega
  have hGS : G = S + BitVec.ofNat 32 0x940 := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hGn, hSn]; omega)
  have hSG : G + 0xFFFFF6C0 = S := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, show (0xFFFFF6C0 : Word).toNat = 2 ^ 32 - 0x940 from rfl, hGn, hSn]; omega)
  have hspG : G + 0x30 = reg m sp := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, show (0x30 : Word).toNat = 0x30 from rfl, hGn]; omega)
  have hGa : G.toNat % 4 = 0 := by omega
  have hGw : G.toNat ≤ 0x40000000 := by omega
  have hGl : 0x940 ≤ G.toNat := by omega
  have fr : ∀ c l, c + l ≤ 0x30 → ∀ (x : Word) (n : Nat), Sep S 0x970 x n → Sep (G + BitVec.ofNat 32 c) l x n :=
    fun c l h x n hx => by rw [hGS, add_ofNat_assoc]; exact hx.sub (c := 0x940 + c) (l := l) (by omega)
  have hiS : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep S 0x970 x 1 := fun x hx =>
    sep_of_le (by omega) (by have := x.isLt; omega)
  have gLow : ∀ c, c + 4 ≤ 0x30 → (G + BitVec.ofNat 32 c).toNat + 4 ≤ 0x40000000 := fun c h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have s0 : St m.mem KSN m 0 (reg m) := ⟨by rw [hpc]; rfl, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, e1, t1⟩ := s0.aluImm hc ksn_at_0 (off' := 2) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFD0 = G from hGd] at t1
  have u1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  have f1 : ∀ r, r ≠ sp → upd (reg m) sp G r = reg m r := fun r h => updz hz h
  obtain ⟨m2, e2, t2⟩ := t1.sw hc ksn_at_2 (off' := 0x4) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x2C) (by decide))
  rw [u1sp, f1 ra (by decide)] at t2
  have hc2 := hc.store32 (v := reg m ra) (lowSep (gLow 0x2C (by omega)) (by decide) (by decide))
  obtain ⟨m3, e3, t3⟩ := t2.sw hc2 ksn_at_4 (off' := 0x6) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x28) (by decide))
  rw [u1sp, f1 8 (by decide)] at t3
  have hc3 := hc2.store32 (v := reg m 8) (lowSep (gLow 0x28 (by omega)) (by decide) (by decide))
  obtain ⟨m4, e4, t4⟩ := t3.sw hc3 ksn_at_6 (off' := 0x8) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x24) (by decide))
  rw [u1sp, f1 9 (by decide)] at t4
  have hc4 := hc3.store32 (v := reg m 9) (lowSep (gLow 0x24 (by omega)) (by decide) (by decide))
  obtain ⟨m5, e5, t5⟩ := t4.sw hc4 ksn_at_8 (off' := 0xA) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x20) (by decide))
  rw [u1sp, f1 18 (by decide)] at t5
  have hc5 := hc4.store32 (v := reg m 18) (lowSep (gLow 0x20 (by omega)) (by decide) (by decide))
  obtain ⟨m6, e6, t6⟩ := t5.sw hc5 ksn_at_a (off' := 0xC) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x1C) (by decide))
  rw [u1sp, f1 19 (by decide)] at t6
  have hc6 := hc5.store32 (v := reg m 19) (lowSep (gLow 0x1C (by omega)) (by decide) (by decide))
  obtain ⟨m7, e7, t7⟩ := t6.sw hc6 ksn_at_c (off' := 0xE) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x18) (by decide))
  rw [u1sp, f1 20 (by decide)] at t7
  have hc7 := hc6.store32 (v := reg m 20) (lowSep (gLow 0x18 (by omega)) (by decide) (by decide))
  obtain ⟨m8, e8, t8⟩ := t7.sw hc7 ksn_at_e (off' := 0x10) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x14) (by decide))
  rw [u1sp, f1 21 (by decide)] at t8
  have hc8 := hc7.store32 (v := reg m 21) (lowSep (gLow 0x14 (by omega)) (by decide) (by decide))
  obtain ⟨m9, e9, t9⟩ := t8.sw hc8 ksn_at_10 (off' := 0x12) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x10) (by decide))
  rw [u1sp, f1 22 (by decide)] at t9
  have hc9 := hc8.store32 (v := reg m 22) (lowSep (gLow 0x10 (by omega)) (by decide) (by decide))
  obtain ⟨m10, e10, t10⟩ := t9.sw hc9 ksn_at_12 (off' := 0x14) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0xC) (by decide))
  rw [u1sp, f1 23 (by decide)] at t10
  have hc10 := hc9.store32 (v := reg m 23) (lowSep (gLow 0xC (by omega)) (by decide) (by decide))
  obtain ⟨m11, e11, t11⟩ := t10.sw hc10 ksn_at_14 (off' := 0x16) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x8) (by decide))
  rw [u1sp, f1 24 (by decide)] at t11
  have hc11 := hc10.store32 (v := reg m 24) (lowSep (gLow 0x8 (by omega)) (by decide) (by decide))
  obtain ⟨m12, e12, t12⟩ := t11.sw hc11 ksn_at_16 (off' := 0x18) (by decide) (by rw [u1sp]; exact aligned_add hGa (k := 0x4) (by decide))
  rw [u1sp, f1 25 (by decide)] at t12
  obtain ⟨M11, hM11⟩ : ∃ M11, memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (m.mem) (G + 0x2C) (reg m ra)) (G + 0x28) (reg m 8)) (G + 0x24) (reg m 9)) (G + 0x20) (reg m 18)) (G + 0x1C) (reg m 19)) (G + 0x18) (reg m 20)) (G + 0x14) (reg m 21)) (G + 0x10) (reg m 22)) (G + 0xC) (reg m 23)) (G + 0x8) (reg m 24)) (G + 0x4) (reg m 25) = M11 := ⟨_, rfl⟩
  rw [hM11] at t12
  have M11out : ∀ x, Sep S 0x970 x 1 → M11 x = m.mem x := fun x hx => by
    rw [← hM11]
    exact (memStore32_get_sep (fr 0x4 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x8 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0xC 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x10 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x14 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x18 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x1C 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x20 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x24 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x28 4 (by omega) x 1 hx)).trans ((memStore32_get_sep (fr 0x2C 4 (by omega) x 1 hx))))))))))))
  have fl2c : memLoad32 M11 (G + 0x2C) = reg m ra := by
    rw [← hM11]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x4) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x8) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x10) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x14) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x18) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x1C) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x20) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x24) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x28) (n := 4) (d := 0x2C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl28 : memLoad32 M11 (G + 0x28) = reg m 8 := by
    rw [← hM11]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x4) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x8) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x10) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x14) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x18) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x1C) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x20) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x24) (n := 4) (d := 0x28) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl24 : memLoad32 M11 (G + 0x24) = reg m 9 := by
    rw [← hM11]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x4) (n := 4) (d := 0x24) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x8) (n := 4) (d := 0x24) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x24) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x10) (n := 4) (d := 0x24) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x14) (n := 4) (d := 0x24) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x18) (n := 4) (d := 0x24) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x1C) (n := 4) (d := 0x24) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x20) (n := 4) (d := 0x24) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl20 : memLoad32 M11 (G + 0x20) = reg m 18 := by
    rw [← hM11]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x4) (n := 4) (d := 0x20) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x8) (n := 4) (d := 0x20) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x20) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x10) (n := 4) (d := 0x20) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x14) (n := 4) (d := 0x20) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x18) (n := 4) (d := 0x20) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x1C) (n := 4) (d := 0x20) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl1c : memLoad32 M11 (G + 0x1C) = reg m 19 := by
    rw [← hM11]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x4) (n := 4) (d := 0x1C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x8) (n := 4) (d := 0x1C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x1C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x10) (n := 4) (d := 0x1C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x14) (n := 4) (d := 0x1C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x18) (n := 4) (d := 0x1C) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl18 : memLoad32 M11 (G + 0x18) = reg m 20 := by
    rw [← hM11]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x4) (n := 4) (d := 0x18) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x8) (n := 4) (d := 0x18) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x18) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x10) (n := 4) (d := 0x18) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x14) (n := 4) (d := 0x18) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl14 : memLoad32 M11 (G + 0x14) = reg m 21 := by
    rw [← hM11]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x4) (n := 4) (d := 0x14) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x8) (n := 4) (d := 0x14) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x14) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x10) (n := 4) (d := 0x14) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl10 : memLoad32 M11 (G + 0x10) = reg m 22 := by
    rw [← hM11]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x4) (n := 4) (d := 0x10) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x8) (n := 4) (d := 0x10) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0xC) (n := 4) (d := 0x10) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have flc : memLoad32 M11 (G + 0xC) = reg m 23 := by
    rw [← hM11]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x4) (n := 4) (d := 0xC) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x8) (n := 4) (d := 0xC) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl8 : memLoad32 M11 (G + 0x8) = reg m 24 := by
    rw [← hM11]
    refine (memLoad32_store32_sep (sep_offsets G (c := 0x4) (n := 4) (d := 0x8) (k := 4) (Or.inl (by omega)) (by omega) (by omega))).trans ?_
    exact memLoad32_store32_same _ _ _
  have fl4 : memLoad32 M11 (G + 0x4) = reg m 25 := by
    rw [← hM11]
    exact memLoad32_store32_same _ _ _
  have epi : ∀ (Mx : Word → BitVec 8) (mx : Machine), St Mx KSN mx 0x2C (reg mx) → CodeIn Mx KSN keySetNewCode →
      reg mx sp = G →
      (∀ c, 4 ≤ c → c + 4 ≤ 0x30 → memLoad32 Mx (G + BitVec.ofNat 32 c) = memLoad32 M11 (G + BitVec.ofNat 32 c)) →
      reg mx 3 = reg m 3 → reg mx 4 = reg m 4 → reg mx 26 = reg m 26 → reg mx 27 = reg m 27 →
      ∃ m', Steps mx m' ∧ m'.pc = retAddr ∧
        (∀ q, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧ m'.mem = Mx := by
    intro Mx mx s hcx hs hF h3 h4 h26 h27
    obtain ⟨n1, d1, u1⟩ := s.lw hcx ksn_at_2c (off' := 0x2E) (by decide)
      (by rw [hs]; exact aligned_add hGa (k := 0x2C) (by decide))
    rw [hs, show memLoad32 Mx (G + 0x2C) = reg m ra from (hF 0x2C (by omega) (by omega)).trans fl2c] at u1
    have q1 : ∀ r, r ≠ ra → reg n1 r = reg mx r := fun r h => by rw [u1.regs]; exact updz s.zero h
    have w1 : reg n1 ra = reg m ra := by rw [u1.regs]; simp +decide only [upd, ite_true, ite_false]
    have p1 : reg n1 sp = G := by rw [q1 sp (by decide)]; exact hs
    obtain ⟨n2, d2, u2⟩ := u1.self.lw hcx ksn_at_2e (off' := 0x30) (by decide)
      (by rw [p1]; exact aligned_add hGa (k := 0x28) (by decide))
    rw [p1, show memLoad32 Mx (G + 0x28) = reg m 8 from (hF 0x28 (by omega) (by omega)).trans fl28] at u2
    have q2 : ∀ r, r ≠ 8 → reg n2 r = reg n1 r := fun r h => by rw [u2.regs]; exact updz u1.self.zero h
    have w2 : reg n2 8 = reg m 8 := by rw [u2.regs]; simp +decide only [upd, ite_true, ite_false]
    have p2 : reg n2 sp = G := by rw [q2 sp (by decide)]; exact p1
    obtain ⟨n3, d3, u3⟩ := u2.self.lw hcx ksn_at_30 (off' := 0x32) (by decide)
      (by rw [p2]; exact aligned_add hGa (k := 0x24) (by decide))
    rw [p2, show memLoad32 Mx (G + 0x24) = reg m 9 from (hF 0x24 (by omega) (by omega)).trans fl24] at u3
    have q3 : ∀ r, r ≠ 9 → reg n3 r = reg n2 r := fun r h => by rw [u3.regs]; exact updz u2.self.zero h
    have w3 : reg n3 9 = reg m 9 := by rw [u3.regs]; simp +decide only [upd, ite_true, ite_false]
    have p3 : reg n3 sp = G := by rw [q3 sp (by decide)]; exact p2
    obtain ⟨n4, d4, u4⟩ := u3.self.lw hcx ksn_at_32 (off' := 0x34) (by decide)
      (by rw [p3]; exact aligned_add hGa (k := 0x20) (by decide))
    rw [p3, show memLoad32 Mx (G + 0x20) = reg m 18 from (hF 0x20 (by omega) (by omega)).trans fl20] at u4
    have q4 : ∀ r, r ≠ 18 → reg n4 r = reg n3 r := fun r h => by rw [u4.regs]; exact updz u3.self.zero h
    have w4 : reg n4 18 = reg m 18 := by rw [u4.regs]; simp +decide only [upd, ite_true, ite_false]
    have p4 : reg n4 sp = G := by rw [q4 sp (by decide)]; exact p3
    obtain ⟨n5, d5, u5⟩ := u4.self.lw hcx ksn_at_34 (off' := 0x36) (by decide)
      (by rw [p4]; exact aligned_add hGa (k := 0x1C) (by decide))
    rw [p4, show memLoad32 Mx (G + 0x1C) = reg m 19 from (hF 0x1C (by omega) (by omega)).trans fl1c] at u5
    have q5 : ∀ r, r ≠ 19 → reg n5 r = reg n4 r := fun r h => by rw [u5.regs]; exact updz u4.self.zero h
    have w5 : reg n5 19 = reg m 19 := by rw [u5.regs]; simp +decide only [upd, ite_true, ite_false]
    have p5 : reg n5 sp = G := by rw [q5 sp (by decide)]; exact p4
    obtain ⟨n6, d6, u6⟩ := u5.self.lw hcx ksn_at_36 (off' := 0x38) (by decide)
      (by rw [p5]; exact aligned_add hGa (k := 0x18) (by decide))
    rw [p5, show memLoad32 Mx (G + 0x18) = reg m 20 from (hF 0x18 (by omega) (by omega)).trans fl18] at u6
    have q6 : ∀ r, r ≠ 20 → reg n6 r = reg n5 r := fun r h => by rw [u6.regs]; exact updz u5.self.zero h
    have w6 : reg n6 20 = reg m 20 := by rw [u6.regs]; simp +decide only [upd, ite_true, ite_false]
    have p6 : reg n6 sp = G := by rw [q6 sp (by decide)]; exact p5
    obtain ⟨n7, d7, u7⟩ := u6.self.lw hcx ksn_at_38 (off' := 0x3A) (by decide)
      (by rw [p6]; exact aligned_add hGa (k := 0x14) (by decide))
    rw [p6, show memLoad32 Mx (G + 0x14) = reg m 21 from (hF 0x14 (by omega) (by omega)).trans fl14] at u7
    have q7 : ∀ r, r ≠ 21 → reg n7 r = reg n6 r := fun r h => by rw [u7.regs]; exact updz u6.self.zero h
    have w7 : reg n7 21 = reg m 21 := by rw [u7.regs]; simp +decide only [upd, ite_true, ite_false]
    have p7 : reg n7 sp = G := by rw [q7 sp (by decide)]; exact p6
    obtain ⟨n8, d8, u8⟩ := u7.self.lw hcx ksn_at_3a (off' := 0x3C) (by decide)
      (by rw [p7]; exact aligned_add hGa (k := 0x10) (by decide))
    rw [p7, show memLoad32 Mx (G + 0x10) = reg m 22 from (hF 0x10 (by omega) (by omega)).trans fl10] at u8
    have q8 : ∀ r, r ≠ 22 → reg n8 r = reg n7 r := fun r h => by rw [u8.regs]; exact updz u7.self.zero h
    have w8 : reg n8 22 = reg m 22 := by rw [u8.regs]; simp +decide only [upd, ite_true, ite_false]
    have p8 : reg n8 sp = G := by rw [q8 sp (by decide)]; exact p7
    obtain ⟨n9, d9, u9⟩ := u8.self.lw hcx ksn_at_3c (off' := 0x3E) (by decide)
      (by rw [p8]; exact aligned_add hGa (k := 0xC) (by decide))
    rw [p8, show memLoad32 Mx (G + 0xC) = reg m 23 from (hF 0xC (by omega) (by omega)).trans flc] at u9
    have q9 : ∀ r, r ≠ 23 → reg n9 r = reg n8 r := fun r h => by rw [u9.regs]; exact updz u8.self.zero h
    have w9 : reg n9 23 = reg m 23 := by rw [u9.regs]; simp +decide only [upd, ite_true, ite_false]
    have p9 : reg n9 sp = G := by rw [q9 sp (by decide)]; exact p8
    obtain ⟨n10, d10, u10⟩ := u9.self.lw hcx ksn_at_3e (off' := 0x40) (by decide)
      (by rw [p9]; exact aligned_add hGa (k := 0x8) (by decide))
    rw [p9, show memLoad32 Mx (G + 0x8) = reg m 24 from (hF 0x8 (by omega) (by omega)).trans fl8] at u10
    have q10 : ∀ r, r ≠ 24 → reg n10 r = reg n9 r := fun r h => by rw [u10.regs]; exact updz u9.self.zero h
    have w10 : reg n10 24 = reg m 24 := by rw [u10.regs]; simp +decide only [upd, ite_true, ite_false]
    have p10 : reg n10 sp = G := by rw [q10 sp (by decide)]; exact p9
    obtain ⟨n11, d11, u11⟩ := u10.self.lw hcx ksn_at_40 (off' := 0x42) (by decide)
      (by rw [p10]; exact aligned_add hGa (k := 0x4) (by decide))
    rw [p10, show memLoad32 Mx (G + 0x4) = reg m 25 from (hF 0x4 (by omega) (by omega)).trans fl4] at u11
    have q11 : ∀ r, r ≠ 25 → reg n11 r = reg n10 r := fun r h => by rw [u11.regs]; exact updz u10.self.zero h
    have w11 : reg n11 25 = reg m 25 := by rw [u11.regs]; simp +decide only [upd, ite_true, ite_false]
    have p11 : reg n11 sp = G := by rw [q11 sp (by decide)]; exact p10
    obtain ⟨n12, d12, u12⟩ := u11.self.aluImm hcx ksn_at_42 (off' := 0x44) (by decide)
    obtain ⟨n13, d13, pc13, mem13, regs13⟩ := u12.jalr hcx ksn_at_44
    have z11 : ∀ r, r ≠ ra → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 22 → r ≠ 23 → r ≠ 24 →
        r ≠ 25 → reg n11 r = reg mx r := fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 => by
      rw [q11 r h11, q10 r h10, q9 r h9, q8 r h8, q7 r h7, q6 r h6, q5 r h5, q4 r h4, q3 r h3, q2 r h2, q1 r h1]
    have vra : reg n11 ra = reg m ra := by rw [q11 ra (by decide), q10 ra (by decide), q9 ra (by decide), q8 ra (by decide), q7 ra (by decide), q6 ra (by decide), q5 ra (by decide), q4 ra (by decide), q3 ra (by decide), q2 ra (by decide)]; exact w1
    have v8 : reg n11 8 = reg m 8 := by rw [q11 8 (by decide), q10 8 (by decide), q9 8 (by decide), q8 8 (by decide), q7 8 (by decide), q6 8 (by decide), q5 8 (by decide), q4 8 (by decide), q3 8 (by decide)]; exact w2
    have v9 : reg n11 9 = reg m 9 := by rw [q11 9 (by decide), q10 9 (by decide), q9 9 (by decide), q8 9 (by decide), q7 9 (by decide), q6 9 (by decide), q5 9 (by decide), q4 9 (by decide)]; exact w3
    have v18 : reg n11 18 = reg m 18 := by rw [q11 18 (by decide), q10 18 (by decide), q9 18 (by decide), q8 18 (by decide), q7 18 (by decide), q6 18 (by decide), q5 18 (by decide)]; exact w4
    have v19 : reg n11 19 = reg m 19 := by rw [q11 19 (by decide), q10 19 (by decide), q9 19 (by decide), q8 19 (by decide), q7 19 (by decide), q6 19 (by decide)]; exact w5
    have v20 : reg n11 20 = reg m 20 := by rw [q11 20 (by decide), q10 20 (by decide), q9 20 (by decide), q8 20 (by decide), q7 20 (by decide)]; exact w6
    have v21 : reg n11 21 = reg m 21 := by rw [q11 21 (by decide), q10 21 (by decide), q9 21 (by decide), q8 21 (by decide)]; exact w7
    have v22 : reg n11 22 = reg m 22 := by rw [q11 22 (by decide), q10 22 (by decide), q9 22 (by decide)]; exact w8
    have v23 : reg n11 23 = reg m 23 := by rw [q11 23 (by decide), q10 23 (by decide)]; exact w9
    have v24 : reg n11 24 = reg m 24 := by rw [q11 24 (by decide)]; exact w10
    have v25 : reg n11 25 = reg m 25 := w11
    have r13 : ∀ r, r ≠ sp → reg n13 r = reg n11 r := fun r h => by rw [regs13]; exact updz u11.self.zero h
    refine ⟨n13, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10
      (.cons d11 (.cons d12 (.single d13)))))))))))), ?_, fun q hq => ?_, by rw [mem13]⟩
    · rw [pc13, add_lit_zero, updz u11.self.zero (show ra ≠ sp by decide), vra, hra, hret]
    · have hq' : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 8 ∨ q = 9 ∨ q = 18 ∨ q = 19 ∨ q = 20 ∨ q = 21 ∨ q = 22 ∨ q = 23 ∨
          q = 24 ∨ q = 25 ∨ q = 26 ∨ q = 27 := by revert q; decide
      rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [regs13]; simp +decide only [upd, ite_true, ite_false]; rw [p11, ← hspG]; rfl
      · rw [r13 3 (by decide), z11 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h3
      · rw [r13 4 (by decide), z11 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h4
      · rw [r13 8 (by decide)]; exact v8
      · rw [r13 9 (by decide)]; exact v9
      · rw [r13 18 (by decide)]; exact v18
      · rw [r13 19 (by decide)]; exact v19
      · rw [r13 20 (by decide)]; exact v20
      · rw [r13 21 (by decide)]; exact v21
      · rw [r13 22 (by decide)]; exact v22
      · rw [r13 23 (by decide)]; exact v23
      · rw [r13 24 (by decide)]; exact v24
      · rw [r13 25 (by decide)]; exact v25
      · rw [r13 26 (by decide), z11 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h26
      · rw [r13 27 (by decide), z11 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h27
  have hO4 : Sep out 4 S 0x970 := by have := sO.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
  have err24 : ∀ (Mx : Word → BitVec 8) (mx : Machine) (fx : Fin 32 → Word), St Mx KSN mx 0x24 fx →
      CodeIn Mx KSN keySetNewCode → fx 19 = out → fx sp = G →
      (∀ c, 4 ≤ c → c + 4 ≤ 0x30 → memLoad32 Mx (G + BitVec.ofNat 32 c) = memLoad32 M11 (G + BitVec.ofNat 32 c)) →
      fx 3 = reg m 3 → fx 4 = reg m 4 → fx 26 = reg m 26 → fx 27 = reg m 27 →
      ∃ m', Steps mx m' ∧ m'.pc = retAddr ∧
        (∀ q, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        m'.mem = memStore8 (memStore32 Mx out 0) (out + 0x4) ((fx a0).extractLsb' 0 8) := by
    intro Mx mx fx s hcx h19 hs hF h3 h4 h26 h27
    have hzx := s.zero
    obtain ⟨o1, f1', w1⟩ := s.sw hcx ksn_at_24 (off' := 0x28) (by decide)
      (by rw [h19, show out + (0x0 : Word) = out from BitVec.add_zero out]; exact hout)
    rw [h19, show out + (0x0 : Word) = out from BitVec.add_zero out, show fx x0 = 0 from hzx] at w1
    have hc1 := hcx.store32 (v := 0) (a := out) (by have := sOc.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this)
    obtain ⟨o2, f2', w2⟩ := w1.sb hc1 ksn_at_28 (off' := 0x2C) (by decide)
    rw [h19] at w2
    have hc2 := hc1.store8 (v := (fx a0).extractLsb' 0 8) (a := out + 0x4) (sOc.sub (c := 4) (l := 1) (by omega))
    obtain ⟨m', c', pc', k', mem'⟩ := epi _ _ w2.self hc2 (by rw [w2.regs]; exact hs)
      (fun c h1 h2 => by
        rw [← hF c h1 h2]
        exact (memLoad32_congr fun j hj => memStore8_ne (by
          rw [add_ofNat_assoc, hGS, add_ofNat_assoc]
          exact fun e => sO 4 (by omega) (0x940 + (c + j)) (by omega) e.symm)).trans
          (memLoad32_store32_sep (by rw [hGS, add_ofNat_assoc]; exact hO4.subR (c := 0x940 + c) (l := 4) (by omega))))
      (by rw [w2.regs]; exact h3) (by rw [w2.regs]; exact h4) (by rw [w2.regs]; exact h26) (by rw [w2.regs]; exact h27)
    exact ⟨m', .cons f1' (.cons f2' c'), pc', k', mem'⟩
  have hcM11 : ∀ {b : Word} {code : List Nat}, 0x40000000 ≤ b.toNat → b.toNat + code.length ≤ 2 ^ 32 →
      CodeIn m.mem b code → CodeIn M11 b code := fun hb hbl hc' i hi => by
    rw [M11out _ (hiS _ (code_hi hb hbl hi))]; exact hc' i hi
  have hc12 := hcM11 (by decide) (by decide) hc
  have hS940 : ∀ x : Word, Sep S 0x970 x 1 → Sep S 0x940 x 1 := fun x hx => by
    have := hx.sub (c := 0) (l := 0x940) (by omega); rwa [add_ofNat_zero] at this
  have hiS9 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep S 0x940 x 1 := fun x hx => hS940 x (hiS x hx)
  have fin : ∀ (Mx : Word → BitVec 8), (∀ x, Sep S 0x940 x 1 → Mx x = M11 x) → ∀ x, Sep S 0x970 x 1 → Mx x = m.mem x :=
    fun Mx h x hx => (h x (hS940 x hx)).trans (M11out x hx)
  have frameOk : ∀ (Mx : Word → BitVec 8), (∀ x, Sep S 0x940 x 1 → Mx x = M11 x) →
      ∀ c, 4 ≤ c → c + 4 ≤ 0x30 → memLoad32 Mx (G + BitVec.ofNat 32 c) = memLoad32 M11 (G + BitVec.ofNat 32 c) :=
    fun Mx h c h1 h2 => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; refine h _ ?_
      rw [hGS, add_ofNat_assoc]
      have := sep_offsets S (c := 0) (n := 0x940) (d := 0x940 + (c + j)) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
  obtain ⟨m13, e13, t13⟩ := t12.alu hc12 ksn_at_18 (off' := 0x1A) (by decide)
  obtain ⟨m14, e14, t14⟩ := t13.aluImm hc12 ksn_at_1a (off' := 0x1E) (by decide)
  obtain ⟨m15, e15, t15⟩ := t14.alu hc12 ksn_at_1e (off' := 0x20) (by decide)
  have v15a1 : reg m15 a1 = aluEval .and len 0x1F := by rw [t15.regs]; simp +decide [upd, ha2]
  have v15a2 : reg m15 a2 = len := by rw [t15.regs]; simp +decide [upd, ha2]
  have v1518 : reg m15 18 = keys := by rw [t15.regs]; simp +decide [upd, aluEval, ha1]
  have v1519 : reg m15 19 = out := by rw [t15.regs]; simp +decide [upd, aluEval, ha0]
  have v15sp : reg m15 sp = G := by rw [t15.regs]; simp +decide [upd]
  have v153 : reg m15 3 = reg m 3 := by rw [t15.regs]; simp +decide [upd]
  have v154 : reg m15 4 = reg m 4 := by rw [t15.regs]; simp +decide [upd]
  have v1526 : reg m15 26 = reg m 26 := by rw [t15.regs]; simp +decide [upd]
  have v1527 : reg m15 27 = reg m 27 := by rw [t15.regs]; simp +decide [upd]
  have u15 := t15.self
  have us21 : ∀ (g : Fin 32 → Word) (v : Word), (21 : Fin 32).val ≠ 0 → upd g 21 v 21 = v := fun g v h => by
    simp only [upd, h, ↓reduceIte]
  have hz15 := u15.zero
  have pre15 : Steps m m15 := .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8 (.cons e9
    (.cons e10 (.cons e11 (.cons e12 (.cons e13 (.cons e14 (.single e15))))))))))))))
  have err5 : ∀ (mx : Machine) (fx : Fin 32 → Word), Steps m mx → St M11 KSN mx 0x22 fx → fx 19 = out → fx sp = G →
      fx 3 = reg m 3 → fx 4 = reg m 4 → fx 26 = reg m 26 → fx 27 = reg m 27 →
      ¬ (len.toNat % 32 = 0 ∧ len.toNat ≤ 0x9F ∧ 32 ≤ len.toNat) →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
        (∀ q, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        ∀ x, Sep S 0x970 x 1 → m'.mem x = keySetMem m.mem out keys len x := by
    intro mx fx c s h19 hs h3 h4 h26 h27 hn
    obtain ⟨o1, f1', w1⟩ := s.aluImm hc12 ksn_at_22 (off' := 0x24) (by decide)
    have hzx := s.zero
    obtain ⟨m', c', pc', k', mem'⟩ := err24 _ _ _ w1 hc12 (by rw [updz hzx (by decide)]; exact h19)
      (by rw [updz hzx (by decide)]; exact hs) (fun _ _ _ => rfl) (by rw [updz hzx (by decide)]; exact h3)
      (by rw [updz hzx (by decide)]; exact h4) (by rw [updz hzx (by decide)]; exact h26) (by rw [updz hzx (by decide)]; exact h27)
    refine ⟨m', c.trans (.cons f1' c'), pc', k', fun x hx => ?_⟩
    rw [mem', show ((upd fx a0 (aluEval .add (fx x0) 5)) a0).extractLsb' 0 8 = 5 by simp +decide only [upd, ite_true, ite_false]; rw [hzx]; rfl]
    unfold keySetMem; rw [ite_eq_right hn]
    exact memStore8_congr (memStore32_congr (M11out x hx))
  by_cases hm32 : ¬ len.toNat % 32 = 0
  · obtain ⟨m16, e16, t16⟩ := u15.notTaken hc12 0x22 ksn_at_20 (by decide)
      (by
        rw [v15a1, show reg m15 x0 = 0 from hz15]
        refine beq_eq_false_iff_ne.mpr fun h => hm32 ?_
        have := congrArg BitVec.toNat h; rwa [and1f_toNat] at this)
    exact err5 m16 _ (pre15.trans (.single e16)) t16 v1519 v15sp v153 v154 v1526 v1527 fun h => hm32 h.1
  replace hm32 := Decidable.of_not_not hm32
  obtain ⟨m16, e16, t16⟩ := u15.taken hc12 0x46 ksn_at_20 (by decide)
    (by
      rw [v15a1, show reg m15 x0 = 0 from hz15,
        show aluEval .and len 0x1F = 0 from BitVec.eq_of_toNat_eq (by rw [and1f_toNat]; exact hm32)]
      exact bt_beq_self _)
  obtain ⟨m17, e17, t17⟩ := t16.alu hc12 ksn_at_46 (off' := 0x48) (by decide)
  obtain ⟨m18, e18, t18⟩ := t17.aluImm hc12 ksn_at_48 (off' := 0x4C) (by decide)
  have q18 : ∀ r, r ≠ a0 → r ≠ 20 → reg m18 r = reg m15 r := fun r h0 h20 => by
    rw [t18.regs, updz t17.zero h0, updz hz15 h20]
  have v18a0 : reg m18 a0 = 0x9F := by rw [t18.regs]; simp +decide only [upd, ite_true, ite_false]
  have v1820 : reg m18 20 = len := by
    rw [t18.regs]; simp +decide only [upd, ite_true, ite_false]; rw [v15a2]; exact BitVec.zero_add len
  have u18 := t18.self
  have pre18 : Steps m m18 := pre15.trans (.cons e16 (.cons e17 (.single e18)))
  by_cases hle : ¬ len.toNat ≤ 0x9F
  · obtain ⟨m19, e19, t19⟩ := u18.taken hc12 0x22 ksn_at_4c (by decide)
      (by rw [v18a0, q18 a2 (by decide) (by decide), v15a2]; exact decide_eq_true (by
        show (0x9F : Word).toNat < len.toNat; rw [show (0x9F : Word).toNat = 0x9F from rfl]; omega))
    exact err5 m19 _ (pre18.trans (.single e19)) t19 (by rw [q18 19 (by decide) (by decide)]; exact v1519)
      (by rw [q18 sp (by decide) (by decide)]; exact v15sp) (by rw [q18 3 (by decide) (by decide)]; exact v153)
      (by rw [q18 4 (by decide) (by decide)]; exact v154) (by rw [q18 26 (by decide) (by decide)]; exact v1526)
      (by rw [q18 27 (by decide) (by decide)]; exact v1527) fun h => hle h.2.1
  replace hle := Decidable.of_not_not hle
  obtain ⟨m19, e19, t19⟩ := u18.notTaken hc12 0x50 ksn_at_4c (by decide)
    (by rw [v18a0, q18 a2 (by decide) (by decide), v15a2]; exact decide_eq_false (by
      show ¬ (0x9F : Word).toNat < len.toNat; rw [show (0x9F : Word).toNat = 0x9F from rfl]; omega))
  obtain ⟨m20, e20, t20⟩ := t19.aluImm hc12 ksn_at_50 (off' := 0x54) (by decide)
  rw [v1820] at t20
  have hz18 := u18.zero
  by_cases h32 : ¬ 32 ≤ len.toNat
  · obtain ⟨m21, e21, t21⟩ := t20.taken hc12 0x22 ksn_at_54 (by decide)
      (by
        rw [us21 _ _ (by decide), show upd (reg m18) 21 (aluEval .srl len 5) x0 = 0 from rfl,
          show aluEval .srl len 5 = 0 from BitVec.eq_of_toNat_eq (by rw [srl5_toNat]; show len.toNat / 32 = 0; omega)]
        exact bt_beq_self _)
    exact err5 m21 _ (pre18.trans (.cons e19 (.cons e20 (.single e21)))) t21
      (by rw [updz hz18 (by decide), q18 19 (by decide) (by decide)]; exact v1519)
      (by rw [updz hz18 (by decide), q18 sp (by decide) (by decide)]; exact v15sp)
      (by rw [updz hz18 (by decide), q18 3 (by decide) (by decide)]; exact v153)
      (by rw [updz hz18 (by decide), q18 4 (by decide) (by decide)]; exact v154)
      (by rw [updz hz18 (by decide), q18 26 (by decide) (by decide)]; exact v1526)
      (by rw [updz hz18 (by decide), q18 27 (by decide) (by decide)]; exact v1527) fun h => h32 h.2.2
  replace h32 := Decidable.of_not_not h32
  obtain ⟨n, hnd⟩ : ∃ n, len.toNat / 32 = n := ⟨_, rfl⟩
  have hlen : len.toNat = 32 * n := by omega
  have hn1 : 1 ≤ n := by omega
  have hn4 : n ≤ 4 := by omega
  have hS5 : aluEval .srl len 5 = BitVec.ofNat 32 n := BitVec.eq_of_toNat_eq (by
    rw [srl5_toNat, BitVec.toNat_ofNat, hnd]; omega)
  rw [hS5] at t20
  obtain ⟨m21, e21, t21⟩ := t20.notTaken hc12 0x58 ksn_at_54 (by decide)
    (by
      rw [us21 _ _ (by decide), show upd (reg m18) 21 (BitVec.ofNat 32 n) x0 = 0 from rfl]
      refine beq_eq_false_iff_ne.mpr fun h => ?_
      have := congrArg BitVec.toNat h; rw [BitVec.toNat_ofNat] at this
      exact absurd this (by show n % 2 ^ 32 ≠ 0; omega))
  obtain ⟨m22, e22, t22⟩ := t21.aluImm hc12 ksn_at_58 (off' := 0x5A) (by decide)
  obtain ⟨m23, e23, t23⟩ := t22.aluImm hc12 ksn_at_5a (off' := 0x5E) (by decide)
  obtain ⟨m24, e24, t24⟩ := t23.alu hc12 ksn_at_5e (off' := 0x62) (by decide)
  obtain ⟨m25, e25, t25⟩ := t24.aluImm hc12 ksn_at_62 (off' := 0x64) (by decide)
  obtain ⟨m26, e26, t26⟩ := t25.alu hc12 ksn_at_64 (off' := 0x66) (by decide)
  have hsll : aluEval .sll (BitVec.ofNat 32 n) 5 = len := BitVec.eq_of_toNat_eq (by
    rw [sll5_toNat, BitVec.toNat_ofNat]; omega)
  have w18 : reg m18 18 = keys := (q18 18 (by decide) (by decide)).trans v1518
  have g26 : ∀ r, r ≠ 21 → r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → reg m26 r = reg m18 r := fun r h1 h2 h3 h4 h5 => by
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; rw [t26.self.zero, hz18]
    rw [t26.regs]; simp only [upd, hr, h1, h2, h3, h4, h5, ↓reduceIte]
  have v2621 : reg m26 21 = BitVec.ofNat 32 n := by rw [t26.regs]; simp +decide only [upd, ite_true, ite_false]
  have v2622 : reg m26 22 = BitVec.ofNat 32 (32 * 0) := by rw [t26.regs]; simp +decide only [upd, ite_true, ite_false]
  have v2623 : reg m26 23 = keys + len := by
    rw [t26.regs]; simp +decide only [upd, ite_true, ite_false]; rw [w18, hsll]; rfl
  have v2624 : reg m26 24 = BitVec.ofNat 32 (32 * (n - 1)) := by
    rw [t26.regs]; simp +decide only [upd, ite_true, ite_false]; rw [hsll]
    apply BitVec.eq_of_toNat_eq
    show (len + 0xFFFFFFE0).toNat = (BitVec.ofNat 32 (32 * (n - 1))).toNat
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0xFFFFFFE0 : Word).toNat = 4294967264 from rfl]; omega
  have v2625 : reg m26 25 = keys + BitVec.ofNat 32 (32 * 0) := by
    rw [t26.regs]; simp +decide only [upd, ite_true, ite_false]; rw [w18]; exact (BitVec.zero_add keys).trans (add_ofNat_zero keys).symm
  have outS : ∀ (b : Word) (L : Nat), Sep b L S 0x970 → ∀ t, t < L → Sep S 0x970 (b + BitVec.ofNat 32 t) 1 :=
    fun b L h t ht => (h.sub (c := t) (l := 1) (by omega)).symm
  have mbEq : ∀ (Mx : Word → BitVec 8), (∀ x, Sep S 0x940 x 1 → Mx x = M11 x) → ∀ (b : Word) (L : Nat),
      Sep b L S 0x970 → ∀ t, t + 32 ≤ L → memBytes Mx (b + BitVec.ofNat 32 t) 32 = memBytes m.mem (b + BitVec.ofNat 32 t) 32 :=
    fun Mx h b L hb t ht => memBytes_eq_of fun j hj => by
      rw [add_ofNat_assoc]; exact fin Mx h _ (outS b L hb (t + j) (by omega))
  have mbEq0 : ∀ (Mx : Word → BitVec 8), (∀ x, Sep S 0x940 x 1 → Mx x = M11 x) → ∀ (b : Word),
      Sep b 32 S 0x970 → memBytes Mx b 32 = memBytes m.mem b 32 := fun Mx h b hb => by
    have := mbEq Mx h b 32 hb 0 (by omega); rwa [add_ofNat_zero] at this
  have fwEq : ∀ (Mx : Word → BitVec 8), (∀ x, Sep S 0x940 x 1 → Mx x = M11 x) → ∀ (b : Word),
      Sep b 40 S 0x970 → feW Mx b = feW m.mem b := fun Mx h b hb =>
    feW_eq2 fun i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact fin Mx h _ (outS b 40 hb (4 * i + j) (by omega))
  have codeX : ∀ (Mx : Word → BitVec 8), (∀ x, Sep S 0x940 x 1 → Mx x = M11 x) → ∀ {b : Word} {code : List Nat},
      0x40000000 ≤ b.toNat → b.toNat + code.length ≤ 2 ^ 32 → CodeIn m.mem b code → CodeIn Mx b code :=
    fun Mx h b code hb hbl hc' i hi => by
      rw [h _ (hiS9 _ (code_hi hb hbl hi)), M11out _ (hiS _ (code_hi hb hbl hi))]; exact hc' i hi
  have hkey : ∀ t, t + 32 ≤ len.toNat → (keys + BitVec.ofNat 32 t).toNat = keys.toNat + t := fun t ht => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hG4S : G + 0xFFFFFFFC = S + BitVec.ofNat 32 0x93C := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, show (0xFFFFFFFC : Word).toNat = 2 ^ 32 - 4 from rfl, hGn, hSn]
    omega)
  have keyStk : ∀ t, t + 32 ≤ len.toNat → Sep (G + 0xFFFFFFFC) 4 (keys + BitVec.ofNat 32 t) 32 := fun t ht => by
    rw [hG4S]; exact ((sK.sub (c := t) (l := 32) (by omega)).subR (c := 0x93C) (l := 4) (by omega)).symm
  have keyS : ∀ t, t + 32 ≤ len.toNat → Sep (keys + BitVec.ofNat 32 t) 32 S 0x970 := fun t ht =>
    sK.sub (c := t) (l := 32) (by omega)
  let P : Nat → Prop := fun k => ∀ (mx : Machine) (i : Nat), i + k + 1 = n →
    St mx.mem KSN mx 0x6A (reg mx) → (∀ x, Sep S 0x940 x 1 → mx.mem x = M11 x) →
    reg mx sp = G → reg mx 18 = keys → reg mx 19 = out → reg mx 20 = len → reg mx 21 = BitVec.ofNat 32 n →
    reg mx 22 = BitVec.ofNat 32 i → reg mx 23 = keys + len → reg mx 24 = BitVec.ofNat 32 (32 * k) →
    reg mx 25 = keys + BitVec.ofNat 32 (32 * i) →
    reg mx 3 = reg m 3 → reg mx 4 = reg m 4 → reg mx 26 = reg m 26 → reg mx 27 = reg m 27 →
    ∃ m', Steps mx m' ∧ m'.pc = retAddr ∧
      (∀ q, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      ∀ x, Sep S 0x970 x 1 → m'.mem x = (match ksOuter m.mem (keys + BitVec.ofNat 32 (32 * i)) k (k + 1) with
        | none => memStore32 (memStore32 m.mem out keys) (out + 4) len
        | some c => memStore8 (memStore32 m.mem out 0) (out + 4) c) x
  have step : ∀ k, (0 < k → P (k - 1)) → P k := by
    intro k hP mx i hik s hR hsp h18 h19 h20 h21 h22 h23 h24 h25 h3 h4 h26 h27
    obtain ⟨q, hq⟩ : ∃ q, keys + BitVec.ofNat 32 (32 * i) = q := ⟨_, rfl⟩
    rw [hq] at h25 ⊢
    have hqn : q.toNat = keys.toNat + 32 * i := by rw [← hq]; exact hkey _ (by omega)
    have hqS : Sep q 32 S 0x970 := hq ▸ keyS (32 * i) (by omega)
    have hz := s.zero
    have hcx := codeX mx.mem hR (by decide) (by decide) hc
    obtain ⟨n1, d1, u1⟩ := s.alu hcx ksn_at_6a (off' := 0x6C) (by decide)
    obtain ⟨n2, c2, pc2, mem2, regs2⟩ := u1.callRa (cb := PKO) hcx ksn_at_6c ksn_at_70 (by decide) (by decide)
    have a02 : reg n2 a0 = q := by rw [regs2]; simp +decide only [upd, ite_true, ite_false]; rw [h25]; exact BitVec.zero_add q
    have ra2 : reg n2 ra = KSN + BitVec.ofNat 32 (0x6C + 8) := by rw [regs2]; simp +decide only [upd, ite_true, ite_false]
    have g2 : ∀ r, r ≠ a0 → r ≠ ra → reg n2 r = reg mx r := fun r h0 h1 => by rw [regs2, updz u1.zero h1, updz hz h0]
    have sp2 : reg n2 sp = G := (g2 sp (by decide) (by decide)).trans hsp
    have hR2 : ∀ x, Sep S 0x940 x 1 → n2.mem x = M11 x := by rw [mem2]; exact hR
    have s940 : ∀ {a : Word} {L : Nat}, Sep a L S 0x970 → Sep a L (G + 0xFFFFF6C0) 0x940 := fun h => by
      rw [hSG]; have := h.subR (c := 0) (l := 0x940) (by omega); rwa [add_ofNat_zero] at this
    obtain ⟨n3, c3, pc3, sp3, k3, a03, fr3⟩ := pkOk_correct n2
      (E.hi (fun x hx => fin n2.mem hR2 x (hiS x hx)) (fwEq n2.mem hR2 _ sOne)) pc2 a02 ra2
      (even_clear _ (by decide)) sp2 hGa hGl hGw (by omega) (s940 hqS) (s940 sOne) (s940 sD) (s940 sS) (s940 sPc)
      (s940 sE1) (s940 sE2)
    have hpk : pkOkSpec (memBytes n2.mem (BitVec.ofNat 32 (img% edPrimeAddress)) 32) (memBytes n2.mem (BitVec.ofNat 32 (img% p256OneAddress)) 32)
        (memBytes n2.mem (BitVec.ofNat 32 (img% edPm1Address)) 32) (feW n2.mem (BitVec.ofNat 32 edOneAddress))
        (feW n2.mem (BitVec.ofNat 32 edDAddress)) (feW n2.mem (BitVec.ofNat 32 edSqrtM1Address)) (memBytes n2.mem q 32) =
        pkOkAt m.mem q := by
      unfold pkOkAt
      rw [mbEq0 _ hR2 _ sPc, mbEq0 _ hR2 _ sE1, mbEq0 _ hR2 _ sE2, fwEq _ hR2 _ sOne, fwEq _ hR2 _ sD, fwEq _ hR2 _ sS,
        mbEq0 _ hR2 _ hqS]
    rw [hpk] at a03
    rw [hSG] at fr3
    have hR3 : ∀ x, Sep S 0x940 x 1 → n3.mem x = M11 x := fun x hx => (fr3 x hx).trans (hR2 x hx)
    have t3 : St n3.mem KSN n3 0x74 (reg n3) := ⟨by rw [pc3], rfl, fun _ => rfl⟩
    have hc3 := codeX n3.mem hR3 (by decide) (by decide) hc
    have w3 : ∀ r, r.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n3 r = reg mx r := fun r hr => by
      rw [k3 r (by revert r; decide), g2 r (by revert r hr; decide) (by revert r hr; decide)]
    have pre3 : Steps mx n3 := .cons d1 (c2.trans c3)
    have v3 : ∀ r, r.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n3 r = reg mx r := w3
    have e24s : ∀ (Mx : Word → BitVec 8) (my : Machine) (fy : Fin 32 → Word) (v : BitVec 8), Steps mx my →
        St Mx KSN my 0x24 fy → (∀ x, Sep S 0x940 x 1 → Mx x = M11 x) → fy 19 = out → fy sp = G →
        fy 3 = reg m 3 → fy 4 = reg m 4 → fy 26 = reg m 26 → fy 27 = reg m 27 → (fy a0).extractLsb' 0 8 = v →
        ∃ m', Steps mx m' ∧ m'.pc = retAddr ∧
          (∀ q, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
          ∀ x, Sep S 0x970 x 1 → m'.mem x = memStore8 (memStore32 m.mem out 0) (out + 4) v x := by
      intro Mx my fy v cy sy hRy h19' hsp' h3' h4' h26' h27' hv
      obtain ⟨m', c', pc', k', mem'⟩ := err24 Mx my fy sy (codeX Mx hRy (by decide) (by decide) hc) h19' hsp'
        (frameOk Mx hRy) h3' h4' h26' h27'
      refine ⟨m', cy.trans c', pc', k', fun x hx => ?_⟩
      rw [mem', hv]; exact memStore8_congr (memStore32_congr (fin Mx hRy x hx))
    by_cases hok : ¬ pkOkAt m.mem q = true
    · have hf : pkOkAt m.mem q = false := by cases h : pkOkAt m.mem q; rfl; exact absurd h hok
      rw [hf] at a03
      obtain ⟨n4, d4, u4⟩ := t3.taken hc3 0xB4 ksn_at_74 (by decide)
        (by rw [a03, show reg n3 x0 = 0 from t3.zero]; decide)
      obtain ⟨n5, d5, u5⟩ := u4.aluImm hc3 ksn_at_b4 (off' := 0xB6) (by decide)
      obtain ⟨n6, d6, u6⟩ := u5.jump hc3 ksn_at_b6 (off' := 0x24) (by decide) (by rw [u5.pc]; decide)
      obtain ⟨m', c', pc', k', mm⟩ := e24s n3.mem n6 _ 0xE (pre3.trans (.cons d4 (.cons d5 (.single d6)))) u6 hR3
        (by rw [updz t3.zero (by decide), v3 19 (by decide)]; exact h19)
        (by rw [updz t3.zero (by decide)]; exact sp3)
        (by rw [updz t3.zero (by decide), v3 3 (by decide)]; exact h3)
        (by rw [updz t3.zero (by decide), v3 4 (by decide)]; exact h4)
        (by rw [updz t3.zero (by decide), v3 26 (by decide)]; exact h26)
        (by rw [updz t3.zero (by decide), v3 27 (by decide)]; exact h27)
        (by simp +decide only [upd, ite_true, ite_false]; rw [show reg n3 x0 = 0 from t3.zero]; rfl)
      refine ⟨m', c', pc', k', fun x hx => ?_⟩
      rw [mm x hx]
      show _ = (match (if pkOkAt m.mem q = true then (if ksDup m.mem q q k = true then some 0xD
        else ksOuter m.mem (q + 0x20) (k - 1) k) else some 0xE) with
        | none => memStore32 (memStore32 m.mem out keys) (out + 4) len
        | some c => memStore8 (memStore32 m.mem out 0) (out + 4) c) x
      rw [ite_eq_right hok]
    replace hok := Decidable.of_not_not hok
    rw [ite_eq_left hok] at a03
    have v318 : reg n3 18 = keys := (v3 18 (by decide)).trans h18
    have v319 : reg n3 19 = out := (v3 19 (by decide)).trans h19
    have v320 : reg n3 20 = len := (v3 20 (by decide)).trans h20
    have v321 : reg n3 21 = BitVec.ofNat 32 n := (v3 21 (by decide)).trans h21
    have v322 : reg n3 22 = BitVec.ofNat 32 i := (v3 22 (by decide)).trans h22
    have v323 : reg n3 23 = keys + len := (v3 23 (by decide)).trans h23
    have v324 : reg n3 24 = BitVec.ofNat 32 (32 * k) := (v3 24 (by decide)).trans h24
    have v325 : reg n3 25 = q := (v3 25 (by decide)).trans h25
    obtain ⟨n4, d4, u4⟩ := t3.notTaken hc3 0x76 ksn_at_74 (by decide)
      (by rw [a03, show reg n3 x0 = 0 from t3.zero]; decide)
    obtain ⟨n5, d5, u5⟩ := u4.notTaken hc3 0x7A ksn_at_76 (by decide)
      (by
        rw [v322, v321]
        show (!((BitVec.ofNat 32 i).ult (BitVec.ofNat 32 n))) = false
        rw [show (BitVec.ofNat 32 i).ult (BitVec.ofNat 32 n) = true from
          decide_eq_true (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)]; rfl)
    obtain ⟨n6, d6, u6⟩ := u5.aluImm hc3 ksn_at_7a (off' := 0x7E) (by decide)
    obtain ⟨n7, d7, u7⟩ := u6.alu hc3 ksn_at_7e (off' := 0x80) (by decide)
    obtain ⟨n8, d8, u8⟩ := u7.alu hc3 ksn_at_80 (off' := 0x82) (by decide)
    have g8 : ∀ r, r ≠ 8 → r ≠ 9 → reg n8 r = reg n3 r := fun r h8 h9 => by
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; rw [u8.self.zero, t3.zero]
      rw [u8.regs]; simp only [upd, hr, h8, h9, ↓reduceIte]
    have v88 : reg n8 8 = BitVec.ofNat 32 (32 * k) := by
      rw [u8.regs]; simp +decide only [upd, ite_true, ite_false]; rw [v324]; exact BitVec.zero_add _
    have v89 : reg n8 9 = q := by
      rw [u8.regs]; simp +decide only [upd, ite_true, ite_false]; rw [v322, v318]
      rw [show aluEval .sll (BitVec.ofNat 32 i) 5 = BitVec.ofNat 32 (32 * i) from BitVec.eq_of_toNat_eq (by
        rw [sll5_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)]
      show BitVec.ofNat 32 (32 * i) + keys = q
      rw [BitVec.add_comm, hq]
    have t8 : St n8.mem KSN n8 0x82 (reg n8) := by rw [u8.mem]; exact u8.self
    have hR8 : ∀ x, Sep S 0x940 x 1 → n8.mem x = M11 x := by rw [u8.mem]; exact hR3
    have stk : ∀ x, Sep S 0x940 x 1 → Sep (G + 0xFFFFFFFC) 4 x 1 := fun x hx => by
      rw [hG4S]; exact hx.sub (c := 0x93C) (l := 4) (by omega)
    obtain ⟨mx', cx, hMx, kx, hT, hF⟩ := ksn_inner (G := G) (q := q) (Mr := n8.mem)
      (codeX n8.mem hR8 (by decide) (by decide) hc) (codeX n8.mem hR8 (by decide) (by decide) ha)
      (codeX n8.mem hR8 (by decide) (by decide) hm) hGa hGw (by omega) (hq ▸ keyStk (32 * i) (by omega)) k n8 q
      (by omega) t8 (fun _ _ => rfl) (by rw [g8 sp (by decide) (by decide)]; exact sp3) v88 v89
      (by rw [g8 25 (by decide) (by decide)]; exact v325)
      (fun j hj => by rw [← hq, add_ofNat_assoc]; exact keyStk _ (by omega))
    have hR' : ∀ x, Sep S 0x940 x 1 → mx'.mem x = M11 x := fun x hx => (hMx x (stk x hx)).trans (hR8 x hx)
    have hcX := codeX mx'.mem hR' (by decide) (by decide) hc
    have hdupEq : ksDup n8.mem q q k = ksDup m.mem q q k :=
      ksDup_congr (mbEq0 n8.mem hR8 q hqS) k q (fun j hj => by
        rw [← hq, add_ofNat_assoc]; exact mbEq n8.mem hR8 keys len.toNat sK _ (by omega))
    have gx : ∀ r, r.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg mx' r = reg n3 r := fun r hr => by
      rw [kx r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)]
      exact g8 r (by revert r; decide) (by revert r; decide)
    have spx : reg mx' sp = G := by
      rw [kx sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        g8 sp (by decide) (by decide)]; exact sp3
    have pre8 : Steps mx n8 := pre3.trans (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.single d8)))))
    rcases hd : ksDup m.mem q q k with _ | _
    · have t9 := hF (hdupEq ▸ hd)
      obtain ⟨n10, d10, u10⟩ := t9.aluImm hcX ksn_at_9a (off' := 0x9E) (by decide)
      obtain ⟨n11, d11, u11⟩ := u10.aluImm hcX ksn_at_9e (off' := 0xA0) (by decide)
      obtain ⟨n12, d12, u12⟩ := u11.aluImm hcX ksn_at_a0 (off' := 0xA2) (by decide)
      have g12 : ∀ r, r ≠ 22 → r ≠ 24 → r ≠ 25 → reg n12 r = reg mx' r := fun r h1 h2 h3' => by
        by_cases hr : r.val = 0
        · have : r = 0 := Fin.ext hr
          subst this; rw [u12.self.zero, t9.zero]
        rw [u12.regs]; simp only [upd, hr, h1, h2, h3', ↓reduceIte]
      have v1225 : reg n12 25 = q + 0x20 := by
        rw [u12.regs]; simp +decide only [upd, ite_true, ite_false]; rw [gx 25 (by decide), v325]; rfl
      have v1222 : reg n12 22 = BitVec.ofNat 32 (i + 1) := by
        rw [u12.regs]; simp +decide only [upd, ite_true, ite_false]; rw [gx 22 (by decide), v322]
        apply BitVec.eq_of_toNat_eq
        show (BitVec.ofNat 32 i + 1).toNat = (BitVec.ofNat 32 (i + 1)).toNat
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]; omega
      have v1224 : reg n12 24 = BitVec.ofNat 32 (32 * k) + 0xFFFFFFE0 := by
        rw [u12.regs]; simp +decide only [upd, ite_true, ite_false]; rw [gx 24 (by decide), v324]; rfl
      have v1223 : reg n12 23 = keys + len := by rw [g12 23 (by decide) (by decide) (by decide), gx 23 (by decide)]; exact v323
      have hq20 : q + 0x20 = keys + BitVec.ofNat 32 (32 * (i + 1)) := by
        rw [← hq, show (0x20 : Word) = BitVec.ofNat 32 32 from rfl, add_ofNat_assoc, show 32 * i + 32 = 32 * (i + 1) by omega]
      have pre12 : Steps mx n12 := pre8.trans (cx.trans (.cons d10 (.cons d11 (.single d12))))
      cases k with
      | zero =>
        have hend : q + 0x20 = keys + len := by
          rw [hq20]; apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_add]; omega
        obtain ⟨n13, d13, u13⟩ := u12.self.notTaken hcX 0xA6 ksn_at_a2 (by decide)
          (by
            rw [v1225, v1223, hend]
            show (!(keys + len == keys + len)) = false
            rw [show (keys + len == keys + len) = true from bt_beq_self _]; rfl)
        have v1219 : reg n12 19 = out := by rw [g12 19 (by decide) (by decide) (by decide), gx 19 (by decide)]; exact v319
        have v1218 : reg n12 18 = keys := by rw [g12 18 (by decide) (by decide) (by decide), gx 18 (by decide)]; exact v318
        have v1220 : reg n12 20 = len := by rw [g12 20 (by decide) (by decide) (by decide), gx 20 (by decide)]; exact v320
        obtain ⟨n14, d14, u14⟩ := u13.sw hcX ksn_at_a6 (off' := 0xAA) (by decide)
          (by rw [v1219, show out + (0x0 : Word) = out from BitVec.add_zero out]; exact hout)
        rw [v1219, show out + (0x0 : Word) = out from BitVec.add_zero out, v1218] at u14
        have hc14 := hcX.store32 (v := keys) (a := out)
          (by have := sOc.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this)
        obtain ⟨n15, d15, u15⟩ := u14.sw hc14 ksn_at_aa (off' := 0xAE) (by decide)
          (by rw [v1219]; exact aligned_add hout (k := 4) (by decide))
        rw [v1219, v1220] at u15
        have hc15 := hc14.store32 (v := len) (a := out + 0x4) (sOc.sub (c := 4) (l := 4) (by omega))
        obtain ⟨n16, d16, u16⟩ := u15.jump hc15 ksn_at_ae (off' := 0x2C) (by decide) (by rw [u15.pc]; decide)
        have spx12 : reg n12 sp = G := by rw [g12 sp (by decide) (by decide) (by decide)]; exact spx
        obtain ⟨m', c', pc', kp, mm⟩ := epi _ _ u16.self hc15 (by rw [u16.regs]; exact spx12)
          (fun c h1 h2 => by
            rw [← frameOk mx'.mem hR' c h1 h2]
            exact (memLoad32_store32_sep (by
              rw [hGS, add_ofNat_assoc]; exact (hO4.subR (c := 0x940 + c) (l := 4) (by omega)) |> fun h => by
                exact ((sO.sub (c := 4) (l := 4) (by omega)).subR (c := 0x940 + c) (l := 4) (by omega)))).trans
              (memLoad32_store32_sep (by rw [hGS, add_ofNat_assoc]; exact hO4.subR (c := 0x940 + c) (l := 4) (by omega))))
          (by rw [u16.regs, g12 3 (by decide) (by decide) (by decide), gx 3 (by decide), v3 3 (by decide)]; exact h3)
          (by rw [u16.regs, g12 4 (by decide) (by decide) (by decide), gx 4 (by decide), v3 4 (by decide)]; exact h4)
          (by rw [u16.regs, g12 26 (by decide) (by decide) (by decide), gx 26 (by decide), v3 26 (by decide)]; exact h26)
          (by rw [u16.regs, g12 27 (by decide) (by decide) (by decide), gx 27 (by decide), v3 27 (by decide)]; exact h27)
        refine ⟨m', pre12.trans (.cons d13 (.cons d14 (.cons d15 (.cons d16 c')))), pc', kp, fun x hx => ?_⟩
        rw [mm]
        show _ = (match (if pkOkAt m.mem q = true then (if ksDup m.mem q q 0 = true then some 0xD
          else ksOuter m.mem (q + 0x20) (0 - 1) 0) else some 0xE) with
          | none => memStore32 (memStore32 m.mem out keys) (out + 4) len
          | some c => memStore8 (memStore32 m.mem out 0) (out + 4) c) x
        rw [ite_eq_left hok]
        exact memStore32_congr (memStore32_congr (fin mx'.mem hR' x hx))
      | succ k' =>
        have hne : q + 0x20 ≠ keys + len := fun h => by
          rw [hq20] at h; have := congrArg BitVec.toNat h
          rw [hkey _ (by omega), BitVec.toNat_add] at this; omega
        obtain ⟨n13, d13, u13⟩ := u12.self.taken hcX 0x6A ksn_at_a2 (by decide)
          (by rw [v1225, v1223]; exact bne_iff_ne.mpr hne)
        have t13 : St n13.mem KSN n13 0x6A (reg n13) := by rw [u13.mem]; exact u13.self
        have r13 : ∀ r, reg n13 r = reg n12 r := u13.regs
        obtain ⟨m', c', pc', kp, mm⟩ := hP (by omega) n13 (i + 1) (by omega) t13
          (by rw [u13.mem]; exact hR') (by rw [r13, g12 sp (by decide) (by decide) (by decide)]; exact spx)
          (by rw [r13, g12 18 (by decide) (by decide) (by decide), gx 18 (by decide)]; exact v318)
          (by rw [r13, g12 19 (by decide) (by decide) (by decide), gx 19 (by decide)]; exact v319)
          (by rw [r13, g12 20 (by decide) (by decide) (by decide), gx 20 (by decide)]; exact v320)
          (by rw [r13, g12 21 (by decide) (by decide) (by decide), gx 21 (by decide)]; exact v321)
          (by rw [r13]; exact v1222) (by rw [r13]; exact v1223)
          (by
            rw [r13, v1224]; apply BitVec.eq_of_toNat_eq
            show (BitVec.ofNat 32 (32 * (k' + 1)) + 0xFFFFFFE0).toNat = (BitVec.ofNat 32 (32 * (k' + 1 - 1))).toNat
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              show (0xFFFFFFE0 : Word).toNat = 4294967264 from rfl]; omega)
          (by rw [r13, v1225, hq20])
          (by rw [r13, g12 3 (by decide) (by decide) (by decide), gx 3 (by decide), v3 3 (by decide)]; exact h3)
          (by rw [r13, g12 4 (by decide) (by decide) (by decide), gx 4 (by decide), v3 4 (by decide)]; exact h4)
          (by rw [r13, g12 26 (by decide) (by decide) (by decide), gx 26 (by decide), v3 26 (by decide)]; exact h26)
          (by rw [r13, g12 27 (by decide) (by decide) (by decide), gx 27 (by decide), v3 27 (by decide)]; exact h27)
        refine ⟨m', pre12.trans (.cons d13 c'), pc', kp, fun x hx => ?_⟩
        rw [mm x hx]
        show (match ksOuter m.mem (keys + BitVec.ofNat 32 (32 * (i + 1))) (k' + 1 - 1) (k' + 1 - 1 + 1) with
          | none => memStore32 (memStore32 m.mem out keys) (out + 4) len
          | some c => memStore8 (memStore32 m.mem out 0) (out + 4) c) x =
          (match (if pkOkAt m.mem q = true then (if ksDup m.mem q q (k' + 1) = true then some 0xD
            else ksOuter m.mem (q + 0x20) (k' + 1 - 1) (k' + 1)) else some 0xE) with
          | none => memStore32 (memStore32 m.mem out keys) (out + 4) len
          | some c => memStore8 (memStore32 m.mem out 0) (out + 4) c) x
        rw [ite_eq_left hok, hd, hq20]; rfl
    · have t9 := hT (hdupEq ▸ hd)
      obtain ⟨n10, d10, u10⟩ := t9.aluImm hcX ksn_at_b0 (off' := 0xB2) (by decide)
      obtain ⟨n11, d11, u11⟩ := u10.jump hcX ksn_at_b2 (off' := 0x24) (by decide) (by rw [u10.pc]; decide)
      obtain ⟨m', c', pc', k', mm⟩ := e24s mx'.mem n11 _ 0xD (pre8.trans (cx.trans (.cons d10 (.single d11)))) u11 hR'
        (by rw [updz t9.zero (by decide), gx 19 (by decide)]; exact v319)
        (by rw [updz t9.zero (by decide)]; exact spx)
        (by rw [updz t9.zero (by decide), gx 3 (by decide), v3 3 (by decide)]; exact h3)
        (by rw [updz t9.zero (by decide), gx 4 (by decide), v3 4 (by decide)]; exact h4)
        (by rw [updz t9.zero (by decide), gx 26 (by decide), v3 26 (by decide)]; exact h26)
        (by rw [updz t9.zero (by decide), gx 27 (by decide), v3 27 (by decide)]; exact h27)
        (by simp +decide only [upd, ite_true, ite_false]; rw [show reg mx' x0 = 0 from t9.zero]; rfl)
      refine ⟨m', c', pc', k', fun x hx => ?_⟩
      rw [mm x hx]
      show _ = (match (if pkOkAt m.mem q = true then (if ksDup m.mem q q k = true then some 0xD
        else ksOuter m.mem (q + 0x20) (k - 1) k) else some 0xE) with
        | none => memStore32 (memStore32 m.mem out keys) (out + 4) len
        | some c => memStore8 (memStore32 m.mem out 0) (out + 4) c) x
      rw [ite_eq_left hok, ite_eq_left hd]
  have outer : ∀ k, P k := by
    intro k
    induction k with
    | zero => exact step 0 fun h => absurd h (by omega)
    | succ k ih => exact step (k + 1) fun _ => ih
  obtain ⟨m27, e27, t27⟩ := t26.self.notTaken hc12 0x6A ksn_at_66 (by decide)
    (by
      rw [g26 18 (by decide) (by decide) (by decide) (by decide) (by decide), w18, v2623]
      refine beq_eq_false_iff_ne.mpr fun h => ?_
      have := congrArg BitVec.toNat h; rw [BitVec.toNat_add] at this; omega)
  have t27' : St m27.mem KSN m27 0x6A (reg m27) := by rw [t27.mem]; exact t27.self
  have k27 : ∀ r, reg m27 r = reg m26 r := t27.regs
  have g18 : ∀ r, r ≠ a0 → r ≠ 20 → r ≠ 21 → r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → reg m27 r = reg m15 r :=
    fun r h0 h20 h1 h2 h3 h4 h5 => by rw [k27, g26 r h1 h2 h3 h4 h5, q18 r h0 h20]
  obtain ⟨m', c', pc', kk, mm⟩ := outer (n - 1) m27 0 (by omega) t27'
    (fun x _ => by rw [t27.mem]) (by rw [g18 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v15sp)
    (by rw [g18 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v1518)
    (by rw [g18 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v1519)
    (by rw [k27, g26 20 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v1820)
    (by rw [k27]; exact v2621) (by rw [k27]; exact v2622) (by rw [k27]; exact v2623)
    (by rw [k27]; exact v2624) (by rw [k27]; exact v2625)
    (by rw [g18 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v153)
    (by rw [g18 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v154)
    (by rw [g18 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v1526)
    (by rw [g18 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact v1527)
  refine ⟨m', pre18.trans (.cons e19 (.cons e20 (.cons e21 (.cons e22 (.cons e23 (.cons e24 (.cons e25 (.cons e26
    (.cons e27 c'))))))))), pc', kk, fun x hx => ?_⟩
  rw [mm x hx]; unfold keySetMem; rw [ite_eq_left ⟨hm32, hle, h32⟩, hnd, add_ofNat_zero,
    show n - 1 + 1 = n by omega]

end C3.RV32
