import C3BootProofs.Proofs.P384Sub

/-!
# Field arithmetic modulo 2^255 - 19: specifications and word facts

`curve25519_dalek`'s 32-bit backend keeps a field element in ten limbs of
alternately 26 and 25 bits (`FieldElement2625`), and its multiplication and
squaring produce ten `u64` sums that `reduce` carries back into limbs.
`feReduceSpec` is `reduce` as the Rust source writes it, on naturals: each
`+=` on a `u64` wraps modulo 2^64.

The lemmas below give each instruction's result as a natural-number fact, so
that `omega` can check one Rust operation at a time against the
instructions that compute it.
-/

namespace C3.RV32

/-- The `u64` at limb `i` of an array at `b`, as two little-endian words. -/
def u64At (M : Word → BitVec 8) (b : Word) (i : Nat) : Nat :=
  (memLoad32 M (b + BitVec.ofNat 32 (8 * i))).toNat + 2 ^ 32 * (memLoad32 M (b + BitVec.ofNat 32 (8 * i + 4))).toNat

/-- `FieldElement2625::reduce`, in the Rust source's order: carry each limb
into the next (26 bits for even limbs, 25 for odd ones), fold the top carry
back into limb 0 times 19, carry limb 0 once more, and keep each limb's low
32 bits. -/
def feReduceSpec (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 : Nat) : List Nat :=
  let z1 := (z1 + z0 / 2 ^ 26) % 2 ^ 64
  let z0 := z0 % 2 ^ 26
  let z5 := (z5 + z4 / 2 ^ 26) % 2 ^ 64
  let z4 := z4 % 2 ^ 26
  let z2 := (z2 + z1 / 2 ^ 25) % 2 ^ 64
  let z1 := z1 % 2 ^ 25
  let z6 := (z6 + z5 / 2 ^ 25) % 2 ^ 64
  let z5 := z5 % 2 ^ 25
  let z3 := (z3 + z2 / 2 ^ 26) % 2 ^ 64
  let z2 := z2 % 2 ^ 26
  let z7 := (z7 + z6 / 2 ^ 26) % 2 ^ 64
  let z6 := z6 % 2 ^ 26
  let z4 := (z4 + z3 / 2 ^ 25) % 2 ^ 64
  let z3 := z3 % 2 ^ 25
  let z8 := (z8 + z7 / 2 ^ 25) % 2 ^ 64
  let z7 := z7 % 2 ^ 25
  let z5 := (z5 + z4 / 2 ^ 26) % 2 ^ 64
  let z4 := z4 % 2 ^ 26
  let z9 := (z9 + z8 / 2 ^ 26) % 2 ^ 64
  let z8 := z8 % 2 ^ 26
  let z0 := (z0 + 19 * (z9 / 2 ^ 25) % 2 ^ 64) % 2 ^ 64
  let z9 := z9 % 2 ^ 25
  let z1 := (z1 + z0 / 2 ^ 26) % 2 ^ 64
  let z0 := z0 % 2 ^ 26
  [z0 % 2 ^ 32, z1 % 2 ^ 32, z2 % 2 ^ 32, z3 % 2 ^ 32, z4 % 2 ^ 32, z5 % 2 ^ 32, z6 % 2 ^ 32, z7 % 2 ^ 32,
    z8 % 2 ^ 32, z9 % 2 ^ 32]

/-- The ten `u64` sums of `<&FieldElement2625 as Mul>::mul`, in the Rust source's
order: `y[j]` times 19 and odd `x[i]` doubled as `u32`s (each wraps modulo
2^32), each product of two `u32`s as a `u64`, and each sum modulo 2^64. -/
def feMulZ (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Nat) : List Nat :=
  let y1_19 := 19 * y1 % 2 ^ 32
  let y2_19 := 19 * y2 % 2 ^ 32
  let y3_19 := 19 * y3 % 2 ^ 32
  let y4_19 := 19 * y4 % 2 ^ 32
  let y5_19 := 19 * y5 % 2 ^ 32
  let y6_19 := 19 * y6 % 2 ^ 32
  let y7_19 := 19 * y7 % 2 ^ 32
  let y8_19 := 19 * y8 % 2 ^ 32
  let y9_19 := 19 * y9 % 2 ^ 32
  let x1_2 := 2 * x1 % 2 ^ 32
  let x3_2 := 2 * x3 % 2 ^ 32
  let x5_2 := 2 * x5 % 2 ^ 32
  let x7_2 := 2 * x7 % 2 ^ 32
  let x9_2 := 2 * x9 % 2 ^ 32
  [(x0 * y0 + x1_2 * y9_19 + x2 * y8_19 + x3_2 * y7_19 + x4 * y6_19 + x5_2 * y5_19 + x6 * y4_19 + x7_2 * y3_19 + x8 * y2_19 + x9_2 * y1_19) % 2 ^ 64,
    (x0 * y1 + x1 * y0 + x2 * y9_19 + x3 * y8_19 + x4 * y7_19 + x5 * y6_19 + x6 * y5_19 + x7 * y4_19 + x8 * y3_19 + x9 * y2_19) % 2 ^ 64,
    (x0 * y2 + x1_2 * y1 + x2 * y0 + x3_2 * y9_19 + x4 * y8_19 + x5_2 * y7_19 + x6 * y6_19 + x7_2 * y5_19 + x8 * y4_19 + x9_2 * y3_19) % 2 ^ 64,
    (x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0 + x4 * y9_19 + x5 * y8_19 + x6 * y7_19 + x7 * y6_19 + x8 * y5_19 + x9 * y4_19) % 2 ^ 64,
    (x0 * y4 + x1_2 * y3 + x2 * y2 + x3_2 * y1 + x4 * y0 + x5_2 * y9_19 + x6 * y8_19 + x7_2 * y7_19 + x8 * y6_19 + x9_2 * y5_19) % 2 ^ 64,
    (x0 * y5 + x1 * y4 + x2 * y3 + x3 * y2 + x4 * y1 + x5 * y0 + x6 * y9_19 + x7 * y8_19 + x8 * y7_19 + x9 * y6_19) % 2 ^ 64,
    (x0 * y6 + x1_2 * y5 + x2 * y4 + x3_2 * y3 + x4 * y2 + x5_2 * y1 + x6 * y0 + x7_2 * y9_19 + x8 * y8_19 + x9_2 * y7_19) % 2 ^ 64,
    (x0 * y7 + x1 * y6 + x2 * y5 + x3 * y4 + x4 * y3 + x5 * y2 + x6 * y1 + x7 * y0 + x8 * y9_19 + x9 * y8_19) % 2 ^ 64,
    (x0 * y8 + x1_2 * y7 + x2 * y6 + x3_2 * y5 + x4 * y4 + x5_2 * y3 + x6 * y2 + x7_2 * y1 + x8 * y0 + x9_2 * y9_19) % 2 ^ 64,
    (x0 * y9 + x1 * y8 + x2 * y7 + x3 * y6 + x4 * y5 + x5 * y4 + x6 * y3 + x7 * y2 + x8 * y1 + x9 * y0) % 2 ^ 64]

/-- `<&FieldElement2625 as Mul>::mul`: the ten sums, then `reduce`. -/
def feMulSpec (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Nat) : List Nat :=
  let z := feMulZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9
  feReduceSpec z[0]! z[1]! z[2]! z[3]! z[4]! z[5]! z[6]! z[7]! z[8]! z[9]!

/-- The ten `u64` sums of `FieldElement2625::square_inner`, in the Rust
source's order: `x[i]` doubled and times 19 as `u32`s (each wraps modulo
2^32), each product of two `u32`s as a `u64`, the `(...) * 2` groups, and
each sum modulo 2^64. -/
def feSqZ (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat) : List Nat :=
  let x0_2 := 2 * x0 % 2 ^ 32
  let x1_2 := 2 * x1 % 2 ^ 32
  let x2_2 := 2 * x2 % 2 ^ 32
  let x3_2 := 2 * x3 % 2 ^ 32
  let x4_2 := 2 * x4 % 2 ^ 32
  let x5_2 := 2 * x5 % 2 ^ 32
  let x6_2 := 2 * x6 % 2 ^ 32
  let x7_2 := 2 * x7 % 2 ^ 32
  let x5_19 := 19 * x5 % 2 ^ 32
  let x6_19 := 19 * x6 % 2 ^ 32
  let x7_19 := 19 * x7 % 2 ^ 32
  let x8_19 := 19 * x8 % 2 ^ 32
  let x9_19 := 19 * x9 % 2 ^ 32
  [(x0 * x0 + x2_2 * x8_19 + x4_2 * x6_19 + (x1_2 * x9_19 + x3_2 * x7_19 + x5 * x5_19) * 2) % 2 ^ 64,
    (x0_2 * x1 + x3_2 * x8_19 + x5_2 * x6_19 + (x2 * x9_19 + x4 * x7_19) * 2) % 2 ^ 64,
    (x0_2 * x2 + x1_2 * x1 + x4_2 * x8_19 + x6 * x6_19 + (x3_2 * x9_19 + x5_2 * x7_19) * 2) % 2 ^ 64,
    (x0_2 * x3 + x1_2 * x2 + x5_2 * x8_19 + (x4 * x9_19 + x6 * x7_19) * 2) % 2 ^ 64,
    (x0_2 * x4 + x1_2 * x3_2 + x2 * x2 + x6_2 * x8_19 + (x5_2 * x9_19 + x7 * x7_19) * 2) % 2 ^ 64,
    (x0_2 * x5 + x1_2 * x4 + x2_2 * x3 + x7_2 * x8_19 + x6 * x9_19 * 2) % 2 ^ 64,
    (x0_2 * x6 + x1_2 * x5_2 + x2_2 * x4 + x3_2 * x3 + x8 * x8_19 + x7_2 * x9_19 * 2) % 2 ^ 64,
    (x0_2 * x7 + x1_2 * x6 + x2_2 * x5 + x3_2 * x4 + x8 * x9_19 * 2) % 2 ^ 64,
    (x0_2 * x8 + x1_2 * x7_2 + x2_2 * x6 + x3_2 * x5_2 + x4 * x4 + x9 * x9_19 * 2) % 2 ^ 64,
    (x0_2 * x9 + x1_2 * x8 + x2_2 * x7 + x3_2 * x6 + x4_2 * x5) % 2 ^ 64]

/-- The `u32` at limb `i` of an array at `b`. -/
def limbAt (M : Word → BitVec 8) (b : Word) (i : Nat) : Nat := (memLoad32 M (b + BitVec.ofNat 32 (4 * i))).toNat

section Step

variable {M : Word → BitVec 8} {base : Word} {m : Machine} {off : Nat} {f : Fin 32 → Word}
  {code : List Nat}

theorem St.luiG (s : St M base m off f) (hc : CodeIn M base code) {rd : Fin 32}
    {imm len : Word} {off' : Nat} (hf : fetchRel code off = some (.lui rd imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') :
    ∃ m1 v, step m = some m1 ∧ imm = v ∧ St M base m1 off' (upd f rd v) :=
  let ⟨m1, h1, h2⟩ := s.lui hc hf hn
  ⟨m1, _, h1, rfl, h2⟩

theorem St.swG (s : St M base m off f) (hc : CodeIn M base code) {rs1 rs2 : Fin 32} {o len : Word}
    {off' : Nat} (hf : fetchRel code off = some (.store .sw rs1 rs2 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (hal : (f rs1 + o).toNat % 4 = 0) {a v : Word}
    (ha : f rs1 + o = a) (hv : f rs2 = v) :
    ∃ m1, step m = some m1 ∧ St (memStore32 M a v) base m1 off' f := by
  subst ha hv; exact s.sw hc hf hn hal

theorem St.lwE (s : St M base m off f) (hc : CodeIn M base code) {rd rs1 : Fin 32} {o len : Word}
    {off' : Nat} (hf : fetchRel code off = some (.load .lw rd rs1 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (hal : (f rs1 + o).toNat % 4 = 0) {v : Word}
    (hv : memLoad32 M (f rs1 + o) = v) :
    ∃ m1, step m = some m1 ∧ St M base m1 off' (upd f rd v) := by
  subst hv; exact s.lw hc hf hn hal

theorem St.aluE (s : St M base m off f) (hc : CodeIn M base code) {op : AluOp} {rd rs1 rs2 : Fin 32}
    {len : Word} {off' : Nat} (hf : fetchRel code off = some (.alu op rd rs1 rs2, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') {v : Word} (hv : aluEval op (f rs1) (f rs2) = v) :
    ∃ m1, step m = some m1 ∧ St M base m1 off' (upd f rd v) := by
  subst hv; exact s.alu hc hf hn

end Step

theorem tn_srl {a v : Word} {k : Word} (h : aluEval .srl a k = v) : v.toNat = a.toNat / 2 ^ (k.toNat % 32) := by
  rw [← h]; show (a >>> (k.toNat % 32)).toNat = _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem tn_sll {a v : Word} {k : Word} (h : aluEval .sll a k = v) :
    v.toNat = a.toNat * 2 ^ (k.toNat % 32) % 2 ^ 32 := by
  rw [← h]; show (a <<< (k.toNat % 32)).toNat = _
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem tn_mul {a b v : Word} (h : aluEval .mul a b = v) : v.toNat = a.toNat * b.toNat % 2 ^ 32 := by
  rw [← h]; exact BitVec.toNat_mul a b

theorem tn_mulhu {a b v : Word} (h : aluEval .mulhu a b = v) : v.toNat = a.toNat * b.toNat / 2 ^ 32 := by
  rw [← h]; show (BitVec.ofNat 32 (a.toNat * b.toNat / 2 ^ 32)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have ha := a.isLt; have hb := b.isLt
  have hp : a.toNat * b.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- `or` of two words whose set bits don't overlap: one below bit `j`, the
other a multiple of `2^j`. -/
theorem tn_or {x y v : Word} {j : Nat} (h : aluEval .or x y = v) (hx : x.toNat < 2 ^ j)
    (hy : y.toNat % 2 ^ j = 0) : v.toNat = x.toNat + y.toNat := by
  rw [← h]; show (x ||| y).toNat = _
  have e : y.toNat = 2 ^ j * (y.toNat / 2 ^ j) := by
    have := Nat.div_add_mod y.toNat (2 ^ j); omega
  rw [BitVec.toNat_or, Nat.or_comm, e, ← Nat.two_pow_add_eq_or_of_lt hx, Nat.add_comm]

theorem tn_or' {x y v : Word} {j : Nat} (h : aluEval .or y x = v) (hx : x.toNat < 2 ^ j)
    (hy : y.toNat % 2 ^ j = 0) : v.toNat = x.toNat + y.toNat := by
  rw [← h]; show (y ||| x).toNat = _
  rw [BitVec.or_comm]; exact tn_or rfl hx hy

/-- The `or` that joins a `u64`'s two words shifted right by `k`: the low
word shifted right by `k` and the high word shifted left by `32 - k`. -/
theorem tn_orS {a b x y v : Word} (k : Nat) (hk : 0 < k ∧ k < 32) (h : aluEval .or x y = v)
    (hx : x.toNat = a.toNat / 2 ^ k) (hy : y.toNat = b.toNat * 2 ^ (32 - k) % 2 ^ 32) :
    v.toNat = x.toNat + y.toNat := by
  have ha := a.isLt
  have hp : 2 ^ k * 2 ^ (32 - k) = 2 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
  refine tn_or (j := 32 - k) h ?_ ?_
  · rw [hx]
    have h1 : a.toNat / 2 ^ k < 2 ^ (32 - k) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), Nat.mul_comm, hp]; exact ha
    exact h1
  · rw [hy]
    have e : b.toNat * 2 ^ (32 - k) % 2 ^ 32 = b.toNat % 2 ^ k * 2 ^ (32 - k) := by
      rw [← hp, Nat.mul_comm (2 ^ k), ← Nat.mul_mod_mul_right, Nat.mul_comm (2 ^ (32 - k))]
    rw [e, Nat.mul_mod_left]

theorem tn_orS' {a b x y v : Word} (k : Nat) (hk : 0 < k ∧ k < 32) (h : aluEval .or y x = v)
    (hx : x.toNat = a.toNat / 2 ^ k) (hy : y.toNat = b.toNat * 2 ^ (32 - k) % 2 ^ 32) :
    v.toNat = x.toNat + y.toNat := by
  rw [← h]; show (y ||| x).toNat = _
  rw [BitVec.or_comm]; exact tn_orS k hk rfl hx hy

theorem and_low {a m : Word} {k : Nat} (hk : k ≤ 32)
    (hm : ∀ i : Fin 32, m.getLsbD i.val = decide (i.val < k)) : (a &&& m).toNat = a.toNat % 2 ^ k := by
  have h : a &&& m = BitVec.ofNat 32 (a.toNat % 2 ^ k) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_mod_two_pow, hm ⟨i, hi⟩]
    simp only [BitVec.getLsbD, hi, decide_true, Bool.true_and]
    exact Bool.and_comm _ _
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := Nat.mod_lt a.toNat (Nat.two_pow_pos k)
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) hk
  omega

theorem tn_and26 {a m v : Word} (h : aluEval .and a m = v) (hm : m = 0x3FFFFFF) : v.toNat = a.toNat % 2 ^ 26 := by
  rw [← h, hm]; exact and_low (by decide) (by decide)

theorem tn_and25 {a m v : Word} (h : aluEval .and a m = v) (hm : m = 0x1FFFFFF) : v.toNat = a.toNat % 2 ^ 25 := by
  rw [← h, hm]; exact and_low (by decide) (by decide)

theorem tn_and26' {a m v : Word} (h : aluEval .and m a = v) (hm : m = 0x3FFFFFF) : v.toNat = a.toNat % 2 ^ 26 := by
  rw [← h, hm]; show (0x3FFFFFF &&& a).toNat = _
  rw [BitVec.and_comm]; exact and_low (by decide) (by decide)

theorem tn_and25' {a m v : Word} (h : aluEval .and m a = v) (hm : m = 0x1FFFFFF) : v.toNat = a.toNat % 2 ^ 25 := by
  rw [← h, hm]; show (0x1FFFFFF &&& a).toNat = _
  rw [BitVec.and_comm]; exact and_low (by decide) (by decide)

theorem small_mod {X Y k : Nat} (hk : k ≤ 32) (e : Y % 2 ^ k = X) : X % 2 ^ 32 = X := by
  rw [← e]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos k))
    (Nat.pow_le_pow_right (by decide) hk))

/-- A value modulo `m`, as an equation with an unnamed quotient: `omega`
handles a chain of these much faster than the remainders. -/
theorem mod_q {v x m : Nat} (h : v = x % m) : ∃ q, v + m * q = x := ⟨x / m, by rw [h]; exact Nat.mod_add_div x m⟩

theorem mod64_of {lo hi : Word} {Q S : Nat} (h : lo.toNat + 2 ^ 32 * hi.toNat + 2 ^ 64 * Q = S) :
    lo.toNat + 2 ^ 32 * hi.toNat = S % 2 ^ 64 := by
  have := lo.isLt; have := hi.isLt
  omega

theorem tn_const {v c : Word} (h : c = v) : v.toNat = c.toNat := by rw [h]

end C3.RV32
