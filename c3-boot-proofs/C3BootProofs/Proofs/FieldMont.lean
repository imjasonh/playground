import C3BootProofs.Proofs.FieldWideMulMain

/-!
# The Montgomery reduction in `FieldElement::multiply`: arithmetic

`p256`'s `montgomery_reduce` adds `m · p · 2^(32 i)` to the 512-bit product
for each limb `i`, with `m` the limb's current value. The compiled code does
each of its `carrying_add` and `carrying_mul_add` steps with a few `add`,
`sltu`, `sub`, and `mulhu` instructions; the lemmas here give each group's
carry equation, and `mont_round` sums one round's six.
-/

namespace C3.RV32

section Step

variable {M : Word → BitVec 8} {base : Word} {m : Machine} {off : Nat} {f : Fin 32 → Word}
  {code : List Nat}

theorem St.aluG (s : St M base m off f) (hc : CodeIn M base code) {op : AluOp} {rd rs1 rs2 : Fin 32}
    {len : Word} {off' : Nat} (hf : fetchRel code off = some (.alu op rd rs1 rs2, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') :
    ∃ m1 v, step m = some m1 ∧ aluEval op (f rs1) (f rs2) = v ∧ St M base m1 off' (upd f rd v) :=
  let ⟨m1, h1, h2⟩ := s.alu hc hf hn
  ⟨m1, _, h1, rfl, h2⟩

theorem St.aluImmG (s : St M base m off f) (hc : CodeIn M base code) {op : AluOp} {rd rs1 : Fin 32}
    {imm len : Word} {off' : Nat} (hf : fetchRel code off = some (.aluImm op rd rs1 imm, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') :
    ∃ m1 v, step m = some m1 ∧ aluEval op (f rs1) imm = v ∧ St M base m1 off' (upd f rd v) :=
  let ⟨m1, h1, h2⟩ := s.aluImm hc hf hn
  ⟨m1, _, h1, rfl, h2⟩

theorem St.lwG (s : St M base m off f) (hc : CodeIn M base code) {rd rs1 : Fin 32} {o len : Word}
    {off' : Nat} (hf : fetchRel code off = some (.load .lw rd rs1 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (hal : (f rs1 + o).toNat % 4 = 0) :
    ∃ m1 v, step m = some m1 ∧ memLoad32 M (f rs1 + o) = v ∧ St M base m1 off' (upd f rd v) :=
  let ⟨m1, h1, h2⟩ := s.lw hc hf hn hal
  ⟨m1, _, h1, rfl, h2⟩

end Step

theorem tn_add {a b r : Word} (h : aluEval .add a b = r) : r.toNat = (a.toNat + b.toNat) % 2 ^ 32 := by
  rw [← h]; exact BitVec.toNat_add a b

theorem tn_sub {a b r : Word} (h : aluEval .sub a b = r) :
    r.toNat = (2 ^ 32 - b.toNat + a.toNat) % 2 ^ 32 := by
  rw [← h]; exact BitVec.toNat_sub a b

theorem tn_sltu {a b r : Word} (h : aluEval .sltu a b = r) :
    (a.toNat < b.toNat ∧ r.toNat = 1) ∨ (b.toNat ≤ a.toNat ∧ r.toNat = 0) := by
  rw [← h]
  show (a.toNat < b.toNat ∧ (if a.ult b then 1 else 0 : Word).toNat = 1) ∨
    (b.toNat ≤ a.toNat ∧ (if a.ult b then 1 else 0 : Word).toNat = 0)
  by_cases hl : a.toNat < b.toNat
  · refine .inl ⟨hl, ?_⟩
    rw [ite_eq_left (by simp only [BitVec.ult]; exact decide_eq_true hl)]; rfl
  · refine .inr ⟨by omega, ?_⟩
    rw [ite_eq_right (by simp only [BitVec.ult]; exact fun e => hl (of_decide_eq_true e))]; rfl

theorem tn_mulhuM1 {a r : Word} (h : aluEval .mulhu a 0xFFFFFFFF = r) :
    (a.toNat = 0 ∧ r.toNat = 0) ∨ (0 < a.toNat ∧ r.toNat + 1 = a.toNat) := by
  rw [← h]
  show (a.toNat = 0 ∧ (BitVec.ofNat 32 ((a.toNat * 4294967295) / 2 ^ 32)).toNat = 0) ∨
    (0 < a.toNat ∧ (BitVec.ofNat 32 ((a.toNat * 4294967295) / 2 ^ 32)).toNat + 1 = a.toNat)
  have ha := a.isLt
  rw [BitVec.toNat_ofNat, show (2 : Nat) ^ 32 = 4294967296 from rfl] at *
  by_cases h0 : a.toNat = 0
  · exact .inl ⟨h0, by rw [h0]⟩
  · have hq : a.toNat * 4294967295 / 4294967296 = a.toNat - 1 := by omega
    rw [hq, Nat.mod_eq_of_lt (by omega)]
    exact .inr ⟨by omega, by omega⟩

/-- `x + y` and its carry, as `add` then `sltu` against either addend. -/
theorem fmP1 {a b y c : Word} (hy : aluEval .add a b = y) (hc : aluEval .sltu y a = c ∨ aluEval .sltu y b = c) :
    y.toNat + 2 ^ 32 * c.toNat = a.toNat + b.toNat := by
  have ey := tn_add hy
  have := a.isLt; have := b.isLt
  rcases hc with hc | hc <;> rcases tn_sltu hc with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

theorem fmP1s {a b y c : Word} (hy : aluEval .add a b = y) (hc : aluEval .sltu y a = c ∨ aluEval .sltu y b = c) :
    y.toNat + 2 ^ 32 * c.toNat = b.toNat + a.toNat := by
  rw [Nat.add_comm b.toNat]; exact fmP1 hy hc

/-- `carrying_add` of three words, as two `add`/`sltu` pairs and an `add` of
the carries. -/
theorem fmP3 {ta tb t cin y c1 c2 c : Word} (ht : aluEval .add ta tb = t)
    (h1 : aluEval .sltu t ta = c1 ∨ aluEval .sltu t tb = c1)
    (hy : aluEval .add cin t = y ∨ aluEval .add t cin = y) (h2 : aluEval .sltu y t = c2)
    (hc : aluEval .add c2 c1 = c ∨ aluEval .add c1 c2 = c) :
    y.toNat + 2 ^ 32 * c.toNat = ta.toNat + tb.toNat + cin.toNat := by
  have et := tn_add ht
  have := ta.isLt; have := tb.isLt; have := cin.isLt; have := t.isLt; have := y.isLt
  have ey : y.toNat = (cin.toNat + t.toNat) % 2 ^ 32 := by
    rcases hy with hy | hy
    · exact tn_add hy
    · rw [tn_add hy, Nat.add_comm]
  have e2 := tn_sltu h2
  have ec : c.toNat = (c2.toNat + c1.toNat) % 2 ^ 32 := by
    rcases hc with hc | hc
    · exact tn_add hc
    · rw [tn_add hc, Nat.add_comm]
  rcases h1 with h1 | h1 <;> rcases tn_sltu h1 with ⟨_, k1⟩ | ⟨_, k1⟩ <;>
    rcases e2 with ⟨_, k2⟩ | ⟨_, k2⟩ <;> omega

theorem fmP3s {ta tb t cin y c1 c2 c : Word} (ht : aluEval .add ta tb = t)
    (h1 : aluEval .sltu t ta = c1 ∨ aluEval .sltu t tb = c1)
    (hy : aluEval .add cin t = y ∨ aluEval .add t cin = y) (h2 : aluEval .sltu y t = c2)
    (hc : aluEval .add c2 c1 = c ∨ aluEval .add c1 c2 = c) :
    y.toNat + 2 ^ 32 * c.toNat = tb.toNat + ta.toNat + cin.toNat := by
  rw [Nat.add_comm tb.toNat]; exact fmP3 ht h1 hy h2 hc

/-- `carrying_mul_add` by `2^32 - 1`: `x - m` plus the carry in for the low
word, and `mulhu m (2^32 - 1)` plus a borrow check and a carry check for the
high word. -/
theorem fmP4 {x m d cin y h sb sr c : Word} (hd : aluEval .sub x m = d) (hh : aluEval .mulhu m 0xFFFFFFFF = h)
    (hb : aluEval .sltu d x = sb ∨ aluEval .sltu d (aluEval .sub 0 m) = sb)
    (hy : aluEval .add d cin = y ∨ aluEval .add cin d = y) (hr : aluEval .sltu y d = sr)
    (hc : c = aluEval .add sr (aluEval .add sb h) ∨ c = aluEval .add sr (aluEval .add h sb) ∨
      c = aluEval .add (aluEval .add sb h) sr ∨ c = aluEval .add (aluEval .add h sb) sr) :
    y.toNat + 2 ^ 32 * c.toNat = m.toNat * (2 ^ 32 - 1) + x.toNat + cin.toNat := by
  have := x.isLt; have := m.isLt; have := cin.isLt; have := d.isLt; have := y.isLt
  have ed := tn_sub hd
  have eh := tn_mulhuM1 hh
  have ey : y.toNat = (d.toNat + cin.toNat) % 2 ^ 32 := by
    rcases hy with hy | hy
    · exact tn_add hy
    · rw [tn_add hy, Nat.add_comm]
  have er := tn_sltu hr
  have eb : (d.toNat < x.toNat ∧ sb.toNat = 1) ∨ (x.toNat ≤ d.toNat ∧ sb.toNat = 0) ∨
      (d.toNat < (2 ^ 32 - m.toNat) % 2 ^ 32 ∧ sb.toNat = 1) ∨
      ((2 ^ 32 - m.toNat) % 2 ^ 32 ≤ d.toNat ∧ sb.toNat = 0) := by
    rcases hb with hb | hb
    · rcases tn_sltu hb with h | h
      · exact .inl h
      · exact .inr (.inl h)
    · have en : (aluEval .sub 0 m).toNat = (2 ^ 32 - m.toNat) % 2 ^ 32 := by
        rw [tn_sub rfl]; rfl
      rcases tn_sltu hb with h | h
      · rw [en] at h; exact .inr (.inr (.inl h))
      · rw [en] at h; exact .inr (.inr (.inr h))
  have es : (sr.toNat + sb.toNat + h.toNat) % 2 ^ 32 = c.toNat := by
    rcases hc with hc | hc | hc | hc <;> rw [hc] <;> simp only [aluEval, BitVec.toNat_add] <;> omega
  rcases eh with ⟨_, kh⟩ | ⟨_, kh⟩ <;> rcases er with ⟨_, kr⟩ | ⟨_, kr⟩ <;>
    rcases eb with ⟨_, kb⟩ | ⟨_, kb⟩ | ⟨_, kb⟩ | ⟨_, kb⟩ <;> omega

/-- One round of the reduction: the six carry equations of round `i`, summed
with the weights of limbs `i + 3` to `i + 9`. The round's multiplier `m`
leaves limb `i` and returns as `m · p`. -/
theorem mont_round {x3 x4 x5 x6 x7 x8 m ci y3 y4 y5 y6 y7 y8 co c1 c2 c3 c4 c5 : Nat}
    (e3 : y3 + 2 ^ 32 * c1 = x3 + m) (e4 : y4 + 2 ^ 32 * c2 = x4 + c1) (e5 : y5 + 2 ^ 32 * c3 = x5 + c2)
    (e6 : y6 + 2 ^ 32 * c4 = x6 + m + c3) (e7 : y7 + 2 ^ 32 * c5 = m * (2 ^ 32 - 1) + x7 + c4)
    (e8 : y8 + 2 ^ 32 * co = x8 + ci + c5) :
    y3 + 2 ^ 32 * y4 + 2 ^ 64 * y5 + 2 ^ 96 * y6 + 2 ^ 128 * y7 + 2 ^ 160 * y8 + 2 ^ 192 * co + 2 ^ 128 * m =
      x3 + 2 ^ 32 * x4 + 2 ^ 64 * x5 + 2 ^ 96 * x6 + 2 ^ 128 * x7 + 2 ^ 160 * x8 + 2 ^ 160 * ci +
        m * (1 + 2 ^ 96 + 2 ^ 160) := by
  omega

end C3.RV32
