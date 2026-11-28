import C3BootProofs.Proofs.BootRaise
import C3BootProofs.Spec.Level

/-!
# The level that `boot` reads

`boot` counts the set bits of the eFuse `SECURE_VERSION` field with a
branch-free bit count on the word that holds it, bits 14 to 29 of the word at
`0x6000883C`. `btPop` is that count, as `Proofs/BootRaise` follows it. This
file proves that `btPop` is `level (Fuses.ofNat v)` for the field's value
`v`, so the raise loop's exit condition in `boot_correct` is a statement
about `Spec/Level`.

The proof turns `btPop` into `Nat` arithmetic, shows that it reads only the
low 16 bits of the shifted word, and checks the 65,536 field values with the
kernel in 16 chunks.
-/

open C3 C3.RV32 C3.RV32.Cur

namespace C3.RV32.BootLevel

/-- The second half of `popN`, from the pair counts `b1`. -/
def popB (b1 : Nat) : Nat :=
  let b2 := ((b1 &&& 0x3333) + (b1 >>> 2 &&& 0x3333)) % 4294967296
  let b3 := (b2 + b2 >>> 4) % 4294967296
  ((b3 &&& 0xF) + ((b3 <<< 20) % 4294967296) >>> 28) % 4294967296

/-- `btPop` in `Nat` arithmetic, from the word shifted right by 14. -/
def popN (a : Nat) : Nat := popB ((4294967296 - (a >>> 1 &&& 0x5555) + a) % 4294967296)

/-- The number of set bits among the low 16 bits of `v`. -/
def bits16 (v : Nat) : Nat :=
  (v >>> 0) % 2 + (v >>> 1) % 2 + (v >>> 2) % 2 + (v >>> 3) % 2 + (v >>> 4) % 2 + (v >>> 5) % 2 + (v >>> 6) % 2 + (v >>> 7) % 2 + (v >>> 8) % 2 + (v >>> 9) % 2 + (v >>> 10) % 2 + (v >>> 11) % 2 + (v >>> 12) % 2 + (v >>> 13) % 2 + (v >>> 14) % 2 + (v >>> 15) % 2

theorem btPop_toNat (w : Word) : (btPop w).toNat = popN (w.toNat >>> 14) := by
  simp only [btPop, popN, popB, aluEval, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_and,
    BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  simp only [show (15 : Word).toNat = 15 from rfl, show (14 : Word).toNat = 14 from rfl,
    show (21845 : Word).toNat = 21845 from rfl, show (13107 : Word).toNat = 13107 from rfl,
    show (2 : Word).toNat = 2 from rfl, show (4 : Word).toNat = 4 from rfl,
    show (20 : Word).toNat = 20 from rfl, show (28 : Word).toNat = 28 from rfl,
    show w.toNat >>> 15 = w.toNat >>> 14 >>> 1 from (Nat.shiftRight_add _ 14 1), Nat.reducePow,
    Nat.reduceMod]

theorem and_low (x : Nat) {m k : Nat} (hm : m < 2 ^ k) : x &&& m = (x % 2 ^ k) &&& m := by
  rw [← Nat.mod_eq_of_lt (Nat.and_lt_two_pow x hm), Nat.and_mod_two_pow, Nat.mod_eq_of_lt hm]

theorem popB_mod {b b' : Nat} (h : b % 65536 = b' % 65536) : popB b = popB b' := by
  have e1 : b &&& 0x3333 = b' &&& 0x3333 := by
    rw [and_low b (k := 14) (by decide), and_low b' (k := 14) (by decide)]; congr 1; omega
  have e2 : b >>> 2 &&& 0x3333 = b' >>> 2 &&& 0x3333 := by
    rw [and_low _ (k := 14) (by decide), and_low (b' >>> 2) (k := 14) (by decide),
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]; congr 1; omega
  simp only [popB, e1, e2]

theorem popN_mod (a : Nat) : popN a = popN (a % 65536) := by
  have hx : a >>> 1 &&& 0x5555 = (a % 65536) >>> 1 &&& 0x5555 := by
    rw [and_low _ (k := 15) (by decide), and_low ((a % 65536) >>> 1) (k := 15) (by decide),
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]; congr 1; omega
  have hle : (a % 65536) >>> 1 &&& 0x5555 ≤ 0x5555 := Nat.and_le_right
  unfold popN; rw [hx]; exact popB_mod (by omega)

/-- The values `h * 4096` to `h * 4096 + 4095` on which `popN` counts the set bits. -/
def popChunk (h : Nat) : Bool :=
  Nat.all 64 fun m _ => Nat.all 64 fun l _ =>
    popN (h * 4096 + m * 64 + l) == bits16 (h * 4096 + m * 64 + l)

theorem popChunk_0 : popChunk 0 = true := by decide +kernel
theorem popChunk_1 : popChunk 1 = true := by decide +kernel
theorem popChunk_2 : popChunk 2 = true := by decide +kernel
theorem popChunk_3 : popChunk 3 = true := by decide +kernel
theorem popChunk_4 : popChunk 4 = true := by decide +kernel
theorem popChunk_5 : popChunk 5 = true := by decide +kernel
theorem popChunk_6 : popChunk 6 = true := by decide +kernel
theorem popChunk_7 : popChunk 7 = true := by decide +kernel
theorem popChunk_8 : popChunk 8 = true := by decide +kernel
theorem popChunk_9 : popChunk 9 = true := by decide +kernel
theorem popChunk_10 : popChunk 10 = true := by decide +kernel
theorem popChunk_11 : popChunk 11 = true := by decide +kernel
theorem popChunk_12 : popChunk 12 = true := by decide +kernel
theorem popChunk_13 : popChunk 13 = true := by decide +kernel
theorem popChunk_14 : popChunk 14 = true := by decide +kernel
theorem popChunk_15 : popChunk 15 = true := by decide +kernel

theorem all_of {n : Nat} {g : Nat → Bool} (h : Nat.all n (fun i _ => g i) = true) :
    ∀ i, i < n → g i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    simp only [Nat.all, Bool.and_eq_true] at h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
    · exact ih h.1 i h'
    · exact h.2

theorem popN_bits {v : Nat} (hv : v < 65536) : popN v = bits16 v := by
  have hall : Nat.all 16 (fun h _ => popChunk h) = true := by
    simp only [Nat.all, popChunk_0, popChunk_1, popChunk_2, popChunk_3, popChunk_4, popChunk_5, popChunk_6, popChunk_7, popChunk_8, popChunk_9, popChunk_10, popChunk_11, popChunk_12, popChunk_13, popChunk_14, popChunk_15, Bool.and_self]
  have hc := all_of hall (v / 4096) (by omega)
  have hm := all_of hc (v % 4096 / 64) (by omega)
  have hl := all_of hm (v % 64) (by omega)
  have e : v / 4096 * 4096 + v % 4096 / 64 * 64 + v % 64 = v := by omega
  rw [e] at hl
  exact beq_iff_eq.mp hl

theorem bit_ite (v i : Nat) : (if v.testBit i then 1 else 0) = v >>> i % 2 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ i) with h | h <;> simp [h]

theorem bits16_level (v : Nat) : bits16 v = level (Fuses.ofNat v) := by
  simp only [Fuses.ofNat, maxLevel, List.range, List.range.loop, List.map, level, bit_ite, bits16]
  omega

/-- The level that `boot` computes from the eFuse word `w` is the level of
the `SECURE_VERSION` field, bits 14 to 29 of `w`. -/
theorem btPop_level (w : Word) :
    (btPop w).toNat = level (Fuses.ofNat ((w.toNat >>> 14) % 65536)) := by
  rw [btPop_toNat, popN_mod, popN_bits (Nat.mod_lt _ (by decide)), bits16_level]

/-- When `boot`'s raise loop leaves, the eFuse level is at least `target`. -/
theorem btPop_ge {w target : Word} (h : (btPop w).ult target = false) :
    target.toNat ≤ level (Fuses.ofNat ((w.toNat >>> 14) % 65536)) := by
  rw [← btPop_level]
  simp only [BitVec.ult, decide_eq_false_iff_not, Nat.not_lt] at h
  exact h

end C3.RV32.BootLevel
