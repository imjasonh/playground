import C3BootProofs.Proofs.MemsetAny
import C3BootProofs.Proofs.ShaSpec

/-!
# `memcpy`, for any buffers

`memcpy_aligned` covers word-aligned buffers. Most callers copy byte
buffers of any alignment and length, so `memcpy_correct` covers every call
whose buffers don't overlap: the compiled `compiler_builtins` `memcpy`
copies the `n` bytes at `src` to `dst` and leaves every other byte outside
its own 16-byte stack frame alone.

The compiled code has four paths. Below 16 bytes it copies one byte at a
time. Otherwise it copies bytes up to the destination's first 4-byte
boundary, then words, then the bytes left over. When the source is then
4-byte aligned too, it copies the words with `lw` and `sw`. Otherwise it
reads aligned source words and splices each pair with shifts, building the
partial words at either end in its stack frame. The proof follows each loop
with `copyBytes`, which says how many bytes are copied so far.
-/

namespace C3.RV32

open C3.Image

/-- `M` with the `k` bytes from `dst` set to the `k` bytes from `src`. -/
def copyBytes (M : Word → BitVec 8) (dst src : Word) (k : Nat) : Word → BitVec 8 :=
  fun x => if (x - dst).toNat < k then M (src + (x - dst)) else M x

theorem copyBytes_zero (M : Word → BitVec 8) (dst src : Word) : copyBytes M dst src 0 = M := by
  funext x; simp [copyBytes]

/-- Copying the next byte copies one more byte. -/
theorem copyBytes_succ {M : Word → BitVec 8} {dst src : Word} {k : Nat} (hk : k < 2 ^ 32) :
    memStore8 (copyBytes M dst src k) (dst + BitVec.ofNat 32 k) (M (src + BitVec.ofNat 32 k)) =
      copyBytes M dst src (k + 1) := by
  funext x
  unfold memStore8 copyBytes
  by_cases hx : x = dst + BitVec.ofNat 32 k
  · subst hx
    rw [ite_eq_left rfl, add_sub_toNat dst hk, ite_eq_left (Nat.lt_succ_self k),
      BitVec.add_comm dst, BitVec.add_sub_cancel]
  · rw [ite_eq_right hx]
    have hne : (x - dst).toNat ≠ k := fun h => hx (sub_eq_ofNat hk h)
    by_cases hlt : (x - dst).toNat < k
    · rw [ite_eq_left hlt, ite_eq_left (by omega)]
    · rw [ite_eq_right hlt, ite_eq_right (by omega)]

/-- A byte apart from the `n` bytes at `dst` keeps its value. -/
theorem copyBytes_sep {M : Word → BitVec 8} {dst src y : Word} {n k : Nat}
    (hs : Sep dst n y 1) (hk : k ≤ n) : copyBytes M dst src k y = M y := by
  unfold copyBytes
  rw [ite_eq_right]
  intro hlt
  have e := sub_eq_ofNat (k := (y - dst).toNat) (y - dst).isLt rfl
  have := hs (y - dst).toNat (by omega) 0 (by decide)
  rw [add_ofNat_zero] at this
  exact this e.symm

theorem CodeIn.copyBytes {M : Word → BitVec 8} {dst src base : Word} {n k : Nat}
    {code : List Nat} (hc : CodeIn M base code) (hs : Sep dst n base code.length) (hk : k ≤ n) :
    CodeIn (C3.RV32.copyBytes M dst src k) base code := fun i hi => by
  rw [copyBytes_sep (hs.subR (c := i) (l := 1) (by omega)) hk]
  exact hc i hi

/-- Storing a word whose bytes are the next 4 source bytes copies them. -/
theorem copyBytes_word {M : Word → BitVec 8} {dst src w : Word} {k : Nat}
    (hk : k + 4 ≤ 2 ^ 32)
    (hw : ∀ i, i < 4 → w.extractLsb' (8 * i) 8 = M (src + BitVec.ofNat 32 (k + i))) :
    memStore32 (copyBytes M dst src k) (dst + BitVec.ofNat 32 k) w = copyBytes M dst src (k + 4) := by
  unfold memStore32
  have e : ∀ j : Nat, dst + BitVec.ofNat 32 k + BitVec.ofNat 32 j = dst + BitVec.ofNat 32 (k + j) :=
    fun j => add_ofNat_assoc dst k j
  rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, show (2 : Word) = BitVec.ofNat 32 2 from rfl,
    show (3 : Word) = BitVec.ofNat 32 3 from rfl, e, e, e,
    show w.extractLsb' 0 8 = M (src + BitVec.ofNat 32 k) from hw 0 (by decide),
    show w.extractLsb' 8 8 = M (src + BitVec.ofNat 32 (k + 1)) from hw 1 (by decide),
    show w.extractLsb' 16 8 = M (src + BitVec.ofNat 32 (k + 2)) from hw 2 (by decide),
    show w.extractLsb' 24 8 = M (src + BitVec.ofNat 32 (k + 3)) from hw 3 (by decide),
    copyBytes_succ (by omega), copyBytes_succ (by omega), copyBytes_succ (by omega),
    copyBytes_succ (by omega)]

/-- Byte `j` of the word loaded from `a`. -/
theorem load_byte (M : Word → BitVec 8) (a : Word) :
    ∀ j, j < 4 → (memLoad32 M a).extractLsb' (8 * j) 8 = M (a + BitVec.ofNat 32 j) := by
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
  (apply BitVec.eq_of_getLsbD_eq
   intro i hi
   simp only [memLoad32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true,
     Bool.true_and])
  · simp [show 8 * 0 + i = i by omega] <;> first | rfl | (intro h; exact absurd h (by omega))
  · simp [show ¬ (8 * 1 + i < 8) by omega, show 8 * 1 + i - 8 = i by omega] <;> first | rfl | (intro h; exact absurd h (by omega))
  · simp [show ¬ (8 * 2 + i < 8) by omega, show ¬ (8 * 2 + i - 8 < 8) by omega, show 8 * 2 + i - 8 - 8 = i by omega] <;> first | rfl | (intro h; exact absurd h (by omega))
  · simp [show ¬ (8 * 3 + i < 8) by omega, show ¬ (8 * 3 + i - 8 < 8) by omega,
      show ¬ (8 * 3 + i - 8 - 8 < 8) by omega, show 8 * 3 + i - 8 - 8 - 8 = i by omega] <;> first | rfl | (intro h; exact absurd h (by omega))

/-- The two halves of a spliced word have no bits in common. -/
theorem splice_disj (p q : Word) (k : Nat) :
    ∀ i, i < 32 → ((q <<< (32 - k)).getLsbD i && (p >>> k).getLsbD i) = false := by
  intro i hi
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases h : i < 32 - k
  · simp [h]
  · rw [BitVec.getLsbD_of_ge p (k + i) (by omega)]; simp

/-- The word `memcpy` stores when the source is `s` bytes past a 4-byte
boundary: the high `4 - s` bytes of `p` followed by the low `s` bytes of
`q`. -/
theorem splice_byte (p q : Word) (s i : Nat) (hs : 1 ≤ s) (hs3 : s ≤ 3) (hi : i < 4) :
    (aluEval .or (aluEval .sll q (BitVec.ofNat 32 (32 - 8 * s)))
        (aluEval .srl p (BitVec.ofNat 32 (8 * s)))).extractLsb' (8 * i) 8 =
      if i + s < 4 then p.extractLsb' (8 * (i + s)) 8 else q.extractLsb' (8 * (i + s - 4)) 8 := by
  have hk : (BitVec.ofNat 32 (32 - 8 * s)).toNat % 32 = 32 - 8 * s := by
    rw [BitVec.toNat_ofNat]; omega
  have hk' : (BitVec.ofNat 32 (8 * s)).toNat % 32 = 8 * s := by
    rw [BitVec.toNat_ofNat]; omega
  show ((q <<< ((BitVec.ofNat 32 (32 - 8 * s)).toNat % 32)) |||
      (p >>> ((BitVec.ofNat 32 (8 * s)).toNat % 32))).extractLsb' (8 * i) 8 = _
  rw [hk, hk', ← Sha256.add_disj (splice_disj p q (8 * s))]
  have hP := p.isLt
  have hQ := q.isLt
  rcases (show s = 1 ∨ s = 2 ∨ s = 3 by omega) with rfl | rfl | rfl <;>
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
  · simp only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT]
    simp only [ite_true, ite_false]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_add, BitVec.toNat_shiftLeft,
      BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    omega

section

set_option maxRecDepth 20000

theorem mcy_at_0 : fetchRel memcpyBodyCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem mcy_at_2 : fetchRel memcpyBodyCode 0x2 = some (.aluImm .add a3 x0 0x10, 2) := by decide
theorem mcy_at_4 : fetchRel memcpyBodyCode 0x4 = some (.branch .bltu a2 a3 0x72, 4) := by decide
theorem mcy_at_8 : fetchRel memcpyBodyCode 0x8 = some (.alu .sub a3 x0 a0, 4) := by decide
theorem mcy_at_c : fetchRel memcpyBodyCode 0xC = some (.aluImm .and a3 a3 0x3, 2) := by decide
theorem mcy_at_e : fetchRel memcpyBodyCode 0xE = some (.alu .add a4 a0 a3, 4) := by decide
theorem mcy_at_12 : fetchRel memcpyBodyCode 0x12 = some (.branch .bgeu a0 a4 0x1A, 4) := by decide
theorem mcy_at_16 : fetchRel memcpyBodyCode 0x16 = some (.alu .add a5 x0 a3, 2) := by decide
theorem mcy_at_18 : fetchRel memcpyBodyCode 0x18 = some (.alu .add a6 x0 a0, 2) := by decide
theorem mcy_at_1a : fetchRel memcpyBodyCode 0x1A = some (.alu .add (17 : Fin 32) x0 a1, 2) := by decide
theorem mcy_at_1c : fetchRel memcpyBodyCode 0x1C = some (.load .lbu (5 : Fin 32) (17 : Fin 32) 0x0, 4) := by decide
theorem mcy_at_20 : fetchRel memcpyBodyCode 0x20 = some (.aluImm .add a5 a5 0xFFFFFFFF, 2) := by decide
theorem mcy_at_22 : fetchRel memcpyBodyCode 0x22 = some (.store .sb a6 (5 : Fin 32) 0x0, 4) := by decide
theorem mcy_at_26 : fetchRel memcpyBodyCode 0x26 = some (.aluImm .add a6 a6 0x1, 2) := by decide
theorem mcy_at_28 : fetchRel memcpyBodyCode 0x28 = some (.aluImm .add (17 : Fin 32) (17 : Fin 32) 0x1, 2) := by decide
theorem mcy_at_2a : fetchRel memcpyBodyCode 0x2A = some (.branch .bne a5 x0 0xFFFFFFF2, 2) := by decide
theorem mcy_at_2c : fetchRel memcpyBodyCode 0x2C = some (.alu .add a1 a1 a3, 2) := by decide
theorem mcy_at_2e : fetchRel memcpyBodyCode 0x2E = some (.alu .sub a2 a2 a3, 2) := by decide
theorem mcy_at_30 : fetchRel memcpyBodyCode 0x30 = some (.aluImm .and a5 a2 0xFFFFFFFC, 4) := by decide
theorem mcy_at_34 : fetchRel memcpyBodyCode 0x34 = some (.aluImm .and (5 : Fin 32) a1 0x3, 4) := by decide
theorem mcy_at_38 : fetchRel memcpyBodyCode 0x38 = some (.alu .add a3 a4 a5, 4) := by decide
theorem mcy_at_3c : fetchRel memcpyBodyCode 0x3C = some (.branch .beq (5 : Fin 32) x0 0x46, 4) := by decide
theorem mcy_at_40 : fetchRel memcpyBodyCode 0x40 = some (.aluImm .add a6 x0 0x0, 2) := by decide
theorem mcy_at_42 : fetchRel memcpyBodyCode 0x42 = some (.aluImm .add (17 : Fin 32) x0 0x4, 2) := by decide
theorem mcy_at_44 : fetchRel memcpyBodyCode 0x44 = some (.alu .sub (17 : Fin 32) (17 : Fin 32) (5 : Fin 32), 4) := by decide
theorem mcy_at_48 : fetchRel memcpyBodyCode 0x48 = some (.aluImm .add (6 : Fin 32) sp 0xC, 4) := by decide
theorem mcy_at_4c : fetchRel memcpyBodyCode 0x4C = some (.aluImm .and (7 : Fin 32) (17 : Fin 32) 0x1, 4) := by decide
theorem mcy_at_50 : fetchRel memcpyBodyCode 0x50 = some (.store .sw sp x0 0xC, 2) := by decide
theorem mcy_at_52 : fetchRel memcpyBodyCode 0x52 = some (.alu .or (6 : Fin 32) (6 : Fin 32) (5 : Fin 32), 4) := by decide
theorem mcy_at_56 : fetchRel memcpyBodyCode 0x56 = some (.branch .bne (7 : Fin 32) x0 0x44, 4) := by decide
theorem mcy_at_5a : fetchRel memcpyBodyCode 0x5A = some (.aluImm .and (17 : Fin 32) (17 : Fin 32) 0x2, 4) := by decide
theorem mcy_at_5e : fetchRel memcpyBodyCode 0x5E = some (.branch .bne (17 : Fin 32) x0 0x4E, 4) := by decide
theorem mcy_at_62 : fetchRel memcpyBodyCode 0x62 = some (.load .lw (17 : Fin 32) sp 0xC, 2) := by decide
theorem mcy_at_64 : fetchRel memcpyBodyCode 0x64 = some (.aluImm .add (7 : Fin 32) a4 0x4, 4) := by decide
theorem mcy_at_68 : fetchRel memcpyBodyCode 0x68 = some (.aluImm .sll a6 (5 : Fin 32) 0x3, 4) := by decide
theorem mcy_at_6c : fetchRel memcpyBodyCode 0x6C = some (.alu .sub (6 : Fin 32) a1 (5 : Fin 32), 4) := by decide
theorem mcy_at_70 : fetchRel memcpyBodyCode 0x70 = some (.branch .bltu (7 : Fin 32) a3 0x5C, 4) := by decide
theorem mcy_at_74 : fetchRel memcpyBodyCode 0x74 = some (.jal x0 0x82, 2) := by decide
theorem mcy_at_76 : fetchRel memcpyBodyCode 0x76 = some (.alu .add a3 x0 a0, 2) := by decide
theorem mcy_at_78 : fetchRel memcpyBodyCode 0x78 = some (.alu .add a4 a0 a2, 4) := by decide
theorem mcy_at_7c : fetchRel memcpyBodyCode 0x7C = some (.branch .bltu a0 a4 0xF6, 4) := by decide
theorem mcy_at_80 : fetchRel memcpyBodyCode 0x80 = some (.jal x0 0x102, 2) := by decide
theorem mcy_at_82 : fetchRel memcpyBodyCode 0x82 = some (.branch .bgeu a4 a3 0xE4, 4) := by decide
theorem mcy_at_86 : fetchRel memcpyBodyCode 0x86 = some (.alu .add a6 x0 a1, 2) := by decide
theorem mcy_at_88 : fetchRel memcpyBodyCode 0x88 = some (.load .lw (17 : Fin 32) a6 0x0, 4) := by decide
theorem mcy_at_8c : fetchRel memcpyBodyCode 0x8C = some (.store .sw a4 (17 : Fin 32) 0x0, 4) := by decide
theorem mcy_at_90 : fetchRel memcpyBodyCode 0x90 = some (.aluImm .add a4 a4 0x4, 2) := by decide
theorem mcy_at_92 : fetchRel memcpyBodyCode 0x92 = some (.aluImm .add a6 a6 0x4, 2) := by decide
theorem mcy_at_94 : fetchRel memcpyBodyCode 0x94 = some (.branch .bltu a4 a3 0xFFFFFFF4, 4) := by decide
theorem mcy_at_98 : fetchRel memcpyBodyCode 0x98 = some (.jal x0 0xCE, 2) := by decide
theorem mcy_at_9a : fetchRel memcpyBodyCode 0x9A = some (.load .lbu a6 a1 0x0, 4) := by decide
theorem mcy_at_9e : fetchRel memcpyBodyCode 0x9E = some (.store .sb (6 : Fin 32) a6 0x0, 4) := by decide
theorem mcy_at_a2 : fetchRel memcpyBodyCode 0xA2 = some (.aluImm .add a6 x0 0x1, 2) := by decide
theorem mcy_at_a4 : fetchRel memcpyBodyCode 0xA4 = some (.aluImm .and (17 : Fin 32) (17 : Fin 32) 0x2, 4) := by decide
theorem mcy_at_a8 : fetchRel memcpyBodyCode 0xA8 = some (.branch .beq (17 : Fin 32) x0 0xFFFFFFBA, 4) := by decide
theorem mcy_at_ac : fetchRel memcpyBodyCode 0xAC = some (.alu .add (17 : Fin 32) a1 a6, 4) := by decide
theorem mcy_at_b0 : fetchRel memcpyBodyCode 0xB0 = some (.load .lh (17 : Fin 32) (17 : Fin 32) 0x0, 4) := by decide
theorem mcy_at_b4 : fetchRel memcpyBodyCode 0xB4 = some (.alu .add a6 a6 (6 : Fin 32), 2) := by decide
theorem mcy_at_b6 : fetchRel memcpyBodyCode 0xB6 = some (.store .sh a6 (17 : Fin 32) 0x0, 4) := by decide
theorem mcy_at_ba : fetchRel memcpyBodyCode 0xBA = some (.load .lw (17 : Fin 32) sp 0xC, 2) := by decide
theorem mcy_at_bc : fetchRel memcpyBodyCode 0xBC = some (.aluImm .add (7 : Fin 32) a4 0x4, 4) := by decide
theorem mcy_at_c0 : fetchRel memcpyBodyCode 0xC0 = some (.aluImm .sll a6 (5 : Fin 32) 0x3, 4) := by decide
theorem mcy_at_c4 : fetchRel memcpyBodyCode 0xC4 = some (.alu .sub (6 : Fin 32) a1 (5 : Fin 32), 4) := by decide
theorem mcy_at_c8 : fetchRel memcpyBodyCode 0xC8 = some (.branch .bgeu (7 : Fin 32) a3 0x2E, 4) := by decide
theorem mcy_at_cc : fetchRel memcpyBodyCode 0xCC = some (.alu .sub (7 : Fin 32) x0 a6, 4) := by decide
theorem mcy_at_d0 : fetchRel memcpyBodyCode 0xD0 = some (.aluImm .and (7 : Fin 32) (7 : Fin 32) 0x18, 4) := by decide
theorem mcy_at_d4 : fetchRel memcpyBodyCode 0xD4 = some (.alu .add (28 : Fin 32) x0 (17 : Fin 32), 2) := by decide
theorem mcy_at_d6 : fetchRel memcpyBodyCode 0xD6 = some (.load .lw (17 : Fin 32) (6 : Fin 32) 0x4, 4) := by decide
theorem mcy_at_da : fetchRel memcpyBodyCode 0xDA = some (.alu .srl (28 : Fin 32) (28 : Fin 32) a6, 4) := by decide
theorem mcy_at_de : fetchRel memcpyBodyCode 0xDE = some (.aluImm .add (6 : Fin 32) (6 : Fin 32) 0x4, 2) := by decide
theorem mcy_at_e0 : fetchRel memcpyBodyCode 0xE0 = some (.alu .sll (29 : Fin 32) (17 : Fin 32) (7 : Fin 32), 4) := by decide
theorem mcy_at_e4 : fetchRel memcpyBodyCode 0xE4 = some (.alu .or (28 : Fin 32) (29 : Fin 32) (28 : Fin 32), 4) := by decide
theorem mcy_at_e8 : fetchRel memcpyBodyCode 0xE8 = some (.aluImm .add (29 : Fin 32) a4 0x8, 4) := by decide
theorem mcy_at_ec : fetchRel memcpyBodyCode 0xEC = some (.store .sw a4 (28 : Fin 32) 0x0, 4) := by decide
theorem mcy_at_f0 : fetchRel memcpyBodyCode 0xF0 = some (.aluImm .add a4 a4 0x4, 2) := by decide
theorem mcy_at_f2 : fetchRel memcpyBodyCode 0xF2 = some (.branch .bltu (29 : Fin 32) a3 0xFFFFFFE2, 4) := by decide
theorem mcy_at_f6 : fetchRel memcpyBodyCode 0xF6 = some (.aluImm .add (7 : Fin 32) x0 0x1, 2) := by decide
theorem mcy_at_f8 : fetchRel memcpyBodyCode 0xF8 = some (.store .sb sp x0 0x8, 4) := by decide
theorem mcy_at_fc : fetchRel memcpyBodyCode 0xFC = some (.store .sb sp x0 0x6, 4) := by decide
theorem mcy_at_100 : fetchRel memcpyBodyCode 0x100 = some (.branch .bne (5 : Fin 32) (7 : Fin 32) 0x18, 4) := by decide
theorem mcy_at_104 : fetchRel memcpyBodyCode 0x104 = some (.aluImm .add (7 : Fin 32) x0 0x0, 2) := by decide
theorem mcy_at_106 : fetchRel memcpyBodyCode 0x106 = some (.aluImm .add (5 : Fin 32) x0 0x0, 2) := by decide
theorem mcy_at_108 : fetchRel memcpyBodyCode 0x108 = some (.aluImm .add (29 : Fin 32) x0 0x0, 2) := by decide
theorem mcy_at_10a : fetchRel memcpyBodyCode 0x10A = some (.aluImm .add (28 : Fin 32) sp 0x8, 4) := by decide
theorem mcy_at_10e : fetchRel memcpyBodyCode 0x10E = some (.aluImm .and (30 : Fin 32) a1 0x1, 4) := by decide
theorem mcy_at_112 : fetchRel memcpyBodyCode 0x112 = some (.branch .bne (30 : Fin 32) x0 0x22, 4) := by decide
theorem mcy_at_116 : fetchRel memcpyBodyCode 0x116 = some (.jal x0 0x36, 2) := by decide
theorem mcy_at_118 : fetchRel memcpyBodyCode 0x118 = some (.load .lbu (7 : Fin 32) (6 : Fin 32) 0x4, 4) := by decide
theorem mcy_at_11c : fetchRel memcpyBodyCode 0x11C = some (.load .lbu (5 : Fin 32) (6 : Fin 32) 0x5, 4) := by decide
theorem mcy_at_120 : fetchRel memcpyBodyCode 0x120 = some (.store .sb sp (7 : Fin 32) 0x8, 4) := by decide
theorem mcy_at_124 : fetchRel memcpyBodyCode 0x124 = some (.aluImm .sll (5 : Fin 32) (5 : Fin 32) 0x8, 2) := by decide
theorem mcy_at_126 : fetchRel memcpyBodyCode 0x126 = some (.aluImm .add (29 : Fin 32) x0 0x2, 2) := by decide
theorem mcy_at_128 : fetchRel memcpyBodyCode 0x128 = some (.aluImm .add (28 : Fin 32) sp 0x6, 4) := by decide
theorem mcy_at_12c : fetchRel memcpyBodyCode 0x12C = some (.aluImm .and (30 : Fin 32) a1 0x1, 4) := by decide
theorem mcy_at_130 : fetchRel memcpyBodyCode 0x130 = some (.branch .beq (30 : Fin 32) x0 0x1C, 4) := by decide
theorem mcy_at_134 : fetchRel memcpyBodyCode 0x134 = some (.alu .add (6 : Fin 32) (6 : Fin 32) (29 : Fin 32), 2) := by decide
theorem mcy_at_136 : fetchRel memcpyBodyCode 0x136 = some (.load .lbu (6 : Fin 32) (6 : Fin 32) 0x4, 4) := by decide
theorem mcy_at_13a : fetchRel memcpyBodyCode 0x13A = some (.store .sb (28 : Fin 32) (6 : Fin 32) 0x0, 4) := by decide
theorem mcy_at_13e : fetchRel memcpyBodyCode 0x13E = some (.load .lbu (6 : Fin 32) sp 0x6, 4) := by decide
theorem mcy_at_142 : fetchRel memcpyBodyCode 0x142 = some (.load .lbu (7 : Fin 32) sp 0x8, 4) := by decide
theorem mcy_at_146 : fetchRel memcpyBodyCode 0x146 = some (.aluImm .sll (6 : Fin 32) (6 : Fin 32) 0x10, 2) := by decide
theorem mcy_at_148 : fetchRel memcpyBodyCode 0x148 = some (.alu .or (5 : Fin 32) (6 : Fin 32) (5 : Fin 32), 4) := by decide
theorem mcy_at_14c : fetchRel memcpyBodyCode 0x14C = some (.alu .sub (6 : Fin 32) x0 a6, 4) := by decide
theorem mcy_at_150 : fetchRel memcpyBodyCode 0x150 = some (.alu .add (5 : Fin 32) (5 : Fin 32) (7 : Fin 32), 2) := by decide
theorem mcy_at_152 : fetchRel memcpyBodyCode 0x152 = some (.aluImm .and (6 : Fin 32) (6 : Fin 32) 0x18, 4) := by decide
theorem mcy_at_156 : fetchRel memcpyBodyCode 0x156 = some (.alu .srl a6 (17 : Fin 32) a6, 4) := by decide
theorem mcy_at_15a : fetchRel memcpyBodyCode 0x15A = some (.alu .sll (17 : Fin 32) (5 : Fin 32) (6 : Fin 32), 4) := by decide
theorem mcy_at_15e : fetchRel memcpyBodyCode 0x15E = some (.alu .or a6 (17 : Fin 32) a6, 4) := by decide
theorem mcy_at_162 : fetchRel memcpyBodyCode 0x162 = some (.store .sw a4 a6 0x0, 4) := by decide
theorem mcy_at_166 : fetchRel memcpyBodyCode 0x166 = some (.alu .add a1 a1 a5, 2) := by decide
theorem mcy_at_168 : fetchRel memcpyBodyCode 0x168 = some (.aluImm .and a2 a2 0x3, 2) := by decide
theorem mcy_at_16a : fetchRel memcpyBodyCode 0x16A = some (.alu .add a4 a3 a2, 4) := by decide
theorem mcy_at_16e : fetchRel memcpyBodyCode 0x16E = some (.branch .bgeu a3 a4 0x14, 4) := by decide
theorem mcy_at_172 : fetchRel memcpyBodyCode 0x172 = some (.load .lbu a4 a1 0x0, 4) := by decide
theorem mcy_at_176 : fetchRel memcpyBodyCode 0x176 = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) := by decide
theorem mcy_at_178 : fetchRel memcpyBodyCode 0x178 = some (.store .sb a3 a4 0x0, 4) := by decide
theorem mcy_at_17c : fetchRel memcpyBodyCode 0x17C = some (.aluImm .add a3 a3 0x1, 2) := by decide
theorem mcy_at_17e : fetchRel memcpyBodyCode 0x17E = some (.aluImm .add a1 a1 0x1, 2) := by decide
theorem mcy_at_180 : fetchRel memcpyBodyCode 0x180 = some (.branch .bne a2 x0 0xFFFFFFF2, 2) := by decide
theorem mcy_at_182 : fetchRel memcpyBodyCode 0x182 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem mcy_at_184 : fetchRel memcpyBodyCode 0x184 = some (.jalr x0 ra 0x0, 2) := by decide

end

section Step

variable {M : Word → BitVec 8} {base : Word} {code : List Nat} {m : Machine} {off : Nat}
  {f : Fin 32 → Word}

theorem St.lh (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {rd rs1 : Fin 32} {o len : Word} {off' : Nat}
    (hf : fetchRel code off = some (.load .lh rd rs1 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off')
    (hal : (f rs1 + o).toNat % 2 = 0) :
    ∃ m1, step m = some m1 ∧
      St M base m1 off' (upd f rd ((M (f rs1 + o + 1) ++ M (f rs1 + o)).signExtend 32)) := by
  refine ⟨_, ?_, s.write (v := (M (f rs1 + o + 1) ++ M (f rs1 + o)).signExtend 32) (rd := rd) hn⟩
  have ha : aligned (loadSize .lh) (reg m rs1 + o) = true := by
    unfold aligned loadSize; rw [s.regs, hal]; rfl
  rw [step_code (s.codeAt hc) s.pc hf, ← s.regs rs1, ← s.mem]
  unfold exec
  simp only [ha, Bool.not_true]
  rfl

theorem St.sh (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {rs1 rs2 : Fin 32} {o len : Word} {off' : Nat}
    (hf : fetchRel code off = some (.store .sh rs1 rs2 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off')
    (hal : (f rs1 + o).toNat % 2 = 0) :
    ∃ m1, step m = some m1 ∧
      St (memStore8 (memStore8 M (f rs1 + o) ((f rs2).extractLsb' 0 8)) (f rs1 + o + 1)
        ((f rs2).extractLsb' 8 8)) base m1 off' f := by
  have ha : aligned (storeSize .sh) (reg m rs1 + o) = true := by
    unfold aligned storeSize; rw [s.regs, hal]; rfl
  refine ⟨Arch.setPc (store16 m (f rs1 + o) ((f rs2).extractLsb' 0 16)) (m.pc + len), ?_, ?_, ?_, ?_⟩
  · rw [step_code (s.codeAt hc) s.pc hf]
    unfold exec
    simp only [ha, Bool.not_true]
    rw [s.regs, s.regs]
    rfl
  · simp only [Machine.setPc_pc]; rw [s.pc, BitVec.add_assoc, hn]
  · rw [← s.mem]
    show memStore8 (memStore8 m.mem (f rs1 + o) (((f rs2).extractLsb' 0 16).extractLsb' 0 8)) (f rs1 + o + 1)
      (((f rs2).extractLsb' 0 16).extractLsb' 8 8) = _
    have e0 : ((f rs2).extractLsb' 0 16).extractLsb' 0 8 = (f rs2).extractLsb' 0 8 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi] <;> omega
    have e1 : ((f rs2).extractLsb' 0 16).extractLsb' 8 8 = (f rs2).extractLsb' 8 8 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi] <;> omega
    rw [e0, e1]
  · intro r; rw [← s.regs r]; rfl

end Step

/-- A byte loop of the form `lbu tmp, 0(sp); addi cnt, cnt, -1; sb tmp, 0(dp);
addi dp, dp, 1; addi sp, sp, 1; bnez cnt` at offset `o`. With `q` bytes
copied, `k` left, and the pointers at byte `q` of each buffer, it copies the
rest and leaves the loop at `o + 16`. `memcpy` has two of them. `B` is the
memory the copy reads from: the source bytes in it stay as they are while
the loop writes the destination. -/
theorem copy_loop {B : Word → BitVec 8} {base dst src : Word} {code : List Nat} {o e : Nat}
    {cnt dp sp tmp : Fin 32}
    (hc : ∀ j, j ≤ e → CodeIn (copyBytes B dst src j) base code) (he : e < 2 ^ 32)
    (ho : o + 16 < 2 ^ 32)
    (hsrc : ∀ j, j < e → ∀ k, k ≤ e → copyBytes B dst src k (src + BitVec.ofNat 32 j) =
      B (src + BitVec.ofNat 32 j))
    (f0 : fetchRel code o = some (.load .lbu tmp sp 0, 4))
    (f1 : fetchRel code (o + 4) = some (.aluImm .add cnt cnt 0xFFFFFFFF, 2))
    (f2 : fetchRel code (o + 6) = some (.store .sb dp tmp 0, 4))
    (f3 : fetchRel code (o + 10) = some (.aluImm .add dp dp 1, 2))
    (f4 : fetchRel code (o + 12) = some (.aluImm .add sp sp 1, 2))
    (f5 : fetchRel code (o + 14) = some (.branch .bne cnt x0 0xFFFFFFF2, 2))
    (h01 : cnt ≠ dp) (h02 : cnt ≠ sp) (h03 : cnt ≠ tmp) (h12 : dp ≠ sp) (h13 : dp ≠ tmp)
    (h23 : sp ≠ tmp) (z0 : cnt.val ≠ 0) (z1 : dp.val ≠ 0) (z2 : sp.val ≠ 0) (z3 : tmp.val ≠ 0) :
    ∀ k q (n : Machine), q + k = e → 0 < k →
      St (copyBytes B dst src q) base n o (reg n) → reg n cnt = BitVec.ofNat 32 k →
      reg n dp = dst + BitVec.ofNat 32 q → reg n sp = src + BitVec.ofNat 32 q →
      ∃ n', Steps n n' ∧ St (copyBytes B dst src e) base n' (o + 16) (reg n') ∧
        reg n' cnt = 0 ∧ reg n' dp = dst + BitVec.ofNat 32 e ∧ reg n' sp = src + BitVec.ofNat 32 e ∧
        ∀ r, r ≠ cnt → r ≠ dp → r ≠ sp → r ≠ tmp → reg n' r = reg n r := by
  intro k
  induction k with
  | zero => intro _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
    intro q n hqe _ s hcnt hdp hsp
    have hcq := hc q (by omega)
    have hcq1 := hc (q + 1) (by omega)
    have lit : ∀ a b : Nat, a + b < 2 ^ 32 → BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) :=
      fun a b _ => ofNat_add_lit a b
    obtain ⟨n1, d1, u1⟩ := s.lbu hcq f0 (off' := o + 4) (lit o 4 (by omega))
    have g1 : reg n1 tmp = (B (src + BitVec.ofNat 32 q)).zeroExtend 32 := by
      rw [u1.upd_eq z3, hsp, add_lit_zero, hsrc q (by omega) q (by omega)]
    have K1 := u1.upd_ne s.zero
    have u1' : St (copyBytes B dst src q) base n1 (o + 4) (reg n1) := u1.self
    obtain ⟨n2, d2, u2⟩ := u1'.aluImm hcq f1 (off' := o + 6) (by rw [show o + 6 = o + 4 + 2 by omega]; exact lit (o + 4) 2 (by omega))
    have g2 : reg n2 cnt = BitVec.ofNat 32 k := by
      rw [u2.upd_eq z0, K1 cnt h03, hcnt, dec_ofNat_succ (by omega)]
    have K2 := u2.upd_ne u1'.zero
    have u2' : St (copyBytes B dst src q) base n2 (o + 6) (reg n2) := u2.self
    obtain ⟨n3, d3, u3⟩ := u2'.sb hcq f2 (off' := o + 10) (by rw [show o + 10 = o + 6 + 4 by omega]; exact lit (o + 6) 4 (by omega))
    have hm : memStore8 (copyBytes B dst src q) (reg n2 dp + 0) ((reg n2 tmp).extractLsb' 0 8) =
        copyBytes B dst src (q + 1) := by
      rw [K2 dp h01.symm, K1 dp h13, hdp, add_lit_zero, K2 tmp h03.symm, g1]
      have : ((B (src + BitVec.ofNat 32 q)).zeroExtend 32).extractLsb' 0 8 = B (src + BitVec.ofNat 32 q) := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi] <;> omega
      rw [this]; exact copyBytes_succ (by omega)
    rw [hm] at u3
    obtain ⟨n4, d4, u4⟩ := u3.aluImm hcq1 f3 (off' := o + 12) (by rw [show o + 12 = o + 10 + 2 by omega]; exact lit (o + 10) 2 (by omega))
    have g4 : reg n4 dp = dst + BitVec.ofNat 32 (q + 1) := by
      rw [u4.upd_eq z1, K2 dp h01.symm, K1 dp h13, hdp]; exact add_ofNat_assoc dst q 1
    have K4 := u4.upd_ne u2'.zero
    have u4' : St (copyBytes B dst src (q + 1)) base n4 (o + 12) (reg n4) := u4.self
    obtain ⟨n5, d5, u5⟩ := u4'.aluImm hcq1 f4 (off' := o + 14) (by rw [show o + 14 = o + 12 + 2 by omega]; exact lit (o + 12) 2 (by omega))
    have g5 : reg n5 sp = src + BitVec.ofNat 32 (q + 1) := by
      rw [u5.upd_eq z2, K4 sp h12.symm, K2 sp h02.symm, K1 sp h23, hsp]; exact add_ofNat_assoc src q 1
    have K5 := u5.upd_ne u4'.zero
    have u5' : St (copyBytes B dst src (q + 1)) base n5 (o + 14) (reg n5) := u5.self
    have c5 : reg n5 cnt = BitVec.ofNat 32 k := by rw [K5 cnt h02, K4 cnt h01, g2]
    have d5' : reg n5 dp = dst + BitVec.ofNat 32 (q + 1) := by rw [K5 dp h12, g4]
    have frame : ∀ r, r ≠ cnt → r ≠ dp → r ≠ sp → r ≠ tmp → reg n5 r = reg n r := fun r q0 q1 q2 q3 => by
      rw [K5 r q2, K4 r q1, K2 r q0, K1 r q3]
    have zz : reg n5 x0 = 0 := u5'.zero
    by_cases hk : k = 0
    · subst hk
      obtain ⟨n6, d6, u6⟩ := u5'.notTaken hcq1 (o + 16) f5
        (by rw [show o + 16 = o + 14 + 2 by omega]; exact lit (o + 14) 2 (by omega)) (by
          simp [branchTaken, c5, zz])
      have hq : q + 1 = e := by omega
      rw [hq] at u6 d5' g5
      refine ⟨n6, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6))))), u6.self, ?_, ?_, ?_, ?_⟩
      · rw [u6.regs, c5]; rfl
      · rw [u6.regs, d5']
      · rw [u6.regs, g5]
      · intro r q0 q1 q2 q3; rw [u6.regs, frame r q0 q1 q2 q3]
    · have back : BitVec.ofNat 32 (o + 14) + 0xFFFFFFF2 = BitVec.ofNat 32 o := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          show (0xFFFFFFF2 : Word).toNat = 2 ^ 32 - 14 from rfl]
        omega
      obtain ⟨n6, d6, u6⟩ := u5'.taken hcq1 o f5 back (by
        simp only [branchTaken, c5, zz, bne_iff_ne, ne_eq]
        intro h; exact hk (ofNat_inj (by omega) (by decide) h))
      obtain ⟨n7, c7, u7, c7', p7, s7, f7⟩ := ih (q + 1) n6 (by omega) (by omega) u6.self
        (by rw [u6.regs, c5]) (by rw [u6.regs, d5']) (by rw [u6.regs, g5])
      refine ⟨n7, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 c7))))), u7, c7', p7, s7,
        fun r q0 q1 q2 q3 => ?_⟩
      rw [f7 r q0 q1 q2 q3, u6.regs, frame r q0 q1 q2 q3]

/-- The aligned word loop at 0x88: with `h + 4 * j` bytes copied, both
pointers at the next byte, both 4-byte aligned, and `w - j` words left, it
copies them and leaves the loop at 0x98. -/
theorem copyw_loop {B : Word → BitVec 8} {base dst src : Word} {h w : Nat}
    (hc : ∀ j, j ≤ w → CodeIn (copyBytes B dst src (h + 4 * j)) base memcpyBodyCode)
    (hald : (dst + BitVec.ofNat 32 h).toNat % 4 = 0) (hals : (src + BitVec.ofNat 32 h).toNat % 4 = 0)
    (hwrap : dst.toNat + h + 4 * w < 2 ^ 32)
    (hsrc : ∀ j, j < h + 4 * w → ∀ k, k ≤ h + 4 * w →
      copyBytes B dst src k (src + BitVec.ofNat 32 j) = B (src + BitVec.ofNat 32 j)) :
    ∀ k j (n : Machine), j + k = w → 0 < k →
      St (copyBytes B dst src (h + 4 * j)) base n 0x88 (reg n) →
      reg n a4 = dst + BitVec.ofNat 32 (h + 4 * j) → reg n a6 = src + BitVec.ofNat 32 (h + 4 * j) →
      reg n a3 = dst + BitVec.ofNat 32 (h + 4 * w) →
      ∃ n', Steps n n' ∧ St (copyBytes B dst src (h + 4 * w)) base n' 0x98 (reg n') ∧
        reg n' a4 = dst + BitVec.ofNat 32 (h + 4 * w) ∧ reg n' a6 = src + BitVec.ofNat 32 (h + 4 * w) ∧
        ∀ r, r ≠ a4 → r ≠ a6 → r ≠ (17 : Fin 32) → reg n' r = reg n r := by
  intro k
  induction k with
  | zero => intro _ _ _ hz; exact absurd hz (Nat.lt_irrefl 0)
  | succ k ih =>
    intro j n hjk _ s h4 h6 h3
    have hcj := hc j (by omega)
    have hcj1 := hc (j + 1) (by omega)
    have hq : h + 4 * j + 4 ≤ h + 4 * w := by omega
    have als : (src + BitVec.ofNat 32 (h + 4 * j)).toNat % 4 = 0 := by
      rw [← add_ofNat_assoc]; exact aligned_add hals (k := 4 * j) (by omega)
    have ald : (dst + BitVec.ofNat 32 (h + 4 * j)).toNat % 4 = 0 := by
      rw [← add_ofNat_assoc]; exact aligned_add hald (k := 4 * j) (by omega)
    obtain ⟨n1, d1, u1⟩ := s.lw hcj mcy_at_88 (off' := 0x8C) (by decide)
      (by rw [h6, add_lit_zero]; exact als)
    have g1 : ∀ i, i < 4 → (reg n1 (17 : Fin 32)).extractLsb' (8 * i) 8 =
        B (src + BitVec.ofNat 32 (h + 4 * j + i)) := fun i hi => by
      rw [u1.upd_eq (by decide), h6, add_lit_zero, load_byte _ _ i hi, add_ofNat_assoc,
        hsrc _ (by omega) _ (by omega)]
    have K1 := u1.upd_ne s.zero
    have u1' : St (copyBytes B dst src (h + 4 * j)) base n1 0x8C (reg n1) := u1.self
    obtain ⟨n2, d2, u2⟩ := u1'.sw hcj mcy_at_8c (off' := 0x90) (by decide)
      (by rw [K1 a4 (by decide), h4, add_lit_zero]; exact ald)
    rw [K1 a4 (by decide), h4, add_lit_zero, copyBytes_word (by omega) g1,
      show h + 4 * j + 4 = h + 4 * (j + 1) by omega] at u2
    obtain ⟨n3, d3, u3⟩ := u2.aluImm hcj1 mcy_at_90 (off' := 0x92) (by decide)
    have g3 : reg n3 a4 = dst + BitVec.ofNat 32 (h + 4 * (j + 1)) := by
      rw [u3.upd_eq (by decide), K1 a4 (by decide), h4]
      show dst + BitVec.ofNat 32 (h + 4 * j) + BitVec.ofNat 32 4 = _
      rw [add_ofNat_assoc]; congr 2
    have K3 := u3.upd_ne u1'.zero
    have u3' : St (copyBytes B dst src (h + 4 * (j + 1))) base n3 0x92 (reg n3) := u3.self
    obtain ⟨n4, d4, u4⟩ := u3'.aluImm hcj1 mcy_at_92 (off' := 0x94) (by decide)
    have g4 : reg n4 a6 = src + BitVec.ofNat 32 (h + 4 * (j + 1)) := by
      rw [u4.upd_eq (by decide), K3 a6 (by decide), K1 a6 (by decide), h6]
      show src + BitVec.ofNat 32 (h + 4 * j) + BitVec.ofNat 32 4 = _
      rw [add_ofNat_assoc]; congr 2
    have K4 := u4.upd_ne u3'.zero
    have u4' : St (copyBytes B dst src (h + 4 * (j + 1))) base n4 0x94 (reg n4) := u4.self
    have a4_4 : reg n4 a4 = dst + BitVec.ofNat 32 (h + 4 * (j + 1)) := by rw [K4 a4 (by decide), g3]
    have a3_4 : reg n4 a3 = dst + BitVec.ofNat 32 (h + 4 * w) := by
      rw [K4 a3 (by decide), K3 a3 (by decide), K1 a3 (by decide), h3]
    have frame : ∀ r, r ≠ a4 → r ≠ a6 → r ≠ (17 : Fin 32) → reg n4 r = reg n r := fun r q4 q6 q7 => by
      rw [K4 r q6, K3 r q4, K1 r q7]
    have ult := ult_ofNat (dst := dst) (a := h + 4 * (j + 1)) (b := h + 4 * w) (by omega) (by omega)
    by_cases hlt : j + 1 < w
    · obtain ⟨n5, d5, u5⟩ := u4'.taken hcj1 0x88 mcy_at_94 (by decide) (by
        simp only [branchTaken]; rw [a4_4, a3_4, ult]; exact decide_eq_true (by omega))
      obtain ⟨n6, c6, u6, q4, q6, f6⟩ := ih (j + 1) n5 (by omega) (by omega) u5.self
        (by rw [u5.regs, a4_4]) (by rw [u5.regs, g4]) (by rw [u5.regs, a3_4])
      refine ⟨n6, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 c6)))), u6, q4, q6, fun r q4 q6 q7 => ?_⟩
      rw [f6 r q4 q6 q7, u5.regs, frame r q4 q6 q7]
    · have hj : j + 1 = w := by omega
      obtain ⟨n5, d5, u5⟩ := u4'.notTaken hcj1 0x98 mcy_at_94 (by decide) (by
        simp only [branchTaken]; rw [a4_4, a3_4, ult]; exact decide_eq_false (by omega))
      rw [hj] at u5 a4_4 g4
      refine ⟨n5, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.single d5)))), u5.self, ?_, ?_, ?_⟩
      · rw [u5.regs, a4_4]
      · rw [u5.regs, g4]
      · intro r q4 q6 q7; rw [u5.regs, frame r q4 q6 q7]

theorem addr_shift (src : Word) {a b c : Nat} (hb : b ≤ a + c) :
    src + BitVec.ofNat 32 a - BitVec.ofNat 32 b + BitVec.ofNat 32 c = src + BitVec.ofNat 32 (a + c - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := src.isLt
  omega

/-- The misaligned word loop at 0xD4, for a source `s` bytes past a 4-byte
boundary. With `h + 4 * j` bytes copied, `a7` holding the source word that
ends with the next `4 - s` source bytes, `t1` at the aligned address of that
word, and `w - 1 - j` words left before the last, it copies them and leaves
the loop at 0xF6, where the last word is left to copy. -/
theorem splice_loop {B : Word → BitVec 8} {base dst src : Word} {h w s : Nat}
    (hc : ∀ j, j ≤ w → CodeIn (copyBytes B dst src (h + 4 * j)) base memcpyBodyCode)
    (hs : 1 ≤ s) (hs3 : s ≤ 3) (hsh : s ≤ h + 4) (hw : 2 ≤ w)
    (hald : (dst + BitVec.ofNat 32 h).toNat % 4 = 0)
    (hals : (src + BitVec.ofNat 32 h - BitVec.ofNat 32 s).toNat % 4 = 0)
    (hwrap : dst.toNat + h + 4 * w < 2 ^ 32) (hwrap' : h + 4 * w < 2 ^ 32)
    (hsrc : ∀ j, j < h + 4 * w → ∀ k, k ≤ h + 4 * w →
      copyBytes B dst src k (src + BitVec.ofNat 32 j) = B (src + BitVec.ofNat 32 j)) :
    ∀ k j (n : Machine), j + k = w - 1 → 0 < k →
      St (copyBytes B dst src (h + 4 * j)) base n 0xD4 (reg n) →
      reg n a4 = dst + BitVec.ofNat 32 (h + 4 * j) →
      reg n (6 : Fin 32) = src + BitVec.ofNat 32 h - BitVec.ofNat 32 s + BitVec.ofNat 32 (4 * j) →
      (∀ i, s ≤ i → i < 4 → (reg n (17 : Fin 32)).extractLsb' (8 * i) 8 =
        B (src + BitVec.ofNat 32 (h + 4 * j + i - s))) →
      reg n a6 = BitVec.ofNat 32 (8 * s) → reg n (7 : Fin 32) = BitVec.ofNat 32 (32 - 8 * s) →
      reg n a3 = dst + BitVec.ofNat 32 (h + 4 * w) →
      ∃ n', Steps n n' ∧ St (copyBytes B dst src (h + 4 * (w - 1))) base n' 0xF6 (reg n') ∧
        reg n' a4 = dst + BitVec.ofNat 32 (h + 4 * (w - 1)) ∧
        reg n' (6 : Fin 32) = src + BitVec.ofNat 32 h - BitVec.ofNat 32 s + BitVec.ofNat 32 (4 * (w - 1)) ∧
        (∀ i, s ≤ i → i < 4 → (reg n' (17 : Fin 32)).extractLsb' (8 * i) 8 =
          B (src + BitVec.ofNat 32 (h + 4 * (w - 1) + i - s))) ∧
        ∀ r, r ≠ a4 → r ≠ (6 : Fin 32) → r ≠ (17 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) →
          reg n' r = reg n r := by
  intro k
  induction k with
  | zero => intro _ _ _ hz; exact absurd hz (Nat.lt_irrefl 0)
  | succ k ih =>
    intro j n hjk _ s0 h4 h6 h7 ha6 ht2 h3
    have hcj := hc j (by omega)
    have hcj1 := hc (j + 1) (by omega)
    let sb := src + BitVec.ofNat 32 h - BitVec.ofNat 32 s
    obtain ⟨n1, d1, u1⟩ := s0.alu hcj mcy_at_d4 (off' := 0xD6) (by decide)
    have g1 : reg n1 (28 : Fin 32) = reg n (17 : Fin 32) := by
      rw [u1.upd_eq (by decide), s0.zero]; exact BitVec.zero_add _
    have K1 := u1.upd_ne s0.zero
    have u1' : St (copyBytes B dst src (h + 4 * j)) base n1 0xD6 (reg n1) := u1.self
    have al1 : (sb + BitVec.ofNat 32 (4 * j) + 4).toNat % 4 = 0 := by
      rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
      exact aligned_add hals (k := 4 * j + 4) (by omega)
    obtain ⟨n2, d2, u2⟩ := u1'.lw hcj mcy_at_d6 (off' := 0xDA) (by decide)
      (by rw [K1 _ (by decide), h6]; exact al1)
    have g2 : ∀ i, i < 4 → (reg n2 (17 : Fin 32)).extractLsb' (8 * i) 8 =
        B (src + BitVec.ofNat 32 (h + 4 * j + 4 + i - s)) := fun i hi => by
      rw [u2.upd_eq (by decide), K1 _ (by decide), h6, load_byte _ _ i hi,
        show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc, add_ofNat_assoc,
        addr_shift src (by omega),
        show h + (4 * j + (4 + i)) - s = h + 4 * j + 4 + i - s by omega,
        hsrc _ (by omega) _ (by omega)]
    have K2 := u2.upd_ne u1'.zero
    have u2' : St (copyBytes B dst src (h + 4 * j)) base n2 0xDA (reg n2) := u2.self
    obtain ⟨n3, d3, u3⟩ := u2'.alu hcj mcy_at_da (off' := 0xDE) (by decide)
    have K3 := u3.upd_ne u2'.zero
    have u3' : St (copyBytes B dst src (h + 4 * j)) base n3 0xDE (reg n3) := u3.self
    obtain ⟨n4, d4, u4⟩ := u3'.aluImm hcj mcy_at_de (off' := 0xE0) (by decide)
    have K4 := u4.upd_ne u3'.zero
    have u4' : St (copyBytes B dst src (h + 4 * j)) base n4 0xE0 (reg n4) := u4.self
    obtain ⟨n5, d5, u5⟩ := u4'.alu hcj mcy_at_e0 (off' := 0xE4) (by decide)
    have K5 := u5.upd_ne u4'.zero
    have u5' : St (copyBytes B dst src (h + 4 * j)) base n5 0xE4 (reg n5) := u5.self
    obtain ⟨n6, d6, u6⟩ := u5'.alu hcj mcy_at_e4 (off' := 0xE8) (by decide)
    have K6 := u6.upd_ne u5'.zero
    have u6' : St (copyBytes B dst src (h + 4 * j)) base n6 0xE8 (reg n6) := u6.self
    have a6_2 : reg n2 a6 = BitVec.ofNat 32 (8 * s) := by rw [K2 a6 (by decide), K1 a6 (by decide), ha6]
    have t2_4 : reg n4 (7 : Fin 32) = BitVec.ofNat 32 (32 - 8 * s) := by
      rw [K4 _ (by decide), K3 _ (by decide), K2 _ (by decide), K1 _ (by decide), ht2]
    have v3 : reg n3 (28 : Fin 32) = aluEval .srl (reg n (17 : Fin 32)) (BitVec.ofNat 32 (8 * s)) := by
      rw [u3.upd_eq (by decide), K2 _ (by decide), g1, a6_2]
    have v5 : reg n5 (29 : Fin 32) = aluEval .sll (reg n2 (17 : Fin 32)) (BitVec.ofNat 32 (32 - 8 * s)) := by
      rw [u5.upd_eq (by decide), K4 _ (by decide), K3 _ (by decide), t2_4]
    have word : reg n6 (28 : Fin 32) = aluEval .or (aluEval .sll (reg n2 (17 : Fin 32))
        (BitVec.ofNat 32 (32 - 8 * s))) (aluEval .srl (reg n (17 : Fin 32)) (BitVec.ofNat 32 (8 * s))) := by
      rw [u6.upd_eq (by decide), v5, K5 _ (by decide), K4 _ (by decide), v3]
    have a4_6 : reg n6 a4 = dst + BitVec.ofNat 32 (h + 4 * j) := by
      rw [K6 a4 (by decide), K5 a4 (by decide), K4 a4 (by decide), K3 a4 (by decide), K2 a4 (by decide),
        K1 a4 (by decide), h4]
    obtain ⟨n7, d7, u7⟩ := u6'.aluImm hcj mcy_at_e8 (off' := 0xEC) (by decide)
    have g7 : reg n7 (29 : Fin 32) = dst + BitVec.ofNat 32 (h + 4 * j + 8) := by
      rw [u7.upd_eq (by decide), a4_6]
      show dst + BitVec.ofNat 32 (h + 4 * j) + BitVec.ofNat 32 8 = _
      rw [add_ofNat_assoc]
    have K7 := u7.upd_ne u6'.zero
    have u7' : St (copyBytes B dst src (h + 4 * j)) base n7 0xEC (reg n7) := u7.self
    have ald : (dst + BitVec.ofNat 32 (h + 4 * j)).toNat % 4 = 0 := by
      rw [← add_ofNat_assoc]; exact aligned_add hald (k := 4 * j) (by omega)
    obtain ⟨n8, d8, u8⟩ := u7'.sw hcj mcy_at_ec (off' := 0xF0) (by decide)
      (by rw [K7 a4 (by decide), a4_6, add_lit_zero]; exact ald)
    have hw8 : ∀ i, i < 4 → (reg n7 (28 : Fin 32)).extractLsb' (8 * i) 8 =
        B (src + BitVec.ofNat 32 (h + 4 * j + i)) := fun i hi => by
      rw [K7 _ (by decide), word, splice_byte _ _ s i hs hs3 hi]
      by_cases hl : i + s < 4
      · rw [ite_eq_left hl, h7 (i + s) (by omega) (by omega),
          show h + 4 * j + (i + s) - s = h + 4 * j + i by omega]
      · rw [ite_eq_right hl, g2 (i + s - 4) (by omega),
          show h + 4 * j + 4 + (i + s - 4) - s = h + 4 * j + i by omega]
    rw [K7 a4 (by decide), a4_6, add_lit_zero, copyBytes_word (by omega) hw8,
      show h + 4 * j + 4 = h + 4 * (j + 1) by omega] at u8
    obtain ⟨n9, d9, u9⟩ := u8.aluImm hcj1 mcy_at_f0 (off' := 0xF2) (by decide)
    have g9 : reg n9 a4 = dst + BitVec.ofNat 32 (h + 4 * (j + 1)) := by
      rw [u9.upd_eq (by decide), K7 a4 (by decide), a4_6]
      show dst + BitVec.ofNat 32 (h + 4 * j) + BitVec.ofNat 32 4 = _
      rw [add_ofNat_assoc]; congr 2
    have K9 := u9.upd_ne u7'.zero
    have u9' : St (copyBytes B dst src (h + 4 * (j + 1))) base n9 0xF2 (reg n9) := u9.self
    have t4_9 : reg n9 (29 : Fin 32) = dst + BitVec.ofNat 32 (h + 4 * j + 8) := by
      rw [K9 _ (by decide), g7]
    have a3_9 : reg n9 a3 = dst + BitVec.ofNat 32 (h + 4 * w) := by
      rw [K9 a3 (by decide), K7 a3 (by decide), K6 a3 (by decide), K5 a3 (by decide), K4 a3 (by decide),
        K3 a3 (by decide), K2 a3 (by decide), K1 a3 (by decide), h3]
    have t1_9 : reg n9 (6 : Fin 32) = sb + BitVec.ofNat 32 (4 * (j + 1)) := by
      rw [K9 _ (by decide), K7 _ (by decide), K6 _ (by decide), K5 _ (by decide), u4.upd_eq (by decide),
        K3 _ (by decide), K2 _ (by decide), K1 _ (by decide), h6]
      show sb + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 4 = _
      rw [add_ofNat_assoc]; congr 2
    have a7_9 : ∀ i, s ≤ i → i < 4 → (reg n9 (17 : Fin 32)).extractLsb' (8 * i) 8 =
        B (src + BitVec.ofNat 32 (h + 4 * (j + 1) + i - s)) := fun i _ hi => by
      rw [K9 _ (by decide), K7 _ (by decide), K6 _ (by decide), K5 _ (by decide), K4 _ (by decide),
        K3 _ (by decide), g2 i hi, show h + 4 * j + 4 + i - s = h + 4 * (j + 1) + i - s by omega]
    have a6_9 : reg n9 a6 = BitVec.ofNat 32 (8 * s) := by
      rw [K9 a6 (by decide), K7 a6 (by decide), K6 a6 (by decide), K5 a6 (by decide), K4 a6 (by decide),
        K3 a6 (by decide), a6_2]
    have t2_9 : reg n9 (7 : Fin 32) = BitVec.ofNat 32 (32 - 8 * s) := by
      rw [K9 _ (by decide), K7 _ (by decide), K6 _ (by decide), K5 _ (by decide), t2_4]
    have frame : ∀ r, r ≠ a4 → r ≠ (6 : Fin 32) → r ≠ (17 : Fin 32) → r ≠ (28 : Fin 32) →
        r ≠ (29 : Fin 32) → reg n9 r = reg n r := fun r q4 q6 q7 q28 q29 => by
      rw [K9 r q4, K7 r q29, K6 r q28, K5 r q29, K4 r q6, K3 r q28, K2 r q7, K1 r q28]
    have ult := ult_ofNat (dst := dst) (a := h + 4 * j + 8) (b := h + 4 * w) (by omega) (by omega)
    have c9 : Steps n n9 := .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7
      (.cons d8 (.single d9))))))))
    by_cases hlt : j + 2 < w
    · obtain ⟨n10, d10, u10⟩ := u9'.taken hcj1 0xD4 mcy_at_f2 (by decide) (by
        simp only [branchTaken]; rw [t4_9, a3_9, ult]; exact decide_eq_true (by omega))
      obtain ⟨n11, c11, u11, q4, q6, q7, f11⟩ := ih (j + 1) n10 (by omega) (by omega) u10.self
        (by rw [u10.regs, g9]) (by rw [u10.regs, t1_9]) (fun i h1 h2 => by rw [u10.regs, a7_9 i h1 h2])
        (by rw [u10.regs, a6_9]) (by rw [u10.regs, t2_9]) (by rw [u10.regs, a3_9])
      refine ⟨n11, c9.trans (.cons d10 c11), u11, q4, q6, q7, fun r r4 r6 r7 r28 r29 => ?_⟩
      rw [f11 r r4 r6 r7 r28 r29, u10.regs, frame r r4 r6 r7 r28 r29]
    · have hj : j + 1 = w - 1 := by omega
      obtain ⟨n10, d10, u10⟩ := u9'.notTaken hcj1 0xF6 mcy_at_f2 (by decide) (by
        simp only [branchTaken]; rw [t4_9, a3_9, ult]; exact decide_eq_false (by omega))
      rw [hj] at u10 g9 t1_9 a7_9
      refine ⟨n10, c9.trans (.single d10), u10.self, ?_, ?_, fun i h1 h2 => ?_, fun r r4 r6 r7 r28 r29 => ?_⟩
      · rw [u10.regs, g9]
      · rw [u10.regs, t1_9]
      · rw [u10.regs, a7_9 i h1 h2]
      · rw [u10.regs, frame r r4 r6 r7 r28 r29]

/-- A store outside both buffers commutes with the copy. -/
theorem copyBytes_store8 {M : Word → BitVec 8} {dst src a : Word} {v : BitVec 8} {n k : Nat}
    (hd : Sep dst n a 1) (hs : Sep src n a 1) (hk : k ≤ n) :
    memStore8 (copyBytes M dst src k) a v = copyBytes (memStore8 M a v) dst src k := by
  funext x
  unfold memStore8 copyBytes
  dsimp only
  by_cases hx : x = a
  · subst hx
    have : ¬ (x - dst).toNat < k := fun hlt => by
      have e := sub_eq_ofNat (k := (x - dst).toNat) (x - dst).isLt rfl
      have := hd (x - dst).toNat (by omega) 0 (by decide)
      rw [add_ofNat_zero] at this
      exact this e.symm
    rw [ite_eq_left rfl, ite_eq_right this, ite_eq_left rfl]
  · rw [ite_eq_right hx]
    by_cases hlt : (x - dst).toNat < k
    · rw [ite_eq_left hlt, ite_eq_left hlt]
      have hne : src + (x - dst) ≠ a := by
        have := hs (x - dst).toNat (by omega) 0 (by decide)
        rw [add_ofNat_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
        exact this
      rw [ite_eq_right hne]
    · rw [ite_eq_right hlt, ite_eq_right hlt, ite_eq_right hx]

/-- Bytes outside a region keep the copy's value when the copy reads from
memory that differs from `M` only inside that region. -/
theorem copyBytes_congr {M B : Word → BitVec 8} {dst src F x : Word} {n : Nat} {l : Nat}
    (hB : ∀ y, Sep F l y 1 → B y = M y) (hs : Sep F l src n) (hx : Sep F l x 1) :
    copyBytes B dst src n x = copyBytes M dst src n x := by
  unfold copyBytes
  by_cases hlt : (x - dst).toNat < n
  · rw [ite_eq_left hlt, ite_eq_left hlt]
    apply hB
    have := hs.subR (c := (x - dst).toNat) (l := 1) (by omega)
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  · rw [ite_eq_right hlt, ite_eq_right hlt]; exact hB x hx

/-- From 0x166, with `q` bytes copied and fewer than 4 left, the compiled
`memcpy` copies the rest one byte at a time, pops its frame, and returns. -/
theorem memcpy_tail {B : Word → BitVec 8} {base dst src : Word} {h w N : Nat} (n : Machine)
    (hc : ∀ j, j ≤ N → CodeIn (copyBytes B dst src j) base memcpyBodyCode)
    (hhw : h + 4 * w ≤ N) (hdiv : 4 * w = (N - h) / 4 * 4)
    (hhN : h ≤ N) (hwrap : dst.toNat + N < 2 ^ 32)
    (hsrc : ∀ j, j < N → ∀ k, k ≤ N →
      copyBytes B dst src k (src + BitVec.ofNat 32 j) = B (src + BitVec.ofNat 32 j))
    (s : St (copyBytes B dst src (h + 4 * w)) base n 0x166 (reg n))
    (ha1 : reg n a1 = src + BitVec.ofNat 32 h) (ha5 : reg n a5 = BitVec.ofNat 32 (4 * w))
    (ha2 : reg n a2 = BitVec.ofNat 32 (N - h)) (ha3 : reg n a3 = dst + BitVec.ofNat 32 (h + 4 * w)) :
    ∃ m', Steps n m' ∧ m'.pc = (reg n ra + 0) &&& ~~~1 ∧ m'.mem = copyBytes B dst src N ∧
      reg m' sp = reg n sp + 0x10 ∧
      ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ sp → reg m' r = reg n r := by
  let q := h + 4 * w
  have hcq := hc q hhw
  have hcN := hc N (Nat.le_refl N)
  obtain ⟨n1, d1, u1⟩ := s.alu hcq mcy_at_166 (off' := 0x168) (by decide)
  have g1 : reg n1 a1 = src + BitVec.ofNat 32 q := by
    rw [u1.upd_eq (by decide), ha1, ha5]; exact add_ofNat_assoc src h (4 * w)
  have K1 := u1.upd_ne s.zero
  have u1' : St (copyBytes B dst src q) base n1 0x168 (reg n1) := u1.self
  obtain ⟨n2, d2, u2⟩ := u1'.aluImm hcq mcy_at_168 (off' := 0x16A) (by decide)
  have g2 : reg n2 a2 = BitVec.ofNat 32 (N - q) := by
    rw [u2.upd_eq (by decide), K1 a2 (by decide), ha2, and3_val (by omega)]
    congr 1; show (N - h) % 4 = N - (h + 4 * w); omega
  have K2 := u2.upd_ne u1'.zero
  have u2' : St (copyBytes B dst src q) base n2 0x16A (reg n2) := u2.self
  obtain ⟨n3, d3, u3⟩ := u2'.alu hcq mcy_at_16a (off' := 0x16E) (by decide)
  have a3_2 : reg n2 a3 = dst + BitVec.ofNat 32 q := by rw [K2 a3 (by decide), K1 a3 (by decide), ha3]
  have g3 : reg n3 a4 = dst + BitVec.ofNat 32 N := by
    rw [u3.upd_eq (by decide), a3_2, g2]
    show dst + BitVec.ofNat 32 q + BitVec.ofNat 32 (N - q) = _
    rw [add_ofNat_assoc, show q + (N - q) = N by omega]
  have K3 := u3.upd_ne u2'.zero
  have u3' : St (copyBytes B dst src q) base n3 0x16E (reg n3) := u3.self
  have a3_3 : reg n3 a3 = dst + BitVec.ofNat 32 q := by rw [K3 a3 (by decide), a3_2]
  have Kf : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg n3 r = reg n r := fun r q1 q2 _ q4 => by
    rw [K3 r q4, K2 r q2, K1 r q1]
  have ult := ult_ofNat (dst := dst) (a := q) (b := N) (by omega) (by omega)
  -- Both cases reach 0x182 with the copy done.
  have T : ∃ n5, Steps n n5 ∧ St (copyBytes B dst src N) base n5 0x182 (reg n5) ∧
      ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg n5 r = reg n r := by
    have c3 : Steps n n3 := .cons d1 (.cons d2 (.single d3))
    by_cases ht : q = N
    · obtain ⟨n4, d4, u4⟩ := u3'.taken hcq 0x182 mcy_at_16e (by decide) (by
        simp only [branchTaken]; rw [a3_3, g3, ult]; simp only [Bool.not_eq_true']
        exact decide_eq_false (by omega))
      rw [ht] at u4
      exact ⟨n4, c3.trans (.single d4), u4.self, fun r q1 q2 q3 q4 => by rw [u4.regs, Kf r q1 q2 q3 q4]⟩
    · obtain ⟨n4, d4, u4⟩ := u3'.notTaken hcq 0x172 mcy_at_16e (by decide) (by
        simp only [branchTaken]; rw [a3_3, g3, ult]; simp only [Bool.not_eq_false']
        exact decide_eq_true (by omega))
      obtain ⟨n5, c5, u5, _, _, _, f5⟩ := copy_loop (o := 0x172) (e := N) (cnt := a2) (dp := a3) (sp := a1)
        (tmp := a4) hc (by omega) (by decide) hsrc mcy_at_172 mcy_at_176 mcy_at_178 mcy_at_17c mcy_at_17e
        mcy_at_180 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (N - q) q n4 (by omega) (by omega) u4.self
        (by rw [u4.regs, K3 a2 (by decide), g2]) (by rw [u4.regs, a3_3])
        (by rw [u4.regs, K3 a1 (by decide), K2 a1 (by decide), g1])
      exact ⟨n5, c3.trans (.cons d4 c5), u5, fun r q1 q2 q3 q4 => by
        rw [f5 r q2 q3 q1 q4, u4.regs, Kf r q1 q2 q3 q4]⟩
  obtain ⟨n5, c5, u5, f5⟩ := T
  obtain ⟨n6, d6, u6⟩ := u5.aluImm hcN mcy_at_182 (off' := 0x184) (by decide)
  have K6 := u6.upd_ne u5.zero
  have u6' : St (copyBytes B dst src N) base n6 0x184 (reg n6) := u6.self
  obtain ⟨n7, d7, pc7, mem7, regs7⟩ := u6'.jalr hcN mcy_at_184
  refine ⟨n7, c5.trans (.cons d6 (.single d7)), ?_, mem7, ?_, fun r q1 q2 q3 q4 qs => ?_⟩
  · rw [pc7, K6 ra (by decide), f5 ra (by decide) (by decide) (by decide) (by decide)]
  · rw [regs7, u6.upd_eq (by decide), f5 sp (by decide) (by decide) (by decide) (by decide)]; rfl
  · rw [regs7, K6 r qs, f5 r q1 q2 q3 q4]

theorem copyBytes_store32 {M : Word → BitVec 8} {dst src a v : Word} {n k : Nat}
    (hd : Sep dst n a 4) (hs : Sep src n a 4) (hk : k ≤ n) :
    memStore32 (copyBytes M dst src k) a v = copyBytes (memStore32 M a v) dst src k := by
  have p : ∀ c, c < 4 → Sep dst n (a + BitVec.ofNat 32 c) 1 ∧ Sep src n (a + BitVec.ofNat 32 c) 1 :=
    fun c hc => ⟨hd.subR (c := c) (l := 1) (by omega), hs.subR (c := c) (l := 1) (by omega)⟩
  have p0 : Sep dst n a 1 ∧ Sep src n a 1 := by
    have := p 0 (by decide); rwa [add_ofNat_zero] at this
  unfold memStore32
  rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, show (2 : Word) = BitVec.ofNat 32 2 from rfl,
    show (3 : Word) = BitVec.ofNat 32 3 from rfl]
  rw [copyBytes_store8 p0.1 p0.2 hk, copyBytes_store8 (p 1 (by decide)).1 (p 1 (by decide)).2 hk,
    copyBytes_store8 (p 2 (by decide)).1 (p 2 (by decide)).2 hk,
    copyBytes_store8 (p 3 (by decide)).1 (p 3 (by decide)).2 hk]

/-- The low 16 bits survive sign extension. The library's `signExtend`
lemmas use `Classical.choice`, so this goes through `ofInt` and `toInt`. -/
theorem signExtend_byte (y : BitVec 16) (k : Nat) (hk : k < 2) :
    (y.signExtend 32).extractLsb' (8 * k) 8 = y.extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat]
  unfold BitVec.signExtend
  rw [BitVec.toNat_ofInt]
  unfold BitVec.toInt
  have hy := y.isLt
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;>
  · simp only [Nat.shiftRight_eq_div_pow]
    split <;> omega

theorem ext0_append (a b : BitVec 8) : (a ++ b).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, show decide (i < 8) = true from decide_eq_true hi,
    Bool.true_and, ite_eq_left (show 0 + i < 8 by omega), Nat.zero_add]

theorem ext8_append (a b : BitVec 8) : (a ++ b).extractLsb' 8 8 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, show decide (i < 8) = true from decide_eq_true hi,
    Bool.true_and, ite_eq_right (show ¬ (8 + i < 8) by omega), show 8 + i - 8 = i by omega]

theorem signExtend_lo (a b : BitVec 8) : ((a ++ b).signExtend 32).extractLsb' 0 8 = b :=
  (signExtend_byte (a ++ b) 0 (by decide)).trans (ext0_append a b)

theorem signExtend_hi (a b : BitVec 8) : ((a ++ b).signExtend 32).extractLsb' 8 8 = a :=
  (signExtend_byte (a ++ b) 1 (by decide)).trans (ext8_append a b)

theorem or_small {x : Word} (hx : x.toNat % 4 = 0) {s : Nat} (hs : s < 4) :
    aluEval .or x (BitVec.ofNat 32 s) = x + BitVec.ofNat 32 s := by
  show x ||| BitVec.ofNat 32 s = _
  rw [Sha256.add_disj]
  intro i hi
  rw [BitVec.getLsbD_ofNat, ← BitVec.testBit_toNat]
  by_cases h2 : i < 2
  · have := Nat.testBit_mod_two_pow x.toNat 2 i
    rw [show 2 ^ 2 = 4 from rfl, hx, Nat.zero_testBit, show decide (i < 2) = true from decide_eq_true h2,
      Bool.true_and] at this
    rw [← this, Bool.false_and]
  · rw [Nat.testBit_lt_two_pow (x := s) (Nat.lt_of_lt_of_le hs (by
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))), Bool.and_false, Bool.and_false]

/-- The code stays in place under any copy that reads from memory equal to
`M0` outside the frame. -/
theorem code_copy {M0 B : Word → BitVec 8} {dst src base F : Word} {N k : Nat} {code : List Nat}
    (hc : CodeIn M0 base code) (hDC : Sep dst N base code.length) (hFC : Sep F 16 base code.length)
    (hB : ∀ y, Sep F 16 y 1 → B y = M0 y) (hk : k ≤ N) : CodeIn (copyBytes B dst src k) base code :=
  fun i hi => by
    rw [copyBytes_sep (hDC.subR (c := i) (l := 1) (by omega)) hk,
      hB _ (hFC.subR (c := i) (l := 1) (by omega))]
    exact hc i hi

/-- The source bytes stay in place under the copy when the buffers don't
overlap. -/
theorem src_copy {B : Word → BitVec 8} {dst src : Word} {N : Nat} (hsep : Sep dst N src N) :
    ∀ j, j < N → ∀ k, k ≤ N → copyBytes B dst src k (src + BitVec.ofNat 32 j) = B (src + BitVec.ofNat 32 j) :=
  fun j hj k hk => copyBytes_sep (hsep.subR (c := j) (l := 1) (by omega)) hk

/-- What `memcpy` needs of its call: its code at `base`, the `N`-byte
buffers at `dst` and `src` apart from each other, from its code, and from
its 16-byte stack frame at `F`, and nothing past the top of memory. -/
structure McEnv (M0 : Word → BitVec 8) (base dst src F : Word) (N : Nat) : Prop where
  code : CodeIn M0 base memcpyBodyCode
  hDC : Sep dst N base memcpyBodyCode.length
  hFC : Sep F 16 base memcpyBodyCode.length
  hdF : Sep dst N F 16
  hsF : Sep src N F 16
  hsep : Sep dst N src N
  hF : F.toNat % 4 = 0
  hFw : F.toNat + 16 ≤ 2 ^ 32
  hdw : dst.toNat + N < 2 ^ 32
  hsw : src.toNat + N < 2 ^ 32

theorem McEnv.codeB {M0 B : Word → BitVec 8} {base dst src F : Word} {N k : Nat}
    (E : McEnv M0 base dst src F N) (hB : ∀ y, Sep F 16 y 1 → B y = M0 y) (hk : k ≤ N) :
    CodeIn (copyBytes B dst src k) base memcpyBodyCode :=
  code_copy E.code E.hDC E.hFC hB hk

theorem McEnv.srcB {M0 B : Word → BitVec 8} {base dst src F : Word} {N : Nat}
    (E : McEnv M0 base dst src F N) (hB : ∀ y, Sep F 16 y 1 → B y = M0 y) {j k : Nat} (hj : j < N)
    (hk : k ≤ N) : copyBytes B dst src k (src + BitVec.ofNat 32 j) = M0 (src + BitVec.ofNat 32 j) := by
  rw [src_copy E.hsep j hj k hk, hB _ (E.hsF.symm.subR (c := j) (l := 1) (by omega))]

theorem McEnv.frameB {M0 B : Word → BitVec 8} {base dst src F : Word} {N k : Nat}
    (E : McEnv M0 base dst src F N) {i : Nat} (hi : i < 16) (hk : k ≤ N) :
    copyBytes B dst src k (F + BitVec.ofNat 32 i) = B (F + BitVec.ofNat 32 i) :=
  copyBytes_sep (E.hdF.subR (c := i) (l := 1) (by omega)) hk

theorem McEnv.store8 {M0 : Word → BitVec 8} {base dst src F : Word} {N : Nat}
    (E : McEnv M0 base dst src F N) {B : Word → BitVec 8} {i k : Nat} {v : BitVec 8} (hi : i < 16)
    (hk : k ≤ N) :
    memStore8 (copyBytes B dst src k) (F + BitVec.ofNat 32 i) v =
      copyBytes (memStore8 B (F + BitVec.ofNat 32 i) v) dst src k :=
  copyBytes_store8 (E.hdF.subR (c := i) (l := 1) (by omega)) (E.hsF.subR (c := i) (l := 1) (by omega)) hk

theorem frame_ne (F : Word) {a b : Nat} (ha : a < 16) (hb : b < 16) (h : a ≠ b) :
    F + BitVec.ofNat 32 a ≠ F + BitVec.ofNat 32 b :=
  add_ofNat_ne F (by omega) (by omega) h

theorem frame_out {F y : Word} (hy : Sep F 16 y 1) {a : Nat} (ha : a < 16) : y ≠ F + BitVec.ofNat 32 a := by
  intro e; have := hy a ha 0 (by decide); rw [add_ofNat_zero] at this; exact this e.symm

/-- The misaligned path's start for a source 1 byte past a 4-byte boundary:
it zeroes the frame word at `F + 12`, copies the next 3 source bytes into its
top 3 bytes with `sb` and `sh`, loads the word, and sets up the splice. -/
theorem mis_head1 {M0 : Word → BitVec 8} {base dst src F : Word} {N h w : Nat}
    (E : McEnv M0 base dst src F N) (n : Machine) (hhw : h + 4 * w ≤ N) (hw : 2 ≤ w)
    (hal : (src + BitVec.ofNat 32 h).toNat % 4 = 1)
    (s0 : St (copyBytes M0 dst src h) base n 0x40 (reg n))
    (ra1 : reg n a1 = src + BitVec.ofNat 32 h) (rt0 : reg n (5 : Fin 32) = BitVec.ofNat 32 1)
    (rsp : reg n sp = F) (ra4 : reg n a4 = dst + BitVec.ofNat 32 h)
    (ra3 : reg n a3 = dst + BitVec.ofNat 32 (h + 4 * w)) :
    ∃ n' B, Steps n n' ∧ (∀ y, Sep F 16 y 1 → B y = M0 y) ∧
      St (copyBytes B dst src h) base n' 0xD4 (reg n') ∧
      reg n' (6 : Fin 32) = src + BitVec.ofNat 32 h - BitVec.ofNat 32 1 ∧
      (∀ i, 1 ≤ i → i < 4 → (reg n' (17 : Fin 32)).extractLsb' (8 * i) 8 =
        B (src + BitVec.ofNat 32 (h + 4 * 0 + i - 1))) ∧
      reg n' a6 = BitVec.ofNat 32 (8 * 1) ∧ reg n' (7 : Fin 32) = BitVec.ofNat 32 (32 - 8 * 1) ∧
      ∀ r, r ≠ a6 → r ≠ (17 : Fin 32) → r ≠ (6 : Fin 32) → r ≠ (7 : Fin 32) → reg n' r = reg n r := by
  have hN : h + 3 < N := by omega
  have hc0 := E.codeB (B := M0) (fun _ _ => rfl) (k := h) (by omega)
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc0 mcy_at_40 (off' := 0x42) (by decide)
  have K1 := u1.upd_ne s0.zero
  have u1' : St (copyBytes M0 dst src h) base n1 0x42 (reg n1) := u1.self
  obtain ⟨n2, d2, u2⟩ := u1'.aluImm hc0 mcy_at_42 (off' := 0x44) (by decide)
  have g2 : reg n2 (17 : Fin 32) = 4 := by rw [u2.upd_eq (by decide), u1'.zero]; rfl
  have K2 := u2.upd_ne u1'.zero
  have u2' : St (copyBytes M0 dst src h) base n2 0x44 (reg n2) := u2.self
  obtain ⟨n3, d3, u3⟩ := u2'.alu hc0 mcy_at_44 (off' := 0x48) (by decide)
  have t0_2 : reg n2 (5 : Fin 32) = BitVec.ofNat 32 1 := by rw [K2 _ (by decide), K1 _ (by decide), rt0]
  have g3 : reg n3 (17 : Fin 32) = 3 := by rw [u3.upd_eq (by decide), g2, t0_2]; rfl
  have K3 := u3.upd_ne u2'.zero
  have u3' : St (copyBytes M0 dst src h) base n3 0x48 (reg n3) := u3.self
  obtain ⟨n4, d4, u4⟩ := u3'.aluImm hc0 mcy_at_48 (off' := 0x4C) (by decide)
  have sp3 : reg n3 sp = F := by rw [K3 sp (by decide), K2 sp (by decide), K1 sp (by decide), rsp]
  have g4 : reg n4 (6 : Fin 32) = F + BitVec.ofNat 32 12 := by rw [u4.upd_eq (by decide), sp3]; rfl
  have K4 := u4.upd_ne u3'.zero
  have u4' : St (copyBytes M0 dst src h) base n4 0x4C (reg n4) := u4.self
  obtain ⟨n5, d5, u5⟩ := u4'.aluImm hc0 mcy_at_4c (off' := 0x50) (by decide)
  have g5 : reg n5 (7 : Fin 32) = 1 := by rw [u5.upd_eq (by decide), K4 _ (by decide), g3]; rfl
  have K5 := u5.upd_ne u4'.zero
  have u5' : St (copyBytes M0 dst src h) base n5 0x50 (reg n5) := u5.self
  have sp5 : reg n5 sp = F := by rw [K5 sp (by decide), K4 sp (by decide), sp3]
  have al12 : (F + BitVec.ofNat 32 12).toNat % 4 = 0 := aligned_add E.hF (k := 12) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5'.sw hc0 mcy_at_50 (off' := 0x52) (by decide)
    (by rw [sp5]; exact al12)
  rw [sp5, show F + (0xC : Word) = F + BitVec.ofNat 32 12 from rfl,
    copyBytes_store32 (E.hdF.subR (c := 12) (l := 4) (by decide))
      (E.hsF.subR (c := 12) (l := 4) (by decide)) (by omega : h ≤ N)] at u6
  let B1 := memStore32 M0 (F + BitVec.ofNat 32 12) (reg n5 x0)
  have hB1 : ∀ y, Sep F 16 y 1 → B1 y = M0 y := fun y hy =>
    memStore32_get_sep (fun i hi j hj e => hy (12 + i) (by omega) j hj (by
      rw [← add_ofNat_assoc]; exact e))
  have hc1 := E.codeB hB1 (k := h) (by omega)
  obtain ⟨n7, d7, u7⟩ := u6.alu hc1 mcy_at_52 (off' := 0x56) (by decide)
  have g7 : reg n7 (6 : Fin 32) = F + BitVec.ofNat 32 13 := by
    rw [u7.upd_eq (by decide), K5 _ (by decide), g4, K5 _ (by decide), K4 _ (by decide), K3 _ (by decide),
      t0_2, or_small al12 (by decide), add_ofNat_assoc]
  have K7 := u7.upd_ne u5'.zero
  have u7' : St (copyBytes B1 dst src h) base n7 0x56 (reg n7) := u7.self
  obtain ⟨n8, d8, u8⟩ := u7'.taken hc1 0x9A mcy_at_56 (by decide) (by
    simp only [branchTaken]; rw [K7 _ (by decide), g5, u7'.zero]; decide)
  obtain ⟨n9, d9, u9⟩ := u8.lbu hc1 mcy_at_9a (off' := 0x9E) (by decide)
  let b0 := M0 (src + BitVec.ofNat 32 h)
  have a1_7 : reg n7 a1 = src + BitVec.ofNat 32 h := by
    rw [K7 a1 (by decide), K5 a1 (by decide), K4 a1 (by decide), K3 a1 (by decide), K2 a1 (by decide),
      K1 a1 (by decide), ra1]
  have g9 : reg n9 a6 = b0.zeroExtend 32 := by
    rw [u9.upd_eq (by decide), a1_7, add_lit_zero, E.srcB hB1 (by omega) (by omega)]
  have K9 := u9.upd_ne u7'.zero
  have u9' : St (copyBytes B1 dst src h) base n9 0x9E (reg n9) := u9.self
  obtain ⟨n10, d10, u10⟩ := u9'.sb hc1 mcy_at_9e (off' := 0xA2) (by decide)
  have zb : (b0.zeroExtend 32).extractLsb' 0 8 = b0 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi] <;> omega
  rw [K9 _ (by decide), g7, add_lit_zero, g9, zb, E.store8 (by decide) (by omega)] at u10
  let B2 := memStore8 B1 (F + BitVec.ofNat 32 13) b0
  have hB2 : ∀ y, Sep F 16 y 1 → B2 y = M0 y := fun y hy => by
    show memStore8 B1 _ _ y = _; rw [memStore8_ne (frame_out hy (by decide)), hB1 y hy]
  have hc2 := E.codeB hB2 (k := h) (by omega)
  obtain ⟨n11, d11, u11⟩ := u10.aluImm hc2 mcy_at_a2 (off' := 0xA4) (by decide)
  have K11 := u11.upd_ne u9'.zero
  have u11' : St (copyBytes B2 dst src h) base n11 0xA4 (reg n11) := u11.self
  obtain ⟨n12, d12, u12⟩ := u11'.aluImm hc2 mcy_at_a4 (off' := 0xA8) (by decide)
  have g12 : reg n12 (17 : Fin 32) = 2 := by
    rw [u12.upd_eq (by decide), K11 _ (by decide), K9 _ (by decide), K7 _ (by decide), K5 _ (by decide),
      K4 _ (by decide), g3]; rfl
  have K12 := u12.upd_ne u11'.zero
  have u12' : St (copyBytes B2 dst src h) base n12 0xA8 (reg n12) := u12.self
  obtain ⟨n13, d13, u13⟩ := u12'.notTaken hc2 0xAC mcy_at_a8 (by decide) (by
    simp only [branchTaken]; rw [g12, u12'.zero]; decide)
  obtain ⟨n14, d14, u14⟩ := u13.alu hc2 mcy_at_ac (off' := 0xB0) (by decide)
  have a6_12 : reg n12 a6 = 1 := by
    rw [K12 a6 (by decide), u11.upd_eq (by decide), u9'.zero]; rfl
  have a1_12 : reg n12 a1 = src + BitVec.ofNat 32 h := by
    rw [K12 a1 (by decide), K11 a1 (by decide), K9 a1 (by decide), a1_7]
  have g14 : reg n14 (17 : Fin 32) = src + BitVec.ofNat 32 (h + 1) := by
    rw [u14.upd_eq (by decide), a1_12, a6_12]; exact add_ofNat_assoc src h 1
  have K14 := u14.upd_ne u12'.zero
  have u14' : St (copyBytes B2 dst src h) base n14 0xB0 (reg n14) := u14.self
  have al2 : (reg n14 (17 : Fin 32) + 0).toNat % 2 = 0 := by
    rw [g14, add_lit_zero, ← add_ofNat_assoc]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨n15, d15, u15⟩ := u14'.lh hc2 mcy_at_b0 (off' := 0xB4) (by decide) al2
  let lo := M0 (src + BitVec.ofNat 32 (h + 1))
  let hi := M0 (src + BitVec.ofNat 32 (h + 2))
  have g15 : reg n15 (17 : Fin 32) = (hi ++ lo).signExtend 32 := by
    rw [u15.upd_eq (by decide), g14, add_lit_zero, show (1 : Word) = BitVec.ofNat 32 1 from rfl,
      add_ofNat_assoc, E.srcB hB2 (by omega) (by omega), E.srcB hB2 (by omega) (by omega)]
  have K15 := u15.upd_ne u14'.zero
  have u15' : St (copyBytes B2 dst src h) base n15 0xB4 (reg n15) := u15.self
  obtain ⟨n16, d16, u16⟩ := u15'.alu hc2 mcy_at_b4 (off' := 0xB6) (by decide)
  have g16 : reg n16 a6 = F + BitVec.ofNat 32 14 := by
    rw [u16.upd_eq (by decide), K15 a6 (by decide), K14 a6 (by decide), a6_12, K15 _ (by decide),
      K14 _ (by decide), K12 _ (by decide), K11 _ (by decide), K9 _ (by decide), g7]
    show (1 : Word) + (F + BitVec.ofNat 32 13) = _
    rw [BitVec.add_comm (1 : Word), show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc]
  have K16 := u16.upd_ne u15'.zero
  have u16' : St (copyBytes B2 dst src h) base n16 0xB6 (reg n16) := u16.self
  obtain ⟨n17, d17, u17⟩ := u16'.sh hc2 mcy_at_b6 (off' := 0xBA) (by decide) (by
    rw [g16, add_lit_zero, BitVec.toNat_add, BitVec.toNat_ofNat]; have := E.hF; omega)
  rw [g16, add_lit_zero, K16 _ (by decide), g15, signExtend_lo, signExtend_hi,
    show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc, E.store8 (by decide) (by omega),
    E.store8 (by decide) (by omega)] at u17
  let B3 := memStore8 (memStore8 B2 (F + BitVec.ofNat 32 14) lo) (F + BitVec.ofNat 32 (14 + 1)) hi
  have hB3 : ∀ y, Sep F 16 y 1 → B3 y = M0 y := fun y hy => by
    show memStore8 (memStore8 B2 _ _) _ _ y = _
    rw [memStore8_ne (frame_out hy (by decide)), memStore8_ne (frame_out hy (by decide)), hB2 y hy]
  have hc3 := E.codeB hB3 (k := h) (by omega)
  obtain ⟨n18, d18, u18⟩ := u17.lw hc3 mcy_at_ba (off' := 0xBC) (by decide) (by
    rw [K16 sp (by decide), K15 sp (by decide), K14 sp (by decide), K12 sp (by decide), K11 sp (by decide),
      K9 sp (by decide), K7 sp (by decide), sp5]; exact al12)
  have sp16 : reg n16 sp = F := by
    rw [K16 sp (by decide), K15 sp (by decide), K14 sp (by decide), K12 sp (by decide), K11 sp (by decide),
      K9 sp (by decide), K7 sp (by decide), sp5]
  have g18 : ∀ i, 1 ≤ i → i < 4 → (reg n18 (17 : Fin 32)).extractLsb' (8 * i) 8 =
      B3 (src + BitVec.ofNat 32 (h + 4 * 0 + i - 1)) := fun i h1 h4 => by
    rw [u18.upd_eq (by decide), sp16, show F + (0xC : Word) = F + BitVec.ofNat 32 12 from rfl,
      load_byte _ _ i h4, add_ofNat_assoc, E.frameB (by omega) (by omega), hB3 _ (E.hsF.symm.subR
        (c := h + 4 * 0 + i - 1) (l := 1) (by omega))]
    show memStore8 (memStore8 (memStore8 B1 _ b0) _ lo) _ hi _ = _
    rcases (show i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl
    · rw [memStore8_ne (frame_ne F (by decide) (by decide) (by decide)),
        memStore8_ne (frame_ne F (by decide) (by decide) (by decide)), memStore8_same]; rfl
    · rw [memStore8_ne (frame_ne F (by decide) (by decide) (by decide)), memStore8_same]; rfl
    · rw [memStore8_same]; rfl
  have K18 := u18.upd_ne u16'.zero
  have Kall : ∀ r, r ≠ a6 → r ≠ (17 : Fin 32) → r ≠ (6 : Fin 32) → r ≠ (7 : Fin 32) →
      reg n18 r = reg n r := fun r q6 q17 q1 q2 => by
    rw [K18 r q17, K16 r q6, K15 r q17, K14 r q17, K12 r q17, K11 r q6, K9 r q6, K7 r q1, K5 r q2, K4 r q1,
      K3 r q17, K2 r q17, K1 r q6]
  have u18' : St (copyBytes B3 dst src h) base n18 0xBC (reg n18) := u18.self
  obtain ⟨n19, d19, u19⟩ := u18'.aluImm hc3 mcy_at_bc (off' := 0xC0) (by decide)
  have g19 : reg n19 (7 : Fin 32) = dst + BitVec.ofNat 32 (h + 4) := by
    rw [u19.upd_eq (by decide), Kall a4 (by decide) (by decide) (by decide) (by decide), ra4]
    exact add_ofNat_assoc dst h 4
  have K19 := u19.upd_ne u18'.zero
  have u19' : St (copyBytes B3 dst src h) base n19 0xC0 (reg n19) := u19.self
  obtain ⟨n20, d20, u20⟩ := u19'.aluImm hc3 mcy_at_c0 (off' := 0xC4) (by decide)
  have t0_18 : reg n18 (5 : Fin 32) = BitVec.ofNat 32 1 := by
    rw [Kall _ (by decide) (by decide) (by decide) (by decide), rt0]
  have g20 : reg n20 a6 = BitVec.ofNat 32 (8 * 1) := by
    rw [u20.upd_eq (by decide), K19 _ (by decide), t0_18]; rfl
  have K20 := u20.upd_ne u19'.zero
  have u20' : St (copyBytes B3 dst src h) base n20 0xC4 (reg n20) := u20.self
  obtain ⟨n21, d21, u21⟩ := u20'.alu hc3 mcy_at_c4 (off' := 0xC8) (by decide)
  have g21 : reg n21 (6 : Fin 32) = src + BitVec.ofNat 32 h - BitVec.ofNat 32 1 := by
    rw [u21.upd_eq (by decide), K20 a1 (by decide), K19 a1 (by decide),
      Kall a1 (by decide) (by decide) (by decide) (by decide), ra1, K20 _ (by decide), K19 _ (by decide),
      t0_18]; rfl
  have K21 := u21.upd_ne u20'.zero
  have u21' : St (copyBytes B3 dst src h) base n21 0xC8 (reg n21) := u21.self
  have a3_21 : reg n21 a3 = dst + BitVec.ofNat 32 (h + 4 * w) := by
    rw [K21 a3 (by decide), K20 a3 (by decide), K19 a3 (by decide),
      Kall a3 (by decide) (by decide) (by decide) (by decide), ra3]
  obtain ⟨n22, d22, u22⟩ := u21'.notTaken hc3 0xCC mcy_at_c8 (by decide) (by
    simp only [branchTaken]
    rw [K21 _ (by decide), K20 _ (by decide), g19, a3_21,
      ult_ofNat (by have := E.hdw; omega) (by have := E.hdw; omega)]
    simp only [Bool.not_eq_false']; exact decide_eq_true (by omega))
  obtain ⟨n23, d23, u23⟩ := u22.alu hc3 mcy_at_cc (off' := 0xD0) (by decide)
  have K23 := u23.upd_ne u21'.zero
  have u23' : St (copyBytes B3 dst src h) base n23 0xD0 (reg n23) := u23.self
  obtain ⟨n24, d24, u24⟩ := u23'.aluImm hc3 mcy_at_d0 (off' := 0xD4) (by decide)
  have K24 := u24.upd_ne u23'.zero
  have a6_23 : reg n23 a6 = BitVec.ofNat 32 (8 * 1) := by rw [K23 a6 (by decide), K21 a6 (by decide), g20]
  refine ⟨n24, B3, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
    (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.cons d16 (.cons d17 (.cons d18
    (.cons d19 (.cons d20 (.cons d21 (.cons d22 (.cons d23 (.single d24))))))))))))))))))))))), hB3, u24.self,
    ?_, fun i h1 h4 => ?_, ?_, ?_, fun r q6 q17 q1 q2 => ?_⟩
  · rw [K24 _ (by decide), K23 _ (by decide), g21]
  · rw [K24 _ (by decide), K23 _ (by decide), K21 _ (by decide), K20 _ (by decide), K19 _ (by decide),
      g18 i h1 h4]
  · rw [K24 a6 (by decide), a6_23]
  · rw [u24.upd_eq (by decide), u23.upd_eq (by decide), u21'.zero, K21 a6 (by decide), g20]; rfl
  · rw [K24 r q2, K23 r q2, K21 r q1, K20 r q6, K19 r q2, Kall r q6 q17 q1 q2]

end C3.RV32
