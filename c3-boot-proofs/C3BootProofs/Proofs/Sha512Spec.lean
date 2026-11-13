import C3BootProofs.Proofs.ShaSpec
import C3BootProofs.Spec.Sha512

/-!
# SHA-512's compression function in the form its machine code takes

The SHA-512 counterpart of `ShaSpec`: `Ch` as the sum of its two halves,
`Maj` as `((b ^ c) & a) ^ (b & c)`, `~e` as `e ^ 0xFFFFFFFFFFFFFFFF`, the
working variables after each round (`vs`), and the message schedule's
recurrence (`sched_rec`), all without `Classical.choice`.
-/

namespace C3.Sha512

/-! ## Bit tricks -/

theorem bitw {x y : W64} (h : ∀ i, i < 64 → x.getLsbD i = y.getLsbD i) : x = y :=
  BitVec.eq_of_getLsbD_eq fun i hi => h i hi

theorem ones_bit : ∀ i : Fin 64, (0xFFFFFFFFFFFFFFFF : W64).getLsbD i.val = true := by decide

theorem not_eq_xor (x : W64) : ~~~x = x ^^^ 0xFFFFFFFFFFFFFFFF := by
  rw [BitVec.not_def, BitVec.xor_comm]; rfl

/-- Words with no bit in common never carry when added. -/
theorem carry_disj {x y : W64} (h : ∀ i, i < 64 → (x.getLsbD i && y.getLsbD i) = false) :
    ∀ i, i ≤ 64 → x.toNat % 2 ^ i + y.toNat % 2 ^ i < 2 ^ i
  | 0, _ => by simp only [Nat.pow_zero, Nat.mod_one]; decide
  | i + 1, hi => by
    have hP : 0 < 2 ^ i := Nat.two_pow_pos i
    rw [Nat.pow_succ, Sha256.mod_mul_two _ _ hP, Sha256.mod_mul_two _ _ hP]
    have hx := Nat.toNat_testBit x.toNat i
    have hy := Nat.toNat_testBit y.toNat i
    have hd : (x.toNat.testBit i && y.toNat.testBit i) = false := h i (by omega)
    refine Sha256.bits_lt _ _ _ _ _ (carry_disj h i (by omega)) (Nat.mod_two_eq_zero_or_one _)
      (Nat.mod_two_eq_zero_or_one _) fun ⟨h1, h2⟩ => ?_
    rw [← hx] at h1; rw [← hy] at h2
    revert hd h1 h2
    cases x.toNat.testBit i <;> cases y.toNat.testBit i <;> decide

/-- So their sum is their `or`. -/
theorem add_disj {x y : W64} (h : ∀ i, i < 64 → (x.getLsbD i && y.getLsbD i) = false) :
    x + y = x ||| y := by
  apply bitw; intro i hi
  have hc : BitVec.carry i x y false = false := by
    unfold BitVec.carry
    have := carry_disj h i (by omega)
    simp only [Bool.toNat_false, Nat.add_zero]
    exact decide_eq_false (Nat.not_le.mpr this)
  rw [BitVec.getLsbD_add hi, hc, BitVec.getLsbD_or]
  have := h i hi
  revert this
  cases x.getLsbD i <;> cases y.getLsbD i <;> decide

/-- `Ch` as the compiled code computes it: the sum of `f & e` and `g & ~e`. -/
theorem ch_add (e f g : W64) : ch e f g = (f &&& e) + (g &&& ~~~e) := by
  unfold ch
  rw [not_eq_xor, add_disj]
  · apply bitw; intro i hi
    have := ones_bit ⟨i, hi⟩
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or, this]
    cases e.getLsbD i <;> cases f.getLsbD i <;> cases g.getLsbD i <;> rfl
  · intro i hi
    have := ones_bit ⟨i, hi⟩
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, this]
    cases e.getLsbD i <;> cases f.getLsbD i <;> cases g.getLsbD i <;> rfl

/-- `Maj` as the compiled code computes it. -/
theorem maj_alt (a b c : W64) : maj a b c = ((b ^^^ c) &&& a) ^^^ (b &&& c) := by
  unfold maj
  apply bitw; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

/-! ## Rounds -/

/-- The eight working variables. -/
structure V8 where
  a : W64
  b : W64
  c : W64
  d : W64
  e : W64
  f : W64
  g : W64
  h : W64

def V8.toList (v : V8) : List W64 := [v.a, v.b, v.c, v.d, v.e, v.f, v.g, v.h]

/-- Round `t` of section 6.4.2 step 3, with the schedule as a function. -/
def rnd (w : Nat → W64) (t : Nat) (v : V8) : V8 :=
  ⟨(v.h + bigSigma1 v.e + ch v.e v.f v.g + k[t]! + w t) + (bigSigma0 v.a + maj v.a v.b v.c), v.a, v.b, v.c,
    v.d + (v.h + bigSigma1 v.e + ch v.e v.f v.g + k[t]! + w t), v.e, v.f, v.g⟩

/-- The working variables after `t` rounds. -/
def vs (w : Nat → W64) (v0 : V8) : Nat → V8
  | 0 => v0
  | t + 1 => rnd w t (vs w v0 t)

theorem round_toList (w : Array W64) (v : V8) (t : Nat) :
    round w v.toList t = (rnd (fun t => w[t]!) t v).toList := rfl

theorem foldl_vs (w : Array W64) (v0 : V8) :
    ∀ n, (List.range n).foldl (round w) v0.toList = (vs (fun t => w[t]!) v0 n).toList
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_vs w v0 n]
    rfl

/-! ## The message schedule -/

/-- One step of `schedule`'s fold. -/
def schedStep (w : Array W64) (t : Nat) : Array W64 :=
  w.push (smallSigma1 w[t + 16 - 2]! + w[t + 16 - 7]! + smallSigma0 w[t + 16 - 15]! + w[t + 16 - 16]!)

def schedInit (block : Bytes) : Array W64 := (List.range 16).toArray.map (wordAt block)

theorem schedule_eq (block : Bytes) :
    schedule block = (List.range 64).foldl schedStep (schedInit block) := rfl

theorem getElem!_lt {a : Array W64} {i : Nat} (h : i < a.size) : a[i]! = a[i] := getElem!_pos a i h

theorem push_lt {a : Array W64} {x : W64} {i : Nat} (h : i < a.size) : (a.push x)[i]! = a[i]! := by
  rw [getElem!_lt (by rw [Array.size_push]; omega), getElem!_lt h, Array.getElem_push_lt h]

theorem push_eq {a : Array W64} {x : W64} : (a.push x)[a.size]! = x := by
  rw [getElem!_lt (by rw [Array.size_push]; omega), Array.getElem_push_eq]

theorem schedStep_size (w : Array W64) (t : Nat) : (schedStep w t).size = w.size + 1 := Array.size_push _

theorem schedStep_lt {w : Array W64} {t i : Nat} (h : i < w.size) : (schedStep w t)[i]! = w[i]! := push_lt h

theorem schedStep_new (w : Array W64) (t : Nat) :
    (schedStep w t)[w.size]! =
      smallSigma1 w[t + 16 - 2]! + w[t + 16 - 7]! + smallSigma0 w[t + 16 - 15]! + w[t + 16 - 16]! := push_eq

theorem init_size (block : Bytes) : (schedInit block).size = 16 := by
  unfold schedInit; rw [Array.size_map, List.size_toArray, List.length_range]

theorem pre_size (block : Bytes) : ∀ n, ((List.range n).foldl schedStep (schedInit block)).size = 16 + n
  | 0 => init_size block
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, schedStep_size, pre_size block n]
    rfl

theorem pre_stable (block : Bytes) (n : Nat) :
    ∀ m, ∀ i, i < 16 + n →
      ((List.range (n + m)).foldl schedStep (schedInit block))[i]! =
        ((List.range n).foldl schedStep (schedInit block))[i]!
  | 0, _, _ => rfl
  | m + 1, i, hi => by
    rw [show n + (m + 1) = (n + m) + 1 from rfl, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    rw [schedStep_lt (by rw [pre_size]; omega)]
    exact pre_stable block n m i hi

theorem pre_new (block : Bytes) (j : Nat) :
    ((List.range (j + 1)).foldl schedStep (schedInit block))[j + 16]! =
      let w := (List.range j).foldl schedStep (schedInit block)
      smallSigma1 w[j + 16 - 2]! + w[j + 16 - 7]! + smallSigma0 w[j + 16 - 15]! + w[j + 16 - 16]! := by
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have := pre_size block j
  rw [show j + 16 = ((List.range j).foldl schedStep (schedInit block)).size by omega, schedStep_new]
  rw [this, Nat.add_comm 16 j]

theorem sched_pre (block : Bytes) {n i : Nat} (hn : n ≤ 64) (hi : i < 16 + n) :
    (schedule block)[i]! = ((List.range n).foldl schedStep (schedInit block))[i]! := by
  rw [schedule_eq, show List.range 64 = List.range (n + (64 - n)) by rw [Nat.add_sub_cancel' hn]]
  exact pre_stable block n (64 - n) i hi

/-- The first 16 schedule words are the block's big-endian words. -/
theorem sched_lt (block : Bytes) {t : Nat} (ht : t < 16) : (schedule block)[t]! = wordAt block t := by
  rw [sched_pre block (n := 0) (by decide) (by omega)]
  show (schedInit block)[t]! = _
  unfold schedInit
  rw [getElem!_lt (by rw [Array.size_map, List.size_toArray, List.length_range]; exact ht), Array.getElem_map]
  simp only [List.getElem_toArray, List.getElem_range]

/-- The message schedule's recurrence, section 6.4.2 step 1. -/
theorem sched_rec (block : Bytes) {t : Nat} (h1 : 16 ≤ t) (h2 : t < 80) :
    (schedule block)[t]! = smallSigma1 (schedule block)[t - 2]! + (schedule block)[t - 7]! +
      smallSigma0 (schedule block)[t - 15]! + (schedule block)[t - 16]! := by
  obtain ⟨j, rfl⟩ : ∃ j, t = j + 16 := ⟨t - 16, by omega⟩
  rw [sched_pre block (n := j + 1) (by omega) (by omega), pre_new block j,
    sched_pre block (n := j) (i := j + 16 - 2) (by omega) (by omega),
    sched_pre block (n := j) (i := j + 16 - 7) (by omega) (by omega),
    sched_pre block (n := j) (i := j + 16 - 15) (by omega) (by omega),
    sched_pre block (n := j) (i := j + 16 - 16) (by omega) (by omega)]

/-- `compress` with the rounds as `vs`. -/
theorem compress_vs (hv : V8) (block : Bytes) :
    compress hv.toList block =
      List.zipWith (· + ·) hv.toList (vs (fun t => (schedule block)[t]!) hv 80).toList := by
  exact congrArg (List.zipWith (· + ·) hv.toList) (foldl_vs (schedule block) hv 80)

end C3.Sha512
