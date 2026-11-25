import C3BootProofs.Proofs.BootWrite
import C3BootProofs.Proofs.ParseSpec

/-!
# The boot-state record, between the code's bytes and `decodeRecord`

`boot_main` reads each copy of the boot-state record with the compiled
`decode` (`bsErr` and `bsMem`) and writes one with `write_state`
(`bwRec`). This file connects both to the specification's `decodeRecord`:

* `bmr_read`: the 32 flash bytes at `b` decode to the state that `decode`
  leaves at `out` (`bmrSt`) when `bsErr` accepts them, and to `none`
  otherwise.
* `bmr_enc`: the 32 bytes that `write_state` builds from a valid state at
  `st` decode to that state.

`bmrOk` and `bmrState` restate `decodeRecord` over a byte function, in the
order the compiled checks run, and `bmr_decode` proves the restatement.
-/

namespace C3.RV32.Cur

open C3 C3.Image

set_option maxRecDepth 4000

theorem bmr_zff (x : BitVec 8) : x.zeroExtend 32 &&& 0xFF = x.zeroExtend 32 := zext_and_ff x

theorem bmr_zext (x : BitVec 8) : (x.zeroExtend 32 : Word).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

theorem bmr_sum4 (x0 x1 x2 x3 : BitVec 8) :
    (((x1.zeroExtend 32 <<< 8 ||| x0.zeroExtend 32) ||| (x2.zeroExtend 32 <<< 16 ||| x3.zeroExtend 32 <<< 24) :
      Word)).toNat = x0.toNat + 256 * (x1.toNat + 256 * (x2.toNat + 256 * x3.toNat)) := by
  have h0 := x0.isLt; have h1 := x1.isLt; have h2 := x2.isLt; have h3 := x3.isLt
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, bmr_zext]
  rw [Nat.mod_eq_of_lt (show x1.toNat <<< 8 < 2 ^ 32 by rw [Nat.shiftLeft_eq]; omega),
    Nat.mod_eq_of_lt (show x2.toNat <<< 16 < 2 ^ 32 by rw [Nat.shiftLeft_eq]; omega),
    Nat.mod_eq_of_lt (show x3.toNat <<< 24 < 2 ^ 32 by rw [Nat.shiftLeft_eq]; omega),
    ← Nat.shiftLeft_add_eq_or_of_lt (i := 8) h0,
    show x3.toNat <<< 24 = (x3.toNat <<< 8) <<< 16 by simp only [Nat.shiftLeft_eq]; omega,
    ← Nat.shiftLeft_or_distrib, Nat.or_comm x2.toNat, ← Nat.shiftLeft_add_eq_or_of_lt (i := 8) h2,
    Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (i := 16)
      (show x1.toNat <<< 8 + x0.toNat < 2 ^ 16 by rw [Nat.shiftLeft_eq]; omega)]
  simp only [Nat.shiftLeft_eq]; omega


/-- Whether `decodeRecord` accepts the bytes `y 0`, ..., `y 31`: the checksum, the
magic, the version, the reserved bytes, the preferred slot, the bounds on the
boots left and the confirmed bits, and the trial slot, in the order that the
compiled `decode` checks them. -/
def bmrOk (y : Nat → Nat) : Bool :=
  (crc32 ((List.range 28).map y) == y 28 + 256 * (y 29 + 256 * (y 30 + 256 * y 31))) &&
  (y 0 == 0x43 && y 1 == 0x33 && y 2 == 0x42 && y 3 == 0x53) && (y 4 + 256 * y 5 == 1) &&
  (y 6 == 0 && y 7 == 0) && decide (y 12 ≤ 1) && (List.range 12).all (fun i => y (16 + i) == 0) &&
  (decide (y 14 ≤ 3) && y 15 &&& 0xFC == 0) && (decide (y 13 ≤ 1) || (y 13 == 0xFF && y 14 == 0))

/-- The slot that byte `n` names when it is 0 or 1. -/
def bmrSlot (n : Nat) : Slot := if n = 0 then .a else .b

/-- The state that `decodeRecord` returns for the bytes `y 0`, ..., `y 31` when
`bmrOk` holds. -/
def bmrState (y : Nat → Nat) : State :=
  ⟨y 8 + 256 * (y 9 + 256 * (y 10 + 256 * y 11)), bmrSlot (y 12),
    if y 13 ≤ 1 then some ⟨bmrSlot (y 13), y 14⟩ else none, y 15⟩

theorem bmr_list (y : Nat → Nat) : (List.range 32).map y = [y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7, y 8, y 9,
    y 10, y 11, y 12, y 13, y 14, y 15, y 16, y 17, y 18, y 19, y 20, y 21, y 22, y 23, y 24, y 25, y 26, y 27,
    y 28, y 29, y 30, y 31] := rfl

theorem bmr_slot_le : ∀ {n : Nat} {s : Slot}, slotOfByte n = some s → n ≤ 1
  | 0, _, _ => by decide
  | 1, _, _ => by decide
  | _ + 2, _, h => by cases (show (none : Option Slot) = some _ from h)

theorem bmr_slot_eq : ∀ {n : Nat}, n ≤ 1 → slotOfByte n = some (bmrSlot n)
  | 0, _ => rfl
  | 1, _ => rfl
  | _ + 2, h => absurd h (by omega)

set_option maxHeartbeats 2000000 in
theorem bmr_some {y : Nat → Nat} {s : State} (h : decodeRecord ((List.range 32).map y) = some s) :
    bmrOk y = true := by
  rw [bmr_list] at h
  simp only [decodeRecord, List.length_cons, List.length_nil, List.take, List.drop, readU32, readHeader,
    readExpect, magicRecord, readU16, readZeros, readU8, Option.bind_eq_bind, Option.pure_def,
    Option.bind_eq_some_iff, require_eq_some, Option.ite_none_right_eq_some, Option.some.injEq] at h
  simp only [Nat.zero_add, Nat.reduceAdd, beq_self_eq_true', Nat.reduceLeDiff, decide_true, Bool.and_true,
    List.cons_beq_cons, List.take, List.drop, List.length_cons, List.length_nil, exists_eq_left',
    exists_const, and_true, true_and, List.all_cons, List.all_nil, Nat.reduceLT, ite_false,
    Option.some.injEq, exists_and_left, List.isEmpty_nil, Nat.lt_irrefl, Bool.and_eq_true, beq_iff_eq, and_assoc,
    decide_eq_true_eq, Option.ite_none_right_eq_some] at h
  obtain ⟨hc, h0, h1, h2, h3, h45, h6, h7, sl, hp, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27,
    h14, h15, ht⟩ := h
  have hp' := bmr_slot_le hp
  simp only [bmrOk, List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, List.all_cons, List.all_nil]
  rw [hc]
  simp only [h0, h1, h2, h3, h45, h6, h7, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h14, h15, hp',
    beq_self_eq_true', decide_true, Bool.true_and, Bool.and_true]
  by_cases e : y 13 = 255
  · rw [ite_eq_left e] at ht
    by_cases e2 : y 14 = 0
    · simp only [e, e2, Nat.reduceLeDiff, decide_false, beq_self_eq_true', Bool.and_self, Bool.or_true]
    · rw [ite_eq_right e2] at ht; simp only [Option.bind_none, reduceCtorEq] at ht
  · rw [ite_eq_right e] at ht
    rw [Option.bind_eq_some_iff] at ht
    obtain ⟨tr, htr, _⟩ := ht
    rw [Option.map_eq_some_iff] at htr
    obtain ⟨t, ht1, _⟩ := htr
    simp only [bmr_slot_le ht1, decide_true, Bool.true_or]

set_option maxHeartbeats 2000000 in
theorem bmr_ok {y : Nat → Nat} (h : bmrOk y = true) : decodeRecord ((List.range 32).map y) = some (bmrState y) := by
  simp only [bmrOk, List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    Bool.or_eq_true, and_assoc, Nat.reduceAdd] at h
  obtain ⟨hc, h0, h1, h2, h3, h45, h6, h7, hp, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27,
    h14, h15, ht⟩ := h
  rw [bmr_list]
  simp only [decodeRecord, List.length_cons, List.length_nil, List.take, List.drop, readU32, readHeader,
    readExpect, magicRecord, readU16, readZeros, readU8, Option.bind_eq_bind, Option.pure_def]
  rw [hc]
  rcases ht with ht | ⟨ht, hk⟩
  · simp only [require, Nat.zero_add, Nat.reduceAdd, beq_self_eq_true', ↓reduceIte, beq_iff_eq, h0, h1, h2, h3,
      Nat.reduceLeDiff, decide_true, h6, h7, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26,
      h27, Option.bind_some, h45, List.all_eq_true, List.isEmpty_iff, Bool.and_eq_true, decide_eq_true_eq,
      List.length_cons, List.length_nil, Nat.reduceLT, List.take_succ_cons, List.take_zero, List.mem_cons,
      List.not_mem_nil, or_false, or_self, imp_self, implies_true, List.drop_succ_cons, List.drop_zero,
      bmr_slot_eq hp, show y 13 ≠ 255 by omega, bmr_slot_eq ht, Option.map_some, h14, true_and, Nat.lt_irrefl,
      List.take_nil, List.drop_nil, h15, bmrState, ht]
  · simp only [require, Nat.zero_add, Nat.reduceAdd, beq_self_eq_true', ↓reduceIte, beq_iff_eq, h0, h1, h2, h3,
      Nat.reduceLeDiff, decide_true, h6, h7, ht, hk, h16, h17, h18, h19, h20, h21, h22, h23, h24,
      h25, h26, h27, Option.bind_some, h45, List.all_eq_true, List.isEmpty_iff, Bool.and_eq_true,
      decide_eq_true_eq, List.length_cons, List.length_nil, Nat.reduceLT, List.take_succ_cons, List.take_zero,
      List.mem_cons, List.not_mem_nil, or_false, or_self, imp_self, implies_true, List.drop_succ_cons,
      List.drop_zero, bmr_slot_eq hp, Nat.zero_le, true_and, Nat.lt_irrefl, List.take_nil, List.drop_nil, h15,
      bmrState]

theorem bmr_decode (y : Nat → Nat) :
    decodeRecord ((List.range 32).map y) = if bmrOk y then some (bmrState y) else none := by
  cases hb : bmrOk y
  · cases hd : decodeRecord ((List.range 32).map y) with
    | none => rfl
    | some s => exact absurd (bmr_some hd) (by rw [hb]; exact Bool.false_ne_true)
  · exact bmr_ok hb

theorem bmr_chain (c1 c2 c3 c4 d5 c6 d7 d8 e9 e10 : Bool) :
    (if (!c1) = true then some (0x11 : BitVec 8) else if (!c2) = true then some 2
      else if (!c3) = true then some 3 else if (!c4) = true then some 4 else if (!d5) = true then some 5
      else if (!c6) = true then some 4 else if (!d7) = true then some 5 else if d8 = true then none
      else if (!e9) = true then some 5 else if (!e10) = true then some 5 else none) = none ↔
    (c1 && c2 && c3 && c4 && d5 && c6 && d7 && (d8 || (e9 && e10))) = true := by
  cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> cases d5 <;> cases c6 <;> cases d7 <;> cases d8 <;>
    cases e9 <;> cases e10 <;> decide

theorem bmr_beq0 (x : BitVec 8) : (x == 0) = (x.toNat == 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj]; rfl

theorem bmr_allZero (M : Word → BitVec 8) (b : Word) : ∀ (k c : Nat),
    allZero M (b + BitVec.ofNat 32 c) k = (List.range k).all fun i => mb M b (c + i) == 0
  | 0, _ => rfl
  | k + 1, c => by
    rw [allZero, show b + BitVec.ofNat 32 c + 1 = b + BitVec.ofNat 32 (c + 1) from add_ofNat_assoc b c 1,
      bmr_allZero M b k (c + 1), List.range_succ_eq_map, List.all_cons,
      List.all_map, bmr_beq0, Nat.add_zero]
    congr 1
    congr 1
    funext i
    simp only [Function.comp_apply]
    rw [show c + 1 + i = c + (i + 1) by omega]

theorem bmr_body (M : Word → BitVec 8) (b : Word) :
    (bsBody M b).map BitVec.toNat = (List.range 28).map (mb M b) := by
  simp only [bsBody, List.map_map]; rfl

theorem bmr_or4 {a b : Nat} : (3 < a ||| b) = ¬ (a < 4 ∧ b < 4) := by
  apply propext
  constructor
  · intro h ⟨h1, h2⟩
    exact Nat.lt_le_asymm (Nat.or_lt_two_pow (n := 2) h1 h2) h
  · intro h
    rcases Nat.lt_or_ge 3 (a ||| b) with h' | h'
    · exact h'
    · exact absurd ⟨Nat.lt_succ_of_le (Nat.le_trans Nat.left_le_or h'),
        Nat.lt_succ_of_le (Nat.le_trans Nat.right_le_or h')⟩ h

set_option maxRecDepth 10000 in
theorem bmr_fc : ∀ x : BitVec 8, (x.toNat &&& 0xFC == 0) = decide (x.toNat < 4) := by decide

theorem bmr_err (M : Word → BitVec 8) (b : Word) : bsErr M b = none ↔ bmrOk (mb M b) = true := by
  have c1 : (crcBits (bsBody M b) == bsSum M b) =
      (crc32 ((List.range 28).map (mb M b)) == mb M b 28 + 256 * (mb M b 29 + 256 * (mb M b 30 + 256 * mb M b 31))) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj, crcBits_toNat, bmr_body]
    exact iff_of_eq (congrArg _ (bmr_sum4 _ _ _ _))
  have hb : ∀ i, mb M b i < 256 := fun i => (M _).isLt
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3
  have c2 : (mw M b 0 == 0x53423343) = (mb M b 0 == 0x43 && mb M b 1 == 0x33 && mb M b 2 == 0x42 && mb M b 3 == 0x53) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, ← BitVec.toNat_inj, mw_toNat, show (0x53423343 : Word).toNat = 0x53423343 from rfl]
    simp only [Bool.and_eq_true, beq_iff_eq, and_assoc, Nat.reduceAdd, le32]
    constructor
    · intro h; exact ⟨by omega, by omega, by omega, by omega⟩
    · intro ⟨e0, e1, e2, e3⟩; omega
  have c3 : (((M (b + 5)).zeroExtend 32 <<< 24 ||| (M (b + 4)).zeroExtend 32 <<< 16 : Word) >>> 16 == 1) =
      (mb M b 4 + 256 * mb M b 5 == 1) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj, version_toNat]; rfl
  have c4 : allZero M (b + 6) 2 = (mb M b 6 == 0 && mb M b 7 == 0) := by
    rw [show (b + 6 : Word) = b + BitVec.ofNat 32 6 from rfl, bmr_allZero]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.all_cons, List.all_nil,
      Nat.reduceAdd, Bool.and_true]
  have c5 : (1 : Word).ult ((M (b + 12)).zeroExtend 32 &&& 0xFF) = !decide (mb M b 12 ≤ 1) := by
    rw [bmr_zff, BitVec.ult, bmr_zext]
    exact Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]; exact Nat.not_le.symm)
  have c6 : allZero M (b + 16) 12 = (List.range 12).all (fun i => mb M b (16 + i) == 0) :=
    bmr_allZero M b 12 16
  have c7 : (3 : Word).ult (((M (b + 15)).zeroExtend 32 ||| (M (b + 14)).zeroExtend 32) &&& 0xFF) =
      !(decide (mb M b 14 ≤ 3) && mb M b 15 &&& 0xFC == 0) := by
    rw [← BitVec.setWidth_or, bmr_zff, BitVec.ult, bmr_zext, BitVec.toNat_or]
    have := bmr_fc (M (b + 15))
    rw [show mb M b 15 = (M (b + 15)).toNat from rfl, this]
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    show 3 < (M (b + 15)).toNat ||| (M (b + 14)).toNat ↔ _
    rw [bmr_or4 (a := (M (b + 15)).toNat) (b := (M (b + 14)).toNat)]
    simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not]
    show ¬((M (b + 15)).toNat < 4 ∧ (M (b + 14)).toNat < 4) ↔ ((M (b + 14)).toNat ≤ 3 → ¬ (M (b + 15)).toNat < 4)
    constructor
    · intro h e f; exact h ⟨f, by omega⟩
    · intro h ⟨e, f⟩; exact h (by omega) e
  have c8 : (bsTrial M b).ult 2 = decide (mb M b 13 ≤ 1) := by
    rw [bsTrial, bmr_zff, BitVec.ult, bmr_zext]
    exact decide_eq_decide.mpr Nat.lt_succ_iff
  have c9 : (bsTrial M b + 0xFFFFFF01 == 0) = (mb M b 13 == 0xFF) := by
    rw [bsTrial, bmr_zff, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj, BitVec.toNat_add, bmr_zext]
    have := hb 13
    show ((M (b + 13)).toNat + 0xFFFFFF01) % 2 ^ 32 = 0 ↔ (M (b + 13)).toNat = 0xFF
    constructor <;> intro h <;> omega
  have c10 : ((M (b + 14)).zeroExtend 32 &&& 0xFF == 0) = (mb M b 14 == 0) := by
    rw [bmr_zff, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj, bmr_zext]; rfl
  unfold bsErr bmrOk
  rw [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10]
  exact bmr_chain _ _ _ _ _ _ _ _ _ _


theorem bmr_trial (M : Word → BitVec 8) (b : Word) : (bsTrial M b).ult 2 = decide (mb M b 13 ≤ 1) := by
  rw [bsTrial, bmr_zff, BitVec.ult, bmr_zext]
  exact decide_eq_decide.mpr Nat.lt_succ_iff

/-- The state held in the eight bytes at `st`, as `decode` leaves it and
`write_state` reads it: the generation, then the trial slot (2 for none),
the boots left, the confirmed bits, and the preferred slot. -/
def bmrSt (M : Word → BitVec 8) (st : Word) : State :=
  ⟨(memLoad32 M st).toNat, bmrSlot (M (st + 7)).toNat,
    if (M (st + 4)).toNat ≤ 1 then some ⟨bmrSlot (M (st + 4)).toNat, (M (st + 5)).toNat⟩ else none,
    (M (st + 6)).toNat⟩

theorem bmr_ne (out : Word) {c d : Nat} (hc : c < 8) (hd : d < 8) (h : c ≠ d) :
    out + BitVec.ofNat 32 c ≠ out + BitVec.ofNat 32 d :=
  add_ofNat_ne out (Nat.lt_trans hc (by decide)) (Nat.lt_trans hd (by decide)) h

theorem bmr_mem (M : Word → BitVec 8) (out b : Word) (h : bsErr M b = none) :
    bmrSt (bsMem M out b) out = bmrState (mb M b) := by
  simp only [bsMem, h]
  have n : ∀ c d, c < 8 → d < 8 → c ≠ d → out + BitVec.ofNat 32 c ≠ out + BitVec.ofNat 32 d :=
    fun c d hc hd e => bmr_ne out hc hd e
  have gen : memLoad32 (memStore8 (memStore8 (memStore8 (memStore8 (memStore32 M out (mw M b 8)) (out + 4)
      (if (bsTrial M b).ult 2 then M (b + 13) else 2)) (out + 5) (M (b + 14))) (out + 6) (M (b + 15)))
      (out + 7) (M (b + 12))) out = mw M b 8 := by
    refine (memLoad32_congr fun j hj => ?_).trans (memLoad32_store32_same M out (mw M b 8))
    have hj8 : j < 8 := Nat.lt_trans hj (by decide)
    have m7 : out + BitVec.ofNat 32 j ≠ out + 7 := n j 7 hj8 (by decide) (Nat.ne_of_lt (Nat.lt_trans hj (by decide)))
    have m6 : out + BitVec.ofNat 32 j ≠ out + 6 := n j 6 hj8 (by decide) (Nat.ne_of_lt (Nat.lt_trans hj (by decide)))
    have m5 : out + BitVec.ofNat 32 j ≠ out + 5 := n j 5 hj8 (by decide) (Nat.ne_of_lt (Nat.lt_trans hj (by decide)))
    have m4 : out + BitVec.ofNat 32 j ≠ out + 4 := n j 4 hj8 (by decide) (Nat.ne_of_lt hj)
    rw [memStore8_ne m7, memStore8_ne m6, memStore8_ne m5, memStore8_ne m4]
  have b7 : out + 7 ≠ out + 6 := n 7 6 (by decide) (by decide) (by decide)
  have b75 : out + 7 ≠ out + 5 := n 7 5 (by decide) (by decide) (by decide)
  have b74 : out + 7 ≠ out + 4 := n 7 4 (by decide) (by decide) (by decide)
  have b65 : out + 6 ≠ out + 5 := n 6 5 (by decide) (by decide) (by decide)
  have b64 : out + 6 ≠ out + 4 := n 6 4 (by decide) (by decide) (by decide)
  have b54 : out + 5 ≠ out + 4 := n 5 4 (by decide) (by decide) (by decide)
  simp only [bmrSt, bmrState, gen, mw_toNat, le32, Nat.reduceAdd]
  rw [memStore8_same, memStore8_ne b7.symm, memStore8_same, memStore8_ne b75.symm, memStore8_ne b65.symm,
    memStore8_same, memStore8_ne b74.symm, memStore8_ne b64.symm, memStore8_ne b54.symm, memStore8_same,
    bmr_trial]
  by_cases e : mb M b 13 ≤ 1
  · simp only [e, decide_true, ite_true, show (M (b + 13)).toNat ≤ 1 from e]; rfl
  · simp only [e, decide_false, Bool.false_eq_true, ite_false]
    rfl

theorem bmr_le32 (v : Word) : v.toNat = le32 (v.extractLsb' 0 8).toNat (v.extractLsb' 8 8).toNat
    (v.extractLsb' 16 8).toNat (v.extractLsb' 24 8).toNat := by
  simp only [BitVec.extractLsb'_toNat, le32, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.div_one]
  have := v.isLt
  omega


theorem bmr_crc (M : Word → BitVec 8) (st : Word) :
    crc32 ((List.range 28).map fun i => (bwRec M st i).toNat) = (bwCrc M st).toNat := by
  rw [bwCrc, crcBits_toNat, List.map_map]
  exact congrArg crc32 (List.map_congr_left fun i hi => by
    simp only [Function.comp_apply, bwRec, ite_eq_left (List.mem_range.mp hi)])

theorem bmr_enc (M : Word → BitVec 8) (st : Word) (h7 : (M (st + 7)).toNat ≤ 1) (h6 : (M (st + 6)).toNat ≤ 3)
    (h45 : (M (st + 4)).toNat ≤ 1 ∧ (M (st + 5)).toNat ≤ 3 ∨ M (st + 4) = 2) :
    decodeRecord ((List.range 32).map fun i => (bwRec M st i).toNat) = some (bmrSt M st) := by
  have h6' : (M (st + 6)).toNat < 4 := Nat.lt_succ_of_le h6
  have f6 := bmr_fc (M (st + 6))
  rw [decide_eq_true h6'] at f6
  have ok : bmrOk (fun i => (bwRec M st i).toNat) = true := by
    simp only [bmrOk]
    rw [bmr_crc, bmr_le32 (bwCrc M st)]
    simp only [bwRec, bwBody, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
      List.all_cons, List.all_nil, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceSub, Nat.reduceMul,
      Nat.reduceAdd, ↓reduceIte, beq_self_eq_true', Bool.true_and, Bool.and_true, h7, decide_true, f6]
    rcases h45 with ⟨a4, a5⟩ | e
    · have ne : M (st + 4) ≠ 2 := fun e => absurd (e ▸ a4) (by decide)
      simp only [bwBoots, bwTrial, ne, ite_false, a4, a5, decide_true, Bool.true_or, Bool.and_true]
      rfl
    · simp only [bwBoots, bwTrial, e, ite_true]
      rfl
  rw [bmr_ok ok]
  simp only [bmrState, bmrSt, bwRec, bwBody, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceSub, Nat.reduceMul,
    ↓reduceIte]
  rw [bmr_le32 (memLoad32 M st)]
  rcases h45 with ⟨a4, a5⟩ | e
  · have ne : M (st + 4) ≠ 2 := fun e => absurd (e ▸ a4) (by decide)
    simp only [bwBoots, bwTrial, ne, ite_false, a4, ite_true]
  · simp only [bwBoots, bwTrial, e, ite_true]
    rfl

theorem bmr_read (M : Word → BitVec 8) (out b : Word) :
    decodeRecord ((List.range 32).map (mb M b)) =
      match bsErr M b with
      | none => some (bmrSt (bsMem M out b) out)
      | some _ => none := by
  rw [bmr_decode]
  cases h : bsErr M b with
  | none => rw [(bmr_err M b).mp h, ite_eq_left rfl, bmr_mem M out b h]
  | some e =>
    have hn : bmrOk (mb M b) = false := by
      cases hk : bmrOk (mb M b)
      · rfl
      · exact absurd ((bmr_err M b).mpr hk) (by rw [h]; exact Option.some_ne_none e)
    rw [hn]
    rfl

end C3.RV32.Cur
