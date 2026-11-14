import C3BootProofs.Proofs.ImageSpec
import C3BootProofs.Theorems.Formats

/-! # `imgW` and `decodeImageHeader`: the segments, and the whole header

The decoder reads every segment, then checks them; the compiled code reads
and checks each segment in turn. Both reject when any read or check fails, so
`segs_rel` relates them by induction on the segments left. `check_rel`
translates `checkSegW`'s word comparisons, which detect a sum that wraps past
2^32, into `segmentOk`'s bounds on natural numbers; `align_rel` turns the
compiled code's masks into remainders. `overlap_rel` and `entry_rel` do the
same for the overlap and entry-point checks, for segments that passed
`checkSegW`. `imgW_rel` puts them together with `hdr_rel`, and
`imageParse_decodes` joins it to `imageParse_correct`. -/

namespace C3

open RV32

/-- The segment kind for a Rust discriminant (0 to 3). -/
def kindOf (k : BitVec 8) : SegmentKind :=
  if k = 0 then .flashCode else if k = 1 then .flashData else if k = 2 then .ramCode else .ramData

/-- A segment as the decoder keeps it. -/
def toSeg (s : SegW) : Segment := ⟨kindOf s.kind, s.addr.toNat, s.off.toNat, s.len.toNat⟩

theorem ofByte_eq : ∀ b : BitVec 8,
    SegmentKind.ofByte b.toNat = if (3 : BitVec 8).ult (b - 1) = true then none else some (kindOf (b - 1)) := by
  decide

theorem kind_cases : ∀ k : BitVec 8, (3 : BitVec 8).ult k = false → k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide

theorem some_bind' {α β : Type} (a : α) (f : α → Option β) : (some a >>= f) = f a := rfl

section Seg

variable {M : Word → BitVec 8} {ptr len : Word}

theorem readSeg_rel (pos : Word) :
    Rel (readSegW M ptr len pos) (readSegment (tailAt M ptr len pos.toNat))
      fun r => (toSeg r.1, tailAt M ptr len r.2.toNat) := by
  unfold readSegW readSegment
  refine Rel.bind (rdU8_rel pos) fun ⟨b, p1⟩ => ?_
  dsimp only
  rw [ofByte_eq]
  by_cases hk : (3 : BitVec 8).ult (b - 1) = true
  · rw [ite_eq_left hk, ite_eq_left hk]; rfl
  · rw [ite_eq_right hk, ite_eq_right hk, some_bind']
    refine Rel.bind (rdRes_rel 3 p1 (by decide)) fun p2 => ?_
    unfold segA
    refine Rel.bind (rdU32_rel p2) fun ⟨a, p3⟩ => ?_
    unfold segO
    refine Rel.bind (rdU32_rel p3) fun ⟨o, p4⟩ => ?_
    unfold segL
    refine Rel.bind (rdU32_rel p4) fun ⟨l, p5⟩ => ?_
    rfl

end Seg

/-! ## Masks -/

theorem testBit_low : ∀ n i : Nat, Nat.testBit (2 ^ n - 1) i = decide (i < n)
  | 0, i => by rw [show 2 ^ 0 - 1 = 0 from rfl, Nat.zero_testBit, decide_eq_false (Nat.not_lt_zero i)]
  | n + 1, 0 => by
    have := Nat.two_pow_pos n
    rw [Nat.testBit_zero, decide_eq_true (Nat.succ_pos n), Nat.pow_succ]
    exact decide_eq_true (by omega)
  | n + 1, j + 1 => by
    have := Nat.two_pow_pos n
    rw [Nat.testBit_succ, show (2 ^ (n + 1) - 1) / 2 = 2 ^ n - 1 by rw [Nat.pow_succ]; omega, testBit_low n j]
    by_cases h : j < n
    · rw [decide_eq_true h, decide_eq_true (Nat.succ_lt_succ h)]
    · rw [decide_eq_false h, decide_eq_false (fun e => h (Nat.lt_of_succ_lt_succ e))]

theorem and_low (x n : Nat) : x &&& (2 ^ n - 1) = x % 2 ^ n :=
  Nat.eq_of_testBit_eq fun i => by
    rw [Nat.testBit_and, testBit_low, Nat.testBit_mod_two_pow, Bool.and_comm]

theorem mask_toNat (w : Word) (n : Nat) (hn : n ≤ 32) :
    (w &&& BitVec.ofNat 32 (2 ^ n - 1)).toNat = w.toNat % 2 ^ n := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hn
    have := Nat.two_pow_pos n
    omega), and_low]

theorem or_mod_zero (a o : Word) (n : Nat) :
    ((a ||| o).toNat % 2 ^ n == 0) = (o.toNat % 2 ^ n == 0 && a.toNat % 2 ^ n == 0) := by
  rw [BitVec.toNat_or, Nat.or_mod_two_pow]
  by_cases ha : a.toNat % 2 ^ n = 0
  · by_cases ho : o.toNat % 2 ^ n = 0
    · rw [ha, ho]; rfl
    · rw [ha, Nat.zero_or, beq_eq_false_iff_ne.mpr ho]; rfl
  · rw [beq_eq_false_iff_ne.mpr ha, Bool.and_false]
    exact beq_eq_false_iff_ne.mpr fun e => ha (Nat.or_eq_zero_iff.mp e).1

/-- `x &&& m != 0` for a low mask, as a remainder. -/
theorem mask_ne (w : Word) (n : Nat) (hn : n ≤ 32) :
    (w &&& BitVec.ofNat 32 (2 ^ n - 1) != 0) = !(w.toNat % 2 ^ n == 0) := by
  rw [bne, ← word_beq, mask_toNat w n hn]; rfl

theorem kindOf_flash : ∀ k : BitVec 8, (3 : BitVec 8).ult k = false → (kindOf k).isFlash = k.ult 2 := by decide

theorem align_rel (s : SegW) (hk : (3 : BitVec 8).ult s.kind = false) :
    alignOk s = if (kindOf s.kind).isFlash then
        (s.off.toNat % flashPage == 0 && s.addr.toNat % flashPage == 0 && s.len.toNat % flashPage == 0)
      else (s.off.toNat % 4 == 0 && s.addr.toNat % 4 == 0 && s.len.toNat % 4 == 0) := by
  unfold alignOk
  dsimp only
  have m16 : ((s.addr ||| s.off) &&& 0xFFFF != 0) = !((s.addr ||| s.off).toNat % 2 ^ 16 == 0) :=
    mask_ne (s.addr ||| s.off) 16 (by decide)
  have l16 : (s.len &&& 0xFFFF != 0) = !(s.len.toNat % 2 ^ 16 == 0) := mask_ne s.len 16 (by decide)
  have m2 : ((s.addr ||| s.off) &&& 3 != 0) = !((s.addr ||| s.off).toNat % 2 ^ 2 == 0) :=
    mask_ne (s.addr ||| s.off) 2 (by decide)
  have l2 : (s.len &&& 3 != 0) = !(s.len.toNat % 2 ^ 2 == 0) := mask_ne s.len 2 (by decide)
  rw [m16, l16, m2, l2, or_mod_zero, or_mod_zero, kindOf_flash _ hk]
  show _ = if s.kind.ult 2 = true then (s.off.toNat % 2 ^ 16 == 0 && s.addr.toNat % 2 ^ 16 == 0 &&
      s.len.toNat % 2 ^ 16 == 0) else (s.off.toNat % 2 ^ 2 == 0 && s.addr.toNat % 2 ^ 2 == 0 &&
      s.len.toNat % 2 ^ 2 == 0)
  generalize (s.off.toNat % 2 ^ 16 == 0) = A
  generalize (s.addr.toNat % 2 ^ 16 == 0) = B
  generalize (s.len.toNat % 2 ^ 16 == 0) = C
  generalize (s.off.toNat % 2 ^ 2 == 0) = D
  generalize (s.addr.toNat % 2 ^ 2 == 0) = E
  generalize (s.len.toNat % 2 ^ 2 == 0) = F
  rcases kind_cases s.kind hk with h | h | h | h <;> rw [h] <;>
    cases A <;> cases B <;> cases C <;> cases D <;> cases E <;> cases F <;> rfl

theorem segOk_eq (il : Nat) (s : SegW) (hk : (3 : BitVec 8).ult s.kind = false) :
    segmentOk il (toSeg s) = (decide (0 < s.len.toNat) && decide (s.off.toNat + s.len.toNat < 2 ^ 32) &&
      decide (s.off.toNat + s.len.toNat ≤ il) && decide (s.addr.toNat + s.len.toNat < 2 ^ 32) &&
      decide ((regionLo s.kind).toNat ≤ s.addr.toNat) &&
      decide (s.addr.toNat + s.len.toNat ≤ (regionHi s.kind).toNat) && alignOk s) := by
  rw [align_rel s hk]
  obtain ⟨k, a, o, l⟩ := s
  rcases kind_cases k hk with h | h | h | h <;> subst h <;> rfl

theorem ult_eq (x y : Word) : x.ult y = decide (x.toNat < y.toNat) := rfl

theorem add_ult (x y : Word) : (x + y).ult x = decide (2 ^ 32 ≤ x.toNat + y.toNat) := by
  rw [ult_eq, BitVec.toNat_add]
  have hx := x.isLt; have hy := y.isLt
  by_cases h : x.toNat + y.toNat < 2 ^ 32
  · rw [Nat.mod_eq_of_lt h, decide_eq_false (by omega), decide_eq_false (by omega)]
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), decide_eq_true (by omega),
      decide_eq_true (by omega)]

theorem check_rel (ilen prev : Word) (s : SegW) (hk : (3 : BitVec 8).ult s.kind = false) :
    match checkSegW ilen prev s with
    | .ok e => segmentOk ilen.toNat (toSeg s) = true ∧ prev.toNat ≤ s.off.toNat ∧
        e.toNat = s.off.toNat + s.len.toNat
    | .error _ => (segmentOk ilen.toNat (toSeg s) && decide (prev.toNat ≤ s.off.toNat)) = false := by
  rw [segOk_eq _ s hk]
  have hl := s.len.isLt
  have ho := s.off.isLt
  have ha := s.addr.isLt
  unfold checkSegW
  dsimp only
  by_cases c1 : (s.len == 0) = true
  · rw [ite_eq_left c1]
    have l0 : s.len.toNat = 0 := by rw [← word_beq] at c1; exact beq_iff_eq.mp c1
    show (_ && _) = false
    rw [decide_eq_false (by omega : ¬ 0 < s.len.toNat)]; simp only [Bool.false_and]
  rw [ite_eq_right c1]
  have l0 : 0 < s.len.toNat := by
    rw [← word_beq] at c1
    exact Nat.pos_of_ne_zero fun e => c1 (beq_iff_eq.mpr e)
  by_cases c2 : (s.off + s.len).ult s.off = true
  · rw [ite_eq_left c2]
    rw [add_ult] at c2
    have := of_decide_eq_true c2
    show (_ && _) = false
    rw [decide_eq_false (by omega : ¬ s.off.toNat + s.len.toNat < 2 ^ 32)]
    simp only [Bool.false_and, Bool.and_false]
  rw [ite_eq_right c2]
  rw [add_ult] at c2
  have w1 : ¬ 2 ^ 32 ≤ s.off.toNat + s.len.toNat := fun h => c2 (decide_eq_true h)
  have e1 : (s.off + s.len).toNat = s.off.toNat + s.len.toNat := toNat_add_lt (by omega)
  by_cases c3 : ilen.ult (s.off + s.len) = true
  · rw [ite_eq_left c3]
    rw [ult_eq, e1] at c3
    have := of_decide_eq_true c3
    show (_ && _) = false
    rw [decide_eq_false (by omega : ¬ s.off.toNat + s.len.toNat ≤ ilen.toNat)]
    simp only [Bool.false_and, Bool.and_false]
  rw [ite_eq_right c3]
  rw [ult_eq, e1] at c3
  have w3 : ¬ ilen.toNat < s.off.toNat + s.len.toNat := fun h => c3 (decide_eq_true h)
  by_cases c4 : (regionHi s.kind).ult (s.addr + s.len) = true
  · rw [ite_eq_left c4]
    rw [ult_eq, BitVec.toNat_add] at c4
    have h4 := of_decide_eq_true c4
    show (_ && _) = false
    by_cases hw : s.addr.toNat + s.len.toNat < 2 ^ 32
    · rw [Nat.mod_eq_of_lt hw] at h4
      rw [decide_eq_false (by omega : ¬ s.addr.toNat + s.len.toNat ≤ (regionHi s.kind).toNat)]
      simp only [Bool.false_and, Bool.and_false]
    · rw [decide_eq_false hw]
      simp only [Bool.false_and, Bool.and_false]
  rw [ite_eq_right c4]
  by_cases c5 : (s.addr + s.len).ult s.addr = true
  · rw [ite_eq_left c5]
    rw [add_ult] at c5
    have := of_decide_eq_true c5
    show (_ && _) = false
    rw [decide_eq_false (by omega : ¬ s.addr.toNat + s.len.toNat < 2 ^ 32)]
    simp only [Bool.false_and, Bool.and_false]
  rw [ite_eq_right c5]
  rw [add_ult] at c5
  have w2 : ¬ 2 ^ 32 ≤ s.addr.toNat + s.len.toNat := fun h => c5 (decide_eq_true h)
  rw [ult_eq, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)] at c4
  have w4 : ¬ (regionHi s.kind).toNat < s.addr.toNat + s.len.toNat := fun h => c4 (decide_eq_true h)
  by_cases c6 : s.addr.ult (regionLo s.kind) = true
  · rw [ite_eq_left c6]
    rw [ult_eq] at c6
    have := of_decide_eq_true c6
    show (_ && _) = false
    rw [decide_eq_false (by omega : ¬ (regionLo s.kind).toNat ≤ s.addr.toNat)]
    simp only [Bool.false_and, Bool.and_false]
  rw [ite_eq_right c6]
  rw [ult_eq] at c6
  have w6 : ¬ s.addr.toNat < (regionLo s.kind).toNat := fun h => c6 (decide_eq_true h)
  cases hal : alignOk s
  · rw [ite_eq_left (by decide : (!false) = true)]
    show (_ && _) = false
    simp only [Bool.false_and, Bool.and_false]
  rw [ite_eq_right (by decide : ¬ (!true) = true)]
  rw [decide_eq_true l0, decide_eq_true (by omega : s.off.toNat + s.len.toNat < 2 ^ 32),
    decide_eq_true (by omega : s.off.toNat + s.len.toNat ≤ ilen.toNat),
    decide_eq_true (by omega : s.addr.toNat + s.len.toNat < 2 ^ 32),
    decide_eq_true (by omega : (regionLo s.kind).toNat ≤ s.addr.toNat),
    decide_eq_true (by omega : s.addr.toNat + s.len.toNat ≤ (regionHi s.kind).toNat)]
  by_cases c8 : s.off.ult prev = true
  · rw [ite_eq_left c8]
    rw [ult_eq] at c8
    have := of_decide_eq_true c8
    show (_ && _) = false
    rw [decide_eq_false (by omega : ¬ prev.toNat ≤ s.off.toNat)]
    simp only [Bool.and_false]
  rw [ite_eq_right c8]
  rw [ult_eq] at c8
  exact ⟨rfl, Nat.le_of_not_lt (fun h => c8 (decide_eq_true h)), e1⟩

section Loop

variable {M : Word → BitVec 8} {ptr len : Word}

theorem segs_rel (ilen : Word) : ∀ n (pos prev : Word),
    match readSegsW M ptr len ilen n pos prev with
    | .ok (segs, _, prev') => readSegments n (tailAt M ptr len pos.toNat) = some (segs.map toSeg) ∧
        (segs.map toSeg).all (segmentOk ilen.toNat) = true ∧
        segmentsOrdered prev.toNat ilen.toNat (segs.map toSeg) = (prev' == ilen) ∧
        ∀ s ∈ segs, (3 : BitVec 8).ult s.kind = false
    | .error _ => readSegments n (tailAt M ptr len pos.toNat) = none ∨
        ∃ ss, readSegments n (tailAt M ptr len pos.toNat) = some ss ∧
          (ss.all (segmentOk ilen.toNat) && segmentsOrdered prev.toNat ilen.toNat ss) = false
  | 0, pos, prev => by
    show readSegments 0 _ = some [] ∧ true = true ∧ (prev.toNat == ilen.toNat) = (prev == ilen) ∧ _
    exact ⟨rfl, rfl, word_beq prev ilen, fun _ h => absurd h (List.not_mem_nil)⟩
  | n + 1, pos, prev => by
    have R := readSeg_rel (M := M) (ptr := ptr) (len := len) pos
    rw [readSegsW]
    cases hr : readSegW M ptr len pos with
    | error e =>
      rw [hr] at R
      refine .inl ?_
      show (readSegment _ >>= _) = none
      rw [show readSegment (tailAt M ptr len pos.toNat) = none from R]; rfl
    | ok r =>
      obtain ⟨s, p1⟩ := r
      have hk := readSegW_kind hr
      have R' : readSegment (tailAt M ptr len pos.toNat) = some (toSeg s, tailAt M ptr len p1.toNat) := by
        rw [hr] at R; exact R
      have spec : ∀ (o : Option (List Segment)), readSegments n (tailAt M ptr len p1.toNat) = o →
          readSegments (n + 1) (tailAt M ptr len pos.toNat) = o >>= fun more => some (toSeg s :: more) := by
        intro o ho
        show (readSegment _ >>= _) = _
        rw [R']
        show (readSegments n (tailAt M ptr len p1.toNat) >>= _) = _
        rw [ho]; rfl
      rw [ok_bind_eq]
      dsimp only
      have C := check_rel ilen prev s hk
      cases hc : checkSegW ilen prev s with
      | error e =>
        rw [hc] at C
        show readSegments (n + 1) _ = none ∨ _
        cases hs : readSegments n (tailAt M ptr len p1.toNat) with
        | none => exact .inl (by rw [spec _ hs]; rfl)
        | some ss =>
          refine .inr ⟨toSeg s :: ss, by rw [spec _ hs]; rfl, ?_⟩
          show ((segmentOk ilen.toNat (toSeg s) && ss.all (segmentOk ilen.toNat)) &&
            (decide (prev.toNat ≤ s.off.toNat) && segmentsOrdered (s.off.toNat + s.len.toNat) ilen.toNat ss)) = false
          revert C
          cases segmentOk ilen.toNat (toSeg s) <;> cases decide (prev.toNat ≤ s.off.toNat) <;>
            intro C <;> first | rfl | simp only [Bool.false_and, Bool.and_false] | (simp only [Bool.and_self] at C; cases C)
      | ok e =>
        rw [hc] at C
        obtain ⟨c1, c2, c3⟩ := C
        rw [ok_bind_eq]
        have IH := segs_rel ilen n p1 e
        cases hs : readSegsW M ptr len ilen n p1 e with
        | error e' =>
          rw [hs] at IH
          show readSegments (n + 1) _ = none ∨ _
          rcases IH with h | ⟨ss, h, hb⟩
          · exact .inl (by rw [spec _ h]; rfl)
          · refine .inr ⟨toSeg s :: ss, by rw [spec _ h]; rfl, ?_⟩
            show ((segmentOk ilen.toNat (toSeg s) && ss.all (segmentOk ilen.toNat)) &&
              (decide (prev.toNat ≤ s.off.toNat) && segmentsOrdered (s.off.toNat + s.len.toNat) ilen.toNat ss)) = false
            rw [c1, decide_eq_true c2, ← c3, Bool.true_and, Bool.true_and]
            exact hb
        | ok q =>
          obtain ⟨rest, p2, prev2⟩ := q
          rw [hs] at IH
          obtain ⟨i1, i2, i3, i4⟩ := IH
          refine ⟨by rw [spec _ i1]; rfl, ?_, ?_, ?_⟩
          · show (segmentOk ilen.toNat (toSeg s) && (rest.map toSeg).all (segmentOk ilen.toNat)) = true
            rw [c1, i2]; rfl
          · show (decide (prev.toNat ≤ s.off.toNat) &&
              segmentsOrdered (s.off.toNat + s.len.toNat) ilen.toNat (rest.map toSeg)) = _
            rw [decide_eq_true c2, ← c3, i3]; rfl
          · intro x hx
            rcases List.mem_cons.mp hx with h | h
            · rw [h]; exact hk
            · exact i4 x h

end Loop

/-! ## Overlaps and the entry point -/

/-- A segment that passed `checkSegW`: its kind is 0 to 3 and the decoder's
`segmentOk` holds. -/
def Good (il : Nat) (s : SegW) : Prop := (3 : BitVec 8).ult s.kind = false ∧ segmentOk il (toSeg s) = true

theorem good_facts {il : Nat} {s : SegW} (g : Good il s) :
    (regionLo s.kind).toNat ≤ s.addr.toNat ∧ s.addr.toNat + s.len.toNat ≤ (regionHi s.kind).toNat := by
  have h := g.2
  rw [segOk_eq _ _ g.1] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1.1.2, of_decide_eq_true h.1.2⟩

theorem phys_good {il : Nat} {s : SegW} (g : Good il s) :
    ∃ t x, physResult s.kind s.addr = some (t, x) ∧ (toSeg s).physical = (t == 0, x.toNat) ∧
      x.toNat + s.len.toNat < 2 ^ 32 ∧ (t = 0 ∨ t = 1) := by
  obtain ⟨hlo, hhi⟩ := good_facts g
  have ha := s.addr.isLt
  obtain ⟨k, a, o, l⟩ := s
  rcases kind_cases k g.1 with h | h | h | h <;> subst h
  · have hlo' : 0x42000000 ≤ a.toNat := hlo
    have hhi' : a.toNat + l.toNat ≤ 0x42800000 := hhi
    refine ⟨0, a + 0xBE000000, ?_, ?_, ?_, .inl rfl⟩
    · show (if a.ult 0x42000000 = true then none else some (0, a + 0xBE000000)) = _
      rw [ult_eq, decide_eq_false (by show ¬ a.toNat < 0x42000000; omega)]; rfl
    · show (true, a.toNat - 0x42000000) = (true, (a + 0xBE000000).toNat)
      rw [BitVec.toNat_add, show (0xBE000000 : Word).toNat = 0xBE000000 from rfl,
        show (a.toNat + 0xBE000000) % 2 ^ 32 = a.toNat - 0x42000000 by omega]
    · show (a + 0xBE000000).toNat + l.toNat < 2 ^ 32
      rw [BitVec.toNat_add, show (0xBE000000 : Word).toNat = 0xBE000000 from rfl]; omega
  · have hlo' : 0x3C000000 ≤ a.toNat := hlo
    have hhi' : a.toNat + l.toNat ≤ 0x3C800000 := hhi
    refine ⟨0, a + 0xC4000000, ?_, ?_, ?_, .inl rfl⟩
    · show (if a.ult 0x3C000000 = true then none else some (0, a + 0xC4000000)) = _
      rw [ult_eq, decide_eq_false (by show ¬ a.toNat < 0x3C000000; omega)]; rfl
    · show (true, a.toNat - 0x3C000000) = (true, (a + 0xC4000000).toNat)
      rw [BitVec.toNat_add, show (0xC4000000 : Word).toNat = 0xC4000000 from rfl,
        show (a.toNat + 0xC4000000) % 2 ^ 32 = a.toNat - 0x3C000000 by omega]
    · show (a + 0xC4000000).toNat + l.toNat < 2 ^ 32
      rw [BitVec.toNat_add, show (0xC4000000 : Word).toNat = 0xC4000000 from rfl]; omega
  · have hlo' : 0x40380000 ≤ a.toNat := hlo
    have hhi' : a.toNat + l.toNat ≤ 0x403A0000 := hhi
    refine ⟨1, a + 0xFF900000, ?_, ?_, ?_, .inr rfl⟩
    · show (if a.ult 0x700000 = true then none else some (1, a + 0xFF900000)) = _
      rw [ult_eq, decide_eq_false (by show ¬ a.toNat < 0x700000; omega)]; rfl
    · show (false, a.toNat - 0x700000) = (false, (a + 0xFF900000).toNat)
      rw [BitVec.toNat_add, show (0xFF900000 : Word).toNat = 0xFF900000 from rfl,
        show (a.toNat + 0xFF900000) % 2 ^ 32 = a.toNat - 0x700000 by omega]
    · show (a + 0xFF900000).toNat + l.toNat < 2 ^ 32
      rw [BitVec.toNat_add, show (0xFF900000 : Word).toNat = 0xFF900000 from rfl]; omega
  · have hhi' : a.toNat + l.toNat ≤ 0x3FCA0000 := hhi
    exact ⟨1, a, rfl, rfl, by show a.toNat + l.toNat < 2 ^ 32; omega, .inr rfl⟩

theorem overlaps_eq {a b : Segment} {pa pb : Bool × Nat} (ha : a.physical = pa) (hb : b.physical = pb) :
    a.overlaps b = (pa.1 == pb.1 && decide (pa.2 < pb.2 + b.length) && decide (pb.2 < pa.2 + a.length)) := by
  unfold Segment.overlaps
  rw [ha, hb]

theorem err_if : ∀ c : Bool, (match (if c = true then Except.error (10 : BitVec 8) else .ok ()) with
    | .ok () => c = false | .error _ => c = true) := by
  intro c; cases c <;> rfl

theorem space_beq {sa sb : BitVec 8} (ha : sa = 0 ∨ sa = 1) (hb : sb = 0 ∨ sb = 1) :
    ((sa == 0) == (sb == 0)) = decide (sa = sb) := by
  rcases ha with h | h <;> rcases hb with h' | h' <;> subst h <;> subst h' <;> rfl

theorem pair_rel {il : Nat} {a b : SegW} {sa : BitVec 8} {xa : Word} (gb : Good il b)
    (ppa : (toSeg a).physical = (sa == 0, xa.toNat)) (wa : xa.toNat + a.len.toNat < 2 ^ 32)
    (sa01 : sa = 0 ∨ sa = 1) :
    match pairW a sa xa b with
    | .ok () => (toSeg a).overlaps (toSeg b) = false
    | .error _ => (toSeg a).overlaps (toSeg b) = true := by
  obtain ⟨sb, xb, hpb, ppb, wb, sb01⟩ := phys_good gb
  unfold pairW
  rw [hpb]
  dsimp only
  rw [overlaps_eq ppa ppb]
  dsimp only
  rw [space_beq sa01 sb01]
  by_cases hs : sa = sb
  · rw [ite_eq_left hs, decide_eq_true hs, Bool.true_and]
    unfold pairChk
    rw [add_ult, decide_eq_false (by show ¬ 2 ^ 32 ≤ a.len.toNat + xa.toNat; omega),
      ite_eq_right (by decide), add_ult, decide_eq_false (by show ¬ 2 ^ 32 ≤ b.len.toNat + xb.toNat; omega),
      ite_eq_right (by decide), ult_eq, ult_eq, toNat_add_lt (by omega), toNat_add_lt (by omega),
      Nat.add_comm b.len.toNat, Nat.add_comm a.len.toNat]
    exact err_if _
  · rw [ite_eq_right hs, decide_eq_false hs, Bool.false_and, Bool.false_and]

theorem inner_rel {il : Nat} {a : SegW} {sa : BitVec 8} {xa : Word}
    (ppa : (toSeg a).physical = (sa == 0, xa.toNat)) (wa : xa.toNat + a.len.toNat < 2 ^ 32)
    (sa01 : sa = 0 ∨ sa = 1) : ∀ bs : List SegW, (∀ b ∈ bs, Good il b) →
    match innerW a sa xa bs with
    | .ok () => (bs.map toSeg).all (fun t => !(toSeg a).overlaps t) = true
    | .error _ => (bs.map toSeg).all (fun t => !(toSeg a).overlaps t) = false
  | [], _ => rfl
  | b :: bs, g => by
    have P := pair_rel (g b (List.mem_cons_self ..)) ppa wa sa01
    show match (pairW a sa xa b >>= fun _ => innerW a sa xa bs) with
      | .ok () => (!(toSeg a).overlaps (toSeg b) && (bs.map toSeg).all (fun t => !(toSeg a).overlaps t)) = true
      | .error _ => (!(toSeg a).overlaps (toSeg b) && (bs.map toSeg).all (fun t => !(toSeg a).overlaps t)) = false
    cases hp : pairW a sa xa b with
    | error e =>
      rw [hp] at P
      show (!(toSeg a).overlaps (toSeg b) && _) = false
      rw [P]; rfl
    | ok u =>
      rw [hp] at P
      rw [ok_bind_eq, P, Bool.not_false, Bool.true_and]
      exact inner_rel ppa wa sa01 bs fun x hx => g x (List.mem_cons_of_mem _ hx)

theorem overlap_rel {il : Nat} : ∀ segs : List SegW, (∀ s ∈ segs, Good il s) →
    match overlapW segs with
    | .ok () => noOverlaps (segs.map toSeg) = true
    | .error _ => noOverlaps (segs.map toSeg) = false
  | [], _ => rfl
  | a :: rest, g => by
    obtain ⟨sa, xa, hpa, ppa, wa, sa01⟩ := phys_good (g a (List.mem_cons_self ..))
    have I := inner_rel ppa wa sa01 rest fun x hx => g x (List.mem_cons_of_mem _ hx)
    show match (physW a >>= fun r => innerW a r.1 r.2 rest >>= fun _ => overlapW rest) with
      | .ok () => ((rest.map toSeg).all (fun t => !(toSeg a).overlaps t) && noOverlaps (rest.map toSeg)) = true
      | .error _ => ((rest.map toSeg).all (fun t => !(toSeg a).overlaps t) && noOverlaps (rest.map toSeg)) = false
    rw [show physW a = .ok (sa, xa) by unfold physW; rw [hpa]; rfl, ok_bind_eq]
    dsimp only
    cases hi : innerW a sa xa rest with
    | error e =>
      rw [hi] at I
      show (_ && _) = false
      rw [I]; rfl
    | ok u =>
      rw [hi] at I
      rw [ok_bind_eq, I, Bool.true_and]
      exact overlap_rel rest fun x hx => g x (List.mem_cons_of_mem _ hx)

theorem exec_eq : ∀ k : BitVec 8, (3 : BitVec 8).ult k = false → ((k &&& 1) == 0) = (kindOf k).isExecutable := by
  decide

theorem entryIn_eq (entry : Word) : ∀ segs : List SegW, (∀ s ∈ segs, (3 : BitVec 8).ult s.kind = false) →
    entryIn entry segs = (segs.map toSeg).any fun s =>
      s.kind.isExecutable && s.address ≤ entry.toNat && entry.toNat < s.address + s.length
  | [], _ => rfl
  | s :: rest, g => by
    rw [List.map_cons, List.any_cons, ← entryIn_eq entry rest fun x hx => g x (List.mem_cons_of_mem _ hx)]
    show ((s.kind &&& 1) == 0 && !entry.ult s.addr && (entry - s.addr).ult s.len || entryIn entry rest) =
      ((kindOf s.kind).isExecutable && decide (s.addr.toNat ≤ entry.toNat) &&
        decide (entry.toNat < s.addr.toNat + s.len.toNat) || entryIn entry rest)
    rw [exec_eq _ (g s (List.mem_cons_self ..)), ult_eq, ult_eq]
    have he := entry.isLt
    have ha := s.addr.isLt
    by_cases h : s.addr.toNat ≤ entry.toNat
    · rw [decide_eq_false (by omega : ¬ entry.toNat < s.addr.toNat), decide_eq_true h, BitVec.toNat_sub,
        show (2 ^ 32 - s.addr.toNat + entry.toNat) % 2 ^ 32 = entry.toNat - s.addr.toNat by omega]
      by_cases h2 : entry.toNat - s.addr.toNat < s.len.toNat
      · rw [decide_eq_true h2, decide_eq_true (by omega : entry.toNat < s.addr.toNat + s.len.toNat)]; rfl
      · rw [decide_eq_false h2, decide_eq_false (by omega : ¬ entry.toNat < s.addr.toNat + s.len.toNat)]; rfl
    · rw [decide_eq_true (by omega : entry.toNat < s.addr.toNat), decide_eq_false h]
      simp only [Bool.not_true, Bool.and_false, Bool.false_and]

theorem entry_rel (entry : Word) (segs : List SegW) (g : ∀ s ∈ segs, (3 : BitVec 8).ult s.kind = false) :
    match entryW entry segs with
    | .ok () => (entry.toNat % 2 == 0 && (segs.map toSeg).any fun s =>
        s.kind.isExecutable && s.address ≤ entry.toNat && entry.toNat < s.address + s.length) = true
    | .error _ => (entry.toNat % 2 == 0 && (segs.map toSeg).any fun s =>
        s.kind.isExecutable && s.address ≤ entry.toNat && entry.toNat < s.address + s.length) = false := by
  unfold entryW
  have m1 : (entry &&& 1 != 0) = !(entry.toNat % 2 ^ 1 == 0) := mask_ne entry 1 (by decide)
  rw [show 2 ^ 1 = 2 from rfl] at m1
  rw [m1, ← entryIn_eq entry segs g]
  generalize (entry.toNat % 2 == 0) = A
  generalize entryIn entry segs = B
  cases A <;> cases B <;> rfl

/-! ## The whole header -/

/-- The decoder's header for what `imgW` returns. -/
def toHdr (ilen : Word) (r : BitVec 8 × Word × BitVec 8 × List SegW) : ImageHeader :=
  ⟨r.1.toNat, r.2.1.toNat, ilen.toNat, r.2.2.2.map toSeg⟩

theorem init_toNat : ∀ c : BitVec 8, ((c.zeroExtend 32 <<< 4 + 0x14 : Word)).toNat = 20 + 16 * c.toNat := by
  decide

theorem good_of {il : Nat} {segs : List SegW} (h : (segs.map toSeg).all (segmentOk il) = true)
    (hk : ∀ s ∈ segs, (3 : BitVec 8).ult s.kind = false) : ∀ s ∈ segs, Good il s := fun s hs =>
  ⟨hk s hs, List.all_eq_true.mp h (toSeg s) (List.mem_map_of_mem hs)⟩

section Whole

variable {M : Word → BitVec 8} {ptr len ilen : Word}

theorem tail_rel (sv cnt : BitVec 8) (entry pos : Word) :
    Rel (do
        let (segs, _, prev) ← readSegsW M ptr len ilen cnt.toNat pos (cnt.zeroExtend 32 <<< 4 + 0x14)
        if prev != ilen then throw 9
        overlapW segs
        entryW entry segs
        pure (sv, entry, cnt, segs))
      (decTail ilen.toNat sv.toNat cnt.toNat entry.toNat (tailAt M ptr len pos.toNat)) (toHdr ilen) := by
  have S := segs_rel (M := M) (ptr := ptr) (len := len) ilen cnt.toNat pos (cnt.zeroExtend 32 <<< 4 + 0x14)
  rw [init_toNat] at S
  unfold decTail
  cases hs : readSegsW M ptr len ilen cnt.toNat pos (cnt.zeroExtend 32 <<< 4 + 0x14) with
  | error e =>
    rw [hs] at S
    show _ = none
    rcases S with h | ⟨ss, h, hb⟩
    · rw [h]; rfl
    · rw [h, some_bind']
      revert hb
      cases ss.all (segmentOk ilen.toNat) <;> cases segmentsOrdered (20 + 16 * cnt.toNat) ilen.toNat ss <;>
        intro hb <;> first | rfl | cases hb
  | ok q =>
    obtain ⟨segs, p', prev'⟩ := q
    rw [hs] at S
    obtain ⟨s1, s2, s3, s4⟩ := S
    rw [ok_bind_eq]
    dsimp only
    rw [s1, some_bind', s2, show require true = some () from rfl, some_bind', s3]
    refine Rel.req _ (fun hb => ?_) (fun hb => ⟨9, ?_⟩)
    · rw [ite_eq_right (by rw [bne, hb]; decide)]
      have O := overlap_rel segs (good_of s2 s4)
      cases ho : overlapW segs with
      | error e =>
        rw [ho] at O
        show _ = none
        rw [O]; rfl
      | ok u =>
        rw [ho] at O
        rw [ok_bind_eq, O, show require true = some () from rfl, some_bind']
        have E := entry_rel entry segs s4
        cases he : entryW entry segs with
        | error e =>
          rw [he] at E
          show _ = none
          rw [E]; rfl
        | ok u' =>
          rw [he] at E
          rw [ok_bind_eq, E]
          rfl
    · rw [ite_eq_left (by rw [bne, hb]; rfl)]; rfl

/-- The `len` bytes at `ptr`, as the Lean decoders take them. -/
abbrev imageBytes (M : Word → BitVec 8) (ptr len : Word) : Bytes := tailAt M ptr len 0

/-- **`imgW` decides what `decodeImageHeader` decides.** It accepts the `len`
bytes at `ptr` and an image of `ilen` bytes exactly when the decoder does, and
then returns the decoder's header. -/
theorem imgW_rel : Rel (imgW M ptr len ilen) (decodeImageHeader (imageBytes M ptr len) ilen.toNat) (toHdr ilen) := by
  unfold imgW
  exact hdr_rel fun sv cnt entry pos => tail_rel sv cnt entry pos

end Whole

/-- **The compiled `image::parse` decodes as the Lean spec does.** Under
`imageParse_correct`'s hypotheses, it returns `Err` when `decodeImageHeader`
rejects the `len` bytes at `ptr` and an image of `ilen` bytes. When the
decoder accepts, it returns `Ok`, and the result holds segments and fields
that `toHdr` maps to the decoder's header. -/
theorem imageParse_decodes (m : Machine) {P R G ptr len out ilen : Word} (env : IEnv P R G ptr len out)
    (code : ICode m.mem P) (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = ptr)
    (ha2 : reg m a2 = len) (ha3 : reg m a3 = ilen) (hsp : reg m sp = G + 0x160) :
    match decodeImageHeader (imageBytes m.mem ptr len) ilen.toNat with
    | none => ∃ e, IErrDone R G out m.mem (reg m) e m
    | some h => ∃ sv entry cnt segs, h = toHdr ilen (sv, entry, cnt, segs) ∧
        IOkDone R G out ilen m.mem (reg m) sv entry cnt segs m := by
  have C := imageParse_correct m env code hpc ha0 ha1 ha2 ha3 hsp
  have Rr := imgW_rel (M := m.mem) (ptr := ptr) (len := len) (ilen := ilen)
  cases hi : imgW m.mem ptr len ilen with
  | error e =>
    rw [hi] at C Rr
    rw [show decodeImageHeader (imageBytes m.mem ptr len) ilen.toNat = none from Rr]
    exact ⟨e, C⟩
  | ok r =>
    obtain ⟨sv, entry, cnt, segs⟩ := r
    rw [hi] at C Rr
    rw [show decodeImageHeader (imageBytes m.mem ptr len) ilen.toNat = some _ from Rr]
    exact ⟨sv, entry, cnt, segs, rfl, C⟩

/-- `mapped_pages_signed` for what the compiled `image::parse` returns: when
`imgW` accepts, each 64 KiB page the cache maps for a flash segment, the
`k`-th from the segment's start, ends inside the image. -/
theorem imgW_pages_signed {M : Word → BitVec 8} {ptr len ilen : Word} {sv cnt : BitVec 8} {entry : Word}
    {segs : List SegW} (h : imgW M ptr len ilen = .ok (sv, entry, cnt, segs)) {s : SegW} (hs : s ∈ segs)
    (hflash : (kindOf s.kind).isFlash = true) {k : Nat} (hk : k < s.len.toNat / flashPage) :
    s.off.toNat + (k + 1) * flashPage ≤ ilen.toNat := by
  have Rr := imgW_rel (M := M) (ptr := ptr) (len := len) (ilen := ilen)
  rw [h] at Rr
  exact mapped_pages_signed (h := toHdr ilen (sv, entry, cnt, segs)) Rr (s := toSeg s)
    (List.mem_map_of_mem hs) hflash hk

end C3
