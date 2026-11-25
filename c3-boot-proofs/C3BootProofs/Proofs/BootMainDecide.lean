import C3BootProofs.Proofs.BootMainWrite

/-!
# `boot_main` from its first check to the jump

From 0x1F4, `boot_main` checks the first slot of the plan with its first
closure. When the slot passes, it writes the trial's record if the plan
tries a trial, and boots it (`bmp_first`). When the slot fails, it ends any
trial, checks the other slot, and boots that slot (`bmp_other`) or halts.
`bmd_main` runs this part against `decideBoot`.
-/

namespace C3.RV32.Cur

open C3 C3.Image C3.RV32.BootMainContract

/-! ## The state's ranges and the plan -/

/-- What every decoded state satisfies: a 32-bit generation, confirmed
bits below 4, and at most 3 boots left in a trial. -/
def BmdValid (st : State) : Prop :=
  st.generation < 2 ^ 32 ∧ st.confirmed < 4 ∧ ∀ t, st.trial = some t → t.bootsLeft ≤ 3

theorem bmd_plan_trial {st : State} (h : (plan st).isTrial = true) :
    ∃ t, st.trial = some t ∧ 0 < t.bootsLeft ∧ (plan st).first = t.slot := by
  revert h; unfold plan
  cases e : st.trial with
  | none => intro h; exact absurd h Bool.false_ne_true
  | some t =>
    intro h
    by_cases hb : 0 < t.bootsLeft
    · exact ⟨t, rfl, hb, by simp only [hb, ↓reduceIte]⟩
    · simp only [hb, ↓reduceIte] at h; exact absurd h Bool.false_ne_true

theorem bmd_slot_num (sl : Slot) : bmrSlot (bmSlotNum sl) = sl := by cases sl <;> rfl

theorem bmd_slot_le (sl : Slot) : bmSlotNum sl ≤ 1 := by cases sl <;> decide

/-! ## Words and bytes -/

theorem bmd_byte (v : Nat) : (BitVec.ofNat 32 v).extractLsb' 0 8 = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_zero,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 8 ∣ 2 ^ 32)]

theorem bmd_byte_hi (a b : Nat) : BitVec.ofNat 8 (a + 256 * b) = BitVec.ofNat 8 a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  exact Nat.add_mul_mod_self_left a 256 b

theorem bmd_toNat8 {v : Nat} (h : v < 256) : (BitVec.ofNat 8 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The trial byte of the word at +4. -/
theorem bmd_word_byte (st : State) :
    (bmWord st).extractLsb' 0 8 = BitVec.ofNat 8 (bmTrialBytes st.trial).1 := by
  have e : ∀ a b c p : Nat, a + 256 * b + 65536 * c + 16777216 * p = a + 256 * (b + 256 * c + 65536 * p) := by
    intro a b c p; omega
  rw [bmWord, bmd_byte, e, bmd_byte_hi]

/-- The next generation, saturated, as `boot_main` computes it from
`generation + 1`. -/
theorem bmd_sat {g : Nat} (hg : g < 2 ^ 32) :
    aluEval .or (aluEval .add (aluEval .sltu 0 (BitVec.ofNat 32 g + 1)) 0xFFFFFFFF) (BitVec.ofNat 32 g + 1) =
      BitVec.ofNat 32 (min (g + 1) maxGeneration) := by
  rcases Nat.lt_or_ge (g + 1) (2 ^ 32) with h | h
  · have e : BitVec.ofNat 32 g + 1 = BitVec.ofNat 32 (g + 1) := ofNat_add_ofNat g 1
    have hn : (0 : Word).ult (BitVec.ofNat 32 (g + 1)) = true := by
      rw [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
      exact decide_eq_true (Nat.succ_pos g)
    have hm : min (g + 1) maxGeneration = g + 1 := Nat.min_eq_left (Nat.le_pred_of_lt h)
    simp only [aluEval, e, hn, ↓reduceIte, hm]
    exact BitVec.zero_or
  · have e : g = 2 ^ 32 - 1 := Nat.le_antisymm (Nat.le_pred_of_lt hg) (Nat.sub_le_of_le_add h)
    subst e; decide

/-- The boots byte less one, as `boot_main` computes it from the word at +5
when the trial has boots left. -/
theorem bmd_boots {b c p : Nat} (hb0 : 0 < b) (hb : b ≤ 3) (hc : c < 4) (hp : p ≤ 1) :
    (aluEval .sub (BitVec.ofNat 32 (b + 256 * c + 65536 * p))
      (aluEval .sltu 0 (aluEval .and (BitVec.ofNat 32 (b + 256 * c + 65536 * p)) 0xFF))).extractLsb' 0 8 =
      BitVec.ofNat 8 (b - 1) := by
  have k : ∀ b, b < 4 → ∀ c, c < 4 → ∀ p, p < 2 → 0 < b →
      (aluEval .sub (BitVec.ofNat 32 (b + 256 * c + 65536 * p))
        (aluEval .sltu 0 (aluEval .and (BitVec.ofNat 32 (b + 256 * c + 65536 * p)) 0xFF))).extractLsb' 0 8 =
        BitVec.ofNat 8 (b - 1) := by decide
  exact k b (Nat.lt_succ_of_le hb) c hc p (Nat.lt_succ_of_le hp) hb0

/-! ## The record stores -/

theorem bmd_ne (st : Word) {c d : Nat} (hc : c < 8) (hd : d < 8) (h : c ≠ d) :
    st + BitVec.ofNat 32 c ≠ st + BitVec.ofNat 32 d :=
  add_ofNat_ne st (Nat.lt_trans hc (by decide)) (Nat.lt_trans hd (by decide)) h

theorem bmd_sep_hi (st : Word) {c : Nat} (h4 : 4 ≤ c) (h8 : c < 8) : Sep (st + BitVec.ofNat 32 c) 1 st 4 := by
  have := sep_offsets st (c := c) (n := 1) (d := 0) (k := 4) (.inr h4) (Nat.le_trans h8 (by decide)) (by decide)
  rwa [add_ofNat_zero] at this

theorem bmd_out {st x : Word} (h : Sep st 8 x 1) {c : Nat} (hc : c < 8) : x ≠ st + BitVec.ofNat 32 c :=
  fun e => h c hc 0 (by decide) (by rw [add_ofNat_zero]; exact e.symm)

/-- The five stores before the trial's write: the preferred slot, the
generation, the trial slot, the boots left, and the confirmed bits. -/
theorem bmd_rec_tr (M : Word → BitVec 8) (st g : Word) (b4 b5 b6 b7 : BitVec 8) :
    memLoad32 (memStore8 (memStore8 (memStore8 (memStore32 (memStore8 M (st + 7) b7) (st + 0x0) g)
      (st + 4) b4) (st + 5) b5) (st + 6) b6) st = g ∧
    bmrSt (memStore8 (memStore8 (memStore8 (memStore32 (memStore8 M (st + 7) b7) (st + 0x0) g)
      (st + 4) b4) (st + 5) b5) (st + 6) b6) st =
      ⟨g.toNat, bmrSlot b7.toNat, if b4.toNat ≤ 1 then some ⟨bmrSlot b4.toNat, b5.toNat⟩ else none, b6.toNat⟩ ∧
    BmwValid (memStore8 (memStore8 (memStore8 (memStore32 (memStore8 M (st + 7) b7) (st + 0x0) g)
      (st + 4) b4) (st + 5) b5) (st + 6) b6) st = ((b7.toNat ≤ 1) ∧ b6.toNat ≤ 3 ∧
        (b4.toNat ≤ 1 ∧ b5.toNat ≤ 3 ∨ b4 = 2)) ∧
    ∀ x, Sep st 8 x 1 → memStore8 (memStore8 (memStore8 (memStore32 (memStore8 M (st + 7) b7) (st + 0x0) g)
      (st + 4) b4) (st + 5) b5) (st + 6) b6 x = M x := by
  have e74 : st + 7 ≠ st + 4 := bmd_ne st (c := 7) (d := 4) (by decide) (by decide) (by decide)
  have e75 : st + 7 ≠ st + 5 := bmd_ne st (c := 7) (d := 5) (by decide) (by decide) (by decide)
  have e76 : st + 7 ≠ st + 6 := bmd_ne st (c := 7) (d := 6) (by decide) (by decide) (by decide)
  have e45 : st + 4 ≠ st + 5 := bmd_ne st (c := 4) (d := 5) (by decide) (by decide) (by decide)
  have e46 : st + 4 ≠ st + 6 := bmd_ne st (c := 4) (d := 6) (by decide) (by decide) (by decide)
  have e56 : st + 5 ≠ st + 6 := bmd_ne st (c := 5) (d := 6) (by decide) (by decide) (by decide)
  have s7 : ∀ i, i < 4 → st + 7 ≠ st + BitVec.ofNat 32 i := fun i hi =>
    bmd_ne st (c := 7) (by decide) (Nat.lt_trans hi (by decide)) (by intro e; subst e; exact absurd hi (by decide))
  have m0 : memLoad32 (memStore8 (memStore8 (memStore8 (memStore32 (memStore8 M (st + 7) b7) (st + 0x0) g)
      (st + 4) b4) (st + 5) b5) (st + 6) b6) st = g := by
    rw [memLoad32_store8_sep (show Sep (st + 6) 1 st 4 from bmd_sep_hi st (c := 6) (by decide) (by decide)),
      memLoad32_store8_sep (show Sep (st + 5) 1 st 4 from bmd_sep_hi st (c := 5) (by decide) (by decide)),
      memLoad32_store8_sep (show Sep (st + 4) 1 st 4 from bmd_sep_hi st (c := 4) (by decide) (by decide)),
      show st + 0x0 = st from BitVec.add_zero st, memLoad32_store32_same]
  have m7 : memStore8 (memStore8 (memStore8 (memStore32 (memStore8 M (st + 7) b7) (st + 0x0) g)
      (st + 4) b4) (st + 5) b5) (st + 6) b6 (st + 7) = b7 := by
    rw [memStore8_ne e76, memStore8_ne e75, memStore8_ne e74, memStore32_ne (a := st + 0x0)
      (by rw [show st + 0x0 = st from BitVec.add_zero st]; exact s7), memStore8_same]
  have m6 : memStore8 (memStore8 (memStore8 (memStore32 (memStore8 M (st + 7) b7) (st + 0x0) g)
      (st + 4) b4) (st + 5) b5) (st + 6) b6 (st + 6) = b6 := memStore8_same _ _ _
  have m5 : memStore8 (memStore8 (memStore8 (memStore32 (memStore8 M (st + 7) b7) (st + 0x0) g)
      (st + 4) b4) (st + 5) b5) (st + 6) b6 (st + 5) = b5 := by
    rw [memStore8_ne e56, memStore8_same]
  have m4 : memStore8 (memStore8 (memStore8 (memStore32 (memStore8 M (st + 7) b7) (st + 0x0) g)
      (st + 4) b4) (st + 5) b5) (st + 6) b6 (st + 4) = b4 := by
    rw [memStore8_ne e46, memStore8_ne e45, memStore8_same]
  refine ⟨m0, ?_, ?_, fun x hx => ?_⟩
  · rw [bmrSt, m0, m7, m6, m5, m4]
  · rw [BmwValid, m7, m6, m5, m4]
  · rw [memStore8_ne (show x ≠ st + 6 from bmd_out hx (c := 6) (by decide)), memStore8_ne (show x ≠ st + 5 from bmd_out hx (c := 5) (by decide)),
      memStore8_ne (show x ≠ st + 4 from bmd_out hx (c := 4) (by decide)),
      memStore32_ne (a := st + 0x0) (fun i hi => by
        rw [show st + 0x0 = st from BitVec.add_zero st]; exact bmd_out hx (Nat.lt_trans hi (by decide))),
      memStore8_ne (show x ≠ st + 7 from bmd_out hx (c := 7) (by decide))]

/-- The four stores before the write that ends a trial: the generation, no
trial, the confirmed bits, and the preferred slot. -/
theorem bmd_rec_nt (M : Word → BitVec 8) (st g : Word) (b4 b6 b7 : BitVec 8) :
    memLoad32 (memStore8 (memStore8 (memStore8 (memStore32 M (st + 0x0) g) (st + 4) b4) (st + 6) b6)
      (st + 7) b7) st = g ∧
    bmrSt (memStore8 (memStore8 (memStore8 (memStore32 M (st + 0x0) g) (st + 4) b4) (st + 6) b6) (st + 7) b7) st =
      ⟨g.toNat, bmrSlot b7.toNat,
        if b4.toNat ≤ 1 then some ⟨bmrSlot b4.toNat,
          (memStore8 (memStore8 (memStore8 (memStore32 M (st + 0x0) g) (st + 4) b4) (st + 6) b6) (st + 7) b7
            (st + 5)).toNat⟩ else none, b6.toNat⟩ ∧
    (BmwValid (memStore8 (memStore8 (memStore8 (memStore32 M (st + 0x0) g) (st + 4) b4) (st + 6) b6)
      (st + 7) b7) st ↔ ((b7.toNat ≤ 1) ∧ b6.toNat ≤ 3 ∧
        (b4.toNat ≤ 1 ∧ (memStore8 (memStore8 (memStore8 (memStore32 M (st + 0x0) g) (st + 4) b4) (st + 6) b6)
          (st + 7) b7 (st + 5)).toNat ≤ 3 ∨ b4 = 2))) ∧
    ∀ x, Sep st 8 x 1 →
      memStore8 (memStore8 (memStore8 (memStore32 M (st + 0x0) g) (st + 4) b4) (st + 6) b6) (st + 7) b7 x = M x := by
  have e74 : st + 7 ≠ st + 4 := bmd_ne st (c := 7) (d := 4) (by decide) (by decide) (by decide)
  have e76 : st + 7 ≠ st + 6 := bmd_ne st (c := 7) (d := 6) (by decide) (by decide) (by decide)
  have e46 : st + 4 ≠ st + 6 := bmd_ne st (c := 4) (d := 6) (by decide) (by decide) (by decide)
  have m0 : memLoad32 (memStore8 (memStore8 (memStore8 (memStore32 M (st + 0x0) g) (st + 4) b4) (st + 6) b6)
      (st + 7) b7) st = g := by
    rw [memLoad32_store8_sep (show Sep (st + 7) 1 st 4 from bmd_sep_hi st (c := 7) (by decide) (by decide)),
      memLoad32_store8_sep (show Sep (st + 6) 1 st 4 from bmd_sep_hi st (c := 6) (by decide) (by decide)),
      memLoad32_store8_sep (show Sep (st + 4) 1 st 4 from bmd_sep_hi st (c := 4) (by decide) (by decide)),
      show st + 0x0 = st from BitVec.add_zero st, memLoad32_store32_same]
  have m7 : memStore8 (memStore8 (memStore8 (memStore32 M (st + 0x0) g) (st + 4) b4) (st + 6) b6) (st + 7) b7
      (st + 7) = b7 := memStore8_same _ _ _
  have m6 : memStore8 (memStore8 (memStore8 (memStore32 M (st + 0x0) g) (st + 4) b4) (st + 6) b6) (st + 7) b7
      (st + 6) = b6 := by rw [memStore8_ne e76.symm, memStore8_same]
  have m4 : memStore8 (memStore8 (memStore8 (memStore32 M (st + 0x0) g) (st + 4) b4) (st + 6) b6) (st + 7) b7
      (st + 4) = b4 := by rw [memStore8_ne e74.symm, memStore8_ne e46, memStore8_same]
  refine ⟨m0, ?_, ?_, fun x hx => ?_⟩
  · rw [bmrSt, m0, m7, m6, m4]
  · rw [BmwValid, m7, m6, m4]
  · rw [memStore8_ne (show x ≠ st + 7 from bmd_out hx (c := 7) (by decide)), memStore8_ne (show x ≠ st + 6 from bmd_out hx (c := 6) (by decide)),
      memStore8_ne (show x ≠ st + 4 from bmd_out hx (c := 4) (by decide)),
      memStore32_ne (a := st + 0x0) (fun i hi => by
        rw [show st + 0x0 = st from BitVec.add_zero st]; exact bmd_out hx (Nat.lt_trans hi (by decide)))]

/-! ## The decision -/

theorem bmd_dec_acc {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {st : State} (hst : (bmRecs flash).1 = st) {mf : Manifest} {sv t : Nat}
    (hA : bmcAccept flash pinned policy (bmLevel M0) (BitVec.ofNat 32 (bmSlotNum (plan st).first)) =
      some (mf, sv, t)) :
    bmDecision flash pinned policy M0 =
      ⟨if (plan st).isTrial then some st.withTrialBootUsed else (plan st).writeFirst,
        .boot (plan st).first (burnTarget sv (st.isConfirmed (plan st).first) (bmLevel M0))⟩ := by
  unfold bmDecision decideBoot
  rw [hst]
  simp only [bmCheck, hA, Option.map]

theorem bmd_dec_rej {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {st : State} (hst : (bmRecs flash).1 = st)
    (hA : bmcAccept flash pinned policy (bmLevel M0) (BitVec.ofNat 32 (bmSlotNum (plan st).first)) = none) :
    (bmDecision flash pinned policy M0).write =
      if (plan st).isTrial then some st.withoutTrial else (plan st).writeFirst := by
  unfold bmDecision decideBoot
  rw [hst]
  simp only [bmCheck, hA, Option.map]
  split <;> rfl

theorem bmd_dec_oth {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {st : State} (hst : (bmRecs flash).1 = st)
    (hA : bmcAccept flash pinned policy (bmLevel M0) (BitVec.ofNat 32 (bmSlotNum (plan st).first)) = none)
    {mf : Manifest} {sv t : Nat}
    (hB : bmcAccept flash pinned policy (bmLevel M0) (BitVec.ofNat 32 (bmSlotNum (plan st).first.other)) =
      some (mf, sv, t)) :
    (bmDecision flash pinned policy M0).outcome =
      .boot (plan st).first.other (burnTarget sv (st.isConfirmed (plan st).first.other) (bmLevel M0)) := by
  unfold bmDecision decideBoot
  rw [hst]
  simp only [bmCheck, hA, hB, Option.map]

/-! ## Registers and the frame at 0x1F4 -/

/-- The registers at 0x1F4, for the state `st` that `bootstate::read`
returned and the frame at `F`. `s0`'s low byte is the plan's first slot,
`s1` holds the word at +4 of the state, `s3`, `s5`, and `s6` hold parts of
it, `s7` the entry level, `s8` the generation plus 1, and `s9` whether the
plan tries a trial. -/
structure BmdPre (flash : Nat → BitVec 8) (M0 : Word → BitVec 8) (F : Word) (st : State)
    (g : Fin 32 → Word) : Prop where
  r8 : g 8 &&& 0xFF = BitVec.ofNat 32 (bmSlotNum (plan st).first)
  r9 : g 9 = bmWord st
  r18 : g 18 = bmCopy (bmRecs flash).2
  r19 : g 19 = BitVec.ofNat 32 (st.confirmed + 256 * bmSlotNum st.preferred)
  r20 : g 20 = F + BitVec.ofNat 32 0xB9A8
  r21 : g 21 = BitVec.ofNat 32 (bmSlotNum st.preferred)
  r22 : g 22 = BitVec.ofNat 32 ((bmTrialBytes st.trial).2 + 256 * st.confirmed + 65536 * bmSlotNum st.preferred)
  r23 : g 23 = btPop (memLoad32 M0 efuseRd)
  r24 : g 24 = BitVec.ofNat 32 st.generation + 1
  r25 : g 25 = if (plan st).isTrial then 1 else 0
  rsp : g sp = F

/-- The registers that `BmdPre` names. -/
def bmdRegs (q : Fin 32) : Bool := q.val ∈ [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25]

theorem bmd_regs_rom : ∀ q, bmdRegs q = true → romKeep q = true := by decide

theorem BmdPre.keep {flash : Nat → BitVec 8} {M0 : Word → BitVec 8} {F : Word} {st : State}
    {g g' : Fin 32 → Word} (P : BmdPre flash M0 F st g) (h : ∀ q, bmdRegs q = true → g' q = g q) :
    BmdPre flash M0 F st g' :=
  ⟨by rw [h 8 (by decide)]; exact P.r8, by rw [h 9 (by decide)]; exact P.r9,
    by rw [h 18 (by decide)]; exact P.r18, by rw [h 19 (by decide)]; exact P.r19,
    by rw [h 20 (by decide)]; exact P.r20, by rw [h 21 (by decide)]; exact P.r21,
    by rw [h 22 (by decide)]; exact P.r22, by rw [h 23 (by decide)]; exact P.r23,
    by rw [h 24 (by decide)]; exact P.r24, by rw [h 25 (by decide)]; exact P.r25,
    by rw [h sp (by decide)]; exact P.rsp⟩

theorem BmdPre.rom {flash : Nat → BitVec 8} {M0 : Word → BitVec 8} {F : Word} {st : State}
    {g g' : Fin 32 → Word} (P : BmdPre flash M0 F st g) (h : ∀ q, romKeep q = true → g' q = g q) :
    BmdPre flash M0 F st g' := P.keep fun q hq => h q (bmd_regs_rom q hq)

theorem bmd_eF {F : Word} (hFk : F.toNat + 0xBE80 < 2 ^ 32) {c : Nat} (hc : c ≤ 0xBE80) :
    (F + BitVec.ofNat 32 c).toNat = F.toNat + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem bmd_below {F x : Word} {k : Nat} (hk : k ≤ F.toNat) (hx : F.toNat ≤ x.toNat) :
    Sep (F - BitVec.ofNat 32 k) k x 1 := by
  have hk' : k < 2 ^ 32 := Nat.lt_of_le_of_lt hk F.isLt
  refine sep_of_le ?_ (x.isLt)
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk']; omega

theorem bmd_rec_sep {F x : Word} (hFk : F.toNat + 0xBE80 < 2 ^ 32) (hx : F.toNat + 0xB9B0 ≤ x.toNat) :
    Sep (F + BitVec.ofNat 32 0xB9A8) 8 x 1 :=
  sep_of_le (by rw [bmd_eF hFk (by decide)]; omega) x.isLt

/-- The ROM write's stack lies below `F`. -/
theorem bmd_stk {F top : Word} {R romStack stack0 : Nat} (hF : F.toNat + 0xBE80 = top.toNat)
    (hlo : 0x3FCC8000 + bmK R romStack stack0 ≤ top.toNat) : 0x90 + romStack ≤ F.toNat := by
  have hKv : bmK R romStack stack0 = 0xBE80 + 0x150 + R + romStack + stack0 := rfl
  omega

/-- The record at `F + 0xB9A8` lies in `boot_main`'s frame. -/
theorem bmd_kin {F top x : Word} {R romStack stack0 : Nat} (hF : F.toNat + 0xBE80 = top.toNat)
    (hlo : 0x3FCC8000 + bmK R romStack stack0 ≤ top.toNat)
    (hx : Sep (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) x 1) :
    Sep (F + BitVec.ofNat 32 0xB9A8) 8 x 1 := by
  have hKv : bmK R romStack stack0 = 0xBE80 + 0x150 + R + romStack + stack0 := rfl
  have hFk : F.toNat + 0xBE80 < 2 ^ 32 := by rw [hF]; exact top.isLt
  have hW : (top - BitVec.ofNat 32 (bmK R romStack stack0)).toNat = top.toNat - bmK R romStack stack0 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, hKv]; omega
  refine bmt_sep_in hx ?_ ?_
  · rw [hW, bmd_eF hFk (by decide), hKv]; omega
  · rw [hW, bmd_eF hFk (by decide), hKv]; omega

/-- Byte `i` of a `k`-byte field at `F + c` lies above the record at `F + 0xB9A8`. -/
theorem bmd_hiOff {F : Word} {c k i : Nat} (hFk : F.toNat + 0xBE80 < 2 ^ 32) (h1 : 0xB9B0 ≤ c)
    (h2 : c + k ≤ 0xBE80) (hi : i < k) : F.toNat + 0xB9B0 ≤ (F + BitVec.ofNat 32 c + BitVec.ofNat 32 i).toNat := by
  rw [BitVec.add_assoc, ofNat_add_ofNat, bmd_eF hFk (by omega)]; omega

set_option maxRecDepth 20000 in
/-- The record at `F + 0xB9A8` lies below the bootloader's code. -/
theorem bmd_lowS {F top : Word} {c n : Nat} (hF : F.toNat + 0xBE80 = top.toNat)
    (hhi : top.toNat ≤ bmPtr.toNat) (hc : c + n ≤ 8) :
    Sep (F + BitVec.ofNat 32 0xB9A8 + BitVec.ofNat 32 c) n BM bootMainCode.length := by
  have hFk : F.toNat + 0xBE80 < 2 ^ 32 := by rw [hF]; exact top.isLt
  have hbp : bmPtr.toNat = 0x3FCDFFF0 := rfl
  refine lowSep ?_ (by decide) (by decide)
  rw [BitVec.add_assoc, ofNat_add_ofNat, bmd_eF hFk (by omega)]
  rw [hbp] at hhi; omega

/-! ## The first slot passes -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- From 0x27C, after the first closure accepted the plan's first slot with
its `Accepted` bytes at `F + 0xBBF0`: when the plan tries a trial,
`boot_main` writes `withTrialBootUsed`, then boots the slot. -/
theorem bmd_acc {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    (X : BmHyp flash pinned policy M0 top R romStack stack0 romBase romCode E)
    {n : Machine} {F : Word} (s : St n.mem BM n 0x27C (reg n)) (hF : F.toNat + 0xBE80 = top.toNat)
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    {st : State} (hst : (bmRecs flash).1 = st) (hv : BmdValid st) (P : BmdPre flash M0 F st (reg n))
    {mf : Manifest} {sv t : Nat}
    (hA : bmcAccept flash pinned policy (bmLevel M0) (BitVec.ofNat 32 (bmSlotNum (plan st).first)) =
      some (mf, sv, t))
    (hAcc : AccOk flash (BitVec.ofNat 32 (bmSlotNum (plan st).first)) mf n.mem (F + BitVec.ofNat 32 0xBBF0))
    (hsvb : n.mem (F + BitVec.ofNat 32 0xBD18) = BitVec.ofNat 8 sv)
    (hlw : memLoad32 n.mem (F + BitVec.ofNat 32 0xBD10) =
      BitVec.ofNat 32 (bmcBase (BitVec.ofNat 32 (bmSlotNum (plan st).first)) + mf.image.offset)) :
    BmEnd (BmJump flash pinned policy M0 top (bmK R romStack stack0)) n := by
  have C := X.env
  have h16 := C.hsp; have hhi := C.hhi; have hlo := C.hlo
  have hKv : bmK R romStack stack0 = 0xBE80 + 0x150 + R + romStack + stack0 := rfl
  have hbp : bmPtr.toNat = 0x3FCDFFF0 := rfl
  obtain ⟨_, hge, hsv, _⟩ := bmc_accept hA
  have hF16 : F.toNat % 16 = 0 := by
    rw [← hF, show (48768 : Nat) = 16 * 3048 from rfl, Nat.add_mul_mod_self_left] at h16; exact h16
  have hFk : F.toNat + 0xBE80 < 2 ^ 32 := by rw [hF]; exact top.isLt
  have hal0 : (F + (BitVec.ofNat 32 0xB9A8 + 0x0)).toNat % 4 = 0 :=
    bmp_align hF16 hFk (by decide) (by decide)
  clear h16 hF16
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  have hD := bmd_dec_acc hst hA
  have hDo : (bmDecision flash pinned policy M0).outcome = .boot (plan st).first
      (burnTarget sv (st.confirmed &&& (plan st).first.bit != 0) (bmLevel M0)) := by rw [hD]; rfl
  -- `s10 = sv`, to 0x280
  obtain ⟨n1, c1, u1⟩ := s.block bmB27 hc bmB27_end ⟨trivial, trivial⟩
  have m1 : n1.mem = n.mem := u1.mem
  have r1 : ∀ r, reg n1 r = (runBlock bmB27 (n.mem, reg n)).2 r := fun r => by rw [u1.regs]
  have t1 : St n1.mem BM n1 0x280 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have s10 : reg n1 26 = BitVec.ofNat 32 sv := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB27, upd, ↓reduceIte]
    rw [P.r20, BitVec.add_assoc, show BitVec.ofNat 32 0xB9A8 + 0x370 = BitVec.ofNat 32 0xBD18 from rfl, hsvb]
    exact bmp_zext hsv
  have k1 : ∀ r, r ≠ 26 → reg n1 r = reg n r := fun r h0 => by
    rw [r1, runBlock_reg _ _ _ r s.zero (by simp only [bmB27]; revert h0; revert r; decide)]
  have P1 : BmdPre flash M0 F st (reg n1) := P.keep fun q hq => k1 q (by rintro rfl; exact absurd hq (by decide))
  have hc1 : CodeIn n1.mem BM bootMainCode := by rw [m1]; exact hc
  have hK1 : BmKeep M0 n1.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [m1]; exact hK
  have hAcc1 : AccOk flash (BitVec.ofNat 32 (bmSlotNum (plan st).first)) mf n1.mem (F + BitVec.ofNat 32 0xBBF0) := by
    rw [m1]; exact hAcc
  have hlw1 : memLoad32 n1.mem (F + BitVec.ofNat 32 0xBD10) =
      BitVec.ofNat 32 (bmcBase (BitVec.ofNat 32 (bmSlotNum (plan st).first)) + mf.image.offset) := by
    rw [m1]; exact hlw
  cases hT : (plan st).isTrial
  · -- no trial: `beqz s9` to 0x2C2
    obtain ⟨n2, e2, t2⟩ := t1.taken hc1 0x2C2 bm_at_280 (by decide)
      (by rw [P1.r25, hT, t1.zero]; decide)
    refine BmEnd.pre (c1.trans (.single e2)) ?_
    have P2 : BmdPre flash M0 F st (reg n2) := P1.keep fun q _ => t2.regs q
    rw [← t2.mem] at hK1 hAcc1 hlw1
    exact bmp_first X ⟨t2.pc, rfl, fun _ => rfl⟩ P2.rsp hF hK1 (c := st.confirmed)
      (p := bmSlotNum st.preferred) hv.2.1 (bmd_slot_le _) hA hDo hAcc1 hlw1 P2.r8 P2.r19 P2.r20
      (by rw [t2.regs]; exact s10) P2.r23
  · -- a trial: write `withTrialBootUsed`
    obtain ⟨tt, htr, hbt, hfirst⟩ := bmd_plan_trial hT
    have hbt3 := hv.2.2 tt htr
    obtain ⟨n2, e2, t2⟩ := t1.notTaken hc1 0x284 bm_at_280 (by decide)
      (by rw [P1.r25, hT, t1.zero]; decide)
    have hS : ∀ c, c < 8 → Sep (reg n1 20 + BitVec.ofNat 32 c) 1 BM bootMainCode.length := fun c hc8 => by
      rw [P1.r20]; exact bmd_lowS hF hhi (Nat.succ_le_of_lt hc8)
    have hS4 : Sep (reg n1 20 + 0x0) 4 BM bootMainCode.length := by
      rw [P1.r20]; exact bmd_lowS (c := 0) hF hhi (by decide)
    have hal : (reg n1 20 + 0x0).toNat % 4 = 0 := by
      rw [P1.r20, BitVec.add_assoc]; exact hal0
    obtain ⟨n3, c3, u3⟩ := t2.block bmB28 hc1
      bmB28_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, hS 7 (by decide), ⟨hal, hS4⟩,
        hS 4 (by decide), hS 5 (by decide), hS 6 (by decide), trivial, trivial, trivial, trivial, trivial⟩
    have r3 : ∀ r, reg n3 r = (runBlock bmB28 (n1.mem, reg n1)).2 r := fun r => by rw [u3.regs]
    have t3 : St n3.mem BM n3 0x2BA (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have m3 : n3.mem = memStore8 (memStore8 (memStore8 (memStore32 (memStore8 n1.mem (reg n1 20 + 7)
        ((reg n1 21).extractLsb' 0 8)) (reg n1 20 + 0x0)
        (aluEval .or (aluEval .add (aluEval .sltu (reg n1 x0) (reg n1 24)) 0xFFFFFFFF) (reg n1 24)))
        (reg n1 20 + 4) ((reg n1 9).extractLsb' 0 8))
        (reg n1 20 + 5) ((aluEval .sub (reg n1 22) (aluEval .sltu (reg n1 x0)
          (aluEval .and (reg n1 22) 0xFF))).extractLsb' 0 8))
        (reg n1 20 + 6) ((reg n1 19).extractLsb' 0 8) := by rw [u3.mem]; rfl
    have hb7 : (reg n1 21).extractLsb' 0 8 = BitVec.ofNat 8 (bmSlotNum st.preferred) := by
      rw [P1.r21, bmd_byte]
    have hg : aluEval .or (aluEval .add (aluEval .sltu (reg n1 x0) (reg n1 24)) 0xFFFFFFFF) (reg n1 24) =
        BitVec.ofNat 32 (min (st.generation + 1) maxGeneration) := by
      rw [t1.zero, P1.r24]; exact bmd_sat hv.1
    have hb4 : (reg n1 9).extractLsb' 0 8 = BitVec.ofNat 8 (bmSlotNum tt.slot) := by
      rw [P1.r9, bmd_word_byte, htr]; rfl
    have hb5 : (aluEval .sub (reg n1 22) (aluEval .sltu (reg n1 x0) (aluEval .and (reg n1 22) 0xFF))).extractLsb' 0 8 =
        BitVec.ofNat 8 (tt.bootsLeft - 1) := by
      rw [t1.zero, P1.r22, htr]
      exact bmd_boots hbt hbt3 hv.2.1 (bmd_slot_le _)
    have hb6 : (reg n1 19).extractLsb' 0 8 = BitVec.ofNat 8 st.confirmed := by
      rw [P1.r19, bmd_byte, bmd_byte_hi]
    rw [hb7, hg, hb4, hb5, hb6, P1.r20] at m3
    obtain ⟨_, hrs, hrv, hrout⟩ := bmd_rec_tr n1.mem (F + BitVec.ofNat 32 0xB9A8)
      (BitVec.ofNat 32 (min (st.generation + 1) maxGeneration)) (BitVec.ofNat 8 (bmSlotNum tt.slot))
      (BitVec.ofNat 8 (tt.bootsLeft - 1)) (BitVec.ofNat 8 st.confirmed) (BitVec.ofNat 8 (bmSlotNum st.preferred))
    rw [← m3] at hrs hrv hrout
    have hgl : min (st.generation + 1) maxGeneration < 2 ^ 32 :=
      Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
    have l7 := bmd_slot_le st.preferred
    have l4 := bmd_slot_le tt.slot
    have hc3 : st.confirmed < 4 := hv.2.1
    rw [bmd_toNat8 (Nat.lt_of_le_of_lt l7 (by decide)), bmd_toNat8 (Nat.lt_of_le_of_lt l4 (by decide)),
      bmd_toNat8 (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_le_of_lt hbt3 (by decide))),
      bmd_toNat8 (Nat.lt_trans hc3 (by decide)), BitVec.toNat_ofNat, Nat.mod_eq_of_lt hgl] at hrs
    rw [bmd_toNat8 (Nat.lt_of_le_of_lt l7 (by decide)), bmd_toNat8 (Nat.lt_of_le_of_lt l4 (by decide)),
      bmd_toNat8 (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_le_of_lt hbt3 (by decide))),
      bmd_toNat8 (Nat.lt_trans hc3 (by decide))] at hrv
    clear hgl
    have hrec : bmrSt n3.mem (F + BitVec.ofNat 32 0xB9A8) = st.withTrialBootUsed := by
      rw [hrs, ite_eq_left_of_eq_true _ _ (eq_true l4), bmd_slot_num, bmd_slot_num]
      unfold State.withTrialBootUsed State.next
      rw [htr]; rfl
    have hval : BmwValid n3.mem (F + BitVec.ofNat 32 0xB9A8) := by
      rw [hrv]
      exact ⟨l7, Nat.le_of_lt_succ hc3, .inl ⟨l4, Nat.le_trans (Nat.sub_le _ _) hbt3⟩⟩
    have k3 : ∀ r, r ≠ a0 → r ≠ a1 → reg n3 r = reg n1 r := fun r h0 h1 => by
      rw [r3, runBlock_reg _ _ _ r t1.zero (by simp only [bmB28]; revert h0 h1; revert r; decide)]
    have P3 : BmdPre flash M0 F st (reg n3) := P1.keep fun q hq => k3 q
      (by rintro rfl; exact absurd hq (by decide)) (by rintro rfl; exact absurd hq (by decide))
    have a0_3 : reg n3 a0 = bmCopy (bmRecs flash).2 := by
      rw [r3]; simp +decide only [runBlock, BInstr.run, bmB28, upd, ↓reduceIte]
      (try rw [t1.zero]); exact (BitVec.zero_add _).trans P1.r18
    have a1_3 : reg n3 a1 = F + BitVec.ofNat 32 0xB9A8 := by
      rw [r3]; simp +decide only [runBlock, BInstr.run, bmB28, upd, ↓reduceIte]; rw [P1.rsp]; rfl
    have hK3 : BmKeep M0 n3.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) :=
      hK1.step fun x hx => hrout x (bmd_kin hF hlo hx)
    have hW : (bmDecision flash pinned policy M0).write = some st.withTrialBootUsed := by
      rw [hD]; simp only [hT, ↓reduceIte]
    obtain ⟨n4, c4, t4, keep4, hK4, fr4⟩ := bmw_call X t3 P3.rsp hF hK3 (j := 0xB9A8) (by decide) (by decide)
      a0_3 a1_3 hW hrec hval bm_at_2ba bm_at_2be (by decide) (by decide)
    have P4 : BmdPre flash M0 F st (reg n4) := P3.rom keep4
    have hstk := bmd_stk hF hlo
    have hfr : ∀ x : Word, F.toNat + 0xB9B0 ≤ x.toNat → n4.mem x = n1.mem x := fun x hx => by
      rw [fr4 x (bmd_below hstk (Nat.le_trans (Nat.le_add_right _ _) hx)), hrout x (bmd_rec_sep hFk hx)]
    refine BmEnd.pre (c1.trans ((Steps.single e2).trans (c3.trans c4))) ?_
    refine bmp_first X t4 P4.rsp hF hK4 (c := st.confirmed) (p := bmSlotNum st.preferred) hv.2.1 (bmd_slot_le _)
      hA hDo ?_ ?_ P4.r8 P4.r19 P4.r20 ?_ P4.r23
    · exact bmt_acc_move hAcc1 fun i hi => hfr _ (bmd_hiOff (k := 0x12C) hFk (by decide) (by decide)
        (Nat.lt_trans hi (by decide)))
    · rw [← hlw1]
      exact bmt_load_congr fun j hj => hfr _ (bmd_hiOff (k := 4) hFk (by decide) (by decide) hj)
    · rw [keep4 26 (by decide), k3 26 (by decide) (by decide)]; exact s10

end C3.RV32.Cur
