import C3BootProofs.Proofs.BootMainDecide

/-!
# `boot_main` from the decoded state to its first check

From 0x174, with the state that `bootstate::read` returned, `boot_main`
computes the plan (`plan`): a trial with boots left is tried first, an
expired trial is ended with a write, and otherwise the preferred slot is
tried. It stores the plan's bytes and goes on at 0x1F4 (`bmd_main`).
`bmq_plan` runs this part against `decideBoot`.
-/

namespace C3.RV32.Cur

open C3 C3.Image C3.RV32.BootMainContract

/-! ## The registers at 0x174 -/

/-- The registers at 0x174 that `BmdPre` names, other than s0, s8, and s9. -/
structure BmqPre (flash : Nat → BitVec 8) (M0 : Word → BitVec 8) (F : Word) (st : State)
    (g : Fin 32 → Word) : Prop where
  r9 : g 9 = bmWord st
  r18 : g 18 = bmCopy (bmRecs flash).2
  r19 : g 19 = BitVec.ofNat 32 (st.confirmed + 256 * bmSlotNum st.preferred)
  r20 : g 20 = F + BitVec.ofNat 32 0xB9A8
  r21 : g 21 = BitVec.ofNat 32 (bmSlotNum st.preferred)
  r22 : g 22 = BitVec.ofNat 32 ((bmTrialBytes st.trial).2 + 256 * st.confirmed + 65536 * bmSlotNum st.preferred)
  r23 : g 23 = btPop (memLoad32 M0 efuseRd)
  rsp : g sp = F

/-- The registers that `BmqPre` names. -/
def bmqRegs (q : Fin 32) : Bool := q.val ∈ [2, 9, 18, 19, 20, 21, 22, 23]

theorem BmqPre.keep {flash : Nat → BitVec 8} {M0 : Word → BitVec 8} {F : Word} {st : State}
    {g g' : Fin 32 → Word} (P : BmqPre flash M0 F st g) (h : ∀ q, bmqRegs q = true → g' q = g q) :
    BmqPre flash M0 F st g' :=
  ⟨by rw [h 9 (by decide)]; exact P.r9,
    by rw [h 18 (by decide)]; exact P.r18, by rw [h 19 (by decide)]; exact P.r19,
    by rw [h 20 (by decide)]; exact P.r20, by rw [h 21 (by decide)]; exact P.r21,
    by rw [h 22 (by decide)]; exact P.r22, by rw [h 23 (by decide)]; exact P.r23,
    by rw [h sp (by decide)]; exact P.rsp⟩

theorem BmqPre.up {flash : Nat → BitVec 8} {M0 : Word → BitVec 8} {F : Word} {st : State}
    {g : Fin 32 → Word} (P : BmqPre flash M0 F st g)
    (h8 : g 8 &&& 0xFF = BitVec.ofNat 32 (bmSlotNum (plan st).first))
    (h24 : g 24 = BitVec.ofNat 32 st.generation + 1) (h25 : g 25 = if (plan st).isTrial then 1 else 0) :
    BmdPre flash M0 F st g :=
  ⟨h8, P.r9, P.r18, P.r19, P.r20, P.r21, P.r22, P.r23, h24, h25, P.rsp⟩

/-! ## The plan's three cases -/

theorem bmq_plan_none {st : State} (h : st.trial = none) : plan st = ⟨st.preferred, false, none⟩ := by
  unfold plan; rw [h]

theorem bmq_plan_live {st : State} {t : Trial} (h : st.trial = some t) (hb : 0 < t.bootsLeft) :
    plan st = ⟨t.slot, true, none⟩ := by
  unfold plan; rw [h]; exact ite_eq_left_of_eq_true _ _ (eq_true hb)

theorem bmq_plan_exp {st : State} {t : Trial} (h : st.trial = some t) (hb : t.bootsLeft = 0) :
    plan st = ⟨st.preferred, false, some st.withoutTrial⟩ := by
  unfold plan; rw [h]; exact ite_eq_right_of_eq_false _ _ (eq_false (by rw [hb]; decide))

/-! ## Low bytes -/

theorem bmq_and_lo (v : Nat) : BitVec.ofNat 32 v &&& 0xFF = BitVec.ofNat 32 (v % 256) := by
  rw [bmt_lo, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 2 ^ 32)]

theorem bmq_and_small {v : Nat} (h : v < 256) : BitVec.ofNat 32 v &&& 0xFF = BitVec.ofNat 32 v := by
  rw [bmq_and_lo, Nat.mod_eq_of_lt h]

theorem bmq_tb_le (tr : Option Trial) : (bmTrialBytes tr).1 ≤ 2 := by
  cases tr with
  | none => decide
  | some t => exact Nat.le_trans (bmd_slot_le t.slot) (by decide)

theorem bmq_word_lo (st : State) : bmWord st &&& 0xFF = BitVec.ofNat 32 (bmTrialBytes st.trial).1 := by
  have e : ∀ a b c p : Nat, a + 256 * b + 65536 * c + 16777216 * p = a + 256 * (b + 256 * c + 65536 * p) := by
    intro a b c p; omega
  rw [bmWord, e, bmq_and_lo, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (bmq_tb_le st.trial) (by decide))]

theorem bmq_s6_lo (b c p : Nat) (h : b < 256) :
    BitVec.ofNat 32 (b + 256 * c + 65536 * p) &&& 0xFF = BitVec.ofNat 32 b := by
  have e : ∀ b c p : Nat, b + 256 * c + 65536 * p = b + 256 * (c + 256 * p) := by
    intro b c p; omega
  rw [e, bmq_and_lo, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

/-! ## The frame -/

set_option maxRecDepth 20000 in
theorem bmq_lowS {F top : Word} {c n : Nat} (hF : F.toNat + 0xBE80 = top.toNat)
    (hhi : top.toNat ≤ bmPtr.toNat) (hc : c + n ≤ 0x4D8) :
    Sep (F + BitVec.ofNat 32 0xB9A8 + BitVec.ofNat 32 c) n BM bootMainCode.length := by
  have hFk : F.toNat + 0xBE80 < 2 ^ 32 := by rw [hF]; exact top.isLt
  have hbp : bmPtr.toNat = 0x3FCDFFF0 := rfl
  refine lowSep ?_ (by decide) (by decide)
  rw [BitVec.add_assoc, ofNat_add_ofNat, bmd_eF hFk (by omega)]
  rw [hbp] at hhi; omega

theorem bmq_kin {F top x : Word} {R romStack stack0 : Nat} {c n : Nat} (hF : F.toNat + 0xBE80 = top.toNat)
    (hlo : 0x3FCC8000 + bmK R romStack stack0 ≤ top.toNat) (hc : c + n ≤ 0x4D8)
    (hx : Sep (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) x 1) :
    Sep (F + BitVec.ofNat 32 0xB9A8 + BitVec.ofNat 32 c) n x 1 := by
  have hKv : bmK R romStack stack0 = 0xBE80 + 0x150 + R + romStack + stack0 := rfl
  have hFk : F.toNat + 0xBE80 < 2 ^ 32 := by rw [hF]; exact top.isLt
  have hW : (top - BitVec.ofNat 32 (bmK R romStack stack0)).toNat = top.toNat - bmK R romStack stack0 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, hKv]; omega
  rw [BitVec.add_assoc, ofNat_add_ofNat]
  refine bmt_sep_in hx ?_ ?_
  · rw [hW, bmd_eF hFk (by omega), hKv]; omega
  · rw [hW, bmd_eF hFk (by omega), hKv]; omega

theorem bmq_ne {a x : Word} (h : Sep a 1 x 1) : x ≠ a :=
  fun e => h 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)

/-- The three plan bytes at `F + 0xB9A8 + 0x12F` lie inside the stack. -/
theorem bmq_keep3 {M0 M : Word → BitVec 8} {F top : Word} {R romStack stack0 : Nat}
    (hF : F.toNat + 0xBE80 = top.toNat) (hlo : 0x3FCC8000 + bmK R romStack stack0 ≤ top.toNat)
    (hK : BmKeep M0 M (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    (v1 v2 v3 : BitVec 8) :
    BmKeep M0 (memStore8 (memStore8 (memStore8 M (F + BitVec.ofNat 32 0xB9A8 + 0x12F) v1)
      (F + BitVec.ofNat 32 0xB9A8 + 0x130) v2) (F + BitVec.ofNat 32 0xB9A8 + 0x131) v3)
      (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) :=
  hK.step fun x hx => by
    rw [memStore8_ne (a := F + BitVec.ofNat 32 0xB9A8 + 0x131) (bmq_ne (bmq_kin (c := 0x131) hF hlo (by decide) hx)),
      memStore8_ne (a := F + BitVec.ofNat 32 0xB9A8 + 0x130) (bmq_ne (bmq_kin (c := 0x130) hF hlo (by decide) hx)),
      memStore8_ne (a := F + BitVec.ofNat 32 0xB9A8 + 0x12F) (bmq_ne (bmq_kin (c := 0x12F) hF hlo (by decide) hx))]

/-! ## No trial -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- From 0x180, when the state has no trial: `boot_main` stores the plan's
bytes and tries the preferred slot. -/
theorem bmq_none {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    {Q : Prop} (X : BmHypQ Q flash pinned policy M0 top R romStack stack0 romBase romCode E)
    {n : Machine} {F : Word} (s : St n.mem BM n 0x180 (reg n)) (hF : F.toNat + 0xBE80 = top.toNat)
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    {st : State} (hst : (bmRecs flash).1 = st) (hv : BmdValid st) (htr : st.trial = none)
    (P : BmqPre flash M0 F st (reg n)) (h24 : reg n 24 = BitVec.ofNat 32 st.generation + 1) :
    BmEnd Q (BmJump flash pinned policy M0 top (bmK R romStack stack0)) n := by
  have C := X.env
  have hhi := C.hhi; have hlo := C.hlo
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  have hS : ∀ c, c + 1 ≤ 0x4D8 → Sep (reg n 20 + BitVec.ofNat 32 c) 1 BM bootMainCode.length :=
    fun c hc' => by rw [P.r20]; exact bmq_lowS hF hhi hc'
  obtain ⟨n1, c1, u1⟩ := s.block bmB16 hc bmB16_end
    ⟨trivial, hS 0x12F (by decide), hS 0x130 (by decide), hS 0x131 (by decide), trivial, trivial⟩
  have r1 : ∀ r, reg n1 r = (runBlock bmB16 (n.mem, reg n)).2 r := fun r => by rw [u1.regs]
  have m1 : n1.mem = memStore8 (memStore8 (memStore8 n.mem (reg n 20 + 0x12F) ((reg n a0).extractLsb' 0 8))
      (reg n 20 + 0x130) ((reg n 21).extractLsb' 0 8)) (reg n 20 + 0x131) ((reg n x0).extractLsb' 0 8) := by
    rw [u1.mem]; rfl
  rw [P.r20] at m1
  have t1 : St n1.mem BM n1 0x190 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ r, r ≠ 25 → r ≠ 8 → reg n1 r = reg n r := fun r h1 h2 => by
    rw [r1, runBlock_reg _ _ _ r s.zero (by simp only [bmB16]; revert h1 h2; revert r; decide)]
  have hK1 : BmKeep M0 n1.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [m1]; exact bmq_keep3 hF hlo hK _ _ _
  have h8 : reg n1 8 = BitVec.ofNat 32 (bmSlotNum st.preferred) := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB16, upd, ↓reduceIte]
    (try rw [s.zero]); exact (BitVec.zero_add _).trans P.r21
  have h25 : reg n1 25 = 0 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB16, upd, ↓reduceIte]
    (try rw [s.zero]); rfl
  have hpl := bmq_plan_none htr
  have P1 : BmdPre flash M0 F st (reg n1) :=
    (P.keep fun q hq => k1 q (by rintro rfl; exact absurd hq (by decide))
      (by rintro rfl; exact absurd hq (by decide))).up
      (by rw [h8, hpl]; exact bmq_and_small (Nat.lt_of_le_of_lt (bmd_slot_le _) (by decide)))
      (by rw [k1 24 (by decide) (by decide)]; exact h24) (by rw [h25, hpl]; rfl)
  have hc1 := hK1.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  obtain ⟨n2, e2, t2⟩ := t1.jump hc1 bm_at_190 (off' := 0x1F4) (by decide) (by rw [t1.pc]; decide)
  refine BmEnd.pre (c1.trans (.single e2)) ?_
  rw [← t2.mem] at hK1
  exact bmd_main X ⟨t2.pc, rfl, fun _ => rfl⟩ hF hK1 hst hv (P1.keep fun q _ => t2.regs q)

/-! ## A trial with boots left -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- From 0x1E2, when the state's trial has boots left: `boot_main` stores
the plan's bytes and tries the trial's slot. -/
theorem bmq_live {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    {Q : Prop} (X : BmHypQ Q flash pinned policy M0 top R romStack stack0 romBase romCode E)
    {n : Machine} {F : Word} (s : St n.mem BM n 0x1E2 (reg n)) (hF : F.toNat + 0xBE80 = top.toNat)
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    {st : State} (hst : (bmRecs flash).1 = st) (hv : BmdValid st) {t : Trial} (htr : st.trial = some t)
    (hb : 0 < t.bootsLeft)
    (P : BmqPre flash M0 F st (reg n)) (h24 : reg n 24 = BitVec.ofNat 32 st.generation + 1) :
    BmEnd Q (BmJump flash pinned policy M0 top (bmK R romStack stack0)) n := by
  have C := X.env
  have hhi := C.hhi; have hlo := C.hlo
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  have hS : ∀ c, c + 1 ≤ 0x4D8 → Sep (reg n 20 + BitVec.ofNat 32 c) 1 BM bootMainCode.length :=
    fun c hc' => by rw [P.r20]; exact bmq_lowS hF hhi hc'
  obtain ⟨n1, c1, u1⟩ := s.block bmB20 hc bmB20_end
    ⟨trivial, trivial, hS 0x12F (by decide), hS 0x130 (by decide), hS 0x131 (by decide), trivial, trivial⟩
  have r1 : ∀ r, reg n1 r = (runBlock bmB20 (n.mem, reg n)).2 r := fun r => by rw [u1.regs]
  obtain ⟨v1, v2, v3, m1⟩ : ∃ v1 v2 v3, n1.mem = memStore8 (memStore8 (memStore8 n.mem (reg n 20 + 0x12F) v1)
      (reg n 20 + 0x130) v2) (reg n 20 + 0x131) v3 := ⟨_, _, _, by rw [u1.mem]; rfl⟩
  rw [P.r20] at m1
  have t1 : St n1.mem BM n1 0x1F4 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ r, r ≠ 25 → r ≠ 8 → r ≠ a0 → reg n1 r = reg n r := fun r h1 h2 h3 => by
    rw [r1, runBlock_reg _ _ _ r s.zero (by simp only [bmB20]; revert h1 h2 h3; revert r; decide)]
  have hK1 : BmKeep M0 n1.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [m1]; exact bmq_keep3 hF hlo hK _ _ _
  have h8 : reg n1 8 = bmWord st := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB20, upd, ↓reduceIte]
    (try rw [s.zero]); exact (BitVec.zero_add _).trans P.r9
  have h25 : reg n1 25 = 1 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB20, upd, ↓reduceIte]
    (try rw [s.zero]); rfl
  have hpl := bmq_plan_live htr hb
  have P1 : BmdPre flash M0 F st (reg n1) :=
    (P.keep fun q hq => k1 q (by rintro rfl; exact absurd hq (by decide))
      (by rintro rfl; exact absurd hq (by decide)) (by rintro rfl; exact absurd hq (by decide))).up
      (by rw [h8, hpl, bmq_word_lo, htr]; rfl)
      (by rw [k1 24 (by decide) (by decide) (by decide)]; exact h24) (by rw [h25, hpl]; rfl)
  refine BmEnd.pre c1 ?_
  exact bmd_main X t1 hF hK1 hst hv P1

/-! ## An expired trial -/

set_option maxRecDepth 20000 in
/-- The word at +4 of the record that ends a trial: no trial, no boots,
the confirmed bits, and the preferred slot. -/
theorem bmq_exw : ∀ c, c < 4 → ∀ p, p < 2 →
    (aluEval .add (aluEval .or (aluEval .sll (aluEval .and (BitVec.ofNat 32 (c + 256 * p)) 255) 16)
      (aluEval .sll (BitVec.ofNat 32 p) 24)) 2).extractLsb' 0 8 = 2 ∧
    (aluEval .add (aluEval .or (aluEval .sll (aluEval .and (BitVec.ofNat 32 (c + 256 * p)) 255) 16)
      (aluEval .sll (BitVec.ofNat 32 p) 24)) 2).extractLsb' 8 8 = 0 ∧
    (aluEval .add (aluEval .or (aluEval .sll (aluEval .and (BitVec.ofNat 32 (c + 256 * p)) 255) 16)
      (aluEval .sll (BitVec.ofNat 32 p) 24)) 2).extractLsb' 16 8 = BitVec.ofNat 8 c ∧
    (aluEval .add (aluEval .or (aluEval .sll (aluEval .and (BitVec.ofNat 32 (c + 256 * p)) 255) 16)
      (aluEval .sll (BitVec.ofNat 32 p) 24)) 2).extractLsb' 24 8 = BitVec.ofNat 8 p := by
  decide

theorem bmq_beq : ∀ p, p < 2 → branchTaken .beq (BitVec.ofNat 32 p) 2 = false := by decide

/-- The four stores that end a trial: the generation word, the word at +4,
and the two plan bytes after the record. -/
theorem bmq_rec_ex (M : Word → BitVec 8) (b g w : Word) (b8 b9 : BitVec 8) :
    memLoad32 (memStore8 (memStore8 (memStore32 (memStore32 M b g) (b + 4) w) (b + 8) b8) (b + 9) b9) b = g ∧
    memStore8 (memStore8 (memStore32 (memStore32 M b g) (b + 4) w) (b + 8) b8) (b + 9) b9 (b + 4) =
      w.extractLsb' 0 8 ∧
    memStore8 (memStore8 (memStore32 (memStore32 M b g) (b + 4) w) (b + 8) b8) (b + 9) b9 (b + 5) =
      w.extractLsb' 8 8 ∧
    memStore8 (memStore8 (memStore32 (memStore32 M b g) (b + 4) w) (b + 8) b8) (b + 9) b9 (b + 6) =
      w.extractLsb' 16 8 ∧
    memStore8 (memStore8 (memStore32 (memStore32 M b g) (b + 4) w) (b + 8) b8) (b + 9) b9 (b + 7) =
      w.extractLsb' 24 8 ∧
    ∀ x, Sep b 10 x 1 →
      memStore8 (memStore8 (memStore32 (memStore32 M b g) (b + 4) w) (b + 8) b8) (b + 9) b9 x = M x := by
  have nb : ∀ c d : Nat, c < 10 → d < 10 → c ≠ d → b + BitVec.ofNat 32 c ≠ b + BitVec.ofNat 32 d :=
    fun c d hc hd h => add_ofNat_ne b (Nat.lt_trans hc (by decide)) (Nat.lt_trans hd (by decide)) h
  have a1 : b + 4 + 1 = b + 5 := by rw [BitVec.add_assoc]; rfl
  have a2 : b + 4 + 2 = b + 6 := by rw [BitVec.add_assoc]; rfl
  have a3 : b + 4 + 3 = b + 7 := by rw [BitVec.add_assoc]; rfl
  have e32 : memStore32 (memStore32 M b g) (b + 4) w = memStore8 (memStore8 (memStore8 (memStore8
      (memStore32 M b g) (b + 4) (w.extractLsb' 0 8)) (b + 5) (w.extractLsb' 8 8)) (b + 6) (w.extractLsb' 16 8))
      (b + 7) (w.extractLsb' 24 8) := by
    rw [memStore32, a1, a2, a3]
  rw [e32]
  have s9 : Sep (b + 9) 1 b 4 := by
    have := sep_offsets b (c := 9) (n := 1) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have s8 : Sep (b + 8) 1 b 4 := by
    have := sep_offsets b (c := 8) (n := 1) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have s7 : Sep (b + 7) 1 b 4 := by
    have := sep_offsets b (c := 7) (n := 1) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have s6 : Sep (b + 6) 1 b 4 := by
    have := sep_offsets b (c := 6) (n := 1) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have s5 : Sep (b + 5) 1 b 4 := by
    have := sep_offsets b (c := 5) (n := 1) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have s4 : Sep (b + 4) 1 b 4 := by
    have := sep_offsets b (c := 4) (n := 1) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, fun x hx => ?_⟩
  · rw [memLoad32_store8_sep s9, memLoad32_store8_sep s8, memLoad32_store8_sep s7, memLoad32_store8_sep s6,
      memLoad32_store8_sep s5, memLoad32_store8_sep s4, memLoad32_store32_same]
  · rw [memStore8_ne (x := b + 4) (a := b + 9) (nb 4 9 (by decide) (by decide) (by decide)), memStore8_ne (x := b + 4) (a := b + 8) (nb 4 8 (by decide) (by decide) (by decide)),
      memStore8_ne (x := b + 4) (a := b + 7) (nb 4 7 (by decide) (by decide) (by decide)), memStore8_ne (x := b + 4) (a := b + 6) (nb 4 6 (by decide) (by decide) (by decide)),
      memStore8_ne (x := b + 4) (a := b + 5) (nb 4 5 (by decide) (by decide) (by decide)), memStore8_same]
  · rw [memStore8_ne (x := b + 5) (a := b + 9) (nb 5 9 (by decide) (by decide) (by decide)), memStore8_ne (x := b + 5) (a := b + 8) (nb 5 8 (by decide) (by decide) (by decide)),
      memStore8_ne (x := b + 5) (a := b + 7) (nb 5 7 (by decide) (by decide) (by decide)), memStore8_ne (x := b + 5) (a := b + 6) (nb 5 6 (by decide) (by decide) (by decide)),
      memStore8_same]
  · rw [memStore8_ne (x := b + 6) (a := b + 9) (nb 6 9 (by decide) (by decide) (by decide)), memStore8_ne (x := b + 6) (a := b + 8) (nb 6 8 (by decide) (by decide) (by decide)),
      memStore8_ne (x := b + 6) (a := b + 7) (nb 6 7 (by decide) (by decide) (by decide)), memStore8_same]
  · rw [memStore8_ne (x := b + 7) (a := b + 9) (nb 7 9 (by decide) (by decide) (by decide)), memStore8_ne (x := b + 7) (a := b + 8) (nb 7 8 (by decide) (by decide) (by decide)),
      memStore8_same]
  · have o : ∀ c, c < 10 → x ≠ b + BitVec.ofNat 32 c := fun c hc e =>
      hx c hc 0 (by decide) (by rw [add_ofNat_zero]; exact e.symm)
    rw [memStore8_ne (a := b + 9) (o 9 (by decide)), memStore8_ne (a := b + 8) (o 8 (by decide)), memStore8_ne (a := b + 7) (o 7 (by decide)),
      memStore8_ne (a := b + 6) (o 6 (by decide)), memStore8_ne (a := b + 5) (o 5 (by decide)), memStore8_ne (a := b + 4) (o 4 (by decide)),
      memStore32_ne (fun i hi => o i (Nat.lt_trans hi (by decide)))]

theorem bmq_rom : ∀ q, bmqRegs q = true → romKeep q = true := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- From 0x198, when the state's trial has no boots left: `boot_main` writes
the state without the trial at `F + 0xBAD0`, stores the plan's bytes, and
tries the preferred slot. -/
theorem bmq_exp {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    {Q : Prop} (X : BmHypQ Q flash pinned policy M0 top R romStack stack0 romBase romCode E)
    {n : Machine} {F : Word} (s : St n.mem BM n 0x198 (reg n)) (hF : F.toNat + 0xBE80 = top.toNat)
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    {st : State} (hst : (bmRecs flash).1 = st) (hv : BmdValid st) {t : Trial} (htr : st.trial = some t)
    (hb : t.bootsLeft = 0)
    (P : BmqPre flash M0 F st (reg n)) (h24 : reg n 24 = BitVec.ofNat 32 st.generation + 1) :
    BmEnd Q (BmJump flash pinned policy M0 top (bmK R romStack stack0)) n := by
  have C := X.env
  have hhi := C.hhi; have hlo := C.hlo; have h16 := C.hsp
  have hF16 : F.toNat % 16 = 0 := by
    rw [← hF, show (48768 : Nat) = 16 * 3048 from rfl, Nat.add_mul_mod_self_left] at h16; exact h16
  have hFk : F.toNat + 0xBE80 < 2 ^ 32 := by rw [hF]; exact top.isLt
  have hal1 : (reg n 20 + 0x128).toNat % 4 = 0 := by
    rw [P.r20, BitVec.add_assoc]; exact bmp_align hF16 hFk (by decide) (by decide)
  have hal2 : (reg n 20 + 0x12C).toNat % 4 = 0 := by
    rw [P.r20, BitVec.add_assoc]; exact bmp_align hF16 hFk (by decide) (by decide)
  clear h16 hF16
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  have hS : ∀ c, c + 1 ≤ 0x4D8 → Sep (reg n 20 + BitVec.ofNat 32 c) 1 BM bootMainCode.length :=
    fun c hc' => by rw [P.r20]; exact bmq_lowS hF hhi hc'
  have hS4 : ∀ c, c + 4 ≤ 0x4D8 → Sep (reg n 20 + BitVec.ofNat 32 c) 4 BM bootMainCode.length :=
    fun c hc' => by rw [P.r20]; exact bmq_lowS hF hhi hc'
  obtain ⟨n1, c1, u1⟩ := s.block bmB18 hc bmB18_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      ⟨hal1, hS4 0x128 (by decide)⟩, ⟨hal2, hS4 0x12C (by decide)⟩, hS 0x130 (by decide),
      hS 0x131 (by decide), trivial, trivial⟩
  have r1 : ∀ r, reg n1 r = (runBlock bmB18 (n.mem, reg n)).2 r := fun r => by rw [u1.regs]
  have m1 : n1.mem = memStore8 (memStore8 (memStore32 (memStore32 n.mem (reg n 20 + 296)
      (aluEval AluOp.or (aluEval AluOp.add (aluEval AluOp.sltu 0 (reg n 24)) 4294967295) (reg n 24)))
      (reg n 20 + 300) (aluEval AluOp.add (aluEval AluOp.or (aluEval AluOp.sll (aluEval AluOp.and (reg n 19) 255) 16)
        (aluEval AluOp.sll (reg n 21) 24)) 2))
      (reg n 20 + 304) ((reg n 21).extractLsb' 0 8)) (reg n 20 + 305) ((0 : Word).extractLsb' 0 8) := by
    rw [u1.mem]; rfl
  have t1 : St n1.mem BM n1 0x1C6 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ r, r ≠ 25 → r ≠ 8 → r ≠ a0 → r ≠ a1 → r ≠ a2 → reg n1 r = reg n r := fun r h1 h2 h3 h4 h5 => by
    rw [r1, runBlock_reg _ _ _ r s.zero (by simp only [bmB18]; revert h1 h2 h3 h4 h5; revert r; decide)]
  have ha2 : reg n1 a2 = 2 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB18, upd, ↓reduceIte]
  have hc4 : st.confirmed < 4 := hv.2.1
  have hp2 : bmSlotNum st.preferred < 2 := Nat.lt_succ_of_le (bmd_slot_le _)
  have hgen := hv.1
  -- The record at `F + 0xBAD0`.
  have e0 : F + BitVec.ofNat 32 0xB9A8 + 296 = F + BitVec.ofNat 32 0xBAD0 := by rw [BitVec.add_assoc]; rfl
  have e4 : F + BitVec.ofNat 32 0xB9A8 + 300 = F + BitVec.ofNat 32 0xBAD0 + 4 := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have e8 : F + BitVec.ofNat 32 0xB9A8 + 304 = F + BitVec.ofNat 32 0xBAD0 + 8 := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have e9 : F + BitVec.ofNat 32 0xB9A8 + 305 = F + BitVec.ofNat 32 0xBAD0 + 9 := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  rw [P.r20, e0, e4, e8, e9, P.r19, P.r21, h24, bmd_sat hgen] at m1
  obtain ⟨hw1, hw2, hw3, hw4⟩ := bmq_exw _ hc4 _ hp2
  obtain ⟨l0, l4, l5, l6, l7, lout⟩ := bmq_rec_ex n.mem (F + BitVec.ofNat 32 0xBAD0) _ _ _ _
  rw [← m1, hw1] at l4
  rw [← m1, hw2] at l5
  rw [← m1, hw3] at l6
  rw [← m1, hw4] at l7
  rw [← m1] at l0 lout
  have hgl : min (st.generation + 1) maxGeneration < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  have hrec : bmrSt n1.mem (F + BitVec.ofNat 32 0xBAD0) = st.withoutTrial := by
    rw [bmrSt, l0, l4, l6, l7, bmd_toNat8 (Nat.lt_trans hp2 (by decide)),
      bmd_toNat8 (Nat.lt_trans hc4 (by decide)), BitVec.toNat_ofNat, Nat.mod_eq_of_lt hgl,
      ite_eq_right_of_eq_false _ _ (eq_false (by decide)), bmd_slot_num]
    rfl
  have hval : BmwValid n1.mem (F + BitVec.ofNat 32 0xBAD0) := by
    rw [BmwValid, l4, l5, l6, l7, bmd_toNat8 (Nat.lt_trans hp2 (by decide)),
      bmd_toNat8 (Nat.lt_trans hc4 (by decide))]
    exact ⟨Nat.le_of_lt_succ hp2, Nat.le_of_lt_succ hc4, .inr rfl⟩
  clear hgl
  have hK1 : BmKeep M0 n1.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) :=
    hK.step fun x hx => lout x (by
      have := bmq_kin (c := 0x128) (n := 10) hF hlo (by decide) hx
      rwa [BitVec.add_assoc] at this)
  have hpl := bmq_plan_exp htr hb
  have hW : (bmDecision flash M0 fun _ => none).write = some st.withoutTrial := by
    rw [bmd_dec_rej hst rfl, hpl]; rfl
  -- 0x1C6: the preferred slot is never 2.
  have hc1 := hK1.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  obtain ⟨n2, e2, t2⟩ := t1.notTaken hc1 0x1CA bm_at_1c6 (by decide)
    (by rw [ha2, k1 21 (by decide) (by decide) (by decide) (by decide) (by decide), P.r21]; exact bmq_beq _ hp2)
  rw [← t2.mem] at hc1 hK1 hrec hval
  have P1 : BmqPre flash M0 F st (reg n1) := P.keep fun q hq => k1 q (by rintro rfl; exact absurd hq (by decide))
    (by rintro rfl; exact absurd hq (by decide)) (by rintro rfl; exact absurd hq (by decide))
    (by rintro rfl; exact absurd hq (by decide)) (by rintro rfl; exact absurd hq (by decide))
  have h24' : reg n1 24 = BitVec.ofNat 32 st.generation + 1 := by
    rw [k1 24 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h24
  -- 0x1CA: the arguments of the write.
  have t2' : St n2.mem BM n2 0x1CA (reg n1) := ⟨t2.pc, rfl, fun r => t2.regs r⟩
  obtain ⟨n3, c3, u3⟩ := t2'.block bmB19 hc1 bmB19_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r3 : ∀ r, reg n3 r = (runBlock bmB19 (n2.mem, reg n1)).2 r := fun r => by rw [u3.regs]
  have m3 : n3.mem = n2.mem := u3.mem
  have t3 : St n3.mem BM n3 0x1D6 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have k3 : ∀ r, r ≠ a0 → r ≠ a1 → reg n3 r = reg n1 r := fun r h1 h2 => by
    rw [r3, runBlock_reg _ _ _ r t1.zero (by simp only [bmB19]; revert h1 h2; revert r; decide)]
  have P3 : BmqPre flash M0 F st (reg n3) := P1.keep fun q hq => k3 q
    (by rintro rfl; exact absurd hq (by decide)) (by rintro rfl; exact absurd hq (by decide))
  have a0_3 : reg n3 a0 = bmCopy (bmRecs flash).2 := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, bmB19, upd, ↓reduceIte]
    (try rw [t1.zero]); exact (BitVec.zero_add _).trans P1.r18
  have a1_3 : reg n3 a1 = F + BitVec.ofNat 32 0xBAD0 := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, bmB19, upd, ↓reduceIte]; rw [P1.rsp]; rfl
  rw [← m3] at hc1 hK1 hrec hval
  obtain ⟨n4, c4, t4, keep4, hK4, _⟩ := bmw_call X t3 P3.rsp hF hK1 (j := 0xBAD0) (by decide) (by decide)
    a0_3 a1_3 bm_none_sound hW hrec hval bm_at_1d6 bm_at_1da (by decide) (by decide)
  have P4 : BmqPre flash M0 F st (reg n4) := P3.keep fun q hq => keep4 q (bmq_rom q hq)
  have h24_4 : reg n4 24 = BitVec.ofNat 32 st.generation + 1 := by
    rw [keep4 24 (by decide), k3 24 (by decide) (by decide)]; exact h24'
  -- 0x1DE: no trial, then on to 0x18E.
  have hc4' := hK4.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  obtain ⟨n5, c5, u5⟩ := t4.block bmB19b hc4' bmB19b_end ⟨trivial, trivial⟩
  have r5 : ∀ r, reg n5 r = (runBlock bmB19b (n4.mem, reg n4)).2 r := fun r => by rw [u5.regs]
  have m5 : n5.mem = n4.mem := u5.mem
  have t5 : St n5.mem BM n5 0x1E0 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have k5 : ∀ r, r ≠ 25 → reg n5 r = reg n4 r := fun r h1 => by
    rw [r5, runBlock_reg _ _ _ r t4.zero (by simp only [bmB19b]; revert h1; revert r; decide)]
  have h25 : reg n5 25 = 0 := by
    rw [r5]; simp +decide only [runBlock, BInstr.run, bmB19b, upd, ↓reduceIte]
    (try rw [t4.zero]); rfl
  rw [← m5] at hc4' hK4
  obtain ⟨n6, e6, t6⟩ := t5.jump hc4' bm_at_1e0 (off' := 0x18E) (by decide) (by rw [t5.pc]; decide)
  rw [← t6.mem] at hc4' hK4
  have t6' : St n6.mem BM n6 0x18E (reg n6) := ⟨t6.pc, rfl, fun _ => rfl⟩
  have k6 : ∀ r, reg n6 r = reg n5 r := t6.regs
  obtain ⟨n7, c7, u7⟩ := t6'.block bmB19c hc4' bmB19c_end ⟨trivial, trivial⟩
  have r7 : ∀ r, reg n7 r = (runBlock bmB19c (n6.mem, reg n6)).2 r := fun r => by rw [u7.regs]
  have m7 : n7.mem = n6.mem := u7.mem
  have t7 : St n7.mem BM n7 0x190 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have k7 : ∀ r, r ≠ 8 → reg n7 r = reg n6 r := fun r h1 => by
    rw [r7, runBlock_reg _ _ _ r t6'.zero (by simp only [bmB19c]; revert h1; revert r; decide)]
  have h8 : reg n7 8 = BitVec.ofNat 32 (bmSlotNum st.preferred) := by
    rw [r7]; simp +decide only [runBlock, BInstr.run, bmB19c, upd, ↓reduceIte]
    (try rw [t6'.zero]); exact (BitVec.zero_add _).trans (by rw [k6, k5 21 (by decide)]; exact P4.r21)
  have P7 : BmdPre flash M0 F st (reg n7) :=
    (P4.keep fun q hq => by
      rw [k7 q (by rintro rfl; exact absurd hq (by decide)), k6, k5 q (by rintro rfl; exact absurd hq (by decide))]).up
      (by rw [h8, hpl]; exact bmq_and_small (Nat.lt_trans hp2 (by decide)))
      (by rw [k7 24 (by decide), k6, k5 24 (by decide)]; exact h24_4)
      (by rw [k7 25 (by decide), k6, h25, hpl]; rfl)
  rw [← m7] at hc4' hK4
  obtain ⟨n8, e8, t8⟩ := t7.jump hc4' bm_at_190 (off' := 0x1F4) (by decide) (by rw [t7.pc]; decide)
  rw [← t8.mem] at hK4
  refine BmEnd.pre (c1.trans ((Steps.single e2).trans (c3.trans (c4.trans (c5.trans
    ((Steps.single e6).trans (c7.trans (.single e8)))))))) ?_
  exact bmd_main X ⟨t8.pc, rfl, fun _ => rfl⟩ hF hK4 hst hv (P7.keep fun q _ => t8.regs q)

/-! ## The plan -/

theorem bmq_tb_ne (sl : Slot) : BitVec.ofNat 32 (bmSlotNum sl) ≠ 2 := by cases sl <;> decide

theorem bmq_nz : ∀ b, b < 4 → 0 < b → BitVec.ofNat 32 b ≠ 0 := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **`boot_main` from 0x174**, with the state that `bootstate::read`
returned and its generation in s8: `boot_main` plans the boot (`plan`),
writes the state without an expired trial, and goes on to check the plan's
first slot. It jumps only into a slot that `decideBoot` boots, or halts. -/
theorem bmq_plan {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    {Q : Prop} (X : BmHypQ Q flash pinned policy M0 top R romStack stack0 romBase romCode E)
    {n : Machine} {F : Word} (s : St n.mem BM n 0x174 (reg n)) (hF : F.toNat + 0xBE80 = top.toNat)
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    {st : State} (hst : (bmRecs flash).1 = st) (hv : BmdValid st)
    (P : BmqPre flash M0 F st (reg n)) (h24 : reg n 24 = BitVec.ofNat 32 st.generation) :
    BmEnd Q (BmJump flash pinned policy M0 top (bmK R romStack stack0)) n := by
  have C := X.env
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  obtain ⟨n1, c1, u1⟩ := s.block bmB15 hc bmB15_end ⟨trivial, trivial, trivial, trivial⟩
  have r1 : ∀ r, reg n1 r = (runBlock bmB15 (n.mem, reg n)).2 r := fun r => by rw [u1.regs]
  have m1 : n1.mem = n.mem := u1.mem
  have t1 : St n1.mem BM n1 0x17C (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ r, r ≠ a1 → r ≠ a0 → r ≠ 24 → reg n1 r = reg n r := fun r h1 h2 h3 => by
    rw [r1, runBlock_reg _ _ _ r s.zero (by simp only [bmB15]; revert h1 h2 h3; revert r; decide)]
  have ha1 : reg n1 a1 = BitVec.ofNat 32 (bmTrialBytes st.trial).1 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB15, upd, ↓reduceIte]
    rw [P.r9]; exact bmq_word_lo st
  have ha0 : reg n1 a0 = 2 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB15, upd, ↓reduceIte]
  have h24' : reg n1 24 = BitVec.ofNat 32 st.generation + 1 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB15, upd, ↓reduceIte]
    rw [h24]; rfl
  have P1 : BmqPre flash M0 F st (reg n1) := P.keep fun q hq => k1 q
    (by rintro rfl; exact absurd hq (by decide)) (by rintro rfl; exact absurd hq (by decide))
    (by rintro rfl; exact absurd hq (by decide))
  rw [← m1] at hc hK
  cases htr : st.trial with
  | none =>
    obtain ⟨n2, e2, t2⟩ := t1.notTaken hc 0x180 bm_at_17c (by decide) (by rw [ha1, ha0, htr]; rfl)
    refine BmEnd.pre (c1.trans (.single e2)) ?_
    rw [← t2.mem] at hK
    exact bmq_none X ⟨t2.pc, rfl, fun _ => rfl⟩ hF hK hst hv htr (P1.keep fun q _ => t2.regs q)
      (by rw [t2.regs]; exact h24')
  | some t =>
    obtain ⟨n2, e2, t2⟩ := t1.taken hc 0x192 bm_at_17c (by decide)
      (by rw [ha1, ha0, htr]; exact bne_iff_ne.mpr (bmq_tb_ne t.slot))
    rw [← t2.mem] at hc hK
    have t2' : St n2.mem BM n2 0x192 (reg n2) := ⟨t2.pc, rfl, fun _ => rfl⟩
    have P2 : BmqPre flash M0 F st (reg n2) := P1.keep fun q _ => t2.regs q
    obtain ⟨n3, c3, u3⟩ := t2'.block bmB17 hc bmB17_end ⟨trivial, trivial⟩
    have r3 : ∀ r, reg n3 r = (runBlock bmB17 (n2.mem, reg n2)).2 r := fun r => by rw [u3.regs]
    have m3 : n3.mem = n2.mem := u3.mem
    have t3 : St n3.mem BM n3 0x196 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
    have k3 : ∀ r, r ≠ a0 → reg n3 r = reg n2 r := fun r h1 => by
      rw [r3, runBlock_reg _ _ _ r t2'.zero (by simp only [bmB17]; revert h1; revert r; decide)]
    have hb3 : t.bootsLeft < 4 := Nat.lt_succ_of_le (hv.2.2 t htr)
    have ha0' : reg n3 a0 = BitVec.ofNat 32 t.bootsLeft := by
      rw [r3]; simp +decide only [runBlock, BInstr.run, bmB17, upd, ↓reduceIte]
      rw [P2.r22, htr]; exact bmq_s6_lo _ _ _ (Nat.lt_trans hb3 (by decide))
    have P3 : BmqPre flash M0 F st (reg n3) := P2.keep fun q hq => k3 q
      (by rintro rfl; exact absurd hq (by decide))
    have h24_3 : reg n3 24 = BitVec.ofNat 32 st.generation + 1 := by
      rw [k3 24 (by decide), t2.regs]; exact h24'
    rw [← m3] at hc hK
    rcases Nat.eq_zero_or_pos t.bootsLeft with hb | hb
    · obtain ⟨n4, e4, t4⟩ := t3.notTaken hc 0x198 bm_at_196 (by decide)
        (by rw [ha0', t3.zero, hb]; rfl)
      refine BmEnd.pre (c1.trans ((Steps.single e2).trans (c3.trans (.single e4)))) ?_
      rw [← t4.mem] at hK
      exact bmq_exp X ⟨t4.pc, rfl, fun _ => rfl⟩ hF hK hst hv htr hb (P3.keep fun q _ => t4.regs q)
        (by rw [t4.regs]; exact h24_3)
    · obtain ⟨n4, e4, t4⟩ := t3.taken hc 0x1E2 bm_at_196 (by decide)
        (by rw [ha0', t3.zero]; exact bne_iff_ne.mpr (bmq_nz _ hb3 hb))
      refine BmEnd.pre (c1.trans ((Steps.single e2).trans (c3.trans (.single e4)))) ?_
      rw [← t4.mem] at hK
      exact bmq_live X ⟨t4.pc, rfl, fun _ => rfl⟩ hF hK hst hv htr hb (P3.keep fun q _ => t4.regs q)
        (by rw [t4.regs]; exact h24_3)

end C3.RV32.Cur
