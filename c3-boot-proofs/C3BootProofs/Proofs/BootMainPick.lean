import C3BootProofs.Proofs.BootMainTail

/-!
# `boot_main`: the level target and the chosen slot

When the first closure accepts a slot, `boot_main` computes the level target
for `boot` from the slot's security version, the slot's confirmed bit, and
the entry level, copies the slot's `Accepted` bytes to the argument buffer,
and goes on at 0x348. `bmp_first` covers this from 0x2C2, for the plan's
first slot, and `bmp_other` from 0x304, for the other slot.
-/

namespace C3.RV32.Cur

open C3 C3.Image C3.RV32.BootMainContract

theorem bmp_level (M0 : Word → BitVec 8) :
    btPop (memLoad32 M0 efuseRd) = BitVec.ofNat 32 (bmLevel M0) :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm)

theorem bmp_zext {sv : Nat} (h : sv ≤ 16) : (BitVec.ofNat 8 sv).zeroExtend 32 = BitVec.ofNat 32 sv := by
  have k : ∀ v, v < 17 → (BitVec.ofNat 8 v).zeroExtend 32 = BitVec.ofNat 32 v := by decide
  exact k sv (by omega)

theorem bmp_andff {sv : Nat} (cf : Bool) (h : sv ≤ 16) :
    aluEval .and (if cf = true then BitVec.ofNat 32 sv else 0) 0xFF =
      (if cf = true then BitVec.ofNat 32 sv else 0) := by
  cases cf
  · exact BitVec.zero_and
  · exact bmt_lowbyte h

theorem bmp_target_le {sv L : Nat} (cf : Bool) (hL : L ≤ sv) (hsv : sv ≤ 16) : burnTarget sv cf L ≤ 16 := by
  unfold burnTarget
  cases cf
  · exact Nat.le_trans hL hsv
  · simp only [Bool.true_and]
    cases decide (L < sv)
    · exact Nat.le_trans hL hsv
    · exact hsv

theorem bmp_align {F k : Word} (hF : F.toNat % 16 = 0) (hFk : F.toNat + 0xBE80 < 2 ^ 32) (hk : k.toNat ≤ 0xBE80)
    (h4 : k.toNat % 4 = 0) : (F + k).toNat % 4 = 0 := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (a := F.toNat + k.toNat) (by omega)]; omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **`boot_main` from 0x2C2**, when the first closure accepted the plan's
first slot: the slot's number in `s0`, the decoded state's confirmed bits
`c` in `s3`, the slot's security version in `s10`, the entry level in `s7`,
and the slot's `Accepted` bytes at `F + 0xBBF0`. -/
theorem bmp_first {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    {Q : Prop} (X : BmHypQ Q flash pinned policy M0 top R romStack stack0 romBase romCode E)
    {n : Machine} {F : Word} (s : St n.mem BM n 0x2C2 (reg n)) (hsp : reg n sp = F)
    (hF : F.toNat + 0xBE80 = top.toNat)
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    {slot : Slot} {mf : Manifest} {sv t c p : Nat} (hc4 : c < 4) (hp : p ≤ 1)
    (hA : bmcAccept flash pinned policy (bmLevel M0) (BitVec.ofNat 32 (bmSlotNum slot)) = some (mf, sv, t))
    {ck : Slot → Option Nat} (hck : BmSound flash pinned policy M0 ck)
    (hD : (bmDecision flash M0 ck).outcome = .boot slot (burnTarget sv (c &&& slot.bit != 0) (bmLevel M0)))
    (hAcc : AccOk flash (BitVec.ofNat 32 (bmSlotNum slot)) mf n.mem (F + BitVec.ofNat 32 0xBBF0))
    (hlw : memLoad32 n.mem (F + BitVec.ofNat 32 0xBD10) =
      BitVec.ofNat 32 (bmcBase (BitVec.ofNat 32 (bmSlotNum slot)) + mf.image.offset))
    (h8 : reg n 8 &&& 0xFF = BitVec.ofNat 32 (bmSlotNum slot)) (h19 : reg n 19 = BitVec.ofNat 32 (c + 256 * p))
    (h20 : reg n 20 = F + BitVec.ofNat 32 0xB9A8) (h26 : reg n 26 = BitVec.ofNat 32 sv)
    (h23 : reg n 23 = btPop (memLoad32 M0 efuseRd)) :
    BmEnd Q (BmJump flash pinned policy M0 top (bmK R romStack stack0)) n := by
  have C := X.env
  have h16 := C.hsp
  obtain ⟨_, hge, hsv, _⟩ := bmc_accept hA
  have hF16 : F.toNat % 16 = 0 := by
    rw [← hF, show (48768 : Nat) = 16 * 3048 from rfl, Nat.add_mul_mod_self_left] at h16; exact h16
  have hFk : F.toNat + 0xBE80 < 2 ^ 32 := by rw [hF]; exact top.isLt
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  have hL := bmp_level M0
  -- the target's operands, to 0x2DA
  obtain ⟨n1, c1, u1⟩ := s.block bmB29 hc bmB29_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n.mem := u1.mem
  have r1 : ∀ r, reg n1 r = (runBlock bmB29 (n.mem, reg n)).2 r := fun r => by rw [u1.regs]
  have t1 : St n1.mem BM n1 0x2DA (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have a0_1 : reg n1 a0 = if (c &&& slot.bit != 0) = true then BitVec.ofNat 32 sv else 0 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB29, upd, ↓reduceIte]
    rw [h19, h26, bmt_low_and _ _ (v := slot.bit) (by cases slot <;> decide)
      (by have := bmt_addlo (k := 1) (by cases slot <;> decide) h8; cases slot <;> exact this)]
    exact bmt_mask_and _ _ _ (bmt_mask c p slot.bit hc4 hp (by cases slot <;> decide))
  have s3_1 : reg n1 19 = reg n 23 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB29, upd, ↓reduceIte]; (try rw [s.zero]); exact BitVec.zero_add _
  have k1 : ∀ r, r ≠ a0 → r ≠ 19 → reg n1 r = reg n r := fun r h0 h1 => by
    rw [r1, runBlock_reg _ _ _ r s.zero (by simp only [bmB29]; revert h0 h1; revert r; decide)]
  -- the larger of the two, to 0x2E0
  obtain ⟨n2, c2, t2, m2, s3_2, k2⟩ := bmt_max t1 (by rw [m1]; exact hc) bm_at_2da bm_at_2de
  have s3_2' : reg n2 19 = BitVec.ofNat 32 (burnTarget sv (c &&& slot.bit != 0) (bmLevel M0)) := by
    rw [s3_2, a0_1, k1 23 (by decide) (by decide), s3_1, h23, hL]
    exact bmt_burn sv (bmLevel M0) _ hsv (Nat.le_trans hge hsv)
  have t2' : St n2.mem BM n2 0x2E0 (reg n2) := t2
  have h20_2 : reg n2 20 = F + BitVec.ofNat 32 0xB9A8 := by
    rw [k2 20 (by decide), k1 20 (by decide) (by decide), h20]
  have hc2 : CodeIn n2.mem BM bootMainCode := by rw [m2, m1]; exact hc
  -- the image's flash address and the copy's arguments, to 0x2F8
  obtain ⟨n3, c3, u3⟩ := t2'.block bmB31 hc2 bmB31_end
    ⟨by show (reg n2 20 + 0x368).toNat % 4 = 0
        rw [h20_2, BitVec.add_assoc]; exact bmp_align hF16 hFk (by decide) (by decide),
      trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have r3 : ∀ r, reg n3 r = (runBlock bmB31 (n2.mem, reg n2)).2 r := fun r => by rw [u3.regs]
  have t3 : St n3.mem BM n3 0x2F8 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have sp2 : reg n2 sp = F := by rw [k2 sp (by decide), k1 sp (by decide) (by decide), hsp]
  have s2_3 : reg n3 18 = BitVec.ofNat 32 (bmcBase (BitVec.ofNat 32 (bmSlotNum slot)) + mf.image.offset) := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, bmB31, upd, ↓reduceIte]
    rw [h20_2, m2, m1, BitVec.add_assoc]; exact hlw
  have a0_3 : reg n3 a0 = F + BitVec.ofNat 32 0xB9AD := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, bmB31, upd, ↓reduceIte]; rw [sp2]; exact BitVec.add_comm _ _
  have a1_3 : reg n3 a1 = F + BitVec.ofNat 32 0xBBF0 := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, bmB31, upd, ↓reduceIte]; rw [sp2]; exact BitVec.add_comm _ _
  have a2_3 : reg n3 a2 = BitVec.ofNat 32 0x120 := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, bmB31, upd, ↓reduceIte]
  have k3 : ∀ r, r ≠ 18 → r ≠ a0 → r ≠ a1 → r ≠ a2 → reg n3 r = reg n2 r := fun r h0 h1 h2 h3 => by
    rw [r3, runBlock_reg _ _ _ r t2'.zero (by simp only [bmB31]; revert h0 h1 h2 h3; revert r; decide)]
  have sp3 : reg n3 sp = F := by rw [k3 sp (by decide) (by decide) (by decide) (by decide), sp2]
  have hK3 : BmKeep M0 n3.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [m3, m2, m1]; exact hK
  -- `memcpy(temp, res1, 0x120)`, to 0x300
  obtain ⟨n4, c4, t4, keep4, hK4, cp4, _⟩ := bmt_copy C t3 sp3 hF hK3 (by decide) (by decide) a0_3 a1_3 a2_3
    bm_at_2f8 bm_at_2fc (by decide) (by decide)
  have t4' : St n4.mem BM n4 0x300 (reg n4) := t4
  have hc4' := hK4.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  -- `s1 = s0`, to 0x302
  obtain ⟨n5, c5, u5⟩ := t4'.block bmB32 hc4' bmB32_end ⟨trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have r5 : ∀ r, reg n5 r = (runBlock bmB32 (n4.mem, reg n4)).2 r := fun r => by rw [u5.regs]
  have t5 : St n5.mem BM n5 0x302 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have s1_5 : reg n5 9 = reg n4 8 := by
    rw [r5]; simp +decide only [runBlock, BInstr.run, bmB32, upd, ↓reduceIte]; (try rw [t4'.zero]); exact BitVec.zero_add _
  have k5 : ∀ r, r ≠ 9 → reg n5 r = reg n4 r := fun r h0 => by
    rw [r5, runBlock_reg _ _ _ r t4'.zero (by simp only [bmB32]; revert h0; revert r; decide)]
  -- `j 0x348`
  obtain ⟨n6, e6, u6⟩ := t5.jump (by rw [m5]; exact hc4') bm_at_302 (off' := 0x348) (by decide)
    (by rw [t5.pc]; decide)
  have t6 : St n6.mem BM n6 0x348 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have q6 : ∀ q, romKeep q = true → q ≠ 9 → q ≠ 18 → q ≠ 19 → reg n6 q = reg n2 q := fun q hq h9 h18 h19 => by
    rw [u6.regs, k5 q h9, keep4 q hq, k3 q h18 (fun e => by subst e; exact absurd hq (by decide))
      (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide))]
  refine BmEnd.pre (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (.single e6)))))) ?_
  refine bmt_tail X t6 ?_ hF ?_ hck hD hA ?_ ?_ ?_ (bmp_target_le _ hge hsv) ?_ ?_
  · rw [q6 sp (by decide) (by decide) (by decide) (by decide), sp2]
  · rw [u6.mem, m5]; exact hK4
  · refine bmt_acc_move hAcc fun i hi => ?_
    rw [u6.mem, m5, cp4 i (Nat.lt_trans hi (by decide)), m3, m2, m1]
  · rw [u6.regs, s1_5, keep4 8 (by decide), k3 8 (by decide) (by decide) (by decide) (by decide),
      k2 8 (by decide), k1 8 (by decide) (by decide), h8]
  · rw [u6.regs, k5 19 (by decide), keep4 19 (by decide), k3 19 (by decide) (by decide) (by decide) (by decide)]
    exact s3_2'
  · rw [u6.regs, k5 18 (by decide), keep4 18 (by decide)]; exact s2_3
  · rw [q6 23 (by decide) (by decide) (by decide) (by decide), k2 23 (by decide),
      k1 23 (by decide) (by decide), h23]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **`boot_main` from 0x304**, when the first closure accepted the plan's
other slot: the first slot's number in `s0`, the other's in `s1`, the
decoded state's confirmed bits `c` in `s3`, the entry level in `s7`, and the
slot's `Accepted` bytes, with its security version at +0x128, at
`F + 0xBD20`. -/
theorem bmp_other {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    {Q : Prop} (X : BmHypQ Q flash pinned policy M0 top R romStack stack0 romBase romCode E)
    {n : Machine} {F : Word} (s : St n.mem BM n 0x304 (reg n)) (hsp : reg n sp = F)
    (hF : F.toNat + 0xBE80 = top.toNat)
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    {slot : Slot} {mf : Manifest} {sv t c p : Nat} (hc4 : c < 4) (hp : p ≤ 1)
    (hA : bmcAccept flash pinned policy (bmLevel M0) (BitVec.ofNat 32 (bmSlotNum slot)) = some (mf, sv, t))
    {ck : Slot → Option Nat} (hck : BmSound flash pinned policy M0 ck)
    (hD : (bmDecision flash M0 ck).outcome = .boot slot (burnTarget sv (c &&& slot.bit != 0) (bmLevel M0)))
    (hAcc : AccOk flash (BitVec.ofNat 32 (bmSlotNum slot)) mf n.mem (F + BitVec.ofNat 32 0xBD20))
    (hsvb : n.mem (F + BitVec.ofNat 32 0xBE48) = BitVec.ofNat 8 sv)
    (hlw : memLoad32 n.mem (F + BitVec.ofNat 32 0xBE40) =
      BitVec.ofNat 32 (bmcBase (BitVec.ofNat 32 (bmSlotNum slot)) + mf.image.offset))
    (h8 : reg n 8 &&& 0xFF = BitVec.ofNat 32 (bmSlotNum slot.other))
    (h9 : reg n 9 &&& 0xFF = BitVec.ofNat 32 (bmSlotNum slot))
    (h19 : reg n 19 = BitVec.ofNat 32 (c + 256 * p)) (h20 : reg n 20 = F + BitVec.ofNat 32 0xB9A8)
    (h23 : reg n 23 = btPop (memLoad32 M0 efuseRd)) :
    BmEnd Q (BmJump flash pinned policy M0 top (bmK R romStack stack0)) n := by
  have C := X.env
  have h16 := C.hsp
  obtain ⟨_, hge, hsv, _⟩ := bmc_accept hA
  have hF16 : F.toNat % 16 = 0 := by
    rw [← hF, show (48768 : Nat) = 16 * 3048 from rfl, Nat.add_mul_mod_self_left] at h16; exact h16
  have hFk : F.toNat + 0xBE80 < 2 ^ 32 := by rw [hF]; exact top.isLt
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  have hL := bmp_level M0
  -- the target's operands, to 0x322
  obtain ⟨n1, c1, u1⟩ := s.block bmB33 hc bmB33_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n.mem := u1.mem
  have r1 : ∀ r, reg n1 r = (runBlock bmB33 (n.mem, reg n)).2 r := fun r => by rw [u1.regs]
  have t1 : St n1.mem BM n1 0x322 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have a0_1 : reg n1 a0 = if (c &&& slot.bit != 0) = true then BitVec.ofNat 32 sv else 0 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB33, upd, ↓reduceIte]
    rw [h19, h20, BitVec.add_assoc, show BitVec.ofNat 32 0xB9A8 + 0x4A0 = BitVec.ofNat 32 0xBE48 from rfl,
      hsvb, bmp_zext hsv, bmt_low_and (BitVec.ofNat 32 (c + 256 * p)) _ (v := slot.bit) (by cases slot <;> decide)
        (by rw [s.zero]; have := bmt_sublo (by cases slot <;> decide) h8; cases slot <;> exact this)]
    rw [bmt_mask_and _ _ _ (bmt_mask c p slot.bit hc4 hp (by cases slot <;> decide))]
    exact bmp_andff _ hsv
  have s3_1 : reg n1 19 = reg n 23 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB33, upd, ↓reduceIte]; (try rw [s.zero]); exact BitVec.zero_add _
  have k1 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ 19 → reg n1 r = reg n r := fun r h0 h1 h2 => by
    rw [r1, runBlock_reg _ _ _ r s.zero (by simp only [bmB33]; revert h0 h1 h2; revert r; decide)]
  -- the larger of the two, to 0x2E0
  obtain ⟨n2, c2, t2, m2, s3_2, k2⟩ := bmt_max t1 (by rw [m1]; exact hc) bm_at_322 bm_at_326
  have s3_2' : reg n2 19 = BitVec.ofNat 32 (burnTarget sv (c &&& slot.bit != 0) (bmLevel M0)) := by
    rw [s3_2, a0_1, k1 23 (by decide) (by decide) (by decide), s3_1, h23, hL]
    exact bmt_burn sv (bmLevel M0) _ hsv (Nat.le_trans hge hsv)
  have t2' : St n2.mem BM n2 0x328 (reg n2) := t2
  have h20_2 : reg n2 20 = F + BitVec.ofNat 32 0xB9A8 := by
    rw [k2 20 (by decide), k1 20 (by decide) (by decide) (by decide), h20]
  have hc2 : CodeIn n2.mem BM bootMainCode := by rw [m2, m1]; exact hc
  -- the image's flash address and the copy's arguments, to 0x340
  obtain ⟨n3, c3, u3⟩ := t2'.block bmB35 hc2 bmB35_end
    ⟨by show (reg n2 20 + 0x498).toNat % 4 = 0
        rw [h20_2, BitVec.add_assoc]; exact bmp_align hF16 hFk (by decide) (by decide),
      trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have r3 : ∀ r, reg n3 r = (runBlock bmB35 (n2.mem, reg n2)).2 r := fun r => by rw [u3.regs]
  have t3 : St n3.mem BM n3 0x340 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have sp2 : reg n2 sp = F := by rw [k2 sp (by decide), k1 sp (by decide) (by decide) (by decide), hsp]
  have s2_3 : reg n3 18 = BitVec.ofNat 32 (bmcBase (BitVec.ofNat 32 (bmSlotNum slot)) + mf.image.offset) := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, bmB35, upd, ↓reduceIte]
    rw [h20_2, m2, m1, BitVec.add_assoc]; exact hlw
  have a0_3 : reg n3 a0 = F + BitVec.ofNat 32 0xB9AD := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, bmB35, upd, ↓reduceIte]; rw [sp2]; exact BitVec.add_comm _ _
  have a1_3 : reg n3 a1 = F + BitVec.ofNat 32 0xBD20 := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, bmB35, upd, ↓reduceIte]; rw [sp2]; exact BitVec.add_comm _ _
  have a2_3 : reg n3 a2 = BitVec.ofNat 32 0x120 := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, bmB35, upd, ↓reduceIte]
  have k3 : ∀ r, r ≠ 18 → r ≠ a0 → r ≠ a1 → r ≠ a2 → reg n3 r = reg n2 r := fun r h0 h1 h2 h3 => by
    rw [r3, runBlock_reg _ _ _ r t2'.zero (by simp only [bmB35]; revert h0 h1 h2 h3; revert r; decide)]
  have sp3 : reg n3 sp = F := by rw [k3 sp (by decide) (by decide) (by decide) (by decide), sp2]
  have hK3 : BmKeep M0 n3.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [m3, m2, m1]; exact hK
  -- `memcpy(temp, res2, 0x120)`, to 0x348
  obtain ⟨n4, c4, t4, keep4, hK4, cp4, _⟩ := bmt_copy C t3 sp3 hF hK3 (by decide) (by decide) a0_3 a1_3 a2_3
    bm_at_340 bm_at_344 (by decide) (by decide)
  have t4' : St n4.mem BM n4 0x348 (reg n4) := t4
  have q4 : ∀ q, romKeep q = true → q ≠ 18 → q ≠ 19 → reg n4 q = reg n2 q := fun q hq h18 h19 => by
    rw [keep4 q hq, k3 q h18 (fun e => by subst e; exact absurd hq (by decide))
      (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide))]
  refine BmEnd.pre (c1.trans (c2.trans (c3.trans c4))) ?_
  refine bmt_tail X t4' ?_ hF hK4 hck hD hA ?_ ?_ ?_ (bmp_target_le _ hge hsv) ?_ ?_
  · rw [q4 sp (by decide) (by decide) (by decide), sp2]
  · refine bmt_acc_move hAcc fun i hi => ?_
    rw [cp4 i (Nat.lt_trans hi (by decide)), m3, m2, m1]
  · rw [q4 9 (by decide) (by decide) (by decide), k2 9 (by decide), k1 9 (by decide) (by decide) (by decide), h9]
  · rw [keep4 19 (by decide), k3 19 (by decide) (by decide) (by decide) (by decide)]
    exact s3_2'
  · rw [keep4 18 (by decide)]; exact s2_3
  · rw [q4 23 (by decide) (by decide) (by decide), k2 23 (by decide), k1 23 (by decide) (by decide) (by decide), h23]

end C3.RV32.Cur
