import C3BootProofs.Proofs.BootMainPlan
import C3BootProofs.Proofs.MemsetAny

/-!
# `boot_main` from its entry to the decoded state

From its entry, `boot_main` saves its registers, logs, sets the flash
size, clears two 32-byte buffers, reads the boot-state records at 0x28000
and 0x29000 into them, decodes each, picks the copy that `readRecords`
picks, counts the eFuse level, logs it, clears the `Buffers`, and goes on
at 0x174 (`bmq_plan`). A failed flash read halts.
-/

namespace C3.RV32.Cur

open C3 C3.Image C3.RV32.BootMainContract

/-! ## The frame -/

theorem bme_kin {F top x : Word} {R romStack stack0 : Nat} {c k : Nat} (hF : F.toNat + 0xBE80 = top.toNat)
    (hlo : 0x3FCC8000 + bmK R romStack stack0 ≤ top.toNat) (hc : c + k ≤ 0xBE80)
    (hx : Sep (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) x 1) :
    Sep (F + BitVec.ofNat 32 c) k x 1 := by
  have hKv : bmK R romStack stack0 = 0xBE80 + 0x150 + R + romStack + stack0 := rfl
  have hFk : F.toNat + 0xBE80 < 2 ^ 32 := by rw [hF]; exact top.isLt
  have hW : (top - BitVec.ofNat 32 (bmK R romStack stack0)).toNat = top.toNat - bmK R romStack stack0 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, hKv]; omega
  refine bmt_sep_in hx ?_ ?_
  · rw [hW, bmd_eF hFk (by omega), hKv]; omega
  · rw [hW, bmd_eF hFk (by omega), hKv]; omega

/-- The `k` bytes below `F` that a callee uses lie inside the stack. -/
theorem bme_below {F top x : Word} {R romStack stack0 : Nat} {k : Nat} (hF : F.toNat + 0xBE80 = top.toNat)
    (hlo : 0x3FCC8000 + bmK R romStack stack0 ≤ top.toNat) (hk : k ≤ 0x150 + R + romStack + stack0)
    (hx : Sep (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) x 1) :
    Sep (F - BitVec.ofNat 32 k) k x 1 := by
  have hKv : bmK R romStack stack0 = 0xBE80 + 0x150 + R + romStack + stack0 := rfl
  have hW : (top - BitVec.ofNat 32 (bmK R romStack stack0)).toNat = top.toNat - bmK R romStack stack0 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, hKv]; omega
  have hS : (F - BitVec.ofNat 32 k).toNat = F.toNat - k := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega)]; omega
  refine bmt_sep_in hx ?_ ?_
  · rw [hW, hS, hKv]; omega
  · rw [hW, hS, hKv]; omega

/-- Bytes in the frame lie apart from code at or above 0x40000000. -/
theorem bme_low {F top b : Word} {c k len : Nat} (hF : F.toNat + 0xBE80 = top.toNat)
    (hhi : top.toNat ≤ bmPtr.toNat) (hc : c + k ≤ 0xBE80) (hb : 0x40000000 ≤ b.toNat)
    (hbl : b.toNat + len ≤ 2 ^ 32) : Sep (F + BitVec.ofNat 32 c) k b len := by
  have hFk : F.toNat + 0xBE80 < 2 ^ 32 := by rw [hF]; exact top.isLt
  have hbp : bmPtr.toNat = 0x3FCDFFF0 := rfl
  refine lowSep ?_ hb hbl
  rw [bmd_eF hFk (by omega)]; rw [hbp] at hhi; omega

/-! ## Calls -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- A call at `off` from `boot_main` to `memset(F + d, 0, N)`, inside the frame. -/
theorem bme_memset {M0 : Word → BitVec 8} {top : Word} {R romStack stack0 : Nat} {romBase : Word}
    {romCode : List Nat} (C : BmEnv M0 top R romStack stack0 romBase romCode) {n : Machine} {F : Word}
    {off d N : Nat} {imm o : Word} (s : St n.mem BM n off (reg n)) (hc : CodeIn n.mem BM bootMainCode)
    (hm : CodeIn n.mem (BitVec.ofNat 32 memsetAddress) memsetCode) (hF : F.toNat + 0xBE80 = top.toNat)
    (h1 : fetchRel bootMainCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : BM + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 memsetAddress)
    (he8 : (BM + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 d) (ha1 : reg n a1 = 0) (ha2 : reg n a2 = BitVec.ofNat 32 N)
    (hd : d + N ≤ 0xBE80) :
    ∃ n', Steps n n' ∧ St n'.mem BM n' (off + 8) (reg n') ∧
      n'.mem = fillBytes n.mem (F + BitVec.ofNat 32 d) 0 N ∧
      ∀ r, r ≠ ra → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → reg n' r = reg n r := by
  have hhi := C.hhi
  have hFk : F.toNat + 0xBE80 < 2 ^ 32 := by rw [hF]; exact top.isLt
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa (cb := BitVec.ofNat 32 memsetAddress) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨n2, c2, pc2, mem2, _, k2⟩ := memset_correct n1 (BitVec.ofNat 32 memsetAddress)
    (BM + BitVec.ofNat 32 (off + 8)) (F + BitVec.ofNat 32 d) 0 N (fun i hi => by rw [mem1]; exact hm i hi)
    (by decide) pc1 (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1])
    (by rw [r1 _ (by decide), ha2]) (by rw [regs1]; simp +decide only [upd, ↓reduceIte])
    (even_clear _ he8) (by rw [bmd_eF hFk (by omega)]; omega)
    (bme_low hF hhi hd (by decide) (by decide))
  rw [mem1] at mem2
  refine ⟨n2, c1.trans c2, ⟨pc2, rfl, fun _ => rfl⟩, mem2, fun r hr h2' h3 h4 h5 h6 => ?_⟩
  rw [k2 r h2' h3 h4 h5 h6, r1 r hr]

/-! ## The registers at 0x116 -/

/-- The registers at 0x116 that `BmqPre` names, other than s7, with the
generation in s8. -/
structure BmePre (flash : Nat → BitVec 8) (F : Word) (st : State) (g : Fin 32 → Word) : Prop where
  r9 : g 9 = bmWord st
  r18 : g 18 = bmCopy (bmRecs flash).2
  r19 : g 19 = BitVec.ofNat 32 (st.confirmed + 256 * bmSlotNum st.preferred)
  r20 : g 20 = F + BitVec.ofNat 32 0xB9A8
  r21 : g 21 = BitVec.ofNat 32 (bmSlotNum st.preferred)
  r22 : g 22 = BitVec.ofNat 32 ((bmTrialBytes st.trial).2 + 256 * st.confirmed + 65536 * bmSlotNum st.preferred)
  r24 : g 24 = BitVec.ofNat 32 st.generation
  rsp : g sp = F

/-- The registers that `BmePre` names. -/
def bmeRegs (q : Fin 32) : Bool := q.val ∈ [2, 9, 18, 19, 20, 21, 22, 24]

theorem BmePre.keep {flash : Nat → BitVec 8} {F : Word} {st : State} {g g' : Fin 32 → Word}
    (P : BmePre flash F st g) (h : ∀ q, bmeRegs q = true → g' q = g q) : BmePre flash F st g' :=
  ⟨by rw [h 9 (by decide)]; exact P.r9,
    by rw [h 18 (by decide)]; exact P.r18, by rw [h 19 (by decide)]; exact P.r19,
    by rw [h 20 (by decide)]; exact P.r20, by rw [h 21 (by decide)]; exact P.r21,
    by rw [h 22 (by decide)]; exact P.r22, by rw [h 24 (by decide)]; exact P.r24,
    by rw [h sp (by decide)]; exact P.rsp⟩

theorem bme_andc (x y : Word) : aluEval .and x y = aluEval .and y x := by
  simp only [aluEval]; exact BitVec.and_comm x y

theorem bme_hiload {M0 M : Word → BitVec 8} {top : Word} {R romStack stack0 : Nat} {romBase : Word}
    {romCode : List Nat} (C : BmEnv M0 top R romStack stack0 romBase romCode)
    (h : BmKeep M0 M (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0)) :
    memLoad32 M efuseRd = memLoad32 M0 efuseRd :=
  bmt_load_congr fun j hj => h.hiOf C _ (by
    have e : (efuseRd + BitVec.ofNat 32 j).toNat = 0x6000883C + j := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega)]
      show (0x6000883C + j) % 2 ^ 32 = 0x6000883C + j; omega
    rw [e]; omega)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- From 0x116, with the decoded state in the registers: `boot_main`
counts the eFuse level, logs it, clears the `Buffers`, and goes on at
0x174. -/
theorem bme_tail {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    {Q : Prop} (X : BmHypQ Q flash pinned policy M0 top R romStack stack0 romBase romCode E)
    {n : Machine} {F : Word} (s : St n.mem BM n 0x116 (reg n)) (hF : F.toNat + 0xBE80 = top.toNat)
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    {st : State} (hst : (bmRecs flash).1 = st) (hv : BmdValid st) (P : BmePre flash F st (reg n)) :
    BmEnd Q (BmJump flash pinned policy M0 top (bmK R romStack stack0)) n := by
  have C := X.env
  have hhi := C.hhi; have hlo := C.hlo
  have hKv : bmK R romStack stack0 = 0xBE80 + 0x150 + R + romStack + stack0 := rfl
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  obtain ⟨n1, c1, u1⟩ := s.block bmB13 hc bmB13_end
    ⟨trivial, by show ((0x60009000 : Word) + 0xFFFFF83C).toNat % 4 = 0; decide, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n.mem := u1.mem
  have r1 : ∀ r, reg n1 r = (runBlock bmB13 (n.mem, reg n)).2 r := fun r => by rw [u1.regs]
  have t1 : St n1.mem BM n1 0x15A (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ 23 → reg n1 r = reg n r := fun r h1 h2 h3 h4 => by
    rw [r1, runBlock_reg bmB13 _ _ r s.zero (by simp only [bmB13]; revert h1 h2 h3 h4; revert r; decide)]
  have h23 : reg n1 23 = btPop (memLoad32 M0 efuseRd) := by
    rw [r1, ← bme_hiload C hK]
    simp +decide only [runBlock, BInstr.run, bmB13, upd, ↓reduceIte]
    rw [show (0x60009000 : Word) + 0xFFFFF83C = efuseRd from by decide,
      show aluEval .add 20480 1365 = (0x5555 : Word) from rfl, show aluEval .add 12288 819 = (0x3333 : Word) from rfl,
      bme_andc 0x5555, bme_andc 0x3333]
    rfl
  have hK1 : BmKeep M0 n1.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [m1]; exact hK
  have sp1 : reg n1 sp = F := by rw [k1 sp (by decide) (by decide) (by decide) (by decide)]; exact P.rsp
  have hc1 := hK1.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  obtain ⟨n2, c2, t2, mem2, keep2⟩ := bm_romcall 0x40000040 X.log t1 sp1 hc1
    (C.rom.hi (hK1.hiOf C) C.hrb (by have := C.hrl; omega)) (by omega) bm_at_15a bm_at_15e
    (by decide) (by decide) (by decide)
  have hK2 : BmKeep M0 n2.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) :=
    hK1.step fun x hx => mem2 x (bme_below hF hlo (by omega) hx)
  have k2 : ∀ q, romKeep q = true → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ 23 → reg n2 q = reg n q :=
    fun q hq h1 h2 h3 h4 => by rw [keep2 q hq, k1 q h1 h2 h3 h4]
  have r23 : reg n2 23 = btPop (memLoad32 M0 efuseRd) := by rw [keep2 23 (by decide), h23]
  have hc2 := hK2.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  obtain ⟨n3, c3, u3⟩ := t2.block bmB14 hc2 bmB14_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have r3 : ∀ r, reg n3 r = (runBlock bmB14 (n2.mem, reg n2)).2 r := fun r => by rw [u3.regs]
  have t3 : St n3.mem BM n3 0x16C (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have k3 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → reg n3 r = reg n2 r := fun r h1 h2 h3 => by
    rw [r3, runBlock_reg bmB14 _ _ r t2.zero (by simp only [bmB14]; revert h1 h2 h3; revert r; decide)]
  have sp2 : reg n2 sp = F := by
    rw [k2 sp (by decide) (by decide) (by decide) (by decide) (by decide)]; exact P.rsp
  have hK3 : BmKeep M0 n3.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [m3]; exact hK2
  obtain ⟨n4, c4, t4, mem4, k4⟩ := bme_memset C t3 (hK3.codeIn C C.code (.inr ⟨by decide, by decide⟩))
    (hK3.codeIn C C.memset (.inr ⟨by decide, by decide⟩)) hF (d := 0x50) (N := 0xB954)
    bm_at_16c bm_at_170 (by decide) (by decide)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, bmB14, upd, ↓reduceIte]; rw [sp2]; rfl)
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, bmB14, upd, ↓reduceIte])
    (by rw [r3]; simp +decide only [runBlock, BInstr.run, bmB14, upd, ↓reduceIte]) (by decide)
  have hK4 : BmKeep M0 n4.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) :=
    hK3.step fun x hx => by rw [mem4, fillBytes_sep (bme_kin hF hlo (by decide) hx) (Nat.le_refl _)]
  have kk : ∀ q, bmeRegs q = true → reg n4 q = reg n q := fun q hq => by
    have h0 : q ≠ a0 := by rintro rfl; exact absurd hq (by decide)
    have h1 : q ≠ a1 := by rintro rfl; exact absurd hq (by decide)
    have h2 : q ≠ a2 := by rintro rfl; exact absurd hq (by decide)
    rw [k4 q (by rintro rfl; exact absurd hq (by decide)) h2 (by rintro rfl; exact absurd hq (by decide))
      (by rintro rfl; exact absurd hq (by decide)) (by rintro rfl; exact absurd hq (by decide))
      (by rintro rfl; exact absurd hq (by decide)), k3 q h0 h1 h2,
      k2 q (by revert hq; revert q; decide) h0 h1 h2 (by rintro rfl; exact absurd hq (by decide))]
  have P4 := P.keep kk
  have r23' : reg n4 23 = btPop (memLoad32 M0 efuseRd) := by
    rw [k4 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k3 23 (by decide) (by decide) (by decide), r23]
  refine BmEnd.pre (c1.trans (c2.trans (c3.trans c4))) ?_
  exact bmq_plan X t4 hF hK4 hst hv ⟨P4.r9, P4.r18, P4.r19, P4.r20, P4.r21, P4.r22, r23', P4.rsp⟩ P4.r24

/-! ## The copy that `readRecords` picks -/

/-- What `decode` leaves at `out` for one copy: 2 at +7 when the copy
doesn't decode, and otherwise the state's generation, its word at +4, a
slot byte at +7, and a state that `bmd_main` can take. -/
def BmeCopy (M : Word → BitVec 8) (out : Word) : Option State → Prop
  | none => M (out + 7) = 2
  | some s => memLoad32 M out = BitVec.ofNat 32 s.generation ∧ memLoad32 M (out + 4) = bmWord s ∧
      (M (out + 7)).toNat ≤ 1 ∧ BmdValid s

theorem bme_d8 (a r : Nat) (ha : a < 256) : (a + 256 * r) / 2 ^ 8 = r := by
  rw [show (2 : Nat) ^ 8 = 256 from rfl, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt ha, Nat.zero_add]

theorem bme_srl3 (a b c p : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) (hp : p < 256) :
    aluEval .srl (BitVec.ofNat 32 (a + 256 * b + 65536 * c + 16777216 * p)) 8 =
        BitVec.ofNat 32 (b + 256 * c + 65536 * p) ∧
      aluEval .srl (BitVec.ofNat 32 (a + 256 * b + 65536 * c + 16777216 * p)) 16 =
        BitVec.ofNat 32 (c + 256 * p) ∧
      aluEval .srl (BitVec.ofNat 32 (a + 256 * b + 65536 * c + 16777216 * p)) 24 = BitVec.ofNat 32 p := by
  have e0 : ∀ a b c p : Nat, a + 256 * b + 65536 * c + 16777216 * p = a + 256 * (b + 256 * (c + 256 * p)) := by
    intro a b c p; omega
  have e1 : ∀ b c p : Nat, b + 256 * c + 65536 * p = b + 256 * (c + 256 * p) := by
    intro b c p; omega
  have lt : ∀ a b c p : Nat, a < 256 → b < 256 → c < 256 → p < 256 →
      a + 256 * b + 65536 * c + 16777216 * p < 2 ^ 32 := by
    intro a b c p ha hb hc hp; omega
  have hx := lt a b c p ha hb hc hp
  have s8 : ∀ k, (BitVec.ofNat 32 k).toNat = k % 2 ^ 32 := fun k => BitVec.toNat_ofNat _ _
  have q1 : (a + 256 * b + 65536 * c + 16777216 * p) % 2 ^ 32 / 2 ^ 8 = b + 256 * c + 65536 * p := by
    rw [Nat.mod_eq_of_lt hx, e0, bme_d8 _ _ ha, e1]
  have q2 : (a + 256 * b + 65536 * c + 16777216 * p) % 2 ^ 32 / 2 ^ 16 = c + 256 * p := by
    rw [show (2 : Nat) ^ 16 = 2 ^ 8 * 2 ^ 8 from rfl, ← Nat.div_div_eq_div_mul, q1, e1, bme_d8 _ _ hb]
  have q3 : (a + 256 * b + 65536 * c + 16777216 * p) % 2 ^ 32 / 2 ^ 24 = p := by
    rw [show (2 : Nat) ^ 24 = 2 ^ 16 * 2 ^ 8 from rfl, ← Nat.div_div_eq_div_mul, q2, bme_d8 _ _ hc]
  have l1 : b + 256 * c + 65536 * p < 2 ^ 32 := Nat.lt_of_le_of_lt (by rw [q1.symm]; exact Nat.div_le_self _ _)
    (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (Nat.le_refl _))
  have l2 : c + 256 * p < 2 ^ 32 := Nat.lt_of_le_of_lt (by rw [q2.symm]; exact Nat.div_le_self _ _)
    (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (Nat.le_refl _))
  have l3 : p < 2 ^ 32 := Nat.lt_trans hp (by decide)
  refine ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_⟩ <;>
    simp only [aluEval, BitVec.toNat_ushiftRight, s8, Nat.shiftRight_eq_div_pow]
  · rw [Nat.mod_eq_of_lt l1]; exact q1
  · rw [Nat.mod_eq_of_lt l2]; exact q2
  · rw [Nat.mod_eq_of_lt l3]; exact q3

/-- The word at +4 shifted right by 8, 16, and 24, as `BmqPre` names them. -/
theorem bme_word (s : State) (hv : BmdValid s) :
    aluEval .srl (bmWord s) 8 =
        BitVec.ofNat 32 ((bmTrialBytes s.trial).2 + 256 * s.confirmed + 65536 * bmSlotNum s.preferred) ∧
      aluEval .srl (bmWord s) 16 = BitVec.ofNat 32 (s.confirmed + 256 * bmSlotNum s.preferred) ∧
      aluEval .srl (bmWord s) 24 = BitVec.ofNat 32 (bmSlotNum s.preferred) := by
  have h2 : (bmTrialBytes s.trial).2 < 256 := by
    obtain ⟨_, _, ht⟩ := hv
    cases e : s.trial with
    | none => decide
    | some t => exact Nat.lt_of_le_of_lt (ht t e) (by decide)
  exact bme_srl3 _ _ _ _ (Nat.lt_of_le_of_lt (bmq_tb_le _) (by decide)) h2
    (Nat.lt_trans hv.2.1 (by decide)) (Nat.lt_of_le_of_lt (bmd_slot_le _) (by decide))

theorem bme_F4 {F top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {M0 : Word → BitVec 8} (C : BmEnv M0 top R romStack stack0 romBase romCode)
    (hF : F.toNat + 0xBE80 = top.toNat) {c : Nat} (hc : c ≤ 0xBE80) (h4 : c % 4 = 0) :
    (F + BitVec.ofNat 32 c).toNat % 4 = 0 := by
  have hFk : F.toNat + 0xBE80 < 2 ^ 32 := by rw [hF]; exact top.isLt
  have hr := (bmd_room C hF).1
  rw [bmd_eF hFk hc]; omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- From 0xEC, when `readRecords` picks copy B: `boot_main` loads its state
and goes on at 0x116. -/
theorem bme_c1 {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    {Q : Prop} (X : BmHypQ Q flash pinned policy M0 top R romStack stack0 romBase romCode E)
    {n : Machine} {F : Word} (s : St n.mem BM n 0xEC (reg n)) (hF : F.toNat + 0xBE80 = top.toNat)
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    {st : State} (hrec : bmRecs flash = (st, some .b)) (hcp : BmeCopy n.mem (F + BitVec.ofNat 32 0x50) (some st))
    (h20 : reg n 20 = F + BitVec.ofNat 32 0xB9A8) (hsp : reg n sp = F) :
    BmEnd Q (BmJump flash pinned policy M0 top (bmK R romStack stack0)) n := by
  have C := X.env
  obtain ⟨hg, hw, _, hv⟩ := hcp
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  obtain ⟨n1, c1, u1⟩ := s.block bmB11 hc bmB11_end
    ⟨by show (reg n sp + 0x54).toNat % 4 = 0; rw [hsp]; exact bme_F4 C hF (c := 0x54) (by decide) (by decide),
      by show (reg n sp + 0x50).toNat % 4 = 0; rw [hsp]; exact bme_F4 C hF (c := 0x50) (by decide) (by decide),
      trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n.mem := u1.mem
  have r1 : ∀ r, reg n1 r = (runBlock bmB11 (n.mem, reg n)).2 r := fun r => by rw [u1.regs]
  have t1 : St n1.mem BM n1 0xFE (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ r, r ≠ 9 → r ≠ 24 → r ≠ 22 → r ≠ 19 → r ≠ 21 → r ≠ 18 → reg n1 r = reg n r :=
    fun r h1 h2 h3 h4 h5 h6 => by
      rw [r1, runBlock_reg bmB11 _ _ r s.zero (by simp only [bmB11]; revert h1 h2 h3 h4 h5 h6; revert r; decide)]
  have e54 : F + 0x54 = F + BitVec.ofNat 32 0x50 + 4 := by rw [BitVec.add_assoc]; rfl
  have e50 : F + 0x50 = F + BitVec.ofNat 32 0x50 := rfl
  have h9 : reg n1 9 = bmWord st := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB11, upd, ↓reduceIte]; rw [hsp, e54, hw]
  have hW := bme_word st hv
  have hst : (bmRecs flash).1 = st := by rw [hrec]
  have P : BmePre flash F st (reg n1) :=
    { r9 := h9
      r18 := by
        rw [r1, hrec]; simp +decide only [runBlock, BInstr.run, bmB11, upd, ↓reduceIte]
      r19 := by
        rw [r1]; simp +decide only [runBlock, BInstr.run, bmB11, upd, ↓reduceIte]; rw [hsp, e54, hw]; exact hW.2.1
      r20 := by rw [k1 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h20
      r21 := by
        rw [r1]; simp +decide only [runBlock, BInstr.run, bmB11, upd, ↓reduceIte]; rw [hsp, e54, hw]; exact hW.2.2
      r22 := by
        rw [r1]; simp +decide only [runBlock, BInstr.run, bmB11, upd, ↓reduceIte]; rw [hsp, e54, hw]; exact hW.1
      r24 := by
        rw [r1]; simp +decide only [runBlock, BInstr.run, bmB11, upd, ↓reduceIte]; rw [hsp, e50, hg]
      rsp := by rw [k1 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hsp }
  have hK1 : BmKeep M0 n1.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [m1]; exact hK
  have hc1 := hK1.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  obtain ⟨n2, e2, t2⟩ := t1.jump hc1 bm_at_fe (off' := 0x116) (by decide) (by rw [t1.pc]; decide)
  refine BmEnd.pre (c1.trans (.single e2)) ?_
  rw [← t2.mem] at hK1
  exact bme_tail X ⟨t2.pc, rfl, fun _ => rfl⟩ hF hK1 hst hv (P.keep fun q _ => t2.regs q)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- From 0x100, when `readRecords` picks copy A: `boot_main` loads its state
and goes on at 0x116. -/
theorem bme_c0 {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    {Q : Prop} (X : BmHypQ Q flash pinned policy M0 top R romStack stack0 romBase romCode E)
    {n : Machine} {F : Word} (s : St n.mem BM n 0x100 (reg n)) (hF : F.toNat + 0xBE80 = top.toNat)
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    {st : State} (hrec : bmRecs flash = (st, some .a))
    (hcp : BmeCopy n.mem (F + BitVec.ofNat 32 0xB9A8) (some st))
    (h20 : reg n 20 = F + BitVec.ofNat 32 0xB9A8) (hsp : reg n sp = F) :
    BmEnd Q (BmJump flash pinned policy M0 top (bmK R romStack stack0)) n := by
  have C := X.env
  obtain ⟨hg, hw, _, hv⟩ := hcp
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  have e4 : F + BitVec.ofNat 32 0xB9A8 + 4 = F + BitVec.ofNat 32 0xB9AC := by rw [BitVec.add_assoc]; rfl
  have e0 : F + BitVec.ofNat 32 0xB9A8 + 0 = F + BitVec.ofNat 32 0xB9A8 := BitVec.add_zero _
  obtain ⟨n1, c1, u1⟩ := s.block bmB12 hc bmB12_end
    ⟨trivial,
      by show (reg n 20 + 4).toNat % 4 = 0; rw [h20, e4]; exact bme_F4 C hF (c := 0xB9AC) (by decide) (by decide),
      by show (reg n 20 + 0).toNat % 4 = 0; rw [h20, e0]; exact bme_F4 C hF (c := 0xB9A8) (by decide) (by decide),
      trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n.mem := u1.mem
  have r1 : ∀ r, reg n1 r = (runBlock bmB12 (n.mem, reg n)).2 r := fun r => by rw [u1.regs]
  have t1 : St n1.mem BM n1 0x116 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ r, r ≠ 9 → r ≠ 24 → r ≠ 22 → r ≠ 19 → r ≠ 21 → r ≠ 18 → reg n1 r = reg n r :=
    fun r h1 h2 h3 h4 h5 h6 => by
      rw [r1, runBlock_reg bmB12 _ _ r s.zero (by simp only [bmB12]; revert h1 h2 h3 h4 h5 h6; revert r; decide)]
  have hW := bme_word st hv
  have hst : (bmRecs flash).1 = st := by rw [hrec]
  have P : BmePre flash F st (reg n1) :=
    { r9 := by rw [r1]; simp +decide only [runBlock, BInstr.run, bmB12, upd, ↓reduceIte]; rw [h20, hw]
      r18 := by rw [r1, hrec]; simp +decide only [runBlock, BInstr.run, bmB12, upd, ↓reduceIte]; rw [s.zero]; rfl
      r19 := by
        rw [r1]; simp +decide only [runBlock, BInstr.run, bmB12, upd, ↓reduceIte]; rw [h20, hw]; exact hW.2.1
      r20 := by rw [k1 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h20
      r21 := by
        rw [r1]; simp +decide only [runBlock, BInstr.run, bmB12, upd, ↓reduceIte]; rw [h20, hw]; exact hW.2.2
      r22 := by
        rw [r1]; simp +decide only [runBlock, BInstr.run, bmB12, upd, ↓reduceIte]; rw [h20, hw]; exact hW.1
      r24 := by
        rw [r1]; simp +decide only [runBlock, BInstr.run, bmB12, upd, ↓reduceIte]; rw [h20, e0, hg]
      rsp := by rw [k1 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hsp }
  have hK1 : BmKeep M0 n1.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [m1]; exact hK
  exact BmEnd.pre c1 (bme_tail X t1 hF hK1 hst hv P)

theorem bme_valid_def : BmdValid State.default := ⟨by decide, by decide, fun _ h => nomatch h⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- From 0xC6, when neither copy decodes: `boot_main` takes the default
state and goes on at 0x116. -/
theorem bme_def {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    {Q : Prop} (X : BmHypQ Q flash pinned policy M0 top R romStack stack0 romBase romCode E)
    {n : Machine} {F : Word} (s : St n.mem BM n 0xC6 (reg n)) (hF : F.toNat + 0xBE80 = top.toNat)
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    (hrec : bmRecs flash = (State.default, none)) (h9 : reg n 9 = 2)
    (h20 : reg n 20 = F + BitVec.ofNat 32 0xB9A8) (hsp : reg n sp = F) :
    BmEnd Q (BmJump flash pinned policy M0 top (bmK R romStack stack0)) n := by
  have C := X.env
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  obtain ⟨n1, c1, u1⟩ := s.block bmB8 hc bmB8_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n.mem := u1.mem
  have r1 : ∀ r, reg n1 r = (runBlock bmB8 (n.mem, reg n)).2 r := fun r => by rw [u1.regs]
  have t1 : St n1.mem BM n1 0xD0 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ r, r ≠ 24 → r ≠ 22 → r ≠ 19 → r ≠ 21 → r ≠ 18 → reg n1 r = reg n r :=
    fun r h2 h3 h4 h5 h6 => by
      rw [r1, runBlock_reg bmB8 _ _ r s.zero (by simp only [bmB8]; revert h2 h3 h4 h5 h6; revert r; decide)]
  have hst : (bmRecs flash).1 = State.default := by rw [hrec]
  have P : BmePre flash F State.default (reg n1) :=
    { r9 := by rw [k1 9 (by decide) (by decide) (by decide) (by decide) (by decide), h9]; rfl
      r18 := by rw [r1, hrec]; simp +decide only [runBlock, BInstr.run, bmB8, upd, ↓reduceIte]; (try rw [s.zero]); try rfl
      r19 := by rw [r1]; simp +decide only [runBlock, BInstr.run, bmB8, upd, ↓reduceIte]; (try rw [s.zero]); try rfl
      r20 := by rw [k1 20 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h20
      r21 := by rw [r1]; simp +decide only [runBlock, BInstr.run, bmB8, upd, ↓reduceIte]; (try rw [s.zero]); try rfl
      r22 := by rw [r1]; simp +decide only [runBlock, BInstr.run, bmB8, upd, ↓reduceIte]; (try rw [s.zero]); try rfl
      r24 := by rw [r1]; simp +decide only [runBlock, BInstr.run, bmB8, upd, ↓reduceIte]; (try rw [s.zero]); try rfl
      rsp := by rw [k1 sp (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hsp }
  have hK1 : BmKeep M0 n1.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [m1]; exact hK
  have hc1 := hK1.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  obtain ⟨n2, e2, t2⟩ := t1.jump hc1 bm_at_d0 (off' := 0x116) (by decide) (by rw [t1.pc]; decide)
  refine BmEnd.pre (c1.trans (.single e2)) ?_
  rw [← t2.mem] at hK1
  exact bme_tail X ⟨t2.pc, rfl, fun _ => rfl⟩ hF hK1 hst bme_valid_def (P.keep fun q _ => t2.regs q)

theorem bme_zt (x : BitVec 8) : (x.zeroExtend 32).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))

theorem bme_z2 {x : BitVec 8} (h : x = 2) : x.zeroExtend 32 = 2 := by rw [h]; rfl

theorem bme_zne {x : BitVec 8} (h : x.toNat ≤ 1) : x.zeroExtend 32 ≠ 2 := fun e => by
  have := congrArg BitVec.toNat e
  rw [bme_zt] at this
  exact Nat.ne_of_lt (Nat.lt_of_le_of_lt h (by decide)) (this.trans rfl)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- From 0xB4, with both copies decoded: `boot_main` picks the copy that
`readRecords` picks, or the default state, and goes on at 0x116. -/
theorem bme_sel {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    {Q : Prop} (X : BmHypQ Q flash pinned policy M0 top R romStack stack0 romBase romCode E)
    {n : Machine} {F : Word} (s : St n.mem BM n 0xB4 (reg n)) (hF : F.toNat + 0xBE80 = top.toNat)
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    (hc0 : BmeCopy n.mem (F + BitVec.ofNat 32 0xB9A8) (decodeRecord (bmcFlash flash 0x28000 32)))
    (hc1 : BmeCopy n.mem (F + BitVec.ofNat 32 0x50) (decodeRecord (bmcFlash flash 0x29000 32)))
    (h20 : reg n 20 = F + BitVec.ofNat 32 0xB9A8) (hsp : reg n sp = F) :
    BmEnd Q (BmJump flash pinned policy M0 top (bmK R romStack stack0)) n := by
  have C := X.env
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  obtain ⟨n1, c1, u1⟩ := s.block bmB7 hc bmB7_end ⟨trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n.mem := u1.mem
  have r1 : ∀ r, reg n1 r = (runBlock bmB7 (n.mem, reg n)).2 r := fun r => by rw [u1.regs]
  have t1 : St n1.mem BM n1 0xBE (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ 9 → reg n1 r = reg n r := fun r h1 h2 h3 => by
    rw [r1, runBlock_reg bmB7 _ _ r s.zero (by simp only [bmB7]; revert h1 h2 h3; revert r; decide)]
  have ez : F + BitVec.ofNat 32 0xB9A8 + 0 = F + BitVec.ofNat 32 0xB9A8 := BitVec.add_zero _
  have e57 : F + 0x57 = F + BitVec.ofNat 32 0x50 + 7 := by rw [BitVec.add_assoc]; rfl
  have ha1 : reg n1 a1 = (n.mem (F + BitVec.ofNat 32 0xB9A8 + 7)).zeroExtend 32 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB7, upd, ↓reduceIte]; rw [h20]
  have ha0 : reg n1 a0 = (n.mem (F + BitVec.ofNat 32 0x50 + 7)).zeroExtend 32 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB7, upd, ↓reduceIte]; rw [hsp, e57]
  have h9 : reg n1 9 = 2 := by
    rw [r1]; simp +decide only [runBlock, BInstr.run, bmB7, upd, ↓reduceIte]; (try rw [s.zero]); try rfl
  have r20 : reg n1 20 = F + BitVec.ofNat 32 0xB9A8 := by
    rw [k1 20 (by decide) (by decide) (by decide)]; exact h20
  have sp1 : reg n1 sp = F := by rw [k1 sp (by decide) (by decide) (by decide)]; exact hsp
  have hK1 : BmKeep M0 n1.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [m1]; exact hK
  have hc1' := hK1.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  cases hda : decodeRecord (bmcFlash flash 0x28000 32) with
  | none =>
    rw [hda] at hc0
    obtain ⟨n2, e2, t2⟩ := t1.notTaken hc1' 0xC2 bm_at_be (by decide)
      (by rw [ha1, h9, bme_z2 hc0]; rfl)
    cases hdb : decodeRecord (bmcFlash flash 0x29000 32) with
    | none =>
      rw [hdb] at hc1
      obtain ⟨n3, e3, t3⟩ := t2.notTaken hc1' 0xC6 bm_at_c2 (by decide)
        (by rw [ha0, h9, bme_z2 hc1]; rfl)
      refine BmEnd.pre (c1.trans (.cons e2 (.single e3))) ?_
      have hrec : bmRecs flash = (State.default, none) := by unfold bmRecs readRecords; rw [hda, hdb]
      have mm : n3.mem = n1.mem := t3.mem
      rw [← mm] at hK1
      exact bme_def X ⟨t3.pc, rfl, fun _ => rfl⟩ hF hK1 hrec (by rw [t3.regs]; exact h9)
        (by rw [t3.regs]; exact r20) (by rw [t3.regs]; exact sp1)
    | some sb =>
      rw [hdb] at hc1
      obtain ⟨n3, e3, t3⟩ := t2.taken hc1' 0xEC bm_at_c2 (by decide)
        (bne_iff_ne.mpr (by rw [ha0, h9]; exact bme_zne hc1.2.2.1))
      refine BmEnd.pre (c1.trans (.cons e2 (.single e3))) ?_
      have hrec : bmRecs flash = (sb, some .b) := by unfold bmRecs readRecords; rw [hda, hdb]
      have mm : n3.mem = n.mem := (t3.mem).trans m1
      rw [← t3.mem] at hK1
      exact bme_c1 X ⟨t3.pc, rfl, fun _ => rfl⟩ hF hK1 hrec (by rw [mm]; exact hc1)
        (by rw [t3.regs]; exact r20) (by rw [t3.regs]; exact sp1)
  | some sa =>
    rw [hda] at hc0
    obtain ⟨n2, e2, t2⟩ := t1.taken hc1' 0xDE bm_at_be (by decide)
      (bne_iff_ne.mpr (by rw [ha1, h9]; exact bme_zne hc0.2.2.1))
    cases hdb : decodeRecord (bmcFlash flash 0x29000 32) with
    | none =>
      rw [hdb] at hc1
      obtain ⟨n3, e3, t3⟩ := t2.taken hc1' 0x100 bm_at_de (by decide)
        (by rw [ha0, h9, bme_z2 hc1]; rfl)
      refine BmEnd.pre (c1.trans (.cons e2 (.single e3))) ?_
      have hrec : bmRecs flash = (sa, some .a) := by unfold bmRecs readRecords; rw [hda, hdb]
      have mm : n3.mem = n.mem := (t3.mem).trans m1
      rw [← t3.mem] at hK1
      exact bme_c0 X ⟨t3.pc, rfl, fun _ => rfl⟩ hF hK1 hrec (by rw [mm]; exact hc0)
        (by rw [t3.regs]; exact r20) (by rw [t3.regs]; exact sp1)
    | some sb =>
      rw [hdb] at hc1
      obtain ⟨n3, e3, t3⟩ := t2.notTaken hc1' 0xE2 bm_at_de (by decide)
        (beq_eq_false_iff_ne.mpr (by rw [ha0, h9]; exact bme_zne hc1.2.2.1))
      have mm3 : n3.mem = n.mem := (t3.mem).trans m1
      have t3' : St n3.mem BM n3 0xE2 (reg n3) := ⟨t3.pc, rfl, fun _ => rfl⟩
      have hK3 : BmKeep M0 n3.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
        rw [mm3]; exact hK
      have r3 : ∀ r, reg n3 r = reg n1 r := fun r => t3.regs r
      have hc3 := hK3.codeIn C C.code (.inr ⟨by decide, by decide⟩)
      obtain ⟨n4, c4, u4⟩ := t3'.block bmB10 hc3 bmB10_end
        ⟨by show (reg n3 sp + 0x50).toNat % 4 = 0; rw [r3, sp1]; exact bme_F4 C hF (c := 0x50) (by decide) (by decide),
          by
            show (reg n3 20 + 0).toNat % 4 = 0
            rw [r3, r20, ez]; exact bme_F4 C hF (c := 0xB9A8) (by decide) (by decide),
          trivial⟩
      have m4 : n4.mem = n.mem := u4.mem.trans mm3
      have r4 : ∀ r, reg n4 r = (runBlock bmB10 (n3.mem, reg n3)).2 r := fun r => by rw [u4.regs]
      have t4 : St n4.mem BM n4 0xE8 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
      have k4 : ∀ r, r ≠ a0 → r ≠ a1 → reg n4 r = reg n3 r := fun r h1 h2 => by
        rw [r4, runBlock_reg bmB10 _ _ r t3'.zero (by simp only [bmB10]; revert h1 h2; revert r; decide)]
      have g4a0 : reg n4 a0 = BitVec.ofNat 32 sb.generation := by
        rw [r4]; simp +decide only [runBlock, BInstr.run, bmB10, upd, ↓reduceIte]
        rw [r3, sp1, mm3, show F + 0x50 = F + BitVec.ofNat 32 0x50 from rfl]; exact hc1.1
      have g4a1 : reg n4 a1 = BitVec.ofNat 32 sa.generation := by
        rw [r4]; simp +decide only [runBlock, BInstr.run, bmB10, upd, ↓reduceIte]
        rw [r3, r20, mm3, ez]; exact hc0.1
      have hK4 : BmKeep M0 n4.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
        rw [m4]; exact hK
      have hc4 := hK4.codeIn C C.code (.inr ⟨by decide, by decide⟩)
      have r20' : reg n4 20 = F + BitVec.ofNat 32 0xB9A8 := by
        rw [k4 20 (by decide) (by decide), r3]; exact r20
      have sp4 : reg n4 sp = F := by rw [k4 sp (by decide) (by decide), r3]; exact sp1
      have hu : (BitVec.ofNat 32 sa.generation).ult (BitVec.ofNat 32 sb.generation) =
          decide (sa.generation < sb.generation) := bmt_ult_eq _ _ hc0.2.2.2.1 hc1.2.2.2.1
      by_cases hlt : sa.generation < sb.generation
      · obtain ⟨n5, e5, t5⟩ := t4.notTaken hc4 0xEC bm_at_e8 (by decide)
          (by show (!(reg n4 a1).ult (reg n4 a0)) = false; rw [g4a0, g4a1, hu, decide_eq_true hlt]; rfl)
        refine BmEnd.pre (c1.trans (.cons e2 (.cons e3 (c4.trans (.single e5))))) ?_
        have hrec : bmRecs flash = (sb, some .b) := by
          unfold bmRecs readRecords; rw [hda, hdb]; exact ite_eq_left_of_eq_true _ _ (eq_true hlt)
        rw [← t5.mem] at hK4
        exact bme_c1 X ⟨t5.pc, rfl, fun _ => rfl⟩ hF hK4 hrec (by rw [t5.mem, m4]; exact hc1)
          (by rw [t5.regs]; exact r20') (by rw [t5.regs]; exact sp4)
      · obtain ⟨n5, e5, t5⟩ := t4.taken hc4 0x100 bm_at_e8 (by decide)
          (by show (!(reg n4 a1).ult (reg n4 a0)) = true; rw [g4a0, g4a1, hu, decide_eq_false hlt]; rfl)
        refine BmEnd.pre (c1.trans (.cons e2 (.cons e3 (c4.trans (.single e5))))) ?_
        have hrec : bmRecs flash = (sa, some .a) := by
          unfold bmRecs readRecords; rw [hda, hdb]; exact ite_eq_right_of_eq_false _ _ (eq_false hlt)
        rw [← t5.mem] at hK4
        exact bme_c0 X ⟨t5.pc, rfl, fun _ => rfl⟩ hF hK4 hrec (by rw [t5.mem, m4]; exact hc0)
          (by rw [t5.regs]; exact r20') (by rw [t5.regs]; exact sp4)

end C3.RV32.Cur
