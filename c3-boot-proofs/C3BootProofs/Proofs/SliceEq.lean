import C3BootProofs.Proofs.Leaves
import C3BootProofs.Proofs.DerTlv

/-!
# Byte-slice equality, as compiled

`<[u8] as PartialEq>::eq` compares the lengths and tail-calls
`<u8 as SlicePartialEq<u8>>::equal_same_length`, which calls `memcmp` and
returns whether it found no difference.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem esl_at_0 : fetchRel equalSameLengthCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem esl_at_2 : fetchRel equalSameLengthCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem esl_at_4 : fetchRel equalSameLengthCode 0x4 = some (.auipc ra 0xD000, 4) := by decide
theorem esl_at_8 : fetchRel equalSameLengthCode 0x8 = some (.jalr ra ra 0xFFFFF90E, 4) := by decide
theorem esl_at_c : fetchRel equalSameLengthCode 0xC = some (.aluImm .sltu a0 a0 0x1, 4) := by decide
theorem esl_at_10 : fetchRel equalSameLengthCode 0x10 = some (.load .lw ra sp 0xC, 2) := by decide
theorem esl_at_12 : fetchRel equalSameLengthCode 0x12 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem esl_at_14 : fetchRel equalSameLengthCode 0x14 = some (.jalr x0 ra 0x0, 2) := by decide
theorem seq_at_0 : fetchRel sliceEqCode 0x0 = some (.branch .bne a1 a3 0x12, 4) := by decide
theorem seq_at_4 : fetchRel sliceEqCode 0x4 = some (.alu .add a4 x0 a1, 2) := by decide
theorem seq_at_6 : fetchRel sliceEqCode 0x6 = some (.alu .add a1 x0 a2, 2) := by decide
theorem seq_at_8 : fetchRel sliceEqCode 0x8 = some (.alu .add a2 x0 a4, 2) := by decide
theorem seq_at_a : fetchRel sliceEqCode 0xA = some (.auipc (6 : Fin 32) 0xFFFFF000, 4) := by decide
theorem seq_at_e : fetchRel sliceEqCode 0xE = some (.jalr x0 (6 : Fin 32) 0x76C, 4) := by decide
theorem seq_at_12 : fetchRel sliceEqCode 0x12 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem seq_at_14 : fetchRel sliceEqCode 0x14 = some (.jalr x0 ra 0x0, 2) := by decide
end

theorem memBytes_eq_iff {M : Word → BitVec 8} {p q : Word} {n : Nat} :
    memBytes M p n = memBytes M q n ↔ ∀ i, i < n → M (p + BitVec.ofNat 32 i) = M (q + BitVec.ofNat 32 i) := by
  constructor
  · intro h i hi
    have := congrArg (fun l => l.getD i 0) h
    simp only [memBytes_getD hi] at this
    exact BitVec.eq_of_toNat_eq this
  · intro h
    unfold memBytes
    exact List.map_congr_left fun i hi => by rw [h i (List.mem_range.mp hi)]

/-- **The compiled `equal_same_length`** returns 1 when the `n` bytes at `p`
equal the `n` bytes at `q` and 0 otherwise. It saves `ra` in the word below
`sp`. -/
theorem equalSameLength_correct (m : Machine) {base retAddr p q : Word} {n : Nat} (hP : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base equalSameLengthCode) (hm : CodeIn m.mem (base + 0xC912) memcmpCode) (hpc : m.pc = base)
    (ha0 : reg m a0 = p) (ha1 : reg m a1 = q) (ha2 : reg m a2 = BitVec.ofNat 32 n) (hn : n < 2 ^ 32)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : (reg m sp).toNat % 4 = 0)
    (sSC : Sep (reg m sp + 0xFFFFFFFC) 4 base equalSameLengthCode.length)
    (sSM : Sep (reg m sp + 0xFFFFFFFC) 4 (base + 0xC912) memcmpCode.length)
    (sSP : Sep (reg m sp + 0xFFFFFFFC) 4 p n) (sSQ : Sep (reg m sp + 0xFFFFFFFC) 4 q n) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (if memBytes m.mem p n = memBytes m.mem q n then 1 else 0) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFFC) 4 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨G, hG⟩ : ∃ G, reg m sp + 0xFFFFFFF0 = G := ⟨_, rfl⟩
  have eG : G + 0xC = reg m sp + 0xFFFFFFFC := by rw [← hG, BitVec.add_assoc]; rfl
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc esl_at_0 (off' := 2) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.sw hc esl_at_2 (off' := 4) (by decide) (by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hG, eG]; exact aligned_add hsp (k := 0xFFFFFFFC) (by decide))
  simp +decide only [upd_app, ↓reduceIte] at u2
  rw [ev_add, hG, eG, hra] at u2
  have hc2 := CodeIn.store32 (v := retAddr) hc sSC
  have frS : ∀ x, Sep (reg m sp + 0xFFFFFFFC) 4 x 1 → memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr x = m.mem x :=
    fun x hx => memStore32_get_sep hx
  have hm2 : CodeIn (memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr) (base + 0xC912) memcmpCode := fun i hi => by
    rw [frS _ (sSM.subR (c := i) (l := 1) (by omega))]; exact hm i hi
  obtain ⟨n3, c3, pc3, mem3, regs3⟩ := u2.self.callRa hc2 esl_at_4 esl_at_8
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hP 0xC912 (by decide))
  have r3 := PEnv.reg1 regs3 u2.self.zero
  have k2 : ∀ q, q ≠ sp → reg n2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  obtain ⟨n4, c4, pc4, a04, k4, mem4⟩ := memcmp_correct n3 (n := n) (by rw [mem3]; exact hm2) pc3
    (by rw [r3 a0 (by decide), k2 a0 (by decide), ha0]) (by rw [r3 a1 (by decide), k2 a1 (by decide), ha1])
    (by rw [r3 a2 (by decide), k2 a2 (by decide), ha2]) hn (by rw [regs3]; simp +decide [upd])
    (even_clear _ (even_at base hP (4 + 8) (by decide)))
  rw [mem3] at a04 mem4
  have hall : (∀ i, i < n → (memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr) (p + BitVec.ofNat 32 i) =
      (memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr) (q + BitVec.ofNat 32 i)) ↔
      memBytes m.mem p n = memBytes m.mem q n := by
    rw [memBytes_eq_iff]
    constructor
    · intro h i hi
      rw [← frS _ (sSP.subR (c := i) (l := 1) hi), ← frS _ (sSQ.subR (c := i) (l := 1) hi)]; exact h i hi
    · intro h i hi
      rw [frS _ (sSP.subR (c := i) (l := 1) hi), frS _ (sSQ.subR (c := i) (l := 1) hi)]; exact h i hi
  obtain ⟨Ms, hMs⟩ : ∃ Ms, memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr = Ms := ⟨_, rfl⟩
  rw [hMs] at mem4 hc2 hall frS a04
  have u4 : St Ms base n4 0xC (reg n4) := ⟨by rw [pc4], mem4, fun _ => rfl⟩
  have sp4 : reg n4 sp = G := by
    rw [k4 sp (by decide) (by decide) (by decide) (by decide) (by decide), r3 sp (by decide), u2.regs]
    simp +decide only [upd_app, ↓reduceIte]
  have k4' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ sp → reg n4 q = reg m q :=
    fun q h0 h1 h2 h3 h4 hr hs => by rw [k4 q h0 h1 h2 h3 h4, r3 q hr, k2 q hs]
  obtain ⟨n5, d5, u5⟩ := u4.aluImm hc2 esl_at_c (off' := 0x10) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5.lw hc2 esl_at_10 (off' := 0x12) (by decide) (by
    rw [upd_ne (by decide) (by decide), sp4, eG]; exact aligned_add hsp (k := 0xFFFFFFFC) (by decide))
  have eRa : memLoad32 Ms (reg m sp + 0xFFFFFFFC) = retAddr := by rw [← hMs]; exact memLoad32_store32_same _ _ _
  rw [upd_ne (by decide) (by decide), sp4, eG, eRa] at u6
  obtain ⟨n7, d7, u7⟩ := u6.aluImm hc2 esl_at_12 (off' := 0x14) (by decide)
  obtain ⟨n8, d8, pc8, mem8, regs8⟩ := u7.jalr hc2 esl_at_14
  have hsl1 : ∀ x : Word, aluEval .sltu x 1 = if x = 0 then 1 else 0 := fun x => by
    by_cases h : x = 0
    · rw [h]; rfl
    · rw [ite_eq_right h]
      show (if x.ult 1 then (1 : Word) else 0) = 0
      exact ite_eq_right (by
        show ¬ decide (x.toNat < (1 : Word).toNat) = true
        rw [decide_eq_true_iff]; intro hx
        exact h (BitVec.eq_of_toNat_eq (by change x.toNat < 1 at hx; change x.toNat = 0; omega)))
  refine ⟨n8, .cons d1 (.cons d2 (c3.trans (c4.trans (.cons d5 (.cons d6 (.cons d7 (.single d8))))))), ?_, ?_,
    fun r h0 h1 h2 h3 h4 => ?_, fun x hx => by rw [mem8, ← frS x hx]⟩
  · rw [pc8]; simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero, hret]
  · rw [regs8]; simp +decide only [upd_app, ↓reduceIte]
    rw [hsl1]
    by_cases he : memBytes m.mem p n = memBytes m.mem q n
    · rw [ite_eq_left he, ite_eq_left ((a04.mpr ((hall).mpr he)))]
    · rw [ite_eq_right he, ite_eq_right (fun h => he (hall.mp (a04.mp h)))]
  · rw [regs8]
    by_cases hr : r = ra
    · subst hr; simp +decide only [upd_app, ↓reduceIte]; rw [hra]
    by_cases hs : r = sp
    · subst hs; simp +decide only [upd_app, ↓reduceIte]
      rw [sp4, ← hG, ev_add, BitVec.add_assoc]; exact BitVec.add_zero _
    by_cases hz0 : r.val = 0
    · have : r = 0 := Fin.ext hz0
      subst this; simp [upd]; exact hz.symm
    simp only [upd_app, hz0, hr, hs, h0, ite_false]
    exact k4' r h0 h1 h2 h3 h4 hr hs

/-- **The compiled `<[u8] as PartialEq>::eq`** returns 1 when the `pl` bytes
at `p` equal the `ql` bytes at `q`, lengths included, and 0 otherwise. -/
theorem sliceEq_correct (m : Machine) {base retAddr p q : Word} {pl ql : Nat} (hP : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base sliceEqCode) (he : CodeIn m.mem (base + 0xFFFFF776) equalSameLengthCode)
    (hm : CodeIn m.mem (base + 0xC088) memcmpCode) (hpc : m.pc = base)
    (ha0 : reg m a0 = p) (ha1 : reg m a1 = BitVec.ofNat 32 pl) (ha2 : reg m a2 = q)
    (ha3 : reg m a3 = BitVec.ofNat 32 ql) (hpl : pl < 2 ^ 32) (hql : ql < 2 ^ 32)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : (reg m sp).toNat % 4 = 0)
    (sSE : Sep (reg m sp + 0xFFFFFFFC) 4 (base + 0xFFFFF776) equalSameLengthCode.length)
    (sSM : Sep (reg m sp + 0xFFFFFFFC) 4 (base + 0xC088) memcmpCode.length)
    (sSP : Sep (reg m sp + 0xFFFFFFFC) 4 p pl) (sSQ : Sep (reg m sp + 0xFFFFFFFC) 4 q ql) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (if memBytes m.mem p pl = memBytes m.mem q ql then 1 else 0) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ t1 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFFC) 4 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  by_cases hne : pl = ql
  · subst hne
    obtain ⟨n1, d1, u1⟩ := s0.notTaken hc 0x4 seq_at_0 (by decide) (by
      rw [ha1, ha3]; simp only [branchTaken, bne_self_eq_false])
    obtain ⟨n2, c2, u2⟩ := St.block [.alu .add a4 x0 a1, .alu .add a1 x0 a2, .alu .add a2 x0 a4] u1 hc
      (off' := 0xA) (by decide) (by simp [BlockOk, BInstr.ok])
    simp only [runBlock, BInstr.run] at u2
    obtain ⟨n3, d3, u3⟩ := u2.auipc hc seq_at_a (off' := 0xE) (by decide)
    obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.jalr hc seq_at_e
    have pcE : n4.pc = base + 0xFFFFF776 := by
      rw [pc4]; simp +decide only [upd_app, ↓reduceIte]
      rw [show base + BitVec.ofNat 32 0xA + 0xFFFFF000 + 0x76C = base + 0xFFFFF776 by
        rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
      exact even_clear _ (even_at base hP 0xFFFFF776 (by decide))
    have g4 : ∀ r, reg n4 r = _ := regs4
    have kq : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a4 → r ≠ t1 → reg n4 r = reg m r := fun r h1 h2 h4 ht => by
      rw [g4]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz.symm
      simp only [upd_app, h0, h1, h2, h4, ht, ite_false]
    have sp4 : reg n4 sp = reg m sp := kq sp (by decide) (by decide) (by decide) (by decide)
    obtain ⟨m5, c5, pc5, a05, k5, f5⟩ := equalSameLength_correct n4 (p := p) (q := q) (n := pl)
      (even_at base hP 0xFFFFF776 (by decide)) (by rw [mem4]; exact he)
      (by rw [mem4, show base + BitVec.ofNat 32 0xFFFFF776 + 0xC912 = base + 0xC088 by rw [BitVec.add_assoc]; rfl]; exact hm) pcE
      (by rw [kq a0 (by decide) (by decide) (by decide) (by decide), ha0])
      (by rw [g4]; simp +decide only [upd_app, ↓reduceIte]; rw [ha2]; exact zw _)
      (by rw [g4]; simp +decide only [upd_app, ↓reduceIte]; rw [ha1]
          show (0 : Word) + (reg m 0 + BitVec.ofNat 32 pl) = _; rw [hz, zw, zw])
      hpl (by rw [kq ra (by decide) (by decide) (by decide) (by decide), hra]) hret (by rw [sp4]; exact hsp)
      (by rw [sp4]; exact sSE)
      (by rw [sp4, show base + BitVec.ofNat 32 0xFFFFF776 + 0xC912 = base + 0xC088 by rw [BitVec.add_assoc]; rfl]; exact sSM)
      (by rw [sp4]; exact sSP) (by rw [sp4]; exact sSQ)
    rw [mem4] at a05
    rw [mem4, sp4] at f5
    refine ⟨m5, .cons d1 (c2.trans (.cons d3 (.cons d4 c5))), pc5, a05, fun r h0 h1 h2 h3 h4 ht => ?_, f5⟩
    rw [k5 r h0 h1 h2 h3 h4, kq r h1 h2 h4 ht]
  · obtain ⟨n1, d1, u1⟩ := s0.taken hc 0x12 seq_at_0 (by decide) (by
      rw [ha1, ha3]; simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
      have := congrArg BitVec.toNat h; rw [ofNat_tn hpl, ofNat_tn hql] at this; exact hne this)
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hc seq_at_12 (off' := 0x14) (by decide)
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc seq_at_14
    refine ⟨n3, .cons d1 (.cons d2 (.single d3)), ?_, ?_, fun r h0 _ _ _ _ _ => ?_, fun x _ => by rw [mem3]⟩
    · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [hra, add_lit_zero, hret]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]
      have : memBytes m.mem p pl ≠ memBytes m.mem q ql := fun h => hne (by
        have := congrArg List.length h; rwa [memBytes_length, memBytes_length] at this)
      rw [ite_eq_right this, hz]; rfl
    · rw [regs3, updz hz h0]

end C3.RV32
