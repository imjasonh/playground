import C3BootProofs.Proofs.SliceEq

/-!
# Byte-array and byte-slice comparisons, as compiled

`<[u8; 32] as PartialEq>::eq` and `ne` in `c3_verify` call `memcmp` on 32
bytes and turn its result into 1 or 0. `c3_verify` compares digests with
them. `<&[u8] as PartialEq>::ne` calls the proved slice `eq` and negates it.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem aeq_at_0 : fetchRel arr32EqCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem aeq_at_2 : fetchRel arr32EqCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem aeq_at_4 : fetchRel arr32EqCode 0x4 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem aeq_at_8 : fetchRel arr32EqCode 0x8 = some (.auipc ra 0xC000, 4) := by decide
theorem aeq_at_c : fetchRel arr32EqCode 0xC = some (.jalr ra ra 0x2A, 4) := by decide
theorem aeq_at_10 : fetchRel arr32EqCode 0x10 = some (.aluImm .sltu a0 a0 0x1, 4) := by decide
theorem aeq_at_14 : fetchRel arr32EqCode 0x14 = some (.load .lw ra sp 0xC, 2) := by decide
theorem aeq_at_16 : fetchRel arr32EqCode 0x16 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem aeq_at_18 : fetchRel arr32EqCode 0x18 = some (.jalr x0 ra 0x0, 2) := by decide
theorem ane_at_0 : fetchRel arr32NeCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem ane_at_2 : fetchRel arr32NeCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem ane_at_4 : fetchRel arr32NeCode 0x4 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem ane_at_8 : fetchRel arr32NeCode 0x8 = some (.auipc ra 0xA000, 4) := by decide
theorem ane_at_c : fetchRel arr32NeCode 0xC = some (.jalr ra ra 0xFFFFFF08, 4) := by decide
theorem ane_at_10 : fetchRel arr32NeCode 0x10 = some (.alu .sltu a0 x0 a0, 4) := by decide
theorem ane_at_14 : fetchRel arr32NeCode 0x14 = some (.load .lw ra sp 0xC, 2) := by decide
theorem ane_at_16 : fetchRel arr32NeCode 0x16 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem ane_at_18 : fetchRel arr32NeCode 0x18 = some (.jalr x0 ra 0x0, 2) := by decide
theorem sne_at_0 : fetchRel sliceNeCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem sne_at_2 : fetchRel sliceNeCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem sne_at_4 : fetchRel sliceNeCode 0x4 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem sne_at_8 : fetchRel sliceNeCode 0x8 = some (.jalr ra ra 0x36E, 4) := by decide
theorem sne_at_c : fetchRel sliceNeCode 0xC = some (.aluImm .xor a0 a0 0x1, 4) := by decide
theorem sne_at_10 : fetchRel sliceNeCode 0x10 = some (.load .lw ra sp 0xC, 2) := by decide
theorem sne_at_12 : fetchRel sliceNeCode 0x12 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem sne_at_14 : fetchRel sliceNeCode 0x14 = some (.jalr x0 ra 0x0, 2) := by decide
theorem aec_at_0 : fetchRel arr32EqCryptoCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem aec_at_2 : fetchRel arr32EqCryptoCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem aec_at_4 : fetchRel arr32EqCryptoCode 0x4 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem aec_at_8 : fetchRel arr32EqCryptoCode 0x8 = some (.auipc ra 0x12000, 4) := by decide
theorem aec_at_c : fetchRel arr32EqCryptoCode 0xC = some (.jalr ra ra 0xFFFFF88E, 4) := by decide
theorem aec_at_10 : fetchRel arr32EqCryptoCode 0x10 = some (.aluImm .sltu a0 a0 0x1, 4) := by decide
theorem aec_at_14 : fetchRel arr32EqCryptoCode 0x14 = some (.load .lw ra sp 0xC, 2) := by decide
theorem aec_at_16 : fetchRel arr32EqCryptoCode 0x16 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem aec_at_18 : fetchRel arr32EqCryptoCode 0x18 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- **The compiled `<[u8; 32] as PartialEq>::eq`** returns 1 when the 32
bytes at `p` equal the 32 bytes at `q` and 0 otherwise. It saves `ra` in the
word below `sp`. -/
theorem arr32Eq_correct (m : Machine) {base retAddr p q : Word} (hP : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base arr32EqCode) (hm : CodeIn m.mem (base + 0xC032) memcmpCode) (hpc : m.pc = base)
    (ha0 : reg m a0 = p) (ha1 : reg m a1 = q)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : (reg m sp).toNat % 4 = 0)
    (sSC : Sep (reg m sp + 0xFFFFFFFC) 4 base arr32EqCode.length)
    (sSM : Sep (reg m sp + 0xFFFFFFFC) 4 (base + 0xC032) memcmpCode.length)
    (sSP : Sep (reg m sp + 0xFFFFFFFC) 4 p 32) (sSQ : Sep (reg m sp + 0xFFFFFFFC) 4 q 32) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (if memBytes m.mem p 32 = memBytes m.mem q 32 then 1 else 0) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFFC) 4 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨G, hG⟩ : ∃ G, reg m sp + 0xFFFFFFF0 = G := ⟨_, rfl⟩
  have eG : G + 0xC = reg m sp + 0xFFFFFFFC := by rw [← hG, BitVec.add_assoc]; rfl
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc aeq_at_0 (off' := 2) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.sw hc aeq_at_2 (off' := 4) (by decide) (by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hG, eG]; exact aligned_add hsp (k := 0xFFFFFFFC) (by decide))
  simp +decide only [upd_app, ↓reduceIte] at u2
  rw [ev_add, hG, eG, hra] at u2
  have hc2 := CodeIn.store32 (v := retAddr) hc sSC
  have frS : ∀ x, Sep (reg m sp + 0xFFFFFFFC) 4 x 1 → memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr x = m.mem x :=
    fun x hx => memStore32_get_sep hx
  have hm2 : CodeIn (memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr) (base + 0xC032) memcmpCode := fun i hi => by
    rw [frS _ (sSM.subR (c := i) (l := 1) (by omega))]; exact hm i hi
  obtain ⟨n2', d2', u2'⟩ := u2.self.aluImm hc2 aeq_at_4 (off' := 8) (by decide)
  obtain ⟨n3, c3, pc3, mem3, regs3⟩ := u2'.self.callRa hc2 aeq_at_8 aeq_at_c
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hP 0xC032 (by decide))
  have r3 := PEnv.reg1 regs3 u2'.self.zero
  have k2 : ∀ q, q ≠ sp → q ≠ a2 → reg n2' q = reg m q := fun q h h2 => by
    rw [u2'.regs, upd_ne' h2 u2.self.zero, u2.regs, updz hz h]
  obtain ⟨n4, c4, pc4, a04, k4, mem4⟩ := memcmp_correct n3 (n := 32) (by rw [mem3]; exact hm2) pc3
    (by rw [r3 a0 (by decide), k2 a0 (by decide) (by decide), ha0])
    (by rw [r3 a1 (by decide), k2 a1 (by decide) (by decide), ha1])
    (by rw [r3 a2 (by decide), u2'.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u2.self.zero]; rfl)
    (by decide) (by rw [regs3]; simp +decide [upd])
    (even_clear _ (even_at base hP (8 + 8) (by decide)))
  rw [mem3] at a04 mem4
  have hall : (∀ i, i < 32 → (memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr) (p + BitVec.ofNat 32 i) =
      (memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr) (q + BitVec.ofNat 32 i)) ↔
      memBytes m.mem p 32 = memBytes m.mem q 32 := by
    rw [memBytes_eq_iff]
    constructor
    · intro h i hi
      rw [← frS _ (sSP.subR (c := i) (l := 1) hi), ← frS _ (sSQ.subR (c := i) (l := 1) hi)]; exact h i hi
    · intro h i hi
      rw [frS _ (sSP.subR (c := i) (l := 1) hi), frS _ (sSQ.subR (c := i) (l := 1) hi)]; exact h i hi
  obtain ⟨Ms, hMs⟩ : ∃ Ms, memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr = Ms := ⟨_, rfl⟩
  rw [hMs] at mem4 hc2 hall frS a04
  have u4 : St Ms base n4 0x10 (reg n4) := ⟨by rw [pc4], mem4, fun _ => rfl⟩
  have sp4 : reg n4 sp = G := by
    rw [k4 sp (by decide) (by decide) (by decide) (by decide) (by decide), r3 sp (by decide), u2'.regs,
      upd_ne (by decide) (by decide), u2.regs]
    simp +decide only [upd_app, ↓reduceIte]
  have k4' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ sp → reg n4 q = reg m q :=
    fun q h0 h1 h2 h3 h4 hr hs => by rw [k4 q h0 h1 h2 h3 h4, r3 q hr, k2 q hs h2]
  obtain ⟨n5, d5, u5⟩ := u4.aluImm hc2 aeq_at_10 (off' := 0x14) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5.lw hc2 aeq_at_14 (off' := 0x16) (by decide) (by
    rw [upd_ne (by decide) (by decide), sp4, eG]; exact aligned_add hsp (k := 0xFFFFFFFC) (by decide))
  have eRa : memLoad32 Ms (reg m sp + 0xFFFFFFFC) = retAddr := by rw [← hMs]; exact memLoad32_store32_same _ _ _
  rw [upd_ne (by decide) (by decide), sp4, eG, eRa] at u6
  obtain ⟨n7, d7, u7⟩ := u6.aluImm hc2 aeq_at_16 (off' := 0x18) (by decide)
  obtain ⟨n8, d8, pc8, mem8, regs8⟩ := u7.jalr hc2 aeq_at_18
  have hsl1 : ∀ x : Word, aluEval .sltu x 1 = if x = 0 then 1 else 0 := fun x => by
    by_cases h : x = 0
    · rw [h]; rfl
    · rw [ite_eq_right h]
      show (if x.ult 1 then (1 : Word) else 0) = 0
      exact ite_eq_right (by
        show ¬ decide (x.toNat < (1 : Word).toNat) = true
        rw [decide_eq_true_iff]; intro hx
        exact h (BitVec.eq_of_toNat_eq (by change x.toNat < 1 at hx; change x.toNat = 0; omega)))
  refine ⟨n8, .cons d1 (.cons d2 (.cons d2' (c3.trans (c4.trans (.cons d5 (.cons d6 (.cons d7 (.single d8)))))))), ?_, ?_,
    fun r h0 h1 h2 h3 h4 => ?_, fun x hx => by rw [mem8, ← frS x hx]⟩
  · rw [pc8]; simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero, hret]
  · rw [regs8]; simp +decide only [upd_app, ↓reduceIte]
    rw [hsl1]
    by_cases he : memBytes m.mem p 32 = memBytes m.mem q 32
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

/-- **The compiled `<[u8; 32] as PartialEq>::ne`** returns 0 when the 32
bytes at `p` equal the 32 bytes at `q` and 1 otherwise. It saves `ra` in the
word below `sp`. -/
theorem arr32Ne_correct (m : Machine) {base retAddr p q : Word} (hP : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base arr32NeCode) (hm : CodeIn m.mem (base + 0x9F10) memcmpCode) (hpc : m.pc = base)
    (ha0 : reg m a0 = p) (ha1 : reg m a1 = q)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : (reg m sp).toNat % 4 = 0)
    (sSC : Sep (reg m sp + 0xFFFFFFFC) 4 base arr32NeCode.length)
    (sSM : Sep (reg m sp + 0xFFFFFFFC) 4 (base + 0x9F10) memcmpCode.length)
    (sSP : Sep (reg m sp + 0xFFFFFFFC) 4 p 32) (sSQ : Sep (reg m sp + 0xFFFFFFFC) 4 q 32) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (if memBytes m.mem p 32 = memBytes m.mem q 32 then 0 else 1) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFFC) 4 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨G, hG⟩ : ∃ G, reg m sp + 0xFFFFFFF0 = G := ⟨_, rfl⟩
  have eG : G + 0xC = reg m sp + 0xFFFFFFFC := by rw [← hG, BitVec.add_assoc]; rfl
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc ane_at_0 (off' := 2) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.sw hc ane_at_2 (off' := 4) (by decide) (by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hG, eG]; exact aligned_add hsp (k := 0xFFFFFFFC) (by decide))
  simp +decide only [upd_app, ↓reduceIte] at u2
  rw [ev_add, hG, eG, hra] at u2
  have hc2 := CodeIn.store32 (v := retAddr) hc sSC
  have frS : ∀ x, Sep (reg m sp + 0xFFFFFFFC) 4 x 1 → memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr x = m.mem x :=
    fun x hx => memStore32_get_sep hx
  have hm2 : CodeIn (memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr) (base + 0x9F10) memcmpCode := fun i hi => by
    rw [frS _ (sSM.subR (c := i) (l := 1) (by omega))]; exact hm i hi
  obtain ⟨n2', d2', u2'⟩ := u2.self.aluImm hc2 ane_at_4 (off' := 8) (by decide)
  obtain ⟨n3, c3, pc3, mem3, regs3⟩ := u2'.self.callRa hc2 ane_at_8 ane_at_c
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hP 0x9F10 (by decide))
  have r3 := PEnv.reg1 regs3 u2'.self.zero
  have k2 : ∀ q, q ≠ sp → q ≠ a2 → reg n2' q = reg m q := fun q h h2 => by
    rw [u2'.regs, upd_ne' h2 u2.self.zero, u2.regs, updz hz h]
  obtain ⟨n4, c4, pc4, a04, k4, mem4⟩ := memcmp_correct n3 (n := 32) (by rw [mem3]; exact hm2) pc3
    (by rw [r3 a0 (by decide), k2 a0 (by decide) (by decide), ha0])
    (by rw [r3 a1 (by decide), k2 a1 (by decide) (by decide), ha1])
    (by rw [r3 a2 (by decide), u2'.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u2.self.zero]; rfl)
    (by decide) (by rw [regs3]; simp +decide [upd])
    (even_clear _ (even_at base hP (8 + 8) (by decide)))
  rw [mem3] at a04 mem4
  have hall : (∀ i, i < 32 → (memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr) (p + BitVec.ofNat 32 i) =
      (memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr) (q + BitVec.ofNat 32 i)) ↔
      memBytes m.mem p 32 = memBytes m.mem q 32 := by
    rw [memBytes_eq_iff]
    constructor
    · intro h i hi
      rw [← frS _ (sSP.subR (c := i) (l := 1) hi), ← frS _ (sSQ.subR (c := i) (l := 1) hi)]; exact h i hi
    · intro h i hi
      rw [frS _ (sSP.subR (c := i) (l := 1) hi), frS _ (sSQ.subR (c := i) (l := 1) hi)]; exact h i hi
  obtain ⟨Ms, hMs⟩ : ∃ Ms, memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr = Ms := ⟨_, rfl⟩
  rw [hMs] at mem4 hc2 hall frS a04
  have u4 : St Ms base n4 0x10 (reg n4) := ⟨by rw [pc4], mem4, fun _ => rfl⟩
  have sp4 : reg n4 sp = G := by
    rw [k4 sp (by decide) (by decide) (by decide) (by decide) (by decide), r3 sp (by decide), u2'.regs,
      upd_ne (by decide) (by decide), u2.regs]
    simp +decide only [upd_app, ↓reduceIte]
  have k4' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ sp → reg n4 q = reg m q :=
    fun q h0 h1 h2 h3 h4 hr hs => by rw [k4 q h0 h1 h2 h3 h4, r3 q hr, k2 q hs h2]
  obtain ⟨n5, d5, u5⟩ := u4.alu hc2 ane_at_10 (off' := 0x14) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5.lw hc2 ane_at_14 (off' := 0x16) (by decide) (by
    rw [upd_ne (by decide) (by decide), sp4, eG]; exact aligned_add hsp (k := 0xFFFFFFFC) (by decide))
  have eRa : memLoad32 Ms (reg m sp + 0xFFFFFFFC) = retAddr := by rw [← hMs]; exact memLoad32_store32_same _ _ _
  rw [upd_ne (by decide) (by decide), sp4, eG, eRa] at u6
  obtain ⟨n7, d7, u7⟩ := u6.aluImm hc2 ane_at_16 (off' := 0x18) (by decide)
  obtain ⟨n8, d8, pc8, mem8, regs8⟩ := u7.jalr hc2 ane_at_18
  have hsl1 : ∀ x : Word, aluEval .sltu (reg n4 0) x = if x = 0 then 0 else 1 := fun x => by
    rw [u4.zero]
    by_cases h : x = 0
    · rw [h]; rfl
    · rw [ite_eq_right h]
      show (if (0 : Word).ult x then (1 : Word) else 0) = 1
      exact ite_eq_left (by
        show decide ((0 : Word).toNat < x.toNat) = true
        rw [decide_eq_true_iff]
        have : x.toNat ≠ 0 := fun hx => h (BitVec.eq_of_toNat_eq (by rw [hx]; rfl))
        change 0 < x.toNat; omega)
  refine ⟨n8, .cons d1 (.cons d2 (.cons d2' (c3.trans (c4.trans (.cons d5 (.cons d6 (.cons d7 (.single d8)))))))), ?_, ?_,
    fun r h0 h1 h2 h3 h4 => ?_, fun x hx => by rw [mem8, ← frS x hx]⟩
  · rw [pc8]; simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero, hret]
  · rw [regs8]; simp +decide only [upd_app, ↓reduceIte]
    rw [hsl1]
    by_cases he : memBytes m.mem p 32 = memBytes m.mem q 32
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

/-- **The compiled `<&[u8] as PartialEq>::ne`** returns 0 when the `pl` bytes
at `p` equal the `ql` bytes at `q`, lengths included, and 1 otherwise. It
writes only the 0x14 bytes below `sp`. -/
theorem sliceNe_correct (m : Machine) {base retAddr p q : Word} {pl ql : Nat} (hP : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base sliceNeCode) (hs : CodeIn m.mem (base + 0xFFFFF372) sliceEqCode)
    (he : CodeIn m.mem (base + 0xFFFFDF1C) equalSameLengthCode) (hm : CodeIn m.mem (base + 0xB2DA) memcmpCode)
    (hpc : m.pc = base) (ha0 : reg m a0 = p) (ha1 : reg m a1 = BitVec.ofNat 32 pl) (ha2 : reg m a2 = q)
    (ha3 : reg m a3 = BitVec.ofNat 32 ql) (hpl : pl < 2 ^ 32) (hql : ql < 2 ^ 32)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : (reg m sp).toNat % 4 = 0)
    (sSC : Sep (reg m sp + 0xFFFFFFEC) 0x14 base sliceNeCode.length)
    (sSS : Sep (reg m sp + 0xFFFFFFEC) 0x14 (base + 0xFFFFF372) sliceEqCode.length)
    (sSE : Sep (reg m sp + 0xFFFFFFEC) 0x14 (base + 0xFFFFDF1C) equalSameLengthCode.length)
    (sSM : Sep (reg m sp + 0xFFFFFFEC) 0x14 (base + 0xB2DA) memcmpCode.length)
    (sSP : Sep (reg m sp + 0xFFFFFFEC) 0x14 p pl) (sSQ : Sep (reg m sp + 0xFFFFFFEC) 0x14 q ql) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (if memBytes m.mem p pl = memBytes m.mem q ql then 0 else 1) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ t1 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFEC) 0x14 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨S, hS⟩ : ∃ S, reg m sp = S := ⟨_, rfl⟩
  rw [hS] at hsp sSC sSS sSE sSM sSP sSQ ⊢
  obtain ⟨G, hG⟩ : ∃ G, S + 0xFFFFFFEC = G := ⟨_, rfl⟩
  rw [hG] at sSC sSS sSE sSM sSP sSQ ⊢
  obtain ⟨F, hF⟩ : ∃ F, S + 0xFFFFFFF0 = F := ⟨_, rfl⟩
  have eW : F + 0xC = G + BitVec.ofNat 32 0x10 := by rw [← hF, ← hG, BitVec.add_assoc, BitVec.add_assoc]; rfl
  have eFG : F + 0xFFFFFFFC = G + BitVec.ofNat 32 0 := by
    rw [← hF, ← hG, BitVec.add_assoc, BitVec.add_assoc]; rfl
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add hsp (k := 0xFFFFFFF0) (by decide)
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc sne_at_0 (off' := 2) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.sw hc sne_at_2 (off' := 4) (by decide) (by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hS, hF]; exact aligned_add hFa (k := 0xC) (by decide))
  simp +decide only [upd_app, ↓reduceIte] at u2
  rw [ev_add, hS, hF, eW, hra] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, memStore32 m.mem (G + BitVec.ofNat 32 0x10) retAddr = Ms := ⟨_, rfl⟩
  have frS : ∀ x, Sep G 0x14 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact memStore32_get_sep (hx.sub (c := 0x10) (l := 4) (by decide))
  have cS : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep G 0x14 b code.length → CodeIn Ms b code :=
    fun h hs i hi => by rw [frS _ (hs.subR (c := i) (l := 1) (by omega))]; exact h i hi
  rw [hMs] at u2
  have hc2 := cS hc sSC
  obtain ⟨n3, c3, pc3, mem3, regs3⟩ := u2.self.callRa hc2 sne_at_4 sne_at_8 (cb := base + 0xFFFFF372)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hP 0xFFFFF372 (by decide))
  have r3 := PEnv.reg1 regs3 u2.self.zero
  have k2 : ∀ q, q ≠ sp → reg n2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp3 : reg n3 sp = F := by
    rw [r3 sp (by decide), u2.regs]; simp +decide only [upd_app, ↓reduceIte]
  have sub4 : ∀ {b : Word} {l : Nat}, Sep G 0x14 b l → Sep (reg n3 sp + 0xFFFFFFFC) 4 b l := fun h => by
    rw [sp3, eFG]; exact h.sub (c := 0) (l := 4) (by decide)
  obtain ⟨n4, c4, pc4, a04, k4, f4⟩ := sliceEq_correct n3 (p := p) (q := q) (pl := pl) (ql := ql)
    (even_at base hP 0xFFFFF372 (by decide)) (by rw [mem3]; exact cS hs sSS)
    (by rw [mem3, BitVec.add_assoc]; exact cS he sSE) (by rw [mem3, BitVec.add_assoc]; exact cS hm sSM) pc3
    (by rw [r3 a0 (by decide), k2 a0 (by decide), ha0]) (by rw [r3 a1 (by decide), k2 a1 (by decide), ha1])
    (by rw [r3 a2 (by decide), k2 a2 (by decide), ha2]) (by rw [r3 a3 (by decide), k2 a3 (by decide), ha3])
    hpl hql (by rw [regs3]; simp +decide [upd]) (even_clear _ (even_at base hP (4 + 8) (by decide)))
    (by rw [sp3]; exact hFa)
    (by rw [BitVec.add_assoc]; exact sub4 sSE) (by rw [BitVec.add_assoc]; exact sub4 sSM)
    (sub4 sSP) (sub4 sSQ)
  rw [mem3, memBytes_congr (fun i hi => frS _ (sSP.subR (c := i) (l := 1) (by omega))),
    memBytes_congr (fun i hi => frS _ (sSQ.subR (c := i) (l := 1) (by omega)))] at a04
  rw [mem3] at f4
  have hsep0 : Sep (reg n3 sp + 0xFFFFFFFC) 4 (G + BitVec.ofNat 32 0x10) 4 := by
    rw [sp3, eFG]; exact sep_offsets G (.inl (by decide)) (by decide) (by decide)
  have hc4 : CodeIn n4.mem base sliceNeCode := fun i hi => by
    rw [f4 _ ((sub4 sSC).subR (c := i) (l := 1) (by omega))]; exact hc2 i hi
  have u4 : St n4.mem base n4 0xC (reg n4) := ⟨by rw [pc4], rfl, fun _ => rfl⟩
  have sp4 : reg n4 sp = F := by
    rw [k4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp3]
  obtain ⟨n5, d5, u5⟩ := u4.aluImm hc4 sne_at_c (off' := 0x10) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5.lw hc4 sne_at_10 (off' := 0x12) (by decide) (by
    rw [upd_ne (by decide) (by decide), sp4, eW, ← eW]; exact aligned_add hFa (k := 0xC) (by decide))
  have eRa : memLoad32 n4.mem (G + BitVec.ofNat 32 0x10) = retAddr := by
    rw [memLoad32_congr (M := Ms) (fun j hj => f4 _ (hsep0.subR (c := j) (l := 1) (by omega))), ← hMs]
    exact memLoad32_store32_same _ _ _
  rw [upd_ne (by decide) (by decide), sp4, eW, eRa] at u6
  obtain ⟨n7, d7, u7⟩ := u6.aluImm hc4 sne_at_12 (off' := 0x14) (by decide)
  obtain ⟨n8, d8, pc8, mem8, regs8⟩ := u7.jalr hc4 sne_at_14
  have k4' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ t1 → q ≠ ra → q ≠ sp → reg n4 q = reg m q :=
    fun q h0 h1 h2 h3 h4 ht hr hs => by rw [k4 q h0 h1 h2 h3 h4 ht, r3 q hr, k2 q hs]
  refine ⟨n8, .cons d1 (.cons d2 (c3.trans (c4.trans (.cons d5 (.cons d6 (.cons d7 (.single d8))))))), ?_, ?_,
    fun r h0 h1 h2 h3 h4 ht => ?_, fun x hx => ?_⟩
  · rw [pc8]; simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero, hret]
  · rw [regs8]; simp +decide only [upd_app, ↓reduceIte]
    rw [a04]
    by_cases he : memBytes m.mem p pl = memBytes m.mem q ql
    · rw [ite_eq_left he, ite_eq_left he]; rfl
    · rw [ite_eq_right he, ite_eq_right he]; rfl
  · rw [regs8]
    by_cases hr : r = ra
    · subst hr; simp +decide only [upd_app, ↓reduceIte]; rw [hra]
    by_cases hs : r = sp
    · subst hs; simp +decide only [upd_app, ↓reduceIte]
      rw [sp4, ← hF, ev_add, BitVec.add_assoc]; exact (BitVec.add_zero _).trans hS.symm
    by_cases hz0 : r.val = 0
    · have : r = 0 := Fin.ext hz0
      subst this; simp [upd]; exact hz.symm
    simp only [upd_app, hz0, hr, hs, h0, ite_false]
    exact k4' r h0 h1 h2 h3 h4 ht hr hs
  · rw [mem8, f4 x (sub4 hx), frS x hx]

/-- **The compiled `<[u8; 32] as PartialEq>::eq` in `c3_crypto`** returns 1 when the 32
bytes at `p` equal the 32 bytes at `q` and 0 otherwise. It saves `ra` in the
word below `sp`. -/
theorem arr32EqCrypto_correct (m : Machine) {base retAddr p q : Word} (hP : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base arr32EqCryptoCode) (hm : CodeIn m.mem (base + 0x11896) memcmpCode) (hpc : m.pc = base)
    (ha0 : reg m a0 = p) (ha1 : reg m a1 = q)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : (reg m sp).toNat % 4 = 0)
    (sSC : Sep (reg m sp + 0xFFFFFFFC) 4 base arr32EqCryptoCode.length)
    (sSM : Sep (reg m sp + 0xFFFFFFFC) 4 (base + 0x11896) memcmpCode.length)
    (sSP : Sep (reg m sp + 0xFFFFFFFC) 4 p 32) (sSQ : Sep (reg m sp + 0xFFFFFFFC) 4 q 32) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (if memBytes m.mem p 32 = memBytes m.mem q 32 then 1 else 0) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFFC) 4 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨G, hG⟩ : ∃ G, reg m sp + 0xFFFFFFF0 = G := ⟨_, rfl⟩
  have eG : G + 0xC = reg m sp + 0xFFFFFFFC := by rw [← hG, BitVec.add_assoc]; rfl
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc aec_at_0 (off' := 2) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.sw hc aec_at_2 (off' := 4) (by decide) (by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hG, eG]; exact aligned_add hsp (k := 0xFFFFFFFC) (by decide))
  simp +decide only [upd_app, ↓reduceIte] at u2
  rw [ev_add, hG, eG, hra] at u2
  have hc2 := CodeIn.store32 (v := retAddr) hc sSC
  have frS : ∀ x, Sep (reg m sp + 0xFFFFFFFC) 4 x 1 → memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr x = m.mem x :=
    fun x hx => memStore32_get_sep hx
  have hm2 : CodeIn (memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr) (base + 0x11896) memcmpCode := fun i hi => by
    rw [frS _ (sSM.subR (c := i) (l := 1) (by omega))]; exact hm i hi
  obtain ⟨n2', d2', u2'⟩ := u2.self.aluImm hc2 aec_at_4 (off' := 8) (by decide)
  obtain ⟨n3, c3, pc3, mem3, regs3⟩ := u2'.self.callRa hc2 aec_at_8 aec_at_c
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hP 0x11896 (by decide))
  have r3 := PEnv.reg1 regs3 u2'.self.zero
  have k2 : ∀ q, q ≠ sp → q ≠ a2 → reg n2' q = reg m q := fun q h h2 => by
    rw [u2'.regs, upd_ne' h2 u2.self.zero, u2.regs, updz hz h]
  obtain ⟨n4, c4, pc4, a04, k4, mem4⟩ := memcmp_correct n3 (n := 32) (by rw [mem3]; exact hm2) pc3
    (by rw [r3 a0 (by decide), k2 a0 (by decide) (by decide), ha0])
    (by rw [r3 a1 (by decide), k2 a1 (by decide) (by decide), ha1])
    (by rw [r3 a2 (by decide), u2'.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u2.self.zero]; rfl)
    (by decide) (by rw [regs3]; simp +decide [upd])
    (even_clear _ (even_at base hP (8 + 8) (by decide)))
  rw [mem3] at a04 mem4
  have hall : (∀ i, i < 32 → (memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr) (p + BitVec.ofNat 32 i) =
      (memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr) (q + BitVec.ofNat 32 i)) ↔
      memBytes m.mem p 32 = memBytes m.mem q 32 := by
    rw [memBytes_eq_iff]
    constructor
    · intro h i hi
      rw [← frS _ (sSP.subR (c := i) (l := 1) hi), ← frS _ (sSQ.subR (c := i) (l := 1) hi)]; exact h i hi
    · intro h i hi
      rw [frS _ (sSP.subR (c := i) (l := 1) hi), frS _ (sSQ.subR (c := i) (l := 1) hi)]; exact h i hi
  obtain ⟨Ms, hMs⟩ : ∃ Ms, memStore32 m.mem (reg m sp + 0xFFFFFFFC) retAddr = Ms := ⟨_, rfl⟩
  rw [hMs] at mem4 hc2 hall frS a04
  have u4 : St Ms base n4 0x10 (reg n4) := ⟨by rw [pc4], mem4, fun _ => rfl⟩
  have sp4 : reg n4 sp = G := by
    rw [k4 sp (by decide) (by decide) (by decide) (by decide) (by decide), r3 sp (by decide), u2'.regs,
      upd_ne (by decide) (by decide), u2.regs]
    simp +decide only [upd_app, ↓reduceIte]
  have k4' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ sp → reg n4 q = reg m q :=
    fun q h0 h1 h2 h3 h4 hr hs => by rw [k4 q h0 h1 h2 h3 h4, r3 q hr, k2 q hs h2]
  obtain ⟨n5, d5, u5⟩ := u4.aluImm hc2 aec_at_10 (off' := 0x14) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5.lw hc2 aec_at_14 (off' := 0x16) (by decide) (by
    rw [upd_ne (by decide) (by decide), sp4, eG]; exact aligned_add hsp (k := 0xFFFFFFFC) (by decide))
  have eRa : memLoad32 Ms (reg m sp + 0xFFFFFFFC) = retAddr := by rw [← hMs]; exact memLoad32_store32_same _ _ _
  rw [upd_ne (by decide) (by decide), sp4, eG, eRa] at u6
  obtain ⟨n7, d7, u7⟩ := u6.aluImm hc2 aec_at_16 (off' := 0x18) (by decide)
  obtain ⟨n8, d8, pc8, mem8, regs8⟩ := u7.jalr hc2 aec_at_18
  have hsl1 : ∀ x : Word, aluEval .sltu x 1 = if x = 0 then 1 else 0 := fun x => by
    by_cases h : x = 0
    · rw [h]; rfl
    · rw [ite_eq_right h]
      show (if x.ult 1 then (1 : Word) else 0) = 0
      exact ite_eq_right (by
        show ¬ decide (x.toNat < (1 : Word).toNat) = true
        rw [decide_eq_true_iff]; intro hx
        exact h (BitVec.eq_of_toNat_eq (by change x.toNat < 1 at hx; change x.toNat = 0; omega)))
  refine ⟨n8, .cons d1 (.cons d2 (.cons d2' (c3.trans (c4.trans (.cons d5 (.cons d6 (.cons d7 (.single d8)))))))), ?_, ?_,
    fun r h0 h1 h2 h3 h4 => ?_, fun x hx => by rw [mem8, ← frS x hx]⟩
  · rw [pc8]; simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero, hret]
  · rw [regs8]; simp +decide only [upd_app, ↓reduceIte]
    rw [hsl1]
    by_cases he : memBytes m.mem p 32 = memBytes m.mem q 32
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

end C3.RV32
