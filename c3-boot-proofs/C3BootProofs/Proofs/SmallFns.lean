import C3BootProofs.Proofs.Parse
import C3BootProofs.Proofs.Leaves
import C3BootProofs.Proofs.SliceEq
import C3BootProofs.Proofs.DerScalar
import C3BootProofs.Proofs.Part

/-!
# Small functions of the trust-root check

- `<&[u8; 97] as PartialEq>::eq` compares two 97-byte arrays, the encoding
  of a P-384 public key, through `memcmp`.
- `next` of the `map_while(Option::as_ref)` iterator over a slice of
  `Option<FulcioIntermediate>`, 32 bytes each: it yields a pointer to the
  next element while that element is `Some`, and advances past it either
  way.
-/

namespace C3.RV32

open C3.Image

theorem eq_at_0 : fetchRel eqArr97Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem eq_at_2 : fetchRel eqArr97Code 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem eq_at_4 : fetchRel eqArr97Code 0x4 = some (.aluImm .add a2 x0 0x61, 4) := by decide
theorem eq_at_8 : fetchRel eqArr97Code 0x8 = some (.auipc ra 0x8000, 4) := by decide
theorem eq_at_c : fetchRel eqArr97Code 0xC = some (.jalr ra ra 0xFFFFFAD4, 4) := by decide
theorem eq_at_10 : fetchRel eqArr97Code 0x10 = some (.aluImm .sltu a0 a0 0x1, 4) := by decide
theorem eq_at_14 : fetchRel eqArr97Code 0x14 = some (.load .lw ra sp 0xC, 2) := by decide
theorem eq_at_16 : fetchRel eqArr97Code 0x16 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem eq_at_18 : fetchRel eqArr97Code 0x18 = some (.jalr x0 ra 0x0, 2) := by decide

theorem seqz_eq (x : Word) : aluEval .sltu x 1 = if x = 0 then 1 else 0 := by
  by_cases h : x = 0
  · subst h; decide
  · simp only [h, ↓reduceIte]
    have : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    simp only [aluEval, BitVec.ult, show (1 : Word).toNat = 1 from rfl, show ¬ x.toNat < 1 by omega, decide_false,
      Bool.false_eq_true, ↓reduceIte]

set_option maxRecDepth 20000 in
/-- **`<&[u8; 97] as PartialEq>::eq`, as compiled**: with `memcmp` where the
image puts it and 16 bytes of stack below `sp`, apart from both functions'
code, it returns 1 in `a0` when the 97 bytes at `p` and `q` are equal and 0
when not, restores `sp` and `ra`, and leaves memory outside its frame as it
was. -/
theorem eqArr97_correct (m : Machine) {base retAddr p q : Word} (hc : CodeIn m.mem base eqArr97Code)
    (hm : CodeIn m.mem (base + 0x7ADC) memcmpCode) (hbase : base.toNat % 2 = 0) (hpc : m.pc = base)
    (ha0 : reg m a0 = p) (ha1 : reg m a1 = q) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : (reg m sp).toNat % 4 = 0) (hS : Sep (reg m sp + 0xFFFFFFF0) 16 base eqArr97Code.length)
    (hSm : Sep (reg m sp + 0xFFFFFFF0) 16 (base + 0x7ADC) memcmpCode.length)
    (hP : Sep p 97 (reg m sp + 0xFFFFFFF0) 16) (hQ : Sep q 97 (reg m sp + 0xFFFFFFF0) 16) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧ reg m' ra = reg m ra ∧
      reg m' a0 = (if memBytes m.mem p 97 = memBytes m.mem q 97 then 1 else 0) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFF0) 16 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, reg m sp + 0xFFFFFFF0 = G := ⟨_, rfl⟩
  rw [hG] at hS hSm hP hQ ⊢
  have hGa : G.toNat % 4 = 0 := hG ▸ aligned_add hsp (k := 0xFFFFFFF0) (by decide)
  have hspG : G + 0x10 = reg m sp := by rw [← hG, BitVec.add_assoc]; exact BitVec.add_zero _
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, e1, t1⟩ := s0.aluImm hc eq_at_0 (off' := 2) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFF0 = G from hG] at t1
  have u1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  have S12 : Sep (G + 0xC) 4 base eqArr97Code.length := hS.sub (c := 0xC) (l := 4) (by decide)
  have S12m : Sep (G + 0xC) 4 (base + 0x7ADC) memcmpCode.length := hSm.sub (c := 0xC) (l := 4) (by decide)
  obtain ⟨m2, e2, t2⟩ := t1.sw hc eq_at_2 (off' := 4) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0xC) (by decide))
  rw [u1sp, show upd (reg m) sp G ra = reg m ra by simp +decide [upd]] at t2
  have hc2 := hc.store32 (v := reg m ra) S12
  have hm2 := hm.store32 (v := reg m ra) S12m
  obtain ⟨m3, e3, t3⟩ := t2.aluImm hc2 eq_at_4 (off' := 8) (by decide)
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := t3.callRa (cb := base + 0x7ADC) hc2 eq_at_8 eq_at_c
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hbase 0x7ADC (by decide))
  have r4 : ∀ r, reg m4 r = upd (upd (upd (reg m) sp G) a2 (aluEval .add (upd (reg m) sp G x0) 0x61)) ra
      (base + BitVec.ofNat 32 (8 + 8)) r := regs4
  obtain ⟨m5, c5, pc5, a05, k5, mem5⟩ := memcmp_correct m4 (p := p) (q := q) (n := 97)
    (by rw [mem4]; exact hm2) pc4 (by rw [r4]; simp +decide [upd, ha0]) (by rw [r4]; simp +decide [upd, ha1])
    (by rw [r4]; simp +decide [upd]) (by decide) (by rw [r4]; simp +decide [upd])
    (even_clear _ (even_at base hbase 0x10 (by decide)))
  have t5 : St (memStore32 m.mem (G + 0xC) (reg m ra)) base m5 0x10 (reg m5) :=
    ⟨by rw [pc5], by rw [mem5, mem4], fun _ => rfl⟩
  obtain ⟨m6, e6, t6⟩ := t5.aluImm hc2 eq_at_10 (off' := 0x14) (by decide)
  have sp5 : reg m5 sp = G := by
    rw [k5 sp (by decide) (by decide) (by decide) (by decide) (by decide), r4]; simp +decide [upd]
  obtain ⟨m7, e7, t7⟩ := t6.lw hc2 eq_at_14 (off' := 0x16) (by decide)
    (by simp +decide only [upd]; rw [sp5]; exact aligned_add hGa (k := 0xC) (by decide))
  have sp6 : upd (reg m5) a0 (aluEval .sltu (reg m5 a0) 1) sp = G := by simp +decide [upd, sp5]
  rw [sp6, memLoad32_store32_same] at t7
  obtain ⟨m8, e8, t8⟩ := t7.aluImm hc2 eq_at_16 (off' := 0x18) (by decide)
  obtain ⟨m9, e9, pc9, mem9, regs9⟩ := t8.jalr hc2 eq_at_18
  have keep5 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ ra → r ≠ sp → reg m5 r = reg m r :=
    fun r h0 h1 h2 h3 h4 h5 h6 => by
      rw [k5 r h0 h1 h2 h3 h4, r4]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h2, h5, h6]
  refine ⟨m9, .cons e1 (.cons e2 (.cons e3 (c4.trans (c5.trans (.cons e6 (.cons e7 (.cons e8 (.single e9)))))))),
    ?_, ?_, ?_, ?_, fun r h0 h1 h2 h3 h4 => ?_, fun x hx => ?_⟩
  · rw [pc9, add_lit_zero]; simp +decide only [upd, ite_true, ite_false]; rw [hra, hret]
  · rw [regs9]; simp +decide only [upd, ite_true, ite_false]; rw [sp5, ← hspG]; rfl
  · rw [regs9]; simp +decide only [upd, ite_true, ite_false]
  · rw [regs9]; simp +decide only [upd, ite_true, ite_false]
    have e4 : ∀ (b : Word), Sep b 97 G 16 → ∀ i, i < 97 → m4.mem (b + BitVec.ofNat 32 i) = m.mem (b + BitVec.ofNat 32 i) :=
      fun b hb i hi => by
        rw [mem4]; exact memStore32_get_sep ((hb.symm.sub (c := 0xC) (l := 4) (by decide)).subR (c := i) (l := 1) (by omega))
    rw [seqz_eq]
    by_cases e : memBytes m.mem p 97 = memBytes m.mem q 97
    · have h0 : reg m5 a0 = 0 := a05.mpr fun i hi => by
        rw [e4 p hP i hi, e4 q hQ i hi]; exact memBytes_eq_iff.mp e i hi
      simp only [h0, e, ↓reduceIte]
    · have h0 : reg m5 a0 ≠ 0 := fun h0 => e (memBytes_eq_iff.mpr fun i hi => by
        have := a05.mp h0 i hi; rwa [e4 p hP i hi, e4 q hQ i hi] at this)
      simp only [h0, e, ↓reduceIte]
  · rw [regs9]
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [upd, hz]
    by_cases hra' : r = ra
    · subst hra'; simp +decide [upd]
    by_cases hsp' : r = sp
    · subst hsp'; simp +decide [upd]; rw [sp5, ← hspG]; rfl
    simp [upd, hr, hra', hsp', h0]
    exact keep5 r h0 h1 h2 h3 h4 hra' hsp'
  · rw [mem9]; exact memStore32_get_sep (hx.sub (c := 0xC) (l := 4) (by decide))

theorem fn_at_0 : fetchRel fulcioIterNextCode 0x0 = some (.load .lw a1 a0 0x0, 2) := by decide
theorem fn_at_2 : fetchRel fulcioIterNextCode 0x2 = some (.load .lw a2 a0 0x4, 2) := by decide
theorem fn_at_4 : fetchRel fulcioIterNextCode 0x4 = some (.branch .beq a1 a2 0x18, 4) := by decide
theorem fn_at_8 : fetchRel fulcioIterNextCode 0x8 = some (.load .lw a2 a1 0x0, 2) := by decide
theorem fn_at_a : fetchRel fulcioIterNextCode 0xA = some (.aluImm .sltu a2 a2 0x1, 4) := by decide
theorem fn_at_e : fetchRel fulcioIterNextCode 0xE = some (.aluImm .add a3 a1 0x20, 4) := by decide
theorem fn_at_12 : fetchRel fulcioIterNextCode 0x12 = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) := by decide
theorem fn_at_14 : fetchRel fulcioIterNextCode 0x14 = some (.store .sw a0 a3 0x0, 2) := by decide
theorem fn_at_16 : fetchRel fulcioIterNextCode 0x16 = some (.alu .and a0 a2 a1, 4) := by decide
theorem fn_at_1a : fetchRel fulcioIterNextCode 0x1A = some (.jalr x0 ra 0x0, 2) := by decide
theorem fn_at_1c : fetchRel fulcioIterNextCode 0x1C = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem fn_at_1e : fetchRel fulcioIterNextCode 0x1E = some (.jalr x0 ra 0x0, 2) := by decide

theorem bt_beq_self (a : Word) : branchTaken .beq a a = true := by
  show (a == a) = true; exact decide_eq_true rfl

theorem ones_and_left (p : Word) : (0xFFFFFFFF : Word) &&& p = p := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp only [BitVec.getLsbD_and]
  rw [show (0xFFFFFFFF : Word).getLsbD i = true from by revert i; decide]; rfl

/-- `next`'s mask: all ones unless the element's tag is zero, then the
pointer kept or cleared by it. -/
theorem fn_mask (t p : Word) :
    aluEval .and (aluEval .add (aluEval .sltu t 1) 0xFFFFFFFF) p = if t = 0 then 0 else p := by
  rw [seqz_eq]
  by_cases h : t = 0
  · simp only [h, ↓reduceIte]; exact BitVec.zero_and
  · simp only [h, ↓reduceIte]; exact ones_and_left p

/-- **`next` of the `map_while(Option::as_ref)` iterator, as compiled**: for
the iterator at `it`, a pointer to the next element and the end of the
slice, it returns 0 when the slice is exhausted and leaves memory alone.
Otherwise it returns 0 for a `None` element and a pointer to the element for
a `Some`, and advances the iterator by the element's 32 bytes. -/
theorem fulcioIterNext_correct (m : Machine) {base retAddr it : Word} (hc : CodeIn m.mem base fulcioIterNextCode)
    (hpc : m.pc = base) (ha0 : reg m a0 = it) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hit : it.toNat % 4 = 0) (hptr : (memLoad32 m.mem it).toNat % 4 = 0)
    (hS : Sep it 4 base fulcioIterNextCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (if memLoad32 m.mem it = memLoad32 m.mem (it + 4) then 0
        else if memLoad32 m.mem (memLoad32 m.mem it) = 0 then 0 else memLoad32 m.mem it) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → reg m' r = reg m r) ∧
      m'.mem = (if memLoad32 m.mem it = memLoad32 m.mem (it + 4) then m.mem
        else memStore32 m.mem it (memLoad32 m.mem it + 0x20)) := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, e1, t1⟩ := s0.lw hc fn_at_0 (off' := 2) (by decide) (by rw [ha0, add_lit_zero]; exact hit)
  rw [ha0, add_lit_zero] at t1
  obtain ⟨m2, e2, t2⟩ := t1.lw hc fn_at_2 (off' := 4) (by decide)
    (by simp +decide only [upd]; rw [ha0]; exact aligned_add hit (k := 4) (by decide))
  rw [show upd (reg m) a1 (memLoad32 m.mem it) a0 = it by simp +decide [upd, ha0]] at t2
  by_cases he : memLoad32 m.mem it = memLoad32 m.mem (it + 4)
  · obtain ⟨m3, e3, t3⟩ := t2.taken hc 0x1C fn_at_4 (by decide) (by simp +decide only [upd]; rw [he]; exact bt_beq_self _)
    obtain ⟨m4, e4, t4⟩ := t3.aluImm hc fn_at_1c (off' := 0x1E) (by decide)
    obtain ⟨m5, e5, pc5, mem5, regs5⟩ := t4.jalr hc fn_at_1e
    refine ⟨m5, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.single e5)))), ?_, ?_, fun r h0 h1 h2 h3 => ?_, ?_⟩
    · rw [pc5, add_lit_zero]; simp +decide only [upd, ite_true, ite_false]; rw [hra, hret]
    · rw [regs5, ite_eq_left_of_eq_true _ _ (eq_true he)]; simp +decide only [upd, ite_true]
    · rw [regs5]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h0, h1, h2]
    · rw [mem5, ite_eq_left_of_eq_true _ _ (eq_true he)]
  · obtain ⟨m3, e3, t3⟩ := t2.notTaken hc 0x8 fn_at_4 (by decide)
      (by simp +decide only [upd]; exact beq_eq_false_iff_ne.mpr he)
    obtain ⟨ptr, hptrd⟩ : ∃ ptr, memLoad32 m.mem it = ptr := ⟨_, rfl⟩
    rw [hptrd] at t3 hptr he ⊢
    have q3a1 : reg m3 a1 = ptr := by rw [t3.regs]; simp +decide [upd]
    have q3a0 : reg m3 a0 = it := by rw [t3.regs]; simp +decide [upd, ha0]
    have k3 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → reg m3 r = reg m r := fun r h0 h1 h2 h3 => by
      rw [t3.regs]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h1, h2]
    obtain ⟨m4, e4, t4⟩ := t3.self.lw hc fn_at_8 (off' := 0xA) (by decide) (by rw [q3a1, add_lit_zero]; exact hptr)
    rw [q3a1, add_lit_zero] at t4
    obtain ⟨m5, e5, t5⟩ := t4.aluImm hc fn_at_a (off' := 0xE) (by decide)
    obtain ⟨m6, e6, t6⟩ := t5.aluImm hc fn_at_e (off' := 0x12) (by decide)
    obtain ⟨m7, e7, t7⟩ := t6.aluImm hc fn_at_12 (off' := 0x14) (by decide)
    have q7a0 : reg m7 a0 = it := by rw [t7.regs]; simp +decide [upd, q3a0]
    have q7a3 : reg m7 a3 = ptr + 0x20 := by rw [t7.regs]; simp +decide [upd, q3a1]; rfl
    have q7a2 : reg m7 a2 = aluEval .add (aluEval .sltu (memLoad32 m.mem ptr) 1) 0xFFFFFFFF := by
      rw [t7.regs]; simp +decide [upd]
    have q7a1 : reg m7 a1 = ptr := by rw [t7.regs]; simp +decide [upd, q3a1]
    have k7 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → reg m7 r = reg m r := fun r h0 h1 h2 h3 => by
      rw [t7.regs]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h2, h3]; exact k3 r h0 h1 h2 h3
    obtain ⟨m8, e8, t8⟩ := t7.self.sw hc fn_at_14 (off' := 0x16) (by decide) (by rw [q7a0, add_lit_zero]; exact hit)
    rw [q7a0, q7a3, add_lit_zero] at t8
    have hc8 := hc.store32 (v := ptr + 0x20) hS
    obtain ⟨m9, e9, t9⟩ := t8.alu hc8 fn_at_16 (off' := 0x1A) (by decide)
    obtain ⟨m10, e10, pc10, mem10, regs10⟩ := t9.jalr hc8 fn_at_1a
    refine ⟨m10, .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (.cons e6 (.cons e7 (.cons e8 (.cons e9
      (.single e10))))))))), ?_, ?_, fun r h0 h1 h2 h3 => ?_, ?_⟩
    · rw [pc10, add_lit_zero]; simp +decide only [upd, ite_false]
      rw [k7 ra (by decide) (by decide) (by decide) (by decide), hra, hret]
    · rw [regs10, ite_eq_right_of_eq_false _ _ (eq_false he)]; simp +decide only [upd, ite_false]
      rw [q7a2, q7a1, fn_mask]; rfl
    · rw [regs10]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h0]; exact k7 r h0 h1 h2 h3
    · rw [mem10, ite_eq_right_of_eq_false _ _ (eq_false he)]

/-- What `next` returns for the iterator at `it`. -/
def fnRes (M : Word → BitVec 8) (it : Word) : Word :=
  if memLoad32 M it = memLoad32 M (it + 4) then 0
  else if memLoad32 M (memLoad32 M it) = 0 then 0 else memLoad32 M it

/-- Memory after `next` for the iterator at `it`. -/
def fnMem (M : Word → BitVec 8) (it : Word) : Word → BitVec 8 :=
  if memLoad32 M it = memLoad32 M (it + 4) then M else memStore32 M it (memLoad32 M it + 0x20)

theorem fe_at_0 : fetchRel fulcioEnumNextCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem fe_at_2 : fetchRel fulcioEnumNextCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem fe_at_4 : fetchRel fulcioEnumNextCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x8, 2) := by decide
theorem fe_at_6 : fetchRel fulcioEnumNextCode 0x6 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem fe_at_8 : fetchRel fulcioEnumNextCode 0x8 = some (.auipc ra 0x0, 4) := by decide
theorem fe_at_c : fetchRel fulcioEnumNextCode 0xC = some (.jalr ra ra 0x1C0, 4) := by decide
theorem fe_at_10 : fetchRel fulcioEnumNextCode 0x10 = some (.alu .add a1 x0 a0, 2) := by decide
theorem fe_at_12 : fetchRel fulcioEnumNextCode 0x12 = some (.branch .beq a0 x0 0xC, 2) := by decide
theorem fe_at_14 : fetchRel fulcioEnumNextCode 0x14 = some (.load .lw a0 (8 : Fin 32) 0x8, 2) := by decide
theorem fe_at_16 : fetchRel fulcioEnumNextCode 0x16 = some (.aluImm .add a2 a0 0x1, 4) := by decide
theorem fe_at_1a : fetchRel fulcioEnumNextCode 0x1A = some (.store .sw (8 : Fin 32) a2 0x8, 2) := by decide
theorem fe_at_1c : fetchRel fulcioEnumNextCode 0x1C = some (.jal x0 0x2, 2) := by decide
theorem fe_at_1e : fetchRel fulcioEnumNextCode 0x1E = some (.load .lw ra sp 0xC, 2) := by decide
theorem fe_at_20 : fetchRel fulcioEnumNextCode 0x20 = some (.load .lw (8 : Fin 32) sp 0x8, 2) := by decide
theorem fe_at_22 : fetchRel fulcioEnumNextCode 0x22 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem fe_at_24 : fetchRel fulcioEnumNextCode 0x24 = some (.jalr x0 ra 0x0, 2) := by decide

theorem fnRes_congr {M M' : Word → BitVec 8} {it : Word}
    (h0 : memLoad32 M' it = memLoad32 M it) (h4 : memLoad32 M' (it + 4) = memLoad32 M (it + 4))
    (hp : memLoad32 M' (memLoad32 M it) = memLoad32 M (memLoad32 M it)) : fnRes M' it = fnRes M it := by
  unfold fnRes; rw [h0, h4, hp]

set_option maxRecDepth 20000 in
/-- **`next` of `Enumerate` over that iterator, as compiled**: for the
`Enumerate` at `it`, the iterator in its first 8 bytes and the count at
`it + 8`, with `next` where the image puts it, it returns the iterator's next
item in `a1` and in `a0` the count before it, and counts the item. When the
iterator yields nothing it returns 0 in both and leaves the count alone. -/
theorem fulcioEnumNext_correct (m : Machine) {base retAddr it : Word} (hc : CodeIn m.mem base fulcioEnumNextCode)
    (hn : CodeIn m.mem (base + 0x1C8) fulcioIterNextCode) (hbase : base.toNat % 2 = 0) (hpc : m.pc = base)
    (ha0 : reg m a0 = it) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : (reg m sp).toNat % 4 = 0) (hit : it.toNat % 4 = 0) (hptr : (memLoad32 m.mem it).toNat % 4 = 0)
    (hS : Sep (reg m sp + 0xFFFFFFF0) 16 base fulcioEnumNextCode.length)
    (hSn : Sep (reg m sp + 0xFFFFFFF0) 16 (base + 0x1C8) fulcioIterNextCode.length)
    (hI : Sep it 12 (reg m sp + 0xFFFFFFF0) 16) (hIc : Sep it 12 base fulcioEnumNextCode.length)
    (hIn : Sep it 12 (base + 0x1C8) fulcioIterNextCode.length)
    (hP : Sep (memLoad32 m.mem it) 4 (reg m sp + 0xFFFFFFF0) 16) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧ reg m' a1 = fnRes m.mem it ∧
      reg m' a0 = (if fnRes m.mem it = 0 then 0 else memLoad32 m.mem (it + 8)) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFF0) 16 x 1 → m'.mem x = (if fnRes m.mem it = 0 then fnMem m.mem it
        else memStore32 (fnMem m.mem it) (it + 8) (memLoad32 m.mem (it + 8) + 1)) x := by
  obtain ⟨G, hG⟩ : ∃ G, reg m sp + 0xFFFFFFF0 = G := ⟨_, rfl⟩
  rw [hG] at hS hSn hI hP ⊢
  have hGa : G.toNat % 4 = 0 := hG ▸ aligned_add hsp (k := 0xFFFFFFF0) (by decide)
  have hspG : G + 0x10 = reg m sp := by rw [← hG, BitVec.add_assoc]; exact BitVec.add_zero _
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  -- the frame
  obtain ⟨m1, e1, t1⟩ := s0.aluImm hc fe_at_0 (off' := 2) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFF0 = G from hG] at t1
  have u1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  obtain ⟨m2, e2, t2⟩ := t1.sw hc fe_at_2 (off' := 4) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 0xC) (by decide))
  rw [u1sp, show upd (reg m) sp G ra = reg m ra by simp +decide [upd]] at t2
  have hc2 := hc.store32 (v := reg m ra) (hS.sub (c := 0xC) (l := 4) (by decide))
  obtain ⟨m3, e3, t3⟩ := t2.sw hc2 fe_at_4 (off' := 6) (by decide)
    (by rw [u1sp]; exact aligned_add hGa (k := 8) (by decide))
  rw [u1sp, show upd (reg m) sp G 8 = reg m 8 by simp +decide [upd]] at t3
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore32 (memStore32 m.mem (G + 0xC) (reg m ra)) (G + 8) (reg m 8) = M2 := ⟨_, rfl⟩
  rw [hM2] at t3
  have M2out : ∀ x, Sep G 16 x 1 → M2 x = m.mem x := fun x hx => by
    rw [← hM2]
    exact (memStore32_get_sep (hx.sub (c := 8) (l := 4) (by decide))).trans
      (memStore32_get_sep (hx.sub (c := 0xC) (l := 4) (by decide)))
  have codeOut : ∀ {b : Word} {code : List Nat}, Sep G 16 b code.length → CodeIn m.mem b code → CodeIn M2 b code :=
    fun h hc' i hi => by rw [M2out _ (h.subR (c := i) (l := 1) (by omega))]; exact hc' i hi
  have hc3 := codeOut hS hc
  have hn3 := codeOut hSn hn
  have ldOut : ∀ (a : Word), (∀ j, j < 4 → Sep G 16 (a + BitVec.ofNat 32 j) 1) → memLoad32 M2 a = memLoad32 m.mem a :=
    fun a h => memLoad32_congr fun j hj => M2out _ (h j hj)
  have l0 : memLoad32 M2 it = memLoad32 m.mem it := ldOut it fun j hj => (hI.sub (c := j) (l := 1) (by omega)).symm
  have l4 : memLoad32 M2 (it + 4) = memLoad32 m.mem (it + 4) := ldOut _ fun j hj => by
    rw [show it + 4 = it + BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
    exact (hI.sub (c := 4 + j) (l := 1) (by omega)).symm
  have l8 : memLoad32 M2 (it + 8) = memLoad32 m.mem (it + 8) := ldOut _ fun j hj => by
    rw [show it + 8 = it + BitVec.ofNat 32 8 from rfl, add_ofNat_assoc]
    exact (hI.sub (c := 8 + j) (l := 1) (by omega)).symm
  have lp : memLoad32 M2 (memLoad32 m.mem it) = memLoad32 m.mem (memLoad32 m.mem it) :=
    ldOut _ fun j hj => (hP.sub (c := j) (l := 1) (by omega)).symm
  have eR : fnRes M2 it = fnRes m.mem it := fnRes_congr l0 l4 lp
  -- the call to `next`
  obtain ⟨m4, e4, t4⟩ := t3.alu hc3 fe_at_6 (off' := 8) (by decide)
  obtain ⟨m5, c5, pc5, mem5, regs5⟩ := t4.callRa (cb := base + 0x1C8) hc3 fe_at_8 fe_at_c
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hbase 0x1C8 (by decide))
  obtain ⟨m6, c6, pc6, a06, k6, mem6⟩ := fulcioIterNext_correct m5 (it := it) (retAddr := base + BitVec.ofNat 32 0x10)
    (by rw [mem5]; exact hn3) pc5 (by rw [regs5]; simp +decide [upd, ha0])
    (by rw [regs5]; simp +decide [upd]) (even_clear _ (even_at base hbase 0x10 (by decide))) hit
    (by rw [mem5, l0]; exact hptr) (hIn.sub (c := 0) (l := 4) (by omega) |> fun h => by rwa [add_ofNat_zero] at h)
  rw [mem5] at a06 mem6
  have r6 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ ra → r ≠ 8 → r ≠ sp → reg m6 r = reg m r :=
    fun r h0 h1 h2 h3 h4 h5 h6 => by
      rw [k6 r h0 h1 h2 h3, regs5]
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h4, h5, h6]
  have r6s0 : reg m6 8 = it := by
    rw [k6 8 (by decide) (by decide) (by decide) (by decide), regs5]; simp +decide only [upd, ite_true, ite_false]
    rw [ha0]; exact BitVec.zero_add _
  have r6sp : reg m6 sp = G := by
    rw [k6 sp (by decide) (by decide) (by decide) (by decide), regs5]; simp +decide [upd]
  have r6ra : reg m6 ra = base + BitVec.ofNat 32 0x10 := by
    rw [k6 ra (by decide) (by decide) (by decide) (by decide), regs5]; simp +decide [upd]
  -- after the call
  have fm : ∀ x, Sep it 4 x 1 → fnMem M2 it x = M2 x := fun x hx => by
    unfold fnMem
    by_cases h : memLoad32 M2 it = memLoad32 M2 (it + 4)
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte]; exact memStore32_get_sep hx
  have i4 : ∀ (b : Word) (n : Nat), Sep it 12 b n → Sep it 4 b n := fun b n h => by
    have := h.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
  have hc6 : CodeIn (fnMem M2 it) base fulcioEnumNextCode := fun i hi => by
    rw [fm _ ((i4 _ _ hIc).subR (c := i) (l := 1) (by omega))]; exact hc3 i hi
  have t6 : St (fnMem M2 it) base m6 0x10 (reg m6) := ⟨by rw [pc6], mem6, fun _ => rfl⟩
  have v6 : reg m6 a0 = fnRes m.mem it := a06.trans eR
  obtain ⟨m7, e7, t7⟩ := t6.alu hc6 fe_at_10 (off' := 0x12) (by decide)
  have r7a1 : reg m7 a1 = fnRes m.mem it := by
    rw [t7.regs]; simp +decide only [upd, ite_true, ite_false]; rw [v6]; exact BitVec.zero_add _
  have r7 : ∀ r, r ≠ a1 → reg m7 r = reg m6 r := fun r h => by rw [t7.regs]; exact updz t6.zero h
  -- loads from the frame after the call
  have so : Sep (G + 8) 4 (G + 0xC) 4 := sep_offsets G (c := 8) (n := 4) (d := 0xC) (k := 4) (by omega) (by omega) (by omega)
  have slotRa : ∀ Mx : Word → BitVec 8,
      (∀ j, j < 4 → Mx (G + 0xC + BitVec.ofNat 32 j) = M2 (G + 0xC + BitVec.ofNat 32 j)) →
      memLoad32 Mx (G + 0xC) = reg m ra := fun Mx h => by
    rw [memLoad32_congr h, ← hM2, memLoad32_store32_sep so, memLoad32_store32_same]
  have slotS0 : ∀ Mx : Word → BitVec 8,
      (∀ j, j < 4 → Mx (G + 8 + BitVec.ofNat 32 j) = M2 (G + 8 + BitVec.ofNat 32 j)) →
      memLoad32 Mx (G + 8) = reg m 8 := fun Mx h => by
    rw [memLoad32_congr h, ← hM2, memLoad32_store32_same]
  have frIt : ∀ c j, c + j < 16 → Sep it 4 (G + BitVec.ofNat 32 c + BitVec.ofNat 32 j) 1 := fun c j h => by
    rw [add_ofNat_assoc]; exact (i4 _ _ hI).subR (c := c + j) (l := 1) (by omega)
  -- the epilogue
  have epi : ∀ (Mx : Word → BitVec 8) (n : Machine), St Mx base n 0x1E (reg n) → reg n sp = G →
      CodeIn Mx base fulcioEnumNextCode → memLoad32 Mx (G + 0xC) = reg m ra → memLoad32 Mx (G + 8) = reg m 8 →
      ∃ n', Steps n n' ∧ n'.pc = retAddr ∧ n'.mem = Mx ∧ reg n' sp = reg m sp ∧ reg n' ra = reg m ra ∧
        reg n' 8 = reg m 8 ∧ ∀ r, r ≠ sp → r ≠ ra → r ≠ 8 → reg n' r = reg n r := by
    intro Mx n t hf hcx h1 h2
    obtain ⟨n1, d1, u1⟩ := t.lw hcx fe_at_1e (off' := 0x20) (by decide) (by rw [hf]; exact aligned_add hGa (k := 0xC) (by decide))
    rw [hf, h1] at u1
    obtain ⟨n2, d2, u2⟩ := u1.self.lw hcx fe_at_20 (off' := 0x22) (by decide)
      (by rw [u1.regs, updz t.zero (by decide), hf]; exact aligned_add hGa (k := 8) (by decide))
    rw [u1.regs, updz t.zero (by decide), hf, h2] at u2
    obtain ⟨n3, d3, u3⟩ := u2.self.aluImm hcx fe_at_22 (off' := 0x24) (by decide)
    obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.self.jalr hcx fe_at_24
    have q2ra : reg n2 ra = reg m ra := by rw [u2.regs, updz u1.self.zero (by decide), u1.regs]; simp +decide [upd]
    have q2sp : reg n2 sp = G := by rw [u2.regs, updz u1.self.zero (by decide), u1.regs, updz t.zero (by decide), hf]
    refine ⟨n4, .cons d1 (.cons d2 (.cons d3 (.single d4))), ?_, mem4, ?_, ?_, ?_, fun r h1 h2 h3 => ?_⟩
    · rw [pc4, add_lit_zero, u3.regs, updz u2.self.zero (by decide), q2ra, hra, hret]
    · rw [regs4, u3.regs]; simp +decide only [upd, ite_true]
      rw [q2sp]; exact hspG
    · rw [regs4, u3.regs, updz u2.self.zero (by decide), q2ra]
    · rw [regs4, u3.regs, updz u2.self.zero (by decide), u2.regs]; simp +decide [upd]
    · rw [regs4, u3.regs, updz u2.self.zero h1, u2.regs, updz u1.self.zero h3, u1.regs, updz t.zero h2]
  have fmOut : ∀ x, Sep G 16 x 1 → fnMem M2 it x = fnMem m.mem it x := fun x hx => by
    unfold fnMem
    rw [l0, l4]
    by_cases h : memLoad32 m.mem it = memLoad32 m.mem (it + 4)
    · simp only [h, ↓reduceIte]; exact M2out x hx
    · simp only [h, ↓reduceIte]; exact memStore32_congr (M2out x hx)
  have keep : ∀ (n : Machine), (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ sp → r ≠ ra → r ≠ 8 → reg n r = reg m7 r) →
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ sp → r ≠ ra → r ≠ 8 → reg n r = reg m r :=
    fun n h r h0 h1 h2 h3 h4 h5 h6 => by rw [h r h0 h1 h2 h4 h5 h6, r7 r h1, r6 r h0 h1 h2 h3 h5 h6 h4]
  have i8 : ∀ (b : Word) (n : Nat), Sep it 12 b n → Sep (it + 8) 4 b n := fun b n h => h.sub (c := 8) (l := 4) (by omega)
  by_cases hr0 : fnRes m.mem it = 0
  · -- the iterator yields nothing
    obtain ⟨n8, d8, u8⟩ := t7.self.taken hc6 0x1E fe_at_12 (by decide)
      (by rw [r7 a0 (by decide), v6, hr0, t7.self.zero]; exact bt_beq_self _)
    obtain ⟨n9, c9, pc9, mem9, sp9, ra9, s09, k9⟩ := epi (fnMem M2 it) n8 ⟨u8.pc, u8.mem, fun _ => rfl⟩
      (by rw [u8.regs, r7 sp (by decide), r6sp]) hc6 (slotRa _ fun j hj => fm _ (frIt 0xC j (by omega)))
      (slotS0 _ fun j hj => fm _ (frIt 8 j (by omega)))
    refine ⟨n9, .cons e1 (.cons e2 (.cons e3 (.cons e4 (c5.trans (c6.trans (.cons e7 (.cons d8 c9))))))), pc9, sp9,
      ?_, ?_, fun r h0 h1 h2 h3 => ?_, fun x hx => ?_⟩
    · rw [k9 a1 (by decide) (by decide) (by decide), u8.regs, r7a1]
    · rw [k9 a0 (by decide) (by decide) (by decide), u8.regs, r7 a0 (by decide), v6, hr0]; rfl
    · by_cases e1' : r = sp
      · subst e1'; exact sp9
      by_cases e2' : r = ra
      · subst e2'; exact ra9
      by_cases e3' : r = 8
      · subst e3'; exact s09
      rw [k9 r e1' e2' e3']
      exact keep n8 (fun r _ _ _ _ _ _ => u8.regs r) r h0 h1 h2 h3 e1' e2' e3'
    · rw [mem9, fmOut x hx, hr0]; rfl
  · -- the iterator yields an item
    obtain ⟨n8, d8, u8⟩ := t7.self.notTaken hc6 0x14 fe_at_12 (by decide)
      (by rw [r7 a0 (by decide), v6, t7.self.zero]; exact beq_eq_false_iff_ne.mpr hr0)
    have q8s0 : reg m7 8 = it := by rw [r7 8 (by decide), r6s0]
    obtain ⟨n9, d9, u9⟩ := u8.lw hc6 fe_at_14 (off' := 0x16) (by decide)
      (by rw [q8s0]; exact aligned_add hit (k := 8) (by decide))
    have l8' : memLoad32 (fnMem M2 it) (it + 8) = memLoad32 m.mem (it + 8) := by
      rw [← l8]
      exact memLoad32_congr fun j hj => fm _ (by
        rw [show it + 8 = it + BitVec.ofNat 32 8 from rfl, add_ofNat_assoc]
        exact sep_offsets it (c := 0) (n := 4) (d := 8 + j) (k := 1) (by omega) (by omega) (by omega) |>
          fun h => by rwa [add_ofNat_zero] at h)
    rw [q8s0, l8'] at u9
    obtain ⟨n10, d10, u10⟩ := u9.aluImm hc6 fe_at_16 (off' := 0x1A) (by decide)
    obtain ⟨n11, d11, u11⟩ := u10.sw hc6 fe_at_1a (off' := 0x1C) (by decide)
      (by simp +decide only [upd]; rw [q8s0]; exact aligned_add hit (k := 8) (by decide))
    have hc11 := hc6.store32 (a := it + 8) (v := memLoad32 m.mem (it + 8) + 1) (i8 _ _ hIc)
    rw [show upd (upd (reg m7) a0 (memLoad32 m.mem (it + 8))) a2 (aluEval .add
        (upd (reg m7) a0 (memLoad32 m.mem (it + 8)) a0) 1) 8 + 8 = it + 8 by simp +decide [upd, q8s0],
      show upd (upd (reg m7) a0 (memLoad32 m.mem (it + 8))) a2 (aluEval .add
        (upd (reg m7) a0 (memLoad32 m.mem (it + 8)) a0) 1) a2 = memLoad32 m.mem (it + 8) + 1 by
          simp +decide [upd]; rfl] at u11
    obtain ⟨n12, d12, u12⟩ := u11.jump hc11 fe_at_1c (off' := 0x1E) (by decide)
      (by rw [u11.pc, BitVec.add_assoc]; exact even_bit0 (even_at base hbase 0x1E (by decide)))
    have fo8 : ∀ c j, c + j < 16 → memStore32 (fnMem M2 it) (it + 8) (memLoad32 m.mem (it + 8) + 1)
        (G + BitVec.ofNat 32 c + BitVec.ofNat 32 j) = M2 (G + BitVec.ofNat 32 c + BitVec.ofNat 32 j) :=
      fun c j h => by
        rw [memStore32_get_sep (by rw [add_ofNat_assoc]; exact (i8 _ _ hI).subR (c := c + j) (l := 1) (by omega)),
          fm _ (frIt c j h)]
    obtain ⟨n13, c13, pc13, mem13, sp13, ra13, s013, k13⟩ := epi _ n12 u12.self
      (by rw [u12.regs]; simp +decide [upd]; rw [r7 sp (by decide), r6sp]) hc11
      (slotRa _ fun j hj => fo8 0xC j (by omega)) (slotS0 _ fun j hj => fo8 8 j (by omega))
    refine ⟨n13, .cons e1 (.cons e2 (.cons e3 (.cons e4 (c5.trans (c6.trans (.cons e7 (.cons d8 (.cons d9
      (.cons d10 (.cons d11 (.cons d12 c13))))))))))), pc13, sp13, ?_, ?_, fun r h0 h1 h2 h3 => ?_, fun x hx => ?_⟩
    · rw [k13 a1 (by decide) (by decide) (by decide), u12.regs]; simp +decide [upd]; exact r7a1
    · rw [k13 a0 (by decide) (by decide) (by decide), u12.regs, ite_eq_right hr0]; simp +decide [upd]
    · by_cases e1' : r = sp
      · subst e1'; exact sp13
      by_cases e2' : r = ra
      · subst e2'; exact ra13
      by_cases e3' : r = 8
      · subst e3'; exact s013
      rw [k13 r e1' e2' e3']
      refine keep n12 (fun r h0 _ h2 _ _ _ => ?_) r h0 h1 h2 h3 e1' e2' e3'
      rw [u12.regs]; simp [upd, h0, h2]
      by_cases hr : r = 0
      · subst hr; rw [ite_eq_left rfl]; exact t7.self.zero.symm
      · simp only [hr, ↓reduceIte]
    · rw [mem13, ite_eq_right hr0]; exact memStore32_congr (fmOut x hx)

/-- Where `nth`'s skipping loop stops for `k` items from the element at `p`
of a slice ending at `endp`, and whether it skipped them all: it stops at the
end of the slice, or just past a `None` element. -/
def fnStop (M : Word → BitVec 8) (endp : Word) : Nat → Word → Word × Bool
  | 0, p => (p, true)
  | k + 1, p => if p = endp then (p, false) else if memLoad32 M p = 0 then (p + 0x20, false)
      else fnStop M endp k (p + 0x20)

theorem fh_at_0 : fetchRel fulcioIterNthCode 0x0 = some (.branch .beq a1 x0 0x24, 2) := by decide
theorem fh_at_2 : fetchRel fulcioIterNthCode 0x2 = some (.load .lw a3 a0 0x0, 2) := by decide
theorem fh_at_4 : fetchRel fulcioIterNthCode 0x4 = some (.load .lw a2 a0 0x4, 2) := by decide
theorem fh_at_6 : fetchRel fulcioIterNthCode 0x6 = some (.branch .beq a3 a2 0x18, 4) := by decide
theorem fh_at_a : fetchRel fulcioIterNthCode 0xA = some (.load .lw a4 a3 0x0, 2) := by decide
theorem fh_at_c : fetchRel fulcioIterNthCode 0xC = some (.aluImm .add a3 a3 0x20, 4) := by decide
theorem fh_at_10 : fetchRel fulcioIterNthCode 0x10 = some (.store .sw a0 a3 0x0, 2) := by decide
theorem fh_at_12 : fetchRel fulcioIterNthCode 0x12 = some (.aluImm .add a5 a1 0xFFFFFFFF, 4) := by decide
theorem fh_at_16 : fetchRel fulcioIterNthCode 0x16 = some (.branch .beq a4 x0 0x4, 2) := by decide
theorem fh_at_18 : fetchRel fulcioIterNthCode 0x18 = some (.alu .add a1 x0 a5, 2) := by decide
theorem fh_at_1a : fetchRel fulcioIterNthCode 0x1A = some (.branch .beq a5 x0 0x4, 2) := by decide
theorem fh_at_1c : fetchRel fulcioIterNthCode 0x1C = some (.branch .bne a4 x0 0xFFFFFFEA, 2) := by decide
theorem fh_at_1e : fetchRel fulcioIterNthCode 0x1E = some (.branch .beq a1 x0 0x6, 2) := by decide
theorem fh_at_20 : fetchRel fulcioIterNthCode 0x20 = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem fh_at_22 : fetchRel fulcioIterNthCode 0x22 = some (.jalr x0 ra 0x0, 2) := by decide
theorem fh_at_24 : fetchRel fulcioIterNthCode 0x24 = some (.auipc (6 : Fin 32) 0x0, 4) := by decide
theorem fh_at_28 : fetchRel fulcioIterNthCode 0x28 = some (.jalr x0 (6 : Fin 32) 0x17E, 4) := by decide

set_option maxRecDepth 20000 in
/-- **`nth` of the `map_while(Option::as_ref)` iterator, as compiled**: for
the iterator at `it` over `L` elements and `n` in `a1`, it skips `n` items
the way `fnStop` says, storing the advanced pointer, and then returns
`next`'s result when it skipped them all and 0 when it stopped early. -/
theorem fulcioIterNth_correct (m : Machine) {base retAddr it : Word} {n L : Nat}
    (hc : CodeIn m.mem base fulcioIterNthCode) (hn : CodeIn m.mem (base + 0x1A2) fulcioIterNextCode)
    (hbase : base.toNat % 2 = 0) (hpc : m.pc = base) (ha0 : reg m a0 = it) (ha1 : reg m a1 = BitVec.ofNat 32 n)
    (hn32 : n < 2 ^ 32) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hit : it.toNat % 4 = 0)
    (hp0 : (memLoad32 m.mem it).toNat % 4 = 0)
    (hend : memLoad32 m.mem (it + 4) = memLoad32 m.mem it + BitVec.ofNat 32 (32 * L)) (hL : 32 * L < 2 ^ 32)
    (hS : Sep it 4 base fulcioIterNthCode.length) (hSn : Sep it 4 (base + 0x1A2) fulcioIterNextCode.length)
    (hE : Sep it 4 (memLoad32 m.mem it) (32 * L)) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (if (fnStop m.mem (memLoad32 m.mem (it + 4)) n (memLoad32 m.mem it)).2 then
        fnRes (memStore32 m.mem it (fnStop m.mem (memLoad32 m.mem (it + 4)) n (memLoad32 m.mem it)).1) it else 0) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ (6 : Fin 32) → reg m' r = reg m r) ∧
      m'.mem = (if (fnStop m.mem (memLoad32 m.mem (it + 4)) n (memLoad32 m.mem it)).2 then
        fnMem (memStore32 m.mem it (fnStop m.mem (memLoad32 m.mem (it + 4)) n (memLoad32 m.mem it)).1) it
        else memStore32 m.mem it (fnStop m.mem (memLoad32 m.mem (it + 4)) n (memLoad32 m.mem it)).1) := by
  obtain ⟨p0, hp0d⟩ : ∃ p0, memLoad32 m.mem it = p0 := ⟨_, rfl⟩
  obtain ⟨e, hed⟩ : ∃ e, memLoad32 m.mem (it + 4) = e := ⟨_, rfl⟩
  rw [hp0d] at hp0 hend hE ⊢
  rw [hed] at hend ⊢
  have hz : reg m 0 = 0 := (show St m.mem base m 0 (reg m) from ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩).zero
  -- memory with the iterator's pointer at `p`
  have codeP : ∀ (p : Word), CodeIn (memStore32 m.mem it p) base fulcioIterNthCode ∧
      CodeIn (memStore32 m.mem it p) (base + 0x1A2) fulcioIterNextCode :=
    fun p => ⟨hc.store32 hS, hn.store32 hSn⟩
  have elt : ∀ (p : Word) (j : Nat), j < L → memLoad32 (memStore32 m.mem it p) (p0 + BitVec.ofNat 32 (32 * j)) =
      memLoad32 m.mem (p0 + BitVec.ofNat 32 (32 * j)) := fun p j hj =>
    memLoad32_store32_sep ((hE.subR (c := 32 * j) (l := 4) (by omega)))
  have endNe : ∀ j, j < L → p0 + BitVec.ofNat 32 (32 * j) ≠ e := fun j hj h => by
    rw [hend] at h
    have := add_ofNat_ne p0 (c := 32 * j) (d := 32 * L) (by omega) (by omega) (by omega)
    exact this h
  have alj : ∀ j, (p0 + BitVec.ofNat 32 (32 * j)).toNat % 4 = 0 := fun j => aligned_add hp0 (by omega)
  -- the tail call into `next` from offset 0x24
  have tailNext : ∀ (n1 : Machine) (p : Word), St (memStore32 m.mem it p) base n1 0x24 (reg n1) → reg n1 a0 = it →
      reg n1 ra = retAddr → p.toNat % 4 = 0 →
      ∃ m', Steps n1 m' ∧ m'.pc = retAddr ∧ reg m' a0 = fnRes (memStore32 m.mem it p) it ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ (6 : Fin 32) → reg m' r = reg n1 r) ∧
        m'.mem = fnMem (memStore32 m.mem it p) it := by
    intro n1 p t h0 hr hpa
    obtain ⟨n2, d2, t2⟩ := t.auipc (codeP p).1 fh_at_24 (off' := 0x28) (by decide)
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := t2.jalr (codeP p).1 fh_at_28
    have hpc3 : n3.pc = base + 0x1A2 := by
      rw [pc3]; simp +decide only [upd, ite_true, ite_false]
      rw [show base + BitVec.ofNat 32 0x24 + 0x0 + 0x17E = base + 0x1A2 by
        rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
      exact even_clear _ (even_at base hbase 0x1A2 (by decide))
    obtain ⟨n4, c4, pc4, a04, k4, mem4⟩ := fulcioIterNext_correct n3 (it := it) (retAddr := retAddr)
      (by rw [mem3]; exact (codeP p).2) hpc3 (by rw [regs3]; simp +decide [upd, h0])
      (by rw [regs3]; simp +decide [upd, hr]) hret hit
      (by rw [mem3, memLoad32_store32_same]; exact hpa) hSn
    rw [mem3] at a04 mem4
    refine ⟨n4, .cons d2 (.cons d3 c4), pc4, a04, fun r h0' h1 h2 h3 h6 => ?_, mem4⟩
    rw [k4 r h0' h1 h2 h3, regs3]
    by_cases hr0 : r.val = 0
    · have : r = 0 := Fin.ext hr0
      subst this; simp [upd]; exact t.zero.symm
    · simp [upd, hr0, h6]
  -- offset 0x1E: return 0 when `a1` is not 0, else tail-call `next`
  have fromE : ∀ (n1 : Machine) (p : Word) (k : Nat), St (memStore32 m.mem it p) base n1 0x1E (reg n1) →
      reg n1 a0 = it → reg n1 ra = retAddr → reg n1 a1 = BitVec.ofNat 32 k → k < 2 ^ 32 → p.toNat % 4 = 0 →
      ∃ m', Steps n1 m' ∧ m'.pc = retAddr ∧
        reg m' a0 = (if k = 0 then fnRes (memStore32 m.mem it p) it else 0) ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ (6 : Fin 32) → reg m' r = reg n1 r) ∧
        m'.mem = (if k = 0 then fnMem (memStore32 m.mem it p) it else memStore32 m.mem it p) := by
    intro n1 p k t h0 hr h1 hk hpa
    by_cases hk0 : k = 0
    · subst hk0
      obtain ⟨n2, d2, t2⟩ := t.taken (codeP p).1 0x24 fh_at_1e (by decide)
        (by rw [h1, t.zero]; exact bt_beq_self _)
      obtain ⟨n3, c3, pc3, a03, k3, mem3⟩ := tailNext n2 p ⟨t2.pc, t2.mem, fun _ => rfl⟩
        (by rw [t2.regs, h0]) (by rw [t2.regs, hr]) hpa
      exact ⟨n3, .cons d2 c3, pc3, by rw [a03]; rfl, fun r h0' h1' h2 h3 h6 => by rw [k3 r h0' h1' h2 h3 h6, t2.regs],
        by rw [mem3]; rfl⟩
    · obtain ⟨n2, d2, t2⟩ := t.notTaken (codeP p).1 0x20 fh_at_1e (by decide)
        (by rw [h1, t.zero]; exact beq_eq_false_iff_ne.mpr fun e => hk0 (by
          have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this))
      obtain ⟨n3, d3, t3⟩ := t2.aluImm (codeP p).1 fh_at_20 (off' := 0x22) (by decide)
      obtain ⟨n4, d4, pc4, mem4, regs4⟩ := t3.jalr (codeP p).1 fh_at_22
      refine ⟨n4, .cons d2 (.cons d3 (.single d4)), ?_, ?_, fun r h0' h1' h2 h3 h6 => ?_, ?_⟩
      · rw [pc4, add_lit_zero]; simp +decide only [upd, ite_false]; rw [hr, hret]
      · rw [regs4]; simp +decide only [upd, hk0, ↓reduceIte]; rw [t.zero]; rfl
      · rw [regs4]; exact updz t.zero h0'
      · rw [mem4]; simp only [hk0, ↓reduceIte]
  have ow : ∀ (a b : Word), memStore32 (memStore32 m.mem it a) it b = memStore32 m.mem it b := fun a b => by
    funext x; exact memStore32_overwrite _ _ _ _ _
  have keepUpd : ∀ (f : Fin 32 → Word) (rd : Fin 32) (v : Word) (r : Fin 32), f 0 = 0 → r ≠ rd →
      upd f rd v r = f r := fun f rd v r h0 h => updz h0 h
  -- the loop at offset 6, with `k` items left and the pointer at element `j`
  have loop : ∀ k j (n1 : Machine), 0 < k → k < 2 ^ 32 → j ≤ L →
      St (memStore32 m.mem it (p0 + BitVec.ofNat 32 (32 * j))) base n1 0x6 (reg n1) → reg n1 a0 = it →
      reg n1 a1 = BitVec.ofNat 32 k → reg n1 a2 = e → reg n1 a3 = p0 + BitVec.ofNat 32 (32 * j) → reg n1 ra = retAddr →
      ∃ m', Steps n1 m' ∧ m'.pc = retAddr ∧
        reg m' a0 = (if (fnStop m.mem e k (p0 + BitVec.ofNat 32 (32 * j))).2 then
          fnRes (memStore32 m.mem it (fnStop m.mem e k (p0 + BitVec.ofNat 32 (32 * j))).1) it else 0) ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ (6 : Fin 32) → reg m' r = reg n1 r) ∧
        m'.mem = (if (fnStop m.mem e k (p0 + BitVec.ofNat 32 (32 * j))).2 then
          fnMem (memStore32 m.mem it (fnStop m.mem e k (p0 + BitVec.ofNat 32 (32 * j))).1) it
          else memStore32 m.mem it (fnStop m.mem e k (p0 + BitVec.ofNat 32 (32 * j))).1) := by
    intro k
    induction k with
    | zero => intro _ _ h; exact absurd h (by decide)
    | succ k ih =>
    intro j n1 _ hk hj t h0 h1 h2 h3 hr
    obtain ⟨p, hpd⟩ : ∃ p, p0 + BitVec.ofNat 32 (32 * j) = p := ⟨_, rfl⟩
    rw [hpd] at t h3 ⊢
    have cp := (codeP p).1
    by_cases hpe : p = e
    · -- the end of the slice
      obtain ⟨n2, d2, t2⟩ := t.taken cp 0x1E fh_at_6 (by decide) (by rw [h3, h2, hpe]; exact bt_beq_self _)
      obtain ⟨n3, c3, pc3, a03, k3, mem3⟩ := fromE n2 p (k + 1) ⟨t2.pc, t2.mem, fun _ => rfl⟩
        (by rw [t2.regs, h0]) (by rw [t2.regs, hr]) (by rw [t2.regs, h1]) hk (by rw [← hpd]; exact alj j)
      have hs : fnStop m.mem e (k + 1) p = (p, false) := by simp only [fnStop, hpe, ↓reduceIte]
      refine ⟨n3, .cons d2 c3, pc3, by rw [a03, hs]; rfl, fun r h0' h1' h2' h3' _ _ h6 => by
        rw [k3 r h0' h1' h2' h3' h6, t2.regs], by rw [mem3, hs]; rfl⟩
    have hjL : j < L := by
      rcases Nat.lt_or_ge j L with h | h
      · exact h
      · exact absurd (by rw [← hpd, show j = L by omega, ← hend]) hpe
    obtain ⟨n2, d2, t2⟩ := t.notTaken cp 0xA fh_at_6 (by decide)
      (by rw [h3, h2]; exact beq_eq_false_iff_ne.mpr hpe)
    obtain ⟨n3, d3, t3⟩ := t2.lw cp fh_at_a (off' := 0xC) (by decide) (by rw [h3, add_lit_zero, ← hpd]; exact alj j)
    rw [h3, add_lit_zero] at t3
    have tag : memLoad32 (memStore32 m.mem it p) p = memLoad32 m.mem p := by
      have := elt p j hjL; rwa [hpd] at this
    rw [tag] at t3
    obtain ⟨n4, d4, t4⟩ := t3.aluImm cp fh_at_c (off' := 0x10) (by decide)
    have q4a3 : upd (upd (reg n1) a4 (memLoad32 m.mem p)) a3 (aluEval .add (upd (reg n1) a4 (memLoad32 m.mem p) a3) 0x20) a3
        = p0 + BitVec.ofNat 32 (32 * (j + 1)) := by
      simp +decide only [upd, ite_true, ite_false]; rw [h3, ← hpd]
      show p0 + BitVec.ofNat 32 (32 * j) + BitVec.ofNat 32 32 = _
      rw [add_ofNat_assoc]
      exact congrArg (fun x => p0 + BitVec.ofNat 32 x) (by omega)
    obtain ⟨n5, d5, t5⟩ := t4.sw cp fh_at_10 (off' := 0x12) (by decide)
      (by simp +decide only [upd, ite_false]; rw [h0, add_lit_zero]; exact hit)
    rw [show upd (upd (reg n1) a4 (memLoad32 m.mem p)) a3 (aluEval .add (upd (reg n1) a4 (memLoad32 m.mem p) a3) 0x20)
      a0 + 0 = it by simp +decide only [upd, ite_false]; rw [h0, add_lit_zero], q4a3, ow] at t5
    have cp' := (codeP (p0 + BitVec.ofNat 32 (32 * (j + 1)))).1
    obtain ⟨n6, d6, t6⟩ := t5.aluImm cp' fh_at_12 (off' := 0x16) (by decide)
    have z1 := t.zero
    have q6 : ∀ r, reg n6 r = upd (upd (upd (reg n1) a4 (memLoad32 m.mem p)) a3
        (aluEval .add (upd (reg n1) a4 (memLoad32 m.mem p) a3) 0x20)) a5
        (aluEval .add (upd (upd (reg n1) a4 (memLoad32 m.mem p)) a3
          (aluEval .add (upd (reg n1) a4 (memLoad32 m.mem p) a3) 0x20) a1) 0xFFFFFFFF) r := t6.regs
    have q6a4 : reg n6 a4 = memLoad32 m.mem p := by rw [q6]; simp +decide [upd]
    have q6a5 : reg n6 a5 = BitVec.ofNat 32 k := by
      rw [q6]; simp +decide only [upd, ite_true, ite_false]; rw [h1]
      apply BitVec.eq_of_toNat_eq
      show (BitVec.ofNat 32 (k + 1) + 0xFFFFFFFF).toNat = _
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl]
      omega
    have q6a3 : reg n6 a3 = p0 + BitVec.ofNat 32 (32 * (j + 1)) := by rw [q6]; simp +decide only [upd, ite_false]; exact q4a3
    have q6o : ∀ r, r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n6 r = reg n1 r := fun r h3' h4 h5 => by
      rw [q6, updz (by simp +decide [upd]) h5, updz (by simp +decide [upd]) h3', updz z1 h4]
    have hp' : (p0 + BitVec.ofNat 32 (32 * (j + 1))).toNat % 4 = 0 := alj (j + 1)
    have hstep : p + 0x20 = p0 + BitVec.ofNat 32 (32 * (j + 1)) := by
      rw [← hpd]; show p0 + BitVec.ofNat 32 (32 * j) + BitVec.ofNat 32 32 = _
      rw [add_ofNat_assoc]; exact congrArg (fun x => p0 + BitVec.ofNat 32 x) (by omega)
    have back : ∀ (n8 : Machine), (∀ r, r ≠ a1 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n8 r = reg n6 r) →
        ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ (6 : Fin 32) → reg n8 r = reg n1 r :=
      fun n8 h r _ h1' _ h3' h4 h5 _ => by rw [h r h1' h3' h4 h5, q6o r h3' h4 h5]
    by_cases ht : memLoad32 m.mem p = 0
    · -- a `None` element: stop just past it
      have hs : fnStop m.mem e (k + 1) p = (p0 + BitVec.ofNat 32 (32 * (j + 1)), false) := by
        simp only [fnStop, hpe, ht, ↓reduceIte]; rw [hstep]
      obtain ⟨n7, d7, t7⟩ := t6.self.taken cp' 0x1A fh_at_16 (by decide) (by rw [q6a4, ht, t6.self.zero]; exact bt_beq_self _)
      have toE : ∃ n8, Steps n7 n8 ∧ St (memStore32 m.mem it (p0 + BitVec.ofNat 32 (32 * (j + 1)))) base n8 0x1E (reg n8) ∧
          ∀ r, reg n8 r = reg n6 r := by
        by_cases hk0 : k = 0
        · obtain ⟨n8, d8, t8⟩ := t7.taken cp' 0x1E fh_at_1a (by decide) (by rw [q6a5, hk0, t6.self.zero]; exact bt_beq_self _)
          exact ⟨n8, .single d8, ⟨t8.pc, t8.mem, fun _ => rfl⟩, fun r => t8.regs r⟩
        · obtain ⟨n8, d8, t8⟩ := t7.notTaken cp' 0x1C fh_at_1a (by decide)
            (by rw [q6a5, t6.self.zero]; exact beq_eq_false_iff_ne.mpr fun e' => hk0 (by
              have := congrArg BitVec.toNat e'; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this))
          obtain ⟨n9, d9, t9⟩ := t8.notTaken cp' 0x1E fh_at_1c (by decide)
            (by rw [q6a4, ht, t6.self.zero]; rfl)
          exact ⟨n9, .cons d8 (.single d9), ⟨t9.pc, t9.mem, fun _ => rfl⟩, fun r => t9.regs r⟩
      obtain ⟨n8, c8, t8, r8⟩ := toE
      obtain ⟨n9, c9, pc9, a09, k9, mem9⟩ := fromE n8 _ (k + 1) t8
        (by rw [r8, q6o a0 (by decide) (by decide) (by decide), h0]) (by rw [r8, q6o ra (by decide) (by decide) (by decide), hr])
        (by rw [r8, q6o a1 (by decide) (by decide) (by decide), h1]) hk hp'
      refine ⟨n9, .cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (c8.trans c9)))))), pc9,
        by rw [a09, hs]; rfl, fun r h0' h1' h2' h3' h4 h5 h6 => ?_, by rw [mem9, hs]; rfl⟩
      rw [k9 r h0' h1' h2' h3' h6]
      exact back n8 (fun r _ _ _ _ => r8 r) r h0' h1' h2' h3' h4 h5 h6
    · -- a `Some` element: count it
      obtain ⟨n7, d7, t7⟩ := t6.self.notTaken cp' 0x18 fh_at_16 (by decide)
        (by rw [q6a4, t6.self.zero]; exact beq_eq_false_iff_ne.mpr ht)
      obtain ⟨n8, d8, t8⟩ := t7.alu cp' fh_at_18 (off' := 0x1A) (by decide)
      have q8 : ∀ r, upd (reg n6) a1 (aluEval .add (reg n6 x0) (reg n6 a5)) r = if r = a1 then BitVec.ofNat 32 k else reg n6 r :=
        fun r => by
          by_cases h : r = a1
          · subst h; simp +decide only [upd, ite_true]; rw [t6.self.zero, q6a5]; exact BitVec.zero_add _
          · rw [updz t6.self.zero h]; simp only [h, ↓reduceIte]
      by_cases hk0 : k = 0
      · subst hk0
        have hs : fnStop m.mem e (0 + 1) p = (p0 + BitVec.ofNat 32 (32 * (j + 1)), true) := by
          simp only [fnStop, hpe, ht, ↓reduceIte]; rw [hstep]
        obtain ⟨n9, d9, t9⟩ := t8.taken cp' 0x1E fh_at_1a (by decide) (by rw [q8, q8, ite_eq_right_of_eq_false _ _ (eq_false (by decide)), ite_eq_right_of_eq_false _ _ (eq_false (by decide)), q6a5, t6.self.zero]; exact bt_beq_self _)
        obtain ⟨n10, c10, pc10, a010, k10, mem10⟩ := fromE n9 _ 0 ⟨t9.pc, t9.mem, fun _ => rfl⟩
          (by rw [t9.regs, q8, ite_eq_right_of_eq_false _ _ (eq_false (by decide)), q6o a0 (by decide) (by decide) (by decide), h0])
          (by rw [t9.regs, q8, ite_eq_right_of_eq_false _ _ (eq_false (by decide)), q6o ra (by decide) (by decide) (by decide), hr])
          (by rw [t9.regs, q8, ite_eq_left_of_eq_true _ _ (eq_true rfl)]) (by decide) hp'
        refine ⟨n10, .cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 c10))))))), pc10,
          by rw [a010, hs]; rfl, fun r h0' h1' h2' h3' h4 h5 h6 => ?_, by rw [mem10, hs]; rfl⟩
        rw [k10 r h0' h1' h2' h3' h6]
        exact back n9 (fun r h1'' _ _ _ => by rw [t9.regs, q8]; simp only [h1'', ↓reduceIte]) r h0' h1' h2' h3' h4 h5 h6
      · have hs : fnStop m.mem e (k + 1) p = fnStop m.mem e k (p0 + BitVec.ofNat 32 (32 * (j + 1))) := by
          simp only [fnStop, hpe, ht, ↓reduceIte]; rw [hstep]
        obtain ⟨n9, d9, t9⟩ := t8.notTaken cp' 0x1C fh_at_1a (by decide)
          (by rw [q8, q8, ite_eq_right_of_eq_false _ _ (eq_false (by decide)), ite_eq_right_of_eq_false _ _ (eq_false (by decide)), q6a5, t6.self.zero]; exact beq_eq_false_iff_ne.mpr fun e' => hk0 (by
            have := congrArg BitVec.toNat e'; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this))
        obtain ⟨n10, d10, t10⟩ := t9.taken cp' 0x6 fh_at_1c (by decide)
          (by rw [q8, q8, ite_eq_right_of_eq_false _ _ (eq_false (by decide)), ite_eq_right_of_eq_false _ _ (eq_false (by decide)), q6a4, t6.self.zero]
              show (memLoad32 m.mem p != 0) = true
              rw [bne_iff_ne]; exact ht)
        have rr : ∀ r, reg n10 r = if r = a1 then BitVec.ofNat 32 k else reg n6 r := fun r => by rw [t10.regs, q8]
        obtain ⟨m', c', pc', a0', k', mem'⟩ := ih (j + 1) n10 (by omega) (by omega) (by omega) ⟨t10.pc, t10.mem, fun _ => rfl⟩
          (by rw [rr, ite_eq_right_of_eq_false _ _ (eq_false (by decide)), q6o a0 (by decide) (by decide) (by decide), h0])
          (by rw [rr, ite_eq_left_of_eq_true _ _ (eq_true rfl)])
          (by rw [rr, ite_eq_right_of_eq_false _ _ (eq_false (by decide)), q6o a2 (by decide) (by decide) (by decide), h2])
          (by rw [rr, ite_eq_right_of_eq_false _ _ (eq_false (by decide)), q6a3])
          (by rw [rr, ite_eq_right_of_eq_false _ _ (eq_false (by decide)), q6o ra (by decide) (by decide) (by decide), hr])
        refine ⟨m', .cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10 c')))))))), pc',
          by rw [a0', hs], fun r h0' h1' h2' h3' h4 h5 h6 => ?_, by rw [mem', hs]⟩
        rw [k' r h0' h1' h2' h3' h4 h5 h6]
        exact back n10 (fun r h1'' _ _ _ => by rw [rr]; simp only [h1'', ↓reduceIte]) r h0' h1' h2' h3' h4 h5 h6
  -- the entry
  have M0 : m.mem = memStore32 m.mem it p0 := by rw [← hp0d, memStore32_self]
  have s0 : St (memStore32 m.mem it p0) base m 0 (reg m) := ⟨by rw [hpc]; simp, M0, fun _ => rfl⟩
  have cp0 := (codeP p0).1
  by_cases hn0 : n = 0
  · subst hn0
    obtain ⟨n2, d2, t2⟩ := s0.taken cp0 0x24 fh_at_0 (by decide) (by rw [ha1, hz]; exact bt_beq_self _)
    obtain ⟨n3, c3, pc3, a03, k3, mem3⟩ := tailNext n2 p0 ⟨t2.pc, t2.mem, fun _ => rfl⟩ (by rw [t2.regs, ha0])
      (by rw [t2.regs, hra]) hp0
    refine ⟨n3, .cons d2 c3, pc3, a03, fun r h0 h1 h2 h3 _ _ h6 => by rw [k3 r h0 h1 h2 h3 h6, t2.regs], mem3⟩
  · obtain ⟨n2, d2, t2⟩ := s0.notTaken cp0 0x2 fh_at_0 (by decide)
      (by rw [ha1, hz]; exact beq_eq_false_iff_ne.mpr fun e' => hn0 (by
        have := congrArg BitVec.toNat e'; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn32] at this))
    obtain ⟨n3, d3, t3⟩ := t2.lw cp0 fh_at_2 (off' := 4) (by decide) (by rw [ha0, add_lit_zero]; exact hit)
    rw [ha0, add_lit_zero, memLoad32_store32_same] at t3
    obtain ⟨n4, d4, t4⟩ := t3.lw cp0 fh_at_4 (off' := 6) (by decide)
      (by simp +decide only [upd, ite_false]; rw [ha0]; exact aligned_add hit (k := 4) (by decide))
    have l4 : memLoad32 (memStore32 m.mem it p0) (it + 4) = e := by
      rw [memLoad32_store32_sep (sep_offsets it (c := 0) (n := 4) (d := 4) (k := 4) (by omega) (by omega) (by omega) |>
        fun h => by rwa [add_ofNat_zero] at h), hed]
    rw [show upd (reg m) a3 p0 a0 + 4 = it + 4 by simp +decide only [upd, ite_false]; rw [ha0], l4] at t4
    rw [show p0 = p0 + BitVec.ofNat 32 (32 * 0) from (add_ofNat_zero p0).symm] at t4
    obtain ⟨m', c', pc', a0', k', mem'⟩ := loop n 0 n4 (by omega) hn32 (Nat.zero_le _) t4.self
      (by rw [t4.regs]; simp +decide [upd, ha0]) (by rw [t4.regs]; simp +decide [upd, ha1])
      (by rw [t4.regs]; simp +decide [upd]) (by rw [t4.regs]; simp +decide [upd])
      (by rw [t4.regs]; simp +decide [upd, hra])
    rw [add_ofNat_zero] at a0' mem'
    refine ⟨m', .cons d2 (.cons d3 (.cons d4 c')), pc', a0', fun r h0 h1 h2 h3 h4 h5 h6 => ?_, mem'⟩
    rw [k' r h0 h1 h2 h3 h4 h5 h6, t4.regs, updz (by simp +decide [upd]) h2, updz hz h3]

end C3.RV32

































