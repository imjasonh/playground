import C3BootProofs.Proofs.ScalarIsZero

/-!
# Constant-time equality wrappers, as compiled

`<subtle::Choice as ConstantTimeEq>::ct_eq` compares the low bits of two
`Choice` bytes through two calls to the proved `black_box`.
`<ConstMontyForm<p384 scalar> as ConstantTimeEq>::ct_eq` calls the proved
`Uint<12>::ct_eq` and passes its result through `black_box`. The 8-limb
`UintRef::split_at (.165)` is the twin of the proved 12-limb one.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem cce_at_0 : fetchRel choiceCtEqCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem cce_at_2 : fetchRel choiceCtEqCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem cce_at_4 : fetchRel choiceCtEqCode 0x4 = some (.alu .xor a0 a0 a1, 2) := by decide
theorem cce_at_6 : fetchRel choiceCtEqCode 0x6 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem cce_at_a : fetchRel choiceCtEqCode 0xA = some (.auipc ra 0xA000, 4) := by decide
theorem cce_at_e : fetchRel choiceCtEqCode 0xE = some (.jalr ra ra 0xFFFFFA74, 4) := by decide
theorem cce_at_12 : fetchRel choiceCtEqCode 0x12 = some (.aluImm .xor a0 a0 0xFFFFFFFF, 4) := by decide
theorem cce_at_16 : fetchRel choiceCtEqCode 0x16 = some (.aluImm .and a0 a0 0x1, 2) := by decide
theorem cce_at_18 : fetchRel choiceCtEqCode 0x18 = some (.load .lw ra sp 0xC, 2) := by decide
theorem cce_at_1a : fetchRel choiceCtEqCode 0x1A = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem cce_at_1c : fetchRel choiceCtEqCode 0x1C = some (.auipc (6 : Fin 32) 0xA000, 4) := by decide
theorem cce_at_20 : fetchRel choiceCtEqCode 0x20 = some (.jalr x0 (6 : Fin 32) 0xFFFFFA62, 4) := by decide
theorem msc_at_0 : fetchRel montyScalarCtEq384Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem msc_at_2 : fetchRel montyScalarCtEq384Code 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem msc_at_4 : fetchRel montyScalarCtEq384Code 0x4 = some (.auipc ra 0x0, 4) := by decide
theorem msc_at_8 : fetchRel montyScalarCtEq384Code 0x8 = some (.jalr ra ra 0xFFFFFAF0, 4) := by decide
theorem msc_at_c : fetchRel montyScalarCtEq384Code 0xC = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem msc_at_10 : fetchRel montyScalarCtEq384Code 0x10 = some (.load .lw ra sp 0xC, 2) := by decide
theorem msc_at_12 : fetchRel montyScalarCtEq384Code 0x12 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem msc_at_14 : fetchRel montyScalarCtEq384Code 0x14 = some (.auipc (6 : Fin 32) 0xFFFFA000, 4) := by decide
theorem msc_at_18 : fetchRel montyScalarCtEq384Code 0x18 = some (.jalr x0 (6 : Fin 32) 0xFFFFF996, 4) := by decide
theorem sa8_at_0 : fetchRel splitAt8Code 0x0 = some (.aluImm .add a2 x0 0x8, 2) := by decide
theorem sa8_at_2 : fetchRel splitAt8Code 0x2 = some (.aluImm .add a3 a1 0x20, 4) := by decide
theorem sa8_at_6 : fetchRel splitAt8Code 0x6 = some (.store .sw a0 a1 0x0, 2) := by decide
theorem sa8_at_8 : fetchRel splitAt8Code 0x8 = some (.store .sw a0 a2 0x4, 2) := by decide
theorem sa8_at_a : fetchRel splitAt8Code 0xA = some (.store .sw a0 a3 0x8, 2) := by decide
theorem sa8_at_c : fetchRel splitAt8Code 0xC = some (.store .sw a0 x0 0xC, 4) := by decide
theorem sa8_at_10 : fetchRel splitAt8Code 0x10 = some (.jalr x0 ra 0x0, 2) := by decide
end

theorem cce_val8 : ∀ b : BitVec 8,
    ((aluEval .and (aluEval .xor ((BitVec.ofNat 32 b.toNat).extractLsb' 0 8 |>.zeroExtend 32) 0xFFFFFFFF) 1).extractLsb' 0 8).zeroExtend 32
      = if BitVec.ofNat 32 b.toNat &&& (1 : Word) = 0 then 1 else 0 := by decide

theorem and1_low (x : Word) : x &&& 1 = BitVec.ofNat 32 (x.extractLsb' 0 8).toNat &&& 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero,
    show (1 : Word).toNat = 1 from rfl, Nat.and_one_is_mod]
  omega

theorem cce_val (x : Word) :
    ((aluEval .and (aluEval .xor ((aluEval .and x 0xFF).extractLsb' 0 8 |>.zeroExtend 32) 0xFFFFFFFF) 1).extractLsb' 0 8).zeroExtend 32
      = if x &&& 1 = 0 then 1 else 0 := by
  rw [and1_low, and_ff_eq]; exact cce_val8 _

/-- **The compiled `<Choice as ConstantTimeEq>::ct_eq`** returns 1 when the
low bits of `a` and `b` agree and 0 otherwise. It writes only the 0x11 bytes
below `sp`. -/
theorem choiceCtEq_correct (m : Machine) {base retAddr a b : Word} (hP : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base choiceCtEqCode) (hb : CodeIn m.mem (base + 0x7C6E) blackBoxU8Code)
    (hpc : m.pc = base) (ha0 : reg m a0 = a) (ha1 : reg m a1 = b)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : (reg m sp).toNat % 4 = 0)
    (sGC : Sep (reg m sp + 0xFFFFFFEF) 0x11 base choiceCtEqCode.length)
    (sGB : Sep (reg m sp + 0xFFFFFFEF) 0x11 (base + 0x7C6E) blackBoxU8Code.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' a0 = (if (a ^^^ b) &&& 1 = 0 then 1 else 0) ∧
      (∀ q, q ≠ a0 → q ≠ t1 → reg m' q = reg m q) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFEF) 0x11 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨S, hS⟩ : ∃ S, reg m sp = S := ⟨_, rfl⟩
  rw [hS] at hsp sGC sGB ⊢
  obtain ⟨G, hG⟩ : ∃ G, S + 0xFFFFFFEF = G := ⟨_, rfl⟩
  rw [hG] at sGC sGB ⊢
  obtain ⟨F, hF⟩ : ∃ F, S + 0xFFFFFFF0 = F := ⟨_, rfl⟩
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add hsp (k := 0xFFFFFFF0) (by decide)
  have eW : F + 0xC = G + BitVec.ofNat 32 0xD := by rw [← hF, ← hG, BitVec.add_assoc, BitVec.add_assoc]; rfl
  have eB1 : F + 0xFFFFFFFF = G + BitVec.ofNat 32 0 := by rw [← hF, ← hG, BitVec.add_assoc, BitVec.add_assoc]; rfl
  have eS : F + 0x10 = S := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero S
  have eB2 : S + 0xFFFFFFFF = G + BitVec.ofNat 32 0x10 := by rw [← hG, BitVec.add_assoc]; rfl
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc cce_at_0 (off' := 2) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.sw hc cce_at_2 (off' := 4) (by decide) (by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hS, hF]; exact aligned_add hFa (k := 0xC) (by decide))
  simp +decide only [upd_app, ↓reduceIte] at u2
  rw [ev_add, hS, hF, eW, hra] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, memStore32 m.mem (G + BitVec.ofNat 32 0xD) retAddr = Ms := ⟨_, rfl⟩
  have frS : ∀ x, Sep G 0x11 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact memStore32_get_sep (hx.sub (c := 0xD) (l := 4) (by decide))
  have cS : ∀ {M : Word → BitVec 8} {b : Word} {code : List Nat}, (∀ x, Sep G 0x11 x 1 → M x = m.mem x) →
      CodeIn m.mem b code → Sep G 0x11 b code.length → CodeIn M b code :=
    fun hM h hs i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact h i hi
  rw [hMs] at u2
  have hc2 := cS frS hc sGC
  obtain ⟨n3, d3, u3⟩ := u2.self.alu hc2 cce_at_4 (off' := 6) (by decide)
  obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hc2 cce_at_6 (off' := 0xA) (by decide)
  obtain ⟨n5, c5, pc5, mem5, regs5⟩ := u4.self.callRa hc2 cce_at_a cce_at_e (cb := base + 0x7C6E)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hP 0x7C6E (by decide))
  have r5 := PEnv.reg1 regs5 u4.self.zero
  have sp5 : reg n5 sp = F := by
    rw [r5 sp (by decide), u4.regs, upd_ne (by decide) (by decide), u3.regs, upd_ne (by decide) (by decide), u2.regs]
    simp +decide only [upd_app, ↓reduceIte]
  have v5 : reg n5 a0 = aluEval .and (aluEval .xor a b) 0xFF := by
    have k2 : ∀ q, q ≠ sp → reg n2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
    rw [r5 a0 (by decide), u4.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [k2 a0 (by decide), k2 a1 (by decide), ha0, ha1]
  have k5 : ∀ q, q ≠ a0 → q ≠ ra → q ≠ sp → reg n5 q = reg m q := fun q h0 hr hs => by
    rw [r5 q hr, u4.regs, upd_ne' h0 u3.self.zero, u3.regs, upd_ne' h0 u2.self.zero, u2.regs, updz hz hs]
  obtain ⟨n6, c6, pc6, a06, k6, f6⟩ := blackBoxU8_correct n5 (base := base + 0x7C6E) (retAddr := base + 0x12)
    (by rw [mem5]; exact cS frS hb sGB) pc5 (by rw [regs5]; simp +decide [upd])
    (even_clear _ (even_at base hP (0xA + 8) (by decide)))
    (by rw [sp5, eB1]; exact sGB.sub (c := 0) (l := 1) (by decide))
  rw [mem5, sp5, eB1] at f6
  have hc6 : CodeIn n6.mem base choiceCtEqCode := fun i hi => by
    rw [f6 _ (sGC.sub (c := 0) (l := 1) (by decide) |>.subR (c := i) (l := 1) (by omega))]; exact hc2 i hi
  have u6 : St n6.mem base n6 0x12 (reg n6) := ⟨by rw [pc6]; rfl, rfl, fun _ => rfl⟩
  obtain ⟨n7, d7, u7⟩ := u6.aluImm hc6 cce_at_12 (off' := 0x16) (by decide)
  obtain ⟨n8, d8, u8⟩ := u7.self.aluImm hc6 cce_at_16 (off' := 0x18) (by decide)
  have sp6 : reg n6 sp = F := by rw [k6 sp (by decide), sp5]
  obtain ⟨n9, d9, u9⟩ := u8.self.lw hc6 cce_at_18 (off' := 0x1A) (by decide) (by
    rw [u8.regs, upd_ne (by decide) (by decide), u7.regs, upd_ne (by decide) (by decide), sp6]
    exact aligned_add hFa (k := 0xC) (by decide))
  have eRa : memLoad32 n6.mem (G + BitVec.ofNat 32 0xD) = retAddr := by
    rw [memLoad32_congr (M := Ms) (fun j hj => f6 _ (by
      rw [add_ofNat_assoc]; exact sep_offsets G (c := 0) (n := 1) (d := 0xD + j) (k := 1) (.inl (by omega)) (by decide)
        (by omega))), ← hMs]
    exact memLoad32_store32_same _ _ _
  have sp8 : reg n8 sp = F := by
    rw [u8.regs, upd_ne (by decide) (by decide), u7.regs, upd_ne (by decide) (by decide), sp6]
  rw [sp8, eW, eRa] at u9
  obtain ⟨n10, d10, u10⟩ := u9.aluImm hc6 cce_at_1a (off' := 0x1C) (by decide)
  obtain ⟨n11, d11, u11⟩ := u10.self.auipc hc6 cce_at_1c (off' := 0x20) (by decide)
  obtain ⟨n12, d12, pc12, mem12, regs12⟩ := u11.self.jalr hc6 cce_at_20
  have pc12' : n12.pc = base + 0x7C6E := by
    rw [pc12, u11.regs]; simp +decide only [upd, ↓reduceIte]
    rw [show base + BitVec.ofNat 32 0x1C + 0x8000 + 0xFFFFFC52 = base + 0x7C6E by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact even_clear _ (even_at base hP 0x7C6E (by decide))
  have k12 : ∀ q, q ≠ t1 → q ≠ sp → q ≠ ra → q ≠ a0 → reg n12 q = reg n6 q := fun q h6 hs hr h0 => by
    rw [regs12, u11.regs, upd_ne' h6 u10.self.zero, u10.regs, upd_ne' hs (upd_zero _ _ _), upd_ne' hr u8.self.zero,
      u8.regs, upd_ne' h0 u7.self.zero, u7.regs, upd_ne' h0 u6.zero]
  have sp12 : reg n12 sp = S := by
    rw [regs12, u11.regs, upd_ne (by decide) (by decide), u10.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [sp8, ev_add, eS]
  have ra12 : reg n12 ra = retAddr := by
    rw [regs12, u11.regs, upd_ne (by decide) (by decide), u10.regs, upd_ne (by decide) (by decide)]
    simp +decide only [upd_app, ↓reduceIte]
  have a012 : reg n12 a0 = aluEval .and (aluEval .xor ((aluEval .and (aluEval .xor a b) 0xFF).extractLsb' 0 8 |>.zeroExtend 32)
      0xFFFFFFFF) 1 := by
    rw [regs12, u11.regs, upd_ne (by decide) (by decide), u10.regs, upd_ne (by decide) (by decide),
      upd_ne (by decide) (by decide), u8.regs]
    simp +decide only [upd_app, ↓reduceIte]
    rw [u7.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [a06, v5]
  have mG : ∀ x, Sep G 0x11 x 1 → n12.mem x = m.mem x := fun x hx => by
    rw [mem12, f6 x (hx.sub (c := 0) (l := 1) (by decide)), frS x hx]
  obtain ⟨m', c', pc', a0', k', f'⟩ := blackBoxU8_correct n12 (base := base + 0x7C6E) (retAddr := retAddr)
    (cS mG hb sGB) pc12' ra12 hret (by rw [sp12, eB2]; exact sGB.sub (c := 0x10) (l := 1) (by decide))
  refine ⟨m', .cons d1 (.cons d2 (.cons d3 (.cons d4 (c5.trans (c6.trans (.cons d7 (.cons d8 (.cons d9 (.cons d10
    (.cons d11 (.cons d12 c'))))))))))), pc', ?_, fun q h0 h6 => ?_, fun x hx => ?_⟩
  · rw [a0', a012]; exact cce_val _
  · rw [k' q h0]
    by_cases hs : q = sp
    · subst hs; rw [sp12, hS]
    by_cases hr : q = ra
    · subst hr; rw [ra12, hra]
    rw [k12 q h6 hs hr h0, k6 q h0, k5 q h0 hr hs]
  · rw [f' x (by rw [sp12, eB2]; exact hx.sub (c := 0x10) (l := 1) (by decide)), mG x hx]

/-- Where `ConstMontyForm<p384 scalar>::ct_eq` runs: its code and its
callees', the 0x54 bytes of stack below `sp0`, and the two 48-byte operands. -/
structure MSEnv (M : Word → BitVec 8) (P sp0 pa pb : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P montyScalarCtEq384Code
  uce : CodeIn M (P + 0xFFFFFAF4) uint12CtEqCode
  spl : CodeIn M (P + 0xFFFFFAF4 + 0x80) splitAt12Code
  lce : CodeIn M (P + 0xFFFFFAF4 + 0xFFFF9DBC) limbCtEqCode
  uiz : CodeIn M (P + 0xFFFFFAF4 + 0xFFFEF3C4) uintRefIsZeroCode
  unz : CodeIn M (P + 0xFFFFFAF4 + 0xFFFEF3C4 + 0x1A) uintRefIsNonzeroCode
  bb : CodeIn M (P + 0xFFFF99AA) blackBoxU8Code
  hsp : sp0.toNat % 4 = 0
  hS : 0x54 ≤ sp0.toNat
  hpa : pa.toNat % 4 = 0
  hpb : pb.toNat % 4 = 0
  sGC : Sep (sp0 + 0xFFFFFFAC) 0x54 P montyScalarCtEq384Code.length
  sGU : Sep (sp0 + 0xFFFFFFAC) 0x54 (P + 0xFFFFFAF4) uint12CtEqCode.length
  sGS : Sep (sp0 + 0xFFFFFFAC) 0x54 (P + 0xFFFFFAF4 + 0x80) splitAt12Code.length
  sGL : Sep (sp0 + 0xFFFFFFAC) 0x54 (P + 0xFFFFFAF4 + 0xFFFF9DBC) limbCtEqCode.length
  sGZ : Sep (sp0 + 0xFFFFFFAC) 0x54 (P + 0xFFFFFAF4 + 0xFFFEF3C4) uintRefIsZeroCode.length
  sGN : Sep (sp0 + 0xFFFFFFAC) 0x54 (P + 0xFFFFFAF4 + 0xFFFEF3C4 + 0x1A) uintRefIsNonzeroCode.length
  sGB : Sep (sp0 + 0xFFFFFFAC) 0x54 (P + 0xFFFF99AA) blackBoxU8Code.length
  sAG : Sep pa 48 (sp0 + 0xFFFFFFAC) 0x54
  sBG : Sep pb 48 (sp0 + 0xFFFFFFAC) 0x54

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `<ConstMontyForm<p384 scalar> as ConstantTimeEq>::ct_eq`**
returns 1 when the 12 limbs at `pa` equal the 12 limbs at `pb` and 0
otherwise. -/
theorem montyScalarCtEq384_correct (m : Machine) {P sp0 pa pb retAddr : Word} (env : MSEnv m.mem P sp0 pa pb)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = pa) (ha1 : reg m a1 = pb)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      reg m' a0 = (if ∀ i : Nat, i < 12 → memLoad32 m.mem (pa + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (pb + BitVec.ofNat 32 (4 * i)) then 1 else 0) ∧
      (∀ q, oidKeep q = true → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFAC) 0x54 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFFAC = G := ⟨_, rfl⟩
  have sGC := env.sGC; have sGU := env.sGU; have sGS := env.sGS; have sGL := env.sGL; have sGZ := env.sGZ
  have sGN := env.sGN; have sGB := env.sGB; have sAG := env.sAG; have sBG := env.sBG
  rw [hG] at sGC sGU sGS sGL sGZ sGN sGB sAG sBG ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFF0 = F := ⟨_, rfl⟩
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add env.hsp (k := 0xFFFFFFF0) (by decide)
  have hFn : 0x44 ≤ F.toNat := by
    rw [← hF, BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 4294967280 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have eW : F + 0xC = G + BitVec.ofNat 32 0x50 := by rw [← hF, ← hG, BitVec.add_assoc, BitVec.add_assoc]; rfl
  have eR : F + 0xFFFFFFBC = G + BitVec.ofNat 32 0 := by rw [← hF, ← hG, BitVec.add_assoc, BitVec.add_assoc]; rfl
  have eS : F + 0x10 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eB : sp0 + 0xFFFFFFFF = G + BitVec.ofNat 32 0x53 := by rw [← hG, BitVec.add_assoc]; rfl
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.aluImm env.cod msc_at_0 (off' := 2) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.sw env.cod msc_at_2 (off' := 4) (by decide) (by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]; exact aligned_add hFa (k := 0xC) (by decide))
  simp +decide only [upd_app, ↓reduceIte] at u2
  rw [ev_add, hsp, hF, eW, hra] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, memStore32 m.mem (G + BitVec.ofNat 32 0x50) retAddr = Ms := ⟨_, rfl⟩
  have frS : ∀ x, Sep G 0x54 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact memStore32_get_sep (hx.sub (c := 0x50) (l := 4) (by decide))
  have cS : ∀ {M : Word → BitVec 8} {b : Word} {code : List Nat}, (∀ x, Sep G 0x54 x 1 → M x = m.mem x) →
      CodeIn m.mem b code → Sep G 0x54 b code.length → CodeIn M b code :=
    fun hM h hs i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact h i hi
  rw [hMs] at u2
  have hc2 := cS frS env.cod sGC
  obtain ⟨n3, c3, pc3, mem3, regs3⟩ := u2.self.callRa hc2 msc_at_4 msc_at_8 (cb := P + 0xFFFFFAF4)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFFAF4 (by decide))
  have r3 := PEnv.reg1 regs3 u2.self.zero
  have k2 : ∀ q, q ≠ sp → reg n2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp3 : reg n3 sp = F := by rw [r3 sp (by decide), u2.regs]; simp +decide only [upd_app, ↓reduceIte]
  have inR : ∀ {b : Word} {l : Nat}, Sep G 0x54 b l → Sep (F + 0xFFFFFFBC) 0x44 b l := fun h => by
    rw [eR]; exact h.sub (c := 0) (l := 0x44) (by decide)
  have inR' : ∀ {b : Word} {k : Nat}, Sep b k G 0x54 → Sep b k (F + 0xFFFFFFBC) 0x44 := fun h => by
    rw [eR]; exact h.subR (c := 0) (l := 0x44) (by decide)
  have uenv : UCEEnv n3.mem (P + 0xFFFFFAF4) F pa pb := by
    rw [mem3]
    exact ⟨even_at P env.hP 0xFFFFFAF4 (by decide), cS frS env.uce sGU, cS frS env.spl sGS, cS frS env.lce sGL,
      cS frS env.uiz sGZ, cS frS env.unz sGN, hFa, hFn, env.hpa, env.hpb, inR sGU, inR sGS, inR sGL, inR sGZ,
      inR sGN, inR' sAG, inR' sBG⟩
  obtain ⟨n4, c4, pc4, sp4, a04, k4, f4⟩ := uint12CtEq_correct n3 uenv pc3 sp3
    (by rw [r3 a0 (by decide), k2 a0 (by decide), ha0]) (by rw [r3 a1 (by decide), k2 a1 (by decide), ha1])
    (by rw [regs3]; simp +decide [upd]) (even_clear _ (even_at P env.hP (4 + 8) (by decide)))
  rw [mem3] at a04 f4
  have hall : (∀ i : Nat, i < 12 → memLoad32 Ms (pa + BitVec.ofNat 32 (4 * i)) = memLoad32 Ms (pb + BitVec.ofNat 32 (4 * i))) ↔
      (∀ i : Nat, i < 12 → memLoad32 m.mem (pa + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (pb + BitVec.ofNat 32 (4 * i))) := by
    have e : ∀ {p : Word}, Sep p 48 G 0x54 → ∀ i, i < 12 →
        memLoad32 Ms (p + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (p + BitVec.ofNat 32 (4 * i)) :=
      fun h i hi => memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact frS _ (h.sub (c := 4 * i + j) (l := 1) (by omega)).symm
    constructor
    · intro h i hi; rw [← e sAG i hi, ← e sBG i hi]; exact h i hi
    · intro h i hi; rw [e sAG i hi, e sBG i hi]; exact h i hi
  have hc4 : CodeIn n4.mem P montyScalarCtEq384Code := fun i hi => by
    rw [f4 _ ((inR sGC).subR (c := i) (l := 1) (by omega))]; exact hc2 i hi
  have u4 : St n4.mem P n4 0xC (reg n4) := ⟨by rw [pc4], rfl, fun _ => rfl⟩
  obtain ⟨n5, d5, u5⟩ := u4.aluImm hc4 msc_at_c (off' := 0x10) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5.self.lw hc4 msc_at_10 (off' := 0x12) (by decide) (by
    rw [u5.regs, upd_ne (by decide) (by decide), sp4]; exact aligned_add hFa (k := 0xC) (by decide))
  have eRa : memLoad32 n4.mem (G + BitVec.ofNat 32 0x50) = retAddr := by
    rw [memLoad32_congr (M := Ms) (fun j hj => f4 _ (by
      rw [eR, add_ofNat_assoc]; exact sep_offsets G (c := 0) (n := 0x44) (d := 0x50 + j) (k := 1) (.inl (by omega))
        (by decide) (by omega))), ← hMs]
    exact memLoad32_store32_same _ _ _
  have sp5 : reg n5 sp = F := by rw [u5.regs, upd_ne (by decide) (by decide), sp4]
  rw [sp5, eW, eRa] at u6
  obtain ⟨n7, d7, u7⟩ := u6.aluImm hc4 msc_at_12 (off' := 0x14) (by decide)
  obtain ⟨n8, d8, u8⟩ := u7.self.auipc hc4 msc_at_14 (off' := 0x18) (by decide)
  obtain ⟨n9, d9, pc9, mem9, regs9⟩ := u8.self.jalr hc4 msc_at_18
  have pc9' : n9.pc = P + 0xFFFF99AA := by
    rw [pc9, u8.regs]; simp +decide only [upd, ↓reduceIte]
    rw [show P + BitVec.ofNat 32 0x14 + 0xFFFFA000 + 0xFFFFF996 = P + 0xFFFF99AA by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact even_clear _ (even_at P env.hP 0xFFFF99AA (by decide))
  have k9 : ∀ q, q ≠ t1 → q ≠ sp → q ≠ ra → q ≠ a0 → reg n9 q = reg n4 q := fun q h6 hs hr h0 => by
    rw [regs9, u8.regs, upd_ne' h6 u7.self.zero, u7.regs, upd_ne' hs (upd_zero _ _ _), upd_ne' hr u5.self.zero,
      u5.regs, upd_ne' h0 u4.zero]
  have sp9 : reg n9 sp = sp0 := by
    rw [regs9, u8.regs, upd_ne (by decide) (by decide), u7.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [sp5, ev_add, eS]
  have ra9 : reg n9 ra = retAddr := by
    rw [regs9, u8.regs, upd_ne (by decide) (by decide), u7.regs, upd_ne (by decide) (by decide)]
    simp +decide only [upd_app, ↓reduceIte]
  have a09 : reg n9 a0 = aluEval .and (reg n4 a0) 0xFF := by
    rw [regs9, u8.regs, upd_ne (by decide) (by decide), u7.regs, upd_ne (by decide) (by decide),
      upd_ne (by decide) (by decide), u5.regs]
    simp +decide only [upd_app, ↓reduceIte]
  have mG : ∀ x, Sep G 0x54 x 1 → n9.mem x = m.mem x := fun x hx => by
    rw [mem9, f4 x (inR hx), frS x hx]
  obtain ⟨m', c', pc', a0', k', f'⟩ := blackBoxU8_correct n9 (base := P + 0xFFFF99AA) (retAddr := retAddr)
    (cS mG env.bb sGB) pc9' ra9 hret (by rw [sp9, eB]; exact sGB.sub (c := 0x53) (l := 1) (by decide))
  refine ⟨m', .cons d1 (.cons d2 (c3.trans (c4.trans (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 c')))))))),
    pc', by rw [k' sp (by decide), sp9], ?_, fun q hq => ?_, fun x hx => ?_⟩
  · rw [a0', a09, a04]
    by_cases h : ∀ i : Nat, i < 12 → memLoad32 m.mem (pa + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (pb + BitVec.ofNat 32 (4 * i))
    · rw [ite_eq_left (hall.mpr h), ite_eq_left h]; rfl
    · rw [ite_eq_right (fun h' => h (hall.mp h')), ite_eq_right h]; rfl
  · have h0 : q ≠ a0 := fun e => by subst e; revert hq; decide
    have h6 : q ≠ t1 := fun e => by subst e; revert hq; decide
    rw [k' q h0]
    by_cases hs : q = sp
    · subst hs; rw [sp9, hsp]
    by_cases hr : q = ra
    · subst hr; rw [ra9, hra]
    rw [k9 q h6 hs hr h0, k4 q hq, r3 q hr, k2 q hs]
  · rw [f' x (by rw [sp9, eB]; exact hx.sub (c := 0x53) (l := 1) (by decide)), mG x hx]

/-- What `split_at (.165)` stores at `out` for the 8 limbs at `p`. -/
def split8Mem (M : Word → BitVec 8) (out p : Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 M out p) (out + 4) 8) (out + 8) (p + 0x20)) (out + 0xC) 0

/-- `split_at (.165)`'s body, from 0x0 to the return at 0x10. -/
def sa8Body : List BInstr :=
  [.aluImm .add a2 x0 0x8, .aluImm .add a3 a1 0x20, .sw a0 a1 0x0, .sw a0 a2 0x4, .sw a0 a3 0x8, .sw a0 x0 0xC]

section
set_option maxRecDepth 20000
theorem sa8Body_end : blockEnd splitAt8Code 0x0 sa8Body = some 0x10 := by decide
end

set_option maxRecDepth 20000 in
/-- **The compiled `UintRef::split_at (.165)`**: it stores `split8Mem` at
`out`. -/
theorem splitAt8_correct (m : Machine) {base retAddr out p : Word} (hc : CodeIn m.mem base splitAt8Code)
    (hpc : m.pc = base) (ha0 : reg m a0 = out) (ha1 : reg m a1 = p) (hout : out.toNat % 4 = 0)
    (hsep : Sep out 16 base splitAt8Code.length) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = split8Mem m.mem out p ∧
      (∀ r, r ≠ a2 → r ≠ a3 → reg m' r = reg m r) := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hok : BlockOk base splitAt8Code.length sa8Body (m.mem, reg m) := by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, sa8Body, upd_app, ↓reduceIte, and_true, true_and]
    rw [ha0, add_lit_zero]
    exact ⟨⟨hout, hsep.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h⟩,
      ⟨aligned_add hout (by decide), hsep.sub (c := 4) (l := 4) (by decide)⟩,
      ⟨aligned_add hout (by decide), hsep.sub (c := 8) (l := 4) (by decide)⟩,
      ⟨aligned_add hout (by decide), hsep.sub (c := 0xC) (l := 4) (by decide)⟩⟩
  obtain ⟨m1, c1, u1⟩ := St.block sa8Body s0 hc sa8Body_end hok
  have hc1 := hc.runBlock sa8Body hok
  simp only [runBlock, BInstr.run, sa8Body] at u1 hc1
  obtain ⟨m2, d2, pc2, mem2, regs2⟩ := u1.jalr hc1 sa8_at_10
  refine ⟨m2, c1.trans (.single d2), ?_, ?_, fun r h2 h3 => ?_⟩
  · rw [pc2]; simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero, hra, hret]
  · rw [mem2]; simp +decide only [upd_app, ↓reduceIte]
    rw [ha0, ha1, hz, add_lit_zero, ev_add, zw]; rfl
  · rw [regs2]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact hz.symm
    simp only [upd_app, h0, h2, h3, ite_false]

end C3.RV32
