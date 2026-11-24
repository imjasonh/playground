import C3BootProofs.Proofs.TimeDigits4

/-!
# `Iter<u8>::all(u8::is_ascii_digit)`, as compiled

`core::slice::Iter<u8>::all` with `u8::is_ascii_digit` walks the iterator
`(ptr, end)` at `a0`, writing the advanced `ptr` back after each byte, and
returns whether every byte it read was an ASCII decimal digit. It stops at
the first byte that isn't one.
-/

namespace C3.RV32

open C3.Image

abbrev AAD : Word := BitVec.ofNat 32 allAsciiDigitAddress

section
set_option maxRecDepth 20000
theorem aad_at_0 : fetchRel allAsciiDigitCode 0x0 = some (.load .lw a4 a0 0x0, 2) := by decide
theorem aad_at_2 : fetchRel allAsciiDigitCode 0x2 = some (.load .lw a1 a0 0x4, 2) := by decide
theorem aad_at_4 : fetchRel allAsciiDigitCode 0x4 = some (.aluImm .add a2 x0 0xA, 2) := by decide
theorem aad_at_6 : fetchRel allAsciiDigitCode 0x6 = some (.alu .add a3 x0 a4, 2) := by decide
theorem aad_at_8 : fetchRel allAsciiDigitCode 0x8 = some (.branch .beq a4 a1 0x16, 4) := by decide
theorem aad_at_1a : fetchRel allAsciiDigitCode 0x1A = some (.branch .bltu a5 a2 0xFFFFFFEC, 4) := by decide
theorem aad_at_1e : fetchRel allAsciiDigitCode 0x1E = some (.alu .xor a1 a1 a3, 2) := by decide
theorem aad_at_20 : fetchRel allAsciiDigitCode 0x20 = some (.aluImm .sltu a0 a1 0x1, 4) := by decide
theorem aad_at_24 : fetchRel allAsciiDigitCode 0x24 = some (.jalr x0 ra 0x0, 2) := by decide
end

def aadB : List BInstr :=
  [.lbu a5 a3 0x0, .aluImm .add a4 a3 0x1, .aluImm .add a5 a5 0xFFFFFFD0, .sw a0 a4 0x0]

section
set_option maxRecDepth 20000
theorem aadB_end : blockEnd allAsciiDigitCode 0xC aadB = some 0x1A := by decide
end

theorem aad_dig : ∀ b : BitVec 8,
    branchTaken .bltu (aluEval .add (b.zeroExtend 32) 0xFFFFFFD0) 10 = (48 ≤ b.toNat && b.toNat ≤ 57) := by decide

theorem aad_eq (x y : Word) : aluEval .sltu (aluEval .xor x y) 1 = if x = y then 1 else 0 := by
  by_cases h : x = y
  · subst h; rw [if_pos rfl]; simp only [aluEval, BitVec.xor_self]; rfl
  · rw [if_neg h]
    have hne : x ^^^ y ≠ 0 := fun e => h (by
      have := congrArg (· ^^^ y) e
      simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at this
      exact this.trans BitVec.zero_xor)
    have hpos : (x ^^^ y).toNat ≠ 0 := fun e => hne (BitVec.eq_of_toNat_eq e)
    simp only [aluEval, BitVec.ult]
    exact if_neg (fun hh => absurd (of_decide_eq_true hh) (by change ¬ (x ^^^ y).toNat < 1; omega))

theorem aad_ne (q : Word) {k : Nat} (h0 : 0 < k) (hk : k < 2 ^ 32) : q ≠ q + BitVec.ofNat 32 k := fun e => by
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  have := q.isLt
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The loop from 0x6, with `c` bytes left from `q`: it returns with 1 in
`a0` when they are all digits and 0 otherwise. -/
theorem aad_loop {M : Word → BitVec 8} {base it retAddr : Word} (hb : base.toNat % 2 = 0)
    (sIC : Sep it 4 base allAsciiDigitCode.length) (hia : it.toNat % 4 = 0) (hret : retAddr &&& ~~~1 = retAddr) :
    ∀ c, ∀ {nn : Machine} {Mx : Word → BitVec 8} {q : Word}, St Mx base nn 0x6 (reg nn) →
    CodeIn Mx base allAsciiDigitCode → (∀ x, Sep it 4 x 1 → Mx x = M x) → reg nn a4 = q →
    reg nn a1 = q + BitVec.ofNat 32 c → reg nn a2 = 10 → reg nn a0 = it → reg nn ra = retAddr → c < 2 ^ 32 →
    (∀ i, i < c → Sep it 4 (q + BitVec.ofNat 32 i) 1) →
    ∃ m', Steps nn m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (if (memBytes M q c).all (fun d => 48 ≤ d && d ≤ 57) then 1 else 0) ∧
      (∀ r, r.val ∉ [10, 11, 12, 13, 14, 15] → reg m' r = reg nn r) ∧ ∀ x, Sep it 4 x 1 → m'.mem x = M x := by
  have hb2 : (base + BitVec.ofNat 32 0x1E).toNat % 2 = 0 := even_at base hb 0x1E (by decide)
  -- the tail from 0x1E
  have fin : ∀ {nn : Machine} {Mx : Word → BitVec 8}, St Mx base nn 0x1E (reg nn) → CodeIn Mx base allAsciiDigitCode →
      reg nn ra = retAddr → ∃ m', Steps nn m' ∧ m'.pc = retAddr ∧
        reg m' a0 = (if reg nn a1 = reg nn a3 then 1 else 0) ∧ (∀ r, r.val ∉ [10, 11] → reg m' r = reg nn r) ∧
        m'.mem = Mx := by
    intro nn Mx st hcx hra
    obtain ⟨n1, d1, u1⟩ := st.alu hcx aad_at_1e (off' := 0x20) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.self.aluImm hcx aad_at_20 (off' := 0x24) (by decide)
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.self.jalr hcx aad_at_24
    refine ⟨n3, .cons d1 (.cons d2 (.single d3)), ?_, ?_, fun r hr => ?_, mem3⟩
    · rw [pc3, add_lit_zero, u2.regs, upd_ne' (by decide) u1.self.zero, u1.regs, upd_ne' (by decide) st.zero, hra, hret]
    · rw [regs3, u2.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; exact aad_eq _ _
    · obtain ⟨h10, h11⟩ : r ≠ a0 ∧ r ≠ a1 := by revert hr; revert r; decide
      rw [regs3, u2.regs, upd_ne' h10 u1.self.zero, u1.regs, upd_ne' h11 st.zero]
  intro c
  induction c with
  | zero =>
    intro nn Mx q st hcx hM r14 r11 r12 r10 r1 _ _
    obtain ⟨n1, d1, u1⟩ := st.alu hcx aad_at_6 (off' := 0x8) (by decide)
    have v13 : reg n1 a3 = q := by
      rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [st.zero, r14]; exact BitVec.zero_add q
    have k1 : ∀ r, r ≠ a3 → reg n1 r = reg nn r := fun r h => by rw [u1.regs, upd_ne' h st.zero]
    obtain ⟨n2, d2, u2⟩ := u1.self.taken hcx 0x1E aad_at_8 (by decide) (by
      rw [k1 a4 (by decide), k1 a1 (by decide), r14, r11, add_ofNat_zero]; exact beq_iff_eq.mpr rfl)
    obtain ⟨m', c', p', a', k', e'⟩ := fin u2.self hcx (by rw [u2.regs, k1 ra (by decide), r1])
    refine ⟨m', .cons d1 (.cons d2 c'), p', ?_, fun r hr => ?_, fun x hx => by rw [e', hM x hx]⟩
    · rw [a', u2.regs, u2.regs, k1 a1 (by decide), r11, v13, add_ofNat_zero, if_pos rfl]; rfl
    · rw [k' r (by revert hr; revert r; decide), u2.regs, k1 r (by revert hr; revert r; decide)]
  | succ c ih =>
    intro nn Mx q st hcx hM r14 r11 r12 r10 r1 hc hS
    obtain ⟨n1, d1, u1⟩ := st.alu hcx aad_at_6 (off' := 0x8) (by decide)
    have v13 : reg n1 a3 = q := by
      rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [st.zero, r14]; exact BitVec.zero_add q
    have k1 : ∀ r, r ≠ a3 → reg n1 r = reg nn r := fun r h => by rw [u1.regs, upd_ne' h st.zero]
    obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hcx 0xC aad_at_8 (by decide) (by
      rw [k1 a4 (by decide), k1 a1 (by decide), r14, r11]
      exact beq_eq_false_iff_ne.mpr (aad_ne q (by omega) hc))
    have sit : Sep it 4 base allAsciiDigitCode.length := sIC
    have r2 : ∀ r, reg n2 r = reg n1 r := u2.regs
    obtain ⟨n3, c3, u3⟩ := St.block aadB u2.self hcx aadB_end (by
      simp +decide only [BlockOk, BInstr.ok, aadB, BInstr.run, upd_app, ↓reduceIte, and_true, true_and]
      rw [r2, k1 a0 (by decide), r10, add_lit_zero]
      exact ⟨hia, sIC⟩)
    have R3 : ∀ r, reg n3 r = (runBlock aadB (Mx, reg n2)).2 r := u3.regs
    have m3 : (runBlock aadB (Mx, reg n2)).1 = memStore32 Mx it (q + 1) := by
      simp +decide only [runBlock, aadB, BInstr.run, upd_app, ↓reduceIte]
      rw [r2, k1 a0 (by decide), r10, add_lit_zero, r2, v13]; rfl
    have u3' : St (memStore32 Mx it (q + 1)) base n3 0x1A (reg n3) := ⟨u3.pc, by rw [u3.mem, m3], fun _ => rfl⟩
    have hc3 : CodeIn (memStore32 Mx it (q + 1)) base allAsciiDigitCode := CodeIn.store32 hcx sIC
    have hq0 : Sep it 4 q 1 := by have := hS 0 (by omega); rwa [add_ofNat_zero] at this
    have v15 : reg n3 a5 = aluEval .add ((M q).zeroExtend 32) 0xFFFFFFD0 := by
      rw [R3]; simp +decide only [runBlock, aadB, BInstr.run, upd_app, ↓reduceIte]
      rw [r2, v13, add_lit_zero, hM q hq0]
    have v14 : reg n3 a4 = q + 1 := by
      rw [R3]; simp +decide only [runBlock, aadB, BInstr.run, upd_app, ↓reduceIte]; rw [r2, v13]; rfl
    have K3 : ∀ r, r.val ∉ [13, 14, 15] → reg n3 r = reg nn r := fun r hr => by
      have hd : r ∉ aadB.filterMap BInstr.dst := by
        simp only [aadB, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
        revert hr; revert r; decide
      rw [R3, runBlock_reg _ _ _ r u2.self.zero hd, r2, k1 r (fun e => by subst e; revert hr; decide)]
    have hspec : memBytes M q (c + 1) = (M q).toNat :: memBytes M (q + 1) c := memBytes_succ M q c
    by_cases hd : (48 ≤ (M q).toNat && (M q).toNat ≤ 57) = true
    · obtain ⟨n4, d4, u4⟩ := u3'.taken hc3 0x6 aad_at_1a (by decide) (by
        rw [v15, K3 a2 (by decide), r12, aad_dig, hd])
      have shift : ∀ i, q + 1 + BitVec.ofNat 32 i = q + BitVec.ofNat 32 (i + 1) := fun i => by
        rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc, Nat.add_comm]
      obtain ⟨m', c', p', a', k', f'⟩ := ih (q := q + 1) u4.self hc3
        (fun x hx => by rw [memStore32_get_sep hx, hM x hx])
        (by rw [u4.regs, v14]) (by rw [u4.regs, K3 a1 (by decide), r11, shift, Nat.add_comm])
        (by rw [u4.regs, K3 a2 (by decide), r12]) (by rw [u4.regs, K3 a0 (by decide), r10])
        (by rw [u4.regs, K3 ra (by decide), r1]) (by omega)
        (fun i hi => by rw [shift]; exact hS (i + 1) (by omega))
      refine ⟨m', .cons d1 (.cons d2 (c3.trans (.cons d4 c'))), p', ?_, fun r hr => ?_, f'⟩
      · rw [a', hspec, List.all_cons, hd, Bool.true_and]
      · rw [k' r hr, u4.regs, K3 r (by revert hr; revert r; decide)]
    · have hd' : (48 ≤ (M q).toNat && (M q).toNat ≤ 57) = false := Bool.eq_false_iff.mpr hd
      obtain ⟨n4, d4, u4⟩ := u3'.notTaken hc3 0x1E aad_at_1a (by decide) (by
        rw [v15, K3 a2 (by decide), r12, aad_dig, hd'])
      obtain ⟨m', c', p', a', k', e'⟩ := fin u4.self hc3 (by rw [u4.regs, K3 ra (by decide), r1])
      refine ⟨m', .cons d1 (.cons d2 (c3.trans (.cons d4 c'))), p', ?_, fun r hr => ?_,
        fun x hx => by rw [e', memStore32_get_sep hx, hM x hx]⟩
      · have e13 : reg n4 a3 = q := by
          rw [u4.regs, R3, runBlock_reg _ _ _ _ u2.self.zero (by decide), r2, v13]
        rw [a', u4.regs a1, K3 a1 (by decide), r11, e13, if_neg (fun e => aad_ne q (by omega) hc e.symm), hspec,
          List.all_cons, hd', Bool.false_and]; rfl
      · rw [k' r (by revert hr; revert r; decide), u4.regs, K3 r (by revert hr; revert r; decide)]

set_option maxRecDepth 20000 in
/-- **The compiled `Iter<u8>::all(u8::is_ascii_digit)`**: with the iterator
over the `L` bytes at `p` at `it`, it returns 1 in `a0` when they are all
digits and 0 otherwise, writing only the iterator's first word. -/
theorem allAsciiDigit_correct (m : Machine) {base it p retAddr : Word} {L : Nat} (hb : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base allAsciiDigitCode) (hpc : m.pc = base) (ha0 : reg m a0 = it) (hia : it.toNat % 4 = 0)
    (lp : memLoad32 m.mem it = p) (le : memLoad32 m.mem (it + 4) = p + BitVec.ofNat 32 L) (hL : L < 2 ^ 32)
    (sIC : Sep it 4 base allAsciiDigitCode.length) (sIP : Sep it 4 p L)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (if (memBytes m.mem p L).all (fun d => 48 ≤ d && d ≤ 57) then 1 else 0) ∧
      (∀ r, r.val ∉ [10, 11, 12, 13, 14, 15] → reg m' r = reg m r) ∧ ∀ x, Sep it 4 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  obtain ⟨n1, d1, u1⟩ := s0.lw hc aad_at_0 (off' := 2) (by decide) (by rw [ha0, add_lit_zero]; exact hia)
  obtain ⟨n2, d2, u2⟩ := u1.self.lw hc aad_at_2 (off' := 4) (by decide) (by
    rw [u1.regs, upd_ne' (by decide) s0.zero, ha0]; exact aligned_add hia (k := 4) (by decide))
  obtain ⟨n3, d3, u3⟩ := u2.self.aluImm hc aad_at_4 (off' := 6) (by decide)
  have k3 : ∀ r, r.val ∉ [11, 12, 14] → reg n3 r = reg m r := fun r hr => by
    obtain ⟨h11, h12, h14⟩ : r ≠ a1 ∧ r ≠ a2 ∧ r ≠ a4 := by revert hr; revert r; decide
    rw [u3.regs, upd_ne' h12 u2.self.zero, u2.regs, upd_ne' h11 u1.self.zero, u1.regs, upd_ne' h14 s0.zero]
  obtain ⟨m', c', p', a', k', f'⟩ := aad_loop (M := m.mem) hb sIC hia hret L u3.self hc (fun _ _ => rfl)
    (by rw [u3.regs, upd_ne' (by decide) u2.self.zero, u2.regs, upd_ne' (by decide) u1.self.zero, u1.regs]
        simp +decide only [upd_app, ↓reduceIte]; rw [ha0, add_lit_zero, lp])
    (by rw [u3.regs, upd_ne' (by decide) u2.self.zero, u2.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [u1.regs, upd_ne' (by decide) s0.zero, ha0, le])
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u2.self.zero]; rfl)
    (by rw [k3 a0 (by decide), ha0]) (by rw [k3 ra (by decide), hra]) hL
    (fun i hi => sIP.subR (c := i) (l := 1) (by omega))
  exact ⟨m', .cons d1 (.cons d2 (.cons d3 c')), p', a', fun r hr => by
    rw [k' r hr, k3 r (by revert hr; revert r; decide)], f'⟩

end C3.RV32
