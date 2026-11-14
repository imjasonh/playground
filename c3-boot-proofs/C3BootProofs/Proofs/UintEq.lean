import C3BootProofs.Proofs.Leaves

/-!
# `Uint<12>::eq` and `Uint<8>::eq`, as compiled

`crypto_bigint`'s constant-time equality ORs the XOR of each pair of limbs
into an accumulator, passes it through the stack, and returns 1 when it is
zero. The two copies differ only in the limb count they load into `a3`, so
one theorem covers any code with these instructions.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem ue12_at_0 : fetchRel uint12EqCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem ue12_at_2 : fetchRel uint12EqCode 0x2 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem ue12_at_4 : fetchRel uint12EqCode 0x4 = some (.aluImm .add a3 x0 0xC, 2) := by decide
theorem ue12_at_6 : fetchRel uint12EqCode 0x6 = some (.branch .beq a3 x0 0x12, 2) := by decide
theorem ue12_at_8 : fetchRel uint12EqCode 0x8 = some (.load .lw a4 a0 0x0, 2) := by decide
theorem ue12_at_a : fetchRel uint12EqCode 0xA = some (.load .lw a5 a1 0x0, 2) := by decide
theorem ue12_at_c : fetchRel uint12EqCode 0xC = some (.alu .xor a4 a4 a5, 2) := by decide
theorem ue12_at_e : fetchRel uint12EqCode 0xE = some (.aluImm .add a0 a0 0x4, 2) := by decide
theorem ue12_at_10 : fetchRel uint12EqCode 0x10 = some (.alu .or a2 a2 a4, 2) := by decide
theorem ue12_at_12 : fetchRel uint12EqCode 0x12 = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem ue12_at_14 : fetchRel uint12EqCode 0x14 = some (.aluImm .add a3 a3 0xFFFFFFFF, 2) := by decide
theorem ue12_at_16 : fetchRel uint12EqCode 0x16 = some (.branch .bne a3 x0 0xFFFFFFF2, 2) := by decide
theorem ue12_at_18 : fetchRel uint12EqCode 0x18 = some (.store .sw sp a2 0xC, 2) := by decide
theorem ue12_at_1a : fetchRel uint12EqCode 0x1A = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem ue12_at_1c : fetchRel uint12EqCode 0x1C = some (.load .lw a0 sp 0xC, 2) := by decide
theorem ue12_at_1e : fetchRel uint12EqCode 0x1E = some (.aluImm .sltu a0 a0 0x1, 4) := by decide
theorem ue12_at_22 : fetchRel uint12EqCode 0x22 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem ue12_at_24 : fetchRel uint12EqCode 0x24 = some (.jalr x0 ra 0x0, 2) := by decide
theorem ue8_at_0 : fetchRel uint8EqCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem ue8_at_2 : fetchRel uint8EqCode 0x2 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem ue8_at_4 : fetchRel uint8EqCode 0x4 = some (.aluImm .add a3 x0 0x8, 2) := by decide
theorem ue8_at_6 : fetchRel uint8EqCode 0x6 = some (.branch .beq a3 x0 0x12, 2) := by decide
theorem ue8_at_8 : fetchRel uint8EqCode 0x8 = some (.load .lw a4 a0 0x0, 2) := by decide
theorem ue8_at_a : fetchRel uint8EqCode 0xA = some (.load .lw a5 a1 0x0, 2) := by decide
theorem ue8_at_c : fetchRel uint8EqCode 0xC = some (.alu .xor a4 a4 a5, 2) := by decide
theorem ue8_at_e : fetchRel uint8EqCode 0xE = some (.aluImm .add a0 a0 0x4, 2) := by decide
theorem ue8_at_10 : fetchRel uint8EqCode 0x10 = some (.alu .or a2 a2 a4, 2) := by decide
theorem ue8_at_12 : fetchRel uint8EqCode 0x12 = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem ue8_at_14 : fetchRel uint8EqCode 0x14 = some (.aluImm .add a3 a3 0xFFFFFFFF, 2) := by decide
theorem ue8_at_16 : fetchRel uint8EqCode 0x16 = some (.branch .bne a3 x0 0xFFFFFFF2, 2) := by decide
theorem ue8_at_18 : fetchRel uint8EqCode 0x18 = some (.store .sw sp a2 0xC, 2) := by decide
theorem ue8_at_1a : fetchRel uint8EqCode 0x1A = some (.aluImm .add a0 sp 0xC, 2) := by decide
theorem ue8_at_1c : fetchRel uint8EqCode 0x1C = some (.load .lw a0 sp 0xC, 2) := by decide
theorem ue8_at_1e : fetchRel uint8EqCode 0x1E = some (.aluImm .sltu a0 a0 0x1, 4) := by decide
theorem ue8_at_22 : fetchRel uint8EqCode 0x22 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem ue8_at_24 : fetchRel uint8EqCode 0x24 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- One pair of limbs, from 0x8 to the branch at 0x16. -/
def ueBody : List BInstr :=
  [.lw a4 a0 0x0, .lw a5 a1 0x0, .alu .xor a4 a4 a5, .aluImm .add a0 a0 0x4, .alu .or a2 a2 a4,
   .aluImm .add a1 a1 0x4, .aluImm .add a3 a3 0xFFFFFFFF]

/-- From 0x18 to the return: the accumulator through the stack, as 1 when
it is zero, and `sp` back. -/
def ueTail : List BInstr :=
  [.sw sp a2 0xC, .aluImm .add a0 sp 0xC, .lw a0 sp 0xC, .aluImm .sltu a0 a0 0x1, .aluImm .add sp sp 0x10]

/-- The instructions of a limb-count-`N` equality. -/
structure UEqCode (code : List Nat) (N : Nat) : Prop where
  pre : blockEnd code 0 [.aluImm .add sp sp 0xFFFFFFF0, .aluImm .add a2 x0 0x0,
    .aluImm .add a3 x0 (BitVec.ofNat 32 N)] = some 6
  h6 : fetchRel code 0x6 = some (.branch .beq a3 x0 0x12, 2)
  body : blockEnd code 0x8 ueBody = some 0x16
  h16 : fetchRel code 0x16 = some (.branch .bne a3 x0 0xFFFFFFF2, 2)
  tail : blockEnd code 0x18 ueTail = some 0x24
  h24 : fetchRel code 0x24 = some (.jalr x0 ra 0x0, 2)

section
set_option maxRecDepth 20000
theorem ue12_code : UEqCode uint12EqCode 12 := ⟨by decide, ue12_at_6, by decide, ue12_at_16, by decide, ue12_at_24⟩
theorem ue8_code : UEqCode uint8EqCode 8 := ⟨by decide, ue8_at_6, by decide, ue8_at_16, by decide, ue8_at_24⟩
end

theorem sltu1 (w : Word) : aluEval .sltu w 1 = if w = 0 then 1 else 0 := by
  by_cases h : w = 0
  · subst h; decide
  · rw [ite_eq_right h]
    have : 0 < w.toNat := by
      rcases Nat.eq_zero_or_pos w.toNat with h' | h'
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h']; rfl)) h
      · exact h'
    show (if BitVec.ult w 1 then 1 else 0) = _
    rw [ite_eq_right (by simp only [BitVec.ult, decide_eq_true_eq]; show ¬ w.toNat < 1; omega)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`Uint<N>::eq`**, for code with `UEqCode`'s instructions: it returns 1
when the `N` limbs at `p` equal those at `q`, and 0 otherwise. It writes
the word below `sp`. -/
theorem uintEq_correct {code : List Nat} {N : Nat} (C : UEqCode code N) (hN : 0 < N) (hN' : N < 2 ^ 32)
    (m : Machine) {base retAddr p q : Word}
    (hc : CodeIn m.mem base code) (hpc : m.pc = base) (ha0 : reg m a0 = p) (ha1 : reg m a1 = q)
    (hp : p.toNat % 4 = 0) (hq : q.toNat % 4 = 0)
    (hsp : (reg m sp).toNat % 4 = 0) (hsep : Sep (reg m sp + 0xFFFFFFFC) 4 base code.length)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (if ∀ i, i < N → memLoad32 m.mem (p + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (q + BitVec.ofNat 32 (4 * i)) then 1 else 0) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFFC) 4 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have eF : reg m sp + 0xFFFFFFF0 + 0xC = reg m sp + 0xFFFFFFFC := by rw [BitVec.add_assoc]; rfl
  -- the tail, from 0x18 with the accumulator in `a2`
  have tail : ∀ {n1 : Machine} {acc : Word}, St m.mem base n1 0x18 (reg n1) → reg n1 a2 = acc →
      reg n1 sp = reg m sp + 0xFFFFFFF0 →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ sp → reg n1 r = reg m r) →
      ∃ m', Steps n1 m' ∧ m'.pc = retAddr ∧ reg m' a0 = (if acc = 0 then 1 else 0) ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧
        ∀ x, Sep (reg m sp + 0xFFFFFFFC) 4 x 1 → m'.mem x = m.mem x := by
    intro n1 acc s1 r2 rsp hk
    obtain ⟨n2, c2, u2⟩ := St.block ueTail s1 hc C.tail (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, ueTail, upd_app, ↓reduceIte, and_true, true_and]
      rw [rsp, eF]
      exact ⟨⟨aligned_add hsp (k := 0xFFFFFFFC) (by decide), hsep⟩, aligned_add hsp (k := 0xFFFFFFFC) (by decide)⟩)
    simp only [runBlock, BInstr.run, ueTail] at u2
    have hcT : CodeIn (memStore32 m.mem (reg n1 sp + 0xC) (reg n1 a2)) base code :=
      hc.store32 (by rw [rsp, eF]; exact hsep)
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hcT C.h24
    refine ⟨n3, c2.trans (.single d3), ?_, ?_, fun r h0' h1' h2' h3' h4' h5' => ?_, fun x hx => ?_⟩
    · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]
      rw [hk ra (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), add_lit_zero,
        hra, hret]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]
      rw [rsp, eF, memLoad32_store32_same, r2, sltu1]
    · rw [regs3]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz.symm
      by_cases hs : r = sp
      · subst hs; simp +decide only [upd_app, ↓reduceIte]
        rw [rsp, ev_add, BitVec.add_assoc, show (0xFFFFFFF0 : Word) + 0x10 = 0 by decide, add_lit_zero]
      simp only [upd_app, h0, hs, h0', ite_false]; exact hk r h0' h1' h2' h3' h4' h5' hs
    · rw [mem3, rsp, eF]
      exact memStore32_get_sep hx
  have orx : ∀ acc x y : Word, aluEval .or acc (aluEval .xor x y) = 0 ↔ acc = 0 ∧ x = y := fun acc x y => by
    exact BitVec.or_eq_zero_iff.trans (and_congr Iff.rfl BitVec.xor_eq_zero_iff)
  -- the loop, from limb `i` with `k` left
  have loop : ∀ k i, i + k = N → 0 < k → ∀ {n1 : Machine} {acc : Word}, St m.mem base n1 0x8 (reg n1) →
      reg n1 a0 = p + BitVec.ofNat 32 (4 * i) → reg n1 a1 = q + BitVec.ofNat 32 (4 * i) →
      reg n1 a3 = BitVec.ofNat 32 k → reg n1 a2 = acc →
      (acc = 0 ↔ ∀ j, j < i → memLoad32 m.mem (p + BitVec.ofNat 32 (4 * j)) =
        memLoad32 m.mem (q + BitVec.ofNat 32 (4 * j))) →
      reg n1 sp = reg m sp + 0xFFFFFFF0 →
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ sp → reg n1 r = reg m r) →
      ∃ n' acc', Steps n1 n' ∧ St m.mem base n' 0x18 (reg n') ∧ reg n' a2 = acc' ∧
        (acc' = 0 ↔ ∀ j, j < N → memLoad32 m.mem (p + BitVec.ofNat 32 (4 * j)) =
          memLoad32 m.mem (q + BitVec.ofNat 32 (4 * j))) ∧
        reg n' sp = reg m sp + 0xFFFFFFF0 ∧
        (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ sp → reg n' r = reg m r) := by
    intro k
    induction k with
    | zero => intro i _ hk; exact absurd hk (Nat.lt_irrefl 0)
    | succ k ih =>
      intro i hik _ n1 acc s1 r0 r1 r3 r2 hacc rsp hk
      obtain ⟨n2, c2, u2⟩ := St.block ueBody s1 hc C.body (by
        simp +decide only [BlockOk, BInstr.ok, BInstr.run, ueBody, upd_app, ↓reduceIte, and_true]
        rw [r0, r1, add_lit_zero, add_lit_zero]
        exact ⟨aligned_add hp (by omega), aligned_add hq (by omega)⟩)
      simp only [runBlock, BInstr.run, ueBody] at u2
      have g2 : ∀ r, reg n2 r = _ := u2.regs
      have w : reg n2 a2 = aluEval .or acc (aluEval .xor (memLoad32 m.mem (p + BitVec.ofNat 32 (4 * i)))
          (memLoad32 m.mem (q + BitVec.ofNat 32 (4 * i)))) := by
        rw [g2]; simp +decide only [upd_app, ↓reduceIte]; rw [r0, r1, r2, add_lit_zero, add_lit_zero]
      have hacc' : aluEval .or acc (aluEval .xor (memLoad32 m.mem (p + BitVec.ofNat 32 (4 * i)))
          (memLoad32 m.mem (q + BitVec.ofNat 32 (4 * i)))) = 0 ↔
          ∀ j, j < i + 1 → memLoad32 m.mem (p + BitVec.ofNat 32 (4 * j)) =
            memLoad32 m.mem (q + BitVec.ofNat 32 (4 * j)) := by
        rw [orx, hacc]
        constructor
        · intro ⟨h1, h2⟩ j hj
          rcases Nat.lt_or_ge j i with h | h
          · exact h1 j h
          · have : j = i := by omega
            subst this; exact h2
        · intro h; exact ⟨fun j hj => h j (by omega), h i (by omega)⟩
      have r23 : reg n2 a3 = BitVec.ofNat 32 k := by
        rw [g2]; simp +decide only [upd_app, ↓reduceIte]; rw [r3, ev_add]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, ofNat_tn (by omega), ofNat_tn (by omega)]
        show (k + 1 + 4294967295) % 2 ^ 32 = k; omega
      have keep2 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ sp → reg n2 r = reg m r :=
        fun r h0' h1' h2' h3' h4' h5' hs => by
          rw [g2]
          by_cases h0 : r.val = 0
          · have : r = 0 := Fin.ext h0
            subst this; simp [upd]; exact hz.symm
          simp only [upd_app, h0, h0', h1', h2', h3', h4', h5', ite_false]; exact hk r h0' h1' h2' h3' h4' h5' hs
      have sp2 : reg n2 sp = reg m sp + 0xFFFFFFF0 := by
        rw [g2]; simp +decide only [upd_app, ↓reduceIte]; exact rsp
      have adv : ∀ b : Word, b + BitVec.ofNat 32 (4 * i) + 4 = b + BitVec.ofNat 32 (4 * (i + 1)) := fun b => by
        rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]; congr 2
      by_cases hk0 : k = 0
      · subst hk0
        obtain ⟨n3, d3, u3⟩ := u2.self.notTaken hc 0x18 C.h16 (by decide) (by rw [r23, u2.self.zero]; decide)
        exact ⟨n3, _, c2.trans (.single d3), u3.self, by rw [u3.regs, w], by rw [← show i + 1 = N by omega]; exact hacc',
          by rw [u3.regs, sp2], fun r h0' h1' h2' h3' h4' h5' hs => by rw [u3.regs]; exact keep2 r h0' h1' h2' h3' h4' h5' hs⟩
      · obtain ⟨n3, d3, u3⟩ := u2.self.taken hc 0x8 C.h16 (by decide) (by
          rw [r23, u2.self.zero]; simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
          have := congrArg BitVec.toNat h; rw [ofNat_tn (by omega)] at this; exact hk0 this)
        obtain ⟨n', acc', c', h1, h2, h3, h4, h5⟩ := ih (i + 1) (by omega) (by omega) u3.self
          (by rw [u3.regs, g2]; simp +decide only [upd_app, ↓reduceIte]; rw [r0, ev_add, adv])
          (by rw [u3.regs, g2]; simp +decide only [upd_app, ↓reduceIte]; rw [r1, ev_add, adv])
          (by rw [u3.regs, r23]) (by rw [u3.regs, w]) hacc' (by rw [u3.regs, sp2])
          (fun r h0' h1' h2' h3' h4' h5' hs => by rw [u3.regs]; exact keep2 r h0' h1' h2' h3' h4' h5' hs)
        exact ⟨n', acc', c2.trans (.cons d3 c'), h1, h2, h3, h4, h5⟩
  obtain ⟨n1, c1, u1⟩ := St.block _ s0 hc C.pre (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u1
  have g1 : ∀ r, reg n1 r = _ := u1.regs
  have sp1 : reg n1 sp = reg m sp + 0xFFFFFFF0 := by rw [g1]; simp +decide only [upd_app, ↓reduceIte, ev_add]
  have a21 : reg n1 a2 = 0 := by
    rw [g1]; simp +decide only [upd_app, ↓reduceIte]
    first | done | (rw [hz]; rfl) | rfl
  have a31 : reg n1 a3 = BitVec.ofNat 32 N := by
    rw [g1]; simp +decide only [upd_app, ↓reduceIte]
    first | done | (rw [hz]; exact zw _) | exact zw _
  have keep1 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ sp → reg n1 r = reg m r :=
    fun r h0' h1' h2' h3' h4' h5' hs => by
      rw [g1]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz.symm
      simp only [upd_app, h0, h2', h3', hs, ite_false]
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc 0x8 C.h6 (by decide) (by
    rw [a31, u1.self.zero]
    simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]; intro h
    have := congrArg BitVec.toNat h; rw [ofNat_tn hN'] at this; change N = 0 at this; omega)
  obtain ⟨n3, acc, c3, s3, r3, hacc, sp3, k3⟩ := loop N 0 (by omega) hN u2.self
    (by rw [u2.regs, g1]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0, add_ofNat_zero])
    (by rw [u2.regs, g1]; simp +decide only [upd_app, ↓reduceIte]; rw [ha1, add_ofNat_zero])
    (by rw [u2.regs, a31]) (by rw [u2.regs, a21]) ⟨fun _ j hj => absurd hj (Nat.not_lt_zero j), fun _ => rfl⟩
    (by rw [u2.regs, sp1]) (fun r h0' h1' h2' h3' h4' h5' hs => by rw [u2.regs]; exact keep1 r h0' h1' h2' h3' h4' h5' hs)
  obtain ⟨m', c', h1, h2, h3, h4⟩ := tail s3 r3 sp3 k3
  refine ⟨m', c1.trans (.cons d2 (c3.trans c')), h1, ?_, h3, h4⟩
  rw [h2]
  by_cases hall : ∀ i, i < N → memLoad32 m.mem (p + BitVec.ofNat 32 (4 * i)) =
      memLoad32 m.mem (q + BitVec.ofNat 32 (4 * i))
  · rw [ite_eq_left (hacc.mpr hall), ite_eq_left hall]
  · rw [ite_eq_right (fun h => hall (hacc.mp h)), ite_eq_right hall]

/-- **The compiled `Uint<12>::eq`**: 1 when the 12 limbs at `p` equal those
at `q`, and 0 otherwise. -/
theorem uint12Eq_correct (m : Machine) {base retAddr p q : Word}
    (hc : CodeIn m.mem base uint12EqCode) (hpc : m.pc = base) (ha0 : reg m a0 = p) (ha1 : reg m a1 = q)
    (hp : p.toNat % 4 = 0) (hq : q.toNat % 4 = 0)
    (hsp : (reg m sp).toNat % 4 = 0) (hsep : Sep (reg m sp + 0xFFFFFFFC) 4 base uint12EqCode.length)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (if ∀ i : Nat, i < 12 → memLoad32 m.mem (p + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (q + BitVec.ofNat 32 (4 * i)) then 1 else 0) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFFC) 4 x 1 → m'.mem x = m.mem x :=
  uintEq_correct ue12_code (by decide) (by decide) m hc hpc ha0 ha1 hp hq hsp hsep hra hret

/-- **The compiled `Uint<8>::eq`**: 1 when the 8 limbs at `p` equal those at
`q`, and 0 otherwise. -/
theorem uint8Eq_correct (m : Machine) {base retAddr p q : Word}
    (hc : CodeIn m.mem base uint8EqCode) (hpc : m.pc = base) (ha0 : reg m a0 = p) (ha1 : reg m a1 = q)
    (hp : p.toNat % 4 = 0) (hq : q.toNat % 4 = 0)
    (hsp : (reg m sp).toNat % 4 = 0) (hsep : Sep (reg m sp + 0xFFFFFFFC) 4 base uint8EqCode.length)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (if ∀ i : Nat, i < 8 → memLoad32 m.mem (p + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (q + BitVec.ofNat 32 (4 * i)) then 1 else 0) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFFC) 4 x 1 → m'.mem x = m.mem x :=
  uintEq_correct ue8_code (by decide) (by decide) m hc hpc ha0 ha1 hp hq hsp hsep hra hret

end C3.RV32
