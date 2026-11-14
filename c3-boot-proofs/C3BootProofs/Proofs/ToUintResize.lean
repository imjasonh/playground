import C3BootProofs.Proofs.LincombShift12
import C3BootProofs.Proofs.ShrWide12Main

/-!
# `UintRef::to_uint_resize::<2>`

The compiled function zeroes a 2-limb result and copies the low two limbs
of its argument into it.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem tur_at_0 : fetchRel toUintResize2Code 0x0 = some (.aluImm .add a2 x0 0x0, 2) := by decide
theorem tur_at_2 : fetchRel toUintResize2Code 0x2 = some (.store .sw a0 a2 0x0, 2) := by decide
theorem tur_at_4 : fetchRel toUintResize2Code 0x4 = some (.store .sw a0 a2 0x4, 2) := by decide
theorem tur_at_6 : fetchRel toUintResize2Code 0x6 = some (.aluImm .add a2 x0 0x2, 2) := by decide
theorem tur_at_8 : fetchRel toUintResize2Code 0x8 = some (.branch .beq a2 x0 0xE, 2) := by decide
theorem tur_at_a : fetchRel toUintResize2Code 0xA = some (.load .lw a3 a1 0x0, 2) := by decide
theorem tur_at_c : fetchRel toUintResize2Code 0xC = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem tur_at_e : fetchRel toUintResize2Code 0xE = some (.store .sw a0 a3 0x0, 2) := by decide
theorem tur_at_10 : fetchRel toUintResize2Code 0x10 = some (.aluImm .add a0 a0 0x4, 2) := by decide
theorem tur_at_12 : fetchRel toUintResize2Code 0x12 = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) := by decide
theorem tur_at_14 : fetchRel toUintResize2Code 0x14 = some (.branch .bne a2 x0 0xFFFFFFF6, 2) := by decide
theorem tur_at_16 : fetchRel toUintResize2Code 0x16 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- From 0 to the branch at 8: zero the result's two words, and the count. -/
def turZ : List BInstr := [.aluImm .add a2 x0 0, .sw a0 a2 0, .sw a0 a2 4, .aluImm .add a2 x0 2]

/-- From 0xA to the branch at 0x14: copy one word and advance. -/
def turL : List BInstr :=
  [.lw a3 a1 0, .aluImm .add a1 a1 4, .sw a0 a3 0, .aluImm .add a0 a0 4, .aluImm .add a2 a2 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem turZ_end : blockEnd toUintResize2Code 0 turZ = some 8 := by decide
theorem turL_end : blockEnd toUintResize2Code 0xA turL = some 0x14 := by decide
end

theorem turZ_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock turZ (M, f)).1 = memStore32 (memStore32 M (f a0 + 0) 0) (f a0 + 4) 0 ∧
    (runBlock turZ (M, f)).2 a2 = 2 ∧
    ∀ q, q ≠ a2 → (runBlock turZ (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, turZ]
  refine ⟨?_, ?_, fun q q2 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rw [show f x0 = 0 from hz]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q2]

theorem turL_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock turL (M, f)).1 = memStore32 M (f a0 + 0) (memLoad32 M (f a1 + 0)) ∧
    (runBlock turL (M, f)).2 a0 = f a0 + 4 ∧ (runBlock turL (M, f)).2 a1 = f a1 + 4 ∧
    (runBlock turL (M, f)).2 a2 = f a2 + 0xFFFFFFFF ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → (runBlock turL (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, turL]
  refine ⟨?_, ?_, ?_, ?_, fun q q0 q1 q2 q3 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1, q2, q3]

theorem turZ_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h0 : (f a0 + 0).toNat % 4 = 0) (h4 : (f a0 + 4).toNat % 4 = 0)
    (s0 : Sep (f a0 + 0) 4 base len) (s4 : Sep (f a0 + 4) 4 base len) :
    BlockOk base len turZ (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, turZ, upd, ↓reduceIte, and_true, true_and]
  exact ⟨⟨h0, s0⟩, h4, s4⟩

theorem turL_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h1 : (f a1 + 0).toNat % 4 = 0) (h0 : (f a0 + 0).toNat % 4 = 0) (s0 : Sep (f a0 + 0) 4 base len) :
    BlockOk base len turL (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, turL, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h1, h0, s0⟩

set_option maxRecDepth 20000 in
/-- **The compiled `UintRef::to_uint_resize::<2>`**: the two words at `out`
get the two words at `src`. It uses no stack, changes only `a0` through
`a3`, and writes only the 8 bytes at `out`. -/
theorem toUintResize2_correct (m : Machine) {P out src retAddr : Word}
    (hc : CodeIn m.mem P toUintResize2Code) (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = src)
    (hout : out.toNat % 4 = 0) (hsrc : src.toNat % 4 = 0) (hos : Sep out 8 src 8)
    (hoc : Sep out 8 P toUintResize2Code.length) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg m' q = reg m q) ∧
      memLoad32 m'.mem out = memLoad32 m.mem src ∧ memLoad32 m'.mem (out + 4) = memLoad32 m.mem (src + 4) ∧
      ∀ x, Sep out 8 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have o0 : Sep out 4 P toUintResize2Code.length := by
    have := hoc.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have o4 : Sep (out + 4) 4 P toUintResize2Code.length := hoc.sub (c := 4) (l := 4) (by decide)
  have al4 : (out + 4).toNat % 4 = 0 := aligned_add hout (by decide)
  have sr4 : (src + 4).toNat % 4 = 0 := aligned_add hsrc (by decide)
  -- zero the result
  obtain ⟨n1, c1, u1⟩ := St.block turZ s0 hc turZ_end
    (turZ_ok (by rw [ha0, add_lit_zero]; exact hout) (by rw [ha0]; exact al4) (by rw [ha0, add_lit_zero]; exact o0)
      (by rw [ha0]; exact o4))
  obtain ⟨zm, z2, zk⟩ := turZ_run (M := m.mem) (f := reg m) hz
  rw [zm, ha0, add_lit_zero] at u1
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 (memStore32 m.mem out 0) (out + 4) 0 = M1 := ⟨_, rfl⟩
  rw [hM1] at u1
  have hc1 : CodeIn M1 P toUintResize2Code := by rw [← hM1]; exact (hc.store32 o0).store32 o4
  have fr1 : ∀ x, Sep out 8 x 1 → M1 x = m.mem x := fun x hx => by
    rw [← hM1, memStore32_get_sep (a := out + 4) (hx.sub (c := 4) (l := 4) (by decide)),
      memStore32_get_sep (by have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)]
  have ls : ∀ k, k = 0 ∨ k = 4 → memLoad32 M1 (src + BitVec.ofNat 32 k) = memLoad32 m.mem (src + BitVec.ofNat 32 k) :=
    fun k hk => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact fr1 _ (hos.subR (c := k + j) (l := 1) (by omega))
  have g1 : ∀ q, reg n1 q = (runBlock turZ (m.mem, reg m)).2 q := u1.regs
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0xA tur_at_8 (by decide) (by rw [g1, z2, u1.self.zero]; decide)
  -- the two limbs
  have r2a0 : reg n2 a0 = out := by rw [u2.regs, g1, zk _ (by decide), ha0]
  have r2a1 : reg n2 a1 = src := by rw [u2.regs, g1, zk _ (by decide), ha1]
  have r2a2 : reg n2 a2 = 2 := by rw [u2.regs, g1, z2]
  obtain ⟨n3, c3, u3⟩ := St.block turL u2.self hc1 turL_end
    (turL_ok (by rw [r2a1, add_lit_zero]; exact hsrc) (by rw [r2a0, add_lit_zero]; exact hout)
      (by rw [r2a0, add_lit_zero]; exact o0))
  obtain ⟨lm3, l03, l13, l23, lk3⟩ := turL_run (M := M1) (f := reg n2) u2.self.zero
  rw [lm3, r2a0, r2a1, add_lit_zero, add_lit_zero] at u3
  have g3 : ∀ q, reg n3 q = (runBlock turL (M1, reg n2)).2 q := u3.regs
  have hc3 : CodeIn (memStore32 M1 out (memLoad32 M1 src)) P toUintResize2Code := hc1.store32 o0
  obtain ⟨n4, d4, u4⟩ := u3.self.taken hc3 0xA tur_at_14 (by decide)
    (by rw [g3, l23, r2a2, u3.self.zero]; decide)
  have r4a0 : reg n4 a0 = out + 4 := by rw [u4.regs, g3, l03, r2a0]
  have r4a1 : reg n4 a1 = src + 4 := by rw [u4.regs, g3, l13, r2a1]
  have r4a2 : reg n4 a2 = 1 := by rw [u4.regs, g3, l23, r2a2]; rfl
  obtain ⟨n5, c5, u5⟩ := St.block turL u4.self hc3 turL_end
    (turL_ok (by rw [r4a1, add_lit_zero]; exact sr4) (by rw [r4a0, add_lit_zero]; exact al4)
      (by rw [r4a0, add_lit_zero]; exact o4))
  obtain ⟨lm5, l05, l15, l25, lk5⟩ := turL_run (M := memStore32 M1 out (memLoad32 M1 src)) (f := reg n4) u4.self.zero
  rw [lm5, r4a0, r4a1, add_lit_zero, add_lit_zero] at u5
  have g5 : ∀ q, reg n5 q = _ := u5.regs
  have hc5 := hc3.store32 (v := memLoad32 (memStore32 M1 out (memLoad32 M1 src)) (src + 4)) o4
  obtain ⟨n6, d6, u6⟩ := u5.self.notTaken hc5 0x16 tur_at_14 (by decide)
    (by rw [g5, l25, r4a2, u5.self.zero]; decide)
  obtain ⟨n7, d7, pc7, mem7, regs7⟩ := u6.self.jalr hc5 tur_at_16
  have keep : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg n6 q = reg m q := fun q q0 q1 q2 q3 => by
    rw [u6.regs, g5, lk5 q q0 q1 q2 q3, u4.regs, g3, lk3 q q0 q1 q2 q3, u2.regs, g1, zk q q2]
  have e1 : memLoad32 (memStore32 M1 out (memLoad32 M1 src)) (src + 4) = memLoad32 m.mem (src + 4) := by
    have h0 : Sep out 4 (src + 4) 4 := by
      have := (hos.sub (c := 0) (l := 4) (by decide)).subR (c := 4) (l := 4) (by decide)
      rwa [add_ofNat_zero] at this
    rw [memLoad32_store32_sep h0]
    exact ls 4 (.inr rfl)
  refine ⟨n7, c1.trans (.cons d2 (c3.trans (.cons d4 (c5.trans (.cons d6 (.single d7)))))), ?_,
    fun q q0 q1 q2 q3 => by rw [regs7, keep q q0 q1 q2 q3], ?_, ?_, fun x hx => ?_⟩
  · rw [pc7, keep ra (by decide) (by decide) (by decide) (by decide), hra, add_lit_zero, hret]
  · have h40 : Sep (out + 4) 4 out 4 := by
      have := sep_offsets out (c := 4) (n := 4) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
    rw [mem7, memLoad32_store32_sep h40, memLoad32_store32_same]
    have := ls 0 (.inl rfl); rwa [add_ofNat_zero] at this
  · rw [mem7, memLoad32_store32_same, e1]
  · rw [mem7, memStore32_get_sep (a := out + 4) (hx.sub (c := 4) (l := 4) (by decide)),
      memStore32_get_sep (by have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this), fr1 x hx]

end C3.RV32
