import C3BootProofs.Proofs.ByteCompare

/-!
# `sec1::point::Tag`'s `from_u8` and `message_len`, as compiled

`Tag::from_u8` accepts the SEC1 encoding tags 0, 2, 3, 4, and 5 and rejects
every other byte. `Tag::message_len` gives the length of an encoded point
with that tag for a field element of `fe` bytes: 1 for the identity, `fe + 1`
for a compressed or compact point, and `2 fe + 1` for an uncompressed one.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem tm_at_0 : fetchRel tagMessageLenCode 0x0 = some (.aluImm .add a2 x0 0x2, 2) := by decide
theorem tm_at_2 : fetchRel tagMessageLenCode 0x2 = some (.aluImm .add a3 a0 0xFFFFFFFE, 4) := by decide
theorem tm_at_6 : fetchRel tagMessageLenCode 0x6 = some (.branch .bltu a3 a2 0x12, 4) := by decide
theorem tm_at_a : fetchRel tagMessageLenCode 0xA = some (.branch .beq a0 x0 0x10, 2) := by decide
theorem tm_at_c : fetchRel tagMessageLenCode 0xC = some (.aluImm .add a2 x0 0x4, 2) := by decide
theorem tm_at_e : fetchRel tagMessageLenCode 0xE = some (.branch .bne a0 a2 0xA, 4) := by decide
theorem tm_at_12 : fetchRel tagMessageLenCode 0x12 = some (.aluImm .sll a0 a1 0x1, 4) := by decide
theorem tm_at_16 : fetchRel tagMessageLenCode 0x16 = some (.jal x0 0x4, 2) := by decide
theorem tm_at_18 : fetchRel tagMessageLenCode 0x18 = some (.alu .add a0 x0 a1, 2) := by decide
theorem tm_at_1a : fetchRel tagMessageLenCode 0x1A = some (.aluImm .add a0 a0 0x1, 2) := by decide
theorem tm_at_1c : fetchRel tagMessageLenCode 0x1C = some (.jalr x0 ra 0x0, 2) := by decide
theorem tf_at_0 : fetchRel tagFromU8Code 0x0 = some (.aluImm .add a3 x0 0x5, 2) := by decide
theorem tf_at_2 : fetchRel tagFromU8Code 0x2 = some (.aluImm .add a2 x0 0x3, 2) := by decide
theorem tf_at_4 : fetchRel tagFromU8Code 0x4 = some (.branch .bltu a3 a1 0x10, 4) := by decide
theorem tf_at_8 : fetchRel tagFromU8Code 0x8 = some (.aluImm .add a3 x0 0x1, 2) := by decide
theorem tf_at_a : fetchRel tagFromU8Code 0xA = some (.branch .beq a1 a3 0xA, 4) := by decide
theorem tf_at_e : fetchRel tagFromU8Code 0xE = some (.store .sb a0 a1 0x4, 4) := by decide
theorem tf_at_12 : fetchRel tagFromU8Code 0x12 = some (.aluImm .add a2 x0 0xFFFFFFFF, 2) := by decide
theorem tf_at_14 : fetchRel tagFromU8Code 0x14 = some (.store .sw a0 a2 0x0, 2) := by decide
theorem tf_at_16 : fetchRel tagFromU8Code 0x16 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- `Tag::message_len` for the tag `t` and a field element of `fe` bytes. -/
def tagMsgLen (t fe : Word) : Word := if t = 0 then 1 else if t = 4 then fe + fe + 1 else fe + 1

/-- What `Tag::from_u8` stores in its `Result<Tag, sec1::Error>` at `out` for
the byte `b`: 0xFFFFFFFF and the tag, or the error 3. -/
def tagFromU8Mem (M : Word → BitVec 8) (out b : Word) : Word → BitVec 8 :=
  if b.toNat ≤ 5 ∧ b.toNat ≠ 1 then memStore32 (memStore8 M (out + 4) (b.extractLsb' 0 8)) out 0xFFFFFFFF
  else memStore32 M out 3

theorem tm_shl1 (fe : Word) : fe <<< ((1 : Word).toNat % 32) = fe + fe := by
  apply BitVec.eq_of_toNat_eq
  rw [show (1 : Word).toNat % 32 = 1 from rfl, BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `Tag::message_len`**: it returns `tagMsgLen` of the tag
and the field element size in `a0`, and writes no memory. -/
theorem tagMessageLen_correct (m : Machine) {base retAddr t fe : Word} (hb : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base tagMessageLenCode) (hpc : m.pc = base) (ha0 : reg m a0 = t) (ha1 : reg m a1 = fe)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' a0 = tagMsgLen t fe ∧ m'.mem = m.mem ∧
      ∀ r, r ≠ a0 → r ≠ a2 → r ≠ a3 → reg m' r = reg m r := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, c1, u1⟩ := St.block [.aluImm .add a2 x0 2, .aluImm .add a3 a0 0xFFFFFFFE] s0 hc (off' := 6) (by decide)
    (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u1
  have k1 : ∀ q, q ≠ a2 → q ≠ a3 → reg n1 q = reg m q := fun q h2 h3 => by
    rw [u1.regs, updz ((updz hz (by decide)).trans hz) h3, updz hz h2]
  have v2 : reg n1 a2 = 2 := by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [hz]; rfl
  have v3 : reg n1 a3 = t + 0xFFFFFFFE := by
    rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0]; rfl
  -- the tail from 0x1A with `x` in `a0`
  have tail : ∀ {n : Machine} (x : Word), St m.mem base n 0x1A (reg n) → reg n a0 = x →
      (∀ r, r ≠ a0 → r ≠ a2 → r ≠ a3 → reg n r = reg m r) →
      ∃ m', Steps n m' ∧ m'.pc = retAddr ∧ reg m' a0 = x + 1 ∧ m'.mem = m.mem ∧
        ∀ r, r ≠ a0 → r ≠ a2 → r ≠ a3 → reg m' r = reg m r := by
    intro n x st r0 kk
    obtain ⟨n1, d1, u1⟩ := st.aluImm hc tm_at_1a (off' := 0x1C) (by decide)
    obtain ⟨n2, d2, pc2, mem2, regs2⟩ := u1.jalr hc tm_at_1c
    refine ⟨n2, .cons d1 (.single d2), ?_, ?_, mem2, fun r h0 h2 h3 => ?_⟩
    · rw [pc2, add_lit_zero, upd_ne' (by decide) st.zero, kk ra (by decide) (by decide) (by decide), hra, hret]
    · rw [regs2]; simp +decide only [upd_app, ↓reduceIte]; rw [r0]; rfl
    · rw [regs2, upd_ne' h0 st.zero]; exact kk r h0 h2 h3
  have t3 : ∀ q, q ≠ a0 → q ≠ a2 → q ≠ a3 → reg n1 q = reg m q := fun q _ h2 h3 => k1 q h2 h3
  by_cases h23 : (t + 0xFFFFFFFE).ult 2 = true
  · have ht : t ≠ 0 ∧ t ≠ 4 := by
      have := of_decide_eq_true (show decide ((t + 0xFFFFFFFE).toNat < (2 : Word).toNat) = true from h23)
      rw [BitVec.toNat_add, show (0xFFFFFFFE : Word).toNat = 4294967294 from rfl,
        show (2 : Word).toNat = 2 from rfl] at this
      refine ⟨fun e => by subst e; revert this; decide, fun e => by subst e; revert this; decide⟩
    obtain ⟨n2, d2, u2⟩ := u1.self.taken hc 0x18 tm_at_6 (by decide) (by rw [v3, v2]; exact h23)
    obtain ⟨n3, d3, u3⟩ := u2.self.alu hc tm_at_18 (off' := 0x1A) (by decide)
    obtain ⟨m', c', h1, h2, h3, h4⟩ := tail fe u3.self
      (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u2.self.zero, u2.regs, k1 a1 (by decide) (by decide),
        ha1]; exact zw fe)
      (fun r h0 h2 h3 => by rw [u3.regs, upd_ne' h0 u2.self.zero, u2.regs]; exact t3 r h0 h2 h3)
    refine ⟨m', c1.trans (.cons d2 (.cons d3 c')), h1, ?_, h3, h4⟩
    rw [h2, tagMsgLen, ite_eq_right ht.1, ite_eq_right ht.2]
  have h23' : (t + 0xFFFFFFFE).ult 2 = false := by
    cases h : (t + 0xFFFFFFFE).ult 2
    · rfl
    · exact absurd h h23
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc 0xA tm_at_6 (by decide) (by rw [v3, v2]; exact h23')
  have r0 : reg n2 a0 = t := by rw [u2.regs, k1 a0 (by decide) (by decide), ha0]
  by_cases h0 : t = 0
  · obtain ⟨n3, d3, u3⟩ := u2.self.taken hc 0x1A tm_at_a (by decide) (by rw [r0, u2.self.zero, h0]; rfl)
    obtain ⟨m', c', h1, h2, h3, h4⟩ := tail 0 u3.self (by rw [u3.regs, r0, h0])
      (fun r h0' h2 h3 => by rw [u3.regs, u2.regs]; exact t3 r h0' h2 h3)
    refine ⟨m', c1.trans (.cons d2 (.cons d3 c')), h1, ?_, h3, h4⟩
    rw [h2, tagMsgLen, ite_eq_left h0]; rfl
  obtain ⟨n3, d3, u3⟩ := u2.self.notTaken hc 0xC tm_at_a (by decide) (by
    rw [r0, u2.self.zero]; exact beq_false_of_ne h0)
  obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hc tm_at_c (off' := 0xE) (by decide)
  have r4 : reg n4 a0 = t := by rw [u4.regs, upd_ne' (by decide) u3.self.zero, u3.regs, r0]
  have v4 : reg n4 a2 = 4 := by rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u3.self.zero]; rfl
  have k4 : ∀ r, r ≠ a0 → r ≠ a2 → r ≠ a3 → reg n4 r = reg m r := fun r h0' h2 h3 => by
    rw [u4.regs, upd_ne' h2 u3.self.zero, u3.regs, u2.regs]; exact t3 r h0' h2 h3
  by_cases h4 : t = 4
  · obtain ⟨n5, d5, u5⟩ := u4.self.notTaken hc 0x12 tm_at_e (by decide) (by
      rw [r4, v4, h4]; exact bne_self_eq_false _)
    obtain ⟨n6, d6, u6⟩ := u5.self.aluImm hc tm_at_12 (off' := 0x16) (by decide)
    obtain ⟨n7, d7, u7⟩ := u6.self.jump hc tm_at_16 (off' := 0x1A) (by decide) (by
      rw [u6.self.pc, show base + BitVec.ofNat 32 0x16 + 0x4 = base + BitVec.ofNat 32 0x1A by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at base hb 0x1A (by decide)))
    obtain ⟨m', c', h1, h2, h3, hk⟩ := tail (fe + fe) u7.self
      (by rw [u7.regs, u6.regs]; simp +decide only [upd_app, ↓reduceIte]
          rw [u5.regs, u4.regs, upd_ne' (by decide) u3.self.zero, u3.regs, u2.regs, k1 a1 (by decide) (by decide), ha1]
          exact tm_shl1 fe)
      (fun r h0' h2 h3 => by rw [u7.regs, u6.regs, upd_ne' h0' u5.self.zero, u5.regs]; exact k4 r h0' h2 h3)
    refine ⟨m', c1.trans (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 c')))))), h1, ?_, h3, hk⟩
    rw [h2, tagMsgLen, ite_eq_right h0, ite_eq_left h4]
  obtain ⟨n5, d5, u5⟩ := u4.self.taken hc 0x18 tm_at_e (by decide) (by
    rw [r4, v4]; simp only [branchTaken, bne_iff_ne, ne_eq]; exact h4)
  obtain ⟨n6, d6, u6⟩ := u5.self.alu hc tm_at_18 (off' := 0x1A) (by decide)
  obtain ⟨m', c', h1, h2, h3, h4'⟩ := tail fe u6.self
    (by rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u5.self.zero, u5.regs, k4 a1 (by decide) (by decide)
      (by decide), ha1]; exact zw fe)
    (fun r h0' h2 h3 => by rw [u6.regs, upd_ne' h0' u5.self.zero, u5.regs]; exact k4 r h0' h2 h3)
  refine ⟨m', c1.trans (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 c'))))), h1, ?_, h3, h4'⟩
  rw [h2, tagMsgLen, ite_eq_right h0, ite_eq_right h4]


set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `Tag::from_u8`**: for the byte `b` in `a1`, it stores
`tagFromU8Mem` at `out`, and changes no other memory. -/
theorem tagFromU8_correct (m : Machine) {base retAddr out b : Word}
    (hc : CodeIn m.mem base tagFromU8Code) (hpc : m.pc = base) (ha0 : reg m a0 = out) (ha1 : reg m a1 = b)
    (hout : out.toNat % 4 = 0) (sOC : Sep out 8 base tagFromU8Code.length)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ m'.mem = tagFromU8Mem m.mem out b ∧
      ∀ r, r ≠ a2 → r ≠ a3 → reg m' r = reg m r := by
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have h0C : Sep out 4 base tagFromU8Code.length := by
    have := sOC.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  obtain ⟨n1, c1, u1⟩ := St.block [.aluImm .add a3 x0 5, .aluImm .add a2 x0 3] s0 hc (off' := 4) (by decide)
    (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u1
  have k1 : ∀ q, q ≠ a2 → q ≠ a3 → reg n1 q = reg m q := fun q h2 h3 => by
    rw [u1.regs, updz ((updz hz (by decide)).trans hz) h2, updz hz h3]
  -- the store of `a2` at 0x14 and the return
  have tail : ∀ {n : Machine} {M : Word → BitVec 8} (x : Word), St M base n 0x14 (reg n) → CodeIn M base tagFromU8Code →
      reg n a2 = x → reg n a0 = out → (∀ r, r ≠ a2 → r ≠ a3 → reg n r = reg m r) →
      ∃ m', Steps n m' ∧ m'.pc = retAddr ∧ m'.mem = memStore32 M out x ∧ ∀ r, r ≠ a2 → r ≠ a3 → reg m' r = reg m r := by
    intro n M x st hcM r2 r0 kk
    obtain ⟨n1, d1, u1⟩ := st.sw hcM tf_at_14 (off' := 0x16) (by decide) (by rw [r0, add_lit_zero]; exact hout)
    rw [r0, add_lit_zero, r2] at u1
    obtain ⟨n2, d2, pc2, mem2, regs2⟩ := u1.jalr (CodeIn.store32 hcM h0C) tf_at_16
    refine ⟨n2, .cons d1 (.single d2), ?_, mem2, fun r h2 h3 => ?_⟩
    · rw [pc2, add_lit_zero, kk ra (by decide) (by decide), hra, hret]
    · rw [regs2]; exact kk r h2 h3
  have v3 : reg n1 a3 = 5 := by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [hz]; rfl
  have v2 : reg n1 a2 = 3 := by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]
  have v1 : reg n1 a1 = b := by rw [k1 a1 (by decide) (by decide), ha1]
  have v0 : reg n1 a0 = out := by rw [k1 a0 (by decide) (by decide), ha0]
  have hb3 : ∀ r, r ≠ a2 → r ≠ a3 → reg n1 r = reg m r := k1
  by_cases hb5 : b.toNat ≤ 5
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc 0x8 tf_at_4 (by decide) (by
      rw [v3, v1]; show decide ((5 : Word).toNat < b.toNat) = false
      exact decide_eq_false (by rw [show (5 : Word).toNat = 5 from rfl]; omega))
    obtain ⟨n3, d3, u3⟩ := u2.self.aluImm hc tf_at_8 (off' := 0xA) (by decide)
    have r3 : ∀ q, q ≠ a3 → reg n3 q = reg n1 q := fun q h => by rw [u3.regs, upd_ne' h u2.self.zero, u2.regs]
    by_cases hb1 : b = 1
    · obtain ⟨n4, d4, u4⟩ := u3.self.taken hc 0x14 tf_at_a (by decide) (by
        rw [r3 a1 (by decide), v1, u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u2.self.zero, hb1]; rfl)
      obtain ⟨m', c', h1, h2, h3⟩ := tail 3 u4.self hc (by rw [u4.regs, r3 a2 (by decide), v2])
        (by rw [u4.regs, r3 a0 (by decide), v0]) (fun r h2 h3 => by rw [u4.regs, r3 r h3]; exact hb3 r h2 h3)
      refine ⟨m', c1.trans (.cons d2 (.cons d3 (.cons d4 c'))), h1, ?_, h3⟩
      rw [h2, tagFromU8Mem, ite_eq_right (fun h => h.2 (by rw [hb1]; rfl))]
    obtain ⟨n4, d4, u4⟩ := u3.self.notTaken hc 0xE tf_at_a (by decide) (by
      rw [r3 a1 (by decide), v1, u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u2.self.zero]
      exact beq_false_of_ne hb1)
    obtain ⟨n5, d5, u5⟩ := u4.self.sb hc tf_at_e (off' := 0x12) (by decide)
    rw [u4.regs a0, r3 a0 (by decide), v0, u4.regs a1, r3 a1 (by decide), v1] at u5
    have hc5 := CodeIn.store8 (v := b.extractLsb' 0 8) hc (sOC.sub (c := 4) (l := 1) (by decide))
    obtain ⟨n6, d6, u6⟩ := u5.aluImm hc5 tf_at_12 (off' := 0x14) (by decide)
    obtain ⟨m', c', h1, h2, h3⟩ := tail 0xFFFFFFFF u6.self hc5
      (by rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u4.self.zero]; rfl)
      (by rw [u6.regs, upd_ne' (by decide) u4.self.zero, u4.regs, r3 a0 (by decide), v0])
      (fun r h2 h3 => by rw [u6.regs, upd_ne' h2 u4.self.zero, u4.regs, r3 r h3]; exact hb3 r h2 h3)
    refine ⟨m', c1.trans (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 c'))))), h1, ?_, h3⟩
    have hb1' : b.toNat ≠ 1 := fun h => hb1 (BitVec.eq_of_toNat_eq h)
    rw [h2, tagFromU8Mem, ite_eq_left ⟨hb5, hb1'⟩]
  obtain ⟨n2, d2, u2⟩ := u1.self.taken hc 0x14 tf_at_4 (by decide) (by
    rw [v3, v1]; show decide ((5 : Word).toNat < b.toNat) = true
    exact decide_eq_true (by rw [show (5 : Word).toNat = 5 from rfl]; omega))
  obtain ⟨m', c', h1, h2, h3⟩ := tail 3 u2.self hc (by rw [u2.regs, v2]) (by rw [u2.regs, v0])
    (fun r h2 h3 => by rw [u2.regs]; exact hb3 r h2 h3)
  refine ⟨m', c1.trans (.cons d2 c'), h1, ?_, h3⟩
  rw [h2, tagFromU8Mem, ite_eq_right (fun h => hb5 h.1)]

end C3.RV32
