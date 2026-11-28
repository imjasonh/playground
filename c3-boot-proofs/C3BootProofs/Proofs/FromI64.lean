import C3BootProofs.Proofs.AbsSign2

/-!
# `Int<2>::from_i64`, as compiled

`crypto_bigint`'s `Int<2>::from_i64` on a 32-bit target: the `i64`'s two
words become the two limbs. The compiled code goes the long way round: it
copies the words into a second buffer, overwrites that buffer with the sign
extension, and copies the words over it again before it returns them.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem fi_at_0 : fetchRel fromI64Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem fi_at_2 : fetchRel fromI64Code 0x2 = some (.store .sw sp a1 0x0, 2) := by decide
theorem fi_at_4 : fetchRel fromI64Code 0x4 = some (.store .sw sp a2 0x4, 2) := by decide
theorem fi_at_6 : fetchRel fromI64Code 0x6 = some (.store .sw sp x0 0x8, 2) := by decide
theorem fi_at_8 : fetchRel fromI64Code 0x8 = some (.store .sw sp x0 0xC, 2) := by decide
theorem fi_at_a : fetchRel fromI64Code 0xA = some (.alu .add a1 x0 sp, 2) := by decide
theorem fi_at_c : fetchRel fromI64Code 0xC = some (.aluImm .add a2 sp 0x8, 2) := by decide
theorem fi_at_e : fetchRel fromI64Code 0xE = some (.aluImm .add a3 x0 0x2, 2) := by decide
theorem fi_at_10 : fetchRel fromI64Code 0x10 = some (.branch .beq a3 x0 0xE, 2) := by decide
theorem fi_at_12 : fetchRel fromI64Code 0x12 = some (.load .lw a4 a1 0x0, 2) := by decide
theorem fi_at_14 : fetchRel fromI64Code 0x14 = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem fi_at_16 : fetchRel fromI64Code 0x16 = some (.store .sw a2 a4 0x0, 2) := by decide
theorem fi_at_18 : fetchRel fromI64Code 0x18 = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem fi_at_1a : fetchRel fromI64Code 0x1A = some (.aluImm .add a3 a3 0xFFFFFFFF, 2) := by decide
theorem fi_at_1c : fetchRel fromI64Code 0x1C = some (.branch .bne a3 x0 0xFFFFFFF6, 2) := by decide
theorem fi_at_1e : fetchRel fromI64Code 0x1E = some (.load .lw a1 sp 0xC, 2) := by decide
theorem fi_at_20 : fetchRel fromI64Code 0x20 = some (.aluImm .srl a1 a1 0x1F, 2) := by decide
theorem fi_at_22 : fetchRel fromI64Code 0x22 = some (.store .sb sp a1 0x8, 4) := by decide
theorem fi_at_26 : fetchRel fromI64Code 0x26 = some (.aluImm .add a1 sp 0x8, 2) := by decide
theorem fi_at_28 : fetchRel fromI64Code 0x28 = some (.load .lbu a2 sp 0x8, 4) := by decide
theorem fi_at_2c : fetchRel fromI64Code 0x2C = some (.alu .sub a2 x0 a2, 4) := by decide
theorem fi_at_30 : fetchRel fromI64Code 0x30 = some (.aluImm .add a3 x0 0x2, 2) := by decide
theorem fi_at_32 : fetchRel fromI64Code 0x32 = some (.branch .beq a3 x0 0xA, 2) := by decide
theorem fi_at_34 : fetchRel fromI64Code 0x34 = some (.store .sw a1 a2 0x0, 2) := by decide
theorem fi_at_36 : fetchRel fromI64Code 0x36 = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem fi_at_38 : fetchRel fromI64Code 0x38 = some (.aluImm .add a3 a3 0xFFFFFFFF, 2) := by decide
theorem fi_at_3a : fetchRel fromI64Code 0x3A = some (.branch .bne a3 x0 0xFFFFFFFA, 2) := by decide
theorem fi_at_3c : fetchRel fromI64Code 0x3C = some (.alu .add a1 x0 sp, 2) := by decide
theorem fi_at_3e : fetchRel fromI64Code 0x3E = some (.aluImm .add a2 sp 0x8, 2) := by decide
theorem fi_at_40 : fetchRel fromI64Code 0x40 = some (.aluImm .add a3 x0 0x2, 2) := by decide
theorem fi_at_42 : fetchRel fromI64Code 0x42 = some (.branch .beq a3 x0 0xE, 2) := by decide
theorem fi_at_44 : fetchRel fromI64Code 0x44 = some (.load .lw a4 a1 0x0, 2) := by decide
theorem fi_at_46 : fetchRel fromI64Code 0x46 = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem fi_at_48 : fetchRel fromI64Code 0x48 = some (.store .sw a2 a4 0x0, 2) := by decide
theorem fi_at_4a : fetchRel fromI64Code 0x4A = some (.aluImm .add a2 a2 0x4, 2) := by decide
theorem fi_at_4c : fetchRel fromI64Code 0x4C = some (.aluImm .add a3 a3 0xFFFFFFFF, 2) := by decide
theorem fi_at_4e : fetchRel fromI64Code 0x4E = some (.branch .bne a3 x0 0xFFFFFFF6, 2) := by decide
theorem fi_at_50 : fetchRel fromI64Code 0x50 = some (.load .lw a1 sp 0x8, 2) := by decide
theorem fi_at_52 : fetchRel fromI64Code 0x52 = some (.load .lw a2 sp 0xC, 2) := by decide
theorem fi_at_54 : fetchRel fromI64Code 0x54 = some (.store .sw a0 a1 0x0, 2) := by decide
theorem fi_at_56 : fetchRel fromI64Code 0x56 = some (.store .sw a0 a2 0x4, 2) := by decide
theorem fi_at_58 : fetchRel fromI64Code 0x58 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem fi_at_5a : fetchRel fromI64Code 0x5A = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- From 0 to 0x10: the frame, `n`'s words at its bottom, the second buffer
zeroed, and the copy loop's pointers. -/
def fiPro : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFFF0, .sw sp a1 0x0, .sw sp a2 0x4, .sw sp x0 0x8, .sw sp x0 0xC, .alu .add a1 x0 sp,
   .aluImm .add a2 sp 0x8, .aluImm .add a3 x0 0x2]

/-- One limb of a copy, at 0x12 and again at 0x44. -/
def fiCp : List BInstr :=
  [.lw a4 a1 0x0, .aluImm .add a1 a1 0x4, .sw a2 a4 0x0, .aluImm .add a2 a2 0x4, .aluImm .add a3 a3 0xFFFFFFFF]

/-- From 0x1E to 0x32: the sign through a byte of the buffer, and the fill
loop's pointer. -/
def fiSign : List BInstr :=
  [.lw a1 sp 0xC, .aluImm .srl a1 a1 0x1F, .sb sp a1 0x8, .aluImm .add a1 sp 0x8, .lbu a2 sp 0x8, .alu .sub a2 x0 a2,
   .aluImm .add a3 x0 0x2]

/-- One limb of the sign extension, from 0x34 to 0x3A. -/
def fiFill : List BInstr := [.sw a1 a2 0x0, .aluImm .add a1 a1 0x4, .aluImm .add a3 a3 0xFFFFFFFF]

def fiMid : List BInstr := [.alu .add a1 x0 sp, .aluImm .add a2 sp 0x8, .aluImm .add a3 x0 0x2]

/-- From 0x50 to 0x5A: the words out, and the frame's release. -/
def fiEpi : List BInstr := [.lw a1 sp 0x8, .lw a2 sp 0xC, .sw a0 a1 0x0, .sw a0 a2 0x4, .aluImm .add sp sp 0x10]

section
set_option maxRecDepth 20000
theorem fiPro_end : blockEnd fromI64Code 0 fiPro = some 0x10 := by decide
theorem fiCp_end1 : blockEnd fromI64Code 0x12 fiCp = some 0x1C := by decide
theorem fiSign_end : blockEnd fromI64Code 0x1E fiSign = some 0x32 := by decide
theorem fiFill_end : blockEnd fromI64Code 0x34 fiFill = some 0x3A := by decide
theorem fiMid_end : blockEnd fromI64Code 0x3C fiMid = some 0x42 := by decide
theorem fiCp_end2 : blockEnd fromI64Code 0x44 fiCp = some 0x4E := by decide
theorem fiEpi_end : blockEnd fromI64Code 0x50 fiEpi = some 0x5A := by decide
end

def fiCpKeep (q : Fin 32) : Bool := q.val ∉ [0, 11, 12, 13, 14]

set_option maxRecDepth 20000 in
theorem fiCp_run {M : Word → BitVec 8} {f : Fin 32 → Word} :
    (runBlock fiCp (M, f)).1 = memStore32 M (f a2 + 0) (memLoad32 M (f a1 + 0)) ∧
    (runBlock fiCp (M, f)).2 a1 = f a1 + 4 ∧ (runBlock fiCp (M, f)).2 a2 = f a2 + 4 ∧
    (runBlock fiCp (M, f)).2 a3 = f a3 + 0xFFFFFFFF ∧
    ∀ q, fiCpKeep q = true → (runBlock fiCp (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, fiCp, upd_app, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
  rotate_left 4
  have h0 : q.val ≠ 0 := fun e => absurd (show fiCpKeep q = false by unfold fiCpKeep; simp [e]) (by rw [hq]; decide)
  simp only [h0, ite_false, pkeep_ne (r := a1) hq rfl, pkeep_ne (r := a2) hq rfl, pkeep_ne (r := a3) hq rfl,
    pkeep_ne (r := a4) hq rfl]
  all_goals first | trivial | rfl

set_option maxRecDepth 20000 in
theorem fiCp_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h11 : (f a1 + 0).toNat % 4 = 0) (h12 : (f a2 + 0).toNat % 4 = 0) (hs : Sep (f a2 + 0) 4 base len) :
    BlockOk base len fiCp (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, fiCp, upd_app, ↓reduceIte, and_true, true_and]
  exact ⟨h11, h12, hs⟩

def fiFillKeep (q : Fin 32) : Bool := q.val ∉ [0, 11, 13]

set_option maxRecDepth 20000 in
theorem fiFill_run {M : Word → BitVec 8} {f : Fin 32 → Word} :
    (runBlock fiFill (M, f)).1 = memStore32 M (f a1 + 0) (f a2) ∧
    (runBlock fiFill (M, f)).2 a1 = f a1 + 4 ∧ (runBlock fiFill (M, f)).2 a3 = f a3 + 0xFFFFFFFF ∧
    ∀ q, fiFillKeep q = true → (runBlock fiFill (M, f)).2 q = f q := by
  simp +decide only [runBlock, BInstr.run, fiFill, upd_app, ↓reduceIte]
  refine ⟨?_, ?_, ?_, fun q hq => ?_⟩
  rotate_left 3
  have h0 : q.val ≠ 0 := fun e => absurd (show fiFillKeep q = false by unfold fiFillKeep; simp [e]) (by rw [hq]; decide)
  simp only [h0, ite_false, pkeep_ne (r := a1) hq rfl, pkeep_ne (r := a3) hq rfl]
  all_goals first | trivial | rfl

/-- **One limb of a copy**, at offset `o` of either copy loop. -/
theorem fi_cp_iter {M : Word → BitVec 8} {P S D : Word} {n : Machine} {i o : Nat}
    (s : St M P n o (reg n)) (hc : CodeIn M P fromI64Code) (hi : i < 2) (hS : S.toNat % 4 = 0) (hD : D.toNat % 4 = 0)
    (hend : blockEnd fromI64Code o fiCp = some (o + 0xA))
    (hbr : fetchRel fromI64Code (o + 0xA) = some (.branch .bne a3 x0 0xFFFFFFF6, 2))
    (hT : BitVec.ofNat 32 (o + 0xA) + 0xFFFFFFF6 = BitVec.ofNat 32 o)
    (hF : BitVec.ofNat 32 (o + 0xA) + 2 = BitVec.ofNat 32 (o + 0xC))
    (sC : Sep (D + BitVec.ofNat 32 (4 * i)) 4 P fromI64Code.length)
    (r11 : reg n a1 = S + BitVec.ofNat 32 (4 * i)) (r12 : reg n a2 = D + BitVec.ofNat 32 (4 * i))
    (r13 : reg n a3 = BitVec.ofNat 32 (2 - i)) :
    ∃ n', Steps n n' ∧
      St (memStore32 M (D + BitVec.ofNat 32 (4 * i)) (memLoad32 M (S + BitVec.ofNat 32 (4 * i))))
        P n' (if i + 1 < 2 then o else o + 0xC) (reg n') ∧
      reg n' a1 = S + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a2 = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' a3 = BitVec.ofNat 32 (2 - (i + 1)) ∧
      ∀ q, fiCpKeep q = true → reg n' q = reg n q := by
  obtain ⟨E1, E11, E12, E13, Ek⟩ := fiCp_run (M := M) (f := reg n)
  obtain ⟨n1, c1, u1⟩ := St.block fiCp s hc hend
    (fiCp_ok (by rw [r11, add_lit_zero]; exact aligned_add hS (by omega))
      (by rw [r12, add_lit_zero]; exact aligned_add hD (by omega)) (by rw [r12, add_lit_zero]; exact sC))
  rw [E1, r12, r11, add_lit_zero, add_lit_zero] at u1
  have hc1 := CodeIn.store32 (v := memLoad32 M (S + BitVec.ofNat 32 (4 * i))) hc sC
  have ea3 : reg n1 a3 = BitVec.ofNat 32 (2 - (i + 1)) := by rw [u1.regs, E13, r13, cnt2_dec i hi]
  have hb : branchTaken .bne (reg n1 a3) (reg n1 x0) = decide (i + 1 < 2) := by
    rw [ea3, u1.self.zero]; exact cnt2_ne i hi
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 a1 = S + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 a2 = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n2 a3 = BitVec.ofNat 32 (2 - (i + 1)) ∧ ∀ q, fiCpKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨by rw [h2, u1.regs, E11, r11, ptr4], by rw [h2, u1.regs, E12, r12, ptr4], by rw [h2, ea3],
      fun q hq => by rw [h2, u1.regs, Ek q hq]⟩
  by_cases hl : i + 1 < 2
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc1 o hbr hT (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 (o + 0xC) hbr hF (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

/-- **One limb of the sign extension**, from 0x34. -/
theorem fi_fill_iter {M : Word → BitVec 8} {P D v : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x34 (reg n)) (hc : CodeIn M P fromI64Code) (hi : i < 2) (hD : D.toNat % 4 = 0)
    (sC : Sep (D + BitVec.ofNat 32 (4 * i)) 4 P fromI64Code.length)
    (r11 : reg n a1 = D + BitVec.ofNat 32 (4 * i)) (r12 : reg n a2 = v) (r13 : reg n a3 = BitVec.ofNat 32 (2 - i)) :
    ∃ n', Steps n n' ∧ St (memStore32 M (D + BitVec.ofNat 32 (4 * i)) v) P n' (if i + 1 < 2 then 0x34 else 0x3C) (reg n') ∧
      reg n' a1 = D + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n' a3 = BitVec.ofNat 32 (2 - (i + 1)) ∧
      ∀ q, fiFillKeep q = true → reg n' q = reg n q := by
  obtain ⟨E1, E11, E13, Ek⟩ := fiFill_run (M := M) (f := reg n)
  obtain ⟨n1, c1, u1⟩ := St.block fiFill s hc fiFill_end (by
    simp +decide only [BlockOk, BInstr.ok, fiFill, and_true]
    rw [r11, add_lit_zero]; exact ⟨aligned_add hD (by omega), sC⟩)
  rw [E1, r11, r12, add_lit_zero] at u1
  have hc1 := CodeIn.store32 (v := v) hc sC
  have ea3 : reg n1 a3 = BitVec.ofNat 32 (2 - (i + 1)) := by rw [u1.regs, E13, r13, cnt2_dec i hi]
  have hb : branchTaken .bne (reg n1 a3) (reg n1 x0) = decide (i + 1 < 2) := by
    rw [ea3, u1.self.zero]; exact cnt2_ne i hi
  have post : ∀ n2 : Machine, (∀ q, reg n2 q = reg n1 q) →
      reg n2 a1 = D + BitVec.ofNat 32 (4 * (i + 1)) ∧ reg n2 a3 = BitVec.ofNat 32 (2 - (i + 1)) ∧
      ∀ q, fiFillKeep q = true → reg n2 q = reg n q := fun n2 h2 => by
    refine ⟨by rw [h2, u1.regs, E11, r11, ptr4], by rw [h2, ea3], fun q hq => by rw [h2, u1.regs, Ek q hq]⟩
  by_cases hl : i + 1 < 2
  · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc1 0x34 fi_at_3a (by decide) (by rw [hb]; exact decide_eq_true hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_left hl]; exact u2.self, post n2 u2.regs⟩
  · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0x3C fi_at_3a (by decide) (by rw [hb]; exact decide_eq_false hl)
    exact ⟨n2, c1.trans (.single d2), by rw [ite_eq_right hl]; exact u2.self, post n2 u2.regs⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `Int<2>::from_i64`**, called with the result at `out` and
an `i64` in `a1` (low word) and `a2` (high word), stores the two words at
`out`. It returns with `sp` and every register but `a1` through `a4` as they
were, and changes no memory outside the 16 bytes below `sp` and the 8 bytes
at `out`. -/
theorem fromI64_correct (m : Machine) {P sp0 out lo hi retAddr : Word}
    (hc : CodeIn m.mem P fromI64Code) (hpc : m.pc = P) (hsp : reg m sp = sp0)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = lo) (ha2 : reg m a2 = hi) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hs4 : sp0.toNat % 4 = 0) (hs16 : 16 ≤ sp0.toNat) (hout : out.toNat % 4 = 0)
    (sFC : Sep (sp0 + 0xFFFFFFF0) 16 P fromI64Code.length) (sOC : Sep out 8 P fromI64Code.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∉ [11, 12, 13, 14] → reg m' q = reg m q) ∧
      memLoad32 m'.mem out = lo ∧ memLoad32 m'.mem (out + 4) = hi ∧
      ∀ x, Sep (sp0 + 0xFFFFFFF0) 16 x 1 → Sep out 8 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hGd⟩ : ∃ G, sp0 + 0xFFFFFFF0 = G := ⟨_, rfl⟩
  rw [hGd] at sFC ⊢
  have hGa : G.toNat % 4 = 0 := by rw [← hGd]; exact aligned_add hs4 (k := 0xFFFFFFF0) (by decide)
  have hGw : G.toNat + 16 = sp0.toNat := by
    rw [← hGd, BitVec.toNat_add]
    have : (0xFFFFFFF0 : Word).toNat = 0xFFFFFFF0 := rfl
    rw [this]; have := sp0.isLt; omega
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have sG : ∀ c l, c + l ≤ 16 → Sep (G + BitVec.ofNat 32 c) l P fromI64Code.length := fun c l h => sFC.sub h
  have aG : ∀ c, c % 4 = 0 → (G + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h => aligned_add hGa h
  have sG0 : Sep G 4 P fromI64Code.length := by have := sG 0 4 (by decide); rwa [add_ofNat_zero] at this
  have sG4 : Sep (G + 4) 4 P fromI64Code.length := sG 4 4 (by decide)
  have sG8 : Sep (G + 8) 4 P fromI64Code.length := sG 8 4 (by decide)
  have sGC : Sep (G + 0xC) 4 P fromI64Code.length := sG 0xC 4 (by decide)
  have g84 : G + 8 + 4 = G + 0xC := by rw [BitVec.add_assoc]; rfl
  have gp4 : G + BitVec.ofNat 32 (4 * 1) = G + 4 := rfl
  have ss : ∀ a b : Nat, a + 4 ≤ b ∨ b + 4 ≤ a → a + 4 ≤ 16 → b + 4 ≤ 16 →
      Sep (G + BitVec.ofNat 32 a) 4 (G + BitVec.ofNat 32 b) 4 := fun a b h ha hb => sep_offsets G h (by omega) (by omega)
  -- the prologue
  obtain ⟨n1, c1, u1⟩ := St.block fiPro s0 hc fiPro_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, fiPro, upd_app, ↓reduceIte, and_true, true_and]
    rw [show aluEval AluOp.add (reg m sp) 0xFFFFFFF0 = G by rw [hsp, ← hGd]; rfl, add_lit_zero]
    exact ⟨⟨hGa, sG0⟩, ⟨aG 4 (by decide), sG4⟩, ⟨aG 8 (by decide), sG8⟩, aG 0xC (by decide), sGC⟩)
  simp only [runBlock, BInstr.run, fiPro] at u1
  simp +decide only [upd_app, ↓reduceIte] at u1
  rw [show aluEval AluOp.add (reg m sp) 0xFFFFFFF0 = G by rw [hsp, ← hGd]; rfl, ha1, ha2, add_lit_zero] at u1
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 (memStore32 (memStore32 (memStore32 m.mem G lo) (G + 4) hi) (G + 8) 0)
      (G + 0xC) 0 = M1 := ⟨_, rfl⟩
  rw [hM1] at u1
  have hc1 : CodeIn M1 P fromI64Code := by
    rw [← hM1]; exact (((hc.store32 sG0).store32 sG4).store32 sG8).store32 sGC
  have fr1 : ∀ x, Sep G 16 x 1 → M1 x = m.mem x := fun x hx => by
    have h0 : Sep G 4 x 1 := by have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    have hC : Sep (G + 0xC) 4 x 1 := hx.sub (c := 0xC) (l := 4) (by decide)
    have h8 : Sep (G + 8) 4 x 1 := hx.sub (c := 8) (l := 4) (by decide)
    have h4 : Sep (G + 4) 4 x 1 := hx.sub (c := 4) (l := 4) (by decide)
    rw [← hM1, memStore32_get_sep hC, memStore32_get_sep h8, memStore32_get_sep h4, memStore32_get_sep h0]
  -- the words at `G` and `G + 4` never change after the prologue
  have lo1 : memLoad32 M1 G = lo := by
    have h4 : Sep (G + 4) 4 G 4 := by have := ss 4 0 (by decide) (by decide) (by decide); rwa [add_ofNat_zero] at this
    have h8 : Sep (G + 8) 4 G 4 := by have := ss 8 0 (by decide) (by decide) (by decide); rwa [add_ofNat_zero] at this
    have hC : Sep (G + 0xC) 4 G 4 := by have := ss 0xC 0 (by decide) (by decide) (by decide); rwa [add_ofNat_zero] at this
    rw [← hM1, memLoad32_store32_sep hC, memLoad32_store32_sep h8, memLoad32_store32_sep h4, memLoad32_store32_same]
  have hi1 : memLoad32 M1 (G + 4) = hi := by
    have h8 : Sep (G + 8) 4 (G + 4) 4 := ss 8 4 (by decide) (by decide) (by decide)
    have hC : Sep (G + 0xC) 4 (G + 4) 4 := ss 0xC 4 (by decide) (by decide) (by decide)
    rw [← hM1, memLoad32_store32_sep hC, memLoad32_store32_sep h8, memLoad32_store32_same]
  /- From here on every store is to `G + 8` or `G + 0xC`. -/
  have keep8 : ∀ {Ma Mb : Word → BitVec 8} (a : Word) (v : Word), (a = G + 8 ∨ a = G + 0xC) →
      memLoad32 Ma G = lo → memLoad32 Ma (G + 4) = hi → (∀ x, Sep G 16 x 1 → Ma x = m.mem x) →
      CodeIn Ma P fromI64Code → Mb = memStore32 Ma a v →
      memLoad32 Mb G = lo ∧ memLoad32 Mb (G + 4) = hi ∧ (∀ x, Sep G 16 x 1 → Mb x = m.mem x) ∧
        CodeIn Mb P fromI64Code := fun a v ha l0 l4 fr cc hb => by
    subst hb
    have sa0 : Sep a 4 G 4 := by
      rcases ha with rfl | rfl
      · have := ss 8 0 (by decide) (by decide) (by decide); rwa [add_ofNat_zero] at this
      · have := ss 0xC 0 (by decide) (by decide) (by decide); rwa [add_ofNat_zero] at this
    have sa4 : Sep a 4 (G + 4) 4 := by
      rcases ha with rfl | rfl
      · exact ss 8 4 (by decide) (by decide) (by decide)
      · exact ss 0xC 4 (by decide) (by decide) (by decide)
    have sac : Sep a 4 P fromI64Code.length := by rcases ha with rfl | rfl <;> assumption
    refine ⟨by rw [memLoad32_store32_sep sa0, l0], by rw [memLoad32_store32_sep sa4, l4], fun x hx => ?_,
      cc.store32 sac⟩
    have hxa : Sep a 4 x 1 := by
      rcases ha with rfl | rfl
      · exact hx.sub (c := 8) (l := 4) (by decide)
      · exact hx.sub (c := 0xC) (l := 4) (by decide)
    rw [memStore32_get_sep hxa, fr x hx]
  have g1 : ∀ q, reg n1 q = _ := u1.regs
  have x13 : reg n1 a3 = 2 := by rw [g1]; simp +decide only [upd_app, ↓reduceIte, aluEval]
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc1 0x12 fi_at_10 (by decide) (by rw [x13, u1.self.zero]; decide)
  have v2 : ∀ q, reg n2 q = reg n1 q := u2.regs
  -- the first copy
  obtain ⟨n3, c3, u3, e11, e12, e13, k3⟩ := fi_cp_iter (i := 0) (o := 0x12) (S := G) (D := G + 8) u2.self hc1
    (by decide) hGa (aG 8 (by decide)) fiCp_end1 fi_at_1c (by decide) (by decide) (by rw [u2_slot0]; exact sG8)
    (by rw [v2, g1]; simp +decide only [upd_app, ↓reduceIte]; exact (BitVec.zero_add _).trans (add_ofNat_zero _).symm)
    (by rw [v2, g1]; simp +decide only [upd_app, ↓reduceIte]; exact (add_ofNat_zero _).symm)
    (by rw [v2, x13]; rfl)
  rw [show (if 0 + 1 < 2 then 0x12 else 0x12 + 0xC : Nat) = 0x12 from rfl, u2_slot0, u2_slot0] at u3
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore32 M1 (G + 8) (memLoad32 M1 G) = M2 := ⟨_, rfl⟩
  rw [hM2] at u3
  obtain ⟨l2, h2, f2, cc2⟩ := keep8 (G + 8) _ (.inl rfl) lo1 hi1 fr1 hc1 hM2.symm
  obtain ⟨n4, c4, u4, -, -, -, k4⟩ := fi_cp_iter (i := 1) (o := 0x12) (S := G) (D := G + 8) u3 cc2 (by decide) hGa
    (aG 8 (by decide)) fiCp_end1 fi_at_1c (by decide) (by decide) (by rw [u2_slot1', g84]; exact sGC) e11 e12 e13
  rw [show (if 1 + 1 < 2 then 0x12 else 0x12 + 0xC : Nat) = 0x1E from rfl, u2_slot1', u2_slot1', g84] at u4
  obtain ⟨M3, hM3⟩ : ∃ M3, memStore32 M2 (G + 0xC) (memLoad32 M2 (G + 4)) = M3 := ⟨_, rfl⟩
  rw [hM3] at u4
  obtain ⟨l3, h3, f3, cc3⟩ := keep8 (G + 0xC) _ (.inr rfl) l2 h2 f2 cc2 hM3.symm
  have k14 : ∀ q, fiCpKeep q = true → reg n4 q = reg n1 q := fun q hq => by rw [k4 q hq, k3 q hq, v2]
  have sp4 : reg n4 sp = G := by rw [k14 sp rfl, g1]; simp +decide only [upd_app, ↓reduceIte]
  -- the sign byte and the fill value
  have sG8b : Sep (G + 8) 1 P fromI64Code.length := sG 8 1 (by decide)
  obtain ⟨n5, c5, u5⟩ := St.block fiSign u4 cc3 fiSign_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, fiSign, upd_app, ↓reduceIte, and_true, true_and]
    rw [sp4]; exact ⟨aG 0xC (by decide), sG8b⟩)
  simp only [runBlock, BInstr.run, fiSign] at u5
  simp +decide only [upd_app, ↓reduceIte] at u5
  rw [sp4] at u5
  obtain ⟨M4, hM4⟩ : ∃ M4, memStore8 M3 (G + 8) (BitVec.extractLsb' 0 8 (aluEval AluOp.srl (memLoad32 M3 (G + 12)) 31)) = M4 :=
    ⟨_, rfl⟩
  rw [hM4] at u5
  have sb0 : Sep (G + 8) 1 G 4 := by
    have := sep_offsets G (c := 8) (n := 1) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  have sb4 : Sep (G + 8) 1 (G + 4) 4 := sep_offsets G (c := 8) (n := 1) (d := 4) (k := 4) (.inr (by decide)) (by decide)
    (by decide)
  have l4 : memLoad32 M4 G = lo := by rw [← hM4, memLoad32_store8_sep sb0, l3]
  have h4 : memLoad32 M4 (G + 4) = hi := by rw [← hM4, memLoad32_store8_sep sb4, h3]
  have f4 : ∀ x, Sep G 16 x 1 → M4 x = m.mem x := fun x hx => by
    have hne : x ≠ G + 8 := fun e => by
      have := hx.point (i := 8) (j := 0) (by decide) (by decide)
      rw [add_ofNat_zero] at this; exact this e.symm
    rw [← hM4, memStore8_ne hne, f3 x hx]
  have cc4 : CodeIn M4 P fromI64Code := by rw [← hM4]; exact cc3.store8 sG8b
  have g5 : ∀ q, reg n5 q = _ := u5.regs
  have x13' : reg n5 a3 = 2 := by rw [g5]; simp +decide only [upd_app, ↓reduceIte, aluEval]
  obtain ⟨n6, d6, u6⟩ := u5.self.notTaken cc4 0x34 fi_at_32 (by decide) (by rw [x13', u5.self.zero]; decide)
  have v6 : ∀ q, reg n6 q = reg n5 q := u6.regs
  obtain ⟨fv, hfv⟩ : ∃ fv, reg n6 a2 = fv := ⟨_, rfl⟩
  -- the sign extension over the copy
  obtain ⟨n7, c7, u7, e11', e13', k7⟩ := fi_fill_iter (i := 0) (D := G + 8) (v := fv) u6.self cc4 (by decide)
    (aG 8 (by decide)) (by rw [u2_slot0]; exact sG8)
    (by rw [v6, g5]; simp +decide only [upd_app, ↓reduceIte]; exact (add_ofNat_zero _).symm) hfv
    (by rw [v6, x13']; rfl)
  rw [show (if 0 + 1 < 2 then 0x34 else 0x3C : Nat) = 0x34 from rfl, u2_slot0] at u7
  obtain ⟨M5, hM5⟩ : ∃ M5, memStore32 M4 (G + 8) fv = M5 := ⟨_, rfl⟩
  rw [hM5] at u7
  obtain ⟨l5, h5, f5, cc5⟩ := keep8 (G + 8) _ (.inl rfl) l4 h4 f4 cc4 hM5.symm
  obtain ⟨n8, c8, u8, -, -, k8⟩ := fi_fill_iter (i := 1) (D := G + 8) (v := fv) u7 cc5 (by decide)
    (aG 8 (by decide)) (by rw [u2_slot1', g84]; exact sGC) e11' (by rw [k7 a2 rfl]; exact hfv) e13'
  rw [show (if 1 + 1 < 2 then 0x34 else 0x3C : Nat) = 0x3C from rfl, u2_slot1', g84] at u8
  obtain ⟨M6, hM6⟩ : ∃ M6, memStore32 M5 (G + 0xC) fv = M6 := ⟨_, rfl⟩
  rw [hM6] at u8
  obtain ⟨l6, h6, f6, cc6⟩ := keep8 (G + 0xC) _ (.inr rfl) l5 h5 f5 cc5 hM6.symm
  have k58 : ∀ q, fiFillKeep q = true → reg n8 q = reg n5 q := fun q hq => by rw [k8 q hq, k7 q hq, v6]
  have k45 : ∀ q, q.val ≠ 0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg n5 q = reg n4 q := fun q h0 h1 h2 h3 => by
    rw [g5]; simp only [upd_app, h0, h1, h2, h3, ite_false]
  have sp8 : reg n8 sp = G := by rw [k58 sp rfl, k45 sp (by decide) (by decide) (by decide) (by decide), sp4]
  -- the second copy, of `n`'s words over the sign extension
  obtain ⟨n9, c9, u9⟩ := St.block fiMid u8 cc6 fiMid_end (by simp [BlockOk, BInstr.ok, fiMid])
  simp only [runBlock, BInstr.run, fiMid] at u9
  simp +decide only [upd_app, ↓reduceIte] at u9
  rw [sp8] at u9
  have g9 : ∀ q, reg n9 q = _ := u9.regs
  have x13'' : reg n9 a3 = 2 := by rw [g9]; simp +decide only [upd_app, ↓reduceIte, aluEval]
  obtain ⟨n10, d10, u10⟩ := u9.self.notTaken cc6 0x44 fi_at_42 (by decide) (by rw [x13'', u9.self.zero]; decide)
  have v10 : ∀ q, reg n10 q = reg n9 q := u10.regs
  obtain ⟨n11, c11, u11, e11'', e12'', e13'', k11⟩ := fi_cp_iter (i := 0) (o := 0x44) (S := G) (D := G + 8) u10.self
    cc6 (by decide) hGa (aG 8 (by decide)) fiCp_end2 fi_at_4e (by decide) (by decide) (by rw [u2_slot0]; exact sG8)
    (by rw [v10, g9]; simp +decide only [upd_app, ↓reduceIte]; exact (BitVec.zero_add _).trans (add_ofNat_zero _).symm)
    (by rw [v10, g9]; simp +decide only [upd_app, ↓reduceIte]; exact (add_ofNat_zero _).symm)
    (by rw [v10, x13'']; rfl)
  rw [show (if 0 + 1 < 2 then 0x44 else 0x44 + 0xC : Nat) = 0x44 from rfl, u2_slot0, u2_slot0, l6] at u11
  obtain ⟨M7, hM7⟩ : ∃ M7, memStore32 M6 (G + 8) lo = M7 := ⟨_, rfl⟩
  rw [hM7] at u11
  obtain ⟨l7, h7, f7, cc7⟩ := keep8 (G + 8) _ (.inl rfl) l6 h6 f6 cc6 hM7.symm
  obtain ⟨n12, c12, u12, -, -, -, k12⟩ := fi_cp_iter (i := 1) (o := 0x44) (S := G) (D := G + 8) u11 cc7 (by decide)
    hGa (aG 8 (by decide)) fiCp_end2 fi_at_4e (by decide) (by decide) (by rw [u2_slot1', g84]; exact sGC)
    e11'' e12'' e13''
  rw [show (if 1 + 1 < 2 then 0x44 else 0x44 + 0xC : Nat) = 0x50 from rfl, u2_slot1', u2_slot1', g84, h7] at u12
  obtain ⟨M8, hM8⟩ : ∃ M8, memStore32 M7 (G + 0xC) hi = M8 := ⟨_, rfl⟩
  rw [hM8] at u12
  obtain ⟨-, -, f8, cc8⟩ := keep8 (G + 0xC) _ (.inr rfl) l7 h7 f7 cc7 hM8.symm
  have m8 : memLoad32 M8 (G + 8) = lo := by
    have h : Sep (G + 0xC) 4 (G + 8) 4 := ss 0xC 8 (by decide) (by decide) (by decide)
    rw [← hM8, memLoad32_store32_sep h, ← hM7, memLoad32_store32_same]
  have mC : memLoad32 M8 (G + 0xC) = hi := by rw [← hM8, memLoad32_store32_same]
  have k812 : ∀ q, fiCpKeep q = true → reg n12 q = reg n9 q := fun q hq => by rw [k12 q hq, k11 q hq, v10]
  have k89 : ∀ q, q.val ≠ 0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg n9 q = reg n8 q := fun q h0 h1 h2 h3 => by
    rw [g9]; simp only [upd_app, h0, h1, h2, h3, ite_false]
  have kAll : ∀ q, q.val ∉ [0, 2, 11, 12, 13, 14] → reg n12 q = reg m q := fun q hq => by
    have ne : ∀ w : Fin 32, w.val ∈ [0, 2, 11, 12, 13, 14] → q ≠ w := fun w hw e => hq (e ▸ hw)
    have h0 : q.val ≠ 0 := fun e => hq (by rw [e]; decide)
    have kc : fiCpKeep q = true := by
      unfold fiCpKeep; simp only [List.mem_cons, List.mem_nil_iff, or_false, decide_eq_true_eq] at hq ⊢; omega
    have kf : fiFillKeep q = true := by
      unfold fiFillKeep; simp only [List.mem_cons, List.mem_nil_iff, or_false, decide_eq_true_eq] at hq ⊢; omega
    rw [k812 q kc, k89 q h0 (ne a1 (by decide)) (ne a2 (by decide)) (ne a3 (by decide)), k58 q kf,
      k45 q h0 (ne a1 (by decide)) (ne a2 (by decide)) (ne a3 (by decide)), k14 q kc, g1]
    simp only [upd_app, h0, ne sp (by decide), ne a1 (by decide), ne a2 (by decide), ne a3 (by decide), ite_false]
  have sp12 : reg n12 sp = G := by
    rw [k812 sp rfl, k89 sp (by decide) (by decide) (by decide) (by decide), sp8]
  have r10 : reg n12 a0 = out := by rw [kAll a0 (by decide), ha0]
  -- the epilogue
  have sO0 : Sep out 4 P fromI64Code.length := by
    have := sOC.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
  have sO4 : Sep (out + 4) 4 P fromI64Code.length := sOC.sub (c := 4) (l := 4) (by decide)
  obtain ⟨n13, c13, u13⟩ := St.block fiEpi u12 cc8 fiEpi_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, fiEpi, upd_app, ↓reduceIte, and_true]
    rw [sp12, r10, add_lit_zero]
    exact ⟨aG 8 (by decide), aG 0xC (by decide), ⟨hout, sO0⟩, aligned_add hout (k := 4) (by decide), sO4⟩)
  simp only [runBlock, BInstr.run, fiEpi] at u13
  simp +decide only [upd_app, ↓reduceIte] at u13
  rw [sp12, r10, add_lit_zero, m8, show G + 12 = G + 0xC from rfl, mC] at u13
  have hc13 := (cc8.store32 (v := lo) sO0).store32 (v := hi) sO4
  obtain ⟨n14, d14, pc14, mem14, regs14⟩ := u13.jalr hc13 fi_at_5a
  have spF : G + 0x10 = sp0 := by rw [← hGd, BitVec.add_assoc]; exact BitVec.add_zero _
  have sOO : Sep (out + 4) 4 out 4 := by
    have := sep_offsets out (c := 4) (n := 4) (d := 0) (k := 4) (.inr (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  refine ⟨n14, c1.trans (.cons d2 (c3.trans (c4.trans (c5.trans (.cons d6 (c7.trans (c8.trans (c9.trans
    (.cons d10 (c11.trans (c12.trans (c13.trans (.single d14))))))))))))), ?_, ?_, fun q hq => ?_, ?_, ?_,
    fun x hx ho => ?_⟩
  · rw [pc14]; simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero, kAll ra (by decide), hra, hret]
  · rw [regs14]; simp +decide only [upd_app, ↓reduceIte]; exact spF
  · by_cases hsq : q = sp
    · subst hsq; rw [regs14, hsp]; simp +decide only [upd_app, ↓reduceIte]; exact spF
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; exact (show reg n14 0 = 0 from rfl).trans (show reg m 0 = 0 from rfl).symm
    have ne : ∀ w : Fin 32, w.val ∈ [11, 12, 13, 14] → q ≠ w := fun w hw e => hq (e ▸ hw)
    rw [regs14]
    simp only [upd_app, h0, hsq, ne a1 (by decide), ne a2 (by decide), ite_false]
    exact kAll q (by
      intro hm; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm hq
      have : q.val ≠ 2 := fun e => hsq (Fin.ext e)
      omega)
  · rw [mem14, memLoad32_store32_sep sOO, memLoad32_store32_same]
  · rw [mem14, memLoad32_store32_same]
  · have h0 : Sep out 4 x 1 := by have := ho.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this
    have h4 : Sep (out + 4) 4 x 1 := ho.sub (c := 4) (l := 4) (by decide)
    rw [mem14, memStore32_get_sep h4, memStore32_get_sep h0, f8 x hx]

end C3.RV32
