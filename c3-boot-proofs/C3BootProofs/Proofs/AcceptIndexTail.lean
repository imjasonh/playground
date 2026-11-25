import C3BootProofs.Proofs.AcceptIndexLoop

/-!
# `boot_main`'s first closure: the index stage finds the trusted root

From 0x440 the index stage asks `Index::doc` for the last document, the
trusted root. It leaves with code 6, 0, or 1 when the document's end
overflows, passes the part's end, or stops short of it. Then it copies the
lengths and the count to `sp + 0x244` through two buffers, and reaches 0x4E4.
-/

namespace C3.RV32.Ac

open C3 C3.Image C3.RV32.P3

set_option maxRecDepth 100000

theorem acx_takeS : ∀ (l : List Nat) (i : Nat), i < l.length → (l.take (i + 1)).sum = (l.take i).sum + l.getD i 0
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | a :: l, 0, _ => by simp only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil,
      List.getD_cons_zero, Nat.add_zero, Nat.zero_add]
  | a :: l, i + 1, h => by
    rw [List.length_cons] at h
    rw [List.take_succ_cons, List.sum_cons, List.take_succ_cons, List.sum_cons, List.getD_cons_succ,
      acx_takeS l i (by omega), Nat.add_assoc]

theorem acx_ld {M M' : Word → BitVec 8} {a a' : Word}
    (h : ∀ j, j < 4 → M (a + BitVec.ofNat 32 j) = M' (a' + BitVec.ofNat 32 j)) :
    memLoad32 M a = memLoad32 M' a' := by
  have h0 := h 0 (by decide)
  rw [add_ofNat_zero, add_ofNat_zero] at h0
  unfold memLoad32
  rw [show (1 : Word) = BitVec.ofNat 32 1 from rfl, show (2 : Word) = BitVec.ofNat 32 2 from rfl,
    show (3 : Word) = BitVec.ofNat 32 3 from rfl, h0, h 1 (by decide), h 2 (by decide), h 3 (by decide)]

/-- The part's `count + 2` lengths. -/
abbrev acxLs (P : AcxP) (c : Nat) : List Nat := acxLens (acxTuf P) 8 (c + 2)

/-- Where the trusted root starts in the part. -/
abbrev acxO (P : AcxP) (c : Nat) : Nat := 8 + 4 * (c + 2) + ((acxLs P c).take (c + 1)).sum

/-- The trusted root's length. -/
abbrev acxLt (P : AcxP) (c : Nat) : Nat := (acxLs P c).getD (c + 1) 0

theorem acx_lsum {P : AcxP} {c : Nat}
    (ok : ∀ i, i < c + 2 → 1 ≤ acxW (acxTuf P) (8 + 4 * i) ∧ acxW (acxTuf P) (8 + 4 * i) ≤ 0x2800) :
    (acxLs P c).sum ≤ (c + 2) * 0x2800 :=
  acx_lens_sum _ 8 (c + 2) fun j hj => (ok j hj).2

theorem acx_osum {P : AcxP} {c : Nat} :
    acxO P c + acxLt P c = 8 + 4 * (c + 2) + (acxLs P c).sum := by
  have h := acx_takeS (acxLs P c) (c + 1) (by rw [acx_lens_length]; omega)
  rw [show c + 1 + 1 = c + 2 by omega, List.take_of_length_le (by rw [acx_lens_length]; exact Nat.le_refl _)] at h
  rw [acxO, acxLt, h, Nat.add_assoc]

/-- The state at 0x4E4. -/
structure AcxS4 (P : AcxP) (c : Nat) (n : Machine) : Prop where
  st : St n.mem AC n 0x4E4 (reg n)
  ac : AcxC P n
  s1 : reg n (9 : Fin 32) = P.B + BitVec.ofNat 32 0x4D60
  w30 : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x3A80) = 0x6800 + memLoad32 P.n0.mem (P.B + BitVec.ofNat 32 0x3A84)
  ro : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x52B4) = BitVec.ofNat 32 (acxO P c)
  rl : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x52B8) = BitVec.ofNat 32 (acxLt P c)
  hol : acxO P c + acxLt P c = (reg P.n0 (23 : Fin 32)).toNat
  cnt : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x3D9C) = BitVec.ofNat 32 c
  idx : ∀ i, i < c + 2 →
    (memLoad32 n.mem (P.B + BitVec.ofNat 32 (0x3C94 + 4 * i))).toNat = acxW (acxTuf P) (8 + 4 * i)
  ok : ∀ i, i < c + 2 → 1 ≤ acxW (acxTuf P) (8 + 4 * i) ∧ acxW (acxTuf P) (8 + 4 * i) ≤ 0x2800
  hc : c ≤ 64
  hlen : 8 + (4 * c + 8) ≤ (reg P.n0 (23 : Fin 32)).toNat
  hL : (reg P.n0 (23 : Fin 32)).toNat ≤ 0x60000
  f0 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 0)).toNat = 0x43
  f1 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 1)).toNat = 0x33
  f2 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 2)).toNat = 0x54
  f3 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 3)).toNat = 0x55
  fv : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 4)).toNat +
    256 * (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 5)).toNat = 2
  fc : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 6)).toNat +
    256 * (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 7)).toNat = c

/-- From 0x440: ask for the trusted root's offset and length. -/
def acxT1 : List BInstr :=
  [.aluImm .add a2 (18 : Fin 32) 0x1, .lui a0 0x2000, .aluImm .add a0 a0 0xFFFFF860, .alu .add a0 a0 sp,
   .lui a1 0x2000, .aluImm .add a1 a1 0xFFFFFED0, .alu .add a1 a1 sp]

theorem acxT1_end : blockEnd bootMainClosure0Code 0x440 acxT1 = some 0x454 := by decide

/-- From 0x45C: load the result's tag. -/
def acxT2 : List BInstr := [.lbu a0 (26 : Fin 32) 0x550]

theorem acxT2_end : blockEnd bootMainClosure0Code 0x45C acxT2 = some 0x460 := by decide

/-- From 0x468: load the offset and the length, and add them. -/
def acxT3 : List BInstr :=
  [.lui a0 0x1000, .aluImm .add a0 a0 0x310, .alu .add a1 sp a0, .lw a0 a1 0x554, .lui a2 0x1000,
   .aluImm .add a2 a2 0x310, .alu .add (9 : Fin 32) sp a2, .lw a1 a1 0x558, .alu .add a0 a0 a1]

theorem acxT3_end : blockEnd bootMainClosure0Code 0x468 acxT3 = some 0x486 := by decide

/-- From 0x49E: copy the lengths to `sp + 0x1872`. -/
def acxT4 : List BInstr :=
  [.lui a0 0x2000, .aluImm .add a0 a0 0xFFFFF872, .alu .add (18 : Fin 32) sp a0, .lui a0 0x2000,
   .aluImm .add a0 a0 0xFFFFFED0, .alu .add a1 sp a0, .aluImm .add a2 x0 0x10C, .alu .add a0 x0 (18 : Fin 32)]

theorem acxT4_end : blockEnd bootMainClosure0Code 0x49E acxT4 = some 0x4B8 := by decide

/-- From 0x4C0: then to `sp + 0x352`. -/
def acxT5 : List BInstr :=
  [.aluImm .add (8 : Fin 32) sp 0x352, .aluImm .add a2 x0 0x10C, .alu .add a0 x0 (8 : Fin 32),
   .alu .add a1 x0 (18 : Fin 32)]

theorem acxT5_end : blockEnd bootMainClosure0Code 0x4C0 acxT5 = some 0x4CC := by decide

/-- From 0x4D4: then to `sp + 0x244`. -/
def acxT6 : List BInstr := [.aluImm .add a0 sp 0x244, .aluImm .add a2 x0 0x10C, .alu .add a1 x0 (8 : Fin 32)]

theorem acxT6_end : blockEnd bootMainClosure0Code 0x4D4 acxT6 = some 0x4DC := by decide

/-- From 0x492 and 0x49A: the codes 0 and 1. -/
def acxC0 : List BInstr := [.aluImm .add a0 x0 0x0]

theorem acxC0_end : blockEnd bootMainClosure0Code 0x492 acxC0 = some 0x494 := by decide

def acxC1 : List BInstr := [.aluImm .add a0 x0 0x1]

theorem acxC1_end : blockEnd bootMainClosure0Code 0x49A acxC1 = some 0x49C := by decide

theorem acx_c0 {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) (s : St n.mem AC n 0x492 (reg n))
    {Q : Machine → Prop} : AcxTo P n Q := by
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := s.block acxC0 (A.code K) acxC0_end ⟨trivial, trivial⟩
  have k1 : ∀ q, acxL q = true → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [acxC0]; revert hq; revert q; decide)]
  have A1 : AcxC P n1 := A.next k1 (fun x _ _ => by rw [u1.mem]; rfl)
  have t1 : St n1.mem AC n1 0x494 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  obtain ⟨n2, e2, t2⟩ := t1.jump (A1.code K) ac_at_494 (off' := 0x434) (by decide) (by rw [t1.pc]; decide)
  refine AcxTo.pre (c1.trans (.single e2)) (acx_exit K (A1.next (fun q _ => by rw [t2.regs]) (fun x _ _ => by
    rw [t2.mem])) ⟨t2.pc, rfl, fun _ => rfl⟩ (c := 0) ?_ (.inl (by decide)))
  rw [t2.regs, u1.regs]; simp +decide only [runBlock, BInstr.run, acxC0, upd, ↓reduceIte, aluEval, hz]

theorem acx_c1 {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) (s : St n.mem AC n 0x49A (reg n))
    {Q : Machine → Prop} : AcxTo P n Q := by
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := s.block acxC1 (A.code K) acxC1_end ⟨trivial, trivial⟩
  have k1 : ∀ q, acxL q = true → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [acxC1]; revert hq; revert q; decide)]
  have A1 : AcxC P n1 := A.next k1 (fun x _ _ => by rw [u1.mem]; rfl)
  have t1 : St n1.mem AC n1 0x49C (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  obtain ⟨n2, e2, t2⟩ := t1.jump (A1.code K) ac_at_49c (off' := 0x434) (by decide) (by rw [t1.pc]; decide)
  refine AcxTo.pre (c1.trans (.single e2)) (acx_exit K (A1.next (fun q _ => by rw [t2.regs]) (fun x _ _ => by
    rw [t2.mem])) ⟨t2.pc, rfl, fun _ => rfl⟩ (c := 1) ?_ (.inl (by decide)))
  rw [t2.regs, u1.regs]; simp +decide only [runBlock, BInstr.run, acxC1, upd, ↓reduceIte, aluEval, hz]

/-- The state at 0x49E: the trusted root ends where the part does. -/
structure AcxS5 (P : AcxP) (c : Nat) (n : Machine) : Prop where
  st : St n.mem AC n 0x49E (reg n)
  ac : AcxC P n
  s1 : reg n (9 : Fin 32) = P.B + BitVec.ofNat 32 0x4D60
  w30 : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x3A80) = 0x6800 + memLoad32 P.n0.mem (P.B + BitVec.ofNat 32 0x3A84)
  ro : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x52B4) = BitVec.ofNat 32 (acxO P c)
  rl : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x52B8) = BitVec.ofNat 32 (acxLt P c)
  hol : acxO P c + acxLt P c = (reg P.n0 (23 : Fin 32)).toNat
  cnt : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x5A28) = BitVec.ofNat 32 c
  idx : ∀ i, i < c + 2 →
    (memLoad32 n.mem (P.B + BitVec.ofNat 32 (0x5920 + 4 * i))).toNat = acxW (acxTuf P) (8 + 4 * i)
  ok : ∀ i, i < c + 2 → 1 ≤ acxW (acxTuf P) (8 + 4 * i) ∧ acxW (acxTuf P) (8 + 4 * i) ≤ 0x2800
  hc : c ≤ 64
  hlen : 8 + (4 * c + 8) ≤ (reg P.n0 (23 : Fin 32)).toNat
  hL : (reg P.n0 (23 : Fin 32)).toNat ≤ 0x60000
  f0 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 0)).toNat = 0x43
  f1 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 1)).toNat = 0x33
  f2 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 2)).toNat = 0x54
  f3 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 3)).toNat = 0x55
  fv : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 4)).toNat +
    256 * (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 5)).toNat = 2
  fc : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 6)).toNat +
    256 * (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 7)).toNat = c

set_option maxHeartbeats 4000000 in
/-- From 0x440 to 0x49E: find the trusted root and check that it ends the
part. -/
theorem acx_t1 {P : AcxP} (K : AcxK P) {c : Nat} {n : Machine} (S : AcxS3 P c n) :
    AcxTo P n (AcxS5 P c) := by
  have F := K.F
  have hFl := F.lo; have hFh := F.hi
  have hc := S.hc
  have A := S.ac
  have hz := S.st.zero
  have rsp := A.rsp K
  obtain ⟨n1, c1, t1, A1, m1, g1⟩ := acx_blk K A S.st acxT1 acxT1_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl (by decide)
  have e1 : ∀ q, acxS q = true → reg n1 q = reg n q := fun q hq => by
    rw [g1, runBlock_reg _ _ _ q hz (by simp only [acxT1]; revert hq; revert q; decide)]
  have ha0 : reg n1 a0 = P.B + BitVec.ofNat 32 0x52B0 := by
    rw [g1]; simp +decide only [runBlock, BInstr.run, acxT1, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    exact acx_k' rsp _ (by decide)
  have ha1 : reg n1 a1 = P.B + BitVec.ofNat 32 0x5920 := by
    rw [g1]; simp +decide only [runBlock, BInstr.run, acxT1, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    exact acx_k' rsp _ (by decide)
  have ha2 : reg n1 a2 = BitVec.ofNat 32 c + 1 := by
    rw [g1]; simp +decide only [runBlock, BInstr.run, acxT1, upd, ↓reduceIte, aluEval]
    rw [S.s2]
  obtain ⟨n2, c2, t2, A2, k2, fr2, out2⟩ := acx_ctid K A1 t1 ac_at_454 ac_at_458 (by decide) (by decide)
    ha0 ha1 ha2
  have hsum := acx_lsum S.ok
  have hS : tufIndexDocSpec n1.mem (P.B + BitVec.ofNat 32 0x5920) (BitVec.ofNat 32 c + 1).toNat =
      .ok (acxO P c, acxLt P c) := by
    rw [m1, show (BitVec.ofNat 32 c + 1).toNat = c + 1 by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]; omega]
    have h := tufIndexDocSpec_ok (M := n.mem) (idx := P.B + BitVec.ofNat 32 0x5920) (lens := acxLs P c)
      (by rw [acx_ao _ 0x5920 0x5A28 0x108 (by decide) (by decide), S.cnt, acx_toNat_ofNat (by omega),
        acx_lens_length])
      (by rw [acx_lens_length]; omega)
      (fun j hj => by
        rw [acx_lens_length] at hj
        unfold idxLen
        rw [add_ofNat_assoc, S.idx j hj, acx_lens_getD _ _ _ _ hj])
      (by rw [acx_lens_length]; omega) (i := c + 1) (by rw [acx_lens_length]; omega)
    rw [acx_lens_length] at h
    exact h
  rw [hS] at out2
  obtain ⟨o0, o4, o8⟩ := out2
  rw [acx_ao _ 0x52B0 0x52B4 4 (by decide) (by decide)] at o4
  rw [acx_ao _ 0x52B0 0x52B8 8 (by decide) (by decide)] at o8
  have r2 : ∀ q, acxS q = true → reg n2 q = reg n q := fun q hq => (k2 q hq).trans (e1 q hq)
  have m2 : ∀ e, e + 4 ≤ 0x5A70 → (0x52BC ≤ e ∨ e + 4 ≤ 0x52B0) →
      memLoad32 n2.mem (P.B + BitVec.ofNat 32 e) = memLoad32 n.mem (P.B + BitVec.ofNat 32 e) := fun e h1 h2 => by
    rw [← m1]
    exact acx_wz F h1 fun x l1 l2 => fr2 x (acx_sepR F (by decide) (by omega))
  have hz2 := t2.zero
  obtain ⟨n3, c3, t3, A3, m3, g3⟩ := acx_blk K A2 t2 acxT2 acxT2_end ⟨trivial, trivial⟩ rfl (by decide)
  have a03 : reg n3 a0 = 0 := by
    rw [g3]; simp +decide only [runBlock, BInstr.run, acxT2, upd, ↓reduceIte]
    rw [r2 _ (by decide), S.s10, acx_ao _ 0x4D60 0x52B0 0x550 (by decide) (by decide), o0]; rfl
  obtain ⟨n4, e4, t4⟩ := t3.taken (A3.code K) 0x468 ac_at_460 (by decide) (acx_beq_t (by rw [a03, t3.zero]))
  have A4 := A3.st t4
  have t4' := acx_st t4
  have hz4 := t4'.zero
  have m4 : n4.mem = n2.mem := by rw [t4.mem, m3]
  have r4 : ∀ q, acxS q = true → reg n4 q = reg n q := fun q hq => by
    rw [t4.regs, g3, runBlock_reg _ _ _ q hz2 (by simp only [acxT2]; revert hq; revert q; decide), r2 q hq]
  have rsp4 := A4.rsp K
  obtain ⟨n5, c5, t5, A5, m5, g5⟩ := acx_blk K A4 t4' acxT3 acxT3_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acxT3]
    simp +decide only [upd, ↓reduceIte, and_true, true_and, aluEval, BitVec.reduceAdd]
    rw [acx_k rsp4 _ (c := 0x4D60) (by decide), acx_ao _ 0x4D60 0x52B4 0x554 (by decide) (by decide),
      acx_ao _ 0x4D60 0x52B8 0x558 (by decide) (by decide)]
    exact ⟨acx_al F (by decide) (by decide), acx_al F (by decide) (by decide)⟩) rfl (by decide)
  have s15 : reg n5 (9 : Fin 32) = P.B + BitVec.ofNat 32 0x4D60 := by
    rw [g5]; simp +decide only [runBlock, BInstr.run, acxT3, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    exact acx_k rsp4 _ (by decide)
  have l4 : memLoad32 n4.mem (P.B + BitVec.ofNat 32 0x52B4) = BitVec.ofNat 32 (acxO P c) := by rw [m4, o4]
  have l8 : memLoad32 n4.mem (P.B + BitVec.ofNat 32 0x52B8) = BitVec.ofNat 32 (acxLt P c) := by rw [m4, o8]
  have a15 : reg n5 a1 = BitVec.ofNat 32 (acxLt P c) := by
    rw [g5]; simp +decide only [runBlock, BInstr.run, acxT3, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    rw [acx_k rsp4 _ (c := 0x4D60) (by decide), acx_ao _ 0x4D60 0x52B8 0x558 (by decide) (by decide), l8]
  have a05 : reg n5 a0 = BitVec.ofNat 32 (acxO P c) + BitVec.ofNat 32 (acxLt P c) := by
    rw [g5]; simp +decide only [runBlock, BInstr.run, acxT3, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    rw [acx_k rsp4 _ (c := 0x4D60) (by decide), acx_ao _ 0x4D60 0x52B8 0x558 (by decide) (by decide), l8,
      acx_ao _ 0x4D60 0x52B4 0x554 (by decide) (by decide), l4]
  have hol := acx_osum (P := P) (c := c)
  have hb : acxO P c + acxLt P c < 2 ^ 32 := by omega
  have hv : (BitVec.ofNat 32 (acxO P c) + BitVec.ofNat 32 (acxLt P c)).toNat = acxO P c + acxLt P c := by
    rw [BitVec.toNat_add, acx_toNat_ofNat (by omega), acx_toNat_ofNat (by omega)]; omega
  have s75 : reg n5 (23 : Fin 32) = reg P.n0 (23 : Fin 32) := A5.kl _ (by decide)
  obtain ⟨n6, e6, t6⟩ := t5.taken (A5.code K) 0x48E ac_at_486 (by decide)
    (acx_bgeu_t (by rw [a05, a15, hv, acx_toNat_ofNat (by omega)]; omega))
  have A6 := A5.st t6
  have t6' := acx_st t6
  have pre := c1.trans (c2.trans (c3.trans ((Steps.single e4).trans (c5.trans (.single e6)))))
  have r6 : ∀ q, reg n6 q = reg n5 q := fun q => t6.regs q
  by_cases h1 : (reg P.n0 (23 : Fin 32)).toNat < acxO P c + acxLt P c
  · obtain ⟨n7, e7, t7⟩ := t6'.notTaken (A6.code K) 0x492 ac_at_48e (by decide)
      (acx_bgeu_f (by rw [r6, r6, s75, a05, hv]; exact h1))
    exact AcxTo.pre (pre.trans (.single e7)) (acx_c0 K (A6.st t7) (acx_st t7))
  obtain ⟨n7, e7, t7⟩ := t6'.taken (A6.code K) 0x496 ac_at_48e (by decide)
    (acx_bgeu_t (by rw [r6, r6, s75, a05, hv]; omega))
  have A7 := A6.st t7
  have t7' := acx_st t7
  have r7 : ∀ q, reg n7 q = reg n5 q := fun q => (t7.regs q).trans (r6 q)
  by_cases h2 : acxO P c + acxLt P c < (reg P.n0 (23 : Fin 32)).toNat
  · obtain ⟨n8, e8, t8⟩ := t7'.notTaken (A7.code K) 0x49A ac_at_496 (by decide)
      (acx_bgeu_f (by rw [r7, r7, s75, a05, hv]; exact h2))
    exact AcxTo.pre (pre.trans ((Steps.single e7).trans (.single e8))) (acx_c1 K (A7.st t8) (acx_st t8))
  obtain ⟨n8, e8, t8⟩ := t7'.taken (A7.code K) 0x49E ac_at_496 (by decide)
    (acx_bgeu_t (by rw [r7, r7, s75, a05, hv]; omega))
  have mm : n8.mem = n2.mem := by rw [t8.mem, t7.mem, t6.mem, m5, m4]
  have M : ∀ e, e + 4 ≤ 0x5A70 → (0x52BC ≤ e ∨ e + 4 ≤ 0x52B0) →
      memLoad32 n8.mem (P.B + BitVec.ofNat 32 e) = memLoad32 n.mem (P.B + BitVec.ofNat 32 e) := fun e h1 h2 => by
    rw [mm]; exact m2 e h1 h2
  refine ⟨n8, pre.trans ((Steps.single e7).trans (.single e8)), .inr ⟨acx_st t8, A7.st t8,
    by rw [t8.regs, r7]; exact s15, by rw [M _ (by decide) (by decide)]; exact S.w30, by rw [mm]; exact o4,
    by rw [mm]; exact o8, by omega, by rw [M _ (by decide) (by decide)]; exact S.cnt,
    fun i hi => by rw [M _ (by omega) (by omega)]; exact S.idx i hi,
    S.ok, S.hc, S.hlen, S.hL, S.f0, S.f1, S.f2, S.f3, S.fv, S.fc⟩⟩

theorem acx_z0 (x : Word) : (0 : Word) + x = x := BitVec.zero_add x

theorem acx_cpL {B : Word} (F : Fr B 0x5A70) {M M' : Word → BitVec 8} {d c N : Nat}
    (fr : ∀ x : Word, (x.toNat < B.toNat + 0x3A40 ∨ B.toNat + 0x3A50 ≤ x.toNat) →
      M' x = copyBytes M (B + BitVec.ofNat 32 d) (B + BitVec.ofNat 32 c) N x)
    (hd1 : 0x3A50 ≤ d) (hd2 : d + N ≤ 0x5A70) {e e' k : Nat} (he : e = d + k) (he' : e' = c + k)
    (hk : k + 4 ≤ N) :
    memLoad32 M' (B + BitVec.ofNat 32 e) = memLoad32 M (B + BitVec.ofNat 32 e') := by
  have hFh := F.hi
  subst he he'
  refine acx_ld fun j hj => ?_
  simp only [add_ofNat_assoc]
  rw [fr _ (by rw [F.at _ (by omega)]; omega), Nat.add_assoc d, ← add_ofNat_assoc B d,
    copyBytes_in (by omega) (by omega), add_ofNat_assoc, Nat.add_assoc c]

theorem acx_cpO {B : Word} (F : Fr B 0x5A70) {M M' : Word → BitVec 8} {d c N : Nat}
    (fr : ∀ x : Word, (x.toNat < B.toNat + 0x3A40 ∨ B.toNat + 0x3A50 ≤ x.toNat) →
      M' x = copyBytes M (B + BitVec.ofNat 32 d) (B + BitVec.ofNat 32 c) N x)
    (hd2 : d + N ≤ 0x5A70) {e : Nat} (he : e + 4 ≤ 0x5A70) (h1 : e + 4 ≤ 0x3A40 ∨ 0x3A50 ≤ e)
    (h2 : e + 4 ≤ d ∨ d + N ≤ e) :
    memLoad32 M' (B + BitVec.ofNat 32 e) = memLoad32 M (B + BitVec.ofNat 32 e) :=
  acx_wz F he fun x l1 l2 => by
    rw [fr x (by omega), copyBytes_sep (acx_sepR F hd2 (by omega)) (Nat.le_refl _)]

set_option maxHeartbeats 4000000 in
/-- From 0x49E to 0x4E4: copy the lengths and the count to `sp + 0x244`. -/
theorem acx_t2 {P : AcxP} (K : AcxK P) {c : Nat} {n : Machine} (S : AcxS5 P c n) :
    AcxTo P n (AcxS4 P c) := by
  have F := K.F
  have hFl := F.lo; have hFh := F.hi
  have hc := S.hc
  have A := S.ac
  have hz := S.st.zero
  have rsp := A.rsp K
  obtain ⟨n1, c1, t1, A1, m1, g1⟩ := acx_blk K A S.st acxT4 acxT4_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl (by decide)
  have r1 : ∀ q, acxS q = true → q ≠ (18 : Fin 32) → reg n1 q = reg n q := fun q hq h => by
    rw [g1, runBlock_reg _ _ _ q hz (by simp only [acxT4]; revert hq h; revert q; decide)]
  have s21 : reg n1 (18 : Fin 32) = P.B + BitVec.ofNat 32 0x52C2 := by
    rw [g1]; simp +decide only [runBlock, BInstr.run, acxT4, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    exact acx_k rsp _ (by decide)
  have a01 : reg n1 a0 = P.B + BitVec.ofNat 32 0x52C2 := by
    rw [g1]; simp +decide only [runBlock, BInstr.run, acxT4, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    rw [acx_z0]; exact acx_k rsp _ (by decide)
  have a11 : reg n1 a1 = P.B + BitVec.ofNat 32 0x5920 := by
    rw [g1]; simp +decide only [runBlock, BInstr.run, acxT4, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    exact acx_k rsp _ (by decide)
  have a21 : reg n1 a2 = BitVec.ofNat 32 0x10C := by
    rw [g1]; simp +decide only [runBlock, BInstr.run, acxT4, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
  obtain ⟨n2, c2, t2, A2, k2, fr2⟩ := acx_cmemcpy K A1 t1 ac_at_4b8 ac_at_4bc (by decide) (by decide)
    (c := 0x5920) (d := 0x52C2) (N := 0x10C) (by decide) (by decide) (by decide) (by decide) (by decide)
    a01 a11 a21
  have hz2 := t2.zero
  have rsp2 := A2.rsp K
  obtain ⟨n3, c3, t3, A3, m3, g3⟩ := acx_blk K A2 t2 acxT5 acxT5_end
    ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl (by decide)
  have r3 : ∀ q, acxS q = true → q ≠ (8 : Fin 32) → q ≠ (18 : Fin 32) → reg n3 q = reg n q := fun q hq h8 h18 => by
    rw [g3, runBlock_reg _ _ _ q hz2 (by simp only [acxT5]; revert hq h8; revert q; decide), k2 q hq, r1 q hq h18]
  have s03 : reg n3 (8 : Fin 32) = P.B + BitVec.ofNat 32 0x3DA2 := by
    rw [g3]; simp +decide only [runBlock, BInstr.run, acxT5, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    exact acx_k rsp2 _ (by decide)
  have a03 : reg n3 a0 = P.B + BitVec.ofNat 32 0x3DA2 := by
    rw [g3]; simp +decide only [runBlock, BInstr.run, acxT5, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    rw [acx_z0]; exact acx_k rsp2 _ (by decide)
  have a13 : reg n3 a1 = P.B + BitVec.ofNat 32 0x52C2 := by
    rw [g3]; simp +decide only [runBlock, BInstr.run, acxT5, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    rw [acx_z0, k2 _ (by decide), s21]
  have a23 : reg n3 a2 = BitVec.ofNat 32 0x10C := by
    rw [g3]; simp +decide only [runBlock, BInstr.run, acxT5, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
  obtain ⟨n4, c4, t4, A4, k4, fr4⟩ := acx_cmemcpy K A3 t3 ac_at_4cc ac_at_4d0 (by decide) (by decide)
    (c := 0x52C2) (d := 0x3DA2) (N := 0x10C) (by decide) (by decide) (by decide) (by decide) (by decide)
    a03 a13 a23
  have hz4 := t4.zero
  have rsp4 := A4.rsp K
  obtain ⟨n5, c5, t5, A5, m5, g5⟩ := acx_blk K A4 t4 acxT6 acxT6_end
    ⟨trivial, trivial, trivial, trivial⟩ rfl (by decide)
  have r5 : ∀ q, acxS q = true → reg n5 q = reg n4 q := fun q hq => by
    rw [g5, runBlock_reg _ _ _ q hz4 (by simp only [acxT6]; revert hq; revert q; decide)]
  have a05 : reg n5 a0 = P.B + BitVec.ofNat 32 0x3C94 := by
    rw [g5]; simp +decide only [runBlock, BInstr.run, acxT6, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    exact acx_k rsp4 _ (by decide)
  have a15 : reg n5 a1 = P.B + BitVec.ofNat 32 0x3DA2 := by
    rw [g5]; simp +decide only [runBlock, BInstr.run, acxT6, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    rw [acx_z0, k4 _ (by decide), s03]
  have a25 : reg n5 a2 = BitVec.ofNat 32 0x10C := by
    rw [g5]; simp +decide only [runBlock, BInstr.run, acxT6, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
  obtain ⟨n6, c6, t6, A6, k6, fr6⟩ := acx_cmemcpy K A5 t5 ac_at_4dc ac_at_4e0 (by decide) (by decide)
    (c := 0x3DA2) (d := 0x3C94) (N := 0x10C) (by decide) (by decide) (by decide) (by decide) (by decide)
    a05 a15 a25
  rw [m5] at fr6
  rw [m3] at fr4
  rw [m1] at fr2
  have O : ∀ e, e + 4 ≤ 0x5A70 → (e + 4 ≤ 0x3A40 ∨ 0x3A50 ≤ e) → (e + 4 ≤ 0x3C94 ∨ 0x3EAE ≤ e) →
      (e + 4 ≤ 0x52C2 ∨ 0x53CE ≤ e) →
      memLoad32 n6.mem (P.B + BitVec.ofNat 32 e) = memLoad32 n.mem (P.B + BitVec.ofNat 32 e) := fun e h1 h2 h3 h4 => by
    rw [acx_cpO F fr6 (by decide) h1 h2 (by omega), acx_cpO F fr4 (by decide) h1 h2 (by omega),
      acx_cpO F fr2 (by decide) h1 h2 h4]
  have I : ∀ k, k + 4 ≤ 0x10C →
      memLoad32 n6.mem (P.B + BitVec.ofNat 32 (0x3C94 + k)) = memLoad32 n.mem (P.B + BitVec.ofNat 32 (0x5920 + k)) :=
    fun k hk => by
      rw [acx_cpL F fr6 (by decide) (by decide) rfl rfl hk, acx_cpL F fr4 (by decide) (by decide) rfl rfl hk,
        acx_cpL F fr2 (by decide) (by decide) rfl rfl hk]
  refine ⟨n6, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans c6)))), .inr ⟨t6, A6,
    by rw [k6 _ (by decide), r5 _ (by decide), k4 _ (by decide), r3 _ (by decide) (by decide) (by decide)];
       exact S.s1,
    by rw [O _ (by decide) (by decide) (by decide) (by decide)]; exact S.w30,
    by rw [O _ (by decide) (by decide) (by decide) (by decide)]; exact S.ro,
    by rw [O _ (by decide) (by decide) (by decide) (by decide)]; exact S.rl, S.hol,
    by rw [I 0x108 (by decide)]; exact S.cnt,
    fun i hi => by rw [I (4 * i) (by omega)]; exact S.idx i hi,
    S.ok, S.hc, S.hlen, S.hL, S.f0, S.f1, S.f2, S.f3, S.fv, S.fc⟩⟩

/-- From 0x2A6 to 0x4E4: the whole index stage, in the frame's terms. -/
theorem acx_to4e4 {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) (s : St n.mem AC n 0x2A6 (reg n)) :
    AcxTo P n (fun n' => ∃ c, AcxS4 P c n') :=
  (acx_to440 K A s).bind fun _ ⟨_, S3⟩ => (acx_t1 K S3).bind fun _ S5 =>
    (acx_t2 K S5).bind fun _ S4 => AcxTo.done ⟨_, S4⟩

end C3.RV32.Ac
