import C3BootProofs.Proofs.AcceptIndexLib

/-!
# `boot_main`'s first closure: the index stage's header

From 0x2A6 the index stage checks the TUF part's length, reads its 8-byte
header from flash, and checks the magic, the version, and the count of
roots.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3

set_option maxRecDepth 100000

theorem acx_fl {B : Word} {c : Nat} (k : Word) (h : c + k.toNat < 2 ^ 32) :
    B + BitVec.ofNat 32 c + k = B + BitVec.ofNat 32 (c + k.toNat) := by
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; have := k.isLt; omega

theorem acx_k {B s : Word} (rsp : s = B + 0x3A50) (k : Word) {c : Nat}
    (h : (0x3A50 + k : Word) = BitVec.ofNat 32 c) : s + k = B + BitVec.ofNat 32 c := by
  rw [rsp, BitVec.add_assoc, h]

theorem acx_k' {B s : Word} (rsp : s = B + 0x3A50) (k : Word) {c : Nat}
    (h : (0x3A50 + k : Word) = BitVec.ofNat 32 c) : k + s = B + BitVec.ofNat 32 c := by
  rw [BitVec.add_comm, acx_k rsp k h]

theorem AcxC.st {P : AcxP} {n n' : Machine} {o : Nat} (A : AcxC P n) (t : St n.mem AC n' o (reg n)) :
    AcxC P n' :=
  A.next (fun q _ => t.regs q) (fun x _ _ => by rw [t.mem])

theorem acx_st {n n' : Machine} {o : Nat} (t : St n.mem AC n' o (reg n)) : St n'.mem AC n' o (reg n') :=
  ⟨t.pc, rfl, fun _ => rfl⟩

/-- A store into the frame, for `BlockOk`. -/
theorem acx_swok {B : Word} (F : Fr B 0x5A70) {e : Nat} (he : e + 4 ≤ 0x5A70) (h4 : e % 4 = 0) :
    (B + BitVec.ofNat 32 e).toNat % 4 = 0 ∧ Sep (B + BitVec.ofNat 32 e) 4 AC bootMainClosure0Code.length :=
  ⟨acx_al F (by omega) h4, acx_hiSep F he (by decide) (by decide)⟩

theorem acx_swok' {B : Word} (F : Fr B 0x5A70) {e : Nat} (k : Word) (he : e + k.toNat + 4 ≤ 0x5A70)
    (h4 : (e + k.toNat) % 4 = 0) :
    (B + BitVec.ofNat 32 e + k).toNat % 4 = 0 ∧ Sep (B + BitVec.ofNat 32 e + k) 4 AC bootMainClosure0Code.length := by
  rw [acx_fl k (by omega)]; exact acx_swok F he h4

theorem acx_bgeu_t {a b : Word} (h : b.toNat ≤ a.toNat) : branchTaken .bgeu a b = true := by
  simp only [branchTaken, BitVec.ult, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]; omega

theorem acx_bgeu_f {a b : Word} (h : a.toNat < b.toNat) : branchTaken .bgeu a b = false := by
  simp only [branchTaken, BitVec.ult, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq]; exact h

theorem acx_bltu_t {a b : Word} (h : a.toNat < b.toNat) : branchTaken .bltu a b = true := by
  simp only [branchTaken, BitVec.ult, decide_eq_true_eq]; exact h

theorem acx_bltu_f {a b : Word} (h : b.toNat ≤ a.toNat) : branchTaken .bltu a b = false := by
  simp only [branchTaken, BitVec.ult, decide_eq_false_iff_not]; omega

theorem acx_beq_t {a b : Word} (h : a = b) : branchTaken .beq a b = true := by
  subst h; exact decide_eq_true rfl

theorem acx_beq_f {a b : Word} (h : a ≠ b) : branchTaken .beq a b = false := by
  simp only [branchTaken, beq_eq_false_iff_ne, ne_eq]; exact h

theorem acx_bne_t {a b : Word} (h : a ≠ b) : branchTaken .bne a b = true := by
  simp only [branchTaken, bne_iff_ne, ne_eq]; exact h

theorem acx_bne_f {a b : Word} (h : a = b) : branchTaken .bne a b = false := by
  subst h; show (!decide (a = a)) = false; rw [decide_eq_true rfl]; rfl

/-- From 0x2A6: the largest part. -/
def acxH0 : List BInstr := [.lui a0 0x60000]

theorem acxH0_end : blockEnd bootMainClosure0Code 0x2A6 acxH0 = some 0x2AA := by decide

/-- From 0x2AE: error 5. -/
def acxH5 : List BInstr := [.aluImm .add a0 x0 0x5]

theorem acxH5_end : blockEnd bootMainClosure0Code 0x2AE acxH5 = some 0x2B0 := by decide

/-- From 0x430: error 0x26, a failed flash read. -/
def acxE26 : List BInstr := [.aluImm .add a0 x0 0x26]

theorem acxE26_end : blockEnd bootMainClosure0Code 0x430 acxE26 = some 0x434 := by decide

theorem acx_e26 {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) (s : St n.mem AC n 0x430 (reg n))
    {Q : Machine → Prop} : AcxTo P n Q := by
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := s.block acxE26 (A.code K) acxE26_end ⟨trivial, trivial⟩
  have k1 : ∀ q, acxL q = true → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [acxE26]; revert hq; revert q; decide)]
  have A1 : AcxC P n1 := A.next k1 (fun x _ _ => by rw [u1.mem]; rfl)
  refine AcxTo.pre c1 (acx_exit K A1 ⟨u1.pc, rfl, fun _ => rfl⟩ (c := 0x26) ?_ (.inr rfl))
  rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acxE26, upd, ↓reduceIte, aluEval, hz, BitVec.zero_add]

theorem acx_e5 {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) (s : St n.mem AC n 0x2AE (reg n))
    {Q : Machine → Prop} : AcxTo P n Q := by
  have hz := s.zero
  obtain ⟨n1, c1, u1⟩ := s.block acxH5 (A.code K) acxH5_end ⟨trivial, trivial⟩
  have k1 : ∀ q, acxL q = true → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [acxH5]; revert hq; revert q; decide)]
  have A1 : AcxC P n1 := A.next k1 (fun x _ _ => by rw [u1.mem]; rfl)
  have t1 : St n1.mem AC n1 0x2B0 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  obtain ⟨n2, e2, t2⟩ := t1.jump (A1.code K) ac_at_2b0 (off' := 0x434) (by decide) (by rw [t1.pc]; decide)
  refine AcxTo.pre (c1.trans (.single e2)) (acx_exit K (A1.next (fun q _ => by rw [t2.regs]) (fun x _ _ => by
    rw [t2.mem])) ⟨t2.pc, rfl, fun _ => rfl⟩ (c := 5) ?_ (.inl (by decide)))
  rw [t2.regs, u1.regs]; simp +decide only [runBlock, BInstr.run, acxH5, upd, ↓reduceIte, aluEval, hz, BitVec.zero_add]

/-- From 0x2B2: clear the header and set up the read of 8 bytes into it. -/
def acxH1 : List BInstr :=
  [.alu .add a1 x0 (23 : Fin 32), .lui a0 0x2000, .aluImm .add a0 a0 0xFFFFFDB0, .alu .add (8 : Fin 32) sp a0,
   .aluImm .add a0 x0 0x0, .sw (8 : Fin 32) a0 0x0, .sw (8 : Fin 32) a0 0x4, .aluImm .add a2 x0 0x0,
   .lui a0 0x2000, .aluImm .add a0 a0 0xFFFFFDB0, .alu .add a3 sp a0, .aluImm .add a4 x0 0x8,
   .alu .add a0 x0 (24 : Fin 32), .lui a5 0x2000, .aluImm .add a5 a5 0xFFFFFDB0, .alu .add (19 : Fin 32) sp a5,
   .aluImm .add (9 : Fin 32) x0 0x8]

theorem acxH1_end : blockEnd bootMainClosure0Code 0x2B2 acxH1 = some 0x2E0 := by decide

/-- The state at 0x2EC: the part's 8-byte header is in the frame. -/
structure AcxS1 (P : AcxP) (n : Machine) : Prop where
  st : St n.mem AC n 0x2EC (reg n)
  c : AcxC P n
  s0 : reg n (8 : Fin 32) = P.B + BitVec.ofNat 32 0x5800
  s1 : reg n (9 : Fin 32) = 8
  s3 : reg n (19 : Fin 32) = P.B + BitVec.ofNat 32 0x5800
  hL : (reg P.n0 (23 : Fin 32)).toNat ≤ 0x60000
  hL8 : 8 ≤ (reg P.n0 (23 : Fin 32)).toNat
  hdr : ∀ i, i < 8 → n.mem (P.B + BitVec.ofNat 32 (0x5800 + i)) = P.flash ((reg P.n0 (24 : Fin 32)).toNat + i)

set_option maxHeartbeats 4000000 in
/-- From 0x2A6 to 0x2EC: check the part's length and read its header. -/
theorem acx_h1 {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) (s : St n.mem AC n 0x2A6 (reg n)) :
    AcxTo P n (AcxS1 P) := by
  have F := K.F
  have hFl := F.lo; have hFh := F.hi
  have rsp := A.rsp K
  have hz := s.zero
  have r23 : reg n (23 : Fin 32) = reg P.n0 23 := A.kl 23 (by decide)
  have r24 : reg n (24 : Fin 32) = reg P.n0 24 := A.kl 24 (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block acxH0 (A.code K) acxH0_end ⟨trivial, trivial⟩
  have k1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [acxH0]; revert hq; revert q; decide)]
  have a01 : reg n1 a0 = 0x60000 := by rw [u1.regs]; simp +decide only [runBlock, BInstr.run, acxH0, upd, ↓reduceIte]
  have A1 : AcxC P n1 := A.next (fun q hq => k1 q (by revert hq; revert q; decide)) (fun x _ _ => by rw [u1.mem]; rfl)
  have t1 : St n1.mem AC n1 0x2AA (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have C1 := A1.code K
  by_cases hL : (reg P.n0 (23 : Fin 32)).toNat ≤ 0x60000
  case neg =>
    obtain ⟨n2, e2, t2⟩ := t1.notTaken C1 0x2AE ac_at_2aa (by decide)
      (acx_bgeu_f (by rw [a01, k1 _ (by decide), r23]; exact Nat.lt_of_not_le hL))
    exact AcxTo.pre (c1.trans (.single e2)) (acx_e5 K (A1.next (fun q _ => by rw [t2.regs])
      (fun x _ _ => by rw [t2.mem])) ⟨t2.pc, rfl, fun _ => rfl⟩)
  obtain ⟨n2, e2, t2⟩ := t1.taken C1 0x2B2 ac_at_2aa (by decide)
    (acx_bgeu_t (by rw [a01, k1 _ (by decide), r23]; exact hL))
  have t2' : St n2.mem AC n2 0x2B2 (reg n2) := ⟨t2.pc, rfl, fun _ => rfl⟩
  have A2 : AcxC P n2 := A1.next (fun q _ => by rw [t2.regs]) (fun x _ _ => by rw [t2.mem])
  have rsp2 := A2.rsp K
  have hz2 := t2'.zero
  obtain ⟨n3, c3, u3⟩ := t2'.block acxH1 (A2.code K) acxH1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acxH1]
    simp +decide only [upd, ↓reduceIte, and_true, true_and, aluEval, BitVec.reduceAdd]
    rw [acx_k rsp2 _ (c := 0x5800) (by decide)]
    exact ⟨acx_swok' F _ (by decide) (by decide), acx_swok' F _ (by decide) (by decide)⟩)
  have g3 : ∀ q, reg n3 q = (runBlock acxH1 (n2.mem, reg n2)).2 q := fun q => by rw [u3.regs]
  have k3 : ∀ q, acxS q = true → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (19 : Fin 32) → reg n3 q = reg n2 q :=
    fun q hq h8 h9 h19 => by
      rw [g3, runBlock_reg _ _ _ q hz2 (by simp only [acxH1]; revert hq h8 h9 h19; revert q; decide)]
  have v3 : ∀ q, reg n3 q = (runBlock acxH1 (n2.mem, reg n2)).2 q := g3
  have m3 : n3.mem = memStore32 (memStore32 n2.mem (P.B + BitVec.ofNat 32 0x5800) 0)
      (P.B + BitVec.ofNat 32 0x5804) 0 := by
    rw [u3.mem]; simp only [runBlock, BInstr.run, acxH1]
    simp +decide only [upd, ↓reduceIte, aluEval, BitVec.reduceAdd, hz2, BitVec.zero_add]
    rw [acx_k rsp2 _ (c := 0x5800) (by decide), acx_fl (0 : Word) (by decide), acx_fl (4 : Word) (by decide)]
    rfl
  have rv : ∀ q, acxL q = true → reg n3 q = reg n q := fun q hq => by
    rw [k3 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide), t2.regs, k1 q (by revert hq; revert q; decide)]
  have A3 : AcxC P n3 := A2.next (fun q hq => by rw [rv q hq, t2.regs, k1 q (by revert hq; revert q; decide)]) (fun x _ h2 => by
    rw [m3, memStore32_get_sep (acx_sepR F (by decide) (by omega)),
      memStore32_get_sep (acx_sepR F (by decide) (by omega))])
  have t3 : St n3.mem AC n3 0x2E0 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have ev : ∀ q, reg n3 q = (runBlock acxH1 (n2.mem, reg n2)).2 q := g3
  have e2r : ∀ q, reg n2 q = reg n1 q := t2.regs
  obtain ⟨n4, c4, t4, A4, kk4, a04, ok4, -⟩ := acx_cfpr K A3 t3 ac_at_2e0 ac_at_2e4 (by decide) (by decide)
    (d := 0x5800) (len := 8) (start := reg P.n0 24) (plen := reg P.n0 23) (off := 0) (by decide) (by decide)
    (by rw [ev]; simp +decide only [runBlock, BInstr.run, acxH1, upd, ↓reduceIte, aluEval, hz2, BitVec.zero_add]
        rw [e2r, k1 _ (by decide), r24]; exact BitVec.zero_add _)
    (by rw [ev]; simp +decide only [runBlock, BInstr.run, acxH1, upd, ↓reduceIte, aluEval, hz2, BitVec.zero_add]
        rw [e2r, k1 _ (by decide), r23]; exact BitVec.zero_add _)
    (by rw [ev]; simp +decide only [runBlock, BInstr.run, acxH1, upd, ↓reduceIte, aluEval, hz2, BitVec.zero_add])
    (by rw [ev]; simp +decide only [runBlock, BInstr.run, acxH1, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
        exact acx_k rsp2 _ (by decide))
    (by rw [ev]; simp +decide only [runBlock, BInstr.run, acxH1, upd, ↓reduceIte, aluEval, hz2, BitVec.zero_add])
  have C4 := A4.code K
  rcases a04 with h0 | h1
  · obtain ⟨n5, e5, t5⟩ := t4.taken C4 0x430 ac_at_2e8 (by decide) (acx_beq_t (by rw [h0, t4.zero]))
    exact AcxTo.pre (c1.trans ((Steps.single e2).trans (c3.trans (c4.trans (.single e5)))))
      (acx_e26 K (A4.st t5) (acx_st t5))
  obtain ⟨n5, e5, t5⟩ := t4.notTaken C4 0x2EC ac_at_2e8 (by decide)
    (acx_beq_f (by rw [h1, t4.zero]; decide))
  obtain ⟨o1, -, o3⟩ := ok4 h1
  refine AcxTo.done ?_ |> AcxTo.pre (c1.trans ((Steps.single e2).trans (c3.trans (c4.trans (.single e5)))))
  have v8 : reg n3 (8 : Fin 32) = P.B + BitVec.ofNat 32 0x5800 := by
    rw [ev]; simp +decide only [runBlock, BInstr.run, acxH1, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    exact acx_k rsp2 _ (by decide)
  have v19 : reg n3 (19 : Fin 32) = P.B + BitVec.ofNat 32 0x5800 := by
    rw [ev]; simp +decide only [runBlock, BInstr.run, acxH1, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    exact acx_k rsp2 _ (by decide)
  have v9 : reg n3 (9 : Fin 32) = 8 := by
    rw [ev]; simp +decide only [runBlock, BInstr.run, acxH1, upd, ↓reduceIte, aluEval, hz2, BitVec.zero_add]
  have h00 : (0 : Word).toNat = 0 := rfl
  rw [h00] at o1 o3
  exact ⟨acx_st t5, A4.st t5, by rw [t5.regs, kk4 _ (by decide), v8], by rw [t5.regs, kk4 _ (by decide), v9],
    by rw [t5.regs, kk4 _ (by decide), v19], hL, by omega, fun i hi => by rw [t5.mem]; exact o3 i hi⟩

end C3.RV32.Ac
