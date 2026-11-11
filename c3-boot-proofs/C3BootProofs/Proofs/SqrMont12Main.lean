import C3BootProofs.Proofs.SqrMont12

/-!
# P-384's Montgomery squaring, end to end

`square_montgomery_form::<12>` runs the loop of `SqrMont12` and then the same
final subtraction and `Uint<12>::select` as `mul_montgomery_form::<12>`, at
other offsets and with the modulus pointer and the top carry in other
registers.
-/

namespace C3.RV32

open C3.Image

/-- The end of a subtraction round, from 0x11C: keep the borrow, store the
difference, and advance the pointers and the count. -/
def sqSubTail : List BInstr :=
  [.alu .add a2 x0 a1, .aluImm .add (9 : Fin 32) (9 : Fin 32) 4, .sw (19 : Fin 32) a0 0,
   .aluImm .add (22 : Fin 32) (22 : Fin 32) 4, .aluImm .add (19 : Fin 32) (19 : Fin 32) 4,
   .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem sqSubTail_end : blockEnd sqMont12Code 0x11C sqSubTail = some 0x12A := by decide
end

set_option maxRecDepth 20000 in
theorem sqSubTail_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock sqSubTail (M, f)).1 = memStore32 M (f (19 : Fin 32) + 0) (f a0) ∧
    (runBlock sqSubTail (M, f)).2 a2 = f a1 ∧
    (runBlock sqSubTail (M, f)).2 (9 : Fin 32) = f (9 : Fin 32) + 4 ∧
    (runBlock sqSubTail (M, f)).2 (22 : Fin 32) = f (22 : Fin 32) + 4 ∧
    (runBlock sqSubTail (M, f)).2 (19 : Fin 32) = f (19 : Fin 32) + 4 ∧
    (runBlock sqSubTail (M, f)).2 (8 : Fin 32) = f (8 : Fin 32) + 0xFFFFFFFF ∧
    ∀ q, q ≠ a2 → q ≠ (9 : Fin 32) → q ≠ (22 : Fin 32) → q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) →
      (runBlock sqSubTail (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, sqSubTail]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q q2 q9 q23 q19 q8 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte, hz]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q2, q9, q23, q19, q8]

theorem sqSubTail_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (f (19 : Fin 32) + 0).toNat % 4 = 0) (hs : Sep (f (19 : Fin 32) + 0) 4 base len) :
    BlockOk base len sqSubTail (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, sqSubTail, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h, hs⟩

/-- `borrowing_sub`'s offset from `square_montgomery_form::<12>`. -/
abbrev sqBsub (P : Word) : Word := P + 0xFFFEF3EA

/-- **One round of the final subtraction**, from 0x10E: subtract limb `i` of
the modulus and the borrow from limb `i` of the accumulator, and store the
difference at limb `i` of the buffer at `D`. `borrowing_sub` also writes
the word below `sp`. -/
theorem sqsub_iter {M : Word → BitVec 8} {P F acc np D b : Word} {n : Machine} {i : Nat}
    (s : St M P n 0x10E (reg n)) (hc : CodeIn M P sqMont12Code) (hb : CodeIn M (sqBsub P) borrowingSubCode)
    (hP : P.toNat % 2 = 0) (hi : i < 12) (hF : F.toNat % 4 = 0) (hacc : acc.toNat % 4 = 0)
    (hnp : np.toNat % 4 = 0) (hD : D.toNat % 4 = 0)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (sqBsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P sqMont12Code.length)
    (sDC : Sep (D + BitVec.ofNat 32 (4 * i)) 4 P sqMont12Code.length)
    (rsp : reg n sp = F) (r9 : reg n (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * i))
    (r23 : reg n (22 : Fin 32) = np + BitVec.ofNat 32 (4 * i)) (r19 : reg n (19 : Fin 32) = D + BitVec.ofNat 32 (4 * i))
    (r8 : reg n (8 : Fin 32) = BitVec.ofNat 32 (12 - i)) (ra2 : reg n a2 = b) :
    ∃ n' Mb, Steps n n' ∧
      St (memStore32 Mb (D + BitVec.ofNat 32 (4 * i))
          (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b))
        P n' (if i + 1 < 12 then 0x10E else 0x12C) (reg n') ∧
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Mb x = M x) ∧
      reg n' a2 = bsubB (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n' sp = F ∧ reg n' (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (22 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (19 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n' (8 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (22 : Fin 32) →
        q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.lw hc sq_at_10e (off' := 0x110) (by decide)
    (by rw [r9, add_lit_zero]; exact aligned_add hacc (by omega))
  obtain ⟨n2, d2, u2⟩ := u1.lw hc sq_at_110 (off' := 0x114) (by decide)
    (by rw [upd_ne (by decide) (by decide), r23, add_lit_zero]; exact aligned_add hnp (by omega))
  rw [r9, add_lit_zero] at u2
  have f0 : upd (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (22 : Fin 32) + 0)) a0 =
      memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) := by simp +decide [upd]
  have f1 : upd (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))) a1
      (memLoad32 M (upd (reg n) a0 (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (22 : Fin 32) + 0)) a1 =
      memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by
    simp +decide only [upd, ↓reduceIte]; rw [r23, add_lit_zero]
  have u2' := u2.self
  have g2a0 : reg n2 a0 = memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f0]
  have g2a1 : reg n2 a1 = memLoad32 M (np + BitVec.ofNat 32 (4 * i)) := by rw [u2.regs, f1]
  have k2 : ∀ q, q ≠ a0 → q ≠ a1 → reg n2 q = reg n q := fun q q0 q1 => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1]
  obtain ⟨n3, c3, u3, a03, a13, sp3, fr3, mem3⟩ := u2'.bsubCall hc hb (even_at P hP 0xFFFEF3EA (by decide))
    sq_at_114 sq_at_118 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP (0x114 + 8) (by decide))
    (by rw [k2 sp (by decide) (by decide), rsp]) hF sFB
  rw [g2a0, g2a1, k2 a2 (by decide) (by decide), ra2] at a03 a13
  have hc3 : CodeIn n3.mem P sqMont12Code := fun j hj => by
    rw [mem3 _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
  have k3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg n3 q = reg n q := fun q q0 q1 q2 q3 q4 qr =>
    by rw [fr3 q q0 q1 q2 q3 q4 qr, k2 q q0 q1]
  have e19 : reg n3 (19 : Fin 32) + 0 = D + BitVec.ofNat 32 (4 * i) := by
    rw [k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r19, add_lit_zero]
  obtain ⟨n4, c4, u4⟩ := St.block sqSubTail u3 hc3 sqSubTail_end
    (sqSubTail_ok (by rw [e19]; exact aligned_add hD (by omega)) (by rw [e19]; exact sDC))
  obtain ⟨em4, t2, t9, t23, t19, t8, tk⟩ := sqSubTail_run (M := n3.mem) (f := reg n3) u3.zero
  have u4' := u4.self
  rw [em4, e19, a03] at u4'
  have g4 : ∀ q, reg n4 q = (runBlock sqSubTail (n3.mem, reg n3)).2 q := u4.regs
  have hc4 := CodeIn.store32 (v := bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i)))
    (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) hc3 sDC
  have e8 : reg n4 (8 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) := by
    rw [g4, t8, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r8, cnt12_dec i hi]
  have hb4 : branchTaken .bne (reg n4 (8 : Fin 32)) (reg n4 x0) = decide (i + 1 < 12) := by
    rw [e8, u4'.zero]; exact cnt12_ne i hi
  have post : ∀ n5 : Machine, (∀ q, reg n5 q = reg n4 q) →
      reg n5 a2 = bsubB (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 M (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M (np + BitVec.ofNat 32 (4 * i))) b) ∧
      reg n5 sp = F ∧ reg n5 (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (22 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (19 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      reg n5 (8 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
      ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (22 : Fin 32) →
        q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → reg n5 q = reg n q := fun n5 h5 => by
    refine ⟨by rw [h5, g4, t2, a13], by rw [h5, g4, tk _ (by decide) (by decide) (by decide) (by decide) (by decide), sp3],
      ?_, ?_, ?_, by rw [h5, e8], fun q q0 q1 q2 q3 q4 qr q9 q23 q19 q8 => ?_⟩
    · rw [h5, g4, t9, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r9, ptr4]
    · rw [h5, g4, t23, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r23, ptr4]
    · rw [h5, g4, t19, k3 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r19, ptr4]
    · rw [h5, g4, tk q q2 q9 q23 q19 q8, k3 q q0 q1 q2 q3 q4 qr]
  by_cases hl : i + 1 < 12
  · obtain ⟨n5, d5, u5⟩ := u4'.taken hc4 0x10E sq_at_12a (by decide) (by rw [hb4]; exact decide_eq_true hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_left hl]; exact u5.self,
      mem3, post n5 u5.regs⟩
  · obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc4 0x12C sq_at_12a (by decide) (by rw [hb4]; exact decide_eq_false hl)
    exact ⟨n5, n3.mem, .cons d1 (.cons d2 (c3.trans (c4.trans (.single d5)))), by rw [ite_eq_right hl]; exact u5.self,
      mem3, post n5 u5.regs⟩

set_option exponentiation.threshold 400 in
/-- **The final subtraction**, from round `i` to its end at 0x12C: the
buffer at `D` gets the accumulator minus the modulus, and `a2` the borrow
out as a mask. -/
theorem sqsub_loop {P F acc np D : Word} {M0 : Word → BitVec 8} (hP : P.toNat % 2 = 0) (hF : F.toNat % 4 = 0)
    (hacc : acc.toNat % 4 = 0) (hnp : np.toNat % 4 = 0) (hD : D.toNat % 4 = 0) (hDw : D.toNat + 48 ≤ 2 ^ 32)
    (sFA : Sep (F + 0xFFFFFFFC) 4 acc 48) (sFN : Sep (F + 0xFFFFFFFC) 4 np 48) (sFD : Sep (F + 0xFFFFFFFC) 4 D 48)
    (sDA : Sep D 48 acc 48) (sDN : Sep D 48 np 48)
    (sFB : Sep (F + 0xFFFFFFFC) 4 (sqBsub P) borrowingSubCode.length)
    (sFC : Sep (F + 0xFFFFFFFC) 4 P sqMont12Code.length)
    (sDB : Sep D 48 (sqBsub P) borrowingSubCode.length) (sDC : Sep D 48 P sqMont12Code.length) :
    ∀ m i, i + m + 1 = 12 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x10E (reg n) → CodeIn M P sqMont12Code → CodeIn M (sqBsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 acc i + 2 ^ (32 * i) * maskBit b = accV M0 np i + accV M D i →
      reg n sp = F → reg n (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * i) →
      reg n (22 : Fin 32) = np + BitVec.ofNat 32 (4 * i) → reg n (19 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (12 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x12C (reg n') ∧ CodeIn M' P sqMont12Code ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 acc 12 + 2 ^ (32 * 12) * maskBit (reg n' a2) = accV M0 np 12 + accV M' D 12 ∧
        reg n' sp = F ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (22 : Fin 32) →
          q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
  have step : ∀ i, i < 12 → ∀ {M : Word → BitVec 8} {n : Machine} {b : Word},
      St M P n 0x10E (reg n) → CodeIn M P sqMont12Code → CodeIn M (sqBsub P) borrowingSubCode →
      (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M x = M0 x) → (b = 0 ∨ b = 0xFFFFFFFF) →
      accV M0 acc i + 2 ^ (32 * i) * maskBit b = accV M0 np i + accV M D i →
      reg n sp = F → reg n (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * i) →
      reg n (22 : Fin 32) = np + BitVec.ofNat 32 (4 * i) → reg n (19 : Fin 32) = D + BitVec.ofNat 32 (4 * i) →
      reg n (8 : Fin 32) = BitVec.ofNat 32 (12 - i) → reg n a2 = b →
      ∃ n' M', Steps n n' ∧ St M' P n' (if i + 1 < 12 then 0x10E else 0x12C) (reg n') ∧
        CodeIn M' P sqMont12Code ∧ CodeIn M' (sqBsub P) borrowingSubCode ∧
        (∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → Sep D 48 x 1 → M' x = M0 x) ∧
        (reg n' a2 = 0 ∨ reg n' a2 = 0xFFFFFFFF) ∧
        accV M0 acc (i + 1) + 2 ^ (32 * (i + 1)) * maskBit (reg n' a2) = accV M0 np (i + 1) + accV M' D (i + 1) ∧
        reg n' sp = F ∧ reg n' (9 : Fin 32) = acc + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (22 : Fin 32) = np + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (19 : Fin 32) = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
        reg n' (8 : Fin 32) = BitVec.ofNat 32 (12 - (i + 1)) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (9 : Fin 32) → q ≠ (22 : Fin 32) →
          q ≠ (19 : Fin 32) → q ≠ (8 : Fin 32) → reg n' q = reg n q := by
    intro i hi M n b s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    obtain ⟨n1, Mb, c1, u1, hMb, e2, esp, e9, e23, e19, e8, fr⟩ := sqsub_iter (i := i) s hc hb hP hi hF hacc hnp hD
      sFB sFC (sDC.sub (by omega)) rsp r9 r23 r19 r8 ra2
    have eA : memLoad32 M (acc + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFA.subR (by omega)) (sDA.subR (by omega))
    have eN : memLoad32 M (np + BitVec.ofNat 32 (4 * i)) = memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)) :=
      load_frame2 hfr (sFN.subR (by omega)) (sDN.subR (by omega))
    rw [eA, eN] at u1 e2
    obtain ⟨bv, bm⟩ := bsub_val (memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i)))
      b hbm
    have hDb : CodeIn Mb (sqBsub P) borrowingSubCode := fun j hj => by
      rw [hMb _ (sFB.subR (c := j) (l := 1) (by omega))]; exact hb j hj
    have hCb : CodeIn Mb P sqMont12Code := fun j hj => by
      rw [hMb _ (sFC.subR (c := j) (l := 1) (by omega))]; exact hc j hj
    refine ⟨n1, _, c1, u1, CodeIn.store32 hCb (sDC.sub (by omega)), CodeIn.store32 hDb (sDB.sub (by omega)),
      fun x hx hd => ?_, by rw [e2]; exact bm, ?_, esp, e9, e23, e19, e8, fr⟩
    · rw [memStore32_get_sep (hd.sub (c := 4 * i) (l := 4) (by omega)), hMb x hx, hfr x hx hd]
    · have hA : accV (memStore32 Mb (D + BitVec.ofNat 32 (4 * i)) (bsubD (memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i)))
          (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) b)) D (i + 1) = accV M D i +
          (bsubD (memLoad32 M0 (acc + BitVec.ofNat 32 (4 * i))) (memLoad32 M0 (np + BitVec.ofNat 32 (4 * i))) b).toNat *
            2 ^ (32 * i) := by
        rw [accV_succ1, accV_store_above (by omega) i (Nat.le_refl i), memLoad32_store32_same]
        congr 1
        exact accV_congr i fun j hj => memLoad32_congr fun q hq =>
          hMb _ ((sFD.subR (c := 4 * j) (l := 4) (by omega)).subR (c := q) (l := 1) (by omega))
      rw [hA, accV_succ1, accV_succ1, pow32_succ, e2]
      exact sub_arith hv bv
  intro m
  induction m with
  | zero =>
    intro i hi M n b s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    have i11 : i = 11 := Nat.succ.inj hi
    subst i11
    obtain ⟨n1, M1, c1, u1, hc1, _, hf1, hm1, hv1, sp1, _, _, _, _, fr⟩ :=
      step 11 (by decide) s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    exact ⟨n1, M1, c1, u1, hc1, hf1, hm1, hv1, sp1, fr⟩
  | succ m ih =>
    intro i hi M n b s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    have hl : i + 1 < 12 := sel_lt1 hi
    obtain ⟨n1, M1, c1, u1, hc1, hb1, hf1, hm1, hv1, sp1, e9, e23, e19, e8, fr⟩ :=
      step i (Nat.lt_trans (Nat.lt_succ_self i) hl) s hc hb hfr hbm hv rsp r9 r23 r19 r8 ra2
    rw [ite_eq_left hl] at u1
    obtain ⟨n', M', c', u', hc', hf', hm', hv', sp', fr'⟩ :=
      ih (i + 1) (sel_succ hi) u1 hc1 hb1 hf1 hm1 hv1 sp1 e9 e23 e19 e8 rfl
    exact ⟨n', M', c1.trans c', u', hc', hf', hm', hv', sp', fun q q0 q1 q2 q3 q4 qr q9 q23 q19 q8 => by
      rw [fr' q q0 q1 q2 q3 q4 qr q9 q23 q19 q8, fr q q0 q1 q2 q3 q4 qr q9 q23 q19 q8]⟩

/-- From 0x12C: spill the top carry, and choose the accumulator when the
top carry is zero and the subtraction borrowed, through a byte of the
frame; then set up the call to `borrowing_sub` whose result goes unused. -/
def sqChoice : List BInstr :=
  [.sw sp (21 : Fin 32) 0x6C, .aluImm .add a0 sp 0x6C, .lw a0 sp 0x6C, .aluImm .sltu (9 : Fin 32) a0 1,
   .alu .and (9 : Fin 32) (9 : Fin 32) a2, .sb sp (9 : Fin 32) 0x6C, .aluImm .add a0 sp 0x6C, .lbu a0 sp 0x6C,
   .aluImm .add a0 a0 0xFFFFFFFF, .alu .and a2 a2 a0, .alu .add a0 x0 (21 : Fin 32), .aluImm .add a1 x0 0]

/-- From 0x152: the arguments of `Uint<12>::select`. -/
def sqSelArgs : List BInstr :=
  [.aluImm .add a1 sp 0x3C, .aluImm .add a2 sp 0xC, .alu .add a0 x0 (18 : Fin 32), .alu .add a3 x0 (9 : Fin 32)]

/-- From 0xF2: the arguments of the `memset` that zeroes the difference
buffer, which `s3` also points at. -/
def sqSubPre : List BInstr :=
  [.aluImm .add a0 sp 0x3C, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0, .aluImm .add (19 : Fin 32) sp 0x3C]

/-- From 0x106: the borrow, the accumulator pointer, and the count. -/
def sqSubInit : List BInstr :=
  [.aluImm .add a2 x0 0, .aluImm .add (9 : Fin 32) sp 0xC, .aluImm .add (8 : Fin 32) x0 0xC]

section
set_option maxRecDepth 20000
theorem sqChoice_end : blockEnd sqMont12Code 0x12C sqChoice = some 0x14A := by decide
theorem sqSelArgs_end : blockEnd sqMont12Code 0x152 sqSelArgs = some 0x15A := by decide
theorem sqSubPre_end : blockEnd sqMont12Code 0xF2 sqSubPre = some 0xFE := by decide
theorem sqSubInit_end : blockEnd sqMont12Code 0x106 sqSubInit = some 0x10C := by decide
end

set_option maxRecDepth 20000 in
theorem sqChoice_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock sqChoice (M, f)).1 = memStore8 (memStore32 M (f sp + 0x6C) (f (21 : Fin 32))) (f sp + 0x6C)
      ((aluEval .and (aluEval .sltu (f (21 : Fin 32)) 1) (f a2)).extractLsb' 0 8) ∧
    (runBlock sqChoice (M, f)).2 (9 : Fin 32) = aluEval .and (aluEval .sltu (f (21 : Fin 32)) 1) (f a2) ∧
    (runBlock sqChoice (M, f)).2 a0 = f (21 : Fin 32) ∧ (runBlock sqChoice (M, f)).2 a1 = 0 ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (9 : Fin 32) → (runBlock sqChoice (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, sqChoice]
  refine ⟨?_, ?_, ?_, ?_, fun q q0 q1 q2 q9 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rw [memLoad32_store32_same]
  · simp +decide only [upd, ↓reduceIte]; rw [memLoad32_store32_same]
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1, q2, q9]

theorem sqChoice_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h : (f sp + 0x6C).toNat % 4 = 0) (hs : Sep (f sp + 0x6C) 4 base len) : BlockOk base len sqChoice (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, sqChoice, upd, ↓reduceIte, and_true, true_and]
  exact ⟨⟨h, hs⟩, h, hs.sub (c := 0) (l := 1) (by decide) |> fun h' => by rwa [add_ofNat_zero] at h'⟩

theorem sqSelArgs_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock sqSelArgs (M, f)).1 = M ∧ (runBlock sqSelArgs (M, f)).2 a1 = f sp + 0x3C ∧
    (runBlock sqSelArgs (M, f)).2 a2 = f sp + 0xC ∧ (runBlock sqSelArgs (M, f)).2 a0 = f (18 : Fin 32) ∧
    (runBlock sqSelArgs (M, f)).2 a3 = f (9 : Fin 32) ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → (runBlock sqSelArgs (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, sqSelArgs]
  refine ⟨trivial, ?_, ?_, ?_, ?_, fun q q0 q1 q2 q3 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1, q2, q3]

theorem sqSubPre_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock sqSubPre (M, f)).1 = M ∧ (runBlock sqSubPre (M, f)).2 a0 = f sp + 0x3C ∧
    (runBlock sqSubPre (M, f)).2 a2 = 0x30 ∧ (runBlock sqSubPre (M, f)).2 a1 = 0 ∧
    (runBlock sqSubPre (M, f)).2 (19 : Fin 32) = f sp + 0x3C ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (19 : Fin 32) → (runBlock sqSubPre (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, sqSubPre]
  refine ⟨trivial, ?_, ?_, ?_, ?_, fun q q0 q1 q2 q3 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1, q2, q3]

theorem sqSubInit_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock sqSubInit (M, f)).1 = M ∧ (runBlock sqSubInit (M, f)).2 a2 = 0 ∧
    (runBlock sqSubInit (M, f)).2 (9 : Fin 32) = f sp + 0xC ∧
    (runBlock sqSubInit (M, f)).2 (8 : Fin 32) = BitVec.ofNat 32 (12 - 0) ∧
    ∀ q, q ≠ a2 → q ≠ (9 : Fin 32) → q ≠ (8 : Fin 32) → (runBlock sqSubInit (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, sqSubInit]
  refine ⟨trivial, ?_, ?_, ?_, fun q q2 q9 q8 => ?_⟩
  · simp +decide only [upd, ↓reduceIte, hz]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q2, q9, q8]


end C3.RV32
