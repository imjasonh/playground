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


/-- From 0xA: keep the arguments, and set up the `memset` that zeroes the
accumulator. -/
def sqProB : List BInstr :=
  [.alu .add (19 : Fin 32) x0 a3, .alu .add (22 : Fin 32) x0 a2, .alu .add (20 : Fin 32) x0 a1,
   .alu .add (18 : Fin 32) x0 a0, .aluImm .add a0 sp 0xC, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0]

/-- From 0x22: zero the top carry and the pass count, load the low limbs of
the operand and the modulus, and point at their next limbs and the
accumulator's. -/
def sqSetupB : List BInstr :=
  [.aluImm .add (21 : Fin 32) x0 0, .aluImm .add (29 : Fin 32) x0 0, .aluImm .add (30 : Fin 32) x0 0,
   .lw (7 : Fin 32) (20 : Fin 32) 0, .lw (28 : Fin 32) (22 : Fin 32) 0, .aluImm .add a6 (20 : Fin 32) 4,
   .aluImm .add (17 : Fin 32) sp 0x10, .aluImm .add (5 : Fin 32) (22 : Fin 32) 4, .aluImm .add (6 : Fin 32) x0 0xC]

section
set_option maxRecDepth 20000
theorem sqProB_end : blockEnd sqMont12Code 0xA sqProB = some 0x1A := by decide
theorem sqSetupB_end : blockEnd sqMont12Code 0x22 sqSetupB = some 0x3E := by decide
end

theorem sqProB_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock sqProB (M, f)).1 = M ∧
    (runBlock sqProB (M, f)).2 (19 : Fin 32) = f a3 ∧ (runBlock sqProB (M, f)).2 (22 : Fin 32) = f a2 ∧
    (runBlock sqProB (M, f)).2 (20 : Fin 32) = f a1 ∧ (runBlock sqProB (M, f)).2 (18 : Fin 32) = f a0 ∧
    (runBlock sqProB (M, f)).2 a0 = f sp + 0xC ∧ (runBlock sqProB (M, f)).2 a2 = 0x30 ∧
    (runBlock sqProB (M, f)).2 a1 = 0 ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (18 : Fin 32) → q ≠ (19 : Fin 32) → q ≠ (20 : Fin 32) →
      q ≠ (22 : Fin 32) → (runBlock sqProB (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, sqProB]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q q0 q1 q2 q18 q19 q20 q22 => ?_⟩
  · simp +decide only [upd, ↓reduceIte, hz]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; exact BitVec.zero_add _
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q0, q1, q2, q18, q19, q20, q22]

/-- The registers the inline setup leaves alone. -/
def sqSetupKeep (q : Fin 32) : Bool := q.val ∉ [5, 6, 7, 16, 17, 21, 28, 29, 30]

set_option maxRecDepth 20000 in
theorem sqSetupB_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock sqSetupB (M, f)).1 = M ∧
    (runBlock sqSetupB (M, f)).2 (21 : Fin 32) = 0 ∧ (runBlock sqSetupB (M, f)).2 (29 : Fin 32) = 0 ∧
    (runBlock sqSetupB (M, f)).2 (30 : Fin 32) = BitVec.ofNat 32 0 ∧
    (runBlock sqSetupB (M, f)).2 (7 : Fin 32) = memLoad32 M (f (20 : Fin 32) + 0) ∧
    (runBlock sqSetupB (M, f)).2 (28 : Fin 32) = memLoad32 M (f (22 : Fin 32) + 0) ∧
    (runBlock sqSetupB (M, f)).2 a6 = f (20 : Fin 32) + 4 ∧
    (runBlock sqSetupB (M, f)).2 (17 : Fin 32) = f sp + 0x10 ∧
    (runBlock sqSetupB (M, f)).2 (5 : Fin 32) = f (22 : Fin 32) + 4 ∧
    (runBlock sqSetupB (M, f)).2 (6 : Fin 32) = 12 ∧
    ∀ q, sqSetupKeep q = true → (runBlock sqSetupB (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, sqSetupB]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp +decide only [upd, ↓reduceIte, hz]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp only [upd, h0, ite_false, pkeep_ne (r := 5) hq rfl, pkeep_ne (r := 6) hq rfl, pkeep_ne (r := 7) hq rfl,
        pkeep_ne (r := a6) hq rfl, pkeep_ne (r := 17) hq rfl, pkeep_ne (r := 21) hq rfl, pkeep_ne (r := 28) hq rfl,
        pkeep_ne (r := 29) hq rfl, pkeep_ne (r := 30) hq rfl]

theorem sqSetupB_ok {M : Word → BitVec 8} {f : Fin 32 → Word} {base : Word} {len : Nat}
    (h20 : (f (20 : Fin 32) + 0).toNat % 4 = 0) (h22 : (f (22 : Fin 32) + 0).toNat % 4 = 0) :
    BlockOk base len sqSetupB (M, f) := by
  simp +decide only [BlockOk, BInstr.ok, BInstr.run, sqSetupB, upd, ↓reduceIte, and_true, true_and]
  exact ⟨h20, h22⟩

/-- Where `square_montgomery_form::<12>` runs: its code and its callees' at
their offsets, the 0xF0 bytes of stack below `sp0` that it, `borrowing_sub`,
and `Uint<12>::select` use, and the result, the operand, and the modulus,
aligned and apart from what each must not touch. -/
structure SQEnv (M : Word → BitVec 8) (P sp0 out xp np : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P sqMont12Code
  save : CodeIn M (P + 0xBFFA) mulMont12SaveCode
  restore : CodeIn M (P + 0xC048) mulMont12RestoreCode
  mset : CodeIn M (P + 0xC754) memsetCode
  bsub : CodeIn M (sqBsub P) borrowingSubCode
  sel : CodeIn M (P + 0xFFFFF5BE) uintSelect12Code
  stub : CodeIn M (P + 0xC7BC) memcpyStubCode
  body : CodeIn M (P + 0xC7C4) memcpyBodyCode
  step : CodeIn M (P + 0xC5AC) uintSelect12StepCode
  hsp : sp0.toNat % 4 = 0
  hS : 0xF0 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hxp : xp.toNat % 4 = 0
  hnp : np.toNat % 4 = 0
  hwo : out.toNat + 48 < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFF10) 0xF0 P sqMont12Code.length
  sGS : Sep (sp0 + 0xFFFFFF10) 0xF0 (P + 0xBFFA) mulMont12SaveCode.length
  sGR : Sep (sp0 + 0xFFFFFF10) 0xF0 (P + 0xC048) mulMont12RestoreCode.length
  sGM : Sep (sp0 + 0xFFFFFF10) 0xF0 (P + 0xC754) memsetCode.length
  sGB : Sep (sp0 + 0xFFFFFF10) 0xF0 (sqBsub P) borrowingSubCode.length
  sGL : Sep (sp0 + 0xFFFFFF10) 0xF0 (P + 0xFFFFF5BE) uintSelect12Code.length
  sGU : Sep (sp0 + 0xFFFFFF10) 0xF0 (P + 0xC7BC) memcpyStubCode.length
  sGY : Sep (sp0 + 0xFFFFFF10) 0xF0 (P + 0xC7C4) memcpyBodyCode.length
  sGP : Sep (sp0 + 0xFFFFFF10) 0xF0 (P + 0xC5AC) uintSelect12StepCode.length
  sOG : Sep out 48 (sp0 + 0xFFFFFF10) 0xF0
  sOC : Sep out 48 P sqMont12Code.length
  sOR : Sep out 48 (P + 0xC048) mulMont12RestoreCode.length
  sOL : Sep out 48 (P + 0xFFFFF5BE) uintSelect12Code.length
  sOY : Sep out 48 (P + 0xC7C4) memcpyBodyCode.length
  sXG : Sep xp 48 (sp0 + 0xFFFFFF10) 0xF0
  sNG : Sep np 48 (sp0 + 0xFFFFFF10) 0xF0

theorem SQEnv.frame {M : Word → BitVec 8} {P sp0 out xp np : Word} (E : SQEnv M P sp0 out xp np)
    {b : Word} {l : Nat} (h : Sep (sp0 + 0xFFFFFF10) 0xF0 b l) : Sep (sp0 + 0xFFFFFF60) 0xA0 b l := by
  rw [(frameA0 sp0 E.hS).2.1]; exact h.sub (by decide)

/-- **The prologue of `square_montgomery_form::<12>`**, from 0 to the outer
loop at 0x42: open the frame at `F`, save registers, zero the accumulator
at `F + 0xC`, and set up the first pass. -/
theorem sq_pro (m : Machine) {P sp0 out xp np K : Word} (E : SQEnv m.mem P sp0 out xp np) (hpc : m.pc = P)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp) (ha2 : reg m a2 = np) (ha3 : reg m a3 = K)
    (hsp : reg m sp = sp0) :
    ∃ n M, Steps m n ∧ St M P n 0x42 (reg n) ∧
      (∀ x, Sep (sp0 + 0xFFFFFF60) 0xA0 x 1 → M x = m.mem x) ∧
      (∀ r o, (r, o) ∈ mmPs → memLoad32 M (sp0 + 0xFFFFFF60 + o) = reg m r) ∧
      accV M (sp0 + 0xFFFFFF60 + 0xC) 12 = 0 ∧
      reg n sp = sp0 + 0xFFFFFF60 ∧ reg n (21 : Fin 32) = 0 ∧ reg n (30 : Fin 32) = BitVec.ofNat 32 0 ∧
      reg n (20 : Fin 32) = xp ∧ reg n (7 : Fin 32) = memLoad32 m.mem xp ∧
      reg n (28 : Fin 32) = memLoad32 m.mem np ∧ reg n (19 : Fin 32) = K ∧
      reg n (5 : Fin 32) = np + BitVec.ofNat 32 (4 * (0 + 1)) ∧
      reg n (17 : Fin 32) = sp0 + 0xFFFFFF60 + 0xC + BitVec.ofNat 32 (4 * (0 + 1)) ∧
      reg n a6 = xp + BitVec.ofNat 32 (4 * (0 + 1)) ∧ reg n (29 : Fin 32) = 0 ∧
      reg n (6 : Fin 32) = 12 ∧ reg n (18 : Fin 32) = out ∧ reg n (22 : Fin 32) = np ∧
      ∀ q, q.val ∈ [3, 4, 27] → reg n q = reg m q := by
  obtain ⟨hG, hFG, hFw⟩ := frameA0 sp0 E.hS
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hFa : (sp0 + 0xFFFFFF60).toNat % 4 = 0 := aligned_add E.hsp (k := 0xFFFFFF60) (by decide)
  have sFC := E.frame E.sGC; have sFS := E.frame E.sGS; have sFM := E.frame E.sGM
  obtain ⟨m1, d1, u1⟩ := s0.aluImm E.code sq_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF60) sp = sp0 + 0xFFFFFF60 := by
    simp +decide [upd, hsp]; rfl
  obtain ⟨m2, c2, u2⟩ := u1.callSave E.code sq_at_2 sq_at_6 (b := P + 0xBFFA)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P E.hP 0xBFFA (by decide))
    (even_at P E.hP 0xA (by decide)) E.save mmSave_shape (by decide) (fun q hq => by
      rw [sp1]
      simp only [mmPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, aligned_add hFa (by decide), sFS.sub (by decide)⟩)
  rw [sp1] at u2
  have codeS : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (sp0 + 0xFFFFFF60) 0xA0 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFF60) 0xA0 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have I2 : ∀ x, Sep (sp0 + 0xFFFFFF60) 0xA0 x 1 →
      saveMem m.mem (sp0 + 0xFFFFFF60) (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF60)) mmPs x = m.mem x :=
    fun x hx => saveMem_outside mmPs fun q hq => by
      simp only [mmPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hx.sub (by decide)
  have r2 : ∀ q, q ≠ sp → q ≠ t0 → reg m2 q = reg m q := fun q q1 q2 => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q1, q2]
  have sp2 : reg m2 sp = sp0 + 0xFFFFFF60 := by rw [u2.regs]; simp +decide [upd]; exact sp1
  -- keep the arguments
  have hc2 := codeS E.code sFC I2
  obtain ⟨m3, c3, u3⟩ := St.block sqProB u2.self hc2 sqProB_end (by
    simp only [BlockOk, BInstr.ok, sqProB]; exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial⟩)
  obtain ⟨em3, p19, p22, p20, p18, pa0, pa2, pa1, pk⟩ := sqProB_run (M := saveMem m.mem (sp0 + 0xFFFFFF60)
    (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF60)) mmPs) (f := reg m2) u2.self.zero
  rw [em3] at u3
  have g3 : ∀ q, reg m3 q = (runBlock sqProB (saveMem m.mem (sp0 + 0xFFFFFF60)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF60)) mmPs, reg m2)).2 q := u3.regs
  -- zero the accumulator
  obtain ⟨m4, c4, u4, a04, fr4⟩ := u3.self.memsetW (B := P + 0xC754) (w := 12) (dst := sp0 + 0xFFFFFF60 + 0xC)
    (even_at P E.hP 0xC754 (by decide)) hc2 (codeS E.mset sFM I2) sq_at_1a sq_at_1e
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P E.hP (0x1A + 8) (by decide)) (by decide)
    (by rw [BitVec.toNat_add]; have : (0xC : Word).toNat = 0xC := rfl; rw [this]; omega) (by decide)
    (aligned_add hFa (k := 0xC) (by decide)) (sFM.sub (c := 0xC) (l := 48) (by decide))
    (by rw [g3, pa0, sp2]) (by rw [g3, pa1]) (by rw [g3, pa2]; rfl)
  obtain ⟨M4, hM4⟩ : ∃ M4, fillWords (saveMem m.mem (sp0 + 0xFFFFFF60)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF60)) mmPs) (sp0 + 0xFFFFFF60 + 0xC) 0 12 = M4 := ⟨_, rfl⟩
  rw [hM4] at u4
  have I4 : ∀ x, Sep (sp0 + 0xFFFFFF60) 0xA0 x 1 → M4 x = m.mem x := fun x hx => by
    rw [← hM4, fillWords_outside (dst := sp0 + 0xFFFFFF60 + 0xC) 12 (hx.sub (c := 0xC) (l := 48) (by decide)), I2 x hx]
  have k4 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg m4 q = reg m3 q := fr4
  have e20 : reg m4 (20 : Fin 32) = xp := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3, p20,
      r2 _ (by decide) (by decide), ha1]
  have e22 : reg m4 (22 : Fin 32) = np := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3, p22,
      r2 _ (by decide) (by decide), ha2]
  have sp4 : reg m4 sp = sp0 + 0xFFFFFF60 := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g3,
      pk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp2]
  -- the inline setup
  have hc4 := codeS E.code sFC I4
  obtain ⟨m5, c5, u5⟩ := St.block sqSetupB u4.self hc4 sqSetupB_end
    (sqSetupB_ok (by rw [e20, add_lit_zero]; exact E.hxp) (by rw [e22, add_lit_zero]; exact E.hnp))
  obtain ⟨em5, s21, s29, s30, s7, s28, sa6, s17, s5, s6, sk⟩ := sqSetupB_run (M := M4) (f := reg m4) u4.self.zero
  rw [em5] at u5
  have g5 : ∀ q, reg m5 q = (runBlock sqSetupB (M4, reg m4)).2 q := u5.regs
  obtain ⟨m7, d7, u7⟩ := u5.self.notTaken hc4 0x42 sq_at_3e (by decide) (by rw [g5, s6, u5.self.zero]; decide)
  have g7 : ∀ q, reg m7 q = reg m5 q := u7.regs
  have kk : ∀ q, sqSetupKeep q = true → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra →
      reg m7 q = (runBlock sqProB (saveMem m.mem (sp0 + 0xFFFFFF60)
        (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF60)) mmPs, reg m2)).2 q :=
    fun q hs h2 h3 h4 h5' h6 hr => by rw [g7 q, g5, sk q hs, k4 q h2 h3 h4 h5' h6 hr, g3]
  have hxF : Sep (sp0 + 0xFFFFFF60) 0xA0 xp 4 := (E.frame E.sXG.symm).subR (c := 0) (l := 4) (by decide) |> fun h => by
    rwa [add_ofNat_zero] at h
  have hnF : Sep (sp0 + 0xFFFFFF60) 0xA0 np 4 := (E.frame E.sNG.symm).subR (c := 0) (l := 4) (by decide) |> fun h => by
    rwa [add_ofNat_zero] at h
  refine ⟨m7, M4, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (.single d7))))), u7.self, I4,
    fun r o hm => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · have slot : ∀ (r : Fin 32) (o : Word), (r, o) ∈ mmPs → 0x70 ≤ o.toNat → o.toNat + 4 ≤ 0xA0 →
        (∀ p ∈ mmPs, p = (r, o) ∨ ((p.2.toNat + 4 ≤ o.toNat ∨ o.toNat + 4 ≤ p.2.toNat) ∧
          p.2.toNat + 4 ≤ 2 ^ 32 ∧ o.toNat + 4 ≤ 2 ^ 32)) → r ≠ sp →
        memLoad32 M4 (sp0 + 0xFFFFFF60 + o) = reg m r := fun r o hm h1 h2 hp hr => by
      have hFo : sp0 + 0xFFFFFF60 + BitVec.ofNat 32 o.toNat = sp0 + 0xFFFFFF60 + o := by rw [ofNat_toNat_self]
      rw [← hM4, ← hFo, fillWords_load_sep (dst := sp0 + 0xFFFFFF60 + 0xC) (by
        have := sep_offsets (sp0 + 0xFFFFFF60) (c := 0xC) (n := 48) (d := o.toNat) (k := 4) (.inl (by omega))
          (by omega) (by omega)
        exact this), hFo, saveMem_slot mmPs _ hm hp, upd_ne (by
          intro h; apply hr; exact Fin.ext (by
            simp only [mmPs, List.mem_cons, List.mem_nil_iff, or_false] at hm
            rcases hm with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' <;>
              (rw [Prod.mk.injEq] at h'; rw [h'.1] at h; exact absurd h (by decide)))) hr]
    simp only [mmPs, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' <;>
      (rw [Prod.mk.injEq] at h'; obtain ⟨rfl, rfl⟩ := h'; exact slot _ _ (by decide) (by decide) (by decide)
        (by decide) (by decide))
  · have hacw : (sp0 + 0xFFFFFF60 + 0xC).toNat + 4 * 12 ≤ 2 ^ 32 := by
      rw [BitVec.toNat_add]; have : (0xC : Word).toNat = 0xC := rfl; rw [this]; omega
    rw [← hM4]
    exact accV_zero 12 fun i hi => fillWords_load 12 i hi hacw
  · rw [g7, g5, sk _ rfl, sp4]
  · rw [g7, g5, s21]
  · rw [g7, g5, s30]
  · rw [g7, g5, sk _ rfl, e20]
  · rw [g7, g5, s7, e20, add_lit_zero, ← hM4,
      fillWords_load_sep (dst := sp0 + 0xFFFFFF60 + 0xC) ((hxF.sub (c := 0xC) (l := 48) (by decide))),
      load_frame I2 hxF]
  · rw [g7, g5, s28, e22, add_lit_zero, ← hM4,
      fillWords_load_sep (dst := sp0 + 0xFFFFFF60 + 0xC) ((hnF.sub (c := 0xC) (l := 48) (by decide))),
      load_frame I2 hnF]
  · rw [kk _ rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), p19,
      r2 _ (by decide) (by decide), ha3]
  · rw [g7, g5, s5, e22]; rfl
  · have e : (0xC : Word) + BitVec.ofNat 32 (4 * (0 + 1)) = 0x10 := by decide
    rw [g7, g5, s17, sp4, BitVec.add_assoc (sp0 + 0xFFFFFF60) 0xC, e]
  · rw [g7, g5, sa6, e20]; rfl
  · rw [g7, g5, s29]
  · rw [g7, g5, s6]
  · rw [kk _ rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), p18,
      r2 _ (by decide) (by decide), ha0]
  · rw [g7, g5, sk _ rfl, e22]
  · have key : ∀ q : Fin 32, q.val ∈ [3, 4, 27] → sqSetupKeep q = true ∧ q ≠ a2 ∧ q ≠ a3 ∧
        q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ ra ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ (18 : Fin 32) ∧ q ≠ (19 : Fin 32) ∧
        q ≠ (20 : Fin 32) ∧ q ≠ (22 : Fin 32) ∧ q ≠ sp ∧ q ≠ t0 := by decide
    obtain ⟨hs, h2, h3, h4, h5', h6, hr, h0, h1, h18, h19, h20, h22, hsp', ht0⟩ := key q hq
    rw [kk q hs h2 h3 h4 h5' h6 hr, pk q h0 h1 h2 h18 h19 h20 h22, r2 q hsp' ht0]

end C3.RV32
