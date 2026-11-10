import C3BootProofs.Proofs.FieldArith
import C3BootProofs.Proofs.FieldDecode
import C3BootProofs.Proofs.Parse

/-!
# `sub_inner`, as compiled

`p256::arithmetic::field::field_impl::sub_inner` subtracts the P-256
modulus from a 9-limb number with nine calls to `borrowing_sub`, then adds
the modulus back under the final borrow mask (`addBack`). Its frame is 0x30
bytes; each `borrowing_sub` call also writes the word 4 bytes below it.
-/

namespace C3.RV32

open C3.Image

theorem alu_zadd (x : Word) : aluEval .add 0#32 x = x := BitVec.zero_add x

/-- `borrowing_sub`'s offset from `sub_inner`. -/
abbrev siBsub (P : Word) : Word := P + 0xFFFF1162

/-- A call from `sub_inner` to `borrowing_sub` with `sp` at `F`. -/
theorem si_bsub {Mx : Word → BitVec 8} {P F : Word} {m : Machine} {off : Nat} {f : Fin 32 → Word}
    {imm o : Word} (s : St Mx P m off f) (hc : CodeIn Mx P subInnerCode)
    (hb : CodeIn Mx (siBsub P) borrowingSubCode) (hP : P.toNat % 2 = 0)
    (h1 : fetchRel subInnerCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel subInnerCode (off + 4) = some (.jalr ra ra o, 4))
    (hcb : P + BitVec.ofNat 32 off + imm + o = siBsub P) (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : f sp = F) (hF : F.toNat % 4 = 0) (hsep : Sep (F + 0xFFFFFFFC) 4 (siBsub P) borrowingSubCode.length) :
    ∃ m', Steps m m' ∧ St m'.mem P m' (off + 8) (reg m') ∧
      reg m' a0 = bsubD (f a0) (f a1) (f a2) ∧ reg m' a1 = bsubB (f a0) (f a1) (bsubD (f a0) (f a1) (f a2)) ∧
      reg m' sp = F ∧ (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg m' q = f q) ∧
      ∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → m'.mem x = Mx x := by
  have hev : (siBsub P).toNat % 2 = 0 := even_at P hP 0xFFFF1162 (by decide)
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hcb hev
  have hz := s.zero
  have r1 : ∀ q, q ≠ ra → reg m1 q = f q := fun q hq => by
    rw [regs1]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, hq]
  obtain ⟨m2, c2, pc2, a02, a12, sp2, fr2, mem2⟩ := borrowingSub_correct m1 (siBsub P)
    (P + BitVec.ofNat 32 (off + 8)) (f a0) (f a1) (f a2) (by show CodeIn m1.mem _ _; rw [mem1]; exact hb) pc1
    (r1 a0 (by decide)) (r1 a1 (by decide)) (r1 a2 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hl) (by rw [r1 sp (by decide), hsp]; exact hF) (by rw [r1 sp (by decide), hsp]; exact hsep)
  rw [r1 sp (by decide), hsp] at sp2 mem2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, a02, a12, sp2, fun q q0 q1 q2 q3 q4 qr => ?_,
    fun x hx => by rw [mem2 x hx, mem1]⟩
  rw [fr2 q q0 q1 q2 q3 q4, r1 q qr]

/-- One of `sub_inner`'s rounds 1 to 8: keep the last difference in `K`, load
limb `i` of both operands, move the borrow mask to `a2`, and call
`borrowing_sub`. -/
theorem si_round {Mx : Word → BitVec 8} {P F lp rp : Word} {m : Machine} {off : Nat} {f : Fin 32 → Word}
    {K : Fin 32} {i : Nat} {imm o : Word} (s : St Mx P m off f) (hc : CodeIn Mx P subInnerCode)
    (hb : CodeIn Mx (siBsub P) borrowingSubCode) (hP : P.toNat % 2 = 0)
    (i1 : fetchRel subInnerCode off = some (.alu .add K x0 a0, 2))
    (i2 : fetchRel subInnerCode (off + 2) = some (.load .lw a0 (8 : Fin 32) (BitVec.ofNat 32 (4 * i)), 2))
    (i3 : fetchRel subInnerCode (off + 2 + 2) = some (.load .lw a2 (9 : Fin 32) (BitVec.ofNat 32 (4 * i)), 2))
    (i4 : fetchRel subInnerCode (off + 2 + 2 + 2) = some (.alu .add a3 x0 a1, 2))
    (i5 : fetchRel subInnerCode (off + 2 + 2 + 2 + 2) = some (.alu .add a1 x0 a2, 2))
    (i6 : fetchRel subInnerCode (off + 2 + 2 + 2 + 2 + 2) = some (.alu .add a2 x0 a3, 2))
    (i7 : fetchRel subInnerCode (off + 2 + 2 + 2 + 2 + 2 + 2) = some (.auipc ra imm, 4))
    (i8 : fetchRel subInnerCode (off + 2 + 2 + 2 + 2 + 2 + 2 + 4) = some (.jalr ra ra o, 4))
    (hcb : P + BitVec.ofNat 32 (off + 2 + 2 + 2 + 2 + 2 + 2) + imm + o = siBsub P)
    (hl : (P + BitVec.ofNat 32 (off + 2 + 2 + 2 + 2 + 2 + 2 + 8)).toNat % 2 = 0)
    (hK0 : K ≠ x0) (hKa : K ≠ a0 ∧ K ≠ a1 ∧ K ≠ a2 ∧ K ≠ a3) (hK8 : K ≠ (8 : Fin 32)) (hK9 : K ≠ (9 : Fin 32))
    (hKs : K ≠ sp) (hK4 : K ≠ a4) (hKr : K ≠ ra)
    (hs0 : f (8 : Fin 32) = lp) (hs1 : f (9 : Fin 32) = rp) (hsp : f sp = F) (hF : F.toNat % 4 = 0)
    (hlp : (lp + BitVec.ofNat 32 (4 * i)).toNat % 4 = 0) (hrp : (rp + BitVec.ofNat 32 (4 * i)).toNat % 4 = 0)
    (hsep : Sep (F + 0xFFFFFFFC) 4 (siBsub P) borrowingSubCode.length) :
    ∃ m', Steps m m' ∧ St m'.mem P m' (off + 2 + 2 + 2 + 2 + 2 + 2 + 8) (reg m') ∧ reg m' K = f a0 ∧
      reg m' a0 = bsubD (memLoad32 Mx (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 Mx (rp + BitVec.ofNat 32 (4 * i)))
        (f a1) ∧
      reg m' a1 = bsubB (memLoad32 Mx (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 Mx (rp + BitVec.ofNat 32 (4 * i)))
        (bsubD (memLoad32 Mx (lp + BitVec.ofNat 32 (4 * i))) (memLoad32 Mx (rp + BitVec.ofNat 32 (4 * i))) (f a1)) ∧
      reg m' sp = F ∧
      (∀ q, q ≠ K → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → reg m' q = f q) ∧
      ∀ x, Sep (F + 0xFFFFFFFC) 4 x 1 → m'.mem x = Mx x := by
  have hz := s.zero
  obtain ⟨m1, d1, u1⟩ := s.alu hc i1 (off' := off + 2) (ofNat_add_ofNat off 2)
  obtain ⟨m2, d2, u2⟩ := u1.lw hc i2 (off' := off + 2 + 2) (ofNat_add_ofNat _ 2)
    (by rw [updz hz (Ne.symm hK8), hs0]; exact hlp)
  obtain ⟨m3, d3, u3⟩ := u2.lw hc i3 (off' := off + 2 + 2 + 2) (ofNat_add_ofNat _ 2)
    (by rw [updz (by simp) (show (9 : Fin 32) ≠ a0 by decide), updz hz (Ne.symm hK9), hs1]; exact hrp)
  obtain ⟨m4, d4, u4⟩ := u3.alu hc i4 (off' := off + 2 + 2 + 2 + 2) (ofNat_add_ofNat _ 2)
  obtain ⟨m5, d5, u5⟩ := u4.alu hc i5 (off' := off + 2 + 2 + 2 + 2 + 2) (ofNat_add_ofNat _ 2)
  obtain ⟨m6, d6, u6⟩ := u5.alu hc i6 (off' := off + 2 + 2 + 2 + 2 + 2 + 2) (ofNat_add_ofNat _ 2)
  have n0 : a0 ≠ K := Ne.symm hKa.1
  have n1 : a1 ≠ K := Ne.symm hKa.2.1
  have n2 : a2 ≠ K := Ne.symm hKa.2.2.1
  have n3 : a3 ≠ K := Ne.symm hKa.2.2.2
  have n8 : (8 : Fin 32) ≠ K := Ne.symm hK8
  have n9 : (9 : Fin 32) ≠ K := Ne.symm hK9
  have ns : sp ≠ K := Ne.symm hKs
  have fz : f 0 = 0 := hz
  have e0 : reg m6 a0 = memLoad32 Mx (lp + BitVec.ofNat 32 (4 * i)) := by
    rw [u6.regs]; simp +decide [upd, n8, hs0]
  have e1 : reg m6 a1 = memLoad32 Mx (rp + BitVec.ofNat 32 (4 * i)) := by
    rw [u6.regs]; simp +decide [upd, n9, hs1, alu_zadd]
  have e2 : reg m6 a2 = f a1 := by
    rw [u6.regs]; simp +decide [upd, n1, alu_zadd]
  have esp : reg m6 sp = F := by rw [u6.regs]; simp +decide [upd, ns, hsp]
  have eK : reg m6 K = f a0 := by
    rw [u6.regs]; simp +decide [upd, Ne.symm n0, Ne.symm n2, Ne.symm n3, Ne.symm n1, hK0, fz, alu_zadd]
  have fr6 : ∀ q, q ≠ K → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg m6 q = f q := fun q qK q0 q1 q2 q3 => by
    rw [u6.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, fz]
    · simp [upd, h0, qK, q0, q1, q2, q3]
  obtain ⟨m7, c7, u7, a07, a17, sp7, fr7, mem7⟩ := si_bsub u6.self hc hb hP i7 i8 hcb hl esp hF hsep
  rw [e0, e1, e2] at a07 a17
  refine ⟨m7, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 c7))))), u7, ?_, a07, a17, sp7,
    fun q qK q0 q1 q2 q3 q4 qr => ?_, mem7⟩
  · rw [fr7 K hKa.1 hKa.2.1 hKa.2.2.1 hKa.2.2.2 hK4 hKr, eK]
  · rw [fr7 q q0 q1 q2 q3 q4 qr, fr6 q qK q0 q1 q2 q3]

end C3.RV32
