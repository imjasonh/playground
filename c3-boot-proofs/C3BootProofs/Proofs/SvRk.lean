import C3BootProofs.Proofs.SvCs

/-!
# `sigstore::verify`: the log entry

After the checkpoint, `sigstore::verify` checks the entry's index against
the checkpoint's size, rebuilds the entry's leaf hash, and checks the
inclusion proof.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

/-- **The error exit at 0x3122**: the entry's index isn't below the
checkpoint's size, `Err(0x1B)`. -/
theorem sv_fail_3122 {B out : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x3830) (E : SvCode n.mem)
    (s : St n.mem SV n 0x3122 (reg n)) (t : Steps n0 n) (fR : ∀ x, SvR B x → n.mem x = n0.mem x)
    (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (hout : reg n (18 : Fin 32) = out) (hO : SvOut B out) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) : SvErrRet B out v n0 := by
  have hz := s.zero
  have sOC := hO.code
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x3128) [.lui a0 0x2000, .aluImm .add a0 a0 0xFFFFFB01] E.self (by decide)
    ⟨trivial, trivial, trivial⟩
  have a01 : reg n1 a0 = 0x1B01 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte, aluEval]
  have r1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs]; simp only [runBlock, BInstr.run]; rw [updz (by rfl) hq, updz hz hq]
  have M1 : n1.mem = n.mem := u1.mem
  have s1 : St n.mem SV n1 0x3128 (reg n1) := ⟨u1.pc, M1, fun _ => rfl⟩
  obtain ⟨n2, d2, u2⟩ := s1.jump E.self sv_at_3128 (off' := 0x2A88) (by decide) (by rw [s1.pc]; decide)
  have s2 : St n.mem SV n2 0x2A88 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have e0 : reg n2 (18 : Fin 32) + 0 = out := by rw [u2.regs, r1 _ (by decide), hout]; exact BitVec.add_zero _
  obtain ⟨n3, d3, u3⟩ := s2.sh E.self sv_at_2a88 (off' := 0x2A8C) (by decide) (by rw [e0]; exact hO.al)
  rw [e0, u2.regs, a01] at u3
  have M3 : n3.mem = memStore8 (memStore8 n.mem out 1) (out + 1) 0x1B := by rw [u3.mem]; rfl
  have C3 : CodeIn n3.mem SV sigstoreVerifyCode := by
    rw [M3]; exact (E.self.store8 (by have := sOC.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this)).store8
      (sOC.sub (c := 1) (l := 1) (by decide))
  have s3 : St n3.mem SV n3 0x2A8C (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  obtain ⟨n4, d4, u4⟩ := s3.jump C3 sv_at_2a8c (off' := 0x970) (by decide) (by rw [s3.pc]; decide)
  have s4 : St n3.mem SV n4 0x970 (reg n4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
  refine sv_ret_err (n := n4) (M := n3.mem) F C3 s4
    (t.trans (c1.trans ((Steps.single d2).trans ((Steps.single d3).trans (.single d4)))))
    (by rw [M3]; exact saves_out2 hO V) hret
    (by rw [u4.regs, u3.regs, u2.regs, r1 sp (by decide), rsp]) (by rw [u4.regs, u3.regs, u2.regs, r1 3 (by decide), r3])
    (by rw [u4.regs, u3.regs, u2.regs, r1 4 (by decide), r4]) ?_ ?_
  · rw [M3, memStore8_ne (out_ne1 out), memStore8_same]
  · intro x hx h0 h1; rw [M3, memStore8_ne h1, memStore8_ne h0, fR x hx]

end C3.RV32.Sv
