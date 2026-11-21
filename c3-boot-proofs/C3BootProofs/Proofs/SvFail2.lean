import C3BootProofs.Proofs.SvFail

/-!
# `sigstore::verify`: more error exits

The exits at 0xEE2 (`Err(0x10)`), 0xEF0 (`Err(0x17)` as one halfword), and
0x2C60 (`Err` with the code in `s0`).
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

/-- The saves survive two byte stores at `out`. -/
theorem saves_out2 {B out : Word} {v : Nat → Word} {M : Word → BitVec 8} {b0 b1 : BitVec 8} (hO : SvOut B out)
    (V : SvSaves B M v) :
    ∀ k, k < 13 → memLoad32 (memStore8 (memStore8 M out b0) (out + 1) b1) (B + BitVec.ofNat 32 (0x382C - 4 * k)) = v k :=
  fun k hk => by
    have sOS := out_sep B out hO
    rw [← V k hk]
    have hs : Sep out 2 (B + BitVec.ofNat 32 (0x382C - 4 * k)) 4 := by
      have := sOS.symm.sub (c := 0x30 - 4 * k) (l := 4) (by omega)
      rw [add_ofNat_assoc, show 0x37FC + (0x30 - 4 * k) = 0x382C - 4 * k by omega] at this
      exact this.symm
    exact memLoad32_congr fun j hj => by
      have h1 : B + BitVec.ofNat 32 (0x382C - 4 * k) + BitVec.ofNat 32 j ≠ out + 1 := fun e => hs 1 (by decide) j hj e.symm
      have h0 : B + BitVec.ofNat 32 (0x382C - 4 * k) + BitVec.ofNat 32 j ≠ out := fun e =>
        hs 0 (by decide) j hj (by rw [add_ofNat_zero]; exact e.symm)
      rw [memStore8_ne h1, memStore8_ne h0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The error exit at 0xEE2**: `Err(0x10)`. -/
theorem sv_fail_ee2 {B out : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x3830) (E : SvCode n.mem)
    (s : St n.mem SV n 0xEE2 (reg n)) (t : Steps n0 n) (fR : ∀ x, SvR B x → n.mem x = n0.mem x)
    (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (hout : reg n (18 : Fin 32) = out) (hO : SvOut B out) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) : SvErrRet B out v n0 := by
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0xEE4) [.aluImm .add a0 x0 0x10] E.self (by decide) ⟨trivial, trivial⟩
  have r1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs]; simp only [runBlock, BInstr.run]; exact upd_ne' hq s.zero
  have m1 : n1.mem = n.mem := u1.mem
  exact sv_fail_ee4 F (by rw [m1]; exact E) ⟨u1.pc, rfl, fun _ => rfl⟩ (t.trans c1)
    (fun x hx => by rw [m1, fR x hx]) (by rw [m1]; exact V) hret (by rw [r1 sp (by decide), rsp])
    (by rw [r1 _ (by decide), hout]) hO (by rw [r1 _ (by decide), r3]) (by rw [r1 _ (by decide), r4])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The error exit at 0xEF0**: store `Err(0x17)` at `out` as one halfword,
and return. -/
theorem sv_fail_ef0 {B out : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x3830) (E : SvCode n.mem)
    (s : St n.mem SV n 0xEF0 (reg n)) (t : Steps n0 n) (fR : ∀ x, SvR B x → n.mem x = n0.mem x)
    (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (hout : reg n (18 : Fin 32) = out) (hO : SvOut B out) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) : SvErrRet B out v n0 := by
  have hz := s.zero
  have sOC := hO.code
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0xEF6) [.lui a0 0x1000, .aluImm .add a0 a0 0x701] E.self (by decide)
    ⟨trivial, trivial, trivial⟩
  have a01 : reg n1 a0 = 0x1701 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte, aluEval]
  have r1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs]; simp only [runBlock, BInstr.run]; rw [updz (by rfl) hq, updz hz hq]
  have M1 : n1.mem = n.mem := u1.mem
  have s1 : St n.mem SV n1 0xEF6 (reg n1) := ⟨u1.pc, M1, fun _ => rfl⟩
  obtain ⟨n2, d2, u2⟩ := s1.jump E.self sv_at_ef6 (off' := 0x2A88) (by decide) (by rw [s1.pc]; decide)
  have s2 : St n.mem SV n2 0x2A88 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have e0 : reg n2 (18 : Fin 32) + 0 = out := by rw [u2.regs, r1 _ (by decide), hout]; exact BitVec.add_zero _
  obtain ⟨n3, d3, u3⟩ := s2.sh E.self sv_at_2a88 (off' := 0x2A8C) (by decide) (by rw [e0]; exact hO.al)
  rw [e0, u2.regs, a01] at u3
  have M3 : n3.mem = memStore8 (memStore8 n.mem out 1) (out + 1) 0x17 := by rw [u3.mem]; rfl
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

def svE2c60 : List BInstr := [.aluImm .add a0 x0 0x1, .sb (18 : Fin 32) a0 0x0, .sb (18 : Fin 32) (8 : Fin 32) 0x1]

set_option maxRecDepth 100000 in
theorem svE2c60_end : blockEnd sigstoreVerifyCode 0x2C60 svE2c60 = some 0x2C6A := by decide

set_option maxHeartbeats 4000000 in
/-- **The error exit at 0x2C60**: store `Err` and the code in `s0` at `out`,
and return. -/
theorem sv_fail_2c60 {B out : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x3830) (E : SvCode n.mem)
    (s : St n.mem SV n 0x2C60 (reg n)) (t : Steps n0 n) (fR : ∀ x, SvR B x → n.mem x = n0.mem x)
    (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (hout : reg n (18 : Fin 32) = out) (hO : SvOut B out) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) : SvErrRet B out v n0 := by
  have hz := s.zero
  have e0 : out + 0 = out := BitVec.add_zero _
  have sOC := hO.code
  obtain ⟨n1, c1, u1⟩ := s.block svE2c60 E.self svE2c60_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, svE2c60]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [hout, e0]
    exact ⟨sOC.sub (c := 0) (l := 1) (by decide) |> fun h => by rwa [add_ofNat_zero] at h,
      sOC.sub (c := 1) (l := 1) (by decide)⟩)
  have m1 : (runBlock svE2c60 (n.mem, reg n)).1 = memStore8 (memStore8 n.mem out 1) (out + 1)
      ((reg n 8).extractLsb' 0 8) := by
    simp +decide only [runBlock, BInstr.run, svE2c60, upd, ↓reduceIte]; rw [hout, e0]; rfl
  have r1 : ∀ q, q ≠ a0 → (runBlock svE2c60 (n.mem, reg n)).2 q = reg n q := fun q hq => by
    simp only [runBlock, BInstr.run, svE2c60]; exact updz hz hq
  have M1 : n1.mem = memStore8 (memStore8 n.mem out 1) (out + 1) ((reg n 8).extractLsb' 0 8) := u1.mem.trans m1
  have C1 : CodeIn n1.mem SV sigstoreVerifyCode := by
    rw [M1]; exact (E.self.store8 (by have := sOC.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this)).store8
      (sOC.sub (c := 1) (l := 1) (by decide))
  have s1 : St n1.mem SV n1 0x2C6A (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  obtain ⟨n2, d2, u2⟩ := s1.jump C1 sv_at_2c6a (off' := 0x970) (by decide) (by rw [s1.pc]; decide)
  have s2 : St n1.mem SV n2 0x970 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  refine sv_ret_err (n := n2) (M := n1.mem) F C1 s2 (t.trans (c1.trans (.single d2))) (by rw [M1]; exact saves_out2 hO V)
    hret (by rw [u2.regs, u1.regs, r1 sp (by decide), rsp]) (by rw [u2.regs, u1.regs, r1 3 (by decide), r3])
    (by rw [u2.regs, u1.regs, r1 4 (by decide), r4]) ?_ ?_
  · rw [M1, memStore8_ne (out_ne1 out), memStore8_same]
  · intro x hx h0 h1; rw [M1, memStore8_ne h1, memStore8_ne h0, fR x hx]

end C3.RV32.Sv
