import C3BootProofs.Proofs.SvEcdsa

/-!
# `sigstore::verify`: its other error exits

Besides 0x966, two error exits store `Err` themselves and jump to the
epilogue at 0x970: 0xEE4, with the code in `a0`, and 0x2A82, which stores
`Err(0x1D)` as one halfword.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

theorem St.sh {M : Word → BitVec 8} {base : Word} {m : Machine} {off : Nat} {f : Fin 32 → Word} {code : List Nat}
    (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {rs1 rs2 : Fin 32} {o len : Word} {off' : Nat}
    (hf : fetchRel code off = some (.store .sh rs1 rs2 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off')
    (hal : (f rs1 + o).toNat % 2 = 0) :
    ∃ m1, step m = some m1 ∧
      St (memStore8 (memStore8 M (f rs1 + o) (((f rs2).extractLsb' 0 16).extractLsb' 0 8)) (f rs1 + o + 1)
        (((f rs2).extractLsb' 0 16).extractLsb' 8 8)) base m1 off' f := by
  have ha : aligned (storeSize .sh) (reg m rs1 + o) = true := by
    unfold aligned storeSize; rw [s.regs, hal]; rfl
  refine ⟨Arch.setPc (store16 m (f rs1 + o) ((f rs2).extractLsb' 0 16)) (m.pc + len), ?_, ?_, ?_, ?_⟩
  · rw [step_code (s.codeAt hc) s.pc hf]
    unfold exec
    simp only [ha, Bool.not_true]
    rw [s.regs, s.regs]
    rfl
  · simp only [Machine.setPc_pc]; rw [s.pc, BitVec.add_assoc, hn]
  · rw [← s.mem]; rfl
  · intro r; rw [← s.regs r]; rfl

/-- The epilogue from 0x970 after the error's bytes are stored at `out`:
`SvErrRet`, when `out` holds 1 and nothing else outside the stack changed. -/
theorem sv_ret_err {B out : Word} {v : Nat → Word} {n0 n : Machine} {M : Word → BitVec 8} (F : Fr B 0x3830)
    (C : CodeIn M SV sigstoreVerifyCode) (s : St M SV n 0x970 (reg n)) (t : Steps n0 n)
    (hS : ∀ k, k < 13 → memLoad32 M (B + BitVec.ofNat 32 (0x382C - 4 * k)) = v k) (hret : v 0 &&& ~~~1 = v 0)
    (rsp : reg n sp = B + 0x21A0) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) (h1 : M out = 1)
    (fR : ∀ x, SvR B x → x ≠ out → x ≠ out + 1 → M x = n0.mem x) : SvErrRet B out v n0 := by
  obtain ⟨n', c', pc', mem', sp', sv', g', t'⟩ := sv_ret (v := v) C F s rsp hS hret
  exact ⟨n', t.trans c', pc', sp', sv', by rw [g', r3], by rw [t', r4], by rw [mem']; exact h1,
    fun x hx h0 h1' => by rw [mem']; exact fR x hx h0 h1'⟩

def svEe4 : List BInstr := [.aluImm .add a1 x0 0x1, .sb (18 : Fin 32) a1 0x0, .sb (18 : Fin 32) a0 0x1]

set_option maxRecDepth 100000 in
theorem svEe4_end : blockEnd sigstoreVerifyCode 0xEE4 svEe4 = some 0xEEE := by decide

theorem out_sep (B out : Word) (hO : SvOut B out) : Sep out 2 (B + BitVec.ofNat 32 0x37FC) 0x34 := by
  have := hO.stk.symm.sub (c := 0x1A0 + 0x37FC) (l := 0x34) (by decide)
  rw [show B + 0xFFFFFE60 + BitVec.ofNat 32 (0x1A0 + 0x37FC) = B + BitVec.ofNat 32 0x37FC by
    rw [BitVec.add_assoc]; rfl] at this
  exact this.symm

theorem out_ne1 (out : Word) : out ≠ out + 1 := by
  have := add_ofNat_ne out (c := 0) (d := 1) (by decide) (by decide) (by decide)
  rwa [add_ofNat_zero] at this

set_option maxHeartbeats 4000000 in
/-- **The error exit at 0xEE4**: store `Err` and the code in `a0` at `out`,
and return. -/
theorem sv_fail_ee4 {B out : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x3830) (E : SvCode n.mem)
    (s : St n.mem SV n 0xEE4 (reg n)) (t : Steps n0 n) (fR : ∀ x, SvR B x → n.mem x = n0.mem x)
    (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (hout : reg n (18 : Fin 32) = out) (hO : SvOut B out) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) : SvErrRet B out v n0 := by
  have hz := s.zero
  have e0 : out + 0 = out := BitVec.add_zero _
  have sOC := hO.code
  have sOS := out_sep B out hO
  obtain ⟨n1, c1, u1⟩ := s.block svEe4 E.self svEe4_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, svEe4]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [hout, e0]
    exact ⟨sOC.sub (c := 0) (l := 1) (by decide) |> fun h => by rwa [add_ofNat_zero] at h,
      sOC.sub (c := 1) (l := 1) (by decide)⟩)
  have m1 : (runBlock svEe4 (n.mem, reg n)).1 = memStore8 (memStore8 n.mem out 1) (out + 1)
      ((reg n a0).extractLsb' 0 8) := by
    simp +decide only [runBlock, BInstr.run, svEe4, upd, ↓reduceIte]; rw [hout, e0]; rfl
  have r1 : ∀ q, q ≠ a1 → (runBlock svEe4 (n.mem, reg n)).2 q = reg n q := fun q hq => by
    simp only [runBlock, BInstr.run, svEe4]; exact updz hz hq
  have M1 : n1.mem = memStore8 (memStore8 n.mem out 1) (out + 1) ((reg n a0).extractLsb' 0 8) := u1.mem.trans m1
  have C1 : CodeIn n1.mem SV sigstoreVerifyCode := by
    rw [M1]; exact (E.self.store8 (by have := sOC.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this)).store8
      (sOC.sub (c := 1) (l := 1) (by decide))
  have s1 : St n1.mem SV n1 0xEEE (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  obtain ⟨n2, d2, u2⟩ := s1.jump C1 sv_at_eee (off' := 0x970) (by decide) (by rw [s1.pc]; decide)
  have s2 : St n1.mem SV n2 0x970 (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have hS : ∀ k, k < 13 → memLoad32 n1.mem (B + BitVec.ofNat 32 (0x382C - 4 * k)) = v k := fun k hk => by
    rw [← V k hk, M1]
    have hs : Sep out 2 (B + BitVec.ofNat 32 (0x382C - 4 * k)) 4 := by
      have := sOS.symm.sub (c := 0x30 - 4 * k) (l := 4) (by omega)
      rw [add_ofNat_assoc, show 0x37FC + (0x30 - 4 * k) = 0x382C - 4 * k by omega] at this
      exact this.symm
    exact memLoad32_congr fun j hj => by
      have h1 : B + BitVec.ofNat 32 (0x382C - 4 * k) + BitVec.ofNat 32 j ≠ out + 1 := fun e => hs 1 (by decide) j hj e.symm
      have h0 : B + BitVec.ofNat 32 (0x382C - 4 * k) + BitVec.ofNat 32 j ≠ out := fun e =>
        hs 0 (by decide) j hj (by rw [add_ofNat_zero]; exact e.symm)
      rw [memStore8_ne h1, memStore8_ne h0]
  refine sv_ret_err (n := n2) (M := n1.mem) F C1 s2 (t.trans (c1.trans (.single d2))) hS hret
    (by rw [u2.regs, u1.regs, r1 sp (by decide), rsp]) (by rw [u2.regs, u1.regs, r1 3 (by decide), r3])
    (by rw [u2.regs, u1.regs, r1 4 (by decide), r4]) ?_ ?_
  · rw [M1, memStore8_ne (out_ne1 out), memStore8_same]
  · intro x hx h0 h1; rw [M1, memStore8_ne h1, memStore8_ne h0, fR x hx]

def svE2a : List BInstr := [.lui a0 0x2000, .aluImm .add a0 a0 0xFFFFFD01]

set_option maxRecDepth 100000 in
theorem svE2a_end : blockEnd sigstoreVerifyCode 0x2A82 svE2a = some 0x2A88 := by decide

set_option maxHeartbeats 4000000 in
/-- **The error exit at 0x2A82**: store `Err(0x1D)` at `out` as one
halfword, and return. -/
theorem sv_fail_2a82 {B out : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x3830) (E : SvCode n.mem)
    (s : St n.mem SV n 0x2A82 (reg n)) (t : Steps n0 n) (fR : ∀ x, SvR B x → n.mem x = n0.mem x)
    (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (hout : reg n (18 : Fin 32) = out) (hO : SvOut B out) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) : SvErrRet B out v n0 := by
  have hz := s.zero
  have sOC := hO.code
  have sOS := out_sep B out hO
  obtain ⟨n1, c1, u1⟩ := s.block svE2a E.self svE2a_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, svE2a]; simp +decide only [upd, ↓reduceIte, true_and, and_true])
  have a01 : reg n1 a0 = 0x1D01 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, svE2a, upd, ↓reduceIte, aluEval]
  have r1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs]; simp only [runBlock, BInstr.run, svE2a]; rw [updz (by rfl) hq, updz hz hq]
  have M1 : n1.mem = n.mem := u1.mem
  have s1 : St n.mem SV n1 0x2A88 (reg n1) := ⟨u1.pc, M1, fun _ => rfl⟩
  have e0 : reg n1 (18 : Fin 32) + 0 = out := by rw [r1 _ (by decide), hout]; exact BitVec.add_zero _
  obtain ⟨n2, d2, u2⟩ := s1.sh E.self sv_at_2a88 (off' := 0x2A8C) (by decide) (by rw [e0]; exact hO.al)
  rw [e0, a01] at u2
  have M2 : n2.mem = memStore8 (memStore8 n.mem out 1) (out + 1) 0x1D := by rw [u2.mem]; rfl
  have C2 : CodeIn n2.mem SV sigstoreVerifyCode := by
    rw [M2]; exact (E.self.store8 (by have := sOC.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this)).store8
      (sOC.sub (c := 1) (l := 1) (by decide))
  have s2 : St n2.mem SV n2 0x2A8C (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  obtain ⟨n3, d3, u3⟩ := s2.jump C2 sv_at_2a8c (off' := 0x970) (by decide) (by rw [s2.pc]; decide)
  have s3 : St n2.mem SV n3 0x970 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
  have hS : ∀ k, k < 13 → memLoad32 n2.mem (B + BitVec.ofNat 32 (0x382C - 4 * k)) = v k := fun k hk => by
    rw [← V k hk, M2]
    have hs : Sep out 2 (B + BitVec.ofNat 32 (0x382C - 4 * k)) 4 := by
      have := sOS.symm.sub (c := 0x30 - 4 * k) (l := 4) (by omega)
      rw [add_ofNat_assoc, show 0x37FC + (0x30 - 4 * k) = 0x382C - 4 * k by omega] at this
      exact this.symm
    exact memLoad32_congr fun j hj => by
      have h1 : B + BitVec.ofNat 32 (0x382C - 4 * k) + BitVec.ofNat 32 j ≠ out + 1 := fun e => hs 1 (by decide) j hj e.symm
      have h0 : B + BitVec.ofNat 32 (0x382C - 4 * k) + BitVec.ofNat 32 j ≠ out := fun e =>
        hs 0 (by decide) j hj (by rw [add_ofNat_zero]; exact e.symm)
      rw [memStore8_ne h1, memStore8_ne h0]
  refine sv_ret_err (n := n3) (M := n2.mem) F C2 s3 (t.trans (c1.trans ((Steps.single d2).trans (.single d3)))) hS hret
    (by rw [u3.regs, u2.regs, r1 sp (by decide), rsp]) (by rw [u3.regs, u2.regs, r1 3 (by decide), r3])
    (by rw [u3.regs, u2.regs, r1 4 (by decide), r4]) ?_ ?_
  · rw [M2, memStore8_ne (out_ne1 out), memStore8_same]
  · intro x hx h0 h1; rw [M2, memStore8_ne h1, memStore8_ne h0, fR x hx]

end C3.RV32.Sv
