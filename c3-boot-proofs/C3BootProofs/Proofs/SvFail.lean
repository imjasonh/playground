import C3BootProofs.Proofs.SvEcdsa

/-!
# `sigstore::verify`: its other error exits

Besides 0x7A4, four error exits store `Err` and the code themselves and
jump to the epilogue at 0x7AE: 0xE3A with the code in `a0`, 0x1882 with it
in `s9`, 0x1AB8 with it in `s4`, and 0x138E with `Err` and the code in the
low half of `a0`. 0x1388, 0xE46, and 0xE4E set `a0` and jump to 0x138E, and
0xE38 sets `a0` and falls through to 0xE3A.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

/-- The epilogue from 0x7AE after the error's bytes are stored at `out`:
`SvErrRet`, when `out` holds 1 and nothing else outside the stack changed. -/
theorem sv_ret_err {B out : Word} {v : Nat → Word} {n0 n : Machine} {M : Word → BitVec 8} (F : Fr B 0x2660)
    (C : CodeIn M SV sigstoreVerifyCode) (s : St M SV n 0x7AE (reg n)) (t : Steps n0 n)
    (hS : ∀ k, k < 13 → memLoad32 M (B + BitVec.ofNat 32 (0x265C - 4 * k)) = v k) (hret : v 0 &&& ~~~1 = v 0)
    (rsp : reg n sp = B + 0x21A0) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) (h1 : M out = 1) (hc : (M (out + 1)).toNat < 0x27)
    (fR : ∀ x, SvR B x → x ≠ out → x ≠ out + 1 → M x = n0.mem x) : SvErrRet B out v n0 := by
  obtain ⟨n', c', pc', mem', sp', sv', g', t'⟩ := sv_ret (v := v) C F s rsp hS hret
  exact ⟨n', t.trans c', pc', sp', sv', by rw [g', r3], by rw [t', r4], by rw [mem']; exact h1,
    by rw [mem']; exact hc, fun x hx h0 h1' => by rw [mem']; exact fR x hx h0 h1'⟩

theorem out_sep (B out : Word) (hO : SvOut B out) : Sep out 2 (B + BitVec.ofNat 32 0x262C) 0x34 := by
  have := hO.stk.symm.sub (c := 0x1590 + 0x262C) (l := 0x34) (by decide)
  rw [show B + 0xFFFFEA70 + BitVec.ofNat 32 (0x1590 + 0x262C) = B + BitVec.ofNat 32 0x262C by
    rw [BitVec.add_assoc]; rfl] at this
  exact this.symm

theorem out_ne1 (out : Word) : out ≠ out + 1 := by
  have := add_ofNat_ne out (c := 0) (d := 1) (by decide) (by decide) (by decide)
  rwa [add_ofNat_zero] at this

set_option maxHeartbeats 4000000 in
/-- **An error exit that stores `Err` itself**: `li a, 1`, `sb a, 0(s2)`,
`sb r, 1(s2)`, and a jump to the epilogue. -/
theorem sv_fail_sb {B out : Word} {v : Nat → Word} {n0 n : Machine} {off e : Nat} {a r : Fin 32} {o len : Word}
    (F : Fr B 0x2660) (E : SvCode n.mem) (ha : a = a0 ∨ a = a1) (hr : r = a0 ∨ r = s4 ∨ r = s9) (hra : r ≠ a)
    (hend : blockEnd sigstoreVerifyCode off
      [.aluImm .add a x0 0x1, .sb (18 : Fin 32) a 0x0, .sb (18 : Fin 32) r 0x1] = some e)
    (hj : fetchRel sigstoreVerifyCode e = some (.jal 0 o, len))
    (hn : BitVec.ofNat 32 e + o = BitVec.ofNat 32 0x7AE) (hev : (SV + BitVec.ofNat 32 e + o).getLsbD 0 = false)
    (s : St n.mem SV n off (reg n)) (t : Steps n0 n) (fR : ∀ x, SvR B x → n.mem x = n0.mem x)
    (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (hout : reg n (18 : Fin 32) = out) (hO : SvOut B out) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) (hc : ((reg n r).extractLsb' 0 8).toNat < 0x27) :
    SvErrRet B out v n0 := by
  have hz := s.zero
  have e0 : out + 0 = out := BitVec.add_zero _
  have sOC := hO.code
  have sOS := out_sep B out hO
  have sO0 : Sep (out + 0) 1 SV sigstoreVerifyCode.length := by
    rw [e0]; have := sOC.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
  have sO1 : Sep (out + 1) 1 SV sigstoreVerifyCode.length := sOC.sub (c := 1) (l := 1) (by decide)
  obtain ⟨n1, M1, r1, c1, s1⟩ : ∃ n1, n1.mem = memStore8 (memStore8 n.mem out 1) (out + 1) ((reg n r).extractLsb' 0 8) ∧
      (∀ q, q ≠ a → reg n1 q = reg n q) ∧ Steps n n1 ∧ St n1.mem SV n1 e (reg n1) := by
    rcases ha with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> (try exact absurd rfl hra) <;>
    · obtain ⟨n1, c1, u1⟩ := s.block _ E.self hend (by
        simp only [BlockOk, BInstr.ok, BInstr.run]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
        rw [hout]; exact ⟨sO0, sO1⟩)
      refine ⟨n1, ?_, fun q hq => ?_, c1, ⟨u1.pc, rfl, fun _ => rfl⟩⟩
      · rw [u1.mem]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [hout, e0]; rfl
      · rw [u1.regs]; simp only [runBlock, BInstr.run]; exact updz hz hq
  have C1 : CodeIn n1.mem SV sigstoreVerifyCode := by
    rw [M1]; rw [e0] at sO0; exact (E.self.store8 sO0).store8 sO1
  obtain ⟨n2, d2, u2⟩ := s1.jump C1 hj hn (by rw [s1.pc]; exact hev)
  have s2 : St n1.mem SV n2 0x7AE (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have ha4 : ∀ q : Fin 32, q.val ∈ [2, 3, 4] → q ≠ a := fun q hq h => by
    subst h; rcases ha with rfl | rfl <;> revert hq <;> decide
  have hS : ∀ k, k < 13 → memLoad32 n1.mem (B + BitVec.ofNat 32 (0x265C - 4 * k)) = v k := fun k hk => by
    rw [← V k hk, M1]
    have hs : Sep out 2 (B + BitVec.ofNat 32 (0x265C - 4 * k)) 4 := by
      have := sOS.symm.sub (c := 0x30 - 4 * k) (l := 4) (by omega)
      rw [add_ofNat_assoc, show 0x262C + (0x30 - 4 * k) = 0x265C - 4 * k by omega] at this
      exact this.symm
    exact memLoad32_congr fun j hj => by
      have h1 : B + BitVec.ofNat 32 (0x265C - 4 * k) + BitVec.ofNat 32 j ≠ out + 1 := fun e => hs 1 (by decide) j hj e.symm
      have h0 : B + BitVec.ofNat 32 (0x265C - 4 * k) + BitVec.ofNat 32 j ≠ out := fun e =>
        hs 0 (by decide) j hj (by rw [add_ofNat_zero]; exact e.symm)
      rw [memStore8_ne h1, memStore8_ne h0]
  refine sv_ret_err (n := n2) (M := n1.mem) F C1 s2 (t.trans (c1.trans (.single d2))) hS hret
    (by rw [u2.regs, r1 sp (ha4 sp (by decide)), rsp]) (by rw [u2.regs, r1 3 (ha4 3 (by decide)), r3])
    (by rw [u2.regs, r1 4 (ha4 4 (by decide)), r4]) ?_ ?_ ?_
  · rw [M1, memStore8_ne (out_ne1 out), memStore8_same]
  · rw [M1, memStore8_same]; exact hc
  · intro x hx h0 h1; rw [M1, memStore8_ne h1, memStore8_ne h0, fR x hx]

set_option maxRecDepth 100000 in
/-- **The error exit at 0xE3A**, with the code in `a0`. -/
theorem sv_fail_e3a {B out : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x2660) (E : SvCode n.mem)
    (s : St n.mem SV n 0xE3A (reg n)) (t : Steps n0 n) (fR : ∀ x, SvR B x → n.mem x = n0.mem x)
    (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (hout : reg n (18 : Fin 32) = out) (hO : SvOut B out) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) (hc : ((reg n a0).extractLsb' 0 8).toNat < 0x27) :
    SvErrRet B out v n0 :=
  sv_fail_sb (a := a1) (r := a0) F E (.inr rfl) (.inl rfl) (by decide) (by decide) sv_at_e44 (by decide)
    (by decide) s t fR V hret rsp hout hO r3 r4 hc

set_option maxRecDepth 100000 in
/-- **The error exit at 0x1882**, with the code in `s9`. -/
theorem sv_fail_1882 {B out : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x2660) (E : SvCode n.mem)
    (s : St n.mem SV n 0x1882 (reg n)) (t : Steps n0 n) (fR : ∀ x, SvR B x → n.mem x = n0.mem x)
    (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (hout : reg n (18 : Fin 32) = out) (hO : SvOut B out) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) (hc : ((reg n (25 : Fin 32)).extractLsb' 0 8).toNat < 0x27) :
    SvErrRet B out v n0 :=
  sv_fail_sb (a := a0) (r := s9) F E (.inl rfl) (.inr (.inr rfl)) (by decide) (by decide) sv_at_188c (by decide)
    (by decide) s t fR V hret rsp hout hO r3 r4 hc

set_option maxRecDepth 100000 in
/-- **The error exit at 0x1AB8**, with the code in `s4`. -/
theorem sv_fail_1ab8 {B out : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x2660) (E : SvCode n.mem)
    (s : St n.mem SV n 0x1AB8 (reg n)) (t : Steps n0 n) (fR : ∀ x, SvR B x → n.mem x = n0.mem x)
    (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (hout : reg n (18 : Fin 32) = out) (hO : SvOut B out) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) (hc : ((reg n (20 : Fin 32)).extractLsb' 0 8).toNat < 0x27) :
    SvErrRet B out v n0 :=
  sv_fail_sb (a := a0) (r := s4) F E (.inl rfl) (.inr (.inl rfl)) (by decide) (by decide) sv_at_1ac2 (by decide)
    (by decide) s t fR V hret rsp hout hO r3 r4 hc

theorem St.sh {M : Word → BitVec 8} {base : Word} {code : List Nat} {m : Machine} {off : Nat}
    {f : Fin 32 → Word} (s : St M base m off f)
    (hc : ∀ i, i < code.length → M (base + BitVec.ofNat 32 i) = byteAt code i)
    {rs1 rs2 : Fin 32} {o len : Word} {off' : Nat}
    (hf : fetchRel code off = some (.store .sh rs1 rs2 o, len))
    (hn : BitVec.ofNat 32 off + len = BitVec.ofNat 32 off') (hal : (f rs1 + o).toNat % 2 = 0) :
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

set_option maxRecDepth 100000 in
/-- **The store at 0x138E**: `sh` stores the low half of `a0`, `Err` and a
code, at `out` at once. -/
theorem sv_fail_138e {B out : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x2660) (E : SvCode n.mem)
    (s : St n.mem SV n 0x138E (reg n)) (t : Steps n0 n) (fR : ∀ x, SvR B x → n.mem x = n0.mem x)
    (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (hout : reg n (18 : Fin 32) = out) (hO : SvOut B out) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32))
    (hlo : (reg n a0).extractLsb' 0 8 = 1) (hhi : ((reg n a0).extractLsb' 8 8).toNat < 0x27) :
    SvErrRet B out v n0 := by
  have e0 : out + 0 = out := BitVec.add_zero _
  have sOC := hO.code
  have sOS := out_sep B out hO
  have sO0 : Sep out 1 SV sigstoreVerifyCode.length := by
    have := sOC.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this
  have sO1 : Sep (out + 1) 1 SV sigstoreVerifyCode.length := sOC.sub (c := 1) (l := 1) (by decide)
  have r18 : reg n (18 : Fin 32) + 0x0 = out := by rw [hout, e0]
  obtain ⟨n2, d2, s2⟩ := s.sh (off' := 0x1392) E.self sv_at_138e (by decide) (by rw [r18]; exact hO.al)
  rw [r18, hlo] at s2
  have C2 : CodeIn (memStore8 (memStore8 n.mem out 1) (out + 1) ((reg n a0).extractLsb' 8 8))
      SV sigstoreVerifyCode := (E.self.store8 sO0).store8 sO1
  obtain ⟨n3, d3, u3⟩ := s2.jump C2 sv_at_1392
    (show BitVec.ofNat 32 0x1392 + 0xFFFFF41C = BitVec.ofNat 32 0x7AE by decide) (by rw [s2.pc]; decide)
  have s3 : St (memStore8 (memStore8 n.mem out 1) (out + 1) ((reg n a0).extractLsb' 8 8))
      SV n3 0x7AE (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
  have hS : ∀ k, k < 13 → memLoad32 (memStore8 (memStore8 n.mem out 1) (out + 1)
      ((reg n a0).extractLsb' 8 8)) (B + BitVec.ofNat 32 (0x265C - 4 * k)) = v k := fun k hk => by
    rw [← V k hk]
    have hs : Sep out 2 (B + BitVec.ofNat 32 (0x265C - 4 * k)) 4 := by
      have := sOS.symm.sub (c := 0x30 - 4 * k) (l := 4) (by omega)
      rw [add_ofNat_assoc, show 0x262C + (0x30 - 4 * k) = 0x265C - 4 * k by omega] at this
      exact this.symm
    exact memLoad32_congr fun j hj => by
      have h1 : B + BitVec.ofNat 32 (0x265C - 4 * k) + BitVec.ofNat 32 j ≠ out + 1 := fun e => hs 1 (by decide) j hj e.symm
      have h0 : B + BitVec.ofNat 32 (0x265C - 4 * k) + BitVec.ofNat 32 j ≠ out := fun e =>
        hs 0 (by decide) j hj (by rw [add_ofNat_zero]; exact e.symm)
      rw [memStore8_ne h1, memStore8_ne h0]
  refine sv_ret_err (n := n3) F C2 s3 (t.trans ((Steps.single d2).trans (.single d3))) hS hret
    (by rw [u3.regs, rsp]) (by rw [u3.regs, r3]) (by rw [u3.regs, r4]) ?_ ?_ ?_
  · rw [memStore8_ne (out_ne1 out), memStore8_same]
  · rw [memStore8_same]; exact hhi
  · intro x hx h0 h1; rw [memStore8_ne h1, memStore8_ne h0, fR x hx]

set_option maxRecDepth 100000 in
/-- An error exit that sets `a0` with `is` and jumps to 0x138E. -/
theorem sv_fail_to138e {B out : Word} {v : Nat → Word} {n0 n : Machine} {off off' : Nat} {is : List BInstr}
    {o : Word} (F : Fr B 0x2660) (E : SvCode n.mem)
    (s : St n.mem SV n off (reg n)) (t : Steps n0 n) (fR : ∀ x, SvR B x → n.mem x = n0.mem x)
    (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (hout : reg n (18 : Fin 32) = out) (hO : SvOut B out) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32))
    (he : blockEnd sigstoreVerifyCode off is = some off') (hok : BlockOk SV sigstoreVerifyCode.length is (n.mem, reg n))
    (hm : (runBlock is (n.mem, reg n)).1 = n.mem)
    (hr : ∀ q : Fin 32, q ≠ a0 → (runBlock is (n.mem, reg n)).2 q = reg n q)
    (hj : fetchRel sigstoreVerifyCode off' = some (.jal x0 o, 2))
    (ht : BitVec.ofNat 32 off' + o = BitVec.ofNat 32 0x138E)
    (hlo : ((runBlock is (n.mem, reg n)).2 a0).extractLsb' 0 8 = 1)
    (hhi : (((runBlock is (n.mem, reg n)).2 a0).extractLsb' 8 8).toNat < 0x27) : SvErrRet B out v n0 := by
  obtain ⟨n1, c1, u1⟩ := s.block is E.self he hok
  rw [hm] at u1
  have s1 : St n.mem SV n1 off' (reg n1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have rr : ∀ q : Fin 32, q ≠ a0 → reg n1 q = reg n q := fun q hq => by rw [u1.regs, hr q hq]
  obtain ⟨n2, d2, u2⟩ := s1.jump E.self hj ht (by rw [s1.pc, BitVec.add_assoc, ht]; decide)
  have s2 : St n.mem SV n2 0x138E (reg n2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have m2 : n2.mem = n.mem := u2.mem
  have E2 : SvCode n2.mem := by rw [m2]; exact E
  rw [← m2] at s2
  exact sv_fail_138e F E2 s2 (t.trans (c1.trans (.single d2))) (by rw [m2]; exact fR) (by rw [m2]; exact V) hret
    (by rw [u2.regs, rr sp (by decide), rsp]) (by rw [u2.regs, rr 18 (by decide), hout])
    hO (by rw [u2.regs, rr 3 (by decide), r3]) (by rw [u2.regs, rr 4 (by decide), r4])
    (by rw [u2.regs, u1.regs]; exact hlo) (by rw [u2.regs, u1.regs]; exact hhi)

set_option maxRecDepth 100000 in
/-- **The error exit at 0x1388**: no listed intermediate issued the leaf,
code 0x1D. -/
theorem sv_fail_1388 {B out : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x2660) (E : SvCode n.mem)
    (s : St n.mem SV n 0x1388 (reg n)) (t : Steps n0 n) (fR : ∀ x, SvR B x → n.mem x = n0.mem x)
    (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (hout : reg n (18 : Fin 32) = out) (hO : SvOut B out) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) : SvErrRet B out v n0 := by
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0x138E) [.lui a0 0x2000, .aluImm .add a0 a0 0xFFFFFD01] E.self (by decide)
    (by simp only [BlockOk, BInstr.ok]; exact ⟨trivial, trivial, trivial⟩)
  have s1 : St n1.mem SV n1 0x138E (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n.mem := u1.mem
  have r1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs]; simp only [runBlock, BInstr.run]; exact (updz (upd_zero _ _ _) hq).trans (updz s.zero hq)
  have ra0 : reg n1 a0 = 0x1D01 := by
    rw [u1.regs]; simp only [runBlock, BInstr.run, aluEval, upd, ↓reduceIte]; rfl
  exact sv_fail_138e F (by rw [m1]; exact E) s1 (t.trans c1) (by rw [m1]; exact fR) (by rw [m1]; exact V) hret
    (by rw [r1 sp (by decide), rsp]) (by rw [r1 18 (by decide), hout]) hO (by rw [r1 3 (by decide), r3])
    (by rw [r1 4 (by decide), r4]) (by rw [ra0]; rfl) (by rw [ra0]; decide)

set_option maxRecDepth 100000 in
/-- **The error exit at 0xE46**: a policy value differs from the trust
root's, code 0x17. -/
theorem sv_fail_e46 {B out : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x2660) (E : SvCode n.mem)
    (s : St n.mem SV n 0xE46 (reg n)) (t : Steps n0 n) (fR : ∀ x, SvR B x → n.mem x = n0.mem x)
    (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (hout : reg n (18 : Fin 32) = out) (hO : SvOut B out) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) : SvErrRet B out v n0 :=
  sv_fail_to138e (is := [.lui a0 0x1000, .aluImm .add a0 a0 0x701]) F E s t fR V hret rsp hout hO r3 r4
    (by decide) (by simp only [BlockOk, BInstr.ok]; exact ⟨trivial, trivial, trivial⟩) rfl
    (fun q hq => by simp only [runBlock, BInstr.run]; exact (updz (upd_zero _ _ _) hq).trans (updz s.zero hq))
    sv_at_e4c (by decide) (by simp only [runBlock, BInstr.run, aluEval, upd, ↓reduceIte]; rfl)
    (by simp only [runBlock, BInstr.run, aluEval, upd, ↓reduceIte]; decide)

set_option maxRecDepth 100000 in
/-- **The error exit at 0xE4E**: the image's signature doesn't verify,
code 0x10. -/
theorem sv_fail_e4e {B out : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x2660) (E : SvCode n.mem)
    (s : St n.mem SV n 0xE4E (reg n)) (t : Steps n0 n) (fR : ∀ x, SvR B x → n.mem x = n0.mem x)
    (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (hout : reg n (18 : Fin 32) = out) (hO : SvOut B out) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) : SvErrRet B out v n0 :=
  sv_fail_to138e (is := [.lui a0 0x1000, .aluImm .add a0 a0 0x1]) F E s t fR V hret rsp hout hO r3 r4
    (by decide) (by simp only [BlockOk, BInstr.ok]; exact ⟨trivial, trivial, trivial⟩) rfl
    (fun q hq => by simp only [runBlock, BInstr.run]; exact (updz (upd_zero _ _ _) hq).trans (updz s.zero hq))
    sv_at_e52 (by decide) (by simp only [runBlock, BInstr.run, aluEval, upd, ↓reduceIte]; rfl)
    (by simp only [runBlock, BInstr.run, aluEval, upd, ↓reduceIte]; decide)

set_option maxRecDepth 100000 in
/-- **The error exit at 0xE38**: the leaf's signature doesn't verify, code
0x10. -/
theorem sv_fail_e38 {B out : Word} {v : Nat → Word} {n0 n : Machine} (F : Fr B 0x2660) (E : SvCode n.mem)
    (s : St n.mem SV n 0xE38 (reg n)) (t : Steps n0 n) (fR : ∀ x, SvR B x → n.mem x = n0.mem x)
    (V : SvSaves B n.mem v) (hret : v 0 &&& ~~~1 = v 0) (rsp : reg n sp = B + 0x21A0)
    (hout : reg n (18 : Fin 32) = out) (hO : SvOut B out) (r3 : reg n (3 : Fin 32) = reg n0 (3 : Fin 32))
    (r4 : reg n (4 : Fin 32) = reg n0 (4 : Fin 32)) : SvErrRet B out v n0 := by
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0xE3A) [.aluImm .add a0 x0 0x10] E.self (by decide)
    (by simp only [BlockOk, BInstr.ok]; exact ⟨trivial, trivial⟩)
  have s1 : St n1.mem SV n1 0xE3A (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = n.mem := u1.mem
  have r1 : ∀ q, q ≠ a0 → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs]; simp only [runBlock, BInstr.run]; exact updz s.zero hq
  have ra0 : reg n1 a0 = 0x10 := by
    rw [u1.regs]; simp only [runBlock, BInstr.run, aluEval, upd, ↓reduceIte]; rfl
  exact sv_fail_e3a F (by rw [m1]; exact E) s1 (t.trans c1) (by rw [m1]; exact fR) (by rw [m1]; exact V) hret
    (by rw [r1 sp (by decide), rsp]) (by rw [r1 18 (by decide), hout]) hO (by rw [r1 3 (by decide), r3])
    (by rw [r1 4 (by decide), r4]) (by rw [ra0]; decide)

theorem shr_byte (x : Word) (k : Nat) (hk : k + 8 ≤ 32) : (x >>> k).extractLsb' 0 8 = x.extractLsb' k 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-- A word from the bytes `sb` stores of it and of it shifted right. -/
theorem ld_of_shr_bytes {M : Word → BitVec 8} {a x : Word} (h0 : M a = x.extractLsb' 0 8)
    (h1 : M (a + 1) = (x >>> 8).extractLsb' 0 8) (h2 : M (a + 2) = (x >>> 16).extractLsb' 0 8)
    (h3 : M (a + 3) = (x >>> 24).extractLsb' 0 8) : memLoad32 M a = x := by
  rw [shr_byte x 8 (by decide)] at h1; rw [shr_byte x 16 (by decide)] at h2; rw [shr_byte x 24 (by decide)] at h3
  exact ld_of_bytes h0 h1 h2 h3

end C3.RV32.Sv
