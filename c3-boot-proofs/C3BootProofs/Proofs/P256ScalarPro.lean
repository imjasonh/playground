import C3BootProofs.Proofs.P256ScalarDecode
import C3BootProofs.Proofs.FieldWideMulMain

/-!
# P-256's `Scalar::mul`: environment, prologue, and epilogue

`Scalar::mul` saves 13 registers at the top of its 0xA0-byte frame, keeps
the result pointer at `F + 0x28`, and calls `widening_mul_fixed::<8, 8>`
with the product's 16 limbs at `F + 0x2C`. The epilogue restores the
registers. `P256Scalar.lean` puts these around the body that
`P256ScalarBody.lean` proves.
-/

namespace C3.RV32

open C3.Image

/-- Where P-256's `Scalar::mul` runs: its code, `widening_mul_fixed::<8, 8>`'s
code and its callees' and `borrowing_sub`'s at their offsets, the 0x100 bytes
of stack at `G` that it and `widening_mul_fixed` use (its frame is the top
0xA0), the result `out`, and the operands at `ap` and `bp`, each apart from
what it must not touch. -/
structure PSMEnv (M : Word → BitVec 8) (P G out ap bp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P p256ScalarMulCode
  wm : CodeIn M (P + 0xFFFFB24E) wideMulCode
  mset : CodeIn M (P + 0xFFFFB24E + 0x7446) memsetCode
  stub : CodeIn M (P + 0xFFFFB24E + 0x74AE) memcpyStubCode
  body : CodeIn M (P + 0xFFFFB24E + 0x74B6) memcpyBodyCode
  bs : CodeIn M (psmBsub P) borrowingSubCode
  hG : G.toNat % 4 = 0
  hGt : G.toNat + 0x100 ≤ 2 ^ 32
  hout : out.toNat % 4 = 0
  hap : ap.toNat % 4 = 0
  hbp : bp.toNat % 4 = 0
  sGC : Sep G 0x100 P p256ScalarMulCode.length
  sGW : Sep G 0x100 (P + 0xFFFFB24E) wideMulCode.length
  sGM : Sep G 0x100 (P + 0xFFFFB24E + 0x7446) memsetCode.length
  sGU : Sep G 0x100 (P + 0xFFFFB24E + 0x74AE) memcpyStubCode.length
  sGB : Sep G 0x100 (P + 0xFFFFB24E + 0x74B6) memcpyBodyCode.length
  sGBs : Sep G 0x100 (psmBsub P) borrowingSubCode.length
  sAG : Sep ap 32 G 0x100
  sBG : Sep bp 32 G 0x100
  sOG : Sep out 32 G 0x100
  sOC : Sep out 32 P p256ScalarMulCode.length
  sOBs : Sep out 32 (psmBsub P) borrowingSubCode.length

/-- The registers the function saves, at offsets from its `sp`. -/
abbrev psmPs : List (Fin 32 × Word) :=
  [(ra, 0x9C), ((8 : Fin 32), 0x98), ((9 : Fin 32), 0x94), ((18 : Fin 32), 0x90), ((19 : Fin 32), 0x8C),
   ((20 : Fin 32), 0x88), ((21 : Fin 32), 0x84), ((22 : Fin 32), 0x80), ((23 : Fin 32), 0x7C),
   ((24 : Fin 32), 0x78), ((25 : Fin 32), 0x74), ((26 : Fin 32), 0x70), ((27 : Fin 32), 0x6C)]

set_option maxRecDepth 20000 in
theorem psmPs_range : ∀ p ∈ psmPs, p.2.toNat % 4 = 0 ∧ 0x6C ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0xA0 := by decide

theorem psmPs_sp : ∀ p ∈ psmPs, p.1 ≠ sp := by decide

section
set_option maxRecDepth 20000
theorem psmSave_end : blockEnd p256ScalarMulCode 2 (saveBlock psmPs) = some 0x1C := by decide
theorem psmRestore_end : blockEnd p256ScalarMulCode 0xB6A (restoreBlock psmPs) = some 0xB84 := by decide
end

theorem psmF_ofs (G : Word) (c : Nat) : G + 0x60 + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x60 + c) := by
  rw [show (0x60 : Word) = BitVec.ofNat 32 0x60 from rfl, add_ofNat_assoc]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The prologue, from entry to the call of `widening_mul_fixed` at 0x20:
save the registers, keep the result pointer, and point `a0` at the
product's limbs. -/
theorem psm_pro (m : Machine) {P G out ap bp F : Word} (env : PSMEnv m.mem P G out ap bp) (hF : G + 0x60 = F)
    (hpc : m.pc = P) (hsp : reg m sp = G + 0x100) (ha0 : reg m a0 = out) (ha1 : reg m a1 = ap)
    (ha2 : reg m a2 = bp) :
    ∃ n M, Steps m n ∧ St M P n 0x20 (reg n) ∧
      (∀ x, Sep F 0xA0 x 1 → M x = m.mem x) ∧
      (∀ r o, (r, o) ∈ psmPs → memLoad32 M (F + o) = reg m r) ∧
      memLoad32 M (F + 0x28) = out ∧
      reg n sp = F ∧ reg n a0 = F + 0x2C ∧ reg n a1 = ap ∧ reg n a2 = bp ∧
      ∀ q, q.val ∉ [2, 10] → reg n q = reg m q := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hGt := env.hGt
  have hFn : F.toNat = G.toNat + 0x60 := by
    rw [← hF, BitVec.toNat_add, show (0x60 : Word).toNat = 0x60 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hFa : F.toNat % 4 = 0 := by rw [hFn]; have := env.hG; omega
  have sFC : Sep F 0xA0 P p256ScalarMulCode.length := by rw [← hF]; exact env.sGC.sub (c := 0x60) (l := 0xA0) (by decide)
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code psm_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF60) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [hsp, ← hF]
    show G + 0x100 + 0xFFFFFF60 = G + 0x60
    rw [BitVec.add_assoc]; rfl
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock psmPs) u1 env.code psmSave_end (saveBlock_ok _ psmPs _ fun p hp => by
    rw [sp1]
    exact ⟨fr_al' hFa (psmPs_range p hp).1, frm_sep' sFC (by have := psmPs_range p hp; omega)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF60)) psmPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep F 0xA0 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]; exact saveMem_outside psmPs fun p hp => frm_sep' hx (by have := psmPs_range p hp; omega)
  have hcv : CodeIn Msv P p256ScalarMulCode := fun i hi => by
    rw [frSv _ (sFC.subR (c := i) (l := 1) (by omega))]; exact env.code i hi
  have r2 : ∀ q, reg m2 q = upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF60) q := u2.regs
  have sp2 : reg m2 sp = F := by rw [r2]; exact sp1
  obtain ⟨m3, d3, u3⟩ := u2.self.swG hcv psm_at_1c (off' := 0x1E) (by decide)
    (by rw [sp2]; exact fr_al' hFa (by decide)) (a := F + 0x28) (v := out) (by rw [sp2])
    (by rw [r2]; simp +decide only [upd_app, ↓reduceIte]; exact ha0)
  obtain ⟨M3, hM3⟩ : ∃ M', memStore32 Msv (F + 0x28) out = M' := ⟨_, rfl⟩
  rw [hM3] at u3
  have hc3 : CodeIn M3 P p256ScalarMulCode := by rw [← hM3]; exact hcv.store32 (frm_sep' sFC (by decide))
  obtain ⟨m4, d4, u4⟩ := u3.self.aluImm hc3 psm_at_1e (off' := 0x20) (by decide)
  have r3 : ∀ q, reg m3 q = reg m2 q := u3.regs
  have g4 : ∀ q, reg m4 q = upd (reg m3) a0 (aluEval .add (reg m3 sp) 0x2C) q := u4.regs
  refine ⟨m4, M3, .cons d1 (c2.trans (.cons d3 (.single d4))), u4.self, fun x hx => ?_, fun r o h => ?_, ?_, ?_, ?_,
    ?_, ?_, fun q hq => ?_⟩
  · rw [← hM3, memStore32_get_sep (frm_sep' hx (by decide)), frSv x hx]
  · have hrange : o.toNat % 4 = 0 ∧ 0x6C ≤ o.toNat ∧ o.toNat + 4 ≤ 0xA0 := psmPs_range (r, o) h
    rw [← hM3, memLoad32_store32_sep (show Sep (F + 0x28) 4 (F + o) 4 from by
      have := sep_offsets F (c := 0x28) (n := 4) (d := o.toNat) (k := 4) (.inl (by omega)) (by decide) (by omega)
      rwa [ofNat_toNat_self] at this), ← hMsv]
    simp only [psmPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  · rw [← hM3, memLoad32_store32_same]
  · rw [g4]; simp +decide only [upd_app, ↓reduceIte]; rw [r3, sp2]
  · rw [g4]; simp +decide only [upd_app, ↓reduceIte]; rw [r3, sp2]; rfl
  · rw [g4]; simp +decide only [upd_app, ↓reduceIte]; rw [r3, r2]; simp +decide only [upd_app, ↓reduceIte]; exact ha1
  · rw [g4]; simp +decide only [upd_app, ↓reduceIte]; rw [r3, r2]; simp +decide only [upd_app, ↓reduceIte]; exact ha2
  · have n10 : q ≠ a0 := fun e => hq (by rw [e]; decide)
    have n2 : q ≠ sp := fun e => hq (by rw [e]; decide)
    rw [g4, upd_app, if_neg n10, r3, r2, upd_app, if_neg n2]
    by_cases h0 : (q : Nat) = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [hz]
    · simp [h0]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The epilogue, from 0xB6A: restore the saved registers and `sp`, and
return. -/
theorem psm_epi {M : Word → BitVec 8} {P F : Word} {v : Fin 32 → Word} {n : Machine}
    (st : St M P n 0xB6A (reg n)) (hc : CodeIn M P p256ScalarMulCode) (hFa : F.toNat % 4 = 0) (rsp : reg n sp = F)
    (hsl : ∀ r o, (r, o) ∈ psmPs → memLoad32 M (F + o) = v r) :
    ∃ n', Steps n n' ∧ n'.pc = v ra &&& ~~~1 ∧ reg n' sp = F + 0xA0 ∧ n'.mem = M ∧
      (∀ r o, (r, o) ∈ psmPs → reg n' r = v r) ∧
      ∀ q, q.val ∉ [1, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ sp → reg n' q = reg n q := by
  obtain ⟨n4, c4, u4⟩ := St.block (restoreBlock psmPs) st hc psmRestore_end
    (restoreBlock_ok M _ psmPs (reg n) rsp psmPs_sp fun p hp => fr_al' hFa (psmPs_range p hp).1)
  simp only [restoreBlock_run M _ psmPs (reg n) rsp psmPs_sp] at u4
  have rsp4 : restoreRegs M F (reg n) psmPs sp = F := by rw [restoreRegs_sp _ _ _ _ psmPs_sp]; exact rsp
  obtain ⟨n5, d5, u5⟩ := u4.aluImm hc psm_at_b84 (off' := 0xB86) (by decide)
  obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.jalr hc psm_at_b86
  refine ⟨n6, c4.trans (.cons d5 (.single d6)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc6]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
    rw [add_lit_zero, hsl ra 0x9C (by decide)]
  · rw [regs6]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [rsp4]; try rfl
  · exact mem6
  · intro r o h
    rw [regs6]
    simp only [psmPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp +decide only [upd_app, ↓reduceIte]
      simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact hsl _ _ (by decide)
  · intro q hq hs
    have ne : ∀ w : Fin 32, w.val ∈ [1, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ w :=
      fun w hw e => hq (e ▸ hw)
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; exact (show reg n6 0 = 0 from rfl).trans (show reg n 0 = 0 from rfl).symm
    rw [regs6]
    simp only [upd_app, h0, hs, ite_false]
    simp only [restoreRegs]
    simp only [upd_app, h0, ne ra (by decide), ne 8 (by decide), ne 9 (by decide), ne 18 (by decide),
      ne 19 (by decide), ne 20 (by decide), ne 21 (by decide), ne 22 (by decide), ne 23 (by decide),
      ne 24 (by decide), ne 25 (by decide), ne 26 (by decide), ne 27 (by decide), ite_false]

end C3.RV32
