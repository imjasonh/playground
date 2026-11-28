import C3BootProofs.Proofs.LincombShift12
import C3BootProofs.Proofs.LincombInt8
import C3BootProofs.Proofs.ShrWide8Main

/-!
# `SignedInt<8>::lincomb_int_reduce_shift::<2>`

The 8-limb instance of `lincombShift8_correct`: the same code, instruction
for instruction, with a smaller frame and 32-byte copies, calling the proved
8-limb `lincomb_int` and `shr_in_place_wide`.
-/

namespace C3.RV32

open C3.Image

theorem ls8_at_0 : fetchRel lincombShift8Code 0x0 = some (.aluImm .add sp sp 0xFFFFFF90, 2) := by decide
theorem ls8_at_2 : fetchRel lincombShift8Code 0x2 = some (.store .sw sp ra 0x6C, 2) := by decide
theorem ls8_at_4 : fetchRel lincombShift8Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x68, 2) := by decide
theorem ls8_at_6 : fetchRel lincombShift8Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x64, 2) := by decide
theorem ls8_at_8 : fetchRel lincombShift8Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x60, 2) := by decide
theorem ls8_at_a : fetchRel lincombShift8Code 0xA = some (.alu .add (18 : Fin 32) x0 a5, 2) := by decide
theorem ls8_at_c : fetchRel lincombShift8Code 0xC = some (.alu .add (9 : Fin 32) x0 a0, 2) := by decide
theorem ls8_at_e : fetchRel lincombShift8Code 0xE = some (.aluImm .add a0 sp 0x34, 2) := by decide
theorem ls8_at_10 : fetchRel lincombShift8Code 0x10 = some (.auipc ra 0x0, 4) := by decide
theorem ls8_at_14 : fetchRel lincombShift8Code 0x14 = some (.jalr ra ra 0x52, 4) := by decide
theorem ls8_at_18 : fetchRel lincombShift8Code 0x18 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem ls8_at_1a : fetchRel lincombShift8Code 0x1A = some (.aluImm .add a1 sp 0x34, 2) := by decide
theorem ls8_at_1c : fetchRel lincombShift8Code 0x1C = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem ls8_at_20 : fetchRel lincombShift8Code 0x20 = some (.auipc ra 0x4000, 4) := by decide
theorem ls8_at_24 : fetchRel lincombShift8Code 0x24 = some (.jalr ra ra 0xFFFFFAEE, 4) := by decide
theorem ls8_at_28 : fetchRel lincombShift8Code 0x28 = some (.load .lw a0 sp 0x54, 2) := by decide
theorem ls8_at_2a : fetchRel lincombShift8Code 0x2A = some (.load .lw a1 sp 0x58, 2) := by decide
theorem ls8_at_2c : fetchRel lincombShift8Code 0x2C = some (.load .lbu (8 : Fin 32) sp 0x5C, 4) := by decide
theorem ls8_at_30 : fetchRel lincombShift8Code 0x30 = some (.store .sw sp a0 0x28, 2) := by decide
theorem ls8_at_32 : fetchRel lincombShift8Code 0x32 = some (.store .sw sp a1 0x2C, 2) := by decide
theorem ls8_at_34 : fetchRel lincombShift8Code 0x34 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem ls8_at_36 : fetchRel lincombShift8Code 0x36 = some (.aluImm .add a1 sp 0x28, 2) := by decide
theorem ls8_at_38 : fetchRel lincombShift8Code 0x38 = some (.alu .add a2 x0 (18 : Fin 32), 2) := by decide
theorem ls8_at_3a : fetchRel lincombShift8Code 0x3A = some (.auipc ra 0x0, 4) := by decide
theorem ls8_at_3e : fetchRel lincombShift8Code 0x3E = some (.jalr ra ra 0x1AC, 4) := by decide
theorem ls8_at_42 : fetchRel lincombShift8Code 0x42 = some (.aluImm .add a1 sp 0x8, 2) := by decide
theorem ls8_at_44 : fetchRel lincombShift8Code 0x44 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem ls8_at_48 : fetchRel lincombShift8Code 0x48 = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem ls8_at_4a : fetchRel lincombShift8Code 0x4A = some (.auipc ra 0x4000, 4) := by decide
theorem ls8_at_4e : fetchRel lincombShift8Code 0x4E = some (.jalr ra ra 0xFFFFFAC4, 4) := by decide
theorem ls8_at_52 : fetchRel lincombShift8Code 0x52 = some (.store .sb (9 : Fin 32) (8 : Fin 32) 0x20, 4) := by decide
theorem ls8_at_56 : fetchRel lincombShift8Code 0x56 = some (.load .lw ra sp 0x6C, 2) := by decide
theorem ls8_at_58 : fetchRel lincombShift8Code 0x58 = some (.load .lw (8 : Fin 32) sp 0x68, 2) := by decide
theorem ls8_at_5a : fetchRel lincombShift8Code 0x5A = some (.load .lw (9 : Fin 32) sp 0x64, 2) := by decide
theorem ls8_at_5c : fetchRel lincombShift8Code 0x5C = some (.load .lw (18 : Fin 32) sp 0x60, 2) := by decide
theorem ls8_at_5e : fetchRel lincombShift8Code 0x5E = some (.aluImm .add sp sp 0x70, 2) := by decide
theorem ls8_at_60 : fetchRel lincombShift8Code 0x60 = some (.jalr x0 ra 0x0, 2) := by decide

/-- Where `lincomb_int_reduce_shift::<2>` runs: its code, its callees' code
at their offsets, the 0x1F0 bytes of stack at `G` that it and its callees use
(its frame is the top 0x70), the result `res`, and the operands, each apart
from what it must not touch. -/
structure LSEnv8 (M : Word → BitVec 8) (P G res ap bp cp dp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P lincombShift8Code
  lc : CodeIn M (P + 0x62) lincomb8Code
  abs : CodeIn M (P + 0x62 + 0xFFFFC6EA) absSign2Code
  wide : CodeIn M (P + 0x62 + 0x398) wideMul8x2Code
  neg : CodeIn M (P + 0x62 + 0x480) condNeg8Code
  mset : CodeIn M (P + 0x62 + 0x3A44) memsetCode
  stub : CodeIn M (P + 0x62 + 0x3AAC) memcpyStubCode
  body : CodeIn M (P + 0x62 + 0x3AB4) memcpyBodyCode
  bsub : CodeIn M (lcBsub8 (P + 0x62)) borrowingSubCode
  sel2 : CodeIn M (P + 0x62 + 0x272E) uintSelect2Code
  sel12 : CodeIn M (P + 0x62 + 0xFFFFFF2A) uintSelect8Code
  zero : CodeIn M (BitVec.ofNat 32 u2ZeroAddress) u2ZeroData
  one : CodeIn M (BitVec.ofNat 32 u2OneAddress) u2OneData
  shr : CodeIn M (P + 0x1E6) shr8Code
  lm : CodeIn M (P + 0x1E6 + 0x1EE) leadMut8Code
  tr : CodeIn M (P + 0x1E6 + 0x1FE) trailing8Code
  hG : G.toNat % 4 = 0
  hGt : G.toNat + 0x1F0 ≤ 2 ^ 32
  hres : res.toNat % 4 = 0
  hap : ap.toNat % 4 = 0
  hbp : bp.toNat % 4 = 0
  hcp : cp.toNat % 4 = 0
  hdp : dp.toNat % 4 = 0
  hwr : res.toNat + 33 < 2 ^ 32
  hwa : ap.toNat + 33 < 2 ^ 32
  hwb : bp.toNat + 33 < 2 ^ 32
  sC : Sep G 0x1F0 P lincombShift8Code.length
  sL : Sep G 0x1F0 (P + 0x62) lincomb8Code.length
  sA : Sep G 0x1F0 (P + 0x62 + 0xFFFFC6EA) absSign2Code.length
  sW : Sep G 0x1F0 (P + 0x62 + 0x398) wideMul8x2Code.length
  sN : Sep G 0x1F0 (P + 0x62 + 0x480) condNeg8Code.length
  sM : Sep G 0x1F0 (P + 0x62 + 0x3A44) memsetCode.length
  sU : Sep G 0x1F0 (P + 0x62 + 0x3AAC) memcpyStubCode.length
  sB : Sep G 0x1F0 (P + 0x62 + 0x3AB4) memcpyBodyCode.length
  sBs : Sep G 0x1F0 (lcBsub8 (P + 0x62)) borrowingSubCode.length
  s2 : Sep G 0x1F0 (P + 0x62 + 0x272E) uintSelect2Code.length
  s12 : Sep G 0x1F0 (P + 0x62 + 0xFFFFFF2A) uintSelect8Code.length
  sZ : Sep G 0x1F0 (BitVec.ofNat 32 u2ZeroAddress) 8
  sO : Sep G 0x1F0 (BitVec.ofNat 32 u2OneAddress) 8
  sS : Sep G 0x1F0 (P + 0x1E6) shr8Code.length
  sLm : Sep G 0x1F0 (P + 0x1E6 + 0x1EE) leadMut8Code.length
  sTr : Sep G 0x1F0 (P + 0x1E6 + 0x1FE) trailing8Code.length
  rG : Sep res 33 G 0x1F0
  aG : Sep ap 33 G 0x1F0
  bG : Sep bp 33 G 0x1F0
  cG : Sep cp 8 G 0x1F0
  dG : Sep dp 8 G 0x1F0
  rC : Sep res 33 P lincombShift8Code.length
  rB : Sep res 33 (P + 0x62 + 0x3AB4) memcpyBodyCode.length

/-- The registers the function saves, at offsets from its `sp`. -/
abbrev lsPs8 : List (Fin 32 × Word) :=
  [(ra, 0x6C), ((8 : Fin 32), 0x68), ((9 : Fin 32), 0x64), ((18 : Fin 32), 0x60)]

theorem lsPs8_range : ∀ p ∈ lsPs8, p.2.toNat % 4 = 0 ∧ 0x60 ≤ p.2.toNat ∧ p.2.toNat + 4 ≤ 0x70 := by decide

theorem lsPs8_sp : ∀ p ∈ lsPs8, p.1 ≠ sp := by decide

section
set_option maxRecDepth 20000
theorem lsSave_end8 : blockEnd lincombShift8Code 2 (saveBlock lsPs8) = some 0xA := by decide
theorem lsRestore_end8 : blockEnd lincombShift8Code 0x56 (restoreBlock lsPs8) = some 0x5E := by decide
end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The prologue, from entry to the call of `lincomb_int` at 0x10: save the
registers, keep the result pointer in `s1` and the shift in `s2`, and point
`a0` at the frame's buffer at `F + 0x34`. -/
theorem ls8_pro (m : Machine) {P F : Word} (hc : CodeIn m.mem P lincombShift8Code) (hFa : F.toNat % 4 = 0)
    (sFC : Sep F 0x70 P lincombShift8Code.length) (hpc : m.pc = P) (hsp : reg m sp + 0xFFFFFF90 = F) :
    ∃ n M, Steps m n ∧ St M P n 0x10 (reg n) ∧
      (∀ x, Sep F 0x70 x 1 → M x = m.mem x) ∧
      (∀ r o, (r, o) ∈ lsPs8 → memLoad32 M (F + o) = reg m r) ∧
      reg n sp = F ∧ reg n a0 = F + 0x34 ∧ reg n (9 : Fin 32) = reg m a0 ∧ reg n (18 : Fin 32) = reg m a5 ∧
      ∀ q, q.val ∉ [2, 9, 10, 18] → reg n q = reg m q := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm hc ls8_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF90) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; exact hsp
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock lsPs8) u1 hc lsSave_end8 (saveBlock_ok _ lsPs8 _ fun p hp => by
    rw [sp1]
    exact ⟨fr_al' hFa (lsPs8_range p hp).1, frm_sep' sFC (by have := lsPs8_range p hp; omega)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF90)) lsPs8 = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep F 0x70 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]; exact saveMem_outside lsPs8 fun p hp => frm_sep' hx (by have := lsPs8_range p hp; omega)
  have hcv : CodeIn Msv P lincombShift8Code := fun i hi => by
    rw [frSv _ (sFC.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have r2 : ∀ q, reg m2 q = upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF90) q := u2.regs
  have sp2 : reg m2 sp = F := by rw [r2]; exact sp1
  obtain ⟨m3, d3, u3⟩ := u2.self.alu hcv ls8_at_a (off' := 0xC) (by decide)
  obtain ⟨m4, d4, u4⟩ := u3.self.alu hcv ls8_at_c (off' := 0xE) (by decide)
  obtain ⟨m5, d5, u5⟩ := u4.self.aluImm hcv ls8_at_e (off' := 0x10) (by decide)
  have r3 : ∀ q, reg m3 q = upd (reg m2) (18 : Fin 32) (aluEval .add (reg m2 x0) (reg m2 a5)) q := u3.regs
  have r4 : ∀ q, reg m4 q = upd (reg m3) (9 : Fin 32) (aluEval .add (reg m3 x0) (reg m3 a0)) q := u4.regs
  have r5 : ∀ q, reg m5 q = upd (reg m4) a0 (aluEval .add (reg m4 sp) 0x34) q := u5.regs
  have z2 : reg m2 x0 = 0 := u2.self.zero
  have z3 : reg m3 x0 = 0 := u3.self.zero
  refine ⟨m5, Msv, .cons d1 (c2.trans (.cons d3 (.cons d4 (.single d5)))), u5.self, frSv, fun r o h => ?_, ?_, ?_,
    ?_, ?_, fun q hq => ?_⟩
  · rw [← hMsv]
    simp only [lsPs8, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  · rw [r5, updz u4.self.zero (by decide), r4, updz u3.self.zero (by decide), r3, updz z2 (by decide)]; exact sp2
  · rw [r5]; simp +decide only [upd_app, ↓reduceIte]
    rw [r4, updz u3.self.zero (by decide), r3, updz z2 (by decide), sp2]; rfl
  · rw [r5, updz u4.self.zero (by decide), r4]; simp +decide only [upd_app, ↓reduceIte]
    rw [z3, r3, updz z2 (by decide), r2, updz hz (by decide)]; exact BitVec.zero_add _
  · rw [r5, updz u4.self.zero (by decide), r4, updz u3.self.zero (by decide), r3]; simp +decide only [upd_app, ↓reduceIte]
    rw [z2, r2, updz hz (by decide)]; exact BitVec.zero_add _
  · have n10 : q ≠ a0 := fun e => hq (by rw [e]; decide)
    have n9 : q ≠ (9 : Fin 32) := fun e => hq (by rw [e]; decide)
    have n18 : q ≠ (18 : Fin 32) := fun e => hq (by rw [e]; decide)
    have n2 : q ≠ sp := fun e => hq (by rw [e]; decide)
    rw [r5, updz u4.self.zero n10, r4, updz u3.self.zero n9, r3, updz z2 n18, r2, updz hz n2]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The epilogue, from 0x56: restore the saved registers and `sp`, and
return. -/
theorem ls8_epi {M : Word → BitVec 8} {P F : Word} {v : Fin 32 → Word} {n : Machine}
    (st : St M P n 0x56 (reg n)) (hc : CodeIn M P lincombShift8Code) (hFa : F.toNat % 4 = 0) (rsp : reg n sp = F)
    (hsl : ∀ r o, (r, o) ∈ lsPs8 → memLoad32 M (F + o) = v r) :
    ∃ n', Steps n n' ∧ n'.pc = v ra &&& ~~~1 ∧ reg n' sp = F + 0x70 ∧ n'.mem = M ∧
      (∀ r o, (r, o) ∈ lsPs8 → reg n' r = v r) ∧
      ∀ q, q.val ∉ [1, 8, 9, 18] → q ≠ sp → reg n' q = reg n q := by
  obtain ⟨n4, c4, u4⟩ := St.block (restoreBlock lsPs8) st hc lsRestore_end8
    (restoreBlock_ok M _ lsPs8 (reg n) rsp lsPs8_sp fun p hp => fr_al' hFa (lsPs8_range p hp).1)
  simp only [restoreBlock_run M _ lsPs8 (reg n) rsp lsPs8_sp] at u4
  have rsp4 : restoreRegs M F (reg n) lsPs8 sp = F := by rw [restoreRegs_sp _ _ _ _ lsPs8_sp]; exact rsp
  obtain ⟨n5, d5, u5⟩ := u4.aluImm hc ls8_at_5e (off' := 0x60) (by decide)
  obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.jalr hc ls8_at_60
  refine ⟨n6, c4.trans (.cons d5 (.single d6)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc6]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
    rw [add_lit_zero, hsl ra 0x6C (by decide)]
  · rw [regs6]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [rsp4]; try rfl
  · exact mem6
  · intro r o h
    rw [regs6]
    simp only [lsPs8, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp +decide only [upd_app, ↓reduceIte]
      simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact hsl _ _ (by decide)
  · intro q hq hs
    have ne : ∀ w : Fin 32, w.val ∈ [1, 8, 9, 18] → q ≠ w := fun w hw e => hq (e ▸ hw)
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; exact (show reg n6 0 = 0 from rfl).trans (show reg n 0 = 0 from rfl).symm
    rw [regs6]
    simp only [upd_app, h0, hs, ite_false]
    simp only [restoreRegs]
    simp only [upd_app, h0, ne ra (by decide), ne 8 (by decide), ne 9 (by decide), ne 18 (by decide), ite_false]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
/-- **The compiled `SignedInt<8>::lincomb_int_reduce_shift::<2>`**, called with
the result at `res`, the signed operands at `ap` and `bp`, the `i64` operands
at `cp` and `dp`, and a shift `s` from 1 to 63: with `σ` and `A` the sign and
magnitude of `a c + b d` that `lincomb_int` computes, the result's sign byte
is `σ` and its magnitude is `A / 2 ^ s` modulo `2 ^ 256`. It returns with `sp`
and the callee-saved registers as they were, and writes nothing outside the
0x1F0 bytes of stack at `G` and the result. -/
theorem lincombShift8_correct (m : Machine) {P G res ap bp cp dp retAddr : Word} {s : Nat}
    (env : LSEnv8 m.mem P G res ap bp cp dp) (hpc : m.pc = P) (hsp : reg m sp = G + 0x1F0)
    (ha0 : reg m a0 = res) (ha1 : reg m a1 = ap) (ha2 : reg m a2 = bp) (ha3 : reg m a3 = cp)
    (ha4 : reg m a4 = dp) (ha5 : reg m a5 = BitVec.ofNat 32 s) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hs1 : 1 ≤ s) (hs2 : s ≤ 63)
    (hsa : (m.mem (ap + 0x20)).toNat ≤ 1) (hsb : (m.mem (bp + 0x20)).toNat ≤ 1) :
    ∃ m' σ A, Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = G + 0x1F0 ∧
      (∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      σ ≤ 1 ∧
      sgnVal σ A = sgnVal (m.mem (ap + 0x20)).toNat (accV m.mem ap 8) * i64Val (accV m.mem cp 2) +
        sgnVal (m.mem (bp + 0x20)).toNat (accV m.mem bp 8) * i64Val (accV m.mem dp 2) ∧
      (m'.mem (res + 0x20)).toNat = σ ∧ accV m'.mem res 8 = A / 2 ^ s % 2 ^ 256 ∧
      ∀ x, Sep G 0x1F0 x 1 → Sep res 33 x 1 → m'.mem x = m.mem x := by
  obtain ⟨F, hF⟩ : ∃ F, G + 0x180 = F := ⟨_, rfl⟩
  have hGt := env.hGt
  have tG : ∀ c, c < 0x1F0 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show G.toNat + c < 2 ^ 32 by omega)]
  have fG : ∀ c, F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x180 + c) := fun c => by
    rw [← hF, show (0x180 : Word) = BitVec.ofNat 32 0x180 from rfl, add_ofNat_assoc]
  have eF : F = G + BitVec.ofNat 32 0x180 := hF.symm
  have hFn : F.toNat = G.toNat + 0x180 := by rw [eF, tG _ (by decide)]
  have hFa : F.toNat % 4 = 0 := by rw [hFn]; have := env.hG; omega
  have aG : ∀ c, c % 4 = 0 → c < 0x1F0 → (G + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [tG c h2]; have := env.hG; omega
  -- every address the function names, as an offset from `G`
  have e8 : F + 8 = G + BitVec.ofNat 32 0x188 := fG 8
  have e38 : F + 0x28 = G + BitVec.ofNat 32 0x1A8 := fG 0x28
  have e44 : F + 0x34 = G + BitVec.ofNat 32 0x1B4 := fG 0x34
  have eS : F + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x170 := by rw [eF, BitVec.add_assoc]; rfl
  have eLc : lcR8 F = G := by
    show F + 0xFFFFFE80 = G
    rw [eF, BitVec.add_assoc, show BitVec.ofNat 32 0x180 + 0xFFFFFE80 = BitVec.ofNat 32 0 from rfl, add_ofNat_zero]
  have eSh : shF8 F = G + BitVec.ofNat 32 0x110 := by show F + 0xFFFFFF90 = _; rw [eF, BitVec.add_assoc]; rfl
  have sub : ∀ {b : Word} {k : Nat} (c l : Nat), c + l ≤ 0x1F0 → Sep G 0x1F0 b k → Sep (G + BitVec.ofNat 32 c) l b k :=
    fun c l h hs => hs.sub h
  have sG : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x1F0 → d + k ≤ 0x1F0 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun h h1 h2 =>
    sep_offsets G h (by omega) (by omega)
  have g0 : ∀ {b : Word} {k : Nat} (l : Nat), l ≤ 0x1F0 → Sep G 0x1F0 b k → Sep G l b k := fun l h hs => by
    have := hs.sub (c := 0) (l := l) (by omega); rwa [add_ofNat_zero] at this
  have inF : ∀ {b : Word} {k : Nat}, Sep G 0x1F0 b k → Sep F 0x70 b k := fun h => by
    rw [eF]; exact sub 0x180 0x70 (by decide) h
  have cOf : ∀ {M : Word → BitVec 8}, (∀ x, Sep G 0x1F0 x 1 → M x = m.mem x) →
      ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep G 0x1F0 b code.length → CodeIn M b code :=
    fun hM _ _ hc hs i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have opG : ∀ {M : Word → BitVec 8}, (∀ x, Sep G 0x1F0 x 1 → M x = m.mem x) →
      ∀ {b : Word} {n : Nat}, Sep b (4 * n) G 0x1F0 → accV M b n = accV m.mem b n := fun hM _ n hb =>
    accV_congr n fun i hi => memLoad32_congr fun j hj => hM _ (by
      have := hb.symm.subR (c := 4 * i + j) (l := 1) (by omega)
      rwa [← add_ofNat_assoc] at this)
  have byG : ∀ {M : Word → BitVec 8}, (∀ x, Sep G 0x1F0 x 1 → M x = m.mem x) →
      ∀ {b : Word}, Sep b 33 G 0x1F0 → M (b + 0x20) = m.mem (b + 0x20) := fun hM _ hb =>
    hM _ (hb.symm.subR (c := 0x20) (l := 1) (by omega))
  -- the prologue
  obtain ⟨n1, M1, c1, st1, fr1, sl1, sp1, a01, s1_1, s2_1, k1⟩ :=
    ls8_pro m env.code hFa (inF env.sC) hpc (by rw [hsp, ← hF, BitVec.add_assoc]; rfl)
  have frG1 : ∀ x, Sep G 0x1F0 x 1 → M1 x = m.mem x := fun x hx => fr1 x (inF hx)
  -- `lincomb_int(a, b, c, d)` into `F + 0x34`
  obtain ⟨t1, ct1, pct1, memt1, regst1⟩ := st1.callRa (cOf frG1 env.code env.sC) ls8_at_10 ls8_at_14
    (cb := P + 0x62) (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x62 (by decide))
  have rt1 := PEnv.reg1 regst1 st1.zero
  have LE : LCEnv8 t1.mem (P + 0x62) F (F + 0x34) ap bp cp dp := by
    rw [memt1]
    exact {
      hP := even_at P env.hP 0x62 (by decide)
      code := cOf frG1 env.lc env.sL
      abs := cOf frG1 env.abs env.sA
      wide := cOf frG1 env.wide env.sW
      neg := cOf frG1 env.neg env.sN
      mset := cOf frG1 env.mset env.sM
      stub := cOf frG1 env.stub env.sU
      body := cOf frG1 env.body env.sB
      bsub := cOf frG1 env.bsub env.sBs
      sel2 := cOf frG1 env.sel2 env.s2
      sel12 := cOf frG1 env.sel12 env.s12
      zero := cOf frG1 env.zero env.sZ
      one := cOf frG1 env.one env.sO
      hsp := hFa
      hS := by omega
      hout := by rw [e44]; exact aG _ (by decide) (by decide)
      hap := env.hap
      hbp := env.hbp
      hcp := env.hcp
      hdp := env.hdp
      hwo := by rw [e44, tG _ (by decide)]; omega
      hwa := env.hwa
      hwb := env.hwb
      sC := by rw [eLc]; exact g0 0x180 (by decide) env.sL
      sA := by rw [eLc]; exact g0 0x180 (by decide) env.sA
      sW := by rw [eLc]; exact g0 0x180 (by decide) env.sW
      sN := by rw [eLc]; exact g0 0x180 (by decide) env.sN
      sM := by rw [eLc]; exact g0 0x180 (by decide) env.sM
      sU := by rw [eLc]; exact g0 0x180 (by decide) env.sU
      sB := by rw [eLc]; exact g0 0x180 (by decide) env.sB
      sBs := by rw [eLc]; exact g0 0x180 (by decide) env.sBs
      s2 := by rw [eLc]; exact g0 0x180 (by decide) env.s2
      s12 := by rw [eLc]; exact g0 0x180 (by decide) env.s12
      sZ := by rw [eLc]; exact g0 0x180 (by decide) env.sZ
      sO := by rw [eLc]; exact g0 0x180 (by decide) env.sO
      oR := by
        rw [eLc, e44]
        have := sG (c := 0x1B4) (n := 41) (d := 0) (k := 0x180) (.inr (by decide)) (by decide) (by decide)
        rwa [add_ofNat_zero] at this
      aR := by rw [eLc]; exact (g0 0x180 (by decide) env.aG.symm).symm
      bR := by rw [eLc]; exact (g0 0x180 (by decide) env.bG.symm).symm
      cR := by rw [eLc]; exact (g0 0x180 (by decide) env.cG.symm).symm
      dR := by rw [eLc]; exact (g0 0x180 (by decide) env.dG.symm).symm
      oC := by rw [e44]; exact sub 0x1B4 41 (by decide) env.sL
      oB := by rw [e44]; exact sub 0x1B4 41 (by decide) env.sB }
  obtain ⟨t2, ct2, pct2, spt2, kt2, sgt2, valt2, frt2⟩ := lincomb8_correct t1 LE pct1
    (by rw [rt1 _ (by decide), sp1]) (by rw [rt1 _ (by decide), a01])
    (by rw [rt1 _ (by decide), k1 _ (by decide), ha1]) (by rw [rt1 _ (by decide), k1 _ (by decide), ha2])
    (by rw [rt1 _ (by decide), k1 _ (by decide), ha3]) (by rw [rt1 _ (by decide), k1 _ (by decide), ha4])
    (by rw [regst1]; simp [upd]) (even_clear _ (even_at P env.hP (0x10 + 8) (by decide)))
    (by rw [memt1, byG frG1 env.aG]; exact hsa) (by rw [memt1, byG frG1 env.bG]; exact hsb)
  rw [memt1, byG frG1 env.aG, byG frG1 env.bG, opG frG1 (n := 8) (sep_pre env.aG (by decide)), opG frG1 (n := 8) (sep_pre env.bG (by decide)),
    opG frG1 (n := 2) (by exact sep_pre env.cG (by decide)), opG frG1 (n := 2) (by exact sep_pre env.dG (by decide))]
    at valt2
  rw [memt1] at frt2
  have frG2 : ∀ x, Sep G 0x1F0 x 1 → t2.mem x = m.mem x := fun x hx => by
    rw [frt2 x (by rw [eLc]; exact g0 0x180 (by decide) hx) (by rw [e44]; exact sub 0x1B4 41 (by decide) hx), frG1 x hx]
  -- the low limbs to `F + 8`
  have st2 : St t2.mem P t2 0x18 (reg t2) := ⟨pct2, rfl, fun _ => rfl⟩
  have hc2 := cOf frG2 env.code env.sC
  obtain ⟨u1, du1, vu1⟩ := st2.aluImm hc2 ls8_at_18 (off' := 0x1A) (by decide)
  have ku1 := vu1.oldReg st2.zero
  obtain ⟨u2, du2, vu2⟩ := vu1.self.aluImm hc2 ls8_at_1a (off' := 0x1C) (by decide)
  have ku2 := vu2.oldReg vu1.self.zero
  obtain ⟨u3, du3, vu3⟩ := vu2.self.aluImm hc2 ls8_at_1c (off' := 0x20) (by decide)
  have ku3 := vu3.oldReg vu2.self.zero
  have spu3 : reg u3 sp = F := by rw [ku3 _ (by decide), ku2 _ (by decide), ku1 _ (by decide), spt2]
  have a0u3 : reg u3 a0 = F + 8 := by
    rw [ku3 _ (by decide), ku2 _ (by decide), vu1.newReg (by decide)]; show reg t2 sp + 8 = _; rw [spt2]
  have a1u3 : reg u3 a1 = F + 0x34 := by
    rw [ku3 _ (by decide), vu2.newReg (by decide)]; show reg u1 sp + 0x34 = _; rw [ku1 _ (by decide), spt2]
  have a2u3 : reg u3 a2 = BitVec.ofNat 32 32 := by
    rw [vu3.newReg (by decide)]; show reg u2 x0 + 0x20 = _; rw [vu2.self.zero]; rfl
  have hev1 : (P + 0x62 + 0x3AAC : Word).toNat % 2 = 0 :=
    even_at (P + 0x62) (even_at P env.hP 0x62 (by decide)) 0x3AAC (by decide)
  obtain ⟨t3, ct3, pct3, memt3, regst3⟩ := vu3.self.callRa hc2 ls8_at_20 ls8_at_24 (cb := P + 0x62 + 0x3AAC)
    (by simp only [BitVec.add_assoc] <;> rfl) hev1
  have rt3 := PEnv.reg1 regst3 vu3.self.zero
  have spt3 : reg t3 sp = F := by rw [rt3 _ (by decide), spu3]
  have scr : ∀ c, 0x180 ≤ c → c < 0x1F0 → Sep (G + BitVec.ofNat 32 0x170) 16 (G + BitVec.ofNat 32 c) 1 :=
    fun c h1 h2 => sG (.inl (by omega)) (by decide) (by omega)
  obtain ⟨t4, ct4, pct4, spt4, -, memt4, kt4⟩ := memcpy_correct t3 (P + 0x62 + 0x3AAC) (P + BitVec.ofNat 32 (0x20 + 8))
    (F + 8) (F + 0x34) 32 (fun i hi => by rw [memt3]; exact cOf frG2 env.stub env.sU i hi) hev1 pct3
    (by rw [rt3 _ (by decide), a0u3]) (by rw [rt3 _ (by decide), a1u3]) (by rw [rt3 _ (by decide), a2u3])
    (by rw [regst3]; simp [upd]) (even_clear _ (even_at P env.hP (0x20 + 8) (by decide)))
    (by
      rw [memt3, spt3, show P + 0x62 + 0x3AAC + 8 = P + 0x62 + 0x3AB4 by rw [BitVec.add_assoc]; rfl, eS, e8, e44]
      exact {
        code := cOf frG2 env.body env.sB
        hDC := sub 0x188 32 (by decide) env.sB
        hFC := sub 0x170 16 (by decide) env.sB
        hdF := sG (.inr (by decide)) (by decide) (by decide)
        hsF := sG (.inr (by decide)) (by decide) (by decide)
        hsep := sG (.inl (by decide)) (by decide) (by decide)
        hF := aG _ (by decide) (by decide)
        hFw := by rw [tG _ (by decide)]; omega
        hdw := by rw [tG _ (by decide)]; omega
        hsw := by rw [tG _ (by decide)]; omega })
  rw [spt3, eS, memt3] at memt4
  have frG4 : ∀ x, Sep G 0x1F0 x 1 → t4.mem x = m.mem x := fun x hx => by
    rw [memt4 x (sub 0x170 16 (by decide) hx), copyBytes_sep (by rw [e8]; exact sub 0x188 32 (by decide) hx) (Nat.le_refl _),
      frG2 x hx]
  have ld4 : ∀ i, i < 8 → memLoad32 t4.mem (F + 8 + BitVec.ofNat 32 (4 * i)) =
      memLoad32 t2.mem (F + 0x34 + BitVec.ofNat 32 (4 * i)) := fun i hi => by
    have h1 : memLoad32 t4.mem (F + 8 + BitVec.ofNat 32 (4 * i)) =
        memLoad32 (copyBytes t2.mem (F + 8) (F + 0x34) 32) (F + 8 + BitVec.ofNat 32 (4 * i)) :=
      memLoad32_congr fun j hj => memt4 _ (by rw [e8, add_ofNat_assoc, add_ofNat_assoc]; exact scr _ (by omega) (by omega))
    rw [h1, cb_load (by omega) (by decide)]
  have kp4 : ∀ c, 0x28 ≤ c → c < 0x70 → t4.mem (F + BitVec.ofNat 32 c) = t2.mem (F + BitVec.ofNat 32 c) :=
    fun c h1 h2 => by
      rw [memt4 _ (by rw [fG]; exact scr _ (by omega) (by omega)),
        copyBytes_sep (by rw [e8, fG]; exact sG (.inl (by omega)) (by decide) (by omega)) (Nat.le_refl _)]
  have kw4 : ∀ c, 0x28 ≤ c → c + 4 ≤ 0x70 →
      memLoad32 t4.mem (F + BitVec.ofNat 32 c) = memLoad32 t2.mem (F + BitVec.ofNat 32 c) := fun c h1 h2 =>
    memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact kp4 _ (by omega) (by omega)
  -- the high limbs to `F + 0x28`, and the sign to `s0`
  have st4 : St t4.mem P t4 0x28 (reg t4) := ⟨pct4, rfl, fun _ => rfl⟩
  have hc4 := cOf frG4 env.code env.sC
  have sp4 : reg t4 sp = F := by rw [spt4, spt3]
  obtain ⟨v1, dv1, wv1⟩ := st4.lwE hc4 ls8_at_28 (off' := 0x2A) (by decide)
    (by rw [sp4]; exact fr_al' hFa (by decide)) (v := memLoad32 t2.mem (F + BitVec.ofNat 32 0x54))
    (by rw [sp4]; exact kw4 0x54 (by decide) (by decide))
  have kv1 := wv1.oldReg st4.zero
  obtain ⟨v2, dv2, wv2⟩ := wv1.self.lwE hc4 ls8_at_2a (off' := 0x2C) (by decide)
    (by rw [kv1 _ (by decide), sp4]; exact fr_al' hFa (by decide)) (v := memLoad32 t2.mem (F + BitVec.ofNat 32 0x58))
    (by rw [kv1 _ (by decide), sp4]; exact kw4 0x58 (by decide) (by decide))
  have kv2 := wv2.oldReg wv1.self.zero
  obtain ⟨v3, dv3, wv3⟩ := wv2.self.lbu hc4 ls8_at_2c (off' := 0x30) (by decide)
  have kv3 := wv3.oldReg wv2.self.zero
  have spv3 : reg v3 sp = F := by rw [kv3 _ (by decide), kv2 _ (by decide), kv1 _ (by decide), sp4]
  have s0v3 : reg v3 (8 : Fin 32) = (t2.mem (F + BitVec.ofNat 32 0x5C)).zeroExtend 32 := by
    rw [wv3.newReg (by decide)]
    show (t4.mem (reg v2 sp + 0x5C)).zeroExtend 32 = _
    rw [kv2 _ (by decide), kv1 _ (by decide), sp4]; exact congrArg _ (kp4 0x5C (by decide) (by decide))
  have a0v3 : reg v3 a0 = memLoad32 t2.mem (F + BitVec.ofNat 32 0x54) := by
    rw [kv3 _ (by decide), kv2 _ (by decide), wv1.newReg (by decide)]
  have a1v3 : reg v3 a1 = memLoad32 t2.mem (F + BitVec.ofNat 32 0x58) := by
    rw [kv3 _ (by decide), wv2.newReg (by decide)]
  obtain ⟨v4, dv4, wv4⟩ := wv3.self.swG hc4 ls8_at_30 (off' := 0x32) (by decide)
    (by rw [spv3]; exact fr_al' hFa (by decide)) (a := F + 0x28) (by rw [spv3]) a0v3
  have hc5a : CodeIn (memStore32 t4.mem (F + 0x28) (memLoad32 t2.mem (F + BitVec.ofNat 32 0x54))) P
      lincombShift8Code := hc4.store32 (by rw [e38]; exact sub 0x1A8 4 (by decide) env.sC)
  obtain ⟨v5, dv5, wv5⟩ := wv4.swG hc5a ls8_at_32 (off' := 0x34) (by decide)
    (by rw [spv3]; exact fr_al' hFa (by decide)) (a := F + 0x2C) (by rw [spv3]) a1v3
  obtain ⟨M5, hM5⟩ : ∃ M, memStore32 (memStore32 t4.mem (F + 0x28) (memLoad32 t2.mem (F + BitVec.ofNat 32 0x54)))
      (F + 0x2C) (memLoad32 t2.mem (F + BitVec.ofNat 32 0x58)) = M := ⟨_, rfl⟩
  rw [hM5] at wv5
  have e3C : F + 0x2C = G + BitVec.ofNat 32 0x1AC := fG 0x2C
  have M5x : ∀ x, Sep (F + 0x28) 8 x 1 → M5 x = t4.mem x := fun x hx => by
    rw [← hM5, memStore32_get_sep (by
        rw [e3C]; rw [e38] at hx; have := hx.sub (c := 4) (l := 4) (by decide); rwa [add_ofNat_assoc] at this),
      memStore32_get_sep (by rw [e38]; rw [e38] at hx; have := hx.sub (c := 0) (l := 4) (by decide); rwa [add_ofNat_zero] at this)]
  have frG5 : ∀ x, Sep G 0x1F0 x 1 → M5 x = m.mem x := fun x hx => by
    rw [M5x x (by rw [e38]; exact sub 0x1A8 8 (by decide) hx), frG4 x hx]
  have hc5 : CodeIn M5 P lincombShift8Code := cOf frG5 env.code env.sC
  obtain ⟨v6, dv6, wv6⟩ := wv5.aluImm hc5 ls8_at_34 (off' := 0x36) (by decide)
  have kv6 := wv6.oldReg wv5.zero
  obtain ⟨v7, dv7, wv7⟩ := wv6.self.aluImm hc5 ls8_at_36 (off' := 0x38) (by decide)
  have kv7 := wv7.oldReg wv6.self.zero
  obtain ⟨v8, dv8, wv8⟩ := wv7.self.alu hc5 ls8_at_38 (off' := 0x3A) (by decide)
  have kv8 := wv8.oldReg wv7.self.zero
  have rv3 : ∀ q, q ≠ (8 : Fin 32) → q ≠ a0 → q ≠ a1 → reg v3 q = reg t4 q := fun q h8 h0 h1 => by
    rw [kv3 q h8, kv2 q h1, kv1 q h0]
  have rv8 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg v8 q = reg v3 q := fun q h0 h1 h2 => by
    rw [kv8 q h2, kv7 q h1, kv6 q h0]
  have spv8 : reg v8 sp = F := by rw [rv8 _ (by decide) (by decide) (by decide), spv3]
  have a0v8 : reg v8 a0 = F + 8 := by
    rw [kv8 _ (by decide), kv7 _ (by decide), wv6.newReg (by decide)]; show reg v3 sp + 8 = _
    rw [spv3]
  have a1v8 : reg v8 a1 = F + 0x28 := by
    rw [kv8 _ (by decide), wv7.newReg (by decide)]; show reg v6 sp + 0x28 = _
    rw [kv6 _ (by decide), spv3]
  have back4 : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg t4 q = reg n1 q :=
    fun q hq => by
      have nq : ∀ r : Fin 32, r.val ∉ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ r :=
        fun r hr e => hr (e ▸ hq)
      rw [kt4 q (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide))
        (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)) (nq 7 (by decide))
        (nq 28 (by decide)) (nq 29 (by decide)) (nq 30 (by decide)) (nq _ (by decide)),
        rt3 q (nq _ (by decide)), ku3 q (nq _ (by decide)), ku2 q (nq _ (by decide)), ku1 q (nq _ (by decide)),
        kt2 q (by revert hq; revert q; decide), rt1 q (nq _ (by decide))]
  have s2v8 : reg v8 a2 = BitVec.ofNat 32 s := by
    rw [wv8.newReg (by decide)]; show reg v7 x0 + reg v7 (18 : Fin 32) = _
    rw [wv7.self.zero, kv7 _ (by decide), kv6 _ (by decide), rv3 _ (by decide) (by decide) (by decide),
      back4 _ (by decide), s2_1, ha5]; exact BitVec.zero_add _
  -- `shr_in_place_wide(F + 8, F + 0x28, s)`
  obtain ⟨t5, ct5, pct5, memt5, regst5⟩ := wv8.self.callRa hc5 ls8_at_3a ls8_at_3e (cb := P + 0x1E6)
    (by simp only [BitVec.add_assoc] <;> rfl) (even_at P env.hP 0x1E6 (by decide))
  have rt5 := PEnv.reg1 regst5 wv8.self.zero
  have eMs : P + 0x1E6 + 0x38C0 = P + 0x62 + 0x3A44 := by simp only [BitVec.add_assoc] <;> rfl
  have eSt : P + 0x1E6 + 0x3928 = P + 0x62 + 0x3AAC := by simp only [BitVec.add_assoc] <;> rfl
  have eBd : P + 0x1E6 + 0x3930 = P + 0x62 + 0x3AB4 := by simp only [BitVec.add_assoc] <;> rfl
  have SE : SHEnv8 t5.mem (P + 0x1E6) F (F + 8) (F + 0x28) := by
    rw [memt5]
    exact {
      hP := even_at P env.hP 0x1E6 (by decide)
      code := cOf frG5 env.shr env.sS
      lm := cOf frG5 env.lm env.sLm
      tr := cOf frG5 env.tr env.sTr
      mset := by rw [eMs]; exact cOf frG5 env.mset env.sM
      stub := by rw [eSt]; exact cOf frG5 env.stub env.sU
      body := by rw [eBd]; exact cOf frG5 env.body env.sB
      hsp := hFa
      hS := by omega
      hlo := by rw [e8]; exact aG _ (by decide) (by decide)
      hhi := by rw [e38]; exact aG _ (by decide) (by decide)
      hwl := by rw [e8, tG _ (by decide)]; omega
      hwh := by rw [e38, tG _ (by decide)]; omega
      sC := by rw [eSh]; exact sub 0x110 0x70 (by decide) env.sS
      sLm := by rw [eSh]; exact sub 0x110 0x70 (by decide) env.sLm
      sTr := by rw [eSh]; exact sub 0x110 0x70 (by decide) env.sTr
      sMs := by rw [eSh, eMs]; exact sub 0x110 0x70 (by decide) env.sM
      sU := by rw [eSh, eSt]; exact sub 0x110 0x70 (by decide) env.sU
      sB := by rw [eSh, eBd]; exact sub 0x110 0x70 (by decide) env.sB
      sL := by rw [eSh, e8]; exact sG (.inr (by decide)) (by decide) (by decide)
      sH := by rw [eSh, e38]; exact sG (.inr (by decide)) (by decide) (by decide)
      sLH := by rw [e8, e38]; exact sG (.inl (by decide)) (by decide) (by decide)
      lC := by rw [e8]; exact sub 0x188 32 (by decide) env.sS
      lB := by rw [e8, eBd]; exact sub 0x188 32 (by decide) env.sB
      hC := by rw [e38]; exact sub 0x1A8 8 (by decide) env.sS
      hLm := by rw [e38]; exact sub 0x1A8 8 (by decide) env.sLm
      hTr := by rw [e38]; exact sub 0x1A8 8 (by decide) env.sTr
      hMs := by rw [e38, eMs]; exact sub 0x1A8 8 (by decide) env.sM
      hU := by rw [e38, eSt]; exact sub 0x1A8 8 (by decide) env.sU
      hB := by rw [e38, eBd]; exact sub 0x1A8 8 (by decide) env.sB }
  obtain ⟨t6, ct6, pct6, spt6, kt6, valt6, frt6⟩ := shr8_correct t5 SE pct5
    (by rw [rt5 _ (by decide), spv8]) (by rw [rt5 _ (by decide), a0v8]) (by rw [rt5 _ (by decide), a1v8])
    (by rw [rt5 _ (by decide), s2v8]) (by rw [regst5]; simp [upd])
    (even_clear _ (even_at P env.hP (0x3A + 8) (by decide))) hs1 hs2
  rw [memt5] at valt6 frt6
  have frG6 : ∀ x, Sep G 0x1F0 x 1 → t6.mem x = m.mem x := fun x hx => by
    rw [frt6 x (by rw [eSh]; exact sub 0x110 0x70 (by decide) hx) (by rw [e8]; exact sub 0x188 32 (by decide) hx)
      (by rw [e38]; exact sub 0x1A8 8 (by decide) hx), frG5 x hx]
  -- the shifted low limbs to `res`
  have st6 : St t6.mem P t6 0x42 (reg t6) := ⟨pct6, rfl, fun _ => rfl⟩
  have hc6 := cOf frG6 env.code env.sC
  obtain ⟨x1, dx1, wx1⟩ := st6.aluImm hc6 ls8_at_42 (off' := 0x44) (by decide)
  have kx1 := wx1.oldReg st6.zero
  obtain ⟨x2, dx2, wx2⟩ := wx1.self.aluImm hc6 ls8_at_44 (off' := 0x48) (by decide)
  have kx2 := wx2.oldReg wx1.self.zero
  obtain ⟨x3, dx3, wx3⟩ := wx2.self.alu hc6 ls8_at_48 (off' := 0x4A) (by decide)
  have kx3 := wx3.oldReg wx2.self.zero
  have rx3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg x3 q = reg t6 q := fun q h0 h1 h2 => by
    rw [kx3 q h0, kx2 q h2, kx1 q h1]
  have rt6 : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg t6 q = reg v3 q :=
    fun q hq => by
      have nq : ∀ r : Fin 32, r.val ∉ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ r :=
        fun r hr e => hr (e ▸ hq)
      rw [kt6 q (by revert hq; revert q; decide), rt5 q (nq _ (by decide)),
        rv8 q (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide))]
  have spx3 : reg x3 sp = F := by rw [rx3 _ (by decide) (by decide) (by decide), spt6]
  have a0x3 : reg x3 a0 = res := by
    rw [wx3.newReg (by decide)]; show reg x2 x0 + reg x2 (9 : Fin 32) = _
    rw [wx2.self.zero, kx2 _ (by decide), kx1 _ (by decide), rt6 _ (by decide),
      rv3 _ (by decide) (by decide) (by decide), back4 _ (by decide), s1_1, ha0]; exact BitVec.zero_add _
  have a1x3 : reg x3 a1 = F + 8 := by
    rw [kx3 _ (by decide), kx2 _ (by decide), wx1.newReg (by decide)]; show reg t6 sp + 8 = _
    rw [spt6]
  have a2x3 : reg x3 a2 = BitVec.ofNat 32 32 := by
    rw [kx3 _ (by decide), wx2.newReg (by decide)]; show reg x1 x0 + 0x20 = _; rw [wx1.self.zero]; rfl
  obtain ⟨t7, ct7, pct7, memt7, regst7⟩ := wx3.self.callRa hc6 ls8_at_4a ls8_at_4e (cb := P + 0x62 + 0x3AAC)
    (by simp only [BitVec.add_assoc] <;> rfl) hev1
  have rt7 := PEnv.reg1 regst7 wx3.self.zero
  have spt7 : reg t7 sp = F := by rw [rt7 _ (by decide), spx3]
  obtain ⟨t8, ct8, pct8, spt8, -, memt8, kt8⟩ := memcpy_correct t7 (P + 0x62 + 0x3AAC) (P + BitVec.ofNat 32 (0x4A + 8))
    res (F + 8) 32 (fun i hi => by rw [memt7]; exact cOf frG6 env.stub env.sU i hi) hev1 pct7
    (by rw [rt7 _ (by decide), a0x3]) (by rw [rt7 _ (by decide), a1x3]) (by rw [rt7 _ (by decide), a2x3])
    (by rw [regst7]; simp [upd]) (even_clear _ (even_at P env.hP (0x4A + 8) (by decide)))
    (by
      rw [memt7, spt7, show P + 0x62 + 0x3AAC + 8 = P + 0x62 + 0x3AB4 by rw [BitVec.add_assoc]; rfl, eS, e8]
      exact {
        code := cOf frG6 env.body env.sB
        hDC := sep_pre env.rB (by decide)
        hFC := sub 0x170 16 (by decide) env.sB
        hdF := (sub 0x170 16 (by decide) (sep_pre env.rG (by decide)).symm).symm
        hsF := sG (.inr (by decide)) (by decide) (by decide)
        hsep := (sub 0x188 32 (by decide) (sep_pre env.rG (by decide)).symm).symm
        hF := aG _ (by decide) (by decide)
        hFw := by rw [tG _ (by decide)]; omega
        hdw := by have := env.hwr; omega
        hsw := by rw [tG _ (by decide)]; omega })
  rw [spt7, eS, memt7] at memt8
  have frR8 : ∀ x, Sep G 0x1F0 x 1 → Sep res 32 x 1 → t8.mem x = m.mem x := fun x hx hr => by
    rw [memt8 x (sub 0x170 16 (by decide) hx), copyBytes_sep hr (Nat.le_refl _), frG6 x hx]
  have hc8 : CodeIn t8.mem P lincombShift8Code := fun i hi => by
    rw [frR8 _ (env.sC.subR (c := i) (l := 1) (by omega)) ((sep_pre env.rC (by decide)).subR (c := i) (l := 1) (by omega))]
    exact env.code i hi
  -- the sign
  have st8 : St t8.mem P t8 0x52 (reg t8) := ⟨pct8, rfl, fun _ => rfl⟩
  have keep8 : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg t8 q = reg v3 q :=
    fun q hq => by
      have nq : ∀ r : Fin 32, r.val ∉ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ r :=
        fun r hr e => hr (e ▸ hq)
      rw [kt8 q (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide))
        (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)) (nq 7 (by decide))
        (nq 28 (by decide)) (nq 29 (by decide)) (nq 30 (by decide)) (nq _ (by decide)),
        rt7 q (nq _ (by decide)), rx3 q (nq _ (by decide)) (nq _ (by decide)) (nq _ (by decide)), rt6 q hq]
  obtain ⟨t9, dt9, wt9⟩ := st8.sb hc8 ls8_at_52 (off' := 0x56) (by decide)
  have r9a : reg t8 (9 : Fin 32) + 0x20 = res + 0x20 := by
    rw [keep8 _ (by decide), rv3 _ (by decide) (by decide) (by decide), back4 _ (by decide), s1_1, ha0]
  have r9v : (reg t8 (8 : Fin 32)).extractLsb' 0 8 = t2.mem (F + BitVec.ofNat 32 0x5C) := by
    rw [keep8 _ (by decide), s0v3, zext_lo]
  rw [r9a, r9v] at wt9
  obtain ⟨M9, hM9⟩ : ∃ M, memStore8 t8.mem (res + 0x20) (t2.mem (F + BitVec.ofNat 32 0x5C)) = M := ⟨_, rfl⟩
  rw [hM9] at wt9
  have M9x : ∀ x, Sep (res + 0x20) 1 x 1 → M9 x = t8.mem x := fun x hx => by
    rw [← hM9]; exact memStore8_ne fun e => hx 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)
  have r30 : ∀ {x : Word}, Sep res 33 x 1 → Sep (res + 0x20) 1 x 1 := fun h => h.sub (c := 0x20) (l := 1) (by decide)
  have hc9 : CodeIn M9 P lincombShift8Code := by
    rw [← hM9]; exact hc8.store8 (env.rC.sub (c := 0x20) (l := 1) (by decide))
  -- the epilogue
  have r9 : ∀ q, reg t9 q = reg t8 q := wt9.regs
  have spt9 : reg t9 sp = F := by rw [r9, spt8, spt7]
  have resF : ∀ c, 0x60 ≤ c → c < 0x70 → Sep res 33 (F + BitVec.ofNat 32 c) 1 := fun c h1 h2 => by
    rw [fG]; exact env.rG.subR (c := 0x180 + c) (l := 1) (by omega)
  have topB : ∀ c, 0x60 ≤ c → c < 0x70 → M9 (F + BitVec.ofNat 32 c) = M1 (F + BitVec.ofNat 32 c) := fun c h1 h2 => by
    rw [M9x _ (r30 (resF c h1 h2)), memt8 _ (by rw [fG]; exact scr _ (by omega) (by omega)),
      copyBytes_sep (sep_pre (resF c h1 h2) (by decide)) (Nat.le_refl _),
      frt6 _ (by rw [eSh, fG]; exact sG (.inl (by omega)) (by decide) (by omega))
        (by rw [e8, fG]; exact sG (.inl (by omega)) (by decide) (by omega))
        (by rw [e38, fG]; exact sG (.inl (by omega)) (by decide) (by omega)),
      M5x _ (by rw [e38, fG]; exact sG (.inl (by omega)) (by decide) (by omega)), kp4 c (by omega) h2,
      frt2 _ (by
          rw [eLc, fG]
          have := sG (c := 0) (n := 0x180) (d := 0x180 + c) (k := 1) (.inl (by omega)) (by decide) (by omega)
          rwa [add_ofNat_zero] at this)
        (by rw [e44, fG]; exact sG (.inl (by omega)) (by decide) (by omega))]
  have hsl : ∀ r o, (r, o) ∈ lsPs8 → memLoad32 M9 (F + o) = reg m r := fun r o h => by
    have hr : o.toNat % 4 = 0 ∧ 0x60 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x70 := lsPs8_range (r, o) h
    rw [← sl1 r o h, ← ofNat_toNat_self o]
    exact memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact topB _ (by omega) (by omega)
  obtain ⟨n2, c2, pc2, sp2, mem2, rs2, ks2⟩ := ls8_epi (v := reg m) wt9.self hc9 hFa spt9 hsl
  -- the result
  have lo6 : accV t6.mem (F + 8) 8 = (accV t2.mem (F + 0x34) 8 + 2 ^ 256 * accV t2.mem (F + 0x34 + 0x20) 2) / 2 ^ s %
      2 ^ 256 := by
    have hlo5 : accV M5 (F + 8) 8 = accV t2.mem (F + 0x34) 8 := by
      rw [← accV_congr2 8 ld4]
      exact accV_congr 8 fun i hi => memLoad32_congr fun j hj => M5x _ (by
        rw [e8, e38, add_ofNat_assoc, add_ofNat_assoc]; exact sG (.inr (by omega)) (by decide) (by omega))
    have hhi5 : accV M5 (F + 0x28) 2 = accV t2.mem (F + 0x34 + 0x20) 2 := by
      apply accV_congr2 2
      intro i hi
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [show F + 0x28 + BitVec.ofNat 32 (4 * 0) = F + 0x28 by rw [BitVec.add_assoc]; rfl,
          show F + 0x34 + 0x20 + BitVec.ofNat 32 (4 * 0) = F + BitVec.ofNat 32 0x54 by simp only [BitVec.add_assoc] <;> rfl,
          ← hM5, memLoad32_store32_sep (by rw [e3C, e38]; exact sG (.inr (by decide)) (by decide) (by decide)),
          memLoad32_store32_same]
      · rw [show F + 0x28 + BitVec.ofNat 32 (4 * 1) = F + 0x2C by rw [BitVec.add_assoc]; rfl,
          show F + 0x34 + 0x20 + BitVec.ofNat 32 (4 * 1) = F + BitVec.ofNat 32 0x58 by simp only [BitVec.add_assoc] <;> rfl,
          ← hM5, memLoad32_store32_same]
    rw [← hlo5, ← hhi5, ← valt6, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (accV_lt _ _ 8)]
  have resv : accV M9 res 8 = accV t6.mem (F + 8) 8 := by
    apply accV_congr2 8
    intro i hi
    rw [← cb_load (M := t6.mem) (dst := res) (src := F + 8) (N := 32) (by omega) (by decide)]
    exact memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]
      rw [M9x _ (by
          have := sep_offsets res (c := 0x20) (n := 1) (d := 4 * i + j) (k := 1) (.inr (by omega)) (by omega) (by omega)
          rwa [show res + BitVec.ofNat 32 0x20 = res + 0x20 from rfl] at this),
        memt8 _ (by
          have := (env.rG.symm.sub (c := 0x170) (l := 16) (by decide)).subR (c := 4 * i + j) (l := 1) (by omega)
          exact this)]
  refine ⟨n2, (t2.mem (F + 0x34 + 0x28)).toNat,
    accV t2.mem (F + 0x34) 8 + 2 ^ 256 * accV t2.mem (F + 0x34 + 0x20) 2,
    c1.trans (ct1.trans (ct2.trans (.cons du1 (.cons du2 (.cons du3 (ct3.trans (ct4.trans (.cons dv1 (.cons dv2
      (.cons dv3 (.cons dv4 (.cons dv5 (.cons dv6 (.cons dv7 (.cons dv8 (ct5.trans (ct6.trans (.cons dx1 (.cons dx2
      (.cons dx3 (ct7.trans (ct8.trans (.cons dt9 c2))))))))))))))))))))))),
    ?_, ?_, fun q hq => ?_, sgt2, valt2, ?_, ?_, fun x hx hr => ?_⟩
  · rw [pc2, hra, hret]
  · rw [sp2, eF, BitVec.add_assoc]; rfl
  · have hmem : q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨
        q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by
      revert hq; revert q; decide
    rcases hmem with rfl | rfl | rfl | h
    · exact rs2 _ 0x68 (by decide)
    · exact rs2 _ 0x64 (by decide)
    · exact rs2 _ 0x60 (by decide)
    · have hq' : q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert h; revert q; decide
      rw [ks2 q (by revert h; revert q; decide) (fun e => by rw [e] at h; revert h; decide), r9, keep8 q hq',
        rv3 q (fun e => by rw [e] at h; revert h; decide) (fun e => by rw [e] at h; revert h; decide)
          (fun e => by rw [e] at h; revert h; decide), back4 q hq', k1 q (by revert h; revert q; decide)]
  · rw [mem2, ← hM9, memStore8_same,
      show F + 0x34 + 0x28 = F + BitVec.ofNat 32 0x5C by simp only [BitVec.add_assoc] <;> rfl]
  · rw [mem2, resv, lo6]
  · rw [mem2, M9x x (r30 hr), frR8 x hx (sep_pre hr (by decide))]

end C3.RV32
