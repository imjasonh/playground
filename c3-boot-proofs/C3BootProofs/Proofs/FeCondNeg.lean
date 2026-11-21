import C3BootProofs.Proofs.FeNeg
import C3BootProofs.Proofs.FeCondAssign

/-!
# `FieldElement2625::conditional_negate`, as compiled

`subtle`'s default `conditional_negate` negates `self` into a stack
temporary through the proved `<&FieldElement2625 as Neg>::neg`, then calls
the proved `conditional_assign(self, &neg, choice)`.
-/

namespace C3.RV32

open C3.Image

/-- The limbs `conditional_negate` leaves in `self`, for `self`'s limbs at `x`
in `M` and the choice `c`. -/
def feCondNegW (M : Word → BitVec 8) (x c : Word) : Nat → Word := fun i =>
  if c = 1 then
    BitVec.ofNat 32 ((feReduceSpec (feNegZ (limbs M x) 0).toNat (feNegZ (limbs M x) 1).toNat
      (feNegZ (limbs M x) 2).toNat (feNegZ (limbs M x) 3).toNat (feNegZ (limbs M x) 4).toNat
      (feNegZ (limbs M x) 5).toNat (feNegZ (limbs M x) 6).toNat (feNegZ (limbs M x) 7).toNat
      (feNegZ (limbs M x) 8).toNat (feNegZ (limbs M x) 9).toNat).getD i 0)
  else limbs M x i

section
set_option maxRecDepth 20000
theorem fcn_at_10 : fetchRel feCondNegCode 0x10 = some (.auipc ra 0x0, 4) := by decide
theorem fcn_at_14 : fetchRel feCondNegCode 0x14 = some (.jalr ra ra 0x154, 4) := by decide
theorem fcn_at_1e : fetchRel feCondNegCode 0x1E = some (.auipc ra 0x0, 4) := by decide
theorem fcn_at_22 : fetchRel feCondNegCode 0x22 = some (.jalr ra ra 0x12, 4) := by decide
theorem fcn_at_2e : fetchRel feCondNegCode 0x2E = some (.jalr x0 ra 0x0, 2) := by decide

def fcnA : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFFC0, .sw sp ra 0x3C, .sw sp (8 : Fin 32) 0x38, .sw sp (9 : Fin 32) 0x34,
    .alu .add (8 : Fin 32) x0 a1, .alu .add (9 : Fin 32) x0 a0, .aluImm .add a0 sp 0xC, .alu .add a1 x0 (9 : Fin 32)]

def fcnB : List BInstr :=
  [.aluImm .add a1 sp 0xC, .alu .add a0 x0 (9 : Fin 32), .alu .add a2 x0 (8 : Fin 32)]

def fcnC : List BInstr :=
  [.lw ra sp 0x3C, .lw (8 : Fin 32) sp 0x38, .lw (9 : Fin 32) sp 0x34, .aluImm .add sp sp 0x40]

theorem fcnA_end : blockEnd feCondNegCode 0 fcnA = some 0x10 := by decide
theorem fcnB_end : blockEnd feCondNegCode 0x18 fcnB = some 0x1E := by decide
theorem fcnC_end : blockEnd feCondNegCode 0x26 fcnC = some 0x2E := by decide
end

/-- What `conditional_negate` needs: its code and its callees', an aligned
stack with 0xE0 bytes below `sp` for its frame and `neg`'s, and `self`
aligned and apart from the stack region and the code that runs after it is
written. -/
structure FCNEnv (M : Word → BitVec 8) (P sp0 x : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P feCondNegCode
  neg : CodeIn M (P + 0x164) feNegCode
  red : CodeIn M (P + 0x164 + 0xFFFFE370) feReduceCode
  fca : CodeIn M (P + 0x30) feCondAssignCode
  hsa : sp0.toNat % 4 = 0
  hS : 0xE0 ≤ sp0.toNat
  hx : x.toNat % 4 = 0
  hxw : x.toNat + 40 < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFF20) 0xE0 P feCondNegCode.length
  sGN : Sep (sp0 + 0xFFFFFF20) 0xE0 (P + 0x164) feNegCode.length
  sGR : Sep (sp0 + 0xFFFFFF20) 0xE0 (P + 0x164 + 0xFFFFE370) feReduceCode.length
  sGA : Sep (sp0 + 0xFFFFFF20) 0xE0 (P + 0x30) feCondAssignCode.length
  sXG : Sep x 40 (sp0 + 0xFFFFFF20) 0xE0
  sXA : Sep x 40 (P + 0x30) feCondAssignCode.length
  sXC : Sep x 40 P feCondNegCode.length

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `FieldElement2625::conditional_negate`**: with `choice` 0
or 1, it leaves `self` or replaces it with its negation (`reduce` of
`16 p - x`), and changes nothing else but 0xE0 bytes of stack. -/
theorem feCondNeg_correct (m : Machine) {P sp0 x c retAddr : Word} (env : FCNEnv m.mem P sp0 x)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = x) (ha1 : reg m a1 = c) (hc01 : c = 0 ∨ c = 1)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∀ i, i < 10 → limbs m'.mem x i = feCondNegW m.mem x c i) ∧
      ∀ y, Sep (sp0 + 0xFFFFFF20) 0xE0 y 1 → Sep x 40 y 1 → m'.mem y = m.mem y := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFF20 = G := ⟨_, rfl⟩
  have hS := env.hS
  have sGC := env.sGC; have sGN := env.sGN; have sGR := env.sGR; have sGA := env.sGA; have sXG := env.sXG
  rw [hG] at sGC sGN sGR sGA sXG ⊢
  have hGn : G.toNat + 0xE0 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFF20 : Word).toNat = 4294967072 from rfl]
    have := sp0.isLt; omega
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsa (k := 0xFFFFFF20) (by decide)
  obtain ⟨F, hF⟩ : ∃ F, G + 0xA0 = F := ⟨_, rfl⟩
  have hFs : sp0 + 0xFFFFFFC0 = F := by rw [← hF, ← hG, BitVec.add_assoc]; rfl
  have eFG : F + 0xFFFFFF60 = G := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero G
  have eFs : F + 0x40 = sp0 := by rw [← hFs, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have hFn : F.toNat = G.toNat + 0xA0 := by
    rw [← hF, BitVec.toNat_add, show (0xA0 : Word).toNat = 0xA0 from rfl]; have := sp0.isLt; omega
  have hFa : F.toNat % 4 = 0 := by rw [hFn]; omega
  obtain ⟨T, hT⟩ : ∃ T, F + 0xC = T := ⟨_, rfl⟩
  have eTG : T = G + BitVec.ofNat 32 0xAC := by rw [← hT, ← hF, BitVec.add_assoc]; rfl
  have hTa : T.toNat % 4 = 0 := by rw [← hT]; exact aligned_add hFa (k := 0xC) (by decide)
  have sFG : ∀ o, o + 4 ≤ 0x40 → ∀ {b : Word} {l : Nat}, Sep G 0xE0 b l → Sep (F + BitVec.ofNat 32 o) 4 b l :=
    fun o ho b l h => by
      have e : F + BitVec.ofNat 32 o = G + BitVec.ofNat 32 (0xA0 + o) := by rw [← hF]; exact add_ofNat_assoc G 0xA0 o
      rw [e]; exact h.sub (c := 0xA0 + o) (l := 4) (by omega)
  have hc := env.cod
  have st0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := st0.zero
  -- the prologue
  obtain ⟨mA, cA, uA⟩ := St.block fcnA st0 hc fcnA_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, fcnA, upd_app, ↓reduceIte, and_true]
    simp only [ev_add]; rw [hsp, hFs]
    repeat' apply And.intro
    all_goals first | exact True.intro | (refine aligned_add hFa ?_; decide) | exact sFG 0x3C (by decide) sGC |
      exact sFG 0x38 (by decide) sGC | exact sFG 0x34 (by decide) sGC)
  simp only [runBlock, BInstr.run, fcnA] at uA
  have MA := uA.mem
  simp +decide only [upd_app, ↓reduceIte] at MA
  simp only [ev_add] at MA; rw [hsp, hFs] at MA
  have frA : ∀ y, Sep G 0xE0 y 1 → mA.mem y = m.mem y := fun y hy => by
    rw [MA, memStore32_get_sep (a := F + 0x34) (sFG 0x34 (by decide) hy),
      memStore32_get_sep (a := F + 0x38) (sFG 0x38 (by decide) hy),
      memStore32_get_sep (a := F + 0x3C) (sFG 0x3C (by decide) hy)]
  have cInA : ∀ (b : Word) (code : List Nat), CodeIn m.mem b code → Sep G 0xE0 b code.length →
      CodeIn mA.mem b code := fun b code hcb hg i hi => by
    rw [frA _ (hg.subR (c := i) (l := 1) (by omega))]; exact hcb i hi
  have spA : reg mA sp = F := by
    rw [uA.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add]; rw [hsp, hFs]
  have A8 : reg mA (8 : Fin 32) = c := by
    rw [uA.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add]; rw [ha1]; exact BitVec.zero_add c
  have A9 : reg mA (9 : Fin 32) = x := by
    rw [uA.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add]; rw [ha0]; exact BitVec.zero_add x
  have A10 : reg mA a0 = T := by
    rw [uA.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add]; rw [hsp, hFs, hT]
  have A11 : reg mA a1 = x := by
    rw [uA.regs]; simp +decide only [upd_app, ↓reduceIte]; simp only [ev_add]; rw [ha0]
    exact (BitVec.zero_add _).trans (BitVec.zero_add x)
  have kA : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg mA q = reg m q :=
    fun q hq => by
      obtain ⟨h0, h1, h2, h3, h4, h5⟩ : q.val ≠ 0 ∧ q ≠ sp ∧ q ≠ (8 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧ q ≠ a0 ∧
          q ≠ a1 := by revert hq; revert q; decide
      rw [uA.regs]; simp only [upd_ne h0 h1, upd_ne h0 h2, upd_ne h0 h3, upd_ne h0 h4, upd_ne h0 h5]
  have hcA := cInA _ _ hc sGC
  have uA' : St mA.mem P mA 0x10 (reg mA) := ⟨uA.pc, rfl, fun _ => rfl⟩
  -- `neg(self)` into the temporary
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := uA'.callRa hcA fcn_at_10 fcn_at_14 (cb := P + 0x164)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x164 (by decide))
  have r1 : ∀ q, q ≠ ra → reg n1 q = reg mA q := fun q h => by rw [regs1]; exact updz uA'.zero h
  have env1 : FNEnv n1.mem (P + 0x164) F T x := by
    rw [mem1]
    refine ⟨even_at P env.hP 0x164 (by decide), cInA _ _ env.neg sGN, cInA _ _ env.red sGR, hFa, by omega, hTa,
      env.hx, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eFG]; exact fun i hi j hj => sGN i (by omega) j hj
    · rw [eFG]; exact fun i hi j hj => sGR i (by omega) j hj
    · rw [eTG]; exact sGN.sub (c := 0xAC) (l := 40) (by decide)
    · rw [eFG, eTG]
      have := sep_offsets G (c := 0xAC) (n := 40) (d := 0) (k := 0xA0) (.inr (by omega)) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    · rw [eFG]; exact fun i hi j hj => sXG i hi j (by omega)
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := feNeg_correct n1 env1 pc1 (by rw [r1 sp (by decide), spA])
    (by rw [r1 a0 (by decide), A10]) (by rw [r1 a1 (by decide), A11])
    (by rw [regs1]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x10 + 8) (by decide)))
  rw [eFG] at f2
  have fr2 : ∀ y, Sep G 0xE0 y 1 → n2.mem y = m.mem y := fun y hy => by
    rw [f2 y (fun i hi j hj => hy i (by omega) j hj) (by rw [eTG]; exact hy.sub (c := 0xAC) (l := 40) (by decide)),
      mem1, frA y hy]
  have slot2 : ∀ k, 0x34 ≤ k → k < 0x40 → n2.mem (F + BitVec.ofNat 32 k) = mA.mem (F + BitVec.ofNat 32 k) :=
    fun k h1 h2 => by
      have e : F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0xA0 + k) := by rw [← hF]; exact add_ofNat_assoc G 0xA0 k
      have s1 : Sep G 0xA0 (G + BitVec.ofNat 32 (0xA0 + k)) 1 := by
        have := sep_offsets G (c := 0) (n := 0xA0) (d := 0xA0 + k) (k := 1) (.inl (by omega)) (by omega) (by omega)
        rwa [add_ofNat_zero] at this
      have s2 : Sep T 40 (G + BitVec.ofNat 32 (0xA0 + k)) 1 := by
        rw [eTG]
        exact sep_offsets G (c := 0xAC) (n := 40) (d := 0xA0 + k) (k := 1) (.inl (by omega)) (by omega) (by omega)
      rw [e, f2 _ s1 s2, mem1]
  have hc2 : CodeIn n2.mem P feCondNegCode := fun i hi => by
    rw [fr2 _ (sGC.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have u2 : St n2.mem P n2 0x18 (reg n2) := ⟨pc2, rfl, fun _ => rfl⟩
  have k2' : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ ra →
      reg n2 q = reg mA q := fun q hq hr => by rw [k2 q hq, r1 q hr]
  -- `conditional_assign(self, &neg, choice)`
  obtain ⟨mB, cB, uB⟩ := St.block fcnB u2 hc2 fcnB_end (by simp +decide only [BlockOk, BInstr.ok, fcnB, and_true])
  simp only [runBlock, BInstr.run, fcnB] at uB
  have hzB : reg n2 0 = 0 := u2.zero
  have B10 : reg mB a0 = x := by
    rw [uB.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [k2' _ (by decide) (by decide), A9]
    exact BitVec.zero_add x
  have B11 : reg mB a1 = T := by
    rw [uB.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2, ev_add, hT]
  have B12 : reg mB a2 = c := by
    rw [uB.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [k2' _ (by decide) (by decide), A8]
    exact BitVec.zero_add c
  have kB : ∀ q : Fin 32, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg mB q = reg n2 q := fun q h0 h1 h2 h3 => by
    rw [uB.regs]; simp only [upd_ne h0 h1, upd_ne h0 h2, upd_ne h0 h3]
  obtain ⟨n3, c3, pc3, mem3, regs3⟩ := uB.self.callRa hc2 fcn_at_1e fcn_at_22 (cb := P + 0x30)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x30 (by decide))
  have r3 : ∀ q, q ≠ ra → reg n3 q = reg mB q := fun q h => by rw [regs3]; exact updz uB.self.zero h
  obtain ⟨n4, c4, pc4, k4, l4, f4⟩ := feCondAssign_correct n3 (s := x) (o := T) (c := c)
    (fun i hi => by rw [mem3, fr2 _ (sGA.subR (c := i) (l := 1) (by omega))]; exact env.fca i hi) pc3
    (by rw [r3 a0 (by decide), B10]) (by rw [r3 a1 (by decide), B11]) (by rw [r3 a2 (by decide), B12]) hc01
    (by rw [regs3]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x1E + 8) (by decide)))
    env.hx hTa env.hxw env.sXA (by rw [eTG]; exact sXG.subR (c := 0xAC) (l := 40) (by decide))
  rw [mem3] at l4 f4
  have hc4 : CodeIn n4.mem P feCondNegCode := fun i hi => by
    rw [f4 _ (env.sXC.subR (c := i) (l := 1) (by omega))]; exact hc2 i hi
  have u4 : St n4.mem P n4 0x26 (reg n4) := ⟨pc4, rfl, fun _ => rfl⟩
  have sp4 : reg n4 sp = F := by rw [k4 sp (by decide), r3 sp (by decide), kB sp (by decide) (by decide) (by decide) (by decide), sp2]
  have ldS : ∀ o, 0x34 ≤ o → o + 4 ≤ 0x40 → memLoad32 n4.mem (F + BitVec.ofNat 32 o) = memLoad32 mA.mem (F + BitVec.ofNat 32 o) :=
    fun o h1 h2 => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, f4 _ (by
          have e : F + BitVec.ofNat 32 (o + j) = G + BitVec.ofNat 32 (0xA0 + (o + j)) := by
            rw [← hF]; exact add_ofNat_assoc G 0xA0 (o + j)
          rw [e]; exact sXG.subR (c := 0xA0 + (o + j)) (l := 1) (by omega)), slot2 _ (by omega) (by omega)]
  have LRA : memLoad32 n4.mem (F + 0x3C) = reg m ra := by
    have h := ldS 0x3C (by decide) (by decide); rw [show (F + BitVec.ofNat 32 0x3C : Word) = F + 0x3C from rfl] at h
    rw [h, MA, memLoad32_store32_sep (a := F + 0x34) (b := F + 0x3C) (sep_offsets F (.inl (by decide)) (by decide) (by decide)),
      memLoad32_store32_sep (a := F + 0x38) (b := F + 0x3C) (sep_offsets F (.inl (by decide)) (by decide) (by decide)),
      memLoad32_store32_same]
  have L8 : memLoad32 n4.mem (F + 0x38) = reg m (8 : Fin 32) := by
    have h := ldS 0x38 (by decide) (by decide); rw [show (F + BitVec.ofNat 32 0x38 : Word) = F + 0x38 from rfl] at h
    rw [h, MA, memLoad32_store32_sep (a := F + 0x34) (b := F + 0x38) (sep_offsets F (.inl (by decide)) (by decide) (by decide)),
      memLoad32_store32_same]
  have L9 : memLoad32 n4.mem (F + 0x34) = reg m (9 : Fin 32) := by
    have h := ldS 0x34 (by decide) (by decide); rw [show (F + BitVec.ofNat 32 0x34 : Word) = F + 0x34 from rfl] at h
    rw [h, MA, memLoad32_store32_same]
  -- the epilogue
  obtain ⟨n5, c5, u5⟩ := St.block fcnC u4 hc4 fcnC_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, fcnC, upd_app, ↓reduceIte, and_true]
    rw [sp4]
    exact ⟨aligned_add hFa (by decide), aligned_add hFa (by decide), aligned_add hFa (by decide)⟩)
  simp only [runBlock, BInstr.run, fcnC] at u5
  obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.self.jalr hc4 fcn_at_2e
  have kM : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg m q :=
    fun q hq => by
      obtain ⟨h0, h1, h2, h3, h4⟩ : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ ra := by revert hq; revert q; decide
      have g1 : q.val ∈ [1, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
      have g2 : q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
      have g3 : q.val ∈ [1, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
      rw [k4 q g1, r3 q h4, kB q h0 h1 h2 h3, k2' q g2 h4, kA q g3]
  refine ⟨n6, cA.trans <| c1.trans (c2.trans (cB.trans (c3.trans (c4.trans (c5.trans (.single d6)))))), ?_, ?_, fun q hq => ?_,
    fun i hi => ?_, fun y hg hx => ?_⟩
  · rw [pc6, u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp4, LRA, hra, add_lit_zero, hret]
  · rw [regs6, u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp4, ev_add, eFs]
  · rw [regs6, u5.regs]
    have key : q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨
        (q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ ra ∧ q ≠ (8 : Fin 32) ∧
          q ≠ (9 : Fin 32) ∧ q ≠ sp) := by revert hq; revert q; decide
    rcases key with rfl | rfl | rfl | ⟨h1, h0, h2, h3, h4, h5⟩
    · simp +decide only [upd_app, ↓reduceIte]; rw [sp4, LRA]
    · simp +decide only [upd_app, ↓reduceIte]; rw [sp4, L8]
    · simp +decide only [upd_app, ↓reduceIte]; rw [sp4, L9]
    · simp only [upd_ne h0 h5, upd_ne h0 h4, upd_ne h0 h3, upd_ne h0 h2]; exact kM q h1
  · rw [mem6, l4 i hi]
    have lx : ∀ j, j < 10 → limbs n2.mem x j = limbs m.mem x j := fun j hj => memLoad32_congr fun k hk => by
      rw [add_ofNat_assoc]; exact fr2 _ (sXG.symm.subR (c := 4 * j + k) (l := 1) (by omega))
    have l1 : ∀ j, j < 10 → limbs n1.mem x j = limbs m.mem x j := fun j hj => memLoad32_congr fun k hk => by
      rw [add_ofNat_assoc, mem1]; exact frA _ (sXG.symm.subR (c := 4 * j + k) (l := 1) (by omega))
    have z : ∀ j, j < 10 → feNegZ (limbs n1.mem x) j = feNegZ (limbs m.mem x) j := fun j hj => by
      unfold feNegZ; rw [l1 j hj]
    unfold feCondNegW
    by_cases h1 : c = 1
    · rw [ite_eq_left h1, ite_eq_left h1, limbs_of_wordsAt w2 i hi, z 0 (by decide), z 1 (by decide), z 2 (by decide),
        z 3 (by decide), z 4 (by decide), z 5 (by decide), z 6 (by decide), z 7 (by decide), z 8 (by decide),
        z 9 (by decide)]
    · rw [ite_eq_right h1, ite_eq_right h1, lx i hi]
  · rw [mem6, f4 y hx, fr2 y hg]

end C3.RV32
