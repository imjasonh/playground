import C3BootProofs.Proofs.CtEq
import C3BootProofs.Proofs.Leaves
import C3BootProofs.Proofs.MemsetAny

/-!
# `ScalarValue<NistP384>::is_zero`, as compiled

`<elliptic_curve::scalar::value::ScalarValue<p384::NistP384>>::is_zero`
zeroes a 12-limb array on its stack with `memset`, compares the scalar with
it through the proved constant-time limb `ct_eq`, ANDs in the proved
`UintRef::is_zero` of two empty slices, and passes the result through the
proved `black_box`. It returns 1 when every limb is zero and 0 otherwise.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem siz_at_0 : fetchRel scalarIsZero384Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem siz_at_2 : fetchRel scalarIsZero384Code 0x2 = some (.store .sw sp ra 0x3C, 2) := by decide
theorem siz_at_4 : fetchRel scalarIsZero384Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x38, 2) := by decide
theorem siz_at_6 : fetchRel scalarIsZero384Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x34, 2) := by decide
theorem siz_at_8 : fetchRel scalarIsZero384Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x30, 2) := by decide
theorem siz_at_a : fetchRel scalarIsZero384Code 0xA = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem siz_at_c : fetchRel scalarIsZero384Code 0xC = some (.alu .add a0 x0 sp, 2) := by decide
theorem siz_at_e : fetchRel scalarIsZero384Code 0xE = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem siz_at_12 : fetchRel scalarIsZero384Code 0x12 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem siz_at_14 : fetchRel scalarIsZero384Code 0x14 = some (.auipc ra 0x14000, 4) := by decide
theorem siz_at_18 : fetchRel scalarIsZero384Code 0x18 = some (.jalr ra ra 0xFFFFF9FE, 4) := by decide
theorem siz_at_1c : fetchRel scalarIsZero384Code 0x1C = some (.aluImm .add (9 : Fin 32) (8 : Fin 32) 0x30, 4) := by decide
theorem siz_at_20 : fetchRel scalarIsZero384Code 0x20 = some (.aluImm .add (18 : Fin 32) sp 0x30, 4) := by decide
theorem siz_at_24 : fetchRel scalarIsZero384Code 0x24 = some (.aluImm .add a1 x0 0xC, 2) := by decide
theorem siz_at_26 : fetchRel scalarIsZero384Code 0x26 = some (.alu .add a2 x0 sp, 2) := by decide
theorem siz_at_28 : fetchRel scalarIsZero384Code 0x28 = some (.aluImm .add a3 x0 0xC, 2) := by decide
theorem siz_at_2a : fetchRel scalarIsZero384Code 0x2A = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem siz_at_2c : fetchRel scalarIsZero384Code 0x2C = some (.auipc ra 0xD000, 4) := by decide
theorem siz_at_30 : fetchRel scalarIsZero384Code 0x30 = some (.jalr ra ra 0xFFFFF84A, 4) := by decide
theorem siz_at_34 : fetchRel scalarIsZero384Code 0x34 = some (.aluImm .and (8 : Fin 32) a0 0xFF, 4) := by decide
theorem siz_at_38 : fetchRel scalarIsZero384Code 0x38 = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem siz_at_3a : fetchRel scalarIsZero384Code 0x3A = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem siz_at_3c : fetchRel scalarIsZero384Code 0x3C = some (.auipc ra 0x0, 4) := by decide
theorem siz_at_40 : fetchRel scalarIsZero384Code 0x40 = some (.jalr ra ra 0x32, 4) := by decide
theorem siz_at_44 : fetchRel scalarIsZero384Code 0x44 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem siz_at_48 : fetchRel scalarIsZero384Code 0x48 = some (.alu .and (8 : Fin 32) (8 : Fin 32) a0, 2) := by decide
theorem siz_at_4a : fetchRel scalarIsZero384Code 0x4A = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem siz_at_4c : fetchRel scalarIsZero384Code 0x4C = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem siz_at_4e : fetchRel scalarIsZero384Code 0x4E = some (.auipc ra 0x0, 4) := by decide
theorem siz_at_52 : fetchRel scalarIsZero384Code 0x52 = some (.jalr ra ra 0x20, 4) := by decide
theorem siz_at_56 : fetchRel scalarIsZero384Code 0x56 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem siz_at_5a : fetchRel scalarIsZero384Code 0x5A = some (.alu .and a0 a0 (8 : Fin 32), 2) := by decide
theorem siz_at_5c : fetchRel scalarIsZero384Code 0x5C = some (.load .lw ra sp 0x3C, 2) := by decide
theorem siz_at_5e : fetchRel scalarIsZero384Code 0x5E = some (.load .lw (8 : Fin 32) sp 0x38, 2) := by decide
theorem siz_at_60 : fetchRel scalarIsZero384Code 0x60 = some (.load .lw (9 : Fin 32) sp 0x34, 2) := by decide
theorem siz_at_62 : fetchRel scalarIsZero384Code 0x62 = some (.load .lw (18 : Fin 32) sp 0x30, 2) := by decide
theorem siz_at_64 : fetchRel scalarIsZero384Code 0x64 = some (.aluImm .add sp sp 0x40, 2) := by decide
theorem siz_at_66 : fetchRel scalarIsZero384Code 0x66 = some (.auipc (6 : Fin 32) 0xD000, 4) := by decide
theorem siz_at_6a : fetchRel scalarIsZero384Code 0x6A = some (.jalr x0 (6 : Fin 32) 0xFFFFF90A, 4) := by decide
end

/-- Where `ScalarValue<NistP384>::is_zero` runs: its code and its callees',
the 0x54 bytes of stack below `sp0`, and the scalar's 48 bytes at `x`. -/
structure SZEnv (M : Word → BitVec 8) (P sp0 x : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P scalarIsZero384Code
  mset : CodeIn M (P + 0x11C02) memsetCode
  cteq : CodeIn M (P + 0xAA66) limbCtEqCode
  isz : CodeIn M (P + 0x6E) uintRefIsZeroCode
  isnz : CodeIn M (P + 0x6E + 0x1A) uintRefIsNonzeroCode
  bb : CodeIn M (P + 0xAB60) blackBoxU8Code
  hsp : sp0.toNat % 4 = 0
  hS : 0x54 ≤ sp0.toNat
  hx : x.toNat % 4 = 0
  hxw : x.toNat + 48 < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFFAC) 0x54 P scalarIsZero384Code.length
  sGM : Sep (sp0 + 0xFFFFFFAC) 0x54 (P + 0x11C02) memsetCode.length
  sGQ : Sep (sp0 + 0xFFFFFFAC) 0x54 (P + 0xAA66) limbCtEqCode.length
  sGZ : Sep (sp0 + 0xFFFFFFAC) 0x54 (P + 0x6E) uintRefIsZeroCode.length
  sGN : Sep (sp0 + 0xFFFFFFAC) 0x54 (P + 0x6E + 0x1A) uintRefIsNonzeroCode.length
  sGB : Sep (sp0 + 0xFFFFFFAC) 0x54 (P + 0xAB60) blackBoxU8Code.length
  sXG : Sep x 48 (sp0 + 0xFFFFFFAC) 0x54

abbrev szPs : List (Fin 32 × Word) := [(ra, 0x3C), ((8 : Fin 32), 0x38), ((9 : Fin 32), 0x34), ((18 : Fin 32), 0x30)]

section
set_option maxRecDepth 20000
theorem szSave_end : blockEnd scalarIsZero384Code 2 (saveBlock szPs) = some 0xA := by decide
theorem szRestore_end : blockEnd scalarIsZero384Code 0x5C (restoreBlock szPs) = some 0x64 := by decide
end


theorem sz_and01 (c : Prop) [Decidable c] : (if c then (1 : Word) else 0) &&& 0xFF = if c then 1 else 0 := by
  by_cases h : c
  · rw [ite_eq_left h]; rfl
  · rw [ite_eq_right h]; rfl

theorem sz_zext01 (c : Prop) [Decidable c] :
    ((if c then (1 : Word) else 0).extractLsb' 0 8).zeroExtend 32 = if c then 1 else 0 := by
  by_cases h : c
  · rw [ite_eq_left h]; rfl
  · rw [ite_eq_right h]; rfl

theorem sz_and1 (c : Prop) [Decidable c] :
    aluEval .and (if c then (1 : Word) else 0) (aluEval .and 1 0xFF) = if c then 1 else 0 := by
  by_cases h : c
  · rw [ite_eq_left h]; rfl
  · rw [ite_eq_right h]; rfl

theorem sz_and1' (c : Prop) [Decidable c] :
    aluEval .and (aluEval .and 1 0xFF) (if c then (1 : Word) else 0) = if c then 1 else 0 := by
  by_cases h : c
  · rw [ite_eq_left h]; rfl
  · rw [ite_eq_right h]; rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `ScalarValue<NistP384>::is_zero`**: 1 in `a0` when the 12
limbs at `x` are all zero, and 0 otherwise. -/
theorem scalarIsZero384_correct (m : Machine) {P sp0 x retAddr : Word} (env : SZEnv m.mem P sp0 x)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = x)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      reg m' a0 = (if ∀ i : Nat, i < 12 → memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) = 0 then 1 else 0) ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      ∀ y, Sep (sp0 + 0xFFFFFFAC) 0x54 y 1 → m'.mem y = m.mem y := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFFAC = G := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFC0 = F := ⟨_, rfl⟩
  have sGC := env.sGC; have sGM := env.sGM; have sGQ := env.sGQ; have sGZ := env.sGZ; have sGN := env.sGN
  have sGB := env.sGB; have sXG := env.sXG
  rw [hG] at sGC sGM sGQ sGZ sGN sGB sXG ⊢
  have hGF : G + 0x14 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFFAC) (by decide)
  have hFa : F.toNat % 4 = 0 := by rw [← hGF]; exact aligned_add hGa (k := 0x14) (by decide)
  have hGw : G.toNat + 0x54 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFFAC : Word).toNat = 4294967212 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have hFn : F.toNat = G.toNat + 0x14 := by
    rw [← hGF, BitVec.toNat_add, show (0x14 : Word).toNat = 0x14 from rfl]; omega
  have eS : F + 0x40 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x14 + k) := fun k => by
    rw [← hGF, show (0x14 : Word) = BitVec.ofNat 32 0x14 from rfl, add_ofNat_assoc]
  have inF : ∀ {b : Word} {l : Nat}, Sep G 0x54 b l → Sep F 0x40 b l := fun h => by
    rw [← hGF]; exact h.sub (c := 0x14) (l := 0x40) (by decide)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0x54 b code'.length → (∀ y, Sep G 0x54 y 1 → M' y = m.mem y) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod siz_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFC0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock szPs) u1 env.cod szSave_end (saveBlock_ok _ szPs _ fun p hp => by
    rw [sp1]
    simp only [szPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> exact ⟨aligned_add hFa (by decide), (inF sGC).sub (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFC0)) szPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ y, Sep F 0x40 y 1 → Msv y = m.mem y := fun y hy => by
    rw [← hMsv]
    exact saveMem_outside szPs fun p hp => by
      simp only [szPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> exact hy.sub (by decide)
  have frSvG : ∀ y, Sep G 0x54 y 1 → Msv y = m.mem y := fun y hy => frSv y (inF hy)
  have hslv : ∀ r o, (r, o) ∈ szPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [szPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  have hcS : CodeIn Msv P scalarIsZero384Code := cIn env.cod sGC frSvG
  obtain ⟨m3, c3, u3⟩ := St.block [.alu .add (8 : Fin 32) x0 a0, .alu .add a0 x0 sp, .aluImm .add a2 x0 0x30,
    .aluImm .add a1 x0 0] u2.self hcS (off' := 0x14) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u3
  have sFM : Sep F (4 * 12) (P + 0x11C02) memsetCode.length := (inF sGM).sub (c := 0) (l := 48) (by decide) |>
    fun h => by rwa [add_ofNat_zero] at h
  obtain ⟨m4, c4, u4, _, k4⟩ := u3.self.memsetW (B := P + 0x11C02) (w := 12) (dst := F)
    (even_at P env.hP 0x11C02 (by decide)) hcS (cIn env.mset sGM frSvG) siz_at_14 siz_at_18
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x14 + 8) (by decide)) (by decide)
    (by omega) (by decide) hFa sFM
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; exact zw F)
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte])
  obtain ⟨Mz, hMz⟩ : ∃ Mz, fillWords Msv F 0 12 = Mz := ⟨_, rfl⟩
  rw [hMz] at u4
  have frZ : ∀ y, Sep G 0x54 y 1 → Mz y = m.mem y := fun y hy => by
    rw [← hMz, fillWords_outside 12 ((inF hy).sub (c := 0) (l := 48) (by decide) |> fun h => by
      rwa [add_ofNat_zero] at h)]; exact frSvG y hy
  have hc4 : CodeIn Mz P scalarIsZero384Code := cIn env.cod sGC frZ
  have g3 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → reg m4 q = _ := k4
  have v48 : reg m4 8 = x := by
    rw [k4 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u3.regs]
    simp +decide only [upd_app, ↓reduceIte]; rw [u2.self.zero, r2 a0 (by decide), ha0]; exact zw x
  have v4sp : reg m4 sp = F := by
    rw [k4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u3.regs]
    simp +decide only [upd_app, ↓reduceIte]; exact sp2
  have K4 : ∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m4 q = reg m q := fun q hq => by
    obtain ⟨h2, h3, h4, h5, h6, hr, h0, h1, h8, hs, hv⟩ : q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ ra ∧ q ≠ a0 ∧
      q ≠ a1 ∧ q ≠ (8 : Fin 32) ∧ q ≠ sp ∧ q.val ≠ 0 := by revert hq; revert q; decide
    rw [k4 q h2 h3 h4 h5 h6 hr, u3.regs, upd_ne hv h1, upd_ne hv h2, upd_ne hv h0, upd_ne hv h8, r2 q hs]
  -- the comparison with the zeroed array
  obtain ⟨m5, c5, u5⟩ := St.block [.aluImm .add (9 : Fin 32) (8 : Fin 32) 0x30, .aluImm .add (18 : Fin 32) sp 0x30,
    .aluImm .add a1 x0 0xC, .alu .add a2 x0 sp, .aluImm .add a3 x0 0xC, .alu .add a0 x0 (8 : Fin 32)] u4 hc4
    (off' := 0x2C) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u5
  have r5 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) →
      reg m5 q = reg m4 q := fun q hv h0 h1 h2 h3 h9 h18 => by
    rw [u5.regs, upd_ne hv h0, upd_ne hv h3, upd_ne hv h2, upd_ne hv h1, upd_ne hv h18, upd_ne hv h9]
  obtain ⟨m6, c6, pc6, mem6, regs6⟩ := u5.self.callRa hc4 siz_at_2c siz_at_30 (cb := P + 0xAA66)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xAA66 (by decide))
  have r6 := PEnv.reg1 regs6 u5.self.zero
  obtain ⟨m7, c7, pc7, a07, k7, mem7⟩ := limbCtEq_correct m6 (base := P + 0xAA66) (p := x) (q := F) (n := 12) (n' := 12)
    (even_at P env.hP 0xAA66 (by decide)) (by rw [mem6]; exact cIn env.cteq sGQ frZ) pc6
    (by rw [r6 a0 (by decide), u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v48]; exact zw x)
    (by rw [r6 a1 (by decide), u5.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [r6 a2 (by decide), u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v4sp]; exact zw F)
    (by rw [r6 a3 (by decide), u5.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by decide) (by decide) env.hx hFa (by rw [regs6]; simp +decide [upd])
    (even_clear _ (even_at P env.hP (0x2C + 8) (by decide)))
  rw [mem6] at a07 mem7
  have hzeq : ∀ i, i < 12 → memLoad32 Mz (x + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) :=
    fun i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact frZ _ (sXG.sub (c := 4 * i + j) (l := 1) (by omega)).symm
  have hzF : ∀ i, i < 12 → memLoad32 Mz (F + BitVec.ofNat 32 (4 * i)) = 0 := fun i hi => by
    rw [← hMz]; exact fillWords_load 12 i hi (by omega)
  have v7 : reg m7 a0 = if (∀ i : Nat, i < 12 → memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) = 0) then 1 else 0 := by
    rw [a07]
    by_cases hZ : ∀ i : Nat, i < 12 → memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) = 0
    · rw [ite_eq_left hZ, ite_eq_left ⟨rfl, fun i hi => by rw [hzeq i hi, hzF i hi]; exact hZ i hi⟩]
    · rw [ite_eq_right hZ, ite_eq_right (fun h => hZ fun i hi => by rw [← hzeq i hi, h.2 i hi, hzF i hi])]
  have eFG : F + 0xFFFFFFEC = G := by rw [← hGF, BitVec.add_assoc]; exact BitVec.add_zero G
  have inZ : ∀ {b : Word} {l : Nat}, Sep G 0x54 b l → Sep G 0x14 b l := fun h =>
    (h.sub (c := 0) (l := 0x14) (by decide)) |> fun h' => by rwa [add_ofNat_zero] at h'
  -- a call to `UintRef::is_zero` on an empty slice, which returns 1
  have isz : ∀ {Mx : Word → BitVec 8} {n : Machine} {o : Nat} {oo ptr : Word}, St Mx P n o (reg n) →
      CodeIn Mx P scalarIsZero384Code → (∀ y, Sep G 0x54 y 1 → Mx y = m.mem y) →
      fetchRel scalarIsZero384Code o = some (.auipc ra 0, 4) → fetchRel scalarIsZero384Code (o + 4) = some (.jalr ra ra oo, 4) →
      P + BitVec.ofNat 32 o + 0 + oo = P + 0x6E → (o + 8) % 2 = 0 → reg n sp = F → reg n a0 = ptr → reg n a1 = 0 →
      ptr.toNat % 4 = 0 →
      ∃ n', Steps n n' ∧ St n'.mem P n' (o + 8) (reg n') ∧ reg n' a0 = 1 ∧
        (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ ra → reg n' q = reg n q) ∧
        ∀ y, Sep G 0x14 y 1 → n'.mem y = Mx y := by
    intro Mx n o oo ptr st hc hM h1 h2 hb ho rsp r0 r1 hptr
    obtain ⟨n1, c1, pc1, mem1, regs1⟩ := st.callRa hc h1 h2 (cb := P + 0x6E) hb (even_at P env.hP 0x6E (by decide))
    have rr := PEnv.reg1 regs1 st.zero
    obtain ⟨n2, c2, pc2, sp2', a02, k2, f2⟩ := uintRefIsZero_correct n1 (P := P + 0x6E) (ptr := ptr) (sp0 := F) (len := 0)
      (even_at P env.hP 0x6E (by decide)) (by rw [mem1]; exact cIn env.isz sGZ hM) (by rw [mem1]; exact cIn env.isnz sGN hM)
      pc1 (by rw [rr sp (by decide), rsp]) hFa (by rw [rr a0 (by decide), r0]) (by rw [rr a1 (by decide), r1]; rfl)
      (by decide) hptr (by rw [eFG]; exact inZ sGZ) (by rw [eFG]; exact inZ sGN) (fun i hi => absurd hi (by omega))
      (by rw [regs1]; simp +decide [upd]) (even_clear _ (even_at P env.hP (o + 8) ho))
    refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, ?_, fun q h0 h1 h2 h3 hr => ?_, fun y hy => ?_⟩
    · rw [a02]; exact ite_eq_left (fun i hi => absurd hi (Nat.not_lt_zero i))
    · rw [k2 q h0 h1 h2 h3, rr q hr]
    · rw [f2 y (by rw [eFG]; exact hy), mem1]
  have u7 : St Mz P m7 (0x2C + 8) (reg m7) := ⟨by rw [pc7], mem7, fun _ => rfl⟩
  obtain ⟨m8, d8, u8⟩ := u7.aluImm hc4 siz_at_34 (off' := 0x38) (by decide)
  obtain ⟨m9, c9, u9⟩ := St.block [.alu .add a0 x0 (9 : Fin 32), .aluImm .add a1 x0 0] u8.self hc4 (off' := 0x3C)
    (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u9
  have k8 : ∀ q, q.val ≠ 0 → q ≠ (8 : Fin 32) → reg m8 q = reg m7 q := fun q hv h => by rw [u8.regs, upd_ne hv h]
  have k9 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → reg m9 q = reg m8 q := fun q hv h0 h1 => by
    rw [u9.regs, upd_ne hv h1, upd_ne hv h0]
  -- registers the comparison leaves alone
  have k76 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ ra → q ≠ (9 : Fin 32) →
      q ≠ (18 : Fin 32) → reg m7 q = reg m4 q := fun q hv h0 h1 h2 h3 h4 h5 hr h9 h18 => by
    rw [k7 q h0 h1 h2 h3 h4 h5, r6 q hr, r5 q hv h0 h1 h2 h3 h9 h18]
  have v79 : reg m7 9 = x + 0x30 := by
    rw [k7 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r6 9 (by decide), u5.regs]
    simp +decide only [upd_app, ↓reduceIte]; rw [v48]; rfl
  have v718 : reg m7 18 = F + 0x30 := by
    rw [k7 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r6 18 (by decide), u5.regs]
    simp +decide only [upd_app, ↓reduceIte]; rw [v4sp]; rfl
  have v7sp : reg m7 sp = F := by
    rw [k76 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), v4sp]
  have v88 : reg m8 8 = if (∀ i : Nat, i < 12 → memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) = 0) then 1 else 0 := by
    rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v7]; exact sz_and01 _
  obtain ⟨m10, c10, u10, a010, k10, f10⟩ := isz u9.self hc4 frZ siz_at_3c siz_at_40 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    (by decide) (by rw [k9 sp (by decide) (by decide) (by decide), k8 sp (by decide) (by decide), v7sp])
    (by rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [k8 9 (by decide) (by decide), v79]; exact zw _)
    (by rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]) (aligned_add env.hx (k := 0x30) (by decide))
  have hc10 : CodeIn m10.mem P scalarIsZero384Code := fun k hk => by
    rw [f10 _ ((inZ sGC).subR (c := k) (l := 1) (by omega))]; exact hc4 k hk
  obtain ⟨m11, d11, u11⟩ := u10.aluImm hc10 siz_at_44 (off' := 0x48) (by decide)
  obtain ⟨m12, d12, u12⟩ := u11.self.alu hc10 siz_at_48 (off' := 0x4A) (by decide)
  have v128 : reg m12 8 = if (∀ i : Nat, i < 12 → memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) = 0) then 1 else 0 := by
    rw [u12.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [u11.regs, upd_ne (by decide) (by decide), k10 8 (by decide) (by decide) (by decide) (by decide) (by decide),
      k9 8 (by decide) (by decide) (by decide), v88, u11.regs]
    simp +decide only [upd_app, ↓reduceIte]; rw [a010]; exact sz_and1 _
  have k12 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ (8 : Fin 32) → reg m12 q = reg m10 q := fun q hv h0 h8 => by
    rw [u12.regs, upd_ne hv h8, u11.regs, upd_ne hv h0]
  obtain ⟨m13, c13, u13⟩ := St.block [.alu .add a0 x0 (18 : Fin 32), .aluImm .add a1 x0 0] u12.self hc10 (off' := 0x4E)
    (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u13
  have k13 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → reg m13 q = reg m12 q := fun q hv h0 h1 => by
    rw [u13.regs, upd_ne hv h1, upd_ne hv h0]
  -- registers kept from m7 through the first `is_zero`
  have k7_12 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ ra → q ≠ (8 : Fin 32) → reg m12 q = reg m7 q :=
    fun q hv h0 h1 h2 h3 hr h8 => by rw [k12 q hv h0 h8, k10 q h0 h1 h2 h3 hr, k9 q hv h0 h1, k8 q hv h8]
  obtain ⟨m14, c14, u14, a014, k14, f14⟩ := isz u13.self hc10 (fun y hy => by rw [f10 y (inZ hy)]; exact frZ y hy)
    siz_at_4e siz_at_52 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (by decide)
    (by rw [k13 sp (by decide) (by decide) (by decide), k7_12 sp (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), v7sp])
    (by rw [u13.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [k7_12 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), v718]; exact zw _)
    (by rw [u13.regs]; simp +decide only [upd_app, ↓reduceIte]) (aligned_add hFa (k := 0x30) (by decide))
  have f14' : ∀ y, Sep G 0x14 y 1 → m14.mem y = Mz y := fun y hy => by rw [f14 y hy, f10 y hy]
  have hc14 : CodeIn m14.mem P scalarIsZero384Code := fun k hk => by
    rw [f14' _ ((inZ sGC).subR (c := k) (l := 1) (by omega))]; exact hc4 k hk
  obtain ⟨m15, d15, u15⟩ := u14.aluImm hc14 siz_at_56 (off' := 0x5A) (by decide)
  obtain ⟨m16, d16, u16⟩ := u15.self.alu hc14 siz_at_5a (off' := 0x5C) (by decide)
  have v16 : reg m16 a0 = if (∀ i : Nat, i < 12 → memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) = 0) then 1 else 0 := by
    have e15a : reg m15 a0 = aluEval .and (reg m14 a0) 0xFF := by
      rw [u15.regs]; simp +decide only [upd_app, ↓reduceIte]
    have e158 : reg m15 8 = reg m14 8 := by rw [u15.regs, upd_ne (by decide) (by decide)]
    rw [u16.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [e15a, e158, a014, k14 8 (by decide) (by decide) (by decide) (by decide) (by decide),
      k13 8 (by decide) (by decide) (by decide), v128]; exact sz_and1' _
  have k16 : ∀ q, q.val ≠ 0 → q ≠ a0 → reg m16 q = reg m14 q := fun q hv h0 => by
    rw [u16.regs, upd_ne hv h0, u15.regs, upd_ne hv h0]
  have K16 : ∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m16 q = reg m q := fun q hq => by
    obtain ⟨hv, h0, h1, h2, h3, h4, h5, hr, h8, h9, h18⟩ : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧
      q ≠ a5 ∧ q ≠ ra ∧ q ≠ (8 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧ q ≠ (18 : Fin 32) := by revert hq; revert q; decide
    rw [k16 q hv h0, k14 q h0 h1 h2 h3 hr, k13 q hv h0 h1, k7_12 q hv h0 h1 h2 h3 hr h8,
      k76 q hv h0 h1 h2 h3 h4 h5 hr h9 h18]
    exact K4 q (by revert hq; revert q; decide)
  have sp16 : reg m16 sp = F := by
    rw [k16 sp (by decide) (by decide), k14 sp (by decide) (by decide) (by decide) (by decide) (by decide),
      k13 sp (by decide) (by decide) (by decide), k7_12 sp (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), v7sp]
  have hFw : F.toNat + 0x40 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have eFt : ∀ k, k < 0x40 → (F + BitVec.ofNat 32 k).toNat = F.toNat + k := fun k hk => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]
  have hMF : ∀ k, 0x30 ≤ k → k < 0x40 → m14.mem (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) := fun k h1 h2 => by
    rw [f14' _ (sep_of_le (by rw [eFt k h2]; omega) (by have := (F + BitVec.ofNat 32 k).isLt; omega)), ← hMz,
      fillWords_outside 12 (sep_of_le (by rw [eFt k h2]; omega) (by have := (F + BitVec.ofNat 32 k).isLt; omega))]
  have slotW : ∀ r o, (r, o) ∈ szPs → memLoad32 m14.mem (F + o) = reg m r := fun r o h => by
    have ho : 0x30 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x40 := by
      simp only [szPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hslv r o h]
    apply memLoad32_congr; intro j hj
    rw [← ofNat_toNat_self o, add_ofNat_assoc, hMF _ (by omega) (by omega)]
  have hpsp : ∀ p ∈ szPs, p.1 ≠ sp := by decide
  obtain ⟨n1, c1, u1⟩ := St.block (restoreBlock szPs) u16.self hc14 szRestore_end
    (restoreBlock_ok m14.mem F szPs (reg m16) sp16 hpsp fun q hq => by
      simp only [szPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
  simp only [restoreBlock_run m14.mem F szPs (reg m16) sp16 hpsp] at u1
  have rsp1 : restoreRegs m14.mem F (reg m16) szPs sp = F := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact sp16
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs m14.mem F f ps q = f q := by
    intro f ps q h0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
  have hreg : ∀ r o, (r, o) ∈ szPs → restoreRegs m14.mem F (reg m16) szPs r = reg m r := fun r o hm => by
    simp only [szPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact slotW _ _ (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.aluImm hc14 siz_at_64 (off' := 0x66) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.auipc hc14 siz_at_66 (off' := 0x6A) (by decide)
  obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.self.jalr hc14 siz_at_6a
  have k4 : ∀ q, q ≠ sp → q ≠ t1 → reg n4 q = restoreRegs m14.mem F (reg m16) szPs q := fun q hs h6 => by
    rw [regs4, u3.regs, updz u2.self.zero h6, u2.regs, updz u1.zero hs]
  have sp4 : reg n4 sp = sp0 := by
    rw [regs4, u3.regs, updz u2.self.zero (by decide), u2.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [ev_add, rsp1, eS]
  have pc4' : n4.pc = P + 0xAB60 := by
    rw [pc4, u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [show P + BitVec.ofNat 32 0x66 + 0xB000 + 0xFFFFFAFA = P + 0xAB60 by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact even_clear _ (even_at P env.hP 0xAB60 (by decide))
  have m4G : ∀ y, Sep G 0x54 y 1 → n4.mem y = m.mem y := fun y hy => by
    rw [mem4, f14' y (inZ hy)]; exact frZ y hy
  have eT : sp0 + 0xFFFFFFFF = G + BitVec.ofNat 32 0x53 := by rw [← hG, BitVec.add_assoc]; rfl
  obtain ⟨m', c', pc', a0', k', f'⟩ := blackBoxU8_correct n4 (base := P + 0xAB60) (retAddr := retAddr)
    (cIn env.bb sGB m4G) pc4'
    (by rw [k4 ra (by decide) (by decide), hreg ra 0x3C (by decide), hra]) hret
    (by rw [sp4, eT]; exact sGB.sub (c := 0x53) (l := 1) (by decide))
  refine ⟨m', .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (.cons d8 (c9.trans (c10.trans
    (.cons d11 (.cons d12 (c13.trans (c14.trans (.cons d15 (.cons d16 (c1.trans (.cons d2 (.cons d3 (.cons d4 c'))))))))))))))))))), pc', ?_, ?_,
    fun q hq => ?_, fun y hy => ?_⟩
  · rw [k' sp (by decide), sp4]
  · rw [a0', k4 a0 (by decide) (by decide), rr _ _ a0 (by decide) (by decide), v16]; exact sz_zext01 _
  · have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨
        (q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧ q ≠ t1 ∧ q ≠ a0 ∧
          (∀ p ∈ szPs, p.1 ≠ q)) := by decide
    rcases key q hq with rfl | rfl | rfl | rfl | ⟨h1, h0, hs, h6, ha, hps⟩
    · rw [k' _ (by decide), k4 _ (by decide) (by decide)]; exact hreg _ 0x3C (by decide)
    · rw [k' _ (by decide), k4 _ (by decide) (by decide)]; exact hreg _ 0x38 (by decide)
    · rw [k' _ (by decide), k4 _ (by decide) (by decide)]; exact hreg _ 0x34 (by decide)
    · rw [k' _ (by decide), k4 _ (by decide) (by decide)]; exact hreg _ 0x30 (by decide)
    · rw [k' q ha, k4 q hs h6, rr _ _ q h0 hps]; exact K16 q h1
  · rw [f' y (by rw [sp4, eT]; exact hy.sub (c := 0x53) (l := 1) (by decide)), m4G y hy]

end C3.RV32
