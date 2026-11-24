import C3BootProofs.Proofs.Uint8CtEq
import C3BootProofs.Proofs.CtAssign

/-!
# `NonZeroScalar::new`, as compiled

`NonZeroScalar<NistP384>::new` compares the scalar with the image's zero
constant through the proved `ConstMontyForm::ct_eq`, negates the result with
the proved `Choice::not`, copies the scalar to `out` with the proved `memcpy`,
and stores the choice after it. The P-256 instance zeroes its comparand on
the stack with `memset` and compares through P-256's `Scalar::ct_eq`.
-/


namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem nz4_at_0 : fetchRel nonZero384Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem nz4_at_2 : fetchRel nonZero384Code 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem nz4_at_4 : fetchRel nonZero384Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x8, 2) := by decide
theorem nz4_at_6 : fetchRel nonZero384Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x4, 2) := by decide
theorem nz4_at_8 : fetchRel nonZero384Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x0, 2) := by decide
theorem nz4_at_a : fetchRel nonZero384Code 0xA = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem nz4_at_c : fetchRel nonZero384Code 0xC = some (.alu .add (9 : Fin 32) x0 a0, 2) := by decide
theorem nz4_at_e : fetchRel nonZero384Code 0xE = some (.lui a1 0x3FCC5000, 4) := by decide
theorem nz4_at_12 : fetchRel nonZero384Code 0x12 = some (.aluImm .add a1 a1 0xFFFFFC94, 4) := by decide
theorem nz4_at_16 : fetchRel nonZero384Code 0x16 = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem nz4_at_18 : fetchRel nonZero384Code 0x18 = some (.auipc ra 0x0, 4) := by decide
theorem nz4_at_1c : fetchRel nonZero384Code 0x1C = some (.jalr ra ra 0xFFFFFEDE, 4) := by decide
theorem nz4_at_20 : fetchRel nonZero384Code 0x20 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem nz4_at_24 : fetchRel nonZero384Code 0x24 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem nz4_at_28 : fetchRel nonZero384Code 0x28 = some (.jalr ra ra 0xFFFFFA8E, 4) := by decide
theorem nz4_at_2c : fetchRel nonZero384Code 0x2C = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem nz4_at_2e : fetchRel nonZero384Code 0x2E = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem nz4_at_32 : fetchRel nonZero384Code 0x32 = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem nz4_at_34 : fetchRel nonZero384Code 0x34 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem nz4_at_36 : fetchRel nonZero384Code 0x36 = some (.auipc ra 0x1000, 4) := by decide
theorem nz4_at_3a : fetchRel nonZero384Code 0x3A = some (.jalr ra ra 0xFFFFF974, 4) := by decide
theorem nz4_at_3e : fetchRel nonZero384Code 0x3E = some (.store .sb (9 : Fin 32) (18 : Fin 32) 0x30, 4) := by decide
theorem nz4_at_42 : fetchRel nonZero384Code 0x42 = some (.load .lw ra sp 0xC, 2) := by decide
theorem nz4_at_44 : fetchRel nonZero384Code 0x44 = some (.load .lw (8 : Fin 32) sp 0x8, 2) := by decide
theorem nz4_at_46 : fetchRel nonZero384Code 0x46 = some (.load .lw (9 : Fin 32) sp 0x4, 2) := by decide
theorem nz4_at_48 : fetchRel nonZero384Code 0x48 = some (.load .lw (18 : Fin 32) sp 0x0, 2) := by decide
theorem nz4_at_4a : fetchRel nonZero384Code 0x4A = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem nz4_at_4c : fetchRel nonZero384Code 0x4C = some (.jalr x0 ra 0x0, 2) := by decide
theorem nz2_at_0 : fetchRel nonZero256Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem nz2_at_2 : fetchRel nonZero256Code 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem nz2_at_4 : fetchRel nonZero256Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x28, 2) := by decide
theorem nz2_at_6 : fetchRel nonZero256Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x24, 2) := by decide
theorem nz2_at_8 : fetchRel nonZero256Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x20, 2) := by decide
theorem nz2_at_a : fetchRel nonZero256Code 0xA = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem nz2_at_c : fetchRel nonZero256Code 0xC = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem nz2_at_e : fetchRel nonZero256Code 0xE = some (.alu .add a0 x0 sp, 2) := by decide
theorem nz2_at_10 : fetchRel nonZero256Code 0x10 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem nz2_at_14 : fetchRel nonZero256Code 0x14 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem nz2_at_16 : fetchRel nonZero256Code 0x16 = some (.auipc ra 0x2000, 4) := by decide
theorem nz2_at_1a : fetchRel nonZero256Code 0x1A = some (.jalr ra ra 0x6EA, 4) := by decide
theorem nz2_at_1e : fetchRel nonZero256Code 0x1E = some (.alu .add a1 x0 sp, 2) := by decide
theorem nz2_at_20 : fetchRel nonZero256Code 0x20 = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem nz2_at_22 : fetchRel nonZero256Code 0x22 = some (.auipc ra 0x0, 4) := by decide
theorem nz2_at_26 : fetchRel nonZero256Code 0x26 = some (.jalr ra ra 0xFFFFFCFE, 4) := by decide
theorem nz2_at_2a : fetchRel nonZero256Code 0x2A = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem nz2_at_2e : fetchRel nonZero256Code 0x2E = some (.auipc ra 0x0, 4) := by decide
theorem nz2_at_32 : fetchRel nonZero256Code 0x32 = some (.jalr ra ra 0xFFFFF842, 4) := by decide
theorem nz2_at_36 : fetchRel nonZero256Code 0x36 = some (.alu .add (9 : Fin 32) x0 a0, 2) := by decide
theorem nz2_at_38 : fetchRel nonZero256Code 0x38 = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem nz2_at_3c : fetchRel nonZero256Code 0x3C = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem nz2_at_3e : fetchRel nonZero256Code 0x3E = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem nz2_at_40 : fetchRel nonZero256Code 0x40 = some (.auipc ra 0x2000, 4) := by decide
theorem nz2_at_44 : fetchRel nonZero256Code 0x44 = some (.jalr ra ra 0x728, 4) := by decide
theorem nz2_at_48 : fetchRel nonZero256Code 0x48 = some (.store .sb (18 : Fin 32) (9 : Fin 32) 0x20, 4) := by decide
theorem nz2_at_4c : fetchRel nonZero256Code 0x4C = some (.load .lw ra sp 0x2C, 2) := by decide
theorem nz2_at_4e : fetchRel nonZero256Code 0x4E = some (.load .lw (8 : Fin 32) sp 0x28, 2) := by decide
theorem nz2_at_50 : fetchRel nonZero256Code 0x50 = some (.load .lw (9 : Fin 32) sp 0x24, 2) := by decide
theorem nz2_at_52 : fetchRel nonZero256Code 0x52 = some (.load .lw (18 : Fin 32) sp 0x20, 2) := by decide
theorem nz2_at_54 : fetchRel nonZero256Code 0x54 = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem nz2_at_56 : fetchRel nonZero256Code 0x56 = some (.jalr x0 ra 0x0, 2) := by decide
end

abbrev nzPs : List (Fin 32 × Word) := [(ra, 0xC), ((8 : Fin 32), 0x8), ((9 : Fin 32), 0x4), ((18 : Fin 32), 0x0)]

section
set_option maxRecDepth 20000
theorem nzSave_end : blockEnd nonZero384Code 2 (saveBlock nzPs) = some 0xA := by decide
theorem nzRestore_end : blockEnd nonZero384Code 0x42 (restoreBlock nzPs) = some 0x4A := by decide
end

/-- Where `NonZeroScalar<NistP384>::new` runs: its code and its callees', the
zero constant, the 0x64 bytes of stack below `sp0`, the result `out`, and the
scalar at `x`. -/
structure NZEnv (M : Word → BitVec 8) (P sp0 out x : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P nonZero384Code
  mcod : CodeIn M (P + 0xFFFFFEF6) montyScalarCtEq384Code
  uce : CodeIn M (P + 0xFFFFFEF6 + 0xFFFFFAF4) uint12CtEqCode
  spl : CodeIn M (P + 0xFFFFFEF6 + 0xFFFFFAF4 + 0x80) splitAt12Code
  lce : CodeIn M (P + 0xFFFFFEF6 + 0xFFFFFAF4 + 0xFFFF9DBC) limbCtEqCode
  uiz : CodeIn M (P + 0xFFFFFEF6 + 0xFFFFFAF4 + 0xFFFEF3C4) uintRefIsZeroCode
  unz : CodeIn M (P + 0xFFFFFEF6 + 0xFFFFFAF4 + 0xFFFEF3C4 + 0x1A) uintRefIsNonzeroCode
  bb : CodeIn M (P + 0xFFFFFEF6 + 0xFFFF99AA) blackBoxU8Code
  cn : CodeIn M (P + 0xFFFFDAB2) choiceNotCode
  cnb : CodeIn M (P + 0xFFFFDAB2 + 0xFFFFBDEE) blackBoxU8Code
  stub : CodeIn M (P + 0x9AA) memcpyStubCode
  body : CodeIn M (P + 0x9AA + 8) memcpyBodyCode
  zero : CodeIn M (BitVec.ofNat 32 scalarZero384Address) scalarZero384Data
  hsp : sp0.toNat % 4 = 0
  hS : 0x64 ≤ sp0.toNat
  hx : x.toNat % 4 = 0
  hxw : x.toNat + 48 < 2 ^ 32
  how : out.toNat + 48 < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFF9C) 0x64 P nonZero384Code.length
  sGM : Sep (sp0 + 0xFFFFFF9C) 0x64 (P + 0xFFFFFEF6) montyScalarCtEq384Code.length
  sGU : Sep (sp0 + 0xFFFFFF9C) 0x64 (P + 0xFFFFFEF6 + 0xFFFFFAF4) uint12CtEqCode.length
  sGS : Sep (sp0 + 0xFFFFFF9C) 0x64 (P + 0xFFFFFEF6 + 0xFFFFFAF4 + 0x80) splitAt12Code.length
  sGL : Sep (sp0 + 0xFFFFFF9C) 0x64 (P + 0xFFFFFEF6 + 0xFFFFFAF4 + 0xFFFF9DBC) limbCtEqCode.length
  sGZ : Sep (sp0 + 0xFFFFFF9C) 0x64 (P + 0xFFFFFEF6 + 0xFFFFFAF4 + 0xFFFEF3C4) uintRefIsZeroCode.length
  sGN : Sep (sp0 + 0xFFFFFF9C) 0x64 (P + 0xFFFFFEF6 + 0xFFFFFAF4 + 0xFFFEF3C4 + 0x1A) uintRefIsNonzeroCode.length
  sGB : Sep (sp0 + 0xFFFFFF9C) 0x64 (P + 0xFFFFFEF6 + 0xFFFF99AA) blackBoxU8Code.length
  sGN' : Sep (sp0 + 0xFFFFFF9C) 0x64 (P + 0xFFFFDAB2) choiceNotCode.length
  sGB' : Sep (sp0 + 0xFFFFFF9C) 0x64 (P + 0xFFFFDAB2 + 0xFFFFBDEE) blackBoxU8Code.length
  sGT : Sep (sp0 + 0xFFFFFF9C) 0x64 (P + 0x9AA) memcpyStubCode.length
  sGY : Sep (sp0 + 0xFFFFFF9C) 0x64 (P + 0x9AA + 8) memcpyBodyCode.length
  sZG : Sep (BitVec.ofNat 32 scalarZero384Address) 48 (sp0 + 0xFFFFFF9C) 0x64
  sXG : Sep x 48 (sp0 + 0xFFFFFF9C) 0x64
  sOG : Sep out 49 (sp0 + 0xFFFFFF9C) 0x64
  sOC : Sep out 49 P nonZero384Code.length
  sOY : Sep out 48 (P + 0x9AA + 8) memcpyBodyCode.length
  sOX : Sep out 48 x 48

theorem nz_zero_load (M : Word → BitVec 8) (hz : CodeIn M (BitVec.ofNat 32 scalarZero384Address) scalarZero384Data)
    (i : Nat) (hi : i < 12) : memLoad32 M (BitVec.ofNat 32 scalarZero384Address + BitVec.ofNat 32 (4 * i)) = 0 := by
  have hd : ∀ k, k < 48 → scalarZero384Data.getD k 0 = 0 := by decide
  rw [memLoad32_congr (M := fun _ => 0) fun j hj => by
    rw [add_ofNat_assoc, hz (4 * i + j) (by simp only [scalarZero384Data, List.length_cons, List.length_nil]; omega)]
    simp only [byteAt]; rw [hd _ (by omega)]; rfl]
  unfold memLoad32
  dsimp only
  decide

theorem nz_copy_in {M : Word → BitVec 8} {dst src : Word} {N i : Nat} (hi : i < N) (hN : N < 2 ^ 32) :
    copyBytes M dst src N (dst + BitVec.ofNat 32 i) = M (src + BitVec.ofNat 32 i) := by
  have e : dst + BitVec.ofNat 32 i - dst = BitVec.ofNat 32 i := by rw [BitVec.add_comm, BitVec.add_sub_cancel]
  unfold copyBytes
  rw [e, ite_eq_left (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi)]

theorem nz_not_byte (c : Prop) [Decidable c] :
    (BitVec.ofNat 32 (1 - (aluEval .and (if c then (1 : Word) else 0) 0xFF).toNat)).extractLsb' 0 8 =
      if c then 0 else 1 := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h]; rfl
  · rw [ite_eq_right h, ite_eq_right h]; rfl

theorem nz_not_le (c : Prop) [Decidable c] : (aluEval .and (if c then (1 : Word) else 0) 0xFF).toNat ≤ 1 := by
  by_cases h : c
  · rw [ite_eq_left h]; decide
  · rw [ite_eq_right h]; decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `NonZeroScalar<NistP384>::new`**: it copies the 48 bytes
of the scalar at `x` to `out` and stores at `out + 0x30` the choice that the
scalar is nonzero. -/
theorem nonZero384_correct (m : Machine) {P sp0 out x retAddr : Word} (env : NZEnv m.mem P sp0 out x)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = x)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ i, i < 48 → m'.mem (out + BitVec.ofNat 32 i) = m.mem (x + BitVec.ofNat 32 i)) ∧
      m'.mem (out + 0x30) =
        (if ∀ i : Nat, i < 12 → memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) = 0 then 0 else 1) ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      ∀ y, Sep (sp0 + 0xFFFFFF9C) 0x64 y 1 → Sep out 49 y 1 → m'.mem y = m.mem y := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFF9C = G := ⟨_, rfl⟩
  have sGC := env.sGC; have sGM := env.sGM; have sGU := env.sGU; have sGS := env.sGS; have sGL := env.sGL
  have sGZ := env.sGZ; have sGN := env.sGN; have sGB := env.sGB; have sGN' := env.sGN'; have sGB' := env.sGB'
  have sGT := env.sGT; have sGY := env.sGY; have sZG := env.sZG; have sXG := env.sXG; have sOG := env.sOG
  rw [hG] at sGC sGM sGU sGS sGL sGZ sGN sGB sGN' sGB' sGT sGY sZG sXG sOG ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFF0 = F := ⟨_, rfl⟩
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFF9C) (by decide)
  have hGw : G.toNat + 0x64 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFF9C : Word).toNat = 4294967196 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have eGF : G + BitVec.ofNat 32 0x54 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hFa : F.toNat % 4 = 0 := by rw [← eGF]; exact aligned_add hGa (k := 0x54) (by decide)
  have hFn : F.toNat = G.toNat + 0x54 := by rw [← eGF, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eS : F + 0x10 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x54 + k) := fun k => by rw [← eGF, add_ofNat_assoc]
  have eT : F + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x44 := by rw [← eGF, BitVec.add_assoc]; rfl
  have eM : F + 0xFFFFFFAC = G + BitVec.ofNat 32 0 := by rw [← eGF, BitVec.add_assoc]; rfl
  have eN : F + 0xFFFFFFFF = G + BitVec.ofNat 32 0x53 := by rw [← eGF, BitVec.add_assoc]; rfl
  have gw : G.toNat + 0x64 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x64 → d + k ≤ 0x64 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
    fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0x64 b code'.length → (∀ y, Sep G 0x64 y 1 → M' y = m.mem y) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have inMS : ∀ {b : Word} {l : Nat}, Sep G 0x64 b l → Sep (F + 0xFFFFFFAC) 0x54 b l := fun h => by
    rw [eM]; exact h.sub (c := 0) (l := 0x54) (by decide)
  have inMS' : ∀ {b : Word} {l : Nat}, Sep b l G 0x64 → Sep b l (F + 0xFFFFFFAC) 0x54 := fun h => by
    rw [eM]; exact h.subR (c := 0) (l := 0x54) (by decide)
  have sOG48 : Sep out 48 G 0x64 := by have := sOG.sub (c := 0) (l := 48) (by decide); rwa [add_ofNat_zero] at this
  have sOC48 : Sep out 48 P nonZero384Code.length := by
    have := env.sOC.sub (c := 0) (l := 48) (by decide); rwa [add_ofNat_zero] at this
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod nz4_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFF0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  have slotC : ∀ (o : Word), o.toNat + 4 ≤ 0x10 → ∀ {b : Word} {l : Nat}, Sep G 0x64 b l → Sep (F + o) 4 b l := by
    intro o h2 b l h
    rw [← ofNat_toNat_self o, eFk]; exact h.sub (c := 0x54 + o.toNat) (l := 4) (by omega)
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock nzPs) u1 env.cod nzSave_end (saveBlock_ok _ nzPs _ fun p hp => by
    rw [sp1]
    simp only [nzPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
    exact ⟨aligned_add hFa (by decide), slotC _ (by decide) sGC⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFF0)) nzPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ y, Sep G 0x64 y 1 → Msv y = m.mem y := fun y hy => by
    rw [← hMsv]
    exact saveMem_outside nzPs fun p hp => by
      simp only [nzPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> exact slotC _ (by decide) hy
  have hslv : ∀ r o, (r, o) ∈ nzPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [nzPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  have hc2 : CodeIn Msv P nonZero384Code := cIn env.cod sGC frSv
  -- compare with the zero constant
  obtain ⟨m3, c3, u3⟩ := St.block [.alu .add (8 : Fin 32) x0 a1, .alu .add (9 : Fin 32) x0 a0] u2.self hc2
    (off' := 0xE) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u3
  obtain ⟨m4, d4, u4⟩ := u3.self.lui hc2 nz4_at_e (off' := 0x12) (by decide)
  obtain ⟨m5, c5, u5⟩ := St.block [.aluImm .add a1 a1 (img% lo12 scalarZero384Address), .alu .add a0 x0 (8 : Fin 32)] u4.self hc2
    (off' := 0x18) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u5
  have v38 : reg m3 8 = x := by
    rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u2.self.zero, r2 a1 (by decide), ha1]; exact zw x
  have v39 : reg m3 9 = out := by
    rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a0 (by decide), ha0]; exact zw out
  have k5 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ sp → reg m5 q = reg m q :=
    fun q hv h0 h1 h8 h9 hs => by
      rw [u5.regs, upd_ne hv h0, upd_ne hv h1, u4.regs, upd_ne hv h1, u3.regs, upd_ne hv h9, upd_ne hv h8, r2 q hs]
  have v58 : reg m5 8 = x := by
    rw [u5.regs, upd_ne (by decide) (by decide), upd_ne (by decide) (by decide), u4.regs, upd_ne (by decide) (by decide),
      v38]
  have v59 : reg m5 9 = out := by
    rw [u5.regs, upd_ne (by decide) (by decide), upd_ne (by decide) (by decide), u4.regs, upd_ne (by decide) (by decide),
      v39]
  have sp5 : reg m5 sp = F := by
    rw [u5.regs, upd_ne (by decide) (by decide), upd_ne (by decide) (by decide), u4.regs, upd_ne (by decide) (by decide),
      u3.regs, upd_ne (by decide) (by decide), upd_ne (by decide) (by decide), sp2]
  have v5a0 : reg m5 a0 = x := by
    rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [u4.regs, upd_ne (by decide) (by decide), v38]; exact zw x
  have v5a1 : reg m5 a1 = BitVec.ofNat 32 scalarZero384Address := by
    rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]
  obtain ⟨m6, c6, pc6, mem6, regs6⟩ := u5.self.callRa hc2 nz4_at_18 nz4_at_1c (cb := P + 0xFFFFFEF6)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFFEF6 (by decide))
  have r6 := PEnv.reg1 regs6 u5.self.zero
  have hZM : CodeIn Msv (BitVec.ofNat 32 scalarZero384Address) scalarZero384Data := fun i hi => by
    rw [frSv _ (sZG.sub (c := i) (l := 1) (by simp only [scalarZero384Data, List.length_cons, List.length_nil] at hi; omega)).symm]
    exact env.zero i hi
  have menv : MSEnv m6.mem (P + 0xFFFFFEF6) F x (BitVec.ofNat 32 scalarZero384Address) := by
    rw [mem6]
    exact ⟨even_at P env.hP 0xFFFFFEF6 (by decide), cIn env.mcod sGM frSv, cIn env.uce sGU frSv,
      cIn env.spl sGS frSv, cIn env.lce sGL frSv, cIn env.uiz sGZ frSv, cIn env.unz sGN frSv, cIn env.bb sGB frSv,
      hFa, by omega, env.hx, by decide, inMS sGM, inMS sGU, inMS sGS, inMS sGL, inMS sGZ, inMS sGN, inMS sGB,
      inMS' sXG, inMS' sZG⟩
  obtain ⟨m7, c7, pc7, sp7, a07, k7, f7⟩ := montyScalarCtEq384_correct m6 menv pc6
    (by rw [r6 sp (by decide), sp5]) (by rw [r6 a0 (by decide), v5a0]) (by rw [r6 a1 (by decide), v5a1])
    (by rw [regs6]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x18 + 8) (by decide)))
  rw [mem6] at a07 f7
  have fr7 : ∀ y, Sep G 0x64 y 1 → m7.mem y = m.mem y := fun y hy => by rw [f7 y (inMS hy), frSv y hy]
  have cnd : (∀ i : Nat, i < 12 → memLoad32 Msv (x + BitVec.ofNat 32 (4 * i)) =
      memLoad32 Msv (BitVec.ofNat 32 scalarZero384Address + BitVec.ofNat 32 (4 * i))) ↔
      (∀ i : Nat, i < 12 → memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) = 0) := by
    have e : ∀ i, i < 12 → memLoad32 Msv (x + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) :=
      fun i hi => memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact frSv _ (sXG.sub (c := 4 * i + j) (l := 1) (by omega)).symm
    constructor
    · intro h i hi; rw [← e i hi, h i hi, nz_zero_load Msv hZM i hi]
    · intro h i hi; rw [e i hi, h i hi, nz_zero_load Msv hZM i hi]
  have a07' : reg m7 a0 = if ∀ i : Nat, i < 12 → memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) = 0 then 1 else 0 := by
    rw [a07]
    by_cases h : ∀ i : Nat, i < 12 → memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) = 0
    · rw [ite_eq_left (cnd.mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (cnd.mp h')), ite_eq_right h]
  have hc7 : CodeIn m7.mem P nonZero384Code := cIn env.cod sGC fr7
  have u7 : St m7.mem P m7 (0x18 + 8) (reg m7) := ⟨by rw [pc7], rfl, fun _ => rfl⟩
  obtain ⟨m8, d8, u8⟩ := u7.aluImm hc7 nz4_at_20 (off' := 0x24) (by decide)
  obtain ⟨m9, c9, pc9, mem9, regs9⟩ := u8.self.callRa hc7 nz4_at_24 nz4_at_28 (cb := P + 0xFFFFDAB2)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFDAB2 (by decide))
  have r9 := PEnv.reg1 regs9 u8.self.zero
  have sp9 : reg m9 sp = F := by rw [r9 sp (by decide), u8.regs, upd_ne (by decide) (by decide), sp7]
  obtain ⟨m10, c10, pc10, a010, k10, f10⟩ := choiceNot_correct m9 (P := P + 0xFFFFDAB2)
    (even_at P env.hP 0xFFFFDAB2 (by decide)) (by rw [mem9]; exact cIn env.cn sGN' fr7)
    (by rw [mem9]; exact cIn env.cnb sGB' fr7) pc9
    (by rw [r9 a0 (by decide), u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [a07'])
    (nz_not_le _) (by rw [regs9]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P env.hP (0x24 + 8) (by decide)))
    (by rw [sp9, eN]; exact sGB'.sub (c := 0x53) (l := 1) (by decide))
  rw [mem9, sp9, eN] at f10
  have fr10 : ∀ y, Sep G 0x64 y 1 → m10.mem y = m.mem y := fun y hy => by
    rw [f10 y (hy.sub (c := 0x53) (l := 1) (by decide)), fr7 y hy]
  have hc10 : CodeIn m10.mem P nonZero384Code := cIn env.cod sGC fr10
  have u10 : St m10.mem P m10 (0x24 + 8) (reg m10) := ⟨by rw [pc10], rfl, fun _ => rfl⟩
  -- copy the scalar and store the choice
  obtain ⟨m11, c11, u11⟩ := St.block [.alu .add (18 : Fin 32) x0 a0, .aluImm .add a2 x0 0x30,
    .alu .add a0 x0 (9 : Fin 32), .alu .add a1 x0 (8 : Fin 32)] u10 hc10 (off' := 0x36) (by decide)
    (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u11
  have k7_10 : ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ ra →
      reg m10 q = reg m5 q := fun q hq hr => by
    have h' : q ≠ a0 ∧ q ≠ t1 ∧ oidKeep q = true := by revert hq; revert q; decide
    rw [k10 q h'.1 h'.2.1, r9 q hr, u8.regs, upd_ne' h'.1 u7.zero, k7 q h'.2.2, r6 q hr]
  obtain ⟨m12, c12, pc12, mem12, regs12⟩ := u11.self.callRa hc10 nz4_at_36 nz4_at_3a (cb := P + 0x9AA)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x9AA (by decide))
  have r12 := PEnv.reg1 regs12 u11.self.zero
  have k11 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (18 : Fin 32) → reg m11 q = reg m10 q :=
    fun q hv h0 h1 h2 h18 => by rw [u11.regs, upd_ne hv h1, upd_ne hv h0, upd_ne hv h2, upd_ne hv h18]
  have sp12 : reg m12 sp = F := by
    rw [r12 sp (by decide), k11 sp (by decide) (by decide) (by decide) (by decide) (by decide),
      k10 sp (by decide) (by decide), sp9]
  have v10_9 : reg m10 9 = out := by rw [k7_10 9 (by decide) (by decide), v59]
  have v10_8 : reg m10 8 = x := by rw [k7_10 8 (by decide) (by decide), v58]
  have hFw : (F + 0xFFFFFFF0).toNat + 16 ≤ 2 ^ 32 := by rw [eT, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have E : McEnv m10.mem (P + 0x9AA + 8) out x (F + 0xFFFFFFF0) 48 :=
    ⟨cIn env.body sGY fr10, env.sOY, by rw [eT]; exact sGY.sub (c := 0x44) (l := 16) (by decide),
      by rw [eT]; exact sOG48.subR (c := 0x44) (l := 16) (by decide),
      by rw [eT]; exact sXG.subR (c := 0x44) (l := 16) (by decide), env.sOX,
      aligned_add hFa (by decide), hFw, env.how, env.hxw⟩
  obtain ⟨m13, c13, pc13, sp13, _, f13, k13⟩ := memcpy_correct m12 (P + 0x9AA) _ out x 48
    (fun i hi => by show m12.mem _ = _; rw [mem12]; exact cIn env.stub sGT fr10 i hi)
    (even_at P env.hP 0x9AA (by decide)) pc12
    (by rw [r12 a0 (by decide), u11.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v10_9]; exact zw out)
    (by rw [r12 a1 (by decide), u11.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v10_8]; exact zw x)
    (by rw [r12 a2 (by decide), u11.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [regs12]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x36 + 8) (by decide)))
    (by rw [mem12, sp12]; exact E)
  rw [sp12, mem12] at f13
  rw [sp12] at sp13
  have pT : ∀ {y : Word}, Sep G 0x64 y 1 → Sep (F + 0xFFFFFFF0) 16 y 1 := fun h => by
    rw [eT]; exact h.sub (c := 0x44) (l := 16) (by decide)
  have hc13 : CodeIn m13.mem P nonZero384Code := fun k hk => by
    rw [f13 _ (pT (sGC.subR (c := k) (l := 1) (by omega))),
      copyBytes_sep (sOC48.subR (c := k) (l := 1) (by omega)) (Nat.le_refl 48), fr10 _ (sGC.subR (c := k) (l := 1) (by omega))]
    exact env.cod k hk
  have u13 : St m13.mem P m13 (0x36 + 8) (reg m13) := ⟨by rw [pc13], rfl, fun _ => rfl⟩
  have kk13 : ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m13 q = reg m12 q :=
    fun q hq => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, ht0, ht1, h7', h28, h29, h30, hs⟩ : q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧
        q ≠ a5 ∧ q ≠ a6 ∧ q ≠ a7 ∧ q ≠ t0 ∧ q ≠ t1 ∧ q ≠ (7 : Fin 32) ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧
        q ≠ (30 : Fin 32) ∧ q ≠ sp := by revert hq; revert q; decide
      exact k13 q h1 h2 h3 h4 h5 h6 h7 ht0 ht1 h7' h28 h29 h30 hs
  have v13_9 : reg m13 9 = out := by
    rw [kk13 9 (by decide), r12 9 (by decide), k11 9 (by decide) (by decide) (by decide) (by decide) (by decide), v10_9]
  have v13_18 : reg m13 18 = BitVec.ofNat 32 (1 - (aluEval .and
      (if ∀ i : Nat, i < 12 → memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) = 0 then (1 : Word) else 0) 0xFF).toNat) := by
    rw [kk13 18 (by decide), r12 18 (by decide), u11.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [u10.zero, a010]; exact zw _
  obtain ⟨m14, d14, u14⟩ := u13.sb hc13 nz4_at_3e (off' := 0x42) (by decide)
  rw [v13_9, v13_18, nz_not_byte] at u14
  obtain ⟨M14, hM14⟩ : ∃ M14, memStore8 m13.mem (out + 0x30)
      (if ∀ i : Nat, i < 12 → memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) = 0 then 0 else 1) = M14 := ⟨_, rfl⟩
  rw [hM14] at u14
  have hc14 : CodeIn M14 P nonZero384Code := by rw [← hM14]; exact hc13.store8 (env.sOC.sub (c := 0x30) (l := 1) (by decide))
  have slotM : ∀ k, 0x54 ≤ k → k < 0x64 → M14 (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) := by
    intro k h1 h2
    rw [← hM14, memStore8_ne (a := out + 0x30) (fun e => sOG 0x30 (by decide) k (by omega) e.symm),
      f13 _ (by rw [eT]; exact offs (.inl (by omega)) (by decide) (by omega)),
      copyBytes_sep (sOG48.subR (c := k) (l := 1) (by omega)) (Nat.le_refl 48),
      f10 _ (offs (.inl (by omega)) (by decide) (by omega)),
      f7 _ (by rw [eM]; exact offs (.inl (by omega)) (by decide) (by omega))]
  have slotW : ∀ r o, (r, o) ∈ nzPs → memLoad32 M14 (F + o) = reg m r := fun r o h => by
    have ho : o.toNat + 4 ≤ 0x10 := by
      simp only [nzPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hslv r o h]
    apply memLoad32_congr; intro j hj
    rw [← ofNat_toNat_self o, add_ofNat_assoc, eFk, slotM _ (by omega) (by omega)]
  have hpsp : ∀ p ∈ nzPs, p.1 ≠ sp := by decide
  obtain ⟨n1, e1, w1⟩ := St.block (restoreBlock nzPs) u14 hc14 nzRestore_end
    (restoreBlock_ok M14 F nzPs (reg m13) sp13 hpsp fun q hq => by
      simp only [nzPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
  simp only [restoreBlock_run M14 F nzPs (reg m13) sp13 hpsp] at w1
  have rsp1 : restoreRegs M14 F (reg m13) nzPs sp = F := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact sp13
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs M14 F f ps q = f q := by
    intro f ps q h0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
  have hreg : ∀ r o, (r, o) ∈ nzPs → restoreRegs M14 F (reg m13) nzPs r = reg m r := fun r o hm => by
    simp only [nzPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact slotW _ _ (by decide)
  obtain ⟨n2, e2, w2⟩ := w1.aluImm hc14 nz4_at_4a (off' := 0x4C) (by decide)
  obtain ⟨n3, e3, pc3, mem3, regs3⟩ := w2.jalr hc14 nz4_at_4c
  have kfin : ∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m13 q = reg m q := fun q hq => by
    have hq' : q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
    obtain ⟨hv, h0, h1, h2, h8, h9, h18, hs, hr⟩ : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ (8 : Fin 32) ∧
        q ≠ (9 : Fin 32) ∧ q ≠ (18 : Fin 32) ∧ q ≠ sp ∧ q ≠ ra := by
      clear hq'; revert hq; revert q; decide
    rw [kk13 q hq', r12 q hr, k11 q hv h0 h1 h2 h18, k7_10 q hq' hr, k5 q hv h0 h1 h8 h9 hs]
  refine ⟨n3, .cons d1 (c2.trans (c3.trans (.cons d4 (c5.trans (c6.trans (c7.trans (.cons d8 (c9.trans (c10.trans
    (c11.trans (c12.trans (c13.trans (.cons d14 (e1.trans (.cons e2 (.single e3)))))))))))))))), ?_, ?_,
    fun i hi => ?_, ?_, fun q hq => ?_, fun y hy ho => ?_⟩
  · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [hreg ra 0xC (by decide), hra, add_lit_zero, hret]
  · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp1, eS]
  · have hs : Sep (F + 0xFFFFFFF0) 16 (out + BitVec.ofNat 32 i) 1 := by
      rw [eT]; exact (sOG48.symm.sub (c := 0x44) (l := 16) (by decide)).subR (c := i) (l := 1) (by omega)
    rw [mem3, ← hM14, memStore8_ne (a := out + 0x30) (add_ofNat_ne out (c := i) (d := 0x30) (by omega) (by decide) (by omega)),
      f13 _ hs, nz_copy_in hi (by decide), fr10 _ (sXG.sub (c := i) (l := 1) (by omega)).symm]
  · rw [mem3, ← hM14, memStore8_same]
  · rw [regs3]
    have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨
        (q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ nzPs, p.1 ≠ q)) := by
      decide
    rcases key q hq with rfl | rfl | rfl | rfl | ⟨h1, h0, hs, hps⟩
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0xC (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x8 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x4 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x0 (by decide)
    · rw [upd_ne h0 hs, rr _ _ q h0 hps]; exact kfin q h1
  · have h48 : Sep out 48 y 1 := by have := ho.sub (c := 0) (l := 48) (by decide); rwa [add_ofNat_zero] at this
    have hne : y ≠ out + 0x30 := fun e => ho 0x30 (by decide) 0 (by decide) (by rw [add_ofNat_zero, e]; rfl)
    rw [mem3, ← hM14, memStore8_ne hne, f13 y (pT hy), copyBytes_sep h48 (Nat.le_refl 48), fr10 y hy]

abbrev nz2Ps : List (Fin 32 × Word) := [(ra, 0x2C), ((8 : Fin 32), 0x28), ((9 : Fin 32), 0x24), ((18 : Fin 32), 0x20)]

section
set_option maxRecDepth 20000
theorem nz2Save_end : blockEnd nonZero256Code 2 (saveBlock nz2Ps) = some 0xA := by decide
theorem nz2Restore_end : blockEnd nonZero256Code 0x4C (restoreBlock nz2Ps) = some 0x54 := by decide
end

/-- Where `NonZeroScalar<NistP256>::new` runs: its code and its callees', the
0x84 bytes of stack below `sp0`, the result `out`, and the scalar at `x`. -/
structure NZ2Env (M : Word → BitVec 8) (P sp0 out x : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P nonZero256Code
  mset : CodeIn M (P + 0x2700) memsetCode
  psc : CodeIn M (P + 0xFFFFFD20) p256ScalarCtEqCode
  uce : CodeIn M (P + 0xFFFFFD20 + 0xFFFFFB5E) uint8CtEqCode
  spl : CodeIn M (P + 0xFFFFFD20 + 0xFFFFFB5E + 0x80) splitAt8Code
  lce : CodeIn M (P + 0xFFFFFD20 + 0xFFFFFB5E + 0xFFFFBCE6) limbCtEqCode
  uiz : CodeIn M (P + 0xFFFFFD20 + 0xFFFFFB5E + 0xFFFF12EE) uintRefIsZeroCode
  unz : CodeIn M (P + 0xFFFFFD20 + 0xFFFFFB5E + 0xFFFF12EE + 0x1A) uintRefIsNonzeroCode
  bb : CodeIn M (P + 0xFFFFFD20 + 0xFFFFB93E) blackBoxU8Code
  cn : CodeIn M (P + 0xFFFFF870) choiceNotCode
  cnb : CodeIn M (P + 0xFFFFF870 + 0xFFFFBDEE) blackBoxU8Code
  stub : CodeIn M (P + 0x2768) memcpyStubCode
  body : CodeIn M (P + 0x2768 + 8) memcpyBodyCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x84 ≤ sp0.toNat
  hx : x.toNat % 4 = 0
  hxw : x.toNat + 32 < 2 ^ 32
  how : out.toNat + 32 < 2 ^ 32
  sGC : Sep (sp0 + 0xFFFFFF7C) 0x84 P nonZero256Code.length
  sGMs : Sep (sp0 + 0xFFFFFF7C) 0x84 (P + 0x2700) memsetCode.length
  sGP : Sep (sp0 + 0xFFFFFF7C) 0x84 (P + 0xFFFFFD20) p256ScalarCtEqCode.length
  sGU : Sep (sp0 + 0xFFFFFF7C) 0x84 (P + 0xFFFFFD20 + 0xFFFFFB5E) uint8CtEqCode.length
  sGS : Sep (sp0 + 0xFFFFFF7C) 0x84 (P + 0xFFFFFD20 + 0xFFFFFB5E + 0x80) splitAt8Code.length
  sGL : Sep (sp0 + 0xFFFFFF7C) 0x84 (P + 0xFFFFFD20 + 0xFFFFFB5E + 0xFFFFBCE6) limbCtEqCode.length
  sGZ : Sep (sp0 + 0xFFFFFF7C) 0x84 (P + 0xFFFFFD20 + 0xFFFFFB5E + 0xFFFF12EE) uintRefIsZeroCode.length
  sGN : Sep (sp0 + 0xFFFFFF7C) 0x84 (P + 0xFFFFFD20 + 0xFFFFFB5E + 0xFFFF12EE + 0x1A) uintRefIsNonzeroCode.length
  sGB : Sep (sp0 + 0xFFFFFF7C) 0x84 (P + 0xFFFFFD20 + 0xFFFFB93E) blackBoxU8Code.length
  sGN' : Sep (sp0 + 0xFFFFFF7C) 0x84 (P + 0xFFFFF870) choiceNotCode.length
  sGB' : Sep (sp0 + 0xFFFFFF7C) 0x84 (P + 0xFFFFF870 + 0xFFFFBDEE) blackBoxU8Code.length
  sGT : Sep (sp0 + 0xFFFFFF7C) 0x84 (P + 0x2768) memcpyStubCode.length
  sGY : Sep (sp0 + 0xFFFFFF7C) 0x84 (P + 0x2768 + 8) memcpyBodyCode.length
  sXG : Sep x 32 (sp0 + 0xFFFFFF7C) 0x84
  sOG : Sep out 0x21 (sp0 + 0xFFFFFF7C) 0x84
  sOC : Sep out 0x21 P nonZero256Code.length
  sOY : Sep out 32 (P + 0x2768 + 8) memcpyBodyCode.length
  sOX : Sep out 32 x 32

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `NonZeroScalar<NistP256>::new`**: it copies the 32 bytes
of the scalar at `x` to `out` and stores at `out + 0x20` the choice that the
scalar is nonzero. -/
theorem nonZero256_correct (m : Machine) {P sp0 out x retAddr : Word} (env : NZ2Env m.mem P sp0 out x)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = x)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ i, i < 32 → m'.mem (out + BitVec.ofNat 32 i) = m.mem (x + BitVec.ofNat 32 i)) ∧
      m'.mem (out + 0x20) =
        (if ∀ i : Nat, i < 8 → memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) = 0 then 0 else 1) ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      ∀ y, Sep (sp0 + 0xFFFFFF7C) 0x84 y 1 → Sep out 0x21 y 1 → m'.mem y = m.mem y := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFF7C = G := ⟨_, rfl⟩
  have sGC := env.sGC; have sGMs := env.sGMs; have sGP := env.sGP; have sGU := env.sGU; have sGS := env.sGS
  have sGL := env.sGL; have sGZ := env.sGZ; have sGN := env.sGN; have sGB := env.sGB; have sGN' := env.sGN'
  have sGB' := env.sGB'; have sGT := env.sGT; have sGY := env.sGY; have sXG := env.sXG; have sOG := env.sOG
  rw [hG] at sGC sGMs sGP sGU sGS sGL sGZ sGN sGB sGN' sGB' sGT sGY sXG sOG ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFD0 = F := ⟨_, rfl⟩
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFF7C) (by decide)
  have hGw : G.toNat + 0x84 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFF7C : Word).toNat = 4294967164 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have eGF : G + BitVec.ofNat 32 0x54 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hFa : F.toNat % 4 = 0 := by rw [← eGF]; exact aligned_add hGa (k := 0x54) (by decide)
  have hFn : F.toNat = G.toNat + 0x54 := by rw [← eGF, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eS : F + 0x30 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x54 + k) := fun k => by rw [← eGF, add_ofNat_assoc]
  have eT : F + 0xFFFFFFF0 = G + BitVec.ofNat 32 0x44 := by rw [← eGF, BitVec.add_assoc]; rfl
  have eM : F + 0xFFFFFFAC = G + BitVec.ofNat 32 0 := by rw [← eGF, BitVec.add_assoc]; rfl
  have eN : F + 0xFFFFFFFF = G + BitVec.ofNat 32 0x53 := by rw [← eGF, BitVec.add_assoc]; rfl
  have gw : G.toNat + 0x84 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x84 → d + k ≤ 0x84 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
    fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0x84 b code'.length → (∀ y, Sep G 0x84 y 1 → M' y = m.mem y) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have inMS : ∀ {b : Word} {l : Nat}, Sep G 0x84 b l → Sep (F + 0xFFFFFFAC) 0x54 b l := fun h => by
    rw [eM]; exact h.sub (c := 0) (l := 0x54) (by decide)
  have inMS' : ∀ {b : Word} {l : Nat}, Sep b l G 0x84 → Sep b l (F + 0xFFFFFFAC) 0x54 := fun h => by
    rw [eM]; exact h.subR (c := 0) (l := 0x54) (by decide)
  have sOG32 : Sep out 32 G 0x84 := by have := sOG.sub (c := 0) (l := 32) (by decide); rwa [add_ofNat_zero] at this
  have sOC32 : Sep out 32 P nonZero256Code.length := by
    have := env.sOC.sub (c := 0) (l := 32) (by decide); rwa [add_ofNat_zero] at this
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod nz2_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  have slotC : ∀ (o : Word), 0x20 ≤ o.toNat → o.toNat + 4 ≤ 0x30 → ∀ {b : Word} {l : Nat}, Sep G 0x84 b l →
      Sep (F + o) 4 b l := by
    intro o h1 h2 b l h
    rw [← ofNat_toNat_self o, eFk]; exact h.sub (c := 0x54 + o.toNat) (l := 4) (by omega)
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock nz2Ps) u1 env.cod nz2Save_end (saveBlock_ok _ nz2Ps _ fun p hp => by
    rw [sp1]
    simp only [nz2Ps, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
    exact ⟨aligned_add hFa (by decide), slotC _ (by decide) (by decide) sGC⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0)) nz2Ps = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ y, Sep G 0x84 y 1 → Msv y = m.mem y := fun y hy => by
    rw [← hMsv]
    exact saveMem_outside nz2Ps fun p hp => by
      simp only [nz2Ps, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> exact slotC _ (by decide) (by decide) hy
  have hslv : ∀ r o, (r, o) ∈ nz2Ps → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [nz2Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  have hc2 : CodeIn Msv P nonZero256Code := cIn env.cod sGC frSv
  -- zero the comparand on the stack, then compare
  obtain ⟨m3, c3, u3⟩ := St.block [.alu .add (8 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .alu .add a0 x0 sp,
    .aluImm .add a2 x0 0x20, .aluImm .add a1 x0 0] u2.self hc2 (off' := 0x16) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u3
  have z2 := u2.self.zero
  obtain ⟨m4, c4, u4, _, k4⟩ := u3.self.memsetW (B := P + 0x2700) (w := 8) (dst := F)
    (even_at P env.hP 0x2700 (by decide)) hc2 (cIn env.mset sGMs frSv) nz2_at_16 nz2_at_1a
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP (0x16 + 8) (by decide)) (by decide)
    (by omega) (by decide) hFa (by rw [← eGF]; exact sGMs.sub (c := 0x54) (l := 32) (by decide))
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; exact zw F)
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [u3.regs]; simp +decide only [upd_app, ↓reduceIte])
  obtain ⟨Mz, hMz⟩ : ∃ Mz, fillWords Msv F 0 8 = Mz := ⟨_, rfl⟩
  rw [hMz] at u4
  have frZ : ∀ y, Sep G 0x84 y 1 → Mz y = m.mem y := fun y hy => by
    rw [← hMz, fillWords_outside 8 (by rw [← eGF]; exact hy.sub (c := 0x54) (l := 32) (by decide)), frSv y hy]
  have hc4 : CodeIn Mz P nonZero256Code := cIn env.cod sGC frZ
  have v4_8 : reg m4 8 = x := by
    rw [k4 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u3.regs]
    simp +decide only [upd_app, ↓reduceIte]; rw [z2, r2 a1 (by decide), ha1]; exact zw x
  have v4_18 : reg m4 18 = out := by
    rw [k4 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u3.regs]
    simp +decide only [upd_app, ↓reduceIte]; rw [r2 a0 (by decide), ha0]; exact zw out
  have v4sp : reg m4 sp = F := by
    rw [k4 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u3.regs]
    simp +decide only [upd_app, ↓reduceIte]; exact sp2
  have K4 : ∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m4 q = reg m q := fun q hq => by
    obtain ⟨h2, h3, h4, h5, h6, hr, h0, h1, h8, h18, hs, hv⟩ : q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ ra ∧
      q ≠ a0 ∧ q ≠ a1 ∧ q ≠ (8 : Fin 32) ∧ q ≠ (18 : Fin 32) ∧ q ≠ sp ∧ q.val ≠ 0 := by revert hq; revert q; decide
    rw [k4 q h2 h3 h4 h5 h6 hr, u3.regs, upd_ne hv h1, upd_ne hv h2, upd_ne hv h0, upd_ne hv h18, upd_ne hv h8,
      r2 q hs]
  obtain ⟨m5, c5, u5⟩ := St.block [.alu .add a1 x0 sp, .alu .add a0 x0 (8 : Fin 32)] u4 hc4 (off' := 0x22)
    (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u5
  have k5 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → reg m5 q = reg m4 q := fun q hv h0 h1 => by
    rw [u5.regs, upd_ne hv h0, upd_ne hv h1]
  have sp5 : reg m5 sp = F := by rw [k5 sp (by decide) (by decide) (by decide), v4sp]
  have v58 : reg m5 8 = x := by rw [k5 8 (by decide) (by decide) (by decide), v4_8]
  have v5_18 : reg m5 18 = out := by rw [k5 18 (by decide) (by decide) (by decide), v4_18]
  have K5 : ∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m5 q = reg m q := fun q hq => by
    have h' : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 := by revert hq; revert q; decide
    rw [k5 q h'.1 h'.2.1 h'.2.2]; exact K4 q hq
  have v5a0 : reg m5 a0 = x := by
    rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v4_8]; exact zw x
  have v5a1 : reg m5 a1 = F := by
    rw [u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v4sp]; exact zw F
  obtain ⟨m6, c6, pc6, mem6, regs6⟩ := u5.self.callRa hc4 nz2_at_22 nz2_at_26 (cb := P + 0xFFFFFD20)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFFD20 (by decide))
  have r6 := PEnv.reg1 regs6 u5.self.zero
  have menv : P2SEnv m6.mem (P + 0xFFFFFD20) F x F := by
    rw [mem6]
    exact ⟨even_at P env.hP 0xFFFFFD20 (by decide), cIn env.psc sGP frZ, cIn env.uce sGU frZ,
      cIn env.spl sGS frZ, cIn env.lce sGL frZ, cIn env.uiz sGZ frZ, cIn env.unz sGN frZ, cIn env.bb sGB frZ,
      hFa, by omega, env.hx, hFa, inMS sGP, inMS sGU, inMS sGS, inMS sGL, inMS sGZ, inMS sGN, inMS sGB,
      inMS' sXG, by rw [eM, ← eGF]; exact offs (.inr (by decide)) (by decide) (by decide)⟩
  obtain ⟨m7, c7, pc7, sp7, a07, k7, f7⟩ := p256ScalarCtEq_correct m6 menv pc6
    (by rw [r6 sp (by decide), sp5]) (by rw [r6 a0 (by decide), v5a0]) (by rw [r6 a1 (by decide), v5a1])
    (by rw [regs6]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x22 + 8) (by decide)))
  rw [mem6] at a07 f7
  have fr7 : ∀ y, Sep G 0x84 y 1 → m7.mem y = m.mem y := fun y hy => by rw [f7 y (inMS hy), frZ y hy]
  have cnd : (∀ i : Nat, i < 8 → memLoad32 Mz (x + BitVec.ofNat 32 (4 * i)) =
      memLoad32 Mz (F + BitVec.ofNat 32 (4 * i))) ↔
      (∀ i : Nat, i < 8 → memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) = 0) := by
    have e : ∀ i, i < 8 → memLoad32 Mz (x + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) :=
      fun i hi => memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact frZ _ (sXG.sub (c := 4 * i + j) (l := 1) (by omega)).symm
    have z : ∀ i, i < 8 → memLoad32 Mz (F + BitVec.ofNat 32 (4 * i)) = 0 := fun i hi => by
      rw [← hMz]; exact fillWords_load 8 i hi (by omega)
    constructor
    · intro h i hi; rw [← e i hi, h i hi, z i hi]
    · intro h i hi; rw [e i hi, h i hi, z i hi]
  have a07' : reg m7 a0 = if ∀ i : Nat, i < 8 → memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) = 0 then 1 else 0 := by
    rw [a07]
    by_cases h : ∀ i : Nat, i < 8 → memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) = 0
    · rw [ite_eq_left (cnd.mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (cnd.mp h')), ite_eq_right h]
  have hc7 : CodeIn m7.mem P nonZero256Code := cIn env.cod sGC fr7
  have u7 : St m7.mem P m7 (0x22 + 8) (reg m7) := ⟨by rw [pc7], rfl, fun _ => rfl⟩
  obtain ⟨m8, d8, u8⟩ := u7.aluImm hc7 nz2_at_2a (off' := 0x2E) (by decide)
  obtain ⟨m9, c9, pc9, mem9, regs9⟩ := u8.self.callRa hc7 nz2_at_2e nz2_at_32 (cb := P + 0xFFFFF870)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFF870 (by decide))
  have r9 := PEnv.reg1 regs9 u8.self.zero
  have sp9 : reg m9 sp = F := by rw [r9 sp (by decide), u8.regs, upd_ne (by decide) (by decide), sp7]
  obtain ⟨m10, c10, pc10, a010, k10, f10⟩ := choiceNot_correct m9 (P := P + 0xFFFFF870)
    (even_at P env.hP 0xFFFFF870 (by decide)) (by rw [mem9]; exact cIn env.cn sGN' fr7)
    (by rw [mem9]; exact cIn env.cnb sGB' fr7) pc9
    (by rw [r9 a0 (by decide), u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [a07'])
    (nz_not_le _) (by rw [regs9]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P env.hP (0x2E + 8) (by decide)))
    (by rw [sp9, eN]; exact sGB'.sub (c := 0x53) (l := 1) (by decide))
  rw [mem9, sp9, eN] at f10
  have fr10 : ∀ y, Sep G 0x84 y 1 → m10.mem y = m.mem y := fun y hy => by
    rw [f10 y (hy.sub (c := 0x53) (l := 1) (by decide)), fr7 y hy]
  have hc10 : CodeIn m10.mem P nonZero256Code := cIn env.cod sGC fr10
  have u10 : St m10.mem P m10 (0x2E + 8) (reg m10) := ⟨by rw [pc10], rfl, fun _ => rfl⟩
  -- copy the scalar and store the choice
  obtain ⟨m11, c11, u11⟩ := St.block [.alu .add (9 : Fin 32) x0 a0, .aluImm .add a2 x0 0x20,
    .alu .add a0 x0 (18 : Fin 32), .alu .add a1 x0 (8 : Fin 32)] u10 hc10 (off' := 0x40) (by decide)
    (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u11
  have k7_10 : ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ ra →
      reg m10 q = reg m5 q := fun q hq hr => by
    have h' : q ≠ a0 ∧ q ≠ t1 ∧ oidKeep q = true := by revert hq; revert q; decide
    rw [k10 q h'.1 h'.2.1, r9 q hr, u8.regs, upd_ne' h'.1 u7.zero, k7 q h'.2.2, r6 q hr]
  obtain ⟨m12, c12, pc12, mem12, regs12⟩ := u11.self.callRa hc10 nz2_at_40 nz2_at_44 (cb := P + 0x2768)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x2768 (by decide))
  have r12 := PEnv.reg1 regs12 u11.self.zero
  have k11 : ∀ q, q.val ≠ 0 → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (9 : Fin 32) → reg m11 q = reg m10 q :=
    fun q hv h0 h1 h2 h9 => by rw [u11.regs, upd_ne hv h1, upd_ne hv h0, upd_ne hv h2, upd_ne hv h9]
  have sp12 : reg m12 sp = F := by
    rw [r12 sp (by decide), k11 sp (by decide) (by decide) (by decide) (by decide) (by decide),
      k10 sp (by decide) (by decide), sp9]
  have v10_18 : reg m10 18 = out := by rw [k7_10 18 (by decide) (by decide), v5_18]
  have v10_8 : reg m10 8 = x := by rw [k7_10 8 (by decide) (by decide), v58]
  have hFw : (F + 0xFFFFFFF0).toNat + 16 ≤ 2 ^ 32 := by rw [eT, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have E : McEnv m10.mem (P + 0x2768 + 8) out x (F + 0xFFFFFFF0) 32 :=
    ⟨cIn env.body sGY fr10, env.sOY, by rw [eT]; exact sGY.sub (c := 0x44) (l := 16) (by decide),
      by rw [eT]; exact sOG32.subR (c := 0x44) (l := 16) (by decide),
      by rw [eT]; exact sXG.subR (c := 0x44) (l := 16) (by decide), env.sOX,
      aligned_add hFa (by decide), hFw, env.how, env.hxw⟩
  obtain ⟨m13, c13, pc13, sp13, _, f13, k13⟩ := memcpy_correct m12 (P + 0x2768) _ out x 32
    (fun i hi => by show m12.mem _ = _; rw [mem12]; exact cIn env.stub sGT fr10 i hi)
    (even_at P env.hP 0x2768 (by decide)) pc12
    (by rw [r12 a0 (by decide), u11.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v10_18]; exact zw out)
    (by rw [r12 a1 (by decide), u11.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [v10_8]; exact zw x)
    (by rw [r12 a2 (by decide), u11.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [regs12]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x40 + 8) (by decide)))
    (by rw [mem12, sp12]; exact E)
  rw [sp12, mem12] at f13
  rw [sp12] at sp13
  have pT : ∀ {y : Word}, Sep G 0x84 y 1 → Sep (F + 0xFFFFFFF0) 16 y 1 := fun h => by
    rw [eT]; exact h.sub (c := 0x44) (l := 16) (by decide)
  have hc13 : CodeIn m13.mem P nonZero256Code := fun k hk => by
    rw [f13 _ (pT (sGC.subR (c := k) (l := 1) (by omega))),
      copyBytes_sep (sOC32.subR (c := k) (l := 1) (by omega)) (Nat.le_refl 32), fr10 _ (sGC.subR (c := k) (l := 1) (by omega))]
    exact env.cod k hk
  have u13 : St m13.mem P m13 (0x40 + 8) (reg m13) := ⟨by rw [pc13], rfl, fun _ => rfl⟩
  have kk13 : ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m13 q = reg m12 q :=
    fun q hq => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, ht0, ht1, h7', h28, h29, h30, hs⟩ : q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧
        q ≠ a5 ∧ q ≠ a6 ∧ q ≠ a7 ∧ q ≠ t0 ∧ q ≠ t1 ∧ q ≠ (7 : Fin 32) ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧
        q ≠ (30 : Fin 32) ∧ q ≠ sp := by revert hq; revert q; decide
      exact k13 q h1 h2 h3 h4 h5 h6 h7 ht0 ht1 h7' h28 h29 h30 hs
  have v13_18 : reg m13 18 = out := by
    rw [kk13 18 (by decide), r12 18 (by decide), k11 18 (by decide) (by decide) (by decide) (by decide) (by decide), v10_18]
  have v13_9 : reg m13 9 = BitVec.ofNat 32 (1 - (aluEval .and
      (if ∀ i : Nat, i < 8 → memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) = 0 then (1 : Word) else 0) 0xFF).toNat) := by
    rw [kk13 9 (by decide), r12 9 (by decide), u11.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [u10.zero, a010]; exact zw _
  obtain ⟨m14, d14, u14⟩ := u13.sb hc13 nz2_at_48 (off' := 0x4C) (by decide)
  rw [v13_18, v13_9, nz_not_byte] at u14
  obtain ⟨M14, hM14⟩ : ∃ M14, memStore8 m13.mem (out + 0x20)
      (if ∀ i : Nat, i < 8 → memLoad32 m.mem (x + BitVec.ofNat 32 (4 * i)) = 0 then 0 else 1) = M14 := ⟨_, rfl⟩
  rw [hM14] at u14
  have hc14 : CodeIn M14 P nonZero256Code := by rw [← hM14]; exact hc13.store8 (env.sOC.sub (c := 0x20) (l := 1) (by decide))
  have slotM : ∀ k, 0x74 ≤ k → k < 0x84 → M14 (G + BitVec.ofNat 32 k) = Msv (G + BitVec.ofNat 32 k) := by
    intro k h1 h2
    rw [← hM14, memStore8_ne (a := out + 0x20) (fun e => sOG 0x20 (by decide) k (by omega) e.symm),
      f13 _ (by rw [eT]; exact offs (.inl (by omega)) (by decide) (by omega)),
      copyBytes_sep (sOG32.subR (c := k) (l := 1) (by omega)) (Nat.le_refl 32),
      f10 _ (offs (.inl (by omega)) (by decide) (by omega)),
      f7 _ (by rw [eM]; exact offs (.inl (by omega)) (by decide) (by omega)),
      ← hMz, fillWords_outside 8 (by rw [← eGF]; exact offs (.inl (by omega)) (by decide) (by omega))]
  have slotW : ∀ r o, (r, o) ∈ nz2Ps → memLoad32 M14 (F + o) = reg m r := fun r o h => by
    have ho : 0x20 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x30 := by
      simp only [nz2Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hslv r o h]
    apply memLoad32_congr; intro j hj
    rw [← ofNat_toNat_self o, add_ofNat_assoc, eFk, slotM _ (by omega) (by omega)]
  have hpsp : ∀ p ∈ nz2Ps, p.1 ≠ sp := by decide
  obtain ⟨n1, e1, w1⟩ := St.block (restoreBlock nz2Ps) u14 hc14 nz2Restore_end
    (restoreBlock_ok M14 F nz2Ps (reg m13) sp13 hpsp fun q hq => by
      simp only [nz2Ps, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
  simp only [restoreBlock_run M14 F nz2Ps (reg m13) sp13 hpsp] at w1
  have rsp1 : restoreRegs M14 F (reg m13) nz2Ps sp = F := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact sp13
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs M14 F f ps q = f q := by
    intro f ps q h0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
  have hreg : ∀ r o, (r, o) ∈ nz2Ps → restoreRegs M14 F (reg m13) nz2Ps r = reg m r := fun r o hm => by
    simp only [nz2Ps, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact slotW _ _ (by decide)
  obtain ⟨n2, e2, w2⟩ := w1.aluImm hc14 nz2_at_54 (off' := 0x56) (by decide)
  obtain ⟨n3, e3, pc3, mem3, regs3⟩ := w2.jalr hc14 nz2_at_56
  have kfin : ∀ q, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m13 q = reg m q := fun q hq => by
    have hq' : q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
    obtain ⟨hv, h0, h1, h2, h9, hr⟩ : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ (9 : Fin 32) ∧ q ≠ ra := by
      clear hq'; revert hq; revert q; decide
    rw [kk13 q hq', r12 q hr, k11 q hv h0 h1 h2 h9, k7_10 q hq' hr, K5 q hq]
  refine ⟨n3, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (.cons d8 (c9.trans (c10.trans
    (c11.trans (c12.trans (c13.trans (.cons d14 (e1.trans (.cons e2 (.single e3)))))))))))))))), ?_, ?_,
    fun i hi => ?_, ?_, fun q hq => ?_, fun y hy ho => ?_⟩
  · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [hreg ra 0x2C (by decide), hra, add_lit_zero, hret]
  · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp1, eS]
  · have hs : Sep (F + 0xFFFFFFF0) 16 (out + BitVec.ofNat 32 i) 1 := by
      rw [eT]; exact (sOG32.symm.sub (c := 0x44) (l := 16) (by decide)).subR (c := i) (l := 1) (by omega)
    rw [mem3, ← hM14, memStore8_ne (a := out + 0x20) (add_ofNat_ne out (c := i) (d := 0x20) (by omega) (by decide) (by omega)),
      f13 _ hs, nz_copy_in hi (by decide), fr10 _ (sXG.sub (c := i) (l := 1) (by omega)).symm]
  · rw [mem3, ← hM14, memStore8_same]
  · rw [regs3]
    have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨
        (q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ nz2Ps, p.1 ≠ q)) := by
      decide
    rcases key q hq with rfl | rfl | rfl | rfl | ⟨h1, h0, hs, hps⟩
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x2C (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x28 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x24 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x20 (by decide)
    · rw [upd_ne h0 hs, rr _ _ q h0 hps]; exact kfin q h1
  · have h48 : Sep out 32 y 1 := by have := ho.sub (c := 0) (l := 32) (by decide); rwa [add_ofNat_zero] at this
    have hne : y ≠ out + 0x20 := fun e => ho 0x20 (by decide) 0 (by decide) (by rw [add_ofNat_zero, e]; rfl)
    rw [mem3, ← hM14, memStore8_ne hne, f13 y (pT hy), copyBytes_sep h48 (Nat.le_refl 32), fr10 y hy]

end C3.RV32
