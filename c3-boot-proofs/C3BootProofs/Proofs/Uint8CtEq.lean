import C3BootProofs.Proofs.CtWrap

/-!
# `Uint<8>::ct_eq`, as compiled

The same code as the proved `Uint<12>::ct_eq` with different call offsets:
it splits each operand with the proved `split_at (.165)`, compares the limbs
with the proved limb `ct_eq`, and checks that both remainders are empty with
the proved `UintRef::is_zero`. P-256's `Scalar::ct_eq` calls it and passes the
result through `black_box`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem u8e_at_0 : fetchRel uint8CtEqCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem u8e_at_2 : fetchRel uint8CtEqCode 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem u8e_at_4 : fetchRel uint8CtEqCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x28, 2) := by decide
theorem u8e_at_6 : fetchRel uint8CtEqCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x24, 2) := by decide
theorem u8e_at_8 : fetchRel uint8CtEqCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x20, 2) := by decide
theorem u8e_at_a : fetchRel uint8CtEqCode 0xA = some (.store .sw sp (19 : Fin 32) 0x1C, 2) := by decide
theorem u8e_at_c : fetchRel uint8CtEqCode 0xC = some (.store .sw sp (20 : Fin 32) 0x18, 2) := by decide
theorem u8e_at_e : fetchRel uint8CtEqCode 0xE = some (.store .sw sp (21 : Fin 32) 0x14, 2) := by decide
theorem u8e_at_10 : fetchRel uint8CtEqCode 0x10 = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem u8e_at_12 : fetchRel uint8CtEqCode 0x12 = some (.alu .add a1 x0 a0, 2) := by decide
theorem u8e_at_14 : fetchRel uint8CtEqCode 0x14 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem u8e_at_16 : fetchRel uint8CtEqCode 0x16 = some (.auipc ra 0x0, 4) := by decide
theorem u8e_at_1a : fetchRel uint8CtEqCode 0x1A = some (.jalr ra ra 0x6A, 4) := by decide
theorem u8e_at_1e : fetchRel uint8CtEqCode 0x1E = some (.load .lw (9 : Fin 32) sp 0x4, 2) := by decide
theorem u8e_at_20 : fetchRel uint8CtEqCode 0x20 = some (.load .lw (18 : Fin 32) sp 0x8, 2) := by decide
theorem u8e_at_22 : fetchRel uint8CtEqCode 0x22 = some (.load .lw (19 : Fin 32) sp 0xC, 2) := by decide
theorem u8e_at_24 : fetchRel uint8CtEqCode 0x24 = some (.load .lw (20 : Fin 32) sp 0x10, 2) := by decide
theorem u8e_at_26 : fetchRel uint8CtEqCode 0x26 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem u8e_at_28 : fetchRel uint8CtEqCode 0x28 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem u8e_at_2a : fetchRel uint8CtEqCode 0x2A = some (.auipc ra 0x0, 4) := by decide
theorem u8e_at_2e : fetchRel uint8CtEqCode 0x2E = some (.jalr ra ra 0x56, 4) := by decide
theorem u8e_at_32 : fetchRel uint8CtEqCode 0x32 = some (.load .lw a2 sp 0x4, 2) := by decide
theorem u8e_at_34 : fetchRel uint8CtEqCode 0x34 = some (.load .lw a3 sp 0x8, 2) := by decide
theorem u8e_at_36 : fetchRel uint8CtEqCode 0x36 = some (.load .lw (8 : Fin 32) sp 0xC, 2) := by decide
theorem u8e_at_38 : fetchRel uint8CtEqCode 0x38 = some (.load .lw (21 : Fin 32) sp 0x10, 2) := by decide
theorem u8e_at_3a : fetchRel uint8CtEqCode 0x3A = some (.alu .add a0 x0 (9 : Fin 32), 2) := by decide
theorem u8e_at_3c : fetchRel uint8CtEqCode 0x3C = some (.alu .add a1 x0 (18 : Fin 32), 2) := by decide
theorem u8e_at_3e : fetchRel uint8CtEqCode 0x3E = some (.auipc ra 0xFFFFC000, 4) := by decide
theorem u8e_at_42 : fetchRel uint8CtEqCode 0x42 = some (.jalr ra ra 0xFFFFFCA8, 4) := by decide
theorem u8e_at_46 : fetchRel uint8CtEqCode 0x46 = some (.aluImm .and (9 : Fin 32) a0 0xFF, 4) := by decide
theorem u8e_at_4a : fetchRel uint8CtEqCode 0x4A = some (.alu .add a0 x0 (19 : Fin 32), 2) := by decide
theorem u8e_at_4c : fetchRel uint8CtEqCode 0x4C = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem u8e_at_4e : fetchRel uint8CtEqCode 0x4E = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem u8e_at_52 : fetchRel uint8CtEqCode 0x52 = some (.jalr ra ra 0x490, 4) := by decide
theorem u8e_at_56 : fetchRel uint8CtEqCode 0x56 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem u8e_at_5a : fetchRel uint8CtEqCode 0x5A = some (.alu .and (9 : Fin 32) (9 : Fin 32) a0, 2) := by decide
theorem u8e_at_5c : fetchRel uint8CtEqCode 0x5C = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem u8e_at_5e : fetchRel uint8CtEqCode 0x5E = some (.alu .add a1 x0 (21 : Fin 32), 2) := by decide
theorem u8e_at_60 : fetchRel uint8CtEqCode 0x60 = some (.auipc ra 0xFFFEF000, 4) := by decide
theorem u8e_at_64 : fetchRel uint8CtEqCode 0x64 = some (.jalr ra ra 0x47E, 4) := by decide
theorem u8e_at_68 : fetchRel uint8CtEqCode 0x68 = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem u8e_at_6c : fetchRel uint8CtEqCode 0x6C = some (.alu .and a0 a0 (9 : Fin 32), 2) := by decide
theorem u8e_at_6e : fetchRel uint8CtEqCode 0x6E = some (.load .lw ra sp 0x2C, 2) := by decide
theorem u8e_at_70 : fetchRel uint8CtEqCode 0x70 = some (.load .lw (8 : Fin 32) sp 0x28, 2) := by decide
theorem u8e_at_72 : fetchRel uint8CtEqCode 0x72 = some (.load .lw (9 : Fin 32) sp 0x24, 2) := by decide
theorem u8e_at_74 : fetchRel uint8CtEqCode 0x74 = some (.load .lw (18 : Fin 32) sp 0x20, 2) := by decide
theorem u8e_at_76 : fetchRel uint8CtEqCode 0x76 = some (.load .lw (19 : Fin 32) sp 0x1C, 2) := by decide
theorem u8e_at_78 : fetchRel uint8CtEqCode 0x78 = some (.load .lw (20 : Fin 32) sp 0x18, 2) := by decide
theorem u8e_at_7a : fetchRel uint8CtEqCode 0x7A = some (.load .lw (21 : Fin 32) sp 0x14, 2) := by decide
theorem u8e_at_7c : fetchRel uint8CtEqCode 0x7C = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem u8e_at_7e : fetchRel uint8CtEqCode 0x7E = some (.jalr x0 ra 0x0, 2) := by decide
theorem psc_at_0 : fetchRel p256ScalarCtEqCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem psc_at_2 : fetchRel p256ScalarCtEqCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem psc_at_4 : fetchRel p256ScalarCtEqCode 0x4 = some (.auipc ra 0x0, 4) := by decide
theorem psc_at_8 : fetchRel p256ScalarCtEqCode 0x8 = some (.jalr ra ra 0xFFFFFB5A, 4) := by decide
theorem psc_at_c : fetchRel p256ScalarCtEqCode 0xC = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem psc_at_10 : fetchRel p256ScalarCtEqCode 0x10 = some (.load .lw ra sp 0xC, 2) := by decide
theorem psc_at_12 : fetchRel p256ScalarCtEqCode 0x12 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem psc_at_14 : fetchRel p256ScalarCtEqCode 0x14 = some (.auipc (6 : Fin 32) 0xFFFFC000, 4) := by decide
theorem psc_at_18 : fetchRel p256ScalarCtEqCode 0x18 = some (.jalr x0 (6 : Fin 32) 0xFFFFF92A, 4) := by decide
end

theorem split8_out {M : Word → BitVec 8} {out p x : Word} (hx : Sep out 16 x 1) : split8Mem M out p x = M x := by
  simp only [split8Mem]
  rw [memStore32_get_sep (a := out + 0xC) (hx.sub (c := 0xC) (l := 4) (by decide)),
    memStore32_get_sep (a := out + 8) (hx.sub (c := 8) (l := 4) (by decide)),
    memStore32_get_sep (a := out + 4) (hx.sub (c := 4) (l := 4) (by decide)),
    memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)]

theorem split8_ld (M : Word → BitVec 8) (out p : Word) :
    memLoad32 (split8Mem M out p) out = p ∧ memLoad32 (split8Mem M out p) (out + 4) = 8 ∧
    memLoad32 (split8Mem M out p) (out + 8) = p + 0x20 ∧ memLoad32 (split8Mem M out p) (out + 0xC) = 0 := by
  have s : ∀ c d : Nat, c + 4 ≤ d ∨ d + 4 ≤ c → d + 4 ≤ 2 ^ 32 → c + 4 ≤ 2 ^ 32 →
      Sep (out + BitVec.ofNat 32 c) 4 (out + BitVec.ofNat 32 d) 4 := fun c d h h1 h2 =>
    sep_offsets out (c := c) (n := 4) (d := d) (k := 4) h h2 h1
  simp only [split8Mem]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [memLoad32_store32_sep (a := out + 0xC) (b := out) (by have := s 0xC 0 (.inr (by decide)) (by decide) (by decide); rwa [add_ofNat_zero] at this),
      memLoad32_store32_sep (a := out + 8) (b := out) (by have := s 8 0 (.inr (by decide)) (by decide) (by decide); rwa [add_ofNat_zero] at this),
      memLoad32_store32_sep (a := out + 4) (b := out) (by have := s 4 0 (.inr (by decide)) (by decide) (by decide); rwa [add_ofNat_zero] at this),
      memLoad32_store32_same]
  · rw [memLoad32_store32_sep (a := out + 0xC) (b := out + 4) (s 0xC 4 (.inr (by decide)) (by decide) (by decide)),
      memLoad32_store32_sep (a := out + 8) (b := out + 4) (s 8 4 (.inr (by decide)) (by decide) (by decide)),
      memLoad32_store32_same]
  · rw [memLoad32_store32_sep (a := out + 0xC) (b := out + 8) (s 0xC 8 (.inr (by decide)) (by decide) (by decide)),
      memLoad32_store32_same]
  · rw [memLoad32_store32_same]

section
set_option maxRecDepth 20000
theorem u8eSave_end : blockEnd uint8CtEqCode 2 (saveBlock ucePs) = some 0x10 := by decide
theorem u8eMov1_end : blockEnd uint8CtEqCode 0x10 uceMov1 = some 0x16 := by decide
theorem u8eLd1_end : blockEnd uint8CtEqCode 0x1E uceLd1 = some 0x2A := by decide
theorem u8eLd2_end : blockEnd uint8CtEqCode 0x32 uceLd2 = some 0x3E := by decide
theorem u8eMid1_end : blockEnd uint8CtEqCode 0x46 uceMid1 = some 0x4E := by decide
theorem u8eMid2_end : blockEnd uint8CtEqCode 0x56 uceMid2 = some 0x60 := by decide
theorem u8eFin_end : blockEnd uint8CtEqCode 0x68 uceFin = some 0x6E := by decide
theorem u8eRestore_end : blockEnd uint8CtEqCode 0x6E (restoreBlock ucePs) = some 0x7C := by decide
end

/-- Where `Uint<8>::ct_eq` runs: its code and its callees', its stack region
of 0x44 bytes below `sp0` (its 0x30-byte frame and `is_zero`'s 0x14 below
it), and the operands at `pa` and `pb`, apart from what each must not touch. -/
structure U8CEEnv (M : Word → BitVec 8) (P sp0 pa pb : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P uint8CtEqCode
  spl : CodeIn M (P + 0x80) splitAt8Code
  lce : CodeIn M (P + 0xFFFFBCE6) limbCtEqCode
  uiz : CodeIn M (P + 0xFFFF12EE) uintRefIsZeroCode
  unz : CodeIn M (P + 0xFFFF12EE + 0x1A) uintRefIsNonzeroCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x44 ≤ sp0.toNat
  hpa : pa.toNat % 4 = 0
  hpb : pb.toNat % 4 = 0
  sRC : Sep (sp0 + 0xFFFFFFBC) 0x44 P uint8CtEqCode.length
  sRS : Sep (sp0 + 0xFFFFFFBC) 0x44 (P + 0x80) splitAt8Code.length
  sRL : Sep (sp0 + 0xFFFFFFBC) 0x44 (P + 0xFFFFBCE6) limbCtEqCode.length
  sRZ : Sep (sp0 + 0xFFFFFFBC) 0x44 (P + 0xFFFF12EE) uintRefIsZeroCode.length
  sRN : Sep (sp0 + 0xFFFFFFBC) 0x44 (P + 0xFFFF12EE + 0x1A) uintRefIsNonzeroCode.length
  sAR : Sep pa 32 (sp0 + 0xFFFFFFBC) 0x44
  sBR : Sep pb 32 (sp0 + 0xFFFFFFBC) 0x44

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `Uint<8>::ct_eq`**: 1 when the 8 limbs at `pa` equal
those at `pb`, and 0 otherwise. It restores `sp`, `ra`, and `s0` through
`s5`, and writes only its 0x44-byte stack region. -/
theorem uint8CtEq_correct (m : Machine) {P sp0 pa pb retAddr : Word} (env : U8CEEnv m.mem P sp0 pa pb)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = pa) (ha1 : reg m a1 = pb)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      reg m' a0 = (if ∀ i : Nat, i < 8 → memLoad32 m.mem (pa + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (pb + BitVec.ofNat 32 (4 * i)) then 1 else 0) ∧
      (∀ q, oidKeep q = true → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFBC) 0x44 x 1 → m'.mem x = m.mem x := by
  obtain ⟨R, hR⟩ : ∃ R, sp0 + 0xFFFFFFBC = R := ⟨_, rfl⟩
  have sRC := env.sRC; have sRS := env.sRS; have sRL := env.sRL; have sRZ := env.sRZ; have sRN := env.sRN
  have sAR := env.sAR; have sBR := env.sBR
  rw [hR] at sRC sRS sRL sRZ sRN sAR sBR ⊢
  have hRa : R.toNat % 4 = 0 := by rw [← hR]; exact aligned_add env.hsp (k := 0xFFFFFFBC) (by decide)
  have hRw : R.toNat + 0x44 = sp0.toNat := by
    rw [← hR, BitVec.toNat_add, show (0xFFFFFFBC : Word).toNat = 4294967228 from rfl]
    have := sp0.isLt; have := env.hS; omega
  obtain ⟨F, hF⟩ : ∃ F, R + 0x14 = F := ⟨_, rfl⟩
  have hFsp : sp0 + 0xFFFFFFD0 = F := by rw [← hF, ← hR, BitVec.add_assoc]; rfl
  have eS : F + 0x30 = sp0 := by rw [← hFsp, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add hRa (k := 0x14) (by decide)
  -- offsets in the region
  have inR : ∀ {c : Nat}, c < 0x30 → F + BitVec.ofNat 32 c = R + BitVec.ofNat 32 (0x14 + c) := fun hc => by
    rw [← hF, show (0x14 : Word) = BitVec.ofNat 32 0x14 from rfl, add_ofNat_assoc]
  have sRF : ∀ {b : Word} {k : Nat}, Sep R 0x44 b k → Sep F 0x30 b k := fun h => by
    rw [← hF]; exact h.sub (c := 0x14) (l := 0x30) (by decide)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep R 0x44 b code'.length → (∀ x, Sep R 0x44 x 1 → M' x = m.mem x) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod u8e_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hFsp]
  have slotSep : ∀ o : Word, 0x14 ≤ o.toNat → o.toNat + 4 ≤ 0x30 → Sep (F + o) 4 P uint8CtEqCode.length := fun o h1 h2 => by
    have := (sRF sRC).sub (c := o.toNat) (l := 4) (by omega); rwa [ofNat_toNat_self] at this
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock ucePs) u1 env.cod u8eSave_end (saveBlock_ok _ ucePs _ fun p hp => by
    rw [sp1]
    simp only [ucePs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨fr_al' hFa (by decide), slotSep _ (by decide) (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFD0)) ucePs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep F 0x30 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside ucePs fun p hp => by
      simp only [ucePs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact frm_sep' hx (by decide)
  have hslv : ∀ r o, (r, o) ∈ ucePs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [ucePs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  -- registers no step of the function writes
  have nw : ∀ q : Fin 32, oidKeep q = true → q ≠ ra → q ≠ sp → q.val ∉ [8, 9, 18, 19, 20, 21] → Prop :=
    fun _ _ _ _ _ => True
  have hcS : CodeIn Msv P uint8CtEqCode := cIn env.cod sRC (fun x hx => frSv x (sRF hx))
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp2 : reg m2 sp = F := by rw [u2.regs, sp1]
  obtain ⟨m3, c3, u3⟩ := St.block uceMov1 u2.self hcS u8eMov1_end (by simp [BlockOk, BInstr.ok, uceMov1])
  simp only [runBlock, BInstr.run, uceMov1] at u3
  have v3 : reg m3 8 = pb ∧ reg m3 a1 = pa ∧ reg m3 a0 = F + 4 ∧ reg m3 sp = F := by
    rw [u3.regs, u3.regs, u3.regs, u3.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [r2 a1 (by decide), r2 a0 (by decide), r2 0 (by decide), hz, ha1, ha0, sp2, ev_add, ev_add, zw, zw]
    exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨v38, v3a1, v3a0, v3sp⟩ := v3
  have k3 : ∀ q, q ≠ 8 → q ≠ a1 → q ≠ a0 → q ≠ sp → reg m3 q = reg m q := fun q h8 h1 h0 hs => by
    rw [u3.regs, updz (by simp [upd]) h0, updz (by simp [upd]) h1, updz u2.self.zero h8, r2 q hs]
  have hSp : CodeIn Msv (P + 0x80) splitAt8Code := cIn env.spl sRS (fun x hx => frSv x (sRF hx))
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.self.callRa hcS u8e_at_16 u8e_at_1a (cb := P + 0x80)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x80 (by decide))
  have r4 := PEnv.reg1 regs4 u3.self.zero
  have hF4 : F + 4 = F + BitVec.ofNat 32 4 := rfl
  have sOut : Sep (F + 4) 16 (P + 0x80) splitAt8Code.length := by rw [hF4]; exact (sRF sRS).sub (by decide)
  obtain ⟨m5, c5, pc5, mem5, k5⟩ := splitAt8_correct m4 (out := F + 4) (p := pa) (by rw [mem4]; exact hSp) pc4
    (by rw [r4 a0 (by decide), v3a0]) (by rw [r4 a1 (by decide), v3a1]) (by rw [hF4]; exact aligned_add hFa (by decide))
    sOut (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP 0x1E (by decide)))
  rw [mem4] at mem5
  -- the first split's result
  obtain ⟨l0, l1, l2, l3⟩ := split8_ld Msv (F + 4) pa
  have hc5 : CodeIn (split8Mem Msv (F + 4) pa) P uint8CtEqCode := fun i hi => by
    rw [split8_out (by rw [hF4]; exact ((sRF sRC).subR (c := i) (l := 1) (by omega)).sub (by decide))]
    exact hcS i hi
  have u5 : St (split8Mem Msv (F + 4) pa) P m5 0x1E (reg m5) := ⟨by rw [pc5], mem5, fun _ => rfl⟩
  have K5 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ ra → reg m5 q = reg m3 q := fun q h2 h3 hr => by rw [k5 q h2 h3, r4 q hr]
  have sp5 : reg m5 sp = F := by rw [K5 sp (by decide) (by decide) (by decide), v3sp]
  have hal : ∀ c : Word, c.toNat % 4 = 0 → (reg m5 sp + c).toNat % 4 = 0 := fun c hc => by
    rw [sp5]; exact fr_al' hFa hc
  obtain ⟨m6, c6, u6⟩ := St.block uceLd1 u5 hc5 u8eLd1_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, uceLd1, upd_app, ↓reduceIte, and_true]
    exact ⟨hal 4 (by decide), hal 8 (by decide), hal 0xC (by decide), hal 0x10 (by decide)⟩)
  simp only [runBlock, BInstr.run, uceLd1] at u6
  have e8 : F + 8 = F + 4 + 4 := by rw [BitVec.add_assoc]; rfl
  have eC : F + 0xC = F + 4 + 8 := by rw [BitVec.add_assoc]; rfl
  have e10 : F + 0x10 = F + 4 + 0xC := by rw [BitVec.add_assoc]; rfl
  have v6 : reg m6 9 = pa ∧ reg m6 18 = 8 ∧ reg m6 19 = pa + 0x20 ∧ reg m6 20 = 0 ∧ reg m6 a0 = F + 4 ∧
      reg m6 a1 = pb ∧ reg m6 sp = F := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5]; exact l0
    · rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5, e8]; exact l1
    · rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5, eC]; exact l2
    · rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5, e10]; exact l3
    · rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5, ev_add]
    · rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [K5 8 (by decide) (by decide) (by decide), v38]
      exact zw pb
    · rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp5
  obtain ⟨v69, v618, v619, v620, v6a0, v6a1, v6sp⟩ := v6
  have k6 : ∀ q, q ≠ 9 → q ≠ 18 → q ≠ 19 → q ≠ 20 → q ≠ a0 → q ≠ a1 → reg m6 q = reg m5 q :=
    fun q h9 h18 h19 h20 h0 h1 => by
      rw [u6.regs]
      by_cases hq0 : q.val = 0
      · have : q = 0 := Fin.ext hq0
        subst this; simp [upd]; exact u5.zero.symm
      simp only [upd_app, hq0, h9, h18, h19, h20, h0, h1, ite_false]
  have hSp5 : CodeIn (split8Mem Msv (F + 4) pa) (P + 0x80) splitAt8Code := fun i hi => by
    rw [split8_out (by rw [hF4]; exact ((sRF sRS).subR (c := i) (l := 1) (by omega)).sub (by decide))]
    exact hSp i hi
  obtain ⟨m7, c7, pc7, mem7, regs7⟩ := u6.self.callRa hc5 u8e_at_2a u8e_at_2e (cb := P + 0x80)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x80 (by decide))
  have r7 := PEnv.reg1 regs7 u6.self.zero
  obtain ⟨m8, c8, pc8, mem8, k8⟩ := splitAt8_correct m7 (out := F + 4) (p := pb) (by rw [mem7]; exact hSp5) pc7
    (by rw [r7 a0 (by decide), v6a0]) (by rw [r7 a1 (by decide), v6a1]) (by rw [hF4]; exact aligned_add hFa (by decide))
    sOut (by rw [regs7]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP 0x32 (by decide)))
  rw [mem7] at mem8
  obtain ⟨l0', l1', l2', l3'⟩ := split8_ld (split8Mem Msv (F + 4) pa) (F + 4) pb
  have outF4 : ∀ x, Sep R 0x44 x 1 → Sep (F + 4) 16 x 1 := fun x hx => by
    rw [hF4]; exact (sRF hx).sub (by decide)
  have M2out : ∀ x, Sep R 0x44 x 1 → split8Mem (split8Mem Msv (F + 4) pa) (F + 4) pb x = m.mem x := fun x hx => by
    rw [split8_out (outF4 x hx), split8_out (outF4 x hx), frSv x (sRF hx)]
  obtain ⟨M2, hM2⟩ : ∃ M2, split8Mem (split8Mem Msv (F + 4) pa) (F + 4) pb = M2 := ⟨_, rfl⟩
  rw [hM2] at mem8 l0' l1' l2' l3' M2out
  have hc8 : CodeIn M2 P uint8CtEqCode := fun i hi => by rw [M2out _ (sRC.subR (c := i) (l := 1) (by omega))]; exact env.cod i hi
  have u8 : St M2 P m8 0x32 (reg m8) := ⟨by rw [pc8], mem8, fun _ => rfl⟩
  have K8 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ ra → reg m8 q = reg m6 q := fun q h2 h3 hr => by rw [k8 q h2 h3, r7 q hr]
  have sp8 : reg m8 sp = F := by rw [K8 sp (by decide) (by decide) (by decide), v6sp]
  have hal8 : ∀ c : Word, c.toNat % 4 = 0 → (reg m8 sp + c).toNat % 4 = 0 := fun c hc => by
    rw [sp8]; exact fr_al' hFa hc
  obtain ⟨m9, c9, u9⟩ := St.block uceLd2 u8 hc8 u8eLd2_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, uceLd2, upd_app, ↓reduceIte, and_true]
    exact ⟨hal8 4 (by decide), hal8 8 (by decide), hal8 0xC (by decide), hal8 0x10 (by decide)⟩)
  simp only [runBlock, BInstr.run, uceLd2] at u9
  have v9 : reg m9 a2 = pb ∧ reg m9 a3 = 8 ∧ reg m9 8 = pb + 0x20 ∧ reg m9 21 = 0 ∧ reg m9 a0 = pa ∧
      reg m9 a1 = 8 ∧ reg m9 sp = F ∧ reg m9 19 = pa + 0x20 ∧ reg m9 20 = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp8]; exact l0'
    · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp8, e8]; exact l1'
    · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp8, eC]; exact l2'
    · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp8, e10]; exact l3'
    · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [K8 9 (by decide) (by decide) (by decide), v69]; exact zw pa
    · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [K8 18 (by decide) (by decide) (by decide), v618]; exact zw _
    · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp8
    · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [K8 19 (by decide) (by decide) (by decide), v619]
    · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [K8 20 (by decide) (by decide) (by decide), v620]
  obtain ⟨v9a2, v9a3, v98, v921, v9a0, v9a1, v9sp, v919, v920⟩ := v9
  have k9 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ 8 → q ≠ 21 → q ≠ a0 → q ≠ a1 → reg m9 q = reg m8 q :=
    fun q h2 h3 h8 h21 h0 h1 => by
      rw [u9.regs]
      by_cases hq0 : q.val = 0
      · have : q = 0 := Fin.ext hq0
        subst this; simp [upd]; exact u8.zero.symm
      simp only [upd_app, hq0, h2, h3, h8, h21, h0, h1, ite_false]
  -- the limbs compared
  have hLc : CodeIn M2 (P + 0xFFFFBCE6) limbCtEqCode := fun i hi => by
    rw [M2out _ (sRL.subR (c := i) (l := 1) (by omega))]; exact env.lce i hi
  obtain ⟨m10, c10, pc10, mem10, regs10⟩ := u9.self.callRa hc8 u8e_at_3e u8e_at_42 (cb := P + 0xFFFFBCE6)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFBCE6 (by decide))
  have r10 := PEnv.reg1 regs10 u9.self.zero
  obtain ⟨m11, c11, pc11, a011, k11, mem11⟩ := limbCtEq_correct m10 (p := pa) (q := pb) (n := 8) (n' := 8)
    (retAddr := P + BitVec.ofNat 32 0x46) (even_at P env.hP 0xFFFFBCE6 (by decide)) (by rw [mem10]; exact hLc) pc10
    (by rw [r10 a0 (by decide), v9a0]) (by rw [r10 a1 (by decide), v9a1]; rfl) (by rw [r10 a2 (by decide), v9a2])
    (by rw [r10 a3 (by decide), v9a3]; rfl) (by decide) (by decide) env.hpa env.hpb
    (by rw [regs10]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP 0x46 (by decide)))
  rw [mem10] at mem11 a011
  have eLim : ∀ b : Word, Sep b 32 R 0x44 → ∀ i : Nat, i < 8 →
      memLoad32 M2 (b + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (b + BitVec.ofNat 32 (4 * i)) :=
    fun b hb i hi => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact M2out _ (hb.symm.subR (c := 4 * i + j) (l := 1) (by omega))
  have a011' : reg m11 a0 = if ∀ i : Nat, i < 8 → memLoad32 m.mem (pa + BitVec.ofNat 32 (4 * i)) =
      memLoad32 m.mem (pb + BitVec.ofNat 32 (4 * i)) then 1 else 0 := by
    rw [a011]
    by_cases h : ∀ i : Nat, i < 8 → memLoad32 m.mem (pa + BitVec.ofNat 32 (4 * i)) =
      memLoad32 m.mem (pb + BitVec.ofNat 32 (4 * i))
    · rw [ite_eq_left (show 8 = 8 ∧ ∀ i : Nat, i < 8 → memLoad32 M2 (pa + BitVec.ofNat 32 (4 * i)) =
        memLoad32 M2 (pb + BitVec.ofNat 32 (4 * i)) from ⟨rfl, fun i hi => by rw [eLim pa sAR i hi, eLim pb sBR i hi]; exact h i hi⟩),
        ite_eq_left h]
    · rw [ite_eq_right (show ¬ (8 = 8 ∧ ∀ i : Nat, i < 8 → memLoad32 M2 (pa + BitVec.ofNat 32 (4 * i)) =
        memLoad32 M2 (pb + BitVec.ofNat 32 (4 * i))) from fun hh => h (fun i hi => by
          rw [← eLim pa sAR i hi, ← eLim pb sBR i hi]; exact hh.2 i hi)), ite_eq_right h]
  have rIs : ∀ c : Nat, (if ∀ i : Nat, i < c → memLoad32 m.mem (pa + BitVec.ofNat 32 (4 * i)) =
      memLoad32 m.mem (pb + BitVec.ofNat 32 (4 * i)) then (1 : Word) else 0).toNat ≤ 1 := fun c => by
    split <;> decide
  -- the saved registers' slots, above `is_zero`'s 0x14 bytes
  have slot : ∀ {Mx : Word → BitVec 8}, (∀ x, Sep R 0x14 x 1 → Mx x = M2 x) →
      ∀ r o, (r, o) ∈ ucePs → memLoad32 Mx (F + o) = reg m r := fun {Mx} hMx r o h => by
    have ho : 0x14 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x30 := by
      simp only [ucePs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    rw [← hslv r o h]
    apply memLoad32_congr; intro j hj
    have e : F + o + BitVec.ofNat 32 j = R + BitVec.ofNat 32 (0x14 + o.toNat + j) := by
      conv => lhs; rw [← ofNat_toNat_self o]
      rw [← hF, show (0x14 : Word) = BitVec.ofNat 32 0x14 from rfl, add_ofNat_assoc, add_ofNat_assoc, Nat.add_assoc]
    have e2 : F + o + BitVec.ofNat 32 j = F + 4 + BitVec.ofNat 32 (o.toNat + j - 4) := by
      conv => lhs; rw [← ofNat_toNat_self o]
      rw [hF4, add_ofNat_assoc, add_ofNat_assoc, show 4 + (o.toNat + j - 4) = o.toNat + j by omega]
    have sR : Sep R 0x14 (F + o + BitVec.ofNat 32 j) 1 := by
      have := sep_offsets R (c := 0) (n := 0x14) (d := 0x14 + o.toNat + j) (k := 1) (.inl (by omega)) (by omega)
        (by omega)
      rw [add_ofNat_zero] at this; rw [e]; exact this
    have sS : Sep (F + 4) 16 (F + o + BitVec.ofNat 32 j) 1 := by
      have := sep_offsets (F + 4) (c := 0) (n := 16) (d := o.toNat + j - 4) (k := 1) (.inl (by omega)) (by omega)
        (by omega)
      rw [add_ofNat_zero] at this; rw [e2]; exact this
    rw [hMx _ sR, ← hM2, split8_out sS, split8_out sS]
  have sp11 : reg m11 sp = F := by
    rw [k11 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r10 sp (by decide),
      k9 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp8]
  have u11 : St M2 P m11 0x46 (reg m11) := ⟨by rw [pc11], mem11, fun _ => rfl⟩
  have R11 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ ra → q ≠ 8 → q ≠ 21 →
      reg m11 q = reg m8 q := fun q h0 h1 h2 h3 h4 h5 hr h8 h21 => by
    rw [k11 q h0 h1 h2 h3 h4 h5, r10 q hr, k9 q h2 h3 h8 h21 h0 h1]
  obtain ⟨m12, c12, u12⟩ := St.block uceMid1 u11 hc8 u8eMid1_end (by simp [BlockOk, BInstr.ok, uceMid1])
  simp only [runBlock, BInstr.run, uceMid1] at u12
  have and_ff : ∀ c : Nat, (if c = 0 then (1 : Word) else 0) = aluEval .and (if c = 0 then (1 : Word) else 0) 0xFF :=
    fun c => by split <;> rfl
  have hZ : CodeIn M2 (P + 0xFFFF12EE) uintRefIsZeroCode := fun i hi => by
    rw [M2out _ (sRZ.subR (c := i) (l := 1) (by omega))]; exact env.uiz i hi
  have hN : CodeIn M2 (P + 0xFFFF12EE + 0x1A) uintRefIsNonzeroCode := fun i hi => by
    rw [M2out _ (sRN.subR (c := i) (l := 1) (by omega))]; exact env.unz i hi
  have eR : F + 0xFFFFFFEC = R := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero R
  have sZ0 : Sep R 0x14 (P + 0xFFFF12EE) uintRefIsZeroCode.length := by
    have := sRZ.sub (c := 0) (l := 0x14) (by decide); rwa [add_ofNat_zero] at this
  have sN0 : Sep R 0x14 (P + 0xFFFF12EE + 0x1A) uintRefIsNonzeroCode.length := by
    have := sRN.sub (c := 0) (l := 0x14) (by decide); rwa [add_ofNat_zero] at this
  have v12 : reg m12 9 = aluEval .and (reg m11 a0) 0xFF ∧ reg m12 a0 = pa + 0x20 ∧ reg m12 a1 = 0 ∧ reg m12 sp = F := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [u12.regs] <;> simp +decide only [upd_app, ↓reduceIte]
    · rw [R11 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        K8 19 (by decide) (by decide) (by decide), v619]; exact zw _
    · rw [R11 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        K8 20 (by decide) (by decide) (by decide), v620]; rfl
    · exact sp11
  obtain ⟨v129, v12a0, v12a1, v12sp⟩ := v12
  obtain ⟨m13, c13, pc13, mem13, regs13⟩ := u12.self.callRa hc8 u8e_at_4e u8e_at_52 (cb := P + 0xFFFF12EE)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFF12EE (by decide))
  have r13 := PEnv.reg1 regs13 u12.self.zero
  obtain ⟨m14, c14, pc14, sp14, a014, k14, f14⟩ := uintRefIsZero_correct m13 (ptr := pa + 0x20) (len := 0) (sp0 := F)
    (retAddr := P + BitVec.ofNat 32 0x56) (even_at P env.hP 0xFFFF12EE (by decide)) (by rw [mem13]; exact hZ)
    (by rw [mem13]; exact hN) pc13 (by rw [r13 sp (by decide), v12sp]) hFa
    (by rw [r13 a0 (by decide), v12a0]) (by rw [r13 a1 (by decide), v12a1]; rfl) (by decide)
    (aligned_add env.hpa (by decide)) (by rw [eR]; exact sZ0) (by rw [eR]; exact sN0)
    (fun i hi => absurd hi (by omega)) (by rw [regs13]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P env.hP 0x56 (by decide)))
  rw [mem13, eR] at f14
  have sub14 : ∀ {b : Word} {k : Nat}, Sep R 0x44 b k → Sep R 0x14 b k := fun h => by
    have := h.sub (c := 0) (l := 0x14) (by decide); rwa [add_ofNat_zero] at this
  have hc14 : CodeIn m14.mem P uint8CtEqCode := fun i hi => by
    rw [f14 _ (sub14 (sRC.subR (c := i) (l := 1) (by omega)))]
    exact hc8 i hi
  have u14 : St m14.mem P m14 0x56 (reg m14) := ⟨by rw [pc14], rfl, fun _ => rfl⟩
  have R14 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ ra → reg m14 q = reg m12 q := fun q h0 h1 h2 h3 hr => by
    rw [k14 q h0 h1 h2 h3, r13 q hr]
  obtain ⟨m15, c15, u15⟩ := St.block uceMid2 u14 hc14 u8eMid2_end (by simp [BlockOk, BInstr.ok, uceMid2])
  simp only [runBlock, BInstr.run, uceMid2] at u15
  have r12 : ∀ q, q ≠ 9 → q ≠ a0 → q ≠ a1 → reg m12 q = reg m11 q := fun q h9 h0 h1 => by
    rw [u12.regs]
    by_cases hq0 : q.val = 0
    · have : q = 0 := Fin.ext hq0
      subst this; simp [upd]; exact u11.zero.symm
    simp only [upd_app, hq0, h9, h0, h1, ite_false]
  have v15 : reg m15 9 = aluEval .and (aluEval .and (reg m11 a0) 0xFF) (aluEval .and 1 0xFF) ∧
      reg m15 a0 = pb + 0x20 ∧ reg m15 a1 = 0 ∧ reg m15 sp = F := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [u15.regs] <;> simp +decide only [upd_app, ↓reduceIte]
    · rw [R14 9 (by decide) (by decide) (by decide) (by decide) (by decide), v129, a014]
      rw [ite_eq_left (fun i hi => absurd hi (Nat.not_lt_zero i))]
    · rw [R14 8 (by decide) (by decide) (by decide) (by decide) (by decide), r12 8 (by decide) (by decide) (by decide),
        k11 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r10 8 (by decide), v98]
      exact zw _
    · rw [R14 21 (by decide) (by decide) (by decide) (by decide) (by decide), r12 21 (by decide) (by decide) (by decide),
        k11 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r10 21 (by decide), v921]; rfl
    · rw [R14 sp (by decide) (by decide) (by decide) (by decide) (by decide), v12sp]
  obtain ⟨v159, v15a0, v15a1, v15sp⟩ := v15
  have r15 : ∀ q, q ≠ 9 → q ≠ a0 → q ≠ a1 → reg m15 q = reg m14 q := fun q h9 h0 h1 => by
    rw [u15.regs]
    by_cases hq0 : q.val = 0
    · have : q = 0 := Fin.ext hq0
      subst this; simp [upd]; exact u14.zero.symm
    simp only [upd_app, hq0, h9, h0, h1, ite_false]
  have hZ14 : CodeIn m14.mem (P + 0xFFFF12EE) uintRefIsZeroCode := fun i hi => by
    rw [f14 _ (sub14 (sRZ.subR (c := i) (l := 1) (by omega)))]; exact hZ i hi
  have hN14 : CodeIn m14.mem (P + 0xFFFF12EE + 0x1A) uintRefIsNonzeroCode := fun i hi => by
    rw [f14 _ (sub14 (sRN.subR (c := i) (l := 1) (by omega)))]; exact hN i hi
  obtain ⟨m16, c16, pc16, mem16, regs16⟩ := u15.self.callRa hc14 u8e_at_60 u8e_at_64 (cb := P + 0xFFFF12EE)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFF12EE (by decide))
  have r16 := PEnv.reg1 regs16 u15.self.zero
  obtain ⟨m17, c17, pc17, sp17, a017, k17, f17⟩ := uintRefIsZero_correct m16 (ptr := pb + 0x20) (len := 0) (sp0 := F)
    (retAddr := P + BitVec.ofNat 32 0x68) (even_at P env.hP 0xFFFF12EE (by decide)) (by rw [mem16]; exact hZ14)
    (by rw [mem16]; exact hN14) pc16 (by rw [r16 sp (by decide), v15sp]) hFa
    (by rw [r16 a0 (by decide), v15a0]) (by rw [r16 a1 (by decide), v15a1]; rfl) (by decide)
    (aligned_add env.hpb (by decide)) (by rw [eR]; exact sZ0) (by rw [eR]; exact sN0)
    (fun i hi => absurd hi (by omega)) (by rw [regs16]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P env.hP 0x68 (by decide)))
  rw [mem16, eR] at f17
  -- memory after the second call agrees with `M2` outside `is_zero`'s bytes
  have f17' : ∀ x, Sep R 0x14 x 1 → m17.mem x = M2 x := fun x hx => by rw [f17 x hx, f14 x hx]
  have hc17 : CodeIn m17.mem P uint8CtEqCode := fun i hi => by
    rw [f17' _ (sub14 (sRC.subR (c := i) (l := 1) (by omega)))]; exact hc8 i hi
  have u17 : St m17.mem P m17 0x68 (reg m17) := ⟨by rw [pc17], rfl, fun _ => rfl⟩
  obtain ⟨m18, c18, u18⟩ := St.block uceFin u17 hc17 u8eFin_end (by simp [BlockOk, BInstr.ok, uceFin])
  simp only [runBlock, BInstr.run, uceFin] at u18
  have R17 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ ra → reg m17 q = reg m15 q := fun q h0 h1 h2 h3 hr => by
    rw [k17 q h0 h1 h2 h3, r16 q hr]
  have sp18 : reg m18 sp = F := by
    rw [u18.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [R17 sp (by decide) (by decide) (by decide) (by decide) (by decide), v15sp]
  have va18 : reg m18 a0 = if ∀ i : Nat, i < 8 → memLoad32 m.mem (pa + BitVec.ofNat 32 (4 * i)) =
      memLoad32 m.mem (pb + BitVec.ofNat 32 (4 * i)) then 1 else 0 := by
    rw [u18.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [a017, ite_eq_left (fun i hi => absurd hi (Nat.not_lt_zero i)),
      R17 9 (by decide) (by decide) (by decide) (by decide) (by decide), v159, a011']
    split <;> rfl
  obtain ⟨m19, c19, u19⟩ := St.block (restoreBlock ucePs) u18.self hc17 u8eRestore_end
    (restoreBlock_ok _ F ucePs (reg m18) sp18 (by decide) fun p hp => by
      simp only [ucePs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact fr_al' hFa (by decide))
  simp only [restoreBlock_run m17.mem F ucePs (reg m18) sp18 (by decide)] at u19
  obtain ⟨m20, d20, u20⟩ := u19.aluImm hc17 u8e_at_7c (off' := 0x7E) (by decide)
  obtain ⟨m21, d21, pc21, mem21, regs21⟩ := u20.jalr hc17 u8e_at_7e
  have hsl := slot f17'
  have rsp19 : restoreRegs m17.mem F (reg m18) ucePs sp = F := by
    rw [restoreRegs_sp _ _ _ _ (by decide)]; exact sp18
  refine ⟨m21, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans
    (c11.trans (c12.trans (c13.trans (c14.trans (c15.trans (c16.trans (c17.trans (c18.trans (c19.trans
    (.cons d20 (.single d21)))))))))))))))))))), ?_, ?_, ?_, fun q hq => ?_, fun x hx => ?_⟩
  · rw [pc21]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
    rw [hsl ra 0x2C (by decide), hra, add_lit_zero, hret]
  · rw [regs21]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp19, ev_add, eS]
  · rw [regs21]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]; exact va18
  · by_cases hs : q = sp
    · subst hs; rw [regs21]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp19, ev_add, eS, hsp]
    have rz : restoreRegs m17.mem F (reg m18) ucePs 0 = 0 := by
      rw [restoreRegs_ne _ _ _ _ _ u18.self.zero (by decide)]; exact u18.self.zero
    by_cases hin : q.val ∈ [1, 8, 9, 18, 19, 20, 21]
    · have h7 : q = ra ∨ q = 8 ∨ q = 9 ∨ q = 18 ∨ q = 19 ∨ q = 20 ∨ q = 21 := by revert hin; revert q; decide
      rcases h7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · rw [regs21]; simp +decide only [upd_app, ↓reduceIte]
        simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
        first
          | exact hsl _ 0x2C (by decide) | exact hsl _ 0x28 (by decide) | exact hsl _ 0x24 (by decide)
          | exact hsl _ 0x20 (by decide) | exact hsl _ 0x1C (by decide) | exact hsl _ 0x18 (by decide)
          | exact hsl _ 0x14 (by decide)
    have key : ∀ q : Fin 32, oidKeep q = true → q.val ∉ [1, 8, 9, 18, 19, 20, 21] → q ≠ sp →
        ∀ r : Fin 32, r.val ∈ [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21] → q ≠ r := by
      decide
    have nq := key q hq hin hs
    rw [regs21, updz rz hs, restoreRegs_ne _ _ _ _ _ u18.self.zero (fun p hp => by
      simp only [ucePs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact (nq _ (by decide)).symm)]
    rw [u18.regs, updz (by simp [upd]) (nq a0 (by decide)), updz u17.zero (nq a0 (by decide)), R17 q (nq a0 (by decide)) (nq a1 (by decide)) (nq a2 (by decide))
      (nq a3 (by decide)) (nq ra (by decide)), r15 q (nq 9 (by decide)) (nq a0 (by decide)) (nq a1 (by decide)),
      R14 q (nq a0 (by decide)) (nq a1 (by decide)) (nq a2 (by decide)) (nq a3 (by decide)) (nq ra (by decide)),
      r12 q (nq 9 (by decide)) (nq a0 (by decide)) (nq a1 (by decide)),
      R11 q (nq a0 (by decide)) (nq a1 (by decide)) (nq a2 (by decide)) (nq a3 (by decide)) (nq a4 (by decide))
        (nq a5 (by decide)) (nq ra (by decide)) (nq 8 (by decide)) (nq 21 (by decide)),
      K8 q (nq a2 (by decide)) (nq a3 (by decide)) (nq ra (by decide)),
      k6 q (nq 9 (by decide)) (nq 18 (by decide)) (nq 19 (by decide)) (nq 20 (by decide)) (nq a0 (by decide))
        (nq a1 (by decide)),
      K5 q (nq a2 (by decide)) (nq a3 (by decide)) (nq ra (by decide)),
      k3 q (nq 8 (by decide)) (nq a1 (by decide)) (nq a0 (by decide)) hs]
  · rw [mem21, f17' x (sub14 hx), M2out x hx]

/-- Where P-256's `Scalar::ct_eq` runs: its code and its
callees', the 0x54 bytes of stack below `sp0`, and the two 32-byte operands. -/
structure P2SEnv (M : Word → BitVec 8) (P sp0 pa pb : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P p256ScalarCtEqCode
  uce : CodeIn M (P + 0xFFFFFB5E) uint8CtEqCode
  spl : CodeIn M (P + 0xFFFFFB5E + 0x80) splitAt8Code
  lce : CodeIn M (P + 0xFFFFFB5E + 0xFFFFBCE6) limbCtEqCode
  uiz : CodeIn M (P + 0xFFFFFB5E + 0xFFFF12EE) uintRefIsZeroCode
  unz : CodeIn M (P + 0xFFFFFB5E + 0xFFFF12EE + 0x1A) uintRefIsNonzeroCode
  bb : CodeIn M (P + 0xFFFFB93E) blackBoxU8Code
  hsp : sp0.toNat % 4 = 0
  hS : 0x54 ≤ sp0.toNat
  hpa : pa.toNat % 4 = 0
  hpb : pb.toNat % 4 = 0
  sGC : Sep (sp0 + 0xFFFFFFAC) 0x54 P p256ScalarCtEqCode.length
  sGU : Sep (sp0 + 0xFFFFFFAC) 0x54 (P + 0xFFFFFB5E) uint8CtEqCode.length
  sGS : Sep (sp0 + 0xFFFFFFAC) 0x54 (P + 0xFFFFFB5E + 0x80) splitAt8Code.length
  sGL : Sep (sp0 + 0xFFFFFFAC) 0x54 (P + 0xFFFFFB5E + 0xFFFFBCE6) limbCtEqCode.length
  sGZ : Sep (sp0 + 0xFFFFFFAC) 0x54 (P + 0xFFFFFB5E + 0xFFFF12EE) uintRefIsZeroCode.length
  sGN : Sep (sp0 + 0xFFFFFFAC) 0x54 (P + 0xFFFFFB5E + 0xFFFF12EE + 0x1A) uintRefIsNonzeroCode.length
  sGB : Sep (sp0 + 0xFFFFFFAC) 0x54 (P + 0xFFFFB93E) blackBoxU8Code.length
  sAG : Sep pa 32 (sp0 + 0xFFFFFFAC) 0x54
  sBG : Sep pb 32 (sp0 + 0xFFFFFFAC) 0x54

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The compiled `<p256::Scalar as ConstantTimeEq>::ct_eq`**
returns 1 when the 8 limbs at `pa` equal the 8 limbs at `pb` and 0
otherwise. -/
theorem p256ScalarCtEq_correct (m : Machine) {P sp0 pa pb retAddr : Word} (env : P2SEnv m.mem P sp0 pa pb)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = pa) (ha1 : reg m a1 = pb)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      reg m' a0 = (if ∀ i : Nat, i < 8 → memLoad32 m.mem (pa + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (pb + BitVec.ofNat 32 (4 * i)) then 1 else 0) ∧
      (∀ q, oidKeep q = true → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFAC) 0x54 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFFAC = G := ⟨_, rfl⟩
  have sGC := env.sGC; have sGU := env.sGU; have sGS := env.sGS; have sGL := env.sGL; have sGZ := env.sGZ
  have sGN := env.sGN; have sGB := env.sGB; have sAG := env.sAG; have sBG := env.sBG
  rw [hG] at sGC sGU sGS sGL sGZ sGN sGB sAG sBG ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFF0 = F := ⟨_, rfl⟩
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add env.hsp (k := 0xFFFFFFF0) (by decide)
  have hFn : 0x44 ≤ F.toNat := by
    rw [← hF, BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 4294967280 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have eW : F + 0xC = G + BitVec.ofNat 32 0x50 := by rw [← hF, ← hG, BitVec.add_assoc, BitVec.add_assoc]; rfl
  have eR : F + 0xFFFFFFBC = G + BitVec.ofNat 32 0 := by rw [← hF, ← hG, BitVec.add_assoc, BitVec.add_assoc]; rfl
  have eS : F + 0x10 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eB : sp0 + 0xFFFFFFFF = G + BitVec.ofNat 32 0x53 := by rw [← hG, BitVec.add_assoc]; rfl
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.aluImm env.cod psc_at_0 (off' := 2) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.sw env.cod psc_at_2 (off' := 4) (by decide) (by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]; exact aligned_add hFa (k := 0xC) (by decide))
  simp +decide only [upd_app, ↓reduceIte] at u2
  rw [ev_add, hsp, hF, eW, hra] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, memStore32 m.mem (G + BitVec.ofNat 32 0x50) retAddr = Ms := ⟨_, rfl⟩
  have frS : ∀ x, Sep G 0x54 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs]; exact memStore32_get_sep (hx.sub (c := 0x50) (l := 4) (by decide))
  have cS : ∀ {M : Word → BitVec 8} {b : Word} {code : List Nat}, (∀ x, Sep G 0x54 x 1 → M x = m.mem x) →
      CodeIn m.mem b code → Sep G 0x54 b code.length → CodeIn M b code :=
    fun hM h hs i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact h i hi
  rw [hMs] at u2
  have hc2 := cS frS env.cod sGC
  obtain ⟨n3, c3, pc3, mem3, regs3⟩ := u2.self.callRa hc2 psc_at_4 psc_at_8 (cb := P + 0xFFFFFB5E)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFFB5E (by decide))
  have r3 := PEnv.reg1 regs3 u2.self.zero
  have k2 : ∀ q, q ≠ sp → reg n2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp3 : reg n3 sp = F := by rw [r3 sp (by decide), u2.regs]; simp +decide only [upd_app, ↓reduceIte]
  have inR : ∀ {b : Word} {l : Nat}, Sep G 0x54 b l → Sep (F + 0xFFFFFFBC) 0x44 b l := fun h => by
    rw [eR]; exact h.sub (c := 0) (l := 0x44) (by decide)
  have inR' : ∀ {b : Word} {k : Nat}, Sep b k G 0x54 → Sep b k (F + 0xFFFFFFBC) 0x44 := fun h => by
    rw [eR]; exact h.subR (c := 0) (l := 0x44) (by decide)
  have uenv : U8CEEnv n3.mem (P + 0xFFFFFB5E) F pa pb := by
    rw [mem3]
    exact ⟨even_at P env.hP 0xFFFFFB5E (by decide), cS frS env.uce sGU, cS frS env.spl sGS, cS frS env.lce sGL,
      cS frS env.uiz sGZ, cS frS env.unz sGN, hFa, hFn, env.hpa, env.hpb, inR sGU, inR sGS, inR sGL, inR sGZ,
      inR sGN, inR' sAG, inR' sBG⟩
  obtain ⟨n4, c4, pc4, sp4, a04, k4, f4⟩ := uint8CtEq_correct n3 uenv pc3 sp3
    (by rw [r3 a0 (by decide), k2 a0 (by decide), ha0]) (by rw [r3 a1 (by decide), k2 a1 (by decide), ha1])
    (by rw [regs3]; simp +decide [upd]) (even_clear _ (even_at P env.hP (4 + 8) (by decide)))
  rw [mem3] at a04 f4
  have hall : (∀ i : Nat, i < 8 → memLoad32 Ms (pa + BitVec.ofNat 32 (4 * i)) = memLoad32 Ms (pb + BitVec.ofNat 32 (4 * i))) ↔
      (∀ i : Nat, i < 8 → memLoad32 m.mem (pa + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (pb + BitVec.ofNat 32 (4 * i))) := by
    have e : ∀ {p : Word}, Sep p 32 G 0x54 → ∀ i, i < 8 →
        memLoad32 Ms (p + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (p + BitVec.ofNat 32 (4 * i)) :=
      fun h i hi => memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact frS _ (h.sub (c := 4 * i + j) (l := 1) (by omega)).symm
    constructor
    · intro h i hi; rw [← e sAG i hi, ← e sBG i hi]; exact h i hi
    · intro h i hi; rw [e sAG i hi, e sBG i hi]; exact h i hi
  have hc4 : CodeIn n4.mem P p256ScalarCtEqCode := fun i hi => by
    rw [f4 _ ((inR sGC).subR (c := i) (l := 1) (by omega))]; exact hc2 i hi
  have u4 : St n4.mem P n4 0xC (reg n4) := ⟨by rw [pc4], rfl, fun _ => rfl⟩
  obtain ⟨n5, d5, u5⟩ := u4.aluImm hc4 psc_at_c (off' := 0x10) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5.self.lw hc4 psc_at_10 (off' := 0x12) (by decide) (by
    rw [u5.regs, upd_ne (by decide) (by decide), sp4]; exact aligned_add hFa (k := 0xC) (by decide))
  have eRa : memLoad32 n4.mem (G + BitVec.ofNat 32 0x50) = retAddr := by
    rw [memLoad32_congr (M := Ms) (fun j hj => f4 _ (by
      rw [eR, add_ofNat_assoc]; exact sep_offsets G (c := 0) (n := 0x44) (d := 0x50 + j) (k := 1) (.inl (by omega))
        (by decide) (by omega))), ← hMs]
    exact memLoad32_store32_same _ _ _
  have sp5 : reg n5 sp = F := by rw [u5.regs, upd_ne (by decide) (by decide), sp4]
  rw [sp5, eW, eRa] at u6
  obtain ⟨n7, d7, u7⟩ := u6.aluImm hc4 psc_at_12 (off' := 0x14) (by decide)
  obtain ⟨n8, d8, u8⟩ := u7.self.auipc hc4 psc_at_14 (off' := 0x18) (by decide)
  obtain ⟨n9, d9, pc9, mem9, regs9⟩ := u8.self.jalr hc4 psc_at_18
  have pc9' : n9.pc = P + 0xFFFFB93E := by
    rw [pc9, u8.regs]; simp +decide only [upd, ↓reduceIte]
    rw [show P + BitVec.ofNat 32 0x14 + 0xFFFFC000 + 0xFFFFF92A = P + 0xFFFFB93E by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact even_clear _ (even_at P env.hP 0xFFFFB93E (by decide))
  have k9 : ∀ q, q ≠ t1 → q ≠ sp → q ≠ ra → q ≠ a0 → reg n9 q = reg n4 q := fun q h6 hs hr h0 => by
    rw [regs9, u8.regs, upd_ne' h6 u7.self.zero, u7.regs, upd_ne' hs (upd_zero _ _ _), upd_ne' hr u5.self.zero,
      u5.regs, upd_ne' h0 u4.zero]
  have sp9 : reg n9 sp = sp0 := by
    rw [regs9, u8.regs, upd_ne (by decide) (by decide), u7.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [sp5, ev_add, eS]
  have ra9 : reg n9 ra = retAddr := by
    rw [regs9, u8.regs, upd_ne (by decide) (by decide), u7.regs, upd_ne (by decide) (by decide)]
    simp +decide only [upd_app, ↓reduceIte]
  have a09 : reg n9 a0 = aluEval .and (reg n4 a0) 0xFF := by
    rw [regs9, u8.regs, upd_ne (by decide) (by decide), u7.regs, upd_ne (by decide) (by decide),
      upd_ne (by decide) (by decide), u5.regs]
    simp +decide only [upd_app, ↓reduceIte]
  have mG : ∀ x, Sep G 0x54 x 1 → n9.mem x = m.mem x := fun x hx => by
    rw [mem9, f4 x (inR hx), frS x hx]
  obtain ⟨m', c', pc', a0', k', f'⟩ := blackBoxU8_correct n9 (base := P + 0xFFFFB93E) (retAddr := retAddr)
    (cS mG env.bb sGB) pc9' ra9 hret (by rw [sp9, eB]; exact sGB.sub (c := 0x53) (l := 1) (by decide))
  refine ⟨m', .cons d1 (.cons d2 (c3.trans (c4.trans (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 c')))))))),
    pc', by rw [k' sp (by decide), sp9], ?_, fun q hq => ?_, fun x hx => ?_⟩
  · rw [a0', a09, a04]
    by_cases h : ∀ i : Nat, i < 8 → memLoad32 m.mem (pa + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (pb + BitVec.ofNat 32 (4 * i))
    · rw [ite_eq_left (hall.mpr h), ite_eq_left h]; rfl
    · rw [ite_eq_right (fun h' => h (hall.mp h')), ite_eq_right h]; rfl
  · have h0 : q ≠ a0 := fun e => by subst e; revert hq; decide
    have h6 : q ≠ t1 := fun e => by subst e; revert hq; decide
    rw [k' q h0]
    by_cases hs : q = sp
    · subst hs; rw [sp9, hsp]
    by_cases hr : q = ra
    · subst hr; rw [ra9, hra]
    rw [k9 q h6 hs hr h0, k4 q hq, r3 q hr, k2 q hs]
  · rw [f' x (by rw [sp9, eB]; exact hx.sub (c := 0x53) (l := 1) (by decide)), mG x hx]

end C3.RV32
