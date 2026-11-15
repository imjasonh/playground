import C3BootProofs.Proofs.FeIsNeg
import C3BootProofs.Proofs.SliceEq

/-!
# `<FieldElement2625 as ConstantTimeEq>::ct_eq`, as compiled

`ct_eq` writes both field elements' canonical bytes to its stack with the
proved `to_bytes`, and compares the two 32-byte strings with the proved
constant-time `<[u8] as ConstantTimeEq>::ct_eq`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem fce_at_0 : fetchRel feCtEqCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFB0, 2) := by decide
theorem fce_at_2 : fetchRel feCtEqCode 0x2 = some (.store .sw sp ra 0x4C, 2) := by decide
theorem fce_at_4 : fetchRel feCtEqCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x48, 2) := by decide
theorem fce_at_6 : fetchRel feCtEqCode 0x6 = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem fce_at_8 : fetchRel feCtEqCode 0x8 = some (.alu .add a1 x0 a0, 2) := by decide
theorem fce_at_a : fetchRel feCtEqCode 0xA = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem fce_at_c : fetchRel feCtEqCode 0xC = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem fce_at_10 : fetchRel feCtEqCode 0x10 = some (.jalr ra ra 0x8A, 4) := by decide
theorem fce_at_14 : fetchRel feCtEqCode 0x14 = some (.aluImm .add a0 sp 0x28, 2) := by decide
theorem fce_at_16 : fetchRel feCtEqCode 0x16 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem fce_at_18 : fetchRel feCtEqCode 0x18 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem fce_at_1c : fetchRel feCtEqCode 0x1C = some (.jalr ra ra 0x7E, 4) := by decide
theorem fce_at_20 : fetchRel feCtEqCode 0x20 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem fce_at_22 : fetchRel feCtEqCode 0x22 = some (.aluImm .add a1 sp 0x28, 2) := by decide
theorem fce_at_24 : fetchRel feCtEqCode 0x24 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem fce_at_28 : fetchRel feCtEqCode 0x28 = some (.jalr ra ra 0xFFFFFF4E, 4) := by decide
theorem fce_at_2c : fetchRel feCtEqCode 0x2C = some (.load .lw ra sp 0x4C, 2) := by decide
theorem fce_at_2e : fetchRel feCtEqCode 0x2E = some (.load .lw (8 : Fin 32) sp 0x48, 2) := by decide
theorem fce_at_30 : fetchRel feCtEqCode 0x30 = some (.aluImm .add sp sp 0x50, 2) := by decide
theorem fce_at_32 : fetchRel feCtEqCode 0x32 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- The instructions from 0x2 to 0xC: `ra` and `s0` saved, `y` kept in `s0`,
and `to_bytes`'s operands. -/
def fceSave : List BInstr :=
  [.sw sp ra 0x4C, .sw sp (8 : Fin 32) 0x48, .alu .add (8 : Fin 32) x0 a1, .alu .add a1 x0 a0, .aluImm .add a0 sp 0x8]

section
set_option maxRecDepth 20000
theorem fceSave_end : blockEnd feCtEqCode 2 fceSave = some 0xC := by decide
end

/-- Where `ct_eq` runs: its code and its callees', the 0x100 bytes of stack
below `sp0`, and the two field elements' limbs. -/
structure FCEEnv (M : Word → BitVec 8) (P sp0 xp yp : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P feCtEqCode
  tb : CodeIn M (P + 0xFFFFE096) feToBytesCode
  red : CodeIn M (P + 0xFFFFE096 + 0x210) feReduceCode
  cs : CodeIn M (P + 0xFFFFEF72) ctEqSliceCode
  ce : CodeIn M (P + 0xFFFFEF72 + 0xFFFFFFE8) ctEqU8Code
  bb : CodeIn M (P + 0xFFFFEF72 + 0xFFFFE836) blackBoxU8Code
  hsp : sp0.toNat % 4 = 0
  hS : 0x100 ≤ sp0.toNat
  hxp : xp.toNat % 4 = 0
  hyp : yp.toNat % 4 = 0
  sGC : Sep (sp0 + 0xFFFFFF00) 0x100 P feCtEqCode.length
  sGT : Sep (sp0 + 0xFFFFFF00) 0x100 (P + 0xFFFFE096) feToBytesCode.length
  sGR : Sep (sp0 + 0xFFFFFF00) 0x100 (P + 0xFFFFE096 + 0x210) feReduceCode.length
  sGS : Sep (sp0 + 0xFFFFFF00) 0x100 (P + 0xFFFFEF72) ctEqSliceCode.length
  sGE : Sep (sp0 + 0xFFFFFF00) 0x100 (P + 0xFFFFEF72 + 0xFFFFFFE8) ctEqU8Code.length
  sGB : Sep (sp0 + 0xFFFFFF00) 0x100 (P + 0xFFFFEF72 + 0xFFFFE836) blackBoxU8Code.length
  sXG : Sep xp 40 (sp0 + 0xFFFFFF00) 0x100
  sYG : Sep yp 40 (sp0 + 0xFFFFFF00) 0x100

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `<FieldElement2625 as ConstantTimeEq>::ct_eq`**: it
returns 1 when the field elements at `xp` and `yp` have the same canonical
bytes and 0 otherwise, and writes only its 0x100-byte stack region. -/
theorem feCtEq_correct (m : Machine) {P sp0 xp yp retAddr : Word} (env : FCEEnv m.mem P sp0 xp yp)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = xp) (ha1 : reg m a1 = yp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      reg m' a0 = (if feBytesOf m.mem xp = feBytesOf m.mem yp then 1 else 0) ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF00) 0x100 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFF00 = G := ⟨_, rfl⟩
  have sGC := env.sGC; have sGT := env.sGT; have sGR := env.sGR; have sGS := env.sGS; have sGE := env.sGE
  have sGB := env.sGB; have sXG := env.sXG; have sYG := env.sYG
  rw [hG] at sGC sGT sGR sGS sGE sGB sXG sYG ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFB0 = F := ⟨_, rfl⟩
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFF00) (by decide)
  have hGw : G.toNat + 0x100 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFF00 : Word).toNat = 4294967040 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have eGF : G + BitVec.ofNat 32 0xB0 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hFa : F.toNat % 4 = 0 := by rw [← eGF]; exact aligned_add hGa (k := 0xB0) (by decide)
  have hFn : F.toNat = G.toNat + 0xB0 := by rw [← eGF, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have eS : F + 0x50 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0xB0 + k) := fun k => by rw [← eGF, add_ofNat_assoc]
  have eR : F + 0xFFFFFF50 = G + BitVec.ofNat 32 0 := by rw [← eGF, BitVec.add_assoc]; rfl
  have eC : F + 0xFFFFFFDF = G + BitVec.ofNat 32 0x8F := by rw [← eGF, BitVec.add_assoc]; rfl
  have gw : G.toNat + 0x100 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x100 → d + k ≤ 0x100 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
    fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0x100 b code'.length → (∀ y, Sep G 0x100 y 1 → M' y = m.mem y) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have inR : ∀ {b : Word} {l : Nat}, Sep G 0x100 b l → Sep (F + 0xFFFFFF50) 0xB0 b l := fun h => by
    rw [eR]; exact h.sub (c := 0) (l := 0xB0) (by decide)
  have sFk : ∀ {b : Word} {l : Nat} (c k : Nat), c + k ≤ 0x50 → Sep G 0x100 b l →
      Sep (F + BitVec.ofNat 32 c) k b l := fun c k h hs => by rw [eFk]; exact hs.sub (by omega)
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.aluImm env.cod fce_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFB0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨n2, c2, u2⟩ := St.block fceSave u1 env.cod fceSave_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, fceSave, upd_app, ↓reduceIte, and_true]
    rw [ev_add, hsp, hF]
    exact ⟨⟨aligned_add hFa (k := 0x4C) (by decide), sFk 0x4C 4 (by decide) sGC⟩,
      aligned_add hFa (k := 0x48) (by decide), sFk 0x48 4 (by decide) sGC⟩)
  simp only [runBlock, BInstr.run, fceSave] at u2
  simp +decide only [upd_app, ↓reduceIte] at u2
  rw [ev_add, hsp, hF, hra] at u2
  obtain ⟨Ms, hMs⟩ : ∃ Ms, memStore32 (memStore32 m.mem (F + 0x4C) retAddr) (F + 0x48) (reg m 8) = Ms := ⟨_, rfl⟩
  rw [hMs] at u2
  have frS : ∀ x, Sep G 0x100 x 1 → Ms x = m.mem x := fun x hx => by
    rw [← hMs, memStore32_get_sep (a := F + 0x48) (sFk 0x48 4 (by decide) hx),
      memStore32_get_sep (a := F + 0x4C) (sFk 0x4C 4 (by decide) hx)]
  have hcS := cIn env.cod sGC frS
  have r2 : ∀ q, q.val ≠ 0 → q ≠ sp → q ≠ 8 → q ≠ a1 → q ≠ a0 → reg n2 q = reg m q := fun q hv hs h8 h1 h0 => by
    rw [u2.regs, upd_ne hv h0, upd_ne hv h1, upd_ne hv h8, upd_ne hv hs]
  have sp2 : reg n2 sp = F := by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]
  have s0_2 : reg n2 8 = yp := by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ha1]; exact zw yp
  -- `to_bytes` of `x` into `sp + 0x8`
  obtain ⟨n3, c3, pc3, mem3, regs3⟩ := u2.self.callRa hcS fce_at_c fce_at_10 (cb := P + 0xFFFFE096)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFE096 (by decide))
  have r3 := PEnv.reg1 regs3 u2.self.zero
  have tenv : TBEnv n3.mem (P + 0xFFFFE096) F (F + 0x8) xp := by
    rw [mem3]
    exact ⟨even_at P env.hP 0xFFFFE096 (by decide), cIn env.tb sGT frS, cIn env.red sGR frS, hFa, by omega, env.hxp,
      inR sGT, inR sGR, sFk 8 32 (by decide) sGT,
      by rw [eR, show F + 0x8 = F + BitVec.ofNat 32 8 from rfl, eFk]; exact offs (.inr (by decide)) (by decide) (by decide),
      by rw [eR]; exact sXG.subR (c := 0) (l := 0xB0) (by decide)⟩
  obtain ⟨n4, c4, pc4, sp4, k4, b4, f4⟩ := feToBytes_correct n3 tenv pc3 (by rw [r3 sp (by decide), sp2])
    (by rw [r3 a0 (by decide), u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rfl)
    (by rw [r3 a1 (by decide), u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ha0]; exact zw xp)
    (by rw [regs3]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0xC + 8) (by decide)))
  rw [mem3, show feToBytesOf _ = feBytesOf Ms xp from rfl,
    feBytesOf_congr fun i hi => frS _ (sXG.sub (c := i) (l := 1) (by omega)).symm] at b4
  rw [mem3] at f4
  have n4G : ∀ x, Sep G 0x100 x 1 → n4.mem x = m.mem x := fun x hx => by
    rw [f4 x (inR hx) (sFk 8 32 (by decide) hx), frS x hx]
  have hc4 := cIn env.cod sGC n4G
  have u4 : St n4.mem P n4 0x14 (reg n4) := ⟨by rw [pc4], rfl, fun _ => rfl⟩
  have K4 : ∀ q, tbKeep q = true → q ≠ ra → reg n4 q = reg n2 q := fun q hk hr => by rw [k4 q hk, r3 q hr]
  -- `to_bytes` of `y` into `sp + 0x28`
  obtain ⟨n5, c5, u5⟩ := St.block [.aluImm .add a0 sp 0x28, .alu .add a1 x0 (8 : Fin 32)] u4 hc4 (off' := 0x18)
    (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u5
  obtain ⟨n6, c6, pc6, mem6, regs6⟩ := u5.self.callRa hc4 fce_at_18 fce_at_1c (cb := P + 0xFFFFE096)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFE096 (by decide))
  have r6 := PEnv.reg1 regs6 u5.self.zero
  have sp4' : reg n4 sp = F := by rw [sp4]
  have tenv2 : TBEnv n6.mem (P + 0xFFFFE096) F (F + 0x28) yp := by
    rw [mem6]
    exact ⟨even_at P env.hP 0xFFFFE096 (by decide), cIn env.tb sGT n4G, cIn env.red sGR n4G, hFa, by omega, env.hyp,
      inR sGT, inR sGR, sFk 0x28 32 (by decide) sGT,
      by rw [eR, show F + 0x28 = F + BitVec.ofNat 32 0x28 from rfl, eFk]
         exact offs (.inr (by decide)) (by decide) (by decide),
      by rw [eR]; exact sYG.subR (c := 0) (l := 0xB0) (by decide)⟩
  obtain ⟨n7, c7, pc7, sp7, k7, b7, f7⟩ := feToBytes_correct n6 tenv2 pc6
    (by rw [r6 sp (by decide), u5.regs]; simp +decide only [upd_app, ↓reduceIte]; exact sp4')
    (by rw [r6 a0 (by decide), u5.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp4']; rfl)
    (by rw [r6 a1 (by decide), u5.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [K4 8 (by decide) (by decide), s0_2]; exact zw yp)
    (by rw [regs6]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x18 + 8) (by decide)))
  rw [mem6, show feToBytesOf _ = feBytesOf n4.mem yp from rfl,
    feBytesOf_congr fun i hi => n4G _ (sYG.sub (c := i) (l := 1) (by omega)).symm] at b7
  rw [mem6] at f7
  have n7G : ∀ x, Sep G 0x100 x 1 → n7.mem x = m.mem x := fun x hx => by
    rw [f7 x (inR hx) (sFk 0x28 32 (by decide) hx), n4G x hx]
  have hc7 := cIn env.cod sGC n7G
  have b4' : memBytes n7.mem (F + 0x8) 32 = feBytesOf m.mem xp := by
    rw [← b4]
    exact memBytes_congr fun i hi => f7 _
      (by rw [eR, show F + 0x8 = F + BitVec.ofNat 32 8 from rfl, eFk, add_ofNat_assoc]
          exact offs (.inl (by omega)) (by decide) (by omega))
      (by rw [show F + 0x8 = F + BitVec.ofNat 32 8 from rfl, add_ofNat_assoc]
          exact sep_offsets F (c := 0x28) (n := 32) (d := 8 + i) (k := 1) (.inr (by omega)) (by decide) (by omega))
  have u7 : St n7.mem P n7 0x20 (reg n7) := ⟨by rw [pc7], rfl, fun _ => rfl⟩
  have K7 : ∀ q, tbKeep q = true → q ≠ ra → q.val ≠ 0 → q ≠ a0 → q ≠ a1 → reg n7 q = reg n4 q :=
    fun q hk hr hv h0 h1 => by
    rw [k7 q hk, r6 q hr, u5.regs, upd_ne hv h1, upd_ne hv h0]
  -- the constant-time comparison
  obtain ⟨n8, c8, u8⟩ := St.block [.aluImm .add a0 sp 0x8, .aluImm .add a1 sp 0x28] u7 hc7 (off' := 0x24)
    (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u8
  obtain ⟨n9, c9, pc9, mem9, regs9⟩ := u8.self.callRa hc7 fce_at_24 fce_at_28 (cb := P + 0xFFFFEF72)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFEF72 (by decide))
  have r9 := PEnv.reg1 regs9 u8.self.zero
  have sp9 : reg n9 sp = F := by rw [r9 sp (by decide), u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp7]
  obtain ⟨n10, c10, pc10, a010, iff10, k10, f10⟩ := ctEqSlice_correct n9 (base := P + 0xFFFFEF72)
    (p := F + 0x8) (q := F + 0x28)
    (even_at P env.hP 0xFFFFEF72 (by decide)) (by rw [mem9]; exact cIn env.cs sGS n7G)
    (by rw [mem9]; exact cIn env.ce sGE n7G) (by rw [mem9]; exact cIn env.bb sGB n7G) pc9
    (by rw [r9 a0 (by decide), u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp7]; rfl)
    (by rw [r9 a1 (by decide), u8.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp7]; rfl)
    (by rw [regs9]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x24 + 8) (by decide)))
    (by rw [sp9]; exact hFa) (by rw [sp9]; omega)
    (by rw [sp9, eC]; exact sGS.sub (by decide)) (by rw [sp9, eC]; exact sGE.sub (by decide))
    (by rw [sp9, eC]; exact sGB.sub (by decide))
    (by rw [sp9, eC, show F + 0x8 = F + BitVec.ofNat 32 8 from rfl, eFk]
        exact offs (.inr (by decide)) (by decide) (by decide))
    (by rw [sp9, eC, show F + 0x28 = F + BitVec.ofNat 32 0x28 from rfl, eFk]
        exact offs (.inr (by decide)) (by decide) (by decide))
  rw [mem9] at iff10
  rw [sp9, eC, mem9] at f10
  have hbytes : reg n10 a0 = 1 ↔ feBytesOf m.mem xp = feBytesOf m.mem yp := by
    rw [iff10, ← memBytes_eq_iff, b4', b7]
  -- the epilogue
  have u10 : St n10.mem P n10 0x2C (reg n10) := ⟨by rw [pc10], rfl, fun _ => rfl⟩
  have n10F : ∀ k, 0x48 ≤ k → k < 0x50 → n10.mem (F + BitVec.ofNat 32 k) = Ms (F + BitVec.ofNat 32 k) :=
    fun k h1 h2 => by
      rw [f10 _ (by rw [eFk]; exact offs (.inl (by omega)) (by decide) (by omega)),
        f7 _ (by rw [eR, eFk]; exact offs (.inl (by omega)) (by decide) (by omega))
          (sep_offsets F (c := 0x28) (n := 32) (d := k) (k := 1) (.inl (by omega)) (by decide) (by omega)),
        f4 _ (by rw [eR, eFk]; exact offs (.inl (by omega)) (by decide) (by omega))
          (sep_offsets F (c := 8) (n := 32) (d := k) (k := 1) (.inl (by omega)) (by decide) (by omega))]
  have ld : ∀ k, 0x48 ≤ k → k + 4 ≤ 0x50 → memLoad32 n10.mem (F + BitVec.ofNat 32 k) = memLoad32 Ms (F + BitVec.ofNat 32 k) :=
    fun k h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc, n10F _ (by omega) (by omega)]
  have lra : memLoad32 n10.mem (F + 0x4C) = retAddr := by
    rw [show F + 0x4C = F + BitVec.ofNat 32 0x4C from rfl, ld 0x4C (by decide) (by decide), ← hMs,
      memLoad32_store32_sep (a := F + 0x48) (b := F + BitVec.ofNat 32 0x4C)
        (sep_offsets F (c := 0x48) (n := 4) (d := 0x4C) (k := 4) (.inl (by decide)) (by decide) (by decide))]
    exact memLoad32_store32_same _ _ _
  have ls0 : memLoad32 n10.mem (F + 0x48) = reg m 8 := by
    rw [show F + 0x48 = F + BitVec.ofNat 32 0x48 from rfl, ld 0x48 (by decide) (by decide), ← hMs]
    exact memLoad32_store32_same _ _ _
  have hc10 : CodeIn n10.mem P feCtEqCode := fun i hi => by
    rw [f10 _ ((sGC.sub (c := 0x8F) (l := 0x21) (by decide)).subR (c := i) (l := 1) (by omega))]
    exact hc7 i hi
  have sp10 : reg n10 sp = F := by rw [k10 sp (by decide) (by decide) (by decide), sp9]
  obtain ⟨n11, c11, u11⟩ := St.block [.lw ra sp 0x4C, .lw (8 : Fin 32) sp 0x48, .aluImm .add sp sp 0x50] u10 hc10
    (off' := 0x32) (by decide) (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, upd_app, ↓reduceIte, and_true]
      rw [sp10]; exact ⟨aligned_add hFa (k := 0x4C) (by decide), aligned_add hFa (k := 0x48) (by decide)⟩)
  simp only [runBlock, BInstr.run] at u11
  simp +decide only [upd_app, ↓reduceIte] at u11
  rw [sp10, lra, ls0] at u11
  obtain ⟨n12, d12, pc12, mem12, regs12⟩ := u11.self.jalr hc10 fce_at_32
  have kq : ∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n10 q = reg m q := fun q hq => by
    have h : q ≠ a0 ∧ q ≠ a1 ∧ q ≠ t1 ∧ q ≠ ra ∧ q.val ≠ 0 ∧ tbKeep q = true ∧ q ≠ sp ∧ q ≠ 8 := by
      revert hq; revert q; decide
    rw [k10 q h.1 h.2.1 h.2.2.1, r9 q h.2.2.2.1, u8.regs, upd_ne h.2.2.2.2.1 h.2.1, upd_ne h.2.2.2.2.1 h.1,
      K7 q h.2.2.2.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.1 h.2.1, K4 q h.2.2.2.2.2.1 h.2.2.2.1,
      r2 q h.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2 h.2.1 h.1]
  refine ⟨n12, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans
    (c11.trans (.single d12))))))))))), ?_, ?_, ?_, fun q hq => ?_, fun x hx => ?_⟩
  · rw [pc12, u11.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero, hret]
  · rw [regs12, u11.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, eS]
  · rw [regs12, u11.regs]; simp +decide only [upd_app, ↓reduceIte]
    by_cases h : feBytesOf m.mem xp = feBytesOf m.mem yp
    · rw [ite_eq_left h]; exact hbytes.mpr h
    · rw [ite_eq_right h]
      rcases a010 with h0 | h1
      · exact h0
      · exact absurd (hbytes.mp h1) h
  · rw [regs12, u11.regs]
    by_cases hr : q = ra
    · subst hr; simp +decide only [upd_app, ↓reduceIte]; exact hra.symm
    by_cases h8 : q = 8
    · subst h8; simp +decide only [upd_app, ↓reduceIte]
    have hs : q ≠ sp := fun e => by subst e; revert hq; decide
    have hv : q.val ≠ 0 := fun e => by have : q = 0 := Fin.ext e; subst this; revert hq; decide
    simp only [upd_app, hv, hs, h8, hr, ite_false]
    exact kq q (by revert hq hr h8; revert q; decide)
  · rw [mem12, f10 x (hx.sub (c := 0x8F) (l := 0x21) (by decide)), n7G x hx]

end C3.RV32
