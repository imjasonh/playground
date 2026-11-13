import C3BootProofs.Proofs.AsProjective

/-!
# `CompletedPoint::as_extended`, as compiled

`curve25519_dalek`'s `CompletedPoint::as_extended` turns `(X, Y, Z, T)`
into the extended point `(X T, Y Z, Z T, X Y)` with four calls to
`<&FieldElement2625 as Mul>::mul`, the last a tail call.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem aex_at_0 : fetchRel asExtendedCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem aex_at_2 : fetchRel asExtendedCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem aex_at_4 : fetchRel asExtendedCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem aex_at_6 : fetchRel asExtendedCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x14, 2) := by decide
theorem aex_at_8 : fetchRel asExtendedCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x10, 2) := by decide
theorem aex_at_a : fetchRel asExtendedCode 0xA = some (.store .sw sp (19 : Fin 32) 0xC, 2) := by decide
theorem aex_at_c : fetchRel asExtendedCode 0xC = some (.store .sw sp (20 : Fin 32) 0x8, 2) := by decide
theorem aex_at_e : fetchRel asExtendedCode 0xE = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem aex_at_10 : fetchRel asExtendedCode 0x10 = some (.alu .add (9 : Fin 32) x0 a0, 2) := by decide
theorem aex_at_12 : fetchRel asExtendedCode 0x12 = some (.aluImm .add (18 : Fin 32) a1 0x78, 4) := by decide
theorem aex_at_16 : fetchRel asExtendedCode 0x16 = some (.alu .add a2 x0 (18 : Fin 32), 2) := by decide
theorem aex_at_18 : fetchRel asExtendedCode 0x18 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem aex_at_1c : fetchRel asExtendedCode 0x1C = some (.jalr ra ra 0xFFFFF8CE, 4) := by decide
theorem aex_at_20 : fetchRel asExtendedCode 0x20 = some (.aluImm .add (19 : Fin 32) (8 : Fin 32) 0x28, 4) := by decide
theorem aex_at_24 : fetchRel asExtendedCode 0x24 = some (.aluImm .add (20 : Fin 32) (8 : Fin 32) 0x50, 4) := by decide
theorem aex_at_28 : fetchRel asExtendedCode 0x28 = some (.aluImm .add a0 (9 : Fin 32) 0x28, 4) := by decide
theorem aex_at_2c : fetchRel asExtendedCode 0x2C = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem aex_at_2e : fetchRel asExtendedCode 0x2E = some (.alu .add a2 x0 (20 : Fin 32), 2) := by decide
theorem aex_at_30 : fetchRel asExtendedCode 0x30 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem aex_at_34 : fetchRel asExtendedCode 0x34 = some (.jalr ra ra 0xFFFFF8B6, 4) := by decide
theorem aex_at_38 : fetchRel asExtendedCode 0x38 = some (.aluImm .add a0 (9 : Fin 32) 0x50, 4) := by decide
theorem aex_at_3c : fetchRel asExtendedCode 0x3C = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem aex_at_3e : fetchRel asExtendedCode 0x3E = some (.alu .add a2 x0 (18 : Fin 32), 2) := by decide
theorem aex_at_40 : fetchRel asExtendedCode 0x40 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem aex_at_44 : fetchRel asExtendedCode 0x44 = some (.jalr ra ra 0xFFFFF8A6, 4) := by decide
theorem aex_at_48 : fetchRel asExtendedCode 0x48 = some (.aluImm .add a0 (9 : Fin 32) 0x78, 4) := by decide
theorem aex_at_4c : fetchRel asExtendedCode 0x4C = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem aex_at_4e : fetchRel asExtendedCode 0x4E = some (.alu .add a2 x0 (19 : Fin 32), 2) := by decide
theorem aex_at_50 : fetchRel asExtendedCode 0x50 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem aex_at_52 : fetchRel asExtendedCode 0x52 = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem aex_at_54 : fetchRel asExtendedCode 0x54 = some (.load .lw (9 : Fin 32) sp 0x14, 2) := by decide
theorem aex_at_56 : fetchRel asExtendedCode 0x56 = some (.load .lw (18 : Fin 32) sp 0x10, 2) := by decide
theorem aex_at_58 : fetchRel asExtendedCode 0x58 = some (.load .lw (19 : Fin 32) sp 0xC, 2) := by decide
theorem aex_at_5a : fetchRel asExtendedCode 0x5A = some (.load .lw (20 : Fin 32) sp 0x8, 2) := by decide
theorem aex_at_5c : fetchRel asExtendedCode 0x5C = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem aex_at_5e : fetchRel asExtendedCode 0x5E = some (.auipc (6 : Fin 32) 0xFFFFE000, 4) := by decide
theorem aex_at_62 : fetchRel asExtendedCode 0x62 = some (.jalr x0 (6 : Fin 32) 0xFFFFF888, 4) := by decide
end

/-- The function's region: its 0x20-byte frame and the 0x140 bytes below it
that `mul` uses. -/
abbrev axR (sp0 : Word) : Word := sp0 + 0xFFFFFEA0

/-- Where `as_extended` runs: its code and `mul`'s, its region below `sp0`,
the result `out` (four field elements), and the completed point `cp`
(four), aligned and apart from each other, the region, and the code. -/
structure AxEnv (M : Word → BitVec 8) (P sp0 out cp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P asExtendedCode
  mul : CodeIn M (P + 0xFFFFD8E6) feMulCode
  red : CodeIn M (P + 0xFFFFE3D6) feReduceCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x160 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hcp : cp.toNat % 4 = 0
  sC : Sep (axR sp0) 0x160 P asExtendedCode.length
  sM : Sep (axR sp0) 0x160 (P + 0xFFFFD8E6) feMulCode.length
  sR : Sep (axR sp0) 0x160 (P + 0xFFFFE3D6) feReduceCode.length
  oR : Sep out 160 (axR sp0) 0x160
  cR : Sep cp 160 (axR sp0) 0x160
  oCp : Sep out 160 cp 160
  oC : Sep out 160 P asExtendedCode.length
  oM : Sep out 160 (P + 0xFFFFD8E6) feMulCode.length
  oRd : Sep out 160 (P + 0xFFFFE3D6) feReduceCode.length

theorem axR_al {sp0 : Word} (h : sp0.toNat % 4 = 0) : (axR sp0).toNat % 4 = 0 :=
  aligned_add h (k := 0xFFFFFEA0) (by decide)

theorem axR_w {sp0 : Word} (h : 0x160 ≤ sp0.toNat) : (axR sp0).toNat + 0x160 = sp0.toNat := by
  rw [BitVec.toNat_add]
  have : (0xFFFFFEA0 : Word).toNat = 4294966944 := rfl
  have := sp0.isLt
  omega

set_option maxRecDepth 20000 in
/-- The environment `mul` needs, called with `sp` at `axR sp0 + c` for `c`
0x140 or 0x160, the result at `out + oc`, and the operands at `cp + xc` and
`cp + yc`. -/
theorem ax_fe' {M : Word → BitVec 8} {P sp0 out cp : Word} (env : AxEnv M P sp0 out cp)
    {M' : Word → BitVec 8} (hM : ∀ x, Sep (axR sp0) 0x160 x 1 → Sep out 160 x 1 → M' x = M x) {c oc xc yc : Nat}
    (hc : c = 0x140 ∨ c = 0x160) (ho : oc + 40 ≤ 160) (hx : xc + 40 ≤ 160) (hy : yc + 40 ≤ 160)
    (hoa : oc % 4 = 0) (hxa : xc % 4 = 0) (hya : yc % 4 = 0) :
    FeMEnv M' (P + 0xFFFFD8E6) (axR sp0 + BitVec.ofNat 32 c) (out + BitVec.ofNat 32 oc) (cp + BitVec.ofNat 32 xc)
      (cp + BitVec.ofNat 32 yc) := by
  have hRw := axR_w env.hS
  have cIn : ∀ {b : Word} {code : List Nat}, CodeIn M b code → Sep (axR sp0) 0x160 b code.length →
      Sep out 160 b code.length → CodeIn M' b code := fun hc' hs ho' i hi => by
    rw [hM _ (hs.subR (c := i) (l := 1) (by omega)) (ho'.subR (c := i) (l := 1) (by omega))]; exact hc' i hi
  have eG : axR sp0 + BitVec.ofNat 32 c + 0xFFFFFEC0 = axR sp0 + BitVec.ofNat 32 (c - 0x140) := by
    rcases hc with rfl | rfl <;> exact BitVec.add_assoc _ _ _
  have er : P + 0xFFFFD8E6 + 0xAF0 = P + 0xFFFFE3D6 := by rw [BitVec.add_assoc]; rfl
  exact {
    hP := even_at P env.hP 0xFFFFD8E6 (by decide)
    code := cIn env.mul env.sM env.oM
    red := by rw [er]; exact cIn env.red env.sR env.oRd
    hsp := aligned_add (axR_al env.hsp) (by rcases hc with rfl | rfl <;> decide)
    hS := by rw [BitVec.toNat_add, ofNat_tn (by omega)]; omega
    hout := aligned_add env.hout (by omega)
    hx := aligned_add env.hcp (by omega)
    hy := aligned_add env.hcp (by omega)
    sGC := by rw [eG]; exact env.sM.sub (by omega)
    sGR := by rw [eG, er]; exact env.sR.sub (by omega)
    sOC := env.oM.sub (by omega)
    sOR := by rw [er]; exact env.oRd.sub (by omega)
    sOG := by rw [eG]; exact (env.oR.sub (c := oc) (l := 40) (by omega)).subR (by omega)
    sXG := by rw [eG]; exact (env.cR.sub (c := xc) (l := 40) (by omega)).subR (by omega)
    sYG := by rw [eG]; exact (env.cR.sub (c := yc) (l := 40) (by omega)).subR (by omega) }

/-- The registers `as_extended` saves, at offsets from its `sp`. -/
abbrev axPs : List (Fin 32 × Word) :=
  [(ra, 0x1C), ((8 : Fin 32), 0x18), ((9 : Fin 32), 0x14), ((18 : Fin 32), 0x10), ((19 : Fin 32), 0xC),
   ((20 : Fin 32), 0x8)]

/-- From 0xE to the first call at 0x18: keep the pointers and pass
`mul(out, X, T)`'s arguments. -/
def axInit : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a1, .alu .add (9 : Fin 32) x0 a0, .aluImm .add (18 : Fin 32) a1 0x78,
   .alu .add a2 x0 (18 : Fin 32)]

/-- From 0x20 to 0x30: `mul(out + 0x28, Y, Z)`'s arguments. -/
def axMid : List BInstr :=
  [.aluImm .add (19 : Fin 32) (8 : Fin 32) 0x28, .aluImm .add (20 : Fin 32) (8 : Fin 32) 0x50,
   .aluImm .add a0 (9 : Fin 32) 0x28, .alu .add a1 x0 (19 : Fin 32), .alu .add a2 x0 (20 : Fin 32)]

/-- From 0x38 to 0x40: `mul(out + 0x50, Z, T)`'s arguments. -/
def axMid2 : List BInstr :=
  [.aluImm .add a0 (9 : Fin 32) 0x50, .alu .add a1 x0 (20 : Fin 32), .alu .add a2 x0 (18 : Fin 32)]

/-- From 0x48 to 0x50: `mul(out + 0x78, X, Y)`'s arguments. -/
def axArgs : List BInstr :=
  [.aluImm .add a0 (9 : Fin 32) 0x78, .alu .add a1 x0 (8 : Fin 32), .alu .add a2 x0 (19 : Fin 32)]

section
set_option maxRecDepth 20000
theorem axSave_end : blockEnd asExtendedCode 2 (saveBlock axPs) = some 0xE := by decide
theorem axInit_end : blockEnd asExtendedCode 0xE axInit = some 0x18 := by decide
theorem axMid_end : blockEnd asExtendedCode 0x20 axMid = some 0x30 := by decide
theorem axMid2_end : blockEnd asExtendedCode 0x38 axMid2 = some 0x40 := by decide
theorem axArgs_end : blockEnd asExtendedCode 0x48 axArgs = some 0x50 := by decide
theorem axRestore_end : blockEnd asExtendedCode 0x50 (restoreBlock axPs) = some 0x5C := by decide
theorem axPs_range : ∀ p ∈ axPs, p.2.toNat % 4 = 0 ∧ p.2.toNat + 4 ≤ 0x20 := by decide
theorem axPs_sp : ∀ p ∈ axPs, p.1 ≠ sp := by decide
end

/-- A call from `as_extended` to `mul` at `P + 0xFFFFD8E6`. -/
theorem ax_call {M : Word → BitVec 8} {P G out xp yp : Word} {n : Machine} {off : Nat} {imm o : Word}
    (hP : P.toNat % 2 = 0) (s : St M P n off (reg n)) (hc : CodeIn M P asExtendedCode)
    (env : FeMEnv M (P + 0xFFFFD8E6) G out xp yp)
    (h1 : fetchRel asExtendedCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel asExtendedCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xFFFFD8E6) (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = G) (r10 : reg n a0 = out) (r11 : reg n a1 = xp) (r12 : reg n a2 = yp) :
    ∃ n', Steps n n' ∧ St n'.mem P n' (off + 8) (reg n') ∧ reg n' sp = G ∧
      (∀ q, feMKeep q = true → q ≠ ra → reg n' q = reg n q) ∧
      (wordsAt n'.mem out 10).map BitVec.toNat = feMulAt M xp yp ∧
      ∀ x, Sep (G + 0xFFFFFEC0) 0x140 x 1 → Sep out 40 x 1 → n'.mem x = M x := by
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb (even_at P hP 0xFFFFD8E6 (by decide))
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨m2, c2, pc2, sp2, k2, v2, f2⟩ := feMul_correct m1 (by rw [mem1]; exact env) pc1
    (by rw [r1 a0 (by decide), r10]) (by rw [r1 a1 (by decide), r11]) (by rw [r1 a2 (by decide), r12])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) (by rw [r1 sp (by decide), rsp])
  rw [mem1] at v2 f2
  exact ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq hr => by rw [k2 q hq, r1 q hr], v2, f2⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `CompletedPoint::as_extended`**: the extended point at
`out` gets `X T`, `Y Z`, `Z T`, and `X Y` from the completed point
`(X, Y, Z, T)` at `cp`, as `mul` computes them. -/
theorem asExtended_correct (m : Machine) {P sp0 out cp retAddr : Word} (env : AxEnv m.mem P sp0 out cp)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = cp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, feMKeep q = true → reg m' q = reg m q) ∧
      (wordsAt m'.mem out 10).map BitVec.toNat = feMulAt m.mem cp (cp + 0x78) ∧
      (wordsAt m'.mem (out + 0x28) 10).map BitVec.toNat = feMulAt m.mem (cp + 0x28) (cp + 0x50) ∧
      (wordsAt m'.mem (out + 0x50) 10).map BitVec.toNat = feMulAt m.mem (cp + 0x50) (cp + 0x78) ∧
      (wordsAt m'.mem (out + 0x78) 10).map BitVec.toNat = feMulAt m.mem cp (cp + 0x28) ∧
      ∀ x, Sep (axR sp0) 0x160 x 1 → Sep out 160 x 1 → m'.mem x = m.mem x := by
  have hRw := axR_w env.hS
  have hRa := axR_al env.hsp
  obtain ⟨F, hF⟩ : ∃ F, axR sp0 + BitVec.ofNat 32 0x140 = F := ⟨_, rfl⟩
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have eF : sp0 + 0xFFFFFFE0 = F := by rw [← hF, BitVec.add_assoc]; rfl
  have hFa : F.toNat % 4 = 0 := hF ▸ aligned_add hRa (by decide)
  have sFC : Sep F 0x20 P asExtendedCode.length := hF ▸ env.sC.sub (by decide)
  have eG : F + 0xFFFFFEC0 = axR sp0 + BitVec.ofNat 32 0 := by rw [← hF, BitVec.add_assoc]; rfl
  have eSl : ∀ (o : Word) (t : Nat), F + o + BitVec.ofNat 32 t = axR sp0 + BitVec.ofNat 32 (0x140 + o.toNat + t) :=
    fun o t => by
      rw [← hF]; conv => lhs; rw [← ofNat_toNat_self o]
      rw [add_ofNat_assoc, add_ofNat_assoc, Nat.add_assoc]
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (axR sp0) 0x160 b code.length → Sep out 160 b code.length →
      (∀ x, Sep (axR sp0) 0x160 x 1 → Sep out 160 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc' hs ho hM i hi => by
      rw [hM _ (hs.subR (c := i) (l := 1) (by omega)) (ho.subR (c := i) (l := 1) (by omega))]; exact hc' i hi
  -- a call changes nothing outside the region and its 40 bytes of `out`
  have frCall : ∀ {M M' : Word → BitVec 8} {c oc : Nat}, c + 0x140 ≤ 0x160 → oc + 40 ≤ 160 →
      (∀ x, Sep (axR sp0 + BitVec.ofNat 32 c) 0x140 x 1 → Sep (out + BitVec.ofNat 32 oc) 40 x 1 → M' x = M x) →
      (∀ x, Sep (axR sp0) 0x160 x 1 → Sep out 160 x 1 → M x = m.mem x) →
      ∀ x, Sep (axR sp0) 0x160 x 1 → Sep out 160 x 1 → M' x = m.mem x := fun hc hoc hM h0 x hx hx' => by
    rw [hM x (hx.sub hc) (hx'.sub hoc), h0 x hx hx']
  -- and keeps the saved registers
  have slKeep : ∀ {M M' : Word → BitVec 8} {oc : Nat}, oc + 40 ≤ 160 →
      (∀ x, Sep (axR sp0 + BitVec.ofNat 32 0) 0x140 x 1 → Sep (out + BitVec.ofNat 32 oc) 40 x 1 → M' x = M x) →
      ∀ r o, (r, o) ∈ axPs → memLoad32 M' (F + o) = memLoad32 M (F + o) := by
    intro M M' oc hoc hM r o h
    obtain ⟨_, ho⟩ := axPs_range (r, o) h
    dsimp only at ho
    exact memLoad32_congr fun t ht => by
      rw [eSl]
      exact hM _ (sep_offsets _ (.inl (by omega)) (by omega) (by omega))
        ((env.oR.sub (c := oc) (l := 40) hoc).subR (by omega))
  -- the operands stay as they were
  have cpKeep : ∀ {M : Word → BitVec 8}, (∀ x, Sep (axR sp0) 0x160 x 1 → Sep out 160 x 1 → M x = m.mem x) →
      ∀ xc yc, xc + 40 ≤ 160 → yc + 40 ≤ 160 →
      feMulAt M (cp + BitVec.ofNat 32 xc) (cp + BitVec.ofNat 32 yc) =
        feMulAt m.mem (cp + BitVec.ofNat 32 xc) (cp + BitVec.ofNat 32 yc) := by
    intro M hM xc yc hx hy
    exact feMulAt_congr (fun t ht => by
        rw [add_ofNat_assoc]
        exact hM _ (env.cR.sub (c := xc + t) (l := 1) (by omega)).symm (env.oCp.subR (c := xc + t) (l := 1) (by omega)))
      (fun t ht => by
        rw [add_ofNat_assoc]
        exact hM _ (env.cR.sub (c := yc + t) (l := 1) (by omega)).symm (env.oCp.subR (c := yc + t) (l := 1) (by omega)))
  -- a call that writes `out + oc'` keeps the words at `out + oc`
  have outKeep : ∀ {M M' : Word → BitVec 8} {c oc oc' : Nat}, c + 0x140 ≤ 0x160 → oc + 40 ≤ 160 →
      (oc + 40 ≤ oc' ∨ oc' + 40 ≤ oc) → oc' + 40 ≤ 160 →
      (∀ x, Sep (axR sp0 + BitVec.ofNat 32 c) 0x140 x 1 → Sep (out + BitVec.ofNat 32 oc') 40 x 1 → M' x = M x) →
      wordsAt M' (out + BitVec.ofNat 32 oc) 10 = wordsAt M (out + BitVec.ofNat 32 oc) 10 := by
    intro M M' c oc oc' hc hoc hd hoc' hM
    exact wordsAt_bytes fun t ht => by
      rw [add_ofNat_assoc]
      exact hM _ ((env.oR.symm.sub (c := c) (l := 0x140) hc).subR (c := oc + t) (l := 1) (by omega))
        (sep_offsets out (by omega) (by omega) (by omega))
  -- the prologue
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code aex_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, eF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock axPs) u1 env.code axSave_end (saveBlock_ok _ axPs _ fun p hp => by
    rw [sp1]
    exact ⟨fr_al' hFa (axPs_range p hp).1, frm_sep' sFC (axPs_range p hp).2⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0)) axPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep (axR sp0) 0x160 x 1 → Sep out 160 x 1 → Msv x = m.mem x := fun x hx _ => by
    rw [← hMsv]
    exact saveMem_outside axPs fun p hp =>
      frm_sep' (hF ▸ hx.sub (c := 0x140) (l := 0x20) (by decide)) (axPs_range p hp).2
  have hslv : ∀ r o, (r, o) ∈ axPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [axPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ r, reg m2 r = upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) r := u2.regs
  obtain ⟨m3, c3, u3⟩ := St.block axInit u2.self (cIn env.code env.sC env.oC frSv) axInit_end
    (by simp [BlockOk, BInstr.ok, axInit])
  simp only [runBlock, BInstr.run, axInit] at u3
  have g3 : ∀ r, reg m3 r = _ := u3.regs
  have v3 : reg m3 sp = F ∧ reg m3 8 = cp ∧ reg m3 9 = out ∧ reg m3 18 = cp + 0x78 ∧ reg m3 a0 = out ∧
      reg m3 a1 = cp ∧ reg m3 a2 = cp + 0x78 := by
    simp +decide only [g3, upd_app, ↓reduceIte, r2]
    simp only [ev_add, hsp, eF, ha0, ha1, zw]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl
  have k3 : ∀ q : Fin 32, q ≠ sp → q ≠ 8 → q ≠ 9 → q ≠ 18 → q ≠ a2 → reg m3 q = reg m q := fun q h1 h2 h3 h4 h5 => by
    rw [g3]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact hz.symm
    simp only [upd_app, h0, h2, h3, h4, h5, ite_false]; rw [r2]; simp only [upd_app, h0, h1, ite_false]
  obtain ⟨v3sp, v38, v39, v318, v3a0, v3a1, v3a2⟩ := v3
  -- the first call: `mul(out, X, T)`
  have fe1 := ax_fe' env frSv (c := 0x140) (oc := 0) (xc := 0) (yc := 0x78) (.inl rfl) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [hF, add_ofNat_zero, add_ofNat_zero] at fe1
  obtain ⟨n4, c4, u4, sp4, k4, w4, f4⟩ := ax_call env.hP u3.self (cIn env.code env.sC env.oC frSv) fe1 aex_at_18
    aex_at_1c (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP _ (by decide)) v3sp v3a0 v3a1 v3a2
  have f4' : ∀ x, Sep (axR sp0 + BitVec.ofNat 32 0) 0x140 x 1 → Sep (out + BitVec.ofNat 32 0) 40 x 1 →
      n4.mem x = Msv x := fun x a b => f4 x (by rw [eG]; exact a) (by rw [add_ofNat_zero] at b; exact b)
  have fr4 := frCall (by decide) (by decide) f4' frSv
  have sl4 : ∀ r o, (r, o) ∈ axPs → memLoad32 n4.mem (F + o) = reg m r := fun r o h =>
    (slKeep (by decide) f4' r o h).trans (hslv r o h)
  have r48 : reg n4 8 = cp := by rw [k4 8 (by decide) (by decide), v38]
  have r49 : reg n4 9 = out := by rw [k4 9 (by decide) (by decide), v39]
  have r418 : reg n4 18 = cp + 0x78 := by rw [k4 18 (by decide) (by decide), v318]
  -- the second call: `mul(out + 0x28, Y, Z)`
  obtain ⟨n5, c5, u5⟩ := St.block axMid u4 (cIn env.code env.sC env.oC fr4) axMid_end
    (by simp [BlockOk, BInstr.ok, axMid])
  simp only [runBlock, BInstr.run, axMid] at u5
  have g5 : ∀ r, reg n5 r = _ := u5.regs
  have v5 : reg n5 sp = F ∧ reg n5 8 = cp ∧ reg n5 9 = out ∧ reg n5 18 = cp + 0x78 ∧ reg n5 19 = cp + 0x28 ∧
      reg n5 20 = cp + 0x50 ∧ reg n5 a0 = out + 0x28 ∧ reg n5 a1 = cp + 0x28 ∧ reg n5 a2 = cp + 0x50 := by
    simp +decide only [g5, upd_app, ↓reduceIte]
    simp only [ev_add, sp4, r48, r49, r418, zw]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl
  obtain ⟨v5sp, v58, v59, v518, v519, v520, v5a0, v5a1, v5a2⟩ := v5
  have k5 : ∀ q : Fin 32, q ≠ 19 → q ≠ 20 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n5 q = reg n4 q :=
    fun q h1 h1' h2 h3 h4 => by
      rw [g5]
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd]; exact u4.zero.symm
      simp only [upd_app, h0, h1, h1', h2, h3, h4, ite_false]
  have fe2 := ax_fe' env fr4 (c := 0x140) (oc := 0x28) (xc := 0x28) (yc := 0x50) (.inl rfl) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [hF] at fe2
  obtain ⟨n6, c6, u6, sp6, k6, w6, f6⟩ := ax_call env.hP u5.self (cIn env.code env.sC env.oC fr4) fe2 aex_at_30
    aex_at_34 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP _ (by decide)) v5sp v5a0 v5a1 v5a2
  have f6' : ∀ x, Sep (axR sp0 + BitVec.ofNat 32 0) 0x140 x 1 → Sep (out + BitVec.ofNat 32 0x28) 40 x 1 →
      n6.mem x = n4.mem x := fun x a b => f6 x (by rw [eG]; exact a) b
  have fr6 := frCall (by decide) (by decide) f6' fr4
  have sl6 : ∀ r o, (r, o) ∈ axPs → memLoad32 n6.mem (F + o) = reg m r := fun r o h =>
    (slKeep (by decide) f6' r o h).trans (sl4 r o h)
  have r68 : reg n6 8 = cp := by rw [k6 8 (by decide) (by decide), v58]
  have r69 : reg n6 9 = out := by rw [k6 9 (by decide) (by decide), v59]
  have r618 : reg n6 18 = cp + 0x78 := by rw [k6 18 (by decide) (by decide), v518]
  have r619 : reg n6 19 = cp + 0x28 := by rw [k6 19 (by decide) (by decide), v519]
  have r620 : reg n6 20 = cp + 0x50 := by rw [k6 20 (by decide) (by decide), v520]
  -- the third call: `mul(out + 0x50, Z, T)`
  obtain ⟨n7, c7, u7⟩ := St.block axMid2 u6 (cIn env.code env.sC env.oC fr6) axMid2_end
    (by simp [BlockOk, BInstr.ok, axMid2])
  simp only [runBlock, BInstr.run, axMid2] at u7
  have g7 : ∀ r, reg n7 r = _ := u7.regs
  have v7 : reg n7 sp = F ∧ reg n7 a0 = out + 0x50 ∧ reg n7 a1 = cp + 0x50 ∧ reg n7 a2 = cp + 0x78 := by
    simp +decide only [g7, upd_app, ↓reduceIte]
    simp only [ev_add, sp6, r69, r618, r620, zw]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl
  obtain ⟨v7sp, v7a0, v7a1, v7a2⟩ := v7
  have k7 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n7 q = reg n6 q := fun q h2 h3 h4 => by
    rw [g7]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u6.zero.symm
    simp only [upd_app, h0, h2, h3, h4, ite_false]
  have fe3 := ax_fe' env fr6 (c := 0x140) (oc := 0x50) (xc := 0x50) (yc := 0x78) (.inl rfl) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [hF] at fe3
  obtain ⟨n8, c8, u8, sp8, k8, w8, f8⟩ := ax_call env.hP u7.self (cIn env.code env.sC env.oC fr6) fe3 aex_at_40
    aex_at_44 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP _ (by decide)) v7sp v7a0 v7a1 v7a2
  have f8' : ∀ x, Sep (axR sp0 + BitVec.ofNat 32 0) 0x140 x 1 → Sep (out + BitVec.ofNat 32 0x50) 40 x 1 →
      n8.mem x = n6.mem x := fun x a b => f8 x (by rw [eG]; exact a) b
  have fr8 := frCall (by decide) (by decide) f8' fr6
  have sl8 : ∀ r o, (r, o) ∈ axPs → memLoad32 n8.mem (F + o) = reg m r := fun r o h =>
    (slKeep (by decide) f8' r o h).trans (sl6 r o h)
  have r88 : reg n8 8 = cp := by rw [k8 8 (by decide) (by decide), k7 8 (by decide) (by decide) (by decide), r68]
  have r89 : reg n8 9 = out := by rw [k8 9 (by decide) (by decide), k7 9 (by decide) (by decide) (by decide), r69]
  have r819 : reg n8 19 = cp + 0x28 := by
    rw [k8 19 (by decide) (by decide), k7 19 (by decide) (by decide) (by decide), r619]
  -- the tail call's arguments and the epilogue
  have hc8 := cIn env.code env.sC env.oC fr8
  obtain ⟨n9, c9, u9⟩ := St.block axArgs u8 hc8 axArgs_end (by simp [BlockOk, BInstr.ok, axArgs])
  simp only [runBlock, BInstr.run, axArgs] at u9
  have g9 : ∀ r, reg n9 r = _ := u9.regs
  have v9 : reg n9 sp = F ∧ reg n9 a0 = out + 0x78 ∧ reg n9 a1 = cp ∧ reg n9 a2 = cp + 0x28 := by
    simp +decide only [g9, upd_app, ↓reduceIte]
    simp only [ev_add, sp8, r88, r89, r819, zw]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl
  obtain ⟨sp9, v9a0, v9a1, v9a2⟩ := v9
  have k9 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n9 q = reg n8 q := fun q h2 h3 h4 => by
    rw [g9]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u8.zero.symm
    simp only [upd_app, h0, h2, h3, h4, ite_false]
  obtain ⟨n10, c10, u10⟩ := St.block (restoreBlock axPs) u9.self hc8 axRestore_end
    (restoreBlock_ok n8.mem _ axPs (reg n9) sp9 axPs_sp fun p hp => fr_al' hFa (axPs_range p hp).1)
  simp only [restoreBlock_run n8.mem _ axPs (reg n9) sp9 axPs_sp] at u10
  obtain ⟨n11, d11, u11⟩ := u10.aluImm hc8 aex_at_5c (off' := 0x5E) (by decide)
  obtain ⟨n12, d12, u12⟩ := u11.auipc hc8 aex_at_5e (off' := 0x62) (by decide)
  obtain ⟨n13, d13, pc13, mem13, regs13⟩ := u12.jalr hc8 aex_at_62
  have rsp10 : restoreRegs n8.mem F (reg n9) axPs sp = F := by rw [restoreRegs_sp _ _ _ _ axPs_sp]; exact sp9
  have rest : ∀ r o, (r, o) ∈ axPs → restoreRegs n8.mem F (reg n9) axPs r = reg m r := fun r o h => by
    simp only [axPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact sl8 _ _ (by decide)
  have restO : ∀ q : Fin 32, q ≠ ra → q ≠ 8 → q ≠ 9 → q ≠ 18 → q ≠ 19 → q ≠ 20 →
      restoreRegs n8.mem F (reg n9) axPs q = reg n9 q := fun q h1 h2 h3 h4 h5 h6 => by
    simp only [restoreRegs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u9.self.zero.symm
    simp only [upd_app, h0, h1, h2, h3, h4, h5, h6, ite_false]
  have r13 : ∀ q, q ≠ sp → q ≠ t1 → reg n13 q = restoreRegs n8.mem F (reg n9) axPs q := fun q h1 h2 => by
    rw [regs13]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this
      rw [restO 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp [upd]; exact u9.self.zero.symm
    simp only [upd_app, h0, h1, h2, ite_false]
  have eSp : F + 0x20 = sp0 := by rw [← eF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have pcM : n13.pc = P + 0xFFFFD8E6 := by
    rw [pc13]; simp +decide only [upd_app, ↓reduceIte]
    rw [show P + BitVec.ofNat 32 0x5E + 0xFFFFE000 + 0xFFFFF888 = P + 0xFFFFD8E6 by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact even_clear _ (even_at P env.hP 0xFFFFD8E6 (by decide))
  have sp13 : reg n13 sp = sp0 := by rw [regs13]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp10, ev_add, eSp]
  have ra13 : reg n13 ra = retAddr := by rw [r13 ra (by decide) (by decide), rest ra 0x1C (by decide), hra]
  have nk : ∀ q : Fin 32, q = a0 ∨ q = a1 ∨ q = a2 → reg n13 q = reg n9 q := fun q hq => by
    rcases hq with rfl | rfl | rfl <;>
    · rw [r13 _ (by decide) (by decide),
        restO _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have eS : axR sp0 + BitVec.ofNat 32 0x160 = sp0 := by
    show sp0 + 0xFFFFFEA0 + BitVec.ofNat 32 0x160 = sp0; rw [BitVec.add_assoc]; exact BitVec.add_zero sp0
  have fe4 := ax_fe' env fr8 (c := 0x160) (oc := 0x78) (xc := 0) (yc := 0x28) (.inr rfl) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [eS, add_ofNat_zero] at fe4
  obtain ⟨mF, cF, pcF, spF, kF, wF, fF⟩ := feMul_correct n13 (by rw [mem13]; exact fe4) pcM
    (by rw [nk a0 (.inl rfl), v9a0]; rfl) (by rw [nk a1 (.inr (.inl rfl)), v9a1])
    (by rw [nk a2 (.inr (.inr rfl)), v9a2]; rfl) ra13 hret sp13
  have eT : sp0 + 0xFFFFFEC0 = axR sp0 + BitVec.ofNat 32 0x20 := by
    show sp0 + 0xFFFFFEC0 = sp0 + 0xFFFFFEA0 + BitVec.ofNat 32 0x20; rw [BitVec.add_assoc]; rfl
  have fF' : ∀ x, Sep (axR sp0 + BitVec.ofNat 32 0x20) 0x140 x 1 → Sep (out + BitVec.ofNat 32 0x78) 40 x 1 →
      mF.mem x = n8.mem x := fun x a b => by rw [fF x (by rw [eT]; exact a) b, mem13]
  rw [mem13] at wF
  refine ⟨mF, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans
    (c10.trans (.cons d11 (.cons d12 (.cons d13 cF)))))))))))), pcF, spF, ?_, ?_, ?_, ?_, ?_,
    frCall (by decide) (by decide) fF' fr8⟩
  · intro q hq
    rw [kF q hq]
    by_cases hra' : q = ra
    · subst hra'; rw [ra13, hra]
    by_cases hsp' : q = sp
    · subst hsp'; rw [sp13, hsp]
    have ht : q ≠ t1 := by rintro rfl; exact absurd hq (by decide)
    rw [r13 q hsp' ht]
    by_cases h8 : q = 8
    · subst h8; exact rest 8 0x18 (by decide)
    by_cases h9 : q = 9
    · subst h9; exact rest 9 0x14 (by decide)
    by_cases h18 : q = 18
    · subst h18; exact rest 18 0x10 (by decide)
    by_cases h19 : q = 19
    · subst h19; exact rest 19 0xC (by decide)
    by_cases h20 : q = 20
    · subst h20; exact rest 20 0x8 (by decide)
    have ha0' : q ≠ a0 := by rintro rfl; exact absurd hq (by decide)
    have ha1' : q ≠ a1 := by rintro rfl; exact absurd hq (by decide)
    have ha2' : q ≠ a2 := by rintro rfl; exact absurd hq (by decide)
    rw [restO q hra' h8 h9 h18 h19 h20, k9 q ha0' ha1' ha2', k8 q hq hra', k7 q ha0' ha1' ha2', k6 q hq hra',
      k5 q h19 h20 ha0' ha1' ha2', k4 q hq hra', k3 q hsp' h8 h9 h18 ha2']
  · have h1 := outKeep (c := 0x20) (oc := 0) (oc' := 0x78) (by decide) (by decide) (.inl (by decide)) (by decide) fF'
    have h2 := outKeep (c := 0) (oc := 0) (oc' := 0x50) (by decide) (by decide) (.inl (by decide)) (by decide) f8'
    have h3 := outKeep (c := 0) (oc := 0) (oc' := 0x28) (by decide) (by decide) (.inl (by decide)) (by decide) f6'
    rw [add_ofNat_zero] at h1 h2 h3
    have h4 := cpKeep frSv 0 0x78 (by decide) (by decide)
    rw [add_ofNat_zero] at h4
    rw [h1, h2, h3, w4, h4]; rfl
  · have h1 := outKeep (c := 0x20) (oc := 0x28) (oc' := 0x78) (by decide) (by decide) (.inl (by decide)) (by decide)
      fF'
    have h2 := outKeep (c := 0) (oc := 0x28) (oc' := 0x50) (by decide) (by decide) (.inl (by decide)) (by decide) f8'
    show List.map BitVec.toNat (wordsAt mF.mem (out + BitVec.ofNat 32 0x28) 10) = _
    rw [h1, h2, w6, cpKeep fr4 0x28 0x50 (by decide) (by decide)]; rfl
  · have h1 := outKeep (c := 0x20) (oc := 0x50) (oc' := 0x78) (by decide) (by decide) (.inl (by decide)) (by decide)
      fF'
    show List.map BitVec.toNat (wordsAt mF.mem (out + BitVec.ofNat 32 0x50) 10) = _
    rw [h1, w8, cpKeep fr6 0x50 0x78 (by decide) (by decide)]; rfl
  · show List.map BitVec.toNat (wordsAt mF.mem (out + BitVec.ofNat 32 0x78) 10) = _
    have h4 := cpKeep fr8 0 0x28 (by decide) (by decide)
    rw [add_ofNat_zero] at h4
    exact wF.trans h4

end C3.RV32
