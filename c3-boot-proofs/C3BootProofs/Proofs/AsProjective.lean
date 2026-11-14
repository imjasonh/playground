import C3BootProofs.Proofs.FeMul
import C3BootProofs.Proofs.ShrWide12

/-!
# `CompletedPoint::as_projective`, as compiled

`curve25519_dalek`'s `CompletedPoint::as_projective` turns `(X, Y, Z, T)`
into the projective point `(X T, Y Z, Z T)` with three calls to
`<&FieldElement2625 as Mul>::mul`, the last a tail call.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem apj_at_0 : fetchRel asProjectiveCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem apj_at_2 : fetchRel asProjectiveCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem apj_at_4 : fetchRel asProjectiveCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x8, 2) := by decide
theorem apj_at_6 : fetchRel asProjectiveCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x4, 2) := by decide
theorem apj_at_8 : fetchRel asProjectiveCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x0, 2) := by decide
theorem apj_at_a : fetchRel asProjectiveCode 0xA = some (.alu .add (8 : Fin 32) x0 a1, 2) := by decide
theorem apj_at_c : fetchRel asProjectiveCode 0xC = some (.alu .add (9 : Fin 32) x0 a0, 2) := by decide
theorem apj_at_e : fetchRel asProjectiveCode 0xE = some (.aluImm .add (18 : Fin 32) a1 0x78, 4) := by decide
theorem apj_at_12 : fetchRel asProjectiveCode 0x12 = some (.alu .add a2 x0 (18 : Fin 32), 2) := by decide
theorem apj_at_14 : fetchRel asProjectiveCode 0x14 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem apj_at_18 : fetchRel asProjectiveCode 0x18 = some (.jalr ra ra 0x338, 4) := by decide
theorem apj_at_1c : fetchRel asProjectiveCode 0x1C = some (.aluImm .add a1 (8 : Fin 32) 0x28, 4) := by decide
theorem apj_at_20 : fetchRel asProjectiveCode 0x20 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x50, 4) := by decide
theorem apj_at_24 : fetchRel asProjectiveCode 0x24 = some (.aluImm .add a0 (9 : Fin 32) 0x28, 4) := by decide
theorem apj_at_28 : fetchRel asProjectiveCode 0x28 = some (.alu .add a2 x0 (8 : Fin 32), 2) := by decide
theorem apj_at_2a : fetchRel asProjectiveCode 0x2A = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem apj_at_2e : fetchRel asProjectiveCode 0x2E = some (.jalr ra ra 0x322, 4) := by decide
theorem apj_at_32 : fetchRel asProjectiveCode 0x32 = some (.aluImm .add a0 (9 : Fin 32) 0x50, 4) := by decide
theorem apj_at_36 : fetchRel asProjectiveCode 0x36 = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem apj_at_38 : fetchRel asProjectiveCode 0x38 = some (.alu .add a2 x0 (18 : Fin 32), 2) := by decide
theorem apj_at_3a : fetchRel asProjectiveCode 0x3A = some (.load .lw ra sp 0xC, 2) := by decide
theorem apj_at_3c : fetchRel asProjectiveCode 0x3C = some (.load .lw (8 : Fin 32) sp 0x8, 2) := by decide
theorem apj_at_3e : fetchRel asProjectiveCode 0x3E = some (.load .lw (9 : Fin 32) sp 0x4, 2) := by decide
theorem apj_at_40 : fetchRel asProjectiveCode 0x40 = some (.load .lw (18 : Fin 32) sp 0x0, 2) := by decide
theorem apj_at_42 : fetchRel asProjectiveCode 0x42 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem apj_at_44 : fetchRel asProjectiveCode 0x44 = some (.auipc (6 : Fin 32) 0xFFFFD000, 4) := by decide
theorem apj_at_48 : fetchRel asProjectiveCode 0x48 = some (.jalr x0 (6 : Fin 32) 0x308, 4) := by decide
end

/-- `mul`'s output for the field elements at `xp` and `yp`. -/
abbrev feMulAt (M : Word → BitVec 8) (xp yp : Word) : List Nat :=
  feMulSpec (limbAt M xp 0) (limbAt M xp 1) (limbAt M xp 2) (limbAt M xp 3) (limbAt M xp 4) (limbAt M xp 5)
    (limbAt M xp 6) (limbAt M xp 7) (limbAt M xp 8) (limbAt M xp 9) (limbAt M yp 0) (limbAt M yp 1)
    (limbAt M yp 2) (limbAt M yp 3) (limbAt M yp 4) (limbAt M yp 5) (limbAt M yp 6) (limbAt M yp 7)
    (limbAt M yp 8) (limbAt M yp 9)

/-- The function's region: its 0x10-byte frame and the 0x140 bytes below it
that `mul` uses. -/
abbrev apR (sp0 : Word) : Word := sp0 + 0xFFFFFEB0

/-- Where `as_projective` runs: its code and `mul`'s, its region below
`sp0`, the result `out` (three field elements), and the completed point
`cp` (four), aligned and apart from each other, the region, and the code. -/
structure ApEnv (M : Word → BitVec 8) (P sp0 out cp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P asProjectiveCode
  mul : CodeIn M (P + 0xFFFFD34C) feMulCode
  red : CodeIn M (P + 0xFFFFDE3C) feReduceCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x150 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hcp : cp.toNat % 4 = 0
  sC : Sep (apR sp0) 0x150 P asProjectiveCode.length
  sM : Sep (apR sp0) 0x150 (P + 0xFFFFD34C) feMulCode.length
  sR : Sep (apR sp0) 0x150 (P + 0xFFFFDE3C) feReduceCode.length
  oR : Sep out 120 (apR sp0) 0x150
  cR : Sep cp 160 (apR sp0) 0x150
  oCp : Sep out 120 cp 160
  oC : Sep out 120 P asProjectiveCode.length
  oM : Sep out 120 (P + 0xFFFFD34C) feMulCode.length
  oRd : Sep out 120 (P + 0xFFFFDE3C) feReduceCode.length


theorem apR_al {sp0 : Word} (h : sp0.toNat % 4 = 0) : (apR sp0).toNat % 4 = 0 :=
  aligned_add h (k := 0xFFFFFEB0) (by decide)

theorem apR_w {sp0 : Word} (h : 0x150 ≤ sp0.toNat) : (apR sp0).toNat + 0x150 = sp0.toNat := by
  rw [BitVec.toNat_add]
  have : (0xFFFFFEB0 : Word).toNat = 4294966960 := rfl
  have := sp0.isLt
  omega

set_option maxRecDepth 20000 in
/-- The environment `mul` needs, called with `sp` at `apR sp0 + c` for `c`
0x140 or 0x150, the result at `out + oc`, and the operands at `cp + xc` and
`cp + yc`. -/
theorem ap_fe' {M : Word → BitVec 8} {P sp0 out cp : Word} (env : ApEnv M P sp0 out cp)
    {M' : Word → BitVec 8} (hM : ∀ x, Sep (apR sp0) 0x150 x 1 → Sep out 120 x 1 → M' x = M x) {c oc xc yc : Nat}
    (hc : c = 0x140 ∨ c = 0x150) (ho : oc + 40 ≤ 120) (hx : xc + 40 ≤ 160) (hy : yc + 40 ≤ 160)
    (hoa : oc % 4 = 0) (hxa : xc % 4 = 0) (hya : yc % 4 = 0) :
    FeMEnv M' (P + 0xFFFFD34C) (apR sp0 + BitVec.ofNat 32 c) (out + BitVec.ofNat 32 oc) (cp + BitVec.ofNat 32 xc)
      (cp + BitVec.ofNat 32 yc) := by
  have hRw := apR_w env.hS
  have cIn : ∀ {b : Word} {code : List Nat}, CodeIn M b code → Sep (apR sp0) 0x150 b code.length →
      Sep out 120 b code.length → CodeIn M' b code := fun hc' hs ho' i hi => by
    rw [hM _ (hs.subR (c := i) (l := 1) (by omega)) (ho'.subR (c := i) (l := 1) (by omega))]; exact hc' i hi
  have eG : apR sp0 + BitVec.ofNat 32 c + 0xFFFFFEC0 = apR sp0 + BitVec.ofNat 32 (c - 0x140) := by
    rcases hc with rfl | rfl <;> exact BitVec.add_assoc _ _ _
  have er : P + 0xFFFFD34C + 0xAF0 = P + 0xFFFFDE3C := by rw [BitVec.add_assoc]; rfl
  exact {
    hP := even_at P env.hP 0xFFFFD34C (by decide)
    code := cIn env.mul env.sM env.oM
    red := by rw [er]; exact cIn env.red env.sR env.oRd
    hsp := aligned_add (apR_al env.hsp) (by rcases hc with rfl | rfl <;> decide)
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


/-- The registers `as_projective` saves, at offsets from its `sp`. -/
abbrev apPs : List (Fin 32 × Word) := [(ra, 0xC), ((8 : Fin 32), 0x8), ((9 : Fin 32), 0x4), ((18 : Fin 32), 0x0)]

/-- From 0xA to the first call at 0x14: keep the pointers and pass
`mul(out, X, T)`'s arguments. -/
def apInit : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a1, .alu .add (9 : Fin 32) x0 a0, .aluImm .add (18 : Fin 32) a1 0x78,
   .alu .add a2 x0 (18 : Fin 32)]

/-- From 0x1C to 0x2A: `mul(out + 0x28, Y, Z)`'s arguments. -/
def apMid : List BInstr :=
  [.aluImm .add a1 (8 : Fin 32) 0x28, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x50, .aluImm .add a0 (9 : Fin 32) 0x28,
   .alu .add a2 x0 (8 : Fin 32)]

/-- From 0x32 to 0x3A: `mul(out + 0x50, Z, T)`'s arguments. -/
def apArgs : List BInstr :=
  [.aluImm .add a0 (9 : Fin 32) 0x50, .alu .add a1 x0 (8 : Fin 32), .alu .add a2 x0 (18 : Fin 32)]

section
set_option maxRecDepth 20000
theorem apSave_end : blockEnd asProjectiveCode 2 (saveBlock apPs) = some 0xA := by decide
theorem apInit_end : blockEnd asProjectiveCode 0xA apInit = some 0x14 := by decide
theorem apMid_end : blockEnd asProjectiveCode 0x1C apMid = some 0x2A := by decide
theorem apArgs_end : blockEnd asProjectiveCode 0x32 apArgs = some 0x3A := by decide
theorem apRestore_end : blockEnd asProjectiveCode 0x3A (restoreBlock apPs) = some 0x42 := by decide
theorem apPs_range : ∀ p ∈ apPs, p.2.toNat % 4 = 0 ∧ p.2.toNat + 4 ≤ 0x10 := by decide
theorem apPs_sp : ∀ p ∈ apPs, p.1 ≠ sp := by decide
end

/-- A call from `as_projective` to `mul` at `P + 0xFFFFD34C`. -/
theorem ap_call {M : Word → BitVec 8} {P G out xp yp : Word} {n : Machine} {off : Nat} {imm o : Word}
    (hP : P.toNat % 2 = 0) (s : St M P n off (reg n)) (hc : CodeIn M P asProjectiveCode)
    (env : FeMEnv M (P + 0xFFFFD34C) G out xp yp)
    (h1 : fetchRel asProjectiveCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel asProjectiveCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0xFFFFD34C) (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = G) (r10 : reg n a0 = out) (r11 : reg n a1 = xp) (r12 : reg n a2 = yp) :
    ∃ n', Steps n n' ∧ St n'.mem P n' (off + 8) (reg n') ∧ reg n' sp = G ∧
      (∀ q, feMKeep q = true → q ≠ ra → reg n' q = reg n q) ∧
      (wordsAt n'.mem out 10).map BitVec.toNat = feMulAt M xp yp ∧
      ∀ x, Sep (G + 0xFFFFFEC0) 0x140 x 1 → Sep out 40 x 1 → n'.mem x = M x := by
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb (even_at P hP 0xFFFFD34C (by decide))
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨m2, c2, pc2, sp2, k2, v2, f2⟩ := feMul_correct m1 (by rw [mem1]; exact env) pc1
    (by rw [r1 a0 (by decide), r10]) (by rw [r1 a1 (by decide), r11]) (by rw [r1 a2 (by decide), r12])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) (by rw [r1 sp (by decide), rsp])
  rw [mem1] at v2 f2
  exact ⟨m2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq hr => by rw [k2 q hq, r1 q hr], v2, f2⟩


theorem limbAt_congr {M M' : Word → BitVec 8} {b : Word} {n : Nat} (h : ∀ t, t < 4 * n → M' (b + BitVec.ofNat 32 t) =
    M (b + BitVec.ofNat 32 t)) : ∀ i, i < n → limbAt M' b i = limbAt M b i := fun i hi => by
  unfold limbAt; congr 1
  exact memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h _ (by omega)

theorem feMulAt_congr {M M' : Word → BitVec 8} {xp yp : Word}
    (hx : ∀ t, t < 40 → M' (xp + BitVec.ofNat 32 t) = M (xp + BitVec.ofNat 32 t))
    (hy : ∀ t, t < 40 → M' (yp + BitVec.ofNat 32 t) = M (yp + BitVec.ofNat 32 t)) :
    feMulAt M' xp yp = feMulAt M xp yp := by
  have ex := limbAt_congr (n := 10) hx
  have ey := limbAt_congr (n := 10) hy
  simp only [feMulAt, ex 0 (by decide), ex 1 (by decide), ex 2 (by decide), ex 3 (by decide), ex 4 (by decide),
    ex 5 (by decide), ex 6 (by decide), ex 7 (by decide), ex 8 (by decide), ex 9 (by decide), ey 0 (by decide),
    ey 1 (by decide), ey 2 (by decide), ey 3 (by decide), ey 4 (by decide), ey 5 (by decide), ey 6 (by decide),
    ey 7 (by decide), ey 8 (by decide), ey 9 (by decide)]

theorem wordsAt_bytes {M M' : Word → BitVec 8} {b : Word} {n : Nat}
    (h : ∀ t, t < 4 * n → M' (b + BitVec.ofNat 32 t) = M (b + BitVec.ofNat 32 t)) : wordsAt M' b n = wordsAt M b n := by
  unfold wordsAt
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h _ (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `CompletedPoint::as_projective`**: the projective point
at `out` gets `X T`, `Y Z`, and `Z T` from the completed point
`(X, Y, Z, T)` at `cp`, as `mul` computes them. -/
theorem asProjective_correct (m : Machine) {P sp0 out cp retAddr : Word} (env : ApEnv m.mem P sp0 out cp)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = cp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, feMKeep q = true → reg m' q = reg m q) ∧
      (wordsAt m'.mem out 10).map BitVec.toNat = feMulAt m.mem cp (cp + 0x78) ∧
      (wordsAt m'.mem (out + 0x28) 10).map BitVec.toNat = feMulAt m.mem (cp + 0x28) (cp + 0x50) ∧
      (wordsAt m'.mem (out + 0x50) 10).map BitVec.toNat = feMulAt m.mem (cp + 0x50) (cp + 0x78) ∧
      ∀ x, Sep (apR sp0) 0x150 x 1 → Sep out 120 x 1 → m'.mem x = m.mem x := by
  have hRw := apR_w env.hS
  have hRa := apR_al env.hsp
  obtain ⟨F, hF⟩ : ∃ F, apR sp0 + BitVec.ofNat 32 0x140 = F := ⟨_, rfl⟩
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have eF : sp0 + 0xFFFFFFF0 = F := by rw [← hF, BitVec.add_assoc]; rfl
  have hFa : F.toNat % 4 = 0 := hF ▸ aligned_add hRa (by decide)
  have sFC : Sep F 0x10 P asProjectiveCode.length := hF ▸ env.sC.sub (by decide)
  have eG : F + 0xFFFFFEC0 = apR sp0 + BitVec.ofNat 32 0 := by rw [← hF, BitVec.add_assoc]; rfl
  have eSl : ∀ (o : Word) (t : Nat), F + o + BitVec.ofNat 32 t = apR sp0 + BitVec.ofNat 32 (0x140 + o.toNat + t) :=
    fun o t => by
      rw [← hF]; conv => lhs; rw [← ofNat_toNat_self o]
      rw [add_ofNat_assoc, add_ofNat_assoc, Nat.add_assoc]
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (apR sp0) 0x150 b code.length → Sep out 120 b code.length →
      (∀ x, Sep (apR sp0) 0x150 x 1 → Sep out 120 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc' hs ho hM i hi => by
      rw [hM _ (hs.subR (c := i) (l := 1) (by omega)) (ho.subR (c := i) (l := 1) (by omega))]; exact hc' i hi
  -- a call changes nothing outside the region and its 40 bytes of `out`
  have frCall : ∀ {M M' : Word → BitVec 8} {c oc : Nat}, c + 0x140 ≤ 0x150 → oc + 40 ≤ 120 →
      (∀ x, Sep (apR sp0 + BitVec.ofNat 32 c) 0x140 x 1 → Sep (out + BitVec.ofNat 32 oc) 40 x 1 → M' x = M x) →
      (∀ x, Sep (apR sp0) 0x150 x 1 → Sep out 120 x 1 → M x = m.mem x) →
      ∀ x, Sep (apR sp0) 0x150 x 1 → Sep out 120 x 1 → M' x = m.mem x := fun hc hoc hM h0 x hx hx' => by
    rw [hM x (hx.sub hc) (hx'.sub hoc), h0 x hx hx']
  -- and keeps the saved registers
  have slKeep : ∀ {M M' : Word → BitVec 8} {oc : Nat}, oc + 40 ≤ 120 →
      (∀ x, Sep (apR sp0 + BitVec.ofNat 32 0) 0x140 x 1 → Sep (out + BitVec.ofNat 32 oc) 40 x 1 → M' x = M x) →
      ∀ r o, (r, o) ∈ apPs → memLoad32 M' (F + o) = memLoad32 M (F + o) := by
    intro M M' oc hoc hM r o h
    obtain ⟨_, ho⟩ := apPs_range (r, o) h
    dsimp only at ho
    exact memLoad32_congr fun t ht => by
      rw [eSl]
      exact hM _ (sep_offsets _ (.inl (by omega)) (by omega) (by omega))
        ((env.oR.sub (c := oc) (l := 40) hoc).subR (by omega))
  -- the prologue
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code apj_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFF0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, eF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock apPs) u1 env.code apSave_end (saveBlock_ok _ apPs _ fun p hp => by
    rw [sp1]
    exact ⟨fr_al' hFa (apPs_range p hp).1, frm_sep' sFC (apPs_range p hp).2⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFF0)) apPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep (apR sp0) 0x150 x 1 → Sep out 120 x 1 → Msv x = m.mem x := fun x hx _ => by
    rw [← hMsv]
    exact saveMem_outside apPs fun p hp =>
      frm_sep' (hF ▸ hx.sub (c := 0x140) (l := 0x10) (by decide)) (apPs_range p hp).2
  have hslv : ∀ r o, (r, o) ∈ apPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [apPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ r, reg m2 r = upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFF0) r := u2.regs
  have z2 : reg m2 x0 = 0 := u2.self.zero
  obtain ⟨m3, c3, u3⟩ := St.block apInit u2.self (cIn env.code env.sC env.oC frSv) apInit_end
    (by simp [BlockOk, BInstr.ok, apInit])
  simp only [runBlock, BInstr.run, apInit] at u3
  have g3 : ∀ r, reg m3 r = _ := u3.regs
  have up2 : ∀ r, r ≠ sp → upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFF0) r = reg m r := fun r h => updz hz h
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
  -- the operands stay as they were
  have cpKeep : ∀ {M : Word → BitVec 8}, (∀ x, Sep (apR sp0) 0x150 x 1 → Sep out 120 x 1 → M x = m.mem x) →
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
  have outKeep : ∀ {M M' : Word → BitVec 8} {c oc oc' : Nat}, c + 0x140 ≤ 0x150 → oc + 40 ≤ 120 →
      (oc + 40 ≤ oc' ∨ oc' + 40 ≤ oc) → oc' + 40 ≤ 120 →
      (∀ x, Sep (apR sp0 + BitVec.ofNat 32 c) 0x140 x 1 → Sep (out + BitVec.ofNat 32 oc') 40 x 1 → M' x = M x) →
      wordsAt M' (out + BitVec.ofNat 32 oc) 10 = wordsAt M (out + BitVec.ofNat 32 oc) 10 := by
    intro M M' c oc oc' hc hoc hd hoc' hM
    exact wordsAt_bytes fun t ht => by
      rw [add_ofNat_assoc]
      exact hM _ ((env.oR.symm.sub (c := c) (l := 0x140) hc).subR (c := oc + t) (l := 1) (by omega))
        (sep_offsets out (by omega) (by omega) (by omega))
  -- the first call: `mul(out, X, T)`
  have fe1 := ap_fe' env frSv (c := 0x140) (oc := 0) (xc := 0) (yc := 0x78) (.inl rfl) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [hF, add_ofNat_zero, add_ofNat_zero] at fe1
  obtain ⟨n4, c4, u4, sp4, k4, w4, f4⟩ := ap_call env.hP u3.self (cIn env.code env.sC env.oC frSv) fe1 apj_at_14
    apj_at_18 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP _ (by decide)) v3sp v3a0 v3a1 v3a2
  have f4' : ∀ x, Sep (apR sp0 + BitVec.ofNat 32 0) 0x140 x 1 → Sep (out + BitVec.ofNat 32 0) 40 x 1 →
      n4.mem x = Msv x := fun x a b => f4 x (by rw [eG]; exact a) (by rw [add_ofNat_zero] at b; exact b)
  have fr4 := frCall (by decide) (by decide) f4' frSv
  have sl4 : ∀ r o, (r, o) ∈ apPs → memLoad32 n4.mem (F + o) = reg m r := fun r o h =>
    (slKeep (by decide) f4' r o h).trans (hslv r o h)
  have r48 : reg n4 8 = cp := by rw [k4 8 (by decide) (by decide), v38]
  have r49 : reg n4 9 = out := by rw [k4 9 (by decide) (by decide), v39]
  have r418 : reg n4 18 = cp + 0x78 := by rw [k4 18 (by decide) (by decide), v318]
  -- the second call: `mul(out + 0x28, Y, Z)`
  obtain ⟨n5, c5, u5⟩ := St.block apMid u4 (cIn env.code env.sC env.oC fr4) apMid_end
    (by simp [BlockOk, BInstr.ok, apMid])
  simp only [runBlock, BInstr.run, apMid] at u5
  have g5 : ∀ r, reg n5 r = _ := u5.regs
  have v5 : reg n5 sp = F ∧ reg n5 8 = cp + 0x50 ∧ reg n5 9 = out ∧ reg n5 18 = cp + 0x78 ∧
      reg n5 a0 = out + 0x28 ∧ reg n5 a1 = cp + 0x28 ∧ reg n5 a2 = cp + 0x50 := by
    simp +decide only [g5, upd_app, ↓reduceIte]
    simp only [ev_add, sp4, r48, r49, r418, zw]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl
  obtain ⟨v5sp, v58, v59, v518, v5a0, v5a1, v5a2⟩ := v5
  have k5 : ∀ q : Fin 32, q ≠ 8 → q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n5 q = reg n4 q := fun q h1 h2 h3 h4 => by
    rw [g5]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u4.zero.symm
    simp only [upd_app, h0, h1, h2, h3, h4, ite_false]
  have fe2 := ap_fe' env fr4 (c := 0x140) (oc := 0x28) (xc := 0x28) (yc := 0x50) (.inl rfl) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [hF] at fe2
  obtain ⟨n6, c6, u6, sp6, k6, w6, f6⟩ := ap_call env.hP u5.self (cIn env.code env.sC env.oC fr4) fe2 apj_at_2a
    apj_at_2e (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP _ (by decide)) v5sp v5a0 v5a1 v5a2
  have f6' : ∀ x, Sep (apR sp0 + BitVec.ofNat 32 0) 0x140 x 1 → Sep (out + BitVec.ofNat 32 0x28) 40 x 1 →
      n6.mem x = n4.mem x := fun x a b => f6 x (by rw [eG]; exact a) b
  have fr6 := frCall (by decide) (by decide) f6' fr4
  have sl6 : ∀ r o, (r, o) ∈ apPs → memLoad32 n6.mem (F + o) = reg m r := fun r o h =>
    (slKeep (by decide) f6' r o h).trans (sl4 r o h)
  have r68 : reg n6 8 = cp + 0x50 := by rw [k6 8 (by decide) (by decide), v58]
  have r69 : reg n6 9 = out := by rw [k6 9 (by decide) (by decide), v59]
  have r618 : reg n6 18 = cp + 0x78 := by rw [k6 18 (by decide) (by decide), v518]
  -- the third call's arguments, the epilogue, and the tail call
  have hc6 := cIn env.code env.sC env.oC fr6
  obtain ⟨n7, c7, u7⟩ := St.block apArgs u6 hc6 apArgs_end (by simp [BlockOk, BInstr.ok, apArgs])
  simp only [runBlock, BInstr.run, apArgs] at u7
  have g7 : ∀ r, reg n7 r = _ := u7.regs
  have v7 : reg n7 sp = F ∧ reg n7 a0 = out + 0x50 ∧ reg n7 a1 = cp + 0x50 ∧ reg n7 a2 = cp + 0x78 := by
    simp +decide only [g7, upd_app, ↓reduceIte]
    simp only [ev_add, sp6, r68, r69, r618, zw]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl
  obtain ⟨sp7, v7a0, v7a1, v7a2⟩ := v7
  have k7 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n7 q = reg n6 q := fun q h2 h3 h4 => by
    rw [g7]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u6.zero.symm
    simp only [upd_app, h0, h2, h3, h4, ite_false]
  obtain ⟨n8, c8, u8⟩ := St.block (restoreBlock apPs) u7.self hc6 apRestore_end
    (restoreBlock_ok n6.mem _ apPs (reg n7) sp7 apPs_sp fun p hp => fr_al' hFa (apPs_range p hp).1)
  simp only [restoreBlock_run n6.mem _ apPs (reg n7) sp7 apPs_sp] at u8
  obtain ⟨n9, d9, u9⟩ := u8.aluImm hc6 apj_at_42 (off' := 0x44) (by decide)
  obtain ⟨n10, d10, u10⟩ := u9.auipc hc6 apj_at_44 (off' := 0x48) (by decide)
  obtain ⟨n11, d11, pc11, mem11, regs11⟩ := u10.jalr hc6 apj_at_48
  have rsp8 : restoreRegs n6.mem F (reg n7) apPs sp = F := by rw [restoreRegs_sp _ _ _ _ apPs_sp]; exact sp7
  have rest : ∀ r o, (r, o) ∈ apPs → restoreRegs n6.mem F (reg n7) apPs r = reg m r := fun r o h => by
    simp only [apPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact sl6 _ _ (by decide)
  have restO : ∀ q : Fin 32, q ≠ ra → q ≠ 8 → q ≠ 9 → q ≠ 18 →
      restoreRegs n6.mem F (reg n7) apPs q = reg n7 q := fun q h1 h2 h3 h4 => by
    simp only [restoreRegs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact u7.self.zero.symm
    simp only [upd_app, h0, h1, h2, h3, h4, ite_false]
  have r11 : ∀ q, q ≠ sp → q ≠ t1 → reg n11 q = restoreRegs n6.mem F (reg n7) apPs q := fun q h1 h2 => by
    rw [regs11]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [restO 0 (by decide) (by decide) (by decide) (by decide)]; simp [upd]; exact u7.self.zero.symm
    simp only [upd_app, h0, h1, h2, ite_false]
  have eSp : F + 0x10 = sp0 := by rw [← eF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have pcM : n11.pc = P + 0xFFFFD34C := by
    rw [pc11]; simp +decide only [upd_app, ↓reduceIte]
    rw [show P + BitVec.ofNat 32 0x44 + 0xFFFFD000 + 0x308 = P + 0xFFFFD34C by
      rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
    exact even_clear _ (even_at P env.hP 0xFFFFD34C (by decide))
  have sp11 : reg n11 sp = sp0 := by rw [regs11]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp8, ev_add, eSp]
  have ra11 : reg n11 ra = retAddr := by rw [r11 ra (by decide) (by decide), rest ra 0xC (by decide), hra]
  have nk : ∀ q : Fin 32, q = a0 ∨ q = a1 ∨ q = a2 → reg n11 q = reg n7 q := fun q hq => by
    rcases hq with rfl | rfl | rfl <;>
    · rw [r11 _ (by decide) (by decide), restO _ (by decide) (by decide) (by decide) (by decide)]
  have eS : apR sp0 + BitVec.ofNat 32 0x150 = sp0 := by
    show sp0 + 0xFFFFFEB0 + BitVec.ofNat 32 0x150 = sp0; rw [BitVec.add_assoc]; exact BitVec.add_zero sp0
  have fe3 := ap_fe' env fr6 (c := 0x150) (oc := 0x50) (xc := 0x50) (yc := 0x78) (.inr rfl) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  rw [eS] at fe3
  obtain ⟨mF, cF, pcF, spF, kF, wF, fF⟩ := feMul_correct n11 (by rw [mem11]; exact fe3) pcM
    (by rw [nk a0 (.inl rfl), v7a0]; rfl) (by rw [nk a1 (.inr (.inl rfl)), v7a1]; rfl)
    (by rw [nk a2 (.inr (.inr rfl)), v7a2]; rfl) ra11 hret sp11
  have eT : sp0 + 0xFFFFFEC0 = apR sp0 + BitVec.ofNat 32 0x10 := by
    show sp0 + 0xFFFFFEC0 = sp0 + 0xFFFFFEB0 + BitVec.ofNat 32 0x10; rw [BitVec.add_assoc]; rfl
  have fF' : ∀ x, Sep (apR sp0 + BitVec.ofNat 32 0x10) 0x140 x 1 → Sep (out + BitVec.ofNat 32 0x50) 40 x 1 →
      mF.mem x = n6.mem x := fun x a b => by rw [fF x (by rw [eT]; exact a) b, mem11]
  rw [mem11] at wF
  refine ⟨mF, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans
    (.cons d9 (.cons d10 (.cons d11 cF)))))))))), pcF, spF, ?_, ?_, ?_, ?_, frCall (by decide) (by decide) fF' fr6⟩
  · intro q hq
    rw [kF q hq]
    by_cases hra' : q = ra
    · subst hra'; rw [ra11, hra]
    by_cases hsp' : q = sp
    · subst hsp'; rw [sp11, hsp]
    have ht : q ≠ t1 := by rintro rfl; exact absurd hq (by decide)
    rw [r11 q hsp' ht]
    by_cases h8 : q = 8
    · subst h8; exact rest 8 0x8 (by decide)
    by_cases h9 : q = 9
    · subst h9; exact rest 9 0x4 (by decide)
    by_cases h18 : q = 18
    · subst h18; exact rest 18 0x0 (by decide)
    have ha0' : q ≠ a0 := by rintro rfl; exact absurd hq (by decide)
    have ha1' : q ≠ a1 := by rintro rfl; exact absurd hq (by decide)
    have ha2' : q ≠ a2 := by rintro rfl; exact absurd hq (by decide)
    rw [restO q hra' h8 h9 h18, k7 q ha0' ha1' ha2', k6 q hq hra', k5 q h8 ha0' ha1' ha2', k4 q hq hra',
      k3 q hsp' h8 h9 h18 ha2']
  · have h1 := outKeep (c := 0x10) (oc := 0) (oc' := 0x50) (by decide) (by decide) (.inl (by decide)) (by decide) fF'
    have h2 := outKeep (c := 0) (oc := 0) (oc' := 0x28) (by decide) (by decide) (.inl (by decide)) (by decide) f6'
    rw [add_ofNat_zero] at h1 h2
    have h3 := cpKeep frSv 0 0x78 (by decide) (by decide)
    rw [add_ofNat_zero] at h3
    rw [h1, h2, w4, h3]; rfl
  · have h1 := outKeep (c := 0x10) (oc := 0x28) (oc' := 0x50) (by decide) (by decide) (.inl (by decide)) (by decide)
      fF'
    show List.map BitVec.toNat (wordsAt mF.mem (out + BitVec.ofNat 32 0x28) 10) = _
    rw [h1, w6, cpKeep fr4 0x28 0x50 (by decide) (by decide)]; rfl
  · show List.map BitVec.toNat (wordsAt mF.mem (out + BitVec.ofNat 32 0x50) 10) = _
    exact wF.trans (cpKeep fr6 0x50 0x78 (by decide) (by decide))

end C3.RV32
