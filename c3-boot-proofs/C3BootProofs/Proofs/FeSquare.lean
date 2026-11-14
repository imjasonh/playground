import C3BootProofs.Proofs.FeSqInner
import C3BootProofs.Proofs.FeReduce

/-!
# `FieldElement2625::square`

`curve25519_dalek`'s field squaring, as compiled: it saves `ra` and `s0`,
calls `square_inner` into a buffer in its frame and `reduce` from that
buffer into the result, restores the two registers, and returns.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem fsr_at_0 : fetchRel feSquareCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFA0, 2) := by decide
theorem fsr_at_2 : fetchRel feSquareCode 0x2 = some (.store .sw sp ra 0x5C, 2) := by decide
theorem fsr_at_4 : fetchRel feSquareCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x58, 2) := by decide
theorem fsr_at_6 : fetchRel feSquareCode 0x6 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem fsr_at_8 : fetchRel feSquareCode 0x8 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem fsr_at_a : fetchRel feSquareCode 0xA = some (.auipc ra 0x0, 4) := by decide
theorem fsr_at_e : fetchRel feSquareCode 0xE = some (.jalr ra ra 0x1C, 4) := by decide
theorem fsr_at_12 : fetchRel feSquareCode 0x12 = some (.aluImm .add a1 sp 0x8, 2) := by decide
theorem fsr_at_14 : fetchRel feSquareCode 0x14 = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem fsr_at_16 : fetchRel feSquareCode 0x16 = some (.auipc ra 0x0, 4) := by decide
theorem fsr_at_1a : fetchRel feSquareCode 0x1A = some (.jalr ra ra 0xFFFFFC76, 4) := by decide
theorem fsr_at_1e : fetchRel feSquareCode 0x1E = some (.load .lw ra sp 0x5C, 2) := by decide
theorem fsr_at_20 : fetchRel feSquareCode 0x20 = some (.load .lw (8 : Fin 32) sp 0x58, 2) := by decide
theorem fsr_at_22 : fetchRel feSquareCode 0x22 = some (.aluImm .add sp sp 0x60, 2) := by decide
theorem fsr_at_24 : fetchRel feSquareCode 0x24 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- `FieldElement2625::square`: `square_inner`'s ten sums, then `reduce`. -/
def feSquareSpec (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Nat) : List Nat :=
  let z := feSqZ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
  feReduceSpec z[0]! z[1]! z[2]! z[3]! z[4]! z[5]! z[6]! z[7]! z[8]! z[9]!

/-- Where `square` runs: its code at an even `P`, `square_inner`'s at
`P + 0x26` and `reduce`'s at `P - 0x374`, the 0xB0 bytes of stack below
`sp0` that the three use, the result at `out`, and the operand at `xp`. -/
structure FeSquareEnv (M : Word → BitVec 8) (P sp0 out xp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P feSquareCode
  sqi : CodeIn M (P + 0x26) feSquareInnerCode
  red : CodeIn M (P + 0xFFFFFC8C) feReduceCode
  hsp : sp0.toNat % 4 = 0
  hS : 0xB0 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hx : xp.toNat % 4 = 0
  sGC : Sep (sp0 + 0xFFFFFF50) 0xB0 P feSquareCode.length
  sGI : Sep (sp0 + 0xFFFFFF50) 0xB0 (P + 0x26) feSquareInnerCode.length
  sGR : Sep (sp0 + 0xFFFFFF50) 0xB0 (P + 0xFFFFFC8C) feReduceCode.length
  sOC : Sep out 40 P feSquareCode.length
  sOR : Sep out 40 (P + 0xFFFFFC8C) feReduceCode.length
  sOG : Sep out 40 (sp0 + 0xFFFFFF50) 0xB0
  sXG : Sep xp 40 (sp0 + 0xFFFFFF50) 0xB0

/-- The registers `square` leaves as they were. -/
def feSquareKeep (q : Fin 32) : Bool := q.val ∉ [5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

theorem fsr_call_at (P : Word) (o k : Word) (off : Nat) (h : BitVec.ofNat 32 off + o = k) :
    P + BitVec.ofNat 32 off + 0x0 + o = P + k := by
  rw [BitVec.add_assoc, BitVec.add_assoc, show (0x0 : Word) + o = o from BitVec.zero_add o, h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The compiled `FieldElement2625::square`**, called with the result at
`out` and the operand's limbs at `xp`: it stores `feSquareSpec` of the limbs,
returns with `sp` and every register but `t0` through `t6` and `a0` through
`a7` as they were, and changes no memory outside its 0xB0 bytes of stack
and the result. -/
theorem feSquare_correct (m : Machine) {P sp0 out xp retAddr : Word} (env : FeSquareEnv m.mem P sp0 out xp)
    (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, feSquareKeep q = true → reg m' q = reg m q) ∧
      (wordsAt m'.mem out 10).map BitVec.toNat =
        feSquareSpec (limbAt m.mem xp 0) (limbAt m.mem xp 1) (limbAt m.mem xp 2) (limbAt m.mem xp 3)
          (limbAt m.mem xp 4) (limbAt m.mem xp 5) (limbAt m.mem xp 6) (limbAt m.mem xp 7)
          (limbAt m.mem xp 8) (limbAt m.mem xp 9) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF50) 0xB0 x 1 → Sep out 40 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFF50 = G := ⟨_, rfl⟩
  obtain ⟨F, hFG⟩ : ∃ F, G + 0x50 = F := ⟨_, rfl⟩
  rw [hG]
  have sGC : Sep G 0xB0 P feSquareCode.length := hG ▸ env.sGC
  have sGI : Sep G 0xB0 (P + 0x26) feSquareInnerCode.length := hG ▸ env.sGI
  have sGR : Sep G 0xB0 (P + 0xFFFFFC8C) feReduceCode.length := hG ▸ env.sGR
  have sOG : Sep out 40 G 0xB0 := hG ▸ env.sOG
  have sXG : Sep xp 40 G 0xB0 := hG ▸ env.sXG
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFF50) (by decide)
  have hF : F.toNat % 4 = 0 := by rw [← hFG]; exact fr_al' hGa (by decide)
  have hFsp : sp0 + 0xFFFFFFA0 = F := by rw [← hFG, ← hG, BitVec.add_assoc]; rfl
  have hspF : F + 0x60 = sp0 := by
    rw [← hFG, ← hG, BitVec.add_assoc, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have fG : ∀ {c : Nat}, F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x50 + c) := fun {c} => by
    rw [← hFG, BitVec.add_assoc, show (0x50 : Word) = BitVec.ofNat 32 0x50 from rfl, ofNat_add_ofNat]
  have eGi : F + 0xFFFFFFB0 = G := by rw [← hFG, BitVec.add_assoc]; exact BitVec.add_zero G
  have eGr : F + 0xFFFFFFE0 = G + BitVec.ofNat 32 0x30 := by rw [← hFG, BitVec.add_assoc]; rfl
  have eZ : F + 0x8 = G + BitVec.ofNat 32 0x58 := fG (c := 8)
  have sepG : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0xB0 → d + k ≤ 0xB0 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun {c n d k} h h1 h2 =>
    sep_offsets G (c := c) (n := n) (d := d) (k := k) h (by omega) (by omega)
  have g0 : G + BitVec.ofNat 32 0 = G := add_ofNat_zero G
  have cOf : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep G 0xB0 b code.length → (∀ x, Sep G 0xB0 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have inG : ∀ {c l : Nat}, c + l ≤ 0xB0 → ∀ x, Sep G 0xB0 x 1 → Sep (G + BitVec.ofNat 32 c) l x 1 :=
    fun h x hx => hx.sub (c := _) (l := _) h
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  -- the prologue
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code fsr_at_0 (off' := 2) (by decide)
  have r1sp : reg m1 sp = F := by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [hsp, hFsp]
  have rk1 : ∀ r, r ≠ sp → reg m1 r = reg m r := fun r h1 => by
    rw [u1.regs]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, h1]
  obtain ⟨p0, dp0, up0⟩ := u1.self.swG env.code fsr_at_2 (off' := 0x4) (by decide)
    (by rw [r1sp]; exact fr_al' hF (by decide)) (a := F + 0x5C) (v := reg m ra) (by rw [r1sp])
    (rk1 _ (by decide))
  obtain ⟨P0, hP0⟩ : ∃ M', memStore32 m.mem (F + 0x5C) (reg m ra) = M' := ⟨_, rfl⟩
  rw [hP0] at up0
  have sFC : ∀ {c : Nat}, c + 4 ≤ 0x60 → Sep (F + BitVec.ofNat 32 c) 4 P feSquareCode.length := fun {c} h => by
    rw [fG]; exact sGC.sub (c := 0x50 + c) (l := 4) (by omega)
  have hcp0 : CodeIn P0 P feSquareCode := by rw [← hP0]; exact env.code.store32 (sFC (c := 0x5C) (by decide))
  obtain ⟨p1, dp1, up1⟩ := up0.swG hcp0 fsr_at_4 (off' := 0x6) (by decide)
    (by rw [r1sp]; exact fr_al' hF (by decide)) (a := F + 0x58) (v := reg m (8 : Fin 32)) (by rw [r1sp])
    (rk1 _ (by decide))
  obtain ⟨P1, hP1⟩ : ∃ M', memStore32 P0 (F + 0x58) (reg m (8 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP1] at up1
  have hcp1 : CodeIn P1 P feSquareCode := by rw [← hP1]; exact hcp0.store32 (sFC (c := 0x58) (by decide))
  have fpro : ∀ x, Sep (F + 0x58) 8 x 1 → P1 x = m.mem x := fun x hx => by
    rw [← hP1, memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h),
      ← hP0, memStore32_get_sep (show Sep (F + 0x5C) 4 x 1 from by
        have := hx.sub (c := 4) (l := 4) (by decide); rwa [BitVec.add_assoc] at this)]
  have inS : ∀ x, Sep G 0xB0 x 1 → Sep (F + 0x58) 8 x 1 := fun x hx => by
    rw [show F + 0x58 = G + BitVec.ofNat 32 0xA8 from fG (c := 0x58)]; exact inG (by decide) x hx
  have frP : ∀ x, Sep G 0xB0 x 1 → P1 x = m.mem x := fun x hx => fpro x (inS x hx)
  have sv5C : memLoad32 P1 (F + 0x5C) = reg m ra := by
    rw [← hP1, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x5C) 4 from
      sep_offsets F (c := 0x58) (n := 4) (d := 0x5C) (k := 4) (by decide) (by decide) (by decide)),
      ← hP0, memLoad32_store32_same]
  have sv58 : memLoad32 P1 (F + 0x58) = reg m (8 : Fin 32) := by rw [← hP1, memLoad32_store32_same]
  -- `mv s0, a0`, `addi a0, sp, 8`, and the call to `square_inner`
  obtain ⟨p2, dp2, up2⟩ := up1.aluE hcp1 fsr_at_6 (off' := 0x8) (by decide) (v := out)
    (by rw [rk1 _ (by decide), rk1 _ (by decide), hz, ha0]; exact BitVec.zero_add _)
  obtain ⟨p3, dp3, up3⟩ := up2.aluImm hcp1 fsr_at_8 (off' := 0xA) (by decide)
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := up3.callRa hcp1 fsr_at_a fsr_at_e (cb := P + 0x26)
    (fsr_call_at P 0x1C 0x26 0xA rfl) (even_at P env.hP 0x26 (by decide))
  have r4 := PEnv.reg1 regs4 up3.zero
  have hS50 : 0x50 ≤ F.toNat := by
    have := env.hS; rw [← hFsp, BitVec.toNat_add, show (0xFFFFFFA0 : Word).toNat = 4294967200 from rfl]; omega
  have SE : FeSqEnv m4.mem (P + 0x26) F (F + 0x8) xp := by
    rw [mem4]
    refine ⟨even_at P env.hP 0x26 (by decide), cOf env.sqi sGI frP, hF, hS50, fr_al' hF (by decide), env.hx,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [eGi]; have := sGI.sub (c := 0) (l := 0x50) (by decide); rwa [g0] at this
    · rw [eZ]; exact sGI.sub (c := 0x58) (l := 0x50) (by decide)
    · rw [eZ, eGi]
      have := sepG (c := 0x58) (n := 0x50) (d := 0) (k := 0x50) (.inr (by decide)) (by decide) (by decide)
      rwa [g0] at this
    · rw [eGi]; have := sXG.subR (c := 0) (l := 0x50) (by decide); rwa [g0] at this
    · rw [eZ]; exact sXG.subR (c := 0x58) (l := 0x50) (by decide)
  obtain ⟨m5, c5, pc5, sp5, k5, out5, fr5⟩ := feSqInner_correct m4 SE pc4
    (by rw [r4 _ (by decide)]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [r1sp])
    (by rw [r4 _ (by decide)]; simp +decide only [upd_app, ↓reduceIte]; rw [rk1 _ (by decide), ha1])
    (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P env.hP (0xA + 8) (by decide)))
    (by rw [r4 _ (by decide)]; simp +decide only [upd_app, ↓reduceIte]; exact r1sp)
  have fr5G : ∀ x, Sep G 0xB0 x 1 → m5.mem x = m.mem x := fun x hx => by
    have h1 : Sep (F + 0xFFFFFFB0) 0x50 x 1 := by
      rw [eGi]; have := inG (c := 0) (l := 0x50) (by decide) x hx; rwa [g0] at this
    have h2 : Sep (F + 0x8) 0x50 x 1 := by rw [eZ]; exact inG (by decide) x hx
    rw [fr5 x h1 h2, mem4, frP x hx]
  have hc5 := cOf env.code sGC fr5G
  have w5 : St m5.mem P m5 0x12 (reg m5) := ⟨by rw [pc5]; try rfl, rfl, fun _ => rfl⟩
  -- `addi a1, sp, 8`, `mv a0, s0`, and the call to `reduce`
  obtain ⟨p6, dp6, up6⟩ := w5.aluImm hc5 fsr_at_12 (off' := 0x14) (by decide)
  obtain ⟨p7, dp7, up7⟩ := up6.aluE hc5 fsr_at_14 (off' := 0x16) (by decide) (v := out)
    (by
      simp +decide only [upd_app, ↓reduceIte]
      rw [k5 _ rfl, r4 _ (by decide)]
      simp +decide only [upd_app, ↓reduceIte]
      exact BitVec.zero_add _)
  obtain ⟨m8, c8, pc8, mem8, regs8⟩ := up7.callRa hc5 fsr_at_16 fsr_at_1a (cb := P + 0xFFFFFC8C)
    (fsr_call_at P 0xFFFFFC76 0xFFFFFC8C 0x16 rfl) (even_at P env.hP 0xFFFFFC8C (by decide))
  have r8 := PEnv.reg1 regs8 up7.zero
  have RE : FREnv m8.mem (P + 0xFFFFFC8C) F out (F + 0x8) := by
    rw [mem8]
    refine ⟨even_at P env.hP 0xFFFFFC8C (by decide), cOf env.red sGR fr5G, hF, by omega, env.hout,
      fr_al' hF (by decide), ?_, env.sOR, ?_, ?_⟩
    · rw [eGr]; exact sGR.sub (c := 0x30) (l := 0x20) (by decide)
    · rw [eGr]; exact sOG.subR (c := 0x30) (l := 0x20) (by decide)
    · rw [eZ, eGr]; exact sepG (.inr (by decide)) (by decide) (by decide)
  obtain ⟨m9, c9, pc9, sp9, k9, out9, fr9⟩ := feReduce_correct m8 RE pc8
    (by rw [r8 _ (by decide)]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [r8 _ (by decide)]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [sp5])
    (by rw [regs8]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P env.hP (0x16 + 8) (by decide)))
    (by rw [r8 _ (by decide)]; simp +decide only [upd_app, ↓reduceIte]; exact sp5)
  have fr9G : ∀ x, Sep G 0xB0 x 1 → Sep out 40 x 1 → m9.mem x = m.mem x := fun x hx ho => by
    have h1 : Sep (F + 0xFFFFFFE0) 0x20 x 1 := by rw [eGr]; exact inG (by decide) x hx
    rw [fr9 x h1 ho, mem8, fr5G x hx]
  have hc9 : CodeIn m9.mem P feSquareCode := fun i hi => by
    rw [fr9G _ (sGC.subR (c := i) (l := 1) (by omega)) (env.sOC.subR (c := i) (l := 1) (by omega))]
    exact env.code i hi
  have rdOf : ∀ {o : Nat} {v : Word}, 0x58 ≤ o → o + 4 ≤ 0x60 →
      memLoad32 P1 (F + BitVec.ofNat 32 o) = v → memLoad32 m9.mem (F + BitVec.ofNat 32 o) = v := fun {o v} h1 h2 hv => by
    have s1 : Sep (F + 0xFFFFFFE0) 0x20 (F + BitVec.ofNat 32 o) 4 := by
      rw [eGr, fG]; exact sepG (.inl (by omega)) (by decide) (by omega)
    have s2 : Sep out 40 (F + BitVec.ofNat 32 o) 4 := by rw [fG]; exact sOG.subR (c := 0x50 + o) (l := 4) (by omega)
    have s3 : Sep (F + 0xFFFFFFB0) 0x50 (F + BitVec.ofNat 32 o) 4 := by
      rw [eGi, fG]; have := sepG (c := 0) (n := 0x50) (d := 0x50 + o) (k := 4) (.inl (by omega)) (by decide) (by omega)
      rwa [g0] at this
    have s4 : Sep (F + 0x8) 0x50 (F + BitVec.ofNat 32 o) 4 := by
      rw [eZ, fG]; exact sepG (.inl (by omega)) (by decide) (by omega)
    rw [load_frame2 fr9 s1 s2, mem8, load_frame2 fr5 s3 s4, mem4, hv]
  have rd5C : memLoad32 m9.mem (F + 0x5C) = reg m ra := rdOf (o := 0x5C) (by decide) (by decide) sv5C
  have rd58 : memLoad32 m9.mem (F + 0x58) = reg m (8 : Fin 32) := rdOf (o := 0x58) (by decide) (by decide) sv58
  -- the epilogue
  have w9 : St m9.mem P m9 0x1E (reg m9) := ⟨by rw [pc9]; try rfl, rfl, fun _ => rfl⟩
  obtain ⟨e0, de0, ue0⟩ := w9.lwE hc9 fsr_at_1e (off' := 0x20) (by decide)
    (by rw [sp9]; exact fr_al' hF (by decide)) (v := reg m ra) (by rw [sp9]; exact rd5C)
  obtain ⟨e1, de1, ue1⟩ := ue0.lwE hc9 fsr_at_20 (off' := 0x22) (by decide)
    (by simp +decide only [upd_app, ↓reduceIte]; rw [sp9]; exact fr_al' hF (by decide)) (v := reg m (8 : Fin 32))
    (by simp +decide only [upd_app, ↓reduceIte]; rw [sp9]; exact rd58)
  obtain ⟨e2, de2, ue2⟩ := ue1.aluImm hc9 fsr_at_22 (off' := 0x24) (by decide)
  obtain ⟨e3, de3, pc3, mem3, regs3⟩ := ue2.jalr hc9 fsr_at_24
  have lP : ∀ i, i < 10 → limbAt P1 xp i = limbAt m.mem xp i := fun i hi => by
    unfold limbAt
    rw [load_frame fpro (show Sep (F + 0x58) 8 (xp + BitVec.ofNat 32 (4 * i)) 4 from by
      rw [show F + 0x58 = G + BitVec.ofNat 32 0xA8 from fG (c := 0x58)]
      exact (sXG.subR (c := 0xA8) (l := 8) (by decide)).symm.subR (c := 4 * i) (l := 4) (by omega))]
  have hz5 := out5
  rw [mem4, lP 0 (by decide), lP 1 (by decide), lP 2 (by decide), lP 3 (by decide), lP 4 (by decide),
    lP 5 (by decide), lP 6 (by decide), lP 7 (by decide), lP 8 (by decide), lP 9 (by decide)] at hz5
  have pass : ∀ q, feSquareKeep q = true → q ≠ sp → q ≠ ra → q ≠ (8 : Fin 32) → reg m9 q = reg m q :=
    fun q hq h1 h2 h3 => by
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; rw [w9.zero, hz]
      have hk : frKeep q = true := by revert hq; revert q; decide
      have hk' : fsqKeep q = true := by revert hq; revert q; decide
      have na0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
      have na1 : q ≠ a1 := fun e => by subst e; exact absurd hq (by decide)
      rw [k9 q hk, r8 q h2, upd_ne h0 na0, upd_ne h0 na1, k5 q hk', r4 q h2, upd_ne h0 na0, upd_ne h0 h3,
        rk1 q h1]
  refine ⟨e3, .cons d1 (.cons dp0 (.cons dp1 (.cons dp2 (.cons dp3 (c4.trans (c5.trans (.cons dp6 (.cons dp7 (c8.trans (c9.trans (.cons de0 (.cons de1 (.cons de2 (.single de3)))))))))))))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [add_lit_zero, hra, hret]
  · rw [regs3]; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [sp9, hspF]
  · intro q hq
    rw [regs3]
    by_cases hs : q = sp
    · subst hs; simp +decide only [upd_app, ↓reduceIte, aluEval]; rw [sp9, hspF, hsp]
    by_cases hr : q = ra
    · subst hr; simp +decide only [upd_app, ↓reduceIte]
    by_cases h8 : q = (8 : Fin 32)
    · subst h8; simp +decide only [upd_app, ↓reduceIte]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact hz.symm
    rw [upd_ne h0 hs, upd_ne h0 h8, upd_ne h0 hr]
    exact pass q hq hs hr h8
  · rw [mem3, out9, mem8]
    simp only [feSquareSpec]
    rw [← hz5]
    rfl
  · intro x hx ho
    rw [mem3, fr9G x hx ho]

end C3.RV32
