import C3BootProofs.Proofs.FeToBytesBody
import C3BootProofs.Proofs.FeReduce
import C3BootProofs.Proofs.Sha256LoopFrame

/-!
# `FieldElement2625::to_bytes`, as compiled

`to_bytes` copies the ten limbs into a frame as `u64`s, calls `reduce` on
them, and then computes the quotient by `p = 2^255 - 19`, carries, and packs
the 32 bytes in the straight-line tail that `FeToBytesBody` proves.
-/

namespace C3.RV32

open C3.Image

/-- `feToBytesSpec` of a list of ten limbs. -/
def feToBytesOf (l : List Nat) : List Nat :=
  feToBytesSpec (l.getD 0 0) (l.getD 1 0) (l.getD 2 0) (l.getD 3 0) (l.getD 4 0) (l.getD 5 0) (l.getD 6 0)
    (l.getD 7 0) (l.getD 8 0) (l.getD 9 0)

/-- The registers the function saves, at offsets from its `sp`. -/
abbrev tbPs : List (Fin 32 × Word) := [(ra, 0x8C), ((8 : Fin 32), 0x88), ((9 : Fin 32), 0x84), ((18 : Fin 32), 0x80)]

/-- From 0xA to the call at 0x54: keep `out`, and copy the limbs into the
frame as `u64`s for `reduce`. -/
def tbCopy : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a0, .lw a0 a1 0x0, .lw a2 a1 0x4, .lw a3 a1 0x8, .lw a4 a1 0xC, .lw a5 a1 0x10,
   .lw a6 a1 0x14, .lw (17 : Fin 32) a1 0x18, .lw (5 : Fin 32) a1 0x1C, .lw (6 : Fin 32) a1 0x20, .lw a1 a1 0x24,
   .sw sp a0 0x30, .sw sp x0 0x34, .sw sp a2 0x38, .sw sp x0 0x3C, .sw sp a3 0x40, .sw sp x0 0x44,
   .sw sp a4 0x48, .sw sp x0 0x4C, .sw sp a5 0x50, .sw sp x0 0x54, .sw sp a6 0x58, .sw sp x0 0x5C,
   .sw sp (17 : Fin 32) 0x60, .sw sp x0 0x64, .sw sp (5 : Fin 32) 0x68, .sw sp x0 0x6C, .sw sp (6 : Fin 32) 0x70,
   .sw sp x0 0x74, .sw sp a1 0x78, .sw sp x0 0x7C, .aluImm .add a0 sp 0x8, .aluImm .add a1 sp 0x30]

section
set_option maxRecDepth 20000
theorem tbSave_end : blockEnd feToBytesCode 2 (saveBlock tbPs) = some 0xA := by decide
theorem tbCopy_end : blockEnd feToBytesCode 0xA tbCopy = some 0x54 := by decide
theorem tbRestore_end : blockEnd feToBytesCode 0x204 (restoreBlock tbPs) = some 0x20C := by decide
end

/-- The frame after the prologue's copy: the limbs at `fp` as ten `u64`s at
`F + 0x30`. -/
def tbCopyMem (M : Word → BitVec 8) (F fp : Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (M) (F + 48) (memLoad32 M (fp + 0))) (F + 52) 0) (F + 56) (memLoad32 M (fp + 4))) (F + 60) 0) (F + 64) (memLoad32 M (fp + 8))) (F + 68) 0) (F + 72) (memLoad32 M (fp + 12))) (F + 76) 0) (F + 80) (memLoad32 M (fp + 16))) (F + 84) 0) (F + 88) (memLoad32 M (fp + 20))) (F + 92) 0) (F + 96) (memLoad32 M (fp + 24))) (F + 100) 0) (F + 104) (memLoad32 M (fp + 28))) (F + 108) 0) (F + 112) (memLoad32 M (fp + 32))) (F + 116) 0) (F + 120) (memLoad32 M (fp + 36))) (F + 124) 0

set_option maxRecDepth 20000 in
theorem tbCopy_u64 (M : Word → BitVec 8) (F fp : Word) :
    ∀ i, i < 10 → u64At (tbCopyMem M F fp) (F + 0x30) i = (memLoad32 M (fp + BitVec.ofNat 32 (4 * i))).toNat := by
  intro i hi
  have e : ∀ j, (F + 0x30 + BitVec.ofNat 32 j) = F + BitVec.ofNat 32 (0x30 + j) := fun j => by
    rw [show (0x30 : Word) = BitVec.ofNat 32 0x30 from rfl, add_ofNat_assoc]
  unfold u64At
  rw [e, e]
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [tbCopyMem]
    simp (disch := decide) only [ls_lit, ls_same]
    rfl

/-- The frame's words that the copy writes: `F + 0x30` to `F + 0x80`. -/
theorem tbCopy_out {M : Word → BitVec 8} {F fp x : Word} (hx : Sep (F + BitVec.ofNat 32 0x30) 0x50 x 1) :
    tbCopyMem M F fp x = M x := by
  have s : ∀ c, 0x30 ≤ c → c + 4 ≤ 0x80 → Sep (F + BitVec.ofNat 32 c) 4 x 1 := fun c h1 h2 => by
    have := hx.sub (c := c - 0x30) (l := 4) (by omega)
    rwa [add_ofNat_assoc, show 0x30 + (c - 0x30) = c by omega] at this
  simp only [tbCopyMem]
  rw [memStore32_get_sep (a := F + 124) (s 124 (by decide) (by decide)),
    memStore32_get_sep (a := F + 120) (s 120 (by decide) (by decide)),
    memStore32_get_sep (a := F + 116) (s 116 (by decide) (by decide)),
    memStore32_get_sep (a := F + 112) (s 112 (by decide) (by decide)),
    memStore32_get_sep (a := F + 108) (s 108 (by decide) (by decide)),
    memStore32_get_sep (a := F + 104) (s 104 (by decide) (by decide)),
    memStore32_get_sep (a := F + 100) (s 100 (by decide) (by decide)),
    memStore32_get_sep (a := F + 96) (s 96 (by decide) (by decide)),
    memStore32_get_sep (a := F + 92) (s 92 (by decide) (by decide)),
    memStore32_get_sep (a := F + 88) (s 88 (by decide) (by decide)),
    memStore32_get_sep (a := F + 84) (s 84 (by decide) (by decide)),
    memStore32_get_sep (a := F + 80) (s 80 (by decide) (by decide)),
    memStore32_get_sep (a := F + 76) (s 76 (by decide) (by decide)),
    memStore32_get_sep (a := F + 72) (s 72 (by decide) (by decide)),
    memStore32_get_sep (a := F + 68) (s 68 (by decide) (by decide)),
    memStore32_get_sep (a := F + 64) (s 64 (by decide) (by decide)),
    memStore32_get_sep (a := F + 60) (s 60 (by decide) (by decide)),
    memStore32_get_sep (a := F + 56) (s 56 (by decide) (by decide)),
    memStore32_get_sep (a := F + 52) (s 52 (by decide) (by decide)),
    memStore32_get_sep (a := F + 48) (s 48 (by decide) (by decide))]

/-- Where `to_bytes` runs: its code and `reduce`'s, its 0x90-byte frame and
the 0x20 bytes below it that `reduce` uses, the output `out`, and the input
limbs at `fp`, apart from what each must not touch. -/
structure TBEnv (M : Word → BitVec 8) (P sp0 out fp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P feToBytesCode
  red : CodeIn M (P + 0x210) feReduceCode
  hsp : sp0.toNat % 4 = 0
  hS : 0xB0 ≤ sp0.toNat
  hfp : fp.toNat % 4 = 0
  sC : Sep (sp0 + 0xFFFFFF50) 0xB0 P feToBytesCode.length
  sR : Sep (sp0 + 0xFFFFFF50) 0xB0 (P + 0x210) feReduceCode.length
  sOC : Sep out 32 P feToBytesCode.length
  sOR : Sep out 32 (sp0 + 0xFFFFFF50) 0xB0
  sIR : Sep fp 40 (sp0 + 0xFFFFFF50) 0xB0

/-- The registers `to_bytes` leaves alone. -/
def tbKeep (q : Fin 32) : Bool := q.val ∉ [5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **The compiled `FieldElement2625::to_bytes`**, called with `out` and the
limbs at `fp`: it stores at `out` the 32 bytes of `feToBytesSpec` applied to
`reduce`'s output for the limbs as `u64`s, returns with `sp` and the
callee-saved registers restored, and changes memory only in its 0xB0-byte
stack region and `out`. -/
theorem feToBytes_correct (m : Machine) {P sp0 out fp retAddr : Word} (env : TBEnv m.mem P sp0 out fp)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = fp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, tbKeep q = true → reg m' q = reg m q) ∧
      memBytes m'.mem out 32 = feToBytesOf (feReduceSpec (memLoad32 m.mem fp).toNat
        (memLoad32 m.mem (fp + 0x4)).toNat (memLoad32 m.mem (fp + 0x8)).toNat (memLoad32 m.mem (fp + 0xC)).toNat
        (memLoad32 m.mem (fp + 0x10)).toNat (memLoad32 m.mem (fp + 0x14)).toNat
        (memLoad32 m.mem (fp + 0x18)).toNat (memLoad32 m.mem (fp + 0x1C)).toNat
        (memLoad32 m.mem (fp + 0x20)).toNat (memLoad32 m.mem (fp + 0x24)).toNat) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF50) 0xB0 x 1 → Sep out 32 x 1 → m'.mem x = m.mem x := by
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFF70 = F := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, sp0 + 0xFFFFFF50 = R := ⟨_, rfl⟩
  have hRF : R + BitVec.ofNat 32 0x20 = F := by rw [← hR, ← hF, BitVec.add_assoc]; rfl
  have hFR : F + 0xFFFFFFE0 = R := by rw [← hRF, BitVec.add_assoc]; exact BitVec.add_zero R
  have sC := env.sC; have sRd := env.sR; have sOR := env.sOR; have sIR := env.sIR
  rw [hR] at sC sRd sOR sIR ⊢
  have hRw : R.toNat + 0xB0 = sp0.toNat := by
    rw [← hR, BitVec.toNat_add, show (0xFFFFFF50 : Word).toNat = 4294967120 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have hRa : R.toNat % 4 = 0 := by rw [← hR]; exact aligned_add env.hsp (k := 0xFFFFFF50) (by decide)
  have hFa : F.toNat % 4 = 0 := by rw [← hRF]; exact aligned_add hRa (by decide)
  -- the frame is the region from 0x20 on
  have inF : ∀ {x : Word} {c l : Nat}, c + l ≤ 0x90 → Sep R 0xB0 x 1 → Sep (F + BitVec.ofNat 32 c) l x 1 :=
    fun h hx => by rw [← hRF, add_ofNat_assoc]; exact hx.sub (by omega)
  have sFC : Sep F 0x90 P feToBytesCode.length := by
    rw [← hRF]; exact sC.sub (c := 0x20) (l := 0x90) (by decide)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep R 0xB0 b code.length → (∀ x, Sep R 0xB0 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  -- the prologue: the frame, the saves, and the copy of the limbs
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code tb_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF70) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock tbPs) u1 env.code tbSave_end (saveBlock_ok _ tbPs _ fun p hp => by
    rw [sp1]
    simp only [tbPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> exact ⟨fr_al' hFa (by decide), frm_sep' sFC (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF70)) tbPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep F 0x90 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside tbPs fun p hp => by
      simp only [tbPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> exact frm_sep' hx (by decide)
  have frSvR : ∀ x, Sep R 0xB0 x 1 → Msv x = m.mem x := fun x hx =>
    frSv x (by have := inF (c := 0) (l := 0x90) (by decide) hx; rwa [add_ofNat_zero] at this)
  have hslv : ∀ r o, (r, o) ∈ tbPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [tbPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ r, reg m2 r = upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF70) r := u2.regs
  have ra2 : reg m2 a1 = fp := by rw [r2]; simp +decide only [upd_app, ↓reduceIte]; exact ha1
  have hcS := cIn env.code sC frSvR
  -- the limbs, read past the saves
  have lw : ∀ j, j + 4 ≤ 40 → memLoad32 Msv (fp + BitVec.ofNat 32 j) = memLoad32 m.mem (fp + BitVec.ofNat 32 j) :=
    fun j hj => memLoad32_congr fun t ht => by
      rw [add_ofNat_assoc]; exact frSvR _ (sIR.symm.subR (c := j + t) (l := 1) (by omega))
  have sp2 : reg m2 sp = F := by rw [r2, sp1]
  have a02 : reg m2 a0 = out := by rw [r2]; simp +decide only [upd_app, ↓reduceIte]; exact ha0
  have z2 : reg m2 0 = 0 := u2.self.zero
  obtain ⟨m3, c3, u3⟩ := St.block tbCopy u2.self hcS tbCopy_end (by
    simp only [BlockOk, BInstr.ok, tbCopy]
    simp +decide only [upd_app, ↓reduceIte, BInstr.run, ra2, sp2, z2, a02]
    repeat' constructor
    all_goals first
      | exact aligned_add env.hfp (by decide)
      | exact fr_al' hFa (by decide)
      | exact frm_sep' sFC (by decide))
  simp only [runBlock, BInstr.run, tbCopy] at u3
  simp +decide only [upd_app, ↓reduceIte, ra2, sp2, z2, a02] at u3
  obtain ⟨Mc, hMc⟩ : ∃ Mc, tbCopyMem Msv F fp = Mc := ⟨_, rfl⟩
  have u3c : St Mc P m3 0x54 (reg m3) := by rw [← hMc]; exact u3.self
  have g3 : ∀ r, reg m3 r = _ := u3.regs
  have v3 : reg m3 sp = F ∧ reg m3 8 = out ∧ reg m3 a0 = F + 8 ∧ reg m3 a1 = F + 0x30 := by
    simp +decide only [g3, upd_app, ↓reduceIte, sp2]
    exact ⟨trivial, BitVec.zero_add out, ev_add _ _, ev_add _ _⟩
  obtain ⟨sp3, s03, a03, a13⟩ := v3
  have k3 : ∀ q : Fin 32, q.val ∉ [5, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17] → reg m3 q = reg m2 q := fun q hq => by
    rw [g3]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact z2.symm
    have ne : ∀ r : Fin 32, r.val ∈ [5, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17] → q ≠ r := fun r hr e => hq (e ▸ hr)
    simp only [upd_app, h0, ne a0 (by decide), ne a1 (by decide), ne a2 (by decide), ne a3 (by decide),
      ne a4 (by decide), ne a5 (by decide), ne a6 (by decide), ne 17 (by decide), ne 5 (by decide),
      ne 6 (by decide), ne 8 (by decide), ite_false]
  have frC : ∀ x, Sep R 0xB0 x 1 → Mc x = m.mem x := fun x hx => by
    rw [← hMc, tbCopy_out (inF (c := 0x30) (l := 0x50) (by decide) hx), frSvR x hx]
  have hu : ∀ i, i < 10 → u64At Mc (F + 0x30) i = (memLoad32 m.mem (fp + BitVec.ofNat 32 (4 * i))).toNat :=
    fun i hi => by rw [← hMc, tbCopy_u64 _ _ _ i hi, lw _ (by omega)]
  -- `reduce` on the ten `u64`s at `F + 0x30`, into `F + 8`
  have hcC := cIn env.code sC frC
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3c.callRa hcC tb_at_54 tb_at_58 (cb := P + 0x210)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x210 (by decide))
  have r4 := PEnv.reg1 regs4 u3c.zero
  have eR8 : R + BitVec.ofNat 32 0x28 = F + 8 := by rw [← hRF, BitVec.add_assoc]; rfl
  have eR30 : R + BitVec.ofNat 32 0x50 = F + 0x30 := by rw [← hRF, BitVec.add_assoc]; rfl
  have RE : FREnv m4.mem (P + 0x210) F (F + 8) (F + 0x30) := by
    rw [mem4]
    refine ⟨even_at P env.hP 0x210 (by decide), cIn env.red sRd frC, hFa, by
      rw [← hRF, BitVec.toNat_add]; show 32 ≤ (R.toNat + 32) % 2 ^ 32; omega, fr_al' hFa (by decide),
      fr_al' hFa (by decide),
      ?_, ?_, ?_, ?_⟩
    · rw [hFR]; have := sRd.sub (c := 0) (l := 0x20) (by decide); rwa [add_ofNat_zero] at this
    · rw [← eR8]; exact sRd.sub (c := 0x28) (l := 40) (by decide)
    · rw [hFR, ← eR8]
      have := sep_offsets R (c := 0x28) (n := 40) (d := 0) (k := 0x20) (.inr (by decide)) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
    · rw [hFR, ← eR30]
      have := sep_offsets R (c := 0x50) (n := 80) (d := 0) (k := 0x20) (.inr (by decide)) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
  obtain ⟨m5, c5, pc5, sp5, k5, outR, frR⟩ := feReduce_correct m4 RE pc4 (by rw [r4 a0 (by decide), a03])
    (by rw [r4 a1 (by decide), a13]) (by rw [regs4]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P env.hP (0x54 + 8) (by decide))) (by rw [r4 sp (by decide), sp3])
  rw [mem4] at outR frR
  rw [hFR] at frR
  have fr5 : ∀ x, Sep R 0xB0 x 1 → m5.mem x = m.mem x := fun x hx => by
    rw [frR x (by have := hx.sub (c := 0) (l := 0x20) (by decide); rwa [add_ofNat_zero] at this)
      (by rw [← eR8]; exact hx.sub (c := 0x28) (l := 40) (by decide)), frC x hx]
  have s05 : reg m5 8 = out := by rw [k5 8 (by decide), r4 8 (by decide), s03]
  have u5 : St m5.mem P m5 0x5C (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  -- the tail: the quotient, the carries, and the bytes
  obtain ⟨n6, M6, c6, u6, hc6, frO, bytes6, k6⟩ := tb_body u5 (cIn env.code sC fr5) sp5 s05 hFa env.sOC
  -- `reduce`'s words, as the tail reads them
  have e8 : ∀ j, F + 8 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (8 + j) := fun j => by
    rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, add_ofNat_assoc]
  have hw : (wordsAt m5.mem (F + 8) 10).map BitVec.toNat = [(memLoad32 m5.mem (F + 0x8)).toNat,
      (memLoad32 m5.mem (F + 0xC)).toNat, (memLoad32 m5.mem (F + 0x10)).toNat, (memLoad32 m5.mem (F + 0x14)).toNat,
      (memLoad32 m5.mem (F + 0x18)).toNat, (memLoad32 m5.mem (F + 0x1C)).toNat, (memLoad32 m5.mem (F + 0x20)).toNat,
      (memLoad32 m5.mem (F + 0x24)).toNat, (memLoad32 m5.mem (F + 0x28)).toNat, (memLoad32 m5.mem (F + 0x2C)).toNat] := by
    show [(memLoad32 m5.mem (F + 8 + BitVec.ofNat 32 (4 * 0))).toNat, (memLoad32 m5.mem (F + 8 + BitVec.ofNat 32 (4 * 1))).toNat,
      (memLoad32 m5.mem (F + 8 + BitVec.ofNat 32 (4 * 2))).toNat, (memLoad32 m5.mem (F + 8 + BitVec.ofNat 32 (4 * 3))).toNat,
      (memLoad32 m5.mem (F + 8 + BitVec.ofNat 32 (4 * 4))).toNat, (memLoad32 m5.mem (F + 8 + BitVec.ofNat 32 (4 * 5))).toNat,
      (memLoad32 m5.mem (F + 8 + BitVec.ofNat 32 (4 * 6))).toNat, (memLoad32 m5.mem (F + 8 + BitVec.ofNat 32 (4 * 7))).toNat,
      (memLoad32 m5.mem (F + 8 + BitVec.ofNat 32 (4 * 8))).toNat, (memLoad32 m5.mem (F + 8 + BitVec.ofNat 32 (4 * 9))).toNat] = _
    simp only [e8]
    rfl
  have hspec : feReduceSpec (memLoad32 m.mem fp).toNat (memLoad32 m.mem (fp + 0x4)).toNat
      (memLoad32 m.mem (fp + 0x8)).toNat (memLoad32 m.mem (fp + 0xC)).toNat (memLoad32 m.mem (fp + 0x10)).toNat
      (memLoad32 m.mem (fp + 0x14)).toNat (memLoad32 m.mem (fp + 0x18)).toNat (memLoad32 m.mem (fp + 0x1C)).toNat
      (memLoad32 m.mem (fp + 0x20)).toNat (memLoad32 m.mem (fp + 0x24)).toNat =
      (wordsAt m5.mem (F + 8) 10).map BitVec.toNat := by
    rw [outR, hu 0 (by decide), hu 1 (by decide), hu 2 (by decide), hu 3 (by decide), hu 4 (by decide),
      hu 5 (by decide), hu 6 (by decide), hu 7 (by decide), hu 8 (by decide), hu 9 (by decide),
      show 4 * 0 = 0 from rfl, add_ofNat_zero]
    rfl
  -- the epilogue
  have slot6 : ∀ r o, (r, o) ∈ tbPs → memLoad32 M6 (F + o) = reg m r := fun r o h => by
    have ho : 0x80 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x90 := by
      simp only [tbPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    rw [← hslv r o h]
    apply memLoad32_congr; intro j hj
    have e : F + o + BitVec.ofNat 32 j = R + BitVec.ofNat 32 (0x20 + o.toNat + j) := by
      conv => lhs; rw [← ofNat_toNat_self o]
      rw [← hRF, add_ofNat_assoc, add_ofNat_assoc, Nat.add_assoc]
    rw [e, frO _ (sOR.subR (c := 0x20 + o.toNat + j) (l := 1) (by omega)),
      frR _ (by
          have := sep_offsets R (c := 0) (n := 0x20) (d := 0x20 + o.toNat + j) (k := 1) (.inl (by omega)) (by omega)
            (by omega)
          rwa [add_ofNat_zero] at this)
        (by rw [← eR8]; exact sep_offsets R (.inl (by omega)) (by omega) (by omega)),
      ← hMc, tbCopy_out (by
        rw [show F + BitVec.ofNat 32 0x30 = R + BitVec.ofNat 32 0x50 from eR30.symm]
        exact sep_offsets R (.inl (by omega)) (by omega) (by omega))]
  have sp6 : reg n6 sp = F := by rw [k6 sp (by decide), sp5]
  obtain ⟨n7, c7, u7⟩ := St.block (restoreBlock tbPs) u6 hc6 tbRestore_end
    (restoreBlock_ok M6 _ tbPs (reg n6) sp6 (by decide) fun p hp => by
      simp only [tbPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> exact fr_al' hFa (by decide))
  simp only [restoreBlock_run M6 _ tbPs (reg n6) sp6 (by decide)] at u7
  obtain ⟨n8, d8, u8⟩ := u7.aluImm hc6 tb_at_20c (off' := 0x20E) (by decide)
  obtain ⟨n9, d9, pc9, mem9, regs9⟩ := u8.jalr hc6 tb_at_20e
  have rsp7 : restoreRegs M6 F (reg n6) tbPs sp = F := by rw [restoreRegs_sp _ _ _ _ (by decide)]; exact sp6
  have eS : F + 0x90 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  refine ⟨n9, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (.cons d8 (.single d9)))))))),
    ?_, ?_, fun q hq => ?_, ?_, fun x hx ho => ?_⟩
  · rw [pc9]; simp +decide only [upd_app, ↓reduceIte]
    simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
    rw [slot6 ra 0x8C (by decide), hra, add_lit_zero, hret]
  · rw [regs9]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp7, ev_add, eS]
  · rw [regs9]
    by_cases hs : q = sp
    · subst hs; simp +decide only [upd_app, ↓reduceIte]; rw [rsp7, ev_add, eS, hsp]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact hz.symm
    simp only [upd_app, h0, hs, ite_false]
    by_cases hr : q = ra
    · subst hr; simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]; exact slot6 ra 0x8C (by decide)
    by_cases h8 : q = 8
    · subst h8; simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]; exact slot6 8 0x88 (by decide)
    by_cases h9 : q = 9
    · subst h9; simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]; exact slot6 9 0x84 (by decide)
    by_cases h18 : q = 18
    · subst h18; simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]; exact slot6 18 0x80 (by decide)
    simp only [restoreRegs, upd_app, h0, hr, h8, h9, h18, ite_false]
    have hb : tbBodyKeep q = true :=
      (by decide : ∀ q : Fin 32, tbKeep q = true → q ≠ 9 → q ≠ 18 → tbBodyKeep q = true) q hq h9 h18
    have hk5 : frKeep q = true := (by decide : ∀ q : Fin 32, tbKeep q = true → frKeep q = true) q hq
    rw [k6 q hb, k5 q hk5, r4 q hr, k3 q ((by decide : ∀ q : Fin 32, tbKeep q = true → q ≠ 8 →
      q.val ∉ [5, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17]) q hq h8), r2]
    exact updz hz hs
  · rw [mem9, bytes6, hspec, hw]; rfl
  · rw [mem9, frO x ho, fr5 x hx]

end C3.RV32
