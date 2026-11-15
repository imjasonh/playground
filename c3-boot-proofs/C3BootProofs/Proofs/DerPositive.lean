import C3BootProofs.Proofs.DerOptional

/-!
# `Der::positive_integer`, as compiled

`Der::positive_integer` reads an `INTEGER` through the proved
`Der::integer` into its 16-byte frame, then rejects the single byte 0x00 and
a first byte with its top bit set, so the value is positive. Its result is a
`Result<&[u8], Error>`, as `Der::integer`'s is. The stack region is its own
frame and `Der::integer`'s 0x20 bytes below it.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem dpi_at_0 : fetchRel derPositiveIntegerCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem dpi_at_6 : fetchRel derPositiveIntegerCode 0x6 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem dpi_at_8 : fetchRel derPositiveIntegerCode 0x8 = some (.alu .add a0 x0 sp, 2) := by decide
theorem dpi_at_a : fetchRel derPositiveIntegerCode 0xA = some (.auipc ra 0x0, 4) := by decide
theorem dpi_at_e : fetchRel derPositiveIntegerCode 0xE = some (.jalr ra ra 0x68, 4) := by decide
theorem dpi_at_12 : fetchRel derPositiveIntegerCode 0x12 = some (.load .lw a0 sp 0x0, 2) := by decide
theorem dpi_at_14 : fetchRel derPositiveIntegerCode 0x14 = some (.branch .beq a0 x0 0x14, 2) := by decide
theorem dpi_at_16 : fetchRel derPositiveIntegerCode 0x16 = some (.load .lw a1 sp 0x4, 2) := by decide
theorem dpi_at_18 : fetchRel derPositiveIntegerCode 0x18 = some (.branch .beq a1 x0 0x20, 2) := by decide
theorem dpi_at_1a : fetchRel derPositiveIntegerCode 0x1A = some (.aluImm .add a2 x0 0x1, 2) := by decide
theorem dpi_at_1c : fetchRel derPositiveIntegerCode 0x1C = some (.branch .bne a1 a2 0x12, 4) := by decide
theorem dpi_at_20 : fetchRel derPositiveIntegerCode 0x20 = some (.load .lbu a2 a0 0x0, 4) := by decide
theorem dpi_at_24 : fetchRel derPositiveIntegerCode 0x24 = some (.branch .bne a2 x0 0xE, 2) := by decide
theorem dpi_at_26 : fetchRel derPositiveIntegerCode 0x26 = some (.jal x0 0x18, 2) := by decide
theorem dpi_at_28 : fetchRel derPositiveIntegerCode 0x28 = some (.load .lbu a0 sp 0x4, 4) := by decide
theorem dpi_at_2c : fetchRel derPositiveIntegerCode 0x2C = some (.jal x0 0x14, 2) := by decide
theorem dpi_at_2e : fetchRel derPositiveIntegerCode 0x2E = some (.load .lbu a2 a0 0x0, 4) := by decide
theorem dpi_at_32 : fetchRel derPositiveIntegerCode 0x32 = some (.aluImm .sll a2 a2 0x18, 2) := by decide
theorem dpi_at_34 : fetchRel derPositiveIntegerCode 0x34 = some (.branch .blt a2 x0 0xA, 4) := by decide
theorem dpi_at_38 : fetchRel derPositiveIntegerCode 0x38 = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem dpi_at_3a : fetchRel derPositiveIntegerCode 0x3A = some (.store .sw (8 : Fin 32) a1 0x4, 2) := by decide
theorem dpi_at_3c : fetchRel derPositiveIntegerCode 0x3C = some (.jal x0 0xC, 2) := by decide
theorem dpi_at_3e : fetchRel derPositiveIntegerCode 0x3E = some (.aluImm .add a0 x0 0x14, 2) := by decide
theorem dpi_at_40 : fetchRel derPositiveIntegerCode 0x40 = some (.store .sw (8 : Fin 32) x0 0x0, 4) := by decide
theorem dpi_at_44 : fetchRel derPositiveIntegerCode 0x44 = some (.store .sb (8 : Fin 32) a0 0x4, 4) := by decide
theorem dpi_at_4c : fetchRel derPositiveIntegerCode 0x4C = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem dpi_at_4e : fetchRel derPositiveIntegerCode 0x4E = some (.jalr x0 ra 0x0, 2) := by decide
theorem dpiSave_end : blockEnd derPositiveIntegerCode 2 (saveBlock [(ra, 0xC), ((8 : Fin 32), 8)]) = some 6 := by
  decide
theorem dpiRestore_end : blockEnd derPositiveIntegerCode 0x48 (restoreBlock [(ra, 0xC), ((8 : Fin 32), 8)]) =
    some 0x4C := by decide
end

/-- `Der::positive_integer`'s result for the unread bytes `L` starting at
`rp`, given `Der::element`'s result `r` for tag 2: `Der::integer`'s, unless
the contents are the single byte 0x00 or start with a byte of 0x80 or more. -/
def derPosIntOf (L : Bytes) (rp : Word) (r : Except DerError DerTlv) : Except DerError (Word × Word) :=
  match r, derIntOf L rp r with
  | .ok t, .ok pl =>
    if (t.len = 1 ∧ L.getD t.header 0 = 0) ∨ 0x80 ≤ L.getD t.header 0 then .error .badDer else .ok pl
  | _, x => x

theorem derPosIntOf_err {L : Bytes} {rp : Word} {r : Except DerError DerTlv} {e : DerError}
    (h : derIntOf L rp r = .error e) : derPosIntOf L rp r = .error e := by
  cases r <;> simp only [derPosIntOf, h]

theorem pi_sign : ∀ b : BitVec 8,
    branchTaken .blt (aluEval .sll (b.zeroExtend 32) 0x18) 0 = decide (0x80 ≤ b.toNat) := by decide

/-- Where `Der::positive_integer` runs: its code and its callees', the 0x30
bytes of stack below `sp0`, the result `out`, the reader at `d`, and the
reader's unread bytes, apart from what each must not touch. -/
structure PIEnv (M : Word → BitVec 8) (P sp0 out d : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P derPositiveIntegerCode
  int : CodeIn M (P + 0x72) derIntegerCode
  elem : CodeIn M (P + 0x72 + 0x5E) derElementCode
  tlv : CodeIn M (P + 0x72 + 0x5E + 0x26) derTlvCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x30 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hd : d.toNat % 4 = 0
  sGC : Sep (sp0 + 0xFFFFFFD0) 0x30 P derPositiveIntegerCode.length
  sGI : Sep (sp0 + 0xFFFFFFD0) 0x30 (P + 0x72) derIntegerCode.length
  sGE : Sep (sp0 + 0xFFFFFFD0) 0x30 (P + 0x72 + 0x5E) derElementCode.length
  sGT : Sep (sp0 + 0xFFFFFFD0) 0x30 (P + 0x72 + 0x5E + 0x26) derTlvCode.length
  sOC : Sep out 8 P derPositiveIntegerCode.length
  sDC : Sep (d + 8) 8 P derPositiveIntegerCode.length
  sDI : Sep (d + 8) 8 (P + 0x72) derIntegerCode.length
  sDT : Sep (d + 8) 8 (P + 0x72 + 0x5E + 0x26) derTlvCode.length
  sOG : Sep out 8 (sp0 + 0xFFFFFFD0) 0x30
  sDG : Sep (d + 8) 8 (sp0 + 0xFFFFFFD0) 0x30
  sRG : Sep (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat (sp0 + 0xFFFFFFD0) 0x30
  sDR : Sep (d + 8) 8 (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat
  sOR : Sep out 8 (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat
  sOD : Sep out 8 (d + 8) 8
  hrp : 0 < (memLoad32 M (d + 8)).toNat
  hrw : (memLoad32 M (d + 8)).toNat + (memLoad32 M (d + 0xC)).toNat < 2 ^ 32

theorem slice_ld0 {M : Word → BitVec 8} {out : Word} (r : Except DerError (Word × Word)) :
    memLoad32 (derSliceMem M out r) out = match r with | .error _ => 0 | .ok (p, _) => p := by
  cases r with
  | error e =>
    simp only [derSliceMem]
    rw [memLoad32_congr fun j hj => memStore8_ne fun e' => by
      have := add_ofNat_ne out (c := 4) (d := j) (by omega) (by omega) (by omega)
      exact this (by rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl] at e'; exact e'.symm)]
    exact memLoad32_store32_same _ _ _
  | ok pl =>
    obtain ⟨p, l⟩ := pl
    simp only [derSliceMem]
    rw [memLoad32_store32_sep (sep_offsets out (c := 4) (n := 4) (d := 0) (k := 4) (.inr (by decide)) (by decide)
      (by decide) |> fun h => by rwa [add_ofNat_zero] at h)]
    exact memLoad32_store32_same _ _ _

theorem slice_ld4 {M : Word → BitVec 8} {out p l : Word} :
    memLoad32 (derSliceMem M out (.ok (p, l))) (out + 4) = l := memLoad32_store32_same _ _ _

theorem slice_b4 {M : Word → BitVec 8} {out : Word} (e : DerError) :
    derSliceMem M out (.error e) (out + 4) = derErrByte e := memStore8_same _ _ _

theorem slice_out {M : Word → BitVec 8} {out x : Word} (r : Except DerError (Word × Word)) (hx : Sep out 8 x 1) :
    derSliceMem M out r x = M x := by
  cases r with
  | error e =>
    simp only [derSliceMem]
    rw [memStore8_ne fun e' => hx.point (i := 4) (j := 0) (by decide) (by decide) (by rw [add_ofNat_zero]; exact e'.symm),
      memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)]
  | ok pl =>
    obtain ⟨p, l⟩ := pl
    simp only [derSliceMem]
    rw [memStore32_get_sep (a := out + 4) (hx.sub (c := 4) (l := 4) (by decide)),
      memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)]

theorem slice_pt {M M' : Word → BitVec 8} {out x : Word} (r : Except DerError (Word × Word)) (h : M x = M' x) :
    derSliceMem M out r x = derSliceMem M' out r x := by
  cases r with
  | error e => exact memStore8_pt (memStore32_pt h)
  | ok pl => obtain ⟨p, l⟩ := pl; exact memStore32_pt (memStore32_pt h)

abbrev piPs : List (Fin 32 × Word) := [(ra, 0xC), ((8 : Fin 32), 8)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `Der::positive_integer`**: with the reader at `d`, whose
unread bytes start at `rp` and number `rl`, it stores `derPosIntOf` of
`Der::element`'s result for tag 2 at `out`, and moves the reader past the
element when `Der::element` reads one. -/
theorem derPositiveInteger_correct (m : Machine) {P sp0 out d retAddr : Word} (env : PIEnv m.mem P sp0 out d)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = d)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, oidKeep q = true → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFD0) 0x30 x 1 →
        m'.mem x = derSliceMem (derAdvance m.mem d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
          (derElement 2 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat))) out
          (derPosIntOf (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)
            (memLoad32 m.mem (d + 8))
            (derElement 2 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat))) x := by
  have hrp0 := env.hrp; have hrw := env.hrw; have sRG := env.sRG; have sDR := env.sDR; have sOR := env.sOR
  generalize hRP : memLoad32 m.mem (d + 8) = rp at hrp0 hrw sRG sDR sOR ⊢
  generalize hRL : memLoad32 m.mem (d + 0xC) = rl at hrw sRG sDR sOR ⊢
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFFD0 = G := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFF0 = F := ⟨_, rfl⟩
  have sGC := env.sGC; have sGI := env.sGI; have sGE := env.sGE; have sGT := env.sGT; have sOG := env.sOG
  have sDG := env.sDG
  rw [hG] at sGC sGI sGE sGT sOG sDG sRG ⊢
  have hGF : G + 0x20 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFFD0) (by decide)
  have hFa : F.toNat % 4 = 0 := by rw [← hGF]; exact aligned_add hGa (k := 0x20) (by decide)
  have hGw : G.toNat + 0x30 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFFD0 : Word).toNat = 4294967248 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have hFn : F.toNat = G.toNat + 0x20 := by
    rw [← hGF, BitVec.toNat_add, show (0x20 : Word).toNat = 0x20 from rfl]; omega
  have eS : F + 0x10 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFG : F + 0xFFFFFFE0 = G := by rw [← hGF, BitVec.add_assoc]; exact BitVec.add_zero G
  -- the frame `[F, F + 0x10)` and `Der::integer`'s `[G, G + 0x20)` inside the region
  have inF : ∀ {b : Word} {l : Nat}, Sep G 0x30 b l → Sep F 0x10 b l := fun h => by
    rw [← hGF]; exact h.sub (c := 0x20) (l := 0x10) (by decide)
  have inI : ∀ {b : Word} {l : Nat}, Sep G 0x30 b l → Sep G 0x20 b l := fun h =>
    (h.sub (c := 0) (l := 0x20) (by decide)) |> fun h' => by rwa [add_ofNat_zero] at h'
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0x30 b code'.length → (∀ x, Sep G 0x30 x 1 → M' x = m.mem x) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod dpi_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFF0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock piPs) u1 env.cod dpiSave_end (saveBlock_ok _ piPs _ fun p hp => by
    rw [sp1]
    simp only [piPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨aligned_add hFa (k := 0xC) (by decide), (inF sGC).sub (by decide)⟩
    · exact ⟨aligned_add hFa (k := 8) (by decide), (inF sGC).sub (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFF0)) piPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep F 0x10 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside piPs fun p hp => by
      simp only [piPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact hx.sub (c := 0xC) (l := 4) (by decide)
      · exact hx.sub (c := 8) (l := 4) (by decide)
  have frSvG : ∀ x, Sep G 0x30 x 1 → Msv x = m.mem x := fun x hx => frSv x (inF hx)
  have frSvI : ∀ x, Sep F 0x10 x 1 → Msv x = m.mem x := frSv
  have hslv : ∀ r o, (r, o) ∈ piPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [piPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  have hcS : CodeIn Msv P derPositiveIntegerCode := cIn env.cod sGC frSvG
  obtain ⟨m3, c3, u3⟩ := St.block [.alu .add (8 : Fin 32) x0 a0, .alu .add a0 x0 sp] u2.self hcS (off' := 0xA)
    (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u3
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.callRa hcS dpi_at_a dpi_at_e (cb := P + 0x72)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x72 (by decide))
  have r4 := PEnv.reg1 regs4 u3.zero
  have hz8 : upd (reg m2) 8 (aluEval .add (reg m2 x0) (reg m2 a0)) 0 = 0 :=
    (updz (r := 0) u2.self.zero (by decide)).trans u2.self.zero
  have v4 : ∀ q, q ≠ ra → q ≠ a0 → q ≠ 8 → q ≠ sp → reg m4 q = reg m q := fun q hr h0 h8 hs => by
    rw [r4 q hr, updz hz8 h0, updz u2.self.zero h8, r2 q hs]
  have v4a0 : reg m4 a0 = F := by
    rw [r4 a0 (by decide)]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; exact zw F
  have v48 : reg m4 8 = out := by
    rw [r4 8 (by decide), updz hz8 (by decide)]
    simp +decide only [upd_app, ↓reduceIte]; rw [r2 a0 (by decide), ha0]; exact zw out
  have v4sp : reg m4 sp = F := by
    rw [r4 sp (by decide), updz hz8 (by decide),
      updz u2.self.zero (by decide), sp2]
  have v4a1 : reg m4 a1 = d := by rw [v4 a1 (by decide) (by decide) (by decide) (by decide), ha1]
  have eD8 : memLoad32 Msv (d + 8) = rp := by
    rw [← hRP]; exact memLoad32_congr fun j hj => frSvG _ (sDG.subR (c := j) (l := 1) (by omega) |>.symm |>
      fun h => h.symm |> fun h => (sDG.symm.subR (c := j) (l := 1) (by omega)).symm |> fun h' => h'.symm)
  have eDC : memLoad32 Msv (d + 0xC) = rl := by
    rw [← hRL]; exact memLoad32_congr fun j hj => frSvG _ (by
      rw [show d + 0xC = d + 8 + BitVec.ofNat 32 4 by rw [BitVec.add_assoc]; rfl, add_ofNat_assoc]
      exact sDG.symm.subR (by omega) |>.symm |> fun h => h.symm)
  have eL : memBytes Msv rp rl.toNat = memBytes m.mem rp rl.toNat :=
    memBytes_congr fun i hi => frSvG _ (sRG.symm.subR (c := i) (l := 1) (by omega) |>.symm |> fun h => h.symm)
  have sOCi : Sep F 8 (P + 0x72) derIntegerCode.length := by
    have := (inF sGI).sub (c := 0) (l := 8) (by decide); rwa [add_ofNat_zero] at this
  have sDFi : Sep (d + 8) 8 G 0x20 := by
    have := sDG.subR (c := 0) (l := 0x20) (by decide); rwa [add_ofNat_zero] at this
  have sRFi : Sep rp rl.toNat G 0x20 := by
    have := sRG.subR (c := 0) (l := 0x20) (by decide); rwa [add_ofNat_zero] at this
  have sOFi : Sep F 8 G 0x20 := by
    rw [← hGF]
    have := sep_offsets G (c := 0x20) (n := 8) (d := 0) (k := 0x20) (.inr (by decide)) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have hE : (P + 0x72 + 0x5E).toNat % 2 = 0 := by rw [BitVec.add_assoc]; exact even_at P env.hP 0xD0 (by decide)
  have hI : DerCallEnv m4.mem derIntegerCode (P + 0x72) 0x5E F F d 8 := by
    rw [mem4]
    refine ⟨even_at P env.hP 0x72 (by decide), hE, cIn env.int sGI frSvG, cIn env.elem sGE frSvG,
      cIn env.tlv sGT frSvG, hFa, by omega, hFa, env.hd, ?_, ?_, ?_, sOCi, env.sDI, env.sDT, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eFG]; exact inI sGI
    · rw [eFG]; exact inI sGE
    · rw [eFG]; exact inI sGT
    · rw [eFG]; exact sOFi
    · rw [eFG]; exact sDFi
    · rw [eFG, eD8, eDC]; exact sRFi
    · rw [eD8]; exact hrp0
    · rw [eD8, eDC]; exact hrw
  obtain ⟨m5, c5, pc5, sp5, k5, f5⟩ := derInteger_correct m4 hI (by rw [mem4, eD8, eDC]; exact sDR) pc4 v4sp v4a0
    v4a1 (by rw [regs4]; simp +decide [upd]) (even_clear _ (even_at P env.hP (0xA + 8) (by decide)))
  rw [mem4, eD8, eDC, eL, eFG] at f5
  generalize hr : derElement 2 (memBytes m.mem rp rl.toNat) = r at f5 ⊢
  generalize hR : derIntOf (memBytes m.mem rp rl.toNat) rp r = R at f5
  have memI : ∀ x, Sep G 0x30 x 1 → m5.mem x = derAdvance m.mem d rp rl r x := fun x hx => by
    have h8 : Sep F 8 x 1 := by have := (inF hx).sub (c := 0) (l := 8) (by decide); rwa [add_ofNat_zero] at this
    rw [f5 x (inI hx), slice_out R h8]
    exact derAdvance_pt r (frSvG x hx)
  have hc5 : CodeIn m5.mem P derPositiveIntegerCode := fun i hi => by
    rw [memI _ (sGC.subR (c := i) (l := 1) (by omega)), derAdvance_outside r (env.sDC.subR (c := i) (l := 1) (by omega))]
    exact env.cod i hi
  have u5 : St m5.mem P m5 0x12 (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  have S5 : Steps m m5 := .cons d1 (c2.trans (c3.trans (c4.trans c5)))
  have K5 : ∀ q, oidKeep q = true → q ≠ ra → q ≠ a0 → q ≠ 8 → q ≠ sp → reg m5 q = reg m q := fun q hq h1 h2 h3 h4 => by
    rw [k5 q hq, v4 q h1 h2 h3 h4]
  have s85 : reg m5 8 = out := by rw [k5 8 (by decide), v48]
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x20 + k) := fun k => by
    rw [← hGF, show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, add_ofNat_assoc]
  have outI : ∀ k, k < 0x10 → Sep G 0x20 (F + BitVec.ofNat 32 k) 1 := fun k hk => by
    rw [eFk]
    have := sep_offsets G (c := 0) (n := 0x20) (d := 0x20 + k) (k := 1) (.inl (by omega)) (by omega) (by omega)
    rwa [add_ofNat_zero] at this
  have ldW : ∀ k, k + 4 ≤ 0x10 → memLoad32 m5.mem (F + BitVec.ofNat 32 k) =
      memLoad32 (derSliceMem (derAdvance Msv d rp rl r) F R) (F + BitVec.ofNat 32 k) := fun k hk =>
    memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact f5 _ (outI _ (by omega))
  have slotV : ∀ k, 8 ≤ k → k < 0x10 → m5.mem (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) :=
    fun k h1 h2 => by
      have hs8 : Sep F 8 (F + BitVec.ofNat 32 k) 1 := by
        have := sep_offsets F (c := 0) (n := 8) (d := k) (k := 1) (.inl (by omega)) (by omega) (by omega)
        rwa [add_ofNat_zero] at this
      have hsd : Sep (d + 8) 8 (F + BitVec.ofNat 32 k) 1 := by
        rw [eFk]; exact sDG.subR (c := 0x20 + k) (l := 1) (by omega)
      rw [f5 _ (outI _ (by omega)), slice_out R hs8, derAdvance_outside r hsd]
  have hpsp : ∀ p ∈ piPs, p.1 ≠ sp := by decide
  -- the epilogue, from 0x48
  have fin : ∀ {Mx : Word → BitVec 8} {n : Machine}, Steps m5 n → St Mx P n 0x48 (reg n) →
      CodeIn Mx P derPositiveIntegerCode →
      (∀ k, 8 ≤ k → k < 0x10 → Mx (F + BitVec.ofNat 32 k) = m5.mem (F + BitVec.ofNat 32 k)) → reg n sp = F →
      (∀ q, oidKeep q = true → q ≠ ra → q ≠ 8 → q ≠ sp → reg n q = reg m q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ n'.mem = Mx ∧ reg n' sp = sp0 ∧
        ∀ q, oidKeep q = true → reg n' q = reg m q := by
    intro Mx n S st hc hsl rsp kq
    have slotW : ∀ r o, (r, o) ∈ piPs → memLoad32 Mx (F + o) = reg m r := fun r o h => by
      have ho : 8 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x10 := by
        simp only [piPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      rw [← hslv r o h]
      apply memLoad32_congr; intro j hj
      rw [← ofNat_toNat_self o, add_ofNat_assoc, hsl _ (by omega) (by omega), slotV _ (by omega) (by omega)]
    obtain ⟨n1, c1, u1⟩ := St.block (restoreBlock piPs) st hc dpiRestore_end
      (restoreBlock_ok Mx F piPs (reg n) rsp hpsp fun q hq => by
        simp only [piPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl <;> exact aligned_add hFa (by decide))
    simp only [restoreBlock_run Mx F piPs (reg n) rsp hpsp] at u1
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hc dpi_at_4c (off' := 0x4E) (by decide)
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc dpi_at_4e
    have rsp1 : restoreRegs Mx F (reg n) piPs sp = F := by rw [restoreRegs_sp _ _ _ _ hpsp]; exact rsp
    have rra : restoreRegs Mx F (reg n) piPs ra = reg m ra := by
      simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]; exact slotW ra 0xC (by decide)
    have rs8 : restoreRegs Mx F (reg n) piPs 8 = reg m 8 := by
      simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]; exact slotW 8 8 (by decide)
    refine ⟨n3, S5.trans (S.trans (c1.trans (.cons d2 (.single d3)))), ?_, mem3, ?_, fun q hq => ?_⟩
    · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [rra, hra, add_lit_zero, hret]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp1, eS]
    · rw [regs3]
      by_cases hs : q = sp
      · subst hs; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp1, eS, hsp]
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd, hz]
      rw [upd_ne h0 hs]
      by_cases hr : q = ra
      · subst hr; exact rra
      by_cases h8 : q = 8
      · subst h8; exact rs8
      have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)), (∀ p ∈ ps, p.1 ≠ q) →
          restoreRegs Mx F f ps q = f q := by
        intro f ps
        induction ps generalizing f with
        | nil => intro _; rfl
        | cons p ps ih =>
          intro h
          simp only [restoreRegs]
          rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
      rw [rr _ _ (by
        intro p hp; simp only [piPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl
        · exact fun e => hr e.symm
        · exact fun e => h8 e.symm)]
      exact kq q hq hr h8 hs
  have outG : ∀ k, 8 ≤ k → k < 0x10 → Sep out 8 (F + BitVec.ofNat 32 k) 1 := fun k h1 h2 => by
    rw [eFk]; exact sOG.subR (c := 0x20 + k) (l := 1) (by omega)
  have codeO : ∀ {Mx : Word → BitVec 8}, CodeIn Mx P derPositiveIntegerCode → ∀ (v : Word),
      CodeIn (memStore32 Mx out v) P derPositiveIntegerCode := fun hc v =>
    CodeIn.store32 hc (env.sOC.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
  -- the error tail, from 0x40
  have errEnd : ∀ {n : Machine} {b : BitVec 8}, Steps m5 n → St m5.mem P n 0x40 (reg n) →
      (reg n a0).extractLsb' 0 8 = b → reg n 8 = out → reg n sp = F →
      (∀ q, oidKeep q = true → q ≠ ra → q ≠ 8 → q ≠ sp → reg n q = reg m q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ reg n' sp = sp0 ∧ (∀ q, oidKeep q = true → reg n' q = reg m q) ∧
        ∀ x, Sep G 0x30 x 1 → n'.mem x = memStore8 (memStore32 (derAdvance m.mem d rp rl r) out 0) (out + 4) b x := by
    intro n b S st hb r8 rsp kq
    obtain ⟨n1, d1, u1⟩ := st.sw hc5 dpi_at_40 (off' := 0x44) (by decide) (by rw [r8, add_lit_zero]; exact env.hout)
    rw [r8, add_lit_zero, st.zero] at u1
    have hc1 := codeO hc5 0
    obtain ⟨n2, d2, u2⟩ := u1.sb hc1 dpi_at_44 (off' := 0x48) (by decide)
    rw [r8, hb] at u2
    have hc2 := CodeIn.store8 (v := b) hc1 (env.sOC.sub (c := 4) (l := 1) (by decide))
    obtain ⟨n', S', pc', mem', sp', k'⟩ := fin (S.trans (.cons d1 (.single d2))) u2.self hc2
      (fun k h1 h2 => by
        rw [memStore8_ne fun e' => outG k h1 h2 4 (by decide) 0 (by decide) (by rw [add_ofNat_zero]; exact e'.symm),
          memStore32_get_sep ((outG k h1 h2).sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)])
      (by rw [u2.regs]; exact rsp) (fun q hq h1 h2 h3 => by rw [u2.regs]; exact kq q hq h1 h2 h3)
    exact ⟨n', S', pc', sp', k', fun x hx => by rw [mem']; exact memStore8_pt (memStore32_pt (memI x hx))⟩
  obtain ⟨n6, d6, u6⟩ := u5.lw hc5 dpi_at_12 (off' := 0x14) (by decide) (by
    rw [show reg m5 sp = F from sp5, add_lit_zero]; exact hFa)
  have v6 : reg n6 a0 = memLoad32 (derSliceMem (derAdvance Msv d rp rl r) F R) F := by
    rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]
    have h0 := ldW 0 (by decide)
    rw [add_ofNat_zero] at h0
    rw [show reg m5 sp = F from sp5, add_lit_zero, h0]
  have r6 : ∀ q, q ≠ a0 → reg n6 q = reg m5 q := fun q h => by rw [u6.regs, upd_ne' h u5.zero]
  have K6 : ∀ q, oidKeep q = true → q ≠ ra → q ≠ 8 → q ≠ sp → reg n6 q = reg m q := fun q hq h1 h2 h3 =>
    by rw [r6 q (fun e => by subst e; exact absurd hq (by decide)), K5 q hq h1
      (fun e => by subst e; exact absurd hq (by decide)) h2 h3]
  have hspec : ∀ x, derSliceMem (derAdvance m.mem d rp rl r) out (derPosIntOf (memBytes m.mem rp rl.toNat) rp r) x =
      derSliceMem (derAdvance m.mem d rp rl r) out (derPosIntOf (memBytes m.mem rp rl.toNat) rp r) x := fun _ => rfl
  clear hspec
  cases R with
  | error e =>
    have v6' : reg n6 a0 = 0 := by rw [v6, slice_ld0]
    obtain ⟨n7, d7, u7⟩ := u6.self.taken hc5 0x28 dpi_at_14 (by decide) (by rw [v6', u6.self.zero]; rfl)
    obtain ⟨n8, d8, u8⟩ := u7.self.lbu hc5 dpi_at_28 (off' := 0x2C) (by decide)
    have v8 : reg n8 a0 = (derErrByte e).zeroExtend 32 := by
      rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [u7.regs, r6 sp (by decide), sp5, show F + 4 = F + BitVec.ofNat 32 4 from rfl, f5 _ (outI 4 (by decide)),
        ← show F + 4 = F + BitVec.ofNat 32 4 from rfl, slice_b4]
    obtain ⟨n9, d9, u9⟩ := u8.self.jump hc5 dpi_at_2c (off' := 0x40) (by decide) (by
      rw [u8.self.pc, show P + BitVec.ofNat 32 0x2C + 0x14 = P + BitVec.ofNat 32 0x40 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P env.hP 0x40 (by decide)))
    have r9 : ∀ q, q ≠ a0 → reg n9 q = reg n6 q := fun q h => by rw [u9.regs, u8.regs, upd_ne' h u7.self.zero, u7.regs]
    obtain ⟨n', S', pc', sp', k', mem'⟩ := errEnd (.cons d6 (.cons d7 (.cons d8 (.single d9)))) u9.self
      (by rw [u9.regs, v8, tlv_zext]) (by rw [r9 8 (by decide), r6 8 (by decide), s85])
      (by rw [r9 sp (by decide), r6 sp (by decide), sp5])
      (fun q hq h1 h2 h3 => by rw [r9 q (fun e => by subst e; exact absurd hq (by decide))]; exact K6 q hq h1 h2 h3)
    refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
    rw [mem' x hx, derPosIntOf_err hR]; rfl
  | ok pl =>
    obtain ⟨p, l⟩ := pl
    cases r with
    | error e => exact absurd hR (by simp only [derIntOf]; intro h; cases h)
    | ok t =>
    have hR0 := hR
    have hb : t.header + t.len ≤ rl.toNat := by have := derElement_bound hr; rwa [memBytes_length] at this
    simp only [derIntOf] at hR
    by_cases h0 : t.len = 0
    · rw [ite_eq_left h0] at hR; cases hR
    rw [ite_eq_right h0] at hR
    by_cases hm : 2 ≤ t.len ∧ (((memBytes m.mem rp rl.toNat).getD t.header 0 = 0 ∧
        (memBytes m.mem rp rl.toNat).getD (t.header + 1) 0 < 0x80) ∨ ((memBytes m.mem rp rl.toNat).getD t.header 0 = 0xFF ∧
        0x80 ≤ (memBytes m.mem rp rl.toNat).getD (t.header + 1) 0))
    · rw [ite_eq_left hm] at hR; cases hR
    rw [ite_eq_right hm] at hR
    clear hm
    simp only [Except.ok.injEq, Prod.mk.injEq] at hR
    obtain ⟨rfl, rfl⟩ := hR
    have hcp : (rp + BitVec.ofNat 32 t.header).toNat = rp.toNat + t.header := by
      rw [BitVec.toNat_add, ofNat_tn (by omega)]; exact Nat.mod_eq_of_lt (by omega)
    have hp0 : rp + BitVec.ofNat 32 t.header ≠ 0 := fun h => by
      have := congrArg BitVec.toNat h; rw [hcp] at this; change _ = 0 at this; omega
    have hl0 : BitVec.ofNat 32 t.len ≠ 0 := fun h => by
      have := congrArg BitVec.toNat h; rw [ofNat_tn (by omega)] at this; exact h0 this
    have hbyte : m5.mem (rp + BitVec.ofNat 32 t.header) = m.mem (rp + BitVec.ofNat 32 t.header) := by
      rw [memI _ (sRG.sub (c := t.header) (l := 1) (by omega)).symm,
        derAdvance_outside (.ok t) (sDR.subR (c := t.header) (l := 1) (by omega))]
    have hL : (m.mem (rp + BitVec.ofNat 32 t.header)).toNat = (memBytes m.mem rp rl.toNat).getD t.header 0 :=
      (memBytes_getD (by omega)).symm
    obtain ⟨Bb, hBb⟩ : ∃ Bb, m.mem (rp + BitVec.ofNat 32 t.header) = Bb := ⟨_, rfl⟩
    rw [hBb] at hbyte hL
    have hspec : derPosIntOf (memBytes m.mem rp rl.toNat) rp (.ok t) =
        if (t.len = 1 ∧ Bb.toNat = 0) ∨ 0x80 ≤ Bb.toNat then .error .badDer
        else .ok (rp + BitVec.ofNat 32 t.header, BitVec.ofNat 32 t.len) := by
      simp only [derPosIntOf]; rw [hR0, hL]
    -- the error tail through 0x3E
    have bad : ∀ {n : Machine}, Steps m5 n → St m5.mem P n 0x3E (reg n) → reg n 8 = out → reg n sp = F →
        (∀ q, oidKeep q = true → q ≠ ra → q ≠ 8 → q ≠ sp → reg n q = reg m q) →
        ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ reg n' sp = sp0 ∧ (∀ q, oidKeep q = true → reg n' q = reg m q) ∧
          ∀ x, Sep G 0x30 x 1 → n'.mem x = derSliceMem (derAdvance m.mem d rp rl (.ok t)) out (.error .badDer) x := by
      intro n S st r8 rsp kq
      obtain ⟨n1, d1, u1⟩ := st.aluImm hc5 dpi_at_3e (off' := 0x40) (by decide)
      obtain ⟨n', S', pc', sp', k', mem'⟩ := errEnd (b := derErrByte .badDer) (S.trans (.single d1)) u1.self
        (by rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [st.zero]; rfl)
        (by rw [u1.regs, upd_ne' (by decide) st.zero, r8]) (by rw [u1.regs, upd_ne' (by decide) st.zero, rsp])
        (fun q hq h1 h2 h3 => by
          rw [u1.regs, upd_ne' (fun e => by subst e; exact absurd hq (by decide)) st.zero]; exact kq q hq h1 h2 h3)
      exact ⟨n', S', pc', sp', k', mem'⟩
    -- the sign check from 0x32
    have post : ∀ {n : Machine}, Steps m5 n → St m5.mem P n 0x32 (reg n) → reg n a2 = Bb.zeroExtend 32 →
        reg n a0 = rp + BitVec.ofNat 32 t.header → reg n a1 = BitVec.ofNat 32 t.len → reg n 8 = out → reg n sp = F →
        (∀ q, oidKeep q = true → q ≠ ra → q ≠ 8 → q ≠ sp → reg n q = reg m q) →
        ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ reg n' sp = sp0 ∧ (∀ q, oidKeep q = true → reg n' q = reg m q) ∧
          ∀ x, Sep G 0x30 x 1 → n'.mem x = derSliceMem (derAdvance m.mem d rp rl (.ok t)) out
            (if 0x80 ≤ Bb.toNat then .error .badDer else .ok (rp + BitVec.ofNat 32 t.header, BitVec.ofNat 32 t.len)) x := by
      intro n S st r2 r0 r1 r8 rsp kq
      obtain ⟨n1, d1, u1⟩ := st.aluImm hc5 dpi_at_32 (off' := 0x34) (by decide)
      have k1 : ∀ q, q ≠ a2 → reg n1 q = reg n q := fun q h => by rw [u1.regs, upd_ne' h st.zero]
      by_cases hs : 0x80 ≤ Bb.toNat
      · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc5 0x3E dpi_at_34 (by decide) (by
          rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r2, u1.self.zero, pi_sign]; exact decide_eq_true hs)
        obtain ⟨n', S', pc', sp', k', mem'⟩ := bad (S.trans (.cons d1 (.single d2))) u2.self
          (by rw [u2.regs, k1 8 (by decide), r8]) (by rw [u2.regs, k1 sp (by decide), rsp])
          (fun q hq h1 h2 h3 => by
            rw [u2.regs, k1 q (fun e => by subst e; exact absurd hq (by decide))]; exact kq q hq h1 h2 h3)
        exact ⟨n', S', pc', sp', k', fun x hx => by rw [mem' x hx, ite_eq_left hs]⟩
      · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc5 0x38 dpi_at_34 (by decide) (by
          rw [u1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r2, u1.self.zero, pi_sign]; exact decide_eq_false hs)
        have k2 : ∀ q, q ≠ a2 → reg n2 q = reg n q := fun q h => by rw [u2.regs, k1 q h]
        obtain ⟨n3, d3, u3⟩ := u2.self.sw hc5 dpi_at_38 (off' := 0x3A) (by decide) (by
          rw [k2 8 (by decide), r8, add_lit_zero]; exact env.hout)
        rw [k2 8 (by decide), k2 a0 (by decide), r8, r0, add_lit_zero] at u3
        have hc3 := codeO hc5 (rp + BitVec.ofNat 32 t.header)
        obtain ⟨n4, d4, u4⟩ := u3.sw hc3 dpi_at_3a (off' := 0x3C) (by decide) (by
          rw [k2 8 (by decide), r8]; exact aligned_add env.hout (k := 4) (by decide))
        rw [k2 8 (by decide), k2 a1 (by decide), r8, r1] at u4
        have hc4 := CodeIn.store32 (v := BitVec.ofNat 32 t.len) hc3 (env.sOC.sub (c := 4) (l := 4) (by decide))
        obtain ⟨n5, d5, u5⟩ := u4.jump hc4 dpi_at_3c (off' := 0x48) (by decide) (by
          rw [u4.pc, show P + BitVec.ofNat 32 0x3C + 0xC = P + BitVec.ofNat 32 0x48 by rw [BitVec.add_assoc]; rfl]
          exact even_bit0 (even_at P env.hP 0x48 (by decide)))
        obtain ⟨n', S', pc', mem', sp', k'⟩ := fin (S.trans (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.single d5))))))
          u5.self hc4
          (fun k h1 h2 => by
            rw [memStore32_get_sep (a := out + 4) ((outG k h1 h2).sub (c := 4) (l := 4) (by decide)),
              memStore32_get_sep ((outG k h1 h2).sub (c := 0) (l := 4) (by decide) |> fun h => by
                rwa [add_ofNat_zero] at h)])
          (by rw [u5.regs, k2 sp (by decide), rsp])
          (fun q hq h1 h2 h3 => by
            rw [u5.regs, k2 q (fun e => by subst e; exact absurd hq (by decide))]
            exact kq q hq h1 h2 h3)
        refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
        rw [mem', ite_eq_right hs]
        exact memStore32_pt (memStore32_pt (memI x hx))
    have v6' : reg n6 a0 = rp + BitVec.ofNat 32 t.header := by rw [v6, slice_ld0]
    obtain ⟨n7, d7, u7⟩ := u6.self.notTaken hc5 0x16 dpi_at_14 (by decide) (by
      rw [v6', u6.self.zero]; exact beq_false_of_ne hp0)
    obtain ⟨n8, d8, u8⟩ := u7.self.lw hc5 dpi_at_16 (off' := 0x18) (by decide) (by
      rw [u7.regs, r6 sp (by decide), sp5]; exact aligned_add hFa (k := 4) (by decide))
    have v8a1 : reg n8 a1 = BitVec.ofNat 32 t.len := by
      rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [u7.regs, r6 sp (by decide), sp5, show F + 4 = F + BitVec.ofNat 32 4 from rfl, ldW 4 (by decide),
        ← show F + 4 = F + BitVec.ofNat 32 4 from rfl, slice_ld4]
    have k8 : ∀ q, q ≠ a1 → reg n8 q = reg n6 q := fun q h => by rw [u8.regs, upd_ne' h u7.self.zero, u7.regs]
    obtain ⟨n9, d9, u9⟩ := u8.self.notTaken hc5 0x1A dpi_at_18 (by decide) (by
      rw [v8a1, u8.self.zero]; exact beq_false_of_ne hl0)
    obtain ⟨n10, d10, u10⟩ := u9.self.aluImm hc5 dpi_at_1a (off' := 0x1C) (by decide)
    have k10 : ∀ q, q ≠ a1 → q ≠ a2 → reg n10 q = reg n6 q := fun q h1 h2 => by
      rw [u10.regs, upd_ne' h2 u9.self.zero, u9.regs, k8 q h1]
    have v10a1 : reg n10 a1 = BitVec.ofNat 32 t.len := by rw [u10.regs, upd_ne' (by decide) u9.self.zero, u9.regs, v8a1]
    have v10a2 : reg n10 a2 = 1 := by
      rw [u10.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u9.self.zero]; rfl
    have v10a0 : reg n10 a0 = rp + BitVec.ofNat 32 t.header := by rw [k10 a0 (by decide) (by decide), v6']
    have K10 : ∀ q, oidKeep q = true → q ≠ ra → q ≠ 8 → q ≠ sp → reg n10 q = reg m q := fun q hq h1 h2 h3 => by
      rw [k10 q (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide))]
      exact K6 q hq h1 h2 h3
    have s810 : reg n10 8 = out := by rw [k10 8 (by decide) (by decide), r6 8 (by decide), s85]
    have sp10 : reg n10 sp = F := by rw [k10 sp (by decide) (by decide), r6 sp (by decide), sp5]
    have S10 : Steps m5 n10 := .cons d6 (.cons d7 (.cons d8 (.cons d9 (.single d10))))
    by_cases h1 : t.len = 1
    · obtain ⟨n11, d11, u11⟩ := u10.self.notTaken hc5 0x20 dpi_at_1c (by decide) (by
        rw [v10a1, v10a2, h1]; rfl)
      obtain ⟨n12, d12, u12⟩ := u11.self.lbu hc5 dpi_at_20 (off' := 0x24) (by decide)
      have v12 : reg n12 a2 = Bb.zeroExtend 32 := by
        rw [u12.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u11.regs, v10a0, add_lit_zero, hbyte]
      have k12 : ∀ q, q ≠ a2 → reg n12 q = reg n10 q := fun q h => by rw [u12.regs, upd_ne' h u11.self.zero, u11.regs]
      by_cases hz0 : Bb.toNat = 0
      · obtain ⟨n13, d13, u13⟩ := u12.self.notTaken hc5 0x26 dpi_at_24 (by decide) (by
          rw [v12, u12.self.zero, int_nz, hz0]; rfl)
        obtain ⟨n14, d14, u14⟩ := u13.self.jump hc5 dpi_at_26 (off' := 0x3E) (by decide) (by
          rw [u13.self.pc, show P + BitVec.ofNat 32 0x26 + 0x18 = P + BitVec.ofNat 32 0x3E by rw [BitVec.add_assoc]; rfl]
          exact even_bit0 (even_at P env.hP 0x3E (by decide)))
        obtain ⟨n', S', pc', sp', k', mem'⟩ := bad (S10.trans (.cons d11 (.cons d12 (.cons d13 (.single d14))))) u14.self
          (by rw [u14.regs, u13.regs, k12 8 (by decide), s810]) (by rw [u14.regs, u13.regs, k12 sp (by decide), sp10])
          (fun q hq h1' h2 h3 => by
            rw [u14.regs, u13.regs, k12 q (fun e => by subst e; exact absurd hq (by decide))]; exact K10 q hq h1' h2 h3)
        refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
        rw [mem' x hx, hspec, ite_eq_left (.inl ⟨h1, hz0⟩)]
      · obtain ⟨n13, d13, u13⟩ := u12.self.taken hc5 0x32 dpi_at_24 (by decide) (by
          rw [v12, u12.self.zero, int_nz]; simp [hz0])
        obtain ⟨n', S', pc', sp', k', mem'⟩ := post (S10.trans (.cons d11 (.cons d12 (.single d13)))) u13.self
          (by rw [u13.regs, v12]) (by rw [u13.regs, k12 a0 (by decide), v10a0])
          (by rw [u13.regs, k12 a1 (by decide), v10a1]) (by rw [u13.regs, k12 8 (by decide), s810])
          (by rw [u13.regs, k12 sp (by decide), sp10])
          (fun q hq h1' h2 h3 => by
            rw [u13.regs, k12 q (fun e => by subst e; exact absurd hq (by decide))]; exact K10 q hq h1' h2 h3)
        refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
        rw [mem' x hx, hspec]
        by_cases hs : 0x80 ≤ Bb.toNat
        · rw [ite_eq_left hs, ite_eq_left (.inr hs)]
        · rw [ite_eq_right hs, ite_eq_right (fun h => h.elim (fun h' => hz0 h'.2) hs)]
    · obtain ⟨n11, d11, u11⟩ := u10.self.taken hc5 0x2E dpi_at_1c (by decide) (by
        rw [v10a1, v10a2]
        refine bne_iff_ne.mpr fun e => h1 ?_
        have := congrArg BitVec.toNat e; rwa [ofNat_tn (by omega)] at this)
      obtain ⟨n12, d12, u12⟩ := u11.self.lbu hc5 dpi_at_2e (off' := 0x32) (by decide)
      have v12 : reg n12 a2 = Bb.zeroExtend 32 := by
        rw [u12.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u11.regs, v10a0, add_lit_zero, hbyte]
      have k12 : ∀ q, q ≠ a2 → reg n12 q = reg n10 q := fun q h => by rw [u12.regs, upd_ne' h u11.self.zero, u11.regs]
      obtain ⟨n', S', pc', sp', k', mem'⟩ := post (S10.trans (.cons d11 (.single d12))) u12.self
        v12 (by rw [k12 a0 (by decide), v10a0]) (by rw [k12 a1 (by decide), v10a1]) (by rw [k12 8 (by decide), s810])
        (by rw [k12 sp (by decide), sp10])
        (fun q hq h1' h2 h3 => by rw [k12 q (fun e => by subst e; exact absurd hq (by decide))]; exact K10 q hq h1' h2 h3)
      refine ⟨n', S', pc', sp', k', fun x hx => ?_⟩
      rw [mem' x hx, hspec]
      by_cases hs : 0x80 ≤ Bb.toNat
      · rw [ite_eq_left hs, ite_eq_left (.inr hs)]
      · rw [ite_eq_right hs, ite_eq_right (fun h => h.elim (fun h' => h1 h'.1) hs)]

end C3.RV32
