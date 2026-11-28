import C3BootProofs.Proofs.DerPositive
import C3BootProofs.Proofs.SliceEq

/-!
# `Der::integer_is`, as compiled

`Der::integer_is` reads a minimally encoded `INTEGER` through the proved
`Der::integer` and compares its contents with the one byte `value` through
the proved byte-slice equality. It returns `Result<bool, Error>` in `a0`
and `a1`: a zero tag and the comparison, or a tag of 1 and the error byte.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem ii_at_0 : fetchRel derIntegerIsCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem ii_at_2 : fetchRel derIntegerIsCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem ii_at_4 : fetchRel derIntegerIsCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem ii_at_6 : fetchRel derIntegerIsCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x14, 2) := by decide
theorem ii_at_8 : fetchRel derIntegerIsCode 0x8 = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem ii_at_a : fetchRel derIntegerIsCode 0xA = some (.alu .add a1 x0 a0, 2) := by decide
theorem ii_at_c : fetchRel derIntegerIsCode 0xC = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem ii_at_e : fetchRel derIntegerIsCode 0xE = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem ii_at_12 : fetchRel derIntegerIsCode 0x12 = some (.jalr ra ra 0xFFFFFFAA, 4) := by decide
theorem ii_at_16 : fetchRel derIntegerIsCode 0x16 = some (.load .lw (8 : Fin 32) sp 0x8, 2) := by decide
theorem ii_at_18 : fetchRel derIntegerIsCode 0x18 = some (.branch .beq (8 : Fin 32) x0 0x1C, 2) := by decide
theorem ii_at_1a : fetchRel derIntegerIsCode 0x1A = some (.load .lw a1 sp 0xC, 2) := by decide
theorem ii_at_1c : fetchRel derIntegerIsCode 0x1C = some (.store .sb sp (9 : Fin 32) 0x13, 4) := by decide
theorem ii_at_20 : fetchRel derIntegerIsCode 0x20 = some (.aluImm .add a2 sp 0x13, 4) := by decide
theorem ii_at_24 : fetchRel derIntegerIsCode 0x24 = some (.aluImm .add a3 x0 0x1, 2) := by decide
theorem ii_at_26 : fetchRel derIntegerIsCode 0x26 = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem ii_at_28 : fetchRel derIntegerIsCode 0x28 = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem ii_at_2c : fetchRel derIntegerIsCode 0x2C = some (.jalr ra ra 0x15C, 4) := by decide
theorem ii_at_30 : fetchRel derIntegerIsCode 0x30 = some (.alu .add a1 x0 a0, 2) := by decide
theorem ii_at_32 : fetchRel derIntegerIsCode 0x32 = some (.jal x0 0x6, 2) := by decide
theorem ii_at_34 : fetchRel derIntegerIsCode 0x34 = some (.load .lbu a1 sp 0xC, 4) := by decide
theorem ii_at_38 : fetchRel derIntegerIsCode 0x38 = some (.aluImm .sltu a0 (8 : Fin 32) 0x1, 4) := by decide
theorem ii_at_3c : fetchRel derIntegerIsCode 0x3C = some (.load .lw ra sp 0x1C, 2) := by decide
theorem ii_at_3e : fetchRel derIntegerIsCode 0x3E = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem ii_at_40 : fetchRel derIntegerIsCode 0x40 = some (.load .lw (9 : Fin 32) sp 0x14, 2) := by decide
theorem ii_at_42 : fetchRel derIntegerIsCode 0x42 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem ii_at_44 : fetchRel derIntegerIsCode 0x44 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- `Der::integer_is`'s result for the unread bytes `L` at `rp` in `M`,
given `Der::element`'s result `r` for tag 2: the error byte, or whether the
contents are the one byte `v`. -/
def derIntIsOf (M : Word → BitVec 8) (L : Bytes) (rp : Word) (r : Except DerError DerTlv) (v : BitVec 8) :
    Except (BitVec 8) Bool :=
  match derIntOf L rp r with
  | .error e => .error (derErrByte e)
  | .ok (q, l) => .ok (decide (memBytes M q l.toNat = [v.toNat]))

/-- Where `Der::integer_is` runs: its code and its callees', the 0x40 bytes
of stack below `sp0`, the reader at `d`, and the reader's unread bytes,
apart from what each must not touch. -/
structure IIEnv (M : Word → BitVec 8) (P sp0 d : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P derIntegerIsCode
  int : CodeIn M (P + 0xFFFFCFB8) derIntegerCode
  elem : CodeIn M (P + 0xFFFFCFB8 + 0x5E) derElementCode
  tlv : CodeIn M (P + 0xFFFFCFB8 + 0x5E + 0x26) derTlvCode
  seq : CodeIn M (P + 0xFFFFE184) sliceEqCode
  esl : CodeIn M (P + 0xFFFFE184 + 0xFFFFEBAA) equalSameLengthCode
  mcm : CodeIn M (P + 0xFFFFE184 + 0xBF68) memcmpCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x40 ≤ sp0.toNat
  hd : d.toNat % 4 = 0
  sGC : Sep (sp0 + 0xFFFFFFC0) 0x40 P derIntegerIsCode.length
  sGI : Sep (sp0 + 0xFFFFFFC0) 0x40 (P + 0xFFFFCFB8) derIntegerCode.length
  sGE : Sep (sp0 + 0xFFFFFFC0) 0x40 (P + 0xFFFFCFB8 + 0x5E) derElementCode.length
  sGT : Sep (sp0 + 0xFFFFFFC0) 0x40 (P + 0xFFFFCFB8 + 0x5E + 0x26) derTlvCode.length
  sGQ : Sep (sp0 + 0xFFFFFFC0) 0x40 (P + 0xFFFFE184) sliceEqCode.length
  sGL : Sep (sp0 + 0xFFFFFFC0) 0x40 (P + 0xFFFFE184 + 0xFFFFEBAA) equalSameLengthCode.length
  sGM : Sep (sp0 + 0xFFFFFFC0) 0x40 (P + 0xFFFFE184 + 0xBF68) memcmpCode.length
  sDC : Sep (d + 8) 8 P derIntegerIsCode.length
  sDI : Sep (d + 8) 8 (P + 0xFFFFCFB8) derIntegerCode.length
  sDT : Sep (d + 8) 8 (P + 0xFFFFCFB8 + 0x5E + 0x26) derTlvCode.length
  sDQ : Sep (d + 8) 8 (P + 0xFFFFE184) sliceEqCode.length
  sDL : Sep (d + 8) 8 (P + 0xFFFFE184 + 0xFFFFEBAA) equalSameLengthCode.length
  sDM : Sep (d + 8) 8 (P + 0xFFFFE184 + 0xBF68) memcmpCode.length
  sDG : Sep (d + 8) 8 (sp0 + 0xFFFFFFC0) 0x40
  sRG : Sep (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat (sp0 + 0xFFFFFFC0) 0x40
  sDR : Sep (d + 8) 8 (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat
  hrp : 0 < (memLoad32 M (d + 8)).toNat
  hrw : (memLoad32 M (d + 8)).toNat + (memLoad32 M (d + 0xC)).toNat < 2 ^ 32

abbrev iiPs : List (Fin 32 × Word) := [(ra, 0x1C), ((8 : Fin 32), 0x18), ((9 : Fin 32), 0x14)]

section
set_option maxRecDepth 20000
theorem iiSave_end : blockEnd derIntegerIsCode 2 (saveBlock iiPs) = some 8 := by decide
theorem iiRestore_end : blockEnd derIntegerIsCode 0x3C (restoreBlock iiPs) = some 0x42 := by decide
end

theorem ii_sltu_ne {x : Word} (h : x ≠ 0) : aluEval .sltu x 1 = 0 := by
  show (if x.ult 1 then 1 else 0) = 0
  cases hu : x.ult 1 with
  | false => rfl
  | true =>
    exfalso; apply h; apply BitVec.eq_of_toNat_eq
    have h2 : decide (x.toNat < 1) = true := hu
    have := of_decide_eq_true h2
    show x.toNat = 0; omega

theorem derIntOf_ok {L : Bytes} {rp q l : Word} {r : Except DerError DerTlv} (h : derIntOf L rp r = .ok (q, l)) :
    ∃ t, r = .ok t ∧ q = rp + BitVec.ofNat 32 t.header ∧ l = BitVec.ofNat 32 t.len := by
  cases r with
  | error e => cases h
  | ok t =>
    refine ⟨t, rfl, ?_⟩
    simp only [derIntOf] at h
    by_cases h1 : t.len = 0
    · rw [ite_eq_left h1] at h; cases h
    · rw [ite_eq_right h1] at h
      by_cases h2 : 2 ≤ t.len ∧ ((L.getD t.header 0 = 0 ∧ L.getD (t.header + 1) 0 < 0x80) ∨
          (L.getD t.header 0 = 0xFF ∧ 0x80 ≤ L.getD (t.header + 1) 0))
      · rw [ite_eq_left h2] at h; cases h
      · rw [ite_eq_right h2] at h; cases h; exact ⟨rfl, rfl⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `Der::integer_is`**: with the reader at `d`, whose unread
bytes start at `rp` and number `rl`, and `value`'s byte in `a1`, it returns
`derIntIsOf` of them in `a0` and `a1`, and moves the reader past the element
when `Der::element` reads one. -/
theorem derIntegerIs_correct (m : Machine) {P sp0 d retAddr : Word} (env : IIEnv m.mem P sp0 d)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = d)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∀ x, Sep (sp0 + 0xFFFFFFC0) 0x40 x 1 →
        m'.mem x = derAdvance m.mem d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
          (derElement 2 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)) x) ∧
      match derIntIsOf m.mem (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)
          (memLoad32 m.mem (d + 8))
          (derElement 2 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat))
          ((reg m a1).extractLsb' 0 8) with
      | .error b => reg m' a0 = 1 ∧ (reg m' a1).extractLsb' 0 8 = b
      | .ok v => reg m' a0 = 0 ∧ reg m' a1 = if v then 1 else 0 := by
  have hrp0 := env.hrp; have hrw := env.hrw; have sRG := env.sRG; have sDR := env.sDR
  generalize hRP : memLoad32 m.mem (d + 8) = rp at hrp0 hrw sRG sDR ⊢
  generalize hRL : memLoad32 m.mem (d + 0xC) = rl at hrw sRG sDR ⊢
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFFC0 = G := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFE0 = F := ⟨_, rfl⟩
  have sGC := env.sGC; have sGI := env.sGI; have sGE := env.sGE; have sGT := env.sGT; have sGQ := env.sGQ
  have sGL := env.sGL; have sGM := env.sGM; have sDG := env.sDG
  rw [hG] at sGC sGI sGE sGT sGQ sGL sGM sDG sRG ⊢
  have hGF : G + 0x20 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFFC0) (by decide)
  have hFa : F.toNat % 4 = 0 := by rw [← hGF]; exact aligned_add hGa (k := 0x20) (by decide)
  have hGw : G.toNat + 0x40 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFFC0 : Word).toNat = 4294967232 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have hFn : F.toNat = G.toNat + 0x20 := by
    rw [← hGF, BitVec.toNat_add, show (0x20 : Word).toNat = 0x20 from rfl]; omega
  have eS : F + 0x20 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFG : F + 0xFFFFFFE0 = G := by rw [← hGF, BitVec.add_assoc]; exact BitVec.add_zero G
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x20 + k) := fun k => by
    rw [← hGF, show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, add_ofNat_assoc]
  have inF : ∀ {b : Word} {l : Nat}, Sep G 0x40 b l → Sep F 0x20 b l := fun h => by
    rw [← hGF]; exact h.sub (c := 0x20) (l := 0x20) (by decide)
  have inI : ∀ {b : Word} {l : Nat}, Sep G 0x40 b l → Sep G 0x20 b l := fun h =>
    (h.sub (c := 0) (l := 0x20) (by decide)) |> fun h' => by rwa [add_ofNat_zero] at h'
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0x40 b code'.length → (∀ x, Sep G 0x40 x 1 → M' x = m.mem x) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod ii_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock iiPs) u1 env.cod iiSave_end (saveBlock_ok _ iiPs _ fun p hp => by
    rw [sp1]
    simp only [iiPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨aligned_add hFa (by decide), (inF sGC).sub (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0)) iiPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep F 0x20 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside iiPs fun p hp => by
      simp only [iiPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> exact hx.sub (by decide)
  have frSvG : ∀ x, Sep G 0x40 x 1 → Msv x = m.mem x := fun x hx => frSv x (inF hx)
  have hslv : ∀ r o, (r, o) ∈ iiPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [iiPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ q, q ≠ sp → reg m2 q = reg m q := fun q h => by rw [u2.regs, updz hz h]
  have sp2 : reg m2 sp = F := by rw [u2.regs]; exact sp1
  have hcS : CodeIn Msv P derIntegerIsCode := cIn env.cod sGC frSvG
  obtain ⟨m3, c3, u3⟩ := St.block [.alu .add (9 : Fin 32) x0 a1, .alu .add a1 x0 a0, .aluImm .add a0 sp 0x8]
    u2.self hcS (off' := 0xE) (by decide) (by simp [BlockOk, BInstr.ok])
  simp only [runBlock, BInstr.run] at u3
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.callRa hcS ii_at_e ii_at_12 (cb := P + 0xFFFFCFB8)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFCFB8 (by decide))
  have r4 := PEnv.reg1 regs4 u3.zero
  have k4 : ∀ q, q ≠ ra → q ≠ a0 → q ≠ a1 → q ≠ (9 : Fin 32) → q ≠ sp → reg m4 q = reg m q :=
    fun q hr h0 h1 h9 hs => by
      rw [r4 q hr, updz ((updz u2.self.zero (by decide)).trans u2.self.zero |> fun h =>
        (updz (r := 0) h (by decide)).trans h) h0, updz ((updz u2.self.zero (by decide)).trans u2.self.zero) h1,
        updz u2.self.zero h9, r2 q hs]
  have v4a0 : reg m4 a0 = F + 8 := by
    rw [r4 a0 (by decide)]; simp +decide only [upd_app, ↓reduceIte]; rw [sp2]; rfl
  have v4a1 : reg m4 a1 = d := by
    rw [r4 a1 (by decide)]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a0 (by decide), ha0]; exact zw d
  have v49 : reg m4 9 = reg m a1 := by
    rw [r4 9 (by decide)]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a1 (by decide)]; exact zw _
  have v4sp : reg m4 sp = F := by
    rw [r4 sp (by decide)]; simp +decide only [upd_app, ↓reduceIte]; exact sp2
  have eD8 : memLoad32 Msv (d + 8) = rp := by
    rw [← hRP]; exact memLoad32_congr fun j hj => frSvG _ (sDG.symm.subR (c := j) (l := 1) (by omega))
  have eDC : memLoad32 Msv (d + 0xC) = rl := by
    rw [← hRL]; exact memLoad32_congr fun j hj => frSvG _ (by
      rw [show d + 0xC = d + 8 + BitVec.ofNat 32 4 by rw [BitVec.add_assoc]; rfl, add_ofNat_assoc]
      exact sDG.symm.subR (by omega))
  have eL : memBytes Msv rp rl.toNat = memBytes m.mem rp rl.toNat :=
    memBytes_congr fun i hi => frSvG _ (sRG.symm.subR (c := i) (l := 1) (by omega))
  have hI : DerCallEnv m4.mem derIntegerCode (P + 0xFFFFCFB8) 0x5E F (F + 8) d 8 := by
    rw [mem4]
    refine ⟨even_at P env.hP 0xFFFFCFB8 (by decide), by rw [BitVec.add_assoc]; exact even_at P env.hP 0xFFFFD016 (by decide),
      cIn env.int sGI frSvG, cIn env.elem sGE frSvG, cIn env.tlv sGT frSvG, hFa, by omega,
      aligned_add hFa (k := 8) (by decide), env.hd, by rw [eFG]; exact inI sGI, by rw [eFG]; exact inI sGE,
      by rw [eFG]; exact inI sGT, (inF sGI).sub (by decide), env.sDI, env.sDT, ?_, ?_, ?_, by rw [eD8]; exact hrp0,
      by rw [eD8, eDC]; exact hrw⟩
    · rw [eFG, show F + 8 = F + BitVec.ofNat 32 8 from rfl, eFk]
      have := sep_offsets G (c := 0x28) (n := 8) (d := 0) (k := 0x20) (.inr (by decide)) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
    · rw [eFG]; exact (sDG.subR (c := 0) (l := 0x20) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h
    · rw [eFG, eD8, eDC]; exact (sRG.subR (c := 0) (l := 0x20) (by decide)) |> fun h => by rwa [add_ofNat_zero] at h
  obtain ⟨m5, c5, pc5, sp5, k5, f5⟩ := derInteger_correct m4 hI (by rw [mem4, eD8, eDC]; exact sDR) pc4 v4sp v4a0
    v4a1 (by rw [regs4]; simp +decide [upd]) (even_clear _ (even_at P env.hP (0xE + 8) (by decide)))
  rw [mem4, eD8, eDC, eL, eFG] at f5
  generalize hr : derElement 2 (memBytes m.mem rp rl.toNat) = r at f5 ⊢
  generalize hR : derIntOf (memBytes m.mem rp rl.toNat) rp r = R at f5
  have outI : ∀ k, k < 0x20 → Sep G 0x20 (F + BitVec.ofNat 32 k) 1 := fun k hk => by
    rw [eFk]
    have := sep_offsets G (c := 0) (n := 0x20) (d := 0x20 + k) (k := 1) (.inl (by omega)) (by decide) (by omega)
    rwa [add_ofNat_zero] at this
  have memI : ∀ x, Sep G 0x40 x 1 → m5.mem x = derAdvance m.mem d rp rl r x := fun x hx => by
    have h8 : Sep (F + 8) 8 x 1 := (inF hx).sub (by decide)
    rw [f5 x (inI hx), slice_out R h8]
    exact derAdvance_pt r (frSvG x hx)
  have hc5 : CodeIn m5.mem P derIntegerIsCode := fun i hi => by
    rw [memI _ (sGC.subR (c := i) (l := 1) (by omega)), derAdvance_outside r (env.sDC.subR (c := i) (l := 1) (by omega))]
    exact env.cod i hi
  have u5 : St m5.mem P m5 0x16 (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  have S5 : Steps m m5 := .cons d1 (c2.trans (c3.trans (c4.trans c5)))
  have K5 : ∀ q, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m5 q = reg m q := fun q hq => by
    have ho : oidKeep q = true := by revert hq; revert q; decide
    have h : q ≠ ra ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ (9 : Fin 32) ∧ q ≠ sp := by revert hq; revert q; decide
    rw [k5 q ho, k4 q h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2]
  have s95 : reg m5 9 = reg m a1 := by rw [k5 9 (by decide), v49]
  -- the saved-register slots are as the prologue left them
  have slot5 : ∀ k, 0x14 ≤ k → k < 0x20 → m5.mem (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) :=
    fun k h1 h2 => by
      have hs8 : Sep (F + 8) 8 (F + BitVec.ofNat 32 k) 1 := by
        rw [show F + 8 = F + BitVec.ofNat 32 8 from rfl]
        exact sep_offsets F (.inl (by omega)) (by decide) (by omega)
      have hsd : Sep (d + 8) 8 (F + BitVec.ofNat 32 k) 1 := by rw [eFk]; exact sDG.subR (c := 0x20 + k) (l := 1) (by omega)
      rw [f5 _ (outI _ (by omega)), slice_out R hs8, derAdvance_outside r hsd]
  obtain ⟨n6, d6, u6⟩ := u5.lw hc5 ii_at_16 (off' := 0x18) (by decide) (by
    rw [sp5]; exact aligned_add hFa (k := 8) (by decide))
  have v6 : reg n6 8 = memLoad32 (derSliceMem (derAdvance Msv d rp rl r) (F + 8) R) (F + 8) := by
    rw [u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp5]
    exact memLoad32_congr fun j hj => by
      rw [show F + 8 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (8 + j) by rw [← add_ofNat_assoc]; rfl]
      exact f5 _ (outI _ (by omega))
  have r6 : ∀ q, q ≠ 8 → reg n6 q = reg m5 q := fun q h => by rw [u6.regs, upd_ne' h u5.zero]
  have hpsp : ∀ p ∈ iiPs, p.1 ≠ sp := by decide
  -- the result tag and the epilogue, from 0x38
  have fin : ∀ {Mx : Word → BitVec 8} {n : Machine}, Steps m n → St Mx P n 0x38 (reg n) →
      CodeIn Mx P derIntegerIsCode →
      (∀ k, 0x14 ≤ k → k < 0x20 → Mx (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k)) → reg n sp = F →
      (∀ q, q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n q = reg m q) →
      ∃ n', Steps m n' ∧ n'.pc = retAddr ∧ n'.mem = Mx ∧ reg n' sp = sp0 ∧
        reg n' a0 = aluEval .sltu (reg n 8) 1 ∧ reg n' a1 = reg n a1 ∧
        ∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg m q := by
    intro Mx n S st hc hsl rsp kq
    obtain ⟨n0, d0, u0⟩ := st.aluImm hc ii_at_38 (off' := 0x3C) (by decide)
    have slotW : ∀ r o, (r, o) ∈ iiPs → memLoad32 Mx (F + o) = reg m r := fun r o h => by
      have ho : 0x14 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x20 := by
        simp only [iiPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      rw [← hslv r o h]
      apply memLoad32_congr; intro j hj
      rw [← ofNat_toNat_self o, add_ofNat_assoc, hsl _ (by omega) (by omega)]
    have rsp0 : upd (reg n) a0 (aluEval .sltu (reg n 8) 1) sp = F := by rw [updz st.zero (by decide), rsp]
    obtain ⟨n1, c1, u1⟩ := St.block (restoreBlock iiPs) u0 hc iiRestore_end
      (restoreBlock_ok Mx F iiPs _ rsp0 hpsp fun q hq => by
        simp only [iiPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> exact aligned_add hFa (by decide))
    simp only [restoreBlock_run Mx F iiPs _ rsp0 hpsp] at u1
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hc ii_at_42 (off' := 0x44) (by decide)
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc ii_at_44
    have rsp1 : restoreRegs Mx F (upd (reg n) a0 (aluEval .sltu (reg n 8) 1)) iiPs sp = F := by
      rw [restoreRegs_sp _ _ _ _ hpsp]; exact rsp0
    have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
        restoreRegs Mx F f ps q = f q := by
      intro f ps q h0
      induction ps generalizing f with
      | nil => intro _; rfl
      | cons p ps ih =>
        intro h
        simp only [restoreRegs]
        rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
    have hreg : ∀ r o, (r, o) ∈ iiPs → restoreRegs Mx F (upd (reg n) a0 (aluEval .sltu (reg n 8) 1)) iiPs r = reg m r :=
      fun r o hm => by
        simp only [iiPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
          exact slotW _ _ (by decide)
    refine ⟨n3, S.trans (.cons d0 (c1.trans (.cons d2 (.single d3)))), ?_, mem3, ?_, ?_, ?_, fun q hq => ?_⟩
    · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [hreg ra 0x1C (by decide), hra, add_lit_zero, hret]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp1, eS]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]
      rw [rr _ _ a0 (by decide) (by decide)]; simp +decide only [upd_app, ↓reduceIte]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]
      rw [rr _ _ a1 (by decide) (by decide), updz st.zero (by decide)]
    · rw [regs3]
      have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
          q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ (q.val ∈ [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] ∧
            q.val ≠ 0 ∧ q ≠ sp ∧ q ≠ a0 ∧ (∀ p ∈ iiPs, p.1 ≠ q)) := by decide
      rcases key q hq with rfl | rfl | rfl | ⟨h1, h0, hs, ha, hps⟩
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x1C (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x18 (by decide)
      · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x14 (by decide)
      · rw [upd_ne h0 hs, rr _ _ q h0 hps, updz st.zero ha]; exact kq q h1
  have hR' := hR
  cases R with
  | error e =>
    have v6' : reg n6 8 = 0 := by rw [v6, slice_ld0]
    obtain ⟨n7, d7, u7⟩ := u6.self.taken hc5 0x34 ii_at_18 (by decide) (by rw [v6', u6.self.zero]; rfl)
    obtain ⟨n8, d8, u8⟩ := u7.self.lbu hc5 ii_at_34 (off' := 0x38) (by decide)
    have v8 : reg n8 a1 = (derErrByte e).zeroExtend 32 := by
      rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [u7.regs, r6 sp (by decide), sp5, show F + 0xC = F + 8 + 4 by rw [BitVec.add_assoc]; rfl,
        show F + 8 + 4 = F + BitVec.ofNat 32 0xC by rw [BitVec.add_assoc]; rfl, f5 _ (outI 0xC (by decide)),
        show F + BitVec.ofNat 32 0xC = F + 8 + 4 by rw [BitVec.add_assoc]; rfl, slice_b4]
    have k8 : ∀ q, q ≠ a1 → q ≠ 8 → reg n8 q = reg m5 q := fun q h1 h8 => by
      rw [u8.regs, upd_ne' h1 u7.self.zero, u7.regs, r6 q h8]
    obtain ⟨n', S', pc', mem', sp', a0', a1', k'⟩ := fin (S5.trans (.cons d6 (.cons d7 (.single d8)))) u8.self hc5
      slot5 (by rw [k8 sp (by decide) (by decide), sp5])
      (fun q hq => by
        rw [k8 q (fun e => by subst e; revert hq; decide) (fun e => by subst e; revert hq; decide)]; exact K5 q hq)
    have hspec : derIntIsOf m.mem (memBytes m.mem rp rl.toNat) rp r ((reg m a1).extractLsb' 0 8) =
        .error (derErrByte e) := by unfold derIntIsOf; rw [hR']
    refine ⟨n', S', pc', sp', k', fun x hx => by rw [mem', memI x hx], ?_⟩
    rw [hspec]
    refine ⟨by rw [a0', u8.regs, upd_ne' (by decide) u7.self.zero, u7.regs, v6']; rfl, ?_⟩
    rw [a1', v8, tlv_zext]
  | ok pl =>
    obtain ⟨q, l⟩ := pl
    obtain ⟨t, hrt, hq, hl⟩ := derIntOf_ok hR'
    subst hrt
    have hb : t.header + t.len ≤ rl.toNat := by have := derElement_bound hr; rwa [memBytes_length] at this
    have hqn : q.toNat = rp.toNat + t.header := by rw [hq, BitVec.toNat_add, ofNat_tn (by omega)]; omega
    have hq0 : q ≠ 0 := fun h => by
      have := congrArg BitVec.toNat h; rw [hqn, show (0 : Word).toNat = 0 from rfl] at this; omega
    have v6' : reg n6 8 = q := by rw [v6, slice_ld0]
    obtain ⟨n7, d7, u7⟩ := u6.self.notTaken hc5 0x1A ii_at_18 (by decide) (by
      rw [v6', u6.self.zero]; exact beq_false_of_ne hq0)
    obtain ⟨n8, d8, u8⟩ := u7.self.lw hc5 ii_at_1a (off' := 0x1C) (by decide) (by
      rw [u7.regs, r6 sp (by decide), sp5]; exact aligned_add hFa (k := 0xC) (by decide))
    have v8 : reg n8 a1 = l := by
      rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [u7.regs, r6 sp (by decide), sp5, show F + 0xC = F + 8 + 4 by rw [BitVec.add_assoc]; rfl, ← slice_ld4 (M := derAdvance Msv d rp rl (.ok t)) (out := F + 8) (p := q) (l := l)]
      exact memLoad32_congr fun j hj => by
        rw [show F + 8 + 4 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0xC + j) by
          rw [show F + 8 + 4 = F + BitVec.ofNat 32 0xC by rw [BitVec.add_assoc]; rfl, add_ofNat_assoc]]
        exact f5 _ (outI _ (by omega))
    have k8 : ∀ q', q' ≠ a1 → q' ≠ 8 → reg n8 q' = reg m5 q' := fun q' h1 h8 => by
      rw [u8.regs, upd_ne' h1 u7.self.zero, u7.regs, r6 q' h8]
    obtain ⟨n9, d9, u9⟩ := u8.self.sb hc5 ii_at_1c (off' := 0x20) (by decide)
    rw [k8 sp (by decide) (by decide), sp5, k8 9 (by decide) (by decide), s95] at u9
    obtain ⟨v, hv⟩ : ∃ v, (reg m a1).extractLsb' 0 8 = v := ⟨_, rfl⟩
    rw [hv] at u9
    have hc9 : CodeIn (memStore8 m5.mem (F + 0x13) v) P derIntegerIsCode :=
      CodeIn.store8 hc5 ((inF sGC).sub (c := 0x13) (l := 1) (by decide))
    obtain ⟨n10, c10, u10⟩ := St.block [.aluImm .add a2 sp 0x13, .aluImm .add a3 x0 1, .alu .add a0 x0 (8 : Fin 32)]
      u9.self hc9 (off' := 0x28) (by decide) (by simp [BlockOk, BInstr.ok])
    simp only [runBlock, BInstr.run] at u10
    obtain ⟨n11, c11, pc11, mem11, regs11⟩ := u10.callRa hc9 ii_at_28 ii_at_2c (cb := P + 0xFFFFE184)
      (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFE184 (by decide))
    have r11 := PEnv.reg1 regs11 u10.zero
    have k11 : ∀ q', q' ≠ ra → q' ≠ a0 → q' ≠ a2 → q' ≠ a3 → reg n11 q' = reg n8 q' := fun q' hr h0 h2 h3 => by
      rw [r11 q' hr, updz ((updz (upd_zero _ _ _) (by decide)).trans (upd_zero _ _ _)) h0, updz (upd_zero _ _ _) h3,
        updz u9.self.zero h2, u9.regs]
    have sp11 : reg n11 sp = F := by
      rw [k11 sp (by decide) (by decide) (by decide) (by decide), k8 sp (by decide) (by decide), sp5]
    have eF4 : F + 0xFFFFFFFC = G + BitVec.ofNat 32 0x1C := by rw [← hGF, BitVec.add_assoc]; rfl
    have frM : ∀ x, Sep G 0x40 x 1 → memStore8 m5.mem (F + 0x13) v x = derAdvance m.mem d rp rl (.ok t) x :=
      fun x hx => by
        rw [memStore8_ne fun e => ((inF hx).sub (c := 0x13) (l := 1) (by decide)).point (i := 0) (j := 0) (by decide)
            (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm), memI x hx]
    have hcM : ∀ {b : Word} {code' : List Nat}, CodeIn m.mem b code' → Sep G 0x40 b code'.length →
        Sep (d + 8) 8 b code'.length → CodeIn (memStore8 m5.mem (F + 0x13) v) b code' := fun hcb hs hd i hi => by
      rw [frM _ (hs.subR (c := i) (l := 1) (by omega)), derAdvance_outside _ (hd.subR (c := i) (l := 1) (by omega))]
      exact hcb i hi
    have s88 : reg n8 8 = q := by rw [u8.regs, upd_ne' (by decide) u7.self.zero, u7.regs, v6']
    obtain ⟨n12, c12, pc12, a012, k12, mem12⟩ := sliceEq_correct n11 (base := P + 0xFFFFE184) (p := q) (pl := t.len)
      (q := F + 0x13) (ql := 1) (even_at P env.hP 0xFFFFE184 (by decide)) (by rw [mem11]; exact hcM env.seq sGQ env.sDQ)
      (by rw [mem11]; exact hcM env.esl sGL env.sDL) (by rw [mem11]; exact hcM env.mcm sGM env.sDM) pc11
      (by rw [r11 a0 (by decide)]; simp +decide only [upd_app, ↓reduceIte]; rw [u9.regs, s88]; exact zw q)
      (by rw [k11 a1 (by decide) (by decide) (by decide) (by decide), v8, hl])
      (by rw [r11 a2 (by decide)]; simp +decide only [upd_app, ↓reduceIte]
          rw [u9.regs, k8 sp (by decide) (by decide), sp5]; rfl)
      (by rw [r11 a3 (by decide)]; simp +decide only [upd_app, ↓reduceIte])
      (by omega) (by decide) (by rw [regs11]; simp +decide [upd])
      (even_clear _ (even_at P env.hP (0x28 + 8) (by decide))) (by rw [sp11]; exact hFa)
      (by rw [sp11, eF4]; exact sGL.sub (by decide)) (by rw [sp11, eF4]; exact sGM.sub (by decide))
      (by rw [sp11, eF4, hq]; exact (sRG.sub (c := t.header) (l := t.len) (by omega)).symm.sub (by decide))
      (by rw [sp11, eF4, show F + 0x13 = F + BitVec.ofNat 32 0x13 from rfl, eFk]
          exact sep_offsets G (.inl (by decide)) (by decide) (by decide))
    rw [sp11, eF4] at mem12
    have frN : ∀ x, Sep G 0x40 x 1 → n12.mem x = derAdvance m.mem d rp rl (.ok t) x := fun x hx => by
      rw [mem12 x (hx.sub (by decide)), mem11, frM x hx]
    have hc12 : CodeIn n12.mem P derIntegerIsCode := fun i hi => by
      rw [frN _ (sGC.subR (c := i) (l := 1) (by omega)), derAdvance_outside _ (env.sDC.subR (c := i) (l := 1) (by omega))]
      exact env.cod i hi
    have u12 : St n12.mem P n12 0x30 (reg n12) := ⟨by rw [pc12], rfl, fun _ => rfl⟩
    obtain ⟨n13, d13, u13⟩ := u12.alu hc12 ii_at_30 (off' := 0x32) (by decide)
    obtain ⟨n14, d14, u14⟩ := u13.self.jump hc12 ii_at_32 (off' := 0x38) (by decide) (by
      rw [u13.self.pc, show P + BitVec.ofNat 32 0x32 + 0x6 = P + BitVec.ofNat 32 0x38 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P env.hP 0x38 (by decide)))
    have k14 : ∀ q', q' ≠ a1 → reg n14 q' = reg n12 q' := fun q' h => by
      rw [u14.regs, u13.regs, upd_ne' h u12.zero]
    have kk : ∀ q', q'.val ∈ [3, 4, 8, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n14 q' = reg n8 q' := fun q' hq => by
      have h : q' ≠ a0 ∧ q' ≠ a1 ∧ q' ≠ a2 ∧ q' ≠ a3 ∧ q' ≠ a4 ∧ q' ≠ t1 ∧ q' ≠ ra := by revert hq; revert q'; decide
      rw [k14 q' h.2.1, k12 q' h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1,
        k11 q' h.2.2.2.2.2.2 h.1 h.2.2.1 h.2.2.2.1]
    obtain ⟨n', S', pc', mem', sp', a0', a1', k'⟩ := fin
      (S5.trans (.cons d6 (.cons d7 (.cons d8 (.cons d9 (c10.trans (c11.trans (c12.trans (.cons d13 (.single d14))))))))))
      u14.self hc12
      (fun k h1 h2 => by
        rw [mem12 _ (by rw [eFk]; exact sep_offsets G (.inl (by omega)) (by decide) (by omega)), mem11,
          memStore8_ne fun e => (sep_offsets F (c := 0x13) (n := 1) (d := k) (k := 1) (.inl (by omega)) (by decide)
            (by omega)).point (i := 0) (j := 0) (by decide) (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)]
        exact slot5 k h1 h2)
      (by rw [k14 sp (by decide), k12 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        k11 sp (by decide) (by decide) (by decide) (by decide), k8 sp (by decide) (by decide), sp5])
      (fun q' hq => by
        rw [kk q' (by revert hq; revert q'; decide), k8 q' (by revert hq; revert q'; decide) (by revert hq; revert q'; decide)]
        exact K5 q' hq)
    have eBq : memBytes n11.mem q t.len = memBytes m.mem q t.len := by
      rw [mem11]
      exact memBytes_congr fun i hi => by
        rw [frM _ (by rw [hq, add_ofNat_assoc]; exact (sRG.sub (c := t.header + i) (l := 1) (by omega)).symm),
          derAdvance_outside _ (by rw [hq, add_ofNat_assoc]; exact sDR.subR (c := t.header + i) (l := 1) (by omega))]
    have eB1 : memBytes n11.mem (F + 0x13) 1 = [v.toNat] := by
      rw [mem11]; show List.map _ (List.range 1) = _
      rw [show List.range 1 = [0] from rfl, List.map_cons, List.map_nil, add_ofNat_zero, memStore8_same]
    have hspec : derIntIsOf m.mem (memBytes m.mem rp rl.toNat) rp (.ok t) v =
        .ok (decide (memBytes m.mem q t.len = [v.toNat])) := by
      unfold derIntIsOf; rw [hR']; dsimp only; rw [hl, ofNat_tn (by omega)]
    refine ⟨n', S', pc', sp', k', fun x hx => by rw [mem', frN x hx], ?_⟩
    rw [hv, hspec]
    refine ⟨by rw [a0', kk 8 (by decide), s88]; exact ii_sltu_ne hq0, ?_⟩
    rw [a1', u14.regs, u13.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [ev_add, show reg n12 x0 = 0 from u12.zero, zw, a012, eBq, eB1]
    by_cases hp : memBytes m.mem q t.len = [v.toNat]
    · rw [ite_eq_left hp, ite_eq_left (decide_eq_true hp)]
    · rw [ite_eq_right hp, ite_eq_right (fun h => hp (of_decide_eq_true h))]

end C3.RV32
