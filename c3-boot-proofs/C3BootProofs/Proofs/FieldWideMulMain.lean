import C3BootProofs.Proofs.FieldWideMul

/-! # `widening_mul_fixed::<8, 8>`, end to end -/

namespace C3.RV32

open C3.Image

theorem fillWords_load {M : Word → BitVec 8} {dst v : Word} :
    ∀ k i, i < k → dst.toNat + 4 * k ≤ 2 ^ 32 → memLoad32 (fillWords M dst v k) (dst + BitVec.ofNat 32 (4 * i)) = v
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, i, hi, hw => by
    simp only [fillWords]
    by_cases h : i = k
    · subst h; exact memLoad32_store32_same _ _ _
    · rw [memLoad32_store32_sep (sep_offsets dst (by omega) (by omega) (by omega))]
      exact fillWords_load k i (by omega) (by omega)

theorem copyWords_load {M : Word → BitVec 8} {dst src : Word} :
    ∀ k i, i < k → dst.toNat + 4 * k ≤ 2 ^ 32 →
      memLoad32 (copyWords M dst src k) (dst + BitVec.ofNat 32 (4 * i)) = memLoad32 M (src + BitVec.ofNat 32 (4 * i))
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, i, hi, hw => by
    simp only [copyWords]
    by_cases h : i = k
    · subst h; exact memLoad32_store32_same _ _ _
    · rw [memLoad32_store32_sep (sep_offsets dst (by omega) (by omega) (by omega))]
      exact copyWords_load k i (by omega) (by omega)

theorem accV_congr2 {M M' : Word → BitVec 8} {b b' : Word} :
    ∀ n, (∀ i, i < n → memLoad32 M' (b' + BitVec.ofNat 32 (4 * i)) = memLoad32 M (b + BitVec.ofNat 32 (4 * i))) →
      accV M' b' n = accV M b n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [accV]
    rw [accV_congr2 n (fun i hi => h i (by omega)), h n (by omega)]

theorem accV_zero {M : Word → BitVec 8} {b : Word} :
    ∀ n, (∀ i, i < n → memLoad32 M (b + BitVec.ofNat 32 (4 * i)) = 0) → accV M b n = 0
  | 0, _ => rfl
  | n + 1, h => by
    simp only [accV]
    rw [accV_zero n (fun i hi => h i (by omega)), h n (by omega), show (0 : Word).toNat = 0 from rfl,
      Nat.zero_mul]

theorem limbVal_append : ∀ (l : List Word) (x : Word), limbVal (l ++ [x]) = limbVal l + 2 ^ (32 * l.length) * x.toNat
  | [], x => by
    simp only [List.nil_append, limbVal, List.length_nil, Nat.mul_zero, Nat.pow_zero, Nat.one_mul]; omega
  | w :: l, x => by
    simp only [List.cons_append, limbVal, List.length_cons]
    rw [limbVal_append l x, Nat.mul_succ, Nat.pow_add]
    simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]; omega

theorem limbVal_wordsAt (M : Word → BitVec 8) (b : Word) : ∀ n, limbVal (wordsAt M b n) = accV M b n
  | 0 => rfl
  | n + 1 => by
    have e : wordsAt M b (n + 1) = wordsAt M b n ++ [memLoad32 M (b + BitVec.ofNat 32 (4 * n))] := by
      simp only [wordsAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [e, limbVal_append, limbVal_wordsAt M b n, wordsAt_length]
    simp only [accV]
    rw [Nat.mul_comm (2 ^ (32 * n))]

/-- What `widening_mul_fixed`'s save helper stores and its restore helper
loads. -/
abbrev wmPs : List (Fin 32 × Word) :=
  [(ra, BitVec.ofNat 32 0x5C), ((8 : Fin 32), BitVec.ofNat 32 0x58), ((9 : Fin 32), BitVec.ofNat 32 0x54),
   ((18 : Fin 32), BitVec.ofNat 32 0x50), ((19 : Fin 32), BitVec.ofNat 32 0x4C),
   ((20 : Fin 32), BitVec.ofNat 32 0x48), ((21 : Fin 32), BitVec.ofNat 32 0x44)]

theorem wmSave_shape : SaveAt wideMulSaveCode 0 wmPs := by simp only [SaveAt]; decide

theorem wmRestore_shape : RestoreAt wideMulRestoreCode 0 wmPs := by simp only [RestoreAt]; decide

theorem fillWord_zero : fillWord 0 = 0 := by decide

/-- Where `widening_mul_fixed::<8, 8>` runs: its code and its helpers' at
their offsets, the 0x60 bytes of stack below `sp0` that it uses, the 16-word
result at `out`, and the 8-word operands at `ap` and `bp`. -/
structure WMEnv (M : Word → BitVec 8) (P sp0 out ap bp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P wideMulCode
  save : CodeIn M (P + 0x1242A) wideMulSaveCode
  restore : CodeIn M (P + 0x1241A) wideMulRestoreCode
  mset : CodeIn M (P + 0x129E4) memsetCode
  stub : CodeIn M (P + 0x12A4C) memcpyStubCode
  body : CodeIn M (P + 0x12A54) memcpyBodyCode
  hsp : sp0.toNat % 4 = 0
  hout : out.toNat % 4 = 0
  hap : ap.toNat % 4 = 0
  hbp : bp.toNat % 4 = 0
  hS : 0x60 ≤ sp0.toNat
  hwo : out.toNat + 64 < 2 ^ 32
  sSC : Sep (sp0 + 0xFFFFFFA0) 0x60 P wideMulCode.length
  sSS : Sep (sp0 + 0xFFFFFFA0) 0x60 (P + 0x1242A) wideMulSaveCode.length
  sSR : Sep (sp0 + 0xFFFFFFA0) 0x60 (P + 0x1241A) wideMulRestoreCode.length
  sSM : Sep (sp0 + 0xFFFFFFA0) 0x60 (P + 0x129E4) memsetCode.length
  sSU : Sep (sp0 + 0xFFFFFFA0) 0x60 (P + 0x12A4C) memcpyStubCode.length
  sSB : Sep (sp0 + 0xFFFFFFA0) 0x60 (P + 0x12A54) memcpyBodyCode.length
  sOC : Sep out 64 P wideMulCode.length
  sOR : Sep out 64 (P + 0x1241A) wideMulRestoreCode.length
  sOU : Sep out 64 (P + 0x12A4C) memcpyStubCode.length
  sOB : Sep out 64 (P + 0x12A54) memcpyBodyCode.length
  sOS : Sep out 64 (sp0 + 0xFFFFFFA0) 0x60
  sAS : Sep ap 32 (sp0 + 0xFFFFFFA0) 0x60
  sBS : Sep bp 32 (sp0 + 0xFFFFFFA0) 0x60

/-- A call from `widening_mul_fixed` to `memset` that zeroes 32 bytes. -/
theorem wm_memset {P : Word} {Mx : Word → BitVec 8} {m : Machine} {off : Nat} {f : Fin 32 → Word}
    {imm o dst : Word} (hP : P.toNat % 2 = 0) (s : St Mx P m off f) (hc : CodeIn Mx P wideMulCode)
    (hms : CodeIn Mx (P + 0x129E4) memsetCode)
    (h1 : fetchRel wideMulCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel wideMulCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x129E4)
    (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hdst : dst.toNat % 4 = 0) (hwd : dst.toNat + 32 < 2 ^ 32) (hsep : Sep dst 32 (P + 0x129E4) memsetCode.length)
    (ha0 : f a0 = dst) (ha1 : f a1 = 0) (ha2 : f a2 = 0x20) :
    ∃ m', Steps m m' ∧ St (fillWords Mx dst 0 8) P m' (off + 8) (reg m') ∧ reg m' a0 = dst ∧
      ∀ r, r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ ra → reg m' r = f r := by
  have hev : (P + 0x129E4).toNat % 2 = 0 := even_at P hP 0x129E4 (by decide)
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb hev
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨m2, c2, pc2, mem2, a02, fr2⟩ := memset_aligned m1 (P + 0x129E4)
    (P + BitVec.ofNat 32 (off + 8)) dst 0 8 (fun i hi => by rw [mem1]; exact hms i hi) hev pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2]; rfl)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) (by decide) hwd (by decide) hdst hsep
  rw [mem1, fillWord_zero] at mem2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], mem2, fun _ => rfl⟩, a02, fun r q2 q3 q4 q5 q6 q7 => ?_⟩
  rw [fr2 r q2 q3 q4 q5 q6, r1 r q7]

/-- A call from `widening_mul_fixed` to `memcpy` that copies 32 bytes. -/
theorem wm_memcpy {P : Word} {Mx : Word → BitVec 8} {m : Machine} {off : Nat} {f : Fin 32 → Word}
    {imm o dst src : Word} (hP : P.toNat % 2 = 0) (s : St Mx P m off f) (hc : CodeIn Mx P wideMulCode)
    (hst : CodeIn Mx (P + 0x12A4C) memcpyStubCode) (hbd : CodeIn Mx (P + 0x12A54) memcpyBodyCode)
    (h1 : fetchRel wideMulCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel wideMulCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = P + 0x12A4C)
    (hl : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hdst : dst.toNat % 4 = 0) (hsrc : src.toNat % 4 = 0) (hwd : dst.toNat + 32 < 2 ^ 32)
    (hds : Sep dst 32 src 32) (hsep : Sep dst 32 (P + 0x12A54) memcpyBodyCode.length)
    (ha0 : f a0 = dst) (ha1 : f a1 = src) (ha2 : f a2 = 0x20) :
    ∃ m', Steps m m' ∧ St (copyWords Mx dst src 8) P m' (off + 8) (reg m') ∧ reg m' a0 = dst ∧
      ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 → r ≠ ra →
        reg m' r = f r := by
  have hev : (P + 0x12A4C).toNat % 2 = 0 := even_at P hP 0x12A4C (by decide)
  obtain ⟨m1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb hev
  have r1 := PEnv.reg1 regs1 s.zero
  have e8 : P + 0x12A4C + 8 = P + 0x12A54 := by rw [BitVec.add_assoc]; rfl
  obtain ⟨m2, c2, pc2, mem2, a02, fr2⟩ := memcpy_aligned m1 (P + 0x12A4C)
    (P + BitVec.ofNat 32 (off + 8)) dst src 8 (fun i hi => by rw [mem1]; exact hst i hi)
    (fun i hi => by rw [mem1, e8]; exact hbd i hi) hev pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2]; rfl)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hl) (by decide) hwd (by decide) hdst hsrc hds
    (by rw [e8]; exact hsep)
  rw [mem1] at mem2
  refine ⟨m2, c1.trans c2, ⟨by rw [pc2], mem2, fun _ => rfl⟩, a02, fun r q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 => ?_⟩
  rw [fr2 r q1 q2 q3 q4 q5 q6 q7 q8 q9, r1 r q10]

/-- The registers `widening_mul_fixed` never writes. -/
def wmKeep (q : Fin 32) : Bool :=
  q.val ∉ [1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 28]

theorem bkeep_ne {p : Fin 32 → Bool} {q r : Fin 32} (h : p q = true) (hr : p r = false) : q ≠ r :=
  fun e => by rw [e, hr] at h; exact Bool.false_ne_true h

theorem fillWords_load_sep {M : Word → BitVec 8} {dst v a : Word} {k : Nat} (h : Sep dst (4 * k) a 4) :
    memLoad32 (fillWords M dst v k) a = memLoad32 M a :=
  memLoad32_congr fun j hj => fillWords_outside k (h.subR (c := j) (l := 1) (by omega))

theorem copyWords_load_sep {M : Word → BitVec 8} {dst src a : Word} {k : Nat} (h : Sep dst (4 * k) a 4) :
    memLoad32 (copyWords M dst src k) a = memLoad32 M a :=
  memLoad32_congr fun j hj => copyWords_outside k (h.subR (c := j) (l := 1) (by omega))

theorem frame_G (sp0 : Word) (h : 0x60 ≤ sp0.toNat) : (sp0 + 0xFFFFFFA0).toNat + 0x60 = sp0.toNat := by
  rw [BitVec.toNat_add]
  have : (0xFFFFFFA0 : Word).toNat = 4294967200 := rfl
  have := sp0.isLt
  omega

set_option maxHeartbeats 4000000 in
/-- `widening_mul_fixed`'s prologue, to the outer loop at 0x42: save the
callee-saved registers in the top of a 0x60-byte frame and zero the 16-word
accumulator below them. -/
theorem wm_pro (m : Machine) {P sp0 out ap bp : Word} (env : WMEnv m.mem P sp0 out ap bp) (hpc : m.pc = P)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = ap) (ha2 : reg m a2 = bp) (hsp : reg m sp = sp0) :
    ∃ n M, Steps m n ∧ St M P n 0x42 (reg n) ∧
      (∀ x, Sep (sp0 + 0xFFFFFFA0) 0x60 x 1 → M x = m.mem x) ∧
      (∀ r o, (r, o) ∈ wmPs → memLoad32 M (sp0 + 0xFFFFFFA0 + o) = reg m r) ∧
      memLoad32 M (sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 0x40) = reg m (22 : Fin 32) ∧
      (∀ i, i < 16 → memLoad32 M (sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 (4 * i)) = 0) ∧
      reg n sp = sp0 + 0xFFFFFFA0 ∧ reg n (5 : Fin 32) = BitVec.ofNat 32 0 ∧
      reg n a6 = sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 (4 * 0) ∧
      reg n (22 : Fin 32) = sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 (4 * 0) ∧ reg n (6 : Fin 32) = 8 ∧
      reg n (21 : Fin 32) = ap ∧ reg n (19 : Fin 32) = bp ∧ reg n (20 : Fin 32) = sp0 + 0xFFFFFFA0 + 0x20 ∧
      reg n (18 : Fin 32) = out ∧ ∀ q, wmKeep q = true → reg n q = reg m q := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hG := frame_G sp0 env.hS
  have hGa : (sp0 + 0xFFFFFFA0).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFFA0) (by decide)
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code wm_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFA0) sp = sp0 + 0xFFFFFFA0 := by
    simp +decide [upd, hsp]; rfl
  have hsv : P + BitVec.ofNat 32 2 + 0x12000 + 0x428 = P + 0x1242A := by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  obtain ⟨m2, c2, u2⟩ := u1.callSave env.code wm_at_2 wm_at_6 (b := P + 0x1242A) hsv
    (even_at P env.hP 0x1242A (by decide)) (even_at P env.hP 0xA (by decide))
    env.save wmSave_shape (by decide) (fun q hq => by
      rw [sp1]
      simp only [wmPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, aligned_add hGa (by decide), env.sSS.sub (by decide)⟩)
  rw [sp1] at u2
  -- code stays put while every write is in the frame
  have codeS : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (sp0 + 0xFFFFFFA0) 0x60 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFFA0) 0x60 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by
      have h1 : Sep (sp0 + 0xFFFFFFA0) 0x60 (_ + BitVec.ofNat 32 i) 1 := hs.subR (c := i) (l := 1) (by omega)
      rw [hM _ h1]; exact hc i hi
  have I2 : ∀ x, Sep (sp0 + 0xFFFFFFA0) 0x60 x 1 →
      saveMem m.mem (sp0 + 0xFFFFFFA0) (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFA0)) wmPs x = m.mem x :=
    fun x hx => saveMem_outside wmPs fun q hq => by
      simp only [wmPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hx.sub (by decide)
  have u2' := u2.self
  have r2 : ∀ q, q ≠ sp → q ≠ t0 → reg m2 q = reg m q := fun q q1 q2 => by
    rw [u2.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, hz]
    · simp [upd, h0, q1, q2]
  have sp2 : reg m2 sp = sp0 + 0xFFFFFFA0 := by rw [u2.regs]; simp +decide [upd]; exact sp1
  obtain ⟨m3, d3, u3⟩ := u2'.sw (codeS env.code env.sSC I2) wm_at_a (off' := 0xC) (by decide)
    (by rw [sp2]; exact aligned_add hGa (k := 0x40) (by decide))
  rw [sp2, show (0x40 : Word) = BitVec.ofNat 32 0x40 from rfl] at u3
  obtain ⟨M3, hM3⟩ : ∃ M3, memStore32 (saveMem m.mem (sp0 + 0xFFFFFFA0)
      (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFA0)) wmPs) (sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 0x40)
      (reg m2 22) = M3 :=
    ⟨_, rfl⟩
  rw [hM3] at u3
  have I3 : ∀ x, Sep (sp0 + 0xFFFFFFA0) 0x60 x 1 → M3 x = m.mem x := fun x hx => by
    rw [← hM3, memStore32_get_sep (hx.sub (c := 0x40) (l := 4) (by decide)), I2 x hx]
  have c3 := codeS env.code env.sSC I3
  have z2 : reg m2 x0 = 0 := u2'.zero
  obtain ⟨m4, d4, u4⟩ := u3.alu c3 wm_at_c (off' := 0xE) (by decide)
  obtain ⟨m5, d5, u5⟩ := u4.alu c3 wm_at_e (off' := 0x10) (by decide)
  obtain ⟨m6, d6, u6⟩ := u5.alu c3 wm_at_10 (off' := 0x12) (by decide)
  obtain ⟨m7, d7, u7⟩ := u6.alu c3 wm_at_12 (off' := 0x14) (by decide)
  obtain ⟨m8, d8, u8⟩ := u7.aluImm c3 wm_at_14 (off' := 0x18) (by decide)
  obtain ⟨m9, d9, u9⟩ := u8.aluImm c3 wm_at_18 (off' := 0x1A) (by decide)
  obtain ⟨m10, d10, u10⟩ := u9.alu c3 wm_at_1a (off' := 0x1C) (by decide)
  have g10 : ∀ q, q ≠ (19 : Fin 32) → q ≠ (21 : Fin 32) → q ≠ (18 : Fin 32) → q ≠ a0 → q ≠ a2 → q ≠ a1 →
      q ≠ (22 : Fin 32) → reg m10 q = reg m2 q := fun q q19 q21 q18 q0 q2 q1 q22 => by
    rw [u10.regs]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd, z2]
    · simp [upd, h0, q19, q21, q18, q0, q2, q1, q22]
  have v0 : reg m10 a0 = sp0 + 0xFFFFFFA0 := by
    rw [u10.regs]; simp +decide only [upd, ↓reduceIte, sp2]; exact BitVec.zero_add _
  have v1 : reg m10 a1 = 0 := by rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
  have v2 : reg m10 a2 = 0x20 := by rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
  have v19 : reg m10 (19 : Fin 32) = bp := by
    rw [u10.regs]; simp +decide only [upd, ↓reduceIte, z2]
    rw [r2 _ (by decide) (by decide), ha2]; exact BitVec.zero_add _
  have v21 : reg m10 (21 : Fin 32) = ap := by
    rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
    rw [r2 _ (by decide) (by decide), ha1]; exact BitVec.zero_add _
  have v18 : reg m10 (18 : Fin 32) = out := by
    rw [u10.regs]; simp +decide only [upd, ↓reduceIte]
    rw [r2 _ (by decide) (by decide), ha0]; exact BitVec.zero_add _
  have v22 : reg m10 (22 : Fin 32) = sp0 + 0xFFFFFFA0 := by
    rw [u10.regs]; simp +decide only [upd, ↓reduceIte, sp2]; exact BitVec.zero_add _
  have hGw : (sp0 + 0xFFFFFFA0).toNat + 0x60 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have hG20 : (sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 0x20).toNat = (sp0 + 0xFFFFFFA0).toNat + 0x20 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨n1, e1, w1, a01, f1⟩ := wm_memset (dst := sp0 + 0xFFFFFFA0) env.hP u10.self c3 (codeS env.mset env.sSM I3)
    wm_at_1c wm_at_20 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x24 (by decide))
    hGa (by omega) (env.sSM.sub (c := 0) (l := 32) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
    v0 v1 v2
  have F1 : ∀ x, Sep (sp0 + 0xFFFFFFA0) 0x60 x 1 → fillWords M3 (sp0 + 0xFFFFFFA0) 0 8 x = m.mem x :=
    fun x hx => by
      rw [fillWords_outside 8 (hx.sub (c := 0) (l := 32) (by decide) |> fun h => by rwa [add_ofNat_zero] at h),
        I3 x hx]
  have c4 := codeS env.code env.sSC F1
  have q1 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → q ≠ (19 : Fin 32) → q ≠ (21 : Fin 32) →
      q ≠ (18 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ (22 : Fin 32) → reg n1 q = reg m2 q :=
    fun q h2 h3 h4 h5 h6 hra h19 h21 h18 h0 h1 h22 => by
      rw [f1 q h2 h3 h4 h5 h6 hra, g10 q h19 h21 h18 h0 h2 h1 h22]
  have sp3 : reg n1 sp = sp0 + 0xFFFFFFA0 := by
    rw [q1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), sp2]
  have z3 : reg n1 x0 = 0 := w1.zero
  obtain ⟨n2, e2, w2⟩ := w1.aluImm c4 wm_at_24 (off' := 0x26) (by decide)
  obtain ⟨n3, e3, w3⟩ := w2.aluImm c4 wm_at_26 (off' := 0x2A) (by decide)
  obtain ⟨n4, e4, w4⟩ := w3.aluImm c4 wm_at_2a (off' := 0x2C) (by decide)
  obtain ⟨n5, e5, w5⟩ := w4.aluImm c4 wm_at_2c (off' := 0x30) (by decide)
  have g14 : ∀ q, q ≠ a0 → q ≠ a2 → q ≠ a1 → q ≠ (20 : Fin 32) → reg n5 q = reg n1 q :=
    fun q h0 h2 h1 h20 => by
      rw [w5.regs]
      by_cases hq : q.val = 0
      · have : q = 0 := Fin.ext hq
        subst this; simp [upd, z3]
      · simp [upd, hq, h0, h2, h1, h20]
  have y0 : reg n5 a0 = sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 0x20 := by
    rw [w5.regs]; simp +decide only [upd, ↓reduceIte, sp3]; rfl
  have y1 : reg n5 a1 = 0 := by rw [w5.regs]; simp +decide only [upd, ↓reduceIte]
  have y2 : reg n5 a2 = 0x20 := by rw [w5.regs]; simp +decide only [upd, ↓reduceIte]
  have y20 : reg n5 (20 : Fin 32) = sp0 + 0xFFFFFFA0 + 0x20 := by
    rw [w5.regs]; simp +decide only [upd, ↓reduceIte, sp3]; rfl
  obtain ⟨n6, e6, w6, a06, f6⟩ := wm_memset (dst := sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 0x20) env.hP w5.self c4
    (codeS env.mset env.sSM F1) wm_at_30 wm_at_34 (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl)
    (even_at P env.hP 0x38 (by decide)) (aligned_add hGa (by decide)) (by omega)
    (env.sSM.sub (c := 0x20) (l := 32) (by decide)) y0 y1 y2
  obtain ⟨M6, hM6⟩ : ∃ M6, fillWords (fillWords M3 (sp0 + 0xFFFFFFA0) 0 8)
      (sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 0x20) 0 8 = M6 := ⟨_, rfl⟩
  rw [hM6] at w6
  have F6 : ∀ x, Sep (sp0 + 0xFFFFFFA0) 0x60 x 1 → M6 x = m.mem x := fun x hx => by
    rw [← hM6, fillWords_outside 8 (hx.sub (c := 0x20) (l := 32) (by decide)), F1 x hx]
  have c6 := codeS env.code env.sSC F6
  have z6 : reg n6 x0 = 0 := w6.zero
  obtain ⟨n7, e7, w7⟩ := w6.aluImm c6 wm_at_38 (off' := 0x3A) (by decide)
  obtain ⟨n8, e8, w8⟩ := w7.alu c6 wm_at_3a (off' := 0x3C) (by decide)
  obtain ⟨n9, e9, w9⟩ := w8.aluImm c6 wm_at_3c (off' := 0x3E) (by decide)
  have b9 : reg n9 (6 : Fin 32) = 8 := by rw [w9.regs]; simp +decide only [upd, ↓reduceIte]
  obtain ⟨n10, e10, w10⟩ := w9.self.notTaken c6 0x42 wm_at_3e (by decide)
    (by rw [b9, w9.self.zero]; decide)
  have g17 : ∀ q, q ≠ (5 : Fin 32) → q ≠ a6 → q ≠ (6 : Fin 32) → reg n10 q = reg n6 q := fun q h5 h16 h6 => by
    rw [w10.regs, w9.regs]
    by_cases hq : q.val = 0
    · have : q = 0 := Fin.ext hq
      subst this; simp [upd, z6]
    · simp [upd, hq, h5, h16, h6]
  -- back to `reg m`, through each call
  have back : ∀ q, q ≠ (5 : Fin 32) → q ≠ a6 → q ≠ (6 : Fin 32) → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ ra →
      q ≠ a0 → q ≠ a1 → q ≠ (20 : Fin 32) → reg n10 q = reg n1 q :=
    fun q h5 h16 h6 h2 h3 h4 h5' hra h0 h1 h20 => by
      rw [g17 q h5 h16 h6, f6 q h2 h3 h4 h5' h16 hra, g14 q h0 h2 h1 h20]
  have sp6 : reg n6 sp = sp0 + 0xFFFFFFA0 := by
    rw [f6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g14 _ (by decide) (by decide) (by decide) (by decide), sp3]
  have sepG : ∀ d, 32 ≤ d → d + 4 ≤ 2 ^ 32 →
      Sep (sp0 + 0xFFFFFFA0) (4 * 8) (sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 d) 4 := fun d h1 h2 => by
    have := sep_offsets (sp0 + 0xFFFFFFA0) (c := 0) (n := 4 * 8) (d := d) (k := 4) (.inl (by omega)) (by decide) h2
    rwa [add_ofNat_zero] at this
  refine ⟨n10, M6, .cons d1 (c2.trans (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
    (.cons d10 (e1.trans (.cons e2 (.cons e3 (.cons e4 (.cons e5 (e6.trans (.cons e7 (.cons e8 (.cons e9
    (.single e10))))))))))))))))))), w10.self, F6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r o h
    simp only [wmPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · rw [← hM6, fillWords_load_sep (sep_offsets _ (.inl (by decide)) (by decide) (by decide)),
        fillWords_load_sep (sepG _ (by decide) (by decide)), ← hM3]
      simp only [saveMem]
      simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same]
      simp +decide only [upd, ↓reduceIte]
  · rw [← hM6, fillWords_load_sep (sep_offsets _ (.inl (by decide)) (by decide) (by decide)),
      fillWords_load_sep (sepG _ (by decide) (by decide)), ← hM3, memLoad32_store32_same,
      r2 _ (by decide) (by decide)]
  · intro i hi
    by_cases h8 : i < 8
    · rw [← hM6, fillWords_load_sep (sep_offsets _ (.inr (by omega)) (by decide) (by omega))]
      exact fillWords_load 8 i h8 (by omega)
    · rw [show sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 (4 * i) =
          sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 0x20 + BitVec.ofNat 32 (4 * (i - 8)) by
        rw [add_ofNat_assoc, show 0x20 + 4 * (i - 8) = 4 * i by omega], ← hM6]
      exact fillWords_load 8 (i - 8) (by omega) (by rw [hG20]; omega)
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), sp3]
  · rw [w10.regs, w9.regs]; simp +decide only [upd, ↓reduceIte, z6]
  · rw [w10.regs, w9.regs]; simp +decide only [upd, ↓reduceIte, sp6]
    exact (BitVec.zero_add _).trans (add_ofNat_zero _).symm
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), f1 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), v22]
    exact (add_ofNat_zero _).symm
  · rw [w10.regs, b9]
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), f1 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), v21]
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), f1 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), v19]
  · rw [g17 _ (by decide) (by decide) (by decide), f6 _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), y20]
  · rw [back _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), f1 _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), v18]
  · intro q hq
    have k := fun r (hr : wmKeep r = false) => bkeep_ne hq hr
    rw [back q (k 5 rfl) (k a6 rfl) (k 6 rfl) (k a2 rfl) (k a3 rfl) (k a4 rfl) (k a5 rfl) (k ra rfl) (k a0 rfl)
      (k a1 rfl) (k 20 rfl), q1 q (k a2 rfl) (k a3 rfl) (k a4 rfl) (k a5 rfl) (k a6 rfl) (k ra rfl) (k 19 rfl)
      (k 21 rfl) (k 18 rfl) (k a0 rfl) (k a1 rfl) (k 22 rfl), r2 q (k sp rfl) (k t0 rfl)]

set_option maxHeartbeats 4000000 in
/-- `widening_mul_fixed`'s epilogue, from 0xB0: copy the accumulator's two
halves to `out`, restore the callee-saved registers, and return. -/
theorem wm_epi {P sp0 out ap bp : Word} {M0 Mx : Word → BitVec 8} {n : Machine} {v : Fin 32 → Word}
    (env : WMEnv M0 P sp0 out ap bp) (s : St Mx P n 0xB0 (reg n))
    (hfr : ∀ x, Sep (sp0 + 0xFFFFFFA0) 0x60 x 1 → Mx x = M0 x)
    (hsl : ∀ r o, (r, o) ∈ wmPs → memLoad32 Mx (sp0 + 0xFFFFFFA0 + o) = v r)
    (hs6 : memLoad32 Mx (sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 0x40) = v (22 : Fin 32))
    (rsp : reg n sp = sp0 + 0xFFFFFFA0) (r18 : reg n (18 : Fin 32) = out) :
    ∃ n', Steps n n' ∧ n'.pc = v ra &&& ~~~1 ∧
      n'.mem = copyWords (copyWords Mx out (sp0 + 0xFFFFFFA0) 8) (out + BitVec.ofNat 32 0x20)
        (sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 0x20) 8 ∧
      reg n' sp = sp0 ∧ (∀ r o, (r, o) ∈ wmPs → reg n' r = v r) ∧ reg n' (22 : Fin 32) = v (22 : Fin 32) ∧
      ∀ q, wmKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have hG := frame_G sp0 env.hS
  have hGa : (sp0 + 0xFFFFFFA0).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFFA0) (by decide)
  have hwo := env.hwo
  have codeX : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn M0 b code →
      Sep (sp0 + 0xFFFFFFA0) 0x60 b code.length → Sep out 64 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFFA0) 0x60 x 1 → Sep out 64 x 1 → M' x = M0 x) → CodeIn M' b code :=
    fun hc hs ho hM i hi => by
      rw [hM _ (hs.subR (c := i) (l := 1) (by omega)) (ho.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have hfr' : ∀ x, Sep (sp0 + 0xFFFFFFA0) 0x60 x 1 → Sep out 64 x 1 → Mx x = M0 x := fun x h _ => hfr x h
  have cx : CodeIn Mx P wideMulCode := codeX env.code env.sSC env.sOC hfr'
  obtain ⟨m1, d1, u1⟩ := s.alu cx wm_at_b0 (off' := 0xB2) (by decide)
  obtain ⟨m2, d2, u2⟩ := u1.aluImm cx wm_at_b2 (off' := 0xB6) (by decide)
  obtain ⟨m3, d3, u3⟩ := u2.alu cx wm_at_b6 (off' := 0xB8) (by decide)
  have k3 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m3 q = reg n q := fun q h0 h1 h2 => by
    rw [u3.regs]
    by_cases hq : q.val = 0
    · have : q = 0 := Fin.ext hq
      subst this; simp [upd, hz]
    · simp [upd, hq, h0, h1, h2]
  have x0' : reg m3 a0 = out := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte, r18]; exact BitVec.zero_add _
  have x1' : reg m3 a1 = sp0 + 0xFFFFFFA0 := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte, hz, rsp]; exact BitVec.zero_add _
  have x2' : reg m3 a2 = 0x20 := by rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
  have hOS := env.sOS
  obtain ⟨m4, c4, u4, a04, f4⟩ := wm_memcpy (dst := out) (src := sp0 + 0xFFFFFFA0) env.hP u3.self cx
    (codeX env.stub env.sSU env.sOU hfr') (codeX env.body env.sSB env.sOB hfr') wm_at_b8 wm_at_bc
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xC0 (by decide)) env.hout hGa (by omega)
    (hOS.sub (c := 0) (l := 32) (by decide) |>.subR (c := 0) (l := 32) (by decide) |> fun h => by
      rwa [add_ofNat_zero, add_ofNat_zero] at h)
    (env.sOB.sub (c := 0) (l := 32) (by decide) |> fun h => by rwa [add_ofNat_zero] at h) x0' x1' x2'
  have F4 : ∀ x, Sep (sp0 + 0xFFFFFFA0) 0x60 x 1 → Sep out 64 x 1 →
      copyWords Mx out (sp0 + 0xFFFFFFA0) 8 x = M0 x := fun x hs ho => by
    rw [copyWords_outside 8 (ho.sub (c := 0) (l := 32) (by decide) |> fun h => by rwa [add_ofNat_zero] at h),
      hfr x hs]
  have c4' := codeX env.code env.sSC env.sOC F4
  have z4 : reg m4 x0 = 0 := u4.zero
  have k4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ ra → reg m4 q = reg n q := fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by
    rw [f4 q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10, k3 q h0 h1 h2]
  have sp4 : reg m4 sp = sp0 + 0xFFFFFFA0 := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), rsp]
  have o4 : reg m4 (18 : Fin 32) = out := by
    rw [k4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), r18]
  obtain ⟨m5, d5, u5⟩ := u4.aluImm c4' wm_at_c0 (off' := 0xC4) (by decide)
  obtain ⟨m6, d6, u6⟩ := u5.aluImm c4' wm_at_c4 (off' := 0xC6) (by decide)
  obtain ⟨m7, d7, u7⟩ := u6.aluImm c4' wm_at_c6 (off' := 0xCA) (by decide)
  have k7 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg m7 q = reg m4 q := fun q h0 h1 h2 => by
    rw [u7.regs]
    by_cases hq : q.val = 0
    · have : q = 0 := Fin.ext hq
      subst this; simp [upd, z4]
    · simp [upd, hq, h0, h1, h2]
  have y0' : reg m7 a0 = out + BitVec.ofNat 32 0x20 := by
    rw [u7.regs]; simp +decide only [upd, ↓reduceIte, o4]; rfl
  have y1' : reg m7 a1 = sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 0x20 := by
    rw [u7.regs]; simp +decide only [upd, ↓reduceIte, sp4]; rfl
  have y2' : reg m7 a2 = 0x20 := by rw [u7.regs]; simp +decide only [upd, ↓reduceIte]
  have hO20 : (out + BitVec.ofNat 32 0x20).toNat = out.toNat + 0x20 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨m8, c8, u8, a08, f8⟩ := wm_memcpy (dst := out + BitVec.ofNat 32 0x20)
    (src := sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 0x20) env.hP u7.self c4'
    (codeX env.stub env.sSU env.sOU F4) (codeX env.body env.sSB env.sOB F4) wm_at_ca wm_at_ce
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xD2 (by decide))
    (aligned_add env.hout (by decide)) (aligned_add hGa (by decide)) (by omega)
    (hOS.sub (c := 0x20) (l := 32) (by decide) |>.subR (c := 0x20) (l := 32) (by decide))
    (env.sOB.sub (c := 0x20) (l := 32) (by decide)) y0' y1' y2'
  obtain ⟨M8, hM8⟩ : ∃ M8, copyWords (copyWords Mx out (sp0 + 0xFFFFFFA0) 8) (out + BitVec.ofNat 32 0x20)
      (sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 0x20) 8 = M8 := ⟨_, rfl⟩
  rw [hM8] at u8
  have F8 : ∀ x, Sep (sp0 + 0xFFFFFFA0) 0x60 x 1 → Sep out 64 x 1 → M8 x = M0 x := fun x hs ho => by
    rw [← hM8, copyWords_outside 8 (ho.sub (c := 0x20) (l := 32) (by decide)), F4 x hs ho]
  -- the frame's top 0x20 bytes, which hold the saved registers, are as they were
  have top : ∀ c, 0x40 ≤ c → c + 4 ≤ 0x60 →
      memLoad32 M8 (sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 c) = memLoad32 Mx (sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 c) :=
    fun c h1 h2 => by
      have so : Sep out 64 (sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 c) 4 := hOS.subR (by omega)
      rw [← hM8, copyWords_load_sep (so.sub (c := 0x20) (l := 32) (by decide)),
        copyWords_load_sep (so.sub (c := 0) (l := 32) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)]
  have c8' := codeX env.code env.sSC env.sOC F8
  have sp8 : reg m8 sp = sp0 + 0xFFFFFFA0 := by
    rw [f8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), k7 _ (by decide) (by decide) (by decide), sp4]
  obtain ⟨m9, c9, u9⟩ := u8.callRestore c8' wm_at_d2 wm_at_d6 (b := P + 0x1241A)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x1241A (by decide))
    (even_at P env.hP 0xDA (by decide)) (codeX env.restore env.sSR env.sOR F8) wmRestore_shape (by decide)
    (fun q hq => by
      rw [sp8]
      simp only [wmPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, by decide, aligned_add hGa (by decide)⟩)
  rw [sp8] at u9
  have slot : ∀ r o, (r, o) ∈ wmPs → 0x40 ≤ o.toNat → o.toNat + 4 ≤ 0x60 →
      memLoad32 M8 (sp0 + 0xFFFFFFA0 + o) = v r := fun r o h h1 h2 => by
    have := top o.toNat h1 h2
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
    rw [this, hsl r o h]
  have rsp9 : restoreRegs M8 (sp0 + 0xFFFFFFA0) (upd (reg m8) t0 (P + BitVec.ofNat 32 (0xCA + 8 + 8))) wmPs sp =
      sp0 + 0xFFFFFFA0 := by
    rw [restoreRegs_sp _ _ _ _ (by decide)]; simp +decide only [upd, ↓reduceIte]; exact sp8
  obtain ⟨m10, d10, u10⟩ := u9.lw c8' wm_at_da (off' := 0xDC) (by decide)
    (by rw [rsp9]; exact aligned_add hGa (k := 0x40) (by decide))
  obtain ⟨m11, d11, u11⟩ := u10.aluImm c8' wm_at_dc (off' := 0xDE) (by decide)
  obtain ⟨m12, d12, pc12, mem12, regs12⟩ := u11.jalr c8' wm_at_de
  have rra : restoreRegs M8 (sp0 + 0xFFFFFFA0) (upd (reg m8) t0 (P + BitVec.ofNat 32 (0xCA + 8 + 8))) wmPs ra =
      v ra := by
    simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
    exact slot ra _ (by simp) (by decide) (by decide)
  refine ⟨m12, .cons d1 (.cons d2 (.cons d3 (c4.trans (.cons d5 (.cons d6 (.cons d7 (c8.trans (c9.trans
    (.cons d10 (.cons d11 (.single d12))))))))))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc12]; simp +decide only [upd, ↓reduceIte]; rw [rra, add_lit_zero]
  · rw [mem12, ← hM8]
  · rw [regs12]; simp +decide only [upd, ↓reduceIte, aluEval]
    rw [rsp9, BitVec.add_assoc]; exact BitVec.add_zero _
  · intro r o h
    rw [regs12]
    simp only [wmPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd, ↓reduceIte]
      exact slot _ _ (by simp) (by decide) (by decide)
  · rw [regs12]; simp +decide only [upd, ↓reduceIte]
    rw [rsp9, show (0x40 : Word) = BitVec.ofNat 32 0x40 from rfl, top 0x40 (by decide) (by decide), hs6]
  · intro q hq
    have k := fun r (hr : wmKeep r = false) => bkeep_ne hq hr
    have hq0 : q.val ≠ 0 ∨ q = 0 := by
      by_cases h : q.val = 0
      · exact .inr (Fin.ext h)
      · exact .inl h
    rw [regs12]
    rcases hq0 with h0 | h0
    · simp only [restoreRegs]
      simp [upd, h0, k ra rfl, k sp rfl, k t0 rfl, k 8 rfl, k 9 rfl, k 18 rfl, k 19 rfl, k 20 rfl, k 21 rfl,
        k 22 rfl]
      rw [f8 q (k a1 rfl) (k a2 rfl) (k a3 rfl) (k a4 rfl) (k a5 rfl) (k a6 rfl) (k a7 rfl) (k t0 rfl) (k t1 rfl)
        (k ra rfl), k7 q (k a0 rfl) (k a1 rfl) (k a2 rfl), k4 q (k a0 rfl) (k a1 rfl) (k a2 rfl) (k a3 rfl)
        (k a4 rfl) (k a5 rfl) (k a6 rfl) (k a7 rfl) (k t0 rfl) (k t1 rfl) (k ra rfl)]
    · subst h0; simp [upd, hz]

theorem wmKeep_row : ∀ q, wmKeep q = true → rowKeep q = true := by decide

set_option maxHeartbeats 4000000 in
/-- **The compiled `widening_mul_fixed::<8, 8>`**, called with the result at
`out` and the operands at `ap` and `bp`. It stores the 512-bit product of the
two 256-bit numbers at `ap` and `bp` in the 16 words at `out`, returns with
`sp` and every register but `a0` through `a7` and `t0` through `t3` as they
were, and changes no memory outside the 0x60 bytes of stack below `sp` and
the result. -/
theorem wideMul_correct (m : Machine) {P sp0 out ap bp retAddr : Word}
    (env : WMEnv m.mem P sp0 out ap bp) (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = ap)
    (ha2 : reg m a2 = bp) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
        q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → reg m' q = reg m q) ∧
      limbVal (wordsAt m'.mem out 16) = limbVal (wordsAt m.mem ap 8) * limbVal (wordsAt m.mem bp 8) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFA0) 0x60 x 1 → Sep out 64 x 1 → m'.mem x = m.mem x := by
  obtain ⟨n, M, c1, s, hF, hsl, hs6, hzero, rsp, r5, r16, r22, r6, r21, r19, r20, r18, keep⟩ :=
    wm_pro m env hpc ha0 ha1 ha2 hsp
  have hG := frame_G sp0 env.hS
  have hGa : (sp0 + 0xFFFFFFA0).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFFA0) (by decide)
  have hwo := env.hwo
  have base0 : ∀ {a : Word} {n : Nat} {b : Word} {k : Nat}, Sep (a + BitVec.ofNat 32 0) n b k → Sep a n b k :=
    fun h => by rwa [add_ofNat_zero] at h
  have cM : CodeIn M P wideMulCode := fun i hi => by
    rw [hF _ (env.sSC.subR (c := i) (l := 1) (by omega))]; exact env.code i hi
  have hv0 : accV M (sp0 + 0xFFFFFFA0) 16 = accV M ap 0 * accV M bp 8 := by
    rw [accV_zero 16 hzero]; exact (Nat.zero_mul _).symm
  obtain ⟨n2, M2, c2, s2, cM2, hF2, hv2, keep2⟩ :=
    wm_rows (B := P) (M0 := M) env.hP hGa env.hap env.hbp (by omega)
      (base0 (env.sAS.symm.sub (c := 0) (l := 64) (by decide)))
      (base0 (env.sBS.symm.sub (c := 0) (l := 64) (by decide)))
      (base0 (env.sSC.sub (c := 0) (l := 64) (by decide)))
      7 0 rfl s cM (fun _ _ => rfl) (fun k _ hk => hzero k hk) hv0 r5 r16 r22 r6 r21 r19 r20
  have upper : ∀ c, 0x40 ≤ c → c + 4 ≤ 0x60 →
      memLoad32 M2 (sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 c) = memLoad32 M (sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => hF2 _ (by
      rw [add_ofNat_assoc]
      exact base0 (sep_offsets (sp0 + 0xFFFFFFA0) (c := 0) (n := 64) (d := c + j) (k := 1) (.inl (by omega))
        (by decide) (by omega)))
  have hfr2 : ∀ x, Sep (sp0 + 0xFFFFFFA0) 0x60 x 1 → M2 x = m.mem x := fun x hx => by
    rw [hF2 x (base0 (hx.sub (c := 0) (l := 64) (by decide))), hF x hx]
  obtain ⟨n3, c3, pc3, mem3, sp3, regs3, r22', keep3⟩ := wm_epi (v := reg m) env s2 hfr2
    (fun r o h => by
      simp only [wmPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      · rw [upper _ (by decide) (by decide)]; exact hsl _ _ (by simp))
    (by rw [upper _ (by decide) (by decide)]; exact hs6)
    (by rw [keep2 _ (by decide), rsp]) (by rw [keep2 _ (by decide), r18])
  refine ⟨n3, c1.trans (c2.trans c3), by rw [pc3, hra, hret], by rw [sp3], ?_, ?_, ?_⟩
  · intro q q0 q1 q2 q3 q4 q5 q6 q7 qt0 qt1 qt2 qt3
    have cat := (by decide : ∀ q : Fin 32, q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨
      q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨ q = (21 : Fin 32) ∨ q = (22 : Fin 32) ∨ q = sp ∨ q = a0 ∨ q = a1 ∨
      q = a2 ∨ q = a3 ∨ q = a4 ∨ q = a5 ∨ q = a6 ∨ q = a7 ∨ q = t0 ∨ q = t1 ∨ q = (7 : Fin 32) ∨
      q = (28 : Fin 32) ∨ wmKeep q = true) q
    rcases cat with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; exact regs3 _ (BitVec.ofNat 32 0x5C) (by simp)
    · subst h; exact regs3 _ (BitVec.ofNat 32 0x58) (by simp)
    · subst h; exact regs3 _ (BitVec.ofNat 32 0x54) (by simp)
    · subst h; exact regs3 _ (BitVec.ofNat 32 0x50) (by simp)
    · subst h; exact regs3 _ (BitVec.ofNat 32 0x4C) (by simp)
    · subst h; exact regs3 _ (BitVec.ofNat 32 0x48) (by simp)
    · subst h; exact regs3 _ (BitVec.ofNat 32 0x44) (by simp)
    · subst h; exact r22'
    · subst h; rw [sp3, hsp]
    · exact absurd h q0
    · exact absurd h q1
    · exact absurd h q2
    · exact absurd h q3
    · exact absurd h q4
    · exact absurd h q5
    · exact absurd h q6
    · exact absurd h q7
    · exact absurd h qt0
    · exact absurd h qt1
    · exact absurd h qt2
    · exact absurd h qt3
    · rw [keep3 q h, keep2 q (wmKeep_row q h), keep q h]
  · have hO20 : (out + BitVec.ofNat 32 0x20).toNat = out.toNat + 0x20 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hOS := env.sOS
    have outw : ∀ i, i < 16 → memLoad32 n3.mem (out + BitVec.ofNat 32 (4 * i)) =
        memLoad32 M2 (sp0 + 0xFFFFFFA0 + BitVec.ofNat 32 (4 * i)) := fun i hi => by
      rw [mem3]
      by_cases h8 : i < 8
      · rw [copyWords_load_sep (sep_offsets out (.inr (by omega)) (by decide) (by omega))]
        exact copyWords_load 8 i h8 (by omega)
      · rw [show out + BitVec.ofNat 32 (4 * i) = out + BitVec.ofNat 32 0x20 + BitVec.ofNat 32 (4 * (i - 8)) by
            rw [add_ofNat_assoc, show 0x20 + 4 * (i - 8) = 4 * i by omega],
          copyWords_load 8 (i - 8) (by omega) (by rw [hO20]; omega),
          copyWords_load_sep (base0 (hOS.sub (c := 0) (l := 32) (by decide)) |>.subR (c := 0x20 + 4 * (i - 8))
            (l := 4) (by omega) |> fun h => by rwa [← add_ofNat_assoc] at h),
          add_ofNat_assoc, show 0x20 + 4 * (i - 8) = 4 * i by omega]
    have opv : ∀ {b : Word}, Sep b 32 (sp0 + 0xFFFFFFA0) 0x60 → accV M b 8 = accV m.mem b 8 := fun hb =>
      accV_congr 8 fun l hl => memLoad32_congr fun j hj => hF _ (by
        have := hb.symm.subR (c := 4 * l + j) (l := 1) (by omega)
        rwa [← add_ofNat_assoc] at this)
    rw [limbVal_wordsAt, limbVal_wordsAt, limbVal_wordsAt, accV_congr2 16 outw, hv2, opv env.sAS, opv env.sBS]
  · intro x hS hO
    rw [mem3, copyWords_outside 8 (hO.sub (c := 0x20) (l := 32) (by decide)),
      copyWords_outside 8 (base0 (hO.sub (c := 0) (l := 32) (by decide))), hfr2 x hS]

end C3.RV32
