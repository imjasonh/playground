import C3BootProofs.Proofs.Sha2OneShot

/-!
# SHA-256 of a list of byte strings, as compiled

The compiled `c3_crypto::sha::sha256_parts` builds a fresh hasher in its
frame like `sha256`, absorbs each of its slices with `update`, moves the
hasher with `memcpy`, and calls `finalize`. `sha256Parts_correct` runs it
through those functions' theorems.
-/

namespace C3.RV32

open C3.Image

section

set_option maxRecDepth 20000

theorem pt_at_0 : fetchRel sha256PartsCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF20, 2) := by decide
theorem pt_at_2 : fetchRel sha256PartsCode 0x2 = some (.store .sw sp ra 0xDC, 2) := by decide
theorem pt_at_4 : fetchRel sha256PartsCode 0x4 = some (.store .sw sp (8 : Fin 32) 0xD8, 2) := by decide
theorem pt_at_6 : fetchRel sha256PartsCode 0x6 = some (.store .sw sp (9 : Fin 32) 0xD4, 2) := by decide
theorem pt_at_8 : fetchRel sha256PartsCode 0x8 = some (.store .sw sp (18 : Fin 32) 0xD0, 2) := by decide
theorem pt_at_a : fetchRel sha256PartsCode 0xA = some (.alu .add (8 : Fin 32) x0 a2, 2) := by decide
theorem pt_at_c : fetchRel sha256PartsCode 0xC = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem pt_at_e : fetchRel sha256PartsCode 0xE = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem pt_at_10 : fetchRel sha256PartsCode 0x10 = some (.aluImm .add a0 sp 0x40, 2) := by decide
theorem pt_at_12 : fetchRel sha256PartsCode 0x12 = some (.lui a1 0x3FCC4000, 4) := by decide
theorem pt_at_16 : fetchRel sha256PartsCode 0x16 = some (.aluImm .add a1 a1 0x2A8, 4) := by decide
theorem pt_at_1a : fetchRel sha256PartsCode 0x1A = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem pt_at_1e : fetchRel sha256PartsCode 0x1E = some (.auipc ra 0xE000, 4) := by decide
theorem pt_at_22 : fetchRel sha256PartsCode 0x22 = some (.jalr ra ra 0xFFFFFCA4, 4) := by decide
theorem pt_at_26 : fetchRel sha256PartsCode 0x26 = some (.store .sb sp x0 0x3F, 4) := by decide
theorem pt_at_2a : fetchRel sha256PartsCode 0x2A = some (.store .sw sp x0 0x60, 2) := by decide
theorem pt_at_2c : fetchRel sha256PartsCode 0x2C = some (.store .sw sp x0 0x64, 2) := by decide
theorem pt_at_2e : fetchRel sha256PartsCode 0x2E = some (.aluImm .sll (8 : Fin 32) (8 : Fin 32) 0x3, 2) := by decide
theorem pt_at_30 : fetchRel sha256PartsCode 0x30 = some (.branch .beq (8 : Fin 32) x0 0x16, 2) := by decide
theorem pt_at_32 : fetchRel sha256PartsCode 0x32 = some (.load .lw a1 (9 : Fin 32) 0x0, 2) := by decide
theorem pt_at_34 : fetchRel sha256PartsCode 0x34 = some (.load .lw a2 (9 : Fin 32) 0x4, 2) := by decide
theorem pt_at_36 : fetchRel sha256PartsCode 0x36 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x8, 2) := by decide
theorem pt_at_38 : fetchRel sha256PartsCode 0x38 = some (.alu .add a0 x0 sp, 2) := by decide
theorem pt_at_3a : fetchRel sha256PartsCode 0x3A = some (.auipc ra 0x0, 4) := by decide
theorem pt_at_3e : fetchRel sha256PartsCode 0x3E = some (.jalr ra ra 0xFFFFFEFA, 4) := by decide
theorem pt_at_42 : fetchRel sha256PartsCode 0x42 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFF8, 2) := by decide
theorem pt_at_44 : fetchRel sha256PartsCode 0x44 = some (.branch .bne (8 : Fin 32) x0 0xFFFFFFEE, 2) := by decide
theorem pt_at_46 : fetchRel sha256PartsCode 0x46 = some (.aluImm .add a0 sp 0x68, 2) := by decide
theorem pt_at_48 : fetchRel sha256PartsCode 0x48 = some (.alu .add a1 x0 sp, 2) := by decide
theorem pt_at_4a : fetchRel sha256PartsCode 0x4A = some (.aluImm .add a2 x0 0x68, 4) := by decide
theorem pt_at_4e : fetchRel sha256PartsCode 0x4E = some (.auipc ra 0xE000, 4) := by decide
theorem pt_at_52 : fetchRel sha256PartsCode 0x52 = some (.jalr ra ra 0xFFFFFC74, 4) := by decide
theorem pt_at_56 : fetchRel sha256PartsCode 0x56 = some (.aluImm .add a1 sp 0x68, 2) := by decide
theorem pt_at_58 : fetchRel sha256PartsCode 0x58 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem pt_at_5a : fetchRel sha256PartsCode 0x5A = some (.auipc ra 0x0, 4) := by decide
theorem pt_at_5e : fetchRel sha256PartsCode 0x5E = some (.jalr ra ra 0xFFFFFD74, 4) := by decide
theorem pt_at_62 : fetchRel sha256PartsCode 0x62 = some (.load .lw ra sp 0xDC, 2) := by decide
theorem pt_at_64 : fetchRel sha256PartsCode 0x64 = some (.load .lw (8 : Fin 32) sp 0xD8, 2) := by decide
theorem pt_at_66 : fetchRel sha256PartsCode 0x66 = some (.load .lw (9 : Fin 32) sp 0xD4, 2) := by decide
theorem pt_at_68 : fetchRel sha256PartsCode 0x68 = some (.load .lw (18 : Fin 32) sp 0xD0, 2) := by decide
theorem pt_at_6a : fetchRel sha256PartsCode 0x6A = some (.aluImm .add sp sp 0xE0, 2) := by decide
theorem pt_at_6c : fetchRel sha256PartsCode 0x6C = some (.jalr x0 ra 0x0, 2) := by decide

theorem ptInit_end : blockEnd sha256PartsCode 0xA ssInit = some 0x1E := by decide

end

/-- The pointer of slice `i` of the slices whose (pointer, length) pairs
start at `P`. -/
def partPtr (M : Word → BitVec 8) (P : Word) (i : Nat) : Word := memLoad32 M (P + BitVec.ofNat 32 (8 * i))

/-- The length of slice `i`. -/
def partLen (M : Word → BitVec 8) (P : Word) (i : Nat) : Nat := (memLoad32 M (P + BitVec.ofNat 32 (8 * i + 4))).toNat

/-- The bytes of the first `k` slices, in order. -/
def partsBytes (M : Word → BitVec 8) (P : Word) : Nat → Bytes
  | 0 => []
  | k + 1 => partsBytes M P k ++ memBytes M (partPtr M P k) (partLen M P k)

theorem partsBytes_length_le (M : Word → BitVec 8) (P : Word) {j k : Nat} (h : j ≤ k) :
    (partsBytes M P j).length ≤ (partsBytes M P k).length := by
  induction k with
  | zero => rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hj | hj
    · have := ih (by omega); simp only [partsBytes, List.length_append]; omega
    · rw [show j = k + 1 by omega]; exact Nat.le_refl _

set_option maxRecDepth 20000 in
/-- `sha256_parts`'s start, from offset 0xA to 0x1E, as `sha256`'s. -/
theorem St.ptInit {M : Word → BitVec 8} {m : Machine} {f : Fin 32 → Word}
    (s : St M (BitVec.ofNat 32 sha256PartsAddress) m 0xA f)
    (hc : CodeIn M (BitVec.ofNat 32 sha256PartsAddress) sha256PartsCode) :
    ∃ m', Steps m m' ∧ St M (BitVec.ofNat 32 sha256PartsAddress) m' 0x1E (reg m') ∧
      reg m' s0 = f a2 ∧ reg m' s1 = f a1 ∧ reg m' s2 = f a0 ∧ reg m' a0 = f sp + 0x40 ∧
      reg m' a1 = BitVec.ofNat 32 shaIVAddress ∧ reg m' a2 = BitVec.ofNat 32 32 ∧
      ∀ r, r ≠ t0 → r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ a0 → r ≠ a1 → r ≠ a2 → reg m' r = f r := by
  have hz := s.zero
  obtain ⟨m1, c1, u1⟩ := St.block ssInit s hc ptInit_end (by simp [BlockOk, BInstr.ok, ssInit])
  have R : ∀ r, reg m1 r = (runBlock ssInit (M, f)).2 r := u1.regs
  refine ⟨m1, c1, ⟨u1.pc, by rw [u1.mem]; rfl, fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r q5 q8 q9 q18 q10 q11 q12 => ?_⟩
  all_goals first
    | (rw [R]; simp only [runBlock, BInstr.run, ssInit]
       rw [updz (by simp [upd]) q12, updz (by simp [upd]) q11, updz (by simp [upd]) q11, updz (by simp [upd]) q10,
         updz (by simp [upd]) q18, updz (by simp [upd]) q9, updz hz q8])
    | (rw [R]; simp +decide only [runBlock, BInstr.run, ssInit, upd_app, ↓reduceIte]
       try (first | rfl | exact BitVec.zero_add _ | (rw [hz]; exact BitVec.zero_add _) | (rw [hz]; rfl)))

/-- Where `sha256_parts` runs: `sha256`'s environment, with the `k` slice
descriptors at `P` in place of the input: each slice below 0x40000000 and
apart from the stack, the descriptors too, and all the slices' bytes
together below 2^32. -/
structure PartsEnv (M : Word → BitVec 8) (out P sp0 : Word) (k : Nat) : Prop where
  cX : CodeIn M (BitVec.ofNat 32 sha256PartsAddress) sha256PartsCode
  cIV : CodeIn M (BitVec.ofNat 32 shaIVAddress) shaIVData
  cU : CodeIn M (BitVec.ofNat 32 shaUpdateAddress) shaUpdateCode
  cUBlk : CodeIn M (BitVec.ofNat 32 shaUpdateBlocksAddress) shaUpdateBlocksCode
  cF : CodeIn M (BitVec.ofNat 32 shaFinalizeAddress) shaFinalizeCode
  cZ : CodeIn M (BitVec.ofNat 32 shaZero32Address) shaZero32Code
  cFBlk : CodeIn M (BitVec.ofNat 32 shaFinBlockAddress) shaFinBlockCode
  cMs : CodeIn M (BitVec.ofNat 32 memsetAddress) memsetCode
  cMS : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  cMB : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  cC : CodeIn M (BitVec.ofNat 32 sha256CompressAddress) sha256CompressCode
  cI : CodeIn M (BitVec.ofNat 32 sha256CompressAddress + 0x25A) rangeFromIndexCode
  cK : CodeIn M (BitVec.ofNat 32 shaKAddress) shaKData
  hsp : sp0.toNat % 16 = 0
  hspl : 0x270 ≤ sp0.toNat
  hspw : sp0.toNat ≤ 0x40000000
  hOw : out.toNat + 32 ≤ 0x40000000
  hP : P.toNat % 4 = 0
  hPw : P.toNat + 8 * k ≤ 0x40000000
  sPF : Sep P (8 * k) (sp0 + 0xFFFFFD90) 0x270
  hlen : (partsBytes M P k).length < 2 ^ 32
  parts : ∀ i, i < k → partLen M P i < 2 ^ 31 ∧ (partPtr M P i).toNat + partLen M P i ≤ 0x40000000 ∧
    Sep (partPtr M P i) (partLen M P i) (sp0 + 0xFFFFFD90) 0x270
  sOF : Sep out 32 (sp0 + 0xFFFFFD90) 0x270
  sKF : Sep (BitVec.ofNat 32 shaKAddress) 256 (sp0 + 0xFFFFFD90) 0x270
  sIF : Sep (BitVec.ofNat 32 shaIVAddress) 32 (sp0 + 0xFFFFFD90) 0x270

theorem ofNat_toNat32 (w : Word) : BitVec.ofNat 32 w.toNat = w :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt w.isLt)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- `sha256_parts`'s loop from offset 0x32: with `r` slices left from slice
`j`, it absorbs each one into the hasher at `F` with `update`, until none
are left, and reaches 0x46. `MH` is memory with the fresh hasher; the loop
changes nothing but the hasher and `update`'s stack below `F`. -/
theorem pt_loop {M0 MH : Word → BitVec 8} {out P sp0 F R : Word} {k : Nat}
    (E : PartsEnv M0 out P sp0 k) (hRd : sp0 + 0xFFFFFD90 = R) (hFR : F = R + BitVec.ofNat 32 0x190)
    (MHR : ∀ x, Sep R 0x270 x 1 → MH x = M0 x) :
    ∀ r j (n : Machine) (Mx : Word → BitVec 8), j + r = k → 0 < r →
      St Mx (BitVec.ofNat 32 sha256PartsAddress) n 0x32 (reg n) →
      (∀ x, Sep (F + 0xFFFFFF00) 0x100 x 1 → Sep F 0x68 x 1 → Mx x = MH x) →
      HasherAt Mx F (partsBytes M0 P j) →
      reg n s0 = BitVec.ofNat 32 (8 * r) → reg n s1 = P + BitVec.ofNat 32 (8 * j) → reg n sp = F →
      ∃ n' My, Steps n n' ∧ St My (BitVec.ofNat 32 sha256PartsAddress) n' 0x46 (reg n') ∧
        (∀ x, Sep (F + 0xFFFFFF00) 0x100 x 1 → Sep F 0x68 x 1 → My x = MH x) ∧
        HasherAt My F (partsBytes M0 P k) ∧
        ∀ q, q ≠ ra → q ≠ (3 : Fin 32) → q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 →
          q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) →
          q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) → q ≠ s0 → q ≠ s1 → reg n' q = reg n q := by
  let Q := BitVec.ofNat 32 sha256PartsAddress
  have hspw := E.hspw
  have hspl := E.hspl
  have sPF := E.sPF; have sKF := E.sKF
  rw [hRd] at sPF sKF
  have hRn : R.toNat = sp0.toNat - 0x270 := by
    rw [← hRd, BitVec.toNat_add, show (0xFFFFFD90 : Word).toNat = 2 ^ 32 - 0x270 from rfl]; omega
  have hRc : ∀ c, c ≤ 0x270 → (R + BitVec.ofNat 32 c).toNat = R.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hFn : F.toNat = sp0.toNat - 0xE0 := by rw [hFR, hRc _ (by omega), hRn]; omega
  have hFa : F.toNat % 16 = 0 := by rw [hFn]; have := E.hsp; omega
  have hFa4 : F.toNat % 4 = 0 := by omega
  have Rx : ∀ c l, c + l ≤ 0x270 → ∀ x, Sep R 0x270 x 1 → Sep (R + BitVec.ofNat 32 c) l x 1 :=
    fun c l h x hx => hx.sub (c := c) (l := l) h
  have codeX : ∀ (My : Word → BitVec 8), (∀ x, Sep R 0x270 x 1 → My x = M0 x) →
      ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn My b code := fun My h b code hc hb hbl i hi => by
    rw [h _ ((data_code (by rw [hRn]; omega) hb hbl).subR (c := i) (l := 1) (by omega))]
    exact hc i hi
  have eU : F + 0xFFFFFF00 = R + BitVec.ofNat 32 0x90 := by rw [hFR, BitVec.add_assoc]; rfl
  have agree : ∀ My : Word → BitVec 8, (∀ x, Sep (F + 0xFFFFFF00) 0x100 x 1 → Sep F 0x68 x 1 → My x = MH x) →
      ∀ x, Sep R 0x270 x 1 → My x = M0 x := fun My h x hx => by
    rw [h x (by rw [eU]; exact Rx _ _ (by omega) x hx) (by rw [hFR]; exact Rx _ _ (by omega) x hx), MHR x hx]
  intro r
  induction r with
  | zero => intro _ _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ r ih =>
    intro j n Mx hjk _ s hinv H hs0 hs1 hsp
    have hMx := agree Mx hinv
    have hcx := codeX Mx hMx _ _ E.cX (by decide) (by decide)
    have hj : j < k := by omega
    obtain ⟨hlt, hpw, hps⟩ := E.parts j hj
    rw [hRd] at hps
    have aP : (P + BitVec.ofNat 32 (8 * j)).toNat % 4 = 0 := aligned_add E.hP (by omega)
    have dP : ∀ c, c < 8 → Mx (P + BitVec.ofNat 32 (8 * j + c)) = M0 (P + BitVec.ofNat 32 (8 * j + c)) :=
      fun c hc => hMx _ (sPF.sub (c := 8 * j + c) (l := 1) (by omega)).symm
    obtain ⟨n1, d1, u1⟩ := s.lw hcx pt_at_32 (off' := 0x34) (by decide) (by rw [hs1, add_lit_zero]; exact aP)
    have K1 := u1.upd_ne s.zero
    have u1' : St Mx Q n1 0x34 (reg n1) := u1.self
    have a1_1 : reg n1 a1 = partPtr M0 P j := by
      rw [u1.upd_eq (by decide), hs1, add_lit_zero]
      exact memLoad32_congr fun i hi => by rw [add_ofNat_assoc]; exact dP i (by omega)
    obtain ⟨n2, d2, u2⟩ := u1'.lw hcx pt_at_34 (off' := 0x36) (by decide)
      (by rw [K1 s1 (by decide), hs1, show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]
          exact aligned_add E.hP (by omega))
    have K2 := u2.upd_ne u1'.zero
    have u2' : St Mx Q n2 0x36 (reg n2) := u2.self
    have a2_2 : reg n2 a2 = BitVec.ofNat 32 (partLen M0 P j) := by
      rw [u2.upd_eq (by decide), K1 s1 (by decide), hs1, show (4 : Word) = BitVec.ofNat 32 4 from rfl,
        add_ofNat_assoc, partLen, ofNat_toNat32]
      exact memLoad32_congr fun i hi => by rw [add_ofNat_assoc, show 8 * j + 4 + i = 8 * j + (4 + i) by omega]
                                           exact dP (4 + i) (by omega)
    obtain ⟨n3, d3, u3⟩ := u2'.aluImm hcx pt_at_36 (off' := 0x38) (by decide)
    have K3 := u3.upd_ne u2'.zero
    have u3' : St Mx Q n3 0x38 (reg n3) := u3.self
    have s1_3 : reg n3 s1 = P + BitVec.ofNat 32 (8 * (j + 1)) := by
      rw [u3.upd_eq (by decide), K2 s1 (by decide), K1 s1 (by decide), hs1]
      show P + BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 8 = _
      rw [add_ofNat_assoc, show 8 * j + 8 = 8 * (j + 1) by omega]
    obtain ⟨n4, d4, u4⟩ := u3'.alu hcx pt_at_38 (off' := 0x3A) (by decide)
    have K4 := u4.upd_ne u3'.zero
    have u4' : St Mx Q n4 0x3A (reg n4) := u4.self
    have K14 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ s1 → reg n4 q = reg n q := fun q h0 h1 h2 h9 => by
      rw [K4 q h0, K3 q h9, K2 q h2, K1 q h1]
    have sp4 : reg n4 sp = F := by rw [K14 sp (by decide) (by decide) (by decide) (by decide), hsp]
    obtain ⟨n5, c5, pc5, mem5, regs5⟩ := u4'.callRa hcx pt_at_3a pt_at_3e (cb := BitVec.ofNat 32 shaUpdateAddress)
      (by decide) (by decide)
    have r5 : ∀ q, q ≠ ra → reg n5 q = reg n4 q := fun q h => by rw [regs5]; exact updz u4'.zero h
    have hdat : memBytes Mx (partPtr M0 P j) (partLen M0 P j) = memBytes M0 (partPtr M0 P j) (partLen M0 P j) :=
      memBytes_congr fun i hi => hMx _ (hps.sub (c := i) (l := 1) (by omega)).symm
    have hl1 : (partsBytes M0 P (j + 1)).length ≤ (partsBytes M0 P k).length := partsBytes_length_le M0 P (by omega)
    have hl2 := E.hlen
    simp only [partsBytes, List.length_append, memBytes_length] at hl1
    obtain ⟨n6, c6, pc6, sp6, K6, H6, fr6⟩ := shaUpdate_correct n5 (S := F) (D := partPtr M0 P j) (sp0 := F)
      (n := partLen M0 P j) (msg := partsBytes M0 P j) (retAddr := Q + BitVec.ofNat 32 (0x3A + 8))
      { cU := by rw [mem5]; exact codeX Mx hMx _ _ E.cU (by decide) (by decide)
        cBlk := by rw [mem5]; exact codeX Mx hMx _ _ E.cUBlk (by decide) (by decide)
        cC := by rw [mem5]; exact codeX Mx hMx _ _ E.cC (by decide) (by decide)
        cI := by rw [mem5]; exact codeX Mx hMx _ _ E.cI (by decide) (by decide)
        cK := fun i hi => by
          have hi' : i < 256 := by rw [show shaKData.length = 256 from rfl] at hi; exact hi
          rw [mem5, hMx _ (sKF.sub (c := i) (l := 1) (by omega)).symm]; exact E.cK i hi
        cMS := by rw [mem5]; exact codeX Mx hMx _ _ E.cMS (by decide) (by decide)
        cMB := by rw [mem5]; exact codeX Mx hMx _ _ E.cMB (by decide) (by decide)
        hS := hFa4
        hSw := by omega
        hsp := hFa
        hspl := by omega
        hspw := by omega
        hDw := hpw
        sDS := by rw [hFR]; exact hps.subR (c := 0x190) (l := 0x68) (by omega)
        sDF := by rw [eU]; exact hps.subR (c := 0x90) (l := 0x100) (by omega)
        sSF := by rw [eU, hFR]; exact sep_offsets R (Or.inr (by omega)) (by omega) (by omega)
        sKS := by rw [hFR]; exact sKF.subR (c := 0x190) (l := 0x68) (by omega)
        sKF := by rw [eU]; exact sKF.subR (c := 0x90) (l := 0x100) (by omega) }
      pc5 (by rw [r5 a0 (by decide), u4.upd_eq (by decide), u3'.zero, K3 sp (by decide), K2 sp (by decide),
          K1 sp (by decide), hsp]; exact BitVec.zero_add _)
      (by rw [r5 a1 (by decide), K4 a1 (by decide), K3 a1 (by decide), K2 a1 (by decide), a1_1])
      (by rw [r5 a2 (by decide), K4 a2 (by decide), K3 a2 (by decide), a2_2])
      (by rw [regs5]; simp +decide only [upd_app, ↓reduceIte]) (by decide)
      (by rw [r5 sp (by decide), sp4]) (by rw [mem5]; exact H) hlt (by omega)
    rw [mem5, hdat] at H6
    rw [mem5] at fr6
    obtain ⟨MU, hMU⟩ : ∃ MU, n6.mem = MU := ⟨_, rfl⟩
    rw [hMU] at H6 fr6
    have inv6 : ∀ x, Sep (F + 0xFFFFFF00) 0x100 x 1 → Sep F 0x68 x 1 → MU x = MH x := fun x h1 h2 => by
      rw [fr6 x h1 h2, hinv x h1 h2]
    have aMU := agree MU inv6
    have cxU := codeX MU aMU _ _ E.cX (by decide) (by decide)
    have u6 : St MU Q n6 0x42 (reg n6) := ⟨by rw [pc6], hMU, fun _ => rfl⟩
    have k6 : ∀ q, q ≠ ra → q ≠ (3 : Fin 32) → q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ a0 → q ≠ a1 →
        q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) →
        q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) → q ≠ sp → reg n6 q = reg n5 q := K6
    obtain ⟨n7, d7, u7⟩ := u6.aluImm cxU pt_at_42 (off' := 0x44) (by decide)
    have K7 := u7.upd_ne u6.zero
    have u7' : St MU Q n7 0x44 (reg n7) := u7.self
    have s0_6 : reg n6 s0 = BitVec.ofNat 32 (8 * (r + 1)) := by
      rw [k6 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), r5 s0 (by decide), K14 s0 (by decide) (by decide) (by decide) (by decide), hs0]
    have s0_7 : reg n7 s0 = BitVec.ofNat 32 (8 * r) := by
      rw [u7.upd_eq (by decide), s0_6]
      show BitVec.ofNat 32 (8 * (r + 1)) + 0xFFFFFFF8 = _
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFF8 : Word).toNat = 2 ^ 32 - 8 from rfl]
      have := E.hPw; omega
    have H6' : HasherAt MU F (partsBytes M0 P (j + 1)) := H6
    have KK : ∀ q, q ≠ ra → q ≠ (3 : Fin 32) → q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 →
        q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) →
        q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) → q ≠ s0 → q ≠ s1 → reg n7 q = reg n q :=
      fun q q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q8 q9 => by
        have q2 : q ≠ sp ∨ q = sp := by by_cases h : q = sp <;> simp [h]
        rw [K7 q q8]
        rcases q2 with q2 | rfl
        · rw [k6 q q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q2, r5 q q1,
            K14 q q10 q11 q12 q9]
        · rw [sp6, hsp]
    by_cases hr : r = 0
    · subst hr
      obtain ⟨n8, d8, u8⟩ := u7'.notTaken cxU 0x46 pt_at_44 (by decide) (by
        simp only [branchTaken]; rw [s0_7, u7'.zero]; decide)
      have hk : j + 1 = k := by omega
      rw [hk] at H6'
      exact ⟨n8, MU, .cons d1 (.cons d2 (.cons d3 (.cons d4 (c5.trans (c6.trans (.cons d7 (.single d8))))))),
        u8.self, inv6, H6', fun q q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q8 q9 => by
          rw [u8.regs, KK q q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q8 q9]⟩
    · obtain ⟨n8, d8, u8⟩ := u7'.taken cxU 0x32 pt_at_44 (by decide) (by
        simp only [branchTaken, s0_7, u7'.zero, bne_iff_ne, ne_eq]
        intro h; apply hr
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl, Nat.mod_eq_of_lt (by have := E.hPw; omega)] at this
        omega)
      have sp7 : reg n7 sp = F := by
        rw [KK sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), hsp]
      have s1_7 : reg n7 s1 = P + BitVec.ofNat 32 (8 * (j + 1)) := by
        rw [K7 s1 (by decide), k6 s1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), r5 s1 (by decide), K4 s1 (by decide), s1_3]
      obtain ⟨n9, My, c9, u9, inv9, H9, K9⟩ := ih (j + 1) n8 MU (by omega) (by omega) u8.self inv6 H6'
        (by rw [u8.regs, s0_7]) (by rw [u8.regs, s1_7]) (by rw [u8.regs, sp7])
      exact ⟨n9, My, .cons d1 (.cons d2 (.cons d3 (.cons d4 (c5.trans (c6.trans (.cons d7 (.cons d8 c9))))))),
        u9, inv9, H9, fun q q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q8 q9 => by
          rw [K9 q q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q8 q9, u8.regs,
            KK q q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q8 q9]⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- **The compiled `c3_crypto::sha::sha256_parts`.** Called with `k` slice
descriptors at `P` and a 32-byte output at `out`, it writes FIPS 180-4's
SHA-256 digest of the slices' bytes, in order, to `out`. It returns to `retAddr` with `sp` restored and the
callee-saved registers kept, and changes no memory outside the output and
0x270 bytes of stack below `sp`. `n` is below 2^31, as Rust's slice lengths
are. -/
theorem sha256Parts_correct (m : Machine) {out P sp0 retAddr : Word} {k : Nat}
    (E : PartsEnv m.mem out P sp0 k) (hpc : m.pc = BitVec.ofNat 32 sha256PartsAddress)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = P) (ha2 : reg m a2 = BitVec.ofNat 32 k)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ r, r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 →
        r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) →
        r ≠ (31 : Fin 32) → reg m' r = reg m r) ∧
      memBytes m'.mem out 32 = sha256 (partsBytes m.mem P k) ∧
      ∀ x, Sep (sp0 + 0xFFFFFD90) 0x270 x 1 → Sep out 32 x 1 → m'.mem x = m.mem x := by
  let Q := BitVec.ofNat 32 sha256PartsAddress
  let M0 := m.mem
  let R := sp0 + 0xFFFFFD90
  let F := sp0 + 0xFFFFFF20
  have hspw := E.hspw
  have hspl := E.hspl
  have hOw := E.hOw
  have hRn : R.toNat = sp0.toNat - 0x270 := by
    show (sp0 + 0xFFFFFD90).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFD90 : Word).toNat = 2 ^ 32 - 0x270 from rfl]; omega
  have hRc : ∀ c, c ≤ 0x270 → (R + BitVec.ofNat 32 c).toNat = R.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hFR : F = R + BitVec.ofNat 32 0x190 := by
    show sp0 + 0xFFFFFF20 = sp0 + 0xFFFFFD90 + BitVec.ofNat 32 0x190; rw [BitVec.add_assoc]; rfl
  have Fc : ∀ c, F + BitVec.ofNat 32 c = R + BitVec.ofNat 32 (0x190 + c) := fun c => by rw [hFR, add_ofNat_assoc]
  have hFn : F.toNat = sp0.toNat - 0xE0 := by rw [hFR, hRc _ (by omega), hRn]; omega
  have hFc : ∀ c, c ≤ 0xE0 → (F + BitVec.ofNat 32 c).toNat = F.toNat + c := fun c hc => by
    rw [Fc, hRc _ (by omega), hFn, hRn]; omega
  have hFa : F.toNat % 16 = 0 := by rw [hFn]; have := E.hsp; omega
  have hFa4 : F.toNat % 4 = 0 := by omega
  have Rx : ∀ c l, c + l ≤ 0x270 → ∀ x, Sep R 0x270 x 1 → Sep (R + BitVec.ofNat 32 c) l x 1 :=
    fun c l h x hx => hx.sub (c := c) (l := l) h
  have Rd : ∀ c l, c + l ≤ 0x270 → ∀ (b : Word) (k : Nat), 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (R + BitVec.ofNat 32 c) l b k := fun c l h b k hb hbk =>
    data_code (by rw [hRc _ (by omega)]; omega) hb hbk
  have codeX : ∀ (My : Word → BitVec 8), (∀ x, Sep R 0x270 x 1 → My x = M0 x) →
      ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn My b code := fun My h b code hc hb hbl i hi => by
    rw [h _ ((data_code (by rw [hRn]; omega) hb hbl).subR (c := i) (l := 1) (by omega))]
    exact hc i hi
  -- The frame and the four saved registers.
  have st0 : St M0 Q m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  obtain ⟨m1, e1, u1⟩ := st0.aluImm E.cX pt_at_0 (off' := 2) (by decide)
  have K1 := u1.upd_ne st0.zero
  have u1' : St M0 Q m1 2 (reg m1) := u1.self
  have sp1 : reg m1 sp = F := by rw [u1.upd_eq (by decide), hsp]; rfl
  have slotA : ∀ c, c + 4 ≤ 0xE0 → c % 4 = 0 → (reg m1 sp + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h1 h2 => by
    rw [sp1]; exact aligned_add hFa4 h2
  obtain ⟨m2, e2, u2⟩ := u1'.sw E.cX pt_at_2 (off' := 4) (by decide) (slotA 0xDC (by omega) (by omega))
  have cS : ∀ (Ma : Word → BitVec 8) (c : Nat) (v : Word), c + 4 ≤ 0xE0 →
      ∀ (b : Word) (code : List Nat), CodeIn Ma b code → 0x40000000 ≤ b.toNat → b.toNat + code.length ≤ 2 ^ 32 →
      CodeIn (memStore32 Ma (F + BitVec.ofNat 32 c) v) b code := fun Ma c v h b code hc hb hbl =>
    hc.store32 (by rw [Fc]; exact Rd _ _ (by omega) _ _ hb hbl)
  rw [sp1] at u2
  have cX2 := cS _ 0xDC (reg m1 ra) (by omega) _ _ E.cX (by decide) (by decide)
  obtain ⟨m3, e3, u3⟩ := u2.sw cX2 pt_at_4 (off' := 6) (by decide) (by rw [sp1]; exact aligned_add hFa4 (k := 0xD8) (by decide))
  rw [sp1] at u3
  have cX3 := cS _ 0xD8 (reg m1 s0) (by omega) _ _ cX2 (by decide) (by decide)
  obtain ⟨m4, e4, u4⟩ := u3.sw cX3 pt_at_6 (off' := 8) (by decide) (by rw [sp1]; exact aligned_add hFa4 (k := 0xD4) (by decide))
  rw [sp1] at u4
  have cX4 := cS _ 0xD4 (reg m1 s1) (by omega) _ _ cX3 (by decide) (by decide)
  obtain ⟨m5, e5, u5⟩ := u4.sw cX4 pt_at_8 (off' := 0xA) (by decide) (by rw [sp1]; exact aligned_add hFa4 (k := 0xD0) (by decide))
  rw [sp1] at u5
  let M1 := memStore32 (memStore32 (memStore32 (memStore32 M0 (F + 0xDC) (reg m1 ra)) (F + 0xD8) (reg m1 s0))
    (F + 0xD4) (reg m1 s1)) (F + 0xD0) (reg m1 s2)
  have M1R : ∀ x, Sep R 0x270 x 1 → M1 x = M0 x := fun x hx => by
    show memStore32 (memStore32 (memStore32 (memStore32 M0 _ _) _ _) _ _) _ _ x = _
    rw [memStore32_get_sep (show Sep (F + 0xD0) 4 x 1 by rw [show F + (0xD0 : Word) = F + BitVec.ofNat 32 0xD0 from rfl, Fc]; exact Rx _ _ (by omega) x hx),
      memStore32_get_sep (show Sep (F + 0xD4) 4 x 1 by rw [show F + (0xD4 : Word) = F + BitVec.ofNat 32 0xD4 from rfl, Fc]; exact Rx _ _ (by omega) x hx),
      memStore32_get_sep (show Sep (F + 0xD8) 4 x 1 by rw [show F + (0xD8 : Word) = F + BitVec.ofNat 32 0xD8 from rfl, Fc]; exact Rx _ _ (by omega) x hx),
      memStore32_get_sep (show Sep (F + 0xDC) 4 x 1 by rw [show F + (0xDC : Word) = F + BitVec.ofNat 32 0xDC from rfl, Fc]; exact Rx _ _ (by omega) x hx)]
  have cM1 := codeX M1 M1R
  have cX5 := cM1 _ _ E.cX (by decide) (by decide)
  obtain ⟨m6, c6, u6, s0_6, s1_6, s2_6, a0_6, a1_6, a2_6, K6⟩ := u5.ptInit cX5
  rw [K1 a2 (by decide), ha2] at s0_6
  rw [K1 a1 (by decide), ha1] at s1_6
  rw [K1 a0 (by decide), ha0] at s2_6
  rw [sp1] at a0_6
  obtain ⟨m7, e7, u7⟩ := u6.auipc cX5 pt_at_1e (off' := 0x22) (by decide)
  obtain ⟨m8, e8, pc8, mem8, regs8⟩ := u7.call cX5 pt_at_22
  have r8 : ∀ r, r ≠ ra → reg m8 r = reg m6 r := fun r h => by
    rw [regs8]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact u6.zero.symm
    · simp [upd, h0, h]
  have sp6 : reg m6 sp = F := by
    rw [K6 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp1]
  have sp8 : reg m8 sp = F := by rw [r8 sp (by decide), sp6]
  have eF16 : F + 0xFFFFFFF0 = R + BitVec.ofNat 32 0x180 := by rw [hFR, BitVec.add_assoc]; rfl
  have hF16 : (F + 0xFFFFFFF0).toNat = R.toNat + 0x180 := by rw [eF16, hRc _ (by omega)]
  obtain ⟨m9, c9, pc9, sp9, a09, mem9, K9⟩ := memcpy_correct m8 (BitVec.ofNat 32 memcpyStubAddress)
    (Q + BitVec.ofNat 32 0x26) (F + BitVec.ofNat 32 0x40) (BitVec.ofNat 32 shaIVAddress) 32
    (fun i hi => by show m8.mem _ = _; rw [mem8]; exact cM1 _ _ E.cMS (by decide) (by decide) i hi) (by decide)
    (by rw [pc8, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]; decide)
    (by rw [r8 a0 (by decide), a0_6]; rfl) (by rw [r8 a1 (by decide), a1_6]) (by rw [r8 a2 (by decide), a2_6])
    (by rw [regs8]; simp +decide [upd]; try rfl) (by decide)
    (by
      rw [mem8, sp8]
      exact { code := cM1 _ _ E.cMB (by decide) (by decide)
              hDC := data_code (by rw [hFc _ (by omega)]; omega) (by decide) (by decide)
              hFC := data_code (by rw [hF16, hRn]; omega) (by decide) (by decide)
              hdF := by rw [Fc, eF16]; exact sep_offsets R (Or.inr (by omega)) (by omega) (by omega)
              hsF := by rw [eF16]; exact E.sIF.subR (c := 0x180) (l := 16) (by omega)
              hsep := by rw [Fc]; exact (E.sIF.subR (c := 0x190 + 0x40) (l := 32) (by omega)).symm
              hF := by rw [hF16, hRn]; have := E.hsp; omega
              hFw := by rw [hF16, hRn]; omega
              hdw := by rw [hFc _ (by omega)]; omega
              hsw := by decide })
  rw [mem8, sp8, eF16] at mem9
  let MA := m9.mem
  have mA : ∀ x, Sep (R + BitVec.ofNat 32 0x180) 16 x 1 →
      MA x = copyBytes M1 (F + BitVec.ofNat 32 0x40) (BitVec.ofNat 32 shaIVAddress) 32 x := mem9
  have MAR : ∀ x, Sep R 0x270 x 1 → MA x = M0 x := fun x hx => by
    rw [mA x (Rx _ _ (by omega) x hx), copyBytes_sep (by rw [Fc]; exact Rx _ _ (by omega) x hx) (Nat.le_refl 32),
      M1R x hx]
  have cMA := codeX MA MAR
  have cXA := cMA _ _ E.cX (by decide) (by decide)
  have u9 : St MA Q m9 0x26 (reg m9) := ⟨by rw [pc9], rfl, fun _ => rfl⟩
  have k9 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp →
      reg m9 r = reg m8 r := K9
  have sp9' : reg m9 sp = F := by rw [sp9, sp8]
  -- A fresh hasher: the initial hash value, an empty buffer, and no blocks.
  obtain ⟨m10, e10, u10⟩ := u9.sb cXA pt_at_26 (off' := 0x2A) (by decide)
  rw [sp9', u9.zero] at u10
  have cXA1 := cXA.store8 (a := F + 0x3F) (v := (0 : Word).extractLsb' 0 8)
    (by rw [show F + (0x3F : Word) = F + BitVec.ofNat 32 0x3F from rfl, Fc]; exact Rd _ _ (by omega) _ _ (by decide) (by decide))
  obtain ⟨m11, e11, u11⟩ := u10.sw cXA1 pt_at_2a (off' := 0x2C) (by decide)
    (by rw [sp9']; exact aligned_add hFa4 (k := 0x60) (by decide))
  rw [sp9', u9.zero] at u11
  have cXA2 := cXA1.store32 (a := F + 0x60) (v := 0)
    (by rw [show F + (0x60 : Word) = F + BitVec.ofNat 32 0x60 from rfl, Fc]; exact Rd _ _ (by omega) _ _ (by decide) (by decide))
  obtain ⟨m12, e12, u12⟩ := u11.sw cXA2 pt_at_2c (off' := 0x2E) (by decide)
    (by rw [sp9']; exact aligned_add hFa4 (k := 0x64) (by decide))
  rw [sp9', u9.zero] at u12
  let MH := memStore32 (memStore32 (memStore8 MA (F + 0x3F) ((0 : Word).extractLsb' 0 8)) (F + 0x60) 0) (F + 0x64) 0
  have FR : ∀ c, c < 0xE0 → Sep R 0x270 (F + BitVec.ofNat 32 c) 1 → False := fun c hc h => by
    have := h (0x190 + c) (by omega) 0 (by decide); rw [add_ofNat_zero, Fc] at this; exact this rfl
  have MHR : ∀ x, Sep R 0x270 x 1 → MH x = M0 x := fun x hx => by
    show memStore32 (memStore32 (memStore8 MA _ _) _ _) _ _ x = _
    rw [memStore32_get_sep (show Sep (F + 0x64) 4 x 1 by rw [show F + (0x64 : Word) = F + BitVec.ofNat 32 0x64 from rfl, Fc]; exact Rx _ _ (by omega) x hx),
      memStore32_get_sep (show Sep (F + 0x60) 4 x 1 by rw [show F + (0x60 : Word) = F + BitVec.ofNat 32 0x60 from rfl, Fc]; exact Rx _ _ (by omega) x hx),
      memStore8_ne (show x ≠ F + 0x3F from fun e => by
        rw [e, show F + (0x3F : Word) = F + BitVec.ofNat 32 0x3F from rfl] at hx; exact FR _ (by omega) hx),
      MAR x hx]
  have hF' : ∀ c, c < 0x68 → ∀ d, d < 0x68 → c ≠ d → F + BitVec.ofNat 32 c ≠ F + BitVec.ofNat 32 d :=
    fun c hc d hd h => add_ofNat_ne F (by omega) (by omega) h
  have H0 : HasherAt MH F [] :=
    { hlen := by decide
      pos := by
        show memStore32 (memStore32 (memStore8 MA _ _) _ _) _ _ _ = _
        rw [memStore32_get_sep (show Sep (F + 0x64) 4 (F + 0x3F) 1 from
            sep_offsets F (c := 0x64) (d := 0x3F) (Or.inr (by omega)) (by omega) (by omega)),
          memStore32_get_sep (show Sep (F + 0x60) 4 (F + 0x3F) 1 from
            sep_offsets F (c := 0x60) (d := 0x3F) (Or.inr (by omega)) (by omega) (by omega)), memStore8_same]
        rfl
      buf := rfl
      hash := by
        show _ = Sha256.h0
        rw [← iv_words (M := M0) E.cIV]
        apply wordsAt_copy; intro k hk
        have hk' : k < 32 := hk
        rw [show F + (0x40 : Word) = F + BitVec.ofNat 32 0x40 from rfl, add_ofNat_assoc]
        show memStore32 (memStore32 (memStore8 MA _ _) _ _) _ _ _ = _
        rw [memStore32_get_sep (show Sep (F + 0x64) 4 (F + BitVec.ofNat 32 (0x40 + k)) 1 from
            sep_offsets F (c := 0x64) (d := 0x40 + k) (Or.inr (by omega)) (by omega) (by omega)),
          memStore32_get_sep (show Sep (F + 0x60) 4 (F + BitVec.ofNat 32 (0x40 + k)) 1 from
            sep_offsets F (c := 0x60) (d := 0x40 + k) (Or.inr (by omega)) (by omega) (by omega)),
          memStore8_ne (show F + BitVec.ofNat 32 (0x40 + k) ≠ F + 0x3F from hF' _ (by omega) 0x3F (by omega) (by omega)),
          mA _ (by rw [Fc]; exact sep_offsets R (Or.inl (by omega)) (by omega) (by omega)),
          ← add_ofNat_assoc, copyBytes_in (by omega) (by omega), M1R _ (E.sIF.sub (c := k) (l := 1) (by omega)).symm]
      lo := by
        show memLoad32 (memStore32 (memStore32 (memStore8 MA _ _) _ _) _ _) _ = _
        rw [memLoad32_store32_sep (show Sep (F + 0x64) 4 (F + 0x60) 4 from
            sep_offsets F (c := 0x64) (d := 0x60) (Or.inr (by omega)) (by omega) (by omega)), memLoad32_store32_same]
        rfl
      hi := by
        show memLoad32 (memStore32 (memStore32 (memStore8 MA _ _) _ _) _ _) _ = _
        rw [memLoad32_store32_same] }
  have cMH := codeX MH MHR
  have cXH := cMH _ _ E.cX (by decide) (by decide)
  have u12' : St MH Q m12 0x2E (reg m12) := u12.self
  have r12 : ∀ r, reg m12 r = reg m9 r := fun r => u12.regs r
  have K69 : ∀ r, r ≠ ra → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp →
      reg m12 r = reg m6 r := fun r q1 q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2 => by
    rw [r12, k9 r q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2, r8 r q1]
  have s0_12 : reg m12 s0 = BitVec.ofNat 32 k := by
    rw [K69 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s0_6]
  have s1_12 : reg m12 s1 = P := by
    rw [K69 s1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s1_6]
  have s2_12 : reg m12 s2 = out := by
    rw [K69 s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s2_6]
  have sp12 : reg m12 sp = F := by rw [r12, sp9']
  -- The slices, each through `update`.
  obtain ⟨m13, e13, u13⟩ := u12'.aluImm cXH pt_at_2e (off' := 0x30) (by decide)
  have K13 := u13.upd_ne u12'.zero
  have u13' : St MH Q m13 0x30 (reg m13) := u13.self
  have s0_13 : reg m13 s0 = BitVec.ofNat 32 (8 * k) := by
    rw [u13.upd_eq (by decide), s0_12]
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 32 k <<< ((3 : Word).toNat % 32)).toNat = _
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (3 : Word).toNat % 32 = 3 from rfl,
      Nat.shiftLeft_eq]
    have := E.hPw; omega
  have HL : ∃ n18 MU, Steps m13 n18 ∧ St MU Q n18 0x46 (reg n18) ∧
      (∀ x, Sep (F + 0xFFFFFF00) 0x100 x 1 → Sep F 0x68 x 1 → MU x = MH x) ∧
      HasherAt MU F (partsBytes M0 P k) ∧
      ∀ q, q ≠ ra → q ≠ (3 : Fin 32) → q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 →
        q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) →
        q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) → q ≠ s0 → q ≠ s1 → reg n18 q = reg m13 q := by
    by_cases hk : k = 0
    · obtain ⟨n14, d14, u14⟩ := u13'.taken cXH 0x46 pt_at_30 (by decide) (by
        simp only [branchTaken]; rw [s0_13, u13'.zero, hk]; decide)
      exact ⟨n14, MH, .single d14, u14.self, fun _ _ _ => rfl, by rw [hk]; exact H0,
        fun q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by rw [u14.regs]⟩
    · obtain ⟨n14, d14, u14⟩ := u13'.notTaken cXH 0x32 pt_at_30 (by decide) (by
        simp only [branchTaken, s0_13, u13'.zero]
        apply decide_eq_false; intro h; apply hk
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl, Nat.mod_eq_of_lt (by have := E.hPw; omega)] at this
        omega)
      obtain ⟨n18, MU, c18, u18, inv18, H18, K18⟩ := pt_loop E rfl hFR MHR k 0 n14 MH (by omega) (by omega) u14.self
        (fun _ _ _ => rfl) H0 (by rw [u14.regs, s0_13])
        (by rw [u14.regs, K13 s1 (by decide), s1_12, Nat.mul_zero, add_ofNat_zero])
        (by rw [u14.regs, K13 sp (by decide), sp12])
      exact ⟨n18, MU, .cons d14 c18, u18, inv18, H18,
        fun q q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q8 q9 => by
          rw [K18 q q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q8 q9, u14.regs]⟩
  obtain ⟨m18, MU, c18, u18, fU, HU, K18⟩ := HL
  have eU : F + 0xFFFFFF00 = R + BitVec.ofNat 32 0x90 := by rw [hFR, BitVec.add_assoc]; rfl
  have MUR : ∀ x, Sep R 0x270 x 1 → MU x = M0 x := fun x hx => by
    rw [fU x (by rw [eU]; exact Rx _ _ (by omega) x hx) (by rw [hFR]; exact Rx _ _ (by omega) x hx), MHR x hx]
  have cMU := codeX MU MUR
  have cXU := cMU _ _ E.cX (by decide) (by decide)
  have K1218 : ∀ r, r ≠ ra → r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 →
      r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) →
      r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) → r ≠ sp → r ≠ s0 → r ≠ s1 → reg m18 r = reg m12 r :=
    fun r q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 _ q8 q9 => by
      rw [K18 r q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q8 q9, K13 r q8]
  have sp18' : reg m18 sp = F := by
    rw [K18 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), K13 sp (by decide), sp12]
  -- Move the hasher, as `finalize` takes it by value.
  obtain ⟨m19, e19, u19⟩ := u18.aluImm cXU pt_at_46 (off' := 0x48) (by decide)
  have K19 := u19.upd_ne u18.zero
  have u19' : St MU Q m19 0x48 (reg m19) := u19.self
  obtain ⟨m20, e20, u20⟩ := u19'.alu cXU pt_at_48 (off' := 0x4A) (by decide)
  have K20 := u20.upd_ne u19'.zero
  have u20' : St MU Q m20 0x4A (reg m20) := u20.self
  obtain ⟨m21, e21, u21⟩ := u20'.aluImm cXU pt_at_4a (off' := 0x4E) (by decide)
  have K21 := u21.upd_ne u20'.zero
  have u21' : St MU Q m21 0x4E (reg m21) := u21.self
  obtain ⟨m22, e22, u22⟩ := u21'.auipc cXU pt_at_4e (off' := 0x52) (by decide)
  obtain ⟨m23, e23, pc23, mem23, regs23⟩ := u22.call cXU pt_at_52
  have r23 : ∀ r, r ≠ ra → reg m23 r = reg m21 r := fun r h => by
    rw [regs23]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact u21'.zero.symm
    · simp [upd, h0, h]
  have K1823 : ∀ r, r ≠ ra → r ≠ a0 → r ≠ a1 → r ≠ a2 → reg m23 r = reg m18 r := fun r q1 q10 q11 q12 => by
    rw [r23 r q1, K21 r q12, K20 r q11, K19 r q10]
  have sp23 : reg m23 sp = F := by rw [K1823 sp (by decide) (by decide) (by decide) (by decide), sp18']
  obtain ⟨m24, c24, pc24, sp24, a024, mem24, K24⟩ := memcpy_correct m23 (BitVec.ofNat 32 memcpyStubAddress)
    (Q + BitVec.ofNat 32 0x56) (F + BitVec.ofNat 32 0x68) F 0x68
    (fun i hi => by show m23.mem _ = _; rw [mem23]; exact cMU _ _ E.cMS (by decide) (by decide) i hi) (by decide)
    (by rw [pc23, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]; decide)
    (by rw [r23 a0 (by decide), K21 a0 (by decide), K20 a0 (by decide), u19.upd_eq (by decide), sp18']; rfl)
    (by rw [r23 a1 (by decide), K21 a1 (by decide), u20.upd_eq (by decide), u19'.zero, K19 sp (by decide), sp18']
        exact BitVec.zero_add _)
    (by rw [r23 a2 (by decide), u21.upd_eq (by decide), u20'.zero]; rfl)
    (by rw [regs23]; simp +decide [upd]; try rfl) (by decide)
    (by
      rw [mem23, sp23]
      exact { code := cMU _ _ E.cMB (by decide) (by decide)
              hDC := data_code (by rw [hFc _ (by omega)]; omega) (by decide) (by decide)
              hFC := data_code (by rw [hF16, hRn]; omega) (by decide) (by decide)
              hdF := by rw [Fc, eF16]; exact sep_offsets R (Or.inr (by omega)) (by omega) (by omega)
              hsF := by rw [eF16, hFR]; exact sep_offsets R (Or.inr (by omega)) (by omega) (by omega)
              hsep := by
                have h := sep_offsets F (c := 0x68) (n := 0x68) (d := 0) (k := 0x68) (Or.inr (by omega)) (by omega)
                  (by omega)
                rwa [add_ofNat_zero] at h
              hF := by rw [hF16, hRn]; have := E.hsp; omega
              hFw := by rw [hF16, hRn]; omega
              hdw := by rw [hFc _ (by omega)]; omega
              hsw := by omega })
  rw [mem23, sp23, eF16] at mem24
  let MC := m24.mem
  have mC : ∀ x, Sep (R + BitVec.ofNat 32 0x180) 16 x 1 → MC x = copyBytes MU (F + BitVec.ofNat 32 0x68) F 0x68 x := mem24
  have MCR : ∀ x, Sep R 0x270 x 1 → MC x = M0 x := fun x hx => by
    rw [mC x (Rx _ _ (by omega) x hx), copyBytes_sep (by rw [Fc]; exact Rx _ _ (by omega) x hx) (Nat.le_refl _),
      MUR x hx]
  have HC : HasherAt MC (F + BitVec.ofNat 32 0x68) (partsBytes M0 P k) := HU.copy fun i hi => by
    rw [mC (F + BitVec.ofNat 32 0x68 + BitVec.ofNat 32 i) (by
        rw [add_ofNat_assoc, Fc]
        exact sep_offsets R (c := 0x180) (n := 16) (d := 0x190 + (0x68 + i)) (k := 1) (Or.inl (by omega)) (by omega)
          (by omega)),
      copyBytes_in hi (by omega)]
  have cMC := codeX MC MCR
  have cXC := cMC _ _ E.cX (by decide) (by decide)
  have u24 : St MC Q m24 0x56 (reg m24) := ⟨by rw [pc24], rfl, fun _ => rfl⟩
  have k24 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp →
      reg m24 r = reg m23 r := K24
  have sp24' : reg m24 sp = F := by rw [sp24, sp23]
  obtain ⟨m25, e25, u25⟩ := u24.aluImm cXC pt_at_56 (off' := 0x58) (by decide)
  have K25 := u25.upd_ne u24.zero
  have u25' : St MC Q m25 0x58 (reg m25) := u25.self
  obtain ⟨m26, e26, u26⟩ := u25'.alu cXC pt_at_58 (off' := 0x5A) (by decide)
  have K26 := u26.upd_ne u25'.zero
  have u26' : St MC Q m26 0x5A (reg m26) := u26.self
  obtain ⟨m27, e27, u27⟩ := u26'.auipc cXC pt_at_5a (off' := 0x5E) (by decide)
  obtain ⟨m28, e28, pc28, mem28, regs28⟩ := u27.call cXC pt_at_5e
  have r28 : ∀ r, r ≠ ra → reg m28 r = reg m26 r := fun r h => by
    rw [regs28]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact u26'.zero.symm
    · simp [upd, h0, h]
  have s2_24 : reg m24 s2 = out := by
    rw [k24 s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), K1823 s2 (by decide) (by decide)
      (by decide) (by decide), K1218 s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), s2_12]
  have eR : F + 0xFFFFFE70 = R := by rw [hFR, BitVec.add_assoc]; exact BitVec.add_zero R
  have hS68 : (F + BitVec.ofNat 32 0x68).toNat = F.toNat + 0x68 := hFc _ (by omega)
  obtain ⟨m29, c29, pc29, sp29, K29, out29, fr29⟩ := shaFinalize_correct m28 (S := F + BitVec.ofNat 32 0x68)
    (out := out) (sp0 := F) (retAddr := Q + BitVec.ofNat 32 0x62) (msg := partsBytes M0 P k)
    { cF := by rw [mem28]; exact cMC _ _ E.cF (by decide) (by decide)
      cZ := by rw [mem28]; exact cMC _ _ E.cZ (by decide) (by decide)
      cBlk := by rw [mem28]; exact cMC _ _ E.cFBlk (by decide) (by decide)
      cMs := by rw [mem28]; exact cMC _ _ E.cMs (by decide) (by decide)
      cMS := by rw [mem28]; exact cMC _ _ E.cMS (by decide) (by decide)
      cMB := by rw [mem28]; exact cMC _ _ E.cMB (by decide) (by decide)
      cC := by rw [mem28]; exact cMC _ _ E.cC (by decide) (by decide)
      cI := by rw [mem28]; exact cMC _ _ E.cI (by decide) (by decide)
      cK := fun i hi => by
        have hi' : i < 256 := by rw [show shaKData.length = 256 from rfl] at hi; exact hi
        rw [mem28, MCR _ (E.sKF.sub (c := i) (l := 1) (by omega)).symm]; exact E.cK i hi
      hS := by rw [hS68]; omega
      hSw := by rw [hS68]; omega
      hsp := hFa
      hspl := by omega
      hspw := by omega
      hOw := hOw
      sSF := by
        rw [eR, Fc]
        have h := sep_offsets R (c := 0x190 + 0x68) (n := 0x68) (d := 0) (k := 0x190) (Or.inr (by omega)) (by omega)
          (by omega)
        rwa [add_ofNat_zero] at h
      sOF := by rw [eR]; have h := E.sOF.subR (c := 0) (l := 0x190) (by omega); rwa [add_ofNat_zero] at h
      sOS := by rw [Fc]; exact E.sOF.subR (c := 0x190 + 0x68) (l := 0x68) (by omega)
      sKS := by rw [Fc]; exact E.sKF.subR (c := 0x190 + 0x68) (l := 0x68) (by omega)
      sKF := by rw [eR]; have h := E.sKF.subR (c := 0) (l := 0x190) (by omega); rwa [add_ofNat_zero] at h }
    (by rw [pc28, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]; decide)
    (by rw [r28 a0 (by decide), u26.upd_eq (by decide), u25'.zero, K25 s2 (by decide), s2_24]
        exact BitVec.zero_add _)
    (by rw [r28 a1 (by decide), K26 a1 (by decide), u25.upd_eq (by decide), sp24']; rfl)
    (by rw [regs28]; simp +decide [upd]; try rfl) (by decide)
    (by rw [r28 sp (by decide), K26 sp (by decide), K25 sp (by decide), sp24']) (by rw [mem28]; exact HC)
  rw [eR, mem28] at fr29
  let MF := m29.mem
  have fF : ∀ x, Sep R 0x190 x 1 → Sep (F + BitVec.ofNat 32 0x68) 0x68 x 1 → Sep out 32 x 1 → MF x = MC x := fr29
  -- The saved registers survive in the frame.
  have slotF : ∀ k, 0xD0 ≤ k → k < 0xE0 → MF (F + BitVec.ofNat 32 k) = M1 (F + BitVec.ofNat 32 k) := by
    intro k h1 h2
    have rk : F + BitVec.ofNat 32 k = R + BitVec.ofNat 32 (0x190 + k) := Fc k
    have hR1 : Sep R 0x190 (F + BitVec.ofNat 32 k) 1 := by
      rw [rk]
      have h := sep_offsets R (c := 0) (n := 0x190) (d := 0x190 + k) (k := 1) (Or.inl (by omega)) (by omega)
        (by omega)
      rwa [add_ofNat_zero] at h
    have hS1 : Sep (F + BitVec.ofNat 32 0x68) 0x68 (F + BitVec.ofNat 32 k) 1 :=
      sep_offsets F (c := 0x68) (d := k) (Or.inl (by omega)) (by omega) (by omega)
    have hO1 : Sep out 32 (F + BitVec.ofNat 32 k) 1 := by rw [rk]; exact E.sOF.subR (c := 0x190 + k) (l := 1) (by omega)
    have hF1 : Sep F 0x68 (F + BitVec.ofNat 32 k) 1 := by
      have h := sep_offsets F (c := 0) (n := 0x68) (d := k) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
      rwa [add_ofNat_zero] at h
    rw [fF _ hR1 hS1 hO1,
      mC _ (by rw [rk]; exact sep_offsets R (Or.inl (by omega)) (by omega) (by omega)),
      copyBytes_sep (sep_offsets F (Or.inl (by omega)) (by omega) (by omega)) (Nat.le_refl _),
      fU _ (by rw [eU, rk]; exact sep_offsets R (Or.inl (by omega)) (by omega) (by omega)) hF1]
    show memStore32 (memStore32 (memStore8 MA _ _) _ _) _ _ _ = _
    rw [memStore32_get_sep (show Sep (F + 0x64) 4 (F + BitVec.ofNat 32 k) 1 from
        sep_offsets F (c := 0x64) (d := k) (Or.inl (by omega)) (by omega) (by omega)),
      memStore32_get_sep (show Sep (F + 0x60) 4 (F + BitVec.ofNat 32 k) 1 from
        sep_offsets F (c := 0x60) (d := k) (Or.inl (by omega)) (by omega) (by omega)),
      memStore8_ne (show F + BitVec.ofNat 32 k ≠ F + 0x3F from add_ofNat_ne F (c := k) (d := 0x3F) (by omega) (by omega) (by omega)),
      mA _ (by rw [rk]; exact sep_offsets R (Or.inl (by omega)) (by omega) (by omega)),
      copyBytes_sep (sep_offsets F (Or.inl (by omega)) (by omega) (by omega)) (Nat.le_refl _)]
  have ldF : ∀ c, 0xD0 ≤ c → c + 4 ≤ 0xE0 → memLoad32 MF (F + BitVec.ofNat 32 c) = memLoad32 M1 (F + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact slotF _ (by omega) (by omega)
  have so : ∀ c d, c < 0xE0 → d < 0xE0 → c + 4 ≤ d ∨ d + 4 ≤ c → Sep (F + BitVec.ofNat 32 c) 4 (F + BitVec.ofNat 32 d) 4 :=
    fun c d hc hd h => sep_offsets F h (by omega) (by omega)
  have vRa : memLoad32 M1 (F + 0xDC) = reg m ra := by
    show memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 M0 _ _) _ _) _ _) _ _) _ = _
    rw [memLoad32_store32_sep (show Sep (F + 0xD0) 4 (F + 0xDC) 4 from so 0xD0 0xDC (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xDC) 4 from so 0xD4 0xDC (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (show Sep (F + 0xD8) 4 (F + 0xDC) 4 from so 0xD8 0xDC (by omega) (by omega) (by omega)),
      memLoad32_store32_same, K1 ra (by decide)]
  have vS0 : memLoad32 M1 (F + 0xD8) = reg m s0 := by
    show memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 M0 _ _) _ _) _ _) _ _) _ = _
    rw [memLoad32_store32_sep (show Sep (F + 0xD0) 4 (F + 0xD8) 4 from so 0xD0 0xD8 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (show Sep (F + 0xD4) 4 (F + 0xD8) 4 from so 0xD4 0xD8 (by omega) (by omega) (by omega)),
      memLoad32_store32_same, K1 s0 (by decide)]
  have vS1 : memLoad32 M1 (F + 0xD4) = reg m s1 := by
    show memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 M0 _ _) _ _) _ _) _ _) _ = _
    rw [memLoad32_store32_sep (show Sep (F + 0xD0) 4 (F + 0xD4) 4 from so 0xD0 0xD4 (by omega) (by omega) (by omega)),
      memLoad32_store32_same, K1 s1 (by decide)]
  have vS2 : memLoad32 M1 (F + 0xD0) = reg m s2 := by
    show memLoad32 (memStore32 (memStore32 (memStore32 (memStore32 M0 _ _) _ _) _ _) _ _) _ = _
    rw [memLoad32_store32_same, K1 s2 (by decide)]
  have cMF : ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn MF b code := fun b code hc hb hbl i hi => by
    have hx : Sep R 0x270 (b + BitVec.ofNat 32 i) 1 :=
      (data_code (by rw [hRn]; omega) hb hbl).subR (c := i) (l := 1) (by omega)
    rw [fF _ (hx.sub (c := 0) (l := 0x190) (by omega) |> fun h => by rwa [add_ofNat_zero] at h)
        (by rw [Fc]; exact Rx _ _ (by omega) _ hx)
        ((data_code hOw hb hbl).subR (c := i) (l := 1) (by omega)), MCR _ hx]
    exact hc i hi
  have cXF := cMF _ _ E.cX (by decide) (by decide)
  have u29 : St MF Q m29 0x62 (reg m29) := ⟨by rw [pc29], rfl, fun _ => rfl⟩
  have sp29' : reg m29 sp = F := sp29
  obtain ⟨m30, e30, u30⟩ := u29.lw cXF pt_at_62 (off' := 0x64) (by decide)
    (by rw [sp29']; exact aligned_add hFa4 (k := 0xDC) (by decide))
  rw [sp29', show memLoad32 MF (F + 0xDC) = reg m ra from (ldF 0xDC (by omega) (by omega)).trans vRa] at u30
  have K30 := u30.upd_ne u29.zero
  have u30' : St MF Q m30 0x64 (reg m30) := u30.self
  obtain ⟨m31, e31, u31⟩ := u30'.lw cXF pt_at_64 (off' := 0x66) (by decide)
    (by rw [K30 sp (by decide), sp29']; exact aligned_add hFa4 (k := 0xD8) (by decide))
  rw [K30 sp (by decide), sp29', show memLoad32 MF (F + 0xD8) = reg m s0 from (ldF 0xD8 (by omega) (by omega)).trans vS0]
    at u31
  have K31 := u31.upd_ne u30'.zero
  have u31' : St MF Q m31 0x66 (reg m31) := u31.self
  obtain ⟨m32, e32, u32⟩ := u31'.lw cXF pt_at_66 (off' := 0x68) (by decide)
    (by rw [K31 sp (by decide), K30 sp (by decide), sp29']; exact aligned_add hFa4 (k := 0xD4) (by decide))
  rw [K31 sp (by decide), K30 sp (by decide), sp29',
    show memLoad32 MF (F + 0xD4) = reg m s1 from (ldF 0xD4 (by omega) (by omega)).trans vS1] at u32
  have K32 := u32.upd_ne u31'.zero
  have u32' : St MF Q m32 0x68 (reg m32) := u32.self
  obtain ⟨m33, e33, u33⟩ := u32'.lw cXF pt_at_68 (off' := 0x6A) (by decide)
    (by rw [K32 sp (by decide), K31 sp (by decide), K30 sp (by decide), sp29']
        exact aligned_add hFa4 (k := 0xD0) (by decide))
  rw [K32 sp (by decide), K31 sp (by decide), K30 sp (by decide), sp29',
    show memLoad32 MF (F + 0xD0) = reg m s2 from (ldF 0xD0 (by omega) (by omega)).trans vS2] at u33
  have K33 := u33.upd_ne u32'.zero
  have u33' : St MF Q m33 0x6A (reg m33) := u33.self
  obtain ⟨m34, e34, u34⟩ := u33'.aluImm cXF pt_at_6a (off' := 0x6C) (by decide)
  have K34 := u34.upd_ne u33'.zero
  have u34' : St MF Q m34 0x6C (reg m34) := u34.self
  obtain ⟨m35, e35, pc35, mem35, regs35⟩ := u34'.jalr cXF pt_at_6c
  have ra34 : reg m34 ra = reg m ra := by
    rw [K34 ra (by decide), K33 ra (by decide), K32 ra (by decide), K31 ra (by decide), u30.upd_eq (by decide)]
  have sp34 : reg m34 sp = sp0 := by
    rw [u34.upd_eq (by decide), K33 sp (by decide), K32 sp (by decide), K31 sp (by decide), K30 sp (by decide), sp29']
    show sp0 + 0xFFFFFF20 + 0xE0 = sp0
    rw [BitVec.add_assoc]; exact BitVec.add_zero sp0
  have k29 : ∀ r, r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 →
      r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) →
      r ≠ (31 : Fin 32) → reg m29 r = reg m28 r := K29
  have k6 : ∀ r, r ≠ t0 → r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ a0 → r ≠ a1 → r ≠ a2 → reg m6 r = reg m1 r := K6
  have S1 : Steps m m12 := .cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 (c6.trans (.cons e7 (.cons e8 (c9.trans
    (.cons e10 (.cons e11 (.single e12)))))))))))
  have S2 : Steps m12 m24 := .cons e13 (c18.trans (.cons e19 (.cons e20 (.cons e21 (.cons e22 (.cons e23 c24))))))
  have S3 : Steps m24 m35 := .cons e25 (.cons e26 (.cons e27 (.cons e28 (c29.trans (.cons e30 (.cons e31 (.cons e32
    (.cons e33 (.cons e34 (.single e35))))))))))
  refine ⟨m35, S1.trans (S2.trans S3), ?_, ?_, fun r q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 => ?_,
    ?_, fun x hx hz => ?_⟩
  · rw [pc35, ra34, add_lit_zero, hra, hret]
  · rw [regs35, sp34]
  · rw [regs35]
    by_cases q1 : r = ra
    · subst q1; exact ra34
    by_cases q2 : r = sp
    · subst q2; rw [sp34, hsp]
    by_cases q8 : r = s0
    · subst q8; rw [K34 s0 (by decide), K33 s0 (by decide), K32 s0 (by decide), u31.upd_eq (by decide)]
    by_cases q9 : r = s1
    · subst q9; rw [K34 s1 (by decide), K33 s1 (by decide), u32.upd_eq (by decide)]
    by_cases q18 : r = s2
    · subst q18; rw [K34 s2 (by decide), u33.upd_eq (by decide)]
    rw [K34 r q2, K33 r q18, K32 r q9, K31 r q8, K30 r q1,
      k29 r q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31, r28 r q1, K26 r q10, K25 r q11,
      k24 r q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2, K1823 r q1 q10 q11 q12,
      K1218 r q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q2 q8 q9,
      K69 r q1 q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2, k6 r q5 q8 q9 q18 q10 q11 q12, K1 r q2]
  · rw [mem35]; exact out29
  · rw [mem35]
    show MF x = M0 x
    rw [fF x (by have h := hx.sub (c := 0) (l := 0x190) (by omega); rwa [add_ofNat_zero] at h)
      (by rw [Fc]; exact Rx _ _ (by omega) x hx) hz, MCR x hx]

end C3.RV32
