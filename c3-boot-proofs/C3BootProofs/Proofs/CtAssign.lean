import C3BootProofs.Proofs.MontMul12Main
import C3BootProofs.Proofs.MemcpyAny
import C3BootProofs.Image.Bootloader

/-!
# Constant-time assignment and `copy_from_slice`, as compiled

`<[u32] as CtAssign>::ct_assign` replaces each word of `dst` with the word of
`src` at its index when the choice is 1, and keeps it when the choice is 0,
through a mask, so it takes the same path either way. It stores the choice
byte on its stack and reads it back, as `black_box` would. `Uint<12>`'s
`ct_assign` tail-calls it with both lengths 12. `copy_from_slice_impl::<u8>`
tail-calls `memcpy` when the lengths match; otherwise it panics.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem sca_at_10 : fetchRel sliceCtAssignCode 0x10 = some (.branch .beq a1 a3 0x2A, 4) := by decide
theorem sca_at_3a : fetchRel sliceCtAssignCode 0x3A = some (.branch .bne a1 x0 0xFFFFFFE8, 2) := by decide
theorem sca_at_3c : fetchRel sliceCtAssignCode 0x3C = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem sca_at_3e : fetchRel sliceCtAssignCode 0x3E = some (.jalr x0 ra 0x0, 2) := by decide
theorem uca_at_0 : fetchRel uint12CtAssignCode 0x0 = some (.alu .add a4 x0 a2, 2) := by decide
theorem uca_at_2 : fetchRel uint12CtAssignCode 0x2 = some (.alu .add a2 x0 a1, 2) := by decide
theorem uca_at_4 : fetchRel uint12CtAssignCode 0x4 = some (.aluImm .add a1 x0 0xC, 2) := by decide
theorem uca_at_6 : fetchRel uint12CtAssignCode 0x6 = some (.aluImm .add a3 x0 0xC, 2) := by decide
theorem uca_at_8 : fetchRel uint12CtAssignCode 0x8 = some (.auipc (6 : Fin 32) 0xFFFFA000, 4) := by decide
theorem uca_at_c : fetchRel uint12CtAssignCode 0xC = some (.jalr x0 (6 : Fin 32) 0xFFFFFB5E, 4) := by decide
theorem cfs_at_0 : fetchRel copyFromSliceU8Code 0x0 = some (.alu .add a4 x0 a1, 2) := by decide
theorem cfs_at_2 : fetchRel copyFromSliceU8Code 0x2 = some (.branch .bne a1 a3 0x10, 4) := by decide
theorem cfs_at_6 : fetchRel copyFromSliceU8Code 0x6 = some (.alu .add a1 x0 a2, 2) := by decide
theorem cfs_at_8 : fetchRel copyFromSliceU8Code 0x8 = some (.alu .add a2 x0 a4, 2) := by decide
theorem cfs_at_a : fetchRel copyFromSliceU8Code 0xA = some (.auipc (6 : Fin 32) 0x7000, 4) := by decide
theorem cfs_at_e : fetchRel copyFromSliceU8Code 0xE = some (.jalr x0 (6 : Fin 32) 0x614, 4) := by decide
end

/-- The prologue, from 0 to the length check at 0x10: open the frame, store
the choice byte and read it back, and store both lengths. -/
def caPro : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFFE0, .sb sp a4 0x10, .aluImm .add a4 sp 0x10, .lbu a6 sp 0x10, .sw sp a1 8,
   .sw sp a3 0xC]

/-- The loop's body, from 0x22 to its branch at 0x3A. -/
def caBody : List BInstr :=
  [.lw a3 a2 0, .lw a5 a0 0, .aluImm .sltu a4 a6 1, .aluImm .add a4 a4 0xFFFFFFFF, .alu .xor a3 a3 a5,
   .alu .and a3 a3 a4, .alu .xor a3 a3 a5, .sw a0 a3 0, .aluImm .add a0 a0 4, .aluImm .add a2 a2 4,
   .aluImm .add a1 a1 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem caPro_end : blockEnd sliceCtAssignCode 0 caPro = some 0x10 := by decide
theorem caBody_end : blockEnd sliceCtAssignCode 0x22 caBody = some 0x3A := by decide
end

/-- The word the body stores, from the source word `S`, the destination
word `D`, and the choice `c`. -/
def caWord (S D c : Word) : Word :=
  aluEval .xor (aluEval .and (aluEval .xor S D) (aluEval .add (aluEval .sltu c 1) 0xFFFFFFFF)) D

theorem caWord_eq (S D c : Word) (hc : c = 0 ∨ c = 1) : caWord S D c = if c = 1 then S else D := by
  unfold caWord
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases hc with rfl | rfl
  · have hm : aluEval .add (aluEval .sltu 0 1) 0xFFFFFFFF = 0 := by decide
    rw [hm, ite_eq_right (by decide)]
    show (((S ^^^ D) &&& 0) ^^^ D).getLsbD i = D.getLsbD i
    have h0 : (0 : Word).getLsbD i = false := BitVec.getLsbD_zero
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_and, h0, Bool.and_false, Bool.false_xor]
  · have hm : aluEval .add (aluEval .sltu 1 1) 0xFFFFFFFF = 0 - 1 := by decide
    rw [hm, ite_eq_left rfl]
    show (((S ^^^ D) &&& (0 - 1)) ^^^ D).getLsbD i = S.getLsbD i
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_xor, ones_bit ⟨i, hi⟩, Bool.and_true]
    generalize S.getLsbD i = x
    generalize D.getLsbD i = y
    cases x <;> cases y <;> rfl

theorem ca_choice (c : Word) (hc : c = 0 ∨ c = 1) : (c.extractLsb' 0 8).zeroExtend 32 = c := by
  rcases hc with rfl | rfl <;> decide

theorem caBody_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock caBody (M, f)).1 = memStore32 M (f a0 + 0)
      (caWord (memLoad32 M (f a2 + 0)) (memLoad32 M (f a0 + 0)) (f a6)) ∧
    (runBlock caBody (M, f)).2 a0 = f a0 + 4 ∧ (runBlock caBody (M, f)).2 a2 = f a2 + 4 ∧
    (runBlock caBody (M, f)).2 a1 = aluEval .add (f a1) 0xFFFFFFFF ∧ (runBlock caBody (M, f)).2 a6 = f a6 ∧
    ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → (runBlock caBody (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, caBody]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q q0 q1 q2 q3 q4 q5 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]; rfl
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · by_cases hq : q.val = 0
    · have : q = 0 := Fin.ext hq
      subst this; simp [upd, hz]
    · simp [upd, hq, q0, q1, q2, q3, q4, q5]

/-- `dst` after the first `k` words of the assignment: word `i` is `src`'s
when `c = 1`, and `dst`'s own when `c = 0`. -/
def selWords (M : Word → BitVec 8) (dst src c : Word) : Nat → Word → BitVec 8
  | 0 => M
  | k + 1 => memStore32 (selWords M dst src c k) (dst + BitVec.ofNat 32 (4 * k))
      (if c = 1 then memLoad32 M (src + BitVec.ofNat 32 (4 * k)) else memLoad32 M (dst + BitVec.ofNat 32 (4 * k)))

theorem selWords_outside {M : Word → BitVec 8} {dst src c x : Word} :
    ∀ k, Sep dst (4 * k) x 1 → selWords M dst src c k x = M x
  | 0, _ => rfl
  | k + 1, h => by
    simp only [selWords]
    rw [memStore32_get_sep (h.sub (c := 4 * k) (l := 4) (by omega)),
      selWords_outside k (h.sub (c := 0) (l := 4 * k) (by omega) |> fun h' => by rwa [add_ofNat_zero] at h')]

theorem selWords_load_sep {M : Word → BitVec 8} {dst src c a : Word} {k : Nat} (h : Sep dst (4 * k) a 4) :
    memLoad32 (selWords M dst src c k) a = memLoad32 M a :=
  memLoad32_congr fun j hj => selWords_outside k (h.subR (c := j) (l := 1) (by omega))

theorem selWords_load {M : Word → BitVec 8} {dst src c : Word} :
    ∀ k i, i < k → dst.toNat + 4 * k ≤ 2 ^ 32 →
      memLoad32 (selWords M dst src c k) (dst + BitVec.ofNat 32 (4 * i)) =
        if c = 1 then memLoad32 M (src + BitVec.ofNat 32 (4 * i)) else memLoad32 M (dst + BitVec.ofNat 32 (4 * i))
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, i, hi, hw => by
    simp only [selWords]
    by_cases h : i = k
    · subst h; exact memLoad32_store32_same _ _ _
    · rw [memLoad32_store32_sep (sep_offsets dst (by omega) (by omega) (by omega))]
      exact selWords_load k i (by omega) (by omega)

theorem CodeIn.selWords {M : Word → BitVec 8} {dst src c base : Word} {code : List Nat} {k : Nat}
    (hc : CodeIn M base code) (hs : Sep dst (4 * k) base code.length) :
    CodeIn (C3.RV32.selWords M dst src c k) base code := fun i hi => by
  rw [selWords_outside k (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi

theorem ca_cnt_dec {n j : Nat} (hj : j < n) :
    aluEval .add (BitVec.ofNat 32 (n - j)) 0xFFFFFFFF = BitVec.ofNat 32 (n - (j + 1)) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 (n - j) + 0xFFFFFFFF).toNat = _
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 from rfl]
  omega

theorem ca_cnt_ne {n j : Nat} (hn : n < 2 ^ 32) (hj : j ≤ n) :
    branchTaken .bne (BitVec.ofNat 32 (n - j)) 0 = decide (j < n) := by
  show (BitVec.ofNat 32 (n - j) != 0) = _
  by_cases h : j < n
  · rw [decide_eq_true h]
    refine bne_iff_ne.mpr fun e => ?_
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    change _ = 0 at this; omega
  · rw [decide_eq_false h, show n - j = 0 by omega]; rfl

/-- **The loop of `<[u32] as CtAssign>::ct_assign`**, from its check at
0x3A with `j` words done. -/
theorem ca_loop {B dst src c : Word} {M0 : Word → BitVec 8} {n : Nat} (hn : n < 2 ^ 32)
    (hdst : dst.toNat % 4 = 0) (hsrc : src.toNat % 4 = 0) (hdw : dst.toNat + 4 * n ≤ 2 ^ 32)
    (sDS : Sep dst (4 * n) src (4 * n)) (sDC : Sep dst (4 * n) B sliceCtAssignCode.length) (hc : c = 0 ∨ c = 1)
    (hcode : CodeIn M0 B sliceCtAssignCode) :
    ∀ k j, j + k = n → ∀ {s : Machine}, St (selWords M0 dst src c j) B s 0x3A (reg s) →
      reg s a1 = BitVec.ofNat 32 (n - j) → reg s a0 = dst + BitVec.ofNat 32 (4 * j) →
      reg s a2 = src + BitVec.ofNat 32 (4 * j) → reg s a6 = c →
      ∃ s', Steps s s' ∧ St (selWords M0 dst src c n) B s' 0x3C (reg s') ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → reg s' q = reg s q := by
  intro k
  induction k with
  | zero =>
    intro j hj s st r1 _ _ _
    have hjn : j = n := by omega
    subst hjn
    obtain ⟨s1, d1, u1⟩ := st.notTaken (CodeIn.selWords hcode sDC) 0x3C sca_at_3a (by decide)
      (by rw [r1, st.zero]; exact (ca_cnt_ne hn (Nat.le_refl _)).trans (decide_eq_false (Nat.lt_irrefl _)))
    exact ⟨s1, .single d1, u1.self, fun q _ _ _ _ _ _ => u1.regs q⟩
  | succ k ih =>
    intro j hj s st r1 r0 r2 r6
    have hjl : j < n := by omega
    have hc0 := CodeIn.selWords (src := src) (c := c) (k := j) hcode (sDC.sub (c := 0) (l := 4 * j) (by omega) |>
      fun h => by rwa [add_ofNat_zero] at h)
    obtain ⟨s1, d1, u1⟩ := st.taken hc0 0x22 sca_at_3a (by decide)
      (by rw [r1, st.zero]; exact (ca_cnt_ne hn (Nat.le_of_lt hjl)).trans (decide_eq_true hjl))
    have hz := u1.zero
    have sD : Sep (dst + BitVec.ofNat 32 (4 * j)) 4 B sliceCtAssignCode.length := sDC.sub (by omega)
    obtain ⟨s2, c2, u2⟩ := St.block caBody u1 hc0 caBody_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, caBody, upd, ↓reduceIte, true_and, and_true]
      rw [r2, r0, add_lit_zero, add_lit_zero]
      exact ⟨aligned_add hsrc (by omega), aligned_add hdst (by omega), aligned_add hdst (by omega), sD⟩)
    obtain ⟨em, e0, e2, e1, e6, fr⟩ := caBody_run (M := selWords M0 dst src c j) (f := reg s) hz
    have eS : memLoad32 (selWords M0 dst src c j) (src + BitVec.ofNat 32 (4 * j)) =
        memLoad32 M0 (src + BitVec.ofNat 32 (4 * j)) :=
      selWords_load_sep ((sDS.subR (c := 4 * j) (l := 4) (by omega)).sub (c := 0) (l := 4 * j) (by omega) |>
        fun h => by rwa [add_ofNat_zero] at h)
    have eD : memLoad32 (selWords M0 dst src c j) (dst + BitVec.ofNat 32 (4 * j)) =
        memLoad32 M0 (dst + BitVec.ofNat 32 (4 * j)) :=
      selWords_load_sep (by
        have := sep_offsets dst (c := 0) (n := 4 * j) (d := 4 * j) (k := 4) (.inl (by omega)) (by omega) (by omega)
        rwa [add_ofNat_zero] at this)
    have hmem : (runBlock caBody (selWords M0 dst src c j, reg s)).1 = selWords M0 dst src c (j + 1) := by
      rw [em, r0, r2, r6, add_lit_zero, add_lit_zero, eS, eD, caWord_eq _ _ _ hc]; rfl
    have u2' := u2.self
    rw [hmem] at u2'
    have g : ∀ q, reg s2 q = (runBlock caBody (selWords M0 dst src c j, reg s)).2 q := u2.regs
    obtain ⟨s', c', u', k'⟩ := ih (j + 1) (by omega) u2' (by rw [g, e1, r1, ca_cnt_dec hjl])
      (by rw [g, e0, r0, ptr4]) (by rw [g, e2, r2, ptr4]) (by rw [g, e6, r6])
    exact ⟨s', .cons d1 (c2.trans c'), u', fun q h0 h1 h2 h3 h4 h5 => by
      rw [k' q h0 h1 h2 h3 h4 h5, g, fr q h0 h1 h2 h3 h4 h5]⟩

theorem caPro_run {M : Word → BitVec 8} {f : Fin 32 → Word} (hz : f 0 = 0) :
    (runBlock caPro (M, f)).1 = memStore32 (memStore32 (memStore8 M (aluEval .add (f sp) 0xFFFFFFE0 + 0x10)
      ((f a4).extractLsb' 0 8)) (aluEval .add (f sp) 0xFFFFFFE0 + 8) (f a1)) (aluEval .add (f sp) 0xFFFFFFE0 + 0xC)
      (f a3) ∧
    (runBlock caPro (M, f)).2 sp = aluEval .add (f sp) 0xFFFFFFE0 ∧
    (runBlock caPro (M, f)).2 a6 = ((f a4).extractLsb' 0 8).zeroExtend 32 ∧
    ∀ q, q ≠ sp → q ≠ a4 → q ≠ a6 → (runBlock caPro (M, f)).2 q = f q := by
  simp only [runBlock, BInstr.run, caPro]
  refine ⟨?_, ?_, ?_, fun q q2 q14 q16 => ?_⟩
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]
  · simp +decide only [upd, ↓reduceIte]; rw [memStore8_same]
  · by_cases hq : q.val = 0
    · have : q = 0 := Fin.ext hq
      subst this; simp [upd, hz]
    · simp [upd, hq, q2, q14, q16]

set_option maxRecDepth 20000 in
/-- **The compiled `<[u32] as CtAssign>::ct_assign`**, called with `dst`
and `src` of `n` words each and a choice of 0 or 1: word `i` of `dst`
becomes `src`'s when the choice is 1 and stays when it is 0. It returns
with `sp` restored, changes only `a0` to `a6` among the registers, and
writes no memory outside `dst` and the 0x20 bytes of stack below `sp`. The
lengths must match; otherwise it panics. -/
theorem sliceCtAssign_correct (m : Machine) {B sp0 dst src c retAddr : Word} {n : Nat}
    (hcode : CodeIn m.mem B sliceCtAssignCode) (hpc : m.pc = B) (hsp : reg m sp = sp0) (hsa : sp0.toNat % 4 = 0)
    (hS : 0x20 ≤ sp0.toNat) (ha0 : reg m a0 = dst) (ha1 : reg m a1 = BitVec.ofNat 32 n) (ha2 : reg m a2 = src)
    (ha3 : reg m a3 = BitVec.ofNat 32 n) (ha4 : reg m a4 = c) (hc : c = 0 ∨ c = 1) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hdst : dst.toNat % 4 = 0) (hsrc : src.toNat % 4 = 0)
    (hdw : dst.toNat + 4 * n ≤ 2 ^ 32) (sFC : Sep (sp0 + 0xFFFFFFE0) 0x20 B sliceCtAssignCode.length)
    (sDC : Sep dst (4 * n) B sliceCtAssignCode.length) (sDF : Sep dst (4 * n) (sp0 + 0xFFFFFFE0) 0x20)
    (sSF : Sep src (4 * n) (sp0 + 0xFFFFFFE0) 0x20) (sDS : Sep dst (4 * n) src (4 * n)) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ i, i < n → memLoad32 m'.mem (dst + BitVec.ofNat 32 (4 * i)) =
        if c = 1 then memLoad32 m.mem (src + BitVec.ofNat 32 (4 * i)) else memLoad32 m.mem (dst + BitVec.ofNat 32 (4 * i))) ∧
      (∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 → Sep dst (4 * n) x 1 → m'.mem x = m.mem x) ∧
      ∀ q, q.val ∉ [10, 11, 12, 13, 14, 15, 16] → reg m' q = reg m q := by
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFE0 = F := ⟨_, rfl⟩
  rw [hF] at sFC sDF sSF ⊢
  have hFw : F.toNat + 0x20 = sp0.toNat := by
    rw [← hF, BitVec.toNat_add, show (0xFFFFFFE0 : Word).toNat = 4294967264 from rfl]; have := sp0.isLt; omega
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add hsa (k := 0xFFFFFFE0) (by decide)
  have hn : n < 2 ^ 32 := by omega
  have s0 : St m.mem B m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have eF : aluEval .add (reg m sp) 0xFFFFFFE0 = F := by rw [hsp, ← hF]; rfl
  obtain ⟨s1, c1, u1⟩ := St.block caPro s0 hcode caPro_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, caPro, upd, ↓reduceIte, true_and, and_true]
    rw [eF]
    exact ⟨sFC.sub (by decide), ⟨aligned_add hFa (k := 8) (by decide), sFC.sub (by decide)⟩,
      aligned_add hFa (k := 0xC) (by decide), sFC.sub (by decide)⟩)
  obtain ⟨em, esp, e6, fr⟩ := caPro_run (M := m.mem) (f := reg m) hz
  rw [eF] at em esp
  rw [ha4, ca_choice c hc] at e6
  obtain ⟨Mp, hMp⟩ : ∃ Mp, memStore32 (memStore32 (memStore8 m.mem (F + 0x10) ((reg m a4).extractLsb' 0 8))
      (F + 8) (reg m a1)) (F + 0xC) (reg m a3) = Mp := ⟨_, rfl⟩
  rw [hMp] at em
  have u1' := u1.self
  rw [em] at u1'
  have frP : ∀ x, Sep F 0x20 x 1 → Mp x = m.mem x := fun x hx => by
    rw [← hMp, memStore32_get_sep (a := F + 0xC) (hx.sub (c := 0xC) (l := 4) (by decide)),
      memStore32_get_sep (a := F + 8) (hx.sub (c := 8) (l := 4) (by decide)),
      memStore8_ne fun e => hx.point (i := 0x10) (j := 0) (by decide) (by decide) (by rw [add_ofNat_zero]; exact e.symm)]
  have hcP : CodeIn Mp B sliceCtAssignCode := fun i hi => by
    rw [frP _ (sFC.subR (c := i) (l := 1) (by omega))]; exact hcode i hi
  have g1 : ∀ q, reg s1 q = (runBlock caPro (m.mem, reg m)).2 q := u1.regs
  obtain ⟨s2, d2, u2⟩ := u1'.taken hcP 0x3A sca_at_10 (by decide) (by
    rw [g1, g1, fr _ (by decide) (by decide) (by decide), fr _ (by decide) (by decide) (by decide), ha1, ha3]
    exact decide_eq_true rfl)
  have g2 : ∀ q, reg s2 q = reg s1 q := u2.regs
  obtain ⟨s3, c3, u3, k3⟩ := ca_loop (M0 := Mp) (src := src) (c := c) hn hdst hsrc hdw sDS sDC hc hcP n 0 (by omega)
    u2.self (by rw [g2, g1, fr _ (by decide) (by decide) (by decide), ha1, Nat.sub_zero])
    (by rw [g2, g1, fr _ (by decide) (by decide) (by decide), ha0]; exact (add_ofNat_zero _).symm)
    (by rw [g2, g1, fr _ (by decide) (by decide) (by decide), ha2]; exact (add_ofNat_zero _).symm)
    (by rw [g2, g1, e6])
  have hc3 := CodeIn.selWords (src := src) (c := c) (k := n) hcP sDC
  obtain ⟨s4, d4, u4⟩ := u3.aluImm hc3 sca_at_3c (off' := 0x3E) (by decide)
  obtain ⟨s5, d5, pc5, mem5, regs5⟩ := u4.jalr hc3 sca_at_3e
  have k3' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ sp → reg s3 q = reg m q :=
    fun q h0 h1 h2 h3 h4 h5 h6 hs => by rw [k3 q h0 h1 h2 h3 h4 h5, g2, g1, fr q hs h4 h6]
  have sp3 : reg s3 sp = F := by
    rw [k3 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g2, g1, esp]
  have eL : ∀ a, Sep F 0x20 a 4 → memLoad32 Mp a = memLoad32 m.mem a := fun a h =>
    memLoad32_congr fun j hj => frP _ (h.subR (c := j) (l := 1) (by omega))
  refine ⟨s5, c1.trans (.cons d2 (c3.trans (.cons d4 (.single d5)))), ?_, ?_, fun i hi => ?_, fun x hx hd => ?_,
    fun q hq => ?_⟩
  · rw [pc5]; simp +decide only [upd, ↓reduceIte]
    rw [k3' ra (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hra,
      add_lit_zero, hret]
  · rw [regs5]; simp +decide only [upd, ↓reduceIte]
    show reg s3 sp + 0x20 = sp0
    rw [sp3, ← hF, BitVec.add_assoc]; exact BitVec.add_zero _
  · rw [mem5, selWords_load n i hi hdw, eL _ (sSF.symm.subR (by omega) |>.symm |> fun h => h.symm |> fun h => h),
      eL _ (sDF.symm.subR (by omega))]
  · rw [mem5, selWords_outside n hd, frP x hx]
  · have h : ∀ r : Fin 32, r.val ∈ [10, 11, 12, 13, 14, 15, 16] → q ≠ r := fun r hr e => by subst e; exact hq hr
    rw [regs5]
    by_cases hs : q = sp
    · subst hs; simp +decide only [upd, ↓reduceIte]
      show reg s3 sp + 0x20 = reg m sp
      rw [sp3, ← hF, BitVec.add_assoc, hsp]; exact BitVec.add_zero _
    · rw [updz u3.zero hs]
      exact k3' q (h a0 (by decide)) (h a1 (by decide)) (h a2 (by decide)) (h a3 (by decide)) (h a4 (by decide))
        (h a5 (by decide)) (h a6 (by decide)) hs

set_option maxRecDepth 20000 in
/-- **The compiled `<Uint<12> as CtAssign>::ct_assign`**: it tail-calls the
slice version with both lengths 12, so `self` becomes `other` when the
choice is 1 and stays when it is 0. -/
theorem uint12CtAssign_correct (m : Machine) {W sp0 dst src c retAddr : Word} (hW : W.toNat % 2 = 0)
    (hcw : CodeIn m.mem W uint12CtAssignCode) (hcode : CodeIn m.mem (W + 0xFFFF9B66) sliceCtAssignCode)
    (hpc : m.pc = W) (hsp : reg m sp = sp0) (hsa : sp0.toNat % 4 = 0) (hS : 0x20 ≤ sp0.toNat)
    (ha0 : reg m a0 = dst) (ha1 : reg m a1 = src) (ha2 : reg m a2 = c) (hc : c = 0 ∨ c = 1)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hdst : dst.toNat % 4 = 0)
    (hsrc : src.toNat % 4 = 0) (hdw : dst.toNat + 48 ≤ 2 ^ 32)
    (sFC : Sep (sp0 + 0xFFFFFFE0) 0x20 (W + 0xFFFF9B66) sliceCtAssignCode.length)
    (sDC : Sep dst 48 (W + 0xFFFF9B66) sliceCtAssignCode.length) (sDF : Sep dst 48 (sp0 + 0xFFFFFFE0) 0x20)
    (sSF : Sep src 48 (sp0 + 0xFFFFFFE0) 0x20) (sDS : Sep dst 48 src 48) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ i, i < 12 → memLoad32 m'.mem (dst + BitVec.ofNat 32 (4 * i)) =
        if c = 1 then memLoad32 m.mem (src + BitVec.ofNat 32 (4 * i)) else memLoad32 m.mem (dst + BitVec.ofNat 32 (4 * i))) ∧
      (∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 → Sep dst 48 x 1 → m'.mem x = m.mem x) ∧
      ∀ q, q.val ∉ [6, 10, 11, 12, 13, 14, 15, 16] → reg m' q = reg m q := by
  have s0 : St m.mem W m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.alu hcw uca_at_0 (off' := 2) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.self.alu hcw uca_at_2 (off' := 4) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.aluImm hcw uca_at_4 (off' := 6) (by decide)
  obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hcw uca_at_6 (off' := 8) (by decide)
  obtain ⟨n5, d5, u5⟩ := u4.self.auipc hcw uca_at_8 (off' := 0xC) (by decide)
  obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.self.jalr hcw uca_at_c
  have k5 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ t1 → reg n5 q = reg m q := fun q h1 h2 h3 h4 ht => by
    rw [u5.regs, updz u4.self.zero ht, u4.regs, updz u3.self.zero h3, u3.regs, updz u2.self.zero h1, u2.regs,
      updz u1.self.zero h2, u1.regs, updz hz h4]
  have e1 : reg n5 a1 = BitVec.ofNat 32 12 := by
    rw [u5.regs, updz u4.self.zero (by decide), u4.regs, updz u3.self.zero (by decide), u3.regs]
    simp +decide only [upd, ↓reduceIte]; rw [u2.self.zero]; rfl
  have e3 : reg n5 a3 = BitVec.ofNat 32 12 := by
    rw [u5.regs, updz u4.self.zero (by decide), u4.regs]
    simp +decide only [upd, ↓reduceIte]; rw [u3.self.zero]; rfl
  have e2 : reg n5 a2 = src := by
    rw [u5.regs, updz u4.self.zero (by decide), u4.regs, updz u3.self.zero (by decide), u3.regs,
      updz u2.self.zero (by decide), u2.regs]
    simp +decide only [upd, ↓reduceIte]; rw [u1.self.zero, u1.regs, updz hz (by decide), ha1]; exact BitVec.zero_add _
  have e4 : reg n5 a4 = c := by
    rw [u5.regs, updz u4.self.zero (by decide), u4.regs, updz u3.self.zero (by decide), u3.regs,
      updz u2.self.zero (by decide), u2.regs, updz u1.self.zero (by decide), u1.regs]
    simp +decide only [upd, ↓reduceIte]; rw [hz, ha2]; exact BitVec.zero_add _
  have et : reg n5 t1 = W + BitVec.ofNat 32 8 + 0xFFFFA000 := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
  have pcA : n6.pc = W + 0xFFFF9B66 := by
    rw [pc6, et, BitVec.add_assoc, BitVec.add_assoc]
    exact even_clear _ (even_at W hW 0xFFFF9B66 (by decide))
  obtain ⟨m', c', pc', sp', val', fr', k'⟩ := sliceCtAssign_correct n6 (n := 12) (by rw [mem6]; exact hcode) pcA
    (by rw [regs6, k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), hsp]) hsa hS
    (by rw [regs6, k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), ha0]) (by rw [regs6, e1])
    (by rw [regs6, e2]) (by rw [regs6, e3]) (by rw [regs6, e4]) hc
    (by rw [regs6, k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), hra]) hret hdst hsrc hdw
    sFC sDC sDF sSF sDS
  rw [mem6] at val' fr'
  refine ⟨m', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 c'))))), pc', sp', val', fr', fun q hq => ?_⟩
  have h : ∀ r : Fin 32, r.val ∈ [6, 10, 11, 12, 13, 14, 15, 16] → q ≠ r := fun r hr e => by subst e; exact hq hr
  rw [k' q (fun hm => hq (List.mem_cons_of_mem _ hm)), regs6, k5 q (h a1 (by decide)) (h a2 (by decide)) (h a3 (by decide))
    (h a4 (by decide)) (h t1 (by decide))]

/-- **The compiled `copy_from_slice_impl::<u8>`**, called with `dst` and
`src` of the same length `n`: it tail-calls `memcpy`, so `dst` holds `src`'s
bytes. Its frame is `memcpy`'s. Different lengths panic. -/
theorem copyFromSliceU8_correct (m : Machine) {W retAddr dst src : Word} {n : Nat} (hW : W.toNat % 2 = 0)
    (hcw : CodeIn m.mem W copyFromSliceU8Code) (hst : CodeIn m.mem (W + 0x761E) memcpyStubCode) (hpc : m.pc = W)
    (ha0 : reg m a0 = dst) (ha1 : reg m a1 = BitVec.ofNat 32 n) (ha2 : reg m a2 = src)
    (ha3 : reg m a3 = BitVec.ofNat 32 n) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (E : McEnv m.mem (W + 0x761E + 8) dst src (reg m sp + 0xFFFFFFF0) n) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧ reg m' a0 = dst ∧
      (∀ x, Sep (reg m sp + 0xFFFFFFF0) 16 x 1 → m'.mem x = copyBytes m.mem dst src n x) ∧
      ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
        r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp → reg m' r = reg m r := by
  have s0 : St m.mem W m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.alu hcw cfs_at_0 (off' := 2) (by decide)
  obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hcw 6 cfs_at_2 (by decide) (by
    rw [u1.regs, updz hz (by decide), u1.regs, updz hz (by decide), ha1, ha3]; exact bne_self_eq_false _)
  obtain ⟨n3, d3, u3⟩ := u2.self.alu hcw cfs_at_6 (off' := 8) (by decide)
  obtain ⟨n4, d4, u4⟩ := u3.self.alu hcw cfs_at_8 (off' := 0xA) (by decide)
  obtain ⟨n5, d5, u5⟩ := u4.self.auipc hcw cfs_at_a (off' := 0xE) (by decide)
  obtain ⟨n6, d6, pc6, mem6, regs6⟩ := u5.self.jalr hcw cfs_at_e
  have g2 : ∀ q, reg n2 q = reg n1 q := u2.regs
  have k5 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a4 → q ≠ t1 → reg n5 q = reg m q := fun q h1 h2 h4 ht => by
    rw [u5.regs, updz u4.self.zero ht, u4.regs, updz u3.self.zero h2, u3.regs, updz u2.self.zero h1, g2, u1.regs,
      updz hz h4]
  have e1 : reg n5 a1 = src := by
    rw [u5.regs, updz u4.self.zero (by decide), u4.regs, updz u3.self.zero (by decide), u3.regs]
    simp +decide only [upd, ↓reduceIte]; rw [u2.self.zero, g2, u1.regs, updz hz (by decide), ha2]
    exact BitVec.zero_add _
  have e2 : reg n5 a2 = BitVec.ofNat 32 n := by
    rw [u5.regs, updz u4.self.zero (by decide), u4.regs]
    simp +decide only [upd, ↓reduceIte]; rw [u3.self.zero, u3.regs, updz u2.self.zero (by decide), g2, u1.regs]
    simp +decide only [upd, ↓reduceIte]; rw [hz, ha1]
    have h1 : (0 : Word) + BitVec.ofNat 32 n = BitVec.ofNat 32 n := BitVec.zero_add _
    show (0 : Word) + ((0 : Word) + BitVec.ofNat 32 n) = BitVec.ofNat 32 n
    rw [h1]; exact BitVec.zero_add _
  have et : reg n5 t1 = W + BitVec.ofNat 32 0xA + 0x7000 := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
  have pcA : n6.pc = W + 0x761E := by
    rw [pc6, et, BitVec.add_assoc, BitVec.add_assoc]
    exact even_clear _ (even_at W hW 0x761E (by decide))
  have sp6 : reg n6 sp = reg m sp := by rw [regs6, k5 _ (by decide) (by decide) (by decide) (by decide)]
  obtain ⟨m', c', pc', sp', a0', mem', k'⟩ := memcpy_correct n6 (W + 0x761E) retAddr dst src n
    (fun i hi => by show n6.mem _ = _; rw [mem6]; exact hst i hi) (even_at W hW 0x761E (by decide)) pcA
    (by rw [regs6, k5 _ (by decide) (by decide) (by decide) (by decide), ha0]) (by rw [regs6, e1])
    (by rw [regs6, e2]) (by rw [regs6, k5 _ (by decide) (by decide) (by decide) (by decide), hra]) hret
    (by rw [mem6, sp6]; exact E)
  rw [mem6, sp6] at mem'
  refine ⟨m', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 c'))))), pc', by rw [sp', sp6], a0', mem',
    fun r q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 => ?_⟩
  rw [k' r q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14, regs6, k5 r q1 q2 q4 q9]

end C3.RV32
