import C3BootProofs.Proofs.ImageLoop

/-!
# `image::parse`: a segment's checks

From offset 0x2CA, the loop checks the segment `read_segment` read, as
`checkSegW` does, stores it in the array, and goes back to 0x188.

The kind sits in the low byte of `s10`, whose other bytes come from the
frame word at `G`; `s10_lo`, `s10_byte`, and `s10_idx` read the kind back
out. The address is split across `s7` and the frame word at `G + 0x10`, and
`a_rebuild` puts it back together.
-/

namespace C3.RV32

open C3.ImageV0

set_option maxRecDepth 20000

theorem s10_lo (X : Word) (k : BitVec 8) :
    aluEval .and (aluEval .or (aluEval .and X 0xFFFFFF00) (k.zeroExtend 32)) 0xFF = k.zeroExtend 32 := by
  show ((X &&& 0xFFFFFF00) ||| k.zeroExtend 32) &&& 0xFF = _
  rw [BitVec.and_or_distrib_right, BitVec.and_assoc, show (0xFFFFFF00 : Word) &&& 0xFF = 0#32 by decide,
    BitVec.and_zero, BitVec.zero_or]
  revert k; decide

theorem s10_byte (X : Word) (k : BitVec 8) :
    (aluEval .or (aluEval .and X 0xFFFFFF00) (k.zeroExtend 32)).extractLsb' 0 8 = k := by
  rw [← lo8_and, show aluEval .or (aluEval .and X 0xFFFFFF00) (k.zeroExtend 32) &&& 0xFF =
    aluEval .and (aluEval .or (aluEval .and X 0xFFFFFF00) (k.zeroExtend 32)) 0xFF from rfl, s10_lo,
    zext_lsb8]

theorem s10_idx (X : Word) (k : BitVec 8) :
    aluEval .srl (aluEval .sll (aluEval .or (aluEval .and X 0xFFFFFF00) (k.zeroExtend 32)) 0x18) 0x16 =
      k.zeroExtend 32 <<< 2 := by
  show (((X &&& 0xFFFFFF00) ||| k.zeroExtend 32) <<< ((0x18 : Word).toNat % 32)) >>>
    ((0x16 : Word).toNat % 32) = _
  rw [show (0x18 : Word).toNat % 32 = 24 from rfl, show (0x16 : Word).toNat % 32 = 22 from rfl,
    BitVec.shiftLeft_or_distrib, BitVec.shiftLeft_and_distrib,
    show (0xFFFFFF00 : Word) <<< 24 = 0#32 by decide, BitVec.and_zero, BitVec.zero_or]
  revert k; decide

theorem a_rebuild (a : Word) :
    aluEval .or (aluEval .sll (aluEval .srl a 8) 8) (aluEval .and a 0xFF) = a := by
  show ((a >>> ((8 : Word).toNat % 32)) <<< ((8 : Word).toNat % 32)) ||| (a &&& 0xFF) = a
  rw [show (8 : Word).toNat % 32 = 8 from rfl]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hff : ∀ i, i < 32 → (0xFF : Word).getLsbD i = decide (i < 8) := by decide
  rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and,
    hff i hi]
  by_cases h : i < 8
  · simp [h, hi]
  · have e : 8 + (i - 8) = i := by omega
    simp [h, hi, e]

theorem tbl_word (M : Word → BitVec 8) (base : Word) (code : List Nat) (hc : CodeIn M base code)
    (i : Nat) (hi : i + 4 ≤ code.length) :
    memLoad32 M (base + BitVec.ofNat 32 i) =
      byteAt code (i + 3) ++ byteAt code (i + 2) ++ byteAt code (i + 1) ++ byteAt code i := by
  have h : ∀ j, j < 4 → M (base + BitVec.ofNat 32 i + BitVec.ofNat 32 j) = byteAt code (i + j) :=
    fun j hj => by rw [add_ofNat_assoc]; exact hc _ (by omega)
  unfold memLoad32
  rw [show M (base + BitVec.ofNat 32 i + 3) = byteAt code (i + 3) from h 3 (by omega),
    show M (base + BitVec.ofNat 32 i + 2) = byteAt code (i + 2) from h 2 (by omega),
    show M (base + BitVec.ofNat 32 i + 1) = byteAt code (i + 1) from h 1 (by omega),
    show M (base + BitVec.ofNat 32 i) = byteAt code i from hc i (by omega)]

theorem kind4 : ∀ k : BitVec 8, (3 : BitVec 8).ult k = false → k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
  decide

/-- The region table entry the loop reads for kind `k`: the region's end. -/
theorem tbl_hi (M : Word → BitVec 8) (hc : CodeIn M 0x3FCC5240 regionEndsData) (k : BitVec 8)
    (hk : (3 : BitVec 8).ult k = false) :
    memLoad32 M (aluEval .add (aluEval .add 0x3FCC5000 0x240) (k.zeroExtend 32 <<< 2) + 0) = regionHi k := by
  rcases kind4 k hk with rfl | rfl | rfl | rfl
  · rw [show aluEval .add (aluEval .add 0x3FCC5000 0x240) ((0 : BitVec 8).zeroExtend 32 <<< 2) + 0 =
      (0x3FCC5240 : Word) + BitVec.ofNat 32 0 from rfl, tbl_word M _ _ hc 0 (by decide)]; decide
  · rw [show aluEval .add (aluEval .add 0x3FCC5000 0x240) ((1 : BitVec 8).zeroExtend 32 <<< 2) + 0 =
      (0x3FCC5240 : Word) + BitVec.ofNat 32 4 from rfl, tbl_word M _ _ hc 4 (by decide)]; decide
  · rw [show aluEval .add (aluEval .add 0x3FCC5000 0x240) ((2 : BitVec 8).zeroExtend 32 <<< 2) + 0 =
      (0x3FCC5240 : Word) + BitVec.ofNat 32 8 from rfl, tbl_word M _ _ hc 8 (by decide)]; decide
  · rw [show aluEval .add (aluEval .add 0x3FCC5000 0x240) ((3 : BitVec 8).zeroExtend 32 <<< 2) + 0 =
      (0x3FCC5240 : Word) + BitVec.ofNat 32 12 from rfl, tbl_word M _ _ hc 12 (by decide)]; decide

/-- The region table entry for kind `k`: the region's start. -/
theorem tbl_lo (M : Word → BitVec 8) (hc : CodeIn M 0x3FCC5250 regionStartsData) (k : BitVec 8)
    (hk : (3 : BitVec 8).ult k = false) :
    memLoad32 M (aluEval .add (k.zeroExtend 32 <<< 2) (aluEval .add 0x3FCC5000 0x250) + 0) = regionLo k := by
  rcases kind4 k hk with rfl | rfl | rfl | rfl
  · rw [show aluEval .add ((0 : BitVec 8).zeroExtend 32 <<< 2) (aluEval .add 0x3FCC5000 0x250) + 0 =
      (0x3FCC5250 : Word) + BitVec.ofNat 32 0 from rfl, tbl_word M _ _ hc 0 (by decide)]; decide
  · rw [show aluEval .add ((1 : BitVec 8).zeroExtend 32 <<< 2) (aluEval .add 0x3FCC5000 0x250) + 0 =
      (0x3FCC5250 : Word) + BitVec.ofNat 32 4 from rfl, tbl_word M _ _ hc 4 (by decide)]; decide
  · rw [show aluEval .add ((2 : BitVec 8).zeroExtend 32 <<< 2) (aluEval .add 0x3FCC5000 0x250) + 0 =
      (0x3FCC5250 : Word) + BitVec.ofNat 32 8 from rfl, tbl_word M _ _ hc 8 (by decide)]; decide
  · rw [show aluEval .add ((3 : BitVec 8).zeroExtend 32 <<< 2) (aluEval .add 0x3FCC5000 0x250) + 0 =
      (0x3FCC5250 : Word) + BitVec.ofNat 32 12 from rfl, tbl_word M _ _ hc 12 (by decide)]; decide

/-- The four stores that put segment `s` in slot `i`. -/
def pushMem (M : Word → BitVec 8) (G : Word) (i : Nat) (s : SegW) (vk : Word) : Word → BitVec 8 :=
  memStore32 (memStore32 (memStore32 (memStore32 M (G + BitVec.ofNat 32 (0x24 + 16 * i)) s.addr)
    (G + BitVec.ofNat 32 (0x28 + 16 * i)) s.off) (G + BitVec.ofNat 32 (0x2C + 16 * i)) s.len)
    (G + BitVec.ofNat 32 (0x30 + 16 * i)) vk

theorem pushMem_ld (M : Word → BitVec 8) (G : Word) (i : Nat) (hi : i < 16) (s : SegW) (vk : Word)
    (d : Nat) (hd : d + 4 ≤ 0x160) (hd4 : d % 4 = 0) :
    memLoad32 (pushMem M G i s vk) (G + BitVec.ofNat 32 d) =
      if 0x30 + 16 * i = d then vk else if 0x2C + 16 * i = d then s.len else
      if 0x28 + 16 * i = d then s.off else if 0x24 + 16 * i = d then s.addr else
      memLoad32 M (G + BitVec.ofNat 32 d) := by
  unfold pushMem
  rw [ld_st _ G _ d _ (by omega) hd (by omega) hd4, ld_st _ G _ d _ (by omega) hd (by omega) hd4,
    ld_st _ G _ d _ (by omega) hd (by omega) hd4, ld_st _ G _ d _ (by omega) hd (by omega) hd4]

theorem pushMem_byte (M : Word → BitVec 8) (G : Word) (i : Nat) (hi : i < 16) (s : SegW) (vk : Word)
    (d : Nat) (hd : d < 0x160) (h : d < 0x24 + 16 * i ∨ 0x34 + 16 * i ≤ d) :
    pushMem M G i s vk (G + BitVec.ofNat 32 d) = M (G + BitVec.ofNat 32 d) := by
  unfold pushMem
  rw [memStore32_get_sep (sep_offsets G (by omega) (by omega) (by omega)),
    memStore32_get_sep (sep_offsets G (by omega) (by omega) (by omega)),
    memStore32_get_sep (sep_offsets G (by omega) (by omega) (by omega)),
    memStore32_get_sep (sep_offsets G (by omega) (by omega) (by omega))]

theorem ArrInv.push {M : Word → BitVec 8} {G : Word} {segs : List SegW} (a : ArrInv M G segs)
    (hi : segs.length < 16) (s : SegW) (vk : Word) (hk : vk.extractLsb' 0 8 = s.kind) :
    ArrInv (pushMem M G segs.length s vk) G (segs ++ [s]) := by
  have hl : (segs ++ [s]).length = segs.length + 1 := by simp
  refine ⟨fun j hj => ?_, fun j h1 h2 w hw => ?_⟩
  · rw [hl] at hj
    by_cases hji : j < segs.length
    · rw [List.getElem_append_left hji]
      obtain ⟨e1, e2, e3, e4⟩ := a.1 j hji
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [pushMem_ld _ _ _ hi _ _ _ (by omega) (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_right (by omega), e1]
      · rw [pushMem_ld _ _ _ hi _ _ _ (by omega) (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_right (by omega), e2]
      · rw [pushMem_ld _ _ _ hi _ _ _ (by omega) (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_right (by omega), e3]
      · rw [pushMem_byte _ _ _ hi _ _ _ (by omega) (by omega), e4]
    · have hj' : j = segs.length := by omega
      subst hj'
      rw [List.getElem_append_right (Nat.le_refl _), List.getElem_singleton]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [pushMem_ld _ _ _ hi _ _ _ (by omega) (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_left rfl]
      · rw [pushMem_ld _ _ _ hi _ _ _ (by omega) (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_left rfl]
      · rw [pushMem_ld _ _ _ hi _ _ _ (by omega) (by omega), ite_eq_right (by omega), ite_eq_left rfl]
      · unfold pushMem; rw [memStore32_lo, hk]
  · rw [hl] at h1
    rw [pushMem_ld _ _ _ hi _ _ _ (by omega) (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega)]
    exact a.2 j (by omega) h2 w hw

theorem s8_step : ∀ i, i < 16 →
    BitVec.ofNat 32 (0x100 - 16 * i) + 0xFFFFFFF0 = BitVec.ofNat 32 (0x100 - 16 * (i + 1)) := by decide

theorem s9_slot : ∀ i, i < 16 → ∀ c, c < 16 →
    BitVec.ofNat 32 (0x2C + 16 * i) + BitVec.ofNat 32 (0x100000000 - 8 + c) = BitVec.ofNat 32 (0x24 + 16 * i + c) := by
  decide

/-- The words below the array are as before the stores. -/
theorem push_lo (M : Word → BitVec 8) (G : Word) (i : Nat) (hi : i < 16) (s : SegW) (vk : Word)
    (c : Nat) (hc : c + 4 ≤ 0x24) :
    memLoad32 (pushMem M G i s vk) (G + BitVec.ofNat 32 c) = memLoad32 M (G + BitVec.ofNat 32 c) := by
  unfold pushMem
  rw [memLoad32_store32_sep (sep_offsets G (by omega) (by omega) (by omega)),
    memLoad32_store32_sep (sep_offsets G (by omega) (by omega) (by omega)),
    memLoad32_store32_sep (sep_offsets G (by omega) (by omega) (by omega)),
    memLoad32_store32_sep (sep_offsets G (by omega) (by omega) (by omega))]

/-- The registers one pass of the loop writes before it stores the segment. -/
abbrev lpClob : List (Fin 32) := [a0, a1, a2, a3, a4, a5, (16 : Fin 32), ra, s3, s4, s6, s7, s10]

/-- During the checks of segment `s`: the loop's invariant at the start of
the pass (memory `Ms`, registers `gs`), and what the reads left. -/
structure CkCtx (R G ptr len out ilen : Word) (M0 : Word → BitVec 8) (f0 : Fin 32 → Word)
    (sv cnt : BitVec 8) (entry : Word) (segs : List SegW) (pos prev : Word)
    (Ms : Word → BitVec 8) (gs : Fin 32 → Word) (s : SegW) (pos' : Word)
    (My : Word → BitVec 8) (g : Fin 32 → Word) : Prop where
  li : LInv R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Ms gs
  lt : segs.length < cnt.toNat
  inv : IInv R G ptr len out ilen M0 f0 My g
  pos : memLoad32 My (G + 0x18 + 8) = pos'
  fr : ByteFr My Ms G
  keep : ∀ r, r ∉ lpClob → g r = gs r
  kd : (3 : BitVec 8).ult s.kind = false

/-- What the machine at `m` does with segment `s`, given what `checkSegW` decides. -/
def CkPost (P R G ptr len out ilen : Word) (M0 : Word → BitVec 8) (f0 : Fin 32 → Word)
    (sv cnt : BitVec 8) (entry : Word) (segs : List SegW) (s : SegW) (pos' : Word) (m : Machine) :
    Except (BitVec 8) Word → Prop
  | .error e => IErrDone R G out M0 f0 e m
  | .ok prev' => ∃ m' My g, Steps m m' ∧ St My P m' 0x188 g ∧
      LInv R G ptr len out ilen M0 f0 sv cnt entry (segs ++ [s]) pos' prev' My g

theorem lp_ip : ∀ rd, rd ∈ lpClob → rd ∈ ipClob ∧ rd ≠ RV32.sp ∧ rd ≠ RV32.s0 ∧ rd ≠ RV32.s1 := by
  decide

section Check

variable {P R G ptr len out ilen : Word} {M0 Ms My : Word → BitVec 8} {f0 gs g : Fin 32 → Word}
  {sv cnt : BitVec 8} {entry : Word} {segs : List SegW} {pos prev pos' : Word} {s : SegW}

theorem CkPost.pre {m m' : Machine} (c : Steps m m') :
    ∀ r, CkPost P R G ptr len out ilen M0 f0 sv cnt entry segs s pos' m' r →
      CkPost P R G ptr len out ilen M0 f0 sv cnt entry segs s pos' m r
  | .error _, h => IErrDone.pre c h
  | .ok _, ⟨n, My, g, c', rest⟩ => ⟨n, My, g, c.trans c', rest⟩

theorem CkCtx.setR (ctx : CkCtx R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Ms gs s pos' My g)
    (rd : Fin 32) {v : Word} (h : rd ∈ lpClob := by decide) :
    CkCtx R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Ms gs s pos' My (upd g rd v) :=
  { ctx with
    inv := ctx.inv.setR rd (lp_ip rd h)
    keep := fun r hr => by
      have hne : r ≠ rd := fun e => hr (by rw [e]; exact h)
      rw [updz ctx.inv.zero hne, ctx.keep r hr] }

theorem lp_sub : ∀ r, r ∉ ipClob → r ∉ lpClob := by decide

theorem nl {r : Fin 32} (hr : r ∉ lpClob) (q : Fin 32) (hq : q ∈ lpClob := by decide) : r ≠ q :=
  fun e => hr (e ▸ hq)

/-- `CkCtx` holds for any registers that agree outside `lpClob`. -/
theorem CkCtx.regs (ctx : CkCtx R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Ms gs s pos' My g)
    {g' : Fin 32 → Word} (h : ∀ r, r ∉ lpClob → g' r = g r) :
    CkCtx R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Ms gs s pos' My g' :=
  { ctx with
    inv := ctx.inv.frameR (fun r hr => h r (lp_sub r hr))
      (by rw [h _ (by decide), ctx.inv.sp]) (by rw [h _ (by decide), ctx.inv.s0])
      (by rw [h _ (by decide), ctx.inv.s1]) (by rw [h _ (by decide), ctx.inv.zero])
    keep := fun r hr => by rw [h r hr, ctx.keep r hr] }

theorem CkCtx.mem (ctx : CkCtx R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Ms gs s pos' My g)
    (env : IEnv P R G ptr len out) (c : Nat) (v : Word) (hc : c + 4 ≤ 8 ∨ (0x10 ≤ c ∧ c + 4 ≤ 0x14)) :
    CkCtx R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Ms gs s pos'
      (memStore32 My (G + BitVec.ofNat 32 c) v) g :=
  { ctx with
    inv := ctx.inv.st32 env c v (Or.inl (by rcases hc with h | ⟨_, h⟩ <;> omega))
    pos := by
      rw [show G + 0x18 + 8 = G + BitVec.ofNat 32 0x20 by rw [BitVec.add_assoc]; rfl,
        memLoad32_store32_sep (sep_offsets G (by omega) (by omega) (by omega)),
        show G + BitVec.ofNat 32 0x20 = G + 0x18 + 8 by rw [BitVec.add_assoc]; rfl, ctx.pos]
    fr := (ByteFr.st32 My G c v hc).trans ctx.fr }

theorem zk_ult2 (k : BitVec 8) : branchTaken .bltu (k.zeroExtend 32) (aluEval .add 0 2) = k.ult 2 := by
  revert k; decide

theorem one_ult_zk (k : BitVec 8) :
    branchTaken .bltu (aluEval .add 0 1) (k.zeroExtend 32) = (1 : BitVec 8).ult k := by
  revert k; decide

theorem sltu_k2 (k : BitVec 8) : aluEval .sltu (k.zeroExtend 32) 2 = if k.ult 2 then 1 else 0 := by
  revert k; decide

/-- Offset 0x418 with 9 in `a6`. -/
theorem CkCtx.e418 (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (ctx : CkCtx R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Ms gs s pos' My g)
    {m : Machine} (st : St My P m 0x418 g) {e : BitVec 8} (h6 : (g (16 : Fin 32)).extractLsb' 0 8 = e)
    {r : Except (BitVec 8) Word} (hr : r = .error e) :
    CkPost P R G ptr len out ilen M0 f0 sv cnt entry segs s pos' m r := by
  subst hr; exact ip_err418 env code0 ctx.inv st h6

/-- From offset 0x2AE: the order check, then the segment stored in its slot
and back to 0x188. -/
theorem lp_ck4 (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (ctx : CkCtx R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Ms gs s pos' My g)
    {m : Machine} (st : St My P m 0x2AE g) {vk : Word} (hvk : vk.extractLsb' 0 8 = s.kind)
    (ha3 : g a3 = s.addr) (hs4 : g s4 = s.off) (hs3 : g s3 = s.len) (hs10 : g s10 = vk)
    (ha1 : g a1 = s.off + s.len) (ha6 : g (16 : Fin 32) = 9)
    (f1 : s.len ≠ 0#32) (f2 : (s.off + s.len).ult s.off = false) (f3 : ilen.ult (s.off + s.len) = false)
    (f4 : (regionHi s.kind).ult (s.addr + s.len) = false) (f5 : (s.addr + s.len).ult s.addr = false)
    (f6 : s.addr.ult (regionLo s.kind) = false) (f7 : alignOk s = true) :
    CkPost P R G ptr len out ilen M0 f0 sv cnt entry segs s pos' m (checkSegW ilen prev s) := by
  have hc := (ctx.inv.code env code0).parse
  have hs5 : g s5 = prev := by rw [ctx.keep s5 (by decide), ctx.li.s5]
  by_cases f8 : s.off.ult prev = true
  · obtain ⟨m1, d1, u1⟩ := st.taken hc 0x418 ip_at_2ae (by decide) (by rw [hs4, hs5]; exact f8)
    exact CkPost.pre (.single d1) _ (ctx.e418 env code0 u1 (by rw [ha6])
      (by simp [checkSegW, f1, f2, f3, f4, f5, f6, f7, f8] <;> rfl))
  · have f8' : s.off.ult prev = false := Bool.eq_false_iff.mpr f8
    have hck : checkSegW ilen prev s = .ok (s.off + s.len) := by
      simp [checkSegW, f1, f2, f3, f4, f5, f6, f7, f8'] <;> rfl
    rw [hck]
    obtain ⟨m1, d1, u1⟩ := st.notTaken hc 0x2B2 ip_at_2ae (by decide) (by rw [hs4, hs5]; exact f8')
    have hi16 : segs.length < 16 := Nat.lt_of_lt_of_le ctx.lt ctx.li.hc
    have hs9 : g s9 = G + BitVec.ofNat 32 (0x2C + 16 * segs.length) := by
      rw [ctx.keep s9 (by decide), ctx.li.s9]
    have hs8 : g s8 = BitVec.ofNat 32 (0x100 - 16 * segs.length) := by
      rw [ctx.keep s8 (by decide), ctx.li.s8]
    have e0 : G + BitVec.ofNat 32 (0x2C + 16 * segs.length) + 0xFFFFFFF8 =
        G + BitVec.ofNat 32 (0x24 + 16 * segs.length) := by
      have h := s9_slot segs.length hi16 0 (by omega)
      rw [Nat.add_zero, Nat.add_zero] at h
      rw [BitVec.add_assoc, show (0xFFFFFFF8 : Word) = BitVec.ofNat 32 (0x100000000 - 8) from rfl, h]
    have e1 : G + BitVec.ofNat 32 (0x2C + 16 * segs.length) + 0xFFFFFFFC =
        G + BitVec.ofNat 32 (0x28 + 16 * segs.length) := by
      have h := s9_slot segs.length hi16 4 (by omega)
      rw [show 0x24 + 16 * segs.length + 4 = 0x28 + 16 * segs.length by omega] at h
      rw [BitVec.add_assoc, show (0xFFFFFFFC : Word) = BitVec.ofNat 32 (0x100000000 - 8 + 4) from rfl, h]
    have e3 : G + BitVec.ofNat 32 (0x2C + 16 * segs.length) + 4 =
        G + BitVec.ofNat 32 (0x30 + 16 * segs.length) := by
      rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]; congr 2; omega
    obtain ⟨m2, d2, u2⟩ := u1.sw hc ip_at_2b2 (off' := 0x2B6) (by decide)
      (by rw [hs9, e0]; exact aligned_add env.hG (by omega))
    rw [hs9, e0, ha3] at u2
    have inv2 := ctx.inv.st32 env (0x24 + 16 * segs.length) s.addr (Or.inr ⟨by omega, by omega⟩)
    have hc2 := (inv2.code env code0).parse
    obtain ⟨m3, d3, u3⟩ := u2.sw hc2 ip_at_2b6 (off' := 0x2BA) (by decide)
      (by rw [hs9, e1]; exact aligned_add env.hG (by omega))
    rw [hs9, e1, hs4] at u3
    have inv3 := inv2.st32 env (0x28 + 16 * segs.length) s.off (Or.inr ⟨by omega, by omega⟩)
    have hc3 := (inv3.code env code0).parse
    obtain ⟨m4, d4, u4⟩ := u3.sw hc3 ip_at_2ba (off' := 0x2BE) (by decide)
      (by rw [hs9, add_lit_zero]; exact aligned_add env.hG (by omega))
    rw [hs9, add_lit_zero, hs3] at u4
    have inv4 := inv3.st32 env (0x2C + 16 * segs.length) s.len (Or.inr ⟨by omega, by omega⟩)
    have hc4 := (inv4.code env code0).parse
    obtain ⟨m5, d5, u5⟩ := u4.sw hc4 ip_at_2be (off' := 0x2C2) (by decide)
      (by rw [hs9, e3]; exact aligned_add env.hG (by omega))
    rw [hs9, e3, hs10] at u5
    have inv5 := inv4.st32 env (0x30 + 16 * segs.length) vk (Or.inr ⟨by omega, by omega⟩)
    have hc5 := (inv5.code env code0).parse
    obtain ⟨m6, d6, u6⟩ := u5.aluImm hc5 ip_at_2c2 (off' := 0x2C4) (by decide)
    obtain ⟨m7, d7, u7⟩ := u6.aluImm hc5 ip_at_2c4 (off' := 0x2C6) (by decide)
    obtain ⟨m8, d8, u8⟩ := u7.alu hc5 ip_at_2c6 (off' := 0x2C8) (by decide)
    obtain ⟨m9, d9, u9⟩ := u8.jump hc5 ip_at_2c8 (off' := 0x188) (by decide)
      (by rw [u8.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0x188 (by decide)))
    have hz := ctx.inv.zero
    have hM : memStore32 (memStore32 (memStore32 (memStore32 My (G + BitVec.ofNat 32 (0x24 + 16 * segs.length))
        s.addr) (G + BitVec.ofNat 32 (0x28 + 16 * segs.length)) s.off)
        (G + BitVec.ofNat 32 (0x2C + 16 * segs.length)) s.len) (G + BitVec.ofNat 32 (0x30 + 16 * segs.length)) vk =
        pushMem My G segs.length s vk := rfl
    rw [hM] at u9 inv5
    have arrY : ArrInv My G segs := ctx.li.arr.agree ctx.fr.arr (by omega)
    refine ⟨m9, _, _, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8
      (.single d9)))))))), u9, ⟨((inv5.setR s8).setR s9).setR s5, ?_, arrY.push hi16 s vk hvk, ?_, ctx.li.hc,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [show G + 0x18 + 8 = G + BitVec.ofNat 32 0x20 by rw [BitVec.add_assoc]; rfl,
        pushMem_ld _ _ _ hi16 _ _ _ (by omega) (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega),
        show G + BitVec.ofNat 32 0x20 = G + 0x18 + 8 by rw [BitVec.add_assoc]; rfl, ctx.pos]
    · simp only [List.length_append, List.length_singleton]; exact ctx.lt
    · rw [updz (by simp) (by decide), updz (by simp) (by decide), updz hz (by decide),
        ctx.keep s2 (by decide), ctx.li.s2]
    · rw [updz (by simp) (by decide), updz (by simp) (by decide), updz hz (by decide),
        ctx.keep s11 (by decide), ctx.li.s11]
    · rw [updz (by simp) (by decide), updz (by simp) (by decide), upd_same (by decide), hs8,
        List.length_append, List.length_singleton]
      exact s8_step _ hi16
    · rw [updz (by simp) (by decide), upd_same (by decide), updz hz (by decide), hs9,
        List.length_append, List.length_singleton]
      show _ + BitVec.ofNat 32 0x10 = _
      rw [add_ofNat_assoc]; congr 2 <;> omega
    · rw [upd_same (by decide)]
      show upd (upd g s8 _) s9 _ 0 + _ = _
      rw [upd_zero, updz (by simp) (by decide), updz hz (by decide), ha1]
      exact BitVec.zero_add _
    · rw [show G + 0x14 = G + BitVec.ofNat 32 0x14 from rfl, push_lo _ _ _ hi16 _ _ _ (by omega),
        ctx.fr.word 0x14 (Or.inr (Or.inl ⟨by omega, by omega⟩))]
      exact ctx.li.mask
    · rw [show G + 8 = G + BitVec.ofNat 32 8 from rfl, push_lo _ _ _ hi16 _ _ _ (by omega),
        ctx.fr.word 8 (Or.inl ⟨by omega, by omega⟩)]
      exact ctx.li.ent
    · rw [show G + 0xC = G + BitVec.ofNat 32 0xC from rfl, push_lo _ _ _ hi16 _ _ _ (by omega),
        ctx.fr.word 0xC (Or.inl ⟨by omega, by omega⟩)]
      exact ctx.li.cntw

theorem sltu_one (w : Word) (h : w ≠ 0) : aluEval .sltu w 1 = 0 := by
  have : ¬ w.toNat < 1 := fun h' => h (BitVec.eq_of_toNat_eq (show w.toNat = 0 by omega))
  show (if w.ult 1 then 1 else 0) = 0
  rw [show w.ult 1 = false from decide_eq_false this]; rfl

theorem k2_one (k : BitVec 8) : k.ult 2 = !(1 : BitVec 8).ult k := by revert k; decide

/-- The first alignment check, on MMU pages. -/
def align1 (s : SegW) : Bool :=
  if ((s.addr ||| s.off) &&& 0xFFFF) != 0 then !s.kind.ult 2
  else !(s.kind.ult 2 && (s.len &&& 0xFFFF) != 0)

/-- The second alignment check, on words. -/
def align2 (s : SegW) : Bool :=
  if ((s.addr ||| s.off) &&& 3) != 0 then !(1 : BitVec 8).ult s.kind
  else !((1 : BitVec 8).ult s.kind && (s.len &&& 3) != 0)

theorem alignOk_eq (s : SegW) : alignOk s = (align1 s && align2 s) := rfl

theorem align1_nz {s : SegW} (h : (s.addr ||| s.off) &&& 0xFFFF ≠ 0) : align1 s = !s.kind.ult 2 := by
  unfold align1; rw [show (((s.addr ||| s.off) &&& 0xFFFF) != 0) = true from bne_iff_ne.mpr h]; rfl

theorem align1_z {s : SegW} (h : (s.addr ||| s.off) &&& 0xFFFF = 0) :
    align1 s = !(s.kind.ult 2 && (s.len &&& 0xFFFF) != 0) := by
  unfold align1; rw [h]; rfl

theorem align2_nz {s : SegW} (h : (s.addr ||| s.off) &&& 3 ≠ 0) : align2 s = !(1 : BitVec 8).ult s.kind := by
  unfold align2; rw [show (((s.addr ||| s.off) &&& 3) != 0) = true from bne_iff_ne.mpr h]; rfl

theorem align2_z {s : SegW} (h : (s.addr ||| s.off) &&& 3 = 0) :
    align2 s = !((1 : BitVec 8).ult s.kind && (s.len &&& 3) != 0) := by
  unfold align2; rw [h]; rfl

/-- From offset 0x290: the word-alignment check, then `lp_ck4`. -/
theorem lp_ck3b (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (ctx : CkCtx R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Ms gs s pos' My g)
    {m : Machine} (st : St My P m 0x290 g) {vk : Word} (hvk : vk.extractLsb' 0 8 = s.kind)
    (ha3 : g a3 = s.addr) (hs4 : g s4 = s.off) (hs3 : g s3 = s.len) (hs10 : g s10 = vk)
    (ha1 : g a1 = s.off + s.len) (ha6 : g (16 : Fin 32) = 9) (ha2 : g a2 = s.kind.zeroExtend 32)
    (ha4 : g a4 = s.addr ||| s.off)
    (f1 : s.len ≠ 0#32) (f2 : (s.off + s.len).ult s.off = false) (f3 : ilen.ult (s.off + s.len) = false)
    (f4 : (regionHi s.kind).ult (s.addr + s.len) = false) (f5 : (s.addr + s.len).ult s.addr = false)
    (f6 : s.addr.ult (regionLo s.kind) = false) (A1 : align1 s = true) :
    CkPost P R G ptr len out ilen M0 f0 sv cnt entry segs s pos' m (checkSegW ilen prev s) := by
  have hc := (ctx.inv.code env code0).parse
  have hz := ctx.inv.zero
  obtain ⟨m1, d1, u1⟩ := st.aluImm hc ip_at_290 (off' := 0x292) (by decide)
  have c1 := ctx.regs (g' := reg m1) fun r hr => by rw [u1.regs, updz hz (nl hr a4)]
  have r1 : ∀ r, r ≠ a4 → reg m1 r = g r := fun r h => by rw [u1.regs, updz hz h]
  have r1a4 : reg m1 a4 = (s.addr ||| s.off) &&& 3 := by rw [u1.regs, upd_same (by decide), ha4]; rfl
  have err : ∀ {n : Machine} {g' : Fin 32 → Word}, St My P n 0x418 g' →
      CkCtx R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Ms gs s pos' My g' →
      g' (16 : Fin 32) = 9 → align2 s = false →
      CkPost P R G ptr len out ilen M0 f0 sv cnt entry segs s pos' n (checkSegW ilen prev s) :=
    fun st' c' h6 hal => c'.e418 env code0 st' (by rw [h6]) (by
      have : alignOk s = false := by rw [alignOk_eq, A1, hal]; rfl
      simp [checkSegW, f1, f2, f3, f4, f5, f6, this] <;> rfl)
  have fin : ∀ {n : Machine} {g' : Fin 32 → Word}, St My P n 0x2AE g' →
      CkCtx R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Ms gs s pos' My g' →
      (∀ r, r ≠ a0 → r ≠ a2 → r ≠ a4 → g' r = g r) → align2 s = true →
      CkPost P R G ptr len out ilen M0 f0 sv cnt entry segs s pos' n (checkSegW ilen prev s) :=
    fun st' c' hr hal => lp_ck4 env code0 c' st' hvk (by rw [hr _ (by decide) (by decide) (by decide), ha3])
      (by rw [hr _ (by decide) (by decide) (by decide), hs4]) (by rw [hr _ (by decide) (by decide) (by decide), hs3])
      (by rw [hr _ (by decide) (by decide) (by decide), hs10]) (by rw [hr _ (by decide) (by decide) (by decide), ha1])
      (by rw [hr _ (by decide) (by decide) (by decide), ha6]) f1 f2 f3 f4 f5 f6
      (by rw [alignOk_eq, A1, hal]; rfl)
  by_cases hx3 : (s.addr ||| s.off) &&& 3 = 0
  · obtain ⟨m2, d2, u2⟩ := u1.self.taken (c1.inv.code env code0).parse 0x29C ip_at_292 (by decide)
      (by rw [r1a4, hx3, c1.inv.zero]; rfl)
    obtain ⟨m3, d3, u3⟩ := u2.aluImm hc ip_at_29c (off' := 0x2A0) (by decide)
    obtain ⟨m4, d4, u4⟩ := u3.aluImm hc ip_at_2a0 (off' := 0x2A4) (by decide)
    obtain ⟨m5, d5, u5⟩ := u4.aluImm hc ip_at_2a4 (off' := 0x2A8) (by decide)
    obtain ⟨m6, d6, u6⟩ := u5.alu hc ip_at_2a8 (off' := 0x2AA) (by decide)
    have c6 := c1.regs (g' := reg m6) fun r hr => by
      rw [u6.regs, updz (by simp) (nl hr a0), updz (by simp) (nl hr a2), updz (by simp) (nl hr a0),
        updz c1.inv.zero (nl hr a0)]
    have r6 : ∀ r, r ≠ a0 → r ≠ a2 → r ≠ a4 → reg m6 r = g r := fun r h0 h2 h4 => by
      rw [u6.regs, updz (by simp) h0, updz (by simp) h2, updz (by simp) h0, updz c1.inv.zero h0, r1 r h4]
    have r6a0 : reg m6 a0 = aluEval .or (aluEval .sltu (aluEval .and s.len 3) 1)
        (aluEval .sltu (s.kind.zeroExtend 32) 2) := by
      rw [u6.regs]; simp +decide only [upd, ↓reduceIte]; rw [r1 a2 (by decide), r1 s3 (by decide), ha2, hs3]
    have pre : Steps m m6 := .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6)))))
    have hc6 := (c6.inv.code env code0).parse
    by_cases hl3 : s.len &&& 3 = 0
    · have hl3' : aluEval .and s.len 3 = 0 := hl3
      obtain ⟨m7, d7, u7⟩ := u6.self.notTaken hc6 0x2AE ip_at_2aa (by decide)
        (by rw [r6a0, c6.inv.zero, hl3', sltu_k2]; cases s.kind.ult 2 <;> rfl)
      exact CkPost.pre (pre.trans (.single d7)) _ (fin u7 c6 r6 (by
        rw [align2_z hx3, hl3]; cases (1 : BitVec 8).ult s.kind <;> rfl))
    · have hl3' : aluEval .and s.len 3 ≠ 0 := hl3
      by_cases hk2 : s.kind.ult 2 = true
      · have h1k : (1 : BitVec 8).ult s.kind = false := by rw [k2_one] at hk2; simpa using hk2
        obtain ⟨m7, d7, u7⟩ := u6.self.notTaken hc6 0x2AE ip_at_2aa (by decide)
          (by rw [r6a0, c6.inv.zero, sltu_one _ hl3', sltu_k2, hk2]; rfl)
        exact CkPost.pre (pre.trans (.single d7)) _ (fin u7 c6 r6 (by rw [align2_z hx3, h1k]; rfl))
      · have hk2' : s.kind.ult 2 = false := Bool.eq_false_iff.mpr hk2
        have h1k : (1 : BitVec 8).ult s.kind = true := by rw [k2_one] at hk2'; simpa using hk2'
        obtain ⟨m7, d7, u7⟩ := u6.self.taken hc6 0x418 ip_at_2aa (by decide)
          (by rw [r6a0, c6.inv.zero, sltu_one _ hl3', sltu_k2, hk2']; rfl)
        exact CkPost.pre (pre.trans (.single d7)) _ (err u7 c6
          (by rw [r6 _ (by decide) (by decide) (by decide), ha6])
          (by rw [align2_z hx3, h1k, show ((s.len &&& 3) != 0) = true from bne_iff_ne.mpr hl3]; rfl))
  · obtain ⟨m2, d2, u2⟩ := u1.self.notTaken (c1.inv.code env code0).parse 0x294 ip_at_292 (by decide)
      (by rw [r1a4, c1.inv.zero]; exact Bool.eq_false_iff.mpr fun h => hx3 (beq_iff_eq.mp h))
    obtain ⟨m3, d3, u3⟩ := u2.aluImm hc ip_at_294 (off' := 0x296) (by decide)
    have c3 := c1.regs (g' := reg m3) fun r hr => by rw [u3.regs, updz c1.inv.zero (nl hr a0)]
    have r3 : ∀ r, r ≠ a0 → r ≠ a2 → r ≠ a4 → reg m3 r = g r := fun r h0 _ h4 => by
      rw [u3.regs, updz c1.inv.zero h0, r1 r h4]
    have hc3 := (c3.inv.code env code0).parse
    have br : branchTaken .bltu (reg m3 a0) (reg m3 a2) = (1 : BitVec 8).ult s.kind := by
      rw [u3.regs a0, u3.regs a2, upd_a0, updz c1.inv.zero (by decide), r1 a2 (by decide), ha2,
        show reg m1 x0 = 0 from c1.inv.zero]
      exact one_ult_zk _
    have pre : Steps m m3 := .cons d1 (.cons d2 (.single d3))
    by_cases hk1 : (1 : BitVec 8).ult s.kind = true
    · obtain ⟨m4, d4, u4⟩ := u3.self.taken hc3 0x418 ip_at_296 (by decide) (by rw [br, hk1])
      exact CkPost.pre (pre.trans (.single d4)) _ (err u4 c3
        (by rw [r3 _ (by decide) (by decide) (by decide), ha6]) (by rw [align2_nz hx3, hk1]; rfl))
    · obtain ⟨m4, d4, u4⟩ := u3.self.notTaken hc3 0x29A ip_at_296 (by decide)
        (by rw [br]; exact Bool.eq_false_iff.mpr hk1)
      obtain ⟨m5, d5, u5⟩ := u4.jump hc3 ip_at_29a (off' := 0x2AE) (by decide)
        (by rw [u4.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0x2AE (by decide)))
      exact CkPost.pre (pre.trans (.cons d4 (.single d5))) _ (fin u5 c3 r3 (by
        rw [align2_nz hx3, Bool.eq_false_iff.mpr hk1]; rfl))

/-- From offset 0x26E: the MMU-page check, then `lp_ck3b`. -/
theorem lp_ck3 (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (ctx : CkCtx R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Ms gs s pos' My g)
    {m : Machine} (st : St My P m 0x26E g) {vk : Word} (hvk : vk.extractLsb' 0 8 = s.kind)
    (ha3 : g a3 = s.addr) (hs4 : g s4 = s.off) (hs3 : g s3 = s.len) (hs10 : g s10 = vk)
    (ha1 : g a1 = s.off + s.len) (ha6 : g (16 : Fin 32) = 9) (ha2 : g a2 = s.kind.zeroExtend 32)
    (f1 : s.len ≠ 0#32) (f2 : (s.off + s.len).ult s.off = false) (f3 : ilen.ult (s.off + s.len) = false)
    (f4 : (regionHi s.kind).ult (s.addr + s.len) = false) (f5 : (s.addr + s.len).ult s.addr = false)
    (f6 : s.addr.ult (regionLo s.kind) = false) :
    CkPost P R G ptr len out ilen M0 f0 sv cnt entry segs s pos' m (checkSegW ilen prev s) := by
  have hc := (ctx.inv.code env code0).parse
  have hz := ctx.inv.zero
  have hmask : memLoad32 My (G + 0x14) = 0xFFFF := by
    rw [show G + 0x14 = G + BitVec.ofNat 32 0x14 from rfl,
      ctx.fr.word 0x14 (Or.inr (Or.inl ⟨by omega, by omega⟩))]
    exact ctx.li.mask
  obtain ⟨m1, d1, u1⟩ := st.alu hc ip_at_26e (off' := 0x272) (by decide)
  obtain ⟨m2, d2, u2⟩ := u1.lw hc ip_at_272 (off' := 0x274) (by decide)
    (by rw [updz hz (by decide), ctx.inv.sp]; exact aligned_add env.hG (k := 0x14) (by decide))
  obtain ⟨m3, d3, u3⟩ := u2.alu hc ip_at_274 (off' := 0x276) (by decide)
  have c3 := ctx.regs (g' := reg m3) fun r hr => by
    rw [u3.regs, updz (by simp) (nl hr a0), updz (by simp) (nl hr a0), updz hz (nl hr a4)]
  have r3 : ∀ r, r ≠ a0 → r ≠ a4 → reg m3 r = g r := fun r h0 h4 => by
    rw [u3.regs, updz (by simp) h0, updz (by simp) h0, updz hz h4]
  have r3a4 : reg m3 a4 = s.addr ||| s.off := by
    rw [r3 a4 |> fun _ => u3.regs a4]; simp +decide only [upd, ↓reduceIte]; rw [ha3, hs4]; rfl
  have r3a0 : reg m3 a0 = (s.addr ||| s.off) &&& 0xFFFF := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
    rw [ctx.inv.sp, hmask, ha3, hs4]; exact BitVec.and_comm _ _
  have hc3 := (c3.inv.code env code0).parse
  have pre : Steps m m3 := .cons d1 (.cons d2 (.single d3))
  have err : ∀ {n : Machine} {g' : Fin 32 → Word}, St My P n 0x418 g' →
      CkCtx R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Ms gs s pos' My g' →
      g' (16 : Fin 32) = 9 → align1 s = false →
      CkPost P R G ptr len out ilen M0 f0 sv cnt entry segs s pos' n (checkSegW ilen prev s) :=
    fun st' c' h6 hal => c'.e418 env code0 st' (by rw [h6]) (by
      have : alignOk s = false := by rw [alignOk_eq, hal]; rfl
      simp [checkSegW, f1, f2, f3, f4, f5, f6, this] <;> rfl)
  have go : ∀ {n : Machine} {g' : Fin 32 → Word}, St My P n 0x290 g' →
      CkCtx R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Ms gs s pos' My g' →
      (∀ r, r ≠ a0 → g' r = reg m3 r) → align1 s = true →
      CkPost P R G ptr len out ilen M0 f0 sv cnt entry segs s pos' n (checkSegW ilen prev s) :=
    fun st' c' hr hal => lp_ck3b env code0 c' st' hvk
      (by rw [hr _ (by decide), r3 _ (by decide) (by decide), ha3])
      (by rw [hr _ (by decide), r3 _ (by decide) (by decide), hs4])
      (by rw [hr _ (by decide), r3 _ (by decide) (by decide), hs3])
      (by rw [hr _ (by decide), r3 _ (by decide) (by decide), hs10])
      (by rw [hr _ (by decide), r3 _ (by decide) (by decide), ha1])
      (by rw [hr _ (by decide), r3 _ (by decide) (by decide), ha6])
      (by rw [hr _ (by decide), r3 _ (by decide) (by decide), ha2])
      (by rw [hr _ (by decide), r3a4]) f1 f2 f3 f4 f5 f6 hal
  by_cases hx : (s.addr ||| s.off) &&& 0xFFFF = 0
  · obtain ⟨m4, d4, u4⟩ := u3.self.taken hc3 0x280 ip_at_276 (by decide)
      (by rw [r3a0, hx, c3.inv.zero]; rfl)
    obtain ⟨m5, d5, u5⟩ := u4.aluImm hc3 ip_at_280 (off' := 0x282) (by decide)
    have c5 := c3.regs (g' := reg m5) fun r hr => by rw [u5.regs, updz c3.inv.zero (nl hr a0)]
    have r5 : ∀ r, r ≠ a0 → reg m5 r = reg m3 r := fun r h0 => by rw [u5.regs, updz c3.inv.zero h0]
    have hc5 := (c5.inv.code env code0).parse
    have br : branchTaken .bltu (reg m5 a0) (reg m5 a2) = (1 : BitVec 8).ult s.kind := by
      rw [u5.regs a0, u5.regs a2, upd_a0, updz c3.inv.zero (by decide), r3 a2 (by decide) (by decide), ha2,
        show reg m3 x0 = 0 from c3.inv.zero]
      exact one_ult_zk _
    by_cases hk1 : (1 : BitVec 8).ult s.kind = true
    · obtain ⟨m6, d6, u6⟩ := u5.self.taken hc5 0x290 ip_at_282 (by decide) (by rw [br, hk1])
      exact CkPost.pre (pre.trans (.cons d4 (.cons d5 (.single d6)))) _ (go u6 c5 r5 (by
        rw [align1_z hx, show s.kind.ult 2 = false by rw [k2_one, hk1]; rfl]; rfl))
    · have hk1' : (1 : BitVec 8).ult s.kind = false := Bool.eq_false_iff.mpr hk1
      obtain ⟨m6, d6, u6⟩ := u5.self.notTaken hc5 0x286 ip_at_282 (by decide) (by rw [br, hk1'])
      obtain ⟨m7, d7, u7⟩ := u6.lw hc5 ip_at_286 (off' := 0x288) (by decide)
        (by rw [r5 _ (by decide), r3 _ (by decide) (by decide), ctx.inv.sp]
            exact aligned_add env.hG (k := 0x14) (by decide))
      obtain ⟨m8, d8, u8⟩ := u7.alu hc5 ip_at_288 (off' := 0x28C) (by decide)
      have c8 := c5.regs (g' := reg m8) fun r hr => by
        rw [u8.regs, updz (by simp) (nl hr a0), updz c5.inv.zero (nl hr a0)]
      have r8 : ∀ r, r ≠ a0 → reg m8 r = reg m3 r := fun r h0 => by
        rw [u8.regs, updz (by simp) h0, updz c5.inv.zero h0, r5 r h0]
      have r8a0 : reg m8 a0 = s.len &&& 0xFFFF := by
        rw [u8.regs]; simp +decide only [upd, ↓reduceIte]
        rw [r5 s3 (by decide), r3 s3 (by decide) (by decide), hs3, r5 sp (by decide),
          r3 sp (by decide) (by decide), ctx.inv.sp, hmask]; rfl
      have hc8 := (c8.inv.code env code0).parse
      have pre8 : Steps m m8 := pre.trans (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.single d8)))))
      have hk2 : s.kind.ult 2 = true := by rw [k2_one, hk1']; rfl
      by_cases hl : s.len &&& 0xFFFF = 0
      · obtain ⟨m9, d9, u9⟩ := u8.self.notTaken hc8 0x290 ip_at_28c (by decide)
          (by rw [r8a0, hl, c8.inv.zero]; rfl)
        exact CkPost.pre (pre8.trans (.single d9)) _ (go u9 c8 r8 (by rw [align1_z hx, hk2, hl]; rfl))
      · obtain ⟨m9, d9, u9⟩ := u8.self.taken hc8 0x418 ip_at_28c (by decide)
          (by rw [r8a0, c8.inv.zero]; exact bne_iff_ne.mpr hl)
        exact CkPost.pre (pre8.trans (.single d9)) _ (err u9 c8
          (by rw [r8 _ (by decide), r3 _ (by decide) (by decide), ha6])
          (by rw [align1_z hx, hk2, show ((s.len &&& 0xFFFF) != 0) = true from bne_iff_ne.mpr hl]; rfl))
  · obtain ⟨m4, d4, u4⟩ := u3.self.notTaken hc3 0x278 ip_at_276 (by decide)
      (by rw [r3a0, c3.inv.zero]; exact Bool.eq_false_iff.mpr fun h => hx (beq_iff_eq.mp h))
    obtain ⟨m5, d5, u5⟩ := u4.aluImm hc3 ip_at_278 (off' := 0x27A) (by decide)
    have c5 := c3.regs (g' := reg m5) fun r hr => by rw [u5.regs, updz c3.inv.zero (nl hr a0)]
    have r5 : ∀ r, r ≠ a0 → reg m5 r = reg m3 r := fun r h0 => by rw [u5.regs, updz c3.inv.zero h0]
    have hc5 := (c5.inv.code env code0).parse
    have br : branchTaken .bltu (reg m5 a2) (reg m5 a0) = s.kind.ult 2 := by
      rw [u5.regs a0, u5.regs a2, upd_a0, updz c3.inv.zero (by decide), r3 a2 (by decide) (by decide), ha2,
        show reg m3 x0 = 0 from c3.inv.zero]
      exact zk_ult2 _
    by_cases hk2 : s.kind.ult 2 = true
    · obtain ⟨m6, d6, u6⟩ := u5.self.taken hc5 0x418 ip_at_27a (by decide) (by rw [br, hk2])
      exact CkPost.pre (pre.trans (.cons d4 (.cons d5 (.single d6)))) _ (err u6 c5
        (by rw [r5 _ (by decide), r3 _ (by decide) (by decide), ha6]) (by rw [align1_nz hx, hk2]; rfl))
    · obtain ⟨m6, d6, u6⟩ := u5.self.notTaken hc5 0x27E ip_at_27a (by decide)
        (by rw [br]; exact Bool.eq_false_iff.mpr hk2)
      obtain ⟨m7, d7, u7⟩ := u6.jump hc5 ip_at_27e (off' := 0x290) (by decide)
        (by rw [u6.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0x290 (by decide)))
      exact CkPost.pre (pre.trans (.cons d4 (.cons d5 (.cons d6 (.single d7))))) _ (go u7 c5 r5 (by
        rw [align1_nz hx, Bool.eq_false_iff.mpr hk2]; rfl))

theorem tbl_al_hi : ∀ k : BitVec 8, (3 : BitVec 8).ult k = false →
    (aluEval .add (aluEval .add 0x3FCC5000 0x240) (k.zeroExtend 32 <<< 2) + 0).toNat % 4 = 0 := by decide

theorem tbl_al_lo : ∀ k : BitVec 8, (3 : BitVec 8).ult k = false →
    (aluEval .add (k.zeroExtend 32 <<< 2) (aluEval .add 0x3FCC5000 0x250) + 0).toNat % 4 = 0 := by decide

/-- From offset 0x236: the region checks, then `lp_ck3`. -/
theorem lp_ck2 (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (ctx : CkCtx R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Ms gs s pos' My g)
    {m : Machine} (st : St My P m 0x236 g) {X : Word}
    (hs7 : g s7 = s.addr) (hs4 : g s4 = s.off) (hs3 : g s3 = s.len)
    (hs10 : g s10 = aluEval .or (aluEval .and X 0xFFFFFF00) (s.kind.zeroExtend 32))
    (ha1 : g a1 = s.off + s.len) (ha6 : g (16 : Fin 32) = 9) (ha2 : g a2 = s.kind.zeroExtend 32)
    (h10 : memLoad32 My (G + 0x10) = aluEval .srl s.addr 8)
    (f1 : s.len ≠ 0#32) (f2 : (s.off + s.len).ult s.off = false) (f3 : ilen.ult (s.off + s.len) = false) :
    CkPost P R G ptr len out ilen M0 f0 sv cnt entry segs s pos' m (checkSegW ilen prev s) := by
  have code := ctx.inv.code env code0
  have hc := code.parse
  have hz := ctx.inv.zero
  obtain ⟨m1, d1, u1⟩ := st.aluImm hc ip_at_236 (off' := 0x23A) (by decide)
  obtain ⟨m2, d2, u2⟩ := u1.aluImm hc ip_at_23a (off' := 0x23C) (by decide)
  obtain ⟨m3, d3, u3⟩ := u2.lui hc ip_at_23c (off' := 0x240) (by decide)
  obtain ⟨m4, d4, u4⟩ := u3.aluImm hc ip_at_240 (off' := 0x244) (by decide)
  obtain ⟨m5, d5, u5⟩ := u4.alu hc ip_at_244 (off' := 0x246) (by decide)
  have r5a3 : upd (upd (upd (upd (upd g a4 (aluEval .sll (g s10) 0x18)) a4
      (aluEval .srl (upd g a4 (aluEval .sll (g s10) 0x18) a4) 0x16)) a3 0x3FCC5000) a3
      (aluEval .add (upd (upd (upd g a4 (aluEval .sll (g s10) 0x18)) a4
        (aluEval .srl (upd g a4 (aluEval .sll (g s10) 0x18) a4) 0x16)) a3 0x3FCC5000 a3) 0x240)) a3
      (aluEval .add (upd (upd (upd (upd g a4 (aluEval .sll (g s10) 0x18)) a4
        (aluEval .srl (upd g a4 (aluEval .sll (g s10) 0x18) a4) 0x16)) a3 0x3FCC5000) a3
        (aluEval .add (upd (upd (upd g a4 (aluEval .sll (g s10) 0x18)) a4
          (aluEval .srl (upd g a4 (aluEval .sll (g s10) 0x18) a4) 0x16)) a3 0x3FCC5000 a3) 0x240) a3)
        (upd (upd (upd (upd g a4 (aluEval .sll (g s10) 0x18)) a4
          (aluEval .srl (upd g a4 (aluEval .sll (g s10) 0x18) a4) 0x16)) a3 0x3FCC5000) a3
          (aluEval .add (upd (upd (upd g a4 (aluEval .sll (g s10) 0x18)) a4
            (aluEval .srl (upd g a4 (aluEval .sll (g s10) 0x18) a4) 0x16)) a3 0x3FCC5000 a3) 0x240) a4)) a3 =
      aluEval .add (aluEval .add 0x3FCC5000 0x240) (s.kind.zeroExtend 32 <<< 2) := by
    simp +decide only [upd, ↓reduceIte]; rw [hs10, s10_idx]
  obtain ⟨m6, d6, u6⟩ := u5.lw hc ip_at_246 (off' := 0x248) (by decide)
    (by rw [r5a3]; exact tbl_al_hi _ ctx.kd)
  rw [r5a3, tbl_hi _ code.ends _ ctx.kd] at u6
  have u6' := u6.self
  have c6 := ctx.regs (g' := reg m6) fun r hr => by
    rw [u6.regs, updz (by simp) (nl hr a0), updz (by simp) (nl hr a3), updz (by simp) (nl hr a3),
      updz (by simp) (nl hr a3), updz (by simp) (nl hr a4), updz hz (nl hr a4)]
  have r6 : ∀ r, r ≠ a0 → r ≠ a3 → r ≠ a4 → reg m6 r = g r := fun r h0 h3 h4 => by
    rw [u6.regs, updz (by simp) h0, updz (by simp) h3, updz (by simp) h3, updz (by simp) h3,
      updz (by simp) h4, updz hz h4]
  have r6a0 : reg m6 a0 = regionHi s.kind := by rw [u6.regs, upd_a0]
  have r6a4 : reg m6 a4 = s.kind.zeroExtend 32 <<< 2 := by
    rw [u6.regs]; simp +decide only [upd, ↓reduceIte]; rw [hs10, s10_idx]
  have hc6 := (c6.inv.code env code0).parse
  -- 0x248: put the address back together.
  obtain ⟨m7, d7, u7⟩ := u6'.lw hc6 ip_at_248 (off' := 0x24A) (by decide)
    (by rw [r6 _ (by decide) (by decide) (by decide), ctx.inv.sp]; exact aligned_add env.hG (k := 0x10) (by decide))
  obtain ⟨m8, d8, u8⟩ := u7.aluImm hc6 ip_at_24a (off' := 0x24C) (by decide)
  obtain ⟨m9, d9, u9⟩ := u8.aluImm hc6 ip_at_24c (off' := 0x250) (by decide)
  obtain ⟨m10, d10, u10⟩ := u9.alu hc6 ip_at_250 (off' := 0x252) (by decide)
  obtain ⟨m11, d11, u11⟩ := u10.alu hc6 ip_at_252 (off' := 0x256) (by decide)
  have c11 := c6.regs (g' := reg m11) fun r hr => by
    rw [u11.regs, updz (by simp) (nl hr a5), updz (by simp) (nl hr a3), updz (by simp) (nl hr a5),
      updz (by simp) (nl hr a3), updz c6.inv.zero (nl hr a3)]
  have r11 : ∀ r, r ≠ a3 → r ≠ a5 → reg m11 r = reg m6 r := fun r h3 h5 => by
    rw [u11.regs, updz (by simp) h5, updz (by simp) h3, updz (by simp) h5, updz (by simp) h3,
      updz c6.inv.zero h3]
  have r11a3 : reg m11 a3 = s.addr := by
    rw [u11.regs]; simp +decide only [upd, ↓reduceIte]
    rw [r6 s7 (by decide) (by decide) (by decide), hs7, r6 sp (by decide) (by decide) (by decide),
      ctx.inv.sp, h10, a_rebuild]
  have r11a5 : reg m11 a5 = s.addr + s.len := by
    rw [u11.regs]; simp +decide only [upd, ↓reduceIte]
    rw [r6 s7 (by decide) (by decide) (by decide), hs7, r6 sp (by decide) (by decide) (by decide),
      ctx.inv.sp, h10, a_rebuild, r6 s3 (by decide) (by decide) (by decide), hs3]; rfl
  have hc11 := (c11.inv.code env code0).parse
  have pre11 : Steps m m11 := .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7
    (.cons d8 (.cons d9 (.cons d10 (.single d11))))))))))
  have h6' : reg m11 (16 : Fin 32) = 9 := by
    rw [r11 _ (by decide) (by decide), r6 _ (by decide) (by decide) (by decide), ha6]
  by_cases f4 : (regionHi s.kind).ult (s.addr + s.len) = true
  · obtain ⟨m12, d12, u12⟩ := u11.self.taken hc11 0x418 ip_at_256 (by decide)
      (by rw [r11 a0 (by decide) (by decide), r6a0, r11a5]; exact f4)
    exact CkPost.pre (pre11.trans (.single d12)) _ (c11.e418 env code0 u12 (by rw [h6'])
      (by simp [checkSegW, f1, f2, f3, f4] <;> rfl))
  have f4' := Bool.eq_false_iff.mpr f4
  obtain ⟨m12, d12, u12⟩ := u11.self.notTaken hc11 0x25A ip_at_256 (by decide)
    (by rw [r11 a0 (by decide) (by decide), r6a0, r11a5]; exact f4')
  by_cases f5 : (s.addr + s.len).ult s.addr = true
  · obtain ⟨m13, d13, u13⟩ := u12.taken hc11 0x418 ip_at_25a (by decide)
      (by rw [r11a5, r11a3]; exact f5)
    exact CkPost.pre (pre11.trans (.cons d12 (.single d13))) _ (c11.e418 env code0 u13 (by rw [h6'])
      (by simp [checkSegW, f1, f2, f3, f4', f5] <;> rfl))
  have f5' := Bool.eq_false_iff.mpr f5
  obtain ⟨m13, d13, u13⟩ := u12.notTaken hc11 0x25E ip_at_25a (by decide)
    (by rw [r11a5, r11a3]; exact f5')
  obtain ⟨m14, d14, u14⟩ := u13.lui hc11 ip_at_25e (off' := 0x262) (by decide)
  obtain ⟨m15, d15, u15⟩ := u14.aluImm hc11 ip_at_262 (off' := 0x266) (by decide)
  obtain ⟨m16, d16, u16⟩ := u15.alu hc11 ip_at_266 (off' := 0x268) (by decide)
  have r16a4 : upd (upd (upd (reg m11) a0 0x3FCC5000) a0 (aluEval .add (upd (reg m11) a0 0x3FCC5000 a0) 0x250)) a4
      (aluEval .add (upd (upd (reg m11) a0 0x3FCC5000) a0 (aluEval .add (upd (reg m11) a0 0x3FCC5000 a0) 0x250) a4)
        (upd (upd (reg m11) a0 0x3FCC5000) a0 (aluEval .add (upd (reg m11) a0 0x3FCC5000 a0) 0x250) a0)) a4 =
      aluEval .add (s.kind.zeroExtend 32 <<< 2) (aluEval .add 0x3FCC5000 0x250) := by
    rw [upd_same (by decide), upd_a0, updz (by simp) (by decide), updz c11.inv.zero (by decide), upd_a0,
      r11 a4 (by decide) (by decide), r6a4]
  obtain ⟨m17, d17, u17⟩ := u16.lw hc11 ip_at_268 (off' := 0x26A) (by decide)
    (by rw [r16a4]; exact tbl_al_lo _ ctx.kd)
  rw [r16a4, tbl_lo _ (c11.inv.code env code0).starts _ ctx.kd] at u17
  have c17 := c11.regs (g' := reg m17) fun r hr => by
    rw [u17.regs, updz (by simp) (nl hr a0), updz (by simp) (nl hr a4), updz (by simp) (nl hr a0),
      updz c11.inv.zero (nl hr a0)]
  have r17 : ∀ r, r ≠ a0 → r ≠ a4 → reg m17 r = reg m11 r := fun r h0 h4 => by
    rw [u17.regs, updz (by simp) h0, updz (by simp) h4, updz (by simp) h0, updz c11.inv.zero h0]
  have hc17 := (c17.inv.code env code0).parse
  have pre17 : Steps m m17 := pre11.trans (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.cons d16
    (.single d17))))))
  by_cases f6 : s.addr.ult (regionLo s.kind) = true
  · obtain ⟨m18, d18, u18⟩ := u17.self.taken hc17 0x418 ip_at_26a (by decide)
      (by rw [r17 a3 (by decide) (by decide), r11a3, u17.regs a0, upd_a0]; exact f6)
    exact CkPost.pre (pre17.trans (.single d18)) _ (c17.e418 env code0 u18
      (by rw [r17 _ (by decide) (by decide), h6'])
      (by simp [checkSegW, f1, f2, f3, f4', f5', f6] <;> rfl))
  have f6' := Bool.eq_false_iff.mpr f6
  obtain ⟨m18, d18, u18⟩ := u17.self.notTaken hc17 0x26E ip_at_26a (by decide)
    (by rw [r17 a3 (by decide) (by decide), r11a3, u17.regs a0, upd_a0]; exact f6')
  have q : ∀ r, r ≠ a0 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg m17 r = g r := fun r h0 h3 h4 h5 => by
    rw [r17 r h0 h4, r11 r h3 h5, r6 r h0 h3 h4]
  exact CkPost.pre (pre17.trans (.single d18)) _ (lp_ck3 env code0 c17 u18 (s10_byte X s.kind)
    (by rw [r17 a3 (by decide) (by decide), r11a3])
    (by rw [q _ (by decide) (by decide) (by decide) (by decide), hs4])
    (by rw [q _ (by decide) (by decide) (by decide) (by decide), hs3])
    (by rw [q _ (by decide) (by decide) (by decide) (by decide), hs10])
    (by rw [q _ (by decide) (by decide) (by decide) (by decide), ha1])
    (by rw [q _ (by decide) (by decide) (by decide) (by decide), ha6])
    (by rw [q _ (by decide) (by decide) (by decide) (by decide), ha2]) f1 f2 f3 f4' f5' f6')

theorem kind_ff : ∀ k : BitVec 8, (3 : BitVec 8).ult k = false →
    branchTaken .beq (aluEval .add (k.zeroExtend 32) 0xFFFFFF01) 0 = false := by decide

/-- **A segment's checks**, from offset 0x2CA: the segment `read_segment`
read is in registers and frame words; the loop checks it as `checkSegW`
does and stores it, or returns its error. -/
theorem lp_check (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (ctx : CkCtx R G ptr len out ilen M0 f0 sv cnt entry segs pos prev Ms gs s pos' My g)
    {m : Machine} (st : St My P m 0x2CA g) (hl : memLoad32 My (G + 0x128) = s.len)
    (ho : memLoad32 My (G + 4) = s.off) (hs7 : g s7 = s.addr) (hs6 : g s6 = s.kind.zeroExtend 32) :
    CkPost P R G ptr len out ilen M0 f0 sv cnt entry segs s pos' m (checkSegW ilen prev s) := by
  have hc := (ctx.inv.code env code0).parse
  have hz := ctx.inv.zero
  have sp0 := ctx.inv.sp
  obtain ⟨m1, d1, u1⟩ := st.lw hc ip_at_2ca (off' := 0x2CE) (by decide)
    (by rw [sp0]; exact aligned_add env.hG (k := 0x128) (by decide))
  obtain ⟨m2, d2, u2⟩ := u1.lw hc ip_at_2ce (off' := 0x2D0) (by decide)
    (by rw [updz hz (by decide), sp0]; exact aligned_add env.hG (k := 0) (by decide))
  obtain ⟨m3, d3, u3⟩ := u2.aluImm hc ip_at_2d0 (off' := 0x2D4) (by decide)
  obtain ⟨m4, d4, u4⟩ := u3.alu hc ip_at_2d4 (off' := 0x2D8) (by decide)
  obtain ⟨m5, d5, u5⟩ := u4.aluImm hc ip_at_2d8 (off' := 0x2DC) (by decide)
  have c5 := ctx.regs (g' := reg m5) fun r hr => by
    rw [u5.regs, updz (by simp) (nl hr a0), updz (by simp) (nl hr s10), updz (by simp) (nl hr a0),
      updz (by simp) (nl hr a0), updz hz (nl hr s3)]
  have r5 : ∀ r, r ≠ a0 → r ≠ s3 → r ≠ s10 → reg m5 r = g r := fun r h0 h3 h10 => by
    rw [u5.regs, updz (by simp) h0, updz (by simp) h10, updz (by simp) h0, updz (by simp) h0, updz hz h3]
  generalize hX : memLoad32 My (G + 0) = X
  have r5s10 : reg m5 s10 = aluEval .or (aluEval .and X 0xFFFFFF00) (s.kind.zeroExtend 32) := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]; rw [sp0, hs6]
    rw [show (0x0 : Word) = 0 from rfl] at hX; rw [hX]
  have r5a0 : reg m5 a0 = aluEval .srl s.addr 8 := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]; rw [hs7]
  have r5s3 : reg m5 s3 = s.len := by
    rw [u5.regs]; simp +decide only [upd, ↓reduceIte]; rw [sp0]; exact hl
  have sp5 : reg m5 sp = G := by rw [r5 _ (by decide) (by decide) (by decide), sp0]
  have hc5 := (c5.inv.code env code0).parse
  obtain ⟨m6, d6, u6⟩ := u5.self.sw hc5 ip_at_2dc (off' := 0x2DE) (by decide)
    (by rw [sp5]; exact aligned_add env.hG (k := 0x10) (by decide))
  rw [sp5, r5a0] at u6
  have c6 := c5.mem env 0x10 (aluEval .srl s.addr 8) (Or.inr ⟨by omega, by omega⟩)
  have hc6 := (c6.inv.code env code0).parse
  obtain ⟨m7, d7, u7⟩ := u6.sw hc6 ip_at_2de (off' := 0x2E0) (by decide)
    (by rw [sp5]; exact aligned_add env.hG (k := 0) (by decide))
  rw [sp5, r5s10, show G + (0x0 : Word) = G + BitVec.ofNat 32 0 from rfl] at u7
  have c7 := c6.mem env 0 (aluEval .or (aluEval .and X 0xFFFFFF00) (s.kind.zeroExtend 32)) (Or.inl (by omega))
  have hc7 := (c7.inv.code env code0).parse
  obtain ⟨m8, d8, u8⟩ := u7.lw hc7 ip_at_2e0 (off' := 0x2E2) (by decide)
    (by rw [sp5]; exact aligned_add env.hG (k := 4) (by decide))
  have v8 : memLoad32 (memStore32 (memStore32 My (G + 0x10) (aluEval .srl s.addr 8)) (G + BitVec.ofNat 32 0)
      (aluEval .or (aluEval .and X 0xFFFFFF00) (s.kind.zeroExtend 32))) (G + 4) = s.off := by
    rw [show G + (4 : Word) = G + BitVec.ofNat 32 4 from rfl,
      memLoad32_store32_sep (sep_offsets G (c := 0) (n := 4) (d := 4) (k := 4) (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (show Sep (G + 0x10) 4 (G + BitVec.ofNat 32 4) 4 from
        sep_offsets G (c := 0x10) (n := 4) (d := 4) (k := 4) (by omega) (by omega) (by omega))]
    exact ho
  rw [sp5, v8] at u8
  obtain ⟨m9, d9, u9⟩ := u8.jump hc7 ip_at_2e2 (off' := 0x21A) (by decide)
    (by rw [u8.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0x21A (by decide)))
  have c9 := c7.regs (g' := reg m9) fun r hr => by
    rw [u9.regs, updz c5.inv.zero (nl hr s4)]
  have r9 : ∀ r, r ≠ s4 → reg m9 r = reg m5 r := fun r h4 => by rw [u9.regs, updz c5.inv.zero h4]
  have r9s4 : reg m9 s4 = s.off := by rw [u9.regs, upd_same (by decide)]
  have hc9 := (c9.inv.code env code0).parse
  obtain ⟨m10, d10, u10⟩ := u9.self.aluImm hc9 ip_at_21a (off' := 0x21E) (by decide)
  rw [r9 s10 (by decide), r5s10, s10_lo] at u10
  obtain ⟨m11, d11, u11⟩ := u10.aluImm hc9 ip_at_21e (off' := 0x222) (by decide)
  obtain ⟨m12, d12, u12⟩ := u11.notTaken hc9 0x224 ip_at_222 (by decide) (by
    rw [upd_a0, upd_same (by decide), show upd (upd (reg m9) a2 (s.kind.zeroExtend 32)) a0
      (aluEval .add (s.kind.zeroExtend 32) 0xFFFFFF01) x0 = 0 from rfl]
    exact kind_ff _ ctx.kd)
  obtain ⟨m13, d13, u13⟩ := u12.aluImm hc9 ip_at_224 (off' := 0x226) (by decide)
  have c13 := c9.regs (g' := reg m13) fun r hr => by
    rw [u13.regs, updz (by simp) (nl hr (16 : Fin 32)), updz (by simp) (nl hr a0),
      updz c9.inv.zero (nl hr a2)]
  have r13 : ∀ r, r ≠ a0 → r ≠ a2 → r ≠ (16 : Fin 32) → reg m13 r = reg m9 r := fun r h0 h2 h6 => by
    rw [u13.regs, updz (by simp) h6, updz (by simp) h0, updz c9.inv.zero h2]
  have r13a6 : reg m13 (16 : Fin 32) = 9 := by
    rw [u13.regs, upd_same (by decide)]; show upd _ a0 _ 0 + 9 = 9; rfl
  have r13a2 : reg m13 a2 = s.kind.zeroExtend 32 := by
    rw [u13.regs, updz (by simp) (by decide), updz (by simp) (by decide), upd_same (by decide)]
  have r13s3 : reg m13 s3 = s.len := by
    rw [r13 _ (by decide) (by decide) (by decide), r9 _ (by decide), r5s3]
  have r13s4 : reg m13 s4 = s.off := by rw [r13 _ (by decide) (by decide) (by decide), r9s4]
  have hc13 := (c13.inv.code env code0).parse
  have pre13 : Steps m m13 := .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7
    (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.single d13))))))))))))
  by_cases f1 : s.len = 0#32
  · obtain ⟨m14, d14, u14⟩ := u13.self.taken hc13 0x418 ip_at_226 (by decide)
      (by rw [r13s3, c13.inv.zero, f1]; rfl)
    exact CkPost.pre (pre13.trans (.single d14)) _ (c13.e418 env code0 u14 (by rw [r13a6])
      (by unfold checkSegW; rw [show (s.len == 0) = true from beq_iff_eq.mpr f1]; rfl))
  obtain ⟨m14, d14, u14⟩ := u13.self.notTaken hc13 0x22A ip_at_226 (by decide)
    (by rw [r13s3, c13.inv.zero]; exact Bool.eq_false_iff.mpr fun h => f1 (beq_iff_eq.mp h))
  obtain ⟨m15, d15, u15⟩ := u14.alu hc13 ip_at_22a (off' := 0x22E) (by decide)
  rw [r13s4, r13s3, show aluEval .add s.off s.len = s.off + s.len from rfl] at u15
  have c15 := c13.setR a1 (v := s.off + s.len)
  have r15 : ∀ r, r ≠ a1 → upd (reg m13) a1 (s.off + s.len) r = reg m13 r := fun r h => updz c13.inv.zero h
  have hc15 := (c15.inv.code env code0).parse
  by_cases f2 : (s.off + s.len).ult s.off = true
  · obtain ⟨m16, d16, u16⟩ := u15.taken hc15 0x300 ip_at_22e (by decide)
      (by rw [upd_same (by decide), r15 s4 (by decide), r13s4]; exact f2)
    obtain ⟨m17, d17, u17⟩ := u16.aluImm hc15 ip_at_300 (off' := 0x302) (by decide)
    obtain ⟨m18, d18, u18⟩ := u17.jump hc15 ip_at_302 (off' := 0x418) (by decide)
      (by rw [u17.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0x418 (by decide)))
    exact CkPost.pre (pre13.trans (.cons d14 (.cons d15 (.cons d16 (.cons d17 (.single d18)))))) _
      (c15.setR (16 : Fin 32) |>.e418 env code0 u18 (by rw [upd_same (by decide)])
        (by simp [checkSegW, f1, f2] <;> rfl))
  have f2' := Bool.eq_false_iff.mpr f2
  obtain ⟨m16, d16, u16⟩ := u15.notTaken hc15 0x232 ip_at_22e (by decide)
    (by rw [upd_same (by decide), r15 s4 (by decide), r13s4]; exact f2')
  have hs1 : upd (reg m13) a1 (s.off + s.len) s1 = ilen := c15.inv.s1
  by_cases f3 : ilen.ult (s.off + s.len) = true
  · obtain ⟨m17, d17, u17⟩ := u16.taken hc15 0x418 ip_at_232 (by decide)
      (by rw [hs1, upd_same (by decide)]; exact f3)
    exact CkPost.pre (pre13.trans (.cons d14 (.cons d15 (.cons d16 (.single d17))))) _
      (c15.e418 env code0 u17 (by rw [r15 _ (by decide), r13a6])
        (by simp [checkSegW, f1, f2', f3] <;> rfl))
  have f3' := Bool.eq_false_iff.mpr f3
  obtain ⟨m17, d17, u17⟩ := u16.notTaken hc15 0x236 ip_at_232 (by decide)
    (by rw [hs1, upd_same (by decide)]; exact f3')
  have q : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ (16 : Fin 32) → r ≠ s4 →
      upd (reg m13) a1 (s.off + s.len) r = reg m5 r := fun r h0 h1 h2 h6 h4 => by
    rw [r15 r h1, r13 r h0 h2 h6, r9 r h4]
  exact CkPost.pre (pre13.trans (.cons d14 (.cons d15 (.cons d16 (.single d17))))) _
    (lp_ck2 env code0 c15 u17
      (by rw [q _ (by decide) (by decide) (by decide) (by decide) (by decide),
        r5 _ (by decide) (by decide) (by decide), hs7])
      (by rw [r15 _ (by decide), r13s4]) (by rw [r15 _ (by decide), r13s3])
      (by rw [q _ (by decide) (by decide) (by decide) (by decide) (by decide), r5s10])
      (upd_same (by decide)) (by rw [r15 _ (by decide), r13a6]) (by rw [r15 _ (by decide), r13a2])
      (by rw [show G + 0x10 = G + BitVec.ofNat 32 0x10 from rfl,
          memLoad32_store32_sep (sep_offsets G (c := 0) (n := 4) (d := 0x10) (k := 4) (by omega) (by omega)
            (by omega)), memLoad32_store32_same])
      f1 f2' f3')

end Check

end C3.RV32
