import C3BootProofs.Proofs.AcceptIndexSetup

/-!
# `boot_main`'s first closure: the index stage reads the lengths

The loop at 0x3FE reads the part's `count + 2` lengths from the index with
`Reader::u32` into the buffer at `B + 0x5920`, and leaves with code 5 when a
length is 0 or more than `maxDocLen`.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3

set_option maxRecDepth 100000

theorem acx_u32some {M : Word → BitVec 8} {out self p e : Word}
    (hR : bytesResult (memLoad32 M self) (memLoad32 M (self + 4)) (memLoad32 M (self + 8)) 4 = some (p, e)) :
    Cur.u32Mem M out self out = 0 ∧ memLoad32 (Cur.u32Mem M out self) (out + 4) = memLoad32 M p ∧
    ∀ x, x ≠ out → Sep (out + 4) 4 x 1 → Cur.u32Mem M out self x = memStore32 M (self + 8) e x := by
  unfold Cur.u32Mem; rw [hR]; dsimp only
  refine ⟨memStore8_same _ _ _, ?_, fun x h1 h2 => ?_⟩
  · rw [memLoad32_store8_sep (by
      have := sep_offsets out (c := 0) (n := 1) (d := 4) (k := 4) (by omega) (by omega) (by omega)
      rwa [add_ofNat_zero] at this), memLoad32_store32_same]
  · rw [memStore8_ne h1, memStore32_get_sep h2]

theorem acx_ao (B : Word) (a c : Nat) (k : Word) (h : a + k.toNat = c) (hc : c < 2 ^ 32) :
    B + BitVec.ofNat 32 a + k = B + BitVec.ofNat 32 c := by
  rw [acx_fl k (by omega), h]

theorem acx_az (x : Word) : x + 0 = x := BitVec.add_zero x

theorem acx_fbD {f : Nat → BitVec 8} {a len i : Nat} (h : i < len) :
    (flashBytes f a len).getD i 0 = (f (a + i)).toNat := by
  simp only [flashBytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h, Option.map_some,
    Option.getD_some]

/-- The length word at `j` in the index buffer. -/
theorem acx_word {P : AcxP} {M : Word → BitVec 8} {c j : Nat}
    (buf : ∀ i, i < 4 * c + 8 →
      M (P.B + BitVec.ofNat 32 (0x5818 + i)) = P.flash ((reg P.n0 (24 : Fin 32)).toNat + 8 + i))
    (hlen : 8 + (4 * c + 8) ≤ (reg P.n0 (23 : Fin 32)).toNat) (hj : j < c + 2) :
    (memLoad32 M (P.B + BitVec.ofNat 32 (0x5818 + 4 * j))).toNat = acxW (acxTuf P) (8 + 4 * j) := by
  have b : ∀ k, k < 4 → (M (P.B + BitVec.ofNat 32 (0x5818 + 4 * j) + BitVec.ofNat 32 k)).toNat =
      (acxTuf P).getD (8 + 4 * j + k) 0 := fun k hk => by
    rw [add_ofNat_assoc, show 0x5818 + 4 * j + k = 0x5818 + (4 * j + k) by omega, buf (4 * j + k) (by omega),
      acxTuf, acx_fbD (by omega), show (reg P.n0 (24 : Fin 32)).toNat + 8 + (4 * j + k) =
        (reg P.n0 (24 : Fin 32)).toNat + (8 + 4 * j + k) by omega]
  have b0 := b 0 (by decide)
  rw [add_ofNat_zero, Nat.add_zero] at b0
  rw [memLoad32_toNat, show (1 : Word) = BitVec.ofNat 32 1 from rfl, show (2 : Word) = BitVec.ofNat 32 2 from rfl,
    show (3 : Word) = BitVec.ofNat 32 3 from rfl, b0, b 1 (by decide), b 2 (by decide), b 3 (by decide)]

theorem acx_rng_f {w : Word} (h1 : 1 ≤ w.toNat) (h2 : w.toNat ≤ 0x2800) :
    branchTaken .bltu (w + 0xFFFFD7FF) 0xFFFFD800 = false :=
  acx_bltu_f (by
    rw [BitVec.toNat_add, show (0xFFFFD7FF : Word).toNat = 0xFFFFD7FF from rfl,
      show (0xFFFFD800 : Word).toNat = 0xFFFFD800 from rfl]
    omega)

theorem acx_rng_lo {w : Word} (h : w.toNat < 1) :
    branchTaken .bltu (w + 0xFFFFD7FF) 0xFFFFD800 = true :=
  acx_bltu_t (by
    rw [BitVec.toNat_add, show (0xFFFFD7FF : Word).toNat = 0xFFFFD7FF from rfl,
      show (0xFFFFD800 : Word).toNat = 0xFFFFD800 from rfl]
    omega)

theorem acx_rng_hi {w : Word} (h : 0x2800 < w.toNat) :
    branchTaken .bltu (w + 0xFFFFD7FF) 0xFFFFD800 = true :=
  acx_bltu_t (by
    have := w.isLt
    rw [BitVec.toNat_add, show (0xFFFFD7FF : Word).toNat = 0xFFFFD7FF from rfl,
      show (0xFFFFD800 : Word).toNat = 0xFFFFD800 from rfl]
    omega)

theorem acx_dec4 {c j : Nat} (hj : j < c + 2) :
    BitVec.ofNat 32 (4 * (c + 2 - j)) + 0xFFFFFFFC = BitVec.ofNat 32 (4 * (c + 2 - (j + 1))) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFC : Word).toNat = 0xFFFFFFFC from rfl]
  omega

theorem acx_inc4 (j : Nat) : BitVec.ofNat 32 (4 * j) + 4 = BitVec.ofNat 32 (4 * (j + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (4 : Word).toNat = 4 from rfl,
    Nat.mod_add_mod, show 4 * (j + 1) = 4 * j + 4 by omega]

/-- From 0x400: point `a0` at the result and `a1` at the reader. -/
def acxL1 : List BInstr :=
  [.lui a0 0x2000, .aluImm .add a0 a0 0xFFFFF860, .alu .add a0 a0 sp, .lui a1 0x2000,
   .aluImm .add a1 a1 0xFFFFFFDC, .alu .add a1 a1 sp]

theorem acxL1_end : blockEnd bootMainClosure0Code 0x400 acxL1 = some 0x410 := by decide

/-- From 0x418: load the result's tag. -/
def acxL2 : List BInstr := [.lbu a0 (26 : Fin 32) 0x550]

theorem acxL2_end : blockEnd bootMainClosure0Code 0x418 acxL2 = some 0x41C := by decide

/-- From 0x41E: store the length and check its bounds. -/
def acxL3 : List BInstr :=
  [.lw a0 (26 : Fin 32) 0x554, .sw (9 : Fin 32) a0 0x0, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4,
   .alu .add a0 a0 (19 : Fin 32), .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFFC]

theorem acxL3_end : blockEnd bootMainClosure0Code 0x41E acxL3 = some 0x42A := by decide

set_option maxHeartbeats 4000000 in
/-- One pass of the loop at 0x3FE: read length `j`. -/
theorem acx_it {P : AcxP} (K : AcxK P) {c j : Nat} {n : Machine} (L : AcxLp P c j n) (hj : j < c + 2) :
    AcxTo P n (AcxLp P c (j + 1)) := by
  have F := K.F
  have hFl := F.lo; have hFh := F.hi
  have hc := L.hc
  have A := L.ac
  have hz := L.st.zero
  obtain ⟨n1, e1, t1⟩ := L.st.notTaken (A.code K) 0x400 ac_at_3fe (by decide)
    (acx_beq_f (by rw [L.s0, hz]; exact acx_ofNat_ne (c := 0) (by omega) (by decide) (by omega)))
  have A1 := A.st t1
  have t1' := acx_st t1
  have hz1 := t1'.zero
  have rsp1 := A1.rsp K
  obtain ⟨n2, c2, t2, A2, m2, g2⟩ := acx_blk K A1 t1' acxL1 acxL1_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl (by decide)
  have e12 : ∀ q, acxS q = true → reg n2 q = reg n q := fun q hq => by
    rw [g2, runBlock_reg _ _ _ q hz1 (by simp only [acxL1]; revert hq; revert q; decide), t1.regs]
  have ha0 : reg n2 a0 = P.B + BitVec.ofNat 32 0x52B0 := by
    rw [g2]; simp +decide only [runBlock, BInstr.run, acxL1, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    exact acx_k' rsp1 _ (by decide)
  have ha1 : reg n2 a1 = P.B + BitVec.ofNat 32 0x5A2C := by
    rw [g2]; simp +decide only [runBlock, BInstr.run, acxL1, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    exact acx_k' rsp1 _ (by decide)
  have m2' : n2.mem = n.mem := by rw [m2, t1.mem]
  obtain ⟨n3, c3, t3, A3, kk3, fr3⟩ := acx_cu32 K A2 t2 ac_at_410 ac_at_414 (by decide) (by decide)
    (len := 4 * c + 8) (by omega) ha0 ha1 (by rw [m2']; exact L.rp) (by rw [m2']; exact L.rl)
  have hR : bytesResult (memLoad32 n2.mem (P.B + BitVec.ofNat 32 0x5A2C))
      (memLoad32 n2.mem (P.B + BitVec.ofNat 32 0x5A2C + 4)) (memLoad32 n2.mem (P.B + BitVec.ofNat 32 0x5A2C + 8)) 4 =
      some (P.B + BitVec.ofNat 32 0x5818 + BitVec.ofNat 32 (4 * j), BitVec.ofNat 32 (4 * j) + 4) := by
    rw [m2', show P.B + BitVec.ofNat 32 0x5A2C + 4 = P.B + BitVec.ofNat 32 0x5A30 from add_ofNat_assoc _ _ _,
      show P.B + BitVec.ofNat 32 0x5A2C + 8 = P.B + BitVec.ofNat 32 0x5A34 from add_ofNat_assoc _ _ _,
      L.rp, L.rl, L.rpos]
    exact acx_br (by
      rw [acx_toNat_ofNat (v := 4 * j) (by omega), acx_toNat_ofNat (v := 4 * c + 8) (by omega),
        show (4 : Word).toNat = 4 from rfl]
      omega)
  obtain ⟨u0, u4, ur⟩ := acx_u32some (out := P.B + BitVec.ofNat 32 0x52B0) hR
  rw [show P.B + BitVec.ofNat 32 0x52B0 + 4 = P.B + BitVec.ofNat 32 0x52B4 from add_ofNat_assoc _ _ _] at u4
  have o0 : n3.mem (P.B + BitVec.ofNat 32 0x52B0) = 0 := by
    rw [fr3 _ (by rw [F.at _ (by decide)]; omega)]; exact u0
  have o4 : memLoad32 n3.mem (P.B + BitVec.ofNat 32 0x52B4) =
      memLoad32 n.mem (P.B + BitVec.ofNat 32 (0x5818 + 4 * j)) := by
    rw [acx_wz F (e := 0x52B4) (by decide) fun x h1 h2 => fr3 x (by omega), u4, m2', add_ofNat_assoc]
  have mx3 : ∀ x : Word, (x.toNat < P.B.toNat + 0x3A20 ∨ P.B.toNat + 0x3A50 ≤ x.toNat) →
      (x.toNat < P.B.toNat + 0x52B0 ∨ P.B.toNat + 0x52B8 ≤ x.toNat) →
      n3.mem x = memStore32 n.mem (P.B + BitVec.ofNat 32 0x5A34) (BitVec.ofNat 32 (4 * j) + 4) x :=
    fun x h1 h2 => by
      rw [fr3 x h1, ur x (fun e => by rw [e, F.at _ (by decide)] at h2; omega)
        (by rw [acx_ao _ 0x52B0 0x52B4 4 (by decide) (by decide)]; exact acx_sepR F (by decide) (by omega)), m2',
        show P.B + BitVec.ofNat 32 0x5A2C + 8 = P.B + BitVec.ofNat 32 0x5A34 from add_ofNat_assoc _ _ _]
  have hz3 := t3.zero
  obtain ⟨n4, c4, t4, A4, m4, g4⟩ := acx_blk K A3 t3 acxL2 acxL2_end ⟨trivial, trivial⟩ rfl (by decide)
  have r3 : ∀ q, acxS q = true → reg n3 q = reg n q := fun q hq => (kk3 q hq).trans (e12 q hq)
  have a04 : reg n4 a0 = 0 := by
    rw [g4]; simp +decide only [runBlock, BInstr.run, acxL2, upd, ↓reduceIte]
    rw [r3 _ (by decide), L.s10, acx_ao _ 0x4D60 0x52B0 0x550 (by decide) (by decide), o0]; rfl
  obtain ⟨n5, e5, t5⟩ := t4.notTaken (A4.code K) 0x41E ac_at_41c (by decide)
    (acx_bne_f (by rw [a04, t4.zero]))
  have A5 := A4.st t5
  have t5' := acx_st t5
  have hz5 := t5'.zero
  have m5 : n5.mem = n3.mem := by rw [t5.mem, m4]
  have r5 : ∀ q, acxS q = true → reg n5 q = reg n q := fun q hq => by
    rw [t5.regs, g4, runBlock_reg _ _ _ q hz3 (by simp only [acxL2]; revert hq; revert q; decide), r3 q hq]
  have r26 : reg n5 (26 : Fin 32) = P.B + BitVec.ofNat 32 0x4D60 := (r5 _ (by decide)).trans L.s10
  have r9 : reg n5 (9 : Fin 32) = P.B + BitVec.ofNat 32 (0x5920 + 4 * j) := (r5 _ (by decide)).trans L.s1
  obtain ⟨n6, c6, u6⟩ := t5'.block acxL3 (A5.code K) acxL3_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acxL3]
    simp +decide only [upd, ↓reduceIte, and_true]
    rw [r26, r9, acx_ao _ 0x4D60 0x52B4 0x554 (by decide) (by decide), acx_az]
    exact ⟨acx_al F (by decide) (by decide), acx_swok F (by omega) (by omega)⟩)
  have g6 : ∀ q, reg n6 q = (runBlock acxL3 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
  have t6 : St n6.mem AC n6 0x42A (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have hw : (memLoad32 n3.mem (P.B + BitVec.ofNat 32 0x52B4)).toNat = acxW (acxTuf P) (8 + 4 * j) := by
    rw [o4]; exact acx_word L.buf L.hlen hj
  have m6 : n6.mem = memStore32 n3.mem (P.B + BitVec.ofNat 32 (0x5920 + 4 * j))
      (memLoad32 n3.mem (P.B + BitVec.ofNat 32 0x52B4)) := by
    rw [u6.mem]; simp only [runBlock, BInstr.run, acxL3]
    simp +decide only [upd, ↓reduceIte]
    rw [r26, r9, acx_ao _ 0x4D60 0x52B4 0x554 (by decide) (by decide), acx_az, m5]
  have k6 : ∀ q, acxS q = true → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → reg n6 q = reg n q := fun q hq h8 h9 => by
    rw [g6, runBlock_reg _ _ _ q hz5 (by simp only [acxL3]; revert hq h8 h9; revert q; decide), r5 q hq]
  have A6 : AcxC P n6 := A5.next
    (fun q hq => by
      rw [k6 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
        ← r5 q (by revert hq; revert q; decide)])
    (fun x _ h2 => by rw [m6, memStore32_get_sep (acx_sepR F (by omega) (by omega)), m5])
  have a06 : reg n6 a0 = memLoad32 n3.mem (P.B + BitVec.ofNat 32 0x52B4) + 0xFFFFD7FF := by
    rw [g6]; simp +decide only [runBlock, BInstr.run, acxL3, upd, ↓reduceIte]
    rw [r26, acx_ao _ 0x4D60 0x52B4 0x554 (by decide) (by decide), r5 _ (by decide), L.s3, m5]; rfl
  have s66 : reg n6 (22 : Fin 32) = 0xFFFFD800 :=
    (k6 _ (by decide) (by decide) (by decide)).trans L.s6
  have pre := c2.trans (c3.trans (c4.trans ((Steps.single e5).trans c6)))
  by_cases hlo : (memLoad32 n3.mem (P.B + BitVec.ofNat 32 0x52B4)).toNat < 1
  · obtain ⟨n7, e7, t7⟩ := t6.taken (A6.code K) 0x2AE ac_at_42a (by decide)
      (by rw [a06, s66]; exact acx_rng_lo hlo)
    exact AcxTo.pre ((Steps.single e1).trans (pre.trans (.single e7))) (acx_e5 K (A6.st t7) (acx_st t7))
  by_cases hhi : 0x2800 < (memLoad32 n3.mem (P.B + BitVec.ofNat 32 0x52B4)).toNat
  · obtain ⟨n7, e7, t7⟩ := t6.taken (A6.code K) 0x2AE ac_at_42a (by decide)
      (by rw [a06, s66]; exact acx_rng_hi hhi)
    exact AcxTo.pre ((Steps.single e1).trans (pre.trans (.single e7))) (acx_e5 K (A6.st t7) (acx_st t7))
  obtain ⟨n7, e7, t7⟩ := t6.notTaken (A6.code K) 0x42E ac_at_42a (by decide)
    (by rw [a06, s66]; exact acx_rng_f (by omega) (by omega))
  have t7' := acx_st t7
  obtain ⟨n8, e8, t8⟩ := t7'.jump ((A6.st t7).code K) ac_at_42e (off' := 0x3FE) (by decide) (by rw [t7'.pc]; decide)
  have rr : ∀ q, reg n8 q = reg n6 q := fun q => by rw [t8.regs, t7.regs]
  have W : ∀ e, e + 4 ≤ 0x5A70 → (0x3A50 ≤ e ∨ e + 4 ≤ 0x3A20) → (0x52B8 ≤ e ∨ e + 4 ≤ 0x52B0) →
      (0x5920 + 4 * j + 4 ≤ e ∨ e + 4 ≤ 0x5920 + 4 * j) →
      memLoad32 n8.mem (P.B + BitVec.ofNat 32 e) =
        memLoad32 (memStore32 n.mem (P.B + BitVec.ofNat 32 0x5A34) (BitVec.ofNat 32 (4 * j) + 4))
          (P.B + BitVec.ofNat 32 e) :=
    fun e he h1 h2 h3 => by
      rw [t8.mem, t7.mem, m6, memLoad32_store32_sep (acx_ss (by omega) he (by omega))]
      exact acx_wz F he fun x hx1 hx2 => mx3 x (by omega) (by omega)
  refine AcxTo.pre ((Steps.single e1).trans (pre.trans ((Steps.single e7).trans (.single e8))))
    (AcxTo.done ⟨acx_st t8, (A6.st t7).st t8, by omega, ?_, ?_, ?_, ?_, (rr _).trans s66, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, hc, L.hlen, L.hL, L.f0, L.f1, L.f2, L.f3, L.fv, L.fc⟩)
  · rw [rr, g6]; simp +decide only [runBlock, BInstr.run, acxL3, upd, ↓reduceIte]
    rw [r5 _ (by decide), L.s0]; exact acx_dec4 hj
  · rw [rr, g6]; simp +decide only [runBlock, BInstr.run, acxL3, upd, ↓reduceIte]
    rw [r9]
    exact acx_ao _ _ _ 4 (by rw [show (4 : Word).toNat = 4 from rfl]; omega) (by omega)
  · rw [rr, k6 _ (by decide) (by decide) (by decide)]; exact L.s2
  · rw [rr, k6 _ (by decide) (by decide) (by decide)]; exact L.s3
  · rw [rr, k6 _ (by decide) (by decide) (by decide)]; exact L.s10
  · rw [W 0x5A2C (by decide) (by omega) (by omega) (by omega),
      memLoad32_store32_sep (acx_ss (by decide) (by decide) (by decide))]; exact L.rp
  · rw [W 0x5A30 (by decide) (by omega) (by omega) (by omega),
      memLoad32_store32_sep (acx_ss (by decide) (by decide) (by decide))]; exact L.rl
  · rw [W 0x5A34 (by decide) (by omega) (by omega) (by omega), memLoad32_store32_same]; exact acx_inc4 j
  · rw [W 0x5A28 (by decide) (by omega) (by omega) (by omega),
      memLoad32_store32_sep (acx_ss (by decide) (by decide) (by decide))]; exact L.cnt
  · rw [W 0x3A80 (by decide) (by omega) (by omega) (by omega),
      memLoad32_store32_sep (acx_ss (by decide) (by decide) (by decide))]; exact L.w30
  · intro i hi
    have hx := F.at (0x5818 + i) (by omega)
    rw [t8.mem, t7.mem, m6, memStore32_get_sep (acx_sepR F (by omega) (by omega)), mx3 _ (by omega) (by omega),
      memStore32_get_sep (acx_sepR F (by decide) (by omega))]
    exact L.buf i hi
  · intro i hi
    rcases Nat.lt_or_ge i j with h | h
    · rw [W (0x5920 + 4 * i) (by omega) (by omega) (by omega) (by omega),
        memLoad32_store32_sep (acx_ss (by omega) (by omega) (by omega))]
      exact L.idx i h
    · rw [show i = j by omega, t8.mem, t7.mem, m6, memLoad32_store32_same]; exact hw
  · intro i hi
    rcases Nat.lt_or_ge i j with h | h
    · exact L.ok i h
    · rw [show i = j by omega, ← hw]; exact ⟨by omega, by omega⟩

theorem acx_loop {P : AcxP} (K : AcxK P) {c : Nat} :
    ∀ (k j : Nat) {n : Machine}, j + k = c + 2 → AcxLp P c j n → AcxTo P n (AcxLp P c (c + 2))
  | 0, _, _, h, L => AcxTo.done (h ▸ L)
  | k + 1, j, _, h, L => (acx_it K L (by omega)).bind fun _ L' => acx_loop K k (j + 1) (by omega) L'

/-- The state at 0x440: the buffer at `B + 0x5920` holds the part's
`count + 2` lengths, each from 1 to `maxDocLen`, and the count after them. -/
structure AcxS3 (P : AcxP) (c : Nat) (n : Machine) : Prop where
  st : St n.mem AC n 0x440 (reg n)
  ac : AcxC P n
  s2 : reg n (18 : Fin 32) = BitVec.ofNat 32 c
  s10 : reg n (26 : Fin 32) = P.B + BitVec.ofNat 32 0x4D60
  cnt : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x5A28) = BitVec.ofNat 32 c
  w30 : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x3A80) = 0x6800 + memLoad32 P.n0.mem (P.B + BitVec.ofNat 32 0x3A84)
  idx : ∀ i, i < c + 2 →
    (memLoad32 n.mem (P.B + BitVec.ofNat 32 (0x5920 + 4 * i))).toNat = acxW (acxTuf P) (8 + 4 * i)
  ok : ∀ i, i < c + 2 → 1 ≤ acxW (acxTuf P) (8 + 4 * i) ∧ acxW (acxTuf P) (8 + 4 * i) ≤ 0x2800
  hc : c ≤ 64
  hlen : 8 + (4 * c + 8) ≤ (reg P.n0 (23 : Fin 32)).toNat
  hL : (reg P.n0 (23 : Fin 32)).toNat ≤ 0x60000
  f0 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 0)).toNat = 0x43
  f1 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 1)).toNat = 0x33
  f2 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 2)).toNat = 0x54
  f3 : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 3)).toNat = 0x55
  fv : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 4)).toNat +
    256 * (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 5)).toNat = 2
  fc : (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 6)).toNat +
    256 * (P.flash ((reg P.n0 (24 : Fin 32)).toNat + 7)).toNat = c

theorem acx_lpx {P : AcxP} (K : AcxK P) {c : Nat} {n : Machine} (L : AcxLp P c (c + 2) n) :
    AcxTo P n (AcxS3 P c) := by
  have A := L.ac
  obtain ⟨n1, e1, t1⟩ := L.st.taken (A.code K) 0x440 ac_at_3fe (by decide)
    (acx_beq_t (by rw [L.s0, L.st.zero, Nat.sub_self, Nat.mul_zero]; rfl))
  refine ⟨n1, .single e1, .inr ⟨acx_st t1, A.st t1, (t1.regs _).trans L.s2, (t1.regs _).trans L.s10,
    by rw [t1.mem]; exact L.cnt, by rw [t1.mem]; exact L.w30, fun i h => by rw [t1.mem]; exact L.idx i h,
    L.ok, L.hc, L.hlen, L.hL, L.f0, L.f1, L.f2, L.f3, L.fv, L.fc⟩⟩

/-- From 0x2A6 to 0x440: check the part's header and read its lengths. -/
theorem acx_to440 {P : AcxP} (K : AcxK P) {n : Machine} (A : AcxC P n) (s : St n.mem AC n 0x2A6 (reg n)) :
    AcxTo P n (fun n' => ∃ c, AcxS3 P c n') :=
  (acx_h1 K A s).bind fun _ S1 => (acx_h2 K S1).bind fun _ M1 => (acx_h3 K M1).bind fun n3 S2 =>
    (acx_h4 K S2).bind fun _ L => (acx_loop K (c := (reg n3 (18 : Fin 32)).toNat)
      ((reg n3 (18 : Fin 32)).toNat + 2) 0 (by omega) L).bind fun _ L' =>
        (acx_lpx K L').bind fun n' S3 => AcxTo.done ⟨_, S3⟩

end C3.RV32.Ac
