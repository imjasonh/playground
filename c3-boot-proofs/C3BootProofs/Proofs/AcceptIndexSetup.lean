import C3BootProofs.Proofs.AcceptIndexHdr

/-!
# `boot_main`'s first closure: the index stage reads the index

From 0x376 the index stage clears a buffer, reads the part's index of
lengths from flash into it, clears the buffer for the lengths, and sets up
a second `Reader` over the index. At 0x3FE it starts the loop that reads
each length.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3

set_option maxRecDepth 100000

/-- The TUF part's bytes in flash. -/
abbrev acxTuf (P : AcxP) : Bytes :=
  flashBytes P.flash (reg P.n0 (24 : Fin 32)).toNat (reg P.n0 (23 : Fin 32)).toNat

theorem acx_ofNat_toNat (x : Word) : BitVec.ofNat 32 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])

theorem acx_sll2 (x : Word) (h : x.toNat ≤ 64) :
    aluEval .add (aluEval .sll x 2) 8 = BitVec.ofNat 32 (4 * x.toNat + 8) := by
  have key : ∀ c : Fin 65, aluEval .add (aluEval .sll (BitVec.ofNat 32 c.val) 2) 8 =
      BitVec.ofNat 32 (4 * c.val + 8) := by decide
  have := key ⟨x.toNat, by omega⟩
  rw [acx_ofNat_toNat] at this
  exact this

/-- The loop at 0x3FE, before it reads length `j`: the index is in the
buffer at `B + 0x5818`, the reader over it is at `B + 0x5A2C`, and the
buffer at `B + 0x5920` holds the lengths before `j`. -/
structure AcxLp (P : AcxP) (c j : Nat) (n : Machine) : Prop where
  st : St n.mem AC n 0x3FE (reg n)
  ac : AcxC P n
  hj : j ≤ c + 2
  s0 : reg n (8 : Fin 32) = BitVec.ofNat 32 (4 * (c + 2 - j))
  s1 : reg n (9 : Fin 32) = P.B + BitVec.ofNat 32 (0x5920 + 4 * j)
  s2 : reg n (18 : Fin 32) = BitVec.ofNat 32 c
  s3 : reg n (19 : Fin 32) = 0xFFFFD7FF
  s6 : reg n (22 : Fin 32) = 0xFFFFD800
  s10 : reg n (26 : Fin 32) = P.B + BitVec.ofNat 32 0x4D60
  rp : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x5A2C) = P.B + BitVec.ofNat 32 0x5818
  rl : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x5A30) = BitVec.ofNat 32 (4 * c + 8)
  rpos : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x5A34) = BitVec.ofNat 32 (4 * j)
  cnt : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x5A28) = BitVec.ofNat 32 c
  w30 : memLoad32 n.mem (P.B + BitVec.ofNat 32 0x3A80) = 0x6800 + memLoad32 P.n0.mem (P.B + BitVec.ofNat 32 0x3A84)
  buf : ∀ i, i < 4 * c + 8 →
    n.mem (P.B + BitVec.ofNat 32 (0x5818 + i)) = P.flash ((reg P.n0 (24 : Fin 32)).toNat + 8 + i)
  idx : ∀ i, i < j → (memLoad32 n.mem (P.B + BitVec.ofNat 32 (0x5920 + 4 * i))).toNat = acxW (acxTuf P) (8 + 4 * i)
  ok : ∀ i, i < j → 1 ≤ acxW (acxTuf P) (8 + 4 * i) ∧ acxW (acxTuf P) (8 + 4 * i) ≤ 0x2800
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

/-- From 0x37E: compare the part's length with 8. -/
def acxH10 : List BInstr := [.aluImm .add a1 x0 0x8, .aluImm .add a0 x0 0x0]

theorem acxH10_end : blockEnd bootMainClosure0Code 0x37E acxH10 = some 0x382 := by decide

/-- From 0x386: set up the read of the index from flash. -/
def acxH11 : List BInstr :=
  [.aluImm .sll (8 : Fin 32) (18 : Fin 32) 0x2, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x8,
   .aluImm .add a2 x0 0x8, .lui a0 0x2000, .aluImm .add a0 a0 0xFFFFFDC8, .alu .add a3 sp a0,
   .alu .add a0 x0 (24 : Fin 32), .alu .add a1 x0 (23 : Fin 32), .alu .add a4 x0 (8 : Fin 32),
   .lui a5 0x2000, .aluImm .add a5 a5 0xFFFFFDC8, .alu .add (19 : Fin 32) sp a5]

theorem acxH11_end : blockEnd bootMainClosure0Code 0x386 acxH11 = some 0x3A8 := by decide

/-- From 0x3B2: save the end of the frame's next buffer, and set up the
call that clears the lengths' buffer. -/
def acxH12 : List BInstr :=
  [.aluImm .add a0 x0 0xD, .aluImm .sll a0 a0 0xB, .lw a1 sp 0x34, .alu .add a0 a0 a1, .sw sp a0 0x30,
   .lui a0 0x2000, .aluImm .add a0 a0 0xFFFFFED0, .alu .add a0 a0 sp, .aluImm .add a2 x0 0x108,
   .aluImm .add a1 x0 0x0, .lui a3 0x2000, .aluImm .add a3 a3 0xFFFFFED0, .alu .add (9 : Fin 32) sp a3]

theorem acxH12_end : blockEnd bootMainClosure0Code 0x3B2 acxH12 = some 0x3D4 := by decide

/-- From 0x3DC: store the count and the reader over the index, and load the
bounds on a length. -/
def acxH13 : List BInstr :=
  [.lui a0 0x2000, .aluImm .add a0 a0 0xFFFFFDB0, .alu .add a0 a0 sp, .sw a0 (18 : Fin 32) 0x228,
   .sw a0 (19 : Fin 32) 0x22C, .sw a0 (8 : Fin 32) 0x230, .sw a0 x0 0x234, .lui a0 0xFFFFD000,
   .aluImm .add (22 : Fin 32) x0 0xFFFFFFFB, .aluImm .add (19 : Fin 32) a0 0x7FF,
   .aluImm .sll (22 : Fin 32) (22 : Fin 32) 0xB]

theorem acxH13_end : blockEnd bootMainClosure0Code 0x3DC acxH13 = some 0x3FE := by decide

set_option maxHeartbeats 4000000 in
/-- From 0x376 to 0x3FE: read the index and set up the loop. -/
theorem acx_h4 {P : AcxP} (K : AcxK P) {n : Machine} (S : AcxS2 P n) :
    AcxTo P n (fun n' => AcxLp P (reg n (18 : Fin 32)).toNat 0 n') := by
  have F := K.F
  have hFl := F.lo; have hFh := F.hi
  have A := S.c
  have hc := S.hc
  have r23 : reg n (23 : Fin 32) = reg P.n0 23 := A.kl 23 (by decide)
  have r24 : reg n (24 : Fin 32) = reg P.n0 24 := A.kl 24 (by decide)
  obtain ⟨n1, c1, t1, A1, kk1, m1⟩ := acx_cmemset K A S.st ac_at_376 ac_at_37a (by decide) (by decide)
    (d := 0x5818) (k := 0x108) (by decide) (by decide) S.a0 S.a1 S.a2
  obtain ⟨n2, c2, t2, A2, m2, g2⟩ := acx_blk K A1 t1 acxH10 acxH10_end ⟨trivial, trivial, trivial⟩ rfl
    (by decide)
  have a12 : reg n2 a1 = 8 := by
    rw [g2]; simp +decide only [runBlock, BInstr.run, acxH10, upd, ↓reduceIte, aluEval]; rw [t1.zero]; rfl
  obtain ⟨n3, e3, t3⟩ := t2.notTaken (A2.code K) 0x386 ac_at_382 (by decide)
    (acx_bltu_f (by rw [a12, g2, runBlock_reg _ _ _ _ t1.zero (by decide), kk1 _ (by decide), r23]; exact S.hL8))
  have A3 := A2.st t3
  have t3' := acx_st t3
  have hz3 := t3'.zero
  have rsp3 := A3.rsp K
  obtain ⟨n4, c4, t4, A4, m4, g4⟩ := acx_blk K A3 t3' acxH11 acxH11_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial⟩ rfl (by decide)
  have k3 : ∀ q, acxS q = true → reg n3 q = reg n q := fun q hq => by
    rw [t3.regs, g2, runBlock_reg _ _ _ q t1.zero (by simp only [acxH10]; revert hq; revert q; decide), kk1 q hq]
  have v80 : reg n4 (8 : Fin 32) = BitVec.ofNat 32 (4 * (reg n (18 : Fin 32)).toNat + 8) := by
    rw [g4]; simp +decide only [runBlock, BInstr.run, acxH11, upd, ↓reduceIte]
    rw [k3 _ (by decide)]; exact acx_sll2 _ hc
  have v19 : reg n4 (19 : Fin 32) = P.B + BitVec.ofNat 32 0x5818 := by
    rw [g4]; simp +decide only [runBlock, BInstr.run, acxH11, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    exact acx_k rsp3 _ (by decide)
  obtain ⟨n5, c5, t5, A5, kk5, a05, ok5, fr5⟩ := acx_cfpr K A4 t4 ac_at_3a8 ac_at_3ac (by decide) (by decide)
    (d := 0x5818) (len := 4 * (reg n (18 : Fin 32)).toNat + 8) (start := reg P.n0 24) (plen := reg P.n0 23)
    (off := 8) (by decide) (by omega)
    (by rw [g4]; simp +decide only [runBlock, BInstr.run, acxH11, upd, ↓reduceIte]
        rw [k3 _ (by decide), r24]; exact BitVec.zero_add _)
    (by rw [g4]; simp +decide only [runBlock, BInstr.run, acxH11, upd, ↓reduceIte]
        rw [k3 _ (by decide), r23]; exact BitVec.zero_add _)
    (by rw [g4]; simp +decide only [runBlock, BInstr.run, acxH11, upd, ↓reduceIte])
    (by rw [g4]; simp +decide only [runBlock, BInstr.run, acxH11, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
        exact acx_k rsp3 _ (by decide))
    (by rw [g4]; simp +decide only [runBlock, BInstr.run, acxH11, upd, ↓reduceIte]
        rw [k3 _ (by decide), acx_sll2 _ hc]; exact BitVec.zero_add _)
  have C5 := A5.code K
  rcases a05 with h0 | h1
  · obtain ⟨n6, e6, t6⟩ := t5.taken C5 0x430 ac_at_3b0 (by decide) (acx_beq_t (by rw [h0, t5.zero]))
    exact AcxTo.pre (c1.trans (c2.trans ((Steps.single e3).trans (c4.trans (c5.trans (.single e6))))))
      (acx_e26 K (A5.st t6) (acx_st t6))
  obtain ⟨n6, e6, t6⟩ := t5.notTaken C5 0x3B2 ac_at_3b0 (by decide)
    (acx_beq_f (by rw [h1, t5.zero]; decide))
  obtain ⟨o1, -, o3⟩ := ok5 h1
  rw [show (8 : Word).toNat = 8 from rfl] at o1 o3
  have A6 := A5.st t6
  have t6' := acx_st t6
  have hz6 := t6'.zero
  have rsp6 := A6.rsp K
  obtain ⟨n7, c7, u7⟩ := t6'.block acxH12 (A6.code K) acxH12_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acxH12]
    simp +decide only [upd, ↓reduceIte, and_true, true_and]
    rw [acx_k rsp6 (0x34 : Word) (c := 0x3A84) (by decide), acx_k rsp6 (0x30 : Word) (c := 0x3A80) (by decide)]
    exact ⟨acx_al F (by decide) (by decide), acx_swok F (by decide) (by decide)⟩)
  have m7 : n7.mem = memStore32 n6.mem (P.B + BitVec.ofNat 32 0x3A80)
      (0x6800 + memLoad32 n6.mem (P.B + BitVec.ofNat 32 0x3A84)) := by
    rw [u7.mem]; simp only [runBlock, BInstr.run, acxH12]
    simp +decide only [upd, ↓reduceIte]
    rw [acx_k rsp6 (0x34 : Word) (c := 0x3A84) (by decide), acx_k rsp6 (0x30 : Word) (c := 0x3A80) (by decide), hz6,
      show aluEval .sll (aluEval .add 0 13) 11 = 0x6800 by decide]
    rfl
  have g7 : ∀ q, reg n7 q = (runBlock acxH12 (n6.mem, reg n6)).2 q := fun q => by rw [u7.regs]
  have t7 : St n7.mem AC n7 0x3D4 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have k7 : ∀ q, acxS q = true → q ≠ (9 : Fin 32) → reg n7 q = reg n6 q := fun q hq h9 => by
    rw [g7, runBlock_reg _ _ _ q hz6 (by simp only [acxH12]; revert hq h9; revert q; decide)]
  have A7 : AcxC P n7 := A6.next
    (fun q hq => k7 q (by revert hq; revert q; decide) (by revert hq; revert q; decide))
    (fun x h1 _ => by rw [m7, memStore32_get_sep (acx_sepR F (by decide) (by omega))])
  have s17 : reg n7 (9 : Fin 32) = P.B + BitVec.ofNat 32 0x5920 := by
    rw [g7]; simp +decide only [runBlock, BInstr.run, acxH12, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    exact acx_k rsp6 _ (by decide)
  obtain ⟨n8, c8, t8, A8, kk8, m8⟩ := acx_cmemset K A7 t7 ac_at_3d4 ac_at_3d8 (by decide) (by decide)
    (d := 0x5920) (k := 0x108) (by decide) (by decide)
    (by rw [g7]; simp +decide only [runBlock, BInstr.run, acxH12, upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
        exact acx_k' rsp6 _ (by decide))
    (by rw [g7]; simp +decide only [runBlock, BInstr.run, acxH12, upd, ↓reduceIte, aluEval, BitVec.reduceAdd, hz6])
    (by rw [g7]; simp +decide only [runBlock, BInstr.run, acxH12, upd, ↓reduceIte, aluEval, BitVec.reduceAdd, hz6])
  have t8' := acx_st t8
  have hz8 := t8'.zero
  have rsp8 := A8.rsp K
  obtain ⟨n9, c9, u9⟩ := t8'.block acxH13 (A8.code K) acxH13_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acxH13]
    simp +decide only [upd, ↓reduceIte, and_true, true_and, aluEval, BitVec.reduceAdd]
    rw [acx_k' rsp8 _ (c := 0x5800) (by decide)]
    exact ⟨acx_swok' F _ (by decide) (by decide), acx_swok' F _ (by decide) (by decide),
      acx_swok' F _ (by decide) (by decide), acx_swok' F _ (by decide) (by decide)⟩)
  have g9 : ∀ q, reg n9 q = (runBlock acxH13 (n8.mem, reg n8)).2 q := fun q => by rw [u9.regs]
  have t9 : St n9.mem AC n9 0x3FE (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have m9 : n9.mem = memStore32 (memStore32 (memStore32 (memStore32 n8.mem (P.B + BitVec.ofNat 32 0x5A28)
      (reg n8 18)) (P.B + BitVec.ofNat 32 0x5A2C) (reg n8 19)) (P.B + BitVec.ofNat 32 0x5A30) (reg n8 8))
      (P.B + BitVec.ofNat 32 0x5A34) 0 := by
    rw [u9.mem]; simp only [runBlock, BInstr.run, acxH13]
    simp +decide only [upd, ↓reduceIte, aluEval, BitVec.reduceAdd]
    rw [acx_k' rsp8 _ (c := 0x5800) (by decide), acx_fl (0x228 : Word) (by decide), acx_fl (0x22C : Word) (by decide),
      acx_fl (0x230 : Word) (by decide), acx_fl (0x234 : Word) (by decide)]
    rfl
  have s39 : reg n9 (19 : Fin 32) = 0xFFFFD7FF := by
    rw [g9]; simp +decide only [runBlock, BInstr.run, acxH13, upd, ↓reduceIte]
  have s69 : reg n9 (22 : Fin 32) = 0xFFFFD800 := by
    rw [g9]; simp +decide only [runBlock, BInstr.run, acxH13, upd, ↓reduceIte]
  have k9 : ∀ q, acxS q = true → q ≠ (19 : Fin 32) → q ≠ (22 : Fin 32) → reg n9 q = reg n8 q :=
    fun q hq h19 h22 => by
      rw [g9, runBlock_reg _ _ _ q hz8 (by simp only [acxH13]; revert hq h19 h22; revert q; decide)]
  have A9 : AcxC P n9 := A8.next
    (fun q hq => k9 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
      (by revert hq; revert q; decide))
    (fun x _ h2 => by
      rw [m9, memStore32_get_sep (acx_sepR F (by decide) (by omega)),
        memStore32_get_sep (acx_sepR F (by decide) (by omega)),
        memStore32_get_sep (acx_sepR F (by decide) (by omega)),
        memStore32_get_sep (acx_sepR F (by decide) (by omega))])
  have r84 : ∀ q, acxS q = true → q ≠ (9 : Fin 32) → reg n8 q = reg n4 q := fun q hq h9 => by
    rw [kk8 q hq, k7 q hq h9, t6.regs, kk5 q hq]
  have rn : ∀ q, acxS q = true → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (19 : Fin 32) →
      q ≠ (22 : Fin 32) → reg n9 q = reg n q := fun q hq h8 h9 h19 h22 => by
    rw [k9 q hq h19 h22, r84 q hq h9, g4,
      runBlock_reg _ _ _ q hz3 (by simp only [acxH11]; revert hq h8 h19; revert q; decide), k3 q hq]
  have mm : ∀ x : Word, (x.toNat < P.B.toNat + 0x5920 ∨ P.B.toNat + 0x5A38 ≤ x.toNat) → n9.mem x = n7.mem x :=
    fun x h => by
      rw [m9, memStore32_get_sep (acx_sepR F (by decide) (by omega)),
        memStore32_get_sep (acx_sepR F (by decide) (by omega)),
        memStore32_get_sep (acx_sepR F (by decide) (by omega)),
        memStore32_get_sep (acx_sepR F (by decide) (by omega)), m8,
        fillBytes_sep (acx_sepR F (by decide) (by omega)) (Nat.le_refl _)]
  have hs8 : reg n8 (8 : Fin 32) = BitVec.ofNat 32 (4 * (reg n (18 : Fin 32)).toNat + 8) :=
    (r84 _ (by decide) (by decide)).trans v80
  have hs19 : reg n8 (19 : Fin 32) = P.B + BitVec.ofNat 32 0x5818 := (r84 _ (by decide) (by decide)).trans v19
  have hs18 : reg n8 (18 : Fin 32) = reg n 18 := by
    rw [r84 _ (by decide) (by decide), g4, runBlock_reg _ _ _ _ hz3 (by decide), k3 _ (by decide)]
  refine AcxTo.pre (c1.trans (c2.trans ((Steps.single e3).trans (c4.trans (c5.trans
    ((Steps.single e6).trans (c7.trans (c8.trans c9)))))))) (AcxTo.done ⟨t9, A9, by omega, ?_, ?_, ?_, s39, s69, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      hc, o1, S.hL, S.f0, S.f1, S.f2, S.f3, S.fv, S.fc⟩)
  · rw [k9 _ (by decide) (by decide) (by decide), hs8, show 4 * ((reg n (18 : Fin 32)).toNat + 2 - 0) =
      4 * (reg n (18 : Fin 32)).toNat + 8 by omega]
  · rw [k9 _ (by decide) (by decide) (by decide), kk8 _ (by decide), s17]
  · rw [rn _ (by decide) (by decide) (by decide) (by decide) (by decide), acx_ofNat_toNat]
  · rw [rn _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact S.s10
  · rw [m9, memLoad32_store32_sep (acx_ss (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (acx_ss (by decide) (by decide) (by decide)), memLoad32_store32_same, hs19]
  · rw [m9, memLoad32_store32_sep (acx_ss (by decide) (by decide) (by decide)), memLoad32_store32_same, hs8]
  · rw [m9, memLoad32_store32_same]; rfl
  · rw [m9, memLoad32_store32_sep (acx_ss (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (acx_ss (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (acx_ss (by decide) (by decide) (by decide)), memLoad32_store32_same, hs18,
      acx_ofNat_toNat]
  · rw [acx_wz F (e := 0x3A80) (by decide) fun x h1 h2 => mm x (by omega), m7, memLoad32_store32_same,
      acx_wz F (e := 0x3A84) (by decide) fun x h1 h2 => A6.keep x (by omega) (by omega)]
  · intro i hi
    have hx := F.at (0x5818 + i) (show 0x5818 + i ≤ 0x5A70 by omega)
    rw [mm _ (by omega), m7, memStore32_get_sep (acx_sepR F (by decide) (by omega)), t6.mem]
    exact o3 i hi
end C3.RV32.Ac
