import C3BootProofs.Proofs.Ed25519VerifyP1b

/-!
# `ed25519_verify`, offsets 0x17C to 0xF1E: `s` reduced

`Scalar::from_canonical_bytes` reduces `s` with an inlined
`montgomery_reduce(mul_internal(s, R))` (`EdvReduceBody.lean`), masks the
nine limbs to 29 bits but the last, and stores them at `F + 0x9F0`.
-/

namespace C3.RV32

open C3.Image

/-- Limb `j` of the reduced `s` that offset 0xF1E leaves at `F + 0x9F0`. -/
def evLimb (w : Nat → Nat) (j : Nat) : Nat :=
  [evrR0 w % 2 ^ 29, evrR1 w % 2 ^ 29, evrR2 w % 2 ^ 29, evrR3 w % 2 ^ 29, evrR4 w % 2 ^ 29, evrR5 w % 2 ^ 29,
   evrR6 w % 2 ^ 29, evrR7 w % 2 ^ 29, evrR8 w].getD j 0

theorem and_mask29 (x : Word) : (aluEval .and x 0x1FFFFFFF).toNat = x.toNat % 2 ^ 29 :=
  wv_and x 29 (by decide)

theorem evLdSt {M0 : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} (C : EvCtx M0 F pk sig msg len)
    {M : Word → BitVec 8} {v : Word} {c d : Nat} (h : c + 4 ≤ d ∨ d + 4 ≤ c) (hc : c + 4 ≤ 0x16A0) (hd : d + 4 ≤ 0x16A0) :
    memLoad32 (memStore32 M (F + BitVec.ofNat 32 c) v) (F + BitVec.ofNat 32 d) = memLoad32 M (F + BitVec.ofNat 32 d) :=
  memLoad32_store32_sep (C.offs h hc hd)

theorem evSt32F {M0 : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} (C : EvCtx M0 F pk sig msg len)
    {M : Word → BitVec 8} {v : Word} {c d : Nat} (h : c + 4 ≤ d ∨ d + 1 ≤ c) (hc : c + 4 ≤ 0x16A0) (hd : d + 1 ≤ 0x16A0) :
    memStore32 M (F + BitVec.ofNat 32 c) v (F + BitVec.ofNat 32 d) = M (F + BitVec.ofNat 32 d) :=
  st32_frame (C.offs h hc hd)

theorem s29PackByte_congr {l l' : Nat → Word} (h : ∀ i, i < 9 → l i = l' i) :
    ∀ j, s29PackByte l j = s29PackByte l' j := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide); have h4 := h 4 (by decide); have h5 := h 5 (by decide)
  have h6 := h 6 (by decide); have h7 := h 7 (by decide); have h8 := h 8 (by decide)
  intro j
  match j with
  | 0 => simp only [s29PackByte]; rw [h0]
  | 1 => simp only [s29PackByte]; rw [h0]
  | 2 => simp only [s29PackByte]; rw [h0]
  | 3 => simp only [s29PackByte]; rw [h0, h1]
  | 4 => simp only [s29PackByte]; rw [h1]
  | 5 => simp only [s29PackByte]; rw [h1]
  | 6 => simp only [s29PackByte]; rw [h1]
  | 7 => simp only [s29PackByte]; rw [h1, h2]
  | 8 => simp only [s29PackByte]; rw [h2]
  | 9 => simp only [s29PackByte]; rw [h2]
  | 10 => simp only [s29PackByte]; rw [h2, h3]
  | 11 => simp only [s29PackByte]; rw [h3]
  | 12 => simp only [s29PackByte]; rw [h3]
  | 13 => simp only [s29PackByte]; rw [h3]
  | 14 => simp only [s29PackByte]; rw [h3, h4]
  | 15 => simp only [s29PackByte]; rw [h4]
  | 16 => simp only [s29PackByte]; rw [h4]
  | 17 => simp only [s29PackByte]; rw [h4]
  | 18 => simp only [s29PackByte]; rw [h4, h5]
  | 19 => simp only [s29PackByte]; rw [h5]
  | 20 => simp only [s29PackByte]; rw [h5]
  | 21 => simp only [s29PackByte]; rw [h5, h6]
  | 22 => simp only [s29PackByte]; rw [h6]
  | 23 => simp only [s29PackByte]; rw [h6]
  | 24 => simp only [s29PackByte]; rw [h6]
  | 25 => simp only [s29PackByte]; rw [h6, h7]
  | 26 => simp only [s29PackByte]; rw [h7]
  | 27 => simp only [s29PackByte]; rw [h7]
  | 28 => simp only [s29PackByte]; rw [h7]
  | 29 => simp only [s29PackByte]; rw [h8]
  | 30 => simp only [s29PackByte]; rw [h8]
  | 31 => simp only [s29PackByte]; rw [h8]
  | _ + 32 => rfl

/-- The 32 bytes `pack` writes for `sub`'s result on the limbs `L`. -/
def evPackS (L : Nat → Nat) : Bytes :=
  (List.range 32).map fun j => (s29PackByte (fun i => BitVec.ofNat 32 (s29Out L i)) j).toNat

theorem ev_flag_and : ∀ b1 b2 : Bool, aluEval .and (aluEval .and (if b1 then (1 : Word) else 0) (if b2 then 1 else 0)) 0xFF =
    if (b1 && b2) then 1 else 0 := by decide

theorem flag_bb : ∀ b : Bool, ((if b then (1 : Word) else 0).extractLsb' 0 8).zeroExtend 32 = if b then 1 else 0 := by
  decide

theorem flag_ff : ∀ b : Bool, aluEval .and (if b then (1 : Word) else 0) 0xFF = if b then 1 else 0 := by decide

theorem flag_bne : ∀ b : Bool, branchTaken .bne (if b then (1 : Word) else 0) 1 = !b := by decide

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0xEE4: the limbs in registers masked to 29 bits, but the
last, and stored at `F + 0x9F0`. -/
theorem ev_mask (C : EvCtx M0 F pk sig msg len) {M1 : Word → BitVec 8} {n1 : Machine}
    (D : EvSt M0 Ms F r0 M1 n1 0xEE4) {R0 R1 R2 R3 R4 R5 R6 R7 R8 : Nat}
    (e0 : (reg n1 a6).toNat = R0) (e1 : (reg n1 7).toNat = R1) (e2 : (reg n1 6).toNat = R2)
    (e3 : (reg n1 5).toNat = R3) (e4 : (reg n1 28).toNat = R4) (e5 : (reg n1 9).toNat = R5)
    (e6 : (reg n1 8).toNat = R6) (e7 : (reg n1 a1).toNat = R7) (e8 : (reg n1 a0).toNat = R8)
    (s3_1 : reg n1 19 = F + 0x90F) (s2_1 : reg n1 18 = 0x1FFFFFFF) :
    ∃ n' M', Steps n1 n' ∧ EvSt M0 Ms F r0 M' n' 0xF1E ∧
      (∀ j, j < 9 → ssAw M' (F + BitVec.ofNat 32 0x9F0) j =
        [R0 % 2 ^ 29, R1 % 2 ^ 29, R2 % 2 ^ 29, R3 % 2 ^ 29, R4 % 2 ^ 29, R5 % 2 ^ 29, R6 % 2 ^ 29, R7 % 2 ^ 29,
          R8].getD j 0) ∧
      (∀ c, c < 0x16A0 → (c < 0x9F0 ∨ 0xA14 ≤ c) → M' (F + BitVec.ofNat 32 c) = M1 (F + BitVec.ofNat 32 c)) ∧
      reg n' 19 = F + 0x90F ∧ reg n' 27 = 0x1FFFFFFF := by
  have K : ∀ {blk : List BInstr} {M' : Word → BitVec 8} {f : Fin 32 → Word} (q : Fin 32), f 0 = 0 →
      q ∉ blk.filterMap BInstr.dst → (runBlock blk (M', f)).2 q = f q := fun q h0 h => runBlock_reg _ _ _ q h0 h
  -- 0xEE4: masks of limbs 0 and 1, and `a4 = F + 0x990`.
  obtain ⟨n2, c2, D2, hr2⟩ := D.block C (off' := 0xEF0)
    [.alu .and a2 a6 (18 : Fin 32), .alu .and a3 (7 : Fin 32) (18 : Fin 32), .aluImm .add a4 (19 : Fin 32) 0x81]
    (blockEnd_cons' ev_at_ee4 rfl (blockEnd_cons' ev_at_ee8 rfl (blockEnd_cons' ev_at_eec rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have va4 : reg n2 a4 = F + BitVec.ofNat 32 0x990 := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [s3_1]; exact add_sp F rfl
  have k2 : ∀ q : Fin 32, q.val ∈ [5, 6, 7, 8, 9, 10, 11, 16, 18, 19, 27, 28] → reg n2 q = reg n1 q := fun q hq => by
    rw [hr2]; exact K q D.st.zero (by revert hq; revert q; decide)
  obtain ⟨n3, d3, D3, k3⟩ := D2.sw C (c := 0x9F0) (off' := 0xEF2) ev_at_ef0 (by decide) (by rw [va4]; exact add_ofNat_assoc ..)
    (by decide) (by decide)
  have v0 : (reg n2 a2).toNat = R0 % 2 ^ 29 := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [s2_1, and_mask29, e0]
  have v1 : (reg n2 a3).toNat = R1 % 2 ^ 29 := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [s2_1, and_mask29, e1]
  have S : ∀ q : Fin 32, q.val ∈ [5, 6, 7, 8, 9, 10, 16, 18, 19, 28] → q.val ≠ 0 := by decide
  -- 0xEF2: mask of limb 2.
  obtain ⟨n4, c4, D4, hr4⟩ := D3.block C (off' := 0xEF6) [.alu .and a2 (6 : Fin 32) (18 : Fin 32)]
    (bEnd1 ev_at_ef2 rfl) ⟨trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have k4 : ∀ q : Fin 32, q ≠ a2 → reg n4 q = reg n3 q := fun q hq => by
    rw [hr4]; simp only [runBlock, BInstr.run]; exact upd_ne' hq D3.st.zero
  have v2 : (reg n4 a2).toNat = R2 % 2 ^ 29 := by
    rw [hr4]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [k3, k3, k2 6 (by decide), k2 18 (by decide), s2_1, and_mask29, e2]
  have a4_4 : reg n4 a4 = F + BitVec.ofNat 32 0x990 := by rw [k4 _ (by decide), k3, va4]
  obtain ⟨n5, d5, D5, k5⟩ := D4.sw C (c := 0x9F4) (off' := 0xEF8) ev_at_ef6 (by decide)
    (by rw [a4_4]; exact add_ofNat_assoc ..) (by decide) (by decide)
  -- 0xEF8: mask of limb 3.
  obtain ⟨n6, c6, D6, hr6⟩ := D5.block C (off' := 0xEFC) [.alu .and a3 (5 : Fin 32) (18 : Fin 32)]
    (bEnd1 ev_at_ef8 rfl) ⟨trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have k6 : ∀ q : Fin 32, q ≠ a3 → reg n6 q = reg n5 q := fun q hq => by
    rw [hr6]; simp only [runBlock, BInstr.run]; exact upd_ne' hq D5.st.zero
  have v3 : (reg n6 a3).toNat = R3 % 2 ^ 29 := by
    rw [hr6]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [k5, k5, k4 _ (by decide), k4 _ (by decide), k3, k3, k2 5 (by decide), k2 18 (by decide), s2_1, and_mask29, e3]
  have a4_6 : reg n6 a4 = F + BitVec.ofNat 32 0x990 := by rw [k6 _ (by decide), k5, a4_4]
  obtain ⟨n7, d7, D7, k7⟩ := D6.sw C (c := 0x9F8) (off' := 0xEFE) ev_at_efc (by decide)
    (by rw [a4_6]; exact add_ofNat_assoc ..) (by decide) (by decide)
  obtain ⟨n8, d8, D8, k8⟩ := D7.sw C (c := 0x9FC) (off' := 0xF00) ev_at_efe (by decide)
    (by rw [k7, a4_6]; exact add_ofNat_assoc ..) (by decide) (by decide)
  -- 0xF00: masks of limbs 4 and 5.
  obtain ⟨n9, c9, D9, hr9⟩ := D8.block C (off' := 0xF08)
    [.alu .and a2 (28 : Fin 32) (18 : Fin 32), .alu .and a3 (9 : Fin 32) (18 : Fin 32)]
    (blockEnd_cons' ev_at_f00 rfl (blockEnd_cons' ev_at_f04 rfl rfl)) ⟨trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have b8 : ∀ q : Fin 32, q.val ∈ [5, 6, 7, 8, 9, 10, 16, 18, 19, 28] → reg n8 q = reg n1 q := fun q hq => by
    rw [k8, k7, k6 q (by revert hq; revert q; decide), k5, k4 q (by revert hq; revert q; decide), k3,
      k2 q (by revert hq; revert q; decide)]
  have v4 : (reg n9 a2).toNat = R4 % 2 ^ 29 := by
    rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [b8 28 (by decide), b8 18 (by decide), s2_1, and_mask29, e4]
  have v5 : (reg n9 a3).toNat = R5 % 2 ^ 29 := by
    rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [b8 9 (by decide), b8 18 (by decide), s2_1, and_mask29, e5]
  have a4_9 : reg n9 a4 = F + BitVec.ofNat 32 0x990 := by
    rw [hr9, K a4 D8.st.zero (by decide), k8, k7, a4_6]
  obtain ⟨n10, d10, D10, k10⟩ := D9.sw C (c := 0xA00) (off' := 0xF0A) ev_at_f08 (by decide)
    (by rw [a4_9]; exact add_ofNat_assoc ..) (by decide) (by decide)
  -- 0xF0A: mask of limb 6.
  obtain ⟨n11, c11, D11, hr11⟩ := D10.block C (off' := 0xF0E) [.alu .and a2 (8 : Fin 32) (18 : Fin 32)]
    (bEnd1 ev_at_f0a rfl) ⟨trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have b10 : ∀ q : Fin 32, q.val ∈ [5, 6, 7, 8, 9, 10, 16, 18, 19, 28] → reg n10 q = reg n1 q := fun q hq => by
    rw [k10, hr9, K q D8.st.zero (by revert hq; revert q; decide), b8 q hq]
  have v6 : (reg n11 a2).toNat = R6 % 2 ^ 29 := by
    rw [hr11]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [b10 8 (by decide), b10 18 (by decide), s2_1, and_mask29, e6]
  have k11 : ∀ q : Fin 32, q ≠ a2 → reg n11 q = reg n10 q := fun q hq => by
    rw [hr11]; simp only [runBlock, BInstr.run]; exact upd_ne' hq D10.st.zero
  have a4_11 : reg n11 a4 = F + BitVec.ofNat 32 0x990 := by rw [k11 _ (by decide), k10, a4_9]
  obtain ⟨n12, d12, D12, k12⟩ := D11.sw C (c := 0xA04) (off' := 0xF10) ev_at_f0e (by decide)
    (by rw [a4_11]; exact add_ofNat_assoc ..) (by decide) (by decide)
  -- 0xF10: `s11 = mask` and the mask of limb 7.
  obtain ⟨n13, c13, D13, hr13⟩ := D12.block C (off' := 0xF16)
    [.alu .add (27 : Fin 32) x0 (18 : Fin 32), .alu .and a1 a1 (18 : Fin 32)]
    (blockEnd_cons' ev_at_f10 rfl (blockEnd_cons' ev_at_f12 rfl rfl)) ⟨trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have b12 : ∀ q : Fin 32, q.val ∈ [5, 6, 7, 8, 9, 10, 16, 18, 19, 28] → reg n12 q = reg n1 q := fun q hq => by
    rw [k12, k11 q (by revert hq; revert q; decide), b10 q hq]
  have a1_12 : reg n12 a1 = reg n1 a1 := by
    rw [k12, k11 _ (by decide), k10, hr9, K a1 D8.st.zero (by decide), k8, k7, k6 _ (by decide), k5,
      k4 _ (by decide), k3, hr2, K a1 D.st.zero (by decide)]
  have v7 : (reg n13 a1).toNat = R7 % 2 ^ 29 := by
    rw [hr13]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [a1_12, b12 18 (by decide), s2_1, and_mask29, e7]
  have s11 : reg n13 27 = 0x1FFFFFFF := by
    rw [hr13]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [b12 18 (by decide), s2_1, D12.st.zero]; rfl
  have a4_13 : reg n13 a4 = F + BitVec.ofNat 32 0x990 := by
    rw [hr13, K a4 D12.st.zero (by decide), k12, a4_11]
  have a2_13 : reg n13 a2 = reg n11 a2 := by rw [hr13, K a2 D12.st.zero (by decide), k12]
  obtain ⟨n14, d14, D14, k14⟩ := D13.sw C (c := 0xA08) (off' := 0xF18) ev_at_f16 (by decide)
    (by rw [a4_13]; exact add_ofNat_assoc ..) (by decide) (by decide)
  obtain ⟨n15, d15, D15, k15⟩ := D14.sw C (c := 0xA0C) (off' := 0xF1A) ev_at_f18 (by decide)
    (by rw [k14, a4_13]; exact add_ofNat_assoc ..) (by decide) (by decide)
  have b15 : ∀ q : Fin 32, q.val ∈ [5, 6, 7, 8, 9, 10, 16, 18, 19, 28] → reg n15 q = reg n1 q := fun q hq => by
    rw [k15, k14, hr13, K q D12.st.zero (by revert hq; revert q; decide), b12 q hq]
  obtain ⟨n16, d16, D16, k16⟩ := D15.sw C (c := 0xA10) (off' := 0xF1E) ev_at_f1a (by decide)
    (by rw [b15 19 (by decide), s3_1]; exact add_ofNat_assoc ..) (by decide) (by decide)
  have v8 : (reg n15 a0).toNat = R8 := by rw [b15 10 (by decide), e8]
  have w1 : reg n4 a3 = reg n2 a3 := by rw [k4 _ (by decide), k3]
  have w2 : reg n6 a2 = reg n4 a2 := by rw [k6 _ (by decide), k5]
  have w3 : reg n7 a3 = reg n6 a3 := k7 _
  have w5 : reg n11 a3 = reg n9 a3 := by rw [k11 _ (by decide), k10]
  have w7 : reg n14 a1 = reg n13 a1 := k14 _
  rw [w1, w2, w3, w5, a2_13, w7] at D16
  refine ⟨n16, _, c2.trans (.cons d3 (c4.trans (.cons d5 (c6.trans (.cons d7 (.cons d8 (c9.trans
    (.cons d10 (c11.trans (.cons d12 (c13.trans (.cons d14 (.cons d15 (.single d16)))))))))))))), D16,
    fun j hj => ?_, fun c h1 h2 => ?_, by rw [k16, b15 19 (by decide), s3_1], by rw [k16, k15, k14, s11]⟩
  · show (memLoad32 _ (F + BitVec.ofNat 32 0x9F0 + BitVec.ofNat 32 (4 * j))).toNat = _
    rw [add_ofNat_assoc]
    match j, hj with
    | 0, _ => simp (disch := decide) only [evLdSt C, memLoad32_store32_same, Nat.reduceMul, Nat.reduceAdd]; exact v0
    | 1, _ => simp (disch := decide) only [evLdSt C, memLoad32_store32_same, Nat.reduceMul, Nat.reduceAdd]; exact v1
    | 2, _ => simp (disch := decide) only [evLdSt C, memLoad32_store32_same, Nat.reduceMul, Nat.reduceAdd]; exact v2
    | 3, _ => simp (disch := decide) only [evLdSt C, memLoad32_store32_same, Nat.reduceMul, Nat.reduceAdd]; exact v3
    | 4, _ => simp (disch := decide) only [evLdSt C, memLoad32_store32_same, Nat.reduceMul, Nat.reduceAdd]; exact v4
    | 5, _ => simp (disch := decide) only [evLdSt C, memLoad32_store32_same, Nat.reduceMul, Nat.reduceAdd]; exact v5
    | 6, _ => simp (disch := decide) only [evLdSt C, memLoad32_store32_same, Nat.reduceMul, Nat.reduceAdd]; exact v6
    | 7, _ => simp (disch := decide) only [evLdSt C, memLoad32_store32_same, Nat.reduceMul, Nat.reduceAdd]; exact v7
    | 8, _ => simp (disch := decide) only [memLoad32_store32_same, Nat.reduceMul, Nat.reduceAdd]; exact v8
  · rcases h2 with h2 | h2 <;> simp (disch := omega) only [evSt32F C]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x17C: `s` reduced, its limbs at `F + 0x9F0`, the message
address at `F + 0xC`, and the rest of the frame from `F + 0x128` up as
before. -/
theorem ev_red (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x17C)
    (h20 : reg n 20 = F + BitVec.ofNat 32 0x90F) (h21 : reg n 21 = msg) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0xF1E ∧
      (∀ j, j < 9 → ssAw M' (F + BitVec.ofNat 32 0x9F0) j = evLimb (evIn M F) j) ∧
      memLoad32 M' (F + 0xC) = msg ∧ memLoad32 M' (F + 0x10) = memLoad32 M (F + 0x10) ∧
      memLoad32 M' (F + 0xD0) = memLoad32 M (F + 0xD0) ∧
      (∀ c, c < 0x16A0 → 0x128 ≤ c → (c < 0x9F0 ∨ 0xA14 ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c)) ∧
      reg n' 19 = F + 0x90F ∧ reg n' 27 = 0x1FFFFFFF := by
  have hcF : Sep F 0x128 EV ed25519VerifyCode.length := by
    have := C.codeF (c := 0) (l := 0x128) (by decide) (b := EV) (k := ed25519VerifyCode.length) (by decide)
      (by rw [ev_len]; decide)
    rwa [add_ofNat_zero] at this
  obtain ⟨n1, M1, c1, u1, fr1, m10, md0, mc, hl, sp1, s3_1, s2_1, g1, t1'⟩ :=
    evr_body D.st (D.code C) D.hsp h20 h21 (by have := C.hF; omega) hcF
  have D1 := D.store C (d := 0) (k := 0x128) u1 sp1 g1 t1' (by decide)
    (fun x hx => fr1 x (by rwa [add_ofNat_zero] at hx))
  simp only [List.map, List.cons.injEq] at hl
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := hl
  obtain ⟨n2, M2, c2, D2, L2, F2, s3_2, s11_2⟩ := ev_mask C D1 e0 e1 e2 e3 e4 e5 e6 e7 e8 s3_1 s2_1
  have hF2 : ∀ c, c < 0x16A0 → (c < 0x9F0 ∨ 0xA14 ≤ c) → c < 0x9F0 ∨ 0xA14 ≤ c := fun _ _ h => h
  refine ⟨n2, M2, c1.trans c2, D2, L2, ?_, ?_, ?_, fun c h1 h2 h3 => ?_, s3_2, s11_2⟩
  · exact (memLoad32_congr (M := M1) (M' := M2) fun j hj => by
      rw [show F + (0xC : Word) = F + BitVec.ofNat 32 0xC from rfl, add_ofNat_assoc]
      exact F2 _ (by omega) (Or.inl (by omega))).trans mc
  · exact (memLoad32_congr (M := M1) (M' := M2) fun j hj => by
      rw [show F + (0x10 : Word) = F + BitVec.ofNat 32 0x10 from rfl, add_ofNat_assoc]
      exact F2 _ (by omega) (Or.inl (by omega))).trans m10
  · exact (memLoad32_congr (M := M1) (M' := M2) fun j hj => by
      rw [show F + (0xD0 : Word) = F + BitVec.ofNat 32 0xD0 from rfl, add_ofNat_assoc]
      exact F2 _ (by omega) (Or.inl (by omega))).trans md0
  · rw [F2 c h1 h3]
    exact fr1 _ (by have := C.offs (c := 0) (n := 0x128) (d := c) (k := 1) (Or.inl h2) (by decide) (by omega)
                    rwa [add_ofNat_zero] at this)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0xF1E: `s` is canonical when `pack(sub(limbs, L))` equals
its bytes at `F + 0x330` and the flag at `F + 0xD0` is set; to offset
0xF70 when it is and to the epilogue with `a0 = 0` when not. -/
theorem ev_canon (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0xF1E)
    {b : Bool} (hD0 : memLoad32 M (F + 0xD0) = if b then 1 else 0) :
    ∃ n' M', Steps n n' ∧
      ((decide (memBytes M (F + BitVec.ofNat 32 0x330) 32 = evPackS (ssAw M (F + BitVec.ofNat 32 0x9F0))) && b) = false →
        EvSt M0 Ms F r0 M' n' 0x100A ∧ reg n' a0 = 0) ∧
      ((decide (memBytes M (F + BitVec.ofNat 32 0x330) 32 = evPackS (ssAw M (F + BitVec.ofNat 32 0x9F0))) && b) = true →
        EvSt M0 Ms F r0 M' n' 0xF70) ∧
      (∀ q : Fin 32, q.val ∈ [19, 27] → reg n' q = reg n q) ∧ reg n' 8 = F + BitVec.ofNat 32 0x330 ∧
      (∀ c, c < 0x16A0 → (c < 0x350 ∨ (0x374 ≤ c ∧ c < 0x9F0) ∨ 0xA10 ≤ c) →
        M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c)) := by
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0xF28)
    [.aluImm .add a0 sp 0x350, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x1F1]
    (blockEnd_cons' ev_at_f1e rfl (blockEnd_cons' ev_at_f20 rfl (blockEnd_cons' ev_at_f24 rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n2, c2, D2, k2, o2, f2⟩ := D1.s29sub C (d := 0x350) (e := 0x9F0) ev_at_f28 ev_at_f2c (by decide) (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; rfl)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp,
      show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨n3, c3, D3, hr3⟩ := D2.block C (off' := 0xF3A)
    [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x1F1, .aluImm .add a1 sp 0x350]
    (blockEnd_cons' ev_at_f30 rfl (blockEnd_cons' ev_at_f34 rfl (blockEnd_cons' ev_at_f38 rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n4, c4, D4, k4, o4, f4⟩ := D3.s29pack C (d := 0x9F0) (e := 0x350) ev_at_f3a ev_at_f3e (by decide) (by decide)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D2.hsp,
      show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D2.hsp]; rfl)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0xF4E)
    [.aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x1F1, .aluImm .add (8 : Fin 32) sp 0x330, .alu .add a0 x0 (8 : Fin 32)]
    (blockEnd_cons' ev_at_f42 rfl (blockEnd_cons' ev_at_f46 rfl (blockEnd_cons' ev_at_f4a rfl
      (blockEnd_cons' ev_at_f4c rfl rfl)))) ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have v8 : reg n5 8 = F + BitVec.ofNat 32 0x330 := by
    rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; rfl
  obtain ⟨n6, c6, D6, k6, a06, f6⟩ := D5.ctEqSlice C (p := F + BitVec.ofNat 32 0x330) (q := F + BitVec.ofNat 32 0x9F0)
    ev_at_f4e ev_at_f52 (by decide) (by decide)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; exact BitVec.zero_add _)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp,
      show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (C.zF (by decide)).symm (C.zF (by decide)).symm
  -- What `ct_eq` compared.
  have fr4 : ∀ c, c < 0x16A0 → (c < 0x350 ∨ (0x374 ≤ c ∧ c < 0x9F0) ∨ 0xA10 ≤ c) →
      n4.mem (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := fun c h1 h2 => by
    rw [f4 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega)),
      f2 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega))]
  have b330 : memBytes n4.mem (F + BitVec.ofNat 32 0x330) 32 = memBytes M (F + BitVec.ofNat 32 0x330) 32 :=
    memBytes_congr fun i hi => by rw [add_ofNat_assoc]; exact fr4 _ (by omega) (Or.inl (by omega))
  have b9F0 : memBytes n4.mem (F + BitVec.ofNat 32 0x9F0) 32 = evPackS (ssAw M (F + BitVec.ofNat 32 0x9F0)) := by
    unfold memBytes evPackS
    refine List.map_congr_left fun j hj => ?_
    rw [o4 j (List.mem_range.mp hj)]
    exact congrArg _ (s29PackByte_congr (fun i hi => o2 i hi) j)
  rw [b330, b9F0] at a06
  generalize hP : decide (memBytes M (F + BitVec.ofNat 32 0x330) 32 = evPackS (ssAw M (F + BitVec.ofNat 32 0x9F0))) = P
  have a06' : reg n6 a0 = if P then 1 else 0 := by
    rw [a06, ← hP]
    by_cases h : memBytes M (F + BitVec.ofNat 32 0x330) 32 = evPackS (ssAw M (F + BitVec.ofNat 32 0x9F0))
    · rw [ite_eq_left h, decide_eq_true h]; rfl
    · rw [ite_eq_right h, decide_eq_false h]; rfl
  have fr6 : ∀ c, c < 0x16A0 → (c < 0x350 ∨ (0x374 ≤ c ∧ c < 0x9F0) ∨ 0xA10 ≤ c) →
      n6.mem (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := fun c h1 h2 => by
    rw [f6 _ (C.zF (by omega)), fr4 c h1 h2]
  have hD6 : memLoad32 n6.mem (F + 0xD0) = if b then 1 else 0 := by
    rw [← hD0]; exact memLoad32_congr fun j hj => by
      rw [show F + (0xD0 : Word) = F + BitVec.ofNat 32 0xD0 from rfl, add_ofNat_assoc]
      exact fr6 _ (by omega) (Or.inl (by omega))
  obtain ⟨n7, c7, D7, hr7⟩ := D6.block C (off' := 0xF5E)
    [.lw a1 sp 0xD0, .alu .and a0 a0 a1, .aluImm .and a0 a0 0xFF]
    (blockEnd_cons' ev_at_f56 rfl (blockEnd_cons' ev_at_f58 rfl (blockEnd_cons' ev_at_f5a rfl rfl)))
    ⟨by show (reg n6 sp + 0xD0).toNat % 4 = 0
        rw [D6.hsp, show F + (0xD0 : Word) = F + BitVec.ofNat 32 0xD0 from rfl]; exact C.al (by decide),
      trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have va7 : reg n7 a0 = if (P && b) then 1 else 0 := by
    rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D6.hsp, hD6, a06', ev_flag_and]
  obtain ⟨n8, c8, D8, k8, a08, f8⟩ := D7.blackBox C ev_at_f5e ev_at_f62 (by decide) (by decide)
  rw [va7, flag_bb] at a08
  obtain ⟨n9, c9, D9, hr9⟩ := D8.block C (off' := 0xF6C) [.aluImm .add a1 x0 1, .aluImm .and a0 a0 0xFF]
    (blockEnd_cons' ev_at_f66 rfl (blockEnd_cons' ev_at_f68 rfl rfl)) ⟨trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have va9 : reg n9 a0 = if (P && b) then 1 else 0 := by
    rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [a08, flag_ff]
  have va19 : reg n9 a1 = 1 := by
    rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.st.zero]; rfl
  have keep9 : ∀ q : Fin 32, q.val ∈ [8, 19, 27] → reg n9 q = reg n5 q := fun q hq => by
    rw [hr9, runBlock_reg _ _ _ q D8.st.zero (by revert hq; revert q; decide),
      k8 q (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      hr7, runBlock_reg _ _ _ q D6.st.zero (by revert hq; revert q; decide),
      k6 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide)]
  have keep5 : ∀ q : Fin 32, q.val ∈ [19, 27] → reg n5 q = reg n q := fun q hq => by
    rw [hr5, runBlock_reg _ _ _ q D4.st.zero (by revert hq; revert q; decide), k4 q (by revert hq; revert q; decide),
      hr3, runBlock_reg _ _ _ q D2.st.zero (by revert hq; revert q; decide), k2 q (by revert hq; revert q; decide),
      hr1, runBlock_reg _ _ _ q D.st.zero (by revert hq; revert q; decide)]
  have frm : ∀ c, c < 0x16A0 → (c < 0x350 ∨ (0x374 ≤ c ∧ c < 0x9F0) ∨ 0xA10 ≤ c) →
      n8.mem (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := fun c h1 h2 => by
    rw [f8 _ (C.zF (by omega)), fr6 c h1 h2]
  have hc9 := D9.code C
  cases hPb : (P && b) with
  | false =>
    obtain ⟨n10, d10, u10⟩ := D9.st.taken hc9 0x1008 ev_at_f6c (by decide) (by rw [va9, va19, hPb]; rfl)
    obtain ⟨n11, c11, D11, hr11⟩ := (D9.jmp u10).block C (off' := 0x100A) [.aluImm .add a0 x0 0]
      (bEnd1 ev_at_1008 rfl) ⟨trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    refine ⟨n11, n8.mem, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans
      (c9.trans (.cons d10 c11))))))))), fun _ => ⟨D11, ?_⟩, fun h => (by cases h), fun q hq => ?_, ?_, frm⟩
    · rw [hr11]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [u10.regs, D9.st.zero]; rfl
    · rw [hr11, runBlock_reg _ _ _ q (by rw [u10.regs]; exact D9.st.zero) (by revert hq; revert q; decide), u10.regs,
        keep9 q (by revert hq; revert q; decide), keep5 q hq]
    · rw [hr11, runBlock_reg _ _ _ 8 (by rw [u10.regs]; exact D9.st.zero) (by decide), u10.regs,
        keep9 8 (by decide), v8]
  | true =>
    obtain ⟨n10, d10, u10⟩ := D9.st.notTaken hc9 0xF70 ev_at_f6c (by decide) (by rw [va9, va19, hPb]; rfl)
    exact ⟨n10, n8.mem, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans
      (c9.trans (.single d10))))))))), fun h => (by cases h), fun _ => D9.jmp u10,
      fun q hq => by rw [u10.regs, keep9 q (by revert hq; revert q; decide), keep5 q hq],
      by rw [u10.regs, keep9 8 (by decide), v8], frm⟩

end

end C3.RV32
