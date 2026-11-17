import C3BootProofs.Proofs.Ed25519VerifyA

/-!
# `ed25519_verify`, offsets 0x104C to 0x158E: the challenge scalar

The hash `sha512 (R ‖ A ‖ M)` becomes the scalar `k`: its 64 bytes are read
as 16 little-endian words, split into a low and a high half of nine 29-bit
limbs, multiplied by `R` and `R²` in Montgomery form, added, reduced, and
packed. `kOf` is that computation on the digest's bytes.
-/

namespace C3.RV32

open C3.Image

/-- `k` bytes of `d` from offset `b`, little-endian. -/
def leL (d : List Nat) (b : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => leL d b j + d.getD (b + j) 0 * 256 ^ j

/-- The digest's low nine limbs, as `from_bytes_wide` splits them. -/
def lo9 (w : Nat → Nat) (i : Nat) : Nat :=
  if i = 0 then w 0 % 2 ^ 29 else
  if i = 1 then (w 0 / 2 ^ 29 + w 1 * 2 ^ 3) % 2 ^ 29 else
  if i = 2 then (w 1 / 2 ^ 26 + w 2 * 2 ^ 6) % 2 ^ 29 else
  if i = 3 then (w 2 / 2 ^ 23 + w 3 * 2 ^ 9) % 2 ^ 29 else
  if i = 4 then (w 3 / 2 ^ 20 + w 4 * 2 ^ 12) % 2 ^ 29 else
  if i = 5 then (w 4 / 2 ^ 17 + w 5 * 2 ^ 15) % 2 ^ 29 else
  if i = 6 then (w 5 / 2 ^ 14 + w 6 * 2 ^ 18) % 2 ^ 29 else
  if i = 7 then (w 6 / 2 ^ 11 + w 7 * 2 ^ 21) % 2 ^ 29 else
  if i = 8 then (w 7 / 2 ^ 8 + w 8 * 2 ^ 24) % 2 ^ 29 else
  0

/-- The digest's high nine limbs. -/
def hi9 (w : Nat → Nat) (i : Nat) : Nat :=
  if i = 0 then (w 8 / 2 ^ 5 + w 9 * 2 ^ 27) % 2 ^ 29 else
  if i = 1 then w 9 / 2 ^ 2 % 2 ^ 29 else
  if i = 2 then (w 9 / 2 ^ 31 + w 10 * 2 ^ 1) % 2 ^ 29 else
  if i = 3 then (w 10 / 2 ^ 28 + w 11 * 2 ^ 4) % 2 ^ 29 else
  if i = 4 then (w 11 / 2 ^ 25 + w 12 * 2 ^ 7) % 2 ^ 29 else
  if i = 5 then (w 12 / 2 ^ 22 + w 13 * 2 ^ 10) % 2 ^ 29 else
  if i = 6 then (w 13 / 2 ^ 19 + w 14 * 2 ^ 13) % 2 ^ 29 else
  if i = 7 then (w 14 / 2 ^ 16 + w 15 * 2 ^ 16) % 2 ^ 29 else
  if i = 8 then w 15 / 2 ^ 13 else
  0

theorem nat9 {P : Nat → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6)
    (h7 : P 7) (h8 : P 8) : ∀ i, i < 9 → P i
  | 0, _ => h0
  | 1, _ => h1
  | 2, _ => h2
  | 3, _ => h3
  | 4, _ => h4
  | 5, _ => h5
  | 6, _ => h6
  | 7, _ => h7
  | 8, _ => h8
  | _ + 9, h => absurd h (by omega)

theorem lo9_of {L w : Nat → Nat}
    (l0 : L 0 = w 0 % 2 ^ 29)
    (l1 : L 1 = (w 0 / 2 ^ 29 + w 1 * 2 ^ 3) % 2 ^ 29)
    (l2 : L 2 = (w 1 / 2 ^ 26 + w 2 * 2 ^ 6) % 2 ^ 29)
    (l3 : L 3 = (w 2 / 2 ^ 23 + w 3 * 2 ^ 9) % 2 ^ 29)
    (l4 : L 4 = (w 3 / 2 ^ 20 + w 4 * 2 ^ 12) % 2 ^ 29)
    (l5 : L 5 = (w 4 / 2 ^ 17 + w 5 * 2 ^ 15) % 2 ^ 29)
    (l6 : L 6 = (w 5 / 2 ^ 14 + w 6 * 2 ^ 18) % 2 ^ 29)
    (l7 : L 7 = (w 6 / 2 ^ 11 + w 7 * 2 ^ 21) % 2 ^ 29)
    (l8 : L 8 = (w 7 / 2 ^ 8 + w 8 * 2 ^ 24) % 2 ^ 29) :
    (fun i => if i < 9 then L i else 0) = lo9 w := by
  funext i
  by_cases hi : i < 9
  · simp only [hi, ↓reduceIte]
    refine nat9 (P := fun i => L i = lo9 w i) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ i hi <;>
      simp only [lo9, Nat.reduceEqDiff, ↓reduceIte] <;> assumption
  · simp only [hi, ↓reduceIte, lo9, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show i ≠ 3 by omega, show i ≠ 4 by omega,
      show i ≠ 5 by omega, show i ≠ 6 by omega, show i ≠ 7 by omega, show i ≠ 8 by omega]

theorem hi9_of {L w : Nat → Nat}
    (l0 : L 0 = (w 8 / 2 ^ 5 + w 9 * 2 ^ 27) % 2 ^ 29)
    (l1 : L 1 = w 9 / 2 ^ 2 % 2 ^ 29)
    (l2 : L 2 = (w 9 / 2 ^ 31 + w 10 * 2 ^ 1) % 2 ^ 29)
    (l3 : L 3 = (w 10 / 2 ^ 28 + w 11 * 2 ^ 4) % 2 ^ 29)
    (l4 : L 4 = (w 11 / 2 ^ 25 + w 12 * 2 ^ 7) % 2 ^ 29)
    (l5 : L 5 = (w 12 / 2 ^ 22 + w 13 * 2 ^ 10) % 2 ^ 29)
    (l6 : L 6 = (w 13 / 2 ^ 19 + w 14 * 2 ^ 13) % 2 ^ 29)
    (l7 : L 7 = (w 14 / 2 ^ 16 + w 15 * 2 ^ 16) % 2 ^ 29)
    (l8 : L 8 = w 15 / 2 ^ 13) :
    (fun i => if i < 9 then L i else 0) = hi9 w := by
  funext i
  by_cases hi : i < 9
  · simp only [hi, ↓reduceIte]
    refine nat9 (P := fun i => L i = hi9 w i) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ i hi <;>
      simp only [hi9, Nat.reduceEqDiff, ↓reduceIte] <;> assumption
  · simp only [hi, ↓reduceIte, hi9, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show i ≠ 3 by omega, show i ≠ 4 by omega,
      show i ≠ 5 by omega, show i ≠ 6 by omega, show i ≠ 7 by omega, show i ≠ 8 by omega]

/-- `Scalar::from_bytes_mod_order_wide(d).to_bytes()` as the code computes it,
with the limbs `R` and `RR` of the Montgomery constants `R` and `R²`. -/
def kOf (R RR : Nat → Nat) (d : List Nat) : List Nat :=
  evPackS fun j => s29AddC (s29Out (smmRed (hi9 fun t => leL d (4 * t) 4 % 2 ^ 32) RR))
    (s29Out (smmRed (lo9 fun t => leL d (4 * t) 4 % 2 ^ 32) R)) (j + 1) % 2 ^ 29

theorem leAcc_leL {M : Word → BitVec 8} {a : Word} {n b : Nat} :
    ∀ k, b + k ≤ n → leAcc M (a + BitVec.ofNat 32 b) k = leL (memBytes M a n) b k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [leAcc, leL]
    rw [leAcc_leL (n := n) k (by omega), memBytes_getD (n := n) (i := b + k) (by omega), add_ofNat_assoc]

theorem s29AddC_congr {a a' b b' : Nat → Nat} :
    ∀ k, (∀ i, i < k → a i = a' i) → (∀ i, i < k → b i = b' i) → s29AddC a b k = s29AddC a' b' k
  | 0, _, _ => rfl
  | k + 1, ha, hb => by
    simp only [s29AddC]
    rw [s29AddC_congr k (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega)), ha k (by omega), hb k (by omega)]

theorem s29Out_lt29 (a : Nat → Nat) (j : Nat) : s29Out a j < 2 ^ 29 := by
  unfold s29Out; exact Nat.mod_lt _ (by decide)

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
/-- **The challenge scalar**, from offset 0x104C. -/
theorem ev_stageB (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x104C)
    (h19 : reg n 19 = F + 0x90F) (h27 : reg n 27 = 0x1FFFFFFF) (hm : memLoad32 M (F + BitVec.ofNat 32 0xC) = msg)
    (hk : memLoad32 M (F + BitVec.ofNat 32 0x10) = BitVec.ofNat 32 len) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x158E ∧ reg n' 18 = F + BitVec.ofNat 32 0x7F0 ∧
      reg n' 23 = F + BitVec.ofNat 32 0x1508 ∧
      memBytes M' (F + BitVec.ofNat 32 0x520) 32 = kOf (smmIn M0 (BitVec.ofNat 32 0x3FCC49E4))
        (smmIn M0 (BitVec.ofNat 32 0x3FCC49C0)) (sha512 (memBytes M (F + BitVec.ofNat 32 0x228) 32 ++
          memBytes M (F + BitVec.ofNat 32 0x128) 32 ++ memBytes M0 msg len)) ∧
      (∀ j, j < 0xC0 → M' (F + BitVec.ofNat 32 (0x5E0 + j)) = M (F + BitVec.ofNat 32 (0x128 + j))) ∧
      (∀ j, j < 0x40 → M' (F + BitVec.ofNat 32 (0x6A0 + j)) = M (F + BitVec.ofNat 32 (0x228 + j))) ∧
      ∀ c, c < 0x308 → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  obtain ⟨n1, M1, c1, D1, k1, r23, E1, cpA, cpB, fr1⟩ := ev_hash C D h19 hm hk
  obtain ⟨n2, M2, c2, D2, k2, w2, -, -, fr2⟩ := ev_dw C D1
  have r19 : reg n2 19 = F + 0x90F := by
    rw [k2 19 (by decide) (by decide) (by decide) (by decide), k1 19 (by decide) (by decide), h19]
  have r23' : reg n2 23 = F + BitVec.ofNat 32 0x1508 := by
    rw [k2 23 (by decide) (by decide) (by decide) (by decide), r23]
  have r27 : reg n2 27 = 0x1FFFFFFF := by
    rw [k2 27 (by decide) (by decide) (by decide) (by decide), k1 27 (by decide) (by decide), h27]
  obtain ⟨n3, M3, c3, D3, k3, lo3, r7, r9, r13, r6, fr3⟩ := ev_fbw1 C D2 r19 r23' r27
  obtain ⟨n4, M4, c4, D4, k4, hi4, a0_4, a1_4, a2_4, fr4⟩ := ev_fbw2 C D3 (Mo := M2)
    (by rw [k3 19 (by decide) (by decide) (by decide), r19]) (by rw [k3 23 (by decide) (by decide) (by decide), r23'])
    (by rw [k3 27 (by decide) (by decide) (by decide), r27]) r7 r9 r13 r6
    (fun c h1 h2 => fr3 c (by omega) (Or.inl (by omega)))
  obtain ⟨n5, M5, c5, D5, k5, mlo, mhi, -, fr5⟩ := ev_mm C D4 a0_4 a1_4 a2_4
  obtain ⟨n6, M6, c6, D6, add6, fr6, k6⟩ := ev_s29add C D5
    (by rw [k5 27 (by decide), k4 27 (by decide) (by decide) (by decide), k3 27 (by decide) (by decide) (by decide), r27])
    (fun t ht => by rw [mhi t ht]; exact s29Out_lt29 _ _) (fun t ht => by rw [mlo t ht]; exact s29Out_lt29 _ _)
  obtain ⟨n7, M7, c7, D7, k7, r18, pk7, fr7⟩ := ev_kpack C D6
  -- the digest's words
  have hW : ∀ t, t < 16 → (memLoad32 M2 (F + BitVec.ofNat 32 (0x9F0 + 4 * t))).toNat =
      leL (sha512 (memBytes M (F + BitVec.ofNat 32 0x228) 32 ++ memBytes M (F + BitVec.ofNat 32 0x128) 32 ++
        memBytes M0 msg len)) (4 * t) 4 % 2 ^ 32 := fun t ht => by
    rw [w2 t ht, BitVec.toNat_ofNat, ← add_ofNat_assoc, leAcc_leL (n := 64) 4 (by omega), E1]
  generalize sha512 (memBytes M (F + BitVec.ofNat 32 0x228) 32 ++ memBytes M (F + BitVec.ofNat 32 0x128) 32 ++
    memBytes M0 msg len) = d at hW ⊢
  have w : ∀ t, t < 16 → ∀ a : Nat, a = 0x9F0 + 4 * t →
      (memLoad32 M2 (F + BitVec.ofNat 32 a)).toNat = leL d (4 * t) 4 % 2 ^ 32 := fun t ht a ha => by
    rw [ha]; exact hW t ht
  have eLo : smmIn M4 (F + BitVec.ofNat 32 0x1508) = lo9 fun t => leL d (4 * t) 4 % 2 ^ 32 := by
    rw [smmIn_congr (M := M3) (M' := M4) (p := F + BitVec.ofNat 32 0x1508) fun i hi => by
      rw [add_ofNat_assoc]; exact fr4 _ (by omega) (Or.inl (by omega))]
    obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := lo3
    rw [w 0 (by decide) 0x9F0 rfl] at l0 l1
    rw [w 1 (by decide) 0x9F4 rfl] at l1 l2
    rw [w 2 (by decide) 0x9F8 rfl] at l2 l3
    rw [w 3 (by decide) 0x9FC rfl] at l3 l4
    rw [w 4 (by decide) 0xA00 rfl] at l4 l5
    rw [w 5 (by decide) 0xA04 rfl] at l5 l6
    rw [w 6 (by decide) 0xA08 rfl] at l6 l7
    rw [w 7 (by decide) 0xA0C rfl] at l7 l8
    rw [w 8 (by decide) 0xA10 rfl] at l8
    exact lo9_of l0 l1 l2 l3 l4 l5 l6 l7 l8
  have eHi : smmIn M4 (F + BitVec.ofNat 32 0x15A8) = hi9 fun t => leL d (4 * t) 4 % 2 ^ 32 := by
    obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := hi4
    rw [w 8 (by decide) 0xA10 rfl] at l0
    rw [w 9 (by decide) 0xA14 rfl] at l0 l1 l2
    rw [w 10 (by decide) 0xA18 rfl] at l2 l3
    rw [w 11 (by decide) 0xA1C rfl] at l3 l4
    rw [w 12 (by decide) 0xA20 rfl] at l4 l5
    rw [w 13 (by decide) 0xA24 rfl] at l5 l6
    rw [w 14 (by decide) 0xA28 rfl] at l6 l7
    rw [w 15 (by decide) 0xA2C rfl] at l7 l8
    exact hi9_of l0 l1 l2 l3 l4 l5 l6 l7 l8
  rw [eLo] at mlo
  rw [eHi] at mhi
  refine ⟨n7, M7, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans c7))))), D7, r18,
    by rw [k7 23 (by decide) (by decide), k6 23 (by decide) (by decide), k5 23 (by decide),
      k4 23 (by decide) (by decide) (by decide), k3 23 (by decide) (by decide) (by decide), r23'], ?_,
    fun j hj => ?_, fun j hj => ?_, fun c hc => ?_⟩
  · rw [pk7]
    exact evPackS_congr fun j hj => by
      refine (add6 j hj).trans ?_
      congr 1
      exact s29AddC_congr _ (fun i hi => mhi i (by omega)) (fun i hi => mlo i (by omega))
  · rw [fr7 _ (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩)), fr6 _ (by omega) (Or.inl (by omega)),
      fr5 _ (by omega) (Or.inl (by omega)), fr4 _ (by omega) (Or.inl (by omega)), fr3 _ (by omega) (Or.inl (by omega)),
      fr2 _ (by omega) (Or.inl (by omega)), cpA j hj]
  · rw [fr7 _ (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩)), fr6 _ (by omega) (Or.inl (by omega)),
      fr5 _ (by omega) (Or.inl (by omega)), fr4 _ (by omega) (Or.inl (by omega)), fr3 _ (by omega) (Or.inl (by omega)),
      fr2 _ (by omega) (Or.inl (by omega)), cpB j hj]
  · rw [fr7 _ (by omega) (Or.inl (by omega)), fr6 _ (by omega) (Or.inl (by omega)),
      fr5 _ (by omega) (Or.inl (by omega)), fr4 _ (by omega) (Or.inl (by omega)), fr3 _ (by omega) (Or.inl (by omega)),
      fr2 _ (by omega) (Or.inl (by omega)), fr1 _ (by omega) (Or.inl hc)]

end

end C3.RV32



