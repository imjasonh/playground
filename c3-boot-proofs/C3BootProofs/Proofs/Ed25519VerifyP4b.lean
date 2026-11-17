import C3BootProofs.Proofs.Ed25519VerifyP4
import C3BootProofs.Proofs.ShaPad5

/-!
# `ed25519_verify`, offsets 0x115A to 0x12CE: SHA-512's `finalize`, inlined

The function pads the hasher's buffer at `F + 0xEF0` (0x80, zeros, and the
message's length in bits as a 128-bit big-endian integer), compresses the
one or two blocks that makes into the hash value at `F + 0xF70`, and writes
the 8 hash words big-endian to `F + 0x9F0`.
-/

namespace C3.RV32

open C3.Image

set_option maxRecDepth 10000 in
set_option linter.unusedSimpArgs false in
/-- The low word of the length in bits, as `finalize` swaps it. -/
theorem lenLo5_eq (lo pos : Word) (hp : ∀ k, 7 ≤ k → pos.getLsbD k = false) :
    ((((lo <<< 2) &&& 0xFF00) ||| ((lo <<< 10) >>> 24)) ||| (pos <<< 27)) |||
      ((((pos <<< 3) ||| (lo <<< 10)) &&& 0xFF00) <<< 8) = bswap32 ((lo <<< 10) ||| (pos <<< 3)) := by
  apply BitVec.eq_of_getLsbD_eq
  unfold bswap32
  apply lt32_cases
  all_goals simp +decide [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, BitVec.getLsbD_extractLsb', tbFF00_0, tbFF00_1, tbFF00_2, tbFF00_3, tbFF00_4, tbFF00_5, tbFF00_6, tbFF00_7, tbFF00_8, tbFF00_9, tbFF00_10, tbFF00_11, tbFF00_12, tbFF00_13, tbFF00_14, tbFF00_15, tbFF00_16, tbFF00_17, tbFF00_18, tbFF00_19, tbFF00_20, tbFF00_21, tbFF00_22, tbFF00_23, tbFF00_24, tbFF00_25, tbFF00_26, tbFF00_27, tbFF00_28, tbFF00_29, tbFF00_30, tbFF00_31, -BitVec.getLsbD_eq_getElem, hp]

set_option maxRecDepth 10000 in
set_option linter.unusedSimpArgs false in
/-- The second word of the length in bits, as `finalize` swaps it when the
block count's high words are zero. -/
theorem lenHi5_eq (lo : Word) :
    ((lo >>> 22) <<< 24 ||| ((((0 : Word) <<< 2) &&& 0xFF00) ||| (((0 : Word) <<< 10) >>> 24))) |||
      (((((0 : Word) <<< 10) ||| (lo >>> 22)) &&& 0xFF00) <<< 8) = bswap32 (lo >>> 22) := by
  apply BitVec.eq_of_getLsbD_eq
  unfold bswap32
  apply lt32_cases
  all_goals simp +decide [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, BitVec.getLsbD_extractLsb', tbFF00_0, tbFF00_1, tbFF00_2, tbFF00_3, tbFF00_4, tbFF00_5, tbFF00_6, tbFF00_7, tbFF00_8, tbFF00_9, tbFF00_10, tbFF00_11, tbFF00_12, tbFF00_13, tbFF00_14, tbFF00_15, tbFF00_16, tbFF00_17, tbFF00_18, tbFF00_19, tbFF00_20, tbFF00_21, tbFF00_22, tbFF00_23, tbFF00_24, tbFF00_25, tbFF00_26, tbFF00_27, tbFF00_28, tbFF00_29, tbFF00_30, tbFF00_31, -BitVec.getLsbD_eq_getElem, BitVec.getLsbD_of_ge]

theorem xor127 : ∀ p, p < 128 → p ^^^ 127 = 127 - p := by decide

set_option maxRecDepth 10000 in
theorem lenLo5_toNat (lo pos : Word) (hp : ∀ k, 7 ≤ k → pos.getLsbD k = false) :
    ((lo <<< 10) ||| (pos <<< 3)).toNat = (lo.toNat * 1024 + pos.toNat * 8) % 2 ^ 32 := by
  rw [← Sha256.add_disj (by
      apply lt32_cases
      all_goals simp +decide [BitVec.getLsbD_shiftLeft, hp, -BitVec.getLsbD_eq_getElem]),
    BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  omega

set_option maxRecDepth 20000 in
/-- The four words `finalize` stores in the buffer's last 16 bytes are the
message's length in bits, a 128-bit big-endian integer. -/
theorem len_bytes5 (M : Word → BitVec 8) (P lo : Word) (pos : Nat) (hp : pos < 128) :
    memBytes (memStore32 (memStore32 (memStore32 (memStore32 M P 0) (P + BitVec.ofNat 32 4) 0)
      (P + BitVec.ofNat 32 8) (bswap32 (lo >>> 22))) (P + BitVec.ofNat 32 12)
      (bswap32 ((lo <<< 10) ||| (BitVec.ofNat 32 pos <<< 3)))) P 16 =
      Sha512.be128 (8 * (128 * lo.toNat + pos)) := by
  have hpb : ∀ k, 7 ≤ k → (BitVec.ofNat 32 pos).getLsbD k = false := fun k hk =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by rw [BitVec.toNat_ofNat]; omega)
      (Nat.pow_le_pow_right (by decide) hk : 2 ^ 7 ≤ 2 ^ k))
  have hpn : (BitVec.ofNat 32 pos).toNat = pos := by rw [BitVec.toNat_ofNat]; omega
  have hl := lo.isLt
  have ne : ∀ c d, c < 16 → d < 16 → c ≠ d → P + BitVec.ofNat 32 c ≠ P + BitVec.ofNat 32 d :=
    fun c d hc hd h => add_ofNat_ne P (by omega) (by omega) h
  have out : ∀ (M' : Word → BitVec 8) (v : Word) (b c : Nat), b + 4 ≤ 16 → c < 16 → (c < b ∨ b + 4 ≤ c) →
      memStore32 M' (P + BitVec.ofNat 32 b) v (P + BitVec.ofNat 32 c) = M' (P + BitVec.ofNat 32 c) :=
    fun M' v b c hb hc h => memStore32_ne fun i hi => by
      rw [add_ofNat_assoc]; exact ne c (b + i) hc (by omega) (by omega)
  have at_ : ∀ (M' : Word → BitVec 8) (v : Word) (b k : Nat), k < 4 →
      memStore32 M' (P + BitVec.ofNat 32 b) v (P + BitVec.ofNat 32 (b + k)) = v.extractLsb' (8 * k) 8 :=
    fun M' v b k hk => by rw [← add_ofNat_assoc]; exact store32_byte _ _ _ k hk
  have b3 : ∀ k, k < 4 → (memStore32 (memStore32 (memStore32 (memStore32 M P 0) (P + BitVec.ofNat 32 4) 0)
      (P + BitVec.ofNat 32 8) (bswap32 (lo >>> 22))) (P + BitVec.ofNat 32 12)
      (bswap32 ((lo <<< 10) ||| (BitVec.ofNat 32 pos <<< 3))) (P + BitVec.ofNat 32 (12 + k))).toNat =
      (lo.toNat * 1024 + pos * 8) % 2 ^ 32 / 2 ^ (8 * (3 - k)) % 256 := fun k hk => by
    rw [at_ _ _ 12 k hk, bswap32_byte _ k hk, byte_toNat, lenLo5_toNat _ _ hpb, hpn]
  have b2 : ∀ k, k < 4 → (memStore32 (memStore32 (memStore32 (memStore32 M P 0) (P + BitVec.ofNat 32 4) 0)
      (P + BitVec.ofNat 32 8) (bswap32 (lo >>> 22))) (P + BitVec.ofNat 32 12)
      (bswap32 ((lo <<< 10) ||| (BitVec.ofNat 32 pos <<< 3))) (P + BitVec.ofNat 32 (8 + k))).toNat =
      lo.toNat / 2 ^ 22 / 2 ^ (8 * (3 - k)) % 256 := fun k hk => by
    rw [out _ _ 12 _ (by decide) (by omega) (Or.inl (by omega)), at_ _ _ 8 k hk, bswap32_byte _ k hk, byte_toNat,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have b1 : ∀ k, k < 4 → (memStore32 (memStore32 (memStore32 (memStore32 M P 0) (P + BitVec.ofNat 32 4) 0)
      (P + BitVec.ofNat 32 8) (bswap32 (lo >>> 22))) (P + BitVec.ofNat 32 12)
      (bswap32 ((lo <<< 10) ||| (BitVec.ofNat 32 pos <<< 3))) (P + BitVec.ofNat 32 (4 + k))).toNat = 0 := fun k hk => by
    rw [out _ _ 12 _ (by decide) (by omega) (Or.inl (by omega)), out _ _ 8 _ (by decide) (by omega) (Or.inl (by omega)),
      at_ _ _ 4 k hk, byte_toNat]; simp
  have b0 : ∀ k, k < 4 → (memStore32 (memStore32 (memStore32 (memStore32 M P 0) (P + BitVec.ofNat 32 4) 0)
      (P + BitVec.ofNat 32 8) (bswap32 (lo >>> 22))) (P + BitVec.ofNat 32 12)
      (bswap32 ((lo <<< 10) ||| (BitVec.ofNat 32 pos <<< 3))) (P + BitVec.ofNat 32 k)).toNat = 0 := fun k hk => by
    rw [out _ _ 12 _ (by decide) (by omega) (Or.inl (by omega)), out _ _ 8 _ (by decide) (by omega) (Or.inl (by omega)),
      out _ _ 4 _ (by decide) (by omega) (Or.inl (by omega)), ← add_ofNat_zero P,
      show (P + BitVec.ofNat 32 0) + BitVec.ofNat 32 k = (P + BitVec.ofNat 32 0) + BitVec.ofNat 32 k from rfl,
      add_ofNat_zero, store32_byte _ _ _ k hk, byte_toNat]; simp
  unfold memBytes Sha512.be128
  rw [show List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from rfl]
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have h0 := b0 0 (by decide); have h1 := b0 1 (by decide); have h2 := b0 2 (by decide); have h3 := b0 3 (by decide)
  have h4 := b1 0 (by decide); have h5 := b1 1 (by decide); have h6 := b1 2 (by decide); have h7 := b1 3 (by decide)
  have h8 := b2 0 (by decide); have h9 := b2 1 (by decide); have h10 := b2 2 (by decide); have h11 := b2 3 (by decide)
  have h12 := b3 0 (by decide); have h13 := b3 1 (by decide); have h14 := b3 2 (by decide); have h15 := b3 3 (by decide)
  simp only [Nat.add_zero] at h4 h8 h12
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The 8 bytes that 8 byte stores at `P` to `P + 7` leave there. -/
theorem rd8 (M : Word → BitVec 8) (P : Word) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    memBytes (memStore8 (memStore8 (memStore8 (memStore8 (memStore8 (memStore8 (memStore8 (memStore8 M
      (P + BitVec.ofNat 32 4) b4) (P + BitVec.ofNat 32 5) b5) (P + BitVec.ofNat 32 6) b6) (P + BitVec.ofNat 32 7) b7)
      (P + BitVec.ofNat 32 0) b0) (P + BitVec.ofNat 32 1) b1) (P + BitVec.ofNat 32 2) b2) (P + BitVec.ofNat 32 3) b3)
      P 8 = [b0.toNat, b1.toNat, b2.toNat, b3.toNat, b4.toNat, b5.toNat, b6.toNat, b7.toNat] := by
  unfold memBytes
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp +decide only [memStore8, BitVec.add_right_inj, ↓reduceIte]

/-- A 64-bit word's bytes, big-endian, from its low and high halves. -/
theorem wordBytes_pk (l h : Word) : Sha512.wordBytes (pk l h) =
    [h.toNat / 2 ^ 24 % 256, h.toNat / 2 ^ 16 % 256, h.toNat / 2 ^ 8 % 256, h.toNat % 256,
     l.toNat / 2 ^ 24 % 256, l.toNat / 2 ^ 16 % 256, l.toNat / 2 ^ 8 % 256, l.toNat % 256] := by
  have hl := l.isLt
  have hh := h.isLt
  unfold Sha512.wordBytes pk
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.map_cons, List.map_nil,
    List.cons.injEq, and_true, Nat.reducePow, Nat.reduceMul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Word `k` of the 64-byte hash value at `stp`. -/
def hvW (M : Word → BitVec 8) (stp : Word) (k : Nat) : Sha512.W64 :=
  pk (memLoad32 M (stp + BitVec.ofNat 32 (8 * k))) (memLoad32 M (stp + BitVec.ofNat 32 (8 * k + 4)))

theorem s5Hv_toList (M : Word → BitVec 8) (stp : Word) : (s5Hv M stp).toList = (List.range 8).map (hvW M stp) := by
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.map_cons, List.map_nil, hvW]
  rfl

theorem flatMap_range_succ (f : Nat → Sha512.W64) (k : Nat) :
    ((List.range (k + 1)).map f).flatMap Sha512.wordBytes =
      ((List.range k).map f).flatMap Sha512.wordBytes ++ Sha512.wordBytes (f k) := by
  rw [List.range_succ, List.map_append, List.flatMap_append]; simp

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}

theorem ev_a3 (F : Word) (o : Nat) : F + 0x90F + BitVec.ofNat 32 o = F + BitVec.ofNat 32 (0x90F + o) :=
  add_ofNat_assoc F 0x90F o

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x115A: the block count and the buffer's byte count loaded
from the hasher, the length in bits computed byte-swapped into `s4` to `s7`,
`127 - pos` into `s2`, and the buffer's next byte and 0x80 into `a0` and
`a1`. -/
theorem ev_flen (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x115A)
    (h19 : reg n 19 = F + 0x90F) (h26 : reg n 26 = F + BitVec.ofNat 32 0xEF0) {h : Bytes}
    (H : S5U.Hasher5At M (F + BitVec.ofNat 32 0xEF0) h) :
    ∃ n', Steps n n' ∧ EvSt M0 Ms F r0 M n' 0x1210 ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q.val ∉ [8, 18, 20, 21, 22, 23, 25] → reg n' q = reg n q) ∧
      reg n' 20 = bswap32 ((BitVec.ofNat 32 (h.length / 128) <<< 10) ||| (BitVec.ofNat 32 (h.length % 128) <<< 3)) ∧
      reg n' 21 = bswap32 (BitVec.ofNat 32 (h.length / 128) >>> 22) ∧ reg n' 22 = 0 ∧ reg n' 23 = 0 ∧
      reg n' 18 = BitVec.ofNat 32 (127 - h.length % 128) ∧ reg n' 25 = BitVec.ofNat 32 (h.length % 128) ∧
      reg n' a0 = F + BitVec.ofNat 32 (0xEF0 + h.length % 128) ∧ reg n' a1 = 0x80 := by
  have z0 := D.st.zero
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x115E) [.aluImm .add a0 (19 : Fin 32) 0x681] (bEnd1 ev_at_115a rfl)
    ⟨trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have k1 : ∀ q : Fin 32, q ≠ a0 → reg n1 q = reg n q := fun q hq => by
    rw [hr1]; simp only [runBlock, BInstr.run]; exact upd_ne' hq z0
  have va0 : reg n1 a0 = F + BitVec.ofNat 32 0xF90 := by
    rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [h19]; exact ev_a3 F 0x681
  have v19 : reg n1 19 = F + 0x90F := by rw [k1 _ (by decide), h19]
  have a0o : ∀ o : Nat, F + BitVec.ofNat 32 0xF90 + BitVec.ofNat 32 o = F + BitVec.ofNat 32 (0xF90 + o) :=
    fun o => add_ofNat_assoc F 0xF90 o
  have e1 : (reg n1 a0 + 0x28).toNat % 4 = 0 := by rw [va0, show F + BitVec.ofNat 32 0xF90 + 0x28 = F + BitVec.ofNat 32 0xFB8 from a0o 0x28]; exact C.al (by decide)
  have e2 : (reg n1 a0 + 0x24).toNat % 4 = 0 := by rw [va0, show F + BitVec.ofNat 32 0xF90 + 0x24 = F + BitVec.ofNat 32 0xFB4 from a0o 0x24]; exact C.al (by decide)
  have e3 : (reg n1 19 + 0x6AD).toNat % 4 = 0 := by rw [v19, show F + 0x90F + 0x6AD = F + BitVec.ofNat 32 0xFBC from ev_a3 F 0x6AD]; exact C.al (by decide)
  have e4 : (reg n1 a0 + 0x20).toNat % 4 = 0 := by rw [va0, show F + BitVec.ofNat 32 0xF90 + 0x20 = F + BitVec.ofNat 32 0xFB0 from a0o 0x20]; exact C.al (by decide)
  obtain ⟨n2, c2, D2, hr2⟩ := D1.block C (off' := 0x1210)
    ((.lw a1 a0 0x28) :: (.lw a2 a0 0x24) :: (.lw (17 : Fin 32) (19 : Fin 32) 0x6AD) :: (.lw a4 a0 0x20) :: (.lbu (25 : Fin 32) (19 : Fin 32) 0x660) :: (.aluImm .srl a6 a1 0x16) :: (.aluImm .sll (5 : Fin 32) (17 : Fin 32) 0xA) :: (.aluImm .srl (6 : Fin 32) a2 0x16) :: (.aluImm .sll (30 : Fin 32) a1 0xA) :: (.aluImm .srl (31 : Fin 32) a4 0x16) :: (.aluImm .sll a5 a2 0xA) :: (.alu .or (7 : Fin 32) (5 : Fin 32) a6) :: (.alu .or (28 : Fin 32) (30 : Fin 32) (6 : Fin 32)) :: (.alu .or (29 : Fin 32) a5 (31 : Fin 32)) :: (.aluImm .sll (8 : Fin 32) a4 0xA) :: (.aluImm .sll a0 (25 : Fin 32) 0x3) :: (.alu .or a0 a0 (8 : Fin 32)) :: (.lui (18 : Fin 32) 0x10000) :: (.aluImm .sll a4 a4 0x2) :: (.aluImm .add a3 (18 : Fin 32) 0xFFFFFF00) :: (.alu .and a4 a4 a3) :: (.aluImm .srl (8 : Fin 32) (8 : Fin 32) 0x18) :: (.alu .or a4 a4 (8 : Fin 32)) :: (.alu .and a0 a0 a3) :: (.aluImm .sll a0 a0 0x8) :: (.aluImm .sll (8 : Fin 32) (25 : Fin 32) 0x1B) :: (.alu .or a4 a4 (8 : Fin 32)) :: (.aluImm .sll a2 a2 0x2) :: (.alu .and a2 a2 a3) :: (.aluImm .srl a5 a5 0x18) :: (.alu .or (20 : Fin 32) a4 a0) :: (.alu .or a2 a2 a5) :: (.alu .and a0 (29 : Fin 32) a3) :: (.aluImm .sll (31 : Fin 32) (31 : Fin 32) 0x18) :: (.aluImm .sll a0 a0 0x8) :: (.alu .or a2 (31 : Fin 32) a2) :: (.alu .or (21 : Fin 32) a2 a0) :: (.aluImm .sll a1 a1 0x2) :: (.alu .and a1 a1 a3) :: (.aluImm .srl a0 (30 : Fin 32) 0x18) :: (.alu .or a0 a0 a1) :: (.alu .and a1 (28 : Fin 32) a3) :: (.aluImm .sll a1 a1 0x8) :: (.aluImm .sll (6 : Fin 32) (6 : Fin 32) 0x18) :: (.alu .or a0 (6 : Fin 32) a0) :: (.aluImm .sll (17 : Fin 32) (17 : Fin 32) 0x2) :: (.alu .and a2 (17 : Fin 32) a3) :: (.aluImm .srl a4 (5 : Fin 32) 0x18) :: (.alu .or (22 : Fin 32) a0 a1) :: (.alu .or a2 a2 a4) :: (.alu .and a0 (7 : Fin 32) a3) :: (.aluImm .sll a6 a6 0x18) :: (.aluImm .sll a0 a0 0x8) :: (.alu .or a1 a6 a2) :: (.alu .or (23 : Fin 32) a1 a0) :: (.aluImm .xor (18 : Fin 32) (25 : Fin 32) 0x7F) :: (.alu .add a0 (26 : Fin 32) (25 : Fin 32)) :: (.aluImm .add a1 x0 0x80) :: [])
    (blockEnd_cons' (off' := 0x1160) ev_at_115e rfl (blockEnd_cons' (off' := 0x1162) ev_at_1160 rfl (blockEnd_cons' (off' := 0x1166) ev_at_1162 rfl (blockEnd_cons' (off' := 0x1168) ev_at_1166 rfl (blockEnd_cons' (off' := 0x116C) ev_at_1168 rfl (blockEnd_cons' (off' := 0x1170) ev_at_116c rfl (blockEnd_cons' (off' := 0x1174) ev_at_1170 rfl (blockEnd_cons' (off' := 0x1178) ev_at_1174 rfl (blockEnd_cons' (off' := 0x117C) ev_at_1178 rfl (blockEnd_cons' (off' := 0x1180) ev_at_117c rfl (blockEnd_cons' (off' := 0x1184) ev_at_1180 rfl (blockEnd_cons' (off' := 0x1188) ev_at_1184 rfl (blockEnd_cons' (off' := 0x118C) ev_at_1188 rfl (blockEnd_cons' (off' := 0x1190) ev_at_118c rfl (blockEnd_cons' (off' := 0x1194) ev_at_1190 rfl (blockEnd_cons' (off' := 0x1198) ev_at_1194 rfl (blockEnd_cons' (off' := 0x119A) ev_at_1198 rfl (blockEnd_cons' (off' := 0x119C) ev_at_119a rfl (blockEnd_cons' (off' := 0x119E) ev_at_119c rfl (blockEnd_cons' (off' := 0x11A2) ev_at_119e rfl (blockEnd_cons' (off' := 0x11A4) ev_at_11a2 rfl (blockEnd_cons' (off' := 0x11A6) ev_at_11a4 rfl (blockEnd_cons' (off' := 0x11A8) ev_at_11a6 rfl (blockEnd_cons' (off' := 0x11AA) ev_at_11a8 rfl (blockEnd_cons' (off' := 0x11AC) ev_at_11aa rfl (blockEnd_cons' (off' := 0x11B0) ev_at_11ac rfl (blockEnd_cons' (off' := 0x11B2) ev_at_11b0 rfl (blockEnd_cons' (off' := 0x11B4) ev_at_11b2 rfl (blockEnd_cons' (off' := 0x11B6) ev_at_11b4 rfl (blockEnd_cons' (off' := 0x11B8) ev_at_11b6 rfl (blockEnd_cons' (off' := 0x11BC) ev_at_11b8 rfl (blockEnd_cons' (off' := 0x11BE) ev_at_11bc rfl (blockEnd_cons' (off' := 0x11C2) ev_at_11be rfl (blockEnd_cons' (off' := 0x11C4) ev_at_11c2 rfl (blockEnd_cons' (off' := 0x11C6) ev_at_11c4 rfl (blockEnd_cons' (off' := 0x11CA) ev_at_11c6 rfl (blockEnd_cons' (off' := 0x11CE) ev_at_11ca rfl (blockEnd_cons' (off' := 0x11D0) ev_at_11ce rfl (blockEnd_cons' (off' := 0x11D2) ev_at_11d0 rfl (blockEnd_cons' (off' := 0x11D6) ev_at_11d2 rfl (blockEnd_cons' (off' := 0x11D8) ev_at_11d6 rfl (blockEnd_cons' (off' := 0x11DC) ev_at_11d8 rfl (blockEnd_cons' (off' := 0x11DE) ev_at_11dc rfl (blockEnd_cons' (off' := 0x11E0) ev_at_11de rfl (blockEnd_cons' (off' := 0x11E4) ev_at_11e0 rfl (blockEnd_cons' (off' := 0x11E6) ev_at_11e4 rfl (blockEnd_cons' (off' := 0x11EA) ev_at_11e6 rfl (blockEnd_cons' (off' := 0x11EE) ev_at_11ea rfl (blockEnd_cons' (off' := 0x11F2) ev_at_11ee rfl (blockEnd_cons' (off' := 0x11F4) ev_at_11f2 rfl (blockEnd_cons' (off' := 0x11F8) ev_at_11f4 rfl (blockEnd_cons' (off' := 0x11FA) ev_at_11f8 rfl (blockEnd_cons' (off' := 0x11FC) ev_at_11fa rfl (blockEnd_cons' (off' := 0x1200) ev_at_11fc rfl (blockEnd_cons' (off' := 0x1204) ev_at_1200 rfl (blockEnd_cons' (off' := 0x1208) ev_at_1204 rfl (blockEnd_cons' (off' := 0x120C) ev_at_1208 rfl (blockEnd_cons' (off' := 0x1210) ev_at_120c rfl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (by simp +decide only [BlockOk, BInstr.ok, BInstr.run, upd, ↓reduceIte, and_true]
        exact ⟨e1, e2, e3, e4⟩)
    rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have S0 : ∀ o : Nat, F + BitVec.ofNat 32 0xEF0 + BitVec.ofNat 32 o = F + BitVec.ofNat 32 (0xEF0 + o) :=
    fun o => add_ofNat_assoc F 0xEF0 o
  have hlo : memLoad32 M (F + BitVec.ofNat 32 0xF90 + 0x20) = BitVec.ofNat 32 (h.length / 128) := by
    rw [show F + BitVec.ofNat 32 0xF90 + 0x20 = F + BitVec.ofNat 32 0xEF0 + 0xC0 from (a0o 0x20).trans (S0 0xC0).symm]
    exact H.lo
  have hhi : memLoad32 M (F + BitVec.ofNat 32 0xF90 + 0x24) = 0 := by
    rw [show F + BitVec.ofNat 32 0xF90 + 0x24 = F + BitVec.ofNat 32 0xEF0 + 0xC4 from (a0o 0x24).trans (S0 0xC4).symm]
    exact H.hi
  have hhi2 : memLoad32 M (F + BitVec.ofNat 32 0xF90 + 0x28) = 0 := by
    rw [show F + BitVec.ofNat 32 0xF90 + 0x28 = F + BitVec.ofNat 32 0xEF0 + 0xC8 from (a0o 0x28).trans (S0 0xC8).symm]
    exact H.hi2
  have hhi3 : memLoad32 M (F + 0x90F + 0x6AD) = 0 := by
    rw [show F + 0x90F + 0x6AD = F + BitVec.ofNat 32 0xEF0 + 0xCC from (ev_a3 F 0x6AD).trans (S0 0xCC).symm]
    exact H.hi3
  have hpos : M (F + 0x90F + 0x660) = BitVec.ofNat 8 (h.length % 128) := by
    rw [show F + 0x90F + 0x660 = F + BitVec.ofNat 32 0xEF0 + 0x7F from (ev_a3 F 0x660).trans (S0 0x7F).symm]
    exact H.pos
  have hp : h.length % 128 < 128 := Nat.mod_lt _ (by decide)
  have hz : BitVec.zeroExtend 32 (BitVec.ofNat 8 (h.length % 128)) = BitVec.ofNat 32 (h.length % 128) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hpb : ∀ k, 7 ≤ k → (BitVec.ofNat 32 (h.length % 128)).getLsbD k = false := fun k hk =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by rw [BitVec.toNat_ofNat]; omega)
      (Nat.pow_le_pow_right (by decide) hk : 2 ^ 7 ≤ 2 ^ k))
  have g20 : reg n2 20 = bswap32 ((BitVec.ofNat 32 (h.length / 128) <<< 10) ||| (BitVec.ofNat 32 (h.length % 128) <<< 3)) := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [va0, v19, hlo, hpos, hz]
    exact lenLo5_eq _ _ hpb
  have g21 : reg n2 21 = bswap32 (BitVec.ofNat 32 (h.length / 128) >>> 22) := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [va0, hlo, hhi]
    exact lenHi5_eq _
  have g22 : reg n2 22 = 0 := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [va0, hhi2, hhi]; rfl
  have g23 : reg n2 23 = 0 := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [va0, v19, hhi3, hhi2]; rfl
  have g25 : reg n2 25 = BitVec.ofNat 32 (h.length % 128) := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [v19, hpos, hz]
  have g18 : reg n2 18 = BitVec.ofNat 32 (127 - h.length % 128) := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [v19, hpos, hz]
    show BitVec.ofNat 32 (h.length % 128) ^^^ 0x7F = _
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : h.length % 128 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : 127 - h.length % 128 < 2 ^ 32), show (0x7F : Word).toNat = 127 from rfl]
    exact xor127 _ hp
  have ga0 : reg n2 a0 = F + BitVec.ofNat 32 (0xEF0 + h.length % 128) := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [v19, hpos, hz, k1 26 (by decide), h26]; exact S0 _
  have ga1 : reg n2 a1 = 0x80 := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
  refine ⟨n2, c1.trans c2, D2, fun q hq hn => ?_, g20, g21, g22, g23, g18, g25, ga0, ga1⟩
  rw [hr2, evb_reg q D1.st.zero (by revert hn; revert hq; revert q; decide), k1 q (by revert hq; revert q; decide)]

/-- A frame byte outside a `memset` into the frame. -/
theorem fb_out (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {d N c : Nat} {v : BitVec 8} (hd : d + N ≤ 0x16A0)
    (hc : c < 0x16A0) (h : c < d ∨ d + N ≤ c) :
    fillBytes M (F + BitVec.ofNat 32 d) v N (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  refine fillBytes_sep (C.offs ?_ hd (by omega)) (Nat.le_refl _)
  rcases h with h | h
  · exact Or.inr (by omega)
  · exact Or.inl (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x1210: the buffer padded with 0x80 and zeros, and, when
fewer than 16 bytes are left for the length, compressed and cleared. After
it, storing the length in the buffer's last 16 bytes and compressing gives
the hash value of the padded message. -/
theorem ev_fpad (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x1210)
    {h : Bytes} (H : S5U.Hasher5At M (F + BitVec.ofNat 32 0xEF0) h)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 (0xEF0 + h.length % 128)) (ha1 : reg n a1 = 0x80)
    (h18 : reg n 18 = BitVec.ofNat 32 (127 - h.length % 128)) (h24 : reg n 24 = F + BitVec.ofNat 32 0xF70) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x1250 ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      (fullBlocks5 h ++ Sha512.blocks ((padTail5 h).length / 128) (padTail5 h)).foldl Sha512.compress Sha512.h0 =
        Sha512.compress (s5Hv M' (F + BitVec.ofNat 32 0xF70)).toList
          (memBytes M' (F + BitVec.ofNat 32 0xEF0) 112 ++ Sha512.be128 (8 * h.length)) ∧
      ∀ c, c < 0x16A0 → (c < 0xEF0 ∨ 0xFB0 ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  have hp : h.length % 128 < 128 := Nat.mod_lt _ (by decide)
  have S0 : ∀ o : Nat, F + BitVec.ofNat 32 0xEF0 + BitVec.ofNat 32 o = F + BitVec.ofNat 32 (0xEF0 + o) :=
    fun o => add_ofNat_assoc F 0xEF0 o
  -- sb a1, 0(a0)
  obtain ⟨n1, d1, D1, k1⟩ := D.sb C ev_at_1210 (off' := 0x1214) rfl (c := 0xEF0 + h.length % 128)
    (by rw [ha0]; exact BitVec.add_zero _) (by omega)
  rw [ha1] at D1
  -- addi a0, a0, 1; li a1, 0; mv a2, s2; memset
  obtain ⟨n2, c2, D2, hr2⟩ := D1.block C (off' := 0x121A)
    [.aluImm .add a0 a0 0x1, .aluImm .add a1 x0 0x0, .alu .add a2 x0 (18 : Fin 32)]
    (blockEnd_cons' ev_at_1214 rfl (blockEnd_cons' ev_at_1216 rfl (blockEnd_cons' ev_at_1218 rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n3, c3, D3, k3⟩ := D2.memset C (d := 0xEF0 + h.length % 128 + 1) (b := 0) (N := 127 - h.length % 128)
    ev_at_121a ev_at_121e (by decide) (by decide)
    (by rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [k1, ha0]
        exact add_ofNat_assoc F _ 1)
    (by rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [D1.st.zero]); try rfl)
    (by rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [D1.st.zero]); rw [k1, h18]
        exact BitVec.zero_add _)
    (by omega)
  have kk3 : ∀ q : Fin 32, q.val ∈ evKeep → reg n3 q = reg n q := fun q hq => by
    rw [k3 q hq, hr2, evb_reg q D1.st.zero (by revert hq; revert q; decide), k1]
  -- the buffer and the hash value after the padding byte and the zeros
  have hb : ∀ m, m ≤ 127 - h.length % 128 →
      memBytes (fillBytes (memStore8 M (F + BitVec.ofNat 32 (0xEF0 + h.length % 128)) ((0x80 : Word).extractLsb' 0 8))
        (F + BitVec.ofNat 32 (0xEF0 + h.length % 128 + 1)) ((0 : Word).extractLsb' 0 8) (127 - h.length % 128))
        (F + BitVec.ofNat 32 0xEF0) (h.length % 128 + 1 + m) = tailBytes5 h ++ [0x80] ++ List.replicate m 0 := by
    intro m hm
    rw [show h.length % 128 + 1 + m = h.length % 128 + (m + 1) by omega, memBytes_split, ← H.buf, memBytes_succ]
    rw [memBytes_congr fun i hi => by
          rw [S0, fb_out C (by omega) (by omega) (Or.inl (by omega)), sb_out C (by omega) (by omega) (by omega)]]
    rw [S0, fb_out C (by omega) (by omega) (Or.inl (by omega)), memStore8_same,
      show F + BitVec.ofNat 32 (0xEF0 + h.length % 128) + 1 = F + BitVec.ofNat 32 (0xEF0 + h.length % 128 + 1) from
        add_ofNat_assoc F _ 1, fill_memBytes _ _ _ hm (by omega)]
    simp
  have hs : s5Hv (fillBytes (memStore8 M (F + BitVec.ofNat 32 (0xEF0 + h.length % 128)) ((0x80 : Word).extractLsb' 0 8))
        (F + BitVec.ofNat 32 (0xEF0 + h.length % 128 + 1)) ((0 : Word).extractLsb' 0 8) (127 - h.length % 128))
        (F + BitVec.ofNat 32 0xF70) = s5Hv M (F + BitVec.ofNat 32 0xEF0 + 0x80) :=
    s5Hv_copy fun i hi => by
      rw [show F + BitVec.ofNat 32 0xEF0 + 0x80 = F + BitVec.ofNat 32 0xF70 from S0 0x80, add_ofNat_assoc,
        fb_out C (by omega) (by omega) (Or.inr (by omega)), sb_out C (by omega) (by omega) (by omega)]
  have fr3 : ∀ c, c < 0x16A0 → (c < 0xEF0 ∨ 0xFB0 ≤ c) →
      fillBytes (memStore8 M (F + BitVec.ofNat 32 (0xEF0 + h.length % 128)) ((0x80 : Word).extractLsb' 0 8))
        (F + BitVec.ofNat 32 (0xEF0 + h.length % 128 + 1)) ((0 : Word).extractLsb' 0 8) (127 - h.length % 128)
        (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := fun c hc hh => by
    rcases hh with hh | hh <;>
      rw [fb_out C (by omega) hc (by omega), sb_out C (by omega) hc (by omega)]
  have hash0 := H.hash
  rw [show F + BitVec.ofNat 32 0xEF0 + 0x80 = F + BitVec.ofNat 32 0xF70 from S0 0x80] at hash0 hs
  -- li a0, 15; bltu a0, s2
  obtain ⟨n4, c4, D4, hr4⟩ := D3.block C (off' := 0x1224) [.aluImm .add a0 x0 0xF] (bEnd1 ev_at_1222 rfl)
    ⟨trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have v15 : reg n4 a0 = 0xF := by
    rw [hr4]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D3.st.zero]; rfl
  have v18 : reg n4 18 = BitVec.ofNat 32 (127 - h.length % 128) := by
    rw [hr4, evb_reg 18 D3.st.zero (by decide), kk3 18 (by decide), h18]
  have kk4 : ∀ q : Fin 32, q.val ∈ evKeep → reg n4 q = reg n q := fun q hq => by
    rw [hr4, evb_reg q D3.st.zero (by revert hq; revert q; decide), kk3 q hq]
  have hbr : branchTaken .bltu (reg n4 a0) (reg n4 18) = decide (h.length % 128 < 112) := by
    rw [v15, v18]
    show decide ((15 : Word).toNat < (BitVec.ofNat 32 (127 - h.length % 128)).toNat) = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 127 - h.length % 128 < 2 ^ 32)]
    exact decide_eq_decide.mpr (show 15 < 127 - h.length % 128 ↔ h.length % 128 < 112 from ⟨by omega, by omega⟩)
  by_cases hlt : h.length % 128 < 112
  · obtain ⟨n5, d5, u5⟩ := D4.st.taken (D4.code C) 0x1250 ev_at_1224 rfl (by rw [hbr]; exact decide_eq_true hlt)
    have e112 := hb (111 - h.length % 128) (by omega)
    rw [show h.length % 128 + 1 + (111 - h.length % 128) = 112 by omega] at e112
    refine ⟨n5, _, c2.trans (c3.trans (c4.trans (Steps.single d5))) |> (Steps.single d1).trans, D4.jmp u5,
      fun q hq => by rw [u5.regs, kk4 q hq], ?_, fr3⟩
    rw [padTail5_short h hlt, List.foldl_append, ← hash0, hs, e112]
    unfold padTail5 padZeros5
    rw [show (239 - h.length % 128) % 128 = 111 - h.length % 128 by omega]
    rfl
  · obtain ⟨n5, d5, u5⟩ := D4.st.notTaken (D4.code C) 0x1228 ev_at_1224 rfl
      (by rw [hbr]; exact decide_eq_false hlt)
    have D5 := D4.jmp u5
    obtain ⟨n6, c6, D6, hr6⟩ := D5.block C (off' := 0x1232)
      [.aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x6F1, .alu .add a0 x0 (24 : Fin 32)]
      (blockEnd_cons' ev_at_1228 rfl (blockEnd_cons' ev_at_122c rfl (blockEnd_cons' ev_at_1230 rfl rfl)))
      ⟨trivial, trivial, trivial, trivial⟩ rfl
      (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n7, c7, D7, k7, hc7, fr7⟩ := D6.finBlock C (a := 0xF70) (b := 0xEF0) ev_at_1232 ev_at_1236 (by decide)
      (by decide)
      (by rw [hr6]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
          rw [u5.regs, kk4 24 (by decide), h24]; exact BitVec.zero_add _)
      (by rw [hr6]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
          rw [D5.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
      (by decide) (by decide) (by decide)
    obtain ⟨n8, c8, D8, hr8⟩ := D7.block C (off' := 0x1248)
      [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x6F1, .aluImm .add a2 x0 0x70, .aluImm .add a1 x0 0x0]
      (blockEnd_cons' ev_at_123a rfl (blockEnd_cons' ev_at_123e rfl (blockEnd_cons' ev_at_1242 rfl
        (blockEnd_cons' ev_at_1246 rfl rfl)))) ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl
      (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n9, c9, D9, k9⟩ := D8.memset C (d := 0xEF0) (b := 0) (N := 0x70) ev_at_1248 ev_at_124c (by decide)
      (by decide)
      (by rw [hr8]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
          rw [D7.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
      (by rw [hr8]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [D7.st.zero]); try rfl)
      (by rw [hr8]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [D7.st.zero]); try rfl)
      (by decide)
    have e128 := hb (127 - h.length % 128) (by omega)
    rw [show h.length % 128 + 1 + (127 - h.length % 128) = 128 by omega] at e128
    have fr7' : ∀ c, c < 0x16A0 → (c < 0xF70 ∨ 0xFB0 ≤ c) → n7.mem (F + BitVec.ofNat 32 c) =
        (fillBytes (memStore8 M (F + BitVec.ofNat 32 (0xEF0 + h.length % 128)) ((0x80 : Word).extractLsb' 0 8))
          (F + BitVec.ofNat 32 (0xEF0 + h.length % 128 + 1)) ((0 : Word).extractLsb' 0 8) (127 - h.length % 128))
          (F + BitVec.ofNat 32 c) := fun c hc hh => by
      refine fr7 _ (C.zF (by omega)) (C.offs ?_ (by decide) (by omega))
      rcases hh with hh | hh
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    have hs9 : s5Hv (fillBytes n7.mem (F + BitVec.ofNat 32 0xEF0) ((0 : Word).extractLsb' 0 8) 0x70)
        (F + BitVec.ofNat 32 0xF70) = s5Hv n7.mem (F + BitVec.ofNat 32 0xF70) :=
      s5Hv_congr fun i hi => by rw [add_ofNat_assoc, fb_out C (by decide) (by omega) (Or.inr (by omega))]
    refine ⟨n9, _, (Steps.single d1).trans (c2.trans (c3.trans (c4.trans ((Steps.single d5).trans (c6.trans
      (c7.trans (c8.trans c9))))))), D9, fun q hq => ?_, ?_, fun c hc hh => ?_⟩
    · rw [k9 q hq, hr8, evb_reg q D7.st.zero (by revert hq; revert q; decide), k7 q hq, hr6,
        evb_reg q D5.st.zero (by revert hq; revert q; decide), u5.regs, kk4 q hq]
    · rw [padTail5_long h (by omega), List.foldl_append, ← hash0, hs9, hc7, ← hs, e128,
        fill_memBytes _ _ _ (Nat.le_refl 112) (by decide)]
      rw [show (BitVec.extractLsb' 0 8 (0 : Word)).toNat = 0 from rfl]
      simp only [List.foldl_cons, List.foldl_nil]
    · rcases hh with hh | hh <;>
        rw [fb_out C (by decide) hc (by omega), fr7' c hc (by omega), fr3 c hc (by omega)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x1250: the length in bits stored in the buffer's last 16
bytes, the buffer compressed into the hash value, and the buffer's byte
count cleared. -/
theorem ev_fend (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x1250)
    (h19 : reg n 19 = F + 0x90F) (h24 : reg n 24 = F + BitVec.ofNat 32 0xF70) {lo : Word} {pos : Nat} (hp : pos < 128)
    (h20 : reg n 20 = bswap32 ((lo <<< 10) ||| (BitVec.ofNat 32 pos <<< 3))) (h21 : reg n 21 = bswap32 (lo >>> 22))
    (h22 : reg n 22 = 0) (h23 : reg n 23 = 0) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x1276 ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      (s5Hv M' (F + BitVec.ofNat 32 0xF70)).toList = Sha512.compress (s5Hv M (F + BitVec.ofNat 32 0xF70)).toList
        (memBytes M (F + BitVec.ofNat 32 0xEF0) 112 ++ Sha512.be128 (8 * (128 * lo.toNat + pos))) ∧
      ∀ c, c < 0x16A0 → (c < 0xEF0 ∨ 0xFB0 ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  obtain ⟨n1, d1, D1, k1⟩ := D.sw C ev_at_1250 (off' := 0x1254) rfl (c := 0xF60) (by rw [h19]; exact ev_a3 F 0x651)
    (by decide) (by decide)
  obtain ⟨n2, d2, D2, k2⟩ := D1.sw C ev_at_1254 (off' := 0x1258) rfl (c := 0xF64)
    (by rw [k1, h19]; exact ev_a3 F 0x655) (by decide) (by decide)
  obtain ⟨n3, d3, D3, k3⟩ := D2.sw C ev_at_1258 (off' := 0x125C) rfl (c := 0xF68)
    (by rw [k2, k1, h19]; exact ev_a3 F 0x659) (by decide) (by decide)
  obtain ⟨n4, d4, D4, k4⟩ := D3.sw C ev_at_125c (off' := 0x1260) rfl (c := 0xF6C)
    (by rw [k3, k2, k1, h19]; exact ev_a3 F 0x65D) (by decide) (by decide)
  simp only [k3, k2, k1] at D4
  rw [h20, h21, h22, h23] at D4
  obtain ⟨M4, hM4, D4⟩ : ∃ M4, M4 = memStore32 (memStore32 (memStore32 (memStore32 M (F + BitVec.ofNat 32 0xF60) 0)
      (F + BitVec.ofNat 32 0xF64) 0) (F + BitVec.ofNat 32 0xF68) (bswap32 (lo >>> 22))) (F + BitVec.ofNat 32 0xF6C)
      (bswap32 ((lo <<< 10) ||| (BitVec.ofNat 32 pos <<< 3))) ∧ EvSt M0 Ms F r0 M4 n4 0x1260 := ⟨_, rfl, D4⟩
  have kk4 : ∀ q, reg n4 q = reg n q := fun q => by rw [k4, k3, k2, k1]
  obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x126A)
    [.aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x6F1, .alu .add a0 x0 (24 : Fin 32)]
    (blockEnd_cons' ev_at_1260 rfl (blockEnd_cons' ev_at_1264 rfl (blockEnd_cons' ev_at_1268 rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n6, c6, D6, k6, hc6, fr6⟩ := D5.finBlock C (a := 0xF70) (b := 0xEF0) ev_at_126a ev_at_126e (by decide)
    (by decide)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [kk4, h24]; exact BitVec.zero_add _)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D4.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by decide) (by decide) (by decide)
  obtain ⟨n7, d7, D7, k7⟩ := D6.sb C ev_at_1272 (off' := 0x1276) rfl (c := 0xF6F)
    (by rw [k6 19 (by decide), hr5, evb_reg 19 D4.st.zero (by decide), kk4, h19]; exact ev_a3 F 0x660) (by decide)
  have fr6' : ∀ c, c < 0x16A0 → (c < 0xF70 ∨ 0xFB0 ≤ c) → n6.mem (F + BitVec.ofNat 32 c) = M4 (F + BitVec.ofNat 32 c) :=
    fun c hc hh => by
      refine fr6 _ (C.zF (by omega)) (C.offs ?_ (by decide) (by omega))
      rcases hh with hh | hh
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
  have fr4 : ∀ c, c < 0x16A0 → (c < 0xF60 ∨ 0xF70 ≤ c) → M4 (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) :=
    fun c hc hh => by
      rcases hh with hh | hh <;>
        rw [hM4, sw_out C (d := 0xF6C) (by decide) hc (by omega), sw_out C (d := 0xF68) (by decide) hc (by omega),
          sw_out C (d := 0xF64) (by decide) hc (by omega), sw_out C (d := 0xF60) (by decide) hc (by omega)]
  have hs4 : s5Hv M4 (F + BitVec.ofNat 32 0xF70) = s5Hv M (F + BitVec.ofNat 32 0xF70) :=
    s5Hv_congr fun i hi => by rw [add_ofNat_assoc, fr4 _ (by omega) (Or.inr (by omega))]
  have hb4 : memBytes M4 (F + BitVec.ofNat 32 0xEF0) 128 =
      memBytes M (F + BitVec.ofNat 32 0xEF0) 112 ++ Sha512.be128 (8 * (128 * lo.toNat + pos)) := by
    rw [show (128 : Nat) = 112 + 16 from rfl, memBytes_split,
      memBytes_congr fun i hi => by rw [add_ofNat_assoc, fr4 _ (by omega) (Or.inl (by omega))],
      show F + BitVec.ofNat 32 0xEF0 + BitVec.ofNat 32 112 = F + BitVec.ofNat 32 0xF60 from add_ofNat_assoc F 0xEF0 112,
      hM4, show F + BitVec.ofNat 32 0xF64 = F + BitVec.ofNat 32 0xF60 + BitVec.ofNat 32 4 from (add_ofNat_assoc F 0xF60 4).symm,
      show F + BitVec.ofNat 32 0xF68 = F + BitVec.ofNat 32 0xF60 + BitVec.ofNat 32 8 from (add_ofNat_assoc F 0xF60 8).symm,
      show F + BitVec.ofNat 32 0xF6C = F + BitVec.ofNat 32 0xF60 + BitVec.ofNat 32 12 from (add_ofNat_assoc F 0xF60 12).symm,
      len_bytes5 _ _ _ _ hp]
  refine ⟨n7, _, (Steps.single d1).trans ((Steps.single d2).trans ((Steps.single d3).trans ((Steps.single d4).trans
    (c5.trans (c6.trans (Steps.single d7)))))), D7, fun q hq => ?_, ?_, fun c hc hh => ?_⟩
  · rw [k7, k6 q hq, hr5, evb_reg q D4.st.zero (by revert hq; revert q; decide), kk4]
  · rw [s5Hv_congr (M := n6.mem) fun i hi => by
        rw [add_ofNat_assoc, sb_out C (by decide) (by omega) (by omega)], hc6, hs4, hb4]
  · rcases hh with hh | hh <;>
      rw [sb_out C (by decide) hc (by omega), fr6' c hc (by omega), fr4 c hc (by omega)]

theorem srl_byte (x : Word) (s : Nat) (hs : s < 32) :
    ((aluEval .srl x (BitVec.ofNat 32 s)).extractLsb' 0 8).toNat = x.toNat / 2 ^ s % 256 := by
  rw [byte_toNat]
  show (x >>> ((BitVec.ofNat 32 s).toNat % 32)).toNat / 2 ^ 0 % 256 = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : s < 2 ^ 32), Nat.mod_eq_of_lt hs, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- One pass of the loop at offset 0x1286: hash word `k` stored big-endian
at `F + 0x9F0 + 8k`. -/
theorem ev_rd_body (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} {k : Nat} (hk : k < 8)
    (D : EvSt M0 Ms F r0 M n 0x1286) (h9 : reg n 9 = F + BitVec.ofNat 32 (0x9F0 + 8 * k))
    (h24 : reg n 24 = F + BitVec.ofNat 32 (0xF70 + 8 * k)) (h16 : reg n 16 = BitVec.ofNat 32 (8 - k)) :
    ∃ n' M', Steps n n' ∧ (k + 1 < 8 → EvSt M0 Ms F r0 M' n' 0x1286) ∧ (k + 1 = 8 → EvSt M0 Ms F r0 M' n' 0x12CE) ∧
      reg n' 9 = F + BitVec.ofNat 32 (0x9F0 + 8 * (k + 1)) ∧ reg n' 24 = F + BitVec.ofNat 32 (0xF70 + 8 * (k + 1)) ∧
      reg n' 16 = BitVec.ofNat 32 (8 - (k + 1)) ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → q ≠ 9 → q ≠ 24 → reg n' q = reg n q) ∧
      memBytes M' (F + BitVec.ofNat 32 (0x9F0 + 8 * k)) 8 = Sha512.wordBytes (hvW M (F + BitVec.ofNat 32 0xF70) k) ∧
      ∀ c, c < 0x16A0 → (c < 0x9F0 + 8 * k ∨ 0x9F0 + 8 * k + 8 ≤ c) →
        M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  have z0 := D.st.zero
  have hA : aluEval .add (reg n x0) (reg n 24) = F + BitVec.ofNat 32 (0xF70 + 8 * k) := by
    rw [z0, h24]; exact BitVec.zero_add _
  have e1 : (F + BitVec.ofNat 32 (0xF70 + 8 * k) + 4).toNat % 4 = 0 := by
    rw [show F + BitVec.ofNat 32 (0xF70 + 8 * k) + 4 = F + BitVec.ofNat 32 (0xF70 + 8 * k + 4) from
      add_ofNat_assoc F _ 4]; exact C.al (by omega)
  have e2 : (F + BitVec.ofNat 32 (0xF70 + 8 * k) + 0).toNat % 4 = 0 := by
    rw [show F + BitVec.ofNat 32 (0xF70 + 8 * k) + 0 = F + BitVec.ofNat 32 (0xF70 + 8 * k + 0) from
      add_ofNat_assoc F _ 0]; exact C.al (by omega)
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x12A4)
    ((.alu .add a0 x0 (24 : Fin 32)) :: (.lw a1 a0 0x4) :: (.lw a2 a0 0x0) :: (.aluImm .srl (17 : Fin 32) a1 0x18) ::
      (.aluImm .srl a4 a2 0x18) :: (.aluImm .srl a5 a2 0x8) :: (.aluImm .srl (8 : Fin 32) a2 0x10) ::
      (.aluImm .srl a0 a1 0x8) :: (.aluImm .srl a3 a1 0x10) :: [])
    (blockEnd_cons' (off' := 0x1288) ev_at_1286 rfl (blockEnd_cons' (off' := 0x128A) ev_at_1288 rfl
      (blockEnd_cons' (off' := 0x128C) ev_at_128a rfl (blockEnd_cons' (off' := 0x1290) ev_at_128c rfl
      (blockEnd_cons' (off' := 0x1294) ev_at_1290 rfl (blockEnd_cons' (off' := 0x1298) ev_at_1294 rfl
      (blockEnd_cons' (off' := 0x129C) ev_at_1298 rfl (blockEnd_cons' (off' := 0x12A0) ev_at_129c rfl
      (blockEnd_cons' (off' := 0x12A4) ev_at_12a0 rfl rfl)))))))))
    (by simp +decide only [BlockOk, BInstr.ok, BInstr.run, upd, ↓reduceIte, and_true, true_and]
        rw [hA]; exact ⟨e1, e2⟩)
    rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have v91 : reg n1 9 = F + BitVec.ofNat 32 (0x9F0 + 8 * k) := by rw [hr1, evb_reg 9 z0 (by decide), h9]
  have v241 : reg n1 24 = F + BitVec.ofNat 32 (0xF70 + 8 * k) := by rw [hr1, evb_reg 24 z0 (by decide), h24]
  have v161 : reg n1 16 = BitVec.ofNat 32 (8 - k) := by rw [hr1, evb_reg 16 z0 (by decide), h16]
  have kk1 : ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → reg n1 q = reg n q := fun q hq h8 => by
    rw [hr1, evb_reg q z0 (by revert h8; revert hq; revert q; decide)]
  -- the bytes the stores take
  have bt : ∀ (r : Fin 32) (x : Word) (s : Nat), s < 32 → reg n1 r = aluEval .srl x (BitVec.ofNat 32 s) →
      ((reg n1 r).extractLsb' 0 8).toNat = x.toNat / 2 ^ s % 256 := fun r x s hs h => by rw [h]; exact srl_byte x s hs
  have t17 := bt 17 (memLoad32 M (F + BitVec.ofNat 32 (0xF70 + 8 * k) + 4)) 24 (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA]; rfl)
  have ta3 := bt a3 (memLoad32 M (F + BitVec.ofNat 32 (0xF70 + 8 * k) + 4)) 16 (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA]; rfl)
  have ta0 := bt a0 (memLoad32 M (F + BitVec.ofNat 32 (0xF70 + 8 * k) + 4)) 8 (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA]; rfl)
  have ta4 := bt a4 (memLoad32 M (F + BitVec.ofNat 32 (0xF70 + 8 * k) + 0)) 24 (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA]; rfl)
  have t8 := bt 8 (memLoad32 M (F + BitVec.ofNat 32 (0xF70 + 8 * k) + 0)) 16 (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA]; rfl)
  have ta5 := bt a5 (memLoad32 M (F + BitVec.ofNat 32 (0xF70 + 8 * k) + 0)) 8 (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA]; rfl)
  have ta1 : ((reg n1 a1).extractLsb' 0 8).toNat = (memLoad32 M (F + BitVec.ofNat 32 (0xF70 + 8 * k) + 4)).toNat % 256 := by
    rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA, byte_toNat, Nat.pow_zero, Nat.div_one]
  have ta2 : ((reg n1 a2).extractLsb' 0 8).toNat = (memLoad32 M (F + BitVec.ofNat 32 (0xF70 + 8 * k) + 0)).toNat % 256 := by
    rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA, byte_toNat, Nat.pow_zero, Nat.div_one]
  -- the 8 byte stores
  have sa : ∀ (j : Nat) (r : Machine), reg r 9 = reg n1 9 →
      reg r 9 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x9F0 + 8 * k + j) := fun j r h => by
    rw [h, v91]; exact add_ofNat_assoc F _ j
  obtain ⟨n2, d2, D2, k2⟩ := D1.sb C ev_at_12a4 (off' := 0x12A8) rfl (c := 0x9F0 + 8 * k + 4) (sa 4 n1 rfl) (by omega)
  obtain ⟨n3, d3, D3, k3⟩ := D2.sb C ev_at_12a8 (off' := 0x12AC) rfl (c := 0x9F0 + 8 * k + 5) (sa 5 n2 (k2 9)) (by omega)
  obtain ⟨n4, d4, D4, k4⟩ := D3.sb C ev_at_12ac (off' := 0x12B0) rfl (c := 0x9F0 + 8 * k + 6)
    (sa 6 n3 (by rw [k3, k2])) (by omega)
  obtain ⟨n5, d5, D5, k5⟩ := D4.sb C ev_at_12b0 (off' := 0x12B4) rfl (c := 0x9F0 + 8 * k + 7)
    (sa 7 n4 (by rw [k4, k3, k2])) (by omega)
  obtain ⟨n6, d6, D6, k6⟩ := D5.sb C ev_at_12b4 (off' := 0x12B8) rfl (c := 0x9F0 + 8 * k + 0)
    (sa 0 n5 (by rw [k5, k4, k3, k2])) (by omega)
  obtain ⟨n7, d7, D7, k7⟩ := D6.sb C ev_at_12b8 (off' := 0x12BC) rfl (c := 0x9F0 + 8 * k + 1)
    (sa 1 n6 (by rw [k6, k5, k4, k3, k2])) (by omega)
  obtain ⟨n8, d8, D8, k8⟩ := D7.sb C ev_at_12bc (off' := 0x12C0) rfl (c := 0x9F0 + 8 * k + 2)
    (sa 2 n7 (by rw [k7, k6, k5, k4, k3, k2])) (by omega)
  obtain ⟨n9, d9, D9, k9⟩ := D8.sb C ev_at_12c0 (off' := 0x12C4) rfl (c := 0x9F0 + 8 * k + 3)
    (sa 3 n8 (by rw [k8, k7, k6, k5, k4, k3, k2])) (by omega)
  simp only [k8, k7, k6, k5, k4, k3, k2] at D9
  have kk9 : ∀ q, reg n9 q = reg n1 q := fun q => by rw [k9, k8, k7, k6, k5, k4, k3, k2]
  obtain ⟨M9, hM9, D9⟩ : ∃ M9, M9 = memStore8 (memStore8 (memStore8 (memStore8 (memStore8 (memStore8 (memStore8
      (memStore8 M (F + BitVec.ofNat 32 (0x9F0 + 8 * k + 4)) ((reg n1 a4).extractLsb' 0 8))
      (F + BitVec.ofNat 32 (0x9F0 + 8 * k + 5)) ((reg n1 8).extractLsb' 0 8))
      (F + BitVec.ofNat 32 (0x9F0 + 8 * k + 6)) ((reg n1 a5).extractLsb' 0 8))
      (F + BitVec.ofNat 32 (0x9F0 + 8 * k + 7)) ((reg n1 a2).extractLsb' 0 8))
      (F + BitVec.ofNat 32 (0x9F0 + 8 * k + 0)) ((reg n1 17).extractLsb' 0 8))
      (F + BitVec.ofNat 32 (0x9F0 + 8 * k + 1)) ((reg n1 a3).extractLsb' 0 8))
      (F + BitVec.ofNat 32 (0x9F0 + 8 * k + 2)) ((reg n1 a0).extractLsb' 0 8))
      (F + BitVec.ofNat 32 (0x9F0 + 8 * k + 3)) ((reg n1 a1).extractLsb' 0 8) ∧
      EvSt M0 Ms F r0 M9 n9 0x12C4 := ⟨_, rfl, D9⟩
  -- addi s1, s1, 8; addi s8, s8, 8; addi a6, a6, -1
  obtain ⟨n10, c10, D10, hr10⟩ := D9.block C (off' := 0x12CA)
    [.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x8, .aluImm .add (24 : Fin 32) (24 : Fin 32) 0x8, .aluImm .add a6 a6 0xFFFFFFFF]
    (blockEnd_cons' ev_at_12c4 rfl (blockEnd_cons' ev_at_12c6 rfl (blockEnd_cons' ev_at_12c8 rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have v9 : reg n10 9 = F + BitVec.ofNat 32 (0x9F0 + 8 * (k + 1)) := by
    rw [hr10]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [kk9, v91]; exact add_sp F (b := 8) (by omega)
  have v24 : reg n10 24 = F + BitVec.ofNat 32 (0xF70 + 8 * (k + 1)) := by
    rw [hr10]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [kk9, v241]; exact add_sp F (b := 8) (by omega)
  have v16 : reg n10 16 = BitVec.ofNat 32 (8 - (k + 1)) := by
    rw [hr10]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [kk9, v161]
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 32 (8 - k) + 0xFFFFFFFF).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl]
    omega
  have kk10 : ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → q ≠ 9 → q ≠ 24 → reg n10 q = reg n q := fun q hq h8 h9 h24 => by
    rw [hr10, evb_reg q D9.st.zero (by revert h24; revert h9; revert hq; revert q; decide), kk9, kk1 q hq h8]
  -- the bytes and the frame
  have hw : memBytes M9 (F + BitVec.ofNat 32 (0x9F0 + 8 * k)) 8 = Sha512.wordBytes (hvW M (F + BitVec.ofNat 32 0xF70) k) := by
    unfold hvW
    rw [show F + BitVec.ofNat 32 0xF70 + BitVec.ofNat 32 (8 * k) = F + BitVec.ofNat 32 (0xF70 + 8 * k) + 0 from
        (add_ofNat_assoc F _ _).trans (add_ofNat_assoc F (0xF70 + 8 * k) 0).symm,
      show F + BitVec.ofNat 32 0xF70 + BitVec.ofNat 32 (8 * k + 4) = F + BitVec.ofNat 32 (0xF70 + 8 * k) + 4 from by
        rw [add_ofNat_assoc, ← Nat.add_assoc]; exact (add_ofNat_assoc F (0xF70 + 8 * k) 4).symm,
      wordBytes_pk, hM9]
    simp only [← add_ofNat_assoc F (0x9F0 + 8 * k)]
    rw [rd8, t17, ta3, ta0, ta1, ta4, t8, ta5, ta2]
  have fr9 : ∀ c, c < 0x16A0 → (c < 0x9F0 + 8 * k ∨ 0x9F0 + 8 * k + 8 ≤ c) →
      M9 (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := fun c hc hh => by
    rw [hM9]
    rcases hh with hh | hh <;>
      rw [sb_out C (by omega) hc (by omega), sb_out C (by omega) hc (by omega), sb_out C (by omega) hc (by omega),
        sb_out C (by omega) hc (by omega), sb_out C (by omega) hc (by omega), sb_out C (by omega) hc (by omega),
        sb_out C (by omega) hc (by omega), sb_out C (by omega) hc (by omega)]
  have cs : Steps n n10 := c1.trans ((Steps.single d2).trans ((Steps.single d3).trans ((Steps.single d4).trans
    ((Steps.single d5).trans ((Steps.single d6).trans ((Steps.single d7).trans ((Steps.single d8).trans
    ((Steps.single d9).trans c10))))))))
  by_cases hk1 : k + 1 < 8
  · obtain ⟨n11, d11, u11⟩ := D10.st.taken (D10.code C) 0x1286 ev_at_12ca rfl (by
      rw [v16, D10.st.zero]
      show (BitVec.ofNat 32 (8 - (k + 1)) != 0) = true
      simp only [bne_iff_ne, ne_eq]
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact absurd this (by show 8 - (k + 1) ≠ 0; omega))
    exact ⟨n11, M9, cs.trans (Steps.single d11), fun _ => D10.jmp u11, fun h => absurd h (by omega),
      by rw [u11.regs, v9], by rw [u11.regs, v24], by rw [u11.regs, v16],
      fun q hq h8 h9 h24 => by rw [u11.regs, kk10 q hq h8 h9 h24], hw, fr9⟩
  · obtain ⟨n11, d11, u11⟩ := D10.st.notTaken (D10.code C) 0x12CE ev_at_12ca rfl (by
      rw [v16, D10.st.zero, show 8 - (k + 1) = 0 by omega]; rfl)
    exact ⟨n11, M9, cs.trans (Steps.single d11), fun h => absurd h hk1, fun _ => D10.jmp u11,
      by rw [u11.regs, v9], by rw [u11.regs, v24], by rw [u11.regs, v16],
      fun q hq h8 h9 h24 => by rw [u11.regs, kk10 q hq h8 h9 h24], hw, fr9⟩

/-- The loop at offset 0x1286 from pass `k` on. -/
theorem ev_rd_loop (C : EvCtx M0 F pk sig msg len) {Mst : Word → BitVec 8} {R : Fin 32 → Word} :
    ∀ d k, k + d = 8 → k < 8 → ∀ (M : Word → BitVec 8) (n : Machine), EvSt M0 Ms F r0 M n 0x1286 →
      reg n 9 = F + BitVec.ofNat 32 (0x9F0 + 8 * k) → reg n 24 = F + BitVec.ofNat 32 (0xF70 + 8 * k) →
      reg n 16 = BitVec.ofNat 32 (8 - k) → (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → q ≠ 9 → q ≠ 24 → reg n q = R q) →
      memBytes M (F + BitVec.ofNat 32 0x9F0) (8 * k) =
        ((List.range k).map (hvW Mst (F + BitVec.ofNat 32 0xF70))).flatMap Sha512.wordBytes →
      (∀ c, c < 0x16A0 → (c < 0x9F0 ∨ 0xA30 ≤ c) → M (F + BitVec.ofNat 32 c) = Mst (F + BitVec.ofNat 32 c)) →
      ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x12CE ∧
        (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → q ≠ 9 → q ≠ 24 → reg n' q = R q) ∧
        memBytes M' (F + BitVec.ofNat 32 0x9F0) 64 =
          (s5Hv Mst (F + BitVec.ofNat 32 0xF70)).toList.flatMap Sha512.wordBytes ∧
        ∀ c, c < 0x16A0 → (c < 0x9F0 ∨ 0xA30 ≤ c) → M' (F + BitVec.ofNat 32 c) = Mst (F + BitVec.ofNat 32 c) := by
  intro d
  induction d with
  | zero => intro k hk hk8; exact absurd hk (by omega)
  | succ d ih =>
    intro k hk hk8 M n D h9 h24 h16 hR hM hfr
    obtain ⟨n1, M1, c1, D1a, D1b, v9, v24, v16, kk, hw, fr⟩ := ev_rd_body C hk8 D h9 h24 h16
    have hW : hvW M (F + BitVec.ofNat 32 0xF70) k = hvW Mst (F + BitVec.ofNat 32 0xF70) k := by
      unfold hvW
      have e : ∀ o, o + 4 ≤ 64 → memLoad32 M (F + BitVec.ofNat 32 0xF70 + BitVec.ofNat 32 o) =
          memLoad32 Mst (F + BitVec.ofNat 32 0xF70 + BitVec.ofNat 32 o) := fun o ho =>
        vk_ld2 fun j hj => by
          rw [add_ofNat_assoc, add_ofNat_assoc]; exact hfr _ (by omega) (Or.inr (by omega))
      rw [e _ (by omega), e _ (by omega)]
    have hM1 : memBytes M1 (F + BitVec.ofNat 32 0x9F0) (8 * (k + 1)) =
        ((List.range (k + 1)).map (hvW Mst (F + BitVec.ofNat 32 0xF70))).flatMap Sha512.wordBytes := by
      rw [show 8 * (k + 1) = 8 * k + 8 by omega, memBytes_split, flatMap_range_succ, ← hM, ← hW, ← hw,
        add_ofNat_assoc, memBytes_congr (M' := M1) (M := M) (p := F + BitVec.ofNat 32 0x9F0) (n := 8 * k)
          fun i hi => by rw [add_ofNat_assoc, fr _ (by omega) (Or.inl (by omega))]]
    have hfr1 : ∀ c, c < 0x16A0 → (c < 0x9F0 ∨ 0xA30 ≤ c) → M1 (F + BitVec.ofNat 32 c) = Mst (F + BitVec.ofNat 32 c) :=
      fun c hc hh => by
        rcases hh with hh | hh
        · rw [fr c hc (Or.inl (by omega)), hfr c hc (Or.inl hh)]
        · rw [fr c hc (Or.inr (by omega)), hfr c hc (Or.inr hh)]
    have hR1 : ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → q ≠ 9 → q ≠ 24 → reg n1 q = R q := fun q hq h8 h9 h24 => by
      rw [kk q hq h8 h9 h24, hR q hq h8 h9 h24]
    by_cases hk1 : k + 1 < 8
    · obtain ⟨n2, M2, c2, rest⟩ := ih (k + 1) (by omega) hk1 M1 n1 (D1a hk1) v9 v24 v16 hR1 hM1 hfr1
      exact ⟨n2, M2, c1.trans c2, rest⟩
    · have h8 : k + 1 = 8 := by omega
      rw [h8, ← s5Hv_toList, show 8 * 8 = 64 from rfl] at hM1
      exact ⟨n1, M1, c1, D1b h8, hR1, hM1, hfr1⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x1276: the 8 hash words written big-endian to `F + 0x9F0`,
and `F + 0x1508` into `s7`. -/
theorem ev_rd (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x1276)
    (h9 : reg n 9 = F + BitVec.ofNat 32 0x9F0) (h24 : reg n 24 = F + BitVec.ofNat 32 0xF70) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x12CE ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → q ≠ 9 → q ≠ 23 → q ≠ 24 → reg n' q = reg n q) ∧
      reg n' 23 = F + BitVec.ofNat 32 0x1508 ∧
      memBytes M' (F + BitVec.ofNat 32 0x9F0) 64 = (s5Hv M (F + BitVec.ofNat 32 0xF70)).toList.flatMap Sha512.wordBytes ∧
      ∀ c, c < 0x16A0 → (c < 0x9F0 ∨ 0xA30 ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x1282)
    [.aluImm .add a6 x0 0x8, .lui a0 0x1000, .aluImm .add a0 a0 0x508, .alu .add (23 : Fin 32) sp a0]
    (blockEnd_cons' ev_at_1276 rfl (blockEnd_cons' ev_at_1278 rfl (blockEnd_cons' ev_at_127a rfl
      (blockEnd_cons' ev_at_127e rfl rfl)))) ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have v16 : reg n1 16 = 8 := by
    rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.st.zero]; rfl
  obtain ⟨n2, d2, u2⟩ := D1.st.notTaken (D1.code C) 0x1286 ev_at_1282 rfl (by rw [v16, D1.st.zero]; rfl)
  have D2 := D1.jmp u2
  have k2 : ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 23 → reg n2 q = reg n q := fun q hq h23 => by
    rw [u2.regs, hr1, evb_reg q D.st.zero (by revert h23; revert hq; revert q; decide)]
  obtain ⟨n3, M3, c3, D3, k3, hb3, fr3⟩ := ev_rd_loop C (Mst := M) (R := reg n2) 8 0 rfl (by decide) M n2 D2
    (by rw [k2 9 (by decide) (by decide), h9]) (by rw [k2 24 (by decide) (by decide), h24])
    (by rw [u2.regs, v16]; rfl) (fun q _ _ _ _ => rfl) rfl (fun _ _ _ => rfl)
  have v23 : reg n1 23 = F + BitVec.ofNat 32 0x1508 := by
    rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; rfl
  exact ⟨n3, M3, c1.trans ((Steps.single d2).trans c3), D3,
    fun q hq h8 h9 h23 h24 => by rw [k3 q hq h8 h9 h24, k2 q hq h23],
    by rw [k3 23 (by decide) (by decide) (by decide) (by decide), u2.regs, v23], hb3, fr3⟩

/-- **The inlined `finalize`.** From offset 0x115A, with the hasher at
`F + 0xEF0` holding `h`, the function writes `sha512 h` to `F + 0x9F0`. -/
theorem ev_final (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x115A)
    (h19 : reg n 19 = F + 0x90F) (h26 : reg n 26 = F + BitVec.ofNat 32 0xEF0) (h24 : reg n 24 = F + BitVec.ofNat 32 0xF70)
    (h9 : reg n 9 = F + BitVec.ofNat 32 0x9F0) {h : Bytes} (H : S5U.Hasher5At M (F + BitVec.ofNat 32 0xEF0) h) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x12CE ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q.val ∉ [8, 9, 18, 20, 21, 22, 23, 24, 25] → reg n' q = reg n q) ∧
      reg n' 23 = F + BitVec.ofNat 32 0x1508 ∧ memBytes M' (F + BitVec.ofNat 32 0x9F0) 64 = sha512 h ∧
      ∀ c, c < 0x16A0 → (c < 0x9F0 ∨ (0xA30 ≤ c ∧ c < 0xEF0) ∨ 0xFB0 ≤ c) →
        M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  obtain ⟨n1, c1, D1, k1, g20, g21, g22, g23, g18, g25, ga0, ga1⟩ := ev_flen C D h19 h26 H
  obtain ⟨n2, M2, c2, D2, k2, E2, fr2⟩ := ev_fpad C D1 H ga0 ga1 g18
    (by rw [k1 24 (by decide) (by decide), h24])
  have p2 : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n1 q := k2
  obtain ⟨n3, M3, c3, D3, k3, E3, fr3⟩ := ev_fend C D2 (by rw [p2 19 (by decide), k1 19 (by decide) (by decide), h19])
    (by rw [p2 24 (by decide), k1 24 (by decide) (by decide), h24]) (Nat.mod_lt _ (by decide))
    (by rw [p2 20 (by decide), g20]) (by rw [p2 21 (by decide), g21]) (by rw [p2 22 (by decide), g22])
    (by rw [p2 23 (by decide), g23])
  obtain ⟨n4, M4, c4, D4, k4, v23, E4, fr4⟩ := ev_rd C D3
    (by rw [k3 9 (by decide), p2 9 (by decide), k1 9 (by decide) (by decide), h9])
    (by rw [k3 24 (by decide), p2 24 (by decide), k1 24 (by decide) (by decide), h24])
  have hlo : (BitVec.ofNat 32 (h.length / 128)).toNat = h.length / 128 := by
    have := H.hlen; rw [BitVec.toNat_ofNat]; omega
  rw [hlo, Nat.div_add_mod] at E3
  refine ⟨n4, M4, c1.trans (c2.trans (c3.trans c4)), D4, fun q hq hn => ?_, v23, ?_, fun c hc hh => ?_⟩
  · rw [k4 q hq (by revert hn; revert q; decide) (by revert hn; revert q; decide) (by revert hn; revert q; decide)
      (by revert hn; revert q; decide), k3 q hq, p2 q hq, k1 q hq (by revert hn; revert q; decide)]
  · rw [E4, E3, ← E2, sha512_stream]
  · have e3 : M3 (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
      rcases hh with hh | hh | hh
      · rw [fr3 c hc (Or.inl (by omega)), fr2 c hc (Or.inl (by omega))]
      · rw [fr3 c hc (Or.inl (by omega)), fr2 c hc (Or.inl (by omega))]
      · rw [fr3 c hc (Or.inr hh), fr2 c hc (Or.inr hh)]
    rcases hh with hh | hh | hh
    · rw [fr4 c hc (Or.inl hh), e3]
    · rw [fr4 c hc (Or.inr hh.1), e3]
    · rw [fr4 c hc (Or.inr (by omega)), e3]

/-- **The challenge hash.** From offset 0x104C, the function writes
`sha512 (R ‖ A ‖ M)` to `F + 0x9F0`, where `R` and `A` are the 32 bytes at
`F + 0x228` and `F + 0x128` and the message is the `len` bytes at `msg`. -/
theorem ev_hash (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x104C)
    (h19 : reg n 19 = F + 0x90F) (hm : memLoad32 M (F + BitVec.ofNat 32 0xC) = msg)
    (hk : memLoad32 M (F + BitVec.ofNat 32 0x10) = BitVec.ofNat 32 len) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x12CE ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q.val ∉ [8, 9, 18, 20, 21, 22, 23, 24, 25, 26] → reg n' q = reg n q) ∧
      reg n' 23 = F + BitVec.ofNat 32 0x1508 ∧ memBytes M' (F + BitVec.ofNat 32 0x9F0) 64 = sha512 (memBytes M (F + BitVec.ofNat 32 0x228) 32 ++
        memBytes M (F + BitVec.ofNat 32 0x128) 32 ++ memBytes M0 msg len) ∧
      ∀ c, c < 0x16A0 → (c < 0x308 ∨ (0x310 ≤ c ∧ c < 0x350) ∨ (0x520 ≤ c ∧ c < 0x5E0) ∨ (0x7F0 ≤ c ∧ c < 0x9F0) ∨
        (0xA30 ≤ c ∧ c < 0xEF0) ∨ 0xFC0 ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  obtain ⟨n1, M1, c1, D1, k1, v9, v24, l308, l30C, H1, fr1⟩ := ev_h1 C D h19
  obtain ⟨n2, M2, c2, D2, k2, v18, H2, fr2⟩ := ev_h2 C D1 v9 (l308.trans hm) (l30C.trans hk) H1
    (by simp only [List.length_append, memBytes_length]; have := C.hlen; omega)
  obtain ⟨n3, M3, c3, D3, k3, v26, v9', H3, fr3⟩ := ev_h3 C D2 v18 H2
  obtain ⟨n4, M4, c4, D4, k4, v23, E4, fr4⟩ := ev_final C D3
    (by rw [k3 19 (by decide) (by decide) (by decide), k2 19 (by decide) (by decide) (by decide) (by decide),
      k1 19 (by decide) (by decide) (by decide), h19])
    v26 (by rw [k3 24 (by decide) (by decide) (by decide), k2 24 (by decide) (by decide) (by decide) (by decide), v24])
    v9' H3
  refine ⟨n4, M4, c1.trans (c2.trans (c3.trans c4)), D4, fun q hq hn => ?_, v23, E4, fun c hc hh => ?_⟩
  · rw [k4 q hq (by revert hn; revert q; decide), k3 q hq (by revert hn; revert q; decide) (by revert hn; revert q; decide),
      k2 q hq (by revert hn; revert q; decide) (by revert hn; revert q; decide) (by revert hn; revert q; decide),
      k1 q hq (by revert hn; revert q; decide) (by revert hn; revert q; decide)]
  · rcases hh with h | h | h | h | h | h
    · rw [fr4 c hc (Or.inl (by omega)), fr3 c hc (Or.inl (by omega)), fr2 c hc (Or.inl (by omega)), fr1 c hc (Or.inl h)]
    · rw [fr4 c hc (Or.inl (by omega)), fr3 c hc (Or.inl (by omega)), fr2 c hc (Or.inl (by omega)),
        fr1 c hc (Or.inr (Or.inl ⟨h.1, by omega⟩))]
    · rw [fr4 c hc (Or.inl (by omega)), fr3 c hc (Or.inl (by omega)), fr2 c hc (Or.inr h.1),
        fr1 c hc (Or.inr (Or.inl ⟨by omega, by omega⟩))]
    · rw [fr4 c hc (Or.inl h.2), fr3 c hc (Or.inr (Or.inl h)), fr2 c hc (Or.inr (by omega)),
        fr1 c hc (Or.inr (Or.inl ⟨by omega, by omega⟩))]
    · rw [fr4 c hc (Or.inr (Or.inl h)), fr3 c hc (Or.inr (Or.inr (Or.inl h))), fr2 c hc (Or.inr (by omega)),
        fr1 c hc (Or.inr (Or.inl ⟨by omega, h.2⟩))]
    · rw [fr4 c hc (Or.inr (Or.inr (by omega))), fr3 c hc (Or.inr (Or.inr (Or.inr h))), fr2 c hc (Or.inr (by omega)),
        fr1 c hc (Or.inr (Or.inr h))]

end

end C3.RV32






