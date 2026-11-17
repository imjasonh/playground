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

end

end C3.RV32

