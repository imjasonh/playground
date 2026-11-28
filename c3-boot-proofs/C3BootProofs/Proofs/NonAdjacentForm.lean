import C3BootProofs.Proofs.IncrementLimb
import C3BootProofs.Proofs.Ashldi3
import C3BootProofs.Proofs.LincombShiftMod12

/-!
# `Scalar::non_adjacent_form`, as compiled

`curve25519_dalek`'s `Scalar::non_adjacent_form(5)`, which the image inlines
`w = 5` into, zeroes its `[i8; 256]` result and a `[u64; 5]` buffer, reads the
scalar's 32 bytes into the buffer's first four words, and then walks the bit
positions: an even window moves on one bit, and an odd one stores a digit
between -15 and 15 and moves on five. Each window is 5 bits of the scalar,
read through `__lshrdi3`, and through `__ashldi3` as well when it straddles
two words. `nafGo` is that loop, from the Rust source, on the scalar as a
natural number.
-/

namespace C3.RV32

open C3.Image

/-- The scalar at `s`: its 32 bytes, little-endian. -/
def nafScalar (M : Word → BitVec 8) (s : Word) : Nat :=
  (memLoad32 M s).toNat + 2 ^ 32 * (memLoad32 M (s + 4)).toNat + 2 ^ 64 * (memLoad32 M (s + 8)).toNat +
    2 ^ 96 * (memLoad32 M (s + 12)).toNat + 2 ^ 128 * (memLoad32 M (s + 16)).toNat +
    2 ^ 160 * (memLoad32 M (s + 20)).toNat + 2 ^ 192 * (memLoad32 M (s + 24)).toNat +
    2 ^ 224 * (memLoad32 M (s + 28)).toNat

/-- `non_adjacent_form(5)`'s loop from bit `pos` with `carry`, for at most
`n` more passes, over the digits `nf` so far. -/
def nafGo (X : Nat) : Nat → Nat → Nat → (Nat → BitVec 8) → Nat → BitVec 8
  | 0, _, _, nf => nf
  | n + 1, pos, carry, nf =>
    if 256 ≤ pos then nf
    else if (carry + X / 2 ^ pos % 32) % 2 = 0 then nafGo X n (pos + 1) carry nf
    else nafGo X n (pos + 5) (if carry + X / 2 ^ pos % 32 < 16 then 0 else 1) fun k =>
      if k = pos then
        BitVec.ofNat 8 (if carry + X / 2 ^ pos % 32 < 16 then carry + X / 2 ^ pos % 32
          else carry + X / 2 ^ pos % 32 + 224)
      else nf k

/-- The 256 digits `non_adjacent_form(5)` returns for the scalar `X`. -/
def nafSpec (X : Nat) : Nat → BitVec 8 := nafGo X 256 0 0 fun _ => 0

/-- Word `j` of the `[u64; 5]` buffer: bits `32 j` up of the scalar. -/
def nafWord (X j : Nat) : Word := BitVec.ofNat 32 (X / 2 ^ (32 * j) % 2 ^ 32)

theorem nafWord_toNat (X j : Nat) : (nafWord X j).toNat = X / 2 ^ (32 * j) % 2 ^ 32 := by
  unfold nafWord; rw [BitVec.toNat_ofNat, Nat.mod_mod]

theorem naf_pair (X i : Nat) :
    (nafWord X (2 * i)).toNat + 2 ^ 32 * (nafWord X (2 * i + 1)).toNat = X / 2 ^ (64 * i) % 2 ^ 64 := by
  rw [nafWord_toNat, nafWord_toNat,
    show X / 2 ^ (32 * (2 * i + 1)) = X / 2 ^ (64 * i) / 2 ^ 32 by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]; congr 2; omega,
    show 32 * (2 * i) = 64 * i by omega]
  generalize X / 2 ^ (64 * i) = Y
  omega

theorem naf_win_lo (X i b : Nat) (hb : b + 5 ≤ 64) :
    X / 2 ^ (64 * i) % 2 ^ 64 / 2 ^ b % 32 = X / 2 ^ (64 * i + b) % 32 := by
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize X / 2 ^ (64 * i) = Y
  have hY := Nat.div_add_mod Y (2 ^ 64)
  generalize Y / 2 ^ 64 = q at hY
  generalize Y % 2 ^ 64 = r at hY ⊢
  subst hY
  have e : 2 ^ 64 * q + r = r + 2 ^ b * (32 * (2 ^ (59 - b) * q)) := by
    have : (2 : Nat) ^ 64 = 2 ^ b * (32 * 2 ^ (59 - b)) := by
      rw [show (32 : Nat) = 2 ^ 5 from rfl, ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    rw [this, Nat.mul_assoc, Nat.mul_assoc, Nat.add_comm]
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos b), Nat.add_mul_mod_self_left]

set_option maxRecDepth 100000 in
theorem naf_win_hi (X pos : Nat) (hX : X < 2 ^ 256) (hp : pos < 256) (hb : 59 ≤ pos % 64) :
    (X / 2 ^ (64 * (pos / 64)) % 2 ^ 64 / 2 ^ (pos % 64) +
        X / 2 ^ (64 * (pos / 64 + 1)) % 2 ^ 64 * 2 ^ (64 - pos % 64) % 2 ^ 64 % 2 ^ 32) % 32 = X / 2 ^ pos % 32 ∧
    X / 2 ^ (64 * (pos / 64)) % 2 ^ 64 / 2 ^ (pos % 64) < 2 ^ (64 - pos % 64) ∧
    X / 2 ^ (64 * (pos / 64 + 1)) % 2 ^ 64 * 2 ^ (64 - pos % 64) % 2 ^ 64 % 2 ^ 32 % 2 ^ (64 - pos % 64) = 0 := by
  have h : pos ∈ [59, 60, 61, 62, 63, 123, 124, 125, 126, 127, 187, 188, 189, 190, 191, 251, 252, 253, 254, 255] := by
    revert hb; revert hp; generalize pos = p; revert p; decide
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;>
  · simp only [Nat.reduceMod, Nat.reduceDiv, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
    refine ⟨by omega, by omega, by omega⟩

set_option maxRecDepth 100000 in
theorem naf_addr : ∀ p, p < 256 →
    aluEval .and (aluEval .srl (BitVec.ofNat 32 p) 3) 0xFFFFFFF8 = BitVec.ofNat 32 (8 * (p / 64)) ∧
    aluEval .and (BitVec.ofNat 32 p) 0x3F = BitVec.ofNat 32 (p % 64) ∧
    branchTaken .bgeu (BitVec.ofNat 32 p) 0x100 = false ∧
    branchTaken .bltu (BitVec.ofNat 32 (p % 64)) 0x3B = decide (p % 64 < 59) ∧
    aluEval .sub 0x40 (BitVec.ofNat 32 (p % 64)) = BitVec.ofNat 32 (64 - p % 64) := by
  decide

set_option maxRecDepth 100000 in
theorem naf_exit : ∀ p, p < 261 → 256 ≤ p → branchTaken .bgeu (BitVec.ofNat 32 p) 0x100 = true := by
  decide

set_option maxRecDepth 100000 in
theorem naf_digit : ∀ v, v < 32 → ∀ c, c < 2 →
    aluEval .and (aluEval .add (BitVec.ofNat 32 v) (BitVec.ofNat 32 c)) 1 = BitVec.ofNat 32 ((v + c) % 2) ∧
    aluEval .or (aluEval .xor (aluEval .sltu (aluEval .add (BitVec.ofNat 32 v) (BitVec.ofNat 32 c)) 0x10) 1)
        (aluEval .sltu 0 (aluEval .add (aluEval .sltu (aluEval .add (BitVec.ofNat 32 v) (BitVec.ofNat 32 c))
          (BitVec.ofNat 32 v)) 0)) = BitVec.ofNat 32 (if v + c < 16 then 0 else 1) ∧
    (aluEval .add (aluEval .add (BitVec.ofNat 32 v) (BitVec.ofNat 32 c))
        (aluEval .and (aluEval .sub 0 (BitVec.ofNat 32 (if v + c < 16 then 0 else 1))) 0xE0)).extractLsb' 0 8 =
      BitVec.ofNat 8 (if v + c < 16 then v + c else v + c + 224) := by
  decide

/-- `((b2 << 16) | (b3 << 24)) | ((b1 << 8) | b0)` on zero-extended bytes. -/
theorem le4_A (b0 b1 b2 b3 : BitVec 8) :
    (aluEval .or (aluEval .or (aluEval .sll (b2.zeroExtend 32) 0x10) (aluEval .sll (b3.zeroExtend 32) 0x18))
      (aluEval .or (aluEval .sll (b1.zeroExtend 32) 8) (b0.zeroExtend 32))).toNat =
      le32 b0.toNat b1.toNat b2.toNat b3.toNat := by
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have v1 : (aluEval .sll (b1.zeroExtend 32) 8).toNat = b1.toNat * 2 ^ 8 := by rw [sll_byte _ (by decide)]; rfl
  have v2 : (aluEval .sll (b2.zeroExtend 32) 0x10).toNat = b2.toNat * 2 ^ 16 := by rw [sll_byte _ (by decide)]; rfl
  have v3 : (aluEval .sll (b3.zeroExtend 32) 0x18).toNat = b3.toNat * 2 ^ 24 := by rw [sll_byte _ (by decide)]; rfl
  have lo : (aluEval .or (aluEval .sll (b1.zeroExtend 32) 8) (b0.zeroExtend 32)).toNat =
      b1.toNat * 2 ^ 8 + b0.toNat := by
    rw [or_nat _ _ (i := 8) (by rw [v1]; exact Nat.mul_mod_left _ _) (by rw [zext_tn]; exact h0), v1, zext_tn]
  have hi : (aluEval .or (aluEval .sll (b2.zeroExtend 32) 0x10) (aluEval .sll (b3.zeroExtend 32) 0x18)).toNat =
      b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 := by
    rw [or_nat' _ _ (i := 24) (by rw [v2]; omega) (by rw [v3]; exact Nat.mul_mod_left _ _), v3, v2]
  rw [or_nat _ _ (i := 16) (by rw [hi]; omega) (by rw [lo]; omega), hi, lo]
  simp only [le32]; omega

/-- `((b1 << 8) | b0) | ((b2 << 16) | (b3 << 24))` on zero-extended bytes. -/
theorem le4_B (b0 b1 b2 b3 : BitVec 8) :
    (aluEval .or (aluEval .or (aluEval .sll (b1.zeroExtend 32) 8) (b0.zeroExtend 32))
      (aluEval .or (aluEval .sll (b2.zeroExtend 32) 0x10) (aluEval .sll (b3.zeroExtend 32) 0x18))).toNat =
      le32 b0.toNat b1.toNat b2.toNat b3.toNat := by
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have v1 : (aluEval .sll (b1.zeroExtend 32) 8).toNat = b1.toNat * 2 ^ 8 := by rw [sll_byte _ (by decide)]; rfl
  have v2 : (aluEval .sll (b2.zeroExtend 32) 0x10).toNat = b2.toNat * 2 ^ 16 := by rw [sll_byte _ (by decide)]; rfl
  have v3 : (aluEval .sll (b3.zeroExtend 32) 0x18).toNat = b3.toNat * 2 ^ 24 := by rw [sll_byte _ (by decide)]; rfl
  have lo : (aluEval .or (aluEval .sll (b1.zeroExtend 32) 8) (b0.zeroExtend 32)).toNat =
      b1.toNat * 2 ^ 8 + b0.toNat := by
    rw [or_nat _ _ (i := 8) (by rw [v1]; exact Nat.mul_mod_left _ _) (by rw [zext_tn]; exact h0), v1, zext_tn]
  have hi : (aluEval .or (aluEval .sll (b2.zeroExtend 32) 0x10) (aluEval .sll (b3.zeroExtend 32) 0x18)).toNat =
      b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 := by
    rw [or_nat' _ _ (i := 24) (by rw [v2]; omega) (by rw [v3]; exact Nat.mul_mod_left _ _), v3, v2]
  rw [or_nat' _ _ (i := 16) (by rw [lo]; omega) (by rw [hi]; omega), hi, lo]
  simp only [le32]; omega

section
set_option maxRecDepth 20000
theorem naf_at_0 : fetchRel nonAdjacentFormCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFA0, 2) := by decide
theorem naf_at_24 : fetchRel nonAdjacentFormCode 0x24 = some (.auipc ra 0x4000, 4) := by decide
theorem naf_at_28 : fetchRel nonAdjacentFormCode 0x28 = some (.jalr ra ra 0x212, 4) := by decide
theorem naf_at_36 : fetchRel nonAdjacentFormCode 0x36 = some (.auipc ra 0x4000, 4) := by decide
theorem naf_at_3a : fetchRel nonAdjacentFormCode 0x3A = some (.jalr ra ra 0x200, 4) := by decide
theorem naf_at_3e : fetchRel nonAdjacentFormCode 0x3E = some (.aluImm .add a6 x0 0x4, 2) := by decide
theorem naf_at_40 : fetchRel nonAdjacentFormCode 0x40 = some (.branch .beq a6 x0 0x4E, 4) := by decide
theorem naf_at_8a : fetchRel nonAdjacentFormCode 0x8A = some (.branch .bne a6 x0 0xFFFFFFBA, 4) := by decide
theorem naf_at_a4 : fetchRel nonAdjacentFormCode 0xA4 = some (.branch .bgeu (19 : Fin 32) (20 : Fin 32) 0x7A, 4) := by decide
theorem naf_at_bc : fetchRel nonAdjacentFormCode 0xBC = some (.auipc ra 0x4000, 4) := by decide
theorem naf_at_c0 : fetchRel nonAdjacentFormCode 0xC0 = some (.jalr ra ra 0x394, 4) := by decide
theorem naf_at_c4 : fetchRel nonAdjacentFormCode 0xC4 = some (.alu .add (26 : Fin 32) x0 a0, 2) := by decide
theorem naf_at_c6 : fetchRel nonAdjacentFormCode 0xC6 = some (.branch .bltu (8 : Fin 32) (22 : Fin 32) 0x18, 4) := by decide
theorem naf_at_d2 : fetchRel nonAdjacentFormCode 0xD2 = some (.auipc ra 0x4000, 4) := by decide
theorem naf_at_d6 : fetchRel nonAdjacentFormCode 0xD6 = some (.jalr ra ra 0x35A, 4) := by decide
theorem naf_at_da : fetchRel nonAdjacentFormCode 0xDA = some (.alu .or (26 : Fin 32) a0 (26 : Fin 32), 4) := by decide
theorem naf_at_ea : fetchRel nonAdjacentFormCode 0xEA = some (.branch .bne a2 x0 0x6, 2) := by decide
theorem naf_at_ec : fetchRel nonAdjacentFormCode 0xEC = some (.aluImm .add (19 : Fin 32) (19 : Fin 32) 0x1, 2) := by decide
theorem naf_at_ee : fetchRel nonAdjacentFormCode 0xEE = some (.jal x0 0xFFFFFFB6, 2) := by decide
theorem naf_at_11c : fetchRel nonAdjacentFormCode 0x11C = some (.jal x0 0xFFFFFF88, 2) := by decide
theorem naf_at_136 : fetchRel nonAdjacentFormCode 0x136 = some (.aluImm .add sp sp 0x60, 2) := by decide
theorem naf_at_138 : fetchRel nonAdjacentFormCode 0x138 = some (.jalr x0 ra 0x0, 2) := by decide

abbrev nafPs : List (Fin 32 × Word) :=
  [(ra, 0x5C), ((8 : Fin 32), 0x58), ((9 : Fin 32), 0x54), ((18 : Fin 32), 0x50), ((19 : Fin 32), 0x4C),
    ((20 : Fin 32), 0x48), ((21 : Fin 32), 0x44), ((22 : Fin 32), 0x40), ((23 : Fin 32), 0x3C),
    ((24 : Fin 32), 0x38), ((25 : Fin 32), 0x34), ((26 : Fin 32), 0x30)]

theorem nafSave_end : blockEnd nonAdjacentFormCode 2 (saveBlock nafPs) = some 0x1A := by decide
theorem nafRestore_end : blockEnd nonAdjacentFormCode 0x11E (restoreBlock nafPs) = some 0x136 := by decide

def nafPre1 : List BInstr :=
  [.alu .add (9 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .aluImm .add a2 x0 0x100, .aluImm .add a1 x0 0x0]

def nafPre2 : List BInstr :=
  [.aluImm .add a0 sp 0x8, .aluImm .add a2 x0 0x28, .aluImm .add a1 x0 0x0, .aluImm .add (8 : Fin 32) sp 0x8]

def nafL1A : List BInstr :=
  [.lbu (17 : Fin 32) (9 : Fin 32) 0x1, .lbu a2 (9 : Fin 32) 0x2, .lbu a3 (9 : Fin 32) 0x3,
    .lbu a4 (9 : Fin 32) 0x0, .lbu (5 : Fin 32) (9 : Fin 32) 0x4, .lbu a0 (9 : Fin 32) 0x5,
    .lbu a1 (9 : Fin 32) 0x6, .lbu a5 (9 : Fin 32) 0x7, .aluImm .sll (17 : Fin 32) (17 : Fin 32) 0x8,
    .aluImm .sll a2 a2 0x10, .aluImm .sll a3 a3 0x18, .alu .or a4 (17 : Fin 32) a4, .alu .or a2 a2 a3,
    .alu .or a2 a2 a4, .aluImm .sll a0 a0 0x8, .aluImm .sll a1 a1 0x10, .aluImm .sll a5 a5 0x18,
    .alu .or a0 a0 (5 : Fin 32), .alu .or a1 a1 a5, .alu .or a0 a0 a1]

def nafL1B : List BInstr :=
  [.sw (8 : Fin 32) a2 0x0, .sw (8 : Fin 32) a0 0x4, .aluImm .add (9 : Fin 32) (9 : Fin 32) 0x8,
    .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x8, .aluImm .add a6 a6 0xFFFFFFFF]

def nafMid : List BInstr :=
  [.aluImm .add (25 : Fin 32) x0 0x0, .aluImm .add (24 : Fin 32) x0 0x0, .aluImm .add (19 : Fin 32) x0 0x0,
    .aluImm .add (20 : Fin 32) x0 0x100, .aluImm .add (21 : Fin 32) sp 0x8, .aluImm .add (22 : Fin 32) x0 0x3B,
    .aluImm .add (23 : Fin 32) x0 0x40]

def nafIA : List BInstr :=
  [.aluImm .srl a0 (19 : Fin 32) 0x3, .aluImm .and a0 a0 0xFFFFFFF8, .alu .add (9 : Fin 32) (21 : Fin 32) a0,
    .lw a0 (9 : Fin 32) 0x0, .lw a1 (9 : Fin 32) 0x4, .aluImm .and (8 : Fin 32) (19 : Fin 32) 0x3F,
    .alu .add a2 x0 (8 : Fin 32)]

def nafIH : List BInstr :=
  [.lw a0 (9 : Fin 32) 0x8, .lw a1 (9 : Fin 32) 0xC, .alu .sub a2 (23 : Fin 32) (8 : Fin 32)]

def nafIW : List BInstr :=
  [.aluImm .and a1 (26 : Fin 32) 0x1F, .alu .add a0 a1 (24 : Fin 32), .aluImm .and a2 a0 0x1]

def nafIO : List BInstr :=
  [.alu .sltu a1 a0 a1, .alu .add a1 a1 (25 : Fin 32), .aluImm .sltu a2 a0 0x10, .aluImm .xor a2 a2 0x1,
    .alu .sltu a1 x0 a1, .alu .or (24 : Fin 32) a2 a1, .alu .sub a1 x0 (24 : Fin 32), .aluImm .and a1 a1 0xE0,
    .alu .add a0 a0 a1, .alu .add a1 (18 : Fin 32) (19 : Fin 32), .sb a1 a0 0x0,
    .aluImm .add (19 : Fin 32) (19 : Fin 32) 0x5, .aluImm .add (25 : Fin 32) x0 0x0]

theorem nafPre1_end : blockEnd nonAdjacentFormCode 0x1A nafPre1 = some 0x24 := by decide
theorem nafPre2_end : blockEnd nonAdjacentFormCode 0x2C nafPre2 = some 0x36 := by decide
theorem nafL1A_end : blockEnd nonAdjacentFormCode 0x44 nafL1A = some 0x80 := by decide
theorem nafL1B_end : blockEnd nonAdjacentFormCode 0x80 nafL1B = some 0x8A := by decide
theorem nafMid_end : blockEnd nonAdjacentFormCode 0x8E nafMid = some 0xA4 := by decide
theorem nafIA_end : blockEnd nonAdjacentFormCode 0xA8 nafIA = some 0xBC := by decide
theorem nafIH_end : blockEnd nonAdjacentFormCode 0xCA nafIH = some 0xD2 := by decide
theorem nafIW_end : blockEnd nonAdjacentFormCode 0xDE nafIW = some 0xEA := by decide
theorem nafIO_end : blockEnd nonAdjacentFormCode 0xF0 nafIO = some 0x11C := by decide
end

theorem and31 (x : Word) : (aluEval .and x 0x1F).toNat = x.toNat % 32 := by
  show (x &&& 0x1F).toNat = _
  rw [BitVec.toNat_and, show (0x1F : Word).toNat = 2 ^ 5 - 1 from rfl, and_pow_sub_one]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- One pass of the main loop, from `0xA4` back to `0xA4`, at a bit position
below 256: an even window moves on a bit, and an odd one stores its digit
and moves on five. -/
theorem naf_iter {P F8 out : Word} {X pos carry : Nat} (mk : Machine)
    (hP : P.toNat % 2 = 0) (hc : CodeIn mk.mem P nonAdjacentFormCode)
    (hls : CodeIn mk.mem (P + 0x4450) lshrdi3Code) (has : CodeIn mk.mem (P + 0x442C) ashldi3Code)
    (t : St mk.mem P mk 0xA4 (reg mk))
    (hX : X < 2 ^ 256) (hpos : pos < 256) (hcar : carry < 2)
    (r19 : reg mk (19 : Fin 32) = BitVec.ofNat 32 pos) (r24 : reg mk (24 : Fin 32) = BitVec.ofNat 32 carry)
    (r25 : reg mk (25 : Fin 32) = 0) (r20 : reg mk (20 : Fin 32) = 0x100) (r21 : reg mk (21 : Fin 32) = F8)
    (r22 : reg mk (22 : Fin 32) = 0x3B) (r23 : reg mk (23 : Fin 32) = 0x40) (r18 : reg mk (18 : Fin 32) = out)
    (hF8 : F8.toNat % 4 = 0)
    (hbuf : ∀ j, j < 10 → memLoad32 mk.mem (F8 + BitVec.ofNat 32 (4 * j)) = nafWord X j)
    (sOC : Sep out 256 P nonAdjacentFormCode.length) :
    ∃ mk', Steps mk mk' ∧ St mk'.mem P mk' 0xA4 (reg mk') ∧ reg mk' (25 : Fin 32) = 0 ∧
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 20, 21, 22, 23, 27] → reg mk' q = reg mk q) ∧
      (if (carry + X / 2 ^ pos % 32) % 2 = 0 then
        mk'.mem = mk.mem ∧ reg mk' (19 : Fin 32) = BitVec.ofNat 32 (pos + 1) ∧
          reg mk' (24 : Fin 32) = BitVec.ofNat 32 carry
      else
        mk'.mem = memStore8 mk.mem (out + BitVec.ofNat 32 pos)
            (BitVec.ofNat 8 (if carry + X / 2 ^ pos % 32 < 16 then carry + X / 2 ^ pos % 32
              else carry + X / 2 ^ pos % 32 + 224)) ∧
          reg mk' (19 : Fin 32) = BitVec.ofNat 32 (pos + 5) ∧
          reg mk' (24 : Fin 32) = BitVec.ofNat 32 (if carry + X / 2 ^ pos % 32 < 16 then 0 else 1)) := by
  obtain ⟨hA1, hA2, hA3, hA4, hA5⟩ := naf_addr pos hpos
  have hz : reg mk 0 = 0 := t.zero
  have hi4 : pos / 64 < 4 := by omega
  have ad4 : ∀ (a : Word) (k : Nat), a + BitVec.ofNat 32 k + 0x4 = a + BitVec.ofNat 32 (k + 4) :=
    fun a k => add_ofNat_assoc a k 4
  have ad8 : ∀ (a : Word) (k : Nat), a + BitVec.ofNat 32 k + 0x8 = a + BitVec.ofNat 32 (k + 8) :=
    fun a k => add_ofNat_assoc a k 8
  have adC : ∀ (a : Word) (k : Nat), a + BitVec.ofNat 32 k + 0xC = a + BitVec.ofNat 32 (k + 12) :=
    fun a k => add_ofNat_assoc a k 12
  obtain ⟨n1, d1, u1⟩ := t.notTaken hc 0xA8 naf_at_a4 (by decide) (by rw [r19, r20]; exact hA3)
  -- the word pair holding bit `pos`, and the shift
  obtain ⟨nA, cA, uA⟩ := St.block nafIA u1 hc nafIA_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, nafIA, upd_app, ↓reduceIte, and_true]
    rw [r19, r21, hA1, ev_add]
    repeat' apply And.intro
    all_goals first | exact True.intro | (rw [add_lit_zero]; exact aligned_add hF8 (by omega)) |
      exact aligned_add hF8 (by omega) | (rw [ad4]; exact aligned_add hF8 (by omega)))
  simp only [runBlock, BInstr.run, nafIA] at uA
  have A10 : reg nA a0 = nafWord X (2 * (pos / 64)) := by
    rw [uA.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r19, r21, hA1, ev_add, add_lit_zero]
    have := hbuf (2 * (pos / 64)) (by omega); rwa [show 4 * (2 * (pos / 64)) = 8 * (pos / 64) by omega] at this
  have A11 : reg nA a1 = nafWord X (2 * (pos / 64) + 1) := by
    rw [uA.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r19, r21, hA1, ev_add, ad4]
    have := hbuf (2 * (pos / 64) + 1) (by omega)
    rwa [show 4 * (2 * (pos / 64) + 1) = 8 * (pos / 64) + 4 by omega] at this
  have A9 : reg nA (9 : Fin 32) = F8 + BitVec.ofNat 32 (8 * (pos / 64)) := by
    rw [uA.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r19, r21, hA1]; rfl
  have A8 : reg nA (8 : Fin 32) = BitVec.ofNat 32 (pos % 64) := by
    rw [uA.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r19, hA2]
  have A12 : reg nA a2 = BitVec.ofNat 32 (pos % 64) := by
    rw [uA.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r19, hA2]; exact BitVec.zero_add _
  have kA : ∀ q : Fin 32, q.val ≠ 0 → q ≠ a0 → q ≠ (9 : Fin 32) → q ≠ a1 → q ≠ (8 : Fin 32) → q ≠ a2 →
      reg nA q = reg mk q := fun q h0 h1 h2 h3 h4 h5 => by
    rw [uA.regs]; simp only [upd_ne h0 h1, upd_ne h0 h2, upd_ne h0 h3, upd_ne h0 h4, upd_ne h0 h5]
  -- `__lshrdi3(lo, hi, pos % 64)`
  obtain ⟨n3, c3, pc3, mem3, regs3⟩ := uA.self.callRa hc naf_at_bc naf_at_c0 (cb := P + 0x4450)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP 0x4450 (by decide))
  have r3 : ∀ q, q ≠ ra → reg n3 q = reg nA q := fun q h => by rw [regs3]; exact updz uA.self.zero h
  obtain ⟨n4, c4, pc4, v4, k4, mem4⟩ := lshrdi3_correct n3 (base := P + 0x4450)
    (retAddr := P + BitVec.ofNat 32 (0xBC + 8)) (lo := nafWord X (2 * (pos / 64)))
    (hi := nafWord X (2 * (pos / 64) + 1)) (s := pos % 64) (by rw [mem3]; exact hls) pc3
    (by rw [r3 a0 (by decide), A10]) (by rw [r3 a1 (by decide), A11]) (by rw [r3 a2 (by decide), A12])
    (by omega) (by rw [regs3]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P hP (0xBC + 8) (by decide)))
  rw [naf_pair] at v4
  have u4 : St mk.mem P n4 0xC4 (reg n4) := ⟨pc4, by rw [mem4, mem3], fun _ => rfl⟩
  have kN : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 27] → reg n4 q = reg mk q :=
    fun q hq => by
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ (9 : Fin 32) ∧ q ≠ a1 ∧ q ≠ (8 : Fin 32) ∧
          q ≠ a2 ∧ q ≠ a3 ∧ q ≠ ra := by revert hq; revert q; decide
      rw [k4 q h1 h3 h6, r3 q h7, kA q h0 h1 h2 h3 h4 h5]
  have N8 : reg n4 (8 : Fin 32) = BitVec.ofNat 32 (pos % 64) := by
    rw [k4 _ (by decide) (by decide) (by decide), r3 _ (by decide), A8]
  have N9 : reg n4 (9 : Fin 32) = F8 + BitVec.ofNat 32 (8 * (pos / 64)) := by
    rw [k4 _ (by decide) (by decide) (by decide), r3 _ (by decide), A9]
  have hn4z : reg n4 0 = 0 := u4.zero
  obtain ⟨n5, d5, u5⟩ := u4.alu hc naf_at_c4 (off' := 0xC6) (by decide)
  have r5 : ∀ q, reg n5 q = upd (reg n4) (26 : Fin 32) (aluEval .add (reg n4 x0) (reg n4 a0)) q := u5.regs
  have S5 : reg n5 (26 : Fin 32) = reg n4 a0 := by
    rw [r5]; simp +decide only [upd_app, ↓reduceIte]; rw [hn4z]; exact BitVec.zero_add _
  have k5 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 27] → reg n5 q = reg n4 q :=
    fun q hq => by
      obtain ⟨h0, h1⟩ : q.val ≠ 0 ∧ q ≠ (26 : Fin 32) := by revert hq; revert q; decide
      rw [r5, upd_ne h0 h1]
  have hW := (X / 2 ^ (64 * (pos / 64)) % 2 ^ 64).lt_succ_self
  have ha0 := (reg n4 a0).isLt
  have ha1 := (reg n4 a1).isLt
  have hpd : pos = 64 * (pos / 64) + pos % 64 := by omega
  -- the window's five bits, at `0xDE`
  have conv : ∃ m7, Steps n5 m7 ∧ St mk.mem P m7 0xDE (reg m7) ∧
      aluEval .and (reg m7 (26 : Fin 32)) 0x1F = BitVec.ofNat 32 (X / 2 ^ pos % 32) ∧
      ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 27] → reg m7 q = reg n4 q := by
    by_cases hb : pos % 64 < 59
    · obtain ⟨n6, d6, u6⟩ := u5.self.taken hc 0xDE naf_at_c6 (by decide) (by
        rw [k5 _ (by decide), k5 _ (by decide), N8, kN _ (by decide), r22, hA4]; exact decide_eq_true hb)
      refine ⟨n6, .single d6, ⟨u6.pc, u6.mem, fun _ => rfl⟩, ?_, fun q hq => ?_⟩
      · rw [u6.regs, S5]
        apply BitVec.eq_of_toNat_eq
        rw [and31, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : X / 2 ^ pos % 32 < 2 ^ 32)]
        have e1 : (reg n4 a0).toNat = X / 2 ^ (64 * (pos / 64)) % 2 ^ 64 / 2 ^ (pos % 64) % 2 ^ 32 := by omega
        rw [e1, Nat.mod_mod_of_dvd _ (by decide : 32 ∣ 2 ^ 32), naf_win_lo X (pos / 64) (pos % 64) (by omega), ← hpd]
      · have h1 : q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 27] := by revert hq; revert q; decide
        rw [u6.regs, k5 q h1]
    · obtain ⟨n6, d6, u6⟩ := u5.self.notTaken hc 0xCA naf_at_c6 (by decide) (by
        rw [k5 _ (by decide), k5 _ (by decide), N8, kN _ (by decide), r22, hA4]; exact decide_eq_false hb)
      obtain ⟨nH, cH, uH⟩ := St.block nafIH u6 hc nafIH_end (by
        simp +decide only [BlockOk, BInstr.ok, BInstr.run, nafIH, upd_app, ↓reduceIte, and_true]
        rw [k5 (9 : Fin 32) (by decide), N9]
        repeat' apply And.intro
        all_goals first | exact True.intro | (rw [ad8]; exact aligned_add hF8 (by omega)) |
          (rw [adC]; exact aligned_add hF8 (by omega)) | exact aligned_add hF8 (by omega))
      simp only [runBlock, BInstr.run, nafIH] at uH
      have H10 : reg nH a0 = nafWord X (2 * (pos / 64 + 1)) := by
        rw [uH.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [k5 (9 : Fin 32) (by decide), N9, ad8]
        have := hbuf (2 * (pos / 64 + 1)) (by omega)
        rwa [show 4 * (2 * (pos / 64 + 1)) = 8 * (pos / 64) + 8 by omega] at this
      have H11 : reg nH a1 = nafWord X (2 * (pos / 64 + 1) + 1) := by
        rw [uH.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [k5 (9 : Fin 32) (by decide), N9, adC]
        have := hbuf (2 * (pos / 64 + 1) + 1) (by omega)
        rwa [show 4 * (2 * (pos / 64 + 1) + 1) = 8 * (pos / 64) + 12 by omega] at this
      have H12 : reg nH a2 = BitVec.ofNat 32 (64 - pos % 64) := by
        rw [uH.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [k5 (23 : Fin 32) (by decide), k5 (8 : Fin 32) (by decide), kN (23 : Fin 32) (by decide), r23, N8, hA5]
      have kH : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nH q = reg n5 q :=
        fun q hq => by
          obtain ⟨h0, h1, h2, h3⟩ : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 := by revert hq; revert q; decide
          rw [uH.regs]; simp only [upd_ne h0 h1, upd_ne h0 h2, upd_ne h0 h3]
      -- `__ashldi3(lo', hi', 64 - pos % 64)`
      obtain ⟨n7, c7, pc7, mem7, regs7⟩ := uH.self.callRa hc naf_at_d2 naf_at_d6 (cb := P + 0x442C)
        (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P hP 0x442C (by decide))
      have r7 : ∀ q, q ≠ ra → reg n7 q = reg nH q := fun q h => by rw [regs7]; exact updz uH.self.zero h
      obtain ⟨n8, c8, pc8, v8, k8, mem8⟩ := ashldi3_correct n7 (base := P + 0x442C)
        (retAddr := P + BitVec.ofNat 32 (0xD2 + 8)) (lo := nafWord X (2 * (pos / 64 + 1)))
        (hi := nafWord X (2 * (pos / 64 + 1) + 1)) (s := 64 - pos % 64) (by rw [mem7]; exact has) pc7
        (by rw [r7 a0 (by decide), H10]) (by rw [r7 a1 (by decide), H11]) (by rw [r7 a2 (by decide), H12])
        (by omega) (by rw [regs7]; simp +decide only [upd_app, ↓reduceIte])
        (even_clear _ (even_at P hP (0xD2 + 8) (by decide)))
      rw [naf_pair] at v8
      have u8 : St mk.mem P n8 0xDA (reg n8) := ⟨pc8, by rw [mem8, mem7], fun _ => rfl⟩
      obtain ⟨n9, d9, u9⟩ := u8.alu hc naf_at_da (off' := 0xDE) (by decide)
      have e26 : reg n8 (26 : Fin 32) = reg n4 a0 := by
        rw [k8 _ (by decide) (by decide) (by decide), r7 _ (by decide), kH _ (by decide), S5]
      obtain ⟨H1, H2, H3⟩ := naf_win_hi X pos hX hpos (by omega)
      have h32 : (2 : Nat) ^ (64 - pos % 64) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega)
      have hb8 := (reg n8 a0).isLt
      have hb8' := (reg n8 a1).isLt
      have eA : (reg n4 a0).toNat = X / 2 ^ (64 * (pos / 64)) % 2 ^ 64 / 2 ^ (pos % 64) := by omega
      have eB : (reg n8 a0).toNat = X / 2 ^ (64 * (pos / 64 + 1)) % 2 ^ 64 * 2 ^ (64 - pos % 64) % 2 ^ 64 % 2 ^ 32 := by
        omega
      refine ⟨n9, .cons d6 (cH.trans (c7.trans (c8.trans (.single d9)))), ⟨u9.pc, u9.mem, fun _ => rfl⟩, ?_,
        fun q hq => ?_⟩
      · rw [u9.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [e26]
        apply BitVec.eq_of_toNat_eq
        rw [and31, or_nat _ _ (i := 64 - pos % 64) (by rw [eB]; exact H3) (by rw [eA]; exact H2), eB, eA,
          Nat.add_comm, H1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : X / 2 ^ pos % 32 < 2 ^ 32)]
      · obtain ⟨h0, h1, h2, h3, h4, h5⟩ : q.val ≠ 0 ∧ q ≠ (26 : Fin 32) ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a3 ∧ q ≠ ra := by
          revert hq; revert q; decide
        have h6 : q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
        have h7 : q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 27] := by revert hq; revert q; decide
        rw [u9.regs, upd_ne h0 h1, k8 q h2 h3 h4, r7 q h5, kH q h6, k5 q h7]
  obtain ⟨m7, c7, u7, hv, k7⟩ := conv
  have hv32 : X / 2 ^ pos % 32 < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨v, hvd⟩ : ∃ v, X / 2 ^ pos % 32 = v := ⟨_, rfl⟩
  rw [hvd] at hv hv32 ⊢
  rw [Nat.add_comm carry v]
  obtain ⟨D1, D2, D3⟩ := naf_digit v hv32 carry hcar
  have q24 : reg m7 (24 : Fin 32) = BitVec.ofNat 32 carry := by rw [k7 _ (by decide), kN _ (by decide), r24]
  have q25 : reg m7 (25 : Fin 32) = 0 := by rw [k7 _ (by decide), kN _ (by decide), r25]
  have q19 : reg m7 (19 : Fin 32) = BitVec.ofNat 32 pos := by rw [k7 _ (by decide), kN _ (by decide), r19]
  have q18 : reg m7 (18 : Fin 32) = out := by rw [k7 _ (by decide), kN _ (by decide), r18]
  obtain ⟨nW, cW, uW⟩ := St.block nafIW u7 hc nafIW_end (by simp +decide only [BlockOk, BInstr.ok, nafIW, and_true])
  simp only [runBlock, BInstr.run, nafIW] at uW
  have W12 : reg nW a2 = BitVec.ofNat 32 ((v + carry) % 2) := by
    rw [uW.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [hv, q24, D1]
  have kW : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 27] → reg nW q = reg mk q :=
    fun q hq => by
      obtain ⟨h0, h1, h2, h3⟩ : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 := by revert hq; revert q; decide
      rw [uW.regs]; simp only [upd_ne h0 h1, upd_ne h0 h2, upd_ne h0 h3]; rw [k7 q hq, kN q hq]
  have hzW : reg nW 0 = 0 := uW.self.zero
  have W11 : reg nW a1 = BitVec.ofNat 32 v := by rw [uW.regs]; simp +decide only [upd_app, ↓reduceIte]; exact hv
  have W10 : reg nW a0 = aluEval .add (BitVec.ofNat 32 v) (BitVec.ofNat 32 carry) := by
    rw [uW.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [hv, q24]
  have W25 : reg nW (25 : Fin 32) = 0 := by rw [kW _ (by decide), r25]
  have S : Steps mk nW := .cons d1 (cA.trans (c3.trans (c4.trans (.cons d5 (c7.trans cW)))))
  by_cases hev : (v + carry) % 2 = 0
  · obtain ⟨e1, de1, ue1⟩ := uW.self.notTaken hc 0xEC naf_at_ea (by decide) (by rw [W12, hev, hzW]; rfl)
    obtain ⟨e2, de2, ue2⟩ := ue1.aluImm hc naf_at_ec (off' := 0xEE) (by decide)
    obtain ⟨e3, de3, ue3⟩ := ue2.jump hc naf_at_ee (off' := 0xA4) (by decide) (by
      rw [ue2.pc, show P + BitVec.ofNat 32 0xEE + 0xFFFFFFB6 = P + BitVec.ofNat 32 0xA4 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P hP 0xA4 (by decide)))
    have ke : ∀ q : Fin 32, q.val ≠ 0 → q ≠ (19 : Fin 32) → reg e3 q = reg nW q := fun q h0 h1 => by
      rw [ue3.regs, upd_ne h0 h1]
    refine ⟨e3, S.trans (.cons de1 (.cons de2 (.single de3))), ⟨ue3.pc, rfl, fun _ => rfl⟩,
      by rw [ke _ (by decide) (by decide), kW _ (by decide), r25], fun q hq => ?_, ?_⟩
    · obtain ⟨h0, h1⟩ : q.val ≠ 0 ∧ q ≠ (19 : Fin 32) := by revert hq; revert q; decide
      have h2 : q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 27] := by revert hq; revert q; decide
      rw [ke q h0 h1, kW q h2]
    · rw [ite_eq_left hev]
      refine ⟨ue3.mem, ?_, by rw [ke _ (by decide) (by decide), kW _ (by decide), r24]⟩
      rw [ue3.regs]; simp +decide only [upd_app, ↓reduceIte]
      rw [kW _ (by decide), r19]; exact ofNat_add_ofNat pos 1
  · obtain ⟨e1, de1, ue1⟩ := uW.self.taken hc 0xF0 naf_at_ea (by decide) (by
      rw [W12, show (v + carry) % 2 = 1 by omega, hzW]; rfl)
    obtain ⟨nO, cO, uO⟩ := St.block nafIO ue1 hc nafIO_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, nafIO, upd_app, ↓reduceIte, and_true]
      rw [kW (18 : Fin 32) (by decide), kW (19 : Fin 32) (by decide), r18, r19, ev_add, add_lit_zero]
      repeat' apply And.intro
      all_goals first | exact True.intro | exact sOC.sub (c := pos) (l := 1) (by omega))
    simp only [runBlock, BInstr.run, nafIO] at uO
    have MO := uO.mem
    simp +decide only [upd_app, ↓reduceIte] at MO
    rw [kW (18 : Fin 32) (by decide), kW (19 : Fin 32) (by decide), r18, r19, ev_add, add_lit_zero, W10, W11,
      W25, D2, D3] at MO
    have hcO : CodeIn nO.mem P nonAdjacentFormCode := by
      rw [MO]; exact hc.store8 (sOC.sub (c := pos) (l := 1) (by omega))
    have uO' : St nO.mem P nO 0x11C (reg nO) := ⟨uO.pc, rfl, fun _ => rfl⟩
    obtain ⟨e3, de3, ue3⟩ := uO'.jump hcO naf_at_11c (off' := 0xA4) (by decide) (by
      rw [uO'.pc, show P + BitVec.ofNat 32 0x11C + 0xFFFFFF88 = P + BitVec.ofNat 32 0xA4 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P hP 0xA4 (by decide)))
    have kO : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 20, 21, 22, 23, 27] → reg nO q = reg nW q := fun q hq => by
      obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ (24 : Fin 32) ∧
          q ≠ (19 : Fin 32) ∧ q ≠ (25 : Fin 32) := by revert hq; revert q; decide
      rw [uO.regs]; simp only [upd_ne h0 h1, upd_ne h0 h2, upd_ne h0 h3, upd_ne h0 h4, upd_ne h0 h5, upd_ne h0 h6]
    refine ⟨e3, S.trans (.cons de1 (cO.trans (.single de3))), ⟨ue3.pc, rfl, fun _ => rfl⟩, ?_,
      fun q hq => ?_, ?_⟩
    · rw [ue3.regs, uO.regs]; simp +decide only [upd_app, ↓reduceIte]
    · have h2 : q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 27] := by revert hq; revert q; decide
      rw [ue3.regs, kO q hq, kW q h2]
    · rw [ite_eq_right hev]
      refine ⟨by rw [ue3.mem, MO], ?_, ?_⟩
      · rw [ue3.regs, uO.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [kW _ (by decide), r19]; exact ofNat_add_ofNat pos 5
      · rw [ue3.regs, uO.regs]; simp +decide only [upd_app, ↓reduceIte]
        rw [W10, W11, W25, D2]

theorem nafGo_exit (X n pos carry : Nat) (nf : Nat → BitVec 8) (h : 256 ≤ pos) : nafGo X n pos carry nf = nf := by
  cases n with
  | zero => rfl
  | succ n => simp only [nafGo, ite_eq_left h]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The main loop, by induction on its passes: from `0xA4` it reaches
`0x11E` with `nafGo`'s digits at `out`. -/
theorem naf_loop {P F8 out : Word} {X : Nat} {M0 : Word → BitVec 8} (hP : P.toNat % 2 = 0) (hX : X < 2 ^ 256)
    (hF8 : F8.toNat % 4 = 0) (hc : CodeIn M0 P nonAdjacentFormCode) (hls : CodeIn M0 (P + 0x4450) lshrdi3Code)
    (has : CodeIn M0 (P + 0x442C) ashldi3Code)
    (sOC : Sep out 256 P nonAdjacentFormCode.length) (sOL : Sep out 256 (P + 0x4450) lshrdi3Code.length)
    (sOA : Sep out 256 (P + 0x442C) ashldi3Code.length) (sOB : Sep out 256 F8 40)
    (hbuf : ∀ j, j < 10 → memLoad32 M0 (F8 + BitVec.ofNat 32 (4 * j)) = nafWord X j) :
    ∀ n pos carry (nf : Nat → BitVec 8) (mk : Machine), St mk.mem P mk 0xA4 (reg mk) →
      (∀ x, Sep out 256 x 1 → mk.mem x = M0 x) → (∀ k, k < 256 → mk.mem (out + BitVec.ofNat 32 k) = nf k) →
      pos ≤ 260 → carry < 2 → 256 - pos ≤ n →
      reg mk (19 : Fin 32) = BitVec.ofNat 32 pos → reg mk (24 : Fin 32) = BitVec.ofNat 32 carry →
      reg mk (25 : Fin 32) = 0 → reg mk (20 : Fin 32) = 0x100 → reg mk (21 : Fin 32) = F8 →
      reg mk (22 : Fin 32) = 0x3B → reg mk (23 : Fin 32) = 0x40 → reg mk (18 : Fin 32) = out →
      ∃ mk', Steps mk mk' ∧ St mk'.mem P mk' 0x11E (reg mk') ∧ (∀ x, Sep out 256 x 1 → mk'.mem x = M0 x) ∧
        (∀ k, k < 256 → mk'.mem (out + BitVec.ofNat 32 k) = nafGo X n pos carry nf k) ∧
        ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 20, 21, 22, 23, 27] → reg mk' q = reg mk q := by
  have cIn : ∀ (mk : Machine) (b : Word) (code : List Nat), CodeIn M0 b code → Sep out 256 b code.length →
      (∀ x, Sep out 256 x 1 → mk.mem x = M0 x) → CodeIn mk.mem b code := fun mk b code hcb hs hf i hi => by
    rw [hf _ (hs.subR (c := i) (l := 1) (by omega))]; exact hcb i hi
  intro n
  induction n with
  | zero =>
    intro pos carry nf mk t hf ho hp hcar hn r19 r24 r25 r20 r21 r22 r23 r18
    obtain ⟨n1, d1, u1⟩ := t.taken (cIn mk _ _ hc sOC hf) 0x11E naf_at_a4 (by decide) (by
      rw [r19, r20]; exact naf_exit pos (by omega) (by omega))
    exact ⟨n1, .single d1, ⟨u1.pc, rfl, fun _ => rfl⟩, fun x hx => by rw [u1.mem]; exact hf x hx,
      fun k hk => by rw [u1.mem]; exact ho k hk, fun q _ => by rw [u1.regs]⟩
  | succ n ih =>
    intro pos carry nf mk t hf ho hp hcar hn r19 r24 r25 r20 r21 r22 r23 r18
    have hcM := cIn mk _ _ hc sOC hf
    by_cases hx : 256 ≤ pos
    · obtain ⟨n1, d1, u1⟩ := t.taken hcM 0x11E naf_at_a4 (by decide) (by
        rw [r19, r20]; exact naf_exit pos (by omega) hx)
      refine ⟨n1, .single d1, ⟨u1.pc, rfl, fun _ => rfl⟩, fun x hx' => by rw [u1.mem]; exact hf x hx',
        fun k hk => ?_, fun q _ => by rw [u1.regs]⟩
      rw [u1.mem, nafGo_exit X _ pos carry nf hx]; exact ho k hk
    have hpos : pos < 256 := by omega
    have hb : ∀ j, j < 10 → memLoad32 mk.mem (F8 + BitVec.ofNat 32 (4 * j)) = nafWord X j := fun j hj => by
      rw [← hbuf j hj]
      exact memLoad32_congr fun i hi => by
        rw [add_ofNat_assoc]; exact hf _ (sOB.subR (c := 4 * j + i) (l := 1) (by omega))
    obtain ⟨mk1, c1, t1, r25', k1, hite⟩ := naf_iter mk hP hcM (cIn mk _ _ hls sOL hf) (cIn mk _ _ has sOA hf) t hX
      hpos hcar r19 r24 r25 r20 r21 r22 r23 r18 hF8 hb sOC
    have q : ∀ (r : Fin 32) (v : Word), r.val ∈ [2, 3, 4, 18, 20, 21, 22, 23, 27] → reg mk r = v → reg mk1 r = v :=
      fun r v hr h => by rw [k1 r hr, h]
    by_cases hev : (carry + X / 2 ^ pos % 32) % 2 = 0
    · rw [ite_eq_left hev] at hite
      obtain ⟨hm, h19, h24⟩ := hite
      obtain ⟨mk', c', t', f', o', k'⟩ := ih (pos + 1) carry nf mk1 t1 (fun x hx => by rw [hm]; exact hf x hx)
        (fun k hk => by rw [hm]; exact ho k hk) (by omega) hcar (by omega) h19 h24 r25'
        (q _ _ (by decide) r20) (q _ _ (by decide) r21) (q _ _ (by decide) r22) (q _ _ (by decide) r23)
        (q _ _ (by decide) r18)
      refine ⟨mk', c1.trans c', t', f', fun k hk => ?_, fun r hr => by rw [k' r hr, k1 r hr]⟩
      rw [o' k hk]; simp only [nafGo, ite_eq_right hx, ite_eq_left hev]
    · rw [ite_eq_right hev] at hite
      obtain ⟨hm, h19, h24⟩ := hite
      obtain ⟨mk', c', t', f', o', k'⟩ := ih (pos + 5) (if carry + X / 2 ^ pos % 32 < 16 then 0 else 1)
        (fun k => if k = pos then
          BitVec.ofNat 8 (if carry + X / 2 ^ pos % 32 < 16 then carry + X / 2 ^ pos % 32
            else carry + X / 2 ^ pos % 32 + 224)
          else nf k) mk1 t1
        (fun x hx => by
          rw [hm, memStore8_ne (fun e => hx pos hpos 0 (by decide) (by rw [add_ofNat_zero]; exact e.symm))]
          exact hf x hx)
        (fun k hk => by
          rw [hm]
          by_cases hkp : k = pos
          · subst hkp; rw [memStore8_same]; exact (ite_eq_left rfl).symm
          · rw [memStore8_ne (add_ofNat_ne out (by omega) (by omega) hkp), ite_eq_right hkp]; exact ho k hk)
        (by omega) (by split <;> decide) (by omega) h19 h24 r25'
        (q _ _ (by decide) r20) (q _ _ (by decide) r21) (q _ _ (by decide) r22) (q _ _ (by decide) r23)
        (q _ _ (by decide) r18)
      refine ⟨mk', c1.trans c', t', f', fun k hk => ?_, fun r hr => by rw [k' r hr, k1 r hr]⟩
      rw [o' k hk]; simp only [nafGo, ite_eq_right hx, ite_eq_right hev]

theorem naf_cnt : ∀ k, k < 4 → aluEval .add (BitVec.ofNat 32 (4 - k)) 0xFFFFFFFF = BitVec.ofNat 32 (4 - (k + 1)) ∧
    branchTaken .bne (BitVec.ofNat 32 (4 - (k + 1))) 0 = decide (k ≠ 3) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- One pass of the loop that reads the scalar into the buffer: bytes `8 k`
through `8 k + 7` become two little-endian words. -/
theorem naf_l1_step {M : Word → BitVec 8} {P s B : Word} {k : Nat} (mk : Machine) {f : Fin 32 → Word}
    (hc : CodeIn M P nonAdjacentFormCode) (t : St M P mk 0x44 f) (hk : k < 4)
    (h9 : f (9 : Fin 32) = s + BitVec.ofNat 32 (8 * k)) (h8 : f (8 : Fin 32) = B + BitVec.ofNat 32 (8 * k))
    (h16 : f a6 = BitVec.ofNat 32 (4 - k)) (hB : B.toNat % 4 = 0) (sBC : Sep B 32 P nonAdjacentFormCode.length) :
    ∃ mk', Steps mk mk' ∧
      St (memStore32 (memStore32 M (B + BitVec.ofNat 32 (8 * k)) (memLoad32 M (s + BitVec.ofNat 32 (8 * k))))
        (B + BitVec.ofNat 32 (8 * k) + 0x4) (memLoad32 M (s + BitVec.ofNat 32 (8 * k) + 4))) P mk'
        (if k = 3 then 0x8E else 0x44) (reg mk') ∧
      reg mk' (9 : Fin 32) = s + BitVec.ofNat 32 (8 * (k + 1)) ∧
      reg mk' (8 : Fin 32) = B + BitVec.ofNat 32 (8 * (k + 1)) ∧ reg mk' a6 = BitVec.ofNat 32 (4 - (k + 1)) ∧
      ∀ q : Fin 32, q.val ∈ [1, 2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg mk' q = f q := by
  obtain ⟨C1, C2⟩ := naf_cnt k hk
  have ad4 : ∀ (a : Word) (j : Nat), a + BitVec.ofNat 32 j + 0x4 = a + BitVec.ofNat 32 (j + 4) :=
    fun a j => add_ofNat_assoc a j 4
  have w5 : ∀ a : Word, a + 4 + 1 = a + 0x5 := fun a => by rw [BitVec.add_assoc]; rfl
  have w6 : ∀ a : Word, a + 4 + 2 = a + 0x6 := fun a => by rw [BitVec.add_assoc]; rfl
  have w7 : ∀ a : Word, a + 4 + 3 = a + 0x7 := fun a => by rw [BitVec.add_assoc]; rfl
  obtain ⟨nA, cA, uA⟩ := St.block nafL1A t hc nafL1A_end (by simp +decide only [BlockOk, BInstr.ok, nafL1A, and_true])
  simp only [runBlock, BInstr.run, nafL1A] at uA
  have VA2 : reg nA a2 = memLoad32 M (s + BitVec.ofNat 32 (8 * k)) := by
    rw [uA.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [h9]
    apply BitVec.eq_of_toNat_eq
    rw [le4_A, memLoad32_toNat, add_lit_zero]
  have VA0 : reg nA a0 = memLoad32 M (s + BitVec.ofNat 32 (8 * k) + 4) := by
    rw [uA.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [h9]
    apply BitVec.eq_of_toNat_eq
    rw [le4_B, memLoad32_toNat, w5, w6, w7]
  have kA : ∀ q : Fin 32, q.val ∈ [1, 2, 3, 4, 8, 9, 16, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nA q = f q :=
    fun q hq => by
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8'⟩ : q.val ≠ 0 ∧ q ≠ (17 : Fin 32) ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧
          q ≠ (5 : Fin 32) ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a5 := by revert hq; revert q; decide
      rw [uA.regs]; simp only [upd_ne h0 h1, upd_ne h0 h2, upd_ne h0 h3, upd_ne h0 h4, upd_ne h0 h5, upd_ne h0 h6,
        upd_ne h0 h7, upd_ne h0 h8']
  have A8 : reg nA (8 : Fin 32) = B + BitVec.ofNat 32 (8 * k) := by rw [kA _ (by decide), h8]
  have uA' : St M P nA 0x80 (reg nA) := uA.self
  obtain ⟨nB, cB, uB⟩ := St.block nafL1B uA' hc nafL1B_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, nafL1B, and_true]
    rw [A8]
    repeat' apply And.intro
    all_goals first | exact True.intro | (rw [add_lit_zero]; exact aligned_add hB (by omega)) |
      (rw [add_lit_zero]; exact sBC.sub (c := 8 * k) (l := 4) (by omega)) |
      (rw [ad4]; exact aligned_add hB (by omega)) | (rw [ad4]; exact sBC.sub (c := 8 * k + 4) (l := 4) (by omega)))
  simp only [runBlock, BInstr.run, nafL1B] at uB
  have MB := uB.mem
  rw [A8, VA2, VA0, add_lit_zero] at MB
  have hcB : CodeIn nB.mem P nonAdjacentFormCode := by
    rw [MB]; exact (hc.store32 (sBC.sub (c := 8 * k) (l := 4) (by omega))).store32
      (by rw [ad4]; exact sBC.sub (c := 8 * k + 4) (l := 4) (by omega))
  have uB' : St nB.mem P nB 0x8A (reg nB) := ⟨uB.pc, rfl, fun _ => rfl⟩
  have B16 : reg nB a6 = BitVec.ofNat 32 (4 - (k + 1)) := by
    rw [uB.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [kA _ (by decide), h16, C1]
  have B9 : reg nB (9 : Fin 32) = s + BitVec.ofNat 32 (8 * (k + 1)) := by
    rw [uB.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [kA _ (by decide), h9, ev_add]
    exact (add_ofNat_assoc s (8 * k) 8).trans (by congr 2)
  have B8 : reg nB (8 : Fin 32) = B + BitVec.ofNat 32 (8 * (k + 1)) := by
    rw [uB.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [A8, ev_add]
    exact (add_ofNat_assoc B (8 * k) 8).trans (by congr 2)
  have kB : ∀ q : Fin 32, q.val ∈ [1, 2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nB q = f q :=
    fun q hq => by
      obtain ⟨h0, h1, h2, h3⟩ : q.val ≠ 0 ∧ q ≠ (9 : Fin 32) ∧ q ≠ (8 : Fin 32) ∧ q ≠ a6 := by revert hq; revert q; decide
      have h4 : q.val ∈ [1, 2, 3, 4, 8, 9, 16, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
      rw [uB.regs]; simp only [upd_ne h0 h1, upd_ne h0 h2, upd_ne h0 h3]; exact kA q h4
  by_cases h3 : k = 3
  · obtain ⟨n1, d1, u1⟩ := uB'.notTaken hcB 0x8E naf_at_8a (by decide) (by
      rw [B16, show reg nB x0 = 0 from uB'.zero, C2, decide_eq_false (by omega)])
    refine ⟨n1, cA.trans (cB.trans (.single d1)), ?_, by rw [u1.regs]; exact B9, by rw [u1.regs]; exact B8,
      by rw [u1.regs]; exact B16, fun q hq => by rw [u1.regs]; exact kB q hq⟩
    rw [ite_eq_left h3]; exact ⟨u1.pc, by rw [u1.mem, MB], fun _ => rfl⟩
  · obtain ⟨n1, d1, u1⟩ := uB'.taken hcB 0x44 naf_at_8a (by decide) (by
      rw [B16, show reg nB x0 = 0 from uB'.zero, C2, decide_eq_true h3])
    refine ⟨n1, cA.trans (cB.trans (.single d1)), ?_, by rw [u1.regs]; exact B9, by rw [u1.regs]; exact B8,
      by rw [u1.regs]; exact B16, fun q hq => by rw [u1.regs]; exact kB q hq⟩
    rw [ite_eq_right h3]; exact ⟨u1.pc, by rw [u1.mem, MB], fun _ => rfl⟩

/-- What `non_adjacent_form` needs: its code and that of `memset`,
`__lshrdi3`, and `__ashldi3`; an aligned stack with 0x60 bytes below `sp`; and
the stack region, the 256-byte result, the 32-byte scalar, and the code
apart. -/
structure NAFEnv (M : Word → BitVec 8) (P sp0 out s : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P nonAdjacentFormCode
  ms : CodeIn M (P + 0x4236) memsetCode
  ls : CodeIn M (P + 0x4450) lshrdi3Code
  as : CodeIn M (P + 0x442C) ashldi3Code
  hsa : sp0.toNat % 4 = 0
  hS : 0x60 ≤ sp0.toNat
  sGC : Sep (sp0 + 0xFFFFFFA0) 0x60 P nonAdjacentFormCode.length
  sGM : Sep (sp0 + 0xFFFFFFA0) 0x60 (P + 0x4236) memsetCode.length
  sGL : Sep (sp0 + 0xFFFFFFA0) 0x60 (P + 0x4450) lshrdi3Code.length
  sGA : Sep (sp0 + 0xFFFFFFA0) 0x60 (P + 0x442C) ashldi3Code.length
  sOC : Sep out 256 P nonAdjacentFormCode.length
  sOM : Sep out 256 (P + 0x4236) memsetCode.length
  sOL : Sep out 256 (P + 0x4450) lshrdi3Code.length
  sOA : Sep out 256 (P + 0x442C) ashldi3Code.length
  sOG : Sep out 256 (sp0 + 0xFFFFFFA0) 0x60
  sSG : Sep s 32 (sp0 + 0xFFFFFFA0) 0x60
  sSO : Sep s 32 out 256
  how : out.toNat + 256 < 2 ^ 32

theorem nafScalar_lt (M : Word → BitVec 8) (s : Word) : nafScalar M s < 2 ^ 256 := by
  unfold nafScalar
  have := (memLoad32 M s).isLt; have := (memLoad32 M (s + 4)).isLt; have := (memLoad32 M (s + 8)).isLt
  have := (memLoad32 M (s + 12)).isLt; have := (memLoad32 M (s + 16)).isLt; have := (memLoad32 M (s + 20)).isLt
  have := (memLoad32 M (s + 24)).isLt; have := (memLoad32 M (s + 28)).isLt
  omega

set_option maxRecDepth 20000 in
theorem nafScalar_word (M : Word → BitVec 8) (s : Word) :
    ∀ j, j < 8 → memLoad32 M (s + BitVec.ofNat 32 (4 * j)) = nafWord (nafScalar M s) j := by
  intro j hj
  apply BitVec.eq_of_toNat_eq
  rw [nafWord_toNat]
  unfold nafScalar
  have := (memLoad32 M s).isLt; have := (memLoad32 M (s + 4)).isLt; have := (memLoad32 M (s + 8)).isLt
  have := (memLoad32 M (s + 12)).isLt; have := (memLoad32 M (s + 16)).isLt; have := (memLoad32 M (s + 20)).isLt
  have := (memLoad32 M (s + 24)).isLt; have := (memLoad32 M (s + 28)).isLt
  match j, hj with
  | 0, _ => rw [show s + BitVec.ofNat 32 (4 * 0) = s from add_ofNat_zero s]; omega
  | 1, _ => show (memLoad32 M (s + 4)).toNat = _; omega
  | 2, _ => show (memLoad32 M (s + 8)).toNat = _; omega
  | 3, _ => show (memLoad32 M (s + 12)).toNat = _; omega
  | 4, _ => show (memLoad32 M (s + 16)).toNat = _; omega
  | 5, _ => show (memLoad32 M (s + 20)).toNat = _; omega
  | 6, _ => show (memLoad32 M (s + 24)).toNat = _; omega
  | 7, _ => show (memLoad32 M (s + 28)).toNat = _; omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The compiled `Scalar::non_adjacent_form(5)`**: it writes `nafSpec` of
the scalar at `s`, the Rust source's width-5 NAF digits, to the 256 bytes at
`out`, and changes nothing else but its 0x60 bytes of stack. -/
theorem nonAdjacentForm_correct (m : Machine) {P sp0 out s retAddr : Word} (env : NAFEnv m.mem P sp0 out s)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = s)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (∀ k, k < 256 → m'.mem (out + BitVec.ofNat 32 k) = nafSpec (nafScalar m.mem s) k) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFA0) 0x60 x 1 → Sep out 256 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFFA0 = G := ⟨_, rfl⟩
  have hS := env.hS
  have sGC := env.sGC; have sGM := env.sGM; have sGL := env.sGL; have sGA := env.sGA
  have sOG := env.sOG; have sSG := env.sSG
  rw [hG] at sGC sGM sGL sGA sOG sSG ⊢
  have hGn : G.toNat + 0x60 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFFA0 : Word).toNat = 4294967200 from rfl]
    have := sp0.isLt; omega
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsa (k := 0xFFFFFFA0) (by decide)
  have eGs : G + 0x60 = sp0 := by rw [← hG, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have slotC : ∀ (o : Word), o.toNat + 4 ≤ 0x60 → ∀ {b : Word} {l : Nat}, Sep G 0x60 b l → Sep (G + o) 4 b l := by
    intro o h b l hs
    rw [← ofNat_toNat_self o]; exact hs.sub (c := o.toNat) (l := 4) (by omega)
  have hc := env.cod
  have hX := nafScalar_lt m.mem s
  have hwX := nafScalar_word m.mem s
  obtain ⟨X, hXdef⟩ : ∃ X, nafScalar m.mem s = X := ⟨_, rfl⟩
  rw [hXdef] at hX hwX ⊢
  have st0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, d1, u1⟩ := st0.aluImm hc naf_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFA0) sp = G := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hG]
  obtain ⟨ms, cs, us⟩ := St.block (saveBlock nafPs) u1 hc nafSave_end (saveBlock_ok _ nafPs _ fun p hp => by
    rw [sp1]
    simp only [nafPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨aligned_add hGa (by decide), slotC _ (by decide) sGC⟩)
  simp only [saveBlock_run] at us
  rw [sp1] at us
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem G (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFA0)) nafPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at us
  have frSv : ∀ x, Sep G 0x60 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside nafPs fun p hp => by
      simp only [nafPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact slotC _ (by decide) hx
  have hslv : ∀ r o, (r, o) ∈ nafPs → memLoad32 Msv (G + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [nafPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ q, q ≠ sp → reg ms q = reg m q := fun q h => by rw [us.regs, updz hz h]
  have sp2 : reg ms sp = G := by rw [us.regs]; exact sp1
  have cInSv : ∀ (b : Word) (code : List Nat), CodeIn m.mem b code → Sep G 0x60 b code.length →
      CodeIn Msv b code := fun b code hcb hg i hi => by
    rw [frSv _ (hg.subR (c := i) (l := 1) (by omega))]; exact hcb i hi
  have hcS := cInSv _ _ hc sGC
  have hz2 : reg ms 0 = 0 := us.self.zero
  -- `s1 = scalar`, `s2 = out`, then `memset(out, 0, 256)`
  obtain ⟨mP, cP, uP⟩ := St.block nafPre1 us.self hcS nafPre1_end (by
    simp +decide only [BlockOk, BInstr.ok, nafPre1, and_true])
  simp only [runBlock, BInstr.run, nafPre1] at uP
  have kP : ∀ q : Fin 32, q.val ≠ 0 → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) → q ≠ a2 → q ≠ a1 →
      reg mP q = reg ms q := fun q h0 h1 h2 h3 h4 => by
    rw [uP.regs]; simp only [upd_ne h0 h1, upd_ne h0 h2, upd_ne h0 h3, upd_ne h0 h4]
  have P9 : reg mP (9 : Fin 32) = s := by
    rw [uP.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [hz2, r2 a1 (by decide), ha1]; exact BitVec.zero_add s
  have P18 : reg mP (18 : Fin 32) = out := by
    rw [uP.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a0 (by decide), ha0]
    exact BitVec.zero_add out
  have Pa2 : reg mP a2 = 0x100 := by rw [uP.regs]; simp +decide only [upd_app, ↓reduceIte]
  have Pa1 : reg mP a1 = 0 := by rw [uP.regs]; simp +decide only [upd_app, ↓reduceIte]
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := uP.self.callRa hcS naf_at_24 naf_at_28 (cb := P + 0x4236)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x4236 (by decide))
  have r2' : ∀ q, q ≠ ra → reg n2 q = reg mP q := fun q h => by rw [regs2]; exact updz uP.self.zero h
  obtain ⟨m3, c3, pc3, mem3, _, k3⟩ := memset_correct n2 (P + 0x4236) (P + BitVec.ofNat 32 (0x24 + 8)) out 0 256
    (fun i hi => by rw [mem2]; exact cInSv _ _ env.ms sGM i hi) (even_at P env.hP 0x4236 (by decide)) pc2
    (by rw [r2' a0 (by decide), kP a0 (by decide) (by decide) (by decide) (by decide) (by decide),
      r2 a0 (by decide), ha0])
    (by rw [r2' a1 (by decide), Pa1]) (by rw [r2' a2 (by decide), Pa2]; rfl)
    (by rw [regs2]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x24 + 8) (by decide)))
    env.how env.sOM
  rw [mem2, show (0 : Word).extractLsb' 0 8 = 0 from rfl] at mem3
  have u3 : St m3.mem P m3 0x2C (reg m3) := ⟨pc3, rfl, fun _ => rfl⟩
  have hc3 : CodeIn m3.mem P nonAdjacentFormCode := fun i hi => by
    rw [mem3, fillBytes_sep (env.sOC.subR (c := i) (l := 1) (by omega)) (Nat.le_refl 256)]; exact hcS i hi
  have sp3 : reg m3 sp = G := by
    rw [k3 sp (by decide) (by decide) (by decide) (by decide) (by decide), r2' sp (by decide),
      kP sp (by decide) (by decide) (by decide) (by decide) (by decide), sp2]
  obtain ⟨B, hB⟩ : ∃ B, G + 0x8 = B := ⟨_, rfl⟩
  have hBn : B.toNat = G.toNat + 8 := by
    rw [← hB, BitVec.toNat_add, show (0x8 : Word).toNat = 8 from rfl]; have := sp0.isLt; omega
  have hBa : B.toNat % 4 = 0 := by rw [hBn]; omega
  -- `s0 = &x_u64`, then `memset(x_u64, 0, 40)`
  obtain ⟨m4, c4, u4⟩ := St.block nafPre2 u3 hc3 nafPre2_end (by simp +decide only [BlockOk, BInstr.ok, nafPre2, and_true])
  simp only [runBlock, BInstr.run, nafPre2] at u4
  have Q0 : reg m4 a0 = B := by rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp3, ev_add, hB]
  have Q8 : reg m4 (8 : Fin 32) = B := by rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [sp3, ev_add, hB]
  have kQ : ∀ q : Fin 32, q.val ≠ 0 → q ≠ a0 → q ≠ a2 → q ≠ a1 → q ≠ (8 : Fin 32) → reg m4 q = reg m3 q :=
    fun q h0 h1 h2 h3 h4 => by rw [u4.regs]; simp only [upd_ne h0 h1, upd_ne h0 h2, upd_ne h0 h3, upd_ne h0 h4]
  obtain ⟨n5, c5, pc5, mem5, regs5⟩ := u4.self.callRa hc3 naf_at_36 naf_at_3a (cb := P + 0x4236)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x4236 (by decide))
  have r5 : ∀ q, q ≠ ra → reg n5 q = reg m4 q := fun q h => by rw [regs5]; exact updz u4.self.zero h
  have hcM3 : CodeIn m3.mem (P + 0x4236) memsetCode := fun i hi => by
    rw [mem3, fillBytes_sep (env.sOM.subR (c := i) (l := 1) (by omega)) (Nat.le_refl 256)]
    exact cInSv _ _ env.ms sGM i hi
  obtain ⟨m5, c5', pc5', mem5', _, k5⟩ := memset_correct n5 (P + 0x4236) (P + BitVec.ofNat 32 (0x36 + 8)) B 0 40
    (fun i hi => by rw [mem5]; exact hcM3 i hi) (even_at P env.hP 0x4236 (by decide)) pc5
    (by rw [r5 a0 (by decide), Q0]) (by rw [r5 a1 (by decide), u4.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [r5 a2 (by decide), u4.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [regs5]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x36 + 8) (by decide)))
    (by rw [hBn]; have := sp0.isLt; omega) (by rw [← hB]; exact sGM.sub (c := 8) (l := 40) (by decide))
  rw [mem5, show (0 : Word).extractLsb' 0 8 = 0 from rfl] at mem5'
  have sepB : ∀ x, Sep G 0x60 x 1 → Sep B 40 x 1 := fun x hx => by rw [← hB]; exact hx.sub (c := 8) (by decide)
  have fr5 : ∀ x, Sep B 40 x 1 → Sep out 256 x 1 → Sep G 0x60 x 1 → m5.mem x = m.mem x := fun x hb ho hg => by
    rw [mem5', fillBytes_sep hb (Nat.le_refl 40), mem3, fillBytes_sep ho (Nat.le_refl 256), frSv x hg]
  have hc5 : CodeIn m5.mem P nonAdjacentFormCode := fun i hi => by
    rw [fr5 _ (sepB _ (sGC.subR (c := i) (l := 1) (by omega))) (env.sOC.subR (c := i) (l := 1) (by omega))
      (sGC.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have u5 : St m5.mem P m5 0x3E (reg m5) := ⟨pc5', rfl, fun _ => rfl⟩
  obtain ⟨n6, d6, u6⟩ := u5.aluImm hc5 naf_at_3e (off' := 0x40) (by decide)
  have hz5 : reg m5 0 = 0 := u5.zero
  obtain ⟨n7, d7, u7⟩ := u6.notTaken hc5 0x44 naf_at_40 (by decide) (by
    simp +decide only [upd_app, ↓reduceIte]; rw [hz5]; rfl)
  -- the scalar's words, through the buffer-reading loop
  have sB : Sep B 32 P nonAdjacentFormCode.length := by rw [← hB]; exact sGC.sub (c := 8) (l := 32) (by decide)
  have sSB : Sep s 32 B 40 := by rw [← hB]; exact sSG.subR (c := 8) (l := 40) (by decide)
  have stepI : ∀ (k : Nat) (M : Word → BitVec 8), k < 4 → (∀ x, Sep B 40 x 1 → M x = m5.mem x) →
      (∀ j, j < 10 → memLoad32 M (B + BitVec.ofNat 32 (4 * j)) = if j < 2 * k then nafWord X j else 0) →
      (∀ x, Sep B 40 x 1 → memStore32 (memStore32 M (B + BitVec.ofNat 32 (8 * k))
          (memLoad32 M (s + BitVec.ofNat 32 (8 * k)))) (B + BitVec.ofNat 32 (8 * k) + 0x4)
          (memLoad32 M (s + BitVec.ofNat 32 (8 * k) + 4)) x = m5.mem x) ∧
      (∀ j, j < 10 → memLoad32 (memStore32 (memStore32 M (B + BitVec.ofNat 32 (8 * k))
          (memLoad32 M (s + BitVec.ofNat 32 (8 * k)))) (B + BitVec.ofNat 32 (8 * k) + 0x4)
          (memLoad32 M (s + BitVec.ofNat 32 (8 * k) + 4))) (B + BitVec.ofNat 32 (4 * j)) =
        if j < 2 * (k + 1) then nafWord X j else 0) := by
    intro k M hk hf hw
    have hsM : ∀ i, i < 32 → M (s + BitVec.ofNat 32 i) = m.mem (s + BitVec.ofNat 32 i) := fun i hi => by
      rw [hf _ (sSB.symm.subR (c := i) (l := 1) (by omega)), fr5 _ (sSB.symm.subR (c := i) (l := 1) (by omega))
        (env.sSO.symm.subR (c := i) (l := 1) (by omega)) (sSG.symm.subR (c := i) (l := 1) (by omega))]
    have L0 : memLoad32 M (s + BitVec.ofNat 32 (8 * k)) = nafWord X (2 * k) := by
      rw [← hwX (2 * k) (by omega), show 4 * (2 * k) = 8 * k by omega]
      exact memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact hsM _ (by omega)
    have L1 : memLoad32 M (s + BitVec.ofNat 32 (8 * k) + 4) = nafWord X (2 * k + 1) := by
      have e : s + BitVec.ofNat 32 (8 * k) + 4 = s + BitVec.ofNat 32 (4 * (2 * k + 1)) :=
        (add_ofNat_assoc s (8 * k) 4).trans (by congr 2; omega)
      rw [e, ← hwX (2 * k + 1) (by omega)]
      exact memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact hsM _ (by omega)
    have eB4 : B + BitVec.ofNat 32 (8 * k) + 0x4 = B + BitVec.ofNat 32 (8 * k + 4) := add_ofNat_assoc B (8 * k) 4
    rw [eB4, L0, L1]
    refine ⟨fun x hx => ?_, fun j hj => ?_⟩
    · rw [memStore32_get_sep (a := B + BitVec.ofNat 32 (8 * k + 4)) (hx.sub (c := 8 * k + 4) (l := 4) (by omega)),
        memStore32_get_sep (a := B + BitVec.ofNat 32 (8 * k)) (hx.sub (c := 8 * k) (l := 4) (by omega))]
      exact hf x hx
    · by_cases h1 : j = 2 * k + 1
      · subst h1
        rw [show 4 * (2 * k + 1) = 8 * k + 4 by omega, memLoad32_store32_same, ite_eq_left (by omega)]
      by_cases h2 : j = 2 * k
      · subst h2
        rw [memLoad32_store32_sep (a := B + BitVec.ofNat 32 (8 * k + 4)) (b := B + BitVec.ofNat 32 (4 * (2 * k)))
          (sep_offsets B (.inr (by omega)) (by omega) (by omega)), show 4 * (2 * k) = 8 * k by omega,
          memLoad32_store32_same, ite_eq_left (by omega)]
      rw [memLoad32_store32_sep (a := B + BitVec.ofNat 32 (8 * k + 4)) (b := B + BitVec.ofNat 32 (4 * j))
          (sep_offsets B (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (a := B + BitVec.ofNat 32 (8 * k)) (b := B + BitVec.ofNat 32 (4 * j))
          (sep_offsets B (by omega) (by omega) (by omega)), hw j hj]
      by_cases hj' : j < 2 * k
      · rw [ite_eq_left hj', ite_eq_left (by omega)]
      · rw [ite_eq_right hj', ite_eq_right (by omega)]
  have fz : ∀ i, i < 40 → m5.mem (B + BitVec.ofNat 32 i) = 0 := fun i hi => by
    rw [mem5']; unfold fillBytes; rw [add_sub_toNat B (by omega), ite_eq_left hi]
  have I0 : ∀ j, j < 10 → memLoad32 m5.mem (B + BitVec.ofNat 32 (4 * j)) = if j < 2 * 0 then nafWord X j else 0 :=
    fun j hj => by
      rw [ite_eq_right (by omega), memLoad32_congr (M := fun _ => 0) fun i hi => by
        rw [add_ofNat_assoc]; exact fz _ (by omega)]
      show (0 : BitVec 8) ++ (0 : BitVec 8) ++ (0 : BitVec 8) ++ (0 : BitVec 8) = (0 : BitVec 32)
      decide
  have sB40 : Sep B 40 P nonAdjacentFormCode.length := by rw [← hB]; exact sGC.sub (c := 8) (l := 40) (by decide)
  have cInB : ∀ M : Word → BitVec 8, (∀ x, Sep B 40 x 1 → M x = m5.mem x) → CodeIn M P nonAdjacentFormCode :=
    fun M hf i hi => by rw [hf _ (sB40.subR (c := i) (l := 1) (by omega))]; exact hc5 i hi
  have r59 : reg m5 (9 : Fin 32) = s := by
    rw [k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), r5 _ (by decide),
      kQ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      k3 _ (by decide) (by decide) (by decide) (by decide) (by decide), r2' _ (by decide), P9]
  have r58 : reg m5 (8 : Fin 32) = B := by
    rw [k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), r5 _ (by decide), Q8]
  obtain ⟨q1, l1, t1, h91, h81, h161, kq1⟩ := naf_l1_step n7 hc5 u7 (k := 0) (by decide)
    (by simp +decide only [upd_app, ↓reduceIte]; rw [r59]; exact (add_ofNat_zero s).symm)
    (by simp +decide only [upd_app, ↓reduceIte]; rw [r58]; exact (add_ofNat_zero B).symm)
    (by simp +decide only [upd_app, ↓reduceIte]; rw [hz5]; rfl) hBa sB
  obtain ⟨F1, W1⟩ := stepI 0 m5.mem (by decide) (fun _ _ => rfl) I0
  rw [ite_eq_right (by decide)] at t1
  obtain ⟨q2, l2, t2, h92, h82, h162, kq2⟩ := naf_l1_step q1 (cInB _ F1) t1 (k := 1) (by decide)
    h91 h81 h161 hBa sB
  obtain ⟨F2, W2⟩ := stepI 1 _ (by decide) F1 W1
  rw [ite_eq_right (by decide)] at t2
  obtain ⟨q3, l3, t3, h93, h83, h163, kq3⟩ := naf_l1_step q2 (cInB _ F2) t2 (k := 2) (by decide)
    h92 h82 h162 hBa sB
  obtain ⟨F3, W3⟩ := stepI 2 _ (by decide) F2 W2
  rw [ite_eq_right (by decide)] at t3
  obtain ⟨q4, l4, t4, h94, h84, h164, kq4⟩ := naf_l1_step q3 (cInB _ F3) t3 (k := 3) (by decide)
    h93 h83 h163 hBa sB
  obtain ⟨F4, W4⟩ := stepI 3 _ (by decide) F3 W3
  rw [ite_eq_left rfl] at t4
  have hzq4 : reg q4 0 = 0 := t4.zero
  have f7k : ∀ q : Fin 32, q.val ∈ [1, 2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg q4 q = reg m5 q :=
    fun q hq => by
      obtain ⟨h0, h1⟩ : q.val ≠ 0 ∧ q ≠ a6 := by revert hq; revert q; decide
      rw [kq4 q hq, kq3 q hq, kq2 q hq, kq1 q hq, upd_ne h0 h1]
  have r5sp : reg m5 sp = G := by
    rw [k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), r5 _ (by decide),
      kQ _ (by decide) (by decide) (by decide) (by decide) (by decide), sp3]
  have r518 : reg m5 (18 : Fin 32) = out := by
    rw [k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), r5 _ (by decide),
      kQ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      k3 _ (by decide) (by decide) (by decide) (by decide) (by decide), r2' _ (by decide), P18]
  -- the main loop's registers, then the loop
  obtain ⟨mM, cM, uM⟩ := St.block nafMid t4 (cInB _ F4) nafMid_end (by
    simp +decide only [BlockOk, BInstr.ok, nafMid, and_true])
  simp only [runBlock, BInstr.run, nafMid] at uM
  have kM : ∀ q : Fin 32, q.val ∈ [1, 2, 3, 4, 18, 26, 27] → reg mM q = reg q4 q := fun q hq => by
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ : q.val ≠ 0 ∧ q ≠ (25 : Fin 32) ∧ q ≠ (24 : Fin 32) ∧
        q ≠ (19 : Fin 32) ∧ q ≠ (20 : Fin 32) ∧ q ≠ (21 : Fin 32) ∧ q ≠ (22 : Fin 32) ∧ q ≠ (23 : Fin 32) := by
      revert hq; revert q; decide
    rw [uM.regs]; simp only [upd_ne h0 h1, upd_ne h0 h2, upd_ne h0 h3, upd_ne h0 h4, upd_ne h0 h5, upd_ne h0 h6,
      upd_ne h0 h7]
  have sOB : Sep out 256 B 40 := by rw [← hB]; exact sOG.subR (c := 8) (l := 40) (by decide)
  have cIn4 : ∀ M : Word → BitVec 8, (∀ x, Sep B 40 x 1 → M x = m5.mem x) → ∀ (b : Word) (code : List Nat),
      CodeIn m.mem b code → Sep G 0x60 b code.length → Sep out 256 b code.length → CodeIn M b code :=
    fun M hf b code hcb hg ho i hi => by
      rw [hf _ (sepB _ (hg.subR (c := i) (l := 1) (by omega))),
        fr5 _ (sepB _ (hg.subR (c := i) (l := 1) (by omega))) (ho.subR (c := i) (l := 1) (by omega))
          (hg.subR (c := i) (l := 1) (by omega))]
      exact hcb i hi
  have w89 : ∀ j, 8 ≤ j → nafWord X j = 0 := fun j hj => by
    unfold nafWord
    rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by decide) (by omega)))]; rfl
  obtain ⟨mE, cE, tE, fE, oE, kE⟩ := naf_loop env.hP hX hBa (cInB _ F4) (cIn4 _ F4 _ _ env.ls sGL env.sOL)
    (cIn4 _ F4 _ _ env.as sGA env.sOA) env.sOC env.sOL env.sOA sOB
    (fun j hj => by
      rw [W4 j hj]
      by_cases h8 : j < 2 * (3 + 1)
      · rw [ite_eq_left h8]
      · rw [ite_eq_right h8, w89 j (by omega)]) 256 0 0 (fun _ => 0) mM
    ⟨uM.pc, rfl, fun _ => rfl⟩ (fun x _ => by rw [uM.mem])
    (fun k hk => by
      rw [uM.mem, F4 _ (sOB.symm.subR (c := k) (l := 1) (by omega)), mem5',
        fillBytes_sep (sOB.symm.subR (c := k) (l := 1) (by omega)) (Nat.le_refl 40), mem3]
      unfold fillBytes; rw [add_sub_toNat out (by omega), ite_eq_left hk])
    (by decide) (by decide) (by decide)
    (by rw [uM.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [uM.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [uM.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [hzq4]; rfl)
    (by rw [uM.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [uM.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [f7k sp (by decide), r5sp, ev_add, hB])
    (by rw [uM.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [uM.regs]; simp +decide only [upd_app, ↓reduceIte])
    (by rw [kM _ (by decide), f7k _ (by decide), r518])
  -- the epilogue
  have hcE : CodeIn mE.mem P nonAdjacentFormCode := fun i hi => by
    rw [fE _ (env.sOC.subR (c := i) (l := 1) (by omega))]; exact cInB _ F4 i hi
  have spE : reg mE sp = G := by rw [kE sp (by decide), kM sp (by decide), f7k sp (by decide), r5sp]
  have hpsp : ∀ p ∈ nafPs, p.1 ≠ sp := by decide
  obtain ⟨e1, ce1, ue1⟩ := St.block (restoreBlock nafPs) tE hcE nafRestore_end
    (restoreBlock_ok mE.mem G nafPs _ spE hpsp fun q hq => by
      simp only [nafPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact aligned_add hGa (by decide))
  simp only [restoreBlock_run mE.mem G nafPs _ spE hpsp] at ue1
  obtain ⟨e2, de2, ue2⟩ := ue1.aluImm hcE naf_at_136 (off' := 0x138) (by decide)
  obtain ⟨e3, de3, pc3', mem3', regs3'⟩ := ue2.jalr hcE naf_at_138
  have slotW : ∀ r o, (r, o) ∈ nafPs → memLoad32 mE.mem (G + o) = reg m r := fun r o h => by
    have ho : 0x30 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x60 := by
      simp only [nafPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hslv r o h]
    apply memLoad32_congr; intro j hj
    have sb : Sep B 40 (G + BitVec.ofNat 32 (o.toNat + j)) 1 := by
      rw [← hB]; exact sep_offsets G (c := 8) (n := 40) (d := o.toNat + j) (k := 1) (.inl (by omega)) (by omega) (by omega)
    rw [← ofNat_toNat_self o, add_ofNat_assoc, fE _ (sOG.subR (c := o.toNat + j) (l := 1) (by omega)), F4 _ sb, mem5',
      fillBytes_sep sb (Nat.le_refl 40), mem3, fillBytes_sep (sOG.subR (c := o.toNat + j) (l := 1) (by omega))
        (Nat.le_refl 256)]
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs mE.mem G f ps q = f q := by
    intro f ps q h0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
  have hreg : ∀ r o, (r, o) ∈ nafPs → restoreRegs mE.mem G (reg mE) nafPs r = reg m r := fun r o hm => by
    simp only [nafPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact slotW _ _ (by decide)
  have rsp : restoreRegs mE.mem G (reg mE) nafPs sp = G := by rw [rr _ _ sp (by decide) (by decide)]; exact spE
  have keepM : ∀ q : Fin 32, q.val ∈ [3, 4, 27] → reg mE q = reg m q := fun q hq => by
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ : q.val ≠ 0 ∧ q ≠ sp ∧ q ≠ ra ∧
        q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ (8 : Fin 32) ∧ q ≠ (9 : Fin 32) ∧
        q ≠ (18 : Fin 32) := by
      revert hq; revert q; decide
    have g1 : q.val ∈ [2, 3, 4, 18, 20, 21, 22, 23, 27] := by revert hq; revert q; decide
    have g2 : q.val ∈ [1, 2, 3, 4, 18, 26, 27] := by revert hq; revert q; decide
    have g3 : q.val ∈ [1, 2, 3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert hq; revert q; decide
    rw [kE q g1, kM q g2, f7k q g3, k5 q h5 h6 h7 h8 h9, r5 q h2, kQ q h0 h3 h5 h4 h10,
      k3 q h5 h6 h7 h8 h9, r2' q h2, kP q h0 h11 h12 h5 h4, r2 q h1]
  have S : Steps m mE := .cons d1 (cs.trans (cP.trans (c2.trans (c3.trans (c4.trans (c5.trans (c5'.trans
    (.cons d6 (.cons d7 (l1.trans (l2.trans (l3.trans (l4.trans (cM.trans cE))))))))))))))
  refine ⟨e3, S.trans (ce1.trans (.cons de2 (.single de3))), ?_, ?_, fun q hq => ?_, fun k hk => ?_,
    fun x hx ho => ?_⟩
  · rw [pc3']; simp +decide only [upd_app, ↓reduceIte]; rw [hreg ra 0x5C (by decide), hra, add_lit_zero, hret]
  · rw [regs3']; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp, eGs]
  · rw [regs3']
    have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨
          q = (21 : Fin 32) ∨ q = (22 : Fin 32) ∨ q = (23 : Fin 32) ∨ q = (24 : Fin 32) ∨ q = (25 : Fin 32) ∨
          q = (26 : Fin 32) ∨ (q.val ∈ [3, 4, 27] ∧ q.val ≠ 0 ∧ q ≠ sp ∧ (∀ p ∈ nafPs, p.1 ≠ q)) := by decide
    rcases key q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨h1, h0, hs, hps⟩
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x5C (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x58 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x54 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x50 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x4C (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x48 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x44 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x40 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x3C (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x38 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x34 (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x30 (by decide)
    · rw [upd_ne h0 hs, rr _ _ q h0 hps]; exact keepM q h1
  · rw [mem3', oE k hk]; rfl
  · rw [mem3', fE x ho, F4 x (sepB x hx), fr5 x (sepB x hx) ho hx]

end C3.RV32
