import C3BootProofs.Proofs.SvLeafH1

/-!
# `sigstore::verify`: the hasher's copy and the digest buffers

From offset 0xBD4, `verify_leaf` copies the hasher to offset 0xA20 of the
frame and zeroes the 48- and 64-byte buffers at offsets 0x1480 and 0x1020.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

theorem sv_hi (B : Word) (c : Nat) : BitVec.ofNat 32 c + (B + 0x21A0) = B + 0x21A0 + BitVec.ofNat 32 c :=
  BitVec.add_comm _ _

theorem sv_7ff (B : Word) (k : Nat) :
    B + 0x21A0 + 0x7FF + BitVec.ofNat 32 k = B + 0x21A0 + BitVec.ofNat 32 (0x7FF + k) := by
  rw [show (0x7FF : Word) = BitVec.ofNat 32 0x7FF from rfl, add_ofNat_assoc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0xBD4 to 0xC26: the hasher copied to offset 0xA20, `s9`,
`s7`, and `s1` at the copy, its state, and the 64-byte buffer. -/
theorem sv_lh2 {B : Word} {msg : Bytes} {n : Machine} (F : Fr B 0x3830) (E : SvCode n.mem) (SC : SvShaCode n.mem)
    (KS : SvKSep B) (s : St n.mem SV n 0xBD4 (reg n)) (rsp : reg n sp = B + 0x21A0)
    (H : SvHasher B n.mem 0x420 msg) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' 0xC26 (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 18, 19, 20, 21, 22, 24, 26, 27] → reg n' q = reg n q) ∧
      reg n' 25 = B + 0x21A0 + BitVec.ofNat 32 0xA20 ∧ reg n' 23 = B + 0x21A0 + BitVec.ofNat 32 0xAA0 ∧
      reg n' 9 = B + 0x21A0 + BitVec.ofNat 32 0x1020 ∧
      SvKeepL B n.mem n'.mem [(0xA20, 0xD0), (0x1480, 0x30), (0x1020, 0x40)] ∧ SvHasher B n'.mem 0xA20 msg ∧
      (∀ x, SvR B x → n'.mem x = n.mem x) := by
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0xBEC) [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221,
    .aluImm .add a1 sp 0x420, .aluImm .add a2 x0 0xD0, .aluImm .add 25 sp 0x7FF, .aluImm .add 25 25 0x221] E.self
    (by decide) ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n.mem := u1.mem
  have s1 : St n1.mem SV n1 0xBEC (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 26, 27] → reg n1 q = reg n q :=
    fun q hq => by rw [u1.regs, runBlock_reg _ _ _ q s.zero (by revert hq; revert q; decide)]
  have v25 : reg n1 25 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [rsp]; exact sv_7ff B 0x221
  have E1 : SvCode n1.mem := by rw [m1]; exact E
  obtain ⟨n2, P2, K2, cp2⟩ := sv_mc (c := 0xA20) (d := 0x420) (N := 0xD0) F E1 s1 sv_at_bec sv_at_bf0 (by decide)
    (by decide) (by rw [k1 sp (by decide), rsp])
    (by rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [rsp]; exact sv_7ff B 0x221)
    (by rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]) (by decide) (by decide) (by decide)
  have E2 : SvCode n2.mem := E1.fr F P2.fr
  have rg2 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n2 q = reg n1 q :=
    fun q hq => P2.regs q (by revert hq; revert q; decide)
  have sp2 : reg n2 sp = B + 0x21A0 := by rw [rg2 sp (by decide), k1 sp (by decide), rsp]
  obtain ⟨n3, c3, u3⟩ := P2.st.block (off' := 0xBFC) [.lui a0 0x1000, .aluImm .add a0 a0 0x480, .alu .add a0 a0 sp]
    E2.self (by decide) ⟨trivial, trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem SV n3 0xBFC (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have k3 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n3 q = reg n2 q :=
    fun q hq => by rw [u3.regs, runBlock_reg _ _ _ q P2.st.zero (by revert hq; revert q; decide)]
  have E3 : SvCode n3.mem := by rw [m3]; exact E2
  have SC3 : SvShaCode n3.mem := SC.sv F KS fun x hx => by rw [m3, P2.fr x hx, m1]
  obtain ⟨n4, c4, s4, sp4, rk4, K4, z4, f4⟩ := sv_zaF (c := 0x1480) (N := 48) F E3 SC3 s3 sv_at_bfc sv_at_c00
    (by decide) (by rw [k3 sp (by decide), sp2])
    (by rw [u3.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [sp2]; exact sv_hi B 0x1480)
    (Or.inl ⟨by decide, rfl⟩) (by decide)
  have E4 : SvCode n4.mem := E3.fr F f4
  obtain ⟨n5, c5, u5⟩ := s4.block (off' := 0xC1E) [.aluImm .add 23 sp 0x7FF, .aluImm .add 23 23 0x2A1,
    .lui a0 0x1000, .aluImm .add a0 a0 0x20, .alu .add a0 a0 sp, .lui a1 0x1000, .aluImm .add a1 a1 0x20,
    .alu .add 9 sp a1] E4.self (by decide) ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0xC1E (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have k5 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 18, 19, 20, 21, 22, 24, 25, 26, 27] → reg n5 q = reg n4 q :=
    fun q hq => by rw [u5.regs, runBlock_reg _ _ _ q s4.zero (by revert hq; revert q; decide)]
  have v5_23 : reg n5 23 = B + 0x21A0 + BitVec.ofNat 32 0xAA0 := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [sp4]; exact sv_7ff B 0x2A1
  have v5_9 : reg n5 9 = B + 0x21A0 + BitVec.ofNat 32 0x1020 := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [sp4]; rfl
  have E5 : SvCode n5.mem := by rw [m5]; exact E4
  have SC5 : SvShaCode n5.mem := SC.sv F KS fun x hx => by rw [m5, f4 x hx, m3, P2.fr x hx, m1]
  obtain ⟨n6, c6, s6, sp6, rk6, K6, z6, f6⟩ := sv_zaF (c := 0x1020) (N := 64) F E5 SC5 s5 sv_at_c1e sv_at_c22
    (by decide) (by rw [k5 sp (by decide), sp4])
    (by rw [u5.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [sp4]; exact sv_hi B 0x1020)
    (Or.inr ⟨by decide, rfl⟩) (by decide)
  refine ⟨n6, c1.trans (P2.steps.trans (c3.trans (c4.trans (c5.trans c6)))), s6, sp6, fun q hq => ?_, ?_, ?_, ?_,
    fun e he hL => ?_, ?_, fun x hx => by rw [f6 x hx, m5, f4 x hx, m3, P2.fr x hx, m1]⟩
  · rw [rk6 q (by revert hq; revert q; decide), k5 q (by revert hq; revert q; decide),
      rk4 q (by revert hq; revert q; decide), k3 q (by revert hq; revert q; decide),
      rg2 q (by revert hq; revert q; decide), k1 q (by revert hq; revert q; decide)]
  · rw [rk6 25 (by decide), k5 25 (by decide), rk4 25 (by decide), k3 25 (by decide), rg2 25 (by decide), v25]
  · rw [rk6 23 (by decide), v5_23]
  · rw [rk6 9 (by decide), v5_9]
  · have h1 := hL _ (List.mem_cons_self ..)
    have h2 := hL _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have h3 := hL _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    simp only at h1 h2 h3
    rw [K6 e he (fun q hq => by rw [List.mem_singleton] at hq; subst hq; simp only; omega), m5,
      K4 e he (fun q hq => by rw [List.mem_singleton] at hq; subst hq; simp only; omega), m3, K2 e he (by omega), m1]
  · refine H.copy fun j hj => ?_
    rw [K6 _ (by omega) (fun q hq => by rw [List.mem_singleton] at hq; subst hq; simp only; omega), m5,
      K4 _ (by omega) (fun q hq => by rw [List.mem_singleton] at hq; subst hq; simp only; omega), m3, cp2 j hj, m1]

theorem sv_o (B : Word) (c k : Nat) :
    B + 0x21A0 + BitVec.ofNat 32 c + BitVec.ofNat 32 k = B + 0x21A0 + BitVec.ofNat 32 (c + k) :=
  add_ofNat_assoc _ _ _

theorem lenLo5_eq' (lo pos : Word) (hp : ∀ k, 7 ≤ k → pos.getLsbD k = false) :
    ((((pos <<< 3) ||| (lo <<< 10)) &&& 0xFF00) <<< 8) |||
      ((((lo <<< 2) &&& 0xFF00) ||| ((lo <<< 10) >>> 24)) ||| (pos <<< 27)) = bswap32 ((lo <<< 10) ||| (pos <<< 3)) := by
  rw [BitVec.or_comm]; exact lenLo5_eq lo pos hp

theorem lenHi5_eq' (lo : Word) :
    (((((0 : Word) <<< 10) ||| (lo >>> 22)) &&& 0xFF00) <<< 8) |||
      ((lo >>> 22) <<< 24 ||| ((((0 : Word) <<< 2) &&& 0xFF00) ||| (((0 : Word) <<< 10) >>> 24))) =
      bswap32 (lo >>> 22) := by
  rw [BitVec.or_comm]; exact lenHi5_eq lo

def svLenA : List BInstr :=
  [.lw 24 27 0xC8, .lw a2 27 0xC4, .lw 17 27 0xCC, .lw a4 27 0xC0, .lbu 20 27 0x7F, .aluImm .srl a6 24 0x16,
   .aluImm .sll 5 17 0xA, .aluImm .srl 6 a2 0x16, .aluImm .sll 7 24 0xA, .aluImm .srl 31 a4 0x16,
   .aluImm .sll a3 a2 0xA, .alu .or 28 5 a6, .alu .or 29 7 6, .alu .or 30 a3 31, .aluImm .sll a5 a4 0xA,
   .aluImm .sll a0 20 0x3, .alu .or a0 a0 a5, .lui 22 0x10000, .aluImm .sll a4 a4 0x2,
   .aluImm .add a1 22 0xFFFFFF00, .alu .and a4 a4 a1, .aluImm .srl a5 a5 0x18, .alu .or a4 a4 a5,
   .alu .and a0 a0 a1, .aluImm .sll a0 a0 0x8, .aluImm .sll a5 20 0x1B, .alu .or a4 a4 a5,
   .aluImm .sll a2 a2 0x2, .alu .and a2 a2 a1, .aluImm .srl a3 a3 0x18, .alu .or a0 a0 a4]

def svLenB : List BInstr :=
  [.alu .or a2 a2 a3, .alu .and a0 30 a1, .aluImm .sll 31 31 0x18, .aluImm .sll a0 a0 0x8, .alu .or a2 31 a2,
   .alu .or a0 a0 a2]

def svLenC : List BInstr :=
  [.aluImm .sll 24 24 0x2, .alu .and a0 24 a1, .aluImm .srl a2 7 0x18, .alu .or a0 a0 a2, .alu .and a2 29 a1,
   .aluImm .sll a2 a2 0x8, .aluImm .sll 6 6 0x18, .alu .or a0 6 a0, .aluImm .sll 17 17 0x2, .alu .and a3 17 a1,
   .aluImm .srl a4 5 0x18, .alu .or 8 a0 a2, .alu .or a3 a3 a4, .alu .and a0 28 a1, .aluImm .sll a6 a6 0x18,
   .aluImm .sll a0 a0 0x8, .alu .or a1 a6 a3, .alu .or 24 a1 a0]

set_option maxRecDepth 100000 in
theorem svLenA_end : blockEnd sigstoreVerifyCode 0xC26 svLenA = some 0xC88 := by decide
set_option maxRecDepth 100000 in
theorem svLenB_end : blockEnd sigstoreVerifyCode 0xC8A svLenB = some 0xC9A := by decide
set_option maxRecDepth 100000 in
theorem svLenC_end : blockEnd sigstoreVerifyCode 0xC9C svLenC = some 0xCD4 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0xC26 to 0xCD4: the buffer's byte count in `s4`, and the
message's length in bits, byte-swapped, in the frame words at 0x78 and
0x74 and in `s0` and `s8`. -/
theorem sv_lh3 {B : Word} {h : Bytes} {n : Machine} (F : Fr B 0x3830) (E : SvCode n.mem)
    (s : St n.mem SV n 0xC26 (reg n)) (rsp : reg n sp = B + 0x21A0)
    (h27 : reg n 27 = B + 0x21A0 + BitVec.ofNat 32 0xA20) (H : SvHasher B n.mem 0xA20 h) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' 0xCD4 (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 9, 18, 19, 21, 23, 25, 26, 27] → reg n' q = reg n q) ∧
      reg n' 20 = BitVec.ofNat 32 (h.length % 128) ∧ reg n' 8 = 0 ∧ reg n' 24 = 0 ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) =
        bswap32 ((BitVec.ofNat 32 (h.length / 128) <<< 10) ||| (BitVec.ofNat 32 (h.length % 128) <<< 3)) ∧
      memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = bswap32 (BitVec.ofNat 32 (h.length / 128) >>> 22) ∧
      SvKeepL B n.mem n'.mem [(0x74, 8)] ∧ (∀ x, SvR B x → n'.mem x = n.mem x) := by
  have al : ∀ k, k % 4 = 0 → k ≤ 0xCC → (reg n 27 + BitVec.ofNat 32 k).toNat % 4 = 0 := fun k hk hk' => by
    rw [h27, sv_o]; exact sv_al F (by omega) (by omega)
  obtain ⟨n1, c1, u1⟩ := s.block svLenA E.self svLenA_end (by
    simp +decide only [svLenA, BlockOk, BInstr.ok, BInstr.run, upd, ↓reduceIte, and_true]
    exact ⟨al 0xC8 (by decide) (by decide), al 0xC4 (by decide) (by decide), al 0xCC (by decide) (by decide),
      al 0xC0 (by decide) (by decide)⟩)
  have m1 : n1.mem = n.mem := u1.mem
  have s1 : St n1.mem SV n1 0xC88 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 21, 23, 25, 26, 27] → reg n1 q = reg n q :=
    fun q hq => by rw [u1.regs, runBlock_reg _ _ _ q s.zero (by revert hq; revert q; decide)]
  have ld : ∀ k, k ≤ 0xCC → reg n 27 + BitVec.ofNat 32 k = B + 0x21A0 + BitVec.ofNat 32 (0xA20 + k) :=
    fun k _ => by rw [h27, sv_o]
  have hlo : memLoad32 n.mem (reg n 27 + 0xC0) = BitVec.ofNat 32 (h.length / 128) := by
    rw [show (0xC0 : Word) = BitVec.ofNat 32 0xC0 from rfl, ld _ (by decide)]; exact H.lo
  have hhi : memLoad32 n.mem (reg n 27 + 0xC4) = 0 := by
    rw [show (0xC4 : Word) = BitVec.ofNat 32 0xC4 from rfl, ld _ (by decide)]; exact H.hi
  have hhi2 : memLoad32 n.mem (reg n 27 + 0xC8) = 0 := by
    rw [show (0xC8 : Word) = BitVec.ofNat 32 0xC8 from rfl, ld _ (by decide)]; exact H.hi2
  have hhi3 : memLoad32 n.mem (reg n 27 + 0xCC) = 0 := by
    rw [show (0xCC : Word) = BitVec.ofNat 32 0xCC from rfl, ld _ (by decide)]; exact H.hi3
  have hpos : n.mem (reg n 27 + 0x7F) = BitVec.ofNat 8 (h.length % 128) := by
    rw [show (0x7F : Word) = BitVec.ofNat 32 0x7F from rfl, ld _ (by decide)]; exact H.pos
  have hp : h.length % 128 < 128 := Nat.mod_lt _ (by decide)
  have hz : BitVec.zeroExtend 32 (BitVec.ofNat 8 (h.length % 128)) = BitVec.ofNat 32 (h.length % 128) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hpb : ∀ k, 7 ≤ k → (BitVec.ofNat 32 (h.length % 128)).getLsbD k = false := fun k hk =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by rw [BitVec.toNat_ofNat]; omega)
      (Nat.pow_le_pow_right (by decide) hk : 2 ^ 7 ≤ 2 ^ k))
  have vA : reg n1 a0 = bswap32 ((BitVec.ofNat 32 (h.length / 128) <<< 10) ||| (BitVec.ofNat 32 (h.length % 128) <<< 3)) := by
    rw [u1.regs]; simp +decide only [svLenA, runBlock, BInstr.run, upd, ↓reduceIte]
    rw [hlo, hpos, hz]
    exact lenLo5_eq' _ _ hpb
  have v20 : reg n1 20 = BitVec.ofNat 32 (h.length % 128) := by
    rw [u1.regs]; simp +decide only [svLenA, runBlock, BInstr.run, upd, ↓reduceIte]; rw [hpos, hz]
  have E1 : SvCode n1.mem := by rw [m1]; exact E
  have sp1 : reg n1 sp = B + 0x21A0 := by rw [k1 sp (by decide), rsp]
  obtain ⟨n2, d2, s2, fr2, K2, W2, rg2⟩ := sv_sw F E1 s1 sv_at_c88 (off' := 0xC8A) (c := 0x78) (by decide)
    (by rw [sp1]; rfl) (by decide) (by decide)
  have E2 : SvCode n2.mem := E1.fr F fr2
  obtain ⟨n3, c3, u3⟩ := s2.block svLenB E2.self svLenB_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem SV n3 0xC9A (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have k3 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 23, 24, 25, 26, 27] → reg n3 q = reg n2 q :=
    fun q hq => by rw [u3.regs, runBlock_reg _ _ _ q s2.zero (by revert hq; revert q; decide)]
  have vB : reg n3 a0 = bswap32 (BitVec.ofNat 32 (h.length / 128) >>> 22) := by
    rw [u3.regs]; simp +decide only [svLenB, runBlock, BInstr.run, upd, ↓reduceIte]
    simp only [rg2, u1.regs]
    simp +decide only [svLenA, runBlock, BInstr.run, upd, ↓reduceIte]
    rw [hlo, hhi]
    exact lenHi5_eq' _
  have E3 : SvCode n3.mem := by rw [m3]; exact E2
  obtain ⟨n4, d4, s4, fr4, K4, W4, rg4⟩ := sv_sw F E3 s3 sv_at_c9a (off' := 0xC9C) (c := 0x74) (by decide)
    (by rw [k3 sp (by decide), rg2, sp1]; rfl) (by decide) (by decide)
  have E4 : SvCode n4.mem := E3.fr F fr4
  obtain ⟨n5, c5, u5⟩ := s4.block svLenC E4.self svLenC_end
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0xCD4 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have k5 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 18, 19, 20, 21, 23, 25, 26, 27] → reg n5 q = reg n4 q :=
    fun q hq => by rw [u5.regs, runBlock_reg _ _ _ q s4.zero (by revert hq; revert q; decide)]
  have v8 : reg n5 8 = 0 := by
    rw [u5.regs]; simp +decide only [svLenC, runBlock, BInstr.run, upd, ↓reduceIte]
    simp only [rg4, u3.regs]
    simp +decide only [svLenB, runBlock, BInstr.run, upd, ↓reduceIte]
    simp only [rg2, u1.regs]
    simp +decide only [svLenA, runBlock, BInstr.run, upd, ↓reduceIte]
    rw [hhi2, hhi]; rfl
  have v24 : reg n5 24 = 0 := by
    rw [u5.regs]; simp +decide only [svLenC, runBlock, BInstr.run, upd, ↓reduceIte]
    simp only [rg4, u3.regs]
    simp +decide only [svLenB, runBlock, BInstr.run, upd, ↓reduceIte]
    simp only [rg2, u1.regs]
    simp +decide only [svLenA, runBlock, BInstr.run, upd, ↓reduceIte]
    rw [hhi3, hhi2]; rfl
  refine ⟨n5, c1.trans (d2.trans (c3.trans (d4.trans c5))), s5, by rw [k5 sp (by decide), rg4, k3 sp (by decide), rg2, sp1],
    fun q hq => ?_, ?_, v8, v24, ?_, ?_, fun e he hL => ?_, fun x hx => by rw [m5, fr4 x hx, m3, fr2 x hx, m1]⟩
  · rw [k5 q (by revert hq; revert q; decide), rg4, k3 q (by revert hq; revert q; decide), rg2,
      k1 q (by revert hq; revert q; decide)]
  · rw [k5 20 (by decide), rg4, k3 20 (by decide), rg2, v20]
  · rw [m5, K4.w32 (by decide) (Or.inr (by decide)), m3, W2, vA]
  · rw [m5, W4, vB]
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    rw [m5, K4 e he (by omega), m3, K2 e he (by omega), m1]

/-- A buffer of `pos` bytes `t`, then 0x80, then `m` zeros. -/
theorem mb_pad {M : Word → BitVec 8} {P : Word} {pos m : Nat} {t : Bytes} (ht : memBytes M P pos = t)
    (h80 : M (P + BitVec.ofNat 32 pos) = 0x80) (hz : ∀ i, i < m → M (P + BitVec.ofNat 32 (pos + 1 + i)) = 0) :
    memBytes M P (pos + 1 + m) = t ++ [0x80] ++ List.replicate m 0 := by
  have e1 : memBytes M (P + BitVec.ofNat 32 pos) 1 = [0x80] := by rw [memBytes_succ, h80]; rfl
  have e2 : memBytes M (P + BitVec.ofNat 32 (pos + 1)) m = List.replicate m 0 := by
    unfold memBytes
    rw [List.map_congr_left (g := fun _ => 0) fun i hi => by
      rw [List.mem_range] at hi; rw [add_ofNat_assoc, hz i hi]; rfl, List.map_const', List.length_range]
  rw [memBytes_split, memBytes_split, ht, e1, e2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0xCD4 to 0xD20: the buffer padded with 0x80 and zeros, and,
when fewer than 16 bytes are left for the length, compressed and cleared.
After it, storing the length in the buffer's last 16 bytes and compressing
gives the hash value of the padded message. -/
theorem sv_lh4 {B : Word} {h : Bytes} {n : Machine} (F : Fr B 0x3830) (E : SvCode n.mem) (SC : SvShaCode n.mem)
    (KS : SvKSep B) (s : St n.mem SV n 0xCD4 (reg n)) (rsp : reg n sp = B + 0x21A0)
    (h20 : reg n 20 = BitVec.ofNat 32 (h.length % 128)) (h25 : reg n 25 = B + 0x21A0 + BitVec.ofNat 32 0xA20)
    (h23 : reg n 23 = B + 0x21A0 + BitVec.ofNat 32 0xAA0) (H : SvHasher B n.mem 0xA20 h) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' 0xD20 (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      (fullBlocks5 h ++ Sha512.blocks ((padTail5 h).length / 128) (padTail5 h)).foldl Sha512.compress Sha512.h0384 =
        Sha512.compress (s5Hv n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0)).toList
          (memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 112 ++ Sha512.be128 (8 * h.length)) ∧
      SvKeepL B n.mem n'.mem [(0xA20, 0xC0)] ∧ (∀ x, SvR B x → n'.mem x = n.mem x) := by
  have hp : h.length % 128 < 128 := Nat.mod_lt _ (by decide)
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0xCE0) [.aluImm .xor 22 20 0x7F, .alu .add a0 25 20, .aluImm .add a1 x0 0x80]
    E.self (by decide) ⟨trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n.mem := u1.mem
  have s1 : St n1.mem SV n1 0xCE0 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 23, 24, 25, 26, 27] → reg n1 q = reg n q :=
    fun q hq => by rw [u1.regs, runBlock_reg _ _ _ q s.zero (by revert hq; revert q; decide)]
  have v22 : reg n1 22 = BitVec.ofNat 32 (127 - h.length % 128) := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [h20]
    show BitVec.ofNat 32 (h.length % 128) ^^^ 0x7F = _
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : h.length % 128 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : 127 - h.length % 128 < 2 ^ 32), show (0x7F : Word).toNat = 127 from rfl]
    exact xor127 _ hp
  have va0 : reg n1 a0 = B + 0x21A0 + BitVec.ofNat 32 (0xA20 + h.length % 128) := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [h25, h20]; exact sv_o B _ _
  have va1 : reg n1 a1 = 0x80 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
  have E1 : SvCode n1.mem := by rw [m1]; exact E
  -- 0xCE0: sb a1, 0(a0)
  obtain ⟨n2, d2, s2, fr2, K2, W2, rg2⟩ := sv_sb F E1 s1 sv_at_ce0 (off' := 0xCE4) (c := 0xA20 + h.length % 128)
    (by decide) (by rw [va0]; exact BitVec.add_zero _) (by omega)
  have E2 : SvCode n2.mem := E1.fr F fr2
  obtain ⟨n3, c3, u3⟩ := s2.block (off' := 0xCEA) [.aluImm .add a0 a0 0x1, .aluImm .add a1 x0 0x0, .alu .add a2 x0 22]
    E2.self (by decide) ⟨trivial, trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem SV n3 0xCEA (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have k3 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n3 q = reg n1 q :=
    fun q hq => by rw [u3.regs, runBlock_reg _ _ _ q s2.zero (by revert hq; revert q; decide), rg2]
  have E3 : SvCode n3.mem := by rw [m3]; exact E2
  obtain ⟨n4, c4, s4, M4, k4⟩ := sv_msF (c := 0xA20 + h.length % 128 + 1) (N := 127 - h.length % 128) (v := 0) F E3 s3
    sv_at_cea sv_at_cee (by decide) (by decide)
    (by rw [u3.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [rg2, va0]; exact sv_o B _ 1)
    (by rw [u3.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    (by rw [u3.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [rg2, v22]; exact BitVec.zero_add _)
    (by omega)
  have kk4 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg n1 q :=
    fun q hq => by
      rw [k4 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide), k3 q hq]
  have S0 : ∀ o : Nat, B + 0x21A0 + BitVec.ofNat 32 0xA20 + BitVec.ofNat 32 o = B + 0x21A0 + BitVec.ofNat 32 (0xA20 + o) :=
    fun o => sv_o B _ _
  have out4 : ∀ e, e < 0x1690 → (e < 0xA20 + h.length % 128 + 1 ∨ 0xAA0 ≤ e) →
      n4.mem (B + 0x21A0 + BitVec.ofNat 32 e) = n2.mem (B + 0x21A0 + BitVec.ofNat 32 e) := fun e he h1 => by
    rw [M4, fillBytes_sep (sepS (B + 0x21A0) (by omega) (by omega) (by omega)) (Nat.le_refl _), m3]
  have fr4 : ∀ x, SvR B x → n4.mem x = n.mem x := fun x hx => by
    rw [M4, fillBytes_sep (svR_hi hx (by omega)) (Nat.le_refl _), m3, fr2 x hx, m1]
  have hb : ∀ m, m ≤ 127 - h.length % 128 → memBytes n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) (h.length % 128 + 1 + m) =
      tailBytes5 h ++ [0x80] ++ List.replicate m 0 := fun m hm => by
    refine mb_pad ?_ ?_ fun i hi => ?_
    · rw [← H.buf]
      exact memBytes_congr fun i hi => by
        rw [S0, out4 _ (by omega) (Or.inl (by omega)), K2 _ (by omega) (Or.inl (by omega)), m1]
    · rw [S0, out4 _ (by omega) (Or.inl (by omega)), W2, va1]; rfl
    · rw [S0, M4, show 0xA20 + (h.length % 128 + 1 + i) = 0xA20 + h.length % 128 + 1 + i by omega,
        ← sv_o B (0xA20 + h.length % 128 + 1) i, fill_at (by omega) (by omega)]
      rfl
  have hs : s5Hv n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = s5Hv n.mem (B + 0x21A0 + BitVec.ofNat 32 (0xA20 + 0x80)) :=
    s5Hv_congr fun i hi => by
      rw [sv_o, out4 _ (by omega) (Or.inr (by omega)), K2 _ (by omega) (Or.inr (by omega)), m1]
  have hash0 := H.hash
  rw [← hs] at hash0
  have KL4 : SvKeepL B n.mem n4.mem [(0xA20, 0x80)] := fun e he hL => by
    have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    rw [out4 e (by omega) (by omega), K2 e he (by omega), m1]
  obtain ⟨n5, c5, u5⟩ := s4.block (off' := 0xCF4) [.aluImm .add a0 x0 0xF] (E3.fr F fun x hx => by
      rw [fr4 x hx, ← m1, ← fr2 x hx, ← m3]).self (by decide) ⟨trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0xCF4 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have E5 : SvCode n5.mem := E.fr F fun x hx => by rw [m5, fr4 x hx]
  have k5 : ∀ q : Fin 32, q ≠ a0 → reg n5 q = reg n4 q := fun q hq => by
    rw [u5.regs]; simp only [runBlock, BInstr.run]; exact upd_ne' hq s4.zero
  have v15 : reg n5 a0 = 0xF := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [s4.zero]; rfl
  have hbr : branchTaken .bltu (reg n5 a0) (reg n5 22) = decide (h.length % 128 < 112) := by
    rw [v15, k5 22 (by decide), kk4 22 (by decide), v22]
    show decide ((15 : Word).toNat < (BitVec.ofNat 32 (127 - h.length % 128)).toNat) = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 127 - h.length % 128 < 2 ^ 32)]
    exact decide_eq_decide.mpr (show 15 < 127 - h.length % 128 ↔ h.length % 128 < 112 from ⟨by omega, by omega⟩)
  have kk5 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 23, 24, 25, 26, 27] → reg n5 q = reg n q := fun q hq => by
    rw [k5 q (by revert hq; revert q; decide), kk4 q (by revert hq; revert q; decide), k1 q hq]
  have fr5 : ∀ x, SvR B x → n5.mem x = n.mem x := fun x hx => by rw [m5, fr4 x hx]
  have KL5 : SvKeepL B n.mem n5.mem [(0xA20, 0xC0)] := by
    rw [m5]
    exact KL4.wider fun q hq => ⟨(0xA20, 0xC0), List.mem_singleton_self _, by
      rw [List.mem_singleton] at hq; subst hq; decide⟩
  by_cases hlt : h.length % 128 < 112
  · obtain ⟨n6, d6, u6⟩ := s5.taken E5.self 0xD20 sv_at_cf4 (by decide) (by rw [hbr]; exact decide_eq_true hlt)
    have s6 : St n6.mem SV n6 0xD20 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
    have m6 : n6.mem = n5.mem := u6.mem
    have e112 := hb (111 - h.length % 128) (by omega)
    rw [show h.length % 128 + 1 + (111 - h.length % 128) = 112 by omega] at e112
    refine ⟨n6, c1.trans (d2.trans (c3.trans (c4.trans (c5.trans (Steps.single d6))))), s6,
      by rw [u6.regs, kk5 sp (by decide), rsp], fun q hq => by rw [u6.regs, kk5 q (by revert hq; revert q; decide)],
      ?_, by rw [m6]; exact KL5, fun x hx => by rw [m6, fr5 x hx]⟩
    rw [m6, m5, padTail5_short h hlt, List.foldl_append, ← hash0, e112]
    unfold padTail5 padZeros5
    rw [show (239 - h.length % 128) % 128 = 111 - h.length % 128 by omega]
    rfl
  · obtain ⟨n6, d6, u6⟩ := s5.notTaken E5.self 0xCF8 sv_at_cf4 (by decide) (by rw [hbr]; exact decide_eq_false hlt)
    have s6 : St n6.mem SV n6 0xCF8 (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
    have m6 : n6.mem = n5.mem := u6.mem
    have E6 : SvCode n6.mem := by rw [m6]; exact E5
    obtain ⟨n7, c7, u7⟩ := s6.block (off' := 0xD02) [.aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x221,
      .alu .add a0 x0 23] E6.self (by decide) ⟨trivial, trivial, trivial, trivial⟩
    have m7 : n7.mem = n6.mem := u7.mem
    have s7 : St n7.mem SV n7 0xD02 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
    have k7 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 23, 24, 25, 26, 27] → reg n7 q = reg n q :=
      fun q hq => by rw [u7.regs, runBlock_reg _ _ _ q s6.zero (by revert hq; revert q; decide), u6.regs, kk5 q hq]
    have E7 : SvCode n7.mem := by rw [m7]; exact E6
    have SC7 : SvShaCode n7.mem := SC.sv F KS fun x hx => by rw [m7, m6, fr5 x hx]
    obtain ⟨n8, c8, s8, sp8, rk8, K8, hv8, f8⟩ := sv_fbF (a := 0xAA0) (b := 0xA20) F E7 SC7 KS s7 sv_at_d02 sv_at_d06
      (by decide) (by decide) (by rw [k7 sp (by decide), rsp])
      (by rw [u7.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [u6.regs, kk5 23 (by decide), h23]
          exact BitVec.zero_add _)
      (by rw [u7.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [u6.regs, kk5 sp (by decide), rsp]
          exact sv_7ff B 0x221)
      (by decide) (by decide) (by decide)
    have E8 : SvCode n8.mem := E7.fr F f8
    obtain ⟨n9, c9, u9⟩ := s8.block (off' := 0xD18) [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x221,
      .aluImm .add a2 x0 0x70, .aluImm .add a1 x0 0x0] E8.self (by decide) ⟨trivial, trivial, trivial, trivial, trivial⟩
    have m9 : n9.mem = n8.mem := u9.mem
    have s9 : St n9.mem SV n9 0xD18 (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
    have E9 : SvCode n9.mem := by rw [m9]; exact E8
    obtain ⟨n10, c10, s10, M10, k10⟩ := sv_msF (c := 0xA20) (N := 0x70) (v := 0) F E9 s9 sv_at_d18 sv_at_d1c
      (by decide) (by decide)
      (by rw [u9.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [sp8]; exact sv_7ff B 0x221)
      (by rw [u9.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
      (by rw [u9.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]) (by decide)
    have kr : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 23, 24, 25, 26, 27] → reg n10 q = reg n q := fun q hq => by
      rw [k10 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide), u9.regs, runBlock_reg _ _ _ q s8.zero (by revert hq; revert q; decide),
        rk8 q (by revert hq; revert q; decide), k7 q (by revert hq; revert q; decide)]
    have out10 : ∀ e, e < 0x1690 → (e < 0xA20 ∨ 0xA90 ≤ e) →
        n10.mem (B + 0x21A0 + BitVec.ofNat 32 e) = n8.mem (B + 0x21A0 + BitVec.ofNat 32 e) := fun e he h1 => by
      rw [M10, fillBytes_sep (sepS (B + 0x21A0) (by omega) (by omega) (by omega)) (Nat.le_refl _), m9]
    have e128 := hb (127 - h.length % 128) (by omega)
    rw [show h.length % 128 + 1 + (127 - h.length % 128) = 128 by omega] at e128
    refine ⟨n10, c1.trans (d2.trans (c3.trans (c4.trans (c5.trans ((Steps.single d6).trans (c7.trans (c8.trans
      (c9.trans c10)))))))), s10, ?_, kr, ?_, fun e he hL => ?_, fun x hx => ?_⟩
    · rw [k10 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u9.regs,
        runBlock_reg _ _ _ sp s8.zero (by decide), sp8]
    · have hR1 : s5Hv n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = s5Hv n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) :=
        s5Hv_congr fun i hi => by rw [sv_o]; exact out10 (0xAA0 + i) (by omega) (Or.inr (by omega))
      have hR2 : memBytes n10.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 112 = List.replicate 112 0 := by
        rw [M10, fill_memBytes _ _ _ (Nat.le_refl 112) (by decide)]; rfl
      have hv8' : (s5Hv n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0)).toList =
          Sha512.compress (s5Hv n4.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0)).toList
            (tailBytes5 h ++ [0x80] ++ List.replicate (127 - h.length % 128) 0) := by
        rw [hv8, m7, m6, m5, e128]
      rw [padTail5_long h (by omega), List.foldl_append, ← hash0, hR1, hR2, hv8']
      simp only [List.foldl_cons, List.foldl_nil]
    · have h1 := hL _ (List.mem_singleton_self _)
      simp only at h1
      rw [out10 e he (by omega), K8 e he (fun q hq => by rw [List.mem_singleton] at hq; subst hq; simp only; omega),
        m7, m6, KL5 e he hL]
    · rw [M10, fillBytes_sep (svR_hi hx (by decide)) (Nat.le_refl _), m9, f8 x hx, m7, m6, fr5 x hx]

end C3.RV32.Sv
