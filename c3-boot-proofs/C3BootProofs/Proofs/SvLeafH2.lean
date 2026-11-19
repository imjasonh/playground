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

end C3.RV32.Sv
