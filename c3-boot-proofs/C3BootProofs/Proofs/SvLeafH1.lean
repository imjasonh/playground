import C3BootProofs.Proofs.SvLeafH

/-!
# `sigstore::verify`: absorbing the `tbsCertificate`

From offset 0xB56, `verify_leaf` builds a SHA-384 hasher at offset 0x420 of
the frame: SHA-384's initial value, the `tbsCertificate`'s full blocks through
`sha384UpdateBlocks`, and the bytes after them copied into the buffer.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

theorem and_ff80 (x : Nat) (hx : x < 2 ^ 31) : x &&& 0x7FFFFF80 = 2 ^ 7 * (x / 2 ^ 7) :=
  Nat.eq_of_testBit_eq fun i => by
    rw [Nat.testBit_and, show (0x7FFFFF80 : Nat) = 2 ^ 7 * (2 ^ 24 - 1) from rfl, Nat.testBit_two_pow_mul,
      Nat.testBit_two_pow_mul, tb_pow_sub_one, Nat.testBit_div_two_pow]
    by_cases h7 : 7 ≤ i
    · rw [Nat.sub_add_cancel h7]
      by_cases h31 : i < 31
      · simp [h7, show i - 7 < 24 by omega]
      · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
        simp
    · simp [h7]

theorem w_ff80 (len : Nat) (h : len < 2 ^ 31) :
    BitVec.ofNat 32 0x7FFFFF80 &&& BitVec.ofNat 32 len = BitVec.ofNat 32 (128 * (len / 128)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len < 2 ^ 32),
    show 0x7FFFFF80 % 2 ^ 32 = 0x7FFFFF80 from rfl, Nat.and_comm, and_ff80 _ h, Nat.mod_eq_of_lt (by omega)]

theorem w_7f (len : Nat) :
    BitVec.ofNat 32 len &&& 0x7F = BitVec.ofNat 32 (len % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [and_mask_word (j := 7) rfl, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide),
    Nat.mod_eq_of_lt (by omega : len % 128 < 2 ^ 32)]

theorem ext8_ofNat (x : Nat) : (BitVec.ofNat 32 x).extractLsb' 0 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  rw [byte_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.pow_zero, Nat.div_one,
    Nat.mod_mod_of_dvd _ (by decide)]

theorem srl7_ofNat (len : Nat) (h : len < 2 ^ 32) :
    aluEval .srl (BitVec.ofNat 32 len) 0x7 = BitVec.ofNat 32 (len / 128) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 len >>> ((0x7 : Word).toNat % 32)).toNat = _
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    show (0x7 : Word).toNat % 32 = 7 from rfl, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem sv_cnt (B : Word) : B + 0x21A0 + BitVec.ofNat 32 0x4A0 + 0x40 = B + 0x21A0 + BitVec.ofNat 32 0x4E0 := by
  rw [show (0x40 : Word) = BitVec.ofNat 32 0x40 from rfl, add_ofNat_assoc]


theorem SvIn.r {B p : Word} {len : Nat} (h : SvIn B p len) {i : Nat} (hi : i < len) : SvR B (p + BitVec.ofNat 32 i) :=
  (h.sep.sub (c := i) (l := 1) (by omega)).symm


theorem sv_cntk (B : Word) (k : Nat) :
    B + 0x21A0 + BitVec.ofNat 32 0x4A0 + BitVec.ofNat 32 k = B + 0x21A0 + BitVec.ofNat 32 (0x4A0 + k) :=
  add_ofNat_assoc _ _ _

theorem blockList128_zero (M : Word → BitVec 8) (p : Word) : blockList128 M p 0 = [] := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0xB56 to 0xBD4: the hasher at offset 0x420 has absorbed the
`len` bytes at `p`, whose length is the word at offset 0x8C. -/
theorem sv_lh1 {B p : Word} {len : Nat} {n : Machine} (F : Fr B 0x3830) (E : SvCode n.mem) (SC : SvShaCode n.mem)
    (KS : SvKSep B) (s : St n.mem SV n 0xB56 (reg n)) (rsp : reg n sp = B + 0x21A0) (h9 : reg n 9 = p)
    (hl : memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 0x8C) = BitVec.ofNat 32 len) (hin : SvIn B p len) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' 0xBD4 (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 21, 22, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B n.mem n'.mem [(0x420, 0xD0)] ∧ SvHasher B n'.mem 0x420 (memBytes n.mem p len) ∧
      (∀ x, SvR B x → n'.mem x = n.mem x) := by
  have hlen : p.toNat + len + 14 ≤ 0x40000000 := hin.lo
  -- 0xB56: lw s0, 0x8C(sp)
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0xB58) [.lw 8 sp 0x8C] E.self (by decide)
    ⟨show (reg n sp + 0x8C).toNat % 4 = 0 by rw [rsp]; exact sv_al F (c := 0x8C) (by decide) (by decide), trivial⟩
  have m1 : n1.mem = n.mem := u1.mem
  have s1 : St n1.mem SV n1 0xB58 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ q : Fin 32, q ≠ 8 → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs]; simp only [runBlock, BInstr.run]; exact upd_ne' hq s.zero
  have v1 : reg n1 8 = BitVec.ofNat 32 len := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [rsp]; exact hl
  have E1 : SvCode n1.mem := by rw [m1]; exact E
  -- 0xB58: sb zero, 0x49F(sp)
  obtain ⟨n2, d2, s2, fr2, K2, W2, rg2⟩ := sv_sb F E1 s1 sv_at_b58 (off' := 0xB5C) (c := 0x49F) (by decide)
    (by rw [k1 sp (by decide), rsp]; rfl) (by decide)
  have E2 : SvCode n2.mem := E1.fr F fr2
  -- 0xB5C: the memcpy's arguments
  obtain ⟨n3, c3, u3⟩ := s2.block (off' := 0xB6E) [.aluImm .add 20 sp 0x4A0, .lui a1 0x3FCC4000, .aluImm .add a1 a1 0x5C0,
    .aluImm .add a2 x0 0x40, .alu .add a0 x0 20] E2.self (by decide) ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem SV n3 0xB6E (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have sp2 : reg n2 sp = B + 0x21A0 := by rw [rg2, k1 sp (by decide), rsp]
  have k3 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 21, 22, 23, 24, 25, 26, 27] → reg n3 q = reg n2 q := fun q hq => by
    rw [u3.regs, runBlock_reg _ _ _ q s2.zero (by revert hq; revert q; decide)]
  have v3a0 : reg n3 a0 = B + 0x21A0 + BitVec.ofNat 32 0x4A0 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [sp2]; exact BitVec.zero_add _
  have v3a1 : reg n3 a1 = IV5 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
  have v3a2 : reg n3 a2 = BitVec.ofNat 32 64 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
  have v320 : reg n3 20 = B + 0x21A0 + BitVec.ofNat 32 0x4A0 := by
    rw [u3.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [sp2]; rfl
  have E3 : SvCode n3.mem := by rw [m3]; exact E2
  -- 0xB6E: memcpy(sp + 0x4A0, IV, 64)
  obtain ⟨n4, P4, K4, cp4⟩ := sv_mcIn (c := 0x4A0) (N := 64) F E3 s3 sv_at_b6e sv_at_b72 (by decide) (by decide)
    (by rw [k3 sp (by decide), sp2]) v3a0 v3a1 v3a2 (by decide) (sv_ivIn F)
  have E4 : SvCode n4.mem := E3.fr F P4.fr
  have fr4 : ∀ x, SvR B x → n4.mem x = n.mem x := fun x hx => by
    rw [P4.fr x hx, m3, fr2 x hx, m1]
  have SC3 : SvShaCode n3.mem := SC.sv F KS fun x hx => by rw [m3, fr2 x hx, m1]
  have hv4 : (s5Hv n4.mem (B + 0x21A0 + BitVec.ofNat 32 0x4A0)).toList = Sha512.h0384 := iv_hv fun j hj => by
    rw [add_ofNat_assoc, cp4 j hj]; exact SC3.iv j hj
  have s4 := P4.st
  have rg4 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg n3 q :=
    fun q hq => P4.regs q (by revert hq; revert q; decide)
  have sp4 : reg n4 sp = B + 0x21A0 := by rw [rg4 sp (by decide), k3 sp (by decide), sp2]
  -- 0xB76: srli a2, s0, 7; addi a0, sp, 0x480
  obtain ⟨n5, c5, u5⟩ := s4.block (off' := 0xB7E) [.aluImm .srl a2 8 0x7, .aluImm .add a0 sp 0x480] E4.self
    (by decide) ⟨trivial, trivial, trivial⟩
  have m5 : n5.mem = n4.mem := u5.mem
  have s5 : St n5.mem SV n5 0xB7E (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have k5 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n5 q = reg n4 q :=
    fun q hq => by rw [u5.regs, runBlock_reg _ _ _ q s4.zero (by revert hq; revert q; decide)]
  have v8_4 : reg n4 8 = BitVec.ofNat 32 len := by
    rw [rg4 8 (by decide), k3 8 (by decide), rg2, v1]
  have hlen32 : len < 2 ^ 32 := by omega
  have v5a2 : reg n5 a2 = BitVec.ofNat 32 (len / 128) := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [v8_4]; exact srl7_ofNat len hlen32
  have v5a0 : reg n5 a0 = B + 0x21A0 + BitVec.ofNat 32 0x480 := by
    rw [u5.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [sp4]; rfl
  have E5 : SvCode n5.mem := by rw [m5]; exact E4
  -- 0xB7E: sw zero, 0x60(a0)
  obtain ⟨n6, d6, s6, fr6, K6, W6, rg6⟩ := sv_sw F E5 s5 sv_at_b7e (off' := 0xB82) (c := 0x4E0) (by decide)
    (by rw [v5a0, show (0x60 : Word) = BitVec.ofNat 32 0x60 from rfl, add_ofNat_assoc]) (by decide) (by decide)
  have E6 : SvCode n6.mem := E5.fr F fr6
  -- 0xB82: li a1, 0
  obtain ⟨n7, c7, u7⟩ := s6.block (off' := 0xB84) [.aluImm .add a1 x0 0x0] E6.self (by decide) ⟨trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have s7 : St n7.mem SV n7 0xB84 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have k7 : ∀ q : Fin 32, q ≠ a1 → reg n7 q = reg n6 q := fun q hq => by
    rw [u7.regs]; simp only [runBlock, BInstr.run]; exact upd_ne' hq s6.zero
  have v7a1 : reg n7 a1 = 0 := by
    rw [u7.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [s6.zero]; rfl
  have v7a0 : reg n7 a0 = B + 0x21A0 + BitVec.ofNat 32 0x480 := by rw [k7 _ (by decide), rg6, v5a0]
  have E7 : SvCode n7.mem := by rw [m7]; exact E6
  -- 0xB84 .. 0xB88: sw a1, 0x64/0x68/0x6C(a0)
  obtain ⟨n8, d8, s8, fr8, K8, W8, rg8⟩ := sv_sw F E7 s7 sv_at_b84 (off' := 0xB86) (c := 0x4E4) (by decide)
    (by rw [v7a0, show (0x64 : Word) = BitVec.ofNat 32 0x64 from rfl, add_ofNat_assoc]) (by decide) (by decide)
  have E8 : SvCode n8.mem := E7.fr F fr8
  obtain ⟨n9, d9, s9, fr9, K9, W9, rg9⟩ := sv_sw F E8 s8 sv_at_b86 (off' := 0xB88) (c := 0x4E8) (by decide)
    (by rw [rg8, v7a0, show (0x68 : Word) = BitVec.ofNat 32 0x68 from rfl, add_ofNat_assoc]) (by decide) (by decide)
  have E9 : SvCode n9.mem := E8.fr F fr9
  obtain ⟨n10, d10, s10, fr10, K10, W10, rg10⟩ := sv_sw F E9 s9 sv_at_b88 (off' := 0xB8A) (c := 0x4EC) (by decide)
    (by rw [rg9, rg8, v7a0, show (0x6C : Word) = BitVec.ofNat 32 0x6C from rfl, add_ofNat_assoc]) (by decide) (by decide)
  have E10 : SvCode n10.mem := E9.fr F fr10
  have kr10 : ∀ q : Fin 32, q ≠ a1 → reg n10 q = reg n5 q := fun q hq => by
    rw [rg10, rg9, rg8, k7 q hq, rg6]
  have c0 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4E0) = 0 := by
    rw [K10.w32 (by decide) (Or.inl (by decide)), K9.w32 (by decide) (Or.inl (by decide)),
      K8.w32 (by decide) (Or.inl (by decide)), m7, W6, s5.zero]
  have c1' : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4E4) = 0 := by
    rw [K10.w32 (by decide) (Or.inl (by decide)), K9.w32 (by decide) (Or.inl (by decide)), W8, v7a1]
  have c2 : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4E8) = 0 := by
    rw [K10.w32 (by decide) (Or.inl (by decide)), W9, rg8, v7a1]
  have c3' : memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4EC) = 0 := by
    rw [W10, rg9, rg8, v7a1]
  have hv10 : (s5Hv n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4A0)).toList = Sha512.h0384 := by
    rw [← hv4]
    congr 1
    refine s5Hv_congr fun i hi => ?_
    rw [add_ofNat_assoc, K10 _ (by omega) (Or.inl (by omega)), K9 _ (by omega) (Or.inl (by omega)),
      K8 _ (by omega) (Or.inl (by omega)), m7, K6 _ (by omega) (Or.inl (by omega)), m5]
  have fr10' : ∀ x, SvR B x → n10.mem x = n.mem x := fun x hx => by
    rw [fr10 x hx, fr9 x hx, fr8 x hx, m7, fr6 x hx, m5, fr4 x hx]
  have KL10 : SvKeepL B n.mem n10.mem [(0x49F, 0x51)] := fun e he hL => by
    have h := hL _ (List.mem_singleton_self _)
    simp only at h
    rw [K10 e he (by omega), K9 e he (by omega), K8 e he (by omega), m7, K6 e he (by omega), m5,
      K4 e he (by omega), m3, K2 e he (by omega), m1]
  have sp10 : reg n10 sp = B + 0x21A0 := by rw [kr10 sp (by decide), k5 sp (by decide), sp4]
  have v10_8 : reg n10 8 = BitVec.ofNat 32 len := by rw [kr10 8 (by decide), k5 8 (by decide), v8_4]
  have v10_9 : reg n10 9 = p := by
    rw [kr10 9 (by decide), k5 9 (by decide), rg4 9 (by decide), k3 9 (by decide), rg2, k1 9 (by decide), h9]
  have v10_20 : reg n10 20 = B + 0x21A0 + BitVec.ofNat 32 0x4A0 := by
    rw [kr10 20 (by decide), k5 20 (by decide), rg4 20 (by decide)]; exact v320
  have v10a2 : reg n10 a2 = BitVec.ofNat 32 (len / 128) := by rw [kr10 a2 (by decide), v5a2]
  have kk10 : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 21, 22, 24, 25, 26, 27] → reg n10 q = reg n q := fun q hq => by
    rw [kr10 q (by revert hq; revert q; decide), k5 q (by revert hq; revert q; decide),
      rg4 q (by revert hq; revert q; decide), k3 q (by revert hq; revert q; decide), rg2,
      k1 q (by revert hq; revert q; decide)]
  have inR : ∀ (M : Word → BitVec 8), (∀ x, SvR B x → M x = n.mem x) → ∀ i, i < len →
      M (p + BitVec.ofNat 32 i) = n.mem (p + BitVec.ofNat 32 i) := fun M hM i hi => hM _ (hin.r hi)
  by_cases hz : len / 128 = 0
  · -- 0xB8A: beq a2, zero: taken
    obtain ⟨n11, d11, u11⟩ := s10.taken E10.self 0xBC0 sv_at_b8a (by decide)
      (by rw [v10a2, s10.zero, hz]; rfl)
    have s11 : St n11.mem SV n11 0xBC0 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have E11 : SvCode n11.mem := by rw [m11]; exact E10
    obtain ⟨n12, c12, u12⟩ := s11.block (off' := 0xBC8) [.aluImm .add a0 sp 0x420, .alu .add a1 x0 9, .alu .add a2 x0 8]
      E11.self (by decide) ⟨trivial, trivial, trivial, trivial⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have s12 : St n12.mem SV n12 0xBC8 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have k12 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n12 q = reg n10 q :=
      fun q hq => by rw [u12.regs, runBlock_reg _ _ _ q s11.zero (by revert hq; revert q; decide), u11.regs]
    have E12 : SvCode n12.mem := by rw [m12]; exact E11
    have hl128 : len < 128 := by omega
    obtain ⟨n13, P13, K13, cp13⟩ := sv_mcIn (c := 0x420) (N := len) F E12 s12 sv_at_bc8 sv_at_bcc (by decide)
      (by decide) (by rw [k12 sp (by decide), sp10])
      (by rw [u12.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [u11.regs, sp10]; rfl)
      (by rw [u12.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [u11.regs, v10_9]
          exact BitVec.zero_add _)
      (by rw [u12.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [u11.regs, v10_8]
          exact BitVec.zero_add _)
      (by omega) hin
    have E13 : SvCode n13.mem := E12.fr F P13.fr
    have rg13 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n13 q = reg n10 q :=
      fun q hq => by rw [P13.regs q (by revert hq; revert q; decide), k12 q hq]
    -- 0xBD0: sb s0, 0x49F(sp)
    obtain ⟨n14, d14, s14, fr14, K14, W14, rg14⟩ := sv_sb F E13 P13.st sv_at_bd0 (off' := 0xBD4) (c := 0x49F) (by decide)
      (by rw [rg13 sp (by decide), sp10]; rfl) (by decide)
    have fr14' : ∀ x, SvR B x → n14.mem x = n.mem x := fun x hx => by
      rw [fr14 x hx, P13.fr x hx, m12, m11, fr10' x hx]
    have hml : (memBytes n.mem p len).length = len := memBytes_length _ _ _
    have hS : ∀ j, j < 64 → n14.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4A0 + j)) =
        n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x4A0 + j)) := fun j hj => by
      rw [K14 _ (by omega) (Or.inr (by omega)), K13 _ (by omega) (Or.inr (by omega)), m12, m11]
    have hW : ∀ c, 0x4A0 ≤ c → c + 4 ≤ 0x4F0 → memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 c) =
        memLoad32 n10.mem (B + 0x21A0 + BitVec.ofNat 32 c) := fun c h1 h2 => by
      rw [K14.w32 (by omega) (Or.inr (by omega)), K13.w32 (by omega) (Or.inr (by omega)), m12, m11]
    have H : SvHasher B n14.mem 0x420 (memBytes n.mem p len) := by
      refine ⟨by rw [hml]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hml, Nat.mod_eq_of_lt hl128]
        show n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x49F) = _
        rw [W14, rg13 8 (by decide), v10_8, ext8_ofNat]
      · rw [hml, tailBytes5_mem, hz, Nat.mul_zero, add_ofNat_zero, Nat.mod_eq_of_lt hl128]
        unfold memBytes
        apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        rw [add_ofNat_assoc, K14 _ (by omega) (Or.inl (by omega)), cp13 i hi, m12, m11, inR n10.mem fr10' i hi]
      · rw [fullBlocks5_mem, hz, blockList128_zero, List.foldl_nil, ← hv10]
        exact congrArg _ (s5Hv_congr fun i hi => by rw [add_ofNat_assoc]; exact hS i hi)
      · rw [hml, hz]; show memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4E0) = _
        rw [hW _ (by decide) (by decide), c0]; rfl
      · show memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4E4) = _
        rw [hW _ (by decide) (by decide), c1']
      · show memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4E8) = _
        rw [hW _ (by decide) (by decide), c2]
      · show memLoad32 n14.mem (B + 0x21A0 + BitVec.ofNat 32 0x4EC) = _
        rw [hW _ (by decide) (by decide), c3']
    refine ⟨n14, c1.trans (d2.trans (c3.trans (P4.steps.trans (c5.trans (d6.trans (c7.trans (d8.trans (d9.trans
      (d10.trans ((Steps.single d11).trans (c12.trans (P13.steps.trans d14)))))))))))), s14,
      by rw [rg14, rg13 sp (by decide), sp10], fun q hq => ?_, fun e he hL => ?_, H, fr14'⟩
    · rw [rg14, rg13 q (by revert hq; revert q; decide), kk10 q hq]
    · have h := hL _ (List.mem_singleton_self _)
      simp only at h
      rw [K14 e he (by omega), K13 e he (by omega), m12, m11,
        KL10 e he fun q hq => by rw [List.mem_singleton] at hq; subst hq; simp only; omega]
  · -- 0xB8A: beq a2, zero: not taken
    obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.self 0xB8C sv_at_b8a (by decide)
      (by rw [v10a2, s10.zero]; exact br_beq_f fun h => hz ((ofNat_eq_zero_iff (by omega)).mp h))
    have s11 : St n11.mem SV n11 0xB8C (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
    have m11 : n11.mem = n10.mem := u11.mem
    have E11 : SvCode n11.mem := by rw [m11]; exact E10
    obtain ⟨n12, c12, u12⟩ := s11.block (off' := 0xBA2) [.lui a0 0x80000000, .aluImm .add a0 a0 0xFFFFFF80,
      .alu .and a0 a0 8, .aluImm .and 8 8 0x7F, .alu .add 23 9 a0, .alu .add a0 x0 20, .alu .add a1 x0 9]
      E11.self (by decide) ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
    have m12 : n12.mem = n11.mem := u12.mem
    have s12 : St n12.mem SV n12 0xBA2 (reg n12) := ⟨u12.pc, rfl, fun _ => rfl⟩
    have k12 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 12, 18, 19, 20, 21, 22, 24, 25, 26, 27] → reg n12 q = reg n10 q :=
      fun q hq => by rw [u12.regs, runBlock_reg _ _ _ q s11.zero (by revert hq; revert q; decide), u11.regs]
    have v12a0 : reg n12 a0 = B + 0x21A0 + BitVec.ofNat 32 0x4A0 := by
      rw [u12.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [u11.regs, v10_20]
      exact BitVec.zero_add _
    have v12a1 : reg n12 a1 = p := by
      rw [u12.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [u11.regs, v10_9]
      exact BitVec.zero_add _
    have v12_8 : reg n12 8 = BitVec.ofNat 32 (len % 128) := by
      rw [u12.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [u11.regs, v10_8]
      exact w_7f len
    have v12_23 : reg n12 23 = p + BitVec.ofNat 32 (128 * (len / 128)) := by
      rw [u12.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; simp only [u11.regs]; rw [v10_8, v10_9]
      show p + (BitVec.ofNat 32 0x7FFFFF80 &&& BitVec.ofNat 32 len) = _
      rw [w_ff80 len (by omega)]
    have sp12 : reg n12 sp = B + 0x21A0 := by rw [k12 sp (by decide), sp10]
    have E12 : SvCode n12.mem := by rw [m12]; exact E11
    have SC12 : SvShaCode n12.mem := SC.sv F KS fun x hx => by rw [m12, m11, fr10' x hx]
    have c12' : memLoad32 n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4A0 + 0x40) = 0 := by rw [sv_cnt, m12, m11, c0]
    -- 0xBA2: sha384UpdateBlocks(sp + 0x4A0, p, len / 128)
    obtain ⟨n13, c13, s13, sp13, rk13, K13, hv13, cnt0, cnt1, cnt2, cnt3, f13⟩ := sv_s5bF (st := 0x4A0)
      (nb := len / 128) F E12 SC12 KS s12 sv_at_ba2 sv_at_ba6 (by decide) (by decide) sp12 v12a0 v12a1
      (by rw [k12 a2 (by decide), v10a2]) (by decide) (by decide)
      (by rw [c12']; show 0 + len / 128 < 2 ^ 32; omega) (hin.shrink (by omega))
    have E13 : SvCode n13.mem := E12.fr F f13
    -- 0xBAA: sb s0, 0x49F(sp)
    obtain ⟨n14, d14, s14, fr14, K14, W14, rg14⟩ := sv_sb F E13 s13 sv_at_baa (off' := 0xBAE) (c := 0x49F) (by decide)
      (by rw [sp13]; rfl) (by decide)
    have E14 : SvCode n14.mem := E13.fr F fr14
    obtain ⟨n15, c15, u15⟩ := s14.block (off' := 0xBB6) [.aluImm .add a0 sp 0x420, .alu .add a1 x0 23,
      .alu .add a2 x0 8] E14.self (by decide) ⟨trivial, trivial, trivial, trivial⟩
    have m15 : n15.mem = n14.mem := u15.mem
    have s15 : St n15.mem SV n15 0xBB6 (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
    have k15 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n15 q = reg n13 q :=
      fun q hq => by rw [u15.regs, runBlock_reg _ _ _ q s14.zero (by revert hq; revert q; decide), rg14]
    have E15 : SvCode n15.mem := by rw [m15]; exact E14
    have hdrop := (hin.drop (k := 128 * (len / 128)) (by omega)).shrink (k := len % 128) (by omega)
    obtain ⟨n16, P16, K16, cp16⟩ := sv_mcIn (c := 0x420) (N := len % 128) F E15 s15 sv_at_bb6 sv_at_bba (by decide)
      (by decide) (by rw [k15 sp (by decide), sp13])
      (by rw [u15.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [rg14, sp13]; rfl)
      (by rw [u15.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
          rw [rg14, rk13 23 (by decide), v12_23]; exact BitVec.zero_add _)
      (by rw [u15.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
          rw [rg14, rk13 8 (by decide), v12_8]; exact BitVec.zero_add _)
      (by omega) hdrop
    have E16 : SvCode n16.mem := E15.fr F P16.fr
    -- 0xBBE: j 0xBD4
    obtain ⟨n17, d17, u17⟩ := P16.st.jump E16.self sv_at_bbe (off' := 0xBD4) (by decide)
      (by rw [P16.st.pc]; decide)
    have s17 : St n17.mem SV n17 0xBD4 (reg n17) := ⟨u17.pc, rfl, fun _ => rfl⟩
    have m17 : n17.mem = n16.mem := u17.mem
    have fr17 : ∀ x, SvR B x → n17.mem x = n.mem x := fun x hx => by
      rw [m17, P16.fr x hx, m15, fr14 x hx, f13 x hx, m12, m11, fr10' x hx]
    have hml : (memBytes n.mem p len).length = len := memBytes_length _ _ _
    have kS : ∀ e, 0x4A0 ≤ e → e < 0x1690 → n17.mem (B + 0x21A0 + BitVec.ofNat 32 e) =
        n13.mem (B + 0x21A0 + BitVec.ofNat 32 e) := fun e h1 h2 => by
      rw [m17, K16 e (by omega) (Or.inr (by omega)), m15, K14 e (by omega) (Or.inr (by omega))]
    have hW : ∀ c, 0x4A0 ≤ c → c + 4 ≤ 0x1690 → memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 c) =
        memLoad32 n13.mem (B + 0x21A0 + BitVec.ofNat 32 c) := fun c h1 h2 =>
      memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact kS _ (by omega) (by omega)
    have H : SvHasher B n17.mem 0x420 (memBytes n.mem p len) := by
      refine ⟨by rw [hml]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hml]
        show n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x49F) = _
        rw [m17, K16 _ (by omega) (Or.inr (by omega)), m15, W14, rk13 8 (by decide), v12_8, ext8_ofNat]
      · rw [hml, tailBytes5_mem]
        unfold memBytes
        apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        rw [add_ofNat_assoc, m17, cp16 i hi, m15, add_ofNat_assoc,
          inR n14.mem (fun x hx => by rw [fr14 x hx, f13 x hx, m12, m11, fr10' x hx]) _ (by omega)]
      · rw [fullBlocks5_mem]
        show (s5Hv n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4A0)).toList = _
        rw [s5Hv_congr (M := n13.mem) fun i hi => by rw [add_ofNat_assoc]; exact kS _ (by omega) (by omega), hv13,
          S5U.blockList128_congr (M := n.mem) (M' := n12.mem) fun i hi => by
            rw [m12, m11]; exact inR n10.mem fr10' i (by omega),
          show (s5Hv n12.mem (B + 0x21A0 + BitVec.ofNat 32 0x4A0)) = s5Hv n10.mem (B + 0x21A0 + BitVec.ofNat 32 0x4A0)
            by rw [m12, m11], hv10]
      · rw [hml]; show memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4E0) = _
        rw [hW _ (by decide) (by decide), ← sv_cnt, cnt0, c12']; exact BitVec.zero_add _
      · show memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4E4) = _
        rw [hW _ (by decide) (by decide), ← sv_cntk B 0x44, show BitVec.ofNat 32 0x44 = (0x44 : Word) from rfl, cnt1,
          show B + 0x21A0 + BitVec.ofNat 32 0x4A0 + (0x44 : Word) = B + 0x21A0 + BitVec.ofNat 32 0x4E4 from sv_cntk B 0x44,
          m12, m11, c1']
      · show memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4E8) = _
        rw [hW _ (by decide) (by decide), ← sv_cntk B 0x48, show BitVec.ofNat 32 0x48 = (0x48 : Word) from rfl, cnt2,
          show B + 0x21A0 + BitVec.ofNat 32 0x4A0 + (0x48 : Word) = B + 0x21A0 + BitVec.ofNat 32 0x4E8 from sv_cntk B 0x48,
          m12, m11, c2]
      · show memLoad32 n17.mem (B + 0x21A0 + BitVec.ofNat 32 0x4EC) = _
        rw [hW _ (by decide) (by decide), ← sv_cntk B 0x4C, show BitVec.ofNat 32 0x4C = (0x4C : Word) from rfl, cnt3,
          show B + 0x21A0 + BitVec.ofNat 32 0x4A0 + (0x4C : Word) = B + 0x21A0 + BitVec.ofNat 32 0x4EC from sv_cntk B 0x4C,
          m12, m11, c3']
    refine ⟨n17, c1.trans (d2.trans (c3.trans (P4.steps.trans (c5.trans (d6.trans (c7.trans (d8.trans (d9.trans
      (d10.trans ((Steps.single d11).trans (c12.trans (c13.trans (d14.trans (c15.trans (P16.steps.trans
      (Steps.single d17)))))))))))))))), s17,
      by rw [u17.regs, P16.regs sp (by decide), k15 sp (by decide), sp13], fun q hq => ?_, fun e he hL => ?_, H, fr17⟩
    · rw [u17.regs, P16.regs q (by revert hq; revert q; decide), k15 q (by revert hq; revert q; decide),
        rk13 q (by revert hq; revert q; decide), k12 q (by revert hq; revert q; decide), kk10 q hq]
    · have h := hL _ (List.mem_singleton_self _)
      simp only at h
      rw [m17, K16 e he (by omega), m15, K14 e he (by omega),
        K13 e he (fun q hq => by rw [List.mem_singleton] at hq; subst hq; simp only; omega), m12, m11,
        KL10 e he fun q hq => by rw [List.mem_singleton] at hq; subst hq; simp only; omega]

end C3.RV32.Sv
