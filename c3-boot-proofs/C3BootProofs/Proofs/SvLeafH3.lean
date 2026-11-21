import C3BootProofs.Proofs.SvLeafH2

/-!
# `sigstore::verify`: the last block and the digest

From offset 0xD20, `verify_leaf` stores the length in bits in the buffer's
last 16 bytes, compresses the buffer, writes the 8 hash words big-endian to
offset 0x1020 of the frame, and keeps the first 48 bytes.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

/-- Two memories whose four words at `P` agree hold the same 16 bytes there. -/
theorem mb16_words {M M' : Word → BitVec 8} {P : Word}
    (h : ∀ i, i < 4 → memLoad32 M' (P + BitVec.ofNat 32 (4 * i)) = memLoad32 M (P + BitVec.ofNat 32 (4 * i))) :
    memBytes M' P 16 = memBytes M P 16 :=
  memBytes_congr fun j hj => by
    obtain ⟨a0, a1, a2, a3⟩ := byte_of_ld (h (j / 4) (by omega))
    obtain ⟨b0, b1, b2, b3⟩ := byte_of_ld (M := M) (a := P + BitVec.ofNat 32 (4 * (j / 4))) rfl
    have e : P + BitVec.ofNat 32 j = P + BitVec.ofNat 32 (4 * (j / 4)) + BitVec.ofNat 32 (j % 4) := by
      rw [add_ofNat_assoc]; congr 2; omega
    rw [e]
    have : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
    rcases this with h' | h' | h' | h' <;> rw [h']
    · rw [add_ofNat_zero, a0, b0]
    · exact a1.trans b1.symm
    · exact a2.trans b2.symm
    · exact a3.trans b3.symm

/-- The four words `finalize` stores are the length in bits, a 128-bit
big-endian integer. -/
theorem be128_words {M : Word → BitVec 8} {P lo : Word} {pos : Nat} (hp : pos < 128)
    (h0 : memLoad32 M (P + BitVec.ofNat 32 0) = 0) (h4 : memLoad32 M (P + BitVec.ofNat 32 4) = 0)
    (h8 : memLoad32 M (P + BitVec.ofNat 32 8) = bswap32 (lo >>> 22))
    (h12 : memLoad32 M (P + BitVec.ofNat 32 12) = bswap32 ((lo <<< 10) ||| (BitVec.ofNat 32 pos <<< 3))) :
    memBytes M P 16 = Sha512.be128 (8 * (128 * lo.toNat + pos)) := by
  have sp : ∀ c d, c + 4 ≤ d ∨ d + 4 ≤ c → c + 4 ≤ 16 → d + 4 ≤ 16 →
      Sep (P + BitVec.ofNat 32 c) 4 (P + BitVec.ofNat 32 d) 4 := fun c d h hc hd =>
    sep_offsets P h (by omega) (by omega)
  rw [← len_bytes5 M P lo pos hp]
  refine mb16_words fun i hi => ?_
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · rw [h0, memLoad32_store32_sep (sp 12 0 (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (sp 8 0 (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (sp 4 0 (by decide) (by decide) (by decide)), add_ofNat_zero, memLoad32_store32_same]
  · rw [h4, memLoad32_store32_sep (sp 12 4 (by decide) (by decide) (by decide)),
      memLoad32_store32_sep (sp 8 4 (by decide) (by decide) (by decide)), memLoad32_store32_same]
  · rw [h8, memLoad32_store32_sep (sp 12 8 (by decide) (by decide) (by decide)), memLoad32_store32_same]
  · rw [h12, memLoad32_store32_same]

theorem sv_a20 (B : Word) (k : Nat) (w : Word) (hw : w = BitVec.ofNat 32 k) :
    B + 0x21A0 + BitVec.ofNat 32 0xA20 + w = B + 0x21A0 + BitVec.ofNat 32 (0xA20 + k) := by
  rw [hw]; exact sv_o B _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0xD20 to 0xD42: the length in bits stored in the buffer's last
16 bytes from `s8`, `s0`, and the frame words at 0x74 and 0x78, and the buffer
compressed into the hash value. -/
theorem sv_lh5 {B lo : Word} {pos : Nat} {n : Machine} (hp : pos < 128) (F : Fr B 0x3830) (E : SvCode n.mem)
    (SC : SvShaCode n.mem) (KS : SvKSep B) (s : St n.mem SV n 0xD20 (reg n)) (rsp : reg n sp = B + 0x21A0)
    (h27 : reg n 27 = B + 0x21A0 + BitVec.ofNat 32 0xA20) (h23 : reg n 23 = B + 0x21A0 + BitVec.ofNat 32 0xAA0)
    (h24 : reg n 24 = 0) (h8 : reg n 8 = 0)
    (w74 : memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = bswap32 (lo >>> 22))
    (w78 : memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = bswap32 ((lo <<< 10) ||| (BitVec.ofNat 32 pos <<< 3))) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' 0xD42 (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      (s5Hv n'.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0)).toList =
        Sha512.compress (s5Hv n.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0)).toList
          (memBytes n.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 112 ++ Sha512.be128 (8 * (128 * lo.toNat + pos))) ∧
      SvKeepL B n.mem n'.mem [(0xA90, 0x50)] ∧ (∀ x, SvR B x → n'.mem x = n.mem x) := by
  -- 0xD20: sw s8, 0x70(s11)
  obtain ⟨n1, d1, s1, fr1, K1, W1, rg1⟩ := sv_sw F E s sv_at_d20 (off' := 0xD24) (c := 0xA90) (by decide)
    (by rw [h27]; exact sv_a20 B 0x70 _ rfl) (by decide) (by decide)
  have E1 : SvCode n1.mem := E.fr F fr1
  obtain ⟨n2, c2, u2⟩ := s1.block (off' := 0xD26) [.alu .add a1 x0 27] E1.self (by decide) ⟨trivial, trivial⟩
  have m2 : n2.mem = n1.mem := u2.mem
  have s2 : St n2.mem SV n2 0xD26 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have k2 : ∀ q : Fin 32, q ≠ a1 → reg n2 q = reg n q := fun q hq => by
    rw [u2.regs]; simp only [runBlock, BInstr.run]; rw [upd_ne' hq s1.zero, rg1]
  have va1 : reg n2 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [u2.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; simp only [rg1]; rw [h27, s.zero]
    exact BitVec.zero_add _
  have E2 : SvCode n2.mem := by rw [m2]; exact E1
  -- 0xD26: sw s0, 0x74(a1)
  obtain ⟨n3, d3, s3, fr3, K3, W3, rg3⟩ := sv_sw F E2 s2 sv_at_d26 (off' := 0xD28) (c := 0xA94) (by decide)
    (by rw [va1]; exact sv_a20 B 0x74 _ rfl) (by decide) (by decide)
  have E3 : SvCode n3.mem := E2.fr F fr3
  -- 0xD28: lw a0, 0x74(sp)
  have sp3 : reg n3 sp = B + 0x21A0 := by rw [rg3, k2 sp (by decide), rsp]
  obtain ⟨n4, c4, u4⟩ := s3.block (off' := 0xD2A) [.lw a0 sp 0x74] E3.self (by decide)
    ⟨show (reg n3 sp + 0x74).toNat % 4 = 0 by rw [sp3]; exact sv_al F (c := 0x74) (by decide) (by decide), trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have s4 : St n4.mem SV n4 0xD2A (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have v4 : reg n4 a0 = bswap32 (lo >>> 22) := by
    rw [u4.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [sp3]
    show memLoad32 n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x74) = _
    rw [K3.w32 (by decide) (Or.inl (by decide)), m2, K1.w32 (by decide) (Or.inl (by decide)), w74]
  have E4 : SvCode n4.mem := by rw [m4]; exact E3
  -- 0xD2A: sw a0, 0x78(a1)
  obtain ⟨n5, d5, s5, fr5, K5, W5, rg5⟩ := sv_sw F E4 s4 sv_at_d2a (off' := 0xD2C) (c := 0xA98) (by decide)
    (by rw [u4.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [rg3, va1]; exact sv_a20 B 0x78 _ rfl)
    (by decide) (by decide)
  have E5 : SvCode n5.mem := E4.fr F fr5
  have sp5 : reg n5 sp = B + 0x21A0 := by rw [rg5, u4.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; exact sp3
  -- 0xD2C: lw a0, 0x78(sp)
  obtain ⟨n6, c6, u6⟩ := s5.block (off' := 0xD2E) [.lw a0 sp 0x78] E5.self (by decide)
    ⟨show (reg n5 sp + 0x78).toNat % 4 = 0 by rw [sp5]; exact sv_al F (c := 0x78) (by decide) (by decide), trivial⟩
  have m6 : n6.mem = n5.mem := u6.mem
  have s6 : St n6.mem SV n6 0xD2E (reg n6) := ⟨u6.pc, rfl, fun _ => rfl⟩
  have v6 : reg n6 a0 = bswap32 ((lo <<< 10) ||| (BitVec.ofNat 32 pos <<< 3)) := by
    rw [u6.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [sp5]
    show memLoad32 n5.mem (B + 0x21A0 + BitVec.ofNat 32 0x78) = _
    rw [K5.w32 (by decide) (Or.inl (by decide)), m4, K3.w32 (by decide) (Or.inl (by decide)), m2,
      K1.w32 (by decide) (Or.inl (by decide)), w78]
  have E6 : SvCode n6.mem := by rw [m6]; exact E5
  have k6 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → reg n6 q = reg n q := fun q h0 h1 => by
    rw [u6.regs]; simp only [runBlock, BInstr.run]; rw [upd_ne' h0 s5.zero, rg5, u4.regs]
    simp only [runBlock, BInstr.run]; rw [upd_ne' h0 s3.zero, rg3, k2 q h1]
  have va1' : reg n6 a1 = B + 0x21A0 + BitVec.ofNat 32 0xA20 := by
    rw [u6.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [rg5, u4.regs]
    simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [rg3, va1]
  -- 0xD2E: sw a0, 0x7C(a1)
  obtain ⟨n7, d7, s7, fr7, K7, W7, rg7⟩ := sv_sw F E6 s6 sv_at_d2e (off' := 0xD30) (c := 0xA9C) (by decide)
    (by rw [va1']; exact sv_a20 B 0x7C _ rfl) (by decide) (by decide)
  have E7 : SvCode n7.mem := E6.fr F fr7
  obtain ⟨n8, c8, u8⟩ := s7.block (off' := 0xD3A) [.aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x221, .alu .add a0 x0 23]
    E7.self (by decide) ⟨trivial, trivial, trivial, trivial⟩
  have m8 : n8.mem = n7.mem := u8.mem
  have s8 : St n8.mem SV n8 0xD3A (reg n8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have k8 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n8 q = reg n q :=
    fun q hq => by
      rw [u8.regs, runBlock_reg _ _ _ q s7.zero (by revert hq; revert q; decide), rg7,
        k6 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)]
  have E8 : SvCode n8.mem := by rw [m8]; exact E7
  have fr8 : ∀ x, SvR B x → n8.mem x = n.mem x := fun x hx => by
    rw [m8, fr7 x hx, m6, fr5 x hx, m4, fr3 x hx, m2, fr1 x hx]
  have SC8 : SvShaCode n8.mem := SC.sv F KS fr8
  obtain ⟨n9, c9, s9, sp9, rk9, K9, hv9, f9⟩ := sv_fbF (a := 0xAA0) (b := 0xA20) F E8 SC8 KS s8 sv_at_d3a sv_at_d3e
    (by decide) (by decide) (by rw [k8 sp (by decide), rsp])
    (by rw [u8.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [rg7, k6 23 (by decide) (by decide), h23]
        exact BitVec.zero_add _)
    (by rw [u8.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [rg7, k6 sp (by decide) (by decide), rsp]; exact sv_7ff B 0x221)
    (by decide) (by decide) (by decide)
  have K8 : SvKeepL B n.mem n8.mem [(0xA90, 0x10)] := fun e he hL => by
    have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    rw [m8, K7 e he (by omega), m6, K5 e he (by omega), m4, K3 e he (by omega), m2, K1 e he (by omega)]
  have hS : s5Hv n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) = s5Hv n.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) :=
    s5Hv_congr fun i hi => by
      rw [sv_o]; exact K8 _ (by omega) fun q hq => by rw [List.mem_singleton] at hq; subst hq; simp only; omega
  have hB : memBytes n8.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 128 =
      memBytes n.mem (B + 0x21A0 + BitVec.ofNat 32 0xA20) 112 ++ Sha512.be128 (8 * (128 * lo.toNat + pos)) := by
    rw [show (128 : Nat) = 112 + 16 from rfl, memBytes_split,
      memBytes_congr (M := n.mem) (M' := n8.mem) (p := B + 0x21A0 + BitVec.ofNat 32 0xA20) (n := 112) fun i hi => by
        rw [sv_o]; exact K8 _ (by omega) fun q hq => by rw [List.mem_singleton] at hq; subst hq; simp only; omega,
      sv_o]
    congr 1
    refine be128_words hp ?_ ?_ ?_ ?_
    · rw [sv_o, m8, K7.w32 (by decide) (Or.inl (by decide)), m6, K5.w32 (by decide) (Or.inl (by decide)), m4,
        K3.w32 (by decide) (Or.inl (by decide)), m2, W1, h24]
    · rw [sv_o, m8, K7.w32 (by decide) (Or.inl (by decide)), m6, K5.w32 (by decide) (Or.inl (by decide)), m4, W3,
        k2 8 (by decide), h8]
    · rw [sv_o, m8, K7.w32 (by decide) (Or.inl (by decide)), m6, W5, v4]
    · rw [sv_o, m8, W7, v6]
  refine ⟨n9, d1.trans (c2.trans (d3.trans (c4.trans (d5.trans (c6.trans (d7.trans (c8.trans c9))))))), s9, sp9,
    fun q hq => by rw [rk9 q hq, k8 q (by revert hq; revert q; decide)], by rw [hv9, hS, hB],
    fun e he hL => ?_, fun x hx => by rw [f9 x hx, fr8 x hx]⟩
  have h1 := hL _ (List.mem_singleton_self _)
  simp only at h1
  rw [K9 e he (fun q hq => by rw [List.mem_singleton] at hq; subst hq; simp only; omega),
    K8 e he (fun q hq => by rw [List.mem_singleton] at hq; subst hq; simp only; omega)]

def svRd1 : List BInstr :=
  [.alu .add a0 x0 23, .lw a1 a0 0x4, .lw a2 a0 0x0, .aluImm .srl 17 a1 0x18, .aluImm .srl a4 a2 0x18,
   .aluImm .srl a5 a2 0x8, .aluImm .srl 8 a2 0x10, .aluImm .srl a0 a1 0x8, .aluImm .srl a3 a1 0x10]

set_option maxRecDepth 100000 in
theorem svRd1_end : blockEnd sigstoreVerifyCode 0xD48 svRd1 = some 0xD66 := by decide

theorem sv_b8 (B : Word) (c : Nat) (j : Nat) (w : Word) (hw : w = BitVec.ofNat 32 j) :
    B + 0x21A0 + BitVec.ofNat 32 c + w = B + 0x21A0 + BitVec.ofNat 32 (c + j) := by
  rw [hw]; exact sv_o B _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- One pass of the loop at offset 0xD48: hash word `k` stored big-endian at
offset `0x1020 + 8k`. -/
theorem sv_rd_body {B : Word} {n : Machine} {k : Nat} (hk : k < 8) (F : Fr B 0x3830) (E : SvCode n.mem)
    (s : St n.mem SV n 0xD48 (reg n)) (h9 : reg n 9 = B + 0x21A0 + BitVec.ofNat 32 (0x1020 + 8 * k))
    (h23 : reg n 23 = B + 0x21A0 + BitVec.ofNat 32 (0xAA0 + 8 * k)) (h16 : reg n 16 = BitVec.ofNat 32 (8 - k)) :
    ∃ n', Steps n n' ∧ (k + 1 < 8 → St n'.mem SV n' 0xD48 (reg n')) ∧ (k + 1 = 8 → St n'.mem SV n' 0xD90 (reg n')) ∧
      reg n' 9 = B + 0x21A0 + BitVec.ofNat 32 (0x1020 + 8 * (k + 1)) ∧
      reg n' 23 = B + 0x21A0 + BitVec.ofNat 32 (0xAA0 + 8 * (k + 1)) ∧ reg n' 16 = BitVec.ofNat 32 (8 - (k + 1)) ∧
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + 8 * k)) 8 =
        Sha512.wordBytes (hvW n.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) k) ∧
      SvKeepL B n.mem n'.mem [(0x1020 + 8 * k, 8)] ∧ (∀ x, SvR B x → n'.mem x = n.mem x) := by
  have z0 := s.zero
  have hA : aluEval .add (reg n x0) (reg n 23) = B + 0x21A0 + BitVec.ofNat 32 (0xAA0 + 8 * k) := by
    rw [z0, h23]; exact BitVec.zero_add _
  obtain ⟨n1, c1, u1⟩ := s.block svRd1 E.self svRd1_end (by
    simp +decide only [svRd1, BlockOk, BInstr.ok, BInstr.run, upd, ↓reduceIte, and_true, true_and]
    rw [hA]
    exact ⟨by rw [sv_b8 B _ 4 (4 : Word) rfl]; exact sv_al F (by omega) (by omega),
      by rw [sv_b8 B _ 0 (0 : Word) rfl]; exact sv_al F (by omega) (by omega)⟩)
  have m1 : n1.mem = n.mem := u1.mem
  have s1 : St n1.mem SV n1 0xD66 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 16, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n1 q = reg n q :=
    fun q hq => by rw [u1.regs, runBlock_reg _ _ _ q z0 (by revert hq; revert q; decide)]
  have hl : memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 (0xAA0 + 8 * k) + 0x0) =
      memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0 + BitVec.ofNat 32 (8 * k)) := by
    rw [sv_b8 B _ 0 (0 : Word) rfl, sv_o, Nat.add_zero]
  have hh : memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 (0xAA0 + 8 * k) + 0x4) =
      memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0 + BitVec.ofNat 32 (8 * k + 4)) := by
    rw [sv_b8 B _ 4 (4 : Word) rfl, sv_o, Nat.add_assoc]
  have bt : ∀ (r : Fin 32) (x : Word) (sh : Nat), sh < 32 → reg n1 r = aluEval .srl x (BitVec.ofNat 32 sh) →
      ((reg n1 r).extractLsb' 0 8).toNat = x.toNat / 2 ^ sh % 256 := fun r x sh hs h => by rw [h]; exact srl_byte x sh hs
  have t17 := bt 17 (memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0 + BitVec.ofNat 32 (8 * k + 4))) 24 (by decide)
    (by rw [u1.regs]; simp +decide only [svRd1, runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA, hh]; rfl)
  have ta3 := bt a3 (memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0 + BitVec.ofNat 32 (8 * k + 4))) 16 (by decide)
    (by rw [u1.regs]; simp +decide only [svRd1, runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA, hh]; rfl)
  have ta0 := bt a0 (memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0 + BitVec.ofNat 32 (8 * k + 4))) 8 (by decide)
    (by rw [u1.regs]; simp +decide only [svRd1, runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA, hh]; rfl)
  have ta4 := bt a4 (memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0 + BitVec.ofNat 32 (8 * k))) 24 (by decide)
    (by rw [u1.regs]; simp +decide only [svRd1, runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA, hl]; rfl)
  have t8 := bt 8 (memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0 + BitVec.ofNat 32 (8 * k))) 16 (by decide)
    (by rw [u1.regs]; simp +decide only [svRd1, runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA, hl]; rfl)
  have ta5 := bt a5 (memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0 + BitVec.ofNat 32 (8 * k))) 8 (by decide)
    (by rw [u1.regs]; simp +decide only [svRd1, runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA, hl]; rfl)
  have ta1 : ((reg n1 a1).extractLsb' 0 8).toNat =
      (memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0 + BitVec.ofNat 32 (8 * k + 4))).toNat % 256 := by
    rw [u1.regs]; simp +decide only [svRd1, runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA, hh, byte_toNat, Nat.pow_zero,
      Nat.div_one]
  have ta2 : ((reg n1 a2).extractLsb' 0 8).toNat =
      (memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0 + BitVec.ofNat 32 (8 * k))).toNat % 256 := by
    rw [u1.regs]; simp +decide only [svRd1, runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA, hl, byte_toNat, Nat.pow_zero,
      Nat.div_one]
  have E1 : SvCode n1.mem := by rw [m1]; exact E
  have v9 : reg n1 9 = B + 0x21A0 + BitVec.ofNat 32 (0x1020 + 8 * k) := by rw [k1 9 (by decide), h9]
  obtain ⟨n2, d2, s2, fr2, K2, W2, rg2⟩ := sv_sb F E1 s1 sv_at_d66 (off' := 0xD6A) (c := 0x1020 + 8 * k + 4)
    (by decide) (by rw [v9]; exact sv_b8 B _ 4 (4 : Word) rfl) (by omega)
  have E2 : SvCode n2.mem := E1.fr F fr2
  obtain ⟨n3, d3, s3, fr3, K3, W3, rg3⟩ := sv_sb F E2 s2 sv_at_d6a (off' := 0xD6E) (c := 0x1020 + 8 * k + 5)
    (by decide) (by rw [rg2, v9]; exact sv_b8 B _ 5 (5 : Word) rfl) (by omega)
  have E3 : SvCode n3.mem := E2.fr F fr3
  obtain ⟨n4, d4, s4, fr4, K4, W4, rg4⟩ := sv_sb F E3 s3 sv_at_d6e (off' := 0xD72) (c := 0x1020 + 8 * k + 6)
    (by decide) (by rw [rg3, rg2, v9]; exact sv_b8 B _ 6 (6 : Word) rfl) (by omega)
  have E4 : SvCode n4.mem := E3.fr F fr4
  obtain ⟨n5, d5, s5, fr5, K5, W5, rg5⟩ := sv_sb F E4 s4 sv_at_d72 (off' := 0xD76) (c := 0x1020 + 8 * k + 7)
    (by decide) (by rw [rg4, rg3, rg2, v9]; exact sv_b8 B _ 7 (7 : Word) rfl) (by omega)
  have E5 : SvCode n5.mem := E4.fr F fr5
  obtain ⟨n6, d6, s6, fr6, K6, W6, rg6⟩ := sv_sb F E5 s5 sv_at_d76 (off' := 0xD7A) (c := 0x1020 + 8 * k + 0)
    (by decide) (by rw [rg5, rg4, rg3, rg2, v9]; exact sv_b8 B _ 0 (0 : Word) rfl) (by omega)
  have E6 : SvCode n6.mem := E5.fr F fr6
  obtain ⟨n7, d7, s7, fr7, K7, W7, rg7⟩ := sv_sb F E6 s6 sv_at_d7a (off' := 0xD7E) (c := 0x1020 + 8 * k + 1)
    (by decide) (by rw [rg6, rg5, rg4, rg3, rg2, v9]; exact sv_b8 B _ 1 (1 : Word) rfl) (by omega)
  have E7 : SvCode n7.mem := E6.fr F fr7
  obtain ⟨n8, d8, s8, fr8, K8, W8, rg8⟩ := sv_sb F E7 s7 sv_at_d7e (off' := 0xD82) (c := 0x1020 + 8 * k + 2)
    (by decide) (by rw [rg7, rg6, rg5, rg4, rg3, rg2, v9]; exact sv_b8 B _ 2 (2 : Word) rfl) (by omega)
  have E8 : SvCode n8.mem := E7.fr F fr8
  obtain ⟨n9, d9, s9, fr9, K9, W9, rg9⟩ := sv_sb F E8 s8 sv_at_d82 (off' := 0xD86) (c := 0x1020 + 8 * k + 3)
    (by decide) (by rw [rg8, rg7, rg6, rg5, rg4, rg3, rg2, v9]; exact sv_b8 B _ 3 (3 : Word) rfl) (by omega)
  have E9 : SvCode n9.mem := E8.fr F fr9
  have y4 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + 8 * k + 4)) = (reg n1 a4).extractLsb' 0 8 := by
    rw [K9 _ (by omega) (by omega), K8 _ (by omega) (by omega), K7 _ (by omega) (by omega), K6 _ (by omega) (by omega), K5 _ (by omega) (by omega), K4 _ (by omega) (by omega), K3 _ (by omega) (by omega), W2]
  have y5 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + 8 * k + 5)) = (reg n1 (8 : Fin 32)).extractLsb' 0 8 := by
    rw [K9 _ (by omega) (by omega), K8 _ (by omega) (by omega), K7 _ (by omega) (by omega), K6 _ (by omega) (by omega), K5 _ (by omega) (by omega), K4 _ (by omega) (by omega), W3, rg2]
  have y6 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + 8 * k + 6)) = (reg n1 a5).extractLsb' 0 8 := by
    rw [K9 _ (by omega) (by omega), K8 _ (by omega) (by omega), K7 _ (by omega) (by omega), K6 _ (by omega) (by omega), K5 _ (by omega) (by omega), W4, rg3, rg2]
  have y7 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + 8 * k + 7)) = (reg n1 a2).extractLsb' 0 8 := by
    rw [K9 _ (by omega) (by omega), K8 _ (by omega) (by omega), K7 _ (by omega) (by omega), K6 _ (by omega) (by omega), W5, rg4, rg3, rg2]
  have y0 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + 8 * k + 0)) = (reg n1 (17 : Fin 32)).extractLsb' 0 8 := by
    rw [K9 _ (by omega) (by omega), K8 _ (by omega) (by omega), K7 _ (by omega) (by omega), W6, rg5, rg4, rg3, rg2]
  have y1 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + 8 * k + 1)) = (reg n1 a3).extractLsb' 0 8 := by
    rw [K9 _ (by omega) (by omega), K8 _ (by omega) (by omega), W7, rg6, rg5, rg4, rg3, rg2]
  have y2 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + 8 * k + 2)) = (reg n1 a0).extractLsb' 0 8 := by
    rw [K9 _ (by omega) (by omega), W8, rg7, rg6, rg5, rg4, rg3, rg2]
  have y3 : n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + 8 * k + 3)) = (reg n1 a1).extractLsb' 0 8 := by
    rw [W9, rg8, rg7, rg6, rg5, rg4, rg3, rg2]
  have hw : memBytes n9.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + 8 * k)) 8 =
      Sha512.wordBytes (hvW n.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) k) := by
    unfold hvW
    rw [wordBytes_pk]
    unfold memBytes
    rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
    simp only [List.map_cons, List.map_nil, sv_o]
    rw [y0, y1, y2, y3, y4, y5, y6, y7, t17, ta3, ta0, ta1, ta4, t8, ta5, ta2]
    simp only [sv_o]
  obtain ⟨n10, c10, u10⟩ := s9.block (off' := 0xD8C) [.aluImm .add 9 9 0x8, .aluImm .add 23 23 0x8,
    .aluImm .add a6 a6 0xFFFFFFFF] E9.self (by decide) ⟨trivial, trivial, trivial, trivial⟩
  have m10 : n10.mem = n9.mem := u10.mem
  have s10 : St n10.mem SV n10 0xD8C (reg n10) := ⟨u10.pc, rfl, fun _ => rfl⟩
  have E10 : SvCode n10.mem := by rw [m10]; exact E9
  have rg91 : ∀ q, reg n9 q = reg n1 q := fun q => by rw [rg9, rg8, rg7, rg6, rg5, rg4, rg3, rg2]
  have k10 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 24, 25, 26, 27] → reg n10 q = reg n q := fun q hq => by
    rw [u10.regs, runBlock_reg _ _ _ q s9.zero (by revert hq; revert q; decide), rg91,
      k1 q (by revert hq; revert q; decide)]
  have v9' : reg n10 9 = B + 0x21A0 + BitVec.ofNat 32 (0x1020 + 8 * (k + 1)) := by
    rw [u10.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [rg91, v9,
      show 0x1020 + 8 * (k + 1) = 0x1020 + 8 * k + 8 by omega]; exact sv_o B _ 8
  have v23' : reg n10 23 = B + 0x21A0 + BitVec.ofNat 32 (0xAA0 + 8 * (k + 1)) := by
    rw [u10.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [rg91, k1 23 (by decide), h23,
      show 0xAA0 + 8 * (k + 1) = 0xAA0 + 8 * k + 8 by omega]; exact sv_o B _ 8
  have v16' : reg n10 16 = BitVec.ofNat 32 (8 - (k + 1)) := by
    rw [u10.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [rg91, k1 16 (by decide), h16]
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 32 (8 - k) + 0xFFFFFFFF).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl]
    omega
  have fr10 : ∀ x, SvR B x → n10.mem x = n.mem x := fun x hx => by
    rw [m10, fr9 x hx, fr8 x hx, fr7 x hx, fr6 x hx, fr5 x hx, fr4 x hx, fr3 x hx, fr2 x hx, m1]
  have KL : SvKeepL B n.mem n10.mem [(0x1020 + 8 * k, 8)] := fun e he hL => by
    have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    rw [m10, K9 e he (by omega), K8 e he (by omega), K7 e he (by omega), K6 e he (by omega), K5 e he (by omega),
      K4 e he (by omega), K3 e he (by omega), K2 e he (by omega), m1]
  have cs : Steps n n10 := c1.trans (d2.trans (d3.trans (d4.trans (d5.trans (d6.trans (d7.trans (d8.trans
    (d9.trans c10))))))))
  have hw' : memBytes n10.mem (B + 0x21A0 + BitVec.ofNat 32 (0x1020 + 8 * k)) 8 =
      Sha512.wordBytes (hvW n.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) k) := by rw [m10, hw]
  by_cases hk1 : k + 1 < 8
  · obtain ⟨n11, d11, u11⟩ := s10.taken E10.self 0xD48 sv_at_d8c (by decide) (by
      rw [v16', s10.zero]
      exact br_bne_t fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact absurd this (by show 8 - (k + 1) ≠ 0; omega))
    exact ⟨n11, cs.trans (Steps.single d11), fun _ => ⟨u11.pc, rfl, fun _ => rfl⟩, fun h => absurd h (by omega),
      by rw [u11.regs, v9'], by rw [u11.regs, v23'], by rw [u11.regs, v16'], fun q hq => by rw [u11.regs, k10 q hq],
      by rw [u11.mem]; exact hw', by rw [u11.mem]; exact KL, fun x hx => by rw [u11.mem]; exact fr10 x hx⟩
  · obtain ⟨n11, d11, u11⟩ := s10.notTaken E10.self 0xD90 sv_at_d8c (by decide) (by
      rw [v16', s10.zero, show 8 - (k + 1) = 0 by omega]; rfl)
    exact ⟨n11, cs.trans (Steps.single d11), fun h => absurd h hk1, fun _ => ⟨u11.pc, rfl, fun _ => rfl⟩,
      by rw [u11.regs, v9'], by rw [u11.regs, v23'], by rw [u11.regs, v16'], fun q hq => by rw [u11.regs, k10 q hq],
      by rw [u11.mem]; exact hw', by rw [u11.mem]; exact KL, fun x hx => by rw [u11.mem]; exact fr10 x hx⟩

/-- The loop at offset 0xD48 from pass `k` on. -/
theorem sv_rd_loop {B : Word} (F : Fr B 0x3830) {Mst : Word → BitVec 8} {R : Fin 32 → Word} :
    ∀ d k, k + d = 8 → k < 8 → ∀ (n : Machine), SvCode n.mem → St n.mem SV n 0xD48 (reg n) →
      reg n 9 = B + 0x21A0 + BitVec.ofNat 32 (0x1020 + 8 * k) → reg n 23 = B + 0x21A0 + BitVec.ofNat 32 (0xAA0 + 8 * k) →
      reg n 16 = BitVec.ofNat 32 (8 - k) →
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 24, 25, 26, 27] → reg n q = R q) →
      memBytes n.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) (8 * k) =
        ((List.range k).map (hvW Mst (B + 0x21A0 + BitVec.ofNat 32 0xAA0))).flatMap Sha512.wordBytes →
      (∀ e, e + 1 ≤ 0x1690 → (e < 0x1020 ∨ 0x1060 ≤ e) →
        n.mem (B + 0x21A0 + BitVec.ofNat 32 e) = Mst (B + 0x21A0 + BitVec.ofNat 32 e)) →
      (∀ x, SvR B x → n.mem x = Mst x) →
      ∃ n', Steps n n' ∧ St n'.mem SV n' 0xD90 (reg n') ∧
        (∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 24, 25, 26, 27] → reg n' q = R q) ∧
        memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 64 =
          (s5Hv Mst (B + 0x21A0 + BitVec.ofNat 32 0xAA0)).toList.flatMap Sha512.wordBytes ∧
        (∀ e, e + 1 ≤ 0x1690 → (e < 0x1020 ∨ 0x1060 ≤ e) →
          n'.mem (B + 0x21A0 + BitVec.ofNat 32 e) = Mst (B + 0x21A0 + BitVec.ofNat 32 e)) ∧
        (∀ x, SvR B x → n'.mem x = Mst x) := by
  intro d
  induction d with
  | zero => intro k hk hk8; exact absurd hk (by omega)
  | succ d ih =>
    intro k hk hk8 n E s h9 h23 h16 hR hM hfr hx
    obtain ⟨n1, c1, s1a, s1b, v9, v23, v16, kk, hw, KL, fr⟩ := sv_rd_body hk8 F E s h9 h23 h16
    have hW : hvW n.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0) k = hvW Mst (B + 0x21A0 + BitVec.ofNat 32 0xAA0) k := by
      unfold hvW
      have e : ∀ o, o + 4 ≤ 64 → memLoad32 n.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0 + BitVec.ofNat 32 o) =
          memLoad32 Mst (B + 0x21A0 + BitVec.ofNat 32 0xAA0 + BitVec.ofNat 32 o) := fun o ho =>
        memLoad32_congr fun j hj => by
          rw [sv_o, sv_o]; exact hfr _ (by omega) (Or.inl (by omega))
      rw [e _ (by omega), e _ (by omega)]
    have kk1 : ∀ e, e + 1 ≤ 0x1690 → (e < 0x1020 + 8 * k ∨ 0x1020 + 8 * k + 8 ≤ e) →
        n1.mem (B + 0x21A0 + BitVec.ofNat 32 e) = n.mem (B + 0x21A0 + BitVec.ofNat 32 e) := fun e he h =>
      KL e he fun q hq => by rw [List.mem_singleton] at hq; subst hq; exact h
    have hM1 : memBytes n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) (8 * (k + 1)) =
        ((List.range (k + 1)).map (hvW Mst (B + 0x21A0 + BitVec.ofNat 32 0xAA0))).flatMap Sha512.wordBytes := by
      rw [show 8 * (k + 1) = 8 * k + 8 by omega, memBytes_split, flatMap_range_succ, ← hM, ← hW, sv_o, ← hw,
        memBytes_congr (M' := n1.mem) (M := n.mem) (p := B + 0x21A0 + BitVec.ofNat 32 0x1020) (n := 8 * k)
          fun i hi => by rw [sv_o]; exact kk1 _ (by omega) (Or.inl (by omega))]
    have hfr1 : ∀ e, e + 1 ≤ 0x1690 → (e < 0x1020 ∨ 0x1060 ≤ e) →
        n1.mem (B + 0x21A0 + BitVec.ofNat 32 e) = Mst (B + 0x21A0 + BitVec.ofNat 32 e) := fun e he h => by
      rw [kk1 e he (by omega), hfr e he h]
    have hR1 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 24, 25, 26, 27] → reg n1 q = R q := fun q hq => by
      rw [kk q hq, hR q hq]
    have hx1 : ∀ x, SvR B x → n1.mem x = Mst x := fun x h => by rw [fr x h, hx x h]
    by_cases hk1 : k + 1 < 8
    · obtain ⟨n2, c2, rest⟩ := ih (k + 1) (by omega) hk1 n1 (E.fr F fr) (s1a hk1) v9 v23 v16 hR1 hM1 hfr1 hx1
      exact ⟨n2, c1.trans c2, rest⟩
    · have h8 : k + 1 = 8 := by omega
      rw [h8, ← s5Hv_toList, show 8 * 8 = 64 from rfl] at hM1
      exact ⟨n1, c1, s1b h8, hR1, hM1, hfr1, hx1⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0xD42 to 0xD90: the 8 hash words at offset 0xAA0 written
big-endian to offset 0x1020. -/
theorem sv_lh6 {B : Word} {n : Machine} (F : Fr B 0x3830) (E : SvCode n.mem) (s : St n.mem SV n 0xD42 (reg n))
    (h9 : reg n 9 = B + 0x21A0 + BitVec.ofNat 32 0x1020) (h23 : reg n 23 = B + 0x21A0 + BitVec.ofNat 32 0xAA0) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' 0xD90 (reg n') ∧
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 18, 19, 20, 21, 22, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 64 =
        (s5Hv n.mem (B + 0x21A0 + BitVec.ofNat 32 0xAA0)).toList.flatMap Sha512.wordBytes ∧
      SvKeepL B n.mem n'.mem [(0x1020, 0x40)] ∧ (∀ x, SvR B x → n'.mem x = n.mem x) := by
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0xD44) [.aluImm .add a6 x0 0x8] E.self (by decide) ⟨trivial, trivial⟩
  have m1 : n1.mem = n.mem := u1.mem
  have s1 : St n1.mem SV n1 0xD44 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ q : Fin 32, q ≠ a6 → reg n1 q = reg n q := fun q hq => by
    rw [u1.regs]; simp only [runBlock, BInstr.run]; exact upd_ne' hq s.zero
  have v16 : reg n1 16 = 8 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [s.zero]; rfl
  have E1 : SvCode n1.mem := by rw [m1]; exact E
  obtain ⟨n2, d2, u2⟩ := s1.notTaken E1.self 0xD48 sv_at_d44 (by decide) (by rw [v16, s1.zero]; rfl)
  have s2 : St n2.mem SV n2 0xD48 (reg n2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have m2 : n2.mem = n.mem := u2.mem.trans m1
  obtain ⟨n3, c3, s3, hR3, hb3, hf3, hx3⟩ := sv_rd_loop F (Mst := n.mem) (R := reg n) 8 0 rfl (by decide) n2
    (by rw [m2]; exact E) s2 (by rw [u2.regs, k1 9 (by decide), h9]) (by rw [u2.regs, k1 23 (by decide), h23])
    (by rw [u2.regs, v16]; rfl) (fun q hq => by rw [u2.regs, k1 q (by revert hq; revert q; decide)]) rfl
    (fun e _ _ => by rw [m2]) (fun x _ => by rw [m2])
  exact ⟨n3, c1.trans ((Steps.single d2).trans c3), s3, hR3, hb3, fun e he hL => hf3 e he (by
    have h := hL _ (List.mem_singleton_self _); simp only at h; omega), hx3⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0xD90 to 0xDC8: the first 48 bytes at offset 0x1020 copied to
offset 0x1480 and back. -/
theorem sv_lh7 {B : Word} {n : Machine} (F : Fr B 0x3830) (E : SvCode n.mem) (s : St n.mem SV n 0xD90 (reg n))
    (rsp : reg n sp = B + 0x21A0) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' 0xDC8 (reg n') ∧
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 48 = memBytes n.mem (B + 0x21A0 + BitVec.ofNat 32 0x1020) 48 ∧
      SvKeepL B n.mem n'.mem [(0x1480, 0x30), (0x1020, 0x30)] ∧ (∀ x, SvR B x → n'.mem x = n.mem x) := by
  obtain ⟨n1, c1, u1⟩ := s.block (off' := 0xDA4) [.lui a0 0x1000, .aluImm .add a0 a0 0x480, .alu .add a0 a0 sp,
    .lui a1 0x1000, .aluImm .add a1 a1 0x20, .alu .add a1 a1 sp, .aluImm .add a2 x0 0x30] E.self (by decide)
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n.mem := u1.mem
  have s1 : St n1.mem SV n1 0xDA4 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have k1 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n1 q = reg n q :=
    fun q hq => by rw [u1.regs, runBlock_reg _ _ _ q s.zero (by revert hq; revert q; decide)]
  have E1 : SvCode n1.mem := by rw [m1]; exact E
  obtain ⟨n2, P2, K2, cp2⟩ := sv_mc (c := 0x1480) (d := 0x1020) (N := 0x30) F E1 s1 sv_at_da4 sv_at_da8 (by decide)
    (by decide) (by rw [k1 sp (by decide), rsp])
    (by rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [rsp]; exact sv_hi B 0x1480)
    (by rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [rsp]; exact sv_hi B 0x1020)
    (by rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]) (by decide) (by decide) (by decide)
  have E2 : SvCode n2.mem := E1.fr F P2.fr
  have sp2 : reg n2 sp = B + 0x21A0 := by rw [P2.regs sp (by decide), k1 sp (by decide), rsp]
  obtain ⟨n3, c3, u3⟩ := P2.st.block (off' := 0xDC0) [.lui a0 0x1000, .aluImm .add a0 a0 0x20, .alu .add a0 a0 sp,
    .lui a1 0x1000, .aluImm .add a1 a1 0x480, .alu .add a1 a1 sp, .aluImm .add a2 x0 0x30] E2.self (by decide)
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have m3 : n3.mem = n2.mem := u3.mem
  have s3 : St n3.mem SV n3 0xDC0 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have k3 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n3 q = reg n2 q :=
    fun q hq => by rw [u3.regs, runBlock_reg _ _ _ q P2.st.zero (by revert hq; revert q; decide)]
  have E3 : SvCode n3.mem := by rw [m3]; exact E2
  obtain ⟨n4, P4, K4, cp4⟩ := sv_mc (c := 0x1020) (d := 0x1480) (N := 0x30) F E3 s3 sv_at_dc0 sv_at_dc4 (by decide)
    (by decide) (by rw [k3 sp (by decide), sp2])
    (by rw [u3.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [sp2]; exact sv_hi B 0x1020)
    (by rw [u3.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [sp2]; exact sv_hi B 0x1480)
    (by rw [u3.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]) (by decide) (by decide) (by decide)
  refine ⟨n4, c1.trans (P2.steps.trans (c3.trans P4.steps)), P4.st, fun q hq => ?_, ?_, fun e he hL => ?_,
    fun x hx => by rw [P4.fr x hx, m3, P2.fr x hx, m1]⟩
  · rw [P4.regs q hq, k3 q hq, P2.regs q hq, k1 q hq]
  · exact memBytes_congr fun i hi => by
      rw [sv_o, cp4 i hi, m3, cp2 i hi, m1]
  · have h1 := hL _ (List.mem_cons_self ..)
    have h2 := hL _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    simp only at h1 h2
    rw [K4 e he (by omega), m3, K2 e he (by omega), m1]

end C3.RV32.Sv
