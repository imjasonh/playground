import C3BootProofs.Proofs.Sha384FnCall
import C3BootProofs.Proofs.LincombShiftMod12

/-!
# `sha384`: the compiled function computes SHA-384

`sha384(out, p, len)` builds a SHA-384 hasher on its stack from the
`len` bytes at `p`, finalizes a copy of it, and writes the 48-byte digest to
`out`. The proof follows the function from its entry to its return.
-/

namespace C3

open Sha512

/-- FIPS 180-4's SHA-384 digest: SHA-512's computation from SHA-384's initial
hash value over the full blocks, then the padded buffer's one or two blocks,
truncated to 48 bytes. -/
theorem sha384_eq_stream (msg : Bytes) :
    sha384 msg = (((fullBlocks5 msg ++ blocks ((padTail5 msg).length / 128) (padTail5 msg)).foldl compress
      h0384).flatMap wordBytes).take 48 := by
  have hpad : pad msg = msg.take (128 * (msg.length / 128)) ++ padTail5 msg := by
    unfold pad padTail5 tailBytes5 padZeros5
    simp only [← List.append_assoc, List.take_append_drop]
  have hA := take_full5_length msg
  have hT := padTail5_length msg
  have hP : (pad msg).length = 128 * (msg.length / 128 + (padTail5 msg).length / 128) := by
    rw [hpad, List.length_append, hA, hT]; unfold padZeros5; omega
  unfold sha384
  simp only
  rw [blocks5_fuel _ _ _ hP (by omega), hpad, blocks5_append _ _ _ _ hA, ← blocks5_take]
  rfl

end C3

namespace C3.RV32

open C3.Image

/-- The 0xD0 bytes at `S` hold the compiled SHA-384 hasher after it has
absorbed `msg`: the bytes after `msg`'s full blocks in the buffer, their
count in the buffer's last byte, the hash of the full blocks from SHA-384's
initial value, and the 128-bit count of blocks. -/
structure Hasher3At (M : Word → BitVec 8) (S : Word) (msg : Bytes) : Prop where
  hlen : msg.length < 2 ^ 32
  pos : M (S + 0x7F) = BitVec.ofNat 8 (msg.length % 128)
  buf : memBytes M S (msg.length % 128) = tailBytes5 msg
  hash : (s5Hv M (S + 0x80)).toList = (fullBlocks5 msg).foldl Sha512.compress Sha512.h0384
  lo : memLoad32 M (S + 0xC0) = BitVec.ofNat 32 (msg.length / 128)
  hi : memLoad32 M (S + 0xC4) = 0
  hi2 : memLoad32 M (S + 0xC8) = 0
  hi3 : memLoad32 M (S + 0xCC) = 0

theorem hasher3_copy {M M' : Word → BitVec 8} {S S' : Word} {h : Bytes} (H : Hasher3At M S h)
    (hc : ∀ j, j < 0xD0 → M' (S' + BitVec.ofNat 32 j) = M (S + BitVec.ofNat 32 j)) : Hasher3At M' S' h := by
  have ld : ∀ c, c + 4 ≤ 0xD0 → memLoad32 M' (S' + BitVec.ofNat 32 c) = memLoad32 M (S + BitVec.ofNat 32 c) :=
    fun c hc' => vk_ld2 fun j hj => by rw [add_ofNat_assoc, add_ofNat_assoc]; exact hc _ (by omega)
  exact ⟨H.hlen, (hc 0x7F (by decide)).trans H.pos,
    by rw [← H.buf]; unfold memBytes
       exact List.map_congr_left fun i hi => by
         rw [hc i (by have := List.mem_range.mp hi; have := Nat.mod_lt h.length (show 128 > 0 by decide); omega)],
    by rw [← H.hash]; congr 1; exact s5Hv_copy fun i hi => by
         rw [show S' + 0x80 = S' + BitVec.ofNat 32 0x80 from rfl, show S + 0x80 = S + BitVec.ofNat 32 0x80 from rfl,
           add_ofNat_assoc, add_ofNat_assoc]; exact hc _ (by omega),
    (ld 0xC0 (by decide)).trans H.lo, (ld 0xC4 (by decide)).trans H.hi, (ld 0xC8 (by decide)).trans H.hi2,
    (ld 0xCC (by decide)).trans H.hi3⟩

set_option maxRecDepth 100000 in
/-- The 64 bytes of SHA-384's initial hash value. -/
theorem hf_iv {M : Word → BitVec 8} {stp : Word}
    (h : ∀ j, j < 64 → M (stp + BitVec.ofNat 32 j) = byteAt sha384IVData j) :
    (s5Hv M stp).toList = Sha512.h0384 := by
  rw [s5Hv_copy (M := fun x => byteAt sha384IVData x.toNat) (b := 0) fun i hi => by
    rw [h i hi]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl]; congr 1; omega]
  decide

/-- The full blocks of `len` bytes at `p`. -/
theorem hf_fullBlocks (M : Word → BitVec 8) (p : Word) (len : Nat) :
    fullBlocks5 (memBytes M p len) = blockList128 M p (len / 128) := by
  unfold fullBlocks5
  rw [memBytes_length, blocks5_take, memBytes_take' (by omega), S5U.blocks128_memBytes M _ _ _ (Nat.le_refl _)]

/-- The bytes after the full blocks of `len` bytes at `p`. -/
theorem hf_tailBytes (M : Word → BitVec 8) (p : Word) (len : Nat) :
    tailBytes5 (memBytes M p len) = memBytes M (p + BitVec.ofNat 32 (128 * (len / 128))) (len % 128) := by
  unfold tailBytes5
  rw [memBytes_length]
  rw [show memBytes M p len = memBytes M p (128 * (len / 128) + len % 128) by rw [Nat.div_add_mod],
    memBytes_split, List.drop_left' (memBytes_length _ _ _)]

theorem hf_and_ff80 (x : Nat) (hx : x < 2 ^ 31) : x &&& 0x7FFFFF80 = 2 ^ 7 * (x / 2 ^ 7) :=
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

theorem hf_ff80 (len : Nat) (h : len < 2 ^ 31) :
    BitVec.ofNat 32 0x7FFFFF80 &&& BitVec.ofNat 32 len = BitVec.ofNat 32 (128 * (len / 128)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : len < 2 ^ 32), show 0x7FFFFF80 % 2 ^ 32 = 0x7FFFFF80 from rfl, Nat.and_comm,
    hf_and_ff80 _ h, Nat.mod_eq_of_lt (by omega)]

theorem hf_7f (len : Nat) : BitVec.ofNat 32 len &&& 0x7F = BitVec.ofNat 32 (len % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [and_mask_word (j := 7) rfl, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide),
    Nat.mod_eq_of_lt (by omega : len % 128 < 2 ^ 32)]

theorem hf_ext8 (x : Nat) : (BitVec.ofNat 32 x).extractLsb' 0 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  rw [byte_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.pow_zero, Nat.div_one,
    Nat.mod_mod_of_dvd _ (by decide)]

theorem hf_srl7 (len : Nat) (h : len < 2 ^ 32) :
    aluEval .srl (BitVec.ofNat 32 len) 0x7 = BitVec.ofNat 32 (len / 128) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 len >>> ((0x7 : Word).toNat % 32)).toNat = _
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    show (0x7 : Word).toNat % 32 = 7 from rfl, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem hf_ofNat_eq_zero {n : Nat} (h : n < 2 ^ 32) (e : BitVec.ofNat 32 n = 0) : n = 0 := by
  have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this; exact this

section
variable {M0 Ms : Word → BitVec 8} {F out p : Word} {len : Nat} {r0 : Fin 32 → Word}

theorem HfCtx.len31 (C : HfCtx M0 F out p len) : len < 2 ^ 31 := by have := C.hp; omega

/-- A frame byte that a word store at `F + d` leaves. -/
theorem hf_sw_out (C : HfCtx M0 F out p len) {M : Word → BitVec 8} {d c : Nat} {v : Word} (hd : d + 4 ≤ 0x240)
    (hc : c < 0x240) (h : c < d ∨ d + 4 ≤ c) :
    memStore32 M (F + BitVec.ofNat 32 d) v (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) :=
  st32_frame (C.offs (by omega) hd (by omega))

/-- A frame byte that a byte store at `F + d` leaves. -/
theorem hf_sb_out (C : HfCtx M0 F out p len) {M : Word → BitVec 8} {d c : Nat} {v : BitVec 8} (hd : d < 0x240)
    (hc : c < 0x240) (h : c ≠ d) :
    memStore8 M (F + BitVec.ofNat 32 d) v (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) :=
  st8_frame (C.offs (by omega) (by omega) (by omega))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x32 to the branch at 0x62: the arguments moved to `s0`,
`s1`, and `s2`, the hasher's buffer count cleared, SHA-384's initial value
copied into its hash value, and its block count cleared. -/
theorem hf_init (C : HfCtx M0 F out p len) {M : Word → BitVec 8} {n : Machine} (D : HfSt M0 Ms F r0 M n 0x32)
    (ha0 : reg n a0 = out) (ha1 : reg n a1 = p) (ha2 : reg n a2 = BitVec.ofNat 32 len) :
    ∃ n' M', Steps n n' ∧ HfSt M0 Ms F r0 M' n' 0x62 ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q.val ∉ [8, 9, 18, 19] → reg n' q = reg n q) ∧
      reg n' 8 = p ∧ reg n' 9 = BitVec.ofNat 32 len ∧ reg n' 18 = out ∧ reg n' 19 = F + BitVec.ofNat 32 0x80 ∧
      reg n' a2 = BitVec.ofNat 32 (len / 128) ∧
      M' (F + BitVec.ofNat 32 0x7F) = 0 ∧ (s5Hv M' (F + BitVec.ofNat 32 0x80)).toList = Sha512.h0384 ∧
      memLoad32 M' (F + BitVec.ofNat 32 0xC0) = 0 ∧ memLoad32 M' (F + BitVec.ofNat 32 0xC4) = 0 ∧
      memLoad32 M' (F + BitVec.ofNat 32 0xC8) = 0 ∧ memLoad32 M' (F + BitVec.ofNat 32 0xCC) = 0 := by
  have z0 := D.st.zero
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x38) [.alu .add (9 : Fin 32) x0 a2, .alu .add (8 : Fin 32) x0 a1,
      .alu .add (18 : Fin 32) x0 a0]
    (blockEnd_cons' hf_at_32 rfl (blockEnd_cons' hf_at_34 rfl (blockEnd_cons' hf_at_36 rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have k1 : ∀ q : Fin 32, q.val ∉ [8, 9, 18] → reg n1 q = reg n q := fun q hq => by
    rw [hr1, evb_reg q z0 (by revert hq; revert q; decide)]
  have v19 : reg n1 9 = BitVec.ofNat 32 len := by
    rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [z0]); rw [ha2]; exact BitVec.zero_add _
  have v18 : reg n1 8 = p := by
    rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [z0]); rw [ha1]; exact BitVec.zero_add _
  have v118 : reg n1 18 = out := by
    rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [z0]); rw [ha0]; exact BitVec.zero_add _
  -- sb zero, 0x7F(sp)
  obtain ⟨n2, d2, D2, k2⟩ := D1.sb C hf_at_38 (off' := 0x3C) rfl (c := 0x7F) (by rw [D1.hsp]; rfl) (by decide)
  rw [D1.st.zero] at D2
  obtain ⟨M2, hM2, D2⟩ : ∃ M2, M2 = memStore8 M (F + BitVec.ofNat 32 0x7F) ((0 : Word).extractLsb' 0 8) ∧
    HfSt M0 Ms F r0 M2 n2 0x3C := ⟨_, rfl, D2⟩
  -- the memcpy's arguments
  obtain ⟨n3, c3, D3, hr3⟩ := D2.block C (off' := 0x4E) [.aluImm .add (19 : Fin 32) sp 0x80, .lui a1 0x3FCC4000,
      .aluImm .add a1 a1 0x430, .aluImm .add a2 x0 0x40, .alu .add a0 x0 (19 : Fin 32)]
    (blockEnd_cons' hf_at_3c rfl (blockEnd_cons' hf_at_40 rfl (blockEnd_cons' hf_at_44 rfl
      (blockEnd_cons' hf_at_48 rfl (blockEnd_cons' hf_at_4c rfl rfl)))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have z2 := D2.st.zero
  have k3 : ∀ q : Fin 32, q.val ∉ [19, 11, 12, 10] → reg n3 q = reg n2 q := fun q hq => by
    rw [hr3, evb_reg q z2 (by revert hq; revert q; decide)]
  have v319 : reg n3 19 = F + BitVec.ofNat 32 0x80 := by
    rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [k2, D1.hsp]; rfl
  have hIV : Sep (BitVec.ofNat 32 sha384IVAddress) 64 (hfG F) 0x660 := C.ro (by decide) (by decide)
  -- memcpy(sp + 0x80, IV, 64)
  obtain ⟨n4, c4, D4, k4, cp4⟩ := D3.memcpy C (d := 0x80) (N := 64) (s := BitVec.ofNat 32 sha384IVAddress)
    hf_at_4e hf_at_52 (by decide) (by decide)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [k2, D1.hsp]; exact BitVec.zero_add _)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    (by decide) (C.zS hIV) (C.fS hIV (by decide)) (by decide)
  -- srli a2, s1, 7
  obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x5A) [.aluImm .srl a2 (9 : Fin 32) 0x7] (bEnd1 hf_at_56 rfl)
    ⟨trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have z4 := D4.st.zero
  have k5 : ∀ q : Fin 32, q ≠ a2 → reg n5 q = reg n4 q := fun q hq => by
    rw [hr5, evb_reg q z4 (by revert hq; revert q; decide)]
  have r9 : reg n4 9 = BitVec.ofNat 32 len := by
    rw [k4 9 (by decide), k3 9 (by decide), k2, v19]
  have va2 : reg n5 a2 = BitVec.ofNat 32 (len / 128) := by
    rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [r9]
    exact hf_srl7 len (by have := C.len31; omega)
  -- the block count cleared
  obtain ⟨n6, d6, D6, k6⟩ := D5.sw C hf_at_5a (off' := 0x5C) rfl (c := 0xC0) (by rw [D5.hsp]; rfl) (by decide)
    (by decide)
  obtain ⟨n7, d7, D7, k7⟩ := D6.sw C hf_at_5c (off' := 0x5E) rfl (c := 0xC4) (by rw [D6.hsp]; rfl) (by decide)
    (by decide)
  obtain ⟨n8, d8, D8, k8⟩ := D7.sw C hf_at_5e (off' := 0x60) rfl (c := 0xC8) (by rw [D7.hsp]; rfl) (by decide)
    (by decide)
  obtain ⟨n9, d9, D9, k9⟩ := D8.sw C hf_at_60 (off' := 0x62) rfl (c := 0xCC) (by rw [D8.hsp]; rfl) (by decide)
    (by decide)
  simp only [k8, k7, k6, D5.st.zero] at D9
  have kk : ∀ q, reg n9 q = reg n5 q := fun q => by rw [k9, k8, k7, k6]
  -- the frame bytes
  have m4 : ∀ c, c < 0x240 → n4.mem (F + BitVec.ofNat 32 c) =
      copyBytes M2 (F + BitVec.ofNat 32 0x80) (BitVec.ofNat 32 sha384IVAddress) 64 (F + BitVec.ofNat 32 c) :=
    fun c hc => cp4 _ (C.zF (c := c) (l := 1) (by omega))
  have st : ∀ c, c < 0x240 → (c < 0xC0 ∨ 0xD0 ≤ c) →
      memStore32 (memStore32 (memStore32 (memStore32 n4.mem (F + BitVec.ofNat 32 0xC0) 0) (F + BitVec.ofNat 32 0xC4) 0)
        (F + BitVec.ofNat 32 0xC8) 0) (F + BitVec.ofNat 32 0xCC) 0 (F + BitVec.ofNat 32 c) =
        n4.mem (F + BitVec.ofNat 32 c) := fun c hc h => by
    rw [hf_sw_out C (by decide) hc (by omega), hf_sw_out C (by decide) hc (by omega),
      hf_sw_out C (by decide) hc (by omega), hf_sw_out C (by decide) hc (by omega)]
  have ivc : CodeIn M2 (BitVec.ofNat 32 sha384IVAddress) sha384IVData := D2.codeRo C C.env.iv (by decide) (by decide)
  refine ⟨n9, _, c1.trans ((Steps.single d2).trans (c3.trans (c4.trans (c5.trans ((Steps.single d6).trans
    ((Steps.single d7).trans ((Steps.single d8).trans (Steps.single d9)))))))), D9, fun q hq hn => ?_,
    by rw [kk, k5 _ (by decide), k4 8 (by decide), k3 8 (by decide), k2, v18],
    by rw [kk, k5 _ (by decide), r9],
    by rw [kk, k5 _ (by decide), k4 18 (by decide), k3 18 (by decide), k2, v118],
    by rw [kk, k5 _ (by decide), k4 19 (by decide), v319],
    by rw [kk, va2], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kk, k5 q (by revert hn; revert hq; revert q; decide), k4 q hq, k3 q (by revert hn; revert hq; revert q; decide),
      k2, k1 q (by revert hn; revert hq; revert q; decide)]
  · rw [st _ (by decide) (Or.inl (by decide)), m4 _ (by decide),
      copyBytes_sep (C.offs (Or.inr (by decide)) (by decide) (by decide)) (Nat.le_refl _), hM2, memStore8_same]; rfl
  · refine hf_iv fun j hj => ?_
    rw [add_ofNat_assoc, st _ (by omega) (Or.inl (by omega)), m4 _ (by omega), ← add_ofNat_assoc,
      copyBytes_in hj (by decide)]
    exact ivc j (by rw [show sha384IVData.length = 64 by decide +kernel]; exact hj)
  · rw [memLoad32_store32_sep (C.offs (c := 0xcc) (d := 0xc0) (by decide) (by decide) (by decide)), memLoad32_store32_sep (C.offs (c := 0xc8) (d := 0xc0) (by decide) (by decide) (by decide)), memLoad32_store32_sep (C.offs (c := 0xc4) (d := 0xc0) (by decide) (by decide) (by decide)), memLoad32_store32_same]
  · rw [memLoad32_store32_sep (C.offs (c := 0xcc) (d := 0xc4) (by decide) (by decide) (by decide)), memLoad32_store32_sep (C.offs (c := 0xc8) (d := 0xc4) (by decide) (by decide) (by decide)), memLoad32_store32_same]
  · rw [memLoad32_store32_sep (C.offs (c := 0xcc) (d := 0xc8) (by decide) (by decide) (by decide)), memLoad32_store32_same]
  · rw [memLoad32_store32_same]

theorem hf_cp_in (C : HfCtx M0 F out p len) {Mn M : Word → BitVec 8} {d N : Nat} {s : Word}
    (cp : ∀ x, Sep (hfG F) 0x420 x 1 → Mn x = copyBytes M (F + BitVec.ofNat 32 d) s N x) (hd : d + N ≤ 0x240)
    {i : Nat} (hi : i < N) : Mn (F + BitVec.ofNat 32 (d + i)) = M (s + BitVec.ofNat 32 i) := by
  rw [cp _ (C.zF (l := 1) (by omega)), ← add_ofNat_assoc, copyBytes_in hi (by omega)]

theorem hf_cp_out (C : HfCtx M0 F out p len) {Mn M : Word → BitVec 8} {d N : Nat} {s : Word}
    (cp : ∀ x, Sep (hfG F) 0x420 x 1 → Mn x = copyBytes M (F + BitVec.ofNat 32 d) s N x) (hd : d + N ≤ 0x240)
    {c : Nat} (hc : c < 0x240) (h : c < d ∨ d + N ≤ c) : Mn (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  rw [cp _ (C.zF (l := 1) (by omega)), copyBytes_sep (C.offs (by omega) hd (by omega)) (Nat.le_refl _)]

theorem hf_ld {Mn M : Word → BitVec 8} {a : Nat}
    (h : ∀ c, a ≤ c → c < a + 4 → Mn (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c)) :
    memLoad32 Mn (F + BitVec.ofNat 32 a) = memLoad32 M (F + BitVec.ofNat 32 a) :=
  memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h _ (by omega) (by omega)

theorem hf_hv {Mn M : Word → BitVec 8} {a : Nat}
    (h : ∀ c, a ≤ c → c < a + 64 → Mn (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c)) :
    s5Hv Mn (F + BitVec.ofNat 32 a) = s5Hv M (F + BitVec.ofNat 32 a) :=
  s5Hv_congr fun j hj => by rw [add_ofNat_assoc]; exact h _ (by omega) (by omega)

theorem hf_cnt (F : Word) : F + BitVec.ofNat 32 0x80 + 0x40 = F + BitVec.ofNat 32 0xC0 := by
  rw [BitVec.add_assoc]; rfl
theorem hf_cnt1 (F : Word) : F + BitVec.ofNat 32 0x80 + 0x44 = F + BitVec.ofNat 32 0xC4 := by
  rw [BitVec.add_assoc]; rfl
theorem hf_cnt2 (F : Word) : F + BitVec.ofNat 32 0x80 + 0x48 = F + BitVec.ofNat 32 0xC8 := by
  rw [BitVec.add_assoc]; rfl
theorem hf_cnt3 (F : Word) : F + BitVec.ofNat 32 0x80 + 0x4C = F + BitVec.ofNat 32 0xCC := by
  rw [BitVec.add_assoc]; rfl

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
/-- From the branch at 0x62 to 0xA8: the hasher at `F` has absorbed the
`len` bytes at `p`. -/
theorem hf_absorb (C : HfCtx M0 F out p len) {M : Word → BitVec 8} {n : Machine} (D : HfSt M0 Ms F r0 M n 0x62)
    (h8 : reg n 8 = p) (h9 : reg n 9 = BitVec.ofNat 32 len) (h19 : reg n 19 = F + BitVec.ofNat 32 0x80)
    (ha2 : reg n a2 = BitVec.ofNat 32 (len / 128))
    (hv : (s5Hv M (F + BitVec.ofNat 32 0x80)).toList = Sha512.h0384)
    (c0 : memLoad32 M (F + BitVec.ofNat 32 0xC0) = 0) (c1 : memLoad32 M (F + BitVec.ofNat 32 0xC4) = 0)
    (c2 : memLoad32 M (F + BitVec.ofNat 32 0xC8) = 0) (c3 : memLoad32 M (F + BitVec.ofNat 32 0xCC) = 0) :
    ∃ n', Steps n n' ∧ HfSt M0 Ms F r0 n'.mem n' 0xA8 ∧ reg n' 18 = reg n 18 ∧
      Hasher3At n'.mem F (memBytes M0 p len) := by
  have hl := C.len31
  have hp := C.hp
  have hml : (memBytes M0 p len).length = len := memBytes_length _ _ _
  have pS : ∀ i, i < len → Sep (hfG F) 0x660 (p + BitVec.ofNat 32 i) 1 := fun i hi =>
    (C.sP.sub (c := i) (l := 1) (by omega)).symm
  by_cases hz : len / 128 = 0
  · have hl128 : len < 128 := by omega
    obtain ⟨n1, d1, u1⟩ := D.st.taken (D.code C) 0x96 hf_at_62 (by decide) (by rw [ha2, D.st.zero, hz]; rfl)
    have D1 := D.jmp u1
    obtain ⟨n2, c2', D2, hr2⟩ := D1.block C (off' := 0x9C) [.alu .add a0 x0 sp, .alu .add a1 x0 (8 : Fin 32),
        .alu .add a2 x0 (9 : Fin 32)]
      (blockEnd_cons' hf_at_96 rfl (blockEnd_cons' hf_at_98 rfl (blockEnd_cons' hf_at_9a rfl rfl)))
      ⟨trivial, trivial, trivial, trivial⟩ rfl
      (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    have z1 := D1.st.zero
    have sP0 : Sep p len (hfG F) 0x660 := C.sP
    obtain ⟨n3, c3', D3, k3, cp3⟩ := D2.memcpy C (d := 0) (N := len) (s := p) hf_at_9c hf_at_a0 (by decide) (by decide)
      (by rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; simp only [u1.regs, D.st.zero, D.hsp]
          exact (BitVec.zero_add _).trans (add_ofNat_zero F).symm)
      (by rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; simp only [u1.regs, h8]; exact BitVec.zero_add _)
      (by rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; simp only [u1.regs, h9]; exact BitVec.zero_add _)
      (by omega) (C.zS sP0) (C.fS sP0 (by omega)) (by omega)
    obtain ⟨n4, d4, D4, k4⟩ := D3.sb C hf_at_a4 (off' := 0xA8) rfl (c := 0x7F) (by rw [D3.hsp]; rfl) (by decide)
    have r9 : reg n3 9 = BitVec.ofNat 32 len := by
      rw [k3 9 (by decide), hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; simp only [u1.regs, h9]
    rw [r9, hf_ext8] at D4
    have m4 := D4.st.mem
    refine ⟨n4, (Steps.single d1).trans (c2'.trans (c3'.trans (Steps.single d4))), by rw [m4]; exact D4, ?_, ?_⟩
    · rw [k4, k3 18 (by decide), hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; exact u1.regs 18
    rw [m4]
    have mb : ∀ c, c < 0x240 → c ≠ 0x7F → len ≤ c →
        memStore8 n3.mem (F + BitVec.ofNat 32 0x7F) (BitVec.ofNat 8 len) (F + BitVec.ofNat 32 c) =
          M (F + BitVec.ofNat 32 c) := fun c hc h1 h2 => by
      rw [hf_sb_out C (by decide) hc h1, hf_cp_out C cp3 (by omega) hc (Or.inr (by omega))]
    refine ⟨by rw [hml]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show memStore8 n3.mem (F + BitVec.ofNat 32 0x7F) _ (F + BitVec.ofNat 32 0x7F) = _
      rw [memStore8_same, hml, Nat.mod_eq_of_lt hl128]
    · rw [hml, hf_tailBytes, hz, Nat.mul_zero, add_ofNat_zero, Nat.mod_eq_of_lt hl128]
      unfold memBytes
      refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi
      have e := hf_cp_in C cp3 (d := 0) (by omega) hi
      rw [Nat.zero_add] at e
      rw [hf_sb_out C (by decide) (by omega) (by omega), e, D.agree _ (pS i hi)]
    · show (s5Hv _ (F + BitVec.ofNat 32 0x80)).toList = _
      rw [hf_hv (M := M) fun c h1 h2 => mb c (by omega) (by omega) (by omega), hv, hf_fullBlocks, hz]; rfl
    · show memLoad32 _ (F + BitVec.ofNat 32 0xC0) = _
      rw [hf_ld (M := M) fun c h1 h2 => mb c (by omega) (by omega) (by omega), c0, hml, hz]; rfl
    · show memLoad32 _ (F + BitVec.ofNat 32 0xC4) = _
      rw [hf_ld (M := M) fun c h1 h2 => mb c (by omega) (by omega) (by omega), c1]
    · show memLoad32 _ (F + BitVec.ofNat 32 0xC8) = _
      rw [hf_ld (M := M) fun c h1 h2 => mb c (by omega) (by omega) (by omega), c2]
    · show memLoad32 _ (F + BitVec.ofNat 32 0xCC) = _
      rw [hf_ld (M := M) fun c h1 h2 => mb c (by omega) (by omega) (by omega), c3]
  · have hne : BitVec.ofNat 32 (len / 128) ≠ 0 := fun e => hz (hf_ofNat_eq_zero (by omega) e)
    obtain ⟨n1, d1, u1⟩ := D.st.notTaken (D.code C) 0x64 hf_at_62 (by decide)
      (by rw [ha2, D.st.zero]; simp [branchTaken]; exact hne)
    have D1 := D.jmp u1
    obtain ⟨n2, c2', D2, hr2⟩ := D1.block C (off' := 0x7A) [.lui a0 0x80000000, .aluImm .add a0 a0 0xFFFFFF80,
        .alu .and a0 a0 (9 : Fin 32), .aluImm .and (9 : Fin 32) (9 : Fin 32) 0x7F,
        .alu .add (20 : Fin 32) (8 : Fin 32) a0, .alu .add a0 x0 (19 : Fin 32), .alu .add a1 x0 (8 : Fin 32)]
      (blockEnd_cons' hf_at_64 rfl (blockEnd_cons' hf_at_68 rfl (blockEnd_cons' hf_at_6c rfl
        (blockEnd_cons' hf_at_6e rfl (blockEnd_cons' hf_at_72 rfl (blockEnd_cons' hf_at_76 rfl
          (blockEnd_cons' hf_at_78 rfl rfl)))))))
      ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
      (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    have v9 : reg n2 9 = BitVec.ofNat 32 (len % 128) := by
      rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; simp only [u1.regs, h9]; exact hf_7f len
    have v20 : reg n2 20 = p + BitVec.ofNat 32 (128 * (len / 128)) := by
      rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; simp only [u1.regs, h9, h8]
      show p + (BitVec.ofNat 32 0x7FFFFF80 &&& BitVec.ofNat 32 len) = _
      rw [hf_ff80 len hl]
    have v18 : reg n2 18 = reg n 18 := by
      rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; exact u1.regs 18
    have sB : Sep p (128 * (len / 128)) (hfG F) 0x660 := by
      have := C.sP.sub (c := 0) (l := 128 * (len / 128)) (by omega); rwa [add_ofNat_zero] at this
    obtain ⟨n3, c3', D3, k3, hv3, cn0, cn1, cn2, cn3, f3⟩ := D2.blocks C (s := 0x80) (nb := len / 128) (bp := p)
      hf_at_7a hf_at_7e (by decide) (by decide)
      (by rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; simp only [u1.regs, h19]
          exact BitVec.zero_add _)
      (by rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; simp only [u1.regs, h8]
          exact BitVec.zero_add _)
      (by rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; simp only [u1.regs, ha2])
      (by decide) (by decide) (by rw [hf_cnt, c0]; show 0 + len / 128 < 2 ^ 32; omega) sB (by omega)
    obtain ⟨n4, d4, D4, k4⟩ := D3.sb C hf_at_82 (off' := 0x86) rfl (c := 0x7F) (by rw [D3.hsp]; rfl) (by decide)
    rw [k3 9 (by decide), v9, hf_ext8] at D4
    obtain ⟨M4, hM4, D4⟩ : ∃ M4, M4 = memStore8 n3.mem (F + BitVec.ofNat 32 0x7F) (BitVec.ofNat 8 (len % 128)) ∧
      HfSt M0 Ms F r0 M4 n4 0x86 := ⟨_, rfl, D4⟩
    obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x8C) [.alu .add a0 x0 sp, .alu .add a1 x0 (20 : Fin 32),
        .alu .add a2 x0 (9 : Fin 32)]
      (blockEnd_cons' hf_at_86 rfl (blockEnd_cons' hf_at_88 rfl (blockEnd_cons' hf_at_8a rfl rfl)))
      ⟨trivial, trivial, trivial, trivial⟩ rfl
      (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    have sT : Sep (p + BitVec.ofNat 32 (128 * (len / 128))) (len % 128) (hfG F) 0x660 :=
      C.sP.sub (by omega)
    obtain ⟨n6, c6, D6, k6, cp6⟩ := D5.memcpy C (d := 0) (N := len % 128)
      (s := p + BitVec.ofNat 32 (128 * (len / 128))) hf_at_8c hf_at_90 (by decide) (by decide)
      (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; simp only [k4, D3.st.zero, D3.hsp]
          exact (BitVec.zero_add _).trans (add_ofNat_zero F).symm)
      (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; simp only [k4, k3 20 (by decide), v20]
          exact BitVec.zero_add _)
      (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; simp only [k4, k3 9 (by decide), v9]
          exact BitVec.zero_add _)
      (by omega) (C.zS sT) (C.fS sT (by omega))
      (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    obtain ⟨n7, d7, u7⟩ := D6.st.jump (D6.code C) hf_at_94 (off' := 0xA8) (by decide) (by rw [D6.st.pc]; decide)
    have D7 := D6.jmp u7
    have m7 : n7.mem = n6.mem := u7.mem
    refine ⟨n7, (Steps.single d1).trans (c2'.trans (c3'.trans ((Steps.single d4).trans (c5.trans
      (c6.trans (Steps.single d7)))))), by rw [m7]; exact D7, ?_, ?_⟩
    · rw [u7.regs, k6 18 (by decide), hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
      rw [k4, k3 18 (by decide), v18]
    rw [m7]
    have mb : ∀ c, c < 0x240 → c ≠ 0x7F → len % 128 ≤ c →
        n6.mem (F + BitVec.ofNat 32 c) = n3.mem (F + BitVec.ofNat 32 c) := fun c hc h1 h2 => by
      rw [hf_cp_out C cp6 (by omega) hc (Or.inr (by omega)), hM4, hf_sb_out C (by decide) hc h1]
    have mh : ∀ c, 0x80 ≤ c → c < 0xD0 → n6.mem (F + BitVec.ofNat 32 c) = n3.mem (F + BitVec.ofNat 32 c) :=
      fun c h1 h2 => mb c (by omega) (by omega) (by omega)
    refine ⟨by rw [hml]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show n6.mem (F + BitVec.ofNat 32 0x7F) = _
      rw [hf_cp_out C cp6 (by omega) (by decide) (Or.inr (by omega)), hM4, memStore8_same, hml]
    · rw [hml, hf_tailBytes]
      unfold memBytes
      refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi
      have e := hf_cp_in C cp6 (d := 0) (by omega) hi
      rw [Nat.zero_add] at e
      rw [e, add_ofNat_assoc, D4.agree _ (pS _ (by omega))]
    · show (s5Hv _ (F + BitVec.ofNat 32 0x80)).toList = _
      rw [hf_hv (M := n3.mem) fun c h1 h2 => mh c h1 (by omega), hv3, hv,
        S5U.blockList128_congr (M := M0) fun i hi => D.agree _ (pS i (by omega)), hf_fullBlocks]
    · show memLoad32 _ (F + BitVec.ofNat 32 0xC0) = _
      rw [hf_ld (M := n3.mem) fun c h1 h2 => mh c (by omega) (by omega), ← hf_cnt, cn0, hf_cnt, c0, hml]
      exact BitVec.zero_add _
    · show memLoad32 _ (F + BitVec.ofNat 32 0xC4) = _
      rw [hf_ld (M := n3.mem) fun c h1 h2 => mh c (by omega) (by omega), ← hf_cnt1, cn1, hf_cnt1, c1]
    · show memLoad32 _ (F + BitVec.ofNat 32 0xC8) = _
      rw [hf_ld (M := n3.mem) fun c h1 h2 => mh c (by omega) (by omega), ← hf_cnt2, cn2, hf_cnt2, c2]
    · show memLoad32 _ (F + BitVec.ofNat 32 0xCC) = _
      rw [hf_ld (M := n3.mem) fun c h1 h2 => mh c (by omega) (by omega), ← hf_cnt3, cn3, hf_cnt3, c3]

/-- A frame byte outside a fill of the frame. -/
theorem hf_fb_out (C : HfCtx M0 F out p len) {M : Word → BitVec 8} {d N c : Nat} {v : BitVec 8} (hd : d + N ≤ 0x240)
    (hc : c < 0x240) (h : c < d ∨ d + N ≤ c) :
    fillBytes M (F + BitVec.ofNat 32 d) v N (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) :=
  fillBytes_sep (C.offs (by omega) hd (by omega)) (Nat.le_refl _)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
/-- From 0xA8 to 0xD6: the hasher copied to `F + 0xD0`, the two digest
buffers cleared, and the finalization's pointers set. -/
theorem hf_copy (C : HfCtx M0 F out p len) {M : Word → BitVec 8} {n : Machine} (D : HfSt M0 Ms F r0 M n 0xA8)
    {h : Bytes} (H : Hasher3At M F h) :
    ∃ n', Steps n n' ∧ HfSt M0 Ms F r0 n'.mem n' 0xD6 ∧ reg n' 18 = reg n 18 ∧
      reg n' 20 = F + BitVec.ofNat 32 0xD0 ∧ reg n' 26 = F + BitVec.ofNat 32 0x150 ∧
      reg n' 8 = F + BitVec.ofNat 32 0x1D0 ∧ Hasher3At n'.mem (F + BitVec.ofNat 32 0xD0) h := by
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0xB4) [.aluImm .add a0 sp 0xD0, .alu .add a1 x0 sp,
      .aluImm .add a2 x0 0xD0, .aluImm .add (20 : Fin 32) sp 0xD0]
    (blockEnd_cons' hf_at_a8 rfl (blockEnd_cons' hf_at_aa rfl (blockEnd_cons' hf_at_ac rfl
      (blockEnd_cons' hf_at_b0 rfl rfl))))
    ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have z0 := D.st.zero
  obtain ⟨n2, c2, D2, k2, cp2⟩ := D1.memcpy C (d := 0xD0) (N := 0xD0) (s := F + BitVec.ofNat 32 0)
    hf_at_b4 hf_at_b8 (by decide) (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; rfl)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]
        exact (BitVec.zero_add _).trans (add_ofNat_zero F).symm)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    (by decide) (C.zF (c := 0) (l := 0xD0) (by decide)).symm
    (C.offs (c := 0xD0) (n := 0xD0) (d := 0) (k := 0xD0) (Or.inr (by decide)) (by decide) (by decide))
    (by rw [C.fN (by decide)]; have := C.hhi; omega)
  have v20 : reg n2 20 = F + BitVec.ofNat 32 0xD0 := by
    rw [k2 20 (by decide), hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; rfl
  have v18 : reg n2 18 = reg n 18 := by
    rw [k2 18 (by decide), hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
  obtain ⟨n3, c3, D3, hr3⟩ := D2.block C (off' := 0xBE) [.aluImm .add a0 sp 0x1A0] (bEnd1 hf_at_bc rfl)
    ⟨trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n4, c4, D4, k4, f4⟩ := D3.zero48 C (d := 0x1A0) hf_at_be hf_at_c2 (by decide) (by decide)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D2.hsp]; rfl) (by decide)
  obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0xCE) [.aluImm .add (26 : Fin 32) sp 0x150,
      .aluImm .add a0 sp 0x1D0, .aluImm .add (8 : Fin 32) sp 0x1D0]
    (blockEnd_cons' hf_at_c6 rfl (blockEnd_cons' hf_at_ca rfl (blockEnd_cons' hf_at_cc rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n6, c6, D6, k6, f6⟩ := D5.zero64 C (d := 0x1D0) hf_at_ce hf_at_d2 (by decide) (by decide)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; rfl) (by decide)
  have k35 : ∀ q : Fin 32, q.val ∈ [18, 20] → reg n6 q = reg n2 q := fun q hq => by
    rw [k6 q (by revert hq; revert q; decide), hr5,
      evb_reg q D4.st.zero (by revert hq; revert q; decide), k4 q (by revert hq; revert q; decide), hr3,
      evb_reg q D2.st.zero (by revert hq; revert q; decide)]
  refine ⟨n6, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans c6)))), D6,
    by rw [k35 18 (by decide), v18], by rw [k35 20 (by decide), v20],
    by rw [k6 26 (by decide), hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; rfl,
    by rw [k6 8 (by decide), hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; rfl, ?_⟩
  refine hasher3_copy H fun j hj => ?_
  have e := hf_cp_in C cp2 (by decide) hj
  rw [add_ofNat_assoc, Nat.zero_add] at e
  rw [add_ofNat_assoc, f6 _ (C.zF (l := 1) (by omega)), hf_fb_out C (by decide) (by omega) (Or.inl (by omega)),
    f4 _ (C.zF (l := 1) (by omega)), hf_fb_out C (by decide) (by omega) (Or.inl (by omega)), e]

theorem hf_a180 (F o c : Word) (h : BitVec.ofNat 32 0x180 + o = BitVec.ofNat 32 0xD0 + c) :
    F + BitVec.ofNat 32 0x180 + o = F + BitVec.ofNat 32 0xD0 + c := by
  rw [BitVec.add_assoc, h, ← BitVec.add_assoc]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
/-- From 0xD6 to 0x18E: the block count and the buffer's byte count loaded
from the hasher at `F + 0xD0`, the length in bits computed byte-swapped into
`s5` to `s8`, `127 - pos` into `s3`, and the buffer's next byte and 0x80
into `a0` and `a1`. -/
theorem hf_flen (C : HfCtx M0 F out p len) {M : Word → BitVec 8} {n : Machine} (D : HfSt M0 Ms F r0 M n 0xD6)
    (h20 : reg n 20 = F + BitVec.ofNat 32 0xD0) {h : Bytes} (H : Hasher3At M (F + BitVec.ofNat 32 0xD0) h) :
    ∃ n', Steps n n' ∧ HfSt M0 Ms F r0 M n' 0x18E ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q.val ∉ [19, 21, 22, 23, 24, 25] → reg n' q = reg n q) ∧
      reg n' 21 = bswap32 ((BitVec.ofNat 32 (h.length / 128) <<< 10) ||| (BitVec.ofNat 32 (h.length % 128) <<< 3)) ∧
      reg n' 22 = bswap32 (BitVec.ofNat 32 (h.length / 128) >>> 22) ∧ reg n' 23 = 0 ∧ reg n' 24 = 0 ∧
      reg n' 19 = BitVec.ofNat 32 (127 - h.length % 128) ∧ reg n' 25 = BitVec.ofNat 32 (h.length % 128) ∧
      reg n' a0 = F + BitVec.ofNat 32 (0xD0 + h.length % 128) ∧ reg n' a1 = 0x80 := by
  have z0 := D.st.zero
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0xD8) [.aluImm .add a0 sp 0x180] (bEnd1 hf_at_d6 rfl)
    ⟨trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have k1 : ∀ q : Fin 32, q ≠ a0 → reg n1 q = reg n q := fun q hq => by
    rw [hr1]; simp only [runBlock, BInstr.run]; exact upd_ne' hq z0
  have va0 : reg n1 a0 = F + BitVec.ofNat 32 0x180 := by
    rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; rfl
  have vsp : reg n1 sp = F := by rw [k1 _ (by decide), D.hsp]
  have a0o : ∀ o : Nat, F + BitVec.ofNat 32 0x180 + BitVec.ofNat 32 o = F + BitVec.ofNat 32 (0x180 + o) :=
    fun o => add_ofNat_assoc F 0x180 o
  have e1 : (reg n1 a0 + 0x18).toNat % 4 = 0 := by rw [va0, show F + BitVec.ofNat 32 0x180 + 0x18 = F + BitVec.ofNat 32 0x198 from a0o 0x18]; exact C.al (by decide)
  have e2 : (reg n1 a0 + 0x14).toNat % 4 = 0 := by rw [va0, show F + BitVec.ofNat 32 0x180 + 0x14 = F + BitVec.ofNat 32 0x194 from a0o 0x14]; exact C.al (by decide)
  have e3 : (reg n1 a0 + 0x1C).toNat % 4 = 0 := by rw [va0, show F + BitVec.ofNat 32 0x180 + 0x1C = F + BitVec.ofNat 32 0x19C from a0o 0x1C]; exact C.al (by decide)
  have e4 : (reg n1 a0 + 0x10).toNat % 4 = 0 := by rw [va0, show F + BitVec.ofNat 32 0x180 + 0x10 = F + BitVec.ofNat 32 0x190 from a0o 0x10]; exact C.al (by decide)
  obtain ⟨n2, c2, D2, hr2⟩ := D1.block C (off' := 0x18E)
    ((.lw (23 : Fin 32) a0 0x18) :: (.lw a2 a0 0x14) :: (.lw (17 : Fin 32) a0 0x1C) :: (.lw a4 a0 0x10) :: (.lbu (25 : Fin 32) sp 0x14F) :: (.aluImm .srl a6 (23 : Fin 32) 0x16) :: (.aluImm .sll (5 : Fin 32) (17 : Fin 32) 0xA) :: (.aluImm .srl (6 : Fin 32) a2 0x16) :: (.aluImm .sll (7 : Fin 32) (23 : Fin 32) 0xA) :: (.aluImm .srl (31 : Fin 32) a4 0x16) :: (.aluImm .sll a3 a2 0xA) :: (.alu .or (28 : Fin 32) (5 : Fin 32) a6) :: (.alu .or (29 : Fin 32) (7 : Fin 32) (6 : Fin 32)) :: (.alu .or (30 : Fin 32) a3 (31 : Fin 32)) :: (.aluImm .sll a5 a4 0xA) :: (.aluImm .sll a0 (25 : Fin 32) 0x3) :: (.alu .or a0 a0 a5) :: (.lui (19 : Fin 32) 0x10000) :: (.aluImm .sll a4 a4 0x2) :: (.aluImm .add a1 (19 : Fin 32) 0xFFFFFF00) :: (.alu .and a4 a4 a1) :: (.aluImm .srl a5 a5 0x18) :: (.alu .or a4 a4 a5) :: (.alu .and a0 a0 a1) :: (.aluImm .sll a0 a0 0x8) :: (.aluImm .sll a5 (25 : Fin 32) 0x1B) :: (.alu .or a4 a4 a5) :: (.aluImm .sll a2 a2 0x2) :: (.alu .and a2 a2 a1) :: (.aluImm .srl a3 a3 0x18) :: (.alu .or (21 : Fin 32) a4 a0) :: (.alu .or a2 a2 a3) :: (.alu .and a0 (30 : Fin 32) a1) :: (.aluImm .sll (31 : Fin 32) (31 : Fin 32) 0x18) :: (.aluImm .sll a0 a0 0x8) :: (.alu .or a2 (31 : Fin 32) a2) :: (.alu .or (22 : Fin 32) a2 a0) :: (.aluImm .sll (23 : Fin 32) (23 : Fin 32) 0x2) :: (.alu .and a0 (23 : Fin 32) a1) :: (.aluImm .srl a2 (7 : Fin 32) 0x18) :: (.alu .or a0 a0 a2) :: (.alu .and a2 (29 : Fin 32) a1) :: (.aluImm .sll a2 a2 0x8) :: (.aluImm .sll (6 : Fin 32) (6 : Fin 32) 0x18) :: (.alu .or a0 (6 : Fin 32) a0) :: (.aluImm .sll (17 : Fin 32) (17 : Fin 32) 0x2) :: (.alu .and a3 (17 : Fin 32) a1) :: (.aluImm .srl a4 (5 : Fin 32) 0x18) :: (.alu .or (23 : Fin 32) a0 a2) :: (.alu .or a3 a3 a4) :: (.alu .and a0 (28 : Fin 32) a1) :: (.aluImm .sll a6 a6 0x18) :: (.aluImm .sll a0 a0 0x8) :: (.alu .or a1 a6 a3) :: (.alu .or (24 : Fin 32) a1 a0) :: (.aluImm .xor (19 : Fin 32) (25 : Fin 32) 0x7F) :: (.alu .add a0 (20 : Fin 32) (25 : Fin 32)) :: (.aluImm .add a1 x0 0x80) :: [])
    (blockEnd_cons' (off' := 0xDC) hf_at_d8 rfl (blockEnd_cons' (off' := 0xDE) hf_at_dc rfl (blockEnd_cons' (off' := 0xE2) hf_at_de rfl (blockEnd_cons' (off' := 0xE4) hf_at_e2 rfl (blockEnd_cons' (off' := 0xE8) hf_at_e4 rfl (blockEnd_cons' (off' := 0xEC) hf_at_e8 rfl (blockEnd_cons' (off' := 0xF0) hf_at_ec rfl (blockEnd_cons' (off' := 0xF4) hf_at_f0 rfl (blockEnd_cons' (off' := 0xF8) hf_at_f4 rfl (blockEnd_cons' (off' := 0xFC) hf_at_f8 rfl (blockEnd_cons' (off' := 0x100) hf_at_fc rfl (blockEnd_cons' (off' := 0x104) hf_at_100 rfl (blockEnd_cons' (off' := 0x108) hf_at_104 rfl (blockEnd_cons' (off' := 0x10C) hf_at_108 rfl (blockEnd_cons' (off' := 0x110) hf_at_10c rfl (blockEnd_cons' (off' := 0x114) hf_at_110 rfl (blockEnd_cons' (off' := 0x116) hf_at_114 rfl (blockEnd_cons' (off' := 0x118) hf_at_116 rfl (blockEnd_cons' (off' := 0x11A) hf_at_118 rfl (blockEnd_cons' (off' := 0x11E) hf_at_11a rfl (blockEnd_cons' (off' := 0x120) hf_at_11e rfl (blockEnd_cons' (off' := 0x122) hf_at_120 rfl (blockEnd_cons' (off' := 0x124) hf_at_122 rfl (blockEnd_cons' (off' := 0x126) hf_at_124 rfl (blockEnd_cons' (off' := 0x128) hf_at_126 rfl (blockEnd_cons' (off' := 0x12C) hf_at_128 rfl (blockEnd_cons' (off' := 0x12E) hf_at_12c rfl (blockEnd_cons' (off' := 0x130) hf_at_12e rfl (blockEnd_cons' (off' := 0x132) hf_at_130 rfl (blockEnd_cons' (off' := 0x134) hf_at_132 rfl (blockEnd_cons' (off' := 0x138) hf_at_134 rfl (blockEnd_cons' (off' := 0x13A) hf_at_138 rfl (blockEnd_cons' (off' := 0x13E) hf_at_13a rfl (blockEnd_cons' (off' := 0x140) hf_at_13e rfl (blockEnd_cons' (off' := 0x142) hf_at_140 rfl (blockEnd_cons' (off' := 0x146) hf_at_142 rfl (blockEnd_cons' (off' := 0x14A) hf_at_146 rfl (blockEnd_cons' (off' := 0x14C) hf_at_14a rfl (blockEnd_cons' (off' := 0x150) hf_at_14c rfl (blockEnd_cons' (off' := 0x154) hf_at_150 rfl (blockEnd_cons' (off' := 0x156) hf_at_154 rfl (blockEnd_cons' (off' := 0x15A) hf_at_156 rfl (blockEnd_cons' (off' := 0x15C) hf_at_15a rfl (blockEnd_cons' (off' := 0x15E) hf_at_15c rfl (blockEnd_cons' (off' := 0x162) hf_at_15e rfl (blockEnd_cons' (off' := 0x164) hf_at_162 rfl (blockEnd_cons' (off' := 0x168) hf_at_164 rfl (blockEnd_cons' (off' := 0x16C) hf_at_168 rfl (blockEnd_cons' (off' := 0x170) hf_at_16c rfl (blockEnd_cons' (off' := 0x172) hf_at_170 rfl (blockEnd_cons' (off' := 0x176) hf_at_172 rfl (blockEnd_cons' (off' := 0x178) hf_at_176 rfl (blockEnd_cons' (off' := 0x17A) hf_at_178 rfl (blockEnd_cons' (off' := 0x17E) hf_at_17a rfl (blockEnd_cons' (off' := 0x182) hf_at_17e rfl (blockEnd_cons' (off' := 0x186) hf_at_182 rfl (blockEnd_cons' (off' := 0x18A) hf_at_186 rfl (blockEnd_cons' (off' := 0x18E) hf_at_18a rfl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (by simp +decide only [BlockOk, BInstr.ok, BInstr.run, upd, ↓reduceIte, and_true]
        exact ⟨e1, e2, e3, e4⟩)
    rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have hlo : memLoad32 M (F + BitVec.ofNat 32 0x180 + 0x10) = BitVec.ofNat 32 (h.length / 128) := by
    rw [hf_a180 F 0x10 0xC0 rfl]; exact H.lo
  have hhi : memLoad32 M (F + BitVec.ofNat 32 0x180 + 0x14) = 0 := by
    rw [hf_a180 F 0x14 0xC4 rfl]; exact H.hi
  have hhi2 : memLoad32 M (F + BitVec.ofNat 32 0x180 + 0x18) = 0 := by
    rw [hf_a180 F 0x18 0xC8 rfl]; exact H.hi2
  have hhi3 : memLoad32 M (F + BitVec.ofNat 32 0x180 + 0x1C) = 0 := by
    rw [hf_a180 F 0x1C 0xCC rfl]; exact H.hi3
  have hpos : M (F + 0x14F) = BitVec.ofNat 8 (h.length % 128) := by
    rw [show F + 0x14F = F + BitVec.ofNat 32 0xD0 + 0x7F by rw [BitVec.add_assoc]; rfl]; exact H.pos
  have hp : h.length % 128 < 128 := Nat.mod_lt _ (by decide)
  have hz : BitVec.zeroExtend 32 (BitVec.ofNat 8 (h.length % 128)) = BitVec.ofNat 32 (h.length % 128) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hpb : ∀ k, 7 ≤ k → (BitVec.ofNat 32 (h.length % 128)).getLsbD k = false := fun k hk =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by rw [BitVec.toNat_ofNat]; omega)
      (Nat.pow_le_pow_right (by decide) hk : 2 ^ 7 ≤ 2 ^ k))
  have g21 : reg n2 21 = bswap32 ((BitVec.ofNat 32 (h.length / 128) <<< 10) ||| (BitVec.ofNat 32 (h.length % 128) <<< 3)) := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [va0, vsp, hlo, hpos, hz]
    exact lenLo5_eq _ _ hpb
  have g22 : reg n2 22 = bswap32 (BitVec.ofNat 32 (h.length / 128) >>> 22) := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [va0, hlo, hhi]
    exact lenHi5_eq _
  have g23 : reg n2 23 = 0 := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [va0, hhi2, hhi]; rfl
  have g24 : reg n2 24 = 0 := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [va0, hhi3, hhi2]; rfl
  have g25 : reg n2 25 = BitVec.ofNat 32 (h.length % 128) := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [vsp, hpos, hz]
  have g19 : reg n2 19 = BitVec.ofNat 32 (127 - h.length % 128) := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [vsp, hpos, hz]
    show BitVec.ofNat 32 (h.length % 128) ^^^ 0x7F = _
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : h.length % 128 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : 127 - h.length % 128 < 2 ^ 32), show (0x7F : Word).toNat = 127 from rfl]
    exact xor127 _ hp
  have ga0 : reg n2 a0 = F + BitVec.ofNat 32 (0xD0 + h.length % 128) := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [vsp, hpos, hz, k1 20 (by decide), h20]; exact add_ofNat_assoc F _ _
  have ga1 : reg n2 a1 = 0x80 := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
  refine ⟨n2, c1.trans c2, D2, fun q hq hn => ?_, g21, g22, g23, g24, g19, g25, ga0, ga1⟩
  rw [hr2, evb_reg q D1.st.zero (by revert hn; revert hq; revert q; decide), k1 q (by revert hq; revert q; decide)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x18E: the buffer padded with 0x80 and zeros, and, when
fewer than 16 bytes are left for the length, compressed and cleared. After
it, storing the length in the buffer's last 16 bytes and compressing gives
the hash value of the padded message. -/
theorem hf_fpad (C : HfCtx M0 F out p len) {M : Word → BitVec 8} {n : Machine} (D : HfSt M0 Ms F r0 M n 0x18E)
    {h : Bytes} (H : Hasher3At M (F + BitVec.ofNat 32 0xD0) h)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 (0xD0 + h.length % 128)) (ha1 : reg n a1 = 0x80)
    (h19 : reg n 19 = BitVec.ofNat 32 (127 - h.length % 128)) (h26 : reg n 26 = F + BitVec.ofNat 32 0x150) :
    ∃ n' M', Steps n n' ∧ HfSt M0 Ms F r0 M' n' 0x1C2 ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      (fullBlocks5 h ++ Sha512.blocks ((padTail5 h).length / 128) (padTail5 h)).foldl Sha512.compress Sha512.h0384 =
        Sha512.compress (s5Hv M' (F + BitVec.ofNat 32 0x150)).toList
          (memBytes M' (F + BitVec.ofNat 32 0xD0) 112 ++ Sha512.be128 (8 * h.length)) ∧
      ∀ c, c < 0x240 → (c < 0xD0 ∨ 0x190 ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  have hp : h.length % 128 < 128 := Nat.mod_lt _ (by decide)
  have S0 : ∀ o : Nat, F + BitVec.ofNat 32 0xD0 + BitVec.ofNat 32 o = F + BitVec.ofNat 32 (0xD0 + o) :=
    fun o => add_ofNat_assoc F 0xD0 o
  -- sb a1, 0(a0)
  obtain ⟨n1, d1, D1, k1⟩ := D.sb C hf_at_18e (off' := 0x192) rfl (c := 0xD0 + h.length % 128)
    (by rw [ha0]; exact BitVec.add_zero _) (by omega)
  rw [ha1] at D1
  -- addi a0, a0, 1; li a1, 0; mv a2, s2; memset
  obtain ⟨n2, c2, D2, hr2⟩ := D1.block C (off' := 0x198)
    [.aluImm .add a0 a0 0x1, .aluImm .add a1 x0 0x0, .alu .add a2 x0 (19 : Fin 32)]
    (blockEnd_cons' hf_at_192 rfl (blockEnd_cons' hf_at_194 rfl (blockEnd_cons' hf_at_196 rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n3, c3, D3, k3⟩ := D2.memset C (d := 0xD0 + h.length % 128 + 1) (b := 0) (N := 127 - h.length % 128)
    hf_at_198 hf_at_19c (by decide) (by decide)
    (by rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [k1, ha0]
        exact add_ofNat_assoc F _ 1)
    (by rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [D1.st.zero]); try rfl)
    (by rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [D1.st.zero]); rw [k1, h19]
        exact BitVec.zero_add _)
    (by omega)
  have kk3 : ∀ q : Fin 32, q.val ∈ evKeep → reg n3 q = reg n q := fun q hq => by
    rw [k3 q hq, hr2, evb_reg q D1.st.zero (by revert hq; revert q; decide), k1]
  -- the buffer and the hash value after the padding byte and the zeros
  have hb : ∀ m, m ≤ 127 - h.length % 128 →
      memBytes (fillBytes (memStore8 M (F + BitVec.ofNat 32 (0xD0 + h.length % 128)) ((0x80 : Word).extractLsb' 0 8))
        (F + BitVec.ofNat 32 (0xD0 + h.length % 128 + 1)) ((0 : Word).extractLsb' 0 8) (127 - h.length % 128))
        (F + BitVec.ofNat 32 0xD0) (h.length % 128 + 1 + m) = tailBytes5 h ++ [0x80] ++ List.replicate m 0 := by
    intro m hm
    rw [show h.length % 128 + 1 + m = h.length % 128 + (m + 1) by omega, memBytes_split, ← H.buf, memBytes_succ]
    rw [memBytes_congr fun i hi => by
          rw [S0, hf_fb_out C (by omega) (by omega) (Or.inl (by omega)), hf_sb_out C (by omega) (by omega) (by omega)]]
    rw [S0, hf_fb_out C (by omega) (by omega) (Or.inl (by omega)), memStore8_same,
      show F + BitVec.ofNat 32 (0xD0 + h.length % 128) + 1 = F + BitVec.ofNat 32 (0xD0 + h.length % 128 + 1) from
        add_ofNat_assoc F _ 1, fill_memBytes _ _ _ hm (by omega)]
    simp
  have hs : s5Hv (fillBytes (memStore8 M (F + BitVec.ofNat 32 (0xD0 + h.length % 128)) ((0x80 : Word).extractLsb' 0 8))
        (F + BitVec.ofNat 32 (0xD0 + h.length % 128 + 1)) ((0 : Word).extractLsb' 0 8) (127 - h.length % 128))
        (F + BitVec.ofNat 32 0x150) = s5Hv M (F + BitVec.ofNat 32 0xD0 + 0x80) :=
    s5Hv_copy fun i hi => by
      rw [show F + BitVec.ofNat 32 0xD0 + 0x80 = F + BitVec.ofNat 32 0x150 from S0 0x80, add_ofNat_assoc,
        hf_fb_out C (by omega) (by omega) (Or.inr (by omega)), hf_sb_out C (by omega) (by omega) (by omega)]
  have fr3 : ∀ c, c < 0x240 → (c < 0xD0 ∨ 0x190 ≤ c) →
      fillBytes (memStore8 M (F + BitVec.ofNat 32 (0xD0 + h.length % 128)) ((0x80 : Word).extractLsb' 0 8))
        (F + BitVec.ofNat 32 (0xD0 + h.length % 128 + 1)) ((0 : Word).extractLsb' 0 8) (127 - h.length % 128)
        (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := fun c hc hh => by
    rcases hh with hh | hh <;>
      rw [hf_fb_out C (by omega) hc (by omega), hf_sb_out C (by omega) hc (by omega)]
  have hash0 := H.hash
  rw [show F + BitVec.ofNat 32 0xD0 + 0x80 = F + BitVec.ofNat 32 0x150 from S0 0x80] at hash0 hs
  -- li a0, 15; bltu a0, s2
  obtain ⟨n4, c4, D4, hr4⟩ := D3.block C (off' := 0x1A2) [.aluImm .add a0 x0 0xF] (bEnd1 hf_at_1a0 rfl)
    ⟨trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have v15 : reg n4 a0 = 0xF := by
    rw [hr4]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D3.st.zero]; rfl
  have v19 : reg n4 19 = BitVec.ofNat 32 (127 - h.length % 128) := by
    rw [hr4, evb_reg 19 D3.st.zero (by decide), kk3 19 (by decide), h19]
  have kk4 : ∀ q : Fin 32, q.val ∈ evKeep → reg n4 q = reg n q := fun q hq => by
    rw [hr4, evb_reg q D3.st.zero (by revert hq; revert q; decide), kk3 q hq]
  have hbr : branchTaken .bltu (reg n4 a0) (reg n4 19) = decide (h.length % 128 < 112) := by
    rw [v15, v19]
    show decide ((15 : Word).toNat < (BitVec.ofNat 32 (127 - h.length % 128)).toNat) = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 127 - h.length % 128 < 2 ^ 32)]
    exact decide_eq_decide.mpr (show 15 < 127 - h.length % 128 ↔ h.length % 128 < 112 from ⟨by omega, by omega⟩)
  by_cases hlt : h.length % 128 < 112
  · obtain ⟨n5, d5, u5⟩ := D4.st.taken (D4.code C) 0x1C2 hf_at_1a2 rfl (by rw [hbr]; exact decide_eq_true hlt)
    have e112 := hb (111 - h.length % 128) (by omega)
    rw [show h.length % 128 + 1 + (111 - h.length % 128) = 112 by omega] at e112
    refine ⟨n5, _, c2.trans (c3.trans (c4.trans (Steps.single d5))) |> (Steps.single d1).trans, D4.jmp u5,
      fun q hq => by rw [u5.regs, kk4 q hq], ?_, fr3⟩
    rw [padTail5_short h hlt, List.foldl_append, ← hash0, hs, e112]
    unfold padTail5 padZeros5
    rw [show (239 - h.length % 128) % 128 = 111 - h.length % 128 by omega]
    rfl
  · obtain ⟨n5, d5, u5⟩ := D4.st.notTaken (D4.code C) 0x1A6 hf_at_1a2 rfl
      (by rw [hbr]; exact decide_eq_false hlt)
    have D5 := D4.jmp u5
    obtain ⟨n6, c6, D6, hr6⟩ := D5.block C (off' := 0x1AA)
      [.aluImm .add a1 sp 0xD0, .alu .add a0 x0 (26 : Fin 32)]
      (blockEnd_cons' hf_at_1a6 rfl (blockEnd_cons' hf_at_1a8 rfl rfl))
      ⟨trivial, trivial, trivial⟩ rfl
      (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n7, c7, D7, k7, hc7, fr7⟩ := D6.finBlock C (a := 0x150) (b := 0xD0) hf_at_1aa hf_at_1ae (by decide)
      (by decide)
      (by rw [hr6]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
          rw [u5.regs, kk4 26 (by decide), h26]; exact BitVec.zero_add _)
      (by rw [hr6]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D5.hsp]; rfl)
      (by decide) (by decide) (by decide)
    obtain ⟨n8, c8, D8, hr8⟩ := D7.block C (off' := 0x1BA)
      [.aluImm .add a0 sp 0xD0, .aluImm .add a2 x0 0x70, .aluImm .add a1 x0 0x0]
      (blockEnd_cons' hf_at_1b2 rfl (blockEnd_cons' hf_at_1b4 rfl (blockEnd_cons' hf_at_1b8 rfl rfl)))
      ⟨trivial, trivial, trivial, trivial⟩ rfl
      (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n9, c9, D9, k9⟩ := D8.memset C (d := 0xD0) (b := 0) (N := 0x70) hf_at_1ba hf_at_1be (by decide)
      (by decide)
      (by rw [hr8]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D7.hsp]; rfl)
      (by rw [hr8]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [D7.st.zero]); try rfl)
      (by rw [hr8]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; (try rw [D7.st.zero]); try rfl)
      (by decide)
    have e128 := hb (127 - h.length % 128) (by omega)
    rw [show h.length % 128 + 1 + (127 - h.length % 128) = 128 by omega] at e128
    have fr7' : ∀ c, c < 0x240 → (c < 0x150 ∨ 0x190 ≤ c) → n7.mem (F + BitVec.ofNat 32 c) =
        (fillBytes (memStore8 M (F + BitVec.ofNat 32 (0xD0 + h.length % 128)) ((0x80 : Word).extractLsb' 0 8))
          (F + BitVec.ofNat 32 (0xD0 + h.length % 128 + 1)) ((0 : Word).extractLsb' 0 8) (127 - h.length % 128))
          (F + BitVec.ofNat 32 c) := fun c hc hh => by
      refine fr7 _ (C.zF (by omega)) (C.offs ?_ (by decide) (by omega))
      rcases hh with hh | hh
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    have hs9 : s5Hv (fillBytes n7.mem (F + BitVec.ofNat 32 0xD0) ((0 : Word).extractLsb' 0 8) 0x70)
        (F + BitVec.ofNat 32 0x150) = s5Hv n7.mem (F + BitVec.ofNat 32 0x150) :=
      s5Hv_congr fun i hi => by rw [add_ofNat_assoc, hf_fb_out C (by decide) (by omega) (Or.inr (by omega))]
    refine ⟨n9, _, (Steps.single d1).trans (c2.trans (c3.trans (c4.trans ((Steps.single d5).trans (c6.trans
      (c7.trans (c8.trans c9))))))), D9, fun q hq => ?_, ?_, fun c hc hh => ?_⟩
    · rw [k9 q hq, hr8, evb_reg q D7.st.zero (by revert hq; revert q; decide), k7 q hq, hr6,
        evb_reg q D5.st.zero (by revert hq; revert q; decide), u5.regs, kk4 q hq]
    · rw [padTail5_long h (by omega), List.foldl_append, ← hash0, hs9, hc7, ← hs, e128,
        fill_memBytes _ _ _ (Nat.le_refl 112) (by decide)]
      rw [show (BitVec.extractLsb' 0 8 (0 : Word)).toNat = 0 from rfl]
      simp only [List.foldl_cons, List.foldl_nil]
    · rcases hh with hh | hh <;>
        rw [hf_fb_out C (by decide) hc (by omega), fr7' c hc (by omega), fr3 c hc (by omega)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- From 0x1C2 to 0x1E0: the length in bits stored in the buffer's last 16
bytes and the buffer compressed into the hash value. -/
theorem hf_fend (C : HfCtx M0 F out p len) {M : Word → BitVec 8} {n : Machine} (D : HfSt M0 Ms F r0 M n 0x1C2)
    (h26 : reg n 26 = F + BitVec.ofNat 32 0x150) {lo : Word} {pos : Nat} (hp : pos < 128)
    (h21 : reg n 21 = bswap32 ((lo <<< 10) ||| (BitVec.ofNat 32 pos <<< 3))) (h22 : reg n 22 = bswap32 (lo >>> 22))
    (h23 : reg n 23 = 0) (h24 : reg n 24 = 0) :
    ∃ n' M', Steps n n' ∧ HfSt M0 Ms F r0 M' n' 0x1E0 ∧ (∀ q : Fin 32, q.val ∈ evKeep → reg n' q = reg n q) ∧
      (s5Hv M' (F + BitVec.ofNat 32 0x150)).toList = Sha512.compress (s5Hv M (F + BitVec.ofNat 32 0x150)).toList
        (memBytes M (F + BitVec.ofNat 32 0xD0) 112 ++ Sha512.be128 (8 * (128 * lo.toNat + pos))) ∧
      ∀ c, c < 0x240 → (c < 0xD0 ∨ 0x190 ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  obtain ⟨n0, c0, D0, hr0⟩ := D.block C (off' := 0x1C4) [.aluImm .add a0 sp 0x100] (bEnd1 hf_at_1c2 rfl)
    ⟨trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have va0 : reg n0 a0 = F + BitVec.ofNat 32 0x100 := by
    rw [hr0]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; rfl
  have kk0 : ∀ q : Fin 32, q.val ∈ evKeep → reg n0 q = reg n q := fun q hq => by
    rw [hr0, evb_reg q D.st.zero (by revert hq; revert q; decide)]
  obtain ⟨n1, d1, D1, k1⟩ := D0.sw C hf_at_1c4 (off' := 0x1C8) rfl (c := 0x140)
    (by rw [va0]; exact add_ofNat_assoc F 0x100 0x40) (by decide) (by decide)
  obtain ⟨n2, d2, D2, k2⟩ := D1.sw C hf_at_1c8 (off' := 0x1CC) rfl (c := 0x144)
    (by rw [k1, va0]; exact add_ofNat_assoc F 0x100 0x44) (by decide) (by decide)
  obtain ⟨n3, d3, D3, k3⟩ := D2.sw C hf_at_1cc (off' := 0x1D0) rfl (c := 0x148)
    (by rw [k2, k1, va0]; exact add_ofNat_assoc F 0x100 0x48) (by decide) (by decide)
  obtain ⟨n4, d4, D4, k4⟩ := D3.sw C hf_at_1d0 (off' := 0x1D4) rfl (c := 0x14C)
    (by rw [k3, k2, k1, va0]; exact add_ofNat_assoc F 0x100 0x4C) (by decide) (by decide)
  simp only [k3, k2, k1] at D4
  rw [kk0 24 (by decide), kk0 23 (by decide), kk0 22 (by decide), kk0 21 (by decide), h21, h22, h23, h24] at D4
  obtain ⟨M4, hM4, D4⟩ : ∃ M4, M4 = memStore32 (memStore32 (memStore32 (memStore32 M (F + BitVec.ofNat 32 0x140) 0)
      (F + BitVec.ofNat 32 0x144) 0) (F + BitVec.ofNat 32 0x148) (bswap32 (lo >>> 22))) (F + BitVec.ofNat 32 0x14C)
      (bswap32 ((lo <<< 10) ||| (BitVec.ofNat 32 pos <<< 3))) ∧ HfSt M0 Ms F r0 M4 n4 0x1D4 := ⟨_, rfl, D4⟩
  have kk4 : ∀ q, reg n4 q = reg n0 q := fun q => by rw [k4, k3, k2, k1]
  obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x1D8)
    [.aluImm .add a1 sp 0xD0, .alu .add a0 x0 (26 : Fin 32)]
    (blockEnd_cons' hf_at_1d4 rfl (blockEnd_cons' hf_at_1d6 rfl rfl))
    ⟨trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n6, c6, D6, k6, hc6, fr6⟩ := D5.finBlock C (a := 0x150) (b := 0xD0) hf_at_1d8 hf_at_1dc (by decide)
    (by decide)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [kk4, kk0 26 (by decide), h26]; exact BitVec.zero_add _)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; rfl)
    (by decide) (by decide) (by decide)
  have fr6' : ∀ c, c < 0x240 → (c < 0x150 ∨ 0x190 ≤ c) → n6.mem (F + BitVec.ofNat 32 c) = M4 (F + BitVec.ofNat 32 c) :=
    fun c hc hh => by
      refine fr6 _ (C.zF (by omega)) (C.offs ?_ (by decide) (by omega))
      rcases hh with hh | hh
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
  have fr4 : ∀ c, c < 0x240 → (c < 0x140 ∨ 0x150 ≤ c) → M4 (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) :=
    fun c hc hh => by
      rcases hh with hh | hh <;>
        rw [hM4, hf_sw_out C (d := 0x14C) (by decide) hc (by omega), hf_sw_out C (d := 0x148) (by decide) hc (by omega),
          hf_sw_out C (d := 0x144) (by decide) hc (by omega), hf_sw_out C (d := 0x140) (by decide) hc (by omega)]
  have hs4 : s5Hv M4 (F + BitVec.ofNat 32 0x150) = s5Hv M (F + BitVec.ofNat 32 0x150) :=
    s5Hv_congr fun i hi => by rw [add_ofNat_assoc, fr4 _ (by omega) (Or.inr (by omega))]
  have hb4 : memBytes M4 (F + BitVec.ofNat 32 0xD0) 128 =
      memBytes M (F + BitVec.ofNat 32 0xD0) 112 ++ Sha512.be128 (8 * (128 * lo.toNat + pos)) := by
    rw [show (128 : Nat) = 112 + 16 from rfl, memBytes_split,
      memBytes_congr fun i hi => by rw [add_ofNat_assoc, fr4 _ (by omega) (Or.inl (by omega))],
      show F + BitVec.ofNat 32 0xD0 + BitVec.ofNat 32 112 = F + BitVec.ofNat 32 0x140 from add_ofNat_assoc F 0xD0 112,
      hM4, show F + BitVec.ofNat 32 0x144 = F + BitVec.ofNat 32 0x140 + BitVec.ofNat 32 4 from (add_ofNat_assoc F 0x140 4).symm,
      show F + BitVec.ofNat 32 0x148 = F + BitVec.ofNat 32 0x140 + BitVec.ofNat 32 8 from (add_ofNat_assoc F 0x140 8).symm,
      show F + BitVec.ofNat 32 0x14C = F + BitVec.ofNat 32 0x140 + BitVec.ofNat 32 12 from (add_ofNat_assoc F 0x140 12).symm,
      len_bytes5 _ _ _ _ hp]
  refine ⟨n6, _, c0.trans ((Steps.single d1).trans ((Steps.single d2).trans ((Steps.single d3).trans ((Steps.single d4).trans
    (c5.trans c6))))), D6, fun q hq => ?_, ?_, fun c hc hh => ?_⟩
  · rw [k6 q hq, hr5, evb_reg q D4.st.zero (by revert hq; revert q; decide), kk4, kk0 q hq]
  · rw [hc6, hs4, hb4]
  · rcases hh with hh | hh <;> rw [fr6' c hc (by omega), fr4 c hc (by omega)]

set_option maxHeartbeats 16000000 in
/-- One pass of the loop at offset 0x1E6: hash word `k` stored big-endian
at `F + 0x1D0 + 8k`. -/
theorem hf_rd_body (C : HfCtx M0 F out p len) {M : Word → BitVec 8} {n : Machine} {k : Nat} (hk : k < 8)
    (D : HfSt M0 Ms F r0 M n 0x1E6) (h8 : reg n 8 = F + BitVec.ofNat 32 (0x1D0 + 8 * k))
    (h26 : reg n 26 = F + BitVec.ofNat 32 (0x150 + 8 * k)) (h16 : reg n 16 = BitVec.ofNat 32 (8 - k)) :
    ∃ n' M', Steps n n' ∧ (k + 1 < 8 → HfSt M0 Ms F r0 M' n' 0x1E6) ∧ (k + 1 = 8 → HfSt M0 Ms F r0 M' n' 0x22E) ∧
      reg n' 8 = F + BitVec.ofNat 32 (0x1D0 + 8 * (k + 1)) ∧ reg n' 26 = F + BitVec.ofNat 32 (0x150 + 8 * (k + 1)) ∧
      reg n' 16 = BitVec.ofNat 32 (8 - (k + 1)) ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 9 → q ≠ 8 → q ≠ 26 → reg n' q = reg n q) ∧
      memBytes M' (F + BitVec.ofNat 32 (0x1D0 + 8 * k)) 8 = Sha512.wordBytes (hvW M (F + BitVec.ofNat 32 0x150) k) ∧
      ∀ c, c < 0x240 → (c < 0x1D0 + 8 * k ∨ 0x1D0 + 8 * k + 8 ≤ c) →
        M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  have z0 := D.st.zero
  have hA : aluEval .add (reg n x0) (reg n 26) = F + BitVec.ofNat 32 (0x150 + 8 * k) := by
    rw [z0, h26]; exact BitVec.zero_add _
  have e1 : (F + BitVec.ofNat 32 (0x150 + 8 * k) + 4).toNat % 4 = 0 := by
    rw [show F + BitVec.ofNat 32 (0x150 + 8 * k) + 4 = F + BitVec.ofNat 32 (0x150 + 8 * k + 4) from
      add_ofNat_assoc F _ 4]; exact C.al (by omega)
  have e2 : (F + BitVec.ofNat 32 (0x150 + 8 * k) + 0).toNat % 4 = 0 := by
    rw [show F + BitVec.ofNat 32 (0x150 + 8 * k) + 0 = F + BitVec.ofNat 32 (0x150 + 8 * k + 0) from
      add_ofNat_assoc F _ 0]; exact C.al (by omega)
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x204)
    ((.alu .add a0 x0 (26 : Fin 32)) :: (.lw a1 a0 0x4) :: (.lw a2 a0 0x0) :: (.aluImm .srl (17 : Fin 32) a1 0x18) ::
      (.aluImm .srl a4 a2 0x18) :: (.aluImm .srl a5 a2 0x8) :: (.aluImm .srl (9 : Fin 32) a2 0x10) ::
      (.aluImm .srl a0 a1 0x8) :: (.aluImm .srl a3 a1 0x10) :: [])
    (blockEnd_cons' (off' := 0x1E8) hf_at_1e6 rfl (blockEnd_cons' (off' := 0x1EA) hf_at_1e8 rfl
      (blockEnd_cons' (off' := 0x1EC) hf_at_1ea rfl (blockEnd_cons' (off' := 0x1F0) hf_at_1ec rfl
      (blockEnd_cons' (off' := 0x1F4) hf_at_1f0 rfl (blockEnd_cons' (off' := 0x1F8) hf_at_1f4 rfl
      (blockEnd_cons' (off' := 0x1FC) hf_at_1f8 rfl (blockEnd_cons' (off' := 0x200) hf_at_1fc rfl
      (blockEnd_cons' (off' := 0x204) hf_at_200 rfl rfl)))))))))
    (by simp +decide only [BlockOk, BInstr.ok, BInstr.run, upd, ↓reduceIte, and_true, true_and]
        rw [hA]; exact ⟨e1, e2⟩)
    rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have v91 : reg n1 8 = F + BitVec.ofNat 32 (0x1D0 + 8 * k) := by rw [hr1, evb_reg 8 z0 (by decide), h8]
  have v241 : reg n1 26 = F + BitVec.ofNat 32 (0x150 + 8 * k) := by rw [hr1, evb_reg 26 z0 (by decide), h26]
  have v161 : reg n1 16 = BitVec.ofNat 32 (8 - k) := by rw [hr1, evb_reg 16 z0 (by decide), h16]
  have kk1 : ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 9 → reg n1 q = reg n q := fun q hq h8 => by
    rw [hr1, evb_reg q z0 (by revert h8; revert hq; revert q; decide)]
  -- the bytes the stores take
  have bt : ∀ (r : Fin 32) (x : Word) (s : Nat), s < 32 → reg n1 r = aluEval .srl x (BitVec.ofNat 32 s) →
      ((reg n1 r).extractLsb' 0 8).toNat = x.toNat / 2 ^ s % 256 := fun r x s hs h => by rw [h]; exact srl_byte x s hs
  have t17 := bt 17 (memLoad32 M (F + BitVec.ofNat 32 (0x150 + 8 * k) + 4)) 24 (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA]; rfl)
  have ta3 := bt a3 (memLoad32 M (F + BitVec.ofNat 32 (0x150 + 8 * k) + 4)) 16 (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA]; rfl)
  have ta0 := bt a0 (memLoad32 M (F + BitVec.ofNat 32 (0x150 + 8 * k) + 4)) 8 (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA]; rfl)
  have ta4 := bt a4 (memLoad32 M (F + BitVec.ofNat 32 (0x150 + 8 * k) + 0)) 24 (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA]; rfl)
  have t8 := bt 9 (memLoad32 M (F + BitVec.ofNat 32 (0x150 + 8 * k) + 0)) 16 (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA]; rfl)
  have ta5 := bt a5 (memLoad32 M (F + BitVec.ofNat 32 (0x150 + 8 * k) + 0)) 8 (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA]; rfl)
  have ta1 : ((reg n1 a1).extractLsb' 0 8).toNat = (memLoad32 M (F + BitVec.ofNat 32 (0x150 + 8 * k) + 4)).toNat % 256 := by
    rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA, byte_toNat, Nat.pow_zero, Nat.div_one]
  have ta2 : ((reg n1 a2).extractLsb' 0 8).toNat = (memLoad32 M (F + BitVec.ofNat 32 (0x150 + 8 * k) + 0)).toNat % 256 := by
    rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [hA, byte_toNat, Nat.pow_zero, Nat.div_one]
  -- the 8 byte stores
  have sa : ∀ (j : Nat) (r : Machine), reg r 8 = reg n1 8 →
      reg r 8 + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (0x1D0 + 8 * k + j) := fun j r h => by
    rw [h, v91]; exact add_ofNat_assoc F _ j
  obtain ⟨n2, d2, D2, k2⟩ := D1.sb C hf_at_204 (off' := 0x208) rfl (c := 0x1D0 + 8 * k + 4) (sa 4 n1 rfl) (by omega)
  obtain ⟨n3, d3, D3, k3⟩ := D2.sb C hf_at_208 (off' := 0x20C) rfl (c := 0x1D0 + 8 * k + 5) (sa 5 n2 (k2 8)) (by omega)
  obtain ⟨n4, d4, D4, k4⟩ := D3.sb C hf_at_20c (off' := 0x210) rfl (c := 0x1D0 + 8 * k + 6)
    (sa 6 n3 (by rw [k3, k2])) (by omega)
  obtain ⟨n5, d5, D5, k5⟩ := D4.sb C hf_at_210 (off' := 0x214) rfl (c := 0x1D0 + 8 * k + 7)
    (sa 7 n4 (by rw [k4, k3, k2])) (by omega)
  obtain ⟨n6, d6, D6, k6⟩ := D5.sb C hf_at_214 (off' := 0x218) rfl (c := 0x1D0 + 8 * k + 0)
    (sa 0 n5 (by rw [k5, k4, k3, k2])) (by omega)
  obtain ⟨n7, d7, D7, k7⟩ := D6.sb C hf_at_218 (off' := 0x21C) rfl (c := 0x1D0 + 8 * k + 1)
    (sa 1 n6 (by rw [k6, k5, k4, k3, k2])) (by omega)
  obtain ⟨n8, d8, D8, k8⟩ := D7.sb C hf_at_21c (off' := 0x220) rfl (c := 0x1D0 + 8 * k + 2)
    (sa 2 n7 (by rw [k7, k6, k5, k4, k3, k2])) (by omega)
  obtain ⟨n9, d9, D9, k9⟩ := D8.sb C hf_at_220 (off' := 0x224) rfl (c := 0x1D0 + 8 * k + 3)
    (sa 3 n8 (by rw [k8, k7, k6, k5, k4, k3, k2])) (by omega)
  simp only [k8, k7, k6, k5, k4, k3, k2] at D9
  have kk9 : ∀ q, reg n9 q = reg n1 q := fun q => by rw [k9, k8, k7, k6, k5, k4, k3, k2]
  obtain ⟨M9, hM9, D9⟩ : ∃ M9, M9 = memStore8 (memStore8 (memStore8 (memStore8 (memStore8 (memStore8 (memStore8
      (memStore8 M (F + BitVec.ofNat 32 (0x1D0 + 8 * k + 4)) ((reg n1 a4).extractLsb' 0 8))
      (F + BitVec.ofNat 32 (0x1D0 + 8 * k + 5)) ((reg n1 9).extractLsb' 0 8))
      (F + BitVec.ofNat 32 (0x1D0 + 8 * k + 6)) ((reg n1 a5).extractLsb' 0 8))
      (F + BitVec.ofNat 32 (0x1D0 + 8 * k + 7)) ((reg n1 a2).extractLsb' 0 8))
      (F + BitVec.ofNat 32 (0x1D0 + 8 * k + 0)) ((reg n1 17).extractLsb' 0 8))
      (F + BitVec.ofNat 32 (0x1D0 + 8 * k + 1)) ((reg n1 a3).extractLsb' 0 8))
      (F + BitVec.ofNat 32 (0x1D0 + 8 * k + 2)) ((reg n1 a0).extractLsb' 0 8))
      (F + BitVec.ofNat 32 (0x1D0 + 8 * k + 3)) ((reg n1 a1).extractLsb' 0 8) ∧
      HfSt M0 Ms F r0 M9 n9 0x224 := ⟨_, rfl, D9⟩
  -- addi s1, s1, 8; addi s8, s8, 8; addi a6, a6, -1
  obtain ⟨n10, c10, D10, hr10⟩ := D9.block C (off' := 0x22A)
    [.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x8, .aluImm .add (26 : Fin 32) (26 : Fin 32) 0x8, .aluImm .add a6 a6 0xFFFFFFFF]
    (blockEnd_cons' hf_at_224 rfl (blockEnd_cons' hf_at_226 rfl (blockEnd_cons' hf_at_228 rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have v9 : reg n10 8 = F + BitVec.ofNat 32 (0x1D0 + 8 * (k + 1)) := by
    rw [hr10]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [kk9, v91]; exact add_sp F (b := 8) (by omega)
  have v24 : reg n10 26 = F + BitVec.ofNat 32 (0x150 + 8 * (k + 1)) := by
    rw [hr10]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [kk9, v241]; exact add_sp F (b := 8) (by omega)
  have v16 : reg n10 16 = BitVec.ofNat 32 (8 - (k + 1)) := by
    rw [hr10]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [kk9, v161]
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 32 (8 - k) + 0xFFFFFFFF).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 4294967295 from rfl]
    omega
  have kk10 : ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 9 → q ≠ 8 → q ≠ 26 → reg n10 q = reg n q := fun q hq h8 h9 h24 => by
    rw [hr10, evb_reg q D9.st.zero (by revert h24; revert h9; revert hq; revert q; decide), kk9, kk1 q hq h8]
  -- the bytes and the frame
  have hw : memBytes M9 (F + BitVec.ofNat 32 (0x1D0 + 8 * k)) 8 = Sha512.wordBytes (hvW M (F + BitVec.ofNat 32 0x150) k) := by
    unfold hvW
    rw [show F + BitVec.ofNat 32 0x150 + BitVec.ofNat 32 (8 * k) = F + BitVec.ofNat 32 (0x150 + 8 * k) + 0 from
        (add_ofNat_assoc F _ _).trans (add_ofNat_assoc F (0x150 + 8 * k) 0).symm,
      show F + BitVec.ofNat 32 0x150 + BitVec.ofNat 32 (8 * k + 4) = F + BitVec.ofNat 32 (0x150 + 8 * k) + 4 from by
        rw [add_ofNat_assoc, ← Nat.add_assoc]; exact (add_ofNat_assoc F (0x150 + 8 * k) 4).symm,
      wordBytes_pk, hM9]
    simp only [← add_ofNat_assoc F (0x1D0 + 8 * k)]
    rw [rd8, t17, ta3, ta0, ta1, ta4, t8, ta5, ta2]
  have fr9 : ∀ c, c < 0x240 → (c < 0x1D0 + 8 * k ∨ 0x1D0 + 8 * k + 8 ≤ c) →
      M9 (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := fun c hc hh => by
    rw [hM9]
    rcases hh with hh | hh <;>
      rw [hf_sb_out C (by omega) hc (by omega), hf_sb_out C (by omega) hc (by omega), hf_sb_out C (by omega) hc (by omega),
        hf_sb_out C (by omega) hc (by omega), hf_sb_out C (by omega) hc (by omega), hf_sb_out C (by omega) hc (by omega),
        hf_sb_out C (by omega) hc (by omega), hf_sb_out C (by omega) hc (by omega)]
  have cs : Steps n n10 := c1.trans ((Steps.single d2).trans ((Steps.single d3).trans ((Steps.single d4).trans
    ((Steps.single d5).trans ((Steps.single d6).trans ((Steps.single d7).trans ((Steps.single d8).trans
    ((Steps.single d9).trans c10))))))))
  by_cases hk1 : k + 1 < 8
  · obtain ⟨n11, d11, u11⟩ := D10.st.taken (D10.code C) 0x1E6 hf_at_22a rfl (by
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
  · obtain ⟨n11, d11, u11⟩ := D10.st.notTaken (D10.code C) 0x22E hf_at_22a rfl (by
      rw [v16, D10.st.zero, show 8 - (k + 1) = 0 by omega]; rfl)
    exact ⟨n11, M9, cs.trans (Steps.single d11), fun h => absurd h hk1, fun _ => D10.jmp u11,
      by rw [u11.regs, v9], by rw [u11.regs, v24], by rw [u11.regs, v16],
      fun q hq h8 h9 h24 => by rw [u11.regs, kk10 q hq h8 h9 h24], hw, fr9⟩

/-- The loop at offset 0x1E6 from pass `k` on. -/
theorem hf_rd_loop (C : HfCtx M0 F out p len) {Mst : Word → BitVec 8} {R : Fin 32 → Word} :
    ∀ d k, k + d = 8 → k < 8 → ∀ (M : Word → BitVec 8) (n : Machine), HfSt M0 Ms F r0 M n 0x1E6 →
      reg n 8 = F + BitVec.ofNat 32 (0x1D0 + 8 * k) → reg n 26 = F + BitVec.ofNat 32 (0x150 + 8 * k) →
      reg n 16 = BitVec.ofNat 32 (8 - k) → (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 9 → q ≠ 8 → q ≠ 26 → reg n q = R q) →
      memBytes M (F + BitVec.ofNat 32 0x1D0) (8 * k) =
        ((List.range k).map (hvW Mst (F + BitVec.ofNat 32 0x150))).flatMap Sha512.wordBytes →
      (∀ c, c < 0x240 → (c < 0x1D0 ∨ 0x210 ≤ c) → M (F + BitVec.ofNat 32 c) = Mst (F + BitVec.ofNat 32 c)) →
      ∃ n' M', Steps n n' ∧ HfSt M0 Ms F r0 M' n' 0x22E ∧
        (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 9 → q ≠ 8 → q ≠ 26 → reg n' q = R q) ∧
        memBytes M' (F + BitVec.ofNat 32 0x1D0) 64 =
          (s5Hv Mst (F + BitVec.ofNat 32 0x150)).toList.flatMap Sha512.wordBytes ∧
        ∀ c, c < 0x240 → (c < 0x1D0 ∨ 0x210 ≤ c) → M' (F + BitVec.ofNat 32 c) = Mst (F + BitVec.ofNat 32 c) := by
  intro d
  induction d with
  | zero => intro k hk hk8; exact absurd hk (by omega)
  | succ d ih =>
    intro k hk hk8 M n D h9 h24 h16 hR hM hfr
    obtain ⟨n1, M1, c1, D1a, D1b, v9, v24, v16, kk, hw, fr⟩ := hf_rd_body C hk8 D h9 h24 h16
    have hW : hvW M (F + BitVec.ofNat 32 0x150) k = hvW Mst (F + BitVec.ofNat 32 0x150) k := by
      unfold hvW
      have e : ∀ o, o + 4 ≤ 64 → memLoad32 M (F + BitVec.ofNat 32 0x150 + BitVec.ofNat 32 o) =
          memLoad32 Mst (F + BitVec.ofNat 32 0x150 + BitVec.ofNat 32 o) := fun o ho =>
        vk_ld2 fun j hj => by
          rw [add_ofNat_assoc, add_ofNat_assoc]; exact hfr _ (by omega) (Or.inl (by omega))
      rw [e _ (by omega), e _ (by omega)]
    have hM1 : memBytes M1 (F + BitVec.ofNat 32 0x1D0) (8 * (k + 1)) =
        ((List.range (k + 1)).map (hvW Mst (F + BitVec.ofNat 32 0x150))).flatMap Sha512.wordBytes := by
      rw [show 8 * (k + 1) = 8 * k + 8 by omega, memBytes_split, flatMap_range_succ, ← hM, ← hW, ← hw,
        add_ofNat_assoc, memBytes_congr (M' := M1) (M := M) (p := F + BitVec.ofNat 32 0x1D0) (n := 8 * k)
          fun i hi => by rw [add_ofNat_assoc, fr _ (by omega) (Or.inl (by omega))]]
    have hfr1 : ∀ c, c < 0x240 → (c < 0x1D0 ∨ 0x210 ≤ c) → M1 (F + BitVec.ofNat 32 c) = Mst (F + BitVec.ofNat 32 c) :=
      fun c hc hh => by
        rcases hh with hh | hh
        · rw [fr c hc (Or.inl (by omega)), hfr c hc (Or.inl hh)]
        · rw [fr c hc (Or.inr (by omega)), hfr c hc (Or.inr hh)]
    have hR1 : ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 9 → q ≠ 8 → q ≠ 26 → reg n1 q = R q := fun q hq h8 h9 h24 => by
      rw [kk q hq h8 h9 h24, hR q hq h8 h9 h24]
    by_cases hk1 : k + 1 < 8
    · obtain ⟨n2, M2, c2, rest⟩ := ih (k + 1) (by omega) hk1 M1 n1 (D1a hk1) v9 v24 v16 hR1 hM1 hfr1
      exact ⟨n2, M2, c1.trans c2, rest⟩
    · have h8 : k + 1 = 8 := by omega
      rw [h8, ← s5Hv_toList, show 8 * 8 = 64 from rfl] at hM1
      exact ⟨n1, M1, c1, D1b h8, hR1, hM1, hfr1⟩


set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- From 0x1E0 to 0x22E: the 8 hash words written big-endian to
`F + 0x1D0`. -/
theorem hf_rd (C : HfCtx M0 F out p len) {M : Word → BitVec 8} {n : Machine} (D : HfSt M0 Ms F r0 M n 0x1E0)
    (h8 : reg n 8 = F + BitVec.ofNat 32 0x1D0) (h26 : reg n 26 = F + BitVec.ofNat 32 0x150) :
    ∃ n' M', Steps n n' ∧ HfSt M0 Ms F r0 M' n' 0x22E ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 9 → q ≠ 8 → q ≠ 26 → reg n' q = reg n q) ∧
      memBytes M' (F + BitVec.ofNat 32 0x1D0) 64 = (s5Hv M (F + BitVec.ofNat 32 0x150)).toList.flatMap Sha512.wordBytes ∧
      ∀ c, c < 0x240 → (c < 0x1D0 ∨ 0x210 ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x1E2) [.aluImm .add a6 x0 0x8] (bEnd1 hf_at_1e0 rfl)
    ⟨trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have v16 : reg n1 16 = 8 := by
    rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.st.zero]; rfl
  obtain ⟨n2, d2, u2⟩ := D1.st.notTaken (D1.code C) 0x1E6 hf_at_1e2 rfl (by rw [v16, D1.st.zero]; rfl)
  have D2 := D1.jmp u2
  have k2 : ∀ q : Fin 32, q.val ∈ evKeep → reg n2 q = reg n q := fun q hq => by
    rw [u2.regs, hr1, evb_reg q D.st.zero (by revert hq; revert q; decide)]
  obtain ⟨n3, M3, c3, D3, k3, hb3, fr3⟩ := hf_rd_loop C (Mst := M) (R := reg n2) 8 0 rfl (by decide) M n2 D2
    (by rw [k2 8 (by decide), h8]) (by rw [k2 26 (by decide), h26])
    (by rw [u2.regs, v16]; rfl) (fun q _ _ _ _ => rfl) rfl (fun _ _ _ => rfl)
  exact ⟨n3, M3, c1.trans ((Steps.single d2).trans c3), D3,
    fun q hq h9 h8 h26 => by rw [k3 q hq h9 h8 h26, k2 q hq], hb3, fr3⟩


end

end C3.RV32
