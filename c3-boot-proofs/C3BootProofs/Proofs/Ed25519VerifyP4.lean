import C3BootProofs.Proofs.Ed25519VerifyP3b
import C3BootProofs.Proofs.Ed25519VerifyWrap2

/-!
# `ed25519_verify`, offsets 0x104C to 0x115A: SHA-512 of `R ‖ A ‖ M`

The function starts a SHA-512 hasher at `F + 0xEF0` (the initial hash value
from `0x3FCC4AF8`, zero counts), feeds it `R` and the key's encoding, copies
it to `F + 0x450` and feeds that the message, then copies it back.
-/

namespace C3.RV32

open C3.Image

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}

/-- A byte store into the frame below the slots. -/
theorem EvSt.sb (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} {off : Nat}
    (D : EvSt M0 Ms F r0 M n off) {rs1 rs2 : Fin 32} {imm len' : Word} {off' c : Nat}
    (hf : fetchRel ed25519VerifyCode off = some (.store .sb rs1 rs2 imm, len'))
    (hn : BitVec.ofNat 32 off + len' = BitVec.ofNat 32 off') (ha : reg n rs1 + imm = F + BitVec.ofNat 32 c)
    (hc : c + 1 ≤ 0x166C) :
    ∃ n1, step n = some n1 ∧
      EvSt M0 Ms F r0 (memStore8 M (F + BitVec.ofNat 32 c) ((reg n rs2).extractLsb' 0 8)) n1 off' ∧
      ∀ q, reg n1 q = reg n q := by
  obtain ⟨n1, d1, u1⟩ := D.st.sb (D.code C) hf hn
  rw [ha] at u1
  exact ⟨n1, d1, D.store C (d := c) (k := 1) u1.self (by rw [u1.regs, D.hsp]) (by rw [u1.regs]) (by rw [u1.regs]) hc
    (fun x hx => st8_frame hx), u1.regs⟩

end

theorem s5Hv_copy {M M' : Word → BitVec 8} {a b : Word}
    (h : ∀ i, i < 64 → M' (a + BitVec.ofNat 32 i) = M (b + BitVec.ofNat 32 i)) : s5Hv M' a = s5Hv M b := by
  have e : ∀ o : Word, o.toNat + 4 ≤ 64 → memLoad32 M' (a + o) = memLoad32 M (b + o) := fun o ho =>
    vk_ld2 fun j hj => by
      have := h (o.toNat + j) (by omega)
      rwa [← add_ofNat_assoc, ← add_ofNat_assoc, ofNat_toNat_self] at this
  unfold s5Hv
  rw [e 0x0 (by decide), e 0x4 (by decide), e 0x8 (by decide), e 0xC (by decide), e 0x10 (by decide),
    e 0x14 (by decide), e 0x18 (by decide), e 0x1C (by decide), e 0x20 (by decide), e 0x24 (by decide),
    e 0x28 (by decide), e 0x2C (by decide), e 0x30 (by decide), e 0x34 (by decide), e 0x38 (by decide),
    e 0x3C (by decide)]

/-- A hasher survives a copy of its 0xD0 bytes. -/
theorem hasher5_copy {M M' : Word → BitVec 8} {S S' : Word} {h : Bytes} (H : S5U.Hasher5At M S h)
    (hc : ∀ j, j < 0xD0 → M' (S' + BitVec.ofNat 32 j) = M (S + BitVec.ofNat 32 j)) : S5U.Hasher5At M' S' h := by
  have ld : ∀ c, c + 4 ≤ 0xD0 → memLoad32 M' (S' + BitVec.ofNat 32 c) = memLoad32 M (S + BitVec.ofNat 32 c) :=
    fun c hc' => vk_ld2 fun j hj => by rw [add_ofNat_assoc, add_ofNat_assoc]; exact hc _ (by omega)
  have hl := H.hlen
  exact ⟨H.hlen, (hc 0x7F (by decide)).trans H.pos,
    by rw [← H.buf]; unfold memBytes
       exact List.map_congr_left fun i hi => by
         rw [hc i (by have := List.mem_range.mp hi; have := Nat.mod_lt h.length (show 128 > 0 by decide); omega)],
    by rw [← H.hash]; congr 1; exact s5Hv_copy fun i hi => by
         rw [show S' + 0x80 = S' + BitVec.ofNat 32 0x80 from rfl, show S + 0x80 = S + BitVec.ofNat 32 0x80 from rfl,
           add_ofNat_assoc, add_ofNat_assoc]; exact hc _ (by omega),
    (ld 0xC0 (by decide)).trans H.lo, (ld 0xC4 (by decide)).trans H.hi, (ld 0xC8 (by decide)).trans H.hi2,
    (ld 0xCC (by decide)).trans H.hi3⟩

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}

theorem evb_reg {M' : Word → BitVec 8} {f : Fin 32 → Word} {blk : List BInstr} (q : Fin 32) (h0 : f 0 = 0)
    (h : q ∉ blk.filterMap BInstr.dst) : (runBlock blk (M', f)).2 q = f q := runBlock_reg _ _ _ q h0 h

/-- A frame byte outside the hasher an `update` call wrote. -/
theorem upd_out (C : EvCtx M0 F pk sig msg len) {M M' : Word → BitVec 8} {s : Nat}
    (fr : ∀ x, Sep (evG F) 0xA10 x 1 → Sep (F + BitVec.ofNat 32 s) 0xD0 x 1 → M' x = M x) (hs : s + 0xD0 ≤ 0x16A0)
    {c : Nat} (hc : c < 0x16A0) (h : c < s ∨ s + 0xD0 ≤ c) : M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  refine fr _ (C.zF (by omega)) (C.offs ?_ hs (by omega))
  rcases h with h | h
  · exact Or.inr (by omega)
  · exact Or.inl (by omega)

theorem sw_out (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {d c : Nat} {v : Word} (hd : d + 4 ≤ 0x16A0)
    (hc : c < 0x16A0) (h : c < d ∨ d + 4 ≤ c) :
    memStore32 M (F + BitVec.ofNat 32 d) v (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  refine st32_frame (C.offs ?_ hd (by omega))
  rcases h with h | h
  · exact Or.inr (by omega)
  · exact Or.inl (by omega)

theorem sb_out (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {d c : Nat} {v : BitVec 8} (hd : d + 1 ≤ 0x16A0)
    (hc : c < 0x16A0) (h : c ≠ d) :
    memStore8 M (F + BitVec.ofNat 32 d) v (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  refine st8_frame (C.offs ?_ hd (by omega))
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact Or.inr (by omega)
  · exact Or.inl (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x104C: the message pointer and length to `F + 0x308`, a
hasher at `F + 0xEF0`, and `R` and the key's encoding fed to it. -/
theorem ev_h1 (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x104C)
    (h19 : reg n 19 = F + 0x90F) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x10B0 ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 9 → q ≠ 24 → reg n' q = reg n q) ∧
      reg n' 9 = F + BitVec.ofNat 32 0x30C ∧
      memLoad32 M' (F + BitVec.ofNat 32 0x308) = memLoad32 M (F + BitVec.ofNat 32 0xC) ∧
      memLoad32 M' (F + BitVec.ofNat 32 0x30C) = memLoad32 M (F + BitVec.ofNat 32 0x10) ∧
      S5U.Hasher5At M' (F + BitVec.ofNat 32 0xEF0)
        (memBytes M (F + BitVec.ofNat 32 0x228) 32 ++ memBytes M (F + BitVec.ofNat 32 0x128) 32) ∧
      ∀ c, c < 0x16A0 → (c < 0x308 ∨ (0x310 ≤ c ∧ c < 0xEF0) ∨ 0xFC0 ≤ c) →
        M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  have z0 := D.st.zero
  -- addi s1, sp, 0x30C
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x104E) [.aluImm .add (9 : Fin 32) sp 0x30C] (bEnd1 ev_at_104c rfl)
    ⟨trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have k1 : ∀ q : Fin 32, q ≠ 9 → reg n1 q = reg n q := fun q hq => by
    rw [hr1]; simp only [runBlock, BInstr.run]; exact upd_ne' hq z0
  have v9 : reg n1 9 = F + BitVec.ofNat 32 0x30C := by
    rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; rfl
  -- lw a0, 0xC(sp); sw a0, 0x308(sp)
  obtain ⟨n2, c2, D2, hr2⟩ := D1.block C (off' := 0x1050) [.lw a0 sp 0xC] (bEnd1 ev_at_104e rfl)
    ⟨by show (reg n1 sp + 0xC).toNat % 4 = 0
        rw [D1.hsp]; exact C.al (by decide), trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have k2 : ∀ q : Fin 32, q ≠ a0 → reg n2 q = reg n1 q := fun q hq => by
    rw [hr2]; simp only [runBlock, BInstr.run]; exact upd_ne' hq D1.st.zero
  have va2 : reg n2 a0 = memLoad32 M (F + BitVec.ofNat 32 0xC) := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D1.hsp]; rfl
  obtain ⟨n3, d3, D3, k3⟩ := D2.sw C ev_at_1050 (off' := 0x1054) rfl (c := 0x308) (by rw [D2.hsp]; rfl) (by decide) (by decide)
  rw [va2] at D3
  have c3 : Steps n2 n3 := Steps.single d3
  -- lw a0, 0x10(sp); sw a0, 0x30C(sp)
  obtain ⟨n4, c4, D4, hr4⟩ := D3.block C (off' := 0x1056) [.lw a0 sp 0x10] (bEnd1 ev_at_1054 rfl)
    ⟨by show (reg n3 sp + 0x10).toNat % 4 = 0
        rw [D3.hsp]; exact C.al (by decide), trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have k4 : ∀ q : Fin 32, q ≠ a0 → reg n4 q = reg n3 q := fun q hq => by
    rw [hr4]; simp only [runBlock, BInstr.run]; exact upd_ne' hq D3.st.zero
  have va4 : reg n4 a0 = memLoad32 M (F + BitVec.ofNat 32 0x10) := by
    rw [hr4]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D3.hsp]
    exact vk_ld2 fun j hj => by
      rw [show F + (16 : Word) + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (16 + j) from add_ofNat_assoc F 16 j]
      try rw [add_ofNat_assoc]
      exact sw_out C (d := 0x308) (c := 0x10 + j) (by decide) (by omega) (Or.inl (by omega))
  obtain ⟨n5, d5, D5, k5⟩ := D4.sw C ev_at_1056 (off' := 0x105A) rfl (c := 0x30C) (by rw [D4.hsp]; rfl) (by decide) (by decide)
  rw [va4] at D5
  have c5 : Steps n4 n5 := Steps.single d5
  -- s8 and the arguments of memcpy(F + 0xF70, IV, 64)
  obtain ⟨n6, c6, D6, hr6⟩ := D5.block C (off' := 0x1070)
    [.aluImm .add (24 : Fin 32) sp 0x7FF, .aluImm .add (24 : Fin 32) (24 : Fin 32) 0x771, .lui a1 0x3FCC5000,
      .aluImm .add a1 a1 0xFFFFFAF8, .aluImm .add a2 x0 0x40, .alu .add a0 x0 (24 : Fin 32)]
    (blockEnd_cons' ev_at_105a rfl (blockEnd_cons' ev_at_105e rfl (blockEnd_cons' ev_at_1062 rfl
      (blockEnd_cons' ev_at_1066 rfl (blockEnd_cons' ev_at_106a rfl (blockEnd_cons' ev_at_106e rfl rfl))))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have v24 : reg n6 24 = F + BitVec.ofNat 32 0xF70 := by
    rw [hr6]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [D5.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl
  have k6 : ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 24 → reg n6 q = reg n5 q := fun q hq h24 => by
    rw [hr6]; exact evb_reg q D5.st.zero (by revert h24; revert hq; revert q; decide)
  obtain ⟨n7, c7, D7, k7, fz7⟩ := D6.memcpy C (d := 0xF70) (s := BitVec.ofNat 32 0x3FCC4AF8) (N := 64)
    ev_at_1070 ev_at_1074 (by decide) (by decide)
    (by rw [hr6]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D5.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]
        exact (BitVec.zero_add _).trans (add_sp F rfl))
    (by rw [hr6]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by rw [hr6]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by decide) (C.zS (C.ro (by decide) (by decide))) (C.fS (C.ro (by decide) (by decide)) (by decide)) (by decide)
  have v19 : reg n7 19 = F + 0x90F := by
    rw [k7 19 (by decide), k6 19 (by decide) (by decide), k5, k4 _ (by decide), k3, k2 _ (by decide), k1 _ (by decide), h19]
  -- the counts and the buffer position cleared
  have a19 : ∀ o c : Nat, 0x90F + o = c → reg n7 19 + BitVec.ofNat 32 o = F + BitVec.ofNat 32 c := fun o c h => by
    rw [v19, ← h]; exact add_ofNat_assoc F 0x90F o
  obtain ⟨n8, d8, D8, k8⟩ := D7.sw C ev_at_1078 (off' := 0x107C) rfl (c := 0xFB0) (a19 0x6A1 _ rfl) (by decide) (by decide)
  obtain ⟨n9, d9, D9, k9⟩ := D8.sw C ev_at_107c (off' := 0x1080) rfl (c := 0xFB4) (by rw [k8]; exact a19 0x6A5 _ rfl) (by decide) (by decide)
  obtain ⟨n10, d10, D10, k10⟩ := D9.sw C ev_at_1080 (off' := 0x1084) rfl (c := 0xFB8) (by rw [k9, k8]; exact a19 0x6A9 _ rfl) (by decide)
    (by decide)
  obtain ⟨n11, d11, D11, k11⟩ := D10.sw C ev_at_1084 (off' := 0x1088) rfl (c := 0xFBC) (by rw [k10, k9, k8]; exact a19 0x6AD _ rfl)
    (by decide) (by decide)
  obtain ⟨n12, d12, D12, k12⟩ := D11.sb C ev_at_1088 (off' := 0x108C) rfl (c := 0xF6F) (by rw [k11, k10, k9, k8]; exact a19 0x660 _ rfl)
    (by decide)
  have z7 : reg n7 x0 = 0 := D7.st.zero
  have z8 : reg n8 x0 = 0 := by rw [k8]; exact z7
  have z9 : reg n9 x0 = 0 := by rw [k9]; exact z8
  have z10 : reg n10 x0 = 0 := by rw [k10]; exact z9
  have z11 : reg n11 x0 = 0 := by rw [k11]; exact z10
  rw [z7, z8, z9, z10, z11] at D12
  obtain ⟨M5, hM5, D6'⟩ : ∃ M5, M5 = memStore32 (memStore32 M (F + BitVec.ofNat 32 0x308)
      (memLoad32 M (F + BitVec.ofNat 32 0xC))) (F + BitVec.ofNat 32 0x30C) (memLoad32 M (F + BitVec.ofNat 32 0x10)) ∧
      EvSt M0 Ms F r0 M5 n6 0x1070 := ⟨_, rfl, D6⟩
  obtain ⟨M12, hM12, D12⟩ : ∃ M12, M12 = memStore8 (memStore32 (memStore32 (memStore32 (memStore32 n7.mem
      (F + BitVec.ofNat 32 0xFB0) 0) (F + BitVec.ofNat 32 0xFB4) 0) (F + BitVec.ofNat 32 0xFB8) 0)
      (F + BitVec.ofNat 32 0xFBC) 0) (F + BitVec.ofNat 32 0xF6F) ((0 : Word).extractLsb' 0 8) ∧
      EvSt M0 Ms F r0 M12 n12 0x108C := ⟨_, rfl, D12⟩
  have fM5 : ∀ c, c < 0x16A0 → (c < 0x308 ∨ 0x310 ≤ c) → M5 (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
    intro c hc h
    rcases h with h | h <;>
      rw [hM5, sw_out C (d := 0x30C) (by decide) hc (by omega), sw_out C (d := 0x308) (by decide) hc (by omega)]
  have fr12 : ∀ c, c < 0x16A0 → (c < 0xEF0 ∨ 0xFC0 ≤ c) → M12 (F + BitVec.ofNat 32 c) = M5 (F + BitVec.ofNat 32 c) := by
    intro c hc h
    rcases h with h | h <;>
      rw [hM12, hM5, sb_out C (d := 0xF6F) (by decide) hc (by omega), sw_out C (d := 0xFBC) (by decide) hc (by omega),
        sw_out C (d := 0xFB8) (by decide) hc (by omega), sw_out C (d := 0xFB4) (by decide) hc (by omega),
        sw_out C (d := 0xFB0) (by decide) hc (by omega), cp_out C fz7 (by decide) hc (by omega)]
  have zl : ∀ c, c < 4 → memLoad32 M12 (F + BitVec.ofNat 32 (0xFB0 + 4 * c)) = 0 := by
    intro c hc
    have s8 : Sep (F + BitVec.ofNat 32 0xF6F) 1 (F + BitVec.ofNat 32 (0xFB0 + 4 * c)) 4 :=
      C.offs (Or.inl (by omega)) (by decide) (by omega)
    have sw : ∀ d, d < 4 → d ≠ c → Sep (F + BitVec.ofNat 32 (0xFB0 + 4 * d)) 4 (F + BitVec.ofNat 32 (0xFB0 + 4 * c)) 4 :=
      fun d hd hdc => C.offs (by omega) (by omega) (by omega)
    rw [hM12, memLoad32_store8_sep s8]
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [memLoad32_store32_sep (sw 3 (by decide) (by decide)), memLoad32_store32_sep (sw 2 (by decide) (by decide)),
        memLoad32_store32_sep (sw 1 (by decide) (by decide))]
      exact memLoad32_store32_same _ _ _
    · rw [memLoad32_store32_sep (sw 3 (by decide) (by decide)), memLoad32_store32_sep (sw 2 (by decide) (by decide))]
      exact memLoad32_store32_same _ _ _
    · rw [memLoad32_store32_sep (sw 3 (by decide) (by decide))]
      exact memLoad32_store32_same _ _ _
    · exact memLoad32_store32_same _ _ _
  have H0 : S5U.Hasher5At M12 (F + BitVec.ofNat 32 0xEF0) [] := by
    refine ⟨by decide, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show F + BitVec.ofNat 32 0xEF0 + 0x7F = F + BitVec.ofNat 32 0xF6F from add_ofNat_assoc F 0xEF0 0x7F, hM12,
        memStore8_same]; rfl
    · rw [show F + BitVec.ofNat 32 0xEF0 + 0x80 = F + BitVec.ofNat 32 0xF70 from add_ofNat_assoc F 0xEF0 0x80,
        s5Hv_copy (M := M0) (b := BitVec.ofNat 32 0x3FCC4AF8) fun i hi => ?_, C.iv]
      · rfl
      rw [add_ofNat_assoc, hM12, sb_out C (d := 0xF6F) (by decide) (by omega) (by omega),
        sw_out C (d := 0xFBC) (by decide) (by omega) (Or.inl (by omega)),
        sw_out C (d := 0xFB8) (by decide) (by omega) (Or.inl (by omega)),
        sw_out C (d := 0xFB4) (by decide) (by omega) (Or.inl (by omega)),
        sw_out C (d := 0xFB0) (by decide) (by omega) (Or.inl (by omega)), cp_at C fz7 (by decide) hi]
      rw [← hM5]; exact D6'.roM C (a := 0x3FCC4AF8) (k := 64) (by decide) (by decide) i hi
    · rw [show F + BitVec.ofNat 32 0xEF0 + 0xC0 = F + BitVec.ofNat 32 (0xFB0 + 4 * 0) from add_ofNat_assoc F 0xEF0 0xC0, zl 0 (by decide)]; rfl
    · rw [show F + BitVec.ofNat 32 0xEF0 + 0xC4 = F + BitVec.ofNat 32 (0xFB0 + 4 * 1) from add_ofNat_assoc F 0xEF0 0xC4, zl 1 (by decide)]
    · rw [show F + BitVec.ofNat 32 0xEF0 + 0xC8 = F + BitVec.ofNat 32 (0xFB0 + 4 * 2) from add_ofNat_assoc F 0xEF0 0xC8, zl 2 (by decide)]
    · rw [show F + BitVec.ofNat 32 0xEF0 + 0xCC = F + BitVec.ofNat 32 (0xFB0 + 4 * 3) from add_ofNat_assoc F 0xEF0 0xCC, zl 3 (by decide)]
  -- update(R), update(A)
  obtain ⟨n13, c13, D13, hr13⟩ := D12.block C (off' := 0x1096)
    [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x6F1, .aluImm .add a1 sp 0x228]
    (blockEnd_cons' ev_at_108c rfl (blockEnd_cons' ev_at_1090 rfl (blockEnd_cons' ev_at_1094 rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n14, c14, D14, k14, H14, fr14⟩ := D13.upd32 C (s := 0xEF0) (d := 0x228) ev_at_1096 ev_at_109a (by decide)
    (by decide)
    (by rw [hr13]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D12.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr13]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D12.hsp]; rfl)
    (by decide) (by decide) (by decide) (Or.inr (by decide)) H0 (by decide)
  obtain ⟨n15, c15, D15, hr15⟩ := D14.block C (off' := 0x10A8)
    [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x6F1, .aluImm .add a1 sp 0x128]
    (blockEnd_cons' ev_at_109e rfl (blockEnd_cons' ev_at_10a2 rfl (blockEnd_cons' ev_at_10a6 rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n16, c16, D16, k16, H16, fr16⟩ := D15.upd32 C (s := 0xEF0) (d := 0x128) ev_at_10a8 ev_at_10ac (by decide)
    (by decide)
    (by rw [hr15]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D14.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr15]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D14.hsp]; rfl)
    (by decide) (by decide) (by decide) (Or.inr (by decide)) H14 (by simp [memBytes_length])
  have fr : ∀ c, c < 0x16A0 → (c < 0xEF0 ∨ 0xFC0 ≤ c) → n16.mem (F + BitVec.ofNat 32 c) = M5 (F + BitVec.ofNat 32 c) := by
    intro c hc h
    rw [upd_out C fr16 (by decide) hc h, upd_out C fr14 (by decide) hc h, fr12 c hc h]
  have bytes : ∀ d, d + 32 ≤ 0x308 → memBytes n14.mem (F + BitVec.ofNat 32 d) 32 = memBytes M (F + BitVec.ofNat 32 d) 32 ∧
      memBytes M12 (F + BitVec.ofNat 32 d) 32 = memBytes M (F + BitVec.ofNat 32 d) 32 := by
    intro d hd
    constructor <;> (unfold memBytes; refine List.map_congr_left fun i hi => ?_; have := List.mem_range.mp hi)
    · rw [add_ofNat_assoc, upd_out C fr14 (by decide) (by omega) (Or.inl (by omega)), fr12 _ (by omega) (Or.inl (by omega)),
        fM5 _ (by omega) (Or.inl (by omega))]
    · rw [add_ofNat_assoc, fr12 _ (by omega) (Or.inl (by omega)), fM5 _ (by omega) (Or.inl (by omega))]
  rw [(bytes 0x228 (by decide)).2, (bytes 0x128 (by decide)).1, List.nil_append] at H16
  have kept : ∀ q : Fin 32, q.val ∈ evKeep → reg n16 q = reg n7 q := fun q hq => by
    rw [k16 q hq, hr15, evb_reg q D14.st.zero (by revert hq; revert q; decide), k14 q hq, hr13,
      evb_reg q D12.st.zero (by revert hq; revert q; decide), k12, k11, k10, k9, k8]
  have ld : ∀ c, c + 4 ≤ 0x16A0 → (c + 4 ≤ 0xEF0) → memLoad32 n16.mem (F + BitVec.ofNat 32 c) =
      memLoad32 M5 (F + BitVec.ofNat 32 c) := fun c h1 h2 =>
    vk_ld2 fun j hj => by rw [add_ofNat_assoc]; try rw [add_ofNat_assoc]
                          exact fr _ (by omega) (Or.inl (by omega))
  refine ⟨n16, n16.mem, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans ((Steps.single d8).trans
    ((Steps.single d9).trans ((Steps.single d10).trans ((Steps.single d11).trans ((Steps.single d12).trans
    (c13.trans (c14.trans (c15.trans c16)))))))))))))), D16, fun q hq h9 h24 => ?_, ?_, ?_, ?_, H16, fun c hc h => ?_⟩
  · rw [kept q hq, k7 q hq, k6 q hq h24, k5, k4 q (by revert hq; revert q; decide), k3, k2 q (by revert hq; revert q; decide),
      k1 q h9]
  · rw [kept 9 (by decide), k7 9 (by decide), k6 9 (by decide) (by decide), k5, k4 _ (by decide), k3, k2 _ (by decide), v9]
  · rw [ld 0x308 (by decide) (by decide), hM5,
      memLoad32_store32_sep (C.offs (c := 0x30C) (n := 4) (d := 0x308) (k := 4) (Or.inr (by decide)) (by decide) (by decide))]
    exact memLoad32_store32_same _ _ _
  · rw [ld 0x30C (by decide) (by decide), hM5]
    exact memLoad32_store32_same _ _ _
  · rcases h with h | h | h
    · rw [fr c hc (Or.inl (by omega)), fM5 c hc (Or.inl h)]
    · rw [fr c hc (Or.inl (by omega)), fM5 c hc (Or.inr (by omega))]
    · rw [fr c hc (Or.inr h), fM5 c hc (Or.inr (by omega))]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x10B0: the hasher copied to `F + 0x450` (with `A` and `R`
copied below it), and the message fed to the copy in a loop that runs once. -/
theorem ev_h2 (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x10B0)
    (h9 : reg n 9 = F + BitVec.ofNat 32 0x30C) (hm : memLoad32 M (F + BitVec.ofNat 32 0x308) = msg)
    (hk : memLoad32 M (F + BitVec.ofNat 32 0x30C) = BitVec.ofNat 32 len) {h : Bytes}
    (H : S5U.Hasher5At M (F + BitVec.ofNat 32 0xEF0) h) (hl : h.length + len < 2 ^ 32) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x1106 ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → q ≠ 9 → q ≠ 18 → reg n' q = reg n q) ∧
      reg n' 18 = F + BitVec.ofNat 32 0x450 ∧
      S5U.Hasher5At M' (F + BitVec.ofNat 32 0x450) (h ++ memBytes M0 msg len) ∧
      ∀ c, c < 0x16A0 → (c < 0x350 ∨ 0x520 ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x10C2)
    [.aluImm .add (18 : Fin 32) sp 0x450, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x6F1, .aluImm .add a2 x0 0xD0,
      .alu .add a0 x0 (18 : Fin 32)]
    (blockEnd_cons' ev_at_10b0 rfl (blockEnd_cons' ev_at_10b4 rfl (blockEnd_cons' ev_at_10b8 rfl
      (blockEnd_cons' ev_at_10bc rfl (blockEnd_cons' ev_at_10c0 rfl rfl)))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have v18 : reg n1 18 = F + BitVec.ofNat 32 0x450 := by
    rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; rfl
  obtain ⟨n2, c2, D2, k2, fz2⟩ := D1.memcpy C (d := 0x450) (s := F + BitVec.ofNat 32 0xEF0) (N := 0xD0)
    ev_at_10c2 ev_at_10c6 (by decide) (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]
        exact (BitVec.zero_add _).trans rfl)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by decide) (C.zF (by decide)).symm (C.offs (by decide) (by decide) (by decide))
    (by rw [C.fN (by decide)]; have := C.hhi; omega)
  obtain ⟨n3, c3, D3, hr3⟩ := D2.block C (off' := 0x10D2)
    [.aluImm .add a0 sp 0x350, .aluImm .add a1 sp 0x128, .aluImm .add a2 x0 0xC0]
    (blockEnd_cons' ev_at_10ca rfl (blockEnd_cons' ev_at_10cc rfl (blockEnd_cons' ev_at_10ce rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n4, c4, D4, k4, fz4⟩ := D3.memcpy C (d := 0x350) (s := F + BitVec.ofNat 32 0x128) (N := 0xC0)
    ev_at_10d2 ev_at_10d6 (by decide) (by decide)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D2.hsp]; rfl)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D2.hsp]; rfl)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by decide) (C.zF (by decide)).symm (C.offs (by decide) (by decide) (by decide))
    (by rw [C.fN (by decide)]; have := C.hhi; omega)
  obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x10E4)
    [.aluImm .add a0 sp 0x410, .aluImm .add a1 sp 0x228, .aluImm .add a2 x0 0x40]
    (blockEnd_cons' ev_at_10da rfl (blockEnd_cons' ev_at_10de rfl (blockEnd_cons' ev_at_10e0 rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n6, c6, D6, k6, fz6⟩ := D5.memcpy C (d := 0x410) (s := F + BitVec.ofNat 32 0x228) (N := 0x40)
    ev_at_10e4 ev_at_10e8 (by decide) (by decide)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; rfl)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; rfl)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by decide) (C.zF (by decide)).symm (C.offs (by decide) (by decide) (by decide))
    (by rw [C.fN (by decide)]; have := C.hhi; omega)
  have fr6 : ∀ c, c < 0x16A0 → (c < 0x350 ∨ 0x520 ≤ c) → n6.mem (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
    intro c hc h
    rcases h with h | h <;>
      rw [cp_out C fz6 (by decide) hc (by omega), cp_out C fz4 (by decide) hc (by omega), cp_out C fz2 (by decide) hc (by omega)]
  have H6 : S5U.Hasher5At n6.mem (F + BitVec.ofNat 32 0x450) h := hasher5_copy H fun j hj => by
    rw [add_ofNat_assoc, cp_out C fz6 (by decide) (by omega) (by omega), cp_out C fz4 (by decide) (by omega) (by omega),
      cp_at C fz2 (by decide) hj]
  have kp6 : ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 18 → reg n6 q = reg n q := fun q hq h18 => by
    rw [k6 q hq, hr5, evb_reg q D4.st.zero (by revert hq; revert q; decide), k4 q hq, hr3,
      evb_reg q D2.st.zero (by revert hq; revert q; decide), k2 q hq, hr1,
      evb_reg q D.st.zero (by revert h18; revert hq; revert q; decide)]
  have v18' : reg n6 18 = F + BitVec.ofNat 32 0x450 := by
    rw [k6 18 (by decide), hr5, evb_reg 18 D4.st.zero (by decide), k4 18 (by decide), hr3,
      evb_reg 18 D2.st.zero (by decide), k2 18 (by decide), v18]
  have v9 : reg n6 9 = F + BitVec.ofNat 32 0x30C := by rw [kp6 9 (by decide) (by decide), h9]
  -- li s0, 8; beqz s0 (not taken)
  obtain ⟨n7, c7, D7, hr7⟩ := D6.block C (off' := 0x10EE) [.aluImm .add (8 : Fin 32) x0 8] (bEnd1 ev_at_10ec rfl)
    ⟨trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have r7 : ∀ q : Fin 32, q ≠ 8 → reg n7 q = reg n6 q := fun q hq => by
    rw [hr7]; simp only [runBlock, BInstr.run]; exact upd_ne' hq D6.st.zero
  have v8 : reg n7 8 = 8 := by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte, D6.st.zero]; try rfl
  obtain ⟨n8, d8, u8⟩ := D7.st.notTaken (D7.code C) 0x10F0 ev_at_10ee rfl (by rw [v8, D7.st.zero]; rfl)
  have D8 := D7.jmp u8
  -- lw a1, -4(s1); lw a2, 0(s1); mv a0, s2
  obtain ⟨n9, c9, D9, hr9⟩ := D8.block C (off' := 0x10F4) [.lw a1 (9 : Fin 32) 0xFFFFFFFC] (bEnd1 ev_at_10f0 rfl)
    ⟨by show (reg n8 9 + 0xFFFFFFFC).toNat % 4 = 0
        rw [u8.regs, r7 9 (by decide), v9,
          show F + BitVec.ofNat 32 0x30C + 0xFFFFFFFC = F + BitVec.ofNat 32 0x308 from add_ofNat_assoc F 0x30C 0xFFFFFFFC]
        exact C.al (by decide), trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have va1 : reg n9 a1 = msg := by
    rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [u8.regs, r7 9 (by decide), v9,
      show F + BitVec.ofNat 32 0x30C + 0xFFFFFFFC = F + BitVec.ofNat 32 0x308 from add_ofNat_assoc F 0x30C 0xFFFFFFFC, ← hm]
    exact vk_ld2 fun j hj => by rw [add_ofNat_assoc]; exact fr6 _ (by omega) (Or.inl (by omega))
  obtain ⟨n10, c10, D10, hr10⟩ := D9.block C (off' := 0x10F8) [.lw a2 (9 : Fin 32) 0x0, .alu .add a0 x0 (18 : Fin 32)]
    (blockEnd_cons' ev_at_10f4 rfl (blockEnd_cons' ev_at_10f6 rfl rfl))
    ⟨by show (reg n9 9 + 0x0).toNat % 4 = 0
        rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [u8.regs, r7 9 (by decide), v9]
        show (F + BitVec.ofNat 32 0x30C + BitVec.ofNat 32 0).toNat % 4 = 0
        rw [add_ofNat_assoc]; exact C.al (by decide), trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have r10 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n10 q = reg n8 q := fun q h0 h1 h2 => by
    rw [hr10, evb_reg q D9.st.zero (by revert h0 h1 h2; revert q; decide), hr9]
    simp only [runBlock, BInstr.run]; exact upd_ne' h1 D8.st.zero
  have va2 : reg n10 a2 = BitVec.ofNat 32 len := by
    rw [hr10]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [u8.regs, r7 9 (by decide), v9, ← hk]
    show memLoad32 n6.mem (F + BitVec.ofNat 32 0x30C + BitVec.ofNat 32 0) = _
    rw [add_ofNat_assoc]
    exact vk_ld2 fun j hj => by rw [add_ofNat_assoc]; exact fr6 _ (by omega) (Or.inl (by omega))
  have va0 : reg n10 a0 = F + BitVec.ofNat 32 0x450 := by
    rw [hr10]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [u8.regs, r7 18 (by decide), v18']; exact BitVec.zero_add _
  have va1' : reg n10 a1 = msg := by
    rw [hr10, evb_reg a1 D9.st.zero (by decide), va1]
  obtain ⟨n11, c11, D11, k11, H11, fr11⟩ := D10.upd C (s := 0x450) (p := msg) (k := len) ev_at_10f8 ev_at_10fc
    (by decide) (by decide) va0 va1' va2 (by decide) (by decide) C.hmsgW (C.fS C.sMsg (by decide)).symm (C.zS C.sMsg)
    H6 C.hlen hl
  rw [D6.bytesOut C.sMsg] at H11
  -- addi s1, s1, 8; addi s0, s0, -8; bnez s0 (not taken)
  obtain ⟨n12, c12, D12, hr12⟩ := D11.block C (off' := 0x1104)
    [.aluImm .add (9 : Fin 32) (9 : Fin 32) 8, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0xFFFFFFF8]
    (blockEnd_cons' ev_at_1100 rfl (blockEnd_cons' ev_at_1102 rfl rfl)) ⟨trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have v8' : reg n12 8 = 0 := by
    rw [hr12]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [k11 8 (by decide), r10 8 (by decide) (by decide) (by decide), u8.regs, v8]; rfl
  obtain ⟨n13, d13, u13⟩ := D12.st.notTaken (D12.code C) 0x1106 ev_at_1104 rfl (by rw [v8', D12.st.zero]; rfl)
  have D13 := D12.jmp u13
  have back : ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → q ≠ 9 → reg n13 q = reg n6 q := fun q hq h8 h9 => by
    rw [u13.regs, hr12, evb_reg q D11.st.zero (by revert h9; revert h8; revert q; decide), k11 q hq,
      r10 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide), u8.regs,
      r7 q h8]
  refine ⟨n13, n11.mem, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans ((Steps.single d8).trans
    (c9.trans (c10.trans (c11.trans (c12.trans (Steps.single d13)))))))))))), D13, fun q hq h8 h9 h18 => ?_, ?_, H11,
    fun c hc h => ?_⟩
  · rw [back q hq h8 h9, kp6 q hq h18]
  · rw [back 18 (by decide) (by decide) (by decide), v18']
  · rw [upd_out C fr11 (by decide) hc (by omega), fr6 c hc h]

/-- A frame byte a `zero64` call did not write. -/
theorem zf_out (C : EvCtx M0 F pk sig msg len) {M M' : Word → BitVec 8} {d : Nat}
    (fz : ∀ x, Sep (evG F) 0xA10 x 1 → M' x = fillBytes M (F + BitVec.ofNat 32 d) 0 64 x) (hd : d + 64 ≤ 0x16A0)
    {c : Nat} (hc : c < 0x16A0) (h : c < d ∨ d + 64 ≤ c) : M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  rw [fz _ (C.zF (by omega))]
  refine fillBytes_sep (C.offs ?_ hd (by omega)) (Nat.le_refl _)
  rcases h with h | h
  · exact Or.inr (by omega)
  · exact Or.inl (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x1106: the hasher moved back to `F + 0xEF0`, and the
digest buffer at `F + 0x7B0` and the buffer at `F + 0x9F0` cleared. -/
theorem ev_h3 (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x1106)
    (h18 : reg n 18 = F + BitVec.ofNat 32 0x450) {h : Bytes} (H : S5U.Hasher5At M (F + BitVec.ofNat 32 0x450) h) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x115A ∧
      (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 9 → q ≠ 26 → reg n' q = reg n q) ∧
      reg n' 26 = F + BitVec.ofNat 32 0xEF0 ∧ reg n' 9 = F + BitVec.ofNat 32 0x9F0 ∧
      S5U.Hasher5At M' (F + BitVec.ofNat 32 0xEF0) h ∧
      ∀ c, c < 0x16A0 → (c < 0x5E0 ∨ (0x7F0 ≤ c ∧ c < 0x9F0) ∨ (0xA30 ≤ c ∧ c < 0xEF0) ∨ 0xFC0 ≤ c) →
        M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  obtain ⟨n1, c1, D1, hr1⟩ := D.block C (off' := 0x1110)
    [.aluImm .add a0 sp 0x5E0, .aluImm .add a1 sp 0x350, .aluImm .add a2 x0 0x1D0]
    (blockEnd_cons' ev_at_1106 rfl (blockEnd_cons' ev_at_110a rfl (blockEnd_cons' ev_at_110c rfl rfl)))
    ⟨trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n2, c2, D2, k2, fz2⟩ := D1.memcpy C (d := 0x5E0) (s := F + BitVec.ofNat 32 0x350) (N := 0x1D0)
    ev_at_1110 ev_at_1114 (by decide) (by decide)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; rfl)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D.hsp]; rfl)
    (by rw [hr1]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by decide) (C.zF (by decide)).symm (C.offs (by decide) (by decide) (by decide))
    (by rw [C.fN (by decide)]; have := C.hhi; omega)
  obtain ⟨n3, c3, D3, hr3⟩ := D2.block C (off' := 0x112E)
    [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x6F1, .aluImm .add a2 x0 0xD0, .alu .add a1 x0 (18 : Fin 32),
      .aluImm .add (26 : Fin 32) sp 0x7FF, .aluImm .add (26 : Fin 32) (26 : Fin 32) 0x6F1]
    (blockEnd_cons' ev_at_1118 rfl (blockEnd_cons' ev_at_111c rfl (blockEnd_cons' ev_at_1120 rfl
      (blockEnd_cons' ev_at_1124 rfl (blockEnd_cons' ev_at_1126 rfl (blockEnd_cons' ev_at_112a rfl rfl))))))
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have v26 : reg n3 26 = F + BitVec.ofNat 32 0xEF0 := by
    rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [D2.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl
  obtain ⟨n4, c4, D4, k4, fz4⟩ := D3.memcpy C (d := 0xEF0) (s := F + BitVec.ofNat 32 0x450) (N := 0xD0)
    ev_at_112e ev_at_1132 (by decide) (by decide)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D2.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [k2 18 (by decide), hr1, evb_reg 18 D.st.zero (by decide), h18]; exact BitVec.zero_add _)
    (by rw [hr3]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; try rfl)
    (by decide) (C.zF (by decide)).symm (C.offs (by decide) (by decide) (by decide))
    (by rw [C.fN (by decide)]; have := C.hhi; omega)
  obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x113A) [.aluImm .add a0 sp 0x7B0] (bEnd1 ev_at_1136 rfl)
    ⟨trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  obtain ⟨n6, c6, D6, k6, fz6⟩ := D5.zero64 C (d := 0x7B0) ev_at_113a ev_at_113e (by decide) (by decide)
    (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; rfl) (by decide)
  obtain ⟨n7, c7, D7, hr7⟩ := D6.block C (off' := 0x1152)
    [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x1F1, .aluImm .add (9 : Fin 32) sp 0x7FF,
      .aluImm .add (9 : Fin 32) (9 : Fin 32) 0x1F1]
    (blockEnd_cons' ev_at_1142 rfl (blockEnd_cons' ev_at_1146 rfl (blockEnd_cons' ev_at_114a rfl
      (blockEnd_cons' ev_at_114e rfl rfl)))) ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl
    (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have v9 : reg n7 9 = F + BitVec.ofNat 32 0x9F0 := by
    rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
    rw [D6.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl
  obtain ⟨n8, c8, D8, k8, fz8⟩ := D7.zero64 C (d := 0x9F0) ev_at_1152 ev_at_1156 (by decide) (by decide)
    (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]
        rw [D6.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl) (by decide)
  have H8 : S5U.Hasher5At n8.mem (F + BitVec.ofNat 32 0xEF0) h := hasher5_copy H fun j hj => by
    rw [add_ofNat_assoc, zf_out C fz8 (by decide) (by omega) (Or.inr (by omega)),
      zf_out C fz6 (by decide) (by omega) (Or.inr (by omega)), cp_at C fz4 (by decide) hj, add_ofNat_assoc,
      cp_out C fz2 (by decide) (by omega) (Or.inl (by omega))]
  refine ⟨n8, n8.mem, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans c8)))))), D8,
    fun q hq h9 h26 => ?_, ?_, ?_, H8, fun c hc hh => ?_⟩
  · rw [k8 q hq, hr7, evb_reg q D6.st.zero (by revert h9; revert hq; revert q; decide), k6 q hq, hr5,
      evb_reg q D4.st.zero (by revert hq; revert q; decide), k4 q hq, hr3,
      evb_reg q D2.st.zero (by revert h26; revert hq; revert q; decide), k2 q hq, hr1,
      evb_reg q D.st.zero (by revert hq; revert q; decide)]
  · rw [k8 26 (by decide), hr7, evb_reg 26 D6.st.zero (by decide), k6 26 (by decide), hr5,
      evb_reg 26 D4.st.zero (by decide), k4 26 (by decide), v26]
  · rw [k8 9 (by decide), v9]
  · rcases hh with hh | hh | hh | hh <;>
      rw [zf_out C fz8 (by decide) hc (by omega), zf_out C fz6 (by decide) hc (by omega),
        cp_out C fz4 (by decide) hc (by omega), cp_out C fz2 (by decide) hc (by omega)]

end

end C3.RV32




