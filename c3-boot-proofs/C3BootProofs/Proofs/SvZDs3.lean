import C3BootProofs.Proofs.SvZDs2

/-!
# `sigstore::verify`: the second half of a constant-time divstep

From the fourth select's return at 0x1C88 to the jump back at 0x1D60: the
new `u` and `v`, doubled, and `q` and `r` with `±u` and `±v` added when `g`
was odd.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

theorem w64_addq (ql qh zl zh : Word) :
    W64 (ql + zl) ((if (ql + zl).ult zl then 1 else 0) + (zh + qh)) = (W64 ql qh + W64 zl zh) % 2 ^ 64 := by
  rw [BitVec.add_comm (if (ql + zl).ult zl then (1 : Word) else 0)]; exact w64_add' ql qh zl zh

theorem w64_neg' {xl xh : Word} : W64 (0 - xl) (0 - xh - (if (0 : Word).ult xl then 1 else 0)) =
    (2 ^ 64 - W64 xl xh) % 2 ^ 64 := w64_neg xl xh

set_option maxHeartbeats 64000000 in
/-- The second half of a constant-time divstep, from 0x1C88 to the jump
back at 0x1D60. -/
theorem zt_partB {B : Word} {m : Machine} {gl dl dh ul uh vl vh ql qh rl rh cnt : Word}
    (F : Fr B 0x3830) (E : SvCode m.mem) (IC : SvIvCode m.mem) (st : St m.mem SV m 0x1C88 (reg m))
    (hsp : reg m sp = B + 0x21A0) (h27 : reg m (27 : Fin 32) = B + 0x21A0 + 0xA20)
    (h23 : reg m (23 : Fin 32) = ctC3 gl dl dh) (h24 : reg m (24 : Fin 32) = ul) (h21 : reg m (21 : Fin 32) = uh)
    (h9 : reg m (9 : Fin 32) = ql) (h22 : reg m (22 : Fin 32) = qh)
    (w10 : memLoad32 m.mem (B + 0x21A0 + 0x10) = gl &&& 1) (wc : memLoad32 m.mem (B + 0x21A0 + 0xC) = ctC1 dl dh)
    (w48 : memLoad32 m.mem (B + 0x21A0 + 0x48) = cnt)
    (w44 : memLoad32 m.mem (B + 0x21A0 + 0x44) = vl) (w40 : memLoad32 m.mem (B + 0x21A0 + 0x40) = vh)
    (w5c : memLoad32 m.mem (B + 0x21A0 + 0x5C) = rl) (w74 : memLoad32 m.mem (B + 0x21A0 + 0x74) = rh) :
    ∃ m', Steps m m' ∧ SvCode m'.mem ∧ SvIvCode m'.mem ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧
      SvKeepL B m.mem m'.mem ztL ∧ St m'.mem SV m' 0x1D60 (reg m') ∧ reg m' sp = B + 0x21A0 ∧
      reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧ reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧
      reg m' (27 : Fin 32) = B + 0x21A0 + 0xA20 ∧
      (∀ c : Word, c.toNat + 4 ≤ 0x80 → 0x24 ≤ c.toNat → c.toNat + 4 ≤ 0x3C →
        memLoad32 m'.mem (B + 0x21A0 + c) = memLoad32 m.mem (B + 0x21A0 + c)) ∧
      memLoad32 m'.mem (B + 0x21A0 + 0x48) = cnt + 0xFFFFFFFF ∧
      W64 (reg m' (24 : Fin 32)) (memLoad32 m'.mem (B + 0x21A0 + 0x3C)) = 2 * W64 (reg m a0) (reg m a1) % 2 ^ 64 ∧
      W64 (memLoad32 m'.mem (B + 0x21A0 + 0x44)) (memLoad32 m'.mem (B + 0x21A0 + 0x40)) =
        2 * (if ctC3 gl dl dh = 1 then W64 rl rh else W64 vl vh) % 2 ^ 64 ∧
      W64 (memLoad32 m'.mem (B + 0x21A0 + 0x70)) (memLoad32 m'.mem (B + 0x21A0 + 0x60)) =
        (W64 ql qh + (if gl &&& 1 = 1 then
          (if ctC1 dl dh = 1 then (2 ^ 64 - W64 ul uh) % 2 ^ 64 else W64 ul uh) else 0)) % 2 ^ 64 ∧
      W64 (memLoad32 m'.mem (B + 0x21A0 + 0x5C)) (memLoad32 m'.mem (B + 0x21A0 + 0x74)) =
        (W64 rl rh + (if gl &&& 1 = 1 then
          (if ctC1 dl dh = 1 then (2 ^ 64 - W64 vl vh) % 2 ^ 64 else W64 vl vh) else 0)) % 2 ^ 64 := by
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hS : (B + 0x21A0).toNat + 0x1690 ≤ 2 ^ 32 := by have := FS.hi; omega
  have c101 := c1_01 dl dh
  have gb := gb01 gl
  have c301 := and01w gb c101
  have hz := st.zero
  -- the fifth block: store `2u`, both candidates for `v`
  obtain ⟨n1, c1, u1⟩ := st.block zt5 E.self zt5_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, zt5, upd, ↓reduceIte, hsp, and_true, true_and]; zt_ok)
  have s1 : St n1.mem SV n1 0x1CA6 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = (runBlock zt5 (m.mem, reg m)).1 := u1.mem
  have b1 : ∀ q : Fin 32, reg n1 q = (runBlock zt5 (m.mem, reg m)).2 q := u1.regs
  have w1 : ∀ c : Word, c.toNat + 4 ≤ 0x80 → (c.toNat + 4 ≤ 0x14 ∨ 0x1C ≤ c.toNat) →
      memLoad32 n1.mem (B + 0x21A0 + c) = memLoad32 m.mem (B + 0x21A0 + c) := fun c hc h => by
    rw [m1]; simp +decide only [runBlock, BInstr.run, zt5, upd, ↓reduceIte, aluEval, hsp]
    rw [zld_st hS (by decide) (by omega) (by show 0x14 + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0x14; omega),
      zld_st hS (by decide) (by omega) (by show 0x18 + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0x18; omega)]
  have u1v : W64 (memLoad32 n1.mem (B + 0x21A0 + 0x14)) (memLoad32 n1.mem (B + 0x21A0 + 0x18)) =
      2 * W64 (reg m a0) (reg m a1) % 2 ^ 64 := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, zt5, upd, ↓reduceIte, aluEval, hsp]
    simp (disch := decide) only [zld_st hS, memLoad32_store32_same]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    exact w64_shl1 _ _
  have q1 : W64 (reg n1 a3) (reg n1 a4) = W64 rl rh ∧ W64 (reg n1 a1) (reg n1 a2) = W64 vl vh ∧
      reg n1 a0 = ctC3 gl dl dh := by
    refine ⟨?_, ?_, ?_⟩
    · rw [b1, b1]; simp +decide only [runBlock, BInstr.run, zt5, upd, ↓reduceIte, aluEval, hz, hsp]
      simp (disch := decide) only [zld_st hS]
      rw [w5c, w74, w_zadd]
    · rw [b1, b1]; simp +decide only [runBlock, BInstr.run, zt5, upd, ↓reduceIte, aluEval, hz, hsp]
      simp (disch := decide) only [zld_st hS]
      rw [w44, w40, w_zadd, w_zadd]
    · rw [b1]; simp +decide only [runBlock, BInstr.run, zt5, upd, ↓reduceIte, aluEval, hz]
      rw [h23]; exact w_zadd _
  have r1_8 : reg n1 (8 : Fin 32) = vl := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, zt5, upd, ↓reduceIte, aluEval, hsp]
    simp (disch := decide) only [zld_st hS]; exact w44
  have r1_25 : reg n1 (25 : Fin 32) = vh := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, zt5, upd, ↓reduceIte, aluEval, hsp]
    simp (disch := decide) only [zld_st hS]; exact w40
  have r1_20 : reg n1 (20 : Fin 32) = rl := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, zt5, upd, ↓reduceIte, aluEval, hsp]
    simp (disch := decide) only [zld_st hS]; exact w5c
  have k1 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 21, 22, 23, 24, 27] → reg n1 q = reg m q := fun q hq => by
    rw [b1, runBlock_reg _ _ _ _ hz (by revert hq; revert q; decide)]
  have fr1 : ∀ x, SvR B x → n1.mem x = m.mem x := fun x hx => by
    rw [m1]; simp +decide only [runBlock, BInstr.run, zt5, upd, ↓reduceIte, aluEval, hsp]
    simp (disch := decide) only [svR_zst32 hx]
  have K1 : SvKeepL B m.mem n1.mem ztL := fun e he hL => by
    simp only [ztL, List.forall_mem_cons, List.forall_mem_nil, and_true] at hL
    obtain ⟨h1, h2, h3, h4, h5⟩ := hL
    rw [m1]; simp +decide only [runBlock, BInstr.run, zt5, upd, ↓reduceIte, aluEval, hsp]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [zk_st32 hS]
  -- the fifth select: `v` or `r`
  have E1 : SvCode n1.mem := E.fr F fr1
  have IC1 : SvIvCode n1.mem := IC.sv F fr1
  have sp1 : reg n1 sp = B + 0x21A0 := by rw [k1 _ (by decide), hsp]
  have c1' : reg n1 a0 = 0 ∨ reg n1 a0 = 1 := by rw [q1.2.2]; exact c301
  obtain ⟨n2, P2, K2, k2, v20, v21⟩ := sv_si F E1 IC1 s1 sv_at_1ca6 sv_at_1caa (by decide) (by decide) sp1 c1'
  have q2 : W64 (reg n2 a0) (reg n2 a1) = if ctC3 gl dl dh = 1 then W64 rl rh else W64 vl vh := by
    rw [v20, v21, w64_sel c1', q1.2.2, q1.1, q1.2.1]
  have r2 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n2 q = reg n1 q :=
    P2.regs
  have sp2 : reg n2 sp = B + 0x21A0 := by rw [r2 _ (by decide), sp1]
  have E2 : SvCode n2.mem := E1.fr F P2.fr
  have IC2 : SvIvCode n2.mem := IC1.sv F P2.fr
  -- the sixth block: store `2v`, `u` and `-u`
  have z2 := P2.st.zero
  have e2_24 : reg n2 (24 : Fin 32) = ul := by rw [r2 _ (by decide), k1 _ (by decide), h24]
  have e2_21 : reg n2 (21 : Fin 32) = uh := by rw [r2 _ (by decide), k1 _ (by decide), h21]
  obtain ⟨n3, c3, u3⟩ := P2.st.block zt6 E2.self zt6_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, zt6, upd, ↓reduceIte, sp2, and_true, true_and]; zt_ok)
  have m3 : n3.mem = (runBlock zt6 (n2.mem, reg n2)).1 := u3.mem
  have b3 : ∀ q : Fin 32, reg n3 q = (runBlock zt6 (n2.mem, reg n2)).2 q := u3.regs
  have s3 : St n3.mem SV n3 0x1CD2 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have w3 : ∀ c : Word, c.toNat + 4 ≤ 0x80 → (c.toNat + 4 ≤ 0x4 ∨ 0xC ≤ c.toNat) →
      memLoad32 n3.mem (B + 0x21A0 + c) = memLoad32 n2.mem (B + 0x21A0 + c) := fun c hc h => by
    rw [m3]; simp +decide only [runBlock, BInstr.run, zt6, upd, ↓reduceIte, aluEval, sp2]
    rw [zld_st hS (by decide) (by omega) (by show 0x8 + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0x8; omega),
      zld_st hS (by decide) (by omega) (by show 0x4 + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0x4; omega)]
  have v3 : W64 (memLoad32 n3.mem (B + 0x21A0 + 0x4)) (memLoad32 n3.mem (B + 0x21A0 + 0x8)) =
      2 * W64 (reg n2 a0) (reg n2 a1) % 2 ^ 64 := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, zt6, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [zld_st hS, memLoad32_store32_same]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    exact w64_shl1 _ _
  -- frame words that the halves so far left alone
  have wk : ∀ c : Word, c.toNat + 4 ≤ 0x80 → (c.toNat + 4 ≤ 0x4 ∨ 0x1C ≤ c.toNat ∨
      (0xC ≤ c.toNat ∧ c.toNat + 4 ≤ 0x14)) →
      memLoad32 n3.mem (B + 0x21A0 + c) = memLoad32 m.mem (B + 0x21A0 + c) := fun c hc h => by
    rw [w3 c hc (by omega), zkld K2 (by omega) (by simp), w1 c hc (by omega)]
  have q3 : W64 (reg n3 a3) (reg n3 a4) = (2 ^ 64 - W64 ul uh) % 2 ^ 64 ∧ W64 (reg n3 a1) (reg n3 a2) = W64 ul uh ∧
      reg n3 a0 = ctC1 dl dh := by
    refine ⟨?_, ?_, ?_⟩
    · rw [b3, b3]; simp +decide only [runBlock, BInstr.run, zt6, upd, ↓reduceIte, aluEval, z2]
      rw [e2_24, e2_21]; exact w64_neg' 
    · rw [b3, b3]; simp +decide only [runBlock, BInstr.run, zt6, upd, ↓reduceIte, aluEval, z2]
      rw [e2_24, e2_21, w_zadd, w_zadd]
    · rw [b3]; simp +decide only [runBlock, BInstr.run, zt6, upd, ↓reduceIte, aluEval, z2, sp2]
      simp (disch := decide) only [zld_st hS]
      rw [zkld K2 (by decide) (by simp), w1 _ (by decide) (by decide), wc, w_zadd]
  have k3 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 20, 21, 22, 24, 25, 27] → reg n3 q = reg n2 q := fun q hq => by
    rw [b3, runBlock_reg _ _ _ _ z2 (by revert hq; revert q; decide)]
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x hx => by
    rw [m3]; simp +decide only [runBlock, BInstr.run, zt6, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [svR_zst32 hx]
  have K3 : SvKeepL B n2.mem n3.mem ztL := fun e he hL => by
    simp only [ztL, List.forall_mem_cons, List.forall_mem_nil, and_true] at hL
    obtain ⟨h1, h2, h3, h4, h5⟩ := hL
    rw [m3]; simp +decide only [runBlock, BInstr.run, zt6, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [zk_st32 hS]
  -- the sixth select: `u` or `-u`
  have E3 : SvCode n3.mem := E2.fr F fr3
  have IC3 : SvIvCode n3.mem := IC2.sv F fr3
  have sp3 : reg n3 sp = B + 0x21A0 := by rw [k3 _ (by decide), sp2]
  have c3' : reg n3 a0 = 0 ∨ reg n3 a0 = 1 := by rw [q3.2.2]; exact c101
  obtain ⟨n4, P4, K4, k4, v40, v41⟩ := sv_si F E3 IC3 s3 sv_at_1cd2 sv_at_1cd6 (by decide) (by decide) sp3 c3'
  have q4 : W64 (reg n4 a0) (reg n4 a1) = if ctC1 dl dh = 1 then (2 ^ 64 - W64 ul uh) % 2 ^ 64 else W64 ul uh := by
    rw [v40, v41, w64_sel c3', q3.2.2, q3.1, q3.2.1]
  have r4 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg n3 q :=
    P4.regs
  have sp4 : reg n4 sp = B + 0x21A0 := by rw [r4 _ (by decide), sp3]
  have E4 : SvCode n4.mem := E3.fr F P4.fr
  have IC4 : SvIvCode n4.mem := IC3.sv F P4.fr
  have e4_27 : reg n4 (27 : Fin 32) = B + 0x21A0 + 0xA20 := by
    rw [r4 _ (by decide), k3 _ (by decide), r2 _ (by decide), k1 _ (by decide), h27]
  have e4_8 : reg n4 (8 : Fin 32) = vl := by rw [r4 _ (by decide), k3 _ (by decide), r2 _ (by decide), r1_8]
  have e4_25 : reg n4 (25 : Fin 32) = vh := by rw [r4 _ (by decide), k3 _ (by decide), r2 _ (by decide), r1_25]
  have e4_9 : reg n4 (9 : Fin 32) = ql := by
    rw [r4 _ (by decide), k3 _ (by decide), r2 _ (by decide), k1 _ (by decide), h9]
  have e4_22 : reg n4 (22 : Fin 32) = qh := by
    rw [r4 _ (by decide), k3 _ (by decide), r2 _ (by decide), k1 _ (by decide), h22]
  have e4_23 : reg n4 (23 : Fin 32) = ctC1 dl dh := by
    rw [r4 _ (by decide), b3]; simp +decide only [runBlock, BInstr.run, zt6, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [zld_st hS]
    rw [zkld K2 (by decide) (by simp), w1 _ (by decide) (by decide), wc]
  -- the seventh block: `q` updated, `v` and `-v`
  have z4 := P4.st.zero
  obtain ⟨n5, c5, u5⟩ := P4.st.block zt7 E4.self zt7_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, zt7, upd, ↓reduceIte, sp4, e4_27, w_add0, and_true,
      true_and]; zt_ok)
  have m5 : n5.mem = (runBlock zt7 (n4.mem, reg n4)).1 := u5.mem
  have b5 : ∀ q : Fin 32, reg n5 q = (runBlock zt7 (n4.mem, reg n4)).2 q := u5.regs
  have s5 : St n5.mem SV n5 0x1D1E (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have g10 : memLoad32 n4.mem (B + 0x21A0 + 0x10) = gl &&& 1 := by
    rw [zkld K4 (by decide) (by simp), wk _ (by decide) (by decide), w10]
  have w5 : ∀ c : Word, c.toNat + 4 ≤ 0x80 → (c.toNat + 4 ≤ 0x60 ∨ 0x74 ≤ c.toNat ∨
      (0x64 ≤ c.toNat ∧ c.toNat + 4 ≤ 0x70)) →
      memLoad32 n5.mem (B + 0x21A0 + c) = memLoad32 n4.mem (B + 0x21A0 + c) := fun c hc h => by
    rw [m5]; simp +decide only [runBlock, BInstr.run, zt7, upd, ↓reduceIte, aluEval, sp4, e4_27, w_add0]
    rw [zld_st hS (by decide) (by omega) (by show 0x60 + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0x60; omega),
      zld_st hS (by decide) (by omega) (by show 0x70 + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0x70; omega),
      zld_st8 hS (by decide) (by omega) (by show 0xA20 + 1 ≤ c.toNat ∨ c.toNat + 4 ≤ 0xA20; omega)]
  have q5n : W64 (memLoad32 n5.mem (B + 0x21A0 + 0x70)) (memLoad32 n5.mem (B + 0x21A0 + 0x60)) =
      (W64 ql qh + (if gl &&& 1 = 1 then
        (if ctC1 dl dh = 1 then (2 ^ 64 - W64 ul uh) % 2 ^ 64 else W64 ul uh) else 0)) % 2 ^ 64 := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, zt7, upd, ↓reduceIte, aluEval, sp4, e4_27, w_add0, z4]
    simp (disch := decide) only [zld_st hS, zld_st8 hS, zst32_get hS, memStore8_same, memLoad32_store32_same]
    rw [g10, zext_trunc01 gb, mask01 gb, mask01' gb, e4_9, e4_22, w64_addq, w64_mask, q4]
  have q5 : W64 (reg n5 a3) (reg n5 a4) = (2 ^ 64 - W64 vl vh) % 2 ^ 64 ∧ W64 (reg n5 a1) (reg n5 a2) = W64 vl vh ∧
      reg n5 a0 = ctC1 dl dh := by
    refine ⟨?_, ?_, ?_⟩
    · rw [b5, b5]; simp +decide only [runBlock, BInstr.run, zt7, upd, ↓reduceIte, aluEval, z4]
      rw [e4_8, e4_25]; exact w64_neg'
    · rw [b5, b5]; simp +decide only [runBlock, BInstr.run, zt7, upd, ↓reduceIte, aluEval, z4]
      rw [e4_8, e4_25, w_zadd, w_zadd]
    · rw [b5]; simp +decide only [runBlock, BInstr.run, zt7, upd, ↓reduceIte, aluEval, z4]
      rw [e4_23, w_zadd]
  have r5_24 : reg n5 (24 : Fin 32) = gl &&& 1 := by
    rw [b5]; simp +decide only [runBlock, BInstr.run, zt7, upd, ↓reduceIte, aluEval, sp4]
    exact g10
  have k5 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 20, 25, 27] → reg n5 q = reg n4 q := fun q hq => by
    rw [b5, runBlock_reg _ _ _ _ z4 (by revert hq; revert q; decide)]
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x hx => by
    rw [m5]; simp +decide only [runBlock, BInstr.run, zt7, upd, ↓reduceIte, aluEval, sp4, e4_27, w_add0]
    simp (disch := decide) only [svR_zst32 hx, svR_zst8 hx]
  have K5 : SvKeepL B n4.mem n5.mem ztL := fun e he hL => by
    simp only [ztL, List.forall_mem_cons, List.forall_mem_nil, and_true] at hL
    obtain ⟨h1, h2, h3, h4, h5⟩ := hL
    rw [m5]; simp +decide only [runBlock, BInstr.run, zt7, upd, ↓reduceIte, aluEval, sp4, e4_27, w_add0]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [zk_st32 hS, zk_st8 hS]
  -- the seventh select: `v` or `-v`
  have E5 : SvCode n5.mem := E4.fr F fr5
  have IC5 : SvIvCode n5.mem := IC4.sv F fr5
  have sp5 : reg n5 sp = B + 0x21A0 := by rw [k5 _ (by decide), sp4]
  have c5' : reg n5 a0 = 0 ∨ reg n5 a0 = 1 := by rw [q5.2.2]; exact c101
  obtain ⟨n6, P6, K6, k6, v60, v61⟩ := sv_si F E5 IC5 s5 sv_at_1d1e sv_at_1d22 (by decide) (by decide) sp5 c5'
  have q6 : W64 (reg n6 a0) (reg n6 a1) = if ctC1 dl dh = 1 then (2 ^ 64 - W64 vl vh) % 2 ^ 64 else W64 vl vh := by
    rw [v60, v61, w64_sel c5', q5.2.2, q5.1, q5.2.1]
  have r6 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n6 q = reg n5 q :=
    P6.regs
  have sp6 : reg n6 sp = B + 0x21A0 := by rw [r6 _ (by decide), sp5]
  have E6 : SvCode n6.mem := E5.fr F P6.fr
  have IC6 : SvIvCode n6.mem := IC5.sv F P6.fr
  have e6_27 : reg n6 (27 : Fin 32) = B + 0x21A0 + 0xA20 := by rw [r6 _ (by decide), k5 _ (by decide), e4_27]
  have e6_24 : reg n6 (24 : Fin 32) = gl &&& 1 := by rw [r6 _ (by decide), r5_24]
  have e6_20 : reg n6 (20 : Fin 32) = rl := by
    rw [r6 _ (by decide), k5 _ (by decide), r4 _ (by decide), k3 _ (by decide), r2 _ (by decide), r1_20]
  -- the eighth block: `r` updated, the new `u` and `v` moved, the count decremented
  have z6 := P6.st.zero
  obtain ⟨n7, c7, u7⟩ := P6.st.block zt8 E6.self zt8_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, zt8, upd, ↓reduceIte, sp6, e6_27, w_add0, and_true,
      true_and]; zt_ok)
  have m7 : n7.mem = (runBlock zt8 (n6.mem, reg n6)).1 := u7.mem
  have b7 : ∀ q : Fin 32, reg n7 q = (runBlock zt8 (n6.mem, reg n6)).2 q := u7.regs
  -- frame words of `n6` from before
  have x6 : ∀ c : Word, c.toNat + 4 ≤ 0x80 → (c.toNat + 4 ≤ 0x60 ∨ 0x74 ≤ c.toNat ∨
      (0x64 ≤ c.toNat ∧ c.toNat + 4 ≤ 0x70)) →
      memLoad32 n6.mem (B + 0x21A0 + c) = memLoad32 n4.mem (B + 0x21A0 + c) := fun c hc h => by
    rw [zkld K6 (by omega) (by simp), w5 c hc h]
  have y4 : ∀ c : Word, c.toNat + 4 ≤ 0x80 → (c.toNat + 4 ≤ 0x4 ∨ 0x1C ≤ c.toNat ∨
      (0xC ≤ c.toNat ∧ c.toNat + 4 ≤ 0x14)) →
      memLoad32 n4.mem (B + 0x21A0 + c) = memLoad32 m.mem (B + 0x21A0 + c) := fun c hc h => by
    rw [zkld K4 (by omega) (by simp), wk c hc h]
  have v4 : ∀ c : Word, c.toNat + 4 ≤ 0x80 → (c.toNat + 4 ≤ 0x4 ∨ 0xC ≤ c.toNat) →
      memLoad32 n4.mem (B + 0x21A0 + c) = memLoad32 n2.mem (B + 0x21A0 + c) := fun c hc h => by
    rw [zkld K4 (by omega) (by simp), w3 c hc (by omega)]
  have w7 : ∀ c : Word, c.toNat + 4 ≤ 0x80 → (c.toNat + 4 ≤ 0x3C ∨ (0x4C ≤ c.toNat ∧ c.toNat + 4 ≤ 0x5C) ∨
      (0x60 ≤ c.toNat ∧ c.toNat + 4 ≤ 0x74) ∨ 0x78 ≤ c.toNat) →
      memLoad32 n7.mem (B + 0x21A0 + c) = memLoad32 n6.mem (B + 0x21A0 + c) := fun c hc h => by
    rw [m7]; simp +decide only [runBlock, BInstr.run, zt8, upd, ↓reduceIte, aluEval, sp6, e6_27, w_add0]
    rw [zld_st hS (by decide) (by omega) (by show 0x3C + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0x3C; omega),
      zld_st hS (by decide) (by omega) (by show 0x74 + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0x74; omega),
      zld_st hS (by decide) (by omega) (by show 0x40 + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0x40; omega),
      zld_st hS (by decide) (by omega) (by show 0x5C + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0x5C; omega),
      zld_st hS (by decide) (by omega) (by show 0x44 + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0x44; omega),
      zld_st hS (by decide) (by omega) (by show 0x48 + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0x48; omega),
      zld_st8 hS (by decide) (by omega) (by show 0xA20 + 1 ≤ c.toNat ∨ c.toNat + 4 ≤ 0xA20; omega)]
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x hx => by
    rw [m7]; simp +decide only [runBlock, BInstr.run, zt8, upd, ↓reduceIte, aluEval, sp6, e6_27, w_add0]
    simp (disch := decide) only [svR_zst32 hx, svR_zst8 hx]
  have K7 : SvKeepL B n6.mem n7.mem ztL := fun e he hL => by
    simp only [ztL, List.forall_mem_cons, List.forall_mem_nil, and_true] at hL
    obtain ⟨h1, h2, h3, h4, h5⟩ := hL
    rw [m7]; simp +decide only [runBlock, BInstr.run, zt8, upd, ↓reduceIte, aluEval, sp6, e6_27, w_add0]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [zk_st32 hS, zk_st8 hS]
  have k7 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 27] → reg n7 q = reg n6 q := fun q hq => by
    rw [b7, runBlock_reg _ _ _ _ z6 (by revert hq; revert q; decide)]
  have e6_3 : ∀ q : Fin 32, q.val ∈ [3, 4] → reg n6 q = reg m q := fun q hq => by
    rw [r6 q (by revert hq; revert q; decide), k5 q (by revert hq; revert q; decide),
      r4 q (by revert hq; revert q; decide), k3 q (by revert hq; revert q; decide),
      r2 q (by revert hq; revert q; decide), k1 q (by revert hq; revert q; decide)]
  -- the slots of `n6` the eighth block reads
  have n6_48 : memLoad32 n6.mem (B + 0x21A0 + 0x48) = cnt := by
    rw [x6 _ (by decide) (by decide), y4 _ (by decide) (by decide), w48]
  have n6_74 : memLoad32 n6.mem (B + 0x21A0 + 0x74) = rh := by
    rw [x6 _ (by decide) (by decide), y4 _ (by decide) (by decide), w74]
  have n6_v : W64 (memLoad32 n6.mem (B + 0x21A0 + 0x4)) (memLoad32 n6.mem (B + 0x21A0 + 0x8)) =
      2 * (if ctC3 gl dl dh = 1 then W64 rl rh else W64 vl vh) % 2 ^ 64 := by
    rw [x6 _ (by decide) (by decide), x6 _ (by decide) (by decide), zkld K4 (by decide) (by simp),
      zkld K4 (by decide) (by simp), v3, q2]
  have n6_u : W64 (memLoad32 n6.mem (B + 0x21A0 + 0x14)) (memLoad32 n6.mem (B + 0x21A0 + 0x18)) =
      2 * W64 (reg m a0) (reg m a1) % 2 ^ 64 := by
    rw [x6 _ (by decide) (by decide), x6 _ (by decide) (by decide), v4 _ (by decide) (by decide),
      v4 _ (by decide) (by decide), zkld K2 (by decide) (by simp), zkld K2 (by decide) (by simp), u1v]
  have p6 : W64 (memLoad32 n6.mem (B + 0x21A0 + 0x70)) (memLoad32 n6.mem (B + 0x21A0 + 0x60)) =
      (W64 ql qh + (if gl &&& 1 = 1 then
        (if ctC1 dl dh = 1 then (2 ^ 64 - W64 ul uh) % 2 ^ 64 else W64 ul uh) else 0)) % 2 ^ 64 := by
    rw [zkld K6 (by decide) (by simp), zkld K6 (by decide) (by simp), q5n]
  refine ⟨n7, c1.trans (P2.steps.trans (c3.trans (P4.steps.trans (c5.trans (P6.steps.trans c7))))),
    E6.fr F fr7, IC6.sv F fr7,
    fun x hx => by rw [fr7 x hx, P6.fr x hx, fr5 x hx, P4.fr x hx, fr3 x hx, P2.fr x hx, fr1 x hx],
    fun e he hL => by
      rw [K7 e he hL, K6 e he (by simp), K5 e he hL, K4 e he (by simp), K3 e he hL, K2 e he (by simp), K1 e he hL],
    ⟨u7.pc, rfl, fun _ => rfl⟩, by rw [k7 _ (by decide), sp6], by rw [k7 _ (by decide), e6_3 _ (by decide)],
    by rw [k7 _ (by decide), e6_3 _ (by decide)], by rw [k7 _ (by decide), e6_27],
    fun c hc h1 h2 => by
      rw [w7 c hc (by omega), x6 c hc (by omega), y4 c hc (by omega)], ?_, ?_, ?_, p6.symm ▸ ?_, ?_⟩
  · rw [m7]; simp +decide only [runBlock, BInstr.run, zt8, upd, ↓reduceIte, aluEval, sp6, e6_27, w_add0]
    simp (disch := decide) only [zld_st hS, zld_st8 hS, memLoad32_store32_same]
    rw [n6_48]
  · rw [b7, m7]; simp +decide only [runBlock, BInstr.run, zt8, upd, ↓reduceIte, aluEval, sp6, e6_27, w_add0]
    simp (disch := decide) only [zld_st hS, zld_st8 hS, memLoad32_store32_same]
    exact n6_u
  · rw [m7]; simp +decide only [runBlock, BInstr.run, zt8, upd, ↓reduceIte, aluEval, sp6, e6_27, w_add0]
    simp (disch := decide) only [zld_st hS, zld_st8 hS, memLoad32_store32_same]
    exact n6_v
  · rw [w7 _ (by decide) (by decide), w7 _ (by decide) (by decide)]
  · rw [m7]; simp +decide only [runBlock, BInstr.run, zt8, upd, ↓reduceIte, aluEval, sp6, e6_27, w_add0, z6]
    simp (disch := decide) only [zld_st hS, zld_st8 hS, zst32_get hS, memStore8_same, memLoad32_store32_same]
    rw [e6_24, zext_trunc01 gb, mask01 gb, mask01' gb, e6_20, n6_74, w64_addq, w64_mask, q6]

end C3.RV32.Sv
