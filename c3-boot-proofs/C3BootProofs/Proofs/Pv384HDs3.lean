import C3BootProofs.Proofs.Pv384HDs2

/-!
# `p384_verify_prehash`: the second half of a constant-time divstep

From the fifth select at 0xE36 to the branch at 0xEFE: the new `v`, `q`,
and `r`.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

theorem add_7ff (S : Word) : S + 0x7FF + 0x581 = S + 0xD80 := by rw [BitVec.add_assoc]; rfl

theorem add_d94 (S : Word) : S + 0xD80 + 0x514 = S + 0x1294 := by rw [BitVec.add_assoc]; rfl

theorem dec_ofNat (r : Nat) : BitVec.ofNat 32 (r + 1) + 0xFFFFFFFF = BitVec.ofNat 32 r := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 0xFFFFFFFF from rfl]
  omega

set_option maxHeartbeats 64000000 in
/-- The second half of a constant-time divstep, from 0xE36 to 0xEFE. -/
theorem ct_partB {B : Word} {m : Machine} {n : Nat} {dl dh gl ul uh vl vh ql qh rl rh : Word}
    (F : Fr B 0x21A0) (E : PvEnv3 m.mem) (st : St m.mem PV m 0xE36 (reg m)) (hsp : reg m sp = B + 0x420)
    (ha0 : reg m a0 = ctC3 gl dl dh) (ha1 : reg m a1 = vl) (ha2 : reg m a2 = vh) (ha3 : reg m a3 = rl)
    (ha4 : reg m a4 = rh) (h8 : reg m (8 : Fin 32) = vh) (h18 : reg m (18 : Fin 32) = ql)
    (h19 : reg m (19 : Fin 32) = vl) (h21 : reg m (21 : Fin 32) = rh) (h22 : reg m (22 : Fin 32) = rl)
    (h23 : reg m (23 : Fin 32) = ul) (h25 : reg m (25 : Fin 32) = qh) (h26 : reg m (26 : Fin 32) = uh)
    (h27 : reg m (27 : Fin 32) = gl &&& 1) (w3c : memLoad32 m.mem (B + 0x420 + 0x3C) = BitVec.ofNat 32 (n + 1))
    (w24 : memLoad32 m.mem (B + 0x420 + 0x24) = ctC1 dl dh) :
    ∃ m', Steps m m' ∧ PvEnv3 m'.mem ∧ (∀ x, PvR B x → m'.mem x = m.mem x) ∧
      (∀ e, e + 1 ≤ 0x1D4C → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0x1294 →
        m'.mem (B + 0x420 + BitVec.ofNat 32 e) = m.mem (B + 0x420 + BitVec.ofNat 32 e)) ∧
      St m'.mem PV m' 0xEFE (reg m') ∧ reg m' sp = B + 0x420 ∧ reg m' (8 : Fin 32) = B + 0x420 + 0xD80 ∧
      reg m' a4 = BitVec.ofNat 32 n ∧ reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧
      reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧
      memLoad32 m'.mem (B + 0x420 + 0x40) = memLoad32 m.mem (B + 0x420 + 0x40) ∧
      memLoad32 m'.mem (B + 0x420 + 0x50) = memLoad32 m.mem (B + 0x420 + 0x50) ∧
      memLoad32 m'.mem (B + 0x420 + 0x48) = memLoad32 m.mem (B + 0x420 + 0x48) ∧
      memLoad32 m'.mem (B + 0x420 + 0x44) = memLoad32 m.mem (B + 0x420 + 0x44) ∧
      memLoad32 m'.mem (B + 0x420 + 0x4C) = memLoad32 m.mem (B + 0x420 + 0x4C) ∧
      reg m' (24 : Fin 32) = memLoad32 m.mem (B + 0x420 + 0x38) ∧
      reg m' (23 : Fin 32) = memLoad32 m.mem (B + 0x420 + 0x2C) ∧
      reg m' (26 : Fin 32) = memLoad32 m.mem (B + 0x420 + 0x34) ∧
      W64 (reg m' (20 : Fin 32)) (reg m' (25 : Fin 32)) =
        2 * (if ctC3 gl dl dh = 1 then W64 rl rh else W64 vl vh) % 2 ^ 64 ∧
      W64 (memLoad32 m'.mem (B + 0x420 + 0x54)) (reg m' (18 : Fin 32)) =
        (W64 ql qh + (if gl &&& 1 = 1 then
          (if ctC1 dl dh = 1 then (2 ^ 64 - W64 ul uh) % 2 ^ 64 else W64 ul uh) else 0)) % 2 ^ 64 ∧
      W64 (reg m' (22 : Fin 32)) (reg m' (13 : Fin 32)) =
        (W64 rl rh + (if gl &&& 1 = 1 then
          (if ctC1 dl dh = 1 then (2 ^ 64 - W64 vl vh) % 2 ^ 64 else W64 vl vh) else 0)) % 2 ^ 64 := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hS : (B + 0x420).toNat + 0x1D80 ≤ 2 ^ 32 := by have := FS.hi; omega
  have c3 : reg m a0 = 0 ∨ reg m a0 = 1 := by rw [ha0]; exact and01w (gb01 gl) (c1_01 dl dh)
  have c1 : ctC1 dl dh = 0 ∨ ctC1 dl dh = 1 := c1_01 dl dh
  have mk := gb01 gl
  -- the fifth select: `v` or `r`
  obtain ⟨n10, P10, K10, k10, v100, v101⟩ := pv_si F E st pv_at_e36 pv_at_e3a (by decide) (by decide) hsp c3
  have q10 : W64 (reg n10 a0) (reg n10 a1) = if ctC3 gl dl dh = 1 then W64 rl rh else W64 vl vh := by
    rw [v100, v101, w64_sel c3, ha0, ha3, ha4, ha1, ha2]
  have E10 : PvEnv3 n10.mem := E.fr F P10.fr
  have r10 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n10 q = reg m q := P10.regs
  have sp10 : reg n10 sp = B + 0x420 := by rw [r10 _ (by decide), hsp]
  have z10 := P10.st.zero
  -- segment 6, to the sixth select at 0xE62: store `v`, and `u` and `-u`
  obtain ⟨n11, c11, u11⟩ := P10.st.block ctS6 E10.E.C.self ctS6_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, ctS6, upd, ↓reduceIte, sp10, add_7ff, add_d80, and_true, true_and]; ct_ok)
  have m11 : n11.mem = (runBlock ctS6 (n10.mem, reg n10)).1 := u11.mem
  have b11 : ∀ q : Fin 32, reg n11 q = (runBlock ctS6 (n10.mem, reg n10)).2 q := u11.regs
  have s11 : St n11.mem PV n11 0xE62 (reg n11) := ⟨u11.pc, rfl, fun _ => rfl⟩
  have v11 : W64 (reg n11 (20 : Fin 32)) (memLoad32 n11.mem (B + 0x420 + 0x20)) =
      2 * W64 (reg n10 a0) (reg n10 a1) % 2 ^ 64 := by
    rw [m11, b11]; simp +decide only [runBlock, BInstr.run, ctS6, upd, ↓reduceIte, aluEval, sp10]
    simp (disch := decide) only [ldst_ne hS, memLoad32_store32_same]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    exact w64_shl1 _ _
  have nu11 : W64 (reg n11 a3) (reg n11 a4) = (2 ^ 64 - W64 ul uh) % 2 ^ 64 := by
    rw [b11, b11]; simp +decide only [runBlock, BInstr.run, ctS6, upd, ↓reduceIte, aluEval, z10]
    rw [r10 _ (by decide), r10 _ (by decide), h23, h26]; exact w64_neg _ _
  have r11_10 : reg n11 a0 = ctC1 dl dh := by
    rw [b11]; simp +decide only [runBlock, BInstr.run, ctS6, upd, ↓reduceIte, aluEval, sp10, z10]
    simp (disch := decide) only [ldst_ne hS]; rw [kld K10 (by decide), w24]; exact BitVec.zero_add _
  have r11_9 : reg n11 (9 : Fin 32) = ctC1 dl dh := by
    rw [b11]; simp +decide only [runBlock, BInstr.run, ctS6, upd, ↓reduceIte, aluEval, sp10]
    simp (disch := decide) only [ldst_ne hS]; rw [kld K10 (by decide), w24]
  have r11_11 : reg n11 a1 = ul := by
    rw [b11]; simp +decide only [runBlock, BInstr.run, ctS6, upd, ↓reduceIte, aluEval, z10]
    rw [r10 _ (by decide), h23]; exact BitVec.zero_add _
  have r11_12 : reg n11 a2 = uh := by
    rw [b11]; simp +decide only [runBlock, BInstr.run, ctS6, upd, ↓reduceIte, aluEval, z10]
    rw [r10 _ (by decide), h26]; exact BitVec.zero_add _
  have r11k : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 18, 19, 21, 22, 23, 24, 25, 26, 27] → reg n11 q = reg n10 q := fun q hq => by
    rw [b11, runBlock_reg _ _ _ _ z10 (by revert hq; revert q; decide)]
  have w40_11 : memLoad32 n11.mem (B + 0x420 + 0x40) = memLoad32 m.mem (B + 0x420 + 0x40) := by
    rw [m11]; simp +decide only [runBlock, BInstr.run, ctS6, upd, ↓reduceIte, aluEval, sp10, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K10 (by decide)]
  have w38_11 : memLoad32 n11.mem (B + 0x420 + 0x38) = memLoad32 m.mem (B + 0x420 + 0x38) := by
    rw [m11]; simp +decide only [runBlock, BInstr.run, ctS6, upd, ↓reduceIte, aluEval, sp10, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K10 (by decide)]
  have w50_11 : memLoad32 n11.mem (B + 0x420 + 0x50) = memLoad32 m.mem (B + 0x420 + 0x50) := by
    rw [m11]; simp +decide only [runBlock, BInstr.run, ctS6, upd, ↓reduceIte, aluEval, sp10, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K10 (by decide)]
  have w48_11 : memLoad32 n11.mem (B + 0x420 + 0x48) = memLoad32 m.mem (B + 0x420 + 0x48) := by
    rw [m11]; simp +decide only [runBlock, BInstr.run, ctS6, upd, ↓reduceIte, aluEval, sp10, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K10 (by decide)]
  have w44_11 : memLoad32 n11.mem (B + 0x420 + 0x44) = memLoad32 m.mem (B + 0x420 + 0x44) := by
    rw [m11]; simp +decide only [runBlock, BInstr.run, ctS6, upd, ↓reduceIte, aluEval, sp10, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K10 (by decide)]
  have w4c_11 : memLoad32 n11.mem (B + 0x420 + 0x4C) = memLoad32 m.mem (B + 0x420 + 0x4C) := by
    rw [m11]; simp +decide only [runBlock, BInstr.run, ctS6, upd, ↓reduceIte, aluEval, sp10, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K10 (by decide)]
  have w2c_11 : memLoad32 n11.mem (B + 0x420 + 0x2C) = memLoad32 m.mem (B + 0x420 + 0x2C) := by
    rw [m11]; simp +decide only [runBlock, BInstr.run, ctS6, upd, ↓reduceIte, aluEval, sp10, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K10 (by decide)]
  have w34_11 : memLoad32 n11.mem (B + 0x420 + 0x34) = memLoad32 m.mem (B + 0x420 + 0x34) := by
    rw [m11]; simp +decide only [runBlock, BInstr.run, ctS6, upd, ↓reduceIte, aluEval, sp10, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K10 (by decide)]
  have w3c_11 : memLoad32 n11.mem (B + 0x420 + 0x3C) = memLoad32 m.mem (B + 0x420 + 0x3C) := by
    rw [m11]; simp +decide only [runBlock, BInstr.run, ctS6, upd, ↓reduceIte, aluEval, sp10, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K10 (by decide)]
  have fr11 : ∀ x, PvR B x → n11.mem x = m.mem x := fun x hx => by
    rw [m11]; simp +decide only [runBlock, BInstr.run, ctS6, upd, ↓reduceIte, aluEval, sp10, add_d80]
    simp (disch := decide) only [pvR_st32 hx, pvR_st8 hx]; rw [P10.fr x hx]
  have fk11 : ∀ e, e + 1 ≤ 0x1D4C → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0x1294 →
      n11.mem (B + 0x420 + BitVec.ofNat 32 e) = m.mem (B + 0x420 + BitVec.ofNat 32 e) := fun e he h1 h2 => by
    rw [m11]; simp +decide only [runBlock, BInstr.run, ctS6, upd, ↓reduceIte, aluEval, sp10, add_d80]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [fk_st32 hS, fk_st8 hS]
    rw [kfk K10 he]
  -- the sixth select: `u` or `-u`
  have E11 : PvEnv3 n11.mem := E.fr F fr11
  have sp11 : reg n11 sp = B + 0x420 := by rw [b11, runBlock_reg _ _ _ _ z10 (by decide), sp10]
  obtain ⟨n12, P12, K12, k12, v120, v121⟩ := pv_si F E11 s11 pv_at_e62 pv_at_e66 (by decide) (by decide) sp11
    (by rw [r11_10]; exact c1)
  have q12 : W64 (reg n12 a0) (reg n12 a1) = if ctC1 dl dh = 1 then (2 ^ 64 - W64 ul uh) % 2 ^ 64 else W64 ul uh := by
    rw [v120, v121, r11_10, w64_sel c1, nu11, r11_11, r11_12]
  have E12 : PvEnv3 n12.mem := E11.fr F P12.fr
  have r12 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n12 q = reg n11 q := P12.regs
  have sp12 : reg n12 sp = B + 0x420 := by rw [r12 _ (by decide), sp11]
  have z12 := P12.st.zero
  -- segment 7, to the last select at 0xEC6: the new `q`, and `v` and `-v`
  obtain ⟨n13, c13, u13⟩ := P12.st.block ctS7 E12.E.C.self ctS7_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, ctS7, upd, ↓reduceIte, aluEval, sp12, add_7ff, add_d80, and_true, true_and]; ct_ok)
  have m13 : n13.mem = (runBlock ctS7 (n12.mem, reg n12)).1 := u13.mem
  have b13 : ∀ q : Fin 32, reg n13 q = (runBlock ctS7 (n12.mem, reg n12)).2 q := u13.regs
  have s13 : St n13.mem PV n13 0xEC6 (reg n13) := ⟨u13.pc, rfl, fun _ => rfl⟩
  have e12 : ∀ q : Fin 32, q.val ∈ [8, 18, 19, 25, 27] → reg n12 q = reg m q := fun q hq => by
    rw [r12 q (by revert hq; revert q; decide), r11k q (by revert hq; revert q; decide),
      r10 q (by revert hq; revert q; decide)]
  have q13 : W64 (memLoad32 n13.mem (B + 0x420 + 0x54)) (reg n13 (18 : Fin 32)) =
      (W64 ql qh + (if gl &&& 1 = 1 then W64 (reg n12 a0) (reg n12 a1) else 0)) % 2 ^ 64 := by
    rw [m13, b13]; simp +decide only [runBlock, BInstr.run, ctS7, upd, ↓reduceIte, aluEval, sp12, add_7ff, add_d80]
    simp (disch := decide) only [ldst_ne hS, memLoad32_store32_same, memStore8_same]
    rw [e12 (18 : Fin 32) (by decide), e12 (25 : Fin 32) (by decide), e12 (27 : Fin 32) (by decide), h18, h25, h27, zext_trunc01 mk, mask01 mk,
      mask01' mk, ← w64_mask]
    exact w64_add' _ _ _ _
  have nv13 : W64 (reg n13 a3) (reg n13 a4) = (2 ^ 64 - W64 vl vh) % 2 ^ 64 := by
    rw [b13, b13]; simp +decide only [runBlock, BInstr.run, ctS7, upd, ↓reduceIte, aluEval, z12]
    rw [e12 _ (by decide), e12 _ (by decide), h19, h8]; exact w64_neg _ _
  have r13_10 : reg n13 a0 = ctC1 dl dh := by
    rw [b13]; simp +decide only [runBlock, BInstr.run, ctS7, upd, ↓reduceIte, aluEval, z12]
    rw [r12 _ (by decide), r11_9]; exact BitVec.zero_add _
  have r13_11 : reg n13 a1 = vl := by
    rw [b13]; simp +decide only [runBlock, BInstr.run, ctS7, upd, ↓reduceIte, aluEval, z12]
    rw [e12 _ (by decide), h19]; exact BitVec.zero_add _
  have r13_12 : reg n13 a2 = vh := by
    rw [b13]; simp +decide only [runBlock, BInstr.run, ctS7, upd, ↓reduceIte, aluEval, z12]
    rw [e12 _ (by decide), h8]; exact BitVec.zero_add _
  have r13_24 : reg n13 (24 : Fin 32) = B + 0x420 + 0xD80 := by
    rw [b13]; simp +decide only [runBlock, BInstr.run, ctS7, upd, ↓reduceIte, aluEval, sp12]
    rw [BitVec.add_assoc]; rfl
  have r13k : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 19, 20, 21, 22, 25, 26, 27] → reg n13 q = reg n12 q := fun q hq => by
    rw [b13, runBlock_reg _ _ _ _ z12 (by revert hq; revert q; decide)]
  have w40_13 : memLoad32 n13.mem (B + 0x420 + 0x40) = memLoad32 n11.mem (B + 0x420 + 0x40) := by
    rw [m13]; simp +decide only [runBlock, BInstr.run, ctS7, upd, ↓reduceIte, aluEval, sp12, add_7ff, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K12 (by decide)]
  have w38_13 : memLoad32 n13.mem (B + 0x420 + 0x38) = memLoad32 n11.mem (B + 0x420 + 0x38) := by
    rw [m13]; simp +decide only [runBlock, BInstr.run, ctS7, upd, ↓reduceIte, aluEval, sp12, add_7ff, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K12 (by decide)]
  have w50_13 : memLoad32 n13.mem (B + 0x420 + 0x50) = memLoad32 n11.mem (B + 0x420 + 0x50) := by
    rw [m13]; simp +decide only [runBlock, BInstr.run, ctS7, upd, ↓reduceIte, aluEval, sp12, add_7ff, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K12 (by decide)]
  have w48_13 : memLoad32 n13.mem (B + 0x420 + 0x48) = memLoad32 n11.mem (B + 0x420 + 0x48) := by
    rw [m13]; simp +decide only [runBlock, BInstr.run, ctS7, upd, ↓reduceIte, aluEval, sp12, add_7ff, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K12 (by decide)]
  have w44_13 : memLoad32 n13.mem (B + 0x420 + 0x44) = memLoad32 n11.mem (B + 0x420 + 0x44) := by
    rw [m13]; simp +decide only [runBlock, BInstr.run, ctS7, upd, ↓reduceIte, aluEval, sp12, add_7ff, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K12 (by decide)]
  have w4c_13 : memLoad32 n13.mem (B + 0x420 + 0x4C) = memLoad32 n11.mem (B + 0x420 + 0x4C) := by
    rw [m13]; simp +decide only [runBlock, BInstr.run, ctS7, upd, ↓reduceIte, aluEval, sp12, add_7ff, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K12 (by decide)]
  have w2c_13 : memLoad32 n13.mem (B + 0x420 + 0x2C) = memLoad32 n11.mem (B + 0x420 + 0x2C) := by
    rw [m13]; simp +decide only [runBlock, BInstr.run, ctS7, upd, ↓reduceIte, aluEval, sp12, add_7ff, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K12 (by decide)]
  have w34_13 : memLoad32 n13.mem (B + 0x420 + 0x34) = memLoad32 n11.mem (B + 0x420 + 0x34) := by
    rw [m13]; simp +decide only [runBlock, BInstr.run, ctS7, upd, ↓reduceIte, aluEval, sp12, add_7ff, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K12 (by decide)]
  have w3c_13 : memLoad32 n13.mem (B + 0x420 + 0x3C) = memLoad32 n11.mem (B + 0x420 + 0x3C) := by
    rw [m13]; simp +decide only [runBlock, BInstr.run, ctS7, upd, ↓reduceIte, aluEval, sp12, add_7ff, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K12 (by decide)]
  have w20_13 : memLoad32 n13.mem (B + 0x420 + 0x20) = memLoad32 n11.mem (B + 0x420 + 0x20) := by
    rw [m13]; simp +decide only [runBlock, BInstr.run, ctS7, upd, ↓reduceIte, aluEval, sp12, add_7ff, add_d80]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld K12 (by decide)]
  have fr13 : ∀ x, PvR B x → n13.mem x = m.mem x := fun x hx => by
    rw [m13]; simp +decide only [runBlock, BInstr.run, ctS7, upd, ↓reduceIte, aluEval, sp12, add_7ff, add_d80]
    simp (disch := decide) only [pvR_st32 hx, pvR_st8 hx]; rw [P12.fr x hx, fr11 x hx]
  have fk13 : ∀ e, e + 1 ≤ 0x1D4C → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0x1294 →
      n13.mem (B + 0x420 + BitVec.ofNat 32 e) = m.mem (B + 0x420 + BitVec.ofNat 32 e) := fun e he h1 h2 => by
    rw [m13]; simp +decide only [runBlock, BInstr.run, ctS7, upd, ↓reduceIte, aluEval, sp12, add_7ff, add_d80]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [fk_st32 hS, fk_st8 hS]
    rw [kfk K12 he, fk11 e he h1 h2]
  -- the last select: `v` or `-v`
  have E13 : PvEnv3 n13.mem := E.fr F fr13
  have sp13 : reg n13 sp = B + 0x420 := by rw [b13, runBlock_reg _ _ _ _ z12 (by decide), sp12]
  obtain ⟨n14, P14, K14, k14, v140, v141⟩ := pv_si F E13 s13 pv_at_ec6 pv_at_eca (by decide) (by decide) sp13
    (by rw [r13_10]; exact c1)
  have q14 : W64 (reg n14 a0) (reg n14 a1) = if ctC1 dl dh = 1 then (2 ^ 64 - W64 vl vh) % 2 ^ 64 else W64 vl vh := by
    rw [v140, v141, r13_10, w64_sel c1, nv13, r13_11, r13_12]
  have E14 : PvEnv3 n14.mem := E13.fr F P14.fr
  have r14 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n14 q = reg n13 q := P14.regs
  have sp14 : reg n14 sp = B + 0x420 := by rw [r14 _ (by decide), sp13]
  have z14 := P14.st.zero
  have r14_24 : reg n14 (24 : Fin 32) = B + 0x420 + 0xD80 := by rw [r14 _ (by decide), r13_24]
  -- segment 8, to the branch at 0xEFE: the new `r`, and the registers the loop carries
  obtain ⟨n15, c15, u15⟩ := P14.st.block ctS8 E14.E.C.self ctS8_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, r14_24, add_7ff, add_d80, and_true, true_and]; ct_ok)
  have m15 : n15.mem = (runBlock ctS8 (n14.mem, reg n14)).1 := u15.mem
  have b15 : ∀ q : Fin 32, reg n15 q = (runBlock ctS8 (n14.mem, reg n14)).2 q := u15.regs
  have s15 : St n15.mem PV n15 0xEFE (reg n15) := ⟨u15.pc, rfl, fun _ => rfl⟩
  have e14 : ∀ q : Fin 32, q.val ∈ [21, 22, 27] → reg n14 q = reg m q := fun q hq => by
    rw [r14 q (by revert hq; revert q; decide), r13k q (by revert hq; revert q; decide),
      r12 q (by revert hq; revert q; decide), r11k q (by revert hq; revert q; decide),
      r10 q (by revert hq; revert q; decide)]
  have r15 : W64 (reg n15 (22 : Fin 32)) (reg n15 a3) =
      (W64 rl rh + (if gl &&& 1 = 1 then W64 (reg n14 a0) (reg n14 a1) else 0)) % 2 ^ 64 := by
    rw [b15, b15]; simp +decide only [runBlock, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, add_7ff, add_d80]
    rw [r14_24]
    simp (disch := decide) only [memStore8_same]
    rw [e14 (22 : Fin 32) (by decide), e14 (21 : Fin 32) (by decide), e14 (27 : Fin 32) (by decide), h22, h21, h27, zext_trunc01 mk, mask01 mk,
      mask01' mk, ← w64_mask]
    exact w64_add' _ _ _ _
  have w40_15 : memLoad32 n15.mem (B + 0x420 + 0x40) = memLoad32 m.mem (B + 0x420 + 0x40) := by
    rw [m15]; simp +decide only [runBlock, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, z14, r14_24, add_d94]
    simp (disch := decide) only [ldst8_ne hS]; rw [kld K14 (by decide), w40_13, w40_11]
  have w38_15 : memLoad32 n15.mem (B + 0x420 + 0x38) = memLoad32 m.mem (B + 0x420 + 0x38) := by
    rw [m15]; simp +decide only [runBlock, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, z14, r14_24, add_d94]
    simp (disch := decide) only [ldst8_ne hS]; rw [kld K14 (by decide), w38_13, w38_11]
  have w50_15 : memLoad32 n15.mem (B + 0x420 + 0x50) = memLoad32 m.mem (B + 0x420 + 0x50) := by
    rw [m15]; simp +decide only [runBlock, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, z14, r14_24, add_d94]
    simp (disch := decide) only [ldst8_ne hS]; rw [kld K14 (by decide), w50_13, w50_11]
  have w48_15 : memLoad32 n15.mem (B + 0x420 + 0x48) = memLoad32 m.mem (B + 0x420 + 0x48) := by
    rw [m15]; simp +decide only [runBlock, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, z14, r14_24, add_d94]
    simp (disch := decide) only [ldst8_ne hS]; rw [kld K14 (by decide), w48_13, w48_11]
  have w44_15 : memLoad32 n15.mem (B + 0x420 + 0x44) = memLoad32 m.mem (B + 0x420 + 0x44) := by
    rw [m15]; simp +decide only [runBlock, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, z14, r14_24, add_d94]
    simp (disch := decide) only [ldst8_ne hS]; rw [kld K14 (by decide), w44_13, w44_11]
  have w4c_15 : memLoad32 n15.mem (B + 0x420 + 0x4C) = memLoad32 m.mem (B + 0x420 + 0x4C) := by
    rw [m15]; simp +decide only [runBlock, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, z14, r14_24, add_d94]
    simp (disch := decide) only [ldst8_ne hS]; rw [kld K14 (by decide), w4c_13, w4c_11]
  have w2c_15 : memLoad32 n15.mem (B + 0x420 + 0x2C) = memLoad32 m.mem (B + 0x420 + 0x2C) := by
    rw [m15]; simp +decide only [runBlock, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, z14, r14_24, add_d94]
    simp (disch := decide) only [ldst8_ne hS]; rw [kld K14 (by decide), w2c_13, w2c_11]
  have w34_15 : memLoad32 n15.mem (B + 0x420 + 0x34) = memLoad32 m.mem (B + 0x420 + 0x34) := by
    rw [m15]; simp +decide only [runBlock, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, z14, r14_24, add_d94]
    simp (disch := decide) only [ldst8_ne hS]; rw [kld K14 (by decide), w34_13, w34_11]
  have w3c_15 : memLoad32 n15.mem (B + 0x420 + 0x3C) = memLoad32 m.mem (B + 0x420 + 0x3C) := by
    rw [m15]; simp +decide only [runBlock, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, z14, r14_24, add_d94]
    simp (disch := decide) only [ldst8_ne hS]; rw [kld K14 (by decide), w3c_13, w3c_11]
  have w54_15 : memLoad32 n15.mem (B + 0x420 + 0x54) = memLoad32 n13.mem (B + 0x420 + 0x54) := by
    rw [m15]; simp +decide only [runBlock, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, z14, r14_24, add_d94]
    simp (disch := decide) only [ldst8_ne hS]; rw [kld K14 (by decide)]
  have fr15 : ∀ x, PvR B x → n15.mem x = m.mem x := fun x hx => by
    rw [m15]; simp +decide only [runBlock, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, z14, r14_24, add_d94]
    simp (disch := decide) only [pvR_st8 hx]; rw [P14.fr x hx, fr13 x hx]
  have fk15 : ∀ e, e + 1 ≤ 0x1D4C → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0x1294 →
      n15.mem (B + 0x420 + BitVec.ofNat 32 e) = m.mem (B + 0x420 + BitVec.ofNat 32 e) := fun e he h1 h2 => by
    rw [m15]; simp +decide only [runBlock, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, z14, r14_24, add_d94]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [fk_st8 hS]
    rw [kfk K14 he, fk13 e he h1 h2]
  have k15 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 18, 19, 20, 21] → reg n15 q = reg n14 q := fun q hq => by
    rw [b15, runBlock_reg _ _ _ _ z14 (by revert hq; revert q; decide)]
  have t15 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 20] → reg n15 q = reg n11 q := fun q hq => by
    rw [k15 q (by revert hq; revert q; decide), r14 q (by revert hq; revert q; decide),
      r13k q (by revert hq; revert q; decide), r12 q (by revert hq; revert q; decide)]
  refine ⟨n15, P10.steps.trans (c11.trans (P12.steps.trans (c13.trans (P14.steps.trans c15)))), E.fr F fr15,
    fr15, fk15, s15, ?_, ?_, ?_, ?_, ?_, w40_15, w50_15, w48_15, w44_15, w4c_15, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [t15 sp (by decide), r11k sp (by decide), sp10]
  · rw [b15]; simp +decide only [runBlock, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, z14, r14_24, add_d94]; exact BitVec.zero_add _
  · rw [b15]; simp +decide only [runBlock, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, z14, r14_24, add_d94]
    rw [kld K14 (by decide), w3c_13, w3c_11, w3c]; exact dec_ofNat n
  · rw [t15 _ (by decide), r11k _ (by decide), r10 _ (by decide)]
  · rw [t15 _ (by decide), r11k _ (by decide), r10 _ (by decide)]
  · rw [b15]; simp +decide only [runBlock, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, z14, r14_24, add_d94]
    simp (disch := decide) only [ldst8_ne hS]; rw [kld K14 (by decide), w38_13, w38_11]
  · rw [b15]; simp +decide only [runBlock, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, z14, r14_24, add_d94]
    simp (disch := decide) only [ldst8_ne hS]; rw [kld K14 (by decide), w2c_13, w2c_11]
  · rw [b15]; simp +decide only [runBlock, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, z14, r14_24, add_d94]
    simp (disch := decide) only [ldst8_ne hS]; rw [kld K14 (by decide), w34_13, w34_11]
  · have h25' : reg n15 (25 : Fin 32) = memLoad32 n11.mem (B + 0x420 + 0x20) := by
      rw [b15]; simp +decide only [runBlock, BInstr.run, ctS8, upd, ↓reduceIte, aluEval, sp14, z14, r14_24, add_d94]
      simp (disch := decide) only [ldst8_ne hS]; rw [kld K14 (by decide), w20_13]
    rw [h25', t15 _ (by decide), v11, q10]
  · rw [w54_15, k15 _ (by decide), r14 _ (by decide), q13, q12]
  · have h13' : reg n15 (13 : Fin 32) = reg n15 a3 := rfl
    rw [h13', r15, q14]

end C3.RV32.Pv
