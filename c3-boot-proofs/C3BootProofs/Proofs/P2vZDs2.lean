import C3BootProofs.Proofs.P2vZDs

/-!
# `p256_verify_prehash`: one constant-time divstep

One pass of the constant-time divstep loop at 0xC3C, to its branch at
0xE02, against `dsStep`.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

set_option maxHeartbeats 64000000 in
/-- The first half of a constant-time divstep, from 0xC3C to the fifth
select at 0xD3C: the new `δ`, `f`, `g`, and `u` stored, and the candidates
for `v` in the argument registers. -/
theorem ct2_partA {B : Word} {m : Machine} {n : Nat} {dl dh fl fh gl gh ul uh vl vh ql qh rl rh : Word}
    (F : Fr B 0x3590) (C : P2vCode m.mem) (IC : P2vIvCode m.mem)
    (st : St m.mem P2V m 0xC3C (reg m)) (hsp : reg m sp = B + 0x21A0) (h8 : reg m (8 : Fin 32) = B + 0x21A0 + 0x920)
    (hcnt : reg m a4 = BitVec.ofNat 32 (n + 1))
    (hdl : memLoad32 m.mem (B + 0x21A0 + 0x40) = dl) (hfl : memLoad32 m.mem (B + 0x21A0 + 0x50) = fl)
    (hfh : memLoad32 m.mem (B + 0x21A0 + 0x48) = fh) (hgl : memLoad32 m.mem (B + 0x21A0 + 0x44) = gl)
    (hgh : memLoad32 m.mem (B + 0x21A0 + 0x4C) = gh) (hql : memLoad32 m.mem (B + 0x21A0 + 0x54) = ql)
    (hdh : reg m (24 : Fin 32) = dh) (hul : reg m (23 : Fin 32) = ul) (huh : reg m (26 : Fin 32) = uh)
    (hvl : reg m (20 : Fin 32) = vl) (hvh : reg m (25 : Fin 32) = vh) (hqh : reg m (18 : Fin 32) = qh)
    (hrl : reg m (22 : Fin 32) = rl) (hrh : reg m (13 : Fin 32) = rh) :
    ∃ m', Steps m m' ∧ P2vCode m'.mem ∧ P2vIvCode m'.mem ∧ (∀ x, P2vR B x → m'.mem x = m.mem x) ∧
      (∀ e, e + 1 ≤ 0x13F0 → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0xC80 →
        m'.mem (B + 0x21A0 + BitVec.ofNat 32 e) = m.mem (B + 0x21A0 + BitVec.ofNat 32 e)) ∧
      St m'.mem P2V m' 0xD3C (reg m') ∧ reg m' sp = B + 0x21A0 ∧
      reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧ reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧
      reg m' a0 = ctC3 gl dl dh ∧ reg m' a1 = vl ∧ reg m' a2 = vh ∧ reg m' a3 = rl ∧ reg m' a4 = rh ∧
      reg m' (8 : Fin 32) = vh ∧ reg m' (18 : Fin 32) = ql ∧ reg m' (19 : Fin 32) = vl ∧
      reg m' (21 : Fin 32) = qh ∧ reg m' (22 : Fin 32) = rl ∧ reg m' (23 : Fin 32) = ul ∧
      reg m' (25 : Fin 32) = rh ∧ reg m' (26 : Fin 32) = uh ∧ reg m' (27 : Fin 32) = gl &&& 1 ∧
      memLoad32 m'.mem (B + 0x21A0 + 0x3C) = BitVec.ofNat 32 (n + 1) ∧
      memLoad32 m'.mem (B + 0x21A0 + 0x24) = ctC1 dl dh ∧
      W64 (memLoad32 m'.mem (B + 0x21A0 + 0x40)) (memLoad32 m'.mem (B + 0x21A0 + 0x38)) =
        (if ctC3 gl dl dh = 1 then (2 + 2 ^ 64 - W64 dl dh) % 2 ^ 64 else (W64 dl dh + 2) % 2 ^ 64) ∧
      W64 (memLoad32 m'.mem (B + 0x21A0 + 0x50)) (memLoad32 m'.mem (B + 0x21A0 + 0x48)) =
        (if ctC3 gl dl dh = 1 then W64 gl gh else W64 fl fh) ∧
      W64 (memLoad32 m'.mem (B + 0x21A0 + 0x44)) (memLoad32 m'.mem (B + 0x21A0 + 0x4C)) =
        asr64 (if ctC3 gl dl dh = 1 then (W64 gl gh + 2 ^ 64 - W64 (fl &&& ctMk gl) (fh &&& ctMk gl)) % 2 ^ 64
          else (W64 (fl &&& ctMk gl) (fh &&& ctMk gl) + W64 gl gh) % 2 ^ 64) ∧
      W64 (memLoad32 m'.mem (B + 0x21A0 + 0x2C)) (memLoad32 m'.mem (B + 0x21A0 + 0x34)) =
        2 * (if ctC3 gl dl dh = 1 then W64 ql qh else W64 ul uh) % 2 ^ 64 := by
  have FS : Fr (B + 0x21A0) 0x13F0 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hS : (B + 0x21A0).toNat + 0x1D80 ≤ 2 ^ 32 := by have := FS.hi; omega
  have gb01' := gb01 gl
  have c101 := c1_01 dl dh
  have c301 := and01w gb01' c101
  have hz := st.zero
  -- segment 1, to the first select at 0xCB0
  obtain ⟨n1, c1, u1⟩ := st.block ctT1 C.self ctT1_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, ctT1, upd, ↓reduceIte, hsp, h8, add_920, and_true, true_and]
    ct2_ok)
  have s1 : St n1.mem P2V n1 0xCB0 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = (runBlock ctT1 (m.mem, reg m)).1 := u1.mem
  have b1 : ∀ q : Fin 32, reg n1 q = (runBlock ctT1 (m.mem, reg m)).2 q := u1.regs
  have r27 : reg n1 (27 : Fin 32) = gl &&& 1 := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, hgl]
  have r21 : reg n1 (21 : Fin 32) = gl := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, hgl]
  have r19 : reg n1 (19 : Fin 32) = vl := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, hvl, hz]
    exact BitVec.zero_add _
  have r18 : reg n1 (18 : Fin 32) = rl := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, hrl, hz]
    exact BitVec.zero_add _
  have r22 : reg n1 (22 : Fin 32) = fh := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; exact hfh
  have r20 : reg n1 (20 : Fin 32) = fl := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; exact hfl
  have r23 : reg n1 (23 : Fin 32) = ul := by
    rw [b1, runBlock_reg _ _ _ _ hz (by decide), hul]
  have r26 : reg n1 (26 : Fin 32) = uh := by
    rw [b1, runBlock_reg _ _ _ _ hz (by decide), huh]
  have r24 : reg n1 (24 : Fin 32) = (gl &&& (1 : Word)) &&& (((dh ^^^ 0x80000000) &&& (0x80000000 - (dh ^^^ 0x80000000) -
      (if (0 : Word).ult dl then 1 else 0))) >>> 0x1F) := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]
    rw [hgl, hdl, hdh]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
  have r10 : reg n1 a0 = reg n1 (24 : Fin 32) := by
    rw [b1, b1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hz]
    exact BitVec.zero_add _
  have q11 : W64 (reg n1 a1) (reg n1 a2) = (W64 dl dh + 2) % 2 ^ 64 := by
    rw [b1, b1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]
    rw [hdl, hdh]; exact w64_add2 _ _
  have q13 : W64 (reg n1 a3) (reg n1 a4) = (2 + 2 ^ 64 - W64 dl dh) % 2 ^ 64 := by
    rw [b1, b1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]
    rw [hdl, hdh]; exact w64_2sub _ _
  have r8 : reg n1 (8 : Fin 32) = fl &&& (if gl &&& 1 = 1 then 0xFFFFFFFF else 0) := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS, st32_get hS, memStore8_same]
    rw [hfl, hgl, zext_trunc01 (gb01 gl), mask01 (gb01 gl)]
  have r25 : reg n1 (25 : Fin 32) = fh &&& (if gl &&& 1 = 1 then 0xFFFFFFFF else 0) := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS, st32_get hS, memStore8_same]
    rw [hfh, hgl, zext_trunc01 (gb01 gl), mask01' (gb01 gl)]
  have w30 : memLoad32 n1.mem (B + 0x21A0 + 0x30) = vh := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS, memLoad32_store32_same]; exact hvh
  have w28 : memLoad32 n1.mem (B + 0x21A0 + 0x28) = rh := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS, memLoad32_store32_same]; exact hrh
  have w3c : memLoad32 n1.mem (B + 0x21A0 + 0x3C) = BitVec.ofNat 32 (n + 1) := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS, memLoad32_store32_same]; exact hcnt
  have w1c : memLoad32 n1.mem (B + 0x21A0 + 0x1C) = qh := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS, memLoad32_store32_same]; exact hqh
  have w24 : memLoad32 n1.mem (B + 0x21A0 + 0x24) = ((dh ^^^ 0x80000000) &&& (0x80000000 - (dh ^^^ 0x80000000) -
      (if (0 : Word).ult dl then 1 else 0))) >>> 0x1F := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS, memLoad32_store32_same]
    rw [hdl, hdh]; simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
  have w40 : memLoad32 n1.mem (B + 0x21A0 + 0x40) = dl := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; exact hdl
  have w44 : memLoad32 n1.mem (B + 0x21A0 + 0x44) = gl := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; exact hgl
  have w48 : memLoad32 n1.mem (B + 0x21A0 + 0x48) = fh := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; exact hfh
  have w4c : memLoad32 n1.mem (B + 0x21A0 + 0x4C) = gh := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; exact hgh
  have w50 : memLoad32 n1.mem (B + 0x21A0 + 0x50) = fl := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; exact hfl
  have w54 : memLoad32 n1.mem (B + 0x21A0 + 0x54) = ql := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920, hz]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; exact hql
  have fr1 : ∀ x, P2vR B x → n1.mem x = m.mem x := fun x hx => by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920, hz]
    simp (disch := decide) only [p2vR_st32 hx, p2vR_st8 hx]
  have fk1 : ∀ e, e + 1 ≤ 0x13F0 → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0xC80 →
      n1.mem (B + 0x21A0 + BitVec.ofNat 32 e) = m.mem (B + 0x21A0 + BitVec.ofNat 32 e) := fun e he h1 h2 => by
    rw [m1]; simp +decide only [runBlock, BInstr.run, ctT1, upd, ↓reduceIte, aluEval, hsp, h8, add_920, hz]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [fk2_st32 hS, fk2_st8 hS]
  -- the first select: `δ`
  have C1 : P2vCode n1.mem := C.fr F fr1
  have IC1 : P2vIvCode n1.mem := IC.p2v F fr1
  have sp1 : reg n1 sp = B + 0x21A0 := by rw [b1, runBlock_reg _ _ _ _ hz (by decide), hsp]
  have c3 : reg n1 a0 = 0 ∨ reg n1 a0 = 1 := by rw [r10, r24]; exact c301
  obtain ⟨n2, P2, K2, k2, v20, v21⟩ := p2v_si F C1 IC1 s1 p2v_at_cb0 p2v_at_cb4 (by decide) (by decide) sp1 c3
  have q2 : W64 (reg n2 a0) (reg n2 a1) = if reg n1 a0 = 1 then (2 + 2 ^ 64 - W64 dl dh) % 2 ^ 64
      else (W64 dl dh + 2) % 2 ^ 64 := by
    rw [v20, v21, w64_sel c3, q11, q13]
  have C2 : P2vCode n2.mem := C1.fr F P2.fr
  have IC2 : P2vIvCode n2.mem := IC1.p2v F P2.fr
  have r2 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n2 q = reg n1 q := P2.regs
  -- segment 2, to the second select at 0xCCA: store `δ`, select `f`
  have sp2 : reg n2 sp = B + 0x21A0 := by rw [r2 _ (by decide), sp1]
  obtain ⟨n3, c3', u3⟩ := P2.st.block ctT2 C2.self ctT2_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, ctT2, upd, ↓reduceIte, sp2, and_true, true_and]; ct2_ok)
  have m3 : n3.mem = (runBlock ctT2 (n2.mem, reg n2)).1 := u3.mem
  have b3 : ∀ q : Fin 32, reg n3 q = (runBlock ctT2 (n2.mem, reg n2)).2 q := u3.regs
  have s3 : St n3.mem P2V n3 0xCCA (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have z2 := P2.st.zero
  have w40_3 : memLoad32 n3.mem (B + 0x21A0 + 0x40) = reg n2 a0 := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst_ne hS, memLoad32_store32_same]
  have w38_3 : memLoad32 n3.mem (B + 0x21A0 + 0x38) = reg n2 a1 := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst_ne hS, memLoad32_store32_same]
  have w30_3 : memLoad32 n3.mem (B + 0x21A0 + 0x30) = vh := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K2 (by decide)]; exact w30
  have w28_3 : memLoad32 n3.mem (B + 0x21A0 + 0x28) = rh := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K2 (by decide)]; exact w28
  have w3c_3 : memLoad32 n3.mem (B + 0x21A0 + 0x3C) = BitVec.ofNat 32 (n + 1) := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K2 (by decide)]; exact w3c
  have w1c_3 : memLoad32 n3.mem (B + 0x21A0 + 0x1C) = qh := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K2 (by decide)]; exact w1c
  have w24_3 : memLoad32 n3.mem (B + 0x21A0 + 0x24) = ((dh ^^^ 0x80000000) &&& (0x80000000 - (dh ^^^ 0x80000000) - (if (0 : Word).ult dl then 1 else 0))) >>> 0x1F := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K2 (by decide)]; exact w24
  have w44_3 : memLoad32 n3.mem (B + 0x21A0 + 0x44) = gl := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K2 (by decide)]; exact w44
  have w48_3 : memLoad32 n3.mem (B + 0x21A0 + 0x48) = fh := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K2 (by decide)]; exact w48
  have w4c_3 : memLoad32 n3.mem (B + 0x21A0 + 0x4C) = gh := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K2 (by decide)]; exact w4c
  have w50_3 : memLoad32 n3.mem (B + 0x21A0 + 0x50) = fl := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K2 (by decide)]; exact w50
  have w54_3 : memLoad32 n3.mem (B + 0x21A0 + 0x54) = ql := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K2 (by decide)]; exact w54
  have fr3 : ∀ x, P2vR B x → n3.mem x = m.mem x := fun x hx => by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [p2vR_st32 hx]; rw [P2.fr x hx, fr1 x hx]
  have fk3 : ∀ e, e + 1 ≤ 0x13F0 → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0xC80 →
      n3.mem (B + 0x21A0 + BitVec.ofNat 32 e) = m.mem (B + 0x21A0 + BitVec.ofNat 32 e) := fun e he h1 h2 => by
    rw [m3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [fk2_st32 hS]
    rw [kfk2 K2 he, fk1 e he h1 h2]
  have r3_10 : reg n3 a0 = reg n1 a0 := by
    rw [b3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, z2]
    rw [r2 _ (by decide), ← r10]; exact BitVec.zero_add _
  have r3_11 : reg n3 a1 = fl := by
    rw [b3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, z2]
    rw [r2 _ (by decide), r20]; exact BitVec.zero_add _
  have r3_12 : reg n3 a2 = fh := by
    rw [b3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, z2]
    rw [r2 _ (by decide), r22]; exact BitVec.zero_add _
  have r3_13 : reg n3 a3 = gl := by
    rw [b3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, z2]
    rw [r2 _ (by decide), r21]; exact BitVec.zero_add _
  have r3_14 : reg n3 a4 = gh := by
    rw [b3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, z2, sp2]
    simp (disch := decide) only [ldst_ne hS]; rw [kld2 K2 (by decide), w4c]; exact BitVec.zero_add _
  have r3_22 : reg n3 (22 : Fin 32) = rl := by
    rw [b3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, z2]
    rw [r2 _ (by decide), r18]; exact BitVec.zero_add _
  -- the second select: `f`
  have C3 : P2vCode n3.mem := C.fr F fr3
  have IC3 : P2vIvCode n3.mem := IC.p2v F fr3
  have sp3 : reg n3 sp = B + 0x21A0 := by rw [b3, runBlock_reg _ _ _ _ z2 (by decide), sp2]
  obtain ⟨n4, P4, K4, k4, v40, v41⟩ := p2v_si F C3 IC3 s3 p2v_at_cca p2v_at_cce (by decide) (by decide) sp3
    (by rw [r3_10]; exact c3)
  have q4 : W64 (reg n4 a0) (reg n4 a1) = if reg n1 a0 = 1 then W64 gl gh else W64 fl fh := by
    rw [v40, v41, r3_10, w64_sel c3, r3_13, r3_14, r3_11, r3_12]
  have C4 : P2vCode n4.mem := C3.fr F P4.fr
  have IC4 : P2vIvCode n4.mem := IC3.p2v F P4.fr
  have r4 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg n3 q := P4.regs
  have r3k : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 19, 20, 21, 23, 24, 25, 26, 27] → reg n3 q = reg n2 q := fun q hq => by
    rw [b3, runBlock_reg _ _ _ _ z2 (by revert hq; revert q; decide)]
  have r3_9 : reg n3 (9 : Fin 32) = gh := by
    rw [b3]; simp +decide only [runBlock, BInstr.run, ctT2, upd, ↓reduceIte, aluEval, z2, sp2]
    simp (disch := decide) only [ldst_ne hS]; rw [kld2 K2 (by decide), w4c]
  -- segment 3, to the third select at 0xCF4: store `f`, and both candidates for `g`
  have sp4 : reg n4 sp = B + 0x21A0 := by rw [r4 _ (by decide), sp3]
  have z4 := P4.st.zero
  have mk := gb01 gl
  obtain ⟨n5, c5, u5⟩ := P4.st.block ctT3 C4.self ctT3_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, ctT3, upd, ↓reduceIte, sp4, and_true, true_and]; ct2_ok)
  have m5 : n5.mem = (runBlock ctT3 (n4.mem, reg n4)).1 := u5.mem
  have b5 : ∀ q : Fin 32, reg n5 q = (runBlock ctT3 (n4.mem, reg n4)).2 q := u5.regs
  have s5 : St n5.mem P2V n5 0xCF4 (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have e4_8 : reg n4 (8 : Fin 32) = fl &&& (if gl &&& 1 = 1 then 0xFFFFFFFF else 0) := by
    rw [r4 _ (by decide), r3k _ (by decide), r2 _ (by decide), r8]
  have e4_25 : reg n4 (25 : Fin 32) = fh &&& (if gl &&& 1 = 1 then 0xFFFFFFFF else 0) := by
    rw [r4 _ (by decide), r3k _ (by decide), r2 _ (by decide), r25]
  have e4_21 : reg n4 (21 : Fin 32) = gl := by rw [r4 _ (by decide), r3k _ (by decide), r2 _ (by decide), r21]
  have e4_20 : reg n4 (20 : Fin 32) = fl := by rw [r4 _ (by decide), r3k _ (by decide), r2 _ (by decide), r20]
  have e4_9 : reg n4 (9 : Fin 32) = gh := by rw [r4 _ (by decide), r3_9]
  have e4_24 : reg n4 (24 : Fin 32) = reg n1 a0 := by rw [r4 _ (by decide), r3k _ (by decide), r2 _ (by decide), r10]
  have w50_5 : memLoad32 n5.mem (B + 0x21A0 + 0x50) = reg n4 a0 := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctT3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst_ne hS, memLoad32_store32_same]
  have w48_5 : memLoad32 n5.mem (B + 0x21A0 + 0x48) = reg n4 a1 := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctT3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst_ne hS, memLoad32_store32_same]
  have q5a : W64 (reg n5 a1) (reg n5 a2) = (W64 (fl &&& (if gl &&& 1 = 1 then 0xFFFFFFFF else 0))
      (fh &&& (if gl &&& 1 = 1 then 0xFFFFFFFF else 0)) + W64 gl gh) % 2 ^ 64 := by
    rw [b5, b5]; simp +decide only [runBlock, BInstr.run, ctT3, upd, ↓reduceIte, aluEval]
    rw [e4_8, e4_21, e4_25, e4_9]; exact w64_add _ _ _ _
  have q5b : W64 (reg n5 a3) (reg n5 a4) = (W64 gl gh + 2 ^ 64 - W64 (fl &&& (if gl &&& 1 = 1 then 0xFFFFFFFF else 0))
      (fh &&& (if gl &&& 1 = 1 then 0xFFFFFFFF else 0))) % 2 ^ 64 := by
    rw [b5, b5]; simp +decide only [runBlock, BInstr.run, ctT3, upd, ↓reduceIte, aluEval]
    rw [e4_8, e4_21, e4_25, e4_9]; exact w64_sub _ _ _ _
  have r5_10 : reg n5 a0 = reg n1 a0 := by
    rw [b5]; simp +decide only [runBlock, BInstr.run, ctT3, upd, ↓reduceIte, aluEval, z4]
    rw [e4_24]; exact BitVec.zero_add _
  have r5k : ∀ q : Fin 32, q.val ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n5 q = reg n4 q := fun q hq => by
    rw [b5, runBlock_reg _ _ _ _ z4 (by revert hq; revert q; decide)]
  have w40_5 : memLoad32 n5.mem (B + 0x21A0 + 0x40) = reg n2 a0 := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctT3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K4 (by decide)]; exact w40_3
  have w38_5 : memLoad32 n5.mem (B + 0x21A0 + 0x38) = reg n2 a1 := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctT3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K4 (by decide)]; exact w38_3
  have w30_5 : memLoad32 n5.mem (B + 0x21A0 + 0x30) = vh := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctT3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K4 (by decide)]; exact w30_3
  have w28_5 : memLoad32 n5.mem (B + 0x21A0 + 0x28) = rh := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctT3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K4 (by decide)]; exact w28_3
  have w3c_5 : memLoad32 n5.mem (B + 0x21A0 + 0x3C) = BitVec.ofNat 32 (n + 1) := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctT3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K4 (by decide)]; exact w3c_3
  have w1c_5 : memLoad32 n5.mem (B + 0x21A0 + 0x1C) = qh := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctT3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K4 (by decide)]; exact w1c_3
  have w24_5 : memLoad32 n5.mem (B + 0x21A0 + 0x24) = (((dh ^^^ 0x80000000) &&& (0x80000000 - (dh ^^^ 0x80000000) - (if (0 : Word).ult dl then 1 else 0))) >>> 0x1F) := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctT3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K4 (by decide)]; exact w24_3
  have w54_5 : memLoad32 n5.mem (B + 0x21A0 + 0x54) = ql := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctT3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K4 (by decide)]; exact w54_3
  have fr5 : ∀ x, P2vR B x → n5.mem x = m.mem x := fun x hx => by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctT3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [p2vR_st32 hx, p2vR_st8 hx]; rw [P4.fr x hx, fr3 x hx]
  have fk5 : ∀ e, e + 1 ≤ 0x13F0 → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0xC80 →
      n5.mem (B + 0x21A0 + BitVec.ofNat 32 e) = m.mem (B + 0x21A0 + BitVec.ofNat 32 e) := fun e he h1 h2 => by
    rw [m5]; simp +decide only [runBlock, BInstr.run, ctT3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [fk2_st32 hS, fk2_st8 hS]
    rw [kfk2 K4 he, fk3 e he h1 h2]
  -- the third select: `g` before the shift
  have C5 : P2vCode n5.mem := C.fr F fr5
  have IC5 : P2vIvCode n5.mem := IC.p2v F fr5
  have sp5 : reg n5 sp = B + 0x21A0 := by rw [b5, runBlock_reg _ _ _ _ z4 (by decide), sp4]
  obtain ⟨n6, P6, K6, k6, v60, v61⟩ := p2v_si F C5 IC5 s5 p2v_at_cf4 p2v_at_cf8 (by decide) (by decide) sp5
    (by rw [r5_10]; exact c3)
  have q6 : W64 (reg n6 a0) (reg n6 a1) = if reg n1 a0 = 1 then W64 (reg n5 a3) (reg n5 a4) else W64 (reg n5 a1) (reg n5 a2) := by
    rw [v60, v61, r5_10, w64_sel c3]
  have C6 : P2vCode n6.mem := C5.fr F P6.fr
  have IC6 : P2vIvCode n6.mem := IC5.p2v F P6.fr
  have r6 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n6 q = reg n5 q := P6.regs
  -- segment 4, to the fourth select at 0xD18: store `g`, select `u` or `q`
  have sp6 : reg n6 sp = B + 0x21A0 := by rw [r6 _ (by decide), sp5]
  have z6 := P6.st.zero
  obtain ⟨n7, c7, u7⟩ := P6.st.block ctT4 C6.self ctT4_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, ctT4, upd, ↓reduceIte, sp6, and_true, true_and]; ct2_ok)
  have m7 : n7.mem = (runBlock ctT4 (n6.mem, reg n6)).1 := u7.mem
  have b7 : ∀ q : Fin 32, reg n7 q = (runBlock ctT4 (n6.mem, reg n6)).2 q := u7.regs
  have s7 : St n7.mem P2V n7 0xD18 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have e6 : ∀ q : Fin 32, q.val ∈ [8, 19, 20, 21, 23, 24, 26] → reg n6 q = reg n1 q := fun q hq => by
    rw [r6 q (by revert hq; revert q; decide), r5k q (by revert hq; revert q; decide), r4 q (by revert hq; revert q; decide),
      r3k q (by revert hq; revert q; decide), r2 q (by revert hq; revert q; decide)]
  have g7 : W64 (memLoad32 n7.mem (B + 0x21A0 + 0x44)) (memLoad32 n7.mem (B + 0x21A0 + 0x4C)) =
      asr64 (W64 (reg n6 a0) (reg n6 a1)) := by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctT4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst_ne hS, memLoad32_store32_same]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    rw [BitVec.or_comm]; exact w64_asr _ _
  have r7_10 : reg n7 a0 = reg n1 a0 := by
    rw [b7]; simp +decide only [runBlock, BInstr.run, ctT4, upd, ↓reduceIte, aluEval, z6]
    rw [e6 _ (by decide), r10]; exact BitVec.zero_add _
  have r7_11 : reg n7 a1 = ul := by
    rw [b7]; simp +decide only [runBlock, BInstr.run, ctT4, upd, ↓reduceIte, aluEval, z6]
    rw [e6 _ (by decide), r23]; exact BitVec.zero_add _
  have r7_12 : reg n7 a2 = uh := by
    rw [b7]; simp +decide only [runBlock, BInstr.run, ctT4, upd, ↓reduceIte, aluEval, z6]
    rw [e6 _ (by decide), r26]; exact BitVec.zero_add _
  have r7_18 : reg n7 (18 : Fin 32) = ql := by
    rw [b7]; simp +decide only [runBlock, BInstr.run, ctT4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst_ne hS]; rw [kld2 K6 (by decide), w54_5]
  have r7_13 : reg n7 a3 = ql := by
    rw [b7]; simp +decide only [runBlock, BInstr.run, ctT4, upd, ↓reduceIte, aluEval, sp6, z6]
    simp (disch := decide) only [ldst_ne hS]; rw [kld2 K6 (by decide), w54_5]; exact BitVec.zero_add _
  have r7_21 : reg n7 (21 : Fin 32) = qh := by
    rw [b7]; simp +decide only [runBlock, BInstr.run, ctT4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst_ne hS]; rw [kld2 K6 (by decide), w1c_5]
  have r7_14 : reg n7 a4 = qh := by
    rw [b7]; simp +decide only [runBlock, BInstr.run, ctT4, upd, ↓reduceIte, aluEval, sp6, z6]
    simp (disch := decide) only [ldst_ne hS]; rw [kld2 K6 (by decide), w1c_5]; exact BitVec.zero_add _
  have r7k : ∀ q : Fin 32, q.val ∈ [8, 19, 20, 22, 23, 24, 25, 26, 27] → reg n7 q = reg n6 q := fun q hq => by
    rw [b7, runBlock_reg _ _ _ _ z6 (by revert hq; revert q; decide)]
  have w40_7 : memLoad32 n7.mem (B + 0x21A0 + 0x40) = reg n2 a0 := by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctT4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K6 (by decide)]; exact w40_5
  have w38_7 : memLoad32 n7.mem (B + 0x21A0 + 0x38) = reg n2 a1 := by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctT4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K6 (by decide)]; exact w38_5
  have w50_7 : memLoad32 n7.mem (B + 0x21A0 + 0x50) = reg n4 a0 := by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctT4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K6 (by decide)]; exact w50_5
  have w48_7 : memLoad32 n7.mem (B + 0x21A0 + 0x48) = reg n4 a1 := by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctT4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K6 (by decide)]; exact w48_5
  have w30_7 : memLoad32 n7.mem (B + 0x21A0 + 0x30) = vh := by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctT4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K6 (by decide)]; exact w30_5
  have w28_7 : memLoad32 n7.mem (B + 0x21A0 + 0x28) = rh := by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctT4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K6 (by decide)]; exact w28_5
  have w3c_7 : memLoad32 n7.mem (B + 0x21A0 + 0x3C) = BitVec.ofNat 32 (n + 1) := by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctT4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K6 (by decide)]; exact w3c_5
  have w24_7 : memLoad32 n7.mem (B + 0x21A0 + 0x24) = (((dh ^^^ 0x80000000) &&& (0x80000000 - (dh ^^^ 0x80000000) - (if (0 : Word).ult dl then 1 else 0))) >>> 0x1F) := by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctT4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K6 (by decide)]; exact w24_5
  have fr7 : ∀ x, P2vR B x → n7.mem x = m.mem x := fun x hx => by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctT4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [p2vR_st32 hx, p2vR_st8 hx]; rw [P6.fr x hx, fr5 x hx]
  have fk7 : ∀ e, e + 1 ≤ 0x13F0 → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0xC80 →
      n7.mem (B + 0x21A0 + BitVec.ofNat 32 e) = m.mem (B + 0x21A0 + BitVec.ofNat 32 e) := fun e he h1 h2 => by
    rw [m7]; simp +decide only [runBlock, BInstr.run, ctT4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [fk2_st32 hS, fk2_st8 hS]
    rw [kfk2 K6 he, fk5 e he h1 h2]
  -- the fourth select: `u` or `q`
  have C7 : P2vCode n7.mem := C.fr F fr7
  have IC7 : P2vIvCode n7.mem := IC.p2v F fr7
  have sp7 : reg n7 sp = B + 0x21A0 := by rw [b7, runBlock_reg _ _ _ _ z6 (by decide), sp6]
  obtain ⟨n8, P8, K8, k8, v80, v81⟩ := p2v_si F C7 IC7 s7 p2v_at_d18 p2v_at_d1c (by decide) (by decide) sp7
    (by rw [r7_10]; exact c3)
  have q8 : W64 (reg n8 a0) (reg n8 a1) = if reg n1 a0 = 1 then W64 ql qh else W64 ul uh := by
    rw [v80, v81, r7_10, w64_sel c3, r7_13, r7_14, r7_11, r7_12]
  have C8 : P2vCode n8.mem := C7.fr F P8.fr
  have IC8 : P2vIvCode n8.mem := IC7.p2v F P8.fr
  have r8' : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n8 q = reg n7 q := P8.regs
  -- segment 5, to the fifth select at 0xD3C: store `u`, select `v` or `r`
  have sp8 : reg n8 sp = B + 0x21A0 := by rw [r8' _ (by decide), sp7]
  have z8 := P8.st.zero
  obtain ⟨n9, c9, u9⟩ := P8.st.block ctT5 C8.self ctT5_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, ctT5, upd, ↓reduceIte, sp8, and_true, true_and]; ct2_ok)
  have m9 : n9.mem = (runBlock ctT5 (n8.mem, reg n8)).1 := u9.mem
  have b9 : ∀ q : Fin 32, reg n9 q = (runBlock ctT5 (n8.mem, reg n8)).2 q := u9.regs
  have s9 : St n9.mem P2V n9 0xD3C (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have u9 : W64 (memLoad32 n9.mem (B + 0x21A0 + 0x2C)) (memLoad32 n9.mem (B + 0x21A0 + 0x34)) =
      2 * W64 (reg n8 a0) (reg n8 a1) % 2 ^ 64 := by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctT5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst_ne hS, memLoad32_store32_same]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    exact w64_shl1 _ _
  have e8 : ∀ q : Fin 32, q.val ∈ [19, 22, 24] → reg n8 q = reg n6 q := fun q hq => by
    rw [r8' q (by revert hq; revert q; decide), r7k q (by revert hq; revert q; decide)]
  have r9_10 : reg n9 a0 = reg n1 a0 := by
    rw [b9]; simp +decide only [runBlock, BInstr.run, ctT5, upd, ↓reduceIte, aluEval, z8]
    rw [e8 _ (by decide), e6 _ (by decide), r10]; exact BitVec.zero_add _
  have r9_11 : reg n9 a1 = vl := by
    rw [b9]; simp +decide only [runBlock, BInstr.run, ctT5, upd, ↓reduceIte, aluEval, z8]
    rw [e8 _ (by decide), e6 _ (by decide), r19]; exact BitVec.zero_add _
  have r9_8 : reg n9 (8 : Fin 32) = vh := by
    rw [b9]; simp +decide only [runBlock, BInstr.run, ctT5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst_ne hS]; rw [kld2 K8 (by decide), w30_7]
  have r9_12 : reg n9 a2 = vh := by
    rw [b9]; simp +decide only [runBlock, BInstr.run, ctT5, upd, ↓reduceIte, aluEval, sp8, z8]
    simp (disch := decide) only [ldst_ne hS]; rw [kld2 K8 (by decide), w30_7]; exact BitVec.zero_add _
  have r9_13 : reg n9 a3 = rl := by
    rw [b9]; simp +decide only [runBlock, BInstr.run, ctT5, upd, ↓reduceIte, aluEval, z8]
    rw [e8 _ (by decide), r6 _ (by decide), r5k _ (by decide), r4 _ (by decide), r3_22]; exact BitVec.zero_add _
  have r9_25 : reg n9 (25 : Fin 32) = rh := by
    rw [b9]; simp +decide only [runBlock, BInstr.run, ctT5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst_ne hS]; rw [kld2 K8 (by decide), w28_7]
  have r9_14 : reg n9 a4 = rh := by
    rw [b9]; simp +decide only [runBlock, BInstr.run, ctT5, upd, ↓reduceIte, aluEval, sp8, z8]
    simp (disch := decide) only [ldst_ne hS]; rw [kld2 K8 (by decide), w28_7]; exact BitVec.zero_add _
  have r9k : ∀ q : Fin 32, q.val ∈ [9, 18, 19, 20, 21, 22, 23, 24, 26, 27] → reg n9 q = reg n8 q := fun q hq => by
    rw [b9, runBlock_reg _ _ _ _ z8 (by revert hq; revert q; decide)]
  have w40_9 : memLoad32 n9.mem (B + 0x21A0 + 0x40) = reg n2 a0 := by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctT5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K8 (by decide)]; exact w40_7
  have w38_9 : memLoad32 n9.mem (B + 0x21A0 + 0x38) = reg n2 a1 := by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctT5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K8 (by decide)]; exact w38_7
  have w50_9 : memLoad32 n9.mem (B + 0x21A0 + 0x50) = reg n4 a0 := by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctT5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K8 (by decide)]; exact w50_7
  have w48_9 : memLoad32 n9.mem (B + 0x21A0 + 0x48) = reg n4 a1 := by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctT5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K8 (by decide)]; exact w48_7
  have w3c_9 : memLoad32 n9.mem (B + 0x21A0 + 0x3C) = BitVec.ofNat 32 (n + 1) := by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctT5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K8 (by decide)]; exact w3c_7
  have w24_9 : memLoad32 n9.mem (B + 0x21A0 + 0x24) = (((dh ^^^ 0x80000000) &&& (0x80000000 - (dh ^^^ 0x80000000) - (if (0 : Word).ult dl then 1 else 0))) >>> 0x1F) := by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctT5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K8 (by decide)]; exact w24_7
  have w44_9 : memLoad32 n9.mem (B + 0x21A0 + 0x44) = memLoad32 n7.mem (B + 0x21A0 + 0x44) := by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctT5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K8 (by decide)]
  have w4c_9 : memLoad32 n9.mem (B + 0x21A0 + 0x4C) = memLoad32 n7.mem (B + 0x21A0 + 0x4C) := by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctT5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [ldst8_ne hS, ldst_ne hS]; rw [kld2 K8 (by decide)]
  have fr9 : ∀ x, P2vR B x → n9.mem x = m.mem x := fun x hx => by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctT5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := decide) only [p2vR_st32 hx, p2vR_st8 hx]; rw [P8.fr x hx, fr7 x hx]
  have fk9 : ∀ e, e + 1 ≤ 0x13F0 → (e < 0x1C ∨ 0x58 ≤ e) → e ≠ 0xC80 →
      n9.mem (B + 0x21A0 + BitVec.ofNat 32 e) = m.mem (B + 0x21A0 + BitVec.ofNat 32 e) := fun e he h1 h2 => by
    rw [m9]; simp +decide only [runBlock, BInstr.run, ctT5, upd, ↓reduceIte, aluEval, sp8]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [fk2_st32 hS, fk2_st8 hS]
    rw [kfk2 K8 he, fk7 e he h1 h2]
  have e9 : ∀ q : Fin 32, q.val ∈ [2, 3, 4] → reg n9 q = reg m q := fun q hq => by
    rw [b9, runBlock_reg _ _ _ _ z8 (by revert hq; revert q; decide), r8' q (by revert hq; revert q; decide),
      b7, runBlock_reg _ _ _ _ z6 (by revert hq; revert q; decide), r6 q (by revert hq; revert q; decide),
      b5, runBlock_reg _ _ _ _ z4 (by revert hq; revert q; decide), r4 q (by revert hq; revert q; decide),
      r3k q (by revert hq; revert q; decide), r2 q (by revert hq; revert q; decide),
      b1, runBlock_reg _ _ _ _ hz (by revert hq; revert q; decide)]
  have e9' : ∀ q : Fin 32, q.val ∈ [19, 22, 23, 26, 27] → reg n9 q = reg n6 q := fun q hq => by
    rw [r9k q (by revert hq; revert q; decide), r8' q (by revert hq; revert q; decide),
      r7k q (by revert hq; revert q; decide)]
  have e5' : ∀ q : Fin 32, q.val ∈ [19, 22, 23, 26, 27] → reg n6 q = reg n3 q := fun q hq => by
    rw [r6 q (by revert hq; revert q; decide), r5k q (by revert hq; revert q; decide),
      r4 q (by revert hq; revert q; decide)]
  have e2' : ∀ q : Fin 32, q.val ∈ [19, 23, 26, 27] → reg n3 q = reg n1 q := fun q hq => by
    rw [r3k q (by revert hq; revert q; decide), r2 q (by revert hq; revert q; decide)]
  have hc3 : reg n1 a0 = ctC3 gl dl dh := by rw [r10, r24]; rfl
  refine ⟨n9, c1.trans (P2.steps.trans (c3'.trans (P4.steps.trans (c5.trans (P6.steps.trans (c7.trans
    (P8.steps.trans c9))))))), C.fr F fr9, IC.p2v F fr9, fr9, fk9, s9, by rw [b9, runBlock_reg _ _ _ _ z8 (by decide), sp8],
    e9 _ (by decide), e9 _ (by decide), by rw [r9_10, hc3], r9_11, r9_12, r9_13, r9_14, r9_8,
    by rw [r9k _ (by decide), r8' _ (by decide), r7_18], by rw [e9' _ (by decide), e5' _ (by decide), e2' _ (by decide), r19],
    by rw [r9k _ (by decide), r8' _ (by decide), r7_21], by rw [e9' _ (by decide), e5' _ (by decide), r3_22],
    by rw [e9' _ (by decide), e5' _ (by decide), e2' _ (by decide), r23],
    r9_25,
    by rw [e9' _ (by decide), e5' _ (by decide), e2' _ (by decide), r26],
    by rw [e9' _ (by decide), e5' _ (by decide), e2' _ (by decide), r27], w3c_9, w24_9, ?_, ?_, ?_, ?_⟩
  · rw [w40_9, w38_9, q2, hc3]
  · rw [w50_9, w48_9, q4, hc3]
  · rw [w44_9, w4c_9, g7, q6, q5a, q5b, hc3]
  · rw [u9, q8, hc3]

end C3.RV32.P2v

