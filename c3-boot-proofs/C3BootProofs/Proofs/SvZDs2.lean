import C3BootProofs.Proofs.SvZDs

/-!
# `sigstore::verify`: the first half of a constant-time divstep

From the loop body's start at 0x1BA4 to the fourth select's return at
0x1C88: the new `δ`, `f`, and `g` stored, and `u` or `q`, whichever the
step keeps, in `a1:a0`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

theorem zkld {B c : Word} {M M' : Word → BitVec 8} {L : List (Nat × Nat)} (K : SvKeepL B M M' L)
    (hc : c.toNat + 4 ≤ 0x1690) (hL : ∀ p ∈ L, c.toNat + 4 ≤ p.1 ∨ p.1 + p.2 ≤ c.toNat) :
    memLoad32 M' (B + 0x21A0 + c) = memLoad32 M (B + 0x21A0 + c) := by
  rw [← ofNat_toNat_self c]
  exact memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]
    exact K _ (by omega) fun p hp => by have := hL p hp; omega

theorem zkb {B : Word} {M M' : Word → BitVec 8} {L : List (Nat × Nat)} (K : SvKeepL B M M' L) {e : Nat}
    (he : e + 1 ≤ 0x1690) (hL : ∀ p ∈ L, e < p.1 ∨ p.1 + p.2 ≤ e) :
    M' (B + 0x21A0 + BitVec.ofNat 32 e) = M (B + 0x21A0 + BitVec.ofNat 32 e) := K e he hL

theorem w_add0 (x : Word) : x + (0 : Word) = x := BitVec.add_zero x

theorem w_zadd (x : Word) : (0 : Word) + x = x := BitVec.zero_add x

theorem s11_lit (B : Word) : B + 0x21A0 + BitVec.ofNat 32 0xA20 = B + 0x21A0 + 0xA20 := rfl

theorem w64_add2' (dl dh : Word) :
    W64 (dl + 2) (dh + (if (dl + 2).ult dl then 1 else 0)) = (W64 dl dh + 2) % 2 ^ 64 := by
  rw [BitVec.add_comm dh]; exact w64_add2 dl dh

theorem w64_asr' (x xh : Word) : W64 (x >>> 1 ||| xh <<< 31) (xh.sshiftRight 1) = asr64 (W64 x xh) := by
  rw [BitVec.or_comm]; exact w64_asr x xh

/-- The frame bytes a divstep keeps. -/
abbrev ztL : List (Nat × Nat) := [(0x4, 0x18), (0x24, 0x28), (0x5C, 0x8), (0x70, 0x8), (0xA20, 1)]

set_option maxHeartbeats 64000000 in
/-- The first half of a constant-time divstep, from 0x1BA4 to the fourth
select's return at 0x1C88. -/
theorem zt_partA {B : Word} {m : Machine} {dl dh fl fh gl gh ul uh vl vh ql qh rl rh cnt : Word}
    (F : Fr B 0x3830) (E : SvCode m.mem) (IC : SvIvCode m.mem) (st : St m.mem SV m 0x1BA4 (reg m))
    (hsp : reg m sp = B + 0x21A0) (h27 : reg m (27 : Fin 32) = B + 0x21A0 + 0xA20)
    (hdl : memLoad32 m.mem (B + 0x21A0 + 0x34) = dl) (hdh : memLoad32 m.mem (B + 0x21A0 + 0x38) = dh)
    (hfl : memLoad32 m.mem (B + 0x21A0 + 0x30) = fl) (hfh : memLoad32 m.mem (B + 0x21A0 + 0x2C) = fh)
    (hgl : memLoad32 m.mem (B + 0x21A0 + 0x24) = gl) (hgh : memLoad32 m.mem (B + 0x21A0 + 0x28) = gh)
    (hul : reg m (24 : Fin 32) = ul) (huh : memLoad32 m.mem (B + 0x21A0 + 0x3C) = uh)
    (hvl : memLoad32 m.mem (B + 0x21A0 + 0x44) = vl) (hvh : memLoad32 m.mem (B + 0x21A0 + 0x40) = vh)
    (hql : memLoad32 m.mem (B + 0x21A0 + 0x70) = ql) (hqh : memLoad32 m.mem (B + 0x21A0 + 0x60) = qh)
    (hrl : memLoad32 m.mem (B + 0x21A0 + 0x5C) = rl) (hrh : memLoad32 m.mem (B + 0x21A0 + 0x74) = rh)
    (hcnt : memLoad32 m.mem (B + 0x21A0 + 0x48) = cnt) :
    ∃ m', Steps m m' ∧ SvCode m'.mem ∧ SvIvCode m'.mem ∧ (∀ x, SvR B x → m'.mem x = m.mem x) ∧
      SvKeepL B m.mem m'.mem ztL ∧ St m'.mem SV m' 0x1C88 (reg m') ∧ reg m' sp = B + 0x21A0 ∧
      reg m' (3 : Fin 32) = reg m (3 : Fin 32) ∧ reg m' (4 : Fin 32) = reg m (4 : Fin 32) ∧
      (∀ q : Fin 32, q.val ∈ [18, 19, 26] → reg m' q = reg m q) ∧
      reg m' (27 : Fin 32) = B + 0x21A0 + 0xA20 ∧
      reg m' (23 : Fin 32) = ctC3 gl dl dh ∧ reg m' (24 : Fin 32) = ul ∧ reg m' (21 : Fin 32) = uh ∧
      reg m' (9 : Fin 32) = ql ∧ reg m' (22 : Fin 32) = qh ∧
      W64 (reg m' a0) (reg m' a1) = (if ctC3 gl dl dh = 1 then W64 ql qh else W64 ul uh) ∧
      memLoad32 m'.mem (B + 0x21A0 + 0x10) = gl &&& 1 ∧ memLoad32 m'.mem (B + 0x21A0 + 0xC) = ctC1 dl dh ∧
      memLoad32 m'.mem (B + 0x21A0 + 0x48) = cnt ∧
      memLoad32 m'.mem (B + 0x21A0 + 0x44) = vl ∧ memLoad32 m'.mem (B + 0x21A0 + 0x40) = vh ∧
      memLoad32 m'.mem (B + 0x21A0 + 0x70) = ql ∧ memLoad32 m'.mem (B + 0x21A0 + 0x60) = qh ∧
      memLoad32 m'.mem (B + 0x21A0 + 0x5C) = rl ∧ memLoad32 m'.mem (B + 0x21A0 + 0x74) = rh ∧
      W64 (memLoad32 m'.mem (B + 0x21A0 + 0x34)) (memLoad32 m'.mem (B + 0x21A0 + 0x38)) =
        (if ctC3 gl dl dh = 1 then (2 + 2 ^ 64 - W64 dl dh) % 2 ^ 64 else (W64 dl dh + 2) % 2 ^ 64) ∧
      W64 (memLoad32 m'.mem (B + 0x21A0 + 0x30)) (memLoad32 m'.mem (B + 0x21A0 + 0x2C)) =
        (if ctC3 gl dl dh = 1 then W64 gl gh else W64 fl fh) ∧
      W64 (memLoad32 m'.mem (B + 0x21A0 + 0x24)) (memLoad32 m'.mem (B + 0x21A0 + 0x28)) =
        asr64 (if ctC3 gl dl dh = 1 then (W64 gl gh + 2 ^ 64 - W64 (fl &&& ctMk gl) (fh &&& ctMk gl)) % 2 ^ 64
          else (W64 (fl &&& ctMk gl) (fh &&& ctMk gl) + W64 gl gh) % 2 ^ 64) := by
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hS : (B + 0x21A0).toNat + 0x1690 ≤ 2 ^ 32 := by have := FS.hi; omega
  have c101 := c1_01 dl dh
  have gb := gb01 gl
  have c301 := and01w gb c101
  have hz := st.zero
  -- the first block, to the select of `δ` at 0x1C18
  obtain ⟨n1, c1, u1⟩ := st.block zt1 E.self zt1_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, zt1, upd, ↓reduceIte, hsp, h27, w_add0, and_true,
      true_and]
    zt_ok)
  have s1 : St n1.mem SV n1 0x1C18 (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have m1 : n1.mem = (runBlock zt1 (m.mem, reg m)).1 := u1.mem
  have b1 : ∀ q : Fin 32, reg n1 q = (runBlock zt1 (m.mem, reg m)).2 q := u1.regs
  have r20 : reg n1 (20 : Fin 32) = gl := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, zt1, upd, ↓reduceIte, aluEval, hsp, hgl]
  have r22 : reg n1 (22 : Fin 32) = fl := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, zt1, upd, ↓reduceIte, aluEval, hsp, h27, w_add0]
    simp (disch := decide) only [zld_st8 hS, zld_st hS]; exact hfl
  have r25 : reg n1 (25 : Fin 32) = fh := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, zt1, upd, ↓reduceIte, aluEval, hsp, h27, w_add0]
    simp (disch := decide) only [zld_st8 hS, zld_st hS]; exact hfh
  have r9 : reg n1 (9 : Fin 32) = fl &&& ctMk gl := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, zt1, upd, ↓reduceIte, aluEval, hsp, h27, w_add0, hz]
    simp (disch := decide) only [zld_st8 hS, zld_st hS, zst32_get hS, memStore8_same]
    rw [hfl, hgl, zext_trunc01 gb, mask01 gb]
  have r21 : reg n1 (21 : Fin 32) = fh &&& ctMk gl := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, zt1, upd, ↓reduceIte, aluEval, hsp, h27, w_add0, hz]
    simp (disch := decide) only [zld_st8 hS, zld_st hS, zst32_get hS, memStore8_same]
    rw [hfh, hgl, zext_trunc01 gb, mask01' gb]
  have r23 : reg n1 (23 : Fin 32) = ctC3 gl dl dh := by
    rw [b1]; simp +decide only [runBlock, BInstr.run, zt1, upd, ↓reduceIte, aluEval, hsp, h27, w_add0, hz]
    simp (disch := decide) only [zld_st8 hS, zld_st hS]
    rw [hgl, hdl, hdh, show ctC3 gl dl dh = (gl &&& 1) &&& ctC1 dl dh from rfl, ← ctC1_alt]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
  have r10 : reg n1 a0 = ctC3 gl dl dh := by
    rw [b1, ← r23, b1]; simp +decide only [runBlock, BInstr.run, zt1, upd, ↓reduceIte, aluEval, hz]
    exact BitVec.zero_add _
  have q11 : W64 (reg n1 a1) (reg n1 a2) = (W64 dl dh + 2) % 2 ^ 64 := by
    rw [b1, b1]; simp +decide only [runBlock, BInstr.run, zt1, upd, ↓reduceIte, aluEval, hsp, h27, w_add0]
    simp (disch := decide) only [zld_st8 hS, zld_st hS]
    rw [hdl, hdh]; exact w64_add2' _ _
  have q13 : W64 (reg n1 a3) (reg n1 a4) = (2 + 2 ^ 64 - W64 dl dh) % 2 ^ 64 := by
    rw [b1, b1]; simp +decide only [runBlock, BInstr.run, zt1, upd, ↓reduceIte, aluEval, hsp, h27, w_add0, hz]
    simp (disch := decide) only [zld_st8 hS, zld_st hS]
    rw [hdl, hdh]; exact w64_2sub _ _
  have r24 : reg n1 (24 : Fin 32) = ul := by rw [b1, runBlock_reg _ _ _ _ hz (by decide), hul]
  have r27 : reg n1 (27 : Fin 32) = B + 0x21A0 + 0xA20 := by rw [b1, runBlock_reg _ _ _ _ hz (by decide), h27]
  have sp1 : reg n1 sp = B + 0x21A0 := by rw [b1, runBlock_reg _ _ _ _ hz (by decide), hsp]
  have k1 : ∀ q : Fin 32, q.val ∈ [3, 4, 18, 19, 26] → reg n1 q = reg m q := fun q hq => by
    rw [b1, runBlock_reg _ _ _ _ hz (by revert hq; revert q; decide)]
  have w1 : ∀ c : Word, c.toNat + 4 ≤ 0x80 → (c.toNat + 4 ≤ 0xC ∨ 0x14 ≤ c.toNat) →
      memLoad32 n1.mem (B + 0x21A0 + c) = memLoad32 m.mem (B + 0x21A0 + c) := fun c hc h => by
    rw [m1]; simp +decide only [runBlock, BInstr.run, zt1, upd, ↓reduceIte, aluEval, hsp, h27, w_add0]
    rw [zld_st hS (by decide) (by omega) (by show 0xC + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0xC; omega),
      zld_st hS (by decide) (by omega) (by show 0x10 + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0x10; omega),
      zld_st8 hS (by decide) (by omega) (by show 0xA20 + 1 ≤ c.toNat ∨ c.toNat + 4 ≤ 0xA20; omega)]
  have w1_10 : memLoad32 n1.mem (B + 0x21A0 + 0x10) = gl &&& 1 := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, zt1, upd, ↓reduceIte, aluEval, hsp, h27, w_add0]
    simp (disch := decide) only [zld_st8 hS, zld_st hS, memLoad32_store32_same]; rw [hgl]
  have w1_c : memLoad32 n1.mem (B + 0x21A0 + 0xC) = ctC1 dl dh := by
    rw [m1]; simp +decide only [runBlock, BInstr.run, zt1, upd, ↓reduceIte, aluEval, hsp, h27, w_add0, hz]
    simp (disch := decide) only [zld_st8 hS, zld_st hS, memLoad32_store32_same]
    rw [hdl, hdh, ← ctC1_alt]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
  have fr1 : ∀ x, SvR B x → n1.mem x = m.mem x := fun x hx => by
    rw [m1]; simp +decide only [runBlock, BInstr.run, zt1, upd, ↓reduceIte, aluEval, hsp, h27, w_add0]
    simp (disch := decide) only [svR_zst32 hx, svR_zst8 hx]
  have K1 : SvKeepL B m.mem n1.mem ztL := fun e he hL => by
    simp only [ztL, List.forall_mem_cons, List.forall_mem_nil, and_true] at hL
    obtain ⟨h1, h2, h3, h4, h5⟩ := hL
    rw [m1]; simp +decide only [runBlock, BInstr.run, zt1, upd, ↓reduceIte, aluEval, hsp, h27, w_add0]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [zk_st32 hS, zk_st8 hS]
  -- the first select: `δ`
  have E1 : SvCode n1.mem := E.fr F fr1
  have IC1 : SvIvCode n1.mem := IC.sv F fr1
  have c3 : reg n1 a0 = 0 ∨ reg n1 a0 = 1 := by rw [r10]; exact c301
  obtain ⟨n2, P2, K2, k2, v20, v21⟩ := sv_si F E1 IC1 s1 sv_at_1c18 sv_at_1c1c (by decide) (by decide) sp1 c3
  have q2 : W64 (reg n2 a0) (reg n2 a1) = if ctC3 gl dl dh = 1 then (2 + 2 ^ 64 - W64 dl dh) % 2 ^ 64
      else (W64 dl dh + 2) % 2 ^ 64 := by
    rw [v20, v21, w64_sel c3, q11, q13, r10]
  have r2 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n2 q = reg n1 q :=
    P2.regs
  have sp2 : reg n2 sp = B + 0x21A0 := by rw [r2 _ (by decide), sp1]
  have E2 : SvCode n2.mem := E1.fr F P2.fr
  have IC2 : SvIvCode n2.mem := IC1.sv F P2.fr
  -- the second block: store `δ`, select `f`
  have z2 := P2.st.zero
  obtain ⟨n3, c3', u3⟩ := P2.st.block zt2 E2.self zt2_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, zt2, upd, ↓reduceIte, sp2, and_true, true_and]; zt_ok)
  have m3 : n3.mem = (runBlock zt2 (n2.mem, reg n2)).1 := u3.mem
  have b3 : ∀ q : Fin 32, reg n3 q = (runBlock zt2 (n2.mem, reg n2)).2 q := u3.regs
  have s3 : St n3.mem SV n3 0x1C30 (reg n3) := ⟨u3.pc, rfl, fun _ => rfl⟩
  have w3 : ∀ c : Word, c.toNat + 4 ≤ 0x80 → (c.toNat + 4 ≤ 0x34 ∨ 0x3C ≤ c.toNat) →
      memLoad32 n3.mem (B + 0x21A0 + c) = memLoad32 n2.mem (B + 0x21A0 + c) := fun c hc h => by
    rw [m3]; simp +decide only [runBlock, BInstr.run, zt2, upd, ↓reduceIte, aluEval, sp2]
    rw [zld_st hS (by decide) (by omega) (by show 0x38 + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0x38; omega),
      zld_st hS (by decide) (by omega) (by show 0x34 + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0x34; omega)]
  have w3_34 : memLoad32 n3.mem (B + 0x21A0 + 0x34) = reg n2 a0 := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, zt2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [zld_st hS, memLoad32_store32_same]
  have w3_38 : memLoad32 n3.mem (B + 0x21A0 + 0x38) = reg n2 a1 := by
    rw [m3]; simp +decide only [runBlock, BInstr.run, zt2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [zld_st hS, memLoad32_store32_same]
  have r3_8 : reg n3 (8 : Fin 32) = gh := by
    rw [b3]; simp +decide only [runBlock, BInstr.run, zt2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [zld_st hS]
    rw [zkld K2 (by decide) (by simp), w1 _ (by decide) (by decide), hgh]
  have r3_10 : reg n3 a0 = ctC3 gl dl dh := by
    rw [b3]; simp +decide only [runBlock, BInstr.run, zt2, upd, ↓reduceIte, aluEval, z2]
    rw [r2 _ (by decide), r23]; exact BitVec.zero_add _
  have q3 : W64 (reg n3 a3) (reg n3 a4) = W64 gl gh ∧ W64 (reg n3 a1) (reg n3 a2) = W64 fl fh := by
    constructor
    · rw [b3, b3]; simp +decide only [runBlock, BInstr.run, zt2, upd, ↓reduceIte, aluEval, z2, sp2]
      simp (disch := decide) only [zld_st hS]
      rw [r2 _ (by decide), r20, zkld K2 (by decide) (by simp), w1 _ (by decide) (by decide), hgh,
        w_zadd, w_zadd]
    · rw [b3, b3]; simp +decide only [runBlock, BInstr.run, zt2, upd, ↓reduceIte, aluEval, z2]
      rw [r2 _ (by decide), r22, r2 _ (by decide), r25, w_zadd, w_zadd]
  have k3 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n3 q = reg n2 q := fun q hq => by
    rw [b3, runBlock_reg _ _ _ _ z2 (by revert hq; revert q; decide)]
  have fr3 : ∀ x, SvR B x → n3.mem x = n2.mem x := fun x hx => by
    rw [m3]; simp +decide only [runBlock, BInstr.run, zt2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := decide) only [svR_zst32 hx]
  have K3 : SvKeepL B n2.mem n3.mem ztL := fun e he hL => by
    simp only [ztL, List.forall_mem_cons, List.forall_mem_nil, and_true] at hL
    obtain ⟨h1, h2, h3, h4, h5⟩ := hL
    rw [m3]; simp +decide only [runBlock, BInstr.run, zt2, upd, ↓reduceIte, aluEval, sp2]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [zk_st32 hS]
  -- the second select: `f`
  have E3 : SvCode n3.mem := E2.fr F fr3
  have IC3 : SvIvCode n3.mem := IC2.sv F fr3
  have sp3 : reg n3 sp = B + 0x21A0 := by rw [k3 _ (by decide), sp2]
  obtain ⟨n4, P4, K4, k4, v40, v41⟩ := sv_si F E3 IC3 s3 sv_at_1c30 sv_at_1c34 (by decide) (by decide) sp3
    (by rw [r3_10]; exact c301)
  have q4 : W64 (reg n4 a0) (reg n4 a1) = if ctC3 gl dl dh = 1 then W64 gl gh else W64 fl fh := by
    have c3' : reg n3 a0 = 0 ∨ reg n3 a0 = 1 := by rw [r3_10]; exact c301
    rw [v40, v41, w64_sel c3', r3_10, q3.1, q3.2]
  have r4 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n4 q = reg n3 q :=
    P4.regs
  have sp4 : reg n4 sp = B + 0x21A0 := by rw [r4 _ (by decide), sp3]
  have E4 : SvCode n4.mem := E3.fr F P4.fr
  have IC4 : SvIvCode n4.mem := IC3.sv F P4.fr
  -- the third block: store `f`, both candidates for `g`
  have z4 := P4.st.zero
  have e4_9 : reg n4 (9 : Fin 32) = fl &&& ctMk gl := by rw [r4 _ (by decide), k3 _ (by decide), r2 _ (by decide), r9]
  have e4_20 : reg n4 (20 : Fin 32) = gl := by rw [r4 _ (by decide), k3 _ (by decide), r2 _ (by decide), r20]
  have e4_21 : reg n4 (21 : Fin 32) = fh &&& ctMk gl := by
    rw [r4 _ (by decide), k3 _ (by decide), r2 _ (by decide), r21]
  have e4_8 : reg n4 (8 : Fin 32) = gh := by rw [r4 _ (by decide), r3_8]
  have e4_23 : reg n4 (23 : Fin 32) = ctC3 gl dl dh := by
    rw [r4 _ (by decide), k3 _ (by decide), r2 _ (by decide), r23]
  obtain ⟨n5, c5, u5⟩ := P4.st.block zt3 E4.self zt3_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, zt3, upd, ↓reduceIte, sp4, and_true, true_and]; zt_ok)
  have m5 : n5.mem = (runBlock zt3 (n4.mem, reg n4)).1 := u5.mem
  have b5 : ∀ q : Fin 32, reg n5 q = (runBlock zt3 (n4.mem, reg n4)).2 q := u5.regs
  have s5 : St n5.mem SV n5 0x1C5A (reg n5) := ⟨u5.pc, rfl, fun _ => rfl⟩
  have w5 : ∀ c : Word, c.toNat + 4 ≤ 0x80 → (c.toNat + 4 ≤ 0x2C ∨ 0x34 ≤ c.toNat) →
      memLoad32 n5.mem (B + 0x21A0 + c) = memLoad32 n4.mem (B + 0x21A0 + c) := fun c hc h => by
    rw [m5]; simp +decide only [runBlock, BInstr.run, zt3, upd, ↓reduceIte, aluEval, sp4]
    rw [zld_st hS (by decide) (by omega) (by show 0x2C + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0x2C; omega),
      zld_st hS (by decide) (by omega) (by show 0x30 + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0x30; omega)]
  have w5_30 : memLoad32 n5.mem (B + 0x21A0 + 0x30) = reg n4 a0 := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, zt3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [zld_st hS, memLoad32_store32_same]
  have w5_2c : memLoad32 n5.mem (B + 0x21A0 + 0x2C) = reg n4 a1 := by
    rw [m5]; simp +decide only [runBlock, BInstr.run, zt3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [zld_st hS, memLoad32_store32_same]
  have q5a : W64 (reg n5 a1) (reg n5 a2) = (W64 (fl &&& ctMk gl) (fh &&& ctMk gl) + W64 gl gh) % 2 ^ 64 := by
    rw [b5, b5]; simp +decide only [runBlock, BInstr.run, zt3, upd, ↓reduceIte, aluEval]
    rw [e4_9, e4_20, e4_21, e4_8]; exact w64_add _ _ _ _
  have q5b : W64 (reg n5 a3) (reg n5 a4) = (W64 gl gh + 2 ^ 64 - W64 (fl &&& ctMk gl) (fh &&& ctMk gl)) % 2 ^ 64 := by
    rw [b5, b5]; simp +decide only [runBlock, BInstr.run, zt3, upd, ↓reduceIte, aluEval]
    rw [e4_9, e4_20, e4_21, e4_8]; exact w64_sub _ _ _ _
  have r5_10 : reg n5 a0 = ctC3 gl dl dh := by
    rw [b5]; simp +decide only [runBlock, BInstr.run, zt3, upd, ↓reduceIte, aluEval, z4]
    rw [e4_23]; exact BitVec.zero_add _
  have k5 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n5 q = reg n4 q := fun q hq => by
    rw [b5, runBlock_reg _ _ _ _ z4 (by revert hq; revert q; decide)]
  have fr5 : ∀ x, SvR B x → n5.mem x = n4.mem x := fun x hx => by
    rw [m5]; simp +decide only [runBlock, BInstr.run, zt3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := decide) only [svR_zst32 hx]
  have K5 : SvKeepL B n4.mem n5.mem ztL := fun e he hL => by
    simp only [ztL, List.forall_mem_cons, List.forall_mem_nil, and_true] at hL
    obtain ⟨h1, h2, h3, h4, h5⟩ := hL
    rw [m5]; simp +decide only [runBlock, BInstr.run, zt3, upd, ↓reduceIte, aluEval, sp4]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [zk_st32 hS]
  -- the third select: `g`
  have E5 : SvCode n5.mem := E4.fr F fr5
  have IC5 : SvIvCode n5.mem := IC4.sv F fr5
  have sp5 : reg n5 sp = B + 0x21A0 := by rw [k5 _ (by decide), sp4]
  obtain ⟨n6, P6, K6, k6, v60, v61⟩ := sv_si F E5 IC5 s5 sv_at_1c5a sv_at_1c5e (by decide) (by decide) sp5
    (by rw [r5_10]; exact c301)
  have q6 : W64 (reg n6 a0) (reg n6 a1) = if ctC3 gl dl dh = 1 then
      (W64 gl gh + 2 ^ 64 - W64 (fl &&& ctMk gl) (fh &&& ctMk gl)) % 2 ^ 64
      else (W64 (fl &&& ctMk gl) (fh &&& ctMk gl) + W64 gl gh) % 2 ^ 64 := by
    have c5' : reg n5 a0 = 0 ∨ reg n5 a0 = 1 := by rw [r5_10]; exact c301
    rw [v60, v61, w64_sel c5', r5_10, q5a, q5b]
  have r6 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n6 q = reg n5 q :=
    P6.regs
  have sp6 : reg n6 sp = B + 0x21A0 := by rw [r6 _ (by decide), sp5]
  have E6 : SvCode n6.mem := E5.fr F P6.fr
  have IC6 : SvIvCode n6.mem := IC5.sv F P6.fr
  -- the fourth block: store `g`, both candidates for `u`
  have z6 := P6.st.zero
  obtain ⟨n7, c7, u7⟩ := P6.st.block zt4 E6.self zt4_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, zt4, upd, ↓reduceIte, sp6, and_true, true_and]; zt_ok)
  have m7 : n7.mem = (runBlock zt4 (n6.mem, reg n6)).1 := u7.mem
  have b7 : ∀ q : Fin 32, reg n7 q = (runBlock zt4 (n6.mem, reg n6)).2 q := u7.regs
  have s7 : St n7.mem SV n7 0x1C80 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  -- frame words untouched since the start
  have wk : ∀ c : Word, c.toNat + 4 ≤ 0x80 → (c.toNat + 4 ≤ 0xC ∨ 0x3C ≤ c.toNat) →
      memLoad32 n6.mem (B + 0x21A0 + c) = memLoad32 m.mem (B + 0x21A0 + c) := fun c hc h => by
    rw [zkld K6 (by omega) (by simp), w5 c hc (by omega), zkld K4 (by omega) (by simp), w3 c hc (by omega),
      zkld K2 (by omega) (by simp), w1 c hc (by omega)]
  have w7 : ∀ c : Word, c.toNat + 4 ≤ 0x80 → (c.toNat + 4 ≤ 0x24 ∨ 0x2C ≤ c.toNat) →
      memLoad32 n7.mem (B + 0x21A0 + c) = memLoad32 n6.mem (B + 0x21A0 + c) := fun c hc h => by
    rw [m7]; simp +decide only [runBlock, BInstr.run, zt4, upd, ↓reduceIte, aluEval, sp6]
    rw [zld_st hS (by decide) (by omega) (by show 0x28 + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0x28; omega),
      zld_st hS (by decide) (by omega) (by show 0x24 + 4 ≤ c.toNat ∨ c.toNat + 4 ≤ 0x24; omega)]
  have g7 : W64 (memLoad32 n7.mem (B + 0x21A0 + 0x24)) (memLoad32 n7.mem (B + 0x21A0 + 0x28)) =
      asr64 (W64 (reg n6 a0) (reg n6 a1)) := by
    rw [m7]; simp +decide only [runBlock, BInstr.run, zt4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [zld_st hS, memLoad32_store32_same]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    exact w64_asr' _ _
  have r7_21 : reg n7 (21 : Fin 32) = uh := by
    rw [b7]; simp +decide only [runBlock, BInstr.run, zt4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [zld_st hS]; rw [wk _ (by decide) (by decide), huh]
  have r7_9 : reg n7 (9 : Fin 32) = ql := by
    rw [b7]; simp +decide only [runBlock, BInstr.run, zt4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [zld_st hS]; rw [wk _ (by decide) (by decide), hql]
  have r7_22 : reg n7 (22 : Fin 32) = qh := by
    rw [b7]; simp +decide only [runBlock, BInstr.run, zt4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [zld_st hS]; rw [wk _ (by decide) (by decide), hqh]
  have e6_24 : reg n6 (24 : Fin 32) = ul := by
    rw [r6 _ (by decide), k5 _ (by decide), r4 _ (by decide), k3 _ (by decide), r2 _ (by decide), r24]
  have e6_23 : reg n6 (23 : Fin 32) = ctC3 gl dl dh := by rw [r6 _ (by decide), k5 _ (by decide), e4_23]
  have k7 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 18, 19, 20, 23, 24, 25, 26, 27] → reg n7 q = reg n6 q := fun q hq => by
    rw [b7, runBlock_reg _ _ _ _ z6 (by revert hq; revert q; decide)]
  have q7 : W64 (reg n7 a3) (reg n7 a4) = W64 ql qh ∧ W64 (reg n7 a1) (reg n7 a2) = W64 ul uh ∧
      reg n7 a0 = ctC3 gl dl dh := by
    refine ⟨?_, ?_, ?_⟩
    · rw [b7, b7]; simp +decide only [runBlock, BInstr.run, zt4, upd, ↓reduceIte, aluEval, z6, sp6]
      simp (disch := decide) only [zld_st hS]
      rw [wk _ (by decide) (by decide), wk _ (by decide) (by decide), hql, hqh, w_zadd, w_zadd]
    · rw [b7, b7]; simp +decide only [runBlock, BInstr.run, zt4, upd, ↓reduceIte, aluEval, z6, sp6]
      simp (disch := decide) only [zld_st hS]
      rw [e6_24, wk _ (by decide) (by decide), huh, w_zadd, w_zadd]
    · rw [b7]; simp +decide only [runBlock, BInstr.run, zt4, upd, ↓reduceIte, aluEval, z6]
      rw [e6_23]; exact BitVec.zero_add _
  have fr7 : ∀ x, SvR B x → n7.mem x = n6.mem x := fun x hx => by
    rw [m7]; simp +decide only [runBlock, BInstr.run, zt4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := decide) only [svR_zst32 hx]
  have K7 : SvKeepL B n6.mem n7.mem ztL := fun e he hL => by
    simp only [ztL, List.forall_mem_cons, List.forall_mem_nil, and_true] at hL
    obtain ⟨h1, h2, h3, h4, h5⟩ := hL
    rw [m7]; simp +decide only [runBlock, BInstr.run, zt4, upd, ↓reduceIte, aluEval, sp6]
    simp (disch := first | decide | omega |
      (simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceMod]; omega))
      only [zk_st32 hS]
  -- the fourth select: `u` or `q`
  have E7 : SvCode n7.mem := E6.fr F fr7
  have IC7 : SvIvCode n7.mem := IC6.sv F fr7
  have sp7 : reg n7 sp = B + 0x21A0 := by rw [k7 _ (by decide), sp6]
  obtain ⟨n8, P8, K8, k8, v80, v81⟩ := sv_si F E7 IC7 s7 sv_at_1c80 sv_at_1c84 (by decide) (by decide) sp7
    (by rw [q7.2.2]; exact c301)
  have r8 : ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n8 q = reg n7 q :=
    P8.regs
  have fr8 : ∀ x, SvR B x → n8.mem x = m.mem x := fun x hx => by
    rw [P8.fr x hx, fr7 x hx, P6.fr x hx, fr5 x hx, P4.fr x hx, fr3 x hx, P2.fr x hx, fr1 x hx]
  have w8 : ∀ c : Word, c.toNat + 4 ≤ 0x80 → (c.toNat + 4 ≤ 0x24 ∨ 0x2C ≤ c.toNat) →
      memLoad32 n8.mem (B + 0x21A0 + c) = memLoad32 n6.mem (B + 0x21A0 + c) := fun c hc h => by
    rw [zkld K8 (by omega) (by simp), w7 c hc h]
  have e6_34 : ∀ c : Word, c.toNat + 4 ≤ 0x80 → (c.toNat + 4 ≤ 0x2C ∨ 0x34 ≤ c.toNat) →
      memLoad32 n6.mem (B + 0x21A0 + c) = memLoad32 n4.mem (B + 0x21A0 + c) := fun c hc h => by
    rw [zkld K6 (by omega) (by simp), w5 c hc h]
  have e4_3c : ∀ c : Word, c.toNat + 4 ≤ 0x80 → (c.toNat + 4 ≤ 0x34 ∨ 0x3C ≤ c.toNat) →
      memLoad32 n4.mem (B + 0x21A0 + c) = memLoad32 n2.mem (B + 0x21A0 + c) := fun c hc h => by
    rw [zkld K4 (by omega) (by simp), w3 c hc h]
  refine ⟨n8, c1.trans (P2.steps.trans (c3'.trans (P4.steps.trans (c5.trans (P6.steps.trans (c7.trans P8.steps)))))),
    E7.fr F P8.fr, IC7.sv F P8.fr, fr8, ?_, P8.st, by rw [r8 _ (by decide), sp7],
    by rw [r8 _ (by decide), k7 _ (by decide), r6 _ (by decide), k5 _ (by decide), r4 _ (by decide),
      k3 _ (by decide), r2 _ (by decide), k1 _ (by decide)],
    by rw [r8 _ (by decide), k7 _ (by decide), r6 _ (by decide), k5 _ (by decide), r4 _ (by decide),
      k3 _ (by decide), r2 _ (by decide), k1 _ (by decide)],
    fun q hq => by rw [r8 q (by revert hq; revert q; decide), k7 q (by revert hq; revert q; decide),
      r6 q (by revert hq; revert q; decide), k5 q (by revert hq; revert q; decide),
      r4 q (by revert hq; revert q; decide), k3 q (by revert hq; revert q; decide),
      r2 q (by revert hq; revert q; decide), k1 q (by revert hq; revert q; decide)],
    by rw [r8 _ (by decide), k7 _ (by decide), r6 _ (by decide), k5 _ (by decide), r4 _ (by decide),
      k3 _ (by decide), r2 _ (by decide), r27],
    by rw [r8 _ (by decide), k7 _ (by decide), e6_23], by rw [r8 _ (by decide), k7 _ (by decide), e6_24],
    by rw [r8 _ (by decide), r7_21], by rw [r8 _ (by decide), r7_9], by rw [r8 _ (by decide), r7_22],
    by rw [v80, v81, w64_sel (by rw [q7.2.2]; exact c301), q7.2.2, q7.1, q7.2.1],
    by rw [w8 _ (by decide) (by decide), e6_34 _ (by decide) (by decide), e4_3c _ (by decide) (by decide),
      zkld K2 (by decide) (by simp), w1_10],
    by rw [w8 _ (by decide) (by decide), e6_34 _ (by decide) (by decide), e4_3c _ (by decide) (by decide),
      zkld K2 (by decide) (by simp), w1_c],
    by rw [w8 _ (by decide) (by decide), wk _ (by decide) (by decide), hcnt],
    by rw [w8 _ (by decide) (by decide), wk _ (by decide) (by decide), hvl],
    by rw [w8 _ (by decide) (by decide), wk _ (by decide) (by decide), hvh],
    by rw [w8 _ (by decide) (by decide), wk _ (by decide) (by decide), hql],
    by rw [w8 _ (by decide) (by decide), wk _ (by decide) (by decide), hqh],
    by rw [w8 _ (by decide) (by decide), wk _ (by decide) (by decide), hrl],
    by rw [w8 _ (by decide) (by decide), wk _ (by decide) (by decide), hrh],
    by rw [w8 _ (by decide) (by decide), w8 _ (by decide) (by decide), e6_34 _ (by decide) (by decide),
      e6_34 _ (by decide) (by decide), zkld K4 (by decide) (by simp), zkld K4 (by decide) (by simp), w3_34, w3_38, q2],
    by rw [w8 _ (by decide) (by decide), w8 _ (by decide) (by decide), zkld K6 (by decide) (by simp),
      zkld K6 (by decide) (by simp), w5_30, w5_2c, q4],
    by rw [zkld K8 (by decide) (by simp), zkld K8 (by decide) (by simp), g7, q6]⟩
  intro e he hL
  rw [K8 e he (by simp), K7 e he hL, K6 e he (by simp), K5 e he hL, K4 e he (by simp), K3 e he hL,
    K2 e he (by simp), K1 e he hL]

end C3.RV32.Sv
