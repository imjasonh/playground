import C3BootProofs.Proofs.ScalarMontBody

/-!
# `curve25519_dalek`'s `Scalar29::montgomery_mul`, as compiled

`montgomery_mul(a, b)` is `montgomery_reduce(mul_internal(a, b))`, both
inlined, followed by a call to `Scalar29::sub(r, &L)`. The compiled function
saves the registers, runs the straight-line body that `ScalarMontBody.lean`
proves, stores the nine reduced limbs in its frame, calls the proved `sub`
on them, and restores the registers.
-/

namespace C3.RV32

open C3.Image

/-- `montgomery_reduce(mul_internal(a, b))`'s limb `i`, before the final `sub`.
It is written with `Nat.rec` rather than `match` so that the kernel reduces
`smmRed a b 8` to `smvR8 a b` without unfolding `smvR8`'s 400 definitions. -/
def smmRed (a b : Nat → Nat) (i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (smvR0 a b) (fun i _ =>
  Nat.rec (motive := fun _ => Nat) (smvR1 a b) (fun i _ =>
  Nat.rec (motive := fun _ => Nat) (smvR2 a b) (fun i _ =>
  Nat.rec (motive := fun _ => Nat) (smvR3 a b) (fun i _ =>
  Nat.rec (motive := fun _ => Nat) (smvR4 a b) (fun i _ =>
  Nat.rec (motive := fun _ => Nat) (smvR5 a b) (fun i _ =>
  Nat.rec (motive := fun _ => Nat) (smvR6 a b) (fun i _ =>
  Nat.rec (motive := fun _ => Nat) (smvR7 a b) (fun _ _ => smvR8 a b) i) i) i) i) i) i) i) i

/-- Where `Scalar29::montgomery_mul` runs: its code, `sub`'s code and its
callees' and `L` at their offsets from `S = P - 0x310`, the 0x1F0 bytes of
stack at `G` that it and `sub` use, the result `out`, and the operands at
`ap` and `bp`, each apart from what it must not touch. -/
structure SMEnv (M : Word → BitVec 8) (P G out ap bp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P scalar29MontMulCode
  scode : CodeIn M (P + 0xFFFFFCF0) scalar29SubCode
  idx : CodeIn M (P + 0xFFFFFCF0 + 0x278) scalar29IndexCode
  idxm : CodeIn M (P + 0xFFFFFCF0 + 0x292) scalar29IndexMutCode
  mset : CodeIn M (P + 0xFFFFFCF0 + 0x5B9C) memsetCode
  stub : CodeIn M (P + 0xFFFFFCF0 + 0x5C04) memcpyStubCode
  body : CodeIn M (P + 0xFFFFFCF0 + 0x5C0C) memcpyBodyCode
  bb : CodeIn M (P + 0xFFFFFCF0 + 0xFFFFEAFA) blackBoxU8Code
  ldata : CodeIn M (BitVec.ofNat 32 scalarLAddress) scalarLData
  hG : G.toNat % 4 = 0
  hGt : G.toNat + 0x1F0 ≤ 2 ^ 32
  hout : out.toNat % 4 = 0
  hot : out.toNat + 36 < 2 ^ 32
  hap : ap.toNat % 4 = 0
  hbp : bp.toNat % 4 = 0
  sGC : Sep G 0x1F0 P scalar29MontMulCode.length
  sGS : Sep G 0x1F0 (P + 0xFFFFFCF0) scalar29SubCode.length
  sGI : Sep G 0x1F0 (P + 0xFFFFFCF0 + 0x278) scalar29IndexCode.length
  sGIM : Sep G 0x1F0 (P + 0xFFFFFCF0 + 0x292) scalar29IndexMutCode.length
  sGM : Sep G 0x1F0 (P + 0xFFFFFCF0 + 0x5B9C) memsetCode.length
  sGSt : Sep G 0x1F0 (P + 0xFFFFFCF0 + 0x5C04) memcpyStubCode.length
  sGB : Sep G 0x1F0 (P + 0xFFFFFCF0 + 0x5C0C) memcpyBodyCode.length
  sGBB : Sep G 0x1F0 (P + 0xFFFFFCF0 + 0xFFFFEAFA) blackBoxU8Code.length
  sGL : Sep G 0x1F0 (BitVec.ofNat 32 scalarLAddress) 36
  sAG : Sep ap 36 G 0x1F0
  sBG : Sep bp 36 G 0x1F0
  sOG : Sep out 36 G 0x1F0
  sOS : Sep out 36 (P + 0xFFFFFCF0) scalar29SubCode.length
  sOB : Sep out 36 (P + 0xFFFFFCF0 + 0x5C0C) memcpyBodyCode.length
  sOC : Sep out 36 P scalar29MontMulCode.length

/-- The registers the function saves, at offsets from its `sp`. -/
abbrev smmPs : List (Fin 32 × Word) :=
  [(ra, 0x18C), ((8 : Fin 32), 0x188), ((9 : Fin 32), 0x184), ((18 : Fin 32), 0x180), ((19 : Fin 32), 0x17C), ((20 : Fin 32), 0x178), ((21 : Fin 32), 0x174), ((22 : Fin 32), 0x170), ((23 : Fin 32), 0x16C), ((24 : Fin 32), 0x168), ((25 : Fin 32), 0x164), ((26 : Fin 32), 0x160), ((27 : Fin 32), 0x15C)]

theorem smm_sub_at (P : Word) : P + BitVec.ofNat 32 0xDB2 + 0xFFFFF000 + 0xFFFFFF3E = P + 0xFFFFFCF0 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; rfl

theorem smmF_ofs (G : Word) (c : Nat) : G + 0x60 + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x60 + c) := by
  rw [show (0x60 : Word) = BitVec.ofNat 32 0x60 from rfl, add_ofNat_assoc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
/-- **The compiled `Scalar29::montgomery_mul`**, called with the result at
`out` and the operands at `ap` and `bp`: limb `j` of `out` is `sub`'s limb `j`
of `montgomery_reduce(mul_internal(a, b))` for the operands' limbs, as the
Rust source computes them. It returns with `sp` and every register but `t0`
through `t6` and `a0` through `a7` as they were, and changes no memory outside
its and `sub`'s 0x1F0 bytes of stack and the result. -/
theorem scalar29MontMul_correct (m : Machine) {P G out ap bp retAddr : Word} (env : SMEnv m.mem P G out ap bp)
    (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = ap) (ha2 : reg m a2 = bp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = G + 0x1F0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = G + 0x1F0 ∧ (∀ q, feMKeep q = true → reg m' q = reg m q) ∧
      (∀ j, j < 9 → memLoad32 m'.mem (out + BitVec.ofNat 32 (4 * j)) =
        BitVec.ofNat 32 (s29Out (smmRed (smmIn m.mem ap) (smmIn m.mem bp)) j)) ∧
      ∀ x, Sep G 0x1F0 x 1 → Sep out 36 x 1 → m'.mem x = m.mem x := by
  obtain ⟨F, hF⟩ : ∃ F, G + 0x60 = F := ⟨_, rfl⟩
  have hGt := env.hGt
  have hFn : F.toNat = G.toNat + 0x60 := by
    rw [← hF, BitVec.toNat_add, show (0x60 : Word).toNat = 0x60 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hFa : F.toNat % 4 = 0 := by rw [hFn]; have := env.hG; omega
  have fG : ∀ c, F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x60 + c) := fun c => by rw [← hF]; exact smmF_ofs G c
  have inF : ∀ {b : Word} {n k : Nat}, Sep G 0x1F0 b k → Sep F 0x190 b k := fun h => by
    rw [← hF]; exact h.sub (c := 0x60) (l := 0x190) (by decide)
  have sFC : Sep F 0x190 P scalar29MontMulCode.length := inF (n := 0) env.sGC
  -- the prologue: the frame, and the registers saved at its top
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code smm_at_0 (off' := 0x2) (by decide)
  have k1 := u1.oldReg hz
  have sp1 : reg m1 sp = F := by
    rw [u1.newReg (by decide)]; show reg m sp + 0xFFFFFE70 = _
    rw [hsp, ← hF, BitVec.add_assoc]; rfl
  obtain ⟨m2, d2, u2⟩ := u1.self.aluImm env.code smm_at_2 (off' := 0x4) (by decide)
  have k2 := u2.oldReg u1.self.zero
  have a3_2 : reg m2 a3 = F + 0x180 := by rw [u2.newReg (by decide)]; show reg m1 sp + 0x180 = _; rw [sp1]
  have sp2 : reg m2 sp = F := by rw [k2 _ (by decide), sp1]
  have rk : ∀ q, q ≠ sp → q ≠ a3 → reg m2 q = reg m q := fun q h1 h2 => by rw [k2 q h2, k1 q h1]
  have u2' : St m.mem P m2 0x4 (reg m2) := u2.self
  obtain ⟨p0, dp0, up0⟩ := u2'.swG env.code smm_at_4 (off' := 0x8) (by decide)
    (by rw [a3_2, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x18C) (v := reg m ra) (by rw [a3_2, BitVec.add_assoc]; rfl)
    (rk _ (by decide) (by decide))
  obtain ⟨P0, hP0⟩ : ∃ M', memStore32 m.mem (F + 0x18C) (reg m ra) = M' := ⟨_, rfl⟩
  rw [hP0] at up0
  have hcp0 : CodeIn P0 P scalar29MontMulCode := by rw [← hP0]; exact env.code.store32 (frm_sep' sFC (by decide))
  obtain ⟨p1, dp1, up1⟩ := up0.swG hcp0 smm_at_8 (off' := 0xA) (by decide)
    (by rw [a3_2, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x188) (v := reg m (8 : Fin 32)) (by rw [a3_2, BitVec.add_assoc]; rfl)
    (rk _ (by decide) (by decide))
  obtain ⟨P1, hP1⟩ : ∃ M', memStore32 P0 (F + 0x188) (reg m (8 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP1] at up1
  have hcp1 : CodeIn P1 P scalar29MontMulCode := by rw [← hP1]; exact hcp0.store32 (frm_sep' sFC (by decide))
  obtain ⟨p2, dp2, up2⟩ := up1.swG hcp1 smm_at_a (off' := 0xC) (by decide)
    (by rw [a3_2, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x184) (v := reg m (9 : Fin 32)) (by rw [a3_2, BitVec.add_assoc]; rfl)
    (rk _ (by decide) (by decide))
  obtain ⟨P2, hP2⟩ : ∃ M', memStore32 P1 (F + 0x184) (reg m (9 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP2] at up2
  have hcp2 : CodeIn P2 P scalar29MontMulCode := by rw [← hP2]; exact hcp1.store32 (frm_sep' sFC (by decide))
  obtain ⟨p3, dp3, up3⟩ := up2.swG hcp2 smm_at_c (off' := 0x10) (by decide)
    (by rw [a3_2, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x180) (v := reg m (18 : Fin 32)) (by rw [a3_2, BitVec.add_assoc]; rfl)
    (rk _ (by decide) (by decide))
  obtain ⟨P3, hP3⟩ : ∃ M', memStore32 P2 (F + 0x180) (reg m (18 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP3] at up3
  have hcp3 : CodeIn P3 P scalar29MontMulCode := by rw [← hP3]; exact hcp2.store32 (frm_sep' sFC (by decide))
  obtain ⟨p4, dp4, up4⟩ := up3.swG hcp3 smm_at_10 (off' := 0x14) (by decide)
    (by rw [sp2]; exact fr_al' hFa (by decide)) (a := F + 0x17C) (v := reg m (19 : Fin 32)) (by rw [sp2])
    (rk _ (by decide) (by decide))
  obtain ⟨P4, hP4⟩ : ∃ M', memStore32 P3 (F + 0x17C) (reg m (19 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP4] at up4
  have hcp4 : CodeIn P4 P scalar29MontMulCode := by rw [← hP4]; exact hcp3.store32 (frm_sep' sFC (by decide))
  obtain ⟨p5, dp5, up5⟩ := up4.swG hcp4 smm_at_14 (off' := 0x18) (by decide)
    (by rw [sp2]; exact fr_al' hFa (by decide)) (a := F + 0x178) (v := reg m (20 : Fin 32)) (by rw [sp2])
    (rk _ (by decide) (by decide))
  obtain ⟨P5, hP5⟩ : ∃ M', memStore32 P4 (F + 0x178) (reg m (20 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP5] at up5
  have hcp5 : CodeIn P5 P scalar29MontMulCode := by rw [← hP5]; exact hcp4.store32 (frm_sep' sFC (by decide))
  obtain ⟨p6, dp6, up6⟩ := up5.swG hcp5 smm_at_18 (off' := 0x1C) (by decide)
    (by rw [sp2]; exact fr_al' hFa (by decide)) (a := F + 0x174) (v := reg m (21 : Fin 32)) (by rw [sp2])
    (rk _ (by decide) (by decide))
  obtain ⟨P6, hP6⟩ : ∃ M', memStore32 P5 (F + 0x174) (reg m (21 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP6] at up6
  have hcp6 : CodeIn P6 P scalar29MontMulCode := by rw [← hP6]; exact hcp5.store32 (frm_sep' sFC (by decide))
  obtain ⟨p7, dp7, up7⟩ := up6.swG hcp6 smm_at_1c (off' := 0x20) (by decide)
    (by rw [sp2]; exact fr_al' hFa (by decide)) (a := F + 0x170) (v := reg m (22 : Fin 32)) (by rw [sp2])
    (rk _ (by decide) (by decide))
  obtain ⟨P7, hP7⟩ : ∃ M', memStore32 P6 (F + 0x170) (reg m (22 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP7] at up7
  have hcp7 : CodeIn P7 P scalar29MontMulCode := by rw [← hP7]; exact hcp6.store32 (frm_sep' sFC (by decide))
  obtain ⟨p8, dp8, up8⟩ := up7.swG hcp7 smm_at_20 (off' := 0x24) (by decide)
    (by rw [sp2]; exact fr_al' hFa (by decide)) (a := F + 0x16C) (v := reg m (23 : Fin 32)) (by rw [sp2])
    (rk _ (by decide) (by decide))
  obtain ⟨P8, hP8⟩ : ∃ M', memStore32 P7 (F + 0x16C) (reg m (23 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP8] at up8
  have hcp8 : CodeIn P8 P scalar29MontMulCode := by rw [← hP8]; exact hcp7.store32 (frm_sep' sFC (by decide))
  obtain ⟨p9, dp9, up9⟩ := up8.swG hcp8 smm_at_24 (off' := 0x28) (by decide)
    (by rw [sp2]; exact fr_al' hFa (by decide)) (a := F + 0x168) (v := reg m (24 : Fin 32)) (by rw [sp2])
    (rk _ (by decide) (by decide))
  obtain ⟨P9, hP9⟩ : ∃ M', memStore32 P8 (F + 0x168) (reg m (24 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP9] at up9
  have hcp9 : CodeIn P9 P scalar29MontMulCode := by rw [← hP9]; exact hcp8.store32 (frm_sep' sFC (by decide))
  obtain ⟨p10, dp10, up10⟩ := up9.swG hcp9 smm_at_28 (off' := 0x2C) (by decide)
    (by rw [sp2]; exact fr_al' hFa (by decide)) (a := F + 0x164) (v := reg m (25 : Fin 32)) (by rw [sp2])
    (rk _ (by decide) (by decide))
  obtain ⟨P10, hP10⟩ : ∃ M', memStore32 P9 (F + 0x164) (reg m (25 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP10] at up10
  have hcp10 : CodeIn P10 P scalar29MontMulCode := by rw [← hP10]; exact hcp9.store32 (frm_sep' sFC (by decide))
  obtain ⟨p11, dp11, up11⟩ := up10.swG hcp10 smm_at_2c (off' := 0x30) (by decide)
    (by rw [sp2]; exact fr_al' hFa (by decide)) (a := F + 0x160) (v := reg m (26 : Fin 32)) (by rw [sp2])
    (rk _ (by decide) (by decide))
  obtain ⟨P11, hP11⟩ : ∃ M', memStore32 P10 (F + 0x160) (reg m (26 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP11] at up11
  have hcp11 : CodeIn P11 P scalar29MontMulCode := by rw [← hP11]; exact hcp10.store32 (frm_sep' sFC (by decide))
  obtain ⟨p12, dp12, up12⟩ := up11.swG hcp11 smm_at_30 (off' := 0x34) (by decide)
    (by rw [sp2]; exact fr_al' hFa (by decide)) (a := F + 0x15C) (v := reg m (27 : Fin 32)) (by rw [sp2])
    (rk _ (by decide) (by decide))
  obtain ⟨P12, hP12⟩ : ∃ M', memStore32 P11 (F + 0x15C) (reg m (27 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP12] at up12
  have hcp12 : CodeIn P12 P scalar29MontMulCode := by rw [← hP12]; exact hcp11.store32 (frm_sep' sFC (by decide))
  have hsv : P12 = saveMem m.mem F (reg m) smmPs := by
    rw [← hP12, ← hP11, ← hP10, ← hP9, ← hP8, ← hP7, ← hP6, ← hP5, ← hP4, ← hP3, ← hP2, ← hP1, ← hP0]; rfl
  have frSv : ∀ x, Sep F 0x190 x 1 → P12 x = m.mem x := fun x hx => by
    rw [hsv]; exact saveMem_outside smmPs fun p hp => frm_sep' hx (by revert hp; revert p; decide)
  have hsl : ∀ r o, (r, o) ∈ smmPs → memLoad32 P12 (F + o) = reg m r := fun r o h => by
    rw [hsv]
    simp only [smmPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
  have cOf : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep G 0x1F0 b code.length →
      CodeIn P12 b code := fun hc hs i hi => by
    rw [frSv _ ((inF (n := 0) hs).subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have sXF : Sep ap 36 F 0x190 := by rw [← hF]; exact env.sAG.subR (c := 0x60) (l := 0x190) (by decide)
  have sYF : Sep bp 36 F 0x190 := by rw [← hF]; exact env.sBG.subR (c := 0x60) (l := 0x190) (by decide)
  -- the body
  have pr : ∀ q, reg p12 q = reg m2 q := up12.regs
  obtain ⟨n1, M1, c1, w1, fr1, ks0, ks1, ks2, ks3, ks4, ks5, ks6, ks7, ks8, ks9, ks10, ks11, ks12, kout, houts, sp_1, g3_1, g4_1⟩ :=
    smm_body (M := P12) (B := P) (F := F) (outp := out) up12.self hcp12 (by rw [pr, sp2])
      (by rw [pr, rk _ (by decide) (by decide), ha0]) (by rw [pr, rk _ (by decide) (by decide), ha1])
      (by rw [pr, rk _ (by decide) (by decide), ha2]) hFa env.hap env.hbp sFC sXF sYF
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at houts
  obtain ⟨o0, o1, o2, o3, o4, o5, o6, o7, o8, -⟩ := houts
  have smmIn_eq : ∀ p, Sep p 36 F 0x190 → smmIn P12 p = smmIn m.mem p := fun p hp => funext fun i => by
    unfold smmIn
    by_cases hi : i < 9
    · rw [ite_eq_left hi, ite_eq_left hi]; unfold limbAt
      rw [load_frame frSv (hp.symm.subR (c := 4 * i) (l := 4) (by omega))]
    · rw [ite_eq_right hi, ite_eq_right hi]
  rw [smmIn_eq ap sXF, smmIn_eq bp sYF] at o0 o1 o2 o3 o4 o5 o6 o7 o8
  have M1m : ∀ x, Sep F 0x190 x 1 → M1 x = m.mem x := fun x hx => by rw [fr1 x hx, frSv x hx]
  have hc1 : CodeIn M1 P scalar29MontMulCode := fun i hi => by
    rw [M1m _ (sFC.subR (c := i) (l := 1) (by omega))]; exact env.code i hi
  -- the reduced limbs to `F + 0x138`
  obtain ⟨t1, e1, v1⟩ := w1.aluImm hc1 smm_at_d94 (off' := 0xD96) (by decide)
  have a1_t : reg t1 a1 = F + 0x100 := by rw [v1.newReg (by decide)]; show reg n1 sp + 0x100 = _; rw [sp_1]
  have tk := v1.oldReg w1.zero
  have v1' : St M1 P t1 0xD96 (reg t1) := v1.self
  obtain ⟨q0, dq0, uq0⟩ := v1'.swG hc1 smm_at_d96 (off' := 0xD98) (by decide)
    (by rw [a1_t, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x138) (v := reg n1 a2)
    (by rw [a1_t, BitVec.add_assoc]; rfl) (tk _ (by decide))
  obtain ⟨Q0, hQ0⟩ : ∃ M', memStore32 M1 (F + 0x138) (reg n1 a2) = M' := ⟨_, rfl⟩
  rw [hQ0] at uq0
  have hcq0 : CodeIn Q0 P scalar29MontMulCode := by rw [← hQ0]; exact hc1.store32 (frm_sep' sFC (by decide))
  obtain ⟨q1, dq1, uq1⟩ := uq0.swG hcq0 smm_at_d98 (off' := 0xD9A) (by decide)
    (by rw [a1_t, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x13C) (v := reg n1 a3)
    (by rw [a1_t, BitVec.add_assoc]; rfl) (tk _ (by decide))
  obtain ⟨Q1, hQ1⟩ : ∃ M', memStore32 Q0 (F + 0x13C) (reg n1 a3) = M' := ⟨_, rfl⟩
  rw [hQ1] at uq1
  have hcq1 : CodeIn Q1 P scalar29MontMulCode := by rw [← hQ1]; exact hcq0.store32 (frm_sep' sFC (by decide))
  obtain ⟨q2, dq2, uq2⟩ := uq1.swG hcq1 smm_at_d9a (off' := 0xD9C) (by decide)
    (by rw [a1_t, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x140) (v := reg n1 a4)
    (by rw [a1_t, BitVec.add_assoc]; rfl) (tk _ (by decide))
  obtain ⟨Q2, hQ2⟩ : ∃ M', memStore32 Q1 (F + 0x140) (reg n1 a4) = M' := ⟨_, rfl⟩
  rw [hQ2] at uq2
  have hcq2 : CodeIn Q2 P scalar29MontMulCode := by rw [← hQ2]; exact hcq1.store32 (frm_sep' sFC (by decide))
  obtain ⟨q3, dq3, uq3⟩ := uq2.swG hcq2 smm_at_d9c (off' := 0xD9E) (by decide)
    (by rw [a1_t, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x144) (v := reg n1 a5)
    (by rw [a1_t, BitVec.add_assoc]; rfl) (tk _ (by decide))
  obtain ⟨Q3, hQ3⟩ : ∃ M', memStore32 Q2 (F + 0x144) (reg n1 a5) = M' := ⟨_, rfl⟩
  rw [hQ3] at uq3
  have hcq3 : CodeIn Q3 P scalar29MontMulCode := by rw [← hQ3]; exact hcq2.store32 (frm_sep' sFC (by decide))
  obtain ⟨q4, dq4, uq4⟩ := uq3.swG hcq3 smm_at_d9e (off' := 0xDA2) (by decide)
    (by rw [a1_t, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x148) (v := reg n1 (5 : Fin 32))
    (by rw [a1_t, BitVec.add_assoc]; rfl) (tk _ (by decide))
  obtain ⟨Q4, hQ4⟩ : ∃ M', memStore32 Q3 (F + 0x148) (reg n1 (5 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hQ4] at uq4
  have hcq4 : CodeIn Q4 P scalar29MontMulCode := by rw [← hQ4]; exact hcq3.store32 (frm_sep' sFC (by decide))
  obtain ⟨q5, dq5, uq5⟩ := uq4.swG hcq4 smm_at_da2 (off' := 0xDA6) (by decide)
    (by rw [a1_t, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x14C) (v := reg n1 a6)
    (by rw [a1_t, BitVec.add_assoc]; rfl) (tk _ (by decide))
  obtain ⟨Q5, hQ5⟩ : ∃ M', memStore32 Q4 (F + 0x14C) (reg n1 a6) = M' := ⟨_, rfl⟩
  rw [hQ5] at uq5
  have hcq5 : CodeIn Q5 P scalar29MontMulCode := by rw [← hQ5]; exact hcq4.store32 (frm_sep' sFC (by decide))
  obtain ⟨q6, dq6, uq6⟩ := uq5.swG hcq5 smm_at_da6 (off' := 0xDA8) (by decide)
    (by rw [a1_t, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x150) (v := reg n1 (9 : Fin 32))
    (by rw [a1_t, BitVec.add_assoc]; rfl) (tk _ (by decide))
  obtain ⟨Q6, hQ6⟩ : ∃ M', memStore32 Q5 (F + 0x150) (reg n1 (9 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hQ6] at uq6
  have hcq6 : CodeIn Q6 P scalar29MontMulCode := by rw [← hQ6]; exact hcq5.store32 (frm_sep' sFC (by decide))
  obtain ⟨q7, dq7, uq7⟩ := uq6.swG hcq6 smm_at_da8 (off' := 0xDAC) (by decide)
    (by rw [a1_t, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x154) (v := reg n1 (17 : Fin 32))
    (by rw [a1_t, BitVec.add_assoc]; rfl) (tk _ (by decide))
  obtain ⟨Q7, hQ7⟩ : ∃ M', memStore32 Q6 (F + 0x154) (reg n1 (17 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hQ7] at uq7
  have hcq7 : CodeIn Q7 P scalar29MontMulCode := by rw [← hQ7]; exact hcq6.store32 (frm_sep' sFC (by decide))
  obtain ⟨q8, dq8, uq8⟩ := uq7.swG hcq7 smm_at_dac (off' := 0xDAE) (by decide)
    (by rw [a1_t, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (a := F + 0x158) (v := reg n1 a0)
    (by rw [a1_t, BitVec.add_assoc]; rfl) (tk _ (by decide))
  obtain ⟨Q8, hQ8⟩ : ∃ M', memStore32 Q7 (F + 0x158) (reg n1 a0) = M' := ⟨_, rfl⟩
  rw [hQ8] at uq8
  have hcq8 : CodeIn Q8 P scalar29MontMulCode := by rw [← hQ8]; exact hcq7.store32 (frm_sep' sFC (by decide))
  have Qm : ∀ x, Sep F 0x190 x 1 → Q8 x = m.mem x := fun x hx => by
    rw [← hQ8, memStore32_get_sep (frm_sep' hx (by decide)), ← hQ7, memStore32_get_sep (frm_sep' hx (by decide)), ← hQ6, memStore32_get_sep (frm_sep' hx (by decide)), ← hQ5, memStore32_get_sep (frm_sep' hx (by decide)), ← hQ4, memStore32_get_sep (frm_sep' hx (by decide)), ← hQ3, memStore32_get_sep (frm_sep' hx (by decide)), ← hQ2, memStore32_get_sep (frm_sep' hx (by decide)), ← hQ1, memStore32_get_sep (frm_sep' hx (by decide)), ← hQ0, memStore32_get_sep (frm_sep' hx (by decide)), M1m x hx]
  have qr : ∀ q, reg q8 q = reg t1 q := uq8.regs
  obtain ⟨t2, e2, v2⟩ := uq8.self.aluImm hcq8 smm_at_dae (off' := 0xDB0) (by decide)
  have k2' := v2.oldReg uq8.self.zero
  obtain ⟨t3, e3, v3⟩ := v2.self.lwE hcq8 smm_at_db0 (off' := 0xDB2) (by decide)
    (by rw [k2' _ (by decide), qr, tk _ (by decide), sp_1]; exact fr_al' hFa (by decide)) (v := out)
    (by rw [k2' _ (by decide), qr, tk _ (by decide), sp_1, ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_lit (by decide), ← hQ4, ls_lit (by decide), ← hQ3, ls_lit (by decide), ← hQ2, ls_lit (by decide), ← hQ1, ls_lit (by decide), ← hQ0, ls_lit (by decide)]; exact kout)
  have k3' := v3.oldReg v2.self.zero
  have a0_3 : reg t3 a0 = out := v3.newReg (by decide)
  have a1_3 : reg t3 a1 = F + 0x138 := by
    rw [k3' _ (by decide), v2.newReg (by decide)]; show reg q8 sp + 0x138 = _; rw [qr, tk _ (by decide), sp_1]
  have sp_3 : reg t3 sp = F := by rw [k3' _ (by decide), k2' _ (by decide), qr, tk _ (by decide), sp_1]
  -- `sub(out, r)`
  obtain ⟨t4, e4, pc4, mem4, regs4⟩ := v3.self.callRa hcq8 smm_at_db2 smm_at_db6 (cb := P + 0xFFFFFCF0)
    (smm_sub_at P) (even_at P env.hP 0xFFFFFCF0 (by decide))
  have r4 := PEnv.reg1 regs4 v3.self.zero
  have cQ : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep G 0x1F0 b code.length → CodeIn Q8 b code :=
    fun hc hs i hi => by rw [Qm _ ((inF (n := 0) hs).subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have g60 : ∀ {b : Word} {k : Nat}, Sep G 0x1F0 b k → Sep G 0x60 b k := fun h => by
    have := h.sub (c := 0) (l := 0x60) (by decide); rwa [add_ofNat_zero] at this
  have hF138 : F + 0x138 = G + BitVec.ofNat 32 0x198 := by rw [← hF, BitVec.add_assoc]; rfl
  have SE : SSEnv Q8 (P + 0xFFFFFCF0) G out (F + 0x138) := {
    hP := even_at P env.hP 0xFFFFFCF0 (by decide)
    code := cQ env.scode env.sGS
    idx := cQ env.idx env.sGI
    idxm := cQ env.idxm env.sGIM
    mset := cQ env.mset env.sGM
    stub := cQ env.stub env.sGSt
    body := cQ env.body env.sGB
    bb := cQ env.bb env.sGBB
    ldata := cQ env.ldata env.sGL
    hG := env.hG
    hGt := by omega
    hout := env.hout
    hot := env.hot
    hap := fr_al' hFa (by decide)
    sGC := g60 env.sGS
    sGI := g60 env.sGI
    sGIM := g60 env.sGIM
    sGM := g60 env.sGM
    sGS := g60 env.sGSt
    sGB := g60 env.sGB
    sGBB := g60 env.sGBB
    sGL := g60 env.sGL
    sAG := by
      rw [hF138]
      have := sep_offsets G (c := 0x198) (n := 36) (d := 0) (k := 0x60) (.inr (by decide)) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
    sOG := (g60 env.sOG.symm).symm
    sOC := env.sOS
    sOB := env.sOB }
  obtain ⟨t5, c5, pc5, sp5, k5, out5, fr5⟩ := scalar29Sub_correct t4 (by rw [mem4]; exact SE) pc4
    (by rw [r4 _ (by decide), a0_3]) (by rw [r4 _ (by decide), a1_3]) (by rw [regs4]; simp [upd])
    (even_clear _ (even_at P env.hP (0xDB2 + 8) (by decide))) (by rw [r4 _ (by decide), sp_3, ← hF])
  rw [mem4] at out5 fr5
  have hc5 : CodeIn t5.mem P scalar29MontMulCode := fun i hi => by
    have hs := env.sGC.subR (c := i) (l := 1) (by omega)
    rw [fr5 _ (g60 hs).symm.symm (env.sOC.subR (c := i) (l := 1) (by omega)),
      Qm _ ((inF (n := 0) env.sGC).subR (c := i) (l := 1) (by omega))]
    exact env.code i hi
  have t5Q : ∀ c, 0x60 + c + 4 ≤ 0x1F0 →
      memLoad32 t5.mem (F + BitVec.ofNat 32 c) = memLoad32 Q8 (F + BitVec.ofNat 32 c) := fun c hc =>
    memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc, fG]
      exact fr5 _ (by
          have := sep_offsets G (c := 0) (n := 0x60) (d := 0x60 + (c + j)) (k := 1) (.inl (by omega)) (by decide)
            (by omega)
          rwa [add_ofNat_zero] at this)
        (env.sOG.subR (c := 0x60 + (c + j)) (l := 1) (by omega))
  have svra : memLoad32 t5.mem (F + 0x18C) = reg m ra := by
    rw [show F + 0x18C = F + BitVec.ofNat 32 0x18C from rfl, t5Q 0x18C (by decide),
      show F + BitVec.ofNat 32 0x18C = F + 0x18C from rfl, ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_lit (by decide), ← hQ4, ls_lit (by decide), ← hQ3, ls_lit (by decide), ← hQ2, ls_lit (by decide), ← hQ1, ls_lit (by decide), ← hQ0, ls_lit (by decide), ks12, hsl ra 0x18C (by decide)]
  have sv8 : memLoad32 t5.mem (F + 0x188) = reg m (8 : Fin 32) := by
    rw [show F + 0x188 = F + BitVec.ofNat 32 0x188 from rfl, t5Q 0x188 (by decide),
      show F + BitVec.ofNat 32 0x188 = F + 0x188 from rfl, ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_lit (by decide), ← hQ4, ls_lit (by decide), ← hQ3, ls_lit (by decide), ← hQ2, ls_lit (by decide), ← hQ1, ls_lit (by decide), ← hQ0, ls_lit (by decide), ks11, hsl (8 : Fin 32) 0x188 (by decide)]
  have sv9 : memLoad32 t5.mem (F + 0x184) = reg m (9 : Fin 32) := by
    rw [show F + 0x184 = F + BitVec.ofNat 32 0x184 from rfl, t5Q 0x184 (by decide),
      show F + BitVec.ofNat 32 0x184 = F + 0x184 from rfl, ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_lit (by decide), ← hQ4, ls_lit (by decide), ← hQ3, ls_lit (by decide), ← hQ2, ls_lit (by decide), ← hQ1, ls_lit (by decide), ← hQ0, ls_lit (by decide), ks10, hsl (9 : Fin 32) 0x184 (by decide)]
  have sv18 : memLoad32 t5.mem (F + 0x180) = reg m (18 : Fin 32) := by
    rw [show F + 0x180 = F + BitVec.ofNat 32 0x180 from rfl, t5Q 0x180 (by decide),
      show F + BitVec.ofNat 32 0x180 = F + 0x180 from rfl, ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_lit (by decide), ← hQ4, ls_lit (by decide), ← hQ3, ls_lit (by decide), ← hQ2, ls_lit (by decide), ← hQ1, ls_lit (by decide), ← hQ0, ls_lit (by decide), ks9, hsl (18 : Fin 32) 0x180 (by decide)]
  have sv19 : memLoad32 t5.mem (F + 0x17C) = reg m (19 : Fin 32) := by
    rw [show F + 0x17C = F + BitVec.ofNat 32 0x17C from rfl, t5Q 0x17C (by decide),
      show F + BitVec.ofNat 32 0x17C = F + 0x17C from rfl, ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_lit (by decide), ← hQ4, ls_lit (by decide), ← hQ3, ls_lit (by decide), ← hQ2, ls_lit (by decide), ← hQ1, ls_lit (by decide), ← hQ0, ls_lit (by decide), ks8, hsl (19 : Fin 32) 0x17C (by decide)]
  have sv20 : memLoad32 t5.mem (F + 0x178) = reg m (20 : Fin 32) := by
    rw [show F + 0x178 = F + BitVec.ofNat 32 0x178 from rfl, t5Q 0x178 (by decide),
      show F + BitVec.ofNat 32 0x178 = F + 0x178 from rfl, ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_lit (by decide), ← hQ4, ls_lit (by decide), ← hQ3, ls_lit (by decide), ← hQ2, ls_lit (by decide), ← hQ1, ls_lit (by decide), ← hQ0, ls_lit (by decide), ks7, hsl (20 : Fin 32) 0x178 (by decide)]
  have sv21 : memLoad32 t5.mem (F + 0x174) = reg m (21 : Fin 32) := by
    rw [show F + 0x174 = F + BitVec.ofNat 32 0x174 from rfl, t5Q 0x174 (by decide),
      show F + BitVec.ofNat 32 0x174 = F + 0x174 from rfl, ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_lit (by decide), ← hQ4, ls_lit (by decide), ← hQ3, ls_lit (by decide), ← hQ2, ls_lit (by decide), ← hQ1, ls_lit (by decide), ← hQ0, ls_lit (by decide), ks6, hsl (21 : Fin 32) 0x174 (by decide)]
  have sv22 : memLoad32 t5.mem (F + 0x170) = reg m (22 : Fin 32) := by
    rw [show F + 0x170 = F + BitVec.ofNat 32 0x170 from rfl, t5Q 0x170 (by decide),
      show F + BitVec.ofNat 32 0x170 = F + 0x170 from rfl, ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_lit (by decide), ← hQ4, ls_lit (by decide), ← hQ3, ls_lit (by decide), ← hQ2, ls_lit (by decide), ← hQ1, ls_lit (by decide), ← hQ0, ls_lit (by decide), ks5, hsl (22 : Fin 32) 0x170 (by decide)]
  have sv23 : memLoad32 t5.mem (F + 0x16C) = reg m (23 : Fin 32) := by
    rw [show F + 0x16C = F + BitVec.ofNat 32 0x16C from rfl, t5Q 0x16C (by decide),
      show F + BitVec.ofNat 32 0x16C = F + 0x16C from rfl, ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_lit (by decide), ← hQ4, ls_lit (by decide), ← hQ3, ls_lit (by decide), ← hQ2, ls_lit (by decide), ← hQ1, ls_lit (by decide), ← hQ0, ls_lit (by decide), ks4, hsl (23 : Fin 32) 0x16C (by decide)]
  have sv24 : memLoad32 t5.mem (F + 0x168) = reg m (24 : Fin 32) := by
    rw [show F + 0x168 = F + BitVec.ofNat 32 0x168 from rfl, t5Q 0x168 (by decide),
      show F + BitVec.ofNat 32 0x168 = F + 0x168 from rfl, ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_lit (by decide), ← hQ4, ls_lit (by decide), ← hQ3, ls_lit (by decide), ← hQ2, ls_lit (by decide), ← hQ1, ls_lit (by decide), ← hQ0, ls_lit (by decide), ks3, hsl (24 : Fin 32) 0x168 (by decide)]
  have sv25 : memLoad32 t5.mem (F + 0x164) = reg m (25 : Fin 32) := by
    rw [show F + 0x164 = F + BitVec.ofNat 32 0x164 from rfl, t5Q 0x164 (by decide),
      show F + BitVec.ofNat 32 0x164 = F + 0x164 from rfl, ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_lit (by decide), ← hQ4, ls_lit (by decide), ← hQ3, ls_lit (by decide), ← hQ2, ls_lit (by decide), ← hQ1, ls_lit (by decide), ← hQ0, ls_lit (by decide), ks2, hsl (25 : Fin 32) 0x164 (by decide)]
  have sv26 : memLoad32 t5.mem (F + 0x160) = reg m (26 : Fin 32) := by
    rw [show F + 0x160 = F + BitVec.ofNat 32 0x160 from rfl, t5Q 0x160 (by decide),
      show F + BitVec.ofNat 32 0x160 = F + 0x160 from rfl, ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_lit (by decide), ← hQ4, ls_lit (by decide), ← hQ3, ls_lit (by decide), ← hQ2, ls_lit (by decide), ← hQ1, ls_lit (by decide), ← hQ0, ls_lit (by decide), ks1, hsl (26 : Fin 32) 0x160 (by decide)]
  have sv27 : memLoad32 t5.mem (F + 0x15C) = reg m (27 : Fin 32) := by
    rw [show F + 0x15C = F + BitVec.ofNat 32 0x15C from rfl, t5Q 0x15C (by decide),
      show F + BitVec.ofNat 32 0x15C = F + 0x15C from rfl, ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_lit (by decide), ← hQ4, ls_lit (by decide), ← hQ3, ls_lit (by decide), ← hQ2, ls_lit (by decide), ← hQ1, ls_lit (by decide), ← hQ0, ls_lit (by decide), ks0, hsl (27 : Fin 32) 0x15C (by decide)]
  -- the epilogue
  have w5 : St t5.mem P t5 0xDBA (reg t5) := ⟨pc5, rfl, fun _ => rfl⟩
  have sp5' : reg t5 sp = F := by rw [sp5, hF]
  obtain ⟨f0, g0, y0⟩ := w5.aluImm hc5 smm_at_dba (off' := 0xDBC) (by decide)
  have A0 : reg f0 a0 = F + 0x180 := by rw [y0.newReg (by decide)]; show reg t5 sp + 0x180 = _; rw [sp5']
  have j0 := y0.oldReg w5.zero
  obtain ⟨f1, g1, y1⟩ := y0.self.lwE hc5 smm_at_dbc (off' := 0xDC0) (by decide)
    (by rw [A0, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m ra)
    (by rw [A0, BitVec.add_assoc]; exact svra)
  have j1 := y1.oldReg y0.self.zero
  have A1 : reg f1 a0 = F + 0x180 := by rw [j1 _ (by decide), A0]
  obtain ⟨f2, g2, y2⟩ := y1.self.lwE hc5 smm_at_dc0 (off' := 0xDC2) (by decide)
    (by rw [A1, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (8 : Fin 32))
    (by rw [A1, BitVec.add_assoc]; exact sv8)
  have j2 := y2.oldReg y1.self.zero
  have A2 : reg f2 a0 = F + 0x180 := by rw [j2 _ (by decide), A1]
  obtain ⟨f3, g3, y3⟩ := y2.self.lwE hc5 smm_at_dc2 (off' := 0xDC4) (by decide)
    (by rw [A2, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (9 : Fin 32))
    (by rw [A2, BitVec.add_assoc]; exact sv9)
  have j3 := y3.oldReg y2.self.zero
  have A3 : reg f3 a0 = F + 0x180 := by rw [j3 _ (by decide), A2]
  obtain ⟨f4, g4, y4⟩ := y3.self.lwE hc5 smm_at_dc4 (off' := 0xDC8) (by decide)
    (by rw [A3, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (18 : Fin 32))
    (by rw [A3, BitVec.add_assoc]; exact sv18)
  have j4 := y4.oldReg y3.self.zero
  have A4 : reg f4 a0 = F + 0x180 := by rw [j4 _ (by decide), A3]
  have sp4 : reg f4 sp = F := by rw [j4 _ (by decide), j3 _ (by decide), j2 _ (by decide), j1 _ (by decide), j0 _ (by decide), sp5']
  obtain ⟨f5, g5, y5⟩ := y4.self.aluImm hc5 smm_at_dc8 (off' := 0xDCA) (by decide)
  have j5 := y5.oldReg y4.self.zero
  have A5 : reg f5 a0 = F + 0x100 := by rw [y5.newReg (by decide)]; show reg f4 sp + 0x100 = _; rw [sp4]
  obtain ⟨f6, g6, y6⟩ := y5.self.lwE hc5 smm_at_dca (off' := 0xDCE) (by decide)
    (by rw [A5, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (19 : Fin 32))
    (by rw [A5, BitVec.add_assoc]; exact sv19)
  have j6 := y6.oldReg y5.self.zero
  have A6 : reg f6 a0 = F + 0x100 := by rw [j6 _ (by decide), A5]
  obtain ⟨f7, g7, y7⟩ := y6.self.lwE hc5 smm_at_dce (off' := 0xDD2) (by decide)
    (by rw [A6, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (20 : Fin 32))
    (by rw [A6, BitVec.add_assoc]; exact sv20)
  have j7 := y7.oldReg y6.self.zero
  have A7 : reg f7 a0 = F + 0x100 := by rw [j7 _ (by decide), A6]
  obtain ⟨f8, g8, y8⟩ := y7.self.lwE hc5 smm_at_dd2 (off' := 0xDD6) (by decide)
    (by rw [A7, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (21 : Fin 32))
    (by rw [A7, BitVec.add_assoc]; exact sv21)
  have j8 := y8.oldReg y7.self.zero
  have A8 : reg f8 a0 = F + 0x100 := by rw [j8 _ (by decide), A7]
  obtain ⟨f9, g9, y9⟩ := y8.self.lwE hc5 smm_at_dd6 (off' := 0xDDA) (by decide)
    (by rw [A8, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (22 : Fin 32))
    (by rw [A8, BitVec.add_assoc]; exact sv22)
  have j9 := y9.oldReg y8.self.zero
  have A9 : reg f9 a0 = F + 0x100 := by rw [j9 _ (by decide), A8]
  obtain ⟨f10, g10, y10⟩ := y9.self.lwE hc5 smm_at_dda (off' := 0xDDE) (by decide)
    (by rw [A9, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (23 : Fin 32))
    (by rw [A9, BitVec.add_assoc]; exact sv23)
  have j10 := y10.oldReg y9.self.zero
  have A10 : reg f10 a0 = F + 0x100 := by rw [j10 _ (by decide), A9]
  obtain ⟨f11, g11, y11⟩ := y10.self.lwE hc5 smm_at_dde (off' := 0xDE2) (by decide)
    (by rw [A10, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (24 : Fin 32))
    (by rw [A10, BitVec.add_assoc]; exact sv24)
  have j11 := y11.oldReg y10.self.zero
  have A11 : reg f11 a0 = F + 0x100 := by rw [j11 _ (by decide), A10]
  obtain ⟨f12, g12, y12⟩ := y11.self.lwE hc5 smm_at_de2 (off' := 0xDE6) (by decide)
    (by rw [A11, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (25 : Fin 32))
    (by rw [A11, BitVec.add_assoc]; exact sv25)
  have j12 := y12.oldReg y11.self.zero
  have A12 : reg f12 a0 = F + 0x100 := by rw [j12 _ (by decide), A11]
  obtain ⟨f13, g13, y13⟩ := y12.self.lwE hc5 smm_at_de6 (off' := 0xDEA) (by decide)
    (by rw [A12, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (26 : Fin 32))
    (by rw [A12, BitVec.add_assoc]; exact sv26)
  have j13 := y13.oldReg y12.self.zero
  have A13 : reg f13 a0 = F + 0x100 := by rw [j13 _ (by decide), A12]
  obtain ⟨f14, g14, y14⟩ := y13.self.lwE hc5 smm_at_dea (off' := 0xDEE) (by decide)
    (by rw [A13, BitVec.add_assoc]; exact fr_al' hFa (by decide)) (v := reg m (27 : Fin 32))
    (by rw [A13, BitVec.add_assoc]; exact sv27)
  have j14 := y14.oldReg y13.self.zero
  have A14 : reg f14 a0 = F + 0x100 := by rw [j14 _ (by decide), A13]
  have spL : reg f14 sp = F := by rw [j14 _ (by decide), j13 _ (by decide), j12 _ (by decide), j11 _ (by decide), j10 _ (by decide), j9 _ (by decide), j8 _ (by decide), j7 _ (by decide), j6 _ (by decide), j5 _ (by decide), j4 _ (by decide), j3 _ (by decide), j2 _ (by decide), j1 _ (by decide), j0 _ (by decide), sp5']
  obtain ⟨f15, g15, y15⟩ := y14.self.aluImm hc5 smm_at_dee (off' := 0xDF0) (by decide)
  obtain ⟨fz, gz, pcz, memz, regsz⟩ := y15.self.jalr hc5 smm_at_df0
  have jz := y15.oldReg y14.self.zero
  have finra : reg fz ra = reg m ra := by
    rw [regsz, jz _ (by decide), j14 _ (by decide), j13 _ (by decide), j12 _ (by decide), j11 _ (by decide), j10 _ (by decide), j9 _ (by decide), j8 _ (by decide), j7 _ (by decide), j6 _ (by decide), j5 _ (by decide), j4 _ (by decide), j3 _ (by decide), j2 _ (by decide), y1.newReg (by decide)]
  have fin8 : reg fz (8 : Fin 32) = reg m (8 : Fin 32) := by
    rw [regsz, jz _ (by decide), j14 _ (by decide), j13 _ (by decide), j12 _ (by decide), j11 _ (by decide), j10 _ (by decide), j9 _ (by decide), j8 _ (by decide), j7 _ (by decide), j6 _ (by decide), j5 _ (by decide), j4 _ (by decide), j3 _ (by decide), y2.newReg (by decide)]
  have fin9 : reg fz (9 : Fin 32) = reg m (9 : Fin 32) := by
    rw [regsz, jz _ (by decide), j14 _ (by decide), j13 _ (by decide), j12 _ (by decide), j11 _ (by decide), j10 _ (by decide), j9 _ (by decide), j8 _ (by decide), j7 _ (by decide), j6 _ (by decide), j5 _ (by decide), j4 _ (by decide), y3.newReg (by decide)]
  have fin18 : reg fz (18 : Fin 32) = reg m (18 : Fin 32) := by
    rw [regsz, jz _ (by decide), j14 _ (by decide), j13 _ (by decide), j12 _ (by decide), j11 _ (by decide), j10 _ (by decide), j9 _ (by decide), j8 _ (by decide), j7 _ (by decide), j6 _ (by decide), j5 _ (by decide), y4.newReg (by decide)]
  have fin19 : reg fz (19 : Fin 32) = reg m (19 : Fin 32) := by
    rw [regsz, jz _ (by decide), j14 _ (by decide), j13 _ (by decide), j12 _ (by decide), j11 _ (by decide), j10 _ (by decide), j9 _ (by decide), j8 _ (by decide), j7 _ (by decide), y6.newReg (by decide)]
  have fin20 : reg fz (20 : Fin 32) = reg m (20 : Fin 32) := by
    rw [regsz, jz _ (by decide), j14 _ (by decide), j13 _ (by decide), j12 _ (by decide), j11 _ (by decide), j10 _ (by decide), j9 _ (by decide), j8 _ (by decide), y7.newReg (by decide)]
  have fin21 : reg fz (21 : Fin 32) = reg m (21 : Fin 32) := by
    rw [regsz, jz _ (by decide), j14 _ (by decide), j13 _ (by decide), j12 _ (by decide), j11 _ (by decide), j10 _ (by decide), j9 _ (by decide), y8.newReg (by decide)]
  have fin22 : reg fz (22 : Fin 32) = reg m (22 : Fin 32) := by
    rw [regsz, jz _ (by decide), j14 _ (by decide), j13 _ (by decide), j12 _ (by decide), j11 _ (by decide), j10 _ (by decide), y9.newReg (by decide)]
  have fin23 : reg fz (23 : Fin 32) = reg m (23 : Fin 32) := by
    rw [regsz, jz _ (by decide), j14 _ (by decide), j13 _ (by decide), j12 _ (by decide), j11 _ (by decide), y10.newReg (by decide)]
  have fin24 : reg fz (24 : Fin 32) = reg m (24 : Fin 32) := by
    rw [regsz, jz _ (by decide), j14 _ (by decide), j13 _ (by decide), j12 _ (by decide), y11.newReg (by decide)]
  have fin25 : reg fz (25 : Fin 32) = reg m (25 : Fin 32) := by
    rw [regsz, jz _ (by decide), j14 _ (by decide), j13 _ (by decide), y12.newReg (by decide)]
  have fin26 : reg fz (26 : Fin 32) = reg m (26 : Fin 32) := by
    rw [regsz, jz _ (by decide), j14 _ (by decide), y13.newReg (by decide)]
  have fin27 : reg fz (27 : Fin 32) = reg m (27 : Fin 32) := by
    rw [regsz, jz _ (by decide), y14.newReg (by decide)]
  have steps : Steps m fz := .cons d1 (.cons d2 (.cons dp0 (.cons dp1 (.cons dp2 (.cons dp3 (.cons dp4 (.cons dp5 (.cons dp6 (.cons dp7 (.cons dp8 (.cons dp9 (.cons dp10 (.cons dp11 (.cons dp12 (c1.trans (.cons e1 (.cons dq0 (.cons dq1 (.cons dq2 (.cons dq3 (.cons dq4 (.cons dq5 (.cons dq6 (.cons dq7 (.cons dq8 (.cons e2 (.cons e3 (e4.trans (c5.trans (.cons g0 (.cons g1 (.cons g2 (.cons g3 (.cons g4 (.cons g5 (.cons g6 (.cons g7 (.cons g8 (.cons g9 (.cons g10 (.cons g11 (.cons g12 (.cons g13 (.cons g14 (.cons g15 (.single gz))))))))))))))))))))))))))))))))))))))))))))))
  have rz : ∀ q, reg fz q = reg f15 q := regsz
  have spz : reg fz sp = G + 0x1F0 := by
    rw [rz, y15.newReg (by decide)]; show reg f14 sp + 0x190 = _
    rw [spL, ← hF, BitVec.add_assoc]; rfl
  have pass : ∀ q : Fin 32, q.val ∈ [3, 4] → reg fz q = reg m q := fun q hq => by
    have nq : ∀ r : Fin 32, r.val ∉ [3, 4] → q ≠ r := fun r hr e => hr (e ▸ hq)
    have hk : feMKeep q = true := by revert hq; revert q; decide
    rw [rz, jz q (nq _ (by decide)), j14 q (nq _ (by decide)), j13 q (nq _ (by decide)), j12 q (nq _ (by decide)), j11 q (nq _ (by decide)), j10 q (nq _ (by decide)), j9 q (nq _ (by decide)), j8 q (nq _ (by decide)), j7 q (nq _ (by decide)), j6 q (nq _ (by decide)), j5 q (nq _ (by decide)), j4 q (nq _ (by decide)), j3 q (nq _ (by decide)), j2 q (nq _ (by decide)), j1 q (nq _ (by decide)), j0 q (nq _ (by decide)),
      k5 q hk, r4 q (nq _ (by decide)), k3' q (nq _ (by decide)), k2' q (nq _ (by decide)), qr,
      tk q (nq _ (by decide))]
    rcases (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq; omega : q.val = 3 ∨ q.val = 4) with h | h
    · have : q = 3 := Fin.ext h
      subst this; rw [g3_1, pr, rk _ (by decide) (by decide)]
    · have : q = 4 := Fin.ext h
      subst this; rw [g4_1, pr, rk _ (by decide) (by decide)]
  refine ⟨fz, steps, ?_, spz, fun q hq => ?_, fun j hj => ?_, fun x hx ho => ?_⟩
  · rw [pcz, add_lit_zero, ← rz, finra, hra, hret]
  · have hmem : q = 0 ∨ q = sp ∨ q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨
        q = (19 : Fin 32) ∨ q = (20 : Fin 32) ∨ q = (21 : Fin 32) ∨ q = (22 : Fin 32) ∨ q = (23 : Fin 32) ∨
        q = (24 : Fin 32) ∨ q = (25 : Fin 32) ∨ q = (26 : Fin 32) ∨ q = (27 : Fin 32) ∨ q.val ∈ [3, 4] := by
      revert hq; revert q; decide
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
    · rfl
    · rw [spz, hsp]
    · exact finra
    · exact fin8
    · exact fin9
    · exact fin18
    · exact fin19
    · exact fin20
    · exact fin21
    · exact fin22
    · exact fin23
    · exact fin24
    · exact fin25
    · exact fin26
    · exact fin27
    · exact pass q h
  · rw [memz, out5 j hj]
    congr 1
    refine s29Out_congr (fun i hi => ?_) hj
    show (memLoad32 Q8 (F + 0x138 + BitVec.ofNat 32 (4 * i))).toNat = _
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show F + 0x138 + BitVec.ofNat 32 (4 * 0) = F + 0x138 by rw [BitVec.add_assoc]; rfl,
        ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_lit (by decide), ← hQ4, ls_lit (by decide), ← hQ3, ls_lit (by decide), ← hQ2, ls_lit (by decide), ← hQ1, ls_lit (by decide), ← hQ0, ls_same rfl, o0]; rfl
    · rw [show F + 0x138 + BitVec.ofNat 32 (4 * 1) = F + 0x13C by rw [BitVec.add_assoc]; rfl,
        ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_lit (by decide), ← hQ4, ls_lit (by decide), ← hQ3, ls_lit (by decide), ← hQ2, ls_lit (by decide), ← hQ1, ls_same rfl, o1]; rfl
    · rw [show F + 0x138 + BitVec.ofNat 32 (4 * 2) = F + 0x140 by rw [BitVec.add_assoc]; rfl,
        ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_lit (by decide), ← hQ4, ls_lit (by decide), ← hQ3, ls_lit (by decide), ← hQ2, ls_same rfl, o2]; rfl
    · rw [show F + 0x138 + BitVec.ofNat 32 (4 * 3) = F + 0x144 by rw [BitVec.add_assoc]; rfl,
        ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_lit (by decide), ← hQ4, ls_lit (by decide), ← hQ3, ls_same rfl, o3]; rfl
    · rw [show F + 0x138 + BitVec.ofNat 32 (4 * 4) = F + 0x148 by rw [BitVec.add_assoc]; rfl,
        ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_lit (by decide), ← hQ4, ls_same rfl, o4]; rfl
    · rw [show F + 0x138 + BitVec.ofNat 32 (4 * 5) = F + 0x14C by rw [BitVec.add_assoc]; rfl,
        ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_lit (by decide), ← hQ5, ls_same rfl, o5]; rfl
    · rw [show F + 0x138 + BitVec.ofNat 32 (4 * 6) = F + 0x150 by rw [BitVec.add_assoc]; rfl,
        ← hQ8, ls_lit (by decide), ← hQ7, ls_lit (by decide), ← hQ6, ls_same rfl, o6]; rfl
    · rw [show F + 0x138 + BitVec.ofNat 32 (4 * 7) = F + 0x154 by rw [BitVec.add_assoc]; rfl,
        ← hQ8, ls_lit (by decide), ← hQ7, ls_same rfl, o7]; rfl
    · rw [show F + 0x138 + BitVec.ofNat 32 (4 * 8) = F + 0x158 by rw [BitVec.add_assoc]; rfl,
        ← hQ8, ls_same rfl, o8]; rfl
  · rw [memz, fr5 x (g60 hx) ho, Qm x (inF (n := 1) hx)]

end C3.RV32
