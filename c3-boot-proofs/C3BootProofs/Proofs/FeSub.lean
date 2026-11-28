import C3BootProofs.Proofs.FeAdd

/-!
# `<&FieldElement2625 as Sub>::sub`

`curve25519_dalek`'s field subtraction, as compiled: it adds `16 p` to the
left operand limb by limb and subtracts the right operand's limbs (`u32`
arithmetic, which wraps in a release build), widens each to a `u64`, and
calls `reduce` on them through its theorem, then copies the result out.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem fsb_at_0 : fetchRel feSubCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF70, 2) := by decide
theorem fsb_at_2 : fetchRel feSubCode 0x2 = some (.store .sw sp ra 0x8C, 2) := by decide
theorem fsb_at_4 : fetchRel feSubCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x88, 2) := by decide
theorem fsb_at_6 : fetchRel feSubCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x84, 2) := by decide
theorem fsb_at_8 : fetchRel feSubCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x80, 2) := by decide
theorem fsb_at_a : fetchRel feSubCode 0xA = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem fsb_at_c : fetchRel feSubCode 0xC = some (.load .lw a0 a1 0x0, 2) := by decide
theorem fsb_at_e : fetchRel feSubCode 0xE = some (.load .lw (30 : Fin 32) a1 0x4, 4) := by decide
theorem fsb_at_12 : fetchRel feSubCode 0x12 = some (.load .lw (7 : Fin 32) a1 0x8, 4) := by decide
theorem fsb_at_16 : fetchRel feSubCode 0x16 = some (.load .lw (28 : Fin 32) a1 0xC, 4) := by decide
theorem fsb_at_1a : fetchRel feSubCode 0x1A = some (.load .lw a6 a1 0x10, 4) := by decide
theorem fsb_at_1e : fetchRel feSubCode 0x1E = some (.load .lw (17 : Fin 32) a1 0x14, 4) := by decide
theorem fsb_at_22 : fetchRel feSubCode 0x22 = some (.load .lw (5 : Fin 32) a1 0x18, 4) := by decide
theorem fsb_at_26 : fetchRel feSubCode 0x26 = some (.load .lw (6 : Fin 32) a1 0x1C, 4) := by decide
theorem fsb_at_2a : fetchRel feSubCode 0x2A = some (.lui a4 0x40000000, 4) := by decide
theorem fsb_at_2e : fetchRel feSubCode 0x2E = some (.aluImm .add a4 a4 0xFFFFFFF0, 2) := by decide
theorem fsb_at_30 : fetchRel feSubCode 0x30 = some (.load .lw (31 : Fin 32) a2 0x0, 4) := by decide
theorem fsb_at_34 : fetchRel feSubCode 0x34 = some (.lui (29 : Fin 32) 0x20000000, 4) := by decide
theorem fsb_at_38 : fetchRel feSubCode 0x38 = some (.load .lw a3 a2 0x4, 2) := by decide
theorem fsb_at_3a : fetchRel feSubCode 0x3A = some (.alu .add a0 a0 a4, 2) := by decide
theorem fsb_at_3c : fetchRel feSubCode 0x3C = some (.aluImm .add (29 : Fin 32) (29 : Fin 32) 0xFFFFFFF0, 2) := by decide
theorem fsb_at_3e : fetchRel feSubCode 0x3E = some (.load .lw a5 a2 0x8, 2) := by decide
theorem fsb_at_40 : fetchRel feSubCode 0x40 = some (.load .lw (9 : Fin 32) a2 0xC, 2) := by decide
theorem fsb_at_42 : fetchRel feSubCode 0x42 = some (.alu .sub (18 : Fin 32) a0 (31 : Fin 32), 4) := by decide
theorem fsb_at_46 : fetchRel feSubCode 0x46 = some (.alu .add (30 : Fin 32) (30 : Fin 32) (29 : Fin 32), 2) := by decide
theorem fsb_at_48 : fetchRel feSubCode 0x48 = some (.alu .sub (30 : Fin 32) (30 : Fin 32) a3, 4) := by decide
theorem fsb_at_4c : fetchRel feSubCode 0x4C = some (.alu .add (7 : Fin 32) (7 : Fin 32) a4, 2) := by decide
theorem fsb_at_4e : fetchRel feSubCode 0x4E = some (.alu .add (28 : Fin 32) (28 : Fin 32) (29 : Fin 32), 2) := by decide
theorem fsb_at_50 : fetchRel feSubCode 0x50 = some (.load .lw a3 a2 0x10, 2) := by decide
theorem fsb_at_52 : fetchRel feSubCode 0x52 = some (.alu .sub (31 : Fin 32) (7 : Fin 32) a5, 4) := by decide
theorem fsb_at_56 : fetchRel feSubCode 0x56 = some (.alu .sub (7 : Fin 32) (28 : Fin 32) (9 : Fin 32), 4) := by decide
theorem fsb_at_5a : fetchRel feSubCode 0x5A = some (.alu .add a6 a6 a4, 2) := by decide
theorem fsb_at_5c : fetchRel feSubCode 0x5C = some (.load .lw (9 : Fin 32) a2 0x14, 2) := by decide
theorem fsb_at_5e : fetchRel feSubCode 0x5E = some (.load .lw a5 a2 0x18, 2) := by decide
theorem fsb_at_60 : fetchRel feSubCode 0x60 = some (.load .lw a0 a2 0x1C, 2) := by decide
theorem fsb_at_62 : fetchRel feSubCode 0x62 = some (.alu .sub a6 a6 a3, 4) := by decide
theorem fsb_at_66 : fetchRel feSubCode 0x66 = some (.load .lw a3 a1 0x20, 2) := by decide
theorem fsb_at_68 : fetchRel feSubCode 0x68 = some (.load .lw a1 a1 0x24, 2) := by decide
theorem fsb_at_6a : fetchRel feSubCode 0x6A = some (.alu .add (17 : Fin 32) (17 : Fin 32) (29 : Fin 32), 2) := by decide
theorem fsb_at_6c : fetchRel feSubCode 0x6C = some (.alu .sub (17 : Fin 32) (17 : Fin 32) (9 : Fin 32), 4) := by decide
theorem fsb_at_70 : fetchRel feSubCode 0x70 = some (.alu .add (5 : Fin 32) (5 : Fin 32) a4, 2) := by decide
theorem fsb_at_72 : fetchRel feSubCode 0x72 = some (.load .lw (9 : Fin 32) a2 0x20, 2) := by decide
theorem fsb_at_74 : fetchRel feSubCode 0x74 = some (.load .lw a2 a2 0x24, 2) := by decide
theorem fsb_at_76 : fetchRel feSubCode 0x76 = some (.alu .sub a5 (5 : Fin 32) a5, 4) := by decide
theorem fsb_at_7a : fetchRel feSubCode 0x7A = some (.alu .add (6 : Fin 32) (6 : Fin 32) (29 : Fin 32), 2) := by decide
theorem fsb_at_7c : fetchRel feSubCode 0x7C = some (.alu .sub (5 : Fin 32) (6 : Fin 32) a0, 4) := by decide
theorem fsb_at_80 : fetchRel feSubCode 0x80 = some (.aluImm .add a0 (18 : Fin 32) 0xFFFFFEE0, 4) := by decide
theorem fsb_at_84 : fetchRel feSubCode 0x84 = some (.alu .add a3 a3 a4, 2) := by decide
theorem fsb_at_86 : fetchRel feSubCode 0x86 = some (.alu .add a1 a1 (29 : Fin 32), 2) := by decide
theorem fsb_at_88 : fetchRel feSubCode 0x88 = some (.alu .sub a3 a3 (9 : Fin 32), 2) := by decide
theorem fsb_at_8a : fetchRel feSubCode 0x8A = some (.alu .sub a1 a1 a2, 2) := by decide
theorem fsb_at_8c : fetchRel feSubCode 0x8C = some (.store .sw sp a0 0x30, 2) := by decide
theorem fsb_at_8e : fetchRel feSubCode 0x8E = some (.store .sw sp x0 0x34, 2) := by decide
theorem fsb_at_90 : fetchRel feSubCode 0x90 = some (.store .sw sp (30 : Fin 32) 0x38, 2) := by decide
theorem fsb_at_92 : fetchRel feSubCode 0x92 = some (.store .sw sp x0 0x3C, 2) := by decide
theorem fsb_at_94 : fetchRel feSubCode 0x94 = some (.store .sw sp (31 : Fin 32) 0x40, 2) := by decide
theorem fsb_at_96 : fetchRel feSubCode 0x96 = some (.store .sw sp x0 0x44, 2) := by decide
theorem fsb_at_98 : fetchRel feSubCode 0x98 = some (.store .sw sp (7 : Fin 32) 0x48, 2) := by decide
theorem fsb_at_9a : fetchRel feSubCode 0x9A = some (.store .sw sp x0 0x4C, 2) := by decide
theorem fsb_at_9c : fetchRel feSubCode 0x9C = some (.store .sw sp a6 0x50, 2) := by decide
theorem fsb_at_9e : fetchRel feSubCode 0x9E = some (.store .sw sp x0 0x54, 2) := by decide
theorem fsb_at_a0 : fetchRel feSubCode 0xA0 = some (.store .sw sp (17 : Fin 32) 0x58, 2) := by decide
theorem fsb_at_a2 : fetchRel feSubCode 0xA2 = some (.store .sw sp x0 0x5C, 2) := by decide
theorem fsb_at_a4 : fetchRel feSubCode 0xA4 = some (.store .sw sp a5 0x60, 2) := by decide
theorem fsb_at_a6 : fetchRel feSubCode 0xA6 = some (.store .sw sp x0 0x64, 2) := by decide
theorem fsb_at_a8 : fetchRel feSubCode 0xA8 = some (.store .sw sp (5 : Fin 32) 0x68, 2) := by decide
theorem fsb_at_aa : fetchRel feSubCode 0xAA = some (.store .sw sp x0 0x6C, 2) := by decide
theorem fsb_at_ac : fetchRel feSubCode 0xAC = some (.store .sw sp a3 0x70, 2) := by decide
theorem fsb_at_ae : fetchRel feSubCode 0xAE = some (.store .sw sp x0 0x74, 2) := by decide
theorem fsb_at_b0 : fetchRel feSubCode 0xB0 = some (.store .sw sp a1 0x78, 2) := by decide
theorem fsb_at_b2 : fetchRel feSubCode 0xB2 = some (.store .sw sp x0 0x7C, 2) := by decide
theorem fsb_at_b4 : fetchRel feSubCode 0xB4 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem fsb_at_b6 : fetchRel feSubCode 0xB6 = some (.aluImm .add a1 sp 0x30, 2) := by decide
theorem fsb_at_b8 : fetchRel feSubCode 0xB8 = some (.auipc ra 0xFFFFF000, 4) := by decide
theorem fsb_at_bc : fetchRel feSubCode 0xBC = some (.jalr ra ra 0x676, 4) := by decide
theorem fsb_at_c0 : fetchRel feSubCode 0xC0 = some (.load .lw a0 sp 0x8, 2) := by decide
theorem fsb_at_c2 : fetchRel feSubCode 0xC2 = some (.load .lw a1 sp 0xC, 2) := by decide
theorem fsb_at_c4 : fetchRel feSubCode 0xC4 = some (.load .lw a2 sp 0x10, 2) := by decide
theorem fsb_at_c6 : fetchRel feSubCode 0xC6 = some (.load .lw a3 sp 0x14, 2) := by decide
theorem fsb_at_c8 : fetchRel feSubCode 0xC8 = some (.load .lw a4 sp 0x18, 2) := by decide
theorem fsb_at_ca : fetchRel feSubCode 0xCA = some (.load .lw a5 sp 0x1C, 2) := by decide
theorem fsb_at_cc : fetchRel feSubCode 0xCC = some (.load .lw (9 : Fin 32) sp 0x20, 2) := by decide
theorem fsb_at_ce : fetchRel feSubCode 0xCE = some (.load .lw a6 sp 0x24, 2) := by decide
theorem fsb_at_d0 : fetchRel feSubCode 0xD0 = some (.load .lw (17 : Fin 32) sp 0x28, 2) := by decide
theorem fsb_at_d2 : fetchRel feSubCode 0xD2 = some (.load .lw (5 : Fin 32) sp 0x2C, 2) := by decide
theorem fsb_at_d4 : fetchRel feSubCode 0xD4 = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem fsb_at_d6 : fetchRel feSubCode 0xD6 = some (.store .sw (8 : Fin 32) a1 0x4, 2) := by decide
theorem fsb_at_d8 : fetchRel feSubCode 0xD8 = some (.store .sw (8 : Fin 32) a2 0x8, 2) := by decide
theorem fsb_at_da : fetchRel feSubCode 0xDA = some (.store .sw (8 : Fin 32) a3 0xC, 2) := by decide
theorem fsb_at_dc : fetchRel feSubCode 0xDC = some (.store .sw (8 : Fin 32) a4 0x10, 2) := by decide
theorem fsb_at_de : fetchRel feSubCode 0xDE = some (.store .sw (8 : Fin 32) a5 0x14, 2) := by decide
theorem fsb_at_e0 : fetchRel feSubCode 0xE0 = some (.store .sw (8 : Fin 32) (9 : Fin 32) 0x18, 2) := by decide
theorem fsb_at_e2 : fetchRel feSubCode 0xE2 = some (.store .sw (8 : Fin 32) a6 0x1C, 4) := by decide
theorem fsb_at_e6 : fetchRel feSubCode 0xE6 = some (.store .sw (8 : Fin 32) (17 : Fin 32) 0x20, 4) := by decide
theorem fsb_at_ea : fetchRel feSubCode 0xEA = some (.store .sw (8 : Fin 32) (5 : Fin 32) 0x24, 4) := by decide
theorem fsb_at_ee : fetchRel feSubCode 0xEE = some (.load .lw ra sp 0x8C, 2) := by decide
theorem fsb_at_f0 : fetchRel feSubCode 0xF0 = some (.load .lw (8 : Fin 32) sp 0x88, 2) := by decide
theorem fsb_at_f2 : fetchRel feSubCode 0xF2 = some (.load .lw (9 : Fin 32) sp 0x84, 2) := by decide
theorem fsb_at_f4 : fetchRel feSubCode 0xF4 = some (.load .lw (18 : Fin 32) sp 0x80, 2) := by decide
theorem fsb_at_f6 : fetchRel feSubCode 0xF6 = some (.aluImm .add sp sp 0x90, 2) := by decide
theorem fsb_at_f8 : fetchRel feSubCode 0xF8 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- `<&FieldElement2625 as Sub>::sub` on the operands' limbs `x` and `y`, as
the Rust source computes it: `reduce` of each `(x[i] + 16 p[i]) - y[i]`,
with `16 p`'s limbs `0x3ffffed << 4`, `0x1ffffff << 4`, and `0x3ffffff << 4`,
and each `+` and `-` on `u32`. -/
def feSubSpec (x y : Nat → Word) : List Nat :=
  feReduceSpec (x 0 + 0x3FFFFED0 - y 0).toNat (x 1 + 0x1FFFFFF0 - y 1).toNat (x 2 + 0x3FFFFFF0 - y 2).toNat
    (x 3 + 0x1FFFFFF0 - y 3).toNat (x 4 + 0x3FFFFFF0 - y 4).toNat (x 5 + 0x1FFFFFF0 - y 5).toNat
    (x 6 + 0x3FFFFFF0 - y 6).toNat (x 7 + 0x1FFFFFF0 - y 7).toNat (x 8 + 0x3FFFFFF0 - y 8).toNat
    (x 9 + 0x1FFFFFF0 - y 9).toNat

theorem fsb_l0 (x y c d : Word) : x + c - y + d = x + (c + d) - y := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (-y) d, ← BitVec.add_assoc,
    BitVec.add_assoc x c d]

/-- Where `sub` runs: its code at an even `P` and `reduce`'s where its call
reaches it, `0xB0` bytes of stack at `G` (its 0x90-byte frame and `reduce`'s
0x20 below), the 4-aligned result at `out`, and the operands at `xp` and
`yp`. The result and the operands are apart from the stack, and the result
from `sub`'s code; the operands may overlap the result. -/
structure FeSubEnv (M : Word → BitVec 8) (P G out xp yp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P feSubCode
  red : CodeIn M (P + 0xFFFFF72E) feReduceCode
  hG : G.toNat % 4 = 0
  hGt : G.toNat + 0xB0 ≤ 2 ^ 32
  hx : xp.toNat % 4 = 0
  hy : yp.toNat % 4 = 0
  hout : out.toNat % 4 = 0
  sGC : Sep G 0xB0 P feSubCode.length
  sGR : Sep G 0xB0 (P + 0xFFFFF72E) feReduceCode.length
  sOC : Sep out 40 P feSubCode.length
  sOG : Sep out 40 G 0xB0
  sXG : Sep xp 40 G 0xB0
  sYG : Sep yp 40 G 0xB0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The compiled `<&FieldElement2625 as Sub>::sub`**, called with the result
at `out` and the operands' ten limbs at `xp` and `yp`: it stores `feSubSpec`
of the limbs. It returns with `sp` and every register but `t0` through `t6`
and `a0` through `a7` as they were, and changes no memory outside its 0xB0
bytes of stack and the result. -/
theorem feSub_correct (m : Machine) {P G out xp yp retAddr : Word} (env : FeSubEnv m.mem P G out xp yp)
    (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp) (ha2 : reg m a2 = yp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = G + 0xB0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = G + 0xB0 ∧ (∀ q, feMKeep q = true → reg m' q = reg m q) ∧
      (wordsAt m'.mem out 10).map BitVec.toNat =
        feSubSpec (fun i => memLoad32 m.mem (xp + BitVec.ofNat 32 (4 * i)))
          (fun i => memLoad32 m.mem (yp + BitVec.ofNat 32 (4 * i))) ∧
      ∀ x, Sep G 0xB0 x 1 → Sep out 40 x 1 → m'.mem x = m.mem x := by
  obtain ⟨F, hF⟩ : ∃ F, G + 0x20 = F := ⟨_, rfl⟩
  have hGt := env.hGt
  have hFn : F.toNat = G.toNat + 0x20 := by
    rw [← hF, BitVec.toNat_add, show (0x20 : Word).toNat = 0x20 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hFa : F.toNat % 4 = 0 := by rw [hFn]; have := env.hG; omega
  have fG : ∀ c, F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x20 + c) := fun c => by
    rw [← hF, show (0x20 : Word) = BitVec.ofNat 32 0x20 from rfl, add_ofNat_assoc]
  have hFsp : G + 0xB0 + 0xFFFFFF70 = F := by rw [← hF, BitVec.add_assoc]; rfl
  have hspF : F + 0x90 = G + 0xB0 := by rw [← hF, BitVec.add_assoc]; rfl
  have hGF : F + 0xFFFFFFE0 = G := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero G
  have inF : ∀ x, Sep G 0xB0 x 1 → Sep F 0x90 x 1 := fun x hx => by
    rw [← hF]; exact hx.sub (c := 0x20) (l := 0x90) (by decide)
  have sFC : Sep F 0x90 P feSubCode.length := by rw [← hF]; exact env.sGC.sub (c := 0x20) (l := 0x90) (by decide)
  have sFR : Sep F 0x90 (P + 0xFFFFF72E) feReduceCode.length := by
    rw [← hF]; exact env.sGR.sub (c := 0x20) (l := 0x90) (by decide)
  have sXF : Sep xp 40 F 0x90 := by rw [← hF]; exact env.sXG.subR (c := 0x20) (l := 0x90) (by decide)
  have sYF : Sep yp 40 F 0x90 := by rw [← hF]; exact env.sYG.subR (c := 0x20) (l := 0x90) (by decide)
  have sOFs : ∀ a b, a + 4 ≤ 40 → b + 4 ≤ 0x90 → Sep (out + BitVec.ofNat 32 a) 4 (F + BitVec.ofNat 32 b) 4 :=
    fun a b h1 h2 => by rw [fG]; exact (env.sOG.sub (c := a) (l := 4) h1).subR (c := 0x20 + b) (l := 4) (by omega)
  -- the prologue: the frame, and `ra`, `s0`, `s1`, and `s2` saved at its top
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code fsb_at_0 (off' := 2) (by decide)
  have k1 := u1.oldReg hz
  have sp1 : reg m1 sp = F := by rw [u1.newReg (by decide)]; show reg m sp + 0xFFFFFF70 = _; rw [hsp, hFsp]
  obtain ⟨p0, dp0, up0⟩ := u1.self.swG env.code fsb_at_2 (off' := 4) (by decide)
    (by rw [sp1]; exact fr_al' hFa (by decide)) (a := F + 0x8C) (v := reg m ra) (by rw [sp1]) (k1 _ (by decide))
  obtain ⟨P0, hP0⟩ : ∃ M', memStore32 m.mem (F + 0x8C) (reg m ra) = M' := ⟨_, rfl⟩
  rw [hP0] at up0
  have hcp0 : CodeIn P0 P feSubCode := by rw [← hP0]; exact env.code.store32 (frm_sep' sFC (by decide))
  obtain ⟨p1, dp1, up1⟩ := up0.swG hcp0 fsb_at_4 (off' := 6) (by decide)
    (by rw [sp1]; exact fr_al' hFa (by decide)) (a := F + 0x88) (v := reg m (8 : Fin 32)) (by rw [sp1])
    (k1 _ (by decide))
  obtain ⟨P1, hP1⟩ : ∃ M', memStore32 P0 (F + 0x88) (reg m (8 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP1] at up1
  have hcp1 : CodeIn P1 P feSubCode := by rw [← hP1]; exact hcp0.store32 (frm_sep' sFC (by decide))
  obtain ⟨p2, dp2, up2⟩ := up1.swG hcp1 fsb_at_6 (off' := 8) (by decide)
    (by rw [sp1]; exact fr_al' hFa (by decide)) (a := F + 0x84) (v := reg m (9 : Fin 32)) (by rw [sp1])
    (k1 _ (by decide))
  obtain ⟨P2, hP2⟩ : ∃ M', memStore32 P1 (F + 0x84) (reg m (9 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP2] at up2
  have hcp2 : CodeIn P2 P feSubCode := by rw [← hP2]; exact hcp1.store32 (frm_sep' sFC (by decide))
  obtain ⟨p3, dp3, up3⟩ := up2.swG hcp2 fsb_at_8 (off' := 0xA) (by decide)
    (by rw [sp1]; exact fr_al' hFa (by decide)) (a := F + 0x80) (v := reg m (18 : Fin 32)) (by rw [sp1])
    (k1 _ (by decide))
  obtain ⟨P3, hP3⟩ : ∃ M', memStore32 P2 (F + 0x80) (reg m (18 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP3] at up3
  have hcp3 : CodeIn P3 P feSubCode := by rw [← hP3]; exact hcp2.store32 (frm_sep' sFC (by decide))
  have fpro : ∀ x, Sep F 0x90 x 1 → P3 x = m.mem x := fun x hx => by
    rw [← hP3, memStore32_get_sep (frm_sep' hx (by decide)), ← hP2, memStore32_get_sep (frm_sep' hx (by decide)),
      ← hP1, memStore32_get_sep (frm_sep' hx (by decide)), ← hP0, memStore32_get_sep (frm_sep' hx (by decide))]
  have sv8C : memLoad32 P3 (F + 0x8C) = reg m ra := by
    rw [← hP3, memLoad32_store32_sep (show Sep (F + 0x80) 4 (F + 0x8C) 4 from sep_offsets F (by decide) (by decide)
      (by decide)), ← hP2, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x8C) 4 from sep_offsets F (by decide)
      (by decide) (by decide)), ← hP1, memLoad32_store32_sep (show Sep (F + 0x88) 4 (F + 0x8C) 4 from
      sep_offsets F (by decide) (by decide) (by decide)), ← hP0, memLoad32_store32_same]
  have sv88 : memLoad32 P3 (F + 0x88) = reg m (8 : Fin 32) := by
    rw [← hP3, memLoad32_store32_sep (show Sep (F + 0x80) 4 (F + 0x88) 4 from sep_offsets F (by decide) (by decide)
      (by decide)), ← hP2, memLoad32_store32_sep (show Sep (F + 0x84) 4 (F + 0x88) 4 from sep_offsets F (by decide)
      (by decide) (by decide)), ← hP1, memLoad32_store32_same]
  have sv84 : memLoad32 P3 (F + 0x84) = reg m (9 : Fin 32) := by
    rw [← hP3, memLoad32_store32_sep (show Sep (F + 0x80) 4 (F + 0x84) 4 from sep_offsets F (by decide) (by decide)
      (by decide)), ← hP2, memLoad32_store32_same]
  have sv80 : memLoad32 P3 (F + 0x80) = reg m (18 : Fin 32) := by rw [← hP3, memLoad32_store32_same]
  obtain ⟨X0, hX0⟩ : ∃ v, memLoad32 m.mem (xp + BitVec.ofNat 32 (4 * 0)) = v := ⟨_, rfl⟩
  obtain ⟨X1, hX1⟩ : ∃ v, memLoad32 m.mem (xp + BitVec.ofNat 32 (4 * 1)) = v := ⟨_, rfl⟩
  obtain ⟨X2, hX2⟩ : ∃ v, memLoad32 m.mem (xp + BitVec.ofNat 32 (4 * 2)) = v := ⟨_, rfl⟩
  obtain ⟨X3, hX3⟩ : ∃ v, memLoad32 m.mem (xp + BitVec.ofNat 32 (4 * 3)) = v := ⟨_, rfl⟩
  obtain ⟨X4, hX4⟩ : ∃ v, memLoad32 m.mem (xp + BitVec.ofNat 32 (4 * 4)) = v := ⟨_, rfl⟩
  obtain ⟨X5, hX5⟩ : ∃ v, memLoad32 m.mem (xp + BitVec.ofNat 32 (4 * 5)) = v := ⟨_, rfl⟩
  obtain ⟨X6, hX6⟩ : ∃ v, memLoad32 m.mem (xp + BitVec.ofNat 32 (4 * 6)) = v := ⟨_, rfl⟩
  obtain ⟨X7, hX7⟩ : ∃ v, memLoad32 m.mem (xp + BitVec.ofNat 32 (4 * 7)) = v := ⟨_, rfl⟩
  obtain ⟨X8, hX8⟩ : ∃ v, memLoad32 m.mem (xp + BitVec.ofNat 32 (4 * 8)) = v := ⟨_, rfl⟩
  obtain ⟨X9, hX9⟩ : ∃ v, memLoad32 m.mem (xp + BitVec.ofNat 32 (4 * 9)) = v := ⟨_, rfl⟩
  obtain ⟨Y0, hY0⟩ : ∃ v, memLoad32 m.mem (yp + BitVec.ofNat 32 (4 * 0)) = v := ⟨_, rfl⟩
  obtain ⟨Y1, hY1⟩ : ∃ v, memLoad32 m.mem (yp + BitVec.ofNat 32 (4 * 1)) = v := ⟨_, rfl⟩
  obtain ⟨Y2, hY2⟩ : ∃ v, memLoad32 m.mem (yp + BitVec.ofNat 32 (4 * 2)) = v := ⟨_, rfl⟩
  obtain ⟨Y3, hY3⟩ : ∃ v, memLoad32 m.mem (yp + BitVec.ofNat 32 (4 * 3)) = v := ⟨_, rfl⟩
  obtain ⟨Y4, hY4⟩ : ∃ v, memLoad32 m.mem (yp + BitVec.ofNat 32 (4 * 4)) = v := ⟨_, rfl⟩
  obtain ⟨Y5, hY5⟩ : ∃ v, memLoad32 m.mem (yp + BitVec.ofNat 32 (4 * 5)) = v := ⟨_, rfl⟩
  obtain ⟨Y6, hY6⟩ : ∃ v, memLoad32 m.mem (yp + BitVec.ofNat 32 (4 * 6)) = v := ⟨_, rfl⟩
  obtain ⟨Y7, hY7⟩ : ∃ v, memLoad32 m.mem (yp + BitVec.ofNat 32 (4 * 7)) = v := ⟨_, rfl⟩
  obtain ⟨Y8, hY8⟩ : ∃ v, memLoad32 m.mem (yp + BitVec.ofNat 32 (4 * 8)) = v := ⟨_, rfl⟩
  obtain ⟨Y9, hY9⟩ : ∃ v, memLoad32 m.mem (yp + BitVec.ofNat 32 (4 * 9)) = v := ⟨_, rfl⟩
  have i10 : reg m1 a0 = out := by rw [k1 _ (by decide), ha0]
  have i11 : reg m1 a1 = xp := by rw [k1 _ (by decide), ha1]
  have i12 : reg m1 a2 = yp := by rw [k1 _ (by decide), ha2]
  obtain ⟨n101, d101, u101⟩ := up3.alu hcp3 fsb_at_a (off' := 0xC) (by decide)
  have f101 : reg n101 (8 : Fin 32) = out := by
    rw [u101.newReg (by decide)]; show reg m1 0 + reg m1 a0 = _
    rw [up3.zero, i10]; exact BitVec.zero_add _
  have k101 := u101.oldReg up3.zero
  obtain ⟨n102, d102, u102⟩ := u101.self.lwE hcp3 fsb_at_c (off' := 0xE) (by decide)
    (by rw [k101 a1 (by decide), i11]; exact fr_al' env.hx (by decide)) (v := X0)
    (by rw [k101 a1 (by decide), i11]; exact (load_frame fpro (sXF.symm.subR (c := 0) (l := 4) (by decide))).trans hX0)
  have f102 : reg n102 a0 = X0 := u102.newReg (by decide)
  have k102 := u102.oldReg u101.self.zero
  obtain ⟨n103, d103, u103⟩ := u102.self.lwE hcp3 fsb_at_e (off' := 0x12) (by decide)
    (by rw [k102 a1 (by decide), k101 a1 (by decide), i11]; exact fr_al' env.hx (by decide)) (v := X1)
    (by rw [k102 a1 (by decide), k101 a1 (by decide), i11]; exact (load_frame fpro (sXF.symm.subR (c := 4) (l := 4) (by decide))).trans hX1)
  have f103 : reg n103 (30 : Fin 32) = X1 := u103.newReg (by decide)
  have k103 := u103.oldReg u102.self.zero
  obtain ⟨n104, d104, u104⟩ := u103.self.lwE hcp3 fsb_at_12 (off' := 0x16) (by decide)
    (by rw [k103 a1 (by decide), k102 a1 (by decide), k101 a1 (by decide), i11]; exact fr_al' env.hx (by decide)) (v := X2)
    (by rw [k103 a1 (by decide), k102 a1 (by decide), k101 a1 (by decide), i11]; exact (load_frame fpro (sXF.symm.subR (c := 8) (l := 4) (by decide))).trans hX2)
  have f104 : reg n104 (7 : Fin 32) = X2 := u104.newReg (by decide)
  have k104 := u104.oldReg u103.self.zero
  obtain ⟨n105, d105, u105⟩ := u104.self.lwE hcp3 fsb_at_16 (off' := 0x1A) (by decide)
    (by rw [k104 a1 (by decide), k103 a1 (by decide), k102 a1 (by decide), k101 a1 (by decide), i11]; exact fr_al' env.hx (by decide)) (v := X3)
    (by rw [k104 a1 (by decide), k103 a1 (by decide), k102 a1 (by decide), k101 a1 (by decide), i11]; exact (load_frame fpro (sXF.symm.subR (c := 12) (l := 4) (by decide))).trans hX3)
  have f105 : reg n105 (28 : Fin 32) = X3 := u105.newReg (by decide)
  have k105 := u105.oldReg u104.self.zero
  obtain ⟨n106, d106, u106⟩ := u105.self.lwE hcp3 fsb_at_1a (off' := 0x1E) (by decide)
    (by rw [k105 a1 (by decide), k104 a1 (by decide), k103 a1 (by decide), k102 a1 (by decide), k101 a1 (by decide), i11]; exact fr_al' env.hx (by decide)) (v := X4)
    (by rw [k105 a1 (by decide), k104 a1 (by decide), k103 a1 (by decide), k102 a1 (by decide), k101 a1 (by decide), i11]; exact (load_frame fpro (sXF.symm.subR (c := 16) (l := 4) (by decide))).trans hX4)
  have f106 : reg n106 a6 = X4 := u106.newReg (by decide)
  have k106 := u106.oldReg u105.self.zero
  obtain ⟨n107, d107, u107⟩ := u106.self.lwE hcp3 fsb_at_1e (off' := 0x22) (by decide)
    (by rw [k106 a1 (by decide), k105 a1 (by decide), k104 a1 (by decide), k103 a1 (by decide), k102 a1 (by decide), k101 a1 (by decide), i11]; exact fr_al' env.hx (by decide)) (v := X5)
    (by rw [k106 a1 (by decide), k105 a1 (by decide), k104 a1 (by decide), k103 a1 (by decide), k102 a1 (by decide), k101 a1 (by decide), i11]; exact (load_frame fpro (sXF.symm.subR (c := 20) (l := 4) (by decide))).trans hX5)
  have f107 : reg n107 a7 = X5 := u107.newReg (by decide)
  have k107 := u107.oldReg u106.self.zero
  obtain ⟨n108, d108, u108⟩ := u107.self.lwE hcp3 fsb_at_22 (off' := 0x26) (by decide)
    (by rw [k107 a1 (by decide), k106 a1 (by decide), k105 a1 (by decide), k104 a1 (by decide), k103 a1 (by decide), k102 a1 (by decide), k101 a1 (by decide), i11]; exact fr_al' env.hx (by decide)) (v := X6)
    (by rw [k107 a1 (by decide), k106 a1 (by decide), k105 a1 (by decide), k104 a1 (by decide), k103 a1 (by decide), k102 a1 (by decide), k101 a1 (by decide), i11]; exact (load_frame fpro (sXF.symm.subR (c := 24) (l := 4) (by decide))).trans hX6)
  have f108 : reg n108 (5 : Fin 32) = X6 := u108.newReg (by decide)
  have k108 := u108.oldReg u107.self.zero
  obtain ⟨n109, d109, u109⟩ := u108.self.lwE hcp3 fsb_at_26 (off' := 0x2A) (by decide)
    (by rw [k108 a1 (by decide), k107 a1 (by decide), k106 a1 (by decide), k105 a1 (by decide), k104 a1 (by decide), k103 a1 (by decide), k102 a1 (by decide), k101 a1 (by decide), i11]; exact fr_al' env.hx (by decide)) (v := X7)
    (by rw [k108 a1 (by decide), k107 a1 (by decide), k106 a1 (by decide), k105 a1 (by decide), k104 a1 (by decide), k103 a1 (by decide), k102 a1 (by decide), k101 a1 (by decide), i11]; exact (load_frame fpro (sXF.symm.subR (c := 28) (l := 4) (by decide))).trans hX7)
  have f109 : reg n109 (6 : Fin 32) = X7 := u109.newReg (by decide)
  have k109 := u109.oldReg u108.self.zero
  obtain ⟨n110, d110, u110⟩ := u109.self.lui hcp3 fsb_at_2a (off' := 0x2E) (by decide)
  have f110 : reg n110 a4 = 0x40000000 := u110.newReg (by decide)
  have k110 := u110.oldReg u109.self.zero
  obtain ⟨n111, d111, u111⟩ := u110.self.aluImm hcp3 fsb_at_2e (off' := 0x30) (by decide)
  have f111 : reg n111 a4 = (0x40000000 + 0xFFFFFFF0) := by
    rw [u111.newReg (by decide)]; show reg n110 a4 + 0xFFFFFFF0 = _; rw [f110]
  have k111 := u111.oldReg u110.self.zero
  obtain ⟨n112, d112, u112⟩ := u111.self.lwE hcp3 fsb_at_30 (off' := 0x34) (by decide)
    (by rw [k111 a2 (by decide), k110 a2 (by decide), k109 a2 (by decide), k108 a2 (by decide), k107 a2 (by decide), k106 a2 (by decide), k105 a2 (by decide), k104 a2 (by decide), k103 a2 (by decide), k102 a2 (by decide), k101 a2 (by decide), i12]; exact fr_al' env.hy (by decide)) (v := Y0)
    (by rw [k111 a2 (by decide), k110 a2 (by decide), k109 a2 (by decide), k108 a2 (by decide), k107 a2 (by decide), k106 a2 (by decide), k105 a2 (by decide), k104 a2 (by decide), k103 a2 (by decide), k102 a2 (by decide), k101 a2 (by decide), i12]; exact (load_frame fpro (sYF.symm.subR (c := 0) (l := 4) (by decide))).trans hY0)
  have f112 : reg n112 (31 : Fin 32) = Y0 := u112.newReg (by decide)
  have k112 := u112.oldReg u111.self.zero
  obtain ⟨n113, d113, u113⟩ := u112.self.lui hcp3 fsb_at_34 (off' := 0x38) (by decide)
  have f113 : reg n113 (29 : Fin 32) = 0x20000000 := u113.newReg (by decide)
  have k113 := u113.oldReg u112.self.zero
  obtain ⟨n114, d114, u114⟩ := u113.self.lwE hcp3 fsb_at_38 (off' := 0x3A) (by decide)
    (by rw [k113 a2 (by decide), k112 a2 (by decide), k111 a2 (by decide), k110 a2 (by decide), k109 a2 (by decide), k108 a2 (by decide), k107 a2 (by decide), k106 a2 (by decide), k105 a2 (by decide), k104 a2 (by decide), k103 a2 (by decide), k102 a2 (by decide), k101 a2 (by decide), i12]; exact fr_al' env.hy (by decide)) (v := Y1)
    (by rw [k113 a2 (by decide), k112 a2 (by decide), k111 a2 (by decide), k110 a2 (by decide), k109 a2 (by decide), k108 a2 (by decide), k107 a2 (by decide), k106 a2 (by decide), k105 a2 (by decide), k104 a2 (by decide), k103 a2 (by decide), k102 a2 (by decide), k101 a2 (by decide), i12]; exact (load_frame fpro (sYF.symm.subR (c := 4) (l := 4) (by decide))).trans hY1)
  have f114 : reg n114 a3 = Y1 := u114.newReg (by decide)
  have k114 := u114.oldReg u113.self.zero
  obtain ⟨n115, d115, u115⟩ := u114.self.alu hcp3 fsb_at_3a (off' := 0x3C) (by decide)
  have f115 : reg n115 a0 = (X0 + (0x40000000 + 0xFFFFFFF0)) := by
    rw [u115.newReg (by decide)]; show reg n114 a0 + reg n114 a4 = _
    rw [k114 a0 (by decide), k113 a0 (by decide), k112 a0 (by decide), k111 a0 (by decide), k110 a0 (by decide), k109 a0 (by decide), k108 a0 (by decide), k107 a0 (by decide), k106 a0 (by decide), k105 a0 (by decide), k104 a0 (by decide), k103 a0 (by decide), f102, k114 a4 (by decide), k113 a4 (by decide), k112 a4 (by decide), f111]
  have k115 := u115.oldReg u114.self.zero
  obtain ⟨n116, d116, u116⟩ := u115.self.aluImm hcp3 fsb_at_3c (off' := 0x3E) (by decide)
  have f116 : reg n116 (29 : Fin 32) = (0x20000000 + 0xFFFFFFF0) := by
    rw [u116.newReg (by decide)]; show reg n115 (29 : Fin 32) + 0xFFFFFFF0 = _; rw [k115 (29 : Fin 32) (by decide), k114 (29 : Fin 32) (by decide), f113]
  have k116 := u116.oldReg u115.self.zero
  have q16_2 : reg n116 sp = F := by rw [k116 sp (by decide), k115 sp (by decide), k114 sp (by decide), k113 sp (by decide), k112 sp (by decide), k111 sp (by decide), k110 sp (by decide), k109 sp (by decide), k108 sp (by decide), k107 sp (by decide), k106 sp (by decide), k105 sp (by decide), k104 sp (by decide), k103 sp (by decide), k102 sp (by decide), k101 sp (by decide), sp1]
  have q16_5 : reg n116 (5 : Fin 32) = X6 := by rw [k116 (5 : Fin 32) (by decide), k115 (5 : Fin 32) (by decide), k114 (5 : Fin 32) (by decide), k113 (5 : Fin 32) (by decide), k112 (5 : Fin 32) (by decide), k111 (5 : Fin 32) (by decide), k110 (5 : Fin 32) (by decide), k109 (5 : Fin 32) (by decide), f108]
  have q16_6 : reg n116 (6 : Fin 32) = X7 := by rw [k116 (6 : Fin 32) (by decide), k115 (6 : Fin 32) (by decide), k114 (6 : Fin 32) (by decide), k113 (6 : Fin 32) (by decide), k112 (6 : Fin 32) (by decide), k111 (6 : Fin 32) (by decide), k110 (6 : Fin 32) (by decide), f109]
  have q16_7 : reg n116 (7 : Fin 32) = X2 := by rw [k116 (7 : Fin 32) (by decide), k115 (7 : Fin 32) (by decide), k114 (7 : Fin 32) (by decide), k113 (7 : Fin 32) (by decide), k112 (7 : Fin 32) (by decide), k111 (7 : Fin 32) (by decide), k110 (7 : Fin 32) (by decide), k109 (7 : Fin 32) (by decide), k108 (7 : Fin 32) (by decide), k107 (7 : Fin 32) (by decide), k106 (7 : Fin 32) (by decide), k105 (7 : Fin 32) (by decide), f104]
  have q16_8 : reg n116 (8 : Fin 32) = out := by rw [k116 (8 : Fin 32) (by decide), k115 (8 : Fin 32) (by decide), k114 (8 : Fin 32) (by decide), k113 (8 : Fin 32) (by decide), k112 (8 : Fin 32) (by decide), k111 (8 : Fin 32) (by decide), k110 (8 : Fin 32) (by decide), k109 (8 : Fin 32) (by decide), k108 (8 : Fin 32) (by decide), k107 (8 : Fin 32) (by decide), k106 (8 : Fin 32) (by decide), k105 (8 : Fin 32) (by decide), k104 (8 : Fin 32) (by decide), k103 (8 : Fin 32) (by decide), k102 (8 : Fin 32) (by decide), f101]
  have q16_10 : reg n116 a0 = (X0 + (0x40000000 + 0xFFFFFFF0)) := by rw [k116 a0 (by decide), f115]
  have q16_11 : reg n116 a1 = xp := by rw [k116 a1 (by decide), k115 a1 (by decide), k114 a1 (by decide), k113 a1 (by decide), k112 a1 (by decide), k111 a1 (by decide), k110 a1 (by decide), k109 a1 (by decide), k108 a1 (by decide), k107 a1 (by decide), k106 a1 (by decide), k105 a1 (by decide), k104 a1 (by decide), k103 a1 (by decide), k102 a1 (by decide), k101 a1 (by decide), i11]
  have q16_12 : reg n116 a2 = yp := by rw [k116 a2 (by decide), k115 a2 (by decide), k114 a2 (by decide), k113 a2 (by decide), k112 a2 (by decide), k111 a2 (by decide), k110 a2 (by decide), k109 a2 (by decide), k108 a2 (by decide), k107 a2 (by decide), k106 a2 (by decide), k105 a2 (by decide), k104 a2 (by decide), k103 a2 (by decide), k102 a2 (by decide), k101 a2 (by decide), i12]
  have q16_13 : reg n116 a3 = Y1 := by rw [k116 a3 (by decide), k115 a3 (by decide), f114]
  have q16_14 : reg n116 a4 = (0x40000000 + 0xFFFFFFF0) := by rw [k116 a4 (by decide), k115 a4 (by decide), k114 a4 (by decide), k113 a4 (by decide), k112 a4 (by decide), f111]
  have q16_16 : reg n116 a6 = X4 := by rw [k116 a6 (by decide), k115 a6 (by decide), k114 a6 (by decide), k113 a6 (by decide), k112 a6 (by decide), k111 a6 (by decide), k110 a6 (by decide), k109 a6 (by decide), k108 a6 (by decide), k107 a6 (by decide), f106]
  have q16_17 : reg n116 a7 = X5 := by rw [k116 a7 (by decide), k115 a7 (by decide), k114 a7 (by decide), k113 a7 (by decide), k112 a7 (by decide), k111 a7 (by decide), k110 a7 (by decide), k109 a7 (by decide), k108 a7 (by decide), f107]
  have q16_28 : reg n116 (28 : Fin 32) = X3 := by rw [k116 (28 : Fin 32) (by decide), k115 (28 : Fin 32) (by decide), k114 (28 : Fin 32) (by decide), k113 (28 : Fin 32) (by decide), k112 (28 : Fin 32) (by decide), k111 (28 : Fin 32) (by decide), k110 (28 : Fin 32) (by decide), k109 (28 : Fin 32) (by decide), k108 (28 : Fin 32) (by decide), k107 (28 : Fin 32) (by decide), k106 (28 : Fin 32) (by decide), f105]
  have q16_30 : reg n116 (30 : Fin 32) = X1 := by rw [k116 (30 : Fin 32) (by decide), k115 (30 : Fin 32) (by decide), k114 (30 : Fin 32) (by decide), k113 (30 : Fin 32) (by decide), k112 (30 : Fin 32) (by decide), k111 (30 : Fin 32) (by decide), k110 (30 : Fin 32) (by decide), k109 (30 : Fin 32) (by decide), k108 (30 : Fin 32) (by decide), k107 (30 : Fin 32) (by decide), k106 (30 : Fin 32) (by decide), k105 (30 : Fin 32) (by decide), k104 (30 : Fin 32) (by decide), f103]
  have q16_31 : reg n116 (31 : Fin 32) = Y0 := by rw [k116 (31 : Fin 32) (by decide), k115 (31 : Fin 32) (by decide), k114 (31 : Fin 32) (by decide), k113 (31 : Fin 32) (by decide), f112]
  obtain ⟨n117, d117, u117⟩ := u116.self.lwE hcp3 fsb_at_3e (off' := 0x40) (by decide)
    (by rw [q16_12]; exact fr_al' env.hy (by decide)) (v := Y2)
    (by rw [q16_12]; exact (load_frame fpro (sYF.symm.subR (c := 8) (l := 4) (by decide))).trans hY2)
  have f117 : reg n117 a5 = Y2 := u117.newReg (by decide)
  have k117 := u117.oldReg u116.self.zero
  obtain ⟨n118, d118, u118⟩ := u117.self.lwE hcp3 fsb_at_40 (off' := 0x42) (by decide)
    (by rw [k117 a2 (by decide), q16_12]; exact fr_al' env.hy (by decide)) (v := Y3)
    (by rw [k117 a2 (by decide), q16_12]; exact (load_frame fpro (sYF.symm.subR (c := 12) (l := 4) (by decide))).trans hY3)
  have f118 : reg n118 (9 : Fin 32) = Y3 := u118.newReg (by decide)
  have k118 := u118.oldReg u117.self.zero
  obtain ⟨n119, d119, u119⟩ := u118.self.alu hcp3 fsb_at_42 (off' := 0x46) (by decide)
  have f119 : reg n119 (18 : Fin 32) = ((X0 + (0x40000000 + 0xFFFFFFF0)) - Y0) := by
    rw [u119.newReg (by decide)]; show reg n118 a0 - reg n118 (31 : Fin 32) = _
    rw [k118 a0 (by decide), k117 a0 (by decide), q16_10, k118 (31 : Fin 32) (by decide), k117 (31 : Fin 32) (by decide), q16_31]
  have k119 := u119.oldReg u118.self.zero
  obtain ⟨n120, d120, u120⟩ := u119.self.alu hcp3 fsb_at_46 (off' := 0x48) (by decide)
  have f120 : reg n120 (30 : Fin 32) = (X1 + (0x20000000 + 0xFFFFFFF0)) := by
    rw [u120.newReg (by decide)]; show reg n119 (30 : Fin 32) + reg n119 (29 : Fin 32) = _
    rw [k119 (30 : Fin 32) (by decide), k118 (30 : Fin 32) (by decide), k117 (30 : Fin 32) (by decide), q16_30, k119 (29 : Fin 32) (by decide), k118 (29 : Fin 32) (by decide), k117 (29 : Fin 32) (by decide), f116]
  have k120 := u120.oldReg u119.self.zero
  obtain ⟨n121, d121, u121⟩ := u120.self.alu hcp3 fsb_at_48 (off' := 0x4C) (by decide)
  have f121 : reg n121 (30 : Fin 32) = ((X1 + (0x20000000 + 0xFFFFFFF0)) - Y1) := by
    rw [u121.newReg (by decide)]; show reg n120 (30 : Fin 32) - reg n120 a3 = _
    rw [f120, k120 a3 (by decide), k119 a3 (by decide), k118 a3 (by decide), k117 a3 (by decide), q16_13]
  have k121 := u121.oldReg u120.self.zero
  obtain ⟨n122, d122, u122⟩ := u121.self.alu hcp3 fsb_at_4c (off' := 0x4E) (by decide)
  have f122 : reg n122 (7 : Fin 32) = (X2 + (0x40000000 + 0xFFFFFFF0)) := by
    rw [u122.newReg (by decide)]; show reg n121 (7 : Fin 32) + reg n121 a4 = _
    rw [k121 (7 : Fin 32) (by decide), k120 (7 : Fin 32) (by decide), k119 (7 : Fin 32) (by decide), k118 (7 : Fin 32) (by decide), k117 (7 : Fin 32) (by decide), q16_7, k121 a4 (by decide), k120 a4 (by decide), k119 a4 (by decide), k118 a4 (by decide), k117 a4 (by decide), q16_14]
  have k122 := u122.oldReg u121.self.zero
  obtain ⟨n123, d123, u123⟩ := u122.self.alu hcp3 fsb_at_4e (off' := 0x50) (by decide)
  have f123 : reg n123 (28 : Fin 32) = (X3 + (0x20000000 + 0xFFFFFFF0)) := by
    rw [u123.newReg (by decide)]; show reg n122 (28 : Fin 32) + reg n122 (29 : Fin 32) = _
    rw [k122 (28 : Fin 32) (by decide), k121 (28 : Fin 32) (by decide), k120 (28 : Fin 32) (by decide), k119 (28 : Fin 32) (by decide), k118 (28 : Fin 32) (by decide), k117 (28 : Fin 32) (by decide), q16_28, k122 (29 : Fin 32) (by decide), k121 (29 : Fin 32) (by decide), k120 (29 : Fin 32) (by decide), k119 (29 : Fin 32) (by decide), k118 (29 : Fin 32) (by decide), k117 (29 : Fin 32) (by decide), f116]
  have k123 := u123.oldReg u122.self.zero
  obtain ⟨n124, d124, u124⟩ := u123.self.lwE hcp3 fsb_at_50 (off' := 0x52) (by decide)
    (by rw [k123 a2 (by decide), k122 a2 (by decide), k121 a2 (by decide), k120 a2 (by decide), k119 a2 (by decide), k118 a2 (by decide), k117 a2 (by decide), q16_12]; exact fr_al' env.hy (by decide)) (v := Y4)
    (by rw [k123 a2 (by decide), k122 a2 (by decide), k121 a2 (by decide), k120 a2 (by decide), k119 a2 (by decide), k118 a2 (by decide), k117 a2 (by decide), q16_12]; exact (load_frame fpro (sYF.symm.subR (c := 16) (l := 4) (by decide))).trans hY4)
  have f124 : reg n124 a3 = Y4 := u124.newReg (by decide)
  have k124 := u124.oldReg u123.self.zero
  obtain ⟨n125, d125, u125⟩ := u124.self.alu hcp3 fsb_at_52 (off' := 0x56) (by decide)
  have f125 : reg n125 (31 : Fin 32) = ((X2 + (0x40000000 + 0xFFFFFFF0)) - Y2) := by
    rw [u125.newReg (by decide)]; show reg n124 (7 : Fin 32) - reg n124 a5 = _
    rw [k124 (7 : Fin 32) (by decide), k123 (7 : Fin 32) (by decide), f122, k124 a5 (by decide), k123 a5 (by decide), k122 a5 (by decide), k121 a5 (by decide), k120 a5 (by decide), k119 a5 (by decide), k118 a5 (by decide), f117]
  have k125 := u125.oldReg u124.self.zero
  obtain ⟨n126, d126, u126⟩ := u125.self.alu hcp3 fsb_at_56 (off' := 0x5A) (by decide)
  have f126 : reg n126 (7 : Fin 32) = ((X3 + (0x20000000 + 0xFFFFFFF0)) - Y3) := by
    rw [u126.newReg (by decide)]; show reg n125 (28 : Fin 32) - reg n125 (9 : Fin 32) = _
    rw [k125 (28 : Fin 32) (by decide), k124 (28 : Fin 32) (by decide), f123, k125 (9 : Fin 32) (by decide), k124 (9 : Fin 32) (by decide), k123 (9 : Fin 32) (by decide), k122 (9 : Fin 32) (by decide), k121 (9 : Fin 32) (by decide), k120 (9 : Fin 32) (by decide), k119 (9 : Fin 32) (by decide), f118]
  have k126 := u126.oldReg u125.self.zero
  obtain ⟨n127, d127, u127⟩ := u126.self.alu hcp3 fsb_at_5a (off' := 0x5C) (by decide)
  have f127 : reg n127 a6 = (X4 + (0x40000000 + 0xFFFFFFF0)) := by
    rw [u127.newReg (by decide)]; show reg n126 a6 + reg n126 a4 = _
    rw [k126 a6 (by decide), k125 a6 (by decide), k124 a6 (by decide), k123 a6 (by decide), k122 a6 (by decide), k121 a6 (by decide), k120 a6 (by decide), k119 a6 (by decide), k118 a6 (by decide), k117 a6 (by decide), q16_16, k126 a4 (by decide), k125 a4 (by decide), k124 a4 (by decide), k123 a4 (by decide), k122 a4 (by decide), k121 a4 (by decide), k120 a4 (by decide), k119 a4 (by decide), k118 a4 (by decide), k117 a4 (by decide), q16_14]
  have k127 := u127.oldReg u126.self.zero
  obtain ⟨n128, d128, u128⟩ := u127.self.lwE hcp3 fsb_at_5c (off' := 0x5E) (by decide)
    (by rw [k127 a2 (by decide), k126 a2 (by decide), k125 a2 (by decide), k124 a2 (by decide), k123 a2 (by decide), k122 a2 (by decide), k121 a2 (by decide), k120 a2 (by decide), k119 a2 (by decide), k118 a2 (by decide), k117 a2 (by decide), q16_12]; exact fr_al' env.hy (by decide)) (v := Y5)
    (by rw [k127 a2 (by decide), k126 a2 (by decide), k125 a2 (by decide), k124 a2 (by decide), k123 a2 (by decide), k122 a2 (by decide), k121 a2 (by decide), k120 a2 (by decide), k119 a2 (by decide), k118 a2 (by decide), k117 a2 (by decide), q16_12]; exact (load_frame fpro (sYF.symm.subR (c := 20) (l := 4) (by decide))).trans hY5)
  have f128 : reg n128 (9 : Fin 32) = Y5 := u128.newReg (by decide)
  have k128 := u128.oldReg u127.self.zero
  obtain ⟨n129, d129, u129⟩ := u128.self.lwE hcp3 fsb_at_5e (off' := 0x60) (by decide)
    (by rw [k128 a2 (by decide), k127 a2 (by decide), k126 a2 (by decide), k125 a2 (by decide), k124 a2 (by decide), k123 a2 (by decide), k122 a2 (by decide), k121 a2 (by decide), k120 a2 (by decide), k119 a2 (by decide), k118 a2 (by decide), k117 a2 (by decide), q16_12]; exact fr_al' env.hy (by decide)) (v := Y6)
    (by rw [k128 a2 (by decide), k127 a2 (by decide), k126 a2 (by decide), k125 a2 (by decide), k124 a2 (by decide), k123 a2 (by decide), k122 a2 (by decide), k121 a2 (by decide), k120 a2 (by decide), k119 a2 (by decide), k118 a2 (by decide), k117 a2 (by decide), q16_12]; exact (load_frame fpro (sYF.symm.subR (c := 24) (l := 4) (by decide))).trans hY6)
  have f129 : reg n129 a5 = Y6 := u129.newReg (by decide)
  have k129 := u129.oldReg u128.self.zero
  obtain ⟨n130, d130, u130⟩ := u129.self.lwE hcp3 fsb_at_60 (off' := 0x62) (by decide)
    (by rw [k129 a2 (by decide), k128 a2 (by decide), k127 a2 (by decide), k126 a2 (by decide), k125 a2 (by decide), k124 a2 (by decide), k123 a2 (by decide), k122 a2 (by decide), k121 a2 (by decide), k120 a2 (by decide), k119 a2 (by decide), k118 a2 (by decide), k117 a2 (by decide), q16_12]; exact fr_al' env.hy (by decide)) (v := Y7)
    (by rw [k129 a2 (by decide), k128 a2 (by decide), k127 a2 (by decide), k126 a2 (by decide), k125 a2 (by decide), k124 a2 (by decide), k123 a2 (by decide), k122 a2 (by decide), k121 a2 (by decide), k120 a2 (by decide), k119 a2 (by decide), k118 a2 (by decide), k117 a2 (by decide), q16_12]; exact (load_frame fpro (sYF.symm.subR (c := 28) (l := 4) (by decide))).trans hY7)
  have f130 : reg n130 a0 = Y7 := u130.newReg (by decide)
  have k130 := u130.oldReg u129.self.zero
  obtain ⟨n131, d131, u131⟩ := u130.self.alu hcp3 fsb_at_62 (off' := 0x66) (by decide)
  have f131 : reg n131 a6 = ((X4 + (0x40000000 + 0xFFFFFFF0)) - Y4) := by
    rw [u131.newReg (by decide)]; show reg n130 a6 - reg n130 a3 = _
    rw [k130 a6 (by decide), k129 a6 (by decide), k128 a6 (by decide), f127, k130 a3 (by decide), k129 a3 (by decide), k128 a3 (by decide), k127 a3 (by decide), k126 a3 (by decide), k125 a3 (by decide), f124]
  have k131 := u131.oldReg u130.self.zero
  obtain ⟨n132, d132, u132⟩ := u131.self.lwE hcp3 fsb_at_66 (off' := 0x68) (by decide)
    (by rw [k131 a1 (by decide), k130 a1 (by decide), k129 a1 (by decide), k128 a1 (by decide), k127 a1 (by decide), k126 a1 (by decide), k125 a1 (by decide), k124 a1 (by decide), k123 a1 (by decide), k122 a1 (by decide), k121 a1 (by decide), k120 a1 (by decide), k119 a1 (by decide), k118 a1 (by decide), k117 a1 (by decide), q16_11]; exact fr_al' env.hx (by decide)) (v := X8)
    (by rw [k131 a1 (by decide), k130 a1 (by decide), k129 a1 (by decide), k128 a1 (by decide), k127 a1 (by decide), k126 a1 (by decide), k125 a1 (by decide), k124 a1 (by decide), k123 a1 (by decide), k122 a1 (by decide), k121 a1 (by decide), k120 a1 (by decide), k119 a1 (by decide), k118 a1 (by decide), k117 a1 (by decide), q16_11]; exact (load_frame fpro (sXF.symm.subR (c := 32) (l := 4) (by decide))).trans hX8)
  have f132 : reg n132 a3 = X8 := u132.newReg (by decide)
  have k132 := u132.oldReg u131.self.zero
  have q32_2 : reg n132 sp = F := by rw [k132 sp (by decide), k131 sp (by decide), k130 sp (by decide), k129 sp (by decide), k128 sp (by decide), k127 sp (by decide), k126 sp (by decide), k125 sp (by decide), k124 sp (by decide), k123 sp (by decide), k122 sp (by decide), k121 sp (by decide), k120 sp (by decide), k119 sp (by decide), k118 sp (by decide), k117 sp (by decide), q16_2]
  have q32_5 : reg n132 (5 : Fin 32) = X6 := by rw [k132 (5 : Fin 32) (by decide), k131 (5 : Fin 32) (by decide), k130 (5 : Fin 32) (by decide), k129 (5 : Fin 32) (by decide), k128 (5 : Fin 32) (by decide), k127 (5 : Fin 32) (by decide), k126 (5 : Fin 32) (by decide), k125 (5 : Fin 32) (by decide), k124 (5 : Fin 32) (by decide), k123 (5 : Fin 32) (by decide), k122 (5 : Fin 32) (by decide), k121 (5 : Fin 32) (by decide), k120 (5 : Fin 32) (by decide), k119 (5 : Fin 32) (by decide), k118 (5 : Fin 32) (by decide), k117 (5 : Fin 32) (by decide), q16_5]
  have q32_6 : reg n132 (6 : Fin 32) = X7 := by rw [k132 (6 : Fin 32) (by decide), k131 (6 : Fin 32) (by decide), k130 (6 : Fin 32) (by decide), k129 (6 : Fin 32) (by decide), k128 (6 : Fin 32) (by decide), k127 (6 : Fin 32) (by decide), k126 (6 : Fin 32) (by decide), k125 (6 : Fin 32) (by decide), k124 (6 : Fin 32) (by decide), k123 (6 : Fin 32) (by decide), k122 (6 : Fin 32) (by decide), k121 (6 : Fin 32) (by decide), k120 (6 : Fin 32) (by decide), k119 (6 : Fin 32) (by decide), k118 (6 : Fin 32) (by decide), k117 (6 : Fin 32) (by decide), q16_6]
  have q32_7 : reg n132 (7 : Fin 32) = ((X3 + (0x20000000 + 0xFFFFFFF0)) - Y3) := by rw [k132 (7 : Fin 32) (by decide), k131 (7 : Fin 32) (by decide), k130 (7 : Fin 32) (by decide), k129 (7 : Fin 32) (by decide), k128 (7 : Fin 32) (by decide), k127 (7 : Fin 32) (by decide), f126]
  have q32_8 : reg n132 (8 : Fin 32) = out := by rw [k132 (8 : Fin 32) (by decide), k131 (8 : Fin 32) (by decide), k130 (8 : Fin 32) (by decide), k129 (8 : Fin 32) (by decide), k128 (8 : Fin 32) (by decide), k127 (8 : Fin 32) (by decide), k126 (8 : Fin 32) (by decide), k125 (8 : Fin 32) (by decide), k124 (8 : Fin 32) (by decide), k123 (8 : Fin 32) (by decide), k122 (8 : Fin 32) (by decide), k121 (8 : Fin 32) (by decide), k120 (8 : Fin 32) (by decide), k119 (8 : Fin 32) (by decide), k118 (8 : Fin 32) (by decide), k117 (8 : Fin 32) (by decide), q16_8]
  have q32_9 : reg n132 (9 : Fin 32) = Y5 := by rw [k132 (9 : Fin 32) (by decide), k131 (9 : Fin 32) (by decide), k130 (9 : Fin 32) (by decide), k129 (9 : Fin 32) (by decide), f128]
  have q32_10 : reg n132 a0 = Y7 := by rw [k132 a0 (by decide), k131 a0 (by decide), f130]
  have q32_11 : reg n132 a1 = xp := by rw [k132 a1 (by decide), k131 a1 (by decide), k130 a1 (by decide), k129 a1 (by decide), k128 a1 (by decide), k127 a1 (by decide), k126 a1 (by decide), k125 a1 (by decide), k124 a1 (by decide), k123 a1 (by decide), k122 a1 (by decide), k121 a1 (by decide), k120 a1 (by decide), k119 a1 (by decide), k118 a1 (by decide), k117 a1 (by decide), q16_11]
  have q32_12 : reg n132 a2 = yp := by rw [k132 a2 (by decide), k131 a2 (by decide), k130 a2 (by decide), k129 a2 (by decide), k128 a2 (by decide), k127 a2 (by decide), k126 a2 (by decide), k125 a2 (by decide), k124 a2 (by decide), k123 a2 (by decide), k122 a2 (by decide), k121 a2 (by decide), k120 a2 (by decide), k119 a2 (by decide), k118 a2 (by decide), k117 a2 (by decide), q16_12]
  have q32_14 : reg n132 a4 = (0x40000000 + 0xFFFFFFF0) := by rw [k132 a4 (by decide), k131 a4 (by decide), k130 a4 (by decide), k129 a4 (by decide), k128 a4 (by decide), k127 a4 (by decide), k126 a4 (by decide), k125 a4 (by decide), k124 a4 (by decide), k123 a4 (by decide), k122 a4 (by decide), k121 a4 (by decide), k120 a4 (by decide), k119 a4 (by decide), k118 a4 (by decide), k117 a4 (by decide), q16_14]
  have q32_15 : reg n132 a5 = Y6 := by rw [k132 a5 (by decide), k131 a5 (by decide), k130 a5 (by decide), f129]
  have q32_16 : reg n132 a6 = ((X4 + (0x40000000 + 0xFFFFFFF0)) - Y4) := by rw [k132 a6 (by decide), f131]
  have q32_17 : reg n132 a7 = X5 := by rw [k132 a7 (by decide), k131 a7 (by decide), k130 a7 (by decide), k129 a7 (by decide), k128 a7 (by decide), k127 a7 (by decide), k126 a7 (by decide), k125 a7 (by decide), k124 a7 (by decide), k123 a7 (by decide), k122 a7 (by decide), k121 a7 (by decide), k120 a7 (by decide), k119 a7 (by decide), k118 a7 (by decide), k117 a7 (by decide), q16_17]
  have q32_18 : reg n132 (18 : Fin 32) = ((X0 + (0x40000000 + 0xFFFFFFF0)) - Y0) := by rw [k132 (18 : Fin 32) (by decide), k131 (18 : Fin 32) (by decide), k130 (18 : Fin 32) (by decide), k129 (18 : Fin 32) (by decide), k128 (18 : Fin 32) (by decide), k127 (18 : Fin 32) (by decide), k126 (18 : Fin 32) (by decide), k125 (18 : Fin 32) (by decide), k124 (18 : Fin 32) (by decide), k123 (18 : Fin 32) (by decide), k122 (18 : Fin 32) (by decide), k121 (18 : Fin 32) (by decide), k120 (18 : Fin 32) (by decide), f119]
  have q32_28 : reg n132 (28 : Fin 32) = (X3 + (0x20000000 + 0xFFFFFFF0)) := by rw [k132 (28 : Fin 32) (by decide), k131 (28 : Fin 32) (by decide), k130 (28 : Fin 32) (by decide), k129 (28 : Fin 32) (by decide), k128 (28 : Fin 32) (by decide), k127 (28 : Fin 32) (by decide), k126 (28 : Fin 32) (by decide), k125 (28 : Fin 32) (by decide), k124 (28 : Fin 32) (by decide), f123]
  have q32_29 : reg n132 (29 : Fin 32) = (0x20000000 + 0xFFFFFFF0) := by rw [k132 (29 : Fin 32) (by decide), k131 (29 : Fin 32) (by decide), k130 (29 : Fin 32) (by decide), k129 (29 : Fin 32) (by decide), k128 (29 : Fin 32) (by decide), k127 (29 : Fin 32) (by decide), k126 (29 : Fin 32) (by decide), k125 (29 : Fin 32) (by decide), k124 (29 : Fin 32) (by decide), k123 (29 : Fin 32) (by decide), k122 (29 : Fin 32) (by decide), k121 (29 : Fin 32) (by decide), k120 (29 : Fin 32) (by decide), k119 (29 : Fin 32) (by decide), k118 (29 : Fin 32) (by decide), k117 (29 : Fin 32) (by decide), f116]
  have q32_30 : reg n132 (30 : Fin 32) = ((X1 + (0x20000000 + 0xFFFFFFF0)) - Y1) := by rw [k132 (30 : Fin 32) (by decide), k131 (30 : Fin 32) (by decide), k130 (30 : Fin 32) (by decide), k129 (30 : Fin 32) (by decide), k128 (30 : Fin 32) (by decide), k127 (30 : Fin 32) (by decide), k126 (30 : Fin 32) (by decide), k125 (30 : Fin 32) (by decide), k124 (30 : Fin 32) (by decide), k123 (30 : Fin 32) (by decide), k122 (30 : Fin 32) (by decide), f121]
  have q32_31 : reg n132 (31 : Fin 32) = ((X2 + (0x40000000 + 0xFFFFFFF0)) - Y2) := by rw [k132 (31 : Fin 32) (by decide), k131 (31 : Fin 32) (by decide), k130 (31 : Fin 32) (by decide), k129 (31 : Fin 32) (by decide), k128 (31 : Fin 32) (by decide), k127 (31 : Fin 32) (by decide), k126 (31 : Fin 32) (by decide), f125]
  obtain ⟨n133, d133, u133⟩ := u132.self.lwE hcp3 fsb_at_68 (off' := 0x6A) (by decide)
    (by rw [q32_11]; exact fr_al' env.hx (by decide)) (v := X9)
    (by rw [q32_11]; exact (load_frame fpro (sXF.symm.subR (c := 36) (l := 4) (by decide))).trans hX9)
  have f133 : reg n133 a1 = X9 := u133.newReg (by decide)
  have k133 := u133.oldReg u132.self.zero
  obtain ⟨n134, d134, u134⟩ := u133.self.alu hcp3 fsb_at_6a (off' := 0x6C) (by decide)
  have f134 : reg n134 a7 = (X5 + (0x20000000 + 0xFFFFFFF0)) := by
    rw [u134.newReg (by decide)]; show reg n133 a7 + reg n133 (29 : Fin 32) = _
    rw [k133 a7 (by decide), q32_17, k133 (29 : Fin 32) (by decide), q32_29]
  have k134 := u134.oldReg u133.self.zero
  obtain ⟨n135, d135, u135⟩ := u134.self.alu hcp3 fsb_at_6c (off' := 0x70) (by decide)
  have f135 : reg n135 a7 = ((X5 + (0x20000000 + 0xFFFFFFF0)) - Y5) := by
    rw [u135.newReg (by decide)]; show reg n134 a7 - reg n134 (9 : Fin 32) = _
    rw [f134, k134 (9 : Fin 32) (by decide), k133 (9 : Fin 32) (by decide), q32_9]
  have k135 := u135.oldReg u134.self.zero
  obtain ⟨n136, d136, u136⟩ := u135.self.alu hcp3 fsb_at_70 (off' := 0x72) (by decide)
  have f136 : reg n136 (5 : Fin 32) = (X6 + (0x40000000 + 0xFFFFFFF0)) := by
    rw [u136.newReg (by decide)]; show reg n135 (5 : Fin 32) + reg n135 a4 = _
    rw [k135 (5 : Fin 32) (by decide), k134 (5 : Fin 32) (by decide), k133 (5 : Fin 32) (by decide), q32_5, k135 a4 (by decide), k134 a4 (by decide), k133 a4 (by decide), q32_14]
  have k136 := u136.oldReg u135.self.zero
  obtain ⟨n137, d137, u137⟩ := u136.self.lwE hcp3 fsb_at_72 (off' := 0x74) (by decide)
    (by rw [k136 a2 (by decide), k135 a2 (by decide), k134 a2 (by decide), k133 a2 (by decide), q32_12]; exact fr_al' env.hy (by decide)) (v := Y8)
    (by rw [k136 a2 (by decide), k135 a2 (by decide), k134 a2 (by decide), k133 a2 (by decide), q32_12]; exact (load_frame fpro (sYF.symm.subR (c := 32) (l := 4) (by decide))).trans hY8)
  have f137 : reg n137 (9 : Fin 32) = Y8 := u137.newReg (by decide)
  have k137 := u137.oldReg u136.self.zero
  obtain ⟨n138, d138, u138⟩ := u137.self.lwE hcp3 fsb_at_74 (off' := 0x76) (by decide)
    (by rw [k137 a2 (by decide), k136 a2 (by decide), k135 a2 (by decide), k134 a2 (by decide), k133 a2 (by decide), q32_12]; exact fr_al' env.hy (by decide)) (v := Y9)
    (by rw [k137 a2 (by decide), k136 a2 (by decide), k135 a2 (by decide), k134 a2 (by decide), k133 a2 (by decide), q32_12]; exact (load_frame fpro (sYF.symm.subR (c := 36) (l := 4) (by decide))).trans hY9)
  have f138 : reg n138 a2 = Y9 := u138.newReg (by decide)
  have k138 := u138.oldReg u137.self.zero
  obtain ⟨n139, d139, u139⟩ := u138.self.alu hcp3 fsb_at_76 (off' := 0x7A) (by decide)
  have f139 : reg n139 a5 = ((X6 + (0x40000000 + 0xFFFFFFF0)) - Y6) := by
    rw [u139.newReg (by decide)]; show reg n138 (5 : Fin 32) - reg n138 a5 = _
    rw [k138 (5 : Fin 32) (by decide), k137 (5 : Fin 32) (by decide), f136, k138 a5 (by decide), k137 a5 (by decide), k136 a5 (by decide), k135 a5 (by decide), k134 a5 (by decide), k133 a5 (by decide), q32_15]
  have k139 := u139.oldReg u138.self.zero
  obtain ⟨n140, d140, u140⟩ := u139.self.alu hcp3 fsb_at_7a (off' := 0x7C) (by decide)
  have f140 : reg n140 (6 : Fin 32) = (X7 + (0x20000000 + 0xFFFFFFF0)) := by
    rw [u140.newReg (by decide)]; show reg n139 (6 : Fin 32) + reg n139 (29 : Fin 32) = _
    rw [k139 (6 : Fin 32) (by decide), k138 (6 : Fin 32) (by decide), k137 (6 : Fin 32) (by decide), k136 (6 : Fin 32) (by decide), k135 (6 : Fin 32) (by decide), k134 (6 : Fin 32) (by decide), k133 (6 : Fin 32) (by decide), q32_6, k139 (29 : Fin 32) (by decide), k138 (29 : Fin 32) (by decide), k137 (29 : Fin 32) (by decide), k136 (29 : Fin 32) (by decide), k135 (29 : Fin 32) (by decide), k134 (29 : Fin 32) (by decide), k133 (29 : Fin 32) (by decide), q32_29]
  have k140 := u140.oldReg u139.self.zero
  obtain ⟨n141, d141, u141⟩ := u140.self.alu hcp3 fsb_at_7c (off' := 0x80) (by decide)
  have f141 : reg n141 (5 : Fin 32) = ((X7 + (0x20000000 + 0xFFFFFFF0)) - Y7) := by
    rw [u141.newReg (by decide)]; show reg n140 (6 : Fin 32) - reg n140 a0 = _
    rw [f140, k140 a0 (by decide), k139 a0 (by decide), k138 a0 (by decide), k137 a0 (by decide), k136 a0 (by decide), k135 a0 (by decide), k134 a0 (by decide), k133 a0 (by decide), q32_10]
  have k141 := u141.oldReg u140.self.zero
  obtain ⟨n142, d142, u142⟩ := u141.self.aluImm hcp3 fsb_at_80 (off' := 0x84) (by decide)
  have f142 : reg n142 a0 = (((X0 + (0x40000000 + 0xFFFFFFF0)) - Y0) + 0xFFFFFEE0) := by
    rw [u142.newReg (by decide)]; show reg n141 (18 : Fin 32) + 0xFFFFFEE0 = _; rw [k141 (18 : Fin 32) (by decide), k140 (18 : Fin 32) (by decide), k139 (18 : Fin 32) (by decide), k138 (18 : Fin 32) (by decide), k137 (18 : Fin 32) (by decide), k136 (18 : Fin 32) (by decide), k135 (18 : Fin 32) (by decide), k134 (18 : Fin 32) (by decide), k133 (18 : Fin 32) (by decide), q32_18]
  have k142 := u142.oldReg u141.self.zero
  obtain ⟨n143, d143, u143⟩ := u142.self.alu hcp3 fsb_at_84 (off' := 0x86) (by decide)
  have f143 : reg n143 a3 = (X8 + (0x40000000 + 0xFFFFFFF0)) := by
    rw [u143.newReg (by decide)]; show reg n142 a3 + reg n142 a4 = _
    rw [k142 a3 (by decide), k141 a3 (by decide), k140 a3 (by decide), k139 a3 (by decide), k138 a3 (by decide), k137 a3 (by decide), k136 a3 (by decide), k135 a3 (by decide), k134 a3 (by decide), k133 a3 (by decide), f132, k142 a4 (by decide), k141 a4 (by decide), k140 a4 (by decide), k139 a4 (by decide), k138 a4 (by decide), k137 a4 (by decide), k136 a4 (by decide), k135 a4 (by decide), k134 a4 (by decide), k133 a4 (by decide), q32_14]
  have k143 := u143.oldReg u142.self.zero
  obtain ⟨n144, d144, u144⟩ := u143.self.alu hcp3 fsb_at_86 (off' := 0x88) (by decide)
  have f144 : reg n144 a1 = (X9 + (0x20000000 + 0xFFFFFFF0)) := by
    rw [u144.newReg (by decide)]; show reg n143 a1 + reg n143 (29 : Fin 32) = _
    rw [k143 a1 (by decide), k142 a1 (by decide), k141 a1 (by decide), k140 a1 (by decide), k139 a1 (by decide), k138 a1 (by decide), k137 a1 (by decide), k136 a1 (by decide), k135 a1 (by decide), k134 a1 (by decide), f133, k143 (29 : Fin 32) (by decide), k142 (29 : Fin 32) (by decide), k141 (29 : Fin 32) (by decide), k140 (29 : Fin 32) (by decide), k139 (29 : Fin 32) (by decide), k138 (29 : Fin 32) (by decide), k137 (29 : Fin 32) (by decide), k136 (29 : Fin 32) (by decide), k135 (29 : Fin 32) (by decide), k134 (29 : Fin 32) (by decide), k133 (29 : Fin 32) (by decide), q32_29]
  have k144 := u144.oldReg u143.self.zero
  obtain ⟨n145, d145, u145⟩ := u144.self.alu hcp3 fsb_at_88 (off' := 0x8A) (by decide)
  have f145 : reg n145 a3 = ((X8 + (0x40000000 + 0xFFFFFFF0)) - Y8) := by
    rw [u145.newReg (by decide)]; show reg n144 a3 - reg n144 (9 : Fin 32) = _
    rw [k144 a3 (by decide), f143, k144 (9 : Fin 32) (by decide), k143 (9 : Fin 32) (by decide), k142 (9 : Fin 32) (by decide), k141 (9 : Fin 32) (by decide), k140 (9 : Fin 32) (by decide), k139 (9 : Fin 32) (by decide), k138 (9 : Fin 32) (by decide), f137]
  have k145 := u145.oldReg u144.self.zero
  obtain ⟨n146, d146, u146⟩ := u145.self.alu hcp3 fsb_at_8a (off' := 0x8C) (by decide)
  have f146 : reg n146 a1 = ((X9 + (0x20000000 + 0xFFFFFFF0)) - Y9) := by
    rw [u146.newReg (by decide)]; show reg n145 a1 - reg n145 a2 = _
    rw [k145 a1 (by decide), f144, k145 a2 (by decide), k144 a2 (by decide), k143 a2 (by decide), k142 a2 (by decide), k141 a2 (by decide), k140 a2 (by decide), k139 a2 (by decide), f138]
  have k146 := u146.oldReg u145.self.zero
  obtain ⟨n147, d147, u147⟩ := u146.self.swG hcp3 fsb_at_8c (off' := 0x8E) (by decide)
    (by rw [k146 sp (by decide), k145 sp (by decide), k144 sp (by decide), k143 sp (by decide), k142 sp (by decide), k141 sp (by decide), k140 sp (by decide), k139 sp (by decide), k138 sp (by decide), k137 sp (by decide), k136 sp (by decide), k135 sp (by decide), k134 sp (by decide), k133 sp (by decide), q32_2]; exact fr_al' hFa (by decide)) (a := F + 0x30) (v := (((X0 + (0x40000000 + 0xFFFFFFF0)) - Y0) + 0xFFFFFEE0))
    (by rw [k146 sp (by decide), k145 sp (by decide), k144 sp (by decide), k143 sp (by decide), k142 sp (by decide), k141 sp (by decide), k140 sp (by decide), k139 sp (by decide), k138 sp (by decide), k137 sp (by decide), k136 sp (by decide), k135 sp (by decide), k134 sp (by decide), k133 sp (by decide), q32_2]) (by rw [k146 a0 (by decide), k145 a0 (by decide), k144 a0 (by decide), k143 a0 (by decide), f142])
  obtain ⟨B147, hB147⟩ : ∃ M', memStore32 P3 (F + 0x30) ((((X0 + (0x40000000 + 0xFFFFFFF0)) - Y0) + 0xFFFFFEE0)) = M' := ⟨_, rfl⟩
  rw [hB147] at u147
  have hc147 : CodeIn B147 P feSubCode := by rw [← hB147]; exact hcp3.store32 (frm_sep' sFC (by decide))
  obtain ⟨n148, d148, u148⟩ := u147.self.swG hc147 fsb_at_8e (off' := 0x90) (by decide)
    (by rw [u147.regs sp, k146 sp (by decide), k145 sp (by decide), k144 sp (by decide), k143 sp (by decide), k142 sp (by decide), k141 sp (by decide), k140 sp (by decide), k139 sp (by decide), k138 sp (by decide), k137 sp (by decide), k136 sp (by decide), k135 sp (by decide), k134 sp (by decide), k133 sp (by decide), q32_2]; exact fr_al' hFa (by decide)) (a := F + 0x34) (v := 0)
    (by rw [u147.regs sp, k146 sp (by decide), k145 sp (by decide), k144 sp (by decide), k143 sp (by decide), k142 sp (by decide), k141 sp (by decide), k140 sp (by decide), k139 sp (by decide), k138 sp (by decide), k137 sp (by decide), k136 sp (by decide), k135 sp (by decide), k134 sp (by decide), k133 sp (by decide), q32_2]) (u147.self.zero)
  obtain ⟨B148, hB148⟩ : ∃ M', memStore32 B147 (F + 0x34) (0) = M' := ⟨_, rfl⟩
  rw [hB148] at u148
  have hc148 : CodeIn B148 P feSubCode := by rw [← hB148]; exact hc147.store32 (frm_sep' sFC (by decide))
  have q48_2 : reg n148 sp = F := by rw [u148.regs sp, u147.regs sp, k146 sp (by decide), k145 sp (by decide), k144 sp (by decide), k143 sp (by decide), k142 sp (by decide), k141 sp (by decide), k140 sp (by decide), k139 sp (by decide), k138 sp (by decide), k137 sp (by decide), k136 sp (by decide), k135 sp (by decide), k134 sp (by decide), k133 sp (by decide), q32_2]
  have q48_5 : reg n148 (5 : Fin 32) = ((X7 + (0x20000000 + 0xFFFFFFF0)) - Y7) := by rw [u148.regs (5 : Fin 32), u147.regs (5 : Fin 32), k146 (5 : Fin 32) (by decide), k145 (5 : Fin 32) (by decide), k144 (5 : Fin 32) (by decide), k143 (5 : Fin 32) (by decide), k142 (5 : Fin 32) (by decide), f141]
  have q48_6 : reg n148 (6 : Fin 32) = (X7 + (0x20000000 + 0xFFFFFFF0)) := by rw [u148.regs (6 : Fin 32), u147.regs (6 : Fin 32), k146 (6 : Fin 32) (by decide), k145 (6 : Fin 32) (by decide), k144 (6 : Fin 32) (by decide), k143 (6 : Fin 32) (by decide), k142 (6 : Fin 32) (by decide), k141 (6 : Fin 32) (by decide), f140]
  have q48_7 : reg n148 (7 : Fin 32) = ((X3 + (0x20000000 + 0xFFFFFFF0)) - Y3) := by rw [u148.regs (7 : Fin 32), u147.regs (7 : Fin 32), k146 (7 : Fin 32) (by decide), k145 (7 : Fin 32) (by decide), k144 (7 : Fin 32) (by decide), k143 (7 : Fin 32) (by decide), k142 (7 : Fin 32) (by decide), k141 (7 : Fin 32) (by decide), k140 (7 : Fin 32) (by decide), k139 (7 : Fin 32) (by decide), k138 (7 : Fin 32) (by decide), k137 (7 : Fin 32) (by decide), k136 (7 : Fin 32) (by decide), k135 (7 : Fin 32) (by decide), k134 (7 : Fin 32) (by decide), k133 (7 : Fin 32) (by decide), q32_7]
  have q48_8 : reg n148 (8 : Fin 32) = out := by rw [u148.regs (8 : Fin 32), u147.regs (8 : Fin 32), k146 (8 : Fin 32) (by decide), k145 (8 : Fin 32) (by decide), k144 (8 : Fin 32) (by decide), k143 (8 : Fin 32) (by decide), k142 (8 : Fin 32) (by decide), k141 (8 : Fin 32) (by decide), k140 (8 : Fin 32) (by decide), k139 (8 : Fin 32) (by decide), k138 (8 : Fin 32) (by decide), k137 (8 : Fin 32) (by decide), k136 (8 : Fin 32) (by decide), k135 (8 : Fin 32) (by decide), k134 (8 : Fin 32) (by decide), k133 (8 : Fin 32) (by decide), q32_8]
  have q48_9 : reg n148 (9 : Fin 32) = Y8 := by rw [u148.regs (9 : Fin 32), u147.regs (9 : Fin 32), k146 (9 : Fin 32) (by decide), k145 (9 : Fin 32) (by decide), k144 (9 : Fin 32) (by decide), k143 (9 : Fin 32) (by decide), k142 (9 : Fin 32) (by decide), k141 (9 : Fin 32) (by decide), k140 (9 : Fin 32) (by decide), k139 (9 : Fin 32) (by decide), k138 (9 : Fin 32) (by decide), f137]
  have q48_10 : reg n148 a0 = (((X0 + (0x40000000 + 0xFFFFFFF0)) - Y0) + 0xFFFFFEE0) := by rw [u148.regs a0, u147.regs a0, k146 a0 (by decide), k145 a0 (by decide), k144 a0 (by decide), k143 a0 (by decide), f142]
  have q48_11 : reg n148 a1 = ((X9 + (0x20000000 + 0xFFFFFFF0)) - Y9) := by rw [u148.regs a1, u147.regs a1, f146]
  have q48_12 : reg n148 a2 = Y9 := by rw [u148.regs a2, u147.regs a2, k146 a2 (by decide), k145 a2 (by decide), k144 a2 (by decide), k143 a2 (by decide), k142 a2 (by decide), k141 a2 (by decide), k140 a2 (by decide), k139 a2 (by decide), f138]
  have q48_13 : reg n148 a3 = ((X8 + (0x40000000 + 0xFFFFFFF0)) - Y8) := by rw [u148.regs a3, u147.regs a3, k146 a3 (by decide), f145]
  have q48_14 : reg n148 a4 = (0x40000000 + 0xFFFFFFF0) := by rw [u148.regs a4, u147.regs a4, k146 a4 (by decide), k145 a4 (by decide), k144 a4 (by decide), k143 a4 (by decide), k142 a4 (by decide), k141 a4 (by decide), k140 a4 (by decide), k139 a4 (by decide), k138 a4 (by decide), k137 a4 (by decide), k136 a4 (by decide), k135 a4 (by decide), k134 a4 (by decide), k133 a4 (by decide), q32_14]
  have q48_15 : reg n148 a5 = ((X6 + (0x40000000 + 0xFFFFFFF0)) - Y6) := by rw [u148.regs a5, u147.regs a5, k146 a5 (by decide), k145 a5 (by decide), k144 a5 (by decide), k143 a5 (by decide), k142 a5 (by decide), k141 a5 (by decide), k140 a5 (by decide), f139]
  have q48_16 : reg n148 a6 = ((X4 + (0x40000000 + 0xFFFFFFF0)) - Y4) := by rw [u148.regs a6, u147.regs a6, k146 a6 (by decide), k145 a6 (by decide), k144 a6 (by decide), k143 a6 (by decide), k142 a6 (by decide), k141 a6 (by decide), k140 a6 (by decide), k139 a6 (by decide), k138 a6 (by decide), k137 a6 (by decide), k136 a6 (by decide), k135 a6 (by decide), k134 a6 (by decide), k133 a6 (by decide), q32_16]
  have q48_17 : reg n148 a7 = ((X5 + (0x20000000 + 0xFFFFFFF0)) - Y5) := by rw [u148.regs a7, u147.regs a7, k146 a7 (by decide), k145 a7 (by decide), k144 a7 (by decide), k143 a7 (by decide), k142 a7 (by decide), k141 a7 (by decide), k140 a7 (by decide), k139 a7 (by decide), k138 a7 (by decide), k137 a7 (by decide), k136 a7 (by decide), f135]
  have q48_18 : reg n148 (18 : Fin 32) = ((X0 + (0x40000000 + 0xFFFFFFF0)) - Y0) := by rw [u148.regs (18 : Fin 32), u147.regs (18 : Fin 32), k146 (18 : Fin 32) (by decide), k145 (18 : Fin 32) (by decide), k144 (18 : Fin 32) (by decide), k143 (18 : Fin 32) (by decide), k142 (18 : Fin 32) (by decide), k141 (18 : Fin 32) (by decide), k140 (18 : Fin 32) (by decide), k139 (18 : Fin 32) (by decide), k138 (18 : Fin 32) (by decide), k137 (18 : Fin 32) (by decide), k136 (18 : Fin 32) (by decide), k135 (18 : Fin 32) (by decide), k134 (18 : Fin 32) (by decide), k133 (18 : Fin 32) (by decide), q32_18]
  have q48_28 : reg n148 (28 : Fin 32) = (X3 + (0x20000000 + 0xFFFFFFF0)) := by rw [u148.regs (28 : Fin 32), u147.regs (28 : Fin 32), k146 (28 : Fin 32) (by decide), k145 (28 : Fin 32) (by decide), k144 (28 : Fin 32) (by decide), k143 (28 : Fin 32) (by decide), k142 (28 : Fin 32) (by decide), k141 (28 : Fin 32) (by decide), k140 (28 : Fin 32) (by decide), k139 (28 : Fin 32) (by decide), k138 (28 : Fin 32) (by decide), k137 (28 : Fin 32) (by decide), k136 (28 : Fin 32) (by decide), k135 (28 : Fin 32) (by decide), k134 (28 : Fin 32) (by decide), k133 (28 : Fin 32) (by decide), q32_28]
  have q48_29 : reg n148 (29 : Fin 32) = (0x20000000 + 0xFFFFFFF0) := by rw [u148.regs (29 : Fin 32), u147.regs (29 : Fin 32), k146 (29 : Fin 32) (by decide), k145 (29 : Fin 32) (by decide), k144 (29 : Fin 32) (by decide), k143 (29 : Fin 32) (by decide), k142 (29 : Fin 32) (by decide), k141 (29 : Fin 32) (by decide), k140 (29 : Fin 32) (by decide), k139 (29 : Fin 32) (by decide), k138 (29 : Fin 32) (by decide), k137 (29 : Fin 32) (by decide), k136 (29 : Fin 32) (by decide), k135 (29 : Fin 32) (by decide), k134 (29 : Fin 32) (by decide), k133 (29 : Fin 32) (by decide), q32_29]
  have q48_30 : reg n148 (30 : Fin 32) = ((X1 + (0x20000000 + 0xFFFFFFF0)) - Y1) := by rw [u148.regs (30 : Fin 32), u147.regs (30 : Fin 32), k146 (30 : Fin 32) (by decide), k145 (30 : Fin 32) (by decide), k144 (30 : Fin 32) (by decide), k143 (30 : Fin 32) (by decide), k142 (30 : Fin 32) (by decide), k141 (30 : Fin 32) (by decide), k140 (30 : Fin 32) (by decide), k139 (30 : Fin 32) (by decide), k138 (30 : Fin 32) (by decide), k137 (30 : Fin 32) (by decide), k136 (30 : Fin 32) (by decide), k135 (30 : Fin 32) (by decide), k134 (30 : Fin 32) (by decide), k133 (30 : Fin 32) (by decide), q32_30]
  have q48_31 : reg n148 (31 : Fin 32) = ((X2 + (0x40000000 + 0xFFFFFFF0)) - Y2) := by rw [u148.regs (31 : Fin 32), u147.regs (31 : Fin 32), k146 (31 : Fin 32) (by decide), k145 (31 : Fin 32) (by decide), k144 (31 : Fin 32) (by decide), k143 (31 : Fin 32) (by decide), k142 (31 : Fin 32) (by decide), k141 (31 : Fin 32) (by decide), k140 (31 : Fin 32) (by decide), k139 (31 : Fin 32) (by decide), k138 (31 : Fin 32) (by decide), k137 (31 : Fin 32) (by decide), k136 (31 : Fin 32) (by decide), k135 (31 : Fin 32) (by decide), k134 (31 : Fin 32) (by decide), k133 (31 : Fin 32) (by decide), q32_31]
  obtain ⟨n149, d149, u149⟩ := u148.self.swG hc148 fsb_at_90 (off' := 0x92) (by decide)
    (by rw [q48_2]; exact fr_al' hFa (by decide)) (a := F + 0x38) (v := ((X1 + (0x20000000 + 0xFFFFFFF0)) - Y1))
    (by rw [q48_2]) (by rw [q48_30])
  obtain ⟨B149, hB149⟩ : ∃ M', memStore32 B148 (F + 0x38) (((X1 + (0x20000000 + 0xFFFFFFF0)) - Y1)) = M' := ⟨_, rfl⟩
  rw [hB149] at u149
  have hc149 : CodeIn B149 P feSubCode := by rw [← hB149]; exact hc148.store32 (frm_sep' sFC (by decide))
  obtain ⟨n150, d150, u150⟩ := u149.self.swG hc149 fsb_at_92 (off' := 0x94) (by decide)
    (by rw [u149.regs sp, q48_2]; exact fr_al' hFa (by decide)) (a := F + 0x3C) (v := 0)
    (by rw [u149.regs sp, q48_2]) (u149.self.zero)
  obtain ⟨B150, hB150⟩ : ∃ M', memStore32 B149 (F + 0x3C) (0) = M' := ⟨_, rfl⟩
  rw [hB150] at u150
  have hc150 : CodeIn B150 P feSubCode := by rw [← hB150]; exact hc149.store32 (frm_sep' sFC (by decide))
  obtain ⟨n151, d151, u151⟩ := u150.self.swG hc150 fsb_at_94 (off' := 0x96) (by decide)
    (by rw [u150.regs sp, u149.regs sp, q48_2]; exact fr_al' hFa (by decide)) (a := F + 0x40) (v := ((X2 + (0x40000000 + 0xFFFFFFF0)) - Y2))
    (by rw [u150.regs sp, u149.regs sp, q48_2]) (by rw [u150.regs (31 : Fin 32), u149.regs (31 : Fin 32), q48_31])
  obtain ⟨B151, hB151⟩ : ∃ M', memStore32 B150 (F + 0x40) (((X2 + (0x40000000 + 0xFFFFFFF0)) - Y2)) = M' := ⟨_, rfl⟩
  rw [hB151] at u151
  have hc151 : CodeIn B151 P feSubCode := by rw [← hB151]; exact hc150.store32 (frm_sep' sFC (by decide))
  obtain ⟨n152, d152, u152⟩ := u151.self.swG hc151 fsb_at_96 (off' := 0x98) (by decide)
    (by rw [u151.regs sp, u150.regs sp, u149.regs sp, q48_2]; exact fr_al' hFa (by decide)) (a := F + 0x44) (v := 0)
    (by rw [u151.regs sp, u150.regs sp, u149.regs sp, q48_2]) (u151.self.zero)
  obtain ⟨B152, hB152⟩ : ∃ M', memStore32 B151 (F + 0x44) (0) = M' := ⟨_, rfl⟩
  rw [hB152] at u152
  have hc152 : CodeIn B152 P feSubCode := by rw [← hB152]; exact hc151.store32 (frm_sep' sFC (by decide))
  obtain ⟨n153, d153, u153⟩ := u152.self.swG hc152 fsb_at_98 (off' := 0x9A) (by decide)
    (by rw [u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]; exact fr_al' hFa (by decide)) (a := F + 0x48) (v := ((X3 + (0x20000000 + 0xFFFFFFF0)) - Y3))
    (by rw [u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]) (by rw [u152.regs (7 : Fin 32), u151.regs (7 : Fin 32), u150.regs (7 : Fin 32), u149.regs (7 : Fin 32), q48_7])
  obtain ⟨B153, hB153⟩ : ∃ M', memStore32 B152 (F + 0x48) (((X3 + (0x20000000 + 0xFFFFFFF0)) - Y3)) = M' := ⟨_, rfl⟩
  rw [hB153] at u153
  have hc153 : CodeIn B153 P feSubCode := by rw [← hB153]; exact hc152.store32 (frm_sep' sFC (by decide))
  obtain ⟨n154, d154, u154⟩ := u153.self.swG hc153 fsb_at_9a (off' := 0x9C) (by decide)
    (by rw [u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]; exact fr_al' hFa (by decide)) (a := F + 0x4C) (v := 0)
    (by rw [u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]) (u153.self.zero)
  obtain ⟨B154, hB154⟩ : ∃ M', memStore32 B153 (F + 0x4C) (0) = M' := ⟨_, rfl⟩
  rw [hB154] at u154
  have hc154 : CodeIn B154 P feSubCode := by rw [← hB154]; exact hc153.store32 (frm_sep' sFC (by decide))
  obtain ⟨n155, d155, u155⟩ := u154.self.swG hc154 fsb_at_9c (off' := 0x9E) (by decide)
    (by rw [u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]; exact fr_al' hFa (by decide)) (a := F + 0x50) (v := ((X4 + (0x40000000 + 0xFFFFFFF0)) - Y4))
    (by rw [u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]) (by rw [u154.regs a6, u153.regs a6, u152.regs a6, u151.regs a6, u150.regs a6, u149.regs a6, q48_16])
  obtain ⟨B155, hB155⟩ : ∃ M', memStore32 B154 (F + 0x50) (((X4 + (0x40000000 + 0xFFFFFFF0)) - Y4)) = M' := ⟨_, rfl⟩
  rw [hB155] at u155
  have hc155 : CodeIn B155 P feSubCode := by rw [← hB155]; exact hc154.store32 (frm_sep' sFC (by decide))
  obtain ⟨n156, d156, u156⟩ := u155.self.swG hc155 fsb_at_9e (off' := 0xA0) (by decide)
    (by rw [u155.regs sp, u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]; exact fr_al' hFa (by decide)) (a := F + 0x54) (v := 0)
    (by rw [u155.regs sp, u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]) (u155.self.zero)
  obtain ⟨B156, hB156⟩ : ∃ M', memStore32 B155 (F + 0x54) (0) = M' := ⟨_, rfl⟩
  rw [hB156] at u156
  have hc156 : CodeIn B156 P feSubCode := by rw [← hB156]; exact hc155.store32 (frm_sep' sFC (by decide))
  obtain ⟨n157, d157, u157⟩ := u156.self.swG hc156 fsb_at_a0 (off' := 0xA2) (by decide)
    (by rw [u156.regs sp, u155.regs sp, u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]; exact fr_al' hFa (by decide)) (a := F + 0x58) (v := ((X5 + (0x20000000 + 0xFFFFFFF0)) - Y5))
    (by rw [u156.regs sp, u155.regs sp, u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]) (by rw [u156.regs a7, u155.regs a7, u154.regs a7, u153.regs a7, u152.regs a7, u151.regs a7, u150.regs a7, u149.regs a7, q48_17])
  obtain ⟨B157, hB157⟩ : ∃ M', memStore32 B156 (F + 0x58) (((X5 + (0x20000000 + 0xFFFFFFF0)) - Y5)) = M' := ⟨_, rfl⟩
  rw [hB157] at u157
  have hc157 : CodeIn B157 P feSubCode := by rw [← hB157]; exact hc156.store32 (frm_sep' sFC (by decide))
  obtain ⟨n158, d158, u158⟩ := u157.self.swG hc157 fsb_at_a2 (off' := 0xA4) (by decide)
    (by rw [u157.regs sp, u156.regs sp, u155.regs sp, u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]; exact fr_al' hFa (by decide)) (a := F + 0x5C) (v := 0)
    (by rw [u157.regs sp, u156.regs sp, u155.regs sp, u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]) (u157.self.zero)
  obtain ⟨B158, hB158⟩ : ∃ M', memStore32 B157 (F + 0x5C) (0) = M' := ⟨_, rfl⟩
  rw [hB158] at u158
  have hc158 : CodeIn B158 P feSubCode := by rw [← hB158]; exact hc157.store32 (frm_sep' sFC (by decide))
  obtain ⟨n159, d159, u159⟩ := u158.self.swG hc158 fsb_at_a4 (off' := 0xA6) (by decide)
    (by rw [u158.regs sp, u157.regs sp, u156.regs sp, u155.regs sp, u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]; exact fr_al' hFa (by decide)) (a := F + 0x60) (v := ((X6 + (0x40000000 + 0xFFFFFFF0)) - Y6))
    (by rw [u158.regs sp, u157.regs sp, u156.regs sp, u155.regs sp, u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]) (by rw [u158.regs a5, u157.regs a5, u156.regs a5, u155.regs a5, u154.regs a5, u153.regs a5, u152.regs a5, u151.regs a5, u150.regs a5, u149.regs a5, q48_15])
  obtain ⟨B159, hB159⟩ : ∃ M', memStore32 B158 (F + 0x60) (((X6 + (0x40000000 + 0xFFFFFFF0)) - Y6)) = M' := ⟨_, rfl⟩
  rw [hB159] at u159
  have hc159 : CodeIn B159 P feSubCode := by rw [← hB159]; exact hc158.store32 (frm_sep' sFC (by decide))
  obtain ⟨n160, d160, u160⟩ := u159.self.swG hc159 fsb_at_a6 (off' := 0xA8) (by decide)
    (by rw [u159.regs sp, u158.regs sp, u157.regs sp, u156.regs sp, u155.regs sp, u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]; exact fr_al' hFa (by decide)) (a := F + 0x64) (v := 0)
    (by rw [u159.regs sp, u158.regs sp, u157.regs sp, u156.regs sp, u155.regs sp, u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]) (u159.self.zero)
  obtain ⟨B160, hB160⟩ : ∃ M', memStore32 B159 (F + 0x64) (0) = M' := ⟨_, rfl⟩
  rw [hB160] at u160
  have hc160 : CodeIn B160 P feSubCode := by rw [← hB160]; exact hc159.store32 (frm_sep' sFC (by decide))
  obtain ⟨n161, d161, u161⟩ := u160.self.swG hc160 fsb_at_a8 (off' := 0xAA) (by decide)
    (by rw [u160.regs sp, u159.regs sp, u158.regs sp, u157.regs sp, u156.regs sp, u155.regs sp, u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]; exact fr_al' hFa (by decide)) (a := F + 0x68) (v := ((X7 + (0x20000000 + 0xFFFFFFF0)) - Y7))
    (by rw [u160.regs sp, u159.regs sp, u158.regs sp, u157.regs sp, u156.regs sp, u155.regs sp, u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]) (by rw [u160.regs (5 : Fin 32), u159.regs (5 : Fin 32), u158.regs (5 : Fin 32), u157.regs (5 : Fin 32), u156.regs (5 : Fin 32), u155.regs (5 : Fin 32), u154.regs (5 : Fin 32), u153.regs (5 : Fin 32), u152.regs (5 : Fin 32), u151.regs (5 : Fin 32), u150.regs (5 : Fin 32), u149.regs (5 : Fin 32), q48_5])
  obtain ⟨B161, hB161⟩ : ∃ M', memStore32 B160 (F + 0x68) (((X7 + (0x20000000 + 0xFFFFFFF0)) - Y7)) = M' := ⟨_, rfl⟩
  rw [hB161] at u161
  have hc161 : CodeIn B161 P feSubCode := by rw [← hB161]; exact hc160.store32 (frm_sep' sFC (by decide))
  obtain ⟨n162, d162, u162⟩ := u161.self.swG hc161 fsb_at_aa (off' := 0xAC) (by decide)
    (by rw [u161.regs sp, u160.regs sp, u159.regs sp, u158.regs sp, u157.regs sp, u156.regs sp, u155.regs sp, u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]; exact fr_al' hFa (by decide)) (a := F + 0x6C) (v := 0)
    (by rw [u161.regs sp, u160.regs sp, u159.regs sp, u158.regs sp, u157.regs sp, u156.regs sp, u155.regs sp, u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]) (u161.self.zero)
  obtain ⟨B162, hB162⟩ : ∃ M', memStore32 B161 (F + 0x6C) (0) = M' := ⟨_, rfl⟩
  rw [hB162] at u162
  have hc162 : CodeIn B162 P feSubCode := by rw [← hB162]; exact hc161.store32 (frm_sep' sFC (by decide))
  obtain ⟨n163, d163, u163⟩ := u162.self.swG hc162 fsb_at_ac (off' := 0xAE) (by decide)
    (by rw [u162.regs sp, u161.regs sp, u160.regs sp, u159.regs sp, u158.regs sp, u157.regs sp, u156.regs sp, u155.regs sp, u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]; exact fr_al' hFa (by decide)) (a := F + 0x70) (v := ((X8 + (0x40000000 + 0xFFFFFFF0)) - Y8))
    (by rw [u162.regs sp, u161.regs sp, u160.regs sp, u159.regs sp, u158.regs sp, u157.regs sp, u156.regs sp, u155.regs sp, u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]) (by rw [u162.regs a3, u161.regs a3, u160.regs a3, u159.regs a3, u158.regs a3, u157.regs a3, u156.regs a3, u155.regs a3, u154.regs a3, u153.regs a3, u152.regs a3, u151.regs a3, u150.regs a3, u149.regs a3, q48_13])
  obtain ⟨B163, hB163⟩ : ∃ M', memStore32 B162 (F + 0x70) (((X8 + (0x40000000 + 0xFFFFFFF0)) - Y8)) = M' := ⟨_, rfl⟩
  rw [hB163] at u163
  have hc163 : CodeIn B163 P feSubCode := by rw [← hB163]; exact hc162.store32 (frm_sep' sFC (by decide))
  obtain ⟨n164, d164, u164⟩ := u163.self.swG hc163 fsb_at_ae (off' := 0xB0) (by decide)
    (by rw [u163.regs sp, u162.regs sp, u161.regs sp, u160.regs sp, u159.regs sp, u158.regs sp, u157.regs sp, u156.regs sp, u155.regs sp, u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]; exact fr_al' hFa (by decide)) (a := F + 0x74) (v := 0)
    (by rw [u163.regs sp, u162.regs sp, u161.regs sp, u160.regs sp, u159.regs sp, u158.regs sp, u157.regs sp, u156.regs sp, u155.regs sp, u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]) (u163.self.zero)
  obtain ⟨B164, hB164⟩ : ∃ M', memStore32 B163 (F + 0x74) (0) = M' := ⟨_, rfl⟩
  rw [hB164] at u164
  have hc164 : CodeIn B164 P feSubCode := by rw [← hB164]; exact hc163.store32 (frm_sep' sFC (by decide))
  have q64_2 : reg n164 sp = F := by rw [u164.regs sp, u163.regs sp, u162.regs sp, u161.regs sp, u160.regs sp, u159.regs sp, u158.regs sp, u157.regs sp, u156.regs sp, u155.regs sp, u154.regs sp, u153.regs sp, u152.regs sp, u151.regs sp, u150.regs sp, u149.regs sp, q48_2]
  have q64_5 : reg n164 (5 : Fin 32) = ((X7 + (0x20000000 + 0xFFFFFFF0)) - Y7) := by rw [u164.regs (5 : Fin 32), u163.regs (5 : Fin 32), u162.regs (5 : Fin 32), u161.regs (5 : Fin 32), u160.regs (5 : Fin 32), u159.regs (5 : Fin 32), u158.regs (5 : Fin 32), u157.regs (5 : Fin 32), u156.regs (5 : Fin 32), u155.regs (5 : Fin 32), u154.regs (5 : Fin 32), u153.regs (5 : Fin 32), u152.regs (5 : Fin 32), u151.regs (5 : Fin 32), u150.regs (5 : Fin 32), u149.regs (5 : Fin 32), q48_5]
  have q64_6 : reg n164 (6 : Fin 32) = (X7 + (0x20000000 + 0xFFFFFFF0)) := by rw [u164.regs (6 : Fin 32), u163.regs (6 : Fin 32), u162.regs (6 : Fin 32), u161.regs (6 : Fin 32), u160.regs (6 : Fin 32), u159.regs (6 : Fin 32), u158.regs (6 : Fin 32), u157.regs (6 : Fin 32), u156.regs (6 : Fin 32), u155.regs (6 : Fin 32), u154.regs (6 : Fin 32), u153.regs (6 : Fin 32), u152.regs (6 : Fin 32), u151.regs (6 : Fin 32), u150.regs (6 : Fin 32), u149.regs (6 : Fin 32), q48_6]
  have q64_7 : reg n164 (7 : Fin 32) = ((X3 + (0x20000000 + 0xFFFFFFF0)) - Y3) := by rw [u164.regs (7 : Fin 32), u163.regs (7 : Fin 32), u162.regs (7 : Fin 32), u161.regs (7 : Fin 32), u160.regs (7 : Fin 32), u159.regs (7 : Fin 32), u158.regs (7 : Fin 32), u157.regs (7 : Fin 32), u156.regs (7 : Fin 32), u155.regs (7 : Fin 32), u154.regs (7 : Fin 32), u153.regs (7 : Fin 32), u152.regs (7 : Fin 32), u151.regs (7 : Fin 32), u150.regs (7 : Fin 32), u149.regs (7 : Fin 32), q48_7]
  have q64_8 : reg n164 (8 : Fin 32) = out := by rw [u164.regs (8 : Fin 32), u163.regs (8 : Fin 32), u162.regs (8 : Fin 32), u161.regs (8 : Fin 32), u160.regs (8 : Fin 32), u159.regs (8 : Fin 32), u158.regs (8 : Fin 32), u157.regs (8 : Fin 32), u156.regs (8 : Fin 32), u155.regs (8 : Fin 32), u154.regs (8 : Fin 32), u153.regs (8 : Fin 32), u152.regs (8 : Fin 32), u151.regs (8 : Fin 32), u150.regs (8 : Fin 32), u149.regs (8 : Fin 32), q48_8]
  have q64_9 : reg n164 (9 : Fin 32) = Y8 := by rw [u164.regs (9 : Fin 32), u163.regs (9 : Fin 32), u162.regs (9 : Fin 32), u161.regs (9 : Fin 32), u160.regs (9 : Fin 32), u159.regs (9 : Fin 32), u158.regs (9 : Fin 32), u157.regs (9 : Fin 32), u156.regs (9 : Fin 32), u155.regs (9 : Fin 32), u154.regs (9 : Fin 32), u153.regs (9 : Fin 32), u152.regs (9 : Fin 32), u151.regs (9 : Fin 32), u150.regs (9 : Fin 32), u149.regs (9 : Fin 32), q48_9]
  have q64_10 : reg n164 a0 = (((X0 + (0x40000000 + 0xFFFFFFF0)) - Y0) + 0xFFFFFEE0) := by rw [u164.regs a0, u163.regs a0, u162.regs a0, u161.regs a0, u160.regs a0, u159.regs a0, u158.regs a0, u157.regs a0, u156.regs a0, u155.regs a0, u154.regs a0, u153.regs a0, u152.regs a0, u151.regs a0, u150.regs a0, u149.regs a0, q48_10]
  have q64_11 : reg n164 a1 = ((X9 + (0x20000000 + 0xFFFFFFF0)) - Y9) := by rw [u164.regs a1, u163.regs a1, u162.regs a1, u161.regs a1, u160.regs a1, u159.regs a1, u158.regs a1, u157.regs a1, u156.regs a1, u155.regs a1, u154.regs a1, u153.regs a1, u152.regs a1, u151.regs a1, u150.regs a1, u149.regs a1, q48_11]
  have q64_12 : reg n164 a2 = Y9 := by rw [u164.regs a2, u163.regs a2, u162.regs a2, u161.regs a2, u160.regs a2, u159.regs a2, u158.regs a2, u157.regs a2, u156.regs a2, u155.regs a2, u154.regs a2, u153.regs a2, u152.regs a2, u151.regs a2, u150.regs a2, u149.regs a2, q48_12]
  have q64_13 : reg n164 a3 = ((X8 + (0x40000000 + 0xFFFFFFF0)) - Y8) := by rw [u164.regs a3, u163.regs a3, u162.regs a3, u161.regs a3, u160.regs a3, u159.regs a3, u158.regs a3, u157.regs a3, u156.regs a3, u155.regs a3, u154.regs a3, u153.regs a3, u152.regs a3, u151.regs a3, u150.regs a3, u149.regs a3, q48_13]
  have q64_14 : reg n164 a4 = (0x40000000 + 0xFFFFFFF0) := by rw [u164.regs a4, u163.regs a4, u162.regs a4, u161.regs a4, u160.regs a4, u159.regs a4, u158.regs a4, u157.regs a4, u156.regs a4, u155.regs a4, u154.regs a4, u153.regs a4, u152.regs a4, u151.regs a4, u150.regs a4, u149.regs a4, q48_14]
  have q64_15 : reg n164 a5 = ((X6 + (0x40000000 + 0xFFFFFFF0)) - Y6) := by rw [u164.regs a5, u163.regs a5, u162.regs a5, u161.regs a5, u160.regs a5, u159.regs a5, u158.regs a5, u157.regs a5, u156.regs a5, u155.regs a5, u154.regs a5, u153.regs a5, u152.regs a5, u151.regs a5, u150.regs a5, u149.regs a5, q48_15]
  have q64_16 : reg n164 a6 = ((X4 + (0x40000000 + 0xFFFFFFF0)) - Y4) := by rw [u164.regs a6, u163.regs a6, u162.regs a6, u161.regs a6, u160.regs a6, u159.regs a6, u158.regs a6, u157.regs a6, u156.regs a6, u155.regs a6, u154.regs a6, u153.regs a6, u152.regs a6, u151.regs a6, u150.regs a6, u149.regs a6, q48_16]
  have q64_17 : reg n164 a7 = ((X5 + (0x20000000 + 0xFFFFFFF0)) - Y5) := by rw [u164.regs a7, u163.regs a7, u162.regs a7, u161.regs a7, u160.regs a7, u159.regs a7, u158.regs a7, u157.regs a7, u156.regs a7, u155.regs a7, u154.regs a7, u153.regs a7, u152.regs a7, u151.regs a7, u150.regs a7, u149.regs a7, q48_17]
  have q64_18 : reg n164 (18 : Fin 32) = ((X0 + (0x40000000 + 0xFFFFFFF0)) - Y0) := by rw [u164.regs (18 : Fin 32), u163.regs (18 : Fin 32), u162.regs (18 : Fin 32), u161.regs (18 : Fin 32), u160.regs (18 : Fin 32), u159.regs (18 : Fin 32), u158.regs (18 : Fin 32), u157.regs (18 : Fin 32), u156.regs (18 : Fin 32), u155.regs (18 : Fin 32), u154.regs (18 : Fin 32), u153.regs (18 : Fin 32), u152.regs (18 : Fin 32), u151.regs (18 : Fin 32), u150.regs (18 : Fin 32), u149.regs (18 : Fin 32), q48_18]
  have q64_28 : reg n164 (28 : Fin 32) = (X3 + (0x20000000 + 0xFFFFFFF0)) := by rw [u164.regs (28 : Fin 32), u163.regs (28 : Fin 32), u162.regs (28 : Fin 32), u161.regs (28 : Fin 32), u160.regs (28 : Fin 32), u159.regs (28 : Fin 32), u158.regs (28 : Fin 32), u157.regs (28 : Fin 32), u156.regs (28 : Fin 32), u155.regs (28 : Fin 32), u154.regs (28 : Fin 32), u153.regs (28 : Fin 32), u152.regs (28 : Fin 32), u151.regs (28 : Fin 32), u150.regs (28 : Fin 32), u149.regs (28 : Fin 32), q48_28]
  have q64_29 : reg n164 (29 : Fin 32) = (0x20000000 + 0xFFFFFFF0) := by rw [u164.regs (29 : Fin 32), u163.regs (29 : Fin 32), u162.regs (29 : Fin 32), u161.regs (29 : Fin 32), u160.regs (29 : Fin 32), u159.regs (29 : Fin 32), u158.regs (29 : Fin 32), u157.regs (29 : Fin 32), u156.regs (29 : Fin 32), u155.regs (29 : Fin 32), u154.regs (29 : Fin 32), u153.regs (29 : Fin 32), u152.regs (29 : Fin 32), u151.regs (29 : Fin 32), u150.regs (29 : Fin 32), u149.regs (29 : Fin 32), q48_29]
  have q64_30 : reg n164 (30 : Fin 32) = ((X1 + (0x20000000 + 0xFFFFFFF0)) - Y1) := by rw [u164.regs (30 : Fin 32), u163.regs (30 : Fin 32), u162.regs (30 : Fin 32), u161.regs (30 : Fin 32), u160.regs (30 : Fin 32), u159.regs (30 : Fin 32), u158.regs (30 : Fin 32), u157.regs (30 : Fin 32), u156.regs (30 : Fin 32), u155.regs (30 : Fin 32), u154.regs (30 : Fin 32), u153.regs (30 : Fin 32), u152.regs (30 : Fin 32), u151.regs (30 : Fin 32), u150.regs (30 : Fin 32), u149.regs (30 : Fin 32), q48_30]
  have q64_31 : reg n164 (31 : Fin 32) = ((X2 + (0x40000000 + 0xFFFFFFF0)) - Y2) := by rw [u164.regs (31 : Fin 32), u163.regs (31 : Fin 32), u162.regs (31 : Fin 32), u161.regs (31 : Fin 32), u160.regs (31 : Fin 32), u159.regs (31 : Fin 32), u158.regs (31 : Fin 32), u157.regs (31 : Fin 32), u156.regs (31 : Fin 32), u155.regs (31 : Fin 32), u154.regs (31 : Fin 32), u153.regs (31 : Fin 32), u152.regs (31 : Fin 32), u151.regs (31 : Fin 32), u150.regs (31 : Fin 32), u149.regs (31 : Fin 32), q48_31]
  obtain ⟨n165, d165, u165⟩ := u164.self.swG hc164 fsb_at_b0 (off' := 0xB2) (by decide)
    (by rw [q64_2]; exact fr_al' hFa (by decide)) (a := F + 0x78) (v := ((X9 + (0x20000000 + 0xFFFFFFF0)) - Y9))
    (by rw [q64_2]) (by rw [q64_11])
  obtain ⟨B165, hB165⟩ : ∃ M', memStore32 B164 (F + 0x78) (((X9 + (0x20000000 + 0xFFFFFFF0)) - Y9)) = M' := ⟨_, rfl⟩
  rw [hB165] at u165
  have hc165 : CodeIn B165 P feSubCode := by rw [← hB165]; exact hc164.store32 (frm_sep' sFC (by decide))
  obtain ⟨n166, d166, u166⟩ := u165.self.swG hc165 fsb_at_b2 (off' := 0xB4) (by decide)
    (by rw [u165.regs sp, q64_2]; exact fr_al' hFa (by decide)) (a := F + 0x7C) (v := 0)
    (by rw [u165.regs sp, q64_2]) (u165.self.zero)
  obtain ⟨B166, hB166⟩ : ∃ M', memStore32 B165 (F + 0x7C) (0) = M' := ⟨_, rfl⟩
  rw [hB166] at u166
  have hc166 : CodeIn B166 P feSubCode := by rw [← hB166]; exact hc165.store32 (frm_sep' sFC (by decide))
  obtain ⟨n167, d167, u167⟩ := u166.self.aluImm hc166 fsb_at_b4 (off' := 0xB6) (by decide)
  have f167 : reg n167 a0 = F + 0x8 := by
    rw [u167.newReg (by decide)]; show reg n166 sp + 0x8 = _; rw [u166.regs sp, u165.regs sp, q64_2]
  have k167 := u167.oldReg u166.self.zero
  obtain ⟨n168, d168, u168⟩ := u167.self.aluImm hc166 fsb_at_b6 (off' := 0xB8) (by decide)
  have f168 : reg n168 a1 = F + 0x30 := by
    rw [u168.newReg (by decide)]; show reg n167 sp + 0x30 = _; rw [k167 sp (by decide), u166.regs sp, u165.regs sp, q64_2]
  have k168 := u168.oldReg u167.self.zero
  -- `reduce` on the ten `u64`s at `F + 0x30`, into `F + 8`
  have fBody : ∀ x, Sep F 0x90 x 1 → B166 x = m.mem x := fun x hx => by
    rw [← hB166, memStore32_get_sep (frm_sep' hx (by decide)), ← hB165, memStore32_get_sep (frm_sep' hx (by decide)), ← hB164, memStore32_get_sep (frm_sep' hx (by decide)), ← hB163, memStore32_get_sep (frm_sep' hx (by decide)), ← hB162, memStore32_get_sep (frm_sep' hx (by decide)), ← hB161, memStore32_get_sep (frm_sep' hx (by decide)), ← hB160, memStore32_get_sep (frm_sep' hx (by decide)), ← hB159, memStore32_get_sep (frm_sep' hx (by decide)), ← hB158, memStore32_get_sep (frm_sep' hx (by decide)), ← hB157, memStore32_get_sep (frm_sep' hx (by decide)), ← hB156, memStore32_get_sep (frm_sep' hx (by decide)), ← hB155, memStore32_get_sep (frm_sep' hx (by decide)), ← hB154, memStore32_get_sep (frm_sep' hx (by decide)), ← hB153, memStore32_get_sep (frm_sep' hx (by decide)), ← hB152, memStore32_get_sep (frm_sep' hx (by decide)), ← hB151, memStore32_get_sep (frm_sep' hx (by decide)), ← hB150, memStore32_get_sep (frm_sep' hx (by decide)), ← hB149, memStore32_get_sep (frm_sep' hx (by decide)), ← hB148, memStore32_get_sep (frm_sep' hx (by decide)), ← hB147, memStore32_get_sep (frm_sep' hx (by decide)), fpro x hx]
  obtain ⟨nC, cC, pcC, memC, regsC⟩ := u168.self.callRa hc166 fsb_at_b8 fsb_at_bc (cb := P + 0xFFFFF72E)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFF72E (by decide))
  have rC := PEnv.reg1 regsC u168.self.zero
  have spC : reg nC sp = F := by rw [rC _ (by decide), k168 sp (by decide), k167 sp (by decide), u166.regs sp, u165.regs sp, q64_2]
  have s0C : reg nC (8 : Fin 32) = out := by rw [rC _ (by decide), k168 (8 : Fin 32) (by decide), k167 (8 : Fin 32) (by decide), u166.regs (8 : Fin 32), u165.regs (8 : Fin 32), q64_8]
  have RE : FREnv nC.mem (P + 0xFFFFF72E) F (F + BitVec.ofNat 32 8) (F + 0x30) := by
    rw [memC]
    refine ⟨even_at P env.hP 0xFFFFF72E (by decide), fun i hi => ?_, hFa, by omega, aligned_add hFa (by decide),
      fr_al' hFa (by decide), ?_, ?_, ?_, ?_⟩
    · rw [fBody _ (sFR.subR (c := i) (l := 1) (by omega))]; exact env.red i hi
    · rw [hGF]; have := env.sGR.sub (c := 0) (l := 0x20) (by decide); rwa [add_ofNat_zero] at this
    · rw [fG]; exact env.sGR.sub (c := 0x28) (l := 40) (by decide)
    · rw [hGF, fG]
      have := sep_offsets G (c := 0x28) (n := 40) (d := 0) (k := 0x20) (.inr (by decide)) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
    · rw [hGF, show F + 0x30 = G + BitVec.ofNat 32 0x50 from fG 0x30]
      have := sep_offsets G (c := 0x50) (n := 80) (d := 0) (k := 0x20) (.inr (by decide)) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
  obtain ⟨nR, cR, pcR, spR, kR, outR, frR⟩ := feReduce_correct nC RE pcC (by rw [rC _ (by decide), k168 a0 (by decide), f167]; try rfl)
    (by rw [rC _ (by decide), f168]) (by rw [regsC]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P env.hP (0xB8 + 8) (by decide))) spC
  rw [memC] at outR frR
  rw [hGF] at frR
  obtain ⟨Mr, hMr⟩ : ∃ M, nR.mem = M := ⟨_, rfl⟩
  rw [hMr] at frR outR
  obtain ⟨R0, hR0⟩ : ∃ v, memLoad32 Mr (F + BitVec.ofNat 32 8 + BitVec.ofNat 32 (4 * 0)) = v := ⟨_, rfl⟩
  have hRl0 : memLoad32 Mr (F + 0x8) = R0 := by rw [← hR0, add_ofNat_assoc]; rfl
  obtain ⟨R1, hR1⟩ : ∃ v, memLoad32 Mr (F + BitVec.ofNat 32 8 + BitVec.ofNat 32 (4 * 1)) = v := ⟨_, rfl⟩
  have hRl1 : memLoad32 Mr (F + 0xC) = R1 := by rw [← hR1, add_ofNat_assoc]; rfl
  obtain ⟨R2, hR2⟩ : ∃ v, memLoad32 Mr (F + BitVec.ofNat 32 8 + BitVec.ofNat 32 (4 * 2)) = v := ⟨_, rfl⟩
  have hRl2 : memLoad32 Mr (F + 0x10) = R2 := by rw [← hR2, add_ofNat_assoc]; rfl
  obtain ⟨R3, hR3⟩ : ∃ v, memLoad32 Mr (F + BitVec.ofNat 32 8 + BitVec.ofNat 32 (4 * 3)) = v := ⟨_, rfl⟩
  have hRl3 : memLoad32 Mr (F + 0x14) = R3 := by rw [← hR3, add_ofNat_assoc]; rfl
  obtain ⟨R4, hR4⟩ : ∃ v, memLoad32 Mr (F + BitVec.ofNat 32 8 + BitVec.ofNat 32 (4 * 4)) = v := ⟨_, rfl⟩
  have hRl4 : memLoad32 Mr (F + 0x18) = R4 := by rw [← hR4, add_ofNat_assoc]; rfl
  obtain ⟨R5, hR5⟩ : ∃ v, memLoad32 Mr (F + BitVec.ofNat 32 8 + BitVec.ofNat 32 (4 * 5)) = v := ⟨_, rfl⟩
  have hRl5 : memLoad32 Mr (F + 0x1C) = R5 := by rw [← hR5, add_ofNat_assoc]; rfl
  obtain ⟨R6, hR6⟩ : ∃ v, memLoad32 Mr (F + BitVec.ofNat 32 8 + BitVec.ofNat 32 (4 * 6)) = v := ⟨_, rfl⟩
  have hRl6 : memLoad32 Mr (F + 0x20) = R6 := by rw [← hR6, add_ofNat_assoc]; rfl
  obtain ⟨R7, hR7⟩ : ∃ v, memLoad32 Mr (F + BitVec.ofNat 32 8 + BitVec.ofNat 32 (4 * 7)) = v := ⟨_, rfl⟩
  have hRl7 : memLoad32 Mr (F + 0x24) = R7 := by rw [← hR7, add_ofNat_assoc]; rfl
  obtain ⟨R8, hR8⟩ : ∃ v, memLoad32 Mr (F + BitVec.ofNat 32 8 + BitVec.ofNat 32 (4 * 8)) = v := ⟨_, rfl⟩
  have hRl8 : memLoad32 Mr (F + 0x28) = R8 := by rw [← hR8, add_ofNat_assoc]; rfl
  obtain ⟨R9, hR9⟩ : ∃ v, memLoad32 Mr (F + BitVec.ofNat 32 8 + BitVec.ofNat 32 (4 * 9)) = v := ⟨_, rfl⟩
  have hRl9 : memLoad32 Mr (F + 0x2C) = R9 := by rw [← hR9, add_ofNat_assoc]; rfl
  have frRG : ∀ x, Sep G 0xB0 x 1 → Mr x = m.mem x := fun x hx => by
    rw [frR x (sep_pre hx (by decide)) (by rw [fG]; exact hx.sub (c := 0x28) (l := 40) (by decide)), fBody x (inF x hx)]
  have hcR : CodeIn Mr P feSubCode := fun i hi => by
    rw [frRG _ (env.sGC.subR (c := i) (l := 1) (by omega))]; exact env.code i hi
  have svR8C : memLoad32 Mr (F + 0x8C) = reg m ra := by
    rw [show memLoad32 Mr (F + 0x8C) = memLoad32 B166 (F + 0x8C) from load_frame2 frR (by show Sep G 0x20 (F + BitVec.ofNat 32 0x8C) 4; rw [fG]; have := sep_offsets G (c := 0) (n := 0x20) (d := 0x20 + 0x8C) (k := 4) (.inl (by decide)) (by decide) (by decide); rwa [add_ofNat_zero] at this)
      (show Sep (F + BitVec.ofNat 32 8) 40 (F + BitVec.ofNat 32 0x8C) 4 from sep_offsets F (c := 8) (n := 40) (d := 0x8C) (k := 4) (.inl (by decide)) (by decide) (by decide))]
    exact (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide)), ← hB162, memLoad32_store32_sep (show Sep (F + 0x6C) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x6C) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide)), ← hB161, memLoad32_store32_sep (show Sep (F + 0x68) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x68) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide)), ← hB160, memLoad32_store32_sep (show Sep (F + 0x64) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x64) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide)), ← hB159, memLoad32_store32_sep (show Sep (F + 0x60) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x60) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide)), ← hB158, memLoad32_store32_sep (show Sep (F + 0x5C) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x5C) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide)), ← hB157, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x58) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide)), ← hB156, memLoad32_store32_sep (show Sep (F + 0x54) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x54) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide)), ← hB155, memLoad32_store32_sep (show Sep (F + 0x50) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x50) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide)), ← hB154, memLoad32_store32_sep (show Sep (F + 0x4C) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x4C) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide)), ← hB153, memLoad32_store32_sep (show Sep (F + 0x48) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x48) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide)), ← hB152, memLoad32_store32_sep (show Sep (F + 0x44) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x44) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide)), ← hB151, memLoad32_store32_sep (show Sep (F + 0x40) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x40) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide)), ← hB150, memLoad32_store32_sep (show Sep (F + 0x3C) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x3C) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide)), ← hB149, memLoad32_store32_sep (show Sep (F + 0x38) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x38) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide)), ← hB148, memLoad32_store32_sep (show Sep (F + 0x34) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x34) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide)), ← hB147, memLoad32_store32_sep (show Sep (F + 0x30) 4 (F + 0x8C) 4 from sep_offsets F (c := 0x30) (n := 4) (d := 0x8C) (k := 4) (by decide) (by decide) (by decide))]; exact sv8C)
  have svR88 : memLoad32 Mr (F + 0x88) = reg m (8 : Fin 32) := by
    rw [show memLoad32 Mr (F + 0x88) = memLoad32 B166 (F + 0x88) from load_frame2 frR (by show Sep G 0x20 (F + BitVec.ofNat 32 0x88) 4; rw [fG]; have := sep_offsets G (c := 0) (n := 0x20) (d := 0x20 + 0x88) (k := 4) (.inl (by decide)) (by decide) (by decide); rwa [add_ofNat_zero] at this)
      (show Sep (F + BitVec.ofNat 32 8) 40 (F + BitVec.ofNat 32 0x88) 4 from sep_offsets F (c := 8) (n := 40) (d := 0x88) (k := 4) (.inl (by decide)) (by decide) (by decide))]
    exact (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x88) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x88) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x88) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x88) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide)), ← hB162, memLoad32_store32_sep (show Sep (F + 0x6C) 4 (F + 0x88) 4 from sep_offsets F (c := 0x6C) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide)), ← hB161, memLoad32_store32_sep (show Sep (F + 0x68) 4 (F + 0x88) 4 from sep_offsets F (c := 0x68) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide)), ← hB160, memLoad32_store32_sep (show Sep (F + 0x64) 4 (F + 0x88) 4 from sep_offsets F (c := 0x64) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide)), ← hB159, memLoad32_store32_sep (show Sep (F + 0x60) 4 (F + 0x88) 4 from sep_offsets F (c := 0x60) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide)), ← hB158, memLoad32_store32_sep (show Sep (F + 0x5C) 4 (F + 0x88) 4 from sep_offsets F (c := 0x5C) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide)), ← hB157, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x88) 4 from sep_offsets F (c := 0x58) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide)), ← hB156, memLoad32_store32_sep (show Sep (F + 0x54) 4 (F + 0x88) 4 from sep_offsets F (c := 0x54) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide)), ← hB155, memLoad32_store32_sep (show Sep (F + 0x50) 4 (F + 0x88) 4 from sep_offsets F (c := 0x50) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide)), ← hB154, memLoad32_store32_sep (show Sep (F + 0x4C) 4 (F + 0x88) 4 from sep_offsets F (c := 0x4C) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide)), ← hB153, memLoad32_store32_sep (show Sep (F + 0x48) 4 (F + 0x88) 4 from sep_offsets F (c := 0x48) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide)), ← hB152, memLoad32_store32_sep (show Sep (F + 0x44) 4 (F + 0x88) 4 from sep_offsets F (c := 0x44) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide)), ← hB151, memLoad32_store32_sep (show Sep (F + 0x40) 4 (F + 0x88) 4 from sep_offsets F (c := 0x40) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide)), ← hB150, memLoad32_store32_sep (show Sep (F + 0x3C) 4 (F + 0x88) 4 from sep_offsets F (c := 0x3C) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide)), ← hB149, memLoad32_store32_sep (show Sep (F + 0x38) 4 (F + 0x88) 4 from sep_offsets F (c := 0x38) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide)), ← hB148, memLoad32_store32_sep (show Sep (F + 0x34) 4 (F + 0x88) 4 from sep_offsets F (c := 0x34) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide)), ← hB147, memLoad32_store32_sep (show Sep (F + 0x30) 4 (F + 0x88) 4 from sep_offsets F (c := 0x30) (n := 4) (d := 0x88) (k := 4) (by decide) (by decide) (by decide))]; exact sv88)
  have svR84 : memLoad32 Mr (F + 0x84) = reg m (9 : Fin 32) := by
    rw [show memLoad32 Mr (F + 0x84) = memLoad32 B166 (F + 0x84) from load_frame2 frR (by show Sep G 0x20 (F + BitVec.ofNat 32 0x84) 4; rw [fG]; have := sep_offsets G (c := 0) (n := 0x20) (d := 0x20 + 0x84) (k := 4) (.inl (by decide)) (by decide) (by decide); rwa [add_ofNat_zero] at this)
      (show Sep (F + BitVec.ofNat 32 8) 40 (F + BitVec.ofNat 32 0x84) 4 from sep_offsets F (c := 8) (n := 40) (d := 0x84) (k := 4) (.inl (by decide)) (by decide) (by decide))]
    exact (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x84) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x84) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x84) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x84) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide)), ← hB162, memLoad32_store32_sep (show Sep (F + 0x6C) 4 (F + 0x84) 4 from sep_offsets F (c := 0x6C) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide)), ← hB161, memLoad32_store32_sep (show Sep (F + 0x68) 4 (F + 0x84) 4 from sep_offsets F (c := 0x68) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide)), ← hB160, memLoad32_store32_sep (show Sep (F + 0x64) 4 (F + 0x84) 4 from sep_offsets F (c := 0x64) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide)), ← hB159, memLoad32_store32_sep (show Sep (F + 0x60) 4 (F + 0x84) 4 from sep_offsets F (c := 0x60) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide)), ← hB158, memLoad32_store32_sep (show Sep (F + 0x5C) 4 (F + 0x84) 4 from sep_offsets F (c := 0x5C) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide)), ← hB157, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x84) 4 from sep_offsets F (c := 0x58) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide)), ← hB156, memLoad32_store32_sep (show Sep (F + 0x54) 4 (F + 0x84) 4 from sep_offsets F (c := 0x54) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide)), ← hB155, memLoad32_store32_sep (show Sep (F + 0x50) 4 (F + 0x84) 4 from sep_offsets F (c := 0x50) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide)), ← hB154, memLoad32_store32_sep (show Sep (F + 0x4C) 4 (F + 0x84) 4 from sep_offsets F (c := 0x4C) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide)), ← hB153, memLoad32_store32_sep (show Sep (F + 0x48) 4 (F + 0x84) 4 from sep_offsets F (c := 0x48) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide)), ← hB152, memLoad32_store32_sep (show Sep (F + 0x44) 4 (F + 0x84) 4 from sep_offsets F (c := 0x44) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide)), ← hB151, memLoad32_store32_sep (show Sep (F + 0x40) 4 (F + 0x84) 4 from sep_offsets F (c := 0x40) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide)), ← hB150, memLoad32_store32_sep (show Sep (F + 0x3C) 4 (F + 0x84) 4 from sep_offsets F (c := 0x3C) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide)), ← hB149, memLoad32_store32_sep (show Sep (F + 0x38) 4 (F + 0x84) 4 from sep_offsets F (c := 0x38) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide)), ← hB148, memLoad32_store32_sep (show Sep (F + 0x34) 4 (F + 0x84) 4 from sep_offsets F (c := 0x34) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide)), ← hB147, memLoad32_store32_sep (show Sep (F + 0x30) 4 (F + 0x84) 4 from sep_offsets F (c := 0x30) (n := 4) (d := 0x84) (k := 4) (by decide) (by decide) (by decide))]; exact sv84)
  have svR80 : memLoad32 Mr (F + 0x80) = reg m (18 : Fin 32) := by
    rw [show memLoad32 Mr (F + 0x80) = memLoad32 B166 (F + 0x80) from load_frame2 frR (by show Sep G 0x20 (F + BitVec.ofNat 32 0x80) 4; rw [fG]; have := sep_offsets G (c := 0) (n := 0x20) (d := 0x20 + 0x80) (k := 4) (.inl (by decide)) (by decide) (by decide); rwa [add_ofNat_zero] at this)
      (show Sep (F + BitVec.ofNat 32 8) 40 (F + BitVec.ofNat 32 0x80) 4 from sep_offsets F (c := 8) (n := 40) (d := 0x80) (k := 4) (.inl (by decide)) (by decide) (by decide))]
    exact (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x80) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x80) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x80) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x80) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide)), ← hB162, memLoad32_store32_sep (show Sep (F + 0x6C) 4 (F + 0x80) 4 from sep_offsets F (c := 0x6C) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide)), ← hB161, memLoad32_store32_sep (show Sep (F + 0x68) 4 (F + 0x80) 4 from sep_offsets F (c := 0x68) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide)), ← hB160, memLoad32_store32_sep (show Sep (F + 0x64) 4 (F + 0x80) 4 from sep_offsets F (c := 0x64) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide)), ← hB159, memLoad32_store32_sep (show Sep (F + 0x60) 4 (F + 0x80) 4 from sep_offsets F (c := 0x60) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide)), ← hB158, memLoad32_store32_sep (show Sep (F + 0x5C) 4 (F + 0x80) 4 from sep_offsets F (c := 0x5C) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide)), ← hB157, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x80) 4 from sep_offsets F (c := 0x58) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide)), ← hB156, memLoad32_store32_sep (show Sep (F + 0x54) 4 (F + 0x80) 4 from sep_offsets F (c := 0x54) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide)), ← hB155, memLoad32_store32_sep (show Sep (F + 0x50) 4 (F + 0x80) 4 from sep_offsets F (c := 0x50) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide)), ← hB154, memLoad32_store32_sep (show Sep (F + 0x4C) 4 (F + 0x80) 4 from sep_offsets F (c := 0x4C) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide)), ← hB153, memLoad32_store32_sep (show Sep (F + 0x48) 4 (F + 0x80) 4 from sep_offsets F (c := 0x48) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide)), ← hB152, memLoad32_store32_sep (show Sep (F + 0x44) 4 (F + 0x80) 4 from sep_offsets F (c := 0x44) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide)), ← hB151, memLoad32_store32_sep (show Sep (F + 0x40) 4 (F + 0x80) 4 from sep_offsets F (c := 0x40) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide)), ← hB150, memLoad32_store32_sep (show Sep (F + 0x3C) 4 (F + 0x80) 4 from sep_offsets F (c := 0x3C) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide)), ← hB149, memLoad32_store32_sep (show Sep (F + 0x38) 4 (F + 0x80) 4 from sep_offsets F (c := 0x38) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide)), ← hB148, memLoad32_store32_sep (show Sep (F + 0x34) 4 (F + 0x80) 4 from sep_offsets F (c := 0x34) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide)), ← hB147, memLoad32_store32_sep (show Sep (F + 0x30) 4 (F + 0x80) 4 from sep_offsets F (c := 0x30) (n := 4) (d := 0x80) (k := 4) (by decide) (by decide) (by decide))]; exact sv80)
  have wR : St Mr P nR 0xC0 (reg nR) := ⟨by rw [pcR], hMr, fun _ => rfl⟩
  have s0R : reg nR (8 : Fin 32) = out := by rw [kR _ rfl, s0C]
  obtain ⟨n169, d169, u169⟩ := wR.lwE hcR fsb_at_c0 (off' := 0xC2) (by decide)
    (by rw [spR]; exact fr_al' hFa (by decide)) (v := R0)
    (by rw [spR]; exact hRl0)
  have f169 : reg n169 a0 = R0 := u169.newReg (by decide)
  have k169 := u169.oldReg wR.zero
  obtain ⟨n170, d170, u170⟩ := u169.self.lwE hcR fsb_at_c2 (off' := 0xC4) (by decide)
    (by rw [k169 sp (by decide), spR]; exact fr_al' hFa (by decide)) (v := R1)
    (by rw [k169 sp (by decide), spR]; exact hRl1)
  have f170 : reg n170 a1 = R1 := u170.newReg (by decide)
  have k170 := u170.oldReg u169.self.zero
  obtain ⟨n171, d171, u171⟩ := u170.self.lwE hcR fsb_at_c4 (off' := 0xC6) (by decide)
    (by rw [k170 sp (by decide), k169 sp (by decide), spR]; exact fr_al' hFa (by decide)) (v := R2)
    (by rw [k170 sp (by decide), k169 sp (by decide), spR]; exact hRl2)
  have f171 : reg n171 a2 = R2 := u171.newReg (by decide)
  have k171 := u171.oldReg u170.self.zero
  obtain ⟨n172, d172, u172⟩ := u171.self.lwE hcR fsb_at_c6 (off' := 0xC8) (by decide)
    (by rw [k171 sp (by decide), k170 sp (by decide), k169 sp (by decide), spR]; exact fr_al' hFa (by decide)) (v := R3)
    (by rw [k171 sp (by decide), k170 sp (by decide), k169 sp (by decide), spR]; exact hRl3)
  have f172 : reg n172 a3 = R3 := u172.newReg (by decide)
  have k172 := u172.oldReg u171.self.zero
  obtain ⟨n173, d173, u173⟩ := u172.self.lwE hcR fsb_at_c8 (off' := 0xCA) (by decide)
    (by rw [k172 sp (by decide), k171 sp (by decide), k170 sp (by decide), k169 sp (by decide), spR]; exact fr_al' hFa (by decide)) (v := R4)
    (by rw [k172 sp (by decide), k171 sp (by decide), k170 sp (by decide), k169 sp (by decide), spR]; exact hRl4)
  have f173 : reg n173 a4 = R4 := u173.newReg (by decide)
  have k173 := u173.oldReg u172.self.zero
  obtain ⟨n174, d174, u174⟩ := u173.self.lwE hcR fsb_at_ca (off' := 0xCC) (by decide)
    (by rw [k173 sp (by decide), k172 sp (by decide), k171 sp (by decide), k170 sp (by decide), k169 sp (by decide), spR]; exact fr_al' hFa (by decide)) (v := R5)
    (by rw [k173 sp (by decide), k172 sp (by decide), k171 sp (by decide), k170 sp (by decide), k169 sp (by decide), spR]; exact hRl5)
  have f174 : reg n174 a5 = R5 := u174.newReg (by decide)
  have k174 := u174.oldReg u173.self.zero
  obtain ⟨n175, d175, u175⟩ := u174.self.lwE hcR fsb_at_cc (off' := 0xCE) (by decide)
    (by rw [k174 sp (by decide), k173 sp (by decide), k172 sp (by decide), k171 sp (by decide), k170 sp (by decide), k169 sp (by decide), spR]; exact fr_al' hFa (by decide)) (v := R6)
    (by rw [k174 sp (by decide), k173 sp (by decide), k172 sp (by decide), k171 sp (by decide), k170 sp (by decide), k169 sp (by decide), spR]; exact hRl6)
  have f175 : reg n175 (9 : Fin 32) = R6 := u175.newReg (by decide)
  have k175 := u175.oldReg u174.self.zero
  obtain ⟨n176, d176, u176⟩ := u175.self.lwE hcR fsb_at_ce (off' := 0xD0) (by decide)
    (by rw [k175 sp (by decide), k174 sp (by decide), k173 sp (by decide), k172 sp (by decide), k171 sp (by decide), k170 sp (by decide), k169 sp (by decide), spR]; exact fr_al' hFa (by decide)) (v := R7)
    (by rw [k175 sp (by decide), k174 sp (by decide), k173 sp (by decide), k172 sp (by decide), k171 sp (by decide), k170 sp (by decide), k169 sp (by decide), spR]; exact hRl7)
  have f176 : reg n176 a6 = R7 := u176.newReg (by decide)
  have k176 := u176.oldReg u175.self.zero
  obtain ⟨n177, d177, u177⟩ := u176.self.lwE hcR fsb_at_d0 (off' := 0xD2) (by decide)
    (by rw [k176 sp (by decide), k175 sp (by decide), k174 sp (by decide), k173 sp (by decide), k172 sp (by decide), k171 sp (by decide), k170 sp (by decide), k169 sp (by decide), spR]; exact fr_al' hFa (by decide)) (v := R8)
    (by rw [k176 sp (by decide), k175 sp (by decide), k174 sp (by decide), k173 sp (by decide), k172 sp (by decide), k171 sp (by decide), k170 sp (by decide), k169 sp (by decide), spR]; exact hRl8)
  have f177 : reg n177 a7 = R8 := u177.newReg (by decide)
  have k177 := u177.oldReg u176.self.zero
  obtain ⟨n178, d178, u178⟩ := u177.self.lwE hcR fsb_at_d2 (off' := 0xD4) (by decide)
    (by rw [k177 sp (by decide), k176 sp (by decide), k175 sp (by decide), k174 sp (by decide), k173 sp (by decide), k172 sp (by decide), k171 sp (by decide), k170 sp (by decide), k169 sp (by decide), spR]; exact fr_al' hFa (by decide)) (v := R9)
    (by rw [k177 sp (by decide), k176 sp (by decide), k175 sp (by decide), k174 sp (by decide), k173 sp (by decide), k172 sp (by decide), k171 sp (by decide), k170 sp (by decide), k169 sp (by decide), spR]; exact hRl9)
  have f178 : reg n178 (5 : Fin 32) = R9 := u178.newReg (by decide)
  have k178 := u178.oldReg u177.self.zero
  obtain ⟨n179, d179, u179⟩ := u178.self.swG hcR fsb_at_d4 (off' := 0xD6) (by decide)
    (by rw [k178 (8 : Fin 32) (by decide), k177 (8 : Fin 32) (by decide), k176 (8 : Fin 32) (by decide), k175 (8 : Fin 32) (by decide), k174 (8 : Fin 32) (by decide), k173 (8 : Fin 32) (by decide), k172 (8 : Fin 32) (by decide), k171 (8 : Fin 32) (by decide), k170 (8 : Fin 32) (by decide), k169 (8 : Fin 32) (by decide), s0R]; exact fr_al' env.hout (by decide)) (a := out + 0x0) (v := R0)
    (by rw [k178 (8 : Fin 32) (by decide), k177 (8 : Fin 32) (by decide), k176 (8 : Fin 32) (by decide), k175 (8 : Fin 32) (by decide), k174 (8 : Fin 32) (by decide), k173 (8 : Fin 32) (by decide), k172 (8 : Fin 32) (by decide), k171 (8 : Fin 32) (by decide), k170 (8 : Fin 32) (by decide), k169 (8 : Fin 32) (by decide), s0R]) (by rw [k178 a0 (by decide), k177 a0 (by decide), k176 a0 (by decide), k175 a0 (by decide), k174 a0 (by decide), k173 a0 (by decide), k172 a0 (by decide), k171 a0 (by decide), k170 a0 (by decide), f169])
  obtain ⟨B179, hB179⟩ : ∃ M', memStore32 Mr (out + 0x0) (R0) = M' := ⟨_, rfl⟩
  rw [hB179] at u179
  have hc179 : CodeIn B179 P feSubCode := by rw [← hB179]; exact hcR.store32 (env.sOC.sub (c := 0x0) (l := 4) (by decide))
  obtain ⟨n180, d180, u180⟩ := u179.self.swG hc179 fsb_at_d6 (off' := 0xD8) (by decide)
    (by rw [u179.regs (8 : Fin 32), k178 (8 : Fin 32) (by decide), k177 (8 : Fin 32) (by decide), k176 (8 : Fin 32) (by decide), k175 (8 : Fin 32) (by decide), k174 (8 : Fin 32) (by decide), k173 (8 : Fin 32) (by decide), k172 (8 : Fin 32) (by decide), k171 (8 : Fin 32) (by decide), k170 (8 : Fin 32) (by decide), k169 (8 : Fin 32) (by decide), s0R]; exact fr_al' env.hout (by decide)) (a := out + 0x4) (v := R1)
    (by rw [u179.regs (8 : Fin 32), k178 (8 : Fin 32) (by decide), k177 (8 : Fin 32) (by decide), k176 (8 : Fin 32) (by decide), k175 (8 : Fin 32) (by decide), k174 (8 : Fin 32) (by decide), k173 (8 : Fin 32) (by decide), k172 (8 : Fin 32) (by decide), k171 (8 : Fin 32) (by decide), k170 (8 : Fin 32) (by decide), k169 (8 : Fin 32) (by decide), s0R]) (by rw [u179.regs a1, k178 a1 (by decide), k177 a1 (by decide), k176 a1 (by decide), k175 a1 (by decide), k174 a1 (by decide), k173 a1 (by decide), k172 a1 (by decide), k171 a1 (by decide), f170])
  obtain ⟨B180, hB180⟩ : ∃ M', memStore32 B179 (out + 0x4) (R1) = M' := ⟨_, rfl⟩
  rw [hB180] at u180
  have hc180 : CodeIn B180 P feSubCode := by rw [← hB180]; exact hc179.store32 (env.sOC.sub (c := 0x4) (l := 4) (by decide))
  obtain ⟨n181, d181, u181⟩ := u180.self.swG hc180 fsb_at_d8 (off' := 0xDA) (by decide)
    (by rw [u180.regs (8 : Fin 32), u179.regs (8 : Fin 32), k178 (8 : Fin 32) (by decide), k177 (8 : Fin 32) (by decide), k176 (8 : Fin 32) (by decide), k175 (8 : Fin 32) (by decide), k174 (8 : Fin 32) (by decide), k173 (8 : Fin 32) (by decide), k172 (8 : Fin 32) (by decide), k171 (8 : Fin 32) (by decide), k170 (8 : Fin 32) (by decide), k169 (8 : Fin 32) (by decide), s0R]; exact fr_al' env.hout (by decide)) (a := out + 0x8) (v := R2)
    (by rw [u180.regs (8 : Fin 32), u179.regs (8 : Fin 32), k178 (8 : Fin 32) (by decide), k177 (8 : Fin 32) (by decide), k176 (8 : Fin 32) (by decide), k175 (8 : Fin 32) (by decide), k174 (8 : Fin 32) (by decide), k173 (8 : Fin 32) (by decide), k172 (8 : Fin 32) (by decide), k171 (8 : Fin 32) (by decide), k170 (8 : Fin 32) (by decide), k169 (8 : Fin 32) (by decide), s0R]) (by rw [u180.regs a2, u179.regs a2, k178 a2 (by decide), k177 a2 (by decide), k176 a2 (by decide), k175 a2 (by decide), k174 a2 (by decide), k173 a2 (by decide), k172 a2 (by decide), f171])
  obtain ⟨B181, hB181⟩ : ∃ M', memStore32 B180 (out + 0x8) (R2) = M' := ⟨_, rfl⟩
  rw [hB181] at u181
  have hc181 : CodeIn B181 P feSubCode := by rw [← hB181]; exact hc180.store32 (env.sOC.sub (c := 0x8) (l := 4) (by decide))
  obtain ⟨n182, d182, u182⟩ := u181.self.swG hc181 fsb_at_da (off' := 0xDC) (by decide)
    (by rw [u181.regs (8 : Fin 32), u180.regs (8 : Fin 32), u179.regs (8 : Fin 32), k178 (8 : Fin 32) (by decide), k177 (8 : Fin 32) (by decide), k176 (8 : Fin 32) (by decide), k175 (8 : Fin 32) (by decide), k174 (8 : Fin 32) (by decide), k173 (8 : Fin 32) (by decide), k172 (8 : Fin 32) (by decide), k171 (8 : Fin 32) (by decide), k170 (8 : Fin 32) (by decide), k169 (8 : Fin 32) (by decide), s0R]; exact fr_al' env.hout (by decide)) (a := out + 0xC) (v := R3)
    (by rw [u181.regs (8 : Fin 32), u180.regs (8 : Fin 32), u179.regs (8 : Fin 32), k178 (8 : Fin 32) (by decide), k177 (8 : Fin 32) (by decide), k176 (8 : Fin 32) (by decide), k175 (8 : Fin 32) (by decide), k174 (8 : Fin 32) (by decide), k173 (8 : Fin 32) (by decide), k172 (8 : Fin 32) (by decide), k171 (8 : Fin 32) (by decide), k170 (8 : Fin 32) (by decide), k169 (8 : Fin 32) (by decide), s0R]) (by rw [u181.regs a3, u180.regs a3, u179.regs a3, k178 a3 (by decide), k177 a3 (by decide), k176 a3 (by decide), k175 a3 (by decide), k174 a3 (by decide), k173 a3 (by decide), f172])
  obtain ⟨B182, hB182⟩ : ∃ M', memStore32 B181 (out + 0xC) (R3) = M' := ⟨_, rfl⟩
  rw [hB182] at u182
  have hc182 : CodeIn B182 P feSubCode := by rw [← hB182]; exact hc181.store32 (env.sOC.sub (c := 0xC) (l := 4) (by decide))
  obtain ⟨n183, d183, u183⟩ := u182.self.swG hc182 fsb_at_dc (off' := 0xDE) (by decide)
    (by rw [u182.regs (8 : Fin 32), u181.regs (8 : Fin 32), u180.regs (8 : Fin 32), u179.regs (8 : Fin 32), k178 (8 : Fin 32) (by decide), k177 (8 : Fin 32) (by decide), k176 (8 : Fin 32) (by decide), k175 (8 : Fin 32) (by decide), k174 (8 : Fin 32) (by decide), k173 (8 : Fin 32) (by decide), k172 (8 : Fin 32) (by decide), k171 (8 : Fin 32) (by decide), k170 (8 : Fin 32) (by decide), k169 (8 : Fin 32) (by decide), s0R]; exact fr_al' env.hout (by decide)) (a := out + 0x10) (v := R4)
    (by rw [u182.regs (8 : Fin 32), u181.regs (8 : Fin 32), u180.regs (8 : Fin 32), u179.regs (8 : Fin 32), k178 (8 : Fin 32) (by decide), k177 (8 : Fin 32) (by decide), k176 (8 : Fin 32) (by decide), k175 (8 : Fin 32) (by decide), k174 (8 : Fin 32) (by decide), k173 (8 : Fin 32) (by decide), k172 (8 : Fin 32) (by decide), k171 (8 : Fin 32) (by decide), k170 (8 : Fin 32) (by decide), k169 (8 : Fin 32) (by decide), s0R]) (by rw [u182.regs a4, u181.regs a4, u180.regs a4, u179.regs a4, k178 a4 (by decide), k177 a4 (by decide), k176 a4 (by decide), k175 a4 (by decide), k174 a4 (by decide), f173])
  obtain ⟨B183, hB183⟩ : ∃ M', memStore32 B182 (out + 0x10) (R4) = M' := ⟨_, rfl⟩
  rw [hB183] at u183
  have hc183 : CodeIn B183 P feSubCode := by rw [← hB183]; exact hc182.store32 (env.sOC.sub (c := 0x10) (l := 4) (by decide))
  obtain ⟨n184, d184, u184⟩ := u183.self.swG hc183 fsb_at_de (off' := 0xE0) (by decide)
    (by rw [u183.regs (8 : Fin 32), u182.regs (8 : Fin 32), u181.regs (8 : Fin 32), u180.regs (8 : Fin 32), u179.regs (8 : Fin 32), k178 (8 : Fin 32) (by decide), k177 (8 : Fin 32) (by decide), k176 (8 : Fin 32) (by decide), k175 (8 : Fin 32) (by decide), k174 (8 : Fin 32) (by decide), k173 (8 : Fin 32) (by decide), k172 (8 : Fin 32) (by decide), k171 (8 : Fin 32) (by decide), k170 (8 : Fin 32) (by decide), k169 (8 : Fin 32) (by decide), s0R]; exact fr_al' env.hout (by decide)) (a := out + 0x14) (v := R5)
    (by rw [u183.regs (8 : Fin 32), u182.regs (8 : Fin 32), u181.regs (8 : Fin 32), u180.regs (8 : Fin 32), u179.regs (8 : Fin 32), k178 (8 : Fin 32) (by decide), k177 (8 : Fin 32) (by decide), k176 (8 : Fin 32) (by decide), k175 (8 : Fin 32) (by decide), k174 (8 : Fin 32) (by decide), k173 (8 : Fin 32) (by decide), k172 (8 : Fin 32) (by decide), k171 (8 : Fin 32) (by decide), k170 (8 : Fin 32) (by decide), k169 (8 : Fin 32) (by decide), s0R]) (by rw [u183.regs a5, u182.regs a5, u181.regs a5, u180.regs a5, u179.regs a5, k178 a5 (by decide), k177 a5 (by decide), k176 a5 (by decide), k175 a5 (by decide), f174])
  obtain ⟨B184, hB184⟩ : ∃ M', memStore32 B183 (out + 0x14) (R5) = M' := ⟨_, rfl⟩
  rw [hB184] at u184
  have hc184 : CodeIn B184 P feSubCode := by rw [← hB184]; exact hc183.store32 (env.sOC.sub (c := 0x14) (l := 4) (by decide))
  have q16_2 : reg n184 sp = F := by rw [u184.regs sp, u183.regs sp, u182.regs sp, u181.regs sp, u180.regs sp, u179.regs sp, k178 sp (by decide), k177 sp (by decide), k176 sp (by decide), k175 sp (by decide), k174 sp (by decide), k173 sp (by decide), k172 sp (by decide), k171 sp (by decide), k170 sp (by decide), k169 sp (by decide), spR]
  have q16_5 : reg n184 (5 : Fin 32) = R9 := by rw [u184.regs (5 : Fin 32), u183.regs (5 : Fin 32), u182.regs (5 : Fin 32), u181.regs (5 : Fin 32), u180.regs (5 : Fin 32), u179.regs (5 : Fin 32), f178]
  have q16_8 : reg n184 (8 : Fin 32) = out := by rw [u184.regs (8 : Fin 32), u183.regs (8 : Fin 32), u182.regs (8 : Fin 32), u181.regs (8 : Fin 32), u180.regs (8 : Fin 32), u179.regs (8 : Fin 32), k178 (8 : Fin 32) (by decide), k177 (8 : Fin 32) (by decide), k176 (8 : Fin 32) (by decide), k175 (8 : Fin 32) (by decide), k174 (8 : Fin 32) (by decide), k173 (8 : Fin 32) (by decide), k172 (8 : Fin 32) (by decide), k171 (8 : Fin 32) (by decide), k170 (8 : Fin 32) (by decide), k169 (8 : Fin 32) (by decide), s0R]
  have q16_9 : reg n184 (9 : Fin 32) = R6 := by rw [u184.regs (9 : Fin 32), u183.regs (9 : Fin 32), u182.regs (9 : Fin 32), u181.regs (9 : Fin 32), u180.regs (9 : Fin 32), u179.regs (9 : Fin 32), k178 (9 : Fin 32) (by decide), k177 (9 : Fin 32) (by decide), k176 (9 : Fin 32) (by decide), f175]
  have q16_10 : reg n184 a0 = R0 := by rw [u184.regs a0, u183.regs a0, u182.regs a0, u181.regs a0, u180.regs a0, u179.regs a0, k178 a0 (by decide), k177 a0 (by decide), k176 a0 (by decide), k175 a0 (by decide), k174 a0 (by decide), k173 a0 (by decide), k172 a0 (by decide), k171 a0 (by decide), k170 a0 (by decide), f169]
  have q16_11 : reg n184 a1 = R1 := by rw [u184.regs a1, u183.regs a1, u182.regs a1, u181.regs a1, u180.regs a1, u179.regs a1, k178 a1 (by decide), k177 a1 (by decide), k176 a1 (by decide), k175 a1 (by decide), k174 a1 (by decide), k173 a1 (by decide), k172 a1 (by decide), k171 a1 (by decide), f170]
  have q16_12 : reg n184 a2 = R2 := by rw [u184.regs a2, u183.regs a2, u182.regs a2, u181.regs a2, u180.regs a2, u179.regs a2, k178 a2 (by decide), k177 a2 (by decide), k176 a2 (by decide), k175 a2 (by decide), k174 a2 (by decide), k173 a2 (by decide), k172 a2 (by decide), f171]
  have q16_13 : reg n184 a3 = R3 := by rw [u184.regs a3, u183.regs a3, u182.regs a3, u181.regs a3, u180.regs a3, u179.regs a3, k178 a3 (by decide), k177 a3 (by decide), k176 a3 (by decide), k175 a3 (by decide), k174 a3 (by decide), k173 a3 (by decide), f172]
  have q16_14 : reg n184 a4 = R4 := by rw [u184.regs a4, u183.regs a4, u182.regs a4, u181.regs a4, u180.regs a4, u179.regs a4, k178 a4 (by decide), k177 a4 (by decide), k176 a4 (by decide), k175 a4 (by decide), k174 a4 (by decide), f173]
  have q16_15 : reg n184 a5 = R5 := by rw [u184.regs a5, u183.regs a5, u182.regs a5, u181.regs a5, u180.regs a5, u179.regs a5, k178 a5 (by decide), k177 a5 (by decide), k176 a5 (by decide), k175 a5 (by decide), f174]
  have q16_16 : reg n184 a6 = R7 := by rw [u184.regs a6, u183.regs a6, u182.regs a6, u181.regs a6, u180.regs a6, u179.regs a6, k178 a6 (by decide), k177 a6 (by decide), f176]
  have q16_17 : reg n184 a7 = R8 := by rw [u184.regs a7, u183.regs a7, u182.regs a7, u181.regs a7, u180.regs a7, u179.regs a7, k178 a7 (by decide), f177]
  obtain ⟨n185, d185, u185⟩ := u184.self.swG hc184 fsb_at_e0 (off' := 0xE2) (by decide)
    (by rw [q16_8]; exact fr_al' env.hout (by decide)) (a := out + 0x18) (v := R6)
    (by rw [q16_8]) (by rw [q16_9])
  obtain ⟨B185, hB185⟩ : ∃ M', memStore32 B184 (out + 0x18) (R6) = M' := ⟨_, rfl⟩
  rw [hB185] at u185
  have hc185 : CodeIn B185 P feSubCode := by rw [← hB185]; exact hc184.store32 (env.sOC.sub (c := 0x18) (l := 4) (by decide))
  obtain ⟨n186, d186, u186⟩ := u185.self.swG hc185 fsb_at_e2 (off' := 0xE6) (by decide)
    (by rw [u185.regs (8 : Fin 32), q16_8]; exact fr_al' env.hout (by decide)) (a := out + 0x1C) (v := R7)
    (by rw [u185.regs (8 : Fin 32), q16_8]) (by rw [u185.regs a6, q16_16])
  obtain ⟨B186, hB186⟩ : ∃ M', memStore32 B185 (out + 0x1C) (R7) = M' := ⟨_, rfl⟩
  rw [hB186] at u186
  have hc186 : CodeIn B186 P feSubCode := by rw [← hB186]; exact hc185.store32 (env.sOC.sub (c := 0x1C) (l := 4) (by decide))
  obtain ⟨n187, d187, u187⟩ := u186.self.swG hc186 fsb_at_e6 (off' := 0xEA) (by decide)
    (by rw [u186.regs (8 : Fin 32), u185.regs (8 : Fin 32), q16_8]; exact fr_al' env.hout (by decide)) (a := out + 0x20) (v := R8)
    (by rw [u186.regs (8 : Fin 32), u185.regs (8 : Fin 32), q16_8]) (by rw [u186.regs a7, u185.regs a7, q16_17])
  obtain ⟨B187, hB187⟩ : ∃ M', memStore32 B186 (out + 0x20) (R8) = M' := ⟨_, rfl⟩
  rw [hB187] at u187
  have hc187 : CodeIn B187 P feSubCode := by rw [← hB187]; exact hc186.store32 (env.sOC.sub (c := 0x20) (l := 4) (by decide))
  obtain ⟨n188, d188, u188⟩ := u187.self.swG hc187 fsb_at_ea (off' := 0xEE) (by decide)
    (by rw [u187.regs (8 : Fin 32), u186.regs (8 : Fin 32), u185.regs (8 : Fin 32), q16_8]; exact fr_al' env.hout (by decide)) (a := out + 0x24) (v := R9)
    (by rw [u187.regs (8 : Fin 32), u186.regs (8 : Fin 32), u185.regs (8 : Fin 32), q16_8]) (by rw [u187.regs (5 : Fin 32), u186.regs (5 : Fin 32), u185.regs (5 : Fin 32), q16_5])
  obtain ⟨B188, hB188⟩ : ∃ M', memStore32 B187 (out + 0x24) (R9) = M' := ⟨_, rfl⟩
  rw [hB188] at u188
  have hc188 : CodeIn B188 P feSubCode := by rw [← hB188]; exact hc187.store32 (env.sOC.sub (c := 0x24) (l := 4) (by decide))
  obtain ⟨n189, d189, u189⟩ := u188.self.lwE hc188 fsb_at_ee (off' := 0xF0) (by decide)
    (by rw [u188.regs sp, u187.regs sp, u186.regs sp, u185.regs sp, q16_2]; exact fr_al' hFa (by decide)) (v := reg m ra)
    (by rw [u188.regs sp, u187.regs sp, u186.regs sp, u185.regs sp, q16_2]; exact (by rw [← hB188, memLoad32_store32_sep (show Sep (out + 0x24) 4 (F + 0x8C) 4 from sOFs 0x24 0x8C (by decide) (by decide)), ← hB187, memLoad32_store32_sep (show Sep (out + 0x20) 4 (F + 0x8C) 4 from sOFs 0x20 0x8C (by decide) (by decide)), ← hB186, memLoad32_store32_sep (show Sep (out + 0x1C) 4 (F + 0x8C) 4 from sOFs 0x1C 0x8C (by decide) (by decide)), ← hB185, memLoad32_store32_sep (show Sep (out + 0x18) 4 (F + 0x8C) 4 from sOFs 0x18 0x8C (by decide) (by decide)), ← hB184, memLoad32_store32_sep (show Sep (out + 0x14) 4 (F + 0x8C) 4 from sOFs 0x14 0x8C (by decide) (by decide)), ← hB183, memLoad32_store32_sep (show Sep (out + 0x10) 4 (F + 0x8C) 4 from sOFs 0x10 0x8C (by decide) (by decide)), ← hB182, memLoad32_store32_sep (show Sep (out + 0xC) 4 (F + 0x8C) 4 from sOFs 0xC 0x8C (by decide) (by decide)), ← hB181, memLoad32_store32_sep (show Sep (out + 0x8) 4 (F + 0x8C) 4 from sOFs 0x8 0x8C (by decide) (by decide)), ← hB180, memLoad32_store32_sep (show Sep (out + 0x4) 4 (F + 0x8C) 4 from sOFs 0x4 0x8C (by decide) (by decide)), ← hB179, memLoad32_store32_sep (show Sep (out + 0x0) 4 (F + 0x8C) 4 from sOFs 0x0 0x8C (by decide) (by decide))]; exact svR8C))
  have f189 : reg n189 ra = reg m ra := u189.newReg (by decide)
  have k189 := u189.oldReg u188.self.zero
  obtain ⟨n190, d190, u190⟩ := u189.self.lwE hc188 fsb_at_f0 (off' := 0xF2) (by decide)
    (by rw [k189 sp (by decide), u188.regs sp, u187.regs sp, u186.regs sp, u185.regs sp, q16_2]; exact fr_al' hFa (by decide)) (v := reg m (8 : Fin 32))
    (by rw [k189 sp (by decide), u188.regs sp, u187.regs sp, u186.regs sp, u185.regs sp, q16_2]; exact (by rw [← hB188, memLoad32_store32_sep (show Sep (out + 0x24) 4 (F + 0x88) 4 from sOFs 0x24 0x88 (by decide) (by decide)), ← hB187, memLoad32_store32_sep (show Sep (out + 0x20) 4 (F + 0x88) 4 from sOFs 0x20 0x88 (by decide) (by decide)), ← hB186, memLoad32_store32_sep (show Sep (out + 0x1C) 4 (F + 0x88) 4 from sOFs 0x1C 0x88 (by decide) (by decide)), ← hB185, memLoad32_store32_sep (show Sep (out + 0x18) 4 (F + 0x88) 4 from sOFs 0x18 0x88 (by decide) (by decide)), ← hB184, memLoad32_store32_sep (show Sep (out + 0x14) 4 (F + 0x88) 4 from sOFs 0x14 0x88 (by decide) (by decide)), ← hB183, memLoad32_store32_sep (show Sep (out + 0x10) 4 (F + 0x88) 4 from sOFs 0x10 0x88 (by decide) (by decide)), ← hB182, memLoad32_store32_sep (show Sep (out + 0xC) 4 (F + 0x88) 4 from sOFs 0xC 0x88 (by decide) (by decide)), ← hB181, memLoad32_store32_sep (show Sep (out + 0x8) 4 (F + 0x88) 4 from sOFs 0x8 0x88 (by decide) (by decide)), ← hB180, memLoad32_store32_sep (show Sep (out + 0x4) 4 (F + 0x88) 4 from sOFs 0x4 0x88 (by decide) (by decide)), ← hB179, memLoad32_store32_sep (show Sep (out + 0x0) 4 (F + 0x88) 4 from sOFs 0x0 0x88 (by decide) (by decide))]; exact svR88))
  have f190 : reg n190 (8 : Fin 32) = reg m (8 : Fin 32) := u190.newReg (by decide)
  have k190 := u190.oldReg u189.self.zero
  obtain ⟨n191, d191, u191⟩ := u190.self.lwE hc188 fsb_at_f2 (off' := 0xF4) (by decide)
    (by rw [k190 sp (by decide), k189 sp (by decide), u188.regs sp, u187.regs sp, u186.regs sp, u185.regs sp, q16_2]; exact fr_al' hFa (by decide)) (v := reg m (9 : Fin 32))
    (by rw [k190 sp (by decide), k189 sp (by decide), u188.regs sp, u187.regs sp, u186.regs sp, u185.regs sp, q16_2]; exact (by rw [← hB188, memLoad32_store32_sep (show Sep (out + 0x24) 4 (F + 0x84) 4 from sOFs 0x24 0x84 (by decide) (by decide)), ← hB187, memLoad32_store32_sep (show Sep (out + 0x20) 4 (F + 0x84) 4 from sOFs 0x20 0x84 (by decide) (by decide)), ← hB186, memLoad32_store32_sep (show Sep (out + 0x1C) 4 (F + 0x84) 4 from sOFs 0x1C 0x84 (by decide) (by decide)), ← hB185, memLoad32_store32_sep (show Sep (out + 0x18) 4 (F + 0x84) 4 from sOFs 0x18 0x84 (by decide) (by decide)), ← hB184, memLoad32_store32_sep (show Sep (out + 0x14) 4 (F + 0x84) 4 from sOFs 0x14 0x84 (by decide) (by decide)), ← hB183, memLoad32_store32_sep (show Sep (out + 0x10) 4 (F + 0x84) 4 from sOFs 0x10 0x84 (by decide) (by decide)), ← hB182, memLoad32_store32_sep (show Sep (out + 0xC) 4 (F + 0x84) 4 from sOFs 0xC 0x84 (by decide) (by decide)), ← hB181, memLoad32_store32_sep (show Sep (out + 0x8) 4 (F + 0x84) 4 from sOFs 0x8 0x84 (by decide) (by decide)), ← hB180, memLoad32_store32_sep (show Sep (out + 0x4) 4 (F + 0x84) 4 from sOFs 0x4 0x84 (by decide) (by decide)), ← hB179, memLoad32_store32_sep (show Sep (out + 0x0) 4 (F + 0x84) 4 from sOFs 0x0 0x84 (by decide) (by decide))]; exact svR84))
  have f191 : reg n191 (9 : Fin 32) = reg m (9 : Fin 32) := u191.newReg (by decide)
  have k191 := u191.oldReg u190.self.zero
  obtain ⟨n192, d192, u192⟩ := u191.self.lwE hc188 fsb_at_f4 (off' := 0xF6) (by decide)
    (by rw [k191 sp (by decide), k190 sp (by decide), k189 sp (by decide), u188.regs sp, u187.regs sp, u186.regs sp, u185.regs sp, q16_2]; exact fr_al' hFa (by decide)) (v := reg m (18 : Fin 32))
    (by rw [k191 sp (by decide), k190 sp (by decide), k189 sp (by decide), u188.regs sp, u187.regs sp, u186.regs sp, u185.regs sp, q16_2]; exact (by rw [← hB188, memLoad32_store32_sep (show Sep (out + 0x24) 4 (F + 0x80) 4 from sOFs 0x24 0x80 (by decide) (by decide)), ← hB187, memLoad32_store32_sep (show Sep (out + 0x20) 4 (F + 0x80) 4 from sOFs 0x20 0x80 (by decide) (by decide)), ← hB186, memLoad32_store32_sep (show Sep (out + 0x1C) 4 (F + 0x80) 4 from sOFs 0x1C 0x80 (by decide) (by decide)), ← hB185, memLoad32_store32_sep (show Sep (out + 0x18) 4 (F + 0x80) 4 from sOFs 0x18 0x80 (by decide) (by decide)), ← hB184, memLoad32_store32_sep (show Sep (out + 0x14) 4 (F + 0x80) 4 from sOFs 0x14 0x80 (by decide) (by decide)), ← hB183, memLoad32_store32_sep (show Sep (out + 0x10) 4 (F + 0x80) 4 from sOFs 0x10 0x80 (by decide) (by decide)), ← hB182, memLoad32_store32_sep (show Sep (out + 0xC) 4 (F + 0x80) 4 from sOFs 0xC 0x80 (by decide) (by decide)), ← hB181, memLoad32_store32_sep (show Sep (out + 0x8) 4 (F + 0x80) 4 from sOFs 0x8 0x80 (by decide) (by decide)), ← hB180, memLoad32_store32_sep (show Sep (out + 0x4) 4 (F + 0x80) 4 from sOFs 0x4 0x80 (by decide) (by decide)), ← hB179, memLoad32_store32_sep (show Sep (out + 0x0) 4 (F + 0x80) 4 from sOFs 0x0 0x80 (by decide) (by decide))]; exact svR80))
  have f192 : reg n192 (18 : Fin 32) = reg m (18 : Fin 32) := u192.newReg (by decide)
  have k192 := u192.oldReg u191.self.zero
  obtain ⟨g4, dg4, ug4⟩ := u192.self.aluImm hc188 fsb_at_f6 (off' := 0xF8) (by decide)
  obtain ⟨g5, dg5, pc5, mem5, regs5⟩ := ug4.self.jalr hc188 fsb_at_f8
  have kf : ∀ q, q ≠ sp → reg g5 q = reg n192 q := fun q hq => by rw [regs5, ug4.oldReg u192.self.zero q hq]
  have spf : reg g5 sp = G + 0xB0 := by
    rw [regs5, ug4.newReg (by decide)]; show reg n192 sp + 0x90 = _; rw [k192 sp (by decide), k191 sp (by decide), k190 sp (by decide), k189 sp (by decide), u188.regs sp, u187.regs sp, u186.regs sp, u185.regs sp, q16_2, hspF]
  have finra : reg n192 ra = reg m ra := by rw [k192 ra (by decide), k191 ra (by decide), k190 ra (by decide), f189]
  have fins0 : reg n192 (8 : Fin 32) = reg m (8 : Fin 32) := by rw [k192 (8 : Fin 32) (by decide), k191 (8 : Fin 32) (by decide), f190]
  have fins1 : reg n192 (9 : Fin 32) = reg m (9 : Fin 32) := by rw [k192 (9 : Fin 32) (by decide), f191]
  have fins2 : reg n192 (18 : Fin 32) = reg m (18 : Fin 32) := by rw [f192]
  have pass : ∀ q : Fin 32, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n192 q = reg m q := by
    intro q hq
    have nl : ∀ r : Fin 32, r.val ∉ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ r := by
      intro r hr e; subst e; exact hr hq
    have hk : frKeep q = true := by
      have : ∀ q : Fin 32, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → frKeep q = true := by decide
      exact this q hq
    rw [k192 (q : Fin 32) (nl _ (by decide)), k191 (q : Fin 32) (nl _ (by decide)), k190 (q : Fin 32) (nl _ (by decide)), k189 (q : Fin 32) (nl _ (by decide)), u188.regs (q : Fin 32), u187.regs (q : Fin 32), u186.regs (q : Fin 32), u185.regs (q : Fin 32), u184.regs (q : Fin 32), u183.regs (q : Fin 32), u182.regs (q : Fin 32), u181.regs (q : Fin 32), u180.regs (q : Fin 32), u179.regs (q : Fin 32), k178 (q : Fin 32) (nl _ (by decide)), k177 (q : Fin 32) (nl _ (by decide)), k176 (q : Fin 32) (nl _ (by decide)), k175 (q : Fin 32) (nl _ (by decide)), k174 (q : Fin 32) (nl _ (by decide)), k173 (q : Fin 32) (nl _ (by decide)), k172 (q : Fin 32) (nl _ (by decide)), k171 (q : Fin 32) (nl _ (by decide)), k170 (q : Fin 32) (nl _ (by decide)), k169 (q : Fin 32) (nl _ (by decide)), kR q hk, rC q (nl _ (by decide)),
      k168 (q : Fin 32) (nl _ (by decide)), k167 (q : Fin 32) (nl _ (by decide)), u166.regs (q : Fin 32), u165.regs (q : Fin 32), u164.regs (q : Fin 32), u163.regs (q : Fin 32), u162.regs (q : Fin 32), u161.regs (q : Fin 32), u160.regs (q : Fin 32), u159.regs (q : Fin 32), u158.regs (q : Fin 32), u157.regs (q : Fin 32), u156.regs (q : Fin 32), u155.regs (q : Fin 32), u154.regs (q : Fin 32), u153.regs (q : Fin 32), u152.regs (q : Fin 32), u151.regs (q : Fin 32), u150.regs (q : Fin 32), u149.regs (q : Fin 32), u148.regs (q : Fin 32), u147.regs (q : Fin 32), k146 (q : Fin 32) (nl _ (by decide)), k145 (q : Fin 32) (nl _ (by decide)), k144 (q : Fin 32) (nl _ (by decide)), k143 (q : Fin 32) (nl _ (by decide)), k142 (q : Fin 32) (nl _ (by decide)), k141 (q : Fin 32) (nl _ (by decide)), k140 (q : Fin 32) (nl _ (by decide)), k139 (q : Fin 32) (nl _ (by decide)), k138 (q : Fin 32) (nl _ (by decide)), k137 (q : Fin 32) (nl _ (by decide)), k136 (q : Fin 32) (nl _ (by decide)), k135 (q : Fin 32) (nl _ (by decide)), k134 (q : Fin 32) (nl _ (by decide)), k133 (q : Fin 32) (nl _ (by decide)), k132 (q : Fin 32) (nl _ (by decide)), k131 (q : Fin 32) (nl _ (by decide)), k130 (q : Fin 32) (nl _ (by decide)), k129 (q : Fin 32) (nl _ (by decide)), k128 (q : Fin 32) (nl _ (by decide)), k127 (q : Fin 32) (nl _ (by decide)), k126 (q : Fin 32) (nl _ (by decide)), k125 (q : Fin 32) (nl _ (by decide)), k124 (q : Fin 32) (nl _ (by decide)), k123 (q : Fin 32) (nl _ (by decide)), k122 (q : Fin 32) (nl _ (by decide)), k121 (q : Fin 32) (nl _ (by decide)), k120 (q : Fin 32) (nl _ (by decide)), k119 (q : Fin 32) (nl _ (by decide)), k118 (q : Fin 32) (nl _ (by decide)), k117 (q : Fin 32) (nl _ (by decide)), k116 (q : Fin 32) (nl _ (by decide)), k115 (q : Fin 32) (nl _ (by decide)), k114 (q : Fin 32) (nl _ (by decide)), k113 (q : Fin 32) (nl _ (by decide)), k112 (q : Fin 32) (nl _ (by decide)), k111 (q : Fin 32) (nl _ (by decide)), k110 (q : Fin 32) (nl _ (by decide)), k109 (q : Fin 32) (nl _ (by decide)), k108 (q : Fin 32) (nl _ (by decide)), k107 (q : Fin 32) (nl _ (by decide)), k106 (q : Fin 32) (nl _ (by decide)), k105 (q : Fin 32) (nl _ (by decide)), k104 (q : Fin 32) (nl _ (by decide)), k103 (q : Fin 32) (nl _ (by decide)), k102 (q : Fin 32) (nl _ (by decide)), k101 (q : Fin 32) (nl _ (by decide)), k1 q (nl _ (by decide))]
  have hmem : ∀ q : Fin 32, feMKeep q = true → q = 0 ∨ q = ra ∨ q = sp ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨
      q = (18 : Fin 32) ∨ q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by decide
  refine ⟨g5, .cons d1 (.cons dp0 (.cons dp1 (.cons dp2 (.cons dp3 (.cons d101 (.cons d102 (.cons d103 (.cons d104 (.cons d105 (.cons d106 (.cons d107 (.cons d108 (.cons d109 (.cons d110 (.cons d111 (.cons d112 (.cons d113 (.cons d114 (.cons d115 (.cons d116 (.cons d117 (.cons d118 (.cons d119 (.cons d120 (.cons d121 (.cons d122 (.cons d123 (.cons d124 (.cons d125 (.cons d126 (.cons d127 (.cons d128 (.cons d129 (.cons d130 (.cons d131 (.cons d132 (.cons d133 (.cons d134 (.cons d135 (.cons d136 (.cons d137 (.cons d138 (.cons d139 (.cons d140 (.cons d141 (.cons d142 (.cons d143 (.cons d144 (.cons d145 (.cons d146 (.cons d147 (.cons d148 (.cons d149 (.cons d150 (.cons d151 (.cons d152 (.cons d153 (.cons d154 (.cons d155 (.cons d156 (.cons d157 (.cons d158 (.cons d159 (.cons d160 (.cons d161 (.cons d162 (.cons d163 (.cons d164 (.cons d165 (.cons d166 (.cons d167 (.cons d168 (cC.trans (cR.trans (.cons d169 (.cons d170 (.cons d171 (.cons d172 (.cons d173 (.cons d174 (.cons d175 (.cons d176 (.cons d177 (.cons d178 (.cons d179 (.cons d180 (.cons d181 (.cons d182 (.cons d183 (.cons d184 (.cons d185 (.cons d186 (.cons d187 (.cons d188 (.cons d189 (.cons d190 (.cons d191 (.cons d192 (.cons dg4 (.single dg5)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), ?_, spf, ?_, ?_, ?_⟩
  · rw [pc5, ug4.oldReg u192.self.zero ra (by decide), add_lit_zero, finra, hra, hret]
  · intro q hq
    rcases hmem q hq with rfl | rfl | rfl | rfl | rfl | rfl | h
    · rw [regs5, ug4.self.zero, hz]
    · rw [kf _ (by decide), finra]
    · rw [spf, hsp]
    · rw [kf _ (by decide), fins0]
    · rw [kf _ (by decide), fins1]
    · rw [kf _ (by decide), fins2]
    · have hs : q ≠ sp := fun e => by subst e; exact absurd h (by decide)
      rw [kf q hs, pass q h]
  · rw [mem5, ← hB188, ← hB187, ← hB186, ← hB185, ← hB184, ← hB183, ← hB182, ← hB181, ← hB180, ← hB179, wordsAt_st10]
    have hw : wordsAt Mr (F + BitVec.ofNat 32 8) 10 = [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9] := by
      rw [← hR0, ← hR1, ← hR2, ← hR3, ← hR4, ← hR5, ← hR6, ← hR7, ← hR8, ← hR9]; rfl
    rw [← hw, outR]
    have uz0 : u64At B166 (F + 0x30) 0 = ((((X0 + (0x40000000 + 0xFFFFFFF0)) - Y0) + 0xFFFFFEE0)).toNat := by
      unfold u64At
      rw [show F + 0x30 + BitVec.ofNat 32 (8 * 0) = F + 0x30 by rw [BitVec.add_assoc]; rfl,
        show F + 0x30 + BitVec.ofNat 32 (8 * 0 + 4) = F + 0x34 by rw [BitVec.add_assoc]; rfl,
        (show memLoad32 B166 (F + 0x30) = (((X0 + (0x40000000 + 0xFFFFFFF0)) - Y0) + 0xFFFFFEE0) from (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x30) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x30) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x30) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x30) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x30) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x30) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x30) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x30) (k := 4) (by decide) (by decide) (by decide)), ← hB162, memLoad32_store32_sep (show Sep (F + 0x6C) 4 (F + 0x30) 4 from sep_offsets F (c := 0x6C) (n := 4) (d := 0x30) (k := 4) (by decide) (by decide) (by decide)), ← hB161, memLoad32_store32_sep (show Sep (F + 0x68) 4 (F + 0x30) 4 from sep_offsets F (c := 0x68) (n := 4) (d := 0x30) (k := 4) (by decide) (by decide) (by decide)), ← hB160, memLoad32_store32_sep (show Sep (F + 0x64) 4 (F + 0x30) 4 from sep_offsets F (c := 0x64) (n := 4) (d := 0x30) (k := 4) (by decide) (by decide) (by decide)), ← hB159, memLoad32_store32_sep (show Sep (F + 0x60) 4 (F + 0x30) 4 from sep_offsets F (c := 0x60) (n := 4) (d := 0x30) (k := 4) (by decide) (by decide) (by decide)), ← hB158, memLoad32_store32_sep (show Sep (F + 0x5C) 4 (F + 0x30) 4 from sep_offsets F (c := 0x5C) (n := 4) (d := 0x30) (k := 4) (by decide) (by decide) (by decide)), ← hB157, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x30) 4 from sep_offsets F (c := 0x58) (n := 4) (d := 0x30) (k := 4) (by decide) (by decide) (by decide)), ← hB156, memLoad32_store32_sep (show Sep (F + 0x54) 4 (F + 0x30) 4 from sep_offsets F (c := 0x54) (n := 4) (d := 0x30) (k := 4) (by decide) (by decide) (by decide)), ← hB155, memLoad32_store32_sep (show Sep (F + 0x50) 4 (F + 0x30) 4 from sep_offsets F (c := 0x50) (n := 4) (d := 0x30) (k := 4) (by decide) (by decide) (by decide)), ← hB154, memLoad32_store32_sep (show Sep (F + 0x4C) 4 (F + 0x30) 4 from sep_offsets F (c := 0x4C) (n := 4) (d := 0x30) (k := 4) (by decide) (by decide) (by decide)), ← hB153, memLoad32_store32_sep (show Sep (F + 0x48) 4 (F + 0x30) 4 from sep_offsets F (c := 0x48) (n := 4) (d := 0x30) (k := 4) (by decide) (by decide) (by decide)), ← hB152, memLoad32_store32_sep (show Sep (F + 0x44) 4 (F + 0x30) 4 from sep_offsets F (c := 0x44) (n := 4) (d := 0x30) (k := 4) (by decide) (by decide) (by decide)), ← hB151, memLoad32_store32_sep (show Sep (F + 0x40) 4 (F + 0x30) 4 from sep_offsets F (c := 0x40) (n := 4) (d := 0x30) (k := 4) (by decide) (by decide) (by decide)), ← hB150, memLoad32_store32_sep (show Sep (F + 0x3C) 4 (F + 0x30) 4 from sep_offsets F (c := 0x3C) (n := 4) (d := 0x30) (k := 4) (by decide) (by decide) (by decide)), ← hB149, memLoad32_store32_sep (show Sep (F + 0x38) 4 (F + 0x30) 4 from sep_offsets F (c := 0x38) (n := 4) (d := 0x30) (k := 4) (by decide) (by decide) (by decide)), ← hB148, memLoad32_store32_sep (show Sep (F + 0x34) 4 (F + 0x30) 4 from sep_offsets F (c := 0x34) (n := 4) (d := 0x30) (k := 4) (by decide) (by decide) (by decide))]; exact (by rw [← hB147, memLoad32_store32_same]))),
        (show memLoad32 B166 (F + 0x34) = 0 from (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x34) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x34) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x34) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x34) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x34) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x34) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x34) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x34) (k := 4) (by decide) (by decide) (by decide)), ← hB162, memLoad32_store32_sep (show Sep (F + 0x6C) 4 (F + 0x34) 4 from sep_offsets F (c := 0x6C) (n := 4) (d := 0x34) (k := 4) (by decide) (by decide) (by decide)), ← hB161, memLoad32_store32_sep (show Sep (F + 0x68) 4 (F + 0x34) 4 from sep_offsets F (c := 0x68) (n := 4) (d := 0x34) (k := 4) (by decide) (by decide) (by decide)), ← hB160, memLoad32_store32_sep (show Sep (F + 0x64) 4 (F + 0x34) 4 from sep_offsets F (c := 0x64) (n := 4) (d := 0x34) (k := 4) (by decide) (by decide) (by decide)), ← hB159, memLoad32_store32_sep (show Sep (F + 0x60) 4 (F + 0x34) 4 from sep_offsets F (c := 0x60) (n := 4) (d := 0x34) (k := 4) (by decide) (by decide) (by decide)), ← hB158, memLoad32_store32_sep (show Sep (F + 0x5C) 4 (F + 0x34) 4 from sep_offsets F (c := 0x5C) (n := 4) (d := 0x34) (k := 4) (by decide) (by decide) (by decide)), ← hB157, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x34) 4 from sep_offsets F (c := 0x58) (n := 4) (d := 0x34) (k := 4) (by decide) (by decide) (by decide)), ← hB156, memLoad32_store32_sep (show Sep (F + 0x54) 4 (F + 0x34) 4 from sep_offsets F (c := 0x54) (n := 4) (d := 0x34) (k := 4) (by decide) (by decide) (by decide)), ← hB155, memLoad32_store32_sep (show Sep (F + 0x50) 4 (F + 0x34) 4 from sep_offsets F (c := 0x50) (n := 4) (d := 0x34) (k := 4) (by decide) (by decide) (by decide)), ← hB154, memLoad32_store32_sep (show Sep (F + 0x4C) 4 (F + 0x34) 4 from sep_offsets F (c := 0x4C) (n := 4) (d := 0x34) (k := 4) (by decide) (by decide) (by decide)), ← hB153, memLoad32_store32_sep (show Sep (F + 0x48) 4 (F + 0x34) 4 from sep_offsets F (c := 0x48) (n := 4) (d := 0x34) (k := 4) (by decide) (by decide) (by decide)), ← hB152, memLoad32_store32_sep (show Sep (F + 0x44) 4 (F + 0x34) 4 from sep_offsets F (c := 0x44) (n := 4) (d := 0x34) (k := 4) (by decide) (by decide) (by decide)), ← hB151, memLoad32_store32_sep (show Sep (F + 0x40) 4 (F + 0x34) 4 from sep_offsets F (c := 0x40) (n := 4) (d := 0x34) (k := 4) (by decide) (by decide) (by decide)), ← hB150, memLoad32_store32_sep (show Sep (F + 0x3C) 4 (F + 0x34) 4 from sep_offsets F (c := 0x3C) (n := 4) (d := 0x34) (k := 4) (by decide) (by decide) (by decide)), ← hB149, memLoad32_store32_sep (show Sep (F + 0x38) 4 (F + 0x34) 4 from sep_offsets F (c := 0x38) (n := 4) (d := 0x34) (k := 4) (by decide) (by decide) (by decide))]; exact (by rw [← hB148, memLoad32_store32_same])))]
      rw [show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    have uz1 : u64At B166 (F + 0x30) 1 = (((X1 + (0x20000000 + 0xFFFFFFF0)) - Y1)).toNat := by
      unfold u64At
      rw [show F + 0x30 + BitVec.ofNat 32 (8 * 1) = F + 0x38 by rw [BitVec.add_assoc]; rfl,
        show F + 0x30 + BitVec.ofNat 32 (8 * 1 + 4) = F + 0x3C by rw [BitVec.add_assoc]; rfl,
        (show memLoad32 B166 (F + 0x38) = ((X1 + (0x20000000 + 0xFFFFFFF0)) - Y1) from (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x38) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x38) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x38) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x38) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x38) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x38) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x38) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x38) (k := 4) (by decide) (by decide) (by decide)), ← hB162, memLoad32_store32_sep (show Sep (F + 0x6C) 4 (F + 0x38) 4 from sep_offsets F (c := 0x6C) (n := 4) (d := 0x38) (k := 4) (by decide) (by decide) (by decide)), ← hB161, memLoad32_store32_sep (show Sep (F + 0x68) 4 (F + 0x38) 4 from sep_offsets F (c := 0x68) (n := 4) (d := 0x38) (k := 4) (by decide) (by decide) (by decide)), ← hB160, memLoad32_store32_sep (show Sep (F + 0x64) 4 (F + 0x38) 4 from sep_offsets F (c := 0x64) (n := 4) (d := 0x38) (k := 4) (by decide) (by decide) (by decide)), ← hB159, memLoad32_store32_sep (show Sep (F + 0x60) 4 (F + 0x38) 4 from sep_offsets F (c := 0x60) (n := 4) (d := 0x38) (k := 4) (by decide) (by decide) (by decide)), ← hB158, memLoad32_store32_sep (show Sep (F + 0x5C) 4 (F + 0x38) 4 from sep_offsets F (c := 0x5C) (n := 4) (d := 0x38) (k := 4) (by decide) (by decide) (by decide)), ← hB157, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x38) 4 from sep_offsets F (c := 0x58) (n := 4) (d := 0x38) (k := 4) (by decide) (by decide) (by decide)), ← hB156, memLoad32_store32_sep (show Sep (F + 0x54) 4 (F + 0x38) 4 from sep_offsets F (c := 0x54) (n := 4) (d := 0x38) (k := 4) (by decide) (by decide) (by decide)), ← hB155, memLoad32_store32_sep (show Sep (F + 0x50) 4 (F + 0x38) 4 from sep_offsets F (c := 0x50) (n := 4) (d := 0x38) (k := 4) (by decide) (by decide) (by decide)), ← hB154, memLoad32_store32_sep (show Sep (F + 0x4C) 4 (F + 0x38) 4 from sep_offsets F (c := 0x4C) (n := 4) (d := 0x38) (k := 4) (by decide) (by decide) (by decide)), ← hB153, memLoad32_store32_sep (show Sep (F + 0x48) 4 (F + 0x38) 4 from sep_offsets F (c := 0x48) (n := 4) (d := 0x38) (k := 4) (by decide) (by decide) (by decide)), ← hB152, memLoad32_store32_sep (show Sep (F + 0x44) 4 (F + 0x38) 4 from sep_offsets F (c := 0x44) (n := 4) (d := 0x38) (k := 4) (by decide) (by decide) (by decide)), ← hB151, memLoad32_store32_sep (show Sep (F + 0x40) 4 (F + 0x38) 4 from sep_offsets F (c := 0x40) (n := 4) (d := 0x38) (k := 4) (by decide) (by decide) (by decide)), ← hB150, memLoad32_store32_sep (show Sep (F + 0x3C) 4 (F + 0x38) 4 from sep_offsets F (c := 0x3C) (n := 4) (d := 0x38) (k := 4) (by decide) (by decide) (by decide))]; exact (by rw [← hB149, memLoad32_store32_same]))),
        (show memLoad32 B166 (F + 0x3C) = 0 from (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x3C) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x3C) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x3C) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x3C) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x3C) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x3C) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x3C) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x3C) (k := 4) (by decide) (by decide) (by decide)), ← hB162, memLoad32_store32_sep (show Sep (F + 0x6C) 4 (F + 0x3C) 4 from sep_offsets F (c := 0x6C) (n := 4) (d := 0x3C) (k := 4) (by decide) (by decide) (by decide)), ← hB161, memLoad32_store32_sep (show Sep (F + 0x68) 4 (F + 0x3C) 4 from sep_offsets F (c := 0x68) (n := 4) (d := 0x3C) (k := 4) (by decide) (by decide) (by decide)), ← hB160, memLoad32_store32_sep (show Sep (F + 0x64) 4 (F + 0x3C) 4 from sep_offsets F (c := 0x64) (n := 4) (d := 0x3C) (k := 4) (by decide) (by decide) (by decide)), ← hB159, memLoad32_store32_sep (show Sep (F + 0x60) 4 (F + 0x3C) 4 from sep_offsets F (c := 0x60) (n := 4) (d := 0x3C) (k := 4) (by decide) (by decide) (by decide)), ← hB158, memLoad32_store32_sep (show Sep (F + 0x5C) 4 (F + 0x3C) 4 from sep_offsets F (c := 0x5C) (n := 4) (d := 0x3C) (k := 4) (by decide) (by decide) (by decide)), ← hB157, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x3C) 4 from sep_offsets F (c := 0x58) (n := 4) (d := 0x3C) (k := 4) (by decide) (by decide) (by decide)), ← hB156, memLoad32_store32_sep (show Sep (F + 0x54) 4 (F + 0x3C) 4 from sep_offsets F (c := 0x54) (n := 4) (d := 0x3C) (k := 4) (by decide) (by decide) (by decide)), ← hB155, memLoad32_store32_sep (show Sep (F + 0x50) 4 (F + 0x3C) 4 from sep_offsets F (c := 0x50) (n := 4) (d := 0x3C) (k := 4) (by decide) (by decide) (by decide)), ← hB154, memLoad32_store32_sep (show Sep (F + 0x4C) 4 (F + 0x3C) 4 from sep_offsets F (c := 0x4C) (n := 4) (d := 0x3C) (k := 4) (by decide) (by decide) (by decide)), ← hB153, memLoad32_store32_sep (show Sep (F + 0x48) 4 (F + 0x3C) 4 from sep_offsets F (c := 0x48) (n := 4) (d := 0x3C) (k := 4) (by decide) (by decide) (by decide)), ← hB152, memLoad32_store32_sep (show Sep (F + 0x44) 4 (F + 0x3C) 4 from sep_offsets F (c := 0x44) (n := 4) (d := 0x3C) (k := 4) (by decide) (by decide) (by decide)), ← hB151, memLoad32_store32_sep (show Sep (F + 0x40) 4 (F + 0x3C) 4 from sep_offsets F (c := 0x40) (n := 4) (d := 0x3C) (k := 4) (by decide) (by decide) (by decide))]; exact (by rw [← hB150, memLoad32_store32_same])))]
      rw [show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    have uz2 : u64At B166 (F + 0x30) 2 = (((X2 + (0x40000000 + 0xFFFFFFF0)) - Y2)).toNat := by
      unfold u64At
      rw [show F + 0x30 + BitVec.ofNat 32 (8 * 2) = F + 0x40 by rw [BitVec.add_assoc]; rfl,
        show F + 0x30 + BitVec.ofNat 32 (8 * 2 + 4) = F + 0x44 by rw [BitVec.add_assoc]; rfl,
        (show memLoad32 B166 (F + 0x40) = ((X2 + (0x40000000 + 0xFFFFFFF0)) - Y2) from (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x40) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x40) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x40) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x40) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x40) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x40) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x40) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x40) (k := 4) (by decide) (by decide) (by decide)), ← hB162, memLoad32_store32_sep (show Sep (F + 0x6C) 4 (F + 0x40) 4 from sep_offsets F (c := 0x6C) (n := 4) (d := 0x40) (k := 4) (by decide) (by decide) (by decide)), ← hB161, memLoad32_store32_sep (show Sep (F + 0x68) 4 (F + 0x40) 4 from sep_offsets F (c := 0x68) (n := 4) (d := 0x40) (k := 4) (by decide) (by decide) (by decide)), ← hB160, memLoad32_store32_sep (show Sep (F + 0x64) 4 (F + 0x40) 4 from sep_offsets F (c := 0x64) (n := 4) (d := 0x40) (k := 4) (by decide) (by decide) (by decide)), ← hB159, memLoad32_store32_sep (show Sep (F + 0x60) 4 (F + 0x40) 4 from sep_offsets F (c := 0x60) (n := 4) (d := 0x40) (k := 4) (by decide) (by decide) (by decide)), ← hB158, memLoad32_store32_sep (show Sep (F + 0x5C) 4 (F + 0x40) 4 from sep_offsets F (c := 0x5C) (n := 4) (d := 0x40) (k := 4) (by decide) (by decide) (by decide)), ← hB157, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x40) 4 from sep_offsets F (c := 0x58) (n := 4) (d := 0x40) (k := 4) (by decide) (by decide) (by decide)), ← hB156, memLoad32_store32_sep (show Sep (F + 0x54) 4 (F + 0x40) 4 from sep_offsets F (c := 0x54) (n := 4) (d := 0x40) (k := 4) (by decide) (by decide) (by decide)), ← hB155, memLoad32_store32_sep (show Sep (F + 0x50) 4 (F + 0x40) 4 from sep_offsets F (c := 0x50) (n := 4) (d := 0x40) (k := 4) (by decide) (by decide) (by decide)), ← hB154, memLoad32_store32_sep (show Sep (F + 0x4C) 4 (F + 0x40) 4 from sep_offsets F (c := 0x4C) (n := 4) (d := 0x40) (k := 4) (by decide) (by decide) (by decide)), ← hB153, memLoad32_store32_sep (show Sep (F + 0x48) 4 (F + 0x40) 4 from sep_offsets F (c := 0x48) (n := 4) (d := 0x40) (k := 4) (by decide) (by decide) (by decide)), ← hB152, memLoad32_store32_sep (show Sep (F + 0x44) 4 (F + 0x40) 4 from sep_offsets F (c := 0x44) (n := 4) (d := 0x40) (k := 4) (by decide) (by decide) (by decide))]; exact (by rw [← hB151, memLoad32_store32_same]))),
        (show memLoad32 B166 (F + 0x44) = 0 from (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x44) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x44) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x44) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x44) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x44) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x44) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x44) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x44) (k := 4) (by decide) (by decide) (by decide)), ← hB162, memLoad32_store32_sep (show Sep (F + 0x6C) 4 (F + 0x44) 4 from sep_offsets F (c := 0x6C) (n := 4) (d := 0x44) (k := 4) (by decide) (by decide) (by decide)), ← hB161, memLoad32_store32_sep (show Sep (F + 0x68) 4 (F + 0x44) 4 from sep_offsets F (c := 0x68) (n := 4) (d := 0x44) (k := 4) (by decide) (by decide) (by decide)), ← hB160, memLoad32_store32_sep (show Sep (F + 0x64) 4 (F + 0x44) 4 from sep_offsets F (c := 0x64) (n := 4) (d := 0x44) (k := 4) (by decide) (by decide) (by decide)), ← hB159, memLoad32_store32_sep (show Sep (F + 0x60) 4 (F + 0x44) 4 from sep_offsets F (c := 0x60) (n := 4) (d := 0x44) (k := 4) (by decide) (by decide) (by decide)), ← hB158, memLoad32_store32_sep (show Sep (F + 0x5C) 4 (F + 0x44) 4 from sep_offsets F (c := 0x5C) (n := 4) (d := 0x44) (k := 4) (by decide) (by decide) (by decide)), ← hB157, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x44) 4 from sep_offsets F (c := 0x58) (n := 4) (d := 0x44) (k := 4) (by decide) (by decide) (by decide)), ← hB156, memLoad32_store32_sep (show Sep (F + 0x54) 4 (F + 0x44) 4 from sep_offsets F (c := 0x54) (n := 4) (d := 0x44) (k := 4) (by decide) (by decide) (by decide)), ← hB155, memLoad32_store32_sep (show Sep (F + 0x50) 4 (F + 0x44) 4 from sep_offsets F (c := 0x50) (n := 4) (d := 0x44) (k := 4) (by decide) (by decide) (by decide)), ← hB154, memLoad32_store32_sep (show Sep (F + 0x4C) 4 (F + 0x44) 4 from sep_offsets F (c := 0x4C) (n := 4) (d := 0x44) (k := 4) (by decide) (by decide) (by decide)), ← hB153, memLoad32_store32_sep (show Sep (F + 0x48) 4 (F + 0x44) 4 from sep_offsets F (c := 0x48) (n := 4) (d := 0x44) (k := 4) (by decide) (by decide) (by decide))]; exact (by rw [← hB152, memLoad32_store32_same])))]
      rw [show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    have uz3 : u64At B166 (F + 0x30) 3 = (((X3 + (0x20000000 + 0xFFFFFFF0)) - Y3)).toNat := by
      unfold u64At
      rw [show F + 0x30 + BitVec.ofNat 32 (8 * 3) = F + 0x48 by rw [BitVec.add_assoc]; rfl,
        show F + 0x30 + BitVec.ofNat 32 (8 * 3 + 4) = F + 0x4C by rw [BitVec.add_assoc]; rfl,
        (show memLoad32 B166 (F + 0x48) = ((X3 + (0x20000000 + 0xFFFFFFF0)) - Y3) from (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x48) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x48) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x48) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x48) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x48) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x48) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x48) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x48) (k := 4) (by decide) (by decide) (by decide)), ← hB162, memLoad32_store32_sep (show Sep (F + 0x6C) 4 (F + 0x48) 4 from sep_offsets F (c := 0x6C) (n := 4) (d := 0x48) (k := 4) (by decide) (by decide) (by decide)), ← hB161, memLoad32_store32_sep (show Sep (F + 0x68) 4 (F + 0x48) 4 from sep_offsets F (c := 0x68) (n := 4) (d := 0x48) (k := 4) (by decide) (by decide) (by decide)), ← hB160, memLoad32_store32_sep (show Sep (F + 0x64) 4 (F + 0x48) 4 from sep_offsets F (c := 0x64) (n := 4) (d := 0x48) (k := 4) (by decide) (by decide) (by decide)), ← hB159, memLoad32_store32_sep (show Sep (F + 0x60) 4 (F + 0x48) 4 from sep_offsets F (c := 0x60) (n := 4) (d := 0x48) (k := 4) (by decide) (by decide) (by decide)), ← hB158, memLoad32_store32_sep (show Sep (F + 0x5C) 4 (F + 0x48) 4 from sep_offsets F (c := 0x5C) (n := 4) (d := 0x48) (k := 4) (by decide) (by decide) (by decide)), ← hB157, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x48) 4 from sep_offsets F (c := 0x58) (n := 4) (d := 0x48) (k := 4) (by decide) (by decide) (by decide)), ← hB156, memLoad32_store32_sep (show Sep (F + 0x54) 4 (F + 0x48) 4 from sep_offsets F (c := 0x54) (n := 4) (d := 0x48) (k := 4) (by decide) (by decide) (by decide)), ← hB155, memLoad32_store32_sep (show Sep (F + 0x50) 4 (F + 0x48) 4 from sep_offsets F (c := 0x50) (n := 4) (d := 0x48) (k := 4) (by decide) (by decide) (by decide)), ← hB154, memLoad32_store32_sep (show Sep (F + 0x4C) 4 (F + 0x48) 4 from sep_offsets F (c := 0x4C) (n := 4) (d := 0x48) (k := 4) (by decide) (by decide) (by decide))]; exact (by rw [← hB153, memLoad32_store32_same]))),
        (show memLoad32 B166 (F + 0x4C) = 0 from (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x4C) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x4C) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x4C) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x4C) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x4C) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x4C) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x4C) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x4C) (k := 4) (by decide) (by decide) (by decide)), ← hB162, memLoad32_store32_sep (show Sep (F + 0x6C) 4 (F + 0x4C) 4 from sep_offsets F (c := 0x6C) (n := 4) (d := 0x4C) (k := 4) (by decide) (by decide) (by decide)), ← hB161, memLoad32_store32_sep (show Sep (F + 0x68) 4 (F + 0x4C) 4 from sep_offsets F (c := 0x68) (n := 4) (d := 0x4C) (k := 4) (by decide) (by decide) (by decide)), ← hB160, memLoad32_store32_sep (show Sep (F + 0x64) 4 (F + 0x4C) 4 from sep_offsets F (c := 0x64) (n := 4) (d := 0x4C) (k := 4) (by decide) (by decide) (by decide)), ← hB159, memLoad32_store32_sep (show Sep (F + 0x60) 4 (F + 0x4C) 4 from sep_offsets F (c := 0x60) (n := 4) (d := 0x4C) (k := 4) (by decide) (by decide) (by decide)), ← hB158, memLoad32_store32_sep (show Sep (F + 0x5C) 4 (F + 0x4C) 4 from sep_offsets F (c := 0x5C) (n := 4) (d := 0x4C) (k := 4) (by decide) (by decide) (by decide)), ← hB157, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x4C) 4 from sep_offsets F (c := 0x58) (n := 4) (d := 0x4C) (k := 4) (by decide) (by decide) (by decide)), ← hB156, memLoad32_store32_sep (show Sep (F + 0x54) 4 (F + 0x4C) 4 from sep_offsets F (c := 0x54) (n := 4) (d := 0x4C) (k := 4) (by decide) (by decide) (by decide)), ← hB155, memLoad32_store32_sep (show Sep (F + 0x50) 4 (F + 0x4C) 4 from sep_offsets F (c := 0x50) (n := 4) (d := 0x4C) (k := 4) (by decide) (by decide) (by decide))]; exact (by rw [← hB154, memLoad32_store32_same])))]
      rw [show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    have uz4 : u64At B166 (F + 0x30) 4 = (((X4 + (0x40000000 + 0xFFFFFFF0)) - Y4)).toNat := by
      unfold u64At
      rw [show F + 0x30 + BitVec.ofNat 32 (8 * 4) = F + 0x50 by rw [BitVec.add_assoc]; rfl,
        show F + 0x30 + BitVec.ofNat 32 (8 * 4 + 4) = F + 0x54 by rw [BitVec.add_assoc]; rfl,
        (show memLoad32 B166 (F + 0x50) = ((X4 + (0x40000000 + 0xFFFFFFF0)) - Y4) from (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x50) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x50) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x50) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x50) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x50) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x50) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x50) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x50) (k := 4) (by decide) (by decide) (by decide)), ← hB162, memLoad32_store32_sep (show Sep (F + 0x6C) 4 (F + 0x50) 4 from sep_offsets F (c := 0x6C) (n := 4) (d := 0x50) (k := 4) (by decide) (by decide) (by decide)), ← hB161, memLoad32_store32_sep (show Sep (F + 0x68) 4 (F + 0x50) 4 from sep_offsets F (c := 0x68) (n := 4) (d := 0x50) (k := 4) (by decide) (by decide) (by decide)), ← hB160, memLoad32_store32_sep (show Sep (F + 0x64) 4 (F + 0x50) 4 from sep_offsets F (c := 0x64) (n := 4) (d := 0x50) (k := 4) (by decide) (by decide) (by decide)), ← hB159, memLoad32_store32_sep (show Sep (F + 0x60) 4 (F + 0x50) 4 from sep_offsets F (c := 0x60) (n := 4) (d := 0x50) (k := 4) (by decide) (by decide) (by decide)), ← hB158, memLoad32_store32_sep (show Sep (F + 0x5C) 4 (F + 0x50) 4 from sep_offsets F (c := 0x5C) (n := 4) (d := 0x50) (k := 4) (by decide) (by decide) (by decide)), ← hB157, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x50) 4 from sep_offsets F (c := 0x58) (n := 4) (d := 0x50) (k := 4) (by decide) (by decide) (by decide)), ← hB156, memLoad32_store32_sep (show Sep (F + 0x54) 4 (F + 0x50) 4 from sep_offsets F (c := 0x54) (n := 4) (d := 0x50) (k := 4) (by decide) (by decide) (by decide))]; exact (by rw [← hB155, memLoad32_store32_same]))),
        (show memLoad32 B166 (F + 0x54) = 0 from (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x54) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x54) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x54) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x54) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x54) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x54) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x54) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x54) (k := 4) (by decide) (by decide) (by decide)), ← hB162, memLoad32_store32_sep (show Sep (F + 0x6C) 4 (F + 0x54) 4 from sep_offsets F (c := 0x6C) (n := 4) (d := 0x54) (k := 4) (by decide) (by decide) (by decide)), ← hB161, memLoad32_store32_sep (show Sep (F + 0x68) 4 (F + 0x54) 4 from sep_offsets F (c := 0x68) (n := 4) (d := 0x54) (k := 4) (by decide) (by decide) (by decide)), ← hB160, memLoad32_store32_sep (show Sep (F + 0x64) 4 (F + 0x54) 4 from sep_offsets F (c := 0x64) (n := 4) (d := 0x54) (k := 4) (by decide) (by decide) (by decide)), ← hB159, memLoad32_store32_sep (show Sep (F + 0x60) 4 (F + 0x54) 4 from sep_offsets F (c := 0x60) (n := 4) (d := 0x54) (k := 4) (by decide) (by decide) (by decide)), ← hB158, memLoad32_store32_sep (show Sep (F + 0x5C) 4 (F + 0x54) 4 from sep_offsets F (c := 0x5C) (n := 4) (d := 0x54) (k := 4) (by decide) (by decide) (by decide)), ← hB157, memLoad32_store32_sep (show Sep (F + 0x58) 4 (F + 0x54) 4 from sep_offsets F (c := 0x58) (n := 4) (d := 0x54) (k := 4) (by decide) (by decide) (by decide))]; exact (by rw [← hB156, memLoad32_store32_same])))]
      rw [show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    have uz5 : u64At B166 (F + 0x30) 5 = (((X5 + (0x20000000 + 0xFFFFFFF0)) - Y5)).toNat := by
      unfold u64At
      rw [show F + 0x30 + BitVec.ofNat 32 (8 * 5) = F + 0x58 by rw [BitVec.add_assoc]; rfl,
        show F + 0x30 + BitVec.ofNat 32 (8 * 5 + 4) = F + 0x5C by rw [BitVec.add_assoc]; rfl,
        (show memLoad32 B166 (F + 0x58) = ((X5 + (0x20000000 + 0xFFFFFFF0)) - Y5) from (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x58) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x58) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x58) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x58) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x58) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x58) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x58) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x58) (k := 4) (by decide) (by decide) (by decide)), ← hB162, memLoad32_store32_sep (show Sep (F + 0x6C) 4 (F + 0x58) 4 from sep_offsets F (c := 0x6C) (n := 4) (d := 0x58) (k := 4) (by decide) (by decide) (by decide)), ← hB161, memLoad32_store32_sep (show Sep (F + 0x68) 4 (F + 0x58) 4 from sep_offsets F (c := 0x68) (n := 4) (d := 0x58) (k := 4) (by decide) (by decide) (by decide)), ← hB160, memLoad32_store32_sep (show Sep (F + 0x64) 4 (F + 0x58) 4 from sep_offsets F (c := 0x64) (n := 4) (d := 0x58) (k := 4) (by decide) (by decide) (by decide)), ← hB159, memLoad32_store32_sep (show Sep (F + 0x60) 4 (F + 0x58) 4 from sep_offsets F (c := 0x60) (n := 4) (d := 0x58) (k := 4) (by decide) (by decide) (by decide)), ← hB158, memLoad32_store32_sep (show Sep (F + 0x5C) 4 (F + 0x58) 4 from sep_offsets F (c := 0x5C) (n := 4) (d := 0x58) (k := 4) (by decide) (by decide) (by decide))]; exact (by rw [← hB157, memLoad32_store32_same]))),
        (show memLoad32 B166 (F + 0x5C) = 0 from (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x5C) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x5C) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x5C) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x5C) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x5C) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x5C) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x5C) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x5C) (k := 4) (by decide) (by decide) (by decide)), ← hB162, memLoad32_store32_sep (show Sep (F + 0x6C) 4 (F + 0x5C) 4 from sep_offsets F (c := 0x6C) (n := 4) (d := 0x5C) (k := 4) (by decide) (by decide) (by decide)), ← hB161, memLoad32_store32_sep (show Sep (F + 0x68) 4 (F + 0x5C) 4 from sep_offsets F (c := 0x68) (n := 4) (d := 0x5C) (k := 4) (by decide) (by decide) (by decide)), ← hB160, memLoad32_store32_sep (show Sep (F + 0x64) 4 (F + 0x5C) 4 from sep_offsets F (c := 0x64) (n := 4) (d := 0x5C) (k := 4) (by decide) (by decide) (by decide)), ← hB159, memLoad32_store32_sep (show Sep (F + 0x60) 4 (F + 0x5C) 4 from sep_offsets F (c := 0x60) (n := 4) (d := 0x5C) (k := 4) (by decide) (by decide) (by decide))]; exact (by rw [← hB158, memLoad32_store32_same])))]
      rw [show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    have uz6 : u64At B166 (F + 0x30) 6 = (((X6 + (0x40000000 + 0xFFFFFFF0)) - Y6)).toNat := by
      unfold u64At
      rw [show F + 0x30 + BitVec.ofNat 32 (8 * 6) = F + 0x60 by rw [BitVec.add_assoc]; rfl,
        show F + 0x30 + BitVec.ofNat 32 (8 * 6 + 4) = F + 0x64 by rw [BitVec.add_assoc]; rfl,
        (show memLoad32 B166 (F + 0x60) = ((X6 + (0x40000000 + 0xFFFFFFF0)) - Y6) from (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x60) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x60) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x60) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x60) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x60) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x60) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x60) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x60) (k := 4) (by decide) (by decide) (by decide)), ← hB162, memLoad32_store32_sep (show Sep (F + 0x6C) 4 (F + 0x60) 4 from sep_offsets F (c := 0x6C) (n := 4) (d := 0x60) (k := 4) (by decide) (by decide) (by decide)), ← hB161, memLoad32_store32_sep (show Sep (F + 0x68) 4 (F + 0x60) 4 from sep_offsets F (c := 0x68) (n := 4) (d := 0x60) (k := 4) (by decide) (by decide) (by decide)), ← hB160, memLoad32_store32_sep (show Sep (F + 0x64) 4 (F + 0x60) 4 from sep_offsets F (c := 0x64) (n := 4) (d := 0x60) (k := 4) (by decide) (by decide) (by decide))]; exact (by rw [← hB159, memLoad32_store32_same]))),
        (show memLoad32 B166 (F + 0x64) = 0 from (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x64) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x64) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x64) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x64) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x64) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x64) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x64) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x64) (k := 4) (by decide) (by decide) (by decide)), ← hB162, memLoad32_store32_sep (show Sep (F + 0x6C) 4 (F + 0x64) 4 from sep_offsets F (c := 0x6C) (n := 4) (d := 0x64) (k := 4) (by decide) (by decide) (by decide)), ← hB161, memLoad32_store32_sep (show Sep (F + 0x68) 4 (F + 0x64) 4 from sep_offsets F (c := 0x68) (n := 4) (d := 0x64) (k := 4) (by decide) (by decide) (by decide))]; exact (by rw [← hB160, memLoad32_store32_same])))]
      rw [show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    have uz7 : u64At B166 (F + 0x30) 7 = (((X7 + (0x20000000 + 0xFFFFFFF0)) - Y7)).toNat := by
      unfold u64At
      rw [show F + 0x30 + BitVec.ofNat 32 (8 * 7) = F + 0x68 by rw [BitVec.add_assoc]; rfl,
        show F + 0x30 + BitVec.ofNat 32 (8 * 7 + 4) = F + 0x6C by rw [BitVec.add_assoc]; rfl,
        (show memLoad32 B166 (F + 0x68) = ((X7 + (0x20000000 + 0xFFFFFFF0)) - Y7) from (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x68) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x68) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x68) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x68) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x68) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x68) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x68) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x68) (k := 4) (by decide) (by decide) (by decide)), ← hB162, memLoad32_store32_sep (show Sep (F + 0x6C) 4 (F + 0x68) 4 from sep_offsets F (c := 0x6C) (n := 4) (d := 0x68) (k := 4) (by decide) (by decide) (by decide))]; exact (by rw [← hB161, memLoad32_store32_same]))),
        (show memLoad32 B166 (F + 0x6C) = 0 from (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x6C) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x6C) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x6C) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x6C) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x6C) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x6C) (k := 4) (by decide) (by decide) (by decide)), ← hB163, memLoad32_store32_sep (show Sep (F + 0x70) 4 (F + 0x6C) 4 from sep_offsets F (c := 0x70) (n := 4) (d := 0x6C) (k := 4) (by decide) (by decide) (by decide))]; exact (by rw [← hB162, memLoad32_store32_same])))]
      rw [show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    have uz8 : u64At B166 (F + 0x30) 8 = (((X8 + (0x40000000 + 0xFFFFFFF0)) - Y8)).toNat := by
      unfold u64At
      rw [show F + 0x30 + BitVec.ofNat 32 (8 * 8) = F + 0x70 by rw [BitVec.add_assoc]; rfl,
        show F + 0x30 + BitVec.ofNat 32 (8 * 8 + 4) = F + 0x74 by rw [BitVec.add_assoc]; rfl,
        (show memLoad32 B166 (F + 0x70) = ((X8 + (0x40000000 + 0xFFFFFFF0)) - Y8) from (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x70) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x70) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x70) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x70) (k := 4) (by decide) (by decide) (by decide)), ← hB164, memLoad32_store32_sep (show Sep (F + 0x74) 4 (F + 0x70) 4 from sep_offsets F (c := 0x74) (n := 4) (d := 0x70) (k := 4) (by decide) (by decide) (by decide))]; exact (by rw [← hB163, memLoad32_store32_same]))),
        (show memLoad32 B166 (F + 0x74) = 0 from (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x74) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x74) (k := 4) (by decide) (by decide) (by decide)), ← hB165, memLoad32_store32_sep (show Sep (F + 0x78) 4 (F + 0x74) 4 from sep_offsets F (c := 0x78) (n := 4) (d := 0x74) (k := 4) (by decide) (by decide) (by decide))]; exact (by rw [← hB164, memLoad32_store32_same])))]
      rw [show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    have uz9 : u64At B166 (F + 0x30) 9 = (((X9 + (0x20000000 + 0xFFFFFFF0)) - Y9)).toNat := by
      unfold u64At
      rw [show F + 0x30 + BitVec.ofNat 32 (8 * 9) = F + 0x78 by rw [BitVec.add_assoc]; rfl,
        show F + 0x30 + BitVec.ofNat 32 (8 * 9 + 4) = F + 0x7C by rw [BitVec.add_assoc]; rfl,
        (show memLoad32 B166 (F + 0x78) = ((X9 + (0x20000000 + 0xFFFFFFF0)) - Y9) from (by rw [← hB166, memLoad32_store32_sep (show Sep (F + 0x7C) 4 (F + 0x78) 4 from sep_offsets F (c := 0x7C) (n := 4) (d := 0x78) (k := 4) (by decide) (by decide) (by decide))]; exact (by rw [← hB165, memLoad32_store32_same]))),
        (show memLoad32 B166 (F + 0x7C) = 0 from (by rw [← hB166, memLoad32_store32_same]))]
      rw [show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    rw [uz0, uz1, uz2, uz3, uz4, uz5, uz6, uz7, uz8, uz9]
    subst hX0 hX1 hX2 hX3 hX4 hX5 hX6 hX7 hX8 hX9 hY0 hY1 hY2 hY3 hY4 hY5 hY6 hY7 hY8 hY9
    rw [fsb_l0]
    rfl
  · intro x hx ho
    rw [mem5, ← hB188, memStore32_get_sep (show Sep (out + 0x24) 4 x 1 from ho.sub (c := 0x24) (l := 4) (by decide)), ← hB187, memStore32_get_sep (show Sep (out + 0x20) 4 x 1 from ho.sub (c := 0x20) (l := 4) (by decide)), ← hB186, memStore32_get_sep (show Sep (out + 0x1C) 4 x 1 from ho.sub (c := 0x1C) (l := 4) (by decide)), ← hB185, memStore32_get_sep (show Sep (out + 0x18) 4 x 1 from ho.sub (c := 0x18) (l := 4) (by decide)), ← hB184, memStore32_get_sep (show Sep (out + 0x14) 4 x 1 from ho.sub (c := 0x14) (l := 4) (by decide)), ← hB183, memStore32_get_sep (show Sep (out + 0x10) 4 x 1 from ho.sub (c := 0x10) (l := 4) (by decide)), ← hB182, memStore32_get_sep (show Sep (out + 0xC) 4 x 1 from ho.sub (c := 0xC) (l := 4) (by decide)), ← hB181, memStore32_get_sep (show Sep (out + 0x8) 4 x 1 from ho.sub (c := 0x8) (l := 4) (by decide)), ← hB180, memStore32_get_sep (show Sep (out + 0x4) 4 x 1 from ho.sub (c := 0x4) (l := 4) (by decide)), ← hB179, memStore32_get_sep (show Sep (out + 0x0) 4 x 1 from ho.sub (c := 0x0) (l := 4) (by decide)), frRG x hx]

end C3.RV32
