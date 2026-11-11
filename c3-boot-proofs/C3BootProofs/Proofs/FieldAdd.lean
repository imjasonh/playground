import C3BootProofs.Proofs.FieldSubOp
import C3BootProofs.Image.BootloaderV0

/-! # `field_impl::add`, as compiled -/

namespace C3.RV32

open C3.ImageV0

theorem limbFlat8 (a0 a1 a2 a3 a4 a5 a6 a7 : Word) :
    limbVal [a0, a1, a2, a3, a4, a5, a6, a7] =
      2 ^ 0 * a0.toNat + 2 ^ 32 * a1.toNat + 2 ^ 64 * a2.toNat + 2 ^ 96 * a3.toNat + 2 ^ 128 * a4.toNat +
      2 ^ 160 * a5.toNat + 2 ^ 192 * a6.toNat + 2 ^ 224 * a7.toNat := by
  simp only [limbVal, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add, Nat.mul_zero, Nat.add_zero]
  omega

set_option exponentiation.threshold 300 in
/-- `field_impl::add` modulo `p`, for operands below `p`. -/
theorem subRes_add {A B : Nat} (hA : A < p256) (hB : B < p256) : subRes (A + B) = (A + B) % p256 := by
  unfold subRes
  have h256 : p256 < 2 ^ 256 := by decide
  by_cases h : A + B < p256
  · rw [ite_eq_left h, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h]
  · rw [ite_eq_right h, Nat.mod_eq_of_lt (by omega)]
    rw [show A + B = (A + B - p256) + p256 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- Where `field_impl::add` runs: `FSEnv`'s layout, with `field_impl::add`'s
code at `P` and `sub_inner`'s where the image puts it relative to that. -/
structure FAEnv (M : Word → BitVec 8) (P sp0 res ap bp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P fieldAddCode
  sicode : CodeIn M (P + 0xFFFFFCAA) subInnerCode
  bsub : CodeIn M (siBsub (P + 0xFFFFFCAA)) borrowingSubCode
  sisave : CodeIn M (P + 0xFFFFFCAA + 0xDC34) subInnerSaveCode
  sirestore : CodeIn M (P + 0xFFFFFCAA + 0xDE3E) subInnerRestoreCode
  hsp : sp0.toNat % 4 = 0
  hres : res.toNat % 4 = 0
  hap : ap.toNat % 4 = 0
  hbp : bp.toNat % 4 = 0
  hS : 0xB4 ≤ sp0.toNat
  hwr : res.toNat + 32 ≤ 2 ^ 32
  sC : Sep (sp0 + 0xFFFFFF4C) 0xB4 P fieldAddCode.length
  sI : Sep (sp0 + 0xFFFFFF4C) 0xB4 (P + 0xFFFFFCAA) subInnerCode.length
  sIb : Sep (sp0 + 0xFFFFFF4C) 0xB4 (siBsub (P + 0xFFFFFCAA)) borrowingSubCode.length
  sIs : Sep (sp0 + 0xFFFFFF4C) 0xB4 (P + 0xFFFFFCAA + 0xDC34) subInnerSaveCode.length
  sIr : Sep (sp0 + 0xFFFFFF4C) 0xB4 (P + 0xFFFFFCAA + 0xDE3E) subInnerRestoreCode.length
  sRS : Sep res 32 (sp0 + 0xFFFFFF4C) 0xB4
  sRC : Sep res 32 P fieldAddCode.length
  sAS : Sep ap 32 (sp0 + 0xFFFFFF4C) 0xB4
  sBS : Sep bp 32 (sp0 + 0xFFFFFF4C) 0xB4

set_option maxHeartbeats 8000000 in
/-- **The compiled `field_impl::add`**, called with the result at `res` and
the operands `A` at `ap` and `B` at `bp`: it stores `subRes (A + B)`, which
is `(A + B) mod p` for operands below `p`. It returns with `sp` and every
register but `a0` through `a7` and `t0` through `t6` as they were, and
changes no memory outside the 0xB4 bytes of stack below `sp` and the
result. -/
theorem fieldAdd_correct (m : Machine) {P sp0 res ap bp retAddr : Word}
    (env : FAEnv m.mem P sp0 res ap bp) (hpc : m.pc = P) (ha0 : reg m a0 = res) (ha1 : reg m a1 = ap)
    (ha2 : reg m a2 = bp) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
        q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) →
        reg m' q = reg m q) ∧
      limbVal (wordsAt m'.mem res 8) = subRes (limbVal (wordsAt m.mem ap 8) + limbVal (wordsAt m.mem bp 8)) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → Sep res 32 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hS := env.hS
  have hGa : (sp0 + 0xFFFFFF80).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFF80) (by decide)
  have cF : ∀ (M' : Word → BitVec 8), (∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M' x = m.mem x) →
      CodeIn M' P fieldAddCode := fun M' hM i hi => by
    rw [hM _ (env.sC.subR (c := i) (l := 1) (by omega))]; exact env.code i hi
  have inF : ∀ c, 0 ≤ c → c + 4 ≤ 0x80 → ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 →
      Sep (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 c) 4 x 1 := fun c _ h2 x hx => by
    rw [fs_frame, add_ofNat_assoc]; exact hx.sub (by omega)
  have F0 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → m.mem x = m.mem x := fun _ _ => rfl
  obtain ⟨n1, d1, u1⟩ := s0.aluImm (cF m.mem F0) fa_at_0 (off' := 0x2) (by decide)
  have e1 : reg n1 sp = sp0 + 0xFFFFFF80 := (u1.regs _).trans ((upd_same (by decide)).trans (by rw [hsp]; rfl))
  have gra_1 : reg n1 ra = reg m ra := ((u1.regs ra).trans ((upd_ne (by decide) (by decide)).trans (rfl)))
  obtain ⟨n2, d2, u2⟩ := u1.self.sw (cF m.mem F0) fa_at_2 (off' := 0x4) (by decide)
    (by rw [e1]; exact aligned_add hGa (k := 0x7C) (by decide))
  rw [e1, gra_1, show (0x7C : Word) = BitVec.ofNat 32 0x7C from rfl] at u2
  obtain ⟨M2, hM2⟩ : ∃ M, memStore32 m.mem (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x7C) (reg m ra) = M := ⟨_, rfl⟩
  rw [hM2] at u2
  have F2 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M2 x = m.mem x := fun x hx => by
    rw [← hM2, memStore32_get_sep (inF 124 (by decide) (by decide) x hx), F0 x hx]
  have g8_2 : reg n2 (8 : Fin 32) = reg m (8 : Fin 32) := ((u2.regs (8 : Fin 32)).trans (((u1.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (rfl)))))
  have gsp_2 : reg n2 sp = sp0 + 0xFFFFFF80 := ((u2.regs sp).trans (e1))
  obtain ⟨n3, d3, u3⟩ := u2.self.sw (cF M2 F2) fa_at_4 (off' := 0x6) (by decide)
    (by rw [gsp_2]; exact aligned_add hGa (k := 0x78) (by decide))
  rw [gsp_2, g8_2, show (0x78 : Word) = BitVec.ofNat 32 0x78 from rfl] at u3
  obtain ⟨M3, hM3⟩ : ∃ M, memStore32 M2 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x78) (reg m (8 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM3] at u3
  have F3 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M3 x = m.mem x := fun x hx => by
    rw [← hM3, memStore32_get_sep (inF 120 (by decide) (by decide) x hx), F2 x hx]
  have g9_3 : reg n3 (9 : Fin 32) = reg m (9 : Fin 32) := ((u3.regs (9 : Fin 32)).trans (((u2.regs (9 : Fin 32)).trans (((u1.regs (9 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (rfl)))))))
  have gsp_3 : reg n3 sp = sp0 + 0xFFFFFF80 := ((u3.regs sp).trans (gsp_2))
  obtain ⟨n4, d4, u4⟩ := u3.self.sw (cF M3 F3) fa_at_6 (off' := 0x8) (by decide)
    (by rw [gsp_3]; exact aligned_add hGa (k := 0x74) (by decide))
  rw [gsp_3, g9_3, show (0x74 : Word) = BitVec.ofNat 32 0x74 from rfl] at u4
  obtain ⟨M4, hM4⟩ : ∃ M, memStore32 M3 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x74) (reg m (9 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM4] at u4
  have F4 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M4 x = m.mem x := fun x hx => by
    rw [← hM4, memStore32_get_sep (inF 116 (by decide) (by decide) x hx), F3 x hx]
  have gsp_4 : reg n4 sp = sp0 + 0xFFFFFF80 := ((u4.regs sp).trans (gsp_3))
  have g18_4 : reg n4 (18 : Fin 32) = reg m (18 : Fin 32) := ((u4.regs (18 : Fin 32)).trans (((u3.regs (18 : Fin 32)).trans (((u2.regs (18 : Fin 32)).trans (((u1.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (rfl)))))))))
  obtain ⟨n5, d5, u5⟩ := u4.self.sw (cF M4 F4) fa_at_8 (off' := 0xA) (by decide)
    (by rw [gsp_4]; exact aligned_add hGa (k := 0x70) (by decide))
  rw [gsp_4, g18_4, show (0x70 : Word) = BitVec.ofNat 32 0x70 from rfl] at u5
  obtain ⟨M5, hM5⟩ : ∃ M, memStore32 M4 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x70) (reg m (18 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM5] at u5
  have F5 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M5 x = m.mem x := fun x hx => by
    rw [← hM5, memStore32_get_sep (inF 112 (by decide) (by decide) x hx), F4 x hx]
  have g18_5 : reg n5 (18 : Fin 32) = reg m (18 : Fin 32) := ((u5.regs (18 : Fin 32)).trans (g18_4))
  have ga0_5 : reg n5 a0 = res := ((u5.regs a0).trans (((u4.regs a0).trans (((u3.regs a0).trans (((u2.regs a0).trans (((u1.regs a0).trans ((upd_ne (by decide) (by decide)).trans (ha0)))))))))))
  obtain ⟨n6, d6, u6⟩ := u5.self.alu (cF M5 F5) fa_at_a (off' := 0xC) (by decide)
  have e6 : reg n6 (18 : Fin 32) = res := (u6.regs _).trans ((upd_same (by decide)).trans (by rw [u5.self.zero, ga0_5]; exact BitVec.zero_add _))
  have ga1_6 : reg n6 a1 = ap := ((u6.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u5.regs a1).trans (((u4.regs a1).trans (((u3.regs a1).trans (((u2.regs a1).trans (((u1.regs a1).trans ((upd_ne (by decide) (by decide)).trans (ha1))))))))))))))
  obtain ⟨n7, x7, d7, hx7, u7⟩ := u6.self.lwG (cF M5 F5) fa_at_c (off' := 0x10) (by decide)
    (by rw [ga1_6]; exact aligned_add env.hap (k := 0x0) (by decide))
  rw [ga1_6] at hx7
  have e7 : reg n7 a6 = x7 := (u7.regs _).trans (upd_same (by decide))
  have ga2_7 : reg n7 a2 = bp := ((u7.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u6.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u5.regs a2).trans (((u4.regs a2).trans (((u3.regs a2).trans (((u2.regs a2).trans (((u1.regs a2).trans ((upd_ne (by decide) (by decide)).trans (ha2)))))))))))))))))
  obtain ⟨n8, x8, d8, hx8, u8⟩ := u7.self.lwG (cF M5 F5) fa_at_10 (off' := 0x12) (by decide)
    (by rw [ga2_7]; exact aligned_add env.hbp (k := 0x0) (by decide))
  rw [ga2_7] at hx8
  have e8 : reg n8 a3 = x8 := (u8.regs _).trans (upd_same (by decide))
  have ga2_8 : reg n8 a2 = bp := ((u8.regs a2).trans ((upd_ne (by decide) (by decide)).trans (ga2_7)))
  obtain ⟨n9, x9, d9, hx9, u9⟩ := u8.self.lwG (cF M5 F5) fa_at_12 (off' := 0x14) (by decide)
    (by rw [ga2_8]; exact aligned_add env.hbp (k := 0x4) (by decide))
  rw [ga2_8] at hx9
  have e9 : reg n9 a4 = x9 := (u9.regs _).trans (upd_same (by decide))
  have ga1_9 : reg n9 a1 = ap := ((u9.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u8.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u7.regs a1).trans ((upd_ne (by decide) (by decide)).trans (ga1_6)))))))))
  obtain ⟨n10, x10, d10, hx10, u10⟩ := u9.self.lwG (cF M5 F5) fa_at_14 (off' := 0x18) (by decide)
    (by rw [ga1_9]; exact aligned_add env.hap (k := 0x4) (by decide))
  rw [ga1_9] at hx10
  have e10 : reg n10 (5 : Fin 32) = x10 := (u10.regs _).trans (upd_same (by decide))
  have ga1_10 : reg n10 a1 = ap := ((u10.regs a1).trans ((upd_ne (by decide) (by decide)).trans (ga1_9)))
  obtain ⟨n11, x11, d11, hx11, u11⟩ := u10.self.lwG (cF M5 F5) fa_at_18 (off' := 0x1C) (by decide)
    (by rw [ga1_10]; exact aligned_add env.hap (k := 0x8) (by decide))
  rw [ga1_10] at hx11
  have e11 : reg n11 (6 : Fin 32) = x11 := (u11.regs _).trans (upd_same (by decide))
  have ga1_11 : reg n11 a1 = ap := ((u11.regs a1).trans ((upd_ne (by decide) (by decide)).trans (ga1_10)))
  obtain ⟨n12, x12, d12, hx12, u12⟩ := u11.self.lwG (cF M5 F5) fa_at_1c (off' := 0x20) (by decide)
    (by rw [ga1_11]; exact aligned_add env.hap (k := 0xC) (by decide))
  rw [ga1_11] at hx12
  have e12 : reg n12 a7 = x12 := (u12.regs _).trans (upd_same (by decide))
  have ga2_12 : reg n12 a2 = bp := ((u12.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u11.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u10.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u9.regs a2).trans ((upd_ne (by decide) (by decide)).trans (ga2_8))))))))))))
  obtain ⟨n13, x13, d13, hx13, u13⟩ := u12.self.lwG (cF M5 F5) fa_at_20 (off' := 0x22) (by decide)
    (by rw [ga2_12]; exact aligned_add env.hbp (k := 0x8) (by decide))
  rw [ga2_12] at hx13
  have e13 : reg n13 a5 = x13 := (u13.regs _).trans (upd_same (by decide))
  have ga0_13 : reg n13 a0 = res := ((u13.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u12.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u11.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u10.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u9.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u8.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u7.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u6.regs a0).trans ((upd_ne (by decide) (by decide)).trans (ga0_5))))))))))))))))))))))))
  have ga2_13 : reg n13 a2 = bp := ((u13.regs a2).trans ((upd_ne (by decide) (by decide)).trans (ga2_12)))
  obtain ⟨n14, x14, d14, hx14, u14⟩ := u13.self.lwG (cF M5 F5) fa_at_22 (off' := 0x24) (by decide)
    (by rw [ga2_13]; exact aligned_add env.hbp (k := 0xC) (by decide))
  rw [ga2_13] at hx14
  have e14 : reg n14 a0 = x14 := (u14.regs _).trans (upd_same (by decide))
  have ga6_14 : reg n14 a6 = x7 := ((u14.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u13.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u12.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u11.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u10.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u9.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u8.regs a6).trans ((upd_ne (by decide) (by decide)).trans (e7)))))))))))))))))))))
  have ga3_14 : reg n14 a3 = x8 := ((u14.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u13.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u12.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u11.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u10.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u9.regs a3).trans ((upd_ne (by decide) (by decide)).trans (e8))))))))))))))))))
  obtain ⟨n15, v15, d15, hv15, u15⟩ := u14.self.aluG (cF M5 F5) fa_at_24 (off' := 0x26) (by decide)
  rw [ga6_14, ga3_14] at hv15
  have e15 : reg n15 a6 = v15 := (u15.regs _).trans (upd_same (by decide))
  have g5_15 : reg n15 (5 : Fin 32) = x10 := ((u15.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u14.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u13.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u12.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u11.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e10)))))))))))))))
  have ga4_15 : reg n15 a4 = x9 := ((u15.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u14.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u13.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u12.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u11.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u10.regs a4).trans ((upd_ne (by decide) (by decide)).trans (e9))))))))))))))))))
  obtain ⟨n16, v16, d16, hv16, u16⟩ := u15.self.aluG (cF M5 F5) fa_at_26 (off' := 0x28) (by decide)
  rw [g5_15, ga4_15] at hv16
  have e16 : reg n16 (5 : Fin 32) = v16 := (u16.regs _).trans (upd_same (by decide))
  have ga6_16 : reg n16 a6 = v15 := ((u16.regs a6).trans ((upd_ne (by decide) (by decide)).trans (e15)))
  have ga3_16 : reg n16 a3 = x8 := ((u16.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u15.regs a3).trans ((upd_ne (by decide) (by decide)).trans (ga3_14))))))
  obtain ⟨n17, v17, d17, hv17, u17⟩ := u16.self.aluG (cF M5 F5) fa_at_28 (off' := 0x2C) (by decide)
  rw [ga6_16, ga3_16] at hv17
  have e17 : reg n17 a3 = v17 := (u17.regs _).trans (upd_same (by decide))
  have g5_17 : reg n17 (5 : Fin 32) = v16 := ((u17.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e16)))
  obtain ⟨n18, v18, d18, hv18, u18⟩ := u17.self.aluG (cF M5 F5) fa_at_2c (off' := 0x30) (by decide)
  rw [g5_17, e17] at hv18
  have e18 : reg n18 (7 : Fin 32) = v18 := (u18.regs _).trans (upd_same (by decide))
  have g5_18 : reg n18 (5 : Fin 32) = v16 := ((u18.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (g5_17)))
  have ga4_18 : reg n18 a4 = x9 := ((u18.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u17.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u16.regs a4).trans ((upd_ne (by decide) (by decide)).trans (ga4_15)))))))))
  obtain ⟨n19, v19, d19, hv19, u19⟩ := u18.self.aluG (cF M5 F5) fa_at_30 (off' := 0x34) (by decide)
  rw [g5_18, ga4_18] at hv19
  have e19 : reg n19 a4 = v19 := (u19.regs _).trans (upd_same (by decide))
  have g5_19 : reg n19 (5 : Fin 32) = v16 := ((u19.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (g5_18)))
  have ga3_19 : reg n19 a3 = v17 := ((u19.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u18.regs a3).trans ((upd_ne (by decide) (by decide)).trans (e17))))))
  have g7_19 : reg n19 (7 : Fin 32) = v18 := ((u19.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e18)))
  obtain ⟨n20, v20, d20, hv20, u20⟩ := u19.self.aluG (cF M5 F5) fa_at_34 (off' := 0x38) (by decide)
  rw [g7_19, g5_19] at hv20
  have e20 : reg n20 a3 = v20 := (u20.regs _).trans (upd_same (by decide))
  have g6_20 : reg n20 (6 : Fin 32) = x11 := ((u20.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u19.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u18.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u17.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u16.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u15.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u14.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u13.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u12.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e11)))))))))))))))))))))))))))
  have ga5_20 : reg n20 a5 = x13 := ((u20.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u19.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u18.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u17.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u16.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u15.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u14.regs a5).trans ((upd_ne (by decide) (by decide)).trans (e13)))))))))))))))))))))
  obtain ⟨n21, v21, d21, hv21, u21⟩ := u20.self.aluG (cF M5 F5) fa_at_38 (off' := 0x3A) (by decide)
  rw [g6_20, ga5_20] at hv21
  have e21 : reg n21 (6 : Fin 32) = v21 := (u21.regs _).trans (upd_same (by decide))
  have ga3_21 : reg n21 a3 = v20 := ((u21.regs a3).trans ((upd_ne (by decide) (by decide)).trans (e20)))
  have ga4_21 : reg n21 a4 = v19 := ((u21.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u20.regs a4).trans ((upd_ne (by decide) (by decide)).trans (e19))))))
  obtain ⟨n22, v22, d22, hv22, u22⟩ := u21.self.aluG (cF M5 F5) fa_at_3a (off' := 0x3C) (by decide)
  rw [ga3_21, ga4_21] at hv22
  have e22 : reg n22 a3 = v22 := (u22.regs _).trans (upd_same (by decide))
  have ga1_22 : reg n22 a1 = ap := ((u22.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u21.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u20.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u19.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u18.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u17.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u16.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u15.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u14.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u13.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u12.regs a1).trans ((upd_ne (by decide) (by decide)).trans (ga1_11)))))))))))))))))))))))))))))))))
  have g5_22 : reg n22 (5 : Fin 32) = v16 := ((u22.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u21.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u20.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (g5_19)))))))))
  obtain ⟨n23, x23, d23, hx23, u23⟩ := u22.self.lwG (cF M5 F5) fa_at_3c (off' := 0x40) (by decide)
    (by rw [ga1_22]; exact aligned_add env.hap (k := 0x10) (by decide))
  rw [ga1_22] at hx23
  have e23 : reg n23 (5 : Fin 32) = x23 := (u23.regs _).trans (upd_same (by decide))
  have ga3_23 : reg n23 a3 = v22 := ((u23.regs a3).trans ((upd_ne (by decide) (by decide)).trans (e22)))
  have g6_23 : reg n23 (6 : Fin 32) = v21 := ((u23.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u22.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e21))))))
  obtain ⟨n24, v24, d24, hv24, u24⟩ := u23.self.aluG (cF M5 F5) fa_at_40 (off' := 0x44) (by decide)
  rw [g6_23, ga3_23] at hv24
  have e24 : reg n24 (28 : Fin 32) = v24 := (u24.regs _).trans (upd_same (by decide))
  have g6_24 : reg n24 (6 : Fin 32) = v21 := ((u24.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (g6_23)))
  have ga5_24 : reg n24 a5 = x13 := ((u24.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u23.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u22.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u21.regs a5).trans ((upd_ne (by decide) (by decide)).trans (ga5_20))))))))))))
  obtain ⟨n25, v25, d25, hv25, u25⟩ := u24.self.aluG (cF M5 F5) fa_at_44 (off' := 0x48) (by decide)
  rw [g6_24, ga5_24] at hv25
  have e25 : reg n25 a5 = v25 := (u25.regs _).trans (upd_same (by decide))
  have g28_25 : reg n25 (28 : Fin 32) = v24 := ((u25.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e24)))
  have ga4_25 : reg n25 a4 = v19 := ((u25.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u24.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u23.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u22.regs a4).trans ((upd_ne (by decide) (by decide)).trans (ga4_21))))))))))))
  have g6_25 : reg n25 (6 : Fin 32) = v21 := ((u25.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (g6_24)))
  obtain ⟨n26, v26, d26, hv26, u26⟩ := u25.self.aluG (cF M5 F5) fa_at_48 (off' := 0x4C) (by decide)
  rw [g28_25, g6_25] at hv26
  have e26 : reg n26 a4 = v26 := (u26.regs _).trans (upd_same (by decide))
  have ga7_26 : reg n26 a7 = x12 := ((u26.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u25.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u24.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u23.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u22.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u21.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u20.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u19.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u18.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u17.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u16.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u15.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u14.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u13.regs a7).trans ((upd_ne (by decide) (by decide)).trans (e12))))))))))))))))))))))))))))))))))))))))))
  have ga0_26 : reg n26 a0 = x14 := ((u26.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u25.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u24.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u23.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u22.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u21.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u20.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u19.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u18.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u17.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u16.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u15.regs a0).trans ((upd_ne (by decide) (by decide)).trans (e14))))))))))))))))))))))))))))))))))))
  obtain ⟨n27, v27, d27, hv27, u27⟩ := u26.self.aluG (cF M5 F5) fa_at_4c (off' := 0x4E) (by decide)
  rw [ga7_26, ga0_26] at hv27
  have e27 : reg n27 a7 = v27 := (u27.regs _).trans (upd_same (by decide))
  have ga4_27 : reg n27 a4 = v26 := ((u27.regs a4).trans ((upd_ne (by decide) (by decide)).trans (e26)))
  have ga5_27 : reg n27 a5 = v25 := ((u27.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u26.regs a5).trans ((upd_ne (by decide) (by decide)).trans (e25))))))
  obtain ⟨n28, v28, d28, hv28, u28⟩ := u27.self.aluG (cF M5 F5) fa_at_4e (off' := 0x50) (by decide)
  rw [ga4_27, ga5_27] at hv28
  have e28 : reg n28 a4 = v28 := (u28.regs _).trans (upd_same (by decide))
  have ga2_28 : reg n28 a2 = bp := ((u28.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u27.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u26.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u25.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u24.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u23.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u22.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u21.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u20.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u19.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u18.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u17.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u16.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u15.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u14.regs a2).trans ((upd_ne (by decide) (by decide)).trans (ga2_13)))))))))))))))))))))))))))))))))))))))))))))
  have ga5_28 : reg n28 a5 = v25 := ((u28.regs a5).trans ((upd_ne (by decide) (by decide)).trans (ga5_27)))
  obtain ⟨n29, x29, d29, hx29, u29⟩ := u28.self.lwG (cF M5 F5) fa_at_50 (off' := 0x52) (by decide)
    (by rw [ga2_28]; exact aligned_add env.hbp (k := 0x10) (by decide))
  rw [ga2_28] at hx29
  have e29 : reg n29 a5 = x29 := (u29.regs _).trans (upd_same (by decide))
  have ga7_29 : reg n29 a7 = v27 := ((u29.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u28.regs a7).trans ((upd_ne (by decide) (by decide)).trans (e27))))))
  have g6_29 : reg n29 (6 : Fin 32) = v21 := ((u29.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u28.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u27.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u26.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (g6_25))))))))))))
  have ga4_29 : reg n29 a4 = v28 := ((u29.regs a4).trans ((upd_ne (by decide) (by decide)).trans (e28)))
  obtain ⟨n30, v30, d30, hv30, u30⟩ := u29.self.aluG (cF M5 F5) fa_at_52 (off' := 0x56) (by decide)
  rw [ga7_29, ga4_29] at hv30
  have e30 : reg n30 (6 : Fin 32) = v30 := (u30.regs _).trans (upd_same (by decide))
  have ga7_30 : reg n30 a7 = v27 := ((u30.regs a7).trans ((upd_ne (by decide) (by decide)).trans (ga7_29)))
  have ga0_30 : reg n30 a0 = x14 := ((u30.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u29.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u28.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u27.regs a0).trans ((upd_ne (by decide) (by decide)).trans (ga0_26))))))))))))
  obtain ⟨n31, v31, d31, hv31, u31⟩ := u30.self.aluG (cF M5 F5) fa_at_56 (off' := 0x5A) (by decide)
  rw [ga7_30, ga0_30] at hv31
  have e31 : reg n31 a0 = v31 := (u31.regs _).trans (upd_same (by decide))
  have ga7_31 : reg n31 a7 = v27 := ((u31.regs a7).trans ((upd_ne (by decide) (by decide)).trans (ga7_30)))
  have ga3_31 : reg n31 a3 = v22 := ((u31.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u30.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u29.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u28.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u27.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u26.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u25.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u24.regs a3).trans ((upd_ne (by decide) (by decide)).trans (ga3_23))))))))))))))))))))))))
  have g6_31 : reg n31 (6 : Fin 32) = v30 := ((u31.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e30)))
  obtain ⟨n32, v32, d32, hv32, u32⟩ := u31.self.aluG (cF M5 F5) fa_at_5a (off' := 0x5E) (by decide)
  rw [g6_31, ga7_31] at hv32
  have e32 : reg n32 a3 = v32 := (u32.regs _).trans (upd_same (by decide))
  have ga7_32 : reg n32 a7 = v27 := ((u32.regs a7).trans ((upd_ne (by decide) (by decide)).trans (ga7_31)))
  have ga0_32 : reg n32 a0 = v31 := ((u32.regs a0).trans ((upd_ne (by decide) (by decide)).trans (e31)))
  obtain ⟨n33, v33, d33, hv33, u33⟩ := u32.self.aluG (cF M5 F5) fa_at_5e (off' := 0x62) (by decide)
  rw [ga0_32, e32] at hv33
  have e33 : reg n33 a7 = v33 := (u33.regs _).trans (upd_same (by decide))
  have ga1_33 : reg n33 a1 = ap := ((u33.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u32.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u31.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u30.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u29.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u28.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u27.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u26.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u25.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u24.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u23.regs a1).trans ((upd_ne (by decide) (by decide)).trans (ga1_22)))))))))))))))))))))))))))))))))
  obtain ⟨n34, x34, d34, hx34, u34⟩ := u33.self.lwG (cF M5 F5) fa_at_62 (off' := 0x66) (by decide)
    (by rw [ga1_33]; exact aligned_add env.hap (k := 0x14) (by decide))
  rw [ga1_33] at hx34
  have e34 : reg n34 (29 : Fin 32) = x34 := (u34.regs _).trans (upd_same (by decide))
  have ga1_34 : reg n34 a1 = ap := ((u34.regs a1).trans ((upd_ne (by decide) (by decide)).trans (ga1_33)))
  obtain ⟨n35, x35, d35, hx35, u35⟩ := u34.self.lwG (cF M5 F5) fa_at_66 (off' := 0x6A) (by decide)
    (by rw [ga1_34]; exact aligned_add env.hap (k := 0x18) (by decide))
  rw [ga1_34] at hx35
  have e35 : reg n35 (30 : Fin 32) = x35 := (u35.regs _).trans (upd_same (by decide))
  have ga1_35 : reg n35 a1 = ap := ((u35.regs a1).trans ((upd_ne (by decide) (by decide)).trans (ga1_34)))
  obtain ⟨n36, x36, d36, hx36, u36⟩ := u35.self.lwG (cF M5 F5) fa_at_6a (off' := 0x6C) (by decide)
    (by rw [ga1_35]; exact aligned_add env.hap (k := 0x1C) (by decide))
  rw [ga1_35] at hx36
  have e36 : reg n36 a1 = x36 := (u36.regs _).trans (upd_same (by decide))
  have ga0_36 : reg n36 a0 = v31 := ((u36.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u35.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u34.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u33.regs a0).trans ((upd_ne (by decide) (by decide)).trans (ga0_32))))))))))))
  have ga2_36 : reg n36 a2 = bp := ((u36.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u35.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u34.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u33.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u32.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u31.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u30.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u29.regs a2).trans ((upd_ne (by decide) (by decide)).trans (ga2_28))))))))))))))))))))))))
  obtain ⟨n37, x37, d37, hx37, u37⟩ := u36.self.lwG (cF M5 F5) fa_at_6c (off' := 0x6E) (by decide)
    (by rw [ga2_36]; exact aligned_add env.hbp (k := 0x14) (by decide))
  rw [ga2_36] at hx37
  have e37 : reg n37 a0 = x37 := (u37.regs _).trans (upd_same (by decide))
  have ga2_37 : reg n37 a2 = bp := ((u37.regs a2).trans ((upd_ne (by decide) (by decide)).trans (ga2_36)))
  have ga3_37 : reg n37 a3 = v32 := ((u37.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u36.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u35.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u34.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u33.regs a3).trans ((upd_ne (by decide) (by decide)).trans (e32)))))))))))))))
  obtain ⟨n38, x38, d38, hx38, u38⟩ := u37.self.lwG (cF M5 F5) fa_at_6e (off' := 0x70) (by decide)
    (by rw [ga2_37]; exact aligned_add env.hbp (k := 0x18) (by decide))
  rw [ga2_37] at hx38
  have e38 : reg n38 a3 = x38 := (u38.regs _).trans (upd_same (by decide))
  have ga2_38 : reg n38 a2 = bp := ((u38.regs a2).trans ((upd_ne (by decide) (by decide)).trans (ga2_37)))
  obtain ⟨n39, x39, d39, hx39, u39⟩ := u38.self.lwG (cF M5 F5) fa_at_70 (off' := 0x72) (by decide)
    (by rw [ga2_38]; exact aligned_add env.hbp (k := 0x1C) (by decide))
  rw [ga2_38] at hx39
  have e39 : reg n39 a2 = x39 := (u39.regs _).trans (upd_same (by decide))
  have g5_39 : reg n39 (5 : Fin 32) = x23 := ((u39.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u38.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u37.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u36.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u35.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u34.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u33.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u32.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u31.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u30.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u29.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u28.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u27.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u26.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u25.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u24.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e23))))))))))))))))))))))))))))))))))))))))))))))))
  have ga5_39 : reg n39 a5 = x29 := ((u39.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u38.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u37.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u36.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u35.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u34.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u33.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u32.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u31.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u30.regs a5).trans ((upd_ne (by decide) (by decide)).trans (e29))))))))))))))))))))))))))))))
  obtain ⟨n40, v40, d40, hv40, u40⟩ := u39.self.aluG (cF M5 F5) fa_at_72 (off' := 0x74) (by decide)
  rw [g5_39, ga5_39] at hv40
  have e40 : reg n40 (5 : Fin 32) = v40 := (u40.regs _).trans (upd_same (by decide))
  have ga7_40 : reg n40 a7 = v33 := ((u40.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u39.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u38.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u37.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u36.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u35.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u34.regs a7).trans ((upd_ne (by decide) (by decide)).trans (e33)))))))))))))))))))))
  obtain ⟨n41, v41, d41, hv41, u41⟩ := u40.self.aluG (cF M5 F5) fa_at_74 (off' := 0x76) (by decide)
  rw [ga7_40, e40] at hv41
  have e41 : reg n41 a7 = v41 := (u41.regs _).trans (upd_same (by decide))
  have g5_41 : reg n41 (5 : Fin 32) = v40 := ((u41.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e40)))
  have ga5_41 : reg n41 a5 = x29 := ((u41.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u40.regs a5).trans ((upd_ne (by decide) (by decide)).trans (ga5_39))))))
  obtain ⟨n42, v42, d42, hv42, u42⟩ := u41.self.aluG (cF M5 F5) fa_at_76 (off' := 0x7A) (by decide)
  rw [g5_41, ga5_41] at hv42
  have e42 : reg n42 a5 = v42 := (u42.regs _).trans (upd_same (by decide))
  have ga7_42 : reg n42 a7 = v41 := ((u42.regs a7).trans ((upd_ne (by decide) (by decide)).trans (e41)))
  have g5_42 : reg n42 (5 : Fin 32) = v40 := ((u42.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (g5_41)))
  have ga4_42 : reg n42 a4 = v28 := ((u42.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u41.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u40.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u39.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u38.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u37.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u36.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u35.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u34.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u33.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u32.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u31.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u30.regs a4).trans ((upd_ne (by decide) (by decide)).trans (ga4_29)))))))))))))))))))))))))))))))))))))))
  obtain ⟨n43, v43, d43, hv43, u43⟩ := u42.self.aluG (cF M5 F5) fa_at_7a (off' := 0x7E) (by decide)
  rw [ga7_42, g5_42] at hv43
  have e43 : reg n43 a4 = v43 := (u43.regs _).trans (upd_same (by decide))
  have ga5_43 : reg n43 a5 = v42 := ((u43.regs a5).trans ((upd_ne (by decide) (by decide)).trans (e42)))
  obtain ⟨n44, v44, d44, hv44, u44⟩ := u43.self.aluG (cF M5 F5) fa_at_7e (off' := 0x80) (by decide)
  rw [e43, ga5_43] at hv44
  have e44 : reg n44 a4 = v44 := (u44.regs _).trans (upd_same (by decide))
  have ga0_44 : reg n44 a0 = x37 := ((u44.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u43.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u42.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u41.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u40.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u39.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u38.regs a0).trans ((upd_ne (by decide) (by decide)).trans (e37)))))))))))))))))))))
  have g29_44 : reg n44 (29 : Fin 32) = x34 := ((u44.regs (29 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u43.regs (29 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u42.regs (29 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u41.regs (29 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u40.regs (29 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u39.regs (29 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u38.regs (29 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u37.regs (29 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u36.regs (29 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u35.regs (29 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e34))))))))))))))))))))))))))))))
  obtain ⟨n45, v45, d45, hv45, u45⟩ := u44.self.aluG (cF M5 F5) fa_at_80 (off' := 0x82) (by decide)
  rw [g29_44, ga0_44] at hv45
  have e45 : reg n45 (29 : Fin 32) = v45 := (u45.regs _).trans (upd_same (by decide))
  have ga4_45 : reg n45 a4 = v44 := ((u45.regs a4).trans ((upd_ne (by decide) (by decide)).trans (e44)))
  obtain ⟨n46, v46, d46, hv46, u46⟩ := u45.self.aluG (cF M5 F5) fa_at_82 (off' := 0x84) (by decide)
  rw [ga4_45, e45] at hv46
  have e46 : reg n46 a4 = v46 := (u46.regs _).trans (upd_same (by decide))
  have ga0_46 : reg n46 a0 = x37 := ((u46.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u45.regs a0).trans ((upd_ne (by decide) (by decide)).trans (ga0_44))))))
  have g29_46 : reg n46 (29 : Fin 32) = v45 := ((u46.regs (29 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e45)))
  obtain ⟨n47, v47, d47, hv47, u47⟩ := u46.self.aluG (cF M5 F5) fa_at_84 (off' := 0x88) (by decide)
  rw [g29_46, ga0_46] at hv47
  have e47 : reg n47 a0 = v47 := (u47.regs _).trans (upd_same (by decide))
  have g29_47 : reg n47 (29 : Fin 32) = v45 := ((u47.regs (29 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (g29_46)))
  have ga4_47 : reg n47 a4 = v46 := ((u47.regs a4).trans ((upd_ne (by decide) (by decide)).trans (e46)))
  have ga5_47 : reg n47 a5 = v42 := ((u47.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u46.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u45.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u44.regs a5).trans ((upd_ne (by decide) (by decide)).trans (ga5_43))))))))))))
  obtain ⟨n48, v48, d48, hv48, u48⟩ := u47.self.aluG (cF M5 F5) fa_at_88 (off' := 0x8C) (by decide)
  rw [ga4_47, g29_47] at hv48
  have e48 : reg n48 a5 = v48 := (u48.regs _).trans (upd_same (by decide))
  have ga0_48 : reg n48 a0 = v47 := ((u48.regs a0).trans ((upd_ne (by decide) (by decide)).trans (e47)))
  obtain ⟨n49, v49, d49, hv49, u49⟩ := u48.self.aluG (cF M5 F5) fa_at_8c (off' := 0x8E) (by decide)
  rw [ga0_48, e48] at hv49
  have e49 : reg n49 a0 = v49 := (u49.regs _).trans (upd_same (by decide))
  have ga3_49 : reg n49 a3 = x38 := ((u49.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u48.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u47.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u46.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u45.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u44.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u43.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u42.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u41.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u40.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u39.regs a3).trans ((upd_ne (by decide) (by decide)).trans (e38)))))))))))))))))))))))))))))))))
  have g30_49 : reg n49 (30 : Fin 32) = x35 := ((u49.regs (30 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u48.regs (30 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u47.regs (30 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u46.regs (30 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u45.regs (30 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u44.regs (30 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u43.regs (30 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u42.regs (30 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u41.regs (30 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u40.regs (30 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u39.regs (30 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u38.regs (30 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u37.regs (30 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u36.regs (30 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e35))))))))))))))))))))))))))))))))))))))))))
  obtain ⟨n50, v50, d50, hv50, u50⟩ := u49.self.aluG (cF M5 F5) fa_at_8e (off' := 0x90) (by decide)
  rw [g30_49, ga3_49] at hv50
  have e50 : reg n50 (30 : Fin 32) = v50 := (u50.regs _).trans (upd_same (by decide))
  have ga0_50 : reg n50 a0 = v49 := ((u50.regs a0).trans ((upd_ne (by decide) (by decide)).trans (e49)))
  obtain ⟨n51, v51, d51, hv51, u51⟩ := u50.self.aluG (cF M5 F5) fa_at_90 (off' := 0x92) (by decide)
  rw [ga0_50, e50] at hv51
  have e51 : reg n51 a0 = v51 := (u51.regs _).trans (upd_same (by decide))
  have ga3_51 : reg n51 a3 = x38 := ((u51.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u50.regs a3).trans ((upd_ne (by decide) (by decide)).trans (ga3_49))))))
  have g30_51 : reg n51 (30 : Fin 32) = v50 := ((u51.regs (30 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e50)))
  obtain ⟨n52, v52, d52, hv52, u52⟩ := u51.self.aluG (cF M5 F5) fa_at_92 (off' := 0x96) (by decide)
  rw [g30_51, ga3_51] at hv52
  have e52 : reg n52 a3 = v52 := (u52.regs _).trans (upd_same (by decide))
  have ga0_52 : reg n52 a0 = v51 := ((u52.regs a0).trans ((upd_ne (by decide) (by decide)).trans (e51)))
  have g30_52 : reg n52 (30 : Fin 32) = v50 := ((u52.regs (30 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (g30_51)))
  have ga5_52 : reg n52 a5 = v48 := ((u52.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u51.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u50.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u49.regs a5).trans ((upd_ne (by decide) (by decide)).trans (e48))))))))))))
  obtain ⟨n53, v53, d53, hv53, u53⟩ := u52.self.aluG (cF M5 F5) fa_at_96 (off' := 0x9A) (by decide)
  rw [ga0_52, g30_52] at hv53
  have e53 : reg n53 a5 = v53 := (u53.regs _).trans (upd_same (by decide))
  have ga3_53 : reg n53 a3 = v52 := ((u53.regs a3).trans ((upd_ne (by decide) (by decide)).trans (e52)))
  obtain ⟨n54, v54, d54, hv54, u54⟩ := u53.self.aluG (cF M5 F5) fa_at_9a (off' := 0x9C) (by decide)
  rw [ga3_53, e53] at hv54
  have e54 : reg n54 a3 = v54 := (u54.regs _).trans (upd_same (by decide))
  have ga1_54 : reg n54 a1 = x36 := ((u54.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u53.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u52.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u51.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u50.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u49.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u48.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u47.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u46.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u45.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u44.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u43.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u42.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u41.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u40.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u39.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u38.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u37.regs a1).trans ((upd_ne (by decide) (by decide)).trans (e36))))))))))))))))))))))))))))))))))))))))))))))))))))))
  have ga2_54 : reg n54 a2 = x39 := ((u54.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u53.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u52.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u51.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u50.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u49.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u48.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u47.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u46.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u45.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u44.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u43.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u42.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u41.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u40.regs a2).trans ((upd_ne (by decide) (by decide)).trans (e39)))))))))))))))))))))))))))))))))))))))))))))
  obtain ⟨n55, v55, d55, hv55, u55⟩ := u54.self.aluG (cF M5 F5) fa_at_9c (off' := 0x9E) (by decide)
  rw [ga1_54, ga2_54] at hv55
  have e55 : reg n55 a1 = v55 := (u55.regs _).trans (upd_same (by decide))
  have ga3_55 : reg n55 a3 = v54 := ((u55.regs a3).trans ((upd_ne (by decide) (by decide)).trans (e54)))
  obtain ⟨n56, v56, d56, hv56, u56⟩ := u55.self.aluG (cF M5 F5) fa_at_9e (off' := 0xA0) (by decide)
  rw [ga3_55, e55] at hv56
  have e56 : reg n56 a3 = v56 := (u56.regs _).trans (upd_same (by decide))
  have ga1_56 : reg n56 a1 = v55 := ((u56.regs a1).trans ((upd_ne (by decide) (by decide)).trans (e55)))
  have ga2_56 : reg n56 a2 = x39 := ((u56.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u55.regs a2).trans ((upd_ne (by decide) (by decide)).trans (ga2_54))))))
  obtain ⟨n57, v57, d57, hv57, u57⟩ := u56.self.aluG (cF M5 F5) fa_at_a0 (off' := 0xA4) (by decide)
  rw [ga1_56, ga2_56] at hv57
  have e57 : reg n57 a2 = v57 := (u57.regs _).trans (upd_same (by decide))
  have ga1_57 : reg n57 a1 = v55 := ((u57.regs a1).trans ((upd_ne (by decide) (by decide)).trans (ga1_56)))
  have ga3_57 : reg n57 a3 = v56 := ((u57.regs a3).trans ((upd_ne (by decide) (by decide)).trans (e56)))
  obtain ⟨n58, v58, d58, hv58, u58⟩ := u57.self.aluG (cF M5 F5) fa_at_a4 (off' := 0xA8) (by decide)
  rw [ga3_57, ga1_57] at hv58
  have e58 : reg n58 a1 = v58 := (u58.regs _).trans (upd_same (by decide))
  have ga2_58 : reg n58 a2 = v57 := ((u58.regs a2).trans ((upd_ne (by decide) (by decide)).trans (e57)))
  obtain ⟨n59, v59, d59, hv59, u59⟩ := u58.self.aluG (cF M5 F5) fa_at_a8 (off' := 0xAA) (by decide)
  rw [e58, ga2_58] at hv59
  have e59 : reg n59 a1 = v59 := (u59.regs _).trans (upd_same (by decide))
  have ga6_59 : reg n59 a6 = v15 := ((u59.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u58.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u57.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u56.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u55.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u54.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u53.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u52.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u51.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u50.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u49.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u48.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u47.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u46.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u45.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u44.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u43.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u42.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u41.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u40.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u39.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u38.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u37.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u36.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u35.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u34.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u33.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u32.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u31.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u30.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u29.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u28.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u27.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u26.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u25.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u24.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u23.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u22.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u21.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u20.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u19.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u18.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u17.regs a6).trans ((upd_ne (by decide) (by decide)).trans (ga6_16)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  have gsp_59 : reg n59 sp = sp0 + 0xFFFFFF80 := ((u59.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u58.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u57.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u56.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u55.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u54.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u53.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u52.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u51.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u50.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u49.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u48.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u47.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u46.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u45.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u44.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u43.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u42.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u41.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u40.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u39.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u38.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u37.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u36.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u35.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u34.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u33.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u32.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u31.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u30.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u29.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u28.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u27.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u26.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u25.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u24.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u23.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u22.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u21.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u20.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u19.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u18.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u17.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u16.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u15.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u14.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u13.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u12.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u11.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u10.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u9.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u8.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u7.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u6.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u5.regs sp).trans (gsp_4))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  obtain ⟨n60, d60, u60⟩ := u59.self.sw (cF M5 F5) fa_at_aa (off' := 0xAC) (by decide)
    (by rw [gsp_59]; exact aligned_add hGa (k := 0x28) (by decide))
  rw [gsp_59, ga6_59, show (0x28 : Word) = BitVec.ofNat 32 0x28 from rfl] at u60
  obtain ⟨M60, hM60⟩ : ∃ M, memStore32 M5 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x28) (v15) = M := ⟨_, rfl⟩
  rw [hM60] at u60
  have F60 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M60 x = m.mem x := fun x hx => by
    rw [← hM60, memStore32_get_sep (inF 40 (by decide) (by decide) x hx), F5 x hx]
  have gsp_60 : reg n60 sp = sp0 + 0xFFFFFF80 := ((u60.regs sp).trans (gsp_59))
  have g7_60 : reg n60 (7 : Fin 32) = v18 := ((u60.regs (7 : Fin 32)).trans (((u59.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u58.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u57.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u56.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u55.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u54.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u53.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u52.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u51.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u50.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u49.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u48.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u47.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u46.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u45.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u44.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u43.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u42.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u41.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u40.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u39.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u38.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u37.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u36.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u35.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u34.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u33.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u32.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u31.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u30.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u29.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u28.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u27.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u26.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u25.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u24.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u23.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u22.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u21.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u20.regs (7 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (g7_19))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  obtain ⟨n61, d61, u61⟩ := u60.self.sw (cF M60 F60) fa_at_ac (off' := 0xAE) (by decide)
    (by rw [gsp_60]; exact aligned_add hGa (k := 0x2C) (by decide))
  rw [gsp_60, g7_60, show (0x2C : Word) = BitVec.ofNat 32 0x2C from rfl] at u61
  obtain ⟨M61, hM61⟩ : ∃ M, memStore32 M60 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x2C) (v18) = M := ⟨_, rfl⟩
  rw [hM61] at u61
  have F61 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M61 x = m.mem x := fun x hx => by
    rw [← hM61, memStore32_get_sep (inF 44 (by decide) (by decide) x hx), F60 x hx]
  have gsp_61 : reg n61 sp = sp0 + 0xFFFFFF80 := ((u61.regs sp).trans (gsp_60))
  have g28_61 : reg n61 (28 : Fin 32) = v24 := ((u61.regs (28 : Fin 32)).trans (((u60.regs (28 : Fin 32)).trans (((u59.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u58.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u57.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u56.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u55.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u54.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u53.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u52.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u51.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u50.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u49.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u48.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u47.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u46.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u45.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u44.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u43.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u42.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u41.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u40.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u39.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u38.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u37.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u36.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u35.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u34.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u33.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u32.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u31.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u30.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u29.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u28.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u27.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u26.regs (28 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (g28_25))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  obtain ⟨n62, d62, u62⟩ := u61.self.sw (cF M61 F61) fa_at_ae (off' := 0xB0) (by decide)
    (by rw [gsp_61]; exact aligned_add hGa (k := 0x30) (by decide))
  rw [gsp_61, g28_61, show (0x30 : Word) = BitVec.ofNat 32 0x30 from rfl] at u62
  obtain ⟨M62, hM62⟩ : ∃ M, memStore32 M61 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x30) (v24) = M := ⟨_, rfl⟩
  rw [hM62] at u62
  have F62 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M62 x = m.mem x := fun x hx => by
    rw [← hM62, memStore32_get_sep (inF 48 (by decide) (by decide) x hx), F61 x hx]
  have gsp_62 : reg n62 sp = sp0 + 0xFFFFFF80 := ((u62.regs sp).trans (gsp_61))
  have g6_62 : reg n62 (6 : Fin 32) = v30 := ((u62.regs (6 : Fin 32)).trans (((u61.regs (6 : Fin 32)).trans (((u60.regs (6 : Fin 32)).trans (((u59.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u58.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u57.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u56.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u55.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u54.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u53.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u52.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u51.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u50.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u49.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u48.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u47.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u46.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u45.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u44.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u43.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u42.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u41.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u40.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u39.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u38.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u37.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u36.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u35.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u34.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u33.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u32.regs (6 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (g6_31))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  obtain ⟨n63, d63, u63⟩ := u62.self.sw (cF M62 F62) fa_at_b0 (off' := 0xB2) (by decide)
    (by rw [gsp_62]; exact aligned_add hGa (k := 0x34) (by decide))
  rw [gsp_62, g6_62, show (0x34 : Word) = BitVec.ofNat 32 0x34 from rfl] at u63
  obtain ⟨M63, hM63⟩ : ∃ M, memStore32 M62 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x34) (v30) = M := ⟨_, rfl⟩
  rw [hM63] at u63
  have F63 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M63 x = m.mem x := fun x hx => by
    rw [← hM63, memStore32_get_sep (inF 52 (by decide) (by decide) x hx), F62 x hx]
  have ga7_63 : reg n63 a7 = v41 := ((u63.regs a7).trans (((u62.regs a7).trans (((u61.regs a7).trans (((u60.regs a7).trans (((u59.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u58.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u57.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u56.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u55.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u54.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u53.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u52.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u51.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u50.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u49.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u48.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u47.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u46.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u45.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u44.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u43.regs a7).trans ((upd_ne (by decide) (by decide)).trans (ga7_42)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  have gsp_63 : reg n63 sp = sp0 + 0xFFFFFF80 := ((u63.regs sp).trans (gsp_62))
  obtain ⟨n64, d64, u64⟩ := u63.self.sw (cF M63 F63) fa_at_b2 (off' := 0xB4) (by decide)
    (by rw [gsp_63]; exact aligned_add hGa (k := 0x38) (by decide))
  rw [gsp_63, ga7_63, show (0x38 : Word) = BitVec.ofNat 32 0x38 from rfl] at u64
  obtain ⟨M64, hM64⟩ : ∃ M, memStore32 M63 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x38) (v41) = M := ⟨_, rfl⟩
  rw [hM64] at u64
  have F64 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M64 x = m.mem x := fun x hx => by
    rw [← hM64, memStore32_get_sep (inF 56 (by decide) (by decide) x hx), F63 x hx]
  have gsp_64 : reg n64 sp = sp0 + 0xFFFFFF80 := ((u64.regs sp).trans (gsp_63))
  have ga4_64 : reg n64 a4 = v46 := ((u64.regs a4).trans (((u63.regs a4).trans (((u62.regs a4).trans (((u61.regs a4).trans (((u60.regs a4).trans (((u59.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u58.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u57.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u56.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u55.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u54.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u53.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u52.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u51.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u50.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u49.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u48.regs a4).trans ((upd_ne (by decide) (by decide)).trans (ga4_47))))))))))))))))))))))))))))))))))))))))))))))
  obtain ⟨n65, d65, u65⟩ := u64.self.sw (cF M64 F64) fa_at_b4 (off' := 0xB6) (by decide)
    (by rw [gsp_64]; exact aligned_add hGa (k := 0x3C) (by decide))
  rw [gsp_64, ga4_64, show (0x3C : Word) = BitVec.ofNat 32 0x3C from rfl] at u65
  obtain ⟨M65, hM65⟩ : ∃ M, memStore32 M64 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x3C) (v46) = M := ⟨_, rfl⟩
  rw [hM65] at u65
  have F65 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M65 x = m.mem x := fun x hx => by
    rw [← hM65, memStore32_get_sep (inF 60 (by decide) (by decide) x hx), F64 x hx]
  have gsp_65 : reg n65 sp = sp0 + 0xFFFFFF80 := ((u65.regs sp).trans (gsp_64))
  have ga0_65 : reg n65 a0 = v51 := ((u65.regs a0).trans (((u64.regs a0).trans (((u63.regs a0).trans (((u62.regs a0).trans (((u61.regs a0).trans (((u60.regs a0).trans (((u59.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u58.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u57.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u56.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u55.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u54.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u53.regs a0).trans ((upd_ne (by decide) (by decide)).trans (ga0_52)))))))))))))))))))))))))))))))))
  obtain ⟨n66, d66, u66⟩ := u65.self.sw (cF M65 F65) fa_at_b6 (off' := 0xB8) (by decide)
    (by rw [gsp_65]; exact aligned_add hGa (k := 0x40) (by decide))
  rw [gsp_65, ga0_65, show (0x40 : Word) = BitVec.ofNat 32 0x40 from rfl] at u66
  obtain ⟨M66, hM66⟩ : ∃ M, memStore32 M65 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x40) (v51) = M := ⟨_, rfl⟩
  rw [hM66] at u66
  have F66 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M66 x = m.mem x := fun x hx => by
    rw [← hM66, memStore32_get_sep (inF 64 (by decide) (by decide) x hx), F65 x hx]
  have gsp_66 : reg n66 sp = sp0 + 0xFFFFFF80 := ((u66.regs sp).trans (gsp_65))
  have ga3_66 : reg n66 a3 = v56 := ((u66.regs a3).trans (((u65.regs a3).trans (((u64.regs a3).trans (((u63.regs a3).trans (((u62.regs a3).trans (((u61.regs a3).trans (((u60.regs a3).trans (((u59.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u58.regs a3).trans ((upd_ne (by decide) (by decide)).trans (ga3_57))))))))))))))))))))
  obtain ⟨n67, d67, u67⟩ := u66.self.sw (cF M66 F66) fa_at_b8 (off' := 0xBA) (by decide)
    (by rw [gsp_66]; exact aligned_add hGa (k := 0x44) (by decide))
  rw [gsp_66, ga3_66, show (0x44 : Word) = BitVec.ofNat 32 0x44 from rfl] at u67
  obtain ⟨M67, hM67⟩ : ∃ M, memStore32 M66 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x44) (v56) = M := ⟨_, rfl⟩
  rw [hM67] at u67
  have F67 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M67 x = m.mem x := fun x hx => by
    rw [← hM67, memStore32_get_sep (inF 68 (by decide) (by decide) x hx), F66 x hx]
  have gsp_67 : reg n67 sp = sp0 + 0xFFFFFF80 := ((u67.regs sp).trans (gsp_66))
  have ga1_67 : reg n67 a1 = v59 := ((u67.regs a1).trans (((u66.regs a1).trans (((u65.regs a1).trans (((u64.regs a1).trans (((u63.regs a1).trans (((u62.regs a1).trans (((u61.regs a1).trans (((u60.regs a1).trans (e59))))))))))))))))
  obtain ⟨n68, d68, u68⟩ := u67.self.sw (cF M67 F67) fa_at_ba (off' := 0xBC) (by decide)
    (by rw [gsp_67]; exact aligned_add hGa (k := 0x48) (by decide))
  rw [gsp_67, ga1_67, show (0x48 : Word) = BitVec.ofNat 32 0x48 from rfl] at u68
  obtain ⟨M68, hM68⟩ : ∃ M, memStore32 M67 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x48) (v59) = M := ⟨_, rfl⟩
  rw [hM68] at u68
  have F68 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M68 x = m.mem x := fun x hx => by
    rw [← hM68, memStore32_get_sep (inF 72 (by decide) (by decide) x hx), F67 x hx]
  have ga0_68 : reg n68 a0 = v51 := ((u68.regs a0).trans (((u67.regs a0).trans (((u66.regs a0).trans (ga0_65))))))
  obtain ⟨n69, d69, u69⟩ := u68.self.aluImm (cF M68 F68) fa_at_bc (off' := 0xBE) (by decide)
  have e69 : reg n69 a0 = 0xFFFFFFFF := (u69.regs _).trans ((upd_same (by decide)).trans (by rw [u68.self.zero]; rfl))
  have gsp_69 : reg n69 sp = sp0 + 0xFFFFFF80 := ((u69.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u68.regs sp).trans (gsp_67)))))
  obtain ⟨n70, d70, u70⟩ := u69.self.sw (cF M68 F68) fa_at_be (off' := 0xC0) (by decide)
    (by rw [gsp_69]; exact aligned_add hGa (k := 0x4C) (by decide))
  rw [gsp_69, e69, show (0x4C : Word) = BitVec.ofNat 32 0x4C from rfl] at u70
  obtain ⟨M70, hM70⟩ : ∃ M, memStore32 M68 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x4C) (0xFFFFFFFF) = M := ⟨_, rfl⟩
  rw [hM70] at u70
  have F70 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M70 x = m.mem x := fun x hx => by
    rw [← hM70, memStore32_get_sep (inF 76 (by decide) (by decide) x hx), F68 x hx]
  have gsp_70 : reg n70 sp = sp0 + 0xFFFFFF80 := ((u70.regs sp).trans (gsp_69))
  have ga0_70 : reg n70 a0 = 0xFFFFFFFF := ((u70.regs a0).trans (e69))
  obtain ⟨n71, d71, u71⟩ := u70.self.sw (cF M70 F70) fa_at_c0 (off' := 0xC2) (by decide)
    (by rw [gsp_70]; exact aligned_add hGa (k := 0x50) (by decide))
  rw [gsp_70, ga0_70, show (0x50 : Word) = BitVec.ofNat 32 0x50 from rfl] at u71
  obtain ⟨M71, hM71⟩ : ∃ M, memStore32 M70 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x50) (0xFFFFFFFF) = M := ⟨_, rfl⟩
  rw [hM71] at u71
  have F71 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M71 x = m.mem x := fun x hx => by
    rw [← hM71, memStore32_get_sep (inF 80 (by decide) (by decide) x hx), F70 x hx]
  have gsp_71 : reg n71 sp = sp0 + 0xFFFFFF80 := ((u71.regs sp).trans (gsp_70))
  have ga0_71 : reg n71 a0 = 0xFFFFFFFF := ((u71.regs a0).trans (ga0_70))
  obtain ⟨n72, d72, u72⟩ := u71.self.sw (cF M71 F71) fa_at_c2 (off' := 0xC4) (by decide)
    (by rw [gsp_71]; exact aligned_add hGa (k := 0x54) (by decide))
  rw [gsp_71, ga0_71, show (0x54 : Word) = BitVec.ofNat 32 0x54 from rfl] at u72
  obtain ⟨M72, hM72⟩ : ∃ M, memStore32 M71 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x54) (0xFFFFFFFF) = M := ⟨_, rfl⟩
  rw [hM72] at u72
  have F72 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M72 x = m.mem x := fun x hx => by
    rw [← hM72, memStore32_get_sep (inF 84 (by decide) (by decide) x hx), F71 x hx]
  have gsp_72 : reg n72 sp = sp0 + 0xFFFFFF80 := ((u72.regs sp).trans (gsp_71))
  obtain ⟨n73, d73, u73⟩ := u72.self.sw (cF M72 F72) fa_at_c4 (off' := 0xC6) (by decide)
    (by rw [gsp_72]; exact aligned_add hGa (k := 0x58) (by decide))
  rw [gsp_72, u72.self.zero, show (0x58 : Word) = BitVec.ofNat 32 0x58 from rfl] at u73
  obtain ⟨M73, hM73⟩ : ∃ M, memStore32 M72 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x58) (0) = M := ⟨_, rfl⟩
  rw [hM73] at u73
  have F73 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M73 x = m.mem x := fun x hx => by
    rw [← hM73, memStore32_get_sep (inF 88 (by decide) (by decide) x hx), F72 x hx]
  have ga1_73 : reg n73 a1 = v59 := ((u73.regs a1).trans (((u72.regs a1).trans (((u71.regs a1).trans (((u70.regs a1).trans (((u69.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u68.regs a1).trans (ga1_67)))))))))))))
  obtain ⟨n74, d74, u74⟩ := u73.self.aluImm (cF M73 F73) fa_at_c6 (off' := 0xC8) (by decide)
  have e74 : reg n74 a1 = 0x1 := (u74.regs _).trans ((upd_same (by decide)).trans (by rw [u73.self.zero]; rfl))
  have gsp_74 : reg n74 sp = sp0 + 0xFFFFFF80 := ((u74.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u73.regs sp).trans (gsp_72)))))
  obtain ⟨n75, d75, u75⟩ := u74.self.sw (cF M73 F73) fa_at_c8 (off' := 0xCA) (by decide)
    (by rw [gsp_74]; exact aligned_add hGa (k := 0x5C) (by decide))
  rw [gsp_74, u74.self.zero, show (0x5C : Word) = BitVec.ofNat 32 0x5C from rfl] at u75
  obtain ⟨M75, hM75⟩ : ∃ M, memStore32 M73 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x5C) (0) = M := ⟨_, rfl⟩
  rw [hM75] at u75
  have F75 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M75 x = m.mem x := fun x hx => by
    rw [← hM75, memStore32_get_sep (inF 92 (by decide) (by decide) x hx), F73 x hx]
  have gsp_75 : reg n75 sp = sp0 + 0xFFFFFF80 := ((u75.regs sp).trans (gsp_74))
  obtain ⟨n76, d76, u76⟩ := u75.self.sw (cF M75 F75) fa_at_ca (off' := 0xCC) (by decide)
    (by rw [gsp_75]; exact aligned_add hGa (k := 0x60) (by decide))
  rw [gsp_75, u75.self.zero, show (0x60 : Word) = BitVec.ofNat 32 0x60 from rfl] at u76
  obtain ⟨M76, hM76⟩ : ∃ M, memStore32 M75 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x60) (0) = M := ⟨_, rfl⟩
  rw [hM76] at u76
  have F76 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M76 x = m.mem x := fun x hx => by
    rw [← hM76, memStore32_get_sep (inF 96 (by decide) (by decide) x hx), F75 x hx]
  have gsp_76 : reg n76 sp = sp0 + 0xFFFFFF80 := ((u76.regs sp).trans (gsp_75))
  have ga1_76 : reg n76 a1 = 0x1 := ((u76.regs a1).trans (((u75.regs a1).trans (e74))))
  obtain ⟨n77, d77, u77⟩ := u76.self.sw (cF M76 F76) fa_at_cc (off' := 0xCE) (by decide)
    (by rw [gsp_76]; exact aligned_add hGa (k := 0x64) (by decide))
  rw [gsp_76, ga1_76, show (0x64 : Word) = BitVec.ofNat 32 0x64 from rfl] at u77
  obtain ⟨M77, hM77⟩ : ∃ M, memStore32 M76 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x64) (0x1) = M := ⟨_, rfl⟩
  rw [hM77] at u77
  have F77 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M77 x = m.mem x := fun x hx => by
    rw [← hM77, memStore32_get_sep (inF 100 (by decide) (by decide) x hx), F76 x hx]
  have gsp_77 : reg n77 sp = sp0 + 0xFFFFFF80 := ((u77.regs sp).trans (gsp_76))
  have ga0_77 : reg n77 a0 = 0xFFFFFFFF := ((u77.regs a0).trans (((u76.regs a0).trans (((u75.regs a0).trans (((u74.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u73.regs a0).trans (((u72.regs a0).trans (ga0_71)))))))))))))
  obtain ⟨n78, d78, u78⟩ := u77.self.sw (cF M77 F77) fa_at_ce (off' := 0xD0) (by decide)
    (by rw [gsp_77]; exact aligned_add hGa (k := 0x68) (by decide))
  rw [gsp_77, ga0_77, show (0x68 : Word) = BitVec.ofNat 32 0x68 from rfl] at u78
  obtain ⟨M78, hM78⟩ : ∃ M, memStore32 M77 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x68) (0xFFFFFFFF) = M := ⟨_, rfl⟩
  rw [hM78] at u78
  have F78 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M78 x = m.mem x := fun x hx => by
    rw [← hM78, memStore32_get_sep (inF 104 (by decide) (by decide) x hx), F77 x hx]
  have gsp_78 : reg n78 sp = sp0 + 0xFFFFFF80 := ((u78.regs sp).trans (gsp_77))
  obtain ⟨n79, d79, u79⟩ := u78.self.sw (cF M78 F78) fa_at_d0 (off' := 0xD2) (by decide)
    (by rw [gsp_78]; exact aligned_add hGa (k := 0x6C) (by decide))
  rw [gsp_78, u78.self.zero, show (0x6C : Word) = BitVec.ofNat 32 0x6C from rfl] at u79
  obtain ⟨M79, hM79⟩ : ∃ M, memStore32 M78 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x6C) (0) = M := ⟨_, rfl⟩
  rw [hM79] at u79
  have F79 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M79 x = m.mem x := fun x hx => by
    rw [← hM79, memStore32_get_sep (inF 108 (by decide) (by decide) x hx), F78 x hx]
  have ga0_79 : reg n79 a0 = 0xFFFFFFFF := ((u79.regs a0).trans (((u78.regs a0).trans (ga0_77))))
  have gsp_79 : reg n79 sp = sp0 + 0xFFFFFF80 := ((u79.regs sp).trans (gsp_78))
  obtain ⟨n80, d80, u80⟩ := u79.self.aluImm (cF M79 F79) fa_at_d2 (off' := 0xD4) (by decide)
  have e80 : reg n80 a0 = sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x4 := (u80.regs _).trans ((upd_same (by decide)).trans (by rw [gsp_79]; rfl))
  have gsp_80 : reg n80 sp = sp0 + 0xFFFFFF80 := ((u80.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_79)))
  have ga1_80 : reg n80 a1 = 0x1 := ((u80.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u79.regs a1).trans (((u78.regs a1).trans (((u77.regs a1).trans (ga1_76)))))))))
  obtain ⟨n81, d81, u81⟩ := u80.self.aluImm (cF M79 F79) fa_at_d4 (off' := 0xD6) (by decide)
  have e81 : reg n81 a1 = sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x28 := (u81.regs _).trans ((upd_same (by decide)).trans (by rw [gsp_80]; rfl))
  have gsp_81 : reg n81 sp = sp0 + 0xFFFFFF80 := ((u81.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_80)))
  have ga2_81 : reg n81 a2 = v57 := ((u81.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u80.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u79.regs a2).trans (((u78.regs a2).trans (((u77.regs a2).trans (((u76.regs a2).trans (((u75.regs a2).trans (((u74.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u73.regs a2).trans (((u72.regs a2).trans (((u71.regs a2).trans (((u70.regs a2).trans (((u69.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u68.regs a2).trans (((u67.regs a2).trans (((u66.regs a2).trans (((u65.regs a2).trans (((u64.regs a2).trans (((u63.regs a2).trans (((u62.regs a2).trans (((u61.regs a2).trans (((u60.regs a2).trans (((u59.regs a2).trans ((upd_ne (by decide) (by decide)).trans (ga2_58)))))))))))))))))))))))))))))))))))))))))))))))))))
  obtain ⟨n82, d82, u82⟩ := u81.self.aluImm (cF M79 F79) fa_at_d6 (off' := 0xD8) (by decide)
  have e82 : reg n82 a2 = sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x4C := (u82.regs _).trans ((upd_same (by decide)).trans (by rw [gsp_81]; rfl))
  have wL : wordsAt M79 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x28) 9 = [v15, v18, v24, v30, v41, v46, v51, v56, v59] := by
    rw [wordsAt9, add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x28 (4 * 0), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x28 (4 * 1), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x28 (4 * 2), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x28 (4 * 3), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x28 (4 * 4), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x28 (4 * 5), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x28 (4 * 6), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x28 (4 * 7), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x28 (4 * 8)]
    rw [← hM79, ← hM78, ← hM77, ← hM76, ← hM75, ← hM73, ← hM72, ← hM71, ← hM70, ← hM68, ← hM67, ← hM66, ← hM65, ← hM64, ← hM63, ← hM62, ← hM61, ← hM60, ← hM5, ← hM4, ← hM3, ← hM2]
    simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same]
  have wR0 : wordsAt M79 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x4C) 9 = [0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0, 0, 0, 0x1, 0xFFFFFFFF, 0] := by
    rw [wordsAt9, add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x4C (4 * 0), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x4C (4 * 1), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x4C (4 * 2), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x4C (4 * 3), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x4C (4 * 4), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x4C (4 * 5), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x4C (4 * 6), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x4C (4 * 7), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x4C (4 * 8)]
    rw [← hM79, ← hM78, ← hM77, ← hM76, ← hM75, ← hM73, ← hM72, ← hM71, ← hM70, ← hM68, ← hM67, ← hM66, ← hM65, ← hM64, ← hM63, ← hM62, ← hM61, ← hM60, ← hM5, ← hM4, ← hM3, ← hM2]
    simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same]
  have wP : wordsAt M79 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x4C) 9 = pLimbs := by rw [wR0]; rfl
  have ldA : ∀ c, c + 4 ≤ 32 → memLoad32 M5 (ap + BitVec.ofNat 32 c) = memLoad32 m.mem (ap + BitVec.ofNat 32 c) :=
    fun c h => memLoad32_congr (M := m.mem) (M' := M5) fun j hj => F5 _ (by
      have := env.sAS.symm.subR (c := c + j) (l := 1) (by omega); rwa [← add_ofNat_assoc] at this)
  have wA : wordsAt m.mem ap 8 = [x7, x10, x11, x12, x23, x34, x35, x36] := by
    rw [wordsAt8, (ldA (4 * 0) (by decide)).symm.trans hx7, (ldA (4 * 1) (by decide)).symm.trans hx10, (ldA (4 * 2) (by decide)).symm.trans hx11, (ldA (4 * 3) (by decide)).symm.trans hx12, (ldA (4 * 4) (by decide)).symm.trans hx23, (ldA (4 * 5) (by decide)).symm.trans hx34, (ldA (4 * 6) (by decide)).symm.trans hx35, (ldA (4 * 7) (by decide)).symm.trans hx36]
  have ldB : ∀ c, c + 4 ≤ 32 → memLoad32 M5 (bp + BitVec.ofNat 32 c) = memLoad32 m.mem (bp + BitVec.ofNat 32 c) :=
    fun c h => memLoad32_congr (M := m.mem) (M' := M5) fun j hj => F5 _ (by
      have := env.sBS.symm.subR (c := c + j) (l := 1) (by omega); rwa [← add_ofNat_assoc] at this)
  have wB : wordsAt m.mem bp 8 = [x8, x9, x13, x14, x29, x37, x38, x39] := by
    rw [wordsAt8, (ldB (4 * 0) (by decide)).symm.trans hx8, (ldB (4 * 1) (by decide)).symm.trans hx9, (ldB (4 * 2) (by decide)).symm.trans hx13, (ldB (4 * 3) (by decide)).symm.trans hx14, (ldB (4 * 4) (by decide)).symm.trans hx29, (ldB (4 * 5) (by decide)).symm.trans hx37, (ldB (4 * 6) (by decide)).symm.trans hx38, (ldB (4 * 7) (by decide)).symm.trans hx39]
  have Ec0 := fmP1 hv15 (.inr hv17)
  have Ec1 := fmP3 hv16 (.inr hv19) (.inr hv18) hv20 (.inl hv22)
  have Ec2 := fmP3 hv21 (.inr hv25) (.inr hv24) hv26 (.inl hv28)
  have Ec3 := fmP3 hv27 (.inr hv31) (.inr hv30) hv32 (.inr hv33)
  have Ec4 := fmP3 hv40 (.inr hv42) (.inl hv41) hv43 (.inl hv44)
  have Ec5 := fmP3 hv45 (.inr hv47) (.inl hv46) hv48 (.inr hv49)
  have Ec6 := fmP3 hv50 (.inr hv52) (.inl hv51) hv53 (.inr hv54)
  have Ec7 := fmP3 hv55 (.inr hv57) (.inl hv56) hv58 (.inl hv59)
  have hsum : limbVal [v15, v18, v24, v30, v41, v46, v51, v56, v59] = limbVal [x7, x10, x11, x12, x23, x34, x35, x36] + limbVal [x8, x9, x13, x14, x29, x37, x38, x39] := by
    rw [limbFlat9, limbFlat8, limbFlat8]
    omega
  have hsi : (P + 0xFFFFFCAA).toNat % 2 = 0 := even_at P env.hP 0xFFFFFCAA (by decide)
  have codeX : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep (sp0 + 0xFFFFFF4C) 0xB4 b code.length →
      (∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have siA : sp0 + 0xFFFFFF80 + 0xFFFFFFCC = sp0 + 0xFFFFFF4C + BitVec.ofNat 32 0 := by
    rw [BitVec.add_assoc, add_ofNat_zero]; rfl
  have inS : ∀ c, (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 c) = sp0 + 0xFFFFFF4C + BitVec.ofNat 32 (0x34 + c) := fun c => by
    rw [fs_frame, add_ofNat_assoc]
  have wrapC : ∀ c, c + 36 ≤ 0x80 → (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 c).toNat + 36 ≤ 2 ^ 32 := fun c h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_add]
    have : (0xFFFFFF80 : Word).toNat = 4294967168 := rfl
    have := sp0.isLt; omega
  have senv : SIEnv M79 (P + 0xFFFFFCAA) (sp0 + 0xFFFFFF80) (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x4) (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x28)
      (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x4C) :=
    ⟨hsi, codeX env.sicode env.sI F79, codeX env.bsub env.sIb F79, codeX env.sisave env.sIs F79,
      codeX env.sirestore env.sIr F79, hGa, aligned_add hGa (by decide), aligned_add hGa (by decide),
      aligned_add hGa (by decide), by rw [BitVec.toNat_add]; have : (0xFFFFFF80 : Word).toNat = 4294967168 := rfl; have := sp0.isLt; omega,
      by rw [siA]; exact env.sI.sub (by decide), by rw [siA]; exact env.sIb.sub (by decide),
      by rw [siA]; exact env.sIs.sub (by decide), by rw [siA]; exact env.sIr.sub (by decide),
      by rw [inS]; exact env.sI.sub (by decide), by rw [inS]; exact env.sIr.sub (by decide),
      by rw [inS, siA]; exact sep_offsets _ (.inr (by decide)) (by decide) (by decide),
      by rw [inS, siA]; exact sep_offsets _ (.inr (by decide)) (by decide) (by decide),
      by rw [inS, siA]; exact sep_offsets _ (.inr (by decide)) (by decide) (by decide),
      ⟨wrapC 0x4 (by decide), wrapC 0x28 (by decide), wrapC 0x4C (by decide)⟩, wP⟩
  obtain ⟨n83, c83, pc83, mem83, regs83⟩ := u82.self.callRa (cF M79 F79) fa_at_d8 fa_at_dc
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) hsi
  have r83 := PEnv.reg1 regs83 u82.self.zero
  rw [← mem83] at senv
  obtain ⟨n84, c84, pc84, sp84, regs84, val84, mask84, frame84⟩ := subInner_correct n83 senv pc83
    (by rw [r83 a0 (by decide), ((u82.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u81.regs a0).trans ((upd_ne (by decide) (by decide)).trans (e80))))))]) (by rw [r83 a1 (by decide), ((u82.regs a1).trans ((upd_ne (by decide) (by decide)).trans (e81)))])
    (by rw [r83 a2 (by decide), e82]) (by rw [regs83]; simp +decide [upd])
    (even_clear _ (even_at P env.hP 0xE0 (by decide))) (by rw [r83 sp (by decide), ((u82.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_81)))])
  rw [mem83, wL, hsum, ← wA, ← wB] at val84
  rw [mem83] at frame84
  have s84 : St n84.mem P n84 0xE0 (reg n84) := ⟨by rw [pc84], rfl, fun _ => rfl⟩
  have F84 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → n84.mem x = m.mem x := fun x hx =>
    (frame84 x (by rw [siA]; exact hx.sub (by decide)) (by rw [inS]; exact hx.sub (by decide))).trans (F79 x hx)
  have cc84 := cF n84.mem F84
  obtain ⟨n85, x85, d85, hx85, u85⟩ := s84.lwG cc84 fa_at_e0 (off' := 0xE2) (by decide)
    (by rw [sp84]; exact aligned_add hGa (k := 0x4) (by decide))
  rw [sp84] at hx85
  have e85 : reg n85 a0 = x85 := (u85.regs _).trans (upd_same (by decide))
  have gsp_85 : reg n85 sp = sp0 + 0xFFFFFF80 := ((u85.regs sp).trans ((upd_ne (by decide) (by decide)).trans (sp84)))
  obtain ⟨n86, x86, d86, hx86, u86⟩ := u85.self.lwG cc84 fa_at_e2 (off' := 0xE4) (by decide)
    (by rw [gsp_85]; exact aligned_add hGa (k := 0x8) (by decide))
  rw [gsp_85] at hx86
  have e86 : reg n86 a1 = x86 := (u86.regs _).trans (upd_same (by decide))
  have gsp_86 : reg n86 sp = sp0 + 0xFFFFFF80 := ((u86.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_85)))
  obtain ⟨n87, x87, d87, hx87, u87⟩ := u86.self.lwG cc84 fa_at_e4 (off' := 0xE6) (by decide)
    (by rw [gsp_86]; exact aligned_add hGa (k := 0xC) (by decide))
  rw [gsp_86] at hx87
  have e87 : reg n87 a2 = x87 := (u87.regs _).trans (upd_same (by decide))
  have gsp_87 : reg n87 sp = sp0 + 0xFFFFFF80 := ((u87.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_86)))
  obtain ⟨n88, x88, d88, hx88, u88⟩ := u87.self.lwG cc84 fa_at_e6 (off' := 0xE8) (by decide)
    (by rw [gsp_87]; exact aligned_add hGa (k := 0x10) (by decide))
  rw [gsp_87] at hx88
  have e88 : reg n88 a3 = x88 := (u88.regs _).trans (upd_same (by decide))
  have gsp_88 : reg n88 sp = sp0 + 0xFFFFFF80 := ((u88.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_87)))
  obtain ⟨n89, x89, d89, hx89, u89⟩ := u88.self.lwG cc84 fa_at_e8 (off' := 0xEA) (by decide)
    (by rw [gsp_88]; exact aligned_add hGa (k := 0x14) (by decide))
  rw [gsp_88] at hx89
  have e89 : reg n89 a4 = x89 := (u89.regs _).trans (upd_same (by decide))
  have gsp_89 : reg n89 sp = sp0 + 0xFFFFFF80 := ((u89.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_88)))
  obtain ⟨n90, x90, d90, hx90, u90⟩ := u89.self.lwG cc84 fa_at_ea (off' := 0xEC) (by decide)
    (by rw [gsp_89]; exact aligned_add hGa (k := 0x18) (by decide))
  rw [gsp_89] at hx90
  have e90 : reg n90 a5 = x90 := (u90.regs _).trans (upd_same (by decide))
  have gsp_90 : reg n90 sp = sp0 + 0xFFFFFF80 := ((u90.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_89)))
  obtain ⟨n91, x91, d91, hx91, u91⟩ := u90.self.lwG cc84 fa_at_ec (off' := 0xEE) (by decide)
    (by rw [gsp_90]; exact aligned_add hGa (k := 0x1C) (by decide))
  rw [gsp_90] at hx91
  have e91 : reg n91 (8 : Fin 32) = x91 := (u91.regs _).trans (upd_same (by decide))
  have gsp_91 : reg n91 sp = sp0 + 0xFFFFFF80 := ((u91.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_90)))
  obtain ⟨n92, x92, d92, hx92, u92⟩ := u91.self.lwG cc84 fa_at_ee (off' := 0xF0) (by decide)
    (by rw [gsp_91]; exact aligned_add hGa (k := 0x20) (by decide))
  rw [gsp_91] at hx92
  have e92 : reg n92 (9 : Fin 32) = x92 := (u92.regs _).trans (upd_same (by decide))
  have g18_92 : reg n92 (18 : Fin 32) = res := ((u92.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u91.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u90.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u89.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u88.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u87.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u86.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u85.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans ((regs84 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((r83 _ (by decide)).trans (((u82.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u81.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u80.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u79.regs (18 : Fin 32)).trans (((u78.regs (18 : Fin 32)).trans (((u77.regs (18 : Fin 32)).trans (((u76.regs (18 : Fin 32)).trans (((u75.regs (18 : Fin 32)).trans (((u74.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u73.regs (18 : Fin 32)).trans (((u72.regs (18 : Fin 32)).trans (((u71.regs (18 : Fin 32)).trans (((u70.regs (18 : Fin 32)).trans (((u69.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u68.regs (18 : Fin 32)).trans (((u67.regs (18 : Fin 32)).trans (((u66.regs (18 : Fin 32)).trans (((u65.regs (18 : Fin 32)).trans (((u64.regs (18 : Fin 32)).trans (((u63.regs (18 : Fin 32)).trans (((u62.regs (18 : Fin 32)).trans (((u61.regs (18 : Fin 32)).trans (((u60.regs (18 : Fin 32)).trans (((u59.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u58.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u57.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u56.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u55.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u54.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u53.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u52.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u51.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u50.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u49.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u48.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u47.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u46.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u45.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u44.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u43.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u42.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u41.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u40.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u39.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u38.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u37.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u36.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u35.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u34.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u33.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u32.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u31.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u30.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u29.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u28.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u27.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u26.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u25.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u24.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u23.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u22.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u21.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u20.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u19.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u18.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u17.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u16.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u15.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u14.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u13.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u12.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u11.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u10.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u9.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u8.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u7.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  have ga0_92 : reg n92 a0 = x85 := ((u92.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u91.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u90.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u89.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u88.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u87.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u86.regs a0).trans ((upd_ne (by decide) (by decide)).trans (e85)))))))))))))))))))))
  obtain ⟨n93, d93, u93⟩ := u92.self.sw cc84 fa_at_f0 (off' := 0xF4) (by decide)
    (by rw [g18_92]; exact aligned_add env.hres (k := 0x0) (by decide))
  rw [g18_92, ga0_92, show (0x0 : Word) = BitVec.ofNat 32 0x0 from rfl] at u93
  obtain ⟨M93, hM93⟩ : ∃ M, memStore32 n84.mem (res + BitVec.ofNat 32 0x0) (x85) = M := ⟨_, rfl⟩
  rw [hM93] at u93
  have cc93 : CodeIn M93 P fieldAddCode := by
    rw [← hM93]; exact CodeIn.store32 cc84 (env.sRC.sub (c := 0) (l := 4) (by decide))
  have ga0_93 : reg n93 a0 = x85 := ((u93.regs a0).trans (ga0_92))
  have g18_93 : reg n93 (18 : Fin 32) = res := ((u93.regs (18 : Fin 32)).trans (g18_92))
  obtain ⟨n94, d94, u94⟩ := u93.self.alu cc93 fa_at_f4 (off' := 0xF6) (by decide)
  have e94 : reg n94 a0 = res := (u94.regs _).trans ((upd_same (by decide)).trans (by rw [u93.self.zero, g18_93]; exact BitVec.zero_add _))
  have ga1_94 : reg n94 a1 = x86 := ((u94.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u93.regs a1).trans (((u92.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u91.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u90.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u89.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u88.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u87.regs a1).trans ((upd_ne (by decide) (by decide)).trans (e86)))))))))))))))))))))))
  obtain ⟨n95, d95, u95⟩ := u94.self.sw cc93 fa_at_f6 (off' := 0xF8) (by decide)
    (by rw [e94]; exact aligned_add env.hres (k := 0x4) (by decide))
  rw [e94, ga1_94, show (0x4 : Word) = BitVec.ofNat 32 0x4 from rfl] at u95
  obtain ⟨M95, hM95⟩ : ∃ M, memStore32 M93 (res + BitVec.ofNat 32 0x4) (x86) = M := ⟨_, rfl⟩
  rw [hM95] at u95
  have cc95 : CodeIn M95 P fieldAddCode := by
    rw [← hM95]; exact CodeIn.store32 cc93 (env.sRC.sub (c := 4) (l := 4) (by decide))
  have ga0_95 : reg n95 a0 = res := ((u95.regs a0).trans (e94))
  have ga2_95 : reg n95 a2 = x87 := ((u95.regs a2).trans (((u94.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u93.regs a2).trans (((u92.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u91.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u90.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u89.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u88.regs a2).trans ((upd_ne (by decide) (by decide)).trans (e87))))))))))))))))))))))
  obtain ⟨n96, d96, u96⟩ := u95.self.sw cc95 fa_at_f8 (off' := 0xFA) (by decide)
    (by rw [ga0_95]; exact aligned_add env.hres (k := 0x8) (by decide))
  rw [ga0_95, ga2_95, show (0x8 : Word) = BitVec.ofNat 32 0x8 from rfl] at u96
  obtain ⟨M96, hM96⟩ : ∃ M, memStore32 M95 (res + BitVec.ofNat 32 0x8) (x87) = M := ⟨_, rfl⟩
  rw [hM96] at u96
  have cc96 : CodeIn M96 P fieldAddCode := by
    rw [← hM96]; exact CodeIn.store32 cc95 (env.sRC.sub (c := 8) (l := 4) (by decide))
  have ga0_96 : reg n96 a0 = res := ((u96.regs a0).trans (ga0_95))
  have ga3_96 : reg n96 a3 = x88 := ((u96.regs a3).trans (((u95.regs a3).trans (((u94.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u93.regs a3).trans (((u92.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u91.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u90.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u89.regs a3).trans ((upd_ne (by decide) (by decide)).trans (e88)))))))))))))))))))))
  obtain ⟨n97, d97, u97⟩ := u96.self.sw cc96 fa_at_fa (off' := 0xFC) (by decide)
    (by rw [ga0_96]; exact aligned_add env.hres (k := 0xC) (by decide))
  rw [ga0_96, ga3_96, show (0xC : Word) = BitVec.ofNat 32 0xC from rfl] at u97
  obtain ⟨M97, hM97⟩ : ∃ M, memStore32 M96 (res + BitVec.ofNat 32 0xC) (x88) = M := ⟨_, rfl⟩
  rw [hM97] at u97
  have cc97 : CodeIn M97 P fieldAddCode := by
    rw [← hM97]; exact CodeIn.store32 cc96 (env.sRC.sub (c := 12) (l := 4) (by decide))
  have ga0_97 : reg n97 a0 = res := ((u97.regs a0).trans (ga0_96))
  have ga4_97 : reg n97 a4 = x89 := ((u97.regs a4).trans (((u96.regs a4).trans (((u95.regs a4).trans (((u94.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u93.regs a4).trans (((u92.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u91.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u90.regs a4).trans ((upd_ne (by decide) (by decide)).trans (e89))))))))))))))))))))
  obtain ⟨n98, d98, u98⟩ := u97.self.sw cc97 fa_at_fc (off' := 0xFE) (by decide)
    (by rw [ga0_97]; exact aligned_add env.hres (k := 0x10) (by decide))
  rw [ga0_97, ga4_97, show (0x10 : Word) = BitVec.ofNat 32 0x10 from rfl] at u98
  obtain ⟨M98, hM98⟩ : ∃ M, memStore32 M97 (res + BitVec.ofNat 32 0x10) (x89) = M := ⟨_, rfl⟩
  rw [hM98] at u98
  have cc98 : CodeIn M98 P fieldAddCode := by
    rw [← hM98]; exact CodeIn.store32 cc97 (env.sRC.sub (c := 16) (l := 4) (by decide))
  have ga0_98 : reg n98 a0 = res := ((u98.regs a0).trans (ga0_97))
  have ga5_98 : reg n98 a5 = x90 := ((u98.regs a5).trans (((u97.regs a5).trans (((u96.regs a5).trans (((u95.regs a5).trans (((u94.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u93.regs a5).trans (((u92.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u91.regs a5).trans ((upd_ne (by decide) (by decide)).trans (e90)))))))))))))))))))
  obtain ⟨n99, d99, u99⟩ := u98.self.sw cc98 fa_at_fe (off' := 0x100) (by decide)
    (by rw [ga0_98]; exact aligned_add env.hres (k := 0x14) (by decide))
  rw [ga0_98, ga5_98, show (0x14 : Word) = BitVec.ofNat 32 0x14 from rfl] at u99
  obtain ⟨M99, hM99⟩ : ∃ M, memStore32 M98 (res + BitVec.ofNat 32 0x14) (x90) = M := ⟨_, rfl⟩
  rw [hM99] at u99
  have cc99 : CodeIn M99 P fieldAddCode := by
    rw [← hM99]; exact CodeIn.store32 cc98 (env.sRC.sub (c := 20) (l := 4) (by decide))
  have g8_99 : reg n99 (8 : Fin 32) = x91 := ((u99.regs (8 : Fin 32)).trans (((u98.regs (8 : Fin 32)).trans (((u97.regs (8 : Fin 32)).trans (((u96.regs (8 : Fin 32)).trans (((u95.regs (8 : Fin 32)).trans (((u94.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u93.regs (8 : Fin 32)).trans (((u92.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e91))))))))))))))))))
  have ga0_99 : reg n99 a0 = res := ((u99.regs a0).trans (ga0_98))
  obtain ⟨n100, d100, u100⟩ := u99.self.sw cc99 fa_at_100 (off' := 0x102) (by decide)
    (by rw [ga0_99]; exact aligned_add env.hres (k := 0x18) (by decide))
  rw [ga0_99, g8_99, show (0x18 : Word) = BitVec.ofNat 32 0x18 from rfl] at u100
  obtain ⟨M100, hM100⟩ : ∃ M, memStore32 M99 (res + BitVec.ofNat 32 0x18) (x91) = M := ⟨_, rfl⟩
  rw [hM100] at u100
  have cc100 : CodeIn M100 P fieldAddCode := by
    rw [← hM100]; exact CodeIn.store32 cc99 (env.sRC.sub (c := 24) (l := 4) (by decide))
  have g9_100 : reg n100 (9 : Fin 32) = x92 := ((u100.regs (9 : Fin 32)).trans (((u99.regs (9 : Fin 32)).trans (((u98.regs (9 : Fin 32)).trans (((u97.regs (9 : Fin 32)).trans (((u96.regs (9 : Fin 32)).trans (((u95.regs (9 : Fin 32)).trans (((u94.regs (9 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u93.regs (9 : Fin 32)).trans (e92)))))))))))))))))
  have ga0_100 : reg n100 a0 = res := ((u100.regs a0).trans (ga0_99))
  obtain ⟨n101, d101, u101⟩ := u100.self.sw cc100 fa_at_102 (off' := 0x104) (by decide)
    (by rw [ga0_100]; exact aligned_add env.hres (k := 0x1C) (by decide))
  rw [ga0_100, g9_100, show (0x1C : Word) = BitVec.ofNat 32 0x1C from rfl] at u101
  obtain ⟨M101, hM101⟩ : ∃ M, memStore32 M100 (res + BitVec.ofNat 32 0x1C) (x92) = M := ⟨_, rfl⟩
  rw [hM101] at u101
  have cc101 : CodeIn M101 P fieldAddCode := by
    rw [← hM101]; exact CodeIn.store32 cc100 (env.sRC.sub (c := 28) (l := 4) (by decide))
  have gsp_101 : reg n101 sp = sp0 + 0xFFFFFF80 := ((u101.regs sp).trans (((u100.regs sp).trans (((u99.regs sp).trans (((u98.regs sp).trans (((u97.regs sp).trans (((u96.regs sp).trans (((u95.regs sp).trans (((u94.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u93.regs sp).trans (((u92.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_91))))))))))))))))))))))
  obtain ⟨n102, x102, d102, hx102, u102⟩ := u101.self.lwG cc101 fa_at_104 (off' := 0x106) (by decide)
    (by rw [gsp_101]; exact aligned_add hGa (k := 0x7C) (by decide))
  rw [gsp_101] at hx102
  have e102 : reg n102 ra = x102 := (u102.regs _).trans (upd_same (by decide))
  have g8_102 : reg n102 (8 : Fin 32) = x91 := ((u102.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u101.regs (8 : Fin 32)).trans (((u100.regs (8 : Fin 32)).trans (g8_99)))))))
  have gsp_102 : reg n102 sp = sp0 + 0xFFFFFF80 := ((u102.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_101)))
  obtain ⟨n103, x103, d103, hx103, u103⟩ := u102.self.lwG cc101 fa_at_106 (off' := 0x108) (by decide)
    (by rw [gsp_102]; exact aligned_add hGa (k := 0x78) (by decide))
  rw [gsp_102] at hx103
  have e103 : reg n103 (8 : Fin 32) = x103 := (u103.regs _).trans (upd_same (by decide))
  have g9_103 : reg n103 (9 : Fin 32) = x92 := ((u103.regs (9 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u102.regs (9 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u101.regs (9 : Fin 32)).trans (g9_100))))))))
  have gsp_103 : reg n103 sp = sp0 + 0xFFFFFF80 := ((u103.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_102)))
  obtain ⟨n104, x104, d104, hx104, u104⟩ := u103.self.lwG cc101 fa_at_108 (off' := 0x10A) (by decide)
    (by rw [gsp_103]; exact aligned_add hGa (k := 0x74) (by decide))
  rw [gsp_103] at hx104
  have e104 : reg n104 (9 : Fin 32) = x104 := (u104.regs _).trans (upd_same (by decide))
  have g18_104 : reg n104 (18 : Fin 32) = res := ((u104.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u103.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u102.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u101.regs (18 : Fin 32)).trans (((u100.regs (18 : Fin 32)).trans (((u99.regs (18 : Fin 32)).trans (((u98.regs (18 : Fin 32)).trans (((u97.regs (18 : Fin 32)).trans (((u96.regs (18 : Fin 32)).trans (((u95.regs (18 : Fin 32)).trans (((u94.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (g18_93))))))))))))))))))))))))))
  have gsp_104 : reg n104 sp = sp0 + 0xFFFFFF80 := ((u104.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_103)))
  obtain ⟨n105, x105, d105, hx105, u105⟩ := u104.self.lwG cc101 fa_at_10a (off' := 0x10C) (by decide)
    (by rw [gsp_104]; exact aligned_add hGa (k := 0x70) (by decide))
  rw [gsp_104] at hx105
  have e105 : reg n105 (18 : Fin 32) = x105 := (u105.regs _).trans (upd_same (by decide))
  have gsp_105 : reg n105 sp = sp0 + 0xFFFFFF80 := ((u105.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_104)))
  obtain ⟨n106, d106, u106⟩ := u105.self.aluImm cc101 fa_at_10c (off' := 0x10E) (by decide)
  have e106 : reg n106 sp = sp0 := (u106.regs _).trans ((upd_same (by decide)).trans (by rw [gsp_105]; show sp0 + 0xFFFFFF80 + 0x80 = sp0; rw [BitVec.add_assoc]; exact BitVec.add_zero _))
  obtain ⟨n107, d107, pc107, mem107, regs107⟩ := u106.self.jalr cc101 fa_at_10e
  have wRes : wordsAt M101 res 8 = [x85, x86, x87, x88, x89, x90, x91, x92] := by
    rw [wordsAt8, ← hM101, ← hM100, ← hM99, ← hM98, ← hM97, ← hM96, ← hM95, ← hM93]
    simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same, Nat.mul_zero]
  have wO : wordsAt n84.mem (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x4) 8 = [x85, x86, x87, x88, x89, x90, x91, x92] := by
    rw [wordsAt8, add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x4 (4 * 0), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x4 (4 * 1), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x4 (4 * 2), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x4 (4 * 3), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x4 (4 * 4), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x4 (4 * 5), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x4 (4 * 6), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x4 (4 * 7)]
    rw [← hx85, ← hx86, ← hx87, ← hx88, ← hx89, ← hx90, ← hx91, ← hx92]
    rfl
  have hval : limbVal (wordsAt M101 res 8) = subRes (limbVal (wordsAt m.mem ap 8) + limbVal (wordsAt m.mem bp 8)) := by
    rw [wRes, ← wO, val84]
  have resF : ∀ x, Sep res 32 x 1 → M101 x = n84.mem x := fun x hx => by
    rw [← hM101, ← hM100, ← hM99, ← hM98, ← hM97, ← hM96, ← hM95, ← hM93]
    simp only [memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide)), memStore32_get_sep (hx.sub (c := 4) (l := 4) (by decide)), memStore32_get_sep (hx.sub (c := 8) (l := 4) (by decide)), memStore32_get_sep (hx.sub (c := 12) (l := 4) (by decide)), memStore32_get_sep (hx.sub (c := 16) (l := 4) (by decide)), memStore32_get_sep (hx.sub (c := 20) (l := 4) (by decide)), memStore32_get_sep (hx.sub (c := 24) (l := 4) (by decide)), memStore32_get_sep (hx.sub (c := 28) (l := 4) (by decide))]
  have slotW : ∀ c, 0x70 ≤ c → c + 4 ≤ 0x80 →
      memLoad32 M101 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 c) = memLoad32 M79 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 c) := fun c h1 h2 =>
    memLoad32_congr (M := M79) (M' := M101) fun j hj => by
      rw [add_ofNat_assoc]
      exact (resF _ (by rw [inS]; exact env.sRS.subR (c := 0x34 + (c + j)) (l := 1) (by omega))).trans
        (frame84 _ (by rw [siA, inS]; exact sep_offsets _ (.inl (by omega)) (by decide) (by omega))
          (by rw [inS, inS]; exact sep_offsets _ (.inl (by omega)) (by decide) (by omega)))
  have sl102 : x102 = reg m ra := by
    rw [← hx102, show (sp0 + 0xFFFFFF80 + 0x7C : Word) = sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x7C from rfl, slotW 0x7C (by decide) (by decide), ← hM79, ← hM78, ← hM77, ← hM76, ← hM75, ← hM73, ← hM72, ← hM71, ← hM70, ← hM68, ← hM67, ← hM66, ← hM65, ← hM64, ← hM63, ← hM62, ← hM61, ← hM60, ← hM5, ← hM4, ← hM3, ← hM2]
    simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same]
  have sl103 : x103 = reg m (8 : Fin 32) := by
    rw [← hx103, show (sp0 + 0xFFFFFF80 + 0x78 : Word) = sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x78 from rfl, slotW 0x78 (by decide) (by decide), ← hM79, ← hM78, ← hM77, ← hM76, ← hM75, ← hM73, ← hM72, ← hM71, ← hM70, ← hM68, ← hM67, ← hM66, ← hM65, ← hM64, ← hM63, ← hM62, ← hM61, ← hM60, ← hM5, ← hM4, ← hM3, ← hM2]
    simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same]
  have sl104 : x104 = reg m (9 : Fin 32) := by
    rw [← hx104, show (sp0 + 0xFFFFFF80 + 0x74 : Word) = sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x74 from rfl, slotW 0x74 (by decide) (by decide), ← hM79, ← hM78, ← hM77, ← hM76, ← hM75, ← hM73, ← hM72, ← hM71, ← hM70, ← hM68, ← hM67, ← hM66, ← hM65, ← hM64, ← hM63, ← hM62, ← hM61, ← hM60, ← hM5, ← hM4, ← hM3, ← hM2]
    simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same]
  have sl105 : x105 = reg m (18 : Fin 32) := by
    rw [← hx105, show (sp0 + 0xFFFFFF80 + 0x70 : Word) = sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x70 from rfl, slotW 0x70 (by decide) (by decide), ← hM79, ← hM78, ← hM77, ← hM76, ← hM75, ← hM73, ← hM72, ← hM71, ← hM70, ← hM68, ← hM67, ← hM66, ← hM65, ← hM64, ← hM63, ← hM62, ← hM61, ← hM60, ← hM5, ← hM4, ← hM3, ← hM2]
    simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same]
  refine ⟨n107, (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.cons d16 (.cons d17 (.cons d18 (.cons d19 (.cons d20 (.cons d21 (.cons d22 (.cons d23 (.cons d24 (.cons d25 (.cons d26 (.cons d27 (.cons d28 (.cons d29 (.cons d30 (.cons d31 (.cons d32 (.cons d33 (.cons d34 (.cons d35 (.cons d36 (.cons d37 (.cons d38 (.cons d39 (.cons d40 (.cons d41 (.cons d42 (.cons d43 (.cons d44 (.cons d45 (.cons d46 (.cons d47 (.cons d48 (.cons d49 (.cons d50 (.cons d51 (.cons d52 (.cons d53 (.cons d54 (.cons d55 (.cons d56 (.cons d57 (.cons d58 (.cons d59 (.cons d60 (.cons d61 (.cons d62 (.cons d63 (.cons d64 (.cons d65 (.cons d66 (.cons d67 (.cons d68 (.cons d69 (.cons d70 (.cons d71 (.cons d72 (.cons d73 (.cons d74 (.cons d75 (.cons d76 (.cons d77 (.cons d78 (.cons d79 (.cons d80 (.cons d81 (.cons d82 (c83.trans (c84.trans (.cons d85 (.cons d86 (.cons d87 (.cons d88 (.cons d89 (.cons d90 (.cons d91 (.cons d92 (.cons d93 (.cons d94 (.cons d95 (.cons d96 (.cons d97 (.cons d98 (.cons d99 (.cons d100 (.cons d101 (.cons d102 (.cons d103 (.cons d104 (.cons d105 (.cons d106 (.single d107))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc107, ((u106.regs ra).trans ((upd_ne (by decide) (by decide)).trans (((u105.regs ra).trans ((upd_ne (by decide) (by decide)).trans (((u104.regs ra).trans ((upd_ne (by decide) (by decide)).trans (((u103.regs ra).trans ((upd_ne (by decide) (by decide)).trans (e102)))))))))))), sl102, add_lit_zero, hra, hret]
  · rw [regs107, e106]
  · intro q q0 q1 q2 q3 q4 q5 q6 q7 qt qt1 qt2 qt3 qt4 qt5 qt6
    rw [regs107]
    by_cases hra' : q = ra
    · subst hra'; rw [((u106.regs ra).trans ((upd_ne (by decide) (by decide)).trans (((u105.regs ra).trans ((upd_ne (by decide) (by decide)).trans (((u104.regs ra).trans ((upd_ne (by decide) (by decide)).trans (((u103.regs ra).trans ((upd_ne (by decide) (by decide)).trans (e102)))))))))))), sl102]
    by_cases hs0 : q = (8 : Fin 32)
    · subst hs0; rw [((u106.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u105.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u104.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e103))))))))), sl103]
    by_cases hs1 : q = (9 : Fin 32)
    · subst hs1; rw [((u106.regs (9 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u105.regs (9 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e104)))))), sl104]
    by_cases hs2 : q = (18 : Fin 32)
    · subst hs2; rw [((u106.regs (18 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e105))), sl105]
    by_cases hsp' : q = sp
    · subst hsp'; rw [e106, hsp]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [u106.self.zero]; rfl
    simp only [u85.regs, u86.regs, u87.regs, u88.regs, u89.regs, u90.regs, u91.regs, u92.regs, u93.regs, u94.regs, u95.regs, u96.regs, u97.regs, u98.regs, u99.regs, u100.regs, u101.regs, u102.regs, u103.regs, u104.regs, u105.regs, u106.regs, upd, h0, hra', hs0, hs1, hs2, hsp', q0, q1, q2, q3, q4, q5, ite_false]
    rw [regs84 q q0 q1 q2 q3 q4 q5 qt, r83 q hra']
    simp only [u1.regs, u2.regs, u3.regs, u4.regs, u5.regs, u6.regs, u7.regs, u8.regs, u9.regs, u10.regs, u11.regs, u12.regs, u13.regs, u14.regs, u15.regs, u16.regs, u17.regs, u18.regs, u19.regs, u20.regs, u21.regs, u22.regs, u23.regs, u24.regs, u25.regs, u26.regs, u27.regs, u28.regs, u29.regs, u30.regs, u31.regs, u32.regs, u33.regs, u34.regs, u35.regs, u36.regs, u37.regs, u38.regs, u39.regs, u40.regs, u41.regs, u42.regs, u43.regs, u44.regs, u45.regs, u46.regs, u47.regs, u48.regs, u49.regs, u50.regs, u51.regs, u52.regs, u53.regs, u54.regs, u55.regs, u56.regs, u57.regs, u58.regs, u59.regs, u60.regs, u61.regs, u62.regs, u63.regs, u64.regs, u65.regs, u66.regs, u67.regs, u68.regs, u69.regs, u70.regs, u71.regs, u72.regs, u73.regs, u74.regs, u75.regs, u76.regs, u77.regs, u78.regs, u79.regs, u80.regs, u81.regs, u82.regs, upd, h0, hs2, hsp', q0, q1, q2, q3, q4, q5, q6, q7, qt, qt1, qt2, qt3, qt4, qt5, ite_false]
  · rw [mem107]; exact hval
  · intro x hS hR; rw [mem107, resF x hR, F84 x hS]

end C3.RV32
