import C3BootProofs.Proofs.FieldMul
import C3BootProofs.Proofs.PointDecode

/-! # `field_impl::sub`, as compiled -/

namespace C3.RV32

open C3.ImageV0

set_option exponentiation.threshold 300 in
/-- `field_impl::sub` modulo `p`, for operands below `p`. -/
theorem subGen_field {A B : Nat} (hA : A < p256) (hB : B < p256) : subGen A B = (A + p256 - B) % p256 := by
  unfold subGen
  have h256 : p256 < 2 ^ 256 := by decide
  by_cases h : A < B
  · rw [ite_eq_left h, show 2 ^ 288 = 2 ^ 256 * 2 ^ 32 from rfl]
    rw [show A + 2 ^ 256 * 2 ^ 32 + p256 - B = (A + p256 - B) + 2 ^ 256 * 2 ^ 32 by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_right h, Nat.mod_eq_of_lt (by omega)]
    rw [show A + p256 - B = (A - B) + p256 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem wordsAt8 (M : Word → BitVec 8) (b : Word) :
    wordsAt M b 8 = [memLoad32 M (b + BitVec.ofNat 32 (4 * 0)), memLoad32 M (b + BitVec.ofNat 32 (4 * 1)),
      memLoad32 M (b + BitVec.ofNat 32 (4 * 2)), memLoad32 M (b + BitVec.ofNat 32 (4 * 3)),
      memLoad32 M (b + BitVec.ofNat 32 (4 * 4)), memLoad32 M (b + BitVec.ofNat 32 (4 * 5)),
      memLoad32 M (b + BitVec.ofNat 32 (4 * 6)), memLoad32 M (b + BitVec.ofNat 32 (4 * 7))] := rfl

/-- Where `field_impl::sub` runs: its code at `P`, `sub_inner`'s code and
helpers where the image puts them relative to it, the 0xB4 bytes of stack
below `sp0` that it and `sub_inner` use, apart from that code, the 8-word
result at `res`, and the 8-word operands at `ap` and `bp`. -/
structure FSEnv (M : Word → BitVec 8) (P sp0 res ap bp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P fieldSubCode
  sicode : CodeIn M (P + 0xFFFFFB88) subInnerCode
  bsub : CodeIn M (siBsub (P + 0xFFFFFB88)) borrowingSubCode
  sisave : CodeIn M (P + 0xFFFFFB88 + 0xDC34) subInnerSaveCode
  sirestore : CodeIn M (P + 0xFFFFFB88 + 0xDE3E) subInnerRestoreCode
  hsp : sp0.toNat % 4 = 0
  hres : res.toNat % 4 = 0
  hap : ap.toNat % 4 = 0
  hbp : bp.toNat % 4 = 0
  hS : 0xB4 ≤ sp0.toNat
  hwr : res.toNat + 32 ≤ 2 ^ 32
  sC : Sep (sp0 + 0xFFFFFF4C) 0xB4 P fieldSubCode.length
  sI : Sep (sp0 + 0xFFFFFF4C) 0xB4 (P + 0xFFFFFB88) subInnerCode.length
  sIb : Sep (sp0 + 0xFFFFFF4C) 0xB4 (siBsub (P + 0xFFFFFB88)) borrowingSubCode.length
  sIs : Sep (sp0 + 0xFFFFFF4C) 0xB4 (P + 0xFFFFFB88 + 0xDC34) subInnerSaveCode.length
  sIr : Sep (sp0 + 0xFFFFFF4C) 0xB4 (P + 0xFFFFFB88 + 0xDE3E) subInnerRestoreCode.length
  sRS : Sep res 32 (sp0 + 0xFFFFFF4C) 0xB4
  sRC : Sep res 32 P fieldSubCode.length
  sAS : Sep ap 32 (sp0 + 0xFFFFFF4C) 0xB4
  sBS : Sep bp 32 (sp0 + 0xFFFFFF4C) 0xB4

theorem fs_frame (sp0 : Word) : sp0 + 0xFFFFFF80 = sp0 + 0xFFFFFF4C + BitVec.ofNat 32 0x34 := by
  rw [BitVec.add_assoc]; rfl

set_option maxHeartbeats 8000000 in
/-- **The compiled `field_impl::sub`**, called with the result at `res` and
the operands `A` at `ap` and `B` at `bp`: it stores `subGen A B`, which is
`A - B` with `p` added back when it borrows, and is `(A + p - B) mod p` for
operands below `p`. It returns with `sp`, `s0`, `ra`, and every register
but `a0` through `a7` and `t0` as they were, and changes no memory outside
the 0xB4 bytes of stack below `sp` and the result. -/
theorem fieldSub_correct (m : Machine) {P sp0 res ap bp retAddr : Word}
    (env : FSEnv m.mem P sp0 res ap bp) (hpc : m.pc = P) (ha0 : reg m a0 = res) (ha1 : reg m a1 = ap)
    (ha2 : reg m a2 = bp) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = sp0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 →
        reg m' q = reg m q) ∧
      limbVal (wordsAt m'.mem res 8) = subGen (limbVal (wordsAt m.mem ap 8)) (limbVal (wordsAt m.mem bp 8)) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → Sep res 32 x 1 → m'.mem x = m.mem x := by
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have hS := env.hS
  have hGa : (sp0 + 0xFFFFFF80).toNat % 4 = 0 := aligned_add env.hsp (k := 0xFFFFFF80) (by decide)
  have cF : ∀ (M' : Word → BitVec 8), (∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M' x = m.mem x) →
      CodeIn M' P fieldSubCode := fun M' hM i hi => by
    rw [hM _ (env.sC.subR (c := i) (l := 1) (by omega))]; exact env.code i hi
  have inF : ∀ c, 0 ≤ c → c + 4 ≤ 0x80 → ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 →
      Sep (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 c) 4 x 1 := fun c _ h2 x hx => by
    rw [fs_frame, add_ofNat_assoc]; exact hx.sub (by omega)
  have F0 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → m.mem x = m.mem x := fun _ _ => rfl
  obtain ⟨n1, d1, u1⟩ := s0.aluImm (cF m.mem F0) fs_at_0 (off' := 0x2) (by decide)
  have e1 : reg n1 sp = sp0 + 0xFFFFFF80 := (u1.regs _).trans ((upd_same (by decide)).trans (by rw [hsp]; rfl))
  have gra_1 : reg n1 ra = reg m ra := ((u1.regs ra).trans ((upd_ne (by decide) (by decide)).trans (rfl)))
  obtain ⟨n2, d2, u2⟩ := u1.self.sw (cF m.mem F0) fs_at_2 (off' := 0x4) (by decide)
    (by rw [e1]; exact aligned_add hGa (k := 0x7C) (by decide))
  rw [e1, gra_1, show (0x7C : Word) = BitVec.ofNat 32 0x7C from rfl] at u2
  obtain ⟨M2, hM2⟩ : ∃ M, memStore32 m.mem (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x7C) (reg m ra) = M := ⟨_, rfl⟩
  rw [hM2] at u2
  have F2 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M2 x = m.mem x := fun x hx => by
    rw [← hM2, memStore32_get_sep (inF 124 (by decide) (by decide) x hx), F0 x hx]
  have g8_2 : reg n2 (8 : Fin 32) = reg m (8 : Fin 32) := ((u2.regs (8 : Fin 32)).trans (((u1.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (rfl)))))
  have gsp_2 : reg n2 sp = sp0 + 0xFFFFFF80 := ((u2.regs sp).trans (e1))
  obtain ⟨n3, d3, u3⟩ := u2.self.sw (cF M2 F2) fs_at_4 (off' := 0x6) (by decide)
    (by rw [gsp_2]; exact aligned_add hGa (k := 0x78) (by decide))
  rw [gsp_2, g8_2, show (0x78 : Word) = BitVec.ofNat 32 0x78 from rfl] at u3
  obtain ⟨M3, hM3⟩ : ∃ M, memStore32 M2 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x78) (reg m (8 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hM3] at u3
  have F3 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M3 x = m.mem x := fun x hx => by
    rw [← hM3, memStore32_get_sep (inF 120 (by decide) (by decide) x hx), F2 x hx]
  have g8_3 : reg n3 (8 : Fin 32) = reg m (8 : Fin 32) := ((u3.regs (8 : Fin 32)).trans (g8_2))
  have ga0_3 : reg n3 a0 = res := ((u3.regs a0).trans (((u2.regs a0).trans (((u1.regs a0).trans ((upd_ne (by decide) (by decide)).trans (ha0)))))))
  obtain ⟨n4, d4, u4⟩ := u3.self.alu (cF M3 F3) fs_at_6 (off' := 0x8) (by decide)
  have e4 : reg n4 (8 : Fin 32) = res := (u4.regs _).trans ((upd_same (by decide)).trans (by rw [u3.self.zero, ga0_3]; exact BitVec.zero_add _))
  have ga0_4 : reg n4 a0 = res := ((u4.regs a0).trans ((upd_ne (by decide) (by decide)).trans (ga0_3)))
  have ga1_4 : reg n4 a1 = ap := ((u4.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u3.regs a1).trans (((u2.regs a1).trans (((u1.regs a1).trans ((upd_ne (by decide) (by decide)).trans (ha1))))))))))
  obtain ⟨n5, x5, d5, hx5, u5⟩ := u4.self.lwG (cF M3 F3) fs_at_8 (off' := 0xA) (by decide)
    (by rw [ga1_4]; exact aligned_add env.hap (k := 0x0) (by decide))
  rw [ga1_4] at hx5
  have e5 : reg n5 a0 = x5 := (u5.regs _).trans (upd_same (by decide))
  have ga1_5 : reg n5 a1 = ap := ((u5.regs a1).trans ((upd_ne (by decide) (by decide)).trans (ga1_4)))
  obtain ⟨n6, x6, d6, hx6, u6⟩ := u5.self.lwG (cF M3 F3) fs_at_a (off' := 0xC) (by decide)
    (by rw [ga1_5]; exact aligned_add env.hap (k := 0x4) (by decide))
  rw [ga1_5] at hx6
  have e6 : reg n6 a3 = x6 := (u6.regs _).trans (upd_same (by decide))
  have ga1_6 : reg n6 a1 = ap := ((u6.regs a1).trans ((upd_ne (by decide) (by decide)).trans (ga1_5)))
  obtain ⟨n7, x7, d7, hx7, u7⟩ := u6.self.lwG (cF M3 F3) fs_at_c (off' := 0xE) (by decide)
    (by rw [ga1_6]; exact aligned_add env.hap (k := 0x8) (by decide))
  rw [ga1_6] at hx7
  have e7 : reg n7 a4 = x7 := (u7.regs _).trans (upd_same (by decide))
  have ga1_7 : reg n7 a1 = ap := ((u7.regs a1).trans ((upd_ne (by decide) (by decide)).trans (ga1_6)))
  obtain ⟨n8, x8, d8, hx8, u8⟩ := u7.self.lwG (cF M3 F3) fs_at_e (off' := 0x10) (by decide)
    (by rw [ga1_7]; exact aligned_add env.hap (k := 0xC) (by decide))
  rw [ga1_7] at hx8
  have e8 : reg n8 a5 = x8 := (u8.regs _).trans (upd_same (by decide))
  have ga1_8 : reg n8 a1 = ap := ((u8.regs a1).trans ((upd_ne (by decide) (by decide)).trans (ga1_7)))
  obtain ⟨n9, x9, d9, hx9, u9⟩ := u8.self.lwG (cF M3 F3) fs_at_10 (off' := 0x14) (by decide)
    (by rw [ga1_8]; exact aligned_add env.hap (k := 0x10) (by decide))
  rw [ga1_8] at hx9
  have e9 : reg n9 a6 = x9 := (u9.regs _).trans (upd_same (by decide))
  have ga1_9 : reg n9 a1 = ap := ((u9.regs a1).trans ((upd_ne (by decide) (by decide)).trans (ga1_8)))
  obtain ⟨n10, x10, d10, hx10, u10⟩ := u9.self.lwG (cF M3 F3) fs_at_14 (off' := 0x18) (by decide)
    (by rw [ga1_9]; exact aligned_add env.hap (k := 0x14) (by decide))
  rw [ga1_9] at hx10
  have e10 : reg n10 a7 = x10 := (u10.regs _).trans (upd_same (by decide))
  have ga1_10 : reg n10 a1 = ap := ((u10.regs a1).trans ((upd_ne (by decide) (by decide)).trans (ga1_9)))
  obtain ⟨n11, x11, d11, hx11, u11⟩ := u10.self.lwG (cF M3 F3) fs_at_18 (off' := 0x1C) (by decide)
    (by rw [ga1_10]; exact aligned_add env.hap (k := 0x18) (by decide))
  rw [ga1_10] at hx11
  have e11 : reg n11 (5 : Fin 32) = x11 := (u11.regs _).trans (upd_same (by decide))
  have ga1_11 : reg n11 a1 = ap := ((u11.regs a1).trans ((upd_ne (by decide) (by decide)).trans (ga1_10)))
  obtain ⟨n12, x12, d12, hx12, u12⟩ := u11.self.lwG (cF M3 F3) fs_at_1c (off' := 0x1E) (by decide)
    (by rw [ga1_11]; exact aligned_add env.hap (k := 0x1C) (by decide))
  rw [ga1_11] at hx12
  have e12 : reg n12 a1 = x12 := (u12.regs _).trans (upd_same (by decide))
  have gsp_12 : reg n12 sp = sp0 + 0xFFFFFF80 := ((u12.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u11.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u10.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u9.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u8.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u7.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u6.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u5.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u4.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u3.regs sp).trans (gsp_2)))))))))))))))))))))))))))))
  have ga0_12 : reg n12 a0 = x5 := ((u12.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u11.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u10.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u9.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u8.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u7.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u6.regs a0).trans ((upd_ne (by decide) (by decide)).trans (e5)))))))))))))))))))))
  obtain ⟨n13, d13, u13⟩ := u12.self.sw (cF M3 F3) fs_at_1e (off' := 0x20) (by decide)
    (by rw [gsp_12]; exact aligned_add hGa (k := 0x30) (by decide))
  rw [gsp_12, ga0_12, show (0x30 : Word) = BitVec.ofNat 32 0x30 from rfl] at u13
  obtain ⟨M13, hM13⟩ : ∃ M, memStore32 M3 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x30) (x5) = M := ⟨_, rfl⟩
  rw [hM13] at u13
  have F13 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M13 x = m.mem x := fun x hx => by
    rw [← hM13, memStore32_get_sep (inF 48 (by decide) (by decide) x hx), F3 x hx]
  have gsp_13 : reg n13 sp = sp0 + 0xFFFFFF80 := ((u13.regs sp).trans (gsp_12))
  have ga3_13 : reg n13 a3 = x6 := ((u13.regs a3).trans (((u12.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u11.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u10.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u9.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u8.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u7.regs a3).trans ((upd_ne (by decide) (by decide)).trans (e6))))))))))))))))))))
  obtain ⟨n14, d14, u14⟩ := u13.self.sw (cF M13 F13) fs_at_20 (off' := 0x22) (by decide)
    (by rw [gsp_13]; exact aligned_add hGa (k := 0x34) (by decide))
  rw [gsp_13, ga3_13, show (0x34 : Word) = BitVec.ofNat 32 0x34 from rfl] at u14
  obtain ⟨M14, hM14⟩ : ∃ M, memStore32 M13 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x34) (x6) = M := ⟨_, rfl⟩
  rw [hM14] at u14
  have F14 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M14 x = m.mem x := fun x hx => by
    rw [← hM14, memStore32_get_sep (inF 52 (by decide) (by decide) x hx), F13 x hx]
  have gsp_14 : reg n14 sp = sp0 + 0xFFFFFF80 := ((u14.regs sp).trans (gsp_13))
  have ga4_14 : reg n14 a4 = x7 := ((u14.regs a4).trans (((u13.regs a4).trans (((u12.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u11.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u10.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u9.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u8.regs a4).trans ((upd_ne (by decide) (by decide)).trans (e7)))))))))))))))))))
  obtain ⟨n15, d15, u15⟩ := u14.self.sw (cF M14 F14) fs_at_22 (off' := 0x24) (by decide)
    (by rw [gsp_14]; exact aligned_add hGa (k := 0x38) (by decide))
  rw [gsp_14, ga4_14, show (0x38 : Word) = BitVec.ofNat 32 0x38 from rfl] at u15
  obtain ⟨M15, hM15⟩ : ∃ M, memStore32 M14 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x38) (x7) = M := ⟨_, rfl⟩
  rw [hM15] at u15
  have F15 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M15 x = m.mem x := fun x hx => by
    rw [← hM15, memStore32_get_sep (inF 56 (by decide) (by decide) x hx), F14 x hx]
  have gsp_15 : reg n15 sp = sp0 + 0xFFFFFF80 := ((u15.regs sp).trans (gsp_14))
  have ga5_15 : reg n15 a5 = x8 := ((u15.regs a5).trans (((u14.regs a5).trans (((u13.regs a5).trans (((u12.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u11.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u10.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u9.regs a5).trans ((upd_ne (by decide) (by decide)).trans (e8))))))))))))))))))
  obtain ⟨n16, d16, u16⟩ := u15.self.sw (cF M15 F15) fs_at_24 (off' := 0x26) (by decide)
    (by rw [gsp_15]; exact aligned_add hGa (k := 0x3C) (by decide))
  rw [gsp_15, ga5_15, show (0x3C : Word) = BitVec.ofNat 32 0x3C from rfl] at u16
  obtain ⟨M16, hM16⟩ : ∃ M, memStore32 M15 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x3C) (x8) = M := ⟨_, rfl⟩
  rw [hM16] at u16
  have F16 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M16 x = m.mem x := fun x hx => by
    rw [← hM16, memStore32_get_sep (inF 60 (by decide) (by decide) x hx), F15 x hx]
  have ga6_16 : reg n16 a6 = x9 := ((u16.regs a6).trans (((u15.regs a6).trans (((u14.regs a6).trans (((u13.regs a6).trans (((u12.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u11.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u10.regs a6).trans ((upd_ne (by decide) (by decide)).trans (e9)))))))))))))))))
  have gsp_16 : reg n16 sp = sp0 + 0xFFFFFF80 := ((u16.regs sp).trans (gsp_15))
  obtain ⟨n17, d17, u17⟩ := u16.self.sw (cF M16 F16) fs_at_26 (off' := 0x28) (by decide)
    (by rw [gsp_16]; exact aligned_add hGa (k := 0x40) (by decide))
  rw [gsp_16, ga6_16, show (0x40 : Word) = BitVec.ofNat 32 0x40 from rfl] at u17
  obtain ⟨M17, hM17⟩ : ∃ M, memStore32 M16 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x40) (x9) = M := ⟨_, rfl⟩
  rw [hM17] at u17
  have F17 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M17 x = m.mem x := fun x hx => by
    rw [← hM17, memStore32_get_sep (inF 64 (by decide) (by decide) x hx), F16 x hx]
  have ga7_17 : reg n17 a7 = x10 := ((u17.regs a7).trans (((u16.regs a7).trans (((u15.regs a7).trans (((u14.regs a7).trans (((u13.regs a7).trans (((u12.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u11.regs a7).trans ((upd_ne (by decide) (by decide)).trans (e10))))))))))))))))
  have gsp_17 : reg n17 sp = sp0 + 0xFFFFFF80 := ((u17.regs sp).trans (gsp_16))
  obtain ⟨n18, d18, u18⟩ := u17.self.sw (cF M17 F17) fs_at_28 (off' := 0x2A) (by decide)
    (by rw [gsp_17]; exact aligned_add hGa (k := 0x44) (by decide))
  rw [gsp_17, ga7_17, show (0x44 : Word) = BitVec.ofNat 32 0x44 from rfl] at u18
  obtain ⟨M18, hM18⟩ : ∃ M, memStore32 M17 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x44) (x10) = M := ⟨_, rfl⟩
  rw [hM18] at u18
  have F18 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M18 x = m.mem x := fun x hx => by
    rw [← hM18, memStore32_get_sep (inF 68 (by decide) (by decide) x hx), F17 x hx]
  have gsp_18 : reg n18 sp = sp0 + 0xFFFFFF80 := ((u18.regs sp).trans (gsp_17))
  have g5_18 : reg n18 (5 : Fin 32) = x11 := ((u18.regs (5 : Fin 32)).trans (((u17.regs (5 : Fin 32)).trans (((u16.regs (5 : Fin 32)).trans (((u15.regs (5 : Fin 32)).trans (((u14.regs (5 : Fin 32)).trans (((u13.regs (5 : Fin 32)).trans (((u12.regs (5 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e11)))))))))))))))
  obtain ⟨n19, d19, u19⟩ := u18.self.sw (cF M18 F18) fs_at_2a (off' := 0x2C) (by decide)
    (by rw [gsp_18]; exact aligned_add hGa (k := 0x48) (by decide))
  rw [gsp_18, g5_18, show (0x48 : Word) = BitVec.ofNat 32 0x48 from rfl] at u19
  obtain ⟨M19, hM19⟩ : ∃ M, memStore32 M18 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x48) (x11) = M := ⟨_, rfl⟩
  rw [hM19] at u19
  have F19 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M19 x = m.mem x := fun x hx => by
    rw [← hM19, memStore32_get_sep (inF 72 (by decide) (by decide) x hx), F18 x hx]
  have gsp_19 : reg n19 sp = sp0 + 0xFFFFFF80 := ((u19.regs sp).trans (gsp_18))
  have ga1_19 : reg n19 a1 = x12 := ((u19.regs a1).trans (((u18.regs a1).trans (((u17.regs a1).trans (((u16.regs a1).trans (((u15.regs a1).trans (((u14.regs a1).trans (((u13.regs a1).trans (e12))))))))))))))
  obtain ⟨n20, d20, u20⟩ := u19.self.sw (cF M19 F19) fs_at_2c (off' := 0x2E) (by decide)
    (by rw [gsp_19]; exact aligned_add hGa (k := 0x4C) (by decide))
  rw [gsp_19, ga1_19, show (0x4C : Word) = BitVec.ofNat 32 0x4C from rfl] at u20
  obtain ⟨M20, hM20⟩ : ∃ M, memStore32 M19 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x4C) (x12) = M := ⟨_, rfl⟩
  rw [hM20] at u20
  have F20 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M20 x = m.mem x := fun x hx => by
    rw [← hM20, memStore32_get_sep (inF 76 (by decide) (by decide) x hx), F19 x hx]
  have gsp_20 : reg n20 sp = sp0 + 0xFFFFFF80 := ((u20.regs sp).trans (gsp_19))
  obtain ⟨n21, d21, u21⟩ := u20.self.sw (cF M20 F20) fs_at_2e (off' := 0x30) (by decide)
    (by rw [gsp_20]; exact aligned_add hGa (k := 0x50) (by decide))
  rw [gsp_20, u20.self.zero, show (0x50 : Word) = BitVec.ofNat 32 0x50 from rfl] at u21
  obtain ⟨M21, hM21⟩ : ∃ M, memStore32 M20 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x50) (0) = M := ⟨_, rfl⟩
  rw [hM21] at u21
  have F21 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M21 x = m.mem x := fun x hx => by
    rw [← hM21, memStore32_get_sep (inF 80 (by decide) (by decide) x hx), F20 x hx]
  have ga0_21 : reg n21 a0 = x5 := ((u21.regs a0).trans (((u20.regs a0).trans (((u19.regs a0).trans (((u18.regs a0).trans (((u17.regs a0).trans (((u16.regs a0).trans (((u15.regs a0).trans (((u14.regs a0).trans (((u13.regs a0).trans (ga0_12))))))))))))))))))
  have ga2_21 : reg n21 a2 = bp := ((u21.regs a2).trans (((u20.regs a2).trans (((u19.regs a2).trans (((u18.regs a2).trans (((u17.regs a2).trans (((u16.regs a2).trans (((u15.regs a2).trans (((u14.regs a2).trans (((u13.regs a2).trans (((u12.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u11.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u10.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u9.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u8.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u7.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u6.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u5.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u4.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u3.regs a2).trans (((u2.regs a2).trans (((u1.regs a2).trans ((upd_ne (by decide) (by decide)).trans (ha2))))))))))))))))))))))))))))))))))))))))))))))))))))
  obtain ⟨n22, x22, d22, hx22, u22⟩ := u21.self.lwG (cF M21 F21) fs_at_30 (off' := 0x32) (by decide)
    (by rw [ga2_21]; exact aligned_add env.hbp (k := 0x0) (by decide))
  rw [ga2_21] at hx22
  have e22 : reg n22 a0 = x22 := (u22.regs _).trans (upd_same (by decide))
  have ga1_22 : reg n22 a1 = x12 := ((u22.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u21.regs a1).trans (((u20.regs a1).trans (ga1_19)))))))
  have ga2_22 : reg n22 a2 = bp := ((u22.regs a2).trans ((upd_ne (by decide) (by decide)).trans (ga2_21)))
  obtain ⟨n23, x23, d23, hx23, u23⟩ := u22.self.lwG (cF M21 F21) fs_at_32 (off' := 0x34) (by decide)
    (by rw [ga2_22]; exact aligned_add env.hbp (k := 0x4) (by decide))
  rw [ga2_22] at hx23
  have e23 : reg n23 a1 = x23 := (u23.regs _).trans (upd_same (by decide))
  have ga2_23 : reg n23 a2 = bp := ((u23.regs a2).trans ((upd_ne (by decide) (by decide)).trans (ga2_22)))
  have ga3_23 : reg n23 a3 = x6 := ((u23.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u22.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u21.regs a3).trans (((u20.regs a3).trans (((u19.regs a3).trans (((u18.regs a3).trans (((u17.regs a3).trans (((u16.regs a3).trans (((u15.regs a3).trans (((u14.regs a3).trans (ga3_13))))))))))))))))))))))
  obtain ⟨n24, x24, d24, hx24, u24⟩ := u23.self.lwG (cF M21 F21) fs_at_34 (off' := 0x36) (by decide)
    (by rw [ga2_23]; exact aligned_add env.hbp (k := 0x8) (by decide))
  rw [ga2_23] at hx24
  have e24 : reg n24 a3 = x24 := (u24.regs _).trans (upd_same (by decide))
  have ga2_24 : reg n24 a2 = bp := ((u24.regs a2).trans ((upd_ne (by decide) (by decide)).trans (ga2_23)))
  have ga4_24 : reg n24 a4 = x7 := ((u24.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u23.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u22.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u21.regs a4).trans (((u20.regs a4).trans (((u19.regs a4).trans (((u18.regs a4).trans (((u17.regs a4).trans (((u16.regs a4).trans (((u15.regs a4).trans (ga4_14)))))))))))))))))))))))
  obtain ⟨n25, x25, d25, hx25, u25⟩ := u24.self.lwG (cF M21 F21) fs_at_36 (off' := 0x38) (by decide)
    (by rw [ga2_24]; exact aligned_add env.hbp (k := 0xC) (by decide))
  rw [ga2_24] at hx25
  have e25 : reg n25 a4 = x25 := (u25.regs _).trans (upd_same (by decide))
  have ga2_25 : reg n25 a2 = bp := ((u25.regs a2).trans ((upd_ne (by decide) (by decide)).trans (ga2_24)))
  have ga5_25 : reg n25 a5 = x8 := ((u25.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u24.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u23.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u22.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u21.regs a5).trans (((u20.regs a5).trans (((u19.regs a5).trans (((u18.regs a5).trans (((u17.regs a5).trans (((u16.regs a5).trans (ga5_15))))))))))))))))))))))))
  obtain ⟨n26, x26, d26, hx26, u26⟩ := u25.self.lwG (cF M21 F21) fs_at_38 (off' := 0x3A) (by decide)
    (by rw [ga2_25]; exact aligned_add env.hbp (k := 0x10) (by decide))
  rw [ga2_25] at hx26
  have e26 : reg n26 a5 = x26 := (u26.regs _).trans (upd_same (by decide))
  have ga6_26 : reg n26 a6 = x9 := ((u26.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u25.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u24.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u23.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u22.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u21.regs a6).trans (((u20.regs a6).trans (((u19.regs a6).trans (((u18.regs a6).trans (((u17.regs a6).trans (ga6_16)))))))))))))))))))))))))
  have ga2_26 : reg n26 a2 = bp := ((u26.regs a2).trans ((upd_ne (by decide) (by decide)).trans (ga2_25)))
  obtain ⟨n27, x27, d27, hx27, u27⟩ := u26.self.lwG (cF M21 F21) fs_at_3a (off' := 0x3E) (by decide)
    (by rw [ga2_26]; exact aligned_add env.hbp (k := 0x14) (by decide))
  rw [ga2_26] at hx27
  have e27 : reg n27 a6 = x27 := (u27.regs _).trans (upd_same (by decide))
  have ga7_27 : reg n27 a7 = x10 := ((u27.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u26.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u25.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u24.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u23.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u22.regs a7).trans ((upd_ne (by decide) (by decide)).trans (((u21.regs a7).trans (((u20.regs a7).trans (((u19.regs a7).trans (((u18.regs a7).trans (ga7_17))))))))))))))))))))))))))
  have ga2_27 : reg n27 a2 = bp := ((u27.regs a2).trans ((upd_ne (by decide) (by decide)).trans (ga2_26)))
  obtain ⟨n28, x28, d28, hx28, u28⟩ := u27.self.lwG (cF M21 F21) fs_at_3e (off' := 0x42) (by decide)
    (by rw [ga2_27]; exact aligned_add env.hbp (k := 0x18) (by decide))
  rw [ga2_27] at hx28
  have e28 : reg n28 a7 = x28 := (u28.regs _).trans (upd_same (by decide))
  have ga2_28 : reg n28 a2 = bp := ((u28.regs a2).trans ((upd_ne (by decide) (by decide)).trans (ga2_27)))
  obtain ⟨n29, x29, d29, hx29, u29⟩ := u28.self.lwG (cF M21 F21) fs_at_42 (off' := 0x44) (by decide)
    (by rw [ga2_28]; exact aligned_add env.hbp (k := 0x1C) (by decide))
  rw [ga2_28] at hx29
  have e29 : reg n29 a2 = x29 := (u29.regs _).trans (upd_same (by decide))
  have gsp_29 : reg n29 sp = sp0 + 0xFFFFFF80 := ((u29.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u28.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u27.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u26.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u25.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u24.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u23.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u22.regs sp).trans ((upd_ne (by decide) (by decide)).trans (((u21.regs sp).trans (gsp_20))))))))))))))))))))))))))
  have ga0_29 : reg n29 a0 = x22 := ((u29.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u28.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u27.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u26.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u25.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u24.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u23.regs a0).trans ((upd_ne (by decide) (by decide)).trans (e22)))))))))))))))))))))
  obtain ⟨n30, d30, u30⟩ := u29.self.sw (cF M21 F21) fs_at_44 (off' := 0x46) (by decide)
    (by rw [gsp_29]; exact aligned_add hGa (k := 0x54) (by decide))
  rw [gsp_29, ga0_29, show (0x54 : Word) = BitVec.ofNat 32 0x54 from rfl] at u30
  obtain ⟨M30, hM30⟩ : ∃ M, memStore32 M21 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x54) (x22) = M := ⟨_, rfl⟩
  rw [hM30] at u30
  have F30 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M30 x = m.mem x := fun x hx => by
    rw [← hM30, memStore32_get_sep (inF 84 (by decide) (by decide) x hx), F21 x hx]
  have gsp_30 : reg n30 sp = sp0 + 0xFFFFFF80 := ((u30.regs sp).trans (gsp_29))
  have ga1_30 : reg n30 a1 = x23 := ((u30.regs a1).trans (((u29.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u28.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u27.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u26.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u25.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u24.regs a1).trans ((upd_ne (by decide) (by decide)).trans (e23))))))))))))))))))))
  obtain ⟨n31, d31, u31⟩ := u30.self.sw (cF M30 F30) fs_at_46 (off' := 0x48) (by decide)
    (by rw [gsp_30]; exact aligned_add hGa (k := 0x58) (by decide))
  rw [gsp_30, ga1_30, show (0x58 : Word) = BitVec.ofNat 32 0x58 from rfl] at u31
  obtain ⟨M31, hM31⟩ : ∃ M, memStore32 M30 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x58) (x23) = M := ⟨_, rfl⟩
  rw [hM31] at u31
  have F31 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M31 x = m.mem x := fun x hx => by
    rw [← hM31, memStore32_get_sep (inF 88 (by decide) (by decide) x hx), F30 x hx]
  have gsp_31 : reg n31 sp = sp0 + 0xFFFFFF80 := ((u31.regs sp).trans (gsp_30))
  have ga3_31 : reg n31 a3 = x24 := ((u31.regs a3).trans (((u30.regs a3).trans (((u29.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u28.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u27.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u26.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u25.regs a3).trans ((upd_ne (by decide) (by decide)).trans (e24)))))))))))))))))))
  obtain ⟨n32, d32, u32⟩ := u31.self.sw (cF M31 F31) fs_at_48 (off' := 0x4A) (by decide)
    (by rw [gsp_31]; exact aligned_add hGa (k := 0x5C) (by decide))
  rw [gsp_31, ga3_31, show (0x5C : Word) = BitVec.ofNat 32 0x5C from rfl] at u32
  obtain ⟨M32, hM32⟩ : ∃ M, memStore32 M31 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x5C) (x24) = M := ⟨_, rfl⟩
  rw [hM32] at u32
  have F32 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M32 x = m.mem x := fun x hx => by
    rw [← hM32, memStore32_get_sep (inF 92 (by decide) (by decide) x hx), F31 x hx]
  have gsp_32 : reg n32 sp = sp0 + 0xFFFFFF80 := ((u32.regs sp).trans (gsp_31))
  have ga4_32 : reg n32 a4 = x25 := ((u32.regs a4).trans (((u31.regs a4).trans (((u30.regs a4).trans (((u29.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u28.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u27.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u26.regs a4).trans ((upd_ne (by decide) (by decide)).trans (e25))))))))))))))))))
  obtain ⟨n33, d33, u33⟩ := u32.self.sw (cF M32 F32) fs_at_4a (off' := 0x4C) (by decide)
    (by rw [gsp_32]; exact aligned_add hGa (k := 0x60) (by decide))
  rw [gsp_32, ga4_32, show (0x60 : Word) = BitVec.ofNat 32 0x60 from rfl] at u33
  obtain ⟨M33, hM33⟩ : ∃ M, memStore32 M32 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x60) (x25) = M := ⟨_, rfl⟩
  rw [hM33] at u33
  have F33 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M33 x = m.mem x := fun x hx => by
    rw [← hM33, memStore32_get_sep (inF 96 (by decide) (by decide) x hx), F32 x hx]
  have gsp_33 : reg n33 sp = sp0 + 0xFFFFFF80 := ((u33.regs sp).trans (gsp_32))
  have ga5_33 : reg n33 a5 = x26 := ((u33.regs a5).trans (((u32.regs a5).trans (((u31.regs a5).trans (((u30.regs a5).trans (((u29.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u28.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u27.regs a5).trans ((upd_ne (by decide) (by decide)).trans (e26)))))))))))))))))
  obtain ⟨n34, d34, u34⟩ := u33.self.sw (cF M33 F33) fs_at_4c (off' := 0x4E) (by decide)
    (by rw [gsp_33]; exact aligned_add hGa (k := 0x64) (by decide))
  rw [gsp_33, ga5_33, show (0x64 : Word) = BitVec.ofNat 32 0x64 from rfl] at u34
  obtain ⟨M34, hM34⟩ : ∃ M, memStore32 M33 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x64) (x26) = M := ⟨_, rfl⟩
  rw [hM34] at u34
  have F34 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M34 x = m.mem x := fun x hx => by
    rw [← hM34, memStore32_get_sep (inF 100 (by decide) (by decide) x hx), F33 x hx]
  have ga6_34 : reg n34 a6 = x27 := ((u34.regs a6).trans (((u33.regs a6).trans (((u32.regs a6).trans (((u31.regs a6).trans (((u30.regs a6).trans (((u29.regs a6).trans ((upd_ne (by decide) (by decide)).trans (((u28.regs a6).trans ((upd_ne (by decide) (by decide)).trans (e27))))))))))))))))
  have gsp_34 : reg n34 sp = sp0 + 0xFFFFFF80 := ((u34.regs sp).trans (gsp_33))
  obtain ⟨n35, d35, u35⟩ := u34.self.sw (cF M34 F34) fs_at_4e (off' := 0x50) (by decide)
    (by rw [gsp_34]; exact aligned_add hGa (k := 0x68) (by decide))
  rw [gsp_34, ga6_34, show (0x68 : Word) = BitVec.ofNat 32 0x68 from rfl] at u35
  obtain ⟨M35, hM35⟩ : ∃ M, memStore32 M34 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x68) (x27) = M := ⟨_, rfl⟩
  rw [hM35] at u35
  have F35 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M35 x = m.mem x := fun x hx => by
    rw [← hM35, memStore32_get_sep (inF 104 (by decide) (by decide) x hx), F34 x hx]
  have ga7_35 : reg n35 a7 = x28 := ((u35.regs a7).trans (((u34.regs a7).trans (((u33.regs a7).trans (((u32.regs a7).trans (((u31.regs a7).trans (((u30.regs a7).trans (((u29.regs a7).trans ((upd_ne (by decide) (by decide)).trans (e28)))))))))))))))
  have gsp_35 : reg n35 sp = sp0 + 0xFFFFFF80 := ((u35.regs sp).trans (gsp_34))
  obtain ⟨n36, d36, u36⟩ := u35.self.sw (cF M35 F35) fs_at_50 (off' := 0x52) (by decide)
    (by rw [gsp_35]; exact aligned_add hGa (k := 0x6C) (by decide))
  rw [gsp_35, ga7_35, show (0x6C : Word) = BitVec.ofNat 32 0x6C from rfl] at u36
  obtain ⟨M36, hM36⟩ : ∃ M, memStore32 M35 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x6C) (x28) = M := ⟨_, rfl⟩
  rw [hM36] at u36
  have F36 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M36 x = m.mem x := fun x hx => by
    rw [← hM36, memStore32_get_sep (inF 108 (by decide) (by decide) x hx), F35 x hx]
  have gsp_36 : reg n36 sp = sp0 + 0xFFFFFF80 := ((u36.regs sp).trans (gsp_35))
  have ga2_36 : reg n36 a2 = x29 := ((u36.regs a2).trans (((u35.regs a2).trans (((u34.regs a2).trans (((u33.regs a2).trans (((u32.regs a2).trans (((u31.regs a2).trans (((u30.regs a2).trans (e29))))))))))))))
  obtain ⟨n37, d37, u37⟩ := u36.self.sw (cF M36 F36) fs_at_52 (off' := 0x54) (by decide)
    (by rw [gsp_36]; exact aligned_add hGa (k := 0x70) (by decide))
  rw [gsp_36, ga2_36, show (0x70 : Word) = BitVec.ofNat 32 0x70 from rfl] at u37
  obtain ⟨M37, hM37⟩ : ∃ M, memStore32 M36 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x70) (x29) = M := ⟨_, rfl⟩
  rw [hM37] at u37
  have F37 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M37 x = m.mem x := fun x hx => by
    rw [← hM37, memStore32_get_sep (inF 112 (by decide) (by decide) x hx), F36 x hx]
  have gsp_37 : reg n37 sp = sp0 + 0xFFFFFF80 := ((u37.regs sp).trans (gsp_36))
  obtain ⟨n38, d38, u38⟩ := u37.self.sw (cF M37 F37) fs_at_54 (off' := 0x56) (by decide)
    (by rw [gsp_37]; exact aligned_add hGa (k := 0x74) (by decide))
  rw [gsp_37, u37.self.zero, show (0x74 : Word) = BitVec.ofNat 32 0x74 from rfl] at u38
  obtain ⟨M38, hM38⟩ : ∃ M, memStore32 M37 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x74) (0) = M := ⟨_, rfl⟩
  rw [hM38] at u38
  have F38 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → M38 x = m.mem x := fun x hx => by
    rw [← hM38, memStore32_get_sep (inF 116 (by decide) (by decide) x hx), F37 x hx]
  have ga0_38 : reg n38 a0 = x22 := ((u38.regs a0).trans (((u37.regs a0).trans (((u36.regs a0).trans (((u35.regs a0).trans (((u34.regs a0).trans (((u33.regs a0).trans (((u32.regs a0).trans (((u31.regs a0).trans (((u30.regs a0).trans (ga0_29))))))))))))))))))
  have gsp_38 : reg n38 sp = sp0 + 0xFFFFFF80 := ((u38.regs sp).trans (gsp_37))
  obtain ⟨n39, d39, u39⟩ := u38.self.aluImm (cF M38 F38) fs_at_56 (off' := 0x58) (by decide)
  have e39 : reg n39 a0 = sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0xC := (u39.regs _).trans ((upd_same (by decide)).trans (by rw [gsp_38]; rfl))
  have gsp_39 : reg n39 sp = sp0 + 0xFFFFFF80 := ((u39.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_38)))
  have ga1_39 : reg n39 a1 = x23 := ((u39.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u38.regs a1).trans (((u37.regs a1).trans (((u36.regs a1).trans (((u35.regs a1).trans (((u34.regs a1).trans (((u33.regs a1).trans (((u32.regs a1).trans (((u31.regs a1).trans (ga1_30)))))))))))))))))))
  obtain ⟨n40, d40, u40⟩ := u39.self.aluImm (cF M38 F38) fs_at_58 (off' := 0x5A) (by decide)
  have e40 : reg n40 a1 = sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x30 := (u40.regs _).trans ((upd_same (by decide)).trans (by rw [gsp_39]; rfl))
  have gsp_40 : reg n40 sp = sp0 + 0xFFFFFF80 := ((u40.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_39)))
  have ga2_40 : reg n40 a2 = x29 := ((u40.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u39.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u38.regs a2).trans (((u37.regs a2).trans (ga2_36))))))))))
  obtain ⟨n41, d41, u41⟩ := u40.self.aluImm (cF M38 F38) fs_at_5a (off' := 0x5C) (by decide)
  have e41 : reg n41 a2 = sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x54 := (u41.regs _).trans ((upd_same (by decide)).trans (by rw [gsp_40]; rfl))
  have w0x30 : wordsAt M38 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x30) 9 = [x5, x6, x7, x8, x9, x10, x11, x12, 0] := by
    rw [wordsAt9, add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x30 (4 * 0), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x30 (4 * 1), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x30 (4 * 2), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x30 (4 * 3), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x30 (4 * 4), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x30 (4 * 5), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x30 (4 * 6), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x30 (4 * 7), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x30 (4 * 8)]
    rw [← hM38, ← hM37, ← hM36, ← hM35, ← hM34, ← hM33, ← hM32, ← hM31, ← hM30, ← hM21, ← hM20, ← hM19, ← hM18, ← hM17, ← hM16, ← hM15, ← hM14, ← hM13, ← hM3, ← hM2]
    simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same]
  have w0x54 : wordsAt M38 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x54) 9 = [x22, x23, x24, x25, x26, x27, x28, x29, 0] := by
    rw [wordsAt9, add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x54 (4 * 0), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x54 (4 * 1), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x54 (4 * 2), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x54 (4 * 3), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x54 (4 * 4), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x54 (4 * 5), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x54 (4 * 6), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x54 (4 * 7), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0x54 (4 * 8)]
    rw [← hM38, ← hM37, ← hM36, ← hM35, ← hM34, ← hM33, ← hM32, ← hM31, ← hM30, ← hM21, ← hM20, ← hM19, ← hM18, ← hM17, ← hM16, ← hM15, ← hM14, ← hM13, ← hM3, ← hM2]
    simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same]
  have ldA : ∀ c, c + 4 ≤ 32 → memLoad32 M3 (ap + BitVec.ofNat 32 c) = memLoad32 m.mem (ap + BitVec.ofNat 32 c) :=
    fun c h => memLoad32_congr (M := m.mem) (M' := M3) fun j hj => F3 _ (by
      have := env.sAS.symm.subR (c := c + j) (l := 1) (by omega); rwa [← add_ofNat_assoc] at this)
  have wA : wordsAt m.mem ap 8 = [x5, x6, x7, x8, x9, x10, x11, x12] := by
    rw [wordsAt8, (ldA (4 * 0) (by decide)).symm.trans hx5, (ldA (4 * 1) (by decide)).symm.trans hx6, (ldA (4 * 2) (by decide)).symm.trans hx7, (ldA (4 * 3) (by decide)).symm.trans hx8, (ldA (4 * 4) (by decide)).symm.trans hx9, (ldA (4 * 5) (by decide)).symm.trans hx10, (ldA (4 * 6) (by decide)).symm.trans hx11, (ldA (4 * 7) (by decide)).symm.trans hx12]
  have ldB : ∀ c, c + 4 ≤ 32 → memLoad32 M21 (bp + BitVec.ofNat 32 c) = memLoad32 m.mem (bp + BitVec.ofNat 32 c) :=
    fun c h => memLoad32_congr (M := m.mem) (M' := M21) fun j hj => F21 _ (by
      have := env.sBS.symm.subR (c := c + j) (l := 1) (by omega); rwa [← add_ofNat_assoc] at this)
  have wB : wordsAt m.mem bp 8 = [x22, x23, x24, x25, x26, x27, x28, x29] := by
    rw [wordsAt8, (ldB (4 * 0) (by decide)).symm.trans hx22, (ldB (4 * 1) (by decide)).symm.trans hx23, (ldB (4 * 2) (by decide)).symm.trans hx24, (ldB (4 * 3) (by decide)).symm.trans hx25, (ldB (4 * 4) (by decide)).symm.trans hx26, (ldB (4 * 5) (by decide)).symm.trans hx27, (ldB (4 * 6) (by decide)).symm.trans hx28, (ldB (4 * 7) (by decide)).symm.trans hx29]
  have hsi : (P + 0xFFFFFB88).toNat % 2 = 0 := even_at P env.hP 0xFFFFFB88 (by decide)
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
  have senv : SIEnvG M38 (P + 0xFFFFFB88) (sp0 + 0xFFFFFF80) (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0xC) (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x30)
      (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x54) :=
    ⟨hsi, codeX env.sicode env.sI F38, codeX env.bsub env.sIb F38, codeX env.sisave env.sIs F38,
      codeX env.sirestore env.sIr F38, hGa, aligned_add hGa (by decide), aligned_add hGa (by decide),
      aligned_add hGa (by decide), by rw [BitVec.toNat_add]; have : (0xFFFFFF80 : Word).toNat = 4294967168 := rfl; have := sp0.isLt; omega,
      by rw [siA]; exact env.sI.sub (by decide), by rw [siA]; exact env.sIb.sub (by decide),
      by rw [siA]; exact env.sIs.sub (by decide), by rw [siA]; exact env.sIr.sub (by decide),
      by rw [inS]; exact env.sI.sub (by decide), by rw [inS]; exact env.sIr.sub (by decide),
      by rw [inS, siA]; exact sep_offsets _ (.inr (by decide)) (by decide) (by decide),
      by rw [inS, siA]; exact sep_offsets _ (.inr (by decide)) (by decide) (by decide),
      by rw [inS, siA]; exact sep_offsets _ (.inr (by decide)) (by decide) (by decide),
      ⟨wrapC 0xC (by decide), wrapC 0x30 (by decide), wrapC 0x54 (by decide)⟩⟩
  obtain ⟨n42, c42, pc42, mem42, regs42⟩ := u41.self.callRa (cF M38 F38) fs_at_5c fs_at_60
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) hsi
  have r42 := PEnv.reg1 regs42 u41.self.zero
  rw [← mem42] at senv
  obtain ⟨n43, c43, pc43, sp43, regs43, val43, mask43, frame43⟩ := subInner_gen n42 senv pc42
    (by rw [r42 a0 (by decide), ((u41.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u40.regs a0).trans ((upd_ne (by decide) (by decide)).trans (e39))))))]) (by rw [r42 a1 (by decide), ((u41.regs a1).trans ((upd_ne (by decide) (by decide)).trans (e40)))])
    (by rw [r42 a2 (by decide), e41]) (by rw [regs42]; simp +decide [upd])
    (even_clear _ (even_at P env.hP 0x64 (by decide))) (by rw [r42 sp (by decide), ((u41.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_40)))])
  rw [mem42, w0x30, w0x54] at val43
  rw [mem42] at frame43
  have s43 : St n43.mem P n43 0x64 (reg n43) := ⟨by rw [pc43], rfl, fun _ => rfl⟩
  have F43 : ∀ x, Sep (sp0 + 0xFFFFFF4C) 0xB4 x 1 → n43.mem x = m.mem x := fun x hx =>
    (frame43 x (by rw [siA]; exact hx.sub (by decide)) (by rw [inS]; exact hx.sub (by decide))).trans (F38 x hx)
  have cc43 := cF n43.mem F43
  obtain ⟨n44, x44, d44, hx44, u44⟩ := s43.lwG cc43 fs_at_64 (off' := 0x66) (by decide)
    (by rw [sp43]; exact aligned_add hGa (k := 0xC) (by decide))
  rw [sp43] at hx44
  have e44 : reg n44 a0 = x44 := (u44.regs _).trans (upd_same (by decide))
  have gsp_44 : reg n44 sp = sp0 + 0xFFFFFF80 := ((u44.regs sp).trans ((upd_ne (by decide) (by decide)).trans (sp43)))
  obtain ⟨n45, x45, d45, hx45, u45⟩ := u44.self.lwG cc43 fs_at_66 (off' := 0x68) (by decide)
    (by rw [gsp_44]; exact aligned_add hGa (k := 0x10) (by decide))
  rw [gsp_44] at hx45
  have e45 : reg n45 a1 = x45 := (u45.regs _).trans (upd_same (by decide))
  have gsp_45 : reg n45 sp = sp0 + 0xFFFFFF80 := ((u45.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_44)))
  obtain ⟨n46, x46, d46, hx46, u46⟩ := u45.self.lwG cc43 fs_at_68 (off' := 0x6A) (by decide)
    (by rw [gsp_45]; exact aligned_add hGa (k := 0x14) (by decide))
  rw [gsp_45] at hx46
  have e46 : reg n46 a2 = x46 := (u46.regs _).trans (upd_same (by decide))
  have gsp_46 : reg n46 sp = sp0 + 0xFFFFFF80 := ((u46.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_45)))
  obtain ⟨n47, x47, d47, hx47, u47⟩ := u46.self.lwG cc43 fs_at_6a (off' := 0x6C) (by decide)
    (by rw [gsp_46]; exact aligned_add hGa (k := 0x18) (by decide))
  rw [gsp_46] at hx47
  have e47 : reg n47 a3 = x47 := (u47.regs _).trans (upd_same (by decide))
  have gsp_47 : reg n47 sp = sp0 + 0xFFFFFF80 := ((u47.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_46)))
  obtain ⟨n48, x48, d48, hx48, u48⟩ := u47.self.lwG cc43 fs_at_6c (off' := 0x6E) (by decide)
    (by rw [gsp_47]; exact aligned_add hGa (k := 0x1C) (by decide))
  rw [gsp_47] at hx48
  have e48 : reg n48 a4 = x48 := (u48.regs _).trans (upd_same (by decide))
  have gsp_48 : reg n48 sp = sp0 + 0xFFFFFF80 := ((u48.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_47)))
  obtain ⟨n49, x49, d49, hx49, u49⟩ := u48.self.lwG cc43 fs_at_6e (off' := 0x70) (by decide)
    (by rw [gsp_48]; exact aligned_add hGa (k := 0x20) (by decide))
  rw [gsp_48] at hx49
  have e49 : reg n49 a5 = x49 := (u49.regs _).trans (upd_same (by decide))
  have gsp_49 : reg n49 sp = sp0 + 0xFFFFFF80 := ((u49.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_48)))
  obtain ⟨n50, x50, d50, hx50, u50⟩ := u49.self.lwG cc43 fs_at_70 (off' := 0x72) (by decide)
    (by rw [gsp_49]; exact aligned_add hGa (k := 0x24) (by decide))
  rw [gsp_49] at hx50
  have e50 : reg n50 a6 = x50 := (u50.regs _).trans (upd_same (by decide))
  have gsp_50 : reg n50 sp = sp0 + 0xFFFFFF80 := ((u50.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_49)))
  obtain ⟨n51, x51, d51, hx51, u51⟩ := u50.self.lwG cc43 fs_at_72 (off' := 0x74) (by decide)
    (by rw [gsp_50]; exact aligned_add hGa (k := 0x28) (by decide))
  rw [gsp_50] at hx51
  have e51 : reg n51 a7 = x51 := (u51.regs _).trans (upd_same (by decide))
  have g8_51 : reg n51 (8 : Fin 32) = res := ((u51.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u50.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u49.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u48.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u47.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u46.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u45.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u44.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans ((regs43 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((r42 _ (by decide)).trans (((u41.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u40.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u39.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u38.regs (8 : Fin 32)).trans (((u37.regs (8 : Fin 32)).trans (((u36.regs (8 : Fin 32)).trans (((u35.regs (8 : Fin 32)).trans (((u34.regs (8 : Fin 32)).trans (((u33.regs (8 : Fin 32)).trans (((u32.regs (8 : Fin 32)).trans (((u31.regs (8 : Fin 32)).trans (((u30.regs (8 : Fin 32)).trans (((u29.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u28.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u27.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u26.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u25.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u24.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u23.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u22.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u21.regs (8 : Fin 32)).trans (((u20.regs (8 : Fin 32)).trans (((u19.regs (8 : Fin 32)).trans (((u18.regs (8 : Fin 32)).trans (((u17.regs (8 : Fin 32)).trans (((u16.regs (8 : Fin 32)).trans (((u15.regs (8 : Fin 32)).trans (((u14.regs (8 : Fin 32)).trans (((u13.regs (8 : Fin 32)).trans (((u12.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u11.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u10.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u9.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u8.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u7.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u6.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u5.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e4)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  have ga0_51 : reg n51 a0 = x44 := ((u51.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u50.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u49.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u48.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u47.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u46.regs a0).trans ((upd_ne (by decide) (by decide)).trans (((u45.regs a0).trans ((upd_ne (by decide) (by decide)).trans (e44)))))))))))))))))))))
  obtain ⟨n52, d52, u52⟩ := u51.self.sw cc43 fs_at_74 (off' := 0x76) (by decide)
    (by rw [g8_51]; exact aligned_add env.hres (k := 0x0) (by decide))
  rw [g8_51, ga0_51, show (0x0 : Word) = BitVec.ofNat 32 0x0 from rfl] at u52
  obtain ⟨M52, hM52⟩ : ∃ M, memStore32 n43.mem (res + BitVec.ofNat 32 0x0) (x44) = M := ⟨_, rfl⟩
  rw [hM52] at u52
  have cc52 : CodeIn M52 P fieldSubCode := by
    rw [← hM52]; exact CodeIn.store32 cc43 (env.sRC.sub (c := 0) (l := 4) (by decide))
  have g8_52 : reg n52 (8 : Fin 32) = res := ((u52.regs (8 : Fin 32)).trans (g8_51))
  have ga1_52 : reg n52 a1 = x45 := ((u52.regs a1).trans (((u51.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u50.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u49.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u48.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u47.regs a1).trans ((upd_ne (by decide) (by decide)).trans (((u46.regs a1).trans ((upd_ne (by decide) (by decide)).trans (e45))))))))))))))))))))
  obtain ⟨n53, d53, u53⟩ := u52.self.sw cc52 fs_at_76 (off' := 0x78) (by decide)
    (by rw [g8_52]; exact aligned_add env.hres (k := 0x4) (by decide))
  rw [g8_52, ga1_52, show (0x4 : Word) = BitVec.ofNat 32 0x4 from rfl] at u53
  obtain ⟨M53, hM53⟩ : ∃ M, memStore32 M52 (res + BitVec.ofNat 32 0x4) (x45) = M := ⟨_, rfl⟩
  rw [hM53] at u53
  have cc53 : CodeIn M53 P fieldSubCode := by
    rw [← hM53]; exact CodeIn.store32 cc52 (env.sRC.sub (c := 4) (l := 4) (by decide))
  have g8_53 : reg n53 (8 : Fin 32) = res := ((u53.regs (8 : Fin 32)).trans (g8_52))
  have ga2_53 : reg n53 a2 = x46 := ((u53.regs a2).trans (((u52.regs a2).trans (((u51.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u50.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u49.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u48.regs a2).trans ((upd_ne (by decide) (by decide)).trans (((u47.regs a2).trans ((upd_ne (by decide) (by decide)).trans (e46)))))))))))))))))))
  obtain ⟨n54, d54, u54⟩ := u53.self.sw cc53 fs_at_78 (off' := 0x7A) (by decide)
    (by rw [g8_53]; exact aligned_add env.hres (k := 0x8) (by decide))
  rw [g8_53, ga2_53, show (0x8 : Word) = BitVec.ofNat 32 0x8 from rfl] at u54
  obtain ⟨M54, hM54⟩ : ∃ M, memStore32 M53 (res + BitVec.ofNat 32 0x8) (x46) = M := ⟨_, rfl⟩
  rw [hM54] at u54
  have cc54 : CodeIn M54 P fieldSubCode := by
    rw [← hM54]; exact CodeIn.store32 cc53 (env.sRC.sub (c := 8) (l := 4) (by decide))
  have g8_54 : reg n54 (8 : Fin 32) = res := ((u54.regs (8 : Fin 32)).trans (g8_53))
  have ga3_54 : reg n54 a3 = x47 := ((u54.regs a3).trans (((u53.regs a3).trans (((u52.regs a3).trans (((u51.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u50.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u49.regs a3).trans ((upd_ne (by decide) (by decide)).trans (((u48.regs a3).trans ((upd_ne (by decide) (by decide)).trans (e47))))))))))))))))))
  obtain ⟨n55, d55, u55⟩ := u54.self.sw cc54 fs_at_7a (off' := 0x7C) (by decide)
    (by rw [g8_54]; exact aligned_add env.hres (k := 0xC) (by decide))
  rw [g8_54, ga3_54, show (0xC : Word) = BitVec.ofNat 32 0xC from rfl] at u55
  obtain ⟨M55, hM55⟩ : ∃ M, memStore32 M54 (res + BitVec.ofNat 32 0xC) (x47) = M := ⟨_, rfl⟩
  rw [hM55] at u55
  have cc55 : CodeIn M55 P fieldSubCode := by
    rw [← hM55]; exact CodeIn.store32 cc54 (env.sRC.sub (c := 12) (l := 4) (by decide))
  have g8_55 : reg n55 (8 : Fin 32) = res := ((u55.regs (8 : Fin 32)).trans (g8_54))
  have ga4_55 : reg n55 a4 = x48 := ((u55.regs a4).trans (((u54.regs a4).trans (((u53.regs a4).trans (((u52.regs a4).trans (((u51.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u50.regs a4).trans ((upd_ne (by decide) (by decide)).trans (((u49.regs a4).trans ((upd_ne (by decide) (by decide)).trans (e48)))))))))))))))))
  obtain ⟨n56, d56, u56⟩ := u55.self.sw cc55 fs_at_7c (off' := 0x7E) (by decide)
    (by rw [g8_55]; exact aligned_add env.hres (k := 0x10) (by decide))
  rw [g8_55, ga4_55, show (0x10 : Word) = BitVec.ofNat 32 0x10 from rfl] at u56
  obtain ⟨M56, hM56⟩ : ∃ M, memStore32 M55 (res + BitVec.ofNat 32 0x10) (x48) = M := ⟨_, rfl⟩
  rw [hM56] at u56
  have cc56 : CodeIn M56 P fieldSubCode := by
    rw [← hM56]; exact CodeIn.store32 cc55 (env.sRC.sub (c := 16) (l := 4) (by decide))
  have g8_56 : reg n56 (8 : Fin 32) = res := ((u56.regs (8 : Fin 32)).trans (g8_55))
  have ga5_56 : reg n56 a5 = x49 := ((u56.regs a5).trans (((u55.regs a5).trans (((u54.regs a5).trans (((u53.regs a5).trans (((u52.regs a5).trans (((u51.regs a5).trans ((upd_ne (by decide) (by decide)).trans (((u50.regs a5).trans ((upd_ne (by decide) (by decide)).trans (e49))))))))))))))))
  obtain ⟨n57, d57, u57⟩ := u56.self.sw cc56 fs_at_7e (off' := 0x80) (by decide)
    (by rw [g8_56]; exact aligned_add env.hres (k := 0x14) (by decide))
  rw [g8_56, ga5_56, show (0x14 : Word) = BitVec.ofNat 32 0x14 from rfl] at u57
  obtain ⟨M57, hM57⟩ : ∃ M, memStore32 M56 (res + BitVec.ofNat 32 0x14) (x49) = M := ⟨_, rfl⟩
  rw [hM57] at u57
  have cc57 : CodeIn M57 P fieldSubCode := by
    rw [← hM57]; exact CodeIn.store32 cc56 (env.sRC.sub (c := 20) (l := 4) (by decide))
  have g8_57 : reg n57 (8 : Fin 32) = res := ((u57.regs (8 : Fin 32)).trans (g8_56))
  have ga6_57 : reg n57 a6 = x50 := ((u57.regs a6).trans (((u56.regs a6).trans (((u55.regs a6).trans (((u54.regs a6).trans (((u53.regs a6).trans (((u52.regs a6).trans (((u51.regs a6).trans ((upd_ne (by decide) (by decide)).trans (e50)))))))))))))))
  obtain ⟨n58, d58, u58⟩ := u57.self.sw cc57 fs_at_80 (off' := 0x84) (by decide)
    (by rw [g8_57]; exact aligned_add env.hres (k := 0x18) (by decide))
  rw [g8_57, ga6_57, show (0x18 : Word) = BitVec.ofNat 32 0x18 from rfl] at u58
  obtain ⟨M58, hM58⟩ : ∃ M, memStore32 M57 (res + BitVec.ofNat 32 0x18) (x50) = M := ⟨_, rfl⟩
  rw [hM58] at u58
  have cc58 : CodeIn M58 P fieldSubCode := by
    rw [← hM58]; exact CodeIn.store32 cc57 (env.sRC.sub (c := 24) (l := 4) (by decide))
  have g8_58 : reg n58 (8 : Fin 32) = res := ((u58.regs (8 : Fin 32)).trans (g8_57))
  have ga7_58 : reg n58 a7 = x51 := ((u58.regs a7).trans (((u57.regs a7).trans (((u56.regs a7).trans (((u55.regs a7).trans (((u54.regs a7).trans (((u53.regs a7).trans (((u52.regs a7).trans (e51))))))))))))))
  obtain ⟨n59, d59, u59⟩ := u58.self.sw cc58 fs_at_84 (off' := 0x88) (by decide)
    (by rw [g8_58]; exact aligned_add env.hres (k := 0x1C) (by decide))
  rw [g8_58, ga7_58, show (0x1C : Word) = BitVec.ofNat 32 0x1C from rfl] at u59
  obtain ⟨M59, hM59⟩ : ∃ M, memStore32 M58 (res + BitVec.ofNat 32 0x1C) (x51) = M := ⟨_, rfl⟩
  rw [hM59] at u59
  have cc59 : CodeIn M59 P fieldSubCode := by
    rw [← hM59]; exact CodeIn.store32 cc58 (env.sRC.sub (c := 28) (l := 4) (by decide))
  have gsp_59 : reg n59 sp = sp0 + 0xFFFFFF80 := ((u59.regs sp).trans (((u58.regs sp).trans (((u57.regs sp).trans (((u56.regs sp).trans (((u55.regs sp).trans (((u54.regs sp).trans (((u53.regs sp).trans (((u52.regs sp).trans (((u51.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_50)))))))))))))))))))
  obtain ⟨n60, x60, d60, hx60, u60⟩ := u59.self.lwG cc59 fs_at_88 (off' := 0x8A) (by decide)
    (by rw [gsp_59]; exact aligned_add hGa (k := 0x7C) (by decide))
  rw [gsp_59] at hx60
  have e60 : reg n60 ra = x60 := (u60.regs _).trans (upd_same (by decide))
  have g8_60 : reg n60 (8 : Fin 32) = res := ((u60.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (((u59.regs (8 : Fin 32)).trans (g8_58)))))
  have gsp_60 : reg n60 sp = sp0 + 0xFFFFFF80 := ((u60.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_59)))
  obtain ⟨n61, x61, d61, hx61, u61⟩ := u60.self.lwG cc59 fs_at_8a (off' := 0x8C) (by decide)
    (by rw [gsp_60]; exact aligned_add hGa (k := 0x78) (by decide))
  rw [gsp_60] at hx61
  have e61 : reg n61 (8 : Fin 32) = x61 := (u61.regs _).trans (upd_same (by decide))
  have gsp_61 : reg n61 sp = sp0 + 0xFFFFFF80 := ((u61.regs sp).trans ((upd_ne (by decide) (by decide)).trans (gsp_60)))
  obtain ⟨n62, d62, u62⟩ := u61.self.aluImm cc59 fs_at_8c (off' := 0x8E) (by decide)
  have e62 : reg n62 sp = sp0 := (u62.regs _).trans ((upd_same (by decide)).trans (by rw [gsp_61]; show sp0 + 0xFFFFFF80 + 0x80 = sp0; rw [BitVec.add_assoc]; exact BitVec.add_zero _))
  obtain ⟨n63, d63, pc63, mem63, regs63⟩ := u62.self.jalr cc59 fs_at_8e
  have wR : wordsAt M59 res 8 = [x44, x45, x46, x47, x48, x49, x50, x51] := by
    rw [wordsAt8, ← hM59, ← hM58, ← hM57, ← hM56, ← hM55, ← hM54, ← hM53, ← hM52]
    simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same, Nat.mul_zero]
  have wO : wordsAt n43.mem (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0xC) 8 = [x44, x45, x46, x47, x48, x49, x50, x51] := by
    rw [wordsAt8, add_ofNat_assoc (sp0 + 0xFFFFFF80) 0xC (4 * 0), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0xC (4 * 1), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0xC (4 * 2), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0xC (4 * 3), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0xC (4 * 4), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0xC (4 * 5), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0xC (4 * 6), add_ofNat_assoc (sp0 + 0xFFFFFF80) 0xC (4 * 7)]
    rw [← hx44, ← hx45, ← hx46, ← hx47, ← hx48, ← hx49, ← hx50, ← hx51]
    rfl
  have l9 : ∀ (l : List Word), limbVal (l ++ [0]) = limbVal l := fun l => by
    rw [limbVal_append, show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  have hval : limbVal (wordsAt M59 res 8) = subGen (limbVal (wordsAt m.mem ap 8)) (limbVal (wordsAt m.mem bp 8)) := by
    rw [wR, ← wO, val43, wA, wB]
    rw [show [x5, x6, x7, x8, x9, x10, x11, x12, 0] = [x5, x6, x7, x8, x9, x10, x11, x12] ++ [0] from rfl, l9,
      show [x22, x23, x24, x25, x26, x27, x28, x29, 0] = [x22, x23, x24, x25, x26, x27, x28, x29] ++ [0] from rfl, l9]
  have resF : ∀ x, Sep res 32 x 1 → M59 x = n43.mem x := fun x hx => by
    rw [← hM59, ← hM58, ← hM57, ← hM56, ← hM55, ← hM54, ← hM53, ← hM52]
    simp only [memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide)), memStore32_get_sep (hx.sub (c := 4) (l := 4) (by decide)), memStore32_get_sep (hx.sub (c := 8) (l := 4) (by decide)), memStore32_get_sep (hx.sub (c := 12) (l := 4) (by decide)), memStore32_get_sep (hx.sub (c := 16) (l := 4) (by decide)), memStore32_get_sep (hx.sub (c := 20) (l := 4) (by decide)), memStore32_get_sep (hx.sub (c := 24) (l := 4) (by decide)), memStore32_get_sep (hx.sub (c := 28) (l := 4) (by decide))]
  have slotW : ∀ c, 0x78 ≤ c → c + 4 ≤ 0x80 →
      memLoad32 M59 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 c) = memLoad32 M38 (sp0 + 0xFFFFFF80 + BitVec.ofNat 32 c) := fun c h1 h2 =>
    memLoad32_congr (M := M38) (M' := M59) fun j hj => by
      rw [add_ofNat_assoc]
      exact (resF _ (by rw [inS]; exact env.sRS.subR (c := 0x34 + (c + j)) (l := 1) (by omega))).trans
        (frame43 _ (by rw [siA, inS]; exact sep_offsets _ (.inl (by omega)) (by decide) (by omega))
          (by rw [inS, inS]; exact sep_offsets _ (.inl (by omega)) (by decide) (by omega)))
  have sl60 : x60 = reg m ra := by
    rw [← hx60, show (sp0 + 0xFFFFFF80 + 0x7C : Word) = sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x7C from rfl, slotW 0x7C (by decide) (by decide), ← hM38, ← hM37, ← hM36, ← hM35, ← hM34, ← hM33, ← hM32, ← hM31, ← hM30, ← hM21, ← hM20, ← hM19, ← hM18, ← hM17, ← hM16, ← hM15, ← hM14, ← hM13, ← hM3, ← hM2]
    simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same]
  have sl61 : x61 = reg m (8 : Fin 32) := by
    rw [← hx61, show (sp0 + 0xFFFFFF80 + 0x78 : Word) = sp0 + 0xFFFFFF80 + BitVec.ofNat 32 0x78 from rfl, slotW 0x78 (by decide) (by decide), ← hM38, ← hM37, ← hM36, ← hM35, ← hM34, ← hM33, ← hM32, ← hM31, ← hM30, ← hM21, ← hM20, ← hM19, ← hM18, ← hM17, ← hM16, ← hM15, ← hM14, ← hM13, ← hM3, ← hM2]
    simp (disch := decide) only [memLoad32_store32_off, memLoad32_store32_same]
  refine ⟨n63, (.cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 (.cons d16 (.cons d17 (.cons d18 (.cons d19 (.cons d20 (.cons d21 (.cons d22 (.cons d23 (.cons d24 (.cons d25 (.cons d26 (.cons d27 (.cons d28 (.cons d29 (.cons d30 (.cons d31 (.cons d32 (.cons d33 (.cons d34 (.cons d35 (.cons d36 (.cons d37 (.cons d38 (.cons d39 (.cons d40 (.cons d41 (c42.trans (c43.trans (.cons d44 (.cons d45 (.cons d46 (.cons d47 (.cons d48 (.cons d49 (.cons d50 (.cons d51 (.cons d52 (.cons d53 (.cons d54 (.cons d55 (.cons d56 (.cons d57 (.cons d58 (.cons d59 (.cons d60 (.cons d61 (.cons d62 (.single d63))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc63, ((u62.regs ra).trans ((upd_ne (by decide) (by decide)).trans (((u61.regs ra).trans ((upd_ne (by decide) (by decide)).trans (e60)))))), sl60, add_lit_zero, hra, hret]
  · rw [regs63, e62]
  · intro q q0 q1 q2 q3 q4 q5 q6 q7 qt
    rw [regs63]
    by_cases hra' : q = ra
    · subst hra'; rw [((u62.regs ra).trans ((upd_ne (by decide) (by decide)).trans (((u61.regs ra).trans ((upd_ne (by decide) (by decide)).trans (e60)))))), sl60]
    by_cases hs0 : q = (8 : Fin 32)
    · subst hs0; rw [((u62.regs (8 : Fin 32)).trans ((upd_ne (by decide) (by decide)).trans (e61))), sl61]
    by_cases hsp' : q = sp
    · subst hsp'; rw [e62, hsp]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; rw [u62.self.zero]; rfl
    simp only [u44.regs, u45.regs, u46.regs, u47.regs, u48.regs, u49.regs, u50.regs, u51.regs, u52.regs, u53.regs, u54.regs, u55.regs, u56.regs, u57.regs, u58.regs, u59.regs, u60.regs, u61.regs, u62.regs, upd, h0, hra', hs0, hsp', q0, q1, q2, q3, q4, q5, q6, q7, ite_false]
    rw [regs43 q q0 q1 q2 q3 q4 q5 qt, r42 q hra']
    simp only [u1.regs, u2.regs, u3.regs, u4.regs, u5.regs, u6.regs, u7.regs, u8.regs, u9.regs, u10.regs, u11.regs, u12.regs, u13.regs, u14.regs, u15.regs, u16.regs, u17.regs, u18.regs, u19.regs, u20.regs, u21.regs, u22.regs, u23.regs, u24.regs, u25.regs, u26.regs, u27.regs, u28.regs, u29.regs, u30.regs, u31.regs, u32.regs, u33.regs, u34.regs, u35.regs, u36.regs, u37.regs, u38.regs, u39.regs, u40.regs, u41.regs, upd, h0, hs0, hsp', q0, q1, q2, q3, q4, q5, q6, q7, qt, ite_false]
  · rw [mem63]; exact hval
  · intro x hS hR; rw [mem63, resF x hR, F43 x hS]

end C3.RV32
