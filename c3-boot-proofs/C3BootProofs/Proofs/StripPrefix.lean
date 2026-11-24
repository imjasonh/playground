import C3BootProofs.Proofs.SliceEq
import C3BootProofs.Proofs.LeafStep

/-!
# `strip_prefix`, as compiled

`<[u8]>::strip_prefix` returns the rest of `s` after `prefix` when `s`
starts with it. The compiled function takes `s` and `prefix` as pointer and
length pairs in `a0` through `a3`, compares with
`<[u8]>::equal_same_length`, and returns the rest as a pointer in `a0` and
a length in `a1`, with a null pointer for `None`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem spf_at_0 : fetchRel stripPrefixCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem spf_at_2 : fetchRel stripPrefixCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem spf_at_4 : fetchRel stripPrefixCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x8, 2) := by decide
theorem spf_at_6 : fetchRel stripPrefixCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x4, 2) := by decide
theorem spf_at_8 : fetchRel stripPrefixCode 0x8 = some (.branch .bgeu a1 a3 0x8, 4) := by decide
theorem spf_at_c : fetchRel stripPrefixCode 0xC = some (.aluImm .add a0 x0 0x0, 2) := by decide
theorem spf_at_e : fetchRel stripPrefixCode 0xE = some (.jal x0 0x1C, 2) := by decide
theorem spf_at_10 : fetchRel stripPrefixCode 0x10 = some (.alu .sub (8 : Fin 32) a1 a3, 4) := by decide
theorem spf_at_14 : fetchRel stripPrefixCode 0x14 = some (.alu .add (9 : Fin 32) a0 a3, 4) := by decide
theorem spf_at_18 : fetchRel stripPrefixCode 0x18 = some (.alu .add a1 x0 a2, 2) := by decide
theorem spf_at_1a : fetchRel stripPrefixCode 0x1A = some (.alu .add a2 x0 a3, 2) := by decide
theorem spf_at_1c : fetchRel stripPrefixCode 0x1C = some (.auipc ra 0x0, 4) := by decide
theorem spf_at_20 : fetchRel stripPrefixCode 0x20 = some (.jalr ra ra 0xFFFFFFCE, 4) := by decide
theorem spf_at_24 : fetchRel stripPrefixCode 0x24 = some (.alu .sub a0 x0 a0, 4) := by decide
theorem spf_at_28 : fetchRel stripPrefixCode 0x28 = some (.alu .and a0 a0 (9 : Fin 32), 2) := by decide
theorem spf_at_2a : fetchRel stripPrefixCode 0x2A = some (.alu .add a1 x0 (8 : Fin 32), 2) := by decide
theorem spf_at_2c : fetchRel stripPrefixCode 0x2C = some (.load .lw ra sp 0xC, 2) := by decide
theorem spf_at_2e : fetchRel stripPrefixCode 0x2E = some (.load .lw (8 : Fin 32) sp 0x8, 2) := by decide
theorem spf_at_30 : fetchRel stripPrefixCode 0x30 = some (.load .lw (9 : Fin 32) sp 0x4, 2) := by decide
theorem spf_at_32 : fetchRel stripPrefixCode 0x32 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem spf_at_34 : fetchRel stripPrefixCode 0x34 = some (.jalr x0 ra 0x0, 2) := by decide
end

theorem spf_sub {a b : Nat} (ha : a < 2 ^ 32) (hb : b ≤ a) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

set_option maxHeartbeats 4000000 in
/-- **The compiled `<[u8]>::strip_prefix`**: called with `s` of `sl` bytes
and `prefix` of `pl` bytes, it returns `s + pl` in `a0` when `pl ≤ sl` and
the first `pl` bytes of `s` are `prefix`, and 0 otherwise. When `pl ≤ sl`,
`a1` holds `sl - pl`. It writes only `a0` through `a4` and the 20 bytes
below `sp`. -/
theorem stripPrefix_correct (m : Machine) {base retAddr s pre : Word} {sl pl : Nat}
    (hc : CodeIn m.mem base stripPrefixCode) (hbase : base.toNat % 2 = 0)
    (he : CodeIn m.mem (base + 0xFFFFFFEA) equalSameLengthCode)
    (hmc : CodeIn m.mem (base + 0xFFFFFFEA + 0xD3BE) memcmpCode) (hpc : m.pc = base)
    (ha0 : reg m a0 = s) (ha1 : reg m a1 = BitVec.ofNat 32 sl) (ha2 : reg m a2 = pre)
    (ha3 : reg m a3 = BitVec.ofNat 32 pl) (hsl : sl < 2 ^ 32) (hpl : pl < 2 ^ 32)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : (reg m sp).toNat % 4 = 0)
    (sSC : Sep (reg m sp + 0xFFFFFFEC) 20 base stripPrefixCode.length)
    (sSE : Sep (reg m sp + 0xFFFFFFEC) 20 (base + 0xFFFFFFEA) equalSameLengthCode.length)
    (sSM : Sep (reg m sp + 0xFFFFFFEC) 20 (base + 0xFFFFFFEA + 0xD3BE) memcmpCode.length)
    (sSS : Sep (reg m sp + 0xFFFFFFEC) 20 s sl) (sSP : Sep (reg m sp + 0xFFFFFFEC) 20 pre pl) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      reg m' a0 = (if pl ≤ sl ∧ memBytes m.mem s pl = memBytes m.mem pre pl then s + BitVec.ofNat 32 pl
        else 0) ∧
      (pl ≤ sl → reg m' a1 = BitVec.ofNat 32 (sl - pl)) ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → reg m' r = reg m r) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFEC) 20 x 1 → m'.mem x = m.mem x := by
  obtain ⟨R0, hR0⟩ : ∃ R0, reg m sp + 0xFFFFFFEC = R0 := ⟨_, rfl⟩
  rw [hR0] at sSC sSE sSM sSS sSP ⊢
  have hR0a : R0.toNat % 4 = 0 := by rw [← hR0]; exact aligned_add hsp (k := 0xFFFFFFEC) (by decide)
  have al : ∀ c, c % 4 = 0 → (R0 + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c h => aligned_add hR0a h
  have sl4 : ∀ {y : Word} {l : Nat} (c : Nat), c + 4 ≤ 20 → Sep R0 20 y l →
      Sep (R0 + BitVec.ofNat 32 c) 4 y l := fun c h hs => hs.sub h
  have z4 : ∀ {y : Word} {l : Nat}, Sep R0 20 y l → Sep R0 4 y l := fun h => by
    have := sl4 0 (by decide) h; rwa [add_ofNat_zero] at this
  have e16 : reg m sp + 0xFFFFFFF0 + 0xC = R0 + BitVec.ofNat 32 16 := by
    rw [← hR0, BitVec.add_assoc, BitVec.add_assoc]; rfl
  have e12 : reg m sp + 0xFFFFFFF0 + 0x8 = R0 + BitVec.ofNat 32 12 := by
    rw [← hR0, BitVec.add_assoc, BitVec.add_assoc]; rfl
  have e8 : reg m sp + 0xFFFFFFF0 + 0x4 = R0 + BitVec.ofNat 32 8 := by
    rw [← hR0, BitVec.add_assoc, BitVec.add_assoc]; rfl
  have eS : reg m sp + 0xFFFFFFF0 + 0xFFFFFFFC = R0 := by rw [← hR0, BitVec.add_assoc]; rfl
  -- the prologue saves `ra`, `s0`, and `s1`
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc spf_at_0 (off' := 2) (by decide)
  have g1 : reg n1 sp = reg m sp + 0xFFFFFFF0 := ls_get u1 (by decide)
  have k1 : ∀ q, q ≠ sp → reg n1 q = reg m q := fun q h => ls_oth u1 h
  obtain ⟨n2, d2, u2⟩ := u1.self.sw hc spf_at_2 (off' := 4) (by decide) (by rw [g1, e16]; exact al 16 (by decide))
  rw [g1, e16, k1 ra (by decide), hra] at u2
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 m.mem (R0 + BitVec.ofNat 32 16) retAddr = M1 := ⟨_, rfl⟩
  rw [hM1] at u2
  have hc1 : CodeIn M1 base stripPrefixCode := by rw [← hM1]; exact hc.store32 (sl4 16 (by decide) sSC)
  obtain ⟨n3, d3, u3⟩ := u2.sw hc1 spf_at_4 (off' := 6) (by decide) (by rw [g1, e12]; exact al 12 (by decide))
  rw [g1, e12, k1 8 (by decide)] at u3
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore32 M1 (R0 + BitVec.ofNat 32 12) (reg m 8) = M2 := ⟨_, rfl⟩
  rw [hM2] at u3
  have hc2 : CodeIn M2 base stripPrefixCode := by rw [← hM2]; exact hc1.store32 (sl4 12 (by decide) sSC)
  obtain ⟨n4, d4, u4⟩ := u3.sw hc2 spf_at_6 (off' := 8) (by decide) (by rw [g1, e8]; exact al 8 (by decide))
  rw [g1, e8, k1 9 (by decide)] at u4
  obtain ⟨M3, hM3⟩ : ∃ M3, memStore32 M2 (R0 + BitVec.ofNat 32 8) (reg m 9) = M3 := ⟨_, rfl⟩
  rw [hM3] at u4
  have fr3 : ∀ x, Sep (R0 + BitVec.ofNat 32 8) 4 x 1 → Sep (R0 + BitVec.ofNat 32 12) 4 x 1 →
      Sep (R0 + BitVec.ofNat 32 16) 4 x 1 → M3 x = m.mem x := fun x h8 h12 h16 => by
    rw [← hM3, memStore32_get_sep h8, ← hM2, memStore32_get_sep h12, ← hM1, memStore32_get_sep h16]
  have fr20 : ∀ {y : Word} {l : Nat}, Sep R0 20 y l → ∀ j, j < l →
      M3 (y + BitVec.ofNat 32 j) = m.mem (y + BitVec.ofNat 32 j) := fun hs j hj =>
    fr3 _ ((sl4 8 (by decide) hs).subR (by omega)) ((sl4 12 (by decide) hs).subR (by omega))
      ((sl4 16 (by decide) hs).subR (by omega))
  have frX : ∀ x, Sep R0 20 x 1 → M3 x = m.mem x := fun x hx => by
    have := fr20 hx 0 (by decide); rwa [add_ofNat_zero] at this
  have hc3 : CodeIn M3 base stripPrefixCode := fun i hi => by rw [fr20 sSC i hi]; exact hc i hi
  have he3 : CodeIn M3 (base + 0xFFFFFFEA) equalSameLengthCode := fun i hi => by rw [fr20 sSE i hi]; exact he i hi
  have hm3 : CodeIn M3 (base + 0xFFFFFFEA + 0xD3BE) memcmpCode := fun i hi => by rw [fr20 sSM i hi]; exact hmc i hi
  have p816 : Sep (R0 + BitVec.ofNat 32 8) 4 (R0 + BitVec.ofNat 32 16) 4 :=
    sep_offsets R0 (Or.inl (by decide)) (by decide) (by decide)
  have p812 : Sep (R0 + BitVec.ofNat 32 8) 4 (R0 + BitVec.ofNat 32 12) 4 :=
    sep_offsets R0 (Or.inl (by decide)) (by decide) (by decide)
  have p1216 : Sep (R0 + BitVec.ofNat 32 12) 4 (R0 + BitVec.ofNat 32 16) 4 :=
    sep_offsets R0 (Or.inl (by decide)) (by decide) (by decide)
  have l16 : memLoad32 M3 (R0 + BitVec.ofNat 32 16) = retAddr := by
    rw [← hM3, memLoad32_store32_sep p816, ← hM2, memLoad32_store32_sep p1216, ← hM1, memLoad32_store32_same]
  have l12 : memLoad32 M3 (R0 + BitVec.ofNat 32 12) = reg m 8 := by
    rw [← hM3, memLoad32_store32_sep p812, ← hM2, memLoad32_store32_same]
  have l8 : memLoad32 M3 (R0 + BitVec.ofNat 32 8) = reg m 9 := by
    rw [← hM3, memLoad32_store32_same]
  -- the epilogue, from 0x2A
  have tail : ∀ {n : Machine} {M : Word → BitVec 8}, CodeIn M base stripPrefixCode → St M base n 0x2A (reg n) →
      reg n sp = reg m sp + 0xFFFFFFF0 → memLoad32 M (R0 + BitVec.ofNat 32 16) = retAddr →
      memLoad32 M (R0 + BitVec.ofNat 32 12) = reg m 8 → memLoad32 M (R0 + BitVec.ofNat 32 8) = reg m 9 →
      ∃ n', Steps n n' ∧ n'.pc = retAddr ∧ n'.mem = M ∧ reg n' a1 = reg n 8 ∧
        (∀ r, r ≠ a1 → r ≠ ra → r ≠ 8 → r ≠ 9 → r ≠ sp → reg n' r = reg n r) ∧
        reg n' ra = retAddr ∧ reg n' 8 = reg m 8 ∧ reg n' 9 = reg m 9 ∧ reg n' sp = reg m sp := by
    intro n M hcM st hsp' j16 j12 j8
    obtain ⟨t1, d1, v1⟩ := st.alu hcM spf_at_2a (off' := 0x2C) (by decide)
    have w1 : reg t1 a1 = reg n 8 := by rw [ls_get v1 (by decide), ls_r0]; exact BitVec.zero_add _
    have o1 : ∀ q, q ≠ a1 → reg t1 q = reg n q := fun q h => ls_oth v1 h
    have sp1 : reg t1 sp = reg m sp + 0xFFFFFFF0 := by rw [o1 sp (by decide), hsp']
    obtain ⟨t2, d2, v2⟩ := v1.self.lw hcM spf_at_2c (off' := 0x2E) (by decide)
      (by rw [sp1, e16]; exact al 16 (by decide))
    rw [sp1, e16, j16] at v2
    have w2 : reg t2 ra = retAddr := ls_get v2 (by decide)
    have o2 : ∀ q, q ≠ ra → reg t2 q = reg t1 q := fun q h => ls_oth v2 h
    have sp2 : reg t2 sp = reg m sp + 0xFFFFFFF0 := by rw [o2 sp (by decide), sp1]
    obtain ⟨t3, d3, v3⟩ := v2.self.lw hcM spf_at_2e (off' := 0x30) (by decide)
      (by rw [sp2, e12]; exact al 12 (by decide))
    rw [sp2, e12, j12] at v3
    have w3 : reg t3 8 = reg m 8 := ls_get v3 (by decide)
    have o3 : ∀ q, q ≠ 8 → reg t3 q = reg t2 q := fun q h => ls_oth v3 h
    have sp3 : reg t3 sp = reg m sp + 0xFFFFFFF0 := by rw [o3 sp (by decide), sp2]
    obtain ⟨t4, d4, v4⟩ := v3.self.lw hcM spf_at_30 (off' := 0x32) (by decide)
      (by rw [sp3, e8]; exact al 8 (by decide))
    rw [sp3, e8, j8] at v4
    have w4 : reg t4 9 = reg m 9 := ls_get v4 (by decide)
    have o4 : ∀ q, q ≠ 9 → reg t4 q = reg t3 q := fun q h => ls_oth v4 h
    obtain ⟨t5, d5, v5⟩ := v4.self.aluImm hcM spf_at_32 (off' := 0x34) (by decide)
    have w5 : reg t5 sp = reg m sp := by
      rw [ls_get v5 (by decide), ev_add, o4 sp (by decide), sp3, BitVec.add_assoc,
        show (0xFFFFFFF0 : Word) + 0x10 = 0 by decide, add_lit_zero]
    have o5 : ∀ q, q ≠ sp → reg t5 q = reg t4 q := fun q h => ls_oth v5 h
    obtain ⟨t6, d6, pc6, mem6, regs6⟩ := v5.self.jalr hcM spf_at_34
    refine ⟨t6, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6))))), ?_, mem6, ?_,
      fun r h1 hr h8 h9 hs => ?_, ?_, ?_, ?_, ?_⟩
    · rw [pc6, o5 ra (by decide), o4 ra (by decide), o3 ra (by decide), w2, add_lit_zero, hret]
    · rw [regs6, o5 a1 (by decide), o4 a1 (by decide), o3 a1 (by decide), o2 a1 (by decide), w1]
    · rw [regs6, o5 r hs, o4 r h9, o3 r h8, o2 r hr, o1 r h1]
    · rw [regs6, o5 ra (by decide), o4 ra (by decide), o3 ra (by decide), w2]
    · rw [regs6, o5 8 (by decide), o4 8 (by decide), w3]
    · rw [regs6, o5 9 (by decide), w4]
    · rw [regs6, w5]
  rcases Nat.lt_or_ge sl pl with hlt | hge
  · -- `s` is shorter than `prefix`: `None`
    obtain ⟨n5, d5, u5⟩ := u4.notTaken hc3 0xC spf_at_8 (by decide) (by
      rw [k1 a1 (by decide), k1 a3 (by decide), ha1, ha3, ls_uge, ls_ofNat_toNat_lt hsl,
        ls_ofNat_toNat_lt hpl, decide_eq_true hlt]; rfl)
    obtain ⟨n6, d6, u6⟩ := u5.aluImm hc3 spf_at_c (off' := 0xE) (by decide)
    obtain ⟨n7, d7, u7⟩ := u6.jump hc3 spf_at_e (off' := 0x2A) (by decide) (by
      rw [u6.pc]; exact ls_even hbase 0xE 0x1C 0x2A (by decide) (by decide))
    obtain ⟨n', c', pc', mem', -, ko, kra, k8, k9, ksp⟩ := tail hc3 u7.self
      (by rw [ls_oth u7 (show sp ≠ a0 by decide), g1]) l16 l12 l8
    refine ⟨n', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 c')))))), pc', ?_,
      fun h => absurd h (Nat.not_le.mpr hlt), fun r h0 h1 h2 h3 h4 => ?_, fun x hx => by rw [mem', frX x hx]⟩
    · rw [ko a0 (by decide) (by decide) (by decide) (by decide) (by decide), ls_get u7 (by decide), ls_r0,
        if_neg (fun h : pl ≤ sl ∧ memBytes m.mem s pl = memBytes m.mem pre pl => absurd h.1 (Nat.not_le.mpr hlt))]
      rfl
    · by_cases e1 : r = ra
      · rw [e1, kra, hra]
      by_cases e2 : r = 8
      · rw [e2, k8]
      by_cases e3 : r = 9
      · rw [e3, k9]
      by_cases e4 : r = sp
      · rw [e4, ksp]
      rw [ko r h1 e1 e2 e3 e4, ls_oth u7 h0, k1 r e4]
  · -- compare the first `pl` bytes
    obtain ⟨n5, d5, u5⟩ := u4.taken hc3 0x10 spf_at_8 (by decide) (by
      rw [k1 a1 (by decide), k1 a3 (by decide), ha1, ha3, ls_uge, ls_ofNat_toNat_lt hsl,
        ls_ofNat_toNat_lt hpl, decide_eq_false (Nat.not_lt.mpr hge)]; rfl)
    obtain ⟨n6, d6, u6⟩ := u5.alu hc3 spf_at_10 (off' := 0x14) (by decide)
    have v6 : reg n6 8 = BitVec.ofNat 32 (sl - pl) := by
      rw [ls_get u6 (by decide), k1 a1 (by decide), k1 a3 (by decide), ha1, ha3]; exact spf_sub hsl hge
    have o6 : ∀ q, q ≠ 8 → reg n6 q = reg n1 q := fun q h => ls_oth u6 h
    obtain ⟨n7, d7, u7⟩ := u6.self.alu hc3 spf_at_14 (off' := 0x18) (by decide)
    have v7 : reg n7 9 = s + BitVec.ofNat 32 pl := by
      rw [ls_get u7 (by decide), o6 a0 (by decide), o6 a3 (by decide), k1 a0 (by decide), k1 a3 (by decide),
        ha0, ha3]; rfl
    have o7 : ∀ q, q ≠ 9 → reg n7 q = reg n6 q := fun q h => ls_oth u7 h
    obtain ⟨n8, d8, u8⟩ := u7.self.alu hc3 spf_at_18 (off' := 0x1A) (by decide)
    have v8 : reg n8 a1 = pre := by
      rw [ls_get u8 (by decide), ls_r0, o7 a2 (by decide), o6 a2 (by decide), k1 a2 (by decide), ha2]
      exact BitVec.zero_add _
    have o8 : ∀ q, q ≠ a1 → reg n8 q = reg n7 q := fun q h => ls_oth u8 h
    obtain ⟨n9, d9, u9⟩ := u8.self.alu hc3 spf_at_1a (off' := 0x1C) (by decide)
    have v9 : reg n9 a2 = BitVec.ofNat 32 pl := by
      rw [ls_get u9 (by decide), ls_r0, o8 a3 (by decide), o7 a3 (by decide), o6 a3 (by decide),
        k1 a3 (by decide), ha3]
      exact BitVec.zero_add _
    have o9 : ∀ q, q ≠ a2 → reg n9 q = reg n8 q := fun q h => ls_oth u9 h
    obtain ⟨n10, c10, pc10, mem10, regs10⟩ := u9.self.callRa hc3 spf_at_1c spf_at_20 (cb := base + 0xFFFFFFEA)
      (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at base hbase 0xFFFFFFEA (by decide))
    have r10 := PEnv.reg1 regs10 u9.self.zero
    have sp10 : reg n10 sp = reg m sp + 0xFFFFFFF0 := by
      rw [r10 sp (by decide), o9 sp (by decide), o8 sp (by decide), o7 sp (by decide), o6 sp (by decide), g1]
    have sSSp : Sep R0 20 s pl := by have := sSS.subR (c := 0) (l := pl) (by omega); rwa [add_ofNat_zero] at this
    obtain ⟨n11, c11, pc11, a011, k11, f11⟩ := equalSameLength_correct n10 (base := base + 0xFFFFFFEA)
      (p := s) (q := pre) (n := pl) (even_at base hbase 0xFFFFFFEA (by decide)) (by rw [mem10]; exact he3)
      (by rw [mem10]; exact hm3) pc10
      (by rw [r10 a0 (by decide), o9 a0 (by decide), o8 a0 (by decide), o7 a0 (by decide), o6 a0 (by decide),
        k1 a0 (by decide), ha0])
      (by rw [r10 a1 (by decide), o9 a1 (by decide), v8]) (by rw [r10 a2 (by decide), v9]) hpl
      (by rw [regs10]; simp +decide [upd]) (even_clear _ (even_at base hbase (0x1C + 8) (by decide)))
      (by rw [sp10]; exact aligned_add hsp (k := 0xFFFFFFF0) (by decide))
      (by rw [sp10, eS]; exact z4 sSE) (by rw [sp10, eS]; exact z4 sSM)
      (by rw [sp10, eS]; exact z4 sSSp) (by rw [sp10, eS]; exact z4 sSP)
    rw [sp10, eS] at f11
    rw [mem10, memBytes_congr (fr20 sSSp), memBytes_congr (fr20 sSP)] at a011
    have hc11 : CodeIn n11.mem base stripPrefixCode := fun i hi => by
      rw [f11 _ ((z4 sSC).subR (c := i) (l := 1) hi), mem10]; exact hc3 i hi
    have keep : ∀ c, 8 ≤ c → c ≤ 16 → memLoad32 n11.mem (R0 + BitVec.ofNat 32 c) =
        memLoad32 M3 (R0 + BitVec.ofNat 32 c) := fun c h1 h2 => memLoad32_congr fun j hj => by
      have := sep_offsets R0 (c := 0) (n := 4) (d := c) (k := 4) (Or.inl (by omega)) (by decide) (by omega)
      rw [add_ofNat_zero] at this
      rw [f11 _ (this.subR (c := j) (l := 1) (by omega)), mem10]
    have u12 : St n11.mem base n11 0x24 (reg n11) := ⟨by rw [pc11], rfl, fun _ => rfl⟩
    obtain ⟨n13, d13, u13⟩ := u12.alu hc11 spf_at_24 (off' := 0x28) (by decide)
    obtain ⟨n14, d14, u14⟩ := u13.self.alu hc11 spf_at_28 (off' := 0x2A) (by decide)
    have v14 : reg n14 a0 =
        if memBytes m.mem s pl = memBytes m.mem pre pl then s + BitVec.ofNat 32 pl else 0 := by
      rw [ls_get u14 (by decide), ls_get u13 (by decide), ls_oth u13 (show (9 : Fin 32) ≠ a0 by decide), ls_r0,
        a011, k11 9 (by decide) (by decide) (by decide) (by decide) (by decide), r10 9 (by decide),
        o9 9 (by decide), o8 9 (by decide), v7]
      exact ls_mask _ _
    have k14 : ∀ q, q ≠ a0 → reg n14 q = reg n11 q := fun q h => by rw [ls_oth u14 h, ls_oth u13 h]
    obtain ⟨n', c', pc', mem', a1', ko, kra, k8, k9, ksp⟩ := tail hc11 u14.self
      (by rw [k14 sp (by decide), k11 sp (by decide) (by decide) (by decide) (by decide) (by decide), sp10])
      ((keep 16 (by decide) (by decide)).trans l16) ((keep 12 (by decide) (by decide)).trans l12)
      ((keep 8 (by decide) (by decide)).trans l8)
    refine ⟨n', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
      (c10.trans (c11.trans (.cons d13 (.cons d14 c')))))))))))), pc', ?_, fun _ => ?_,
      fun r h0 h1 h2 h3 h4 => ?_, fun x hx => by rw [mem', f11 x (z4 hx), mem10, frX x hx]⟩
    · rw [ko a0 (by decide) (by decide) (by decide) (by decide) (by decide), v14]
      by_cases hP : memBytes m.mem s pl = memBytes m.mem pre pl
      · rw [if_pos hP, if_pos ⟨hge, hP⟩]
      · rw [if_neg hP, if_neg (fun h : pl ≤ sl ∧ memBytes m.mem s pl = memBytes m.mem pre pl => hP h.2)]
    · rw [a1', k14 8 (by decide), k11 8 (by decide) (by decide) (by decide) (by decide) (by decide),
        r10 8 (by decide), o9 8 (by decide), o8 8 (by decide), o7 8 (by decide), v6]
    · by_cases e1 : r = ra
      · rw [e1, kra, hra]
      by_cases e2 : r = 8
      · rw [e2, k8]
      by_cases e3 : r = 9
      · rw [e3, k9]
      by_cases e4 : r = sp
      · rw [e4, ksp]
      rw [ko r h1 e1 e2 e3 e4, k14 r h0, k11 r h0 h1 h2 h3 h4, r10 r e1, o9 r h2, o8 r h1, o7 r e3, o6 r e2,
        k1 r e4]

end C3.RV32
