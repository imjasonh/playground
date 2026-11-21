import C3BootProofs.Proofs.DerTlv

/-!
# `Der::element`, as compiled

`Der::element` fails with `Truncated` when the reader has no bytes left and
with `BadDer` when the next tag is not the one it expects, and otherwise
tail-calls `Der::tlv`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem elm_at_0 : fetchRel derElementCode 0x0 = some (.load .lw a3 a1 0xC, 2) := by decide
theorem elm_at_2 : fetchRel derElementCode 0x2 = some (.branch .beq a3 x0 0x14, 2) := by decide
theorem elm_at_4 : fetchRel derElementCode 0x4 = some (.load .lw a3 a1 0x8, 2) := by decide
theorem elm_at_6 : fetchRel derElementCode 0x6 = some (.load .lbu a3 a3 0x0, 4) := by decide
theorem elm_at_a : fetchRel derElementCode 0xA = some (.branch .bne a3 a2 0x10, 4) := by decide
theorem elm_at_e : fetchRel derElementCode 0xE = some (.auipc (6 : Fin 32) 0x0, 4) := by decide
theorem elm_at_12 : fetchRel derElementCode 0x12 = some (.jalr x0 (6 : Fin 32) 0x18, 4) := by decide
theorem elm_at_16 : fetchRel derElementCode 0x16 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem elm_at_18 : fetchRel derElementCode 0x18 = some (.jal x0 0x4, 2) := by decide
theorem elm_at_1a : fetchRel derElementCode 0x1A = some (.aluImm .add a1 x0 0x14, 2) := by decide
theorem elm_at_1c : fetchRel derElementCode 0x1C = some (.store .sw a0 x0 0x0, 4) := by decide
theorem elm_at_20 : fetchRel derElementCode 0x20 = some (.store .sb a0 a1 0x4, 4) := by decide
theorem elm_at_24 : fetchRel derElementCode 0x24 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- The error exit at 0x1C, with `Error`'s discriminant in `a1`. -/
theorem elm_exit {M : Word → BitVec 8} {P out retAddr : Word} {n : Machine} (s : St M P n 0x1C (reg n))
    (hc : CodeIn M P derElementCode) (ha0 : reg n a0 = out) (hra : reg n ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hout : out.toNat % 4 = 0) (sOC : Sep out 17 P derElementCode.length) :
    ∃ n', Steps n n' ∧ n'.pc = retAddr ∧
      n'.mem = memStore8 (memStore32 M out 0) (out + 4) ((reg n a1).extractLsb' 0 8) ∧ ∀ r, reg n' r = reg n r := by
  have hz := s.zero
  obtain ⟨n1, d1, u1⟩ := s.sw hc elm_at_1c (off' := 0x20) (by decide) (by rw [ha0, add_lit_zero]; exact hout)
  rw [ha0, add_lit_zero, hz] at u1
  have hc1 := CodeIn.store32 (v := 0) hc (sOC.sub (c := 0) (l := 4) (by decide) |> fun h => by
    rwa [add_ofNat_zero] at h)
  obtain ⟨n2, d2, u2⟩ := u1.sb hc1 elm_at_20 (off' := 0x24) (by decide)
  rw [ha0] at u2
  have hc2 := CodeIn.store8 (v := (reg n a1).extractLsb' 0 8) hc1 (sOC.sub (c := 4) (l := 1) (by decide))
  obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc2 elm_at_24
  exact ⟨n3, .cons d1 (.cons d2 (.single d3)), by rw [pc3, hra, add_lit_zero, hret], mem3, regs3⟩

set_option maxRecDepth 20000 in
/-- **The compiled `Der::element`**: with the reader at `d` and the expected
tag in `a2`, it stores `derElement` of the unread bytes at `out`, through
`Der::tlv` at `base + 0x26` when the tag matches. -/
theorem derElement_correct (m : Machine) {base out d retAddr : Word} {tag : Nat} (hP : base.toNat % 2 = 0)
    (hc : CodeIn m.mem base derElementCode) (ht : CodeIn m.mem (base + 0x26) derTlvCode) (hpc : m.pc = base)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = d) (ha2 : reg m a2 = BitVec.ofNat 32 tag) (htag : tag < 256)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hout : out.toNat % 4 = 0)
    (hd : d.toNat % 4 = 0) (sOC : Sep out 17 base derElementCode.length)
    (sOT : Sep out 17 (base + 0x26) derTlvCode.length) (sDT : Sep (d + 8) 8 (base + 0x26) derTlvCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧
      m'.mem = derTlvMem m.mem out d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
        (derElement tag (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)) ∧
      ∀ r, tlvClob r = false → reg m' r = reg m r := by
  obtain ⟨rp, hrp⟩ : ∃ rp, memLoad32 m.mem (d + 8) = rp := ⟨_, rfl⟩
  obtain ⟨rl, hrl⟩ : ∃ rl, memLoad32 m.mem (d + 0xC) = rl := ⟨_, rfl⟩
  rw [hrp, hrl]
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.lw hc elm_at_0 (off' := 2) (by decide)
    (by rw [ha1]; exact aligned_add hd (k := 0xC) (by decide))
  rw [ha1, hrl] at u1
  have K1 := tlv_keep (v := rl) (rd := a3) hz (by decide) (fun _ _ => rfl)
  by_cases hl0 : rl = 0
  · obtain ⟨n2, d2, u2⟩ := u1.taken hc 0x16 elm_at_2 (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [hl0]; rfl)
    obtain ⟨n3, d3, u3⟩ := u2.aluImm hc elm_at_16 (off' := 0x18) (by decide)
    obtain ⟨n4, d4, u4⟩ := u3.jump hc elm_at_18 (off' := 0x1C) (by decide) (by
      rw [u3.pc, show base + BitVec.ofNat 32 0x18 + 4 = base + BitVec.ofNat 32 0x1C by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at base hP 0x1C (by decide)))
    obtain ⟨n5, c5, pc5, mem5, k5⟩ := elm_exit u4.self hc
      (by rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]; exact ha0)
      (by rw [u4.regs]; simp +decide only [upd_app, ↓reduceIte]; exact hra) hret hout sOC
    refine ⟨n5, .cons d1 (.cons d2 (.cons d3 (.cons d4 c5))), pc5, ?_, fun r hr => ?_⟩
    · rw [mem5, u4.regs, hl0]; simp +decide only [upd_app, ↓reduceIte]; rfl
    · rw [k5, u4.regs]; exact tlv_keep hz (by decide) K1 r hr
  obtain ⟨n2, d2, u2⟩ := u1.notTaken hc 0x4 elm_at_2 (by decide) (by
    simp only [upd_app]; simp +decide only [↓reduceIte]
    simp only [branchTaken]; exact beq_false_of_ne hl0)
  obtain ⟨n3, d3, u3⟩ := u2.lw hc elm_at_4 (off' := 0x6) (by decide)
    (by simp +decide only [upd_app, ↓reduceIte]; rw [ha1]; exact aligned_add hd (k := 8) (by decide))
  obtain ⟨n4, d4, u4⟩ := u3.lbu hc elm_at_6 (off' := 0xA) (by decide)
  obtain ⟨j, hj⟩ : ∃ j, rl.toNat = j + 1 := ⟨rl.toNat - 1, by
    have : rl.toNat ≠ 0 := fun h => hl0 (BitVec.eq_of_toNat_eq h); omega⟩
  have hL1 : memBytes m.mem rp rl.toNat = (m.mem rp).toNat :: memBytes m.mem (rp + 1) j := by
    rw [hj, memBytes_succ]
  have v4 : upd (upd (upd (reg m) a3 rl) a3 (memLoad32 m.mem (upd (reg m) a3 rl a1 + 8))) a3
      ((m.mem (upd (upd (reg m) a3 rl) a3 (memLoad32 m.mem (upd (reg m) a3 rl a1 + 8)) a3 + 0)).zeroExtend 32) a3 =
      (m.mem rp).zeroExtend 32 := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ha1, hrp, add_lit_zero]
  have K4 : ∀ r, tlvClob r = false → upd (upd (upd (reg m) a3 rl) a3 (memLoad32 m.mem (upd (reg m) a3 rl a1 + 8))) a3
      ((m.mem (upd (upd (reg m) a3 rl) a3 (memLoad32 m.mem (upd (reg m) a3 rl a1 + 8)) a3 + 0)).zeroExtend 32) r =
      reg m r := tlv_keep hz (by decide) (tlv_keep hz (by decide) K1)
  have Kx : ∀ q, q ≠ a3 → upd (upd (upd (reg m) a3 rl) a3 (memLoad32 m.mem (upd (reg m) a3 rl a1 + 8))) a3
      ((m.mem (upd (upd (reg m) a3 rl) a3 (memLoad32 m.mem (upd (reg m) a3 rl a1 + 8)) a3 + 0)).zeroExtend 32) q =
      reg m q := fun q h => by
    rw [updz (upd_zero _ _ _) h, updz (upd_zero _ _ _) h, updz hz h]
  rw [hL1]
  by_cases hm : (m.mem rp).toNat = tag
  · obtain ⟨n5, d5, u5⟩ := u4.notTaken hc 0xE elm_at_a (by decide) (by
      rw [v4, Kx a2 (by decide), ha2]
      show ((m.mem rp).zeroExtend 32 != BitVec.ofNat 32 tag) = false
      have heq : ((m.mem rp).zeroExtend 32 : Word) = BitVec.ofNat 32 tag := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (m.mem rp).isLt; omega), ofNat_tn (by omega), hm]
      rw [heq]; exact bne_self_eq_false _)
    obtain ⟨n6, d6, u6⟩ := u5.auipc hc elm_at_e (off' := 0x12) (by decide)
    obtain ⟨n7, d7, pc7, mem7, regs7⟩ := u6.jalr hc elm_at_12
    have pcT : n7.pc = base + 0x26 := by
      rw [pc7]; simp +decide only [upd_app, ↓reduceIte]
      rw [show base + BitVec.ofNat 32 0xE + 0x0 + 0x18 = base + 0x26 by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
      exact even_clear _ (even_at base hP 0x26 (by decide))
    have r7 : ∀ q, q ≠ 6 → q ≠ a3 → reg n7 q = reg m q := fun q h6 h3 => by
      rw [regs7, upd_ne' h6 (by simp [upd]), Kx q h3]
    obtain ⟨m8, c8, pc8, mem8, k8⟩ := derTlv_correct n7 (even_at base hP 0x26 (by decide)) (by rw [mem7]; exact ht)
      pcT (by rw [r7 a0 (by decide) (by decide), ha0]) (by rw [r7 a1 (by decide) (by decide), ha1])
      (by rw [r7 ra (by decide) (by decide), hra]) hret hout hd sOT sDT
    rw [mem7, hrp, hrl, hL1] at mem8
    refine ⟨m8, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 c8)))))), pc8, ?_,
      fun r hr => ?_⟩
    · rw [mem8]; simp only [derElement, hm, ↓reduceIte]
    · rw [k8 r hr, regs7]
      have h6 : r ≠ 6 := fun e => by rw [e] at hr; exact Bool.noConfusion hr
      rw [upd_ne' h6 (by simp [upd])]; exact K4 r hr
  obtain ⟨n5, d5, u5⟩ := u4.taken hc 0x1A elm_at_a (by decide) (by
    rw [v4, Kx a2 (by decide), ha2]
    show ((m.mem rp).zeroExtend 32 != BitVec.ofNat 32 tag) = true
    simp only [bne_iff_ne, ne_eq]
    intro h; apply hm
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (m.mem rp).isLt; omega), ofNat_tn (by omega)] at this)
  obtain ⟨n6, d6, u6⟩ := u5.self.aluImm hc elm_at_1a (off' := 0x1C) (by decide)
  obtain ⟨n7, c7, pc7, mem7, k7⟩ := elm_exit u6.self hc
    (by rw [u6.regs, upd_ne (by decide) (by decide), u5.regs, Kx a0 (by decide), ha0])
    (by rw [u6.regs, upd_ne (by decide) (by decide), u5.regs, Kx ra (by decide), hra]) hret hout sOC
  refine ⟨n7, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 c7))))), pc7, ?_, fun r hr => ?_⟩
  · rw [mem7, u6.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [u5.self.zero]
    simp only [derElement, hm, ↓reduceIte]; rfl
  · rw [k7, u6.regs]
    exact tlv_keep hz (by decide) (fun r hr => by rw [u5.regs]; exact K4 r hr) r hr

end C3.RV32
