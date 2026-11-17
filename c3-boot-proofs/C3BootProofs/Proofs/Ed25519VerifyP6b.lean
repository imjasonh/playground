import C3BootProofs.Proofs.Ed25519VerifyP6

/-!
# `ed25519_verify`, offsets 0x16CC to 0x189C: the double-base multiplication loop

Each pass doubles `r`, adds or subtracts the entries of the two NAF tables
that the two digits select, and converts the sum back to projective form.
-/

namespace C3.RV32

open C3.Image

/-- One digit's step: the completed point `t`, plus the table entry `b / 2`
for a positive digit, minus entry `(256 - b) / 2` for a negative one. -/
def digStep (T : Nat → Pt) (b : BitVec 8) (t : Pt) : Pt :=
  if b.toNat = 0 then t
  else if b.toNat ≤ 15 then addNL (extL t) (T (b.toNat / 2))
  else subNL (extL t) (T ((256 - b.toNat) / 2))

/-- The sign `ed25519_verify` computes from a digit: `0`, `1`, or `0xFF`. -/
def digFlag (b : BitVec 8) : Word := if b = 0 then 0 else if b.toNat < 128 then 1 else 0xFF

theorem digFlag_eq : ∀ b : BitVec 8, aluEval .and (aluEval .sub (aluEval .slt 0 (b.signExtend 32))
    (aluEval .srl (b.signExtend 32) 0x1F)) 0xFF = digFlag b := by decide

theorem digFlag_pos (b : BitVec 8) (h1 : 1 ≤ b.toNat) (h2 : b.toNat ≤ 15) : digFlag b = 1 := by
  unfold digFlag
  rw [ite_eq_right (fun e => by rw [e] at h1; exact absurd h1 (by decide)), ite_eq_left (by omega)]

theorem digFlag_neg (b : BitVec 8) (h : 241 ≤ b.toNat) : digFlag b = 0xFF := by
  unfold digFlag
  rw [ite_eq_right (fun e => by rw [e] at h; exact absurd h (by decide)), ite_eq_right (by omega)]

theorem sext_pos_all : ∀ b : BitVec 8, b.toNat ≤ 15 → (b.signExtend 32).toNat = b.toNat := by decide

theorem sext_pos (b : BitVec 8) (h : b.toNat ≤ 15) : (b.signExtend 32).toNat = b.toNat := sext_pos_all b h

theorem negx_all : ∀ b : BitVec 8, 241 ≤ b.toNat →
    (aluEval .sra (aluEval .sll (aluEval .sub 0 (aluEval .and (b.signExtend 32) 0xFF)) 0x18) 0x18).toNat =
      256 - b.toNat := by decide

theorem negx (b : BitVec 8) (h : 241 ≤ b.toNat) :
    (aluEval .sra (aluEval .sll (aluEval .sub 0 (aluEval .and (b.signExtend 32) 0xFF)) 0x18) 0x18).toNat =
      256 - b.toNat := negx_all b h

section
variable {M0 Ms : Word → BitVec 8} {F pk sig msg : Word} {len : Nat} {r0 : Fin 32 → Word}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- The digit step at offset 0x16E4: the completed point at `F + 0x1468` plus
or minus the table entry at `F + 0x9F0` that the digit at `F + p` selects. -/
theorem ev_digA (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x16E4)
    {b : BitVec 8} {T : Nat → Pt} {p : Nat} (hp : reg n 9 = F + BitVec.ofNat 32 p) (hpb : p < 0x1468)
    (hb : M (F + BitVec.ofNat 32 p) = b) (hbr : b.toNat ≤ 15 ∨ 241 ≤ b.toNat) (h22 : reg n 22 = 1)
    (hT : ∀ j, j < 8 → ptAt M (F + BitVec.ofNat 32 (0x9F0 + 160 * j)) = T j) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x17AE ∧ (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → reg n' q = reg n q) ∧
      ptAt M' (F + BitVec.ofNat 32 0x1468) = digStep T b (ptAt M (F + BitVec.ofNat 32 0x1468)) ∧
      ∀ c, c < 0x16A0 → (c < 0x1468 ∨ 0x1648 ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  have z0 := D.st.zero
  obtain ⟨n1, d1, u1⟩ := D.st.lb (D.code C) ev_at_16e4 (off' := 0x16E8) rfl
  have D1 := D.regs u1.self (fun q hq => by
    rw [u1.regs]; rcases hq with rfl | rfl | rfl <;> simp +decide only [upd, ↓reduceIte])
  have v8 : reg n1 8 = b.signExtend 32 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [hp, add_lit_zero, hb]
  have k1 : ∀ q : Fin 32, q ≠ 8 → reg n1 q = reg n q := fun q hq => by rw [u1.regs]; exact upd_ne' hq z0
  obtain ⟨n2, c2, D2, hr2⟩ := D1.block C (off' := 0x16F6) [.alu .slt a0 x0 (8 : Fin 32), .aluImm .srl a1 (8 : Fin 32) 0x1F, .alu .sub a0 a0 a1, .aluImm .and a0 a0 0xFF]
    (blockEnd_cons' (off' := 0x16EC) ev_at_16e8 rfl (blockEnd_cons' (off' := 0x16F0) ev_at_16ec rfl (blockEnd_cons' (off' := 0x16F2) ev_at_16f0 rfl (blockEnd_cons' (off' := 0x16F6) ev_at_16f2 rfl rfl)))) ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have k2 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → reg n2 q = reg n1 q := fun q h0 h1 => by
    rw [hr2, evb_reg q D1.st.zero (by revert h1 h0; revert q; decide)]
  have vf : reg n2 a0 = digFlag b := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [v8, D1.st.zero]; exact digFlag_eq b
  have kk : ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → reg n2 q = reg n q := fun q hq h8 => by
    rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), k1 q h8]
  rcases (show b.toNat = 0 ∨ (1 ≤ b.toNat ∧ b.toNat ≤ 15) ∨ 241 ≤ b.toNat by omega) with h0 | hpos | hneg
  · -- zero digit
    have hb0 : b = 0 := BitVec.eq_of_toNat_eq h0
    obtain ⟨n3, d3, u3⟩ := D2.st.taken (D2.code C) 0x17AE ev_at_16f6 rfl (by rw [vf, D2.st.zero, hb0]; decide)
    refine ⟨n3, M, (Steps.single d1).trans (c2.trans (Steps.single d3)), D2.jmp u3, fun q hq h8 => ?_, ?_,
      fun _ _ _ => rfl⟩
    · rw [u3.regs, kk q hq h8]
    · unfold digStep; rw [ite_eq_left h0]
  · -- positive digit
    obtain ⟨n3, d3, u3⟩ := D2.st.notTaken (D2.code C) 0x16F8 ev_at_16f6 rfl (by
      rw [vf, D2.st.zero, digFlag_pos b hpos.1 hpos.2]; decide)
    have D3 := D2.jmp u3
    obtain ⟨n4, d4, u4⟩ := D3.st.notTaken (D3.code C) 0x16FC ev_at_16f8 rfl (by
      rw [u3.regs, vf, digFlag_pos b hpos.1 hpos.2, u3.regs, kk 22 (by decide) (by decide), h22]; decide)
    have D4 := D3.jmp u4
    obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x170C) [.lui a0 0x1000, .aluImm .add a0 a0 0x508, .alu .add a0 a0 sp, .lui a1 0x1000, .aluImm .add a1 a1 0x468, .alu .add a1 a1 sp]
      (blockEnd_cons' (off' := 0x16FE) ev_at_16fc rfl (blockEnd_cons' (off' := 0x1702) ev_at_16fe rfl (blockEnd_cons' (off' := 0x1704) ev_at_1702 rfl (blockEnd_cons' (off' := 0x1706) ev_at_1704 rfl (blockEnd_cons' (off' := 0x170A) ev_at_1706 rfl (blockEnd_cons' (off' := 0x170C) ev_at_170a rfl rfl)))))) ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n6, c6, D6, k6, w6, f6⟩ := D5.ax C (d := 0x1508) (e := 0x1468) ev_at_170c ev_at_1710 (by decide)
      (by decide) (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; exact BitVec.add_comm _ _)
      (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; exact BitVec.add_comm _ _) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    obtain ⟨n7, c7, D7, hr7⟩ := D6.block C (off' := 0x1726) [.lui a0 0x1000, .aluImm .add a0 a0 0x5A8, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x1F1, .alu .add a2 x0 (8 : Fin 32)]
      (blockEnd_cons' (off' := 0x1716) ev_at_1714 rfl (blockEnd_cons' (off' := 0x171A) ev_at_1716 rfl (blockEnd_cons' (off' := 0x171C) ev_at_171a rfl (blockEnd_cons' (off' := 0x1720) ev_at_171c rfl (blockEnd_cons' (off' := 0x1724) ev_at_1720 rfl (blockEnd_cons' (off' := 0x1726) ev_at_1724 rfl rfl)))))) ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    have v8' : reg n6 8 = b.signExtend 32 := by
      rw [k6 8 (by decide), hr5, evb_reg 8 D4.st.zero (by decide), u4.regs, u3.regs, k2 8 (by decide) (by decide), v8]
    obtain ⟨n8, c8, D8, k8, f8⟩ := D7.nsel C (d := 0x15A8) (t := 0x9F0) (x := b.signExtend 32) ev_at_1726
      ev_at_172a (by decide) (by decide)
      (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D6.hsp]; exact BitVec.add_comm _ _)
      (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D6.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
      (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [v8']; (try rw [D6.st.zero]); exact BitVec.zero_add _)
      (by rw [sext_pos b hpos.2]; exact hpos.2) (by decide) (by decide) (by decide)
    obtain ⟨n9, c9, D9, hr9⟩ := D8.block C (off' := 0x1746) [.lui a0 0x1000, .aluImm .add a0 a0 0x468, .alu .add a0 a0 sp, .lui a1 0x1000, .aluImm .add a1 a1 0x508, .alu .add a1 a1 sp, .lui a2 0x1000, .aluImm .add a2 a2 0x5A8, .alu .add a2 a2 sp]
      (blockEnd_cons' (off' := 0x1730) ev_at_172e rfl (blockEnd_cons' (off' := 0x1734) ev_at_1730 rfl (blockEnd_cons' (off' := 0x1736) ev_at_1734 rfl (blockEnd_cons' (off' := 0x1738) ev_at_1736 rfl (blockEnd_cons' (off' := 0x173C) ev_at_1738 rfl (blockEnd_cons' (off' := 0x173E) ev_at_173c rfl (blockEnd_cons' (off' := 0x1740) ev_at_173e rfl (blockEnd_cons' (off' := 0x1744) ev_at_1740 rfl (blockEnd_cons' (off' := 0x1746) ev_at_1744 rfl rfl))))))))) ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n10, c10, D10, k10, w10, f10⟩ := D9.ean C (d := 0x1468) (e := 0x1508) (g := 0x15A8) ev_at_1746
      ev_at_174a (by decide) (by decide)
      (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.hsp]; exact BitVec.add_comm _ _)
      (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.hsp]; exact BitVec.add_comm _ _)
      (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.hsp]; exact BitVec.add_comm _ _)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨n11, d11, u11⟩ := D10.st.jump (D10.code C) ev_at_174e (off' := 0x17AE) (by decide)
      (by rw [D10.st.pc]; decide)
    have e7 : ptAt n8.mem (F + BitVec.ofNat 32 0x1508) = extL (ptAt M (F + BitVec.ofNat 32 0x1468)) := by
      rw [← w6]; exact ptB fun j hj => by rw [f8 _ (C.zF (by omega)), copyBytes_sep (C.offs (by omega) (by decide) (by omega))
        (Nat.le_refl _)]
    have s8 : ptAt n8.mem (F + BitVec.ofNat 32 0x15A8) = T (b.toNat / 2) := by
      rw [← hT _ (by omega), show 0x9F0 + 160 * (b.toNat / 2) = 0x9F0 + b.toNat / 2 * 160 by omega]
      refine ptB fun j hj => ?_
      rw [f8 _ (C.zF (by omega)), ← add_ofNat_assoc, cb_in hj (by decide), sext_pos b hpos.2, add_ofNat_assoc,
        add_ofNat_assoc, Nat.add_assoc, f6 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega))]
    refine ⟨n11, n10.mem, (Steps.single d1).trans (c2.trans ((Steps.single d3).trans ((Steps.single d4).trans
      (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans (Steps.single d11)))))))))), D10.jmp u11,
      fun q hq h8 => ?_, ?_, fun c hc hh => ?_⟩
    · rw [u11.regs, k10 q hq, hr9, evb_reg q D8.st.zero (by revert hq; revert q; decide), k8 q hq, hr7,
        evb_reg q D6.st.zero (by revert hq; revert q; decide), k6 q hq, hr5, evb_reg q D4.st.zero (by revert hq; revert q; decide),
        u4.regs, u3.regs, kk q hq h8]
    · rw [w10, e7, s8]; unfold digStep; rw [ite_eq_right (by omega), ite_eq_left hpos.2]
    · rw [f10 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega)), f8 _ (C.zF (by omega)),
        copyBytes_sep (C.offs (by omega) (by decide) (by omega)) (Nat.le_refl _),
        f6 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega))]
  · -- negative digit
    obtain ⟨n3, d3, u3⟩ := D2.st.notTaken (D2.code C) 0x16F8 ev_at_16f6 rfl (by
      rw [vf, D2.st.zero, digFlag_neg b hneg]; decide)
    have D3 := D2.jmp u3
    obtain ⟨n4, d4, u4⟩ := D3.st.taken (D3.code C) 0x1750 ev_at_16f8 rfl (by
      rw [u3.regs, vf, digFlag_neg b hneg, u3.regs, kk 22 (by decide) (by decide), h22]; decide)
    have D4 := D3.jmp u4
    obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x1764) [.aluImm .and (8 : Fin 32) (8 : Fin 32) 0xFF, .lui a0 0x1000, .aluImm .add a0 a0 0x508, .alu .add a0 a0 sp, .lui a1 0x1000, .aluImm .add a1 a1 0x468, .alu .add a1 a1 sp]
      (blockEnd_cons' (off' := 0x1754) ev_at_1750 rfl (blockEnd_cons' (off' := 0x1756) ev_at_1754 rfl (blockEnd_cons' (off' := 0x175A) ev_at_1756 rfl (blockEnd_cons' (off' := 0x175C) ev_at_175a rfl (blockEnd_cons' (off' := 0x175E) ev_at_175c rfl (blockEnd_cons' (off' := 0x1762) ev_at_175e rfl (blockEnd_cons' (off' := 0x1764) ev_at_1762 rfl rfl))))))) ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n6, c6, D6, k6, w6, f6⟩ := D5.ax C (d := 0x1508) (e := 0x1468) ev_at_1764 ev_at_1768 (by decide)
      (by decide) (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; exact BitVec.add_comm _ _)
      (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; exact BitVec.add_comm _ _) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    obtain ⟨n7, c7, D7, hr7⟩ := D6.block C (off' := 0x1786) [.alu .sub a0 x0 (8 : Fin 32), .aluImm .sll a0 a0 0x18, .aluImm .sra a2 a0 0x18, .lui a0 0x1000, .aluImm .add a0 a0 0x5A8, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x1F1]
      (blockEnd_cons' (off' := 0x1770) ev_at_176c rfl (blockEnd_cons' (off' := 0x1772) ev_at_1770 rfl (blockEnd_cons' (off' := 0x1776) ev_at_1772 rfl (blockEnd_cons' (off' := 0x1778) ev_at_1776 rfl (blockEnd_cons' (off' := 0x177C) ev_at_1778 rfl (blockEnd_cons' (off' := 0x177E) ev_at_177c rfl (blockEnd_cons' (off' := 0x1782) ev_at_177e rfl (blockEnd_cons' (off' := 0x1786) ev_at_1782 rfl rfl)))))))) ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    have v8' : reg n6 8 = aluEval .and (b.signExtend 32) 0xFF := by
      rw [k6 8 (by decide), hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [u4.regs, u3.regs, k2 8 (by decide) (by decide), v8]
    obtain ⟨n8, c8, D8, k8, f8⟩ := D7.nsel C (d := 0x15A8) (t := 0x9F0)
      (x := aluEval .sra (aluEval .sll (aluEval .sub 0 (aluEval .and (b.signExtend 32) 0xFF)) 0x18) 0x18)
      ev_at_1786 ev_at_178a (by decide) (by decide)
      (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D6.hsp]; exact BitVec.add_comm _ _)
      (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D6.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
      (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [v8', D6.st.zero])
      (by rw [negx b hneg]; omega) (by decide) (by decide) (by decide)
    obtain ⟨n9, c9, D9, hr9⟩ := D8.block C (off' := 0x17A6) [.lui a0 0x1000, .aluImm .add a0 a0 0x468, .alu .add a0 a0 sp, .lui a1 0x1000, .aluImm .add a1 a1 0x508, .alu .add a1 a1 sp, .lui a2 0x1000, .aluImm .add a2 a2 0x5A8, .alu .add a2 a2 sp]
      (blockEnd_cons' (off' := 0x1790) ev_at_178e rfl (blockEnd_cons' (off' := 0x1794) ev_at_1790 rfl (blockEnd_cons' (off' := 0x1796) ev_at_1794 rfl (blockEnd_cons' (off' := 0x1798) ev_at_1796 rfl (blockEnd_cons' (off' := 0x179C) ev_at_1798 rfl (blockEnd_cons' (off' := 0x179E) ev_at_179c rfl (blockEnd_cons' (off' := 0x17A0) ev_at_179e rfl (blockEnd_cons' (off' := 0x17A4) ev_at_17a0 rfl (blockEnd_cons' (off' := 0x17A6) ev_at_17a4 rfl rfl))))))))) ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n10, c10, D10, k10, w10, f10⟩ := D9.esn C (d := 0x1468) (e := 0x1508) (g := 0x15A8) ev_at_17a6
      ev_at_17aa (by decide) (by decide)
      (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.hsp]; exact BitVec.add_comm _ _)
      (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.hsp]; exact BitVec.add_comm _ _)
      (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.hsp]; exact BitVec.add_comm _ _)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have e7 : ptAt n8.mem (F + BitVec.ofNat 32 0x1508) = extL (ptAt M (F + BitVec.ofNat 32 0x1468)) := by
      rw [← w6]; exact ptB fun j hj => by rw [f8 _ (C.zF (by omega)), copyBytes_sep (C.offs (by omega) (by decide) (by omega))
        (Nat.le_refl _)]
    have s8 : ptAt n8.mem (F + BitVec.ofNat 32 0x15A8) = T ((256 - b.toNat) / 2) := by
      rw [← hT _ (by omega), show 0x9F0 + 160 * ((256 - b.toNat) / 2) = 0x9F0 + (256 - b.toNat) / 2 * 160 by omega]
      refine ptB fun j hj => ?_
      rw [f8 _ (C.zF (by omega)), ← add_ofNat_assoc, cb_in hj (by decide), negx b hneg, add_ofNat_assoc,
        add_ofNat_assoc, Nat.add_assoc, f6 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega))]
    refine ⟨n10, n10.mem, (Steps.single d1).trans (c2.trans ((Steps.single d3).trans ((Steps.single d4).trans
      (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans c10)))))))), D10, fun q hq h8 => ?_, ?_, fun c hc hh => ?_⟩
    · rw [k10 q hq, hr9, evb_reg q D8.st.zero (by revert hq; revert q; decide), k8 q hq, hr7,
        evb_reg q D6.st.zero (by revert hq; revert q; decide), k6 q hq, hr5,
        evb_reg q D4.st.zero (by revert h8; revert hq; revert q; decide), u4.regs, u3.regs, kk q hq h8]
    · rw [w10, e7, s8]; unfold digStep; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [f10 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega)), f8 _ (C.zF (by omega)),
        copyBytes_sep (C.offs (by omega) (by decide) (by omega)) (Nat.le_refl _),
        f6 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega))]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- The digit step at offset 0x17AE: the completed point at `F + 0x1468` plus
or minus the table entry at `F + 0xEF0` that the digit at `F + p` selects. -/
theorem ev_digB (C : EvCtx M0 F pk sig msg len) {M : Word → BitVec 8} {n : Machine} (D : EvSt M0 Ms F r0 M n 0x17AE)
    {b : BitVec 8} {T : Nat → Pt} {p : Nat} (hp : reg n 21 = F + BitVec.ofNat 32 p) (hpb : p < 0x1468)
    (hb : M (F + BitVec.ofNat 32 p) = b) (hbr : b.toNat ≤ 15 ∨ 241 ≤ b.toNat) (h22 : reg n 22 = 1)
    (hT : ∀ j, j < 8 → ptAt M (F + BitVec.ofNat 32 (0xEF0 + 160 * j)) = T j) :
    ∃ n' M', Steps n n' ∧ EvSt M0 Ms F r0 M' n' 0x1878 ∧ (∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → reg n' q = reg n q) ∧
      ptAt M' (F + BitVec.ofNat 32 0x1468) = digStep T b (ptAt M (F + BitVec.ofNat 32 0x1468)) ∧
      ∀ c, c < 0x16A0 → (c < 0x1468 ∨ 0x1648 ≤ c) → M' (F + BitVec.ofNat 32 c) = M (F + BitVec.ofNat 32 c) := by
  have z0 := D.st.zero
  obtain ⟨n1, d1, u1⟩ := D.st.lb (D.code C) ev_at_17ae (off' := 0x17B2) rfl
  have D1 := D.regs u1.self (fun q hq => by
    rw [u1.regs]; rcases hq with rfl | rfl | rfl <;> simp +decide only [upd, ↓reduceIte])
  have v8 : reg n1 8 = b.signExtend 32 := by
    rw [u1.regs]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [hp, add_lit_zero, hb]
  have k1 : ∀ q : Fin 32, q ≠ 8 → reg n1 q = reg n q := fun q hq => by rw [u1.regs]; exact upd_ne' hq z0
  obtain ⟨n2, c2, D2, hr2⟩ := D1.block C (off' := 0x17C0) [.alu .slt a0 x0 (8 : Fin 32), .aluImm .srl a1 (8 : Fin 32) 0x1F, .alu .sub a0 a0 a1, .aluImm .and a0 a0 0xFF]
    (blockEnd_cons' (off' := 0x17B6) ev_at_17b2 rfl (blockEnd_cons' (off' := 0x17BA) ev_at_17b6 rfl (blockEnd_cons' (off' := 0x17BC) ev_at_17ba rfl (blockEnd_cons' (off' := 0x17C0) ev_at_17bc rfl rfl)))) ⟨trivial, trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
  have k2 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → reg n2 q = reg n1 q := fun q h0 h1 => by
    rw [hr2, evb_reg q D1.st.zero (by revert h1 h0; revert q; decide)]
  have vf : reg n2 a0 = digFlag b := by
    rw [hr2]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [v8, D1.st.zero]; exact digFlag_eq b
  have kk : ∀ q : Fin 32, q.val ∈ evKeep → q ≠ 8 → reg n2 q = reg n q := fun q hq h8 => by
    rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide), k1 q h8]
  rcases (show b.toNat = 0 ∨ (1 ≤ b.toNat ∧ b.toNat ≤ 15) ∨ 241 ≤ b.toNat by omega) with h0 | hpos | hneg
  · -- zero digit
    have hb0 : b = 0 := BitVec.eq_of_toNat_eq h0
    obtain ⟨n3, d3, u3⟩ := D2.st.taken (D2.code C) 0x1878 ev_at_17c0 rfl (by rw [vf, D2.st.zero, hb0]; decide)
    refine ⟨n3, M, (Steps.single d1).trans (c2.trans (Steps.single d3)), D2.jmp u3, fun q hq h8 => ?_, ?_,
      fun _ _ _ => rfl⟩
    · rw [u3.regs, kk q hq h8]
    · unfold digStep; rw [ite_eq_left h0]
  · -- positive digit
    obtain ⟨n3, d3, u3⟩ := D2.st.notTaken (D2.code C) 0x17C2 ev_at_17c0 rfl (by
      rw [vf, D2.st.zero, digFlag_pos b hpos.1 hpos.2]; decide)
    have D3 := D2.jmp u3
    obtain ⟨n4, d4, u4⟩ := D3.st.notTaken (D3.code C) 0x17C6 ev_at_17c2 rfl (by
      rw [u3.regs, vf, digFlag_pos b hpos.1 hpos.2, u3.regs, kk 22 (by decide) (by decide), h22]; decide)
    have D4 := D3.jmp u4
    obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x17D6) [.lui a0 0x1000, .aluImm .add a0 a0 0x508, .alu .add a0 a0 sp, .lui a1 0x1000, .aluImm .add a1 a1 0x468, .alu .add a1 a1 sp]
      (blockEnd_cons' (off' := 0x17C8) ev_at_17c6 rfl (blockEnd_cons' (off' := 0x17CC) ev_at_17c8 rfl (blockEnd_cons' (off' := 0x17CE) ev_at_17cc rfl (blockEnd_cons' (off' := 0x17D0) ev_at_17ce rfl (blockEnd_cons' (off' := 0x17D4) ev_at_17d0 rfl (blockEnd_cons' (off' := 0x17D6) ev_at_17d4 rfl rfl)))))) ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n6, c6, D6, k6, w6, f6⟩ := D5.ax C (d := 0x1508) (e := 0x1468) ev_at_17d6 ev_at_17da (by decide)
      (by decide) (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; exact BitVec.add_comm _ _)
      (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; exact BitVec.add_comm _ _) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    obtain ⟨n7, c7, D7, hr7⟩ := D6.block C (off' := 0x17F0) [.lui a0 0x1000, .aluImm .add a0 a0 0x5A8, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x6F1, .alu .add a2 x0 (8 : Fin 32)]
      (blockEnd_cons' (off' := 0x17E0) ev_at_17de rfl (blockEnd_cons' (off' := 0x17E4) ev_at_17e0 rfl (blockEnd_cons' (off' := 0x17E6) ev_at_17e4 rfl (blockEnd_cons' (off' := 0x17EA) ev_at_17e6 rfl (blockEnd_cons' (off' := 0x17EE) ev_at_17ea rfl (blockEnd_cons' (off' := 0x17F0) ev_at_17ee rfl rfl)))))) ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    have v8' : reg n6 8 = b.signExtend 32 := by
      rw [k6 8 (by decide), hr5, evb_reg 8 D4.st.zero (by decide), u4.regs, u3.regs, k2 8 (by decide) (by decide), v8]
    obtain ⟨n8, c8, D8, k8, f8⟩ := D7.nsel C (d := 0x15A8) (t := 0xEF0) (x := b.signExtend 32) ev_at_17f0
      ev_at_17f4 (by decide) (by decide)
      (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D6.hsp]; exact BitVec.add_comm _ _)
      (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D6.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
      (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [v8']; (try rw [D6.st.zero]); exact BitVec.zero_add _)
      (by rw [sext_pos b hpos.2]; exact hpos.2) (by decide) (by decide) (by decide)
    obtain ⟨n9, c9, D9, hr9⟩ := D8.block C (off' := 0x1810) [.lui a0 0x1000, .aluImm .add a0 a0 0x468, .alu .add a0 a0 sp, .lui a1 0x1000, .aluImm .add a1 a1 0x508, .alu .add a1 a1 sp, .lui a2 0x1000, .aluImm .add a2 a2 0x5A8, .alu .add a2 a2 sp]
      (blockEnd_cons' (off' := 0x17FA) ev_at_17f8 rfl (blockEnd_cons' (off' := 0x17FE) ev_at_17fa rfl (blockEnd_cons' (off' := 0x1800) ev_at_17fe rfl (blockEnd_cons' (off' := 0x1802) ev_at_1800 rfl (blockEnd_cons' (off' := 0x1806) ev_at_1802 rfl (blockEnd_cons' (off' := 0x1808) ev_at_1806 rfl (blockEnd_cons' (off' := 0x180A) ev_at_1808 rfl (blockEnd_cons' (off' := 0x180E) ev_at_180a rfl (blockEnd_cons' (off' := 0x1810) ev_at_180e rfl rfl))))))))) ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n10, c10, D10, k10, w10, f10⟩ := D9.ean C (d := 0x1468) (e := 0x1508) (g := 0x15A8) ev_at_1810
      ev_at_1814 (by decide) (by decide)
      (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.hsp]; exact BitVec.add_comm _ _)
      (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.hsp]; exact BitVec.add_comm _ _)
      (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.hsp]; exact BitVec.add_comm _ _)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨n11, d11, u11⟩ := D10.st.jump (D10.code C) ev_at_1818 (off' := 0x1878) (by decide)
      (by rw [D10.st.pc]; decide)
    have e7 : ptAt n8.mem (F + BitVec.ofNat 32 0x1508) = extL (ptAt M (F + BitVec.ofNat 32 0x1468)) := by
      rw [← w6]; exact ptB fun j hj => by rw [f8 _ (C.zF (by omega)), copyBytes_sep (C.offs (by omega) (by decide) (by omega))
        (Nat.le_refl _)]
    have s8 : ptAt n8.mem (F + BitVec.ofNat 32 0x15A8) = T (b.toNat / 2) := by
      rw [← hT _ (by omega), show 0xEF0 + 160 * (b.toNat / 2) = 0xEF0 + b.toNat / 2 * 160 by omega]
      refine ptB fun j hj => ?_
      rw [f8 _ (C.zF (by omega)), ← add_ofNat_assoc, cb_in hj (by decide), sext_pos b hpos.2, add_ofNat_assoc,
        add_ofNat_assoc, Nat.add_assoc, f6 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega))]
    refine ⟨n11, n10.mem, (Steps.single d1).trans (c2.trans ((Steps.single d3).trans ((Steps.single d4).trans
      (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans (Steps.single d11)))))))))), D10.jmp u11,
      fun q hq h8 => ?_, ?_, fun c hc hh => ?_⟩
    · rw [u11.regs, k10 q hq, hr9, evb_reg q D8.st.zero (by revert hq; revert q; decide), k8 q hq, hr7,
        evb_reg q D6.st.zero (by revert hq; revert q; decide), k6 q hq, hr5, evb_reg q D4.st.zero (by revert hq; revert q; decide),
        u4.regs, u3.regs, kk q hq h8]
    · rw [w10, e7, s8]; unfold digStep; rw [ite_eq_right (by omega), ite_eq_left hpos.2]
    · rw [f10 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega)), f8 _ (C.zF (by omega)),
        copyBytes_sep (C.offs (by omega) (by decide) (by omega)) (Nat.le_refl _),
        f6 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega))]
  · -- negative digit
    obtain ⟨n3, d3, u3⟩ := D2.st.notTaken (D2.code C) 0x17C2 ev_at_17c0 rfl (by
      rw [vf, D2.st.zero, digFlag_neg b hneg]; decide)
    have D3 := D2.jmp u3
    obtain ⟨n4, d4, u4⟩ := D3.st.taken (D3.code C) 0x181A ev_at_17c2 rfl (by
      rw [u3.regs, vf, digFlag_neg b hneg, u3.regs, kk 22 (by decide) (by decide), h22]; decide)
    have D4 := D3.jmp u4
    obtain ⟨n5, c5, D5, hr5⟩ := D4.block C (off' := 0x182E) [.aluImm .and (8 : Fin 32) (8 : Fin 32) 0xFF, .lui a0 0x1000, .aluImm .add a0 a0 0x508, .alu .add a0 a0 sp, .lui a1 0x1000, .aluImm .add a1 a1 0x468, .alu .add a1 a1 sp]
      (blockEnd_cons' (off' := 0x181E) ev_at_181a rfl (blockEnd_cons' (off' := 0x1820) ev_at_181e rfl (blockEnd_cons' (off' := 0x1824) ev_at_1820 rfl (blockEnd_cons' (off' := 0x1826) ev_at_1824 rfl (blockEnd_cons' (off' := 0x1828) ev_at_1826 rfl (blockEnd_cons' (off' := 0x182C) ev_at_1828 rfl (blockEnd_cons' (off' := 0x182E) ev_at_182c rfl rfl))))))) ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n6, c6, D6, k6, w6, f6⟩ := D5.ax C (d := 0x1508) (e := 0x1468) ev_at_182e ev_at_1832 (by decide)
      (by decide) (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; exact BitVec.add_comm _ _)
      (by rw [hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D4.hsp]; exact BitVec.add_comm _ _) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    obtain ⟨n7, c7, D7, hr7⟩ := D6.block C (off' := 0x1850) [.alu .sub a0 x0 (8 : Fin 32), .aluImm .sll a0 a0 0x18, .aluImm .sra a2 a0 0x18, .lui a0 0x1000, .aluImm .add a0 a0 0x5A8, .alu .add a0 a0 sp, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x6F1]
      (blockEnd_cons' (off' := 0x183A) ev_at_1836 rfl (blockEnd_cons' (off' := 0x183C) ev_at_183a rfl (blockEnd_cons' (off' := 0x1840) ev_at_183c rfl (blockEnd_cons' (off' := 0x1842) ev_at_1840 rfl (blockEnd_cons' (off' := 0x1846) ev_at_1842 rfl (blockEnd_cons' (off' := 0x1848) ev_at_1846 rfl (blockEnd_cons' (off' := 0x184C) ev_at_1848 rfl (blockEnd_cons' (off' := 0x1850) ev_at_184c rfl rfl)))))))) ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    have v8' : reg n6 8 = aluEval .and (b.signExtend 32) 0xFF := by
      rw [k6 8 (by decide), hr5]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [u4.regs, u3.regs, k2 8 (by decide) (by decide), v8]
    obtain ⟨n8, c8, D8, k8, f8⟩ := D7.nsel C (d := 0x15A8) (t := 0xEF0)
      (x := aluEval .sra (aluEval .sll (aluEval .sub 0 (aluEval .and (b.signExtend 32) 0xFF)) 0x18) 0x18)
      ev_at_1850 ev_at_1854 (by decide) (by decide)
      (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D6.hsp]; exact BitVec.add_comm _ _)
      (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D6.hsp, show aluEval .add F 0x7FF = F + BitVec.ofNat 32 0x7FF from rfl]; exact add_sp F rfl)
      (by rw [hr7]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [v8', D6.st.zero])
      (by rw [negx b hneg]; omega) (by decide) (by decide) (by decide)
    obtain ⟨n9, c9, D9, hr9⟩ := D8.block C (off' := 0x1870) [.lui a0 0x1000, .aluImm .add a0 a0 0x468, .alu .add a0 a0 sp, .lui a1 0x1000, .aluImm .add a1 a1 0x508, .alu .add a1 a1 sp, .lui a2 0x1000, .aluImm .add a2 a2 0x5A8, .alu .add a2 a2 sp]
      (blockEnd_cons' (off' := 0x185A) ev_at_1858 rfl (blockEnd_cons' (off' := 0x185E) ev_at_185a rfl (blockEnd_cons' (off' := 0x1860) ev_at_185e rfl (blockEnd_cons' (off' := 0x1862) ev_at_1860 rfl (blockEnd_cons' (off' := 0x1866) ev_at_1862 rfl (blockEnd_cons' (off' := 0x1868) ev_at_1866 rfl (blockEnd_cons' (off' := 0x186A) ev_at_1868 rfl (blockEnd_cons' (off' := 0x186E) ev_at_186a rfl (blockEnd_cons' (off' := 0x1870) ev_at_186e rfl rfl))))))))) ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩ rfl (fun q hq => by rcases hq with rfl | rfl | rfl <;> simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte])
    obtain ⟨n10, c10, D10, k10, w10, f10⟩ := D9.esn C (d := 0x1468) (e := 0x1508) (g := 0x15A8) ev_at_1870
      ev_at_1874 (by decide) (by decide)
      (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.hsp]; exact BitVec.add_comm _ _)
      (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.hsp]; exact BitVec.add_comm _ _)
      (by rw [hr9]; simp +decide only [runBlock, BInstr.run, upd, ↓reduceIte]; rw [D8.hsp]; exact BitVec.add_comm _ _)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have e7 : ptAt n8.mem (F + BitVec.ofNat 32 0x1508) = extL (ptAt M (F + BitVec.ofNat 32 0x1468)) := by
      rw [← w6]; exact ptB fun j hj => by rw [f8 _ (C.zF (by omega)), copyBytes_sep (C.offs (by omega) (by decide) (by omega))
        (Nat.le_refl _)]
    have s8 : ptAt n8.mem (F + BitVec.ofNat 32 0x15A8) = T ((256 - b.toNat) / 2) := by
      rw [← hT _ (by omega), show 0xEF0 + 160 * ((256 - b.toNat) / 2) = 0xEF0 + (256 - b.toNat) / 2 * 160 by omega]
      refine ptB fun j hj => ?_
      rw [f8 _ (C.zF (by omega)), ← add_ofNat_assoc, cb_in hj (by decide), negx b hneg, add_ofNat_assoc,
        add_ofNat_assoc, Nat.add_assoc, f6 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega))]
    refine ⟨n10, n10.mem, (Steps.single d1).trans (c2.trans ((Steps.single d3).trans ((Steps.single d4).trans
      (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans c10)))))))), D10, fun q hq h8 => ?_, ?_, fun c hc hh => ?_⟩
    · rw [k10 q hq, hr9, evb_reg q D8.st.zero (by revert hq; revert q; decide), k8 q hq, hr7,
        evb_reg q D6.st.zero (by revert hq; revert q; decide), k6 q hq, hr5,
        evb_reg q D4.st.zero (by revert h8; revert hq; revert q; decide), u4.regs, u3.regs, kk q hq h8]
    · rw [w10, e7, s8]; unfold digStep; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [f10 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega)), f8 _ (C.zF (by omega)),
        copyBytes_sep (C.offs (by omega) (by decide) (by omega)) (Nat.le_refl _),
        f6 _ (C.zF (by omega)) (C.offs (by omega) (by decide) (by omega))]

end

end C3.RV32

