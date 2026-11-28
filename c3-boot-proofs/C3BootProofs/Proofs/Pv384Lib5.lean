import C3BootProofs.Proofs.Pv384Lib4
import C3BootProofs.Proofs.P384Neg

/-!
# `p384_verify_prehash`: the calls of the main loop

The wrapper for the field negation that the main loop of the linear
combination applies to a table entry with a negative digit, and the panic
the loop's bounds checks lead to.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

/-- The functions of the main loop and the steps after it. -/
structure PvCode6 (M : Word → BitVec 8) : Prop where
  neg : CodeIn M (BitVec.ofNat 32 p384NegAddress) p384NegCode

theorem PvCode6.hi {M M' : Word → BitVec 8} (C : PvCode6 M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    PvCode6 M' :=
  ⟨codeHi C.neg (by decide) (by decide) h⟩

/-- Everything the main loop and the steps after it need. -/
structure PvEnv6 (M : Word → BitVec 8) : Prop where
  E : PvEnv5 M
  C6 : PvCode6 M

theorem PvEnv6.fr {B : Word} {M M' : Word → BitVec 8} (E : PvEnv6 M) (F : Fr B 0x21A0)
    (h : ∀ x, PvR B x → M' x = M x) : PvEnv6 M' :=
  ⟨E.E.fr F h, E.C6.hi fun x hx => h x (pvR_of_hi F hx)⟩

/-- The negation of a coordinate, as `p384_neg` computes it. -/
def negY (y : Nat) : Nat := if y = 0 then 0 else (p384 + 2 ^ 384 - y) % 2 ^ 384

theorem negY_lt {y : Nat} (h : y < p384) : negY y < p384 := by
  unfold negY
  by_cases h0 : y = 0
  · rw [ite_eq_left h0]; exact p384_pos
  · rw [ite_eq_right h0]
    have hp : p384 < 2 ^ 384 := by unfold p384; decide
    rw [show p384 + 2 ^ 384 - y = (p384 - y) + 2 ^ 384 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

set_option maxHeartbeats 8000000 in
/-- A call to `p384_neg` on the 12 limbs at offset `cx` of the frame, to `co`. -/
theorem pv_neg {B : Word} {m : Machine} {off : Nat} {imm o : Word} {co cx : Nat} (F : Fr B 0x21A0)
    (E : PvEnv6 m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 p384NegAddress)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 co)
    (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 cx) (hco : co + 48 ≤ 0x1D4C) (hcx : cx + 48 ≤ 0x1D4C)
    (aco : co % 4 = 0) (acx : cx % 4 = 0) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem co 48 ∧
      accV m'.mem (B + 0x420 + BitVec.ofNat 32 co) 12 = negY (accV m.mem (B + 0x420 + BitVec.ofNat 32 cx) 12) := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.E.E.E.E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have lh : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (ngR (B + 0x420)) 0x54 b l := fun b l hb hl => FS.lowHi (by decide) rfl hb hl
  have oh : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (B + 0x420 + BitVec.ofNat 32 co) 48 b l := fun b l hb hl => FS.sepHi (by omega) hb hl
  have EN : NgEnv n1.mem (BitVec.ofNat 32 p384NegAddress) (B + 0x420) (B + 0x420 + BitVec.ofNat 32 co)
      (B + 0x420 + BitVec.ofNat 32 cx) := by
    rw [mem1]
    refine ⟨by decide, E.C6.neg, ?_, ?_, ?_, ?_, ?_, ?_, E.E.E.E.E.D.D.pmod, by omega, by omega,
      pv_al F (by omega) aco, pv_al F (by omega) acx, pv_wr F (by omega),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      lh _ _ (by decide) (by decide), (pv_lowK F (n := 48) (k := 0x54) (by decide) (by decide) (by decide)).symm,
      oh _ _ (by decide) (by decide), oh _ _ (by decide) (by decide),
      FS.lowN (k := 0x54) (by decide) (by decide) (by omega), FS.lowN (k := 0x54) (by decide) (by decide) (by omega)⟩
    · rw [show BitVec.ofNat 32 p384NegAddress + 0x130AC = BitVec.ofNat 32 uint12IsNonzeroAddress by decide]
      exact E.E.E.E.E.C2.unz
    · rw [show BitVec.ofNat 32 p384NegAddress + 0x3F2 = BitVec.ofNat 32 uintRefIsNonzeroAddress by decide]
      exact E.E.E.E.E.C.K.refnz
    · rw [show BitVec.ofNat 32 p384NegAddress + 0x13D7C = MSET by decide]; exact E.E.E.E.E.C.K.mset
    · rw [show ngBsub (BitVec.ofNat 32 p384NegAddress) = BSUB by decide]; exact E.E.E.E.E.C.K.bsub
    · rw [show BitVec.ofNat 32 p384NegAddress + 0x13DE4 = MCS by decide]; exact E.E.E.E.E.C.K.stub
    · rw [show BitVec.ofNat 32 p384NegAddress + 0x13DEC = MCS + 8 by decide]; exact E.E.E.E.E.C.K.body
  obtain ⟨n2, c2, pc2, sp2, k2, val2, fr2⟩ := p384Neg_correct n1 EN pc1 (by rw [r1 sp (by decide)]; exact hsp)
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1] at val2 fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_lo (k := 0x54) hx (by decide) (by decide))
      (pvR_hi hx hco), pv_regs_call r1 (fun q hq => k2 q (by revert hq; revert q; decide)) sp2 hsp⟩,
    fun e he1 he2 => fr2 _ (pv_lowB F (k := 0x54) (by decide) (by decide) (by omega))
      (sepS (B + 0x420) (by omega) (by omega) (by omega)), val2⟩

end C3.RV32.Pv
