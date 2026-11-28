import C3BootProofs.Proofs.P2vIvLib
import C3BootProofs.Proofs.Pv384HDs4

/-!
# `p256_verify_prehash`: the constant-time divsteps

The inversion of the sum's `Z` runs its divsteps in constant time, as
`p384_verify_prehash` does: each step computes both outcomes and picks one
with `select_i64`. This file holds that loop's blocks, at 0xC3C, and the
frame facts its proof uses; the arithmetic lemmas are `Pv384HDs`'s.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

set_option maxHeartbeats 4000000 in
/-- A call to `select_i64`, with the choice 0 or 1 in `a0`. -/
theorem p2v_si {B : Word} {m : Machine} {off : Nat} {imm o : Word} (F : Fr B 0x3590)
    (C : P2vCode m.mem) (IC : P2vIvCode m.mem) (s : St m.mem P2V m off (reg m))
    (h1 : fetchRel p256VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p256VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : P2V + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 selectI64Address)
    (he8 : (P2V + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0) (hsp : reg m sp = B + 0x21A0)
    (hc : reg m a0 = 0 ∨ reg m a0 = 1) :
    ∃ m', P2vPost B m m' (off + 8) ∧ P2vKeep B m.mem m'.mem 0 0 ∧
      (∀ q : Fin 32, q ≠ ra → q ≠ a0 → q ≠ a1 → q ≠ a3 → q ≠ a4 → q ≠ a5 → reg m' q = reg m q) ∧
      reg m' a0 = (if reg m a0 = 1 then reg m a3 else reg m a1) ∧
      reg m' a1 = (if reg m a0 = 1 then reg m a4 else reg m a2) := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = B + 0x21A0 := by rw [r1 sp (by decide)]; exact hsp
  obtain ⟨n2, c2, pc2, sp2, k2, v0, v1, fr2⟩ := selectI64_correct n1 (by rw [mem1]; exact IC.sel64) pc1
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
    (by rw [sp1, p2v_sp1]; exact F.sepHi (by decide) (by decide) (by decide))
  have a0e : reg n1 a0 = reg m a0 := r1 a0 (by decide)
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩,
    fun x hx => by rw [fr2 x (by rw [sp1, p2v_sp1]; exact sep1_ne (p2vR_sp1 hx)), mem1],
    fun q hq => ?_⟩, fun e he1 _ => ?_, fun q hr h0 h1' h3 h4 h5 => by
      rw [k2 q h0 h1' h3 h4 h5, r1 q hr], ?_, ?_⟩
  · by_cases h : q = sp
    · subst h; rw [sp2, sp1, hsp]
    · rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)]
  · rw [fr2 _ (by
      rw [sp1, p2v_sp1, ← p2v_base']
      exact sep1_ne (sepS B (by omega) (by omega) (by omega))), mem1]
  · rcases hc with h | h
    · rw [ite_eq_right (by rw [h]; decide), (v0 (by rw [a0e, h]; rfl)).1, r1 a1 (by decide)]
    · rw [ite_eq_left h, (v1 (by rw [a0e, h]; rfl)).1, r1 a3 (by decide)]
  · rcases hc with h | h
    · rw [ite_eq_right (by rw [h]; decide), (v0 (by rw [a0e, h]; rfl)).2, r1 a2 (by decide)]
    · rw [ite_eq_left h, (v1 (by rw [a0e, h]; rfl)).2, r1 a4 (by decide)]

theorem p2vR_st32 {B x c v : Word} {M : Word → BitVec 8} (hx : P2vR B x) (hc : c.toNat + 4 ≤ 0x13F0) :
    memStore32 M (B + 0x21A0 + c) v x = M x := by
  have := p2vR_hi (c := c.toNat) (l := 4) hx hc
  rw [ofNat_toNat_self] at this
  exact memStore32_get_sep this

theorem p2vR_st8 {B x c : Word} {v : BitVec 8} {M : Word → BitVec 8} (hx : P2vR B x) (hc : c.toNat + 1 ≤ 0x13F0) :
    memStore8 M (B + 0x21A0 + c) v x = M x := by
  have := p2vR_hi (c := c.toNat) (l := 1) hx hc
  rw [ofNat_toNat_self] at this
  exact memStore8_ne (sep1_ne this)

theorem fk2_st32 {B c v : Word} {M : Word → BitVec 8} {e : Nat} (hS : (B + 0x21A0).toNat + 0x1D80 ≤ 2 ^ 32)
    (hc : c.toNat + 4 ≤ 0x1D80) (he : e + 1 ≤ 0x1D80) (h : c.toNat + 4 ≤ e ∨ e + 1 ≤ c.toNat) :
    memStore32 M (B + 0x21A0 + c) v (B + 0x21A0 + BitVec.ofNat 32 e) = M (B + 0x21A0 + BitVec.ofNat 32 e) :=
  memStore32_get_sep (fr_sep hS (by decide) (by decide) hc (by rw [BitVec.toNat_ofNat]; omega)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact h))

theorem fk2_st8 {B c : Word} {v : BitVec 8} {M : Word → BitVec 8} {e : Nat} (hS : (B + 0x21A0).toNat + 0x1D80 ≤ 2 ^ 32)
    (hc : c.toNat + 1 ≤ 0x1D80) (he : e + 1 ≤ 0x1D80) (h : c.toNat + 1 ≤ e ∨ e + 1 ≤ c.toNat) :
    memStore8 M (B + 0x21A0 + c) v (B + 0x21A0 + BitVec.ofNat 32 e) = M (B + 0x21A0 + BitVec.ofNat 32 e) :=
  memStore8_ne (sep1_ne (fr_sep hS (by decide) (by decide) hc (by rw [BitVec.toNat_ofNat]; omega)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact h)))

theorem add_920 (S : Word) : S + 0x920 + 0x360 = S + 0xC80 := by rw [BitVec.add_assoc]; rfl

theorem add_7ff121 (S : Word) : S + 0x7FF + 0x121 = S + 0x920 := by rw [BitVec.add_assoc]; rfl

theorem add_7ff481 (S : Word) : S + 0x7FF + 0x481 = S + 0xC80 := by rw [BitVec.add_assoc]; rfl

theorem fr2_al {B c : Word} (FS : Fr (B + 0x21A0) 0x13F0) (hc : c.toNat % 4 = 0) (hc' : c.toNat < 0x13F0) :
    (B + 0x21A0 + c).toNat % 4 = 0 := by
  have := FS.al; have := FS.hi; rw [BitVec.toNat_add]; omega

theorem fr2_code {B c : Word} (FS : Fr (B + 0x21A0) 0x13F0) {n : Nat} (hc : c.toNat + n ≤ 0x13F0) :
    Sep (B + 0x21A0 + c) n P2V p256VerifyPrehashCode.length := by
  have := FS.hi
  have e : (B + 0x21A0 + c).toNat = (B + 0x21A0).toNat + c.toNat := by rw [BitVec.toNat_add]; omega
  exact sep_of_le (by rw [e, show P2V.toNat = p256VerifyPrehashAddress from rfl]; unfold p256VerifyPrehashAddress; omega)
    (by rw [show P2V.toNat = p256VerifyPrehashAddress from rfl]; decide)

/-- The block side conditions: aligned stores to the frame, apart from the code. -/
macro "ct2_ok" : tactic => `(tactic| (
  repeat' apply And.intro
  all_goals first
    | exact fr2_al (by assumption) (by decide) (by decide)
    | exact fr2_code (by assumption) (by decide)))

theorem kld2 {B c : Word} {M M' : Word → BitVec 8} (K : P2vKeep B M M' 0 0) (hc : c.toNat + 4 ≤ 0x13F0) :
    memLoad32 M' (B + 0x21A0 + c) = memLoad32 M (B + 0x21A0 + c) := by
  rw [← ofNat_toNat_self c]
  exact memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact K _ (by omega) (by omega)

theorem kfk2 {B : Word} {M M' : Word → BitVec 8} (K : P2vKeep B M M' 0 0) {e : Nat} (he : e + 1 ≤ 0x13F0) :
    M' (B + 0x21A0 + BitVec.ofNat 32 e) = M (B + 0x21A0 + BitVec.ofNat 32 e) := K e he (by omega)

def ctT1 : List BInstr :=
  [.lw (21 : Fin 32) sp 0x44, .aluImm .and (27 : Fin 32) (21 : Fin 32) 0x1, .alu .add (19 : Fin 32) x0 (20 : Fin 32),
   .lui a5 0x80000000, .alu .xor a0 (24 : Fin 32) a5, .sb (8 : Fin 32) (27 : Fin 32) 0x360, .lw (9 : Fin 32) sp 0x40,
   .sw sp (25 : Fin 32) 0x30, .alu .sltu a2 x0 (9 : Fin 32), .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x481,
   .aluImm .add a1 (9 : Fin 32) 0x2, .sw sp a3 0x28, .sw sp a4 0x3C, .lbu a4 (8 : Fin 32) 0x360,
   .aluImm .add a6 x0 0x2, .alu .sub a3 a6 (9 : Fin 32), .alu .sub a5 a5 a0, .alu .sub a5 a5 a2,
   .alu .sltu a2 a1 (9 : Fin 32), .alu .add a2 a2 (24 : Fin 32), .alu .and a0 a0 a5, .aluImm .srl a5 a0 0x1F,
   .sw sp a5 0x24, .aluImm .sltu a0 a4 0x1, .alu .sub a4 x0 a4, .aluImm .add a0 a0 0xFFFFFFFF,
   .sw sp (18 : Fin 32) 0x1C, .alu .add (18 : Fin 32) x0 (22 : Fin 32), .lw (22 : Fin 32) sp 0x48,
   .lw (20 : Fin 32) sp 0x50, .alu .and (8 : Fin 32) (20 : Fin 32) a4, .alu .sltu a4 a6 (9 : Fin 32),
   .alu .and (25 : Fin 32) (22 : Fin 32) a0, .alu .sub a0 x0 (24 : Fin 32), .alu .sub a4 a0 a4,
   .alu .and (24 : Fin 32) (27 : Fin 32) a5, .alu .add a0 x0 (24 : Fin 32)]
set_option maxHeartbeats 4000000 in
theorem ctT1_end : blockEnd p256VerifyPrehashCode 0xC3C ctT1 = some 0xCB0 := by decide
def ctT2 : List BInstr :=
  [.sw sp a0 0x40, .sw sp a1 0x38, .alu .add a0 x0 (24 : Fin 32), .alu .add a1 x0 (20 : Fin 32),
   .alu .add a2 x0 (22 : Fin 32), .alu .add (22 : Fin 32) x0 (18 : Fin 32), .alu .add a3 x0 (21 : Fin 32),
   .lw (9 : Fin 32) sp 0x4C, .alu .add a4 x0 (9 : Fin 32)]
set_option maxHeartbeats 4000000 in
theorem ctT2_end : blockEnd p256VerifyPrehashCode 0xCB8 ctT2 = some 0xCCA := by decide
def ctT3 : List BInstr :=
  [.sw sp a0 0x50, .sw sp a1 0x48, .alu .add a1 (8 : Fin 32) (21 : Fin 32), .alu .sltu a2 a1 (8 : Fin 32),
   .alu .add a0 (25 : Fin 32) (9 : Fin 32), .alu .add a2 a2 a0, .alu .sltu a0 (21 : Fin 32) (8 : Fin 32),
   .alu .sub a4 (9 : Fin 32) (25 : Fin 32), .alu .sub a4 a4 a0, .alu .sub a3 (21 : Fin 32) (8 : Fin 32),
   .alu .add a0 x0 (24 : Fin 32)]
set_option maxHeartbeats 4000000 in
theorem ctT3_end : blockEnd p256VerifyPrehashCode 0xCD2 ctT3 = some 0xCF4 := by decide
def ctT4 : List BInstr :=
  [.aluImm .sll a2 a1 0x1F, .aluImm .srl a0 a0 0x1, .alu .or a0 a0 a2, .sw sp a0 0x44, .aluImm .sra a1 a1 0x1,
   .sw sp a1 0x4C, .alu .add a0 x0 (24 : Fin 32), .alu .add a1 x0 (23 : Fin 32), .alu .add a2 x0 (26 : Fin 32),
   .lw (18 : Fin 32) sp 0x54, .alu .add a3 x0 (18 : Fin 32), .lw (21 : Fin 32) sp 0x1C, .alu .add a4 x0 (21 : Fin 32)]
set_option maxHeartbeats 4000000 in
theorem ctT4_end : blockEnd p256VerifyPrehashCode 0xCFC ctT4 = some 0xD18 := by decide
def ctT5 : List BInstr :=
  [.aluImm .srl a2 a0 0x1F, .aluImm .sll a1 a1 0x1, .alu .or a1 a1 a2, .sw sp a1 0x34, .aluImm .sll a0 a0 0x1,
   .sw sp a0 0x2C, .alu .add a0 x0 (24 : Fin 32), .alu .add a1 x0 (19 : Fin 32), .lw (8 : Fin 32) sp 0x30,
   .alu .add a2 x0 (8 : Fin 32), .alu .add a3 x0 (22 : Fin 32), .lw (25 : Fin 32) sp 0x28,
   .alu .add a4 x0 (25 : Fin 32)]
set_option maxHeartbeats 4000000 in
theorem ctT5_end : blockEnd p256VerifyPrehashCode 0xD20 ctT5 = some 0xD3C := by decide
def ctT6 : List BInstr :=
  [.aluImm .srl a2 a0 0x1F, .aluImm .sll a1 a1 0x1, .aluImm .sll (20 : Fin 32) a0 0x1, .alu .or a1 a1 a2,
   .sw sp a1 0x20, .alu .sltu a0 x0 (23 : Fin 32), .alu .sub a4 x0 (26 : Fin 32), .alu .sub a3 x0 (23 : Fin 32),
   .alu .sub a4 a4 a0, .lw (9 : Fin 32) sp 0x24, .alu .add a0 x0 (9 : Fin 32), .alu .add a1 x0 (23 : Fin 32),
   .alu .add a2 x0 (26 : Fin 32)]
set_option maxHeartbeats 4000000 in
theorem ctT6_end : blockEnd p256VerifyPrehashCode 0xD44 ctT6 = some 0xD68 := by decide
def ctT7 : List BInstr :=
  [.aluImm .add a2 sp 0x7FF, .aluImm .add a2 a2 0x121, .sb a2 (27 : Fin 32) 0x360,
   .aluImm .add (23 : Fin 32) sp 0x7FF, .aluImm .add (23 : Fin 32) (23 : Fin 32) 0x481, .aluImm .add a2 sp 0x7FF,
   .aluImm .add a2 a2 0x121, .lbu a2 a2 0x360, .alu .sub a3 x0 a2, .aluImm .sltu a2 a2 0x1, .alu .and a0 a0 a3,
   .alu .sltu a4 x0 (19 : Fin 32), .aluImm .add a2 a2 0xFFFFFFFF, .alu .and a1 a1 a2,
   .alu .add (18 : Fin 32) (18 : Fin 32) a0, .sw sp (18 : Fin 32) 0x54, .alu .sltu a0 (18 : Fin 32) a0,
   .alu .add a1 a1 (21 : Fin 32), .alu .sub a5 x0 (8 : Fin 32), .alu .add (18 : Fin 32) a1 a0,
   .alu .sub a3 x0 (19 : Fin 32), .alu .sub a4 a5 a4, .alu .add a0 x0 (9 : Fin 32),
   .aluImm .add (24 : Fin 32) sp 0x7FF, .aluImm .add (24 : Fin 32) (24 : Fin 32) 0x121,
   .alu .add a1 x0 (19 : Fin 32), .alu .add a2 x0 (8 : Fin 32)]
set_option maxHeartbeats 4000000 in
theorem ctT7_end : blockEnd p256VerifyPrehashCode 0xD70 ctT7 = some 0xDCA := by decide
def ctT8 : List BInstr :=
  [.alu .add (8 : Fin 32) x0 (24 : Fin 32), .lw a4 sp 0x3C, .sb (24 : Fin 32) (27 : Fin 32) 0x360,
   .lbu a2 (24 : Fin 32) 0x360, .aluImm .add a4 a4 0xFFFFFFFF, .alu .sub a3 x0 a2, .aluImm .sltu a2 a2 0x1,
   .aluImm .add a2 a2 0xFFFFFFFF, .alu .and a0 a0 a3, .alu .and a1 a1 a2, .alu .add (22 : Fin 32) (22 : Fin 32) a0,
   .alu .sltu a0 (22 : Fin 32) a0, .alu .add a1 a1 (25 : Fin 32), .lw (25 : Fin 32) sp 0x20, .alu .add a3 a1 a0,
   .lw (23 : Fin 32) sp 0x2C, .lw (24 : Fin 32) sp 0x38, .lw (26 : Fin 32) sp 0x34]
set_option maxHeartbeats 4000000 in
theorem ctT8_end : blockEnd p256VerifyPrehashCode 0xDD2 ctT8 = some 0xE02 := by decide

/-- The constant-time loop's state, as `CtRegs` with the frame at
`B + 0x21A0`: `δ` in the slot at 0x40 and `s8`, `f` in the slots at 0x50 and
0x48, `g` in the slots at 0x44 and 0x4C, `u` in `s7:s10`, `v` in `s4:s9`,
`q` in the slot at 0x54 and `s2`, and `r` in `s6:a3` (low word first). -/
def CtRegs2 (B : Word) (M : Word → BitVec 8) (f : Fin 32 → Word) (s : Ds) : Prop :=
  W64 (memLoad32 M (B + 0x21A0 + 0x40)) (f 24) = s.δ ∧
  W64 (memLoad32 M (B + 0x21A0 + 0x50)) (memLoad32 M (B + 0x21A0 + 0x48)) = s.f ∧
  W64 (memLoad32 M (B + 0x21A0 + 0x44)) (memLoad32 M (B + 0x21A0 + 0x4C)) = s.g ∧
  W64 (f 23) (f 26) = s.u ∧ W64 (f 20) (f 25) = s.v ∧
  W64 (memLoad32 M (B + 0x21A0 + 0x54)) (f 18) = s.q ∧ W64 (f 22) (f 13) = s.r

theorem CtRegs2.of {B : Word} {M M' : Word → BitVec 8} {f f' : Fin 32 → Word} {s : Ds} (h : CtRegs2 B M f s)
    (hm : M' = M) (hf : ∀ q, f' q = f q) : CtRegs2 B M' f' s := by
  subst hm; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨by rw [hf]; exact h1, h2, h3, by rw [hf, hf]; exact h4, by rw [hf, hf]; exact h5,
    by rw [hf]; exact h6, by rw [hf, hf]; exact h7⟩

end C3.RV32.P2v
