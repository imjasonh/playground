import C3BootProofs.Proofs.FeAdd
import C3BootProofs.Proofs.FeSub
import C3BootProofs.Proofs.AsProjective

/-!
# Calls to the field operations

Many compiled curve25519 functions are chains of calls to the proved
`FieldElement2625` add, sub, and mul. These lemmas run one such call from a
caller's `St` and state its result on the limbs as a function of the
operands' limbs, so a caller's proof only supplies where each callee runs.
-/

namespace C3.RV32

/-- The ten 32-bit limbs at `a`. -/
def limbs (M : Word → BitVec 8) (a : Word) : Nat → Word := fun i => memLoad32 M (a + BitVec.ofNat 32 (4 * i))

/-- The limbs `add` stores for operand limbs `x` and `y`. -/
def feAddW (x y : Nat → Word) : Nat → Word := fun i => x i + y i

/-- The limbs `sub` stores for operand limbs `x` and `y`. -/
def feSubW (x y : Nat → Word) : Nat → Word := fun i => BitVec.ofNat 32 ((feSubSpec x y).getD i 0)

/-- The limbs `mul` stores for operand limbs `x` and `y`. -/
def feMulW (x y : Nat → Word) : Nat → Word := fun i =>
  BitVec.ofNat 32 ((feMulSpec (x 0).toNat (x 1).toNat (x 2).toNat (x 3).toNat (x 4).toNat (x 5).toNat (x 6).toNat
    (x 7).toNat (x 8).toNat (x 9).toNat (y 0).toNat (y 1).toNat (y 2).toNat (y 3).toNat (y 4).toNat (y 5).toNat
    (y 6).toNat (y 7).toNat (y 8).toNat (y 9).toNat).getD i 0)

theorem limbs_of_wordsAt {M : Word → BitVec 8} {a : Word} {L : List Nat}
    (h : (wordsAt M a 10).map BitVec.toNat = L) : ∀ i, i < 10 → limbs M a i = BitVec.ofNat 32 (L.getD i 0) := by
  intro i hi
  rw [← h]
  unfold wordsAt limbs
  rw [List.getD_eq_getElem?_getD, List.map_map, List.getElem?_map, List.getElem?_range hi]
  exact (ofNat_toNat_self _).symm

theorem St.callFeMul {M : Word → BitVec 8} {P : Word} {code : List Nat} {nm : Machine} {off : Nat}
    (s : St M P nm off (reg nm)) (hc : CodeIn M P code) {imm o cb : Word}
    (h1 : fetchRel code off = some (.auipc ra imm, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = cb) (hev : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (env : FeMEnv M cb (reg nm sp) (reg nm a0) (reg nm a1) (reg nm a2)) :
    ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = reg nm sp ∧
      (∀ q, feMKeep q = true → q ≠ ra → reg nm' q = reg nm q) ∧
      (∀ i, i < 10 → limbs nm'.mem (reg nm a0) i = feMulW (limbs M (reg nm a1)) (limbs M (reg nm a2)) i) ∧
      ∀ x, Sep (reg nm sp + 0xFFFFFEC0) 0x140 x 1 → Sep (reg nm a0) 40 x 1 → nm'.mem x = M x := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb env.hP
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := feMul_correct n1 (by rw [mem1]; exact env) pc1
    (r1 a0 (by decide)) (r1 a1 (by decide)) (r1 a2 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev) (r1 sp (by decide))
  rw [mem1] at w2 f2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hk hr => by rw [k2 q hk, r1 q hr], fun i hi => ?_, f2⟩
  rw [limbs_of_wordsAt w2 i hi]; rfl

theorem St.callFeAdd {M : Word → BitVec 8} {P : Word} {code : List Nat} {nm : Machine} {off : Nat}
    (s : St M P nm off (reg nm)) (hc : CodeIn M P code) {imm o cb G : Word}
    (h1 : fetchRel code off = some (.auipc ra imm, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = cb) (hev : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg nm sp = G + 0x50) (env : FeAddEnv M cb G (reg nm a0) (reg nm a1) (reg nm a2)) :
    ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = reg nm sp ∧
      (∀ q, feMKeep q = true → q ≠ ra → reg nm' q = reg nm q) ∧
      (∀ i, i < 10 → limbs nm'.mem (reg nm a0) i = feAddW (limbs M (reg nm a1)) (limbs M (reg nm a2)) i) ∧
      ∀ x, Sep G 0x50 x 1 → Sep (reg nm a0) 40 x 1 → nm'.mem x = M x := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb env.hP
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := feAdd_correct n1 (by rw [mem1]; exact env) pc1
    (r1 a0 (by decide)) (r1 a1 (by decide)) (r1 a2 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev) (by rw [r1 sp (by decide), hsp])
  rw [mem1] at w2 f2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2, hsp],
    fun q hk hr => by rw [k2 q hk, r1 q hr], fun i hi => ?_, f2⟩
  exact w2 i hi

theorem St.callFeSub {M : Word → BitVec 8} {P : Word} {code : List Nat} {nm : Machine} {off : Nat}
    (s : St M P nm off (reg nm)) (hc : CodeIn M P code) {imm o cb G : Word}
    (h1 : fetchRel code off = some (.auipc ra imm, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = cb) (hev : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg nm sp = G + 0xB0) (env : FeSubEnv M cb G (reg nm a0) (reg nm a1) (reg nm a2)) :
    ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = reg nm sp ∧
      (∀ q, feMKeep q = true → q ≠ ra → reg nm' q = reg nm q) ∧
      (∀ i, i < 10 → limbs nm'.mem (reg nm a0) i = feSubW (limbs M (reg nm a1)) (limbs M (reg nm a2)) i) ∧
      ∀ x, Sep G 0xB0 x 1 → Sep (reg nm a0) 40 x 1 → nm'.mem x = M x := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb env.hP
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := feSub_correct n1 (by rw [mem1]; exact env) pc1
    (r1 a0 (by decide)) (r1 a1 (by decide)) (r1 a2 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev) (by rw [r1 sp (by decide), hsp])
  rw [mem1] at w2 f2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2, hsp],
    fun q hk hr => by rw [k2 q hk, r1 q hr], fun i hi => ?_, f2⟩
  exact limbs_of_wordsAt w2 i hi

end C3.RV32
