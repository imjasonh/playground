import C3BootProofs.Proofs.EdDouble
import C3BootProofs.Proofs.AsExtended
import C3BootProofs.Proofs.FeCtEq
import C3BootProofs.Proofs.FeCall

/-!
# Calls to the Edwards point and field operations

These lemmas run one call to the proved `ProjectivePoint::double`,
`CompletedPoint::as_projective` and `as_extended`, `mul`, and `ct_eq` from a
caller's `St`, and state the result on each field element's limb list
(`feW`), so a caller composes the calls without restating their
environments' arithmetic.
-/

namespace C3.RV32

/-- `mul`'s output for limb lists `a` and `b`. -/
def mulL (a b : List Nat) : List Nat :=
  feMulSpec (a.getD 0 0) (a.getD 1 0) (a.getD 2 0) (a.getD 3 0) (a.getD 4 0) (a.getD 5 0) (a.getD 6 0)
    (a.getD 7 0) (a.getD 8 0) (a.getD 9 0) (b.getD 0 0) (b.getD 1 0) (b.getD 2 0) (b.getD 3 0) (b.getD 4 0)
    (b.getD 5 0) (b.getD 6 0) (b.getD 7 0) (b.getD 8 0) (b.getD 9 0)

/-- The canonical bytes of the field element with limb list `l`. -/
def bytesL (l : List Nat) : List Nat :=
  feToBytesOf (feReduceSpec (l.getD 0 0) (l.getD 1 0) (l.getD 2 0) (l.getD 3 0) (l.getD 4 0) (l.getD 5 0)
    (l.getD 6 0) (l.getD 7 0) (l.getD 8 0) (l.getD 9 0))

theorem feMulAt_eq (M : Word → BitVec 8) (x y : Word) : feMulAt M x y = mulL (feW M x) (feW M y) := rfl

theorem feBytesOf_eq (M : Word → BitVec 8) (x : Word) : feBytesOf M x = bytesL (feW M x) := by
  have e0 : (memLoad32 M x).toNat = (feW M x).getD 0 0 := by
    show _ = (memLoad32 M (x + BitVec.ofNat 32 (4 * 0))).toNat
    rw [show 4 * 0 = 0 from rfl, add_ofNat_zero]
  unfold feBytesOf
  rw [e0]
  rfl

theorem St.callEdDouble {M : Word → BitVec 8} {P : Word} {code : List Nat} {nm : Machine} {off : Nat}
    (s : St M P nm off (reg nm)) (hc : CodeIn M P code) {imm o cb : Word}
    (h1 : fetchRel code off = some (.auipc ra imm, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = cb) (hev : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (env : EdDblEnv M cb (reg nm sp + 0xFFFFFDF0) (reg nm a0) (reg nm a1)) :
    ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = reg nm sp ∧
      (∀ q, feMKeep q = true → q ≠ ra → reg nm' q = reg nm q) ∧
      edDoubleSpec (feW M (reg nm a1)) (feW M (reg nm a1 + 0x28)) (feW M (reg nm a1 + 0x50)) =
        (feW nm'.mem (reg nm a0), feW nm'.mem (reg nm a0 + 0x28), feW nm'.mem (reg nm a0 + 0x50),
          feW nm'.mem (reg nm a0 + 0x78)) ∧
      ∀ x, Sep (reg nm sp + 0xFFFFFDF0) 0x210 x 1 → Sep (reg nm a0) 160 x 1 → nm'.mem x = M x := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb env.hP
  have r1 := PEnv.reg1 regs1 s.zero
  have esp : reg nm sp + 0xFFFFFDF0 + 0x210 = reg nm sp := by rw [BitVec.add_assoc]; exact BitVec.add_zero _
  obtain ⟨n2, c2, pc2, sp2, k2, w0, w1, w2, w3, f2⟩ := edDouble_correct n1 (by rw [mem1]; exact env) pc1
    (r1 a0 (by decide)) (r1 a1 (by decide)) (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
    (by rw [r1 sp (by decide), esp])
  rw [mem1] at w0 w1 w2 w3 f2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, by rw [sp2, esp],
    fun q hk hr => by rw [k2 q hk, r1 q hr], ?_, f2⟩
  rw [w0, w1, w2, w3]

theorem St.callAsProj {M : Word → BitVec 8} {P : Word} {code : List Nat} {nm : Machine} {off : Nat}
    (s : St M P nm off (reg nm)) (hc : CodeIn M P code) {imm o cb : Word}
    (h1 : fetchRel code off = some (.auipc ra imm, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = cb) (hev : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (env : ApEnv M cb (reg nm sp) (reg nm a0) (reg nm a1)) :
    ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = reg nm sp ∧
      (∀ q, feMKeep q = true → q ≠ ra → reg nm' q = reg nm q) ∧
      feW nm'.mem (reg nm a0) = mulL (feW M (reg nm a1)) (feW M (reg nm a1 + 0x78)) ∧
      feW nm'.mem (reg nm a0 + 0x28) = mulL (feW M (reg nm a1 + 0x28)) (feW M (reg nm a1 + 0x50)) ∧
      feW nm'.mem (reg nm a0 + 0x50) = mulL (feW M (reg nm a1 + 0x50)) (feW M (reg nm a1 + 0x78)) ∧
      ∀ x, Sep (apR (reg nm sp)) 0x150 x 1 → Sep (reg nm a0) 120 x 1 → nm'.mem x = M x := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb env.hP
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w0, w1, w2, f2⟩ := asProjective_correct n1 (by rw [mem1]; exact env) pc1
    (r1 sp (by decide)) (r1 a0 (by decide)) (r1 a1 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev)
  rw [mem1] at w0 w1 w2 f2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hk hr => by rw [k2 q hk, r1 q hr],
    w0, w1, w2, f2⟩

theorem St.callAsExt {M : Word → BitVec 8} {P : Word} {code : List Nat} {nm : Machine} {off : Nat}
    (s : St M P nm off (reg nm)) (hc : CodeIn M P code) {imm o cb : Word}
    (h1 : fetchRel code off = some (.auipc ra imm, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = cb) (hev : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (env : AxEnv M cb (reg nm sp) (reg nm a0) (reg nm a1)) :
    ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = reg nm sp ∧
      (∀ q, feMKeep q = true → q ≠ ra → reg nm' q = reg nm q) ∧
      feW nm'.mem (reg nm a0) = mulL (feW M (reg nm a1)) (feW M (reg nm a1 + 0x78)) ∧
      feW nm'.mem (reg nm a0 + 0x28) = mulL (feW M (reg nm a1 + 0x28)) (feW M (reg nm a1 + 0x50)) ∧
      feW nm'.mem (reg nm a0 + 0x50) = mulL (feW M (reg nm a1 + 0x50)) (feW M (reg nm a1 + 0x78)) ∧
      feW nm'.mem (reg nm a0 + 0x78) = mulL (feW M (reg nm a1)) (feW M (reg nm a1 + 0x28)) ∧
      ∀ x, Sep (axR (reg nm sp)) 0x160 x 1 → Sep (reg nm a0) 160 x 1 → nm'.mem x = M x := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb env.hP
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w0, w1, w2, w3, f2⟩ := asExtended_correct n1 (by rw [mem1]; exact env) pc1
    (r1 sp (by decide)) (r1 a0 (by decide)) (r1 a1 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev)
  rw [mem1] at w0 w1 w2 w3 f2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hk hr => by rw [k2 q hk, r1 q hr],
    w0, w1, w2, w3, f2⟩

theorem St.callFeMulL {M : Word → BitVec 8} {P : Word} {code : List Nat} {nm : Machine} {off : Nat}
    (s : St M P nm off (reg nm)) (hc : CodeIn M P code) {imm o cb : Word}
    (h1 : fetchRel code off = some (.auipc ra imm, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = cb) (hev : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (env : FeMEnv M cb (reg nm sp) (reg nm a0) (reg nm a1) (reg nm a2)) :
    ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = reg nm sp ∧
      (∀ q, feMKeep q = true → q ≠ ra → reg nm' q = reg nm q) ∧
      feW nm'.mem (reg nm a0) = mulL (feW M (reg nm a1)) (feW M (reg nm a2)) ∧
      ∀ x, Sep (reg nm sp + 0xFFFFFEC0) 0x140 x 1 → Sep (reg nm a0) 40 x 1 → nm'.mem x = M x := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb env.hP
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨n2, c2, pc2, sp2, k2, w2, f2⟩ := feMul_correct n1 (by rw [mem1]; exact env) pc1
    (r1 a0 (by decide)) (r1 a1 (by decide)) (r1 a2 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev) (r1 sp (by decide))
  rw [mem1] at w2 f2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hk hr => by rw [k2 q hk, r1 q hr],
    w2, f2⟩

theorem St.callFeCtEq {M : Word → BitVec 8} {P : Word} {code : List Nat} {nm : Machine} {off : Nat}
    (s : St M P nm off (reg nm)) (hc : CodeIn M P code) {imm o cb : Word}
    (h1 : fetchRel code off = some (.auipc ra imm, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra o, 4))
    (hb : P + BitVec.ofNat 32 off + imm + o = cb) (hev : (P + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (env : FCEEnv M cb (reg nm sp) (reg nm a0) (reg nm a1)) :
    ∃ nm', Steps nm nm' ∧ St nm'.mem P nm' (off + 8) (reg nm') ∧ reg nm' sp = reg nm sp ∧
      reg nm' a0 = (if bytesL (feW M (reg nm a0)) = bytesL (feW M (reg nm a1)) then 1 else 0) ∧
      (∀ q, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg nm' q = reg nm q) ∧
      ∀ x, Sep (reg nm sp + 0xFFFFFF00) 0x100 x 1 → nm'.mem x = M x := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa hc h1 h2 hb env.hP
  have r1 := PEnv.reg1 regs1 s.zero
  obtain ⟨n2, c2, pc2, sp2, a02, k2, f2⟩ := feCtEq_correct n1 (by rw [mem1]; exact env) pc1
    (r1 sp (by decide)) (r1 a0 (by decide)) (r1 a1 (by decide)) (by rw [regs1]; simp +decide [upd])
    (even_clear _ hev)
  rw [mem1, feBytesOf_eq, feBytesOf_eq] at a02
  rw [mem1] at f2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, a02,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)], f2⟩

end C3.RV32
