import C3BootProofs.Proofs.Panic
import C3BootProofs.Proofs.MemcpyAny

/-!
# Checked copies: `NafLookupTable5::select` and `CtOption::unwrap`

`NafLookupTable5<ProjectiveNielsPoint>::select(x)` bounds-checks `x / 2`
against the table's eight entries and tail-calls `memcpy` for the 160-byte
entry. `CtOption<NonZeroScalar>::unwrap` asserts the choice byte is 1 and
tail-calls `memcpy` for the scalar. Each panics otherwise.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem nsl_at_0 : fetchRel nafSelectCode 0x0 = some (.aluImm .add a4 x0 0xF, 2) := by decide
theorem nsl_at_2 : fetchRel nafSelectCode 0x2 = some (.aluImm .srl a3 a2 0x1, 4) := by decide
theorem nsl_at_6 : fetchRel nafSelectCode 0x6 = some (.branch .bltu a4 a2 0x1A, 4) := by decide
theorem nsl_at_18 : fetchRel nafSelectCode 0x18 = some (.auipc (6 : Fin 32) 0x4000, 4) := by decide
theorem nsl_at_1c : fetchRel nafSelectCode 0x1C = some (.jalr x0 (6 : Fin 32) 0x42, 4) := by decide
theorem nsl_at_20 : fetchRel nafSelectCode 0x20 = some (.aluImm .add a1 x0 0x8, 2) := by decide
theorem nsl_at_22 : fetchRel nafSelectCode 0x22 = some (.alu .add a0 x0 a3, 2) := by decide
theorem nsl_at_24 : fetchRel nafSelectCode 0x24 = some (.auipc ra 0xFFFFD000, 4) := by decide
theorem nsl_at_28 : fetchRel nafSelectCode 0x28 = some (.jalr ra ra 0xFFFFFA90, 4) := by decide

def nslB : List BInstr :=
  [.aluImm .add a2 x0 0xA0, .alu .mul a2 a3 a2, .alu .add a1 a1 a2, .aluImm .add a2 x0 0xA0]

theorem nslB_end : blockEnd nafSelectCode 0xA nslB = some 0x18 := by decide

theorem cu4_at_2 : fetchRel ctUnwrap384Code 0x2 = some (.load .lbu a2 a1 0x30, 4) := by decide
theorem cu4_at_6 : fetchRel ctUnwrap384Code 0x6 = some (.aluImm .add a3 x0 0x1, 2) := by decide
theorem cu4_at_8 : fetchRel ctUnwrap384Code 0x8 = some (.store .sb sp a2 0xF, 4) := by decide
theorem cu4_at_c : fetchRel ctUnwrap384Code 0xC = some (.branch .bne a2 a3 0x12, 4) := by decide
theorem cu4_at_16 : fetchRel ctUnwrap384Code 0x16 = some (.auipc (6 : Fin 32) 0x11000, 4) := by decide
theorem cu4_at_1a : fetchRel ctUnwrap384Code 0x1A = some (.jalr x0 (6 : Fin 32) 0x6B2, 4) := by decide
theorem cu4_at_1e : fetchRel ctUnwrap384Code 0x1E = some (.aluImm .add a0 sp 0xF, 4) := by decide
theorem cu4_at_22 : fetchRel ctUnwrap384Code 0x22 = some (.auipc ra 0x10000, 4) := by decide
theorem cu4_at_26 : fetchRel ctUnwrap384Code 0x26 = some (.jalr ra ra 0x682, 4) := by decide
theorem cu2_at_2 : fetchRel ctUnwrap256Code 0x2 = some (.load .lbu a2 a1 0x20, 4) := by decide
theorem cu2_at_6 : fetchRel ctUnwrap256Code 0x6 = some (.aluImm .add a3 x0 0x1, 2) := by decide
theorem cu2_at_8 : fetchRel ctUnwrap256Code 0x8 = some (.store .sb sp a2 0xF, 4) := by decide
theorem cu2_at_c : fetchRel ctUnwrap256Code 0xC = some (.branch .bne a2 a3 0x12, 4) := by decide
theorem cu2_at_16 : fetchRel ctUnwrap256Code 0x16 = some (.auipc (6 : Fin 32) 0x11000, 4) := by decide
theorem cu2_at_1a : fetchRel ctUnwrap256Code 0x1A = some (.jalr x0 (6 : Fin 32) 0x62A, 4) := by decide
theorem cu2_at_1e : fetchRel ctUnwrap256Code 0x1E = some (.aluImm .add a0 sp 0xF, 4) := by decide
theorem cu2_at_22 : fetchRel ctUnwrap256Code 0x22 = some (.auipc ra 0x10000, 4) := by decide
theorem cu2_at_26 : fetchRel ctUnwrap256Code 0x26 = some (.jalr ra ra 0x5FA, 4) := by decide

def cuA (k : Word) : List BInstr := [.aluImm .add sp sp 0xFFFFFFF0, .lbu a2 a1 k, .aluImm .add a3 x0 0x1, .sb sp a2 0xF]
def cuB (k : Word) : List BInstr := [.aluImm .add a2 x0 k, .aluImm .add sp sp 0x10]

theorem cu4A_end : blockEnd ctUnwrap384Code 0 (cuA 0x30) = some 0xC := by decide
theorem cu4B_end : blockEnd ctUnwrap384Code 0x10 (cuB 0x30) = some 0x16 := by decide
theorem cu2A_end : blockEnd ctUnwrap256Code 0 (cuA 0x20) = some 0xC := by decide
theorem cu2B_end : blockEnd ctUnwrap256Code 0x10 (cuB 0x20) = some 0x16 := by decide
end

def nslBase : Word := BitVec.ofNat 32 nafSelectAddress
def stubBase : Word := BitVec.ofNat 32 memcpyStubAddress

theorem nsl_off : ∀ n, n < 16 →
    aluEval .mul (aluEval .srl (BitVec.ofNat 32 n) 0x1) 0xA0 = BitVec.ofNat 32 (n / 2 * 160) := by decide

theorem nsl_off' {x : Word} (hx : x.toNat ≤ 15) :
    aluEval .mul (aluEval .srl x 0x1) 0xA0 = BitVec.ofNat 32 (x.toNat / 2 * 160) := by
  have e : BitVec.ofNat 32 x.toNat = x :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt x.isLt)
  have := nsl_off x.toNat (by omega)
  rwa [e] at this

set_option maxRecDepth 20000 in
/-- **The compiled `NafLookupTable5<ProjectiveNielsPoint>::select`** with
the table at `tbl` and `x`: for `x ≤ 15` it copies the 160-byte entry
`x / 2` to `out` with `memcpy` and returns; otherwise it panics. -/
theorem nafSelect_correct (m : Machine) {out tbl x retAddr : Word} (hP : PanicCode m.mem)
    (hc : CodeIn m.mem nslBase nafSelectCode) (hstub : CodeIn m.mem stubBase memcpyStubCode)
    (hpc : m.pc = nslBase) (ha0 : reg m a0 = out) (ha1 : reg m a1 = tbl) (ha2 : reg m a2 = x)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    (x.toNat ≤ 15 →
      McEnv m.mem (stubBase + 8) out (tbl + BitVec.ofNat 32 (x.toNat / 2 * 160)) (reg m sp + 0xFFFFFFF0) 160 →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
        ∀ y, Sep (reg m sp + 0xFFFFFFF0) 16 y 1 →
          m'.mem y = copyBytes m.mem out (tbl + BitVec.ofNat 32 (x.toNat / 2 * 160)) 160 y) ∧
    (15 < x.toNat → Room (reg m sp) 48 → Panics m) := by
  have st0 : St m.mem nslBase m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨m1, e1, s1⟩ := st0.aluImm hc nsl_at_0 (off' := 2) (by decide)
  obtain ⟨m2, e2, s2⟩ := s1.aluImm hc nsl_at_2 (off' := 6) (by decide)
  have B : branchTaken .bltu (upd (upd (reg m) a4 (aluEval .add (reg m x0) 0xF)) a3
      (aluEval .srl (upd (reg m) a4 (aluEval .add (reg m x0) 0xF) a2) 0x1) a4)
      (upd (upd (reg m) a4 (aluEval .add (reg m x0) 0xF)) a3
        (aluEval .srl (upd (reg m) a4 (aluEval .add (reg m x0) 0xF) a2) 0x1) a2) = decide (15 < x.toNat) := by
    simp +decide only [upd_app, ↓reduceIte]; rw [hz, ha2]; rfl
  refine ⟨fun hx E => ?_, fun hx hR => ?_⟩
  · obtain ⟨m3, e3, s3⟩ := s2.notTaken hc 0xA nsl_at_6 (by decide) (by rw [B, decide_eq_false (Nat.not_lt.mpr hx)])
    obtain ⟨m4, c4, s4⟩ := St.block nslB s3 hc nslB_end (by simp [BlockOk, BInstr.ok, nslB])
    simp only [runBlock, BInstr.run, nslB] at s4
    obtain ⟨m5, e5, s5⟩ := s4.auipc hc nsl_at_18 (off' := 0x1C) (by decide)
    obtain ⟨m6, e6, pc6, mem6, regs6⟩ := s5.jalr hc nsl_at_1c
    have pc6' : m6.pc = stubBase := by
      rw [pc6]; simp +decide only [upd_app, ↓reduceIte]; try decide
    have r6 : ∀ q, reg m6 q = _ := regs6
    have A0 : reg m6 a0 = out := by rw [r6]; simp +decide only [upd_app, ↓reduceIte]; exact ha0
    have A1 : reg m6 a1 = tbl + BitVec.ofNat 32 (x.toNat / 2 * 160) := by
      rw [r6]; simp +decide only [upd_app, ↓reduceIte]
      rw [ha1, ha2, show aluEval .add (0 : Word) 160 = 0xA0 from rfl, nsl_off' hx]; rfl
    have A2 : reg m6 a2 = BitVec.ofNat 32 160 := by rw [r6]; simp +decide only [upd_app, ↓reduceIte]; try rfl
    have RA : reg m6 ra = retAddr := by rw [r6]; simp +decide only [upd_app, ↓reduceIte]; exact hra
    have SP : reg m6 sp = reg m sp := by rw [r6]; simp +decide only [upd_app, ↓reduceIte]
    obtain ⟨m7, c7, pc7, sp7, _, mem7, k7⟩ := memcpy_correct m6 stubBase retAddr out _ 160
      (by intro i hi; rw [mem6]; exact hstub i hi) (by decide) pc6' A0 A1 A2 RA hret (by rw [mem6, SP]; exact E)
    have K6 : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m6 q = reg m q := by
      intro q hq
      have hq' : q = 3 ∨ q = 4 ∨ q = 8 ∨ q = 9 ∨ q = 18 ∨ q = 19 ∨ q = 20 ∨ q = 21 ∨ q = 22 ∨ q = 23 ∨ q = 24 ∨
          q = 25 ∨ q = 26 ∨ q = 27 := by revert hq; revert q; decide
      rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (rw [r6]; simp +decide only [upd_app, ↓reduceIte])
    refine ⟨m7, .cons e1 (.cons e2 (.cons e3 (c4.trans (.cons e5 (.cons e6 c7))))), pc7, by rw [sp7, SP],
      fun q hq => ?_, fun y hy => ?_⟩
    · rw [k7 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide), K6 q hq]
    rw [mem7 y (by rw [SP]; exact hy), mem6]
  · obtain ⟨m3, e3, s3⟩ := s2.taken hc 0x20 nsl_at_6 (by decide) (by rw [B, decide_eq_true hx])
    obtain ⟨m4, e4, s4⟩ := s3.aluImm hc nsl_at_20 (off' := 0x22) (by decide)
    obtain ⟨m5, e5, s5⟩ := s4.alu hc nsl_at_22 (off' := 0x24) (by decide)
    obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s5.self.callRa hc nsl_at_24 nsl_at_28
      (cb := BitVec.ofNat 32 panicBoundsCheckAddress) (by decide) (by decide)
    refine Panics.of_steps (.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 c1)))))
      (panicBoundsCheck_panics n1 (by rw [mem1]; exact hP) pc1 ?_)
    rw [regs1, upd_ne (by decide) (by decide), s5.regs]
    simp +decide only [upd_app, ↓reduceIte]; exact hR

theorem McEnv.store8_frame {M : Word → BitVec 8} {base dst src F : Word} {N : Nat}
    (E : McEnv M base dst src F N) {o : Nat} (ho : o < 16) {v : BitVec 8} :
    McEnv (memStore8 M (F + BitVec.ofNat 32 o) v) base dst src F N :=
  { E with code := E.code.store8 (E.hFC.sub (c := o) (l := 1) (by omega)) }

theorem cu_bne : ∀ b : BitVec 8, branchTaken .bne (b.zeroExtend 32) 1 = !decide (b = 1) := by decide

theorem cu_frame {S : Word} (h : 16 ≤ S.toNat) (hS : S.toNat ≤ dramEnd) :
    (S + 0xFFFFFFF0 + BitVec.ofNat 32 0xF).toNat + 1 ≤ dramEnd := by
  unfold dramEnd at *
  rw [BitVec.toNat_add, BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 4294967280 from rfl, BitVec.toNat_ofNat]
  omega

set_option maxRecDepth 20000 in
/-- The shape of both `CtOption<NonZeroScalar>::unwrap`s: read the choice
byte at `s + k`, spill it to the stack, and either tail-call `memcpy` for
`N` bytes or pass the spilled byte to `assert_failed::<u8, u8>`. -/
theorem ctUnwrap_gen (m : Machine) {B out s retAddr k imm1 o1 imm2 o2 : Word} {code : List Nat} {N : Nat}
    (hP : PanicCode m.mem) (hc : CodeIn m.mem B code) (hstub : CodeIn m.mem stubBase memcpyStubCode)
    (hB : dramEnd ≤ B.toNat) (hBl : B.toNat + code.length ≤ 2 ^ 32)
    (hpc : m.pc = B) (ha0 : reg m a0 = out) (ha1 : reg m a1 = s)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hR : Room (reg m sp) 64)
    (eA : blockEnd code 0 (cuA k) = some 0xC) (eB : blockEnd code 0x10 (cuB (BitVec.ofNat 32 N)) = some 0x16)
    (fC : fetchRel code 0xC = some (.branch .bne a2 a3 0x12, 4))
    (f16 : fetchRel code 0x16 = some (.auipc (6 : Fin 32) imm1, 4))
    (f1a : fetchRel code 0x1A = some (.jalr x0 (6 : Fin 32) o1, 4))
    (f1e : fetchRel code 0x1E = some (.aluImm .add a0 sp 0xF, 4))
    (f22 : fetchRel code 0x22 = some (.auipc ra imm2, 4)) (f26 : fetchRel code (0x22 + 4) = some (.jalr ra ra o2, 4))
    (hT1 : (B + BitVec.ofNat 32 0x16 + imm1 + o1) &&& ~~~1 = stubBase)
    (hT2 : B + BitVec.ofNat 32 0x22 + imm2 + o2 = BitVec.ofNat 32 assertFailedU8Address) :
    (m.mem (s + k) = 1 → McEnv m.mem (stubBase + 8) out s (reg m sp + 0xFFFFFFF0) N →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        ∀ y, Sep (reg m sp + 0xFFFFFFF0) 16 y 1 → m'.mem y = copyBytes m.mem out s N y) ∧
    (m.mem (s + k) ≠ 1 → Panics m) := by
  have st0 : St m.mem B m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := st0.zero
  obtain ⟨S, hS⟩ : ∃ S, reg m sp = S := ⟨_, rfl⟩
  rw [hS] at hR ⊢
  obtain ⟨F, hF⟩ : ∃ F, S + 0xFFFFFFF0 = F := ⟨_, rfl⟩
  have hFw : (F + BitVec.ofNat 32 0xF).toNat + 1 ≤ dramEnd := by rw [← hF]; exact cu_frame (by have := hR.2.1; omega) hR.2.2
  have sFB : Sep (F + BitVec.ofNat 32 0xF) 1 B code.length := sep_of_le (by omega) hBl
  obtain ⟨mA, cA, uA⟩ := St.block (cuA k) st0 hc eA (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, cuA, upd_app, ↓reduceIte, and_true, true_and]
    simp only [ev_add]; rw [hS, hF]; exact sFB)
  obtain ⟨t, ht⟩ : ∃ t, m.mem (s + k) = t := ⟨_, rfl⟩
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore8 m.mem (F + BitVec.ofNat 32 0xF) ((t.zeroExtend 32 : Word).extractLsb' 0 8) = M1 :=
    ⟨_, rfl⟩
  have MA : (runBlock (cuA k) (m.mem, reg m)).1 = M1 := by
    simp +decide only [runBlock, BInstr.run, cuA, upd_app, ↓reduceIte]; simp only [ev_add]; rw [hS, hF, ha1, ht, ← hM1]; rfl
  have uA' : St M1 B mA 0xC (reg mA) := ⟨uA.pc, by rw [uA.mem, MA], fun _ => rfl⟩
  have RA : ∀ q, reg mA q = (runBlock (cuA k) (m.mem, reg m)).2 q := uA.regs
  have A2 : reg mA a2 = t.zeroExtend 32 := by
    rw [RA]; simp +decide only [runBlock, BInstr.run, cuA, upd_app, ↓reduceIte]; rw [ha1, ht]
  have A3 : reg mA a3 = 1 := by rw [RA]; simp +decide only [runBlock, BInstr.run, cuA, upd_app, ↓reduceIte]; try rfl
  have A0 : reg mA a0 = out := by rw [RA]; simp +decide only [runBlock, BInstr.run, cuA, upd_app, ↓reduceIte]; exact ha0
  have AR : reg mA ra = retAddr := by rw [RA]; simp +decide only [runBlock, BInstr.run, cuA, upd_app, ↓reduceIte]; exact hra
  have AS : reg mA sp = F := by
    rw [RA]; simp +decide only [runBlock, BInstr.run, cuA, upd_app, ↓reduceIte]; simp only [ev_add]; rw [hS, hF]
  have hcA : CodeIn M1 B code := by rw [← hM1]; exact hc.store8 sFB
  have hzA := uA'.zero
  refine ⟨fun h1 E => ?_, fun h1 => ?_⟩
  · rw [ht] at h1; rw [hF] at E
    obtain ⟨m3, e3, s3⟩ := uA'.notTaken hcA 0x10 fC (by decide) (by rw [A2, A3, h1]; decide)
    obtain ⟨m4, c4, s4⟩ := St.block (cuB (BitVec.ofNat 32 N)) s3 hcA eB (by simp [BlockOk, BInstr.ok, cuB])
    obtain ⟨m5, e5, s5⟩ := s4.auipc hcA f16 (off' := 0x1A) (by decide)
    obtain ⟨m6, e6, pc6, mem6, regs6⟩ := s5.jalr hcA f1a
    have r6 : ∀ q, reg m6 q = _ := regs6
    have pc6' : m6.pc = stubBase := by
      rw [pc6]; simp +decide only [runBlock, BInstr.run, cuB, upd_app, ↓reduceIte]; exact hT1
    have S6 : reg m6 sp = S := by
      rw [r6]; simp +decide only [runBlock, BInstr.run, cuB, upd_app, ↓reduceIte]; simp only [ev_add]
      rw [AS, ← hF, BitVec.add_assoc]; exact BitVec.add_zero S
    have B0 : reg m6 a0 = out := by
      rw [r6]; simp +decide only [runBlock, BInstr.run, cuB, upd_app, ↓reduceIte]; exact A0
    have B1 : reg m6 a1 = s := by
      rw [r6]; simp +decide only [runBlock, BInstr.run, cuB, upd_app, ↓reduceIte]
      rw [RA]; simp +decide only [runBlock, BInstr.run, cuA, upd_app, ↓reduceIte]; exact ha1
    have B2 : reg m6 a2 = BitVec.ofNat 32 N := by
      rw [r6]; simp +decide only [runBlock, BInstr.run, cuB, upd_app, ↓reduceIte]; simp only [ev_add]
      rw [hzA]; exact BitVec.zero_add _
    have BR : reg m6 ra = retAddr := by
      rw [r6]; simp +decide only [runBlock, BInstr.run, cuB, upd_app, ↓reduceIte]; exact AR
    have hsS : Sep (F + BitVec.ofNat 32 0xF) 1 stubBase memcpyStubCode.length :=
      sep_of_le (by have : dramEnd ≤ stubBase.toNat := by decide
                    omega) (by decide)
    have fr : ∀ y, Sep F 16 y 1 → M1 y = m.mem y := fun y hy => by
      rw [← hM1]; exact memStore8_ne (frame_out hy (a := 0xF) (by decide))
    obtain ⟨m7, c7, pc7, sp7, _, mem7, _⟩ := memcpy_correct m6 stubBase retAddr out s N
      (by intro i hi; rw [mem6, ← hM1]; exact hstub.store8 hsS i hi) (by decide) pc6' B0 B1 B2 BR hret
      (by rw [mem6, S6, hF, ← hM1]; exact E.store8_frame (by decide))
    refine ⟨m7, cA.trans (.cons e3 (c4.trans (.cons e5 (.cons e6 c7)))), pc7, by rw [sp7, S6], fun y hy => ?_⟩
    rw [hF] at hy
    rw [mem7 y (by rw [S6, hF]; exact hy), mem6]
    exact copyBytes_congr fr E.hsF.symm hy
  · rw [ht] at h1
    obtain ⟨m3, e3, s3⟩ := uA'.taken hcA 0x1E fC (by decide) (by rw [A2, A3, cu_bne, decide_eq_false h1]; rfl)
    obtain ⟨m4, e4, s4⟩ := s3.aluImm hcA f1e (off' := 0x22) (by decide)
    obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s4.self.callRa hcA (by exact f22) f26 hT2 (by decide)
    refine Panics.of_steps (cA.trans (.cons e3 (.cons e4 c1)))
      (assertFailedU8_panics n1 (by rw [mem1, ← hM1]; exact hP.store8 hFw) pc1 ?_)
    rw [regs1, upd_ne (by decide) (by decide), s4.regs, upd_ne (by decide) (by decide), AS, ← hF]
    exact hR.frame

/-- **The compiled `CtOption<NonZeroScalar<NistP384>>::unwrap`** with the
option at `s`: when the choice byte at `s + 0x30` is 1, it copies the 48-byte
scalar to `out` with `memcpy` and returns; otherwise it panics. -/
theorem ctUnwrap384_correct (m : Machine) {out s retAddr : Word} (hP : PanicCode m.mem)
    (hc : CodeIn m.mem (BitVec.ofNat 32 ctUnwrap384Address) ctUnwrap384Code)
    (hstub : CodeIn m.mem stubBase memcpyStubCode) (hpc : m.pc = BitVec.ofNat 32 ctUnwrap384Address)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = s) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hR : Room (reg m sp) 64) :
    (m.mem (s + 0x30) = 1 → McEnv m.mem (stubBase + 8) out s (reg m sp + 0xFFFFFFF0) 0x30 →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        ∀ y, Sep (reg m sp + 0xFFFFFFF0) 16 y 1 → m'.mem y = copyBytes m.mem out s 0x30 y) ∧
    (m.mem (s + 0x30) ≠ 1 → Panics m) :=
  ctUnwrap_gen m hP hc hstub (by decide) (by decide) hpc ha0 ha1 hra hret hR cu4A_end cu4B_end cu4_at_c cu4_at_16
    cu4_at_1a cu4_at_1e cu4_at_22 cu4_at_26 (by decide) (by decide)

/-- **The compiled `CtOption<NonZeroScalar<NistP256>>::unwrap`** with the
option at `s`: when the choice byte at `s + 0x20` is 1, it copies the 32-byte
scalar to `out` with `memcpy` and returns; otherwise it panics. -/
theorem ctUnwrap256_correct (m : Machine) {out s retAddr : Word} (hP : PanicCode m.mem)
    (hc : CodeIn m.mem (BitVec.ofNat 32 ctUnwrap256Address) ctUnwrap256Code)
    (hstub : CodeIn m.mem stubBase memcpyStubCode) (hpc : m.pc = BitVec.ofNat 32 ctUnwrap256Address)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = s) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hR : Room (reg m sp) 64) :
    (m.mem (s + 0x20) = 1 → McEnv m.mem (stubBase + 8) out s (reg m sp + 0xFFFFFFF0) 0x20 →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = reg m sp ∧
        ∀ y, Sep (reg m sp + 0xFFFFFFF0) 16 y 1 → m'.mem y = copyBytes m.mem out s 0x20 y) ∧
    (m.mem (s + 0x20) ≠ 1 → Panics m) :=
  ctUnwrap_gen m hP hc hstub (by decide) (by decide) hpc ha0 ha1 hra hret hR cu2A_end cu2B_end cu2_at_c cu2_at_16
    cu2_at_1a cu2_at_1e cu2_at_22 cu2_at_26 (by decide) (by decide)

end C3.RV32
