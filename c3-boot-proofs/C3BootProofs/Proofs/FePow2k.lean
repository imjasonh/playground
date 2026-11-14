import C3BootProofs.Proofs.EdDouble

/-!
# `FieldElement2625::pow2k`

`curve25519_dalek`'s repeated squaring, as compiled: it squares the operand
into a buffer in its frame, then squares that buffer into a second one and
copies it back with `memcpy` `k - 1` times, and copies the buffer out to the
result with `memcpy`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem fpk_at_0 : fetchRel fePow2kCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFA0, 2) := by decide
theorem fpk_at_2 : fetchRel fePow2kCode 0x2 = some (.store .sw sp ra 0x5C, 2) := by decide
theorem fpk_at_4 : fetchRel fePow2kCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x58, 2) := by decide
theorem fpk_at_6 : fetchRel fePow2kCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x54, 2) := by decide
theorem fpk_at_8 : fetchRel fePow2kCode 0x8 = some (.alu .add (9 : Fin 32) x0 a2, 2) := by decide
theorem fpk_at_a : fetchRel fePow2kCode 0xA = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem fpk_at_c : fetchRel fePow2kCode 0xC = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem fpk_at_e : fetchRel fePow2kCode 0xE = some (.auipc ra 0x0, 4) := by decide
theorem fpk_at_12 : fetchRel fePow2kCode 0x12 = some (.jalr ra ra 0x44, 4) := by decide
theorem fpk_at_16 : fetchRel fePow2kCode 0x16 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFF, 2) := by decide
theorem fpk_at_18 : fetchRel fePow2kCode 0x18 = some (.branch .beq (9 : Fin 32) x0 0x20, 2) := by decide
theorem fpk_at_1a : fetchRel fePow2kCode 0x1A = some (.aluImm .add a0 sp 0x2C, 2) := by decide
theorem fpk_at_1c : fetchRel fePow2kCode 0x1C = some (.aluImm .add a1 sp 0x4, 2) := by decide
theorem fpk_at_1e : fetchRel fePow2kCode 0x1E = some (.auipc ra 0x0, 4) := by decide
theorem fpk_at_22 : fetchRel fePow2kCode 0x22 = some (.jalr ra ra 0x34, 4) := by decide
theorem fpk_at_26 : fetchRel fePow2kCode 0x26 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem fpk_at_28 : fetchRel fePow2kCode 0x28 = some (.aluImm .add a1 sp 0x2C, 2) := by decide
theorem fpk_at_2a : fetchRel fePow2kCode 0x2A = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem fpk_at_2e : fetchRel fePow2kCode 0x2E = some (.auipc ra 0x6000, 4) := by decide
theorem fpk_at_32 : fetchRel fePow2kCode 0x32 = some (.jalr ra ra 0x2BC, 4) := by decide
theorem fpk_at_36 : fetchRel fePow2kCode 0x36 = some (.jal x0 0xFFFFFFE0, 2) := by decide
theorem fpk_at_38 : fetchRel fePow2kCode 0x38 = some (.aluImm .add a1 sp 0x4, 2) := by decide
theorem fpk_at_3a : fetchRel fePow2kCode 0x3A = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem fpk_at_3e : fetchRel fePow2kCode 0x3E = some (.alu .add a0 x0 (8 : Fin 32), 2) := by decide
theorem fpk_at_40 : fetchRel fePow2kCode 0x40 = some (.auipc ra 0x6000, 4) := by decide
theorem fpk_at_44 : fetchRel fePow2kCode 0x44 = some (.jalr ra ra 0x2AA, 4) := by decide
theorem fpk_at_48 : fetchRel fePow2kCode 0x48 = some (.load .lw ra sp 0x5C, 2) := by decide
theorem fpk_at_4a : fetchRel fePow2kCode 0x4A = some (.load .lw (8 : Fin 32) sp 0x58, 2) := by decide
theorem fpk_at_4c : fetchRel fePow2kCode 0x4C = some (.load .lw (9 : Fin 32) sp 0x54, 2) := by decide
theorem fpk_at_4e : fetchRel fePow2kCode 0x4E = some (.aluImm .add sp sp 0x60, 2) := by decide
theorem fpk_at_50 : fetchRel fePow2kCode 0x50 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- `square` applied `k` times. -/
def sqIter : Nat → List Nat → List Nat
  | 0, l => l
  | k + 1, l => sqL (sqIter k l)

/-- Where `pow2k` runs: its code at an even `P` and its callees' where its
calls reach them, 0x110 bytes of stack at `G` (its 0x60-byte frame and the
0xB0 bytes below it that `square` uses), the result's 40 bytes at `out`,
and the operand's at `xp`. The stack is apart from the code, the result,
and the operand, and the result from the code `pow2k` runs after writing
it. -/
structure FpkEnv (M : Word → BitVec 8) (P G out xp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P fePow2kCode
  sq : CodeIn M (P + 0x52) feSquareCode
  sqi : CodeIn M (P + 0x78) feSquareInnerCode
  red : CodeIn M (P + 0xFFFFFCDE) feReduceCode
  mcS : CodeIn M (P + 0x62EA) memcpyStubCode
  mcB : CodeIn M (P + 0x62F2) memcpyBodyCode
  hG : G.toNat % 4 = 0
  hGt : G.toNat + 0x110 ≤ 2 ^ 32
  hout : out.toNat % 4 = 0
  hot : out.toNat + 40 < 2 ^ 32
  hx : xp.toNat % 4 = 0
  sGC : Sep G 0x110 P fePow2kCode.length
  sGQ : Sep G 0x110 (P + 0x52) feSquareCode.length
  sGI : Sep G 0x110 (P + 0x78) feSquareInnerCode.length
  sGR : Sep G 0x110 (P + 0xFFFFFCDE) feReduceCode.length
  sGM : Sep G 0x110 (P + 0x62EA) memcpyStubCode.length
  sGB : Sep G 0x110 (P + 0x62F2) memcpyBodyCode.length
  sOC : Sep out 40 P fePow2kCode.length
  sOB : Sep out 40 (P + 0x62F2) memcpyBodyCode.length
  sOG : Sep out 40 G 0x110
  sXG : Sep xp 40 G 0x110

/-- The registers `pow2k`'s loop leaves alone. -/
def pkKeep (q : Fin 32) : Bool :=
  q.val ∉ [1, 2, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

theorem pk_ne {q r : Fin 32} (hq : pkKeep q = true) (hr : pkKeep r = false) : q ≠ r := fun e => by
  subst e; rw [hr] at hq; exact Bool.noConfusion hq

theorem pk_notin {L : List (Fin 32)} (hL : ∀ r ∈ L, pkKeep r = false) {q : Fin 32} (hq : pkKeep q = true) :
    q ∉ L := fun h => by rw [hL q h] at hq; exact Bool.noConfusion hq

theorem pkKeep_sq : ∀ q, pkKeep q = true → feSquareKeep q = true := by decide

/-- Code that a stack-only frame leaves alone. -/
theorem fpk_codeS {M M0 : Word → BitVec 8} {G b : Word} {code : List Nat} (hc : CodeIn M0 b code)
    (hG : Sep G 0x110 b code.length) (fr : ∀ y, Sep G 0x110 y 1 → M y = M0 y) : CodeIn M b code :=
  fun i hi => by rw [fr _ (hG.subR (c := i) (l := 1) (by omega))]; exact hc i hi

/-- Code that a frame leaves alone. -/
theorem fpk_code {M M0 : Word → BitVec 8} {G out b : Word} {code : List Nat} (hc : CodeIn M0 b code)
    (hG : Sep G 0x110 b code.length) (hO : Sep out 40 b code.length)
    (fr : ∀ y, Sep G 0x110 y 1 → Sep out 40 y 1 → M y = M0 y) : CodeIn M b code :=
  fun i hi => by
    rw [fr _ (hG.subR (c := i) (l := 1) (by omega)) (hO.subR (c := i) (l := 1) (by omega))]; exact hc i hi

theorem fpk_sepG {G : Word} {c n d k : Nat} (h : c + n ≤ d ∨ d + k ≤ c) (h1 : c + n ≤ 0x110) (h2 : d + k ≤ 0x110) :
    Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
  sep_offsets G h (by omega) (by omega)

theorem fpk_sepG0 {G : Word} {c n k : Nat} (h : k ≤ c) (h1 : c + n ≤ 0x110) : Sep (G + BitVec.ofNat 32 c) n G k := by
  have := fpk_sepG (G := G) (c := c) (n := n) (d := 0) (k := k) (.inr (by omega)) h1 (by omega)
  rwa [add_ofNat_zero] at this

/-- `square`'s environment, for a call from `pow2k`. -/
theorem fpk_sqEnv {M M0 : Word → BitVec 8} {P G out xp o x : Word} (env : FpkEnv M0 P G out xp)
    (fr : ∀ y, Sep G 0x110 y 1 → M y = M0 y) (ho : o.toNat % 4 = 0) (hx : x.toNat % 4 = 0)
    (sOQ : Sep o 40 (P + 0x52) feSquareCode.length) (sOR : Sep o 40 (P + 0xFFFFFCDE) feReduceCode.length)
    (sOG : Sep o 40 G 0xB0) (sXG : Sep x 40 G 0xB0) : FeSquareEnv M (P + 0x52) (G + 0xB0) o x := by
  have hGt := env.hGt
  have e1 : P + 0x52 + 0x26 = P + 0x78 := by rw [BitVec.add_assoc]; rfl
  have e2 : P + 0x52 + 0xFFFFFC8C = P + 0xFFFFFCDE := by rw [BitVec.add_assoc]; rfl
  have g : (G + BitVec.ofNat 32 0xB0).toNat = G.toNat + 0xB0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 0xB0 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega)]
  refine ⟨even_at P env.hP 0x52 (by decide), fpk_codeS env.sq env.sGQ fr, ?_, ?_,
    aligned_add env.hG (k := 0xB0) (by decide), by rw [show (G + 0xB0 : Word) = G + BitVec.ofNat 32 0xB0 from rfl, g]; omega,
    ho, hx, ?_, ?_, ?_, sOQ, by rw [e2]; exact sOR, by rw [edd_low]; exact sOG, by rw [edd_low]; exact sXG⟩
  · rw [e1]; exact fpk_codeS env.sqi env.sGI fr
  · rw [e2]; exact fpk_codeS env.red env.sGR fr
  · rw [edd_low]; exact sep_pre env.sGQ (by decide)
  · rw [edd_low, e1]; exact sep_pre env.sGI (by decide)
  · rw [edd_low, e2]; exact sep_pre env.sGR (by decide)

theorem St.own {M : Word → BitVec 8} {base : Word} {n : Machine} {off : Nat} {f : Fin 32 → Word}
    (s : St M base n off f) : St n.mem base n off (reg n) := ⟨s.pc, rfl, fun _ => rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **`pow2k`'s loop**, from 0x16 with `j` squarings done and `r` left: the
buffer at `G + 0xB4` holds `sqIter (j + r)` of the operand when it reaches
0x38. Each pass squares the buffer into the one at `G + 0xDC` and copies it
back with `memcpy`. Nothing changes outside the low 0x104 bytes of stack. -/
theorem fpk_loop {P G out xp : Word} {M0 : Word → BitVec 8} (env : FpkEnv M0 P G out xp) {X : List Nat}
    {r0 : Fin 32 → Word} :
    ∀ r j (n : Machine), r + 1 < 2 ^ 32 → St n.mem P n 0x16 (reg n) →
      (∀ y, Sep G 0x110 y 1 → n.mem y = M0 y) →
      reg n sp = G + 0xB0 → reg n (9 : Fin 32) = BitVec.ofNat 32 (r + 1) → (∀ q, pkKeep q = true → reg n q = r0 q) →
      feW n.mem (G + BitVec.ofNat 32 0xB4) = sqIter j X →
      ∃ n', Steps n n' ∧ St n'.mem P n' 0x38 (reg n') ∧ (∀ y, Sep G 0x104 y 1 → n'.mem y = n.mem y) ∧
        reg n' sp = G + 0xB0 ∧ (∀ q, pkKeep q = true → reg n' q = r0 q) ∧
        feW n'.mem (G + BitVec.ofNat 32 0xB4) = sqIter (j + r) X := by
  have hGt := env.hGt
  have alG : ∀ c, c % 4 = 0 → (G + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c hc => aligned_add env.hG hc
  have gB : ∀ (o : Word) (d : Nat), (0xB0 : Word) + o = BitVec.ofNat 32 d → G + 0xB0 + o = G + BitVec.ofNat 32 d :=
    fun o d h => edd_g G _ _ d h
  have sepS : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x110 → d + k ≤ 0x110 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun h h1 h2 => fpk_sepG h h1 h2
  have gw : ∀ {c : Nat}, c < 0x110 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun {c} h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]
  intro r
  induction r with
  | zero =>
    intro j n _ s fr hsp h9 hk hB
    have hc : CodeIn n.mem P fePow2kCode := fpk_codeS env.code env.sGC fr
    obtain ⟨n1, d1, u1⟩ := s.aluImm hc fpk_at_16 (off' := 0x18) (by decide)
    have k1 := u1.oldReg s.zero
    have s1 : reg n1 (9 : Fin 32) = 0 := by
      rw [u1.newReg (by decide)]; show reg n 9 + 0xFFFFFFFF = _; rw [h9]; rfl
    obtain ⟨n2, d2, u2⟩ := u1.self.taken hc 0x38 fpk_at_18 (by decide) (by
      simp only [branchTaken, s1, u1.self.zero]; decide)
    refine ⟨n2, .cons d1 (.single d2), u2.own, fun _ _ => by rw [u2.mem], by rw [u2.regs, k1 _ (by decide), hsp],
      fun q hq => by rw [u2.regs, k1 q (pk_ne hq (by decide)), hk q hq], by rw [Nat.add_zero, u2.mem]; exact hB⟩
  | succ r ih =>
    intro j n hr s fr hsp h9 hk hB
    have hc : CodeIn n.mem P fePow2kCode := fpk_codeS env.code env.sGC fr
    -- 0x16 `addi s1, s1, -1`, 0x18 `beqz s1`
    obtain ⟨n1, d1, u1⟩ := s.aluImm hc fpk_at_16 (off' := 0x18) (by decide)
    have k1 := u1.oldReg s.zero
    have s1 : reg n1 (9 : Fin 32) = BitVec.ofNat 32 (r + 1) := by
      rw [u1.newReg (by decide)]; show reg n 9 + 0xFFFFFFFF = _; rw [h9]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 from rfl]
      omega
    obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc 0x1A fpk_at_18 (by decide) (by
      simp only [branchTaken, s1, u1.self.zero]
      exact beq_toNat (by rw [BitVec.toNat_ofNat, zero_toNat]; omega))
    -- 0x1A `addi a0, sp, 0x2C`, 0x1C `addi a1, sp, 4`, and `square` into the buffer at `G + 0xDC`
    obtain ⟨n3, d3, u3⟩ := u2.self.aluImm hc fpk_at_1a (off' := 0x1C) (by decide)
    have k3 := u3.oldReg u2.self.zero
    obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hc fpk_at_1c (off' := 0x1E) (by decide)
    have k4 := u4.oldReg u3.self.zero
    have sp2 : reg n2 sp = G + 0xB0 := by rw [u2.regs, k1 _ (by decide), hsp]
    have sp4 : reg n4 sp = G + 0xB0 := by rw [k4 _ (by decide), k3 _ (by decide), sp2]
    obtain ⟨c1m, cc1m, pc1m, mem1m, regs1m⟩ := u4.self.callRa hc fpk_at_1e fpk_at_22 (cb := P + 0x52)
      (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x52 (by decide))
    have r1m := PEnv.reg1 regs1m u4.self.zero
    obtain ⟨c1, cc1, pc1, sp1c, kk1, out1, fr1⟩ := feSquare_correct c1m (retAddr := P + BitVec.ofNat 32 (0x1E + 8))
      (fpk_sqEnv env (by rw [mem1m]; exact fr) (o := G + BitVec.ofNat 32 0xDC) (x := G + BitVec.ofNat 32 0xB4)
        (alG _ (by decide)) (alG _ (by decide)) (env.sGQ.sub (by decide)) (env.sGR.sub (by decide))
        (fpk_sepG0 (by decide) (by decide)) (fpk_sepG0 (by decide) (by decide)))
      pc1m
      (by rw [r1m _ (by decide), k4 _ (by decide), u3.newReg (by decide)]; show reg n2 sp + 0x2C = _
          rw [sp2]; exact gB _ _ rfl)
      (by rw [r1m _ (by decide), u4.newReg (by decide)]; show reg n3 sp + 0x4 = _
          rw [k3 _ (by decide), sp2]; exact gB _ _ rfl)
      (by rw [regs1m]; try simp +decide only [upd_app, ↓reduceIte])
      (even_clear _ (even_at P env.hP (0x1E + 8) (by decide)))
      (by rw [r1m _ (by decide), sp4])
    rw [mem1m, edd_low] at fr1
    rw [mem1m] at out1
    have hsq : feW c1.mem (G + BitVec.ofNat 32 0xDC) = sqIter (j + 1) X := by
      rw [← feW_words, out1]; show sqL (feW n.mem (G + BitVec.ofNat 32 0xB4)) = _; rw [hB]; rfl
    have frc1 : ∀ y, Sep G 0x110 y 1 → c1.mem y = M0 y := fun y hy => by
      rw [fr1 y (sep_pre hy (by decide)) (hy.sub (c := 0xDC) (l := 40) (by decide)), fr y hy]
    have hc1 : CodeIn c1.mem P fePow2kCode := fpk_codeS env.code env.sGC frc1
    have w1 : St c1.mem P c1 0x26 (reg c1) := ⟨by rw [pc1]; try rfl, rfl, fun _ => rfl⟩
    -- 0x26..0x2E: `addi a0, sp, 4`, `addi a1, sp, 0x2C`, `li a2, 0x28`, and `memcpy` back
    obtain ⟨n5, d5, u5⟩ := w1.aluImm hc1 fpk_at_26 (off' := 0x28) (by decide)
    have k5 := u5.oldReg w1.zero
    obtain ⟨n6, d6, u6⟩ := u5.self.aluImm hc1 fpk_at_28 (off' := 0x2A) (by decide)
    have k6 := u6.oldReg u5.self.zero
    obtain ⟨n7, d7, u7⟩ := u6.self.aluImm hc1 fpk_at_2a (off' := 0x2E) (by decide)
    have k7 := u7.oldReg u6.self.zero
    have sp7 : reg n7 sp = G + 0xB0 := by rw [k7 _ (by decide), k6 _ (by decide), k5 _ (by decide), sp1c]
    obtain ⟨c2m, cc2m, pc2m, mem2m, regs2m⟩ := u7.self.callRa hc1 fpk_at_2e fpk_at_32 (cb := P + 0x62EA)
      (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x62EA (by decide))
    have r2m := PEnv.reg1 regs2m u7.self.zero
    have eA0 : G + 0xB0 + 0xFFFFFFF0 = G + BitVec.ofNat 32 0xA0 := gB _ _ rfl
    obtain ⟨c2, cc2, pc2, sp2c, _, mem2, K2⟩ := memcpy_correct c2m (P + 0x62EA) (P + BitVec.ofNat 32 (0x2E + 8))
      (G + BitVec.ofNat 32 0xB4) (G + BitVec.ofNat 32 0xDC) 40
      (fun i hi => by show c2m.mem _ = _; rw [mem2m]; exact fpk_codeS env.mcS env.sGM frc1 i hi)
      (even_at P env.hP 0x62EA (by decide)) pc2m
      (by rw [r2m _ (by decide), k7 _ (by decide), k6 _ (by decide), u5.newReg (by decide)]
          show reg c1 sp + 0x4 = _; rw [sp1c]; exact gB _ _ rfl)
      (by rw [r2m _ (by decide), k7 _ (by decide), u6.newReg (by decide)]
          show reg n5 sp + 0x2C = _; rw [k5 _ (by decide), sp1c]; exact gB _ _ rfl)
      (by rw [r2m _ (by decide), u7.newReg (by decide)]; show reg n6 0 + 0x28 = _; rw [u6.self.zero]; rfl)
      (by rw [regs2m]; try simp +decide only [upd_app, ↓reduceIte])
      (even_clear _ (even_at P env.hP (0x2E + 8) (by decide)))
      (by
        rw [r2m _ (by decide), sp7, eA0, mem2m, show P + 0x62EA + 8 = P + 0x62F2 by rw [BitVec.add_assoc]; rfl]
        exact { code := fpk_codeS env.mcB env.sGB frc1
                hDC := env.sGB.sub (c := 0xB4) (l := 40) (by decide)
                hFC := env.sGB.sub (c := 0xA0) (l := 16) (by decide)
                hdF := sepS (.inr (by decide)) (by decide) (by decide)
                hsF := sepS (.inr (by decide)) (by decide) (by decide)
                hsep := sepS (.inl (by decide)) (by decide) (by decide)
                hF := alG _ (by decide)
                hFw := by rw [gw (by decide)]; omega
                hdw := by rw [gw (by decide)]; omega
                hsw := by rw [gw (by decide)]; omega })
    rw [r2m _ (by decide), sp7, eA0, mem2m] at mem2
    have fr2 : ∀ y, Sep (G + BitVec.ofNat 32 0xA0) 16 y 1 → Sep (G + BitVec.ofNat 32 0xB4) 40 y 1 →
        c2.mem y = c1.mem y := fun y h1 h2 => by rw [mem2 y h1, copyBytes_sep h2 (Nat.le_refl _)]
    have hB2 : feW c2.mem (G + BitVec.ofNat 32 0xB4) = sqIter (j + 1) X := by
      rw [feW_frame (a := G + BitVec.ofNat 32 0xB4) fun i hi => load_frame mem2
        ((sepS (.inl (by decide)) (by decide) (by decide) : Sep (G + BitVec.ofNat 32 0xA0) 16 (G + BitVec.ofNat 32 0xB4) 40).subR
          (c := 4 * i) (l := 4) (by omega)), feW_copy, hsq]
    have frc2 : ∀ y, Sep G 0x110 y 1 → c2.mem y = M0 y := fun y hy => by
      rw [fr2 y (hy.sub (c := 0xA0) (l := 16) (by decide)) (hy.sub (c := 0xB4) (l := 40) (by decide)), frc1 y hy]
    have hc2 : CodeIn c2.mem P fePow2kCode := fpk_codeS env.code env.sGC frc2
    have w2 : St c2.mem P c2 0x36 (reg c2) := ⟨by rw [pc2]; try rfl, rfl, fun _ => rfl⟩
    -- 0x36 `j 0x16`
    obtain ⟨n8, d8, u8⟩ := w2.jump hc2 fpk_at_36 (off' := 0x16) (by decide)
      (pc_even (off := 0x36) (off' := 0x16) env.hP w2.pc (by decide) (by decide))
    have kc2 : ∀ q, (pkKeep q = true ∨ q = (9 : Fin 32)) → reg c2 q = reg n1 q := fun q hq => by
      have hm : pkKeep q = true ∨ q = (9 : Fin 32) → feMKeep q = true ∧ q ≠ ra ∧ q ≠ sp ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 := by
        revert q; decide
      obtain ⟨hf, hra', hs, h0, h1', h2'⟩ := hm hq
      rw [K2 q (fun e => by subst e; exact absurd hf (by decide)) h2' (fun e => by subst e; exact absurd hf (by decide))
        (fun e => by subst e; exact absurd hf (by decide)) (fun e => by subst e; exact absurd hf (by decide))
        (fun e => by subst e; exact absurd hf (by decide)) (fun e => by subst e; exact absurd hf (by decide))
        (fun e => by subst e; exact absurd hf (by decide)) (fun e => by subst e; exact absurd hf (by decide))
        (fun e => by subst e; exact absurd hf (by decide)) (fun e => by subst e; exact absurd hf (by decide))
        (fun e => by subst e; exact absurd hf (by decide)) (fun e => by subst e; exact absurd hf (by decide)) hs,
        r2m q hra', k7 q h2', k6 q h1', k5 q h0, kk1 q hf, r1m q hra', k4 q h1', k3 q h0, u2.regs]
    obtain ⟨n', c', u', fr', sp', k', hB'⟩ := ih (j + 1) n8 (by omega) u8.own (fun y hy => by rw [u8.mem]; exact frc2 y hy)
      (by rw [u8.regs, sp2c, r2m _ (by decide), sp7]) (by rw [u8.regs, kc2 _ (.inr rfl), s1])
      (fun q hq => by rw [u8.regs, kc2 q (.inl hq), k1 q (pk_ne hq (by decide)), hk q hq])
      (by rw [u8.mem]; exact hB2)
    refine ⟨n', .cons d1 (.cons d2 (.cons d3 (.cons d4 (cc1m.trans (cc1.trans (.cons d5 (.cons d6 (.cons d7
      (cc2m.trans (cc2.trans (.cons d8 c'))))))))))), u', fun y hy => ?_, sp', k', ?_⟩
    · rw [fr' y hy, u8.mem, fr2 y (hy.sub (c := 0xA0) (l := 16) (by decide)) (hy.sub (c := 0xB4) (l := 40) (by decide)),
        fr1 y (sep_pre hy (by decide)) (hy.sub (c := 0xDC) (l := 40) (by decide))]
    · rw [hB', show j + 1 + r = j + (r + 1) by omega]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
/-- **The compiled `FieldElement2625::pow2k`**, called with the result at
`out`, the operand's limbs at `xp`, and `k` with `0 < k < 2^32` (the Rust
source asserts `k > 0` in debug builds): it stores `sqIter k`, `square`
applied `k` times, of the operand's limbs. It returns with `sp` and every
register but `t0` through `t6` and `a0` through `a7` as they were, and
changes no memory outside its 0x110 bytes of stack and the result. -/
theorem fePow2k_correct (m : Machine) {P G out xp retAddr : Word} {k : Nat} (env : FpkEnv m.mem P G out xp)
    (hk0 : 0 < k) (hk1 : k < 2 ^ 32) (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp)
    (ha2 : reg m a2 = BitVec.ofNat 32 k) (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr)
    (hsp : reg m sp = G + 0x110) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = G + 0x110 ∧ (∀ q, feMKeep q = true → reg m' q = reg m q) ∧
      feW m'.mem out = sqIter k (feW m.mem xp) ∧
      ∀ x, Sep G 0x110 x 1 → Sep out 40 x 1 → m'.mem x = m.mem x := by
  have hGt := env.hGt
  have hc0 := env.code
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  have alG : ∀ c, c % 4 = 0 → (G + BitVec.ofNat 32 c).toNat % 4 = 0 := fun c hc => aligned_add env.hG hc
  have gB : ∀ (o : Word) (d : Nat), (0xB0 : Word) + o = BitVec.ofNat 32 d → G + 0xB0 + o = G + BitVec.ofNat 32 d :=
    fun o d h => edd_g G _ _ d h
  have sepS : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0x110 → d + k ≤ 0x110 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k := fun h h1 h2 => fpk_sepG h h1 h2
  have sep0 : ∀ {n d k : Nat}, n ≤ d → d + k ≤ 0x110 → Sep G n (G + BitVec.ofNat 32 d) k := fun {n d k} h1 h2 => by
    have := fpk_sepG (G := G) (c := 0) (n := n) (d := d) (k := k) (.inl (by omega)) (by omega) h2
    rwa [add_ofNat_zero] at this
  have gw : ∀ {c : Nat}, c < 0x110 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun {c} h => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]
  -- the prologue: the frame, and `ra`, `s0`, and `s1` saved at its top
  obtain ⟨m1, d1, u1⟩ := s0.aluImm hc0 fpk_at_0 (off' := 2) (by decide)
  have k1 := u1.oldReg hz
  have sp1 : reg m1 sp = G + 0xB0 := by
    rw [u1.newReg (by decide)]; show reg m sp + 0xFFFFFFA0 = _; rw [hsp, BitVec.add_assoc]; rfl
  obtain ⟨p0, dp0, up0⟩ := u1.self.swG hc0 fpk_at_2 (off' := 4) (by decide)
    (by rw [sp1, gB 0x5C 0x10C rfl]; exact alG _ (by decide)) (a := G + BitVec.ofNat 32 0x10C) (v := reg m ra)
    (by rw [sp1]; exact gB _ _ rfl) (k1 _ (by decide))
  obtain ⟨Q0, hQ0⟩ : ∃ M, memStore32 m.mem (G + BitVec.ofNat 32 0x10C) (reg m ra) = M := ⟨_, rfl⟩
  rw [hQ0] at up0
  have hq0 : CodeIn Q0 P fePow2kCode := by rw [← hQ0]; exact hc0.store32 (env.sGC.sub (by decide))
  obtain ⟨p1, dp1, up1⟩ := up0.swG hq0 fpk_at_4 (off' := 6) (by decide)
    (by rw [sp1, gB 0x58 0x108 rfl]; exact alG _ (by decide)) (a := G + BitVec.ofNat 32 0x108) (v := reg m (8 : Fin 32))
    (by rw [sp1]; exact gB _ _ rfl) (k1 _ (by decide))
  obtain ⟨Q1, hQ1⟩ : ∃ M, memStore32 Q0 (G + BitVec.ofNat 32 0x108) (reg m (8 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hQ1] at up1
  have hq1 : CodeIn Q1 P fePow2kCode := by rw [← hQ1]; exact hq0.store32 (env.sGC.sub (by decide))
  obtain ⟨p2, dp2, up2⟩ := up1.swG hq1 fpk_at_6 (off' := 8) (by decide)
    (by rw [sp1, gB 0x54 0x104 rfl]; exact alG _ (by decide)) (a := G + BitVec.ofNat 32 0x104) (v := reg m (9 : Fin 32))
    (by rw [sp1]; exact gB _ _ rfl) (k1 _ (by decide))
  obtain ⟨Q2, hQ2⟩ : ∃ M, memStore32 Q1 (G + BitVec.ofNat 32 0x104) (reg m (9 : Fin 32)) = M := ⟨_, rfl⟩
  rw [hQ2] at up2
  have fpro : ∀ y, Sep (G + BitVec.ofNat 32 0x104) 12 y 1 → Q2 y = m.mem y := fun y hy => by
    rw [← hQ2, memStore32_get_sep (sep_pre hy (by decide)), ← hQ1,
      memStore32_get_sep (by have := hy.sub (c := 4) (l := 4) (by decide); rwa [add_ofNat_assoc] at this), ← hQ0,
      memStore32_get_sep (by have := hy.sub (c := 8) (l := 4) (by decide); rwa [add_ofNat_assoc] at this)]
  have frQ : ∀ y, Sep G 0x110 y 1 → Q2 y = m.mem y := fun y hy => fpro y (hy.sub (by decide))
  have hq2 : CodeIn Q2 P fePow2kCode := fpk_codeS env.code env.sGC frQ
  -- 0x8 `mv s1, a2`, 0xA `mv s0, a0`, 0xC `addi a0, sp, 4`, and `square` into the buffer at `G + 0xB4`
  obtain ⟨n1, e1, v1⟩ := up2.alu hq2 fpk_at_8 (off' := 0xA) (by decide)
  have j1 := v1.oldReg up2.zero
  obtain ⟨n2, e2, v2⟩ := v1.self.alu hq2 fpk_at_a (off' := 0xC) (by decide)
  have j2 := v2.oldReg v1.self.zero
  obtain ⟨n3, e3, v3⟩ := v2.self.aluImm hq2 fpk_at_c (off' := 0xE) (by decide)
  have j3 := v3.oldReg v2.self.zero
  have r3 : ∀ q, q ≠ a0 → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ sp → reg n3 q = reg m q :=
    fun q h0 h8 h9 hs => by rw [j3 q h0, j2 q h8, j1 q h9, k1 q hs]
  have sp3 : reg n3 sp = G + 0xB0 := by rw [j3 _ (by decide), j2 _ (by decide), j1 _ (by decide), sp1]
  have s0_3 : reg n3 (8 : Fin 32) = out := by
    rw [j3 _ (by decide), v2.newReg (by decide)]; show reg n1 0 + reg n1 a0 = _
    rw [v1.self.zero, j1 _ (by decide), k1 _ (by decide), ha0]; exact BitVec.zero_add _
  have s1_3 : reg n3 (9 : Fin 32) = BitVec.ofNat 32 k := by
    rw [j3 _ (by decide), j2 _ (by decide), v1.newReg (by decide)]; show reg m1 0 + reg m1 a2 = _
    rw [u1.self.zero, k1 _ (by decide), ha2]; exact BitVec.zero_add _
  obtain ⟨c1m, cc1m, pc1m, mem1m, regs1m⟩ := v3.self.callRa hq2 fpk_at_e fpk_at_12 (cb := P + 0x52)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x52 (by decide))
  have r1m := PEnv.reg1 regs1m v3.self.zero
  obtain ⟨c1, cc1, pc1, sp1c, kk1, out1, fr1⟩ := feSquare_correct c1m (retAddr := P + BitVec.ofNat 32 (0xE + 8))
    (fpk_sqEnv env (by rw [mem1m]; exact frQ) (o := G + BitVec.ofNat 32 0xB4) (x := xp)
      (alG _ (by decide)) env.hx (env.sGQ.sub (by decide)) (env.sGR.sub (by decide))
      (fpk_sepG0 (by decide) (by decide)) (sepR0 env.sXG (by decide)))
    pc1m
    (by rw [r1m _ (by decide), v3.newReg (by decide)]; show reg n2 sp + 0x4 = _
        rw [j2 _ (by decide), j1 _ (by decide), sp1]; exact gB _ _ rfl)
    (by rw [r1m _ (by decide), r3 _ (by decide) (by decide) (by decide) (by decide), ha1])
    (by rw [regs1m]; try simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P env.hP (0xE + 8) (by decide)))
    (by rw [r1m _ (by decide), sp3])
  rw [mem1m, edd_low] at fr1
  rw [mem1m] at out1
  have frc1 : ∀ y, Sep G 0x110 y 1 → c1.mem y = m.mem y := fun y hy => by
    rw [fr1 y (sep_pre hy (by decide)) (hy.sub (c := 0xB4) (l := 40) (by decide)), frQ y hy]
  have hB1 : feW c1.mem (G + BitVec.ofNat 32 0xB4) = sqIter 1 (feW m.mem xp) := by
    rw [← feW_words, out1]; show sqL (feW Q2 xp) = _
    rw [feW_frame fun i hi => load_frame frQ (env.sXG.symm.subR (c := 4 * i) (l := 4) (by omega))]; rfl
  have w1 : St c1.mem P c1 0x16 (reg c1) := ⟨by rw [pc1]; try rfl, rfl, fun _ => rfl⟩
  -- the loop
  obtain ⟨nL, cL, uL, frL, spL, kL, hBL⟩ := fpk_loop env (X := feW m.mem xp) (r0 := reg n3) (k - 1) 1 c1
    (by omega) w1 frc1 sp1c (by rw [kk1 _ (by decide), r1m _ (by decide), s1_3, Nat.sub_add_cancel hk0])
    (fun q hq => by rw [kk1 q (pkKeep_sq q hq), r1m q (pk_ne hq (by decide))]) hB1
  rw [show 1 + (k - 1) = k by omega] at hBL
  have frSL : ∀ y, Sep G 0x110 y 1 → nL.mem y = m.mem y := fun y hy => by
    rw [frL y (sep_pre hy (by decide)), frc1 y hy]
  have hcL : CodeIn nL.mem P fePow2kCode := fpk_codeS env.code env.sGC frSL
  -- 0x38..0x40: `addi a1, sp, 4`, `li a2, 0x28`, `mv a0, s0`, and `memcpy` out
  obtain ⟨n4, e4, v4⟩ := uL.aluImm hcL fpk_at_38 (off' := 0x3A) (by decide)
  have j4 := v4.oldReg uL.zero
  obtain ⟨n5, e5, v5⟩ := v4.self.aluImm hcL fpk_at_3a (off' := 0x3E) (by decide)
  have j5 := v5.oldReg v4.self.zero
  obtain ⟨n6, e6, v6⟩ := v5.self.alu hcL fpk_at_3e (off' := 0x40) (by decide)
  have j6 := v6.oldReg v5.self.zero
  have sp6 : reg n6 sp = G + 0xB0 := by rw [j6 _ (by decide), j5 _ (by decide), j4 _ (by decide), spL]
  obtain ⟨c2m, cc2m, pc2m, mem2m, regs2m⟩ := v6.self.callRa hcL fpk_at_40 fpk_at_44 (cb := P + 0x62EA)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x62EA (by decide))
  have r2m := PEnv.reg1 regs2m v6.self.zero
  have eA0 : G + 0xB0 + 0xFFFFFFF0 = G + BitVec.ofNat 32 0xA0 := gB _ _ rfl
  obtain ⟨c2, cc2, pc2, sp2c, _, mem2, K2⟩ := memcpy_correct c2m (P + 0x62EA) (P + BitVec.ofNat 32 (0x40 + 8))
    out (G + BitVec.ofNat 32 0xB4) 40
    (fun i hi => by show c2m.mem _ = _; rw [mem2m]; exact fpk_codeS env.mcS env.sGM frSL i hi)
    (even_at P env.hP 0x62EA (by decide)) pc2m
    (by rw [r2m _ (by decide), v6.newReg (by decide)]; show reg n5 0 + reg n5 8 = _
        rw [v5.self.zero, j5 _ (by decide), j4 _ (by decide), kL _ (by decide), s0_3]; exact BitVec.zero_add _)
    (by rw [r2m _ (by decide), j6 _ (by decide), j5 _ (by decide), v4.newReg (by decide)]
        show reg nL sp + 0x4 = _; rw [spL]; exact gB _ _ rfl)
    (by rw [r2m _ (by decide), j6 _ (by decide), v5.newReg (by decide)]; show reg n4 0 + 0x28 = _
        rw [v4.self.zero]; rfl)
    (by rw [regs2m]; try simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P env.hP (0x40 + 8) (by decide)))
    (by
      rw [r2m _ (by decide), sp6, eA0, mem2m, show P + 0x62EA + 8 = P + 0x62F2 by rw [BitVec.add_assoc]; rfl]
      exact { code := fpk_codeS env.mcB env.sGB frSL
              hDC := env.sOB
              hFC := env.sGB.sub (c := 0xA0) (l := 16) (by decide)
              hdF := env.sOG.subR (c := 0xA0) (l := 16) (by decide)
              hsF := sepS (.inr (by decide)) (by decide) (by decide)
              hsep := env.sOG.subR (c := 0xB4) (l := 40) (by decide)
              hF := alG _ (by decide)
              hFw := by rw [gw (by decide)]; omega
              hdw := env.hot
              hsw := by rw [gw (by decide)]; omega })
  rw [r2m _ (by decide), sp6, eA0, mem2m] at mem2
  have fr2 : ∀ y, Sep (G + BitVec.ofNat 32 0xA0) 16 y 1 → Sep out 40 y 1 → c2.mem y = nL.mem y :=
    fun y h1 h2 => by rw [mem2 y h1, copyBytes_sep h2 (Nat.le_refl _)]
  have hOut : feW c2.mem out = sqIter k (feW m.mem xp) := by
    rw [feW_frame (a := out) fun i hi => load_frame mem2
      ((env.sOG.subR (c := 0xA0) (l := 16) (by decide)).symm.subR (c := 4 * i) (l := 4) (by omega)), feW_copy, hBL]
  have hc2 : CodeIn c2.mem P fePow2kCode := fun i hi => by
    rw [fr2 _ ((env.sGC.sub (c := 0xA0) (l := 16) (by decide)).subR (c := i) (l := 1) (by omega))
      (env.sOC.subR (c := i) (l := 1) (by omega))]; exact hcL i hi
  have w2 : St c2.mem P c2 0x48 (reg c2) := ⟨by rw [pc2]; try rfl, rfl, fun _ => rfl⟩
  -- the epilogue
  have slot : ∀ c, 0x104 ≤ c → c + 4 ≤ 0x110 → memLoad32 c2.mem (G + BitVec.ofNat 32 c) = memLoad32 Q2 (G + BitVec.ofNat 32 c) :=
    fun c h1 h2 => by
      rw [load_frame2 fr2 (sepS (.inl (by omega)) (by omega) (by omega)) (env.sOG.subR (c := c) (l := 4) (by omega)),
        load_frame frL (sep0 (by omega) (by omega)),
        load_frame2 fr1 (sep0 (by omega) (by omega)) (sepS (.inl (by omega)) (by omega) (by omega))]
  have sv0 : memLoad32 Q2 (G + BitVec.ofNat 32 0x10C) = reg m ra := by
    rw [← hQ2, memLoad32_store32_sep (sepS (.inl (by decide)) (by decide) (by decide)), ← hQ1,
      memLoad32_store32_sep (sepS (.inl (by decide)) (by decide) (by decide)), ← hQ0, memLoad32_store32_same]
  have sv1 : memLoad32 Q2 (G + BitVec.ofNat 32 0x108) = reg m (8 : Fin 32) := by
    rw [← hQ2, memLoad32_store32_sep (sepS (.inl (by decide)) (by decide) (by decide)), ← hQ1, memLoad32_store32_same]
  have sv2 : memLoad32 Q2 (G + BitVec.ofNat 32 0x104) = reg m (9 : Fin 32) := by rw [← hQ2, memLoad32_store32_same]
  have kc2 : ∀ q, pkKeep q = true → q ≠ (8 : Fin 32) → reg c2 q = reg m q := fun q hq h8 => by
    have hf : feMKeep q = true := by revert hq; revert q; decide
    rw [K2 q (fun e => by subst e; exact absurd hf (by decide)) (fun e => by subst e; exact absurd hf (by decide))
      (fun e => by subst e; exact absurd hf (by decide)) (fun e => by subst e; exact absurd hf (by decide))
      (fun e => by subst e; exact absurd hf (by decide)) (fun e => by subst e; exact absurd hf (by decide))
      (fun e => by subst e; exact absurd hf (by decide)) (fun e => by subst e; exact absurd hf (by decide))
      (fun e => by subst e; exact absurd hf (by decide)) (fun e => by subst e; exact absurd hf (by decide))
      (fun e => by subst e; exact absurd hf (by decide)) (fun e => by subst e; exact absurd hf (by decide))
      (fun e => by subst e; exact absurd hf (by decide)) (pk_ne hq (by decide)),
      r2m q (pk_ne hq (by decide)), j6 q (pk_ne hq (by decide)), j5 q (pk_ne hq (by decide)),
      j4 q (pk_ne hq (by decide)), kL q hq, r3 q (pk_ne hq (by decide)) h8 (pk_ne hq (by decide)) (pk_ne hq (by decide))]
  have spc2 : reg c2 sp = G + 0xB0 := by rw [sp2c, r2m _ (by decide), sp6]
  obtain ⟨f1, df1, uf1⟩ := w2.lwE hc2 fpk_at_48 (off' := 0x4A) (by decide)
    (by rw [spc2, gB 0x5C 0x10C rfl]; exact alG _ (by decide)) (v := reg m ra)
    (by rw [spc2, gB 0x5C 0x10C rfl, slot _ (by decide) (by decide), sv0])
  have g1 := uf1.oldReg w2.zero
  obtain ⟨f2, df2, uf2⟩ := uf1.self.lwE hc2 fpk_at_4a (off' := 0x4C) (by decide)
    (by rw [g1 _ (by decide), spc2, gB 0x58 0x108 rfl]; exact alG _ (by decide)) (v := reg m (8 : Fin 32))
    (by rw [g1 _ (by decide), spc2, gB 0x58 0x108 rfl, slot _ (by decide) (by decide), sv1])
  have g2 := uf2.oldReg uf1.self.zero
  obtain ⟨f3, df3, uf3⟩ := uf2.self.lwE hc2 fpk_at_4c (off' := 0x4E) (by decide)
    (by rw [g2 _ (by decide), g1 _ (by decide), spc2, gB 0x54 0x104 rfl]; exact alG _ (by decide))
    (v := reg m (9 : Fin 32))
    (by rw [g2 _ (by decide), g1 _ (by decide), spc2, gB 0x54 0x104 rfl, slot _ (by decide) (by decide), sv2])
  have g3 := uf3.oldReg uf2.self.zero
  obtain ⟨f4, df4, uf4⟩ := uf3.self.aluImm hc2 fpk_at_4e (off' := 0x50) (by decide)
  have g4 := uf4.oldReg uf3.self.zero
  obtain ⟨f5, df5, pcf5, memf5, regsf5⟩ := uf4.self.jalr hc2 fpk_at_50
  have ra4 : reg f4 ra = reg m ra := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), uf1.newReg (by decide)]
  have sp4 : reg f4 sp = G + 0x110 := by
    rw [uf4.newReg (by decide)]; show reg f3 sp + 0x60 = _
    rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide), spc2, BitVec.add_assoc]; rfl
  have fin : ∀ q, feMKeep q = true → q = sp ∨ q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨
      (pkKeep q = true ∧ q ≠ (8 : Fin 32)) := by decide
  have steps : Steps m f5 := .cons d1 (.cons dp0 (.cons dp1 (.cons dp2 (.cons e1 (.cons e2 (.cons e3 (cc1m.trans
    (cc1.trans (cL.trans (.cons e4 (.cons e5 (.cons e6 (cc2m.trans (cc2.trans (.cons df1 (.cons df2 (.cons df3
    (.cons df4 (.single df5)))))))))))))))))))
  refine ⟨f5, steps, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pcf5, ra4, add_lit_zero, hra, hret]
  · rw [regsf5, sp4]
  · intro q hq
    rw [regsf5]
    rcases fin q hq with h | h | h | h | ⟨h, h8⟩
    · subst h; rw [sp4, hsp]
    · subst h; exact ra4
    · subst h; rw [g4 _ (by decide), g3 _ (by decide), uf2.newReg (by decide)]
    · subst h; rw [g4 _ (by decide), uf3.newReg (by decide)]
    · rw [g4 q (pk_ne h (by decide)), g3 q (pk_ne h (by decide)), g2 q h8, g1 q (pk_ne h (by decide)), kc2 q h h8]
  · rw [memf5, hOut]
  · intro x hx ho
    rw [memf5, fr2 x (hx.sub (c := 0xA0) (l := 16) (by decide)) ho, frSL x hx]

end C3.RV32
