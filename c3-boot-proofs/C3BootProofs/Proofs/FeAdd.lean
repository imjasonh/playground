import C3BootProofs.Proofs.FlashRead
import C3BootProofs.Proofs.FeMul

/-!
# `<&FieldElement2625 as Add>::add`

`curve25519_dalek`'s field addition, as compiled: it copies the left
operand's ten limbs into its frame with `memcpy`, adds the right operand's
limbs into them in a loop (`u32` addition, which wraps in a release build),
and copies the sum out to the result with `memcpy`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem fad_at_0 : fetchRel feAddCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem fad_at_2 : fetchRel feAddCode 0x2 = some (.store .sw sp ra 0x3C, 2) := by decide
theorem fad_at_4 : fetchRel feAddCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x38, 2) := by decide
theorem fad_at_6 : fetchRel feAddCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x34, 2) := by decide
theorem fad_at_8 : fetchRel feAddCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x30, 2) := by decide
theorem fad_at_a : fetchRel feAddCode 0xA = some (.alu .add (9 : Fin 32) x0 a2, 2) := by decide
theorem fad_at_c : fetchRel feAddCode 0xC = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem fad_at_e : fetchRel feAddCode 0xE = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem fad_at_10 : fetchRel feAddCode 0x10 = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem fad_at_14 : fetchRel feAddCode 0x14 = some (.aluImm .add (8 : Fin 32) sp 0x8, 2) := by decide
theorem fad_at_16 : fetchRel feAddCode 0x16 = some (.auipc ra 0x6000, 4) := by decide
theorem fad_at_1a : fetchRel feAddCode 0x1A = some (.jalr ra ra 0xFFFFFD72, 4) := by decide
theorem fad_at_1e : fetchRel feAddCode 0x1E = some (.aluImm .add a0 x0 0xA, 2) := by decide
theorem fad_at_20 : fetchRel feAddCode 0x20 = some (.branch .beq a0 x0 0x12, 2) := by decide
theorem fad_at_22 : fetchRel feAddCode 0x22 = some (.load .lw a1 (9 : Fin 32) 0x0, 2) := by decide
theorem fad_at_24 : fetchRel feAddCode 0x24 = some (.load .lw a2 (8 : Fin 32) 0x0, 2) := by decide
theorem fad_at_26 : fetchRel feAddCode 0x26 = some (.alu .add a1 a1 a2, 2) := by decide
theorem fad_at_28 : fetchRel feAddCode 0x28 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x4, 2) := by decide
theorem fad_at_2a : fetchRel feAddCode 0x2A = some (.store .sw (8 : Fin 32) a1 0x0, 2) := by decide
theorem fad_at_2c : fetchRel feAddCode 0x2C = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem fad_at_2e : fetchRel feAddCode 0x2E = some (.aluImm .add a0 a0 0xFFFFFFFF, 2) := by decide
theorem fad_at_30 : fetchRel feAddCode 0x30 = some (.branch .bne a0 x0 0xFFFFFFF2, 2) := by decide
theorem fad_at_32 : fetchRel feAddCode 0x32 = some (.aluImm .add a1 sp 0x8, 2) := by decide
theorem fad_at_34 : fetchRel feAddCode 0x34 = some (.aluImm .add a2 x0 0x28, 4) := by decide
theorem fad_at_38 : fetchRel feAddCode 0x38 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem fad_at_3a : fetchRel feAddCode 0x3A = some (.auipc ra 0x6000, 4) := by decide
theorem fad_at_3e : fetchRel feAddCode 0x3E = some (.jalr ra ra 0xFFFFFD4E, 4) := by decide
theorem fad_at_42 : fetchRel feAddCode 0x42 = some (.load .lw ra sp 0x3C, 2) := by decide
theorem fad_at_44 : fetchRel feAddCode 0x44 = some (.load .lw (8 : Fin 32) sp 0x38, 2) := by decide
theorem fad_at_46 : fetchRel feAddCode 0x46 = some (.load .lw (9 : Fin 32) sp 0x34, 2) := by decide
theorem fad_at_48 : fetchRel feAddCode 0x48 = some (.load .lw (18 : Fin 32) sp 0x30, 2) := by decide
theorem fad_at_4a : fetchRel feAddCode 0x4A = some (.aluImm .add sp sp 0x40, 2) := by decide
theorem fad_at_4c : fetchRel feAddCode 0x4C = some (.jalr x0 ra 0x0, 2) := by decide
end

theorem memLoad32_eq {M M' : Word → BitVec 8} {a b : Word}
    (h : ∀ j, j < 4 → M' (a + BitVec.ofNat 32 j) = M (b + BitVec.ofNat 32 j)) :
    memLoad32 M' a = memLoad32 M b := by
  unfold memLoad32
  have h0 := h 0 (by decide)
  rw [add_ofNat_zero, add_ofNat_zero] at h0
  rw [h0, show a + 1 = a + BitVec.ofNat 32 1 from rfl, show b + 1 = b + BitVec.ofNat 32 1 from rfl, h 1 (by decide),
    show a + 2 = a + BitVec.ofNat 32 2 from rfl, show b + 2 = b + BitVec.ofNat 32 2 from rfl, h 2 (by decide),
    show a + 3 = a + BitVec.ofNat 32 3 from rfl, show b + 3 = b + BitVec.ofNat 32 3 from rfl, h 3 (by decide)]

theorem cb_in {M : Word → BitVec 8} {dst src : Word} {N i : Nat} (hi : i < N) (hN : N < 2 ^ 32) :
    copyBytes M dst src N (dst + BitVec.ofNat 32 i) = M (src + BitVec.ofNat 32 i) := by
  unfold copyBytes
  rw [add_sub_toNat dst (by omega), ite_eq_left hi, BitVec.add_comm dst, BitVec.add_sub_cancel]

/-- A word that `memcpy` copied, read back from the destination. -/
theorem cb_load {M : Word → BitVec 8} {dst src : Word} {N i : Nat} (h : 4 * i + 4 ≤ N) (hN : N < 2 ^ 32) :
    memLoad32 (copyBytes M dst src N) (dst + BitVec.ofNat 32 (4 * i)) =
      memLoad32 M (src + BitVec.ofNat 32 (4 * i)) :=
  memLoad32_eq fun j hj => by rw [add_ofNat_assoc, add_ofNat_assoc, cb_in (by omega) hN]

theorem sep_pre {B x : Word} {n k l : Nat} (h : Sep B n x l) (hk : k ≤ n) : Sep B k x l := by
  have := h.sub (c := 0) (l := k) (by omega); rwa [add_ofNat_zero] at this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The addition loop of `add`, from 0x22 with `j` limbs added: the frame's
buffer at `F + 8` holds the left operand's limbs (in `Mb`), and `y` the
right operand's. It reaches 0x32 with all ten limbs replaced by their sums,
and nothing else in memory changed. -/
theorem fad_loop {Mb : Word → BitVec 8} {P F y : Word} (hc : CodeIn Mb P feAddCode)
    (hF : F.toNat % 4 = 0) (hFt : F.toNat + 0x30 ≤ 2 ^ 32) (hy : y.toNat % 4 = 0)
    (sBC : Sep (F + 8) 40 P feAddCode.length) (sBY : Sep (F + 8) 40 y 40) :
    ∀ r j (n : Machine) (Mj : Word → BitVec 8), j + r = 10 → 0 < r → St Mj P n 0x22 (reg n) →
      reg n a0 = BitVec.ofNat 32 r → reg n (9 : Fin 32) = y + BitVec.ofNat 32 (4 * j) →
      reg n (8 : Fin 32) = F + 8 + BitVec.ofNat 32 (4 * j) →
      (∀ t, t < j → memLoad32 Mj (F + 8 + BitVec.ofNat 32 (4 * t)) =
        memLoad32 Mb (F + 8 + BitVec.ofNat 32 (4 * t)) + memLoad32 Mb (y + BitVec.ofNat 32 (4 * t))) →
      (∀ x, Sep (F + 8) (4 * j) x 1 → Mj x = Mb x) →
      ∃ n' M', Steps n n' ∧ St M' P n' 0x32 (reg n') ∧
        (∀ t, t < 10 → memLoad32 M' (F + 8 + BitVec.ofNat 32 (4 * t)) =
          memLoad32 Mb (F + 8 + BitVec.ofNat 32 (4 * t)) + memLoad32 Mb (y + BitVec.ofNat 32 (4 * t))) ∧
        (∀ x, Sep (F + 8) 40 x 1 → M' x = Mb x) ∧
        ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → reg n' q = reg n q := by
  intro r
  induction r with
  | zero => intro _ _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ r ih =>
    intro j n Mj hjr _ s ha0 hs1 hs0 hdone hrest
    have hcj : CodeIn Mj P feAddCode := fun i hi => by
      rw [hrest _ (sep_pre (sBC.subR (c := i) (l := 1) (by omega)) (by omega))]; exact hc i hi
    have hz := s.zero
    have hFn : (F + 8).toNat = F.toNat + 8 := by
      rw [BitVec.toNat_add, show (8 : Word).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
    have hB4 : (F + 8 + BitVec.ofNat 32 (4 * j)).toNat % 4 = 0 := aligned_add (by rw [hFn]; omega) (by omega)
    have hY4 : (y + BitVec.ofNat 32 (4 * j)).toNat % 4 = 0 := aligned_add hy (by omega)
    have sJ : ∀ {d k : Nat}, 4 * j ≤ d → d + k ≤ 40 → Sep (F + 8) (4 * j) (F + 8 + BitVec.ofNat 32 d) k :=
      fun {d k} h1 h2 => by
        have := sep_offsets (F + 8) (c := 0) (n := 4 * j) (d := d) (k := k) (.inl (by omega)) (by omega)
          (by omega)
        rwa [add_ofNat_zero] at this
    -- 0x22 `lw a1, 0(s1)` and 0x24 `lw a2, 0(s0)`
    obtain ⟨n1, d1, u1⟩ := s.lwE hcj fad_at_22 (off' := 0x24) (by decide)
      (by rw [hs1, add_lit_zero]; exact hY4) (v := memLoad32 Mb (y + BitVec.ofNat 32 (4 * j)))
      (by
        rw [hs1, add_lit_zero]
        exact load_frame hrest ((sep_pre sBY (k := 4 * j) (by omega)).subR (c := 4 * j) (l := 4) (by omega)))
    have k1 := u1.oldReg hz
    obtain ⟨n2, d2, u2⟩ := u1.self.lwE hcj fad_at_24 (off' := 0x26) (by decide)
      (by rw [k1 _ (by decide), hs0, add_lit_zero]; exact hB4) (v := memLoad32 Mb (F + 8 + BitVec.ofNat 32 (4 * j)))
      (by rw [k1 _ (by decide), hs0, add_lit_zero]; exact load_frame hrest (sJ (Nat.le_refl _) (by omega)))
    have k2 := u2.oldReg u1.self.zero
    -- 0x26 `add a1, a1, a2`, 0x28 `addi s1, s1, 4`, 0x2A `sw a1, 0(s0)`
    obtain ⟨n3, d3, u3⟩ := u2.self.alu hcj fad_at_26 (off' := 0x28) (by decide)
    have k3 := u3.oldReg u2.self.zero
    obtain ⟨V, hV⟩ : ∃ V, memLoad32 Mb (F + 8 + BitVec.ofNat 32 (4 * j)) +
        memLoad32 Mb (y + BitVec.ofNat 32 (4 * j)) = V := ⟨_, rfl⟩
    have a1_3 : reg n3 a1 = V := by
      rw [u3.newReg (by decide)]; show reg n2 a1 + reg n2 a2 = _
      rw [k2 _ (by decide), u1.newReg (by decide), u2.newReg (by decide), BitVec.add_comm, hV]
    obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hcj fad_at_28 (off' := 0x2A) (by decide)
    have k4 := u4.oldReg u3.self.zero
    obtain ⟨n5, d5, u5⟩ := u4.self.swG hcj fad_at_2a (off' := 0x2C) (by decide)
      (by rw [k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), hs0, add_lit_zero]; exact hB4)
      (a := F + 8 + BitVec.ofNat 32 (4 * j)) (v := V)
      (by rw [k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), hs0, add_lit_zero])
      (by rw [k4 _ (by decide), a1_3])
    obtain ⟨M5, hM5⟩ : ∃ M, memStore32 Mj (F + 8 + BitVec.ofNat 32 (4 * j)) V = M := ⟨_, rfl⟩
    rw [hM5] at u5
    have hS4 : ∀ x, Sep (F + 8) (4 * (j + 1)) x 1 → Sep (F + 8 + BitVec.ofNat 32 (4 * j)) 4 x 1 := fun x hx => by
      exact hx.sub (c := 4 * j) (l := 4) (by omega)
    have hrest5 : ∀ x, Sep (F + 8) (4 * (j + 1)) x 1 → M5 x = Mb x := fun x hx => by
      rw [← hM5, memStore32_get_sep (hS4 x hx), hrest x (sep_pre hx (by omega))]
    have hc5 : CodeIn M5 P feAddCode := fun i hi => by
      rw [hrest5 _ (sep_pre (sBC.subR (c := i) (l := 1) (by omega)) (by omega))]; exact hc i hi
    have hdone5 : ∀ t, t < j + 1 → memLoad32 M5 (F + 8 + BitVec.ofNat 32 (4 * t)) =
        memLoad32 Mb (F + 8 + BitVec.ofNat 32 (4 * t)) + memLoad32 Mb (y + BitVec.ofNat 32 (4 * t)) := by
      intro t ht
      by_cases htj : t = j
      · subst htj; rw [← hM5, memLoad32_store32_same, hV]
      · rw [← hM5, memLoad32_store32_sep (sep_offsets (F + 8) (c := 4 * j) (n := 4) (d := 4 * t) (k := 4)
          (.inr (by omega)) (by omega) (by omega)), hdone t (by omega)]
    -- 0x2C `addi s0, s0, 4`, 0x2E `addi a0, a0, -1`, 0x30 `bnez a0`
    obtain ⟨n6, d6, u6⟩ := u5.aluImm hc5 fad_at_2c (off' := 0x2E) (by decide)
    have k6 := u6.oldReg u5.zero
    obtain ⟨n7, d7, u7⟩ := u6.self.aluImm hc5 fad_at_2e (off' := 0x30) (by decide)
    have k7 := u7.oldReg u6.self.zero
    have a0_7 : reg n7 a0 = BitVec.ofNat 32 r := by
      rw [u7.newReg (by decide)]; show reg n6 a0 + 0xFFFFFFFF = _
      rw [k6 _ (by decide), k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), ha0]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 2 ^ 32 - 1 from rfl]
      omega
    have s1_7 : reg n7 (9 : Fin 32) = y + BitVec.ofNat 32 (4 * (j + 1)) := by
      rw [k7 _ (by decide), k6 _ (by decide), u4.newReg (by decide)]; show reg n3 (9 : Fin 32) + 0x4 = _
      rw [k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), hs1, show (0x4 : Word) = BitVec.ofNat 32 4 from rfl,
        add_ofNat_assoc, show 4 * j + 4 = 4 * (j + 1) by omega]
    have s0_7 : reg n7 (8 : Fin 32) = F + 8 + BitVec.ofNat 32 (4 * (j + 1)) := by
      rw [k7 _ (by decide), u6.newReg (by decide)]; show reg n4 (8 : Fin 32) + 0x4 = _
      rw [k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), hs0,
        show (0x4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc, show 4 * j + 4 = 4 * (j + 1) by omega]
    have keep7 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → reg n7 q = reg n q :=
      fun q h0 h1 h2 h8 h9 => by rw [k7 q h0, k6 q h8, k4 q h9, k3 q h1, k2 q h2, k1 q h1]
    by_cases hr : r = 0
    · subst hr
      obtain ⟨n8, d8, u8⟩ := u7.self.notTaken hc5 0x32 fad_at_30 (by decide) (by
        simp only [branchTaken, a0_7, u7.self.zero]; decide)
      refine ⟨n8, M5, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.single d8))))))),
        u8.self, fun t ht => hdone5 t (by omega), fun x hx => hrest5 x (by rwa [show 4 * (j + 1) = 40 by omega]),
        fun q h0 h1 h2 h8 h9 => by rw [u8.regs, keep7 q h0 h1 h2 h8 h9]⟩
    · obtain ⟨n8, d8, u8⟩ := u7.self.taken hc5 0x22 fad_at_30 (by decide) (by
        simp only [branchTaken, a0_7, u7.self.zero]
        exact bne_toNat (by rw [BitVec.toNat_ofNat, zero_toNat]; omega))
      obtain ⟨n', M', c', u', dn', fr', kk⟩ := ih (j + 1) n8 M5 (by omega) (by omega) u8.self
        (by rw [u8.regs, a0_7]) (by rw [u8.regs, s1_7]) (by rw [u8.regs, s0_7]) hdone5 hrest5
      exact ⟨n', M', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 c'))))))), u',
        dn', fr', fun q h0 h1 h2 h8 h9 => by rw [kk q h0 h1 h2 h8 h9, u8.regs, keep7 q h0 h1 h2 h8 h9]⟩

/-- Where `add` runs: its code at an even `P` and `memcpy`'s stub and body
where its calls reach them, `0x50` bytes of stack at `G` (its 0x40-byte frame
and `memcpy`'s 16 below), the result's 40 bytes at `out`, and the operands'
at `xp` and `yp`, `yp` 4-aligned. The result and the operands are apart from
the stack, and the result from the code; the operands may overlap the result,
since `add` reads them before it writes it. -/
structure FeAddEnv (M : Word → BitVec 8) (P G out xp yp : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P feAddCode
  mcS : CodeIn M (P + 0x5D88) memcpyStubCode
  mcB : CodeIn M (P + 0x5D90) memcpyBodyCode
  hG : G.toNat % 4 = 0
  hGt : G.toNat + 0x50 ≤ 2 ^ 32
  hy : yp.toNat % 4 = 0
  hout : out.toNat + 40 < 2 ^ 32
  hx : xp.toNat + 40 < 2 ^ 32
  sGC : Sep G 0x50 P feAddCode.length
  sGS : Sep G 0x50 (P + 0x5D88) memcpyStubCode.length
  sGB : Sep G 0x50 (P + 0x5D90) memcpyBodyCode.length
  sOC : Sep out 40 P feAddCode.length
  sOB : Sep out 40 (P + 0x5D90) memcpyBodyCode.length
  sOG : Sep out 40 G 0x50
  sXG : Sep xp 40 G 0x50
  sYG : Sep yp 40 G 0x50

theorem fad_mc (P : Word) : P + 0x5D88 + 8 = P + 0x5D90 := by rw [BitVec.add_assoc]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `<&FieldElement2625 as Add>::add`**, called with the result
at `out` and the operands' ten limbs at `xp` and `yp`: each limb of the result
is the sum of the operands' limbs modulo 2^32, as the Rust source's `+=` on
`u32` in a release build. It returns with `sp` and every register but `t0`
through `t6` and `a0` through `a7` as they were, and changes no memory outside
its 0x50 bytes of stack and the result. -/
theorem feAdd_correct (m : Machine) {P G out xp yp retAddr : Word} (env : FeAddEnv m.mem P G out xp yp)
    (hpc : m.pc = P) (ha0 : reg m a0 = out) (ha1 : reg m a1 = xp) (ha2 : reg m a2 = yp)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = G + 0x50) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = G + 0x50 ∧ (∀ q, feMKeep q = true → reg m' q = reg m q) ∧
      (∀ i, i < 10 → memLoad32 m'.mem (out + BitVec.ofNat 32 (4 * i)) =
        memLoad32 m.mem (xp + BitVec.ofNat 32 (4 * i)) + memLoad32 m.mem (yp + BitVec.ofNat 32 (4 * i))) ∧
      ∀ x, Sep G 0x50 x 1 → Sep out 40 x 1 → m'.mem x = m.mem x := by
  obtain ⟨F, hF⟩ : ∃ F, G + 0x10 = F := ⟨_, rfl⟩
  have hGt := env.hGt
  have hFn : F.toNat = G.toNat + 0x10 := by
    rw [← hF, BitVec.toNat_add, show (0x10 : Word).toNat = 0x10 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hFa : F.toNat % 4 = 0 := by rw [hFn]; have := env.hG; omega
  have fG : ∀ c, F + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x10 + c) := fun c => by
    rw [← hF, show (0x10 : Word) = BitVec.ofNat 32 0x10 from rfl, add_ofNat_assoc]
  have hFsp : G + 0x50 + 0xFFFFFFC0 = F := by rw [← hF, BitVec.add_assoc]; rfl
  have hspF : F + 0x40 = G + 0x50 := by rw [← hF, BitVec.add_assoc]; rfl
  have hGF : F + 0xFFFFFFF0 = G := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero G
  have e8 : F + 8 = G + BitVec.ofNat 32 0x18 := fG 8
  have hF8 : (F + 8).toNat = F.toNat + 8 := by
    rw [BitVec.toNat_add, show (8 : Word).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
  have inF : ∀ x, Sep G 0x50 x 1 → Sep F 0x40 x 1 := fun x hx => by
    rw [← hF]; exact hx.sub (c := 0x10) (l := 0x40) (by decide)
  have in8 : ∀ x, Sep G 0x50 x 1 → Sep (F + 8) 40 x 1 := fun x hx => by
    rw [e8]; exact hx.sub (c := 0x18) (l := 40) (by decide)
  have in0 : ∀ x, Sep G 0x50 x 1 → Sep G 16 x 1 := fun x hx => sep_pre hx (by decide)
  have sFC : Sep F 0x40 P feAddCode.length := by rw [← hF]; exact env.sGC.sub (c := 0x10) (l := 0x40) (by decide)
  have sFS : Sep F 0x40 (P + 0x5D88) memcpyStubCode.length := by
    rw [← hF]; exact env.sGS.sub (c := 0x10) (l := 0x40) (by decide)
  have sFB : Sep F 0x40 (P + 0x5D90) memcpyBodyCode.length := by
    rw [← hF]; exact env.sGB.sub (c := 0x10) (l := 0x40) (by decide)
  have s8G : Sep (F + 8) 40 G 16 := by
    rw [e8]; have := sep_offsets G (c := 0x18) (n := 40) (d := 0) (k := 16) (.inr (by decide)) (by decide) (by decide)
    rwa [add_ofNat_zero] at this
  -- the prologue: the frame, and `ra`, `s0`, `s1`, and `s2` saved at its top
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code fad_at_0 (off' := 2) (by decide)
  have k1 := u1.oldReg hz
  have sp1 : reg m1 sp = F := by rw [u1.newReg (by decide)]; show reg m sp + 0xFFFFFFC0 = _; rw [hsp, hFsp]
  obtain ⟨p0, dp0, up0⟩ := u1.self.swG env.code fad_at_2 (off' := 4) (by decide)
    (by rw [sp1]; exact fr_al' hFa (by decide)) (a := F + 0x3C) (v := reg m ra) (by rw [sp1]) (k1 _ (by decide))
  obtain ⟨P0, hP0⟩ : ∃ M', memStore32 m.mem (F + 0x3C) (reg m ra) = M' := ⟨_, rfl⟩
  rw [hP0] at up0
  have hcp0 : CodeIn P0 P feAddCode := by rw [← hP0]; exact env.code.store32 (frm_sep' sFC (by decide))
  obtain ⟨p1, dp1, up1⟩ := up0.swG hcp0 fad_at_4 (off' := 6) (by decide)
    (by rw [sp1]; exact fr_al' hFa (by decide)) (a := F + 0x38) (v := reg m (8 : Fin 32)) (by rw [sp1])
    (k1 _ (by decide))
  obtain ⟨P1, hP1⟩ : ∃ M', memStore32 P0 (F + 0x38) (reg m (8 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP1] at up1
  have hcp1 : CodeIn P1 P feAddCode := by rw [← hP1]; exact hcp0.store32 (frm_sep' sFC (by decide))
  obtain ⟨p2, dp2, up2⟩ := up1.swG hcp1 fad_at_6 (off' := 8) (by decide)
    (by rw [sp1]; exact fr_al' hFa (by decide)) (a := F + 0x34) (v := reg m (9 : Fin 32)) (by rw [sp1])
    (k1 _ (by decide))
  obtain ⟨P2, hP2⟩ : ∃ M', memStore32 P1 (F + 0x34) (reg m (9 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP2] at up2
  have hcp2 : CodeIn P2 P feAddCode := by rw [← hP2]; exact hcp1.store32 (frm_sep' sFC (by decide))
  obtain ⟨p3, dp3, up3⟩ := up2.swG hcp2 fad_at_8 (off' := 0xA) (by decide)
    (by rw [sp1]; exact fr_al' hFa (by decide)) (a := F + 0x30) (v := reg m (18 : Fin 32)) (by rw [sp1])
    (k1 _ (by decide))
  obtain ⟨P3, hP3⟩ : ∃ M', memStore32 P2 (F + 0x30) (reg m (18 : Fin 32)) = M' := ⟨_, rfl⟩
  rw [hP3] at up3
  have hcp3 : CodeIn P3 P feAddCode := by rw [← hP3]; exact hcp2.store32 (frm_sep' sFC (by decide))
  have fpro : ∀ x, Sep F 0x40 x 1 → P3 x = m.mem x := fun x hx => by
    rw [← hP3, memStore32_get_sep (frm_sep' hx (by decide)), ← hP2, memStore32_get_sep (frm_sep' hx (by decide)),
      ← hP1, memStore32_get_sep (frm_sep' hx (by decide)), ← hP0, memStore32_get_sep (frm_sep' hx (by decide))]
  have sv3C : memLoad32 P3 (F + 0x3C) = reg m ra := by
    rw [← hP3, memLoad32_store32_sep (show Sep (F + 0x30) 4 (F + 0x3C) 4 from sep_offsets F (by decide) (by decide)
      (by decide)), ← hP2, memLoad32_store32_sep (show Sep (F + 0x34) 4 (F + 0x3C) 4 from sep_offsets F (by decide)
      (by decide) (by decide)), ← hP1, memLoad32_store32_sep (show Sep (F + 0x38) 4 (F + 0x3C) 4 from
      sep_offsets F (by decide) (by decide) (by decide)), ← hP0, memLoad32_store32_same]
  have sv38 : memLoad32 P3 (F + 0x38) = reg m (8 : Fin 32) := by
    rw [← hP3, memLoad32_store32_sep (show Sep (F + 0x30) 4 (F + 0x38) 4 from sep_offsets F (by decide) (by decide)
      (by decide)), ← hP2, memLoad32_store32_sep (show Sep (F + 0x34) 4 (F + 0x38) 4 from sep_offsets F (by decide)
      (by decide) (by decide)), ← hP1, memLoad32_store32_same]
  have sv34 : memLoad32 P3 (F + 0x34) = reg m (9 : Fin 32) := by
    rw [← hP3, memLoad32_store32_sep (show Sep (F + 0x30) 4 (F + 0x34) 4 from sep_offsets F (by decide) (by decide)
      (by decide)), ← hP2, memLoad32_store32_same]
  have sv30 : memLoad32 P3 (F + 0x30) = reg m (18 : Fin 32) := by rw [← hP3, memLoad32_store32_same]
  have cOf : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep F 0x40 b code.length → CodeIn P3 b code :=
    fun hc hs i hi => by rw [fpro _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  -- 0xA..0x14: the operands and the buffer
  obtain ⟨n1, e1, v1⟩ := up3.alu hcp3 fad_at_a (off' := 0xC) (by decide)
  have j1 := v1.oldReg up3.zero
  obtain ⟨n2, e2, v2⟩ := v1.self.alu hcp3 fad_at_c (off' := 0xE) (by decide)
  have j2 := v2.oldReg v1.self.zero
  obtain ⟨n3, e3, v3⟩ := v2.self.aluImm hcp3 fad_at_e (off' := 0x10) (by decide)
  have j3 := v3.oldReg v2.self.zero
  obtain ⟨n4, e4, v4⟩ := v3.self.aluImm hcp3 fad_at_10 (off' := 0x14) (by decide)
  have j4 := v4.oldReg v3.self.zero
  obtain ⟨n5, e5, v5⟩ := v4.self.aluImm hcp3 fad_at_14 (off' := 0x16) (by decide)
  have j5 := v5.oldReg v4.self.zero
  have x1 : reg n1 (9 : Fin 32) = yp := by
    rw [v1.newReg (by decide)]; show reg m1 0 + reg m1 a2 = _
    rw [up3.zero, k1 _ (by decide), ha2]; exact BitVec.zero_add _
  have x2 : reg n2 (18 : Fin 32) = out := by
    rw [v2.newReg (by decide)]; show reg n1 0 + reg n1 a0 = _
    rw [v1.self.zero, j1 _ (by decide), k1 _ (by decide), ha0]; exact BitVec.zero_add _
  have x3 : reg n3 a0 = F + 8 := by
    rw [v3.newReg (by decide)]; show reg n2 sp + 0x8 = _; rw [j2 _ (by decide), j1 _ (by decide), sp1]
  have x4 : reg n4 a2 = 0x28 := by
    rw [v4.newReg (by decide)]; show reg n3 0 + 0x28 = _; rw [v3.self.zero]; rfl
  have x5 : reg n5 (8 : Fin 32) = F + 8 := by
    rw [v5.newReg (by decide)]; show reg n4 sp + 0x8 = _
    rw [j4 _ (by decide), j3 _ (by decide), j2 _ (by decide), j1 _ (by decide), sp1]
  -- 0x16: `memcpy` copies the left operand into the buffer
  obtain ⟨n6, c6, pc6, mem6, regs6⟩ := v5.self.callRa hcp3 fad_at_16 fad_at_1a (cb := P + 0x5D88)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x5D88 (by decide))
  have r6 := PEnv.reg1 regs6 v5.self.zero
  have sp6 : reg n6 sp = F := by
    rw [r6 _ (by decide), j5 _ (by decide), j4 _ (by decide), j3 _ (by decide), j2 _ (by decide), j1 _ (by decide), sp1]
  obtain ⟨n7, c7, pc7, sp7, a07, mem7, K7⟩ := memcpy_correct n6 (P + 0x5D88) (P + BitVec.ofNat 32 (0x16 + 8))
    (F + 8) xp 40 (fun i hi => by show n6.mem _ = _; rw [mem6]; exact cOf env.mcS sFS i hi)
    (even_at P env.hP 0x5D88 (by decide)) pc6 (by rw [r6 _ (by decide), j5 _ (by decide), j4 _ (by decide), x3])
    (by rw [r6 _ (by decide), j5 _ (by decide), j4 _ (by decide), j3 _ (by decide), j2 _ (by decide),
      j1 _ (by decide), k1 _ (by decide), ha1])
    (by rw [r6 _ (by decide), j5 _ (by decide), x4]; rfl)
    (by rw [regs6]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at P env.hP (0x16 + 8) (by decide)))
    (by
      rw [mem6, sp6, hGF, fad_mc]
      exact { code := cOf env.mcB sFB
              hDC := by rw [e8]; exact env.sGB.sub (c := 0x18) (l := 40) (by decide)
              hFC := by have := env.sGB.sub (c := 0) (l := 16) (by decide); rwa [add_ofNat_zero] at this
              hdF := s8G
              hsF := by have := env.sXG.subR (c := 0) (l := 16) (by decide); rwa [add_ofNat_zero] at this
              hsep := by rw [e8]; exact (env.sXG.subR (c := 0x18) (l := 40) (by decide)).symm
              hF := env.hG
              hFw := by omega
              hdw := by rw [hF8]; omega
              hsw := env.hx })
  rw [mem6, sp6, hGF] at mem7
  rw [sp6] at sp7
  obtain ⟨Mb, hMb⟩ : ∃ M, n7.mem = M := ⟨_, rfl⟩
  rw [hMb] at mem7
  have MbG : ∀ x, Sep G 0x50 x 1 → Mb x = m.mem x := fun x hx => by
    rw [mem7 x (in0 x hx), copyBytes_sep (in8 x hx) (Nat.le_refl _), fpro x (inF x hx)]
  have hcb : CodeIn Mb P feAddCode := fun i hi => by
    rw [MbG _ (env.sGC.subR (c := i) (l := 1) (by omega))]; exact env.code i hi
  have Xw : ∀ i, i < 10 → memLoad32 Mb (F + 8 + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (xp + BitVec.ofNat 32 (4 * i)) :=
    fun i hi => by
      rw [load_frame mem7 (by
          rw [e8, add_ofNat_assoc]
          have := sep_offsets G (c := 0) (n := 16) (d := 0x18 + 4 * i) (k := 4) (.inl (by omega)) (by decide) (by omega)
          rwa [add_ofNat_zero] at this),
        cb_load (by omega) (by decide),
        load_frame fpro (by
          rw [← hF]; exact (env.sXG.subR (c := 0x10) (l := 0x40) (by decide)).symm.subR (c := 4 * i) (l := 4)
            (by omega))]
  have Yw : ∀ i, i < 10 → memLoad32 Mb (yp + BitVec.ofNat 32 (4 * i)) = memLoad32 m.mem (yp + BitVec.ofNat 32 (4 * i)) :=
    fun i hi => load_frame MbG (env.sYG.symm.subR (c := 4 * i) (l := 4) (by omega))
  -- 0x1E `li a0, 10`, 0x20 `beqz a0`, and the loop
  have w7 : St Mb P n7 0x1E (reg n7) := ⟨by rw [pc7], hMb, fun _ => rfl⟩
  obtain ⟨n8, e8', v8⟩ := w7.aluImm hcb fad_at_1e (off' := 0x20) (by decide)
  have j8 := v8.oldReg w7.zero
  have a0_8 : reg n8 a0 = BitVec.ofNat 32 10 := by
    rw [v8.newReg (by decide)]; show reg n7 0 + 0xA = _; rw [w7.zero]; rfl
  obtain ⟨n9, e9, v9⟩ := v8.self.notTaken hcb 0x22 fad_at_20 (by decide) (by
    simp only [branchTaken, a0_8, v8.self.zero]; decide)
  have back9 : ∀ q, q ≠ a0 → q ≠ ra → q ≠ sp → q.val ∉ [11, 12, 13, 14, 15, 16, 17, 5, 6, 7, 28, 29, 30, 31] →
      reg n9 q = reg n5 q := fun q h0 h1 h2 h3 => by
    rw [v9.regs, j8 q h0, K7 q (fun e => by subst e; exact h3 (by decide)) (fun e => by subst e; exact h3 (by decide))
      (fun e => by subst e; exact h3 (by decide)) (fun e => by subst e; exact h3 (by decide))
      (fun e => by subst e; exact h3 (by decide)) (fun e => by subst e; exact h3 (by decide))
      (fun e => by subst e; exact h3 (by decide)) (fun e => by subst e; exact h3 (by decide))
      (fun e => by subst e; exact h3 (by decide)) (fun e => by subst e; exact h3 (by decide))
      (fun e => by subst e; exact h3 (by decide)) (fun e => by subst e; exact h3 (by decide))
      (fun e => by subst e; exact h3 (by decide)) h2, r6 q h1]
  obtain ⟨nL, ML, cL, uL, dnL, frL, kL⟩ := fad_loop (Mb := Mb) hcb hFa (by omega) env.hy
    (by rw [e8]; exact env.sGC.sub (c := 0x18) (l := 40) (by decide))
    (by rw [e8]; exact (env.sYG.subR (c := 0x18) (l := 40) (by decide)).symm) 10 0 n9 Mb (by omega) (by omega)
    v9.self (by rw [v9.regs, a0_8])
    (by rw [back9 _ (by decide) (by decide) (by decide) (by decide), j5 _ (by decide), j4 _ (by decide),
      j3 _ (by decide), j2 _ (by decide), x1, add_ofNat_zero])
    (by rw [back9 _ (by decide) (by decide) (by decide) (by decide), x5, add_ofNat_zero])
    (fun t ht => absurd ht (Nat.not_lt_zero _)) (fun _ _ => rfl)
  have hcL : CodeIn ML P feAddCode := fun i hi => by
    rw [frL _ (in8 _ (env.sGC.subR (c := i) (l := 1) (by omega)))]; exact hcb i hi
  have sp_L : reg nL sp = F := by
    rw [kL _ (by decide) (by decide) (by decide) (by decide) (by decide), v9.regs, j8 _ (by decide), sp7]
  have s2_L : reg nL (18 : Fin 32) = out := by
    rw [kL _ (by decide) (by decide) (by decide) (by decide) (by decide),
      back9 _ (by decide) (by decide) (by decide) (by decide), j5 _ (by decide), j4 _ (by decide), j3 _ (by decide), x2]
  -- 0x32..0x3A: `memcpy` copies the sums out to the result
  obtain ⟨nA, eA, vA⟩ := uL.aluImm hcL fad_at_32 (off' := 0x34) (by decide)
  have jA := vA.oldReg uL.zero
  obtain ⟨nB, eB, vB⟩ := vA.self.aluImm hcL fad_at_34 (off' := 0x38) (by decide)
  have jB := vB.oldReg vA.self.zero
  obtain ⟨nC, eC, vC⟩ := vB.self.alu hcL fad_at_38 (off' := 0x3A) (by decide)
  have jC := vC.oldReg vB.self.zero
  have a1_C : reg nC a1 = F + 8 := by
    rw [jC _ (by decide), jB _ (by decide), vA.newReg (by decide)]; show reg nL sp + 0x8 = _; rw [sp_L]
  have a2_C : reg nC a2 = 0x28 := by
    rw [jC _ (by decide), vB.newReg (by decide)]; show reg nA 0 + 0x28 = _; rw [vA.self.zero]; rfl
  have a0_C : reg nC a0 = out := by
    rw [vC.newReg (by decide)]; show reg nB 0 + reg nB (18 : Fin 32) = _
    rw [vB.self.zero, jB _ (by decide), jA _ (by decide), s2_L]; exact BitVec.zero_add _
  have sp_C : reg nC sp = F := by rw [jC _ (by decide), jB _ (by decide), jA _ (by decide), sp_L]
  obtain ⟨nD, cD, pcD, memD, regsD⟩ := vC.self.callRa hcL fad_at_3a fad_at_3e (cb := P + 0x5D88)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x5D88 (by decide))
  have rD := PEnv.reg1 regsD vC.self.zero
  have spD : reg nD sp = F := by rw [rD _ (by decide), sp_C]
  have MLG : ∀ x, Sep G 0x50 x 1 → ML x = m.mem x := fun x hx => by rw [frL x (in8 x hx), MbG x hx]
  have cOfL : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → Sep G 0x50 b code.length → CodeIn ML b code :=
    fun hc hs i hi => by rw [MLG _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  obtain ⟨nE, cE, pcE, spE, a0E, memE, KE⟩ := memcpy_correct nD (P + 0x5D88) (P + BitVec.ofNat 32 (0x3A + 8))
    out (F + 8) 40 (fun i hi => by show nD.mem _ = _; rw [memD]; exact cOfL env.mcS env.sGS i hi)
    (even_at P env.hP 0x5D88 (by decide)) pcD (by rw [rD _ (by decide), a0_C]) (by rw [rD _ (by decide), a1_C])
    (by rw [rD _ (by decide), a2_C]; rfl) (by rw [regsD]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at P env.hP (0x3A + 8) (by decide)))
    (by
      rw [memD, spD, hGF, fad_mc]
      exact { code := cOfL env.mcB env.sGB
              hDC := env.sOB
              hFC := by have := env.sGB.sub (c := 0) (l := 16) (by decide); rwa [add_ofNat_zero] at this
              hdF := by have := env.sOG.subR (c := 0) (l := 16) (by decide); rwa [add_ofNat_zero] at this
              hsF := s8G
              hsep := by rw [e8]; exact env.sOG.subR (c := 0x18) (l := 40) (by decide)
              hF := env.hG
              hFw := by omega
              hdw := env.hout
              hsw := by rw [hF8]; omega })
  rw [memD, spD, hGF] at memE
  rw [spD] at spE
  obtain ⟨Mf, hMf⟩ : ∃ M, nE.mem = M := ⟨_, rfl⟩
  rw [hMf] at memE
  have MfG : ∀ x, Sep G 0x50 x 1 → Sep out 40 x 1 → Mf x = m.mem x := fun x hx ho => by
    rw [memE x (in0 x hx), copyBytes_sep ho (Nat.le_refl _), MLG x hx]
  have hcE : CodeIn Mf P feAddCode := fun i hi => by
    rw [MfG _ (env.sGC.subR (c := i) (l := 1) (by omega)) (env.sOC.subR (c := i) (l := 1) (by omega))]
    exact env.code i hi
  have rdSlot : ∀ o, 0x30 ≤ o → o + 4 ≤ 0x40 →
      memLoad32 Mf (F + BitVec.ofNat 32 o) = memLoad32 P3 (F + BitVec.ofNat 32 o) := fun o h1 h2 => by
    have hG16 : Sep G 16 (F + BitVec.ofNat 32 o) 4 := by
      rw [fG]
      have := sep_offsets G (c := 0) (n := 16) (d := 0x10 + o) (k := 4) (.inl (by omega)) (by decide) (by omega)
      rwa [add_ofNat_zero] at this
    have hO : Sep out 40 (F + BitVec.ofNat 32 o) 4 := by rw [fG]; exact env.sOG.subR (c := 0x10 + o) (l := 4) (by omega)
    have h8 : Sep (F + 8) 40 (F + BitVec.ofNat 32 o) 4 := by
      rw [e8, fG]; exact sep_offsets G (.inl (by omega)) (by decide) (by omega)
    rw [load_frame memE hG16, load_frame (fun a ha => copyBytes_sep ha (Nat.le_refl _)) hO, load_frame frL h8,
      load_frame mem7 hG16, load_frame (fun a ha => copyBytes_sep ha (Nat.le_refl _)) h8]
  -- the epilogue
  have wE : St Mf P nE 0x42 (reg nE) := ⟨by rw [pcE], hMf, fun _ => rfl⟩
  obtain ⟨g0, dg0, ug0⟩ := wE.lwE hcE fad_at_42 (off' := 0x44) (by decide)
    (by rw [spE]; exact fr_al' hFa (by decide)) (v := reg m ra)
    (by rw [spE]; exact (rdSlot 0x3C (by decide) (by decide)).trans sv3C)
  have kg0 := ug0.oldReg wE.zero
  obtain ⟨g1, dg1, ug1⟩ := ug0.self.lwE hcE fad_at_44 (off' := 0x46) (by decide)
    (by rw [kg0 _ (by decide), spE]; exact fr_al' hFa (by decide)) (v := reg m (8 : Fin 32))
    (by rw [kg0 _ (by decide), spE]; exact (rdSlot 0x38 (by decide) (by decide)).trans sv38)
  have kg1 := ug1.oldReg ug0.self.zero
  obtain ⟨g2, dg2, ug2⟩ := ug1.self.lwE hcE fad_at_46 (off' := 0x48) (by decide)
    (by rw [kg1 _ (by decide), kg0 _ (by decide), spE]; exact fr_al' hFa (by decide)) (v := reg m (9 : Fin 32))
    (by rw [kg1 _ (by decide), kg0 _ (by decide), spE]; exact (rdSlot 0x34 (by decide) (by decide)).trans sv34)
  have kg2 := ug2.oldReg ug1.self.zero
  obtain ⟨g3, dg3, ug3⟩ := ug2.self.lwE hcE fad_at_48 (off' := 0x4A) (by decide)
    (by rw [kg2 _ (by decide), kg1 _ (by decide), kg0 _ (by decide), spE]; exact fr_al' hFa (by decide))
    (v := reg m (18 : Fin 32))
    (by
      rw [kg2 _ (by decide), kg1 _ (by decide), kg0 _ (by decide), spE]
      exact (rdSlot 0x30 (by decide) (by decide)).trans sv30)
  have kg3 := ug3.oldReg ug2.self.zero
  obtain ⟨g4, dg4, ug4⟩ := ug3.self.aluImm hcE fad_at_4a (off' := 0x4C) (by decide)
  obtain ⟨g5, dg5, pc5, mem5, regs5⟩ := ug4.self.jalr hcE fad_at_4c
  have fra : reg g3 ra = reg m ra := by
    rw [kg3 _ (by decide), kg2 _ (by decide), kg1 _ (by decide), ug0.newReg (by decide)]
  have fs0 : reg g3 (8 : Fin 32) = reg m (8 : Fin 32) := by
    rw [kg3 _ (by decide), kg2 _ (by decide), ug1.newReg (by decide)]
  have fs1 : reg g3 (9 : Fin 32) = reg m (9 : Fin 32) := by rw [kg3 _ (by decide), ug2.newReg (by decide)]
  have fs2 : reg g3 (18 : Fin 32) = reg m (18 : Fin 32) := ug3.newReg (by decide)
  have kf : ∀ q, q ≠ sp → reg g5 q = reg g3 q := fun q hq => by rw [regs5, ug4.oldReg ug3.self.zero q hq]
  have spf : reg g5 sp = G + 0x50 := by
    rw [regs5, ug4.newReg (by decide)]; show reg g3 sp + 0x40 = _
    rw [kg3 _ (by decide), kg2 _ (by decide), kg1 _ (by decide), kg0 _ (by decide), spE, hspF]
  have pass : ∀ q : Fin 32, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg g3 q = reg m q := by
    intro q hq
    have disj : ∀ q : Fin 32, q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q.val ∉ [11, 12, 13, 14, 15, 16, 17, 5, 6, 7, 28, 29, 30, 31] := by decide
    have nl : ∀ r : Fin 32, r.val ∉ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] → q ≠ r := by
      intro r hr e; subst e; exact hr hq
    rw [kg3 _ (nl _ (by decide)), kg2 _ (nl _ (by decide)), kg1 _ (nl _ (by decide)), kg0 _ (nl _ (by decide)),
      KE q (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide))
        (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide))
        (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide)),
      rD q (nl _ (by decide)), jC _ (nl _ (by decide)), jB _ (nl _ (by decide)), jA _ (nl _ (by decide)),
      kL q (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide)),
      back9 q (nl _ (by decide)) (nl _ (by decide)) (nl _ (by decide))
        (disj q hq),
      j5 _ (nl _ (by decide)), j4 _ (nl _ (by decide)), j3 _ (nl _ (by decide)), j2 _ (nl _ (by decide)),
      j1 _ (nl _ (by decide)), k1 _ (nl _ (by decide))]
  have hmem : ∀ q : Fin 32, feMKeep q = true → q = 0 ∨ q = ra ∨ q = sp ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨
      q = (18 : Fin 32) ∨ q.val ∈ [3, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by decide
  refine ⟨g5, .cons d1 (.cons dp0 (.cons dp1 (.cons dp2 (.cons dp3 (.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5
    (c6.trans (c7.trans (.cons e8' (.cons e9 (cL.trans (.cons eA (.cons eB (.cons eC (cD.trans (cE.trans (.cons dg0
    (.cons dg1 (.cons dg2 (.cons dg3 (.cons dg4 (.single dg5))))))))))))))))))))))))), ?_, spf, ?_, ?_, ?_⟩
  · rw [pc5, ug4.oldReg ug3.self.zero ra (by decide), add_lit_zero, fra, hra, hret]
  · intro q hq
    rcases hmem q hq with rfl | rfl | rfl | rfl | rfl | rfl | h
    · rw [regs5, ug4.self.zero, hz]
    · rw [kf _ (by decide), fra]
    · rw [spf, hsp]
    · rw [kf _ (by decide), fs0]
    · rw [kf _ (by decide), fs1]
    · rw [kf _ (by decide), fs2]
    · have hs : q ≠ sp := fun e => by subst e; exact absurd h (by decide)
      rw [kf q hs, pass q h]
  · intro i hi
    rw [mem5, load_frame memE (by
        have := (env.sOG.subR (c := 0) (l := 16) (by decide)).symm
        rw [add_ofNat_zero] at this; exact this.subR (c := 4 * i) (l := 4) (by omega)),
      cb_load (by omega) (by decide), dnL i hi, Xw i hi, Yw i hi]
  · intro x hx ho; rw [mem5, MfG x hx ho]

end C3.RV32
