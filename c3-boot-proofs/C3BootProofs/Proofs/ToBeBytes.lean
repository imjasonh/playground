import C3BootProofs.Proofs.ZeroArray
import C3BootProofs.Proofs.CtInto

/-!
# `Uint<12>::to_be_byte_array` and `Uint<8>::to_be_byte_array`, as compiled

Each function zeroes a stack buffer with `Array::default`, stores the limbs
into it big-endian from the most significant limb down, and copies the buffer
to the result with `memcpy`.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem tb12_at_0 : fetchRel toBeBytes12Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem tb12_at_2 : fetchRel toBeBytes12Code 0x2 = some (.store .sw sp ra 0x3C, 2) := by decide
theorem tb12_at_4 : fetchRel toBeBytes12Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x38, 2) := by decide
theorem tb12_at_6 : fetchRel toBeBytes12Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x34, 2) := by decide
theorem tb12_at_8 : fetchRel toBeBytes12Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x30, 2) := by decide
theorem tb12_at_a : fetchRel toBeBytes12Code 0xA = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem tb12_at_c : fetchRel toBeBytes12Code 0xC = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem tb12_at_e : fetchRel toBeBytes12Code 0xE = some (.alu .add a0 x0 sp, 2) := by decide
theorem tb12_at_10 : fetchRel toBeBytes12Code 0x10 = some (.alu .add (8 : Fin 32) x0 sp, 2) := by decide
theorem tb12_at_12 : fetchRel toBeBytes12Code 0x12 = some (.auipc ra 0xFFFF9000, 4) := by decide
theorem tb12_at_16 : fetchRel toBeBytes12Code 0x16 = some (.jalr ra ra 0x7EC, 4) := by decide
theorem tb12_at_1a : fetchRel toBeBytes12Code 0x1A = some (.aluImm .add a0 (9 : Fin 32) 0x2C, 4) := by decide
theorem tb12_at_1e : fetchRel toBeBytes12Code 0x1E = some (.aluImm .add a1 x0 0x30, 4) := by decide
theorem tb12_at_22 : fetchRel toBeBytes12Code 0x22 = some (.branch .beq a1 x0 0x28, 2) := by decide
theorem tb12_at_24 : fetchRel toBeBytes12Code 0x24 = some (.load .lw a2 a0 0x0, 2) := by decide
theorem tb12_at_26 : fetchRel toBeBytes12Code 0x26 = some (.aluImm .srl a3 a2 0x18, 4) := by decide
theorem tb12_at_2a : fetchRel toBeBytes12Code 0x2A = some (.aluImm .srl a4 a2 0x8, 4) := by decide
theorem tb12_at_2e : fetchRel toBeBytes12Code 0x2E = some (.aluImm .srl a5 a2 0x10, 4) := by decide
theorem tb12_at_32 : fetchRel toBeBytes12Code 0x32 = some (.store .sb (8 : Fin 32) a3 0x0, 4) := by decide
theorem tb12_at_36 : fetchRel toBeBytes12Code 0x36 = some (.store .sb (8 : Fin 32) a5 0x1, 4) := by decide
theorem tb12_at_3a : fetchRel toBeBytes12Code 0x3A = some (.store .sb (8 : Fin 32) a4 0x2, 4) := by decide
theorem tb12_at_3e : fetchRel toBeBytes12Code 0x3E = some (.store .sb (8 : Fin 32) a2 0x3, 4) := by decide
theorem tb12_at_42 : fetchRel toBeBytes12Code 0x42 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem tb12_at_44 : fetchRel toBeBytes12Code 0x44 = some (.aluImm .add a1 a1 0xFFFFFFFC, 2) := by decide
theorem tb12_at_46 : fetchRel toBeBytes12Code 0x46 = some (.aluImm .add a0 a0 0xFFFFFFFC, 2) := by decide
theorem tb12_at_48 : fetchRel toBeBytes12Code 0x48 = some (.branch .bne a1 x0 0xFFFFFFDC, 2) := by decide
theorem tb12_at_4a : fetchRel toBeBytes12Code 0x4A = some (.alu .add a1 x0 sp, 2) := by decide
theorem tb12_at_4c : fetchRel toBeBytes12Code 0x4C = some (.aluImm .add a2 x0 0x30, 4) := by decide
theorem tb12_at_50 : fetchRel toBeBytes12Code 0x50 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem tb12_at_52 : fetchRel toBeBytes12Code 0x52 = some (.auipc ra 0x1000, 4) := by decide
theorem tb12_at_56 : fetchRel toBeBytes12Code 0x56 = some (.jalr ra ra 0xFFFFF90A, 4) := by decide
theorem tb12_at_5a : fetchRel toBeBytes12Code 0x5A = some (.load .lw ra sp 0x3C, 2) := by decide
theorem tb12_at_5c : fetchRel toBeBytes12Code 0x5C = some (.load .lw (8 : Fin 32) sp 0x38, 2) := by decide
theorem tb12_at_5e : fetchRel toBeBytes12Code 0x5E = some (.load .lw (9 : Fin 32) sp 0x34, 2) := by decide
theorem tb12_at_60 : fetchRel toBeBytes12Code 0x60 = some (.load .lw (18 : Fin 32) sp 0x30, 2) := by decide
theorem tb12_at_62 : fetchRel toBeBytes12Code 0x62 = some (.aluImm .add sp sp 0x40, 2) := by decide
theorem tb12_at_64 : fetchRel toBeBytes12Code 0x64 = some (.jalr x0 ra 0x0, 2) := by decide
theorem tb8_at_0 : fetchRel toBeBytes8Code 0x0 = some (.aluImm .add sp sp 0xFFFFFFD0, 2) := by decide
theorem tb8_at_2 : fetchRel toBeBytes8Code 0x2 = some (.store .sw sp ra 0x2C, 2) := by decide
theorem tb8_at_4 : fetchRel toBeBytes8Code 0x4 = some (.store .sw sp (8 : Fin 32) 0x28, 2) := by decide
theorem tb8_at_6 : fetchRel toBeBytes8Code 0x6 = some (.store .sw sp (9 : Fin 32) 0x24, 2) := by decide
theorem tb8_at_8 : fetchRel toBeBytes8Code 0x8 = some (.store .sw sp (18 : Fin 32) 0x20, 2) := by decide
theorem tb8_at_a : fetchRel toBeBytes8Code 0xA = some (.alu .add (9 : Fin 32) x0 a1, 2) := by decide
theorem tb8_at_c : fetchRel toBeBytes8Code 0xC = some (.alu .add (18 : Fin 32) x0 a0, 2) := by decide
theorem tb8_at_e : fetchRel toBeBytes8Code 0xE = some (.alu .add a0 x0 sp, 2) := by decide
theorem tb8_at_10 : fetchRel toBeBytes8Code 0x10 = some (.alu .add (8 : Fin 32) x0 sp, 2) := by decide
theorem tb8_at_12 : fetchRel toBeBytes8Code 0x12 = some (.auipc ra 0xFFFFB000, 4) := by decide
theorem tb8_at_16 : fetchRel toBeBytes8Code 0x16 = some (.jalr ra ra 0x734, 4) := by decide
theorem tb8_at_1a : fetchRel toBeBytes8Code 0x1A = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0x1C, 2) := by decide
theorem tb8_at_1c : fetchRel toBeBytes8Code 0x1C = some (.aluImm .add a0 x0 0x20, 4) := by decide
theorem tb8_at_20 : fetchRel toBeBytes8Code 0x20 = some (.branch .beq a0 x0 0x28, 2) := by decide
theorem tb8_at_22 : fetchRel toBeBytes8Code 0x22 = some (.load .lw a1 (9 : Fin 32) 0x0, 2) := by decide
theorem tb8_at_24 : fetchRel toBeBytes8Code 0x24 = some (.aluImm .srl a2 a1 0x18, 4) := by decide
theorem tb8_at_28 : fetchRel toBeBytes8Code 0x28 = some (.aluImm .srl a3 a1 0x8, 4) := by decide
theorem tb8_at_2c : fetchRel toBeBytes8Code 0x2C = some (.aluImm .srl a4 a1 0x10, 4) := by decide
theorem tb8_at_30 : fetchRel toBeBytes8Code 0x30 = some (.store .sb (8 : Fin 32) a2 0x0, 4) := by decide
theorem tb8_at_34 : fetchRel toBeBytes8Code 0x34 = some (.store .sb (8 : Fin 32) a4 0x1, 4) := by decide
theorem tb8_at_38 : fetchRel toBeBytes8Code 0x38 = some (.store .sb (8 : Fin 32) a3 0x2, 4) := by decide
theorem tb8_at_3c : fetchRel toBeBytes8Code 0x3C = some (.store .sb (8 : Fin 32) a1 0x3, 4) := by decide
theorem tb8_at_40 : fetchRel toBeBytes8Code 0x40 = some (.aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, 2) := by decide
theorem tb8_at_42 : fetchRel toBeBytes8Code 0x42 = some (.aluImm .add a0 a0 0xFFFFFFFC, 2) := by decide
theorem tb8_at_44 : fetchRel toBeBytes8Code 0x44 = some (.aluImm .add (9 : Fin 32) (9 : Fin 32) 0xFFFFFFFC, 2) := by decide
theorem tb8_at_46 : fetchRel toBeBytes8Code 0x46 = some (.branch .bne a0 x0 0xFFFFFFDC, 2) := by decide
theorem tb8_at_48 : fetchRel toBeBytes8Code 0x48 = some (.alu .add a1 x0 sp, 2) := by decide
theorem tb8_at_4a : fetchRel toBeBytes8Code 0x4A = some (.aluImm .add a2 x0 0x20, 4) := by decide
theorem tb8_at_4e : fetchRel toBeBytes8Code 0x4E = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem tb8_at_50 : fetchRel toBeBytes8Code 0x50 = some (.auipc ra 0x3000, 4) := by decide
theorem tb8_at_54 : fetchRel toBeBytes8Code 0x54 = some (.jalr ra ra 0xFFFFF82A, 4) := by decide
theorem tb8_at_58 : fetchRel toBeBytes8Code 0x58 = some (.load .lw ra sp 0x2C, 2) := by decide
theorem tb8_at_5a : fetchRel toBeBytes8Code 0x5A = some (.load .lw (8 : Fin 32) sp 0x28, 2) := by decide
theorem tb8_at_5c : fetchRel toBeBytes8Code 0x5C = some (.load .lw (9 : Fin 32) sp 0x24, 2) := by decide
theorem tb8_at_5e : fetchRel toBeBytes8Code 0x5E = some (.load .lw (18 : Fin 32) sp 0x20, 2) := by decide
theorem tb8_at_60 : fetchRel toBeBytes8Code 0x60 = some (.aluImm .add sp sp 0x30, 2) := by decide
theorem tb8_at_62 : fetchRel toBeBytes8Code 0x62 = some (.jalr x0 ra 0x0, 2) := by decide
end

def tb12Body : List BInstr :=
  [.lw a2 a0 0x0, .aluImm .srl a3 a2 0x18, .aluImm .srl a4 a2 0x8, .aluImm .srl a5 a2 0x10,
    .sb (8 : Fin 32) a3 0x0, .sb (8 : Fin 32) a5 0x1, .sb (8 : Fin 32) a4 0x2, .sb (8 : Fin 32) a2 0x3,
    .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, .aluImm .add a1 a1 0xFFFFFFFC, .aluImm .add a0 a0 0xFFFFFFFC]

set_option maxRecDepth 20000 in
theorem tb12Body_end : blockEnd toBeBytes12Code 0x24 tb12Body = some 0x48 := by decide

/-- The big-endian bytes of the limbs at `s` from limb `11` down, for the
first `j` of them. -/
def beLimbs (M : Word → BitVec 8) (s : Word) (top j : Nat) : Bytes :=
  (List.range j).flatMap fun i => Sha256.wordBytes (memLoad32 M (s + BitVec.ofNat 32 (4 * (top - i))))

theorem beLimbs_succ (M : Word → BitVec 8) (s : Word) (top j : Nat) :
    beLimbs M s top (j + 1) = beLimbs M s top j ++ Sha256.wordBytes (memLoad32 M (s + BitVec.ofNat 32 (4 * (top - j)))) := by
  unfold beLimbs
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem tb_sub4 {k : Nat} (hk : 4 * (k + 1) < 2 ^ 32) :
    aluEval .add (BitVec.ofNat 32 (4 * (k + 1))) 0xFFFFFFFC = BitVec.ofNat 32 (4 * k) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 (4 * (k + 1)) + 0xFFFFFFFC).toNat = _
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFC : Word).toNat = 2 ^ 32 - 4 from rfl]
  omega

theorem tb_dec {s : Word} {i : Nat} (hi : 1 ≤ i) (hi' : 4 * i < 2 ^ 32) :
    aluEval .add (s + BitVec.ofNat 32 (4 * i)) 0xFFFFFFFC = s + BitVec.ofNat 32 (4 * (i - 1)) := by
  show s + BitVec.ofNat 32 (4 * i) + 0xFFFFFFFC = _
  rw [BitVec.add_assoc]
  refine congrArg (HAdd.hAdd s) (BitVec.eq_of_toNat_eq ?_)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFC : Word).toNat = 2 ^ 32 - 4 from rfl]
  omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
/-- The loop from offset 0x24, with `k` limbs left after the first `j`: it
loads limb `11 - j` and stores it big-endian at `G + 4 j`, until none are
left. -/
theorem tb12_loop {Mz M0 : Word → BitVec 8} {s G : Word}
    (hc : ∀ Mx : Word → BitVec 8, (∀ x, Sep G 48 x 1 → Mx x = Mz x) →
      CodeIn Mx (BitVec.ofNat 32 toBeBytes12Address) toBeBytes12Code)
    (hsrc : ∀ i, i < 48 → Mz (s + BitVec.ofNat 32 i) = M0 (s + BitVec.ofNat 32 i))
    (hsG : Sep s 48 G 48) (hsa : s.toNat % 4 = 0) (hGw : G.toNat + 48 ≤ 0x40000000) :
    ∀ k j (n : Machine) (Mx : Word → BitVec 8), j + k = 12 → 0 < k →
      St Mx (BitVec.ofNat 32 toBeBytes12Address) n 0x24 (reg n) → (∀ x, Sep G 48 x 1 → Mx x = Mz x) →
      memBytes Mx G (4 * j) = beLimbs M0 s 11 j →
      reg n a1 = BitVec.ofNat 32 (4 * k) → reg n a0 = s + BitVec.ofNat 32 (4 * (11 - j)) →
      reg n s0 = G + BitVec.ofNat 32 (4 * j) →
      ∃ n' Mf, Steps n n' ∧ St Mf (BitVec.ofNat 32 toBeBytes12Address) n' 0x4A (reg n') ∧
        (∀ x, Sep G 48 x 1 → Mf x = Mz x) ∧ memBytes Mf G 48 = beLimbs M0 s 11 12 ∧
        ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ s0 → reg n' r = reg n r := by
  intro k
  induction k with
  | zero => intro _ _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
    intro j n Mx hjk _ st hag hbytes ha1 ha0 hs0
    have hcx := hc Mx hag
    have hz := st.zero
    obtain ⟨n1, c1, u1⟩ := St.block tb12Body st hcx tb12Body_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, tb12Body, upd_app, ↓reduceIte, and_true, true_and]
      have hs0' : reg n (8 : Fin 32) = G + BitVec.ofNat 32 (4 * j) := hs0
      rw [ha0, add_lit_zero, hs0']
      have sc : ∀ c, c < 4 → Sep (G + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 c) 1
          (BitVec.ofNat 32 toBeBytes12Address) toBeBytes12Code.length := fun c hc =>
        sep_of_le (by
          rw [add_ofNat_assoc, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * j + c) (by omega),
            show (BitVec.ofNat 32 toBeBytes12Address).toNat = 0x403b3ef2 by decide]
          omega) (by decide)
      exact ⟨aligned_add hsa (by omega), sc 0 (by omega), sc 1 (by omega), sc 2 (by omega), sc 3 (by omega)⟩)
    obtain ⟨v, hv⟩ : ∃ v, memLoad32 Mx (s + BitVec.ofNat 32 (4 * (11 - j))) = v := ⟨_, rfl⟩
    have hv0 : v = memLoad32 M0 (s + BitVec.ofNat 32 (4 * (11 - j))) := by
      rw [← hv]; apply memLoad32_congr; intro i hi; rw [add_ofNat_assoc, ← hsrc _ (by omega)]
      exact hag _ (hsG.sub (c := 4 * (11 - j) + i) (l := 1) (by omega)).symm
    let p := G + BitVec.ofNat 32 (4 * j)
    have eM : (runBlock tb12Body (Mx, reg n)).1 = beStore Mx p v := by
      simp +decide only [runBlock, BInstr.run, tb12Body, upd_app, ↓reduceIte]
      rw [ha0, hs0]; simp only [add_lit_zero]; rw [hv]; rfl
    have R1 : ∀ q, reg n1 q = (runBlock tb12Body (Mx, reg n)).2 q := u1.regs
    have u1' : St (beStore Mx p v) (BitVec.ofNat 32 toBeBytes12Address) n1 0x48 (reg n1) :=
      ⟨u1.pc, by rw [u1.mem, eM], fun _ => rfl⟩
    have hag' : ∀ x, Sep G 48 x 1 → beStore Mx p v x = Mz x := fun x hx => by
      rw [beStore_out (hx.sub (c := 4 * j) (l := 4) (by omega)), hag x hx]
    have hcx' := hc _ hag'
    have hbytes' : memBytes (beStore Mx p v) G (4 * (j + 1)) = beLimbs M0 s 11 (j + 1) := by
      rw [show 4 * (j + 1) = 4 * j + 4 by omega, memBytes_split, beLimbs_succ, ← hbytes, beStore_bytes, hv0]
      congr 1
      apply memBytes_congr; intro i hi
      exact beStore_out (sep_offsets G (c := 4 * j) (n := 4) (d := i) (k := 1) (Or.inr (by omega)) (by omega)
        (by omega))
    have a11 : reg n1 a1 = BitVec.ofNat 32 (4 * k) := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, tb12Body, upd_app, ↓reduceIte]; rw [ha1]
      exact tb_sub4 (by omega)
    have s01 : reg n1 s0 = G + BitVec.ofNat 32 (4 * (j + 1)) := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, tb12Body, upd_app, ↓reduceIte]; rw [hs0]
      show G + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 4 = _
      rw [add_ofNat_assoc, show 4 * j + 4 = 4 * (j + 1) by omega]
    have K1 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ s0 → reg n1 r = reg n r :=
      fun r h0 h1 h2 h3 h4 h5 h8 => by
        rw [R1]; refine runBlock_reg _ _ _ r hz ?_
        simp only [tb12Body, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
        simp [h0, h1, h2, h3, h4, h5, h8]
    by_cases hk : k = 0
    · subst hk
      obtain ⟨n2, d2, u2⟩ := u1'.notTaken hcx' 0x4A tb12_at_48 (by decide) (by
        simp only [branchTaken]; rw [a11, u1'.zero]; decide)
      have hj : j + 1 = 12 := by omega
      rw [hj] at hbytes'
      exact ⟨n2, _, c1.trans (.single d2), u2.self, hag', hbytes',
        fun r h0 h1 h2 h3 h4 h5 h8 => by rw [u2.regs, K1 r h0 h1 h2 h3 h4 h5 h8]⟩
    · obtain ⟨n2, d2, u2⟩ := u1'.taken hcx' 0x24 tb12_at_48 (by decide) (by
        simp only [branchTaken, a11, u1'.zero, bne_iff_ne, ne_eq]
        intro h; exact hk (by have := ofNat_inj (c := 4 * k) (d := 0) (by omega) (by decide) h; omega))
      have a01 : reg n1 a0 = s + BitVec.ofNat 32 (4 * (11 - (j + 1))) := by
        rw [R1]; simp +decide only [runBlock, BInstr.run, tb12Body, upd_app, ↓reduceIte]; rw [ha0]
        rw [tb_dec (by omega) (by omega), show 11 - j - 1 = 11 - (j + 1) by omega]
      obtain ⟨n3, Mf, c3, u3, hag3, hb3, K3⟩ := ih (j + 1) n2 _ (by omega) (by omega) u2.self hag' hbytes'
        (by rw [u2.regs, a11]) (by rw [u2.regs, a01]) (by rw [u2.regs, s01])
      exact ⟨n3, Mf, c1.trans (.cons d2 c3), u3, hag3, hb3,
        fun r h0 h1 h2 h3 h4 h5 h8 => by rw [K3 r h0 h1 h2 h3 h4 h5 h8, u2.regs, K1 r h0 h1 h2 h3 h4 h5 h8]⟩

def tb12Pro : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFFC0, .sw sp ra 0x3C, .sw sp (8 : Fin 32) 0x38, .sw sp (9 : Fin 32) 0x34,
    .sw sp (18 : Fin 32) 0x30, .alu .add (9 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .alu .add a0 x0 sp,
    .alu .add (8 : Fin 32) x0 sp]
def tb12Init : List BInstr := [.aluImm .add a0 (9 : Fin 32) 0x2C, .aluImm .add a1 x0 0x30]
def tb12Fin : List BInstr := [.alu .add a1 x0 sp, .aluImm .add a2 x0 0x30, .alu .add a0 x0 (18 : Fin 32)]
def tb12Epi : List BInstr :=
  [.lw ra sp 0x3C, .lw (8 : Fin 32) sp 0x38, .lw (9 : Fin 32) sp 0x34, .lw (18 : Fin 32) sp 0x30,
    .aluImm .add sp sp 0x40]

set_option maxRecDepth 20000 in
theorem tb12Pro_end : blockEnd toBeBytes12Code 0 tb12Pro = some 0x12 := by decide
set_option maxRecDepth 20000 in
theorem tb12Init_end : blockEnd toBeBytes12Code 0x1A tb12Init = some 0x22 := by decide
set_option maxRecDepth 20000 in
theorem tb12Fin_end : blockEnd toBeBytes12Code 0x4A tb12Fin = some 0x52 := by decide
set_option maxRecDepth 20000 in
theorem tb12Epi_end : blockEnd toBeBytes12Code 0x5A tb12Epi = some 0x64 := by decide

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- **The compiled `Uint<12>::to_be_byte_array`**, from the 12 limbs at `s`
to `out`: the 48 bytes at `out` are the limbs' big-endian bytes from the
most significant limb, limb 11, down. It returns with `sp` and the
callee-saved registers kept, and changes no memory outside `out` and 0x90
bytes of stack below `sp`. -/
theorem toBeBytes12_correct (m : Machine) {out s sp0 retAddr : Word}
    (hc : CodeIn m.mem (BitVec.ofNat 32 toBeBytes12Address) toBeBytes12Code)
    (hZ : CodeIn m.mem (BitVec.ofNat 32 zeroArray48Address) zeroArray48Code)
    (hMS : CodeIn m.mem (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode)
    (hMB : CodeIn m.mem (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode)
    (hpc : m.pc = BitVec.ofNat 32 toBeBytes12Address) (ha0 : reg m a0 = out) (ha1 : reg m a1 = s)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (hsp16 : sp0.toNat % 16 = 0) (hspl : 0x90 ≤ sp0.toNat) (hspw : sp0.toNat ≤ 0x40000000)
    (hsa : s.toNat % 4 = 0) (hsw : s.toNat + 48 ≤ 0x40000000) (how : out.toNat + 48 ≤ 0x40000000)
    (sSF : Sep s 48 (sp0 + 0xFFFFFF70) 0x90) (sOF : Sep out 48 (sp0 + 0xFFFFFF70) 0x90) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ (3 : Fin 32) → q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 →
        q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) →
        q ≠ (31 : Fin 32) → reg m' q = reg m q) ∧
      memBytes m'.mem out 48 = beLimbs m.mem s 11 12 ∧
      ∀ x, Sep (sp0 + 0xFFFFFF70) 0x90 x 1 → Sep out 48 x 1 → m'.mem x = m.mem x := by
  let Q := BitVec.ofNat 32 toBeBytes12Address
  let M0 := m.mem
  let R := sp0 + 0xFFFFFF70
  let G := sp0 + 0xFFFFFFC0
  have hRn : R.toNat = sp0.toNat - 0x90 := by
    show (sp0 + 0xFFFFFF70).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFF70 : Word).toNat = 2 ^ 32 - 0x90 from rfl]; omega
  have hRc : ∀ c, c ≤ 0x90 → (R + BitVec.ofNat 32 c).toNat = R.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hGR : G = R + BitVec.ofNat 32 0x50 := by
    show sp0 + 0xFFFFFFC0 = sp0 + 0xFFFFFF70 + BitVec.ofNat 32 0x50; rw [BitVec.add_assoc]; rfl
  have Gc : ∀ c, G + BitVec.ofNat 32 c = R + BitVec.ofNat 32 (0x50 + c) := fun c => by rw [hGR, add_ofNat_assoc]
  have hGn : G.toNat = sp0.toNat - 0x40 := by rw [hGR, hRc _ (by omega), hRn]; omega
  have hGa : G.toNat % 16 = 0 := by rw [hGn]; omega
  have hGa4 : G.toNat % 4 = 0 := by omega
  have hQn : Q.toNat = 0x403b3ef2 := by decide
  have Rd : ∀ c l, c + l ≤ 0x90 → ∀ (b : Word) (k : Nat), 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (R + BitVec.ofNat 32 c) l b k := fun c l h b k hb hbk => sep_of_le (by rw [hRc _ (by omega)]; omega) hbk
  have st0 : St M0 Q m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  have slotP : ∀ (o : Nat), o + 4 ≤ 0x40 → o % 4 = 0 →
      (G + BitVec.ofNat 32 o).toNat % 4 = 0 ∧ Sep (G + BitVec.ofNat 32 o) 4 Q toBeBytes12Code.length := by
    intro o h2 h3
    refine ⟨aligned_add hGa4 h3, ?_⟩
    rw [Gc]; exact Rd _ _ (by omega) _ _ (by rw [hQn]; decide) (by rw [hQn]; decide)
  obtain ⟨n1, c1, u1⟩ := St.block tb12Pro st0 hc tb12Pro_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, tb12Pro, upd_app, ↓reduceIte, and_true]
    simp only [ev_add]; rw [hsp]
    exact ⟨True.intro, slotP 0x3C (by omega) (by omega), slotP 0x38 (by omega) (by omega),
      slotP 0x34 (by omega) (by omega), slotP 0x30 (by omega) (by omega)⟩)
  obtain ⟨M1, hM1⟩ : ∃ M1, (runBlock tb12Pro (M0, reg m)).1 = M1 := ⟨_, rfl⟩
  have eM1 : M1 = memStore32 (memStore32 (memStore32 (memStore32 M0 (G + BitVec.ofNat 32 0x3C) retAddr)
      (G + BitVec.ofNat 32 0x38) (reg m s0)) (G + BitVec.ofNat 32 0x34) (reg m s1)) (G + BitVec.ofNat 32 0x30)
      (reg m s2) := by
    rw [← hM1]; simp +decide only [runBlock, BInstr.run, tb12Pro, upd_app, ↓reduceIte]; simp only [ev_add]
    rw [hsp, hra]; rfl
  have M1o : ∀ x, Sep (G + BitVec.ofNat 32 0x30) 16 x 1 → M1 x = M0 x := fun x hx => by
    have g : ∀ c, c + 4 ≤ 16 → Sep (G + BitVec.ofNat 32 (0x30 + c)) 4 x 1 := fun c hc => by
      have := hx.sub (c := c) (l := 4) hc; rwa [add_ofNat_assoc] at this
    rw [eM1, memStore32_get_sep (g 0 (by omega)), memStore32_get_sep (g 4 (by omega)),
      memStore32_get_sep (g 8 (by omega)), memStore32_get_sep (g 12 (by omega))]
  have M1slot : ∀ Mx : Word → BitVec 8, (∀ c, 0x30 ≤ c → c < 0x40 → Mx (G + BitVec.ofNat 32 c) = M1 (G + BitVec.ofNat 32 c)) →
      memLoad32 Mx (G + 0x3C) = retAddr ∧ memLoad32 Mx (G + 0x38) = reg m s0 ∧
      memLoad32 Mx (G + 0x34) = reg m s1 ∧ memLoad32 Mx (G + 0x30) = reg m s2 := by
    intro Mx h
    have L : ∀ o, 0x30 ≤ o → o + 4 ≤ 0x40 → memLoad32 Mx (G + BitVec.ofNat 32 o) = memLoad32 M1 (G + BitVec.ofNat 32 o) :=
      fun o h1 h2 => memLoad32_congr fun k hk => by rw [add_ofNat_assoc]; exact h _ (by omega) (by omega)
    have so : ∀ c d, c + 4 ≤ d ∨ d + 4 ≤ c → c < 0x40 → d < 0x40 →
        Sep (G + BitVec.ofNat 32 c) 4 (G + BitVec.ofNat 32 d) 4 := fun c d h hc hd => sep_offsets G h (by omega) (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · show memLoad32 Mx (G + BitVec.ofNat 32 0x3C) = _
      rw [L _ (by omega) (by omega), eM1, memLoad32_store32_sep (so 0x30 0x3C (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (so 0x34 0x3C (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (so 0x38 0x3C (by omega) (by omega) (by omega)), memLoad32_store32_same]
    · show memLoad32 Mx (G + BitVec.ofNat 32 0x38) = _
      rw [L _ (by omega) (by omega), eM1, memLoad32_store32_sep (so 0x30 0x38 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (so 0x34 0x38 (by omega) (by omega) (by omega)), memLoad32_store32_same]
    · show memLoad32 Mx (G + BitVec.ofNat 32 0x34) = _
      rw [L _ (by omega) (by omega), eM1, memLoad32_store32_sep (so 0x30 0x34 (by omega) (by omega) (by omega)),
        memLoad32_store32_same]
    · show memLoad32 Mx (G + BitVec.ofNat 32 0x30) = _
      rw [L _ (by omega) (by omega), eM1, memLoad32_store32_same]
  have R1 : ∀ q, reg n1 q = (runBlock tb12Pro (M0, reg m)).2 q := u1.regs
  have u1' : St M1 Q n1 0x12 (reg n1) := ⟨u1.pc, by rw [u1.mem, hM1], fun _ => rfl⟩
  have M1hi : ∀ x : Word, 0x40000000 ≤ x.toNat → M1 x = M0 x := fun x hx =>
    M1o x (sep_of_le (by rw [Gc, hRc _ (by omega)]; omega) (by have := x.isLt; omega))
  have hc1 : CodeIn M1 Q toBeBytes12Code := fun i hi => by
    rw [M1hi _ (code_hi (b := Q) (by rw [hQn]; decide) (by rw [hQn]; decide) hi)]; exact hc i hi
  have K1 : ∀ q, q ≠ sp → q ≠ s0 → q ≠ s1 → q ≠ s2 → q ≠ a0 → reg n1 q = reg m q := fun q h2 h8 h9 h18 h10 => by
    rw [R1]; refine runBlock_reg _ _ _ q hz ?_
    simp only [tb12Pro, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    simp [h2, h8, h9, h18, h10]
  have sp1 : reg n1 sp = G := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, tb12Pro, upd_app, ↓reduceIte]; simp only [ev_add]; rw [hsp]
  have a01 : reg n1 a0 = G := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, tb12Pro, upd_app, ↓reduceIte]; simp only [ev_add]; rw [hsp]
    exact BitVec.zero_add _
  have s01 : reg n1 s0 = G := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, tb12Pro, upd_app, ↓reduceIte]; simp only [ev_add]; rw [hsp]
    exact BitVec.zero_add _
  have s11 : reg n1 s1 = s := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, tb12Pro, upd_app, ↓reduceIte]; simp only [ev_add]
    exact (BitVec.zero_add _).trans ha1
  have s21 : reg n1 s2 = out := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, tb12Pro, upd_app, ↓reduceIte]; simp only [ev_add]
    exact (BitVec.zero_add _).trans ha0
  -- `Array::default`.
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := u1'.callRa hc1 tb12_at_12 tb12_at_16
    (show Q + BitVec.ofNat 32 0x12 + 0xFFFF9000 + 0x7EC = BitVec.ofNat 32 zeroArray48Address by decide) (by decide)
  have r2 : ∀ q, q ≠ ra → reg n2 q = reg n1 q := fun q h => by rw [regs2]; exact updz u1'.zero h
  have eGR50 : G + 0xFFFFFFB0 = R := by rw [hGR, BitVec.add_assoc]; exact BitVec.add_zero R
  obtain ⟨n3, c3, pc3, sp3, K3, fr3⟩ := zeroArray48_correct n2 (d := G) (T := G)
    (retAddr := Q + BitVec.ofNat 32 (0x12 + 8))
    (by rw [mem2]; intro i hi; rw [M1hi _ (code_hi (b := BitVec.ofNat 32 zeroArray48Address) (by decide) (by decide) hi)]
        exact hZ i hi)
    (by rw [mem2]; intro i hi; rw [M1hi _ (code_hi (b := BitVec.ofNat 32 memcpyStubAddress) (by decide) (by decide) hi)]
        exact hMS i hi)
    (by rw [mem2]; intro i hi; rw [M1hi _ (code_hi (b := BitVec.ofNat 32 memcpyStubAddress + 8) (by decide) (by decide) hi)]
        exact hMB i hi)
    pc2 (by rw [r2 a0 (by decide), a01]) (by rw [regs2]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at Q (by decide) _ (by omega))) (by rw [r2 sp (by decide), sp1]) hGa (by rw [hGn]; omega)
    (by rw [hGn]; omega) (by rw [hGn]; omega)
    (by rw [eGR50, hGR]
        have := sep_offsets R (c := 0x50) (n := 48) (d := 0) (k := 0x50) (Or.inr (by omega)) (by omega) (by omega)
        rwa [add_ofNat_zero] at this)
  rw [eGR50, mem2] at fr3
  obtain ⟨Mz, hMz⟩ : ∃ Mz, n3.mem = Mz := ⟨_, rfl⟩
  rw [hMz] at fr3
  have hG48 : ∀ x, Sep R 0x90 x 1 → Sep G 48 x 1 := fun x hx => by rw [hGR]; exact hx.sub (c := 0x50) (l := 48) (by omega)
  have MzO : ∀ x, Sep R 0x90 x 1 → Mz x = M0 x := fun x hx => by
    rw [fr3 x (by have := hx.sub (c := 0) (l := 0x50) (by omega); rwa [add_ofNat_zero] at this),
      fillBytes_sep (hG48 x hx) (Nat.le_refl _), M1o x (by rw [Gc]; exact hx.sub (c := 0x80) (l := 16) (by omega))]
  have Mzhi : ∀ x : Word, 0x40000000 ≤ x.toNat → Mz x = M0 x := fun x hx =>
    MzO x (sep_of_le (by rw [hRn]; omega) (by have := x.isLt; omega))
  have k3 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → reg n3 q = reg n2 q := K3
  have hc3 : CodeIn Mz Q toBeBytes12Code := fun i hi => by
    rw [Mzhi _ (code_hi (b := Q) (by rw [hQn]; decide) (by rw [hQn]; decide) hi)]; exact hc i hi
  have u3 : St Mz Q n3 0x1A (reg n3) := ⟨by rw [pc3], hMz, fun _ => rfl⟩
  have k31 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra →
      reg n3 q = reg n1 q := fun q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 => by
    rw [k3 q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13, r2 q h14]
  obtain ⟨n4, c4, u4⟩ := St.block tb12Init u3 hc3 tb12Init_end (by simp [BlockOk, BInstr.ok, tb12Init])
  have R4 : ∀ q, reg n4 q = (runBlock tb12Init (Mz, reg n3)).2 q := u4.regs
  have u4' : St Mz Q n4 0x22 (reg n4) := ⟨u4.pc, by rw [u4.mem]; rfl, fun _ => rfl⟩
  have a14 : reg n4 a1 = BitVec.ofNat 32 (4 * 12) := by
    rw [R4]; simp +decide only [runBlock, BInstr.run, tb12Init, upd_app, ↓reduceIte]
  have a04 : reg n4 a0 = s + BitVec.ofNat 32 (4 * (11 - 0)) := by
    rw [R4]; simp +decide only [runBlock, BInstr.run, tb12Init, upd_app, ↓reduceIte]
    rw [k31 s1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s11]; rfl
  have k4 : ∀ q, q ≠ a0 → q ≠ a1 → reg n4 q = reg n3 q := fun q h0 h1 => by
    rw [R4]; simp only [runBlock, BInstr.run, tb12Init]; rw [updz (by simp [upd]) h1, updz u3.zero h0]
  obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc3 0x24 tb12_at_22 (by decide) (by
    simp only [branchTaken]; rw [a14, u4'.zero]; decide)
  have hsG : Sep s 48 G 48 := by rw [hGR]; exact sSF.subR (c := 0x50) (l := 48) (by omega)
  have hGw : G.toNat + 48 ≤ 0x40000000 := by rw [hGn]; omega
  obtain ⟨n6, Mf, c6, u6, hag6, hb6, K6⟩ := tb12_loop (Mz := Mz) (M0 := M0)
    (fun Mx h i hi => by
      have hq := code_hi (b := Q) (by rw [hQn]; decide) (by rw [hQn]; decide) hi
      rw [h _ (sep_of_le (b := Q + BitVec.ofNat 32 i) (by rw [hGn]; omega)
        (by have := (Q + BitVec.ofNat 32 i).isLt; omega))]
      exact hc3 i hi)
    (fun i hi => MzO _ (sSF.sub (c := i) (l := 1) (by omega)).symm) hsG hsa hGw 12 0 n5 Mz rfl (by decide)
    u5.self (fun _ _ => rfl) rfl (by rw [u5.regs, a14]) (by rw [u5.regs, a04])
    (by rw [u5.regs, k4 s0 (by decide) (by decide),
      k31 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s01, add_ofNat_zero])
  have hc6 : CodeIn Mf Q toBeBytes12Code := fun i hi => by
    have hq := code_hi (b := Q) (by rw [hQn]; decide) (by rw [hQn]; decide) hi
    rw [hag6 _ (sep_of_le (b := Q + BitVec.ofNat 32 i) (by rw [hGn]; omega)
      (by have := (Q + BitVec.ofNat 32 i).isLt; omega))]
    exact hc3 i hi
  have Mfhi : ∀ x : Word, 0x40000000 ≤ x.toNat → Mf x = M0 x := fun x hx => by
    rw [hag6 x (sep_of_le (by rw [hGn]; omega) (by have := x.isLt; omega)), Mzhi x hx]
  have K6' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ s0 → q ≠ a6 → q ≠ a7 → q ≠ t0 →
      q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra →
      q ≠ sp → q ≠ s1 → q ≠ s2 → reg n6 q = reg m q :=
    fun q h0 h1 h2 h3 h4 h5 h8 h6 h7 h5' h6' h7' h28 h29 h30 hr hs h9 h18 => by
      rw [K6 q h0 h1 h2 h3 h4 h5 h8, u5.regs, k4 q h0 h1, k31 q h1 h2 h3 h4 h5 h6 h7 h5' h6' h7' h28 h29 h30 hr,
        K1 q hs h8 h9 h18 h0]
  have sp6 : reg n6 sp = G := by
    rw [K6 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u5.regs,
      k4 sp (by decide) (by decide), k31 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp1]
  have s26 : reg n6 s2 = out := by
    rw [K6 s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u5.regs,
      k4 s2 (by decide) (by decide), k31 s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s21]
  obtain ⟨n7, c7, u7⟩ := St.block tb12Fin u6 hc6 tb12Fin_end (by simp [BlockOk, BInstr.ok, tb12Fin])
  have R7 : ∀ q, reg n7 q = (runBlock tb12Fin (Mf, reg n6)).2 q := u7.regs
  have u7' : St Mf Q n7 0x52 (reg n7) := ⟨u7.pc, by rw [u7.mem]; rfl, fun _ => rfl⟩
  have k7 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n7 q = reg n6 q := fun q h0 h1 h2 => by
    rw [R7]; simp only [runBlock, BInstr.run, tb12Fin]
    rw [updz (by simp [upd]) h0, updz (by simp [upd]) h2, updz u6.zero h1]
  obtain ⟨n8, c8, pc8, mem8, regs8⟩ := u7'.callRa hc6 tb12_at_52 tb12_at_56
    (show Q + BitVec.ofNat 32 0x52 + 0x1000 + 0xFFFFF90A = BitVec.ofNat 32 memcpyStubAddress by decide) (by decide)
  have r8 : ∀ q, q ≠ ra → reg n8 q = reg n7 q := fun q h => by rw [regs8]; exact updz u7'.zero h
  have sp8 : reg n8 sp = G := by rw [r8 sp (by decide), k7 sp (by decide) (by decide) (by decide), sp6]
  have eF : G + 0xFFFFFFF0 = R + BitVec.ofNat 32 0x40 := by rw [hGR, BitVec.add_assoc]; rfl
  have hF : (G + 0xFFFFFFF0).toNat = R.toNat + 0x40 := by rw [eF, hRc _ (by omega)]
  have hBn : (BitVec.ofNat 32 memcpyStubAddress + 8 : Word).toNat = 0x403b4856 := by decide
  obtain ⟨n9, c9, pc9, sp9, _, mem9, K9⟩ := memcpy_correct n8 (BitVec.ofNat 32 memcpyStubAddress)
    (Q + BitVec.ofNat 32 (0x52 + 8)) out G 48
    (fun i hi => by
      show n8.mem _ = _; rw [mem8, Mfhi _ (code_hi (b := BitVec.ofNat 32 memcpyStubAddress) (by decide) (by decide) hi)]
      exact hMS i hi)
    (by decide) pc8
    (by rw [r8 a0 (by decide), R7]; simp +decide only [runBlock, BInstr.run, tb12Fin, upd_app, ↓reduceIte]
        simp only [ev_add]; exact (BitVec.zero_add _).trans s26)
    (by rw [r8 a1 (by decide), R7]; simp +decide only [runBlock, BInstr.run, tb12Fin, upd_app, ↓reduceIte]
        simp only [ev_add]; exact (BitVec.zero_add _).trans sp6)
    (by rw [r8 a2 (by decide), R7]; simp +decide only [runBlock, BInstr.run, tb12Fin, upd_app, ↓reduceIte])
    (by rw [regs8]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at Q (by decide) _ (by omega)))
    (by
      rw [mem8, sp8]
      exact { code := fun i hi => by
                rw [Mfhi _ (code_hi (b := BitVec.ofNat 32 memcpyStubAddress + 8) (by decide) (by decide) hi)]
                exact hMB i hi
              hDC := sep_of_le (by rw [hBn]; omega) (by decide)
              hFC := sep_of_le (by rw [hF, hRn, hBn]; omega) (by decide)
              hdF := by rw [eF]; exact sOF.subR (c := 0x40) (l := 16) (by omega)
              hsF := by
                rw [eF, hGR]
                exact sep_offsets R (c := 0x50) (n := 48) (d := 0x40) (k := 16) (Or.inr (by omega)) (by omega)
                  (by omega)
              hsep := by rw [hGR]; exact sOF.subR (c := 0x50) (l := 48) (by omega)
              hF := by rw [hF, hRn]; omega
              hFw := by rw [hF]; omega
              hdw := by omega
              hsw := by rw [hGn]; omega })
  rw [mem8, sp8, eF] at mem9
  obtain ⟨M9, hM9⟩ : ∃ M9, n9.mem = M9 := ⟨_, rfl⟩
  rw [hM9] at mem9
  have k9 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ sp →
      reg n9 q = reg n8 q := K9
  have M9o : ∀ x, Sep R 0x90 x 1 → Sep out 48 x 1 → M9 x = M0 x := fun x hx hy => by
    rw [mem9 x (hx.sub (c := 0x40) (l := 16) (by omega)), copyBytes_sep hy (Nat.le_refl _), hag6 x (hG48 x hx),
      MzO x hx]
  have M9hi : ∀ x : Word, 0x40000000 ≤ x.toNat → M9 x = M0 x := fun x hx =>
    M9o x (sep_of_le (by rw [hRn]; omega) (by have := x.isLt; omega)) (sep_of_le (by omega) (by have := x.isLt; omega))
  have hc9 : CodeIn M9 Q toBeBytes12Code := fun i hi => by
    rw [M9hi _ (code_hi (b := Q) (by rw [hQn]; decide) (by rw [hQn]; decide) hi)]; exact hc i hi
  have u9 : St M9 Q n9 0x5A (reg n9) := ⟨by rw [pc9], hM9, fun _ => rfl⟩
  have sp9' : reg n9 sp = G := by rw [sp9, sp8]
  obtain ⟨n10, c10, u10⟩ := St.block tb12Epi u9 hc9 tb12Epi_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, tb12Epi, upd_app, ↓reduceIte, and_true]
    rw [sp9']
    exact ⟨aligned_add hGa4 (k := 0x3C) (by decide), aligned_add hGa4 (k := 0x38) (by decide),
      aligned_add hGa4 (k := 0x34) (by decide), aligned_add hGa4 (k := 0x30) (by decide)⟩)
  have slots := M1slot M9 fun c h1 h2 => by
    have e1 : Sep (R + BitVec.ofNat 32 0x40) 16 (G + BitVec.ofNat 32 c) 1 := by
      rw [Gc]; exact sep_offsets R (c := 0x40) (n := 16) (d := 0x50 + c) (k := 1) (Or.inl (by omega)) (by omega)
        (by omega)
    have e2 : Sep out 48 (G + BitVec.ofNat 32 c) 1 := by rw [Gc]; exact sOF.subR (c := 0x50 + c) (l := 1) (by omega)
    have e3 : Sep G 48 (G + BitVec.ofNat 32 c) 1 := by
      have := sep_offsets G (c := 0) (n := 48) (d := c) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    have e4 : Sep R 0x50 (G + BitVec.ofNat 32 c) 1 := by
      rw [Gc]
      have := sep_offsets R (c := 0) (n := 0x50) (d := 0x50 + c) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    rw [mem9 _ e1, copyBytes_sep e2 (Nat.le_refl _), hag6 _ e3, fr3 _ e4, fillBytes_sep e3 (Nat.le_refl _)]
  have R10 : ∀ q, reg n10 q = (runBlock tb12Epi (M9, reg n9)).2 q := u10.regs
  have u10' : St M9 Q n10 0x64 (reg n10) := ⟨u10.pc, by rw [u10.mem]; rfl, fun _ => rfl⟩
  obtain ⟨n11, d11, pc11, mem11, regs11⟩ := u10'.jalr hc9 tb12_at_64
  have ra10 : reg n10 ra = retAddr := by
    rw [R10]; simp +decide only [runBlock, BInstr.run, tb12Epi, upd_app, ↓reduceIte]; rw [sp9']; exact slots.1
  have s010 : reg n10 s0 = reg m s0 := by
    rw [R10]; simp +decide only [runBlock, BInstr.run, tb12Epi, upd_app, ↓reduceIte]; rw [sp9']; exact slots.2.1
  have s110 : reg n10 s1 = reg m s1 := by
    rw [R10]; simp +decide only [runBlock, BInstr.run, tb12Epi, upd_app, ↓reduceIte]; rw [sp9']; exact slots.2.2.1
  have s210 : reg n10 s2 = reg m s2 := by
    rw [R10]; simp +decide only [runBlock, BInstr.run, tb12Epi, upd_app, ↓reduceIte]; rw [sp9']; exact slots.2.2.2
  have sp10 : reg n10 sp = sp0 := by
    rw [R10]; simp +decide only [runBlock, BInstr.run, tb12Epi, upd_app, ↓reduceIte]; simp only [ev_add]; rw [sp9']
    show sp0 + 0xFFFFFFC0 + 0x40 = sp0
    rw [BitVec.add_assoc]; exact BitVec.add_zero sp0
  have k10 : ∀ q, q ≠ ra → q ≠ s0 → q ≠ s1 → q ≠ s2 → q ≠ sp → reg n10 q = reg n9 q := fun q h1 h8 h9 h18 h2 => by
    rw [R10]; refine runBlock_reg _ _ _ q u9.zero ?_
    simp only [tb12Epi, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    simp [h1, h8, h9, h18, h2]
  refine ⟨n11, c1.trans (c2.trans (c3.trans (c4.trans (.cons d5 (c6.trans (c7.trans (c8.trans (c9.trans
    (c10.trans (.single d11)))))))))), ?_, by rw [regs11, sp10],
    fun q q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 => ?_, ?_, fun x hx hy => ?_⟩
  · rw [pc11, ra10, add_lit_zero, hret]
  · rw [regs11]
    by_cases qr : q = ra
    · subst qr; rw [ra10, hra]
    by_cases q8 : q = s0
    · subst q8; exact s010
    by_cases q9 : q = s1
    · subst q9; exact s110
    by_cases q18 : q = s2
    · subst q18; exact s210
    by_cases qs : q = sp
    · subst qs; rw [sp10, hsp]
    rw [k10 q qr q8 q9 q18 qs, k9 q q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 qs, r8 q qr,
      k7 q q10 q11 q12, K6' q q10 q11 q12 q13 q14 q15 q8 q16 q17 q5 q6 q7 q28 q29 q30 qr qs q9 q18]
  · have e : memBytes M9 out 48 = memBytes Mf G 48 := by
      unfold memBytes; apply List.map_congr_left; intro i hi; have hi := List.mem_range.mp hi
      show (M9 (out + BitVec.ofNat 32 i)).toNat = (Mf (G + BitVec.ofNat 32 i)).toNat
      rw [mem9 _ (((sOF.sub (c := i) (l := 1) (by omega)).subR (c := 0x40) (l := 16) (by omega)).symm),
        copyBytes_in hi (by omega)]
    rw [mem11, e]; exact hb6
  · rw [mem11]; exact M9o x hx hy

def tb8Body : List BInstr :=
  [.lw a1 s1 0x0, .aluImm .srl a2 a1 0x18, .aluImm .srl a3 a1 0x8, .aluImm .srl a4 a1 0x10,
    .sb (8 : Fin 32) a2 0x0, .sb (8 : Fin 32) a4 0x1, .sb (8 : Fin 32) a3 0x2, .sb (8 : Fin 32) a1 0x3,
    .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x4, .aluImm .add a0 a0 0xFFFFFFFC, .aluImm .add s1 s1 0xFFFFFFFC]

set_option maxRecDepth 20000 in
theorem tb8Body_end : blockEnd toBeBytes8Code 0x22 tb8Body = some 0x46 := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
/-- The loop from offset 0x22, with `k` limbs left after the first `j`: it
loads limb `7 - j` and stores it big-endian at `G + 4 j`, until none are
left. -/
theorem tb8_loop {Mz M0 : Word → BitVec 8} {s G : Word}
    (hc : ∀ Mx : Word → BitVec 8, (∀ x, Sep G 32 x 1 → Mx x = Mz x) →
      CodeIn Mx (BitVec.ofNat 32 toBeBytes8Address) toBeBytes8Code)
    (hsrc : ∀ i, i < 32 → Mz (s + BitVec.ofNat 32 i) = M0 (s + BitVec.ofNat 32 i))
    (hsG : Sep s 32 G 32) (hsa : s.toNat % 4 = 0) (hGw : G.toNat + 32 ≤ 0x40000000) :
    ∀ k j (n : Machine) (Mx : Word → BitVec 8), j + k = 8 → 0 < k →
      St Mx (BitVec.ofNat 32 toBeBytes8Address) n 0x22 (reg n) → (∀ x, Sep G 32 x 1 → Mx x = Mz x) →
      memBytes Mx G (4 * j) = beLimbs M0 s 7 j →
      reg n a0 = BitVec.ofNat 32 (4 * k) → reg n s1 = s + BitVec.ofNat 32 (4 * (7 - j)) →
      reg n s0 = G + BitVec.ofNat 32 (4 * j) →
      ∃ n' Mf, Steps n n' ∧ St Mf (BitVec.ofNat 32 toBeBytes8Address) n' 0x48 (reg n') ∧
        (∀ x, Sep G 32 x 1 → Mf x = Mz x) ∧ memBytes Mf G 32 = beLimbs M0 s 7 8 ∧
        ∀ r, r ≠ s1 → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ s0 → reg n' r = reg n r := by
  intro k
  induction k with
  | zero => intro _ _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ k ih =>
    intro j n Mx hjk _ st hag hbytes ha1 ha0 hs0
    have hcx := hc Mx hag
    have hz := st.zero
    obtain ⟨n1, c1, u1⟩ := St.block tb8Body st hcx tb8Body_end (by
      simp +decide only [BlockOk, BInstr.ok, BInstr.run, tb8Body, upd_app, ↓reduceIte, and_true, true_and]
      have hs0' : reg n (8 : Fin 32) = G + BitVec.ofNat 32 (4 * j) := hs0
      rw [ha0, add_lit_zero, hs0']
      have sc : ∀ c, c < 4 → Sep (G + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 c) 1
          (BitVec.ofNat 32 toBeBytes8Address) toBeBytes8Code.length := fun c hc =>
        sep_of_le (by
          rw [add_ofNat_assoc, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * j + c) (by omega),
            show (BitVec.ofNat 32 toBeBytes8Address).toNat = 0x403b1fd4 by decide]
          omega) (by decide)
      exact ⟨aligned_add hsa (by omega), sc 0 (by omega), sc 1 (by omega), sc 2 (by omega), sc 3 (by omega)⟩)
    obtain ⟨v, hv⟩ : ∃ v, memLoad32 Mx (s + BitVec.ofNat 32 (4 * (7 - j))) = v := ⟨_, rfl⟩
    have hv0 : v = memLoad32 M0 (s + BitVec.ofNat 32 (4 * (7 - j))) := by
      rw [← hv]; apply memLoad32_congr; intro i hi; rw [add_ofNat_assoc, ← hsrc _ (by omega)]
      exact hag _ (hsG.sub (c := 4 * (7 - j) + i) (l := 1) (by omega)).symm
    let p := G + BitVec.ofNat 32 (4 * j)
    have eM : (runBlock tb8Body (Mx, reg n)).1 = beStore Mx p v := by
      simp +decide only [runBlock, BInstr.run, tb8Body, upd_app, ↓reduceIte]
      rw [ha0, hs0]; simp only [add_lit_zero]; rw [hv]; rfl
    have R1 : ∀ q, reg n1 q = (runBlock tb8Body (Mx, reg n)).2 q := u1.regs
    have u1' : St (beStore Mx p v) (BitVec.ofNat 32 toBeBytes8Address) n1 0x46 (reg n1) :=
      ⟨u1.pc, by rw [u1.mem, eM], fun _ => rfl⟩
    have hag' : ∀ x, Sep G 32 x 1 → beStore Mx p v x = Mz x := fun x hx => by
      rw [beStore_out (hx.sub (c := 4 * j) (l := 4) (by omega)), hag x hx]
    have hcx' := hc _ hag'
    have hbytes' : memBytes (beStore Mx p v) G (4 * (j + 1)) = beLimbs M0 s 7 (j + 1) := by
      rw [show 4 * (j + 1) = 4 * j + 4 by omega, memBytes_split, beLimbs_succ, ← hbytes, beStore_bytes, hv0]
      congr 1
      apply memBytes_congr; intro i hi
      exact beStore_out (sep_offsets G (c := 4 * j) (n := 4) (d := i) (k := 1) (Or.inr (by omega)) (by omega)
        (by omega))
    have a11 : reg n1 a0 = BitVec.ofNat 32 (4 * k) := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, tb8Body, upd_app, ↓reduceIte]; rw [ha1]
      exact tb_sub4 (by omega)
    have s01 : reg n1 s0 = G + BitVec.ofNat 32 (4 * (j + 1)) := by
      rw [R1]; simp +decide only [runBlock, BInstr.run, tb8Body, upd_app, ↓reduceIte]; rw [hs0]
      show G + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 4 = _
      rw [add_ofNat_assoc, show 4 * j + 4 = 4 * (j + 1) by omega]
    have K1 : ∀ r, r ≠ s1 → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ s0 → reg n1 r = reg n r :=
      fun r h0 h1 h2 h3 h4 h5 h8 => by
        rw [R1]; refine runBlock_reg _ _ _ r hz ?_
        simp only [tb8Body, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
        simp [h0, h1, h2, h3, h4, h5, h8]
    by_cases hk : k = 0
    · subst hk
      obtain ⟨n2, d2, u2⟩ := u1'.notTaken hcx' 0x48 tb8_at_46 (by decide) (by
        simp only [branchTaken]; rw [a11, u1'.zero]; decide)
      have hj : j + 1 = 8 := by omega
      rw [hj] at hbytes'
      exact ⟨n2, _, c1.trans (.single d2), u2.self, hag', hbytes',
        fun r h0 h1 h2 h3 h4 h5 h8 => by rw [u2.regs, K1 r h0 h1 h2 h3 h4 h5 h8]⟩
    · obtain ⟨n2, d2, u2⟩ := u1'.taken hcx' 0x22 tb8_at_46 (by decide) (by
        simp only [branchTaken, a11, u1'.zero, bne_iff_ne, ne_eq]
        intro h; exact hk (by have := ofNat_inj (c := 4 * k) (d := 0) (by omega) (by decide) h; omega))
      have a01 : reg n1 s1 = s + BitVec.ofNat 32 (4 * (7 - (j + 1))) := by
        rw [R1]; simp +decide only [runBlock, BInstr.run, tb8Body, upd_app, ↓reduceIte]; rw [ha0]
        rw [tb_dec (by omega) (by omega), show 7 - j - 1 = 7 - (j + 1) by omega]
      obtain ⟨n3, Mf, c3, u3, hag3, hb3, K3⟩ := ih (j + 1) n2 _ (by omega) (by omega) u2.self hag' hbytes'
        (by rw [u2.regs, a11]) (by rw [u2.regs, a01]) (by rw [u2.regs, s01])
      exact ⟨n3, Mf, c1.trans (.cons d2 c3), u3, hag3, hb3,
        fun r h0 h1 h2 h3 h4 h5 h8 => by rw [K3 r h0 h1 h2 h3 h4 h5 h8, u2.regs, K1 r h0 h1 h2 h3 h4 h5 h8]⟩


def tb8Pro : List BInstr :=
  [.aluImm .add sp sp 0xFFFFFFD0, .sw sp ra 0x2C, .sw sp (8 : Fin 32) 0x28, .sw sp (9 : Fin 32) 0x24,
    .sw sp (18 : Fin 32) 0x20, .alu .add (9 : Fin 32) x0 a1, .alu .add (18 : Fin 32) x0 a0, .alu .add a0 x0 sp,
    .alu .add (8 : Fin 32) x0 sp]
def tb8Init : List BInstr := [.aluImm .add s1 s1 0x1C, .aluImm .add a0 x0 0x20]
def tb8Fin : List BInstr := [.alu .add a1 x0 sp, .aluImm .add a2 x0 0x20, .alu .add a0 x0 (18 : Fin 32)]
def tb8Epi : List BInstr :=
  [.lw ra sp 0x2C, .lw (8 : Fin 32) sp 0x28, .lw (9 : Fin 32) sp 0x24, .lw (18 : Fin 32) sp 0x20,
    .aluImm .add sp sp 0x30]

set_option maxRecDepth 20000 in
theorem tb8Pro_end : blockEnd toBeBytes8Code 0 tb8Pro = some 0x12 := by decide
set_option maxRecDepth 20000 in
theorem tb8Init_end : blockEnd toBeBytes8Code 0x1A tb8Init = some 0x20 := by decide
set_option maxRecDepth 20000 in
theorem tb8Fin_end : blockEnd toBeBytes8Code 0x48 tb8Fin = some 0x50 := by decide
set_option maxRecDepth 20000 in
theorem tb8Epi_end : blockEnd toBeBytes8Code 0x58 tb8Epi = some 0x62 := by decide

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- **The compiled `Uint<8>::to_be_byte_array`**, from the 8 limbs at `s`
to `out`: the 32 bytes at `out` are the limbs' big-endian bytes from the
most significant limb, limb 7, down. It returns with `sp` and the
callee-saved registers kept, and changes no memory outside `out` and 0x70
bytes of stack below `sp`. -/
theorem toBeBytes8_correct (m : Machine) {out s sp0 retAddr : Word}
    (hc : CodeIn m.mem (BitVec.ofNat 32 toBeBytes8Address) toBeBytes8Code)
    (hZ : CodeIn m.mem (BitVec.ofNat 32 shaZero32Address) shaZero32Code)
    (hMS : CodeIn m.mem (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode)
    (hMB : CodeIn m.mem (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode)
    (hpc : m.pc = BitVec.ofNat 32 toBeBytes8Address) (ha0 : reg m a0 = out) (ha1 : reg m a1 = s)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (hsp16 : sp0.toNat % 16 = 0) (hspl : 0x70 ≤ sp0.toNat) (hspw : sp0.toNat ≤ 0x40000000)
    (hsa : s.toNat % 4 = 0) (hsw : s.toNat + 32 ≤ 0x40000000) (how : out.toNat + 32 ≤ 0x40000000)
    (sSF : Sep s 32 (sp0 + 0xFFFFFF90) 0x70) (sOF : Sep out 32 (sp0 + 0xFFFFFF90) 0x70) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ (3 : Fin 32) → q ≠ t0 → q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 →
        q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) →
        q ≠ (31 : Fin 32) → reg m' q = reg m q) ∧
      memBytes m'.mem out 32 = beLimbs m.mem s 7 8 ∧
      ∀ x, Sep (sp0 + 0xFFFFFF90) 0x70 x 1 → Sep out 32 x 1 → m'.mem x = m.mem x := by
  let Q := BitVec.ofNat 32 toBeBytes8Address
  let M0 := m.mem
  let R := sp0 + 0xFFFFFF90
  let G := sp0 + 0xFFFFFFD0
  have hRn : R.toNat = sp0.toNat - 0x70 := by
    show (sp0 + 0xFFFFFF90).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFF90 : Word).toNat = 2 ^ 32 - 0x70 from rfl]; omega
  have hRc : ∀ c, c ≤ 0x70 → (R + BitVec.ofNat 32 c).toNat = R.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hGR : G = R + BitVec.ofNat 32 0x40 := by
    show sp0 + 0xFFFFFFD0 = sp0 + 0xFFFFFF90 + BitVec.ofNat 32 0x40; rw [BitVec.add_assoc]; rfl
  have Gc : ∀ c, G + BitVec.ofNat 32 c = R + BitVec.ofNat 32 (0x40 + c) := fun c => by rw [hGR, add_ofNat_assoc]
  have hGn : G.toNat = sp0.toNat - 0x30 := by rw [hGR, hRc _ (by omega), hRn]; omega
  have hGa : G.toNat % 16 = 0 := by rw [hGn]; omega
  have hGa4 : G.toNat % 4 = 0 := by omega
  have hQn : Q.toNat = 0x403b1fd4 := by decide
  have Rd : ∀ c l, c + l ≤ 0x70 → ∀ (b : Word) (k : Nat), 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (R + BitVec.ofNat 32 c) l b k := fun c l h b k hb hbk => sep_of_le (by rw [hRc _ (by omega)]; omega) hbk
  have st0 : St M0 Q m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := st0.zero
  have slotP : ∀ (o : Nat), o + 4 ≤ 0x30 → o % 4 = 0 →
      (G + BitVec.ofNat 32 o).toNat % 4 = 0 ∧ Sep (G + BitVec.ofNat 32 o) 4 Q toBeBytes8Code.length := by
    intro o h2 h3
    refine ⟨aligned_add hGa4 h3, ?_⟩
    rw [Gc]; exact Rd _ _ (by omega) _ _ (by rw [hQn]; decide) (by rw [hQn]; decide)
  obtain ⟨n1, c1, u1⟩ := St.block tb8Pro st0 hc tb8Pro_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, tb8Pro, upd_app, ↓reduceIte, and_true]
    simp only [ev_add]; rw [hsp]
    exact ⟨True.intro, slotP 0x2C (by omega) (by omega), slotP 0x28 (by omega) (by omega),
      slotP 0x24 (by omega) (by omega), slotP 0x20 (by omega) (by omega)⟩)
  obtain ⟨M1, hM1⟩ : ∃ M1, (runBlock tb8Pro (M0, reg m)).1 = M1 := ⟨_, rfl⟩
  have eM1 : M1 = memStore32 (memStore32 (memStore32 (memStore32 M0 (G + BitVec.ofNat 32 0x2C) retAddr)
      (G + BitVec.ofNat 32 0x28) (reg m s0)) (G + BitVec.ofNat 32 0x24) (reg m s1)) (G + BitVec.ofNat 32 0x20)
      (reg m s2) := by
    rw [← hM1]; simp +decide only [runBlock, BInstr.run, tb8Pro, upd_app, ↓reduceIte]; simp only [ev_add]
    rw [hsp, hra]; rfl
  have M1o : ∀ x, Sep (G + BitVec.ofNat 32 0x20) 16 x 1 → M1 x = M0 x := fun x hx => by
    have g : ∀ c, c + 4 ≤ 16 → Sep (G + BitVec.ofNat 32 (0x20 + c)) 4 x 1 := fun c hc => by
      have := hx.sub (c := c) (l := 4) hc; rwa [add_ofNat_assoc] at this
    rw [eM1, memStore32_get_sep (g 0 (by omega)), memStore32_get_sep (g 4 (by omega)),
      memStore32_get_sep (g 8 (by omega)), memStore32_get_sep (g 12 (by omega))]
  have M1slot : ∀ Mx : Word → BitVec 8, (∀ c, 0x20 ≤ c → c < 0x30 → Mx (G + BitVec.ofNat 32 c) = M1 (G + BitVec.ofNat 32 c)) →
      memLoad32 Mx (G + 0x2C) = retAddr ∧ memLoad32 Mx (G + 0x28) = reg m s0 ∧
      memLoad32 Mx (G + 0x24) = reg m s1 ∧ memLoad32 Mx (G + 0x20) = reg m s2 := by
    intro Mx h
    have L : ∀ o, 0x20 ≤ o → o + 4 ≤ 0x30 → memLoad32 Mx (G + BitVec.ofNat 32 o) = memLoad32 M1 (G + BitVec.ofNat 32 o) :=
      fun o h1 h2 => memLoad32_congr fun k hk => by rw [add_ofNat_assoc]; exact h _ (by omega) (by omega)
    have so : ∀ c d, c + 4 ≤ d ∨ d + 4 ≤ c → c < 0x30 → d < 0x30 →
        Sep (G + BitVec.ofNat 32 c) 4 (G + BitVec.ofNat 32 d) 4 := fun c d h hc hd => sep_offsets G h (by omega) (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · show memLoad32 Mx (G + BitVec.ofNat 32 0x2C) = _
      rw [L _ (by omega) (by omega), eM1, memLoad32_store32_sep (so 0x20 0x2C (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (so 0x24 0x2C (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (so 0x28 0x2C (by omega) (by omega) (by omega)), memLoad32_store32_same]
    · show memLoad32 Mx (G + BitVec.ofNat 32 0x28) = _
      rw [L _ (by omega) (by omega), eM1, memLoad32_store32_sep (so 0x20 0x28 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (so 0x24 0x28 (by omega) (by omega) (by omega)), memLoad32_store32_same]
    · show memLoad32 Mx (G + BitVec.ofNat 32 0x24) = _
      rw [L _ (by omega) (by omega), eM1, memLoad32_store32_sep (so 0x20 0x24 (by omega) (by omega) (by omega)),
        memLoad32_store32_same]
    · show memLoad32 Mx (G + BitVec.ofNat 32 0x20) = _
      rw [L _ (by omega) (by omega), eM1, memLoad32_store32_same]
  have R1 : ∀ q, reg n1 q = (runBlock tb8Pro (M0, reg m)).2 q := u1.regs
  have u1' : St M1 Q n1 0x12 (reg n1) := ⟨u1.pc, by rw [u1.mem, hM1], fun _ => rfl⟩
  have M1hi : ∀ x : Word, 0x40000000 ≤ x.toNat → M1 x = M0 x := fun x hx =>
    M1o x (sep_of_le (by rw [Gc, hRc _ (by omega)]; omega) (by have := x.isLt; omega))
  have hc1 : CodeIn M1 Q toBeBytes8Code := fun i hi => by
    rw [M1hi _ (code_hi (b := Q) (by rw [hQn]; decide) (by rw [hQn]; decide) hi)]; exact hc i hi
  have K1 : ∀ q, q ≠ sp → q ≠ s0 → q ≠ s1 → q ≠ s2 → q ≠ a0 → reg n1 q = reg m q := fun q h2 h8 h9 h18 h10 => by
    rw [R1]; refine runBlock_reg _ _ _ q hz ?_
    simp only [tb8Pro, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    simp [h2, h8, h9, h18, h10]
  have sp1 : reg n1 sp = G := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, tb8Pro, upd_app, ↓reduceIte]; simp only [ev_add]; rw [hsp]
  have a01 : reg n1 a0 = G := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, tb8Pro, upd_app, ↓reduceIte]; simp only [ev_add]; rw [hsp]
    exact BitVec.zero_add _
  have s01 : reg n1 s0 = G := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, tb8Pro, upd_app, ↓reduceIte]; simp only [ev_add]; rw [hsp]
    exact BitVec.zero_add _
  have s11 : reg n1 s1 = s := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, tb8Pro, upd_app, ↓reduceIte]; simp only [ev_add]
    exact (BitVec.zero_add _).trans ha1
  have s21 : reg n1 s2 = out := by
    rw [R1]; simp +decide only [runBlock, BInstr.run, tb8Pro, upd_app, ↓reduceIte]; simp only [ev_add]
    exact (BitVec.zero_add _).trans ha0
  -- `Array::default`.
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := u1'.callRa hc1 tb8_at_12 tb8_at_16
    (show Q + BitVec.ofNat 32 0x12 + 0xFFFFB000 + 0x734 = BitVec.ofNat 32 shaZero32Address by decide) (by decide)
  have r2 : ∀ q, q ≠ ra → reg n2 q = reg n1 q := fun q h => by rw [regs2]; exact updz u1'.zero h
  have eGR50 : G + 0xFFFFFFC0 = R := by rw [hGR, BitVec.add_assoc]; exact BitVec.add_zero R
  obtain ⟨n3, c3, pc3, sp3, K3, fr3⟩ := shaZero32_correct n2 (d := G) (T := G)
    (retAddr := Q + BitVec.ofNat 32 (0x12 + 8))
    (by rw [mem2]; intro i hi; rw [M1hi _ (code_hi (b := BitVec.ofNat 32 shaZero32Address) (by decide) (by decide) hi)]
        exact hZ i hi)
    (by rw [mem2]; intro i hi; rw [M1hi _ (code_hi (b := BitVec.ofNat 32 memcpyStubAddress) (by decide) (by decide) hi)]
        exact hMS i hi)
    (by rw [mem2]; intro i hi; rw [M1hi _ (code_hi (b := BitVec.ofNat 32 memcpyStubAddress + 8) (by decide) (by decide) hi)]
        exact hMB i hi)
    pc2 (by rw [r2 a0 (by decide), a01]) (by rw [regs2]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at Q (by decide) _ (by omega))) (by rw [r2 sp (by decide), sp1]) hGa (by rw [hGn]; omega)
    (by rw [hGn]; omega) (by rw [hGn]; omega)
    (by rw [eGR50, hGR]
        have := sep_offsets R (c := 0x40) (n := 32) (d := 0) (k := 0x40) (Or.inr (by omega)) (by omega) (by omega)
        rwa [add_ofNat_zero] at this)
  rw [eGR50, mem2] at fr3
  obtain ⟨Mz, hMz⟩ : ∃ Mz, n3.mem = Mz := ⟨_, rfl⟩
  rw [hMz] at fr3
  have hG48 : ∀ x, Sep R 0x70 x 1 → Sep G 32 x 1 := fun x hx => by rw [hGR]; exact hx.sub (c := 0x40) (l := 32) (by omega)
  have MzO : ∀ x, Sep R 0x70 x 1 → Mz x = M0 x := fun x hx => by
    rw [fr3 x (by have := hx.sub (c := 0) (l := 0x40) (by omega); rwa [add_ofNat_zero] at this),
      fillBytes_sep (hG48 x hx) (Nat.le_refl _), M1o x (by rw [Gc]; exact hx.sub (c := 0x60) (l := 16) (by omega))]
  have Mzhi : ∀ x : Word, 0x40000000 ≤ x.toNat → Mz x = M0 x := fun x hx =>
    MzO x (sep_of_le (by rw [hRn]; omega) (by have := x.isLt; omega))
  have k3 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → reg n3 q = reg n2 q := K3
  have hc3 : CodeIn Mz Q toBeBytes8Code := fun i hi => by
    rw [Mzhi _ (code_hi (b := Q) (by rw [hQn]; decide) (by rw [hQn]; decide) hi)]; exact hc i hi
  have u3 : St Mz Q n3 0x1A (reg n3) := ⟨by rw [pc3], hMz, fun _ => rfl⟩
  have k31 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra →
      reg n3 q = reg n1 q := fun q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 => by
    rw [k3 q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13, r2 q h14]
  obtain ⟨n4, c4, u4⟩ := St.block tb8Init u3 hc3 tb8Init_end (by simp [BlockOk, BInstr.ok, tb8Init])
  have R4 : ∀ q, reg n4 q = (runBlock tb8Init (Mz, reg n3)).2 q := u4.regs
  have u4' : St Mz Q n4 0x20 (reg n4) := ⟨u4.pc, by rw [u4.mem]; rfl, fun _ => rfl⟩
  have a04c : reg n4 a0 = BitVec.ofNat 32 (4 * 8) := by
    rw [R4]; simp +decide only [runBlock, BInstr.run, tb8Init, upd_app, ↓reduceIte]
  have s14 : reg n4 s1 = s + BitVec.ofNat 32 (4 * (7 - 0)) := by
    rw [R4]; simp +decide only [runBlock, BInstr.run, tb8Init, upd_app, ↓reduceIte]
    rw [k31 s1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s11]; rfl
  have k4 : ∀ q, q ≠ s1 → q ≠ a0 → reg n4 q = reg n3 q := fun q h9 h0 => by
    rw [R4]; simp only [runBlock, BInstr.run, tb8Init]; rw [updz (by simp [upd]) h0, updz u3.zero h9]
  obtain ⟨n5, d5, u5⟩ := u4'.notTaken hc3 0x22 tb8_at_20 (by decide) (by
    simp only [branchTaken]; rw [a04c, u4'.zero]; decide)
  have hsG : Sep s 32 G 32 := by rw [hGR]; exact sSF.subR (c := 0x40) (l := 32) (by omega)
  have hGw : G.toNat + 32 ≤ 0x40000000 := by rw [hGn]; omega
  obtain ⟨n6, Mf, c6, u6, hag6, hb6, K6⟩ := tb8_loop (Mz := Mz) (M0 := M0)
    (fun Mx h i hi => by
      have hq := code_hi (b := Q) (by rw [hQn]; decide) (by rw [hQn]; decide) hi
      rw [h _ (sep_of_le (b := Q + BitVec.ofNat 32 i) (by rw [hGn]; omega)
        (by have := (Q + BitVec.ofNat 32 i).isLt; omega))]
      exact hc3 i hi)
    (fun i hi => MzO _ (sSF.sub (c := i) (l := 1) (by omega)).symm) hsG hsa hGw 8 0 n5 Mz rfl (by decide)
    u5.self (fun _ _ => rfl) rfl (by rw [u5.regs, a04c]) (by rw [u5.regs, s14])
    (by rw [u5.regs, k4 s0 (by decide) (by decide),
      k31 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s01, add_ofNat_zero])
  have hc6 : CodeIn Mf Q toBeBytes8Code := fun i hi => by
    have hq := code_hi (b := Q) (by rw [hQn]; decide) (by rw [hQn]; decide) hi
    rw [hag6 _ (sep_of_le (b := Q + BitVec.ofNat 32 i) (by rw [hGn]; omega)
      (by have := (Q + BitVec.ofNat 32 i).isLt; omega))]
    exact hc3 i hi
  have Mfhi : ∀ x : Word, 0x40000000 ≤ x.toNat → Mf x = M0 x := fun x hx => by
    rw [hag6 x (sep_of_le (by rw [hGn]; omega) (by have := x.isLt; omega)), Mzhi x hx]
  have K6' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ s0 → q ≠ a6 → q ≠ a7 → q ≠ t0 →
      q ≠ t1 → q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra →
      q ≠ sp → q ≠ s1 → q ≠ s2 → reg n6 q = reg m q :=
    fun q h0 h1 h2 h3 h4 h5 h8 h6 h7 h5' h6' h7' h28 h29 h30 hr hs h9 h18 => by
      rw [K6 q h9 h0 h1 h2 h3 h4 h8, u5.regs, k4 q h9 h0, k31 q h1 h2 h3 h4 h5 h6 h7 h5' h6' h7' h28 h29 h30 hr,
        K1 q hs h8 h9 h18 h0]
  have sp6 : reg n6 sp = G := by
    rw [K6 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u5.regs,
      k4 sp (by decide) (by decide), k31 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp1]
  have s26 : reg n6 s2 = out := by
    rw [K6 s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), u5.regs,
      k4 s2 (by decide) (by decide), k31 s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s21]
  obtain ⟨n7, c7, u7⟩ := St.block tb8Fin u6 hc6 tb8Fin_end (by simp [BlockOk, BInstr.ok, tb8Fin])
  have R7 : ∀ q, reg n7 q = (runBlock tb8Fin (Mf, reg n6)).2 q := u7.regs
  have u7' : St Mf Q n7 0x50 (reg n7) := ⟨u7.pc, by rw [u7.mem]; rfl, fun _ => rfl⟩
  have k7 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n7 q = reg n6 q := fun q h0 h1 h2 => by
    rw [R7]; simp only [runBlock, BInstr.run, tb8Fin]
    rw [updz (by simp [upd]) h0, updz (by simp [upd]) h2, updz u6.zero h1]
  obtain ⟨n8, c8, pc8, mem8, regs8⟩ := u7'.callRa hc6 tb8_at_50 tb8_at_54
    (show Q + BitVec.ofNat 32 0x50 + 0x3000 + 0xFFFFF82A = BitVec.ofNat 32 memcpyStubAddress by decide) (by decide)
  have r8 : ∀ q, q ≠ ra → reg n8 q = reg n7 q := fun q h => by rw [regs8]; exact updz u7'.zero h
  have sp8 : reg n8 sp = G := by rw [r8 sp (by decide), k7 sp (by decide) (by decide) (by decide), sp6]
  have eF : G + 0xFFFFFFF0 = R + BitVec.ofNat 32 0x30 := by rw [hGR, BitVec.add_assoc]; rfl
  have hF : (G + 0xFFFFFFF0).toNat = R.toNat + 0x30 := by rw [eF, hRc _ (by omega)]
  have hBn : (BitVec.ofNat 32 memcpyStubAddress + 8 : Word).toNat = 0x403b4856 := by decide
  obtain ⟨n9, c9, pc9, sp9, _, mem9, K9⟩ := memcpy_correct n8 (BitVec.ofNat 32 memcpyStubAddress)
    (Q + BitVec.ofNat 32 (0x50 + 8)) out G 32
    (fun i hi => by
      show n8.mem _ = _; rw [mem8, Mfhi _ (code_hi (b := BitVec.ofNat 32 memcpyStubAddress) (by decide) (by decide) hi)]
      exact hMS i hi)
    (by decide) pc8
    (by rw [r8 a0 (by decide), R7]; simp +decide only [runBlock, BInstr.run, tb8Fin, upd_app, ↓reduceIte]
        simp only [ev_add]; exact (BitVec.zero_add _).trans s26)
    (by rw [r8 a1 (by decide), R7]; simp +decide only [runBlock, BInstr.run, tb8Fin, upd_app, ↓reduceIte]
        simp only [ev_add]; exact (BitVec.zero_add _).trans sp6)
    (by rw [r8 a2 (by decide), R7]; simp +decide only [runBlock, BInstr.run, tb8Fin, upd_app, ↓reduceIte])
    (by rw [regs8]; simp +decide only [upd_app, ↓reduceIte])
    (even_clear _ (even_at Q (by decide) _ (by omega)))
    (by
      rw [mem8, sp8]
      exact { code := fun i hi => by
                rw [Mfhi _ (code_hi (b := BitVec.ofNat 32 memcpyStubAddress + 8) (by decide) (by decide) hi)]
                exact hMB i hi
              hDC := sep_of_le (by rw [hBn]; omega) (by decide)
              hFC := sep_of_le (by rw [hF, hRn, hBn]; omega) (by decide)
              hdF := by rw [eF]; exact sOF.subR (c := 0x30) (l := 16) (by omega)
              hsF := by
                rw [eF, hGR]
                exact sep_offsets R (c := 0x40) (n := 32) (d := 0x30) (k := 16) (Or.inr (by omega)) (by omega)
                  (by omega)
              hsep := by rw [hGR]; exact sOF.subR (c := 0x40) (l := 32) (by omega)
              hF := by rw [hF, hRn]; omega
              hFw := by rw [hF]; omega
              hdw := by omega
              hsw := by rw [hGn]; omega })
  rw [mem8, sp8, eF] at mem9
  obtain ⟨M9, hM9⟩ : ∃ M9, n9.mem = M9 := ⟨_, rfl⟩
  rw [hM9] at mem9
  have k9 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ sp →
      reg n9 q = reg n8 q := K9
  have M9o : ∀ x, Sep R 0x70 x 1 → Sep out 32 x 1 → M9 x = M0 x := fun x hx hy => by
    rw [mem9 x (hx.sub (c := 0x30) (l := 16) (by omega)), copyBytes_sep hy (Nat.le_refl _), hag6 x (hG48 x hx),
      MzO x hx]
  have M9hi : ∀ x : Word, 0x40000000 ≤ x.toNat → M9 x = M0 x := fun x hx =>
    M9o x (sep_of_le (by rw [hRn]; omega) (by have := x.isLt; omega)) (sep_of_le (by omega) (by have := x.isLt; omega))
  have hc9 : CodeIn M9 Q toBeBytes8Code := fun i hi => by
    rw [M9hi _ (code_hi (b := Q) (by rw [hQn]; decide) (by rw [hQn]; decide) hi)]; exact hc i hi
  have u9 : St M9 Q n9 0x58 (reg n9) := ⟨by rw [pc9], hM9, fun _ => rfl⟩
  have sp9' : reg n9 sp = G := by rw [sp9, sp8]
  obtain ⟨n10, c10, u10⟩ := St.block tb8Epi u9 hc9 tb8Epi_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, tb8Epi, upd_app, ↓reduceIte, and_true]
    rw [sp9']
    exact ⟨aligned_add hGa4 (k := 0x2C) (by decide), aligned_add hGa4 (k := 0x28) (by decide),
      aligned_add hGa4 (k := 0x24) (by decide), aligned_add hGa4 (k := 0x20) (by decide)⟩)
  have slots := M1slot M9 fun c h1 h2 => by
    have e1 : Sep (R + BitVec.ofNat 32 0x30) 16 (G + BitVec.ofNat 32 c) 1 := by
      rw [Gc]; exact sep_offsets R (c := 0x30) (n := 16) (d := 0x40 + c) (k := 1) (Or.inl (by omega)) (by omega)
        (by omega)
    have e2 : Sep out 32 (G + BitVec.ofNat 32 c) 1 := by rw [Gc]; exact sOF.subR (c := 0x40 + c) (l := 1) (by omega)
    have e3 : Sep G 32 (G + BitVec.ofNat 32 c) 1 := by
      have := sep_offsets G (c := 0) (n := 32) (d := c) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    have e4 : Sep R 0x40 (G + BitVec.ofNat 32 c) 1 := by
      rw [Gc]
      have := sep_offsets R (c := 0) (n := 0x40) (d := 0x40 + c) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
    rw [mem9 _ e1, copyBytes_sep e2 (Nat.le_refl _), hag6 _ e3, fr3 _ e4, fillBytes_sep e3 (Nat.le_refl _)]
  have R10 : ∀ q, reg n10 q = (runBlock tb8Epi (M9, reg n9)).2 q := u10.regs
  have u10' : St M9 Q n10 0x62 (reg n10) := ⟨u10.pc, by rw [u10.mem]; rfl, fun _ => rfl⟩
  obtain ⟨n11, d11, pc11, mem11, regs11⟩ := u10'.jalr hc9 tb8_at_62
  have ra10 : reg n10 ra = retAddr := by
    rw [R10]; simp +decide only [runBlock, BInstr.run, tb8Epi, upd_app, ↓reduceIte]; rw [sp9']; exact slots.1
  have s010 : reg n10 s0 = reg m s0 := by
    rw [R10]; simp +decide only [runBlock, BInstr.run, tb8Epi, upd_app, ↓reduceIte]; rw [sp9']; exact slots.2.1
  have s110 : reg n10 s1 = reg m s1 := by
    rw [R10]; simp +decide only [runBlock, BInstr.run, tb8Epi, upd_app, ↓reduceIte]; rw [sp9']; exact slots.2.2.1
  have s210 : reg n10 s2 = reg m s2 := by
    rw [R10]; simp +decide only [runBlock, BInstr.run, tb8Epi, upd_app, ↓reduceIte]; rw [sp9']; exact slots.2.2.2
  have sp10 : reg n10 sp = sp0 := by
    rw [R10]; simp +decide only [runBlock, BInstr.run, tb8Epi, upd_app, ↓reduceIte]; simp only [ev_add]; rw [sp9']
    show sp0 + 0xFFFFFFD0 + 0x30 = sp0
    rw [BitVec.add_assoc]; exact BitVec.add_zero sp0
  have k10 : ∀ q, q ≠ ra → q ≠ s0 → q ≠ s1 → q ≠ s2 → q ≠ sp → reg n10 q = reg n9 q := fun q h1 h8 h9 h18 h2 => by
    rw [R10]; refine runBlock_reg _ _ _ q u9.zero ?_
    simp only [tb8Epi, List.filterMap_cons, List.filterMap_nil, BInstr.dst]
    simp [h1, h8, h9, h18, h2]
  refine ⟨n11, c1.trans (c2.trans (c3.trans (c4.trans (.cons d5 (c6.trans (c7.trans (c8.trans (c9.trans
    (c10.trans (.single d11)))))))))), ?_, by rw [regs11, sp10],
    fun q q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 => ?_, ?_, fun x hx hy => ?_⟩
  · rw [pc11, ra10, add_lit_zero, hret]
  · rw [regs11]
    by_cases qr : q = ra
    · subst qr; rw [ra10, hra]
    by_cases q8 : q = s0
    · subst q8; exact s010
    by_cases q9 : q = s1
    · subst q9; exact s110
    by_cases q18 : q = s2
    · subst q18; exact s210
    by_cases qs : q = sp
    · subst qs; rw [sp10, hsp]
    rw [k10 q qr q8 q9 q18 qs, k9 q q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 qs, r8 q qr,
      k7 q q10 q11 q12, K6' q q10 q11 q12 q13 q14 q15 q8 q16 q17 q5 q6 q7 q28 q29 q30 qr qs q9 q18]
  · have e : memBytes M9 out 32 = memBytes Mf G 32 := by
      unfold memBytes; apply List.map_congr_left; intro i hi; have hi := List.mem_range.mp hi
      show (M9 (out + BitVec.ofNat 32 i)).toNat = (Mf (G + BitVec.ofNat 32 i)).toNat
      rw [mem9 _ (((sOF.sub (c := i) (l := 1) (by omega)).subR (c := 0x30) (l := 16) (by omega)).symm),
        copyBytes_in hi (by omega)]
    rw [mem11, e]; exact hb6
  · rw [mem11]; exact M9o x hx hy


end C3.RV32
