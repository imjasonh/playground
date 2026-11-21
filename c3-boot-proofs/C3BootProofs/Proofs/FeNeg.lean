import C3BootProofs.Proofs.FeCall

/-!
# `-&FieldElement2625`, as compiled

`<&FieldElement2625 as Neg>::neg` hands `reduce` the `[u64; 10]` of
`16 p - x`, limb by limb with `u32` wrapping, and copies the reduced limbs
out.
-/

namespace C3.RV32

open C3.Image

abbrev negPs : List (Fin 32 × Word) := [(ra, 0x7C), ((8 : Fin 32), 0x78)]

section
set_option maxRecDepth 20000
theorem fng_at_0 : fetchRel feNegCode 0x0 = some (.aluImm .add sp sp 0xFFFFFF80, 2) := by decide
theorem fng_at_2 : fetchRel feNegCode 0x2 = some (.store .sw sp ra 0x7C, 2) := by decide
theorem fng_at_4 : fetchRel feNegCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x78, 2) := by decide
theorem fng_at_6 : fetchRel feNegCode 0x6 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem fng_at_8 : fetchRel feNegCode 0x8 = some (.load .lw a0 a1 0x0, 2) := by decide
theorem fng_at_a : fetchRel feNegCode 0xA = some (.load .lw a2 a1 0x4, 2) := by decide
theorem fng_at_c : fetchRel feNegCode 0xC = some (.load .lw a3 a1 0x8, 2) := by decide
theorem fng_at_e : fetchRel feNegCode 0xE = some (.load .lw a4 a1 0xC, 2) := by decide
theorem fng_at_10 : fetchRel feNegCode 0x10 = some (.load .lw a5 a1 0x10, 2) := by decide
theorem fng_at_12 : fetchRel feNegCode 0x12 = some (.load .lw a6 a1 0x14, 4) := by decide
theorem fng_at_16 : fetchRel feNegCode 0x16 = some (.load .lw (17 : Fin 32) a1 0x18, 4) := by decide
theorem fng_at_1a : fetchRel feNegCode 0x1A = some (.load .lw (5 : Fin 32) a1 0x1C, 4) := by decide
theorem fng_at_1e : fetchRel feNegCode 0x1E = some (.load .lw (6 : Fin 32) a1 0x20, 4) := by decide
theorem fng_at_22 : fetchRel feNegCode 0x22 = some (.load .lw (7 : Fin 32) a1 0x24, 4) := by decide
theorem fng_at_26 : fetchRel feNegCode 0x26 = some (.lui a1 0x40000000, 4) := by decide
theorem fng_at_2a : fetchRel feNegCode 0x2A = some (.aluImm .add a1 a1 0xFFFFFFF0, 2) := by decide
theorem fng_at_2c : fetchRel feNegCode 0x2C = some (.lui (28 : Fin 32) 0x20000000, 4) := by decide
theorem fng_at_30 : fetchRel feNegCode 0x30 = some (.alu .sub a0 a1 a0, 4) := by decide
theorem fng_at_34 : fetchRel feNegCode 0x34 = some (.aluImm .add (28 : Fin 32) (28 : Fin 32) 0xFFFFFFF0, 2) := by decide
theorem fng_at_36 : fetchRel feNegCode 0x36 = some (.aluImm .add a0 a0 0xFFFFFEE0, 4) := by decide
theorem fng_at_3a : fetchRel feNegCode 0x3A = some (.alu .sub a2 (28 : Fin 32) a2, 4) := by decide
theorem fng_at_3e : fetchRel feNegCode 0x3E = some (.alu .sub a3 a1 a3, 4) := by decide
theorem fng_at_42 : fetchRel feNegCode 0x42 = some (.alu .sub a4 (28 : Fin 32) a4, 4) := by decide
theorem fng_at_46 : fetchRel feNegCode 0x46 = some (.alu .sub a5 a1 a5, 4) := by decide
theorem fng_at_4a : fetchRel feNegCode 0x4A = some (.alu .sub a6 (28 : Fin 32) a6, 4) := by decide
theorem fng_at_4e : fetchRel feNegCode 0x4E = some (.alu .sub (17 : Fin 32) a1 (17 : Fin 32), 4) := by decide
theorem fng_at_52 : fetchRel feNegCode 0x52 = some (.alu .sub (5 : Fin 32) (28 : Fin 32) (5 : Fin 32), 4) := by decide
theorem fng_at_56 : fetchRel feNegCode 0x56 = some (.alu .sub a1 a1 (6 : Fin 32), 4) := by decide
theorem fng_at_5a : fetchRel feNegCode 0x5A = some (.alu .sub (6 : Fin 32) (28 : Fin 32) (7 : Fin 32), 4) := by decide
theorem fng_at_5e : fetchRel feNegCode 0x5E = some (.store .sw sp a0 0x0, 2) := by decide
theorem fng_at_60 : fetchRel feNegCode 0x60 = some (.store .sw sp x0 0x4, 2) := by decide
theorem fng_at_62 : fetchRel feNegCode 0x62 = some (.store .sw sp a2 0x8, 2) := by decide
theorem fng_at_64 : fetchRel feNegCode 0x64 = some (.store .sw sp x0 0xC, 2) := by decide
theorem fng_at_66 : fetchRel feNegCode 0x66 = some (.store .sw sp a3 0x10, 2) := by decide
theorem fng_at_68 : fetchRel feNegCode 0x68 = some (.store .sw sp x0 0x14, 2) := by decide
theorem fng_at_6a : fetchRel feNegCode 0x6A = some (.store .sw sp a4 0x18, 2) := by decide
theorem fng_at_6c : fetchRel feNegCode 0x6C = some (.store .sw sp x0 0x1C, 2) := by decide
theorem fng_at_6e : fetchRel feNegCode 0x6E = some (.store .sw sp a5 0x20, 2) := by decide
theorem fng_at_70 : fetchRel feNegCode 0x70 = some (.store .sw sp x0 0x24, 2) := by decide
theorem fng_at_72 : fetchRel feNegCode 0x72 = some (.store .sw sp a6 0x28, 2) := by decide
theorem fng_at_74 : fetchRel feNegCode 0x74 = some (.store .sw sp x0 0x2C, 2) := by decide
theorem fng_at_76 : fetchRel feNegCode 0x76 = some (.store .sw sp (17 : Fin 32) 0x30, 2) := by decide
theorem fng_at_78 : fetchRel feNegCode 0x78 = some (.store .sw sp x0 0x34, 2) := by decide
theorem fng_at_7a : fetchRel feNegCode 0x7A = some (.store .sw sp (5 : Fin 32) 0x38, 2) := by decide
theorem fng_at_7c : fetchRel feNegCode 0x7C = some (.store .sw sp x0 0x3C, 2) := by decide
theorem fng_at_7e : fetchRel feNegCode 0x7E = some (.store .sw sp a1 0x40, 2) := by decide
theorem fng_at_80 : fetchRel feNegCode 0x80 = some (.store .sw sp x0 0x44, 2) := by decide
theorem fng_at_82 : fetchRel feNegCode 0x82 = some (.store .sw sp (6 : Fin 32) 0x48, 2) := by decide
theorem fng_at_84 : fetchRel feNegCode 0x84 = some (.store .sw sp x0 0x4C, 2) := by decide
theorem fng_at_86 : fetchRel feNegCode 0x86 = some (.aluImm .add a0 sp 0x50, 2) := by decide
theorem fng_at_88 : fetchRel feNegCode 0x88 = some (.alu .add a1 x0 sp, 2) := by decide
theorem fng_at_8a : fetchRel feNegCode 0x8A = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem fng_at_8e : fetchRel feNegCode 0x8E = some (.jalr ra ra 0x2E6, 4) := by decide
theorem fng_at_92 : fetchRel feNegCode 0x92 = some (.load .lw a0 sp 0x50, 2) := by decide
theorem fng_at_94 : fetchRel feNegCode 0x94 = some (.load .lw a1 sp 0x54, 2) := by decide
theorem fng_at_96 : fetchRel feNegCode 0x96 = some (.load .lw a2 sp 0x58, 2) := by decide
theorem fng_at_98 : fetchRel feNegCode 0x98 = some (.load .lw a3 sp 0x5C, 2) := by decide
theorem fng_at_9a : fetchRel feNegCode 0x9A = some (.load .lw a4 sp 0x60, 2) := by decide
theorem fng_at_9c : fetchRel feNegCode 0x9C = some (.load .lw a5 sp 0x64, 2) := by decide
theorem fng_at_9e : fetchRel feNegCode 0x9E = some (.load .lw a6 sp 0x68, 2) := by decide
theorem fng_at_a0 : fetchRel feNegCode 0xA0 = some (.load .lw (17 : Fin 32) sp 0x6C, 2) := by decide
theorem fng_at_a2 : fetchRel feNegCode 0xA2 = some (.load .lw (5 : Fin 32) sp 0x70, 2) := by decide
theorem fng_at_a4 : fetchRel feNegCode 0xA4 = some (.load .lw (6 : Fin 32) sp 0x74, 2) := by decide
theorem fng_at_a6 : fetchRel feNegCode 0xA6 = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem fng_at_a8 : fetchRel feNegCode 0xA8 = some (.store .sw (8 : Fin 32) a1 0x4, 2) := by decide
theorem fng_at_aa : fetchRel feNegCode 0xAA = some (.store .sw (8 : Fin 32) a2 0x8, 2) := by decide
theorem fng_at_ac : fetchRel feNegCode 0xAC = some (.store .sw (8 : Fin 32) a3 0xC, 2) := by decide
theorem fng_at_ae : fetchRel feNegCode 0xAE = some (.store .sw (8 : Fin 32) a4 0x10, 2) := by decide
theorem fng_at_b0 : fetchRel feNegCode 0xB0 = some (.store .sw (8 : Fin 32) a5 0x14, 2) := by decide
theorem fng_at_b2 : fetchRel feNegCode 0xB2 = some (.store .sw (8 : Fin 32) a6 0x18, 4) := by decide
theorem fng_at_b6 : fetchRel feNegCode 0xB6 = some (.store .sw (8 : Fin 32) (17 : Fin 32) 0x1C, 4) := by decide
theorem fng_at_ba : fetchRel feNegCode 0xBA = some (.store .sw (8 : Fin 32) (5 : Fin 32) 0x20, 4) := by decide
theorem fng_at_be : fetchRel feNegCode 0xBE = some (.store .sw (8 : Fin 32) (6 : Fin 32) 0x24, 4) := by decide
theorem fng_at_c2 : fetchRel feNegCode 0xC2 = some (.load .lw ra sp 0x7C, 2) := by decide
theorem fng_at_c4 : fetchRel feNegCode 0xC4 = some (.load .lw (8 : Fin 32) sp 0x78, 2) := by decide
theorem fng_at_c6 : fetchRel feNegCode 0xC6 = some (.aluImm .add sp sp 0x80, 2) := by decide
theorem fng_at_c8 : fetchRel feNegCode 0xC8 = some (.jalr x0 ra 0x0, 2) := by decide
theorem negSave_end : blockEnd feNegCode 2 (saveBlock negPs) = some 6 := by decide
theorem negRestore_end : blockEnd feNegCode 0xC2 (restoreBlock negPs) = some 0xC6 := by decide

def fngX1 : List BInstr :=
  [.alu .add (8 : Fin 32) x0 a0,
    .lw a0 a1 0x0,
    .lw a2 a1 0x4,
    .lw a3 a1 0x8,
    .lw a4 a1 0xC,
    .lw a5 a1 0x10,
    .lw a6 a1 0x14,
    .lw (17 : Fin 32) a1 0x18,
    .lw (5 : Fin 32) a1 0x1C,
    .lw (6 : Fin 32) a1 0x20,
    .lw (7 : Fin 32) a1 0x24,
    .lui a1 0x40000000,
    .aluImm .add a1 a1 0xFFFFFFF0,
    .lui (28 : Fin 32) 0x20000000,
    .alu .sub a0 a1 a0,
    .aluImm .add (28 : Fin 32) (28 : Fin 32) 0xFFFFFFF0,
    .aluImm .add a0 a0 0xFFFFFEE0,
    .alu .sub a2 (28 : Fin 32) a2,
    .alu .sub a3 a1 a3,
    .alu .sub a4 (28 : Fin 32) a4,
    .alu .sub a5 a1 a5,
    .alu .sub a6 (28 : Fin 32) a6,
    .alu .sub (17 : Fin 32) a1 (17 : Fin 32),
    .alu .sub (5 : Fin 32) (28 : Fin 32) (5 : Fin 32),
    .alu .sub a1 a1 (6 : Fin 32),
    .alu .sub (6 : Fin 32) (28 : Fin 32) (7 : Fin 32)]

theorem fngX1_end : blockEnd feNegCode 0x6 fngX1 = some 0x5E := by decide

def fngX2 : List BInstr :=
  [.sw sp a0 0x0,
    .sw sp x0 0x4,
    .sw sp a2 0x8,
    .sw sp x0 0xC,
    .sw sp a3 0x10,
    .sw sp x0 0x14,
    .sw sp a4 0x18,
    .sw sp x0 0x1C,
    .sw sp a5 0x20,
    .sw sp x0 0x24,
    .sw sp a6 0x28,
    .sw sp x0 0x2C,
    .sw sp (17 : Fin 32) 0x30,
    .sw sp x0 0x34,
    .sw sp (5 : Fin 32) 0x38,
    .sw sp x0 0x3C,
    .sw sp a1 0x40,
    .sw sp x0 0x44,
    .sw sp (6 : Fin 32) 0x48,
    .sw sp x0 0x4C]

theorem fngX2_end : blockEnd feNegCode 0x5E fngX2 = some 0x86 := by decide

def fngX3 : List BInstr :=
  [.aluImm .add a0 sp 0x50,
    .alu .add a1 x0 sp]

theorem fngX3_end : blockEnd feNegCode 0x86 fngX3 = some 0x8A := by decide

def fngY1 : List BInstr :=
  [.lw a0 sp 0x50,
    .lw a1 sp 0x54,
    .lw a2 sp 0x58,
    .lw a3 sp 0x5C,
    .lw a4 sp 0x60,
    .lw a5 sp 0x64,
    .lw a6 sp 0x68,
    .lw (17 : Fin 32) sp 0x6C,
    .lw (5 : Fin 32) sp 0x70,
    .lw (6 : Fin 32) sp 0x74]

theorem fngY1_end : blockEnd feNegCode 0x92 fngY1 = some 0xA6 := by decide

def fngY2 : List BInstr :=
  [.sw (8 : Fin 32) a0 0x0,
    .sw (8 : Fin 32) a1 0x4,
    .sw (8 : Fin 32) a2 0x8,
    .sw (8 : Fin 32) a3 0xC,
    .sw (8 : Fin 32) a4 0x10,
    .sw (8 : Fin 32) a5 0x14,
    .sw (8 : Fin 32) a6 0x18,
    .sw (8 : Fin 32) (17 : Fin 32) 0x1C,
    .sw (8 : Fin 32) (5 : Fin 32) 0x20,
    .sw (8 : Fin 32) (6 : Fin 32) 0x24]

theorem fngY2_end : blockEnd feNegCode 0xA6 fngY2 = some 0xC2 := by decide

end

/-- `16 p - x` for limb `i`, wrapping in `u32`, as `neg` hands it to
`reduce`. -/
def feNegZ (x : Nat → Word) (i : Nat) : Word :=
  (if i = 0 then 0x3FFFFED0 else if i % 2 = 0 then 0x3FFFFFF0 else 0x1FFFFFF0) - x i

theorem fng_limb0 (x : Word) : aluEval .add (aluEval .sub 0x3FFFFFF0 x) 0xFFFFFEE0 = 0x3FFFFED0 - x := by
  apply BitVec.eq_of_toNat_eq
  show (0x3FFFFFF0 - x + 0xFFFFFEE0 : Word).toNat = (0x3FFFFED0 - x : Word).toNat
  rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_sub]
  have := x.isLt
  show ((2 ^ 32 - x.toNat + 0x3FFFFFF0) % 2 ^ 32 + 0xFFFFFEE0) % 2 ^ 32 = (2 ^ 32 - x.toNat + 0x3FFFFED0) % 2 ^ 32
  omega

theorem wordsAt_congr2 {M M' : Word → BitVec 8} {a b : Word} {n : Nat}
    (h : ∀ i, i < n → memLoad32 M (a + BitVec.ofNat 32 (4 * i)) = memLoad32 M' (b + BitVec.ofNat 32 (4 * i))) :
    wordsAt M a n = wordsAt M' b n := by
  unfold wordsAt
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

/-- Where `neg` runs: its code and `reduce`'s, the 0xA0 bytes of stack below
`sp0` (its 0x80-byte frame and `reduce`'s 0x20 below it), the operand at
`ip`, and the result at `out`. -/
structure FNEnv (M : Word → BitVec 8) (P sp0 out ip : Word) : Prop where
  hP : P.toNat % 2 = 0
  cod : CodeIn M P feNegCode
  red : CodeIn M (P + 0xFFFFE370) feReduceCode
  hsp : sp0.toNat % 4 = 0
  hS : 0xA0 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hip : ip.toNat % 4 = 0
  sGC : Sep (sp0 + 0xFFFFFF60) 0xA0 P feNegCode.length
  sGR : Sep (sp0 + 0xFFFFFF60) 0xA0 (P + 0xFFFFE370) feReduceCode.length
  sOC : Sep out 40 P feNegCode.length
  sOG : Sep out 40 (sp0 + 0xFFFFFF60) 0xA0
  sIG : Sep ip 40 (sp0 + 0xFFFFFF60) 0xA0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- **The compiled `<&FieldElement2625 as Neg>::neg`**: it stores at `out`
`reduce` of `16 p - x`, for the operand's limbs `x` at `ip`. -/
theorem feNeg_correct (m : Machine) {P sp0 out ip retAddr : Word} (env : FNEnv m.mem P sp0 out ip)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = ip)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      (wordsAt m'.mem out 10).map BitVec.toNat =
        feReduceSpec (feNegZ (limbs m.mem ip) 0).toNat (feNegZ (limbs m.mem ip) 1).toNat
          (feNegZ (limbs m.mem ip) 2).toNat (feNegZ (limbs m.mem ip) 3).toNat (feNegZ (limbs m.mem ip) 4).toNat
          (feNegZ (limbs m.mem ip) 5).toNat (feNegZ (limbs m.mem ip) 6).toNat (feNegZ (limbs m.mem ip) 7).toNat
          (feNegZ (limbs m.mem ip) 8).toNat (feNegZ (limbs m.mem ip) 9).toNat ∧
      ∀ x, Sep (sp0 + 0xFFFFFF60) 0xA0 x 1 → Sep out 40 x 1 → m'.mem x = m.mem x := by
  obtain ⟨G, hG⟩ : ∃ G, sp0 + 0xFFFFFF60 = G := ⟨_, rfl⟩
  have sGC := env.sGC; have sGR := env.sGR; have sOG := env.sOG; have sIG := env.sIG
  rw [hG] at sGC sGR sOG sIG ⊢
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFF80 = F := ⟨_, rfl⟩
  have hGF : G + BitVec.ofNat 32 0x20 = F := by rw [← hG, ← hF, BitVec.add_assoc]; rfl
  have hGa : G.toNat % 4 = 0 := by rw [← hG]; exact aligned_add env.hsp (k := 0xFFFFFF60) (by decide)
  have hFa : F.toNat % 4 = 0 := by rw [← hGF]; exact aligned_add hGa (k := 0x20) (by decide)
  have hGw : G.toNat + 0xA0 = sp0.toNat := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFF60 : Word).toNat = 4294967136 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have hFn : F.toNat = G.toNat + 0x20 := by rw [← hGF, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have gw : G.toNat + 0xA0 ≤ 2 ^ 32 := by have := sp0.isLt; omega
  have eS : F + 0x80 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have eFk : ∀ k, F + BitVec.ofNat 32 k = G + BitVec.ofNat 32 (0x20 + k) := fun k => by rw [← hGF, add_ofNat_assoc]
  have eF50 : F + 0x50 = G + BitVec.ofNat 32 0x70 := by rw [← hGF, BitVec.add_assoc]; rfl
  have eFr : F + 0xFFFFFFE0 = G := by rw [← hGF, BitVec.add_assoc]; exact BitVec.add_zero G
  have offs : ∀ {c n d k : Nat}, c + n ≤ d ∨ d + k ≤ c → c + n ≤ 0xA0 → d + k ≤ 0xA0 →
      Sep (G + BitVec.ofNat 32 c) n (G + BitVec.ofNat 32 d) k :=
    fun h h1 h2 => sep_offsets G h (by omega) (by omega)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code' : List Nat}, CodeIn m.mem b code' →
      Sep G 0xA0 b code'.length → (∀ x, Sep G 0xA0 x 1 → M' x = m.mem x) → CodeIn M' b code' :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have sepFF : ∀ k j, k + 4 ≤ j ∨ j + 4 ≤ k → k + 4 ≤ 0x80 → j + 4 ≤ 0x80 →
      Sep (F + BitVec.ofNat 32 k) 4 (F + BitVec.ofNat 32 j) 4 := fun k j h h1 h2 => by
    rw [eFk, eFk]; exact offs (by omega) (by omega) (by omega)
  have sepOO : ∀ k j, k + 4 ≤ j ∨ j + 4 ≤ k → k + 4 ≤ 40 → j + 4 ≤ 40 →
      Sep (out + BitVec.ofNat 32 k) 4 (out + BitVec.ofNat 32 j) 4 := fun k j h h1 h2 =>
    sep_offsets out h (by have := env.sOG; omega) (by omega)
  have tC : ∀ k, k + 4 ≤ 0x80 → Sep (F + BitVec.ofNat 32 k) 4 P feNegCode.length := fun k h => by
    rw [eFk]; exact sGC.sub (by omega)
  have tX : ∀ k, k + 4 ≤ 0x80 → ∀ {x : Word}, Sep G 0xA0 x 1 → Sep (F + BitVec.ofNat 32 k) 4 x 1 :=
    fun k h x hx => by rw [eFk]; exact hx.sub (by omega)
  have slotC : ∀ (o : Word), 0x78 ≤ o.toNat → o.toNat + 4 ≤ 0x80 → ∀ {b : Word} {l : Nat}, Sep G 0xA0 b l →
      Sep (F + o) 4 b l := by
    intro o h1 h2 b l h
    rw [← ofNat_toNat_self o, eFk]; exact h.sub (c := 0x20 + o.toNat) (l := 4) (by omega)
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.cod fng_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF80) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨ms, cs, us⟩ := St.block (saveBlock negPs) u1 env.cod negSave_end (saveBlock_ok _ negPs _ fun p hp => by
    rw [sp1]
    simp only [negPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl <;> exact ⟨aligned_add hFa (by decide), slotC _ (by decide) (by decide) sGC⟩)
  simp only [saveBlock_run] at us
  rw [sp1] at us
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFF80)) negPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at us
  have frSv : ∀ x, Sep G 0xA0 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside negPs fun p hp => by
      simp only [negPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl <;> exact slotC _ (by decide) (by decide) hx
  have hslv : ∀ r o, (r, o) ∈ negPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [negPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ q, q ≠ sp → reg ms q = reg m q := fun q h => by rw [us.regs, updz hz h]
  have sp2 : reg ms sp = F := by rw [us.regs]; exact sp1
  have hcS : CodeIn Msv P feNegCode := cIn env.cod sGC frSv
  have ldI : ∀ k, k + 4 ≤ 40 → memLoad32 Msv (ip + BitVec.ofNat 32 k) = memLoad32 m.mem (ip + BitVec.ofNat 32 k) :=
    fun k h => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact frSv _ (sIG.sub (c := k + j) (l := 1) (by omega)).symm
  -- `16 p - x` into the frame
  obtain ⟨mX1, cX1, uX1⟩ := St.block fngX1 us.self hcS fngX1_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, fngX1, upd_app, ↓reduceIte, and_true]
    rw [r2 a1 (by decide), ha1]
    repeat' apply And.intro
    all_goals first | trivial | (refine aligned_add env.hip ?_; decide))
  simp only [runBlock, BInstr.run, fngX1] at uX1
  have rX : ∀ q, reg mX1 q = _ := uX1.regs
  have c40 : aluEval .add 0x40000000 0xFFFFFFF0 = 0x3FFFFFF0 := by decide
  have c20 : aluEval .add 0x20000000 0xFFFFFFF0 = 0x1FFFFFF0 := by decide
  have XV0 : reg mX1 a0 = feNegZ (limbs m.mem ip) 0 := by
    rw [rX]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a1 (by decide), ha1]; simp only [c40, c20]
    rw [show memLoad32 Msv (ip + 0x0) = memLoad32 m.mem (ip + 0x0) from ldI 0x0 (by decide)]
    rw [fng_limb0]; rfl
  have XV1 : reg mX1 a2 = feNegZ (limbs m.mem ip) 1 := by
    rw [rX]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a1 (by decide), ha1]; simp only [c40, c20]
    rw [show memLoad32 Msv (ip + 0x4) = memLoad32 m.mem (ip + 0x4) from ldI 0x4 (by decide)]
    rfl
  have XV2 : reg mX1 a3 = feNegZ (limbs m.mem ip) 2 := by
    rw [rX]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a1 (by decide), ha1]; simp only [c40, c20]
    rw [show memLoad32 Msv (ip + 0x8) = memLoad32 m.mem (ip + 0x8) from ldI 0x8 (by decide)]
    rfl
  have XV3 : reg mX1 a4 = feNegZ (limbs m.mem ip) 3 := by
    rw [rX]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a1 (by decide), ha1]; simp only [c40, c20]
    rw [show memLoad32 Msv (ip + 0xC) = memLoad32 m.mem (ip + 0xC) from ldI 0xC (by decide)]
    rfl
  have XV4 : reg mX1 a5 = feNegZ (limbs m.mem ip) 4 := by
    rw [rX]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a1 (by decide), ha1]; simp only [c40, c20]
    rw [show memLoad32 Msv (ip + 0x10) = memLoad32 m.mem (ip + 0x10) from ldI 0x10 (by decide)]
    rfl
  have XV5 : reg mX1 a6 = feNegZ (limbs m.mem ip) 5 := by
    rw [rX]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a1 (by decide), ha1]; simp only [c40, c20]
    rw [show memLoad32 Msv (ip + 0x14) = memLoad32 m.mem (ip + 0x14) from ldI 0x14 (by decide)]
    rfl
  have XV6 : reg mX1 (17 : Fin 32) = feNegZ (limbs m.mem ip) 6 := by
    rw [rX]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a1 (by decide), ha1]; simp only [c40, c20]
    rw [show memLoad32 Msv (ip + 0x18) = memLoad32 m.mem (ip + 0x18) from ldI 0x18 (by decide)]
    rfl
  have XV7 : reg mX1 (5 : Fin 32) = feNegZ (limbs m.mem ip) 7 := by
    rw [rX]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a1 (by decide), ha1]; simp only [c40, c20]
    rw [show memLoad32 Msv (ip + 0x1C) = memLoad32 m.mem (ip + 0x1C) from ldI 0x1C (by decide)]
    rfl
  have XV8 : reg mX1 a1 = feNegZ (limbs m.mem ip) 8 := by
    rw [rX]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a1 (by decide), ha1]; simp only [c40, c20]
    rw [show memLoad32 Msv (ip + 0x20) = memLoad32 m.mem (ip + 0x20) from ldI 0x20 (by decide)]
    rfl
  have XV9 : reg mX1 (6 : Fin 32) = feNegZ (limbs m.mem ip) 9 := by
    rw [rX]; simp +decide only [upd_app, ↓reduceIte]; rw [r2 a1 (by decide), ha1]; simp only [c40, c20]
    rw [show memLoad32 Msv (ip + 0x24) = memLoad32 m.mem (ip + 0x24) from ldI 0x24 (by decide)]
    rfl
  have spX1 : reg mX1 sp = F := by rw [rX]; simp +decide only [upd_app, ↓reduceIte]; exact sp2
  obtain ⟨mX2, cX2, u2⟩ := St.block fngX2 uX1.self hcS fngX2_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, fngX2, and_true]
    rw [spX1]
    repeat' apply And.intro
    all_goals first | trivial | (refine aligned_add hFa ?_; decide) | exact tC _ (by decide))
  simp only [runBlock, BInstr.run, fngX2] at u2
  rw [spX1] at u2
  have W0 : memLoad32 mX2.mem (F + 0x0) = feNegZ (limbs m.mem ip) 0 := by
    rw [u2.mem]
    rw [memLoad32_store32_sep (a := F + 0x4C) (b := F + 0x0) (sepFF 0x4C 0x0 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x48) (b := F + 0x0) (sepFF 0x48 0x0 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x44) (b := F + 0x0) (sepFF 0x44 0x0 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x40) (b := F + 0x0) (sepFF 0x40 0x0 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x3C) (b := F + 0x0) (sepFF 0x3C 0x0 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x38) (b := F + 0x0) (sepFF 0x38 0x0 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x34) (b := F + 0x0) (sepFF 0x34 0x0 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x30) (b := F + 0x0) (sepFF 0x30 0x0 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x2C) (b := F + 0x0) (sepFF 0x2C 0x0 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x28) (b := F + 0x0) (sepFF 0x28 0x0 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x24) (b := F + 0x0) (sepFF 0x24 0x0 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x20) (b := F + 0x0) (sepFF 0x20 0x0 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x1C) (b := F + 0x0) (sepFF 0x1C 0x0 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x18) (b := F + 0x0) (sepFF 0x18 0x0 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x14) (b := F + 0x0) (sepFF 0x14 0x0 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x10) (b := F + 0x0) (sepFF 0x10 0x0 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0xC) (b := F + 0x0) (sepFF 0xC 0x0 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x8) (b := F + 0x0) (sepFF 0x8 0x0 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x4) (b := F + 0x0) (sepFF 0x4 0x0 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_same]
    exact XV0
  have W4 : memLoad32 mX2.mem (F + 0x4) = 0 := by
    rw [u2.mem]
    rw [memLoad32_store32_sep (a := F + 0x4C) (b := F + 0x4) (sepFF 0x4C 0x4 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x48) (b := F + 0x4) (sepFF 0x48 0x4 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x44) (b := F + 0x4) (sepFF 0x44 0x4 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x40) (b := F + 0x4) (sepFF 0x40 0x4 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x3C) (b := F + 0x4) (sepFF 0x3C 0x4 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x38) (b := F + 0x4) (sepFF 0x38 0x4 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x34) (b := F + 0x4) (sepFF 0x34 0x4 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x30) (b := F + 0x4) (sepFF 0x30 0x4 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x2C) (b := F + 0x4) (sepFF 0x2C 0x4 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x28) (b := F + 0x4) (sepFF 0x28 0x4 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x24) (b := F + 0x4) (sepFF 0x24 0x4 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x20) (b := F + 0x4) (sepFF 0x20 0x4 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x1C) (b := F + 0x4) (sepFF 0x1C 0x4 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x18) (b := F + 0x4) (sepFF 0x18 0x4 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x14) (b := F + 0x4) (sepFF 0x14 0x4 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x10) (b := F + 0x4) (sepFF 0x10 0x4 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0xC) (b := F + 0x4) (sepFF 0xC 0x4 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x8) (b := F + 0x4) (sepFF 0x8 0x4 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_same]
    exact uX1.self.zero
  have W8 : memLoad32 mX2.mem (F + 0x8) = feNegZ (limbs m.mem ip) 1 := by
    rw [u2.mem]
    rw [memLoad32_store32_sep (a := F + 0x4C) (b := F + 0x8) (sepFF 0x4C 0x8 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x48) (b := F + 0x8) (sepFF 0x48 0x8 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x44) (b := F + 0x8) (sepFF 0x44 0x8 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x40) (b := F + 0x8) (sepFF 0x40 0x8 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x3C) (b := F + 0x8) (sepFF 0x3C 0x8 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x38) (b := F + 0x8) (sepFF 0x38 0x8 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x34) (b := F + 0x8) (sepFF 0x34 0x8 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x30) (b := F + 0x8) (sepFF 0x30 0x8 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x2C) (b := F + 0x8) (sepFF 0x2C 0x8 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x28) (b := F + 0x8) (sepFF 0x28 0x8 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x24) (b := F + 0x8) (sepFF 0x24 0x8 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x20) (b := F + 0x8) (sepFF 0x20 0x8 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x1C) (b := F + 0x8) (sepFF 0x1C 0x8 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x18) (b := F + 0x8) (sepFF 0x18 0x8 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x14) (b := F + 0x8) (sepFF 0x14 0x8 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x10) (b := F + 0x8) (sepFF 0x10 0x8 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0xC) (b := F + 0x8) (sepFF 0xC 0x8 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_same]
    exact XV1
  have W12 : memLoad32 mX2.mem (F + 0xC) = 0 := by
    rw [u2.mem]
    rw [memLoad32_store32_sep (a := F + 0x4C) (b := F + 0xC) (sepFF 0x4C 0xC (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x48) (b := F + 0xC) (sepFF 0x48 0xC (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x44) (b := F + 0xC) (sepFF 0x44 0xC (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x40) (b := F + 0xC) (sepFF 0x40 0xC (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x3C) (b := F + 0xC) (sepFF 0x3C 0xC (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x38) (b := F + 0xC) (sepFF 0x38 0xC (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x34) (b := F + 0xC) (sepFF 0x34 0xC (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x30) (b := F + 0xC) (sepFF 0x30 0xC (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x2C) (b := F + 0xC) (sepFF 0x2C 0xC (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x28) (b := F + 0xC) (sepFF 0x28 0xC (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x24) (b := F + 0xC) (sepFF 0x24 0xC (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x20) (b := F + 0xC) (sepFF 0x20 0xC (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x1C) (b := F + 0xC) (sepFF 0x1C 0xC (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x18) (b := F + 0xC) (sepFF 0x18 0xC (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x14) (b := F + 0xC) (sepFF 0x14 0xC (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x10) (b := F + 0xC) (sepFF 0x10 0xC (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_same]
    exact uX1.self.zero
  have W16 : memLoad32 mX2.mem (F + 0x10) = feNegZ (limbs m.mem ip) 2 := by
    rw [u2.mem]
    rw [memLoad32_store32_sep (a := F + 0x4C) (b := F + 0x10) (sepFF 0x4C 0x10 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x48) (b := F + 0x10) (sepFF 0x48 0x10 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x44) (b := F + 0x10) (sepFF 0x44 0x10 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x40) (b := F + 0x10) (sepFF 0x40 0x10 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x3C) (b := F + 0x10) (sepFF 0x3C 0x10 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x38) (b := F + 0x10) (sepFF 0x38 0x10 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x34) (b := F + 0x10) (sepFF 0x34 0x10 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x30) (b := F + 0x10) (sepFF 0x30 0x10 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x2C) (b := F + 0x10) (sepFF 0x2C 0x10 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x28) (b := F + 0x10) (sepFF 0x28 0x10 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x24) (b := F + 0x10) (sepFF 0x24 0x10 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x20) (b := F + 0x10) (sepFF 0x20 0x10 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x1C) (b := F + 0x10) (sepFF 0x1C 0x10 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x18) (b := F + 0x10) (sepFF 0x18 0x10 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x14) (b := F + 0x10) (sepFF 0x14 0x10 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_same]
    exact XV2
  have W20 : memLoad32 mX2.mem (F + 0x14) = 0 := by
    rw [u2.mem]
    rw [memLoad32_store32_sep (a := F + 0x4C) (b := F + 0x14) (sepFF 0x4C 0x14 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x48) (b := F + 0x14) (sepFF 0x48 0x14 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x44) (b := F + 0x14) (sepFF 0x44 0x14 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x40) (b := F + 0x14) (sepFF 0x40 0x14 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x3C) (b := F + 0x14) (sepFF 0x3C 0x14 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x38) (b := F + 0x14) (sepFF 0x38 0x14 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x34) (b := F + 0x14) (sepFF 0x34 0x14 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x30) (b := F + 0x14) (sepFF 0x30 0x14 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x2C) (b := F + 0x14) (sepFF 0x2C 0x14 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x28) (b := F + 0x14) (sepFF 0x28 0x14 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x24) (b := F + 0x14) (sepFF 0x24 0x14 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x20) (b := F + 0x14) (sepFF 0x20 0x14 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x1C) (b := F + 0x14) (sepFF 0x1C 0x14 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x18) (b := F + 0x14) (sepFF 0x18 0x14 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_same]
    exact uX1.self.zero
  have W24 : memLoad32 mX2.mem (F + 0x18) = feNegZ (limbs m.mem ip) 3 := by
    rw [u2.mem]
    rw [memLoad32_store32_sep (a := F + 0x4C) (b := F + 0x18) (sepFF 0x4C 0x18 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x48) (b := F + 0x18) (sepFF 0x48 0x18 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x44) (b := F + 0x18) (sepFF 0x44 0x18 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x40) (b := F + 0x18) (sepFF 0x40 0x18 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x3C) (b := F + 0x18) (sepFF 0x3C 0x18 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x38) (b := F + 0x18) (sepFF 0x38 0x18 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x34) (b := F + 0x18) (sepFF 0x34 0x18 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x30) (b := F + 0x18) (sepFF 0x30 0x18 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x2C) (b := F + 0x18) (sepFF 0x2C 0x18 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x28) (b := F + 0x18) (sepFF 0x28 0x18 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x24) (b := F + 0x18) (sepFF 0x24 0x18 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x20) (b := F + 0x18) (sepFF 0x20 0x18 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x1C) (b := F + 0x18) (sepFF 0x1C 0x18 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_same]
    exact XV3
  have W28 : memLoad32 mX2.mem (F + 0x1C) = 0 := by
    rw [u2.mem]
    rw [memLoad32_store32_sep (a := F + 0x4C) (b := F + 0x1C) (sepFF 0x4C 0x1C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x48) (b := F + 0x1C) (sepFF 0x48 0x1C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x44) (b := F + 0x1C) (sepFF 0x44 0x1C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x40) (b := F + 0x1C) (sepFF 0x40 0x1C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x3C) (b := F + 0x1C) (sepFF 0x3C 0x1C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x38) (b := F + 0x1C) (sepFF 0x38 0x1C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x34) (b := F + 0x1C) (sepFF 0x34 0x1C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x30) (b := F + 0x1C) (sepFF 0x30 0x1C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x2C) (b := F + 0x1C) (sepFF 0x2C 0x1C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x28) (b := F + 0x1C) (sepFF 0x28 0x1C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x24) (b := F + 0x1C) (sepFF 0x24 0x1C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x20) (b := F + 0x1C) (sepFF 0x20 0x1C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_same]
    exact uX1.self.zero
  have W32 : memLoad32 mX2.mem (F + 0x20) = feNegZ (limbs m.mem ip) 4 := by
    rw [u2.mem]
    rw [memLoad32_store32_sep (a := F + 0x4C) (b := F + 0x20) (sepFF 0x4C 0x20 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x48) (b := F + 0x20) (sepFF 0x48 0x20 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x44) (b := F + 0x20) (sepFF 0x44 0x20 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x40) (b := F + 0x20) (sepFF 0x40 0x20 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x3C) (b := F + 0x20) (sepFF 0x3C 0x20 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x38) (b := F + 0x20) (sepFF 0x38 0x20 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x34) (b := F + 0x20) (sepFF 0x34 0x20 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x30) (b := F + 0x20) (sepFF 0x30 0x20 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x2C) (b := F + 0x20) (sepFF 0x2C 0x20 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x28) (b := F + 0x20) (sepFF 0x28 0x20 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x24) (b := F + 0x20) (sepFF 0x24 0x20 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_same]
    exact XV4
  have W36 : memLoad32 mX2.mem (F + 0x24) = 0 := by
    rw [u2.mem]
    rw [memLoad32_store32_sep (a := F + 0x4C) (b := F + 0x24) (sepFF 0x4C 0x24 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x48) (b := F + 0x24) (sepFF 0x48 0x24 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x44) (b := F + 0x24) (sepFF 0x44 0x24 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x40) (b := F + 0x24) (sepFF 0x40 0x24 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x3C) (b := F + 0x24) (sepFF 0x3C 0x24 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x38) (b := F + 0x24) (sepFF 0x38 0x24 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x34) (b := F + 0x24) (sepFF 0x34 0x24 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x30) (b := F + 0x24) (sepFF 0x30 0x24 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x2C) (b := F + 0x24) (sepFF 0x2C 0x24 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x28) (b := F + 0x24) (sepFF 0x28 0x24 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_same]
    exact uX1.self.zero
  have W40 : memLoad32 mX2.mem (F + 0x28) = feNegZ (limbs m.mem ip) 5 := by
    rw [u2.mem]
    rw [memLoad32_store32_sep (a := F + 0x4C) (b := F + 0x28) (sepFF 0x4C 0x28 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x48) (b := F + 0x28) (sepFF 0x48 0x28 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x44) (b := F + 0x28) (sepFF 0x44 0x28 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x40) (b := F + 0x28) (sepFF 0x40 0x28 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x3C) (b := F + 0x28) (sepFF 0x3C 0x28 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x38) (b := F + 0x28) (sepFF 0x38 0x28 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x34) (b := F + 0x28) (sepFF 0x34 0x28 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x30) (b := F + 0x28) (sepFF 0x30 0x28 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x2C) (b := F + 0x28) (sepFF 0x2C 0x28 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_same]
    exact XV5
  have W44 : memLoad32 mX2.mem (F + 0x2C) = 0 := by
    rw [u2.mem]
    rw [memLoad32_store32_sep (a := F + 0x4C) (b := F + 0x2C) (sepFF 0x4C 0x2C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x48) (b := F + 0x2C) (sepFF 0x48 0x2C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x44) (b := F + 0x2C) (sepFF 0x44 0x2C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x40) (b := F + 0x2C) (sepFF 0x40 0x2C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x3C) (b := F + 0x2C) (sepFF 0x3C 0x2C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x38) (b := F + 0x2C) (sepFF 0x38 0x2C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x34) (b := F + 0x2C) (sepFF 0x34 0x2C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x30) (b := F + 0x2C) (sepFF 0x30 0x2C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_same]
    exact uX1.self.zero
  have W48 : memLoad32 mX2.mem (F + 0x30) = feNegZ (limbs m.mem ip) 6 := by
    rw [u2.mem]
    rw [memLoad32_store32_sep (a := F + 0x4C) (b := F + 0x30) (sepFF 0x4C 0x30 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x48) (b := F + 0x30) (sepFF 0x48 0x30 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x44) (b := F + 0x30) (sepFF 0x44 0x30 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x40) (b := F + 0x30) (sepFF 0x40 0x30 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x3C) (b := F + 0x30) (sepFF 0x3C 0x30 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x38) (b := F + 0x30) (sepFF 0x38 0x30 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x34) (b := F + 0x30) (sepFF 0x34 0x30 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_same]
    exact XV6
  have W52 : memLoad32 mX2.mem (F + 0x34) = 0 := by
    rw [u2.mem]
    rw [memLoad32_store32_sep (a := F + 0x4C) (b := F + 0x34) (sepFF 0x4C 0x34 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x48) (b := F + 0x34) (sepFF 0x48 0x34 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x44) (b := F + 0x34) (sepFF 0x44 0x34 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x40) (b := F + 0x34) (sepFF 0x40 0x34 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x3C) (b := F + 0x34) (sepFF 0x3C 0x34 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x38) (b := F + 0x34) (sepFF 0x38 0x34 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_same]
    exact uX1.self.zero
  have W56 : memLoad32 mX2.mem (F + 0x38) = feNegZ (limbs m.mem ip) 7 := by
    rw [u2.mem]
    rw [memLoad32_store32_sep (a := F + 0x4C) (b := F + 0x38) (sepFF 0x4C 0x38 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x48) (b := F + 0x38) (sepFF 0x48 0x38 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x44) (b := F + 0x38) (sepFF 0x44 0x38 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x40) (b := F + 0x38) (sepFF 0x40 0x38 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x3C) (b := F + 0x38) (sepFF 0x3C 0x38 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_same]
    exact XV7
  have W60 : memLoad32 mX2.mem (F + 0x3C) = 0 := by
    rw [u2.mem]
    rw [memLoad32_store32_sep (a := F + 0x4C) (b := F + 0x3C) (sepFF 0x4C 0x3C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x48) (b := F + 0x3C) (sepFF 0x48 0x3C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x44) (b := F + 0x3C) (sepFF 0x44 0x3C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x40) (b := F + 0x3C) (sepFF 0x40 0x3C (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_same]
    exact uX1.self.zero
  have W64 : memLoad32 mX2.mem (F + 0x40) = feNegZ (limbs m.mem ip) 8 := by
    rw [u2.mem]
    rw [memLoad32_store32_sep (a := F + 0x4C) (b := F + 0x40) (sepFF 0x4C 0x40 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x48) (b := F + 0x40) (sepFF 0x48 0x40 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x44) (b := F + 0x40) (sepFF 0x44 0x40 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_same]
    exact XV8
  have W68 : memLoad32 mX2.mem (F + 0x44) = 0 := by
    rw [u2.mem]
    rw [memLoad32_store32_sep (a := F + 0x4C) (b := F + 0x44) (sepFF 0x4C 0x44 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_sep (a := F + 0x48) (b := F + 0x44) (sepFF 0x48 0x44 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_same]
    exact uX1.self.zero
  have W72 : memLoad32 mX2.mem (F + 0x48) = feNegZ (limbs m.mem ip) 9 := by
    rw [u2.mem]
    rw [memLoad32_store32_sep (a := F + 0x4C) (b := F + 0x48) (sepFF 0x4C 0x48 (.inr (by decide)) (by decide) (by decide))]
    rw [memLoad32_store32_same]
    exact XV9
  have W76 : memLoad32 mX2.mem (F + 0x4C) = 0 := by
    rw [u2.mem]
    rw [memLoad32_store32_same]
    exact uX1.self.zero
  have fX2 : ∀ x, Sep G 0xA0 x 1 → mX2.mem x = m.mem x := fun x hx => by
    rw [u2.mem, memStore32_get_sep (a := F + 0x4C) (tX 0x4C (by decide) hx), memStore32_get_sep (a := F + 0x48) (tX 0x48 (by decide) hx), memStore32_get_sep (a := F + 0x44) (tX 0x44 (by decide) hx), memStore32_get_sep (a := F + 0x40) (tX 0x40 (by decide) hx), memStore32_get_sep (a := F + 0x3C) (tX 0x3C (by decide) hx), memStore32_get_sep (a := F + 0x38) (tX 0x38 (by decide) hx), memStore32_get_sep (a := F + 0x34) (tX 0x34 (by decide) hx), memStore32_get_sep (a := F + 0x30) (tX 0x30 (by decide) hx), memStore32_get_sep (a := F + 0x2C) (tX 0x2C (by decide) hx), memStore32_get_sep (a := F + 0x28) (tX 0x28 (by decide) hx), memStore32_get_sep (a := F + 0x24) (tX 0x24 (by decide) hx), memStore32_get_sep (a := F + 0x20) (tX 0x20 (by decide) hx), memStore32_get_sep (a := F + 0x1C) (tX 0x1C (by decide) hx), memStore32_get_sep (a := F + 0x18) (tX 0x18 (by decide) hx), memStore32_get_sep (a := F + 0x14) (tX 0x14 (by decide) hx), memStore32_get_sep (a := F + 0x10) (tX 0x10 (by decide) hx), memStore32_get_sep (a := F + 0xC) (tX 0xC (by decide) hx), memStore32_get_sep (a := F + 0x8) (tX 0x8 (by decide) hx), memStore32_get_sep (a := F + 0x4) (tX 0x4 (by decide) hx), memStore32_get_sep (a := F + 0x0) (tX 0x0 (by decide) hx)]
    exact frSv x hx
  have tS1 : ∀ j k, j + 4 ≤ k → k < 0x80 → Sep (F + BitVec.ofNat 32 j) 4 (F + BitVec.ofNat 32 k) 1 :=
    fun j k h1 h2 => by rw [eFk, eFk]; exact offs (.inl (by omega)) (by omega) (by omega)
  have slX2 : ∀ k, 0x78 ≤ k → k < 0x80 → mX2.mem (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) :=
    fun k h1 h2 => by rw [u2.mem, memStore32_get_sep (a := F + 0x4C) (tS1 0x4C k (by omega) h2), memStore32_get_sep (a := F + 0x48) (tS1 0x48 k (by omega) h2), memStore32_get_sep (a := F + 0x44) (tS1 0x44 k (by omega) h2), memStore32_get_sep (a := F + 0x40) (tS1 0x40 k (by omega) h2), memStore32_get_sep (a := F + 0x3C) (tS1 0x3C k (by omega) h2), memStore32_get_sep (a := F + 0x38) (tS1 0x38 k (by omega) h2), memStore32_get_sep (a := F + 0x34) (tS1 0x34 k (by omega) h2), memStore32_get_sep (a := F + 0x30) (tS1 0x30 k (by omega) h2), memStore32_get_sep (a := F + 0x2C) (tS1 0x2C k (by omega) h2), memStore32_get_sep (a := F + 0x28) (tS1 0x28 k (by omega) h2), memStore32_get_sep (a := F + 0x24) (tS1 0x24 k (by omega) h2), memStore32_get_sep (a := F + 0x20) (tS1 0x20 k (by omega) h2), memStore32_get_sep (a := F + 0x1C) (tS1 0x1C k (by omega) h2), memStore32_get_sep (a := F + 0x18) (tS1 0x18 k (by omega) h2), memStore32_get_sep (a := F + 0x14) (tS1 0x14 k (by omega) h2), memStore32_get_sep (a := F + 0x10) (tS1 0x10 k (by omega) h2), memStore32_get_sep (a := F + 0xC) (tS1 0xC k (by omega) h2), memStore32_get_sep (a := F + 0x8) (tS1 0x8 k (by omega) h2), memStore32_get_sep (a := F + 0x4) (tS1 0x4 k (by omega) h2), memStore32_get_sep (a := F + 0x0) (tS1 0x0 k (by omega) h2)]
  have hcX2 : CodeIn mX2.mem P feNegCode := cIn env.cod sGC fX2
  have uX2' : St mX2.mem P mX2 0x86 (reg mX2) := ⟨u2.pc, rfl, fun _ => rfl⟩
  have rX2 : ∀ q, reg mX2 q = reg mX1 q := u2.regs
  obtain ⟨mX3, cX3, uX3⟩ := St.block fngX3 uX2' hcX2 fngX3_end (by simp [BlockOk, BInstr.ok, fngX3])
  simp only [runBlock, BInstr.run, fngX3] at uX3
  obtain ⟨mc, cc, pcc, memc, regsc⟩ := uX3.self.callRa hcX2 fng_at_8a fng_at_8e (cb := P + 0xFFFFE370)
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFE370 (by decide))
  have rc := PEnv.reg1 regsc uX3.self.zero
  have spX3 : reg mX3 sp = F := by rw [uX3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rX2, spX1]
  have spc : reg mc sp = F := by rw [rc sp (by decide), spX3]
  have fenv : FREnv mc.mem (P + 0xFFFFE370) F (F + 0x50) F := by
    rw [memc]
    refine ⟨even_at P env.hP 0xFFFFE370 (by decide), cIn env.red sGR fX2, hFa, by omega,
      aligned_add hFa (k := 0x50) (by decide), hFa, by rw [eFr]; have := sGR.sub (c := 0) (l := 0x20) (by decide); rwa [add_ofNat_zero] at this, by rw [eF50]; exact sGR.sub (by decide),
      ?_, ?_⟩
    · rw [eFr, eF50]; have := offs (c := 0x70) (n := 40) (d := 0) (k := 0x20) (.inr (by decide)) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
    · rw [eFr, ← hGF]; have := offs (c := 0x20) (n := 80) (d := 0) (k := 0x20) (.inr (by decide)) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
  obtain ⟨mr, cr, pcr, spr, kr, wr, fr⟩ := feReduce_correct mc fenv pcc
    (by rw [rc a0 (by decide), uX3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rX2, spX1]; rfl)
    (by rw [rc a1 (by decide), uX3.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [rX2, spX1]; exact zw _)
    (by rw [regsc]; simp +decide [upd]) (even_clear _ (even_at P env.hP (0x8A + 8) (by decide))) spc
  rw [memc] at wr fr
  have U0 : u64At mX2.mem F 0 = (feNegZ (limbs m.mem ip) 0).toNat := by
    show (memLoad32 mX2.mem (F + 0x0)).toNat + 2 ^ 32 * (memLoad32 mX2.mem (F + 0x4)).toNat = _
    rw [W0, W4, show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  have U1 : u64At mX2.mem F 1 = (feNegZ (limbs m.mem ip) 1).toNat := by
    show (memLoad32 mX2.mem (F + 0x8)).toNat + 2 ^ 32 * (memLoad32 mX2.mem (F + 0xC)).toNat = _
    rw [W8, W12, show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  have U2 : u64At mX2.mem F 2 = (feNegZ (limbs m.mem ip) 2).toNat := by
    show (memLoad32 mX2.mem (F + 0x10)).toNat + 2 ^ 32 * (memLoad32 mX2.mem (F + 0x14)).toNat = _
    rw [W16, W20, show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  have U3 : u64At mX2.mem F 3 = (feNegZ (limbs m.mem ip) 3).toNat := by
    show (memLoad32 mX2.mem (F + 0x18)).toNat + 2 ^ 32 * (memLoad32 mX2.mem (F + 0x1C)).toNat = _
    rw [W24, W28, show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  have U4 : u64At mX2.mem F 4 = (feNegZ (limbs m.mem ip) 4).toNat := by
    show (memLoad32 mX2.mem (F + 0x20)).toNat + 2 ^ 32 * (memLoad32 mX2.mem (F + 0x24)).toNat = _
    rw [W32, W36, show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  have U5 : u64At mX2.mem F 5 = (feNegZ (limbs m.mem ip) 5).toNat := by
    show (memLoad32 mX2.mem (F + 0x28)).toNat + 2 ^ 32 * (memLoad32 mX2.mem (F + 0x2C)).toNat = _
    rw [W40, W44, show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  have U6 : u64At mX2.mem F 6 = (feNegZ (limbs m.mem ip) 6).toNat := by
    show (memLoad32 mX2.mem (F + 0x30)).toNat + 2 ^ 32 * (memLoad32 mX2.mem (F + 0x34)).toNat = _
    rw [W48, W52, show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  have U7 : u64At mX2.mem F 7 = (feNegZ (limbs m.mem ip) 7).toNat := by
    show (memLoad32 mX2.mem (F + 0x38)).toNat + 2 ^ 32 * (memLoad32 mX2.mem (F + 0x3C)).toNat = _
    rw [W56, W60, show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  have U8 : u64At mX2.mem F 8 = (feNegZ (limbs m.mem ip) 8).toNat := by
    show (memLoad32 mX2.mem (F + 0x40)).toNat + 2 ^ 32 * (memLoad32 mX2.mem (F + 0x44)).toNat = _
    rw [W64, W68, show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  have U9 : u64At mX2.mem F 9 = (feNegZ (limbs m.mem ip) 9).toNat := by
    show (memLoad32 mX2.mem (F + 0x48)).toNat + 2 ^ 32 * (memLoad32 mX2.mem (F + 0x4C)).toNat = _
    rw [W72, W76, show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  rw [U0, U1, U2, U3, U4, U5, U6, U7, U8, U9] at wr
  have spr' : reg mr sp = F := by rw [spr]
  have frG : ∀ x, Sep G 0xA0 x 1 → mr.mem x = m.mem x := fun x hx => by
    rw [fr x (by rw [eFr]; exact hx.sub (c := 0) (l := 0x20) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)
      (by rw [eF50]; exact hx.sub (by decide)), fX2 x hx]
  have slr : ∀ k, 0x78 ≤ k → k < 0x80 → mr.mem (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) :=
    fun k h1 h2 => by
      have e1 : Sep (F + 0xFFFFFFE0) 0x20 (F + BitVec.ofNat 32 k) 1 := by
        rw [eFr, eFk]
        have := offs (c := 0) (n := 0x20) (d := 0x20 + k) (k := 1) (.inl (by omega)) (by decide) (by omega)
        rwa [add_ofNat_zero] at this
      have e2 : Sep (F + 0x50) 40 (F + BitVec.ofNat 32 k) 1 := by
        rw [eF50, eFk]; exact offs (.inl (by omega)) (by decide) (by omega)
      rw [fr _ e1 e2, slX2 k h1 h2]
  have hcr : CodeIn mr.mem P feNegCode := cIn env.cod sGC frG
  have ur : St mr.mem P mr 0x92 (reg mr) := ⟨by rw [pcr], rfl, fun _ => rfl⟩
  -- copy the reduced limbs out
  obtain ⟨mY1, cY1, uY1⟩ := St.block fngY1 ur hcr fngY1_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, fngY1, upd_app, ↓reduceIte, and_true]
    rw [spr']
    repeat' apply And.intro
    all_goals first | trivial | (refine aligned_add hFa ?_; decide))
  simp only [runBlock, BInstr.run, fngY1] at uY1
  have YV0 : reg mY1 a0 = memLoad32 mr.mem (F + 0x50) := by
    rw [uY1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [spr']
  have YV1 : reg mY1 a1 = memLoad32 mr.mem (F + 0x54) := by
    rw [uY1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [spr']
  have YV2 : reg mY1 a2 = memLoad32 mr.mem (F + 0x58) := by
    rw [uY1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [spr']
  have YV3 : reg mY1 a3 = memLoad32 mr.mem (F + 0x5C) := by
    rw [uY1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [spr']
  have YV4 : reg mY1 a4 = memLoad32 mr.mem (F + 0x60) := by
    rw [uY1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [spr']
  have YV5 : reg mY1 a5 = memLoad32 mr.mem (F + 0x64) := by
    rw [uY1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [spr']
  have YV6 : reg mY1 a6 = memLoad32 mr.mem (F + 0x68) := by
    rw [uY1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [spr']
  have YV7 : reg mY1 (17 : Fin 32) = memLoad32 mr.mem (F + 0x6C) := by
    rw [uY1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [spr']
  have YV8 : reg mY1 (5 : Fin 32) = memLoad32 mr.mem (F + 0x70) := by
    rw [uY1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [spr']
  have YV9 : reg mY1 (6 : Fin 32) = memLoad32 mr.mem (F + 0x74) := by
    rw [uY1.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [spr']
  have s0r : reg mr 8 = out := by
    rw [kr 8 (by decide), rc 8 (by decide), uX3.regs]; simp +decide only [upd_app, ↓reduceIte]
    rw [rX2, rX]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, r2 a0 (by decide), ha0]
    first | exact zw _ | (rw [us.self.zero]; exact zw _)
  have s0Y1 : reg mY1 8 = out := by rw [uY1.regs]; simp +decide only [upd_app, ↓reduceIte]; exact s0r
  obtain ⟨mY2, cY2, uy2⟩ := St.block fngY2 uY1.self hcr fngY2_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, fngY2, and_true]
    rw [s0Y1]
    repeat' apply And.intro
    all_goals first | trivial | (refine aligned_add env.hout ?_; decide) | exact env.sOC.sub (by decide))
  simp only [runBlock, BInstr.run, fngY2] at uy2
  rw [s0Y1] at uy2
  have wY : wordsAt mY2.mem out 10 = wordsAt mr.mem (F + 0x50) 10 := by
    apply wordsAt_congr2
    intro i hi
    match i, hi with
    | 0, _ =>
      show memLoad32 mY2.mem (out + 0x0) = memLoad32 mr.mem (F + 0x50 + 0x0)
      rw [uy2.mem]
      rw [memLoad32_store32_sep (a := out + 0x24) (b := out + 0x0) (sepOO 0x24 0x0 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x20) (b := out + 0x0) (sepOO 0x20 0x0 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x1C) (b := out + 0x0) (sepOO 0x1C 0x0 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x18) (b := out + 0x0) (sepOO 0x18 0x0 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x14) (b := out + 0x0) (sepOO 0x14 0x0 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x10) (b := out + 0x0) (sepOO 0x10 0x0 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0xC) (b := out + 0x0) (sepOO 0xC 0x0 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x8) (b := out + 0x0) (sepOO 0x8 0x0 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x4) (b := out + 0x0) (sepOO 0x4 0x0 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_same]
      rw [show F + 0x50 + 0x0 = F + 0x50 by rw [BitVec.add_assoc]; rfl]
      exact YV0
    | 1, _ =>
      show memLoad32 mY2.mem (out + 0x4) = memLoad32 mr.mem (F + 0x50 + 0x4)
      rw [uy2.mem]
      rw [memLoad32_store32_sep (a := out + 0x24) (b := out + 0x4) (sepOO 0x24 0x4 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x20) (b := out + 0x4) (sepOO 0x20 0x4 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x1C) (b := out + 0x4) (sepOO 0x1C 0x4 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x18) (b := out + 0x4) (sepOO 0x18 0x4 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x14) (b := out + 0x4) (sepOO 0x14 0x4 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x10) (b := out + 0x4) (sepOO 0x10 0x4 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0xC) (b := out + 0x4) (sepOO 0xC 0x4 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x8) (b := out + 0x4) (sepOO 0x8 0x4 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_same]
      rw [show F + 0x50 + 0x4 = F + 0x54 by rw [BitVec.add_assoc]; rfl]
      exact YV1
    | 2, _ =>
      show memLoad32 mY2.mem (out + 0x8) = memLoad32 mr.mem (F + 0x50 + 0x8)
      rw [uy2.mem]
      rw [memLoad32_store32_sep (a := out + 0x24) (b := out + 0x8) (sepOO 0x24 0x8 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x20) (b := out + 0x8) (sepOO 0x20 0x8 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x1C) (b := out + 0x8) (sepOO 0x1C 0x8 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x18) (b := out + 0x8) (sepOO 0x18 0x8 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x14) (b := out + 0x8) (sepOO 0x14 0x8 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x10) (b := out + 0x8) (sepOO 0x10 0x8 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0xC) (b := out + 0x8) (sepOO 0xC 0x8 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_same]
      rw [show F + 0x50 + 0x8 = F + 0x58 by rw [BitVec.add_assoc]; rfl]
      exact YV2
    | 3, _ =>
      show memLoad32 mY2.mem (out + 0xC) = memLoad32 mr.mem (F + 0x50 + 0xC)
      rw [uy2.mem]
      rw [memLoad32_store32_sep (a := out + 0x24) (b := out + 0xC) (sepOO 0x24 0xC (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x20) (b := out + 0xC) (sepOO 0x20 0xC (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x1C) (b := out + 0xC) (sepOO 0x1C 0xC (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x18) (b := out + 0xC) (sepOO 0x18 0xC (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x14) (b := out + 0xC) (sepOO 0x14 0xC (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x10) (b := out + 0xC) (sepOO 0x10 0xC (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_same]
      rw [show F + 0x50 + 0xC = F + 0x5C by rw [BitVec.add_assoc]; rfl]
      exact YV3
    | 4, _ =>
      show memLoad32 mY2.mem (out + 0x10) = memLoad32 mr.mem (F + 0x50 + 0x10)
      rw [uy2.mem]
      rw [memLoad32_store32_sep (a := out + 0x24) (b := out + 0x10) (sepOO 0x24 0x10 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x20) (b := out + 0x10) (sepOO 0x20 0x10 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x1C) (b := out + 0x10) (sepOO 0x1C 0x10 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x18) (b := out + 0x10) (sepOO 0x18 0x10 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x14) (b := out + 0x10) (sepOO 0x14 0x10 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_same]
      rw [show F + 0x50 + 0x10 = F + 0x60 by rw [BitVec.add_assoc]; rfl]
      exact YV4
    | 5, _ =>
      show memLoad32 mY2.mem (out + 0x14) = memLoad32 mr.mem (F + 0x50 + 0x14)
      rw [uy2.mem]
      rw [memLoad32_store32_sep (a := out + 0x24) (b := out + 0x14) (sepOO 0x24 0x14 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x20) (b := out + 0x14) (sepOO 0x20 0x14 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x1C) (b := out + 0x14) (sepOO 0x1C 0x14 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x18) (b := out + 0x14) (sepOO 0x18 0x14 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_same]
      rw [show F + 0x50 + 0x14 = F + 0x64 by rw [BitVec.add_assoc]; rfl]
      exact YV5
    | 6, _ =>
      show memLoad32 mY2.mem (out + 0x18) = memLoad32 mr.mem (F + 0x50 + 0x18)
      rw [uy2.mem]
      rw [memLoad32_store32_sep (a := out + 0x24) (b := out + 0x18) (sepOO 0x24 0x18 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x20) (b := out + 0x18) (sepOO 0x20 0x18 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x1C) (b := out + 0x18) (sepOO 0x1C 0x18 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_same]
      rw [show F + 0x50 + 0x18 = F + 0x68 by rw [BitVec.add_assoc]; rfl]
      exact YV6
    | 7, _ =>
      show memLoad32 mY2.mem (out + 0x1C) = memLoad32 mr.mem (F + 0x50 + 0x1C)
      rw [uy2.mem]
      rw [memLoad32_store32_sep (a := out + 0x24) (b := out + 0x1C) (sepOO 0x24 0x1C (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_sep (a := out + 0x20) (b := out + 0x1C) (sepOO 0x20 0x1C (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_same]
      rw [show F + 0x50 + 0x1C = F + 0x6C by rw [BitVec.add_assoc]; rfl]
      exact YV7
    | 8, _ =>
      show memLoad32 mY2.mem (out + 0x20) = memLoad32 mr.mem (F + 0x50 + 0x20)
      rw [uy2.mem]
      rw [memLoad32_store32_sep (a := out + 0x24) (b := out + 0x20) (sepOO 0x24 0x20 (.inr (by decide)) (by decide) (by decide))]
      rw [memLoad32_store32_same]
      rw [show F + 0x50 + 0x20 = F + 0x70 by rw [BitVec.add_assoc]; rfl]
      exact YV8
    | 9, _ =>
      show memLoad32 mY2.mem (out + 0x24) = memLoad32 mr.mem (F + 0x50 + 0x24)
      rw [uy2.mem]
      rw [memLoad32_store32_same]
      rw [show F + 0x50 + 0x24 = F + 0x74 by rw [BitVec.add_assoc]; rfl]
      exact YV9
  have oS1 : ∀ k, k + 4 ≤ 40 → ∀ z, Sep out 40 z 1 → Sep (out + BitVec.ofNat 32 k) 4 z 1 := fun k h z hz => hz.sub h
  have fY : ∀ z, Sep out 40 z 1 → mY2.mem z = mr.mem z := fun z hz => by rw [uy2.mem, memStore32_get_sep (a := out + 0x24) (oS1 0x24 (by decide) z hz), memStore32_get_sep (a := out + 0x20) (oS1 0x20 (by decide) z hz), memStore32_get_sep (a := out + 0x1C) (oS1 0x1C (by decide) z hz), memStore32_get_sep (a := out + 0x18) (oS1 0x18 (by decide) z hz), memStore32_get_sep (a := out + 0x14) (oS1 0x14 (by decide) z hz), memStore32_get_sep (a := out + 0x10) (oS1 0x10 (by decide) z hz), memStore32_get_sep (a := out + 0xC) (oS1 0xC (by decide) z hz), memStore32_get_sep (a := out + 0x8) (oS1 0x8 (by decide) z hz), memStore32_get_sep (a := out + 0x4) (oS1 0x4 (by decide) z hz), memStore32_get_sep (a := out + 0x0) (oS1 0x0 (by decide) z hz)]
  have slY : ∀ k, 0x78 ≤ k → k < 0x80 → mY2.mem (F + BitVec.ofNat 32 k) = Msv (F + BitVec.ofNat 32 k) :=
    fun k h1 h2 => by
      rw [fY _ ((sOG.subR (c := 0x20 + k) (l := 1) (by omega)) |> fun h => by rwa [← eFk] at h), slr k h1 h2]
  have hcY : CodeIn mY2.mem P feNegCode := fun i hi => by
    rw [fY _ (env.sOC.subR (c := i) (l := 1) (by omega))]; exact hcr i hi
  have uY2' : St mY2.mem P mY2 0xC2 (reg mY2) := ⟨uy2.pc, rfl, fun _ => rfl⟩
  have spY : reg mY2 sp = F := by rw [uy2.regs, uY1.regs]; simp +decide only [upd_app, ↓reduceIte]; exact spr'
  have hpsp : ∀ p ∈ negPs, p.1 ≠ sp := by decide
  obtain ⟨e1, ce1, ue1⟩ := St.block (restoreBlock negPs) uY2' hcY negRestore_end
    (restoreBlock_ok mY2.mem F negPs _ spY hpsp fun q hq => by
      simp only [negPs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl <;> exact aligned_add hFa (by decide))
  simp only [restoreBlock_run mY2.mem F negPs _ spY hpsp] at ue1
  obtain ⟨e2, de2, ue2⟩ := ue1.aluImm hcY fng_at_c6 (off' := 0xC8) (by decide)
  obtain ⟨e3, de3, pc3, mem3, regs3⟩ := ue2.jalr hcY fng_at_c8
  have slotW : ∀ r o, (r, o) ∈ negPs → memLoad32 mY2.mem (F + o) = reg m r := fun r o h => by
    have ho : 0x78 ≤ o.toNat ∧ o.toNat + 4 ≤ 0x80 := by
      simp only [negPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hslv r o h]
    apply memLoad32_congr; intro j hj
    rw [← ofNat_toNat_self o, add_ofNat_assoc, slY _ (by omega) (by omega)]
  have rr : ∀ (f : Fin 32 → Word) (ps : List (Fin 32 × Word)) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs mY2.mem F f ps q = f q := by
    intro f ps q h0
    induction ps generalizing f with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro h
      simp only [restoreRegs]
      rw [ih _ (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')), upd_ne h0 (fun e => h p List.mem_cons_self e.symm)]
  have hreg : ∀ r o, (r, o) ∈ negPs → restoreRegs mY2.mem F (reg mY2) negPs r = reg m r := fun r o hm => by
    simp only [negPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      exact slotW _ _ (by decide)
  have rsp : restoreRegs mY2.mem F (reg mY2) negPs sp = F := by rw [rr _ _ sp (by decide) (by decide)]; exact spY
  have keepY : ∀ q, q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg mY2 q = reg m q := fun q hq => by
    have h : q.val ≠ 0 ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ a6 ∧ q ≠ a7 ∧ q ≠ 5 ∧ q ≠ 6 ∧
        q ≠ 7 ∧ q ≠ 28 ∧ q ≠ 29 ∧ q ≠ 30 ∧ q ≠ 8 ∧ q ≠ ra ∧ q ≠ sp ∧ frKeep q = true := by revert hq; revert q; decide
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
    rw [uy2.regs, uY1.regs]
    simp only [upd_ne h0 h1, upd_ne h0 h2, upd_ne h0 h3, upd_ne h0 h4, upd_ne h0 h5, upd_ne h0 h6, upd_ne h0 h7,
      upd_ne h0 h8, upd_ne h0 h9, upd_ne h0 h10]
    rw [kr q h18, rc q h16, uX3.regs]
    simp only [upd_ne h0 h1, upd_ne h0 h2]
    rw [rX2, rX]
    simp only [upd_ne h0 h1, upd_ne h0 h2, upd_ne h0 h3, upd_ne h0 h4, upd_ne h0 h5, upd_ne h0 h6, upd_ne h0 h7,
      upd_ne h0 h8, upd_ne h0 h9, upd_ne h0 h10, upd_ne h0 h11, upd_ne h0 h12, upd_ne h0 h13, upd_ne h0 h14,
      upd_ne h0 h15]
    exact r2 q h17
  have S : Steps m mY2 := .cons d1 (cs.trans (cX1.trans (cX2.trans (cX3.trans (cc.trans (cr.trans (cY1.trans cY2)))))))
  refine ⟨e3, S.trans (ce1.trans (.cons de2 (.single de3))), ?_, ?_, fun q hq => ?_, ?_, fun x hx ho => ?_⟩
  · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]; rw [hreg ra 0x7C (by decide), hra, add_lit_zero, hret]
  · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, rsp, eS]
  · rw [regs3]
    have key : ∀ q : Fin 32, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        q = ra ∨ q = (8 : Fin 32) ∨ (q.val ∈ [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] ∧ q.val ≠ 0 ∧
          q ≠ sp ∧ (∀ p ∈ negPs, p.1 ≠ q)) := by decide
    rcases key q hq with rfl | rfl | ⟨h1, h0, hs, hps⟩
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x7C (by decide)
    · simp +decide only [upd_app, ↓reduceIte]; exact hreg _ 0x78 (by decide)
    · rw [upd_ne h0 hs, rr _ _ q h0 hps]; exact keepY q h1
  · rw [mem3, wY]; exact wr
  · rw [mem3, fY x ho, frG x hx]

end C3.RV32
