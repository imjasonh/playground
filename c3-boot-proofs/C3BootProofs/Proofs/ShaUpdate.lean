import C3BootProofs.Proofs.Sha256Compress
import C3BootProofs.Proofs.MemcpyAny
import C3BootProofs.Proofs.ShaStream
import C3BootProofs.Proofs.FieldMul

/-!
# SHA-256's `update`

The compiled `<sha2::Sha256 as digest::Update>::update` keeps the hasher as
0x68 bytes: a 64-byte buffer whose last byte holds how many bytes of it are
in use, the 8 hash words, and a 64-bit count of the blocks compressed. It
appends the new bytes to the buffer, compresses the buffer when it fills,
compresses whole blocks of the new bytes in place, and buffers the rest.

`shaBlocks_correct` covers the helper that adds to the block count and
compresses: a tail call into `compress256`, so it runs through
`sha256Compress_correct`.
-/

namespace C3.RV32

open C3.Image

set_option maxRecDepth 40000 in
/-- `compress256`'s environment survives a store outside everything it uses. -/
theorem SCEnv.store32 {M : Word → BitVec 8} {P sp0 stp bp a v : Word} {n : Nat}
    (env : SCEnv M P sp0 stp bp n) (hC : Sep a 4 P sha256CompressCode.length)
    (hI : Sep a 4 (P + 0x2B94) shaIndexCode.length) (h97 : Sep a 4 (P + 0xC09C) shaSigma1PartCode.length)
    (hK : Sep a 4 (BitVec.ofNat 32 shaKAddress) 256) : SCEnv (memStore32 M a v) P sp0 stp bp n :=
  { env with
    code := env.code.store32 hC
    idx := env.idx.store32 hI
    o97 := env.o97.store32 h97
    kdata := env.kdata.store32 hK }

theorem blockList_congr {M M' : Word → BitVec 8} {bp : Word} {k : Nat}
    (h : ∀ i, i < 64 * k → M' (bp + BitVec.ofNat 32 i) = M (bp + BitVec.ofNat 32 i)) :
    blockList M' bp k = blockList M bp k := by
  unfold blockList
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.mp hj
  apply memBytes_congr
  intro i hi
  rw [add_ofNat_assoc]
  exact h _ (by omega)

section

set_option maxRecDepth 20000

theorem sb_at_0 : fetchRel shaUpdateBlocksCode 0x0 = some (.load .lw a3 a0 0x20, 2) := by decide
theorem sb_at_2 : fetchRel shaUpdateBlocksCode 0x2 = some (.load .lw a4 a0 0x24, 2) := by decide
theorem sb_at_4 : fetchRel shaUpdateBlocksCode 0x4 = some (.alu .add a5 a3 a2, 4) := by decide
theorem sb_at_8 : fetchRel shaUpdateBlocksCode 0x8 = some (.alu .sltu a3 a5 a3, 4) := by decide
theorem sb_at_c : fetchRel shaUpdateBlocksCode 0xC = some (.alu .add a3 a3 a4, 2) := by decide
theorem sb_at_e : fetchRel shaUpdateBlocksCode 0xE = some (.store .sw a0 a5 0x20, 2) := by decide
theorem sb_at_10 : fetchRel shaUpdateBlocksCode 0x10 = some (.store .sw a0 a3 0x24, 2) := by decide
theorem sb_at_12 : fetchRel shaUpdateBlocksCode 0x12 = some (.auipc (6 : Fin 32) 0xD000, 4) := by decide
theorem sb_at_16 : fetchRel shaUpdateBlocksCode 0x16 = some (.jalr x0 (6 : Fin 32) 0xFFFFFC0C, 4) := by decide
theorem su_at_0 : fetchRel shaUpdateCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem su_at_2 : fetchRel shaUpdateCode 0x2 = some (.auipc (5 : Fin 32) 0x19000, 4) := by decide
theorem su_at_6 : fetchRel shaUpdateCode 0x6 = some (.jalr (5 : Fin 32) (5 : Fin 32) 0xFFFFFC24, 4) := by decide
theorem su_at_a : fetchRel shaUpdateCode 0xA = some (.store .sw sp (20 : Fin 32) 0x8, 2) := by decide
theorem su_at_c : fetchRel shaUpdateCode 0xC = some (.alu .add (9 : Fin 32) x0 a2, 2) := by decide
theorem su_at_e : fetchRel shaUpdateCode 0xE = some (.alu .add (20 : Fin 32) x0 a0, 2) := by decide
theorem su_at_10 : fetchRel shaUpdateCode 0x10 = some (.load .lbu (8 : Fin 32) a0 0x3F, 4) := by decide
theorem su_at_14 : fetchRel shaUpdateCode 0x14 = some (.aluImm .add a2 x0 0x40, 4) := by decide
theorem su_at_18 : fetchRel shaUpdateCode 0x18 = some (.alu .sub a2 a2 (8 : Fin 32), 2) := by decide
theorem su_at_1a : fetchRel shaUpdateCode 0x1A = some (.branch .bgeu (9 : Fin 32) a2 0x24, 4) := by decide
theorem su_at_1e : fetchRel shaUpdateCode 0x1E = some (.alu .add a0 (20 : Fin 32) (8 : Fin 32), 4) := by decide
theorem su_at_22 : fetchRel shaUpdateCode 0x22 = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem su_at_24 : fetchRel shaUpdateCode 0x24 = some (.auipc ra 0x19000, 4) := by decide
theorem su_at_28 : fetchRel shaUpdateCode 0x28 = some (.jalr ra ra 0xFFFFFE40, 4) := by decide
theorem su_at_2c : fetchRel shaUpdateCode 0x2C = some (.alu .add (8 : Fin 32) (8 : Fin 32) (9 : Fin 32), 2) := by decide
theorem su_at_2e : fetchRel shaUpdateCode 0x2E = some (.store .sb (20 : Fin 32) (8 : Fin 32) 0x3F, 4) := by decide
theorem su_at_32 : fetchRel shaUpdateCode 0x32 = some (.auipc (5 : Fin 32) 0x19000, 4) := by decide
theorem su_at_36 : fetchRel shaUpdateCode 0x36 = some (.jalr (5 : Fin 32) (5 : Fin 32) 0xFFFFFA32, 4) := by decide
theorem su_at_3a : fetchRel shaUpdateCode 0x3A = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem su_at_3c : fetchRel shaUpdateCode 0x3C = some (.jalr x0 ra 0x0, 2) := by decide
theorem su_at_3e : fetchRel shaUpdateCode 0x3E = some (.aluImm .add (18 : Fin 32) (20 : Fin 32) 0x40, 4) := by decide
theorem su_at_42 : fetchRel shaUpdateCode 0x42 = some (.branch .beq (8 : Fin 32) x0 0x28, 2) := by decide
theorem su_at_44 : fetchRel shaUpdateCode 0x44 = some (.alu .add (19 : Fin 32) a1 a2, 4) := by decide
theorem su_at_48 : fetchRel shaUpdateCode 0x48 = some (.alu .sub (9 : Fin 32) (9 : Fin 32) a2, 2) := by decide
theorem su_at_4a : fetchRel shaUpdateCode 0x4A = some (.alu .add a0 (20 : Fin 32) (8 : Fin 32), 4) := by decide
theorem su_at_4e : fetchRel shaUpdateCode 0x4E = some (.auipc ra 0x19000, 4) := by decide
theorem su_at_52 : fetchRel shaUpdateCode 0x52 = some (.jalr ra ra 0xFFFFFE16, 4) := by decide
theorem su_at_56 : fetchRel shaUpdateCode 0x56 = some (.aluImm .add a2 x0 0x1, 2) := by decide
theorem su_at_58 : fetchRel shaUpdateCode 0x58 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem su_at_5a : fetchRel shaUpdateCode 0x5A = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem su_at_5c : fetchRel shaUpdateCode 0x5C = some (.auipc ra 0x0, 4) := by decide
theorem su_at_60 : fetchRel shaUpdateCode 0x60 = some (.jalr ra ra 0x4C, 4) := by decide
theorem su_at_64 : fetchRel shaUpdateCode 0x64 = some (.store .sb (20 : Fin 32) x0 0x3F, 4) := by decide
theorem su_at_68 : fetchRel shaUpdateCode 0x68 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem su_at_6a : fetchRel shaUpdateCode 0x6A = some (.lui a0 0x80000000, 4) := by decide
theorem su_at_6e : fetchRel shaUpdateCode 0x6E = some (.aluImm .add a0 a0 0xFFFFFFC0, 4) := by decide
theorem su_at_72 : fetchRel shaUpdateCode 0x72 = some (.aluImm .srl a2 (9 : Fin 32) 0x6, 4) := by decide
theorem su_at_76 : fetchRel shaUpdateCode 0x76 = some (.alu .and a0 a0 (9 : Fin 32), 2) := by decide
theorem su_at_78 : fetchRel shaUpdateCode 0x78 = some (.aluImm .and (9 : Fin 32) (9 : Fin 32) 0x3F, 4) := by decide
theorem su_at_7c : fetchRel shaUpdateCode 0x7C = some (.alu .add (19 : Fin 32) a1 a0, 4) := by decide
theorem su_at_80 : fetchRel shaUpdateCode 0x80 = some (.branch .beq a2 x0 0xC, 2) := by decide
theorem su_at_82 : fetchRel shaUpdateCode 0x82 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem su_at_84 : fetchRel shaUpdateCode 0x84 = some (.auipc ra 0x0, 4) := by decide
theorem su_at_88 : fetchRel shaUpdateCode 0x88 = some (.jalr ra ra 0x24, 4) := by decide
theorem su_at_8c : fetchRel shaUpdateCode 0x8C = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem su_at_8e : fetchRel shaUpdateCode 0x8E = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem su_at_90 : fetchRel shaUpdateCode 0x90 = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem su_at_92 : fetchRel shaUpdateCode 0x92 = some (.store .sb (20 : Fin 32) (9 : Fin 32) 0x3F, 4) := by decide
theorem su_at_96 : fetchRel shaUpdateCode 0x96 = some (.auipc (5 : Fin 32) 0x19000, 4) := by decide
theorem su_at_9a : fetchRel shaUpdateCode 0x9A = some (.jalr (5 : Fin 32) (5 : Fin 32) 0xFFFFF9CE, 4) := by decide
theorem su_at_9e : fetchRel shaUpdateCode 0x9E = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem su_at_a0 : fetchRel shaUpdateCode 0xA0 = some (.auipc (6 : Fin 32) 0x19000, 4) := by decide
theorem su_at_a4 : fetchRel shaUpdateCode 0xA4 = some (.jalr x0 (6 : Fin 32) 0xFFFFFDC4, 4) := by decide

end

/-- **The block helper of `update`.** Called with the hash words at `st`,
the 64-bit block count after them at `st + 0x20`, and `n` blocks at `bp`,
it adds `n` to the count and compresses the blocks into the hash words, as
`sha256Compress_correct` says, then returns. It changes no memory outside
`compress256`'s frame and the 40 bytes at `st`. -/
theorem shaBlocks_correct (m : Machine) {st bp sp0 retAddr : Word} {n : Nat}
    (hcode : CodeIn m.mem (BitVec.ofNat 32 shaUpdateBlocksAddress) shaUpdateBlocksCode)
    (hpc : m.pc = BitVec.ofNat 32 shaUpdateBlocksAddress)
    (env : SCEnv m.mem (BitVec.ofNat 32 sha256CompressAddress) sp0 st bp n)
    (ha0 : reg m a0 = st) (ha1 : reg m a1 = bp) (ha2 : reg m a2 = BitVec.ofNat 32 n)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (hcnt : (memLoad32 m.mem (st + 0x20)).toNat + n < 2 ^ 32)
    (cC : Sep (st + 0x20) 8 (BitVec.ofNat 32 sha256CompressAddress) sha256CompressCode.length)
    (cI : Sep (st + 0x20) 8 (BitVec.ofNat 32 sha256CompressAddress + 0x2B94) shaIndexCode.length)
    (c97 : Sep (st + 0x20) 8 (BitVec.ofNat 32 sha256CompressAddress + 0xC09C) shaSigma1PartCode.length)
    (cK : Sep (st + 0x20) 8 (BitVec.ofNat 32 shaKAddress) 256)
    (cF : Sep (st + 0x20) 8 (sp0 + 0xFFFFFF20) 0xE0) (cB : Sep bp (64 * n) (st + 0x20) 8)
    (cU : Sep (st + 0x20) 8 (BitVec.ofNat 32 shaUpdateBlocksAddress) shaUpdateBlocksCode.length) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q ≠ (3 : Fin 32) → q ≠ (5 : Fin 32) → q ≠ (6 : Fin 32) → q ≠ (7 : Fin 32) →
        q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ (17 : Fin 32) →
        q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ (31 : Fin 32) →
        reg m' q = reg m q) ∧
      wordsAt m'.mem st 8 = (blockList m.mem bp n).foldl Sha256.compress (wordsAt m.mem st 8) ∧
      memLoad32 m'.mem (st + 0x20) = memLoad32 m.mem (st + 0x20) + BitVec.ofNat 32 n ∧
      memLoad32 m'.mem (st + 0x24) = memLoad32 m.mem (st + 0x24) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF20) 0xE0 x 1 → Sep st 40 x 1 → m'.mem x = m.mem x := by
  let B := BitVec.ofNat 32 shaUpdateBlocksAddress
  let P := BitVec.ofNat 32 sha256CompressAddress
  let M := m.mem
  let lo := memLoad32 M (st + 0x20)
  let hi := memLoad32 M (st + 0x24)
  have s0 : St M B m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := s0.zero
  have al20 : (st + 0x20).toNat % 4 = 0 := aligned_add env.hstp (k := 0x20) (by decide)
  have al24 : (st + 0x24).toNat % 4 = 0 := aligned_add env.hstp (k := 0x24) (by decide)
  obtain ⟨n1, d1, u1⟩ := s0.lw hcode sb_at_0 (off' := 0x2) (by decide) (by rw [ha0]; exact al20)
  have g1 : reg n1 a3 = lo := by rw [u1.upd_eq (by decide), ha0]
  have K1 := u1.upd_ne hz
  have u1' : St M B n1 0x2 (reg n1) := u1.self
  obtain ⟨n2, d2, u2⟩ := u1'.lw hcode sb_at_2 (off' := 0x4) (by decide)
    (by rw [K1 a0 (by decide), ha0]; exact al24)
  have g2 : reg n2 a4 = hi := by rw [u2.upd_eq (by decide), K1 a0 (by decide), ha0]
  have K2 := u2.upd_ne u1'.zero
  have u2' : St M B n2 0x4 (reg n2) := u2.self
  obtain ⟨n3, d3, u3⟩ := u2'.alu hcode sb_at_4 (off' := 0x8) (by decide)
  have g3 : reg n3 a5 = lo + BitVec.ofNat 32 n := by
    rw [u3.upd_eq (by decide), K2 a3 (by decide), g1, K2 a2 (by decide), K1 a2 (by decide), ha2]; rfl
  have K3 := u3.upd_ne u2'.zero
  have u3' : St M B n3 0x8 (reg n3) := u3.self
  obtain ⟨n4, d4, u4⟩ := u3'.alu hcode sb_at_8 (off' := 0xC) (by decide)
  have nolt : (lo + BitVec.ofNat 32 n).ult lo = false := by
    simp only [BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat]
    apply decide_eq_false
    have := lo.isLt
    rw [Nat.mod_eq_of_lt (a := n) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have g4 : reg n4 a3 = 0 := by
    rw [u4.upd_eq (by decide), g3, K3 a3 (by decide), K2 a3 (by decide), g1]
    show (if (lo + BitVec.ofNat 32 n).ult lo then (1 : Word) else 0) = 0
    rw [nolt]; rfl
  have K4 := u4.upd_ne u3'.zero
  have u4' : St M B n4 0xC (reg n4) := u4.self
  obtain ⟨n5, d5, u5⟩ := u4'.alu hcode sb_at_c (off' := 0xE) (by decide)
  have g5 : reg n5 a3 = hi := by
    rw [u5.upd_eq (by decide), g4, K4 a4 (by decide), K3 a4 (by decide), g2]; exact BitVec.zero_add _
  have K5 := u5.upd_ne u4'.zero
  have u5' : St M B n5 0xE (reg n5) := u5.self
  have a0_5 : reg n5 a0 = st := by
    rw [K5 a0 (by decide), K4 a0 (by decide), K3 a0 (by decide), K2 a0 (by decide), K1 a0 (by decide), ha0]
  have a5_5 : reg n5 a5 = lo + BitVec.ofNat 32 n := by
    rw [K5 a5 (by decide), K4 a5 (by decide), g3]
  obtain ⟨n6, d6, u6⟩ := u5'.sw hcode sb_at_e (off' := 0x10) (by decide) (by rw [a0_5]; exact al20)
  rw [a0_5, a5_5] at u6
  let M1 := memStore32 M (st + 0x20) (lo + BitVec.ofNat 32 n)
  have hc1 : CodeIn M1 B shaUpdateBlocksCode := hcode.store32 (cU.sub (c := 0) (l := 4) (by omega) |>
    fun h => by rwa [add_ofNat_zero] at h)
  have e20 : st + 0x20 = st + BitVec.ofNat 32 32 := rfl
  have e24 : st + 0x20 + BitVec.ofNat 32 4 = st + 0x24 := by rw [BitVec.add_assoc]; rfl
  have s0_ : ∀ {b : Word} {l : Nat}, Sep (st + 0x20) 8 b l → Sep (st + 0x20) 4 b l := fun h => by
    have := h.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
  have s4_ : ∀ {b : Word} {l : Nat}, Sep (st + 0x20) 8 b l → Sep (st + 0x24) 4 b l := fun h => by
    have := h.sub (c := 4) (l := 4) (by omega); rwa [e24] at this
  have a3_5 : reg n5 a3 = hi := g5
  obtain ⟨n7, d7, u7⟩ := u6.sw hc1 sb_at_10 (off' := 0x12) (by decide) (by rw [a0_5]; exact al24)
  rw [a0_5, a3_5] at u7
  let M2 := memStore32 M1 (st + 0x24) hi
  have hc2 : CodeIn M2 B shaUpdateBlocksCode := hc1.store32 (s4_ cU)
  obtain ⟨n8, d8, u8⟩ := u7.auipc hc2 sb_at_12 (off' := 0x16) (by decide)
  obtain ⟨n9, d9, pc9, mem9, regs9⟩ := u8.jalr hc2 sb_at_16
  have hP : n9.pc = P := by rw [pc9]; simp +decide only [upd, ite_false, ite_true]; decide
  have r9 : ∀ r, r ≠ (6 : Fin 32) → reg n9 r = reg n5 r := fun r h6 => by
    rw [regs9]
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]; exact u5'.zero.symm
    · simp [upd, h0, h6]
  have r9m : ∀ r, r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ (6 : Fin 32) → reg n9 r = reg m r := fun r q3 q4 q5 q6 => by
    rw [r9 r q6, K5 r q3, K4 r q3, K3 r q5, K2 r q4, K1 r q3]
  have env2 : SCEnv n9.mem P sp0 st bp n := by
    rw [mem9]
    exact (env.store32 (s0_ cC) (s0_ cI) (s0_ c97) (s0_ cK)).store32 (s4_ cC) (s4_ cI) (s4_ c97) (s4_ cK)
  obtain ⟨m', c', pc', sp', K', wst, fr⟩ := sha256Compress_correct n9 env2 hP
    (by rw [r9m a0 (by decide) (by decide) (by decide) (by decide), ha0])
    (by rw [r9m a1 (by decide) (by decide) (by decide) (by decide), ha1])
    (by rw [r9m a2 (by decide) (by decide) (by decide) (by decide), ha2])
    (by rw [r9m ra (by decide) (by decide) (by decide) (by decide), hra]) hret
    (by rw [r9m sp (by decide) (by decide) (by decide) (by decide), hsp])
  have stS : ∀ i, i < 8 → Sep (st + 0x20) 4 (st + BitVec.ofNat 32 (4 * i)) 4 ∧
      Sep (st + 0x24) 4 (st + BitVec.ofNat 32 (4 * i)) 4 := fun i hi =>
    ⟨by rw [e20]; exact sep_offsets st (by omega) (by omega) (by omega),
     by rw [show st + (0x24 : Word) = st + BitVec.ofNat 32 36 from rfl]; exact sep_offsets st (by omega) (by omega) (by omega)⟩
  have w2 : wordsAt n9.mem st 8 = wordsAt M st 8 := by
    rw [mem9]; apply wordsAt_congr; intro i hi
    show memLoad32 (memStore32 (memStore32 M _ _) _ _) _ = _
    rw [memLoad32_store32_sep (stS i hi).2, memLoad32_store32_sep (stS i hi).1]
  have b2 : blockList n9.mem bp n = blockList M bp n := by
    rw [mem9]; apply blockList_congr; intro i hi
    have hb : Sep (st + 0x20) 8 (bp + BitVec.ofNat 32 i) 1 := (cB.sub (c := i) (l := 1) (by omega)).symm
    show memStore32 (memStore32 M _ _) _ _ _ = _
    rw [memStore32_get_sep (s4_ hb), memStore32_get_sep (s0_ hb)]
  have e36 : st + BitVec.ofNat 32 36 = st + 0x24 := rfl
  have e32 : st + BitVec.ofNat 32 32 = st + 0x20 := rfl
  have cnt' : ∀ (o : Nat), o = 32 ∨ o = 36 →
      memLoad32 m'.mem (st + BitVec.ofNat 32 o) = memLoad32 n9.mem (st + BitVec.ofNat 32 o) := by
    intro o ho
    apply memLoad32_congr; intro j hj
    rw [add_ofNat_assoc]
    apply fr
    · have := cF.symm.subR (c := o - 32 + j) (l := 1) (by omega)
      rwa [e20, add_ofNat_assoc, show 32 + (o - 32 + j) = o + j by omega] at this
    · have := sep_offsets st (c := 0) (n := 32) (d := o + j) (k := 1) (by omega) (by omega) (by omega)
      rwa [add_ofNat_zero] at this
  refine ⟨m', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 c')))))))),
    pc', sp', fun q q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 => ?_, ?_, ?_, ?_,
    fun x hF hx => ?_⟩
  · rw [K' q q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31, r9m q q13 q14 q15 q6]
  · rw [wst, b2, w2]
  · rw [← e32, cnt' 32 (Or.inl rfl), mem9, e32]
    show memLoad32 (memStore32 (memStore32 M _ _) _ _) _ = _
    rw [memLoad32_store32_sep (by rw [← e36, ← e32]; exact sep_offsets st (by omega) (by omega) (by omega)),
      memLoad32_store32_same]
  · rw [← e36, cnt' 36 (Or.inr rfl), mem9, e36]
    show memLoad32 (memStore32 (memStore32 M _ _) _ _) _ = _
    rw [memLoad32_store32_same]
  · rw [fr x hF (hx.sub (c := 0) (l := 32) (by omega) |> fun h => by rwa [add_ofNat_zero] at h), mem9]
    show memStore32 (memStore32 M _ _) _ _ x = _
    rw [memStore32_get_sep (by have := hx.sub (c := 36) (l := 4) (by omega); rwa [e36] at this),
      memStore32_get_sep (by have := hx.sub (c := 32) (l := 4) (by omega); rwa [e32] at this)]

end C3.RV32
