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

theorem memBytes_take (M : Word → BitVec 8) (p : Word) {k n : Nat} (h : k ≤ n) :
    (memBytes M p n).take k = memBytes M p k := by
  unfold memBytes
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

theorem memBytes_drop (M : Word → BitVec 8) (p : Word) {k n : Nat} (h : k ≤ n) :
    (memBytes M p n).drop k = memBytes M (p + BitVec.ofNat 32 k) (n - k) := by
  have := memBytes_split M p k (n - k)
  rw [show k + (n - k) = n by omega] at this
  rw [this, List.drop_left' (memBytes_length M p k)]

/-- The 0x68 bytes at `S` hold the compiled hasher after it has absorbed
`msg`: the bytes after `msg`'s full blocks in the buffer, their count in its
last byte, the hash of the full blocks, and the 64-bit count of blocks. -/
structure HasherAt (M : Word → BitVec 8) (S : Word) (msg : Bytes) : Prop where
  hlen : msg.length < 2 ^ 32
  pos : M (S + 0x3F) = BitVec.ofNat 8 (msg.length % 64)
  buf : memBytes M S (msg.length % 64) = tailBytes msg
  hash : wordsAt M (S + 0x40) 8 = (fullBlocks msg).foldl Sha256.compress Sha256.h0
  lo : memLoad32 M (S + 0x60) = BitVec.ofNat 32 (msg.length / 64)
  hi : memLoad32 M (S + 0x64) = 0

/-- Where `update` runs: the code of `update`, its helpers, `compress256`,
and `memcpy` at their addresses in the image; the hasher at `S`, the `n`
input bytes at `D`, and the 0x100 bytes of stack below `sp0` apart from each
other and from the round constants; and all three at data-bus addresses,
below every code address. -/
structure UpdEnv (M : Word → BitVec 8) (S D sp0 : Word) (n : Nat) : Prop where
  cU : CodeIn M (BitVec.ofNat 32 shaUpdateAddress) shaUpdateCode
  cSave : CodeIn M (BitVec.ofNat 32 shaUpdateSaveAddress) shaUpdateSaveCode
  cRest : CodeIn M (BitVec.ofNat 32 shaUpdateRestoreAddress) shaUpdateRestoreCode
  cBlk : CodeIn M (BitVec.ofNat 32 shaUpdateBlocksAddress) shaUpdateBlocksCode
  cC : CodeIn M (BitVec.ofNat 32 sha256CompressAddress) sha256CompressCode
  cI : CodeIn M (BitVec.ofNat 32 sha256CompressAddress + 0x2B94) shaIndexCode
  c97 : CodeIn M (BitVec.ofNat 32 sha256CompressAddress + 0xC09C) shaSigma1PartCode
  cK : CodeIn M (BitVec.ofNat 32 shaKAddress) shaKData
  cMS : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  cMB : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  hS : S.toNat % 4 = 0
  hSw : S.toNat + 0x68 ≤ 0x40000000
  hsp : sp0.toNat % 16 = 0
  hspl : 0x100 ≤ sp0.toNat
  hspw : sp0.toNat ≤ 0x40000000
  hDw : D.toNat + n ≤ 0x40000000
  sDS : Sep D n S 0x68
  sDF : Sep D n (sp0 + 0xFFFFFF00) 0x100
  sSF : Sep S 0x68 (sp0 + 0xFFFFFF00) 0x100
  sKS : Sep (BitVec.ofNat 32 shaKAddress) 256 S 0x68
  sKF : Sep (BitVec.ofNat 32 shaKAddress) 256 (sp0 + 0xFFFFFF00) 0x100

/-- What `update`'s save helper stores, and where in the frame. -/
abbrev updSavePs : List (Fin 32 × Word) := [(ra, 0x1C), (s0, 0x18), (s1, 0x14), (s2, 0x10), (s3, 0x0C)]

/-- What `update`'s restore helper loads, and from where in the frame. -/
abbrev updRestorePs : List (Fin 32 × Word) :=
  [(ra, 0x1C), (s0, 0x18), (s1, 0x14), (s2, 0x10), (s3, 0x0C), (s4, 8)]

theorem updSave_shape : SaveAt shaUpdateSaveCode 0 updSavePs := by simp only [SaveAt]; decide

theorem updRestore_shape : RestoreAt shaUpdateRestoreCode 0 updRestorePs := by simp only [RestoreAt]; decide

/-- Any data-bus range below 0x40000000 is apart from code at or above
0x40000000. -/
theorem data_code {a b : Word} {n l : Nat} (ha : a.toNat + n ≤ 0x40000000) (hb : 0x40000000 ≤ b.toNat)
    (hbl : b.toNat + l ≤ 2 ^ 32) : Sep a n b l :=
  sep_of_le (by omega) hbl

set_option maxRecDepth 20000 in
/-- `update`'s prologue, to offset 0x0C: it allocates a 0x20-byte frame at
`G`, saves `ra` and `s0` through `s3` with its save helper, and stores `s4`.
Any later memory that keeps the frame's top 24 bytes gives back the saved
registers. -/
theorem upd_pro {M : Word → BitVec 8} {m : Machine} {G : Word}
    (st0 : St M (BitVec.ofNat 32 shaUpdateAddress) m 0 (reg m))
    (cU : CodeIn M (BitVec.ofNat 32 shaUpdateAddress) shaUpdateCode)
    (cSave : CodeIn M (BitVec.ofNat 32 shaUpdateSaveAddress) shaUpdateSaveCode)
    (hG : reg m sp + 0xFFFFFFE0 = G) (hGa : G.toNat % 4 = 0) (hGw : G.toNat + 32 ≤ 0x40000000) :
    ∃ m2 M2, Steps m m2 ∧ St M2 (BitVec.ofNat 32 shaUpdateAddress) m2 0x0C (reg m2) ∧ reg m2 sp = G ∧
      (∀ r, r ≠ sp → r ≠ t0 → reg m2 r = reg m r) ∧ (∀ x, Sep G 32 x 1 → M2 x = M x) ∧
      ∀ Mx : Word → BitVec 8, (∀ k, 8 ≤ k → k < 32 → Mx (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k)) →
        memLoad32 Mx (G + 0x1C) = reg m ra ∧ memLoad32 Mx (G + 0x18) = reg m s0 ∧
        memLoad32 Mx (G + 0x14) = reg m s1 ∧ memLoad32 Mx (G + 0x10) = reg m s2 ∧
        memLoad32 Mx (G + 0x0C) = reg m s3 ∧ memLoad32 Mx (G + 8) = reg m s4 := by
  have hz := st0.zero
  have sepC : ∀ c l, c + l ≤ 32 → ∀ (b : Word) (k : Nat), 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (G + BitVec.ofNat 32 c) l b k := fun c l h b k hb hbk => by
    apply data_code _ hb hbk
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have frx : ∀ c l, c + l ≤ 32 → ∀ (x : Word), Sep G 32 x 1 → Sep (G + BitVec.ofNat 32 c) l x 1 :=
    fun c l h x hx => hx.sub (c := c) (l := l) (by omega)
  obtain ⟨m1, e1, t1⟩ := st0.aluImm cU su_at_0 (off' := 2) (by decide)
  rw [show aluEval .add (reg m sp) 0xFFFFFFE0 = G from hG] at t1
  have f1sp : upd (reg m) sp G sp = G := by simp +decide [upd]
  have f1 : ∀ r, r ≠ sp → upd (reg m) sp G r = reg m r := fun r h => by
    by_cases hr : r.val = 0
    · have : r = 0 := Fin.ext hr
      subst this; simp [upd, hz]
    · simp [upd, hr, h]
  obtain ⟨m2, k2, t2⟩ := t1.callSave cU su_at_2 su_at_6 (b := BitVec.ofNat 32 shaUpdateSaveAddress)
    (by decide) (by decide) (by decide) cSave updSave_shape (by decide) (fun p hp => by
      rw [f1sp]
      simp only [updSavePs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact ⟨by decide, aligned_add hGa (k := 0x1C) (by decide), sepC 0x1C 4 (by omega) _ _ (by decide) (by decide)⟩
      · exact ⟨by decide, aligned_add hGa (k := 0x18) (by decide), sepC 0x18 4 (by omega) _ _ (by decide) (by decide)⟩
      · exact ⟨by decide, aligned_add hGa (k := 0x14) (by decide), sepC 0x14 4 (by omega) _ _ (by decide) (by decide)⟩
      · exact ⟨by decide, aligned_add hGa (k := 0x10) (by decide), sepC 0x10 4 (by omega) _ _ (by decide) (by decide)⟩
      · exact ⟨by decide, aligned_add hGa (k := 0x0C) (by decide), sepC 0x0C 4 (by omega) _ _ (by decide) (by decide)⟩)
  rw [f1sp] at t2
  obtain ⟨M1, hM1⟩ : ∃ M1, saveMem M G (upd (reg m) sp G) updSavePs = M1 := ⟨_, rfl⟩
  rw [hM1] at t2
  have M1out : ∀ x, Sep G 32 x 1 → M1 x = M x := fun x hx => by
    rw [← hM1]; simp only [saveMem]
    rw [memStore32_get_sep (show Sep (G + 0x0C) 4 x 1 from frx 0x0C 4 (by omega) x hx), memStore32_get_sep (show Sep (G + 0x10) 4 x 1 from frx 0x10 4 (by omega) x hx),
      memStore32_get_sep (show Sep (G + 0x14) 4 x 1 from frx 0x14 4 (by omega) x hx), memStore32_get_sep (show Sep (G + 0x18) 4 x 1 from frx 0x18 4 (by omega) x hx),
      memStore32_get_sep (show Sep (G + 0x1C) 4 x 1 from frx 0x1C 4 (by omega) x hx)]
  have cU1 : CodeIn M1 (BitVec.ofNat 32 shaUpdateAddress) shaUpdateCode := fun i hi => by
    have hs := sepC 0 32 (by omega) (BitVec.ofNat 32 shaUpdateAddress) shaUpdateCode.length (by decide) (by decide)
    rw [add_ofNat_zero] at hs
    rw [M1out _ (hs.subR (c := i) (l := 1) (by omega))]
    exact cU i hi
  have g2 : ∀ r, r ≠ sp → r ≠ t0 →
      upd (upd (reg m) sp G) t0 (BitVec.ofNat 32 shaUpdateAddress + BitVec.ofNat 32 (2 + 8)) r = reg m r :=
    fun r h1 h2 => by
      by_cases hr : r.val = 0
      · have : r = 0 := Fin.ext hr
        subst this; simp [upd, hz]
      · simp [upd, hr, h1, h2]
  have g2sp : upd (upd (reg m) sp G) t0 (BitVec.ofNat 32 shaUpdateAddress + BitVec.ofNat 32 (2 + 8)) sp = G := by
    simp +decide [upd]
  obtain ⟨m3, e3, t3⟩ := t2.sw cU1 su_at_a (off' := 0x0C) (by decide)
    (by rw [g2sp]; exact aligned_add hGa (k := 8) (by decide))
  rw [g2sp, g2 s4 (by decide) (by decide)] at t3
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore32 M1 (G + 8) (reg m s4) = M2 := ⟨_, rfl⟩
  rw [hM2] at t3
  have M2out : ∀ x, Sep G 32 x 1 → M2 x = M x := fun x hx => by
    rw [← hM2, memStore32_get_sep (show Sep (G + 8) 4 x 1 from frx 8 4 (by omega) x hx), M1out x hx]
  have M2slots : memLoad32 M2 (G + 0x1C) = reg m ra ∧ memLoad32 M2 (G + 0x18) = reg m s0 ∧
      memLoad32 M2 (G + 0x14) = reg m s1 ∧ memLoad32 M2 (G + 0x10) = reg m s2 ∧
      memLoad32 M2 (G + 0x0C) = reg m s3 ∧ memLoad32 M2 (G + 8) = reg m s4 := by
    have so : ∀ c d, c < 32 → d < 32 → c + 4 ≤ d ∨ d + 4 ≤ c →
        Sep (G + BitVec.ofNat 32 c) 4 (G + BitVec.ofNat 32 d) 4 :=
      fun c d hc hd h => sep_offsets G h (by omega) (by omega)
    rw [← hM2, ← hM1]; simp only [saveMem]
    refine ⟨?_, ?_, ?_, ?_, ?_, memLoad32_store32_same _ _ _⟩
    · rw [memLoad32_store32_sep (show Sep (G + 8) 4 (G + 0x1C) 4 from so 8 0x1C (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x0C) 4 (G + 0x1C) 4 from so 0x0C 0x1C (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x10) 4 (G + 0x1C) 4 from so 0x10 0x1C (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x14) 4 (G + 0x1C) 4 from so 0x14 0x1C (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x18) 4 (G + 0x1C) 4 from so 0x18 0x1C (by omega) (by omega) (by omega)), memLoad32_store32_same,
        f1 ra (by decide)]
    · rw [memLoad32_store32_sep (show Sep (G + 8) 4 (G + 0x18) 4 from so 8 0x18 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x0C) 4 (G + 0x18) 4 from so 0x0C 0x18 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x10) 4 (G + 0x18) 4 from so 0x10 0x18 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x14) 4 (G + 0x18) 4 from so 0x14 0x18 (by omega) (by omega) (by omega)), memLoad32_store32_same,
        f1 s0 (by decide)]
    · rw [memLoad32_store32_sep (show Sep (G + 8) 4 (G + 0x14) 4 from so 8 0x14 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x0C) 4 (G + 0x14) 4 from so 0x0C 0x14 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x10) 4 (G + 0x14) 4 from so 0x10 0x14 (by omega) (by omega) (by omega)), memLoad32_store32_same,
        f1 s1 (by decide)]
    · rw [memLoad32_store32_sep (show Sep (G + 8) 4 (G + 0x10) 4 from so 8 0x10 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x0C) 4 (G + 0x10) 4 from so 0x0C 0x10 (by omega) (by omega) (by omega)), memLoad32_store32_same,
        f1 s2 (by decide)]
    · rw [memLoad32_store32_sep (show Sep (G + 8) 4 (G + 0x0C) 4 from so 8 0x0C (by omega) (by omega) (by omega)), memLoad32_store32_same,
        f1 s3 (by decide)]
  refine ⟨m3, M2, .cons e1 (k2.trans (.single e3)), t3.self, ?_, fun r h1 h2 => ?_, M2out, fun Mx h => ?_⟩
  · rw [t3.regs, g2sp]
  · rw [t3.regs, g2 r h1 h2]
  · have e : ∀ c, 8 ≤ c → c + 4 ≤ 32 → memLoad32 Mx (G + BitVec.ofNat 32 c) = memLoad32 M2 (G + BitVec.ofNat 32 c) :=
      fun c h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h _ (by omega) (by omega)
    obtain ⟨q1, q2, q3, q4, q5, q6⟩ := M2slots
    exact ⟨(e 0x1C (by omega) (by omega)).trans q1, (e 0x18 (by omega) (by omega)).trans q2,
      (e 0x14 (by omega) (by omega)).trans q3, (e 0x10 (by omega) (by omega)).trans q4,
      (e 0x0C (by omega) (by omega)).trans q5, (e 8 (by omega) (by omega)).trans q6⟩

/-- Registers after `update`'s restore helper, with `t0` the helper's link. -/
abbrev updRestored (M : Word → BitVec 8) (G : Word) (f : Fin 32 → Word) : Fin 32 → Word :=
  restoreRegs M G f updRestorePs

set_option maxRecDepth 20000 in
/-- `update`'s return when the bytes fit in the buffer, from offset 0x32: the
restore helper, freeing the frame, and `ret`. -/
theorem upd_ret {M : Word → BitVec 8} {m : Machine} {f : Fin 32 → Word} {G : Word}
    (s : St M (BitVec.ofNat 32 shaUpdateAddress) m 0x32 f)
    (hc : CodeIn M (BitVec.ofNat 32 shaUpdateAddress) shaUpdateCode)
    (hR : CodeIn M (BitVec.ofNat 32 shaUpdateRestoreAddress) shaUpdateRestoreCode)
    (hsp : f sp = G) (hG : G.toNat % 4 = 0) :
    ∃ m', Steps m m' ∧ m'.pc = memLoad32 M (G + 0x1C) &&& ~~~1 ∧ m'.mem = M ∧
      ∀ r, reg m' r = upd (updRestored M G (upd f t0 (BitVec.ofNat 32 shaUpdateAddress +
        BitVec.ofNat 32 (0x32 + 8)))) sp (G + 0x20) r := by
  obtain ⟨m1, e1, t1⟩ := s.callRestore hc su_at_32 su_at_36 (b := BitVec.ofNat 32 shaUpdateRestoreAddress)
    (by decide) (by decide) (by decide) hR updRestore_shape (by decide) (fun p hp => by
      rw [hsp]
      simp only [updRestorePs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x1C) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x18) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x14) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x10) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x0C) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 8) (by decide)⟩)
  rw [hsp] at t1
  obtain ⟨m2, e2, t2⟩ := t1.aluImm hc su_at_3a (off' := 0x3C) (by decide)
  have q : restoreRegs M G (upd f t0 (BitVec.ofNat 32 shaUpdateAddress + BitVec.ofNat 32 (0x32 + 8)))
      updRestorePs sp = G := by
    simp +decide only [restoreRegs, upd]; simp [hsp]
  rw [q, show aluEval .add G 0x20 = G + 0x20 from rfl] at t2
  obtain ⟨m3, e3, pc3, mem3, regs3⟩ := t2.jalr hc su_at_3c
  refine ⟨m3, e1.trans (.cons e2 (.single e3)), ?_, mem3, regs3⟩
  rw [pc3]; simp +decide only [upd, restoreRegs, add_lit_zero]; simp

set_option maxRecDepth 20000 in
/-- `update`'s end otherwise, from offset 0x96: the restore helper, freeing
the frame, and a tail call of `memcpy` for the bytes left over. -/
theorem upd_tail {M : Word → BitVec 8} {m : Machine} {f : Fin 32 → Word} {G : Word}
    (s : St M (BitVec.ofNat 32 shaUpdateAddress) m 0x96 f)
    (hc : CodeIn M (BitVec.ofNat 32 shaUpdateAddress) shaUpdateCode)
    (hR : CodeIn M (BitVec.ofNat 32 shaUpdateRestoreAddress) shaUpdateRestoreCode)
    (hsp : f sp = G) (hG : G.toNat % 4 = 0) :
    ∃ m', Steps m m' ∧ m'.pc = BitVec.ofNat 32 memcpyStubAddress ∧ m'.mem = M ∧
      ∀ r, r ≠ t1 → reg m' r = upd (updRestored M G (upd f t0 (BitVec.ofNat 32 shaUpdateAddress +
        BitVec.ofNat 32 (0x96 + 8)))) sp (G + 0x20) r := by
  obtain ⟨m1, e1, t1'⟩ := s.callRestore hc su_at_96 su_at_9a (b := BitVec.ofNat 32 shaUpdateRestoreAddress)
    (by decide) (by decide) (by decide) hR updRestore_shape (by decide) (fun p hp => by
      rw [hsp]
      simp only [updRestorePs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x1C) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x18) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x14) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x10) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 0x0C) (by decide)⟩
      · exact ⟨by decide, by decide, aligned_add hG (k := 8) (by decide)⟩)
  rw [hsp] at t1'
  obtain ⟨m2, e2, t2⟩ := t1'.aluImm hc su_at_9e (off' := 0xA0) (by decide)
  have q : restoreRegs M G (upd f t0 (BitVec.ofNat 32 shaUpdateAddress + BitVec.ofNat 32 (0x96 + 8)))
      updRestorePs sp = G := by
    simp +decide only [restoreRegs, upd]; simp [hsp]
  rw [q, show aluEval .add G 0x20 = G + 0x20 from rfl] at t2
  obtain ⟨m3, e3, t3⟩ := t2.auipc hc su_at_a0 (off' := 0xA4) (by decide)
  obtain ⟨m4, e4, pc4, mem4, regs4⟩ := t3.jalr hc su_at_a4
  refine ⟨m4, e1.trans (.cons e2 (.cons e3 (.single e4))), ?_, mem4, fun r h6 => ?_⟩
  · rw [pc4, show ∀ (F : Fin 32 → Word) (v : Word), upd F (6 : Fin 32) v 6 = v from fun F v => by simp [upd]]
    decide
  · rw [regs4]
    have h6' : r ≠ (6 : Fin 32) := h6
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]
    · simp only [upd, h0, h6', ite_false]

set_option maxRecDepth 100000 in
theorem and63_small : ∀ r, r < 64 → r &&& 63 = r := by decide

theorem and63 (x : Nat) : x &&& 63 = x % 64 := by
  have h1 : x &&& 63 ≤ 63 := Nat.and_le_right
  have e := Nat.and_mod_two_pow (a := x) (b := 63) (n := 6)
  rw [show (2 : Nat) ^ 6 = 64 from rfl, Nat.mod_eq_of_lt (show x &&& 63 < 64 by omega), show 63 % 64 = 63 from rfl,
    and63_small _ (Nat.mod_lt _ (by decide))] at e
  exact e

theorem and63_val {x : Nat} (hx : x < 2 ^ 32) : aluEval .and (BitVec.ofNat 32 x) 0x3F = BitVec.ofNat 32 (x % 64) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 x &&& 0x3F).toNat = _
  rw [BitVec.toNat_and, show (0x3F : Word).toNat = 63 from rfl, and63, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx]
  omega

theorem srl6_val {x : Nat} (hx : x < 2 ^ 32) : aluEval .srl (BitVec.ofNat 32 x) 6 = BitVec.ofNat 32 (x / 64) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 x >>> ((6 : Word).toNat % 32)).toNat = _
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    show (6 : Word).toNat % 32 = 6 from rfl, Nat.shiftRight_eq_div_pow]
  omega

theorem m64_bits : ∀ i : Fin 31, ((0x7FFFFFC0 : Word).getLsbD i.val && (0x3F : Word).getLsbD i.val) = false ∧
    ((0x7FFFFFC0 : Word).getLsbD i.val || (0x3F : Word).getLsbD i.val) = true := by decide

/-- The mask `update` uses for the bytes in whole blocks. -/
theorem mask64_val {x : Nat} (hx : x < 2 ^ 31) :
    aluEval .and 0x7FFFFFC0 (BitVec.ofNat 32 x) = BitVec.ofNat 32 (64 * (x / 64)) := by
  let w := BitVec.ofNat 32 x
  have hw31 : w.getLsbD 31 = false := by
    show (BitVec.ofNat 32 x).getLsbD 31 = false
    rw [BitVec.getLsbD_ofNat, Nat.testBit_lt_two_pow hx, Bool.and_false]
  have hd : (0x7FFFFFC0 &&& w) + (0x3F &&& w) = w := by
    rw [Sha256.add_disj]
    · apply Sha256.bitw; intro i hi
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_and]
      by_cases h31 : i = 31
      · subst h31; rw [hw31]; decide
      · have := (m64_bits ⟨i, by omega⟩).2
        cases hb : w.getLsbD i <;> simp_all
    · intro i hi
      simp only [BitVec.getLsbD_and]
      by_cases h31 : i = 31
      · subst h31; rw [hw31]; decide
      · have := (m64_bits ⟨i, by omega⟩).1
        cases w.getLsbD i <;> simp_all
  have e : (0x7FFFFFC0 : Word) &&& w = w - (0x3F &&& w) := by
    calc (0x7FFFFFC0 : Word) &&& w = (0x7FFFFFC0 &&& w) + (0x3F &&& w) - (0x3F &&& w) :=
          (BitVec.add_sub_cancel ..).symm
      _ = w - (0x3F &&& w) := by rw [hd]
  show (0x7FFFFFC0 : Word) &&& w = _
  rw [e]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_and, show (0x3F : Word).toNat = 63 from rfl, Nat.and_comm, and63]
  show (2 ^ 32 - (BitVec.ofNat 32 x).toNat % 64 + (BitVec.ofNat 32 x).toNat) % 2 ^ 32 = (BitVec.ofNat 32 (64 * (x / 64))).toNat
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x < 2 ^ 32 by omega)]
  omega

theorem copyBytes_in {M : Word → BitVec 8} {dst src : Word} {N i : Nat} (hi : i < N) (hN : N < 2 ^ 32) :
    copyBytes M dst src N (dst + BitVec.ofNat 32 i) = M (src + BitVec.ofNat 32 i) := by
  unfold copyBytes
  rw [add_sub_toNat dst (by omega), ite_eq_left hi, BitVec.add_comm dst, BitVec.add_sub_cancel]

theorem copyBytes_out {M : Word → BitVec 8} {dst src x : Word} {N : Nat} (h : ¬ (x - dst).toNat < N) :
    copyBytes M dst src N x = M x := by
  unfold copyBytes; rw [ite_eq_right h]


theorem updR_other (M : Word → BitVec 8) (G w v : Word) (f : Fin 32 → Word) (hz : f 0 = 0) (r : Fin 32)
    (q1 : r ≠ ra) (q8 : r ≠ s0) (q9 : r ≠ s1) (q18 : r ≠ s2) (q19 : r ≠ s3) (q20 : r ≠ s4) (q2 : r ≠ sp)
    (q5 : r ≠ t0) : upd (updRestored M G (upd f t0 v)) sp w r = f r := by
  by_cases h0 : r.val = 0
  · have : r = 0 := Fin.ext h0
    subst this; simp [upd, hz]
  · simp only [updRestored, restoreRegs, upd, h0, q1, q8, q9, q18, q19, q20, q2, q5, ite_false]

theorem updR_saved (M : Word → BitVec 8) (G w v : Word) (f : Fin 32 → Word) :
    upd (updRestored M G (upd f t0 v)) sp w ra = memLoad32 M (G + 0x1C) ∧
    upd (updRestored M G (upd f t0 v)) sp w s0 = memLoad32 M (G + 0x18) ∧
    upd (updRestored M G (upd f t0 v)) sp w s1 = memLoad32 M (G + 0x14) ∧
    upd (updRestored M G (upd f t0 v)) sp w s2 = memLoad32 M (G + 0x10) ∧
    upd (updRestored M G (upd f t0 v)) sp w s3 = memLoad32 M (G + 0x0C) ∧
    upd (updRestored M G (upd f t0 v)) sp w s4 = memLoad32 M (G + 8) ∧
    upd (updRestored M G (upd f t0 v)) sp w sp = w := by
  simp +decide [updRestored, restoreRegs, upd]


set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
/-- `update` from offset 0x6A, once the buffer is empty: it compresses the
whole blocks of the `nk` input bytes left at `Dk` in place, buffers the
rest with a tail call of `memcpy`, and returns. `pre` is the blocks
compressed so far, and `msg'` the message with the new bytes appended. -/
theorem upd_join {M0 Mx : Word → BitVec 8} {S D sp0 Dk : Word} {n nk : Nat} {msg' : Bytes}
    {pre : List Bytes} (nn : Machine) {f : Fin 32 → Word} {rRa rS0 rS1 rS2 rS3 rS4 : Word}
    (E : UpdEnv M0 S D sp0 n) (s : St Mx (BitVec.ofNat 32 shaUpdateAddress) nn 0x6A f)
    (hagree : ∀ x, Sep (sp0 + 0xFFFFFF00) 0x100 x 1 → Sep S 0x68 x 1 → Mx x = M0 x)
    (hnk : nk ≤ n) (hDk : Dk = D + BitVec.ofNat 32 (n - nk)) (hn : n < 2 ^ 31)
    (fa1 : f a1 = Dk) (fs1 : f s1 = BitVec.ofNat 32 nk) (fs2 : f s2 = S + 0x40) (fs4 : f s4 = S)
    (fsp : f sp = sp0 + 0xFFFFFFE0)
    (hslots : ∀ My : Word → BitVec 8, (∀ k, 8 ≤ k → k < 32 →
        My (sp0 + 0xFFFFFFE0 + BitVec.ofNat 32 k) = Mx (sp0 + 0xFFFFFFE0 + BitVec.ofNat 32 k)) →
      memLoad32 My (sp0 + 0xFFFFFFE0 + 0x1C) = rRa ∧ memLoad32 My (sp0 + 0xFFFFFFE0 + 0x18) = rS0 ∧
      memLoad32 My (sp0 + 0xFFFFFFE0 + 0x14) = rS1 ∧ memLoad32 My (sp0 + 0xFFFFFFE0 + 0x10) = rS2 ∧
      memLoad32 My (sp0 + 0xFFFFFFE0 + 0x0C) = rS3 ∧ memLoad32 My (sp0 + 0xFFFFFFE0 + 8) = rS4)
    (hret : rRa &&& ~~~1 = rRa)
    (hhash : wordsAt Mx (S + 0x40) 8 = pre.foldl Sha256.compress Sha256.h0)
    (hlo : memLoad32 Mx (S + 0x60) = BitVec.ofNat 32 pre.length) (hhi : memLoad32 Mx (S + 0x64) = 0)
    (hfull : fullBlocks msg' = pre ++ Sha256.blocks (nk / 64) (memBytes M0 Dk nk))
    (htail : tailBytes msg' = (memBytes M0 Dk nk).drop (64 * (nk / 64)))
    (hlen : msg'.length < 2 ^ 32) :
    ∃ m', Steps nn m' ∧ m'.pc = rRa ∧ reg m' sp = sp0 ∧ reg m' s0 = rS0 ∧ reg m' s1 = rS1 ∧
      reg m' s2 = rS2 ∧ reg m' s3 = rS3 ∧ reg m' s4 = rS4 ∧
      (∀ r, r ≠ ra → r ≠ sp → r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ s0 → r ≠ s1 →
        r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ s2 → r ≠ s3 →
        r ≠ s4 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) →
        reg m' r = f r) ∧
      HasherAt m'.mem S msg' ∧
      ∀ x, Sep (sp0 + 0xFFFFFF00) 0x100 x 1 → Sep S 0x68 x 1 → m'.mem x = M0 x := by
  let U := BitVec.ofNat 32 shaUpdateAddress
  let G := sp0 + 0xFFFFFFE0
  let R := sp0 + 0xFFFFFF00
  let k := nk / 64
  have hSw := E.hSw
  have hspw := E.hspw
  have hspl := E.hspl
  have hDw := E.hDw
  have hRn : R.toNat = sp0.toNat - 0x100 := by
    show (sp0 + 0xFFFFFF00).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFF00 : Word).toNat = 2 ^ 32 - 0x100 from rfl]; omega
  have hGn : G.toNat = sp0.toNat - 0x20 := by
    show (sp0 + 0xFFFFFFE0).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFFE0 : Word).toNat = 2 ^ 32 - 0x20 from rfl]; omega
  have hGa : G.toNat % 4 = 0 := by rw [hGn]; have := E.hsp; omega
  have hGR : G = R + BitVec.ofNat 32 0xE0 := by
    show sp0 + 0xFFFFFFE0 = sp0 + 0xFFFFFF00 + BitVec.ofNat 32 0xE0
    rw [BitVec.add_assoc]; rfl
  have hDkn : Dk.toNat = D.toNat + (n - nk) := by
    rw [hDk, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n - nk) (by omega)]; omega
  -- Code, anywhere at or above 0x40000000, is apart from the stack and the hasher.
  have codeX : ∀ (My : Word → BitVec 8), (∀ x, Sep R 0x100 x 1 → Sep S 0x68 x 1 → My x = M0 x) →
      ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn My b code := fun My h b code hc hb hbl i hi => by
    rw [h _ ((data_code (by rw [hRn]; omega) hb hbl).subR (c := i) (l := 1) (by omega))
      ((data_code (by omega) hb hbl).subR (c := i) (l := 1) (by omega))]
    exact hc i hi
  have cU := codeX Mx hagree _ _ E.cU (by decide) (by decide)
  obtain ⟨n1, d1, u1⟩ := s.lui cU su_at_6a (off' := 0x6E) (by decide)
  have K1 := u1.upd_ne s.zero
  have u1' : St Mx U n1 0x6E (reg n1) := u1.self
  obtain ⟨n2, d2, u2⟩ := u1'.aluImm cU su_at_6e (off' := 0x72) (by decide)
  have g2 : reg n2 a0 = 0x7FFFFFC0 := by rw [u2.upd_eq (by decide), u1.upd_eq (by decide)]; rfl
  have K2 := u2.upd_ne u1'.zero
  have u2' : St Mx U n2 0x72 (reg n2) := u2.self
  have s1_2 : reg n2 s1 = BitVec.ofNat 32 nk := by rw [K2 s1 (by decide), K1 s1 (by decide), fs1]
  obtain ⟨n3, d3, u3⟩ := u2'.aluImm cU su_at_72 (off' := 0x76) (by decide)
  have g3 : reg n3 a2 = BitVec.ofNat 32 k := by rw [u3.upd_eq (by decide), s1_2, srl6_val (by omega)]
  have K3 := u3.upd_ne u2'.zero
  have u3' : St Mx U n3 0x76 (reg n3) := u3.self
  obtain ⟨n4, d4, u4⟩ := u3'.alu cU su_at_76 (off' := 0x78) (by decide)
  have g4 : reg n4 a0 = BitVec.ofNat 32 (64 * k) := by
    rw [u4.upd_eq (by decide), K3 a0 (by decide), g2, K3 s1 (by decide), s1_2, mask64_val (by omega)]
  have K4 := u4.upd_ne u3'.zero
  have u4' : St Mx U n4 0x78 (reg n4) := u4.self
  obtain ⟨n5, d5, u5⟩ := u4'.aluImm cU su_at_78 (off' := 0x7C) (by decide)
  have g5 : reg n5 s1 = BitVec.ofNat 32 (nk % 64) := by
    rw [u5.upd_eq (by decide), K4 s1 (by decide), K3 s1 (by decide), s1_2, and63_val (by omega)]
  have K5 := u5.upd_ne u4'.zero
  have u5' : St Mx U n5 0x7C (reg n5) := u5.self
  obtain ⟨n6, d6, u6⟩ := u5'.alu cU su_at_7c (off' := 0x80) (by decide)
  have g6 : reg n6 s3 = Dk + BitVec.ofNat 32 (64 * k) := by
    rw [u6.upd_eq (by decide), K5 a1 (by decide), K4 a1 (by decide), K3 a1 (by decide), K2 a1 (by decide),
      K1 a1 (by decide), fa1, K5 a0 (by decide), g4]; rfl
  have K6 := u6.upd_ne u5'.zero
  have u6' : St Mx U n6 0x80 (reg n6) := u6.self
  have K16 : ∀ r, r ≠ a0 → r ≠ a2 → r ≠ s1 → r ≠ s3 → reg n6 r = f r := fun r q0 q2 q9 q19 => by
    rw [K6 r q19, K5 r q9, K4 r q0, K3 r q2, K2 r q0, K1 r q0]
  have c6 : Steps nn n6 := .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6)))))
  have hkk : 64 * k ≤ nk := by show 64 * (nk / 64) ≤ nk; omega
  have hblk : Sha256.blocks k (memBytes M0 Dk nk) = blockList Mx Dk k := by
    rw [blocks_take, memBytes_take _ _ hkk, blocks_memBytes M0 k k Dk (Nat.le_refl k)]
    apply blockList_congr; intro i hi
    have hD := E.sDF.sub (c := n - nk + i) (l := 1) (by omega)
    have hS' := E.sDS.sub (c := n - nk + i) (l := 1) (by omega)
    rw [hDk, add_ofNat_assoc]
    exact (hagree _ hD.symm hS'.symm).symm
  have hfl : pre.length + k = msg'.length / 64 := by
    rw [← fullBlocks_length, hfull, List.length_append, blocks_length _ _ (by rw [memBytes_length]; exact hkk)]
  have RG : G + 0xFFFFFF20 = R := by
    show sp0 + 0xFFFFFFE0 + 0xFFFFFF20 = sp0 + 0xFFFFFF00; rw [BitVec.add_assoc]; rfl
  have e60 : S + 0x40 + 0x20 = S + BitVec.ofNat 32 0x60 := by rw [BitVec.add_assoc]; rfl
  have e40 : S + 0x40 = S + BitVec.ofNat 32 0x40 := rfl
  have hS40 : (S + 0x40).toNat = S.toNat + 0x40 := by
    rw [e40, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hS60 : (S + 0x40 + 0x20).toNat = S.toNat + 0x60 := by
    rw [e60, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  -- The whole blocks of the input, compressed in place.
  have H8 : ∃ n8 Mc, Steps nn n8 ∧ St Mc U n8 0x8C (reg n8) ∧
      wordsAt Mc (S + 0x40) 8 = (pre ++ Sha256.blocks k (memBytes M0 Dk nk)).foldl Sha256.compress Sha256.h0 ∧
      memLoad32 Mc (S + 0x60) = BitVec.ofNat 32 (pre.length + k) ∧ memLoad32 Mc (S + 0x64) = 0 ∧
      (∀ x, Sep R 0xE0 x 1 → Sep (S + 0x40) 40 x 1 → Mc x = Mx x) ∧
      reg n8 s1 = BitVec.ofNat 32 (nk % 64) ∧ reg n8 s3 = Dk + BitVec.ofNat 32 (64 * k) ∧
      (∀ r, r ≠ ra → r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 →
        r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ s1 → r ≠ s3 → r ≠ (28 : Fin 32) →
        r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) → reg n8 r = f r) := by
    by_cases hk0 : k = 0
    · obtain ⟨n7, d7, u7⟩ := u6'.taken cU 0x8C su_at_80 (by decide) (by
        simp only [branchTaken]; rw [K6 a2 (by decide), K5 a2 (by decide), K4 a2 (by decide), g3, u6'.zero, hk0]
        rfl)
      refine ⟨n7, Mx, c6.trans (.single d7), u7.self, ?_, ?_, ?_, fun _ _ _ => rfl, ?_, ?_,
        fun r q1 q3 q5 q6 q7 q10 q11 q12 _ _ _ _ _ q9 q19 _ _ _ _ => ?_⟩
      · rw [hhash, hk0]; simp [Sha256.blocks]
      · rw [hlo, hk0]; rfl
      · exact hhi
      · rw [u7.regs, K6 s1 (by decide), g5]
      · rw [u7.regs, g6]
      · rw [u7.regs, K16 r q10 q12 q9 q19]
    · obtain ⟨n7, d7, u7⟩ := u6'.notTaken cU 0x82 su_at_80 (by decide) (by
        simp only [branchTaken]; rw [K6 a2 (by decide), K5 a2 (by decide), K4 a2 (by decide), g3, u6'.zero]
        rw [beq_eq_false_iff_ne]
        intro h; exact hk0 (ofNat_inj (by omega) (by decide) h))
      obtain ⟨n8, d8, u8⟩ := u7.alu cU su_at_82 (off' := 0x84) (by decide)
      have g8 : reg n8 a0 = S + 0x40 := by
        rw [u8.upd_eq (by decide), u6'.zero, K16 s2 (by decide) (by decide) (by decide) (by decide), fs2]
        exact BitVec.zero_add _
      have K8 := u8.upd_ne u6'.zero
      have u8' : St Mx U n8 0x84 (reg n8) := u8.self
      obtain ⟨n9, d9, u9⟩ := u8'.auipc cU su_at_84 (off' := 0x88) (by decide)
      obtain ⟨n10, d10, pc10, mem10, regs10⟩ := u9.call cU su_at_88
      have r10 : ∀ r, r ≠ ra → reg n10 r = reg n8 r := fun r h => by
        rw [regs10]
        by_cases h0 : r.val = 0
        · have : r = 0 := Fin.ext h0
          subst this; simp [upd]; exact u8'.zero.symm
        · simp [upd, h0, h]
      have ra10 : reg n10 ra = U + BitVec.ofNat 32 0x8C := by rw [regs10]; simp +decide [upd]; rfl
      have pc10' : n10.pc = BitVec.ofNat 32 shaUpdateBlocksAddress := by
        rw [pc10, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]
        decide
      have cX10 : ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
          b.toNat + code.length ≤ 2 ^ 32 → CodeIn n10.mem b code := fun b code hc hb hbl => by
        rw [mem10]; exact codeX Mx hagree b code hc hb hbl
      have sR : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 → Sep R 0xE0 b l :=
        fun b l hb hbl => data_code (by rw [hRn]; omega) hb hbl
      have s40 : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 → Sep (S + 0x40) 32 b l :=
        fun b l hb hbl => data_code (by rw [hS40]; omega) hb hbl
      have s60 : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
          Sep (S + 0x40 + 0x20) 8 b l := fun b l hb hbl => data_code (by rw [hS60]; omega) hb hbl
      have kR : Sep R 0xE0 (BitVec.ofNat 32 shaKAddress) 256 := by
        have := E.sKF.symm.sub (c := 0) (l := 0xE0) (by omega); rwa [add_ofNat_zero] at this
      have kS : ∀ c l, c + l ≤ 0x68 → Sep (S + BitVec.ofNat 32 c) l (BitVec.ofNat 32 shaKAddress) 256 :=
        fun c l h => E.sKS.symm.sub (c := c) (l := l) h
      have dR : Sep Dk (64 * k) R 0xE0 := by
        rw [hDk]; exact (E.sDF.sub (c := n - nk) (l := 64 * k) (by omega)).subR (c := 0) (l := 0xE0) (by omega)
          |> fun h => by rwa [add_ofNat_zero] at h
      have dS : ∀ c l, c + l ≤ 0x68 → Sep Dk (64 * k) (S + BitVec.ofNat 32 c) l := fun c l h => by
        rw [hDk]; exact (E.sDS.sub (c := n - nk) (l := 64 * k) (by omega)).subR (c := c) (l := l) h
      have SR : ∀ c l, c + l ≤ 0x68 → Sep (S + BitVec.ofNat 32 c) l R 0xE0 := fun c l h =>
        (E.sSF.sub (c := c) (l := l) h).subR (c := 0) (l := 0xE0) (by omega) |> fun h' => by
          rwa [add_ofNat_zero] at h'
      have env : SCEnv n10.mem (BitVec.ofNat 32 sha256CompressAddress) G (S + 0x40) Dk k :=
        { hP := by decide
          code := cX10 _ _ E.cC (by decide) (by decide)
          idx := cX10 _ _ E.cI (by decide) (by decide)
          o97 := cX10 _ _ E.c97 (by decide) (by decide)
          kdata := fun i hi => by
            have hi' : i < 256 := by rw [show shaKData.length = 256 from rfl] at hi; exact hi
            rw [mem10, hagree _ ((E.sKF.sub (c := i) (l := 1) (by omega)).symm)
              ((E.sKS.sub (c := i) (l := 1) (by omega)).symm)]
            exact E.cK i hi
          hsp := hGa
          hS := by rw [hGn]; omega
          hstp := by rw [hS40]; have := E.hS; omega
          hwbp := by rw [hDkn]; omega
          sC := by rw [RG]; exact sR _ _ (by decide) (by decide)
          sI := by rw [RG]; exact sR _ _ (by decide) (by decide)
          s97 := by rw [RG]; exact sR _ _ (by decide) (by decide)
          sK := by rw [RG]; exact kR
          stC := s40 _ _ (by decide) (by decide)
          stI := s40 _ _ (by decide) (by decide)
          st97 := s40 _ _ (by decide) (by decide)
          stK := by rw [e40]; exact kS 0x40 32 (by omega)
          stF := by rw [RG, e40]; exact SR 0x40 32 (by omega)
          bF := by rw [RG]; exact dR
          bSt := by rw [e40]; exact dS 0x40 32 (by omega) }
      have lo10 : memLoad32 n10.mem (S + 0x40 + 0x20) = BitVec.ofNat 32 pre.length := by rw [mem10, e60]; exact hlo
      obtain ⟨n11, c11, pc11, sp11, K11, w11, lo11, hi11, fr11⟩ := shaBlocks_correct n10
        (cX10 _ _ E.cBlk (by decide) (by decide)) pc10' env
        (by rw [r10 a0 (by decide), g8]) (by rw [r10 a1 (by decide), K8 a1 (by decide), K16 a1 (by decide)
          (by decide) (by decide) (by decide), fa1])
        (by rw [r10 a2 (by decide), K8 a2 (by decide), K6 a2 (by decide), K5 a2 (by decide), K4 a2 (by decide), g3])
        ra10 (by decide)
        (by rw [r10 sp (by decide), K8 sp (by decide), K16 sp (by decide) (by decide) (by decide) (by decide), fsp])
        (by rw [lo10, BitVec.toNat_ofNat]; omega)
        (s60 _ _ (by decide) (by decide)) (s60 _ _ (by decide) (by decide)) (s60 _ _ (by decide) (by decide))
        (by rw [e60]; exact kS 0x60 8 (by omega)) (by rw [RG, e60]; exact SR 0x60 8 (by omega))
        (by rw [e60]; exact dS 0x60 8 (by omega)) (s60 _ _ (by decide) (by decide))
      have k11 : ∀ r, r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 → r ≠ a2 →
          r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) →
          r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) → reg n11 r = reg n10 r := fun r q3 q5 q6 q7 q10 q11 q12 q13
          q14 q15 q16 q17 q28 q29 q30 q31 => K11 r q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31
      refine ⟨n11, n11.mem, c6.trans (.cons d7 (.cons d8 (.cons d9 (.cons d10 c11)))),
        ⟨by rw [pc11], rfl, fun _ => rfl⟩, ?_, ?_, ?_, fun x hx hy => ?_, ?_, ?_,
        fun r q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q9 q19 q28 q29 q30 q31 => ?_⟩
      · rw [w11, mem10, hhash, hblk, List.foldl_append]
      · rw [show S + (0x60 : Word) = S + 0x40 + 0x20 from e60.symm, lo11, lo10, BitVec.ofNat_add_ofNat]
      · rw [show S + (0x64 : Word) = S + 0x40 + 0x24 by rw [BitVec.add_assoc]; rfl, hi11, mem10,
          show S + 0x40 + (0x24 : Word) = S + 0x64 by rw [BitVec.add_assoc]; rfl]
        exact hhi
      · rw [fr11 x (by rw [RG]; exact hx) hy, mem10]
      · rw [k11 s1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          r10 s1 (by decide), K8 s1 (by decide), K6 s1 (by decide), g5]
      · rw [k11 s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          r10 s3 (by decide), K8 s3 (by decide), g6]
      · rw [k11 r q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31, r10 r q1, K8 r q10,
          K16 r q10 q12 q9 q19]
  obtain ⟨n8, Mc, c8, u8, w8, lo8, hi8, fr8, s1_8, s3_8, K8'⟩ := H8
  have hMc : ∀ x, Sep R 0x100 x 1 → Sep S 0x68 x 1 → Mc x = M0 x := fun x hx hy => by
    rw [fr8 x (by have := hx.sub (c := 0) (l := 0xE0) (by omega); rwa [add_ofNat_zero] at this)
      (by rw [e40]; exact hy.sub (c := 0x40) (l := 40) (by omega)), hagree x hx hy]
  have cU8 := codeX Mc hMc _ _ E.cU (by decide) (by decide)
  have s4_8 : reg n8 s4 = S := by
    rw [K8' s4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), fs4]
  have sp8 : reg n8 sp = G := by
    rw [K8' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), fsp]
  obtain ⟨n9, d9, u9⟩ := u8.alu cU8 su_at_8c (off' := 0x8E) (by decide)
  have K9 := u9.upd_ne u8.zero
  have u9' : St Mc U n9 0x8E (reg n9) := u9.self
  obtain ⟨n10, d10, u10⟩ := u9'.alu cU8 su_at_8e (off' := 0x90) (by decide)
  have K10 := u10.upd_ne u9'.zero
  have u10' : St Mc U n10 0x90 (reg n10) := u10.self
  obtain ⟨n11, d11, u11⟩ := u10'.alu cU8 su_at_90 (off' := 0x92) (by decide)
  have K11 := u11.upd_ne u10'.zero
  have u11' : St Mc U n11 0x92 (reg n11) := u11.self
  have a0_11 : reg n11 a0 = S := by
    rw [K11 a0 (by decide), K10 a0 (by decide), u9.upd_eq (by decide), u8.zero, s4_8]; exact BitVec.zero_add _
  have a1_11 : reg n11 a1 = Dk + BitVec.ofNat 32 (64 * k) := by
    rw [K11 a1 (by decide), u10.upd_eq (by decide), u9'.zero, K9 s3 (by decide), s3_8]; exact BitVec.zero_add _
  have s1_11 : reg n11 s1 = BitVec.ofNat 32 (nk % 64) := by
    rw [K11 s1 (by decide), K10 s1 (by decide), K9 s1 (by decide), s1_8]
  have a2_11 : reg n11 a2 = BitVec.ofNat 32 (nk % 64) := by
    rw [u11.upd_eq (by decide), u10'.zero, K10 s1 (by decide), K9 s1 (by decide), s1_8]; exact BitVec.zero_add _
  have s4_11 : reg n11 s4 = S := by rw [K11 s4 (by decide), K10 s4 (by decide), K9 s4 (by decide), s4_8]
  have sp11 : reg n11 sp = G := by rw [K11 sp (by decide), K10 sp (by decide), K9 sp (by decide), sp8]
  obtain ⟨n12, d12, u12⟩ := u11'.sb cU8 su_at_92 (off' := 0x96) (by decide)
  rw [s4_11, s1_11] at u12
  let pv := (BitVec.ofNat 32 (nk % 64)).extractLsb' 0 8
  let Mt := memStore8 Mc (S + 0x3F) pv
  have e3F : S + 0x3F = S + BitVec.ofNat 32 0x3F := rfl
  have hMt : ∀ x, Sep R 0x100 x 1 → Sep S 0x68 x 1 → Mt x = M0 x := fun x hx hy => by
    have hne : x ≠ S + 0x3F := fun e => by
      have := hy 0x3F (by omega) 0 (by decide); rw [add_ofNat_zero, ← e3F] at this; exact this e.symm
    show memStore8 Mc _ _ x = _
    rw [memStore8_ne hne, hMc x hx hy]
  have cUt := codeX Mt hMt _ _ E.cU (by decide) (by decide)
  have cRt := codeX Mt hMt _ _ E.cRest (by decide) (by decide)
  obtain ⟨n13, c13, pc13, mem13, regs13⟩ := upd_tail u12 cUt cRt sp11 hGa
  have z11 : reg n11 0 = 0 := u11'.zero
  have oth : ∀ r, r ≠ t1 → r ≠ ra → r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ s3 → r ≠ s4 → r ≠ sp → r ≠ t0 →
      reg n13 r = reg n11 r := fun r q6 q1 q8 q9 q18 q19 q20 q2 q5 => by
    rw [regs13 r q6]; exact updR_other _ _ _ _ _ z11 r q1 q8 q9 q18 q19 q20 q2 q5
  obtain ⟨vra, vs0, vs1, vs2, vs3, vs4, vsp⟩ := updR_saved Mt G (G + 0x20)
    (BitVec.ofNat 32 shaUpdateAddress + BitVec.ofNat 32 (0x96 + 8)) (reg n11)
  -- The frame's saved slots survive, so the restore helper gives back the entry registers.
  have slotX : ∀ k', 8 ≤ k' → k' < 32 → Mt (G + BitVec.ofNat 32 k') = Mx (G + BitVec.ofNat 32 k') := by
    intro k' h1 h2
    have hGk : G + BitVec.ofNat 32 k' = R + BitVec.ofNat 32 (0xE0 + k') := by rw [hGR, add_ofNat_assoc]
    have sk : Sep (S + 0x40) 40 (G + BitVec.ofNat 32 k') 1 := by
      rw [e40, hGk]; exact (E.sSF.sub (c := 0x40) (l := 40) (by omega)).subR (c := 0xE0 + k') (l := 1) (by omega)
    have rk : Sep R 0xE0 (G + BitVec.ofNat 32 k') 1 := by
      rw [hGk]; have := sep_offsets R (c := 0) (n := 0xE0) (d := 0xE0 + k') (k := 1) (by omega) (by omega)
        (by omega); rwa [add_ofNat_zero] at this
    have hne : G + BitVec.ofNat 32 k' ≠ S + 0x3F := by
      intro e
      have := (E.sSF.sub (c := 0x3F) (l := 1) (by omega)).subR (c := 0xE0 + k') (l := 1) (by omega) 0 (by decide)
        0 (by decide)
      rw [add_ofNat_zero, add_ofNat_zero, ← hGk, ← e3F] at this; exact this e.symm
    show memStore8 Mc _ _ _ = _
    rw [memStore8_ne hne, fr8 _ rk sk]
  obtain ⟨hra', hs0', hs1', hs2', hs3', hs4'⟩ := hslots Mt slotX
  have sp13 : reg n13 sp = sp0 := by
    rw [regs13 sp (by decide), vsp]; show sp0 + 0xFFFFFFE0 + 0x20 = sp0; rw [BitVec.add_assoc]; exact BitVec.add_zero _
  -- The tail call of `memcpy` buffers the bytes left over.
  let Sk := Dk + BitVec.ofNat 32 (64 * k)
  have hSkn : Sk.toNat = D.toNat + (n - nk) + 64 * k := by
    show (Dk + BitVec.ofNat 32 (64 * k)).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hDkn, Nat.mod_eq_of_lt (a := 64 * k) (by omega)]; omega
  have hSk : Sk = D + BitVec.ofNat 32 (n - nk + 64 * k) := by
    show Dk + BitVec.ofNat 32 (64 * k) = _; rw [hDk, add_ofNat_assoc]
  let F' := sp0 + 0xFFFFFFF0
  have hF' : F' = R + BitVec.ofNat 32 0xF0 := by
    show sp0 + 0xFFFFFFF0 = sp0 + 0xFFFFFF00 + BitVec.ofNat 32 0xF0; rw [BitVec.add_assoc]; rfl
  have hF'n : F'.toNat = sp0.toNat - 16 := by
    show (sp0 + 0xFFFFFFF0).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 2 ^ 32 - 16 from rfl]; omega
  have hnr : nk % 64 + (n - nk + 64 * k) ≤ n := by omega
  have hFe : sp0 + (0xFFFFFFF0 : Word) = R + BitVec.ofNat 32 0xF0 := hF'
  have hFn : (sp0 + (0xFFFFFFF0 : Word)).toNat = sp0.toNat - 16 := hF'n
  have E' : McEnv n13.mem (BitVec.ofNat 32 memcpyStubAddress + 8) S Sk (reg n13 sp + 0xFFFFFFF0) (nk % 64) := by
    rw [sp13, mem13]
    exact { code := codeX Mt hMt _ _ E.cMB (by decide) (by decide)
            hDC := data_code (by omega) (by decide) (by decide)
            hFC := data_code (by rw [hFn]; omega) (by decide) (by decide)
            hdF := by
              rw [hFe]; exact (E.sSF.sub (c := 0) (l := nk % 64) (by omega)).subR (c := 0xF0) (l := 16) (by omega)
                |> fun h => by rwa [add_ofNat_zero] at h
            hsF := by
              rw [hFe, hSk]
              exact (E.sDF.sub (c := n - nk + 64 * k) (l := nk % 64) (by omega)).subR (c := 0xF0) (l := 16)
                (by omega)
            hsep := by
              rw [hSk]
              have h := (E.sDS.sub (c := n - nk + 64 * k) (l := nk % 64) (by omega)).subR (c := 0)
                (l := nk % 64) (by omega)
              rw [add_ofNat_zero] at h
              exact h.symm
            hF := by rw [hFn]; have := E.hsp; omega
            hFw := by rw [hFn]; omega
            hdw := by omega
            hsw := by rw [hSkn]; omega }
  obtain ⟨n14, c14, pc14, sp14, a014, mem14, K14⟩ := memcpy_correct n13 (BitVec.ofNat 32 memcpyStubAddress) rRa
    S Sk (nk % 64) (fun i hi => by
      show n13.mem _ = _; rw [mem13]; exact codeX Mt hMt _ _ E.cMS (by decide) (by decide) i hi) (by decide) pc13
    (by rw [oth a0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), a0_11])
    (by rw [oth a1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), a1_11])
    (by rw [oth a2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), a2_11])
    (by rw [regs13 ra (by decide), vra, hra']) hret E'
  rw [sp13, mem13] at mem14
  have hlen64 : msg'.length % 64 = nk % 64 := by
    have := tailBytes_length msg'; rw [htail, List.length_drop, memBytes_length] at this; omega
  have hN : nk % 64 < 2 ^ 32 := by omega
  -- Bytes of the hasher after the tail call.
  have atS : ∀ c, c < 0x68 → n14.mem (S + BitVec.ofNat 32 c) = copyBytes Mt S Sk (nk % 64) (S + BitVec.ofNat 32 c) :=
    fun c hc => mem14 _ (by
      rw [hFe]; exact ((E.sSF.sub (c := c) (l := 1) (by omega)).subR (c := 0xF0) (l := 16) (by omega)).symm)
  have hiS : ∀ c, 0x40 ≤ c → c < 0x68 → n14.mem (S + BitVec.ofNat 32 c) = Mc (S + BitVec.ofNat 32 c) := by
    intro c h1 h2
    rw [atS c h2, copyBytes_out (by rw [add_sub_toNat S (by omega)]; omega)]
    show memStore8 Mc _ _ _ = _
    rw [memStore8_ne (by rw [e3F]; exact add_ofNat_ne S (by omega) (by omega) (by omega))]
  have ld : ∀ c, 0x40 ≤ c → c + 4 ≤ 0x68 → memLoad32 n14.mem (S + BitVec.ofNat 32 c) = memLoad32 Mc (S + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact hiS _ (by omega) (by omega)
  have pvE : pv = BitVec.ofNat 8 (msg'.length % 64) := by
    rw [hlen64]; apply BitVec.eq_of_toNat_eq
    show ((BitVec.ofNat 32 (nk % 64)).extractLsb' 0 8).toNat = _
    rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]; omega
  have H' : HasherAt n14.mem S msg' :=
    { hlen := hlen
      pos := by
        rw [e3F, atS 0x3F (by omega), copyBytes_out (by rw [add_sub_toNat S (by omega)]; omega), ← e3F]
        show memStore8 Mc _ _ _ = _
        rw [memStore8_same, pvE]
      buf := by
        rw [hlen64, htail, memBytes_drop _ _ hkk, show nk - 64 * k = nk % 64 by show nk - 64 * (nk / 64) = _; omega]
        unfold memBytes
        apply List.map_congr_left
        intro i hi
        have hi := List.mem_range.mp hi
        have h1 : Mt (Sk + BitVec.ofNat 32 i) = M0 (Sk + BitVec.ofNat 32 i) := by
          apply hMt
          · rw [hSk, add_ofNat_assoc]
            exact (E.sDF.sub (c := n - nk + 64 * k + i) (l := 1) (by omega)).symm
          · rw [hSk, add_ofNat_assoc]
            exact (E.sDS.sub (c := n - nk + 64 * k + i) (l := 1) (by omega)).symm
        rw [atS i (by omega), copyBytes_in hi hN, h1]
      hash := by
        rw [hfull, ← w8]
        apply wordsAt_congr; intro i hi
        rw [e40, add_ofNat_assoc]; exact ld _ (by omega) (by omega)
      lo := by
        rw [show S + (0x60 : Word) = S + BitVec.ofNat 32 0x60 from rfl, ld 0x60 (by omega) (by omega),
          show S + BitVec.ofNat 32 0x60 = S + 0x60 from rfl, lo8, hfl]
      hi := by
        rw [show S + (0x64 : Word) = S + BitVec.ofNat 32 0x64 from rfl, ld 0x64 (by omega) (by omega),
          show S + BitVec.ofNat 32 0x64 = S + 0x64 from rfl, hi8] }
  have k14 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp →
      reg n14 r = reg n13 r := K14
  refine ⟨n14, c8.trans (.cons d9 (.cons d10 (.cons d11 (.cons d12 (c13.trans c14))))), pc14, by rw [sp14, sp13],
    ?_, ?_, ?_, ?_, ?_, fun r q1 q2 q3 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q28 q29 q30 q31 =>
      ?_, H', fun x hx hy => ?_⟩
  · rw [k14 s0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), regs13 s0 (by decide), vs0, hs0']
  · rw [k14 s1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), regs13 s1 (by decide), vs1, hs1']
  · rw [k14 s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), regs13 s2 (by decide), vs2, hs2']
  · rw [k14 s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), regs13 s3 (by decide), vs3, hs3']
  · rw [k14 s4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), regs13 s4 (by decide), vs4, hs4']
  · rw [k14 r q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2, oth r q6 q1 q8 q9 q18 q19 q20 q2 q5,
      K11 r q12, K10 r q11, K9 r q10, K8' r q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q9 q19 q28 q29 q30 q31]
  · have hxF : Sep (sp0 + 0xFFFFFFF0) 16 x 1 := by
      rw [hFe]; exact hx.sub (c := 0xF0) (l := 16) (by omega)
    rw [mem14 x hxF, copyBytes_out (fun hlt => by
      have e := sub_eq_ofNat (k := (x - S).toNat) (x - S).isLt rfl
      have := hy (x - S).toNat (by omega) 0 (by decide); rw [add_ofNat_zero] at this; exact this e.symm)]
    exact hMt x hx hy

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
/-- **The compiled `update` of `sha2`'s SHA-256.** Called with the hasher
at `S` holding `msg` and `n` bytes at `D`, it leaves the hasher holding
`msg` followed by those bytes, returns to `retAddr` with `sp` restored and
the callee-saved registers kept, and changes no memory outside the hasher
and 0x100 bytes of stack below `sp`. `n` is below 2^31, as Rust's slice
lengths are, and the whole message stays below 2^32 bytes. -/
theorem shaUpdate_correct (m : Machine) {S D sp0 retAddr : Word} {n : Nat} {msg : Bytes}
    (E : UpdEnv m.mem S D sp0 n) (hpc : m.pc = BitVec.ofNat 32 shaUpdateAddress)
    (ha0 : reg m a0 = S) (ha1 : reg m a1 = D) (ha2 : reg m a2 = BitVec.ofNat 32 n)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (H : HasherAt m.mem S msg) (hn : n < 2 ^ 31) (hlen : msg.length + n < 2 ^ 32) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ r, r ≠ ra → r ≠ (3 : Fin 32) → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 →
        r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) →
        r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) → r ≠ sp → reg m' r = reg m r) ∧
      HasherAt m'.mem S (msg ++ memBytes m.mem D n) ∧
      ∀ x, Sep (sp0 + 0xFFFFFF00) 0x100 x 1 → Sep S 0x68 x 1 → m'.mem x = m.mem x := by
  let U := BitVec.ofNat 32 shaUpdateAddress
  let M0 := m.mem
  let G := sp0 + 0xFFFFFFE0
  let R := sp0 + 0xFFFFFF00
  let data := memBytes M0 D n
  let pos := msg.length % 64
  have hSw := E.hSw
  have hspw := E.hspw
  have hspl := E.hspl
  have hDw := E.hDw
  have hRn : R.toNat = sp0.toNat - 0x100 := by
    show (sp0 + 0xFFFFFF00).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFF00 : Word).toNat = 2 ^ 32 - 0x100 from rfl]; omega
  have hGn : G.toNat = sp0.toNat - 0x20 := by
    show (sp0 + 0xFFFFFFE0).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFFE0 : Word).toNat = 2 ^ 32 - 0x20 from rfl]; omega
  have hGa : G.toNat % 4 = 0 := by rw [hGn]; have := E.hsp; omega
  have hGR : G = R + BitVec.ofNat 32 0xE0 := by
    show sp0 + 0xFFFFFFE0 = sp0 + 0xFFFFFF00 + BitVec.ofNat 32 0xE0
    rw [BitVec.add_assoc]; rfl
  have codeX : ∀ (My : Word → BitVec 8), (∀ x, Sep R 0x100 x 1 → Sep S 0x68 x 1 → My x = M0 x) →
      ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn My b code := fun My h b code hc hb hbl i hi => by
    rw [h _ ((data_code (by rw [hRn]; omega) hb hbl).subR (c := i) (l := 1) (by omega))
      ((data_code (by omega) hb hbl).subR (c := i) (l := 1) (by omega))]
    exact hc i hi
  have st0 : St M0 U m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  obtain ⟨m2, M2, c2, u2, sp2, K2, out2, slots⟩ := upd_pro st0 E.cU E.cSave
    (by rw [hsp]) hGa (by rw [hGn]; omega)
  have hM2 : ∀ x, Sep R 0x100 x 1 → Sep S 0x68 x 1 → M2 x = M0 x := fun x hx _ => out2 x (by
    rw [hGR]; exact hx.sub (c := 0xE0) (l := 32) (by omega))
  have cU2 := codeX M2 hM2 _ _ E.cU (by decide) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.alu cU2 su_at_c (off' := 0x0E) (by decide)
  have K3 := u3.upd_ne u2.zero
  have u3' : St M2 U n3 0x0E (reg n3) := u3.self
  obtain ⟨n4, d4, u4⟩ := u3'.alu cU2 su_at_e (off' := 0x10) (by decide)
  have K4 := u4.upd_ne u3'.zero
  have u4' : St M2 U n4 0x10 (reg n4) := u4.self
  have s4_4 : reg n4 s4 = S := by
    rw [u4.upd_eq (by decide), u3'.zero, K3 a0 (by decide), K2 a0 (by decide) (by decide), ha0]
    exact BitVec.zero_add _
  have s1_4 : reg n4 s1 = BitVec.ofNat 32 n := by
    rw [K4 s1 (by decide), u3.upd_eq (by decide), u2.zero, K2 a2 (by decide) (by decide), ha2]
    exact BitVec.zero_add _
  obtain ⟨n5, d5, u5⟩ := u4'.lbu cU2 su_at_10 (off' := 0x14) (by decide)
  have SG : ∀ c, c < 0x68 → Sep G 32 (S + BitVec.ofNat 32 c) 1 := fun c hc => by
    rw [hGR]; exact ((E.sSF.sub (c := c) (l := 1) (by omega)).subR (c := 0xE0) (l := 32) (by omega)).symm
  have posB : M2 (S + 0x3F) = BitVec.ofNat 8 pos := by
    rw [show S + (0x3F : Word) = S + BitVec.ofNat 32 0x3F from rfl, out2 _ (SG 0x3F (by omega))]
    exact H.pos
  have a0_4 : reg n4 a0 = S := by rw [K4 a0 (by decide), K3 a0 (by decide), K2 a0 (by decide) (by decide), ha0]
  have g5 : reg n5 s0 = BitVec.ofNat 32 pos := by
    rw [u5.upd_eq (by decide), a0_4, posB]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hpos : pos < 64 := Nat.mod_lt _ (by decide)
  have K5 := u5.upd_ne u4'.zero
  have u5' : St M2 U n5 0x14 (reg n5) := u5.self
  obtain ⟨n6, d6, u6⟩ := u5'.aluImm cU2 su_at_14 (off' := 0x18) (by decide)
  have K6 := u6.upd_ne u5'.zero
  have u6' : St M2 U n6 0x18 (reg n6) := u6.self
  obtain ⟨n7, d7, u7⟩ := u6'.alu cU2 su_at_18 (off' := 0x1A) (by decide)
  have g7 : reg n7 a2 = BitVec.ofNat 32 (64 - pos) := by
    rw [u7.upd_eq (by decide), u6.upd_eq (by decide), u5'.zero, K6 s0 (by decide), g5,
      show aluEval .add (0 : Word) 0x40 = BitVec.ofNat 32 64 from rfl]
    exact sub_val (x := 64) (y := pos) (by omega) (by decide)
  have K7 := u7.upd_ne u6'.zero
  have u7' : St M2 U n7 0x1A (reg n7) := u7.self
  -- Registers so far, against the entry machine's.
  have K27 : ∀ r, r ≠ sp → r ≠ t0 → r ≠ s1 → r ≠ s4 → r ≠ s0 → r ≠ a2 → reg n7 r = reg m r :=
    fun r q2 q5 q9 q20 q8 q12 => by rw [K7 r q12, K6 r q12, K5 r q8, K4 r q20, K3 r q9, K2 r q2 q5]
  have s0_7 : reg n7 s0 = BitVec.ofNat 32 pos := by rw [K7 s0 (by decide), K6 s0 (by decide), g5]
  have s1_7 : reg n7 s1 = BitVec.ofNat 32 n := by
    rw [K7 s1 (by decide), K6 s1 (by decide), K5 s1 (by decide), s1_4]
  have s4_7 : reg n7 s4 = S := by rw [K7 s4 (by decide), K6 s4 (by decide), K5 s4 (by decide), s4_4]
  have a1_7 : reg n7 a1 = D := by rw [K27 a1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ha1]
  have sp7 : reg n7 sp = G := by
    rw [K7 sp (by decide), K6 sp (by decide), K5 sp (by decide), K4 sp (by decide), K3 sp (by decide), sp2]
  have c7 : Steps m n7 := c2.trans (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.single d7)))))
  have ultR := ult_lit (x := n) (y := 64 - pos) (by omega) (by omega)
  have hGF : G + 0xFFFFFFF0 = R + BitVec.ofNat 32 0xD0 := by
    show sp0 + 0xFFFFFFE0 + 0xFFFFFFF0 = sp0 + 0xFFFFFF00 + BitVec.ofNat 32 0xD0
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have hFn : (G + 0xFFFFFFF0).toNat = sp0.toNat - 0x30 := by
    rw [hGF, BitVec.toNat_add, BitVec.toNat_ofNat, hRn]; omega
  -- A `memcpy` call from `update`, with `sp` at `G`, of `N` bytes from `D` into the buffer at byte `p`.
  have mcEnv : ∀ (My : Word → BitVec 8) (p N : Nat), p + N ≤ 64 → N ≤ n →
      (∀ x, Sep R 0x100 x 1 → Sep S 0x68 x 1 → My x = M0 x) →
      McEnv My (BitVec.ofNat 32 memcpyStubAddress + 8) (S + BitVec.ofNat 32 p) D (G + 0xFFFFFFF0) N := by
    intro My p N hpN hNn hMy
    have hSp : (S + BitVec.ofNat 32 p).toNat = S.toNat + p := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    exact { code := codeX My hMy _ _ E.cMB (by decide) (by decide)
            hDC := data_code (by rw [hSp]; omega) (by decide) (by decide)
            hFC := data_code (by rw [hFn]; omega) (by decide) (by decide)
            hdF := by rw [hGF]; exact (E.sSF.sub (c := p) (l := N) (by omega)).subR (c := 0xD0) (l := 16) (by omega)
            hsF := by
              rw [hGF]; have h := (E.sDF.sub (c := 0) (l := N) (by omega)).subR (c := 0xD0) (l := 16) (by omega)
              rwa [add_ofNat_zero] at h
            hsep := by
              have h := (E.sDS.sub (c := 0) (l := N) (by omega)).subR (c := p) (l := N) (by omega)
              rw [add_ofNat_zero] at h; exact h.symm
            hF := by rw [hFn]; have := E.hsp; omega
            hFw := by rw [hFn]; omega
            hdw := by rw [hSp]; omega
            hsw := by omega }
  -- After such a call, memory outside the stack area and the hasher is the entry memory's.
  have mcOut : ∀ (My Mz : Word → BitVec 8) (p N : Nat), p + N ≤ 0x68 →
      (∀ x, Sep R 0x100 x 1 → Sep S 0x68 x 1 → My x = M0 x) →
      (∀ x, Sep (G + 0xFFFFFFF0) 16 x 1 → Mz x = copyBytes My (S + BitVec.ofNat 32 p) D N x) →
      ∀ x, Sep R 0x100 x 1 → Sep S 0x68 x 1 → Mz x = M0 x := by
    intro My Mz p N hpN hMy hMz x hx hy
    rw [hMz x (by rw [hGF]; exact hx.sub (c := 0xD0) (l := 16) (by omega)),
      copyBytes_sep (hy.sub (c := p) (l := N) hpN) (Nat.le_refl N), hMy x hx hy]
  have hposd : pos = msg.length % 64 := rfl
  have hdata : data.length = n := memBytes_length _ _ _
  have hmsgd : msg ++ memBytes m.mem D n = msg ++ data := rfl
  have zR : reg n7 0 = 0 := u7'.zero
  by_cases hA : n < 64 - pos
  · -- The bytes fit in the buffer: copy them in and store the new count.
    obtain ⟨n8, d8, u8⟩ := u7'.notTaken cU2 0x1E su_at_1a (by decide) (by
      simp only [branchTaken]; rw [s1_7, g7, ultR]; simp only [Bool.not_eq_false']
      exact decide_eq_true hA)
    obtain ⟨n9, d9, u9⟩ := u8.alu cU2 su_at_1e (off' := 0x22) (by decide)
    have K9 := u9.upd_ne zR
    have u9' : St M2 U n9 0x22 (reg n9) := u9.self
    have a0_9 : reg n9 a0 = S + BitVec.ofNat 32 pos := by rw [u9.upd_eq (by decide), s4_7, s0_7]; rfl
    obtain ⟨n10, d10, u10⟩ := u9'.alu cU2 su_at_22 (off' := 0x24) (by decide)
    have K10 := u10.upd_ne u9'.zero
    have u10' : St M2 U n10 0x24 (reg n10) := u10.self
    have a2_10 : reg n10 a2 = BitVec.ofNat 32 n := by
      rw [u10.upd_eq (by decide), u9'.zero, K9 s1 (by decide), s1_7]; exact BitVec.zero_add _
    obtain ⟨n11, d11, u11⟩ := u10'.auipc cU2 su_at_24 (off' := 0x28) (by decide)
    obtain ⟨n12, d12, pc12, mem12, regs12⟩ := u11.call cU2 su_at_28
    have r12 : ∀ r, r ≠ ra → reg n12 r = reg n10 r := fun r h => by
      rw [regs12]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd]; exact u10'.zero.symm
      · simp [upd, h0, h]
    have ra12 : reg n12 ra = U + BitVec.ofNat 32 0x2C := by rw [regs12]; simp +decide [upd]; rfl
    have pc12' : n12.pc = BitVec.ofNat 32 memcpyStubAddress := by
      rw [pc12, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]
      decide
    have sp12 : reg n12 sp = G := by rw [r12 sp (by decide), K10 sp (by decide), K9 sp (by decide), sp7]
    obtain ⟨n13, c13, pc13, sp13, a013, mem13, K13⟩ := memcpy_correct n12 (BitVec.ofNat 32 memcpyStubAddress)
      (U + BitVec.ofNat 32 0x2C) (S + BitVec.ofNat 32 pos) D n (fun i hi => by
        show n12.mem _ = _; rw [mem12]; exact codeX M2 hM2 _ _ E.cMS (by decide) (by decide) i hi) (by decide) pc12'
      (by rw [r12 a0 (by decide), K10 a0 (by decide), a0_9])
      (by rw [r12 a1 (by decide), K10 a1 (by decide), K9 a1 (by decide), a1_7])
      (by rw [r12 a2 (by decide), a2_10]) ra12 (by decide)
      (by rw [mem12, sp12]; exact mcEnv M2 pos n (by omega) (Nat.le_refl n) hM2)
    rw [sp12, mem12] at mem13
    let MA := n13.mem
    have mA : ∀ x, Sep (G + 0xFFFFFFF0) 16 x 1 → MA x = copyBytes M2 (S + BitVec.ofNat 32 pos) D n x := mem13
    have hMA := mcOut M2 MA pos n (by omega) hM2 mem13
    have cUA := codeX MA hMA _ _ E.cU (by decide) (by decide)
    have u13 : St MA U n13 0x2C (reg n13) := ⟨by rw [pc13], rfl, fun _ => rfl⟩
    have k13 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
        r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp →
        reg n13 r = reg n12 r := K13
    have K7_13 : ∀ r, r ≠ ra → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 →
        r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) →
        r ≠ (30 : Fin 32) → r ≠ sp → reg n13 r = reg n7 r :=
      fun r q1 q10 q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2 => by
        rw [k13 r q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2, r12 r q1, K10 r q12, K9 r q10]
    obtain ⟨n14, d14, u14⟩ := u13.alu cUA su_at_2c (off' := 0x2E) (by decide)
    have K14 := u14.upd_ne u13.zero
    have u14' : St MA U n14 0x2E (reg n14) := u14.self
    have s0_14 : reg n14 s0 = BitVec.ofNat 32 (pos + n) := by
      rw [u14.upd_eq (by decide), K7_13 s0 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), s0_7,
        K7_13 s1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), s1_7]
      exact BitVec.ofNat_add_ofNat _ _
    have s4_14 : reg n14 s4 = S := by
      rw [K14 s4 (by decide), K7_13 s4 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), s4_7]
    have sp14 : reg n14 sp = G := by
      rw [K14 sp (by decide), sp13, sp12]
    obtain ⟨n15, d15, u15⟩ := u14'.sb cUA su_at_2e (off' := 0x32) (by decide)
    rw [s4_14, s0_14] at u15
    let pv := (BitVec.ofNat 32 (pos + n)).extractLsb' 0 8
    let Mt := memStore8 MA (S + 0x3F) pv
    have e3F : S + 0x3F = S + BitVec.ofNat 32 0x3F := rfl
    have hMt : ∀ x, Sep R 0x100 x 1 → Sep S 0x68 x 1 → Mt x = M0 x := fun x hx hy => by
      have hne : x ≠ S + 0x3F := fun e => by
        have := hy 0x3F (by omega) 0 (by decide); rw [add_ofNat_zero, ← e3F] at this; exact this e.symm
      show memStore8 MA _ _ x = _
      rw [memStore8_ne hne, hMA x hx hy]
    have cUt := codeX Mt hMt _ _ E.cU (by decide) (by decide)
    have cRt := codeX Mt hMt _ _ E.cRest (by decide) (by decide)
    obtain ⟨n16, c16, pc16, mem16, regs16⟩ := upd_ret u15 cUt cRt sp14 hGa
    have SF : ∀ c, c < 0x68 → Sep (G + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 c) 1 := fun c hc => by
      rw [hGF]; exact ((E.sSF.sub (c := c) (l := 1) (by omega)).subR (c := 0xD0) (l := 16) (by omega)).symm
    -- The hasher's bytes after the buffer's new bytes are the entry memory's.
    have hiS : ∀ c, pos + n ≤ c → c ≠ 0x3F → c < 0x68 → Mt (S + BitVec.ofNat 32 c) = M0 (S + BitVec.ofNat 32 c) := by
      intro c h1 h2 h3
      show memStore8 MA _ _ _ = _
      rw [memStore8_ne (by rw [e3F]; exact add_ofNat_ne S (by omega) (by omega) h2), mA _ (SF c h3),
        copyBytes_sep (sep_offsets S (c := pos) (n := n) (d := c) (k := 1) (Or.inl h1) (by omega) (by omega))
          (Nat.le_refl n), out2 _ (SG c h3)]
    have ld : ∀ c, 0x40 ≤ c → c + 4 ≤ 0x68 →
        memLoad32 Mt (S + BitVec.ofNat 32 c) = memLoad32 M0 (S + BitVec.ofNat 32 c) :=
      fun c h1 h2 => memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact hiS _ (by omega) (by omega) (by omega)
    have slotX : ∀ k', 8 ≤ k' → k' < 32 → Mt (G + BitVec.ofNat 32 k') = M2 (G + BitVec.ofNat 32 k') := by
      intro k' h1 h2
      have hGk : G + BitVec.ofNat 32 k' = R + BitVec.ofNat 32 (0xE0 + k') := by rw [hGR, add_ofNat_assoc]
      have hne : G + BitVec.ofNat 32 k' ≠ S + 0x3F := by
        intro e
        have := (E.sSF.sub (c := 0x3F) (l := 1) (by omega)).subR (c := 0xE0 + k') (l := 1) (by omega) 0 (by decide)
          0 (by decide)
        rw [add_ofNat_zero, add_ofNat_zero, ← hGk, ← e3F] at this; exact this e.symm
      show memStore8 MA _ _ _ = _
      rw [memStore8_ne hne, mA (G + BitVec.ofNat 32 k') (by
          rw [hGF, hGk]; exact sep_offsets R (c := 0xD0) (n := 16) (d := 0xE0 + k') (k := 1) (Or.inl (by omega))
            (by omega) (by omega)),
        copyBytes_sep (by
          rw [hGk]; exact (E.sSF.sub (c := pos) (l := n) (by omega)).subR (c := 0xE0 + k') (l := 1) (by omega))
          (Nat.le_refl n)]
    obtain ⟨hra', hs0', hs1', hs2', hs3', hs4'⟩ := slots Mt slotX
    obtain ⟨vra, vs0, vs1, vs2, vs3, vs4, vsp⟩ := updR_saved Mt G (G + 0x20)
      (BitVec.ofNat 32 shaUpdateAddress + BitVec.ofNat 32 (0x32 + 8)) (reg n14)
    have hm : (msg ++ data).length % 64 = pos + n := by rw [List.length_append, hdata]; omega
    obtain ⟨hf1, hf2⟩ := fullBlocks_append msg data
    rw [tailBytes_length, hdata, show (msg.length % 64 + n) / 64 = 0 by omega] at hf1 hf2
    have H' : HasherAt Mt S (msg ++ data) :=
      { hlen := by rw [List.length_append, hdata]; omega
        pos := by
          rw [hm]; show memStore8 MA _ _ _ = _
          rw [memStore8_same]; apply BitVec.eq_of_toNat_eq
          show ((BitVec.ofNat 32 (pos + n)).extractLsb' 0 8).toNat = _
          rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]; omega
        buf := by
          rw [hm, hf2, Nat.mul_zero, List.drop_zero, ← H.buf, memBytes_split]
          have b1 : memBytes Mt S pos = memBytes M0 S pos := memBytes_congr fun i hi => by
            show memStore8 MA _ _ _ = _
            rw [memStore8_ne (by rw [e3F]; exact add_ofNat_ne S (by omega) (by omega) (by omega)),
              mA _ (SF i (by omega)),
              copyBytes_sep (sep_offsets S (c := pos) (n := n) (d := i) (k := 1) (Or.inr (by omega)) (by omega)
                (by omega)) (Nat.le_refl n), out2 _ (SG i (by omega))]
          have b2 : memBytes Mt (S + BitVec.ofNat 32 pos) n = data := by
            unfold memBytes
            apply List.map_congr_left
            intro i hi
            have hi := List.mem_range.mp hi
            show (Mt (S + BitVec.ofNat 32 pos + BitVec.ofNat 32 i)).toNat = (M0 (D + BitVec.ofNat 32 i)).toNat
            have h3 : S + BitVec.ofNat 32 pos + BitVec.ofNat 32 i ≠ S + 0x3F := by
              rw [add_ofNat_assoc, e3F]; exact add_ofNat_ne S (by omega) (by omega) (by omega)
            have h4 : Sep (G + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 pos + BitVec.ofNat 32 i) 1 := by
              rw [add_ofNat_assoc]; exact SF _ (by omega)
            show (memStore8 MA _ _ _).toNat = _
            rw [memStore8_ne h3, mA _ h4, copyBytes_in hi (by omega),
              hM2 _ (E.sDF.sub (c := i) (l := 1) (by omega)).symm (E.sDS.sub (c := i) (l := 1) (by omega)).symm]
          rw [b1, b2]
        hash := by
          rw [hf1, show Sha256.blocks 0 (tailBytes msg ++ data) = [] from rfl, List.append_nil, ← H.hash]
          apply wordsAt_congr; intro i hi
          rw [show S + (0x40 : Word) = S + BitVec.ofNat 32 0x40 from rfl, add_ofNat_assoc]
          exact ld _ (by omega) (by omega)
        lo := by
          rw [List.length_append, hdata, show (msg.length + n) / 64 = msg.length / 64 by omega, ← H.lo,
            show S + (0x60 : Word) = S + BitVec.ofNat 32 0x60 from rfl]
          exact ld 0x60 (by omega) (by omega)
        hi := by
          rw [← H.hi, show S + (0x64 : Word) = S + BitVec.ofNat 32 0x64 from rfl]
          exact ld 0x64 (by omega) (by omega) }
    refine ⟨n16, c7.trans (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (c13.trans
      (.cons d14 (.cons d15 c16)))))))), ?_, ?_,
      fun r q1 q3 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q2 => ?_, by rw [mem16]; exact H',
      fun x hx hy => by rw [mem16]; exact hMt x hx hy⟩
    · rw [pc16, hra', hra, hret]
    · rw [regs16 sp, vsp]; show sp0 + 0xFFFFFFE0 + 0x20 = sp0; rw [BitVec.add_assoc]; exact BitVec.add_zero _
    · rw [regs16 r]
      by_cases h8 : r = s0
      · subst h8; rw [vs0, hs0']
      by_cases h9 : r = s1
      · subst h9; rw [vs1, hs1']
      by_cases h18 : r = s2
      · subst h18; rw [vs2, hs2']
      by_cases h19 : r = s3
      · subst h19; rw [vs3, hs3']
      by_cases h20 : r = s4
      · subst h20; rw [vs4, hs4']
      rw [updR_other _ _ _ _ _ u14'.zero r q1 h8 h9 h18 h19 h20 q2 q5, K14 r h8,
        K7_13 r q1 q10 q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2, K27 r q2 q5 h9 h20 h8 q12]
  · sorry

end C3.RV32
