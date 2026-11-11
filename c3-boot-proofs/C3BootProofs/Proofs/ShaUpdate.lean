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

set_option maxRecDepth 20000 in
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
  sorry

end C3.RV32
