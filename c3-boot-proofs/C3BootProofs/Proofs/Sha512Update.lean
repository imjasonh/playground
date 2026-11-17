import C3BootProofs.Proofs.Sha2Update
import C3BootProofs.Proofs.Sha512Blocks
import C3BootProofs.Proofs.ShaStream5

/-!
# SHA-512's `update`, as compiled in the current image

The hasher is 0xD0 bytes: a 128-byte buffer whose last byte holds how many
bytes of it are in use, the 8 hash words, and a 128-bit count of the blocks
compressed. `update` compiles to the same instructions as SHA-256's, with
128-byte blocks, so its proof follows `Sha2Update.lean`; the block helper is
`sha384UpdateBlocks_correct`.
-/

namespace C3.RV32.S5U

open C3.Image C3.RV32

set_option maxRecDepth 40000 in
/-- `compress512`'s environment survives a store outside everything it uses. -/
theorem S5Env.store32 {M : Word → BitVec 8} {P sp0 stp bp a v : Word} {n : Nat}
    (env : S5Env M P sp0 stp bp n) (hC : Sep a 4 P sha512CompressCode.length)
    (hI : Sep a 4 (P + 0xFFFFFFEA) rangeFromIndexCode.length) (hU : Sep a 4 (P + 0x5AC) memcpyStubCode.length)
    (hB : Sep a 4 (P + 0x5B4) memcpyBodyCode.length) (hZ : Sep a 4 (P + 0x544) memsetCode.length)
    (hK : Sep a 4 (BitVec.ofNat 32 sha512KAddress) 640) : S5Env (memStore32 M a v) P sp0 stp bp n :=
  { env with
    code := env.code.store32 hC
    idx := env.idx.store32 hI
    stub := env.stub.store32 hU
    body := env.body.store32 hB
    mset := env.mset.store32 hZ
    kdata := env.kdata.store32 hK }

theorem blockList128_congr {M M' : Word → BitVec 8} {bp : Word} {k : Nat}
    (h : ∀ i, i < 128 * k → M' (bp + BitVec.ofNat 32 i) = M (bp + BitVec.ofNat 32 i)) :
    blockList128 M' bp k = blockList128 M bp k := by
  unfold blockList128
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.mp hj
  apply memBytes_congr
  intro i hi
  rw [add_ofNat_assoc]
  exact h _ (by omega)

theorem blockList128_cons (M : Word → BitVec 8) (bp : Word) (k : Nat) :
    blockList128 M bp (k + 1) = memBytes M bp 128 :: blockList128 M (bp + BitVec.ofNat 32 128) k := by
  unfold blockList128
  have r1 : List.range (k + 1) = 0 :: (List.range k).map (1 + ·) := by
    rw [Nat.add_comm k 1, range_add_split 1 k]; rfl
  rw [r1, List.map_cons, List.map_map]
  simp only [Nat.mul_zero, add_ofNat_zero]
  congr 1
  exact List.map_congr_left fun j _ => by
    simp only [Function.comp_apply]
    rw [show 128 * (1 + j) = 128 + 128 * j by omega, ← add_ofNat_assoc]

/-- `Sha512.blocks` on `128 * k` bytes in memory produces `blockList128 M bp k`. -/
theorem blocks128_memBytes (M : Word → BitVec 8) :
    ∀ (k fuel : Nat) (bp : Word), k ≤ fuel → Sha512.blocks fuel (memBytes M bp (128 * k)) = blockList128 M bp k
  | 0, fuel, bp, _ => by
    cases fuel <;> rfl
  | k + 1, 0, _, h => absurd h (by omega)
  | k + 1, fuel + 1, bp, h => by
    rw [show 128 * (k + 1) = 128 + 128 * k by omega, memBytes_split, blockList128_cons]
    have hlen : (memBytes M bp 128).length = 128 := memBytes_length M bp 128
    have hne : (memBytes M bp 128 ++ memBytes M (bp + BitVec.ofNat 32 128) (128 * k)).isEmpty = false := by
      cases hc : memBytes M bp 128 with
      | nil => rw [hc] at hlen; cases hlen
      | cons _ _ => rfl
    unfold Sha512.blocks
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte, List.take_append_of_le_length (Nat.le_of_eq hlen.symm),
      List.take_of_length_le (Nat.le_of_eq hlen), List.drop_append_of_le_length (Nat.le_of_eq hlen.symm),
      List.drop_eq_nil_of_le (Nat.le_of_eq hlen), List.nil_append]
    rw [blocks128_memBytes M k fuel _ (by omega)]


section
set_option maxRecDepth 20000
theorem s5u_at_0 : fetchRel sha512UpdateCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem s5u_at_2 : fetchRel sha512UpdateCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem s5u_at_4 : fetchRel sha512UpdateCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem s5u_at_6 : fetchRel sha512UpdateCode 0x6 = some (.store .sw sp (9 : Fin 32) 0x14, 2) := by decide
theorem s5u_at_8 : fetchRel sha512UpdateCode 0x8 = some (.store .sw sp (18 : Fin 32) 0x10, 2) := by decide
theorem s5u_at_a : fetchRel sha512UpdateCode 0xA = some (.store .sw sp (19 : Fin 32) 0xC, 2) := by decide
theorem s5u_at_c : fetchRel sha512UpdateCode 0xC = some (.store .sw sp (20 : Fin 32) 0x8, 2) := by decide
theorem s5u_at_e : fetchRel sha512UpdateCode 0xE = some (.alu .add (9 : Fin 32) x0 a2, 2) := by decide
theorem s5u_at_10 : fetchRel sha512UpdateCode 0x10 = some (.alu .add (20 : Fin 32) x0 a0, 2) := by decide
theorem s5u_at_12 : fetchRel sha512UpdateCode 0x12 = some (.load .lbu (8 : Fin 32) a0 0x7F, 4) := by decide
theorem s5u_at_16 : fetchRel sha512UpdateCode 0x16 = some (.aluImm .add a2 x0 0x80, 4) := by decide
theorem s5u_at_1a : fetchRel sha512UpdateCode 0x1A = some (.alu .sub a2 a2 (8 : Fin 32), 2) := by decide
theorem s5u_at_1c : fetchRel sha512UpdateCode 0x1C = some (.branch .bgeu (9 : Fin 32) a2 0x28, 4) := by decide
theorem s5u_at_20 : fetchRel sha512UpdateCode 0x20 = some (.alu .add a0 (20 : Fin 32) (8 : Fin 32), 4) := by decide
theorem s5u_at_24 : fetchRel sha512UpdateCode 0x24 = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem s5u_at_26 : fetchRel sha512UpdateCode 0x26 = some (.auipc ra 0x4000, 4) := by decide
theorem s5u_at_2a : fetchRel sha512UpdateCode 0x2A = some (.jalr ra ra 0xFFFFFD9C, 4) := by decide
theorem s5u_at_2e : fetchRel sha512UpdateCode 0x2E = some (.alu .add (8 : Fin 32) (8 : Fin 32) (9 : Fin 32), 2) := by decide
theorem s5u_at_30 : fetchRel sha512UpdateCode 0x30 = some (.store .sb (20 : Fin 32) (8 : Fin 32) 0x7F, 4) := by decide
theorem s5u_at_34 : fetchRel sha512UpdateCode 0x34 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem s5u_at_36 : fetchRel sha512UpdateCode 0x36 = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem s5u_at_38 : fetchRel sha512UpdateCode 0x38 = some (.load .lw (9 : Fin 32) sp 0x14, 2) := by decide
theorem s5u_at_3a : fetchRel sha512UpdateCode 0x3A = some (.load .lw (18 : Fin 32) sp 0x10, 2) := by decide
theorem s5u_at_3c : fetchRel sha512UpdateCode 0x3C = some (.load .lw (19 : Fin 32) sp 0xC, 2) := by decide
theorem s5u_at_3e : fetchRel sha512UpdateCode 0x3E = some (.load .lw (20 : Fin 32) sp 0x8, 2) := by decide
theorem s5u_at_40 : fetchRel sha512UpdateCode 0x40 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem s5u_at_42 : fetchRel sha512UpdateCode 0x42 = some (.jalr x0 ra 0x0, 2) := by decide
theorem s5u_at_44 : fetchRel sha512UpdateCode 0x44 = some (.aluImm .add (18 : Fin 32) (20 : Fin 32) 0x80, 4) := by decide
theorem s5u_at_48 : fetchRel sha512UpdateCode 0x48 = some (.branch .beq (8 : Fin 32) x0 0x28, 2) := by decide
theorem s5u_at_4a : fetchRel sha512UpdateCode 0x4A = some (.alu .add (19 : Fin 32) a1 a2, 4) := by decide
theorem s5u_at_4e : fetchRel sha512UpdateCode 0x4E = some (.alu .sub (9 : Fin 32) (9 : Fin 32) a2, 2) := by decide
theorem s5u_at_50 : fetchRel sha512UpdateCode 0x50 = some (.alu .add a0 (20 : Fin 32) (8 : Fin 32), 4) := by decide
theorem s5u_at_54 : fetchRel sha512UpdateCode 0x54 = some (.auipc ra 0x4000, 4) := by decide
theorem s5u_at_58 : fetchRel sha512UpdateCode 0x58 = some (.jalr ra ra 0xFFFFFD6E, 4) := by decide
theorem s5u_at_5c : fetchRel sha512UpdateCode 0x5C = some (.aluImm .add a2 x0 0x1, 2) := by decide
theorem s5u_at_5e : fetchRel sha512UpdateCode 0x5E = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem s5u_at_60 : fetchRel sha512UpdateCode 0x60 = some (.alu .add a1 x0 (20 : Fin 32), 2) := by decide
theorem s5u_at_62 : fetchRel sha512UpdateCode 0x62 = some (.auipc ra 0xFFFF6000, 4) := by decide
theorem s5u_at_66 : fetchRel sha512UpdateCode 0x66 = some (.jalr ra ra 0x170, 4) := by decide
theorem s5u_at_6a : fetchRel sha512UpdateCode 0x6A = some (.store .sb (20 : Fin 32) x0 0x7F, 4) := by decide
theorem s5u_at_6e : fetchRel sha512UpdateCode 0x6E = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem s5u_at_70 : fetchRel sha512UpdateCode 0x70 = some (.lui a0 0x80000000, 4) := by decide
theorem s5u_at_74 : fetchRel sha512UpdateCode 0x74 = some (.aluImm .add a0 a0 0xFFFFFF80, 4) := by decide
theorem s5u_at_78 : fetchRel sha512UpdateCode 0x78 = some (.aluImm .srl a2 (9 : Fin 32) 0x7, 4) := by decide
theorem s5u_at_7c : fetchRel sha512UpdateCode 0x7C = some (.alu .and a0 a0 (9 : Fin 32), 2) := by decide
theorem s5u_at_7e : fetchRel sha512UpdateCode 0x7E = some (.aluImm .and (9 : Fin 32) (9 : Fin 32) 0x7F, 4) := by decide
theorem s5u_at_82 : fetchRel sha512UpdateCode 0x82 = some (.alu .add (19 : Fin 32) a1 a0, 4) := by decide
theorem s5u_at_86 : fetchRel sha512UpdateCode 0x86 = some (.branch .beq a2 x0 0xC, 2) := by decide
theorem s5u_at_88 : fetchRel sha512UpdateCode 0x88 = some (.alu .add a0 x0 (18 : Fin 32), 2) := by decide
theorem s5u_at_8a : fetchRel sha512UpdateCode 0x8A = some (.auipc ra 0xFFFF6000, 4) := by decide
theorem s5u_at_8e : fetchRel sha512UpdateCode 0x8E = some (.jalr ra ra 0x148, 4) := by decide
theorem s5u_at_92 : fetchRel sha512UpdateCode 0x92 = some (.alu .add a0 x0 (20 : Fin 32), 2) := by decide
theorem s5u_at_94 : fetchRel sha512UpdateCode 0x94 = some (.alu .add a1 x0 (19 : Fin 32), 2) := by decide
theorem s5u_at_96 : fetchRel sha512UpdateCode 0x96 = some (.alu .add a2 x0 (9 : Fin 32), 2) := by decide
theorem s5u_at_98 : fetchRel sha512UpdateCode 0x98 = some (.store .sb (20 : Fin 32) (9 : Fin 32) 0x7F, 4) := by decide
theorem s5u_at_9c : fetchRel sha512UpdateCode 0x9C = some (.load .lw ra sp 0x1C, 2) := by decide
theorem s5u_at_9e : fetchRel sha512UpdateCode 0x9E = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem s5u_at_a0 : fetchRel sha512UpdateCode 0xA0 = some (.load .lw (9 : Fin 32) sp 0x14, 2) := by decide
theorem s5u_at_a2 : fetchRel sha512UpdateCode 0xA2 = some (.load .lw (18 : Fin 32) sp 0x10, 2) := by decide
theorem s5u_at_a4 : fetchRel sha512UpdateCode 0xA4 = some (.load .lw (19 : Fin 32) sp 0xC, 2) := by decide
theorem s5u_at_a6 : fetchRel sha512UpdateCode 0xA6 = some (.load .lw (20 : Fin 32) sp 0x8, 2) := by decide
theorem s5u_at_a8 : fetchRel sha512UpdateCode 0xA8 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem s5u_at_aa : fetchRel sha512UpdateCode 0xAA = some (.auipc (6 : Fin 32) 0x4000, 4) := by decide
theorem s5u_at_ae : fetchRel sha512UpdateCode 0xAE = some (.jalr x0 (6 : Fin 32) 0xFFFFFD18, 4) := by decide
end

/-- The 0xD0 bytes at `S` hold the compiled hasher after it has absorbed
`msg`: the bytes after `msg`'s full blocks in the buffer, their count in its
last byte, the hash of the full blocks, and the 64-bit count of blocks. -/
structure Hasher5At (M : Word → BitVec 8) (S : Word) (msg : Bytes) : Prop where
  hlen : msg.length < 2 ^ 32
  pos : M (S + 0x7F) = BitVec.ofNat 8 (msg.length % 128)
  buf : memBytes M S (msg.length % 128) = tailBytes5 msg
  hash : (s5Hv M (S + 0x80)).toList = (fullBlocks5 msg).foldl Sha512.compress Sha512.h0
  lo : memLoad32 M (S + 0xC0) = BitVec.ofNat 32 (msg.length / 128)
  hi : memLoad32 M (S + 0xC4) = 0
  hi2 : memLoad32 M (S + 0xC8) = 0
  hi3 : memLoad32 M (S + 0xCC) = 0

/-- Where `update` runs: the code of `update`, its block helper,
`compress512` with `RangeFrom::index` and `memset`, and `memcpy` at their addresses in the
image; the hasher at `S`, the `n` input bytes at `D`, and the 0x3B0 bytes of
stack below `sp0` apart from each other and from the round constants; and all
three at data-bus addresses, below every code address. -/
structure UpdEnv (M : Word → BitVec 8) (S D sp0 : Word) (n : Nat) : Prop where
  cU : CodeIn M (BitVec.ofNat 32 sha512UpdateAddress) sha512UpdateCode
  cBlk : CodeIn M (BitVec.ofNat 32 sha384UpdateBlocksAddress) sha384UpdateBlocksCode
  cC : CodeIn M (BitVec.ofNat 32 sha512CompressAddress) sha512CompressCode
  cI : CodeIn M (BitVec.ofNat 32 sha512CompressAddress + 0xFFFFFFEA) rangeFromIndexCode
  cZ : CodeIn M (BitVec.ofNat 32 sha512CompressAddress + 0x544) memsetCode
  cK : CodeIn M (BitVec.ofNat 32 sha512KAddress) sha512KData
  cMS : CodeIn M (BitVec.ofNat 32 memcpyStubAddress) memcpyStubCode
  cMB : CodeIn M (BitVec.ofNat 32 memcpyStubAddress + 8) memcpyBodyCode
  hS : S.toNat % 4 = 0
  hSw : S.toNat + 0xD0 ≤ 0x40000000
  hsp : sp0.toNat % 16 = 0
  hspl : 0x3B0 ≤ sp0.toNat
  hspw : sp0.toNat ≤ 0x40000000
  hDw : D.toNat + n ≤ 0x40000000
  sDS : Sep D n S 0xD0
  sDF : Sep D n (sp0 + 0xFFFFFC50) 0x3B0
  sSF : Sep S 0xD0 (sp0 + 0xFFFFFC50) 0x3B0
  sKS : Sep (BitVec.ofNat 32 sha512KAddress) 640 S 0xD0
  sKF : Sep (BitVec.ofNat 32 sha512KAddress) 640 (sp0 + 0xFFFFFC50) 0x3B0

theorem k5_stub_at : (BitVec.ofNat 32 sha512CompressAddress + 0x5AC : Word) = BitVec.ofNat 32 memcpyStubAddress := by
  decide

theorem k5_body_at : (BitVec.ofNat 32 sha512CompressAddress + 0x5B4 : Word) = BitVec.ofNat 32 memcpyStubAddress + 8 := by
  decide

section
set_option maxRecDepth 20000
theorem updPro_end : blockEnd sha512UpdateCode 0 updPro = some 0xE := by decide
theorem updEpiR_end : blockEnd sha512UpdateCode 0x34 updEpi = some 0x42 := by decide
theorem updEpiT_end : blockEnd sha512UpdateCode 0x9C updEpi = some 0xAA := by decide
end

set_option maxRecDepth 20000 in
/-- `update`'s prologue, to offset 0x0E: it allocates a 0x20-byte frame at
`G` and saves `ra` and `s0` through `s4` in it. Any later memory that keeps
the frame's top 24 bytes gives back the saved registers. -/
theorem upd_pro {M : Word → BitVec 8} {m : Machine} {G : Word}
    (st0 : St M (BitVec.ofNat 32 sha512UpdateAddress) m 0 (reg m))
    (cU : CodeIn M (BitVec.ofNat 32 sha512UpdateAddress) sha512UpdateCode)
    (hG : reg m sp + 0xFFFFFFE0 = G) (hGa : G.toNat % 4 = 0) (hGw : G.toNat + 32 ≤ 0x40000000) :
    ∃ m2 M2, Steps m m2 ∧ St M2 (BitVec.ofNat 32 sha512UpdateAddress) m2 0x0E (reg m2) ∧ reg m2 sp = G ∧
      (∀ r, r ≠ sp → reg m2 r = reg m r) ∧ (∀ x, Sep G 32 x 1 → M2 x = M x) ∧
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
  have sU : ∀ c, c + 4 ≤ 32 → Sep (G + BitVec.ofNat 32 c) 4 (BitVec.ofNat 32 sha512UpdateAddress)
      sha512UpdateCode.length := fun c h => sepC c 4 h _ _ (by decide) (by decide)
  obtain ⟨m2, c2, u2⟩ := St.block updPro st0 cU updPro_end (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, updPro, upd_app, ↓reduceIte, and_true]
    simp only [ev_add]; rw [hG]
    exact ⟨True.intro, ⟨aligned_add hGa (k := 0x1C) (by decide), sU 0x1C (by omega)⟩,
      ⟨aligned_add hGa (k := 0x18) (by decide), sU 0x18 (by omega)⟩,
      ⟨aligned_add hGa (k := 0x14) (by decide), sU 0x14 (by omega)⟩,
      ⟨aligned_add hGa (k := 0x10) (by decide), sU 0x10 (by omega)⟩,
      ⟨aligned_add hGa (k := 0xC) (by decide), sU 0xC (by omega)⟩,
      aligned_add hGa (k := 8) (by decide), sU 8 (by omega)⟩)
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore32 (memStore32 (memStore32 (memStore32 (memStore32 (memStore32 M
      (G + 0x1C) (reg m ra)) (G + 0x18) (reg m s0)) (G + 0x14) (reg m s1)) (G + 0x10) (reg m s2))
      (G + 0x0C) (reg m s3)) (G + 8) (reg m s4) = M2 := ⟨_, rfl⟩
  have eM : (runBlock updPro (M, reg m)).1 = M2 := by
    simp +decide only [runBlock, BInstr.run, updPro, upd_app, ↓reduceIte]; simp only [ev_add]; rw [hG, ← hM2]
  have eR : ∀ r, (runBlock updPro (M, reg m)).2 r = upd (reg m) sp G r := fun r => by
    simp only [runBlock, BInstr.run, updPro]; simp only [ev_add]; rw [hG]
  have M2out : ∀ x, Sep G 32 x 1 → M2 x = M x := fun x hx => by
    rw [← hM2, memStore32_get_sep (show Sep (G + 8) 4 x 1 from frx 8 4 (by omega) x hx),
      memStore32_get_sep (show Sep (G + 0x0C) 4 x 1 from frx 0x0C 4 (by omega) x hx),
      memStore32_get_sep (show Sep (G + 0x10) 4 x 1 from frx 0x10 4 (by omega) x hx),
      memStore32_get_sep (show Sep (G + 0x14) 4 x 1 from frx 0x14 4 (by omega) x hx),
      memStore32_get_sep (show Sep (G + 0x18) 4 x 1 from frx 0x18 4 (by omega) x hx),
      memStore32_get_sep (show Sep (G + 0x1C) 4 x 1 from frx 0x1C 4 (by omega) x hx)]
  have M2slots : memLoad32 M2 (G + 0x1C) = reg m ra ∧ memLoad32 M2 (G + 0x18) = reg m s0 ∧
      memLoad32 M2 (G + 0x14) = reg m s1 ∧ memLoad32 M2 (G + 0x10) = reg m s2 ∧
      memLoad32 M2 (G + 0x0C) = reg m s3 ∧ memLoad32 M2 (G + 8) = reg m s4 := by
    have so : ∀ c d, c < 32 → d < 32 → c + 4 ≤ d ∨ d + 4 ≤ c →
        Sep (G + BitVec.ofNat 32 c) 4 (G + BitVec.ofNat 32 d) 4 :=
      fun c d hc hd h => sep_offsets G h (by omega) (by omega)
    rw [← hM2]
    refine ⟨?_, ?_, ?_, ?_, ?_, memLoad32_store32_same _ _ _⟩
    · rw [memLoad32_store32_sep (show Sep (G + 8) 4 (G + 0x1C) 4 from so 8 0x1C (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x0C) 4 (G + 0x1C) 4 from so 0x0C 0x1C (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x10) 4 (G + 0x1C) 4 from so 0x10 0x1C (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x14) 4 (G + 0x1C) 4 from so 0x14 0x1C (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x18) 4 (G + 0x1C) 4 from so 0x18 0x1C (by omega) (by omega) (by omega)),
        memLoad32_store32_same]
    · rw [memLoad32_store32_sep (show Sep (G + 8) 4 (G + 0x18) 4 from so 8 0x18 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x0C) 4 (G + 0x18) 4 from so 0x0C 0x18 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x10) 4 (G + 0x18) 4 from so 0x10 0x18 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x14) 4 (G + 0x18) 4 from so 0x14 0x18 (by omega) (by omega) (by omega)),
        memLoad32_store32_same]
    · rw [memLoad32_store32_sep (show Sep (G + 8) 4 (G + 0x14) 4 from so 8 0x14 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x0C) 4 (G + 0x14) 4 from so 0x0C 0x14 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x10) 4 (G + 0x14) 4 from so 0x10 0x14 (by omega) (by omega) (by omega)),
        memLoad32_store32_same]
    · rw [memLoad32_store32_sep (show Sep (G + 8) 4 (G + 0x10) 4 from so 8 0x10 (by omega) (by omega) (by omega)),
        memLoad32_store32_sep (show Sep (G + 0x0C) 4 (G + 0x10) 4 from so 0x0C 0x10 (by omega) (by omega) (by omega)),
        memLoad32_store32_same]
    · rw [memLoad32_store32_sep (show Sep (G + 8) 4 (G + 0x0C) 4 from so 8 0x0C (by omega) (by omega) (by omega)),
        memLoad32_store32_same]
  refine ⟨m2, M2, c2, ⟨u2.pc, by rw [u2.mem, eM], fun _ => rfl⟩, ?_, fun r h1 => ?_, M2out, fun Mx h => ?_⟩
  · rw [u2.regs, eR]; simp +decide only [upd_app, ↓reduceIte]
  · rw [u2.regs, eR, updz hz h1]
  · have e : ∀ c, 8 ≤ c → c + 4 ≤ 32 → memLoad32 Mx (G + BitVec.ofNat 32 c) = memLoad32 M2 (G + BitVec.ofNat 32 c) :=
      fun c h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact h _ (by omega) (by omega)
    obtain ⟨q1, q2, q3, q4, q5, q6⟩ := M2slots
    exact ⟨(e 0x1C (by omega) (by omega)).trans q1, (e 0x18 (by omega) (by omega)).trans q2,
      (e 0x14 (by omega) (by omega)).trans q3, (e 0x10 (by omega) (by omega)).trans q4,
      (e 0x0C (by omega) (by omega)).trans q5, (e 8 (by omega) (by omega)).trans q6⟩

set_option maxRecDepth 20000 in
/-- `update`'s epilogue from `off`, where its code reloads `ra` and `s0`
through `s4` from the frame at `G` and frees the frame. -/
theorem upd_epi {M : Word → BitVec 8} {m : Machine} {f : Fin 32 → Word} {G : Word} {off off' : Nat}
    (s : St M (BitVec.ofNat 32 sha512UpdateAddress) m off f)
    (hc : CodeIn M (BitVec.ofNat 32 sha512UpdateAddress) sha512UpdateCode)
    (he : blockEnd sha512UpdateCode off updEpi = some off')
    (hsp : f sp = G) (hG : G.toNat % 4 = 0) :
    ∃ m', Steps m m' ∧ St M (BitVec.ofNat 32 sha512UpdateAddress) m' off' (upd (updRestored M G f) sp (G + 0x20)) := by
  obtain ⟨m1, c1, u1⟩ := St.block updEpi s hc he (by
    simp +decide only [BlockOk, BInstr.ok, BInstr.run, updEpi, upd_app, ↓reduceIte, and_true]
    rw [hsp]
    exact ⟨aligned_add hG (k := 0x1C) (by decide), aligned_add hG (k := 0x18) (by decide),
      aligned_add hG (k := 0x14) (by decide), aligned_add hG (k := 0x10) (by decide),
      aligned_add hG (k := 0xC) (by decide), aligned_add hG (k := 8) (by decide)⟩)
  refine ⟨m1, c1, ⟨u1.pc, by rw [u1.mem]; rfl, fun r => ?_⟩⟩
  rw [u1.regs]
  simp only [runBlock, BInstr.run, updEpi, updRestored, restoreRegs]
  simp +decide only [upd_app, ↓reduceIte]
  rw [hsp]; rfl

set_option maxRecDepth 20000 in
/-- `update`'s return when the bytes fit in the buffer, from offset 0x34:
the epilogue and `ret`. -/
theorem upd_ret {M : Word → BitVec 8} {m : Machine} {f : Fin 32 → Word} {G : Word}
    (s : St M (BitVec.ofNat 32 sha512UpdateAddress) m 0x34 f)
    (hc : CodeIn M (BitVec.ofNat 32 sha512UpdateAddress) sha512UpdateCode)
    (hsp : f sp = G) (hG : G.toNat % 4 = 0) :
    ∃ m', Steps m m' ∧ m'.pc = memLoad32 M (G + 0x1C) &&& ~~~1 ∧ m'.mem = M ∧
      ∀ r, reg m' r = upd (updRestored M G f) sp (G + 0x20) r := by
  obtain ⟨m1, c1, u1⟩ := upd_epi s hc updEpiR_end hsp hG
  obtain ⟨m3, e3, pc3, mem3, regs3⟩ := u1.jalr hc s5u_at_42
  refine ⟨m3, c1.trans (.single e3), ?_, mem3, regs3⟩
  rw [pc3]; simp +decide only [updRestored, restoreRegs, upd_app, ↓reduceIte, add_lit_zero]

set_option maxRecDepth 20000 in
/-- `update`'s end otherwise, from offset 0x9C: the epilogue and a tail call
of `memcpy` for the bytes left over. -/
theorem upd_tail {M : Word → BitVec 8} {m : Machine} {f : Fin 32 → Word} {G : Word}
    (s : St M (BitVec.ofNat 32 sha512UpdateAddress) m 0x9C f)
    (hc : CodeIn M (BitVec.ofNat 32 sha512UpdateAddress) sha512UpdateCode)
    (hsp : f sp = G) (hG : G.toNat % 4 = 0) :
    ∃ m', Steps m m' ∧ m'.pc = BitVec.ofNat 32 memcpyStubAddress ∧ m'.mem = M ∧
      ∀ r, r ≠ t1 → reg m' r = upd (updRestored M G f) sp (G + 0x20) r := by
  obtain ⟨m1, c1, u1⟩ := upd_epi s hc updEpiT_end hsp hG
  obtain ⟨m3, e3, t3⟩ := u1.auipc hc s5u_at_aa (off' := 0xAE) (by decide)
  obtain ⟨m4, e4, pc4, mem4, regs4⟩ := t3.jalr hc s5u_at_ae
  refine ⟨m4, c1.trans (.cons e3 (.single e4)), ?_, mem4, fun r h6 => ?_⟩
  · rw [pc4, show ∀ (F : Fin 32 → Word) (v : Word), upd F (6 : Fin 32) v 6 = v from fun F v => by simp [upd]]
    decide
  · rw [regs4]
    have h6' : r ≠ (6 : Fin 32) := h6
    by_cases h0 : r.val = 0
    · have : r = 0 := Fin.ext h0
      subst this; simp [upd]
    · simp only [upd, h0, h6', ite_false]

set_option maxRecDepth 100000 in
theorem and63_small : ∀ r, r < 128 → r &&& 127 = r := by decide

theorem and63 (x : Nat) : x &&& 127 = x % 128 := by
  have h1 : x &&& 127 ≤ 127 := Nat.and_le_right
  have e := Nat.and_mod_two_pow (a := x) (b := 127) (n := 7)
  rw [show (2 : Nat) ^ 7 = 128 from rfl, Nat.mod_eq_of_lt (show x &&& 127 < 128 by omega), show 127 % 128 = 127 from rfl,
    and63_small _ (Nat.mod_lt _ (by decide))] at e
  exact e

theorem and63_val {x : Nat} (hx : x < 2 ^ 32) : aluEval .and (BitVec.ofNat 32 x) 0x7F = BitVec.ofNat 32 (x % 128) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 x &&& 0x7F).toNat = _
  rw [BitVec.toNat_and, show (0x7F : Word).toNat = 127 from rfl, and63, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx]
  omega

theorem srl6_val {x : Nat} (hx : x < 2 ^ 32) : aluEval .srl (BitVec.ofNat 32 x) 7 = BitVec.ofNat 32 (x / 128) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 x >>> ((7 : Word).toNat % 32)).toNat = _
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    show (7 : Word).toNat % 32 = 7 from rfl, Nat.shiftRight_eq_div_pow]
  omega

theorem m64_bits : ∀ i : Fin 31, ((0x7FFFFF80 : Word).getLsbD i.val && (0x7F : Word).getLsbD i.val) = false ∧
    ((0x7FFFFF80 : Word).getLsbD i.val || (0x7F : Word).getLsbD i.val) = true := by decide

/-- The mask `update` uses for the bytes in whole blocks. -/
theorem mask64_val {x : Nat} (hx : x < 2 ^ 31) :
    aluEval .and 0x7FFFFF80 (BitVec.ofNat 32 x) = BitVec.ofNat 32 (128 * (x / 128)) := by
  let w := BitVec.ofNat 32 x
  have hw31 : w.getLsbD 31 = false := by
    show (BitVec.ofNat 32 x).getLsbD 31 = false
    rw [BitVec.getLsbD_ofNat, Nat.testBit_lt_two_pow hx, Bool.and_false]
  have hd : (0x7FFFFF80 &&& w) + (0x7F &&& w) = w := by
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
  have e : (0x7FFFFF80 : Word) &&& w = w - (0x7F &&& w) := by
    calc (0x7FFFFF80 : Word) &&& w = (0x7FFFFF80 &&& w) + (0x7F &&& w) - (0x7F &&& w) :=
          (BitVec.add_sub_cancel ..).symm
      _ = w - (0x7F &&& w) := by rw [hd]
  show (0x7FFFFF80 : Word) &&& w = _
  rw [e]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_and, show (0x7F : Word).toNat = 127 from rfl, Nat.and_comm, and63]
  show (2 ^ 32 - (BitVec.ofNat 32 x).toNat % 128 + (BitVec.ofNat 32 x).toNat) % 2 ^ 32 = (BitVec.ofNat 32 (128 * (x / 128))).toNat
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x < 2 ^ 32 by omega)]
  omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
/-- `update` from offset 0x70, once the buffer is empty: it compresses the
whole blocks of the `nk` input bytes left at `Dk` in place, buffers the
rest with a tail call of `memcpy`, and returns. `pre` is the blocks
compressed so far, and `msg'` the message with the new bytes appended. -/
theorem upd_join {M0 Mx : Word → BitVec 8} {S D sp0 Dk : Word} {n nk : Nat} {msg' : Bytes}
    {pre : List Bytes} (nn : Machine) {f : Fin 32 → Word} {rRa rS0 rS1 rS2 rS3 rS4 : Word}
    (E : UpdEnv M0 S D sp0 n) (s : St Mx (BitVec.ofNat 32 sha512UpdateAddress) nn 0x70 f)
    (hagree : ∀ x, Sep (sp0 + 0xFFFFFC50) 0x3B0 x 1 → Sep S 0xD0 x 1 → Mx x = M0 x)
    (hnk : nk ≤ n) (hDk : Dk = D + BitVec.ofNat 32 (n - nk)) (hn : n < 2 ^ 31)
    (fa1 : f a1 = Dk) (fs1 : f s1 = BitVec.ofNat 32 nk) (fs2 : f s2 = S + 0x80) (fs4 : f s4 = S)
    (fsp : f sp = sp0 + 0xFFFFFFE0)
    (hslots : ∀ My : Word → BitVec 8, (∀ k, 8 ≤ k → k < 32 →
        My (sp0 + 0xFFFFFFE0 + BitVec.ofNat 32 k) = Mx (sp0 + 0xFFFFFFE0 + BitVec.ofNat 32 k)) →
      memLoad32 My (sp0 + 0xFFFFFFE0 + 0x1C) = rRa ∧ memLoad32 My (sp0 + 0xFFFFFFE0 + 0x18) = rS0 ∧
      memLoad32 My (sp0 + 0xFFFFFFE0 + 0x14) = rS1 ∧ memLoad32 My (sp0 + 0xFFFFFFE0 + 0x10) = rS2 ∧
      memLoad32 My (sp0 + 0xFFFFFFE0 + 0x0C) = rS3 ∧ memLoad32 My (sp0 + 0xFFFFFFE0 + 8) = rS4)
    (hret : rRa &&& ~~~1 = rRa)
    (hhash : (s5Hv Mx (S + 0x80)).toList = pre.foldl Sha512.compress Sha512.h0)
    (hlo : memLoad32 Mx (S + 0xC0) = BitVec.ofNat 32 pre.length) (hhi : memLoad32 Mx (S + 0xC4) = 0)
    (hhi2 : memLoad32 Mx (S + 0xC8) = 0) (hhi3 : memLoad32 Mx (S + 0xCC) = 0)
    (hfull : fullBlocks5 msg' = pre ++ Sha512.blocks (nk / 128) (memBytes M0 Dk nk))
    (htail : tailBytes5 msg' = (memBytes M0 Dk nk).drop (128 * (nk / 128)))
    (hlen : msg'.length < 2 ^ 32) :
    ∃ m', Steps nn m' ∧ m'.pc = rRa ∧ reg m' sp = sp0 ∧ reg m' s0 = rS0 ∧ reg m' s1 = rS1 ∧
      reg m' s2 = rS2 ∧ reg m' s3 = rS3 ∧ reg m' s4 = rS4 ∧
      (∀ r, r ≠ ra → r ≠ sp → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ s0 → r ≠ s1 →
        r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ s2 → r ≠ s3 →
        r ≠ s4 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) →
        reg m' r = f r) ∧
      Hasher5At m'.mem S msg' ∧
      ∀ x, Sep (sp0 + 0xFFFFFC50) 0x3B0 x 1 → Sep S 0xD0 x 1 → m'.mem x = M0 x := by
  let U := BitVec.ofNat 32 sha512UpdateAddress
  let G := sp0 + 0xFFFFFFE0
  let R := sp0 + 0xFFFFFC50
  let k := nk / 128
  have hSw := E.hSw
  have hspw := E.hspw
  have hspl := E.hspl
  have hDw := E.hDw
  have hRn : R.toNat = sp0.toNat - 0x3B0 := by
    show (sp0 + 0xFFFFFC50).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFC50 : Word).toNat = 2 ^ 32 - 0x3B0 from rfl]; omega
  have hGn : G.toNat = sp0.toNat - 0x20 := by
    show (sp0 + 0xFFFFFFE0).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFFE0 : Word).toNat = 2 ^ 32 - 0x20 from rfl]; omega
  have hGa : G.toNat % 4 = 0 := by rw [hGn]; have := E.hsp; omega
  have hGR : G = R + BitVec.ofNat 32 0x390 := by
    show sp0 + 0xFFFFFFE0 = sp0 + 0xFFFFFC50 + BitVec.ofNat 32 0x390
    rw [BitVec.add_assoc]; rfl
  have hDkn : Dk.toNat = D.toNat + (n - nk) := by
    rw [hDk, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n - nk) (by omega)]; omega
  -- Code, anywhere at or above 0x40000000, is apart from the stack and the hasher.
  have codeX : ∀ (My : Word → BitVec 8), (∀ x, Sep R 0x3B0 x 1 → Sep S 0xD0 x 1 → My x = M0 x) →
      ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn My b code := fun My h b code hc hb hbl i hi => by
    rw [h _ ((data_code (by rw [hRn]; omega) hb hbl).subR (c := i) (l := 1) (by omega))
      ((data_code (by omega) hb hbl).subR (c := i) (l := 1) (by omega))]
    exact hc i hi
  have cU := codeX Mx hagree _ _ E.cU (by decide) (by decide)
  obtain ⟨n1, d1, u1⟩ := s.lui cU s5u_at_70 (off' := 0x74) (by decide)
  have K1 := u1.upd_ne s.zero
  have u1' : St Mx U n1 0x74 (reg n1) := u1.self
  obtain ⟨n2, d2, u2⟩ := u1'.aluImm cU s5u_at_74 (off' := 0x78) (by decide)
  have g2 : reg n2 a0 = 0x7FFFFF80 := by rw [u2.upd_eq (by decide), u1.upd_eq (by decide)]; rfl
  have K2 := u2.upd_ne u1'.zero
  have u2' : St Mx U n2 0x78 (reg n2) := u2.self
  have s1_2 : reg n2 s1 = BitVec.ofNat 32 nk := by rw [K2 s1 (by decide), K1 s1 (by decide), fs1]
  obtain ⟨n3, d3, u3⟩ := u2'.aluImm cU s5u_at_78 (off' := 0x7C) (by decide)
  have g3 : reg n3 a2 = BitVec.ofNat 32 k := by rw [u3.upd_eq (by decide), s1_2, srl6_val (by omega)]
  have K3 := u3.upd_ne u2'.zero
  have u3' : St Mx U n3 0x7C (reg n3) := u3.self
  obtain ⟨n4, d4, u4⟩ := u3'.alu cU s5u_at_7c (off' := 0x7E) (by decide)
  have g4 : reg n4 a0 = BitVec.ofNat 32 (128 * k) := by
    rw [u4.upd_eq (by decide), K3 a0 (by decide), g2, K3 s1 (by decide), s1_2, mask64_val (by omega)]
  have K4 := u4.upd_ne u3'.zero
  have u4' : St Mx U n4 0x7E (reg n4) := u4.self
  obtain ⟨n5, d5, u5⟩ := u4'.aluImm cU s5u_at_7e (off' := 0x82) (by decide)
  have g5 : reg n5 s1 = BitVec.ofNat 32 (nk % 128) := by
    rw [u5.upd_eq (by decide), K4 s1 (by decide), K3 s1 (by decide), s1_2, and63_val (by omega)]
  have K5 := u5.upd_ne u4'.zero
  have u5' : St Mx U n5 0x82 (reg n5) := u5.self
  obtain ⟨n6, d6, u6⟩ := u5'.alu cU s5u_at_82 (off' := 0x86) (by decide)
  have g6 : reg n6 s3 = Dk + BitVec.ofNat 32 (128 * k) := by
    rw [u6.upd_eq (by decide), K5 a1 (by decide), K4 a1 (by decide), K3 a1 (by decide), K2 a1 (by decide),
      K1 a1 (by decide), fa1, K5 a0 (by decide), g4]; rfl
  have K6 := u6.upd_ne u5'.zero
  have u6' : St Mx U n6 0x86 (reg n6) := u6.self
  have K16 : ∀ r, r ≠ a0 → r ≠ a2 → r ≠ s1 → r ≠ s3 → reg n6 r = f r := fun r q0 q2 q9 q19 => by
    rw [K6 r q19, K5 r q9, K4 r q0, K3 r q2, K2 r q0, K1 r q0]
  have c6 : Steps nn n6 := .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6)))))
  have hkk : 128 * k ≤ nk := by show 128 * (nk / 128) ≤ nk; omega
  have hblk : Sha512.blocks k (memBytes M0 Dk nk) = blockList128 Mx Dk k := by
    rw [blocks5_take, memBytes_take _ _ hkk, blocks128_memBytes M0 k k Dk (Nat.le_refl k)]
    apply blockList128_congr; intro i hi
    have hD := E.sDF.sub (c := n - nk + i) (l := 1) (by omega)
    have hS' := E.sDS.sub (c := n - nk + i) (l := 1) (by omega)
    rw [hDk, add_ofNat_assoc]
    exact (hagree _ hD.symm hS'.symm).symm
  have hfl : pre.length + k = msg'.length / 128 := by
    rw [← fullBlocks5_length, hfull, List.length_append, blocks5_length _ _ (by rw [memBytes_length]; exact hkk)]
  have RG : G + 0xFFFFFC70 = R := by
    show sp0 + 0xFFFFFFE0 + 0xFFFFFC70 = sp0 + 0xFFFFFC50; rw [BitVec.add_assoc]; rfl
  have eC0 : S + 0x80 + 0x40 = S + BitVec.ofNat 32 0xC0 := by rw [BitVec.add_assoc]; rfl
  have e80 : S + 0x80 = S + BitVec.ofNat 32 0x80 := rfl
  have hS80 : (S + 0x80).toNat = S.toNat + 0x80 := by
    rw [e80, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hSC0 : (S + 0x80 + 0x40).toNat = S.toNat + 0xC0 := by
    rw [eC0, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  -- The whole blocks of the input, compressed in place.
  have H8 : ∃ n8 Mc, Steps nn n8 ∧ St Mc U n8 0x92 (reg n8) ∧
      (s5Hv Mc (S + 0x80)).toList = (pre ++ Sha512.blocks k (memBytes M0 Dk nk)).foldl Sha512.compress Sha512.h0 ∧
      memLoad32 Mc (S + 0xC0) = BitVec.ofNat 32 (pre.length + k) ∧ memLoad32 Mc (S + 0xC4) = 0 ∧
      memLoad32 Mc (S + 0xC8) = 0 ∧ memLoad32 Mc (S + 0xCC) = 0 ∧
      (∀ x, Sep R 0x390 x 1 → Sep (S + 0x80) 0x50 x 1 → Mc x = Mx x) ∧
      reg n8 s1 = BitVec.ofNat 32 (nk % 128) ∧ reg n8 s3 = Dk + BitVec.ofNat 32 (128 * k) ∧
      (∀ r, r ≠ ra → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 →
        r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ s1 → r ≠ s3 → r ≠ (28 : Fin 32) →
        r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) → reg n8 r = f r) := by
    by_cases hk0 : k = 0
    · obtain ⟨n7, d7, u7⟩ := u6'.taken cU 0x92 s5u_at_86 (by decide) (by
        simp only [branchTaken]; rw [K6 a2 (by decide), K5 a2 (by decide), K4 a2 (by decide), g3, u6'.zero, hk0]
        rfl)
      refine ⟨n7, Mx, c6.trans (.single d7), u7.self, ?_, ?_, hhi, hhi2, hhi3, fun _ _ _ => rfl, ?_, ?_,
        fun r q1 q5 q6 q7 q10 q11 q12 _ _ _ _ _ q9 q19 _ _ _ _ => ?_⟩
      · rw [hhash, hk0]; simp [Sha512.blocks]
      · rw [hlo, hk0]; rfl
      · rw [u7.regs, K6 s1 (by decide), g5]
      · rw [u7.regs, g6]
      · rw [u7.regs, K16 r q10 q12 q9 q19]
    · obtain ⟨n7, d7, u7⟩ := u6'.notTaken cU 0x88 s5u_at_86 (by decide) (by
        simp only [branchTaken]; rw [K6 a2 (by decide), K5 a2 (by decide), K4 a2 (by decide), g3, u6'.zero]
        rw [beq_eq_false_iff_ne]
        intro h; exact hk0 (ofNat_inj (by omega) (by decide) h))
      obtain ⟨n8, d8, u8⟩ := u7.alu cU s5u_at_88 (off' := 0x8A) (by decide)
      have g8 : reg n8 a0 = S + 0x80 := by
        rw [u8.upd_eq (by decide), u6'.zero, K16 s2 (by decide) (by decide) (by decide) (by decide), fs2]
        exact BitVec.zero_add _
      have K8 := u8.upd_ne u6'.zero
      have u8' : St Mx U n8 0x8A (reg n8) := u8.self
      obtain ⟨n9, d9, u9⟩ := u8'.auipc cU s5u_at_8a (off' := 0x8E) (by decide)
      obtain ⟨n10, d10, pc10, mem10, regs10⟩ := u9.call cU s5u_at_8e
      have r10 : ∀ r, r ≠ ra → reg n10 r = reg n8 r := fun r h => by
        rw [regs10]
        by_cases h0 : r.val = 0
        · have : r = 0 := Fin.ext h0
          subst this; simp [upd]; exact u8'.zero.symm
        · simp [upd, h0, h]
      have ra10 : reg n10 ra = U + BitVec.ofNat 32 0x92 := by rw [regs10]; simp +decide [upd]; rfl
      have pc10' : n10.pc = BitVec.ofNat 32 sha384UpdateBlocksAddress := by
        rw [pc10, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]
        decide
      have cX10 : ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
          b.toNat + code.length ≤ 2 ^ 32 → CodeIn n10.mem b code := fun b code hc hb hbl => by
        rw [mem10]; exact codeX Mx hagree b code hc hb hbl
      have sR : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 → Sep R 0x390 b l :=
        fun b l hb hbl => data_code (by rw [hRn]; omega) hb hbl
      have s80 : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 → Sep (S + 0x80) 64 b l :=
        fun b l hb hbl => data_code (by rw [hS80]; omega) hb hbl
      have sC0 : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
          Sep (S + 0x80 + 0x40) 16 b l := fun b l hb hbl => data_code (by rw [hSC0]; omega) hb hbl
      have kR : Sep R 0x390 (BitVec.ofNat 32 sha512KAddress) 640 := by
        have := E.sKF.symm.sub (c := 0) (l := 0x390) (by omega); rwa [add_ofNat_zero] at this
      have kS : ∀ c l, c + l ≤ 0xD0 → Sep (S + BitVec.ofNat 32 c) l (BitVec.ofNat 32 sha512KAddress) 640 :=
        fun c l h => E.sKS.symm.sub (c := c) (l := l) h
      have dR : Sep Dk (128 * k) R 0x390 := by
        rw [hDk]; exact (E.sDF.sub (c := n - nk) (l := 128 * k) (by omega)).subR (c := 0) (l := 0x390) (by omega)
          |> fun h => by rwa [add_ofNat_zero] at h
      have dS : ∀ c l, c + l ≤ 0xD0 → Sep Dk (128 * k) (S + BitVec.ofNat 32 c) l := fun c l h => by
        rw [hDk]; exact (E.sDS.sub (c := n - nk) (l := 128 * k) (by omega)).subR (c := c) (l := l) h
      have SR : ∀ c l, c + l ≤ 0xD0 → Sep (S + BitVec.ofNat 32 c) l R 0x390 := fun c l h =>
        (E.sSF.sub (c := c) (l := l) h).subR (c := 0) (l := 0x390) (by omega) |> fun h' => by
          rwa [add_ofNat_zero] at h'
      have env : S5Env n10.mem (BitVec.ofNat 32 sha512CompressAddress) G (S + 0x80) Dk k :=
        { hP := by decide
          code := cX10 _ _ E.cC (by decide) (by decide)
          idx := cX10 _ _ E.cI (by decide) (by decide)
          stub := by rw [k5_stub_at]; exact cX10 _ _ E.cMS (by decide) (by decide)
          body := by rw [k5_body_at]; exact cX10 _ _ E.cMB (by decide) (by decide)
          mset := cX10 _ _ E.cZ (by decide) (by decide)
          kdata := fun i hi => by
            have hi' : i < 640 := by rw [show sha512KData.length = 640 from rfl] at hi; exact hi
            rw [mem10, hagree _ ((E.sKF.sub (c := i) (l := 1) (by omega)).symm)
              ((E.sKS.sub (c := i) (l := 1) (by omega)).symm)]
            exact E.cK i hi
          hsp := hGa
          hS := by rw [hGn]; omega
          hstp := by rw [hS80]; have := E.hS; omega
          hwbp := by rw [hDkn]; omega
          sC := by rw [RG]; exact sR _ _ (by decide) (by decide)
          sI := by rw [RG]; exact sR _ _ (by decide) (by decide)
          sU := by rw [RG]; exact sR _ _ (by decide) (by decide)
          sB := by rw [RG]; exact sR _ _ (by decide) (by decide)
          sZ := by rw [RG]; exact sR _ _ (by decide) (by decide)
          sK := by rw [RG]; exact kR
          stC := s80 _ _ (by decide) (by decide)
          stI := s80 _ _ (by decide) (by decide)
          stU := s80 _ _ (by decide) (by decide)
          stB := s80 _ _ (by decide) (by decide)
          stZ := s80 _ _ (by decide) (by decide)
          stK := by rw [e80]; exact kS 0x80 64 (by omega)
          stF := by rw [RG, e80]; exact SR 0x80 64 (by omega)
          bF := by rw [RG]; exact dR
          bSt := by rw [e80]; exact dS 0x80 64 (by omega) }
      have lo10 : memLoad32 n10.mem (S + 0x80 + 0x40) = BitVec.ofNat 32 pre.length := by rw [mem10, eC0]; exact hlo
      obtain ⟨n11, c11, pc11, sp11, K11, w11, lo11, hi11, hi11b, hi11c, fr11⟩ := sha384UpdateBlocks_correct n10
        (cX10 _ _ E.cBlk (by decide) (by decide)) pc10' env
        (by rw [r10 a0 (by decide), g8]) (by rw [r10 a1 (by decide), K8 a1 (by decide), K16 a1 (by decide)
          (by decide) (by decide) (by decide), fa1])
        (by rw [r10 a2 (by decide), K8 a2 (by decide), K6 a2 (by decide), K5 a2 (by decide), K4 a2 (by decide), g3])
        ra10 (by decide)
        (by rw [r10 sp (by decide), K8 sp (by decide), K16 sp (by decide) (by decide) (by decide) (by decide), fsp])
        (by rw [lo10, BitVec.toNat_ofNat]; omega)
        (sC0 _ _ (by decide) (by decide)) (sC0 _ _ (by decide) (by decide)) (sC0 _ _ (by decide) (by decide))
        (sC0 _ _ (by decide) (by decide)) (sC0 _ _ (by decide) (by decide)) (by rw [eC0]; exact kS 0xC0 16 (by omega))
        (by rw [RG, eC0]; exact SR 0xC0 16 (by omega)) (by rw [eC0]; exact dS 0xC0 16 (by omega)) (sC0 _ _ (by decide) (by decide))
      have k11 : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 → r ≠ a2 →
          r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) →
          r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) → reg n11 r = reg n10 r := fun r q5 q6 q7 q10 q11 q12 q13
          q14 q15 q16 q17 q28 q29 q30 q31 => K11 r q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31
      refine ⟨n11, n11.mem, c6.trans (.cons d7 (.cons d8 (.cons d9 (.cons d10 c11)))),
        ⟨by rw [pc11], rfl, fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, fun x hx hy => ?_, ?_, ?_,
        fun r q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q9 q19 q28 q29 q30 q31 => ?_⟩
      · rw [w11, mem10, hhash, hblk, List.foldl_append]
      · rw [show S + (0xC0 : Word) = S + 0x80 + 0x40 from eC0.symm, lo11, lo10, BitVec.ofNat_add_ofNat]
      · rw [show S + (0xC4 : Word) = S + 0x80 + 0x44 by rw [BitVec.add_assoc]; rfl, hi11, mem10,
          show S + 0x80 + (0x44 : Word) = S + 0xC4 by rw [BitVec.add_assoc]; rfl]
        exact hhi
      · rw [show S + (0xC8 : Word) = S + 0x80 + 0x48 by rw [BitVec.add_assoc]; rfl, hi11b, mem10,
          show S + 0x80 + (0x48 : Word) = S + 0xC8 by rw [BitVec.add_assoc]; rfl]
        exact hhi2
      · rw [show S + (0xCC : Word) = S + 0x80 + 0x4C by rw [BitVec.add_assoc]; rfl, hi11c, mem10,
          show S + 0x80 + (0x4C : Word) = S + 0xCC by rw [BitVec.add_assoc]; rfl]
        exact hhi3
      · rw [fr11 x (by rw [RG]; exact hx) hy, mem10]
      · rw [k11 s1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          r10 s1 (by decide), K8 s1 (by decide), K6 s1 (by decide), g5]
      · rw [k11 s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          r10 s3 (by decide), K8 s3 (by decide), g6]
      · rw [k11 r q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31, r10 r q1, K8 r q10,
          K16 r q10 q12 q9 q19]
  obtain ⟨n8, Mc, c8, u8, w8, lo8, hi8, hi8b, hi8c, fr8, s1_8, s3_8, K8'⟩ := H8
  have hMc : ∀ x, Sep R 0x3B0 x 1 → Sep S 0xD0 x 1 → Mc x = M0 x := fun x hx hy => by
    rw [fr8 x (by have := hx.sub (c := 0) (l := 0x390) (by omega); rwa [add_ofNat_zero] at this)
      (by rw [e80]; exact hy.sub (c := 0x80) (l := 0x50) (by omega)), hagree x hx hy]
  have cU8 := codeX Mc hMc _ _ E.cU (by decide) (by decide)
  have s4_8 : reg n8 s4 = S := by
    rw [K8' s4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), fs4]
  have sp8 : reg n8 sp = G := by
    rw [K8' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), fsp]
  obtain ⟨n9, d9, u9⟩ := u8.alu cU8 s5u_at_92 (off' := 0x94) (by decide)
  have K9 := u9.upd_ne u8.zero
  have u9' : St Mc U n9 0x94 (reg n9) := u9.self
  obtain ⟨n10, d10, u10⟩ := u9'.alu cU8 s5u_at_94 (off' := 0x96) (by decide)
  have K10 := u10.upd_ne u9'.zero
  have u10' : St Mc U n10 0x96 (reg n10) := u10.self
  obtain ⟨n11, d11, u11⟩ := u10'.alu cU8 s5u_at_96 (off' := 0x98) (by decide)
  have K11 := u11.upd_ne u10'.zero
  have u11' : St Mc U n11 0x98 (reg n11) := u11.self
  have a0_11 : reg n11 a0 = S := by
    rw [K11 a0 (by decide), K10 a0 (by decide), u9.upd_eq (by decide), u8.zero, s4_8]; exact BitVec.zero_add _
  have a1_11 : reg n11 a1 = Dk + BitVec.ofNat 32 (128 * k) := by
    rw [K11 a1 (by decide), u10.upd_eq (by decide), u9'.zero, K9 s3 (by decide), s3_8]; exact BitVec.zero_add _
  have s1_11 : reg n11 s1 = BitVec.ofNat 32 (nk % 128) := by
    rw [K11 s1 (by decide), K10 s1 (by decide), K9 s1 (by decide), s1_8]
  have a2_11 : reg n11 a2 = BitVec.ofNat 32 (nk % 128) := by
    rw [u11.upd_eq (by decide), u10'.zero, K10 s1 (by decide), K9 s1 (by decide), s1_8]; exact BitVec.zero_add _
  have s4_11 : reg n11 s4 = S := by rw [K11 s4 (by decide), K10 s4 (by decide), K9 s4 (by decide), s4_8]
  have sp11 : reg n11 sp = G := by rw [K11 sp (by decide), K10 sp (by decide), K9 sp (by decide), sp8]
  obtain ⟨n12, d12, u12⟩ := u11'.sb cU8 s5u_at_98 (off' := 0x9C) (by decide)
  rw [s4_11, s1_11] at u12
  let pv := (BitVec.ofNat 32 (nk % 128)).extractLsb' 0 8
  let Mt := memStore8 Mc (S + 0x7F) pv
  have e3F : S + 0x7F = S + BitVec.ofNat 32 0x7F := rfl
  have hMt : ∀ x, Sep R 0x3B0 x 1 → Sep S 0xD0 x 1 → Mt x = M0 x := fun x hx hy => by
    have hne : x ≠ S + 0x7F := fun e => by
      have := hy 0x7F (by omega) 0 (by decide); rw [add_ofNat_zero, ← e3F] at this; exact this e.symm
    show memStore8 Mc _ _ x = _
    rw [memStore8_ne hne, hMc x hx hy]
  have cUt := codeX Mt hMt _ _ E.cU (by decide) (by decide)
  obtain ⟨n13, c13, pc13, mem13, regs13⟩ := upd_tail u12 cUt sp11 hGa
  have z11 : reg n11 0 = 0 := u11'.zero
  have oth : ∀ r, r ≠ t1 → r ≠ ra → r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ s3 → r ≠ s4 → r ≠ sp → r ≠ t0 →
      reg n13 r = reg n11 r := fun r q6 q1 q8 q9 q18 q19 q20 q2 q5 => by
    rw [regs13 r q6]; exact updR_other _ _ _ _ z11 r q1 q8 q9 q18 q19 q20 q2
  obtain ⟨vra, vs0, vs1, vs2, vs3, vs4, vsp⟩ := updR_saved Mt G (G + 0x20) (reg n11)
  -- The frame's saved slots survive, so the restore helper gives back the entry registers.
  have slotX : ∀ k', 8 ≤ k' → k' < 32 → Mt (G + BitVec.ofNat 32 k') = Mx (G + BitVec.ofNat 32 k') := by
    intro k' h1 h2
    have hGk : G + BitVec.ofNat 32 k' = R + BitVec.ofNat 32 (0x390 + k') := by rw [hGR, add_ofNat_assoc]
    have sk : Sep (S + 0x80) 0x50 (G + BitVec.ofNat 32 k') 1 := by
      rw [e80, hGk]; exact (E.sSF.sub (c := 0x80) (l := 0x50) (by omega)).subR (c := 0x390 + k') (l := 1) (by omega)
    have rk : Sep R 0x390 (G + BitVec.ofNat 32 k') 1 := by
      rw [hGk]; have := sep_offsets R (c := 0) (n := 0x390) (d := 0x390 + k') (k := 1) (by omega) (by omega)
        (by omega); rwa [add_ofNat_zero] at this
    have hne : G + BitVec.ofNat 32 k' ≠ S + 0x7F := by
      intro e
      have := (E.sSF.sub (c := 0x7F) (l := 1) (by omega)).subR (c := 0x390 + k') (l := 1) (by omega) 0 (by decide)
        0 (by decide)
      rw [add_ofNat_zero, add_ofNat_zero, ← hGk, ← e3F] at this; exact this e.symm
    show memStore8 Mc _ _ _ = _
    rw [memStore8_ne hne, fr8 _ rk sk]
  obtain ⟨hra', hs0', hs1', hs2', hs3', hs4'⟩ := hslots Mt slotX
  have sp13 : reg n13 sp = sp0 := by
    rw [regs13 sp (by decide), vsp]; show sp0 + 0xFFFFFFE0 + 0x20 = sp0; rw [BitVec.add_assoc]; exact BitVec.add_zero _
  -- The tail call of `memcpy` buffers the bytes left over.
  let Sk := Dk + BitVec.ofNat 32 (128 * k)
  have hSkn : Sk.toNat = D.toNat + (n - nk) + 128 * k := by
    show (Dk + BitVec.ofNat 32 (128 * k)).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hDkn, Nat.mod_eq_of_lt (a := 128 * k) (by omega)]; omega
  have hSk : Sk = D + BitVec.ofNat 32 (n - nk + 128 * k) := by
    show Dk + BitVec.ofNat 32 (128 * k) = _; rw [hDk, add_ofNat_assoc]
  let F' := sp0 + 0xFFFFFFF0
  have hF' : F' = R + BitVec.ofNat 32 0x3A0 := by
    show sp0 + 0xFFFFFFF0 = sp0 + 0xFFFFFC50 + BitVec.ofNat 32 0x3A0; rw [BitVec.add_assoc]; rfl
  have hF'n : F'.toNat = sp0.toNat - 16 := by
    show (sp0 + 0xFFFFFFF0).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 2 ^ 32 - 16 from rfl]; omega
  have hnr : nk % 128 + (n - nk + 128 * k) ≤ n := by omega
  have hFe : sp0 + (0xFFFFFFF0 : Word) = R + BitVec.ofNat 32 0x3A0 := hF'
  have hFn : (sp0 + (0xFFFFFFF0 : Word)).toNat = sp0.toNat - 16 := hF'n
  have E' : McEnv n13.mem (BitVec.ofNat 32 memcpyStubAddress + 8) S Sk (reg n13 sp + 0xFFFFFFF0) (nk % 128) := by
    rw [sp13, mem13]
    exact { code := codeX Mt hMt _ _ E.cMB (by decide) (by decide)
            hDC := data_code (by omega) (by decide) (by decide)
            hFC := data_code (by rw [hFn]; omega) (by decide) (by decide)
            hdF := by
              rw [hFe]; exact (E.sSF.sub (c := 0) (l := nk % 128) (by omega)).subR (c := 0x3A0) (l := 16) (by omega)
                |> fun h => by rwa [add_ofNat_zero] at h
            hsF := by
              rw [hFe, hSk]
              exact (E.sDF.sub (c := n - nk + 128 * k) (l := nk % 128) (by omega)).subR (c := 0x3A0) (l := 16)
                (by omega)
            hsep := by
              rw [hSk]
              have h := (E.sDS.sub (c := n - nk + 128 * k) (l := nk % 128) (by omega)).subR (c := 0)
                (l := nk % 128) (by omega)
              rw [add_ofNat_zero] at h
              exact h.symm
            hF := by rw [hFn]; have := E.hsp; omega
            hFw := by rw [hFn]; omega
            hdw := by omega
            hsw := by rw [hSkn]; omega }
  obtain ⟨n14, c14, pc14, sp14, a014, mem14, K14⟩ := memcpy_correct n13 (BitVec.ofNat 32 memcpyStubAddress) rRa
    S Sk (nk % 128) (fun i hi => by
      show n13.mem _ = _; rw [mem13]; exact codeX Mt hMt _ _ E.cMS (by decide) (by decide) i hi) (by decide) pc13
    (by rw [oth a0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), a0_11])
    (by rw [oth a1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), a1_11])
    (by rw [oth a2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), a2_11])
    (by rw [regs13 ra (by decide), vra, hra']) hret E'
  rw [sp13, mem13] at mem14
  have hlen64 : msg'.length % 128 = nk % 128 := by
    have := tailBytes5_length msg'; rw [htail, List.length_drop, memBytes_length] at this; omega
  have hN : nk % 128 < 2 ^ 32 := by omega
  -- Bytes of the hasher after the tail call.
  have atS : ∀ c, c < 0xD0 → n14.mem (S + BitVec.ofNat 32 c) = copyBytes Mt S Sk (nk % 128) (S + BitVec.ofNat 32 c) :=
    fun c hc => mem14 _ (by
      rw [hFe]; exact ((E.sSF.sub (c := c) (l := 1) (by omega)).subR (c := 0x3A0) (l := 16) (by omega)).symm)
  have hiS : ∀ c, 0x80 ≤ c → c < 0xD0 → n14.mem (S + BitVec.ofNat 32 c) = Mc (S + BitVec.ofNat 32 c) := by
    intro c h1 h2
    rw [atS c h2, copyBytes_out (by rw [add_sub_toNat S (by omega)]; omega)]
    show memStore8 Mc _ _ _ = _
    rw [memStore8_ne (by rw [e3F]; exact add_ofNat_ne S (by omega) (by omega) (by omega))]
  have ld : ∀ c, 0x80 ≤ c → c + 4 ≤ 0xD0 → memLoad32 n14.mem (S + BitVec.ofNat 32 c) = memLoad32 Mc (S + BitVec.ofNat 32 c) :=
    fun c h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact hiS _ (by omega) (by omega)
  have pvE : pv = BitVec.ofNat 8 (msg'.length % 128) := by
    rw [hlen64]; apply BitVec.eq_of_toNat_eq
    show ((BitVec.ofNat 32 (nk % 128)).extractLsb' 0 8).toNat = _
    rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]; omega
  have H' : Hasher5At n14.mem S msg' :=
    { hlen := hlen
      pos := by
        rw [e3F, atS 0x7F (by omega), copyBytes_out (by rw [add_sub_toNat S (by omega)]; omega), ← e3F]
        show memStore8 Mc _ _ _ = _
        rw [memStore8_same, pvE]
      buf := by
        rw [hlen64, htail, memBytes_drop _ _ hkk, show nk - 128 * k = nk % 128 by show nk - 128 * (nk / 128) = _; omega]
        unfold memBytes
        apply List.map_congr_left
        intro i hi
        have hi := List.mem_range.mp hi
        have h1 : Mt (Sk + BitVec.ofNat 32 i) = M0 (Sk + BitVec.ofNat 32 i) := by
          apply hMt
          · rw [hSk, add_ofNat_assoc]
            exact (E.sDF.sub (c := n - nk + 128 * k + i) (l := 1) (by omega)).symm
          · rw [hSk, add_ofNat_assoc]
            exact (E.sDS.sub (c := n - nk + 128 * k + i) (l := 1) (by omega)).symm
        rw [atS i (by omega), copyBytes_in hi hN, h1]
      hash := by
        rw [hfull, ← w8, s5Hv_congr (M := Mc) (M' := n14.mem) fun i hi => by
          rw [e80, add_ofNat_assoc]; exact hiS _ (by omega) (by omega)]
      lo := by
        rw [show S + (0xC0 : Word) = S + BitVec.ofNat 32 0xC0 from rfl, ld 0xC0 (by omega) (by omega),
          show S + BitVec.ofNat 32 0xC0 = S + 0xC0 from rfl, lo8, hfl]
      hi := by
        rw [show S + (0xC4 : Word) = S + BitVec.ofNat 32 0xC4 from rfl, ld 0xC4 (by omega) (by omega),
          show S + BitVec.ofNat 32 0xC4 = S + 0xC4 from rfl, hi8]
      hi2 := by
        rw [show S + (0xC8 : Word) = S + BitVec.ofNat 32 0xC8 from rfl, ld 0xC8 (by omega) (by omega),
          show S + BitVec.ofNat 32 0xC8 = S + 0xC8 from rfl, hi8b]
      hi3 := by
        rw [show S + (0xCC : Word) = S + BitVec.ofNat 32 0xCC from rfl, ld 0xCC (by omega) (by omega),
          show S + BitVec.ofNat 32 0xCC = S + 0xCC from rfl, hi8c] }
  have k14 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp →
      reg n14 r = reg n13 r := K14
  refine ⟨n14, c8.trans (.cons d9 (.cons d10 (.cons d11 (.cons d12 (c13.trans c14))))), pc14, by rw [sp14, sp13],
    ?_, ?_, ?_, ?_, ?_, fun r q1 q2 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q28 q29 q30 q31 =>
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
      K11 r q12, K10 r q11, K9 r q10, K8' r q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q9 q19 q28 q29 q30 q31]
  · have hxF : Sep (sp0 + 0xFFFFFFF0) 16 x 1 := by
      rw [hFe]; exact hx.sub (c := 0x3A0) (l := 16) (by omega)
    rw [mem14 x hxF, copyBytes_out (fun hlt => by
      have e := sub_eq_ofNat (k := (x - S).toNat) (x - S).isLt rfl
      have := hy (x - S).toNat (by omega) 0 (by decide); rw [add_ofNat_zero] at this; exact this e.symm)]
    exact hMt x hx hy

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
/-- **The compiled `update` of `sha2`'s SHA-512.** Called with the hasher
at `S` holding `msg` and `n` bytes at `D`, it leaves the hasher holding
`msg` followed by those bytes, returns to `retAddr` with `sp` restored and
the callee-saved registers kept, and changes no memory outside the hasher
and 0x3B0 bytes of stack below `sp`. `n` is below 2^31, as Rust's slice
lengths are, and the whole message stays below 2^32 bytes. -/
theorem sha512Update_correct (m : Machine) {S D sp0 retAddr : Word} {n : Nat} {msg : Bytes}
    (E : UpdEnv m.mem S D sp0 n) (hpc : m.pc = BitVec.ofNat 32 sha512UpdateAddress)
    (ha0 : reg m a0 = S) (ha1 : reg m a1 = D) (ha2 : reg m a2 = BitVec.ofNat 32 n)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0)
    (H : Hasher5At m.mem S msg) (hn : n < 2 ^ 31) (hlen : msg.length + n < 2 ^ 32) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ r, r ≠ ra → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 →
        r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) →
        r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) → r ≠ sp → reg m' r = reg m r) ∧
      Hasher5At m'.mem S (msg ++ memBytes m.mem D n) ∧
      ∀ x, Sep (sp0 + 0xFFFFFC50) 0x3B0 x 1 → Sep S 0xD0 x 1 → m'.mem x = m.mem x := by
  let U := BitVec.ofNat 32 sha512UpdateAddress
  let M0 := m.mem
  let G := sp0 + 0xFFFFFFE0
  let R := sp0 + 0xFFFFFC50
  let data := memBytes M0 D n
  let pos := msg.length % 128
  have hSw := E.hSw
  have hspw := E.hspw
  have hspl := E.hspl
  have hDw := E.hDw
  have hRn : R.toNat = sp0.toNat - 0x3B0 := by
    show (sp0 + 0xFFFFFC50).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFC50 : Word).toNat = 2 ^ 32 - 0x3B0 from rfl]; omega
  have hGn : G.toNat = sp0.toNat - 0x20 := by
    show (sp0 + 0xFFFFFFE0).toNat = _
    rw [BitVec.toNat_add, show (0xFFFFFFE0 : Word).toNat = 2 ^ 32 - 0x20 from rfl]; omega
  have hGa : G.toNat % 4 = 0 := by rw [hGn]; have := E.hsp; omega
  have hGR : G = R + BitVec.ofNat 32 0x390 := by
    show sp0 + 0xFFFFFFE0 = sp0 + 0xFFFFFC50 + BitVec.ofNat 32 0x390
    rw [BitVec.add_assoc]; rfl
  have codeX : ∀ (My : Word → BitVec 8), (∀ x, Sep R 0x3B0 x 1 → Sep S 0xD0 x 1 → My x = M0 x) →
      ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn My b code := fun My h b code hc hb hbl i hi => by
    rw [h _ ((data_code (by rw [hRn]; omega) hb hbl).subR (c := i) (l := 1) (by omega))
      ((data_code (by omega) hb hbl).subR (c := i) (l := 1) (by omega))]
    exact hc i hi
  have st0 : St M0 U m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  obtain ⟨m2, M2, c2, u2, sp2, K2, out2, slots⟩ := upd_pro st0 E.cU
    (by rw [hsp]) hGa (by rw [hGn]; omega)
  have hM2 : ∀ x, Sep R 0x3B0 x 1 → Sep S 0xD0 x 1 → M2 x = M0 x := fun x hx _ => out2 x (by
    rw [hGR]; exact hx.sub (c := 0x390) (l := 32) (by omega))
  have cU2 := codeX M2 hM2 _ _ E.cU (by decide) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.alu cU2 s5u_at_e (off' := 0x10) (by decide)
  have K3 := u3.upd_ne u2.zero
  have u3' : St M2 U n3 0x10 (reg n3) := u3.self
  obtain ⟨n4, d4, u4⟩ := u3'.alu cU2 s5u_at_10 (off' := 0x12) (by decide)
  have K4 := u4.upd_ne u3'.zero
  have u4' : St M2 U n4 0x12 (reg n4) := u4.self
  have s4_4 : reg n4 s4 = S := by
    rw [u4.upd_eq (by decide), u3'.zero, K3 a0 (by decide), K2 a0 (by decide), ha0]
    exact BitVec.zero_add _
  have s1_4 : reg n4 s1 = BitVec.ofNat 32 n := by
    rw [K4 s1 (by decide), u3.upd_eq (by decide), u2.zero, K2 a2 (by decide), ha2]
    exact BitVec.zero_add _
  obtain ⟨n5, d5, u5⟩ := u4'.lbu cU2 s5u_at_12 (off' := 0x16) (by decide)
  have SG : ∀ c, c < 0xD0 → Sep G 32 (S + BitVec.ofNat 32 c) 1 := fun c hc => by
    rw [hGR]; exact ((E.sSF.sub (c := c) (l := 1) (by omega)).subR (c := 0x390) (l := 32) (by omega)).symm
  have posB : M2 (S + 0x7F) = BitVec.ofNat 8 pos := by
    rw [show S + (0x7F : Word) = S + BitVec.ofNat 32 0x7F from rfl, out2 _ (SG 0x7F (by omega))]
    exact H.pos
  have a0_4 : reg n4 a0 = S := by rw [K4 a0 (by decide), K3 a0 (by decide), K2 a0 (by decide), ha0]
  have g5 : reg n5 s0 = BitVec.ofNat 32 pos := by
    rw [u5.upd_eq (by decide), a0_4, posB]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hpos : pos < 128 := Nat.mod_lt _ (by decide)
  have K5 := u5.upd_ne u4'.zero
  have u5' : St M2 U n5 0x16 (reg n5) := u5.self
  obtain ⟨n6, d6, u6⟩ := u5'.aluImm cU2 s5u_at_16 (off' := 0x1A) (by decide)
  have K6 := u6.upd_ne u5'.zero
  have u6' : St M2 U n6 0x1A (reg n6) := u6.self
  obtain ⟨n7, d7, u7⟩ := u6'.alu cU2 s5u_at_1a (off' := 0x1C) (by decide)
  have g7 : reg n7 a2 = BitVec.ofNat 32 (128 - pos) := by
    rw [u7.upd_eq (by decide), u6.upd_eq (by decide), u5'.zero, K6 s0 (by decide), g5,
      show aluEval .add (0 : Word) 0x80 = BitVec.ofNat 32 128 from rfl]
    exact sub_val (x := 128) (y := pos) (by omega) (by decide)
  have K7 := u7.upd_ne u6'.zero
  have u7' : St M2 U n7 0x1C (reg n7) := u7.self
  -- Registers so far, against the entry machine's.
  have K27 : ∀ r, r ≠ sp → r ≠ t0 → r ≠ s1 → r ≠ s4 → r ≠ s0 → r ≠ a2 → reg n7 r = reg m r :=
    fun r q2 q5 q9 q20 q8 q12 => by rw [K7 r q12, K6 r q12, K5 r q8, K4 r q20, K3 r q9, K2 r q2]
  have s0_7 : reg n7 s0 = BitVec.ofNat 32 pos := by rw [K7 s0 (by decide), K6 s0 (by decide), g5]
  have s1_7 : reg n7 s1 = BitVec.ofNat 32 n := by
    rw [K7 s1 (by decide), K6 s1 (by decide), K5 s1 (by decide), s1_4]
  have s4_7 : reg n7 s4 = S := by rw [K7 s4 (by decide), K6 s4 (by decide), K5 s4 (by decide), s4_4]
  have a1_7 : reg n7 a1 = D := by rw [K27 a1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ha1]
  have sp7 : reg n7 sp = G := by
    rw [K7 sp (by decide), K6 sp (by decide), K5 sp (by decide), K4 sp (by decide), K3 sp (by decide), sp2]
  have c7 : Steps m n7 := c2.trans (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.single d7)))))
  have ultR := ult_lit (x := n) (y := 128 - pos) (by omega) (by omega)
  have hGF : G + 0xFFFFFFF0 = R + BitVec.ofNat 32 0x380 := by
    show sp0 + 0xFFFFFFE0 + 0xFFFFFFF0 = sp0 + 0xFFFFFC50 + BitVec.ofNat 32 0x380
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl
  have hFn : (G + 0xFFFFFFF0).toNat = sp0.toNat - 0x30 := by
    rw [hGF, BitVec.toNat_add, BitVec.toNat_ofNat, hRn]; omega
  -- A `memcpy` call from `update`, with `sp` at `G`, of `N` bytes from `D` into the buffer at byte `p`.
  have mcEnv : ∀ (My : Word → BitVec 8) (p N : Nat), p + N ≤ 128 → N ≤ n →
      (∀ x, Sep R 0x3B0 x 1 → Sep S 0xD0 x 1 → My x = M0 x) →
      McEnv My (BitVec.ofNat 32 memcpyStubAddress + 8) (S + BitVec.ofNat 32 p) D (G + 0xFFFFFFF0) N := by
    intro My p N hpN hNn hMy
    have hSp : (S + BitVec.ofNat 32 p).toNat = S.toNat + p := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    exact { code := codeX My hMy _ _ E.cMB (by decide) (by decide)
            hDC := data_code (by rw [hSp]; omega) (by decide) (by decide)
            hFC := data_code (by rw [hFn]; omega) (by decide) (by decide)
            hdF := by rw [hGF]; exact (E.sSF.sub (c := p) (l := N) (by omega)).subR (c := 0x380) (l := 16) (by omega)
            hsF := by
              rw [hGF]; have h := (E.sDF.sub (c := 0) (l := N) (by omega)).subR (c := 0x380) (l := 16) (by omega)
              rwa [add_ofNat_zero] at h
            hsep := by
              have h := (E.sDS.sub (c := 0) (l := N) (by omega)).subR (c := p) (l := N) (by omega)
              rw [add_ofNat_zero] at h; exact h.symm
            hF := by rw [hFn]; have := E.hsp; omega
            hFw := by rw [hFn]; omega
            hdw := by rw [hSp]; omega
            hsw := by omega }
  -- After such a call, memory outside the stack area and the hasher is the entry memory's.
  have mcOut : ∀ (My Mz : Word → BitVec 8) (p N : Nat), p + N ≤ 0xD0 →
      (∀ x, Sep R 0x3B0 x 1 → Sep S 0xD0 x 1 → My x = M0 x) →
      (∀ x, Sep (G + 0xFFFFFFF0) 16 x 1 → Mz x = copyBytes My (S + BitVec.ofNat 32 p) D N x) →
      ∀ x, Sep R 0x3B0 x 1 → Sep S 0xD0 x 1 → Mz x = M0 x := by
    intro My Mz p N hpN hMy hMz x hx hy
    rw [hMz x (by rw [hGF]; exact hx.sub (c := 0x380) (l := 16) (by omega)),
      copyBytes_sep (hy.sub (c := p) (l := N) hpN) (Nat.le_refl N), hMy x hx hy]
  have hposd : pos = msg.length % 128 := rfl
  have hdata : data.length = n := memBytes_length _ _ _
  have hmsgd : msg ++ memBytes m.mem D n = msg ++ data := rfl
  have zR : reg n7 0 = 0 := u7'.zero
  have ld2 : ∀ c, c + 4 ≤ 0xD0 → memLoad32 M2 (S + BitVec.ofNat 32 c) = memLoad32 M0 (S + BitVec.ofNat 32 c) :=
    fun c hc => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact out2 _ (SG _ (by omega))
  -- The paths that compress end in `upd_join` at 0x70.
  have J : ∀ (nn : Machine) (Mx : Word → BitVec 8) (f : Fin 32 → Word) (Dk : Word) (nk : Nat)
      (pre : List Bytes), Steps m nn → St Mx U nn 0x70 f →
      (∀ x, Sep R 0x3B0 x 1 → Sep S 0xD0 x 1 → Mx x = M0 x) →
      (∀ k, 8 ≤ k → k < 32 → Mx (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k)) →
      nk ≤ n → Dk = D + BitVec.ofNat 32 (n - nk) →
      f a1 = Dk → f s1 = BitVec.ofNat 32 nk → f s2 = S + 0x80 → f s4 = S → f sp = G →
      (∀ r, r ≠ ra → r ≠ sp → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ s0 → r ≠ s1 →
        r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ s2 → r ≠ s3 →
        r ≠ s4 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) →
        f r = reg m r) →
      (s5Hv Mx (S + 0x80)).toList = pre.foldl Sha512.compress Sha512.h0 →
      memLoad32 Mx (S + 0xC0) = BitVec.ofNat 32 pre.length → memLoad32 Mx (S + 0xC4) = 0 →
      memLoad32 Mx (S + 0xC8) = 0 → memLoad32 Mx (S + 0xCC) = 0 →
      fullBlocks5 (msg ++ data) = pre ++ Sha512.blocks (nk / 128) (memBytes M0 Dk nk) →
      tailBytes5 (msg ++ data) = (memBytes M0 Dk nk).drop (128 * (nk / 128)) →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
        (∀ r, r ≠ ra → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 →
          r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) →
          r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) → r ≠ sp → reg m' r = reg m r) ∧
        Hasher5At m'.mem S (msg ++ memBytes m.mem D n) ∧
        ∀ x, Sep (sp0 + 0xFFFFFC50) 0x3B0 x 1 → Sep S 0xD0 x 1 → m'.mem x = m.mem x := by
    intro nn Mx f Dk nk pre cn sn hag hsl hnk hDk fa1 fs1 fs2 fs4 fsp fo hh hl hhi hhi8 hhiC hf ht
    obtain ⟨m', c', pc', sp', s0', s1', s2', s3', s4', K', H', fr'⟩ := upd_join (msg' := msg ++ data) nn E sn
      hag hnk hDk hn fa1 fs1 fs2 fs4 fsp
      (fun My h => slots My fun k h1 h2 => (h k h1 h2).trans (hsl k h1 h2)) (by rw [hra]; exact hret)
      hh hl hhi hhi8 hhiC hf ht (by rw [List.length_append, hdata]; exact hlen)
    refine ⟨m', cn.trans c', by rw [pc', hra], sp',
      fun r q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q2 => ?_, H', fr'⟩
    by_cases h8 : r = s0
    · subst h8; exact s0'
    by_cases h9 : r = s1
    · subst h9; exact s1'
    by_cases h18 : r = s2
    · subst h18; exact s2'
    by_cases h19 : r = s3
    · subst h19; exact s3'
    by_cases h20 : r = s4
    · subst h20; exact s4'
    rw [K' r q1 q2 q5 q6 q7 h8 h9 q10 q11 q12 q13 q14 q15 q16 q17 h18 h19 h20 q28 q29 q30 q31,
      fo r q1 q2 q5 q6 q7 h8 h9 q10 q11 q12 q13 q14 q15 q16 q17 h18 h19 h20 q28 q29 q30 q31]
  by_cases hA : n < 128 - pos
  · -- The bytes fit in the buffer: copy them in and store the new count.
    obtain ⟨n8, d8, u8⟩ := u7'.notTaken cU2 0x20 s5u_at_1c (by decide) (by
      simp only [branchTaken]; rw [s1_7, g7, ultR]; simp only [Bool.not_eq_false']
      exact decide_eq_true hA)
    obtain ⟨n9, d9, u9⟩ := u8.alu cU2 s5u_at_20 (off' := 0x24) (by decide)
    have K9 := u9.upd_ne zR
    have u9' : St M2 U n9 0x24 (reg n9) := u9.self
    have a0_9 : reg n9 a0 = S + BitVec.ofNat 32 pos := by rw [u9.upd_eq (by decide), s4_7, s0_7]; rfl
    obtain ⟨n10, d10, u10⟩ := u9'.alu cU2 s5u_at_24 (off' := 0x26) (by decide)
    have K10 := u10.upd_ne u9'.zero
    have u10' : St M2 U n10 0x26 (reg n10) := u10.self
    have a2_10 : reg n10 a2 = BitVec.ofNat 32 n := by
      rw [u10.upd_eq (by decide), u9'.zero, K9 s1 (by decide), s1_7]; exact BitVec.zero_add _
    obtain ⟨n11, d11, u11⟩ := u10'.auipc cU2 s5u_at_26 (off' := 0x2A) (by decide)
    obtain ⟨n12, d12, pc12, mem12, regs12⟩ := u11.call cU2 s5u_at_2a
    have r12 : ∀ r, r ≠ ra → reg n12 r = reg n10 r := fun r h => by
      rw [regs12]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd]; exact u10'.zero.symm
      · simp [upd, h0, h]
    have ra12 : reg n12 ra = U + BitVec.ofNat 32 0x2E := by rw [regs12]; simp +decide [upd]; rfl
    have pc12' : n12.pc = BitVec.ofNat 32 memcpyStubAddress := by
      rw [pc12, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]
      decide
    have sp12 : reg n12 sp = G := by rw [r12 sp (by decide), K10 sp (by decide), K9 sp (by decide), sp7]
    obtain ⟨n13, c13, pc13, sp13, a013, mem13, K13⟩ := memcpy_correct n12 (BitVec.ofNat 32 memcpyStubAddress)
      (U + BitVec.ofNat 32 0x2E) (S + BitVec.ofNat 32 pos) D n (fun i hi => by
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
    have u13 : St MA U n13 0x2E (reg n13) := ⟨by rw [pc13], rfl, fun _ => rfl⟩
    have k13 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
        r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ sp →
        reg n13 r = reg n12 r := K13
    have K7_13 : ∀ r, r ≠ ra → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 →
        r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) →
        r ≠ (30 : Fin 32) → r ≠ sp → reg n13 r = reg n7 r :=
      fun r q1 q10 q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2 => by
        rw [k13 r q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2, r12 r q1, K10 r q12, K9 r q10]
    obtain ⟨n14, d14, u14⟩ := u13.alu cUA s5u_at_2e (off' := 0x30) (by decide)
    have K14 := u14.upd_ne u13.zero
    have u14' : St MA U n14 0x30 (reg n14) := u14.self
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
    obtain ⟨n15, d15, u15⟩ := u14'.sb cUA s5u_at_30 (off' := 0x34) (by decide)
    rw [s4_14, s0_14] at u15
    let pv := (BitVec.ofNat 32 (pos + n)).extractLsb' 0 8
    let Mt := memStore8 MA (S + 0x7F) pv
    have e3F : S + 0x7F = S + BitVec.ofNat 32 0x7F := rfl
    have hMt : ∀ x, Sep R 0x3B0 x 1 → Sep S 0xD0 x 1 → Mt x = M0 x := fun x hx hy => by
      have hne : x ≠ S + 0x7F := fun e => by
        have := hy 0x7F (by omega) 0 (by decide); rw [add_ofNat_zero, ← e3F] at this; exact this e.symm
      show memStore8 MA _ _ x = _
      rw [memStore8_ne hne, hMA x hx hy]
    have cUt := codeX Mt hMt _ _ E.cU (by decide) (by decide)
    obtain ⟨n16, c16, pc16, mem16, regs16⟩ := upd_ret u15 cUt sp14 hGa
    have SF : ∀ c, c < 0xD0 → Sep (G + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 c) 1 := fun c hc => by
      rw [hGF]; exact ((E.sSF.sub (c := c) (l := 1) (by omega)).subR (c := 0x380) (l := 16) (by omega)).symm
    -- The hasher's bytes after the buffer's new bytes are the entry memory's.
    have hiS : ∀ c, pos + n ≤ c → c ≠ 0x7F → c < 0xD0 → Mt (S + BitVec.ofNat 32 c) = M0 (S + BitVec.ofNat 32 c) := by
      intro c h1 h2 h3
      show memStore8 MA _ _ _ = _
      rw [memStore8_ne (by rw [e3F]; exact add_ofNat_ne S (by omega) (by omega) h2), mA _ (SF c h3),
        copyBytes_sep (sep_offsets S (c := pos) (n := n) (d := c) (k := 1) (Or.inl h1) (by omega) (by omega))
          (Nat.le_refl n), out2 _ (SG c h3)]
    have ld : ∀ c, 0x80 ≤ c → c + 4 ≤ 0xD0 →
        memLoad32 Mt (S + BitVec.ofNat 32 c) = memLoad32 M0 (S + BitVec.ofNat 32 c) :=
      fun c h1 h2 => memLoad32_congr fun j hj => by
        rw [add_ofNat_assoc]; exact hiS _ (by omega) (by omega) (by omega)
    have slotX : ∀ k', 8 ≤ k' → k' < 32 → Mt (G + BitVec.ofNat 32 k') = M2 (G + BitVec.ofNat 32 k') := by
      intro k' h1 h2
      have hGk : G + BitVec.ofNat 32 k' = R + BitVec.ofNat 32 (0x390 + k') := by rw [hGR, add_ofNat_assoc]
      have hne : G + BitVec.ofNat 32 k' ≠ S + 0x7F := by
        intro e
        have := (E.sSF.sub (c := 0x7F) (l := 1) (by omega)).subR (c := 0x390 + k') (l := 1) (by omega) 0 (by decide)
          0 (by decide)
        rw [add_ofNat_zero, add_ofNat_zero, ← hGk, ← e3F] at this; exact this e.symm
      show memStore8 MA _ _ _ = _
      rw [memStore8_ne hne, mA (G + BitVec.ofNat 32 k') (by
          rw [hGF, hGk]; exact sep_offsets R (c := 0x380) (n := 16) (d := 0x390 + k') (k := 1) (Or.inl (by omega))
            (by omega) (by omega)),
        copyBytes_sep (by
          rw [hGk]; exact (E.sSF.sub (c := pos) (l := n) (by omega)).subR (c := 0x390 + k') (l := 1) (by omega))
          (Nat.le_refl n)]
    obtain ⟨hra', hs0', hs1', hs2', hs3', hs4'⟩ := slots Mt slotX
    obtain ⟨vra, vs0, vs1, vs2, vs3, vs4, vsp⟩ := updR_saved Mt G (G + 0x20) (reg n14)
    have hm : (msg ++ data).length % 128 = pos + n := by rw [List.length_append, hdata]; omega
    obtain ⟨hf1, hf2⟩ := fullBlocks5_append msg data
    rw [tailBytes5_length, hdata, show (msg.length % 128 + n) / 128 = 0 by omega] at hf1 hf2
    have H' : Hasher5At Mt S (msg ++ data) :=
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
            have h3 : S + BitVec.ofNat 32 pos + BitVec.ofNat 32 i ≠ S + 0x7F := by
              rw [add_ofNat_assoc, e3F]; exact add_ofNat_ne S (by omega) (by omega) (by omega)
            have h4 : Sep (G + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 pos + BitVec.ofNat 32 i) 1 := by
              rw [add_ofNat_assoc]; exact SF _ (by omega)
            show (memStore8 MA _ _ _).toNat = _
            rw [memStore8_ne h3, mA _ h4, copyBytes_in hi (by omega),
              hM2 _ (E.sDF.sub (c := i) (l := 1) (by omega)).symm (E.sDS.sub (c := i) (l := 1) (by omega)).symm]
          rw [b1, b2]
        hash := by
          rw [hf1, show Sha512.blocks 0 (tailBytes5 msg ++ data) = [] from rfl, List.append_nil, ← H.hash,
            s5Hv_congr (M := M0) (M' := Mt) fun i hi => by
              rw [show S + (0x80 : Word) = S + BitVec.ofNat 32 0x80 from rfl, add_ofNat_assoc]
              exact hiS _ (by omega) (by omega) (by omega)]
        lo := by
          rw [List.length_append, hdata, show (msg.length + n) / 128 = msg.length / 128 by omega, ← H.lo,
            show S + (0xC0 : Word) = S + BitVec.ofNat 32 0xC0 from rfl]
          exact ld 0xC0 (by omega) (by omega)
        hi := by
          rw [← H.hi, show S + (0xC4 : Word) = S + BitVec.ofNat 32 0xC4 from rfl]
          exact ld 0xC4 (by omega) (by omega)
        hi2 := by
          rw [← H.hi2, show S + (0xC8 : Word) = S + BitVec.ofNat 32 0xC8 from rfl]
          exact ld 0xC8 (by omega) (by omega)
        hi3 := by
          rw [← H.hi3, show S + (0xCC : Word) = S + BitVec.ofNat 32 0xCC from rfl]
          exact ld 0xCC (by omega) (by omega) }
    refine ⟨n16, c7.trans (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (c13.trans
      (.cons d14 (.cons d15 c16)))))))), ?_, ?_,
      fun r q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q2 => ?_, by rw [mem16]; exact H',
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
      rw [updR_other _ _ _ _ u14'.zero r q1 h8 h9 h18 h19 h20 q2, K14 r h8,
        K7_13 r q1 q10 q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2, K27 r q2 q5 h9 h20 h8 q12]
  · -- The bytes fill the buffer.
    obtain ⟨n8, d8, u8⟩ := u7'.taken cU2 0x44 s5u_at_1c (by decide) (by
      simp only [branchTaken]; rw [s1_7, g7, ultR, decide_eq_false hA]; rfl)
    obtain ⟨n9, d9, u9⟩ := u8.aluImm cU2 s5u_at_44 (off' := 0x48) (by decide)
    have K9 := u9.upd_ne zR
    have u9' : St M2 U n9 0x48 (reg n9) := u9.self
    have s2_9 : reg n9 s2 = S + 0x80 := by rw [u9.upd_eq (by decide), s4_7]; rfl
    have hh2 : (s5Hv M2 (S + 0x80)).toList = (fullBlocks5 msg).foldl Sha512.compress Sha512.h0 := by
      rw [← H.hash, s5Hv_congr (M := M0) (M' := M2) fun i hi => by
        rw [show S + (0x80 : Word) = S + BitVec.ofNat 32 0x80 from rfl, add_ofNat_assoc]
        exact out2 _ (SG _ (by omega))]
    have hl2 : memLoad32 M2 (S + 0xC0) = BitVec.ofNat 32 (fullBlocks5 msg).length := by
      rw [fullBlocks5_length, ← H.lo, show S + (0xC0 : Word) = S + BitVec.ofNat 32 0xC0 from rfl]
      exact ld2 0xC0 (by omega)
    have hc4 : memLoad32 M2 (S + 0xC4) = 0 := by
      rw [← H.hi, show S + (0xC4 : Word) = S + BitVec.ofNat 32 0xC4 from rfl]
      exact ld2 0xC4 (by omega)
    have hc8 : memLoad32 M2 (S + 0xC8) = 0 := by
      rw [← H.hi2, show S + (0xC8 : Word) = S + BitVec.ofNat 32 0xC8 from rfl]
      exact ld2 0xC8 (by omega)
    have hcC : memLoad32 M2 (S + 0xCC) = 0 := by
      rw [← H.hi3, show S + (0xCC : Word) = S + BitVec.ofNat 32 0xCC from rfl]
      exact ld2 0xCC (by omega)
    by_cases hp0 : pos = 0
    · -- The buffer is empty: compress straight from the input.
      obtain ⟨n10, d10, u10⟩ := u9'.taken cU2 0x70 s5u_at_48 (by decide) (by
        simp only [branchTaken]; rw [K9 s0 (by decide), s0_7, u9'.zero, hp0]; rfl)
      have ht0 : tailBytes5 msg = [] := List.eq_nil_of_length_eq_zero (by rw [tailBytes5_length]; exact hp0)
      obtain ⟨hf1, hf2⟩ := fullBlocks5_append msg data
      rw [ht0, List.length_nil, Nat.zero_add, List.nil_append, hdata] at hf1 hf2
      exact J n10 M2 (reg n9) D n (fullBlocks5 msg) (c7.trans (.cons d8 (.cons d9 (.single d10)))) u10 hM2
        (fun _ _ _ => rfl) (Nat.le_refl n) (by rw [Nat.sub_self, add_ofNat_zero])
        (by rw [K9 a1 (by decide), a1_7]) (by rw [K9 s1 (by decide), s1_7]) s2_9
        (by rw [K9 s4 (by decide), s4_7]) (by rw [K9 sp (by decide), sp7])
        (fun r q1 q2 q5 _ _ h8 h9 _ _ q12 _ _ _ _ _ h18 _ h20 _ _ _ _ => by
          rw [K9 r h18, K27 r q2 q5 h9 h20 h8 q12])
        hh2 hl2 hc4 hc8 hcC hf1 hf2
    · -- The buffer holds `pos` bytes: fill it from the input and compress it.
      let rem := 128 - pos
      have hrem : rem ≤ n := by omega
      obtain ⟨n10, d10, u10⟩ := u9'.notTaken cU2 0x4A s5u_at_48 (by decide) (by
        simp only [branchTaken]; rw [K9 s0 (by decide), s0_7, u9'.zero, beq_eq_false_iff_ne]
        intro h; exact hp0 (ofNat_inj (by omega) (by decide) h))
      have a1_9 : reg n9 a1 = D := by rw [K9 a1 (by decide), a1_7]
      have a2_9 : reg n9 a2 = BitVec.ofNat 32 rem := by rw [K9 a2 (by decide), g7]
      obtain ⟨n11, d11, u11⟩ := u10.alu cU2 s5u_at_4a (off' := 0x4E) (by decide)
      have K11 := u11.upd_ne u9'.zero
      have u11' : St M2 U n11 0x4E (reg n11) := u11.self
      have s3_11 : reg n11 s3 = D + BitVec.ofNat 32 rem := by rw [u11.upd_eq (by decide), a1_9, a2_9]; rfl
      obtain ⟨n12, d12, u12⟩ := u11'.alu cU2 s5u_at_4e (off' := 0x50) (by decide)
      have K12 := u12.upd_ne u11'.zero
      have u12' : St M2 U n12 0x50 (reg n12) := u12.self
      have s1_12 : reg n12 s1 = BitVec.ofNat 32 (n - rem) := by
        rw [u12.upd_eq (by decide), K11 s1 (by decide), K9 s1 (by decide), s1_7, K11 a2 (by decide), a2_9]
        exact sub_val hrem (by omega)
      obtain ⟨n13, d13, u13⟩ := u12'.alu cU2 s5u_at_50 (off' := 0x54) (by decide)
      have K13 := u13.upd_ne u12'.zero
      have u13' : St M2 U n13 0x54 (reg n13) := u13.self
      have a0_13 : reg n13 a0 = S + BitVec.ofNat 32 pos := by
        rw [u13.upd_eq (by decide), K12 s4 (by decide), K11 s4 (by decide), K9 s4 (by decide), s4_7,
          K12 s0 (by decide), K11 s0 (by decide), K9 s0 (by decide), s0_7]; rfl
      -- Registers so far, against `n7`'s.
      have K9_13 : ∀ r, r ≠ s2 → r ≠ s3 → r ≠ s1 → r ≠ a0 → reg n13 r = reg n7 r := fun r q18 q19 q9 q10 => by
        rw [K13 r q10, K12 r q9, K11 r q19, K9 r q18]
      obtain ⟨n14, d14, u14⟩ := u13'.auipc cU2 s5u_at_54 (off' := 0x58) (by decide)
      obtain ⟨n15, d15, pc15, mem15, regs15⟩ := u14.call cU2 s5u_at_58
      have r15 : ∀ r, r ≠ ra → reg n15 r = reg n13 r := fun r h => by
        rw [regs15]
        by_cases h0 : r.val = 0
        · have : r = 0 := Fin.ext h0
          subst this; simp [upd]; exact u13'.zero.symm
        · simp [upd, h0, h]
      have ra15 : reg n15 ra = U + BitVec.ofNat 32 0x5C := by rw [regs15]; simp +decide [upd]; rfl
      have pc15' : n15.pc = BitVec.ofNat 32 memcpyStubAddress := by
        rw [pc15, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]
        decide
      have sp15 : reg n15 sp = G := by
        rw [r15 sp (by decide), K9_13 sp (by decide) (by decide) (by decide) (by decide), sp7]
      obtain ⟨n16, c16, pc16, sp16, a016, mem16, K16⟩ := memcpy_correct n15 (BitVec.ofNat 32 memcpyStubAddress)
        (U + BitVec.ofNat 32 0x5C) (S + BitVec.ofNat 32 pos) D rem (fun i hi => by
          show n15.mem _ = _; rw [mem15]; exact codeX M2 hM2 _ _ E.cMS (by decide) (by decide) i hi) (by decide)
        pc15' (by rw [r15 a0 (by decide), a0_13])
        (by rw [r15 a1 (by decide), K13 a1 (by decide), K12 a1 (by decide), K11 a1 (by decide), a1_9])
        (by rw [r15 a2 (by decide), K13 a2 (by decide), K12 a2 (by decide), K11 a2 (by decide), a2_9])
        ra15 (by decide) (by rw [mem15, sp15]; exact mcEnv M2 pos rem (by omega) hrem hM2)
      rw [sp15, mem15] at mem16
      let MB := n16.mem
      have mB : ∀ x, Sep (G + 0xFFFFFFF0) 16 x 1 → MB x = copyBytes M2 (S + BitVec.ofNat 32 pos) D rem x := mem16
      have hMB := mcOut M2 MB pos rem (by omega) hM2 mem16
      have cUB := codeX MB hMB _ _ E.cU (by decide) (by decide)
      have u16 : St MB U n16 0x5C (reg n16) := ⟨by rw [pc16], rfl, fun _ => rfl⟩
      have k16 : ∀ r, r ≠ ra → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 →
          r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) →
          r ≠ (30 : Fin 32) → r ≠ sp → reg n16 r = reg n13 r :=
        fun r q1 _ q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2 => by
          rw [K16 r q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2, r15 r q1]
      obtain ⟨n17, d17, u17⟩ := u16.aluImm cUB s5u_at_5c (off' := 0x5E) (by decide)
      have K17 := u17.upd_ne u16.zero
      have u17' : St MB U n17 0x5E (reg n17) := u17.self
      obtain ⟨n18, d18, u18⟩ := u17'.alu cUB s5u_at_5e (off' := 0x60) (by decide)
      have K18 := u18.upd_ne u17'.zero
      have u18' : St MB U n18 0x60 (reg n18) := u18.self
      obtain ⟨n19, d19, u19⟩ := u18'.alu cUB s5u_at_60 (off' := 0x62) (by decide)
      have K19 := u19.upd_ne u18'.zero
      have u19' : St MB U n19 0x62 (reg n19) := u19.self
      have K16_19 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → reg n19 r = reg n16 r := fun r q10 q11 q12 => by
        rw [K19 r q11, K18 r q10, K17 r q12]
      have s2_16 : reg n16 s2 = S + 0x80 := by
        rw [k16 s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          K13 s2 (by decide), K12 s2 (by decide), K11 s2 (by decide), s2_9]
      have s4_16 : reg n16 s4 = S := by
        rw [k16 s4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          K9_13 s4 (by decide) (by decide) (by decide) (by decide), s4_7]
      have a0_19 : reg n19 a0 = S + 0x80 := by
        rw [K19 a0 (by decide), u18.upd_eq (by decide), u17'.zero, K17 s2 (by decide), s2_16]
        exact BitVec.zero_add _
      have a1_19 : reg n19 a1 = S := by
        rw [u19.upd_eq (by decide), u18'.zero, K18 s4 (by decide), K17 s4 (by decide), s4_16]
        exact BitVec.zero_add _
      have a2_19 : reg n19 a2 = BitVec.ofNat 32 1 := by
        rw [K19 a2 (by decide), K18 a2 (by decide), u17.upd_eq (by decide), u16.zero]; rfl
      have sp19 : reg n19 sp = G := by
        rw [K16_19 sp (by decide) (by decide) (by decide), sp16, sp15]
      obtain ⟨n20, d20, u20⟩ := u19'.auipc cUB s5u_at_62 (off' := 0x66) (by decide)
      obtain ⟨n21, d21, pc21, mem21, regs21⟩ := u20.call cUB s5u_at_66
      have r21 : ∀ r, r ≠ ra → reg n21 r = reg n19 r := fun r h => by
        rw [regs21]
        by_cases h0 : r.val = 0
        · have : r = 0 := Fin.ext h0
          subst this; simp [upd]; exact u19'.zero.symm
        · simp [upd, h0, h]
      have ra21 : reg n21 ra = U + BitVec.ofNat 32 0x6A := by rw [regs21]; simp +decide [upd]; rfl
      have pc21' : n21.pc = BitVec.ofNat 32 sha384UpdateBlocksAddress := by
        rw [pc21, show ∀ (F : Fin 32 → Word) (v : Word), upd F ra v ra = v from fun F v => by simp [upd]]
        decide
      have RG : G + 0xFFFFFC70 = R := by
        show sp0 + 0xFFFFFFE0 + 0xFFFFFC70 = sp0 + 0xFFFFFC50; rw [BitVec.add_assoc]; rfl
      have eC0 : S + 0x80 + 0x40 = S + BitVec.ofNat 32 0xC0 := by rw [BitVec.add_assoc]; rfl
      have e80 : S + 0x80 = S + BitVec.ofNat 32 0x80 := rfl
      have hS80 : (S + 0x80).toNat = S.toNat + 0x80 := by
        rw [e80, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have hSC0 : (S + 0x80 + 0x40).toNat = S.toNat + 0xC0 := by
        rw [eC0, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have cX21 : ∀ (b : Word) (code : List Nat), CodeIn M0 b code → 0x40000000 ≤ b.toNat →
          b.toNat + code.length ≤ 2 ^ 32 → CodeIn n21.mem b code := fun b code hc hb hbl => by
        rw [mem21]; exact codeX MB hMB b code hc hb hbl
      have sR : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 → Sep R 0x390 b l :=
        fun b l hb hbl => data_code (by rw [hRn]; omega) hb hbl
      have s80 : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 → Sep (S + 0x80) 64 b l :=
        fun b l hb hbl => data_code (by rw [hS80]; omega) hb hbl
      have sC0 : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
          Sep (S + 0x80 + 0x40) 16 b l := fun b l hb hbl => data_code (by rw [hSC0]; omega) hb hbl
      have kR : Sep R 0x390 (BitVec.ofNat 32 sha512KAddress) 640 := by
        have := E.sKF.symm.sub (c := 0) (l := 0x390) (by omega); rwa [add_ofNat_zero] at this
      have kS : ∀ c l, c + l ≤ 0xD0 → Sep (S + BitVec.ofNat 32 c) l (BitVec.ofNat 32 sha512KAddress) 640 :=
        fun c l h => E.sKS.symm.sub (c := c) (l := l) h
      have SR : ∀ c l, c + l ≤ 0xD0 → Sep (S + BitVec.ofNat 32 c) l R 0x390 := fun c l h =>
        (E.sSF.sub (c := c) (l := l) h).subR (c := 0) (l := 0x390) (by omega) |> fun h' => by
          rwa [add_ofNat_zero] at h'
      have SS : ∀ d k, 128 ≤ d → d + k ≤ 0xD0 → Sep S (128 * 1) (S + BitVec.ofNat 32 d) k := fun d k h1 h2 => by
        have := sep_offsets S (c := 0) (n := 128 * 1) (d := d) (k := k) (Or.inl (by omega)) (by omega) (by omega)
        rwa [add_ofNat_zero] at this
      have env : S5Env n21.mem (BitVec.ofNat 32 sha512CompressAddress) G (S + 0x80) S 1 :=
        { hP := by decide
          code := cX21 _ _ E.cC (by decide) (by decide)
          idx := cX21 _ _ E.cI (by decide) (by decide)
          stub := by rw [k5_stub_at]; exact cX21 _ _ E.cMS (by decide) (by decide)
          body := by rw [k5_body_at]; exact cX21 _ _ E.cMB (by decide) (by decide)
          mset := cX21 _ _ E.cZ (by decide) (by decide)
          kdata := fun i hi => by
            have hi' : i < 640 := by rw [show sha512KData.length = 640 from rfl] at hi; exact hi
            rw [mem21, hMB _ ((E.sKF.sub (c := i) (l := 1) (by omega)).symm)
              ((E.sKS.sub (c := i) (l := 1) (by omega)).symm)]
            exact E.cK i hi
          hsp := hGa
          hS := by rw [hGn]; omega
          hstp := by rw [hS80]; have := E.hS; omega
          hwbp := by omega
          sC := by rw [RG]; exact sR _ _ (by decide) (by decide)
          sI := by rw [RG]; exact sR _ _ (by decide) (by decide)
          sU := by rw [RG]; exact sR _ _ (by decide) (by decide)
          sB := by rw [RG]; exact sR _ _ (by decide) (by decide)
          sZ := by rw [RG]; exact sR _ _ (by decide) (by decide)
          sK := by rw [RG]; exact kR
          stC := s80 _ _ (by decide) (by decide)
          stI := s80 _ _ (by decide) (by decide)
          stU := s80 _ _ (by decide) (by decide)
          stB := s80 _ _ (by decide) (by decide)
          stZ := s80 _ _ (by decide) (by decide)
          stK := by rw [e80]; exact kS 0x80 64 (by omega)
          stF := by rw [RG, e80]; exact SR 0x80 64 (by omega)
          bF := by
            rw [RG]; have := SR 0 (128 * 1) (by omega); rwa [add_ofNat_zero] at this
          bSt := by rw [e80]; exact SS 0x80 64 (by omega) (by omega) }
      -- The hasher's bytes from 0x40 on are untouched by the `memcpy`.
      have hiB : ∀ c, 0x80 ≤ c → c < 0xD0 → MB (S + BitVec.ofNat 32 c) = M0 (S + BitVec.ofNat 32 c) :=
        fun c h1 h2 => by
          rw [mB _ (by rw [hGF]; exact ((E.sSF.sub (c := c) (l := 1) (by omega)).subR (c := 0x380) (l := 16)
              (by omega)).symm),
            copyBytes_sep (sep_offsets S (c := pos) (n := rem) (d := c) (k := 1) (Or.inl (by omega)) (by omega)
              (by omega)) (Nat.le_refl rem), out2 _ (SG c h2)]
      have ldB : ∀ c, 0x80 ≤ c → c + 4 ≤ 0xD0 →
          memLoad32 MB (S + BitVec.ofNat 32 c) = memLoad32 M0 (S + BitVec.ofNat 32 c) :=
        fun c h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact hiB _ (by omega) (by omega)
      have lo21 : memLoad32 n21.mem (S + 0x80 + 0x40) = BitVec.ofNat 32 (msg.length / 128) := by
        rw [mem21, eC0, ldB 0xC0 (by omega) (by omega)]; exact H.lo
      obtain ⟨n22, c22, pc22, sp22, K22, w22, lo22, hi22, hi22b, hi22c, fr22⟩ := sha384UpdateBlocks_correct n21
        (cX21 _ _ E.cBlk (by decide) (by decide)) pc21' env
        (by rw [r21 a0 (by decide), a0_19]) (by rw [r21 a1 (by decide), a1_19])
        (by rw [r21 a2 (by decide), a2_19]) ra21 (by decide) (by rw [r21 sp (by decide), sp19])
        (by rw [lo21, BitVec.toNat_ofNat]; omega)
        (sC0 _ _ (by decide) (by decide)) (sC0 _ _ (by decide) (by decide)) (sC0 _ _ (by decide) (by decide))
        (sC0 _ _ (by decide) (by decide)) (sC0 _ _ (by decide) (by decide)) (by rw [eC0]; exact kS 0xC0 16 (by omega))
        (by rw [RG, eC0]; exact SR 0xC0 16 (by omega)) (by rw [eC0]; exact SS 0xC0 16 (by omega) (by omega))
        (sC0 _ _ (by decide) (by decide))
      let MC := n22.mem
      have u22 : St MC U n22 0x6A (reg n22) := ⟨by rw [pc22], rfl, fun _ => rfl⟩
      have k22 : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 → r ≠ a1 → r ≠ a2 →
          r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) →
          r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) → reg n22 r = reg n21 r := fun r q5 q6 q7 q10 q11 q12 q13
          q14 q15 q16 q17 q28 q29 q30 q31 => K22 r q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31
      have fC : ∀ x, Sep (G + 0xFFFFFC70) 0x390 x 1 → Sep (S + 0x80) 0x50 x 1 → MC x = n21.mem x := fr22
      have hMC : ∀ x, Sep R 0x3B0 x 1 → Sep S 0xD0 x 1 → MC x = M0 x := fun x hx hy => by
        rw [fC x (by rw [RG]; have := hx.sub (c := 0) (l := 0x390) (by omega); rwa [add_ofNat_zero] at this)
          (by rw [e80]; exact hy.sub (c := 0x80) (l := 0x50) (by omega)), mem21, hMB x hx hy]
      have cUC := codeX MC hMC _ _ E.cU (by decide) (by decide)
      -- From `n13` to `n22`, the registers the code keeps.
      have K13_22 : ∀ r, r ≠ ra → r ≠ t0 → r ≠ t1 → r ≠ (7 : Fin 32) → r ≠ a0 →
          r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ (28 : Fin 32) →
          r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ (31 : Fin 32) → r ≠ sp → reg n22 r = reg n13 r :=
        fun r q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q2 => by
          rw [k22 r q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31, r21 r q1, K16_19 r q10 q11 q12,
            k16 r q1 q10 q11 q12 q13 q14 q15 q16 q17 q5 q6 q7 q28 q29 q30 q2]
      have s4_22 : reg n22 s4 = S := by
        rw [K13_22 s4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide), K9_13 s4 (by decide) (by decide) (by decide) (by decide), s4_7]
      obtain ⟨n23, d23, u23⟩ := u22.sb cUC s5u_at_6a (off' := 0x6E) (by decide)
      rw [s4_22, u22.zero] at u23
      let Mx := memStore8 MC (S + 0x7F) ((0 : Word).extractLsb' 0 8)
      have e3F : S + 0x7F = S + BitVec.ofNat 32 0x7F := rfl
      have hMx : ∀ x, Sep R 0x3B0 x 1 → Sep S 0xD0 x 1 → Mx x = M0 x := fun x hx hy => by
        have hne : x ≠ S + 0x7F := fun e => by
          have := hy 0x7F (by omega) 0 (by decide); rw [add_ofNat_zero, ← e3F] at this; exact this e.symm
        show memStore8 MC _ _ x = _
        rw [memStore8_ne hne, hMC x hx hy]
      have cUx := codeX Mx hMx _ _ E.cU (by decide) (by decide)
      obtain ⟨n24, d24, u24⟩ := u23.alu cUx s5u_at_6e (off' := 0x70) (by decide)
      have K24 := u24.upd_ne u22.zero
      have a1_24 : reg n24 a1 = D + BitVec.ofNat 32 rem := by
        rw [u24.upd_eq (by decide), u22.zero, K13_22 s3 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), K13 s3 (by decide),
          K12 s3 (by decide), s3_11]
        exact BitVec.zero_add _
      have s1_24 : reg n24 s1 = BitVec.ofNat 32 (n - rem) := by
        rw [K24 s1 (by decide), K13_22 s1 (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide), K13 s1 (by decide), s1_12]
      have s2_24 : reg n24 s2 = S + 0x80 := by
        rw [K24 s2 (by decide), k22 s2 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), r21 s2 (by decide), K16_19 s2 (by decide) (by decide) (by decide), s2_16]
      have s4_24 : reg n24 s4 = S := by rw [K24 s4 (by decide), s4_22]
      have sp24 : reg n24 sp = G := by
        rw [K24 sp (by decide), sp22]
      -- Bytes of the hasher after the store.
      have nx : ∀ c, 0x80 ≤ c → c < 0xD0 → Mx (S + BitVec.ofNat 32 c) = MC (S + BitVec.ofNat 32 c) :=
        fun c h1 h2 => by
          show memStore8 MC _ _ _ = _
          rw [memStore8_ne (by rw [e3F]; exact add_ofNat_ne S (by omega) (by omega) (by omega))]
      have ldx : ∀ c, 0x80 ≤ c → c + 4 ≤ 0xD0 →
          memLoad32 Mx (S + BitVec.ofNat 32 c) = memLoad32 MC (S + BitVec.ofNat 32 c) :=
        fun c h1 h2 => memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact nx _ (by omega) (by omega)
      have hsl : ∀ k, 8 ≤ k → k < 32 → Mx (G + BitVec.ofNat 32 k) = M2 (G + BitVec.ofNat 32 k) := by
        intro k h1 h2
        have hGk : G + BitVec.ofNat 32 k = R + BitVec.ofNat 32 (0x390 + k) := by rw [hGR, add_ofNat_assoc]
        have hne : G + BitVec.ofNat 32 k ≠ S + 0x7F := by
          intro e
          have := (E.sSF.sub (c := 0x7F) (l := 1) (by omega)).subR (c := 0x390 + k) (l := 1) (by omega) 0
            (by decide) 0 (by decide)
          rw [add_ofNat_zero, add_ofNat_zero, ← hGk, ← e3F] at this; exact this e.symm
        show memStore8 MC _ _ _ = _
        rw [memStore8_ne hne, fC (G + BitVec.ofNat 32 k) (by
            rw [RG, hGk]
            have := sep_offsets R (c := 0) (n := 0x390) (d := 0x390 + k) (k := 1) (Or.inl (by omega)) (by omega)
              (by omega)
            rwa [add_ofNat_zero] at this)
            (by
              rw [e80, hGk]
              exact (E.sSF.sub (c := 0x80) (l := 0x50) (by omega)).subR (c := 0x390 + k) (l := 1) (by omega)),
          mem21, mB (G + BitVec.ofNat 32 k) (by
            rw [hGF, hGk]; exact sep_offsets R (c := 0x380) (n := 16) (d := 0x390 + k) (k := 1) (Or.inl (by omega))
              (by omega) (by omega)),
          copyBytes_sep (by
            rw [hGk]; exact (E.sSF.sub (c := pos) (l := rem) (by omega)).subR (c := 0x390 + k) (l := 1) (by omega))
            (Nat.le_refl rem)]
      let blk := memBytes MB (S + BitVec.ofNat 32 (128 * 0)) 128
      have hblk : tailBytes5 msg ++ data.take rem = blk := by
        show _ = memBytes MB (S + BitVec.ofNat 32 (128 * 0)) 128
        rw [Nat.mul_zero, add_ofNat_zero, show memBytes MB S 128 = memBytes MB S (pos + rem) by
          rw [show pos + rem = 128 by omega], memBytes_split, ← H.buf, memBytes_take _ _ hrem]
        have b1 : memBytes MB S pos = memBytes M0 S pos := memBytes_congr fun i hi => by
          rw [mB _ (by rw [hGF]; exact ((E.sSF.sub (c := i) (l := 1) (by omega)).subR (c := 0x380) (l := 16)
              (by omega)).symm),
            copyBytes_sep (sep_offsets S (c := pos) (n := rem) (d := i) (k := 1) (Or.inr (by omega)) (by omega)
              (by omega)) (Nat.le_refl rem), out2 _ (SG i (by omega))]
        have b2 : memBytes MB (S + BitVec.ofNat 32 pos) rem = memBytes M0 D rem := by
          unfold memBytes
          apply List.map_congr_left
          intro i hi
          have hi := List.mem_range.mp hi
          show (MB (S + BitVec.ofNat 32 pos + BitVec.ofNat 32 i)).toNat = (M0 (D + BitVec.ofNat 32 i)).toNat
          rw [mB _ (by rw [hGF, add_ofNat_assoc]; exact ((E.sSF.sub (c := pos + i) (l := 1) (by omega)).subR
              (c := 0x380) (l := 16) (by omega)).symm), copyBytes_in hi (by omega),
            hM2 _ (E.sDF.sub (c := i) (l := 1) (by omega)).symm (E.sDS.sub (c := i) (l := 1) (by omega)).symm]
        rw [b1, b2]
      have hdrop : data.drop rem = memBytes M0 (D + BitVec.ofNat 32 rem) (n - rem) := memBytes_drop _ _ hrem
      obtain ⟨hf1, hf2⟩ := fullBlocks5_fill msg data (r := rem) (by rw [tailBytes5_length]; omega)
        (by rw [hdata]; exact hrem)
      rw [hdata, hdrop, hblk, List.append_cons] at hf1
      rw [hdata, hdrop] at hf2
      have wB : (s5Hv MB (S + 0x80)).toList = (fullBlocks5 msg).foldl Sha512.compress Sha512.h0 := by
        rw [← H.hash, s5Hv_congr (M := M0) (M' := MB) fun i hi => by
          rw [e80, add_ofNat_assoc]; exact hiB _ (by omega) (by omega)]
      have wx : (s5Hv Mx (S + 0x80)).toList = (s5Hv MC (S + 0x80)).toList := by
        rw [s5Hv_congr (M := MC) (M' := Mx) fun i hi => by
          rw [e80, add_ofNat_assoc]; exact nx _ (by omega) (by omega)]
      exact J n24 Mx (reg n24) (D + BitVec.ofNat 32 rem) (n - rem) (fullBlocks5 msg ++ [blk])
        (c7.trans (.cons d8 (.cons d9 (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15
          (c16.trans (.cons d17 (.cons d18 (.cons d19 (.cons d20 (.cons d21 (c22.trans
          (.cons d23 (.single d24)))))))))))))))))) u24.self hMx hsl (by omega)
        (by rw [show n - (n - rem) = rem by omega]) a1_24 s1_24 s2_24 s4_24 sp24
        (fun r q1 q2 q5 q6 q7 h8 h9 q10 q11 q12 q13 q14 q15 q16 q17 h18 h19 h20 q28 q29 q30 q31 => by
          rw [K24 r q11, K13_22 r q1 q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 q2,
            K9_13 r h18 h19 h9 q10, K27 r q2 q5 h9 h20 h8 q12])
        (by rw [wx, w22, mem21, wB, List.foldl_append]; rfl)
        (by
          rw [List.length_append, fullBlocks5_length, List.length_singleton,
            show S + (0xC0 : Word) = S + BitVec.ofNat 32 0xC0 from rfl, ldx 0xC0 (by omega) (by omega), ← eC0,
            lo22, lo21, BitVec.ofNat_add_ofNat])
        (by
          rw [show S + (0xC4 : Word) = S + BitVec.ofNat 32 0xC4 from rfl, ldx 0xC4 (by omega) (by omega),
            show S + BitVec.ofNat 32 0xC4 = S + 0x80 + 0x44 by rw [BitVec.add_assoc]; rfl, hi22, mem21,
            show S + 0x80 + (0x44 : Word) = S + BitVec.ofNat 32 0xC4 by rw [BitVec.add_assoc]; rfl,
            ldB 0xC4 (by omega) (by omega)]
          exact H.hi)
        (by
          rw [show S + (0xC8 : Word) = S + BitVec.ofNat 32 0xC8 from rfl, ldx 0xC8 (by omega) (by omega),
            show S + BitVec.ofNat 32 0xC8 = S + 0x80 + 0x48 by rw [BitVec.add_assoc]; rfl, hi22b, mem21,
            show S + 0x80 + (0x48 : Word) = S + BitVec.ofNat 32 0xC8 by rw [BitVec.add_assoc]; rfl,
            ldB 0xC8 (by omega) (by omega)]
          exact H.hi2)
        (by
          rw [show S + (0xCC : Word) = S + BitVec.ofNat 32 0xCC from rfl, ldx 0xCC (by omega) (by omega),
            show S + BitVec.ofNat 32 0xCC = S + 0x80 + 0x4C by rw [BitVec.add_assoc]; rfl, hi22c, mem21,
            show S + 0x80 + (0x4C : Word) = S + BitVec.ofNat 32 0xCC by rw [BitVec.add_assoc]; rfl,
            ldB 0xCC (by omega) (by omega)]
          exact H.hi3)
        hf1 hf2

end C3.RV32.S5U
