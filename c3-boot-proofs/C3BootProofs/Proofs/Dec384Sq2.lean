import C3BootProofs.Proofs.Dec384Sq

/-!
# P-384 point decompression: one inlined Montgomery squaring

`dq_sq` runs one pass of `square_repeat_montgomery_form`'s loop in
`decompress`, from 0x34E to the loop's head at 0x348: it squares the
working value at `S + 0x98C` in Montgomery form, through the copy at
`S + 0x9BC`, the loop of `Dec384Sq.lean`, and the final subtraction.
-/

namespace C3.RV32.Dq

open C3.Image

set_option maxRecDepth 20000

abbrev MCS : Word := BitVec.ofNat 32 memcpyStubAddress
abbrev MSET : Word := BitVec.ofNat 32 memsetAddress
abbrev SEL : Word := BitVec.ofNat 32 uintSelect12Address
abbrev MM : Word := BitVec.ofNat 32 mulMont12Address

/-- The code `decompress` runs and calls, at its addresses in the image. -/
structure DqCode (M : Word → BitVec 8) : Prop where
  self : CodeIn M DP p384DecompressCode
  stub : CodeIn M MCS memcpyStubCode
  body : CodeIn M (MCS + 8) memcpyBodyCode
  mset : CodeIn M MSET memsetCode
  bsub : CodeIn M BSUB borrowingSubCode
  sel : CodeIn M SEL uintSelect12Code
  mm : CodeIn M MM mulMont12Code

theorem codeHi {M M' : Word → BitVec 8} {b : Word} {code : List Nat} (hc : CodeIn M b code)
    (hb : 0x40000000 ≤ b.toNat) (hl : b.toNat + code.length ≤ 2 ^ 32)
    (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) : CodeIn M' b code := fun i hi => by
  rw [h _ (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]; exact hc i hi

theorem DqCode.hi {M M' : Word → BitVec 8} (C : DqCode M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    DqCode M' :=
  ⟨codeHi C.self (by decide) (by decide) h, codeHi C.stub (by decide) (by decide) h,
    codeHi C.body (by decide) (by decide) h, codeHi C.mset (by decide) (by decide) h,
    codeHi C.bsub (by decide) (by decide) h, codeHi C.sel (by decide) (by decide) h,
    codeHi C.mm (by decide) (by decide) h⟩

/-- `decompress`'s frame at `S`, with room below for its callees, all below
the code. -/
structure DqFrame (S : Word) : Prop where
  al : S.toNat % 16 = 0
  lo : 0x100 ≤ S.toNat
  hi : S.toNat + 0xA50 ≤ 0x40000000

theorem DqFrame.at {S : Word} (F : DqFrame S) (c : Nat) (hc : c ≤ 0xA50) : (S + BitVec.ofNat 32 c).toNat = S.toNat + c := by
  have := F.hi; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem DqFrame.below {S : Word} (F : DqFrame S) (c : Nat) (hc : 0 < c) (hc' : c ≤ 0x100) :
    (S + BitVec.ofNat 32 (2 ^ 32 - c)).toNat = S.toNat - c := by
  have := F.lo; have := S.isLt; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- A frame region is apart from code above `0x40000000`. -/
theorem DqFrame.sepHi {S : Word} (F : DqFrame S) {c n : Nat} (h : c + n ≤ 0xA50) {b : Word} {len : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hl : b.toNat + len ≤ 2 ^ 32) : Sep (S + BitVec.ofNat 32 c) n b len :=
  sep_of_le (by rw [F.at c (by omega)]; have := F.hi; omega) hl

theorem DqFrame.sepHiB {S : Word} (F : DqFrame S) {c : Nat} (hc : 0 < c) (hc' : c ≤ 0x100) {b : Word} {len : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hl : b.toNat + len ≤ 2 ^ 32) : Sep (S + BitVec.ofNat 32 (2 ^ 32 - c)) c b len :=
  sep_of_le (by rw [F.below c hc hc']; have := F.hi; omega) hl

theorem DqFrame.hiOut {S : Word} (F : DqFrame S) {c n : Nat} (h : c + n ≤ 0xA50) {x : Word} (hx : 0x40000000 ≤ x.toNat) :
    Sep (S + BitVec.ofNat 32 c) n x 1 := F.sepHi h hx (by have := x.isLt; omega)

theorem DqFrame.hiOutB {S : Word} (F : DqFrame S) {c : Nat} (hc : 0 < c) (hc' : c ≤ 0x100) {x : Word}
    (hx : 0x40000000 ≤ x.toNat) : Sep (S + BitVec.ofNat 32 (2 ^ 32 - c)) c x 1 :=
  F.sepHiB hc hc' hx (by have := x.isLt; omega)

theorem cp_at {M : Word → BitVec 8} {dst src : Word} {N i : Nat} (hi : i < N) (hN : N < 2 ^ 32) :
    copyBytes M dst src N (dst + BitVec.ofNat 32 i) = M (src + BitVec.ofNat 32 i) := by
  unfold copyBytes
  rw [BitVec.add_comm dst, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ite_eq_left hi]

theorem fill_at {M : Word → BitVec 8} {dst : Word} {v : BitVec 8} {N i : Nat} (hi : i < N) (hN : N < 2 ^ 32) :
    fillBytes M dst v N (dst + BitVec.ofNat 32 i) = v := by
  unfold fillBytes
  rw [BitVec.add_comm dst, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ite_eq_left hi]

theorem ld_ofNat (M : Word → BitVec 8) (a : Word) :
    memLoad32 M a = M (a + BitVec.ofNat 32 3) ++ M (a + BitVec.ofNat 32 2) ++ M (a + BitVec.ofNat 32 1) ++
      M (a + BitVec.ofNat 32 0) := by
  unfold memLoad32; rw [add_ofNat_zero]; rfl

theorem cp_word {M : Word → BitVec 8} {dst src : Word} {N k : Nat} (hk : k + 4 ≤ N) (hN : N < 2 ^ 32) :
    memLoad32 (copyBytes M dst src N) (dst + BitVec.ofNat 32 k) = memLoad32 M (src + BitVec.ofNat 32 k) := by
  rw [ld_ofNat, ld_ofNat, add_ofNat_assoc dst k 3, add_ofNat_assoc dst k 2, add_ofNat_assoc dst k 1,
    add_ofNat_assoc dst k 0, add_ofNat_assoc src k 3, add_ofNat_assoc src k 2, add_ofNat_assoc src k 1,
    add_ofNat_assoc src k 0, cp_at (by omega) hN, cp_at (by omega) hN, cp_at (by omega) hN, cp_at (by omega) hN]

theorem fill_word0 {M : Word → BitVec 8} {dst : Word} {N k : Nat} (hk : k + 4 ≤ N) (hN : N < 2 ^ 32) :
    memLoad32 (fillBytes M dst ((0 : Word).extractLsb' 0 8) N) (dst + BitVec.ofNat 32 k) = 0 := by
  rw [memLoad32_congr (M := fun _ => (0 : BitVec 8)) fun j hj => by
    rw [add_ofNat_assoc, fill_at (by omega) hN]; rfl]
  unfold memLoad32
  exact (by decide : ((0 : BitVec 8) ++ (0 : BitVec 8) ++ (0 : BitVec 8) ++ (0 : BitVec 8)) = (0 : Word))

/-- A call to `memcpy` from `decompress`, with `sp` at `S`. -/
theorem dq_memcpy {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o dst src S : Word}
    {N : Nat} (s : St Mx DP n off g) (C : DqCode Mx)
    (h1 : fetchRel p384DecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384DecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DP + BitVec.ofNat 32 off + imm + o = MCS) (he8 : (DP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = dst) (ha1 : g a1 = src) (ha2 : g a2 = BitVec.ofNat 32 N)
    (E : McEnv Mx (MCS + 8) dst src (S + 0xFFFFFFF0) N) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' (off + 8) (reg n') ∧
      (∀ x, Sep (S + 0xFFFFFFF0) 16 x 1 → n'.mem x = copyBytes Mx dst src N x) ∧
      ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
        r ≠ (7 : Fin 32) → r ≠ (28 : Fin 32) → r ≠ (29 : Fin 32) → r ≠ (30 : Fin 32) → r ≠ ra → reg n' r = g r := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  obtain ⟨n2, c2, pc2, sp2, a02, mem2, k2⟩ := memcpy_correct n1 MCS (DP + BitVec.ofNat 32 (off + 8)) dst src N
    (fun i hi => by rw [mem1]; exact C.stub i hi) (by decide) pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) (by rw [mem1, r1 sp (by decide), hsp]; exact E)
  rw [r1 sp (by decide), hsp, mem1] at mem2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, mem2,
    fun r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hra => ?_⟩
  by_cases hs : r = sp
  · subst hs; rw [sp2, r1 sp (by decide)]
  · rw [k2 r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hs, r1 r hra]

/-- A call to `memset` from `decompress`. -/
theorem dq_memset {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o dst b : Word}
    {N : Nat} (s : St Mx DP n off g) (C : DqCode Mx)
    (h1 : fetchRel p384DecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384DecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DP + BitVec.ofNat 32 off + imm + o = MSET) (he8 : (DP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : g a0 = dst) (ha1 : g a1 = b) (ha2 : g a2 = BitVec.ofNat 32 N)
    (hw : dst.toNat + N < 2 ^ 32) (hDC : Sep dst N MSET memsetCode.length) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' (off + 8) (reg n') ∧ n'.mem = fillBytes Mx dst (b.extractLsb' 0 8) N ∧
      ∀ r, r ≠ a0 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ ra → reg n' r = g r := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  obtain ⟨n2, c2, pc2, mem2, a02, k2⟩ := memset_correct n1 MSET (DP + BitVec.ofNat 32 (off + 8)) dst b N
    (fun i hi => by rw [mem1]; exact C.mset i hi) (by decide) pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) hw hDC
  rw [mem1] at mem2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, mem2,
    fun r h0 h2 h3 h4 h5 h6 hra => by rw [k2 r h2 h3 h4 h5 h6, r1 r hra]⟩

theorem spo (S : Word) (a b : Word) : aluEval .add (aluEval .add S a) b = S + (a + b) := BitVec.add_assoc S a b

theorem fill_word_out {M : Word → BitVec 8} {dst a : Word} {v : BitVec 8} {N : Nat} (h : Sep dst N a 4) :
    memLoad32 (fillBytes M dst v N) a = memLoad32 M a :=
  memLoad32_congr fun j hj => fillBytes_sep (h.subR (c := j) (l := 1) (by omega)) (Nat.le_refl N)

theorem cp_word_out {M : Word → BitVec 8} {dst src a : Word} {N : Nat} (h : Sep dst N a 4) :
    memLoad32 (copyBytes M dst src N) a = memLoad32 M a :=
  memLoad32_congr fun j hj => copyBytes_sep (h.subR (c := j) (l := 1) (by omega)) (Nat.le_refl N)

theorem st32_word_out {M : Word → BitVec 8} {b a v : Word} (h : Sep b 4 a 4) :
    memLoad32 (memStore32 M b v) a = memLoad32 M a := memLoad32_store32_sep h

theorem sepS (S : Word) {c n d k : Nat} (h : c + n ≤ d ∨ d + k ≤ c) (hc : c + n ≤ 2 ^ 32) (hd : d + k ≤ 2 ^ 32) :
    Sep (S + BitVec.ofNat 32 c) n (S + BitVec.ofNat 32 d) k := sep_offsets S h hc hd

def dqPre1 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x1BD, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x18D,
   .aluImm .add a2 x0 0x30]
def dqPre2 : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x18D, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0x0]
def dqPre3 : List BInstr :=
  [.aluImm .add (27 : Fin 32) x0 0x0, .aluImm .add (17 : Fin 32) x0 0x0, .lw a6 (25 : Fin 32) 0x30,
   .aluImm .add (5 : Fin 32) x0 0x0]

theorem dqPre1_end : blockEnd p384DecompressCode 0x350 dqPre1 = some 0x364 := by decide
theorem dqPre2_end : blockEnd p384DecompressCode 0x36C dqPre2 = some 0x37A := by decide
theorem dqPre3_end : blockEnd p384DecompressCode 0x382 dqPre3 = some 0x38C := by decide

/-- The registers the start of a squaring leaves alone. -/
def preKeep (q : Fin 32) : Bool := q.val ∉ [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 27, 28, 29, 30]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The start of a squaring**, from 0x34E to the loop at 0x390: save the
count, copy the working value to the operand at `S + 0x9BC`, and clear the
accumulator at `S + 0x98C`. -/
theorem dq_sq_pre {M : Word → BitVec 8} {S : Word} {n : Machine} {j : Nat} (C : DqCode M) (F : DqFrame S)
    (s : St M DP n 0x34E (reg n)) (rsp : reg n sp = S) (ra1 : reg n a1 = BitVec.ofNat 32 j)
    (r25 : reg n (25 : Fin 32) = S + BitVec.ofNat 32 0x98C) (r22 : reg n (22 : Fin 32) = 12) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' 0x390 (reg n') ∧ DqCode n'.mem ∧
      (∀ i, i < 12 → memLoad32 n'.mem (S + BitVec.ofNat 32 (0x9BC + 4 * i)) =
        memLoad32 M (S + BitVec.ofNat 32 (0x98C + 4 * i))) ∧
      (∀ i, i < 12 → memLoad32 n'.mem (S + BitVec.ofNat 32 (0x98C + 4 * i)) = 0) ∧
      memLoad32 n'.mem (S + BitVec.ofNat 32 0x3C) = BitVec.ofNat 32 j ∧
      (∀ x, Sep (S + BitVec.ofNat 32 (2 ^ 32 - 16)) 16 x 1 → Sep (S + BitVec.ofNat 32 0x3C) 4 x 1 →
        Sep (S + BitVec.ofNat 32 0x98C) 0x60 x 1 → n'.mem x = M x) ∧
      reg n' (27 : Fin 32) = 0 ∧ reg n' (17 : Fin 32) = 0 ∧ reg n' a6 = memLoad32 M (S + BitVec.ofNat 32 0x98C) ∧
      reg n' (5 : Fin 32) = 0 ∧ ∀ q, preKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  -- save the count
  obtain ⟨n1, d1, u1⟩ := s.sw C.self dp_at_34e (off' := 0x350) (by decide)
    (by rw [rsp]; show (S + BitVec.ofNat 32 0x3C).toNat % 4 = 0; rw [F.at 0x3C (by decide)]; omega)
  rw [rsp, ra1] at u1
  have u1' : St (memStore32 M (S + BitVec.ofNat 32 0x3C) (BitVec.ofNat 32 j)) DP n1 0x350 (reg n1) := u1.self
  have h1hi : ∀ x : Word, 0x40000000 ≤ x.toNat → memStore32 M (S + BitVec.ofNat 32 0x3C) (BitVec.ofNat 32 j) x = M x :=
    fun x hx => memStore32_get_sep (F.hiOut (c := 0x3C) (n := 4) (by decide) hx)
  have C1 := C.hi h1hi
  obtain ⟨M1, hM1⟩ : ∃ M1, memStore32 M (S + BitVec.ofNat 32 0x3C) (BitVec.ofNat 32 j) = M1 := ⟨_, rfl⟩
  rw [hM1] at u1' h1hi C1
  -- copy the working value
  obtain ⟨n2, c2, u2⟩ := u1'.block dqPre1 C1.self dqPre1_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r2 : ∀ q, reg n2 q = (runBlock dqPre1 (M1, reg n1)).2 q := fun q => by rw [u2.regs]
  have sp1 : reg n1 sp = S := by rw [u1.regs, rsp]
  have k2 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → reg n2 q = reg n q := fun q h0 h1 h2 => by
    rw [r2, runBlock_reg _ _ _ q u1'.zero (by simp only [dqPre1]; revert h0 h1 h2; revert q; decide), u1.regs]
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have fA : (S + 0xFFFFFFF0).toNat % 4 = 0 := by rw [hb16]; omega
  have fW : (S + 0xFFFFFFF0).toNat + 16 ≤ 2 ^ 32 := by rw [hb16]; omega
  have dW : (S + BitVec.ofNat 32 0x9BC).toNat + 48 < 2 ^ 32 := by rw [F.at 0x9BC (by decide)]; omega
  have sW : (S + BitVec.ofNat 32 0x98C).toNat + 48 < 2 ^ 32 := by rw [F.at 0x98C (by decide)]; omega
  have hFC : Sep (S + 0xFFFFFFF0) 16 (MCS + 8) memcpyBodyCode.length :=
    sep_of_le (by rw [hb16, show (MCS + 8).toNat = 0x403b4856 from rfl]; omega) (by decide)
  have hdF : Sep (S + BitVec.ofNat 32 0x9BC) 48 (S + 0xFFFFFFF0) 16 :=
    (sep_of_le (by rw [hb16, F.at 0x9BC (by decide)]; omega) (by omega)).symm
  have hsF : Sep (S + BitVec.ofNat 32 0x98C) 48 (S + 0xFFFFFFF0) 16 :=
    (sep_of_le (by rw [hb16, F.at 0x98C (by decide)]; omega) (by omega)).symm
  have below16 : ∀ c, c + 4 ≤ 0xA50 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 c) 4 := fun c hc =>
    sep_of_le (by rw [hb16, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)
  obtain ⟨n3, c3, u3, fr3, k3⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x9BC) (src := S + BitVec.ofNat 32 0x98C)
    (S := S) (N := 48) (⟨u2.pc, u2.mem, fun _ => rfl⟩ : St M1 DP n2 0x364 (reg n2)) C1 dp_at_364 dp_at_368
    (by decide) (by decide)
    (by rw [k2 sp (by decide) (by decide) (by decide)]; exact rsp)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, dqPre1, upd, ↓reduceIte]; rw [sp1, spo]; try rfl)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, dqPre1, upd, ↓reduceIte]; rw [sp1, spo]; try rfl)
    (by rw [r2]; simp +decide only [runBlock, BInstr.run, dqPre1, upd, ↓reduceIte]; (try rw [u1'.zero]); try rfl)
    ⟨C1.body, F.sepHi (by decide) (by decide) (by decide), hFC, hdF, hsF,
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, dW, sW⟩
  have h3hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n3.mem x = M x := fun x hx => by
    rw [fr3 x (sep_of_le (by rw [hb16]; omega) (by have := x.isLt; omega)),
      copyBytes_sep (F.hiOut (c := 0x9BC) (n := 48) (by decide) hx) (Nat.le_refl _), h1hi x hx]
  have C3 := C.hi h3hi
  have k3' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg n3 q = reg n q :=
    fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr => by
      rw [k3 q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr, k2 q h0 h1 h2]
  -- clear the accumulator
  obtain ⟨n4, c4, u4⟩ := u3.block dqPre2 C3.self dqPre2_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r4 : ∀ q, reg n4 q = (runBlock dqPre2 (n3.mem, reg n3)).2 q := fun q => by rw [u4.regs]
  have sp3 : reg n3 sp = S := by
    rw [k3' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact rsp
  obtain ⟨n5, c5, u5, mem5, k5⟩ := dq_memset (dst := S + BitVec.ofNat 32 0x98C) (b := 0) (N := 48)
    (⟨u4.pc, u4.mem, fun _ => rfl⟩ : St n3.mem DP n4 0x37A (reg n4)) C3 dp_at_37a dp_at_37e (by decide) (by decide)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, dqPre2, upd, ↓reduceIte]; rw [sp3, spo]; try rfl)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, dqPre2, upd, ↓reduceIte]; (try rw [u3.zero]); try rfl)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, dqPre2, upd, ↓reduceIte]; (try rw [u3.zero]); try rfl)
    (by rw [F.at 0x98C (by decide)]; omega) (F.sepHi (by decide) (by decide) (by decide))
  have h5hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n5.mem x = M x := fun x hx => by
    rw [mem5, fillBytes_sep (F.hiOut (c := 0x98C) (n := 48) (by decide) hx) (Nat.le_refl _), h3hi x hx]
  have C5 := C.hi h5hi
  have k5' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg n5 q = reg n q :=
    fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr => by
      have hb : q ∉ dqPre2.filterMap BInstr.dst := by simp only [dqPre2]; revert h0 h1 h2; revert q; decide
      rw [k5 q h0 h2 h3 h4 h5 h6 hr, r4, runBlock_reg _ _ _ q u3.zero hb, k3' q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr]
  -- the operand copy and the cleared accumulator, read word by word
  have wcopy : ∀ i, i < 12 → memLoad32 n5.mem (S + BitVec.ofNat 32 (0x9BC + 4 * i)) =
      memLoad32 M (S + BitVec.ofNat 32 (0x98C + 4 * i)) := fun i hi => by
    rw [mem5, fill_word_out (sepS S (c := 0x98C) (n := 48) (d := 0x9BC + 4 * i) (k := 4) (.inl (by omega)) (by decide)
        (by omega)),
      load_frame fr3 (below16 _ (by omega)), ← add_ofNat_assoc S 0x9BC (4 * i), cp_word (by omega) (by decide),
      add_ofNat_assoc, ← hM1,
      st32_word_out (sepS S (c := 0x3C) (n := 4) (d := 0x98C + 4 * i) (k := 4) (.inl (by omega)) (by decide) (by omega))]
  have wzero : ∀ i, i < 12 → memLoad32 n5.mem (S + BitVec.ofNat 32 (0x98C + 4 * i)) = 0 := fun i hi => by
    rw [mem5, ← add_ofNat_assoc S 0x98C (4 * i)]; exact fill_word0 (by omega) (by decide)
  have r25' : reg n5 (25 : Fin 32) = S + BitVec.ofNat 32 0x98C := by
    rw [k5' 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact r25
  obtain ⟨n6, c6, u6⟩ := u5.block dqPre3 C5.self dqPre3_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, dqPre3]
    simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [r25']
    show (S + BitVec.ofNat 32 0x98C + BitVec.ofNat 32 0x30).toNat % 4 = 0
    rw [add_ofNat_assoc, F.at _ (by decide)]
    omega)
  have r6 : ∀ q, reg n6 q = (runBlock dqPre3 (n5.mem, reg n5)).2 q := fun q => by rw [u6.regs]
  have t6 : St n5.mem DP n6 0x38C (reg n6) := ⟨u6.pc, u6.mem, fun _ => rfl⟩
  have e22 : reg n6 (22 : Fin 32) = 12 := by
    rw [r6, runBlock_reg _ _ _ 22 u5.zero (by decide), k5' 22 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact r22
  obtain ⟨n7, d7, u7⟩ := t6.notTaken C5.self 0x390 dp_at_38c (by decide) (by
    show (reg n6 (22 : Fin 32) == reg n6 x0) = false; rw [e22, t6.zero]; rfl)
  refine ⟨n7, .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (.single d7)))))),
    ⟨u7.pc, rfl, fun _ => rfl⟩, by rw [u7.mem]; exact C5, fun i hi => by rw [u7.mem]; exact wcopy i hi,
    fun i hi => by rw [u7.mem]; exact wzero i hi, ?_, fun x hx hj hw => ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [u7.mem, mem5, fill_word_out (sepS S (c := 0x98C) (n := 48) (d := 0x3C) (k := 4) (.inr (by decide)) (by decide)
        (by decide)),
      load_frame fr3 (below16 0x3C (by decide)),
      cp_word_out (sepS S (c := 0x9BC) (n := 48) (d := 0x3C) (k := 4) (.inr (by decide)) (by decide) (by decide)),
      ← hM1, memLoad32_store32_same]
  · have e0 : S + BitVec.ofNat 32 0x98C + BitVec.ofNat 32 0 = S + BitVec.ofNat 32 0x98C := add_ofNat_zero _
    rw [u7.mem, mem5, fillBytes_sep (by have := hw.sub (c := 0) (l := 48) (by decide); rwa [e0] at this) (Nat.le_refl _),
      fr3 x hx, copyBytes_sep (by have := hw.sub (c := 0x30) (l := 48) (by decide); rwa [add_ofNat_assoc] at this)
        (Nat.le_refl _), ← hM1]
    exact memStore32_get_sep hj
  · rw [u7.regs, r6]; simp +decide only [runBlock, BInstr.run, dqPre3, upd, ↓reduceIte]; (try rw [u5.zero]); try rfl
  · rw [u7.regs, r6]; simp +decide only [runBlock, BInstr.run, dqPre3, upd, ↓reduceIte]; (try rw [u5.zero]); try rfl
  · rw [u7.regs, r6]; simp +decide only [runBlock, BInstr.run, dqPre3, upd, ↓reduceIte]
    rw [r25']
    have := wcopy 0 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero] at this
    show memLoad32 n5.mem (S + BitVec.ofNat 32 0x98C + BitVec.ofNat 32 0x30) = _
    rw [add_ofNat_assoc]; exact this
  · rw [u7.regs, r6]; simp +decide only [runBlock, BInstr.run, dqPre3, upd, ↓reduceIte]; (try rw [u5.zero]); try rfl
  · have h0 : q ≠ a0 := pkeep_ne (r := a0) hq rfl
    have hb : q ∉ dqPre3.filterMap BInstr.dst := by simp only [dqPre3]; revert hq; revert q; decide
    rw [u7.regs, r6, runBlock_reg _ _ _ q u5.zero hb,
      k5' q h0 (pkeep_ne (r := a1) hq rfl) (pkeep_ne (r := a2) hq rfl) (pkeep_ne (r := a3) hq rfl)
        (pkeep_ne (r := a4) hq rfl) (pkeep_ne (r := a5) hq rfl) (pkeep_ne (r := a6) hq rfl)
        (pkeep_ne (r := a7) hq rfl) (pkeep_ne (r := t0) hq rfl) (pkeep_ne (r := t1) hq rfl)
        (pkeep_ne (r := 7) hq rfl) (pkeep_ne (r := 28) hq rfl) (pkeep_ne (r := 29) hq rfl)
        (pkeep_ne (r := 30) hq rfl) (pkeep_ne (r := ra) hq rfl)]

theorem sel_mset : SEL + 0x197E = MSET := by decide
theorem sel_stub : SEL + 0x19E6 = MCS := by decide
theorem sel_body : SEL + 0x19EE = MCS + 8 := by decide

/-- A call to `Uint<12>::select` from `decompress`, with `sp` at `S`: the 12
words at `out` become `bp`'s when the choice is 1 and `ap`'s when it is 0. -/
theorem dq_sel {Mx : Word → BitVec 8} {n : Machine} {off : Nat} {g : Fin 32 → Word} {imm o out ap bp c S : Word}
    (s : St Mx DP n off g) (C : DqCode Mx) (F : DqFrame S)
    (h1 : fetchRel p384DecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384DecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DP + BitVec.ofNat 32 off + imm + o = SEL) (he8 : (DP + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : g sp = S) (ha0 : g a0 = out) (ha1 : g a1 = ap) (ha2 : g a2 = bp) (ha3 : g a3 = c) (hcc : c = 0 ∨ c = 1)
    {co ca cb : Nat} (hco : co + 48 ≤ 0xA50) (hca : ca + 48 ≤ 0xA50) (hcb : cb + 48 ≤ 0xA50)
    (eo : out = S + BitVec.ofNat 32 co) (ea : ap = S + BitVec.ofNat 32 ca) (eb : bp = S + BitVec.ofNat 32 cb)
    (aco : co % 4 = 0) (aca : ca % 4 = 0) (acb : cb % 4 = 0) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' (off + 8) (reg n') ∧
      (∀ i, i < 12 → memLoad32 n'.mem (out + BitVec.ofNat 32 (4 * i)) =
        if c = 1 then memLoad32 Mx (bp + BitVec.ofNat 32 (4 * i)) else memLoad32 Mx (ap + BitVec.ofNat 32 (4 * i))) ∧
      (∀ x, Sep (S + 0xFFFFFFB0) 0x50 x 1 → Sep out 48 x 1 → n'.mem x = Mx x) ∧
      ∀ r, selKeep r = true → r ≠ ra → reg n' r = g r := by
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = g r := fun r h => by rw [regs1]; exact updz s.zero h
  have sp1 : reg n1 sp = S := by rw [r1 sp (by decide)]; exact hsp
  have hb50 : (S + 0xFFFFFFB0).toNat = S.toNat - 0x50 := F.below 0x50 (by decide) (by decide)
  have hSa := F.al; have hSl := F.lo; have hSh := F.hi
  have frS : ∀ (cx : Nat), cx + 48 ≤ 0xA50 → Sep (S + BitVec.ofNat 32 cx) 48 (S + 0xFFFFFFB0) 0x50 := fun cx h =>
    (sep_of_le (by rw [hb50, F.at cx (by omega)]; omega) (by rw [F.at cx (by omega)]; omega)).symm
  have frC : ∀ (b : Word) (len : Nat), 0x40000000 ≤ b.toNat → b.toNat + len ≤ 2 ^ 32 → Sep (S + 0xFFFFFFB0) 0x50 b len :=
    fun b len hb hl => sep_of_le (by rw [hb50]; omega) hl
  have E : SelEnv n1.mem SEL (reg n1 sp) out ap bp := by
    rw [sp1, mem1]
    refine ⟨by decide, C.sel, by rw [sel_mset]; exact C.mset, by rw [sel_stub]; exact C.stub,
      by rw [sel_body]; exact C.body, by omega, by omega, ?_, ?_, ?_, ?_,
      frC _ _ (by decide) (by decide), frC _ _ (by rw [sel_mset]; decide) (by rw [sel_mset]; decide),
      frC _ _ (by rw [sel_stub]; decide) (by rw [sel_stub]; decide), frC _ _ (by rw [sel_body]; decide)
        (by rw [sel_body]; decide), ?_, ?_, ?_, ?_, ?_⟩
    · rw [eo, F.at co (by omega)]; omega
    · rw [ea, F.at ca (by omega)]; omega
    · rw [eb, F.at cb (by omega)]; omega
    · rw [eo, F.at co (by omega)]; omega
    · rw [eo]; exact frS co hco
    · rw [eo]; exact F.sepHi hco (by decide) (by decide)
    · rw [eo, sel_body]; exact F.sepHi hco (by decide) (by decide)
    · rw [ea]; exact frS ca hca
    · rw [eb]; exact frS cb hcb
  obtain ⟨n2, c2, pc2, sp2, vals, fr2, k2⟩ := uintSelect12_correct n1 E pc1 (by rw [r1 a0 (by decide)]; exact ha0)
    (by rw [r1 a1 (by decide)]; exact ha1) (by rw [r1 a2 (by decide)]; exact ha2) (by rw [r1 a3 (by decide)]; exact ha3)
    hcc (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1] at vals fr2
  rw [sp1] at fr2
  exact ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, vals, fr2, fun r hr hra => by rw [k2 r hr, r1 r hra]⟩

def dqP1 : List BInstr :=
  [.aluImm .add a0 sp 0x62C, .aluImm .add a2 x0 0x30, .aluImm .add a1 x0 0x0, .aluImm .add (24 : Fin 32) sp 0x62C]
def dqP2 : List BInstr :=
  [.aluImm .add (20 : Fin 32) x0 0x0, .aluImm .add (8 : Fin 32) sp 0x7FF, .aluImm .add (8 : Fin 32) (8 : Fin 32) 0x18D,
   .aluImm .add (9 : Fin 32) x0 0xC, .aluImm .add (18 : Fin 32) sp 0x134]
def dqP3 : List BInstr := [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x1ED, .aluImm .add a1 sp 0x62C, .aluImm .add a2 x0 0x30]
def dqP4 : List BInstr :=
  [.sw sp (27 : Fin 32) 0x62C, .aluImm .add a1 sp 0x62C, .lw a0 sp 0x62C, .aluImm .sltu a0 a0 0x1,
   .alu .and (24 : Fin 32) a0 (20 : Fin 32), .sb sp (24 : Fin 32) 0x62C, .lbu a0 sp 0x62C, .aluImm .add a0 a0 0xFFFFFFFF,
   .alu .and a2 (20 : Fin 32) a0, .alu .add a0 x0 (27 : Fin 32), .aluImm .add a1 x0 0x0]
def dqP5 : List BInstr :=
  [.aluImm .add a0 sp 0x62C, .aluImm .add a1 sp 0x7FF, .aluImm .add a1 a1 0x1ED, .aluImm .add a2 sp 0x7FF,
   .aluImm .add a2 a2 0x18D, .alu .add a3 x0 (24 : Fin 32)]
def dqP6 : List BInstr := [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x18D, .aluImm .add a1 sp 0x62C, .aluImm .add a2 x0 0x30]
def dqP7 : List BInstr :=
  [.lw a1 sp 0x3C, .aluImm .add a1 a1 0x1, .aluImm .add (18 : Fin 32) sp 0x7FF, .aluImm .add (18 : Fin 32) (18 : Fin 32) 0x1C1]

theorem dqP1_end : blockEnd p384DecompressCode 0x43C dqP1 = some 0x44A := by decide
theorem dqP2_end : blockEnd p384DecompressCode 0x452 dqP2 = some 0x462 := by decide
theorem dqP3_end : blockEnd p384DecompressCode 0x484 dqP3 = some 0x494 := by decide
theorem dqP4_end : blockEnd p384DecompressCode 0x49C dqP4 = some 0x4C2 := by decide
theorem dqP5_end : blockEnd p384DecompressCode 0x4CA dqP5 = some 0x4E0 := by decide
theorem dqP6_end : blockEnd p384DecompressCode 0x4E8 dqP6 = some 0x4F8 := by decide
theorem dqP7_end : blockEnd p384DecompressCode 0x500 dqP7 = some 0x50C := by decide

theorem byte01 (c : Word) (h : c = 0 ∨ c = 1) : (c.extractLsb' 0 8).zeroExtend 32 = c := by
  rcases h with rfl | rfl <;> decide

/-- The registers the end of a squaring leaves alone. -/
def postKeep (q : Fin 32) : Bool :=
  q.val ∉ [1, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 24, 28, 29, 30, 31]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The end of a squaring**, from 0x43C to the loop's head at 0x348: the
conditional subtraction of the modulus, which leaves at `S + 0x98C` the
accumulator when the top carry `s11` is zero and the subtraction borrowed,
and the difference otherwise. -/
theorem dq_sq_post {M : Word → BitVec 8} {S : Word} {n : Machine} (C : DqCode M) (F : DqFrame S)
    (s : St M DP n 0x43C (reg n)) (rsp : reg n sp = S) :
    ∃ (n' : Machine) (Dv : Nat) (b : Word), Steps n n' ∧ St n'.mem DP n' 0x348 (reg n') ∧ DqCode n'.mem ∧
      (b = 0 ∨ b = 0xFFFFFFFF) ∧ Dv < 2 ^ 384 ∧
      accV M (S + BitVec.ofNat 32 0x98C) 12 + 2 ^ 384 * maskBit b = accV M (S + BitVec.ofNat 32 0x134) 12 + Dv ∧
      accV n'.mem (S + BitVec.ofNat 32 0x98C) 12 =
        (if (reg n (27 : Fin 32)).toNat = 0 ∧ maskBit b = 1 then accV M (S + BitVec.ofNat 32 0x98C) 12 else Dv) ∧
      reg n' a1 = memLoad32 M (S + BitVec.ofNat 32 0x3C) + 1 ∧ reg n' (18 : Fin 32) = S + BitVec.ofNat 32 0x9C0 ∧
      (∀ x, Sep (S + 0xFFFFFFB0) 0x50 x 1 → Sep (S + BitVec.ofNat 32 0x62C) 48 x 1 →
        Sep (S + BitVec.ofNat 32 0x98C) 48 x 1 → Sep (S + BitVec.ofNat 32 0x9EC) 48 x 1 → n'.mem x = M x) ∧
      ∀ q, postKeep q = true → reg n' q = reg n q := by
  have hz := s.zero
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  have hb4 : (S + 0xFFFFFFFC).toNat = S.toNat - 4 := F.below 4 (by decide) (by decide)
  have hb16 : (S + 0xFFFFFFF0).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have hb50 : (S + 0xFFFFFFB0).toNat = S.toNat - 0x50 := F.below 0x50 (by decide) (by decide)
  have lowS : ∀ (c : Nat) (B : Word) (k : Nat), 0 < k → k ≤ 0x100 → B.toNat = S.toNat - k → ∀ d l, d + l ≤ 0xA50 →
      Sep B k (S + BitVec.ofNat 32 d) l := fun c B k hk hk' hB d l hd =>
    sep_of_le (by rw [hB, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have hiB : ∀ (B : Word) (k : Nat), B.toNat + k ≤ S.toNat → ∀ x : Word, 0x40000000 ≤ x.toNat → Sep B k x 1 :=
    fun B k h x hx => sep_of_le (by omega) (by have := x.isLt; omega)
  -- clear the buffer at S + 0x62C
  obtain ⟨n1, c1, u1⟩ := s.block dqP1 C.self dqP1_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r1 : ∀ q, reg n1 q = (runBlock dqP1 (M, reg n)).2 q := fun q => by rw [u1.regs]
  obtain ⟨n2, c2, u2, mem2, k2⟩ := dq_memset (dst := S + BitVec.ofNat 32 0x62C) (b := 0) (N := 48)
    (⟨u1.pc, u1.mem, fun _ => rfl⟩ : St M DP n1 0x44A (reg n1)) C dp_at_44a dp_at_44e (by decide) (by decide)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqP1, upd, ↓reduceIte]; rw [rsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqP1, upd, ↓reduceIte]; (try rw [hz]); try rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, dqP1, upd, ↓reduceIte]; (try rw [hz]); try rfl)
    (by rw [F.at 0x62C (by decide)]; omega) (F.sepHi (by decide) (by decide) (by decide))
  obtain ⟨M2, hM2⟩ : ∃ M2, fillBytes M (S + BitVec.ofNat 32 0x62C) ((0 : Word).extractLsb' 0 8) 48 = M2 := ⟨_, rfl⟩
  rw [hM2] at mem2
  have h2hi : ∀ x : Word, 0x40000000 ≤ x.toNat → M2 x = M x := fun x hx => by
    rw [← hM2, fillBytes_sep (F.hiOut (c := 0x62C) (n := 48) (by decide) hx) (Nat.le_refl _)]
  have C2 := C.hi h2hi
  have k2' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ ra → q ≠ (24 : Fin 32) →
      reg n2 q = reg n q := fun q h0 h1 h2 h3 h4 h5 h6 hr h24 => by
    have hb : q ∉ dqP1.filterMap BInstr.dst := by simp only [dqP1]; revert h0 h1 h2 h24; revert q; decide
    rw [k2 q h0 h2 h3 h4 h5 h6 hr, r1, runBlock_reg _ _ _ q hz hb]
  have e24 : reg n2 (24 : Fin 32) = S + BitVec.ofNat 32 0x62C := by
    rw [k2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r1]
    simp +decide only [runBlock, BInstr.run, dqP1, upd, ↓reduceIte]; rw [rsp]; rfl
  have sp2 : reg n2 sp = S := by
    rw [k2' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact rsp
  -- the subtraction
  have u2' : St M2 DP n2 0x452 (reg n2) := ⟨u2.pc, mem2, fun _ => rfl⟩
  obtain ⟨n3, c3, u3⟩ := u2'.block dqP2 C2.self dqP2_end ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r3 : ∀ q, reg n3 q = (runBlock dqP2 (M2, reg n2)).2 q := fun q => by rw [u3.regs]
  have t3 : St M2 DP n3 0x462 (reg n3) := ⟨u3.pc, u3.mem, fun _ => rfl⟩
  have e9 : reg n3 (9 : Fin 32) = 12 := by
    rw [r3]; simp +decide only [runBlock, BInstr.run, dqP2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl
  obtain ⟨n4, d4, u4⟩ := t3.notTaken C2.self 0x464 dp_at_462 (by decide) (by
    show (reg n3 (9 : Fin 32) == reg n3 x0) = false; rw [e9, t3.zero]; rfl)
  have k3 : ∀ q, q ≠ (8 : Fin 32) → q ≠ (9 : Fin 32) → q ≠ (18 : Fin 32) → q ≠ (20 : Fin 32) → reg n4 q = reg n2 q :=
    fun q h8 h9 h18 h20 => by
      have hb : q ∉ dqP2.filterMap BInstr.dst := by simp only [dqP2]; revert h8 h9 h18 h20; revert q; decide
      rw [u4.regs, r3, runBlock_reg _ _ _ q u2.zero hb]
  have sB : Sep (S + 0xFFFFFFFC) 4 BSUB borrowingSubCode.length :=
    sep_of_le (by rw [hb4, show BSUB.toNat = 0x403a2320 from rfl]; omega) (by decide)
  have sFC : Sep (S + 0xFFFFFFFC) 4 DP p384DecompressCode.length :=
    sep_of_le (by rw [hb4, show DP.toNat = 0x403a5262 from rfl]; omega) (by decide)
  obtain ⟨n5, M5, c5, u5, hc5, hbs5, fr5, hm5, hv5, sp5, k5⟩ := dq_sub_loop (F := S) (acc := S + BitVec.ofNat 32 0x98C)
    (np := S + BitVec.ofNat 32 0x134) (D := S + BitVec.ofNat 32 0x62C) (M0 := M2) (by omega)
    (by rw [F.at _ (by decide)]; omega) (by rw [F.at _ (by decide)]; omega) (by rw [F.at _ (by decide)]; omega)
    (by rw [F.at _ (by decide)]; omega)
    (lowS 0 _ 4 (by decide) (by decide) hb4 _ _ (by decide)) (lowS 0 _ 4 (by decide) (by decide) hb4 _ _ (by decide))
    (lowS 0 _ 4 (by decide) (by decide) hb4 _ _ (by decide))
    (sepS S (.inl (by decide)) (by decide) (by decide)) (sepS S (.inr (by decide)) (by decide) (by decide))
    sB sFC (F.sepHi (by decide) (by decide) (by decide)) (F.sepHi (by decide) (by decide) (by decide))
    11 0 (by decide) (⟨u4.pc, u4.mem, fun _ => rfl⟩ : St M2 DP n4 0x464 (reg n4)) C2.self C2.bsub (fun _ _ _ => rfl)
    (.inl rfl) (by simp [accV, maskBit])
    (by rw [k3 sp (by decide) (by decide) (by decide) (by decide)]; exact sp2)
    (by rw [Nat.mul_zero, add_ofNat_zero, u4.regs, r3]; simp +decide only [runBlock, BInstr.run, dqP2, upd, ↓reduceIte]
        rw [sp2, spo]; rfl)
    (by rw [Nat.mul_zero, add_ofNat_zero, u4.regs, r3]; simp +decide only [runBlock, BInstr.run, dqP2, upd, ↓reduceIte]
        rw [sp2]; rfl)
    (by rw [Nat.mul_zero, add_ofNat_zero, k3 24 (by decide) (by decide) (by decide) (by decide), e24])
    (by rw [u4.regs, e9]; rfl)
    (by rw [u4.regs, r3]; simp +decide only [runBlock, BInstr.run, dqP2, upd, ↓reduceIte]; (try rw [u2.zero]); try rfl)
  have lo4 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFFC) 4 x 1 := fun x hx =>
    hiB _ 4 (by rw [hb4]; omega) x hx
  have lo16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    hiB _ 16 (by rw [hb16]; omega) x hx
  have lo50 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (S + 0xFFFFFFB0) 0x50 x 1 := fun x hx =>
    hiB _ 0x50 (by rw [hb50]; omega) x hx
  have h5hi : ∀ x : Word, 0x40000000 ≤ x.toNat → M5 x = M x := fun x hx => by
    rw [fr5 x (lo4 x hx) (F.hiOut (c := 0x62C) (n := 48) (by decide) hx), h2hi x hx]
  have C5 := C.hi h5hi
  have s27 : reg n5 (27 : Fin 32) = reg n (27 : Fin 32) := by
    rw [k5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), k3 _ (by decide) (by decide) (by decide) (by decide),
      k2' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  -- copy the difference to S + 0x9EC
  obtain ⟨n6, c6, u6⟩ := u5.block dqP3 hc5 dqP3_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r6 : ∀ q, reg n6 q = (runBlock dqP3 (M5, reg n5)).2 q := fun q => by rw [u6.regs]
  have fA : (S + 0xFFFFFFF0).toNat % 4 = 0 := by rw [hb16]; omega
  have fW : (S + 0xFFFFFFF0).toNat + 16 ≤ 2 ^ 32 := by rw [hb16]; omega
  have hFC : Sep (S + 0xFFFFFFF0) 16 (MCS + 8) memcpyBodyCode.length :=
    sep_of_le (by rw [hb16, show (MCS + 8).toNat = 0x403b4856 from rfl]; omega) (by decide)
  have b16 : ∀ c, c + 48 ≤ 0xA50 → Sep (S + BitVec.ofNat 32 c) 48 (S + 0xFFFFFFF0) 16 := fun c hc =>
    (sep_of_le (by rw [hb16, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)).symm
  have w48 : ∀ c, c + 48 ≤ 0xA50 → (S + BitVec.ofNat 32 c).toNat + 48 < 2 ^ 32 := fun c hc => by
    rw [F.at c (by omega)]; omega
  obtain ⟨n7, c7, u7, fr7, k7⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x9EC) (src := S + BitVec.ofNat 32 0x62C)
    (S := S) (N := 48) (⟨u6.pc, u6.mem, fun _ => rfl⟩ : St M5 DP n6 0x494 (reg n6)) C5 dp_at_494 dp_at_498
    (by decide) (by decide) (by rw [r6, runBlock_reg _ _ _ sp u5.zero (by decide)]; exact sp5)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, dqP3, upd, ↓reduceIte]; rw [sp5, spo]; rfl)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, dqP3, upd, ↓reduceIte]; rw [sp5]; rfl)
    (by rw [r6]; simp +decide only [runBlock, BInstr.run, dqP3, upd, ↓reduceIte]; (try rw [u5.zero]); try rfl)
    ⟨C5.body, F.sepHi (by decide) (by decide) (by decide), hFC, b16 _ (by decide), b16 _ (by decide),
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, w48 _ (by decide), w48 _ (by decide)⟩
  have h7hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n7.mem x = M x := fun x hx => by
    rw [fr7 x (lo16 x hx), copyBytes_sep (F.hiOut (c := 0x9EC) (n := 48) (by decide) hx) (Nat.le_refl _), h5hi x hx]
  have C7 := C.hi h7hi
  have k7' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg n7 q = reg n5 q :=
    fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr => by
      have hb : q ∉ dqP3.filterMap BInstr.dst := by simp only [dqP3]; revert h0 h1 h2; revert q; decide
      rw [k7 q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr, r6, runBlock_reg _ _ _ q u5.zero hb]
  have sp7 : reg n7 sp = S := by
    rw [k7' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp5
  -- the choice
  obtain ⟨mc, hmc⟩ : ∃ mc, reg n (27 : Fin 32) = mc := ⟨_, rfl⟩
  obtain ⟨bw, hbw⟩ : ∃ bw, reg n5 (20 : Fin 32) = bw := ⟨_, rfl⟩
  rw [hbw] at hm5 hv5
  have e27 : reg n7 (27 : Fin 32) = mc := by
    rw [k7' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s27, hmc]
  have e20 : reg n7 (20 : Fin 32) = bw := by
    rw [k7' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hbw]
  obtain ⟨cc, hcc⟩ : ∃ cc, aluEval .and (aluEval .sltu mc 1) bw = cc := ⟨_, rfl⟩
  have hcv := choice_val mc bw hm5
  rw [hcc] at hcv
  have hc01 : cc = 0 ∨ cc = 1 := by
    rw [hcv]; by_cases h : mc.toNat = 0 ∧ maskBit bw = 1
    · rw [ite_eq_left h]; exact .inr rfl
    · rw [ite_eq_right h]; exact .inl rfl
  have u7' : St n7.mem DP n7 0x49C (reg n7) := u7
  have a62C : (S + BitVec.ofNat 32 0x62C).toNat % 4 = 0 := by rw [F.at _ (by decide)]; omega
  obtain ⟨n8, c8, u8⟩ := u7'.block dqP4 C7.self dqP4_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, dqP4]
    simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp7]
    exact ⟨⟨a62C, F.sepHi (by decide) (by decide) (by decide)⟩, a62C, F.sepHi (by decide) (by decide) (by decide)⟩)
  have r8 : ∀ q, reg n8 q = (runBlock dqP4 (n7.mem, reg n7)).2 q := fun q => by rw [u8.regs]
  have m8 : n8.mem = memStore8 (memStore32 n7.mem (S + BitVec.ofNat 32 0x62C) mc) (S + BitVec.ofNat 32 0x62C)
      (cc.extractLsb' 0 8) := by
    rw [u8.mem]; simp +decide only [runBlock, BInstr.run, dqP4, upd, ↓reduceIte]
    rw [sp7, e27, e20, memLoad32_store32_same, ← hcc]; rfl
  have v24 : reg n8 (24 : Fin 32) = cc := by
    rw [r8]; simp +decide only [runBlock, BInstr.run, dqP4, upd, ↓reduceIte]
    rw [sp7, e27, e20, memLoad32_store32_same, ← hcc]
  have k8 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ (24 : Fin 32) → reg n8 q = reg n7 q := fun q h0 h1 h2 h24 => by
    have hb : q ∉ dqP4.filterMap BInstr.dst := by simp only [dqP4]; revert h0 h1 h2 h24; revert q; decide
    rw [r8, runBlock_reg _ _ _ q u7'.zero hb]
  have hc8 : CodeIn n8.mem DP p384DecompressCode := by
    rw [m8]; exact CodeIn.store8 (CodeIn.store32 C7.self (F.sepHi (by decide) (by decide) (by decide)))
      (F.sepHi (by decide) (by decide) (by decide))
  have h8hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n8.mem x = M x := fun x hx => by
    rw [m8, memStore8_ne (fun e => (F.hiOut (c := 0x62C) (n := 1) (by decide) hx) 0 (by decide) 0 (by decide)
      (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore32_get_sep (F.hiOut (c := 0x62C) (n := 4) (by decide) hx), h7hi x hx]
  have C8 := C.hi h8hi
  -- borrowing_sub, whose result goes unused
  obtain ⟨n9, c9, u9, _, _, sp9, fr9, mem9⟩ := (⟨u8.pc, rfl, fun _ => rfl⟩ : St n8.mem DP n8 0x4C2 (reg n8)).bsubCall
    C8.self C8.bsub (by decide) dp_at_4c2 dp_at_4c6 (by decide) (by decide)
    (by rw [k8 sp (by decide) (by decide) (by decide) (by decide)]; exact sp7) (by omega) sB
  have h9hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n9.mem x = M x := fun x hx => by
    rw [mem9 x (lo4 x hx), h8hi x hx]
  have C9 := C.hi h9hi
  have k9 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ ra → q ≠ (24 : Fin 32) → reg n9 q = reg n7 q :=
    fun q h0 h1 h2 h3 h4 hr h24 => by rw [fr9 q h0 h1 h2 h3 h4 hr, k8 q h0 h1 h2 h24]
  have e24' : reg n9 (24 : Fin 32) = cc := by rw [fr9 _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide), v24]
  -- select into S + 0x62C, then copy it to the accumulator
  obtain ⟨n10, c10, u10⟩ := u9.block dqP5 C9.self dqP5_end ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have r10 : ∀ q, reg n10 q = (runBlock dqP5 (n9.mem, reg n9)).2 q := fun q => by rw [u10.regs]
  obtain ⟨n11, c11, u11, vals, fr11, k11⟩ := dq_sel (out := S + BitVec.ofNat 32 0x62C)
    (ap := S + BitVec.ofNat 32 0x9EC) (bp := S + BitVec.ofNat 32 0x98C) (c := cc) (S := S)
    (⟨u10.pc, u10.mem, fun _ => rfl⟩ : St n9.mem DP n10 0x4E0 (reg n10)) C9 F dp_at_4e0 dp_at_4e4 (by decide) (by decide)
    (by rw [r10, runBlock_reg _ _ _ sp u9.zero (by decide)]; exact sp9)
    (by rw [r10]; simp +decide only [runBlock, BInstr.run, dqP5, upd, ↓reduceIte]; rw [sp9]; rfl)
    (by rw [r10]; simp +decide only [runBlock, BInstr.run, dqP5, upd, ↓reduceIte]; rw [sp9, spo]; rfl)
    (by rw [r10]; simp +decide only [runBlock, BInstr.run, dqP5, upd, ↓reduceIte]; rw [sp9, spo]; rfl)
    (by rw [r10]; simp +decide only [runBlock, BInstr.run, dqP5, upd, ↓reduceIte]; rw [e24']
        exact BitVec.zero_add _)
    hc01 (by decide) (by decide) (by decide) rfl rfl rfl (by decide) (by decide) (by decide)
  have h11hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n11.mem x = M x := fun x hx => by
    rw [fr11 x (lo50 x hx) (F.hiOut (c := 0x62C) (n := 48) (by decide) hx), h9hi x hx]
  have C11 := C.hi h11hi
  have k11' : ∀ q, selKeep q = true → q ≠ ra → reg n11 q = reg n9 q := fun q hq hr => by
    have hb : q ∉ dqP5.filterMap BInstr.dst := by simp only [dqP5]; revert hq; revert q; decide
    rw [k11 q hq hr, r10, runBlock_reg _ _ _ q u9.zero hb]
  have sp11 : reg n11 sp = S := by rw [k11' sp rfl (by decide)]; exact sp9
  obtain ⟨n12, c12, u12⟩ := u11.block dqP6 C11.self dqP6_end ⟨trivial, trivial, trivial, trivial, trivial⟩
  have r12 : ∀ q, reg n12 q = (runBlock dqP6 (n11.mem, reg n11)).2 q := fun q => by rw [u12.regs]
  obtain ⟨n13, c13, u13, fr13, k13⟩ := dq_memcpy (dst := S + BitVec.ofNat 32 0x98C) (src := S + BitVec.ofNat 32 0x62C)
    (S := S) (N := 48) (⟨u12.pc, u12.mem, fun _ => rfl⟩ : St n11.mem DP n12 0x4F8 (reg n12)) C11 dp_at_4f8 dp_at_4fc
    (by decide) (by decide) (by rw [r12, runBlock_reg _ _ _ sp u11.zero (by decide)]; exact sp11)
    (by rw [r12]; simp +decide only [runBlock, BInstr.run, dqP6, upd, ↓reduceIte]; rw [sp11, spo]; rfl)
    (by rw [r12]; simp +decide only [runBlock, BInstr.run, dqP6, upd, ↓reduceIte]; rw [sp11]; rfl)
    (by rw [r12]; simp +decide only [runBlock, BInstr.run, dqP6, upd, ↓reduceIte]; (try rw [u11.zero]); try rfl)
    ⟨C11.body, F.sepHi (by decide) (by decide) (by decide), hFC, b16 _ (by decide), b16 _ (by decide),
      sepS S (.inr (by decide)) (by decide) (by decide), fA, fW, w48 _ (by decide), w48 _ (by decide)⟩
  have h13hi : ∀ x : Word, 0x40000000 ≤ x.toNat → n13.mem x = M x := fun x hx => by
    rw [fr13 x (lo16 x hx), copyBytes_sep (F.hiOut (c := 0x98C) (n := 48) (by decide) hx) (Nat.le_refl _),
      h11hi x hx]
  have C13 := C.hi h13hi
  have k13' : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → q ≠ a6 → q ≠ a7 → q ≠ t0 → q ≠ t1 →
      q ≠ (7 : Fin 32) → q ≠ (28 : Fin 32) → q ≠ (29 : Fin 32) → q ≠ (30 : Fin 32) → q ≠ ra → reg n13 q = reg n11 q :=
    fun q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr => by
      have hb : q ∉ dqP6.filterMap BInstr.dst := by simp only [dqP6]; revert h0 h1 h2; revert q; decide
      rw [k13 q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hr, r12, runBlock_reg _ _ _ q u11.zero hb]
  have sp13 : reg n13 sp = S := by
    rw [k13' sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact sp11
  -- the frame, through each step
  have frame : ∀ x, Sep (S + 0xFFFFFFB0) 0x50 x 1 → Sep (S + BitVec.ofNat 32 0x62C) 48 x 1 →
      Sep (S + BitVec.ofNat 32 0x98C) 48 x 1 → Sep (S + BitVec.ofNat 32 0x9EC) 48 x 1 → n13.mem x = M x := by
    intro x h50 h62 h98 h9E
    have h16 : Sep (S + 0xFFFFFFF0) 16 x 1 := by
      have := h50.sub (c := 0x40) (l := 16) (by decide)
      rwa [show S + 0xFFFFFFB0 + BitVec.ofNat 32 0x40 = S + 0xFFFFFFF0 by rw [BitVec.add_assoc]; rfl] at this
    have h4 : Sep (S + 0xFFFFFFFC) 4 x 1 := by
      have := h50.sub (c := 0x4C) (l := 4) (by decide)
      rwa [show S + 0xFFFFFFB0 + BitVec.ofNat 32 0x4C = S + 0xFFFFFFFC by rw [BitVec.add_assoc]; rfl] at this
    rw [fr13 x h16, copyBytes_sep h98 (Nat.le_refl _), fr11 x h50 h62, mem9 x h4, m8,
      memStore8_ne (fun e => h62 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore32_get_sep (h62.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h),
      fr7 x h16, copyBytes_sep h9E (Nat.le_refl _), fr5 x h4 h62, ← hM2, fillBytes_sep h62 (Nat.le_refl _)]
  -- the accumulator, word by word
  have below16 : ∀ c, c + 4 ≤ 0xA50 → Sep (S + 0xFFFFFFF0) 16 (S + BitVec.ofNat 32 c) 4 := fun c hc =>
    sep_of_le (by rw [hb16, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)
  have below4 : ∀ c, c + 4 ≤ 0xA50 → Sep (S + 0xFFFFFFFC) 4 (S + BitVec.ofNat 32 c) 4 := fun c hc =>
    sep_of_le (by rw [hb4, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)
  have below50 : ∀ c, c + 4 ≤ 0xA50 → Sep (S + 0xFFFFFFB0) 0x50 (S + BitVec.ofNat 32 c) 4 := fun c hc =>
    sep_of_le (by rw [hb50, F.at c (by omega)]; omega) (by rw [F.at c (by omega)]; omega)
  have n9acc : ∀ i, i < 12 → memLoad32 n9.mem (S + BitVec.ofNat 32 0x98C + BitVec.ofNat 32 (4 * i)) =
      memLoad32 M (S + BitVec.ofNat 32 0x98C + BitVec.ofNat 32 (4 * i)) := fun i hi => by
    rw [add_ofNat_assoc, load_frame mem9 (below4 _ (by omega)), m8, ld_ofNat, ld_ofNat]
    have h62 : ∀ j, j < 4 → Sep (S + BitVec.ofNat 32 0x62C) 4 (S + BitVec.ofNat 32 (0x98C + 4 * i) + BitVec.ofNat 32 j) 1 :=
      fun j hj => by rw [add_ofNat_assoc]; exact sepS S (.inl (by omega)) (by decide) (by omega)
    rw [memStore8_ne (fun e => (h62 3 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore8_ne (fun e => (h62 2 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore8_ne (fun e => (h62 1 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore8_ne (fun e => (h62 0 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore32_get_sep (h62 3 (by decide)), memStore32_get_sep (h62 2 (by decide)),
      memStore32_get_sep (h62 1 (by decide)), memStore32_get_sep (h62 0 (by decide)), ← ld_ofNat, ← ld_ofNat,
      load_frame fr7 (below16 _ (by omega)),
      cp_word_out (sepS S (c := 0x9EC) (n := 48) (d := 0x98C + 4 * i) (k := 4) (.inr (by omega)) (by decide) (by omega)),
      load_frame2 fr5 (below4 _ (by omega)) (sepS S (c := 0x62C) (n := 48) (d := 0x98C + 4 * i) (k := 4)
        (.inl (by omega)) (by decide) (by omega)), ← hM2,
      fill_word_out (sepS S (c := 0x62C) (n := 48) (d := 0x98C + 4 * i) (k := 4) (.inl (by omega)) (by decide) (by omega))]
  have n9d : ∀ i, i < 12 → memLoad32 n9.mem (S + BitVec.ofNat 32 0x9EC + BitVec.ofNat 32 (4 * i)) =
      memLoad32 M5 (S + BitVec.ofNat 32 0x62C + BitVec.ofNat 32 (4 * i)) := fun i hi => by
    rw [add_ofNat_assoc, load_frame mem9 (below4 _ (by omega)), m8, ld_ofNat, ld_ofNat]
    have h62 : ∀ j, j < 4 → Sep (S + BitVec.ofNat 32 0x62C) 4 (S + BitVec.ofNat 32 (0x9EC + 4 * i) + BitVec.ofNat 32 j) 1 :=
      fun j hj => by rw [add_ofNat_assoc]; exact sepS S (.inl (by omega)) (by decide) (by omega)
    rw [memStore8_ne (fun e => (h62 3 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore8_ne (fun e => (h62 2 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore8_ne (fun e => (h62 1 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore8_ne (fun e => (h62 0 (by decide)) 0 (by decide) 0 (by decide) (by rw [add_ofNat_zero, add_ofNat_zero]; exact e.symm)),
      memStore32_get_sep (h62 3 (by decide)), memStore32_get_sep (h62 2 (by decide)),
      memStore32_get_sep (h62 1 (by decide)), memStore32_get_sep (h62 0 (by decide)), ← ld_ofNat, ← ld_ofNat,
      load_frame fr7 (below16 _ (by omega)), ← add_ofNat_assoc, cp_word (by omega) (by decide)]
  have n13acc : ∀ i, i < 12 → memLoad32 n13.mem (S + BitVec.ofNat 32 0x98C + BitVec.ofNat 32 (4 * i)) =
      if cc = 1 then memLoad32 M (S + BitVec.ofNat 32 0x98C + BitVec.ofNat 32 (4 * i))
      else memLoad32 M5 (S + BitVec.ofNat 32 0x62C + BitVec.ofNat 32 (4 * i)) := fun i hi => by
    rw [load_frame fr13 (by rw [add_ofNat_assoc]; exact below16 _ (by omega)), cp_word (by omega) (by decide),
      vals i hi, n9acc i hi, n9d i hi]
  -- reload the count and loop
  have a3C : (S + BitVec.ofNat 32 0x3C).toNat % 4 = 0 := by rw [F.at _ (by decide)]; omega
  obtain ⟨n14, c14, u14⟩ := u13.block dqP7 C13.self dqP7_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, dqP7]
    simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [sp13]; exact a3C)
  have r14 : ∀ q, reg n14 q = (runBlock dqP7 (n13.mem, reg n13)).2 q := fun q => by rw [u14.regs]
  have t14 : St n13.mem DP n14 0x50C (reg n14) := ⟨u14.pc, u14.mem, fun _ => rfl⟩
  obtain ⟨n15, d15, u15⟩ := t14.jump C13.self dp_at_50c (off' := 0x348) (by decide) (by rw [t14.pc]; decide)
  have s3C : ∀ c, c + 48 ≤ 0xA50 → 0x3C + 4 ≤ c → Sep (S + BitVec.ofNat 32 c) 48 (S + BitVec.ofNat 32 0x3C) 4 :=
    fun c h1 h2 => sepS S (.inr (by omega)) (by omega) (by decide)
  have h3C : memLoad32 n13.mem (S + BitVec.ofNat 32 0x3C) = memLoad32 M (S + BitVec.ofNat 32 0x3C) :=
    memLoad32_congr fun j hj => frame _ ((below50 0x3C (by decide)).subR (c := j) (l := 1) (by omega))
      ((s3C 0x62C (by decide) (by decide)).subR (c := j) (l := 1) (by omega))
      ((s3C 0x98C (by decide) (by decide)).subR (c := j) (l := 1) (by omega))
      ((s3C 0x9EC (by decide) (by decide)).subR (c := j) (l := 1) (by omega))
  have hdv : accV M5 (S + BitVec.ofNat 32 0x62C) 12 < 2 ^ 384 := accV_lt M5 _ 12
  have sA : ∀ d, d + 4 ≤ 0x62C → Sep (S + BitVec.ofNat 32 0x62C) 48 (S + BitVec.ofNat 32 d) 4 :=
    fun d hd => sepS S (.inr (by omega)) (by decide) (by omega)
  have sA' : ∀ d, 0x62C + 48 ≤ d → d + 4 ≤ 0xA50 → Sep (S + BitVec.ofNat 32 0x62C) 48 (S + BitVec.ofNat 32 d) 4 :=
    fun d hd hd' => sepS S (.inl (by omega)) (by decide) (by omega)
  have eA : accV M2 (S + BitVec.ofNat 32 0x98C) 12 = accV M (S + BitVec.ofNat 32 0x98C) 12 :=
    accV_congr2 12 fun i hi => by
      rw [← hM2, add_ofNat_assoc, fill_word_out (sA' _ (by omega) (by omega))]
  have eN : accV M2 (S + BitVec.ofNat 32 0x134) 12 = accV M (S + BitVec.ofNat 32 0x134) 12 :=
    accV_congr2 12 fun i hi => by
      rw [← hM2, add_ofNat_assoc, fill_word_out (sA _ (by omega))]
  rw [eA, eN] at hv5
  refine ⟨n15, accV M5 (S + BitVec.ofNat 32 0x62C) 12, bw,
    c1.trans (c2.trans (c3.trans (.cons d4 (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans (c11.trans
      (c12.trans (c13.trans (c14.trans (.single d15)))))))))))))),
    ⟨u15.pc, by rw [u15.mem], fun _ => rfl⟩, by rw [u15.mem]; exact C13, hm5, hdv, hv5, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u15.mem, hmc]
    by_cases hcd : mc.toNat = 0 ∧ maskBit bw = 1
    · rw [ite_eq_left hcd]
      have h1 : cc = 1 := by rw [hcv, ite_eq_left hcd]
      exact accV_congr2 12 fun i hi => by rw [n13acc i hi, ite_eq_left h1]
    · rw [ite_eq_right hcd]
      have h0 : cc ≠ 1 := by rw [hcv, ite_eq_right hcd]; decide
      exact accV_congr2 12 fun i hi => by rw [n13acc i hi, ite_eq_right h0]
  · rw [u15.regs, r14]; simp +decide only [runBlock, BInstr.run, dqP7, upd, ↓reduceIte]
    rw [sp13]; show aluEval .add (memLoad32 n13.mem (S + BitVec.ofNat 32 0x3C)) 1 = _; rw [h3C]; rfl
  · rw [u15.regs, r14]; simp +decide only [runBlock, BInstr.run, dqP7, upd, ↓reduceIte]; rw [sp13, spo]; rfl
  · intro x h50 h62 h98 h9E; rw [u15.mem]; exact frame x h50 h62 h98 h9E
  · intro q hq
    have hb14 : q ∉ dqP7.filterMap BInstr.dst := by simp only [dqP7]; revert hq; revert q; decide
    have ne : ∀ r : Fin 32, postKeep r = false → q ≠ r := fun r hr => pkeep_ne hq hr
    rw [u15.regs, r14, runBlock_reg _ _ _ q u13.zero hb14,
      k13' q (ne a0 rfl) (ne a1 rfl) (ne a2 rfl) (ne a3 rfl) (ne a4 rfl) (ne a5 rfl) (ne a6 rfl) (ne a7 rfl)
        (ne t0 rfl) (ne t1 rfl) (ne 7 rfl) (ne 28 rfl) (ne 29 rfl) (ne 30 rfl) (ne ra rfl),
      k11' q (by revert hq; revert q; decide) (ne ra rfl),
      k9 q (ne a0 rfl) (ne a1 rfl) (ne a2 rfl) (ne a3 rfl) (ne a4 rfl) (ne ra rfl) (ne 24 rfl),
      k7' q (ne a0 rfl) (ne a1 rfl) (ne a2 rfl) (ne a3 rfl) (ne a4 rfl) (ne a5 rfl) (ne a6 rfl) (ne a7 rfl)
        (ne t0 rfl) (ne t1 rfl) (ne 7 rfl) (ne 28 rfl) (ne 29 rfl) (ne 30 rfl) (ne ra rfl),
      k5 q (ne a0 rfl) (ne a1 rfl) (ne a2 rfl) (ne a3 rfl) (ne a4 rfl) (ne ra rfl) (ne 8 rfl) (ne 18 rfl)
        (ne 24 rfl) (ne 9 rfl) (ne 20 rfl),
      k3 q (ne 8 rfl) (ne 9 rfl) (ne 18 rfl) (ne 20 rfl),
      k2' q (ne a0 rfl) (ne a1 rfl) (ne a2 rfl) (ne a3 rfl) (ne a4 rfl) (ne a5 rfl) (ne a6 rfl) (ne ra rfl) (ne 24 rfl)]

theorem accV_zero {M : Word → BitVec 8} {b : Word} :
    ∀ n, (∀ i, i < n → memLoad32 M (b + BitVec.ofNat 32 (4 * i)) = 0) → accV M b n = 0
  | 0, _ => rfl
  | n + 1, h => by
    rw [accV_succ1, accV_zero n fun i hi => h i (by omega), h n (by omega), show (0 : Word).toNat = 0 from rfl,
      Nat.zero_mul]

/-- The registers a squaring leaves alone. -/
def sqKeep (q : Fin 32) : Bool := q.val ∈ [2, 3, 4, 19, 21, 22, 23, 25, 26]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **One squaring in Montgomery form**, from 0x34E to the loop's head at
0x348: for the working value `W < N` at `S + 0x98C` and the modulus `N`
at `S + 0x134`, it leaves `R < N` at `S + 0x98C` with
`R · 2³⁸⁴ ≡ W · W (mod N)`, and counts the pass in `a1`. -/
theorem dq_sq {M : Word → BitVec 8} {S : Word} {n : Machine} {j : Nat} (C : DqCode M) (F : DqFrame S)
    (s : St M DP n 0x34E (reg n)) (rsp : reg n sp = S) (ra1 : reg n a1 = BitVec.ofNat 32 j)
    (r25 : reg n (25 : Fin 32) = S + BitVec.ofNat 32 0x98C) (r22 : reg n (22 : Fin 32) = 12)
    (r19 : reg n (19 : Fin 32) = S + BitVec.ofNat 32 0x9BC) (r23 : reg n (23 : Fin 32) = 0xFFFFFFFF)
    (r21 : reg n (21 : Fin 32) = S + BitVec.ofNat 32 0x138) (r26 : reg n (26 : Fin 32) = S + BitVec.ofNat 32 0x990)
    (r18 : reg n (18 : Fin 32) = S + BitVec.ofNat 32 0x9C0)
    (hN0 : memLoad32 M (S + BitVec.ofNat 32 0x134) = 0xFFFFFFFF)
    (hW : accV M (S + BitVec.ofNat 32 0x98C) 12 < accV M (S + BitVec.ofNat 32 0x134) 12) :
    ∃ n', Steps n n' ∧ St n'.mem DP n' 0x348 (reg n') ∧ DqCode n'.mem ∧
      accV n'.mem (S + BitVec.ofNat 32 0x98C) 12 < accV M (S + BitVec.ofNat 32 0x134) 12 ∧
      accV n'.mem (S + BitVec.ofNat 32 0x98C) 12 * 2 ^ 384 % accV M (S + BitVec.ofNat 32 0x134) 12 =
        accV M (S + BitVec.ofNat 32 0x98C) 12 * accV M (S + BitVec.ofNat 32 0x98C) 12 %
          accV M (S + BitVec.ofNat 32 0x134) 12 ∧
      reg n' a1 = BitVec.ofNat 32 j + 1 ∧ reg n' (18 : Fin 32) = S + BitVec.ofNat 32 0x9C0 ∧
      (∀ x, Sep (S + 0xFFFFFFB0) 0x50 x 1 → Sep (S + BitVec.ofNat 32 0x3C) 4 x 1 →
        Sep (S + BitVec.ofNat 32 0x62C) 48 x 1 → Sep (S + BitVec.ofNat 32 0x98C) 0x90 x 1 → n'.mem x = M x) ∧
      ∀ q, sqKeep q = true → reg n' q = reg n q := by
  have hSl := F.lo; have hSh := F.hi; have hSa := F.al
  obtain ⟨n1, c1, u1, C1, wcopy, wzero, w3C, fr1, e27, e17, e16, e5, k1⟩ :=
    dq_sq_pre (j := j) C F s rsp ra1 r25 r22
  have k1' : ∀ q, sqKeep q = true → reg n1 q = reg n q := fun q hq => k1 q (by revert hq; revert q; decide)
  have sep98 : ∀ d, d + 4 ≤ 0xA50 → (0x98C + 0x60 ≤ d ∨ d + 4 ≤ 0x98C) →
      Sep (S + BitVec.ofNat 32 0x98C) 0x60 (S + BitVec.ofNat 32 d) 4 :=
    fun d h1 h2 => sepS S h2 (by decide) (by omega)
  have hb16 : (S + BitVec.ofNat 32 (2 ^ 32 - 16)).toNat = S.toNat - 16 := F.below 16 (by decide) (by decide)
  have lo16 : ∀ d, d + 4 ≤ 0xA50 → Sep (S + BitVec.ofNat 32 (2 ^ 32 - 16)) 16 (S + BitVec.ofNat 32 d) 4 := fun d hd =>
    sep_of_le (by rw [hb16, F.at d (by omega)]; omega) (by rw [F.at d (by omega)]; omega)
  have nfr : ∀ i, i < 12 → memLoad32 n1.mem (S + BitVec.ofNat 32 (0x134 + 4 * i)) =
      memLoad32 M (S + BitVec.ofNat 32 (0x134 + 4 * i)) := fun i hi =>
    memLoad32_congr fun q hq => fr1 _ ((lo16 _ (by omega)).subR (c := q) (l := 1) (by omega))
      ((sepS S (c := 0x3C) (n := 4) (d := 0x134 + 4 * i) (k := 4) (.inl (by omega)) (by decide) (by omega)).subR
        (c := q) (l := 1) (by omega))
      ((sep98 _ (by omega) (.inr (by omega))).subR (c := q) (l := 1) (by omega))
  have eN : accV n1.mem (S + BitVec.ofNat 32 0x134) 12 = accV M (S + BitVec.ofNat 32 0x134) 12 :=
    accV_congr2 12 fun i hi => by rw [add_ofNat_assoc, nfr i hi]
  have eX : accV n1.mem (S + BitVec.ofNat 32 0x9BC) 12 = accV M (S + BitVec.ofNat 32 0x98C) 12 :=
    accV_congr2 12 fun i hi => by rw [add_ofNat_assoc, add_ofNat_assoc, wcopy i hi]
  have eA0 : accV n1.mem (S + BitVec.ofNat 32 0x98C) 12 = 0 :=
    accV_zero 12 fun i hi => by rw [add_ofNat_assoc]; exact wzero i hi
  have eN0 : memLoad32 n1.mem (S + BitVec.ofNat 32 0x134) = 0xFFFFFFFF := by
    have := nfr 0 (by decide); simp only [Nat.mul_zero, Nat.add_zero] at this; rw [this, hN0]
  have hNpos : 0 < accV M (S + BitVec.ofNat 32 0x134) 12 := by omega
  -- the loop
  obtain ⟨n2, M2, c2, u2, hc2, hf2, ⟨U, hU⟩, hbd2, k2⟩ := dq_outer (B := DP) (acc := S + BitVec.ofNat 32 0x98C)
    (xp := S + BitVec.ofNat 32 0x9BC) (np := S + BitVec.ofNat 32 0x134) (M0 := n1.mem)
    (by rw [F.at _ (by decide)]; omega) (by rw [F.at _ (by decide)]; omega) (by rw [F.at _ (by decide)]; omega)
    (by rw [F.at _ (by decide)]; omega) (sepS S (.inl (by decide)) (by decide) (by decide))
    (sepS S (.inr (by decide)) (by decide) (by decide)) (F.sepHi (by decide) (by decide) (by decide)) eN0
    (by rw [eX, eN]; exact hW) 11 0 (by decide) u1 C1.self (fun _ _ => rfl)
    ⟨0, by rw [eA0, e27, show (0 : Word).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero, Nat.mul_zero, Nat.zero_mul,
      Nat.add_zero, show accV n1.mem (S + BitVec.ofNat 32 0x9BC) 0 = 0 from rfl, Nat.zero_mul]⟩
    (by rw [eA0, e27, eN, show (0 : Word).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]; omega)
    (by rw [e5]; rfl) (by rw [k1' 19 rfl]; exact r19)
    (by rw [e16]; have := wcopy 0 (by decide); simp only [Nat.mul_zero, Nat.add_zero] at this; exact this.symm)
    (by rw [k1' 23 rfl]; exact r23) (by rw [k1' 25 rfl]; exact r25)
    (by rw [k1' 21 rfl, r21, add_ofNat_assoc])
    (by rw [k1' 26 rfl, r26, add_ofNat_assoc]) (by rw [k1 18 (by decide), r18, add_ofNat_assoc]) e17 (by rw [k1' 22 rfl]; exact r22)
  have h2hi : ∀ x : Word, 0x40000000 ≤ x.toNat → M2 x = M x := fun x hx => by
    rw [hf2 x (F.hiOut (c := 0x98C) (n := 48) (by decide) hx)]
    exact fr1 x (F.hiOutB (c := 16) (by decide) (by decide) hx) (F.hiOut (c := 0x3C) (n := 4) (by decide) hx)
      (F.hiOut (c := 0x98C) (n := 0x60) (by decide) hx)
  have C2 := C.hi h2hi
  have sp2 : reg n2 sp = S := by rw [k2 sp rfl, k1' sp rfl]; exact rsp
  obtain ⟨n3, Dv, b, c3, u3, C3, hb, hDv, hsub, hres, ha13, h183, fr3, k3⟩ := dq_sq_post C2 F u2 sp2
  -- the arithmetic
  have eN2 : accV M2 (S + BitVec.ofNat 32 0x134) 12 = accV M (S + BitVec.ofNat 32 0x134) 12 := by
    rw [← eN]
    exact accV_congr2 12 fun i hi => memLoad32_congr fun q hq => hf2 _ (by
      rw [add_ofNat_assoc, add_ofNat_assoc]
      exact sepS S (c := 0x98C) (n := 48) (d := 0x134 + (4 * i + q)) (k := 1) (.inr (by omega)) (by decide) (by omega))
  rw [eN2] at hsub
  obtain ⟨A, hA⟩ : ∃ A, accV M2 (S + BitVec.ofNat 32 0x98C) 12 = A := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, accV M (S + BitVec.ofNat 32 0x134) 12 = N := ⟨_, rfl⟩
  obtain ⟨mc, hmc⟩ : ∃ mc, (reg n2 (27 : Fin 32)).toNat = mc := ⟨_, rfl⟩
  rw [hA, hN] at hsub
  rw [hA, hmc] at hres
  rw [hA, hmc, show (2 : Nat) ^ (32 * 12) = 2 ^ 384 from rfl, eN, hN, eX] at hU
  rw [hA, hmc, show (2 : Nat) ^ (32 * 12) = 2 ^ 384 from rfl, eN, hN] at hbd2
  have hNl : N < 2 ^ 384 := by rw [← hN]; exact accV_lt M _ 12
  have fin := mm_final_arith hDv hNl hbd2 hsub (mb_le1 b)
  rw [hN] at hNpos
  have hR : accV n3.mem (S + BitVec.ofNat 32 0x98C) 12 = (A + mc * 2 ^ 384) % N := by rw [hres, fin]
  refine ⟨n3, c1.trans (c2.trans c3), u3, C3, by rw [hN, hR]; exact Nat.mod_lt _ hNpos,
    by rw [hN, hR]; exact mont_congr rfl hU, ?_, h183, fun x h50 h3C h62 h98 => ?_, fun q hq => ?_⟩
  · rw [ha13, show memLoad32 M2 (S + BitVec.ofNat 32 0x3C) = memLoad32 n1.mem (S + BitVec.ofNat 32 0x3C) from
      memLoad32_congr fun q hq => hf2 _ (by
        rw [add_ofNat_assoc]
        exact sepS S (c := 0x98C) (n := 48) (d := 0x3C + q) (k := 1) (.inr (by omega)) (by decide) (by omega)), w3C]
  · have hA48 : Sep (S + BitVec.ofNat 32 0x98C) 48 x 1 := by
      have := h98.sub (c := 0) (l := 48) (by decide); rwa [add_ofNat_zero] at this
    have hE48 : Sep (S + BitVec.ofNat 32 0x9EC) 48 x 1 := by
      have := h98.sub (c := 0x60) (l := 48) (by decide); rwa [add_ofNat_assoc] at this
    have h60 : Sep (S + BitVec.ofNat 32 0x98C) 0x60 x 1 := by
      have := h98.sub (c := 0) (l := 0x60) (by decide); rwa [add_ofNat_zero] at this
    have h16 : Sep (S + BitVec.ofNat 32 (2 ^ 32 - 16)) 16 x 1 := by
      have := h50.sub (c := 0x40) (l := 16) (by decide)
      rwa [show S + 0xFFFFFFB0 + BitVec.ofNat 32 0x40 = S + BitVec.ofNat 32 (2 ^ 32 - 16) by rw [BitVec.add_assoc]; rfl]
        at this
    rw [fr3 x h50 h62 hA48 hE48, hf2 x hA48, fr1 x h16 h3C h60]
  · rw [k3 q (by revert hq; revert q; decide), k2 q (by revert hq; revert q; decide), k1' q hq]

end C3.RV32.Dq
