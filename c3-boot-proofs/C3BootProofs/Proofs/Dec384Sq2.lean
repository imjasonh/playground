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

/-- The code `decompress` runs and calls, at its addresses in the image. -/
structure DqCode (M : Word → BitVec 8) : Prop where
  self : CodeIn M DP p384DecompressCode
  stub : CodeIn M MCS memcpyStubCode
  body : CodeIn M (MCS + 8) memcpyBodyCode
  mset : CodeIn M MSET memsetCode
  bsub : CodeIn M BSUB borrowingSubCode
  sel : CodeIn M SEL uintSelect12Code

theorem codeHi {M M' : Word → BitVec 8} {b : Word} {code : List Nat} (hc : CodeIn M b code)
    (hb : 0x40000000 ≤ b.toNat) (hl : b.toNat + code.length ≤ 2 ^ 32)
    (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) : CodeIn M' b code := fun i hi => by
  rw [h _ (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]; exact hc i hi

theorem DqCode.hi {M M' : Word → BitVec 8} (C : DqCode M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    DqCode M' :=
  ⟨codeHi C.self (by decide) (by decide) h, codeHi C.stub (by decide) (by decide) h,
    codeHi C.body (by decide) (by decide) h, codeHi C.mset (by decide) (by decide) h,
    codeHi C.bsub (by decide) (by decide) h, codeHi C.sel (by decide) (by decide) h⟩

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

end C3.RV32.Dq
