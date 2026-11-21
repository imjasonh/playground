import C3BootProofs.Proofs.Pv384Lib3
import C3BootProofs.Proofs.MontRetrieve12
import C3BootProofs.Proofs.ToBeBytes
import C3BootProofs.Proofs.Wnaf

/-!
# `p384_verify_prehash`: the calls that make the wNAF digits

Wrappers, in the terms of `Pv384Lib.lean`, for the calls that turn `u₁` and
`u₂` into wNAF digits: `zeroArray48`, `montgomery_retrieve::<12>`,
`Uint<12>::to_be_byte_array`, `<[u8]>::reverse`, and `wnaf_form`.
-/

namespace C3.RV32.Pv

open C3.Image C3.RV32.P3 C3.RV32.Dq

set_option maxRecDepth 20000

/-- The functions that make the wNAF digits. -/
structure PvCode5 (M : Word → BitVec 8) : Prop where
  mr : CodeIn M (BitVec.ofNat 32 montRetrieve12Address) montRetrieve12Code
  tbb : CodeIn M (BitVec.ofNat 32 toBeBytes12Address) toBeBytes12Code
  rev : CodeIn M (BitVec.ofNat 32 sliceReverseAddress) sliceReverseCode
  wf : CodeIn M (BitVec.ofNat 32 wnafFormAddress) wnafFormCode
  il : CodeIn M (BitVec.ofNat 32 incrementLimbAddress) incrementLimbCode
  lsh : CodeIn M (BitVec.ofNat 32 lshrdi3Address) lshrdi3Code
  ash : CodeIn M (BitVec.ofNat 32 ashldi3Address) ashldi3Code

theorem PvCode5.hi {M M' : Word → BitVec 8} (C : PvCode5 M) (h : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) :
    PvCode5 M' :=
  ⟨codeHi C.mr (by decide) (by decide) h, codeHi C.tbb (by decide) (by decide) h,
    codeHi C.rev (by decide) (by decide) h, codeHi C.wf (by decide) (by decide) h,
    codeHi C.il (by decide) (by decide) h, codeHi C.lsh (by decide) (by decide) h,
    codeHi C.ash (by decide) (by decide) h⟩

/-- Everything the stages from the wNAF digits on need. -/
structure PvEnv5 (M : Word → BitVec 8) : Prop where
  E : PvEnv4 M
  C5 : PvCode5 M

theorem PvEnv5.fr {B : Word} {M M' : Word → BitVec 8} (E : PvEnv5 M) (F : Fr B 0x21A0)
    (h : ∀ x, PvR B x → M' x = M x) : PvEnv5 M' :=
  ⟨E.E.fr F h, E.C5.hi fun x hx => h x (pvR_of_hi F hx)⟩

set_option maxHeartbeats 8000000 in
/-- A call to `montgomery_retrieve::<12>` with the order: the limbs at
offset `cx` of the frame, out of Montgomery form, at `co`. -/
theorem pv_mr {B : Word} {m : Machine} {off : Nat} {imm o : Word} {co cx : Nat} (F : Fr B 0x21A0)
    (E : PvEnv5 m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 montRetrieve12Address)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 co)
    (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 cx) (ha2 : reg m a2 = BitVec.ofNat 32 0x3FCC4D28)
    (ha3 : reg m a3 = BitVec.ofNat 32 0xE88FDC45) (hco : co + 48 ≤ 0x1D4C) (hcx : cx + 48 ≤ 0x1D4C)
    (aco : co % 4 = 0) (acx : cx % 4 = 0) (hX : accV m.mem (B + 0x420 + BitVec.ofNat 32 cx) 12 < n384) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem co 48 ∧
      accV m'.mem (B + 0x420 + BitVec.ofNat 32 co) 12 = n3fm (accV m.mem (B + 0x420 + BitVec.ofNat 32 cx) 12) 1 := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.E.E.E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have lh : ∀ (b : Word) (l : Nat), 0x40000000 ≤ b.toNat → b.toNat + l ≤ 2 ^ 32 →
      Sep (B + 0x420 + 0xFFFFFFB0) 0x50 b l := fun b l hb hl => FS.lowHi (by decide) rfl hb hl
  have EN : MREnv n1.mem (BitVec.ofNat 32 montRetrieve12Address) (B + 0x420) (B + 0x420 + BitVec.ofNat 32 co)
      (B + 0x420 + BitVec.ofNat 32 cx) n3M := by
    rw [mem1]
    refine ⟨by decide, E.C5.mr, ?_, ?_, ?_, by omega, by omega, pv_al F (by omega) aco, pv_al F (by omega) acx,
      by decide, pv_wr F (by omega), lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      lh _ _ (by decide) (by decide), lh _ _ (by decide) (by decide),
      FS.lowN (k := 0x50) (by decide) (by decide) (by omega), FS.sepHi (by omega) (by decide) (by decide),
      FS.sepHi (by omega) (by decide) (by decide), FS.lowN (k := 0x50) (by decide) (by decide) (by omega),
      pv_lowK F (n := 48) (k := 0x50) (by decide) (by decide) (by decide)⟩
    · rw [show BitVec.ofNat 32 montRetrieve12Address + 0xA30 = MSET by decide]; exact E.E.E.E.C.K.mset
    · rw [show BitVec.ofNat 32 montRetrieve12Address + 0xA98 = MCS by decide]; exact E.E.E.E.C.K.stub
    · rw [show BitVec.ofNat 32 montRetrieve12Address + 0xAA0 = MCS + 8 by decide]; exact E.E.E.E.C.K.body
  have hk : ((BitVec.ofNat 32 0xE88FDC45 : Word).toNat * (memLoad32 n1.mem n3M).toNat + 1) % 2 ^ 32 = 0 := by
    rw [mem1, n3M_w0 E.E.E.E.D2.nmod]; decide
  obtain ⟨n2, c2, pc2, sp2, val2, lt2, fr2, k2⟩ := montRetrieve12_correct n1 EN pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
    (by rw [r1 a2 (by decide)]; exact ha2) (by rw [r1 a3 (by decide)]; exact ha3)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) (by rw [r1 sp (by decide)]; exact hsp) hk
  rw [mem1, n3M_val E.E.E.E.D2.nmod] at val2 lt2
  rw [mem1] at fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_lo (k := 0x50) hx (by decide) (by decide))
      (pvR_hi hx hco), fun q hq => ?_⟩, fun e he1 he2 => fr2 _ (pv_lowB F (k := 0x50) (by decide) (by decide) (by omega))
      (sepS (B + 0x420) (by omega) (by omega) (by omega)), ?_⟩
  · by_cases h : q = sp
    · subst h; rw [sp2, hsp]
    · rw [k2 q (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]
  · exact n3_mont (lt2 hX) (by rw [val2, Nat.mul_one])

theorem cons_aux (a A W c D : Nat) : a + c * A + W * (c * D) = a + c * (A + W * D) := by
  rw [Nat.mul_add, Nat.mul_left_comm W c D, Nat.add_assoc]

theorem app_aux (b X P Y : Nat) : b + 256 * (X + P * Y) = b + 256 * X + P * 256 * Y := by
  rw [Nat.mul_add, ← Nat.add_assoc, Nat.mul_left_comm 256 P Y, Nat.mul_assoc P 256 Y]

theorem accV_cons (M : Word → BitVec 8) (b : Word) :
    ∀ j, accV M b (j + 1) = (memLoad32 M b).toNat + 2 ^ 32 * accV M (b + 4) j
  | 0 => by rw [accV_succ1, Nat.mul_zero, add_ofNat_zero]; show 0 + _ * 1 = _ + 2 ^ 32 * 0; omega
  | j + 1 => by
    rw [accV_succ1, accV_cons M b j, accV_succ1 M (b + 4) j,
      show b + 4 + BitVec.ofNat 32 (4 * j) = b + BitVec.ofNat 32 (4 * (j + 1)) by
        rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]; congr 2; omega,
      show 32 * (j + 1) = 32 + 32 * j by omega, Nat.pow_add]
    exact cons_aux _ _ _ _ _

theorem leN_append : ∀ (x y : List Nat), leN (x ++ y) = leN x + 256 ^ x.length * leN y
  | [], y => by simp [leN]
  | b :: x, y => by
    simp only [List.cons_append, leN, leN_append x y, List.length_cons, Nat.pow_succ]; exact app_aux _ _ _ _

theorem leN_wordBytes (w : Word) : leN (Sha256.wordBytes w).reverse = w.toNat := by
  have := w.isLt
  simp only [Sha256.wordBytes, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, leN] <;> omega

theorem leN_beLimbs (M : Word → BitVec 8) (s : Word) :
    ∀ j, j ≤ 12 → leN (beLimbs M s 11 j).reverse = accV M (s + BitVec.ofNat 32 (4 * (12 - j))) j
  | 0, _ => rfl
  | j + 1, hj => by
    rw [beLimbs_succ, List.reverse_append, leN_append, leN_wordBytes, List.length_reverse,
      show (Sha256.wordBytes _).length = 4 from rfl, leN_beLimbs M s j (by omega), accV_cons,
      show s + BitVec.ofNat 32 (4 * (12 - (j + 1))) + 4 = s + BitVec.ofNat 32 (4 * (12 - j)) by
        rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]; congr 2; omega,
      show 4 * (11 - j) = 4 * (12 - (j + 1)) by omega]

/-- The little-endian value of the reversed big-endian bytes of 12 limbs. -/
theorem leN_beLimbs12 (M : Word → BitVec 8) (s : Word) : leN (beLimbs M s 11 12).reverse = accV M s 12 := by
  rw [leN_beLimbs M s 12 (Nat.le_refl _), Nat.sub_self, Nat.mul_zero, add_ofNat_zero]

theorem memBytes_keep {B : Word} {M M' : Word → BitVec 8} {c w d N : Nat} (K : PvKeep B M M' c w)
    (hd : d + N ≤ 0x1D4C) (h : d + N ≤ c ∨ c + w ≤ d) :
    memBytes M' (B + 0x420 + BitVec.ofNat 32 d) N = memBytes M (B + 0x420 + BitVec.ofNat 32 d) N :=
  memBytes_congr fun j hj => by rw [add_ofNat_assoc]; exact K _ (by omega) (by omega)

theorem memBytes_cp {M M' : Word → BitVec 8} {S : Word} {c d N : Nat}
    (h : ∀ q, q < N → M' (S + BitVec.ofNat 32 (c + q)) = M (S + BitVec.ofNat 32 (d + q))) :
    memBytes M' (S + BitVec.ofNat 32 c) N = memBytes M (S + BitVec.ofNat 32 d) N := by
  unfold memBytes
  exact List.map_congr_left fun i hi => by
    rw [add_ofNat_assoc, add_ofNat_assoc, h i (List.mem_range.mp hi)]

def pvZ : List BInstr := [.aluImm .add a0 a0 0x1, .aluImm .add a1 a1 0xFFFFFFFF]
theorem pvZ_end : blockEnd p384VerifyPrehashCode 0x9F8 pvZ = some 0x9FC := by decide

theorem ofNat_dec (r : Nat) : BitVec.ofNat 32 (r + 1) + 0xFFFFFFFF = BitVec.ofNat 32 r := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xFFFFFFFF : Word).toNat = 0xFFFFFFFF from rfl]
  omega

theorem ofNat_ne0 {k : Nat} (h0 : 0 < k) (h1 : k < 2 ^ 32) : BitVec.ofNat 32 k ≠ 0 := fun h => by
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this; omega

/-- The byte loop at 0x9F4 that zeroes the `r` bytes from offset `c + i` of
the frame. -/
theorem pv_zl {B : Word} (F : Fr B 0x21A0) {c : Nat} :
    ∀ (r i : Nat) {m : Machine}, PvEnv m.mem → St m.mem PV m 0x9F4 (reg m) →
      reg m a0 = B + 0x420 + BitVec.ofNat 32 (c + i) → reg m a1 = BitVec.ofNat 32 r → 0 < r →
      c + i + r ≤ 0x1D4C →
      ∃ m', Steps m m' ∧ St m'.mem PV m' 0x9FE (reg m') ∧ (∀ x, PvR B x → m'.mem x = m.mem x) ∧
        PvKeep B m.mem m'.mem (c + i) r ∧ (∀ j, j < r → m'.mem (B + 0x420 + BitVec.ofNat 32 (c + i + j)) = 0) ∧
        (∀ q, q ≠ a0 → q ≠ a1 → reg m' q = reg m q)
  | 0, _, _, _, _, _, _, h0, _ => absurd h0 (Nat.lt_irrefl 0)
  | k + 1, i, m, E, s, ha0, ha1, _, hr => by
    obtain ⟨m1, d1, s1, E1, fr1, K1, V1, rg1⟩ := pv_sb F E s pv_at_9f4 (off' := 0x9F8) (c := c + i) (by decide)
      (by rw [ha0]; exact BitVec.add_zero _) (by omega)
    rw [s.zero] at V1
    obtain ⟨m2, c2, u2⟩ := s1.block pvZ E1.C.self pvZ_end ⟨trivial, trivial, trivial⟩
    have s2 : St m1.mem PV m2 0x9FC (reg m2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
    have a02 : reg m2 a0 = B + 0x420 + BitVec.ofNat 32 (c + (i + 1)) := by
      rw [u2.regs]; simp +decide only [runBlock, BInstr.run, pvZ, upd, ↓reduceIte, aluEval]
      rw [rg1, ha0, show (1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc, Nat.add_assoc]
    have a12 : reg m2 a1 = BitVec.ofNat 32 k := by
      rw [u2.regs]; simp +decide only [runBlock, BInstr.run, pvZ, upd, ↓reduceIte, aluEval]
      rw [rg1, ha1]; exact ofNat_dec k
    have k2 : ∀ q, q ≠ a0 → q ≠ a1 → reg m2 q = reg m q := fun q h0 h1 => by
      rw [u2.regs, runBlock_reg _ _ _ q s1.zero (by simp [pvZ, BInstr.dst, h0, h1]), rg1]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · obtain ⟨m3, d3, u3⟩ := s2.notTaken E1.C.self 0x9FE pv_at_9fc (by decide) (by rw [a12, s2.zero]; decide)
      refine ⟨m3, d1.trans (c2.trans (.single d3)), ⟨u3.pc, rfl, fun _ => rfl⟩, fun x hx => by
        rw [u3.mem, fr1 x hx], fun e he1 he2 => by rw [u3.mem]; exact K1 e he1 he2, fun j hj => ?_,
        fun q h0 h1 => by rw [u3.regs, k2 q h0 h1]⟩
      obtain rfl : j = 0 := by omega
      rw [u3.mem, Nat.add_zero]; exact V1
    · obtain ⟨m3, d3, u3⟩ := s2.taken E1.C.self 0x9F4 pv_at_9fc (by decide)
        (by rw [a12, s2.zero]; simp only [branchTaken]; exact bne_iff_ne.2 (ofNat_ne0 hk (by omega)))
      have s3 : St m3.mem PV m3 0x9F4 (reg m3) := ⟨u3.pc, rfl, fun _ => rfl⟩
      have E3 : PvEnv m3.mem := by rw [u3.mem]; exact E1
      obtain ⟨m4, c4, s4, fr4, K4, V4, k4⟩ := pv_zl F k (i + 1) E3 s3 (by rw [u3.regs, a02]) (by rw [u3.regs, a12])
        hk (by omega)
      refine ⟨m4, d1.trans (c2.trans (.cons d3 c4)), s4, fun x hx => by rw [fr4 x hx, u3.mem, fr1 x hx],
        fun e he1 he2 => ?_, fun j hj => ?_, fun q h0 h1 => by rw [k4 q h0 h1, u3.regs, k2 q h0 h1]⟩
      · rw [K4 e he1 (by omega), u3.mem, K1 e he1 (by omega)]
      · rcases Nat.eq_zero_or_pos j with rfl | hj0
        · rw [Nat.add_zero, K4 _ (by omega) (by omega), u3.mem]; exact V1
        · have := V4 (j - 1) (by omega)
          rwa [show c + (i + 1) + (j - 1) = c + i + j by omega] at this

theorem pv_regs_call {m m1 m2 : Machine} {S : Word} (r1 : ∀ r, r ≠ ra → reg m1 r = reg m r)
    (k2 : ∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m2 q = reg m1 q)
    (sp2 : reg m2 sp = S) (hsp : reg m sp = S) :
    ∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m2 q = reg m q := fun q hq => by
  by_cases h : q = sp
  · subst h; rw [sp2, hsp]
  · rw [k2 q (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]

set_option maxHeartbeats 8000000 in
/-- A call to `Uint<12>::to_be_byte_array`: the big-endian bytes of the
limbs at offset `cx` of the frame, at `co`; reversed, they are the limbs'
little-endian number. -/
theorem pv_tbb {B : Word} {m : Machine} {off : Nat} {imm o : Word} {co cx : Nat} (F : Fr B 0x21A0)
    (E : PvEnv5 m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 toBeBytes12Address)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 co)
    (ha1 : reg m a1 = B + 0x420 + BitVec.ofNat 32 cx) (hco : co + 48 ≤ 0x1D4C) (hcx : cx + 48 ≤ 0x1D4C)
    (acx : cx % 4 = 0) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem co 48 ∧
      leN (memBytes m'.mem (B + 0x420 + BitVec.ofNat 32 co) 48).reverse =
        accV m.mem (B + 0x420 + BitVec.ofNat 32 cx) 12 := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.E.E.E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  obtain ⟨n2, c2, pc2, sp2, k2, val2, fr2⟩ := toBeBytes12_correct n1 (by rw [mem1]; exact E.C5.tbb)
    (by rw [mem1]; exact E.E.E.E.C.K.za) (by rw [mem1]; exact E.E.E.E.C.K.stub) (by rw [mem1]; exact E.E.E.E.C.K.body)
    pc1 (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) (by rw [r1 sp (by decide)]; exact hsp) hFa (by omega)
    (by omega) (pv_al F (by omega) acx) (by rw [pv_at F cx (by omega)]; have := F.hi; omega)
    (by rw [pv_at F co (by omega)]; have := F.hi; omega) (FS.lowN (k := 0x90) (by decide) (by decide) (by omega))
    (FS.lowN (k := 0x90) (by decide) (by decide) (by omega))
  rw [mem1] at val2 fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_lo (k := 0x90) hx (by decide) (by decide))
      (pvR_hi hx hco), pv_regs_call r1 (fun q hq => k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide)) sp2 hsp⟩,
    fun e he1 he2 => fr2 _ (pv_lowB F (k := 0x90) (by decide) (by decide) (by omega))
      (sepS (B + 0x420) (by omega) (by omega) (by omega)), ?_⟩
  rw [val2]; exact leN_beLimbs12 _ _

set_option maxHeartbeats 8000000 in
/-- A call to `<[u8]>::reverse` on the `N` bytes at offset `c` of the frame. -/
theorem pv_rev {B : Word} {m : Machine} {off : Nat} {imm o : Word} {c N : Nat} (F : Fr B 0x21A0)
    (E : PvEnv5 m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 sliceReverseAddress)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 c)
    (ha1 : reg m a1 = BitVec.ofNat 32 N) (hc : c + N ≤ 0x1D4C) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem c N ∧
      memBytes m'.mem (B + 0x420 + BitVec.ofNat 32 c) N = (memBytes m.mem (B + 0x420 + BitVec.ofNat 32 c) N).reverse := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.E.E.E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  obtain ⟨n2, c2, pc2, val2, fr2, k2⟩ := sliceReverse_correct n1 (by rw [mem1]; exact E.C5.rev) pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1) (by omega)
    (by rw [pv_at F c (by omega)]; have := F.hi; omega) (FS.sepHi (by omega) (by decide) (by decide))
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1] at val2 fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (pvR_hi hx hc),
      fun q hq => by rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
        r1 q (by revert hq; revert q; decide)]⟩,
    fun e he1 he2 => fr2 _ (sepS (B + 0x420) (by omega) (by omega) (by omega)), ?_⟩
  apply List.ext_getElem (by simp [memBytes_length])
  intro i h1' h2'
  rw [memBytes_length] at h1'
  rw [List.getElem_reverse]
  simp only [memBytes, List.getElem_map, List.getElem_range, List.length_map, List.length_range]
  rw [val2 i h1']

/-- The digit bytes of a wNAF expansion in an `n`-byte buffer of zeros. -/
def wnafBytes (ds : List Int) (n : Nat) : List Nat :=
  (List.range n).map fun i => if i < ds.length then digB (ds.getD i 0) else 0

set_option maxHeartbeats 8000000 in
/-- A call to `zeroArray48` on offset `c` of the frame. -/
theorem pv_za {B : Word} {m : Machine} {off : Nat} {imm o : Word} {c : Nat} (F : Fr B 0x21A0)
    (E : PvEnv5 m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 zeroArray48Address)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 c) (hc : c + 48 ≤ 0x1D4C) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem c 48 ∧
      ∀ j, j < 48 → m'.mem (B + 0x420 + BitVec.ofNat 32 (c + j)) = 0 := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.E.E.E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  obtain ⟨n2, c2, pc2, sp2, k2, fr2⟩ := zeroArray48_correct n1 (by rw [mem1]; exact E.E.E.E.C.K.za)
    (by rw [mem1]; exact E.E.E.E.C.K.stub) (by rw [mem1]; exact E.E.E.E.C.K.body) pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
    (by rw [r1 sp (by decide)]; exact hsp) hFa (by omega) (by omega)
    (by rw [pv_at F c (by omega)]; have := F.hi; omega) (FS.lowN (k := 0x50) (by decide) (by decide) (by omega))
  rw [mem1] at fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => ?_,
      fun q hq => ?_⟩, fun e he1 he2 => ?_, fun j hj => ?_⟩
  · rw [fr2 x (pvR_lo (k := 0x50) hx (by decide) (by decide)), fillBytes_sep (pvR_hi hx hc) (Nat.le_refl _)]
  · by_cases h : q = sp
    · subst h; rw [sp2, hsp]
    · rw [k2 q (by revert hq h; revert q; decide) (by revert hq h; revert q; decide) (by revert hq h; revert q; decide)
        (by revert hq h; revert q; decide) (by revert hq h; revert q; decide) (by revert hq h; revert q; decide)
        (by revert hq h; revert q; decide) (by revert hq h; revert q; decide) (by revert hq h; revert q; decide)
        (by revert hq h; revert q; decide) (by revert hq h; revert q; decide) (by revert hq h; revert q; decide)
        (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]
  · rw [fr2 _ (pv_lowB F (k := 0x50) (by decide) (by decide) (by omega)),
      fillBytes_sep (sepS (B + 0x420) (by omega) (by omega) (by omega)) (Nat.le_refl _)]
  · rw [fr2 _ (pv_lowB F (k := 0x50) (by decide) (by decide) (by omega)), ← add_ofNat_assoc,
      fill_at hj (by decide)]

theorem getD_rep0 : ∀ (n i : Nat), (List.replicate n (0 : Nat)).getD i 0 = 0
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | n + 1, i + 1 => getD_rep0 n i

theorem digB_lt (d : Int) : digB d < 256 := by
  unfold digB; omega

set_option maxHeartbeats 8000000 in
/-- A call to `wnaf_form` with the 0x181-byte digit buffer of zeros at offset
`cw` of the frame and the 48 little-endian bytes of the number `X` at `cc`. -/
theorem pv_wf {B : Word} {m : Machine} {off : Nat} {imm o : Word} {cw cc X : Nat} (F : Fr B 0x21A0)
    (E : PvEnv5 m.mem) (s : St m.mem PV m off (reg m))
    (h1 : fetchRel p384VerifyPrehashCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel p384VerifyPrehashCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : PV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 wnafFormAddress)
    (he8 : (PV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x420) (ha0 : reg m a0 = B + 0x420 + BitVec.ofNat 32 cw)
    (ha1 : reg m a1 = BitVec.ofNat 32 0x181) (ha2 : reg m a2 = B + 0x420 + BitVec.ofNat 32 cc)
    (ha3 : reg m a3 = BitVec.ofNat 32 0x30) (ha4 : reg m a4 = BitVec.ofNat 32 0x180)
    (hcw : cw + 0x181 ≤ 0x1D4C) (hcc : cc + 0x30 ≤ 0x1D4C) (hs : cc + 0x30 ≤ cw ∨ cw + 0x181 ≤ cc)
    (hX : leN (memBytes m.mem (B + 0x420 + BitVec.ofNat 32 cc) 0x30) = X)
    (hZ : memBytes m.mem (B + 0x420 + BitVec.ofNat 32 cw) 0x181 = List.replicate 0x181 0) :
    ∃ m', PvPost B m m' (off + 8) ∧ PvKeep B m.mem m'.mem cw 0x181 ∧
      reg m' a0 = BitVec.ofNat 32 (wnafGo X 0x180 0x181 0 0).length ∧
      memBytes m'.mem (B + 0x420 + BitVec.ofNat 32 cw) 0x181 = wnafBytes (wnafGo X 0x180 0x181 0 0) 0x181 ∧
      (wnafGo X 0x180 0x181 0 0).length ≤ 0x181 := by
  have FS : Fr (B + 0x420) 0x1D80 := F.sub (c := 0x420) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  have h70 : (B + 0x420 + 0xFFFFFF90).toNat = (B + 0x420).toNat - 0x70 := FS.below 0x70 (by decide) (by decide)
  have e90 : B + 0x420 + 0xFFFFFF90 + 0xFFFFFFE0 = B + 0x420 + BitVec.ofNat 32 (2 ^ 32 - 0x90) := by
    rw [BitVec.add_assoc]; rfl
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.E.E.E.C.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have hbytes : ∀ b ∈ memBytes m.mem (B + 0x420 + BitVec.ofNat 32 cc) 0x30, b < 256 := fun b hb' => by
    unfold memBytes at hb'
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb'
    exact BitVec.isLt _
  have C : WfCtx n1.mem (B + 0x420 + 0xFFFFFF90) (B + 0x420 + BitVec.ofNat 32 cw) (B + 0x420 + BitVec.ofNat 32 cc)
      0x181 0x30 0x180 := by
    rw [mem1]
    refine ⟨E.C5.wf, E.E.E.E.C.K.mset, E.C5.il, E.E.E.E.C.K.stub, E.E.E.E.C.K.body, E.C5.lsh, E.C5.ash,
      E.E.E.E.C2.exu, E.E.E.E.C.K.panic, ⟨by omega, by omega, by unfold dramEnd; omega⟩,
      by unfold dramEnd; omega, by decide, by decide,
      by unfold dramEnd; rw [pv_at F cw (by omega)]; have := F.hi; omega,
      by rw [e90]; exact FS.lowN (k := 0x90) (by decide) (by decide) (by omega),
      by rw [pv_at F cc (by omega)]; have := F.hi; omega,
      by rw [e90]; exact FS.lowN (k := 0x90) (by decide) (by decide) (by omega),
      sepS (B + 0x420) (by omega) (by omega) (by omega), ?_⟩
    have := leN_lt _ hbytes
    rw [memBytes_length] at this
    exact this
  obtain ⟨n2, c2, pc2, sp2, k2, a02, dg2, tl2, hl2, fr2⟩ := wnafForm_correct n1 C pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
    (by rw [r1 a2 (by decide)]; exact ha2) (by rw [r1 a3 (by decide)]; exact ha3)
    (by rw [r1 a4 (by decide)]; exact ha4) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
    (by rw [r1 sp (by decide)]; exact hsp)
  rw [mem1] at a02 dg2 tl2 hl2 fr2
  have eS : wnafSpec (memBytes m.mem (B + 0x420 + BitVec.ofNat 32 cc) 0x30) 0x180 = wnafGo X 0x180 0x181 0 0 := by
    unfold wnafSpec; rw [hX]
  rw [eS] at a02 dg2 tl2 hl2
  have lo : ∀ x, PvR B x → Sep (B + 0x420 + 0xFFFFFF70) 0x90 x 1 := fun x hx => by
    have := pvR_lo (k := 0x90) hx (by decide) (by decide); exact this
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (lo x hx) (pvR_hi hx hcw),
      pv_regs_call r1 (fun q hq => k2 q (by revert hq; revert q; decide)) sp2 hsp⟩,
    fun e he1 he2 => fr2 _ (pv_lowB F (k := 0x90) (by decide) (by decide) (by omega))
      (sepS (B + 0x420) (by omega) (by omega) (by omega)), a02, ?_, hl2⟩
  apply List.ext_getElem (by simp [memBytes_length, wnafBytes])
  intro i h1' h2'
  rw [memBytes_length] at h1'
  simp only [memBytes, wnafBytes, List.getElem_map, List.getElem_range]
  by_cases hi : i < (wnafGo X 0x180 0x181 0 0).length
  · rw [ite_eq_left hi, dg2 i hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (digB_lt _)]
  · rw [ite_eq_right hi, tl2 i (by omega) h1']
    have := congrArg (·.getD i 0) hZ
    simp only [memBytes_getD h1'] at this
    rw [this, getD_rep0]

theorem memBytes_zero {M : Word → BitVec 8} {S : Word} {c N : Nat}
    (h : ∀ j, j < N → M (S + BitVec.ofNat 32 (c + j)) = 0) : memBytes M (S + BitVec.ofNat 32 c) N = List.replicate N 0 := by
  apply List.ext_getElem (by simp [memBytes_length])
  intro i h1 h2
  rw [memBytes_length] at h1
  simp only [memBytes, List.getElem_map, List.getElem_range, List.getElem_replicate]
  rw [add_ofNat_assoc, h i h1]; rfl

theorem memLoad32_cp {M M' : Word → BitVec 8} {S : Word} {c d : Nat}
    (h : ∀ q, q < 4 → M' (S + BitVec.ofNat 32 (c + q)) = M (S + BitVec.ofNat 32 (d + q))) :
    memLoad32 M' (S + BitVec.ofNat 32 c) = memLoad32 M (S + BitVec.ofNat 32 d) := by
  rw [ld_ofNat, ld_ofNat]
  simp only [add_ofNat_assoc]
  rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]

end C3.RV32.Pv
