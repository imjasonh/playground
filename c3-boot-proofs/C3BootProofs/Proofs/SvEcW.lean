import C3BootProofs.Proofs.SvEcPt
import C3BootProofs.Proofs.Pv384Lib4
import C3BootProofs.Proofs.ToBeBytes

/-!
# `sigstore::verify`: the P-256 check's wNAF digits

Before computing each scalar's width-5 NAF digits, the check clears a
257-byte buffer one byte at a time. `ec_zloop` proves that loop.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 100000

def ecZ1 : List BInstr := [.sb a0 x0 0x0, .aluImm .add a0 a0 0x1, .aluImm .add a1 a1 0xFFFFFFFF]
theorem ecZ1_end : blockEnd sigstoreVerifyCode 0x184E ecZ1 = some 0x1856 := by decide

set_option maxHeartbeats 4000000 in
/-- **The clearing loop** at 0x184E: with `j` bytes left from frame offset
`c + i`, it zeroes them and leaves at 0x1858. -/
theorem ec_zloop {B : Word} (F : Fr B 0x3830) {c N : Nat} (hN : c + N ≤ 0x1690) :
    ∀ j i {m : Machine} {Mx : Word → BitVec 8}, i + j = N → 0 < j → CodeIn Mx SV sigstoreVerifyCode →
      St Mx SV m 0x184E (reg m) → reg m a0 = B + 0x21A0 + BitVec.ofNat 32 (c + i) → reg m a1 = BitVec.ofNat 32 j →
      ∃ m' Mx', Steps m m' ∧ St Mx' SV m' 0x1858 (reg m') ∧ CodeIn Mx' SV sigstoreVerifyCode ∧
        (∀ q : Fin 32, q ≠ a0 → q ≠ a1 → reg m' q = reg m q) ∧
        (∀ t, t < j → Mx' (B + 0x21A0 + BitVec.ofNat 32 (c + i + t)) = 0) ∧
        (∀ x, Sep (B + 0x21A0 + BitVec.ofNat 32 (c + i)) j x 1 → Mx' x = Mx x) := by
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  intro j
  induction j with
  | zero => intro _ _ _ _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ j ih =>
    intro i m Mx hij _ hc st h0 h1
    have hz := st.zero
    have hsc : Sep (B + 0x21A0 + BitVec.ofNat 32 (c + i)) 1 SV sigstoreVerifyCode.length :=
      FS.sepHi (by omega) (by decide) (by decide)
    obtain ⟨m1, c1, u1⟩ := st.block ecZ1 hc ecZ1_end (by
      simp +decide only [BlockOk, BInstr.ok, ecZ1, and_true]
      rw [h0, show (0x0 : Word) = BitVec.ofNat 32 0 from rfl, add_ofNat_zero]; exact hsc)
    have M1 : (runBlock ecZ1 (Mx, reg m)).1 = memStore8 Mx (B + 0x21A0 + BitVec.ofNat 32 (c + i)) 0 := by
      simp +decide only [runBlock, BInstr.run, ecZ1, upd, ↓reduceIte]
      rw [h0, hz, show (0x0 : Word) = BitVec.ofNat 32 0 from rfl, add_ofNat_zero]; rfl
    have C1 : CodeIn (runBlock ecZ1 (Mx, reg m)).1 SV sigstoreVerifyCode := by rw [M1]; exact hc.store8 hsc
    have s1 : St (runBlock ecZ1 (Mx, reg m)).1 SV m1 0x1856 (reg m1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
    have r1a0 : reg m1 a0 = B + 0x21A0 + BitVec.ofNat 32 (c + (i + 1)) := by
      rw [u1.regs]; simp +decide only [runBlock, BInstr.run, ecZ1, upd, ↓reduceIte, aluEval]
      rw [h0, show (0x1 : Word) = BitVec.ofNat 32 1 from rfl, add_ofNat_assoc, show c + i + 1 = c + (i + 1) by omega]
    have r1a1 : reg m1 a1 = BitVec.ofNat 32 j := by
      rw [u1.regs]; simp +decide only [runBlock, BInstr.run, ecZ1, upd, ↓reduceIte, aluEval]
      rw [h1]; exact ofNat_pred j
    have k1 : ∀ q : Fin 32, q ≠ a0 → q ≠ a1 → reg m1 q = reg m q := fun q h0' h1' => by
      have hq : q ∉ ecZ1.filterMap BInstr.dst := by
        simp only [ecZ1, List.filterMap_cons, List.filterMap_nil, BInstr.dst, List.mem_cons, List.mem_nil_iff,
          or_false, not_or]; exact ⟨h0', h1'⟩
      rw [u1.regs, runBlock_reg _ _ _ q hz hq]
    have fr1 : ∀ x, x ≠ B + 0x21A0 + BitVec.ofNat 32 (c + i) → (runBlock ecZ1 (Mx, reg m)).1 x = Mx x :=
      fun x hx => by rw [M1, memStore8_ne hx]
    have z1 : (runBlock ecZ1 (Mx, reg m)).1 (B + 0x21A0 + BitVec.ofNat 32 (c + i)) = 0 := by
      rw [M1, memStore8_same]
    by_cases hj : j = 0
    · subst hj
      obtain ⟨m2, d2, u2⟩ := s1.notTaken C1 0x1858 sv_at_1856 (by decide)
        (by show (reg m1 a1 != reg m1 x0) = false; rw [r1a1, s1.zero]; rfl)
      refine ⟨m2, _, c1.trans (.single d2), u2.self, C1, fun q h0' h1' => by rw [u2.regs, k1 q h0' h1'],
        fun t ht => by obtain rfl : t = 0 := by omega
                       exact z1, fun x hx => fr1 x fun e => ?_⟩
      have := hx 0 (by decide) 0 (by decide); rw [add_ofNat_zero, add_ofNat_zero] at this; exact this e.symm
    · have hne : reg m1 a1 ≠ 0 := by
        rw [r1a1]; intro e
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), show (0 : Word).toNat = 0 from rfl] at this
        exact hj this
      obtain ⟨m2, d2, u2⟩ := s1.taken C1 0x184E sv_at_1856 (by decide)
        (by show (reg m1 a1 != reg m1 x0) = true; rw [s1.zero, bne_iff_ne]; exact hne)
      obtain ⟨m3, M3, c3, s3, C3, k3, z3, f3⟩ := ih (i + 1) (by omega) (Nat.pos_of_ne_zero hj) C1 u2.self
        (by rw [u2.regs, r1a0]) (by rw [u2.regs, r1a1])
      refine ⟨m3, M3, c1.trans (.cons d2 c3), s3, C3, fun q h0' h1' => by rw [k3 q h0' h1', u2.regs, k1 q h0' h1'],
        fun t ht => ?_, fun x hx => ?_⟩
      · rcases t with _ | t
        · rw [Nat.add_zero, f3 _ (sepS (B + 0x21A0) (c := c + (i + 1)) (n := j) (d := c + i) (k := 1)
            (Or.inr (by omega)) (by omega) (by omega)), z1]
        · rw [show c + i + (t + 1) = c + (i + 1) + t by omega]; exact z3 t (by omega)
      · rw [f3 x (hx.sub (c := 1) (l := j) (by omega) |> fun h => by
            rw [add_ofNat_assoc, show c + i + 1 = c + (i + 1) by omega] at h; exact h)]
        exact fr1 x fun e => by
          have := hx 0 (by omega) 0 (by decide); rw [add_ofNat_zero, add_ofNat_zero] at this; exact this e.symm

/-- The code that makes the wNAF digits. -/
structure SvWnCode (M : Word → BitVec 8) : Prop where
  tbb : CodeIn M (BitVec.ofNat 32 toBeBytes8Address) toBeBytes8Code
  z32 : CodeIn M (BitVec.ofNat 32 shaZero32Address) shaZero32Code
  rev : CodeIn M (BitVec.ofNat 32 sliceReverseAddress) sliceReverseCode
  wf : CodeIn M WF wnafFormCode
  il : CodeIn M (BitVec.ofNat 32 incrementLimbAddress) incrementLimbCode
  lsh : CodeIn M (BitVec.ofNat 32 lshrdi3Address) lshrdi3Code
  ash : CodeIn M (BitVec.ofNat 32 ashldi3Address) ashldi3Code
  exu : CodeIn M (BitVec.ofNat 32 expectUsizeAddress) expectUsizeCode

theorem SvWnCode.sv {M M0 : Word → BitVec 8} {B : Word} (F : Fr B 0x3830) (D : SvWnCode M0)
    (fR : ∀ x, SvR B x → M x = M0 x) : SvWnCode M := by
  have hx : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => fR x (sep_of_le (by
    have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega))
  exact ⟨codeHi D.tbb (by decide) (by decide) hx, codeHi D.z32 (by decide) (by decide) hx,
    codeHi D.rev (by decide) (by decide) hx, codeHi D.wf (by decide) (by decide) hx,
    codeHi D.il (by decide) (by decide) hx, codeHi D.lsh (by decide) (by decide) hx,
    codeHi D.ash (by decide) (by decide) hx, codeHi D.exu (by decide) (by decide) hx⟩

theorem leN_beLimbs8' (M : Word → BitVec 8) (s : Word) :
    ∀ j, j ≤ 8 → leN (beLimbs M s 7 j).reverse = accV M (s + BitVec.ofNat 32 (4 * (8 - j))) j
  | 0, _ => rfl
  | j + 1, hj => by
    rw [beLimbs_succ, List.reverse_append, leN_append, leN_wordBytes, List.length_reverse,
      show (Sha256.wordBytes _).length = 4 from rfl, leN_beLimbs8' M s j (by omega), accV_cons,
      show s + BitVec.ofNat 32 (4 * (8 - (j + 1))) + 4 = s + BitVec.ofNat 32 (4 * (8 - j)) by
        rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]; congr 2; omega,
      show 4 * (7 - j) = 4 * (8 - (j + 1)) by omega]

theorem leN_beLimbs8 (M : Word → BitVec 8) (s : Word) : leN (beLimbs M s 7 8).reverse = accV M s 8 := by
  rw [leN_beLimbs8' M s 8 (Nat.le_refl _), Nat.sub_self, Nat.mul_zero, add_ofNat_zero]

set_option maxHeartbeats 8000000 in
/-- **A call to `to_be_byte_array` for 8 limbs** at offset `cx`, into offset
`co`. -/
theorem sv_tbb8 {B : Word} {m : Machine} {off : Nat} {imm o : Word} {co cx : Nat} (F : Fr B 0x3830)
    (E : SvCode m.mem) (WC : SvWnCode m.mem) (s : St m.mem SV m off (reg m))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 toBeBytes8Address)
    (he8 : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x21A0) (ha0 : reg m a0 = B + 0x21A0 + BitVec.ofNat 32 co)
    (ha1 : reg m a1 = B + 0x21A0 + BitVec.ofNat 32 cx) (hco : co + 32 ≤ 0x1690) (hcx : cx + 32 ≤ 0x1690)
    (acx : cx % 4 = 0) :
    ∃ m', SvPost B m m' (off + 8) ∧ SvKeep B m.mem m'.mem co 32 ∧
      leN (memBytes m'.mem (B + 0x21A0 + BitVec.ofNat 32 co) 32).reverse =
        accV m.mem (B + 0x21A0 + BitVec.ofNat 32 cx) 8 := by
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  obtain ⟨n2, c2, pc2, sp2, k2, val2, fr2⟩ := toBeBytes8_correct n1 (by rw [mem1]; exact WC.tbb)
    (by rw [mem1]; exact WC.z32) (by rw [mem1]; exact E.K.stub) (by rw [mem1]; exact E.K.body)
    pc1 (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8) (by rw [r1 sp (by decide)]; exact hsp) hFa (by omega)
    (by omega) (sv_al F (by omega) acx) (by rw [sv_at F cx (by omega)]; have := F.hi; omega)
    (by rw [sv_at F co (by omega)]; have := F.hi; omega) (FS.lowN (k := 0x70) (by decide) (by decide) (by omega))
    (FS.lowN (k := 0x70) (by decide) (by decide) (by omega))
  rw [mem1] at val2 fr2
  have lo : ∀ x, SvR B x → Sep (B + 0x21A0 + 0xFFFFFF90) 0x70 x 1 := fun x hx => svR_lo (k := 0x70) hx (by decide) (by decide)
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (lo x hx) (svR_hi hx hco),
      fun q hq => ?_⟩, fun e he1 he2 => ?_, ?_⟩
  · by_cases h : q = sp
    · subst h; rw [sp2, hsp]
    · have hq' := hq
      rw [k2 q (by revert hq' h; revert q; decide) (by revert hq' h; revert q; decide) (by revert hq' h; revert q; decide)
        (by revert hq' h; revert q; decide) (by revert hq' h; revert q; decide) (by revert hq' h; revert q; decide)
        (by revert hq' h; revert q; decide) (by revert hq' h; revert q; decide) (by revert hq' h; revert q; decide)
        (by revert hq' h; revert q; decide) (by revert hq' h; revert q; decide) (by revert hq' h; revert q; decide)
        (by revert hq' h; revert q; decide) (by revert hq' h; revert q; decide) (by revert hq' h; revert q; decide),
        r1 q (by revert hq; revert q; decide)]
  · exact fr2 _ (FS.lowB (FS.below 0x70 (by decide) (by decide)) (by decide) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega))
  · rw [val2]; exact leN_beLimbs8 _ _

set_option maxHeartbeats 8000000 in
/-- **A call to `<[u8]>::reverse`** on the `N` bytes at offset `c`. -/
theorem sv_rev {B : Word} {m : Machine} {off : Nat} {imm o : Word} {c N : Nat} (F : Fr B 0x3830)
    (E : SvCode m.mem) (WC : SvWnCode m.mem) (s : St m.mem SV m off (reg m))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 sliceReverseAddress)
    (he8 : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : reg m a0 = B + 0x21A0 + BitVec.ofNat 32 c) (ha1 : reg m a1 = BitVec.ofNat 32 N) (hc : c + N ≤ 0x1690) :
    ∃ m', SvPost B m m' (off + 8) ∧ SvKeep B m.mem m'.mem c N ∧
      memBytes m'.mem (B + 0x21A0 + BitVec.ofNat 32 c) N = (memBytes m.mem (B + 0x21A0 + BitVec.ofNat 32 c) N).reverse := by
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  obtain ⟨n2, c2, pc2, val2, fr2, k2⟩ := sliceReverse_correct n1 (by rw [mem1]; exact WC.rev) pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1) (by omega)
    (by rw [sv_at F c (by omega)]; have := F.hi; omega) (FS.sepHi (by omega) (by decide) (by decide))
    (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
  rw [mem1] at val2 fr2
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (svR_hi hx hc),
      fun q hq => by rw [k2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide),
        r1 q (by revert hq; revert q; decide)]⟩,
    fun e he1 he2 => fr2 _ (sepS (B + 0x21A0) (by omega) (by omega) (by omega)), ?_⟩
  apply List.ext_getElem (by simp [memBytes_length])
  intro i h1' h2'
  rw [memBytes_length] at h1'
  rw [List.getElem_reverse]
  simp only [memBytes, List.getElem_map, List.getElem_range, List.length_map, List.length_range]
  rw [val2 i h1']

set_option maxHeartbeats 8000000 in
/-- **A call to `wnaf_form`** with the 0x101-byte digit buffer of zeros at
offset `cw` and the 32 little-endian bytes of the number `X` at `cc`. -/
theorem sv_wf {B : Word} {m : Machine} {off : Nat} {imm o : Word} {cw cc X : Nat} (F : Fr B 0x3830)
    (E : SvCode m.mem) (WC : SvWnCode m.mem) (s : St m.mem SV m off (reg m))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 wnafFormAddress)
    (he8 : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (hsp : reg m sp = B + 0x21A0) (ha0 : reg m a0 = B + 0x21A0 + BitVec.ofNat 32 cw)
    (ha1 : reg m a1 = BitVec.ofNat 32 0x101) (ha2 : reg m a2 = B + 0x21A0 + BitVec.ofNat 32 cc)
    (ha3 : reg m a3 = BitVec.ofNat 32 0x20) (ha4 : reg m a4 = BitVec.ofNat 32 0x100)
    (hcw : cw + 0x101 ≤ 0x1690) (hcc : cc + 0x20 ≤ 0x1690) (hs : cc + 0x20 ≤ cw ∨ cw + 0x101 ≤ cc)
    (hX : leN (memBytes m.mem (B + 0x21A0 + BitVec.ofNat 32 cc) 0x20) = X)
    (hZ : memBytes m.mem (B + 0x21A0 + BitVec.ofNat 32 cw) 0x101 = List.replicate 0x101 0) :
    ∃ m', SvPost B m m' (off + 8) ∧ SvKeep B m.mem m'.mem cw 0x101 ∧
      reg m' a0 = BitVec.ofNat 32 (wnafGo X 0x100 0x101 0 0).length ∧
      memBytes m'.mem (B + 0x21A0 + BitVec.ofNat 32 cw) 0x101 = wnafBytes (wnafGo X 0x100 0x101 0 0) 0x101 ∧
      (wnafGo X 0x100 0x101 0 0).length ≤ 0x101 := by
  have FS : Fr (B + 0x21A0) 0x1690 := F.sub (c := 0x21A0) (by decide) (by decide)
  have hFa := FS.al; have hFl := FS.lo; have hFh := FS.hi
  have e90 : B + 0x21A0 + 0xFFFFFF90 + 0xFFFFFFE0 = B + 0x21A0 + BitVec.ofNat 32 (2 ^ 32 - 0x90) := by
    rw [BitVec.add_assoc]; rfl
  have h70 : (B + 0x21A0 + 0xFFFFFF90).toNat = (B + 0x21A0).toNat - 0x70 := FS.below 0x70 (by decide) (by decide)
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have hBl := F.lo; have hBh := F.hi; have hBa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa E.self h1 h2 hb (by decide)
  have r1 : ∀ r, r ≠ ra → reg n1 r = reg m r := fun r h => by rw [regs1]; exact updz s.zero h
  have hbytes : ∀ b ∈ memBytes m.mem (B + 0x21A0 + BitVec.ofNat 32 cc) 0x20, b < 256 := fun b hb' => by
    unfold memBytes at hb'
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb'
    exact BitVec.isLt _
  have C : WfCtx n1.mem (B + 0x21A0 + 0xFFFFFF90) (B + 0x21A0 + BitVec.ofNat 32 cw) (B + 0x21A0 + BitVec.ofNat 32 cc)
      0x101 0x20 0x100 := by
    rw [mem1]
    refine ⟨WC.wf, E.K.mset, WC.il, E.K.stub, E.K.body, WC.lsh, WC.ash, WC.exu, E.K.panic,
      ⟨by rw [h70, hS]; omega, by rw [h70, hS]; omega, by rw [h70, hS]; unfold dramEnd; omega⟩,
      by rw [h70, hS]; unfold dramEnd; omega, by decide, by decide,
      by unfold dramEnd; rw [sv_at F cw (by omega)]; have := F.hi; omega,
      by rw [e90]; exact FS.lowN (k := 0x90) (by decide) (by decide) (by omega),
      by rw [sv_at F cc (by omega)]; have := F.hi; omega,
      by rw [e90]; exact FS.lowN (k := 0x90) (by decide) (by decide) (by omega),
      sepS (B + 0x21A0) (by omega) (by omega) (by omega), ?_⟩
    have := leN_lt _ hbytes
    rw [memBytes_length] at this
    exact this
  obtain ⟨n2, c2, pc2, sp2, k2, a02, dg2, tl2, hl2, fr2⟩ := wnafForm_correct n1 C pc1
    (by rw [r1 a0 (by decide)]; exact ha0) (by rw [r1 a1 (by decide)]; exact ha1)
    (by rw [r1 a2 (by decide)]; exact ha2) (by rw [r1 a3 (by decide)]; exact ha3)
    (by rw [r1 a4 (by decide)]; exact ha4) (by rw [regs1]; simp +decide [upd]) (even_clear _ he8)
    (by rw [r1 sp (by decide)]; exact hsp)
  rw [mem1] at a02 dg2 tl2 hl2 fr2
  have eS : wnafSpec (memBytes m.mem (B + 0x21A0 + BitVec.ofNat 32 cc) 0x20) 0x100 = wnafGo X 0x100 0x101 0 0 := by
    unfold wnafSpec; rw [hX]
  rw [eS] at a02 dg2 tl2 hl2
  have lo : ∀ x, SvR B x → Sep (B + 0x21A0 + 0xFFFFFF70) 0x90 x 1 := fun x hx => svR_lo (k := 0x90) hx (by decide) (by decide)
  refine ⟨n2, ⟨c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun x hx => fr2 x (lo x hx) (svR_hi hx hcw),
      fun q hq => by
        by_cases h : q = sp
        · subst h; rw [sp2]; exact hsp.symm
        · rw [k2 q (by revert hq h; revert q; decide), r1 q (by revert hq; revert q; decide)]⟩,
    fun e he1 he2 => fr2 _ (FS.lowB (FS.below 0x90 (by decide) (by decide)) (by decide) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega)), a02, ?_, hl2⟩
  apply List.ext_getElem (by simp [memBytes_length, wnafBytes])
  intro i h1' h2'
  rw [memBytes_length] at h1'
  simp only [memBytes, wnafBytes, List.getElem_map, List.getElem_range]
  by_cases hi : i < (wnafGo X 0x100 0x101 0 0).length
  · rw [ite_eq_left hi, dg2 i hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (digB_lt _)]
  · rw [ite_eq_right hi, tl2 i (by omega) h1']
    have := congrArg (·.getD i 0) hZ
    simp only [memBytes_getD h1'] at this
    rw [this, getD_rep0]

theorem SvKeep.mb {B : Word} {M M' : Word → BitVec 8} {c w d N : Nat} (K : SvKeep B M M' c w)
    (hd : d + N ≤ 0x1690) (h : d + N ≤ c ∨ c + w ≤ d) :
    memBytes M' (B + 0x21A0 + BitVec.ofNat 32 d) N = memBytes M (B + 0x21A0 + BitVec.ofNat 32 d) N :=
  memBytes_congr fun j hj => by rw [add_ofNat_assoc]; exact K.range hd h j hj

theorem SvKeepL.mb {B : Word} {M M' : Word → BitVec 8} {L : List (Nat × Nat)} {d N : Nat} (K : SvKeepL B M M' L)
    (hd : d + N ≤ 0x1690) (h : ∀ p ∈ L, d + N ≤ p.1 ∨ p.1 + p.2 ≤ d) :
    memBytes M' (B + 0x21A0 + BitVec.ofNat 32 d) N = memBytes M (B + 0x21A0 + BitVec.ofNat 32 d) N :=
  memBytes_congr fun j hj => by rw [add_ofNat_assoc]; exact K.range hd h j hj

end C3.RV32.Sv
