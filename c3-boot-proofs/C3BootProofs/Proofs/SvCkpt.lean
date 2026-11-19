import C3BootProofs.Proofs.SvTpv
import C3BootProofs.Proofs.CheckpointLine
import C3BootProofs.Proofs.Base64Decode

/-!
# `sigstore::verify`: the checkpoint's lines

`verify_checkpoint` splits the checkpoint into lines with
`checkpoint::line`, whose result lands in `sigstore::verify`'s frame.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv

set_option maxRecDepth 20000

/-- The checkpoint code `sigstore::verify` calls, beyond `SvCode`. -/
structure SvCkCode (M : Word → BitVec 8) : Prop where
  line : CodeIn M (BitVec.ofNat 32 checkpointLineAddress) checkpointLineCode
  b64 : CodeIn M BDI base64DecodeIntoCode
  cw : CodeIn M BCW copyFromSliceU8Code

theorem SvCkCode.sv {M M0 : Word → BitVec 8} {B : Word} (F : Fr B 0x3830) (D : SvCkCode M0)
    (fR : ∀ x, SvR B x → M x = M0 x) : SvCkCode M := by
  have hx : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => fR x (sep_of_le (by
    have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega))
  exact ⟨codeHi D.line (by decide) (by decide) hx, codeHi D.b64 (by decide) (by decide) hx,
    codeHi D.cw (by decide) (by decide) hx⟩

theorem nlScan_congr {M M' : Word → BitVec 8} {p : Word} :
    ∀ (f k : Nat), (∀ i, k ≤ i → i < k + f → M (p + BitVec.ofNat 32 i) = M' (p + BitVec.ofNat 32 i)) →
      nlScan M p k f = nlScan M' p k f
  | 0, _, _ => rfl
  | f + 1, k, h => by
    simp only [nlScan]
    rw [h k (Nat.le_refl k) (by omega), nlScan_congr f (k + 1) fun i h1 h2 => h i (by omega) (by omega)]

theorem nlScan_lt {M : Word → BitVec 8} {p : Word} :
    ∀ (f k i : Nat), nlScan M p k f = some i → k ≤ i ∧ i < k + f
  | 0, _, _, h => by cases h
  | f + 1, k, i, h => by
    simp only [nlScan] at h
    by_cases hc : M (p + BitVec.ofNat 32 k) = 0x0A
    · simp only [hc, ↓reduceIte] at h
      cases h
      exact ⟨Nat.le_refl _, Nat.lt_add_of_pos_right (Nat.succ_pos f)⟩
    · simp only [hc, ↓reduceIte] at h
      obtain ⟨h1, h2⟩ := nlScan_lt f (k + 1) i h
      exact ⟨Nat.le_of_succ_le h1, by rw [Nat.add_succ, ← Nat.succ_add]; exact h2⟩

theorem nlScan_ro {B p : Word} {nl : Nat} {M M0 : Word → BitVec 8} (F : Fr B 0x3830)
    (fR : ∀ x, SvR B x → M x = M0 x) (h : SvRo B p nl) : nlScan M p 0 nl = nlScan M0 p 0 nl := by
  apply nlScan_congr
  intro i _ hi
  rcases h with h | ⟨h1, h2⟩
  · exact fR _ (h.r (by omega))
  · exact fR _ (dataR F h1 h2 i (by omega))

theorem sub_ofNat {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The bytes after a line's newline. -/
theorem line_rest {B p : Word} {nl i : Nat} (h : SvRo B p nl) (hi : i < nl) :
    SvRo B (p + BitVec.ofNat 32 (i + 1)) (nl - (i + 1)) := by
  rcases h with h | ⟨h1, h2⟩
  · exact .inl (h.drop (by omega))
  · have e : (p + BitVec.ofNat 32 (i + 1)).toNat = p.toNat + (i + 1) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    exact .inr ⟨by rw [e]; omega, by rw [e]; omega⟩

theorem SvRo.ne0 {B p : Word} {nl : Nat} (h : SvRo B p nl) : p ≠ 0 := by
  rcases h with h | ⟨h1, _⟩
  · exact h.pos_ne
  · intro e; rw [e] at h1; exact absurd h1 (by decide)

theorem br_bgeu_t {a b : Word} (h : ¬ a.toNat < b.toNat) : branchTaken .bgeu a b = true := by
  simp only [branchTaken, BitVec.ult, Bool.not_eq_true', decide_eq_false_iff_not]; exact h
theorem br_bgeu_f {a b : Word} (h : a.toNat < b.toNat) : branchTaken .bgeu a b = false := by
  simp only [branchTaken, BitVec.ult, Bool.not_eq_false', decide_eq_true_eq]; exact h

theorem br_blt0_t {a : Word} (h : ¬ a.toNat < 2 ^ 31) : branchTaken .blt a 0 = true := by
  simp only [branchTaken, BitVec.slt, BitVec.toInt, decide_eq_true_eq]
  have := a.isLt
  have h1 : ¬ (2 * a.toNat < 2 ^ 32) := by omega
  simp only [h1, ↓reduceIte, show BitVec.toNat (0 : Word) = 0 from rfl]
  omega
theorem br_blt0_f {a : Word} (h : a.toNat < 2 ^ 31) : branchTaken .blt a 0 = false := by
  simp only [branchTaken, BitVec.slt, BitVec.toInt, decide_eq_false_iff_not]
  have h1 : 2 * a.toNat < 2 ^ 32 := by omega
  simp only [h1, ↓reduceIte, show BitVec.toNat (0 : Word) = 0 from rfl]
  omega

theorem ne32_add {n : Nat} (h1 : n < 2 ^ 32) (h2 : n ≠ 32) : BitVec.ofNat 32 n + 0xFFFFFFE0 ≠ 0 := fun e => by
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  exact h2 (by simp only [show (0xFFFFFFE0 : Word).toNat = 2 ^ 32 - 32 from rfl,
    show (0 : Word).toNat = 0 from rfl] at this; omega)

/-- A byte minus `'0'` is zero exactly when the byte is `'0'`. -/
theorem digit0_iff : ∀ b : BitVec 8, b.zeroExtend 32 + 0xFFFFFFD0 = 0 ↔ b = 0x30 := by decide

/-- What `checkpoint::line` leaves at offset `oc` of the frame. -/
def LineW (M : Word → BitVec 8) (B : Word) (oc : Nat) (p : Word) (n : Nat) : Option Nat → Prop
  | none => memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 oc) = 0 ∧ M (B + 0x21A0 + BitVec.ofNat 32 (oc + 4)) = 0x1A
  | some i => memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 oc) = p ∧
      memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 4)) = BitVec.ofNat 32 i ∧
      memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 8)) = p + BitVec.ofNat 32 (i + 1) ∧
      memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (oc + 12)) = BitVec.ofNat 32 n - BitVec.ofNat 32 (i + 1)

set_option maxHeartbeats 8000000 in
/-- **A call to `checkpoint::line`** on the `nl` bytes at `p`, with the
result at offset `oc`. -/
theorem sv_lineF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o p : Word} {oc nl : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (CK : SvCkCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 checkpointLineAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc) (ha1 : reg n a1 = p)
    (ha2 : reg n a2 = BitVec.ofNat 32 nl) (ho2 : oc + 16 ≤ 0x1690) (ho3 : oc % 4 = 0) (hin : SvRo B p nl) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 16)] ∧ LineW n'.mem B oc p nl (nlScan M p 0 nl) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hf := hin.fit
  obtain ⟨n2, c2, pc2, mem2, k2⟩ := checkpointLine_correct n1 (base := BitVec.ofNat 32 checkpointLineAddress)
    (by rw [mem1]; exact CK.line) pc1 (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [r1 a2 (by decide), ha2]) (by omega) (sv_al F (by omega) ho3)
    (by rw [← sv_base']; exact F.sepHi (by omega) (by decide) (by decide))
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
  rw [mem1] at mem2
  have l4 := lit4 (B + 0x21A0) oc (by omega)
  have l8 := lit8 (B + 0x21A0) oc (by omega)
  have l12 := lit12 (B + 0x21A0) oc (by omega)
  have hO : ∀ x, Sep (B + 0x21A0 + BitVec.ofNat 32 oc) 16 x 1 → n2.mem x = M x := fun x hx => by
    have hs : ∀ c l, c + l ≤ 16 → Sep (B + 0x21A0 + BitVec.ofNat 32 (oc + c)) l x 1 := fun c l h => by
      have := hx.sub (c := c) (l := l) h; rwa [add_ofNat_assoc] at this
    have h0 := hs 0 4 (by omega)
    rw [Nat.add_zero] at h0
    rw [mem2]
    cases nlScan M p 0 nl with
    | none =>
      simp only [lineMem]
      rw [l4]
      have hne : x ≠ B + 0x21A0 + BitVec.ofNat 32 (oc + 4) := fun e => by
        have := hs 4 1 (by omega) 0 (by omega) 0 (by omega); rw [add_ofNat_zero, add_ofNat_zero] at this
        exact this e.symm
      rw [memStore8_ne hne, memStore32_get_sep h0]
    | some i =>
      simp only [lineMem]
      rw [l4, l8, show (0xC : Word) = 12 from rfl, l12]
      rw [memStore32_get_sep (hs 12 4 (by omega)), memStore32_get_sep (hs 8 4 (by omega)),
        memStore32_get_sep (hs 4 4 (by omega)), memStore32_get_sep h0]
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, fun q hq => ?_, fun e he hL => ?_, ?_,
    fun x hx => hO x (svR_hi hx ho2)⟩
  · have hq' : q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧ q ≠ ra := by revert hq; revert q; decide
    obtain ⟨q11, q12, q13, q14, q15, q1⟩ := hq'
    rw [k2 q q11 q12 q13 q14 q15, r1 q q1]
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    exact hO _ (sepS (B + 0x21A0) (by omega) (by omega) (by omega))
  · rw [mem2]
    cases nlScan M p 0 nl with
    | none =>
      simp only [LineW, lineMem]
      rw [l4]
      refine ⟨?_, memStore8_same _ _ _⟩
      rw [memLoad32_store8_sep (sepS (B + 0x21A0) (by omega) (by omega) (by omega)), memLoad32_store32_same]
    | some i =>
      simp only [LineW, lineMem]
      rw [l4, l8, show (0xC : Word) = 12 from rfl, l12]
      have z : B + 0x21A0 + BitVec.ofNat 32 oc = B + 0x21A0 + BitVec.ofNat 32 (oc + 0) := by rw [Nat.add_zero]
      rw [z]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [ld_st_ne (by omega) (by omega) (by omega), ld_st_ne (by omega) (by omega) (by omega),
          ld_st_ne (by omega) (by omega) (by omega), ld_st_eq rfl]
      · rw [ld_st_ne (by omega) (by omega) (by omega), ld_st_ne (by omega) (by omega) (by omega), ld_st_eq rfl]
      · rw [ld_st_ne (by omega) (by omega) (by omega), ld_st_eq rfl]
      · rw [ld_st_eq rfl]

theorem memBytes_range {M : Word → BitVec 8} {a : Word} {n : Nat} {L : Bytes} (h : memBytes M a n = L) :
    ∀ j, j < n → M (a + BitVec.ofNat 32 j) = BitVec.ofNat 8 (L.getD j 0) := fun j hj => by
  rw [← h, getD_memBytes M a hj, BitVec.ofNat_toNat, BitVec.setWidth_eq]

set_option maxHeartbeats 8000000 in
/-- **A call to `base64::decode_into`** on the `nl` bytes at `t`, with the
result at offset `rc` and the output buffer of `L` bytes at offset `oc`. -/
theorem sv_b64F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o t : Word} {rc oc nl L : Nat}
    (F : Fr B 0x3830) (C : SvCode M) (CK : SvCkCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BDI)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 rc) (ha1 : reg n a1 = t)
    (ha2 : reg n a2 = BitVec.ofNat 32 nl) (ha3 : reg n a3 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha4 : reg n a4 = BitVec.ofNat 32 L) (hr2 : rc + 8 ≤ 0x1690) (hr3 : rc % 4 = 0) (ho2 : oc + L ≤ 0x1690)
    (hs : rc + 8 ≤ oc ∨ oc + L ≤ rc) (hin : SvRo B t nl) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(rc, 8), (oc, L)] ∧
      (∀ bs, base64Decode (memBytes M t nl) = some bs → bs.length ≤ L →
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 rc) = 0 ∧
        memLoad32 n'.mem (B + 0x21A0 + BitVec.ofNat 32 (rc + 4)) = BitVec.ofNat 32 bs.length ∧
        memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 oc) bs.length = bs) ∧
      ((∀ bs, base64Decode (memBytes M t nl) = some bs → L < bs.length) →
        n'.mem (B + 0x21A0 + BitVec.ofNat 32 rc) = 1) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have hpl := hin.lo
  have eB : MCS + 8 = BMB := by decide
  obtain ⟨n2, c2, pc2, sp2, k2, ok2, bad2, f2⟩ := base64DecodeInto_correct n1 (sp0 := B + 0x21A0)
    (by rw [mem1]; exact CK.b64) (by rw [mem1]; exact CK.cw) (by rw [mem1]; exact C.K.stub)
    (by rw [mem1, ← eB]; exact C.K.body) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1]) (by rw [r1 a2 (by decide), ha2])
    (by rw [r1 a3 (by decide), ha3]) (by rw [r1 a4 (by decide), ha4])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) (by rw [r1 sp (by decide), rsp])
    (by rw [hS]; omega) (by rw [hS]; omega) (by rw [hS]; omega)
    (by rw [sv_at F _ (by omega)]; omega) (sv_al F (by omega) hr3) (by rw [sv_at F _ (by omega)]; omega)
    (by omega)
    (by rw [sv_sp50, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (by rw [sv_sp50]; exact (hin.sep F (c := 0x2150) (n := 0x50) (by decide)).symm)
    (by rw [sv_sp50, ← sv_base']; exact sepS B (by omega) (by omega) (by omega))
    (by rw [← sv_base']; exact (hin.sep F (c := 0x21A0 + oc) (n := L) (by omega)).symm)
    (sepS (B + 0x21A0) hs (by omega) (by omega))
  rw [mem1] at ok2 bad2 f2
  rw [sv_sp50] at f2
  have hfS : ∀ x, SvR B x → Sep (B + BitVec.ofNat 32 0x2150) 0x50 x 1 := fun x hx => by
    have := svR_lo (k := 0x50) hx (by decide) (by decide)
    rwa [sv_lo B 0x50 (by decide)] at this
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2,
    fun q hq => by rw [k2 q (by revert hq; revert q; decide), r1 q (by revert hq; revert q; decide)],
    fun e he hL => ?_, fun bs hd hl => ?_, bad2, fun x hx => f2 x (hfS x hx) (svR_hi hx ho2) (svR_hi hx hr2)⟩
  · have h1 := hL _ List.mem_cons_self
    have h2 := hL _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    simp only at h1 h2
    exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega)) (sepS (B + 0x21A0) (by omega) (by omega) (by omega))
  · obtain ⟨b0, b4, bm⟩ := ok2 bs hd hl
    exact ⟨b0, by rw [← add_ofNat_assoc]; exact b4, bm⟩

/-- **A call to `memset`** on `N` bytes at offset `c`, stated as a step of a
stage. -/
theorem sv_ms2F {n : Machine} {B : Word} {off : Nat} {imm o v : Word} {c N : Nat}
    (F : Fr B 0x3830) (C : SvCode n.mem) (s : St n.mem SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = MSET) (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 c) (ha1 : reg n a1 = v) (ha2 : reg n a2 = BitVec.ofNat 32 N)
    (hc : c + N ≤ 0x1690) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B n.mem n'.mem [(c, N)] ∧ (∀ x, SvR B x → n'.mem x = n.mem x) := by
  obtain ⟨n', st, s', mem', regs'⟩ := sv_msF F C s h1 h2 hb hev ha0 ha1 ha2 hc
  refine ⟨n', st, s', fun q hq => regs' q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    (by revert hq; revert q; decide) (by revert hq; revert q; decide), fun e he hL => ?_,
    fun x hx => by rw [mem']; exact fillBytes_sep (svR_hi hx hc) (Nat.le_refl N)⟩
  have h1 := hL _ (List.mem_singleton_self _)
  simp only at h1
  rw [mem']
  exact fillBytes_sep (sepS (B + 0x21A0) (by omega) (by omega) (by omega)) (Nat.le_refl N)

end C3.RV32.Sv
