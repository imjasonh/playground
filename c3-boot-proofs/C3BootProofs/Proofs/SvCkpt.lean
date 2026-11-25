import C3BootProofs.Proofs.SvTpv
import C3BootProofs.Proofs.CheckpointLine
import C3BootProofs.Proofs.Base64Decode
import C3BootProofs.Proofs.StripPrefix

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
  spf : CodeIn M (BitVec.ofNat 32 stripPrefixAddress) stripPrefixCode

theorem SvCkCode.sv {M M0 : Word → BitVec 8} {B : Word} (FW : Fr (B + 0xFFFFEC10) 0x3A50) (D : SvCkCode M0)
    (fR : ∀ x, SvR B x → M x = M0 x) : SvCkCode M := by
  have hx : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => fR x (svR_hiMem (sv_frW FW) hx)
  exact ⟨codeHi D.line (by decide) (by decide) hx, codeHi D.b64 (by decide) (by decide) hx,
    codeHi D.cw (by decide) (by decide) hx, codeHi D.spf (by decide) (by decide) hx⟩

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

theorem nlScan_ro {B p : Word} {nl : Nat} {M M0 : Word → BitVec 8} (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (fR : ∀ x, SvR B x → M x = M0 x) (h : SvRo B p nl) : nlScan M p 0 nl = nlScan M0 p 0 nl := by
  apply nlScan_congr
  intro i _ hi
  rcases h with h | ⟨h1, h2⟩
  · exact sv_pt fR h i (by omega)
  · exact fR _ (dataR FW h1 h2 i (by omega))

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
    (F : Fr B 0x2660) (C : SvCode M) (CK : SvCkCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 checkpointLineAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc) (ha1 : reg n a1 = p)
    (ha2 : reg n a2 = BitVec.ofNat 32 nl) (ho2 : oc + 16 ≤ 0x4C0) (ho3 : oc % 4 = 0) (hin : SvRo B p nl) :
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

theorem sv_sp50 (B : Word) : B + 0x21A0 + 0xFFFFFFB0 = B + BitVec.ofNat 32 0x2150 := by
  rw [BitVec.add_assoc]; rfl

theorem memBytes_range {M : Word → BitVec 8} {a : Word} {n : Nat} {L : Bytes} (h : memBytes M a n = L) :
    ∀ j, j < n → M (a + BitVec.ofNat 32 j) = BitVec.ofNat 8 (L.getD j 0) := fun j hj => by
  rw [← h, getD_memBytes M a hj, BitVec.ofNat_toNat, BitVec.setWidth_eq]

set_option maxHeartbeats 8000000 in
/-- **A call to `base64::decode_into`** on the `nl` bytes at `t`, with the
result at offset `rc` and the output buffer of `L` bytes at offset `oc`. -/
theorem sv_b64F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o t : Word} {rc oc nl L : Nat}
    (F : Fr B 0x2660) (C : SvCode M) (CK : SvCkCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BDI)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 rc) (ha1 : reg n a1 = t)
    (ha2 : reg n a2 = BitVec.ofNat 32 nl) (ha3 : reg n a3 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha4 : reg n a4 = BitVec.ofNat 32 L) (hr2 : rc + 8 ≤ 0x4C0) (hr3 : rc % 4 = 0) (ho2 : oc + L ≤ 0x4C0)
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
  obtain ⟨n2, c2, pc2, sp2, k2, ok2, bad2, -, f2⟩ := base64DecodeInto_correct n1 (sp0 := B + 0x21A0)
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
    (F : Fr B 0x2660) (C : SvCode n.mem) (s : St n.mem SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = MSET) (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 c) (ha1 : reg n a1 = v) (ha2 : reg n a2 = BitVec.ofNat 32 N)
    (hc : c + N ≤ 0x4C0) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧
      (∀ q : Fin 32, q.val ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B n.mem n'.mem [(c, N)] ∧ (∀ x, SvR B x → n'.mem x = n.mem x) := by
  have hFh := F.hi
  obtain ⟨n', st, s', mem', regs'⟩ := c_memset s C.self C.K h1 h2 hb hev ha0 ha1 ha2
    (by rw [sv_at F _ (by omega)]; omega) (by rw [← sv_base']; exact F.sepHi (by omega) (by decide) (by decide))
  refine ⟨n', st, s', fun q hq => regs' q (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
    (by revert hq; revert q; decide) (by revert hq; revert q; decide), fun e he hL => ?_,
    fun x hx => by rw [mem']; exact fillBytes_sep (svR_hi hx hc) (Nat.le_refl N)⟩
  have h1 := hL _ (List.mem_singleton_self _)
  simp only at h1
  rw [mem']
  exact fillBytes_sep (sepS (B + 0x21A0) (by omega) (by omega) (by omega)) (Nat.le_refl N)

/-- The little-endian word of bytes `i` to `i + 3` of `L`. -/
def le4 (L : Bytes) (i : Nat) : Word :=
  BitVec.ofNat 8 (L.getD (i + 3) 0) ++ BitVec.ofNat 8 (L.getD (i + 2) 0) ++ BitVec.ofNat 8 (L.getD (i + 1) 0) ++
    BitVec.ofNat 8 (L.getD i 0)

theorem ld_digest {M : Word → BitVec 8} {a : Word} {n : Nat} {L : Bytes} (h : memBytes M a n = L) (hn : 4 ≤ n) :
    memLoad32 M a = le4 L 0 := by
  have r := memBytes_range h
  unfold memLoad32 le4
  rw [show a = a + BitVec.ofNat 32 0 from (add_ofNat_zero a).symm, add_ofNat_zero,
    show (3 : Word) = BitVec.ofNat 32 3 from rfl, show (2 : Word) = BitVec.ofNat 32 2 from rfl,
    show (1 : Word) = BitVec.ofNat 32 1 from rfl, r 3 (by omega), r 2 (by omega), r 1 (by omega)]
  have h0 := r 0 (by omega)
  rw [add_ofNat_zero] at h0
  rw [h0]

theorem partsBytes_four (M : Word → BitVec 8) (P : Word) :
    partsBytes M P 4 = memBytes M (partPtr M P 0) (partLen M P 0) ++ memBytes M (partPtr M P 1) (partLen M P 1) ++
      memBytes M (partPtr M P 2) (partLen M P 2) ++ memBytes M (partPtr M P 3) (partLen M P 3) := by
  simp only [partsBytes, List.nil_append]

theorem partPtr_at {M : Word → BitVec 8} {B p : Word} {pc i : Nat}
    (h : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + 8 * i)) = p) :
    partPtr M (B + 0x21A0 + BitVec.ofNat 32 pc) i = p := by
  unfold partPtr; rw [add_ofNat_assoc]; exact h

theorem partLen_at {M : Word → BitVec 8} {B : Word} {pc i l : Nat} (hl : l < 2 ^ 32)
    (h : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + (8 * i + 4))) = BitVec.ofNat 32 l) :
    partLen M (B + 0x21A0 + BitVec.ofNat 32 pc) i = l := by
  unfold partLen; rw [add_ofNat_assoc, h, BitVec.toNat_ofNat]; omega

set_option maxHeartbeats 8000000 in
/-- **A call to `c3_crypto::sha::sha256_parts`** on four slices whose
descriptors are at offset `pc`, with the digest at offset `oc`. -/
theorem sv_sha256P4F {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o p0 p1 p2 p3 : Word}
    {oc pc l0 l1 l2 l3 : Nat}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (C : SvCode M) (SC : SvSha2Code M) (RS : SvRoSep B) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 sha256PartsAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = B + 0x21A0 + BitVec.ofNat 32 oc)
    (ha1 : reg n a1 = B + 0x21A0 + BitVec.ofNat 32 pc) (ha2 : reg n a2 = BitVec.ofNat 32 4)
    (ho2 : oc + 32 ≤ 0x4C0) (hp2 : pc + 32 ≤ 0x4C0) (hp3 : pc % 4 = 0)
    (hp0 : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 pc) = p0)
    (hl0 : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + 4)) = BitVec.ofNat 32 l0)
    (hp1 : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + 8)) = p1)
    (hl1 : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + 12)) = BitVec.ofNat 32 l1)
    (hp2' : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + 16)) = p2)
    (hl2 : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + 20)) = BitVec.ofNat 32 l2)
    (hp3' : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + 24)) = p3)
    (hl3 : memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + 28)) = BitVec.ofNat 32 l3)
    (r0 : SvRo B p0 l0) (r1 : SvRo B p1 l1) (r2 : SvRo B p2 l2) (r3 : SvRo B p3 l3)
    (hl0' : l0 < 2 ^ 31) (hl1' : l1 < 2 ^ 31) (hl2' : l2 < 2 ^ 31) (hl3' : l3 < 2 ^ 31) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧ reg n' sp = B + 0x21A0 ∧
      (∀ q : Fin 32, q.val ∈ [3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg n' q = reg n q) ∧
      SvKeepL B M n'.mem [(oc, 32)] ∧
      memBytes n'.mem (B + 0x21A0 + BitVec.ofNat 32 oc) 32 =
        sha256 (memBytes M p0 l0 ++ memBytes M p1 l1 ++ memBytes M p2 l2 ++ memBytes M p3 l3) ∧
      (∀ x, SvR B x → n'.mem x = M x) := by
  have F := sv_frW FW
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1' := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  have hq0 := r0.lo; have hq1 := r1.lo; have hq2 := r2.lo; have hq3 := r3.lo
  have z0 : 0 < p0.toNat := Nat.pos_of_ne_zero fun e => r0.ne0 (BitVec.eq_of_toNat_eq e)
  have z1 : 0 < p1.toNat := Nat.pos_of_ne_zero fun e => r1.ne0 (BitVec.eq_of_toNat_eq e)
  have z2 : 0 < p2.toNat := Nat.pos_of_ne_zero fun e => r2.ne0 (BitVec.eq_of_toNat_eq e)
  have z3 : 0 < p3.toNat := Nat.pos_of_ne_zero fun e => r3.ne0 (BitVec.eq_of_toNat_eq e)
  have e0 := partPtr_at (i := 0) (show memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + 8 * 0)) = p0 by exact hp0)
  have e1 := partPtr_at (i := 1) (show memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + 8 * 1)) = p1 by exact hp1)
  have e2 := partPtr_at (i := 2) (show memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + 8 * 2)) = p2 by exact hp2')
  have e3 := partPtr_at (i := 3) (show memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + 8 * 3)) = p3 by exact hp3')
  have f0 := partLen_at (i := 0) (by omega) (show memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + (8 * 0 + 4))) =
    BitVec.ofNat 32 l0 by exact hl0)
  have f1 := partLen_at (i := 1) (by omega) (show memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + (8 * 1 + 4))) =
    BitVec.ofNat 32 l1 by exact hl1)
  have f2' := partLen_at (i := 2) (by omega) (show memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + (8 * 2 + 4))) =
    BitVec.ofNat 32 l2 by exact hl2)
  have f3 := partLen_at (i := 3) (by omega) (show memLoad32 M (B + 0x21A0 + BitVec.ofNat 32 (pc + (8 * 3 + 4))) =
    BitVec.ofNat 32 l3 by exact hl3)
  have hpb : partsBytes M (B + 0x21A0 + BitVec.ofNat 32 pc) 4 =
      memBytes M p0 l0 ++ memBytes M p1 l1 ++ memBytes M p2 l2 ++ memBytes M p3 l3 := by
    rw [partsBytes_four, e0, e1, e2, e3, f0, f1, f2', f3]
  have env : PartsEnv n1.mem (B + 0x21A0 + BitVec.ofNat 32 oc) (B + 0x21A0 + BitVec.ofNat 32 pc) (B + 0x21A0) 4 := by
    rw [mem1]
    refine ⟨SC.parts, SC.iv, SC.upd, SC.ublk, SC.fin, SC.z, SC.fblk, SC.ms, SC.mcs, SC.mcb, SC.cmp, SC.idx, SC.k,
      by rw [hS]; omega, by rw [hS]; omega, by rw [hS]; omega,
      by rw [sv_at F _ (by omega)]; omega, sv_al F (by omega) hp3, by rw [sv_at F _ (by omega)]; omega,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [sv_sp270, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [hpb, List.length_append, List.length_append, List.length_append, memBytes_length, memBytes_length,
        memBytes_length, memBytes_length]; omega
    · intro i hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
      · rw [e0, f0, sv_sp270]; exact ⟨hl0', hq0, (r0.sep F (c := 0x1F30) (n := 0x270) (by decide)).symm⟩
      · rw [e1, f1, sv_sp270]; exact ⟨hl1', hq1, (r1.sep F (c := 0x1F30) (n := 0x270) (by decide)).symm⟩
      · rw [e2, f2', sv_sp270]; exact ⟨hl2', hq2, (r2.sep F (c := 0x1F30) (n := 0x270) (by decide)).symm⟩
      · rw [e3, f3, sv_sp270]; exact ⟨hl3', hq3, (r3.sep F (c := 0x1F30) (n := 0x270) (by decide)).symm⟩
    · rw [sv_sp270, ← sv_base']; exact sepS B (by omega) (by omega) (by omega)
    · rw [sv_sp270]
      have h := RS.sub (c := 0x1590 + 0x1F30) (l := 0x270) (by decide)
      rw [svW_at B 0x1F30 (by decide)] at h
      have h' := h.subR (c := 0xF24) (l := 256) (by decide)
      rw [show BitVec.ofNat 32 (img% roWindowAddress) + BitVec.ofNat 32 0xF24 = SK2 from rfl] at h'
      exact h'.symm
    · rw [sv_sp270]; exact (F.bufData (c := 0x1F30) (n := 0x270) (by decide) (by decide) (by decide)).symm
  obtain ⟨n2, c2, pc2, sp2, k2, dg2, f2⟩ := sha256Parts_correct n1 env pc1
    (by rw [r1' a0 (by decide), ha0]) (by rw [r1' a1 (by decide), ha1]) (by rw [r1' a2 (by decide), ha2])
    (by rw [regs1]; simp +decide [upd]) (even_clear _ hev) (by rw [r1' sp (by decide), rsp])
  rw [mem1, sv_sp270] at f2
  rw [mem1, hpb] at dg2
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩, sp2, fun q hq => ?_,
    fun e he hL => ?_, dg2, fun x hx => f2 x (svR_sp270 hx) (svR_hi hx ho2)⟩
  · have hq' : q ≠ t0 ∧ q ≠ t1 ∧ q ≠ (7 : Fin 32) ∧ q ≠ a0 ∧ q ≠ a1 ∧ q ≠ a2 ∧ q ≠ a3 ∧ q ≠ a4 ∧ q ≠ a5 ∧
        q ≠ a6 ∧ q ≠ a7 ∧ q ≠ (28 : Fin 32) ∧ q ≠ (29 : Fin 32) ∧ q ≠ (30 : Fin 32) ∧ q ≠ (31 : Fin 32) ∧
        q ≠ ra := by revert hq; revert q; decide
    obtain ⟨q5, q6, q7, q10, q11, q12, q13, q14, q15, q16, q17, q28, q29, q30, q31, q1⟩ := hq'
    rw [k2 q q5 q6 q7 q10 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31, r1' q q1]
  · have h1 := hL _ (List.mem_singleton_self _)
    simp only at h1
    exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))
      (sepS (B + 0x21A0) (by omega) (by omega) (by omega))

theorem SvRo.shrink {B q : Word} {ql k : Nat} (h : SvRo B q ql) (hk : k ≤ ql) : SvRo B q k := by
  rcases h with h | ⟨h1, h2⟩
  · exact .inl (h.shrink hk)
  · exact .inr ⟨h1, by omega⟩

theorem spf_ite {M M0 : Word → BitVec 8} {B p a b : Word} {sl pl : Nat} {X : Bytes}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (fR : ∀ x, SvR B x → M x = M0 x) (hp : SvRo B p sl) :
    (if pl ≤ sl ∧ memBytes M p pl = X then a else b) = (if pl ≤ sl ∧ memBytes M0 p pl = X then a else b) := by
  by_cases h : pl ≤ sl
  · rw [sv_mbRo FW fR (hp.shrink h)]
  · simp [h]

set_option maxHeartbeats 8000000 in
/-- **A call to `<[u8]>::strip_prefix`** of the `pl` bytes at `q` from the `sl` bytes at `p`. -/
theorem sv_spfF {M : Word → BitVec 8} {n : Machine} {B : Word} {off : Nat} {imm o p q : Word} {sl pl : Nat}
    (F : Fr B 0x2660) (C : SvCode M) (CK : SvCkCode M) (s : St M SV n off (reg n))
    (h1 : fetchRel sigstoreVerifyCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel sigstoreVerifyCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : SV + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 stripPrefixAddress)
    (hev : (SV + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (rsp : reg n sp = B + 0x21A0) (ha0 : reg n a0 = p) (ha1 : reg n a1 = BitVec.ofNat 32 sl)
    (ha2 : reg n a2 = q) (ha3 : reg n a3 = BitVec.ofNat 32 pl) (hp : SvRo B p sl) (hq : SvRo B q pl) :
    ∃ n', Steps n n' ∧ St n'.mem SV n' (off + 8) (reg n') ∧
      (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ ra → reg n' r = reg n r) ∧
      reg n' a0 = (if pl ≤ sl ∧ memBytes M p pl = memBytes M q pl then p + BitVec.ofNat 32 pl else 0) ∧
      (pl ≤ sl → reg n' a1 = BitVec.ofNat 32 (sl - pl)) ∧
      SvKeepL B M n'.mem [] ∧ (∀ x, SvR B x → n'.mem x = M x) := by
  have hFl := F.lo; have hFh := F.hi; have hFa := F.al
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa C.self h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hS : (B + (0x21A0 : Word)).toNat = B.toNat + 0x21A0 := F.at 0x21A0 (by decide)
  obtain ⟨n2, c2, pc2, a02, a12, k2, f2⟩ := stripPrefix_correct n1 (s := p) (pre := q) (sl := sl) (pl := pl)
    (by rw [mem1]; exact CK.spf) (by decide)
    (by rw [mem1, show (BitVec.ofNat 32 stripPrefixAddress : Word) + 0xFFFFFFEA =
      BitVec.ofNat 32 equalSameLengthAddress by decide]; exact C.equalSameLength)
    (by rw [mem1, show (BitVec.ofNat 32 stripPrefixAddress : Word) + 0xFFFFFFEA + 0xD3BE =
      BitVec.ofNat 32 memcmpAddress by decide]; exact C.memcmp) pc1
    (by rw [r1 a0 (by decide), ha0]) (by rw [r1 a1 (by decide), ha1])
    (by rw [r1 a2 (by decide), ha2]) (by rw [r1 a3 (by decide), ha3]) (by have := hp.fit; omega)
    (by have := hq.fit; omega) (by rw [regs1]; simp +decide [upd]) (even_clear _ hev)
    (by rw [r1 sp (by decide), rsp, hS]; omega)
    (by rw [r1 sp (by decide), rsp, sv_sp14]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [r1 sp (by decide), rsp, sv_sp14]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [r1 sp (by decide), rsp, sv_sp14]; exact F.sepHi (by decide) (by decide) (by decide))
    (by rw [r1 sp (by decide), rsp, sv_sp14]; exact hp.sep F (by decide))
    (by rw [r1 sp (by decide), rsp, sv_sp14]; exact hq.sep F (by decide))
  rw [mem1, r1 sp (by decide), rsp, sv_sp14] at f2
  rw [mem1] at a02
  have hfS : ∀ x, SvR B x → Sep (B + BitVec.ofNat 32 0x218C) 20 x 1 := fun x hx => by
    have := svR_lo (k := 20) hx (by decide) (by decide)
    rwa [sv_lo B 20 (by decide)] at this
  refine ⟨n2, c1.trans c2, ⟨by rw [pc2], rfl, fun _ => rfl⟩,
    fun r h0 h1 h2 h3 h4 hra => by rw [k2 r h0 h1 h2 h3 h4, r1 r hra], a02, a12, fun e he _ => ?_,
    fun x hx => f2 x (hfS x hx)⟩
  exact f2 _ (by rw [← sv_base']; exact sepS B (by omega) (by omega) (by omega))

end C3.RV32.Sv
