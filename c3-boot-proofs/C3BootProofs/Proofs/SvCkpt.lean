import C3BootProofs.Proofs.SvTpv
import C3BootProofs.Proofs.CheckpointLine

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

theorem SvCkCode.sv {M M0 : Word → BitVec 8} {B : Word} (F : Fr B 0x3830) (D : SvCkCode M0)
    (fR : ∀ x, SvR B x → M x = M0 x) : SvCkCode M := by
  have hx : ∀ x : Word, 0x40000000 ≤ x.toNat → M x = M0 x := fun x hx => fR x (sep_of_le (by
    have hb : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 := F.below 0x1A0 (by decide) (by decide)
    have := F.hi; rw [hb]; omega) (by have := x.isLt; omega))
  exact ⟨codeHi D.line (by decide) (by decide) hx⟩

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

end C3.RV32.Sv
