import C3BootProofs.Proofs.ImageTop
import C3BootProofs.Proofs.ParseSpec

/-! # `imgW` and `decodeImageHeader`: the header

`Rel x y f` relates what the compiled code decides, `x`, to what the Lean
decoder returns, `y`: `Ok a` to `some (f a)`, and every error to `none`.
`Rel.bind` composes it through the two monads' binds, so each reader the
compiled code calls relates to the decoder's reader at the same position
(`rdU8_rel` to `rdRes_rel`), and each layer of the compiled header check
(`hdrChip` to `hdrLen`) relates to the decoder's matching layer (`decChip` to
`decLen`). `hdr_rel` takes the rest of `imgW` as a continuation `K`. -/

namespace C3

open RV32

/-- Relates what the compiled code decides to what the Lean decoder returns:
`Ok a` to `some (f a)`, and any error to `none`. -/
def Rel {ε α β : Type} (x : Except ε α) (y : Option β) (f : α → β) : Prop :=
  match x with
  | .ok a => y = some (f a)
  | .error _ => y = none

theorem Rel.bind {ε α β γ δ : Type} {x : Except ε α} {y : Option β} {f : α → β} {g : α → Except ε γ}
    {h : β → Option δ} {k : γ → δ} (r : Rel x y f) (rg : ∀ a, Rel (g a) (h (f a)) k) :
    Rel (x >>= g) (y >>= h) k := by
  cases x with
  | error e => show (y >>= h) = none; rw [show y = none from r]; rfl
  | ok a => show Rel (g a) (y >>= h) k; rw [show y = some (f a) from r]; exact rg a

theorem Rel.req {ε α δ : Type} {x : Except ε α} {h : Unit → Option δ} {k : α → δ} (b : Bool)
    (r : b = true → Rel x (h ()) k) (e : b = false → ∃ c, x = .error c) :
    Rel x (require b >>= h) k := by
  cases b with
  | true => exact r rfl
  | false => obtain ⟨c, hc⟩ := e rfl; rw [hc]; rfl

theorem ebind_assoc {ε α β γ : Type} (x : Except ε α) (f : α → Except ε β) (g : β → Except ε γ) :
    (x >>= f) >>= g = x >>= fun a => f a >>= g := by
  cases x <;> rfl

/-- The bytes from position `p` of the `len` bytes at `ptr`. -/
def tailAt (M : Word → BitVec 8) (ptr len : Word) (p : Nat) : Bytes :=
  (List.range' p (len.toNat - p)).map fun i => (M (ptr + BitVec.ofNat 32 i)).toNat

/-- Byte `i` at `ptr`. -/
abbrev ib (M : Word → BitVec 8) (ptr : Word) (i : Nat) : Nat := (M (ptr + BitVec.ofNat 32 i)).toNat

section Bytes

variable {M : Word → BitVec 8} {ptr len : Word}

theorem tailAt_succ {p : Nat} (h : p < len.toNat) : tailAt M ptr len p = ib M ptr p :: tailAt M ptr len (p + 1) := by
  unfold tailAt
  rw [show len.toNat - p = (len.toNat - (p + 1)) + 1 by omega, List.range'_succ]
  rfl

theorem tailAt_end {p : Nat} (h : len.toNat ≤ p) : tailAt M ptr len p = [] := by
  unfold tailAt; rw [show len.toNat - p = 0 by omega]; rfl

theorem ofNat_toNat' (x : Word) : BitVec.ofNat 32 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])

theorem toNat_add_lt {a b : Word} (h : a.toNat + b.toNat < 2 ^ 32) : (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem rdB_eq (n pos : Word) :
    rdB ptr len n pos = if pos.toNat + n.toNat ≤ len.toNat then .ok (ptr + pos, pos + n) else .error 0 := by
  unfold rdB; rw [bytesResult_eq]
  by_cases h : pos.toNat + n.toNat ≤ len.toNat
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

theorem ib_pos (pos : Word) : ib M ptr pos.toNat = (M (ptr + pos)).toNat := by
  unfold ib; rw [ofNat_toNat']

theorem ib_add (pos : Word) (i : Nat) : ib M ptr (pos.toNat + i) = (M (ptr + pos + BitVec.ofNat 32 i)).toNat := by
  unfold ib; rw [← add_ofNat_assoc, ofNat_toNat']

theorem rdU8_rel (pos : Word) :
    Rel (rdU8 M ptr len pos) (readU8 (tailAt M ptr len pos.toNat))
      fun r => (r.1.toNat, tailAt M ptr len r.2.toNat) := by
  unfold rdU8; rw [rdB_eq]
  have hl := len.isLt
  by_cases h : pos.toNat + (1 : Word).toNat ≤ len.toNat
  · rw [ite_eq_left h]
    have h1 : (1 : Word).toNat = 1 := rfl
    rw [h1] at h
    show readU8 _ = some ((M (ptr + pos)).toNat, tailAt M ptr len (pos + 1).toNat)
    rw [tailAt_succ (by omega), toNat_add_lt (by rw [h1]; omega), h1, ib_pos]; rfl
  · rw [ite_eq_right h]
    show readU8 _ = none
    rw [tailAt_end (by have : (1 : Word).toNat = 1 := rfl; omega)]; rfl

theorem tailAt_length (p : Nat) : (tailAt M ptr len p).length = len.toNat - p := by
  unfold tailAt; rw [List.length_map, List.length_range']

theorem readU16_short : ∀ {bs : Bytes}, bs.length < 2 → readU16 bs = none
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _, h => absurd h (by simp)

theorem readU32_short : ∀ {bs : Bytes}, bs.length < 4 → readU32 bs = none
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _, h => absurd h (by simp)

theorem rdU16_rel (pos : Word) :
    Rel (rdU16 M ptr len pos) (readU16 (tailAt M ptr len pos.toNat))
      fun r => (r.1.toNat, tailAt M ptr len r.2.toNat) := by
  unfold rdU16; rw [rdB_eq]
  have hl := len.isLt
  have h2 : (2 : Word).toNat = 2 := rfl
  by_cases h : pos.toNat + (2 : Word).toNat ≤ len.toNat
  · rw [ite_eq_left h]
    rw [h2] at h
    show readU16 _ = some ((((M (ptr + pos + 1)).zeroExtend 32 <<< 24 ||| (M (ptr + pos)).zeroExtend 32 <<< 16 : Word)
      >>> 16).toNat, tailAt M ptr len (pos + 2).toNat)
    rw [tailAt_succ (by omega), tailAt_succ (by omega), toNat_add_lt (by rw [h2]; omega), h2, version_toNat,
      ib_pos, ib_add pos 1]; rfl
  · rw [ite_eq_right h]
    show readU16 _ = none
    exact readU16_short (by rw [tailAt_length]; omega)

theorem rdU32_rel (pos : Word) :
    Rel (rdU32 M ptr len pos) (readU32 (tailAt M ptr len pos.toNat))
      fun r => (r.1.toNat, tailAt M ptr len r.2.toNat) := by
  unfold rdU32; rw [rdB_eq]
  have hl := len.isLt
  have h4 : (4 : Word).toNat = 4 := rfl
  by_cases h : pos.toNat + (4 : Word).toNat ≤ len.toNat
  · rw [ite_eq_left h]
    rw [h4] at h
    show readU32 _ = some ((memLoad32 M (ptr + pos)).toNat, tailAt M ptr len (pos + 4).toNat)
    rw [tailAt_succ (by omega), tailAt_succ (by omega), tailAt_succ (by omega), tailAt_succ (by omega),
      toNat_add_lt (by rw [h4]; omega), h4, memLoad32_toNat, ib_pos, ib_add pos 1, ib_add pos 2, ib_add pos 3]
    rfl
  · rw [ite_eq_right h]
    show readU32 _ = none
    exact readU32_short (by rw [tailAt_length]; omega)

theorem toNat_beq0 : ∀ x : BitVec 8, (x.toNat == 0) = (x == 0) := by decide

theorem tail_take_all : ∀ k p, p + k ≤ len.toNat →
    ((tailAt M ptr len p).take k).all (· == 0) = allZero M (ptr + BitVec.ofNat 32 p) k
  | 0, _, _ => rfl
  | k + 1, p, h => by
    rw [tailAt_succ (by omega), List.take_succ_cons, List.all_cons, tail_take_all k (p + 1) (by omega)]
    show ((ib M ptr p == 0) && _) = ((M (ptr + BitVec.ofNat 32 p) == 0) && allZero M (ptr + BitVec.ofNat 32 p + 1) k)
    rw [toNat_beq0, show ptr + BitVec.ofNat 32 p + 1 = ptr + BitVec.ofNat 32 (p + 1) from add_ofNat_assoc ptr p 1]

theorem tail_drop : ∀ k p, p + k ≤ len.toNat → (tailAt M ptr len p).drop k = tailAt M ptr len (p + k)
  | 0, _, _ => rfl
  | k + 1, p, h => by
    rw [tailAt_succ (by omega), List.drop_succ_cons, tail_drop k (p + 1) (by omega), Nat.add_right_comm,
      Nat.add_assoc]

theorem rdRes_rel (n pos : Word) (hn : 0 < n.toNat) :
    Rel (rdRes M ptr len n pos) (readZeros n.toNat (tailAt M ptr len pos.toNat)) fun e => tailAt M ptr len e.toNat := by
  unfold rdRes; rw [rdB_eq]
  have hl := len.isLt
  unfold readZeros
  rw [tailAt_length]
  by_cases h : pos.toNat + n.toNat ≤ len.toNat
  · rw [ite_eq_left h]
    show Rel (if allZero M (ptr + pos) n.toNat = true then pure (pos + n) else throw 4) _ _
    rw [ite_eq_right (show ¬ len.toNat - pos.toNat < n.toNat by omega), tail_take_all _ _ h, ofNat_toNat',
      tail_drop _ _ h]
    by_cases hz : allZero M (ptr + pos) n.toNat = true
    · rw [ite_eq_left hz, ite_eq_left hz]
      show _ = some (tailAt M ptr len (pos + n).toNat)
      rw [toNat_add_lt (by omega)]
    · rw [ite_eq_right hz, ite_eq_right hz]; rfl
  · rw [ite_eq_right h, ite_eq_left (show len.toNat - pos.toNat < n.toNat by omega)]; rfl

theorem le32_magic {a b c d : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    ([a, b, c, d] == magicImage) = (le32 a b c d == 0x4D493343) := by
  by_cases h : le32 a b c d = 0x4D493343
  · have e0 : a = 0x43 := by unfold le32 at h; omega
    have e1 : b = 0x33 := by unfold le32 at h; omega
    have e2 : c = 0x49 := by unfold le32 at h; omega
    have e3 : d = 0x4D := by unfold le32 at h; omega
    subst e0 e1 e2 e3; rfl
  · rw [show (le32 a b c d == 0x4D493343) = false from beq_eq_false_iff_ne.mpr h]
    apply beq_eq_false_iff_ne.mpr
    intro e
    unfold magicImage at e
    injection e with e0 e
    injection e with e1 e
    injection e with e2 e
    injection e with e3
    subst e0 e1 e2 e3
    exact h rfl

theorem magic_rel :
    Rel (rdMagic M ptr len 0x4D493343 0) (readExpect magicImage (tailAt M ptr len 0))
      fun e => tailAt M ptr len e.toNat := by
  unfold rdMagic readExpect; rw [rdB_eq]
  have hl := len.isLt
  have h4 : (4 : Word).toNat = 4 := rfl
  have h0 : (0 : Word).toNat = 0 := rfl
  rw [h0, h4, tailAt_length, show magicImage.length = 4 from rfl]
  by_cases h : 0 + 4 ≤ len.toNat
  · rw [ite_eq_left h]
    show Rel (if (memLoad32 M (ptr + 0) == 0x4D493343) = true then pure (0 + 4) else throw 2) _ _
    have hk : (memLoad32 M (ptr + 0) == 0x4D493343) =
        (le32 (ib M ptr 0) (ib M ptr 1) (ib M ptr 2) (ib M ptr 3) == 0x4D493343) := by
      have e0 : ib M ptr 0 = (M (ptr + 0)).toNat := rfl
      have e1 : ib M ptr 1 = (M (ptr + 0 + 1)).toNat := by rw [show ptr + (0 : Word) = ptr from BitVec.add_zero ptr]; rfl
      have e2 : ib M ptr 2 = (M (ptr + 0 + 2)).toNat := by rw [show ptr + (0 : Word) = ptr from BitVec.add_zero ptr]; rfl
      have e3 : ib M ptr 3 = (M (ptr + 0 + 3)).toNat := by rw [show ptr + (0 : Word) = ptr from BitVec.add_zero ptr]; rfl
      rw [e0, e1, e2, e3, ← memLoad32_toNat]
      by_cases hm : memLoad32 M (ptr + 0) = 0x4D493343
      · rw [hm]; rfl
      · rw [beq_eq_false_iff_ne.mpr hm]
        exact (beq_eq_false_iff_ne.mpr fun e : (memLoad32 M (ptr + 0)).toNat = 0x4D493343 =>
          hm (BitVec.eq_of_toNat_eq e)).symm
    rw [tailAt_succ (by omega), tailAt_succ (by omega), tailAt_succ (by omega), tailAt_succ (by omega),
      show List.take 4 (ib M ptr 0 :: ib M ptr (0 + 1) :: ib M ptr (0 + 1 + 1) :: ib M ptr (0 + 1 + 1 + 1) ::
        tailAt M ptr len (0 + 1 + 1 + 1 + 1)) = [ib M ptr 0, ib M ptr 1, ib M ptr 2, ib M ptr 3] from rfl,
      le32_magic (M _).isLt (M _).isLt (M _).isLt (M _).isLt,
      show decide (4 ≤ len.toNat - 0) = true from decide_eq_true (by omega), Bool.and_true, hk]
    by_cases hm : (le32 (ib M ptr 0) (ib M ptr 1) (ib M ptr 2) (ib M ptr 3) == 0x4D493343) = true
    · rw [ite_eq_left hm, ite_eq_left hm]
      show _ = some (tailAt M ptr len (0 + 4 : Word).toNat)
      rfl
    · rw [ite_eq_right hm, ite_eq_right hm]; rfl
  · rw [ite_eq_right h]
    show _ = none
    rw [ite_eq_right]
    intro e
    rw [Bool.and_eq_true] at e
    exact h (by have := of_decide_eq_true e.2; omega)

theorem ver_rel (pos : Word) :
    Rel (rdVer1 M ptr len pos) (do
        let (version, rest) ← readU16 (tailAt M ptr len pos.toNat)
        require (version == 1)
        pure rest)
      fun e => tailAt M ptr len e.toNat := by
  unfold rdVer1
  refine Rel.bind (rdU16_rel pos) fun ⟨v, e⟩ => ?_
  show Rel (if (v == 1) = true then pure e else throw 3) (require (v.toNat == 1) >>= fun _ => pure _) _
  have hv : (v.toNat == 1) = (v == 1) := by
    by_cases h : v = 1
    · rw [h]; rfl
    · rw [beq_eq_false_iff_ne.mpr h]
      exact beq_eq_false_iff_ne.mpr fun e : v.toNat = 1 => h (BitVec.eq_of_toNat_eq e)
  rw [hv]
  refine Rel.req _ (fun hb => ?_) (fun hb => ⟨3, by rw [ite_eq_right (by rw [hb]; decide)]; rfl⟩)
  rw [ite_eq_left hb]; rfl

theorem header_rel :
    Rel (rdMagic M ptr len 0x4D493343 0 >>= rdVer1 M ptr len) (readHeader magicImage (tailAt M ptr len 0))
      fun e => tailAt M ptr len e.toNat :=
  Rel.bind magic_rel fun e => ver_rel e

end Bytes

/-! ## `decodeImageHeader` in layers -/

/-- The decoder after the entry point and image length. -/
def decTail (il sv count entry : Nat) (rest : Bytes) : Option ImageHeader := do
  let segments ← readSegments count rest
  require (segments.all (segmentOk il))
  require (segmentsOrdered (20 + 16 * count) il segments)
  require (noOverlaps segments)
  require (entry % 2 == 0 && segments.any fun s =>
    s.kind.isExecutable && s.address ≤ entry && entry < s.address + s.length)
  pure ⟨sv, entry, il, segments⟩

def decLen (il sv count : Nat) (rest : Bytes) : Option ImageHeader := do
  let (entry, rest) ← readU32 rest
  let (length, rest) ← readU32 rest
  require (length == il)
  decTail il sv count entry rest

def decCnt (il sv : Nat) (rest : Bytes) : Option ImageHeader := do
  let (count, rest) ← readU8 rest
  require (0 < count && count ≤ 16)
  let rest ← readZeros 2 rest
  decLen il sv count rest

def decSv (il : Nat) (rest : Bytes) : Option ImageHeader := do
  let (sv, rest) ← readU8 rest
  require (sv ≤ 16)
  decCnt il sv rest

def decChip (il : Nat) (rest : Bytes) : Option ImageHeader := do
  let (chip, rest) ← readU16 rest
  require (chip == 5)
  decSv il rest

theorem decode_layers (bytes : Bytes) (il : Nat) :
    decodeImageHeader bytes il = readHeader magicImage bytes >>= decChip il := rfl


theorem word_beq (a b : Word) : (a.toNat == b.toNat) = (a == b) := by
  by_cases h : a = b
  · rw [h, (beq_iff_eq (a := b.toNat) (b := b.toNat)).mpr rfl, (beq_iff_eq (a := b) (b := b)).mpr rfl]
  · rw [beq_eq_false_iff_ne.mpr h]
    exact beq_eq_false_iff_ne.mpr fun e => h (BitVec.eq_of_toNat_eq e)

section Layers

variable {M : Word → BitVec 8} {ptr len ilen : Word} {γ : Type}
  {K : BitVec 8 × BitVec 8 × Word × Word → Except (BitVec 8) γ} {f : γ → ImageHeader}

theorem len_rel (hK : ∀ sv cnt entry pos, Rel (K (sv, cnt, entry, pos))
      (decTail ilen.toNat sv.toNat cnt.toNat entry.toNat (tailAt M ptr len pos.toNat)) f)
    (sv cnt : BitVec 8) (pos : Word) :
    Rel (hdrLen M ptr len ilen sv cnt pos >>= K) (decLen ilen.toNat sv.toNat cnt.toNat (tailAt M ptr len pos.toNat)) f := by
  unfold hdrLen decLen
  rw [ebind_assoc]
  refine Rel.bind (rdU32_rel pos) fun ⟨entry, p1⟩ => ?_
  dsimp only
  unfold hdrLn
  rw [ebind_assoc]
  refine Rel.bind (rdU32_rel p1) fun ⟨ln, p2⟩ => ?_
  dsimp only
  rw [word_beq]
  refine Rel.req _ (fun hb => ?_) (fun hb => ⟨7, ?_⟩)
  · rw [ite_eq_right (by rw [bne, hb]; decide)]
    exact hK sv cnt entry p2
  · rw [ite_eq_left (by rw [bne, hb]; rfl)]; rfl


theorem cnt_bad {c : Nat} (h : (decide (0 < c) && decide (c ≤ 16)) = false) : c = 0 ∨ 16 < c := by
  by_cases h0 : c = 0
  · exact .inl h0
  · refine .inr ?_
    by_cases h1 : c ≤ 16
    · rw [decide_eq_true (by omega : 0 < c), decide_eq_true h1] at h; cases h
    · omega

theorem cnt_rel (hK : ∀ sv cnt entry pos, Rel (K (sv, cnt, entry, pos))
      (decTail ilen.toNat sv.toNat cnt.toNat entry.toNat (tailAt M ptr len pos.toNat)) f)
    (sv : BitVec 8) (pos : Word) :
    Rel (hdrCnt M ptr len ilen sv pos >>= K) (decCnt ilen.toNat sv.toNat (tailAt M ptr len pos.toNat)) f := by
  unfold hdrCnt decCnt
  rw [ebind_assoc]
  refine Rel.bind (rdU8_rel pos) fun ⟨cnt, p1⟩ => ?_
  dsimp only
  refine Rel.req _ (fun hb => ?_) (fun hb => ⟨5, ?_⟩)
  · rw [Bool.and_eq_true] at hb
    have h0 := of_decide_eq_true hb.1
    have h1 := of_decide_eq_true hb.2
    rw [ite_eq_right (fun h => by rcases h with h | h <;> omega)]
    show Rel ((rdRes M ptr len 2 p1 >>= fun pos => hdrLen M ptr len ilen sv cnt pos) >>= K) _ f
    rw [ebind_assoc]
    exact Rel.bind (rdRes_rel 2 p1 (by decide)) fun pos => len_rel hK sv cnt pos
  · rw [ite_eq_left (cnt_bad hb)]; rfl

theorem sv_rel (hK : ∀ sv cnt entry pos, Rel (K (sv, cnt, entry, pos))
      (decTail ilen.toNat sv.toNat cnt.toNat entry.toNat (tailAt M ptr len pos.toNat)) f)
    (pos : Word) :
    Rel (hdrSv M ptr len ilen pos >>= K) (decSv ilen.toNat (tailAt M ptr len pos.toNat)) f := by
  unfold hdrSv decSv
  rw [ebind_assoc]
  refine Rel.bind (rdU8_rel pos) fun ⟨sv, p1⟩ => ?_
  dsimp only
  refine Rel.req _ (fun hb => ?_) (fun hb => ⟨5, ?_⟩)
  · rw [ite_eq_right (Nat.not_lt.mpr (of_decide_eq_true hb))]
    exact cnt_rel hK sv p1
  · rw [ite_eq_left (Nat.lt_of_not_le (of_decide_eq_false hb))]; rfl

theorem chip_rel (hK : ∀ sv cnt entry pos, Rel (K (sv, cnt, entry, pos))
      (decTail ilen.toNat sv.toNat cnt.toNat entry.toNat (tailAt M ptr len pos.toNat)) f)
    (pos : Word) :
    Rel (hdrChip M ptr len ilen pos >>= K) (decChip ilen.toNat (tailAt M ptr len pos.toNat)) f := by
  unfold hdrChip decChip
  rw [ebind_assoc]
  refine Rel.bind (rdU16_rel pos) fun ⟨chip, p1⟩ => ?_
  dsimp only
  have hc : (chip.toNat == 5) = (chip == 5) := word_beq chip 5
  rw [hc]
  refine Rel.req _ (fun hb => ?_) (fun hb => ⟨8, ?_⟩)
  · rw [ite_eq_right (by rw [bne, hb]; decide)]
    exact sv_rel hK p1
  · rw [ite_eq_left (by rw [bne, hb]; rfl)]; rfl

theorem hdr_rel (hK : ∀ sv cnt entry pos, Rel (K (sv, cnt, entry, pos))
      (decTail ilen.toNat sv.toNat cnt.toNat entry.toNat (tailAt M ptr len pos.toNat)) f) :
    Rel (hdrW M ptr len ilen >>= K) (decodeImageHeader (tailAt M ptr len 0) ilen.toNat) f := by
  rw [decode_layers]
  have e : hdrW M ptr len ilen >>= K =
      (rdMagic M ptr len 0x4D493343 0 >>= rdVer1 M ptr len) >>= fun p => hdrChip M ptr len ilen p >>= K := by
    unfold hdrW
    cases rdMagic M ptr len 0x4D493343 0 with
    | error => rfl
    | ok p =>
      show (rdVer1 M ptr len p >>= fun pos => hdrChip M ptr len ilen pos) >>= K = _
      rw [ebind_assoc]; rfl
  rw [e]
  exact Rel.bind header_rel fun p => chip_rel hK p

end Layers

end C3
