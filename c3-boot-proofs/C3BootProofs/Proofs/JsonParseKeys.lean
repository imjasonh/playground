import C3BootProofs.Proofs.JsonParseFrame

/-!
# `json::parse`: the key checks of a closed object

When `parse` closes an object, it reopens the object's bytes with `members`
and walks its members with `next_member`. In canonical mode, each key must
sort after the one before it (`keysCanon`). In strict mode, no key may equal
a later one (`keysStrict`), which an inner walk checks with `slice_ne`.
-/

namespace C3.RV32

open C3.Image C3.Json

theorem slt0 (w : Word) : w.slt 0 = decide (2 ^ 31 ≤ w.toNat) := by
  rw [BitVec.slt]
  have h := BitVec.toInt_eq_toNat_cond w
  have h0 : (0 : Word).toInt = 0 := rfl
  rw [h0, h]
  have := w.isLt
  rcases Nat.lt_or_ge (2 * w.toNat) (2 ^ 32) with hc | hc
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩

theorem sub_zext_slt (x y : BitVec 8) (hne : x ≠ y) :
    (aluEval .sub (x.zeroExtend 32) (y.zeroExtend 32)).slt 0 = decide (x.toNat < y.toNat) ∧
      aluEval .sub (x.zeroExtend 32) (y.zeroExtend 32) ≠ 0 := by
  have hx := x.isLt
  have hy := y.isLt
  have hn : x.toNat ≠ y.toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
  have e : (aluEval .sub (x.zeroExtend 32) (y.zeroExtend 32)).toNat = (2 ^ 32 - y.toNat + x.toNat) % 2 ^ 32 := by
    show ((x.zeroExtend 32) - (y.zeroExtend 32)).toNat = _
    rw [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 32)]
  refine ⟨?_, fun h => ?_⟩
  · rw [slt0, e]
    exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
  · have := congrArg BitVec.toNat h
    rw [e] at this
    have h0 : (0 : Word).toNat = 0 := rfl
    omega

/-- The sign `parse` reads after `memcmp` over the shorter length, and after
the length difference when those bytes are equal, is the key order. -/
theorem cmp_lt {M : Word → BitVec 8} {a b v : Word} {la lb : Nat} (hla : la < 2 ^ 31) (hlb : lb < 2 ^ 31)
    (hc : CmpRes M a b (min la lb) v) :
    (v ≠ 0 → v.slt 0 = bytesLt (memBytes M a la) (memBytes M b lb)) ∧
      (v = 0 → (BitVec.ofNat 32 la - BitVec.ofNat 32 lb).slt 0 = bytesLt (memBytes M a la) (memBytes M b lb)) := by
  rcases hc with ⟨hv, heq⟩ | ⟨i, hi, hpre, hne, hv⟩
  · refine ⟨fun h => absurd hv h, fun _ => ?_⟩
    rw [bytesLt_prefix _ _ fun j hj => ?_, memBytes_length, memBytes_length, slt0]
    · have e : (BitVec.ofNat 32 la - BitVec.ofNat 32 lb).toNat = (2 ^ 32 - lb + la) % 2 ^ 32 := by
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : la < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : lb < 2 ^ 32)]
      rw [e]
      exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
    · rw [memBytes_length, memBytes_length] at hj
      rw [memBytes_getD (by omega), memBytes_getD (by omega), heq j hj]
  · obtain ⟨h1, h2⟩ := sub_zext_slt _ _ hne
    rw [← hv] at h1 h2
    refine ⟨fun _ => ?_, fun h => absurd h h2⟩
    have hia : i < la := by omega
    have hib : i < lb := by omega
    rw [h1, bytesLt_first _ _ i (by rw [memBytes_length]; exact hia) (by rw [memBytes_length]; exact hib)
      (fun j hj => by rw [memBytes_getD (by omega), memBytes_getD (by omega), hpre j hj])
      (by rw [memBytes_getD hia, memBytes_getD hib]; exact fun h => hne (BitVec.eq_of_toNat_eq h)),
      memBytes_getD hia, memBytes_getD hib]

section
variable {M0 Mp M : Word → BitVec 8} {base s p out F : Word} {n : Nat} {g0 : Fin 32 → Word}

theorem PaEnv.sepF (E : PaEnv M0 base s p out n g0 Mp F) {a : Word} {l : Nat} (h : Sep s 404 a l) {d w : Nat}
    (hdw : 164 + d + w ≤ 404) : Sep (F + BitVec.ofNat 32 d) w a l := by
  rw [← E.hF, add_ofNat_assoc]; exact h.sub (by omega)

theorem PaEnv.below (E : PaEnv M0 base s p out n g0 Mp F) {d w : Nat} (h : 164 + d + w ≤ 2 ^ 32) :
    Sep (F + BitVec.ofNat 32 d) w s 164 := (gt_below E.hF h).symm

theorem PaEnv.alF (E : PaEnv M0 base s p out n g0 Mp F) {d : Nat} (hd : d % 4 = 0) :
    (F + BitVec.ofNat 32 d).toNat % 4 = 0 := aligned_add E.halF hd

theorem PaEnv.qnz (E : PaEnv M0 base s p out n g0 Mp F) {st l : Nat} (h : st + l ≤ n) :
    (p + BitVec.ofNat 32 st).toNat ≠ 0 ∧ (p + BitVec.ofNat 32 st).toNat + l < 2 ^ 32 := by
  have := E.hpn; have := E.hp0
  rw [toNat_add_lt (by omega)]; exact ⟨by omega, by omega⟩

theorem PaEnv.sepq (E : PaEnv M0 base s p out n g0 Mp F) {st l : Nat} (h : st + l ≤ n) :
    Sep s 404 (p + BitVec.ofNat 32 st) l := E.sP.subR h

/-- The bytes of a slice of the document, read from memory that changed
only on the stack. -/
theorem PaEnv.slice (E : PaEnv M0 base s p out n g0 Mp F) {st l : Nat} (h : st + l ≤ n) (hO : Out M0 M s 404) :
    memBytes M (p + BitVec.ofNat 32 st) l = slice (memBytes M0 p n) st l := by
  rw [← memBytes_slice h, hO.bytes E.sP]

end

theorem MemRes.outF {M1 M2 : Word → BitVec 8} {F : Word} {cc : Nat}
    {r : Option (Option (Word × Nat × Word × Nat × Nat))} (h : MemRes M1 M2 (F + 0xA8) (F + BitVec.ofNat 32 cc) r)
    (hcc : 144 ≤ cc ∧ cc + 12 ≤ 168) : Out M1 M2 (F + BitVec.ofNat 32 144) 44 := fun x hx => by
  refine h.out ?_ ?_
  · have := sep_in hx (d := 24) (l := 20) (by decide)
    rwa [add_ofNat_assoc] at this
  · have := sep_in hx (d := cc - 144 + 8) (l := 4) (by omega)
    rwa [add_ofNat_assoc, show 144 + (cc - 144 + 8) = cc + 8 by omega, ← add_ofNat_assoc] at this

section
variable {M0 Mp M : Word → BitVec 8} {base s p out F : Word} {n : Nat} {g0 f : Fin 32 → Word} {c : Bool}
  {stk : List (Bool × Nat)} {Q : Post}

/-- A call to `next_member` from `parse`, with `out` at `F + 0xA8` and the
cursor at `F + cc` over the `l` bytes of the document at `st`. -/
theorem pa_nm (E : PaEnv M0 base s p out n g0 Mp F) {off cc st l pos : Nat} {hi lo : Word}
    (h1 : fetchRel jsonParseCode off = some (.auipc ra hi, 4))
    (h2 : fetchRel jsonParseCode (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = base + 0xFFFFF372 + 0xFFFFF438) (hev : (off + 8) % 2 = 0)
    (hcc : cc = 0x90 ∨ cc = 0x9C) (hFI : FInv M0 Mp s F n stk M) (hR : PRegs f g0 F p n c)
    (h0 : f a0 = F + 0xA8) (ha1 : f a1 = F + BitVec.ofNat 32 cc)
    (hmp : memLoad32 M (F + BitVec.ofNat 32 cc) = p + BitVec.ofNat 32 st)
    (hmn : memLoad32 M (F + BitVec.ofNat 32 cc + 4) = BitVec.ofNat 32 l)
    (hmq : memLoad32 M (F + BitVec.ofNat 32 cc + 8) = BitVec.ofNat 32 pos) (hsl : st + l ≤ n) (hpos : pos < 2 ^ 32)
    (k : ∀ m2 : Machine, FInv M0 Mp s F n stk m2.mem →
      (∃ M1, Out M M1 s 164 ∧ MemRes M1 m2.mem (F + 0xA8) (F + BitVec.ofNat 32 cc)
        (memRes (p + BitVec.ofNat 32 st) (nextMember (slice (memBytes M0 p n) st l) pos))) →
      (∀ d, d + 4 ≤ 16 ∨ 144 ≤ d ∧ d + 4 ≤ 168 ∧ (d + 4 ≤ cc + 8 ∨ cc + 12 ≤ d) →
        memLoad32 m2.mem (F + BitVec.ofNat 32 d) = memLoad32 M (F + BitVec.ofNat 32 d)) →
      WP jsonParseCode base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP jsonParseCode base Q M off f := by
  have hcd : 144 ≤ cc ∧ cc + 12 ≤ 168 ∧ cc % 4 = 0 := by rcases hcc with rfl | rfl <;> decide
  have hc1 : ParseCode M base := E.code.out hFI.1 E.sep
  obtain ⟨hq0, hqn⟩ := E.qnz hsl
  refine WP.callNextMember (tb := base + 0xFFFFF372 + 0xFFFFF438) (out := F + 0xA8) (c := F + BitVec.ofNat 32 cc)
    (s := s) (p := p + BitVec.ofNat 32 st) (n := l) (pos := pos) h1 h2 htgt
    (even_at _ (even_at base E.hb _ (by decide)) _ (by decide)) hev hc1.get.nm
    (by rw [gt_ad_ri]; exact hc1.get.ri) (by rw [gt_ad_ke]; exact hc1.get.ke) h0 ha1
    (by rw [hR.sp, E.hF]) E.hal (E.alF (d := 0xA8) (by decide)) (E.alF hcd.2.2) hmp hmn hmq (by omega) hpos hq0
    (by omega) ?_ ?_ (sep_low E.sep.get.nm (by decide)) (sep_low (E.sepq hsl) (by decide))
    (E.below (d := 0xA8) (w := 20) (by decide)) (E.below (d := cc) (w := 12) (by omega))
    (sep_offsets F (c := 0xA8) (n := 20) (d := cc) (k := 12) (Or.inr (by omega)) (by decide) (by omega))
    (E.sepF E.sep.get.nm (d := 0xA8) (w := 20) (by decide)) (E.sepF E.sep.get.nm (d := cc) (w := 12) (by omega))
    (sep_low E.sep.parse (by decide)) (E.sepF E.sep.parse (d := 0xA8) (w := 20) (by decide))
    (E.sepF E.sep.parse (d := cc) (w := 12) (by omega)) fun m2 hMR => ?_
  · rw [gt_ad_ri]; have := E.sep.get.ri.sub (c := 0) (l := 164) (by decide); rwa [add_ofNat_zero] at this
  · rw [gt_ad_ke]; exact sep_low E.sep.get.ke (by decide)
  rw [E.slice hsl hFI.1] at hMR
  obtain ⟨M1, hOa, hM⟩ := hMR
  have hOa' : Out M M1 (s + BitVec.ofNat 32 0) 164 := by rw [add_ofNat_zero]; exact hOa
  refine k m2 ((hFI.out E.hF hOa' (Or.inl (by decide))).outF E.hF (hM.outF ⟨hcd.1, hcd.2.1⟩)
    (Or.inr ⟨Nat.le_refl _, by decide⟩)) ⟨M1, hOa, hM⟩ fun d hd => ?_
  have hd168 : d + 4 ≤ 168 := by rcases hd with h | ⟨_, h, _⟩ <;> omega
  refine (memLoad32_congr fun j hj => ?_).trans (hOa.load32 (E.below (d := d) (w := 4) (by omega)).symm)
  rw [add_ofNat_assoc]
  refine hM.out (sep_offsets F (c := d + j) (n := 1) (d := 168) (k := 20) (Or.inl (by omega)) (by omega) (by decide))
    ?_
  show Sep _ 1 (F + BitVec.ofNat 32 cc + BitVec.ofNat 32 8) 4
  rw [add_ofNat_assoc]
  have hs : d + j + 1 ≤ cc + 8 ∨ cc + 8 + 4 ≤ d + j := by
    rcases hd with h | ⟨_, _, h | h⟩
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  exact sep_offsets F hs (by omega) (by omega)

end

theorem gt_ad_nm (b : Word) : b + 0xFFFFF372 + 0xFFFFF438 + 0x1DE = b + 0xFFFFF372 + 0xFFFFF616 := gt_ad_ri _

end C3.RV32
