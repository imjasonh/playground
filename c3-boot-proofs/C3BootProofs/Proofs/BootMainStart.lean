import C3BootProofs.Proofs.BootMainEntry

/-!
# `boot_main` from its entry to 0xB4

`boot_main` saves registers, logs, records the flash size, reads the two
boot-state records from flash at 0x28000 and 0x29000, and decodes each.
`bmsDecoded` shows what the decoded copies hold, and `bmsBoot` runs from
the entry to the jump into the application, or to a halt or a panic.
-/

namespace C3.RV32.Cur

open C3 C3.Image C3.RV32.BootMainContract

/-! ## The decoded copies -/

theorem bms_ok4 {y : Nat → Nat} (h : bmrOk y = true) :
    y 12 ≤ 1 ∧ y 14 ≤ 3 ∧ y 15 &&& 0xFC = 0 ∧ (y 13 ≤ 1 ∨ (y 13 = 0xFF ∧ y 14 = 0)) := by
  simp only [bmrOk, List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    Bool.or_eq_true, and_assoc, Nat.reduceAdd] at h
  obtain ⟨_, _, _, _, _, _, _, _, hp, _, _, _, _, _, _, _, _, _, _, _, _, h14, h15, ht⟩ := h
  exact ⟨hp, h14, h15, ht⟩

theorem bms_bytes (M : Word → BitVec 8) (out b : Word) (h : bsErr M b = none) :
    bsMem M out b (out + 4) = (if (bsTrial M b).ult 2 then M (b + 13) else 2) ∧
      bsMem M out b (out + 5) = M (b + 14) ∧ bsMem M out b (out + 6) = M (b + 15) ∧
      bsMem M out b (out + 7) = M (b + 12) := by
  simp only [bsMem, h]
  have n : ∀ c d, c < 8 → d < 8 → c ≠ d → out + BitVec.ofNat 32 c ≠ out + BitVec.ofNat 32 d :=
    fun c d hc hd e => bmr_ne out hc hd e
  have b7 : out + 7 ≠ out + 6 := n 7 6 (by decide) (by decide) (by decide)
  have b75 : out + 7 ≠ out + 5 := n 7 5 (by decide) (by decide) (by decide)
  have b74 : out + 7 ≠ out + 4 := n 7 4 (by decide) (by decide) (by decide)
  have b65 : out + 6 ≠ out + 5 := n 6 5 (by decide) (by decide) (by decide)
  have b64 : out + 6 ≠ out + 4 := n 6 4 (by decide) (by decide) (by decide)
  have b54 : out + 5 ≠ out + 4 := n 5 4 (by decide) (by decide) (by decide)
  refine ⟨?_, ?_, ?_, memStore8_same _ _ _⟩
  · rw [memStore8_ne b74.symm, memStore8_ne b64.symm, memStore8_ne b54.symm, memStore8_same]
  · rw [memStore8_ne b75.symm, memStore8_ne b65.symm, memStore8_same]
  · rw [memStore8_ne b7.symm, memStore8_same]

theorem bms_gen (M : Word → BitVec 8) (out b : Word) (h : bsErr M b = none) :
    memLoad32 (bsMem M out b) out = mw M b 8 := by
  simp only [bsMem, h]
  have n : ∀ c d, c < 8 → d < 8 → c ≠ d → out + BitVec.ofNat 32 c ≠ out + BitVec.ofNat 32 d :=
    fun c d hc hd e => bmr_ne out hc hd e
  refine (memLoad32_congr fun j hj => ?_).trans (memLoad32_store32_same M out (mw M b 8))
  have hj8 : j < 8 := Nat.lt_trans hj (by decide)
  have m7 : out + BitVec.ofNat 32 j ≠ out + 7 := n j 7 hj8 (by decide) (Nat.ne_of_lt (Nat.lt_trans hj (by decide)))
  have m6 : out + BitVec.ofNat 32 j ≠ out + 6 := n j 6 hj8 (by decide) (Nat.ne_of_lt (Nat.lt_trans hj (by decide)))
  have m5 : out + BitVec.ofNat 32 j ≠ out + 5 := n j 5 hj8 (by decide) (Nat.ne_of_lt (Nat.lt_trans hj (by decide)))
  have m4 : out + BitVec.ofNat 32 j ≠ out + 4 := n j 4 hj8 (by decide) (Nat.ne_of_lt hj)
  rw [memStore8_ne m7, memStore8_ne m6, memStore8_ne m5, memStore8_ne m4]

theorem bms_ld (M : Word → BitVec 8) (a : Word) :
    memLoad32 M a = BitVec.ofNat 32 ((M a).toNat + 256 * (M (a + 1)).toNat + 65536 * (M (a + 2)).toNat +
      16777216 * (M (a + 3)).toNat) := by
  apply BitVec.eq_of_toNat_eq
  have h0 := (M a).isLt; have h1 := (M (a + 1)).isLt; have h2 := (M (a + 2)).isLt
  have h3 := (M (a + 3)).isLt
  rw [memLoad32_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [le32]; omega

theorem bms_sn {k : Nat} (h : k ≤ 1) : bmSlotNum (bmrSlot k) = k := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with e | e <;> subst e <;> rfl

theorem bms_a4 (out : Word) : out + 4 + 1 = out + 5 := by rw [BitVec.add_assoc]; rfl
theorem bms_a5 (out : Word) : out + 4 + 2 = out + 6 := by rw [BitVec.add_assoc]; rfl
theorem bms_a6 (out : Word) : out + 4 + 3 = out + 7 := by rw [BitVec.add_assoc]; rfl

/-- What `decode` leaves at `out` for the record at `b`, in the form
`BmeCopy` names. -/
theorem bms_copy (M : Word → BitVec 8) (out b : Word) :
    BmeCopy (bsMem M out b) out (decodeRecord ((List.range 32).map (mb M b))) := by
  rw [bmr_read M out b]
  cases h : bsErr M b with
  | some e =>
    show bsMem M out b (out + 7) = 2
    simp only [bsMem, h]; exact memStore8_same _ _ _
  | none =>
    obtain ⟨hp, h14, h15, ht⟩ := bms_ok4 ((bmr_err M b).mp h)
    obtain ⟨e4, e5, e6, e7⟩ := bms_bytes M out b h
    have tr := bmr_trial M b
    have h15' : (M (b + 15)).toNat < 4 := by
      have := bmr_fc (M (b + 15))
      have e : ((M (b + 15)).toNat &&& 0xFC == 0) = true := beq_iff_eq.mpr h15
      rw [this] at e; exact of_decide_eq_true e
    refine ⟨(ofNat_toNat_self _).symm, ?_, by rw [e7]; exact hp, ⟨(memLoad32 _ _).isLt, ?_, ?_⟩⟩
    · rw [bms_ld _ (out + 4), bms_a4, bms_a5, bms_a6]
      unfold bmWord bmrSt
      rw [e5, e6, e7, bms_sn (show (M (b + 12)).toNat ≤ 1 from hp)]
      by_cases e : mb M b 13 ≤ 1
      · rw [tr, decide_eq_true e, if_pos rfl] at e4
        rw [e4, if_pos (show (M (b + 13)).toNat ≤ 1 from e)]
        simp only [bmTrialBytes]
        rw [bms_sn (show (M (b + 13)).toNat ≤ 1 from e)]
      · rw [tr, decide_eq_false e] at e4
        rw [e4]
        have z : (M (b + 14)).toNat = 0 := by
          rcases ht with h' | ⟨_, h'⟩
          · exact absurd h' e
          · exact h'
        rw [if_neg (by decide), z]
        rfl
    · unfold bmrSt; rw [e6]; exact h15'
    · intro t htr
      unfold bmrSt at htr
      by_cases e : (bsMem M out b (out + 4)).toNat ≤ 1
      · rw [if_pos e] at htr
        cases htr
        rw [e5]; exact h14
      · rw [if_neg e] at htr; exact nomatch htr

theorem bms_congr {M M' : Word → BitVec 8} {out : Word} {o : Option State}
    (h : ∀ j, j < 8 → M' (out + BitVec.ofNat 32 j) = M (out + BitVec.ofNat 32 j)) (c : BmeCopy M out o) :
    BmeCopy M' out o := by
  cases o with
  | none => show M' (out + 7) = 2; rw [show out + 7 = out + BitVec.ofNat 32 7 from rfl, h 7 (by decide)]; exact c
  | some st =>
    obtain ⟨c1, c2, c3, c4⟩ := c
    refine ⟨(memLoad32_congr fun j hj => h j (Nat.lt_trans hj (by decide))).trans c1, ?_, ?_, c4⟩
    · refine (memLoad32_congr fun j hj => ?_).trans c2
      show M' (out + BitVec.ofNat 32 4 + BitVec.ofNat 32 j) = M (out + BitVec.ofNat 32 4 + BitVec.ofNat 32 j)
      rw [add_ofNat_assoc]; exact h (4 + j) (by omega)
    · rw [show out + 7 = out + BitVec.ofNat 32 7 from rfl, h 7 (by decide)]; exact c3

theorem bms_list {M : Word → BitVec 8} {flash : Nat → BitVec 8} {b : Word} {A : Nat}
    (h : ∀ i, i < 32 → M (b + BitVec.ofNat 32 i) = flash (A + i)) :
    (List.range 32).map (mb M b) = bmcFlash flash A 32 :=
  List.map_congr_left fun i hi => by
    show (M (b + BitVec.ofNat 32 i)).toNat = (flash (A + i)).toNat
    rw [h i (List.mem_range.mp hi)]

/-- `decode` stores only the eight bytes at `out`. -/
theorem bms_bsx (M : Word → BitVec 8) {out b x : Word} (h : Sep out 8 x 1) : bsMem M out b x = M x := by
  have ne : ∀ j, j < 8 → x ≠ out + BitVec.ofNat 32 j := fun j hj e => h j hj 0 (by decide)
    (by rw [add_ofNat_zero]; exact e.symm)
  unfold bsMem
  cases hE : bsErr M b with
  | some e =>
    simp only
    rw [memStore8_ne (show x ≠ out + 7 from ne 7 (by decide)), memStore8_ne (by have := ne 0 (by decide); rwa [add_ofNat_zero] at this)]
  | none =>
    simp only
    rw [memStore8_ne (show x ≠ out + 7 from ne 7 (by decide)), memStore8_ne (show x ≠ out + 6 from ne 6 (by decide)), memStore8_ne (show x ≠ out + 5 from ne 5 (by decide)),
      memStore8_ne (show x ≠ out + 4 from ne 4 (by decide)), memStore32_get_sep (fun i hi j hj e => ne i (by omega)
        (by rw [show j = 0 by omega, add_ofNat_zero] at e; exact e.symm))]

/-! ## The frame below and above `F` -/

theorem bms_lo {F top : Word} {k c n : Nat} (hF : F.toNat + 0xBE80 = top.toNat) (hk : k ≤ F.toNat)
    (hc : c + n ≤ 0xBE80) : Sep (F - BitVec.ofNat 32 k) k (F + BitVec.ofNat 32 c) n := by
  have hFk : F.toNat + 0xBE80 < 2 ^ 32 := by rw [hF]; exact top.isLt
  have hS : (F - BitVec.ofNat 32 k).toNat = F.toNat - k := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega)]; omega
  exact sep_of_le (by rw [hS, bmd_eF hFk (by omega)]; omega) (by rw [bmd_eF hFk (by omega)]; omega)

theorem bms_Fbig {M0 : Word → BitVec 8} {top : Word} {R romStack stack0 : Nat} {romBase : Word}
    {romCode : List Nat} (C : BmEnv M0 top R romStack stack0 romBase romCode) {F : Word}
    (hF : F.toNat + 0xBE80 = top.toNat) :
    0x3FCC8000 + 0x150 + R + romStack + stack0 ≤ F.toNat ∧ F.toNat + 0xBE80 ≤ 0x3FCDFFF0 := by
  have hlo := C.hlo; have hhi := C.hhi
  have hKv : bmK R romStack stack0 = 0xBE80 + 0x150 + R + romStack + stack0 := rfl
  have hbp : bmPtr.toNat = 0x3FCDFFF0 := rfl
  rw [hKv] at hlo; rw [hbp] at hhi
  exact ⟨by omega, by omega⟩

theorem bms_m70 {F : Word} (h : 112 ≤ F.toNat) : F + 0xFFFFFF90 = F - BitVec.ofNat 32 112 :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, BitVec.toNat_sub, show (0xFFFFFF90 : Word).toNat = 2 ^ 32 - 112 from rfl,
      BitVec.toNat_ofNat]
    omega)

/-! ## Calls -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- A call of `flash::read` from `boot_main` for the 32 bytes at flash
address `A` into the buffer at `F + d`. -/
theorem bms_frd {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    (X : BmHyp flash pinned policy M0 top R romStack stack0 romBase romCode E)
    {n : Machine} {F : Word} {off d A : Nat} {imm o : Word} (s : St n.mem BM n off (reg n))
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    (hF : F.toNat + 0xBE80 = top.toNat)
    (h1 : fetchRel bootMainCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : BM + BitVec.ofNat 32 off + imm + o = (img% flashReadAddress))
    (he8 : (BM + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : reg n a0 = BitVec.ofNat 32 A) (hA : A < 2 ^ 32) (ha1 : reg n a1 = F + BitVec.ofNat 32 d)
    (ha2 : reg n a2 = 32) (hsp : reg n sp = F) (hd : d + 32 ≤ 0xBE80) :
    ∃ n', Steps n n' ∧ St n'.mem BM n' (off + 8) (reg n') ∧ reg n' sp = F ∧
      (reg n' a0 = 0 ∨ reg n' a0 = 1) ∧
      (reg n' a0 = 1 → ∀ i, i < 32 → n'.mem (F + BitVec.ofNat 32 d + BitVec.ofNat 32 i) = flash (A + i)) ∧
      BmKeep M0 n'.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) ∧
      ∀ x, Sep (F - BitVec.ofNat 32 (0x150 + R)) (0x150 + R) x 1 → Sep (F + BitVec.ofNat 32 d) 32 x 1 →
        n'.mem x = n.mem x := by
  have C := X.env
  have hlo := C.hlo; have hhi := C.hhi
  have hFk : F.toNat + 0xBE80 < 2 ^ 32 := by rw [hF]; exact top.isLt
  obtain ⟨hFl, hFh⟩ := bms_Fbig C hF
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa (cb := (img% flashReadAddress)) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have hK1 : BmKeep M0 n1.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [mem1]; exact hK
  have hS : (F - BitVec.ofNat 32 (0x150 + R)).toNat = F.toNat - (0x150 + R) := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 0x150 + R) (by omega)]; omega
  have hGF : F - BitVec.ofNat 32 (0x150 + R) + BitVec.ofNat 32 (0x150 + R) = F := BitVec.sub_add_cancel _ _
  have hFa := (bmd_room C hF).1
  have hR4 := C.hR
  have hrl := C.hrl; have hrb := C.hrb
  have env : FRdEnv n1.mem (img% flashReadAddress) (F - BitVec.ofNat 32 (0x150 + R)) (F + BitVec.ofNat 32 d) 32
      R romBase romCode :=
    { hP := rfl
      code := hK1.codeIn C C.frd (.inr ⟨by decide, by decide⟩)
      mset := by
        rw [show ((img% flashReadAddress) : Word) + (img% memsetAddress + 0x100000000 - flashReadAddress) =
          BitVec.ofNat 32 memsetAddress from by decide]
        exact hK1.codeIn C C.memset (.inr ⟨by decide, by decide⟩)
      fw := by
        rw [show ((img% flashReadAddress) : Word) + 0xFFFFFFE8 = BitVec.ofNat 32 romFlashReadWordsAddress from
          by decide]
        exact hK1.codeIn C C.rfw (.inr ⟨by decide, by decide⟩)
      hG := by rw [hS]; omega
      hR := hR4
      hGt := by rw [hS]; omega
      hlen := by rw [bmd_eF hFk (by omega)]; show F.toNat + d + 32 < 2 ^ 32; omega
      sGC := lowSep (by rw [hS]; omega) (by decide) (by decide)
      sGM := lowSep (by rw [hS]; omega) (by decide) (by decide)
      sGW := lowSep (by rw [hS]; omega) (by decide) (by decide)
      sOC := bme_low hF hhi (k := 32) hd (by decide) (by decide)
      sOW := bme_low hF hhi (k := 32) hd (by decide) (by decide)
      sOG := (bms_lo hF (by omega) hd).symm
      rom := hK1.codeIn C C.rom (.inr ⟨hrb, by omega⟩)
      sGR := lowSep (by rw [hS]; omega) hrb (by omega)
      sOR := bme_low hF hhi (k := 32) hd hrb (by omega) }
  obtain ⟨n2, c2, pc2, sp2, _, a02, ok2, fr2⟩ := flashRead_correct X.rom n1 env pc1
    (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1]) (by rw [r1 _ (by decide), ha2])
    (by rw [regs1]; simp +decide only [upd, ↓reduceIte]) (even_clear _ he8)
    (by rw [r1 _ (by decide), hsp, hGF])
  refine ⟨n2, c1.trans c2, ⟨pc2, rfl, fun _ => rfl⟩, by rw [sp2, hGF], a02, fun h i hi => ?_,
    hK.step fun x hx => ?_, fun x h1 h2 => by rw [fr2 x h1 h2, mem1]⟩
  · rw [ok2 h i hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA]
  · rw [fr2 x (bme_below hF hlo (by omega) hx) (bme_kin hF hlo hd hx), mem1]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- A call of `bootstate::decode` from `boot_main` for the record at
`F + b`, into `F + o`. -/
theorem bms_bsd {M0 : Word → BitVec 8} {top : Word} {R romStack stack0 : Nat} {romBase : Word}
    {romCode : List Nat} (C : BmEnv M0 top R romStack stack0 romBase romCode)
    {n : Machine} {F : Word} {off o b : Nat} {imm o' : Word} (s : St n.mem BM n off (reg n))
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    (hF : F.toNat + 0xBE80 = top.toNat)
    (h1 : fetchRel bootMainCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel bootMainCode (off + 4) = some (.jalr ra ra o', 4))
    (hb : BM + BitVec.ofNat 32 off + imm + o' = BSD)
    (he8 : (BM + BitVec.ofNat 32 (off + 8)).toNat % 2 = 0)
    (ha0 : reg n a0 = F + BitVec.ofNat 32 o) (ha1 : reg n a1 = F + BitVec.ofNat 32 b) (hsp : reg n sp = F)
    (ho : o + 8 ≤ 0xBE80) (ho4 : o % 4 = 0) (hbb : b + 32 ≤ 0xBE80) :
    ∃ n', Steps n n' ∧ St n'.mem BM n' (off + 8) (reg n') ∧
      (∀ r, r ≠ ra → r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ t0 →
        reg n' r = reg n r) ∧
      BmKeep M0 n'.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) ∧
      ∀ x, Sep (F - BitVec.ofNat 32 112) 112 x 1 →
        n'.mem x = bsMem n.mem (F + BitVec.ofNat 32 o) (F + BitVec.ofNat 32 b) x := by
  have hlo := C.hlo; have hhi := C.hhi
  have hFk : F.toNat + 0xBE80 < 2 ^ 32 := by rw [hF]; exact top.isLt
  obtain ⟨hFl, hFh⟩ := bms_Fbig C hF
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  obtain ⟨n1, c1, pc1, mem1, regs1⟩ := s.callRa (cb := BSD) hc h1 h2 hb (by decide)
  have r1 := PEnv.reg1 regs1 s.zero
  have sp1 : reg n1 sp = F := by rw [r1 _ (by decide), hsp]
  have e70 : reg n1 sp + 0xFFFFFF90 = F - BitVec.ofNat 32 112 := by rw [sp1]; exact bms_m70 (by omega)
  have hFa := (bmd_room C hF).1
  obtain ⟨n2, c2, pc2, _, k2, mem2⟩ := bootstateDecode_correct n1
    (C.bs.hi fun x hx => by rw [mem1]; exact hK.hiOf C x hx) pc1
    (by rw [r1 _ (by decide), ha0]) (by rw [r1 _ (by decide), ha1])
    (by rw [regs1]; simp +decide only [upd, ↓reduceIte]) (even_clear _ he8)
    (by rw [sp1]; exact hFa) (by rw [sp1]; omega) (by rw [sp1]; omega)
    ⟨fun e => by
      have := congrArg BitVec.toNat e
      rw [bmd_eF hFk (by omega)] at this; exact absurd this (by show ¬ F.toNat + b = 0; omega),
      by rw [bmd_eF hFk (by omega)]; omega⟩
    (by rw [e70]; exact (bms_lo hF (by omega) hbb).symm)
    (bme_F4 C hF (by omega) ho4) (by rw [bmd_eF hFk (by omega)]; omega)
    (by rw [e70]; exact (bms_lo hF (by omega) ho).symm)
  rw [e70, mem1] at mem2
  refine ⟨n2, c1.trans c2, ⟨pc2, rfl, fun _ => rfl⟩,
    fun r hr h0 h1' h2' h3 h4 h5 h6 ht => by rw [k2 r h0 h1' h2' h3 h4 h5 h6 ht, r1 r hr],
    hK.step fun x hx => ?_, mem2⟩
  rw [mem2 x (bme_below hF hlo (by omega) hx), bms_bsx _ (bme_kin hF hlo ho hx)]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- At 0xD2, after a failed flash read, `boot_main` halts. -/
theorem bms_halt {M0 : Word → BitVec 8} {top : Word} {R romStack stack0 : Nat} {romBase : Word}
    {romCode : List Nat} (C : BmEnv M0 top R romStack stack0 romBase romCode) {n : Machine} {F : Word}
    {g : Fin 32 → Word} (s : St n.mem BM n 0xD2 g)
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    (hsp : g sp = F) (hF : F.toNat + 0xBE80 = top.toNat) : Panics n := by
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  obtain ⟨n1, d1, u1⟩ := s.aluImm hc bm_at_d2 (off' := 0xD6) (by decide)
  obtain ⟨n2, c2, pc2, mem2, regs2⟩ := u1.self.callRa (cb := haltBase) hc bm_at_d6 bm_at_da
    (by decide) (by decide)
  have sp2 : reg n2 sp = F := by
    rw [regs2, updz u1.self.zero (by decide), u1.regs, updz s.zero (by decide), hsp]
  have hP : PanicCode n.mem := bmt_panic C.panic (hK.hiOf C)
  exact Panics.of_steps (.cons d1 c2) (halt_panics n2 (by rw [mem2]; exact hP) pc2
    (by rw [sp2]; exact bmd_room C hF))

/-! ## From 0x64 to 0xB4 -/

theorem bms_hiF {F top : Word} {c j : Nat} (hF : F.toNat + 0xBE80 = top.toNat) (hj : c + j + 1 ≤ 0xBE80)
    {k : Nat} (hk : k ≤ F.toNat) : Sep (F - BitVec.ofNat 32 k) k (F + BitVec.ofNat 32 c + BitVec.ofNat 32 j) 1 := by
  rw [add_ofNat_assoc]; exact bms_lo hF hk (by omega)

theorem bms_off (F : Word) {c n d j : Nat} (h : c + n ≤ d + j ∨ d + j + 1 ≤ c) (hc : c + n ≤ 0xBE80)
    (hj : d + j + 1 ≤ 0xBE80) : Sep (F + BitVec.ofNat 32 c) n (F + BitVec.ofNat 32 d + BitVec.ofNat 32 j) 1 := by
  rw [add_ofNat_assoc]; exact sep_offsets F h (by omega) (by omega)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- From 0x64: `boot_main` reads both records, halting when a read fails,
decodes each, and goes on at 0xB4. -/
theorem bms_reads {flash : Nat → BitVec 8} {pinned : Bytes} {policy : Policy} {M0 : Word → BitVec 8}
    {top : Word} {R romStack stack0 : Nat} {romBase : Word} {romCode : List Nat}
    {E : (Word → BitVec 8) → Prop}
    (X : BmHyp flash pinned policy M0 top R romStack stack0 romBase romCode E)
    {n : Machine} {F : Word} (s : St n.mem BM n 0x64 (reg n)) (hF : F.toNat + 0xBE80 = top.toNat)
    (hK : BmKeep M0 n.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0))
    (hsp : reg n sp = F) :
    BmEnd (BmJump flash pinned policy M0 top (bmK R romStack stack0)) n := by
  have C := X.env
  obtain ⟨hFl, hFh⟩ := bms_Fbig C hF
  have hc := hK.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  -- 0x64: the first read.
  obtain ⟨n1, c1, u1⟩ := s.block bmB3 hc bmB3_end ⟨trivial, trivial, trivial, trivial⟩
  have m1 : n1.mem = n.mem := u1.mem
  have r1 : ∀ r, reg n1 r = (runBlock bmB3 (n.mem, reg n)).2 r := fun r => by rw [u1.regs]
  have t1 : St n1.mem BM n1 0x6E (reg n1) := ⟨u1.pc, rfl, fun _ => rfl⟩
  have K1 : BmKeep M0 n1.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [m1]; exact hK
  obtain ⟨n2, c2, t2, sp2, a02, ok2, K2, _⟩ := bms_frd X t1 K1 hF bm_at_6e bm_at_72 (by decide) (by decide)
    (A := 0x28000) (d := 0x10)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, bmB3, upd, ↓reduceIte]; (try rw [s.zero]); try rfl)
    (by decide)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, bmB3, upd, ↓reduceIte]; rw [hsp]; rfl)
    (by rw [r1]; simp +decide only [runBlock, BInstr.run, bmB3, upd, ↓reduceIte]; (try rw [s.zero]); try rfl)
    (by rw [r1, runBlock_reg bmB3 _ _ sp s.zero (by decide), hsp]) (by decide)
  have hc2 := K2.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  rcases a02 with z2 | o2
  · obtain ⟨n3, e3, t3⟩ := t2.taken hc2 0xD2 bm_at_76 (by decide)
      (by show (reg n2 a0 == reg n2 0) = true; rw [z2, t2.zero]; rfl)
    rw [← t3.mem] at K2
    exact BmEnd.pre (c1.trans (c2.trans (.single e3))) (.inr (bms_halt C ⟨t3.pc, rfl, t3.regs⟩ K2 sp2 hF))
  obtain ⟨n3, e3, t3⟩ := t2.notTaken hc2 0x78 bm_at_76 (by decide)
    (by show (reg n2 a0 == reg n2 0) = false; rw [o2, t2.zero]; rfl)
  have t3' : St n3.mem BM n3 0x78 (reg n3) := ⟨t3.pc, rfl, fun _ => rfl⟩
  have m3 : n3.mem = n2.mem := t3.mem
  have K3 : BmKeep M0 n3.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [m3]; exact K2
  have hc3 := K3.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  -- 0x78: the second read.
  obtain ⟨n4, c4, u4⟩ := t3'.block bmB4 hc3 bmB4_end ⟨trivial, trivial, trivial, trivial⟩
  have m4 : n4.mem = n3.mem := u4.mem
  have r4 : ∀ r, reg n4 r = (runBlock bmB4 (n3.mem, reg n3)).2 r := fun r => by rw [u4.regs]
  have t4 : St n4.mem BM n4 0x82 (reg n4) := ⟨u4.pc, rfl, fun _ => rfl⟩
  have K4 : BmKeep M0 n4.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [m4]; exact K3
  have sp3 : reg n3 sp = F := by rw [t3.regs]; exact sp2
  obtain ⟨n5, c5, t5, sp5, a05, ok5, K5, fr5⟩ := bms_frd X t4 K4 hF bm_at_82 bm_at_86 (by decide) (by decide)
    (A := 0x29000) (d := 0x30)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, bmB4, upd, ↓reduceIte]; (try rw [t3'.zero]); try rfl)
    (by decide)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, bmB4, upd, ↓reduceIte]; rw [sp3]; rfl)
    (by rw [r4]; simp +decide only [runBlock, BInstr.run, bmB4, upd, ↓reduceIte]; (try rw [t3'.zero]); try rfl)
    (by rw [r4, runBlock_reg bmB4 _ _ sp t3'.zero (by decide), sp3]) (by decide)
  have hc5 := K5.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  rcases a05 with z5 | o5
  · obtain ⟨n6, e6, t6⟩ := t5.taken hc5 0xD2 bm_at_8a (by decide)
      (by show (reg n5 a0 == reg n5 0) = true; rw [z5, t5.zero]; rfl)
    rw [← t6.mem] at K5
    exact BmEnd.pre (c1.trans (c2.trans (.cons e3 (c4.trans (c5.trans (.single e6))))))
      (.inr (bms_halt C ⟨t6.pc, rfl, t6.regs⟩ K5 sp5 hF))
  obtain ⟨n6, e6, t6⟩ := t5.notTaken hc5 0x8C bm_at_8a (by decide)
    (by show (reg n5 a0 == reg n5 0) = false; rw [o5, t5.zero]; rfl)
  have t6' : St n6.mem BM n6 0x8C (reg n6) := ⟨t6.pc, rfl, fun _ => rfl⟩
  have m6 : n6.mem = n5.mem := t6.mem
  have K6 : BmKeep M0 n6.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [m6]; exact K5
  have hc6 := K6.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  have sp6 : reg n6 sp = F := by rw [t6.regs]; exact sp5
  -- the bytes read
  have b1 : ∀ i, i < 32 → n6.mem (F + BitVec.ofNat 32 0x10 + BitVec.ofNat 32 i) = flash (0x28000 + i) := by
    intro i hi
    rw [m6, fr5 _ (bms_hiF hF (by omega) (by omega)) (bms_off F (by omega) (by decide) (by omega)), m4, m3]
    exact ok2 o2 i hi
  have b2 : ∀ i, i < 32 → n6.mem (F + BitVec.ofNat 32 0x30 + BitVec.ofNat 32 i) = flash (0x29000 + i) := by
    intro i hi; rw [m6]; exact ok5 o5 i hi
  -- 0x8C: the first decode.
  obtain ⟨n7, c7, u7⟩ := t6'.block bmB5 hc6 bmB5_end ⟨trivial, trivial, trivial, trivial, trivial, trivial,
    trivial, trivial⟩
  have m7 : n7.mem = n6.mem := u7.mem
  have r7 : ∀ r, reg n7 r = (runBlock bmB5 (n6.mem, reg n6)).2 r := fun r => by rw [u7.regs]
  have t7 : St n7.mem BM n7 0xA0 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have K7 : BmKeep M0 n7.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [m7]; exact K6
  have sp7 : reg n7 sp = F := by rw [r7, runBlock_reg bmB5 _ _ sp t6'.zero (by decide), sp6]
  have g20 : reg n7 20 = F + BitVec.ofNat 32 0xB9A8 := by
    rw [r7]; simp +decide only [runBlock, BInstr.run, bmB5, upd, ↓reduceIte]; rw [sp6]; rfl
  obtain ⟨n8, c8, t8, k8, K8, f8⟩ := bms_bsd C t7 K7 hF bm_at_a0 bm_at_a4 (by decide) (by decide)
    (o := 0xB9A8) (b := 0x10)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, bmB5, upd, ↓reduceIte]; rw [sp6, BitVec.add_comm]; rfl)
    (by rw [r7]; simp +decide only [runBlock, BInstr.run, bmB5, upd, ↓reduceIte]; rw [sp6]; rfl)
    sp7 (by decide) (by decide) (by decide)
  have hc8 := K8.codeIn C C.code (.inr ⟨by decide, by decide⟩)
  have sp8 : reg n8 sp = F := by
    rw [k8 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), sp7]
  have h20 : reg n8 20 = F + BitVec.ofNat 32 0xB9A8 := by
    rw [k8 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), g20]
  -- 0xA8: the second decode.
  obtain ⟨n9, c9, u9⟩ := t8.block bmB6 hc8 bmB6_end ⟨trivial, trivial, trivial⟩
  have m9 : n9.mem = n8.mem := u9.mem
  have r9 : ∀ r, reg n9 r = (runBlock bmB6 (n8.mem, reg n8)).2 r := fun r => by rw [u9.regs]
  have t9 : St n9.mem BM n9 0xAC (reg n9) := ⟨u9.pc, rfl, fun _ => rfl⟩
  have K9 : BmKeep M0 n9.mem (top - BitVec.ofNat 32 (bmK R romStack stack0)) (bmK R romStack stack0) := by
    rw [m9]; exact K8
  have k9 : ∀ r, r ≠ a0 → r ≠ a1 → reg n9 r = reg n8 r := fun r h0 h1 => by
    rw [r9, runBlock_reg bmB6 _ _ r t8.zero (by simp only [bmB6]; revert h0 h1; revert r; decide)]
  obtain ⟨n10, c10, t10, k10, K10, f10⟩ := bms_bsd C t9 K9 hF bm_at_ac bm_at_b0 (by decide) (by decide)
    (o := 0x50) (b := 0x30)
    (by rw [r9]; simp +decide only [runBlock, BInstr.run, bmB6, upd, ↓reduceIte]; rw [sp8]; rfl)
    (by rw [r9]; simp +decide only [runBlock, BInstr.run, bmB6, upd, ↓reduceIte]; rw [sp8]; rfl)
    (by rw [k9 sp (by decide) (by decide), sp8]) (by decide) (by decide) (by decide)
  have k10' : ∀ r, r = sp ∨ r = 20 → reg n10 r = reg n8 r := fun r hr => by
    rcases hr with rfl | rfl
    · rw [k10 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), k9 sp (by decide) (by decide)]
    · rw [k10 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), k9 20 (by decide) (by decide)]
  -- the copies
  have hk112 : 112 ≤ F.toNat := by omega
  have M8 : ∀ c j, c + j + 1 ≤ 0xBE80 → Sep (F + BitVec.ofNat 32 0xB9A8) 8 (F + BitVec.ofNat 32 c +
      BitVec.ofNat 32 j) 1 → n8.mem (F + BitVec.ofNat 32 c + BitVec.ofNat 32 j) =
      n6.mem (F + BitVec.ofNat 32 c + BitVec.ofNat 32 j) := fun c j hj hs => by
    rw [f8 _ (bms_hiF hF hj hk112), bms_bsx _ hs, m7]
  have cA : BmeCopy n8.mem (F + BitVec.ofNat 32 0xB9A8) (decodeRecord (bmcFlash flash 0x28000 32)) := by
    have := bms_copy n7.mem (F + BitVec.ofNat 32 0xB9A8) (F + BitVec.ofNat 32 0x10)
    rw [bms_list (A := 0x28000) (fun i hi => by rw [m7]; exact b1 i hi)] at this
    exact bms_congr (fun j hj => f8 _ (bms_hiF hF (by omega) hk112)) this
  have cB : BmeCopy n10.mem (F + BitVec.ofNat 32 0x50) (decodeRecord (bmcFlash flash 0x29000 32)) := by
    have := bms_copy n9.mem (F + BitVec.ofNat 32 0x50) (F + BitVec.ofNat 32 0x30)
    rw [bms_list (A := 0x29000) (fun i hi => by
      rw [m9, M8 0x30 i (by omega) (bms_off F (by omega) (by decide) (by omega))]; exact b2 i hi)] at this
    exact bms_congr (fun j hj => f10 _ (bms_hiF hF (by omega) hk112)) this
  have cA' : BmeCopy n10.mem (F + BitVec.ofNat 32 0xB9A8) (decodeRecord (bmcFlash flash 0x28000 32)) :=
    bms_congr (fun j hj => by
      rw [f10 _ (bms_hiF hF (by omega) hk112), bms_bsx _ (bms_off F (by omega) (by decide) (by omega)), m9]) cA
  exact BmEnd.pre (c1.trans (c2.trans (.cons e3 (c4.trans (c5.trans (.cons e6 (c7.trans (c8.trans
    (c9.trans c10))))))))) (bme_sel X t10 hF K10 cA' cB
      (by rw [k10' 20 (.inr rfl)]; exact h20) (by rw [k10' sp (.inl rfl)]; exact sp8))

end C3.RV32.Cur
