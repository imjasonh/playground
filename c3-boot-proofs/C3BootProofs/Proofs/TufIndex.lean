import C3BootProofs.Proofs.LeafStep
import C3BootProofs.Spec.Tuf

/-!
# A TUF part's index, as compiled

`tuf::Index::doc` finds document `i`'s offset in the part and its length.
`Index` holds the 66 lengths and then the root count at `0x108`, and the
compiled function writes `Result<(u32, u32), Error>` to `a0`: a tag byte (0
for `Ok`), the error's byte at 1, and the offset and length at 4 and 8.

`tufIndexDocSpec_ok` and `splitDocs_getD` connect the offsets to
`decodeTufParts`: document `i` starts after the header, the index, and the
documents before it.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem tid_at_0 : fetchRel tufIndexDocCode 0x0 = some (.load .lw a3 a1 0x108, 4) := by decide
theorem tid_at_4 : fetchRel tufIndexDocCode 0x4 = some (.aluImm .add a4 x0 0xFFFFFFFE, 2) := by decide
theorem tid_at_6 : fetchRel tufIndexDocCode 0x6 = some (.branch .bgeu a3 a4 0x40, 4) := by decide
theorem tid_at_a : fetchRel tufIndexDocCode 0xA = some (.aluImm .add (17 : Fin 32) a3 0x2, 4) := by decide
theorem tid_at_e : fetchRel tufIndexDocCode 0xE = some (.aluImm .srl a4 (17 : Fin 32) 0x1E, 4) := by decide
theorem tid_at_12 : fetchRel tufIndexDocCode 0x12 = some (.branch .bne a4 x0 0x34, 2) := by decide
theorem tid_at_14 : fetchRel tufIndexDocCode 0x14 = some (.lui a4 0x40000000, 4) := by decide
theorem tid_at_18 : fetchRel tufIndexDocCode 0x18 = some (.aluImm .add a4 a4 0xFFFFFFFE, 2) := by decide
theorem tid_at_1a : fetchRel tufIndexDocCode 0x1A = some (.branch .bgeu (17 : Fin 32) a4 0x2C, 4) := by decide
theorem tid_at_1e : fetchRel tufIndexDocCode 0x1E = some (.aluImm .add a4 x0 0x43, 4) := by decide
theorem tid_at_22 : fetchRel tufIndexDocCode 0x22 = some (.branch .bltu a2 a4 0x8, 4) := by decide
theorem tid_at_26 : fetchRel tufIndexDocCode 0x26 = some (.aluImm .add a1 x0 0x5, 2) := by decide
theorem tid_at_28 : fetchRel tufIndexDocCode 0x28 = some (.jal x0 0x20, 2) := by decide
theorem tid_at_2a : fetchRel tufIndexDocCode 0x2A = some (.aluImm .sll a4 (17 : Fin 32) 0x2, 4) := by decide
theorem tid_at_2e : fetchRel tufIndexDocCode 0x2E = some (.aluImm .sll a5 a2 0x2, 4) := by decide
theorem tid_at_32 : fetchRel tufIndexDocCode 0x32 = some (.aluImm .add a4 a4 0x8, 2) := by decide
theorem tid_at_34 : fetchRel tufIndexDocCode 0x34 = some (.alu .add a6 a1 a5, 4) := by decide
theorem tid_at_38 : fetchRel tufIndexDocCode 0x38 = some (.branch .beq a5 x0 0x1C, 2) := by decide
theorem tid_at_3a : fetchRel tufIndexDocCode 0x3A = some (.load .lw a3 a1 0x0, 2) := by decide
theorem tid_at_3c : fetchRel tufIndexDocCode 0x3C = some (.alu .add a4 a4 a3, 2) := by decide
theorem tid_at_3e : fetchRel tufIndexDocCode 0x3E = some (.aluImm .add a1 a1 0x4, 2) := by decide
theorem tid_at_40 : fetchRel tufIndexDocCode 0x40 = some (.aluImm .add a5 a5 0xFFFFFFFC, 2) := by decide
theorem tid_at_42 : fetchRel tufIndexDocCode 0x42 = some (.branch .bgeu a4 a3 0xFFFFFFF6, 4) := by decide
theorem tid_at_46 : fetchRel tufIndexDocCode 0x46 = some (.aluImm .add a1 x0 0x6, 2) := by decide
theorem tid_at_48 : fetchRel tufIndexDocCode 0x48 = some (.store .sb a0 a1 0x1, 4) := by decide
theorem tid_at_4c : fetchRel tufIndexDocCode 0x4C = some (.aluImm .add a1 x0 0x1, 2) := by decide
theorem tid_at_4e : fetchRel tufIndexDocCode 0x4E = some (.store .sb a0 a1 0x0, 4) := by decide
theorem tid_at_52 : fetchRel tufIndexDocCode 0x52 = some (.jalr x0 ra 0x0, 2) := by decide
theorem tid_at_54 : fetchRel tufIndexDocCode 0x54 = some (.aluImm .add a1 x0 0x42, 4) := by decide
theorem tid_at_58 : fetchRel tufIndexDocCode 0x58 = some (.branch .bltu a1 (17 : Fin 32) 0xFFFFFFCE, 4) := by decide
theorem tid_at_5c : fetchRel tufIndexDocCode 0x5C = some (.branch .bgeu a2 (17 : Fin 32) 0xFFFFFFCA, 4) := by decide
theorem tid_at_60 : fetchRel tufIndexDocCode 0x60 = some (.aluImm .add a1 x0 0x0, 2) := by decide
theorem tid_at_62 : fetchRel tufIndexDocCode 0x62 = some (.load .lw a2 a6 0x0, 4) := by decide
theorem tid_at_66 : fetchRel tufIndexDocCode 0x66 = some (.store .sw a0 a4 0x4, 2) := by decide
theorem tid_at_68 : fetchRel tufIndexDocCode 0x68 = some (.store .sw a0 a2 0x8, 2) := by decide
theorem tid_at_6a : fetchRel tufIndexDocCode 0x6A = some (.jal x0 0xFFFFFFE4, 2) := by decide
end

/-- Length `j` of the index at `idx`. -/
def idxLen (M : Word → BitVec 8) (idx : Word) (j : Nat) : Nat :=
  (memLoad32 M (idx + BitVec.ofNat 32 (4 * j))).toNat

/-- `acc` plus the `f` lengths from `j`, or `none` when a sum reaches `2 ^ 32`. -/
def idxSum (M : Word → BitVec 8) (idx : Word) : Nat → Nat → Nat → Option Nat
  | _, acc, 0 => some acc
  | j, acc, f + 1 =>
    if acc + idxLen M idx j < 2 ^ 32 then idxSum M idx (j + 1) (acc + idxLen M idx j) f else none

/-- The end of `Index::doc`, once the offset is summed. -/
def tidTail (M : Word → BitVec 8) (idx : Word) (i cnt : Nat) : Option Nat → Except Nat (Nat × Nat)
  | none => .error 6
  | some off => if 66 < cnt ∨ cnt ≤ i then .error 5 else .ok (off, idxLen M idx i)

/-- `Index::doc(i)` for the index at `idx`: the offset and length of
document `i`, or `Error::OutOfRange` (5) or `Error::Overflow` (6). -/
def tufIndexDocSpec (M : Word → BitVec 8) (idx : Word) (i : Nat) : Except Nat (Nat × Nat) :=
  if 0x3FFFFFFC ≤ (memLoad32 M (idx + 0x108)).toNat then .error 6
  else if 67 ≤ i then .error 5
  else tidTail M idx i ((memLoad32 M (idx + 0x108)).toNat + 2)
    (idxSum M idx 0 (8 + 4 * ((memLoad32 M (idx + 0x108)).toNat + 2)) i)

/-- The `Result<(u32, u32), Error>` at `out` holds `r`. -/
def tidOut (M : Word → BitVec 8) (out : Word) : Except Nat (Nat × Nat) → Prop
  | .error e => M out = 1 ∧ M (out + 1) = BitVec.ofNat 8 e
  | .ok (o, l) => M out = 0 ∧ memLoad32 M (out + 4) = BitVec.ofNat 32 o ∧
      memLoad32 M (out + 8) = BitVec.ofNat 32 l

/-- The registers `Index::doc` keeps: all but `a1` through `a7`. -/
abbrev tidKeep (q : Fin 32) : Bool := q.val < 11 || 17 < q.val

/-- What a run from `n` ends with: `Index::doc` returned to `retAddr` with
`r` at `out`. -/
abbrev TidPost (m n : Machine) (out retAddr : Word) (r : Except Nat (Nat × Nat)) : Prop :=
  ∃ m', Steps n m' ∧ m'.pc = retAddr ∧ (∀ q, tidKeep q = true → reg m' q = reg m q) ∧
    (∀ x, Sep out 12 x 1 → m'.mem x = m.mem x) ∧ tidOut m'.mem out r

theorem tid_sub4 (g : Nat) : BitVec.ofNat 32 (4 * (g + 1)) + 0xFFFFFFFC = BitVec.ofNat 32 (4 * g) := by
  show BitVec.ofNat 32 (4 * (g + 1)) + BitVec.ofNat 32 0xFFFFFFFC = _
  rw [ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem tid_ne0 {g : Nat} (h : 4 * (g + 1) < 2 ^ 32) : (BitVec.ofNat 32 (4 * (g + 1)) == 0) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro e
  have := congrArg BitVec.toNat e
  rw [ls_ofNat_toNat_lt h] at this
  exact absurd (show 4 * (g + 1) = 0 from this) (by omega)

theorem tid_srl (x : Word) : branchTaken .bne (aluEval .srl x 0x1E) 0 = decide (2 ^ 30 ≤ x.toNat) := by
  have hv : (aluEval .srl x 0x1E).toNat = x.toNat / 2 ^ 30 := by
    show (x >>> 30).toNat = _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  show (aluEval .srl x 0x1E != 0) = _
  by_cases h : 2 ^ 30 ≤ x.toNat
  · rw [decide_eq_true h]
    apply bne_iff_ne.mpr
    intro e
    have := congrArg BitVec.toNat e
    rw [hv] at this
    have h2 : 1 ≤ x.toNat / 2 ^ 30 := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
    exact absurd (show x.toNat / 2 ^ 30 = 0 from this) (by omega)
  · rw [decide_eq_false h]
    have : aluEval .srl x 0x1E = 0 := BitVec.eq_of_toNat_eq (by
      rw [hv, Nat.div_eq_of_lt (show x.toNat < 2 ^ 30 by omega)]; rfl)
    rw [this]; rfl

theorem tid_sll2 {c : Nat} (h : c < 2 ^ 30) : aluEval .sll (BitVec.ofNat 32 c) 0x2 = BitVec.ofNat 32 (4 * c) := by
  show BitVec.ofNat 32 c <<< 2 = _
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, ls_ofNat_toNat_lt (show c < 2 ^ 32 by omega),
    ls_ofNat_toNat_lt (show 4 * c < 2 ^ 32 by omega), show (2 : Nat) ^ 2 = 4 from rfl,
    Nat.mod_eq_of_lt (show c * 4 < 2 ^ 32 by omega)]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- **The compiled `tuf::Index::doc`**: called with the result's address
`out` in `a0` (4-byte aligned), the index's address `idx` in `a1` (4-byte
aligned), and `i` in `a2`, it writes `tufIndexDocSpec` of the index to
`out` as `tidOut` reads it and returns. It writes no other memory and keeps
every register but `a1` through `a7`. It reads the index before it writes. -/
theorem tufIndexDoc_correct (m : Machine) {base out idx iw retAddr : Word}
    (hc : CodeIn m.mem base tufIndexDocCode) (hbase : base.toNat % 2 = 0) (hpc : m.pc = base)
    (ha0 : reg m a0 = out) (ha1 : reg m a1 = idx) (ha2 : reg m a2 = iw)
    (hout : out.toNat % 4 = 0) (hidx : idx.toNat % 4 = 0) (sOC : Sep out 12 base tufIndexDocCode.length)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ (∀ q, tidKeep q = true → reg m' q = reg m q) ∧
      (∀ x, Sep out 12 x 1 → m'.mem x = m.mem x) ∧ tidOut m'.mem out (tufIndexDocSpec m.mem idx iw.toNat) := by
  have hiw := iw.isLt
  -- the error exit at 0x48, with the error in `a1`
  have errX : ∀ {n : Machine} {f : Fin 32 → Word} (e : Nat), e < 256 → St m.mem base n 0x48 f →
      f a0 = out → f a1 = BitVec.ofNat 32 e → f ra = retAddr → (∀ q, tidKeep q = true → f q = reg m q) →
      TidPost m n out retAddr (.error e) := by
    intro n f e he st fa0 fa1 fra kk
    obtain ⟨n1, d1, u1⟩ := st.sb hc tid_at_48 (off' := 0x4C) (by decide)
    rw [fa0, fa1, ls_byte he] at u1
    have hc1 : CodeIn (memStore8 m.mem (out + 1) (BitVec.ofNat 8 e)) base tufIndexDocCode :=
      hc.store8 (sOC.sub (c := 1) (l := 1) (by decide))
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hc1 tid_at_4c (off' := 0x4E) (by decide)
    obtain ⟨n3, d3, u3⟩ := u2.sb hc1 tid_at_4e (off' := 0x52) (by decide)
    have v1 : (upd f a1 (aluEval .add (f 0) 0x1) a1).extractLsb' 0 8 = 1 := by
      rw [upd_app, if_neg (by decide), if_pos rfl, st.zero]; rfl
    have w0 : upd f a1 (aluEval .add (f 0) 0x1) a0 = out := by rw [upd_ne' (by decide) st.zero, fa0]
    rw [v1, w0, add_lit_zero] at u3
    have hc3 : CodeIn (memStore8 (memStore8 m.mem (out + 1) (BitVec.ofNat 8 e)) out 1) base tufIndexDocCode :=
      hc1.store8 (by have := sOC.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this)
    obtain ⟨n4, d4, pc4, mem4, regs4⟩ := u3.jalr hc3 tid_at_52
    have hne : out + 1 ≠ out := fun h => absurd (h.trans (add_ofNat_zero out).symm)
      (add_ofNat_ne out (c := 1) (d := 0) (by decide) (by decide) (by decide))
    refine ⟨n4, .cons d1 (.cons d2 (.cons d3 (.single d4))), ?_, fun q hq => ?_, fun x hx => ?_, ?_⟩
    · rw [pc4, upd_ne' (by decide) st.zero, fra, add_lit_zero, hret]
    · rw [regs4]; exact ls_keep (by decide) st.zero _ kk q hq
    · rw [mem4, memStore8_ne (by rw [← add_ofNat_zero out]; exact ls_sep_ne hx (by decide)),
        memStore8_ne (show x ≠ out + 1 from ls_sep_ne hx (i := 1) (by decide))]
    · simp only [tidOut]
      exact ⟨by rw [mem4, memStore8_same], by rw [mem4, memStore8_ne hne, memStore8_same]⟩
  -- `Error::OutOfRange`, from 0x26
  have err5 : ∀ {n : Machine} {f : Fin 32 → Word}, St m.mem base n 0x26 f →
      f a0 = out → f ra = retAddr → (∀ q, tidKeep q = true → f q = reg m q) →
      TidPost m n out retAddr (.error 5) := by
    intro n f st fa0 fra kk
    obtain ⟨n1, d1, u1⟩ := st.aluImm hc tid_at_26 (off' := 0x28) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.jump hc tid_at_28 (off' := 0x48) (by decide) (by
      rw [u1.pc]; exact ls_even hbase 0x28 0x20 0x48 (by decide) (by decide))
    obtain ⟨m', c', h⟩ := errX 5 (by decide) u2 (by rw [upd_ne' (by decide) st.zero, fa0])
      (by rw [upd_app, if_neg (by decide), if_pos rfl, st.zero]; rfl)
      (by rw [upd_ne' (by decide) st.zero, fra]) (ls_keep (by decide) st.zero _ kk)
    exact ⟨m', .cons d1 (.cons d2 c'), h⟩
  -- `Error::Overflow`, from 0x46
  have err6 : ∀ {n : Machine} {f : Fin 32 → Word}, St m.mem base n 0x46 f →
      f a0 = out → f ra = retAddr → (∀ q, tidKeep q = true → f q = reg m q) →
      TidPost m n out retAddr (.error 6) := by
    intro n f st fa0 fra kk
    obtain ⟨n1, d1, u1⟩ := st.aluImm hc tid_at_46 (off' := 0x48) (by decide)
    obtain ⟨m', c', h⟩ := errX 6 (by decide) u1 (by rw [upd_ne' (by decide) st.zero, fa0])
      (by rw [upd_app, if_neg (by decide), if_pos rfl, st.zero]; rfl)
      (by rw [upd_ne' (by decide) st.zero, fra]) (ls_keep (by decide) st.zero _ kk)
    exact ⟨m', .cons d1 c', h⟩
  -- the success path, from 0x54
  have okTail : ∀ (off cnt : Nat) {n : Machine}, off < 2 ^ 32 → cnt < 2 ^ 32 → St m.mem base n 0x54 (reg n) →
      reg n a0 = out → reg n a4 = BitVec.ofNat 32 off → reg n a6 = idx + BitVec.ofNat 32 (4 * iw.toNat) →
      reg n 17 = BitVec.ofNat 32 cnt → reg n a2 = iw → reg n ra = retAddr →
      (∀ q, tidKeep q = true → reg n q = reg m q) →
      TidPost m n out retAddr (tidTail m.mem idx iw.toNat cnt (some off)) := by
    intro off cnt n hoff hcnt st f0 f4 f6 f7 f2 fra kk
    simp only [tidTail]
    obtain ⟨n1, d1, u1⟩ := st.aluImm hc tid_at_54 (off' := 0x58) (by decide)
    have v1 : reg n1 a1 = 0x42 := by rw [ls_get u1 (by decide), ls_r0]; rfl
    have k1 := ls_kst u1 (by decide) kk
    by_cases c1 : 66 < cnt
    · obtain ⟨n2, d2, u2⟩ := u1.self.taken hc 0x26 tid_at_58 (by decide) (by
        rw [v1, ls_oth u1 (by decide), f7, ls_ult, ls_ofNat_toNat_lt hcnt]; exact decide_eq_true c1)
      obtain ⟨m', c', h⟩ := err5 u2 (by rw [ls_oth u1 (by decide), f0]) (by rw [ls_oth u1 (by decide), fra]) k1
      rw [if_pos (Or.inl c1 : 66 < cnt ∨ cnt ≤ iw.toNat)]; exact ⟨m', .cons d1 (.cons d2 c'), h⟩
    obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc 0x5C tid_at_58 (by decide) (by
      rw [v1, ls_oth u1 (by decide), f7, ls_ult, ls_ofNat_toNat_lt hcnt]; exact decide_eq_false c1)
    have k2 := ls_kbr u2 k1
    have r2 : ∀ q, q ≠ a1 → reg n2 q = reg n q := fun q h => by rw [u2.regs, ls_oth u1 h]
    by_cases c2 : cnt ≤ iw.toNat
    · obtain ⟨n3, d3, u3⟩ := u2.self.taken hc 0x26 tid_at_5c (by decide) (by
        rw [r2 a2 (by decide), f2, r2 17 (by decide), f7, ls_uge, ls_ofNat_toNat_lt hcnt,
          decide_eq_false (by omega)]; rfl)
      obtain ⟨m', c', h⟩ := err5 u3 (by rw [r2 a0 (by decide), f0]) (by rw [r2 ra (by decide), fra]) k2
      rw [if_pos (Or.inr c2 : 66 < cnt ∨ cnt ≤ iw.toNat)]; exact ⟨m', .cons d1 (.cons d2 (.cons d3 c')), h⟩
    obtain ⟨n3, d3, u3⟩ := u2.self.notTaken hc 0x60 tid_at_5c (by decide) (by
      rw [r2 a2 (by decide), f2, r2 17 (by decide), f7, ls_uge, ls_ofNat_toNat_lt hcnt,
        decide_eq_true (by omega)]; rfl)
    rw [if_neg (fun h => h.elim c1 c2)]
    have k3 := ls_kbr u3 k2
    have r3 : ∀ q, q ≠ a1 → reg n3 q = reg n q := fun q h => by rw [u3.regs, r2 q h]
    obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hc tid_at_60 (off' := 0x62) (by decide)
    have k4 := ls_kst u4 (by decide) k3
    have v4 : reg n4 a1 = 0 := by rw [ls_get u4 (by decide), ls_r0]; rfl
    have r4 : ∀ q, q ≠ a1 → reg n4 q = reg n q := fun q h => by rw [ls_oth u4 h, r3 q h]
    obtain ⟨n5, d5, u5⟩ := u4.self.lw hc tid_at_62 (off' := 0x66) (by decide) (by
      rw [r4 a6 (by decide), f6, add_lit_zero]; exact aligned_add hidx (by omega))
    have k5 := ls_kst u5 (by decide) k4
    have v5 : reg n5 a2 = memLoad32 m.mem (idx + BitVec.ofNat 32 (4 * iw.toNat)) := by
      rw [ls_get u5 (by decide), r4 a6 (by decide), f6, add_lit_zero]
    have r5 : ∀ q, q ≠ a1 → q ≠ a2 → reg n5 q = reg n q := fun q h1 h2 => by rw [ls_oth u5 h2, r4 q h1]
    have w0 : reg n5 a0 = out := by rw [r5 a0 (by decide) (by decide), f0]
    obtain ⟨n6, d6, u6⟩ := u5.self.sw hc tid_at_66 (off' := 0x68) (by decide) (by
      rw [w0]; exact aligned_add hout (k := 4) (by decide))
    rw [w0, r5 a4 (by decide) (by decide), f4] at u6
    have hc6 : CodeIn (memStore32 m.mem (out + 4) (BitVec.ofNat 32 off)) base tufIndexDocCode :=
      hc.store32 (sOC.sub (c := 4) (l := 4) (by decide))
    obtain ⟨n7, d7, u7⟩ := u6.sw hc6 tid_at_68 (off' := 0x6A) (by decide) (by
      rw [w0]; exact aligned_add hout (k := 8) (by decide))
    rw [w0, v5] at u7
    have hc7 : CodeIn (memStore32 (memStore32 m.mem (out + 4) (BitVec.ofNat 32 off)) (out + 8)
        (memLoad32 m.mem (idx + BitVec.ofNat 32 (4 * iw.toNat)))) base tufIndexDocCode :=
      hc6.store32 (sOC.sub (c := 8) (l := 4) (by decide))
    obtain ⟨n8, d8, u8⟩ := u7.jump hc7 tid_at_6a (off' := 0x4E) (by decide) (by
      rw [u7.pc]; exact ls_even hbase 0x6A 0xFFFFFFE4 0x4E (by decide) (by decide))
    obtain ⟨n9, d9, u9⟩ := u8.sb hc7 tid_at_4e (off' := 0x52) (by decide)
    have v5a1 : reg n5 a1 = 0 := by rw [ls_oth u5 (by decide), v4]
    rw [w0, v5a1, add_lit_zero] at u9
    have hc9 : CodeIn (memStore8 (memStore32 (memStore32 m.mem (out + 4) (BitVec.ofNat 32 off)) (out + 8)
        (memLoad32 m.mem (idx + BitVec.ofNat 32 (4 * iw.toNat)))) out ((0 : Word).extractLsb' 0 8))
        base tufIndexDocCode :=
      hc7.store8 (by have := sOC.sub (c := 0) (l := 1) (by decide); rwa [add_ofNat_zero] at this)
    obtain ⟨n10, d10, pc10, mem10, regs10⟩ := u9.jalr hc9 tid_at_52
    have s04 : Sep out 1 (out + 4) 4 := by
      have := sep_offsets out (c := 0) (n := 1) (d := 4) (k := 4) (.inl (by decide)) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
    have s08 : Sep out 1 (out + 8) 4 := by
      have := sep_offsets out (c := 0) (n := 1) (d := 8) (k := 4) (.inl (by decide)) (by decide) (by decide)
      rwa [add_ofNat_zero] at this
    have s48 : Sep (out + 8) 4 (out + 4) 4 :=
      sep_offsets out (c := 8) (n := 4) (d := 4) (k := 4) (.inr (by decide)) (by decide) (by decide)
    refine ⟨n10, .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8
      (.cons d9 (.single d10))))))))), ?_, fun q hq => by rw [regs10]; exact k5 q hq, fun x hx => ?_, ?_⟩
    · rw [pc10, r5 ra (by decide) (by decide), fra, add_lit_zero, hret]
    · rw [mem10, memStore8_ne (by rw [← add_ofNat_zero out]; exact ls_sep_ne hx (by decide)),
        memStore32_get_sep (show Sep (out + 8) 4 x 1 from hx.sub (c := 8) (l := 4) (by decide)),
        memStore32_get_sep (show Sep (out + 4) 4 x 1 from hx.sub (c := 4) (l := 4) (by decide))]
    · simp only [tidOut]
      refine ⟨?_, ?_, ?_⟩
      · rw [mem10, memStore8_same]; rfl
      · rw [mem10, memLoad32_store8_sep s04, memLoad32_store32_sep s48, memLoad32_store32_same]
      · rw [mem10, memLoad32_store8_sep s08, memLoad32_store32_same, idxLen, ls_ofNat_toNat]
  -- the offset loop at 0x38, with `k` lengths summed and `g` to go
  have loop : ∀ cnt, cnt < 2 ^ 32 → iw.toNat < 67 → ∀ g k acc (n : Machine), k + g = iw.toNat → acc < 2 ^ 32 →
      St m.mem base n 0x38 (reg n) → reg n a0 = out → reg n a1 = idx + BitVec.ofNat 32 (4 * k) →
      reg n a5 = BitVec.ofNat 32 (4 * g) → reg n a4 = BitVec.ofNat 32 acc →
      reg n a6 = idx + BitVec.ofNat 32 (4 * iw.toNat) → reg n 17 = BitVec.ofNat 32 cnt → reg n a2 = iw →
      reg n ra = retAddr → (∀ q, tidKeep q = true → reg n q = reg m q) →
      TidPost m n out retAddr (tidTail m.mem idx iw.toNat cnt (idxSum m.mem idx k acc g)) := by
    intro cnt hcnt hi67 g
    induction g with
    | zero =>
      intro k acc n _ hacc st f0 _ f5 f4 f6 f7 f2 fra kk
      obtain ⟨n1, d1, u1⟩ := st.taken hc 0x54 tid_at_38 (by decide) (by rw [f5, ls_r0]; rfl)
      obtain ⟨m', c', h⟩ := okTail acc cnt hacc hcnt u1.self (by rw [u1.regs, f0]) (by rw [u1.regs, f4])
        (by rw [u1.regs, f6]) (by rw [u1.regs, f7]) (by rw [u1.regs, f2]) (by rw [u1.regs, fra]) (ls_kbr u1 kk)
      simp only [idxSum]; exact ⟨m', .cons d1 c', h⟩
    | succ g ih =>
      intro k acc n hk hacc st f0 f1 f5 f4 f6 f7 f2 fra kk
      have hg : 4 * (g + 1) < 2 ^ 32 := by omega
      obtain ⟨n1, d1, u1⟩ := st.notTaken hc 0x3A tid_at_38 (by decide) (by rw [f5, ls_r0]; exact tid_ne0 hg)
      have k1 := ls_kbr u1 kk
      obtain ⟨n2, d2, u2⟩ := u1.self.lw hc tid_at_3a (off' := 0x3C) (by decide) (by
        rw [u1.regs, f1, add_lit_zero]; exact aligned_add hidx (by omega))
      have k2 := ls_kst u2 (by decide) k1
      have v2 : reg n2 a3 = memLoad32 m.mem (idx + BitVec.ofNat 32 (4 * k)) := by
        rw [ls_get u2 (by decide), u1.regs, f1, add_lit_zero]
      have r2 : ∀ q, q ≠ a3 → reg n2 q = reg n q := fun q h => by rw [ls_oth u2 h, u1.regs]
      obtain ⟨n3, d3, u3⟩ := u2.self.alu hc tid_at_3c (off' := 0x3E) (by decide)
      have k3 := ls_kst u3 (by decide) k2
      have v3 : reg n3 a4 = BitVec.ofNat 32 (acc + idxLen m.mem idx k) := by
        rw [ls_get u3 (by decide), ev_add, v2, r2 a4 (by decide), f4, ← ls_ofNat_toNat
          (memLoad32 m.mem (idx + BitVec.ofNat 32 (4 * k))), ofNat_add_ofNat]; rfl
      obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hc tid_at_3e (off' := 0x40) (by decide)
      have k4 := ls_kst u4 (by decide) k3
      obtain ⟨n5, d5, u5⟩ := u4.self.aluImm hc tid_at_40 (off' := 0x42) (by decide)
      have k5 := ls_kst u5 (by decide) k4
      have r5 : ∀ q, q ≠ a1 → q ≠ a3 → q ≠ a4 → q ≠ a5 → reg n5 q = reg n q := fun q h1 h3 h4 h5 => by
        rw [ls_oth u5 h5, ls_oth u4 h1, ls_oth u3 h4, r2 q h3]
      have v5a4 : reg n5 a4 = BitVec.ofNat 32 (acc + idxLen m.mem idx k) := by
        rw [ls_oth u5 (by decide), ls_oth u4 (by decide), v3]
      have v5a3 : reg n5 a3 = memLoad32 m.mem (idx + BitVec.ofNat 32 (4 * k)) := by
        rw [ls_oth u5 (by decide), ls_oth u4 (by decide), ls_oth u3 (by decide), v2]
      have v5a1 : reg n5 a1 = idx + BitVec.ofNat 32 (4 * (k + 1)) := by
        rw [ls_oth u5 (by decide), ls_get u4 (by decide), ev_add, ls_oth u3 (by decide), r2 a1 (by decide), f1]
        show idx + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 4 = _
        rw [add_ofNat_assoc, show 4 * k + 4 = 4 * (k + 1) by omega]
      have v5a5 : reg n5 a5 = BitVec.ofNat 32 (4 * g) := by
        rw [ls_get u5 (by decide), ev_add, ls_oth u4 (by decide), ls_oth u3 (by decide), r2 a5 (by decide), f5,
          tid_sub4]
      have hL : idxLen m.mem idx k = (memLoad32 m.mem (idx + BitVec.ofNat 32 (4 * k))).toNat := rfl
      have hLlt := (memLoad32 m.mem (idx + BitVec.ofNat 32 (4 * k))).isLt
      by_cases ov : 2 ^ 32 ≤ acc + idxLen m.mem idx k
      · obtain ⟨n6, d6, u6⟩ := u5.self.notTaken hc 0x46 tid_at_42 (by decide) (by
          rw [v5a4, v5a3, ls_uge, BitVec.toNat_ofNat, Nat.mod_eq_sub_mod ov, Nat.mod_eq_of_lt (by omega),
            ← hL, decide_eq_true (by omega)]; rfl)
        obtain ⟨m', c', h⟩ := err6 u6 (by rw [r5 a0 (by decide) (by decide) (by decide) (by decide), f0])
          (by rw [r5 ra (by decide) (by decide) (by decide) (by decide), fra]) k5
        simp only [idxSum]; rw [if_neg (show ¬ (acc + idxLen m.mem idx k < 2 ^ 32) by omega)]
        exact ⟨m', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 c'))))), h⟩
      obtain ⟨n6, d6, u6⟩ := u5.self.taken hc 0x38 tid_at_42 (by decide) (by
        rw [v5a4, v5a3, ls_uge, ls_ofNat_toNat_lt (by omega), ← hL, decide_eq_false (by omega)]; rfl)
      have r6 : ∀ q, q ≠ a1 → q ≠ a3 → q ≠ a4 → q ≠ a5 → reg n6 q = reg n q := fun q h1 h3 h4 h5 => by
        rw [u6.regs, r5 q h1 h3 h4 h5]
      obtain ⟨m', c', h⟩ := ih (k + 1) (acc + idxLen m.mem idx k) n6 (by omega) (by omega) u6.self
        (by rw [r6 a0 (by decide) (by decide) (by decide) (by decide), f0]) (by rw [u6.regs, v5a1])
        (by rw [u6.regs, v5a5]) (by rw [u6.regs, v5a4])
        (by rw [r6 a6 (by decide) (by decide) (by decide) (by decide), f6])
        (by rw [r6 17 (by decide) (by decide) (by decide) (by decide), f7])
        (by rw [r6 a2 (by decide) (by decide) (by decide) (by decide), f2])
        (by rw [r6 ra (by decide) (by decide) (by decide) (by decide), fra]) (ls_kbr u6 k5)
      simp only [idxSum]; rw [if_pos (show acc + idxLen m.mem idx k < 2 ^ 32 by omega)]
      exact ⟨m', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 c'))))), h⟩
  -- the checks before the loop
  obtain ⟨Rw, hRw⟩ : ∃ Rw, memLoad32 m.mem (idx + 0x108) = Rw := ⟨_, rfl⟩
  have hRlt := Rw.isLt
  have s0 : St m.mem base m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have k0 : ∀ q, tidKeep q = true → reg m q = reg m q := fun _ _ => rfl
  obtain ⟨n1, d1, u1⟩ := s0.lw hc tid_at_0 (off' := 0x4) (by decide) (by
    rw [ha1]; exact aligned_add hidx (k := 0x108) (by decide))
  have k1 := ls_kst u1 (by decide) k0
  have v1 : reg n1 a3 = Rw := by rw [ls_get u1 (by decide), ha1, hRw]
  obtain ⟨n2, d2, u2⟩ := u1.self.aluImm hc tid_at_4 (off' := 0x6) (by decide)
  have k2 := ls_kst u2 (by decide) k1
  have v2 : reg n2 a4 = BitVec.ofNat 32 0xFFFFFFFE := by rw [ls_get u2 (by decide), ls_r0]; rfl
  have r2 : ∀ q, q ≠ a3 → q ≠ a4 → reg n2 q = reg m q := fun q h3 h4 => by rw [ls_oth u2 h4, ls_oth u1 h3]
  have f0 : ∀ {n : Machine}, (∀ q, q ≠ a3 → q ≠ a4 → reg n q = reg m q) → reg n a0 = out := fun h => by
    rw [h a0 (by decide) (by decide), ha0]
  have fra : ∀ {n : Machine}, (∀ q, q ≠ a3 → q ≠ a4 → reg n q = reg m q) → reg n ra = retAddr := fun h => by
    rw [h ra (by decide) (by decide), hra]
  have spec6 : 0x3FFFFFFC ≤ Rw.toNat → tufIndexDocSpec m.mem idx iw.toNat = .error 6 := fun h => by
    unfold tufIndexDocSpec; rw [hRw]; exact if_pos h
  by_cases A : 0xFFFFFFFE ≤ Rw.toNat
  · obtain ⟨n3, d3, u3⟩ := u2.self.taken hc 0x46 tid_at_6 (by decide) (by
      rw [ls_oth u2 (by decide), v1, v2, ls_uge, ls_ofNat_toNat_lt (c := 0xFFFFFFFE) (by decide),
        decide_eq_false (show ¬ Rw.toNat < 0xFFFFFFFE by omega)]; rfl)
    obtain ⟨m', c', h⟩ := err6 u3 (f0 r2) (fra r2) k2
    rw [spec6 (by omega)]; exact ⟨m', .cons d1 (.cons d2 (.cons d3 c')), h⟩
  obtain ⟨n3, d3, u3⟩ := u2.self.notTaken hc 0xA tid_at_6 (by decide) (by
    rw [ls_oth u2 (by decide), v1, v2, ls_uge, ls_ofNat_toNat_lt (c := 0xFFFFFFFE) (by decide),
      decide_eq_true (show Rw.toNat < 0xFFFFFFFE by omega)]; rfl)
  have k3 := ls_kbr u3 k2
  obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hc tid_at_a (off' := 0xE) (by decide)
  have k4 := ls_kst u4 (by decide) k3
  have v4 : reg n4 17 = BitVec.ofNat 32 (Rw.toNat + 2) := by
    rw [ls_get u4 (by decide), u3.regs, ls_oth u2 (by decide), v1]; exact ls_add_lit Rw 2
  obtain ⟨n5, d5, u5⟩ := u4.self.aluImm hc tid_at_e (off' := 0x12) (by decide)
  have k5 := ls_kst u5 (by decide) k4
  have r5 : ∀ q, q ≠ a3 → q ≠ a4 → q ≠ 17 → reg n5 q = reg m q := fun q h3 h4 h7 => by
    rw [ls_oth u5 h4, ls_oth u4 h7, u3.regs, r2 q h3 h4]
  have v5 : reg n5 17 = BitVec.ofNat 32 (Rw.toNat + 2) := by rw [ls_oth u5 (by decide), v4]
  have hz5 : reg n5 a4 = aluEval .srl (BitVec.ofNat 32 (Rw.toNat + 2)) 0x1E := by
    rw [ls_get u5 (by decide), v4]
  have g5 : ∀ q, q ≠ a3 → q ≠ a4 → q ≠ 17 → reg n5 q = reg m q := r5
  have f05 : reg n5 a0 = out := by rw [g5 a0 (by decide) (by decide) (by decide), ha0]
  have fra5 : reg n5 ra = retAddr := by rw [g5 ra (by decide) (by decide) (by decide), hra]
  by_cases B1 : 2 ^ 30 ≤ Rw.toNat + 2
  · obtain ⟨n6, d6, u6⟩ := u5.self.taken hc 0x46 tid_at_12 (by decide) (by
      rw [hz5, ls_r0, tid_srl, ls_ofNat_toNat_lt (by omega)]; exact decide_eq_true B1)
    obtain ⟨m', c', h⟩ := err6 u6 f05 fra5 k5
    rw [spec6 (by omega)]; exact ⟨m', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 c'))))), h⟩
  obtain ⟨n6, d6, u6⟩ := u5.self.notTaken hc 0x14 tid_at_12 (by decide) (by
    rw [hz5, ls_r0, tid_srl, ls_ofNat_toNat_lt (by omega)]; exact decide_eq_false B1)
  have k6 := ls_kbr u6 k5
  obtain ⟨n7, d7, u7⟩ := u6.self.lui hc tid_at_14 (off' := 0x18) (by decide)
  have k7 := ls_kst u7 (by decide) k6
  obtain ⟨n8, d8, u8⟩ := u7.self.aluImm hc tid_at_18 (off' := 0x1A) (by decide)
  have k8 := ls_kst u8 (by decide) k7
  have v8 : reg n8 a4 = BitVec.ofNat 32 0x3FFFFFFE := by rw [ls_get u8 (by decide), ls_get u7 (by decide)]; rfl
  have g8 : ∀ q, q ≠ a4 → reg n8 q = reg n5 q := fun q h => by rw [ls_oth u8 h, ls_oth u7 h, u6.regs]
  by_cases B2 : 0x3FFFFFFE ≤ Rw.toNat + 2
  · obtain ⟨n9, d9, u9⟩ := u8.self.taken hc 0x46 tid_at_1a (by decide) (by
      rw [g8 17 (by decide), v5, v8, ls_uge, ls_ofNat_toNat_lt (c := Rw.toNat + 2) (by omega),
        ls_ofNat_toNat_lt (c := 0x3FFFFFFE) (by decide),
        decide_eq_false (show ¬ Rw.toNat + 2 < 0x3FFFFFFE by omega)]; rfl)
    obtain ⟨m', c', h⟩ := err6 u9 (by rw [g8 a0 (by decide), f05]) (by rw [g8 ra (by decide), fra5]) k8
    rw [spec6 (by omega)]
    exact ⟨m', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 c')))))))), h⟩
  obtain ⟨n9, d9, u9⟩ := u8.self.notTaken hc 0x1E tid_at_1a (by decide) (by
    rw [g8 17 (by decide), v5, v8, ls_uge, ls_ofNat_toNat_lt (c := Rw.toNat + 2) (by omega),
      ls_ofNat_toNat_lt (c := 0x3FFFFFFE) (by decide),
      decide_eq_true (show Rw.toNat + 2 < 0x3FFFFFFE by omega)]; rfl)
  have k9 := ls_kbr u9 k8
  obtain ⟨n10, d10, u10⟩ := u9.self.aluImm hc tid_at_1e (off' := 0x22) (by decide)
  have k10 := ls_kst u10 (by decide) k9
  have g10 : ∀ q, q ≠ a4 → reg n10 q = reg n5 q := fun q h => by rw [ls_oth u10 h, u9.regs, g8 q h]
  have v10 : reg n10 a4 = 0x43 := by rw [ls_get u10 (by decide), ls_r0]; rfl
  have a2_5 : reg n5 a2 = iw := by rw [g5 a2 (by decide) (by decide) (by decide), ha2]
  have hspec : tufIndexDocSpec m.mem idx iw.toNat = if 67 ≤ iw.toNat then .error 5 else
      tidTail m.mem idx iw.toNat (Rw.toNat + 2) (idxSum m.mem idx 0 (8 + 4 * (Rw.toNat + 2)) iw.toNat) := by
    unfold tufIndexDocSpec; rw [hRw]; exact if_neg (by omega)
  rw [hspec]
  by_cases C : 67 ≤ iw.toNat
  · obtain ⟨n11, d11, u11⟩ := u10.self.notTaken hc 0x26 tid_at_22 (by decide) (by
      rw [g10 a2 (by decide), a2_5, v10, ls_ult]; exact decide_eq_false (show ¬ iw.toNat < 67 by omega))
    obtain ⟨m', c', h⟩ := err5 u11 (by rw [g10 a0 (by decide), f05]) (by rw [g10 ra (by decide), fra5]) k10
    rw [if_pos C]
    exact ⟨m', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
      (.cons d10 (.cons d11 c')))))))))), h⟩
  rw [if_neg C]
  obtain ⟨n11, d11, u11⟩ := u10.self.taken hc 0x2A tid_at_22 (by decide) (by
    rw [g10 a2 (by decide), a2_5, v10, ls_ult]; exact decide_eq_true (show iw.toNat < 67 by omega))
  have k11 := ls_kbr u11 k10
  obtain ⟨n12, d12, u12⟩ := u11.self.aluImm hc tid_at_2a (off' := 0x2E) (by decide)
  have k12 := ls_kst u12 (by decide) k11
  obtain ⟨n13, d13, u13⟩ := u12.self.aluImm hc tid_at_2e (off' := 0x32) (by decide)
  have k13 := ls_kst u13 (by decide) k12
  obtain ⟨n14, d14, u14⟩ := u13.self.aluImm hc tid_at_32 (off' := 0x34) (by decide)
  have k14 := ls_kst u14 (by decide) k13
  obtain ⟨n15, d15, u15⟩ := u14.self.alu hc tid_at_34 (off' := 0x38) (by decide)
  have k15 := ls_kst u15 (by decide) k14
  have g15 : ∀ q, q ≠ a4 → q ≠ a5 → q ≠ a6 → reg n15 q = reg n5 q := fun q h4 h5 h6 => by
    rw [ls_oth u15 h6, ls_oth u14 h4, ls_oth u13 h5, ls_oth u12 h4, u11.regs, g10 q h4]
  have v13a5 : reg n13 a5 = BitVec.ofNat 32 (4 * iw.toNat) := by
    rw [ls_get u13 (by decide), ls_oth u12 (by decide), u11.regs, g10 a2 (by decide), a2_5]
    exact (congrArg (fun x => aluEval .sll x 0x2) (ls_ofNat_toNat iw).symm).trans
      (tid_sll2 (c := iw.toNat) (by omega))
  have v14a5 : reg n14 a5 = BitVec.ofNat 32 (4 * iw.toNat) := by rw [ls_oth u14 (by decide), v13a5]
  have v15a5 : reg n15 a5 = BitVec.ofNat 32 (4 * iw.toNat) := by rw [ls_oth u15 (by decide), v14a5]
  have v14a1 : reg n14 a1 = idx := by
    rw [ls_oth u14 (by decide), ls_oth u13 (by decide), ls_oth u12 (by decide), u11.regs, g10 a1 (by decide),
      g5 a1 (by decide) (by decide) (by decide), ha1]
  have v15a4 : reg n15 a4 = BitVec.ofNat 32 (8 + 4 * (Rw.toNat + 2)) := by
    rw [ls_oth u15 (by decide), ls_get u14 (by decide), ev_add, ls_oth u13 (by decide), ls_get u12 (by decide),
      u11.regs, g10 17 (by decide), v5, tid_sll2 (c := Rw.toNat + 2) (by omega)]
    show BitVec.ofNat 32 (4 * (Rw.toNat + 2)) + BitVec.ofNat 32 8 = _
    rw [ofNat_add_ofNat, Nat.add_comm]
  have v15a6 : reg n15 a6 = idx + BitVec.ofNat 32 (4 * iw.toNat) := by
    rw [ls_get u15 (by decide), ev_add, v14a1, v14a5]
  obtain ⟨m', c', h⟩ := loop (Rw.toNat + 2) (by omega) (by omega) iw.toNat 0 (8 + 4 * (Rw.toNat + 2)) n15
    (by omega) (by omega) u15.self (by rw [g15 a0 (by decide) (by decide) (by decide), f05])
    (by rw [g15 a1 (by decide) (by decide) (by decide), g5 a1 (by decide) (by decide) (by decide), ha1]
        exact (add_ofNat_zero idx).symm)
    v15a5 v15a4 v15a6 (by rw [g15 17 (by decide) (by decide) (by decide), v5])
    (by rw [g15 a2 (by decide) (by decide) (by decide), a2_5]) (by rw [g15 ra (by decide) (by decide) (by decide), fra5])
    k15
  exact ⟨m', .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9
    (.cons d10 (.cons d11 (.cons d12 (.cons d13 (.cons d14 (.cons d15 c')))))))))))))), h⟩

theorem idxSum_take {M : Word → BitVec 8} {idx : Word} : ∀ (lens : List Nat) (i k acc : Nat), i ≤ lens.length →
    (∀ j, j < lens.length → idxLen M idx (k + j) = lens.getD j 0) → acc + (lens.take i).sum < 2 ^ 32 →
    idxSum M idx k acc i = some (acc + (lens.take i).sum)
  | _, 0, k, acc, _, _, _ => by simp [idxSum]
  | [], i + 1, _, _, hi, _, _ => absurd hi (by simp)
  | L :: ls, i + 1, k, acc, hi, h, hs => by
    have h0 : idxLen M idx k = L := by simpa using h 0 (by simp)
    rw [List.take_succ_cons, List.sum_cons] at hs ⊢
    simp only [idxSum]
    rw [h0, if_pos (show acc + L < 2 ^ 32 by omega), idxSum_take ls i (k + 1) (acc + L) (by simp at hi; omega)
      (fun j hj => by
        have := h (j + 1) (by simp; omega)
        rwa [List.getD_cons_succ, show k + (j + 1) = k + 1 + j by omega] at this) (by omega),
      Nat.add_assoc]

/-- `Index::doc(i)` when the index holds the lengths `lens`, as many as the
root count says: document `i` starts after the 8-byte header, the index,
and the documents before it. -/
theorem tufIndexDocSpec_ok {M : Word → BitVec 8} {idx : Word} {lens : List Nat}
    (hcnt : lens.length = (memLoad32 M (idx + 0x108)).toNat + 2) (hle : lens.length ≤ 66)
    (hL : ∀ j, j < lens.length → idxLen M idx j = lens.getD j 0)
    (hsum : 8 + 4 * lens.length + lens.sum < 2 ^ 32) {i : Nat} (hi : i < lens.length) :
    tufIndexDocSpec M idx i = .ok (8 + 4 * lens.length + (lens.take i).sum, lens.getD i 0) := by
  have htake : (lens.take i).sum ≤ lens.sum := by
    have := congrArg List.sum (List.take_append_drop i lens)
    rw [List.sum_append] at this; omega
  unfold tufIndexDocSpec
  rw [if_neg (show ¬ 0x3FFFFFFC ≤ (memLoad32 M (idx + 0x108)).toNat by omega),
    if_neg (show ¬ 67 ≤ i by omega), ← hcnt,
    idxSum_take lens i 0 _ (Nat.le_of_lt hi) (fun j hj => by rw [Nat.zero_add]; exact hL j hj) (by omega)]
  simp only [tidTail]
  rw [if_neg (fun h => h.elim (fun h1 => absurd h1 (by omega)) (fun h2 => absurd h2 (by omega))), hL i hi]

/-- `splitDocs` puts document `i` right after the documents before it. -/
theorem splitDocs_getD : ∀ {lens : List Nat} {bytes : Bytes} {docs : List Bytes} {r : Bytes},
    splitDocs lens bytes = some (docs, r) → ∀ i, i < lens.length →
      docs.getD i [] = (bytes.drop (lens.take i).sum).take (lens.getD i 0)
  | [], _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | len :: lens, bytes, docs, r, h, i, hi => by
    by_cases hl : len ≤ bytes.length
    · cases hs : splitDocs lens (bytes.drop len) with
      | none =>
        have e : splitDocs (len :: lens) bytes = none := by simp [splitDocs, require, hl, hs]
        rw [e] at h; cases h
      | some p =>
        obtain ⟨docs', r'⟩ := p
        have e : splitDocs (len :: lens) bytes = some (bytes.take len :: docs', r') := by
          simp [splitDocs, require, hl, hs]
        rw [e] at h
        cases h
        cases i with
        | zero => rfl
        | succ i =>
          rw [List.getD_cons_succ, List.take_succ_cons, List.sum_cons, List.getD_cons_succ,
            ← List.drop_drop, splitDocs_getD hs i (by simp at hi; omega)]
    · have e : splitDocs (len :: lens) bytes = none := by simp [splitDocs, require, hl]
      rw [e] at h; cases h

end C3.RV32
