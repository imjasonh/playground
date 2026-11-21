import C3BootProofs.Proofs.DerElement

/-!
# `Der::oid`, as compiled

`Der::oid` reads an `0x01, 0x11, 0x06, 0xce, 0x22, 0xcc, 0x2a, 0x84, 0x48, 0x00, 0x19, 0x46,
    0x97, 0x00, 0x00, 0x00, 0xe7, 0x80, 0xc0, 0x8b, 0x12, 0x45, 0x1d, 0xcd,
    0x22, 0x48, 0x05, 0x47, 0x42, 0x86, 0xaa, 0x86, 0x63, 0x00, 0x08, 0x02,
    0x83, 0x87, 0x06, 0x00, 0x93, 0x85, 0x07, 0x08, 0x93, 0xb5, 0x15, 0x00,
    0xf9, 0x8d, 0x99, 0xed, 0x85, 0x06, 0xfd, 0x83, 0x13, 0xc7, 0x17, 0x00,
    0x7d, 0x16, 0x7d, 0xf2, 0xb3, 0x35, 0x00, 0x01, 0xf9, 0x8d, 0x89, 0xc5,
    0x08, 0xc0, 0x23, 0x22, 0x04, 0x01, 0x09, 0xa8, 0x51, 0x45, 0x19, 0xa0,
    0x03, 0x45, 0x81, 0x00, 0x23, 0x20, 0x04, 0x00, 0x23, 0x02, 0xa4, 0x00,
    0xf2, 0x40, 0x62, 0x44, 0x05, 0x61, 0x82, 0x80JECT IDENTIFIER` element through `Der::element`
and checks its contents: not empty, each subidentifier in its shortest
base-128 form, and the last byte ending one.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem oid_at_0 : fetchRel derOidCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFE0, 2) := by decide
theorem oid_at_2 : fetchRel derOidCode 0x2 = some (.store .sw sp ra 0x1C, 2) := by decide
theorem oid_at_4 : fetchRel derOidCode 0x4 = some (.store .sw sp (8 : Fin 32) 0x18, 2) := by decide
theorem oid_at_6 : fetchRel derOidCode 0x6 = some (.alu .add (8 : Fin 32) x0 a0, 2) := by decide
theorem oid_at_8 : fetchRel derOidCode 0x8 = some (.aluImm .add a0 sp 0x4, 2) := by decide
theorem oid_at_a : fetchRel derOidCode 0xA = some (.aluImm .add a2 x0 0x6, 2) := by decide
theorem oid_at_c : fetchRel derOidCode 0xC = some (.auipc ra 0x0, 4) := by decide
theorem oid_at_10 : fetchRel derOidCode 0x10 = some (.jalr ra ra 0xFFFFF8BC, 4) := by decide
theorem oid_at_14 : fetchRel derOidCode 0x14 = some (.load .lw a0 sp 0x4, 2) := by decide
theorem oid_at_16 : fetchRel derOidCode 0x16 = some (.branch .beq a0 x0 0x3E, 2) := by decide
theorem oid_at_18 : fetchRel derOidCode 0x18 = some (.load .lw a6 sp 0x8, 2) := by decide
theorem oid_at_1a : fetchRel derOidCode 0x1A = some (.aluImm .add a4 x0 0x1, 2) := by decide
theorem oid_at_1c : fetchRel derOidCode 0x1C = some (.alu .add a2 x0 a6, 2) := by decide
theorem oid_at_1e : fetchRel derOidCode 0x1E = some (.alu .add a3 x0 a0, 2) := by decide
theorem oid_at_20 : fetchRel derOidCode 0x20 = some (.branch .beq a6 x0 0x20, 4) := by decide
theorem oid_at_24 : fetchRel derOidCode 0x24 = some (.load .lb a5 a3 0x0, 4) := by decide
theorem oid_at_28 : fetchRel derOidCode 0x28 = some (.aluImm .add a1 a5 0x80, 4) := by decide
theorem oid_at_2c : fetchRel derOidCode 0x2C = some (.aluImm .sltu a1 a1 0x1, 4) := by decide
theorem oid_at_30 : fetchRel derOidCode 0x30 = some (.alu .and a1 a1 a4, 2) := by decide
theorem oid_at_32 : fetchRel derOidCode 0x32 = some (.branch .bne a1 x0 0x1E, 2) := by decide
theorem oid_at_34 : fetchRel derOidCode 0x34 = some (.aluImm .add a3 a3 0x1, 2) := by decide
theorem oid_at_36 : fetchRel derOidCode 0x36 = some (.aluImm .srl a5 a5 0x1F, 2) := by decide
theorem oid_at_38 : fetchRel derOidCode 0x38 = some (.aluImm .xor a4 a5 0x1, 4) := by decide
theorem oid_at_3c : fetchRel derOidCode 0x3C = some (.aluImm .add a2 a2 0xFFFFFFFF, 2) := by decide
theorem oid_at_3e : fetchRel derOidCode 0x3E = some (.branch .bne a2 x0 0xFFFFFFE6, 2) := by decide
theorem oid_at_40 : fetchRel derOidCode 0x40 = some (.alu .sltu a1 x0 a6, 4) := by decide
theorem oid_at_44 : fetchRel derOidCode 0x44 = some (.alu .and a1 a1 a4, 2) := by decide
theorem oid_at_46 : fetchRel derOidCode 0x46 = some (.branch .beq a1 x0 0xA, 2) := by decide
theorem oid_at_48 : fetchRel derOidCode 0x48 = some (.store .sw (8 : Fin 32) a0 0x0, 2) := by decide
theorem oid_at_4a : fetchRel derOidCode 0x4A = some (.store .sw (8 : Fin 32) a6 0x4, 4) := by decide
theorem oid_at_4e : fetchRel derOidCode 0x4E = some (.jal x0 0x12, 2) := by decide
theorem oid_at_50 : fetchRel derOidCode 0x50 = some (.aluImm .add a0 x0 0x14, 2) := by decide
theorem oid_at_52 : fetchRel derOidCode 0x52 = some (.jal x0 0x6, 2) := by decide
theorem oid_at_54 : fetchRel derOidCode 0x54 = some (.load .lbu a0 sp 0x8, 4) := by decide
theorem oid_at_58 : fetchRel derOidCode 0x58 = some (.store .sw (8 : Fin 32) x0 0x0, 4) := by decide
theorem oid_at_5c : fetchRel derOidCode 0x5C = some (.store .sb (8 : Fin 32) a0 0x4, 4) := by decide
theorem oid_at_60 : fetchRel derOidCode 0x60 = some (.load .lw ra sp 0x1C, 2) := by decide
theorem oid_at_62 : fetchRel derOidCode 0x62 = some (.load .lw (8 : Fin 32) sp 0x18, 2) := by decide
theorem oid_at_64 : fetchRel derOidCode 0x64 = some (.aluImm .add sp sp 0x20, 2) := by decide
theorem oid_at_66 : fetchRel derOidCode 0x66 = some (.jalr x0 ra 0x0, 2) := by decide
end

/-- `derOidOk.go` with an early failure apart: `none` when a subidentifier
starts with 0x80, else whether the bytes end a subidentifier. -/
def oidScan : Bool → Bytes → Option Bool
  | atStart, [] => some atStart
  | atStart, b :: bs => if atStart && b == 0x80 then none else oidScan (b < 0x80) bs

theorem oidScan_go : ∀ (bs : Bytes) (atStart : Bool),
    derOidOk.go atStart bs = (match oidScan atStart bs with | none => false | some a => a)
  | [], _ => rfl
  | b :: bs, atStart => by
    simp only [derOidOk.go, oidScan]
    split
    · rfl
    · exact oidScan_go bs _

theorem oid_b1 : ∀ b : BitVec 8,
    aluEval .sltu (aluEval .add (b.signExtend 32) 0x80) 1 = if b.toNat = 0x80 then 1 else 0 := by decide

theorem oid_b2 : ∀ b : BitVec 8,
    aluEval .xor (aluEval .srl (b.signExtend 32) 0x1F) 1 = if b.toNat < 0x80 then 1 else 0 := by decide

theorem oid_and (P : Prop) [Decidable P] (y : Bool) :
    aluEval .and (if P then (1 : Word) else 0) (if y then 1 else 0) = if (y && decide P) then 1 else 0 := by
  by_cases hp : P
  · rw [ite_eq_left hp, decide_eq_true hp]; cases y <;> rfl
  · rw [ite_eq_right hp, decide_eq_false hp]; cases y <;> rfl

/-- One byte of the check, from 0x28 after the load. -/
def oidChk : List BInstr := [.aluImm .add a1 a5 0x80, .aluImm .sltu a1 a1 0x1, .alu .and a1 a1 a4]

/-- The rest of a byte, from 0x34. -/
def oidNext : List BInstr :=
  [.aluImm .add a3 a3 0x1, .aluImm .srl a5 a5 0x1F, .aluImm .xor a4 a5 0x1, .aluImm .add a2 a2 0xFFFFFFFF]

section
set_option maxRecDepth 20000
theorem oidChk_end : blockEnd derOidCode 0x28 oidChk = some 0x32 := by decide
theorem oidNext_end : blockEnd derOidCode 0x34 oidNext = some 0x3E := by decide
end

set_option maxRecDepth 20000 in
/-- **The check loop**, from 0x24 with `k` content bytes left at `p` and the
state "at the start of a subidentifier" in `a4`: it leaves at 0x50 when a
subidentifier starts with 0x80, and otherwise at 0x40 with the final state
in `a4`. -/
theorem oid_loop {M : Word → BitVec 8} {P : Word} (hc : CodeIn M P derOidCode) :
    ∀ k, ∀ {n : Machine} {atStart : Bool} {p : Word}, 1 ≤ k → k < 2 ^ 32 → St M P n 0x24 (reg n) →
      reg n a2 = BitVec.ofNat 32 k → reg n a3 = p → reg n a4 = (if atStart then 1 else 0) →
      ∃ n', Steps n n' ∧
        (match oidScan atStart (memBytes M p k) with
          | none => St M P n' 0x50 (reg n')
          | some a => St M P n' 0x40 (reg n') ∧ reg n' a4 = (if a then 1 else 0)) ∧
        ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n' r = reg n r
  | 0, _, _, _, hk, _, _, _, _, _ => absurd hk (by decide)
  | k + 1, n, atStart, p, _, hk32, s, ra2, ra3, ra4 => by
    have hz := s.zero
    obtain ⟨n1, d1, u1⟩ := s.lb hc oid_at_24 (off' := 0x28) (by decide)
    rw [ra3, add_lit_zero] at u1
    obtain ⟨n2, c2, u2⟩ := St.block oidChk u1 hc oidChk_end (by simp [BlockOk, BInstr.ok, oidChk])
    simp only [runBlock, BInstr.run, oidChk] at u2
    have g2 : ∀ r, reg n2 r = _ := u2.regs
    have a12 : reg n2 a1 = if (atStart && (M p).toNat == 0x80) then 1 else 0 := by
      rw [g2]; simp +decide only [upd_app, ↓reduceIte]
      rw [oid_b1, ra4, oid_and]; rfl
    have hmem : memBytes M p (k + 1) = (M p).toNat :: memBytes M (p + 1) k := memBytes_succ _ _ _
    have k2 : ∀ r, r ≠ a1 → r ≠ a5 → reg n2 r = reg n r := fun r h1 h5 => by
      rw [g2]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz.symm
      simp only [upd_app, h0, h1, h5, ite_false]
    by_cases hfail : (atStart && (M p).toNat == 0x80) = true
    · obtain ⟨n3, d3, u3⟩ := u2.self.taken hc 0x50 oid_at_32 (by decide) (by
        rw [a12]; simp only [hfail, ↓reduceIte]; rfl)
      refine ⟨n3, .cons d1 (c2.trans (.single d3)), ?_, fun r h1 _ _ _ h5 => by rw [u3.regs, k2 r h1 h5]⟩
      rw [hmem]; simp only [oidScan, hfail, ↓reduceIte]; exact u3.self
    have hf' : (atStart && (M p).toNat == 0x80) = false := by simpa using hfail
    obtain ⟨n3, d3, u3⟩ := u2.self.notTaken hc 0x34 oid_at_32 (by decide) (by
      rw [a12]; simp only [hf', Bool.false_eq_true, ↓reduceIte]; rfl)
    obtain ⟨n4, c4, u4⟩ := St.block oidNext u3.self hc oidNext_end (by simp [BlockOk, BInstr.ok, oidNext])
    simp only [runBlock, BInstr.run, oidNext] at u4
    have g4 : ∀ r, reg n4 r = _ := u4.regs
    have e3 : reg n3 = reg n2 := funext u3.regs
    have v4 : reg n4 a3 = p + 1 ∧ reg n4 a4 = (if (M p).toNat < 0x80 then 1 else 0) ∧
        reg n4 a2 = BitVec.ofNat 32 k := by
      simp +decide only [g4, upd_app, ↓reduceIte, e3]
      rw [k2 a3 (by decide) (by decide), ra3, k2 a2 (by decide) (by decide), ra2]
      refine ⟨rfl, ?_, ?_⟩
      · rw [g2]; simp +decide only [upd_app, ↓reduceIte]; exact oid_b2 _
      · apply BitVec.eq_of_toNat_eq
        rw [ev_add, BitVec.toNat_add, ofNat_tn hk32, ofNat_tn (by omega)]
        show (k + 1 + 4294967295) % 2 ^ 32 = k
        omega
    obtain ⟨v4a3, v4a4, v4a2⟩ := v4
    have k4 : ∀ r, r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → reg n4 r = reg n r := fun r h1 h2 h3 h4 h5 => by
      rw [g4]
      by_cases h0 : r.val = 0
      · have : r = 0 := Fin.ext h0
        subst this; simp [upd]; exact hz.symm
      simp only [upd_app, h0, h2, h3, h4, h5, ite_false]; rw [e3, k2 r h1 h5]
    have hscan : oidScan atStart (memBytes M p (k + 1)) = oidScan ((M p).toNat < 0x80) (memBytes M (p + 1) k) := by
      rw [hmem]; simp only [oidScan, hf', Bool.false_eq_true, ↓reduceIte]
    by_cases hk : k = 0
    · subst hk
      obtain ⟨n5, d5, u5⟩ := u4.self.notTaken hc 0x40 oid_at_3e (by decide) (by rw [v4a2, u4.self.zero]; decide)
      refine ⟨n5, .cons d1 (c2.trans (.cons d3 (c4.trans (.single d5)))), ?_, fun r h1 h2 h3 h4 h5 => by
        rw [u5.regs, k4 r h1 h2 h3 h4 h5]⟩
      rw [hscan]
      refine ⟨u5.self, ?_⟩
      rw [u5.regs, v4a4]
      by_cases hb : (M p).toNat < 0x80 <;> simp [hb]
    · obtain ⟨n5, d5, u5⟩ := u4.self.taken hc 0x24 oid_at_3e (by decide) (by
        rw [v4a2, u4.self.zero]; simp only [branchTaken, bne_iff_ne, ne_eq]; intro h
        have := congrArg BitVec.toNat h; rw [ofNat_tn (by omega)] at this; exact hk this)
      obtain ⟨n6, c6, h6, k6⟩ := oid_loop hc k (atStart := decide ((M p).toNat < 0x80)) (by omega) (by omega) u5.self
        (by rw [u5.regs, v4a2]) (by rw [u5.regs, v4a3]) (by rw [u5.regs, v4a4]; simp)
      refine ⟨n6, .cons d1 (c2.trans (.cons d3 (c4.trans (.cons d5 c6)))), ?_, fun r h1 h2 h3 h4 h5 => by
        rw [k6 r h1 h2 h3 h4 h5, u5.regs, k4 r h1 h2 h3 h4 h5]⟩
      rw [hscan]; exact h6

theorem memStore8_pt {M M' : Word → BitVec 8} {a x : Word} {v : BitVec 8} (h : M x = M' x) :
    memStore8 M a v x = memStore8 M' a v x := by
  unfold memStore8; split
  · rfl
  · exact h

theorem memStore32_pt {M M' : Word → BitVec 8} {a v x : Word} (h : M x = M' x) :
    memStore32 M a v x = memStore32 M' a v x := by
  unfold memStore32
  exact memStore8_pt (memStore8_pt (memStore8_pt (memStore8_pt h)))

theorem derTlv_bound {L : Bytes} {t : DerTlv} (h : derTlv L = .ok t) : t.header + t.len ≤ L.length := by
  match L with
  | [] => simp only [derTlv] at h; cases h
  | [tag] =>
    simp only [derTlv] at h
    by_cases h1 : tag % 32 = 31
    · simp only [h1, ↓reduceIte] at h; cases h
    · simp only [h1, ↓reduceIte] at h; cases h
  | tag :: first :: afterLen =>
    simp only [derTlv] at h
    by_cases h1 : tag % 32 = 31
    · simp only [h1, ↓reduceIte] at h; cases h
    simp only [h1, ↓reduceIte] at h
    by_cases h2 : first < 0x80
    · simp only [h2, ↓reduceIte] at h
      by_cases h3 : afterLen.length < first
      · simp only [h3, ↓reduceIte] at h; cases h
      · simp only [h3, ↓reduceIte] at h; cases h; simp only [List.length_cons]; omega
    simp only [h2, ↓reduceIte] at h
    by_cases h3 : first % 128 = 0 ∨ 4 < first % 128
    · simp only [h3, ↓reduceIte] at h; cases h
    simp only [h3, ↓reduceIte] at h
    clear h3
    by_cases h4 : afterLen.length < first % 128
    · simp only [h4, ↓reduceIte] at h; cases h
    simp only [h4, ↓reduceIte] at h
    by_cases h5 : afterLen.head? = some 0
    · simp only [h5, ↓reduceIte] at h; cases h
    simp only [h5, ↓reduceIte] at h
    cases hl : derLongLen 0 (afterLen.take (first % 128)) with
    | error e => simp only [hl] at h; cases h
    | ok len =>
      simp only [hl] at h
      by_cases h6 : len < 0x80
      · simp only [h6, ↓reduceIte] at h; cases h
      simp only [h6, ↓reduceIte] at h
      by_cases h7 : afterLen.length - first % 128 < len
      · simp only [h7, ↓reduceIte] at h; cases h
      simp only [h7, ↓reduceIte] at h; cases h; simp only [List.length_cons]; omega

theorem derElement_bound {tag : Nat} {L : Bytes} {t : DerTlv} (h : derElement tag L = .ok t) :
    t.header + t.len ≤ L.length := by
  unfold derElement at h
  split at h
  · cases h
  · split at h
    · exact derTlv_bound h
    · cases h

theorem memBytes_drop_take {M : Word → BitVec 8} {p : Word} {n h l : Nat} (hl : h + l ≤ n) :
    ((memBytes M p n).drop h).take l = memBytes M (p + BitVec.ofNat 32 h) l := by
  unfold memBytes
  rw [← List.map_drop, ← List.map_take]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, List.length_drop, List.length_range]; omega
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
    rw [add_ofNat_assoc]

/-- The reader at `d` after `Der::element` returns `r`. -/
def derAdvance (M : Word → BitVec 8) (d rp rl : Word) : Except DerError DerTlv → Word → BitVec 8
  | .error _ => M
  | .ok t => memStore32 (memStore32 M (d + 8) (rp + BitVec.ofNat 32 (t.header + t.len))) (d + 0xC)
      (rl - BitVec.ofNat 32 (t.header + t.len))

theorem derTlvMem_outside {M : Word → BitVec 8} {o d rp rl x : Word} (r : Except DerError DerTlv)
    (hx : Sep o 17 x 1) : derTlvMem M o d rp rl r x = derAdvance M d rp rl r x := by
  cases r with
  | error e =>
    simp only [derTlvMem, derAdvance]
    rw [memStore8_ne fun e' => hx 4 (by decide) 0 (by decide) (by rw [add_ofNat_zero]; exact e'.symm),
      memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)]
  | ok t =>
    simp only [derTlvMem, derAdvance]
    rw [memStore8_ne fun e' => hx 0x10 (by decide) 0 (by decide) (by rw [add_ofNat_zero]; exact e'.symm),
      memStore32_get_sep (a := o + 0xC) (hx.sub (c := 0xC) (l := 4) (by decide)),
      memStore32_get_sep (a := o + 8) (hx.sub (c := 8) (l := 4) (by decide)),
      memStore32_get_sep (a := o + 4) (hx.sub (c := 4) (l := 4) (by decide)),
      memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)]

theorem derAdvance_outside {M : Word → BitVec 8} {d rp rl x : Word} (r : Except DerError DerTlv)
    (hx : Sep (d + 8) 8 x 1) : derAdvance M d rp rl r x = M x := by
  cases r with
  | error e => rfl
  | ok t =>
    simp only [derAdvance]
    rw [memStore32_get_sep (a := d + 0xC) (by
        rw [show d + 0xC = d + 8 + BitVec.ofNat 32 4 by rw [BitVec.add_assoc]; rfl]; exact hx.sub (by decide)),
      memStore32_get_sep (hx.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)]

theorem derAdvance_pt {M M' : Word → BitVec 8} {d rp rl x : Word} (r : Except DerError DerTlv) (h : M x = M' x) :
    derAdvance M d rp rl r x = derAdvance M' d rp rl r x := by
  cases r with
  | error e => exact h
  | ok t => exact memStore32_pt (memStore32_pt h)

theorem derTlvMem_err0 {M : Word → BitVec 8} {o d rp rl : Word} (e : DerError) :
    memLoad32 (derTlvMem M o d rp rl (.error e)) o = 0 := by
  simp only [derTlvMem]
  rw [memLoad32_store8_sep (sep_offsets o (c := 4) (n := 1) (d := 0) (k := 4) (.inr (by decide)) (by decide)
    (by decide) |> fun h => by rwa [add_ofNat_zero] at h), memLoad32_store32_same]

theorem derTlvMem_err4 {M : Word → BitVec 8} {o d rp rl : Word} (e : DerError) :
    derTlvMem M o d rp rl (.error e) (o + 4) = derErrByte e := by
  simp only [derTlvMem]; rw [memStore8_same]

theorem derTlvMem_ok0 {M : Word → BitVec 8} {o d rp rl : Word} (t : DerTlv) :
    memLoad32 (derTlvMem M o d rp rl (.ok t)) o = rp + BitVec.ofNat 32 t.header := by
  simp only [derTlvMem]
  rw [show o + 4 = o + BitVec.ofNat 32 4 from rfl, show o + 8 = o + BitVec.ofNat 32 8 from rfl,
    show o + 0xC = o + BitVec.ofNat 32 0xC from rfl, show o + 0x10 = o + BitVec.ofNat 32 0x10 from rfl]
  have s : ∀ c, 4 ≤ c → c + 4 ≤ 0x14 → Sep (o + BitVec.ofNat 32 c) 4 o 4 := fun c h1 h2 => by
    have := sep_offsets o (c := c) (n := 4) (d := 0) (k := 4) (.inr (by omega)) (by omega) (by decide)
    rwa [add_ofNat_zero] at this
  rw [memLoad32_store8_sep (sep_offsets o (c := 0x10) (n := 1) (d := 0) (k := 4) (.inr (by decide)) (by decide)
      (by decide) |> fun h => by rwa [add_ofNat_zero] at h),
    memLoad32_store32_sep (s 0xC (by decide) (by decide)), memLoad32_store32_sep (s 8 (by decide) (by decide)),
    memLoad32_store32_sep (s 4 (by decide) (by decide)), memLoad32_store32_same]

theorem derTlvMem_ok4 {M : Word → BitVec 8} {o d rp rl : Word} (t : DerTlv) :
    memLoad32 (derTlvMem M o d rp rl (.ok t)) (o + 4) = BitVec.ofNat 32 t.len := by
  simp only [derTlvMem]
  rw [show o + 4 = o + BitVec.ofNat 32 4 from rfl, show o + 8 = o + BitVec.ofNat 32 8 from rfl,
    show o + 0xC = o + BitVec.ofNat 32 0xC from rfl, show o + 0x10 = o + BitVec.ofNat 32 0x10 from rfl]
  have s : ∀ c, 8 ≤ c → c + 4 ≤ 0x14 → Sep (o + BitVec.ofNat 32 c) 4 (o + BitVec.ofNat 32 4) 4 := fun c h1 h2 =>
    sep_offsets o (.inr (by omega)) (by omega) (by decide)
  rw [memLoad32_store8_sep (sep_offsets o (c := 0x10) (n := 1) (d := 4) (k := 4) (.inr (by decide)) (by decide)
      (by decide)),
    memLoad32_store32_sep (s 0xC (by decide) (by decide)), memLoad32_store32_sep (s 8 (by decide) (by decide)),
    memLoad32_store32_same]

/-- What `Der::oid` stores at `out`. -/
def derOidMem (M : Word → BitVec 8) (out rp : Word) : Except DerError DerTlv → Word → BitVec 8
  | .error e => memStore8 (memStore32 M out 0) (out + 4) (derErrByte e)
  | .ok t => memStore32 (memStore32 M out (rp + BitVec.ofNat 32 t.header)) (out + 4) (BitVec.ofNat 32 t.len)

/-- Where `Der::oid` runs: its code and its callees', its 0x20-byte frame
below `sp0`, the result `out`, the reader at `d`, and the reader's unread
bytes, apart from what each must not touch. -/
structure OidEnv (M : Word → BitVec 8) (P sp0 out d : Word) : Prop where
  hP : P.toNat % 2 = 0
  code : CodeIn M P derOidCode
  elem : CodeIn M (P + 0xFFFFF8C8) derElementCode
  tlv : CodeIn M (P + 0xFFFFF8EE) derTlvCode
  hsp : sp0.toNat % 4 = 0
  hS : 0x20 ≤ sp0.toNat
  hout : out.toNat % 4 = 0
  hd : d.toNat % 4 = 0
  sFC : Sep (sp0 + 0xFFFFFFE0) 0x20 P derOidCode.length
  sFE : Sep (sp0 + 0xFFFFFFE0) 0x20 (P + 0xFFFFF8C8) derElementCode.length
  sFT : Sep (sp0 + 0xFFFFFFE0) 0x20 (P + 0xFFFFF8EE) derTlvCode.length
  sOC : Sep out 8 P derOidCode.length
  sDC : Sep (d + 8) 8 P derOidCode.length
  sDT : Sep (d + 8) 8 (P + 0xFFFFF8EE) derTlvCode.length
  sOF : Sep out 8 (sp0 + 0xFFFFFFE0) 0x20
  sDF : Sep (d + 8) 8 (sp0 + 0xFFFFFFE0) 0x20
  sRF : Sep (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat (sp0 + 0xFFFFFFE0) 0x20
  sRD : Sep (memLoad32 M (d + 8)) (memLoad32 M (d + 0xC)).toNat (d + 8) 8
  hrp : 0 < (memLoad32 M (d + 8)).toNat
  hrw : (memLoad32 M (d + 8)).toNat + (memLoad32 M (d + 0xC)).toNat < 2 ^ 32

/-- The registers `Der::oid` may write. -/
def oidKeep (q : Fin 32) : Bool := q.val ∉ [5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17]

abbrev oidPs : List (Fin 32 × Word) := [(ra, 0x1C), ((8 : Fin 32), 0x18)]

/-- From 0x1A to the empty check at 0x20. -/
def oidPre : List BInstr := [.aluImm .add a4 x0 0x1, .alu .add a2 x0 a6, .alu .add a3 x0 a0]

/-- From 0x40 to the final branch at 0x46. -/
def oidFin : List BInstr := [.alu .sltu a1 x0 a6, .alu .and a1 a1 a4]

def oidMov : List BInstr := [.alu .add (8 : Fin 32) x0 a0, .aluImm .add a0 sp 0x4, .aluImm .add a2 x0 0x6]

section
set_option maxRecDepth 20000
theorem oidSave_end : blockEnd derOidCode 2 (saveBlock oidPs) = some 0x6 := by decide
theorem oidMov_end : blockEnd derOidCode 0x6 oidMov = some 0xC := by decide
theorem oidPre_end : blockEnd derOidCode 0x1A oidPre = some 0x20 := by decide
theorem oidFin_end : blockEnd derOidCode 0x40 oidFin = some 0x46 := by decide
theorem oidRestore_end : blockEnd derOidCode 0x60 (restoreBlock oidPs) = some 0x64 := by decide
end

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `Der::oid`**: with the reader at `d`, whose unread bytes
start at `rp` and number `rl`, it stores `derOid` of those bytes at `out`
and moves the reader past the element `Der::element` read. Outside its
frame, nothing else changes. -/
theorem derOid_correct (m : Machine) {P sp0 out d retAddr : Word} (env : OidEnv m.mem P sp0 out d)
    (hpc : m.pc = P) (hsp : reg m sp = sp0) (ha0 : reg m a0 = out) (ha1 : reg m a1 = d)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, oidKeep q = true → reg m' q = reg m q) ∧
      ∀ x, Sep (sp0 + 0xFFFFFFE0) 0x20 x 1 →
        m'.mem x = derOidMem (derAdvance m.mem d (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC))
          (derElement 6 (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)))
          out (memLoad32 m.mem (d + 8))
          (derOid (memBytes m.mem (memLoad32 m.mem (d + 8)) (memLoad32 m.mem (d + 0xC)).toNat)) x := by
  obtain ⟨rp, hrp⟩ : ∃ rp, memLoad32 m.mem (d + 8) = rp := ⟨_, rfl⟩
  obtain ⟨rl, hrl⟩ : ∃ rl, memLoad32 m.mem (d + 0xC) = rl := ⟨_, rfl⟩
  have sRF := env.sRF; have sRD := env.sRD; have hrp0 := env.hrp; have hrw := env.hrw
  rw [hrp, hrl] at sRF sRD hrw ⊢
  rw [hrp] at hrp0
  obtain ⟨F, hF⟩ : ∃ F, sp0 + 0xFFFFFFE0 = F := ⟨_, rfl⟩
  have sFC := env.sFC; have sFE := env.sFE; have sFT := env.sFT; have sOF := env.sOF; have sDF := env.sDF
  rw [hF] at sFC sFE sFT sOF sDF sRF ⊢
  have hFw : F.toNat + 0x20 = sp0.toNat := by
    rw [← hF, BitVec.toNat_add, show (0xFFFFFFE0 : Word).toNat = 4294967264 from rfl]
    have := sp0.isLt; have := env.hS; omega
  have hFa : F.toNat % 4 = 0 := by rw [← hF]; exact aligned_add env.hsp (k := 0xFFFFFFE0) (by decide)
  have cIn : ∀ {M' : Word → BitVec 8} {b : Word} {code : List Nat}, CodeIn m.mem b code →
      Sep F 0x20 b code.length → (∀ x, Sep F 0x20 x 1 → M' x = m.mem x) → CodeIn M' b code :=
    fun hc hs hM i hi => by rw [hM _ (hs.subR (c := i) (l := 1) (by omega))]; exact hc i hi
  have s0 : St m.mem P m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  have hz := s0.zero
  -- the prologue
  obtain ⟨m1, d1, u1⟩ := s0.aluImm env.code oid_at_0 (off' := 2) (by decide)
  have sp1 : upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) sp = F := by
    simp +decide only [upd_app, ↓reduceIte]; rw [ev_add, hsp, hF]
  obtain ⟨m2, c2, u2⟩ := St.block (saveBlock oidPs) u1 env.code oidSave_end (saveBlock_ok _ oidPs _ fun p hp => by
    rw [sp1]
    simp only [oidPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨fr_al' hFa (by decide), frm_sep' sFC (by decide)⟩
    · exact ⟨fr_al' hFa (by decide), frm_sep' sFC (by decide)⟩)
  simp only [saveBlock_run] at u2
  rw [sp1] at u2
  obtain ⟨Msv, hMsv⟩ : ∃ Msv, saveMem m.mem F (upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0)) oidPs = Msv :=
    ⟨_, rfl⟩
  rw [hMsv] at u2
  have frSv : ∀ x, Sep F 0x20 x 1 → Msv x = m.mem x := fun x hx => by
    rw [← hMsv]
    exact saveMem_outside oidPs fun p hp => by
      simp only [oidPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact frm_sep' hx (by decide)
      · exact frm_sep' hx (by decide)
  have hslv : ∀ r o, (r, o) ∈ oidPs → memLoad32 Msv (F + o) = reg m r := fun r o h => by
    rw [← hMsv]
    simp only [oidPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp only [saveMem]
      simp (disch := decide) only [ls_lit, ls_same]
      simp +decide only [upd_app, ↓reduceIte]
  have r2 : ∀ r, reg m2 r = upd (reg m) sp (aluEval .add (reg m sp) 0xFFFFFFE0) r := u2.regs
  obtain ⟨m3, c3, u3⟩ := St.block oidMov u2.self (cIn env.code sFC frSv) oidMov_end
    (by simp [BlockOk, BInstr.ok, oidMov])
  simp only [runBlock, BInstr.run, oidMov] at u3
  have g3 : ∀ r, reg m3 r = _ := u3.regs
  have v3 : reg m3 sp = F ∧ reg m3 8 = out ∧ reg m3 a0 = F + 4 ∧ reg m3 a2 = BitVec.ofNat 32 6 ∧ reg m3 a1 = d := by
    simp +decide only [g3, upd_app, ↓reduceIte, r2]
    simp only [ev_add, hsp, hF, ha0, ha1, zw]
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩
  obtain ⟨v3sp, v38, v3a0, v3a2, v3a1⟩ := v3
  have k3 : ∀ q : Fin 32, q ≠ sp → q ≠ 8 → q ≠ a0 → q ≠ a2 → reg m3 q = reg m q := fun q h1 h2 h3 h4 => by
    rw [g3]
    by_cases h0 : q.val = 0
    · have : q = 0 := Fin.ext h0
      subst this; simp [upd]; exact hz.symm
    simp only [upd_app, h0, h2, h3, h4, ite_false]; rw [r2]; simp only [upd_app, h0, h1, ite_false]
  -- `element`
  have hcS := cIn env.code sFC frSv
  obtain ⟨m4, c4, pc4, mem4, regs4⟩ := u3.self.callRa hcS oid_at_c oid_at_10
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0xFFFFF8C8 (by decide))
  have r4 := PEnv.reg1 regs4 u3.self.zero
  have eT : P + BitVec.ofNat 32 0xFFFFF8C8 + 0x26 = P + 0xFFFFF8EE := by rw [BitVec.add_assoc]; rfl
  have hF4 : F + 4 = F + BitVec.ofNat 32 4 := rfl
  obtain ⟨m5, c5, pc5, mem5, k5⟩ := derElement_correct m4 (tag := 6) (even_at P env.hP 0xFFFFF8C8 (by decide))
    (by rw [mem4]; exact cIn env.elem sFE frSv) (by rw [mem4, eT]; exact cIn env.tlv sFT frSv) pc4
    (by rw [r4 a0 (by decide), v3a0]) (by rw [r4 a1 (by decide), v3a1]) (by rw [r4 a2 (by decide), v3a2]) (by decide)
    (by rw [regs4]; simp +decide [upd]) (even_clear _ (even_at P env.hP (0xC + 8) (by decide)))
    (by rw [hF4]; exact aligned_add hFa (by decide)) env.hd
    (by rw [hF4]; exact sFE.sub (by decide)) (by rw [eT, hF4]; exact sFT.sub (by decide))
    (by rw [eT]; exact env.sDT)
  rw [mem4] at mem5
  have eD8 : memLoad32 Msv (d + 8) = rp := by
    rw [← hrp]; exact memLoad32_congr fun j hj => frSv _ (sDF.symm.subR (c := j) (l := 1) (by omega))
  have eDC : memLoad32 Msv (d + 0xC) = rl := by
    rw [← hrl]; exact memLoad32_congr fun j hj => frSv _ (by
      rw [show d + 0xC = d + 8 + BitVec.ofNat 32 4 by rw [BitVec.add_assoc]; rfl, add_ofNat_assoc]
      exact sDF.symm.subR (by omega))
  have eL : memBytes Msv rp rl.toNat = memBytes m.mem rp rl.toNat :=
    memBytes_congr fun i hi => frSv _ (sRF.symm.subR (c := i) (l := 1) (by omega))
  rw [eD8, eDC, eL] at mem5
  obtain ⟨r, hr⟩ : ∃ r, derElement 6 (memBytes m.mem rp rl.toNat) = r := ⟨_, rfl⟩
  rw [hr] at mem5 ⊢
  -- the epilogue, from 0x60
  have epi : ∀ {Mx : Word → BitVec 8} {n : Machine}, St Mx P n 0x60 (reg n) → CodeIn Mx P derOidCode →
      reg n sp = F → (∀ q o, (q, o) ∈ oidPs → memLoad32 Mx (F + o) = reg m q) →
      ∃ n', Steps n n' ∧ n'.pc = retAddr ∧ n'.mem = Mx ∧ reg n' sp = sp0 ∧ reg n' ra = reg m ra ∧
        reg n' 8 = reg m 8 ∧ ∀ q, q ≠ ra → q ≠ 8 → q ≠ sp → reg n' q = reg n q := by
    intro Mx n s hc rsp hsl
    obtain ⟨n1, c1, u1⟩ := St.block (restoreBlock oidPs) s hc oidRestore_end
      (restoreBlock_ok Mx _ oidPs (reg n) rsp (by decide) fun p hp => by
        simp only [oidPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl <;> exact fr_al' hFa (by decide))
    simp only [restoreBlock_run Mx _ oidPs (reg n) rsp (by decide)] at u1
    obtain ⟨n2, d2, u2⟩ := u1.aluImm hc oid_at_64 (off' := 0x66) (by decide)
    obtain ⟨n3, d3, pc3, mem3, regs3⟩ := u2.jalr hc oid_at_66
    have rsp1 : restoreRegs Mx F (reg n) oidPs sp = F := by rw [restoreRegs_sp _ _ _ _ (by decide)]; exact rsp
    have eS : F + 0x20 = sp0 := by rw [← hF, BitVec.add_assoc]; exact BitVec.add_zero sp0
    refine ⟨n3, c1.trans (.cons d2 (.single d3)), ?_, mem3, ?_, ?_, ?_, fun q h1 h8 hs => ?_⟩
    · rw [pc3]; simp +decide only [upd_app, ↓reduceIte]
      simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]
      rw [hsl ra 0x1C (by decide), hra, add_lit_zero, hret]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]; rw [rsp1, ev_add, eS]
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]
      simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]; exact hsl ra 0x1C (by decide)
    · rw [regs3]; simp +decide only [upd_app, ↓reduceIte]
      simp only [restoreRegs]; simp +decide only [upd_app, ↓reduceIte]; exact hsl 8 0x18 (by decide)
    · rw [regs3]
      by_cases h0 : q.val = 0
      · have : q = 0 := Fin.ext h0
        subst this; simp [upd]; exact s.zero.symm
      simp only [upd_app, h0, hs, ite_false, restoreRegs, h1, h8]
  have u5 : St m5.mem P m5 0x14 (reg m5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  have K5 : ∀ q, tlvClob q = false → q ≠ ra → reg m5 q = reg m3 q := fun q hq hr => by rw [k5 q hq, r4 q hr]
  have sp5 : reg m5 sp = F := by rw [K5 sp (by decide) (by decide), v3sp]
  have s85 : reg m5 8 = out := by rw [K5 8 (by decide) (by decide), v38]
  have fr5' : ∀ x, Sep F 0x20 x 1 → m5.mem x = derAdvance m.mem d rp rl r x := fun x hx => by
    rw [mem5, derTlvMem_outside r (by rw [hF4]; exact hx.sub (by decide)), derAdvance_pt r (frSv x hx)]
  have fr5 : ∀ x, Sep F 0x20 x 1 → Sep (d + 8) 8 x 1 → m5.mem x = m.mem x := fun x hx hd' => by
    rw [fr5' x hx, derAdvance_outside r hd']
  have hc5 : CodeIn m5.mem P derOidCode := fun i hi => by
    rw [fr5 _ (sFC.subR (c := i) (l := 1) (by omega)) (env.sDC.subR (c := i) (l := 1) (by omega))]; exact env.code i hi
  have hsl5 : ∀ q o, (q, o) ∈ oidPs → memLoad32 m5.mem (F + o) = reg m q := fun q o h => by
    have ho : o = 0x1C ∨ o = 0x18 := by
      simp only [oidPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
    rw [← hslv q o h]
    apply memLoad32_congr; intro j hj
    have e : F + o + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (o.toNat + j) := by
      conv => lhs; rw [← ofNat_toNat_self o]
      rw [add_ofNat_assoc]
    have ho' : o.toNat = 0x1C ∨ o.toNat = 0x18 := by rcases ho with rfl | rfl <;> decide
    rw [mem5, e, derTlvMem_outside r (by
        rw [hF4]; exact sep_offsets F (c := 4) (n := 17) (d := o.toNat + j) (k := 1) (.inl (by omega)) (by omega)
          (by omega)),
      derAdvance_outside r (sDF.subR (by omega))]
  -- the two tails
  have errT : ∀ {n : Machine} {b : BitVec 8}, St m5.mem P n 0x58 (reg n) → reg n a0 = b.zeroExtend 32 →
      reg n 8 = out → reg n sp = F →
      ∃ n', Steps n n' ∧ n'.pc = retAddr ∧ n'.mem = memStore8 (memStore32 m5.mem out 0) (out + 4) b ∧
        reg n' sp = sp0 ∧ reg n' ra = reg m ra ∧ reg n' 8 = reg m 8 ∧
        ∀ q, q ≠ ra → q ≠ 8 → q ≠ sp → reg n' q = reg n q := by
    intro n b s ra0 r8 rsp
    obtain ⟨n1, d1, u1⟩ := s.sw hc5 oid_at_58 (off' := 0x5C) (by decide) (by rw [r8, add_lit_zero]; exact env.hout)
    rw [r8, add_lit_zero, s.zero] at u1
    have hc1 := CodeIn.store32 (v := 0) hc5 (env.sOC.sub (c := 0) (l := 4) (by decide) |> fun h => by
      rwa [add_ofNat_zero] at h)
    obtain ⟨n2, d2, u2⟩ := u1.sb hc1 oid_at_5c (off' := 0x60) (by decide)
    rw [r8, ra0, tlv_zext] at u2
    have hc2 := CodeIn.store8 (v := b) hc1 (env.sOC.sub (c := 4) (l := 1) (by decide))
    have hsl2 : ∀ q o, (q, o) ∈ oidPs → memLoad32 (memStore8 (memStore32 m5.mem out 0) (out + 4) b) (F + o) = reg m q :=
      fun q o h => by
        rw [← hsl5 q o h]
        apply memLoad32_congr; intro j hj
        have hfo : Sep out 8 (F + o + BitVec.ofNat 32 j) 1 := by
          have ho : o.toNat + 4 ≤ 0x20 := by
            simp only [oidPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
            rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
          have e : F + o + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (o.toNat + j) := by
            conv => lhs; rw [← ofNat_toNat_self o]
            rw [add_ofNat_assoc]
          rw [e]; exact sOF.subR (c := o.toNat + j) (l := 1) (by omega)
        rw [memStore8_ne fun e => hfo 4 (by decide) 0 (by decide) (by rw [add_ofNat_zero]; exact e.symm),
          memStore32_get_sep (hfo.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)]
    obtain ⟨n3, c3, pc3, mem3, sp3, ra3, s83, k3⟩ := epi u2.self hc2 (by rw [u2.regs, rsp]) hsl2
    exact ⟨n3, .cons d1 (.cons d2 c3), pc3, mem3, sp3, ra3, s83, fun q h1 h8 hs => by
      rw [k3 q h1 h8 hs, u2.regs]⟩
  have okT : ∀ {n : Machine} {cp ln : Word}, St m5.mem P n 0x48 (reg n) → reg n a0 = cp → reg n a6 = ln →
      reg n 8 = out → reg n sp = F →
      ∃ n', Steps n n' ∧ n'.pc = retAddr ∧ n'.mem = memStore32 (memStore32 m5.mem out cp) (out + 4) ln ∧
        reg n' sp = sp0 ∧ reg n' ra = reg m ra ∧ reg n' 8 = reg m 8 ∧
        ∀ q, q ≠ ra → q ≠ 8 → q ≠ sp → reg n' q = reg n q := by
    intro n cp ln s ra0 ra6 r8 rsp
    obtain ⟨n1, d1, u1⟩ := s.sw hc5 oid_at_48 (off' := 0x4A) (by decide) (by rw [r8, add_lit_zero]; exact env.hout)
    rw [r8, add_lit_zero, ra0] at u1
    have hc1 := CodeIn.store32 (v := cp) hc5 (env.sOC.sub (c := 0) (l := 4) (by decide) |> fun h => by
      rwa [add_ofNat_zero] at h)
    obtain ⟨n2, d2, u2⟩ := u1.sw hc1 oid_at_4a (off' := 0x4E) (by decide)
      (by rw [r8]; exact aligned_add env.hout (k := 4) (by decide))
    rw [r8, ra6] at u2
    have hc2 := CodeIn.store32 (v := ln) hc1 (env.sOC.sub (c := 4) (l := 4) (by decide))
    obtain ⟨n3, d3, u3⟩ := u2.jump hc2 oid_at_4e (off' := 0x60) (by decide) (by
      rw [u2.pc, show P + BitVec.ofNat 32 0x4E + 0x12 = P + BitVec.ofNat 32 0x60 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P env.hP 0x60 (by decide)))
    have hsl3 : ∀ q o, (q, o) ∈ oidPs → memLoad32 (memStore32 (memStore32 m5.mem out cp) (out + 4) ln) (F + o) =
        reg m q := fun q o h => by
      rw [← hsl5 q o h]
      apply memLoad32_congr; intro j hj
      have ho : o.toNat + 4 ≤ 0x20 := by
        simp only [oidPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
      have e : F + o + BitVec.ofNat 32 j = F + BitVec.ofNat 32 (o.toNat + j) := by
        conv => lhs; rw [← ofNat_toNat_self o]
        rw [add_ofNat_assoc]
      have hfo : Sep out 8 (F + o + BitVec.ofNat 32 j) 1 := by rw [e]; exact sOF.subR (c := o.toNat + j) (l := 1) (by omega)
      rw [memStore32_get_sep (a := out + 4) (hfo.sub (c := 4) (l := 4) (by decide)),
        memStore32_get_sep (hfo.sub (c := 0) (l := 4) (by decide) |> fun h => by rwa [add_ofNat_zero] at h)]
    obtain ⟨n4, c4, pc4, mem4, sp4, ra4, s84, k4⟩ := epi u3.self hc2 (by rw [u3.regs, rsp]) hsl3
    exact ⟨n4, .cons d1 (.cons d2 (.cons d3 c4)), pc4, mem4, sp4, ra4, s84, fun q h1 h8 hs => by
      rw [k4 q h1 h8 hs, u3.regs]⟩
  have badP : ∀ {n : Machine}, St m5.mem P n 0x50 (reg n) → reg n 8 = out → reg n sp = F →
      ∃ n', Steps n n' ∧ n'.pc = retAddr ∧ n'.mem = memStore8 (memStore32 m5.mem out 0) (out + 4) (derErrByte .badDer) ∧
        reg n' sp = sp0 ∧ reg n' ra = reg m ra ∧ reg n' 8 = reg m 8 ∧
        ∀ q, q ≠ ra → q ≠ 8 → q ≠ sp → q ≠ a0 → reg n' q = reg n q := by
    intro n s r8 rsp
    obtain ⟨n1, d1, u1⟩ := s.aluImm hc5 oid_at_50 (off' := 0x52) (by decide)
    obtain ⟨n2, d2, u2⟩ := u1.jump hc5 oid_at_52 (off' := 0x58) (by decide) (by
      rw [u1.pc, show P + BitVec.ofNat 32 0x52 + 0x6 = P + BitVec.ofNat 32 0x58 by rw [BitVec.add_assoc]; rfl]
      exact even_bit0 (even_at P env.hP 0x58 (by decide)))
    obtain ⟨n3, c3, pc3, mem3, sp3, ra3, s83, k3⟩ := errT (b := 0x14) u2.self
      (by rw [u2.regs]; simp +decide only [upd_app, ↓reduceIte]; rw [s.zero]; rfl)
      (by rw [u2.regs, upd_ne (by decide) (by decide), r8]) (by rw [u2.regs, upd_ne (by decide) (by decide), rsp])
    exact ⟨n3, .cons d1 (.cons d2 c3), pc3, mem3, sp3, ra3, s83, fun q h1 h8 hs h0 => by
      rw [k3 q h1 h8 hs, u2.regs, upd_ne' h0 s.zero]⟩
  -- the result in the caller's terms
  have finish : ∀ {n' : Machine} {Mo : Word → BitVec 8} (res : Except DerError DerTlv), Steps m n' →
      n'.pc = retAddr → n'.mem = Mo → (∀ x, Sep F 0x20 x 1 → Mo x = derOidMem (derAdvance m.mem d rp rl r) out rp res x) →
      reg n' sp = sp0 → reg n' ra = reg m ra → reg n' 8 = reg m 8 →
      (∀ q, oidKeep q = true → q ≠ ra → q ≠ 8 → q ≠ sp → reg n' q = reg m5 q) →
      derOid (memBytes m.mem rp rl.toNat) = res →
      ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, oidKeep q = true → reg m' q = reg m q) ∧
        ∀ x, Sep F 0x20 x 1 → m'.mem x = derOidMem (derAdvance m.mem d rp rl r) out rp
          (derOid (memBytes m.mem rp rl.toNat)) x := by
    intro n' Mo res st pc' mem' hmo sp' ra' s8' kq hres
    refine ⟨n', st, pc', sp', fun q hq => ?_, fun x hx => by rw [mem', hres]; exact hmo x hx⟩
    by_cases hr' : q = ra
    · subst hr'; exact ra'
    by_cases h8 : q = 8
    · subst h8; exact s8'
    by_cases hs : q = sp
    · subst hs; rw [sp', hsp]
    have hkc : ∀ q : Fin 32, oidKeep q = true → tlvClob q = false := by decide
    have hc := hkc q hq
    have h0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
    have h2 : q ≠ a2 := fun e => by subst e; exact absurd hq (by decide)
    rw [kq q hq hr' h8 hs, K5 q hc hr', k3 q hs h8 h0 h2]
  have hF8 : F + 8 = F + 4 + 4 := by rw [BitVec.add_assoc]; rfl
  have hspa : (reg m5 sp + 4).toNat % 4 = 0 := by rw [sp5]; exact aligned_add hFa (k := 4) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5.lw hc5 oid_at_14 (off' := 0x16) (by decide) hspa
  rw [sp5] at u6
  have k6 : ∀ q, q ≠ a0 → reg n6 q = reg m5 q := fun q h => by rw [u6.regs, upd_ne' h u5.zero]
  cases r with
  | error e =>
    have h0 : memLoad32 m5.mem (F + 4) = 0 := by rw [mem5]; exact derTlvMem_err0 e
    obtain ⟨n7, d7, u7⟩ := u6.taken hc5 0x54 oid_at_16 (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [h0]; rfl)
    obtain ⟨n8, d8, u8⟩ := u7.lbu hc5 oid_at_54 (off' := 0x58) (by decide)
    have eb : m5.mem (upd (reg m5) a0 (memLoad32 m5.mem (F + 4)) sp + 8) = derErrByte e := by
      rw [upd_ne (by decide) (by decide), sp5, hF8, mem5]; exact derTlvMem_err4 e
    rw [eb] at u8
    obtain ⟨n9, c9, pc9, mem9, sp9, ra9, s89, k9⟩ := errT (b := derErrByte e) u8.self
      (by rw [u8.regs]; simp +decide only [upd_app, ↓reduceIte])
      (by rw [u8.regs, upd_ne (by decide) (by decide), upd_ne (by decide) (by decide), s85])
      (by rw [u8.regs, upd_ne (by decide) (by decide), upd_ne (by decide) (by decide), sp5])
    refine finish (.error e) (.cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (.cons d6 (.cons d7 (.cons d8 c9))))))))
      pc9 mem9 (fun x hx => ?_) sp9 ra9 s89 (fun q hq h1 h8 hs => ?_) (by simp only [derOid, hr])
    · simp only [derOidMem]
      exact memStore8_pt (memStore32_pt (fr5' x hx))
    · have h0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
      rw [k9 q h1 h8 hs, u8.regs, upd_ne' h0 u7.zero, upd_ne' h0 u5.zero]
  | ok t =>
    have hb : t.header + t.len ≤ rl.toNat := by
      have := derElement_bound hr; rwa [memBytes_length] at this
    have h0 : memLoad32 m5.mem (F + 4) = rp + BitVec.ofNat 32 t.header := by rw [mem5]; exact derTlvMem_ok0 t
    have hcp : (rp + BitVec.ofNat 32 t.header).toNat = rp.toNat + t.header := by
      rw [BitVec.toNat_add, ofNat_tn (by omega)]; exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨n7, d7, u7⟩ := u6.notTaken hc5 0x18 oid_at_16 (by decide) (by
      simp only [upd_app]; simp +decide only [↓reduceIte]; rw [h0]
      show (rp + BitVec.ofNat 32 t.header == 0) = false
      exact beq_false_of_ne fun h => by have := congrArg BitVec.toNat h; rw [hcp] at this; change _ = 0 at this; omega)
    obtain ⟨n8, d8, u8⟩ := u7.lw hc5 oid_at_18 (off' := 0x1A) (by decide)
      (by rw [upd_ne (by decide) (by decide), sp5]; exact aligned_add hFa (k := 8) (by decide))
    have elen : memLoad32 m5.mem (upd (reg m5) a0 (memLoad32 m5.mem (F + 4)) sp + 8) = BitVec.ofNat 32 t.len := by
      rw [upd_ne (by decide) (by decide), sp5, hF8, mem5]; exact derTlvMem_ok4 t
    rw [elen, h0] at u8
    obtain ⟨n9, c9, u9⟩ := St.block oidPre u8 hc5 oidPre_end (by simp [BlockOk, BInstr.ok, oidPre])
    simp only [runBlock, BInstr.run, oidPre] at u9
    have g9 : ∀ q, reg n9 q = _ := u9.regs
    have hlen32 : t.len < 2 ^ 32 := by omega
    have v9 : reg n9 a4 = 1 ∧ reg n9 a2 = BitVec.ofNat 32 t.len ∧ reg n9 a3 = rp + BitVec.ofNat 32 t.header ∧
        reg n9 a6 = BitVec.ofNat 32 t.len ∧ reg n9 a0 = rp + BitVec.ofNat 32 t.header ∧ reg n9 8 = out ∧
        reg n9 sp = F := by
      simp +decide only [g9, upd_app, ↓reduceIte]
      rw [s85, sp5]
      exact ⟨trivial, zw _, zw _, trivial, trivial, rfl, rfl⟩
    obtain ⟨v9a4, v9a2, v9a3, v9a6, v9a0, v98, v9sp⟩ := v9
    have k9 : ∀ q, q ≠ a0 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a6 → reg n9 q = reg m5 q := fun q h0 h2 h3 h4 h6 => by
      rw [g9]
      by_cases hq0 : q.val = 0
      · have : q = 0 := Fin.ext hq0
        subst this; simp [upd]; exact u5.zero.symm
      simp only [upd_app, hq0, h0, h2, h3, h4, h6, ite_false]
    have hcont : t.content (memBytes m.mem rp rl.toNat) = memBytes m5.mem (rp + BitVec.ofNat 32 t.header) t.len := by
      rw [DerTlv.content, memBytes_drop_take hb]
      apply memBytes_congr; intro i hi
      rw [add_ofNat_assoc]
      exact (fr5 _ (sRF.symm.subR (c := t.header + i) (l := 1) (by omega))
        (sRD.symm.subR (c := t.header + i) (l := 1) (by omega))).symm
    have hres : derOid (memBytes m.mem rp rl.toNat) =
        if derOidOk (memBytes m5.mem (rp + BitVec.ofNat 32 t.header) t.len) then .ok t else .error .badDer := by
      simp only [derOid, hr, hcont]
    have z9 : reg n9 x0 = 0 := u9.self.zero
    -- 0x40: the final check, with the state in `a4`
    have at40 : ∀ {n : Machine} {a : Bool}, Steps m n → St m5.mem P n 0x40 (reg n) → reg n a6 = BitVec.ofNat 32 t.len →
        reg n a4 = (if a then 1 else 0) → reg n a0 = rp + BitVec.ofNat 32 t.header → reg n 8 = out → reg n sp = F →
        (∀ q, oidKeep q = true → q ≠ ra → q ≠ 8 → q ≠ sp → reg n q = reg m5 q) →
        derOid (memBytes m.mem rp rl.toNat) = (if (t.len != 0 && a) then .ok t else .error .badDer) →
        ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧ (∀ q, oidKeep q = true → reg m' q = reg m q) ∧
          ∀ x, Sep F 0x20 x 1 → m'.mem x = derOidMem (derAdvance m.mem d rp rl (.ok t)) out rp
            (derOid (memBytes m.mem rp rl.toNat)) x := by
      intro n a st s ra6 ra4 ra0 r8 rsp kn hspec
      obtain ⟨n1, c1, u1⟩ := St.block oidFin s hc5 oidFin_end (by simp [BlockOk, BInstr.ok, oidFin])
      simp only [runBlock, BInstr.run, oidFin] at u1
      have g1 : ∀ q, reg n1 q = _ := u1.regs
      have a11 : reg n1 a1 = if (t.len != 0 && a) then 1 else 0 := by
        rw [g1]; simp +decide only [upd_app, ↓reduceIte]
        rw [ra6, ra4, s.zero]
        have hs : aluEval .sltu 0 (BitVec.ofNat 32 t.len) = if t.len ≠ 0 then 1 else 0 := by
          by_cases h : t.len = 0
          · rw [h]; rfl
          · rw [ite_eq_left h]
            show (if (0 : Word).ult (BitVec.ofNat 32 t.len) then (1 : Word) else 0) = 1
            exact ite_eq_left (by
              show decide ((0 : Word).toNat < (BitVec.ofNat 32 t.len).toNat) = true
              rw [ofNat_tn hlen32]; exact decide_eq_true (by change 0 < t.len; omega))
        have hbne : (t.len != 0) = decide (t.len ≠ 0) := Bool.eq_iff_iff.mpr
          ⟨fun h => decide_eq_true (bne_iff_ne.mp h), fun h => bne_iff_ne.mpr (of_decide_eq_true h)⟩
        rw [hs, oid_and, Bool.and_comm, hbne]
      have k1 : ∀ q, q ≠ a1 → reg n1 q = reg n q := fun q h => by
        rw [g1]
        by_cases hq0 : q.val = 0
        · have : q = 0 := Fin.ext hq0
          subst this; simp [upd]; exact s.zero.symm
        simp only [upd_app, hq0, h, ite_false]
      by_cases hok : (t.len != 0 && a) = true
      · obtain ⟨n2, d2, u2⟩ := u1.self.notTaken hc5 0x48 oid_at_46 (by decide) (by
          rw [a11, u1.self.zero, ite_eq_left hok]; rfl)
        obtain ⟨n3, c3, pc3, mem3, sp3, ra3, s83, k3⟩ := okT u2.self (by rw [u2.regs, k1 a0 (by decide), ra0])
          (by rw [u2.regs, k1 a6 (by decide), ra6]) (by rw [u2.regs, k1 8 (by decide), r8])
          (by rw [u2.regs, k1 sp (by decide), rsp])
        refine finish (.ok t) (st.trans (c1.trans (.cons d2 c3))) pc3 mem3 (fun x hx => ?_) sp3 ra3 s83
          (fun q hq h1 h8 hs => ?_) (by rw [hspec, ite_eq_left hok])
        · simp only [derOidMem]; exact memStore32_pt (memStore32_pt (fr5' x hx))
        · have hq1 : q ≠ a1 := fun e => by subst e; exact absurd hq (by decide)
          rw [k3 q h1 h8 hs, u2.regs, k1 q hq1, kn q hq h1 h8 hs]
      · have hok' : (t.len != 0 && a) = false := by
          revert hok; cases (t.len != 0 && a) <;> intro h
          · rfl
          · exact absurd rfl h
        obtain ⟨n2, d2, u2⟩ := u1.self.taken hc5 0x50 oid_at_46 (by decide) (by
          rw [a11, u1.self.zero, hok']; rfl)
        obtain ⟨n3, c3, pc3, mem3, sp3, ra3, s83, k3⟩ := badP u2.self (by rw [u2.regs, k1 8 (by decide), r8])
          (by rw [u2.regs, k1 sp (by decide), rsp])
        refine finish (.error .badDer) (st.trans (c1.trans (.cons d2 c3))) pc3 mem3 (fun x hx => ?_) sp3 ra3 s83
          (fun q hq h1 h8 hs => ?_) (by rw [hspec, hok']; rfl)
        · simp only [derOidMem]; exact memStore8_pt (memStore32_pt (fr5' x hx))
        · have hq1 : q ≠ a1 := fun e => by subst e; exact absurd hq (by decide)
          have hq0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
          rw [k3 q h1 h8 hs hq0, u2.regs, k1 q hq1, kn q hq h1 h8 hs]
    have S9 : Steps m n9 := .cons d1 (c2.trans (c3.trans (c4.trans (c5.trans (.cons d6 (.cons d7 (.cons d8 c9)))))))
    have kn9 : ∀ q, oidKeep q = true → q ≠ ra → q ≠ 8 → q ≠ sp → reg n9 q = reg m5 q := fun q hq _ _ _ =>
      k9 q (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide))
        (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide))
        (fun e => by subst e; exact absurd hq (by decide))
    by_cases hl0 : t.len = 0
    · obtain ⟨n10, d10, u10⟩ := u9.self.taken hc5 0x40 oid_at_20 (by decide) (by rw [v9a6, z9, hl0]; rfl)
      refine at40 (a := true) (S9.trans (.single d10)) u10.self (by rw [u10.regs, v9a6]) (by rw [u10.regs, v9a4]; rfl)
        (by rw [u10.regs, v9a0]) (by rw [u10.regs, v98]) (by rw [u10.regs, v9sp])
        (fun q hq h1 h8 hs => by rw [u10.regs, kn9 q hq h1 h8 hs]) ?_
      rw [hres, hl0]; rfl
    obtain ⟨n10, d10, u10⟩ := u9.self.notTaken hc5 0x24 oid_at_20 (by decide) (by
      rw [v9a6, z9]; show (BitVec.ofNat 32 t.len == 0) = false
      exact beq_false_of_ne fun h => by have := congrArg BitVec.toNat h; rw [ofNat_tn hlen32] at this; exact hl0 this)
    obtain ⟨n11, c11, h11, k11⟩ := oid_loop hc5 t.len (atStart := true) (by omega) hlen32 u10.self
      (by rw [u10.regs, v9a2]) (by rw [u10.regs, v9a3]) (by rw [u10.regs, v9a4]; rfl)
    have kn11 : ∀ q, oidKeep q = true → q ≠ ra → q ≠ 8 → q ≠ sp → reg n11 q = reg m5 q := fun q hq h1 h8 hs => by
      rw [k11 q (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide))
        (fun e => by subst e; exact absurd hq (by decide)) (fun e => by subst e; exact absurd hq (by decide))
        (fun e => by subst e; exact absurd hq (by decide)), u10.regs, kn9 q hq h1 h8 hs]
    have keep11 : ∀ q, q ≠ a1 → q ≠ a2 → q ≠ a3 → q ≠ a4 → q ≠ a5 → reg n11 q = reg n9 q := fun q h1 h2 h3 h4 h5 => by
      rw [k11 q h1 h2 h3 h4 h5, u10.regs]
    have hok : derOidOk (memBytes m5.mem (rp + BitVec.ofNat 32 t.header) t.len) =
        (match oidScan true (memBytes m5.mem (rp + BitVec.ofNat 32 t.header) t.len) with
          | none => false | some a => a) := by
      rw [derOidOk, oidScan_go]
      have : (memBytes m5.mem (rp + BitVec.ofNat 32 t.header) t.len).isEmpty = false := by
        rw [List.isEmpty_eq_false_iff_exists_mem]
        obtain ⟨j, hj⟩ : ∃ j, t.len = j + 1 := ⟨t.len - 1, by omega⟩
        rw [hj, memBytes_succ]; exact ⟨_, List.mem_cons_self⟩
      rw [this]; rfl
    revert h11
    cases hs : oidScan true (memBytes m5.mem (rp + BitVec.ofNat 32 t.header) t.len) with
    | none =>
      intro h11
      obtain ⟨n12, c12, pc12, mem12, sp12, ra12, s812, k12⟩ := badP h11
        (by rw [keep11 8 (by decide) (by decide) (by decide) (by decide) (by decide), v98])
        (by rw [keep11 sp (by decide) (by decide) (by decide) (by decide) (by decide), v9sp])
      refine finish (.error .badDer) (S9.trans (.cons d10 (c11.trans c12))) pc12 mem12 (fun x hx => ?_) sp12 ra12
        s812 (fun q hq h1 h8 hs => ?_) (by rw [hres, hok, hs]; rfl)
      · simp only [derOidMem]; exact memStore8_pt (memStore32_pt (fr5' x hx))
      · have hq0 : q ≠ a0 := fun e => by subst e; exact absurd hq (by decide)
        rw [k12 q h1 h8 hs hq0, kn11 q hq h1 h8 hs]
    | some a =>
      intro ⟨h11, ha4⟩
      refine at40 (a := a) (S9.trans (.cons d10 c11)) h11
        (by rw [keep11 a6 (by decide) (by decide) (by decide) (by decide) (by decide), v9a6]) ha4
        (by rw [keep11 a0 (by decide) (by decide) (by decide) (by decide) (by decide), v9a0])
        (by rw [keep11 8 (by decide) (by decide) (by decide) (by decide) (by decide), v98])
        (by rw [keep11 sp (by decide) (by decide) (by decide) (by decide) (by decide), v9sp]) kn11 ?_
      rw [hres, hok, hs]
      have : (t.len != 0) = true := bne_iff_ne.mpr hl0
      rw [this, Bool.true_and]

end C3.RV32
