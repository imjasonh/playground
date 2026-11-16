import C3BootProofs.Proofs.EdDecompressAt

/-!
# `CompressedEdwardsY::decompress`, as compiled

`decompress` builds `Y` from the 32 bytes with `FieldElement::from_bytes`
(inlined: ten `load3_at`/`load4_at` calls and a `reduce`), computes
`u = Y² - 1` and `v = d Y² + 1`, takes `sqrt_ratio_i(u, v)` (inlined: a
chain of `square`, `mul`, `pow22501`, `pow2k`, `ct_eq`, `neg`,
`conditional_assign`, `is_negative`, and `conditional_negate`), and, when
`u / v` is a square, negates the root by the encoding's sign bit and writes
`Some((X, Y, 1, X Y))`. `decSpec` in `DecCall.lean` states the result on
limb lists.
-/

namespace C3.RV32

open C3.Image

theorem ofNat_add2 (o : Nat) : BitVec.ofNat 32 o + 2 = BitVec.ofNat 32 (o + 2) := BitVec.ofNat_add_ofNat ..

theorem sll_toNat (a b : Word) : (aluEval .sll a b).toNat = a.toNat * 2 ^ (b.toNat % 32) % 2 ^ 32 := by
  show (a <<< (b.toNat % 32)).toNat = _
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem srl_toNat (a b : Word) : (aluEval .srl a b).toNat = a.toNat / 2 ^ (b.toNat % 32) := by
  show (a >>> (b.toNat % 32)).toNat = _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The byte at `p + i`, as a number. -/
abbrev byteN (M : Word → BitVec 8) (p : Word) (i : Nat) : Nat := (M (p + BitVec.ofNat 32 i)).toNat

theorem add_off (R : Word) {a b c : Nat} (h : a + b = c) :
    R + BitVec.ofNat 32 a + BitVec.ofNat 32 b = R + BitVec.ofNat 32 c := by
  subst h; exact add_ofNat_assoc ..

theorem add_sp (R : Word) {a b c : Nat} (h : a + b = c) :
    aluEval .add (R + BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = R + BitVec.ofNat 32 c := by
  subst h; exact add_ofNat_assoc ..

theorem ld_st_eq {M : Word → BitVec 8} {b v : Word} {c d : Nat} (h : c = d) :
    memLoad32 (memStore32 M (b + BitVec.ofNat 32 c) v) (b + BitVec.ofNat 32 d) = v := by
  subst h; exact memLoad32_store32_same _ _ _

theorem ld_st_ne {M : Word → BitVec 8} {b v : Word} {c d : Nat} (h : c + 4 ≤ d ∨ d + 4 ≤ c)
    (hc : c + 4 ≤ 2 ^ 32) (hd : d + 4 ≤ 2 ^ 32) :
    memLoad32 (memStore32 M (b + BitVec.ofNat 32 c) v) (b + BitVec.ofNat 32 d) = memLoad32 M (b + BitVec.ofNat 32 d) :=
  memLoad32_store32_sep (sep_offsets b h hc hd)

theorem getD_memBytes (M : Word → BitVec 8) (p : Word) {n j : Nat} (h : j < n) :
    (memBytes M p n).getD j 0 = byteN M p j := by
  unfold memBytes; rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]; rfl

/-- The bytes `from_bytes` reads are the entry memory's. -/
theorem DecSt.bytes {M0 Ms M : Word → BitVec 8} {R : Word} {r0 : Fin 32 → Word} {nm : Machine} {off : Nat}
    (D : DecSt M0 Ms R r0 M nm off) {bp : Word} (sB : Sep bp 32 R 0x6F0) :
    ∀ j, j < 32 → M (bp + BitVec.ofNat 32 j) = M0 (bp + BitVec.ofNat 32 j) := fun j hj =>
  D.agree _ (sB.sub (c := j) (l := 1) (by omega)).symm

/-- `v³` and `v⁷`, as `sqrt_ratio_i` computes them. -/
def sqrtV3 (v : List Nat) : List Nat := mulL (sqL v) v
def sqrtV7 (v : List Nat) : List Nat := mulL (sqL (sqrtV3 v)) v

/-! ## Choices, operands, and values carried across calls -/

/-- A `Choice` as `subtle` keeps it in a register: 1 or 0. -/
def bw (b : Bool) : Word := if b then 1 else 0

theorem bw_ct (A B : List Nat) : (if bytesL A = bytesL B then (1 : Word) else 0) = bw (feEqL A B) := by
  unfold bw feEqL; by_cases h : bytesL A = bytesL B <;> simp [h]

theorem bw_or (a b : Bool) : aluEval .or (bw a) (bw b) = bw (a || b) := by
  cases a <;> cases b <;> decide

theorem bw_zext (a : Bool) : aluEval .and (bw a) 0xFF = bw a := by cases a <;> decide

theorem bw_bb (a : Bool) : ((bw a).extractLsb' 0 8).zeroExtend 32 = bw a := by cases a <;> decide

theorem bw_01 (a : Bool) : bw a = 0 ∨ bw a = 1 := by cases a <;> decide

theorem bw_ite {α : Type} (a : Bool) (x y : α) : (if bw a = 1 then x else y) = if a then x else y := by
  cases a <;> rfl

theorem bw_beq (a : Bool) : (bw a == 1) = a := by cases a <;> decide

theorem bw_isNeg (X : List Nat) : BitVec.ofNat 32 ((bytesL X).getD 0 0 % 2) = bw (isNegL X) := by
  unfold bw isNegL
  have h := Nat.mod_two_eq_zero_or_one ((bytesL X).getD 0 0)
  rcases h with h | h <;> rw [h] <;> rfl

section Carry

variable {M0 Ms M M' : Word → BitVec 8} {R : Word} {r0 : Fin 32 → Word} {nm : Machine} {off : Nat}

theorem DecCtx.opF (C : DecCtx M0 R) {j : Nat} (hj : j % 4 = 0) (hj1 : 0x450 ≤ j) (hj2 : j + 40 ≤ 0x6F0) :
    OpOK R (R + BitVec.ofNat 32 j) := ⟨aligned_add C.hR hj, (C.offs0 hj1 hj2).symm⟩

theorem DecCtx.opC (_ : DecCtx M0 R) {c : Word} (hc : Sep c 40 R 0x6F0) (h4 : c.toNat % 4 = 0) : OpOK R c :=
  ⟨h4, by have := hc.subR (c := 0) (l := 0x450) (by decide); rwa [add_ofNat_zero] at this⟩

theorem DecCtx.wideF (C : DecCtx M0 R) {j : Nat} (hj : j + 40 ≤ 0x6F0) : (R + BitVec.ofNat 32 j).toNat + 40 < 2 ^ 32 := by
  rw [C.toNat_off (by omega)]; have := C.hRw; omega

theorem DecSt.constW (D : DecSt M0 Ms R r0 M nm off) {c : Word} (hc : Sep c 40 R 0x6F0) : feW M c = feW M0 c :=
  feW_frame fun i hi => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]; exact D.agree _ (hc.sub (c := 4 * i + j) (l := 1) (by omega)).symm

/-- A field element in the frame that a call leaves alone. -/
theorem keepW (C : DecCtx M0 R) {k n j : Nat}
    (fr : ∀ z, Sep (R + BitVec.ofNat 32 k) n z 1 → Sep R 0x450 z 1 → M' z = M z)
    (hd : k + n ≤ j ∨ j + 40 ≤ k) (hk : k + n ≤ 0x6F0) (hj1 : 0x450 ≤ j) (hj2 : j + 40 ≤ 0x6F0) :
    feW M' (R + BitVec.ofNat 32 j) = feW M (R + BitVec.ofNat 32 j) :=
  feW_frame2 fr (C.offs hd hk hj2) (C.offs0 hj1 hj2)

theorem keepW0 (C : DecCtx M0 R) {j : Nat} (fr : ∀ z, Sep R 0x450 z 1 → M' z = M z) (hj1 : 0x450 ≤ j)
    (hj2 : j + 40 ≤ 0x6F0) : feW M' (R + BitVec.ofNat 32 j) = feW M (R + BitVec.ofNat 32 j) :=
  feW_frame fun i hi => memLoad32_congr fun q hq => by
    rw [add_ofNat_assoc, add_ofNat_assoc]
    exact fr _ (C.offs0 (by omega) (by omega))

end Carry

set_option maxRecDepth 20000 in
/-- A `memcpy` of the field element at `R + j` to `R + k`. -/
theorem DecSt.memcpyF (C : DecCtx M0 R) {off : Nat} (D : DecSt M0 Ms R r0 M nm off) {imm o : Word}
    (h1 : fetchRel edDecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel edDecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DEC + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 memcpyStubAddress) (hev : off % 2 = 0)
    {k j : Nat} (hk1 : 0x450 ≤ k) (hk2 : k + 40 ≤ 0x6D4) (hj1 : 0x450 ≤ j) (hj2 : j + 40 ≤ 0x6F0)
    (hkj : k + 40 ≤ j ∨ j + 40 ≤ k)
    (ha0 : reg nm a0 = R + BitVec.ofNat 32 k) (ha1 : reg nm a1 = R + BitVec.ofNat 32 j)
    (ha2 : reg nm a2 = BitVec.ofNat 32 40) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' (off + 8) ∧
      feW nm'.mem (R + BitVec.ofNat 32 k) = feW M (R + BitVec.ofNat 32 j) ∧
      (∀ q, q.val ∈ [8, 9, 18, 19, 20, 21] → reg nm' q = reg nm q) ∧
      ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → nm'.mem z = M z := by
  obtain ⟨n1, c1, D1, cp, k1, f1⟩ := D.memcpy C h1 h2 hb hev hk1 hk2 ha0 ha1 ha2 (C.offs0 hj1 hj2).symm
    (C.wideF hj2) (C.offs hkj (by omega) hj2)
  refine ⟨n1, c1, D1, ?_, k1, f1⟩
  rw [← feW_copy (M := M) (dst := R + BitVec.ofNat 32 k)]
  exact feW_frame fun i hi => memLoad32_congr fun q hq => by
    rw [add_ofNat_assoc, add_ofNat_assoc]; exact cp _ (C.offs0 (by omega) (by omega))

set_option maxRecDepth 20000 in
/-- A `memcpy` of the field element at `c`, outside the stack, to `R + k`. -/
theorem DecSt.memcpyC (C : DecCtx M0 R) {off : Nat} (D : DecSt M0 Ms R r0 M nm off) {imm o : Word}
    (h1 : fetchRel edDecompressCode off = some (.auipc ra imm, 4))
    (h2 : fetchRel edDecompressCode (off + 4) = some (.jalr ra ra o, 4))
    (hb : DEC + BitVec.ofNat 32 off + imm + o = BitVec.ofNat 32 memcpyStubAddress) (hev : off % 2 = 0)
    {k : Nat} {c : Word} (hk1 : 0x450 ≤ k) (hk2 : k + 40 ≤ 0x6D4) (hc : Sep c 40 R 0x6F0)
    (hcw : c.toNat + 40 < 2 ^ 32)
    (ha0 : reg nm a0 = R + BitVec.ofNat 32 k) (ha1 : reg nm a1 = c) (ha2 : reg nm a2 = BitVec.ofNat 32 40) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' (off + 8) ∧
      feW nm'.mem (R + BitVec.ofNat 32 k) = feW M c ∧
      (∀ q, q.val ∈ [8, 9, 18, 19, 20, 21] → reg nm' q = reg nm q) ∧
      ∀ z, Sep (R + BitVec.ofNat 32 k) 40 z 1 → Sep R 0x450 z 1 → nm'.mem z = M z := by
  obtain ⟨n1, c1, D1, cp, k1, f1⟩ := D.memcpy C h1 h2 hb hev hk1 hk2 ha0 ha1 ha2
    (by have := hc.subR (c := 0) (l := 0x450) (by decide); rwa [add_ofNat_zero] at this) hcw
    (hc.subR (c := k) (l := 40) (by omega)).symm
  refine ⟨n1, c1, D1, ?_, k1, f1⟩
  rw [← feW_copy (M := M) (dst := R + BitVec.ofNat 32 k)]
  exact feW_frame fun i hi => memLoad32_congr fun q hq => by
    rw [add_ofNat_assoc, add_ofNat_assoc]; exact cp _ (C.offs0 (by omega) (by omega))

/-! ## Prologue and epilogue -/

/-- The registers the prologue saves, at their offsets from `sp + 0x280`. -/
abbrev decPs : List (Fin 32 × Word) :=
  [(ra, BitVec.ofNat 32 0x1C), ((8 : Fin 32), BitVec.ofNat 32 0x18), ((9 : Fin 32), BitVec.ofNat 32 0x14),
   ((18 : Fin 32), BitVec.ofNat 32 0x10), ((19 : Fin 32), BitVec.ofNat 32 0xC), ((20 : Fin 32), BitVec.ofNat 32 8),
   ((21 : Fin 32), BitVec.ofNat 32 4)]

section
set_option maxRecDepth 20000
theorem decSave_end : blockEnd edDecompressCode 0x6 (saveBlockR a2 decPs) = some 0x1E := by decide
theorem decRestore_end : blockEnd edDecompressCode 0x33A (restoreBlockR a0 decPs) = some 0x352 := by decide
end

theorem restoreRegs_other (M : Word → BitVec 8) (G : Word) :
    ∀ (ps : List (Fin 32 × Word)) (f : Fin 32 → Word) (q : Fin 32), q.val ≠ 0 → (∀ p ∈ ps, p.1 ≠ q) →
      restoreRegs M G f ps q = f q
  | [], _, _, _, _ => rfl
  | p :: ps, f, q, hq, h => by
    simp only [restoreRegs]
    rw [restoreRegs_other M G ps _ q hq (fun p' hp' => h p' (List.mem_cons_of_mem _ hp')),
      upd_ne hq (fun e => h p List.mem_cons_self e.symm)]

theorem decPs_restore (M : Word → BitVec 8) (G : Word) (f : Fin 32 → Word) :
    ∀ r o, (r, o) ∈ decPs → restoreRegs M G f decPs r = memLoad32 M (G + o) := by
  intro r o hm
  simp only [decPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp +decide only [restoreRegs, upd, ↓reduceIte]

set_option maxRecDepth 20000 in
/-- From offset 0x334: the store of the `Option` tag `v` at `out`, the
epilogue, and the return. -/
theorem dec_tail {Mx : Word → BitVec 8} {nm : Machine} {R out v : Word} {rM : Fin 32 → Word}
    (hc : CodeIn Mx DEC edDecompressCode) (s : St Mx DEC nm 0x334 (reg nm))
    (hsp : reg nm sp = R + BitVec.ofNat 32 0x450) (hs2 : reg nm (18 : Fin 32) = out) (ha0 : reg nm a0 = v)
    (hout : out.toNat % 4 = 0) (hR : R.toNat % 4 = 0) (sOC : Sep out 4 DEC edDecompressCode.length)
    (hsl : ∀ r o, (r, o) ∈ decPs → memLoad32 (memStore32 Mx out v) (R + BitVec.ofNat 32 0x6D0 + o) = rM r)
    (hret : rM ra &&& ~~~1 = rM ra) :
    ∃ m', Steps nm m' ∧ m'.pc = rM ra ∧ reg m' sp = R + BitVec.ofNat 32 0x6F0 ∧
      (∀ r o, (r, o) ∈ decPs → reg m' r = rM r) ∧
      (∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg m' q = reg nm q) ∧ m'.mem = memStore32 Mx out v := by
  obtain ⟨n1, d1, u1⟩ := s.sw hc dec_at_334 (off' := 0x338) (by decide) (by rw [hs2, add_lit_zero]; exact hout)
  rw [hs2, add_lit_zero, ha0] at u1
  have hc' : CodeIn (memStore32 Mx out v) DEC edDecompressCode := hc.store32 sOC
  obtain ⟨n2, d2, u2⟩ := u1.aluImm hc' dec_at_338 (off' := 0x33A) (by decide)
  have a0_2 : upd (reg nm) a0 (aluEval .add (reg nm sp) 0x280) a0 = R + BitVec.ofNat 32 0x6D0 := by
    simp only [upd_app, ↓reduceIte]; rw [hsp]; exact add_sp R rfl
  have hal : ∀ p ∈ decPs, (R + BitVec.ofNat 32 0x6D0 + p.2).toNat % 4 = 0 := by
    intro p hp
    simp only [decPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (rw [add_ofNat_assoc]; exact aligned_add hR (by decide))
  obtain ⟨n3, c3, u3⟩ := St.block (restoreBlockR a0 decPs) u2 hc' decRestore_end
    (restoreBlockR_ok _ (R + BitVec.ofNat 32 0x6D0) a0 (by decide) decPs _ a0_2 (by decide) hal)
  rw [restoreBlockR_run _ (R + BitVec.ofNat 32 0x6D0) a0 (by decide) decPs _ a0_2 (by decide)] at u3
  dsimp only at u3
  obtain ⟨n4, d4, u4⟩ := u3.aluImm hc' dec_at_352 (off' := 0x356) (by decide)
  obtain ⟨n5, d5, pc5, mem5, regs5⟩ := u4.jalr hc' dec_at_356
  have oth : ∀ q : Fin 32, q.val ∉ [0, 1, 2, 8, 9, 10, 18, 19, 20, 21] →
      reg n5 q = reg nm q := fun q hq => by
    have h0 : q.val ≠ 0 := fun h => hq (by simp [h])
    have hps : ∀ p ∈ decPs, p.1 ≠ q := by
      intro p hp e; apply hq
      simp only [decPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (rw [← e]; decide)
    have hsq : q ≠ sp := fun e => hq (by rw [e]; decide)
    have ha0q : q ≠ a0 := fun e => hq (by rw [e]; decide)
    rw [regs5, upd_ne h0 hsq, restoreRegs_other _ _ decPs _ q h0 hps, upd_ne h0 ha0q]
  have spR : restoreRegs (memStore32 Mx out v) (R + BitVec.ofNat 32 0x6D0)
      (upd (reg nm) a0 (aluEval .add (reg nm sp) 0x280)) decPs sp = R + BitVec.ofNat 32 0x450 := by
    rw [restoreRegs_other _ _ decPs _ sp (by decide) (by decide), upd_ne (by decide) (by decide), hsp]
  refine ⟨n5, .cons d1 (.cons d2 (c3.trans (.cons d4 (.single d5)))), ?_, ?_, fun r o hm => ?_,
    fun q hq => oth q (by revert hq; revert q; decide), by rw [mem5]⟩
  · rw [pc5, upd_ne (by decide) (by decide), decPs_restore _ _ _ ra (BitVec.ofNat 32 0x1C) (by decide),
      hsl ra _ (by decide), add_lit_zero, hret]
  · rw [regs5]; simp only [upd_app, ↓reduceIte]; rw [spR]; exact add_sp R rfl
  · have hr : r ≠ sp := by
      simp only [decPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    have h0 : r.val ≠ 0 := by
      simp only [decPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [regs5, upd_ne h0 hr, decPs_restore _ _ _ r o hm, hsl r o hm]

section Ends

variable {M0 Ms M : Word → BitVec 8} {R : Word} {r0 : Fin 32 → Word} {nm : Machine}

theorem DecSt.slotW {off : Nat} (D : DecSt M0 Ms R r0 M nm off) {c : Nat} (h1 : 0x6D4 ≤ c)
    (h2 : c + 4 ≤ 0x6F0) : memLoad32 M (R + BitVec.ofNat 32 c) = memLoad32 Ms (R + BitVec.ofNat 32 c) :=
  memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact D.slots _ (by omega) (by omega)

theorem decPs_off {R : Word} : ∀ r o, (r, o) ∈ decPs →
    ∃ c, R + BitVec.ofNat 32 0x6D0 + o = R + BitVec.ofNat 32 c ∧ 0x6D4 ≤ c ∧ c + 4 ≤ 0x6F0 := by
  intro r o hm
  simp only [decPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨_, add_ofNat_assoc R 0x6D0 _, by decide, by decide⟩

theorem cb_load_off {M : Word → BitVec 8} {dst src : Word} {N c : Nat} (h : c + 4 ≤ N) (hN : N < 2 ^ 32) :
    memLoad32 (copyBytes M dst src N) (dst + BitVec.ofNat 32 c) = memLoad32 M (src + BitVec.ofNat 32 c) :=
  memLoad32_eq fun j hj => by rw [add_ofNat_assoc, add_ofNat_assoc, cb_in (by omega) hN]

theorem feW_eq2 {M M' : Word → BitVec 8} {a b : Word} (h : ∀ i, i < 10 →
    memLoad32 M' (a + BitVec.ofNat 32 (4 * i)) = memLoad32 M (b + BitVec.ofNat 32 (4 * i))) :
    feW M' a = feW M b := by
  unfold feW limbAt
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide),
    h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide)]

theorem feW_copyAt {M : Word → BitVec 8} {dst src : Word} {N c : Nat} (h : c + 40 ≤ N) (hN : N < 2 ^ 32) :
    feW (copyBytes M dst src N) (dst + BitVec.ofNat 32 c) = feW M (src + BitVec.ofNat 32 c) :=
  feW_eq2 fun i hi => by rw [add_ofNat_assoc, add_ofNat_assoc, cb_load_off (by omega) hN]

set_option maxRecDepth 20000 in
/-- From offset 0x332, when `u / v` is not a square: `None`. -/
theorem dec_none (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm 0x332) {out : Word} {rM : Fin 32 → Word}
    (hs2 : reg nm (18 : Fin 32) = out) (hout : out.toNat % 4 = 0) (sOR : Sep out 0xA4 R 0x6F0)
    (hoW : out.toNat + 0xA4 ≤ 0x40000000)
    (hsl : ∀ r o, (r, o) ∈ decPs → memLoad32 Ms (R + BitVec.ofNat 32 0x6D0 + o) = rM r)
    (hret : rM ra &&& ~~~1 = rM ra) :
    ∃ m', Steps nm m' ∧ m'.pc = rM ra ∧ reg m' sp = R + BitVec.ofNat 32 0x6F0 ∧
      (∀ r o, (r, o) ∈ decPs → reg m' r = rM r) ∧
      (∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg m' q = r0 q) ∧ memLoad32 m'.mem out = 0 ∧
      ∀ x, Sep R 0x6F0 x 1 → Sep out 0xA4 x 1 → m'.mem x = M0 x := by
  obtain ⟨n1, c1, D1, v1, k1⟩ := D.aluImmS C dec_at_332 (off' := 0x334) (by decide) (by decide)
  obtain ⟨m', c', pc', sp', sv', kp', mem'⟩ := dec_tail (C.code D1.agree C.E.cod (by decide) (by decide)) D1.st
    D1.hsp (by rw [k1 _ (by decide), hs2]) v1 hout C.hR
    (sep_of_le (by have : DEC.toNat = 0x403affd0 := by decide
                   omega) (by decide))
    (fun r o hm => by
      obtain ⟨c, hc, h1, h2⟩ := decPs_off (R := R) r o hm
      rw [hc, memLoad32_store32_sep (sep_pre (sOR.subR (c := c) (l := 4) (by omega)) (by omega)),
        D1.slotW h1 h2, ← hc]
      exact hsl r o hm) hret
  refine ⟨m', c1.trans c', pc', sp', sv', fun q hq => by rw [kp' q hq, D1.keep q hq], ?_, fun x hx hy => ?_⟩
  · rw [mem', memLoad32_store32_same, D.zero]; rfl
  · rw [mem', st32_frame (sep_pre hy (by decide)), D1.agree x hx]

theorem sep_self_off (b : Word) {c : Nat} (h : 4 ≤ c) (hc : c + 4 ≤ 2 ^ 32) : Sep b 4 (b + BitVec.ofNat 32 c) 4 := by
  have := sep_offsets b (c := 0) (n := 4) (d := c) (k := 4) (Or.inl h) (by decide) hc
  rwa [add_ofNat_zero] at this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- From offset 0x31C, when `u / v` is a square: the point's 160 bytes from
`R + 0x4A0` copied to `out + 4`, and the tag 1. -/
theorem dec_some (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm 0x31C) {out : Word} {rM : Fin 32 → Word}
    (hs2 : reg nm (18 : Fin 32) = out) (hout : out.toNat % 4 = 0) (sOR : Sep out 0xA4 R 0x6F0)
    (hoW : out.toNat + 0xA4 ≤ 0x40000000)
    (hsl : ∀ r o, (r, o) ∈ decPs → memLoad32 Ms (R + BitVec.ofNat 32 0x6D0 + o) = rM r)
    (hret : rM ra &&& ~~~1 = rM ra) :
    ∃ m', Steps nm m' ∧ m'.pc = rM ra ∧ reg m' sp = R + BitVec.ofNat 32 0x6F0 ∧
      (∀ r o, (r, o) ∈ decPs → reg m' r = rM r) ∧
      (∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg m' q = r0 q) ∧ memLoad32 m'.mem out = 1 ∧
      (∀ k, k < 4 → feW m'.mem (out + BitVec.ofNat 32 4 + BitVec.ofNat 32 (40 * k)) =
        feW M (R + BitVec.ofNat 32 0x4A0 + BitVec.ofNat 32 (40 * k))) ∧
      ∀ x, Sep R 0x6F0 x 1 → Sep out 0xA4 x 1 → m'.mem x = M0 x := by
  obtain ⟨n1, c1, D1, v1, k1⟩ := D.aluImmS C dec_at_31c (off' := 0x320) (by decide) (by decide)
  obtain ⟨n2, c2, D2, v2, k2⟩ := D1.aluImmS C dec_at_320 (off' := 0x322) (by decide) (by decide)
  obtain ⟨n3, c3, D3, v3, k3⟩ := D2.aluImmS C dec_at_322 (off' := 0x326) (by decide) (by decide)
  have a0_3 : reg n3 a0 = out + BitVec.ofNat 32 4 := by rw [k3 _ (by decide), k2 _ (by decide), v1, hs2]; rfl
  have a1_3 : reg n3 a1 = R + BitVec.ofNat 32 0x4A0 := by rw [k3 _ (by decide), v2, D1.hsp]; exact add_sp R rfl
  have a2_3 : reg n3 a2 = BitVec.ofNat 32 160 := by rw [v3, D2.zero]; rfl
  have s2_3 : reg n3 (18 : Fin 32) = out := by rw [k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), hs2]
  have hc := C.code D3.agree C.E.cod (by decide) (by decide)
  obtain ⟨n4, c4, pc4, mem4, regs4⟩ := D3.st.callRa (cb := BitVec.ofNat 32 memcpyStubAddress) hc dec_at_326
    dec_at_32a (by decide) (by decide)
  have r4 := PEnv.reg1 regs4 D3.zero
  have eF : R + BitVec.ofNat 32 0x450 + 0xFFFFFFF0 = R + BitVec.ofNat 32 0x440 := by rw [BitVec.add_assoc]; rfl
  have ho4 : (out + BitVec.ofNat 32 4).toNat = out.toNat + 4 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have sO4 : Sep (out + BitVec.ofNat 32 4) 160 R 0x6F0 := sOR.sub (by decide)
  have hst : (BitVec.ofNat 32 memcpyStubAddress + 8 : Word).toNat = 0x403b4856 := by decide
  have E : McEnv n4.mem (BitVec.ofNat 32 memcpyStubAddress + 8) (out + BitVec.ofNat 32 4) (R + BitVec.ofNat 32 0x4A0)
      (reg n4 sp + 0xFFFFFFF0) 160 := by
    rw [mem4, r4 sp (by decide), D3.hsp, eF]
    exact { code := C.code D3.agree C.E.mcb (by decide) (by decide)
            hDC := sep_of_le (by rw [ho4, hst]; omega) (by decide)
            hFC := C.hiSep (by decide) (by decide) (by decide)
            hdF := sO4.subR (by decide)
            hsF := C.offs (Or.inr (by decide)) (by decide) (by decide)
            hsep := sO4.subR (by decide)
            hF := aligned_add C.hR (by decide)
            hFw := by rw [C.toNat_off (by decide)]; have := C.hRw; omega
            hdw := by rw [ho4]; omega
            hsw := by rw [C.toNat_off (by decide)]; have := C.hRw; omega }
  obtain ⟨n5, c5, pc5, sp5, _, f5, k5⟩ := memcpy_correct n4 (BitVec.ofNat 32 memcpyStubAddress)
    (DEC + BitVec.ofNat 32 (0x326 + 8)) (out + BitVec.ofNat 32 4) (R + BitVec.ofNat 32 0x4A0) 160
    (fun i hi => by rw [mem4]; exact C.code D3.agree C.E.mcs (by decide) (by decide) i hi) (by decide) pc4
    (by rw [r4 a0 (by decide), a0_3]) (by rw [r4 a1 (by decide), a1_3]) (by rw [r4 a2 (by decide), a2_3])
    (by rw [regs4]; simp +decide [upd]) (even_clear _ (C.even _ (by decide))) E
  rw [mem4, r4 sp (by decide), D3.hsp, eF] at f5
  have hFo : ∀ c, c < 0xA4 → Sep (R + BitVec.ofNat 32 0x440) 16 (out + BitVec.ofNat 32 c) 1 := fun c hc =>
    ((sOR.sub (c := c) (l := 1) (by omega)).subR (c := 0x440) (l := 16) (by decide)).symm
  -- memory after the copy: the copy, away from `memcpy`'s frame
  have hMc : ∀ x, Sep (R + BitVec.ofNat 32 0x440) 16 x 1 → Sep (out + BitVec.ofNat 32 4) 160 x 1 → n5.mem x = M x :=
    fun x h1 h2 => by rw [f5 x h1, copyBytes_sep h2 (Nat.le_refl _)]
  have hcM : ∀ x : Word, 0x40000000 ≤ x.toNat → n5.mem x = M x := fun x hx =>
    hMc x (C.hiSep (by decide) hx (by have := x.isLt; omega)) (sep_of_le (by rw [ho4]; omega) (by have := x.isLt; omega))
  have hc5 : CodeIn n5.mem DEC edDecompressCode := hc.hi hcM (by decide) (by decide)
  have u5 : St n5.mem DEC n5 0x32E (reg n5) := ⟨by rw [pc5], rfl, fun _ => rfl⟩
  obtain ⟨n6, d6, u6⟩ := u5.aluImm hc5 dec_at_32e (off' := 0x330) (by decide)
  obtain ⟨n7, d7, u7⟩ := u6.jump hc5 dec_at_330 (off' := 0x334) (by decide) (by rw [u6.pc]; decide)
  have sp7 : reg n7 sp = R + BitVec.ofNat 32 0x450 := by
    rw [u7.upd_ne u5.zero sp (by decide), sp5, r4 sp (by decide), D3.hsp]
  have s27 : reg n7 (18 : Fin 32) = out := by
    rw [u7.upd_ne u5.zero _ (by decide), k5 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      r4 _ (by decide), s2_3]
  have a07 : reg n7 a0 = 1 := by rw [u7.upd_eq (by decide), u5.zero]; rfl
  obtain ⟨m', c', pc', sp', sv', kp', mem'⟩ := dec_tail hc5 u7.self sp7 s27 a07 hout C.hR
    (sep_of_le (by have : DEC.toNat = 0x403affd0 := by decide
                   omega) (by decide))
    (fun r o hm => by
      obtain ⟨c, hc', h1, h2⟩ := decPs_off (R := R) r o hm
      have e1 : memLoad32 n5.mem (R + BitVec.ofNat 32 c) = memLoad32 M (R + BitVec.ofNat 32 c) :=
        memLoad32_congr fun q hq => by
          rw [add_ofNat_assoc]
          exact hMc _ (C.offs (Or.inl (by omega)) (by decide) (by omega)) (sO4.subR (c := c + q) (l := 1) (by omega))
      rw [hc', memLoad32_store32_sep (sep_pre (sOR.subR (c := c) (l := 4) (by omega)) (by omega)), e1,
        D3.slotW h1 h2, ← hc']
      exact hsl r o hm) hret
  have keepn : ∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg n7 q = r0 q := fun q hq => by
    rw [u7.upd_ne u5.zero _ (by revert hq; revert q; decide),
      k5 q (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide) (by revert hq; revert q; decide)
        (by revert hq; revert q; decide) (by revert hq; revert q; decide),
      r4 q (by revert hq; revert q; decide), D3.keep q hq]
  refine ⟨m', c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (.cons d6 (.cons d7 c')))))), pc', sp', sv',
    fun q hq => by rw [kp' q hq, keepn q hq], by rw [mem', memLoad32_store32_same], fun k hk => ?_, fun x hx hy => ?_⟩
  · rw [mem']
    refine (feW_frame (M := n5.mem) fun i hi => ?_).trans ((feW_frame (M' := n5.mem) fun i hi => ?_).trans (feW_copyAt (N := 160) (c := 40 * k) (by omega) (by decide)))
    · rw [add_ofNat_assoc, add_ofNat_assoc]
      exact memLoad32_store32_sep (sep_self_off out (by omega) (by omega))
    · exact memLoad32_congr fun q hq => by
        rw [add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc, f5 _ (hFo _ (by omega))]
  · rw [mem', st32_frame (sep_pre hy (by decide)), hMc x (C.inR (by decide) hx) (hy.sub (by decide)), D3.agree x hx]

end Ends

section Phases

variable {M0 Ms M : Word → BitVec 8} {R : Word} {r0 : Fin 32 → Word} {nm : Machine}

/-- `load3_at`'s bytes, as addresses `load3_correct` forms them. -/
theorem ld3_addr (bp : Word) (i : Nat) :
    bp + BitVec.ofNat 32 i + 1 = bp + BitVec.ofNat 32 (i + 1) ∧
    bp + BitVec.ofNat 32 i + 2 = bp + BitVec.ofNat 32 (i + 2) ∧
    bp + BitVec.ofNat 32 i + 3 = bp + BitVec.ofNat 32 (i + 3) :=
  ⟨add_ofNat_assoc bp i 1, add_ofNat_assoc bp i 2, add_ofNat_assoc bp i 3⟩

set_option maxRecDepth 20000 in
/-- `li a1, i; mv a0, s4; call load3_at; sw zero, hi+4(sp); slli a0, a0, sh;
sw a0, hi(sp)`: one `u64` limb of `from_bytes`. -/
theorem DecSt.ld3G (C : DecCtx M0 R) {o : Nat} (D : DecSt M0 Ms R r0 M nm o) {bp : Word} (hs4 : reg nm (20 : Fin 32) = bp)
    (hB : ∀ j, j < 32 → M (bp + BitVec.ofNat 32 j) = M0 (bp + BitVec.ofNat 32 j))
    {i sh hi : Nat} {imm o2 : Word}
    (f1 : fetchRel edDecompressCode o = some (.aluImm .add a1 x0 (BitVec.ofNat 32 i), 2))
    (f2 : fetchRel edDecompressCode (o + 2) = some (.alu .add a0 x0 (20 : Fin 32), 2))
    (f3 : fetchRel edDecompressCode (o + 2 + 2) = some (.auipc ra imm, 4))
    (f4 : fetchRel edDecompressCode (o + 2 + 2 + 4) = some (.jalr ra ra o2, 4))
    (hb : DEC + BitVec.ofNat 32 (o + 2 + 2) + imm + o2 = BitVec.ofNat 32 feLoad3Address)
    (f5 : fetchRel edDecompressCode (o + 2 + 2 + 8) = some (.store .sw sp x0 (BitVec.ofNat 32 (hi + 4)), 2))
    (f6 : fetchRel edDecompressCode (o + 2 + 2 + 8 + 2) = some (.aluImm .sll a0 a0 (BitVec.ofNat 32 sh), 2))
    (f7 : fetchRel edDecompressCode (o + 2 + 2 + 8 + 2 + 2) = some (.store .sw sp a0 (BitVec.ofNat 32 hi), 2))
    (ho : o % 2 = 0) (hi4 : hi % 4 = 0) (hhi : 0x450 + hi + 8 ≤ 0x6D4) (hsh : sh < 32) (hi32 : i + 3 ≤ 32)
    {o' : Nat} (ho' : o + 2 + 2 + 8 + 2 + 2 + 2 = o') :
    ∃ nm' w, Steps nm nm' ∧
      DecSt M0 Ms R r0 (memStore32 (memStore32 M (R + BitVec.ofNat 32 (0x450 + hi + 4)) 0)
        (R + BitVec.ofNat 32 (0x450 + hi)) w) nm' o' ∧
      w.toNat = (byteN M0 bp i + 2 ^ 8 * byteN M0 bp (i + 1) + 2 ^ 16 * byteN M0 bp (i + 2)) * 2 ^ sh % 2 ^ 32 ∧
      reg nm' (20 : Fin 32) = bp ∧ (∀ q, q.val ∈ [8, 9, 18, 19, 20, 21] → reg nm' q = reg nm q) := by
  obtain ⟨n1, c1, D1, v1, k1⟩ := D.aluImmS C f1 (ofNat_add2 o) (by decide)
  obtain ⟨n2, c2, D2, v2, k2⟩ := D1.aluS C f2 (ofNat_add2 _) (by decide)
  obtain ⟨n3, c3, D3, v3, k3⟩ := D2.load3 C f3 f4 hb (by omega)
  have a0_2 : reg n2 a0 = bp := by rw [v2, D1.zero, k1 _ (by decide), hs4]; exact BitVec.zero_add _
  have a1_2 : reg n2 a1 = BitVec.ofNat 32 i := by rw [k2 _ (by decide), v1, D.zero]; exact BitVec.zero_add _
  rw [a0_2, a1_2, (ld3_addr bp i).1, (ld3_addr bp i).2.1, hB _ (by omega), hB _ (by omega), hB _ (by omega)] at v3
  obtain ⟨n4, c4, D4, k4⟩ := D3.swF C f5 (ofNat_add2 _) (c := 0x450 + hi + 4)
    (by rw [k3 sp (by decide) (by decide) (by decide) (by decide), k2 sp (by decide), k1 sp (by decide), D.hsp,
      add_ofNat_assoc, show 0x450 + (hi + 4) = 0x450 + hi + 4 by omega]) (by omega) (by omega) (by omega)
  rw [D3.zero] at D4
  obtain ⟨n5, c5, D5, v5, k5⟩ := D4.aluImmS C f6 (ofNat_add2 _) (by decide)
  obtain ⟨n6, c6, D6, k6⟩ := D5.swF C f7 (ofNat_add2 _) (c := 0x450 + hi)
    (by rw [k5 sp (by decide), k4 sp, k3 sp (by decide) (by decide) (by decide) (by decide), k2 sp (by decide),
      k1 sp (by decide), D.hsp, add_ofNat_assoc]) (by omega) (by omega) (by omega)
  subst ho'
  refine ⟨n6, reg n5 a0, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans c6)))), D6, ?_, ?_, fun q hq => ?_⟩
  · rw [v5, sll_toNat, k4 a0, v3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sh < 2 ^ 32),
      Nat.mod_eq_of_lt hsh]
  · rw [k6, k5 _ (by decide), k4, k3 _ (by decide) (by decide) (by decide) (by decide), k2 _ (by decide),
      k1 _ (by decide), hs4]
  · have h0 : q ≠ a0 := by revert hq; revert q; decide
    have h1 : q ≠ a1 := by revert hq; revert q; decide
    have h2 : q ≠ a2 := by revert hq; revert q; decide
    have hr : q ≠ ra := by revert hq; revert q; decide
    rw [k6, k5 q h0, k4, k3 q h0 h1 h2 hr, k2 q h0, k1 q h1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x1E to 0xE0: `FieldElement::from_bytes` of the 32 bytes at
`bp`, with the result `Y` at `R + 0x544`. -/
theorem dec_ph1 (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm 0x1E) {out bp : Word}
    (ha0 : reg nm a0 = out) (ha1 : reg nm a1 = bp) (sB : Sep bp 32 R 0x6F0) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' 0xE0 ∧ reg nm' (18 : Fin 32) = out ∧
      reg nm' (20 : Fin 32) = bp ∧
      feW nm'.mem (R + BitVec.ofNat 32 0x544) = redL (decLoad (memBytes M0 bp 32)) := by
  obtain ⟨n1, c1, D1, v1, k1⟩ := D.aluS C dec_at_1e (off' := 0x20) (by decide) (by decide)
  obtain ⟨n2, c2, D2, v2, k2⟩ := D1.aluS C dec_at_20 (off' := 0x22) (by decide) (by decide)
  obtain ⟨n3, c3, D3, v3, k3⟩ := D2.aluS C dec_at_22 (off' := 0x24) (by decide) (by decide)
  obtain ⟨n4, c4, D4, v4, k4⟩ := D3.aluImmS C dec_at_24 (off' := 0x26) (by decide) (by decide)
  have s4_1 : reg n1 (20 : Fin 32) = bp := by rw [v1, D.zero, ha1]; exact BitVec.zero_add _
  have s2_2 : reg n2 (18 : Fin 32) = out := by rw [v2, D1.zero, k1 _ (by decide), ha0]; exact BitVec.zero_add _
  have a0_4 : reg n4 a0 = bp := by
    rw [k4 _ (by decide), v3, D2.zero, k2 _ (by decide), k1 _ (by decide), ha1]; exact BitVec.zero_add _
  have a1_4 : reg n4 a1 = BitVec.ofNat 32 0 := by rw [v4, D3.zero]; rfl
  have s4_4 : reg n4 (20 : Fin 32) = bp := by rw [k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), s4_1]
  have s2_4 : reg n4 (18 : Fin 32) = out := by rw [k4 _ (by decide), k3 _ (by decide), s2_2]
  -- limb 0: `load4_at(0)`
  obtain ⟨n5, c5, D5, v5, k5⟩ := D4.load4 C dec_at_26 dec_at_2a (by decide) (by decide)
  rw [a0_4, a1_4, (ld3_addr bp 0).1, (ld3_addr bp 0).2.1, (ld3_addr bp 0).2.2, D4.bytes sB _ (by decide),
    D4.bytes sB _ (by decide), D4.bytes sB _ (by decide), D4.bytes sB _ (by decide)] at v5
  have sp5 : reg n5 sp = R + BitVec.ofNat 32 0x450 := D5.hsp
  obtain ⟨n6, c6, D6, k6⟩ := D5.swF C dec_at_2e (off' := 0x30) (by decide) (c := 0x4A4) (by rw [sp5]; exact add_off R rfl) (by decide)
    (by decide) (by decide)
  rw [D5.zero] at D6
  obtain ⟨n7, c7, D7, k7⟩ := D6.swF C dec_at_30 (off' := 0x32) (by decide) (c := 0x4A0) (by rw [k6, sp5]; exact add_off R rfl) (by decide)
    (by decide) (by decide)
  have s4_7 : reg n7 (20 : Fin 32) = bp := by
    rw [k7, k6, k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), s4_4]
  have s2_7 : reg n7 (18 : Fin 32) = out := by
    rw [k7, k6, k5 _ (by decide) (by decide) (by decide) (by decide) (by decide), s2_4]
  -- limbs 1 to 4: `load3_at`
  obtain ⟨n8, w1, c8, D8, hw1, s4_8, k8⟩ := D7.ld3G C s4_7 (D7.bytes sB) (o' := 0x44) (i := 4) (sh := 6) (hi := 0x58)
    dec_at_32 dec_at_34 dec_at_36 dec_at_3a (by decide) dec_at_3e dec_at_40 dec_at_42 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  obtain ⟨n9, w2, c9, D9, hw2, s4_9, k9⟩ := D8.ld3G C s4_8 (D8.bytes sB) (o' := 0x56) (i := 7) (sh := 5) (hi := 0x60)
    dec_at_44 dec_at_46 dec_at_48 dec_at_4c (by decide) dec_at_50 dec_at_52 dec_at_54 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  obtain ⟨n10, w3, c10, D10, hw3, s4_10, k10⟩ := D9.ld3G C s4_9 (D9.bytes sB) (o' := 0x68) (i := 10) (sh := 3) (hi := 0x68)
    dec_at_56 dec_at_58 dec_at_5a dec_at_5e (by decide) dec_at_62 dec_at_64 dec_at_66 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  obtain ⟨n11, w4, c11, D11, hw4, s4_11, k11⟩ := D10.ld3G C s4_10 (D10.bytes sB) (o' := 0x7A) (i := 13) (sh := 2) (hi := 0x70)
    dec_at_68 dec_at_6a dec_at_6c dec_at_70 (by decide) dec_at_74 dec_at_76 dec_at_78 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  -- limb 5: `load4_at(16)`
  obtain ⟨n12, c12, D12, v12, k12⟩ := D11.aluImmS C dec_at_7a (off' := 0x7C) (by decide) (by decide)
  obtain ⟨n13, c13, D13, v13, k13⟩ := D12.aluS C dec_at_7c (off' := 0x7E) (by decide) (by decide)
  obtain ⟨n14, c14, D14, v14, k14⟩ := D13.load4 C dec_at_7e dec_at_82 (by decide) (by decide)
  have a0_13 : reg n13 a0 = bp := by rw [v13, D12.zero, k12 _ (by decide), s4_11]; exact BitVec.zero_add _
  have a1_13 : reg n13 a1 = BitVec.ofNat 32 16 := by rw [k13 _ (by decide), v12, D11.zero]; rfl
  rw [a0_13, a1_13, (ld3_addr bp 16).1, (ld3_addr bp 16).2.1, (ld3_addr bp 16).2.2, D13.bytes sB _ (by decide),
    D13.bytes sB _ (by decide), D13.bytes sB _ (by decide), D13.bytes sB _ (by decide)] at v14
  have sp14 : reg n14 sp = R + BitVec.ofNat 32 0x450 := D14.hsp
  obtain ⟨n15, c15, D15, k15⟩ := D14.swF C dec_at_86 (off' := 0x88) (by decide) (c := 0x4CC) (by rw [sp14]; exact add_off R rfl) (by decide)
    (by decide) (by decide)
  rw [D14.zero] at D15
  obtain ⟨n16, c16, D16, k16⟩ := D15.swF C dec_at_88 (off' := 0x8A) (by decide) (c := 0x4C8) (by rw [k15, sp14]; exact add_off R rfl)
    (by decide) (by decide) (by decide)
  have s4_16 : reg n16 (20 : Fin 32) = bp := by
    rw [k16, k15, k14 _ (by decide) (by decide) (by decide) (by decide) (by decide), k13 _ (by decide),
      k12 _ (by decide), s4_11]
  -- limbs 6 to 8: `load3_at`
  obtain ⟨n17, w6, c17, D17, hw6, s4_17, k17⟩ := D16.ld3G C s4_16 (D16.bytes sB) (o' := 0x9C) (i := 20) (sh := 7) (hi := 0x80)
    dec_at_8a dec_at_8c dec_at_8e dec_at_92 (by decide) dec_at_96 dec_at_98 dec_at_9a (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  obtain ⟨n18, w7, c18, D18, hw7, s4_18, k18⟩ := D17.ld3G C s4_17 (D17.bytes sB) (o' := 0xAE) (i := 23) (sh := 5) (hi := 0x88)
    dec_at_9c dec_at_9e dec_at_a0 dec_at_a4 (by decide) dec_at_a8 dec_at_aa dec_at_ac (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  obtain ⟨n19, w8, c19, D19, hw8, s4_19, k19⟩ := D18.ld3G C s4_18 (D18.bytes sB) (o' := 0xC0) (i := 26) (sh := 4) (hi := 0x90)
    dec_at_ae dec_at_b0 dec_at_b2 dec_at_b6 (by decide) dec_at_ba dec_at_bc dec_at_be (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  -- limb 9: `(load3_at(29) & 0x7FFFFF) << 2`
  obtain ⟨n20, c20, D20, v20, k20⟩ := D19.aluImmS C dec_at_c0 (off' := 0xC2) (by decide) (by decide)
  obtain ⟨n21, c21, D21, v21, k21⟩ := D20.aluS C dec_at_c2 (off' := 0xC4) (by decide) (by decide)
  obtain ⟨n22, c22, D22, v22, k22⟩ := D21.load3 C dec_at_c4 dec_at_c8 (by decide) (by decide)
  have a0_21 : reg n21 a0 = bp := by rw [v21, D20.zero, k20 _ (by decide), s4_19]; exact BitVec.zero_add _
  have a1_21 : reg n21 a1 = BitVec.ofNat 32 29 := by rw [k21 _ (by decide), v20, D19.zero]; rfl
  rw [a0_21, a1_21, (ld3_addr bp 29).1, (ld3_addr bp 29).2.1, D21.bytes sB _ (by decide), D21.bytes sB _ (by decide),
    D21.bytes sB _ (by decide)] at v22
  have sp22 : reg n22 sp = R + BitVec.ofNat 32 0x450 := D22.hsp
  obtain ⟨n23, c23, D23, k23⟩ := D22.swF C dec_at_cc (off' := 0xCE) (by decide) (c := 0x4EC) (by rw [sp22]; exact add_off R rfl) (by decide)
    (by decide) (by decide)
  rw [D22.zero] at D23
  obtain ⟨n24, c24, D24, v24, k24⟩ := D23.aluImmS C dec_at_ce (off' := 0xD0) (by decide) (by decide)
  obtain ⟨n25, c25, D25, v25, k25⟩ := D24.aluImmS C dec_at_d0 (off' := 0xD2) (by decide) (by decide)
  obtain ⟨n26, c26, D26, k26⟩ := D25.swF C dec_at_d2 (off' := 0xD4) (by decide) (c := 0x4E8)
    (by rw [k25 _ (by decide), k24 _ (by decide), k23, sp22]; exact add_off R rfl) (by decide) (by decide) (by decide)
  -- `reduce`
  obtain ⟨n27, c27, D27, v27, k27⟩ := D26.aluImmS C dec_at_d4 (off' := 0xD6) (by decide) (by decide)
  obtain ⟨n28, c28, D28, v28, k28⟩ := D27.aluImmS C dec_at_d6 (off' := 0xD8) (by decide) (by decide)
  have sp26 : reg n26 sp = R + BitVec.ofNat 32 0x450 := D26.hsp
  obtain ⟨n29, c29, D29, w29, k29, _⟩ := D28.reduce C dec_at_d8 dec_at_dc (by decide) (by decide) (k := 0x544) (j := 0x4A0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [k28 _ (by decide), v27, sp26]; exact add_sp R rfl) (by rw [v28, k27 _ (by decide), sp26]; exact add_sp R rfl)
  have s4_26 : reg n26 (20 : Fin 32) = bp := by
    rw [k26, k25 _ (by decide), k24 _ (by decide), k23, k22 _ (by decide) (by decide) (by decide) (by decide),
      k21 _ (by decide), k20 _ (by decide), s4_19]
  have s2_26 : reg n26 (18 : Fin 32) = out := by
    rw [k26, k25 _ (by decide), k24 _ (by decide), k23, k22 _ (by decide) (by decide) (by decide) (by decide),
      k21 _ (by decide), k20 _ (by decide), k19 _ (by decide), k18 _ (by decide), k17 _ (by decide), k16, k15,
      k14 _ (by decide) (by decide) (by decide) (by decide) (by decide), k13 _ (by decide), k12 _ (by decide),
      k11 _ (by decide), k10 _ (by decide), k9 _ (by decide), k8 _ (by decide), s2_7]
  refine ⟨n29, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans
    (c11.trans (c12.trans (c13.trans (c14.trans (c15.trans (c16.trans (c17.trans (c18.trans (c19.trans (c20.trans
    (c21.trans (c22.trans (c23.trans (c24.trans (c25.trans (c26.trans (c27.trans (c28.trans c29))))))))))))))))))))))))))),
    D29, ?_, ?_, ?_⟩
  · rw [k29 _ (by decide), k28 _ (by decide), k27 _ (by decide), s2_26]
  · rw [k29 _ (by decide), k28 _ (by decide), k27 _ (by decide), s4_26]
  · rw [w29]
    congr 1
    rw [show List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from rfl]
    simp only [List.map_cons, List.map_nil, u64At, add_ofNat_assoc]
    simp (disch := decide) only [ld_st_eq, ld_st_ne]
    rw [k6, v5, hw1, hw2, hw3, hw4, k15, v14, hw6, hw7, hw8, v25, srl_toNat, v24, sll_toNat, k23, v22,
      show (9 : Word).toNat % 32 = 9 from rfl, show (7 : Word).toNat % 32 = 7 from rfl]
    unfold decLoad
    simp (disch := decide) only [getD_memBytes]
    rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0xE0 to 0x174: `Y²`, `u = Y² - 1`, `v = d Y² + 1`, and the
products `u v³` and `u v⁷` that `sqrt_ratio_i` starts from. -/
theorem dec_ph2 (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm 0xE0) {out bp : Word} {Y one d u v : List Nat}
    (hs2 : reg nm (18 : Fin 32) = out) (hs4 : reg nm (20 : Fin 32) = bp)
    (hY : feW M (R + BitVec.ofNat 32 0x544) = Y)
    (sO : Sep (BitVec.ofNat 32 edOneAddress) 40 R 0x6F0) (sD : Sep (BitVec.ofNat 32 edDAddress) 40 R 0x6F0)
    (hO : feW M0 (BitVec.ofNat 32 edOneAddress) = one) (hDd : feW M0 (BitVec.ofNat 32 edDAddress) = d)
    (hu : u = subL (sqL Y) one) (hv : v = addL (mulL (sqL Y) d) one) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' 0x174 ∧ reg nm' (18 : Fin 32) = out ∧
      reg nm' (20 : Fin 32) = bp ∧ feW nm'.mem (R + BitVec.ofNat 32 0x544) = Y ∧
      feW nm'.mem (R + BitVec.ofNat 32 0x594) = u ∧ feW nm'.mem (R + BitVec.ofNat 32 0x5BC) = v ∧
      feW nm'.mem (R + BitVec.ofNat 32 0x634) = mulL u (sqrtV3 v) ∧
      feW nm'.mem (R + BitVec.ofNat 32 0x684) = mulL u (sqrtV7 v) := by
  obtain ⟨n1, c1, D1, v1, k1⟩ := D.aluImmS C dec_at_e0 (off' := 0xE2) (by decide) (by decide)
  have r1_18 : reg n1 (18 : Fin 32) = out := by rw [k1 _ (by decide), hs2]
  have r1_20 : reg n1 (20 : Fin 32) = bp := by rw [k1 _ (by decide), hs4]
  have r1_10 : reg n1 a0 = R + BitVec.ofNat 32 0x56C := by rw [v1, D.hsp]; exact add_sp R rfl
  obtain ⟨n2, c2, D2, v2, k2⟩ := D1.aluImmS C dec_at_e2 (off' := 0xE4) (by decide) (by decide)
  have r2_18 : reg n2 (18 : Fin 32) = out := by rw [k2 _ (by decide), r1_18]
  have r2_20 : reg n2 (20 : Fin 32) = bp := by rw [k2 _ (by decide), r1_20]
  have r2_10 : reg n2 a0 = R + BitVec.ofNat 32 0x56C := by rw [k2 _ (by decide), r1_10]
  have r2_11 : reg n2 a1 = R + BitVec.ofNat 32 0x544 := by rw [v2, D1.hsp]; exact add_sp R rfl
  obtain ⟨n3, c3, D3, w3, k3, f3⟩ := D2.sq C dec_at_e4 dec_at_e8 (by decide) (by decide) (k := 0x56C) (by decide) (by decide) (by decide) r2_10 (by rw [r2_11]; exact C.opF (by decide) (by decide) (by decide))
  have r3_18 : reg n3 (18 : Fin 32) = out := by rw [k3 _ (by decide), r2_18]
  have r3_20 : reg n3 (20 : Fin 32) = bp := by rw [k3 _ (by decide), r2_20]
  have m3_544 : feW n3.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f3 (by decide) (by decide) (by decide) (by decide)).trans hY
  have m3_56c : feW n3.mem (R + BitVec.ofNat 32 0x56C) = sqL (Y) := by rw [w3, r2_11, hY]
  obtain ⟨n4, c4, D4, v4, k4⟩ := D3.luiS C dec_at_ec (off' := 0xF0) (by decide) (by decide)
  have r4_18 : reg n4 (18 : Fin 32) = out := by rw [k4 _ (by decide), r3_18]
  have r4_20 : reg n4 (20 : Fin 32) = bp := by rw [k4 _ (by decide), r3_20]
  obtain ⟨n5, c5, D5, v5, k5⟩ := D4.aluImmS C dec_at_f0 (off' := 0xF4) (by decide) (by decide)
  have r5_18 : reg n5 (18 : Fin 32) = out := by rw [k5 _ (by decide), r4_18]
  have r5_20 : reg n5 (20 : Fin 32) = bp := by rw [k5 _ (by decide), r4_20]
  have r5_8 : reg n5 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [v5, v4]; decide
  obtain ⟨n6, c6, D6, v6, k6⟩ := D5.aluImmS C dec_at_f4 (off' := 0xF6) (by decide) (by decide)
  have r6_18 : reg n6 (18 : Fin 32) = out := by rw [k6 _ (by decide), r5_18]
  have r6_20 : reg n6 (20 : Fin 32) = bp := by rw [k6 _ (by decide), r5_20]
  have r6_8 : reg n6 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k6 _ (by decide), r5_8]
  have r6_10 : reg n6 a0 = R + BitVec.ofNat 32 0x594 := by rw [v6, D5.hsp]; exact add_sp R rfl
  obtain ⟨n7, c7, D7, v7, k7⟩ := D6.aluImmS C dec_at_f6 (off' := 0xF8) (by decide) (by decide)
  have r7_18 : reg n7 (18 : Fin 32) = out := by rw [k7 _ (by decide), r6_18]
  have r7_20 : reg n7 (20 : Fin 32) = bp := by rw [k7 _ (by decide), r6_20]
  have r7_8 : reg n7 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k7 _ (by decide), r6_8]
  have r7_10 : reg n7 a0 = R + BitVec.ofNat 32 0x594 := by rw [k7 _ (by decide), r6_10]
  have r7_11 : reg n7 a1 = R + BitVec.ofNat 32 0x56C := by rw [v7, D6.hsp]; exact add_sp R rfl
  obtain ⟨n8, c8, D8, v8, k8⟩ := D7.aluS C dec_at_f8 (off' := 0xFA) (by decide) (by decide)
  have r8_18 : reg n8 (18 : Fin 32) = out := by rw [k8 _ (by decide), r7_18]
  have r8_20 : reg n8 (20 : Fin 32) = bp := by rw [k8 _ (by decide), r7_20]
  have r8_8 : reg n8 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k8 _ (by decide), r7_8]
  have r8_10 : reg n8 a0 = R + BitVec.ofNat 32 0x594 := by rw [k8 _ (by decide), r7_10]
  have r8_11 : reg n8 a1 = R + BitVec.ofNat 32 0x56C := by rw [k8 _ (by decide), r7_11]
  have r8_12 : reg n8 a2 = BitVec.ofNat 32 edOneAddress := by rw [v8, D7.zero, r7_8]; exact BitVec.zero_add _
  obtain ⟨n9, c9, D9, w9, k9, f9⟩ := D8.sub C dec_at_fa dec_at_fe (by decide) (by decide) (k := 0x594) (by decide) (by decide) (by decide) r8_10 (by rw [r8_11]; exact C.opF (by decide) (by decide) (by decide)) (by rw [r8_12]; exact C.opC sO (by decide))
  have r9_18 : reg n9 (18 : Fin 32) = out := by rw [k9 _ (by decide), r8_18]
  have r9_20 : reg n9 (20 : Fin 32) = bp := by rw [k9 _ (by decide), r8_20]
  have r9_8 : reg n9 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k9 _ (by decide), r8_8]
  have m9_544 : feW n9.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f9 (by decide) (by decide) (by decide) (by decide)).trans m3_544
  have m9_56c : feW n9.mem (R + BitVec.ofNat 32 0x56C) = sqL (Y) := (keepW C f9 (by decide) (by decide) (by decide) (by decide)).trans m3_56c
  have m9_594 : feW n9.mem (R + BitVec.ofNat 32 0x594) = u := by rw [w9, r8_11, r8_12, m3_56c, (D8.constW sO), hO, hu]
  obtain ⟨n10, c10, D10, v10, k10⟩ := D9.luiS C dec_at_102 (off' := 0x106) (by decide) (by decide)
  have r10_18 : reg n10 (18 : Fin 32) = out := by rw [k10 _ (by decide), r9_18]
  have r10_20 : reg n10 (20 : Fin 32) = bp := by rw [k10 _ (by decide), r9_20]
  have r10_8 : reg n10 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k10 _ (by decide), r9_8]
  obtain ⟨n11, c11, D11, v11, k11⟩ := D10.aluImmS C dec_at_106 (off' := 0x10A) (by decide) (by decide)
  have r11_18 : reg n11 (18 : Fin 32) = out := by rw [k11 _ (by decide), r10_18]
  have r11_20 : reg n11 (20 : Fin 32) = bp := by rw [k11 _ (by decide), r10_20]
  have r11_8 : reg n11 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k11 _ (by decide), r10_8]
  have r11_12 : reg n11 a2 = BitVec.ofNat 32 edDAddress := by rw [v11, v10]; decide
  obtain ⟨n12, c12, D12, v12, k12⟩ := D11.aluImmS C dec_at_10a (off' := 0x10C) (by decide) (by decide)
  have r12_18 : reg n12 (18 : Fin 32) = out := by rw [k12 _ (by decide), r11_18]
  have r12_20 : reg n12 (20 : Fin 32) = bp := by rw [k12 _ (by decide), r11_20]
  have r12_8 : reg n12 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k12 _ (by decide), r11_8]
  have r12_12 : reg n12 a2 = BitVec.ofNat 32 edDAddress := by rw [k12 _ (by decide), r11_12]
  have r12_10 : reg n12 a0 = R + BitVec.ofNat 32 0x4A0 := by rw [v12, D11.hsp]; exact add_sp R rfl
  obtain ⟨n13, c13, D13, v13, k13⟩ := D12.aluImmS C dec_at_10c (off' := 0x10E) (by decide) (by decide)
  have r13_18 : reg n13 (18 : Fin 32) = out := by rw [k13 _ (by decide), r12_18]
  have r13_20 : reg n13 (20 : Fin 32) = bp := by rw [k13 _ (by decide), r12_20]
  have r13_8 : reg n13 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k13 _ (by decide), r12_8]
  have r13_12 : reg n13 a2 = BitVec.ofNat 32 edDAddress := by rw [k13 _ (by decide), r12_12]
  have r13_10 : reg n13 a0 = R + BitVec.ofNat 32 0x4A0 := by rw [k13 _ (by decide), r12_10]
  have r13_11 : reg n13 a1 = R + BitVec.ofNat 32 0x56C := by rw [v13, D12.hsp]; exact add_sp R rfl
  obtain ⟨n14, c14, D14, w14, k14, f14⟩ := D13.mul C dec_at_10e dec_at_112 (by decide) (by decide) (k := 0x4A0) (by decide) (by decide) (by decide) r13_10 (by rw [r13_11]; exact C.opF (by decide) (by decide) (by decide)) (by rw [r13_12]; exact C.opC sD (by decide))
  have r14_18 : reg n14 (18 : Fin 32) = out := by rw [k14 _ (by decide), r13_18]
  have r14_20 : reg n14 (20 : Fin 32) = bp := by rw [k14 _ (by decide), r13_20]
  have r14_8 : reg n14 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k14 _ (by decide), r13_8]
  have m14_544 : feW n14.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f14 (by decide) (by decide) (by decide) (by decide)).trans m9_544
  have m14_56c : feW n14.mem (R + BitVec.ofNat 32 0x56C) = sqL (Y) := (keepW C f14 (by decide) (by decide) (by decide) (by decide)).trans m9_56c
  have m14_594 : feW n14.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f14 (by decide) (by decide) (by decide) (by decide)).trans m9_594
  have m14_4a0 : feW n14.mem (R + BitVec.ofNat 32 0x4A0) = mulL (sqL (Y)) (d) := by rw [w14, r13_11, r13_12, m9_56c, (D13.constW sD), hDd]
  obtain ⟨n15, c15, D15, v15, k15⟩ := D14.aluImmS C dec_at_116 (off' := 0x118) (by decide) (by decide)
  have r15_18 : reg n15 (18 : Fin 32) = out := by rw [k15 _ (by decide), r14_18]
  have r15_20 : reg n15 (20 : Fin 32) = bp := by rw [k15 _ (by decide), r14_20]
  have r15_8 : reg n15 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k15 _ (by decide), r14_8]
  have r15_10 : reg n15 a0 = R + BitVec.ofNat 32 0x5BC := by rw [v15, D14.hsp]; exact add_sp R rfl
  obtain ⟨n16, c16, D16, v16, k16⟩ := D15.aluImmS C dec_at_118 (off' := 0x11A) (by decide) (by decide)
  have r16_18 : reg n16 (18 : Fin 32) = out := by rw [k16 _ (by decide), r15_18]
  have r16_20 : reg n16 (20 : Fin 32) = bp := by rw [k16 _ (by decide), r15_20]
  have r16_8 : reg n16 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k16 _ (by decide), r15_8]
  have r16_10 : reg n16 a0 = R + BitVec.ofNat 32 0x5BC := by rw [k16 _ (by decide), r15_10]
  have r16_11 : reg n16 a1 = R + BitVec.ofNat 32 0x4A0 := by rw [v16, D15.hsp]; exact add_sp R rfl
  obtain ⟨n17, c17, D17, v17, k17⟩ := D16.aluS C dec_at_11a (off' := 0x11C) (by decide) (by decide)
  have r17_18 : reg n17 (18 : Fin 32) = out := by rw [k17 _ (by decide), r16_18]
  have r17_20 : reg n17 (20 : Fin 32) = bp := by rw [k17 _ (by decide), r16_20]
  have r17_8 : reg n17 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k17 _ (by decide), r16_8]
  have r17_10 : reg n17 a0 = R + BitVec.ofNat 32 0x5BC := by rw [k17 _ (by decide), r16_10]
  have r17_11 : reg n17 a1 = R + BitVec.ofNat 32 0x4A0 := by rw [k17 _ (by decide), r16_11]
  have r17_12 : reg n17 a2 = BitVec.ofNat 32 edOneAddress := by rw [v17, D16.zero, r16_8]; exact BitVec.zero_add _
  obtain ⟨n18, c18, D18, w18, k18, f18⟩ := D17.add C dec_at_11c dec_at_120 (by decide) (by decide) (k := 0x5BC) (by decide) (by decide) (by decide) r17_10 (by rw [r17_11]; exact C.opF (by decide) (by decide) (by decide)) (by rw [r17_12]; exact C.opC sO (by decide)) (by rw [r17_11]; exact C.wideF (by decide))
  have r18_18 : reg n18 (18 : Fin 32) = out := by rw [k18 _ (by decide), r17_18]
  have r18_20 : reg n18 (20 : Fin 32) = bp := by rw [k18 _ (by decide), r17_20]
  have r18_8 : reg n18 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k18 _ (by decide), r17_8]
  have m18_544 : feW n18.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f18 (by decide) (by decide) (by decide) (by decide)).trans m14_544
  have m18_56c : feW n18.mem (R + BitVec.ofNat 32 0x56C) = sqL (Y) := (keepW C f18 (by decide) (by decide) (by decide) (by decide)).trans m14_56c
  have m18_594 : feW n18.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f18 (by decide) (by decide) (by decide) (by decide)).trans m14_594
  have m18_4a0 : feW n18.mem (R + BitVec.ofNat 32 0x4A0) = mulL (sqL (Y)) (d) := (keepW C f18 (by decide) (by decide) (by decide) (by decide)).trans m14_4a0
  have m18_5bc : feW n18.mem (R + BitVec.ofNat 32 0x5BC) = v := by rw [w18, r17_11, r17_12, m14_4a0, (D17.constW sO), hO, hv]
  obtain ⟨n19, c19, D19, v19, k19⟩ := D18.aluImmS C dec_at_124 (off' := 0x126) (by decide) (by decide)
  have r19_18 : reg n19 (18 : Fin 32) = out := by rw [k19 _ (by decide), r18_18]
  have r19_20 : reg n19 (20 : Fin 32) = bp := by rw [k19 _ (by decide), r18_20]
  have r19_8 : reg n19 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k19 _ (by decide), r18_8]
  have r19_10 : reg n19 a0 = R + BitVec.ofNat 32 0x4A0 := by rw [v19, D18.hsp]; exact add_sp R rfl
  obtain ⟨n20, c20, D20, v20, k20⟩ := D19.aluImmS C dec_at_126 (off' := 0x128) (by decide) (by decide)
  have r20_18 : reg n20 (18 : Fin 32) = out := by rw [k20 _ (by decide), r19_18]
  have r20_20 : reg n20 (20 : Fin 32) = bp := by rw [k20 _ (by decide), r19_20]
  have r20_8 : reg n20 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k20 _ (by decide), r19_8]
  have r20_10 : reg n20 a0 = R + BitVec.ofNat 32 0x4A0 := by rw [k20 _ (by decide), r19_10]
  have r20_11 : reg n20 a1 = R + BitVec.ofNat 32 0x5BC := by rw [v20, D19.hsp]; exact add_sp R rfl
  obtain ⟨n21, c21, D21, w21, k21, f21⟩ := D20.sq C dec_at_128 dec_at_12c (by decide) (by decide) (k := 0x4A0) (by decide) (by decide) (by decide) r20_10 (by rw [r20_11]; exact C.opF (by decide) (by decide) (by decide))
  have r21_18 : reg n21 (18 : Fin 32) = out := by rw [k21 _ (by decide), r20_18]
  have r21_20 : reg n21 (20 : Fin 32) = bp := by rw [k21 _ (by decide), r20_20]
  have r21_8 : reg n21 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k21 _ (by decide), r20_8]
  have m21_544 : feW n21.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f21 (by decide) (by decide) (by decide) (by decide)).trans m18_544
  have m21_56c : feW n21.mem (R + BitVec.ofNat 32 0x56C) = sqL (Y) := (keepW C f21 (by decide) (by decide) (by decide) (by decide)).trans m18_56c
  have m21_594 : feW n21.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f21 (by decide) (by decide) (by decide) (by decide)).trans m18_594
  have m21_5bc : feW n21.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW C f21 (by decide) (by decide) (by decide) (by decide)).trans m18_5bc
  have m21_4a0 : feW n21.mem (R + BitVec.ofNat 32 0x4A0) = sqL (v) := by rw [w21, r20_11, m18_5bc]
  obtain ⟨n22, c22, D22, v22, k22⟩ := D21.aluImmS C dec_at_130 (off' := 0x132) (by decide) (by decide)
  have r22_18 : reg n22 (18 : Fin 32) = out := by rw [k22 _ (by decide), r21_18]
  have r22_20 : reg n22 (20 : Fin 32) = bp := by rw [k22 _ (by decide), r21_20]
  have r22_8 : reg n22 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k22 _ (by decide), r21_8]
  have r22_10 : reg n22 a0 = R + BitVec.ofNat 32 0x5E4 := by rw [v22, D21.hsp]; exact add_sp R rfl
  obtain ⟨n23, c23, D23, v23, k23⟩ := D22.aluImmS C dec_at_132 (off' := 0x134) (by decide) (by decide)
  have r23_18 : reg n23 (18 : Fin 32) = out := by rw [k23 _ (by decide), r22_18]
  have r23_20 : reg n23 (20 : Fin 32) = bp := by rw [k23 _ (by decide), r22_20]
  have r23_8 : reg n23 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k23 _ (by decide), r22_8]
  have r23_10 : reg n23 a0 = R + BitVec.ofNat 32 0x5E4 := by rw [k23 _ (by decide), r22_10]
  have r23_11 : reg n23 a1 = R + BitVec.ofNat 32 0x4A0 := by rw [v23, D22.hsp]; exact add_sp R rfl
  obtain ⟨n24, c24, D24, v24, k24⟩ := D23.aluImmS C dec_at_134 (off' := 0x136) (by decide) (by decide)
  have r24_18 : reg n24 (18 : Fin 32) = out := by rw [k24 _ (by decide), r23_18]
  have r24_20 : reg n24 (20 : Fin 32) = bp := by rw [k24 _ (by decide), r23_20]
  have r24_8 : reg n24 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k24 _ (by decide), r23_8]
  have r24_10 : reg n24 a0 = R + BitVec.ofNat 32 0x5E4 := by rw [k24 _ (by decide), r23_10]
  have r24_11 : reg n24 a1 = R + BitVec.ofNat 32 0x4A0 := by rw [k24 _ (by decide), r23_11]
  have r24_12 : reg n24 a2 = R + BitVec.ofNat 32 0x5BC := by rw [v24, D23.hsp]; exact add_sp R rfl
  obtain ⟨n25, c25, D25, w25, k25, f25⟩ := D24.mul C dec_at_136 dec_at_13a (by decide) (by decide) (k := 0x5E4) (by decide) (by decide) (by decide) r24_10 (by rw [r24_11]; exact C.opF (by decide) (by decide) (by decide)) (by rw [r24_12]; exact C.opF (by decide) (by decide) (by decide))
  have r25_18 : reg n25 (18 : Fin 32) = out := by rw [k25 _ (by decide), r24_18]
  have r25_20 : reg n25 (20 : Fin 32) = bp := by rw [k25 _ (by decide), r24_20]
  have r25_8 : reg n25 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k25 _ (by decide), r24_8]
  have m25_544 : feW n25.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f25 (by decide) (by decide) (by decide) (by decide)).trans m21_544
  have m25_56c : feW n25.mem (R + BitVec.ofNat 32 0x56C) = sqL (Y) := (keepW C f25 (by decide) (by decide) (by decide) (by decide)).trans m21_56c
  have m25_594 : feW n25.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f25 (by decide) (by decide) (by decide) (by decide)).trans m21_594
  have m25_5bc : feW n25.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW C f25 (by decide) (by decide) (by decide) (by decide)).trans m21_5bc
  have m25_4a0 : feW n25.mem (R + BitVec.ofNat 32 0x4A0) = sqL (v) := (keepW C f25 (by decide) (by decide) (by decide) (by decide)).trans m21_4a0
  have m25_5e4 : feW n25.mem (R + BitVec.ofNat 32 0x5E4) = sqrtV3 v := by rw [w25, r24_11, r24_12, m21_4a0, m21_5bc] <;> rfl
  obtain ⟨n26, c26, D26, v26, k26⟩ := D25.aluImmS C dec_at_13e (off' := 0x140) (by decide) (by decide)
  have r26_18 : reg n26 (18 : Fin 32) = out := by rw [k26 _ (by decide), r25_18]
  have r26_20 : reg n26 (20 : Fin 32) = bp := by rw [k26 _ (by decide), r25_20]
  have r26_8 : reg n26 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k26 _ (by decide), r25_8]
  have r26_10 : reg n26 a0 = R + BitVec.ofNat 32 0x4A0 := by rw [v26, D25.hsp]; exact add_sp R rfl
  obtain ⟨n27, c27, D27, v27, k27⟩ := D26.aluImmS C dec_at_140 (off' := 0x142) (by decide) (by decide)
  have r27_18 : reg n27 (18 : Fin 32) = out := by rw [k27 _ (by decide), r26_18]
  have r27_20 : reg n27 (20 : Fin 32) = bp := by rw [k27 _ (by decide), r26_20]
  have r27_8 : reg n27 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k27 _ (by decide), r26_8]
  have r27_10 : reg n27 a0 = R + BitVec.ofNat 32 0x4A0 := by rw [k27 _ (by decide), r26_10]
  have r27_11 : reg n27 a1 = R + BitVec.ofNat 32 0x5E4 := by rw [v27, D26.hsp]; exact add_sp R rfl
  obtain ⟨n28, c28, D28, w28, k28, f28⟩ := D27.sq C dec_at_142 dec_at_146 (by decide) (by decide) (k := 0x4A0) (by decide) (by decide) (by decide) r27_10 (by rw [r27_11]; exact C.opF (by decide) (by decide) (by decide))
  have r28_18 : reg n28 (18 : Fin 32) = out := by rw [k28 _ (by decide), r27_18]
  have r28_20 : reg n28 (20 : Fin 32) = bp := by rw [k28 _ (by decide), r27_20]
  have r28_8 : reg n28 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k28 _ (by decide), r27_8]
  have m28_544 : feW n28.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f28 (by decide) (by decide) (by decide) (by decide)).trans m25_544
  have m28_56c : feW n28.mem (R + BitVec.ofNat 32 0x56C) = sqL (Y) := (keepW C f28 (by decide) (by decide) (by decide) (by decide)).trans m25_56c
  have m28_594 : feW n28.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f28 (by decide) (by decide) (by decide) (by decide)).trans m25_594
  have m28_5bc : feW n28.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW C f28 (by decide) (by decide) (by decide) (by decide)).trans m25_5bc
  have m28_5e4 : feW n28.mem (R + BitVec.ofNat 32 0x5E4) = sqrtV3 v := (keepW C f28 (by decide) (by decide) (by decide) (by decide)).trans m25_5e4
  have m28_4a0 : feW n28.mem (R + BitVec.ofNat 32 0x4A0) = sqL (sqrtV3 v) := by rw [w28, r27_11, m25_5e4]
  obtain ⟨n29, c29, D29, v29, k29⟩ := D28.aluImmS C dec_at_14a (off' := 0x14C) (by decide) (by decide)
  have r29_18 : reg n29 (18 : Fin 32) = out := by rw [k29 _ (by decide), r28_18]
  have r29_20 : reg n29 (20 : Fin 32) = bp := by rw [k29 _ (by decide), r28_20]
  have r29_8 : reg n29 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k29 _ (by decide), r28_8]
  have r29_10 : reg n29 a0 = R + BitVec.ofNat 32 0x60C := by rw [v29, D28.hsp]; exact add_sp R rfl
  obtain ⟨n30, c30, D30, v30, k30⟩ := D29.aluImmS C dec_at_14c (off' := 0x14E) (by decide) (by decide)
  have r30_18 : reg n30 (18 : Fin 32) = out := by rw [k30 _ (by decide), r29_18]
  have r30_20 : reg n30 (20 : Fin 32) = bp := by rw [k30 _ (by decide), r29_20]
  have r30_8 : reg n30 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k30 _ (by decide), r29_8]
  have r30_10 : reg n30 a0 = R + BitVec.ofNat 32 0x60C := by rw [k30 _ (by decide), r29_10]
  have r30_11 : reg n30 a1 = R + BitVec.ofNat 32 0x4A0 := by rw [v30, D29.hsp]; exact add_sp R rfl
  obtain ⟨n31, c31, D31, v31, k31⟩ := D30.aluImmS C dec_at_14e (off' := 0x150) (by decide) (by decide)
  have r31_18 : reg n31 (18 : Fin 32) = out := by rw [k31 _ (by decide), r30_18]
  have r31_20 : reg n31 (20 : Fin 32) = bp := by rw [k31 _ (by decide), r30_20]
  have r31_8 : reg n31 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k31 _ (by decide), r30_8]
  have r31_10 : reg n31 a0 = R + BitVec.ofNat 32 0x60C := by rw [k31 _ (by decide), r30_10]
  have r31_11 : reg n31 a1 = R + BitVec.ofNat 32 0x4A0 := by rw [k31 _ (by decide), r30_11]
  have r31_12 : reg n31 a2 = R + BitVec.ofNat 32 0x5BC := by rw [v31, D30.hsp]; exact add_sp R rfl
  obtain ⟨n32, c32, D32, w32, k32, f32⟩ := D31.mul C dec_at_150 dec_at_154 (by decide) (by decide) (k := 0x60C) (by decide) (by decide) (by decide) r31_10 (by rw [r31_11]; exact C.opF (by decide) (by decide) (by decide)) (by rw [r31_12]; exact C.opF (by decide) (by decide) (by decide))
  have r32_18 : reg n32 (18 : Fin 32) = out := by rw [k32 _ (by decide), r31_18]
  have r32_20 : reg n32 (20 : Fin 32) = bp := by rw [k32 _ (by decide), r31_20]
  have r32_8 : reg n32 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k32 _ (by decide), r31_8]
  have m32_544 : feW n32.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f32 (by decide) (by decide) (by decide) (by decide)).trans m28_544
  have m32_56c : feW n32.mem (R + BitVec.ofNat 32 0x56C) = sqL (Y) := (keepW C f32 (by decide) (by decide) (by decide) (by decide)).trans m28_56c
  have m32_594 : feW n32.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f32 (by decide) (by decide) (by decide) (by decide)).trans m28_594
  have m32_5bc : feW n32.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW C f32 (by decide) (by decide) (by decide) (by decide)).trans m28_5bc
  have m32_5e4 : feW n32.mem (R + BitVec.ofNat 32 0x5E4) = sqrtV3 v := (keepW C f32 (by decide) (by decide) (by decide) (by decide)).trans m28_5e4
  have m32_4a0 : feW n32.mem (R + BitVec.ofNat 32 0x4A0) = sqL (sqrtV3 v) := (keepW C f32 (by decide) (by decide) (by decide) (by decide)).trans m28_4a0
  have m32_60c : feW n32.mem (R + BitVec.ofNat 32 0x60C) = sqrtV7 v := by rw [w32, r31_11, r31_12, m28_4a0, m28_5bc] <;> rfl
  obtain ⟨n33, c33, D33, v33, k33⟩ := D32.aluImmS C dec_at_158 (off' := 0x15A) (by decide) (by decide)
  have r33_18 : reg n33 (18 : Fin 32) = out := by rw [k33 _ (by decide), r32_18]
  have r33_20 : reg n33 (20 : Fin 32) = bp := by rw [k33 _ (by decide), r32_20]
  have r33_8 : reg n33 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k33 _ (by decide), r32_8]
  have r33_10 : reg n33 a0 = R + BitVec.ofNat 32 0x634 := by rw [v33, D32.hsp]; exact add_sp R rfl
  obtain ⟨n34, c34, D34, v34, k34⟩ := D33.aluImmS C dec_at_15a (off' := 0x15C) (by decide) (by decide)
  have r34_18 : reg n34 (18 : Fin 32) = out := by rw [k34 _ (by decide), r33_18]
  have r34_20 : reg n34 (20 : Fin 32) = bp := by rw [k34 _ (by decide), r33_20]
  have r34_8 : reg n34 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k34 _ (by decide), r33_8]
  have r34_10 : reg n34 a0 = R + BitVec.ofNat 32 0x634 := by rw [k34 _ (by decide), r33_10]
  have r34_11 : reg n34 a1 = R + BitVec.ofNat 32 0x594 := by rw [v34, D33.hsp]; exact add_sp R rfl
  obtain ⟨n35, c35, D35, v35, k35⟩ := D34.aluImmS C dec_at_15c (off' := 0x15E) (by decide) (by decide)
  have r35_18 : reg n35 (18 : Fin 32) = out := by rw [k35 _ (by decide), r34_18]
  have r35_20 : reg n35 (20 : Fin 32) = bp := by rw [k35 _ (by decide), r34_20]
  have r35_8 : reg n35 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k35 _ (by decide), r34_8]
  have r35_10 : reg n35 a0 = R + BitVec.ofNat 32 0x634 := by rw [k35 _ (by decide), r34_10]
  have r35_11 : reg n35 a1 = R + BitVec.ofNat 32 0x594 := by rw [k35 _ (by decide), r34_11]
  have r35_12 : reg n35 a2 = R + BitVec.ofNat 32 0x5E4 := by rw [v35, D34.hsp]; exact add_sp R rfl
  obtain ⟨n36, c36, D36, w36, k36, f36⟩ := D35.mul C dec_at_15e dec_at_162 (by decide) (by decide) (k := 0x634) (by decide) (by decide) (by decide) r35_10 (by rw [r35_11]; exact C.opF (by decide) (by decide) (by decide)) (by rw [r35_12]; exact C.opF (by decide) (by decide) (by decide))
  have r36_18 : reg n36 (18 : Fin 32) = out := by rw [k36 _ (by decide), r35_18]
  have r36_20 : reg n36 (20 : Fin 32) = bp := by rw [k36 _ (by decide), r35_20]
  have r36_8 : reg n36 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k36 _ (by decide), r35_8]
  have m36_544 : feW n36.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f36 (by decide) (by decide) (by decide) (by decide)).trans m32_544
  have m36_56c : feW n36.mem (R + BitVec.ofNat 32 0x56C) = sqL (Y) := (keepW C f36 (by decide) (by decide) (by decide) (by decide)).trans m32_56c
  have m36_594 : feW n36.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f36 (by decide) (by decide) (by decide) (by decide)).trans m32_594
  have m36_5bc : feW n36.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW C f36 (by decide) (by decide) (by decide) (by decide)).trans m32_5bc
  have m36_5e4 : feW n36.mem (R + BitVec.ofNat 32 0x5E4) = sqrtV3 v := (keepW C f36 (by decide) (by decide) (by decide) (by decide)).trans m32_5e4
  have m36_4a0 : feW n36.mem (R + BitVec.ofNat 32 0x4A0) = sqL (sqrtV3 v) := (keepW C f36 (by decide) (by decide) (by decide) (by decide)).trans m32_4a0
  have m36_60c : feW n36.mem (R + BitVec.ofNat 32 0x60C) = sqrtV7 v := (keepW C f36 (by decide) (by decide) (by decide) (by decide)).trans m32_60c
  have m36_634 : feW n36.mem (R + BitVec.ofNat 32 0x634) = mulL u (sqrtV3 v) := by rw [w36, r35_11, r35_12, m32_594, m32_5e4] <;> rfl
  obtain ⟨n37, c37, D37, v37, k37⟩ := D36.aluImmS C dec_at_166 (off' := 0x168) (by decide) (by decide)
  have r37_18 : reg n37 (18 : Fin 32) = out := by rw [k37 _ (by decide), r36_18]
  have r37_20 : reg n37 (20 : Fin 32) = bp := by rw [k37 _ (by decide), r36_20]
  have r37_8 : reg n37 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k37 _ (by decide), r36_8]
  have r37_10 : reg n37 a0 = R + BitVec.ofNat 32 0x684 := by rw [v37, D36.hsp]; exact add_sp R rfl
  obtain ⟨n38, c38, D38, v38, k38⟩ := D37.aluImmS C dec_at_168 (off' := 0x16A) (by decide) (by decide)
  have r38_18 : reg n38 (18 : Fin 32) = out := by rw [k38 _ (by decide), r37_18]
  have r38_20 : reg n38 (20 : Fin 32) = bp := by rw [k38 _ (by decide), r37_20]
  have r38_8 : reg n38 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k38 _ (by decide), r37_8]
  have r38_10 : reg n38 a0 = R + BitVec.ofNat 32 0x684 := by rw [k38 _ (by decide), r37_10]
  have r38_11 : reg n38 a1 = R + BitVec.ofNat 32 0x594 := by rw [v38, D37.hsp]; exact add_sp R rfl
  obtain ⟨n39, c39, D39, v39, k39⟩ := D38.aluImmS C dec_at_16a (off' := 0x16C) (by decide) (by decide)
  have r39_18 : reg n39 (18 : Fin 32) = out := by rw [k39 _ (by decide), r38_18]
  have r39_20 : reg n39 (20 : Fin 32) = bp := by rw [k39 _ (by decide), r38_20]
  have r39_8 : reg n39 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k39 _ (by decide), r38_8]
  have r39_10 : reg n39 a0 = R + BitVec.ofNat 32 0x684 := by rw [k39 _ (by decide), r38_10]
  have r39_11 : reg n39 a1 = R + BitVec.ofNat 32 0x594 := by rw [k39 _ (by decide), r38_11]
  have r39_12 : reg n39 a2 = R + BitVec.ofNat 32 0x60C := by rw [v39, D38.hsp]; exact add_sp R rfl
  obtain ⟨n40, c40, D40, w40, k40, f40⟩ := D39.mul C dec_at_16c dec_at_170 (by decide) (by decide) (k := 0x684) (by decide) (by decide) (by decide) r39_10 (by rw [r39_11]; exact C.opF (by decide) (by decide) (by decide)) (by rw [r39_12]; exact C.opF (by decide) (by decide) (by decide))
  have r40_18 : reg n40 (18 : Fin 32) = out := by rw [k40 _ (by decide), r39_18]
  have r40_20 : reg n40 (20 : Fin 32) = bp := by rw [k40 _ (by decide), r39_20]
  have r40_8 : reg n40 (8 : Fin 32) = BitVec.ofNat 32 edOneAddress := by rw [k40 _ (by decide), r39_8]
  have m40_544 : feW n40.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f40 (by decide) (by decide) (by decide) (by decide)).trans m36_544
  have m40_56c : feW n40.mem (R + BitVec.ofNat 32 0x56C) = sqL (Y) := (keepW C f40 (by decide) (by decide) (by decide) (by decide)).trans m36_56c
  have m40_594 : feW n40.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f40 (by decide) (by decide) (by decide) (by decide)).trans m36_594
  have m40_5bc : feW n40.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW C f40 (by decide) (by decide) (by decide) (by decide)).trans m36_5bc
  have m40_5e4 : feW n40.mem (R + BitVec.ofNat 32 0x5E4) = sqrtV3 v := (keepW C f40 (by decide) (by decide) (by decide) (by decide)).trans m36_5e4
  have m40_4a0 : feW n40.mem (R + BitVec.ofNat 32 0x4A0) = sqL (sqrtV3 v) := (keepW C f40 (by decide) (by decide) (by decide) (by decide)).trans m36_4a0
  have m40_60c : feW n40.mem (R + BitVec.ofNat 32 0x60C) = sqrtV7 v := (keepW C f40 (by decide) (by decide) (by decide) (by decide)).trans m36_60c
  have m40_634 : feW n40.mem (R + BitVec.ofNat 32 0x634) = mulL u (sqrtV3 v) := (keepW C f40 (by decide) (by decide) (by decide) (by decide)).trans m36_634
  have m40_684 : feW n40.mem (R + BitVec.ofNat 32 0x684) = mulL u (sqrtV7 v) := by rw [w40, r39_11, r39_12, m36_594, m36_60c] <;> rfl
  exact ⟨n40, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans (c11.trans (c12.trans (c13.trans (c14.trans (c15.trans (c16.trans (c17.trans (c18.trans (c19.trans (c20.trans (c21.trans (c22.trans (c23.trans (c24.trans (c25.trans (c26.trans (c27.trans (c28.trans (c29.trans (c30.trans (c31.trans (c32.trans (c33.trans (c34.trans (c35.trans (c36.trans (c37.trans (c38.trans (c39.trans (c40))))))))))))))))))))))))))))))))))))))), D40, r40_18, r40_20, m40_544, m40_594, m40_5bc, m40_634, m40_684⟩


set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- From offset 0x174 to 0x270: the rest of `sqrt_ratio_i`. The root `r` is
`u v³ (u v⁷)^((p-5)/8)`, `chk` is `v r²`, and the result is `|r|` or
`|r √-1|`, with `a0` set when `u / v` is a square. -/
theorem dec_ph3 (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm 0x174) {out bp : Word}
    {Y u v uv3 uv7 rr chk sm : List Nat}
    (hs2 : reg nm (18 : Fin 32) = out) (hs4 : reg nm (20 : Fin 32) = bp)
    (hY : feW M (R + BitVec.ofNat 32 0x544) = Y) (hu : feW M (R + BitVec.ofNat 32 0x594) = u)
    (hv : feW M (R + BitVec.ofNat 32 0x5BC) = v) (h3 : feW M (R + BitVec.ofNat 32 0x634) = uv3)
    (h7 : feW M (R + BitVec.ofNat 32 0x684) = uv7)
    (sS : Sep (BitVec.ofNat 32 edSqrtM1Address) 40 R 0x6F0) (hS : feW M0 (BitVec.ofNat 32 edSqrtM1Address) = sm)
    (hrr : rr = mulL uv3 (mulL uv7 (sqIter 2 (pw19L uv7)))) (hchk : chk = mulL v (sqL rr)) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' 0x270 ∧ reg nm' (18 : Fin 32) = out ∧
      reg nm' (20 : Fin 32) = bp ∧
      reg nm' a0 = bw ((feEqL (chk) (negL (u))) || (feEqL (chk) (u))) ∧
      feW nm'.mem (R + BitVec.ofNat 32 0x544) = Y ∧
      feW nm'.mem (R + BitVec.ofNat 32 0x6AC) = condNegL ((if (feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u))) then mulL (sm) (rr) else rr)) (isNegL ((if (feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u))) then mulL (sm) (rr) else rr))) := by
  obtain ⟨n1, c1, D1, v1, k1⟩ := D.aluImmS C dec_at_174 (off' := 0x176) (by decide) (by decide)
  have r1_18 : reg n1 (18 : Fin 32) = out := by rw [k1 _ (by decide), hs2]
  have r1_20 : reg n1 (20 : Fin 32) = bp := by rw [k1 _ (by decide), hs4]
  have r1_10 : reg n1 a0 = R + BitVec.ofNat 32 0x4A0 := by rw [v1, D.hsp]; exact add_sp R rfl
  obtain ⟨n2, c2, D2, v2, k2⟩ := D1.aluImmS C dec_at_176 (off' := 0x178) (by decide) (by decide)
  have r2_18 : reg n2 (18 : Fin 32) = out := by rw [k2 _ (by decide), r1_18]
  have r2_20 : reg n2 (20 : Fin 32) = bp := by rw [k2 _ (by decide), r1_20]
  have r2_10 : reg n2 a0 = R + BitVec.ofNat 32 0x4A0 := by rw [k2 _ (by decide), r1_10]
  have r2_11 : reg n2 a1 = R + BitVec.ofNat 32 0x684 := by rw [v2, D1.hsp]; exact add_sp R rfl
  obtain ⟨n3, c3, D3, w3, k3, f3⟩ := D2.pow22501 C dec_at_178 dec_at_17c (by decide) (by decide) (k := 0x4A0) (by decide) (by decide) (by decide) r2_10 (by rw [r2_11]; exact C.opF (by decide) (by decide) (by decide)) (by rw [r2_11]; exact C.offs (by decide) (by decide) (by decide))
  have r3_18 : reg n3 (18 : Fin 32) = out := by rw [k3 _ (by decide), r2_18]
  have r3_20 : reg n3 (20 : Fin 32) = bp := by rw [k3 _ (by decide), r2_20]
  have m3_544 : feW n3.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f3 (by decide) (by decide) (by decide) (by decide)).trans hY
  have m3_594 : feW n3.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f3 (by decide) (by decide) (by decide) (by decide)).trans hu
  have m3_5bc : feW n3.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW C f3 (by decide) (by decide) (by decide) (by decide)).trans hv
  have m3_634 : feW n3.mem (R + BitVec.ofNat 32 0x634) = uv3 := (keepW C f3 (by decide) (by decide) (by decide) (by decide)).trans h3
  have m3_684 : feW n3.mem (R + BitVec.ofNat 32 0x684) = uv7 := (keepW C f3 (by decide) (by decide) (by decide) (by decide)).trans h7
  have m3_4a0 : feW n3.mem (R + BitVec.ofNat 32 0x4A0) = pw19L (uv7) := by rw [w3, r2_11, h7]
  obtain ⟨n4, c4, D4, v4, k4⟩ := D3.aluImmS C dec_at_180 (off' := 0x182) (by decide) (by decide)
  have r4_18 : reg n4 (18 : Fin 32) = out := by rw [k4 _ (by decide), r3_18]
  have r4_20 : reg n4 (20 : Fin 32) = bp := by rw [k4 _ (by decide), r3_20]
  have r4_10 : reg n4 a0 = R + BitVec.ofNat 32 0x6AC := by rw [v4, D3.hsp]; exact add_sp R rfl
  obtain ⟨n5, c5, D5, v5, k5⟩ := D4.aluImmS C dec_at_182 (off' := 0x184) (by decide) (by decide)
  have r5_18 : reg n5 (18 : Fin 32) = out := by rw [k5 _ (by decide), r4_18]
  have r5_20 : reg n5 (20 : Fin 32) = bp := by rw [k5 _ (by decide), r4_20]
  have r5_10 : reg n5 a0 = R + BitVec.ofNat 32 0x6AC := by rw [k5 _ (by decide), r4_10]
  have r5_11 : reg n5 a1 = R + BitVec.ofNat 32 0x4A0 := by rw [v5, D4.hsp]; exact add_sp R rfl
  obtain ⟨n6, c6, D6, v6, k6⟩ := D5.aluImmS C dec_at_184 (off' := 0x186) (by decide) (by decide)
  have r6_18 : reg n6 (18 : Fin 32) = out := by rw [k6 _ (by decide), r5_18]
  have r6_20 : reg n6 (20 : Fin 32) = bp := by rw [k6 _ (by decide), r5_20]
  have r6_10 : reg n6 a0 = R + BitVec.ofNat 32 0x6AC := by rw [k6 _ (by decide), r5_10]
  have r6_11 : reg n6 a1 = R + BitVec.ofNat 32 0x4A0 := by rw [k6 _ (by decide), r5_11]
  have r6_12 : reg n6 a2 = BitVec.ofNat 32 2 := by rw [v6, D5.zero]; rfl
  obtain ⟨n7, c7, D7, w7, k7, f7⟩ := D6.pow2k C dec_at_186 dec_at_18a (by decide) (by decide) (e := 2) (by decide) (by decide) (k := 0x6AC) (by decide) (by decide) (by decide) r6_10 (by rw [r6_11]; exact C.opF (by decide) (by decide) (by decide)) r6_12
  have r7_18 : reg n7 (18 : Fin 32) = out := by rw [k7 _ (by decide), r6_18]
  have r7_20 : reg n7 (20 : Fin 32) = bp := by rw [k7 _ (by decide), r6_20]
  have m7_544 : feW n7.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f7 (by decide) (by decide) (by decide) (by decide)).trans m3_544
  have m7_594 : feW n7.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f7 (by decide) (by decide) (by decide) (by decide)).trans m3_594
  have m7_5bc : feW n7.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW C f7 (by decide) (by decide) (by decide) (by decide)).trans m3_5bc
  have m7_634 : feW n7.mem (R + BitVec.ofNat 32 0x634) = uv3 := (keepW C f7 (by decide) (by decide) (by decide) (by decide)).trans m3_634
  have m7_684 : feW n7.mem (R + BitVec.ofNat 32 0x684) = uv7 := (keepW C f7 (by decide) (by decide) (by decide) (by decide)).trans m3_684
  have m7_4a0 : feW n7.mem (R + BitVec.ofNat 32 0x4A0) = pw19L (uv7) := (keepW C f7 (by decide) (by decide) (by decide) (by decide)).trans m3_4a0
  have m7_6ac : feW n7.mem (R + BitVec.ofNat 32 0x6AC) = sqIter 2 (pw19L (uv7)) := by rw [w7, r6_11, m3_4a0]
  obtain ⟨n8, c8, D8, v8, k8⟩ := D7.aluImmS C dec_at_18e (off' := 0x190) (by decide) (by decide)
  have r8_18 : reg n8 (18 : Fin 32) = out := by rw [k8 _ (by decide), r7_18]
  have r8_20 : reg n8 (20 : Fin 32) = bp := by rw [k8 _ (by decide), r7_20]
  have r8_10 : reg n8 a0 = R + BitVec.ofNat 32 0x65C := by rw [v8, D7.hsp]; exact add_sp R rfl
  obtain ⟨n9, c9, D9, v9, k9⟩ := D8.aluImmS C dec_at_190 (off' := 0x192) (by decide) (by decide)
  have r9_18 : reg n9 (18 : Fin 32) = out := by rw [k9 _ (by decide), r8_18]
  have r9_20 : reg n9 (20 : Fin 32) = bp := by rw [k9 _ (by decide), r8_20]
  have r9_10 : reg n9 a0 = R + BitVec.ofNat 32 0x65C := by rw [k9 _ (by decide), r8_10]
  have r9_11 : reg n9 a1 = R + BitVec.ofNat 32 0x684 := by rw [v9, D8.hsp]; exact add_sp R rfl
  obtain ⟨n10, c10, D10, v10, k10⟩ := D9.aluImmS C dec_at_192 (off' := 0x194) (by decide) (by decide)
  have r10_18 : reg n10 (18 : Fin 32) = out := by rw [k10 _ (by decide), r9_18]
  have r10_20 : reg n10 (20 : Fin 32) = bp := by rw [k10 _ (by decide), r9_20]
  have r10_10 : reg n10 a0 = R + BitVec.ofNat 32 0x65C := by rw [k10 _ (by decide), r9_10]
  have r10_11 : reg n10 a1 = R + BitVec.ofNat 32 0x684 := by rw [k10 _ (by decide), r9_11]
  have r10_12 : reg n10 a2 = R + BitVec.ofNat 32 0x6AC := by rw [v10, D9.hsp]; exact add_sp R rfl
  obtain ⟨n11, c11, D11, w11, k11, f11⟩ := D10.mul C dec_at_194 dec_at_198 (by decide) (by decide) (k := 0x65C) (by decide) (by decide) (by decide) r10_10 (by rw [r10_11]; exact C.opF (by decide) (by decide) (by decide)) (by rw [r10_12]; exact C.opF (by decide) (by decide) (by decide))
  have r11_18 : reg n11 (18 : Fin 32) = out := by rw [k11 _ (by decide), r10_18]
  have r11_20 : reg n11 (20 : Fin 32) = bp := by rw [k11 _ (by decide), r10_20]
  have m11_544 : feW n11.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f11 (by decide) (by decide) (by decide) (by decide)).trans m7_544
  have m11_594 : feW n11.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f11 (by decide) (by decide) (by decide) (by decide)).trans m7_594
  have m11_5bc : feW n11.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW C f11 (by decide) (by decide) (by decide) (by decide)).trans m7_5bc
  have m11_634 : feW n11.mem (R + BitVec.ofNat 32 0x634) = uv3 := (keepW C f11 (by decide) (by decide) (by decide) (by decide)).trans m7_634
  have m11_684 : feW n11.mem (R + BitVec.ofNat 32 0x684) = uv7 := (keepW C f11 (by decide) (by decide) (by decide) (by decide)).trans m7_684
  have m11_4a0 : feW n11.mem (R + BitVec.ofNat 32 0x4A0) = pw19L (uv7) := (keepW C f11 (by decide) (by decide) (by decide) (by decide)).trans m7_4a0
  have m11_6ac : feW n11.mem (R + BitVec.ofNat 32 0x6AC) = sqIter 2 (pw19L (uv7)) := (keepW C f11 (by decide) (by decide) (by decide) (by decide)).trans m7_6ac
  have m11_65c : feW n11.mem (R + BitVec.ofNat 32 0x65C) = mulL (uv7) (sqIter 2 (pw19L (uv7))) := by rw [w11, r10_11, r10_12, m7_684, m7_6ac]
  obtain ⟨n12, c12, D12, v12, k12⟩ := D11.aluImmS C dec_at_19c (off' := 0x19E) (by decide) (by decide)
  have r12_18 : reg n12 (18 : Fin 32) = out := by rw [k12 _ (by decide), r11_18]
  have r12_20 : reg n12 (20 : Fin 32) = bp := by rw [k12 _ (by decide), r11_20]
  have r12_10 : reg n12 a0 = R + BitVec.ofNat 32 0x6AC := by rw [v12, D11.hsp]; exact add_sp R rfl
  obtain ⟨n13, c13, D13, v13, k13⟩ := D12.aluImmS C dec_at_19e (off' := 0x1A0) (by decide) (by decide)
  have r13_18 : reg n13 (18 : Fin 32) = out := by rw [k13 _ (by decide), r12_18]
  have r13_20 : reg n13 (20 : Fin 32) = bp := by rw [k13 _ (by decide), r12_20]
  have r13_10 : reg n13 a0 = R + BitVec.ofNat 32 0x6AC := by rw [k13 _ (by decide), r12_10]
  have r13_11 : reg n13 a1 = R + BitVec.ofNat 32 0x634 := by rw [v13, D12.hsp]; exact add_sp R rfl
  obtain ⟨n14, c14, D14, v14, k14⟩ := D13.aluImmS C dec_at_1a0 (off' := 0x1A2) (by decide) (by decide)
  have r14_18 : reg n14 (18 : Fin 32) = out := by rw [k14 _ (by decide), r13_18]
  have r14_20 : reg n14 (20 : Fin 32) = bp := by rw [k14 _ (by decide), r13_20]
  have r14_10 : reg n14 a0 = R + BitVec.ofNat 32 0x6AC := by rw [k14 _ (by decide), r13_10]
  have r14_11 : reg n14 a1 = R + BitVec.ofNat 32 0x634 := by rw [k14 _ (by decide), r13_11]
  have r14_12 : reg n14 a2 = R + BitVec.ofNat 32 0x65C := by rw [v14, D13.hsp]; exact add_sp R rfl
  obtain ⟨n15, c15, D15, w15, k15, f15⟩ := D14.mul C dec_at_1a2 dec_at_1a6 (by decide) (by decide) (k := 0x6AC) (by decide) (by decide) (by decide) r14_10 (by rw [r14_11]; exact C.opF (by decide) (by decide) (by decide)) (by rw [r14_12]; exact C.opF (by decide) (by decide) (by decide))
  have r15_18 : reg n15 (18 : Fin 32) = out := by rw [k15 _ (by decide), r14_18]
  have r15_20 : reg n15 (20 : Fin 32) = bp := by rw [k15 _ (by decide), r14_20]
  have m15_544 : feW n15.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f15 (by decide) (by decide) (by decide) (by decide)).trans m11_544
  have m15_594 : feW n15.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f15 (by decide) (by decide) (by decide) (by decide)).trans m11_594
  have m15_5bc : feW n15.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW C f15 (by decide) (by decide) (by decide) (by decide)).trans m11_5bc
  have m15_634 : feW n15.mem (R + BitVec.ofNat 32 0x634) = uv3 := (keepW C f15 (by decide) (by decide) (by decide) (by decide)).trans m11_634
  have m15_684 : feW n15.mem (R + BitVec.ofNat 32 0x684) = uv7 := (keepW C f15 (by decide) (by decide) (by decide) (by decide)).trans m11_684
  have m15_4a0 : feW n15.mem (R + BitVec.ofNat 32 0x4A0) = pw19L (uv7) := (keepW C f15 (by decide) (by decide) (by decide) (by decide)).trans m11_4a0
  have m15_65c : feW n15.mem (R + BitVec.ofNat 32 0x65C) = mulL (uv7) (sqIter 2 (pw19L (uv7))) := (keepW C f15 (by decide) (by decide) (by decide) (by decide)).trans m11_65c
  have m15_6ac : feW n15.mem (R + BitVec.ofNat 32 0x6AC) = rr := by rw [w15, r14_11, r14_12, m11_634, m11_65c, hrr]
  obtain ⟨n16, c16, D16, v16, k16⟩ := D15.aluImmS C dec_at_1aa (off' := 0x1AC) (by decide) (by decide)
  have r16_18 : reg n16 (18 : Fin 32) = out := by rw [k16 _ (by decide), r15_18]
  have r16_20 : reg n16 (20 : Fin 32) = bp := by rw [k16 _ (by decide), r15_20]
  have r16_10 : reg n16 a0 = R + BitVec.ofNat 32 0x4A0 := by rw [v16, D15.hsp]; exact add_sp R rfl
  obtain ⟨n17, c17, D17, v17, k17⟩ := D16.aluImmS C dec_at_1ac (off' := 0x1AE) (by decide) (by decide)
  have r17_18 : reg n17 (18 : Fin 32) = out := by rw [k17 _ (by decide), r16_18]
  have r17_20 : reg n17 (20 : Fin 32) = bp := by rw [k17 _ (by decide), r16_20]
  have r17_10 : reg n17 a0 = R + BitVec.ofNat 32 0x4A0 := by rw [k17 _ (by decide), r16_10]
  have r17_11 : reg n17 a1 = R + BitVec.ofNat 32 0x6AC := by rw [v17, D16.hsp]; exact add_sp R rfl
  obtain ⟨n18, c18, D18, w18, k18, f18⟩ := D17.sq C dec_at_1ae dec_at_1b2 (by decide) (by decide) (k := 0x4A0) (by decide) (by decide) (by decide) r17_10 (by rw [r17_11]; exact C.opF (by decide) (by decide) (by decide))
  have r18_18 : reg n18 (18 : Fin 32) = out := by rw [k18 _ (by decide), r17_18]
  have r18_20 : reg n18 (20 : Fin 32) = bp := by rw [k18 _ (by decide), r17_20]
  have m18_544 : feW n18.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f18 (by decide) (by decide) (by decide) (by decide)).trans m15_544
  have m18_594 : feW n18.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f18 (by decide) (by decide) (by decide) (by decide)).trans m15_594
  have m18_5bc : feW n18.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW C f18 (by decide) (by decide) (by decide) (by decide)).trans m15_5bc
  have m18_634 : feW n18.mem (R + BitVec.ofNat 32 0x634) = uv3 := (keepW C f18 (by decide) (by decide) (by decide) (by decide)).trans m15_634
  have m18_684 : feW n18.mem (R + BitVec.ofNat 32 0x684) = uv7 := (keepW C f18 (by decide) (by decide) (by decide) (by decide)).trans m15_684
  have m18_65c : feW n18.mem (R + BitVec.ofNat 32 0x65C) = mulL (uv7) (sqIter 2 (pw19L (uv7))) := (keepW C f18 (by decide) (by decide) (by decide) (by decide)).trans m15_65c
  have m18_6ac : feW n18.mem (R + BitVec.ofNat 32 0x6AC) = rr := (keepW C f18 (by decide) (by decide) (by decide) (by decide)).trans m15_6ac
  have m18_4a0 : feW n18.mem (R + BitVec.ofNat 32 0x4A0) = sqL (rr) := by rw [w18, r17_11, m15_6ac]
  obtain ⟨n19, c19, D19, v19, k19⟩ := D18.aluImmS C dec_at_1b6 (off' := 0x1B8) (by decide) (by decide)
  have r19_18 : reg n19 (18 : Fin 32) = out := by rw [k19 _ (by decide), r18_18]
  have r19_20 : reg n19 (20 : Fin 32) = bp := by rw [k19 _ (by decide), r18_20]
  have r19_10 : reg n19 a0 = R + BitVec.ofNat 32 0x65C := by rw [v19, D18.hsp]; exact add_sp R rfl
  obtain ⟨n20, c20, D20, v20, k20⟩ := D19.aluImmS C dec_at_1b8 (off' := 0x1BA) (by decide) (by decide)
  have r20_18 : reg n20 (18 : Fin 32) = out := by rw [k20 _ (by decide), r19_18]
  have r20_20 : reg n20 (20 : Fin 32) = bp := by rw [k20 _ (by decide), r19_20]
  have r20_10 : reg n20 a0 = R + BitVec.ofNat 32 0x65C := by rw [k20 _ (by decide), r19_10]
  have r20_11 : reg n20 a1 = R + BitVec.ofNat 32 0x5BC := by rw [v20, D19.hsp]; exact add_sp R rfl
  obtain ⟨n21, c21, D21, v21, k21⟩ := D20.aluImmS C dec_at_1ba (off' := 0x1BC) (by decide) (by decide)
  have r21_18 : reg n21 (18 : Fin 32) = out := by rw [k21 _ (by decide), r20_18]
  have r21_20 : reg n21 (20 : Fin 32) = bp := by rw [k21 _ (by decide), r20_20]
  have r21_10 : reg n21 a0 = R + BitVec.ofNat 32 0x65C := by rw [k21 _ (by decide), r20_10]
  have r21_11 : reg n21 a1 = R + BitVec.ofNat 32 0x5BC := by rw [k21 _ (by decide), r20_11]
  have r21_12 : reg n21 a2 = R + BitVec.ofNat 32 0x4A0 := by rw [v21, D20.hsp]; exact add_sp R rfl
  obtain ⟨n22, c22, D22, w22, k22, f22⟩ := D21.mul C dec_at_1bc dec_at_1c0 (by decide) (by decide) (k := 0x65C) (by decide) (by decide) (by decide) r21_10 (by rw [r21_11]; exact C.opF (by decide) (by decide) (by decide)) (by rw [r21_12]; exact C.opF (by decide) (by decide) (by decide))
  have r22_18 : reg n22 (18 : Fin 32) = out := by rw [k22 _ (by decide), r21_18]
  have r22_20 : reg n22 (20 : Fin 32) = bp := by rw [k22 _ (by decide), r21_20]
  have m22_544 : feW n22.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f22 (by decide) (by decide) (by decide) (by decide)).trans m18_544
  have m22_594 : feW n22.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f22 (by decide) (by decide) (by decide) (by decide)).trans m18_594
  have m22_5bc : feW n22.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW C f22 (by decide) (by decide) (by decide) (by decide)).trans m18_5bc
  have m22_634 : feW n22.mem (R + BitVec.ofNat 32 0x634) = uv3 := (keepW C f22 (by decide) (by decide) (by decide) (by decide)).trans m18_634
  have m22_684 : feW n22.mem (R + BitVec.ofNat 32 0x684) = uv7 := (keepW C f22 (by decide) (by decide) (by decide) (by decide)).trans m18_684
  have m22_6ac : feW n22.mem (R + BitVec.ofNat 32 0x6AC) = rr := (keepW C f22 (by decide) (by decide) (by decide) (by decide)).trans m18_6ac
  have m22_4a0 : feW n22.mem (R + BitVec.ofNat 32 0x4A0) = sqL (rr) := (keepW C f22 (by decide) (by decide) (by decide) (by decide)).trans m18_4a0
  have m22_65c : feW n22.mem (R + BitVec.ofNat 32 0x65C) = chk := by rw [w22, r21_11, r21_12, m18_5bc, m18_4a0, hchk]
  obtain ⟨n23, c23, D23, v23, k23⟩ := D22.aluImmS C dec_at_1c4 (off' := 0x1C6) (by decide) (by decide)
  have r23_18 : reg n23 (18 : Fin 32) = out := by rw [k23 _ (by decide), r22_18]
  have r23_20 : reg n23 (20 : Fin 32) = bp := by rw [k23 _ (by decide), r22_20]
  have r23_10 : reg n23 a0 = R + BitVec.ofNat 32 0x65C := by rw [v23, D22.hsp]; exact add_sp R rfl
  obtain ⟨n24, c24, D24, v24, k24⟩ := D23.aluImmS C dec_at_1c6 (off' := 0x1C8) (by decide) (by decide)
  have r24_18 : reg n24 (18 : Fin 32) = out := by rw [k24 _ (by decide), r23_18]
  have r24_20 : reg n24 (20 : Fin 32) = bp := by rw [k24 _ (by decide), r23_20]
  have r24_10 : reg n24 a0 = R + BitVec.ofNat 32 0x65C := by rw [k24 _ (by decide), r23_10]
  have r24_11 : reg n24 a1 = R + BitVec.ofNat 32 0x594 := by rw [v24, D23.hsp]; exact add_sp R rfl
  obtain ⟨n25, c25, D25, w25, k25, f25⟩ := D24.ctEq C dec_at_1c8 dec_at_1cc (by decide) (by decide) (by rw [r24_10]; exact C.opF (by decide) (by decide) (by decide)) (by rw [r24_11]; exact C.opF (by decide) (by decide) (by decide))
  have r25_18 : reg n25 (18 : Fin 32) = out := by rw [k25 _ (by decide), r24_18]
  have r25_20 : reg n25 (20 : Fin 32) = bp := by rw [k25 _ (by decide), r24_20]
  have m25_544 : feW n25.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW0 C f25 (by decide) (by decide)).trans m22_544
  have m25_594 : feW n25.mem (R + BitVec.ofNat 32 0x594) = u := (keepW0 C f25 (by decide) (by decide)).trans m22_594
  have m25_5bc : feW n25.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW0 C f25 (by decide) (by decide)).trans m22_5bc
  have m25_634 : feW n25.mem (R + BitVec.ofNat 32 0x634) = uv3 := (keepW0 C f25 (by decide) (by decide)).trans m22_634
  have m25_684 : feW n25.mem (R + BitVec.ofNat 32 0x684) = uv7 := (keepW0 C f25 (by decide) (by decide)).trans m22_684
  have m25_6ac : feW n25.mem (R + BitVec.ofNat 32 0x6AC) = rr := (keepW0 C f25 (by decide) (by decide)).trans m22_6ac
  have m25_4a0 : feW n25.mem (R + BitVec.ofNat 32 0x4A0) = sqL (rr) := (keepW0 C f25 (by decide) (by decide)).trans m22_4a0
  have m25_65c : feW n25.mem (R + BitVec.ofNat 32 0x65C) = chk := (keepW0 C f25 (by decide) (by decide)).trans m22_65c
  have r25_10 : reg n25 a0 = bw (feEqL (chk) (u)) := by rw [w25, r24_10, r24_11, m22_65c, m22_594, bw_ct]
  obtain ⟨n26, c26, D26, v26, k26⟩ := D25.aluS C dec_at_1d0 (off' := 0x1D2) (by decide) (by decide)
  have r26_18 : reg n26 (18 : Fin 32) = out := by rw [k26 _ (by decide), r25_18]
  have r26_20 : reg n26 (20 : Fin 32) = bp := by rw [k26 _ (by decide), r25_20]
  have r26_10 : reg n26 a0 = bw (feEqL (chk) (u)) := by rw [k26 _ (by decide), r25_10]
  have r26_19 : reg n26 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [v26, D25.zero, r25_10]; exact BitVec.zero_add _
  obtain ⟨n27, c27, D27, v27, k27⟩ := D26.aluImmS C dec_at_1d2 (off' := 0x1D4) (by decide) (by decide)
  have r27_18 : reg n27 (18 : Fin 32) = out := by rw [k27 _ (by decide), r26_18]
  have r27_20 : reg n27 (20 : Fin 32) = bp := by rw [k27 _ (by decide), r26_20]
  have r27_19 : reg n27 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k27 _ (by decide), r26_19]
  have r27_10 : reg n27 a0 = R + BitVec.ofNat 32 0x4A0 := by rw [v27, D26.hsp]; exact add_sp R rfl
  obtain ⟨n28, c28, D28, v28, k28⟩ := D27.aluImmS C dec_at_1d4 (off' := 0x1D6) (by decide) (by decide)
  have r28_18 : reg n28 (18 : Fin 32) = out := by rw [k28 _ (by decide), r27_18]
  have r28_20 : reg n28 (20 : Fin 32) = bp := by rw [k28 _ (by decide), r27_20]
  have r28_19 : reg n28 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k28 _ (by decide), r27_19]
  have r28_10 : reg n28 a0 = R + BitVec.ofNat 32 0x4A0 := by rw [k28 _ (by decide), r27_10]
  have r28_11 : reg n28 a1 = R + BitVec.ofNat 32 0x594 := by rw [v28, D27.hsp]; exact add_sp R rfl
  obtain ⟨n29, c29, D29, w29, k29, f29⟩ := D28.neg C dec_at_1d6 dec_at_1da (by decide) (by decide) (k := 0x4A0) (by decide) (by decide) (by decide) r28_10 (by rw [r28_11]; exact C.opF (by decide) (by decide) (by decide))
  have r29_18 : reg n29 (18 : Fin 32) = out := by rw [k29 _ (by decide), r28_18]
  have r29_20 : reg n29 (20 : Fin 32) = bp := by rw [k29 _ (by decide), r28_20]
  have r29_19 : reg n29 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k29 _ (by decide), r28_19]
  have m29_544 : feW n29.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f29 (by decide) (by decide) (by decide) (by decide)).trans m25_544
  have m29_594 : feW n29.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f29 (by decide) (by decide) (by decide) (by decide)).trans m25_594
  have m29_5bc : feW n29.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW C f29 (by decide) (by decide) (by decide) (by decide)).trans m25_5bc
  have m29_634 : feW n29.mem (R + BitVec.ofNat 32 0x634) = uv3 := (keepW C f29 (by decide) (by decide) (by decide) (by decide)).trans m25_634
  have m29_684 : feW n29.mem (R + BitVec.ofNat 32 0x684) = uv7 := (keepW C f29 (by decide) (by decide) (by decide) (by decide)).trans m25_684
  have m29_6ac : feW n29.mem (R + BitVec.ofNat 32 0x6AC) = rr := (keepW C f29 (by decide) (by decide) (by decide) (by decide)).trans m25_6ac
  have m29_65c : feW n29.mem (R + BitVec.ofNat 32 0x65C) = chk := (keepW C f29 (by decide) (by decide) (by decide) (by decide)).trans m25_65c
  have m29_4a0 : feW n29.mem (R + BitVec.ofNat 32 0x4A0) = negL (u) := by rw [w29, r28_11, m25_594]
  obtain ⟨n30, c30, D30, v30, k30⟩ := D29.aluImmS C dec_at_1de (off' := 0x1E0) (by decide) (by decide)
  have r30_18 : reg n30 (18 : Fin 32) = out := by rw [k30 _ (by decide), r29_18]
  have r30_20 : reg n30 (20 : Fin 32) = bp := by rw [k30 _ (by decide), r29_20]
  have r30_19 : reg n30 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k30 _ (by decide), r29_19]
  have r30_10 : reg n30 a0 = R + BitVec.ofNat 32 0x65C := by rw [v30, D29.hsp]; exact add_sp R rfl
  obtain ⟨n31, c31, D31, v31, k31⟩ := D30.aluImmS C dec_at_1e0 (off' := 0x1E2) (by decide) (by decide)
  have r31_18 : reg n31 (18 : Fin 32) = out := by rw [k31 _ (by decide), r30_18]
  have r31_20 : reg n31 (20 : Fin 32) = bp := by rw [k31 _ (by decide), r30_20]
  have r31_19 : reg n31 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k31 _ (by decide), r30_19]
  have r31_10 : reg n31 a0 = R + BitVec.ofNat 32 0x65C := by rw [k31 _ (by decide), r30_10]
  have r31_11 : reg n31 a1 = R + BitVec.ofNat 32 0x4A0 := by rw [v31, D30.hsp]; exact add_sp R rfl
  obtain ⟨n32, c32, D32, w32, k32, f32⟩ := D31.ctEq C dec_at_1e2 dec_at_1e6 (by decide) (by decide) (by rw [r31_10]; exact C.opF (by decide) (by decide) (by decide)) (by rw [r31_11]; exact C.opF (by decide) (by decide) (by decide))
  have r32_18 : reg n32 (18 : Fin 32) = out := by rw [k32 _ (by decide), r31_18]
  have r32_20 : reg n32 (20 : Fin 32) = bp := by rw [k32 _ (by decide), r31_20]
  have r32_19 : reg n32 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k32 _ (by decide), r31_19]
  have m32_544 : feW n32.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW0 C f32 (by decide) (by decide)).trans m29_544
  have m32_594 : feW n32.mem (R + BitVec.ofNat 32 0x594) = u := (keepW0 C f32 (by decide) (by decide)).trans m29_594
  have m32_5bc : feW n32.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW0 C f32 (by decide) (by decide)).trans m29_5bc
  have m32_634 : feW n32.mem (R + BitVec.ofNat 32 0x634) = uv3 := (keepW0 C f32 (by decide) (by decide)).trans m29_634
  have m32_684 : feW n32.mem (R + BitVec.ofNat 32 0x684) = uv7 := (keepW0 C f32 (by decide) (by decide)).trans m29_684
  have m32_6ac : feW n32.mem (R + BitVec.ofNat 32 0x6AC) = rr := (keepW0 C f32 (by decide) (by decide)).trans m29_6ac
  have m32_65c : feW n32.mem (R + BitVec.ofNat 32 0x65C) = chk := (keepW0 C f32 (by decide) (by decide)).trans m29_65c
  have m32_4a0 : feW n32.mem (R + BitVec.ofNat 32 0x4A0) = negL (u) := (keepW0 C f32 (by decide) (by decide)).trans m29_4a0
  have r32_10 : reg n32 a0 = bw (feEqL (chk) (negL (u))) := by rw [w32, r31_10, r31_11, m29_65c, m29_4a0, bw_ct]
  obtain ⟨n33, c33, D33, v33, k33⟩ := D32.aluS C dec_at_1ea (off' := 0x1EC) (by decide) (by decide)
  have r33_18 : reg n33 (18 : Fin 32) = out := by rw [k33 _ (by decide), r32_18]
  have r33_20 : reg n33 (20 : Fin 32) = bp := by rw [k33 _ (by decide), r32_20]
  have r33_19 : reg n33 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k33 _ (by decide), r32_19]
  have r33_10 : reg n33 a0 = bw (feEqL (chk) (negL (u))) := by rw [k33 _ (by decide), r32_10]
  have r33_8 : reg n33 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [v33, D32.zero, r32_10]; exact BitVec.zero_add _
  obtain ⟨n34, c34, D34, v34, k34⟩ := D33.aluImmS C dec_at_1ec (off' := 0x1EE) (by decide) (by decide)
  have r34_18 : reg n34 (18 : Fin 32) = out := by rw [k34 _ (by decide), r33_18]
  have r34_20 : reg n34 (20 : Fin 32) = bp := by rw [k34 _ (by decide), r33_20]
  have r34_19 : reg n34 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k34 _ (by decide), r33_19]
  have r34_8 : reg n34 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k34 _ (by decide), r33_8]
  have r34_10 : reg n34 a0 = R + BitVec.ofNat 32 0x4A0 := by rw [v34, D33.hsp]; exact add_sp R rfl
  obtain ⟨n35, c35, D35, v35, k35⟩ := D34.aluImmS C dec_at_1ee (off' := 0x1F0) (by decide) (by decide)
  have r35_18 : reg n35 (18 : Fin 32) = out := by rw [k35 _ (by decide), r34_18]
  have r35_20 : reg n35 (20 : Fin 32) = bp := by rw [k35 _ (by decide), r34_20]
  have r35_19 : reg n35 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k35 _ (by decide), r34_19]
  have r35_8 : reg n35 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k35 _ (by decide), r34_8]
  have r35_10 : reg n35 a0 = R + BitVec.ofNat 32 0x4A0 := by rw [k35 _ (by decide), r34_10]
  have r35_11 : reg n35 a1 = R + BitVec.ofNat 32 0x594 := by rw [v35, D34.hsp]; exact add_sp R rfl
  obtain ⟨n36, c36, D36, w36, k36, f36⟩ := D35.neg C dec_at_1f0 dec_at_1f4 (by decide) (by decide) (k := 0x4A0) (by decide) (by decide) (by decide) r35_10 (by rw [r35_11]; exact C.opF (by decide) (by decide) (by decide))
  have r36_18 : reg n36 (18 : Fin 32) = out := by rw [k36 _ (by decide), r35_18]
  have r36_20 : reg n36 (20 : Fin 32) = bp := by rw [k36 _ (by decide), r35_20]
  have r36_19 : reg n36 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k36 _ (by decide), r35_19]
  have r36_8 : reg n36 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k36 _ (by decide), r35_8]
  have m36_544 : feW n36.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f36 (by decide) (by decide) (by decide) (by decide)).trans m32_544
  have m36_594 : feW n36.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f36 (by decide) (by decide) (by decide) (by decide)).trans m32_594
  have m36_5bc : feW n36.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW C f36 (by decide) (by decide) (by decide) (by decide)).trans m32_5bc
  have m36_634 : feW n36.mem (R + BitVec.ofNat 32 0x634) = uv3 := (keepW C f36 (by decide) (by decide) (by decide) (by decide)).trans m32_634
  have m36_684 : feW n36.mem (R + BitVec.ofNat 32 0x684) = uv7 := (keepW C f36 (by decide) (by decide) (by decide) (by decide)).trans m32_684
  have m36_6ac : feW n36.mem (R + BitVec.ofNat 32 0x6AC) = rr := (keepW C f36 (by decide) (by decide) (by decide) (by decide)).trans m32_6ac
  have m36_65c : feW n36.mem (R + BitVec.ofNat 32 0x65C) = chk := (keepW C f36 (by decide) (by decide) (by decide) (by decide)).trans m32_65c
  have m36_4a0 : feW n36.mem (R + BitVec.ofNat 32 0x4A0) = negL (u) := by rw [w36, r35_11, m32_594]
  obtain ⟨n37, c37, D37, v37, k37⟩ := D36.luiS C dec_at_1f8 (off' := 0x1FC) (by decide) (by decide)
  have r37_18 : reg n37 (18 : Fin 32) = out := by rw [k37 _ (by decide), r36_18]
  have r37_20 : reg n37 (20 : Fin 32) = bp := by rw [k37 _ (by decide), r36_20]
  have r37_19 : reg n37 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k37 _ (by decide), r36_19]
  have r37_8 : reg n37 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k37 _ (by decide), r36_8]
  obtain ⟨n38, c38, D38, v38, k38⟩ := D37.aluImmS C dec_at_1fc (off' := 0x200) (by decide) (by decide)
  have r38_18 : reg n38 (18 : Fin 32) = out := by rw [k38 _ (by decide), r37_18]
  have r38_20 : reg n38 (20 : Fin 32) = bp := by rw [k38 _ (by decide), r37_20]
  have r38_19 : reg n38 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k38 _ (by decide), r37_19]
  have r38_8 : reg n38 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k38 _ (by decide), r37_8]
  have r38_21 : reg n38 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [v38, v37]; decide
  obtain ⟨n39, c39, D39, v39, k39⟩ := D38.aluImmS C dec_at_200 (off' := 0x202) (by decide) (by decide)
  have r39_18 : reg n39 (18 : Fin 32) = out := by rw [k39 _ (by decide), r38_18]
  have r39_20 : reg n39 (20 : Fin 32) = bp := by rw [k39 _ (by decide), r38_20]
  have r39_19 : reg n39 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k39 _ (by decide), r38_19]
  have r39_8 : reg n39 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k39 _ (by decide), r38_8]
  have r39_21 : reg n39 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k39 _ (by decide), r38_21]
  have r39_10 : reg n39 a0 = R + BitVec.ofNat 32 0x684 := by rw [v39, D38.hsp]; exact add_sp R rfl
  obtain ⟨n40, c40, D40, v40, k40⟩ := D39.aluImmS C dec_at_202 (off' := 0x204) (by decide) (by decide)
  have r40_18 : reg n40 (18 : Fin 32) = out := by rw [k40 _ (by decide), r39_18]
  have r40_20 : reg n40 (20 : Fin 32) = bp := by rw [k40 _ (by decide), r39_20]
  have r40_19 : reg n40 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k40 _ (by decide), r39_19]
  have r40_8 : reg n40 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k40 _ (by decide), r39_8]
  have r40_21 : reg n40 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k40 _ (by decide), r39_21]
  have r40_10 : reg n40 a0 = R + BitVec.ofNat 32 0x684 := by rw [k40 _ (by decide), r39_10]
  have r40_11 : reg n40 a1 = R + BitVec.ofNat 32 0x4A0 := by rw [v40, D39.hsp]; exact add_sp R rfl
  obtain ⟨n41, c41, D41, v41, k41⟩ := D40.aluS C dec_at_204 (off' := 0x206) (by decide) (by decide)
  have r41_18 : reg n41 (18 : Fin 32) = out := by rw [k41 _ (by decide), r40_18]
  have r41_20 : reg n41 (20 : Fin 32) = bp := by rw [k41 _ (by decide), r40_20]
  have r41_19 : reg n41 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k41 _ (by decide), r40_19]
  have r41_8 : reg n41 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k41 _ (by decide), r40_8]
  have r41_21 : reg n41 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k41 _ (by decide), r40_21]
  have r41_10 : reg n41 a0 = R + BitVec.ofNat 32 0x684 := by rw [k41 _ (by decide), r40_10]
  have r41_11 : reg n41 a1 = R + BitVec.ofNat 32 0x4A0 := by rw [k41 _ (by decide), r40_11]
  have r41_12 : reg n41 a2 = BitVec.ofNat 32 edSqrtM1Address := by rw [v41, D40.zero, r40_21]; exact BitVec.zero_add _
  obtain ⟨n42, c42, D42, w42, k42, f42⟩ := D41.mul C dec_at_206 dec_at_20a (by decide) (by decide) (k := 0x684) (by decide) (by decide) (by decide) r41_10 (by rw [r41_11]; exact C.opF (by decide) (by decide) (by decide)) (by rw [r41_12]; exact C.opC sS (by decide))
  have r42_18 : reg n42 (18 : Fin 32) = out := by rw [k42 _ (by decide), r41_18]
  have r42_20 : reg n42 (20 : Fin 32) = bp := by rw [k42 _ (by decide), r41_20]
  have r42_19 : reg n42 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k42 _ (by decide), r41_19]
  have r42_8 : reg n42 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k42 _ (by decide), r41_8]
  have r42_21 : reg n42 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k42 _ (by decide), r41_21]
  have m42_544 : feW n42.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f42 (by decide) (by decide) (by decide) (by decide)).trans m36_544
  have m42_594 : feW n42.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f42 (by decide) (by decide) (by decide) (by decide)).trans m36_594
  have m42_5bc : feW n42.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW C f42 (by decide) (by decide) (by decide) (by decide)).trans m36_5bc
  have m42_634 : feW n42.mem (R + BitVec.ofNat 32 0x634) = uv3 := (keepW C f42 (by decide) (by decide) (by decide) (by decide)).trans m36_634
  have m42_6ac : feW n42.mem (R + BitVec.ofNat 32 0x6AC) = rr := (keepW C f42 (by decide) (by decide) (by decide) (by decide)).trans m36_6ac
  have m42_65c : feW n42.mem (R + BitVec.ofNat 32 0x65C) = chk := (keepW C f42 (by decide) (by decide) (by decide) (by decide)).trans m36_65c
  have m42_4a0 : feW n42.mem (R + BitVec.ofNat 32 0x4A0) = negL (u) := (keepW C f42 (by decide) (by decide) (by decide) (by decide)).trans m36_4a0
  have m42_684 : feW n42.mem (R + BitVec.ofNat 32 0x684) = mulL (negL (u)) (sm) := by rw [w42, r41_11, r41_12, m36_4a0, (D41.constW sS), hS]
  obtain ⟨n43, c43, D43, v43, k43⟩ := D42.aluImmS C dec_at_20e (off' := 0x210) (by decide) (by decide)
  have r43_18 : reg n43 (18 : Fin 32) = out := by rw [k43 _ (by decide), r42_18]
  have r43_20 : reg n43 (20 : Fin 32) = bp := by rw [k43 _ (by decide), r42_20]
  have r43_19 : reg n43 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k43 _ (by decide), r42_19]
  have r43_8 : reg n43 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k43 _ (by decide), r42_8]
  have r43_21 : reg n43 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k43 _ (by decide), r42_21]
  have r43_10 : reg n43 a0 = R + BitVec.ofNat 32 0x65C := by rw [v43, D42.hsp]; exact add_sp R rfl
  obtain ⟨n44, c44, D44, v44, k44⟩ := D43.aluImmS C dec_at_210 (off' := 0x212) (by decide) (by decide)
  have r44_18 : reg n44 (18 : Fin 32) = out := by rw [k44 _ (by decide), r43_18]
  have r44_20 : reg n44 (20 : Fin 32) = bp := by rw [k44 _ (by decide), r43_20]
  have r44_19 : reg n44 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k44 _ (by decide), r43_19]
  have r44_8 : reg n44 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k44 _ (by decide), r43_8]
  have r44_21 : reg n44 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k44 _ (by decide), r43_21]
  have r44_10 : reg n44 a0 = R + BitVec.ofNat 32 0x65C := by rw [k44 _ (by decide), r43_10]
  have r44_11 : reg n44 a1 = R + BitVec.ofNat 32 0x684 := by rw [v44, D43.hsp]; exact add_sp R rfl
  obtain ⟨n45, c45, D45, w45, k45, f45⟩ := D44.ctEq C dec_at_212 dec_at_216 (by decide) (by decide) (by rw [r44_10]; exact C.opF (by decide) (by decide) (by decide)) (by rw [r44_11]; exact C.opF (by decide) (by decide) (by decide))
  have r45_18 : reg n45 (18 : Fin 32) = out := by rw [k45 _ (by decide), r44_18]
  have r45_20 : reg n45 (20 : Fin 32) = bp := by rw [k45 _ (by decide), r44_20]
  have r45_19 : reg n45 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k45 _ (by decide), r44_19]
  have r45_8 : reg n45 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k45 _ (by decide), r44_8]
  have r45_21 : reg n45 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k45 _ (by decide), r44_21]
  have m45_544 : feW n45.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW0 C f45 (by decide) (by decide)).trans m42_544
  have m45_594 : feW n45.mem (R + BitVec.ofNat 32 0x594) = u := (keepW0 C f45 (by decide) (by decide)).trans m42_594
  have m45_5bc : feW n45.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW0 C f45 (by decide) (by decide)).trans m42_5bc
  have m45_634 : feW n45.mem (R + BitVec.ofNat 32 0x634) = uv3 := (keepW0 C f45 (by decide) (by decide)).trans m42_634
  have m45_6ac : feW n45.mem (R + BitVec.ofNat 32 0x6AC) = rr := (keepW0 C f45 (by decide) (by decide)).trans m42_6ac
  have m45_65c : feW n45.mem (R + BitVec.ofNat 32 0x65C) = chk := (keepW0 C f45 (by decide) (by decide)).trans m42_65c
  have m45_4a0 : feW n45.mem (R + BitVec.ofNat 32 0x4A0) = negL (u) := (keepW0 C f45 (by decide) (by decide)).trans m42_4a0
  have m45_684 : feW n45.mem (R + BitVec.ofNat 32 0x684) = mulL (negL (u)) (sm) := (keepW0 C f45 (by decide) (by decide)).trans m42_684
  have r45_10 : reg n45 a0 = bw (feEqL (chk) (mulL (negL (u)) (sm))) := by rw [w45, r44_10, r44_11, m42_65c, m42_684, bw_ct]
  obtain ⟨n46, c46, D46, v46, k46⟩ := D45.aluS C dec_at_21a (off' := 0x21C) (by decide) (by decide)
  have r46_18 : reg n46 (18 : Fin 32) = out := by rw [k46 _ (by decide), r45_18]
  have r46_20 : reg n46 (20 : Fin 32) = bp := by rw [k46 _ (by decide), r45_20]
  have r46_19 : reg n46 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k46 _ (by decide), r45_19]
  have r46_8 : reg n46 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k46 _ (by decide), r45_8]
  have r46_21 : reg n46 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k46 _ (by decide), r45_21]
  have r46_10 : reg n46 a0 = bw (feEqL (chk) (mulL (negL (u)) (sm))) := by rw [k46 _ (by decide), r45_10]
  have r46_9 : reg n46 (9 : Fin 32) = bw (feEqL (chk) (mulL (negL (u)) (sm))) := by rw [v46, D45.zero, r45_10]; exact BitVec.zero_add _
  obtain ⟨n47, c47, D47, v47, k47⟩ := D46.aluImmS C dec_at_21c (off' := 0x21E) (by decide) (by decide)
  have r47_18 : reg n47 (18 : Fin 32) = out := by rw [k47 _ (by decide), r46_18]
  have r47_20 : reg n47 (20 : Fin 32) = bp := by rw [k47 _ (by decide), r46_20]
  have r47_19 : reg n47 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k47 _ (by decide), r46_19]
  have r47_8 : reg n47 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k47 _ (by decide), r46_8]
  have r47_21 : reg n47 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k47 _ (by decide), r46_21]
  have r47_9 : reg n47 (9 : Fin 32) = bw (feEqL (chk) (mulL (negL (u)) (sm))) := by rw [k47 _ (by decide), r46_9]
  have r47_10 : reg n47 a0 = R + BitVec.ofNat 32 0x684 := by rw [v47, D46.hsp]; exact add_sp R rfl
  obtain ⟨n48, c48, D48, v48, k48⟩ := D47.aluImmS C dec_at_21e (off' := 0x220) (by decide) (by decide)
  have r48_18 : reg n48 (18 : Fin 32) = out := by rw [k48 _ (by decide), r47_18]
  have r48_20 : reg n48 (20 : Fin 32) = bp := by rw [k48 _ (by decide), r47_20]
  have r48_19 : reg n48 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k48 _ (by decide), r47_19]
  have r48_8 : reg n48 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k48 _ (by decide), r47_8]
  have r48_21 : reg n48 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k48 _ (by decide), r47_21]
  have r48_9 : reg n48 (9 : Fin 32) = bw (feEqL (chk) (mulL (negL (u)) (sm))) := by rw [k48 _ (by decide), r47_9]
  have r48_10 : reg n48 a0 = R + BitVec.ofNat 32 0x684 := by rw [k48 _ (by decide), r47_10]
  have r48_12 : reg n48 a2 = R + BitVec.ofNat 32 0x6AC := by rw [v48, D47.hsp]; exact add_sp R rfl
  obtain ⟨n49, c49, D49, v49, k49⟩ := D48.aluS C dec_at_220 (off' := 0x222) (by decide) (by decide)
  have r49_18 : reg n49 (18 : Fin 32) = out := by rw [k49 _ (by decide), r48_18]
  have r49_20 : reg n49 (20 : Fin 32) = bp := by rw [k49 _ (by decide), r48_20]
  have r49_19 : reg n49 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k49 _ (by decide), r48_19]
  have r49_8 : reg n49 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k49 _ (by decide), r48_8]
  have r49_21 : reg n49 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k49 _ (by decide), r48_21]
  have r49_9 : reg n49 (9 : Fin 32) = bw (feEqL (chk) (mulL (negL (u)) (sm))) := by rw [k49 _ (by decide), r48_9]
  have r49_10 : reg n49 a0 = R + BitVec.ofNat 32 0x684 := by rw [k49 _ (by decide), r48_10]
  have r49_12 : reg n49 a2 = R + BitVec.ofNat 32 0x6AC := by rw [k49 _ (by decide), r48_12]
  have r49_11 : reg n49 a1 = BitVec.ofNat 32 edSqrtM1Address := by rw [v49, D48.zero, r48_21]; exact BitVec.zero_add _
  obtain ⟨n50, c50, D50, w50, k50, f50⟩ := D49.mul C dec_at_222 dec_at_226 (by decide) (by decide) (k := 0x684) (by decide) (by decide) (by decide) r49_10 (by rw [r49_11]; exact C.opC sS (by decide)) (by rw [r49_12]; exact C.opF (by decide) (by decide) (by decide))
  have r50_18 : reg n50 (18 : Fin 32) = out := by rw [k50 _ (by decide), r49_18]
  have r50_20 : reg n50 (20 : Fin 32) = bp := by rw [k50 _ (by decide), r49_20]
  have r50_19 : reg n50 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k50 _ (by decide), r49_19]
  have r50_8 : reg n50 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k50 _ (by decide), r49_8]
  have r50_21 : reg n50 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k50 _ (by decide), r49_21]
  have r50_9 : reg n50 (9 : Fin 32) = bw (feEqL (chk) (mulL (negL (u)) (sm))) := by rw [k50 _ (by decide), r49_9]
  have m50_544 : feW n50.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f50 (by decide) (by decide) (by decide) (by decide)).trans m45_544
  have m50_594 : feW n50.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f50 (by decide) (by decide) (by decide) (by decide)).trans m45_594
  have m50_5bc : feW n50.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW C f50 (by decide) (by decide) (by decide) (by decide)).trans m45_5bc
  have m50_634 : feW n50.mem (R + BitVec.ofNat 32 0x634) = uv3 := (keepW C f50 (by decide) (by decide) (by decide) (by decide)).trans m45_634
  have m50_6ac : feW n50.mem (R + BitVec.ofNat 32 0x6AC) = rr := (keepW C f50 (by decide) (by decide) (by decide) (by decide)).trans m45_6ac
  have m50_65c : feW n50.mem (R + BitVec.ofNat 32 0x65C) = chk := (keepW C f50 (by decide) (by decide) (by decide) (by decide)).trans m45_65c
  have m50_4a0 : feW n50.mem (R + BitVec.ofNat 32 0x4A0) = negL (u) := (keepW C f50 (by decide) (by decide) (by decide) (by decide)).trans m45_4a0
  have m50_684 : feW n50.mem (R + BitVec.ofNat 32 0x684) = mulL (sm) (rr) := by rw [w50, r49_11, r49_12, (D49.constW sS), hS, m45_6ac]
  obtain ⟨n51, c51, D51, v51, k51⟩ := D50.aluS C dec_at_22a (off' := 0x22C) (by decide) (by decide)
  have r51_18 : reg n51 (18 : Fin 32) = out := by rw [k51 _ (by decide), r50_18]
  have r51_20 : reg n51 (20 : Fin 32) = bp := by rw [k51 _ (by decide), r50_20]
  have r51_19 : reg n51 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k51 _ (by decide), r50_19]
  have r51_8 : reg n51 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k51 _ (by decide), r50_8]
  have r51_21 : reg n51 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k51 _ (by decide), r50_21]
  have r51_9 : reg n51 (9 : Fin 32) = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [v51, r50_9, r50_8, bw_or]
  obtain ⟨n52, c52, D52, v52, k52⟩ := D51.aluImmS C dec_at_22c (off' := 0x230) (by decide) (by decide)
  have r52_18 : reg n52 (18 : Fin 32) = out := by rw [k52 _ (by decide), r51_18]
  have r52_20 : reg n52 (20 : Fin 32) = bp := by rw [k52 _ (by decide), r51_20]
  have r52_19 : reg n52 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k52 _ (by decide), r51_19]
  have r52_8 : reg n52 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k52 _ (by decide), r51_8]
  have r52_21 : reg n52 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k52 _ (by decide), r51_21]
  have r52_9 : reg n52 (9 : Fin 32) = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [k52 _ (by decide), r51_9]
  have r52_10 : reg n52 a0 = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [v52, r51_9, bw_zext]
  obtain ⟨n53, c53, D53, w53, k53, f53⟩ := D52.blackBox C dec_at_230 dec_at_234 (by decide) (by decide)
  have r53_18 : reg n53 (18 : Fin 32) = out := by rw [k53 _ (by decide) (by decide), r52_18]
  have r53_20 : reg n53 (20 : Fin 32) = bp := by rw [k53 _ (by decide) (by decide), r52_20]
  have r53_19 : reg n53 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k53 _ (by decide) (by decide), r52_19]
  have r53_8 : reg n53 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k53 _ (by decide) (by decide), r52_8]
  have r53_21 : reg n53 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k53 _ (by decide) (by decide), r52_21]
  have r53_9 : reg n53 (9 : Fin 32) = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [k53 _ (by decide) (by decide), r52_9]
  have m53_544 : feW n53.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW0 C f53 (by decide) (by decide)).trans m50_544
  have m53_594 : feW n53.mem (R + BitVec.ofNat 32 0x594) = u := (keepW0 C f53 (by decide) (by decide)).trans m50_594
  have m53_5bc : feW n53.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW0 C f53 (by decide) (by decide)).trans m50_5bc
  have m53_634 : feW n53.mem (R + BitVec.ofNat 32 0x634) = uv3 := (keepW0 C f53 (by decide) (by decide)).trans m50_634
  have m53_6ac : feW n53.mem (R + BitVec.ofNat 32 0x6AC) = rr := (keepW0 C f53 (by decide) (by decide)).trans m50_6ac
  have m53_65c : feW n53.mem (R + BitVec.ofNat 32 0x65C) = chk := (keepW0 C f53 (by decide) (by decide)).trans m50_65c
  have m53_4a0 : feW n53.mem (R + BitVec.ofNat 32 0x4A0) = negL (u) := (keepW0 C f53 (by decide) (by decide)).trans m50_4a0
  have m53_684 : feW n53.mem (R + BitVec.ofNat 32 0x684) = mulL (sm) (rr) := (keepW0 C f53 (by decide) (by decide)).trans m50_684
  have r53_10 : reg n53 a0 = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [w53, r52_10, bw_bb]
  obtain ⟨n54, c54, D54, v54, k54⟩ := D53.aluImmS C dec_at_238 (off' := 0x23C) (by decide) (by decide)
  have r54_18 : reg n54 (18 : Fin 32) = out := by rw [k54 _ (by decide), r53_18]
  have r54_20 : reg n54 (20 : Fin 32) = bp := by rw [k54 _ (by decide), r53_20]
  have r54_19 : reg n54 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k54 _ (by decide), r53_19]
  have r54_8 : reg n54 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k54 _ (by decide), r53_8]
  have r54_21 : reg n54 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k54 _ (by decide), r53_21]
  have r54_9 : reg n54 (9 : Fin 32) = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [k54 _ (by decide), r53_9]
  have r54_10 : reg n54 a0 = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [k54 _ (by decide), r53_10]
  have r54_12 : reg n54 a2 = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [v54, r53_10, bw_zext]
  obtain ⟨n55, c55, D55, v55, k55⟩ := D54.aluImmS C dec_at_23c (off' := 0x23E) (by decide) (by decide)
  have r55_18 : reg n55 (18 : Fin 32) = out := by rw [k55 _ (by decide), r54_18]
  have r55_20 : reg n55 (20 : Fin 32) = bp := by rw [k55 _ (by decide), r54_20]
  have r55_19 : reg n55 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k55 _ (by decide), r54_19]
  have r55_8 : reg n55 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k55 _ (by decide), r54_8]
  have r55_21 : reg n55 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k55 _ (by decide), r54_21]
  have r55_9 : reg n55 (9 : Fin 32) = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [k55 _ (by decide), r54_9]
  have r55_12 : reg n55 a2 = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [k55 _ (by decide), r54_12]
  have r55_10 : reg n55 a0 = R + BitVec.ofNat 32 0x6AC := by rw [v55, D54.hsp]; exact add_sp R rfl
  obtain ⟨n56, c56, D56, v56, k56⟩ := D55.aluImmS C dec_at_23e (off' := 0x240) (by decide) (by decide)
  have r56_18 : reg n56 (18 : Fin 32) = out := by rw [k56 _ (by decide), r55_18]
  have r56_20 : reg n56 (20 : Fin 32) = bp := by rw [k56 _ (by decide), r55_20]
  have r56_19 : reg n56 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k56 _ (by decide), r55_19]
  have r56_8 : reg n56 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k56 _ (by decide), r55_8]
  have r56_21 : reg n56 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k56 _ (by decide), r55_21]
  have r56_9 : reg n56 (9 : Fin 32) = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [k56 _ (by decide), r55_9]
  have r56_12 : reg n56 a2 = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [k56 _ (by decide), r55_12]
  have r56_10 : reg n56 a0 = R + BitVec.ofNat 32 0x6AC := by rw [k56 _ (by decide), r55_10]
  have r56_11 : reg n56 a1 = R + BitVec.ofNat 32 0x684 := by rw [v56, D55.hsp]; exact add_sp R rfl
  obtain ⟨n57, c57, D57, w57, k57, f57⟩ := D56.condAssign C dec_at_240 dec_at_244 (by decide) (by decide) (k := 0x6AC) (j := 0x684) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r56_10 r56_11 r56_12 (bw_01 _)
  have r57_18 : reg n57 (18 : Fin 32) = out := by rw [k57 _ (by decide), r56_18]
  have r57_20 : reg n57 (20 : Fin 32) = bp := by rw [k57 _ (by decide), r56_20]
  have r57_19 : reg n57 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k57 _ (by decide), r56_19]
  have r57_8 : reg n57 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k57 _ (by decide), r56_8]
  have r57_21 : reg n57 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k57 _ (by decide), r56_21]
  have r57_9 : reg n57 (9 : Fin 32) = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [k57 _ (by decide), r56_9]
  have m57_544 : feW n57.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f57 (by decide) (by decide) (by decide) (by decide)).trans m53_544
  have m57_594 : feW n57.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f57 (by decide) (by decide) (by decide) (by decide)).trans m53_594
  have m57_5bc : feW n57.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW C f57 (by decide) (by decide) (by decide) (by decide)).trans m53_5bc
  have m57_634 : feW n57.mem (R + BitVec.ofNat 32 0x634) = uv3 := (keepW C f57 (by decide) (by decide) (by decide) (by decide)).trans m53_634
  have m57_65c : feW n57.mem (R + BitVec.ofNat 32 0x65C) = chk := (keepW C f57 (by decide) (by decide) (by decide) (by decide)).trans m53_65c
  have m57_4a0 : feW n57.mem (R + BitVec.ofNat 32 0x4A0) = negL (u) := (keepW C f57 (by decide) (by decide) (by decide) (by decide)).trans m53_4a0
  have m57_684 : feW n57.mem (R + BitVec.ofNat 32 0x684) = mulL (sm) (rr) := (keepW C f57 (by decide) (by decide) (by decide) (by decide)).trans m53_684
  have m57_6ac : feW n57.mem (R + BitVec.ofNat 32 0x6AC) = (if (feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u))) then mulL (sm) (rr) else rr) := by rw [w57, bw_ite, m53_684, m53_6ac]
  obtain ⟨n58, c58, D58, v58, k58⟩ := D57.aluImmS C dec_at_248 (off' := 0x24A) (by decide) (by decide)
  have r58_18 : reg n58 (18 : Fin 32) = out := by rw [k58 _ (by decide), r57_18]
  have r58_20 : reg n58 (20 : Fin 32) = bp := by rw [k58 _ (by decide), r57_20]
  have r58_19 : reg n58 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k58 _ (by decide), r57_19]
  have r58_8 : reg n58 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k58 _ (by decide), r57_8]
  have r58_21 : reg n58 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k58 _ (by decide), r57_21]
  have r58_9 : reg n58 (9 : Fin 32) = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [k58 _ (by decide), r57_9]
  have r58_10 : reg n58 a0 = R + BitVec.ofNat 32 0x6AC := by rw [v58, D57.hsp]; exact add_sp R rfl
  obtain ⟨n59, c59, D59, w59, k59, f59⟩ := D58.isNeg C dec_at_24a dec_at_24e (by decide) (by decide) (by rw [r58_10]; exact C.opF (by decide) (by decide) (by decide))
  have r59_18 : reg n59 (18 : Fin 32) = out := by rw [k59 _ (by decide), r58_18]
  have r59_20 : reg n59 (20 : Fin 32) = bp := by rw [k59 _ (by decide), r58_20]
  have r59_19 : reg n59 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k59 _ (by decide), r58_19]
  have r59_8 : reg n59 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k59 _ (by decide), r58_8]
  have r59_21 : reg n59 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k59 _ (by decide), r58_21]
  have r59_9 : reg n59 (9 : Fin 32) = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [k59 _ (by decide), r58_9]
  have m59_544 : feW n59.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW0 C f59 (by decide) (by decide)).trans m57_544
  have m59_594 : feW n59.mem (R + BitVec.ofNat 32 0x594) = u := (keepW0 C f59 (by decide) (by decide)).trans m57_594
  have m59_5bc : feW n59.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW0 C f59 (by decide) (by decide)).trans m57_5bc
  have m59_634 : feW n59.mem (R + BitVec.ofNat 32 0x634) = uv3 := (keepW0 C f59 (by decide) (by decide)).trans m57_634
  have m59_65c : feW n59.mem (R + BitVec.ofNat 32 0x65C) = chk := (keepW0 C f59 (by decide) (by decide)).trans m57_65c
  have m59_4a0 : feW n59.mem (R + BitVec.ofNat 32 0x4A0) = negL (u) := (keepW0 C f59 (by decide) (by decide)).trans m57_4a0
  have m59_684 : feW n59.mem (R + BitVec.ofNat 32 0x684) = mulL (sm) (rr) := (keepW0 C f59 (by decide) (by decide)).trans m57_684
  have m59_6ac : feW n59.mem (R + BitVec.ofNat 32 0x6AC) = (if (feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u))) then mulL (sm) (rr) else rr) := (keepW0 C f59 (by decide) (by decide)).trans m57_6ac
  have r59_10 : reg n59 a0 = bw (isNegL ((if (feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u))) then mulL (sm) (rr) else rr))) := by rw [w59, r58_10, m57_6ac, bw_isNeg]
  obtain ⟨n60, c60, D60, v60, k60⟩ := D59.aluImmS C dec_at_252 (off' := 0x256) (by decide) (by decide)
  have r60_18 : reg n60 (18 : Fin 32) = out := by rw [k60 _ (by decide), r59_18]
  have r60_20 : reg n60 (20 : Fin 32) = bp := by rw [k60 _ (by decide), r59_20]
  have r60_19 : reg n60 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k60 _ (by decide), r59_19]
  have r60_8 : reg n60 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k60 _ (by decide), r59_8]
  have r60_21 : reg n60 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k60 _ (by decide), r59_21]
  have r60_9 : reg n60 (9 : Fin 32) = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [k60 _ (by decide), r59_9]
  have r60_10 : reg n60 a0 = bw (isNegL ((if (feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u))) then mulL (sm) (rr) else rr))) := by rw [k60 _ (by decide), r59_10]
  have r60_11 : reg n60 a1 = bw (isNegL ((if (feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u))) then mulL (sm) (rr) else rr))) := by rw [v60, r59_10, bw_zext]
  obtain ⟨n61, c61, D61, v61, k61⟩ := D60.aluImmS C dec_at_256 (off' := 0x258) (by decide) (by decide)
  have r61_18 : reg n61 (18 : Fin 32) = out := by rw [k61 _ (by decide), r60_18]
  have r61_20 : reg n61 (20 : Fin 32) = bp := by rw [k61 _ (by decide), r60_20]
  have r61_19 : reg n61 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k61 _ (by decide), r60_19]
  have r61_8 : reg n61 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k61 _ (by decide), r60_8]
  have r61_21 : reg n61 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k61 _ (by decide), r60_21]
  have r61_9 : reg n61 (9 : Fin 32) = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [k61 _ (by decide), r60_9]
  have r61_11 : reg n61 a1 = bw (isNegL ((if (feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u))) then mulL (sm) (rr) else rr))) := by rw [k61 _ (by decide), r60_11]
  have r61_10 : reg n61 a0 = R + BitVec.ofNat 32 0x6AC := by rw [v61, D60.hsp]; exact add_sp R rfl
  obtain ⟨n62, c62, D62, w62, k62, f62⟩ := D61.condNeg C dec_at_258 dec_at_25c (by decide) (by decide) (k := 0x6AC) (by decide) (by decide) (by decide) r61_10 r61_11 (bw_01 _)
  have r62_18 : reg n62 (18 : Fin 32) = out := by rw [k62 _ (by decide), r61_18]
  have r62_20 : reg n62 (20 : Fin 32) = bp := by rw [k62 _ (by decide), r61_20]
  have r62_19 : reg n62 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k62 _ (by decide), r61_19]
  have r62_8 : reg n62 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k62 _ (by decide), r61_8]
  have r62_21 : reg n62 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k62 _ (by decide), r61_21]
  have r62_9 : reg n62 (9 : Fin 32) = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [k62 _ (by decide), r61_9]
  have m62_544 : feW n62.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f62 (by decide) (by decide) (by decide) (by decide)).trans m59_544
  have m62_594 : feW n62.mem (R + BitVec.ofNat 32 0x594) = u := (keepW C f62 (by decide) (by decide) (by decide) (by decide)).trans m59_594
  have m62_5bc : feW n62.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW C f62 (by decide) (by decide) (by decide) (by decide)).trans m59_5bc
  have m62_634 : feW n62.mem (R + BitVec.ofNat 32 0x634) = uv3 := (keepW C f62 (by decide) (by decide) (by decide) (by decide)).trans m59_634
  have m62_65c : feW n62.mem (R + BitVec.ofNat 32 0x65C) = chk := (keepW C f62 (by decide) (by decide) (by decide) (by decide)).trans m59_65c
  have m62_4a0 : feW n62.mem (R + BitVec.ofNat 32 0x4A0) = negL (u) := (keepW C f62 (by decide) (by decide) (by decide) (by decide)).trans m59_4a0
  have m62_684 : feW n62.mem (R + BitVec.ofNat 32 0x684) = mulL (sm) (rr) := (keepW C f62 (by decide) (by decide) (by decide) (by decide)).trans m59_684
  have m62_6ac : feW n62.mem (R + BitVec.ofNat 32 0x6AC) = condNegL ((if (feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u))) then mulL (sm) (rr) else rr)) (isNegL ((if (feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u))) then mulL (sm) (rr) else rr))) := by rw [w62, m59_6ac, bw_beq]
  obtain ⟨n63, c63, D63, v63, k63⟩ := D62.aluS C dec_at_260 (off' := 0x264) (by decide) (by decide)
  have r63_18 : reg n63 (18 : Fin 32) = out := by rw [k63 _ (by decide), r62_18]
  have r63_20 : reg n63 (20 : Fin 32) = bp := by rw [k63 _ (by decide), r62_20]
  have r63_19 : reg n63 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k63 _ (by decide), r62_19]
  have r63_8 : reg n63 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k63 _ (by decide), r62_8]
  have r63_21 : reg n63 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k63 _ (by decide), r62_21]
  have r63_9 : reg n63 (9 : Fin 32) = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [k63 _ (by decide), r62_9]
  have r63_10 : reg n63 a0 = bw ((feEqL (chk) (negL (u))) || (feEqL (chk) (u))) := by rw [v63, r62_8, r62_19, bw_or]
  obtain ⟨n64, c64, D64, v64, k64⟩ := D63.aluImmS C dec_at_264 (off' := 0x268) (by decide) (by decide)
  have r64_18 : reg n64 (18 : Fin 32) = out := by rw [k64 _ (by decide), r63_18]
  have r64_20 : reg n64 (20 : Fin 32) = bp := by rw [k64 _ (by decide), r63_20]
  have r64_19 : reg n64 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k64 _ (by decide), r63_19]
  have r64_8 : reg n64 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k64 _ (by decide), r63_8]
  have r64_21 : reg n64 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k64 _ (by decide), r63_21]
  have r64_9 : reg n64 (9 : Fin 32) = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [k64 _ (by decide), r63_9]
  have r64_10 : reg n64 a0 = bw ((feEqL (chk) (negL (u))) || (feEqL (chk) (u))) := by rw [v64, r63_10, bw_zext]
  obtain ⟨n65, c65, D65, w65, k65, f65⟩ := D64.blackBox C dec_at_268 dec_at_26c (by decide) (by decide)
  have r65_18 : reg n65 (18 : Fin 32) = out := by rw [k65 _ (by decide) (by decide), r64_18]
  have r65_20 : reg n65 (20 : Fin 32) = bp := by rw [k65 _ (by decide) (by decide), r64_20]
  have r65_19 : reg n65 (19 : Fin 32) = bw (feEqL (chk) (u)) := by rw [k65 _ (by decide) (by decide), r64_19]
  have r65_8 : reg n65 (8 : Fin 32) = bw (feEqL (chk) (negL (u))) := by rw [k65 _ (by decide) (by decide), r64_8]
  have r65_21 : reg n65 (21 : Fin 32) = BitVec.ofNat 32 edSqrtM1Address := by rw [k65 _ (by decide) (by decide), r64_21]
  have r65_9 : reg n65 (9 : Fin 32) = bw ((feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u)))) := by rw [k65 _ (by decide) (by decide), r64_9]
  have m65_544 : feW n65.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW0 C f65 (by decide) (by decide)).trans m62_544
  have m65_594 : feW n65.mem (R + BitVec.ofNat 32 0x594) = u := (keepW0 C f65 (by decide) (by decide)).trans m62_594
  have m65_5bc : feW n65.mem (R + BitVec.ofNat 32 0x5BC) = v := (keepW0 C f65 (by decide) (by decide)).trans m62_5bc
  have m65_634 : feW n65.mem (R + BitVec.ofNat 32 0x634) = uv3 := (keepW0 C f65 (by decide) (by decide)).trans m62_634
  have m65_65c : feW n65.mem (R + BitVec.ofNat 32 0x65C) = chk := (keepW0 C f65 (by decide) (by decide)).trans m62_65c
  have m65_4a0 : feW n65.mem (R + BitVec.ofNat 32 0x4A0) = negL (u) := (keepW0 C f65 (by decide) (by decide)).trans m62_4a0
  have m65_684 : feW n65.mem (R + BitVec.ofNat 32 0x684) = mulL (sm) (rr) := (keepW0 C f65 (by decide) (by decide)).trans m62_684
  have m65_6ac : feW n65.mem (R + BitVec.ofNat 32 0x6AC) = condNegL ((if (feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u))) then mulL (sm) (rr) else rr)) (isNegL ((if (feEqL (chk) (mulL (negL (u)) (sm))) || (feEqL (chk) (negL (u))) then mulL (sm) (rr) else rr))) := (keepW0 C f65 (by decide) (by decide)).trans m62_6ac
  have r65_10 : reg n65 a0 = bw ((feEqL (chk) (negL (u))) || (feEqL (chk) (u))) := by rw [w65, r64_10, bw_bb]
  exact ⟨n65, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans (c11.trans (c12.trans (c13.trans (c14.trans (c15.trans (c16.trans (c17.trans (c18.trans (c19.trans (c20.trans (c21.trans (c22.trans (c23.trans (c24.trans (c25.trans (c26.trans (c27.trans (c28.trans (c29.trans (c30.trans (c31.trans (c32.trans (c33.trans (c34.trans (c35.trans (c36.trans (c37.trans (c38.trans (c39.trans (c40.trans (c41.trans (c42.trans (c43.trans (c44.trans (c45.trans (c46.trans (c47.trans (c48.trans (c49.trans (c50.trans (c51.trans (c52.trans (c53.trans (c54.trans (c55.trans (c56.trans (c57.trans (c58.trans (c59.trans (c60.trans (c61.trans (c62.trans (c63.trans (c64.trans (c65)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), D65, r65_18, r65_20, r65_10, m65_544, m65_6ac⟩


set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x270 to the branch at 0x2BA: the root `X` is copied to the
frame's start and `Y` to offset 0x25C, and `s1` keeps whether `u / v` is a
square. -/
theorem dec_ph4a (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm 0x270) {out bp : Word} {X Y : List Nat} {ok : Bool}
    (hs2 : reg nm (18 : Fin 32) = out) (hs4 : reg nm (20 : Fin 32) = bp) (ha0 : reg nm a0 = bw (ok))
    (hY : feW M (R + BitVec.ofNat 32 0x544) = Y) (hX : feW M (R + BitVec.ofNat 32 0x6AC) = X) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' 0x2BA ∧ reg nm' (18 : Fin 32) = out ∧
      reg nm' (20 : Fin 32) = bp ∧ reg nm' (9 : Fin 32) = bw (ok) ∧
      feW nm'.mem (R + BitVec.ofNat 32 0x450) = X ∧ feW nm'.mem (R + BitVec.ofNat 32 0x6AC) = Y := by
  obtain ⟨n1, c1, D1, v1, k1⟩ := D.aluImmS C dec_at_270 (off' := 0x274) (by decide) (by decide)
  have r1_18 : reg n1 (18 : Fin 32) = out := by rw [k1 _ (by decide), hs2]
  have r1_20 : reg n1 (20 : Fin 32) = bp := by rw [k1 _ (by decide), hs4]
  have r1_10 : reg n1 a0 = bw (ok) := by rw [k1 _ (by decide), ha0]
  have r1_8 : reg n1 (8 : Fin 32) = R + BitVec.ofNat 32 0x4A3 := by rw [v1, D.hsp]; exact add_sp R rfl
  obtain ⟨n2, c2, D2, v2, k2⟩ := D1.aluImmS C dec_at_274 (off' := 0x278) (by decide) (by decide)
  have r2_18 : reg n2 (18 : Fin 32) = out := by rw [k2 _ (by decide), r1_18]
  have r2_20 : reg n2 (20 : Fin 32) = bp := by rw [k2 _ (by decide), r1_20]
  have r2_10 : reg n2 a0 = bw (ok) := by rw [k2 _ (by decide), r1_10]
  have r2_8 : reg n2 (8 : Fin 32) = R + BitVec.ofNat 32 0x4A3 := by rw [k2 _ (by decide), r1_8]
  have r2_9 : reg n2 (9 : Fin 32) = bw (ok) := by rw [v2, r1_10, bw_zext]
  obtain ⟨n3, c3, D3, v3, k3⟩ := D2.aluImmS C dec_at_278 (off' := 0x27A) (by decide) (by decide)
  have r3_18 : reg n3 (18 : Fin 32) = out := by rw [k3 _ (by decide), r2_18]
  have r3_20 : reg n3 (20 : Fin 32) = bp := by rw [k3 _ (by decide), r2_20]
  have r3_10 : reg n3 a0 = bw (ok) := by rw [k3 _ (by decide), r2_10]
  have r3_8 : reg n3 (8 : Fin 32) = R + BitVec.ofNat 32 0x4A3 := by rw [k3 _ (by decide), r2_8]
  have r3_9 : reg n3 (9 : Fin 32) = bw (ok) := by rw [k3 _ (by decide), r2_9]
  have r3_11 : reg n3 a1 = R + BitVec.ofNat 32 0x6AC := by rw [v3, D2.hsp]; exact add_sp R rfl
  obtain ⟨n4, c4, D4, v4, k4⟩ := D3.aluImmS C dec_at_27a (off' := 0x27E) (by decide) (by decide)
  have r4_18 : reg n4 (18 : Fin 32) = out := by rw [k4 _ (by decide), r3_18]
  have r4_20 : reg n4 (20 : Fin 32) = bp := by rw [k4 _ (by decide), r3_20]
  have r4_10 : reg n4 a0 = bw (ok) := by rw [k4 _ (by decide), r3_10]
  have r4_8 : reg n4 (8 : Fin 32) = R + BitVec.ofNat 32 0x4A3 := by rw [k4 _ (by decide), r3_8]
  have r4_9 : reg n4 (9 : Fin 32) = bw (ok) := by rw [k4 _ (by decide), r3_9]
  have r4_11 : reg n4 a1 = R + BitVec.ofNat 32 0x6AC := by rw [k4 _ (by decide), r3_11]
  have r4_12 : reg n4 a2 = BitVec.ofNat 32 40 := by rw [v4, D3.zero]; rfl
  obtain ⟨n5, c5, D5, v5, k5⟩ := D4.aluS C dec_at_27e (off' := 0x280) (by decide) (by decide)
  have r5_18 : reg n5 (18 : Fin 32) = out := by rw [k5 _ (by decide), r4_18]
  have r5_20 : reg n5 (20 : Fin 32) = bp := by rw [k5 _ (by decide), r4_20]
  have r5_8 : reg n5 (8 : Fin 32) = R + BitVec.ofNat 32 0x4A3 := by rw [k5 _ (by decide), r4_8]
  have r5_9 : reg n5 (9 : Fin 32) = bw (ok) := by rw [k5 _ (by decide), r4_9]
  have r5_11 : reg n5 a1 = R + BitVec.ofNat 32 0x6AC := by rw [k5 _ (by decide), r4_11]
  have r5_12 : reg n5 a2 = BitVec.ofNat 32 40 := by rw [k5 _ (by decide), r4_12]
  have r5_10 : reg n5 a0 = R + BitVec.ofNat 32 0x4A3 := by rw [v5, D4.zero, r4_8]; exact BitVec.zero_add _
  obtain ⟨n6, c6, D6, w6, k6, f6⟩ := D5.memcpyF C dec_at_280 dec_at_284 (by decide) (by decide) (k := 0x4A3) (j := 0x6AC) (by decide) (by decide) (by decide) (by decide) (by decide) r5_10 r5_11 r5_12
  have r6_18 : reg n6 (18 : Fin 32) = out := by rw [k6 _ (by decide), r5_18]
  have r6_20 : reg n6 (20 : Fin 32) = bp := by rw [k6 _ (by decide), r5_20]
  have r6_8 : reg n6 (8 : Fin 32) = R + BitVec.ofNat 32 0x4A3 := by rw [k6 _ (by decide), r5_8]
  have r6_9 : reg n6 (9 : Fin 32) = bw (ok) := by rw [k6 _ (by decide), r5_9]
  have m6_544 : feW n6.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f6 (by decide) (by decide) (by decide) (by decide)).trans hY
  have m6_6ac : feW n6.mem (R + BitVec.ofNat 32 0x6AC) = X := (keepW C f6 (by decide) (by decide) (by decide) (by decide)).trans hX
  have m6_4a3 : feW n6.mem (R + BitVec.ofNat 32 0x4A3) = X := by rw [w6, hX]
  obtain ⟨n7, c7, D7, v7, k7⟩ := D6.aluS C dec_at_288 (off' := 0x28A) (by decide) (by decide)
  have r7_18 : reg n7 (18 : Fin 32) = out := by rw [k7 _ (by decide), r6_18]
  have r7_20 : reg n7 (20 : Fin 32) = bp := by rw [k7 _ (by decide), r6_20]
  have r7_8 : reg n7 (8 : Fin 32) = R + BitVec.ofNat 32 0x4A3 := by rw [k7 _ (by decide), r6_8]
  have r7_9 : reg n7 (9 : Fin 32) = bw (ok) := by rw [k7 _ (by decide), r6_9]
  have r7_10 : reg n7 a0 = R + BitVec.ofNat 32 0x450 := by rw [v7, D6.zero, D6.hsp]; exact BitVec.zero_add _
  obtain ⟨n8, c8, D8, v8, k8⟩ := D7.aluImmS C dec_at_28a (off' := 0x28E) (by decide) (by decide)
  have r8_18 : reg n8 (18 : Fin 32) = out := by rw [k8 _ (by decide), r7_18]
  have r8_20 : reg n8 (20 : Fin 32) = bp := by rw [k8 _ (by decide), r7_20]
  have r8_8 : reg n8 (8 : Fin 32) = R + BitVec.ofNat 32 0x4A3 := by rw [k8 _ (by decide), r7_8]
  have r8_9 : reg n8 (9 : Fin 32) = bw (ok) := by rw [k8 _ (by decide), r7_9]
  have r8_10 : reg n8 a0 = R + BitVec.ofNat 32 0x450 := by rw [k8 _ (by decide), r7_10]
  have r8_12 : reg n8 a2 = BitVec.ofNat 32 40 := by rw [v8, D7.zero]; rfl
  obtain ⟨n9, c9, D9, v9, k9⟩ := D8.aluS C dec_at_28e (off' := 0x290) (by decide) (by decide)
  have r9_18 : reg n9 (18 : Fin 32) = out := by rw [k9 _ (by decide), r8_18]
  have r9_20 : reg n9 (20 : Fin 32) = bp := by rw [k9 _ (by decide), r8_20]
  have r9_8 : reg n9 (8 : Fin 32) = R + BitVec.ofNat 32 0x4A3 := by rw [k9 _ (by decide), r8_8]
  have r9_9 : reg n9 (9 : Fin 32) = bw (ok) := by rw [k9 _ (by decide), r8_9]
  have r9_10 : reg n9 a0 = R + BitVec.ofNat 32 0x450 := by rw [k9 _ (by decide), r8_10]
  have r9_12 : reg n9 a2 = BitVec.ofNat 32 40 := by rw [k9 _ (by decide), r8_12]
  have r9_11 : reg n9 a1 = R + BitVec.ofNat 32 0x4A3 := by rw [v9, D8.zero, r8_8]; exact BitVec.zero_add _
  obtain ⟨n10, c10, D10, w10, k10, f10⟩ := D9.memcpyF C dec_at_290 dec_at_294 (by decide) (by decide) (k := 0x450) (j := 0x4A3) (by decide) (by decide) (by decide) (by decide) (by decide) r9_10 r9_11 r9_12
  have r10_18 : reg n10 (18 : Fin 32) = out := by rw [k10 _ (by decide), r9_18]
  have r10_20 : reg n10 (20 : Fin 32) = bp := by rw [k10 _ (by decide), r9_20]
  have r10_8 : reg n10 (8 : Fin 32) = R + BitVec.ofNat 32 0x4A3 := by rw [k10 _ (by decide), r9_8]
  have r10_9 : reg n10 (9 : Fin 32) = bw (ok) := by rw [k10 _ (by decide), r9_9]
  have m10_544 : feW n10.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f10 (by decide) (by decide) (by decide) (by decide)).trans m6_544
  have m10_6ac : feW n10.mem (R + BitVec.ofNat 32 0x6AC) = X := (keepW C f10 (by decide) (by decide) (by decide) (by decide)).trans m6_6ac
  have m10_4a3 : feW n10.mem (R + BitVec.ofNat 32 0x4A3) = X := (keepW C f10 (by decide) (by decide) (by decide) (by decide)).trans m6_4a3
  have m10_450 : feW n10.mem (R + BitVec.ofNat 32 0x450) = X := by rw [w10, m6_4a3]
  obtain ⟨n11, c11, D11, v11, k11⟩ := D10.aluImmS C dec_at_298 (off' := 0x29A) (by decide) (by decide)
  have r11_18 : reg n11 (18 : Fin 32) = out := by rw [k11 _ (by decide), r10_18]
  have r11_20 : reg n11 (20 : Fin 32) = bp := by rw [k11 _ (by decide), r10_20]
  have r11_9 : reg n11 (9 : Fin 32) = bw (ok) := by rw [k11 _ (by decide), r10_9]
  have r11_8 : reg n11 (8 : Fin 32) = R + BitVec.ofNat 32 0x478 := by rw [v11, D10.hsp]; exact add_sp R rfl
  obtain ⟨n12, c12, D12, v12, k12⟩ := D11.aluImmS C dec_at_29a (off' := 0x29C) (by decide) (by decide)
  have r12_18 : reg n12 (18 : Fin 32) = out := by rw [k12 _ (by decide), r11_18]
  have r12_20 : reg n12 (20 : Fin 32) = bp := by rw [k12 _ (by decide), r11_20]
  have r12_9 : reg n12 (9 : Fin 32) = bw (ok) := by rw [k12 _ (by decide), r11_9]
  have r12_8 : reg n12 (8 : Fin 32) = R + BitVec.ofNat 32 0x478 := by rw [k12 _ (by decide), r11_8]
  have r12_11 : reg n12 a1 = R + BitVec.ofNat 32 0x544 := by rw [v12, D11.hsp]; exact add_sp R rfl
  obtain ⟨n13, c13, D13, v13, k13⟩ := D12.aluImmS C dec_at_29c (off' := 0x2A0) (by decide) (by decide)
  have r13_18 : reg n13 (18 : Fin 32) = out := by rw [k13 _ (by decide), r12_18]
  have r13_20 : reg n13 (20 : Fin 32) = bp := by rw [k13 _ (by decide), r12_20]
  have r13_9 : reg n13 (9 : Fin 32) = bw (ok) := by rw [k13 _ (by decide), r12_9]
  have r13_8 : reg n13 (8 : Fin 32) = R + BitVec.ofNat 32 0x478 := by rw [k13 _ (by decide), r12_8]
  have r13_11 : reg n13 a1 = R + BitVec.ofNat 32 0x544 := by rw [k13 _ (by decide), r12_11]
  have r13_12 : reg n13 a2 = BitVec.ofNat 32 40 := by rw [v13, D12.zero]; rfl
  obtain ⟨n14, c14, D14, v14, k14⟩ := D13.aluS C dec_at_2a0 (off' := 0x2A2) (by decide) (by decide)
  have r14_18 : reg n14 (18 : Fin 32) = out := by rw [k14 _ (by decide), r13_18]
  have r14_20 : reg n14 (20 : Fin 32) = bp := by rw [k14 _ (by decide), r13_20]
  have r14_9 : reg n14 (9 : Fin 32) = bw (ok) := by rw [k14 _ (by decide), r13_9]
  have r14_8 : reg n14 (8 : Fin 32) = R + BitVec.ofNat 32 0x478 := by rw [k14 _ (by decide), r13_8]
  have r14_11 : reg n14 a1 = R + BitVec.ofNat 32 0x544 := by rw [k14 _ (by decide), r13_11]
  have r14_12 : reg n14 a2 = BitVec.ofNat 32 40 := by rw [k14 _ (by decide), r13_12]
  have r14_10 : reg n14 a0 = R + BitVec.ofNat 32 0x478 := by rw [v14, D13.zero, r13_8]; exact BitVec.zero_add _
  obtain ⟨n15, c15, D15, w15, k15, f15⟩ := D14.memcpyF C dec_at_2a2 dec_at_2a6 (by decide) (by decide) (k := 0x478) (j := 0x544) (by decide) (by decide) (by decide) (by decide) (by decide) r14_10 r14_11 r14_12
  have r15_18 : reg n15 (18 : Fin 32) = out := by rw [k15 _ (by decide), r14_18]
  have r15_20 : reg n15 (20 : Fin 32) = bp := by rw [k15 _ (by decide), r14_20]
  have r15_9 : reg n15 (9 : Fin 32) = bw (ok) := by rw [k15 _ (by decide), r14_9]
  have r15_8 : reg n15 (8 : Fin 32) = R + BitVec.ofNat 32 0x478 := by rw [k15 _ (by decide), r14_8]
  have m15_544 : feW n15.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f15 (by decide) (by decide) (by decide) (by decide)).trans m10_544
  have m15_6ac : feW n15.mem (R + BitVec.ofNat 32 0x6AC) = X := (keepW C f15 (by decide) (by decide) (by decide) (by decide)).trans m10_6ac
  have m15_4a3 : feW n15.mem (R + BitVec.ofNat 32 0x4A3) = X := (keepW C f15 (by decide) (by decide) (by decide) (by decide)).trans m10_4a3
  have m15_450 : feW n15.mem (R + BitVec.ofNat 32 0x450) = X := (keepW C f15 (by decide) (by decide) (by decide) (by decide)).trans m10_450
  have m15_478 : feW n15.mem (R + BitVec.ofNat 32 0x478) = Y := by rw [w15, m10_544]
  obtain ⟨n16, c16, D16, v16, k16⟩ := D15.aluImmS C dec_at_2aa (off' := 0x2AC) (by decide) (by decide)
  have r16_18 : reg n16 (18 : Fin 32) = out := by rw [k16 _ (by decide), r15_18]
  have r16_20 : reg n16 (20 : Fin 32) = bp := by rw [k16 _ (by decide), r15_20]
  have r16_9 : reg n16 (9 : Fin 32) = bw (ok) := by rw [k16 _ (by decide), r15_9]
  have r16_8 : reg n16 (8 : Fin 32) = R + BitVec.ofNat 32 0x478 := by rw [k16 _ (by decide), r15_8]
  have r16_10 : reg n16 a0 = R + BitVec.ofNat 32 0x6AC := by rw [v16, D15.hsp]; exact add_sp R rfl
  obtain ⟨n17, c17, D17, v17, k17⟩ := D16.aluImmS C dec_at_2ac (off' := 0x2B0) (by decide) (by decide)
  have r17_18 : reg n17 (18 : Fin 32) = out := by rw [k17 _ (by decide), r16_18]
  have r17_20 : reg n17 (20 : Fin 32) = bp := by rw [k17 _ (by decide), r16_20]
  have r17_9 : reg n17 (9 : Fin 32) = bw (ok) := by rw [k17 _ (by decide), r16_9]
  have r17_8 : reg n17 (8 : Fin 32) = R + BitVec.ofNat 32 0x478 := by rw [k17 _ (by decide), r16_8]
  have r17_10 : reg n17 a0 = R + BitVec.ofNat 32 0x6AC := by rw [k17 _ (by decide), r16_10]
  have r17_12 : reg n17 a2 = BitVec.ofNat 32 40 := by rw [v17, D16.zero]; rfl
  obtain ⟨n18, c18, D18, v18, k18⟩ := D17.aluS C dec_at_2b0 (off' := 0x2B2) (by decide) (by decide)
  have r18_18 : reg n18 (18 : Fin 32) = out := by rw [k18 _ (by decide), r17_18]
  have r18_20 : reg n18 (20 : Fin 32) = bp := by rw [k18 _ (by decide), r17_20]
  have r18_9 : reg n18 (9 : Fin 32) = bw (ok) := by rw [k18 _ (by decide), r17_9]
  have r18_8 : reg n18 (8 : Fin 32) = R + BitVec.ofNat 32 0x478 := by rw [k18 _ (by decide), r17_8]
  have r18_10 : reg n18 a0 = R + BitVec.ofNat 32 0x6AC := by rw [k18 _ (by decide), r17_10]
  have r18_12 : reg n18 a2 = BitVec.ofNat 32 40 := by rw [k18 _ (by decide), r17_12]
  have r18_11 : reg n18 a1 = R + BitVec.ofNat 32 0x478 := by rw [v18, D17.zero, r17_8]; exact BitVec.zero_add _
  obtain ⟨n19, c19, D19, w19, k19, f19⟩ := D18.memcpyF C dec_at_2b2 dec_at_2b6 (by decide) (by decide) (k := 0x6AC) (j := 0x478) (by decide) (by decide) (by decide) (by decide) (by decide) r18_10 r18_11 r18_12
  have r19_18 : reg n19 (18 : Fin 32) = out := by rw [k19 _ (by decide), r18_18]
  have r19_20 : reg n19 (20 : Fin 32) = bp := by rw [k19 _ (by decide), r18_20]
  have r19_9 : reg n19 (9 : Fin 32) = bw (ok) := by rw [k19 _ (by decide), r18_9]
  have r19_8 : reg n19 (8 : Fin 32) = R + BitVec.ofNat 32 0x478 := by rw [k19 _ (by decide), r18_8]
  have m19_544 : feW n19.mem (R + BitVec.ofNat 32 0x544) = Y := (keepW C f19 (by decide) (by decide) (by decide) (by decide)).trans m15_544
  have m19_4a3 : feW n19.mem (R + BitVec.ofNat 32 0x4A3) = X := (keepW C f19 (by decide) (by decide) (by decide) (by decide)).trans m15_4a3
  have m19_450 : feW n19.mem (R + BitVec.ofNat 32 0x450) = X := (keepW C f19 (by decide) (by decide) (by decide) (by decide)).trans m15_450
  have m19_478 : feW n19.mem (R + BitVec.ofNat 32 0x478) = Y := (keepW C f19 (by decide) (by decide) (by decide) (by decide)).trans m15_478
  have m19_6ac : feW n19.mem (R + BitVec.ofNat 32 0x6AC) = Y := by rw [w19, m15_478]
  exact ⟨n19, c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans (c11.trans (c12.trans (c13.trans (c14.trans (c15.trans (c16.trans (c17.trans (c18.trans (c19)))))))))))))))))), D19, r19_18, r19_20, r19_9, m19_450, m19_6ac⟩


theorem sign_bw : ∀ x : BitVec 8, aluEval .srl (x.zeroExtend 32) 7 = bw (x.toNat / 128 == 1) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- From offset 0x2BC, where `u / v` is a square, to 0x31C: `X` negated by
the encoding's sign bit, and `X`, `Y`, `1`, and `X Y` in the frame from
offset 0x50, ready to copy out. -/
theorem dec_ph4b (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm 0x2BC) {out bp : Word} {X Y one : List Nat}
    (hs2 : reg nm (18 : Fin 32) = out) (hs4 : reg nm (20 : Fin 32) = bp) (sB : Sep bp 32 R 0x6F0)
    (hX : feW M (R + BitVec.ofNat 32 0x450) = X) (hY : feW M (R + BitVec.ofNat 32 0x6AC) = Y)
    (sO : Sep (BitVec.ofNat 32 edOneAddress) 40 R 0x6F0) (hO : feW M0 (BitVec.ofNat 32 edOneAddress) = one) :
    ∃ nm', Steps nm nm' ∧ DecSt M0 Ms R r0 nm'.mem nm' 0x31C ∧ reg nm' (18 : Fin 32) = out ∧
      feW nm'.mem (R + BitVec.ofNat 32 0x4A0) = condNegL (X) (byteN M0 bp 31 / 128 == 1) ∧
      feW nm'.mem (R + BitVec.ofNat 32 0x4C8) = Y ∧ feW nm'.mem (R + BitVec.ofNat 32 0x4F0) = one ∧
      feW nm'.mem (R + BitVec.ofNat 32 0x518) = mulL (condNegL (X) (byteN M0 bp 31 / 128 == 1)) (Y) := by
  obtain ⟨nA, cA, DA, vA, kA⟩ := D.lbuS C dec_at_2bc (off' := 0x2C0) (by decide) (by decide)
  obtain ⟨nB, cB, DB, vB, kB⟩ := DA.aluImmS C dec_at_2c0 (off' := 0x2C2) (by decide) (by decide)
  have aB : reg nB a0 = bw (byteN M0 bp 31 / 128 == 1) := by
    rw [vB, vA, hs4, show bp + (0x1F : Word) = bp + BitVec.ofNat 32 31 from rfl, D.bytes sB 31 (by decide)]
    exact sign_bw _
  have rB_18 : reg nB (18 : Fin 32) = out := by rw [kB _ (by decide), kA _ (by decide), hs2]
  have rB_20 : reg nB (20 : Fin 32) = bp := by rw [kB _ (by decide), kA _ (by decide), hs4]
  obtain ⟨n1, c1, D1, w1, k1, f1⟩ := DB.blackBox C dec_at_2c2 dec_at_2c6 (by decide) (by decide)
  have r1_18 : reg n1 (18 : Fin 32) = out := by rw [k1 _ (by decide) (by decide), rB_18]
  have r1_20 : reg n1 (20 : Fin 32) = bp := by rw [k1 _ (by decide) (by decide), rB_20]
  have m1_450 : feW n1.mem (R + BitVec.ofNat 32 0x450) = X := (keepW0 C f1 (by decide) (by decide)).trans hX
  have m1_6ac : feW n1.mem (R + BitVec.ofNat 32 0x6AC) = Y := (keepW0 C f1 (by decide) (by decide)).trans hY
  have r1_10 : reg n1 a0 = bw (byteN M0 bp 31 / 128 == 1) := by rw [w1, aB, bw_bb]
  obtain ⟨n2, c2, D2, v2, k2⟩ := D1.aluImmS C dec_at_2ca (off' := 0x2CE) (by decide) (by decide)
  have r2_18 : reg n2 (18 : Fin 32) = out := by rw [k2 _ (by decide), r1_18]
  have r2_20 : reg n2 (20 : Fin 32) = bp := by rw [k2 _ (by decide), r1_20]
  have r2_10 : reg n2 a0 = bw (byteN M0 bp 31 / 128 == 1) := by rw [k2 _ (by decide), r1_10]
  have r2_11 : reg n2 a1 = bw (byteN M0 bp 31 / 128 == 1) := by rw [v2, r1_10, bw_zext]
  obtain ⟨n3, c3, D3, v3, k3⟩ := D2.aluS C dec_at_2ce (off' := 0x2D0) (by decide) (by decide)
  have r3_18 : reg n3 (18 : Fin 32) = out := by rw [k3 _ (by decide), r2_18]
  have r3_20 : reg n3 (20 : Fin 32) = bp := by rw [k3 _ (by decide), r2_20]
  have r3_11 : reg n3 a1 = bw (byteN M0 bp 31 / 128 == 1) := by rw [k3 _ (by decide), r2_11]
  have r3_10 : reg n3 a0 = R + BitVec.ofNat 32 0x450 := by rw [v3, D2.zero, D2.hsp]; exact BitVec.zero_add _
  obtain ⟨n4, c4, D4, w4, k4, f4⟩ := D3.condNeg C dec_at_2d0 dec_at_2d4 (by decide) (by decide) (k := 0x450) (by decide) (by decide) (by decide) r3_10 r3_11 (bw_01 _)
  have r4_18 : reg n4 (18 : Fin 32) = out := by rw [k4 _ (by decide), r3_18]
  have r4_20 : reg n4 (20 : Fin 32) = bp := by rw [k4 _ (by decide), r3_20]
  have m4_6ac : feW n4.mem (R + BitVec.ofNat 32 0x6AC) = Y := (keepW C f4 (by decide) (by decide) (by decide) (by decide)).trans m1_6ac
  have m4_450 : feW n4.mem (R + BitVec.ofNat 32 0x450) = condNegL (X) (byteN M0 bp 31 / 128 == 1) := by rw [w4, m1_450, bw_beq]
  obtain ⟨n5, c5, D5, v5, k5⟩ := D4.aluImmS C dec_at_2d8 (off' := 0x2DA) (by decide) (by decide)
  have r5_18 : reg n5 (18 : Fin 32) = out := by rw [k5 _ (by decide), r4_18]
  have r5_20 : reg n5 (20 : Fin 32) = bp := by rw [k5 _ (by decide), r4_20]
  have r5_10 : reg n5 a0 = R + BitVec.ofNat 32 0x4A0 := by rw [v5, D4.hsp]; exact add_sp R rfl
  obtain ⟨n6, c6, D6, v6, k6⟩ := D5.aluS C dec_at_2da (off' := 0x2DC) (by decide) (by decide)
  have r6_18 : reg n6 (18 : Fin 32) = out := by rw [k6 _ (by decide), r5_18]
  have r6_20 : reg n6 (20 : Fin 32) = bp := by rw [k6 _ (by decide), r5_20]
  have r6_10 : reg n6 a0 = R + BitVec.ofNat 32 0x4A0 := by rw [k6 _ (by decide), r5_10]
  have r6_11 : reg n6 a1 = R + BitVec.ofNat 32 0x450 := by rw [v6, D5.zero, D5.hsp]; exact BitVec.zero_add _
  obtain ⟨n7, c7, D7, v7, k7⟩ := D6.aluImmS C dec_at_2dc (off' := 0x2E0) (by decide) (by decide)
  have r7_18 : reg n7 (18 : Fin 32) = out := by rw [k7 _ (by decide), r6_18]
  have r7_20 : reg n7 (20 : Fin 32) = bp := by rw [k7 _ (by decide), r6_20]
  have r7_10 : reg n7 a0 = R + BitVec.ofNat 32 0x4A0 := by rw [k7 _ (by decide), r6_10]
  have r7_11 : reg n7 a1 = R + BitVec.ofNat 32 0x450 := by rw [k7 _ (by decide), r6_11]
  have r7_12 : reg n7 a2 = BitVec.ofNat 32 40 := by rw [v7, D6.zero]; rfl
  obtain ⟨n8, c8, D8, w8, k8, f8⟩ := D7.memcpyF C dec_at_2e0 dec_at_2e4 (by decide) (by decide) (k := 0x4A0) (j := 0x450) (by decide) (by decide) (by decide) (by decide) (by decide) r7_10 r7_11 r7_12
  have r8_18 : reg n8 (18 : Fin 32) = out := by rw [k8 _ (by decide), r7_18]
  have r8_20 : reg n8 (20 : Fin 32) = bp := by rw [k8 _ (by decide), r7_20]
  have m8_6ac : feW n8.mem (R + BitVec.ofNat 32 0x6AC) = Y := (keepW C f8 (by decide) (by decide) (by decide) (by decide)).trans m4_6ac
  have m8_450 : feW n8.mem (R + BitVec.ofNat 32 0x450) = condNegL (X) (byteN M0 bp 31 / 128 == 1) := (keepW C f8 (by decide) (by decide) (by decide) (by decide)).trans m4_450
  have m8_4a0 : feW n8.mem (R + BitVec.ofNat 32 0x4A0) = condNegL (X) (byteN M0 bp 31 / 128 == 1) := by rw [w8, m4_450]
  obtain ⟨n9, c9, D9, v9, k9⟩ := D8.aluImmS C dec_at_2e8 (off' := 0x2EA) (by decide) (by decide)
  have r9_18 : reg n9 (18 : Fin 32) = out := by rw [k9 _ (by decide), r8_18]
  have r9_20 : reg n9 (20 : Fin 32) = bp := by rw [k9 _ (by decide), r8_20]
  have r9_10 : reg n9 a0 = R + BitVec.ofNat 32 0x518 := by rw [v9, D8.hsp]; exact add_sp R rfl
  obtain ⟨n10, c10, D10, v10, k10⟩ := D9.aluS C dec_at_2ea (off' := 0x2EC) (by decide) (by decide)
  have r10_18 : reg n10 (18 : Fin 32) = out := by rw [k10 _ (by decide), r9_18]
  have r10_20 : reg n10 (20 : Fin 32) = bp := by rw [k10 _ (by decide), r9_20]
  have r10_10 : reg n10 a0 = R + BitVec.ofNat 32 0x518 := by rw [k10 _ (by decide), r9_10]
  have r10_11 : reg n10 a1 = R + BitVec.ofNat 32 0x450 := by rw [v10, D9.zero, D9.hsp]; exact BitVec.zero_add _
  obtain ⟨n11, c11, D11, v11, k11⟩ := D10.aluImmS C dec_at_2ec (off' := 0x2EE) (by decide) (by decide)
  have r11_18 : reg n11 (18 : Fin 32) = out := by rw [k11 _ (by decide), r10_18]
  have r11_20 : reg n11 (20 : Fin 32) = bp := by rw [k11 _ (by decide), r10_20]
  have r11_10 : reg n11 a0 = R + BitVec.ofNat 32 0x518 := by rw [k11 _ (by decide), r10_10]
  have r11_11 : reg n11 a1 = R + BitVec.ofNat 32 0x450 := by rw [k11 _ (by decide), r10_11]
  have r11_12 : reg n11 a2 = R + BitVec.ofNat 32 0x6AC := by rw [v11, D10.hsp]; exact add_sp R rfl
  obtain ⟨n12, c12, D12, w12, k12, f12⟩ := D11.mul C dec_at_2ee dec_at_2f2 (by decide) (by decide) (k := 0x518) (by decide) (by decide) (by decide) r11_10 (by rw [r11_11]; exact C.opF (by decide) (by decide) (by decide)) (by rw [r11_12]; exact C.opF (by decide) (by decide) (by decide))
  have r12_18 : reg n12 (18 : Fin 32) = out := by rw [k12 _ (by decide), r11_18]
  have r12_20 : reg n12 (20 : Fin 32) = bp := by rw [k12 _ (by decide), r11_20]
  have m12_6ac : feW n12.mem (R + BitVec.ofNat 32 0x6AC) = Y := (keepW C f12 (by decide) (by decide) (by decide) (by decide)).trans m8_6ac
  have m12_450 : feW n12.mem (R + BitVec.ofNat 32 0x450) = condNegL (X) (byteN M0 bp 31 / 128 == 1) := (keepW C f12 (by decide) (by decide) (by decide) (by decide)).trans m8_450
  have m12_4a0 : feW n12.mem (R + BitVec.ofNat 32 0x4A0) = condNegL (X) (byteN M0 bp 31 / 128 == 1) := (keepW C f12 (by decide) (by decide) (by decide) (by decide)).trans m8_4a0
  have m12_518 : feW n12.mem (R + BitVec.ofNat 32 0x518) = mulL (condNegL (X) (byteN M0 bp 31 / 128 == 1)) (Y) := by rw [w12, r11_11, r11_12, m8_450, m8_6ac]
  obtain ⟨n13, c13, D13, v13, k13⟩ := D12.aluImmS C dec_at_2f6 (off' := 0x2F8) (by decide) (by decide)
  have r13_18 : reg n13 (18 : Fin 32) = out := by rw [k13 _ (by decide), r12_18]
  have r13_20 : reg n13 (20 : Fin 32) = bp := by rw [k13 _ (by decide), r12_20]
  have r13_10 : reg n13 a0 = R + BitVec.ofNat 32 0x4C8 := by rw [v13, D12.hsp]; exact add_sp R rfl
  obtain ⟨n14, c14, D14, v14, k14⟩ := D13.aluImmS C dec_at_2f8 (off' := 0x2FA) (by decide) (by decide)
  have r14_18 : reg n14 (18 : Fin 32) = out := by rw [k14 _ (by decide), r13_18]
  have r14_20 : reg n14 (20 : Fin 32) = bp := by rw [k14 _ (by decide), r13_20]
  have r14_10 : reg n14 a0 = R + BitVec.ofNat 32 0x4C8 := by rw [k14 _ (by decide), r13_10]
  have r14_11 : reg n14 a1 = R + BitVec.ofNat 32 0x6AC := by rw [v14, D13.hsp]; exact add_sp R rfl
  obtain ⟨n15, c15, D15, v15, k15⟩ := D14.aluImmS C dec_at_2fa (off' := 0x2FE) (by decide) (by decide)
  have r15_18 : reg n15 (18 : Fin 32) = out := by rw [k15 _ (by decide), r14_18]
  have r15_20 : reg n15 (20 : Fin 32) = bp := by rw [k15 _ (by decide), r14_20]
  have r15_10 : reg n15 a0 = R + BitVec.ofNat 32 0x4C8 := by rw [k15 _ (by decide), r14_10]
  have r15_11 : reg n15 a1 = R + BitVec.ofNat 32 0x6AC := by rw [k15 _ (by decide), r14_11]
  have r15_12 : reg n15 a2 = BitVec.ofNat 32 40 := by rw [v15, D14.zero]; rfl
  obtain ⟨n16, c16, D16, w16, k16, f16⟩ := D15.memcpyF C dec_at_2fe dec_at_302 (by decide) (by decide) (k := 0x4C8) (j := 0x6AC) (by decide) (by decide) (by decide) (by decide) (by decide) r15_10 r15_11 r15_12
  have r16_18 : reg n16 (18 : Fin 32) = out := by rw [k16 _ (by decide), r15_18]
  have r16_20 : reg n16 (20 : Fin 32) = bp := by rw [k16 _ (by decide), r15_20]
  have m16_6ac : feW n16.mem (R + BitVec.ofNat 32 0x6AC) = Y := (keepW C f16 (by decide) (by decide) (by decide) (by decide)).trans m12_6ac
  have m16_450 : feW n16.mem (R + BitVec.ofNat 32 0x450) = condNegL (X) (byteN M0 bp 31 / 128 == 1) := (keepW C f16 (by decide) (by decide) (by decide) (by decide)).trans m12_450
  have m16_4a0 : feW n16.mem (R + BitVec.ofNat 32 0x4A0) = condNegL (X) (byteN M0 bp 31 / 128 == 1) := (keepW C f16 (by decide) (by decide) (by decide) (by decide)).trans m12_4a0
  have m16_518 : feW n16.mem (R + BitVec.ofNat 32 0x518) = mulL (condNegL (X) (byteN M0 bp 31 / 128 == 1)) (Y) := (keepW C f16 (by decide) (by decide) (by decide) (by decide)).trans m12_518
  have m16_4c8 : feW n16.mem (R + BitVec.ofNat 32 0x4C8) = Y := by rw [w16, m12_6ac]
  obtain ⟨n17, c17, D17, v17, k17⟩ := D16.aluImmS C dec_at_306 (off' := 0x308) (by decide) (by decide)
  have r17_18 : reg n17 (18 : Fin 32) = out := by rw [k17 _ (by decide), r16_18]
  have r17_20 : reg n17 (20 : Fin 32) = bp := by rw [k17 _ (by decide), r16_20]
  have r17_10 : reg n17 a0 = R + BitVec.ofNat 32 0x4F0 := by rw [v17, D16.hsp]; exact add_sp R rfl
  obtain ⟨n18, c18, D18, v18, k18⟩ := D17.luiS C dec_at_308 (off' := 0x30C) (by decide) (by decide)
  have r18_18 : reg n18 (18 : Fin 32) = out := by rw [k18 _ (by decide), r17_18]
  have r18_20 : reg n18 (20 : Fin 32) = bp := by rw [k18 _ (by decide), r17_20]
  have r18_10 : reg n18 a0 = R + BitVec.ofNat 32 0x4F0 := by rw [k18 _ (by decide), r17_10]
  obtain ⟨n19, c19, D19, v19, k19⟩ := D18.aluImmS C dec_at_30c (off' := 0x310) (by decide) (by decide)
  have r19_18 : reg n19 (18 : Fin 32) = out := by rw [k19 _ (by decide), r18_18]
  have r19_20 : reg n19 (20 : Fin 32) = bp := by rw [k19 _ (by decide), r18_20]
  have r19_10 : reg n19 a0 = R + BitVec.ofNat 32 0x4F0 := by rw [k19 _ (by decide), r18_10]
  have r19_11 : reg n19 a1 = BitVec.ofNat 32 edOneAddress := by rw [v19, v18]; decide
  obtain ⟨n20, c20, D20, v20, k20⟩ := D19.aluImmS C dec_at_310 (off' := 0x314) (by decide) (by decide)
  have r20_18 : reg n20 (18 : Fin 32) = out := by rw [k20 _ (by decide), r19_18]
  have r20_20 : reg n20 (20 : Fin 32) = bp := by rw [k20 _ (by decide), r19_20]
  have r20_10 : reg n20 a0 = R + BitVec.ofNat 32 0x4F0 := by rw [k20 _ (by decide), r19_10]
  have r20_11 : reg n20 a1 = BitVec.ofNat 32 edOneAddress := by rw [k20 _ (by decide), r19_11]
  have r20_12 : reg n20 a2 = BitVec.ofNat 32 40 := by rw [v20, D19.zero]; rfl
  obtain ⟨n21, c21, D21, w21, k21, f21⟩ := D20.memcpyC C dec_at_314 dec_at_318 (by decide) (by decide) (k := 0x4F0) (by decide) (by decide) sO (by decide) r20_10 r20_11 r20_12
  have r21_18 : reg n21 (18 : Fin 32) = out := by rw [k21 _ (by decide), r20_18]
  have r21_20 : reg n21 (20 : Fin 32) = bp := by rw [k21 _ (by decide), r20_20]
  have m21_6ac : feW n21.mem (R + BitVec.ofNat 32 0x6AC) = Y := (keepW C f21 (by decide) (by decide) (by decide) (by decide)).trans m16_6ac
  have m21_450 : feW n21.mem (R + BitVec.ofNat 32 0x450) = condNegL (X) (byteN M0 bp 31 / 128 == 1) := (keepW C f21 (by decide) (by decide) (by decide) (by decide)).trans m16_450
  have m21_4a0 : feW n21.mem (R + BitVec.ofNat 32 0x4A0) = condNegL (X) (byteN M0 bp 31 / 128 == 1) := (keepW C f21 (by decide) (by decide) (by decide) (by decide)).trans m16_4a0
  have m21_518 : feW n21.mem (R + BitVec.ofNat 32 0x518) = mulL (condNegL (X) (byteN M0 bp 31 / 128 == 1)) (Y) := (keepW C f21 (by decide) (by decide) (by decide) (by decide)).trans m16_518
  have m21_4c8 : feW n21.mem (R + BitVec.ofNat 32 0x4C8) = Y := (keepW C f21 (by decide) (by decide) (by decide) (by decide)).trans m16_4c8
  have m21_4f0 : feW n21.mem (R + BitVec.ofNat 32 0x4F0) = one := by rw [w21, D20.constW sO, hO]
  exact ⟨n21, cA.trans (cB.trans (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans (c9.trans (c10.trans (c11.trans (c12.trans (c13.trans (c14.trans (c15.trans (c16.trans (c17.trans (c18.trans (c19.trans (c20.trans (c21)))))))))))))))))))))), D21, r21_18, m21_4a0, m21_4c8, m21_4f0, m21_518⟩


/-- What `decompress` leaves at `out`: the tag 1 and the point's `X`, `Y`,
`Z`, `T` limbs after it, or the tag 0. -/
def DecOut (M : Word → BitVec 8) (out : Word) : Option (List Nat × List Nat × List Nat × List Nat) → Prop
  | some (X, Y, Z, T) => memLoad32 M out = 1 ∧ feW M (out + BitVec.ofNat 32 4) = X ∧
      feW M (out + BitVec.ofNat 32 4 + BitVec.ofNat 32 40) = Y ∧
      feW M (out + BitVec.ofNat 32 4 + BitVec.ofNat 32 80) = Z ∧
      feW M (out + BitVec.ofNat 32 4 + BitVec.ofNat 32 120) = T
  | none => memLoad32 M out = 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- From the branch at 0x2BA to the return, on the choice `ok` in `s1`. -/
theorem dec_finish (C : DecCtx M0 R) (D : DecSt M0 Ms R r0 M nm 0x2BA) {out bp : Word} {X Y one : List Nat}
    {ok : Bool} {rM : Fin 32 → Word}
    (hs2 : reg nm (18 : Fin 32) = out) (hs4 : reg nm (20 : Fin 32) = bp) (hs1 : reg nm (9 : Fin 32) = bw ok)
    (hX : feW M (R + BitVec.ofNat 32 0x450) = X) (hY : feW M (R + BitVec.ofNat 32 0x6AC) = Y)
    (sB : Sep bp 32 R 0x6F0) (sO : Sep (BitVec.ofNat 32 edOneAddress) 40 R 0x6F0)
    (hO : feW M0 (BitVec.ofNat 32 edOneAddress) = one) (hout : out.toNat % 4 = 0) (sOR : Sep out 0xA4 R 0x6F0)
    (hoW : out.toNat + 0xA4 ≤ 0x40000000)
    (hsl : ∀ r o, (r, o) ∈ decPs → memLoad32 Ms (R + BitVec.ofNat 32 0x6D0 + o) = rM r)
    (hret : rM ra &&& ~~~1 = rM ra) :
    ∃ m', Steps nm m' ∧ m'.pc = rM ra ∧ reg m' sp = R + BitVec.ofNat 32 0x6F0 ∧
      (∀ r o, (r, o) ∈ decPs → reg m' r = rM r) ∧
      (∀ q, q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] → reg m' q = r0 q) ∧
      DecOut m'.mem out (if ok then
        some (condNegL X ((memBytes M0 bp 32).getD 31 0 / 128 == 1), Y, one,
          mulL (condNegL X ((memBytes M0 bp 32).getD 31 0 / 128 == 1)) Y) else none) ∧
      ∀ x, Sep R 0x6F0 x 1 → Sep out 0xA4 x 1 → m'.mem x = M0 x := by
  have hc := C.code D.agree C.E.cod (by decide) (by decide)
  rw [getD_memBytes M0 bp (by decide : 31 < 32)]
  cases ok
  · obtain ⟨n1, d1, u1⟩ := D.st.taken hc 0x332 dec_at_2ba (by decide) (by rw [hs1, D.zero]; decide)
    have D1 : DecSt M0 Ms R r0 M n1 0x332 :=
      ⟨u1.self, by rw [u1.regs, D.hsp], fun q hq => by rw [u1.regs, D.keep q hq], D.agree, D.slots⟩
    obtain ⟨m', c', pc', sp', sv', kp', tag, fr⟩ := dec_none C D1 (by rw [u1.regs, hs2]) hout sOR hoW hsl hret
    exact ⟨m', .cons d1 c', pc', sp', sv', kp', tag, fr⟩
  · obtain ⟨n1, d1, u1⟩ := D.st.notTaken hc 0x2BC dec_at_2ba (by decide) (by rw [hs1, D.zero]; decide)
    have D1 : DecSt M0 Ms R r0 M n1 0x2BC :=
      ⟨u1.self, by rw [u1.regs, D.hsp], fun q hq => by rw [u1.regs, D.keep q hq], D.agree, D.slots⟩
    obtain ⟨n2, c2, D2, s2_2, hX2, hY2, hO2, hT2⟩ := dec_ph4b C D1 (by rw [u1.regs, hs2]) (by rw [u1.regs, hs4]) sB
      (by rw [hX]) (by rw [hY]) sO hO
    obtain ⟨m', c', pc', sp', sv', kp', tag, hk, fr⟩ := dec_some C D2 s2_2 hout sOR hoW hsl hret
    refine ⟨m', .cons d1 (c2.trans c'), pc', sp', sv', kp', ⟨tag, ?_, ?_, ?_, ?_⟩, fr⟩
    · have := hk 0 (by decide)
      rw [show 40 * 0 = 0 from rfl, add_ofNat_zero, add_ofNat_zero] at this
      rw [this, hX2]
    · have := hk 1 (by decide)
      rw [show 40 * 1 = 40 from rfl, add_ofNat_assoc R 0x4A0 40] at this
      rw [this, hY2]
    · have := hk 2 (by decide)
      rw [show 40 * 2 = 80 from rfl, add_ofNat_assoc R 0x4A0 80] at this
      rw [this, hO2]
    · have := hk 3 (by decide)
      rw [show 40 * 3 = 120 from rfl, add_ofNat_assoc R 0x4A0 120] at this
      rw [this, hT2]

/-- `decSpec` in the order the compiled code computes it. -/
theorem decSpec_eq (one d sm : List Nat) (b : Bytes) :
    decSpec one d sm b =
      (let Y := redL (decLoad b)
       let u := subL (sqL Y) one
       let v := addL (mulL (sqL Y) d) one
       let rr := mulL (mulL u (mulL (sqL v) v)) (mulL (mulL u (mulL (sqL (mulL (sqL v) v)) v))
         (sqIter 2 (pw19L (mulL u (mulL (sqL (mulL (sqL v) v)) v)))))
       let chk := mulL v (sqL rr)
       let r1 := if (feEqL chk (mulL (negL u) sm)) || (feEqL chk (negL u)) then mulL sm rr else rr
       let X := condNegL (condNegL r1 (isNegL r1)) (b.getD 31 0 / 128 == 1)
       if (feEqL chk (negL u)) || (feEqL chk u) then some (X, Y, one, mulL X Y) else none) := by
  unfold decSpec decSqrtRatio
  simp only [Bool.or_comm]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The compiled `CompressedEdwardsY::decompress`.** Called with the 32
bytes at `bp` and the result slot at `out`, it writes `decSpec` of the
bytes, with the image's `ONE`, `EDWARDS_D`, and `SQRT_M1`, to `out`: the
tag 1 and the point's extended coordinates, or the tag 0. It returns with
`sp` and the callee-saved registers restored and writes nothing outside
`out`'s 0xA4 bytes and the 0x6F0 bytes of stack below `sp`. -/
theorem edDecompress_correct (m : Machine) {sp0 out bp retAddr : Word} (E : DecEnv m.mem)
    (hpc : m.pc = DEC) (ha0 : reg m a0 = out) (ha1 : reg m a1 = bp) (hra : reg m ra = retAddr)
    (hret : retAddr &&& ~~~1 = retAddr) (hsp : reg m sp = sp0) (hsa : sp0.toNat % 4 = 0)
    (hsl : 0x6F0 ≤ sp0.toNat) (hsw : sp0.toNat ≤ 0x40000000) (hout : out.toNat % 4 = 0)
    (hoW : out.toNat + 0xA4 ≤ 0x40000000)
    (sOG : Sep out 0xA4 (sp0 + 0xFFFFF910) 0x6F0) (sBG : Sep bp 32 (sp0 + 0xFFFFF910) 0x6F0)
    (sO : Sep (BitVec.ofNat 32 edOneAddress) 40 (sp0 + 0xFFFFF910) 0x6F0)
    (sD : Sep (BitVec.ofNat 32 edDAddress) 40 (sp0 + 0xFFFFF910) 0x6F0)
    (sS : Sep (BitVec.ofNat 32 edSqrtM1Address) 40 (sp0 + 0xFFFFF910) 0x6F0) :
    ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' sp = sp0 ∧
      (∀ q, q.val ∈ [1, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → reg m' q = reg m q) ∧
      DecOut m'.mem out (decSpec (feW m.mem (BitVec.ofNat 32 edOneAddress)) (feW m.mem (BitVec.ofNat 32 edDAddress))
        (feW m.mem (BitVec.ofNat 32 edSqrtM1Address)) (memBytes m.mem bp 32)) ∧
      ∀ x, Sep (sp0 + 0xFFFFF910) 0x6F0 x 1 → Sep out 0xA4 x 1 → m'.mem x = m.mem x := by
  obtain ⟨R, hR⟩ : ∃ R, sp0 + 0xFFFFF910 = R := ⟨_, rfl⟩
  rw [hR] at sOG sBG sO sD sS ⊢
  have hRn : R.toNat = sp0.toNat - 0x6F0 := by
    rw [← hR, BitVec.toNat_add, show (0xFFFFF910 : Word).toNat = 2 ^ 32 - 0x6F0 from rfl]; omega
  have C : DecCtx m.mem R := ⟨E, by omega, by omega⟩
  have eF : sp0 + 0xFFFFFD60 = R + BitVec.ofNat 32 0x450 := by rw [← hR, BitVec.add_assoc]; rfl
  have eS : R + BitVec.ofNat 32 0x6F0 = sp0 := by rw [← hR, BitVec.add_assoc]; exact BitVec.add_zero sp0
  have hc := E.cod
  have st0 : St m.mem DEC m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  obtain ⟨m1, d1, u1⟩ := st0.aluImm hc dec_at_0 (off' := 4) (by decide)
  obtain ⟨m2, d2, u2⟩ := u1.self.aluImm hc dec_at_4 (off' := 6) (by decide)
  have sp1 : reg m1 sp = R + BitVec.ofNat 32 0x450 := by rw [u1.upd_eq (by decide), hsp]; exact eF
  have sp2 : reg m2 sp = R + BitVec.ofNat 32 0x450 := by rw [u2.upd_ne u1.self.zero sp (by decide), sp1]
  have a22 : reg m2 a2 = R + BitVec.ofNat 32 0x6D0 := by rw [u2.upd_eq (by decide), sp1]; exact add_sp R rfl
  have r2 : ∀ q, q ≠ sp → q ≠ a2 → reg m2 q = reg m q := fun q h1 h2 => by
    rw [u2.upd_ne u1.self.zero q h2, u1.upd_ne st0.zero q h1]
  obtain ⟨m3, c3, u3⟩ := St.block (saveBlockR a2 decPs) u2.self hc decSave_end (saveBlockR_ok a2 _ decPs _ fun p hp => by
    rw [a22]
    simp only [decPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by rw [add_ofNat_assoc]; exact aligned_add C.hR (by decide),
        by rw [add_ofNat_assoc]; exact C.hiSep (by decide) (by decide) (by decide)⟩)
  rw [saveBlockR_run, a22] at u3
  obtain ⟨Ms, hMs⟩ : ∃ Ms, saveMem m.mem (R + BitVec.ofNat 32 0x6D0) (reg m2) decPs = Ms := ⟨_, rfl⟩
  rw [hMs] at u3
  dsimp only at u3
  have D0 : DecSt m.mem Ms R (reg m) Ms m3 0x1E :=
    ⟨⟨u3.pc, u3.mem, fun _ => rfl⟩, by rw [u3.regs, sp2],
      fun q hq => by rw [u3.regs, r2 q (by revert hq; revert q; decide) (by revert hq; revert q; decide)],
      fun x hx => by
        rw [← hMs]
        exact saveMem_outside decPs fun p hp => by
          simp only [decPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (rw [add_ofNat_assoc]; exact C.inR (by decide) hx),
      fun _ _ _ => rfl⟩
  have hsl0 : ∀ r o, (r, o) ∈ decPs → memLoad32 Ms (R + BitVec.ofNat 32 0x6D0 + o) = reg m r := fun r o hm => by
    have hr : r ≠ sp ∧ r ≠ a2 := by
      simp only [decPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    rw [← hMs, saveMem_slot decPs _ hm (by
      simp only [decPs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide),
      r2 r hr.1 hr.2]
  have hret' : reg m ra &&& ~~~1 = reg m ra := by rw [hra]; exact hret
  obtain ⟨n1, c1, D1, s2_1, s4_1, hY1⟩ := dec_ph1 C D0 (by rw [u3.regs, r2 a0 (by decide) (by decide), ha0])
    (by rw [u3.regs, r2 a1 (by decide) (by decide), ha1]) sBG
  obtain ⟨n2, c2, D2, s2_2, s4_2, hY2, hu2, hv2, h32, h72⟩ := dec_ph2 C D1 s2_1 s4_1 hY1 sO sD rfl rfl rfl rfl
  obtain ⟨n3, c3', D3, s2_3, s4_3, a0_3, hY3, hX3⟩ := dec_ph3 C D2 s2_2 s4_2 hY2 hu2 hv2 h32 h72 sS rfl rfl rfl
  obtain ⟨n4, c4, D4, s2_4, s4_4, s1_4, hX4, hY4⟩ := dec_ph4a C D3 s2_3 s4_3 a0_3 hY3 hX3
  obtain ⟨m', c', pc', sp', sv', kp', out', fr⟩ := dec_finish C D4 s2_4 s4_4 s1_4 hX4 hY4 sBG sO rfl hout sOG hoW
    hsl0 hret'
  refine ⟨m', .cons d1 (.cons d2 (c3.trans (c1.trans (c2.trans (c3'.trans (c4.trans c')))))), by rw [pc', hra],
    by rw [sp', eS], fun q hq => ?_, by rw [decSpec_eq]; exact out', fr⟩
  have hq' : q = ra ∨ q = (8 : Fin 32) ∨ q = (9 : Fin 32) ∨ q = (18 : Fin 32) ∨ q = (19 : Fin 32) ∨
      q = (20 : Fin 32) ∨ q = (21 : Fin 32) ∨ q.val ∈ [3, 4, 22, 23, 24, 25, 26, 27] := by
    revert hq; revert q; decide
  rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  · exact sv' _ (BitVec.ofNat 32 0x1C) (by decide)
  · exact sv' _ (BitVec.ofNat 32 0x18) (by decide)
  · exact sv' _ (BitVec.ofNat 32 0x14) (by decide)
  · exact sv' _ (BitVec.ofNat 32 0x10) (by decide)
  · exact sv' _ (BitVec.ofNat 32 0xC) (by decide)
  · exact sv' _ (BitVec.ofNat 32 8) (by decide)
  · exact sv' _ (BitVec.ofNat 32 4) (by decide)
  · exact kp' q h

end Phases

end C3.RV32
