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


end Phases

end C3.RV32
