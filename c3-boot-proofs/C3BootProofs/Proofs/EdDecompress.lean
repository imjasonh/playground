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

end Phases

end C3.RV32
