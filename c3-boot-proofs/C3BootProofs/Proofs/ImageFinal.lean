import C3BootProofs.Proofs.ImageOverlap
import C3BootProofs.Image.BootloaderV0

/-!
# `image::parse`: the entry-point check and the copy out

From offset 0x3C0, `image::parse` checks that an executable segment holds
the entry point (`entryW`), copies the segment array into the result with
`memcpy`, stores the header's fields after it, and returns through the
epilogue.
-/

namespace C3.RV32

open C3.ImageV0

set_option maxRecDepth 20000

theorem lo_byte (M : Word → BitVec 8) (a : Word) : (memLoad32 M a).extractLsb' 0 8 = M a := by
  unfold memLoad32
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_extractLsb']
  simp only [BitVec.getLsbD_append]
  simp [hi]

theorem copy_ld (M : Word → BitVec 8) (dst src : Word) (hw : dst.toNat + 0x100 ≤ 2 ^ 32) :
    ∀ k, k ≤ 64 → ∀ j, j < k →
      memLoad32 (copyWords M dst src k) (dst + BitVec.ofNat 32 (4 * j)) = memLoad32 M (src + BitVec.ofNat 32 (4 * j))
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | k + 1, hk, j, hj => by
    simp only [copyWords]
    by_cases hjk : j = k
    · subst hjk; exact memLoad32_store32_same _ _ _
    · rw [memLoad32_store32_sep (sep_offsets dst (by omega) (by omega) (by omega))]
      exact copy_ld M dst src hw k (by omega) j (by omega)

theorem copy_byte (M : Word → BitVec 8) (dst src : Word) (hw : dst.toNat + 0x100 ≤ 2 ^ 32) :
    ∀ k, k ≤ 64 → ∀ j, j < k →
      copyWords M dst src k (dst + BitVec.ofNat 32 (4 * j)) = M (src + BitVec.ofNat 32 (4 * j))
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | k + 1, hk, j, hj => by
    simp only [copyWords]
    by_cases hjk : j = k
    · subst hjk; rw [memStore32_lo, lo_byte]
    · rw [memStore32_get_sep (sep_offsets dst (by omega) (by omega) (by omega))]
      exact copy_byte M dst src hw k (by omega) j (by omega)

/-- The result `image::parse` writes for `Ok`: the 16 segment slots, then the
entry point, image length, segment count, and security version. -/
def OutOk (M : Word → BitVec 8) (out : Word) (sv : BitVec 8) (entry : Word) (cnt : BitVec 8) (ilen : Word)
    (segs : List SegW) : Prop :=
  (∀ j (h : j < segs.length),
    memLoad32 M (out + BitVec.ofNat 32 (16 * j)) = segs[j].addr ∧
    memLoad32 M (out + BitVec.ofNat 32 (16 * j + 4)) = segs[j].off ∧
    memLoad32 M (out + BitVec.ofNat 32 (16 * j + 8)) = segs[j].len ∧
    M (out + BitVec.ofNat 32 (16 * j + 12)) = segs[j].kind) ∧
  (∀ j, segs.length ≤ j → j < 16 → ∀ w, w < 4 → memLoad32 M (out + BitVec.ofNat 32 (16 * j + 4 * w)) = 0) ∧
  memLoad32 M (out + 0x100) = entry ∧ memLoad32 M (out + 0x104) = ilen ∧
  memLoad32 M (out + 0x108) = cnt.zeroExtend 32 ∧ M (out + 0x10C) = sv

/-- From `n`, `image::parse` returns `Ok` with the result `OutOk` describes,
nothing else outside the stack changed, and the caller's registers restored. -/
def IOkDone (R G out ilen : Word) (M0 : Word → BitVec 8) (f0 : Fin 32 → Word) (sv : BitVec 8) (entry : Word)
    (cnt : BitVec 8) (segs : List SegW) (n : Machine) : Prop :=
  ∃ n', Steps n n' ∧ n'.pc = f0 ra &&& ~~~1 ∧ reg n' sp = G + 0x160 ∧
    (∀ r, r ∉ ipTmp → r ≠ sp → reg n' r = f0 r) ∧
    (∀ x, Sep R 0x190 x 1 → Sep out 0x110 x 1 → n'.mem x = M0 x) ∧
    OutOk n'.mem out sv entry cnt ilen segs

section Final

variable {P R G ptr len out ilen : Word} {M0 Mx : Word → BitVec 8} {f0 g : Fin 32 → Word}

/-- **The copy out**, from offset 0x3F0: `memcpy` copies the segment array
into the result, then the header's fields follow it, and `image::parse`
returns. -/
theorem ip_copyOut (env : IEnv P R G ptr len out) (code0 : ICode M0 P)
    (inv : IInv R G ptr len out ilen M0 f0 Mx g) {m : Machine} (st : St Mx P m 0x3F0 g)
    {segs : List SegW} {sv cnt : BitVec 8} {entry : Word} (arr : ArrInv Mx G segs) (hl : segs.length ≤ 16)
    (h2 : g s2 = sv.zeroExtend 32) (hent : memLoad32 Mx (G + 8) = entry)
    (hcw : memLoad32 Mx (G + 0xC) = cnt.zeroExtend 32) :
    IOkDone R G out ilen M0 f0 sv entry cnt segs m := by
  have hc := (inv.code env code0).parse
  have hz := inv.zero
  have oG : ∀ j n c k, j + n ≤ 0x110 → c + k ≤ 0x160 → Sep (out + BitVec.ofNat 32 j) n (G + BitVec.ofNat 32 c) k :=
    fun j n c k h1 h2 => by
      rw [env.g_ofs]; exact (env.hOS.sub (c := j) (l := n) h1).subR (c := 0x30 + c) (l := k) (by omega)
  have oW : ∀ j n i l, j + n ≤ 0x110 → i + l ≤ ipWindowLen →
      Sep (out + BitVec.ofNat 32 j) n (ipWindow P + BitVec.ofNat 32 i) l :=
    fun j n i l h1 h2 => (env.hOW.sub (c := j) (l := n) h1).subR (c := i) (l := l) h2
  have oP : ∀ j, j + 4 ≤ 0x110 → Sep (out + BitVec.ofNat 32 j) 4 P imageParseCode.length := fun j hj => by
    have := oW j 4 0x2AE imageParseCode.length hj (by decide)
    rwa [← ip_wP P] at this
  have oo : ∀ j n i l, j + n ≤ i ∨ i + l ≤ j → j + n ≤ 0x110 → i + l ≤ 0x110 →
      Sep (out + BitVec.ofNat 32 j) n (out + BitVec.ofNat 32 i) l :=
    fun j n i l h h1 h2 => sep_offsets out h (by have := env.hwrap; omega) (by have := env.hwrap; omega)
  have hw := env.hwrap
  -- 0x3F0: memcpy(out, G + 0x24, 0x100).
  obtain ⟨m1, d1, u1⟩ := st.aluImm hc ip_at_3f0 (off' := 0x3F2) (by decide)
  obtain ⟨m2, d2, u2⟩ := u1.aluImm hc ip_at_3f2 (off' := 0x3F6) (by decide)
  obtain ⟨m3, d3, u3⟩ := u2.alu hc ip_at_3f6 (off' := 0x3F8) (by decide)
  obtain ⟨m4, c4, u4, mem4, a04, fr4⟩ := ip_memcpy env u3 (inv.code env code0) ip_at_3f8 ip_at_3fc
    (by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl) (even_at P env.hP 0x400 (by decide))
    (by rw [upd_a0]; simp +decide only [upd, ↓reduceIte]; rw [inv.s0]; exact BitVec.zero_add _)
    (by rw [updz (by simp) (by decide), updz (by simp) (by decide), upd_same (by decide), inv.sp]; rfl)
    (by rw [updz (by simp) (by decide), upd_same (by decide)]; rfl)
  rw [mem4] at u4
  have k4 : ∀ r, r ∉ ipClob → reg m4 r = g r := fun r hr => by
    have n : ∀ q : Fin 32, q ∈ ipClob → r ≠ q := fun q hq e => hr (e ▸ hq)
    rw [fr4 r (n a1 (by decide)) (n a2 (by decide)) (n a3 (by decide)) (n a4 (by decide)) (n a5 (by decide))
      (n a6 (by decide)) (n a7 (by decide)) (n t0 (by decide)) (n t1 (by decide)) (n ra (by decide)),
      updz (by simp) (n a0 (by decide)), updz (by simp) (n a2 (by decide)), updz hz (n a1 (by decide))]
  have r4 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → r ≠ a3 → r ≠ a4 → r ≠ a5 → r ≠ a6 → r ≠ a7 → r ≠ t0 → r ≠ t1 →
      r ≠ ra → reg m4 r = g r := fun r h0 h1 h2 h3 h4 h5 h6 h7 ht0 ht1 hra => by
    rw [fr4 r h1 h2 h3 h4 h5 h6 h7 ht0 ht1 hra, updz (by simp) h0, updz (by simp) h2, updz hz h1]
  have sp4 : reg m4 sp = G := by
    rw [r4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), inv.sp]
  have s04 : reg m4 RV32.s0 = out := by
    rw [r4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), inv.s0]
  have s14 : reg m4 s1 = ilen := by
    rw [r4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), inv.s1]
  have s24 : reg m4 s2 = sv.zeroExtend 32 := by
    rw [r4 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), h2]
  have hz4 : reg m4 0 = 0 := u4.zero
  generalize hMc : copyWords Mx out (G + 0x24) 64 = Mc at u4
  have cG : ∀ c, c + 4 ≤ 0x160 → memLoad32 Mc (G + BitVec.ofNat 32 c) = memLoad32 Mx (G + BitVec.ofNat 32 c) :=
    fun c hc' => memLoad32_congr fun j hj => by
      have hs := oG 0 (4 * 64) (c + j) 1 (by omega) (by omega)
      rw [add_ofNat_zero, ← add_ofNat_assoc] at hs
      rw [← hMc]; exact copyWords_outside 64 hs
  have winC : ∀ k, k < ipWindowLen → Mc (ipWindow P + BitVec.ofNat 32 k) = M0 (ipWindow P + BitVec.ofNat 32 k) :=
    fun k hk => by
      have hs := oW 0 (4 * 64) k 1 (by omega) (by omega)
      rw [add_ofNat_zero] at hs
      rw [← hMc, copyWords_outside 64 hs, inv.win env k hk]
  have hcC := (ip_codes code0 winC).1
  -- 0x400: the header's fields after the segments.
  obtain ⟨m5, d5, u5⟩ := u4.lw hcC ip_at_400 (off' := 0x402) (by decide)
    (by rw [sp4]; exact aligned_add env.hG (k := 8) (by decide))
  rw [sp4, show G + (8 : Word) = G + BitVec.ofNat 32 8 from rfl, cG 8 (by omega),
    show G + BitVec.ofNat 32 8 = G + 8 from rfl, hent] at u5
  obtain ⟨m6, d6, u6⟩ := u5.aluImm hcC ip_at_402 (off' := 0x406) (by decide)
  have e6 : aluEval .add (upd (reg m4) a0 entry RV32.s0) 0x100 = out + BitVec.ofNat 32 0x100 := by
    rw [updz hz4 (by decide), s04]; rfl
  rw [e6] at u6
  have g6 : ∀ r, r ≠ a0 → r ≠ a1 → upd (upd (reg m4) a0 entry) a1 (out + BitVec.ofNat 32 0x100) r = reg m4 r :=
    fun r h0 h1 => by rw [updz (by simp) h1, updz hz4 h0]
  obtain ⟨m7, d7, u7⟩ := u6.sw hcC ip_at_406 (off' := 0x408) (by decide)
    (by rw [upd_same (by decide), add_lit_zero]; exact aligned_add env.hout (by decide))
  rw [upd_same (by decide), add_lit_zero, updz (by simp) (by decide), upd_a0] at u7
  have hc7 := hcC.store32 (v := entry) (oP 0x100 (by omega))
  obtain ⟨m8, d8, u8⟩ := u7.sw hc7 ip_at_408 (off' := 0x40A) (by decide)
    (by rw [upd_same (by decide)]; show (out + BitVec.ofNat 32 0x100 + BitVec.ofNat 32 4).toNat % 4 = 0
        rw [add_ofNat_assoc]; exact aligned_add env.hout (by decide))
  rw [upd_same (by decide), g6 s1 (by decide) (by decide), s14,
    show out + BitVec.ofNat 32 0x100 + 4 = out + BitVec.ofNat 32 0x104 by
      rw [show (4 : Word) = BitVec.ofNat 32 4 from rfl, add_ofNat_assoc]] at u8
  have hc8 := hc7.store32 (v := ilen) (oP 0x104 (by omega))
  obtain ⟨m9, d9, u9⟩ := u8.lw hc8 ip_at_40a (off' := 0x40C) (by decide)
    (by rw [g6 sp (by decide) (by decide), sp4]; exact aligned_add env.hG (k := 0xC) (by decide))
  rw [g6 sp (by decide) (by decide), sp4, show G + (0xC : Word) = G + BitVec.ofNat 32 0xC from rfl,
    memLoad32_store32_sep (oG 0x104 4 0xC 4 (by omega) (by omega)),
    memLoad32_store32_sep (oG 0x100 4 0xC 4 (by omega) (by omega)), cG 0xC (by omega),
    show G + BitVec.ofNat 32 0xC = G + 0xC from rfl, hcw] at u9
  obtain ⟨m10, d10, u10⟩ := u9.sw hc8 ip_at_40c (off' := 0x40E) (by decide)
    (by rw [updz (by simp) (by decide), upd_same (by decide)]
        show (out + BitVec.ofNat 32 0x100 + BitVec.ofNat 32 8).toNat % 4 = 0
        rw [add_ofNat_assoc]; exact aligned_add env.hout (by decide))
  rw [updz (by simp) (by decide), upd_same (by decide), upd_a0,
    show out + BitVec.ofNat 32 0x100 + 8 = out + BitVec.ofNat 32 0x108 by
      rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, add_ofNat_assoc]] at u10
  have hc10 := hc8.store32 (v := cnt.zeroExtend 32) (oP 0x108 (by omega))
  obtain ⟨m11, d11, u11⟩ := u10.sb hc10 ip_at_40e (off' := 0x412) (by decide)
  have v11a : upd (upd (upd (reg m4) a0 entry) a1 (out + BitVec.ofNat 32 0x100)) a0 (cnt.zeroExtend 32)
      RV32.s0 + 0x10C = out + BitVec.ofNat 32 0x10C := by
    rw [updz (by simp) (by decide), g6 _ (by decide) (by decide), s04]; rfl
  have v11b : (upd (upd (upd (reg m4) a0 entry) a1 (out + BitVec.ofNat 32 0x100)) a0 (cnt.zeroExtend 32)
      s2).extractLsb' 0 8 = sv := by
    rw [updz (by simp) (by decide), g6 _ (by decide) (by decide), s24, zext_lsb8]
  rw [v11a, v11b] at u11
  have s10C : Sep (out + BitVec.ofNat 32 0x10C) 1 P imageParseCode.length := by
    have := (oP 0x10C (by omega)).sub (c := 0) (l := 1) (by omega)
    rwa [add_ofNat_zero] at this
  have hc11 := hc10.store8 (v := sv) s10C
  obtain ⟨m12, d12, u12⟩ := u11.jump hc11 ip_at_412 (off' := 0xC0) (by decide)
    (by rw [u11.pc, BitVec.add_assoc]; exact even_bit0 (even_at P env.hP 0xC0 (by decide)))
  generalize hMF : memStore8 (memStore32 (memStore32 (memStore32 Mc (out + BitVec.ofNat 32 0x100) entry)
    (out + BitVec.ofNat 32 0x104) ilen) (out + BitVec.ofNat 32 0x108) (cnt.zeroExtend 32))
    (out + BitVec.ofNat 32 0x10C) sv = MF at u12
  -- What the header stores leave alone.
  have hdr : ∀ x, Sep (out + BitVec.ofNat 32 0x100) 0x10 x 1 → MF x = Mc x := fun x hx => by
    rw [← hMF, memStore8_ne (fun e => hx 0xC (by omega) 0 (by omega) (by
        rw [add_ofNat_assoc, add_ofNat_zero, e])),
      memStore32_get_sep (by have := hx.sub (c := 8) (l := 4) (by omega); rwa [add_ofNat_assoc] at this),
      memStore32_get_sep (by have := hx.sub (c := 4) (l := 4) (by omega); rwa [add_ofNat_assoc] at this),
      memStore32_get_sep (by have := hx.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this)]
  have winF : ∀ k, k < ipWindowLen → MF (ipWindow P + BitVec.ofNat 32 k) = M0 (ipWindow P + BitVec.ofNat 32 k) :=
    fun k hk => by
      rw [hdr _ (by have := oW 0x100 0x10 k 1 (by omega) (by omega); exact this), winC k hk]
  have stkF : ∀ c, c < 0x160 → MF (G + BitVec.ofNat 32 c) = Mx (G + BitVec.ofNat 32 c) := fun c hc' => by
    have h1 := oG 0x100 0x10 c 1 (by omega) (by omega)
    have h2 := oG 0 (4 * 64) c 1 (by omega) (by omega)
    rw [add_ofNat_zero] at h2
    rw [hdr _ h1, ← hMc, copyWords_outside 64 h2]
  obtain ⟨n', c', pc', mem', sp', regs'⟩ := ip_final (f0 := f0) env code0 u12 sp4 winF
    (fun p hp => by
      rw [← inv.slots p hp]
      have hk : p.2 + 4 ≤ 0x160 := by
        simp only [ipSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact memLoad32_congr fun j hj => by rw [add_ofNat_assoc]; exact stkF _ (by omega))
    (fun r hr => by
      have n : ∀ q : Fin 32, q ∈ ipClob → r ≠ q := fun q hq e => hr (e ▸ hq)
      rw [updz (by simp) (n a0 (by decide)), g6 r (n a0 (by decide)) (n a1 (by decide)), k4 r hr, inv.keep r hr])
  -- The result, read back.
  have hdrL : ∀ c, c + 4 ≤ 0x100 → memLoad32 MF (out + BitVec.ofNat 32 c) = memLoad32 Mc (out + BitVec.ofNat 32 c) :=
    fun c hc' => memLoad32_congr fun j hj => by
      rw [add_ofNat_assoc]; exact hdr _ (oo 0x100 0x10 (c + j) 1 (by omega) (by omega) (by omega))
  have srcE : ∀ c, G + 0x24 + BitVec.ofNat 32 c = G + BitVec.ofNat 32 (0x24 + c) := fun c => by
    show G + BitVec.ofNat 32 0x24 + _ = _; rw [add_ofNat_assoc]
  have cpL : ∀ w, w < 64 → memLoad32 Mc (out + BitVec.ofNat 32 (4 * w)) =
      memLoad32 Mx (G + BitVec.ofNat 32 (0x24 + 4 * w)) := fun w hw => by
    rw [← hMc, copy_ld Mx out (G + 0x24) (by omega) 64 (by omega) w hw, srcE]
  have cpB : ∀ w, w < 64 → Mc (out + BitVec.ofNat 32 (4 * w)) = Mx (G + BitVec.ofNat 32 (0x24 + 4 * w)) :=
    fun w hw => by rw [← hMc, copy_byte Mx out (G + 0x24) (by omega) 64 (by omega) w hw, srcE]
  have o1 : Sep (out + BitVec.ofNat 32 0x10C) 1 (out + BitVec.ofNat 32 0x100) 4 := oo _ _ _ _ (by omega) (by omega) (by omega)
  have o2 : Sep (out + BitVec.ofNat 32 0x10C) 1 (out + BitVec.ofNat 32 0x104) 4 := oo _ _ _ _ (by omega) (by omega) (by omega)
  have o3 : Sep (out + BitVec.ofNat 32 0x10C) 1 (out + BitVec.ofNat 32 0x108) 4 := oo _ _ _ _ (by omega) (by omega) (by omega)
  refine ⟨n', .cons d1 (.cons d2 (.cons d3 (c4.trans (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.cons d9 (.cons d10
    (.cons d11 (.cons d12 c'))))))))))), pc', sp', regs', fun x hR hO => ?_, ?_⟩
  · rw [mem', hdr x (hO.sub (c := 0x100) (l := 0x10) (by omega))]
    have h256 := hO.sub (c := 0) (l := 4 * 64) (by omega)
    rw [add_ofNat_zero] at h256
    rw [← hMc, copyWords_outside 64 h256, inv.outside x hR]
  rw [mem']
  refine ⟨fun j hj => ?_, fun j h1 h2 w hw => ?_, ?_, ?_, ?_, ?_⟩
  · have hj16 : j < 16 := by omega
    obtain ⟨e1, e2, e3, e4⟩ := arr.1 j hj
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hdrL _ (by omega), show 16 * j = 4 * (4 * j) by omega, cpL _ (by omega),
        show 0x24 + 4 * (4 * j) = 0x24 + 16 * j by omega, e1]
    · rw [hdrL _ (by omega), show 16 * j + 4 = 4 * (4 * j + 1) by omega, cpL _ (by omega),
        show 0x24 + 4 * (4 * j + 1) = 0x28 + 16 * j by omega, e2]
    · rw [hdrL _ (by omega), show 16 * j + 8 = 4 * (4 * j + 2) by omega, cpL _ (by omega),
        show 0x24 + 4 * (4 * j + 2) = 0x2C + 16 * j by omega, e3]
    · rw [hdr _ (oo 0x100 0x10 (16 * j + 12) 1 (by omega) (by omega) (by omega)),
        show 16 * j + 12 = 4 * (4 * j + 3) by omega, cpB _ (by omega),
        show 0x24 + 4 * (4 * j + 3) = 0x30 + 16 * j by omega, e4]
  · rw [hdrL _ (by omega), show 16 * j + 4 * w = 4 * (4 * j + w) by omega, cpL _ (by omega),
      show 0x24 + 4 * (4 * j + w) = 0x24 + 16 * j + 4 * w by omega]
    exact arr.2 j h1 h2 w hw
  · rw [← hMF, show out + (0x100 : Word) = out + BitVec.ofNat 32 0x100 from rfl, memLoad32_store8_sep o1,
      memLoad32_store32_sep (oo 0x108 4 0x100 4 (by omega) (by omega) (by omega)),
      memLoad32_store32_sep (oo 0x104 4 0x100 4 (by omega) (by omega) (by omega)), memLoad32_store32_same]
  · rw [← hMF, show out + (0x104 : Word) = out + BitVec.ofNat 32 0x104 from rfl, memLoad32_store8_sep o2,
      memLoad32_store32_sep (oo 0x108 4 0x104 4 (by omega) (by omega) (by omega)), memLoad32_store32_same]
  · rw [← hMF, show out + (0x108 : Word) = out + BitVec.ofNat 32 0x108 from rfl, memLoad32_store8_sep o3,
      memLoad32_store32_same]
  · rw [← hMF, show out + (0x10C : Word) = out + BitVec.ofNat 32 0x10C from rfl, memStore8_same]

/-- The entry-point loop's invariant at offset 0x3C8, at segment `i`. -/
structure EnInv (R G ptr len out ilen : Word) (M0 : Word → BitVec 8) (f0 : Fin 32 → Word)
    (sv cnt : BitVec 8) (entry : Word) (segs : List SegW) (i : Nat)
    (Mx : Word → BitVec 8) (g : Fin 32 → Word) : Prop where
  inv : IInv R G ptr len out ilen M0 f0 Mx g
  arr : ArrInv Mx G segs
  hl : segs.length = cnt.toNat
  hc : cnt.toNat ≤ 16
  hi : i ≤ cnt.toNat
  s2 : g s2 = sv.zeroExtend 32
  s11 : g s11 = G + BitVec.ofNat 32 (0x24 + 16 * cnt.toNat)
  a6 : g (16 : Fin 32) = 0xB
  it : memLoad32 Mx (G + 0x14) = G + BitVec.ofNat 32 (0x24 + 16 * i)
  ent : memLoad32 Mx (G + 8) = entry
  cntw : memLoad32 Mx (G + 0xC) = cnt.zeroExtend 32

theorem kind_odd (k : BitVec 8) : (aluEval .and (k.zeroExtend 32) 1 != 0) = !((k &&& 1) == 0) := by
  revert k; decide

/-- An entry point in segment `s`. -/
def inSeg (entry : Word) (s : SegW) : Bool :=
  (s.kind &&& 1) == 0 && !entry.ult s.addr && (entry - s.addr).ult s.len

theorem entryIn_cons (entry : Word) (s : SegW) (rest : List SegW) :
    entryIn entry (s :: rest) = (inSeg entry s || entryIn entry rest) := rfl

/-- **The entry-point loop**, from offset 0x3C8 at segment `i`: it finds an
executable segment that holds the entry point and copies the result out, or
returns error 11. -/
theorem en_loop (env : IEnv P R G ptr len out) (code0 : ICode M0 P) {segs : List SegW} {sv cnt : BitVec 8}
    {entry : Word} :
    ∀ n i {Mx : Word → BitVec 8} {g : Fin 32 → Word} {m : Machine}, i + n = cnt.toNat →
      EnInv R G ptr len out ilen M0 f0 sv cnt entry segs i Mx g → St Mx P m 0x3C8 g →
      (entryIn entry (segs.drop i) = true ∧ IOkDone R G out ilen M0 f0 sv entry cnt segs m) ∨
        (entryIn entry (segs.drop i) = false ∧ IErrDone R G out M0 f0 11 m)
  | n, i, Mx, g, m, hn, ei, st => by
    have hc := (ei.inv.code env code0).parse
    have hz := ei.inv.zero
    have sp0 := ei.inv.sp
    obtain ⟨m1, d1, u1⟩ := st.lw hc ip_at_3c8 (off' := 0x3CA) (by decide)
      (by rw [sp0]; exact aligned_add env.hG (k := 0x14) (by decide))
    rw [sp0, ei.it] at u1
    have inv1 := ei.inv.setR a1 (v := G + BitVec.ofNat 32 (0x24 + 16 * i))
    have hc1 := (inv1.code env code0).parse
    match n with
    | 0 =>
      obtain ⟨m2, d2, u2⟩ := u1.taken hc1 0x418 ip_at_3ca (by decide)
        (by rw [upd_same (by decide), updz hz (by decide), ei.s11, show i = cnt.toNat by omega]
            exact beq_iff_eq.mpr rfl)
      refine .inr ⟨by rw [List.drop_of_length_le (by rw [ei.hl]; omega)]; rfl, ?_⟩
      exact IErrDone.pre (.cons d1 (.single d2))
        (ip_err418 env code0 inv1 u2 (by rw [updz hz (by decide), ei.a6]; rfl))
    | n + 1 =>
      have hi : i < cnt.toNat := by omega
      have hi16 : i < 16 := Nat.lt_of_lt_of_le hi ei.hc
      have hil : i < segs.length := by rw [ei.hl]; exact hi
      obtain ⟨e1, e2, e3, e4⟩ := ei.arr.1 i hil
      obtain ⟨m2, d2, u2⟩ := u1.notTaken hc1 0x3CE ip_at_3ca (by decide)
        (by rw [upd_same (by decide), updz hz (by decide), ei.s11]
            exact Bool.eq_false_iff.mpr fun h => add_ofNat_ne G (c := 0x24 + 16 * i) (d := 0x24 + 16 * cnt.toNat)
              (by omega) (by have := ei.hc; omega) (by omega) (beq_iff_eq.mp h))
      obtain ⟨m3, d3, u3⟩ := u2.lbu hc1 ip_at_3ce (off' := 0x3D2) (by decide)
      rw [upd_same (by decide), show G + BitVec.ofNat 32 (0x24 + 16 * i) + 0xC = G + BitVec.ofNat 32 (0x30 + 16 * i) by
        rw [show (0xC : Word) = BitVec.ofNat 32 0xC from rfl, add_ofNat_assoc]; congr 2 <;> omega, e4] at u3
      obtain ⟨m4, d4, u4⟩ := u3.aluImm hc1 ip_at_3d2 (off' := 0x3D4) (by decide)
      obtain ⟨m5, d5, u5⟩ := u4.aluImm hc1 ip_at_3d4 (off' := 0x3D8) (by decide)
      have u5' := u5.self
      have r5 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → reg m5 r = g r := fun r h0 h1 h2 => by
        rw [u5.regs, updz (by simp) h0, updz (by simp) h2, updz (by simp) h2, updz hz h1]
      have r5a0 : reg m5 a0 = G + BitVec.ofNat 32 (0x24 + 16 * (i + 1)) := by
        rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
        show _ + BitVec.ofNat 32 0x10 = _; rw [add_ofNat_assoc]; congr 2 <;> omega
      have r5a1 : reg m5 a1 = G + BitVec.ofNat 32 (0x24 + 16 * i) := by
        rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
      have r5a2 : reg m5 a2 = aluEval .and (segs[i].kind.zeroExtend 32) 1 := by
        rw [u5.regs]; simp +decide only [upd, ↓reduceIte]
      have inv5 : IInv R G ptr len out ilen M0 f0 Mx (reg m5) := ei.inv.frameR
        (fun r hr => r5 r (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide)))
        (by rw [r5 _ (by decide) (by decide) (by decide), sp0]) (by rw [r5 _ (by decide) (by decide) (by decide), ei.inv.s0])
        (by rw [r5 _ (by decide) (by decide) (by decide), ei.inv.s1]) u5.zero
      obtain ⟨m6, d6, u6⟩ := u5'.sw (inv5.code env code0).parse ip_at_3d8 (off' := 0x3DA) (by decide)
        (by rw [inv5.sp]; exact aligned_add env.hG (k := 0x14) (by decide))
      rw [inv5.sp, r5a0] at u6
      have inv6 := inv5.st32 env 0x14 (G + BitVec.ofNat 32 (0x24 + 16 * (i + 1))) (Or.inl (by omega))
      generalize hM6 : memStore32 Mx (G + 0x14) (G + BitVec.ofNat 32 (0x24 + 16 * (i + 1))) = M6 at u6
      have hM6' : memStore32 Mx (G + BitVec.ofNat 32 0x14) (G + BitVec.ofNat 32 (0x24 + 16 * (i + 1))) = M6 := hM6
      rw [hM6'] at inv6
      have hc6 := (inv6.code env code0).parse
      have arr6 : ArrInv M6 G segs := by
        rw [← hM6']; exact ei.arr.agree (ArrAgree.st32 Mx G 0x14 _ (Or.inl (by omega)) (by omega))
          (by rw [ei.hl]; exact ei.hc)
      have ld6 : ∀ c, c + 4 ≤ 0x14 ∨ (0x18 ≤ c ∧ c + 4 ≤ 0x160) →
          memLoad32 M6 (G + BitVec.ofNat 32 c) = memLoad32 Mx (G + BitVec.ofNat 32 c) := fun c hc' => by
        rw [← hM6', memLoad32_store32_sep (sep_offsets G (by omega) (by omega) (by omega))]
      have ent6 : memLoad32 M6 (G + 8) = entry := by
        rw [show G + 8 = G + BitVec.ofNat 32 8 from rfl, ld6 8 (Or.inl (by omega))]; exact ei.ent
      have pre6 : Steps m m6 := .cons d1 (.cons d2 (.cons d3 (.cons d4 (.cons d5 (.single d6)))))
      have next : ∀ {m' : Machine} {g' : Fin 32 → Word}, Steps m m' → St M6 P m' 0x3C8 g' →
          (∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → g' r = g r) →
          (entryIn entry (segs.drop (i + 1)) = true ∧ IOkDone R G out ilen M0 f0 sv entry cnt segs m) ∨
            (entryIn entry (segs.drop (i + 1)) = false ∧ IErrDone R G out M0 f0 11 m) := by
        intro m' g' c' st' hr
        have ei' : EnInv R G ptr len out ilen M0 f0 sv cnt entry segs (i + 1) M6 g' :=
          ⟨inv6.frameR (fun r hr' => by
              have h0 : r ≠ a0 := fun e => hr' (e ▸ by decide)
              have h1 : r ≠ a1 := fun e => hr' (e ▸ by decide)
              have h2 : r ≠ a2 := fun e => hr' (e ▸ by decide)
              rw [hr r h0 h1 h2, r5 r h0 h1 h2])
            (by rw [hr _ (by decide) (by decide) (by decide), sp0]) (by rw [hr _ (by decide) (by decide) (by decide), ei.inv.s0])
            (by rw [hr _ (by decide) (by decide) (by decide), ei.inv.s1]) st'.zero,
           arr6, ei.hl, ei.hc, by omega, by rw [hr _ (by decide) (by decide) (by decide), ei.s2],
           by rw [hr _ (by decide) (by decide) (by decide), ei.s11], by rw [hr _ (by decide) (by decide) (by decide), ei.a6],
           by rw [← hM6]; exact memLoad32_store32_same _ _ _, ent6,
           by rw [show G + 0xC = G + BitVec.ofNat 32 0xC from rfl, ld6 0xC (Or.inl (by omega))]; exact ei.cntw⟩
        rcases en_loop env code0 n (i + 1) (by omega) ei' st' with ⟨h, ok⟩ | ⟨h, er⟩
        · exact .inl ⟨h, let ⟨n', c'', rest⟩ := ok; ⟨n', c'.trans c'', rest⟩⟩
        · exact .inr ⟨h, IErrDone.pre c' er⟩
      rw [List.drop_eq_getElem_cons hil, entryIn_cons]
      by_cases hk : (segs[i].kind &&& 1) == 0
      · obtain ⟨m7, d7, u7⟩ := u6.notTaken hc6 0x3DC ip_at_3da (by decide)
          (by rw [r5a2, inv5.zero]; show (_ != _) = false; rw [kind_odd, hk]; rfl)
        obtain ⟨m8, d8, u8⟩ := u7.lw hc6 ip_at_3dc (off' := 0x3DE) (by decide)
          (by rw [r5a1, add_lit_zero]; exact aligned_add env.hG (by omega))
        rw [r5a1, add_lit_zero, ld6 _ (Or.inr ⟨by omega, by omega⟩), e1] at u8
        obtain ⟨m9, d9, u9⟩ := u8.lw hc6 ip_at_3de (off' := 0x3E0) (by decide)
          (by rw [updz inv5.zero (by decide), inv5.sp]; exact aligned_add env.hG (k := 8) (by decide))
        rw [updz inv5.zero (by decide), inv5.sp, ent6] at u9
        have k9 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → upd (upd (reg m5) a2 segs[i].addr) a0 entry r = g r :=
          fun r h0 h1 h2 => by rw [updz (by simp) h0, updz inv5.zero h2, r5 r h0 h1 h2]
        by_cases e5 : entry.ult segs[i].addr = true
        · obtain ⟨m10, d10, u10⟩ := u9.taken hc6 0x3C8 ip_at_3e0 (by decide)
            (by rw [upd_a0, updz (by simp) (by decide), upd_same (by decide)]; exact e5)
          have hin : inSeg entry segs[i] = false := by unfold inSeg; rw [hk, e5]; rfl
          rw [hin, Bool.false_or]
          exact next (pre6.trans (.cons d7 (.cons d8 (.cons d9 (.single d10))))) u10 k9
        · have e5' := Bool.eq_false_iff.mpr e5
          obtain ⟨m10, d10, u10⟩ := u9.notTaken hc6 0x3E4 ip_at_3e0 (by decide)
            (by rw [upd_a0, updz (by simp) (by decide), upd_same (by decide)]; exact e5')
          obtain ⟨m11, d11, u11⟩ := u10.lw hc6 ip_at_3e4 (off' := 0x3E6) (by decide)
            (by rw [updz (by simp) (by decide), updz inv5.zero (by decide), r5a1]
                exact aligned_add env.hG (k := 0x2C + 16 * i) (by omega) |> fun h => by
                  rwa [show G + BitVec.ofNat 32 (0x2C + 16 * i) = G + BitVec.ofNat 32 (0x24 + 16 * i) + 8 by
                    rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, add_ofNat_assoc]; congr 2 <;> omega] at h)
          rw [updz (by simp) (by decide), updz inv5.zero (by decide), r5a1,
            show G + BitVec.ofNat 32 (0x24 + 16 * i) + 8 = G + BitVec.ofNat 32 (0x2C + 16 * i) by
              rw [show (8 : Word) = BitVec.ofNat 32 8 from rfl, add_ofNat_assoc]; congr 2 <;> omega,
            ld6 _ (Or.inr ⟨by omega, by omega⟩), e3] at u11
          obtain ⟨m12, d12, u12⟩ := u11.lw hc6 ip_at_3e6 (off' := 0x3E8) (by decide)
            (by rw [updz (by simp) (by decide), updz (by simp) (by decide), updz inv5.zero (by decide), inv5.sp]
                exact aligned_add env.hG (k := 8) (by decide))
          rw [updz (by simp) (by decide), updz (by simp) (by decide), updz inv5.zero (by decide), inv5.sp, ent6] at u12
          obtain ⟨m13, d13, u13⟩ := u12.alu hc6 ip_at_3e8 (off' := 0x3EC) (by decide)
          have k13 : ∀ r, r ≠ a0 → r ≠ a1 → r ≠ a2 → reg m13 r = g r := fun r h0 h1 h2 => by
            rw [u13.regs, updz (by simp) h2, updz (by simp) h0, updz (by simp) h1, k9 r h0 h1 h2]
          have r13a2 : reg m13 a2 = entry - segs[i].addr := by
            rw [u13.regs]; simp +decide only [upd, ↓reduceIte]; rfl
          have r13a1 : reg m13 a1 = segs[i].len := by rw [u13.regs]; simp +decide only [upd, ↓reduceIte]
          have pre13 : Steps m m13 := pre6.trans (.cons d7 (.cons d8 (.cons d9 (.cons d10 (.cons d11
            (.cons d12 (.single d13)))))))
          by_cases e6 : (entry - segs[i].addr).ult segs[i].len = true
          · obtain ⟨m14, d14, u14⟩ := u13.self.notTaken hc6 0x3F0 ip_at_3ec (by decide)
              (by rw [r13a2, r13a1]; show (!_) = false; rw [e6]; rfl)
            have hin : inSeg entry segs[i] = true := by unfold inSeg; rw [hk, e5', e6]; rfl
            rw [hin, Bool.true_or]
            refine .inl ⟨rfl, ?_⟩
            have inv14 : IInv R G ptr len out ilen M0 f0 M6 (reg m13) := inv6.frameR
              (fun r hr => by
                have h0 : r ≠ a0 := fun e => hr (e ▸ by decide)
                have h1 : r ≠ a1 := fun e => hr (e ▸ by decide)
                have h2 : r ≠ a2 := fun e => hr (e ▸ by decide)
                rw [k13 r h0 h1 h2, r5 r h0 h1 h2])
              (by rw [k13 _ (by decide) (by decide) (by decide), sp0])
              (by rw [k13 _ (by decide) (by decide) (by decide), ei.inv.s0])
              (by rw [k13 _ (by decide) (by decide) (by decide), ei.inv.s1]) u13.zero
            have ok := ip_copyOut env code0 inv14 u14 arr6 (by rw [ei.hl]; exact ei.hc)
              (by rw [k13 _ (by decide) (by decide) (by decide), ei.s2]) ent6
              (by rw [show G + 0xC = G + BitVec.ofNat 32 0xC from rfl, ld6 0xC (Or.inl (by omega))]; exact ei.cntw)
            obtain ⟨n', c', rest⟩ := ok
            exact ⟨n', (pre13.trans (.single d14)).trans c', rest⟩
          · obtain ⟨m14, d14, u14⟩ := u13.self.taken hc6 0x3C8 ip_at_3ec (by decide)
              (by rw [r13a2, r13a1]; show (!_) = true; rw [Bool.eq_false_iff.mpr e6]; rfl)
            have hin : inSeg entry segs[i] = false := by
              unfold inSeg; rw [hk, e5', Bool.eq_false_iff.mpr e6]; rfl
            rw [hin, Bool.false_or]
            exact next (pre13.trans (.single d14)) u14 k13
      · obtain ⟨m7, d7, u7⟩ := u6.taken hc6 0x3C8 ip_at_3da (by decide)
          (by rw [r5a2, inv5.zero]; show (_ != _) = true; rw [kind_odd, Bool.eq_false_iff.mpr hk]; rfl)
        have hin : inSeg entry segs[i] = false := by unfold inSeg; rw [Bool.eq_false_iff.mpr hk]; rfl
        rw [hin, Bool.false_or]
        exact next (pre6.trans (.single d7)) u7 r5

/-- From offset 0x3C0 after the overlap loops: an odd entry point is error 11;
otherwise the entry-point loop, then the copy out. -/
theorem en_start (env : IEnv P R G ptr len out) (code0 : ICode M0 P) {segs : List SegW} {sv cnt : BitVec 8}
    {entry : Word} (b : OBase R G ptr len out ilen M0 f0 sv cnt entry segs Mx g) {m : Machine}
    (st : St Mx P m 0x3C0 g) :
    match entryW entry segs with
    | .error e => IErrDone R G out M0 f0 e m
    | .ok () => IOkDone R G out ilen M0 f0 sv entry cnt segs m := by
  have hc := (b.inv.code env code0).parse
  have hz := b.inv.zero
  obtain ⟨m1, d1, u1⟩ := st.lw hc ip_at_3c0 (off' := 0x3C2) (by decide)
    (by rw [b.inv.sp]; exact aligned_add env.hG (k := 8) (by decide))
  rw [b.inv.sp, b.ent] at u1
  obtain ⟨m2, d2, u2⟩ := u1.aluImm hc ip_at_3c2 (off' := 0x3C4) (by decide)
  obtain ⟨m3, d3, u3⟩ := u2.aluImm hc ip_at_3c4 (off' := 0x3C6) (by decide)
  have k3 : ∀ r, r ≠ a1 → r ≠ (16 : Fin 32) → upd (upd (upd g a1 entry) a1 (aluEval .and (upd g a1 entry a1) 1))
      (16 : Fin 32) (aluEval .add (upd (upd g a1 entry) a1 (aluEval .and (upd g a1 entry a1) 1) x0) 0xB) r = g r :=
    fun r h1 h6 => by rw [updz (by simp) h6, updz (by simp) h1, updz hz h1]
  have v3a1 : upd (upd (upd g a1 entry) a1 (aluEval .and (upd g a1 entry a1) 1))
      (16 : Fin 32) (aluEval .add (upd (upd g a1 entry) a1 (aluEval .and (upd g a1 entry a1) 1) x0) 0xB) a1 =
      entry &&& 1 := by
    rw [updz (by simp) (by decide), upd_same (by decide), upd_same (by decide)]; rfl
  have r3 : ∀ r, r ≠ a1 → r ≠ (16 : Fin 32) → reg m3 r = g r := fun r h1 h6 => by rw [u3.regs]; exact k3 r h1 h6
  have r3a1 : reg m3 a1 = entry &&& 1 := by rw [u3.regs]; exact v3a1
  have r3a6 : reg m3 (16 : Fin 32) = 0xB := by
    rw [u3.regs]; simp +decide only [upd, ↓reduceIte]
  have inv3 : IInv R G ptr len out ilen M0 f0 Mx (reg m3) := b.inv.frameR
    (fun r hr => r3 r (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide)))
    (by rw [r3 _ (by decide) (by decide), b.inv.sp]) (by rw [r3 _ (by decide) (by decide), b.inv.s0])
    (by rw [r3 _ (by decide) (by decide), b.inv.s1]) u3.zero
  have pre : Steps m m3 := .cons d1 (.cons d2 (.single d3))
  unfold entryW
  by_cases ho : ((entry &&& 1) != 0) = true
  · rw [ite_eq_left ho]
    obtain ⟨m4, d4, u4⟩ := u3.self.taken hc 0x418 ip_at_3c6 (by decide) (by rw [r3a1, inv3.zero]; exact ho)
    exact IErrDone.pre (pre.trans (.single d4)) (ip_err418 env code0 inv3 u4 (by rw [r3a6]; rfl))
  · have ho' := Bool.eq_false_iff.mpr ho
    rw [ite_eq_right ho]
    obtain ⟨m4, d4, u4⟩ := u3.self.notTaken hc 0x3C8 ip_at_3c6 (by decide) (by rw [r3a1, inv3.zero]; exact ho')
    have ei : EnInv R G ptr len out ilen M0 f0 sv cnt entry segs 0 Mx (reg m3) :=
      ⟨inv3, b.arr, b.hl, b.hc, by omega, by rw [r3 _ (by decide) (by decide), b.s2],
       by rw [r3 _ (by decide) (by decide), b.s11], r3a6, by rw [b.it], b.ent, b.cntw⟩
    rcases en_loop env code0 cnt.toNat 0 (by omega) ei u4 with ⟨h, ok⟩ | ⟨h, er⟩
    · rw [List.drop_zero] at h; rw [ite_eq_left h]
      obtain ⟨n', c', rest⟩ := ok
      exact ⟨n', (pre.trans (.single d4)).trans c', rest⟩
    · rw [List.drop_zero] at h; rw [ite_eq_right (by rw [h]; decide)]
      exact IErrDone.pre (pre.trans (.single d4)) er

end Final

end C3.RV32
