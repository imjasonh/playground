import C3BootProofs.Proofs.Panic
import C3BootProofs.Proofs.Sec1Tag
import C3BootProofs.Proofs.DerTlv

/-!
# `sec1::point::EncodedPoint`'s `tag` and `is_identity`, as compiled

The image passes `tag` the encoded point's first byte. `tag` converts it with
`Tag::from_u8` and unwraps the result with `Result::expect`, so it returns
the byte for the SEC1 tags 0, 2, 3, 4, and 5 and panics for any other byte.
`is_identity` compares that tag with 0, the identity's tag.
-/

namespace C3.RV32

open C3.Image

section
set_option maxRecDepth 20000
theorem ept_at_0 : fetchRel encodedPointTagCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFC0, 2) := by decide
theorem ept_at_2 : fetchRel encodedPointTagCode 0x2 = some (.store .sw sp ra 0x3C, 2) := by decide
theorem ept_at_4 : fetchRel encodedPointTagCode 0x4 = some (.aluImm .and a1 a0 0xFF, 4) := by decide
theorem ept_at_8 : fetchRel encodedPointTagCode 0x8 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem ept_at_a : fetchRel encodedPointTagCode 0xA = some (.auipc ra 0xFFFFE000, 4) := by decide
theorem ept_at_e : fetchRel encodedPointTagCode 0xE = some (.jalr ra ra 0xFFFFFCD6, 4) := by decide
theorem ept_at_12 : fetchRel encodedPointTagCode 0x12 = some (.aluImm .add a0 sp 0x8, 2) := by decide
theorem ept_at_14 : fetchRel encodedPointTagCode 0x14 = some (.auipc ra 0x0, 4) := by decide
theorem ept_at_18 : fetchRel encodedPointTagCode 0x18 = some (.jalr ra ra 0x12, 4) := by decide
theorem ept_at_1c : fetchRel encodedPointTagCode 0x1C = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem ept_at_20 : fetchRel encodedPointTagCode 0x20 = some (.load .lw ra sp 0x3C, 2) := by decide
theorem ept_at_22 : fetchRel encodedPointTagCode 0x22 = some (.aluImm .add sp sp 0x40, 2) := by decide
theorem ept_at_24 : fetchRel encodedPointTagCode 0x24 = some (.jalr x0 ra 0x0, 2) := by decide
theorem epi_at_0 : fetchRel encodedPointIsIdentityCode 0x0 = some (.aluImm .add sp sp 0xFFFFFFF0, 2) := by decide
theorem epi_at_2 : fetchRel encodedPointIsIdentityCode 0x2 = some (.store .sw sp ra 0xC, 2) := by decide
theorem epi_at_4 : fetchRel encodedPointIsIdentityCode 0x4 = some (.auipc ra 0x0, 4) := by decide
theorem epi_at_8 : fetchRel encodedPointIsIdentityCode 0x8 = some (.jalr ra ra 0x16, 4) := by decide
theorem epi_at_c : fetchRel encodedPointIsIdentityCode 0xC = some (.aluImm .and a0 a0 0xFF, 4) := by decide
theorem epi_at_10 : fetchRel encodedPointIsIdentityCode 0x10 = some (.aluImm .sltu a0 a0 0x1, 4) := by decide
theorem epi_at_14 : fetchRel encodedPointIsIdentityCode 0x14 = some (.load .lw ra sp 0xC, 2) := by decide
theorem epi_at_16 : fetchRel encodedPointIsIdentityCode 0x16 = some (.aluImm .add sp sp 0x10, 2) := by decide
theorem epi_at_18 : fetchRel encodedPointIsIdentityCode 0x18 = some (.jalr x0 ra 0x0, 2) := by decide
end

theorem ept_zext_tn : ∀ t : BitVec 8, (t.zeroExtend 32 : Word).toNat = t.toNat := by decide

theorem zext_seqz : ∀ t : BitVec 8, aluEval .sltu (t.zeroExtend 32 : Word) 1 = if t = 0 then 1 else 0 := by
  decide

theorem Room.frame64 {S : Word} {k : Nat} (h : Room S (k + 64)) : Room (S + 0xFFFFFFC0) k := by
  obtain ⟨h0, h1, h2⟩ := h
  have e : (S + 0xFFFFFFC0).toNat = S.toNat - 64 := by
    rw [BitVec.toNat_add, show (0xFFFFFFC0 : Word).toNat = 4294967232 from rfl]; unfold dramEnd at h2; omega
  refine ⟨?_, ?_, ?_⟩ <;> rw [e] <;> unfold dramEnd at * <;> omega

theorem tagFromU8Mem_code {M : Word → BitVec 8} {base out b : Word} {code : List Nat} (hc : CodeIn M base code)
    (h : Sep out 8 base code.length) : CodeIn (tagFromU8Mem M out b) base code := by
  have h4 : Sep out 4 base code.length := by
    have := h.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
  unfold tagFromU8Mem
  split
  · exact (hc.store8 (h.sub (c := 4) (l := 1) (by omega))).store32 h4
  · exact hc.store32 h4

theorem PanicCode.tagFromU8Mem {M : Word → BitVec 8} {out b : Word} (hP : PanicCode M)
    (h : out.toNat + 8 ≤ dramEnd) : PanicCode (tagFromU8Mem M out b) := by
  unfold C3.RV32.tagFromU8Mem
  split
  · refine (hP.store8 ?_).store32 (by omega)
    rw [BitVec.toNat_add, show (4 : Word).toNat = 4 from rfl]; omega
  · exact hP.store32 (by omega)

/-- `tagFromU8Mem` changes only the 8 bytes at `out`. -/
theorem tagFromU8Mem_out {M : Word → BitVec 8} {out b x : Word} (h : Sep out 8 x 1) :
    tagFromU8Mem M out b x = M x := by
  have h4 : Sep out 4 x 1 := by
    have := h.sub (c := 0) (l := 4) (by omega); rwa [add_ofNat_zero] at this
  unfold tagFromU8Mem
  split
  · rw [memStore32_get_sep h4, memStore8_ne (fun e => h 4 (by omega) 0 (by omega) (by
      rw [add_ofNat_zero]; exact e.symm))]
  · exact memStore32_get_sep h4

/-- A byte is a SEC1 tag that `Tag::from_u8` accepts. -/
def Sec1TagOk (t : BitVec 8) : Prop := t.toNat ≤ 5 ∧ t.toNat ≠ 1

instance (t : BitVec 8) : Decidable (Sec1TagOk t) := inferInstanceAs (Decidable (_ ∧ _))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The compiled `EncodedPoint::tag`** for the first byte `t`: for a tag
that `Tag::from_u8` accepts it returns `t` in `a0`; for any other byte it
panics. It changes no memory outside its 64-byte frame. -/
theorem encodedPointTag_correct (m : Machine) {retAddr : Word} {t : BitVec 8} (hP : PanicCode m.mem)
    (hc : CodeIn m.mem (BitVec.ofNat 32 encodedPointTagAddress) encodedPointTagCode)
    (hcT : CodeIn m.mem (BitVec.ofNat 32 tagFromU8Address) tagFromU8Code)
    (hcE : CodeIn m.mem (BitVec.ofNat 32 expectTagAddress) expectTagCode)
    (hpc : m.pc = BitVec.ofNat 32 encodedPointTagAddress) (ha0 : reg m a0 = t.zeroExtend 32)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hR : Room (reg m sp) 112) :
    (Sec1TagOk t → ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' a0 = t.zeroExtend 32 ∧ reg m' sp = reg m sp ∧
      (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg m' q = reg m q) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFC0) 0x40 x 1 → m'.mem x = m.mem x) ∧
    (¬ Sec1TagOk t → Panics m) := by
  let Q := BitVec.ofNat 32 encodedPointTagAddress
  obtain ⟨S, hS⟩ : ∃ S, reg m sp = S := ⟨_, rfl⟩
  rw [hS] at hR ⊢
  have hRG : Room (S + 0xFFFFFFC0) 48 := hR.frame64
  obtain ⟨hSa, hSl, hSh⟩ := hR
  unfold dramEnd at hSh
  obtain ⟨G, hG⟩ : ∃ G, S + 0xFFFFFFC0 = G := ⟨_, rfl⟩
  rw [hG] at hRG ⊢
  have hGn : G.toNat = S.toNat - 64 := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFFC0 : Word).toNat = 4294967232 from rfl]; omega
  have hGc : ∀ c, c ≤ 64 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have sk : ∀ c l, c + l ≤ 64 → ∀ (b : Word) (k : Nat), 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (G + BitVec.ofNat 32 c) l b k := fun c l h b k hb hbk => sep_of_le (by rw [hGc c (by omega)]; omega) hbk
  have s0 : St m.mem Q m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := s0.zero
  -- The frame, `a1 = t`, and `a0 = G + 8`.
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc ept_at_0 (off' := 2) (by decide)
  have e1 : aluEval .add (reg m sp) 0xFFFFFFC0 = G := by rw [ev_add, hS, hG]
  rw [e1] at u1
  obtain ⟨n2, d2, u2⟩ := u1.sw hc ept_at_2 (off' := 4) (by decide) (by
    simp +decide only [upd_app, ↓reduceIte]
    show (G + BitVec.ofNat 32 0x3C).toNat % 4 = 0
    rw [hGc _ (by omega), hGn]; omega)
  simp +decide only [upd_app, ↓reduceIte] at u2
  rw [hra] at u2
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore32 m.mem (G + 0x3C) retAddr = M2 := ⟨_, rfl⟩
  rw [hM2] at u2
  have fr2 : ∀ x, Sep (G + BitVec.ofNat 32 0x3C) 4 x 1 → M2 x = m.mem x := fun x hx => by
    rw [← hM2]; exact memStore32_get_sep hx
  have c2 : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn M2 b code := fun h hb hbl => by
    rw [← hM2]; exact h.store32 (sk 0x3C 4 (by omega) _ _ hb hbl)
  have hc2 := c2 hc (by decide) (by decide)
  obtain ⟨n3, d3, u3⟩ := u2.self.aluImm hc2 ept_at_4 (off' := 8) (by decide)
  obtain ⟨n4, d4, u4⟩ := u3.self.aluImm hc2 ept_at_8 (off' := 0xA) (by decide)
  have r4 : ∀ q, q ≠ a0 → q ≠ a1 → q ≠ sp → reg n4 q = reg m q := fun q h0 h1 h2 => by
    rw [u4.upd_ne u3.self.zero q h0, u3.upd_ne u2.self.zero q h1, u2.regs]; exact updz hz h2
  have sp4 : reg n4 sp = G := by
    rw [u4.upd_ne u3.self.zero sp (by decide), u3.upd_ne u2.self.zero sp (by decide), u2.regs]
    simp +decide only [upd_app, ↓reduceIte]
  have sp3 : reg n3 sp = G := by
    rw [u3.upd_ne u2.self.zero sp (by decide), u2.regs]; simp +decide only [upd_app, ↓reduceIte]
  have a04 : reg n4 a0 = G + 8 := by rw [u4.upd_eq (by decide), sp3]; rfl
  have a14 : reg n4 a1 = t.zeroExtend 32 := by
    rw [u4.upd_ne u3.self.zero a1 (by decide), u3.upd_eq (by decide), u2.regs]
    simp +decide only [upd_app, ↓reduceIte]; rw [ha0]; exact zext_and_ff t
  -- `Tag::from_u8`.
  obtain ⟨n5, c5, pc5, mem5, regs5⟩ := u4.self.callRa hc2 ept_at_a ept_at_e
    (show Q + BitVec.ofNat 32 0xA + 0xFFFFE000 + 0xFFFFFCD6 = BitVec.ofNat 32 tagFromU8Address by decide) (by decide)
  have r5 : ∀ q, q ≠ ra → reg n5 q = reg n4 q := fun q h => by rw [regs5]; exact updz u4.self.zero h
  have hO8 : Sep (G + BitVec.ofNat 32 8) 8 (BitVec.ofNat 32 tagFromU8Address) tagFromU8Code.length :=
    sk 8 8 (by omega) _ _ (by decide) (by decide)
  obtain ⟨n6, c6, pc6, mem6, regs6⟩ := tagFromU8_correct n5 (out := G + 8) (b := t.zeroExtend 32)
    (retAddr := Q + BitVec.ofNat 32 (0xA + 8)) (by rw [mem5]; exact c2 hcT (by decide) (by decide)) pc5
    (by rw [r5 a0 (by decide), a04]) (by rw [r5 a1 (by decide), a14])
    (by show (G + BitVec.ofNat 32 8).toNat % 4 = 0; rw [hGc _ (by omega), hGn]; omega) hO8
    (by rw [regs5]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at Q (by decide) _ (by decide)))
  rw [mem5] at mem6
  obtain ⟨M6, hM6⟩ : ∃ M6, tagFromU8Mem M2 (G + 8) (t.zeroExtend 32) = M6 := ⟨_, rfl⟩
  rw [hM6] at mem6
  have fr6 : ∀ x, Sep (G + BitVec.ofNat 32 8) 8 x 1 → M6 x = M2 x := fun x hx => by
    rw [← hM6]; exact tagFromU8Mem_out hx
  have cc6 : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn M6 b code := fun h hb hbl => by
    rw [← hM6]; exact tagFromU8Mem_code (c2 h hb hbl) (sk 8 8 (by omega) _ _ hb hbl)
  have hc6 := cc6 hc (by decide) (by decide)
  have u6 : St M6 Q n6 0x12 (reg n6) := ⟨by rw [pc6], mem6, fun _ => rfl⟩
  have k6 : ∀ q, q ≠ a2 → q ≠ a3 → q ≠ ra → reg n6 q = reg n4 q := fun q h2 h3 h1 => by
    rw [regs6 q h2 h3, r5 q h1]
  obtain ⟨n7, d7, u7⟩ := u6.aluImm hc6 ept_at_12 (off' := 0x14) (by decide)
  have sp7 : reg n7 sp = G := by
    rw [u7.upd_ne u6.zero sp (by decide), k6 sp (by decide) (by decide) (by decide), sp4]
  obtain ⟨n8, c8, pc8, mem8, regs8⟩ := u7.self.callRa hc6 ept_at_14 ept_at_18
    (show Q + BitVec.ofNat 32 0x14 + 0x0 + 0x12 = BitVec.ofNat 32 expectTagAddress by decide) (by decide)
  have r8 : ∀ q, q ≠ ra → reg n8 q = reg n7 q := fun q h => by rw [regs8]; exact updz u7.self.zero h
  have hP6 : PanicCode M6 := by
    rw [← hM6]
    refine PanicCode.tagFromU8Mem (by rw [← hM2]; exact hP.store32 (by show (G + BitVec.ofNat 32 0x3C).toNat + 4 ≤ dramEnd; rw [hGc _ (by omega)]; unfold dramEnd; omega))
      (by rw [show G + (8 : Word) = G + BitVec.ofNat 32 8 from rfl, hGc _ (by omega)]; unfold dramEnd; omega)
  have hE := expectTag_correct n8 (p := G + 8) (retAddr := Q + BitVec.ofNat 32 (0x14 + 8)) (by rw [mem8]; exact hP6)
    (by rw [mem8]; exact cc6 hcE (by decide) (by decide)) pc8
    (by rw [r8 a0 (by decide), u7.upd_eq (by decide), u6.regs, k6 sp (by decide) (by decide) (by decide), sp4]; rfl)
    (by show (G + BitVec.ofNat 32 8).toNat % 4 = 0; rw [hGc _ (by omega), hGn]; omega)
    (by rw [regs8]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at Q (by decide) _ (by decide)))
    (by rw [r8 sp (by decide), sp7]; exact hRG)
  have tz : (t.zeroExtend 32 : Word).toNat = t.toNat := ept_zext_tn t
  refine ⟨fun hok => ?_, fun hno => ?_⟩
  · have hok' : (t.zeroExtend 32 : Word).toNat ≤ 5 ∧ (t.zeroExtend 32 : Word).toNat ≠ 1 := by rw [tz]; exact hok
    have eOk : M6 = memStore32 (memStore8 M2 (G + 8 + 4) ((t.zeroExtend 32 : Word).extractLsb' 0 8)) (G + 8)
        0xFFFFFFFF := by rw [← hM6]; unfold tagFromU8Mem; rw [ite_eq_left hok']
    have hS84 : Sep (G + 8) 4 (G + 8 + 4) 1 := by
      show Sep (G + BitVec.ofNat 32 8) 4 (G + BitVec.ofNat 32 8 + BitVec.ofNat 32 4) 1
      rw [add_ofNat_assoc]
      exact sep_offsets G (c := 8) (n := 4) (d := 12) (k := 1) (Or.inl (by omega)) (by omega) (by omega)
    obtain ⟨n9, c9, pc9, a09, mem9, k9⟩ := hE.1 (by rw [mem8, eOk]; exact memLoad32_store32_same _ _ _)
    rw [mem8] at a09 mem9
    have a09' : reg n9 a0 = t.zeroExtend 32 := by
      rw [a09, eOk, memStore32_get_sep hS84, memStore8_same, tlv_zext]
    have u9 : St M6 Q n9 0x1C (reg n9) := ⟨by rw [pc9], mem9, fun _ => rfl⟩
    obtain ⟨n10, d10, u10⟩ := u9.aluImm hc6 ept_at_1c (off' := 0x20) (by decide)
    have sp9 : reg n9 sp = G := by
      rw [k9 sp (by decide) (by decide) (by decide), r8 sp (by decide), sp7]
    obtain ⟨n11, d11, u11⟩ := u10.self.lw hc6 ept_at_20 (off' := 0x22) (by decide) (by
      rw [u10.upd_ne u9.zero sp (by decide), sp9]
      show (G + BitVec.ofNat 32 0x3C).toNat % 4 = 0; rw [hGc _ (by omega), hGn]; omega)
    have eRa : memLoad32 M6 (reg n10 sp + 0x3C) = retAddr := by
      rw [u10.upd_ne u9.zero sp (by decide), sp9, eOk,
        memLoad32_store32_sep (by
          show Sep (G + BitVec.ofNat 32 8) 4 (G + BitVec.ofNat 32 0x3C) 4
          exact sep_offsets G (c := 8) (n := 4) (d := 0x3C) (k := 4) (Or.inl (by omega)) (by omega) (by omega)),
        memLoad32_store8_sep (by
          show Sep (G + BitVec.ofNat 32 8 + BitVec.ofNat 32 4) 1 (G + BitVec.ofNat 32 0x3C) 4
          rw [add_ofNat_assoc]
          exact sep_offsets G (c := 12) (n := 1) (d := 0x3C) (k := 4) (Or.inl (by omega)) (by omega) (by omega)),
        ← hM2, memLoad32_store32_same]
    rw [eRa] at u11
    obtain ⟨n12, d12, u12⟩ := u11.self.aluImm hc6 ept_at_22 (off' := 0x24) (by decide)
    obtain ⟨n13, d13, pc13, mem13, regs13⟩ := u12.self.jalr hc6 ept_at_24
    have k12 : ∀ q, q ≠ sp → reg n12 q = reg n11 q := fun q h => u12.upd_ne u11.self.zero q h
    have k11 : ∀ q, q ≠ ra → reg n11 q = reg n10 q := fun q h => u11.upd_ne u10.self.zero q h
    have k10 : ∀ q, q ≠ a0 → reg n10 q = reg n9 q := fun q h => u10.upd_ne u9.zero q h
    refine ⟨n13, .cons d1 (.cons d2 (.cons d3 (.cons d4 (c5.trans (c6.trans (.cons d7 (c8.trans (c9.trans
      (.cons d10 (.cons d11 (.cons d12 (.single d13)))))))))))), ?_, ?_, ?_, ?_, ?_⟩
    · rw [pc13, k12 ra (by decide), u11.upd_eq (by decide), add_lit_zero, hret]
    · rw [regs13, k12 a0 (by decide), k11 a0 (by decide), u10.upd_eq (by decide), a09']; exact zext_and_ff t
    · rw [regs13, u12.upd_eq (by decide), k11 sp (by decide), k10 sp (by decide), sp9, ← hG, ev_add,
        BitVec.add_assoc]
      exact BitVec.add_zero S
    · intro q q0 q1 q2 q3
      rw [regs13]
      by_cases qs : q = sp
      · subst qs; rw [u12.upd_eq (by decide), k11 sp (by decide), k10 sp (by decide), sp9, ← hG, ev_add,
          BitVec.add_assoc, hS]
        exact BitVec.add_zero S
      by_cases qr : q = ra
      · subst qr; rw [k12 ra (by decide), u11.upd_eq (by decide), hra]
      rw [k12 q qs, k11 q qr, k10 q q0, k9 q q0 q1 q2, r8 q qr, u7.upd_ne u6.zero q q0, u6.regs, k6 q q2 q3 qr,
        r4 q q0 q1 qs]
    · intro x hx
      rw [mem13, fr6 x (hx.sub (c := 8) (l := 8) (by omega)), fr2 x (hx.sub (c := 0x3C) (l := 4) (by omega))]
  · have eErr : M6 = memStore32 M2 (G + 8) 3 := by
      rw [← hM6]; unfold tagFromU8Mem
      exact ite_eq_right fun h => hno ⟨by rw [← tz]; exact h.1, by rw [← tz]; exact h.2⟩
    exact Panics.of_steps (.cons d1 (.cons d2 (.cons d3 (.cons d4 (c5.trans (c6.trans (.cons d7 c8)))))))
      (hE.2 (by rw [mem8, eErr, memLoad32_store32_same]; decide))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The compiled `EncodedPoint::is_identity`** for the first byte `t`:
for a tag that `Tag::from_u8` accepts it returns 1 when `t` is 0, the
identity's tag, and 0 otherwise; for any other byte it panics. It changes
no memory outside 0x50 bytes of stack below `sp`. -/
theorem encodedPointIsIdentity_correct (m : Machine) {retAddr : Word} {t : BitVec 8} (hP : PanicCode m.mem)
    (hc : CodeIn m.mem (BitVec.ofNat 32 encodedPointIsIdentityAddress) encodedPointIsIdentityCode)
    (hcG : CodeIn m.mem (BitVec.ofNat 32 encodedPointTagAddress) encodedPointTagCode)
    (hcT : CodeIn m.mem (BitVec.ofNat 32 tagFromU8Address) tagFromU8Code)
    (hcE : CodeIn m.mem (BitVec.ofNat 32 expectTagAddress) expectTagCode)
    (hpc : m.pc = BitVec.ofNat 32 encodedPointIsIdentityAddress) (ha0 : reg m a0 = t.zeroExtend 32)
    (hra : reg m ra = retAddr) (hret : retAddr &&& ~~~1 = retAddr) (hR : Room (reg m sp) 128) :
    (Sec1TagOk t → ∃ m', Steps m m' ∧ m'.pc = retAddr ∧ reg m' a0 = (if t = 0 then 1 else 0) ∧
      reg m' sp = reg m sp ∧ (∀ q, q ≠ a0 → q ≠ a1 → q ≠ a2 → q ≠ a3 → reg m' q = reg m q) ∧
      ∀ x, Sep (reg m sp + 0xFFFFFFB0) 0x50 x 1 → m'.mem x = m.mem x) ∧
    (¬ Sec1TagOk t → Panics m) := by
  let Q := BitVec.ofNat 32 encodedPointIsIdentityAddress
  obtain ⟨S, hS⟩ : ∃ S, reg m sp = S := ⟨_, rfl⟩
  rw [hS] at hR ⊢
  have hRG : Room (S + 0xFFFFFFF0) 112 := hR.frame
  obtain ⟨hSa, hSl, hSh⟩ := hR
  unfold dramEnd at hSh
  obtain ⟨G, hG⟩ : ∃ G, S + 0xFFFFFFF0 = G := ⟨_, rfl⟩
  rw [hG] at hRG
  have hGn : G.toNat = S.toNat - 16 := by
    rw [← hG, BitVec.toNat_add, show (0xFFFFFFF0 : Word).toNat = 4294967280 from rfl]; omega
  have hGc : ∀ c, c ≤ 16 → (G + BitVec.ofNat 32 c).toNat = G.toNat + c := fun c hc => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have sk : ∀ (b : Word) (k : Nat), 0x40000000 ≤ b.toNat → b.toNat + k ≤ 2 ^ 32 →
      Sep (G + BitVec.ofNat 32 0xC) 4 b k := fun b k hb hbk => sep_of_le (by rw [hGc _ (by omega)]; omega) hbk
  have s0 : St m.mem Q m 0 (reg m) := ⟨by rw [hpc, add_ofNat_zero], rfl, fun _ => rfl⟩
  have hz := s0.zero
  obtain ⟨n1, d1, u1⟩ := s0.aluImm hc epi_at_0 (off' := 2) (by decide)
  have e1 : aluEval .add (reg m sp) 0xFFFFFFF0 = G := by rw [ev_add, hS, hG]
  rw [e1] at u1
  obtain ⟨n2, d2, u2⟩ := u1.sw hc epi_at_2 (off' := 4) (by decide) (by
    simp +decide only [upd_app, ↓reduceIte]
    show (G + BitVec.ofNat 32 0xC).toNat % 4 = 0
    rw [hGc _ (by omega), hGn]; omega)
  simp +decide only [upd_app, ↓reduceIte] at u2
  rw [hra] at u2
  obtain ⟨M2, hM2⟩ : ∃ M2, memStore32 m.mem (G + 0xC) retAddr = M2 := ⟨_, rfl⟩
  rw [hM2] at u2
  have fr2 : ∀ x, Sep (G + BitVec.ofNat 32 0xC) 4 x 1 → M2 x = m.mem x := fun x hx => by
    rw [← hM2]; exact memStore32_get_sep hx
  have c2 : ∀ {b : Word} {code : List Nat}, CodeIn m.mem b code → 0x40000000 ≤ b.toNat →
      b.toNat + code.length ≤ 2 ^ 32 → CodeIn M2 b code := fun h hb hbl => by
    rw [← hM2]; exact h.store32 (sk _ _ hb hbl)
  have hc2 := c2 hc (by decide) (by decide)
  obtain ⟨n3, c3, pc3, mem3, regs3⟩ := u2.self.callRa hc2 epi_at_4 epi_at_8
    (show Q + BitVec.ofNat 32 0x4 + 0x0 + 0x16 = BitVec.ofNat 32 encodedPointTagAddress by decide) (by decide)
  have r3 : ∀ q, q ≠ ra → q ≠ sp → reg n3 q = reg m q := fun q h hs => by
    rw [regs3, updz u2.self.zero h, u2.regs]; exact updz hz hs
  have sp3 : reg n3 sp = G := by
    rw [regs3, updz u2.self.zero (by decide), u2.regs]; simp +decide only [upd_app, ↓reduceIte]
  have hT := encodedPointTag_correct n3 (t := t) (retAddr := Q + BitVec.ofNat 32 (0x4 + 8))
    (by rw [mem3, ← hM2]; exact hP.store32 (by
      show (G + BitVec.ofNat 32 0xC).toNat + 4 ≤ dramEnd; rw [hGc _ (by omega)]; unfold dramEnd; omega))
    (by rw [mem3]; exact c2 hcG (by decide) (by decide)) (by rw [mem3]; exact c2 hcT (by decide) (by decide))
    (by rw [mem3]; exact c2 hcE (by decide) (by decide)) pc3 (by rw [r3 a0 (by decide) (by decide), ha0])
    (by rw [regs3]; simp +decide only [upd_app, ↓reduceIte]) (even_clear _ (even_at Q (by decide) _ (by decide)))
    (by rw [sp3]; exact hRG)
  refine ⟨fun hok => ?_, fun hno => Panics.of_steps (.cons d1 (.cons d2 c3)) (hT.2 hno)⟩
  obtain ⟨n4, c4, pc4, a04, sp4, k4, fr4⟩ := hT.1 hok
  rw [sp3] at sp4 fr4
  rw [mem3] at fr4
  obtain ⟨M4, hM4⟩ : ∃ M4, n4.mem = M4 := ⟨_, rfl⟩
  rw [hM4] at fr4
  have hGl : (G + 0xFFFFFFC0).toNat = G.toNat - 64 := by
    rw [BitVec.toNat_add, show (0xFFFFFFC0 : Word).toNat = 4294967232 from rfl]; omega
  have hFG : ∀ c, c < 16 → Sep (G + 0xFFFFFFC0) 0x40 (G + BitVec.ofNat 32 c) 1 := fun c hc =>
    sep_of_le (by rw [hGl, hGc _ (by omega)]; omega) (by rw [hGc _ (by omega)]; omega)
  have hQn : Q.toNat = (img% encodedPointIsIdentityAddress) := by decide
  have hc4 : CodeIn M4 Q encodedPointIsIdentityCode := fun i hi => by
    rw [fr4 _ ((sep_of_le (b := Q) (k := encodedPointIsIdentityCode.length) (by rw [hGl, hQn]; omega)
      (by rw [hQn]; decide)).subR (c := i) (l := 1) hi)]
    exact hc2 i hi
  have u4 : St M4 Q n4 0xC (reg n4) := ⟨by rw [pc4], hM4, fun _ => rfl⟩
  obtain ⟨n5, d5, u5⟩ := u4.aluImm hc4 epi_at_c (off' := 0x10) (by decide)
  obtain ⟨n6, d6, u6⟩ := u5.self.aluImm hc4 epi_at_10 (off' := 0x14) (by decide)
  have k6 : ∀ q, q ≠ a0 → reg n6 q = reg n4 q := fun q h => by
    rw [u6.upd_ne u5.self.zero q h, u5.upd_ne u4.zero q h]
  obtain ⟨n7, d7, u7⟩ := u6.self.lw hc4 epi_at_14 (off' := 0x16) (by decide) (by
    rw [k6 sp (by decide), sp4]; show (G + BitVec.ofNat 32 0xC).toNat % 4 = 0; rw [hGc _ (by omega), hGn]; omega)
  have eRa : memLoad32 M4 (reg n6 sp + 0xC) = retAddr := by
    rw [k6 sp (by decide), sp4]
    rw [memLoad32_congr (M := M2) fun j hj => by
      show M4 (G + BitVec.ofNat 32 0xC + BitVec.ofNat 32 j) = M2 (G + BitVec.ofNat 32 0xC + BitVec.ofNat 32 j)
      rw [add_ofNat_assoc]; exact fr4 _ (hFG _ (by omega))]
    rw [← hM2]; exact memLoad32_store32_same _ _ _
  rw [eRa] at u7
  obtain ⟨n8, d8, u8⟩ := u7.self.aluImm hc4 epi_at_16 (off' := 0x18) (by decide)
  obtain ⟨n9, d9, pc9, mem9, regs9⟩ := u8.self.jalr hc4 epi_at_18
  have k8 : ∀ q, q ≠ sp → reg n8 q = reg n7 q := fun q h => u8.upd_ne u7.self.zero q h
  have k7 : ∀ q, q ≠ ra → reg n7 q = reg n6 q := fun q h => u7.upd_ne u6.self.zero q h
  have spF : reg n8 sp = S := by
    rw [u8.upd_eq (by decide), k7 sp (by decide), k6 sp (by decide), sp4, ← hG, ev_add, BitVec.add_assoc]
    exact BitVec.add_zero S
  have eGa : G + 0xFFFFFFC0 = S + 0xFFFFFFB0 := by rw [← hG, BitVec.add_assoc]; rfl
  have eGc : G + BitVec.ofNat 32 0xC = S + 0xFFFFFFB0 + BitVec.ofNat 32 0x4C := by
    rw [← hG, BitVec.add_assoc, BitVec.add_assoc]; rfl
  refine ⟨n9, .cons d1 (.cons d2 (c3.trans (c4.trans (.cons d5 (.cons d6 (.cons d7 (.cons d8 (.single d9)))))))),
    ?_, ?_, by rw [regs9, spF], fun q q0 q1 q2 q3 => ?_, fun x hx => ?_⟩
  · rw [pc9, k8 ra (by decide), u7.upd_eq (by decide), add_lit_zero, hret]
  · rw [regs9, k8 a0 (by decide), k7 a0 (by decide), u6.upd_eq (by decide), u5.self.regs, u5.upd_eq (by decide),
      a04, zext_and_ff]
    exact zext_seqz t
  · rw [regs9]
    by_cases qs : q = sp
    · subst qs; rw [spF, hS]
    by_cases qr : q = ra
    · subst qr; rw [k8 ra (by decide), u7.upd_eq (by decide), hra]
    rw [k8 q qs, k7 q qr, k6 q q0, k4 q q0 q1 q2 q3, r3 q qr qs]
  · rw [mem9, fr4 x (by rw [eGa]; have := hx.sub (c := 0) (l := 0x40) (by omega); rwa [add_ofNat_zero] at this),
      fr2 x (by rw [eGc]; exact hx.sub (c := 0x4C) (l := 4) (by omega))]

end C3.RV32
