import C3BootProofs.Proofs.AcceptBundleSegs

/-!
# `boot_main`'s first closure: the bundle stage

From 0x1816 to the call to `sigstore::verify` at 0x1A46: move the trust root
to `sp + 0x1870`, read the bundle part with a `Reader` at `sp + 0xDD0`
(`Reader::magic`, `Reader::version_1`, and `bundle::field` six times), and
lay the `Bundle` out at `sp + 0x1320` for `sigstore::verify`, with the
image's digest at `sp + 0x108`.
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3

/-- What holds at the call to `sigstore::verify` at 0x1A46 of a stage that
started in `n0`: the `Bundle` that `decodeBundle` makes of the bundle part's
`L` bytes at `Bf` is laid out at `sp + 0x1320`; the trust root's first five
bytes and the copy of its other 0x423 bytes from `sp + 0xDD0` are at
`sp + 0x1870`; the image's digest at `sp + 0x108` and the memory outside the
slots in `acbW` are as they were; and the registers hold the call's
arguments and return address. -/
structure AcBundlePost (B Bf : Word) (L : Nat) (n0 n : Machine) : Prop where
  bundle : ∃ b, decodeBundle (memBytes n0.mem Bf L) = some b ∧
    Sv.SvBundleAt (B + 0x13F0) n.mem (acSlot B 0x1320) b
  rootHdr : memLoad32 n.mem (acSlot B 0x1870) = 0x3FCC6621 ∧ n.mem (acSlot B 0x1874) = 0x2B
  root : memBytes n.mem (acSlot B 0x1875) 0x423 = memBytes n0.mem (acSlot B 0xDD0) 0x423
  digest : memBytes n.mem (acSlot B 0x108) 32 = memBytes n0.mem (acSlot B 0x108) 32
  keep : ∀ x, AcbOut acbW B x → n.mem x = n0.mem x
  a0 : reg n a0 = acSlot B 0xDD0
  a1 : reg n a1 = acSlot B 0x1320
  a2 : reg n a2 = acSlot B 0x1870
  a3 : reg n a3 = acSlot B 0x108
  ra : reg n ra = AC + BitVec.ofNat 32 0x1A42 + 0xC000

/-- **The bundle stage**, from 0x1816 to the call to `sigstore::verify` at
0x1A46. It reaches 0x1A46 only when the bundle part decodes, and then
`AcBundlePost` holds and `s5`, `s9`, and `s11` are as at 0x1816. -/
def AcBundleStage : Prop :=
  ∀ (n : Machine) (B Bf g t r : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (L : Nat),
    CodeIn n.mem AC bootMainClosure0Code → AcBundleEnv n.mem → Fr B 0x5A70 → Sep B 0x5A70 Bf acBufLen →
    St n.mem AC n 0x1816 (reg n) → AcInv B Bf g t v M0 n → memLoad32 n.mem (acSlot B 0x40) = r →
    AcBundlePre B Bf L n → AcStage B Bf g t r v M0 n 0x1A46 (fun n' =>
      AcBundlePost B Bf L n n' ∧ ∀ q : Fin 32, q.val ∈ [21, 25, 27] → reg n' q = reg n q)

theorem acb_sq (B : Word) (a : Nat) (k : Word) {c : Nat}
    (h : BitVec.ofNat 32 (0x3A50 + a) + k = BitVec.ofNat 32 (0x3A50 + c)) : acSlot B a + k = acSlot B c := by
  unfold acSlot; rw [BitVec.add_assoc, h]

/-- The `Bundle`'s struct is outside `sigstore::verify`'s stack. -/
theorem acb_bdIn {B : Word} (F : Fr B 0x5A70) : Sv.SvIn (B + 0x13F0) (acSlot B 0x1320) 0x30 := by
  have e1 : (acSlot B 0x1320).toNat = B.toNat + 0x4D70 := F.at _ (by decide)
  have := F.lo; have := F.hi
  have e2 : (B + 0x13F0 + 0xFFFFEA70).toNat = B.toNat - 0x1A0 := by
    rw [BitVec.toNat_add, BitVec.toNat_add]; simp only [BitVec.reduceToNat]; omega
  exact ⟨(sep_of_le (by rw [e2, e1]; omega) (by rw [e1]; omega)).symm, by rw [e1]; omega, by rw [e1]; omega⟩

/-- A field of the bundle part, as `sigstore::verify` reads it. -/
theorem acb_field {B Bf : Word} {L : Nat} {M M0 : Word → BitVec 8} (Y : AcbBuf B Bf L)
    (h : ∀ x, AcbOut acbW B x → M x = M0 x) {p l : Nat} {pw lw : Word} (hp : pw = Bf + BitVec.ofNat 32 p)
    (hl : lw.toNat = l) (hpl : p + l ≤ L) :
    Sv.SvBytesAt (B + 0x13F0) M pw lw (memBytes M0 (Bf + BitVec.ofNat 32 p) l) := by
  subst hp hl
  have := Y.hL
  exact ⟨Y.sv.sub (by omega), acb_bytesBuf h (by decide) Y.hs (by unfold acBufLen; omega)⟩

theorem acb_rootHdr {B : Word} {n0 n : Machine} (K : AcbK B n0 n) :
    memLoad32 n.mem (acSlot B 0x1870) = 0x3FCC6621 ∧ n.mem (acSlot B 0x1874) = 0x2B := by
  refine ⟨?_, ?_⟩
  · rw [memLoad32_congr (M := acbMi n0.mem B) (b := acSlot B 0x1870) fun j hj => by
      rw [add_ofNat_assoc]
      exact K.keep _ (acb_at (c := 0x3A50 + 0x1870) (l := 4) (by decide) (by decide) (by decide) hj)]
    unfold acbMi
    simp (disch := decide) only [acSlot, Nat.reduceAdd, acb_lsb, memLoad32_store32_same]
  · have h := K.keep (acSlot B 0x1874) (acb_at (c := 0x3A50 + 0x1874) (l := 1) (j := 0) (by decide) (by decide)
      (by decide) (by decide))
    rw [h]
    unfold acbMi
    exact memStore8_same _ _ _

theorem acb_root {B : Word} {n0 n : Machine} (K : AcbK B n0 n) :
    memBytes n.mem (acSlot B 0x1875) 0x423 = memBytes n0.mem (acSlot B 0xDD0) 0x423 := by
  unfold memBytes
  refine List.map_congr_left fun i hi => congrArg BitVec.toNat ?_
  have hi := List.mem_range.mp hi
  rw [K.keep (acSlot B 0x1875 + BitVec.ofNat 32 i) (by
      rw [add_ofNat_assoc]
      exact acb_at (c := 0x3A50 + 0x1875) (l := 0x423) (by decide) (by decide) (by decide) hi)]
  have h1 : Sep (acSlot B 0x1874) 1 (acSlot B 0x1875 + BitVec.ofNat 32 i) 1 := by
    rw [add_ofNat_assoc]; exact sep_offsets B (by omega) (by decide) (by omega)
  have h2 : Sep (acSlot B 0x1870) 4 (acSlot B 0x1875 + BitVec.ofNat 32 i) 1 := by
    rw [add_ofNat_assoc]; exact sep_offsets B (by omega) (by decide) (by omega)
  unfold acbMi
  rw [memStore8_ne (acb_ne1 h1), memStore32_get_sep h2, copyBytes_in hi (by decide)]

theorem acb_digest {B : Word} {n0 n : Machine} (K : AcbK B n0 n) :
    memBytes n.mem (acSlot B 0x108) 32 = memBytes n0.mem (acSlot B 0x108) 32 :=
  memBytes_congr fun i hi => by
    rw [add_ofNat_assoc]
    exact K.kw _ (acb_at (c := 0x3A50 + 0x108) (l := 32) (by decide) (by decide) (by decide) hi)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem acBundleStage : AcBundleStage := by
  intro n0 B Bf g t r v M0 L C E F hs s I hr P
  have G : AcbG B Bf g t r v M0 L n0 := ⟨C, E, ⟨F, hs, P.sv, P.hL⟩, I, hr⟩
  have hL := P.hL
  obtain ⟨n1, c1, K1, s1, ra0, ra1, R1⟩ := acb_init G s P
  refine acb_stage G (acb_pre c1 (acb_bind (acb_hdr G K1 s1 ra0 ra1 R1) ?_))
  rintro n2 K2 ⟨s2, R2, h6, hmag, hver⟩
  obtain ⟨l1, hl1⟩ : ∃ l, (memLoad32 n0.mem (Bf + BitVec.ofNat 32 6)).toNat = l := ⟨_, rfl⟩
  obtain ⟨l2, hl2⟩ : ∃ l, (memLoad32 n0.mem (Bf + BitVec.ofNat 32 (10 + l1))).toNat = l := ⟨_, rfl⟩
  refine acb_bind (acb_seg1 G K2 s2 R2 h6 hl1 hl2) ?_
  rintro n3 K3 ⟨s3, r26, r23, h38, h34, l1a, l1b, l2a, l2b, hq3, R3⟩
  refine acb_bind (acb_seg2 G K3 s3 R3 hq3) ?_
  rintro n4 K4 ⟨s4, ra4, r8, rk4, h8, hq4, R4, f4⟩
  rw [show 14 + l1 + l2 + 4 = 18 + l1 + l2 by omega] at ra4
  rw [show 14 + l1 + l2 + 12 = 26 + l1 + l2 by omega] at R4 hq4
  obtain ⟨l4, hl4⟩ : ∃ l, (memLoad32 n0.mem (Bf + BitVec.ofNat 32 (26 + l1 + l2))).toNat = l := ⟨_, rfl⟩
  have kb : ∀ k : Word, k.toNat < 8 →
      Bf + BitVec.ofNat 32 (18 + l1 + l2) + k = Bf + BitVec.ofNat 32 (18 + l1 + l2 + k.toNat) :=
    fun k hk => Dq.frame_lit k (by omega)
  have hP : ∀ k : Word, k.toNat < 8 → ∀ c : Nat, c + 4 ≤ 0x5A70 →
      Sep (B + BitVec.ofNat 32 c) 4 (Bf + BitVec.ofNat 32 (18 + l1 + l2) + k) 1 := fun k hk c hc => by
    rw [kb k hk]
    exact ((acb_bufSep hs hc (Nat.le_refl acBufLen)).sub (c := 18 + l1 + l2 + k.toNat) (l := 1)
      (by unfold acBufLen; omega)).symm
  refine acb_bind (acb_seg3 G K4 s4 ra4 r8 hP R4 hq4 hl4) ?_
  rintro n5 K5 ⟨s5, r18, r22, l4b, m4, hq5, R5, v30, v18, v14, v1C, v2C, v28, r19, r9, rk5, f5⟩
  rw [show 26 + l1 + l2 + 4 + l4 = 30 + l1 + l2 + l4 by omega] at hq5 R5
  rw [show 26 + l1 + l2 + 4 = 30 + l1 + l2 by omega] at r18
  obtain ⟨l5, hl5⟩ : ∃ l, (memLoad32 n0.mem (Bf + BitVec.ofNat 32 (30 + l1 + l2 + l4))).toNat = l :=
    ⟨_, rfl⟩
  refine acb_bind (acb_seg4 G K5 s5 R5 hq5 hl5) ?_
  rintro n6 K6 ⟨s6, r20, r24, l5a, l5b, hq6, R6, rk6, f6⟩
  rw [show 30 + l1 + l2 + l4 + 4 + l5 = 34 + l1 + l2 + l4 + l5 by omega] at hq6 R6
  rw [show 30 + l1 + l2 + l4 + 4 = 34 + l1 + l2 + l4 by omega] at r20
  obtain ⟨l6, hl6⟩ : ∃ l, (memLoad32 n0.mem (Bf + BitVec.ofNat 32 (34 + l1 + l2 + l4 + l5))).toNat = l :=
    ⟨_, rfl⟩
  refine acb_bind (acb_seg5 G K6 s6 R6 hq6 hl6) ?_
  rintro n7 K7 ⟨s7, ra7, w7, l6a, l6b, hL7, rk7, f7⟩
  rw [show 34 + l1 + l2 + l4 + l5 + 4 = 38 + l1 + l2 + l4 + l5 by omega] at ra7
  have f5' : ∀ x, AcbOut (acbFc ++ acbS) B x → n5.mem x = n4.mem x := fun x hx =>
    f5 x (acb_mono (by decide) hx) (acb_mono (by decide) hx)
  have ld75 : ∀ c : Nat, (∀ p ∈ acbFc, p.1 + p.2 ≤ c ∨ c + 4 ≤ p.1) → c + 4 ≤ 2 ^ 32 →
      memLoad32 n7.mem (B + BitVec.ofNat 32 c) = memLoad32 n5.mem (B + BitVec.ofNat 32 c) := fun c hW hc =>
    (acb_ld f7 hW hc (by decide)).trans (acb_ld f6 hW hc (by decide))
  have ld53 : ∀ c : Nat, (∀ p ∈ acbFc ++ acbS, p.1 + p.2 ≤ c ∨ c + 4 ≤ p.1) → c + 4 ≤ 2 ^ 32 →
      memLoad32 n5.mem (B + BitVec.ofNat 32 c) = memLoad32 n3.mem (B + BitVec.ofNat 32 c) := fun c hW hc =>
    (acb_ld f5' hW hc (by decide)).trans (acb_ld f4 (fun p hp => hW p (List.mem_append_left _ hp)) hc
      (by decide))
  have g38 : memLoad32 n7.mem (acSlot B 0x38) = Bf + BitVec.ofNat 32 (14 + l1) :=
    ((ld75 (0x3A50 + 0x38) (by decide) (by decide)).trans (ld53 _ (by decide) (by decide))).trans h38
  have g34 : memLoad32 n7.mem (acSlot B 0x34) = memLoad32 n3.mem (acSlot B 0x34) :=
    (ld75 (0x3A50 + 0x34) (by decide) (by decide)).trans (ld53 _ (by decide) (by decide))
  have g30 := (ld75 (0x3A50 + 0x30) (by decide) (by decide)).trans v30
  have g18 := (ld75 (0x3A50 + 0x18) (by decide) (by decide)).trans v18
  have g14 := (ld75 (0x3A50 + 0x14) (by decide) (by decide)).trans v14
  have g1C := (ld75 (0x3A50 + 0x1C) (by decide) (by decide)).trans v1C
  have g2C := (ld75 (0x3A50 + 0x2C) (by decide) (by decide)).trans v2C
  have g28 := (ld75 (0x3A50 + 0x28) (by decide) (by decide)).trans v28
  have g26 : reg n7 26 = Bf + BitVec.ofNat 32 10 := by
    rw [rk7 26 (by decide), rk6 26 (by decide), rk5 26 (by decide), rk4 26 (by decide)]; exact r26
  have g23 : reg n7 23 = reg n3 23 := by
    rw [rk7 23 (by decide), rk6 23 (by decide), rk5 23 (by decide), rk4 23 (by decide)]
  have g18r : reg n7 18 = Bf + BitVec.ofNat 32 (30 + l1 + l2) := by
    rw [rk7 18 (by decide), rk6 18 (by decide)]; exact r18
  have g22 : reg n7 22 = reg n5 22 := by rw [rk7 22 (by decide), rk6 22 (by decide)]
  have g20 : reg n7 20 = Bf + BitVec.ofNat 32 (34 + l1 + l2 + l4) := by rw [rk7 20 (by decide)]; exact r20
  have g24 : reg n7 24 = reg n6 24 := rk7 24 (by decide)
  have g19 := (rk7 19 (by decide)).trans ((rk6 19 (by decide)).trans r19)
  have g9 := (rk7 9 (by decide)).trans ((rk6 9 (by decide)).trans r9)
  obtain ⟨n8, c8, K8, pc8, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, qa0, qa1, qa2, qa3, qra, -⟩ :=
    acb_seg6 G K7 s7 g26 g23 g38 g34 g18r g22 g20 g24 ra7 rfl g9 g1C g2C g28 g30 g19 g18 g14
  refine acb_pre c8 (acb_ret K8 ⟨pc8, ?_⟩)
  have kb0 : ∀ k : Word, k.toNat < 8 →
      n4.mem (Bf + BitVec.ofNat 32 (18 + l1 + l2) + k) = n0.mem (Bf + BitVec.ofNat 32 (18 + l1 + l2) + k) :=
    fun k hk => by
      rw [kb k hk]; exact K4.kw _ (acb_buf (by decide) hs (by unfold acBufLen; omega))
  obtain ⟨u1, u2, u3⟩ := acb_u64 n0.mem (Bf + BitVec.ofNat 32 (18 + l1 + l2)) rfl rfl
  have hd := acb_decode (L := L) n0.mem Bf hmag hver hl1 ⟨l1a, l1b⟩ hl2 ⟨l2a, l2b⟩ h8 hl4 l4b m4 hl5 ⟨l5a, l5b⟩ hl6
    ⟨l6a, l6b⟩ (by omega)
  have e5 : Bf + BitVec.ofNat 32 (18 + l1 + l2) + 4 + 1 = Bf + BitVec.ofNat 32 (18 + l1 + l2) + 5 := by
    rw [BitVec.add_assoc]; rfl
  have e6 : Bf + BitVec.ofNat 32 (18 + l1 + l2) + 4 + 2 = Bf + BitVec.ofNat 32 (18 + l1 + l2) + 6 := by
    rw [BitVec.add_assoc]; rfl
  have e7 : Bf + BitVec.ofNat 32 (18 + l1 + l2) + 4 + 3 = Bf + BitVec.ofNat 32 (18 + l1 + l2) + 7 := by
    rw [BitVec.add_assoc]; rfl
  refine ⟨⟨_, hd, acb_al F _ (by decide) (by decide), acb_bdIn F, ?_, ?_, ?_, ?_, ?_, ?_⟩, acb_rootHdr K8,
    acb_root K8, acb_digest K8, K8.kw, qa0, qa1, qa2, qa3, qra⟩
  · rw [acb_sq B 0x1320 4 (c := 0x1324) (by decide), q1, q2]
    exact acb_field G.Y K8.kw rfl r23 (by omega)
  · rw [acb_sq B 0x1320 8 (c := 0x1328) (by decide), acb_sq B 0x1320 0xC (c := 0x132C) (by decide), q3, q4]
    exact acb_field G.Y K8.kw rfl h34 (by omega)
  · rw [acb_sq B 0x1320 0x10 (c := 0x1330) (by decide), acb_sq B 0x1320 0x14 (c := 0x1334) (by decide), q5, q6]
    exact acb_field G.Y K8.kw rfl r22 (by omega)
  · rw [acb_sq B 0x1320 0x18 (c := 0x1338) (by decide), acb_sq B 0x1320 0x1C (c := 0x133C) (by decide), q7, q8]
    exact acb_field G.Y K8.kw rfl r24 (by omega)
  · rw [acb_sq B 0x1320 0x20 (c := 0x1340) (by decide), acb_sq B 0x1320 0x24 (c := 0x1344) (by decide), q9,
      q10]
    exact acb_field G.Y K8.kw rfl w7 (by omega)
  · unfold Sv.SvU64At
    rw [acb_sq B 0x1320 0x28 (c := 0x1348) (by decide), acb_sq B 0x1348 4 (c := 0x134C) (by decide)]
    refine ⟨u1, ?_, ?_⟩
    · rw [u2]; apply BitVec.eq_of_toNat_eq
      rw [q11, memLoad32_toNat, kb0 0 (by decide), kb0 1 (by decide), kb0 2 (by decide), kb0 3 (by decide),
        show Bf + BitVec.ofNat 32 (18 + l1 + l2) + 0 = Bf + BitVec.ofNat 32 (18 + l1 + l2) from BitVec.add_zero _]
    · rw [u3]; apply BitVec.eq_of_toNat_eq
      rw [q12, memLoad32_toNat, e5, e6, e7, kb0 4 (by decide), kb0 5 (by decide), kb0 6 (by decide),
        kb0 7 (by decide)]

end C3.RV32.Ac
