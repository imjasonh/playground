import C3BootProofs.Proofs.TufRoleKeysKey

/-!
# `decode_key`'s key decodes, inlined in `RoleKeys::read`

Once the key type and the scheme match, `RoleKeys::read` decodes the public
key text: an ECDSA key with `pem_spki`, whose DER it checks against the
curve's SPKI prefix before it copies the point to `F + 0x55C`, and an
Ed25519 key with `hex_decode`, whose 32 bytes it copies there. Each path
ends at 0x628 with the key's tag in `a0`, or at 0x6EA without a key.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

theorem rk_pemLen {pem bs : Bytes} (h : pemSpkiModel pem = some bs) : bs.length ≤ 128 := by
  unfold pemSpkiModel pemDecode at h
  split at h
  · split at h
    · split at h
      · split at h
        · cases h; assumption
        · cases h
      · cases h
    · cases h
  · cases h

theorem rk_ultb (a b : Word) : branchTaken .bltu a b = decide (a.toNat < b.toNat) := rfl

theorem rk_bneF {a b : Word} (h : branchTaken .bne a b = false) : a = b := by
  simpa [branchTaken] using h

theorem rk_inj {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : BitVec.ofNat 32 a = BitVec.ofNat 32 b) :
    a = b := by
  have := congrArg BitVec.toNat h; rwa [ofNat_tn ha, ofNat_tn hb] at this

theorem rk_addne {L c : Nat} {k : Word} (hk : k + BitVec.ofNat 32 c = 0) (hL : L < 2 ^ 32) (hc : c < 2 ^ 32)
    (h : L ≠ c) : BitVec.ofNat 32 L + k ≠ 0 := fun e => h (rk_inj hL hc (by
  calc BitVec.ofNat 32 L = BitVec.ofNat 32 L + k + BitVec.ofNat 32 c := by
        rw [BitVec.add_assoc, hk]; exact (BitVec.add_zero _).symm
    _ = BitVec.ofNat 32 c := by rw [e]; exact BitVec.zero_add _))

theorem rkSpki_of {t kl : Nat} {pfx pub der : Bytes} (hq : pemSpkiModel pub = some der) :
    rkSpki t pfx kl pub = if der.take pfx.length = pfx ∧ der.length = pfx.length + kl then
      some (t, der.drop pfx.length) else none := by
  unfold rkSpki; rw [hq]

theorem rk_mbCopy {M : Word → BitVec 8} {dst src : Word} {n : Nat} (hn : n < 2 ^ 32) :
    memBytes (copyBytes M dst src n) dst n = memBytes M src n := by
  unfold memBytes
  exact List.map_congr_left fun i hi => by rw [copyBytes_at (List.mem_range.mp hi) hn]

theorem rk_mbTake {M : Word → BitVec 8} {p : Word} {n k : Nat} (h : k ≤ n) :
    (memBytes M p n).take k = memBytes M p k := by
  have := tuf_memBytes_drop_take (M := M) (p := p) (n := n) (h := 0) (l := k) (by omega)
  rwa [List.drop_zero, add_ofNat_zero] at this

theorem rk_mbDrop {M : Word → BitVec 8} {p : Word} {n k : Nat} (h : k ≤ n) :
    (memBytes M p n).drop k = memBytes M (p + BitVec.ofNat 32 k) (n - k) := by
  have := tuf_memBytes_drop_take (M := M) (p := p) (n := n) (h := k) (l := n - k) (by omega)
  rwa [List.take_of_length_le (by rw [List.length_drop, memBytes_length]; omega)] at this

section
variable {M0 M1 Md M : Word → BitVec 8} {s out F P : Word} {N : Nat} {g0 gL g : Fin 32 → Word} {Q : Post}

theorem RkW.tps (E : RkEnv M0 M1 s out F P N g0) {M' : Word → BitVec 8} (hW : RkW s Md M)
    (h : ∀ x, Sep x 1 s 304 → Sep x 1 (F + 0x75C) 128 → M' x = M x) : RkW s Md M' :=
  hW.out2 (c1 := 0) (k1 := 304) (c2 := 2188) (k2 := 128)
    (fun x h1 h2 => h x (by rwa [add_ofNat_zero] at h1) (by
      rw [show F + 0x75C = F + BitVec.ofNat 32 0x75C from rfl, E.Fc]; exact h2))
    (Or.inl (by decide)) (Or.inr (Or.inl (by decide)))

theorem RkEnv.F75 (E : RkEnv M0 M1 s out F P N g0) : (F + 0x75C : Word) ≠ 0 := fun e => by
  have := E.FN (c := 0x75C) (by decide)
  rw [show F + BitVec.ofNat 32 0x75C = F + 0x75C from rfl, e, show (0 : Word).toNat = 0 from rfl] at this
  omega

/-- The P-256 key at 0x4F2: `pem_spki` on the public key text, the
26-byte SPKI prefix, and the 65-byte point. -/
theorem rk_p256 (E : RkEnv M0 M1 s out F P N g0) (hOd : Out M1 Md s 3004) (hW : RkW s Md M)
    (hL0 : gL 0 = 0) (hLsp : gL sp = F) (hL24 : gL 24 = F + 0xA6C) (hk : ∀ x, x ∉ rkDc → g x = gL x)
    {pq : Word} {pl : Nat} {pub : Bytes} (h8 : g 8 = pq) (h9 : g 9 = BitVec.ofNat 32 pl)
    (h22 : (g 22).extractLsb' 0 8 = 0xFF) (hpw : pq.toNat + pl ≤ 0x40000000) (hSp : Sep s 3056 pq pl)
    (hpub : memBytes M pq pl = pub) (K : RkK Q s F gL Md (rkSpki 0 p256SpkiPrefix 65 pub)) :
    WP tufRoleKeysReadCode TRK Q M 0x4F2 g := by
  have hO : Out M1 M s 3004 := hOd.trans hW.outer
  have hc := E.code hO
  have hsp : g sp = F := (hk sp (by decide)).trans hLsp
  refine WP.aluImm rkr_at_4f2 ?_; wn
  refine WP.alu rkr_at_4f6 ?_; wn
  refine WP.alu rkr_at_4f8 ?_; wn
  refine WP.callTps (out := F + 0x75C) (s := s) (p := pq) (n := pl) rkr_at_4fa rkr_at_4fe (by decide) (by decide)
    hc.tps (by rsimp; rw [ev0, h8]) (by rsimp; rw [ev0, h9])
    (by rsimp; rw [hsp]; rfl) (by rsimp; rw [hsp, E.hF]) E.hal (by have := E.hsw; omega)
    (tex_sepL E.hro (by decide)) hpw (tex_sepL hSp (by decide)) (E.wF (c := 0x75C) (by decide))
    (by have := E.fs (c := 0x75C) (n := 128) (d := 0) (k := 304) (Or.inr (by decide)) (by decide) (by decide)
        rwa [add_ofNat_zero] at this)
    (by have := E.cS (c := 0) (w := 304) (by decide); rwa [add_ofNat_zero] at this)
    (E.cF (c := 0x75C) (by decide)) fun m2 hR => ?_
  wn
  rw [hpub] at hR
  rcases hq : pemSpkiModel pub with _ | der <;> rw [hq] at hR
  · have hm : rkSpki 0 p256SpkiPrefix 65 pub = none := by unfold rkSpki; rw [hq]
    rw [hm] at K
    refine WP.branch rkr_at_502 (fun _ => ?_) (fun eb => ?_)
    · wn
      exact rk_6ea hL0 hLsp hL24 (by keepz hL0) (hW.tps E hR.1) (by rsimp; exact h22) K
    · exfalso; rsimp at eb; rw [hR.2] at eb; exact absurd eb (by decide)
  obtain ⟨hfr, ha0, ha1, hder⟩ := hR
  have hdl : der.length ≤ 128 := rk_pemLen hq
  have hW2 := hW.tps E hfr
  have hO2 : Out M1 m2.mem s 3004 := hOd.trans hW2.outer
  have hc2 := E.code hO2
  refine WP.branch rkr_at_502 (fun eb => ?_) (fun _ => ?_)
  · exfalso; rsimp at eb; rw [ha0] at eb; exact E.F75 (beq_iff_eq.mp eb)
  wn
  refine WP.alu rkr_at_506 ?_; wn
  refine WP.alu rkr_at_508 ?_; wn
  refine WP.aluImm rkr_at_50a ?_; wn
  have hdl32 : der.length < 2 ^ 32 := by omega
  refine WP.branch rkr_at_50c (fun eb => ?_) (fun eb => ?_)
  · rsimp at eb
    simp only [rk_ultb, ev0, ha1, ofNat_tn hdl32, BitVec.reduceToNat, decide_eq_true_eq] at eb
    have hm : rkSpki 0 p256SpkiPrefix 65 pub = none := by
      rw [rkSpki_of hq, if_neg (fun h => by have := h.2; rw [show p256SpkiPrefix.length = 26 from rfl] at this; omega)]
    rw [hm] at K
    wn
    exact rk_6ea hL0 hLsp hL24 (by keepz hL0) hW2 (by rsimp; exact h22) K
  rsimp at eb
  simp only [rk_ultb, ev0, ha1, ofNat_tn hdl32, BitVec.reduceToNat, decide_eq_false_iff_not] at eb
  have h26 : 26 ≤ der.length := by omega
  wn
  refine WP.aluImm rkr_at_510 ?_; wn
  refine WP.alu rkr_at_512 ?_; wn
  refine WP.lui rkr_at_514 ?_; wn
  refine WP.aluImm rkr_at_518 ?_; wn
  refine WP.callEsl (tb := TPS_ESL) (q1 := F + 0x75C) (q2 := TRK_P256) (r := s + BitVec.ofNat 32 300) (l := 26)
    rkr_at_51c rkr_at_520 (by decide) (by decide) (by decide) hc2.tps.esl hc2.tps.mc
    (by rsimp; simp only [ev0, ha0]) (by rsimp; try rfl) (by rsimp; try rfl) (by decide)
    (by rsimp; rw [hsp, ← E.hF, BitVec.add_assoc]; rfl) (by rsimp; rw [hsp]; exact E.halF)
    (E.lowS (by decide) (by decide) (by decide)) (E.lowS (by decide) (by decide) (by decide))
    (E.fs (c := 0x75C) (n := 26) (d := 300) (k := 4) (Or.inr (by decide)) (by decide) (by decide)).symm
    (tuf_sep_ro (E.hro.sub (c := 300) (l := 4) (by decide)) (by decide) (by decide)) (E.cS (by decide))
    fun m3 r3 hO3 => ?_
  wn
  have hW3 : RkW s Md m3.mem := hW2.out hO3 (Or.inl (by decide))
  have hO3' : Out M1 m3.mem s 3004 := hOd.trans hW3.outer
  have hc3 := E.code hO3'
  rw [← rk_mbTake (n := der.length) h26, hder, hc2.mP256] at r3
  have hpl : p256SpkiPrefix.length = 26 := rfl
  by_cases hpf : der.take 26 = p256SpkiPrefix
  rotate_left
  · have hm : rkSpki 0 p256SpkiPrefix 65 pub = none := by
      rw [rkSpki_of hq, if_neg (fun h => hpf (by rw [← hpl]; exact h.1))]
    rw [hm] at K
    rw [if_neg hpf] at r3
    refine WP.branch rkr_at_524 (fun _ => ?_) (fun eb => ?_)
    · wn
      exact rk_6ea hL0 hLsp hL24 (by keepz hL0) hW3 (by rsimp; exact h22) K
    · exfalso; rsimp at eb; rw [r3] at eb; exact absurd eb (by decide)
  rw [if_pos hpf] at r3
  refine WP.branch rkr_at_524 (fun eb => ?_) (fun _ => ?_)
  · exfalso; rsimp at eb; rw [r3] at eb; exact absurd eb (by decide)
  wn
  refine WP.aluImm rkr_at_528 ?_; wn
  by_cases h91 : der.length = 91
  rotate_left
  · have hm : rkSpki 0 p256SpkiPrefix 65 pub = none := by
      rw [rkSpki_of hq, if_neg (fun h => h91 (by rw [h.2, hpl]))]
    rw [hm] at K
    refine WP.branch rkr_at_52c (fun _ => ?_) (fun eb => ?_)
    · wn
      exact rk_6ea hL0 hLsp hL24 (by keepz hL0) hW3 (by rsimp; exact h22) K
    · exfalso; rsimp at eb; rw [ha1] at eb
      rw [ev0, ev_add] at eb
      exact rk_addne (c := 91) (by decide) hdl32 (by decide) h91 (rk_bneF eb)
  refine WP.branch rkr_at_52c (fun eb => ?_) (fun _ => ?_)
  · exfalso; rsimp at eb; rw [ha1, h91] at eb; exact absurd eb (by decide)
  wn
  have hm : rkSpki 0 p256SpkiPrefix 65 pub = some (0, der.drop 26) := by
    rw [rkSpki_of hq, if_pos ⟨by rw [hpl]; exact hpf, by rw [h91, hpl]⟩, hpl]
  rw [hm] at K
  refine WP.aluImm rkr_at_530 ?_; wn
  refine WP.aluImm rkr_at_534 ?_; wn
  refine WP.aluImm rkr_at_538 ?_; wn
  refine WP.callMemcpy (dst := F + 0x55C) (src := F + 0x776) (F := s + BitVec.ofNat 32 288) (N := 65)
    rkr_at_53c rkr_at_540 (by decide) (by decide) (by decide) hc3.tps.bms
    (E.mcFF hc3 (c := 0x55C) (d := 0x776) (n := 65) (Or.inl (by decide)) (by decide) (by decide) (by decide)
      (by decide))
    (by rsimp; rw [hsp]; rfl) (by rsimp; rw [ha0, ev0, ev_add, BitVec.add_assoc]; rfl) (by rsimp; try rfl)
    (by rsimp; rw [hsp]; exact (E.sp 288 (by decide)).symm) (E.cS (by decide)) (E.cF (c := 0x55C) (by decide))
    fun m4 hm4 => ?_
  wn
  refine WP.aluImm rkr_at_544 ?_; wn
  refine WP.jal rkr_at_546 (by decide) ?_; wn
  have hcp : Out m3.mem (copyBytes m3.mem (F + 0x55C) (F + 0x776) 65) (s + BitVec.ofNat 32 1676) 65 := fun x hx => by
    rw [show F + 0x55C = s + BitVec.ofNat 32 1676 from E.Fc 0x55C]; exact copyBytes_sep hx.symm (Nat.le_refl _)
  have hW4 : RkW s Md m4.mem := (hW3.out hcp (Or.inr (Or.inl (by decide)))).out hm4 (Or.inl (by decide))
  refine rk_628 hL0 hLsp hL24 (by keepz hL0) hW4 (by rsimp; rfl) ?_ K
  refine ⟨by rw [List.length_drop, h91]; decide, ?_⟩
  rw [List.length_drop, h91]
  show memBytes m4.mem (F + 0x55C) 65 = _
  rw [hm4.bytes (p := F + 0x55C) (n := 65) (E.fs (c := 0x55C) (n := 65) (d := 288) (k := 16) (Or.inr (by decide)) (by decide) (by decide)).symm,
    rk_mbCopy (by decide), hO3.bytes (p := F + 0x776) (n := 65) (E.fs (c := 0x776) (n := 65) (d := 300) (k := 4) (Or.inr (by decide)) (by decide)
      (by decide)).symm, ← hder, rk_mbDrop h26, h91, BitVec.add_assoc]
  rfl


/-- The P-384 key at 0x69A: `pem_spki` on the public key text, the
23-byte SPKI prefix, and the 97-byte point. -/
theorem rk_p384 (E : RkEnv M0 M1 s out F P N g0) (hOd : Out M1 Md s 3004) (hW : RkW s Md M)
    (hL0 : gL 0 = 0) (hLsp : gL sp = F) (hL24 : gL 24 = F + 0xA6C) (hk : ∀ x, x ∉ rkDc → g x = gL x)
    {pq : Word} {pl : Nat} {pub : Bytes} (h8 : g 8 = pq) (h9 : g 9 = BitVec.ofNat 32 pl)
    (h22 : (g 22).extractLsb' 0 8 = 0xFF) (hpw : pq.toNat + pl ≤ 0x40000000) (hSp : Sep s 3056 pq pl)
    (hpub : memBytes M pq pl = pub) (K : RkK Q s F gL Md (rkSpki 1 p384SpkiPrefix 97 pub)) :
    WP tufRoleKeysReadCode TRK Q M 0x69A g := by
  have hO : Out M1 M s 3004 := hOd.trans hW.outer
  have hc := E.code hO
  have hsp : g sp = F := (hk sp (by decide)).trans hLsp
  refine WP.aluImm rkr_at_69a ?_; wn
  refine WP.alu rkr_at_69e ?_; wn
  refine WP.alu rkr_at_6a0 ?_; wn
  refine WP.callTps (out := F + 0x75C) (s := s) (p := pq) (n := pl) rkr_at_6a2 rkr_at_6a6 (by decide) (by decide)
    hc.tps (by rsimp; rw [ev0, h8]) (by rsimp; rw [ev0, h9])
    (by rsimp; rw [hsp]; rfl) (by rsimp; rw [hsp, E.hF]) E.hal (by have := E.hsw; omega)
    (tex_sepL E.hro (by decide)) hpw (tex_sepL hSp (by decide)) (E.wF (c := 0x75C) (by decide))
    (by have := E.fs (c := 0x75C) (n := 128) (d := 0) (k := 304) (Or.inr (by decide)) (by decide) (by decide)
        rwa [add_ofNat_zero] at this)
    (by have := E.cS (c := 0) (w := 304) (by decide); rwa [add_ofNat_zero] at this)
    (E.cF (c := 0x75C) (by decide)) fun m2 hR => ?_
  wn
  rw [hpub] at hR
  rcases hq : pemSpkiModel pub with _ | der <;> rw [hq] at hR
  · have hm : rkSpki 1 p384SpkiPrefix 97 pub = none := by unfold rkSpki; rw [hq]
    rw [hm] at K
    refine WP.branch rkr_at_6aa (fun _ => ?_) (fun eb => ?_)
    · wn
      exact rk_6ea hL0 hLsp hL24 (by keepz hL0) (hW.tps E hR.1) (by rsimp; exact h22) K
    · exfalso; rsimp at eb; rw [hR.2] at eb; exact absurd eb (by decide)
  obtain ⟨hfr, ha0, ha1, hder⟩ := hR
  have hdl : der.length ≤ 128 := rk_pemLen hq
  have hW2 := hW.tps E hfr
  have hO2 : Out M1 m2.mem s 3004 := hOd.trans hW2.outer
  have hc2 := E.code hO2
  refine WP.branch rkr_at_6aa (fun eb => ?_) (fun _ => ?_)
  · exfalso; rsimp at eb; rw [ha0] at eb; exact E.F75 (beq_iff_eq.mp eb)
  wn
  refine WP.alu rkr_at_6ac ?_; wn
  refine WP.alu rkr_at_6ae ?_; wn
  refine WP.aluImm rkr_at_6b0 ?_; wn
  have hdl32 : der.length < 2 ^ 32 := by omega
  refine WP.branch rkr_at_6b2 (fun eb => ?_) (fun eb => ?_)
  · rsimp at eb
    simp only [rk_ultb, ev0, ha1, ofNat_tn hdl32, BitVec.reduceToNat, decide_eq_true_eq] at eb
    have hm : rkSpki 1 p384SpkiPrefix 97 pub = none := by
      rw [rkSpki_of hq, if_neg (fun h => by have := h.2; rw [show p384SpkiPrefix.length = 23 from rfl] at this; omega)]
    rw [hm] at K
    wn
    exact rk_6ea hL0 hLsp hL24 (by keepz hL0) hW2 (by rsimp; exact h22) K
  rsimp at eb
  simp only [rk_ultb, ev0, ha1, ofNat_tn hdl32, BitVec.reduceToNat, decide_eq_false_iff_not] at eb
  have h26 : 23 ≤ der.length := by omega
  wn
  refine WP.aluImm rkr_at_6b6 ?_; wn
  refine WP.alu rkr_at_6b8 ?_; wn
  refine WP.lui rkr_at_6ba ?_; wn
  refine WP.aluImm rkr_at_6be ?_; wn
  refine WP.callEsl (tb := TPS_ESL) (q1 := F + 0x75C) (q2 := TRK_P384) (r := s + BitVec.ofNat 32 300) (l := 23)
    rkr_at_6c2 rkr_at_6c6 (by decide) (by decide) (by decide) hc2.tps.esl hc2.tps.mc
    (by rsimp; simp only [ev0, ha0]) (by rsimp; try rfl) (by rsimp; try rfl) (by decide)
    (by rsimp; rw [hsp, ← E.hF, BitVec.add_assoc]; rfl) (by rsimp; rw [hsp]; exact E.halF)
    (E.lowS (by decide) (by decide) (by decide)) (E.lowS (by decide) (by decide) (by decide))
    (E.fs (c := 0x75C) (n := 23) (d := 300) (k := 4) (Or.inr (by decide)) (by decide) (by decide)).symm
    (tuf_sep_ro (E.hro.sub (c := 300) (l := 4) (by decide)) (by decide) (by decide)) (E.cS (by decide))
    fun m3 r3 hO3 => ?_
  wn
  have hW3 : RkW s Md m3.mem := hW2.out hO3 (Or.inl (by decide))
  have hO3' : Out M1 m3.mem s 3004 := hOd.trans hW3.outer
  have hc3 := E.code hO3'
  rw [← rk_mbTake (n := der.length) h26, hder, hc2.mP384] at r3
  have hpl : p384SpkiPrefix.length = 23 := rfl
  by_cases hpf : der.take 23 = p384SpkiPrefix
  rotate_left
  · have hm : rkSpki 1 p384SpkiPrefix 97 pub = none := by
      rw [rkSpki_of hq, if_neg (fun h => hpf (by rw [← hpl]; exact h.1))]
    rw [hm] at K
    rw [if_neg hpf] at r3
    refine WP.branch rkr_at_6ca (fun _ => ?_) (fun eb => ?_)
    · wn
      exact rk_6ea hL0 hLsp hL24 (by keepz hL0) hW3 (by rsimp; exact h22) K
    · exfalso; rsimp at eb; rw [r3] at eb; exact absurd eb (by decide)
  rw [if_pos hpf] at r3
  refine WP.branch rkr_at_6ca (fun eb => ?_) (fun _ => ?_)
  · exfalso; rsimp at eb; rw [r3] at eb; exact absurd eb (by decide)
  wn
  refine WP.aluImm rkr_at_6cc ?_; wn
  by_cases h91 : der.length = 120
  rotate_left
  · have hm : rkSpki 1 p384SpkiPrefix 97 pub = none := by
      rw [rkSpki_of hq, if_neg (fun h => h91 (by rw [h.2, hpl]))]
    rw [hm] at K
    refine WP.branch rkr_at_6d0 (fun _ => ?_) (fun eb => ?_)
    · wn
      exact rk_6ea hL0 hLsp hL24 (by keepz hL0) hW3 (by rsimp; exact h22) K
    · exfalso; rsimp at eb; rw [ha1] at eb
      rw [ev0, ev_add] at eb
      exact rk_addne (c := 120) (by decide) hdl32 (by decide) h91 (rk_bneF eb)
  refine WP.branch rkr_at_6d0 (fun eb => ?_) (fun _ => ?_)
  · exfalso; rsimp at eb; rw [ha1, h91] at eb; exact absurd eb (by decide)
  wn
  have hm : rkSpki 1 p384SpkiPrefix 97 pub = some (1, der.drop 23) := by
    rw [rkSpki_of hq, if_pos ⟨by rw [hpl]; exact hpf, by rw [h91, hpl]⟩, hpl]
  rw [hm] at K
  refine WP.aluImm rkr_at_6d2 ?_; wn
  refine WP.aluImm rkr_at_6d6 ?_; wn
  refine WP.aluImm rkr_at_6da ?_; wn
  refine WP.callMemcpy (dst := F + 0x55C) (src := F + 0x773) (F := s + BitVec.ofNat 32 288) (N := 97)
    rkr_at_6de rkr_at_6e2 (by decide) (by decide) (by decide) hc3.tps.bms
    (E.mcFF hc3 (c := 0x55C) (d := 0x773) (n := 97) (Or.inl (by decide)) (by decide) (by decide) (by decide)
      (by decide))
    (by rsimp; rw [hsp]; rfl) (by rsimp; rw [ha0, ev0, ev_add, BitVec.add_assoc]; rfl) (by rsimp; try rfl)
    (by rsimp; rw [hsp]; exact (E.sp 288 (by decide)).symm) (E.cS (by decide)) (E.cF (c := 0x55C) (by decide))
    fun m4 hm4 => ?_
  wn
  refine WP.aluImm rkr_at_6e6 ?_; wn
  refine WP.jal rkr_at_6e8 (by decide) ?_; wn
  have hcp : Out m3.mem (copyBytes m3.mem (F + 0x55C) (F + 0x773) 97) (s + BitVec.ofNat 32 1676) 97 := fun x hx => by
    rw [show F + 0x55C = s + BitVec.ofNat 32 1676 from E.Fc 0x55C]; exact copyBytes_sep hx.symm (Nat.le_refl _)
  have hW4 : RkW s Md m4.mem := (hW3.out hcp (Or.inr (Or.inl (by decide)))).out hm4 (Or.inl (by decide))
  refine rk_628 hL0 hLsp hL24 (by keepz hL0) hW4 (by rsimp; rfl) ?_ K
  refine ⟨by rw [List.length_drop, h91]; decide, ?_⟩
  rw [List.length_drop, h91]
  show memBytes m4.mem (F + 0x55C) 97 = _
  rw [hm4.bytes (p := F + 0x55C) (n := 97) (E.fs (c := 0x55C) (n := 97) (d := 288) (k := 16) (Or.inr (by decide)) (by decide) (by decide)).symm,
    rk_mbCopy (by decide), hO3.bytes (p := F + 0x773) (n := 97) (E.fs (c := 0x773) (n := 97) (d := 300) (k := 4) (Or.inr (by decide)) (by decide)
      (by decide)).symm, ← hder, rk_mbDrop h26, h91, BitVec.add_assoc]
  rfl


theorem rkHex_of {pub : Bytes} {pl : Nat} (hpl : pub.length = pl) :
    rkHex pub = match (if pl ≤ 256 then parseHex pub else none) with
      | none => none
      | some k => if k.length = 32 then some (2, k) else none := by
  subst hpl; rfl

/-- The Ed25519 key at 0x5FC: `hex_decode` on the public key text, and its
32 bytes. -/
theorem rk_ed (E : RkEnv M0 M1 s out F P N g0) (hOd : Out M1 Md s 3004) (hW : RkW s Md M)
    (hL0 : gL 0 = 0) (hLsp : gL sp = F) (hL24 : gL 24 = F + 0xA6C) (hk : ∀ x, x ∉ rkDc → g x = gL x)
    {pq : Word} {pl : Nat} {pub : Bytes} (h8 : g 8 = pq) (h9 : g 9 = BitVec.ofNat 32 pl)
    (h22 : (g 22).extractLsb' 0 8 = 0xFF) (hpw : pq.toNat + pl ≤ 0x40000000) (hSp : Sep s 3056 pq pl)
    (hpub : memBytes M pq pl = pub) (K : RkK Q s F gL Md (rkHex pub)) :
    WP tufRoleKeysReadCode TRK Q M 0x5FC g := by
  have hO : Out M1 M s 3004 := hOd.trans hW.outer
  have hc := E.code hO
  have hsp : g sp = F := (hk sp (by decide)).trans hLsp
  have hpl : pub.length = pl := by rw [← hpub, memBytes_length]
  rw [rkHex_of hpl] at K
  refine WP.aluImm rkr_at_5fc ?_; wn
  refine WP.alu rkr_at_600 ?_; wn
  refine WP.alu rkr_at_602 ?_; wn
  refine WP.callHex (text := pq) (out := F + 0x75C) (r := s + BitVec.ofNat 32 272) (len := pl)
    rkr_at_604 rkr_at_608 (by decide) (by decide) hc.hex hc.hv
    (by rsimp; rw [ev0, h8]) (by rsimp; rw [ev0, h9]) (by rsimp; rw [hsp]; rfl) (by omega)
    (by rsimp; rw [hsp, ← E.hF, BitVec.add_assoc]; rfl) (by rsimp; rw [hsp]; exact E.halF)
    (E.lowS (by decide) (by decide) (by decide)) (E.lowS (by decide) (by decide) (by decide))
    (hSp.sub (by decide))
    (E.fs (c := 0x75C) (n := 128) (d := 272) (k := 32) (Or.inr (by decide)) (by decide) (by decide)).symm
    (E.lowF (by decide) (by decide) (by decide)) (E.lowF (by decide) (by decide) (by decide))
    (by rw [show (F + 0x75C : Word) = s + BitVec.ofNat 32 2188 from E.Fc 0x75C]; exact hSp.sub (by decide))
    (E.cS (by decide)) (E.cF (c := 0x75C) (by decide)) fun m2 r0 r1 rb hfr => ?_
  wn
  have hW2 : RkW s Md m2.mem := hW.out2 (c1 := 272) (k1 := 32) (c2 := 2188) (k2 := 128)
    (fun x h1 h2 => hfr x h1 (by rw [show F + 0x75C = F + BitVec.ofNat 32 0x75C from rfl, E.Fc]; exact h2))
    (Or.inl (by decide)) (Or.inr (Or.inl (by decide)))
  have hO2 : Out M1 m2.mem s 3004 := hOd.trans hW2.outer
  have hspec : tufHexDecodeSpec M pq pl = if pl ≤ 256 then parseHex pub else none := by
    unfold tufHexDecodeSpec; rw [hpub]
  rw [hspec] at r0 rb
  rcases hx : (if pl ≤ 256 then parseHex pub else none) with _ | key <;> rw [hx] at r0 rb K
  · replace r0 : reg m2 a0 = 0 := r0
    refine WP.branch rkr_at_60c (fun _ => ?_) (fun eb => ?_)
    · wn
      exact rk_6ea hL0 hLsp hL24 (by keepz hL0) hW2 (by rsimp; exact h22) K
    · exfalso; rsimp at eb; rw [r0] at eb; exact absurd eb (by decide)
  obtain ⟨hkl, hkb⟩ := rb key rfl
  replace r0 : reg m2 a0 = F + 0x75C := r0
  replace K : RkK Q s F gL Md (if key.length = 32 then some (2, key) else none) := K
  refine WP.branch rkr_at_60c (fun eb => ?_) (fun _ => ?_)
  · exfalso; rsimp at eb; rw [r0] at eb; exact E.F75 (beq_iff_eq.mp eb)
  wn
  refine WP.aluImm rkr_at_60e ?_; wn
  have hp2 : pl / 2 < 2 ^ 32 := by omega
  by_cases h32 : pl / 2 = 32
  rotate_left
  · rw [if_neg (by rw [hkl]; exact h32)] at K
    refine WP.branch rkr_at_610 (fun _ => ?_) (fun eb => ?_)
    · wn
      exact rk_6ea hL0 hLsp hL24 (by keepz hL0) hW2 (by rsimp; exact h22) K
    · exfalso; rsimp at eb; rw [r1, ev_add] at eb
      exact rk_addne (c := 32) (by decide) hp2 (by decide) h32 (rk_bneF eb)
  rw [if_pos (by rw [hkl]; exact h32)] at K
  refine WP.branch rkr_at_610 (fun eb => ?_) (fun _ => ?_)
  · exfalso; rsimp at eb; rw [r1, h32] at eb; exact absurd eb (by decide)
  wn
  have hc2 := E.code hO2
  refine WP.alu rkr_at_612 ?_; wn
  refine WP.aluImm rkr_at_614 ?_; wn
  refine WP.aluImm rkr_at_618 ?_; wn
  refine WP.alu rkr_at_61c ?_; wn
  refine WP.callMemcpy (dst := F + 0x55C) (src := F + 0x75C) (F := s + BitVec.ofNat 32 288) (N := 32)
    rkr_at_61e rkr_at_622 (by decide) (by decide) (by decide) hc2.tps.bms
    (E.mcFF hc2 (c := 0x55C) (d := 0x75C) (n := 32) (Or.inl (by decide)) (by decide) (by decide) (by decide)
      (by decide))
    (by rsimp; rw [hsp]; rfl) (by rsimp; simp only [ev0, r0]) (by rsimp; try rfl)
    (by rsimp; rw [hsp]; exact (E.sp 288 (by decide)).symm) (E.cS (by decide)) (E.cF (c := 0x55C) (by decide))
    fun m4 hm4 => ?_
  wn
  refine WP.aluImm rkr_at_626 ?_; wn
  have hcp : Out m2.mem (copyBytes m2.mem (F + 0x55C) (F + 0x75C) 32) (s + BitVec.ofNat 32 1676) 32 :=
    fun x hx => by
      rw [show F + 0x55C = s + BitVec.ofNat 32 1676 from E.Fc 0x55C]; exact copyBytes_sep hx.symm (Nat.le_refl _)
  have hW4 : RkW s Md m4.mem := (hW2.out hcp (Or.inr (Or.inl (by decide)))).out hm4 (Or.inl (by decide))
  refine rk_628 hL0 hLsp hL24 (by keepz hL0) hW4 (by rsimp; rfl) ?_ K
  refine ⟨by rw [hkl, h32]; decide, ?_⟩
  rw [hkl, h32]
  show memBytes m4.mem (F + 0x55C) 32 = _
  rw [hm4.bytes (p := F + 0x55C) (n := 32) (E.fs (c := 0x55C) (n := 32) (d := 288) (k := 16) (Or.inr (by decide))
      (by decide) (by decide)).symm, rk_mbCopy (by decide), ← hkb, h32]
end

end C3.RV32
