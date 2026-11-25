import C3BootProofs.Proofs.TufRoleKeysMetSig

/-!
# `RoleKeys::met`: the signature checks

From 0x22A, `met` checks the decoded signature at `F + 0x48` against the key
in the slot by the slot's tag. Each check ends at 0x314 with `a0` nonzero
only when the signature verifies, or skips the key at 0x2C0.
-/

namespace C3.RV32

open C3.Image C3.Json C3.RV32.P2v C3.RV32.Pv C3.RV32.Sv C3.RV32.P3

set_option maxRecDepth 20000

/-- The registers that the signature checks keep: `sp`, 0x62 in `s2`, the
`RoleKeys` in `s3`, the count in `s4`, `i` and `i + 1` in `s6` and `s7`, the
tag in `s8`, `s9`, and `s10`. -/
abbrev rmSL : List (Fin 32) := [sp, 18, 19, 20, 22, 23, 24, 25, 26]

section
variable {M0 M1 Mz : Word → BitVec 8} {s F R MP SP : Word} {ML SL : Nat} {g0 : Fin 32 → Word}
  {S : Prop} {H : Post}

theorem rm_n64 : ∀ n, n < 129 → branchTaken .bne (aluEval .add (BitVec.ofNat 32 n) 0xFFFFFFC0) 0 = false →
    n = 64 := by decide

/-- From 0x298, the Ed25519 check: a signature of 64 bytes, verified with
`ed25519Verify` against the 32-byte key at `pk`. -/
theorem rm_ed (E : RmEnv M0 M1 s F R MP SP ML SL g0) {G g : Fin 32 → Word} (hK : ∀ x, x ∈ rmSL → g x = G x)
    (hsp : g sp = F) (hz : g 0 = 0) (hfr : ∀ x, x ∉ rkE → g x = g0 x) {pk : Word} (h8 : g 8 = pk)
    (hpk : Sep s 0x3920 pk 32) (hpkw : pk.toNat + 32 < 2 ^ 32) {n : Nat} (hn : n ≤ 128)
    (h12 : g 12 = BitVec.ofNat 32 n) (h13 : g 13 = F + BitVec.ofNat 32 0x48)
    {Mk : Word → BitVec 8} (hM : RmVM M1 Mz Mk s F) (hmp : memLoad32 Mz (F + BitVec.ofNat 32 0x14) = MP)
    (hml : memLoad32 Mz (F + BitVec.ofNat 32 0x10) = BitVec.ofNat 32 ML)
    (hskip : ∀ Mk' g', RmVM M1 Mz Mk' s F → (∀ x, x ∈ rmSL → g' x = G x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk' 0x2C0 g')
    (hdone : ∀ Mk' g', RmVM M1 Mz Mk' s F → (∀ x, x ∈ rmSL → g' x = G x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → (g' 10 ≠ 0 → n = 64 ∧
        ed25519Verify (memBytes M0 pk 32) (memBytes M0 MP ML) (memBytes Mk (F + BitVec.ofNat 32 0x48) 64) = true) →
      WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk' 0x314 g') :
    WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x298 g := by
  have hF48 : F + BitVec.ofNat 32 0x48 = s + BitVec.ofNat 32 0x3778 := E.Fc 0x48
  have hlo := E.hlo
  have hhi := E.hhi
  refine WP.aluImm rkm_at_298 ?_; wn
  refine WP.branch rkm_at_29c (fun eb => ?_) (fun eb => ?_) <;> wn
  · exact hskip Mk _ hM (by rmkeep hK) (by rsimp; (try exact hz)) (by keepz E.hz0)
  have h64 : n = 64 := rm_n64 n (by omega) (by (try rsimp at eb); rw [h12] at eb; exact eb)
  subst h64
  have C := E.code hM.1
  have hmp' : memLoad32 Mk (F + BitVec.ofNat 32 0x14) = MP := (hM.2.load (c := 8) (by decide)).trans hmp
  have hml' : memLoad32 Mk (F + BitVec.ofNat 32 0x10) = BitVec.ofNat 32 ML :=
    (hM.2.load (c := 4) (by decide)).trans hml
  have hFn : (F + BitVec.ofNat 32 0x48).toNat = s.toNat + 0x3730 + 0x48 := E.FN (by decide)
  refine WP.alu rkm_at_29e ?_; wn
  refine WP.lw rkm_at_2a0 (by (try rsimp); rw [hsp]; exact E.alF (c := 0x14) (by decide)) ?_; wn
  refine WP.lw rkm_at_2a2 (by (try rsimp); rw [hsp]; exact E.alF (c := 0x10) (by decide)) ?_; wn
  refine WP.callEdM (F := s + BitVec.ofNat 32 0x2090) (pk := pk) (sig := F + BitVec.ofNat 32 0x48) (msg := MP)
    (len := ML) rkm_at_2a4 rkm_at_2a8 (by decide) (by decide)
    (E.ev C (hpk.sub (c := 0x1680) (l := 0x20B0) (by decide)).symm (by rw [hF48]; exact E.ss (Or.inr (by decide)) (by decide) (by decide))
      (E.hSM.sub (c := 0x1680) (l := 0x20B0) (by decide)).symm hpkw (by omega) E.hMw E.hML) C.edI C.edK
    (by (try rsimp); rw [hsp]; exact E.evF) (by (try rsimp); rw [ev0, h8])
    (by (try rsimp); rw [hsp]; exact hmp') (by (try rsimp); rw [hsp]; exact hml') (by (try rsimp); exact h13)
    (by rw [E.evG]; exact E.lowS (by decide) (by decide) (by decide)) fun m2 hv hO => ?_
  have hM2 : RmVM M1 Mz m2.mem s F := RmVM.one E.toRmBase hM (by rw [← E.evG]; exact hO) (by decide)
  refine WP.jal rkm_at_2ac (by decide) ?_; wn
  refine hdone m2.mem _ hM2 (by rmkeep hK) (by rsimp; (try exact hz)) (by keepz E.hz0) fun ha => ⟨rfl, ?_⟩
  have hv' := hv (by (try rsimp at ha); exact ha)
  rwa [E.bytes hM.1 hpk, E.bytes hM.1 E.hSM] at hv'

/-- `der::scalar::<N>`'s value has `N` bytes. -/
theorem rmv_scalar {N : Nat} {L : Bytes} {rp : Word} {r : Except DerError DerTlv} {bs : Bytes}
    (hL : ∀ b ∈ L, b < 256) (h : derScalarOf N L rp r = .ok bs) : bs.length = N ∧ ∀ b ∈ bs, b < 256 := by
  unfold derScalarOf at h
  split at h
  next t _ _ =>
    generalize hc : (if (t.content L).head? = some 0 then (t.content L).drop 1 else t.content L) = c at h
    have hm : ∀ b ∈ c, b ∈ L := by
      intro b hb
      subst hc
      split at hb
      · exact List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_drop hb))
      · exact List.mem_of_mem_drop (List.mem_of_mem_take hb)
    by_cases hn : N < c.length
    · rw [ite_eq_left hn] at h; cases h
    · rw [ite_eq_right hn] at h
      cases h
      have hle := Nat.le_of_not_lt hn
      refine ⟨?_, fun b hb => ?_⟩
      · rw [List.length_append, List.length_replicate]; omega
      · rcases List.mem_append.mp hb with h1 | h1
        · rw [List.eq_of_mem_replicate h1]; decide
        · exact hL b (hm b h1)
  next => cases h
  next => cases h

/-- `der::ecdsa_signature::<N>`'s `r` and `s` have `N` bytes each. -/
theorem rmv_sig {N : Nat} {M : Word → BitVec 8} {p : Word} {n : Nat} {r s : Bytes}
    (h : ecdsaSigOf N M p n = .ok (r, s)) :
    (r.length = N ∧ ∀ b ∈ r, b < 256) ∧ (s.length = N ∧ ∀ b ∈ s, b < 256) := by
  unfold ecdsaSigOf at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · next r' hr =>
        split at h
        · cases h
        · next s' hs =>
          split at h
          · cases h
            exact ⟨rmv_scalar memBytes_mem_lt hr, rmv_scalar memBytes_mem_lt hs⟩
          · cases h
    · cases h

theorem rmv_mb {M : Word → BitVec 8} {a : Word} {r : Bytes} {N : Nat} (hl : r.length = N) (hb : ∀ b ∈ r, b < 256)
    (h : ∀ j, j < N → M (a + BitVec.ofNat 32 j) = BitVec.ofNat 8 (r.getD j 0)) : memBytes M a N = r := by
  apply List.ext_getElem (by rw [memBytes_length, hl])
  intro i h1 h2
  have e := memBytes_getD (M := M) (p := a) (n := N) (i := i) (by rw [← hl]; exact h2)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at e
  rw [e, h i (by rw [← hl]; exact h2), BitVec.toNat_ofNat,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
  exact Nat.mod_eq_of_lt (hb _ (List.getElem_mem h2))

/-- `memcpy` within the frame keeps `RmVM`. -/
theorem RmVM.cp (E : RmBase M0 M1 s F R MP SP ML SL g0) {Ma Mb : Word → BitVec 8} (h : RmVM M1 Mz Ma s F)
    {c N : Nat} {src : Word} (hO : Out (copyBytes Ma (F + BitVec.ofNat 32 c) src N) Mb (s + BitVec.ofNat 32 0x3720) 16)
    (hok : RmOk (0x3730 + c) N) : RmVM M1 Mz Mb s F :=
  RmVM.two E h (d1 := 0x3720) (l1 := 16) (d2 := 0x3730 + c) (l2 := N)
    (fun x h1 h2 => (hO x h1).trans (copyBytes_sep (by rw [E.Fc]; exact h2.symm) (Nat.le_refl _))) (by decide) hok

/-- What `memcpy` within the frame copies. -/
theorem rmv_cp (E : RmBase M0 M1 s F R MP SP ML SL g0) {Ma Mb : Word → BitVec 8} {c d N : Nat}
    (hO : Out (copyBytes Ma (F + BitVec.ofNat 32 c) (F + BitVec.ofNat 32 d) N) Mb (s + BitVec.ofNat 32 0x3720) 16)
    (hc : c + N ≤ 0x1F0) : memBytes Mb (F + BitVec.ofNat 32 c) N = memBytes Ma (F + BitVec.ofNat 32 d) N :=
  memBytes_ext fun i hi => by
    have hx : Sep (F + BitVec.ofNat 32 c + BitVec.ofNat 32 i) 1 (s + BitVec.ofNat 32 0x3720) 16 := by
      rw [add_ofNat_assoc]; exact E.fs (Or.inr (by omega)) (by omega) (by decide)
    rw [hO _ hx]; exact copyBytes_at hi (by omega)

/-- Bytes of the frame that a change in two ranges misses. -/
theorem rmv_kb (E : RmBase M0 M1 s F R MP SP ML SL g0) {Ma Mb : Word → BitVec 8} {c n d1 l1 d2 l2 : Nat}
    (hO : ∀ x, Sep x 1 (s + BitVec.ofNat 32 d1) l1 → Sep x 1 (s + BitVec.ofNat 32 d2) l2 → Mb x = Ma x)
    (h1 : 0x3730 + c + n ≤ d1 ∨ d1 + l1 ≤ 0x3730 + c) (h2 : 0x3730 + c + n ≤ d2 ∨ d2 + l2 ≤ 0x3730 + c)
    (hc : c + n ≤ 0x1F0) (hd1 : d1 + l1 ≤ 0x3920) (hd2 : d2 + l2 ≤ 0x3920) :
    memBytes Mb (F + BitVec.ofNat 32 c) n = memBytes Ma (F + BitVec.ofNat 32 c) n :=
  memBytes_eq_of fun j hj => by
    rw [add_ofNat_assoc]
    exact hO _ (E.fs (c := c + j) (n := 1) (by omega) (by omega) hd1) (E.fs (c := c + j) (n := 1) (by omega) (by omega) hd2)

theorem rmv_hfG (s : Word) : hfG (s + BitVec.ofNat 32 0x34F0) = s + BitVec.ofNat 32 0x30D0 := by
  show s + BitVec.ofNat 32 0x34F0 + 0xFFFFFBE0 = _
  rw [BitVec.add_assoc]; rfl

/-- From 0x23E, the P-384 check: the DER signature decoded by
`ecdsa_signature::<48>`, the message hashed with SHA-384, and both
verified with `p384_verify_prehash` against the 97-byte key at `pk`. -/
theorem rm_p384 (E : RmEnv M0 M1 s F R MP SP ML SL g0) (hH : ∀ m, Halting m → rmQ H M0 s g0 S m.pc m.mem (reg m))
    {G g : Fin 32 → Word} (hK : ∀ x, x ∈ rmSL → g x = G x)
    (hsp : g sp = F) (hz : g 0 = 0) (hfr : ∀ x, x ∉ rkE → g x = g0 x) {pk : Word} (h8 : g 8 = pk)
    (hpk : Sep s 0x3920 pk 0x61) (hpkw : pk.toNat + 0x61 ≤ 0x40000000) {n : Nat} (hn : n ≤ 128)
    (h12 : g 12 = BitVec.ofNat 32 n) (h13 : g 13 = F + BitVec.ofNat 32 0x48)
    {Mk : Word → BitVec 8} (hM : RmVM M1 Mz Mk s F) (hmp : memLoad32 Mz (F + BitVec.ofNat 32 0x14) = MP)
    (hml : memLoad32 Mz (F + BitVec.ofNat 32 0x10) = BitVec.ofNat 32 ML)
    (hskip : ∀ Mk' g', RmVM M1 Mz Mk' s F → (∀ x, x ∈ rmSL → g' x = G x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk' 0x2C0 g')
    (hdone : ∀ Mk' g', RmVM M1 Mz Mk' s F → (∀ x, x ∈ rmSL → g' x = G x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → (g' 10 ≠ 0 → ∃ r s', ecdsaSigOf 48 Mk (F + BitVec.ofNat 32 0x48) n = .ok (r, s') ∧
        p384Verify (memBytes M0 pk 0x61) (sha384 (memBytes M0 MP ML)) r s' = true) →
      WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk' 0x314 g') :
    WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x23E g := by
  have hF48 : F + BitVec.ofNat 32 0x48 = s + BitVec.ofNat 32 0x3778 := E.Fc 0x48
  have hFC8 : F + BitVec.ofNat 32 0xC8 = s + BitVec.ofNat 32 0x37F8 := E.Fc 0xC8
  have hF12C : F + BitVec.ofNat 32 0x12C = s + BitVec.ofNat 32 0x385C := E.Fc 0x12C
  have hF15C : F + BitVec.ofNat 32 0x15C = s + BitVec.ofNat 32 0x388C := E.Fc 0x15C
  have hF18C : F + BitVec.ofNat 32 0x18C = s + BitVec.ofNat 32 0x38BC := E.Fc 0x18C
  have hw : F + 0xFFFFFE90 = s + BitVec.ofNat 32 0x35C0 := E.Fm (c := 0x170) (by decide) rfl
  have hFn : (F + BitVec.ofNat 32 0x48).toNat = s.toNat + 0x3730 + 0x48 := E.FN (by decide)
  have hlo := E.hlo
  have hhi := E.hhi
  have C := E.code hM.1
  refine WP.aluImm rkm_at_23e ?_; wn
  refine WP.alu rkm_at_240 ?_; wn
  refine WP.callEs48 (sp0 := F) (out := F + BitVec.ofNat 32 0xC8) (p := F + BitVec.ofNat 32 0x48) (n := n)
    rkm_at_242 rkm_at_246 (by decide) (by decide)
    (E.es48 C.es48 (by have := E.wF (c := 0xC8) (k := 97) (by decide); omega) (by omega) (by omega)
      (by rw [hFC8]; exact E.ss (Or.inr (by decide)) (by decide) (by decide))
      (by rw [hF48]; exact E.ss (Or.inr (by decide)) (by omega) (by decide)))
    (by (try rsimp); exact hsp) (by (try rsimp); rw [ev_add, hsp]; rfl) (by (try rsimp); rw [ev0, h13])
    (by (try rsimp); exact h12) (by rw [hw]; exact E.lowS (by decide) (by decide) (by decide)) (E.cF (by decide))
    fun m2 hso hk2 => ?_
  have hM2 : RmVM M1 Mz m2.mem s F := RmVM.two E.toRmBase hM (d1 := 0x35C0) (l1 := 0x170) (d2 := 0x37F8) (l2 := 97)
    (by rw [← hw, ← hFC8]; exact hk2) (by decide) (by decide)
  clear hk2
  generalize m2.mem = M2 at hM2 hso
  refine WP.lbu rkm_at_24a ?_; wn
  unfold tmcSigOut at hso
  split at hso
  rotate_left
  · refine WP.branch rkm_at_24e (fun _ => ?_) (fun eb => ?_) <;> wn
    · exact hskip M2 _ hM2 (by rmkeep hK) (by rsimp; (try exact hz)) (by keepz E.hz0)
    · exfalso; (try rsimp at eb); rw [hsp] at eb
      rw [show F + 200 = F + BitVec.ofNat 32 0xC8 from rfl, hso.1] at eb
      exact absurd eb (by decide)
  next r s' hes =>
  obtain ⟨⟨hrl, hrb⟩, ⟨hsl, hsb⟩⟩ := rmv_sig hes
  have hr2 : memBytes M2 (F + BitVec.ofNat 32 0xC9) 48 = r := rmv_mb hrl hrb fun j hj => by
    rw [add_ofNat_assoc, show 0xC9 + j = 0xC8 + (1 + j) by omega, ← add_ofNat_assoc]; exact hso.2.1 j hj
  have hs2 : memBytes M2 (F + BitVec.ofNat 32 0xF9) 48 = s' := rmv_mb hsl hsb fun j hj => by
    rw [add_ofNat_assoc, show 0xF9 + j = 0xC8 + (48 + 1 + j) by omega, ← add_ofNat_assoc]; exact hso.2.2 j hj
  clear hso
  refine WP.branch rkm_at_24e (fun _ => ?_) (fun _ => ?_) <;> wn
  · exact hskip M2 _ hM2 (by rmkeep hK) (by rsimp; (try exact hz)) (by keepz E.hz0)
  have hc2 := E.codeA hM2.1
  refine WP.aluImm rkm_at_250 ?_; wn
  refine WP.aluImm rkm_at_252 ?_; wn
  refine WP.aluImm rkm_at_256 ?_; wn
  refine WP.callMemcpy (dst := F + BitVec.ofNat 32 0x12C) (src := F + BitVec.ofNat 32 0xC9)
    (F := s + BitVec.ofNat 32 0x3720) (N := 48) rkm_at_25a rkm_at_25e (by decide) (by decide) (by decide)
    hc2.rk.tps.bms (E.mcFF hc2 (c := 0x12C) (d := 0xC9) (n := 48) (Or.inr (by decide)) (by decide) (by decide))
    (by (try rsimp); rw [ev_add, hsp]; rfl) (by (try rsimp); rw [ev_add, hsp]; rfl)
    (by (try rsimp); (try simp only [ev0]); try rfl)
    (by (try rsimp); rw [hsp]; exact (E.sp 0x3720 (by decide)).symm) (E.lowS (by decide) (by decide) (by decide))
    (E.cF (by decide)) fun m3 hO3 => ?_
  have hM3 : RmVM M1 Mz m3.mem s F := RmVM.cp E.toRmBase hM2 hO3 (by decide)
  have hr3 : memBytes m3.mem (F + BitVec.ofNat 32 0x12C) 48 = r := (rmv_cp E.toRmBase hO3 (by decide)).trans hr2
  have hs3 : memBytes m3.mem (F + BitVec.ofNat 32 0xF9) 48 = s' := by
    rw [← hs2]
    exact memBytes_eq_of fun j hj => by
      rw [add_ofNat_assoc]
      refine (hO3 _ (E.fs (c := 0xF9 + j) (n := 1) (Or.inr (by omega)) (by omega) (by decide))).trans ?_
      exact copyBytes_sep (rm_ff F (Or.inr (by omega)) (by decide) (by omega)) (Nat.le_refl _)
  clear hO3 hr2 hs2
  generalize m3.mem = M3 at hM3 hr3 hs3
  have hc3 := E.codeA hM3.1
  refine WP.aluImm rkm_at_262 ?_; wn
  refine WP.aluImm rkm_at_264 ?_; wn
  refine WP.aluImm rkm_at_268 ?_; wn
  refine WP.callMemcpy (dst := F + BitVec.ofNat 32 0x15C) (src := F + BitVec.ofNat 32 0xF9)
    (F := s + BitVec.ofNat 32 0x3720) (N := 48) rkm_at_26c rkm_at_270 (by decide) (by decide) (by decide)
    hc3.rk.tps.bms (E.mcFF hc3 (c := 0x15C) (d := 0xF9) (n := 48) (Or.inr (by decide)) (by decide) (by decide))
    (by (try rsimp); rw [ev_add, hsp]; rfl) (by (try rsimp); rw [ev_add, hsp]; rfl)
    (by (try rsimp); (try simp only [ev0]); try rfl)
    (by (try rsimp); rw [hsp]; exact (E.sp 0x3720 (by decide)).symm) (E.lowS (by decide) (by decide) (by decide))
    (E.cF (by decide)) fun m4 hO4 => ?_
  have hM4 : RmVM M1 Mz m4.mem s F := RmVM.cp E.toRmBase hM3 hO4 (by decide)
  have hs4 : memBytes m4.mem (F + BitVec.ofNat 32 0x15C) 48 = s' := (rmv_cp E.toRmBase hO4 (by decide)).trans hs3
  have hr4 : memBytes m4.mem (F + BitVec.ofNat 32 0x12C) 48 = r := by
    rw [← hr3]
    refine rmv_kb E.toRmBase (d1 := 0x3720) (l1 := 16) (d2 := 0x388C) (l2 := 48) (fun x h1 h2 => ?_)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    exact (hO4 x h1).trans (copyBytes_sep (by rw [hF15C]; exact h2.symm) (Nat.le_refl _))
  clear hO4 hr3 hs3
  generalize m4.mem = M4 at hM4 hr4 hs4
  have C4 := E.code hM4.1
  have hmp4 : memLoad32 M4 (F + BitVec.ofNat 32 0x14) = MP := (hM4.2.load (c := 8) (by decide)).trans hmp
  have hml4 : memLoad32 M4 (F + BitVec.ofNat 32 0x10) = BitVec.ofNat 32 ML :=
    (hM4.2.load (c := 4) (by decide)).trans hml
  refine WP.aluImm rkm_at_274 ?_; wn
  refine WP.lw rkm_at_276 (by (try rsimp); rw [hsp]; exact E.alF (c := 0x14) (by decide)) ?_; wn
  refine WP.lw rkm_at_278 (by (try rsimp); rw [hsp]; exact E.alF (c := 0x10) (by decide)) ?_; wn
  refine WP.callSha384M (F := s + BitVec.ofNat 32 0x34F0) (out := F + BitVec.ofNat 32 0x18C) (p := MP) (len := ML)
    rkm_at_27a rkm_at_27e (by decide) (by decide)
    (E.hf C4.hf (E.hSM.sub (c := 0x30D0) (l := 0x660) (by decide)).symm
      (by rw [hF18C]; exact E.ss (Or.inr (by decide)) (by decide) (by decide)) E.hMw
      (by have := E.wF (c := 0x18C) (k := 48) (by decide); omega))
    (by (try rsimp); rw [hsp]; exact E.hfF) (by (try rsimp); rw [ev_add, hsp]; rfl)
    (by (try rsimp); rw [hsp]; exact hmp4) (by (try rsimp); rw [hsp]; exact hml4)
    (by rw [rmv_hfG]; exact E.lowS (by decide) (by decide) (by decide)) (E.cF (by decide)) fun m5 hh hk5 => ?_
  rw [rmv_hfG] at hk5
  have hM5 : RmVM M1 Mz m5.mem s F := RmVM.two E.toRmBase hM4 (d1 := 0x30D0) (l1 := 0x660) (d2 := 0x38BC) (l2 := 48)
    (by rw [← hF18C]; exact hk5) (by decide) (by decide)
  have hr5 : memBytes m5.mem (F + BitVec.ofNat 32 0x12C) 48 = r := by
    rw [← hr4]
    exact rmv_kb E.toRmBase (d1 := 0x30D0) (l1 := 0x660) (d2 := 0x38BC) (l2 := 48)
      (by rw [← hF18C]; exact hk5) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs5 : memBytes m5.mem (F + BitVec.ofNat 32 0x15C) 48 = s' := by
    rw [← hs4]
    exact rmv_kb E.toRmBase (d1 := 0x30D0) (l1 := 0x660) (d2 := 0x38BC) (l2 := 48)
      (by rw [← hF18C]; exact hk5) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [E.bytes hM4.1 E.hSM] at hh
  clear hk5 hr4 hs4
  generalize m5.mem = M5 at hM5 hr5 hs5 hh
  have C5 := E.code hM5.1
  refine WP.aluImm rkm_at_282 ?_; wn
  refine WP.aluImm rkm_at_284 ?_; wn
  refine WP.aluImm rkm_at_288 ?_; wn
  refine WP.aluImm rkm_at_28a ?_; wn
  refine WP.alu rkm_at_28c ?_; wn
  refine WP.callPvM (B := s + BitVec.ofNat 32 0x1590) (pk := pk) (ph := F + BitVec.ofNat 32 0x18C)
    (rp := F + BitVec.ofNat 32 0x12C) (sq := F + BitVec.ofNat 32 0x15C) rkm_at_28e rkm_at_292 (by decide) (by decide)
    (fun m _ => hH m) C5.pv E.pvfr (by (try rsimp); rw [hsp]; exact E.pvF) (by (try rsimp); rw [ev0, h8])
    (by (try rsimp); rw [ev_add, hsp]; rfl) (by (try rsimp); (try simp only [ev0]); try rfl)
    (by (try rsimp); rw [ev_add, hsp]; rfl) (by (try rsimp); rw [ev_add, hsp]; rfl)
    (by rw [E.pvlo]; exact (hpk.sub (c := 0x13F0) (l := 0x2340) (by decide)).symm) hpkw
    (by rw [E.pvlo, hF12C]; exact E.ss (Or.inr (by decide)) (by decide) (by decide))
    (by rw [E.pvlo, hF15C]; exact E.ss (Or.inr (by decide)) (by decide) (by decide))
    (by rw [E.pvlo, hF18C]; exact E.ss (Or.inr (by decide)) (by decide) (by decide))
    (by have := E.wF (c := 0x18C) (k := 48) (by decide); omega)
    (by rw [E.pvlo]; exact E.lowS (by decide) (by decide) (by decide)) fun m6 hv hO6 => ?_
  have hM6 : RmVM M1 Mz m6.mem s F := RmVM.one E.toRmBase hM5 (by rw [← E.pvlo]; exact hO6) (by decide)
  refine WP.jal rkm_at_296 (by decide) ?_; wn
  refine hdone m6.mem _ hM6 (by rmkeep hK) (by rsimp; (try exact hz)) (by keepz E.hz0) fun ha => ⟨r, s', hes, ?_⟩
  have hv' := hv (by (try rsimp at ha); exact ha)
  rwa [E.bytes hM5.1 hpk, hh, hr5, hs5] at hv'

/-- From 0x2AE, the P-256 check: the DER signature decoded by
`ecdsa_signature::<32>`, the message hashed with SHA-256, and both
verified with `p256_verify_prehash` against the 65-byte key at `pk`. -/
theorem rm_p256 (E : RmEnv M0 M1 s F R MP SP ML SL g0) (hH : ∀ m, Halting m → rmQ H M0 s g0 S m.pc m.mem (reg m))
    {G g : Fin 32 → Word} (hK : ∀ x, x ∈ rmSL → g x = G x)
    (hsp : g sp = F) (hz : g 0 = 0) (hfr : ∀ x, x ∉ rkE → g x = g0 x) {pk : Word} (h8 : g 8 = pk)
    (hpk : Sep s 0x3920 pk 0x41) (hpk0 : 0 < pk.toNat) (hpkw : pk.toNat + 0x41 ≤ 0x40000000) {n : Nat}
    (hn : n ≤ 128) (h12 : g 12 = BitVec.ofNat 32 n) (h13 : g 13 = F + BitVec.ofNat 32 0x48)
    {Mk : Word → BitVec 8} (hM : RmVM M1 Mz Mk s F) (hmp : memLoad32 Mz (F + BitVec.ofNat 32 0x14) = MP)
    (hml : memLoad32 Mz (F + BitVec.ofNat 32 0x10) = BitVec.ofNat 32 ML)
    (hskip : ∀ Mk' g', RmVM M1 Mz Mk' s F → (∀ x, x ∈ rmSL → g' x = G x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk' 0x2C0 g')
    (hdone : ∀ Mk' g', RmVM M1 Mz Mk' s F → (∀ x, x ∈ rmSL → g' x = G x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → (g' 10 ≠ 0 → ∃ r s', ecdsaSigOf 32 Mk (F + BitVec.ofNat 32 0x48) n = .ok (r, s') ∧
        p256Verify (memBytes M0 pk 65) (sha256 (memBytes M0 MP ML)) r s' = true) →
      WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk' 0x314 g') :
    WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x2AE g := by
  have hF48 : F + BitVec.ofNat 32 0x48 = s + BitVec.ofNat 32 0x3778 := E.Fc 0x48
  have hFC8 : F + BitVec.ofNat 32 0xC8 = s + BitVec.ofNat 32 0x37F8 := E.Fc 0xC8
  have hF12C : F + BitVec.ofNat 32 0x12C = s + BitVec.ofNat 32 0x385C := E.Fc 0x12C
  have hF15C : F + BitVec.ofNat 32 0x15C = s + BitVec.ofNat 32 0x388C := E.Fc 0x15C
  have hF18C : F + BitVec.ofNat 32 0x18C = s + BitVec.ofNat 32 0x38BC := E.Fc 0x18C
  have hw : F + 0xFFFFFED0 = s + BitVec.ofNat 32 0x3600 := E.Fm (c := 0x130) (by decide) rfl
  have hw2 : F + 0xFFFFFD90 = s + BitVec.ofNat 32 0x34C0 := E.Fm (c := 0x270) (by decide) rfl
  have hFn : (F + BitVec.ofNat 32 0x48).toNat = s.toNat + 0x3730 + 0x48 := E.FN (by decide)
  have hlo := E.hlo
  have hhi := E.hhi
  have C := E.code hM.1
  refine WP.aluImm rkm_at_2ae ?_; wn
  refine WP.alu rkm_at_2b0 ?_; wn
  refine WP.callEs32 (sp0 := F) (out := F + BitVec.ofNat 32 0xC8) (p := F + BitVec.ofNat 32 0x48) (n := n)
    rkm_at_2b2 rkm_at_2b6 (by decide) (by decide)
    (E.es32 C.es32 (by have := E.wF (c := 0xC8) (k := 65) (by decide); omega) (by omega) (by omega)
      (by rw [hFC8]; exact E.ss (Or.inr (by decide)) (by decide) (by decide))
      (by rw [hF48]; exact E.ss (Or.inr (by decide)) (by omega) (by decide)))
    (by (try rsimp); exact hsp) (by (try rsimp); rw [ev_add, hsp]; rfl) (by (try rsimp); rw [ev0, h13])
    (by (try rsimp); exact h12) (by rw [hw]; exact E.lowS (by decide) (by decide) (by decide)) (E.cF (by decide))
    fun m2 hso hk2 => ?_
  have hM2 : RmVM M1 Mz m2.mem s F := RmVM.two E.toRmBase hM (d1 := 0x3600) (l1 := 0x130) (d2 := 0x37F8) (l2 := 65)
    (by rw [← hw, ← hFC8]; exact hk2) (by decide) (by decide)
  clear hk2
  generalize m2.mem = M2 at hM2 hso
  refine WP.lbu rkm_at_2ba ?_; wn
  unfold tmcSigOut at hso
  split at hso
  rotate_left
  · refine WP.branch rkm_at_2be (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [hsp] at eb
      rw [show F + 200 = F + BitVec.ofNat 32 0xC8 from rfl, hso.1] at eb
      exact absurd eb (by decide)
    · exact hskip M2 _ hM2 (by rmkeep hK) (by rsimp; (try exact hz)) (by keepz E.hz0)
  next r s' hes =>
  obtain ⟨⟨hrl, hrb⟩, ⟨hsl, hsb⟩⟩ := rmv_sig hes
  have hr2 : memBytes M2 (F + BitVec.ofNat 32 0xC9) 32 = r := rmv_mb hrl hrb fun j hj => by
    rw [add_ofNat_assoc, show 0xC9 + j = 0xC8 + (1 + j) by omega, ← add_ofNat_assoc]; exact hso.2.1 j hj
  have hs2 : memBytes M2 (F + BitVec.ofNat 32 0xE9) 32 = s' := rmv_mb hsl hsb fun j hj => by
    rw [add_ofNat_assoc, show 0xE9 + j = 0xC8 + (32 + 1 + j) by omega, ← add_ofNat_assoc]; exact hso.2.2 j hj
  clear hso
  refine WP.branch rkm_at_2be (fun _ => ?_) (fun _ => ?_) <;> wn
  rotate_left
  · exact hskip M2 _ hM2 (by rmkeep hK) (by rsimp; (try exact hz)) (by keepz E.hz0)
  have hc2 := E.codeA hM2.1
  refine WP.aluImm rkm_at_2d2 ?_; wn
  refine WP.aluImm rkm_at_2d4 ?_; wn
  refine WP.aluImm rkm_at_2d8 ?_; wn
  refine WP.callMemcpy (dst := F + BitVec.ofNat 32 0x12C) (src := F + BitVec.ofNat 32 0xC9)
    (F := s + BitVec.ofNat 32 0x3720) (N := 32) rkm_at_2dc rkm_at_2e0 (by decide) (by decide) (by decide)
    hc2.rk.tps.bms (E.mcFF hc2 (c := 0x12C) (d := 0xC9) (n := 32) (Or.inr (by decide)) (by decide) (by decide))
    (by (try rsimp); rw [ev_add, hsp]; rfl) (by (try rsimp); rw [ev_add, hsp]; rfl)
    (by (try rsimp); (try simp only [ev0]); try rfl)
    (by (try rsimp); rw [hsp]; exact (E.sp 0x3720 (by decide)).symm) (E.lowS (by decide) (by decide) (by decide))
    (E.cF (by decide)) fun m3 hO3 => ?_
  have hM3 : RmVM M1 Mz m3.mem s F := RmVM.cp E.toRmBase hM2 hO3 (by decide)
  have hr3 : memBytes m3.mem (F + BitVec.ofNat 32 0x12C) 32 = r := (rmv_cp E.toRmBase hO3 (by decide)).trans hr2
  have hs3 : memBytes m3.mem (F + BitVec.ofNat 32 0xE9) 32 = s' := by
    rw [← hs2]
    exact memBytes_eq_of fun j hj => by
      rw [add_ofNat_assoc]
      refine (hO3 _ (E.fs (c := 0xE9 + j) (n := 1) (Or.inr (by omega)) (by omega) (by decide))).trans ?_
      exact copyBytes_sep (rm_ff F (Or.inr (by omega)) (by decide) (by omega)) (Nat.le_refl _)
  clear hO3 hr2 hs2
  generalize m3.mem = M3 at hM3 hr3 hs3
  have hc3 := E.codeA hM3.1
  refine WP.aluImm rkm_at_2e4 ?_; wn
  refine WP.aluImm rkm_at_2e6 ?_; wn
  refine WP.aluImm rkm_at_2ea ?_; wn
  refine WP.callMemcpy (dst := F + BitVec.ofNat 32 0x15C) (src := F + BitVec.ofNat 32 0xE9)
    (F := s + BitVec.ofNat 32 0x3720) (N := 32) rkm_at_2ee rkm_at_2f2 (by decide) (by decide) (by decide)
    hc3.rk.tps.bms (E.mcFF hc3 (c := 0x15C) (d := 0xE9) (n := 32) (Or.inr (by decide)) (by decide) (by decide))
    (by (try rsimp); rw [ev_add, hsp]; rfl) (by (try rsimp); rw [ev_add, hsp]; rfl)
    (by (try rsimp); (try simp only [ev0]); try rfl)
    (by (try rsimp); rw [hsp]; exact (E.sp 0x3720 (by decide)).symm) (E.lowS (by decide) (by decide) (by decide))
    (E.cF (by decide)) fun m4 hO4 => ?_
  have hM4 : RmVM M1 Mz m4.mem s F := RmVM.cp E.toRmBase hM3 hO4 (by decide)
  have hs4 : memBytes m4.mem (F + BitVec.ofNat 32 0x15C) 32 = s' := (rmv_cp E.toRmBase hO4 (by decide)).trans hs3
  have hr4 : memBytes m4.mem (F + BitVec.ofNat 32 0x12C) 32 = r := by
    rw [← hr3]
    refine rmv_kb E.toRmBase (d1 := 0x3720) (l1 := 16) (d2 := 0x388C) (l2 := 32) (fun x h1 h2 => ?_)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    exact (hO4 x h1).trans (copyBytes_sep (by rw [hF15C]; exact h2.symm) (Nat.le_refl _))
  clear hO4 hr3 hs3
  generalize m4.mem = M4 at hM4 hr4 hs4
  have C4 := E.code hM4.1
  have hmp4 : memLoad32 M4 (F + BitVec.ofNat 32 0x14) = MP := (hM4.2.load (c := 8) (by decide)).trans hmp
  have hml4 : memLoad32 M4 (F + BitVec.ofNat 32 0x10) = BitVec.ofNat 32 ML :=
    (hM4.2.load (c := 4) (by decide)).trans hml
  refine WP.aluImm rkm_at_2f6 ?_; wn
  refine WP.lw rkm_at_2f8 (by (try rsimp); rw [hsp]; exact E.alF (c := 0x14) (by decide)) ?_; wn
  refine WP.lw rkm_at_2fa (by (try rsimp); rw [hsp]; exact E.alF (c := 0x10) (by decide)) ?_; wn
  refine WP.callSha256M (sp0 := F) (out := F + BitVec.ofNat 32 0x18C) (p := MP) (n := ML)
    rkm_at_2fc rkm_at_300 (by decide) (by decide)
    (E.sha C4.sha E.hMw (by have := E.wF (c := 0x18C) (k := 32) (by decide); omega)
      (E.hSM.sub (c := 0x34C0) (l := 0x270) (by decide)).symm
      (by rw [hF18C]; exact E.ss (Or.inr (by decide)) (by decide) (by decide)))
    (by (try rsimp); exact hsp) (by (try rsimp); rw [ev_add, hsp]; rfl)
    (by (try rsimp); rw [hsp]; exact hmp4) (by (try rsimp); rw [hsp]; exact hml4) E.hML
    (by rw [hw2]; exact E.lowS (by decide) (by decide) (by decide)) (E.cF (by decide)) fun m5 hh hk5 => ?_
  rw [hw2] at hk5
  have hM5 : RmVM M1 Mz m5.mem s F := RmVM.two E.toRmBase hM4 (d1 := 0x34C0) (l1 := 0x270) (d2 := 0x38BC) (l2 := 32)
    (by rw [← hF18C]; exact hk5) (by decide) (by decide)
  have hr5 : memBytes m5.mem (F + BitVec.ofNat 32 0x12C) 32 = r := by
    rw [← hr4]
    exact rmv_kb E.toRmBase (d1 := 0x34C0) (l1 := 0x270) (d2 := 0x38BC) (l2 := 32)
      (by rw [← hF18C]; exact hk5) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs5 : memBytes m5.mem (F + BitVec.ofNat 32 0x15C) 32 = s' := by
    rw [← hs4]
    exact rmv_kb E.toRmBase (d1 := 0x34C0) (l1 := 0x270) (d2 := 0x38BC) (l2 := 32)
      (by rw [← hF18C]; exact hk5) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [E.bytes hM4.1 E.hSM] at hh
  clear hk5 hr4 hs4
  generalize m5.mem = M5 at hM5 hr5 hs5 hh
  have C5 := E.code hM5.1
  have hin : ∀ {c l : Nat}, c + l ≤ 0x1F0 →
      P2vIn (s + BitVec.ofNat 32 0x1A0) (F + BitVec.ofNat 32 c) l := fun {c l} hcl =>
    ⟨by
      rw [E.p2lo, E.Fc]
      have := E.ss (c := 0x3730 + c) (n := l) (d := 0) (k := 0x3730) (Or.inr (by omega)) (by omega) (by decide)
      rwa [add_ofNat_zero] at this,
      by rw [E.FN (by omega)]; omega, E.wF hcl⟩
  refine WP.aluImm rkm_at_304 ?_; wn
  refine WP.aluImm rkm_at_306 ?_; wn
  refine WP.aluImm rkm_at_308 ?_; wn
  refine WP.alu rkm_at_30a ?_; wn
  refine WP.callP2vM (B := s + BitVec.ofNat 32 0x1A0) (pk := pk) (dg := F + BitVec.ofNat 32 0x18C)
    (rp := F + BitVec.ofNat 32 0x12C) (sq := F + BitVec.ofNat 32 0x15C) rkm_at_30c rkm_at_310 (by decide) (by decide)
    (fun m _ => hH m) C5.p2v C5.p2k E.p2fr E.p2ro (by (try rsimp); rw [hsp]; exact E.p2F) (by (try rsimp); rw [ev0, h8])
    (by (try rsimp); rw [ev_add, hsp]; rfl) (by (try rsimp); rw [ev_add, hsp]; rfl)
    (by (try rsimp); rw [ev_add, hsp]; rfl) (hin (by decide)) (hin (by decide))
    ⟨by rw [E.p2lo]; have := (hpk.sub (c := 0) (l := 0x3730) (by decide)).symm; rwa [add_ofNat_zero] at this,
      hpk0, hpkw⟩ (hin (by decide))
    (by
      rw [E.p2lo]
      have := E.lowS (c := 0) (w := 0x3730) (b := TRM) (l := tufRoleKeysMetCode.length) (by decide) (by decide)
        (by decide)
      rwa [add_ofNat_zero] at this) fun m6 hv hO6 => ?_
  have hM6 : RmVM M1 Mz m6.mem s F := RmVM.one E.toRmBase hM5 (d := 0) (by rw [add_ofNat_zero, ← E.p2lo]; exact hO6) (by decide)
  refine hdone m6.mem _ hM6 (by rmkeep hK) (by rsimp; (try exact hz)) (by keepz E.hz0) fun ha => ⟨r, s', hes, ?_⟩
  have hv' := hv (by (try rsimp at ha); exact ha)
  rwa [E.bytes hM5.1 hpk, hh, hr5, hs5] at hv'

theorem rm_okEd {k msg sig bs : Bytes} (hp : parseHex sig = some bs) (hl : bs.length = 64)
    (hv : ed25519Verify k msg bs = true) : sigOkT (2, k) msg sig = true := by
  show sigValid (.ed25519 k) msg sig = true
  unfold sigValid; rw [hp]
  show (bs.length == 64 && ed25519Verify k msg bs) = true
  rw [hl, hv]; rfl

theorem rm_ok384 {k msg sig bs r s : Bytes} (hp : parseHex sig = some bs) (he : ecdsaSignature 48 bs = some (r, s))
    (hv : p384Verify k (sha384 msg) r s = true) : sigOkT (1, k) msg sig = true := by
  show sigValid (.p384 k) msg sig = true
  unfold sigValid; rw [hp]
  show (match ecdsaSignature 48 bs with | some (r, s) => p384Verify k (sha384 msg) r s | none => false) = true
  rw [he]; exact hv

theorem rm_ok256 {k msg sig bs r s : Bytes} (hp : parseHex sig = some bs) (he : ecdsaSignature 32 bs = some (r, s))
    (hv : p256Verify k (sha256 msg) r s = true) : sigOkT (0, k) msg sig = true := by
  show sigValid (.p256 k) msg sig = true
  unfold sigValid; rw [hp]
  show (match ecdsaSignature 32 bs with | some (r, s) => p256Verify k (sha256 msg) r s | none => false) = true
  rw [he]; exact hv

/-- From 0x22A: the check for the slot's tag. The decoded signature `bs`
of the hex signature `sig` is at `F + 0x48`; `a0` is nonzero at 0x314 only
when `sig` checks against slot `i`'s key. -/
theorem rm_ver (E : RmEnv M0 M1 s F R MP SP ML SL g0) (hH : ∀ m, Halting m → rmQ H M0 s g0 S m.pc m.mem (reg m))
    {t : Nat} {es : List RkEntry} (hR : RkAt M0 R t es) (hw : RkWf es) {i ti : Nat} {ki : Bytes} (hi8 : i < 8)
    (hki : rmKeyAt es i = some (ti, ki)) {G g : Fin 32 → Word} (hK : ∀ x, x ∈ rmSL → g x = G x)
    (hsp : g sp = F) (hz : g 0 = 0) (hfr : ∀ x, x ∉ rkE → g x = g0 x) (h27 : g 27 = R + BitVec.ofNat 32 (98 * i))
    (h24 : g 24 = (BitVec.ofNat 8 ti).zeroExtend 32) {l : Nat} {sig bs : Bytes}
    (h10 : g 10 = F + BitVec.ofNat 32 0x48) (h11 : g 11 = BitVec.ofNat 32 (l / 2)) (hl : l ≤ 256)
    (hp : parseHex sig = some bs) (hbl : bs.length = l / 2)
    {Mk : Word → BitVec 8} (hM : RmVM M1 Mz Mk s F) (hbm : memBytes Mk (F + BitVec.ofNat 32 0x48) (l / 2) = bs)
    (hmp : memLoad32 Mz (F + BitVec.ofNat 32 0x14) = MP)
    (hml : memLoad32 Mz (F + BitVec.ofNat 32 0x10) = BitVec.ofNat 32 ML)
    (hskip : ∀ Mk' g', RmVM M1 Mz Mk' s F → (∀ x, x ∈ rmSL → g' x = G x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk' 0x2C0 g')
    (hdone : ∀ Mk' g', RmVM M1 Mz Mk' s F → (∀ x, x ∈ rmSL → g' x = G x) → g' 0 = 0 →
      (∀ x, x ∉ rkE → g' x = g0 x) → (g' 10 ≠ 0 → sigOkT (ti, nb ki) (memBytes M0 MP ML) sig = true) →
      WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk' 0x314 g') :
    WP tufRoleKeysMetCode TRM (rmQ H M0 s g0 S) Mk 0x22A g := by
  rcases rm_slotKey hR hi8 with ⟨hn, -⟩ | ⟨tj, kj, hk', -, hb⟩
  · rw [hki] at hn; cases hn
  rw [hki] at hk'; cases hk'
  have hRw := E.hRw
  have hRN : (R + BitVec.ofNat 32 (98 * i + 1)).toNat = R.toNat + (98 * i + 1) := E.RN (by omega)
  have hSk : ∀ {w : Nat}, w ≤ 97 → Sep s 0x3920 (R + BitVec.ofNat 32 (98 * i + 1)) w := fun hw' =>
    E.hSR.subR (by omega)
  have hn : l / 2 ≤ 128 := by omega
  refine WP.alu rkm_at_22a ?_; wn
  refine WP.alu rkm_at_22c ?_; wn
  refine WP.aluImm rkm_at_22e ?_; wn
  refine WP.aluImm rkm_at_232 ?_; wn
  have h8 : aluEval .add (g 27) 1 = R + BitVec.ofNat 32 (98 * i + 1) := by
    rw [ev_add, h27]; exact add_ofNat_assoc R (98 * i) 1
  rcases rm_wfAt hw hki with ⟨ht, hkl⟩ | ⟨ht, hkl⟩ | ⟨ht, hkl⟩ <;> simp only at ht hkl <;> subst ht
  · -- P-256
    refine WP.branch rkm_at_234 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [h24] at eb; exact absurd eb (by decide)
    refine WP.aluImm rkm_at_238 ?_; wn
    refine WP.branch rkm_at_23a (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [h24] at eb; exact absurd eb (by decide)
    refine rm_p256 E hH (G := G) (by rmkeep hK) (by rsimp; exact hsp) (by rsimp; (try exact hz)) (by keepz E.hz0)
      (pk := R + BitVec.ofNat 32 (98 * i + 1)) (by (try rsimp); exact h8) (hSk (by decide)) (by omega) (by omega) hn
      (by (try rsimp); (try rw [show g x0 = 0 from hz]); rw [ev0, h11]) (by (try rsimp); (try rw [show g x0 = 0 from hz]); rw [ev0, h10]) hM hmp hml
      (fun Mk' g' a b c d => hskip Mk' g' a b c d) fun Mk' g' a b c d hv => hdone Mk' g' a b c d fun ha => ?_
    obtain ⟨r, s', hes, hv'⟩ := hv ha
    rw [hkl] at hb; rw [hb] at hv'
    have he := ecdsaSignature_mem hes
    rw [hbm] at he
    exact rm_ok256 hp he hv'
  · -- P-384
    refine WP.branch rkm_at_234 (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [h24] at eb; exact absurd eb (by decide)
    refine WP.aluImm rkm_at_238 ?_; wn
    refine WP.branch rkm_at_23a (fun eb => ?_) (fun _ => ?_) <;> wn
    · exfalso; (try rsimp at eb); rw [h24] at eb; exact absurd eb (by decide)
    refine rm_p384 E hH (G := G) (by rmkeep hK) (by rsimp; exact hsp) (by rsimp; (try exact hz)) (by keepz E.hz0)
      (pk := R + BitVec.ofNat 32 (98 * i + 1)) (by (try rsimp); exact h8) (hSk (by decide)) (by omega) hn
      (by (try rsimp); (try rw [show g x0 = 0 from hz]); rw [ev0, h11]) (by (try rsimp); (try rw [show g x0 = 0 from hz]); rw [ev0, h10]) hM hmp hml
      (fun Mk' g' a b c d => hskip Mk' g' a b c d) fun Mk' g' a b c d hv => hdone Mk' g' a b c d fun ha => ?_
    obtain ⟨r, s', hes, hv'⟩ := hv ha
    rw [hkl] at hb; rw [hb] at hv'
    have he := ecdsaSignature_mem hes
    rw [hbm] at he
    exact rm_ok384 hp he hv'
  · -- Ed25519
    refine WP.branch rkm_at_234 (fun _ => ?_) (fun eb => ?_) <;> wn
    rotate_left
    · exfalso; (try rsimp at eb); rw [h24] at eb; exact absurd eb (by decide)
    refine rm_ed E (G := G) (by rmkeep hK) (by rsimp; exact hsp) (by rsimp; (try exact hz)) (by keepz E.hz0)
      (pk := R + BitVec.ofNat 32 (98 * i + 1)) (by (try rsimp); exact h8) (hSk (by decide)) (by omega) hn
      (by (try rsimp); (try rw [show g x0 = 0 from hz]); rw [ev0, h11]) (by (try rsimp); (try rw [show g x0 = 0 from hz]); rw [ev0, h10]) hM hmp hml
      (fun Mk' g' a b c d => hskip Mk' g' a b c d) fun Mk' g' a b c d hv => hdone Mk' g' a b c d fun ha => ?_
    obtain ⟨h64, hv'⟩ := hv ha
    rw [hkl] at hb; rw [hb, ← h64, hbm] at hv'
    exact rm_okEd hp (by rw [hbl, h64]) hv'

end

end C3.RV32
