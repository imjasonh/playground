import C3BootProofs.Proofs.TufRoleKeys

/-!
# The code that `RoleKeys::read` runs, and its calls

`RkCode` names the code `RoleKeys::read` and its callees run and the keys
and prefixes it compares. The call wrappers turn the contracts of
`pem_spki`, `hex_decode`, and `copy_from_slice` into steps of the caller's
weakest precondition.
-/

namespace C3.RV32

open C3.Image C3.Json

set_option maxRecDepth 20000

abbrev TRK_ROLES : Word := BitVec.ofNat 32 tufRolesKeyAddress
abbrev TRK_THR : Word := BitVec.ofNat 32 tufThresholdKeyAddress
abbrev TRK_KEYS : Word := BitVec.ofNat 32 tufKeysKeyAddress
abbrev TRK_KIDS : Word := BitVec.ofNat 32 tufKeyidsKeyAddress
abbrev TRK_KT : Word := BitVec.ofNat 32 tufKeytypeKeyAddress
abbrev TRK_SC : Word := BitVec.ofNat 32 tufSchemeKeyAddress
abbrev TRK_KV : Word := BitVec.ofNat 32 tufKeyvalKeyAddress
abbrev TRK_PUB : Word := BitVec.ofNat 32 tufPublicKeyAddress
abbrev TRK_P256 : Word := BitVec.ofNat 32 tufP256PrefixAddress
abbrev TRK_P384 : Word := BitVec.ofNat 32 tufP384PrefixAddress
abbrev TRK_HEX : Word := BitVec.ofNat 32 tufHexDecodeAddress

/-- The code `RoleKeys::read` runs, and the keys and prefixes it compares. -/
structure RkCode (M : Word → BitVec 8) : Prop where
  self : CodeIn M TRK tufRoleKeysReadCode
  pm : PmCode M
  u64 : CodeIn M TPR_JU jsonU64Code
  aad : CodeIn M AAD allAsciiDigitCode
  tps : TpsCode M
  hex : CodeIn M TRK_HEX tufHexDecodeCode
  hv : CodeIn M (TRK_HEX + 0x88) tufHexValueCode
  roles : CodeIn M TRK_ROLES tufRolesKeyData
  thr : CodeIn M TRK_THR tufThresholdKeyData
  keys : CodeIn M TRK_KEYS tufKeysKeyData
  kids : CodeIn M TRK_KIDS tufKeyidsKeyData
  kt : CodeIn M TRK_KT tufKeytypeKeyData
  sc : CodeIn M TRK_SC tufSchemeKeyData
  kv : CodeIn M TRK_KV tufKeyvalKeyData
  pub : CodeIn M TRK_PUB tufPublicKeyData
  p256 : CodeIn M TRK_P256 tufP256PrefixData
  p384 : CodeIn M TRK_P384 tufP384PrefixData

theorem RkCode.of_out {M M' : Word → BitVec 8} {s : Word} {k : Nat} (h : RkCode M) (hO : Out M M' s k)
    (hs : s.toNat + k ≤ 0x40000000) (hro : Sep s k (BitVec.ofNat 32 roWindowAddress) roWindowSize) :
    RkCode M' :=
  ⟨tpm_codeIn h.self hO hs (by decide) (by decide), h.pm.of_out hO hs hro,
    tpm_codeIn h.u64 hO hs (by decide) (by decide), tpm_codeIn h.aad hO hs (by decide) (by decide),
    h.tps.of_out hO hs hro, tpm_codeIn h.hex hO hs (by decide) (by decide),
    tpm_codeIn h.hv hO hs (by decide) (by decide),
    hO.codeIn h.roles (tuf_sep_ro hro (by decide) (by decide)), hO.codeIn h.thr (tuf_sep_ro hro (by decide) (by decide)),
    hO.codeIn h.keys (tuf_sep_ro hro (by decide) (by decide)), hO.codeIn h.kids (tuf_sep_ro hro (by decide) (by decide)),
    hO.codeIn h.kt (tuf_sep_ro hro (by decide) (by decide)), hO.codeIn h.sc (tuf_sep_ro hro (by decide) (by decide)),
    hO.codeIn h.kv (tuf_sep_ro hro (by decide) (by decide)), hO.codeIn h.pub (tuf_sep_ro hro (by decide) (by decide)),
    hO.codeIn h.p256 (tuf_sep_ro hro (by decide) (by decide)),
    hO.codeIn h.p384 (tuf_sep_ro hro (by decide) (by decide))⟩

section
variable {M : Word → BitVec 8} (h : RkCode M)
include h

theorem RkCode.mRoles : memBytes M TRK_ROLES 5 = ascii!"roles" := tuf_codeIn_memBytes h.roles (by decide)
theorem RkCode.mThr : memBytes M TRK_THR 9 = ascii!"threshold" := tuf_codeIn_memBytes h.thr (by decide)
theorem RkCode.mKeys : memBytes M TRK_KEYS 4 = ascii!"keys" := tuf_codeIn_memBytes h.keys (by decide)
theorem RkCode.mKids : memBytes M TRK_KIDS 6 = ascii!"keyids" := tuf_codeIn_memBytes h.kids (by decide)
theorem RkCode.mKt : memBytes M TRK_KT 7 = ascii!"keytype" := tuf_codeIn_memBytes h.kt (by decide)
theorem RkCode.mSc : memBytes M TRK_SC 6 = ascii!"scheme" := tuf_codeIn_memBytes h.sc (by decide)
theorem RkCode.mKv : memBytes M TRK_KV 6 = ascii!"keyval" := tuf_codeIn_memBytes h.kv (by decide)
theorem RkCode.mPub : memBytes M TRK_PUB 6 = ascii!"public" := tuf_codeIn_memBytes h.pub (by decide)
theorem RkCode.mP256 : memBytes M TRK_P256 26 = p256SpkiPrefix := tuf_codeIn_memBytes h.p256 (by decide)
theorem RkCode.mP384 : memBytes M TRK_P384 23 = p384SpkiPrefix := tuf_codeIn_memBytes h.p384 (by decide)

end

/-- The registers `hex_decode` may change. -/
abbrev rkHexClob : List (Fin 32) := [a0, a1, a2, a3, a4, a5]

/-- The registers `copy_from_slice` may change. -/
abbrev rkCfsClob : List (Fin 32) := [a1, a2, a3, a4, a5, a6, a7, 5, 6, 7, 28, 29, 30]

section
variable {code : List Nat} {base : Word} {Q : Post} {M : Word → BitVec 8} {off : Nat} {f : Fin 32 → Word}

/-- A call to `pem_spki` on the `n` bytes at `p`, into the 128 bytes at
`out`, with its stack the 304 bytes at `s`. -/
theorem WP.callTps {hi lo out s p : Word} {n : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = TPS) (hev : (off + 8) % 2 = 0)
    (hc : TpsCode M) (h0 : f a0 = p) (ha1 : f a1 = BitVec.ofNat 32 n) (ha2 : f a2 = out)
    (hsp : f sp = s + BitVec.ofNat 32 304) (hal : s.toNat % 4 = 0) (hsw : s.toNat + 304 ≤ 0x40000000)
    (hro : Sep s 304 (BitVec.ofNat 32 roWindowAddress) roWindowSize) (hpw : p.toNat + n ≤ 0x40000000)
    (hSp : Sep s 304 p n) (how : out.toNat + 128 ≤ 0x40000000) (hso : Sep out 128 s 304)
    (hSb : Sep s 304 base code.length) (hsb : Sep out 128 base code.length)
    (k : ∀ m2 : Machine, TpsRes M m2.mem s out (reg m2 a0) (reg m2 a1) (pemSpkiModel (memBytes M p n)) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 jClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := TPS) (cl := jClob)
    (P := fun m2 => TpsRes M m2.mem s out (reg m2 a0) (reg m2 a1) (pemSpkiModel (memBytes M p n)))
    h1 h2 (by rw [htgt]; exact even_clear _ (by decide)) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc' i hi => by
      have hfr : ∀ x, Sep x 1 s 304 → Sep x 1 out 128 → m2.mem x = M x := by
        rcases hq : pemSpkiModel (memBytes M p n) with _ | _ <;> rw [hq] at hP
        · exact hP.1
        · exact hP.1
      rw [hfr _ (hSb.symm.sub (c := i) (l := 1) hi) (hsb.symm.sub (c := i) (l := 1) hi)]
      exact hc' i hi) k
  obtain ⟨m2, c2, pc2, hR, hfr⟩ := tufPemSpki_correct m1 (retAddr := base + BitVec.ofNat 32 (off + 8))
    (out := out) (s := s) (p := p) (n := n)
    (by rw [hmem1]; exact hc) hpc1 (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1)
    (by rw [hreg1]; rsimp; exact ha2) (by rw [hreg1]; rsimp; exact hsp) (by rw [hreg1]; rsimp)
    (even_clear _ (even_at base hb _ hev)) hal hsw hro hpw hSp how hso
  rw [hmem1] at hR
  exact ⟨m2, c2, pc2, hR, hfr⟩

/-- A call to `hex_decode` on the `len` bytes at `text`, into the 128 bytes
at `out`, whose frame is the 32 bytes at `r`. -/
theorem WP.callHex {hi lo text out r : Word} {len : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = TRK_HEX) (hev : (off + 8) % 2 = 0)
    (hc : CodeIn M TRK_HEX tufHexDecodeCode) (hv : CodeIn M (TRK_HEX + 0x88) tufHexValueCode)
    (h0 : f a0 = text) (ha1 : f a1 = BitVec.ofNat 32 len) (ha2 : f a2 = out) (hlen : len < 2 ^ 32)
    (hsp : f sp + 0xFFFFFFE0 = r) (hal : (f sp).toNat % 4 = 0)
    (sSC : Sep r 32 TRK_HEX tufHexDecodeCode.length) (sSV : Sep r 32 (TRK_HEX + 0x88) tufHexValueCode.length)
    (sST : Sep r 32 text len) (sSO : Sep r 32 out 128) (sOC : Sep out 128 TRK_HEX tufHexDecodeCode.length)
    (sOV : Sep out 128 (TRK_HEX + 0x88) tufHexValueCode.length) (sOT : Sep out 128 text len)
    (hSb : Sep r 32 base code.length) (hsb : Sep out 128 base code.length)
    (k : ∀ m2 : Machine, reg m2 a0 = (if (tufHexDecodeSpec M text len).isSome then out else 0) →
      reg m2 a1 = BitVec.ofNat 32 (len / 2) →
      (∀ bs, tufHexDecodeSpec M text len = some bs → bs.length = len / 2 ∧ memBytes m2.mem out (len / 2) = bs) →
      (∀ x, Sep x 1 r 32 → Sep x 1 out 128 → m2.mem x = M x) →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 rkHexClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := TRK_HEX) (cl := rkHexClob)
    (P := fun m2 => reg m2 a0 = (if (tufHexDecodeSpec M text len).isSome then out else 0) ∧
      reg m2 a1 = BitVec.ofNat 32 (len / 2) ∧
      (∀ bs, tufHexDecodeSpec M text len = some bs → bs.length = len / 2 ∧ memBytes m2.mem out (len / 2) = bs) ∧
      (∀ x, Sep x 1 r 32 → Sep x 1 out 128 → m2.mem x = M x))
    h1 h2 (by rw [htgt]; exact even_clear _ (by decide)) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc' i hi => by
      rw [hP.2.2.2 _ (hSb.symm.sub (c := i) (l := 1) hi) (hsb.symm.sub (c := i) (l := 1) hi)]
      exact hc' i hi) (fun m2 hP => k m2 hP.1 hP.2.1 hP.2.2.1 hP.2.2.2)
  have hs1 : reg m1 sp = f sp := by rw [hreg1]; rsimp
  obtain ⟨m2, c2, pc2, r0, r1, rb, hfr, hmf⟩ := tufHexDecode_correct m1 (base := TRK_HEX) (text := text)
    (out := out) (len := len) (by rw [hmem1]; exact hc) (by rw [hmem1]; exact hv) (by decide) hpc1
    (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2) hlen
    (retAddr := base + BitVec.ofNat 32 (off + 8)) (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev))
    (by rw [hs1]; exact hal) (by rw [hs1, hsp]; exact sSC) (by rw [hs1, hsp]; exact sSV)
    (by rw [hs1, hsp]; exact sST) (by rw [hs1, hsp]; exact sSO) sOC sOV sOT
  rw [hmem1] at r0 rb
  refine ⟨m2, c2, pc2, ⟨r0, r1, rb, fun x hx ho => ?_⟩, fun x hx => ?_⟩
  · rw [hmf x (by rw [hs1, hsp]; exact hx.symm) ho.symm, hmem1]
  · simp only [rkHexClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hx
    exact hfr x n0 n1 n2 n3 n4 n5

/-- A call to `copy_from_slice(dst, src)` with both lengths `N`, whose
frame is the 16 bytes at `F`. -/
theorem WP.callCfs {hi lo dst src F : Word} {N : Nat}
    (h1 : fetchRel code off = some (.auipc ra hi, 4)) (h2 : fetchRel code (off + 4) = some (.jalr ra ra lo, 4))
    (htgt : base + BitVec.ofNat 32 off + hi + lo = BCW) (hev : (off + 8) % 2 = 0)
    (hcw : CodeIn M BCW copyFromSliceU8Code) (hcs : CodeIn M BMS memcpyStubCode) (E : McEnv M BMB dst src F N)
    (h0 : f a0 = dst) (ha1 : f a1 = BitVec.ofNat 32 N) (ha2 : f a2 = src) (ha3 : f a3 = BitVec.ofNat 32 N)
    (hsp : f sp = F + 16) (hFb : Sep F 16 base code.length) (hDb : Sep dst N base code.length)
    (k : ∀ m2 : Machine, Out (copyBytes M dst src N) m2.mem F 16 →
      WP code base Q m2.mem (off + 8) (clob (upd f ra (base + BitVec.ofNat 32 (off + 8))) m2 rkCfsClob)) :
    WP code base Q M off f := by
  refine WP.callGen (tb := BCW) (cl := rkCfsClob) (P := fun m2 => Out (copyBytes M dst src N) m2.mem F 16)
    h1 h2 (by rw [htgt]; exact even_clear _ (by decide)) (fun m1 hpc1 hmem1 hreg1 hb => ?_)
    (fun m2 hP hc => hP.codeIn (fun i hi => by
      rw [copyBytes_sep (sep_pt hDb hi).symm (Nat.le_refl _)]; exact hc i hi) hFb) k
  have hsp1 : reg m1 sp = F + 16 := by rw [hreg1]; rsimp; exact hsp
  have hF : reg m1 sp + 0xFFFFFFF0 = F := by
    rw [hsp1, BitVec.add_assoc, show (16 : Word) + 0xFFFFFFF0 = 0 by decide, add_lit_zero]
  obtain ⟨m2, c2, pc2, sp2, -, hmem, hfr⟩ := copyFromSliceU8_correct m1 (W := BCW)
    (retAddr := base + BitVec.ofNat 32 (off + 8)) (dst := dst) (src := src) (n := N) (by decide)
    (by rw [hmem1]; exact hcw) (by rw [hmem1, show BCW + 0x761E = BMS by decide]; exact hcs) hpc1
    (by rw [hreg1]; rsimp; exact h0) (by rw [hreg1]; rsimp; exact ha1) (by rw [hreg1]; rsimp; exact ha2)
    (by rw [hreg1]; rsimp; exact ha3) (by rw [hreg1]; rsimp) (even_clear _ (even_at base hb _ hev))
    (by rw [hF, hmem1, show BCW + 0x761E + 8 = BMB by decide]; exact E)
  refine ⟨m2, c2, pc2, fun x hx => ?_, fun x hx => ?_⟩
  · rw [hmem x (by rw [hF]; exact hx.symm), hmem1]
  · by_cases hs : x = sp
    · subst hs; exact sp2
    simp only [rkCfsClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := hx
    exact hfr x n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 hs

end

end C3.RV32
