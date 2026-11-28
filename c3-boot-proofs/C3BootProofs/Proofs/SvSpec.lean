import C3BootProofs.Proofs.SvGsSpec
import C3BootProofs.Models.SafegcdP256
import C3BootProofs.Models.SafegcdP384
import C3BootProofs.Models.EcdsaClosed
import C3BootProofs.Models.P256Consts
import C3BootProofs.Proofs.SvPvWitness
import C3BootProofs.Proofs.SvEdImage
import C3BootProofs.Proofs.SvVerifyAt
import C3BootProofs.Proofs.SvSpecAux

/-!
# `sigstore::verify` computes `sigstoreVerify`

`sv_verify_spec_pi`: called with a `Bundle` and a `SigstoreRoot` laid out
as `SvBundleAt` and `SvRootAt` say, and the artifact's digest at `a3`, the
compiled `sigstore::verify` returns `Err`, panics only if an inversion bound
fails (`PanicIf`), or returns `Ok` with the time and log index of
`sigstoreVerify bundle root digest`. `sv_verify_spec` weakens the panic to
`Panics`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Gd C3.RV32.P2v

theorem fulcio_addr {r q : Word} {i : Nat} (h : q = r + BitVec.ofNat 32 0x2C + BitVec.ofNat 32 (i * 0x20)) :
    q + 0xFFFFFFFC = r + 0x28 + BitVec.ofNat 32 (0x20 * i) ∧ q + 0x0 = r + 0x28 + BitVec.ofNat 32 (0x20 * i) + 4 ∧
      (q + BitVec.ofNat 32 0x20) + 0xFFFFFFF4 = r + 0x28 + BitVec.ofNat 32 (0x20 * i) + 0x18 := by
  subst h
  rw [Nat.mul_comm i 0x20]
  refine ⟨?_, ?_, ?_⟩ <;> bv_omega

theorem derOptRes_tlv {tag : Nat} {L : Bytes} {t : DerTlv} (h : derOptRes tag L = some (.ok t)) : derTlv L = .ok t := by
  cases L with
  | nil => cases h
  | cons b rest =>
    change (if b = tag then some (derTlv (b :: rest)) else none) = _ at h
    by_cases hb : b = tag
    · rw [ite_eq_left hb] at h; exact Option.some.inj h
    · rw [ite_eq_right hb] at h; cases h

theorem tsa_addr {r q : Word} {i : Nat} (h : q = r + BitVec.ofNat 32 0x308 + BitVec.ofNat 32 (i * 0x20)) :
    q + 0x20 = r + 0x328 + BitVec.ofNat 32 (0x20 * i) ∧ q + 0x24 = r + 0x328 + BitVec.ofNat 32 (0x20 * i) + 4 ∧
      (q + BitVec.ofNat 32 0x20) + 0x18 = r + 0x328 + BitVec.ofNat 32 (0x20 * i) + 0x18 := by
  subst h
  rw [Nat.mul_comm i 0x20]
  refine ⟨?_, ?_, ?_⟩ <;> bv_omega

theorem dec1_toNat {k : Nat} (h1 : 1 ≤ k) (h2 : k < 2 ^ 32) : (BitVec.ofNat 32 k + BitVec.ofNat 32 0xFFFFFFFF).toNat = k - 1 := by
  rw [BitVec.toNat_add, ofNat_toNat_lt h2, ofNat_toNat_lt (by decide)]; omega

/-- **`sv_verify_spec` with its panic refined**: `sigstore::verify` returns
`Err`, panics only if an inversion bound fails, or computes
`sigstoreVerify`. -/
def SvVerifySpecPI : Prop :=
  ∀ {Me : Word → BitVec 8} {n : Machine} {B : Word} {bundle : Bundle} {root : SigstoreRoot}
    (_Bd : SvBundleAt B Me (reg n a1) bundle) (_R : SvRootAt B Me (reg n a2) root)
    (_C : CodeIn Me SV sigstoreVerifyCode)
    (_E : SvCode Me)
    (_FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (_s : St Me SV n 0 (reg n))
    (_rsp : reg n sp = B + 0x2660)
    (_hret : ((fun k => reg n (savedReg k))) 0 &&& ~~~1 = ((fun k => reg n (savedReg k))) 0)
    (_hO : SvOut B (reg n a0))
    (_D0 : P2Data Me)
    (_SD0 : SvData Me)
    (_HE0 : HfEnv Me)
    (_RS : SvRoSep B)
    (_PE0 : PvEnv7 Me)
    (_PE0' : P2vEnv Me)
    (_dg_in : SvIn B (reg n a3) 32)
    (_S2 : SvSha2Code Me)
    (_CK0 : SvCkCode Me)
    (_EE0 : EvEnv Me)
    (_hiv : (s5Hv Me (BitVec.ofNat 32 (img% sha512IVAddress))).toList = Sha512.h0)
    (_RK0 : SvRkCode Me)
    (_hOk : SvOutOk B (reg n a0))
    (_OD : SvOidData Me)
    (_ND : CodeIn Me (BitVec.ofNat 32 b2sOrder256Address) b2sOrder256Data)
    (_UD : CodeIn Me (BitVec.ofNat 32 p256OneAddress) p256OneData)
    (_LD : CodeIn Me (BitVec.ofNat 32 edOrderAddress) edOrderData)
    (_PD : CodeIn Me (BitVec.ofNat 32 edPrimeAddress) edPrimeData)
    (_PmD : CodeIn Me (BitVec.ofNat 32 edPm1Address) edPm1Data)
    (_E1D : CodeIn Me (BitVec.ofNat 32 edOneAddress) edOneData)
    (_EdD : CodeIn Me (BitVec.ofNat 32 edDAddress) edDData)
    (_SmD : CodeIn Me (BitVec.ofNat 32 edSqrtM1Address) edSqrtM1Data)
    (_D2D : CodeIn Me (BitVec.ofNat 32 edwardsD2Address) edwardsD2Data)
    (_BsD : CodeIn Me (BitVec.ofNat 32 edBaseAddress) edBaseData)
    (_KRD : CodeIn Me (BitVec.ofNat 32 edMontRAddress) edMontRData)
    (_KRRD : CodeIn Me (BitVec.ofNat 32 edMontRRAddress) edMontRRData)
    (_RD : SvRekorData Me),
    SvErrRet B (reg n a0) (fun k => reg n (savedReg k)) n ∨ PanicIf n ∨
      ∃ v, sigstoreVerify bundle root (memBytes Me (reg n a3) 32) = some v ∧
        SvOkRet B (reg n a0) (fun k => reg n (savedReg k)) n (BitVec.ofNat 32 (v.signedTime % 2 ^ 32))
          (BitVec.ofNat 32 (v.signedTime / 2 ^ 32)) (BitVec.ofNat 32 (v.logIndex % 2 ^ 32))
          (BitVec.ofNat 32 (v.logIndex / 2 ^ 32))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
/-- **`sigstore::verify` computes `sigstoreVerify`**, and panics only if an
inversion bound fails. -/
theorem sv_verify_spec_pi : SvVerifySpecPI := by
  intro Me n B bundle root Bd R C E FW s rsp hret hO D0 SD0 HE0 RS PE0 PE0' dg_in S2 CK0 EE0 hiv RK0 hOk OD ND UD LD
    PD PmD E1D EdD SmD D2D BsD KRD KRRD RD
  rcases sv_verify_at Bd R C E FW s rsp hret hO D0 SD0 HE0 RS PE0
    (fun _ _ _ _ _ _ M => C3.RV32.Safegcd.pvSide_holds M _ _ _ _ _) PE0' dg_in S2
    (fun _ _ _ _ _ _ M => C3.RV32.Safegcd.pvSide_holds M _ _ _ _ _) CK0 EE0 hiv RK0 hOk with e | p | hsc
  · exact .inl e
  · exact .inr (.inl p)
  refine .inr (.inr ?_)
  obtain ⟨t_1_1_1, c0, c1, tl1_2_1_1, c2, tl8_2_1_1, c3, tl16_2_1_1, c4, bp16_2_1_1, bl16_2_1_1, c5, hsc⟩ := hsc
  obtain ⟨c6, tl28_2_1_1, c7, c8, te41_2_1_1, c9, c10, tl1_3_1_1, c11, ip1_3_1_1, il1_3_1_1, c12, hsc⟩ := hsc
  obtain ⟨c13, tl8_3_1_1, c14, op21_3_1_1, ol21_3_1_1, c15, c16, tl3_4_1_1, c17, tl11_4_1_1, c18, tm20_4_1_1, hsc⟩ := hsc
  obtain ⟨rs20_4_1_1, c19, tm28_4_1_1, rs28_4_1_1, c20, c21, tl2_5_1_1, c22, tl6_5_1_1, c23, op15_5_1_1, ol15_5_1_1, hsc⟩ := hsc
  obtain ⟨prp15_5_1_1, pu15_5_1_1, c24, ta15_5_1_1, c25, c26, c27, c28, tl35_5_1_1, c29, bp35_5_1_1, bl35_5_1_1, hsc⟩ := hsc
  obtain ⟨c30, c31, c32, c33, c34, tl9_6_1_1, c35, c36, tl24_6_1_1, c37, c38, u0_1, hsc⟩ := hsc
  obtain ⟨u1_1, u2_1, k_2_1, f2c'_2_1, f30'_2_1, rem'_2_1, sl0'_2_1, sl1'_2_1, sl2'_2_1, sl3'_2_1, sl4'_2_1, sl5'_2_1, hsc⟩ := hsc
  obtain ⟨sl6'_2_1, sl7'_2_1, sl8'_2_1, sl9'_2_1, cur'_2_1, c39, c40, c41, c42, c43, c44, c45, hsc⟩ := hsc
  obtain ⟨c46, c47, c48, c49, c50, c51, sr40_2_1, ss40_2_1, c52, k_4_1, c53, c54, hsc⟩ := hsc
  obtain ⟨c'_4_1, q'_4_1, c55, c56, c57, pv_5_1, c58, c59, c60, c61, c62, c63, hsc⟩ := hsc
  obtain ⟨c64, sr43_6_1, ss43_6_1, c65, c66, tl10_1_1_3, c67, c68, tl21_1_1_3, c69, c70, te30_1_1_3, hsc⟩ := hsc
  obtain ⟨c71, c72, tl2_2_1_3, c73, c74, op13_2_1_3, ol13_2_1_3, c75, to13_2_1_3, c76, c77, tl21_2_1_3, hsc⟩ := hsc
  obtain ⟨c78, c79, tl32_2_1_3, c80, c81, c82, te43_2_1_3, c83, tl2_3_1_3, c84, c85, te11_3_1_3, hsc⟩ := hsc
  obtain ⟨c86, c87, tl19_3_1_3, c88, op28_3_1_3, ol28_3_1_3, c89, to28_3_1_3, c90, c91, tl2_4_1_3, c92, hsc⟩ := hsc
  obtain ⟨c93, vp23_4_1_3, vl23_4_1_3, c94, te23_4_1_3, c95, c96, tr5_w328_5_1_3, tr5_w32c_5_1_3, c97, c98, tl2_6_1_3, hsc⟩ := hsc
  obtain ⟨c99, c100, tl13_6_1_3, c101, c102, c103, te25_6_1_3, c104, tl31_6_1_3, c105, c106, te39_6_1_3, hsc⟩ := hsc
  obtain ⟨c107, tl45_6_1_3, c108, c109, c110, tl6_1_2_3, c111, op15_1_2_3, ol15_1_2_3, c112, to15_1_2_3, c113, hsc⟩ := hsc
  obtain ⟨tl20_1_2_3, c114, c115, c116, trv_w64_2_2_3, trv_w7c_2_2_3, c117, c118, k_3_3, dg'_3_3, flag'_3_3, cp'_3_3, hsc⟩ := hsc
  obtain ⟨rem'_3_3, c119, c120, c121, c122, op9_3_3, ol9_3_3, c123, te9_3_3, c124, c125, vp20_3_3, hsc⟩ := hsc
  obtain ⟨vl20_3_3, c126, te20_3_3, c127, sr25_3_3, ss25_3_3, c128, c129, tl9_1_4_3, c130, c131, c132, hsc⟩ := hsc
  obtain ⟨te20_1_4_3, c133, op26_1_4_3, ol26_1_4_3, c134, to26_1_4_3, c135, tl30_1_4_3, c136, c137, te39_1_4_3, c138, hsc⟩ := hsc
  obtain ⟨vp45_1_4_3, vl45_1_4_3, c139, te45_1_4_3, c140, c141, c142, tl2_2_4_3, c143, ip2_2_4_3, il2_2_4_3, c144, hsc⟩ := hsc
  obtain ⟨c145, tl13_2_4_3, c146, tm18_2_4_3, c147, tt3_w264_3_4_3, tt3_w268_3_4_3, c148, c149, tt4_w264_4_4_3, tt4_w268_4_4_3, c150, hsc⟩ := hsc
  obtain ⟨c151, tt5_w264_5_4_3, tt5_w268_5_4_3, c152, c153, tt6_w264_6_4_3, tt6_w268_6_4_3, c154, c155, k_6_3, c156, c157, hsc⟩ := hsc
  obtain ⟨c'_6_3, q'_6_3, c158, c159, c160, c161, c162, c163, pv_8_3, c164, c165, ix8_1_1_4, hsc⟩ := hsc
  obtain ⟨c166, ix18_1_1_4, c167, ix26_1_1_4, c168, ix34_1_1_4, c169, c170, c171, c172, c'_2_4, p'_2_4, hsc⟩ := hsc
  obtain ⟨w64'_2_4, w74'_2_4, c173, c174, c175, bs7_2_4, c176, c177, k_3_4, c178, c179, c'_3_4, hsc⟩ := hsc
  obtain ⟨q'_3_4, c180, c181, c182, sg_5_4, k_5_4, f'_5_4, w38'_5_4, w50'_5_4, sg'_5_4, c183, c184, hsc⟩ := hsc
  obtain ⟨c185, c186, c187, root6_3_6_4, c188, c189, c190, c191, c192, c193, c194, c195, hsc⟩ := hsc
  obtain ⟨c196, c197, c198⟩ := hsc
  subst c40
  have hext := readExtensions_code (sv_extConsts SD0) c37 c38 c39 c46 c47 c48 c49 c50
  have hleaf := parseLeaf_code c0 c1 rfl rfl c2 rfl rfl c3 rfl rfl c4 c5 c6 rfl rfl c7 rfl rfl c8 c9 c10 rfl rfl c11 c12
    c13 rfl rfl c14 c15 (c16.trans (sv_ecdsa384 OD)) rfl rfl c17 rfl rfl c18 c19 c20 c21 rfl rfl c22 rfl rfl c23 rfl rfl
    c24 c25 c26 (c27.trans (sv_prime256 OD)) (c28.trans (sv_ecpub OD)) c29 c30 c31 c32 (gsModel _ c33 c34) rfl rfl c35 c36
    hext c51 c52
  rw [Bd.leaf.2] at hleaf
  have fq : ∀ {i : Nat} {c q : Word}, (c, q) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i
      (BitVec.ofNat 32 0x100, reg n a2 + BitVec.ofNat 32 0x2C) →
      q + 0xFFFFFFFC = reg n a2 + 0x28 + BitVec.ofNat 32 (0x20 * i) ∧ q + 0x0 = reg n a2 + 0x28 + BitVec.ofNat 32 (0x20 * i) + 4 ∧
      (q + BitVec.ofNat 32 0x20) + 0xFFFFFFF4 = reg n a2 + 0x28 + BitVec.ofNat 32 (0x20 * i) + 0x18 := by
    intro i c q h
    exact fulcio_addr (svIter_ptr2 h)
  obtain ⟨fa1, fa2, fa3⟩ := fq c55
  rw [fa1, fa2] at c56
  rw [fa1] at c57
  rw [fa3] at c58
  obtain ⟨hkf, hfind⟩ := find?_of_search (l := root.fulcio) (cap := 8) (k := k_4_1) (name := FulcioKey.subject)
    (nameAt := fun i => memBytes Me (memLoad32 Me (reg n a2 + 0x28 + BitVec.ofNat 32 (0x20 * i)))
      (memLoad32 Me (reg n a2 + 0x28 + BitVec.ofNat 32 (0x20 * i) + 4)).toNat)
    (used := fun i => memLoad32 Me (reg n a2 + 0x28 + BitVec.ofNat 32 (0x20 * i)) ≠ 0)
    (fun i h => (R.fulcio.2.1 i h).name.2) (fun i h1 h2 hne => hne (R.fulcio.2.2 i h1 h2)) c53 c57 c56
    (fun i hi e => by
      have h0 := c54 i hi _ _ rfl
      obtain ⟨g1, g2, -⟩ := fq (i := i) rfl
      rw [g1, g2] at h0
      exact h0 e)
  have Ek := R.fulcio.2.1 k_4_1 hkf
  have hiss := c56.symm.trans Ek.name.2
  have hsr40 := ecdsaSigOf_bytes c52
  have hp384 := C3.Models.p384_model_closed _ _ _ _ _ _ _ _ _
    (svPvAt_frame (e1 := 0x170) (e2 := 0xC8) (e3 := 0xF8) (off_of_sep Ek.keyIn.sep) (isrn_off RS)
      (by rw [sha384_length]; rfl) (sha384_lt _) (by decide) (by decide) (by decide) (.inr (by decide))
      (.inr (by decide)) (.inl (by decide))) c58 c59
  rw [svBytes_self hsr40.1.1 hsr40.1.2, svBytes_self hsr40.2.1 hsr40.2.2, Ek.key] at hp384
  unfold sigstoreVerify
  rw [hleaf]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [hfind]
  simp only [Option.bind_some]
  unfold verifyLeaf
  rw [hiss, beq_iff_eq.mpr rfl, hp384]
  simp only [Bool.and_self, require_true, Option.bind_some]
  rw [show reg n a2 + 0x0 = reg n a2 from BitVec.add_zero _] at c60
  rw [c60.trans R.issuer.2, c61.trans R.buildSignerUri.2, c62.trans R.repositoryId.2, c63.trans R.ownerId.2,
    c64.trans R.trigger.2, beq_iff_eq.mpr rfl, require_true]
  simp only [Option.bind_some]
  have hsig := ecdsaSignature_mem c65
  rw [Bd.imageSignature.2] at hsig
  rw [hsig]
  simp only [Option.bind_some]
  have hp256 := C3.Models.p256_model_closed (C3.Models.P256Consts.of D0 ND UD PE0'.GD PE0'.OD PE0'.AD) _ _ _ _ c66
  have hsr43 := ecdsaSigOf_bytes c65
  rw [b32_self hsr43.1.1 hsr43.1.2, b32_self hsr43.1.1 hsr43.1.2, b32_self hsr43.2.1 hsr43.2.2,
    b32_self hsr43.2.1 hsr43.2.2] at hp256
  rw [c31, show (BitVec.ofNat 32 0x41).toNat = 65 from rfl, hp256, require_true]
  simp only [Option.bind_some]
  subst c120
  have hsa := readSignedAttributes_code (B := B) (sv_contentType SD0) (sv_tstInfo SD0) (sv_messageDigest SD0)
    (svChain.cons ⟨c109, c110, tl6_1_2_3, c111, op15_1_2_3, ol15_1_2_3, c112, to15_1_2_3, c113, tl20_1_2_3, c114, c115,
      c116, trv_w64_2_2_3, trv_w7c_2_2_3, c117, c118, rfl⟩ c119)
    c122.1 c122.2
  have htst := readTstInfo_code c130 c131 rfl rfl c132 c133 rfl rfl c134 c135 rfl rfl c136 rfl rfl c137 c138 c139 c140 c141
    c142 rfl rfl c143 c144 c145 rfl rfl c146 c147 (optional_code c148) c150 (optional_code c152) (optional_last_code c154)
  have hts := parseTimestamp_code (sv_signedData SD0) (sv_tstInfo SD0) (sv_ecdsa256 SD0) c67 c68 rfl rfl c69 rfl rfl c70 c71
    c72 rfl rfl c73 c74 rfl rfl c75 c76 c77 rfl rfl c78 c79 rfl rfl c80 c81 rfl rfl c82 c83 rfl rfl c84 c85 c86 c87
    rfl rfl c88 rfl rfl c89 c90 c91 rfl rfl c92 c93 rfl rfl c94 c95 c96 rfl rfl (tsa4_code c97) c99 c100 rfl rfl
    c101 c102 rfl rfl c103 c104 rfl rfl c105 c106 c107 rfl rfl c108 hsa rfl rfl c123 c124 c125 rfl rfl c126 c127 c128 c129
    htst
  rw [Bd.timestamp.2] at hts
  rw [hts]
  simp only [Option.bind_some]
  have tq : ∀ {i : Nat} {c q : Word}, (c, q) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i
      (BitVec.ofNat 32 0x100, reg n a2 + BitVec.ofNat 32 0x308) →
      q + 0x20 = reg n a2 + 0x328 + BitVec.ofNat 32 (0x20 * i) ∧ q + 0x24 = reg n a2 + 0x328 + BitVec.ofNat 32 (0x20 * i) + 4 ∧
      (q + BitVec.ofNat 32 0x20) + 0x18 = reg n a2 + 0x328 + BitVec.ofNat 32 (0x20 * i) + 0x18 := by
    intro i c q h
    exact tsa_addr (svIter_ptr2 h)
  obtain ⟨ta1, ta2, ta3⟩ := tq c158
  rw [ta1, ta2] at c159
  rw [ta1] at c160
  rw [ta3] at c164
  obtain ⟨hkt, hfindt⟩ := find?_of_search (l := root.tsas) (cap := 8) (k := k_6_3) (name := TsaKey.signerId)
    (nameAt := fun i => memBytes Me (memLoad32 Me (reg n a2 + 0x328 + BitVec.ofNat 32 (0x20 * i)))
      (memLoad32 Me (reg n a2 + 0x328 + BitVec.ofNat 32 (0x20 * i) + 4)).toNat)
    (used := fun i => memLoad32 Me (reg n a2 + 0x328 + BitVec.ofNat 32 (0x20 * i)) ≠ 0)
    (fun i h => (R.tsas.2.1 i h).name.2) (fun i h1 h2 hne => hne (R.tsas.2.2 i h1 h2)) c156 c160 c159
    (fun i hi e => by
      have h0 := c157 i hi _ _ rfl
      obtain ⟨g1, g2, -⟩ := tq (i := i) rfl
      rw [g1, g2] at h0
      exact h0 e)
  rw [hfindt]
  simp only [Option.bind_some]
  have Et := R.tsas.2.1 k_6_3 hkt
  have hsid := c159.symm.trans Et.name.2
  have hsr24 := ecdsaSigOf_bytes c128
  have hp384t := C3.Models.p384_model_closed _ _ _ _ _ _ _ _ _
    (svPvAt_frame (e1 := 0x420) (e2 := 0x190) (e3 := 0x1C0) (off_of_sep Et.keyIn.sep) (isrn_off RS)
      (by rw [sha256_length]; rfl) (sha256_lt _) (by decide) (by decide) (by decide) (.inr (by decide))
      (.inr (by decide)) (.inl (by decide))) c164 c165
  rw [svBytes_self hsr24.1.1 hsr24.1.2, svBytes_self hsr24.2.1 hsr24.2.2, Et.key] at hp384t
  have hB45 := derTlv_mem_bound (derOptRes_tlv c108)
  have hk45 : 1 ≤ tl45_6_1_3.header + tl45_6_1_3.len := by have := derTlv_header (derOptRes_tlv c108); omega
  have hk45' : tl45_6_1_3.header + tl45_6_1_3.len < 2 ^ 32 := by
    have := (BitVec.ofNat 32 tl13_6_1_3.len - BitVec.ofNat 32 (te25_6_1_3.header + te25_6_1_3.len) -
      BitVec.ofNat 32 (tl31_6_1_3.header + tl31_6_1_3.len) - BitVec.ofNat 32 (te39_6_1_3.header + te39_6_1_3.len)).isLt
    omega
  rw [sv_setTag SD0, dec1_toNat hk45 hk45'] at hp384t
  unfold verifyTimestamp
  simp only
  rw [hsid, beq_iff_eq.mpr rfl, c161, beq_iff_eq.mpr rfl, ← Bd.imageSignature.2, c162, c141,
    show memBytes Me vp45_1_4_3 (32 : Word).toNat = memBytes Me vp45_1_4_3 32 from rfl, beq_iff_eq.mpr rfl]
  rw [ofNat_toNat_lt hk45']
  obtain ⟨n45, hn45⟩ : ∃ n45, tl45_6_1_3.header + tl45_6_1_3.len = n45 + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero (by omega)).symm⟩
  rw [memBytes_dropK' Me _ hk45]
  rw [List.singleton_append] at hp384t
  rw [hp384t]
  rw [hn45, memBytes_succ]
  simp only [List.isEmpty_cons, Bool.not_false, Bool.and_self, require_true, Option.bind_some]
  have hN := (memLoad32 Me (reg n a1 + 0x1C)).isLt
  have b8 := nlScan_bound c166
  have b18 := nlScan_bound c167
  have b26 := nlScan_bound c168
  have b34 := nlScan_bound c169
  have h8 : ix8_1_1_4 < 2 ^ 32 := by omega
  have h18 : ix18_1_1_4 < 2 ^ 32 := by omega
  have h26 : ix26_1_1_4 < 2 ^ 32 := by omega
  have hs1 := splitLine_scan0 c166
  have hs2 := splitLine_scan0 c167
  have hs3 := splitLine_scan0 c168
  have hs4 := splitLine_scan0 c169
  have e34 : ix34_1_1_4 = 0 := by
    have := congrArg BitVec.toNat c170
    rw [ofNat_toNat_lt (by omega)] at this
    exact this
  subst e34
  have hS : (BitVec.ofNat 32 ((((memLoad32 Me (reg n a1 + 0x1C)).toNat - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) -
      (ix26_1_1_4 + 1)) - BitVec.ofNat 32 (0 + 1)).toNat =
      (((memLoad32 Me (reg n a1 + 0x1C)).toNat - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1) - (0 + 1) := by
    rw [BitVec.toNat_sub, ofNat_toNat_lt (by omega), ofNat_toNat_lt (by omega)]
    omega
  have hSpos : (((memLoad32 Me (reg n a1 + 0x1C)).toNat - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1) - (0 + 1) ≠ 0 :=
    fun e => c171 (BitVec.eq_of_toNat_eq (by rw [hS, e]; rfl))
  have hsl := c172.elim (fun h => h.2.1) (fun h => h.2.1)
  have hd := len19 h18 (c172.elim (fun h => h.2.2.2.1) (fun h => h.2.2.2))
  have hlead : 1 < ix18_1_1_4 → Me (memLoad32 Me (reg n a1 + 0x18) + BitVec.ofNat 32 (ix8_1_1_4 + 1)) ≠ 0x30 := by
    intro h1
    rcases c172 with h | h
    · exact h.2.2.2.2
    · exact absurd (by rw [ofNat_toNat_lt h18]; exact h1) h.1
  rw [ofNat_toNat_lt h18] at c173 c174
  have hck := ckd_fold (M := Me) ix18_1_1_4 (s' := (c'_2_4, p'_2_4, w64'_2_4, w74'_2_4))
    (s := (BitVec.ofNat 32 ix18_1_1_4, memLoad32 Me (reg n a1 + 0x18) + BitVec.ofNat 32 (ix8_1_1_4 + 1),
      BitVec.ofNat 32 0x0, BitVec.ofNat 32 0x0)) (fun i hi s1 e => c174 i hi _ _ _ _ e) c173
  dsimp only at hck
  have htree := treeSize_code hd.1 hd.2 hlead hck.1 hck.2 c175
  rw [ofNat_toNat_lt h26] at c176
  rw [ofNat_toNat_lt h8] at c179 c181 c183
  have lq : ∀ {i : Nat} {c q : Word}, (c, q) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0,
      s.2 + BitVec.ofNat 32 0x20)) i (BitVec.ofNat 32 0x200, reg n a2 + BitVec.ofNat 32 0x108) →
      q + 0x20 = reg n a2 + 0x128 + BitVec.ofNat 32 (0x20 * i) ∧ q + 0x24 = reg n a2 + 0x128 + BitVec.ofNat 32 (0x20 * i) + 4 ∧
      q + BitVec.ofNat 32 0x20 = reg n a2 + 0x128 + BitVec.ofNat 32 (0x20 * i) := by
    intro i c q h
    exact log_addr (svIter_ptr2 h)
  obtain ⟨la1, la2, la3⟩ := lq c180
  rw [la1, la2] at c181
  rw [la1] at c182
  obtain ⟨hkl, hfindl⟩ := find?_of_search (l := root.logs) (cap := 16) (k := k_3_4) (name := LogKey.origin)
    (nameAt := fun i => memBytes Me (memLoad32 Me (reg n a2 + 0x128 + BitVec.ofNat 32 (0x20 * i)))
      (memLoad32 Me (reg n a2 + 0x128 + BitVec.ofNat 32 (0x20 * i) + 4)).toNat)
    (used := fun i => memLoad32 Me (reg n a2 + 0x128 + BitVec.ofNat 32 (0x20 * i)) ≠ 0)
    (fun i h => (R.logs.2.1 i h).name.2) (fun i h1 h2 hne => hne (R.logs.2.2 i h1 h2)) c178 c182 c181
    (fun i hi e => by
      have h0 := c179 i hi _ _ rfl
      obtain ⟨g1, g2, -⟩ := lq (i := i) rfl
      rw [g1, g2] at h0
      exact h0 e)
  have Elg := R.logs.2.1 k_3_4 hkl
  rw [la3] at c183 c186
  subst c184
  obtain ⟨m', hm', -, hm1⟩ := cosig_chain (sv_sigPrefix OD) rfl (by rw [sha256_length]; decide) (sha256_lt _) k_5_4 c183
    (Nat.le_refl _) (fun _ => rfl) (fun h => absurd (by decide) h)
  have hm2 := hm1 c185
  subst hm2
  rw [hS, sv_newline OD, keyIdOne RK0, Elg.key, ofNat_toNat_lt h8] at hm'
  have hsg := checkpointSigs_sig _ hm' (fun s0 e => by cases e)
  have hlen := notAdd_toNat hsl
  rw [hS] at hlen
  have hed := svEdModel_sigMem RS (EdM.EdImage.ofCode LD PD UD PmD E1D EdD SmD D2D BsD)
    (EdK.KImage.ofCode KRD KRRD) sg'_5_4 _ _ _ _ c186
  rw [hlen, memBytes_sigMem_in Elg.keyIn (Nat.le_refl _), memBytes_sigMem_in Bd.checkpoint.1 (Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)),
    memBytes_sigMem_sig hsg.1 hsg.2, Elg.key] at hed
  rw [← Bd.checkpoint.2]
  unfold verifyCheckpoint
  rw [hs1]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [hs2]
  simp only [Option.bind_some]
  rw [hs3]
  simp only [Option.bind_some]
  rw [hs4]
  simp only [Option.bind_some]
  obtain ⟨nS, hnS⟩ : ∃ nS, (((memLoad32 Me (reg n a1 + 0x1C)).toNat - (ix8_1_1_4 + 1)) - (ix18_1_1_4 + 1)) -
      (ix26_1_1_4 + 1) - (0 + 1) = nS + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero hSpos).symm⟩
  have hsne : ∀ p, (!List.isEmpty (memBytes Me p ((((memLoad32 Me (reg n a1 + 0x1C)).toNat - (ix8_1_1_4 + 1)) -
      (ix18_1_1_4 + 1)) - (ix26_1_1_4 + 1) - (0 + 1)))) = true := fun p => by rw [hnS, memBytes_succ]; rfl
  have hz : ∀ p, memBytes Me p 0 = [] := fun _ => rfl
  have hkid : ∀ o pk : Bytes, logKeyId o pk = (sha256 (o ++ [0x0A] ++ [0x01] ++ pk)).take 4 := fun o pk => by
    unfold logKeyId; rw [List.append_assoc o [0x0A] [0x01]]; rfl
  rw [hz, hsne, List.isEmpty_nil, Bool.true_and, require_true]
  simp only [Option.bind_some]
  rw [memBytes_length, memBytes_length, memBytes_take' (Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)), htree]
  simp only [Option.bind_some]
  rw [c176]
  simp only [Option.bind_some]
  rw [c177, beq_iff_eq.mpr rfl, require_true]
  simp only [Option.bind_some]
  rw [hfindl]
  simp only [Option.bind_some]
  rw [hkid, hm']
  simp only [Option.bind_some]
  rw [hed, require_true]
  simp only [Option.bind_some]
  rw [Option.pure_def, Option.bind_some]
  have p1 : ({ log := root.logs[k_3_4]'hkl, size := pair64 w64'_2_4 w74'_2_4, root := bs7_2_4 } : Checkpoint).size =
    pair64 w64'_2_4 w74'_2_4 := rfl
  have p2 : ({ log := root.logs[k_3_4]'hkl, size := pair64 w64'_2_4 w74'_2_4, root := bs7_2_4 } : Checkpoint).root =
    bs7_2_4 := rfl
  have p3 : ({ log := root.logs[k_3_4]'hkl, size := pair64 w64'_2_4 w74'_2_4, root := bs7_2_4 } : Checkpoint).log =
    root.logs[k_3_4]'hkl := rfl
  rw [p1, p2, p3]
  have h2C : reg n a1 + 0x2C = reg n a1 + 0x28 + 4 := by rw [BitVec.add_assoc]; rfl
  have hli : pair64 (memLoad32 Me (reg n a1 + 0x28)) (memLoad32 Me (reg n a1 + 0x2C)) = bundle.logIndex := by
    rw [Bd.logIndex.2.1, h2C, Bd.logIndex.2.2]
    exact pair64_ofNat Bd.logIndex.1
  have hlt := win_lt c187
  rw [hli] at hlt
  rw [decide_eq_true hlt, require_true]
  simp only [Option.bind_some]
  rw [hli, RD.leaf', RD.pre', RD.mid1', RD.mid2', RD.post', Bd.leaf.2, Bd.inclusionProof.2] at c188
  have hrk : ∀ d sg c, rekorLeafHash d sg c = sha256 ([] ++ [0x00] ++ rekorPre ++ base64Encode d ++ rekorMid1 ++
      base64Encode sg ++ rekorMid2 ++ base64Encode c ++ rekorPost) := fun d sg c => by
    unfold rekorLeafHash leafHash rekorEntry
    simp only [List.nil_append, List.append_assoc, List.cons_append]
  rw [hrk, c188]
  simp only [Option.bind_some]
  have hr6 := rootFromInclusion_hash c188 (sha256_hash _)
  rw [b32_self hr6.1 hr6.2, b32_self c177 (base64Decode_lt c176)] at c189
  subst c189
  rw [beq_iff_eq.mpr rfl, require_true]
  simp only [Option.bind_some]
  have ht18 : tm18_2_4_3 < 2 ^ 64 := by have := generalizedTime_lt c147; omega
  have ht20 : tm20_4_1_1 < 2 ^ 64 := by have := readTime_lt c19; omega
  have ht28 : tm28_4_1_1 < 2 ^ 64 := by have := readTime_lt c20; omega
  have w1 := win_le c190
  rw [pair64_halves ht20, pair64_halves ht18] at w1
  have w2 := win_le c191
  rw [pair64_halves ht28, pair64_halves ht18] at w2
  obtain ⟨f1, f2, f3, f4⟩ := fulcio_win fa1
  rw [f1, f2] at c192
  rw [f3, f4] at c193
  have w3 := win_ge Ek.notBefore ht18 c192
  have w4 := win_le' Ek.notAfter ht18 c193
  obtain ⟨t1, t2, t3, t4⟩ := tsa_win ta1
  rw [t1, t2] at c194
  rw [t3, t4] at c195
  have w5 := win_ge Et.notBefore ht18 c194
  have w6 := win_le' Et.notAfter ht18 c195
  rw [la3] at c196 c197
  obtain ⟨l1, l2, l3, l4⟩ := log_win (reg n a2 + 0x128 + BitVec.ofNat 32 (0x20 * k_3_4))
  rw [l1, l2] at c196
  rw [l3, l4] at c197
  have w7 := win_ge Elg.notBefore ht18 c196
  have w8 := win_le' Elg.notAfter ht18 c197
  simp only [Window.contains, decide_eq_true w1, decide_eq_true w2, decide_eq_true w3, decide_eq_true w4,
    decide_eq_true w5, decide_eq_true w6, decide_eq_true w7, decide_eq_true w8, Bool.and_self, require_true,
    Option.bind_some]
  refine ⟨_, rfl, ?_⟩
  rw [Bd.logIndex.2.1, h2C, Bd.logIndex.2.2, ← ofNat_mod32 bundle.logIndex] at c198
  exact c198


/-- **`sigstore::verify` computes `sigstoreVerify`.** It returns `Err`, panics, or
returns `Ok` as `sv_verify_spec_pi` says. -/
theorem sv_verify_spec {Me : Word → BitVec 8} {n : Machine} {B : Word} {bundle : Bundle} {root : SigstoreRoot}
    (Bd : SvBundleAt B Me (reg n a1) bundle) (R : SvRootAt B Me (reg n a2) root)
    (C : CodeIn Me SV sigstoreVerifyCode)
    (E : SvCode Me)
    (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (s : St Me SV n 0 (reg n))
    (rsp : reg n sp = B + 0x2660)
    (hret : ((fun k => reg n (savedReg k))) 0 &&& ~~~1 = ((fun k => reg n (savedReg k))) 0)
    (hO : SvOut B (reg n a0))
    (D0 : P2Data Me)
    (SD0 : SvData Me)
    (HE0 : HfEnv Me)
    (RS : SvRoSep B)
    (PE0 : PvEnv7 Me)
    (PE0' : P2vEnv Me)
    (dg_in : SvIn B (reg n a3) 32)
    (S2 : SvSha2Code Me)
    (CK0 : SvCkCode Me)
    (EE0 : EvEnv Me)
    (hiv : (s5Hv Me (BitVec.ofNat 32 (img% sha512IVAddress))).toList = Sha512.h0)
    (RK0 : SvRkCode Me)
    (hOk : SvOutOk B (reg n a0))
    (OD : SvOidData Me)
    (ND : CodeIn Me (BitVec.ofNat 32 b2sOrder256Address) b2sOrder256Data)
    (UD : CodeIn Me (BitVec.ofNat 32 p256OneAddress) p256OneData)
    (LD : CodeIn Me (BitVec.ofNat 32 edOrderAddress) edOrderData)
    (PD : CodeIn Me (BitVec.ofNat 32 edPrimeAddress) edPrimeData)
    (PmD : CodeIn Me (BitVec.ofNat 32 edPm1Address) edPm1Data)
    (E1D : CodeIn Me (BitVec.ofNat 32 edOneAddress) edOneData)
    (EdD : CodeIn Me (BitVec.ofNat 32 edDAddress) edDData)
    (SmD : CodeIn Me (BitVec.ofNat 32 edSqrtM1Address) edSqrtM1Data)
    (D2D : CodeIn Me (BitVec.ofNat 32 edwardsD2Address) edwardsD2Data)
    (BsD : CodeIn Me (BitVec.ofNat 32 edBaseAddress) edBaseData)
    (KRD : CodeIn Me (BitVec.ofNat 32 edMontRAddress) edMontRData)
    (KRRD : CodeIn Me (BitVec.ofNat 32 edMontRRAddress) edMontRRData)
    (RD : SvRekorData Me) :
    SvErrRet B (reg n a0) (fun k => reg n (savedReg k)) n ∨ Panics n ∨
    ∃ v, sigstoreVerify bundle root (memBytes Me (reg n a3) 32) = some v ∧
      SvOkRet B (reg n a0) (fun k => reg n (savedReg k)) n (BitVec.ofNat 32 (v.signedTime % 2 ^ 32))
        (BitVec.ofNat 32 (v.signedTime / 2 ^ 32)) (BitVec.ofNat 32 (v.logIndex % 2 ^ 32))
        (BitVec.ofNat 32 (v.logIndex / 2 ^ 32)) :=
  (sv_verify_spec_pi Bd R C E FW s rsp hret hO D0 SD0 HE0 RS PE0 PE0' dg_in S2 CK0 EE0 hiv RK0 hOk OD ND UD LD PD
    PmD E1D EdD SmD D2D BsD KRD KRRD RD).imp_right (Or.imp_left PanicIf.panics)

end C3.RV32.Sv
