import C3BootProofs.Proofs.SvGsSpec
import C3BootProofs.Models.SafegcdP256
import C3BootProofs.Models.SafegcdP384
import C3BootProofs.Models.EcdsaClosed
import C3BootProofs.Models.P256Consts
import C3BootProofs.Proofs.SvPvWitness
import C3BootProofs.Proofs.SvEdImage

/-!
# `sigstore::verify` computes `sigstoreVerify`

`sv_verify_spec`: called with a `Bundle` and a `SigstoreRoot` laid out as
`SvBundleAt` and `SvRootAt` say, and the artifact's digest at `a3`, the
compiled `sigstore::verify` returns `Err`, panics, or returns `Ok` with the
time and log index of `sigstoreVerify bundle root digest`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Gd

theorem fulcio_addr {r q : Word} {i : Nat} (h : q = r + BitVec.ofNat 32 0x3C + BitVec.ofNat 32 (i * 0x20)) :
    q + 0xFFFFFFFC = r + 0x38 + BitVec.ofNat 32 (0x20 * i) ∧ q + 0x0 = r + 0x38 + BitVec.ofNat 32 (0x20 * i) + 4 ∧
      (q + BitVec.ofNat 32 0x20) + 0xFFFFFFF4 = r + 0x38 + BitVec.ofNat 32 (0x20 * i) + 0x18 := by
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

theorem tsa_addr {r q : Word} {i : Nat} (h : q = r + BitVec.ofNat 32 0x198 + BitVec.ofNat 32 (i * 0x20)) :
    q + 0x20 = r + 0x1B8 + BitVec.ofNat 32 (0x20 * i) ∧ q + 0x24 = r + 0x1B8 + BitVec.ofNat 32 (0x20 * i) + 4 ∧
      (q + BitVec.ofNat 32 0x20) + 0x18 = r + 0x1B8 + BitVec.ofNat 32 (0x20 * i) + 0x18 := by
  subst h
  rw [Nat.mul_comm i 0x20]
  refine ⟨?_, ?_, ?_⟩ <;> bv_omega

theorem dec1_toNat {k : Nat} (h1 : 1 ≤ k) (h2 : k < 2 ^ 32) : (BitVec.ofNat 32 k + BitVec.ofNat 32 0xFFFFFFFF).toNat = k - 1 := by
  rw [BitVec.toNat_add, ofNat_toNat_lt h2, ofNat_toNat_lt (by decide)]; omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
/-- **`sigstore::verify` computes `sigstoreVerify`.** -/
theorem sv_verify_spec {Me : Word → BitVec 8} {n : Machine} {B : Word} {bundle : Bundle} {root : SigstoreRoot}
    (Bd : SvBundleAt B Me (reg n a1) bundle) (R : SvRootAt B Me (reg n a2) root)
    (C : CodeIn Me SV sigstoreVerifyCode)
    (E : SvCode Me)
    (F : Fr B 0x3830)
    (s : St Me SV n 0 (reg n))
    (rsp : reg n sp = B + 0x3830)
    (hret : ((fun k => reg n (savedReg k))) 0 &&& ~~~1 = ((fun k => reg n (savedReg k))) 0)
    (hO : SvOut B (reg n a0))
    (D0 : P2Data Me)
    (SD0 : SvData Me)
    (SH0 : SvShaCode Me)
    (KS : SvKSep B)
    (PE0 : PvEnv7 Me)
    (EC0 : SvEcCode Me)
    (IC0 : SvIvCode Me)
    (UC0 : SvUpCode Me)
    (BG0 : BGEnv Me)
    (RS : SvRoSep B)
    (BY0 : BYEnv Me)
    (dg_in : SvIn B (reg n a3) 32)
    (UE0 : CodeIn Me (BitVec.ofNat 32 uint8EqAddress) uint8EqCode)
    (N80 : CodeIn Me (BitVec.ofNat 32 norm8Address) norm8Code)
    (PM0 : CodeIn Me (BitVec.ofNat 32 p256ScalarMulAddress) p256ScalarMulCode)
    (WM0 : CodeIn Me (BitVec.ofNat 32 wideMulAddress) wideMulCode)
    (PT0 : SvPtCode Me)
    (WN0 : SvWnCode Me)
    (ME : MlEnv Me)
    (P2C0 : P2Code Me)
    (GDC0 : C3.RV32.Gd.GdCode Me)
    (SC0 : CodeIn Me (BitVec.ofNat 32 p256ScalarCtEqAddress) p256ScalarCtEqCode)
    (hidC : CodeIn Me (BitVec.ofNat 32 p256IdentityAddress) p256IdentityData)
    (GD : CodeIn Me (BitVec.ofNat 32 p256GMontAddress) p256GMontData)
    (OD : CodeIn Me (BitVec.ofNat 32 p256MontOneAddress) p256MontOneData)
    (AD : CodeIn Me (BitVec.ofNat 32 p256AffineIdXAddress) p256AffineIdXData)
    (S2 : SvSha2Code Me)
    (KS' : SvK2Sep B)
    (CK0 : SvCkCode Me)
    (EE0 : EvEnv Me)
    (hiv : (s5Hv Me (BitVec.ofNat 32 0x3FCC4AF8)).toList = Sha512.h0)
    (RK0 : SvRkCode Me)
    (hOk : SvOutOk B (reg n a0))
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
        (BitVec.ofNat 32 (v.logIndex / 2 ^ 32)) := by
  rcases sv_verify_at Bd R C E F s rsp hret hO D0 SD0 SH0 KS PE0
    (fun _ _ _ _ _ _ M => C3.RV32.Safegcd.pvSide_holds M _ _ _ _ _) EC0 IC0 UC0 BG0 RS BY0 dg_in UE0 N80 PM0 WM0 PT0 WN0
    ME P2C0 GDC0 SC0 hidC GD OD AD (C3.RV32.Safegcd.hzi_holds D0) S2 KS'
    (fun _ _ _ _ _ _ M => C3.RV32.Safegcd.pvSide_holds M _ _ _ _ _) CK0 EE0 hiv RK0 hOk with e | p | hsc
  · exact .inl e
  · exact .inr (.inl p)
  refine .inr (.inr ?_)
  obtain ⟨t_1_1_1, c0, c1, tl1_2_1_1, c2, tl8_2_1_1, c3, tl16_2_1_1, c4, bp16_2_1_1, bl16_2_1_1, c5, hsc⟩ := hsc
  obtain ⟨c6, tl29_2_1_1, c7, c8, te43_2_1_1, c9, c10, tl2_3_1_1, c11, ip2_3_1_1, il2_3_1_1, c12, hsc⟩ := hsc
  obtain ⟨c13, tl9_3_1_1, c14, op19_3_1_1, ol19_3_1_1, c15, c16, tl6_4_1_1, c17, tl13_4_1_1, c18, tm22_4_1_1, hsc⟩ := hsc
  obtain ⟨rs22_4_1_1, c19, tm31_4_1_1, rs31_4_1_1, c20, c21, tl2_5_1_1, c22, tl6_5_1_1, c23, op15_5_1_1, ol15_5_1_1, hsc⟩ := hsc
  obtain ⟨prp15_5_1_1, pu15_5_1_1, c24, ta15_5_1_1, c25, c26, c27, c28, tl35_5_1_1, c29, bp35_5_1_1, bl35_5_1_1, hsc⟩ := hsc
  obtain ⟨c30, c31, c32, c33, c34, tl9_6_1_1, c35, c36, tl25_6_1_1, c37, c38, u0_1, hsc⟩ := hsc
  obtain ⟨u1_1, u2_1, k_2_1, f30'_2_1, f34'_2_1, rem'_2_1, cur'_2_1, sl0'_2_1, sl1'_2_1, sl2'_2_1, sl3'_2_1, sl4'_2_1, hsc⟩ := hsc
  obtain ⟨sl5'_2_1, sl6'_2_1, sl7'_2_1, sl8'_2_1, sl9'_2_1, c39, c40, c41, c42, c43, c44, c45, hsc⟩ := hsc
  obtain ⟨c46, c47, c48, c49, c50, c51, sr43_2_1, ss43_2_1, c52, k_4_1, c53, c54, hsc⟩ := hsc
  obtain ⟨c'_4_1, q'_4_1, c55, c56, c57, pv_5_1, c58, c59, c60, c61, c62, c63, hsc⟩ := hsc
  obtain ⟨c64, tl49_1_6_1, c65, c66, bs9_2_6_1, c67, te9_2_6_1, c68, bs16_2_6_1, c69, te16_2_6_1, c70, hsc⟩ := hsc
  obtain ⟨c71, c72, σd_2, σf_2, Dv_2, Fv_2, c73, c74, c75, c76, c77, stm_2, hsc⟩ := hsc
  obtain ⟨c78, τd_2, τf_2, Dz_2, Fz_2, c79, c80, c81, c82, c83, tl10_1_1_3, c84, hsc⟩ := hsc
  obtain ⟨c85, tl22_1_1_3, c86, c87, te33_1_1_3, c88, c89, tl41_1_1_3, c90, c91, op53_1_1_3, ol53_1_1_3, hsc⟩ := hsc
  obtain ⟨c92, to53_1_1_3, c93, c94, tl2_2_1_3, c95, c96, tl15_2_1_3, c97, c98, c99, te26_2_1_3, hsc⟩ := hsc
  obtain ⟨c100, tl32_2_1_3, c101, c102, te41_2_1_3, c103, c104, tl49_2_1_3, c105, op58_2_1_3, ol58_2_1_3, c106, hsc⟩ := hsc
  obtain ⟨to58_2_1_3, c107, c108, tl2_3_1_3, c109, c110, vp23_3_1_3, vl23_3_1_3, c111, te23_3_1_3, c112, c113, hsc⟩ := hsc
  obtain ⟨tsa4_w2a8_4_1_3, tsa4_w2ac_4_1_3, c114, c115, tl2_5_1_3, c116, c117, tl13_5_1_3, c118, c119, c120, te25_5_1_3, hsc⟩ := hsc
  obtain ⟨c121, tl31_5_1_3, c122, c123, te39_5_1_3, c124, tl45_5_1_3, c125, c126, c127, tl6_1_2_3, c128, hsc⟩ := hsc
  obtain ⟨op15_1_2_3, ol15_1_2_3, c129, to15_1_2_3, c130, tl20_1_2_3, c131, c132, c133, tsav_r24_2_2_3, tsav_w78_2_2_3, tsav_w1388_2_2_3, hsc⟩ := hsc
  obtain ⟨tsav_w138c_2_2_3, c134, c135, c136, u0, u1, u2, u3, u4, u5, u6, u7, hsc⟩ := hsc
  obtain ⟨u8, u9, u10, u11, u12, u13, u14, u15, u16, u17, u18, u19, hsc⟩ := hsc
  obtain ⟨u20, u21, u22, u23, u24, u25, u26, u27, u28, u29, u30, u31, hsc⟩ := hsc
  obtain ⟨k_3_3, dg'_3_3, flag'_3_3, cp'_3_3, rem'_3_3, c137, c138, c139, c140, op8_3_3, ol8_3_3, c141, hsc⟩ := hsc
  obtain ⟨te8_3_3, c142, c143, vp19_3_3, vl19_3_3, c144, te19_3_3, c145, sr24_3_3, ss24_3_3, c146, c147, hsc⟩ := hsc
  obtain ⟨tl13_1_4_3, c148, c149, c150, te26_1_4_3, c151, op32_1_4_3, ol32_1_4_3, c152, to32_1_4_3, c153, tl36_1_4_3, hsc⟩ := hsc
  obtain ⟨c154, c155, te45_1_4_3, c156, vp51_1_4_3, vl51_1_4_3, c157, te51_1_4_3, c158, c159, c160, tl2_2_4_3, hsc⟩ := hsc
  obtain ⟨c161, ip2_2_4_3, il2_2_4_3, c162, c163, tl13_2_4_3, c164, tm18_2_4_3, c165, tst3_w1328_3_4_3, tst3_w132c_3_4_3, c166, hsc⟩ := hsc
  obtain ⟨c167, tst4_r8_4_4_3, tst4_w1328_4_4_3, tst4_w132c_4_4_3, c168, c169, tst5_w1328_5_4_3, tst5_w132c_5_4_3, c170, c171, tst6_w1328_6_4_3, tst6_w132c_6_4_3, hsc⟩ := hsc
  obtain ⟨c172, c173, k_5_3, c174, c175, c'_5_3, q'_5_3, c176, c177, c178, c179, c180, hsc⟩ := hsc
  obtain ⟨c181, pv_7_3, c182, c183, ix7_1_1_4, c184, ix17_1_1_4, c185, ix25_1_1_4, c186, ix33_1_1_4, c187, hsc⟩ := hsc
  obtain ⟨c188, c189, c190, c'_2_4, p'_2_4, x21'_2_4, w60'_2_4, w70'_2_4, c191, c192, c193, bs7_2_4, hsc⟩ := hsc
  obtain ⟨c194, c195, k_3_4, c196, c197, c'_3_4, q'_3_4, w80'_3_4, c198, c199, c200, u32, hsc⟩ := hsc
  obtain ⟨u33, u34, u35, u36, u37, u38, u39, u40, u41, u42, u43, u44, hsc⟩ := hsc
  obtain ⟨u45, u46, u47, u48, u49, u50, u51, u52, u53, u54, u55, u56, hsc⟩ := hsc
  obtain ⟨u57, u58, u59, u60, sg_5_4, k_5_4, c'_5_4, x21'_5_4, rl'_5_4, rp'_5_4, dg'_5_4, w8'_5_4, hsc⟩ := hsc
  obtain ⟨wc'_5_4, w28'_5_4, w2c'_5_4, w30'_5_4, w38'_5_4, w40'_5_4, w5c'_5_4, sg'_5_4, c201, c202, c203, c204, hsc⟩ := hsc
  obtain ⟨c205, root6_3_6_4, c206, c207, c208, c209, c210, c211, c212, c213, c214, c215, hsc⟩ := hsc
  have c216 := hsc
  subst c40
  have hext := readExtensions_code (sv_extConsts SD0) c37 c38 c39 c46 c47 c48 c49 c50
  have hleaf := parseLeaf_code c0 c1 rfl rfl c2 rfl rfl c3 rfl rfl c4 c5 c6 rfl rfl c7 rfl rfl c8 c9 c10 rfl rfl c11 c12
    c13 rfl rfl c14 c15 (c16.trans (sv_ecdsa384 SD0)) rfl rfl c17 rfl rfl c18 c19 c20 c21 rfl rfl c22 rfl rfl c23 rfl rfl
    c24 c25 c26 (c27.trans (sv_prime256 SD0)) (c28.trans (sv_ecpub SD0)) c29 c30 c31 c32 (gsModel _ c33 c34) rfl rfl c35 c36
    hext c51 c52
  rw [Bd.leaf.2] at hleaf
  have fq : ∀ {i : Nat} {c q : Word}, (c, q) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i
      (BitVec.ofNat 32 0x80, reg n a2 + BitVec.ofNat 32 0x3C) →
      q + 0xFFFFFFFC = reg n a2 + 0x38 + BitVec.ofNat 32 (0x20 * i) ∧ q + 0x0 = reg n a2 + 0x38 + BitVec.ofNat 32 (0x20 * i) + 4 ∧
      (q + BitVec.ofNat 32 0x20) + 0xFFFFFFF4 = reg n a2 + 0x38 + BitVec.ofNat 32 (0x20 * i) + 0x18 := by
    intro i c q h
    have hy := svIter_ptr2 h
    exact fulcio_addr hy
  obtain ⟨fa1, fa2, fa3⟩ := fq c55
  rw [fa1, fa2] at c56
  rw [fa1] at c57
  rw [fa3] at c58
  obtain ⟨hkf, hfind⟩ := find?_of_search (l := root.fulcio) (cap := 4) (k := k_4_1) (name := FulcioKey.subject)
    (nameAt := fun i => memBytes Me (memLoad32 Me (reg n a2 + 0x38 + BitVec.ofNat 32 (0x20 * i)))
      (memLoad32 Me (reg n a2 + 0x38 + BitVec.ofNat 32 (0x20 * i) + 4)).toNat)
    (used := fun i => memLoad32 Me (reg n a2 + 0x38 + BitVec.ofNat 32 (0x20 * i)) ≠ 0)
    (fun i h => (R.fulcio.2.1 i h).name.2) (fun i h1 h2 hne => hne (R.fulcio.2.2 i h1 h2)) c53 c57 c56
    (fun i hi e => by
      have h0 := c54 i hi _ _ rfl
      obtain ⟨g1, g2, -⟩ := fq (i := i) rfl
      rw [g1, g2] at h0
      exact h0 e)
  have Ek := R.fulcio.2.1 k_4_1 hkf
  have hiss := c56.symm.trans Ek.name.2
  have hsr43 := ecdsaSigOf_bytes c52
  have hp384 := C3.Models.p384_model_closed _ _ _ _ _ _ _ _ _
    (svPvAt_frame (e1 := 0x1020) (e2 := 0xD0) (e3 := 0x100) (off_of_sep Ek.keyIn.sep) (isrn_off RS)
      (by rw [sha384_length]; rfl) (sha384_lt _) (by decide) (by decide) (by decide) (.inr (by decide))
      (.inr (by decide)) (.inl (by decide))) c58 c59
  rw [svBytes_self hsr43.1.1 hsr43.1.2, svBytes_self hsr43.2.1 hsr43.2.2, Ek.key] at hp384
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
  have hsig := ecdsaSignature32_code c65 c66 rfl rfl c67 c68 rfl rfl c69 c70 c71
  rw [Bd.imageSignature.2] at hsig
  rw [hsig]
  simp only [Option.bind_some]
  have hp256 := C3.Models.p256_model_closed (C3.Models.P256Consts.of D0 ND UD GD OD AD) _ _ _ _
    ⟨c72, σd_2, σf_2, Dv_2, Fv_2, c73, c74, c75, c76, c77, stm_2, c78, τd_2, τf_2, Dz_2, Fz_2, c79, c80, c81, c82, c83⟩
  have hr9 := derScalarOf_bytes memBytes_mem_lt c67
  have hs16 := derScalarOf_bytes memBytes_mem_lt c69
  rw [b32_self hr9.1 hr9.2, b32_self hs16.1 hs16.2] at hp256
  rw [c31, show (BitVec.ofNat 32 0x41).toNat = 65 from rfl, hp256, require_true]
  simp only [Option.bind_some]
  subst c138
  have hsa := readSignedAttributes_code (B := B) (sv_contentType SD0) (sv_tstInfo SD0) (sv_messageDigest SD0)
    (svChain.cons ⟨c126, c127, tl6_1_2_3, c128, op15_1_2_3, ol15_1_2_3, c129, to15_1_2_3, c130, tl20_1_2_3, c131, c132,
      c133, tsav_r24_2_2_3, tsav_w78_2_2_3, tsav_w1388_2_2_3, tsav_w138c_2_2_3, c134, c135, c136, rfl⟩ c137)
    c140.1 c140.2
  have htst := readTstInfo_code c148 c149 rfl rfl c150 c151 rfl rfl c152 c153 rfl rfl c154 rfl rfl c155 c156 c157 c158 c159
    c160 rfl rfl c161 c162 c163 rfl rfl c164 c165 (optional_code c166) c168 (optional_code c170) (optional_last_code c172)
  have hts := parseTimestamp_code (sv_signedData SD0) (sv_tstInfo SD0) (sv_ecdsa256 SD0) c84 c85 rfl rfl c86 rfl rfl c87 c88
    c89 rfl rfl c90 c91 rfl rfl c92 c93 c94 rfl rfl c95 c96 rfl rfl c97 c98 rfl rfl c99 c100 rfl rfl c101 c102 c103 c104
    rfl rfl c105 rfl rfl c106 c107 c108 rfl rfl c109 c110 rfl rfl c111 c112 c113 rfl rfl (tsa4_code c114) c116 c117 rfl rfl
    c118 c119 rfl rfl c120 c121 rfl rfl c122 c123 c124 rfl rfl c125 hsa rfl rfl c141 c142 c143 rfl rfl c144 c145 c146 c147
    htst
  rw [Bd.timestamp.2] at hts
  rw [hts]
  simp only [Option.bind_some]
  have tq : ∀ {i : Nat} {c q : Word}, (c, q) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0, s.2 + BitVec.ofNat 32 0x20)) i
      (BitVec.ofNat 32 0x80, reg n a2 + BitVec.ofNat 32 0x198) →
      q + 0x20 = reg n a2 + 0x1B8 + BitVec.ofNat 32 (0x20 * i) ∧ q + 0x24 = reg n a2 + 0x1B8 + BitVec.ofNat 32 (0x20 * i) + 4 ∧
      (q + BitVec.ofNat 32 0x20) + 0x18 = reg n a2 + 0x1B8 + BitVec.ofNat 32 (0x20 * i) + 0x18 := by
    intro i c q h
    exact tsa_addr (svIter_ptr2 h)
  obtain ⟨ta1, ta2, ta3⟩ := tq c176
  rw [ta1, ta2] at c177
  rw [ta1] at c178
  rw [ta3] at c182
  obtain ⟨hkt, hfindt⟩ := find?_of_search (l := root.tsas) (cap := 4) (k := k_5_3) (name := TsaKey.signerId)
    (nameAt := fun i => memBytes Me (memLoad32 Me (reg n a2 + 0x1B8 + BitVec.ofNat 32 (0x20 * i)))
      (memLoad32 Me (reg n a2 + 0x1B8 + BitVec.ofNat 32 (0x20 * i) + 4)).toNat)
    (used := fun i => memLoad32 Me (reg n a2 + 0x1B8 + BitVec.ofNat 32 (0x20 * i)) ≠ 0)
    (fun i h => (R.tsas.2.1 i h).name.2) (fun i h1 h2 hne => hne (R.tsas.2.2 i h1 h2)) c174 c178 c177
    (fun i hi e => by
      have h0 := c175 i hi _ _ rfl
      obtain ⟨g1, g2, -⟩ := tq (i := i) rfl
      rw [g1, g2] at h0
      exact h0 e)
  rw [hfindt]
  simp only [Option.bind_some]
  have Et := R.tsas.2.1 k_5_3 hkt
  have hsid := c177.symm.trans Et.name.2
  have hsr24 := ecdsaSigOf_bytes c146
  have hp384t := C3.Models.p384_model_closed _ _ _ _ _ _ _ _ _
    (svPvAt_frame (e1 := 0x420) (e2 := 0xA40) (e3 := 0xA70) (off_of_sep Et.keyIn.sep) (isrn_off RS)
      (by rw [sha256_length]; rfl) (sha256_lt _) (by decide) (by decide) (by decide) (.inl (by decide))
      (.inl (by decide)) (.inl (by decide))) c182 c183
  rw [svBytes_self hsr24.1.1 hsr24.1.2, svBytes_self hsr24.2.1 hsr24.2.2, Et.key] at hp384t
  have hB45 := derTlv_mem_bound (derOptRes_tlv c125)
  have hk45 : 1 ≤ tl45_5_1_3.header + tl45_5_1_3.len := by have := derTlv_header (derOptRes_tlv c125); omega
  have hk45' : tl45_5_1_3.header + tl45_5_1_3.len < 2 ^ 32 := by
    have := (BitVec.ofNat 32 tl13_5_1_3.len - BitVec.ofNat 32 (te25_5_1_3.header + te25_5_1_3.len) -
      BitVec.ofNat 32 (tl31_5_1_3.header + tl31_5_1_3.len) - BitVec.ofNat 32 (te39_5_1_3.header + te39_5_1_3.len)).isLt
    omega
  rw [sv_setTag SD0, dec1_toNat hk45 hk45'] at hp384t
  unfold verifyTimestamp
  simp only
  rw [hsid, beq_iff_eq.mpr rfl, c179, beq_iff_eq.mpr rfl, ← Bd.imageSignature.2, c180, c159,
    show memBytes Me vp51_1_4_3 (32 : Word).toNat = memBytes Me vp51_1_4_3 32 from rfl, beq_iff_eq.mpr rfl]
  rw [ofNat_toNat_lt hk45']
  obtain ⟨n45, hn45⟩ : ∃ n45, tl45_5_1_3.header + tl45_5_1_3.len = n45 + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero (by omega)).symm⟩
  rw [memBytes_dropK' Me _ hk45]
  rw [List.singleton_append] at hp384t
  rw [hp384t]
  rw [hn45, memBytes_succ]
  simp only [List.isEmpty_cons, Bool.not_false, Bool.and_self, require_true, Option.bind_some]
  have hN := (memLoad32 Me (reg n a1 + 0x1C)).isLt
  have b7 := nlScan_bound c184
  have b17 := nlScan_bound c185
  have b25 := nlScan_bound c186
  have b33 := nlScan_bound c187
  have h7 : ix7_1_1_4 < 2 ^ 32 := by omega
  have h17 : ix17_1_1_4 < 2 ^ 32 := by omega
  have h25 : ix25_1_1_4 < 2 ^ 32 := by omega
  have hs1 := splitLine_scan0 c184
  have hs2 := splitLine_scan0 c185
  have hs3 := splitLine_scan0 c186
  have hs4 := splitLine_scan0 c187
  have e33 : ix33_1_1_4 = 0 := by
    have := congrArg BitVec.toNat c188
    rw [ofNat_toNat_lt (by omega)] at this
    exact this
  subst e33
  have hS : (BitVec.ofNat 32 ((((memLoad32 Me (reg n a1 + 0x1C)).toNat - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) -
      (ix25_1_1_4 + 1)) - BitVec.ofNat 32 (0 + 1)).toNat =
      (((memLoad32 Me (reg n a1 + 0x1C)).toNat - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1) - (0 + 1) := by
    rw [BitVec.toNat_sub, ofNat_toNat_lt (by omega), ofNat_toNat_lt (by omega)]
    omega
  have hSpos : (((memLoad32 Me (reg n a1 + 0x1C)).toNat - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1) - (0 + 1) ≠ 0 :=
    fun e => c189 (BitVec.eq_of_toNat_eq (by rw [hS, e]; rfl))
  have hsl := c190.elim (fun h => h.2.1) (fun h => h.2.1)
  have hd := len19 h17 (c190.elim (fun h => h.2.2.2.1) (fun h => h.2.2.2))
  have hlead : 1 < ix17_1_1_4 → Me (memLoad32 Me (reg n a1 + 0x18) + BitVec.ofNat 32 (ix7_1_1_4 + 1)) ≠ 0x30 := by
    intro h1
    rcases c190 with h | h
    · exact h.2.2.2.2
    · exact absurd (by rw [ofNat_toNat_lt h17]; exact h1) h.1
  rw [ofNat_toNat_lt h17] at c191 c192
  have hck := ckd_fold (M := Me) ix17_1_1_4 (s' := (c'_2_4, p'_2_4, x21'_2_4, w60'_2_4, w70'_2_4))
    (s := (BitVec.ofNat 32 ix17_1_1_4, memLoad32 Me (reg n a1 + 0x18) + BitVec.ofNat 32 (ix7_1_1_4 + 1), vl23_3_1_3,
      BitVec.ofNat 32 0x0, BitVec.ofNat 32 0x0)) (fun i hi s1 e => c192 i hi _ _ _ _ _ e) c191
  dsimp only at hck
  have htree := treeSize_code hd.1 hd.2 hlead hck.1 hck.2 c193
  rw [ofNat_toNat_lt h25] at c194
  rw [ofNat_toNat_lt h7] at c197 c199 c201
  have lq : ∀ {i : Nat} {c q w : Word}, (c, q, w) = svIter (fun s => (s.1 + BitVec.ofNat 32 0xFFFFFFE0,
      s.2.1 + BitVec.ofNat 32 0x20, memLoad32 Me (s.2.1 + 0x20))) i (BitVec.ofNat 32 0x100, reg n a2 + BitVec.ofNat 32 0x98, reg n a2) →
      q + 0x20 = reg n a2 + 0xB8 + BitVec.ofNat 32 (0x20 * i) ∧ q + 0x24 = reg n a2 + 0xB8 + BitVec.ofNat 32 (0x20 * i) + 4 ∧
      q + BitVec.ofNat 32 0x20 = reg n a2 + 0xB8 + BitVec.ofNat 32 (0x20 * i) := by
    intro i c q w h
    exact log_addr (svIter_ptr3 h)
  obtain ⟨la1, la2, la3⟩ := lq c198
  rw [la1, la2] at c199
  rw [la1] at c200
  obtain ⟨hkl, hfindl⟩ := find?_of_search (l := root.logs) (cap := 8) (k := k_3_4) (name := LogKey.origin)
    (nameAt := fun i => memBytes Me (memLoad32 Me (reg n a2 + 0xB8 + BitVec.ofNat 32 (0x20 * i)))
      (memLoad32 Me (reg n a2 + 0xB8 + BitVec.ofNat 32 (0x20 * i) + 4)).toNat)
    (used := fun i => memLoad32 Me (reg n a2 + 0xB8 + BitVec.ofNat 32 (0x20 * i)) ≠ 0)
    (fun i h => (R.logs.2.1 i h).name.2) (fun i h1 h2 hne => hne (R.logs.2.2 i h1 h2)) c196 c200 c199
    (fun i hi e => by
      have h0 := c197 i hi _ _ _ rfl
      obtain ⟨g1, g2, -⟩ := lq (i := i) rfl
      rw [g1, g2] at h0
      exact h0 e)
  have Elg := R.logs.2.1 k_3_4 hkl
  rw [la3] at c201 c204
  subst c202
  obtain ⟨m', hm', -, hm1⟩ := cosig_chain (sv_sigPrefix SD0) rfl (by rw [sha256_length]; decide) (sha256_lt _) k_5_4 c201
    (Nat.le_refl _) (fun _ => rfl) (fun h => absurd (by decide) h)
  have hm2 := hm1 c203
  subst hm2
  rw [hS, sv_newline SD0, keyIdOne RK0, Elg.key, ofNat_toNat_lt h7] at hm'
  have hsg := checkpointSigs_sig _ hm' (fun s0 e => by cases e)
  have hlen := notAdd_toNat hsl
  rw [hS] at hlen
  have hed := svEdModel_sigMem RS (EdM.EdImage.ofCode LD PD UD PmD E1D EdD SmD D2D BsD)
    (EdK.KImage.ofCode KRD KRRD) sg'_5_4 _ _ _ _ c204
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
  obtain ⟨nS, hnS⟩ : ∃ nS, (((memLoad32 Me (reg n a1 + 0x1C)).toNat - (ix7_1_1_4 + 1)) - (ix17_1_1_4 + 1)) -
      (ix25_1_1_4 + 1) - (0 + 1) = nS + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero hSpos).symm⟩
  have hsne : ∀ p, (!List.isEmpty (memBytes Me p ((((memLoad32 Me (reg n a1 + 0x1C)).toNat - (ix7_1_1_4 + 1)) -
      (ix17_1_1_4 + 1)) - (ix25_1_1_4 + 1) - (0 + 1)))) = true := fun p => by rw [hnS, memBytes_succ]; rfl
  have hz : ∀ p, memBytes Me p 0 = [] := fun _ => rfl
  have hkid : ∀ o pk : Bytes, logKeyId o pk = (sha256 (o ++ [0x0A] ++ [0x01] ++ pk)).take 4 := fun o pk => by
    unfold logKeyId; rw [List.append_assoc o [0x0A] [0x01]]; rfl
  rw [hz, hsne, List.isEmpty_nil, Bool.true_and, require_true]
  simp only [Option.bind_some]
  rw [memBytes_length, memBytes_length, memBytes_take' (Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)), htree]
  simp only [Option.bind_some]
  rw [c194]
  simp only [Option.bind_some]
  rw [c195, beq_iff_eq.mpr rfl, require_true]
  simp only [Option.bind_some]
  rw [hfindl]
  simp only [Option.bind_some]
  rw [hkid, hm']
  simp only [Option.bind_some]
  rw [hed, require_true]
  simp only [Option.bind_some]
  rw [Option.pure_def, Option.bind_some]
  have p1 : ({ log := root.logs[k_3_4]'hkl, size := pair64 w60'_2_4 w70'_2_4, root := bs7_2_4 } : Checkpoint).size =
    pair64 w60'_2_4 w70'_2_4 := rfl
  have p2 : ({ log := root.logs[k_3_4]'hkl, size := pair64 w60'_2_4 w70'_2_4, root := bs7_2_4 } : Checkpoint).root =
    bs7_2_4 := rfl
  have p3 : ({ log := root.logs[k_3_4]'hkl, size := pair64 w60'_2_4 w70'_2_4, root := bs7_2_4 } : Checkpoint).log =
    root.logs[k_3_4]'hkl := rfl
  rw [p1, p2, p3]
  have h2C : reg n a1 + 0x2C = reg n a1 + 0x28 + 4 := by rw [BitVec.add_assoc]; rfl
  have hli : pair64 (memLoad32 Me (reg n a1 + 0x28)) (memLoad32 Me (reg n a1 + 0x2C)) = bundle.logIndex := by
    rw [Bd.logIndex.2.1, h2C, Bd.logIndex.2.2]
    exact pair64_ofNat Bd.logIndex.1
  have hlt := win_lt c205
  rw [hli] at hlt
  rw [decide_eq_true hlt, require_true]
  simp only [Option.bind_some]
  rw [hli, RD.leaf', RD.pre', RD.mid1', RD.mid2', RD.post', Bd.leaf.2, Bd.inclusionProof.2] at c206
  have hrk : ∀ d sg c, rekorLeafHash d sg c = sha256 ([] ++ [0x00] ++ rekorPre ++ base64Encode d ++ rekorMid1 ++
      base64Encode sg ++ rekorMid2 ++ base64Encode c ++ rekorPost) := fun d sg c => by
    unfold rekorLeafHash leafHash rekorEntry
    simp only [List.nil_append, List.append_assoc, List.cons_append]
  rw [hrk, c206]
  simp only [Option.bind_some]
  have hr6 := rootFromInclusion_hash c206 (sha256_hash _)
  rw [b32_self hr6.1 hr6.2, b32_self c195 (base64Decode_lt c194)] at c207
  subst c207
  rw [beq_iff_eq.mpr rfl, require_true]
  simp only [Option.bind_some]
  have ht18 : tm18_2_4_3 < 2 ^ 64 := by have := generalizedTime_lt c165; omega
  have ht22 : tm22_4_1_1 < 2 ^ 64 := by have := readTime_lt c19; omega
  have ht31 : tm31_4_1_1 < 2 ^ 64 := by have := readTime_lt c20; omega
  have w1 := win_le c208
  rw [pair64_halves ht22, pair64_halves ht18] at w1
  have w2 := win_le c209
  rw [pair64_halves ht31, pair64_halves ht18] at w2
  obtain ⟨f1, f2, f3, f4⟩ := fulcio_win fa1
  rw [f1, f2] at c210
  rw [f3, f4] at c211
  have w3 := win_ge Ek.notBefore ht18 c210
  have w4 := win_le' Ek.notAfter ht18 c211
  obtain ⟨t1, t2, t3, t4⟩ := tsa_win ta1
  rw [t1, t2] at c212
  rw [t3, t4] at c213
  have w5 := win_ge Et.notBefore ht18 c212
  have w6 := win_le' Et.notAfter ht18 c213
  rw [la3] at c214 c215
  obtain ⟨l1, l2, l3, l4⟩ := log_win (reg n a2 + 0xB8 + BitVec.ofNat 32 (0x20 * k_3_4))
  rw [l1, l2] at c214
  rw [l3, l4] at c215
  have w7 := win_ge Elg.notBefore ht18 c214
  have w8 := win_le' Elg.notAfter ht18 c215
  simp only [Window.contains, decide_eq_true w1, decide_eq_true w2, decide_eq_true w3, decide_eq_true w4,
    decide_eq_true w5, decide_eq_true w6, decide_eq_true w7, decide_eq_true w8, Bool.and_self, require_true,
    Option.bind_some]
  refine ⟨_, rfl, ?_⟩
  rw [Bd.logIndex.2.1, h2C, Bd.logIndex.2.2, ← ofNat_mod32 bundle.logIndex] at c216
  exact c216

end C3.RV32.Sv
