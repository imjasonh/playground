import C3BootProofs.Proofs.P2vP256A
import C3BootProofs.Proofs.P2vP256Np
import C3BootProofs.Proofs.P2vZE
import C3BootProofs.Models.SafegcdP256

/-!
# `p256VerifyPrehash`

The stages composed, from the entry to the return: the range checks and key
decode, the inversion of `s` (`ivLoop8`), the tables and wNAF digits, the
main loop (`mlMain2`), the inversion of the sum's `Z` (`zvLoop`), and the
comparison with `r`. The function returns 1 only when `SvP256Facts` holds,
returns 0 otherwise, or panics.

It panics only when the inversion of `s` leaves `|f| ≠ 1`
(`p256VerifyPrehash_correct_bound`), so given safegcd's divstep bound
(`P256InvBound`) it doesn't panic (`p256VerifyPrehash_correct_np`).
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Gd

/-- What the success condition says the P-256 check computed for the key at
`bp`, the digest at `dg`, and the scalars `r` and `s`. -/
def SvP256Facts (M : Word → BitVec 8) (bp dg : Word) (r s : Bytes) : Prop :=
  (((inScalarRange (b32 r) (memBytes M (BitVec.ofNat 32 (img% p256OrderBeAddress)) 32) = true) ∧ (inScalarRange (b32 s) (memBytes M (BitVec.ofNat 32 (img% p256OrderBeAddress)) 32) = true) ∧ (M bp = 4) ∧ True) ∧ ((GsOk M bp) ∧ (beNat (b32 r) < C3.p256.n) ∧ (beNat (b32 s) < C3.p256.n) ∧ (beNat (b32 r) ≠ 0) ∧ (beNat (b32 s) ≠ 0) ∧ True)) ∧ ∃ σd_2 σf_2 Dv_2 Fv_2, σd_2 ≤ 1 ∧ σf_2 ≤ 1 ∧ sgnVal σf_2 Fv_2 = (p256Sf M s).f ∧ sgnVal σd_2 Dv_2 = (p256Sf M s).d ∧ (((Fv_2 = accV M (BitVec.ofNat 32 (img% p256OneAddress)) 8)) ∧ True) ∧ ∃ stm_2, mlMain2 (tbl2 (accV M (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8, accV M (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8, accV M (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8)) (tbl2 ((gsVal M bp 1 * 2 ^ 256 % p256), (gsVal M bp 0x21 * 2 ^ 256 % p256), (accV M (BitVec.ofNat 32 (img% p256MontOneAddress)) 8))) (wnafBytes (wnafGo ((psmVal (((beNat (memBytes M (dg) 32) % C3.p256.n)) * ((normVal8 σd_2 σf_2 Dv_2 (accV M (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0) 0x101) (wnafBytes (wnafGo ((psmVal (((beNat (b32 r))) * ((normVal8 σd_2 σf_2 Dv_2 (accV M (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0) 0x101) (max (wnafGo ((psmVal (((beNat (memBytes M (dg) 32) % C3.p256.n)) * ((normVal8 σd_2 σf_2 Dv_2 (accV M (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0).length (wnafGo ((psmVal (((beNat (b32 r))) * ((normVal8 σd_2 σf_2 Dv_2 (accV M (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0).length) = some stm_2 ∧ ∃ τd_2 τf_2 Dz_2 Fz_2, τd_2 ≤ 1 ∧ τf_2 ≤ 1 ∧ sgnVal τf_2 Fz_2 = (p256Sz M stm_2.1.2.2).f ∧ sgnVal τd_2 Dz_2 = (p256Sz M stm_2.1.2.2).d ∧ ((((beNat (b32 r)) = (p2fm ((if (((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV M (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm ((stm_2.1.1)) ((if ((((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV M (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV M (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV M (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 τd_2 τf_2 Dz_2 (accV M (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) else 0) else 0) else 0)) else accV M (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8)) 1) % C3.p256.n)) ∧ True)

end C3.RV32.Sv

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Sv C3.RV32.Gd

set_option maxRecDepth 100000

/-- The code and constants that `p256VerifyPrehash` and its callees read. -/
structure P2vEnv (M : Word → BitVec 8) : Prop where
  ME : MlEnv M
  EC : P2vEcCode M
  IC : P2vIvCode M
  UC : P2vUpCode M
  D : P2Data M
  BG : BGEnv M
  BY : BYEnv M
  UE : CodeIn M (BitVec.ofNat 32 uint8EqAddress) uint8EqCode
  N8 : CodeIn M (BitVec.ofNat 32 norm8Address) norm8Code
  PM : CodeIn M (BitVec.ofNat 32 p256ScalarMulAddress) p256ScalarMulCode
  WM : CodeIn M (BitVec.ofNat 32 wideMulAddress) wideMulCode
  PT : P2vPtCode M
  WN : P2vWnCode M
  P2C : P2Code M
  GDC : GdCode M
  SC : CodeIn M (BitVec.ofNat 32 p256ScalarCtEqAddress) p256ScalarCtEqCode
  hid : CodeIn M (BitVec.ofNat 32 (img% p256IdentityAddress)) p256IdentityData
  GD : CodeIn M (BitVec.ofNat 32 (img% p256GMontAddress)) p256GMontData
  OD : CodeIn M (BitVec.ofNat 32 (img% p256MontOneAddress)) p256MontOneData
  AD : CodeIn M (BitVec.ofNat 32 (img% p256AffineIdXAddress)) p256AffineIdXData

theorem p256_zx (b : BitVec 8) : (b.zeroExtend 32).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

theorem p256_nzw (Z : Nat) : (((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF) = 0 ∨
    (((if Z = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF) = 1 := by
  by_cases h : Z = 0
  · rw [ite_eq_left h]; exact .inl (by decide)
  · rw [ite_eq_right h]; exact .inr (by decide)

/-- **Safegcd's divstep bound** for `p256VerifyPrehash`'s inversion of
`s`: for every `x` in `[1, n)`, `ivLoop8`'s 591 divsteps from `f = n`,
`g = x`, `d = 0`, and `e = 1` end with `|f| = 1`. crypto-bigint 0.7.11 runs
`(45907·256 + 30179) / 19929 = 591` divsteps (`safegcd.rs`, `iterations`),
which is the bound from <https://github.com/sipa/safegcd-bounds>. That
bound is checked by computer search, not proved here. -/
def P256InvBound : Prop :=
  ∀ x : Nat, 0 < x → x < C3.p256.n → (ivLoop8 C3.p256.n 10 ⟨1, (C3.p256.n : Int), (x : Int), 0, 1, 0x24F⟩).f.natAbs = 1

/-- Given safegcd's bound, the inversion of a nonzero `s` below `n` leaves
`|f| = 1`. -/
theorem p256_ivf (hB : P256InvBound) {σ A : Nat} {M0 : Word → BitVec 8} {sq : Word}
    (hN : accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8 = C3.p256.n)
    (h1 : accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 = 1)
    (hs0 : beNat (memBytes M0 sq 32) ≠ 0) (hsn : beNat (memBytes M0 sq 32) < C3.p256.n)
    (hv : sgnVal σ A = (ivLoop8 (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) 10
      (p256Iv0 M0 (memBytes M0 sq 32))).f) :
    A = 1 := by
  have e := congrArg Int.natAbs hv
  rw [Safegcd.sgnVal_natAbs] at e
  rw [e]
  unfold p256Iv0
  rw [hN, h1, b32_mem]
  exact hB _ (Nat.pos_of_ne_zero hs0) hsn

set_option maxHeartbeats 64000000 in
/-- **`p256VerifyPrehash`**, from its entry to its return: it panics,
returns 0, or returns 1 with `SvP256Facts` for the key at `pk`, the digest
at `dg`, and the scalars at `rp` and `sq`. It panics only if safegcd's
divstep bound fails or the image's 1 isn't 1. It returns with `sp`, `ra`,
`s0` to `s11`, `gp`, and `tp` as they were, and changes no memory outside
its frame. -/
theorem p256VerifyPrehash_correct_bound (m : Machine) {B pk dg rp sq : Word}
    (E : P2vEnv m.mem) (F : Fr B 0x3590) (hpc : m.pc = P2V) (hsp : reg m sp = B + 0x3590)
    (ha0 : reg m a0 = pk) (ha1 : reg m a1 = dg) (ha2 : reg m a2 = rp) (ha3 : reg m a3 = sq)
    (hret : reg m ra &&& ~~~1 = reg m ra) (RS : P2vRoSep B)
    (r_in : P2vIn B rp 32) (s_in : P2vIn B sq 32) (k_in : P2vIn B pk 0x41) (dg_in : P2vIn B dg 32) :
    ((P256InvBound → accV m.mem (BitVec.ofNat 32 (img% p256OneAddress)) 8 ≠ 1) ∧ Panics m) ∨
    P2vRet B (fun k => reg m (savedReg k)) m 0 ∨
    (SvP256Facts m.mem pk dg (memBytes m.mem rp 32) (memBytes m.mem sq 32) ∧
      P2vRet B (fun k => reg m (savedReg k)) m 1) := by
  have hN : 0 < accV m.mem (BitVec.ofNat 32 (img% b2sOrder256Address)) 8 := by
    show 0 < accV m.mem BYO 8; rw [E.BY.ord]; decide
  have hP : 0 < accV m.mem (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 := by
    rw [show accV m.mem (BitVec.ofNat 32 (img% p256ModulusAddress)) 8 = p256 from E.D.N]; unfold p256; decide
  have hG : Pt2Lt (accV m.mem (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8, accV m.mem (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8, accV m.mem (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8) := by
    rw [code_accV E.GD 0 8 (by decide), code_accV E.GD 0x20 8 (by decide), code_accV E.GD 0x40 8 (by decide)]
    exact ⟨by decide, by decide, by decide⟩
  have hQ : Pt2Lt ((gsVal m.mem pk 1 * 2 ^ 256 % p256), (gsVal m.mem pk 0x21 * 2 ^ 256 % p256), (accV m.mem (BitVec.ofNat 32 (img% p256MontOneAddress)) 8)) := by
    have z : accV m.mem (BitVec.ofNat 32 (img% p256MontOneAddress) + BitVec.ofNat 32 0) 8 = dataVal p256MontOneData 0 8 :=
      code_accV E.OD 0 8 (by decide)
    rw [add_ofNat_zero] at z
    exact ⟨Nat.mod_lt _ (by unfold p256; decide), Nat.mod_lt _ (by unfold p256; decide),
      by show accV m.mem (BitVec.ofNat 32 (img% p256MontOneAddress)) 8 < p256; rw [z]; decide⟩
  have hidR : accV m.mem (BitVec.ofNat 32 (img% p256AffineIdXAddress)) 8 < p256 := by
    have z : accV m.mem (BitVec.ofNat 32 (img% p256AffineIdXAddress) + BitVec.ofNat 32 0) 8 = dataVal p256AffineIdXData 0 8 :=
      code_accV E.AD 0 8 (by decide)
    rw [add_ofNat_zero] at z
    rw [z]; decide
  have s : St m.mem P2V m 0 (reg m) := ⟨by rw [hpc]; simp, rfl, fun _ => rfl⟩
  obtain ⟨n1, c1, s1, sp1, r1_9, r1_19, r1_8, r1_20, k1⟩ := p2v_pro E.ME.C.self F s hsp
  have m1 : n1.mem = p2vSaves m.mem B m := s1.mem
  rw [← m1] at s1
  have fM1 : ∀ x, P2vR B x → n1.mem x = m.mem x := fun x hx => by
    rw [m1]; exact p2vSaves_out (by
      have := hx.sub (c := 0x36FC) (l := 0x34) (by decide)
      rwa [BitVec.add_assoc, show (0xFFFFFE60 : Word) + BitVec.ofNat 32 0x36FC = BitVec.ofNat 32 0x355C from rfl] at this)
  have E1 : P2vCode n1.mem := E.ME.C.fr F fM1
  have V1 : P2vSaves B n1.mem (fun k => reg m (savedReg k)) := fun k hk => by rw [m1]; exact p2vSaves_read k hk
  have h3 : reg n1 (3 : Fin 32) = reg m (3 : Fin 32) := k1 3 (by decide)
  have h4 : reg n1 (4 : Fin 32) = reg m (4 : Fin 32) := k1 4 (by decide)
  rcases p2v_p256_inv F E1 V1 hret s1 m.mem fM1 sp1 (r1_8.trans ha2) (r1_9.trans ha0) (r1_19.trans ha1)
      (r1_20.trans ha3) r_in s_in k_in dg_in E.EC E.IC E.UC E.D E.BG RS E.BY with
    ⟨-, e⟩ | ⟨hR, n2, c2, fM2, s2, I2⟩
  · exact .inr (.inl (P2vRet.pre c1 h3 h4 fM1 e))
  obtain ⟨n3, c3, fr3, s3, I3⟩ := p2v_ivloop F hret hN 10 s2 I2 (by show (0x24F : Nat) ≠ 0; decide)
    (by show (0x24F : Nat) ≤ 62 * 10; decide)
  have fM3 : ∀ x, P2vR B x → n3.mem x = m.mem x := fun x hx => (fr3 x hx).trans (fM2 x hx)
  rcases p2v_p256_z_or F hret s3 I3 m.mem fM3 E.EC E.UC E.UE E.N8 RS E.PM E.WM E.PT E.WN E.ME hG hQ E.IC E.hid with
    ⟨hF, e⟩ | ⟨hSC, stm, hst, l4, n4, c4, fM4, s4, I4⟩
  · refine .inl ⟨fun hB h1 => hF ?_, Panics.of_steps (c1.trans (c2.trans c3)) e⟩
    rw [p256_ivf hB E.BY.ord h1 hR.2.2.2.2.2.1 hR.2.2.2.1 I3.vf, h1]
  obtain ⟨n5, c5, fr5, s5, I5⟩ := p2v_zvloop F hret hP 10 s4 I4 (by show (0x24F : Nat) ≠ 0; decide)
    (by show (0x24F : Nat) ≤ 62 * 10; decide)
  have fM5 : ∀ x, P2vR B x → n5.mem x = m.mem x := fun x hx => (fr5 x hx).trans (fM4 x hx)
  have c15 : Steps m n5 := c1.trans (c2.trans (c3.trans (c4.trans c5)))
  have g3 : reg n5 (3 : Fin 32) = reg m (3 : Fin 32) := I5.g3.trans h3
  have g4 : reg n5 (4 : Fin 32) = reg m (4 : Fin 32) := I5.g4.trans h4
  have W3 : ((n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x920)).zeroExtend 32).toNat ≤ 1 := by rw [p256_zx]; exact I3.lf
  have V3 : sgnVal ((n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x920)).zeroExtend 32).toNat
      (accV n3.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8) = (p256Sf m.mem (memBytes m.mem sq 32)).f := by
    rw [p256_zx]; exact I3.vf
  have W5 : ((n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0)).zeroExtend 32).toNat ≤ 1 := by rw [p256_zx]; exact I5.lf
  have V5 : sgnVal ((n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xFA0)).zeroExtend 32).toNat
      (accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8) = (p256Sz m.mem stm.1.2.2).f := by
    rw [p256_zx]; exact I5.vf
  rcases p2v_ze (rem := 0) F I5.E I5.V hret s5 m.mem fM5 I5.sp I5.g14 rfl I5.w10 rfl I5.a180 rfl rfl I5.a980 rfl rfl
      I5.a1338 I5.a1358 rfl rfl rfl rfl E.UC E.EC E.UE E.N8 E.P2C E.GDC E.D E.SC E.BY E.WN I5.lf I5.ld (p256_nzw _)
      l4.1 l4.2.1 hidR (C3.RV32.Safegcd.hzi_holds E.D stm.1.2.2 _ _ _ _ I5.ld W5 V5 I5.vd) with
    ⟨-, e⟩ | ⟨h6, x6⟩
  · exact .inr (.inl (P2vRet.pre c15 g3 g4 fM5 e))
  obtain ⟨n6, c6, s6, E6, V6, fR6, sp6, r6_3, r6_4, a6, -⟩ := x6
  obtain ⟨n7, d7, u7⟩ := s6.jump E6.self p2v_at_10c4 (off' := 0x144) (by decide) (by rw [s6.pc]; decide)
  have s7 : St n7.mem P2V n7 0x144 (reg n7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have hr := p2v_retR F (by rw [u7.mem]; exact E6.self) s7 (c6.trans (.single d7))
    (fun x hx => by rw [u7.mem]; exact (fR6 x hx).trans (fM5 x hx).symm) (by rw [u7.mem]; exact V6) hret
    ((u7.regs sp).trans sp6) ((u7.regs 3).trans r6_3) ((u7.regs 4).trans r6_4)
  rw [(u7.regs a0).trans a6] at hr
  refine .inr (.inr ⟨?_, P2vRet.pre c15 g3 g4 fM5 hr⟩)
  have hc : (((if accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = accV m.mem (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF) =
      (((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF) &&& (((if accV n5.mem (B + 0x21A0 + BitVec.ofNat 32 0xF80) 8 = accV m.mem (BitVec.ofNat 32 (img% p256OneAddress)) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF) :=
    BitVec.and_comm _ _
  rw [hc] at h6
  unfold SvP256Facts
  rw [b32_mem, b32_mem]
  exact ⟨hR, _, _, _, _, I3.ld, W3, V3, I3.vd, hSC, stm, hst, _, _, _, _, I5.ld, W5, V5, I5.vd, h6, trivial⟩

/-- **`p256VerifyPrehash`**, from its entry to its return: it panics,
returns 0, or returns 1 with `SvP256Facts` for the key at `pk`, the digest
at `dg`, and the scalars at `rp` and `sq`. It returns with `sp`, `ra`, `s0`
to `s11`, `gp`, and `tp` as they were, and changes no memory outside its
frame. -/
theorem p256VerifyPrehash_correct (m : Machine) {B pk dg rp sq : Word}
    (E : P2vEnv m.mem) (F : Fr B 0x3590) (hpc : m.pc = P2V) (hsp : reg m sp = B + 0x3590)
    (ha0 : reg m a0 = pk) (ha1 : reg m a1 = dg) (ha2 : reg m a2 = rp) (ha3 : reg m a3 = sq)
    (hret : reg m ra &&& ~~~1 = reg m ra) (RS : P2vRoSep B)
    (r_in : P2vIn B rp 32) (s_in : P2vIn B sq 32) (k_in : P2vIn B pk 0x41) (dg_in : P2vIn B dg 32) :
    Panics m ∨ P2vRet B (fun k => reg m (savedReg k)) m 0 ∨
    (SvP256Facts m.mem pk dg (memBytes m.mem rp 32) (memBytes m.mem sq 32) ∧
      P2vRet B (fun k => reg m (savedReg k)) m 1) := by
  rcases p256VerifyPrehash_correct_bound m E F hpc hsp ha0 ha1 ha2 ha3 hret RS r_in s_in k_in dg_in with
    ⟨-, e⟩ | h
  · exact .inl e
  · exact .inr h

/-- **`p256VerifyPrehash` without the panic**: given safegcd's divstep
bound, it returns 0, or returns 1 with `SvP256Facts` for the key at `pk`,
the digest at `dg`, and the scalars at `rp` and `sq`. It returns with `sp`,
`ra`, `s0` to `s11`, `gp`, and `tp` as they were, and changes no memory
outside its frame. -/
theorem p256VerifyPrehash_correct_np (m : Machine) {B pk dg rp sq : Word}
    (E : P2vEnv m.mem) (F : Fr B 0x3590) (hpc : m.pc = P2V) (hsp : reg m sp = B + 0x3590)
    (ha0 : reg m a0 = pk) (ha1 : reg m a1 = dg) (ha2 : reg m a2 = rp) (ha3 : reg m a3 = sq)
    (hret : reg m ra &&& ~~~1 = reg m ra) (RS : P2vRoSep B)
    (r_in : P2vIn B rp 32) (s_in : P2vIn B sq 32) (k_in : P2vIn B pk 0x41) (dg_in : P2vIn B dg 32)
    (UD : CodeIn m.mem (BitVec.ofNat 32 (img% p256OneAddress)) p256OneData) (hB : P256InvBound) :
    P2vRet B (fun k => reg m (savedReg k)) m 0 ∨
    (SvP256Facts m.mem pk dg (memBytes m.mem rp 32) (memBytes m.mem sq 32) ∧
      P2vRet B (fun k => reg m (savedReg k)) m 1) := by
  rcases p256VerifyPrehash_correct_bound m E F hpc hsp ha0 ha1 ha2 ha3 hret RS r_in s_in k_in dg_in with
    ⟨h, -⟩ | h
  · have z := code_accV UD 0 8 (by decide)
    rw [add_ofNat_zero] at z
    exact absurd (z.trans (by decide)) (h hB)
  · exact h

end C3.RV32.P2v
