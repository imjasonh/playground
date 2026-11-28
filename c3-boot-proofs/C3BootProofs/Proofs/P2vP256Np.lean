import C3BootProofs.Proofs.P2vP256C
import C3BootProofs.Models.EcdsaWnaf

/-!
# `p256VerifyPrehash` from the inverse to the inversion of `Z`, without a panic

`p2v_p256_z` panics in two places:

* At 0x10C8, `NonZeroScalar::invert_vartime`'s `unwrap` (elliptic-curve
  0.14.3, `src/scalar/nonzero.rs:229`), when the inversion of `s` ends with
  `f ≠ 1` (`p2v_ive`).
* At 0x10D8, the bounds check on the main loop's table index, when a wNAF
  digit byte is not one that `DigOk` allows (`ml2_pair`).

The digits always pass (`p2vnp_ne`). `p2v_p256_z_np` takes `f = 1` as a
hypothesis and has no panic, and `p2v_p256_z_or` splits the panic off as
`f ≠ 1`.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Sv C3.Models

set_option maxRecDepth 100000

theorem p2vnp_add {T : Nat → Pt2} {acc : Pt2} {b : Nat} (h : DigOk b) : ∃ o, mlAdd2 T acc b = some o := by
  unfold mlAdd2
  rcases h with rfl | ⟨_, h2⟩ | ⟨_, h2, h3⟩
  · exact ⟨_, rfl⟩
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]; exact ⟨_, rfl⟩
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; exact ⟨_, rfl⟩

theorem p2vnp_pair {T : Nat → Pt2} {D : List Nat} {k : Nat} (st : Pt2 × Bool) (h : DigOk (D.getD k 0)) :
    ∃ st', mlPair2 T D k st = some st' := by
  unfold mlPair2
  by_cases hk : 0x101 < k + 1
  · rw [ite_eq_left hk]; exact ⟨_, rfl⟩
  · rw [ite_eq_right hk]
    obtain ⟨o, e⟩ := p2vnp_add (T := T) (acc := st.1) h
    rw [e]
    cases o
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem p2vnp_loop {T0 T1 : Nat → Pt2} {D0 D1 : List Nat} (h0 : ∀ k, DigOk (D0.getD k 0))
    (h1 : ∀ k, DigOk (D1.getD k 0)) : ∀ k st, ∃ st', mlLoop2 T0 T1 D0 D1 k st = some st'
  | 0, st => ⟨st, rfl⟩
  | k + 1, st => by
    obtain ⟨a, ea⟩ := p2vnp_pair (T := T0) (if st.2 then ptDbl2 st.1 else st.1, st.2) (h0 k)
    obtain ⟨b, eb⟩ := p2vnp_pair (T := T1) a (h1 k)
    obtain ⟨c, ec⟩ := p2vnp_loop h0 h1 k b
    exact ⟨c, by rw [mlLoop2, mlIter2, ea, Option.bind_some, eb, Option.bind_some, ec]⟩

/-- The main loop never fails on digits that `DigOk` allows. -/
theorem p2vnp_ne {T0 T1 : Nat → Pt2} {D0 D1 : List Nat} {L : Nat} (h0 : ∀ k, DigOk (D0.getD k 0))
    (h1 : ∀ k, DigOk (D1.getD k 0)) : mlMain2 T0 T1 D0 D1 L ≠ none := by
  obtain ⟨c, ec⟩ := p2vnp_loop (T0 := T0) (T1 := T1) h0 h1 L (idPt2, false)
  unfold mlMain2; rw [ec]; nofun

theorem p2vnp_dig (U : Nat) : ∀ k, DigOk ((wnafBytes (wnafGo U 0x100 0x101 0 0) 0x101).getD k 0) :=
  wnafBytes_digOk (wnafGo_dig _ _ _ (Nat.zero_le _)) 0x101

set_option maxHeartbeats 64000000 in
/-- **The check from the inverse to the inversion of `Z`, without a panic**:
from 0x610 to 0xBEE, given that the inversion of `s` left `f = 1`. -/
theorem p2v_p256_z_np {B r3 r4 : Word} {qx qy qz rv sv zv N : Nat} {v : Nat → Word} {n0 : Machine}
    {st : Iv} (F : Fr B 0x3590) (hret : v 0 &&& ~~~1 = v 0) (s : St n0.mem P2V n0 0x610 (reg n0))
    (I : IvInv B n0 v r3 r4 qx qy qz rv sv zv N st)
    (M0 : Word → BitVec 8) (fM : ∀ x, P2vR B x → n0.mem x = M0 x)
    (EC0 : P2vEcCode M0) (UC0 : P2vUpCode M0) (UE0 : CodeIn M0 (BitVec.ofNat 32 uint8EqAddress) uint8EqCode) (N80 : CodeIn M0 (BitVec.ofNat 32 norm8Address) norm8Code) (RS : P2vRoSep B) (PM0 : CodeIn M0 (BitVec.ofNat 32 p256ScalarMulAddress) p256ScalarMulCode) (WM0 : CodeIn M0 (BitVec.ofNat 32 wideMulAddress) wideMulCode) (PT0 : P2vPtCode M0) (WN0 : P2vWnCode M0) (ME : MlEnv M0)
    (hG : Pt2Lt (accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8, accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8, accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8))
    (hQ : Pt2Lt (qx, qy, qz))
    (IC0 : P2vIvCode M0) (hid : CodeIn M0 (BitVec.ofNat 32 (img% p256IdentityAddress)) p256IdentityData)
    (hF : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8) :
    (((((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8)) ∧ True) ∧ ∃ stm, mlMain2 (tbl2 (accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8, accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8, accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8)) (tbl2 (qx, qy, qz)) (wnafBytes (wnafGo ((psmVal ((zv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0) 0x101) (wnafBytes (wnafGo ((psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0) 0x101) (max (wnafGo ((psmVal ((zv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0).length (wnafGo ((psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0).length) = some stm ∧ Pt2Lt stm.1 ∧
      ∃ m', Steps n0 m' ∧ (∀ x, P2vR B x → m'.mem x = M0 x) ∧ St m'.mem P2V m' 0xBEE (reg m') ∧
        ZvInv B m' v r3 r4 (((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF) rv stm.1.1 stm.1.2.1
          (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) (p256Zv0 M0 stm.1.2.2)) := by
  rcases p2v_p256_tab F hret s I M0 fM EC0 UC0 UE0 N80 RS PM0 WM0 PT0 WN0 ME hG hQ with ⟨hn, -⟩ | ⟨x1, n1, c1, fR1, s1, ME1, V1, g1_3, g1_4,
      r1_2, r1_8, r1_9, r1_a0, r1_18, r1_19, r1_20, r1_21, r1_26, w1_980, w1_c80, w1_10e4, w1_11ec, a1_180, a1_1a0, a1_1c0, a1_260, a1_2e0, a1_f80, a1_1044, a1_10c4, G1⟩
  · exact absurd ⟨hF, trivial⟩ hn
  have hL0 : (wnafGo ((psmVal ((zv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0).length ≤ 0x101 :=
    wnafGo_len (by have := accV_lt n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x260) 8; rw [a1_260] at this; exact this) _ _ _ (by decide) (by decide)
  have hL1 : (wnafGo ((psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0).length ≤ 0x101 :=
    wnafGo_len (by have := accV_lt n1.mem (B + 0x21A0 + BitVec.ofNat 32 0x2E0) 8; rw [a1_2e0] at this; exact this) _ _ _ (by decide) (by decide)
  rcases ml2_main F ME1 RS (F.dataIn fR1 hid (by decide) (by decide)) s1 r1_2 r1_9 r1_a0 hL0 hL1 G1 with
    ⟨hn, -⟩ | ⟨stm, hst, n2, c2, ME2, fr2, K2, s2, r2_2, r2_3, r2_4, -, -, A2, l2⟩
  · exact absurd hn (p2vnp_ne (p2vnp_dig _) (p2vnp_dig _))
  have fR2 : ∀ x, P2vR B x → n2.mem x = M0 x := fun x hx => (fr2 x hx).trans (fR1 x hx)
  rcases p2v_zs (rv := rv) F ME2.C (V1.keepL K2 (by decide)) hret s2 M0 fR2 r2_2
      ((K2.acc (by decide) (by decide)).trans a1_180) (congrArg Prod.fst A2) (congrArg (fun p => p.2.1) A2)
      (congrArg (fun p => p.2.2) A2) RS EC0 with
    ⟨hn, -⟩ | ⟨n3, c3, s3, E3, V3, fR3, r3_2, r3_3, r3_4, r3_a0, r3_a4, r3_24, w3_10, w3_40, b3_220, b3_920, b3_fa0,
      b3_1004, -, -, -, -, a3_180, a3_200, a3_900, a3_980, -, a3_f80, a3_fe4, a3_1338, a3_1358, -, -⟩
  · exact absurd trivial hn
  refine ⟨x1, stm, hst, l2, n3, c1.trans (c2.trans c3), fR3, s3, E3, IC0.p2v F fR3, UC0.p2v F fR3, V3, r3_2,
    by rw [r3_3, r2_3, g1_3], by rw [r3_4, r2_4, g1_4], r3_a0, r3_a4, by rw [w3_40, r3_24]; rfl,
    by show 0x24F < 2 ^ 32; decide, w3_10, accV_dataR F fR3 (by decide) (by decide), a3_980, a3_180,
    a3_1338, a3_1358, by rw [b3_fa0, a3_f80]; rfl, by rw [b3_fa0]; decide, by rw [b3_920, a3_900]; rfl,
    by rw [b3_920]; decide, by rw [b3_220, a3_200]; rfl, by rw [b3_220]; decide,
    by rw [b3_1004, a3_fe4]; rfl, by rw [b3_1004]; decide⟩

set_option maxHeartbeats 64000000 in
/-- **The check from the inverse to the inversion of `Z`**: from 0x610 to
0xBEE, or a panic when the inversion of `s` left `f ≠ 1`. -/
theorem p2v_p256_z_or {B r3 r4 : Word} {qx qy qz rv sv zv N : Nat} {v : Nat → Word} {n0 : Machine}
    {st : Iv} (F : Fr B 0x3590) (hret : v 0 &&& ~~~1 = v 0) (s : St n0.mem P2V n0 0x610 (reg n0))
    (I : IvInv B n0 v r3 r4 qx qy qz rv sv zv N st)
    (M0 : Word → BitVec 8) (fM : ∀ x, P2vR B x → n0.mem x = M0 x)
    (EC0 : P2vEcCode M0) (UC0 : P2vUpCode M0) (UE0 : CodeIn M0 (BitVec.ofNat 32 uint8EqAddress) uint8EqCode) (N80 : CodeIn M0 (BitVec.ofNat 32 norm8Address) norm8Code) (RS : P2vRoSep B) (PM0 : CodeIn M0 (BitVec.ofNat 32 p256ScalarMulAddress) p256ScalarMulCode) (WM0 : CodeIn M0 (BitVec.ofNat 32 wideMulAddress) wideMulCode) (PT0 : P2vPtCode M0) (WN0 : P2vWnCode M0) (ME : MlEnv M0)
    (hG : Pt2Lt (accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8, accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8, accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8))
    (hQ : Pt2Lt (qx, qy, qz))
    (IC0 : P2vIvCode M0) (hid : CodeIn M0 (BitVec.ofNat 32 (img% p256IdentityAddress)) p256IdentityData) :
    (accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 ≠ accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8 ∧
      Panics n0) ∨
    (((((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8) = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8)) ∧ True) ∧ ∃ stm, mlMain2 (tbl2 (accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) 8, accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) 8, accV M0 (BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) 8)) (tbl2 (qx, qy, qz)) (wnafBytes (wnafGo ((psmVal ((zv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0) 0x101) (wnafBytes (wnafGo ((psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0) 0x101) (max (wnafGo ((psmVal ((zv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0).length (wnafGo ((psmVal ((rv) * ((normVal8 ((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x1004))).toNat (((n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x920))).zeroExtend 32).toNat ((accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0xFE4) 8)) (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8)))))) 0x100 0x101 0 0).length) = some stm ∧ Pt2Lt stm.1 ∧
      ∃ m', Steps n0 m' ∧ (∀ x, P2vR B x → m'.mem x = M0 x) ∧ St m'.mem P2V m' 0xBEE (reg m') ∧
        ZvInv B m' v r3 r4 (((if stm.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF) rv stm.1.1 stm.1.2.1
          (accV M0 (BitVec.ofNat 32 (img% p256ModulusAddress)) 8) (p256Zv0 M0 stm.1.2.2)) := by
  by_cases hF : accV n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x900) 8 = accV M0 (BitVec.ofNat 32 (img% p256OneAddress)) 8
  · exact .inr (p2v_p256_z_np F hret s I M0 fM EC0 UC0 UE0 N80 RS PM0 WM0 PT0 WN0 ME hG hQ IC0 hid hF)
  · rcases p2v_p256_z F hret s I M0 fM EC0 UC0 UE0 N80 RS PM0 WM0 PT0 WN0 ME hG hQ IC0 hid with e | h
    · exact .inl ⟨hF, e⟩
    · exact .inr h

end C3.RV32.P2v
