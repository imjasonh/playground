import C3BootProofs.Proofs.P2vIvLoop
import C3BootProofs.Proofs.P2vA1
import C3BootProofs.Proofs.P2vA2
import C3BootProofs.Proofs.P2vA3
import C3BootProofs.Proofs.P256Defs
import C3BootProofs.Proofs.Sha512Load

/-!
# `p256VerifyPrehash`: the check up to the inversion of `s`

From 0x48 to the inversion's head at 0x3E4: `p2v_a1`, `p2v_a2`, and `p2v_a3`
check `r` and `s`, decode the key, and set up the inversion, whose state is
then `IvInv` for the starting `ivLoop8` state `p256Iv0`.
-/

namespace C3.RV32.P2v

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Sv

set_option maxRecDepth 100000

theorem b32_mem (M : Word → BitVec 8) (p : Word) : b32 (memBytes M p 32) = memBytes M p 32 := by
  unfold b32
  apply List.ext_getElem
  · rw [memBytes_length, List.length_map, List.length_range]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have hb := memBytes_lt M p (n := 32) (i := i) (by rw [memBytes_length] at h2; exact h2)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at hb
    rw [BitVec.toNat_ofNat, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
    exact Nat.mod_eq_of_lt hb

/-- What `p2v_a1` and `p2v_a2` check: `r` and `s` are in range and nonzero,
and the key is an uncompressed point that `GsOk` accepts. -/
def P2vRange (M0 : Word → BitVec 8) (pk rp sq : Word) : Prop :=
  ((inScalarRange (memBytes M0 rp 32) (memBytes M0 (BitVec.ofNat 32 (img% p256OrderBeAddress)) 32) = true) ∧
    (inScalarRange (memBytes M0 sq 32) (memBytes M0 (BitVec.ofNat 32 (img% p256OrderBeAddress)) 32) = true) ∧
    (M0 pk = 4) ∧ True) ∧
  ((GsOk M0 pk) ∧ (beNat (memBytes M0 rp 32) < C3.p256.n) ∧ (beNat (memBytes M0 sq 32) < C3.p256.n) ∧
    (beNat (memBytes M0 rp 32) ≠ 0) ∧ (beNat (memBytes M0 sq 32) ≠ 0) ∧ True)

set_option maxHeartbeats 64000000 in
/-- **The check up to the inversion of `s`**: from 0x48 to 0x3E4, or a
return of 0 when `r` or `s` is out of range or the key isn't a point on the
curve. -/
theorem p2v_p256_inv {B pk dg rp sq : Word} {v : Nat → Word} {n0 : Machine}
    (F : Fr B 0x3590) (E0 : P2vCode n0.mem) (V0 : P2vSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (s0 : St n0.mem P2V n0 0x48 (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, P2vR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0) (g0_8 : reg n0 (8 : Fin 32) = rp) (g0_9 : reg n0 (9 : Fin 32) = pk)
    (g0_19 : reg n0 (19 : Fin 32) = dg) (g0_20 : reg n0 (20 : Fin 32) = sq)
    (r_in : P2vIn B rp 32) (s_in : P2vIn B sq 32) (k_in : P2vIn B pk 0x41) (dg_in : P2vIn B dg 32)
    (EC0 : P2vEcCode M0) (IC0 : P2vIvCode M0) (UC0 : P2vUpCode M0) (D0 : P2Data M0) (BG0 : BGEnv M0)
    (RS : P2vRoSep B) (BY0 : BYEnv M0) :
    (¬ P2vRange M0 pk rp sq ∧ P2vRet B v n0 0) ∨
    (P2vRange M0 pk rp sq ∧
      ∃ m, Steps n0 m ∧ (∀ x, P2vR B x → m.mem x = M0 x) ∧ St m.mem P2V m 0x3E4 (reg m) ∧
        IvInv B m v (reg n0 (3 : Fin 32)) (reg n0 (4 : Fin 32))
          (gsVal M0 pk 1 * 2 ^ 256 % p256) (gsVal M0 pk 0x21 * 2 ^ 256 % p256)
          (accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8) (beNat (memBytes M0 rp 32))
          (beNat (memBytes M0 sq 32)) (beNat (memBytes M0 dg 32) % C3.p256.n)
          (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) (p256Iv0 M0 (memBytes M0 sq 32))) := by
  rcases p2v_a1 F E0 V0 hret s0 M0 fM g0_2 g0_8 g0_9 g0_19 g0_20 r_in s_in k_in dg_in EC0 with
    ⟨hn, e⟩ | ⟨x1_0, x1_1, x1_2, n1, c1, s1, E1, V1, fR1, r1_2, r1_3, r1_4, r1_8, r1_9, r1_19, r1_20, -⟩
  · exact .inl ⟨fun h => hn h.1, e⟩
  have h1 := And.intro x1_0 (And.intro x1_1 (And.intro x1_2 trivial))
  have CH1 : ∀ x, P2vR B x → n1.mem x = n0.mem x := fun x hx => (fR1 x hx).trans (fM x hx).symm
  rcases p2v_a2 F E1 V1 hret s1 M0 fR1 r1_2 r1_8 r1_9 r1_19 r1_20 r_in s_in k_in dg_in EC0 D0 BG0 with
    ⟨hn, e⟩ | ⟨x2_0, x2_1, x2_2, x2_3, x2_4, n2, c2, s2, E2, V2, fR2, r2_2, r2_3, r2_4, r2_18, r2_19, r2_26,
      a2_58, a2_78, -, -, a2_200, -, a2_fe4, -⟩
  · exact .inl ⟨fun h => hn h.2, P2vRet.pre c1 r1_3 r1_4 CH1 e⟩
  have h2 := And.intro x2_0 (And.intro x2_1 (And.intro x2_2 (And.intro x2_3 (And.intro x2_4 trivial))))
  rcases p2v_a3 F E2 V2 hret s2 M0 fR2 r2_2 r2_18 r2_19 r2_26 a2_58 a2_78 a2_200 a2_fe4 EC0 RS BY0 x2_3 x2_4 dg_in with
    ⟨hn, -⟩ | ⟨n3, c3, s3, E3, V3, fR3, r3_2, r3_3, r3_4, r3_8, r3_9, r3_19, r3_21, r3_22, r3_23, r3_24, r3_26,
      r3_27, b3_220, b3_920, b3_9a0, b3_1004, -, -, -, -, -, -, -, a3_120, a3_140, a3_160, a3_180, a3_1a0, a3_1c0,
      a3_200, a3_900, a3_980, -, -, -, a3_fe4, -⟩
  · exact absurd trivial hn
  obtain ⟨n4, d4, u4⟩ := s3.notTaken E3.self 0x3E4 p2v_at_3e0 (by decide)
    (by show (reg n3 24 == reg n3 x0) = false; rw [r3_24, s3.zero]; decide)
  have I3 : IvInv B n3 v (reg n0 (3 : Fin 32)) (reg n0 (4 : Fin 32))
      (gsVal M0 pk 1 * 2 ^ 256 % p256) (gsVal M0 pk 0x21 * 2 ^ 256 % p256)
      (accV M0 (BitVec.ofNat 32 (img% p256MontOneAddress)) 8) (beNat (memBytes M0 rp 32))
      (beNat (memBytes M0 sq 32)) (beNat (memBytes M0 dg 32) % C3.p256.n)
      (accV M0 (BitVec.ofNat 32 (img% b2sOrder256Address)) 8) (p256Iv0 M0 (memBytes M0 sq 32)) :=
    ⟨E3, IC0.p2v F fR3, EC0.p2v F fR3, UC0.p2v F fR3, V3, r3_2, by rw [r3_3, r2_3, r1_3],
      by rw [r3_4, r2_4, r1_4], r3_8, r3_9, r3_22, r3_23, r3_26, r3_27, by rw [r3_19, r3_21]; rfl,
      r3_24, by show 0x24F < 2 ^ 32; decide, accV_dataR F fR3 (by decide) (by decide),
      a3_120, a3_140, a3_160, a3_180, a3_1a0, a3_1c0,
      by rw [b3_920, a3_900]; rfl, by rw [b3_920]; decide,
      by rw [b3_220, a3_200]; show _ = ((beNat (b32 (memBytes M0 sq 32)) : Nat) : Int); rw [b32_mem]; rfl,
      by rw [b3_220]; decide,
      by rw [b3_1004, a3_fe4]; rfl, by rw [b3_1004]; decide,
      by rw [b3_9a0, a3_980]; rfl, by rw [b3_9a0]; decide⟩
  exact .inr ⟨⟨h1, h2⟩, n4, c1.trans (c2.trans (c3.trans (.single d4))), fun x hx => by rw [u4.mem]; exact fR3 x hx,
    ⟨u4.pc, rfl, fun _ => rfl⟩, I3.of u4.mem fun q _ => u4.regs q⟩

end C3.RV32.P2v
