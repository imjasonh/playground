import C3BootProofs.Proofs.SvP2
import C3BootProofs.Proofs.SvPvModel

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.P2v

set_option maxRecDepth 100000

theorem sv_accData {B : Word} {M M0 : Word → BitVec 8} (FW : Fr (B + 0xFFFFEC10) 0x3A50)
    (fR : ∀ x, SvR B x → M x = M0 x) {q : Word} (h1 : (img% dataWindowAddress) ≤ q.toNat)
    (h2 : q.toNat + 32 ≤ (img% dataWindowAddress + dataWindowSize)) : accV M q 8 = accV M0 q 8 :=
  accV_congr 8 fun i hi => memLoad32_congr fun j hj => by
    rw [add_ofNat_assoc]
    exact fR _ (dataR (ql := 32) FW h1 h2 (4 * i + j) (by omega))

theorem sv_bytes32 {B : Word} {M : Word → BitVec 8} {l : Bytes} {e : Nat}
    (h0 : M (B + 0x21A0 + BitVec.ofNat 32 e) = BitVec.ofNat 8 (l.getD 0 0))
    (h1 : ∀ j, j < 31 → M (B + 0x21A0 + BitVec.ofNat 32 (e + 1 + j)) = BitVec.ofNat 8 (l.getD (1 + j) 0)) :
    memBytes M (B + 0x21A0 + BitVec.ofNat 32 e) 32 = b32 l :=
  memBytes_svBytes fun j hj => by
    rw [add_ofNat_assoc]
    rcases j with _ | i
    · exact h0
    · rw [show e + (i + 1) = e + 1 + i by omega, show i + 1 = 1 + i by omega]; exact h1 i (by omega)

/-- `SvP256Facts` reads the key, the digest, and constants in the data window,
so it holds on any memory that agrees with `M` there. -/
theorem SvP256Facts.toM0 {B bp dg : Word} {r s : Bytes} {M M0 : Word → BitVec 8}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (fR : ∀ x, SvR B x → M x = M0 x)
    (k_in : SvIn B bp 0x41) (dg_in : SvIn B dg 32) (h : SvP256Facts M bp dg r s) : SvP256Facts M0 bp dg r s := by
  have eN := sv_accData FW fR (q := BitVec.ofNat 32 (img% b2sOrder256Address)) (by decide) (by decide)
  have eO := sv_accData FW fR (q := BitVec.ofNat 32 (img% p256OneAddress)) (by decide) (by decide)
  have eP := sv_accData FW fR (q := BitVec.ofNat 32 (img% p256ModulusAddress)) (by decide) (by decide)
  have eR := sv_accData FW fR (q := BitVec.ofNat 32 (img% p256R2Address)) (by decide) (by decide)
  have eG0 := sv_accData FW fR (q := BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x0) (by decide) (by decide)
  have eG1 := sv_accData FW fR (q := BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x20) (by decide) (by decide)
  have eG2 := sv_accData FW fR (q := BitVec.ofNat 32 (img% p256GMontAddress) + BitVec.ofNat 32 0x40) (by decide) (by decide)
  have eM := sv_accData FW fR (q := BitVec.ofNat 32 (img% p256MontOneAddress)) (by decide) (by decide)
  have eA := sv_accData FW fR (q := BitVec.ofNat 32 (img% p256AffineIdXAddress)) (by decide) (by decide)
  have eB : memBytes M (BitVec.ofNat 32 (img% p256OrderBeAddress)) 32 =
      memBytes M0 (BitVec.ofNat 32 (img% p256OrderBeAddress)) 32 :=
    sv_mbRo FW fR (.inr ⟨by decide, by decide⟩)
  have eD : memBytes M dg 32 = memBytes M0 dg 32 := sv_mb fR dg_in
  have e0 : M bp = M0 bp := by
    have := sv_pt fR k_in 0 (by decide)
    rwa [BitVec.add_zero] at this
  have eS : ∀ l, p256Sf M l = p256Sf M0 l := fun l => by unfold p256Sf p256Iv0; rw [eN, eO]
  have eZ : ∀ Z, p256Sz M Z = p256Sz M0 Z := fun Z => by unfold p256Sz p256Zv0; simp only [eP, eR]
  have eg : ∀ o, o + 32 ≤ 0x41 → gsVal M bp o = gsVal M0 bp o := fun o ho => by
    have e : memBytes M (bp + BitVec.ofNat 32 o) 32 = memBytes M0 (bp + BitVec.ofNat 32 o) 32 :=
      memBytes_congr fun i hi => by rw [add_ofNat_assoc]; exact sv_pt fR k_in (o + i) (by omega)
    unfold gsVal; rw [e]
  have eGs : GsOk M bp = GsOk M0 bp := by unfold GsOk; rw [e0, eg 1 (by decide), eg 0x21 (by decide)]
  unfold SvP256Facts at h ⊢
  simp only [eN, eO, eP, eG0, eG1, eG2, eM, eA, eB, eD, e0, eS, eZ, eg 1 (by decide), eg 0x21 (by decide),
    eGs] at h
  exact h

set_option linter.unusedVariables false in
/-- **The P-256 signature check**: `p256_verify_prehash`, from 0xA4C to 0xA60. -/
theorem sv_p2st {B out bp x20 x21 x22 x24 x26 q : Word} {sr ss : Bytes} {v : Nat → Word} {n0 : Machine}
    (FW : Fr (B + 0xFFFFEC10) 0x3A50) (E0 : SvCode n0.mem) (V0 : SvSaves B n0.mem v) (hret : v 0 &&& ~~~1 = v 0)
    (hO : SvOut B out) (s0 : St n0.mem SV n0 0xA4C (reg n0))
    (M0 : Word → BitVec 8) (fM : ∀ x, SvR B x → n0.mem x = M0 x)
    (g0_2 : reg n0 sp = B + 0x21A0)
    (g0_18 : reg n0 (18 : Fin 32) = out)
    (g0_19 : reg n0 (19 : Fin 32) = bp)
    (g0_20 : reg n0 (20 : Fin 32) = x20)
    (g0_21 : reg n0 (21 : Fin 32) = x21)
    (g0_22 : reg n0 (22 : Fin 32) = x22)
    (g0_23 : reg n0 (23 : Fin 32) = q)
    (g0_24 : reg n0 (24 : Fin 32) = x24)
    (g0_26 : reg n0 (26 : Fin 32) = x26)
    (b0_130 : n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) = BitVec.ofNat 8 (sr.getD 0 0))
    (q0_131 : ∀ j, j < 31 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x131 + j)) = BitVec.ofNat 8 (sr.getD (1 + j) 0))
    (q0_150 : ∀ j, j < 32 → n0.mem (B + 0x21A0 + BitVec.ofNat 32 (0x150 + j)) = BitVec.ofNat 8 (ss.getD j 0))
    (PE0 : P2vEnv M0) (RS : SvRoSep B) (k_in : SvIn B x24 0x41) (dg_in : SvIn B x20 32) :
    SvErrRet B out v n0 ∨ Panics n0 ∨
    (SvP256Facts M0 x24 x20 (b32 sr) (b32 ss) ∧
    ∃ n', Steps n0 n' ∧
        St n'.mem SV n' 0xA60 (reg n') ∧
        SvCode n'.mem ∧
        SvSaves B n'.mem v ∧
        (∀ x, SvR B x → n'.mem x = M0 x) ∧
        reg n' sp = B + 0x21A0 ∧
        reg n' (3 : Fin 32) = reg n0 (3 : Fin 32) ∧
        reg n' (4 : Fin 32) = reg n0 (4 : Fin 32) ∧
        reg n' (18 : Fin 32) = out ∧
        reg n' (19 : Fin 32) = bp ∧
        reg n' (20 : Fin 32) = x20 ∧
        reg n' (21 : Fin 32) = x21 ∧
        reg n' (22 : Fin 32) = x22 ∧
        reg n' (23 : Fin 32) = q ∧
        reg n' (24 : Fin 32) = x24 ∧
        reg n' (26 : Fin 32) = x26 ∧
        SvKeepL B n0.mem n'.mem []) := by
  have er : memBytes n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x130) 32 = b32 sr :=
    sv_bytes32 b0_130 fun j hj => q0_131 j hj
  have es : memBytes n0.mem (B + 0x21A0 + BitVec.ofNat 32 0x150) 32 = b32 ss :=
    memBytes_svBytes fun j hj => by rw [add_ofNat_assoc]; exact q0_150 j hj
  rcases sv_p2c FW E0 V0 hret hO s0 M0 fM g0_2 g0_18 PE0 RS (by rw [g0_24]; exact k_in)
      (by rw [g0_20]; exact dg_in) with h | h | ⟨hf, n', c, s, E, V, f, hs, k, K⟩
  · exact .inl h
  · exact .inr (.inl h)
  · rw [er, es, g0_24, g0_20] at hf
    refine .inr (.inr ⟨?_, n', c, s, E, V, f, hs, k 3 (by decide), k 4 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, K⟩)
    · exact SvP256Facts.toM0 FW fM k_in dg_in hf
    · rw [k 18 (by decide), g0_18]
    · rw [k 19 (by decide), g0_19]
    · rw [k 20 (by decide), g0_20]
    · rw [k 21 (by decide), g0_21]
    · rw [k 22 (by decide), g0_22]
    · rw [k 23 (by decide), g0_23]
    · rw [k 24 (by decide), g0_24]
    · rw [k 26 (by decide), g0_26]

end C3.RV32.Sv
