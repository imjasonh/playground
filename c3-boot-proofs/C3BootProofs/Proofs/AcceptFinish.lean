import C3BootProofs.Proofs.AcceptStages
import C3BootProofs.Proofs.SvSpec
import C3BootProofs.Proofs.MemcpyAny

/-!
# The closure's last stage: verify, check the expiry, and write the result

At 0x1A46 `c3_bootloader::boot_main::{closure#0}` calls `sigstore::verify`
with the bundle, the trust root, and the image's digest, into a result at
`sp + 0xDD0`. An `Err` takes the exit at 0x7D6 with the error's code. An
`Ok` whose signing time is past the manifest's expiry takes that exit with
code 0x25. Otherwise the closure copies the 11 bytes at `sp + 0x238` and the
255 bytes at `sp + 0x139` into the result, stores the slot, the signing time,
and the manifest's fields, and returns.

`sigstore::verify` writes up to 0x1A0 bytes below the closure's frame, so the
stage keeps memory as it was outside the frame and those bytes
(`AcFinishInv`), not outside the frame alone (`AcInv`). `SvErrRet` says
nothing about the error's code, so an `Err` whose code is 0x27 or more
reaches 0x7D6 outside `AcFail` (`AcFinishBad`).
-/

namespace C3.RV32.Ac

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Gd C3.RV32.P2v C3.RV32.Sv

/-- The code and data that the stage runs and reads, outside the frame:
`memcpy`, and what `sv_verify_spec` needs. -/
structure AcFinishEnv (M : Word → BitVec 8) : Prop where
  mcs : CodeIn M MCS memcpyStubCode
  mcb : CodeIn M (MCS + 8) memcpyBodyCode
  sv : CodeIn M SV sigstoreVerifyCode
  svc : SvCode M
  p2 : P2Data M
  svd : SvData M
  hf : HfEnv M
  pv : PvEnv7 M
  p2v : P2vEnv M
  sha2 : SvSha2Code M
  ck : SvCkCode M
  ev : EvEnv M
  iv : (s5Hv M (BitVec.ofNat 32 (img% sha512IVAddress))).toList = Sha512.h0
  rk : SvRkCode M
  oid : SvOidData M
  nd : CodeIn M (BitVec.ofNat 32 b2sOrder256Address) b2sOrder256Data
  ud : CodeIn M (BitVec.ofNat 32 p256OneAddress) p256OneData
  ld : CodeIn M (BitVec.ofNat 32 edOrderAddress) edOrderData
  pd : CodeIn M (BitVec.ofNat 32 edPrimeAddress) edPrimeData
  pmd : CodeIn M (BitVec.ofNat 32 edPm1Address) edPm1Data
  e1d : CodeIn M (BitVec.ofNat 32 edOneAddress) edOneData
  edd : CodeIn M (BitVec.ofNat 32 edDAddress) edDData
  smd : CodeIn M (BitVec.ofNat 32 edSqrtM1Address) edSqrtM1Data
  d2d : CodeIn M (BitVec.ofNat 32 edwardsD2Address) edwardsD2Data
  bsd : CodeIn M (BitVec.ofNat 32 edBaseAddress) edBaseData
  krd : CodeIn M (BitVec.ofNat 32 edMontRAddress) edMontRData
  krrd : CodeIn M (BitVec.ofNat 32 edMontRRAddress) edMontRRData
  rekor : SvRekorData M

/-- At 0x1A46: `ra` is the `auipc` before the call, the arguments point at
the result (`sp + 0xDD0`), the bundle (`sp + 0x1320`), the trust root
(`sp + 0x1870`), and the digest (`sp + 0x108`), the manifest's expiry is at
`sp + 0x20`, and the result pointer `r` is at `sp + 0x40`. -/
structure AcFinishPre (B r : Word) (bundle : Bundle) (root : SigstoreRoot) (expiry : Nat) (n : Machine) :
    Prop where
  st : St n.mem AC n 0x1A46 (reg n)
  ra : reg n ra = AC + BitVec.ofNat 32 0x1A42 + 0xC000
  a0 : reg n a0 = acSlot B 0xDD0
  a1 : reg n a1 = acSlot B 0x1320
  a2 : reg n a2 = acSlot B 0x1870
  a3 : reg n a3 = acSlot B 0x108
  bundle : SvBundleAt (B + 0x13F0) n.mem (acSlot B 0x1320) bundle
  root : SvRootAt (B + 0x13F0) n.mem (acSlot B 0x1870) root
  expiry : SvU64At n.mem (acSlot B 0x20) expiry
  res : memLoad32 n.mem (acSlot B 0x40) = r
  ro : SvRoSep (B + 0x13F0)
  rsep : Sep r 0x12C (B + 0xFFFFFE60) 0x5C10
  ral : r.toNat % 4 = 0
  rlo : r.toNat + 0x12C ≤ 0x40000000

/-- `AcInv`, with memory kept outside the frame and the 0x1A0 bytes below it. -/
structure AcFinishInv (B Bf g t : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (n : Machine) : Prop where
  sp : reg n sp = B + 0x3A50
  gp : reg n (3 : Fin 32) = g
  tp : reg n (4 : Fin 32) = t
  saves : ∀ k, k < 13 → memLoad32 n.mem (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k
  out : ∀ x, Sep x 1 (B + 0xFFFFFE60) 0x5C10 → Sep x 1 Bf acBufLen → n.mem x = M0 x

/-- The exit at 0x7D6 with a code of 0x27 or more. -/
def AcFinishBad (B r : Word) (n : Machine) : Prop :=
  n.pc = AC + 0x7D6 ∧ memLoad32 n.mem (acSlot B 0x40) = r ∧ 0x27 ≤ (reg n (21 : Fin 32) &&& 0xFF).toNat

/-- The result the closure writes at `r` when the bundle verifies and its
signing time is no later than the expiry, from the registers and frame of
`n0` at 0x1A46. -/
def AcFinishRes (B Bf r : Word) (M0 : Word → BitVec 8) (bundle : Bundle) (root : SigstoreRoot) (expiry : Nat)
    (n0 : Machine) (M : Word → BitVec 8) : Prop :=
  ∃ vv, sigstoreVerify bundle root (memBytes n0.mem (acSlot B 0x108) 32) = some vv ∧ vv.signedTime ≤ expiry ∧
    M r = (reg n0 (21 : Fin 32)).extractLsb' 0 8 ∧
    (∀ i, i < 11 → M (r + BitVec.ofNat 32 (1 + i)) = n0.mem (acSlot B (0x238 + i))) ∧
    M (r + 0xC) = (reg n0 (25 : Fin 32)).extractLsb' 0 8 ∧
    (∀ i, i < 0xFF → M (r + BitVec.ofNat 32 (0xD + i)) = n0.mem (acSlot B (0x139 + i))) ∧
    M (r + 0x10C) = (reg n0 (27 : Fin 32)).extractLsb' 0 8 ∧
    (∀ i, i < 3 → M (r + BitVec.ofNat 32 (0x10D + i)) = n0.mem (acSlot B (0x136 + i))) ∧
    memLoad32 M (r + 0x110) = BitVec.ofNat 32 (vv.signedTime % 2 ^ 32) ∧
    memLoad32 M (r + 0x114) = BitVec.ofNat 32 (vv.signedTime / 2 ^ 32) ∧
    M (r + 0x118) = (reg n0 (27 : Fin 32)).extractLsb' 0 8 ∧
    memLoad32 M (r + 0x120) = memLoad32 n0.mem (acSlot B 0x44) ∧
    M (r + 0x128) = (reg n0 (27 : Fin 32)).extractLsb' 0 8 ∧
    ∀ x, Sep x 1 (B + 0xFFFFFE60) 0x5C10 → Sep x 1 Bf acBufLen → Sep x 1 r 0x12C → M x = M0 x

/-- From `n0`, the closure panics, reaches an exit, or returns with the
result written. -/
def AcFinishPost (B Bf g t r : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (bundle : Bundle)
    (root : SigstoreRoot) (expiry : Nat) (n0 : Machine) : Prop :=
  ∃ n', Steps n0 n' ∧ (Halting n' ∨
    (AcFinishInv B Bf g t v M0 n' ∧ (AcFail B r n' ∨ AcFinishBad B r n')) ∨
    (n'.pc = v 0 ∧ reg n' sp = B + 0x5A70 ∧ (∀ k, k < 13 → reg n' (savedReg k) = v k) ∧
      reg n' (3 : Fin 32) = g ∧ reg n' (4 : Fin 32) = t ∧
      AcFinishRes B Bf r M0 bundle root expiry n0 n'.mem))

/-- **The last stage**, from 0x1A46 to the return. -/
def AcFinishStage : Prop :=
  ∀ (n : Machine) (B Bf g t r : Word) (v : Nat → Word) (M0 : Word → BitVec 8) (bundle : Bundle)
    (root : SigstoreRoot) (expiry : Nat),
    (∀ M, (∀ x, Sep x 1 B 0x5A70 → Sep x 1 Bf acBufLen → M x = M0 x) → AcFinishEnv M) →
    CodeIn n.mem AC bootMainClosure0Code → Fr B 0x5A70 → v 0 &&& ~~~1 = v 0 →
    AcInv B Bf g t v M0 n → AcFinishPre B r bundle root expiry n →
    AcFinishPost B Bf g t r v M0 bundle root expiry n

/-! ### Addresses -/

theorem acf_ofNatToNat (x : Word) : BitVec.ofNat 32 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

theorem acf_sp (B : Word) (k : Nat) : B + 0x3A50 + BitVec.ofNat 32 k = acSlot B k :=
  add_ofNat_assoc B 0x3A50 k

theorem acf_sp40 (B : Word) : B + 0x3A50 + (0x40 : Word) = acSlot B 0x40 := acf_sp B 0x40

theorem acf_sp44 (B : Word) : B + 0x3A50 + (0x44 : Word) = acSlot B 0x44 := acf_sp B 0x44

theorem acf_slot_add (B : Word) (c k : Nat) : acSlot B c + BitVec.ofNat 32 k = acSlot B (c + k) := by
  show B + BitVec.ofNat 32 (0x3A50 + c) + BitVec.ofNat 32 k = B + BitVec.ofNat 32 (0x3A50 + (c + k))
  rw [add_ofNat_assoc, Nat.add_assoc]

theorem acf_slot1 (B : Word) (c : Nat) : acSlot B c + 1 = acSlot B (c + 1) := acf_slot_add B c 1

theorem acf_wS (B : Word) (c : Nat) :
    B + 0xFFFFFE60 + BitVec.ofNat 32 (0x3BF0 + c) = acSlot B c := by
  show _ = B + BitVec.ofNat 32 (0x3A50 + c)
  rw [BitVec.add_assoc, show (0xFFFFFE60 : Word) = BitVec.ofNat 32 0xFFFFFE60 from rfl, BitVec.ofNat_add_ofNat]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [show 0xFFFFFE60 + (0x3BF0 + c) = (0x3A50 + c) + 2 ^ 32 by omega, Nat.add_mod_right]

theorem acf_svB (B : Word) : B + 0x13F0 + 0xFFFFEA70 = B + 0xFFFFFE60 := by
  rw [BitVec.add_assoc]; rfl

section Frame

variable {B : Word}

theorem acf_lo (F : Fr B 0x5A70) : (B + 0xFFFFFE60).toNat = B.toNat - 0x1A0 :=
  F.below 0x1A0 (by decide) (by decide)

theorem acf_slotN (F : Fr B 0x5A70) {c : Nat} (hc : c ≤ 0x2020) : (acSlot B c).toNat = B.toNat + (0x3A50 + c) :=
  F.at _ (by omega)

theorem acf_F16N (F : Fr B 0x5A70) : (B + 0x3A50 + 0xFFFFFFF0 : Word).toNat = B.toNat + 0x3A40 := by
  have h1 : (B + 0x3A50 : Word).toNat = B.toNat + 0x3A50 := F.at 0x3A50 (by decide)
  have := F.hi
  rw [BitVec.toNat_add, h1, show (0xFFFFFFF0 : Word).toNat = 0xFFFFFFF0 from rfl]
  omega

theorem acf_al (F : Fr B 0x5A70) {c : Nat} (h1 : c + 4 ≤ 0x2020) (h2 : c % 4 = 0) :
    (acSlot B c).toNat % 4 = 0 := by
  rw [acf_slotN F (by omega)]; have := F.al; omega

theorem acf_svRW {x : Word} (h : Sep x 1 (B + 0xFFFFFE60) 0x5C10) : SvR (B + 0x13F0) x := by
  unfold SvR; rw [acf_svB]
  have := h.symm.sub (c := 0) (l := 0x3BF0) (by decide)
  rwa [add_ofNat_zero] at this

theorem acf_svRS (F : Fr B 0x5A70) {c : Nat} (hc : c < 0x2020) : SvR (B + 0x13F0) (acSlot B c) := by
  unfold SvR; rw [acf_svB]
  have := F.lo; have := F.hi
  exact sep_of_le (by rw [acf_lo F, acf_slotN F (by omega)]; omega) (by rw [acf_slotN F (by omega)]; omega)

theorem acf_hiW (F : Fr B 0x5A70) {x : Word} (hx : 0x40000000 ≤ x.toNat) : Sep x 1 (B + 0xFFFFFE60) 0x5C10 := by
  have := F.lo; have := F.hi; have := x.isLt
  exact (sep_of_le (by rw [acf_lo F]; omega) (by omega)).symm

theorem acf_wB {x : Word} (h : Sep x 1 (B + 0xFFFFFE60) 0x5C10) : Sep x 1 B 0x5A70 := by
  have := h.subR (c := 0x1A0) (l := 0x5A70) (by decide)
  have e : B + 0xFFFFFE60 + BitVec.ofNat 32 0x1A0 = B := by
    rw [BitVec.add_assoc]
    exact (congrArg (B + ·) (by decide : (0xFFFFFE60 : Word) + BitVec.ofNat 32 0x1A0 = 0)).trans (BitVec.add_zero B)
  rwa [e] at this

theorem acf_wSlot {x : Word} (h : Sep x 1 (B + 0xFFFFFE60) 0x5C10) {c l : Nat} (hcl : c + l ≤ 0x2020) :
    Sep (acSlot B c) l x 1 := by
  have := h.subR (c := 0x3BF0 + c) (l := l) (by omega)
  rw [acf_wS B _] at this
  exact this.symm

theorem acf_wne {x : Word} (h : Sep x 1 (B + 0xFFFFFE60) 0x5C10) {c : Nat} (hc : c < 0x2020) : x ≠ acSlot B c :=
  fun e => (acf_wSlot h (c := c) (l := 1) (by omega)) 0 (by decide) 0 (by decide)
    (by rw [add_ofNat_zero, add_ofNat_zero, e])

theorem acf_slot_ne (B : Word) {c d : Nat} (hc : c < 0x2020) (hd : d < 0x2020) (h : c ≠ d) :
    acSlot B c ≠ acSlot B d :=
  add_ofNat_ne B (by omega) (by omega) (by omega)

theorem acf_slot_sep (B : Word) {c n d k : Nat} (h : c + n ≤ d ∨ d + k ≤ c) (hc : c + n ≤ 0x2020)
    (hd : d + k ≤ 0x2020) : Sep (acSlot B c) n (acSlot B d) k :=
  sep_offsets B (by omega) (by omega) (by omega)

theorem acf_frW (F : Fr B 0x5A70) : Fr (B + 0x13F0 + 0xFFFFEC10) 0x3A50 := by
  have e : B + 0x13F0 + 0xFFFFEC10 = B := by
    rw [BitVec.add_assoc]
    exact (congrArg (B + ·) (by decide : (0x13F0 : Word) + 0xFFFFEC10 = 0)).trans (BitVec.add_zero B)
  rw [e]
  have := F.hi
  refine ⟨F.al, F.lo, by omega, ?_⟩
  have h := F.dsep.sub (c := 0) (l := 0x3A50 + 0x1A0) (by decide)
  rwa [add_ofNat_zero] at h

theorem acf_F16S (F : Fr B 0x5A70) {c n : Nat} (hc : c + n ≤ 0x2020) :
    Sep (B + 0x3A50 + 0xFFFFFFF0) 16 (acSlot B c) n :=
  sep_of_le (by rw [acf_F16N F, acf_slotN F (by omega)]; omega) (by rw [acf_slotN F (by omega)]; have := F.hi; omega)

theorem acf_F16W {x : Word} (h : Sep x 1 (B + 0xFFFFFE60) 0x5C10) : Sep (B + 0x3A50 + 0xFFFFFFF0) 16 x 1 := by
  have := h.subR (c := 0x3BE0) (l := 16) (by decide)
  rw [show B + 0xFFFFFE60 + BitVec.ofNat 32 0x3BE0 = B + 0x3A50 + 0xFFFFFFF0 by
    simp only [BitVec.add_assoc] <;> rfl] at this
  exact this.symm

theorem acf_hiF16 (F : Fr B 0x5A70) {x : Word} {len : Nat} (hx : 0x40000000 ≤ x.toNat)
    (hl : x.toNat + len ≤ 2 ^ 32) : Sep (B + 0x3A50 + 0xFFFFFFF0) 16 x len :=
  sep_of_le (by rw [acf_F16N F]; have := F.hi; omega) hl

theorem acf_svOut (F : Fr B 0x5A70) : SvOut (B + 0x13F0) (acSlot B 0xDD0) := by
  have := F.lo; have := F.hi; have := F.al
  have hs := acf_slotN F (c := 0xDD0) (by decide)
  have hSV : SV.toNat = 0x403ad502 := by decide
  refine ⟨?_, ?_, by rw [hs]; omega⟩
  · rw [acf_svB]; exact (sep_of_le (by rw [acf_lo F, hs]; omega) (by rw [hs]; omega)).symm
  · exact sep_of_le (by rw [hs, hSV]; omega) (by set_option maxRecDepth 100000 in decide)

theorem acf_svOutOk (F : Fr B 0x5A70) : SvOutOk (B + 0x13F0) (acSlot B 0xDD0) := by
  have := F.lo; have := F.hi; have := F.al
  have hs := acf_slotN F (c := 0xDD0) (by decide)
  have hSV : SV.toNat = 0x403ad502 := by decide
  refine ⟨?_, ?_, by rw [hs]; omega, by rw [hs]; omega⟩
  · rw [acf_svB]; exact (sep_of_le (by rw [acf_lo F, hs]; omega) (by rw [hs]; omega)).symm
  · exact sep_of_le (by rw [hs, hSV]; omega) (by set_option maxRecDepth 100000 in decide)

theorem acf_svIn (F : Fr B 0x5A70) : SvIn (B + 0x13F0) (acSlot B 0x108) 32 := by
  have := F.lo; have := F.hi
  have hs := acf_slotN F (c := 0x108) (by decide)
  refine ⟨?_, by rw [hs]; omega, by rw [hs]; omega⟩
  rw [acf_svB]; exact (sep_of_le (by rw [acf_lo F, hs]; omega) (by rw [hs]; omega)).symm

end Frame

section Result

variable {B r : Word}

theorem acf_rat (rlo : r.toNat + 0x12C ≤ 0x40000000) {k : Nat} (hk : k ≤ 0x12C) :
    (r + BitVec.ofNat 32 k).toNat = r.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem acf_ral (rlo : r.toNat + 0x12C ≤ 0x40000000) (ral : r.toNat % 4 = 0) {k : Nat} (hk : k ≤ 0x12C)
    (h4 : k % 4 = 0) : (r + BitVec.ofNat 32 k).toNat % 4 = 0 := by
  rw [acf_rat rlo hk]; omega

theorem acf_rC (rlo : r.toNat + 0x12C ≤ 0x40000000) {c n : Nat} (h : c + n ≤ 0x12C) {b : Word} {len : Nat}
    (hb : 0x40000000 ≤ b.toNat) (hl : b.toNat + len ≤ 2 ^ 32) : Sep (r + BitVec.ofNat 32 c) n b len :=
  sep_of_le (by rw [acf_rat rlo (by omega)]; omega) hl

theorem acf_rF (rsep : Sep r 0x12C (B + 0xFFFFFE60) 0x5C10) {c n : Nat} (h : c + n ≤ 0x12C) :
    Sep (r + BitVec.ofNat 32 c) n (B + 0x3A50 + 0xFFFFFFF0) 16 := by
  have := (rsep.sub (c := c) (l := n) h).subR (c := 0x3BE0) (l := 16) (by decide)
  rwa [show B + 0xFFFFFE60 + BitVec.ofNat 32 0x3BE0 = B + 0x3A50 + 0xFFFFFFF0 by
    simp only [BitVec.add_assoc] <;> rfl] at this

theorem acf_rS (rsep : Sep r 0x12C (B + 0xFFFFFE60) 0x5C10) {c n d k : Nat} (h : c + n ≤ 0x12C)
    (hd : d + k ≤ 0x2020) : Sep (r + BitVec.ofNat 32 c) n (acSlot B d) k := by
  have := (rsep.sub (c := c) (l := n) h).subR (c := 0x3BF0 + d) (l := k) (by omega)
  rwa [acf_wS B _] at this

theorem acf_rHi (rlo : r.toNat + 0x12C ≤ 0x40000000) {x : Word} (hx : 0x40000000 ≤ x.toNat) : Sep r 0x12C x 1 :=
  sep_of_le (by omega) (by have := x.isLt; omega)

theorem acf_rSl (rsep : Sep r 0x12C (B + 0xFFFFFE60) 0x5C10) {c : Nat} (hc : c < 0x2020) : Sep r 0x12C (acSlot B c) 1 := by
  have := acf_rS rsep (c := 0) (n := 0x12C) (d := c) (k := 1) (by decide) (by omega)
  rwa [add_ofNat_zero] at this

theorem acf_rx {x : Word} (h : Sep r 0x12C x 1) : ∀ k : Word, k.toNat < 0x12C → x ≠ r + k :=
  fun k hk e => h k.toNat hk 0 (by decide) (by rw [add_ofNat_zero, acf_ofNatToNat, e])

theorem acf_rne {a : Nat} (ha : a < 2 ^ 32) {k : Word} (hk : k.toNat ≠ a) : r + BitVec.ofNat 32 a ≠ r + k :=
  fun e => hk (by rw [← (BitVec.add_right_inj r).1 e, BitVec.toNat_ofNat]; omega)

end Result

/-! ### Copies, code, and saves -/

theorem acf_cb_out {M : Word → BitVec 8} {dst src x : Word} {N : Nat} (h : Sep dst N x 1) :
    copyBytes M dst src N x = M x :=
  copyBytes_sep h (Nat.le_refl N)

theorem acf_cb_in {M : Word → BitVec 8} {dst src : Word} {N i : Nat} (hi : i < N) (hN : N < 2 ^ 32) :
    copyBytes M dst src N (dst + BitVec.ofNat 32 i) = M (src + BitVec.ofNat 32 i) := by
  unfold copyBytes
  rw [BitVec.add_comm dst, BitVec.add_sub_cancel, ite_eq_left (by rw [BitVec.toNat_ofNat]; omega)]

theorem acf_codeKeep {M M' : Word → BitVec 8} {b : Word} {code : List Nat}
    (hK : ∀ x : Word, 0x40000000 ≤ x.toNat → M' x = M x) (h : CodeIn M b code)
    (hb : 0x40000000 ≤ b.toNat) (hl : b.toNat + code.length ≤ 2 ^ 32) : CodeIn M' b code := fun i hi => by
  have h2 : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have e := BitVec.toNat_add b (BitVec.ofNat 32 i)
  rw [h2, Nat.mod_eq_of_lt (by omega)] at e
  rw [hK _ (by rw [e]; omega)]
  exact h i hi

theorem acf_ld {M M' : Word → BitVec 8} {B : Word} {c : Nat}
    (hK : ∀ j, j < 4 → M' (acSlot B (c + j)) = M (acSlot B (c + j))) :
    memLoad32 M' (acSlot B c) = memLoad32 M (acSlot B c) :=
  memLoad32_congr fun j hj => by rw [acf_slot_add]; exact hK j hj

theorem acf_saves {M M' : Word → BitVec 8} {B : Word} {v : Nat → Word}
    (hK : ∀ c, 0x1FEC ≤ c → c < 0x2020 → M' (acSlot B c) = M (acSlot B c))
    (hS : ∀ k, k < 13 → memLoad32 M (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k) :
    ∀ k, k < 13 → memLoad32 M' (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k := fun k hk => by
  rw [← hS k hk]
  apply memLoad32_congr
  intro j hj
  rw [add_ofNat_assoc, show 0x5A6C - 4 * k + j = 0x3A50 + (0x201C - 4 * k + j) by omega]
  exact hK _ (by omega) (by omega)

/-! ### Values -/

theorem acf_zx (b : BitVec 8) : (b.zeroExtend 32).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_toNat_eq
  simp
  omega

theorem acf_time {bundle : Bundle} {root : SigstoreRoot} {d : Bytes} {vv : Verified}
    (h : sigstoreVerify bundle root d = some vv) :
    ∃ tsa, tsa ∈ root.tsas ∧ vv.signedTime ≤ tsa.window.notAfter := by
  unfold sigstoreVerify at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, require_eq_some, Bool.and_eq_true, Window.contains,
    decide_eq_true_eq] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ts, _, tsa, htsa, _, _, _, _, _, _, _, _, _, _, _, hw, hv⟩ := h
  refine ⟨tsa, List.mem_of_find?_eq_some htsa, ?_⟩
  simp only [Option.pure_def, Option.some.injEq] at hv
  subst hv
  exact hw.1.2.2

theorem acf_time_lt {B a : Word} {M : Word → BitVec 8} {root : SigstoreRoot} (R : SvRootAt B M a root)
    {bundle : Bundle} {d : Bytes} {vv : Verified} (h : sigstoreVerify bundle root d = some vv) :
    vv.signedTime < 2 ^ 64 := by
  obtain ⟨tsa, hm, hle⟩ := acf_time h
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hm
  have := (R.tsas.2.1 i hi).notAfter.1
  omega

theorem acf_lex {T X : Nat} (hT : T < 2 ^ 64) (hX : X < 2 ^ 64) :
    (if BitVec.ofNat 32 (T / 2 ^ 32) = BitVec.ofNat 32 (X / 2 ^ 32) then
      BitVec.ult (BitVec.ofNat 32 X) (BitVec.ofNat 32 (T % 2 ^ 32))
    else BitVec.ult (BitVec.ofNat 32 (X / 2 ^ 32)) (BitVec.ofNat 32 (T / 2 ^ 32))) = decide (X < T) := by
  have h1 : T / 2 ^ 32 < 2 ^ 32 := by omega
  have h2 : X / 2 ^ 32 < 2 ^ 32 := by omega
  split
  · rename_i h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_decide]
    exact ⟨fun _ => by omega, fun _ => by omega⟩
  · rename_i h
    have : T / 2 ^ 32 ≠ X / 2 ^ 32 := fun e => h (by rw [e])
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_decide]
    exact ⟨fun _ => by omega, fun _ => by omega⟩

/-! ### Blocks -/

/-- From 0x1A4A: load `Ok`/`Err`'s discriminant. -/
def acfA : List BInstr := [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x91, .lbu a0 a0 0x540]

/-- From 0x1A58: load the error's code. -/
def acfE : List BInstr := [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x91, .lbu (8 : Fin 32) a0 0x541]

/-- At 0x1A6A: the code to `s5`. -/
def acfJ : List BInstr := [.alu .add (21 : Fin 32) x0 (8 : Fin 32)]

/-- From 0x1A70: load the signing time and the expiry's high word. -/
def acfO : List BInstr :=
  [.aluImm .add a0 sp 0x7FF, .aluImm .add a0 a0 0x91, .lw (8 : Fin 32) a0 0x54C, .lw (18 : Fin 32) a0 0x548,
   .lw a0 sp 0x24]

/-- From 0x1A86: compare the high words. -/
def acfN : List BInstr := [.lw a0 sp 0x24, .alu .sltu a0 a0 (8 : Fin 32)]

/-- From 0x1A8E: compare the low words. -/
def acfT : List BInstr := [.lw a0 sp 0x20, .alu .sltu a0 a0 (18 : Fin 32)]

/-- At 0x1A96: the code 0x25. -/
def acfX : List BInstr := [.aluImm .add (8 : Fin 32) x0 0x25]

/-- From 0x1A9C: the arguments of the first `memcpy`. -/
def acfS1 : List BInstr :=
  [.lw (9 : Fin 32) sp 0x40, .aluImm .add a0 (9 : Fin 32) 0x1, .aluImm .add a1 sp 0x238, .aluImm .add a2 x0 0xB]

/-- From 0x1AAE: the arguments of the second `memcpy`. -/
def acfS2 : List BInstr := [.aluImm .add a0 (9 : Fin 32) 0xD, .aluImm .add a1 sp 0x139, .aluImm .add a2 x0 0xFF]

/-- From 0x1AC2: the slot's bytes, `s11`, and the signing time. -/
def acfB1 : List BInstr :=
  [.lbu a0 sp 0x136, .lbu a1 sp 0x137, .lbu a2 sp 0x138, .sb (9 : Fin 32) (27 : Fin 32) 0x10C,
   .sb (9 : Fin 32) a0 0x10D, .sb (9 : Fin 32) a1 0x10E, .sb (9 : Fin 32) a2 0x10F,
   .sw (9 : Fin 32) (18 : Fin 32) 0x110, .sw (9 : Fin 32) (8 : Fin 32) 0x114, .sb (9 : Fin 32) (27 : Fin 32) 0x118]

/-- From 0x1AEA: the manifest's word and the codes. -/
def acfB2 : List BInstr :=
  [.lw a0 sp 0x44, .sw (9 : Fin 32) a0 0x120, .sb (9 : Fin 32) (21 : Fin 32) 0x0, .sb (9 : Fin 32) (25 : Fin 32) 0xC,
   .sb (9 : Fin 32) (27 : Fin 32) 0x128]

theorem acfA_end : blockEnd bootMainClosure0Code 0x1A4A acfA = some 0x1A56 :=
  blockEnd_cons' ac_at_1a4a rfl <| blockEnd_cons' ac_at_1a4e rfl <| blockEnd_cons' ac_at_1a52 rfl rfl

theorem acfE_end : blockEnd bootMainClosure0Code 0x1A58 acfE = some 0x1A64 :=
  blockEnd_cons' ac_at_1a58 rfl <| blockEnd_cons' ac_at_1a5c rfl <| blockEnd_cons' ac_at_1a60 rfl rfl

theorem acfJ_end : blockEnd bootMainClosure0Code 0x1A6A acfJ = some 0x1A6C :=
  blockEnd_cons' ac_at_1a6a rfl rfl

theorem acfO_end : blockEnd bootMainClosure0Code 0x1A70 acfO = some 0x1A82 :=
  blockEnd_cons' ac_at_1a70 rfl <| blockEnd_cons' ac_at_1a74 rfl <| blockEnd_cons' ac_at_1a78 rfl <|
  blockEnd_cons' ac_at_1a7c rfl <| blockEnd_cons' ac_at_1a80 rfl rfl

theorem acfN_end : blockEnd bootMainClosure0Code 0x1A86 acfN = some 0x1A8C :=
  blockEnd_cons' ac_at_1a86 rfl <| blockEnd_cons' ac_at_1a88 rfl rfl

theorem acfT_end : blockEnd bootMainClosure0Code 0x1A8E acfT = some 0x1A94 :=
  blockEnd_cons' ac_at_1a8e rfl <| blockEnd_cons' ac_at_1a90 rfl rfl

theorem acfX_end : blockEnd bootMainClosure0Code 0x1A96 acfX = some 0x1A9A :=
  blockEnd_cons' ac_at_1a96 rfl rfl

theorem acfS1_end : blockEnd bootMainClosure0Code 0x1A9C acfS1 = some 0x1AA6 :=
  blockEnd_cons' ac_at_1a9c rfl <| blockEnd_cons' ac_at_1a9e rfl <| blockEnd_cons' ac_at_1aa2 rfl <|
  blockEnd_cons' ac_at_1aa4 rfl rfl

theorem acfS2_end : blockEnd bootMainClosure0Code 0x1AAE acfS2 = some 0x1ABA :=
  blockEnd_cons' ac_at_1aae rfl <| blockEnd_cons' ac_at_1ab2 rfl <| blockEnd_cons' ac_at_1ab6 rfl rfl

theorem acfB1_end : blockEnd bootMainClosure0Code 0x1AC2 acfB1 = some 0x1AEA :=
  blockEnd_cons' ac_at_1ac2 rfl <| blockEnd_cons' ac_at_1ac6 rfl <| blockEnd_cons' ac_at_1aca rfl <|
  blockEnd_cons' ac_at_1ace rfl <| blockEnd_cons' ac_at_1ad2 rfl <| blockEnd_cons' ac_at_1ad6 rfl <|
  blockEnd_cons' ac_at_1ada rfl <| blockEnd_cons' ac_at_1ade rfl <| blockEnd_cons' ac_at_1ae2 rfl <|
  blockEnd_cons' ac_at_1ae6 rfl rfl

theorem acfB2_end : blockEnd bootMainClosure0Code 0x1AEA acfB2 = some 0x1AFC :=
  blockEnd_cons' ac_at_1aea rfl <| blockEnd_cons' ac_at_1aec rfl <| blockEnd_cons' ac_at_1af0 rfl <|
  blockEnd_cons' ac_at_1af4 rfl <| blockEnd_cons' ac_at_1af8 rfl rfl

section B1
variable {M M1 : Word → BitVec 8} {f : Fin 32 → Word} {r : Word}

theorem acf_b1_10c (hr : f 9 = r) (hM : (runBlock acfB1 (M, f)).1 = M1) :
    M1 (r + 0x10C) = (f 27).extractLsb' 0 8 := by
  subst hM
  simp +decide only [runBlock, BInstr.run, acfB1, upd, ↓reduceIte]
  rw [hr]
  simp (config := {decide := true}) only [memStore32, memStore8, BitVec.add_assoc, BitVec.reduceAdd,
    BitVec.add_right_inj, ite_false, ite_true]

theorem acf_b1_10d (hr : f 9 = r) (hM : (runBlock acfB1 (M, f)).1 = M1) :
    M1 (r + 0x10D) = M (f sp + 0x136) ∧ M1 (r + 0x10E) = M (f sp + 0x137) ∧ M1 (r + 0x10F) = M (f sp + 0x138) := by
  subst hM
  simp +decide only [runBlock, BInstr.run, acfB1, upd, ↓reduceIte]
  rw [hr]
  simp (config := {decide := true}) only [memStore32, memStore8, BitVec.add_assoc, BitVec.reduceAdd,
    BitVec.add_right_inj, ite_false, ite_true, acf_zx, and_self]

theorem acf_b1_110 (hr : f 9 = r) (hM : (runBlock acfB1 (M, f)).1 = M1) :
    memLoad32 M1 (r + 0x110) = f 18 ∧ memLoad32 M1 (r + 0x114) = f 8 ∧ M1 (r + 0x118) = (f 27).extractLsb' 0 8 := by
  subst hM
  simp +decide only [runBlock, BInstr.run, acfB1, upd, ↓reduceIte]
  rw [hr]
  simp (config := {decide := true}) only [memLoad32, memStore32, memStore8, BitVec.add_assoc, BitVec.reduceAdd,
    BitVec.add_right_inj, ite_false, ite_true, bytes_reassemble, and_self]

/-- The first block stores only at `r + 0x10C` to `r + 0x118`. -/
theorem acf_b1_keep (hr : f 9 = r) (hM : (runBlock acfB1 (M, f)).1 = M1) (x : Word)
    (h : ∀ k : Word, 0x10C ≤ k.toNat → k.toNat < 0x119 → (x = r + k) = False) : M1 x = M x := by
  subst hM
  simp +decide only [runBlock, BInstr.run, acfB1, upd, ↓reduceIte]
  rw [hr]
  simp only [memStore32, memStore8, BitVec.add_assoc, BitVec.reduceAdd]
  simp (disch := decide) only [h, ite_false]

end B1

section B2
variable {M M2 : Word → BitVec 8} {f : Fin 32 → Word} {r : Word}

theorem acf_b2_120 (hr : f 9 = r) (hM : (runBlock acfB2 (M, f)).1 = M2) :
    memLoad32 M2 (r + 0x120) = memLoad32 M (f sp + 0x44) := by
  subst hM
  simp +decide only [runBlock, BInstr.run, acfB2, upd, ↓reduceIte]
  rw [hr]
  generalize memLoad32 M (f sp + 0x44) = w
  simp (config := {decide := true}) only [memLoad32, memStore32, memStore8, BitVec.add_assoc, BitVec.reduceAdd,
    BitVec.add_right_inj, ite_false, ite_true, bytes_reassemble]

theorem acf_b2_bytes (hr : f 9 = r) (hM : (runBlock acfB2 (M, f)).1 = M2) :
    M2 (r + 0) = (f 21).extractLsb' 0 8 ∧ M2 (r + 0xC) = (f 25).extractLsb' 0 8 ∧
      M2 (r + 0x128) = (f 27).extractLsb' 0 8 := by
  subst hM
  simp +decide only [runBlock, BInstr.run, acfB2, upd, ↓reduceIte]
  rw [hr]
  simp (config := {decide := true}) only [memStore32, memStore8, BitVec.add_assoc, BitVec.reduceAdd,
    BitVec.add_right_inj, ite_false, ite_true, and_self]

/-- The second block stores only at `r`, `r + 0xC`, `r + 0x120` to
`r + 0x123`, and `r + 0x128`. -/
theorem acf_b2_keep (hr : f 9 = r) (hM : (runBlock acfB2 (M, f)).1 = M2) (x : Word)
    (h : ∀ k : Word, (k.toNat = 0 ∨ k.toNat = 0xC ∨ (0x120 ≤ k.toNat ∧ k.toNat < 0x129)) → (x = r + k) = False) :
    M2 x = M x := by
  subst hM
  simp +decide only [runBlock, BInstr.run, acfB2, upd, ↓reduceIte]
  rw [hr]
  simp only [memStore32, memStore8, BitVec.add_assoc, BitVec.reduceAdd]
  simp (disch := decide) only [h, ite_false]

end B2

/-! ### Paths -/

section Paths

variable {M : Word → BitVec 8} {m : Machine} {B : Word}

/-- 0x1A4A to the branch on the discriminant. -/
theorem acf_seg_tag (C : CodeIn M AC bootMainClosure0Code) (s : St M AC m 0x1A4A (reg m))
    (rsp : reg m sp = B + 0x3A50) :
    ∃ m', Steps m m' ∧ St M AC m' 0x1A56 (reg m') ∧ reg m' a0 = (M (acSlot B 0xDD0)).zeroExtend 32 ∧
      ∀ q : Fin 32, q.val ≠ 10 → reg m' q = reg m q := by
  have hz := s.zero
  obtain ⟨m1, c1, u1⟩ := s.block acfA C acfA_end ⟨trivial, trivial, trivial, trivial⟩
  refine ⟨m1, c1, ⟨u1.pc, u1.mem, fun _ => rfl⟩, ?_, fun q hq => ?_⟩
  · rw [u1.regs]
    show (M (reg m sp + 0x7FF + 0x91 + 0x540)).zeroExtend 32 = _
    rw [rsp]
    exact congrArg (fun a => (M a).zeroExtend 32) (by simp only [BitVec.add_assoc] <;> rfl)
  · rw [u1.regs, runBlock_reg _ _ _ q hz (by simp only [acfA]; revert hq; revert q; decide)]

/-- `Err`: 0x1A56 to 0x1A6A, with the error's code in `s0`. -/
theorem acf_seg_err (C : CodeIn M AC bootMainClosure0Code) (s : St M AC m 0x1A56 (reg m))
    (rsp : reg m sp = B + 0x3A50) (ha : reg m a0 ≠ 0) :
    ∃ m', Steps m m' ∧ St M AC m' 0x1A6A (reg m') ∧ reg m' (8 : Fin 32) = (M (acSlot B 0xDD1)).zeroExtend 32 ∧
      ∀ q : Fin 32, q.val ≠ 10 → q.val ≠ 8 → reg m' q = reg m q := by
  have hz := s.zero
  obtain ⟨m1, e1, t1⟩ := s.notTaken C 0x1A58 ac_at_1a56 (by decide)
    (by show (reg m a0 == reg m 0) = false; rw [hz]; simpa using ha)
  obtain ⟨m2, c2, u2⟩ := t1.block acfE C acfE_end ⟨trivial, trivial, trivial, trivial⟩
  obtain ⟨m3, e3, t3⟩ := u2.jump C ac_at_1a64 (off' := 0x1A6A) (by decide) (by rw [u2.pc]; decide)
  refine ⟨m3, .cons e1 (c2.trans (.cons e3 (.refl _))), ⟨t3.pc, t3.mem, fun _ => rfl⟩, ?_, fun q h0 h1 => ?_⟩
  · rw [t3.regs]
    show (M (reg m sp + 0x7FF + 0x91 + 0x541)).zeroExtend 32 = _
    rw [rsp]
    exact congrArg (fun a => (M a).zeroExtend 32) (by simp only [BitVec.add_assoc] <;> rfl)
  · rw [t3.regs, runBlock_reg _ _ _ q hz (by simp only [acfE]; revert h0 h1; revert q; decide)]

/-- 0x1A6A to the exit at 0x7D6, with the code in `s5`. -/
theorem acf_seg_7d6 (C : CodeIn M AC bootMainClosure0Code) (s : St M AC m 0x1A6A (reg m)) :
    ∃ m', Steps m m' ∧ St M AC m' 0x7D6 (reg m') ∧ reg m' (21 : Fin 32) = reg m (8 : Fin 32) ∧
      ∀ q : Fin 32, q.val ≠ 21 → reg m' q = reg m q := by
  have hz := s.zero
  obtain ⟨m1, c1, u1⟩ := s.block acfJ C acfJ_end ⟨trivial, trivial⟩
  obtain ⟨m2, e2, t2⟩ := u1.jump C ac_at_1a6c (off' := 0x7D6) (by decide) (by rw [u1.pc]; decide)
  refine ⟨m2, c1.trans (.cons e2 (.refl _)), ⟨t2.pc, t2.mem, fun _ => rfl⟩, ?_, fun q h0 => ?_⟩
  · rw [t2.regs]; show reg m 0 + reg m 8 = _; rw [hz]; exact BitVec.zero_add _
  · rw [t2.regs, runBlock_reg _ _ _ q hz (by simp only [acfJ]; revert h0; revert q; decide)]

/-- `Ok`: 0x1A56 to the branch on the expiry at 0x1A94, with `a0` set when
the expiry `X` is earlier than the signing time `T`. -/
theorem acf_seg_cmp {T X : Nat} (C : CodeIn M AC bootMainClosure0Code) (F : Fr B 0x5A70)
    (s : St M AC m 0x1A56 (reg m)) (rsp : reg m sp = B + 0x3A50) (ha : reg m a0 = 0)
    (hlo : memLoad32 M (acSlot B 0xDD8) = BitVec.ofNat 32 (T % 2 ^ 32))
    (hhi : memLoad32 M (acSlot B 0xDDC) = BitVec.ofNat 32 (T / 2 ^ 32))
    (hX : SvU64At M (acSlot B 0x20) X) (hT : T < 2 ^ 64) :
    ∃ m', Steps m m' ∧ St M AC m' 0x1A94 (reg m') ∧ reg m' a0 = (if X < T then 1 else 0) ∧
      reg m' (8 : Fin 32) = BitVec.ofNat 32 (T / 2 ^ 32) ∧ reg m' (18 : Fin 32) = BitVec.ofNat 32 (T % 2 ^ 32) ∧
      ∀ q : Fin 32, q.val ≠ 10 → q.val ≠ 8 → q.val ≠ 18 → reg m' q = reg m q := by
  have hz := s.zero
  have e1 : B + 0x3A50 + 0x7FF + 0x91 + 0x54C = acSlot B 0xDDC := by simp only [BitVec.add_assoc] <;> rfl
  have e2 : B + 0x3A50 + 0x7FF + 0x91 + 0x548 = acSlot B 0xDD8 := by simp only [BitVec.add_assoc] <;> rfl
  have e24 : B + 0x3A50 + 0x24 = acSlot B 0x24 := acf_sp B 0x24
  have e20 : B + 0x3A50 + 0x20 = acSlot B 0x20 := acf_sp B 0x20
  obtain ⟨m1, d1, t1⟩ := s.taken C 0x1A70 ac_at_1a56 (by decide)
    (by show (reg m a0 == reg m 0) = true; rw [hz, ha]; rfl)
  obtain ⟨m2, c2, u2⟩ := t1.block acfO C acfO_end
    ⟨trivial, trivial,
     by show (reg m sp + 0x7FF + 0x91 + 0x54C).toNat % 4 = 0; rw [rsp, e1]; exact acf_al F (by decide) (by decide),
     by show (reg m sp + 0x7FF + 0x91 + 0x548).toNat % 4 = 0; rw [rsp, e2]; exact acf_al F (by decide) (by decide),
     by show (reg m sp + 0x24).toNat % 4 = 0; rw [rsp, e24]; exact acf_al F (by decide) (by decide), trivial⟩
  have hX4 : memLoad32 M (acSlot B 0x24) = BitVec.ofNat 32 (X / 2 ^ 32) := by
    rw [← show acSlot B 0x20 + 4 = acSlot B 0x24 from acf_slot_add B 0x20 4]; exact hX.2.2
  have r8 : reg m2 (8 : Fin 32) = BitVec.ofNat 32 (T / 2 ^ 32) := by
    rw [u2.regs]; show memLoad32 M (reg m sp + 0x7FF + 0x91 + 0x54C) = _; rw [rsp, e1, hhi]
  have r18 : reg m2 (18 : Fin 32) = BitVec.ofNat 32 (T % 2 ^ 32) := by
    rw [u2.regs]; show memLoad32 M (reg m sp + 0x7FF + 0x91 + 0x548) = _; rw [rsp, e2, hlo]
  have r10 : reg m2 a0 = BitVec.ofNat 32 (X / 2 ^ 32) := by
    rw [u2.regs]; show memLoad32 M (reg m sp + 0x24) = _; rw [rsp, e24, hX4]
  have k2 : ∀ q : Fin 32, q.val ≠ 10 → q.val ≠ 8 → q.val ≠ 18 → reg m2 q = reg m q := fun q h0 h1 h2 => by
    rw [u2.regs, runBlock_reg _ _ _ q hz (by simp only [acfO]; revert h0 h1 h2; revert q; decide)]
  have t2 : St M AC m2 0x1A82 (reg m2) := ⟨u2.pc, u2.mem, fun _ => rfl⟩
  have hz2 := t2.zero
  have sp2 : reg m2 sp = B + 0x3A50 := by rw [k2 sp (by decide) (by decide) (by decide), rsp]
  have L := acf_lex hT hX.1
  obtain heq | heq := Decidable.em (BitVec.ofNat 32 (T / 2 ^ 32) = BitVec.ofNat 32 (X / 2 ^ 32))
  · rw [ite_eq_left heq] at L
    obtain ⟨m3, d3, t3⟩ := t2.taken C 0x1A8E ac_at_1a82 (by decide)
      (by show (reg m2 8 == reg m2 a0) = true; rw [r8, r10, heq]; exact beq_iff_eq.mpr rfl)
    obtain ⟨m4, c4, u4⟩ := t3.block acfT C acfT_end
      ⟨by show (reg m2 sp + 0x20).toNat % 4 = 0; rw [sp2, e20]; exact acf_al F (by decide) (by decide),
       trivial, trivial⟩
    have k4 : ∀ q : Fin 32, q.val ≠ 10 → reg m4 q = reg m2 q := fun q h0 => by
      rw [u4.regs, runBlock_reg _ _ _ q hz2 (by simp only [acfT]; revert h0; revert q; decide)]
    refine ⟨m4, .cons d1 (c2.trans (.cons d3 c4)), ⟨u4.pc, u4.mem, fun _ => rfl⟩, ?_,
      by rw [k4 _ (by decide), r8], by rw [k4 _ (by decide), r18],
      fun q h0 h1 h2 => by rw [k4 q h0, k2 q h0 h1 h2]⟩
    rw [u4.regs]
    show (if BitVec.ult (memLoad32 M (reg m2 sp + 0x20)) (reg m2 18) then 1 else 0) = _
    rw [sp2, e20, hX.2.1, r18, L]
    simp only [decide_eq_true_eq]
  · rw [ite_eq_right heq] at L
    obtain ⟨m3, d3, t3⟩ := t2.notTaken C 0x1A86 ac_at_1a82 (by decide)
      (by show (reg m2 8 == reg m2 a0) = false; rw [r8, r10]; simpa using heq)
    obtain ⟨m4, c4, u4⟩ := t3.block acfN C acfN_end
      ⟨by show (reg m2 sp + 0x24).toNat % 4 = 0; rw [sp2, e24]; exact acf_al F (by decide) (by decide),
       trivial, trivial⟩
    obtain ⟨m5, d5, t5⟩ := u4.jump C ac_at_1a8c (off' := 0x1A94) (by decide) (by rw [u4.pc]; decide)
    have k5 : ∀ q : Fin 32, q.val ≠ 10 → reg m5 q = reg m2 q := fun q h0 => by
      rw [t5.regs, runBlock_reg _ _ _ q hz2 (by simp only [acfN]; revert h0; revert q; decide)]
    refine ⟨m5, .cons d1 (c2.trans (.cons d3 (c4.trans (.cons d5 (.refl _))))), ⟨t5.pc, t5.mem, fun _ => rfl⟩,
      ?_, by rw [k5 _ (by decide), r8], by rw [k5 _ (by decide), r18],
      fun q h0 h1 h2 => by rw [k5 q h0, k2 q h0 h1 h2]⟩
    rw [t5.regs]
    show (if BitVec.ult (memLoad32 M (reg m2 sp + 0x24)) (reg m2 8) then 1 else 0) = _
    rw [sp2, e24, hX4, r8, L]
    simp only [decide_eq_true_eq]

/-- Past the expiry: 0x1A94 to 0x1A6A with the code 0x25 in `s0`. -/
theorem acf_seg_late (C : CodeIn M AC bootMainClosure0Code) (s : St M AC m 0x1A94 (reg m)) (ha : reg m a0 ≠ 0) :
    ∃ m', Steps m m' ∧ St M AC m' 0x1A6A (reg m') ∧ reg m' (8 : Fin 32) = 0x25 ∧
      ∀ q : Fin 32, q.val ≠ 8 → reg m' q = reg m q := by
  have hz := s.zero
  obtain ⟨m1, e1, t1⟩ := s.notTaken C 0x1A96 ac_at_1a94 (by decide)
    (by show (reg m a0 == reg m 0) = false; rw [hz]; simpa using ha)
  obtain ⟨m2, c2, u2⟩ := t1.block acfX C acfX_end ⟨trivial, trivial⟩
  obtain ⟨m3, e3, t3⟩ := u2.jump C ac_at_1a9a (off' := 0x1A6A) (by decide) (by rw [u2.pc]; decide)
  refine ⟨m3, .cons e1 (c2.trans (.cons e3 (.refl _))), ⟨t3.pc, t3.mem, fun _ => rfl⟩, ?_, fun q h0 => ?_⟩
  · rw [t3.regs]; show reg m 0 + 0x25 = _; rw [hz]; decide
  · rw [t3.regs, runBlock_reg _ _ _ q hz (by simp only [acfX]; revert h0; revert q; decide)]

end Paths

/-- What the success path leaves, from memory `M` and registers `f` at 0x1A9C. -/
def AcfWrite (B r : Word) (M : Word → BitVec 8) (f : Fin 32 → Word) (M' : Word → BitVec 8) : Prop :=
  M' (r + 0) = (f 21).extractLsb' 0 8 ∧
  (∀ i, i < 11 → M' (r + BitVec.ofNat 32 (1 + i)) = M (acSlot B (0x238 + i))) ∧
  M' (r + 0xC) = (f 25).extractLsb' 0 8 ∧
  (∀ i, i < 0xFF → M' (r + BitVec.ofNat 32 (0xD + i)) = M (acSlot B (0x139 + i))) ∧
  M' (r + 0x10C) = (f 27).extractLsb' 0 8 ∧
  (∀ i, i < 3 → M' (r + BitVec.ofNat 32 (0x10D + i)) = M (acSlot B (0x136 + i))) ∧
  memLoad32 M' (r + 0x110) = f 18 ∧ memLoad32 M' (r + 0x114) = f 8 ∧
  M' (r + 0x118) = (f 27).extractLsb' 0 8 ∧
  memLoad32 M' (r + 0x120) = memLoad32 M (acSlot B 0x44) ∧
  M' (r + 0x128) = (f 27).extractLsb' 0 8 ∧
  ∀ x, Sep x 1 (B + 0xFFFFFE60) 0x5C10 → Sep x 1 r 0x12C → M' x = M x

set_option maxRecDepth 100000 in
theorem acf_mc {M : Word → BitVec 8} {B r : Word} (F : Fr B 0x5A70) (rsep : Sep r 0x12C (B + 0xFFFFFE60) 0x5C10)
    (rlo : r.toNat + 0x12C ≤ 0x40000000) (CB : CodeIn M (MCS + 8) memcpyBodyCode) {c d n : Nat}
    (hc : c + n ≤ 0x12C) (hd : d + n ≤ 0x2020) :
    McEnv M (MCS + 8) (r + BitVec.ofNat 32 c) (acSlot B d) (B + 0x3A50 + 0xFFFFFFF0) n := by
  have hMB : 0x40000000 ≤ (MCS + 8).toNat := by decide
  have hMBl : (MCS + 8).toNat + memcpyBodyCode.length ≤ 2 ^ 32 := by decide
  have := F.al; have := F.hi
  exact ⟨CB, acf_rC rlo hc hMB hMBl, acf_hiF16 F hMB hMBl, acf_rF rsep hc, (acf_F16S F hd).symm, acf_rS rsep hc hd,
    by rw [acf_F16N F]; omega, by rw [acf_F16N F]; omega, by rw [acf_rat rlo (by omega)]; omega,
    by rw [acf_slotN F (by omega)]; omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The success path, from 0x1A9C to the closure's return. -/
theorem acf_seg_write {M : Word → BitVec 8} {m : Machine} {B r : Word} {v : Nat → Word}
    (C : CodeIn M AC bootMainClosure0Code) (F : Fr B 0x5A70)
    (CS : CodeIn M MCS memcpyStubCode) (CB : CodeIn M (MCS + 8) memcpyBodyCode)
    (s : St M AC m 0x1A9C (reg m)) (rsp : reg m sp = B + 0x3A50) (hres : memLoad32 M (acSlot B 0x40) = r)
    (hS : ∀ k, k < 13 → memLoad32 M (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k) (hret : v 0 &&& ~~~1 = v 0)
    (rsep : Sep r 0x12C (B + 0xFFFFFE60) 0x5C10) (ral : r.toNat % 4 = 0) (rlo : r.toNat + 0x12C ≤ 0x40000000) :
    AcRet B v m (AcfWrite B r M (reg m)) := by
  have hz := s.zero
  have hAC : 0x40000000 ≤ AC.toNat := by decide
  have hACl : AC.toNat + bootMainClosure0Code.length ≤ 2 ^ 32 := by decide
  have hMS : 0x40000000 ≤ MCS.toNat := by decide
  have hMSl : MCS.toNat + memcpyStubCode.length ≤ 2 ^ 32 := by decide
  have hMB : 0x40000000 ≤ (MCS + 8).toNat := by decide
  have hMBl : (MCS + 8).toNat + memcpyBodyCode.length ≤ 2 ^ 32 := by decide
  have hi16 : ∀ x : Word, 0x40000000 ≤ x.toNat → Sep (B + 0x3A50 + 0xFFFFFFF0) 16 x 1 := fun x hx =>
    acf_hiF16 F hx (by have := x.isLt; omega)
  -- The arguments of the first copy.
  obtain ⟨m1, c1, u1⟩ := s.block acfS1 C acfS1_end (by
    simp only [BlockOk, BInstr.ok, acfS1]; simp +decide only [and_true]
    rw [rsp, acf_sp40]; exact acf_al F (by decide) (by decide))
  have t1 : St M AC m1 0x1AA6 (reg m1) := ⟨u1.pc, u1.mem, fun _ => rfl⟩
  have hz1 := t1.zero
  have r9_1 : reg m1 (9 : Fin 32) = r := by
    rw [u1.regs]; show memLoad32 M (reg m sp + 0x40) = r; rw [rsp, acf_sp40, hres]
  have a0_1 : reg m1 a0 = r + BitVec.ofNat 32 1 := by
    rw [u1.regs]; show memLoad32 M (reg m sp + 0x40) + 1 = _; rw [rsp, acf_sp40, hres]; rfl
  have a1_1 : reg m1 a1 = acSlot B 0x238 := by
    rw [u1.regs]; show reg m sp + 0x238 = _; rw [rsp]; exact acf_sp B 0x238
  have a2_1 : reg m1 a2 = BitVec.ofNat 32 0xB := by
    rw [u1.regs]; show reg m 0 + 0xB = _; rw [hz]; rfl
  obtain ⟨m2, c2, pc2, mem2, regs2⟩ := t1.callRa (cb := MCS) C ac_at_1aa6 ac_at_1aaa (by decide) (by decide)
  have sp2 : reg m2 sp = B + 0x3A50 := by
    rw [regs2, updz hz1 (by decide), u1.regs, runBlock_reg _ _ _ _ hz (by decide), rsp]
  obtain ⟨m3, c3, pc3, sp3, -, mem3, k3⟩ := memcpy_correct m2 MCS (AC + BitVec.ofNat 32 0x1AAE)
    (r + BitVec.ofNat 32 1) (acSlot B 0x238) 0xB
    (fun i hi => by show m2.mem _ = _; rw [mem2]; exact CS i hi) (by decide) pc2
    (by rw [regs2, updz hz1 (by decide), a0_1]) (by rw [regs2, updz hz1 (by decide), a1_1])
    (by rw [regs2, updz hz1 (by decide), a2_1]) (by rw [regs2]; rfl) (by decide)
    (by rw [mem2, sp2]; exact acf_mc F rsep rlo CB (by decide) (by decide))
  rw [sp2] at mem3
  have K3 : ∀ x, Sep (B + 0x3A50 + 0xFFFFFFF0) 16 x 1 → Sep r 0x12C x 1 → m3.mem x = M x := fun x h1 h2 => by
    rw [mem3 x h1, mem2]; exact acf_cb_out (h2.sub (c := 1) (l := 0xB) (by decide))
  have KH3 : ∀ x : Word, 0x40000000 ≤ x.toNat → m3.mem x = M x := fun x hx => K3 x (hi16 x hx) (acf_rHi rlo hx)
  have C3 := acf_codeKeep KH3 C hAC hACl
  have CS3 := acf_codeKeep KH3 CS hMS hMSl
  have CB3 := acf_codeKeep KH3 CB hMB hMBl
  have k3' : ∀ q : Fin 32, (q.val = 3 ∨ q.val = 4 ∨ q.val = 8 ∨ q.val = 9 ∨ (18 ≤ q.val ∧ q.val ≤ 27)) →
      reg m3 q = reg m2 q := fun q hq => by
    apply k3 <;> rintro rfl <;> revert hq <;> decide
  have t3 : St m3.mem AC m3 0x1AAE (reg m3) := ⟨pc3, rfl, fun _ => rfl⟩
  have hz3 := t3.zero
  have r9_3 : reg m3 (9 : Fin 32) = r := by rw [k3' _ (by decide), regs2, updz hz1 (by decide), r9_1]
  have sp3' : reg m3 sp = B + 0x3A50 := by rw [sp3, sp2]
  -- The arguments of the second copy.
  obtain ⟨m4, c4, u4⟩ := t3.block acfS2 C3 acfS2_end ⟨trivial, trivial, trivial, trivial⟩
  have t4 : St m3.mem AC m4 0x1ABA (reg m4) := ⟨u4.pc, u4.mem, fun _ => rfl⟩
  have hz4 := t4.zero
  have a0_4 : reg m4 a0 = r + BitVec.ofNat 32 0xD := by
    rw [u4.regs]; show reg m3 9 + 0xD = _; rw [r9_3]; rfl
  have a1_4 : reg m4 a1 = acSlot B 0x139 := by
    rw [u4.regs]; show reg m3 sp + 0x139 = _; rw [sp3']; exact acf_sp B 0x139
  have a2_4 : reg m4 a2 = BitVec.ofNat 32 0xFF := by
    rw [u4.regs]; show reg m3 0 + 0xFF = _; rw [hz3]; rfl
  obtain ⟨m5, c5, pc5, mem5, regs5⟩ := t4.callRa (cb := MCS) C3 ac_at_1aba ac_at_1abe (by decide) (by decide)
  have sp5 : reg m5 sp = B + 0x3A50 := by
    rw [regs5, updz hz4 (by decide), u4.regs, runBlock_reg _ _ _ _ hz3 (by decide), sp3']
  obtain ⟨m6, c6, pc6, sp6, -, mem6, k6⟩ := memcpy_correct m5 MCS (AC + BitVec.ofNat 32 0x1AC2)
    (r + BitVec.ofNat 32 0xD) (acSlot B 0x139) 0xFF
    (fun i hi => by show m5.mem _ = _; rw [mem5]; exact CS3 i hi) (by decide) pc5
    (by rw [regs5, updz hz4 (by decide), a0_4]) (by rw [regs5, updz hz4 (by decide), a1_4])
    (by rw [regs5, updz hz4 (by decide), a2_4]) (by rw [regs5]; rfl) (by decide)
    (by rw [mem5, sp5]; exact acf_mc F rsep rlo CB3 (by decide) (by decide))
  rw [sp5] at mem6
  have K6 : ∀ x, Sep (B + 0x3A50 + 0xFFFFFFF0) 16 x 1 → Sep r 0x12C x 1 → m6.mem x = M x := fun x h1 h2 => by
    rw [mem6 x h1, mem5, acf_cb_out (h2.sub (c := 0xD) (l := 0xFF) (by decide))]; exact K3 x h1 h2
  have KH6 : ∀ x : Word, 0x40000000 ≤ x.toNat → m6.mem x = M x := fun x hx => K6 x (hi16 x hx) (acf_rHi rlo hx)
  have C6 := acf_codeKeep KH6 C hAC hACl
  have k6' : ∀ q : Fin 32, (q.val = 3 ∨ q.val = 4 ∨ q.val = 8 ∨ q.val = 9 ∨ (18 ≤ q.val ∧ q.val ≤ 27)) →
      reg m6 q = reg m5 q := fun q hq => by
    apply k6 <;> rintro rfl <;> revert hq <;> decide
  have t6 : St m6.mem AC m6 0x1AC2 (reg m6) := ⟨pc6, rfl, fun _ => rfl⟩
  have hz6 := t6.zero
  have R6 : ∀ q : Fin 32, (q.val = 3 ∨ q.val = 4 ∨ q.val = 8 ∨ q.val = 9 ∨ (18 ≤ q.val ∧ q.val ≤ 27)) →
      reg m6 q = reg m3 q := fun q hq => by
    rw [k6' q hq, regs5, updz hz4 (by rintro rfl; revert hq; decide), u4.regs,
      runBlock_reg _ _ _ q hz3 (by simp only [acfS2]; revert hq; revert q; decide)]
  have R3 : ∀ q : Fin 32, (q.val = 3 ∨ q.val = 4 ∨ q.val = 8 ∨ (18 ≤ q.val ∧ q.val ≤ 27)) →
      reg m3 q = reg m q := fun q hq => by
    rw [k3' q (by revert hq; revert q; decide), regs2, updz hz1 (by rintro rfl; revert hq; decide), u1.regs,
      runBlock_reg _ _ _ q hz (by simp only [acfS1]; revert hq; revert q; decide)]
  have r9_6 : reg m6 (9 : Fin 32) = r := by rw [R6 _ (by decide), r9_3]
  have sp6' : reg m6 sp = B + 0x3A50 := by rw [sp6, sp5]
  -- The stores.
  obtain ⟨m7, c7, u7⟩ := t6.block acfB1 C6 acfB1_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acfB1]; simp +decide only [upd, ↓reduceIte, true_and, and_true]
    rw [r9_6]
    exact ⟨acf_rC rlo (c := 0x10C) (by decide) hAC hACl, acf_rC rlo (c := 0x10D) (by decide) hAC hACl,
      acf_rC rlo (c := 0x10E) (by decide) hAC hACl, acf_rC rlo (c := 0x10F) (by decide) hAC hACl,
      ⟨acf_ral rlo ral (k := 0x110) (by decide) (by decide), acf_rC rlo (c := 0x110) (by decide) hAC hACl⟩,
      ⟨acf_ral rlo ral (k := 0x114) (by decide) (by decide), acf_rC rlo (c := 0x114) (by decide) hAC hACl⟩,
      acf_rC rlo (c := 0x118) (by decide) hAC hACl⟩)
  have t7 : St m7.mem AC m7 0x1AEA (reg m7) := ⟨u7.pc, rfl, fun _ => rfl⟩
  have hz7 := t7.zero
  have R7 : ∀ q : Fin 32, (q.val = 3 ∨ q.val = 4 ∨ q.val = 8 ∨ q.val = 9 ∨ (18 ≤ q.val ∧ q.val ≤ 27)) →
      reg m7 q = reg m6 q := fun q hq => by
    rw [u7.regs, runBlock_reg _ _ _ q hz6 (by simp only [acfB1]; revert hq; revert q; decide)]
  have r9_7 : reg m7 (9 : Fin 32) = r := by rw [R7 _ (by decide), r9_6]
  have sp7 : reg m7 sp = B + 0x3A50 := by rw [u7.regs, runBlock_reg _ _ _ _ hz6 (by decide), sp6']
  have KH7 : ∀ x : Word, 0x40000000 ≤ x.toNat → m7.mem x = M x := fun x hx => by
    rw [u7.mem, acf_b1_keep r9_6 rfl x (fun k _ h2 => eq_false (acf_rx (acf_rHi rlo hx) k (by omega)))]
    exact KH6 x hx
  have C7 := acf_codeKeep KH7 C hAC hACl
  obtain ⟨m8, c8, u8⟩ := t7.block acfB2 C7 acfB2_end (by
    simp only [BlockOk, BInstr.ok, BInstr.run, acfB2]; simp +decide only [upd, ↓reduceIte, and_true]
    rw [sp7, r9_7, acf_sp44]
    exact ⟨acf_al F (by decide) (by decide),
      ⟨acf_ral rlo ral (k := 0x120) (by decide) (by decide), acf_rC rlo (c := 0x120) (by decide) hAC hACl⟩,
      acf_rC rlo (c := 0x0) (by decide) hAC hACl, acf_rC rlo (c := 0xC) (by decide) hAC hACl,
      acf_rC rlo (c := 0x128) (by decide) hAC hACl⟩)
  have M78 : (runBlock acfB2 (m7.mem, reg m7)).1 = m8.mem := u8.mem.symm
  have M67 : (runBlock acfB1 (m6.mem, reg m6)).1 = m7.mem := u7.mem.symm
  have b2k : ∀ x, (∀ k : Word, k.toNat < 0x12C →
      (k.toNat = 0 ∨ k.toNat = 0xC ∨ (0x120 ≤ k.toNat ∧ k.toNat < 0x129)) → x ≠ r + k) → m8.mem x = m7.mem x :=
    fun x h => acf_b2_keep r9_7 M78 x (fun k hk => eq_false (h k (by omega) hk))
  have b1k : ∀ x, (∀ k : Word, k.toNat < 0x12C → (0x10C ≤ k.toNat ∧ k.toNat < 0x119) → x ≠ r + k) →
      m7.mem x = m6.mem x :=
    fun x h => acf_b1_keep r9_6 M67 x (fun k h1 h2 => eq_false (h k (by omega) ⟨h1, h2⟩))
  have K8 : ∀ x, Sep (B + 0x3A50 + 0xFFFFFFF0) 16 x 1 → Sep r 0x12C x 1 → m8.mem x = M x := fun x h1 h2 => by
    rw [b2k x (fun k hk _ => acf_rx h2 k hk), b1k x (fun k hk _ => acf_rx h2 k hk)]; exact K6 x h1 h2
  have C8 := acf_codeKeep (fun x hx => K8 x (hi16 x hx) (acf_rHi rlo hx)) C hAC hACl
  have t8 : St m8.mem AC m8 0x1AFC (reg m8) := ⟨u8.pc, rfl, fun _ => rfl⟩
  have R8 : ∀ q : Fin 32, (q.val = 3 ∨ q.val = 4 ∨ q.val = 8 ∨ q.val = 9 ∨ (18 ≤ q.val ∧ q.val ≤ 27)) →
      reg m8 q = reg m7 q := fun q hq => by
    rw [u8.regs, runBlock_reg _ _ _ q hz7 (by simp only [acfB2]; revert hq; revert q; decide)]
  have sp8 : reg m8 sp = B + 0x3A50 := by rw [u8.regs, runBlock_reg _ _ _ _ hz7 (by decide), sp7]
  obtain ⟨m9, e9, t9⟩ := t8.jump C8 ac_at_1afc (off' := 0x184) (by decide) (by rw [u8.pc]; decide)
  have sp9 : reg m9 sp = B + 0x3A50 := by rw [t9.regs, sp8]
  have hS9 : ∀ k, k < 13 → memLoad32 m8.mem (B + BitVec.ofNat 32 (0x5A6C - 4 * k)) = v k :=
    acf_saves (fun c h1 h2 => K8 _ (acf_F16S F (by omega)) (acf_rSl rsep (by omega))) hS
  obtain ⟨n', c', pc', mem', sp', sv', r3', r4'⟩ := ac_ret C8 F ⟨t9.pc, t9.mem, fun _ => rfl⟩ sp9 hS9 hret
  have Rall : ∀ q : Fin 32, (q.val = 3 ∨ q.val = 4 ∨ q.val = 8 ∨ (18 ≤ q.val ∧ q.val ≤ 27)) →
      reg m8 q = reg m q := fun q hq => by
    rw [R8 q (by revert hq; revert q; decide), R7 q (by revert hq; revert q; decide),
      R6 q (by revert hq; revert q; decide), R3 q hq]
  unfold AcRet
  refine ⟨n', c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans
    (.cons e9 c')))))))), pc', sp', sv', ?_, ?_, ?_⟩
  · rw [r3', t9.regs, Rall _ (by decide)]
  · rw [r4', t9.regs, Rall _ (by decide)]
  unfold AcfWrite
  rw [mem']
  have hB2 := acf_b2_bytes r9_7 M78
  have hB1a := acf_b1_10d r9_6 M67
  have hB1b := acf_b1_110 r9_6 M67
  have bk : ∀ a : Nat, a < 0x12C → a ≠ 0 → a ≠ 0xC → (a < 0x10C ∨ 0x119 ≤ a) → (a < 0x120 ∨ 0x129 ≤ a) →
      m8.mem (r + BitVec.ofNat 32 a) = m6.mem (r + BitVec.ofNat 32 a) := fun a ha h0 hc h1 h2 => by
    rw [b2k _ (fun k _ hk => acf_rne (by omega) (by omega)), b1k _ (fun k _ hk => acf_rne (by omega) (by omega))]
  have bk2 : ∀ a : Nat, a < 0x12C → a ≠ 0 → a ≠ 0xC → (a < 0x120 ∨ 0x129 ≤ a) →
      m8.mem (r + BitVec.ofNat 32 a) = m7.mem (r + BitVec.ofNat 32 a) := fun a ha h0 hc h2 =>
    b2k _ (fun k _ hk => acf_rne (by omega) (by omega))
  have slot6 : ∀ c, c < 0x2020 → m6.mem (acSlot B c) = M (acSlot B c) := fun c hc =>
    K6 _ (acf_F16S F (by omega)) (acf_rSl rsep hc)
  have slot7 : ∀ c, c < 0x2020 → m7.mem (acSlot B c) = M (acSlot B c) := fun c hc => by
    rw [b1k _ (fun k hk _ => acf_rx (acf_rSl rsep hc) k hk)]; exact slot6 c hc
  refine ⟨?_, fun i hi => ?_, ?_, fun i hi => ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, fun x hw hx => ?_⟩
  · rw [hB2.1, R7 _ (by decide), R6 _ (by decide), R3 _ (by decide)]
  · rw [bk (1 + i) (by omega) (by omega) (by omega) (.inl (by omega)) (.inl (by omega)), mem6 _ (acf_rF rsep (c := 1 + i) (n := 1) (by omega)).symm, mem5,
      acf_cb_out (sep_offsets r (by omega) (by omega) (by omega)), mem3 _ (acf_rF rsep (c := 1 + i) (n := 1) (by omega)).symm,
      mem2, ← add_ofNat_assoc, acf_cb_in hi (by decide), acf_slot_add]
  · rw [hB2.2.1, R7 _ (by decide), R6 _ (by decide), R3 _ (by decide)]
  · rw [bk (0xD + i) (by omega) (by omega) (by omega) (.inl (by omega)) (.inl (by omega)), mem6 _ (acf_rF rsep (c := 0xD + i) (n := 1) (by omega)).symm, mem5,
      ← add_ofNat_assoc, acf_cb_in hi (by decide), acf_slot_add]
    exact K3 _ (acf_F16S F (by omega)) (acf_rSl rsep (by omega))
  · rw [show (r + 0x10C : Word) = r + BitVec.ofNat 32 0x10C from rfl, bk2 0x10C (by decide) (by decide) (by decide) (.inl (by decide))]
    exact (acf_b1_10c r9_6 M67).trans (by rw [R6 _ (by decide), R3 _ (by decide)])
  · rw [bk2 (0x10D + i) (by omega) (by omega) (by omega) (.inl (by omega))]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · rw [show r + BitVec.ofNat 32 (0x10D + 0) = r + 0x10D from rfl, hB1a.1, sp6']; exact (congrArg m6.mem (acf_sp B _)).trans (slot6 _ (by decide))
    · rw [show r + BitVec.ofNat 32 (0x10D + 1) = r + 0x10E from rfl, hB1a.2.1, sp6']; exact (congrArg m6.mem (acf_sp B _)).trans (slot6 _ (by decide))
    · rw [show r + BitVec.ofNat 32 (0x10D + 2) = r + 0x10F from rfl, hB1a.2.2, sp6']; exact (congrArg m6.mem (acf_sp B _)).trans (slot6 _ (by decide))
  · refine (memLoad32_congr fun j hj => ?_).trans (hB1b.1.trans ?_)
    · rw [show r + 0x110 + BitVec.ofNat 32 j = r + BitVec.ofNat 32 (0x110 + j) from add_ofNat_assoc r 0x110 j]
      exact bk2 _ (by omega) (by omega) (by omega) (.inl (by omega))
    · rw [R6 _ (by decide), R3 _ (by decide)]
  · refine (memLoad32_congr fun j hj => ?_).trans (hB1b.2.1.trans ?_)
    · rw [show r + 0x114 + BitVec.ofNat 32 j = r + BitVec.ofNat 32 (0x114 + j) from add_ofNat_assoc r 0x114 j]
      exact bk2 _ (by omega) (by omega) (by omega) (.inl (by omega))
    · rw [R6 _ (by decide), R3 _ (by decide)]
  · rw [show (r + 0x118 : Word) = r + BitVec.ofNat 32 0x118 from rfl, bk2 0x118 (by decide) (by decide) (by decide) (.inl (by decide))]
    exact hB1b.2.2.trans (by rw [R6 _ (by decide), R3 _ (by decide)])
  · rw [acf_b2_120 r9_7 M78, sp7, acf_sp44]
    exact acf_ld fun j hj => slot7 _ (by omega)
  · rw [hB2.2.2, R7 _ (by decide), R6 _ (by decide), R3 _ (by decide)]
  · exact K8 x (acf_F16W hw) hx.symm

/-- At 0x7D6 after `sigstore::verify` returned: the invariant, and the exit
with the code in `s5`. -/
theorem acf_exit {B Bf g t r : Word} {v : Nat → Word} {M0 : Word → BitVec 8} {n n2 n5 : Machine}
    (I : AcInv B Bf g t v M0 n) (P : memLoad32 n.mem (acSlot B 0x40) = r)
    (K : ∀ x, Sep x 1 (B + 0xFFFFFE60) 0x5C10 → n2.mem x = n.mem x)
    (KS : ∀ c, c < 0x2020 → (c < 0xDD0 ∨ 0xDE8 ≤ c) → n2.mem (acSlot B c) = n.mem (acSlot B c))
    (s : St n2.mem AC n5 0x7D6 (reg n5)) (rsp : reg n5 sp = B + 0x3A50) (r3 : reg n5 (3 : Fin 32) = g)
    (r4 : reg n5 (4 : Fin 32) = t) :
    AcFinishInv B Bf g t v M0 n5 ∧ (AcFail B r n5 ∨ AcFinishBad B r n5) := by
  have M5 : n5.mem = n2.mem := s.mem
  refine ⟨⟨rsp, r3, r4, ?_, fun x hw hb => ?_⟩, ?_⟩
  · rw [M5]; exact acf_saves (fun c h1 h2 => KS c h2 (by omega)) I.saves
  · rw [M5, K x hw]; exact I.out x (acf_wB hw) hb
  · have hr : memLoad32 n5.mem (acSlot B 0x40) = r := by
      rw [M5, acf_ld fun j hj => KS _ (by omega) (by omega)]; exact P
    unfold AcFail AcFinishBad
    by_cases h : (reg n5 (21 : Fin 32) &&& 0xFF).toNat < 0x27
    · exact .inl (.inr (.inr (.inl ⟨s.pc, hr, h⟩)))
    · exact .inr ⟨s.pc, hr, by omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The last stage holds.** -/
theorem ac_finish_stage : AcFinishStage := by
  unfold AcFinishStage AcFinishPost
  intro n B Bf g t r v M0 bundle root expiry hE C F hret I P
  have E := hE n.mem I.out
  have hz := P.st.zero
  have hAC : 0x40000000 ≤ AC.toNat := by decide
  have hACl : AC.toNat + bootMainClosure0Code.length ≤ 2 ^ 32 := by decide
  have hMS : 0x40000000 ≤ MCS.toNat := by decide
  have hMSl : MCS.toNat + memcpyStubCode.length ≤ 2 ^ 32 := by decide
  have hMB : 0x40000000 ≤ (MCS + 8).toNat := by decide
  have hMBl : (MCS + 8).toNat + memcpyBodyCode.length ≤ 2 ^ 32 := by decide
  obtain ⟨n1, e1, pc1, mem1, regs1⟩ := P.st.call C ac_at_1a46
  have R1 : ∀ q : Fin 32, q ≠ ra → reg n1 q = reg n q := fun q h => by rw [regs1, updz hz h]
  have ra1 : reg n1 ra = AC + BitVec.ofNat 32 0x1A4A := by rw [regs1]; rfl
  have s1 : St n.mem SV n1 0 (reg n1) := ⟨by rw [pc1, P.ra]; decide, mem1, fun _ => rfl⟩
  have a0_1 : reg n1 a0 = acSlot B 0xDD0 := by rw [R1 _ (by decide), P.a0]
  have sp1 : reg n1 sp = B + 0x13F0 + 0x2660 := by
    rw [R1 _ (by decide), I.sp, BitVec.add_assoc]; rfl
  have hv1 : (fun k => reg n1 (savedReg k)) 0 &&& ~~~1 = (fun k => reg n1 (savedReg k)) 0 := by
    show reg n1 ra &&& ~~~1 = reg n1 ra; rw [ra1]; decide
  have sv := sv_verify_spec (B := B + 0x13F0) (by rw [R1 _ (by decide), P.a1]; exact P.bundle)
    (by rw [R1 _ (by decide), P.a2]; exact P.root) E.sv E.svc (acf_frW F) s1 sp1 hv1
    (by rw [a0_1]; exact acf_svOut F) E.p2 E.svd E.hf P.ro E.pv E.p2v
    (by rw [R1 _ (by decide), P.a3]; exact acf_svIn F) E.sha2 E.ck E.ev E.iv E.rk
    (by rw [a0_1]; exact acf_svOutOk F) E.oid E.nd E.ud E.ld E.pd E.pmd E.e1d E.edd E.smd E.d2d E.bsd E.krd E.krrd
    E.rekor
  rw [R1 a3 (by decide), P.a3] at sv
  rw [a0_1] at sv
  rcases sv with ⟨n2, c2, pc2, sp2, sv2, r3, r4, m2, K2⟩ | ⟨n', c', hh⟩ | ⟨vv, hv, n2, c2, pc2, sp2, sv2, r3, r4, m2, mlo, mhi, -, -, K2⟩
  · -- `Err`.
    have sp2' : reg n2 sp = B + 0x3A50 := by rw [sp2, BitVec.add_assoc]; rfl
    have K : ∀ x, Sep x 1 (B + 0xFFFFFE60) 0x5C10 → n2.mem x = n.mem x := fun x hw => by
      rw [K2 x (acf_svRW hw) (acf_wne hw (by decide)) (by rw [acf_slot1]; exact acf_wne hw (by decide)), mem1]
    have KS : ∀ c, c < 0x2020 → (c < 0xDD0 ∨ 0xDE8 ≤ c) → n2.mem (acSlot B c) = n.mem (acSlot B c) :=
      fun c hc h => by
        rw [K2 _ (acf_svRS F hc) (acf_slot_ne B hc (by decide) (by omega))
          (by rw [acf_slot1]; exact acf_slot_ne B hc (by decide) (by omega)), mem1]
    have C2 := acf_codeKeep (fun x hx => K x (acf_hiW F hx)) C hAC hACl
    have s2 : St n2.mem AC n2 0x1A4A (reg n2) := ⟨by rw [pc2]; exact ra1, rfl, fun _ => rfl⟩
    obtain ⟨n3, c3, s3, a3, k3⟩ := acf_seg_tag C2 s2 sp2'
    obtain ⟨n4, c4, s4, s0, k4⟩ := acf_seg_err C2 s3 (by rw [k3 _ (by decide)]; exact sp2')
      (by rw [a3, m2]; decide)
    obtain ⟨n5, c5, s5, s5v, k5⟩ := acf_seg_7d6 C2 s4
    have hg : ∀ q : Fin 32, (q = 3 ∨ q = 4 ∨ q = sp) → reg n5 q = reg n2 q := fun q hq => by
      rw [k5 q (by rcases hq with rfl | rfl | rfl <;> decide), k4 q (by rcases hq with rfl | rfl | rfl <;> decide)
        (by rcases hq with rfl | rfl | rfl <;> decide), k3 q (by rcases hq with rfl | rfl | rfl <;> decide)]
    refine ⟨n5, .cons e1 (c2.trans (c3.trans (c4.trans c5))), .inr (.inl (acf_exit I P.res K KS s5 ?_ ?_ ?_))⟩
    · rw [hg _ (by decide), sp2']
    · rw [hg _ (by decide), r3, R1 _ (by decide), I.gp]
    · rw [hg _ (by decide), r4, R1 _ (by decide), I.tp]
  · exact ⟨n', .cons e1 c', .inl hh⟩
  · -- `Ok`.
    have sp2' : reg n2 sp = B + 0x3A50 := by rw [sp2, BitVec.add_assoc]; rfl
    have K : ∀ x, Sep x 1 (B + 0xFFFFFE60) 0x5C10 → n2.mem x = n.mem x := fun x hw => by
      rw [K2 x (acf_svRW hw) (acf_wSlot hw (by decide)), mem1]
    have KS : ∀ c, c < 0x2020 → (c < 0xDD0 ∨ 0xDE8 ≤ c) → n2.mem (acSlot B c) = n.mem (acSlot B c) :=
      fun c hc h => by
        rw [K2 _ (acf_svRS F hc) (acf_slot_sep B (by omega) (by decide) (by omega)), mem1]
    have KH : ∀ x : Word, 0x40000000 ≤ x.toNat → n2.mem x = n.mem x := fun x hx => K x (acf_hiW F hx)
    have C2 := acf_codeKeep KH C hAC hACl
    have s2 : St n2.mem AC n2 0x1A4A (reg n2) := ⟨by rw [pc2]; exact ra1, rfl, fun _ => rfl⟩
    have hT := acf_time_lt P.root hv
    have hlo : memLoad32 n2.mem (acSlot B 0xDD8) = BitVec.ofNat 32 (vv.signedTime % 2 ^ 32) := by
      rw [← acf_slot_add B 0xDD0 8]; exact mlo
    have hhi : memLoad32 n2.mem (acSlot B 0xDDC) = BitVec.ofNat 32 (vv.signedTime / 2 ^ 32) := by
      rw [← acf_slot_add B 0xDD0 0xC]; exact mhi
    have hX : SvU64At n2.mem (acSlot B 0x20) expiry := by
      refine ⟨P.expiry.1, ?_, ?_⟩
      · rw [acf_ld fun j hj => KS _ (by omega) (by omega)]; exact P.expiry.2.1
      · rw [show acSlot B 0x20 + 4 = acSlot B 0x24 from acf_slot_add B 0x20 4,
          acf_ld fun j hj => KS _ (by omega) (by omega), ← acf_slot_add B 0x20 4]
        exact P.expiry.2.2
    obtain ⟨n3, c3, s3, a3, k3⟩ := acf_seg_tag C2 s2 sp2'
    obtain ⟨n4, c4, s4, a4, s0_4, s2_4, k4⟩ := acf_seg_cmp C2 F s3 (by rw [k3 _ (by decide)]; exact sp2')
      (by rw [a3, m2]; rfl) hlo hhi hX hT
    have k34 : ∀ q : Fin 32, (q.val = 3 ∨ q.val = 4 ∨ q.val = 2 ∨ q.val = 21 ∨ q.val = 25 ∨ q.val = 27) →
        reg n4 q = reg n2 q := fun q hq => by
      rw [k4 q (by omega) (by omega) (by omega), k3 q (by omega)]
    by_cases hlt : expiry < vv.signedTime
    · rw [ite_eq_left hlt] at a4
      obtain ⟨n5, c5, s5, s0_5, k5⟩ := acf_seg_late C2 s4 (by rw [a4]; decide)
      obtain ⟨n6, c6, s6, s5v, k6⟩ := acf_seg_7d6 C2 s5
      have hg : ∀ q : Fin 32, (q.val = 3 ∨ q.val = 4 ∨ q.val = 2) → reg n6 q = reg n2 q := fun q hq => by
        rw [k6 q (by omega), k5 q (by omega), k34 q (by omega)]
      refine ⟨n6, .cons e1 (c2.trans (c3.trans (c4.trans (c5.trans c6)))), .inr (.inl ⟨?_, .inl ?_⟩)⟩
      · refine (acf_exit I P.res K KS s6 ?_ ?_ ?_).1
        · rw [hg sp (by decide), sp2']
        · rw [hg _ (by decide), r3, R1 _ (by decide), I.gp]
        · rw [hg _ (by decide), r4, R1 _ (by decide), I.tp]
      · unfold AcFail
        refine .inr (.inr (.inl ⟨s6.pc, ?_, ?_⟩))
        · rw [s6.mem, acf_ld fun j hj => KS _ (by omega) (by omega)]; exact P.res
        · rw [s5v, s0_5]; decide
    · rw [ite_eq_right hlt] at a4
      have hz4 := s4.zero
      obtain ⟨n5, e5, s5⟩ := s4.taken C2 0x1A9C ac_at_1a94 (by decide)
        (by show (reg n4 a0 == reg n4 0) = true; rw [hz4, a4]; rfl)
      have CS := acf_codeKeep KH E.mcs hMS hMSl
      have CB := acf_codeKeep KH E.mcb hMB hMBl
      obtain ⟨n', c', pc', sp', sv', r3', r4', W⟩ := acf_seg_write C2 F CS CB ⟨s5.pc, s5.mem, fun _ => rfl⟩
        (by rw [s5.regs, k34 sp (by decide), sp2'])
        (by rw [acf_ld fun j hj => KS _ (by omega) (by omega)]; exact P.res)
        (acf_saves (fun c h1 h2 => KS c h2 (by omega)) I.saves) hret P.rsep P.ral P.rlo
      have Rq : ∀ q : Fin 32, (q.val = 3 ∨ q.val = 4 ∨ q.val = 21 ∨ q.val = 25 ∨ q.val = 27) →
          reg n5 q = reg n2 q := fun q hq => by rw [s5.regs, k34 q (by omega)]
      have Rs : ∀ k, 0 < k → k < 13 → reg n2 (savedReg k) = reg n (savedReg k) := fun k h0 hk => by
        rw [sv2 k hk]; apply R1; revert h0; revert hk; revert k; decide
      have r21 : reg n5 (21 : Fin 32) = reg n (21 : Fin 32) := by rw [Rq _ (by decide)]; exact Rs 6 (by decide) (by decide)
      have r25 : reg n5 (25 : Fin 32) = reg n (25 : Fin 32) := by rw [Rq _ (by decide)]; exact Rs 10 (by decide) (by decide)
      have r27 : reg n5 (27 : Fin 32) = reg n (27 : Fin 32) := by rw [Rq _ (by decide)]; exact Rs 12 (by decide) (by decide)
      have r18 : reg n5 (18 : Fin 32) = BitVec.ofNat 32 (vv.signedTime % 2 ^ 32) := by rw [s5.regs, s2_4]
      have r8 : reg n5 (8 : Fin 32) = BitVec.ofNat 32 (vv.signedTime / 2 ^ 32) := by rw [s5.regs, s0_4]
      obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11⟩ := W
      refine ⟨n', .cons e1 (c2.trans (c3.trans (c4.trans (.cons e5 c')))), .inr (.inr ⟨pc', sp', sv', ?_, ?_, ?_⟩)⟩
      · rw [r3', Rq _ (by decide), r3, R1 _ (by decide), I.gp]
      · rw [r4', Rq _ (by decide), r4, R1 _ (by decide), I.tp]
      unfold AcFinishRes
      refine ⟨vv, hv, by omega, ?_, fun i hi => ?_, ?_, fun i hi => ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, ?_,
        fun x hw hb hx => ?_⟩
      · exact (congrArg n'.mem (BitVec.add_zero r).symm).trans (w0.trans (by rw [r21]))
      · rw [w1 i hi, KS _ (by omega) (by omega)]
      · rw [w2, r25]
      · rw [w3 i hi, KS _ (by omega) (by omega)]
      · rw [w4, r27]
      · rw [w5 i hi, KS _ (by omega) (by omega)]
      · rw [w6, r18]
      · rw [w7, r8]
      · rw [w8, r27]
      · rw [w9, acf_ld fun j hj => KS _ (by omega) (by omega)]
      · rw [w10, r27]
      · rw [w11 x hw hx, K x hw]; exact I.out x (acf_wB hw) hb

end C3.RV32.Ac
