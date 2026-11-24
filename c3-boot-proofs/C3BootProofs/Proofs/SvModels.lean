import C3BootProofs.Proofs.SvVerifyAt
import C3BootProofs.Spec.Sigstore

/-!
# What the link to `sigstoreVerify` assumes about the signature models

The success condition of `sigstore::verify` states the signature checks as
the models the machine-code proofs compute: `pvModel` for P-384
(`SvPvRes`), the multi-scalar multiplication `mlMain2` and its inversions for
P-256 (`SvP256Facts`), `evSpec` for Ed25519, and `GsOk` for a P-256 point.
`SvEdModel` and `SvGsModel` state that a model agrees with
`Spec/Ed25519.lean` or `Spec/Ecdsa.lean` for the constants in memory `M`.
The ECDSA models are `SvP256Model'` and `SvP384Model'` in `Models/`.
-/

namespace C3.RV32.Sv

open C3.Image C3.RV32.P3 C3.RV32.Dq C3.RV32.Pv C3.RV32.Gs C3.RV32.P2 C3.RV32.Gd

/-- What the success condition says the P-256 check computed for the key at
`bp`, the digest at `dg`, and the scalars `r` and `s`. -/
def SvP256Facts (M : Word → BitVec 8) (bp dg : Word) (r s : Bytes) : Prop :=
  (((inScalarRange (b32 r) (memBytes M (BitVec.ofNat 32 0x3FCC4288) 32) = true) ∧ (inScalarRange (b32 s) (memBytes M (BitVec.ofNat 32 0x3FCC4288) 32) = true) ∧ (M bp = 4) ∧ True) ∧ ((GsOk M bp) ∧ (beNat (b32 r) < C3.p256.n) ∧ (beNat (b32 s) < C3.p256.n) ∧ (beNat (b32 r) ≠ 0) ∧ (beNat (b32 s) ≠ 0) ∧ True)) ∧ ∃ σd_2 σf_2 Dv_2 Fv_2, σd_2 ≤ 1 ∧ σf_2 ≤ 1 ∧ sgnVal σf_2 Fv_2 = (p256Sf M s).f ∧ sgnVal σd_2 Dv_2 = (p256Sf M s).d ∧ (((Fv_2 = accV M (BitVec.ofNat 32 0x3FCC42E8) 8)) ∧ True) ∧ ∃ stm_2, mlMain2 (tbl2 (accV M (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x0) 8, accV M (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x20) 8, accV M (BitVec.ofNat 32 0x3FCC4690 + BitVec.ofNat 32 0x40) 8)) (tbl2 ((gsVal M bp 1 * 2 ^ 256 % p256), (gsVal M bp 0x21 * 2 ^ 256 % p256), (accV M (BitVec.ofNat 32 0x3FCC43A8) 8))) (wnafBytes (wnafGo ((psmVal (((beNat (memBytes M (dg) 32) % C3.p256.n)) * ((normVal8 σd_2 σf_2 Dv_2 (accV M (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0) 0x101) (wnafBytes (wnafGo ((psmVal (((beNat (b32 r))) * ((normVal8 σd_2 σf_2 Dv_2 (accV M (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0) 0x101) (max (wnafGo ((psmVal (((beNat (memBytes M (dg) 32) % C3.p256.n)) * ((normVal8 σd_2 σf_2 Dv_2 (accV M (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length (wnafGo ((psmVal (((beNat (b32 r))) * ((normVal8 σd_2 σf_2 Dv_2 (accV M (BitVec.ofNat 32 0x3FCC4268) 8)))))) 0x100 0x101 0 0).length) = some stm_2 ∧ ∃ τd_2 τf_2 Dz_2 Fz_2, τd_2 ≤ 1 ∧ τf_2 ≤ 1 ∧ sgnVal τf_2 Fz_2 = (p256Sz M stm_2.1.2.2).f ∧ sgnVal τd_2 Dz_2 = (p256Sz M stm_2.1.2.2).d ∧ ((((beNat (b32 r)) = (p2fm ((if (((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV M (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then p2fm ((stm_2.1.1)) ((if ((((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV M (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8).zeroExtend 32) = 1 then (if (((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV M (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32).extractLsb' 0 8) = 1 then (if (((((((((if stm_2.1.2.2 = 0 then 0 else 1 : Word)) &&& BitVec.ofNat 32 0xFF))) &&& (((if Fz_2 = accV M (BitVec.ofNat 32 0x3FCC42E8) 8 then 1 else 0 : Word)) &&& BitVec.ofNat 32 0xFF)).extractLsb' 0 8).zeroExtend 32) &&& BitVec.ofNat 32 0xFF) = 1 then normVal8 τd_2 τf_2 Dz_2 (accV M (BitVec.ofNat 32 0x3FCC4B38) 8) else 0) else 0) else 0)) else accV M (BitVec.ofNat 32 0x3FCC442C) 8)) 1) % C3.p256.n)) ∧ True)

/-- `ed25519_verify` accepts only signatures that `ed25519Verify` accepts. -/
def SvEdModel (M : Word → BitVec 8) : Prop :=
  ∀ pk sig msg len, evSpec M pk sig msg len = true →
    ed25519Verify (memBytes M pk 32) (memBytes M msg len) (memBytes M sig 64) = true

/-- A SEC 1 point the code accepts is on P-256. -/
def SvGsModel (M : Word → BitVec 8) : Prop :=
  ∀ bp, M bp = 4 → GsOk M bp → (C3.p256.decodePoint (memBytes M bp 65)).isSome = true

end C3.RV32.Sv
