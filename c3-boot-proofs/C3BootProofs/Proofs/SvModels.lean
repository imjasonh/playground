import C3BootProofs.Proofs.P2vP256
import C3BootProofs.Proofs.Ed25519VerifyC
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

/-- `ed25519_verify` accepts only signatures that `ed25519Verify` accepts. -/
def SvEdModel (M : Word → BitVec 8) : Prop :=
  ∀ pk sig msg len, evSpec M pk sig msg len = true →
    ed25519Verify (memBytes M pk 32) (memBytes M msg len) (memBytes M sig 64) = true

/-- A SEC 1 point the code accepts is on P-256. -/
def SvGsModel (M : Word → BitVec 8) : Prop :=
  ∀ bp, M bp = 4 → GsOk M bp → (C3.p256.decodePoint (memBytes M bp 65)).isSome = true

end C3.RV32.Sv
