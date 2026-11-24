import C3BootProofs.Spec.TrustedRoot
import C3BootProofs.Spec.Sigstore

/-!
# Accepting a slot under Sigstore's TUF root

`c3_verify::tuf_slot::accept_slot`: the image header, the image's security
version against the eFuse level, the TUF metadata from the pinned root, the
keys of the trusted root that the metadata vouches for with the compiled-in
`policy`, the Sigstore bundle against the image's digest, and the TSA's
signed time against the metadata's expiry. It returns the image's security
version and the signed time.
-/

namespace C3

/-- `tuf_slot::accept_slot`, for a whole image. -/
def acceptTufSlot (image bundle tuf pinned : Bytes) (policy : Policy) (efuseLevel : Nat) :
    Option (Nat × Nat) := do
  let header ← decodeImageHeader image image.length
  require (header.securityVersion ≥ efuseLevel)
  let parts ← decodeTufParts tuf
  let (_, expiry) ← verifyTuf pinned parts
  let root ← extractTrustedRoot parts.trustedRoot policy
  let verified ← sigstoreVerify (← decodeBundle bundle) root (sha256 image)
  require (verified.signedTime ≤ expiry)
  pure (header.securityVersion, verified.signedTime)

end C3
