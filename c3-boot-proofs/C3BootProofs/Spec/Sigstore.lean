import C3BootProofs.Spec.Tsa

/-!
# The Sigstore check

`sigstoreVerify` is the decision `c3_verify::sigstore::verify` makes about
a slot's bundle, composed from the parts in the other specification files,
in the same order: the bundle proves the release workflow signed an image
whose SHA-256 digest is `imageDigest`, under the keys and policy of `root`.

- The leaf certificate fits the profile, its issuer is a listed Fulcio
  intermediate, and that intermediate signed it.
- The leaf's identity-policy extensions equal the root's policy.
- The leaf's P-256 key signed the image digest.
- A listed TSA timestamped that signature.
- A listed log's checkpoint is signed, the entry's index is inside its
  tree, and the inclusion proof for the entry rebuilt from the digest, the
  signature, and the certificate yields the checkpoint's root.
- The TSA's signed time is inside the leaf's, the intermediate's, the
  TSA's, and the log's validity windows.

It returns the signed time and the entry's log index.
-/

namespace C3

/-- What a verified bundle proves. -/
structure Verified where
  signedTime : Nat
  logIndex : Nat
  deriving DecidableEq, Repr

/-- `sigstore::verify`. -/
def sigstoreVerify (bundle : Bundle) (root : SigstoreRoot) (imageDigest : Bytes) : Option Verified := do
  let leaf ← parseLeaf bundle.leafCertificate
  let intermediate ← root.fulcio.find? (·.subject == leaf.issuer)
  require (verifyLeaf leaf intermediate)
  let p := root.policy
  require (leaf.identity == [p.issuer, p.buildSignerUri, p.repositoryId, p.ownerId, p.trigger])
  let (r, s) ← ecdsaSignature 32 bundle.imageSignature
  require (p256Verify leaf.publicKey imageDigest r s)
  let ts ← parseTimestamp bundle.timestamp
  let tsa ← root.tsas.find? (·.signerId == ts.signerId)
  require (verifyTimestamp ts tsa bundle.imageSignature)
  let checkpoint ← verifyCheckpoint bundle.checkpoint root
  require (bundle.logIndex < checkpoint.size)
  let leafHash := rekorLeafHash imageDigest bundle.imageSignature bundle.leafCertificate
  let computed ← rootFromInclusion bundle.logIndex checkpoint.size leafHash bundle.inclusionProof
  require (computed == checkpoint.root)
  let t := ts.genTime
  require (Window.contains ⟨leaf.notBefore, leaf.notAfter⟩ t && intermediate.window.contains t &&
    tsa.window.contains t && checkpoint.log.window.contains t)
  pure ⟨t, bundle.logIndex⟩

end C3
