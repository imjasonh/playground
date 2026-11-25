import C3BootProofs.AuditPending
import C3BootProofs.Proofs.Boot
import C3BootProofs.Proofs.BootSpec

/-!
# Pending proofs

The modules this file imports describe the bootloader image from before the
TUF cutover (digest `c3-boot/bootloader/dev-image.sha256` before
`fe413a32…`). They no longer build against the current image, so the root
`C3BootProofs` module doesn't import them, `scripts/image-facts.py` skips
them, and CI doesn't check them. They stay as they were, so the next proofs
can start from them.

Six functions changed shape in the cutover: `manifest_parse`,
`generalized_time`, `sigstore::verify`, `boot`, `boot_main`'s first closure,
and `boot_main`. The root module proves `manifest_parse`,
`generalized_time`, and `sigstore::verify` again. The modules here prove
something about the other three: `Proofs/BootSpec` and `Proofs/Boot` cover
`boot`, `boot_main`, and its first closure, which now read the TUF part and
burn eFuses.

Lemmas that these modules imported from retired modules moved:
`Proofs/CheckSigs`'s read-only-data congruences are in `Proofs/EdVerifyRo`,
`Proofs/KeySet`'s `lowSep` is in `Proof/Mem`, its `memBytes_eq_of` is in
`Proofs/ShaTools`, and `Proofs/Keys`'s `bytesMem_congr` is in
`Proofs/ReaderArray`.
-/
