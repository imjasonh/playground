import C3BootProofs.AuditPending
import C3BootProofs.Proofs.Boot
import C3BootProofs.Proofs.BootSpec
import C3BootProofs.Proofs.SvAttrLoop
import C3BootProofs.Proofs.SvCLoop
import C3BootProofs.Proofs.SvCg
import C3BootProofs.Proofs.SvCgLoop
import C3BootProofs.Proofs.SvCk2
import C3BootProofs.Proofs.SvCkdLoop
import C3BootProofs.Proofs.SvCkptLink
import C3BootProofs.Proofs.SvCm
import C3BootProofs.Proofs.SvConstsLink
import C3BootProofs.Proofs.SvCosigLink
import C3BootProofs.Proofs.SvCosigLoop
import C3BootProofs.Proofs.SvCr1
import C3BootProofs.Proofs.SvD
import C3BootProofs.Proofs.SvDbc2m
import C3BootProofs.Proofs.SvEdImage
import C3BootProofs.Proofs.SvEkuLoop
import C3BootProofs.Proofs.SvEntry
import C3BootProofs.Proofs.SvExtLink
import C3BootProofs.Proofs.SvExtListLink
import C3BootProofs.Proofs.SvExtLoop
import C3BootProofs.Proofs.SvFail2
import C3BootProofs.Proofs.SvILoop
import C3BootProofs.Proofs.SvLeafH
import C3BootProofs.Proofs.SvLeafH1
import C3BootProofs.Proofs.SvLeafH2
import C3BootProofs.Proofs.SvLeafH3
import C3BootProofs.Proofs.SvLeafHash
import C3BootProofs.Proofs.SvLeafLink
import C3BootProofs.Proofs.SvPvWitness
import C3BootProofs.Proofs.SvSegAttr
import C3BootProofs.Proofs.SvSegAttrPre
import C3BootProofs.Proofs.SvSegCert
import C3BootProofs.Proofs.SvSegCkpt
import C3BootProofs.Proofs.SvSegCosig
import C3BootProofs.Proofs.SvSegDbc
import C3BootProofs.Proofs.SvSegDku
import C3BootProofs.Proofs.SvSegDpv
import C3BootProofs.Proofs.SvSegEku
import C3BootProofs.Proofs.SvSegExt
import C3BootProofs.Proofs.SvSegLeaf
import C3BootProofs.Proofs.SvSegLog
import C3BootProofs.Proofs.SvSegSv
import C3BootProofs.Proofs.SvSegTs
import C3BootProofs.Proofs.SvSegTsa
import C3BootProofs.Proofs.SvSegTst
import C3BootProofs.Proofs.SvSegTst4o
import C3BootProofs.Proofs.SvSegTst4x0
import C3BootProofs.Proofs.SvSegTst4x1
import C3BootProofs.Proofs.SvSegWin
import C3BootProofs.Proofs.SvSha
import C3BootProofs.Proofs.SvSpec
import C3BootProofs.Proofs.SvSpecAux
import C3BootProofs.Proofs.SvTLoop
import C3BootProofs.Proofs.SvTop
import C3BootProofs.Proofs.SvTs
import C3BootProofs.Proofs.SvTs1
import C3BootProofs.Proofs.SvTsa1
import C3BootProofs.Proofs.SvTsa2
import C3BootProofs.Proofs.SvTsa3
import C3BootProofs.Proofs.SvTsa4
import C3BootProofs.Proofs.SvTsa4n
import C3BootProofs.Proofs.SvTsa4s
import C3BootProofs.Proofs.SvTsa5
import C3BootProofs.Proofs.SvTsaLink
import C3BootProofs.Proofs.SvTsaa
import C3BootProofs.Proofs.SvTsal
import C3BootProofs.Proofs.SvTsav
import C3BootProofs.Proofs.SvTsavct
import C3BootProofs.Proofs.SvTsavmd
import C3BootProofs.Proofs.SvTsavother
import C3BootProofs.Proofs.SvTsax
import C3BootProofs.Proofs.SvTst1
import C3BootProofs.Proofs.SvTst2
import C3BootProofs.Proofs.SvTst3
import C3BootProofs.Proofs.SvTst3n
import C3BootProofs.Proofs.SvTst3s
import C3BootProofs.Proofs.SvTst4
import C3BootProofs.Proofs.SvTst4b
import C3BootProofs.Proofs.SvTst4e0
import C3BootProofs.Proofs.SvTst4e1
import C3BootProofs.Proofs.SvTst4n
import C3BootProofs.Proofs.SvTst4nn
import C3BootProofs.Proofs.SvTst4ns
import C3BootProofs.Proofs.SvTst4o
import C3BootProofs.Proofs.SvTst4x0
import C3BootProofs.Proofs.SvTst4x1
import C3BootProofs.Proofs.SvTst5
import C3BootProofs.Proofs.SvTst5n
import C3BootProofs.Proofs.SvTst5s
import C3BootProofs.Proofs.SvTst6
import C3BootProofs.Proofs.SvTst6n
import C3BootProofs.Proofs.SvTst6s
import C3BootProofs.Proofs.SvVerify
import C3BootProofs.Proofs.SvVerifyAt
import C3BootProofs.Proofs.SvWin0
import C3BootProofs.Proofs.SvWin1
import C3BootProofs.Proofs.SvWin2
import C3BootProofs.Proofs.SvWin3
import C3BootProofs.Proofs.SvWin4
import C3BootProofs.Proofs.SvWin5
import C3BootProofs.Proofs.SvWin6
import C3BootProofs.Proofs.SvWin7
import C3BootProofs.Proofs.SvWinLink
import C3BootProofs.Proofs.SvX2

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
and `boot_main`. The root module proves `manifest_parse` and
`generalized_time` again. Every module here proves something about one of
the other four, or imports a module that does:

- `Proofs/Sv*`: the stages of `sigstore::verify`. Its code and its
  read-only data moved; the P-256 check is now a call to
  `p256_verify_prehash` and the leaf certificate's time check calls
  `generalized_time`.
- `Proofs/BootSpec` and `Proofs/Boot`: `boot`, `boot_main`, and its first
  closure, which now read the TUF part and burn eFuses.
- `Models/P256*`, `Models/SafegcdP256`, `Models/P384*`,
  `Models/WeierstrassNist`, and `Models/EcdsaModels`/`EcdsaClosed`: the
  elliptic-curve models of `sigstore::verify`'s P-256 and P-384 stages.
- `Models/Ed25519SvModel*` and `Models/Ed25519Closed`: the Ed25519 model of
  `sigstore::verify`'s signature stage.

Lemmas that these modules imported from retired modules moved:
`Proofs/CheckSigs`'s read-only-data congruences are in `Proofs/EdVerifyRo`,
`Proofs/KeySet`'s `lowSep` is in `Proof/Mem`, its `memBytes_eq_of` is in
`Proofs/ShaTools`, and `Proofs/Keys`'s `bytesMem_congr` is in
`Proofs/ReaderArray`.
-/
