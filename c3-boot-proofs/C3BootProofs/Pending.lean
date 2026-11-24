import C3BootProofs.AuditPending
import C3BootProofs.Proofs.Boot
import C3BootProofs.Proofs.BootSpec
import C3BootProofs.Proofs.SvAttrLoop
import C3BootProofs.Proofs.SvCLoop
import C3BootProofs.Proofs.SvCSearch
import C3BootProofs.Proofs.SvCalls
import C3BootProofs.Proofs.SvCg
import C3BootProofs.Proofs.SvCg0
import C3BootProofs.Proofs.SvCg1
import C3BootProofs.Proofs.SvCg2
import C3BootProofs.Proofs.SvCg3
import C3BootProofs.Proofs.SvCg4
import C3BootProofs.Proofs.SvCgLoop
import C3BootProofs.Proofs.SvCk1
import C3BootProofs.Proofs.SvCk2
import C3BootProofs.Proofs.SvCk2a
import C3BootProofs.Proofs.SvCk2b
import C3BootProofs.Proofs.SvCkd
import C3BootProofs.Proofs.SvCkdLoop
import C3BootProofs.Proofs.SvCke
import C3BootProofs.Proofs.SvCkpt
import C3BootProofs.Proofs.SvCkptLink
import C3BootProofs.Proofs.SvClend
import C3BootProofs.Proofs.SvClhit
import C3BootProofs.Proofs.SvClmiss
import C3BootProofs.Proofs.SvCm
import C3BootProofs.Proofs.SvCmdl
import C3BootProofs.Proofs.SvCmdn
import C3BootProofs.Proofs.SvCme
import C3BootProofs.Proofs.SvCmf
import C3BootProofs.Proofs.SvCmk
import C3BootProofs.Proofs.SvCmn
import C3BootProofs.Proofs.SvCms
import C3BootProofs.Proofs.SvCmx
import C3BootProofs.Proofs.SvCne
import C3BootProofs.Proofs.SvCnm
import C3BootProofs.Proofs.SvCns
import C3BootProofs.Proofs.SvCongr
import C3BootProofs.Proofs.SvConstsLink
import C3BootProofs.Proofs.SvCosigLink
import C3BootProofs.Proofs.SvCosigLoop
import C3BootProofs.Proofs.SvCr1
import C3BootProofs.Proofs.SvCr1e
import C3BootProofs.Proofs.SvCr1n
import C3BootProofs.Proofs.SvCs
import C3BootProofs.Proofs.SvCs1
import C3BootProofs.Proofs.SvCsa
import C3BootProofs.Proofs.SvCsx
import C3BootProofs.Proofs.SvD
import C3BootProofs.Proofs.SvData
import C3BootProofs.Proofs.SvDbc1
import C3BootProofs.Proofs.SvDbc2
import C3BootProofs.Proofs.SvDbc2e
import C3BootProofs.Proofs.SvDbc2m
import C3BootProofs.Proofs.SvDeku1
import C3BootProofs.Proofs.SvDeku2
import C3BootProofs.Proofs.SvDeku3
import C3BootProofs.Proofs.SvDer
import C3BootProofs.Proofs.SvDer2
import C3BootProofs.Proofs.SvDer3
import C3BootProofs.Proofs.SvDer4
import C3BootProofs.Proofs.SvDer5
import C3BootProofs.Proofs.SvDerBridge
import C3BootProofs.Proofs.SvDku1
import C3BootProofs.Proofs.SvDku2
import C3BootProofs.Proofs.SvDp0
import C3BootProofs.Proofs.SvDp1
import C3BootProofs.Proofs.SvDp2
import C3BootProofs.Proofs.SvDp3
import C3BootProofs.Proofs.SvDp4
import C3BootProofs.Proofs.SvDp5
import C3BootProofs.Proofs.SvDpv
import C3BootProofs.Proofs.SvEc
import C3BootProofs.Proofs.SvEcA1
import C3BootProofs.Proofs.SvEcA2
import C3BootProofs.Proofs.SvEcA3
import C3BootProofs.Proofs.SvEcD
import C3BootProofs.Proofs.SvEcDs
import C3BootProofs.Proofs.SvEcLib2
import C3BootProofs.Proofs.SvEcMl
import C3BootProofs.Proofs.SvEcMl2
import C3BootProofs.Proofs.SvEcMl3
import C3BootProofs.Proofs.SvEcPt
import C3BootProofs.Proofs.SvEcT0a
import C3BootProofs.Proofs.SvEcT0b
import C3BootProofs.Proofs.SvEcT0c
import C3BootProofs.Proofs.SvEcT1a
import C3BootProofs.Proofs.SvEcT1b
import C3BootProofs.Proofs.SvEcT1c
import C3BootProofs.Proofs.SvEcW
import C3BootProofs.Proofs.SvEcW2
import C3BootProofs.Proofs.SvEcW3
import C3BootProofs.Proofs.SvEcdsa
import C3BootProofs.Proofs.SvEd
import C3BootProofs.Proofs.SvEdImage
import C3BootProofs.Proofs.SvEkuLoop
import C3BootProofs.Proofs.SvEntry
import C3BootProofs.Proofs.SvExtLink
import C3BootProofs.Proofs.SvExtListLink
import C3BootProofs.Proofs.SvExtLoop
import C3BootProofs.Proofs.SvFail
import C3BootProofs.Proofs.SvFail2
import C3BootProofs.Proofs.SvGt
import C3BootProofs.Proofs.SvILoop
import C3BootProofs.Proofs.SvISearch
import C3BootProofs.Proofs.SvIend
import C3BootProofs.Proofs.SvIhit
import C3BootProofs.Proofs.SvImiss
import C3BootProofs.Proofs.SvIvA
import C3BootProofs.Proofs.SvIvB
import C3BootProofs.Proofs.SvIvE
import C3BootProofs.Proofs.SvIvHc
import C3BootProofs.Proofs.SvIvHx
import C3BootProofs.Proofs.SvIvLib
import C3BootProofs.Proofs.SvIvLoop
import C3BootProofs.Proofs.SvKu
import C3BootProofs.Proofs.SvL1
import C3BootProofs.Proofs.SvL2
import C3BootProofs.Proofs.SvL3
import C3BootProofs.Proofs.SvL4
import C3BootProofs.Proofs.SvL5
import C3BootProofs.Proofs.SvL6
import C3BootProofs.Proofs.SvL7
import C3BootProofs.Proofs.SvL8a
import C3BootProofs.Proofs.SvLayout
import C3BootProofs.Proofs.SvLeafH
import C3BootProofs.Proofs.SvLeafH1
import C3BootProofs.Proofs.SvLeafH2
import C3BootProofs.Proofs.SvLeafH3
import C3BootProofs.Proofs.SvLeafHash
import C3BootProofs.Proofs.SvLeafLink
import C3BootProofs.Proofs.SvLh
import C3BootProofs.Proofs.SvLib2
import C3BootProofs.Proofs.SvMs0
import C3BootProofs.Proofs.SvNSearch
import C3BootProofs.Proofs.SvOk
import C3BootProofs.Proofs.SvP256
import C3BootProofs.Proofs.SvP256A
import C3BootProofs.Proofs.SvP256All
import C3BootProofs.Proofs.SvP256B
import C3BootProofs.Proofs.SvP256C
import C3BootProofs.Proofs.SvP256D
import C3BootProofs.Proofs.SvP256St
import C3BootProofs.Proofs.SvPv
import C3BootProofs.Proofs.SvPvWitness
import C3BootProofs.Proofs.SvRk
import C3BootProofs.Proofs.SvRl
import C3BootProofs.Proofs.SvRm
import C3BootProofs.Proofs.SvSeg
import C3BootProofs.Proofs.SvSegAttr
import C3BootProofs.Proofs.SvSegAttrPre
import C3BootProofs.Proofs.SvSegCert
import C3BootProofs.Proofs.SvSegCk
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
import C3BootProofs.Proofs.SvSha2
import C3BootProofs.Proofs.SvSpec
import C3BootProofs.Proofs.SvSpecAux
import C3BootProofs.Proofs.SvTLoop
import C3BootProofs.Proofs.SvTSearch
import C3BootProofs.Proofs.SvTlend
import C3BootProofs.Proofs.SvTlhit
import C3BootProofs.Proofs.SvTlmiss
import C3BootProofs.Proofs.SvTop
import C3BootProofs.Proofs.SvTp
import C3BootProofs.Proofs.SvTpv
import C3BootProofs.Proofs.SvTs
import C3BootProofs.Proofs.SvTs1
import C3BootProofs.Proofs.SvTsa
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
import C3BootProofs.Proofs.SvTsig
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
import C3BootProofs.Proofs.SvTsv
import C3BootProofs.Proofs.SvVerify
import C3BootProofs.Proofs.SvVerifyAt
import C3BootProofs.Proofs.SvWin0
import C3BootProofs.Proofs.SvWin0e
import C3BootProofs.Proofs.SvWin0n
import C3BootProofs.Proofs.SvWin1
import C3BootProofs.Proofs.SvWin1e
import C3BootProofs.Proofs.SvWin1n
import C3BootProofs.Proofs.SvWin2
import C3BootProofs.Proofs.SvWin2e
import C3BootProofs.Proofs.SvWin2n
import C3BootProofs.Proofs.SvWin3
import C3BootProofs.Proofs.SvWin3e
import C3BootProofs.Proofs.SvWin3n
import C3BootProofs.Proofs.SvWin4
import C3BootProofs.Proofs.SvWin4e
import C3BootProofs.Proofs.SvWin4n
import C3BootProofs.Proofs.SvWin5
import C3BootProofs.Proofs.SvWin5e
import C3BootProofs.Proofs.SvWin5n
import C3BootProofs.Proofs.SvWin6
import C3BootProofs.Proofs.SvWin6e
import C3BootProofs.Proofs.SvWin6n
import C3BootProofs.Proofs.SvWin7
import C3BootProofs.Proofs.SvWin7e
import C3BootProofs.Proofs.SvWin7n
import C3BootProofs.Proofs.SvWinLink
import C3BootProofs.Proofs.SvX1
import C3BootProofs.Proofs.SvX2
import C3BootProofs.Proofs.SvX2c
import C3BootProofs.Proofs.SvX2n
import C3BootProofs.Proofs.SvX2z
import C3BootProofs.Proofs.SvZA
import C3BootProofs.Proofs.SvZB
import C3BootProofs.Proofs.SvZDs
import C3BootProofs.Proofs.SvZDs2
import C3BootProofs.Proofs.SvZDs3
import C3BootProofs.Proofs.SvZDs4
import C3BootProofs.Proofs.SvZE
import C3BootProofs.Proofs.SvZLib
import C3BootProofs.Proofs.SvZLib2
import C3BootProofs.Proofs.SvZLoop
import C3BootProofs.Proofs.SvZLoop2
import C3BootProofs.Proofs.SvZS

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
