# TODO: Anchor trust directly to Sigstore's TUF root

## Goal

Eliminate all custom operator-maintained signing keys (the 2-of-4 offline Ed25519 genesis key set, key-set rotation chain, and custom signed trust-root blob) and rely directly on Sigstore's established TUF root (`sigstore/root-signing`) and keyless signing everywhere possible.

This is intentionally deferred until the current proof work in #710 wraps up, so it does not derail ongoing progress.

## Planned architectural change

### 1. Bootloader & verifier (`c3-bootloader`, `c3-verify`)
- **Replace the genesis key set with Sigstore's TUF root:** Compile Sigstore's pinned TUF root (`N.root.json` — root keys, threshold, and version) into the bootloader instead of `GENESIS`.
- **Compile the release identity policy into the bootloader:** Hardcode the Fulcio OIDC issuer, GitHub numeric repository ID, numeric owner ID, workflow URI, and build trigger rather than reading them from a custom signed blob.
- **Verify Sigstore TUF metadata on-device:** Replace `chain` + `trustroot` verification with a `no_std` TUF verifier covering:
  - Root rotation chain (`N+1.root.json` … `M.root.json`) over TUF canonical JSON,
  - `targets.json` signature verification under `M.root.json`,
  - `trusted_root.json` digest verification against `targets.json`,
  - Extraction of Fulcio intermediates, Rekor v2 log keys, and TSA signing certificates with their validity windows.

### 2. Slot format, host tooling, and CI (`c3-verify`, `c3-ota`, workflows)
- Replace the slot manifest's `chain` and `blob` parts with Sigstore's TUF metadata (`root` chain, `targets.json`, `trusted_root.json`).
- Update `c3-release.yml` to automatically fetch and package the latest Sigstore TUF metadata into every release slot — no manual offline signing ceremony on Sigstore rotations.
- Retire `c3-trust-root.yml` and the custom genesis/chain/blob signing subcommands in `c3-ota`.

### 3. eFuse `SECURE_VERSION` semantics
- All 16 monotonic eFuse raises (`0`–`16`) are reserved **exclusively** for anti-rollback of security-critical **app** fixes (`image.security_version >= efuse_level`).
- Routine app releases spend `0` eFuse bits.
- Routine Sigstore / Rekor / Fulcio / TSA rotations spend `0` eFuse bits.
- Emergency Sigstore key rotations also spend `0` eFuse bits (see accepted tradeoffs below).
- Hardware Secure Boot v2 (RSA-3072 for the frozen bootloader itself — optionally signed once with an ephemeral key if no USB updates are planned) and `efuse::lock()` remain unchanged.

### 4. Lean proofs (`c3-boot-proofs`)
- Retire `Spec/TrustRoot.lean`, `Theorems/TrustRoot.lean`, and the machine-code proofs for `chain`, `keys`, and `trustroot`.
- Specify and prove the on-device TUF verifier (strict JSON / canonical JSON parsing, root chain, `targets.json` → `trusted_root.json` checks) on top of the existing verified ECDSA P-256 / Ed25519 / SHA-256 primitives.
- Update `boot_main` and the headline theorem to anchor authenticity directly to Sigstore's TUF root and the compiled-in release identity policy.
- **Sequencing note:** Coordinate this binary change with switching the verified image to the production configuration (`C3_EFUSE_BURN=on` + implemented `efuse::lock()`) so `boot_main` composition and the headline theorem only have to be finalized once on the production binary.

## Accepted tradeoffs

- **On-device JSON / TUF parsing:** Adds a strict JSON / TUF canonical-JSON parser and verifier to the bootloader and Lean proofs, replacing the smaller custom binary trust-root blob.
- **Baked-in identity policy:** Moving to a different GitHub repository or workflow path requires a USB bootloader reflash (pinning numeric repository and owner IDs survives repository renames).
- **Sigstore TUF key algorithms:** Assumes Sigstore's TUF root keyholders continue using signature algorithms implemented by the bootloader (ECDSA P-256 / P-384 / Ed25519).
- **Emergency Sigstore key revocation:** Because `SECURE_VERSION` only floors the app's `security_version` and not the TUF `targets.json` version, a pre-revocation `trusted_root.json` remains validly TUF-signed. Simultaneous compromise of Fulcio, Rekor, and TSA is accepted as out of scope for OTA and handled via USB recovery.

## Cutover plan

### Done without changing the bootloader

The verifier and its specification exist, and the bootloader image is
unchanged (`bootloader/dev-image.sha256` still pins
`7b2964d01ca71f7ad3a86037ace21d98d4aed1af6181fabccb3de7e680464fce`):

- `c3-verify`'s `tuf` feature has `json` (strict and canonical JSON),
  `tuf` (the C3TU container, the root chain, and `targets.json`),
  `trusted_root` (Fulcio, Rekor, and TSA keys into a `TrustRoot`), and
  `tuf_slot::accept_slot`. The feature is off in the bootloader build,
  because compiling the modules in changes how the existing code is
  inlined, and so the image digest, even with nothing calling them.
- `c3-ota` has `tuf-root`, `tuf-package`, `tuf-verify`, and `tuf-accept`,
  and `testdata/tuf/` pins Sigstore's roots 5 through 16, `targets.json`,
  and `trusted_root.json` from `sigstore/root-signing` (`fetch.sh`
  downloads them again).
- `c3-boot-proofs/C3BootProofs/Spec/{Json,Tuf,TrustedRoot,Accept}.lean`
  specify the same checks, and `c3-boot-proofs.yml` requires
  `lake exe tuf-check` to agree with `c3-ota`'s `tuf_vectors` on 3,144
  cases. `fuzz/` has a `tuf` target.
- The formats are in `docs/formats.md`, under "TUF part".

### Steps

Do these as one bootloader change, so the image digest, the extracted
function bytes, and the proofs change once:

1. **Slot format.** Give the manifest a version 2 that replaces the
   `chain` and `blob` parts with one `tuf` part. Update
   `manifest::parse`, `c3-ota slot`, `ota/tests/mutation.rs`, the fuzz
   seeds, and `qemu/scenarios.sh`.
2. **Development trust.** Replace the development genesis keys with a
   development TUF repository: a root and targets signed by seeds in
   `testdata/keys/`, listing fakestore's `trusted_root.json`. `ota/src/tuf.rs`
   already builds and signs such metadata for the test cases.
3. **Build settings.** Replace `C3_GENESIS` with `C3_TUF_ROOT` (`dev`, or
   the canonical root that `c3-ota tuf-root` writes) and compile the
   identity policy in from build settings. Keep the rule that a production
   root requires `C3_EFUSE_BURN=on`.
4. **Memory.** Bound what the bootloader reads into RAM. Holding the whole
   TUF part needs room for every root; reading one root at a time from
   flash needs two root buffers, `targets.json`, `trusted_root.json`, and
   `trusted_root::buffer_len` of it (about 14 KB for today's file). Cap
   documents on the device well below `MAX_DOC_LEN`, and measure peak
   stack in QEMU before choosing sizes. A trial build that called
   `tuf_slot::accept_slot` from `check_slot` with a 32 KB TUF buffer and a
   16 KB key buffer grew `.text` from 84,640 to 93,896 bytes (of 147,456)
   and `.rodata` from 4,704 to 10,912 bytes. Its buffers took about 73 KB
   of the 89 KB left for the stack, before any stack frames.
5. **Wire it in.** `check_slot` calls `tuf_slot::accept_slot` with the
   pinned root and compiled-in policy, logs the `TufError`, and drops
   `GENESIS`. `Accepted.level` is the image's `security_version`, so
   `decide` and the level rules don't change.
6. **Production configuration.** In the same change, implement
   `efuse::lock()`, fix eFuse programming timing at 160 MHz, build with
   `C3_EFUSE_BURN=on`, and pin Sigstore's current root and the real
   repository and owner IDs. Then pin the new digest.
7. **Proofs.** Regenerate `Image/Bootloader*.lean` with
   `scripts/extract-functions.py` and the generated proofs with their
   `gen-*.py` scripts, and rework the hand-written machine-code proofs
   whose functions moved. Retire `Spec/TrustRoot.lean`,
   `Theorems/TrustRoot.lean`, and the proofs for `chain`, `keys`, and
   `trustroot`. Prove that the machine code of `json::parse`,
   `tuf::verify`, `trusted_root::extract`, and `tuf_slot::accept_slot`
   computes the new specifications, prove properties of the specifications
   (a canonical document re-encodes to itself; an accepted chain has a
   threshold of signatures under each root), and restate the headline
   theorem from the pinned TUF root and the compiled-in policy. Rebuild
   the boot lockstep scenarios.
8. **Release and CI.** `c3-release.yml` fetches the TUF metadata with a
   TUF client, packages the roots after the pinned one with
   `tuf-package`, and runs `tuf-verify` before it signs. Change
   `c3-trust-root.yml` to open a pull request that refreshes
   `testdata/tuf/` when Sigstore publishes a root, then retire `c3-ota link`,
   `c3-ota blob`, and the genesis keys.

### Open questions

- **Chain growth.** Every slot carries each root after the pinned one,
  about 5.5 KB each, up to 32. Sigstore published 12 roots from root 5 to
  root 16. Is re-pinning over USB the answer when the chain grows too
  long, or should the device keep the newest root it verified, which
  adds trusted writable state?
- **Expiry.** Roots and `targets.json` expire within months, so each
  release needs fresh metadata, and a slot signed before expiry stays
  bootable for good. Only the final root's expiry counts, so an expired
  root earlier in the chain passes. Is that what we want?
- **Limits.** `extract` rejects a trusted root with more than 4 usable
  Fulcio intermediates, 8 Ed25519 logs, or 4 TSAs. Today's file uses 2,
  1, and 1. Should the device skip extra entries instead of rejecting
  every update?
- **Key types.** Roots 1 through 4 use hex ECDSA keys, which the device
  doesn't decode, and Rekor's P-256 log and any non-P-384 certificate
  authority are skipped. A change in Sigstore's key types stops OTA until
  a USB reflash.
- **Development root.** Generated seeds, as in step 2, or Sigstore's
  staging repository?
